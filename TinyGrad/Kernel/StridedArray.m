Package["TinyGrad`"]

PackageExport[StridedArray]
PackageExport[StridedArrayQ]
PackageExport[ShapeStrides]
PackageExport[$TypeByteCounts]

PackageImport["Wolfram`Class`"]



$TypeByteCounts = <|
    "Void" -> 1,
    "UnsignedInteger8" -> 1, "Integer8" -> 1,
    "UnsignedInteger16" -> 2, "Integer16" -> 2,
    "UnsignedInteger32" -> 4, "Integer32" -> 4,
    "UnsignedInteger64" -> 8, "Integer64" -> 8,
    "Real16" -> 2, "Real32" -> 4, "Real64" -> 8,
    "ComplexReal32" -> 8, "ComplexReal64" -> 16,
    "CFloat" -> 4, "CDouble" -> 8,
    "CUnsignedChar" -> 1, "CSignedChar" -> 1,
    "CUnsignedShort" -> 2, "CShort" -> 2,
    "CUnsignedInt" -> 4, "CInt" -> 4,
    "CUnsignedLong" -> 8, "CLong" -> 8,
    "OpaqueRawPointer" -> 8
|>


ShapeStridesSize[shape_, strides_] := If[AnyTrue[shape, EqualTo[0]], 0, (shape - 1) . strides + 1]

Class[StridedArray,

    "$Init"[self_,
        initData : _ ? NumericArrayQ | _ ? NumericQ,
        initStrides : {___Integer} | Automatic : Automatic
    ] :> Enclose @ Block[{
        data,
        type, shape,
        itemByteCount, strides
    },
        If[ NumericArrayQ[initData],
            data = initData;
            shape = Dimensions[data],
            data = ConfirmBy[NumericArray[{initData}], NumericArrayQ];
            shape = {}
        ];
        data = Flatten[data];
        type = NumericArrayType[data];
        itemByteCount = ConfirmBy[$TypeByteCounts[type], IntegerQ];
        strides = Replace[initStrides, Automatic :> ShapeStrides[shape]];
        ConfirmAssert[Length[shape] == Length[strides]];
        self["Pointer"] = RawMemoryExport[data];
        ConfirmAssert[self["Pointer"]["Value"]["Type"] === type];
        self["Type"] = type;
        self["ItemByteCount"] = Quantity[itemByteCount, "Bytes"];
        self["Shape"] = shape;
        self["Strides"] = strides;
        self["Size"] = ShapeStridesSize[shape, strides];

        f_Symbol[largs___, self, rargs___] /; MemberQ[Attributes[f], NumericFunction] ^:=
            elementwiseVarArgs[FunctionLayer[Apply[f]], self, {largs}, {rargs}];

        Dimensions[self] ^:= self["Shape"];

        ArrayReshape[self, args___] ^:= reshape[StridedArray[self], args];

        ArrayPad[self, args___] ^:= pad[StridedArray[self], args];

        Part[self, args___] ^:= part[StridedArray[self], args];

        Cast[self, args___] ^:= cast[StridedArray[self], args];

        Transpose[self, args___] ^:= StridedArray[self]["Transpose"[args]];

        Less[self, other_] ^:= StridedArray[self]["Less"[other]];

        self
    ],

    "$Properties" -> {"Dimension", "Rank", "ByteCount", "$Normal", "NumericArray", "NormalNumericArray"},

    "Dimension"[self_] :> Times @@ self["Shape"],
    "Rank"[self_] :> Length[self["Shape"]],
    "ByteCount"[self_] :> self["Size"] * self["ItemByteCount"],

    "$Format"[self_, form___] :> BoxForm`ArrangeSummaryBox[
        "StridedArray",
        self,
        None,
        {
            {BoxForm`SummaryItem[{"Type: ", self["Type"]}]},
            {BoxForm`SummaryItem[{"Shape: ", self["Shape"]}]},
            {BoxForm`SummaryItem[{"Strides: ", self["Strides"]}]}
        },
        {
            {BoxForm`SummaryItem[{"Pointer: ", BaseForm[self["Pointer"]["Value"]["Address"], 16]}]},
            {BoxForm`SummaryItem[{"Size: ", self["Size"]}]},
            {BoxForm`SummaryItem[{"ByteCount: ", self["ByteCount"]}]}
        },
        form
    ],

    (* TODO: Compile *)
    (*
        FunctionCompile @ Function[{
            Typed[pointer, "RawPointer"::["MachineInteger"]],
            Typed[shape, "ListVector"::["MachineInteger"]],
            Typed[strides, "ListVector"::["MachineInteger"]]},
	        Array[FromRawPointer[pointer, Total[strides * ({##} - 1)]] &, shape]
        ]
    *)
    "$Normal"[self_] :> Enclose @ Block[{pointer = self["Pointer"], shape = self["Shape"], strides = self["Strides"], dim = self["Dimension"], perm},
        ConfirmAssert[Length[shape] === Length[strides]];
        perm = Quiet @ FindPermutation[ShapeStrides[shape], strides];
        If[ MatchQ[perm, _Cycles] && self["Size"] == ShapeStridesSize[shape, strides],
            Normal @ If[NumericArrayQ[#], Transpose[#, perm], #] & @ ArrayReshape[Confirm @ self["NumericArray"], Permute[shape, InversePermutation[perm]]],
            Normal @ ArrayReshape[ Confirm[self["NumericArray"]][[Mod[Flatten[Array[{##} - 1 &, shape] . strides], self["Size"]] + 1]], shape]
        ]
    ],
    "NumericArray"[self_] :> RawMemoryImport[self["Pointer"], {"NumericArray", self["Size"]}],
    "NormalNumericArray"[self_] :> Block[{shape = self["Shape"], strides = self["Strides"]},
        {shape, strides} = Replace[Thread @ MapThread[If[#2 == 0, Nothing, {#1, #2}] &, {shape, strides}], {} -> {{}, {}}];
        ArrayReshape[
            If[ Length[shape] > 0 && strides != ShapeStrides[shape],
                self["NumericArray"][[Mod[Flatten[Array[{##} - 1 &, shape] . strides], self["Size"]] + 1]],
                self["NumericArray"]
            ],
            ReplacePart[self["Shape"], Position[self["Strides"], 0, {1}, Heads -> False] -> 1]
        ]
    ],

    "Transpose"[self_, list_List : {2, 1}] :> (self["Transpose"[InversePermutation @ FindPermutation[list]]]; self),
    "Transpose"[self_, perm_Cycles] :> (
        self["Shape"] = Permute[self["Shape"], perm];
        self["Strides"] = Permute[self["Strides"], perm];
        self
    ),

    "Expand"[self_, shape : Shape] :> Enclose[
        ConfirmAssert[Length[self["Shape"]] == Length[shape]];
        ConfirmAssert[And @@ MapThread[#1 == #2 || #2 == 1 && #3 == 0 &, {shape, self["Shape"], self["Strides"]}]];
        self["Shape"] = shape;
        self
    ],

    "Reshape"[self_, shape : Shape] :> reshape[self, shape],

    "Cast"[self_, type_, opts : OptionsPattern[]] :> cast[self, type, opts],

    "Sum"[self_, lvl_, opts : OptionsPattern[]] :> reduce[Total, self, lvl, opts],
    "Max"[self_, lvl_, opts : OptionsPattern[]] :> reduce[Max, self, lvl, opts],

    "Maximum"[self_, other_] :> With[{lvl = self["Rank"]}, elementwise[FunctionLayer[Apply[MapThread[Max, {#1, #2}, lvl] &]], self, {}, {other}]],
    "Less"[self_, other_] :> elementwise[FunctionLayer[Apply[Less]], self, {}, {other}],

    f_String[self_] /; MemberQ[Attributes[Evaluate @ Symbol[f]], NumericFunction] :> elementwise[ElementwiseLayer[Symbol[f]], self],

    "Where"[self_, x_, y_] :> elementwise[FunctionLayer[Apply[If[#1 != 0, #2, #3] &]], self, {}, {x, y}],

    "Empty"[size_, type_] :> StridedArray[NumericArray[ConstantArray[0, size], type]],
    "Arange"[n : _Integer ? NonNegative | Automatic : Automatic, shape : Shape | Automatic : Automatic] :> With[{dim = Times @@ shape},
        StridedArray[ArrayReshape[PadRight[Range @ Replace[n, Automatic -> dim], dim], shape], ShapeStrides[shape]]
    ],

    "MulSum"[self_, other_, lvl_] :> Enclose @ Block[{axes = LevelAxes[lvl], y, rank = self["Rank"], shape = Dimensions[self], keepAxes},
        ConfirmAssert[shape == Dimensions[other]];
        ConfirmAssert[AllTrue[axes, Between[#, {1, rank}] &]];
        keepAxes = Delete[Range[rank], List /@ axes];
        y = StridedArray[other];
        If[ AllTrue[self["Strides"][[keepAxes]] * y["Strides"][[keepAxes]], EqualTo[0]],
            StridedArray[
                ReshapeLayer[ReplacePart[shape, Thread[axes -> 1]]] @ DotLayer[][{
                    ArrayReshape[
                        Transpose[self, Ordering @ Join[keepAxes, axes]],
                        Append[shape[[keepAxes]], Times @@ shape[[axes]]]
                    ]["NormalNumericArray"],
                    ArrayReshape[
                        Transpose[y, Ordering @ Join[axes, keepAxes]],
                        Prepend[shape[[keepAxes]], Times @@ shape[[axes]]]
                    ]["NormalNumericArray"]
                }]
            ],
            (self * y)["Sum"[axes, "KeepDims" -> True]]
        ]
    ]
]

StridedArrayQ = StridedArray["$Test"]

PrimeReshape[shape_, strides_ : None] := Block[{factors = Sow[FactorInteger /@ shape], primeShape},
    primeShape = Catenate[Table @@@ Catenate[factors]];
    If[strides === None, Return[primeShape]];
	{
        primeShape,
        Catenate @ MapThread[ShapeStrides[Catenate[Table @@@ #2], #1] &, {strides, factors}]
    }
]

PrimeReshape[a_::[StridedArray]] := (
	{a["Shape"], a["Strides"]} = PrimeReshape[a["Shape"], a["Strides"]];
    a["Size"] = ShapeStridesSize[a["Shape"], a["Strides"]];
	a
)

reshape[self_, shape_] := Enclose @ Block[{strides, merge},
    If[self["Shape"] == shape, Return[self]];
    ConfirmAssert[self["Dimension"] == Times @@ shape];
    strides = ShapeStrides[shape];
    merge = mergeShapeStrides[{{shape, strides}, {self["Shape"], self["Strides"]}}];

    If[ Length[merge] == 1,
        self["Strides"] = merge[[1, 2]],

        self["Pointer"] = RawMemoryExport @ ConfirmBy[
            Flatten @ NumericArray[Replace[Normal[self], x_ ? NumericQ :> {x}], self["Type"]],
            NumericArrayQ
        ];
        self["Strides"] = strides;
        self["Size"] = ShapeStridesSize[shape, strides]
    ];
    self["Shape"] = shape;
    self
]

part[self_, args___] := Enclose @ With[{array = NumericArray[PartLayer[{args}] @ Normal[self], self["Type"]]},
    self["Pointer"] = RawMemoryExport @ Flatten @ array;
    self["Shape"] = Dimensions[array];
    self["Strides"] = ShapeStrides[self["Shape"]];
    self["Size"] = ShapeStridesSize[self["Shape"], self["Strides"]];
    self
]

pad[self_, padding_] := Enclose @ With[{array = NumericArray[PaddingLayer[padding] @ Normal[self], self["Type"]]},
    self["Pointer"] = RawMemoryExport @ Flatten @ array;
    self["Shape"] = Dimensions[array];
    self["Strides"] = ShapeStrides[self["Shape"]];
    self["Size"] = ShapeStridesSize[self["Shape"], self["Strides"]];
    self
]

cast[self_, type_, OptionsPattern[{Method -> Automatic}]] := Enclose @ With[{
    method = Replace[OptionValue[Method], Automatic :> If[StringContainsQ[type, "Integer"], "ClipAndRound", "ClipAndCoerce"]]
},
    self["ItemByteCount"] = ConfirmBy[$TypeByteCounts[type], IntegerQ];
    self["Type"] = type;
    self["Pointer"] = RawMemoryExport @ ConfirmBy[NumericArray[Confirm @ self["NumericArray"], type, method], NumericArrayQ];
    self
]

elementwiseVarArgs[f_, self_, largs_List, rargs_List] := Block[{
    sizes = If[StridedArrayQ[#], #["Size"], Times @@ Dimensions[#]] & /@ Join[largs, {self}, rargs],
    take, drop
},
    {take, drop} = TakeDrop[Join[largs, {self}, rargs], PositionLargest[sizes, 1][[1, 1]]];
    elementwise[f, StridedArray[Last[take]], Most[take], drop]
]

elementwise[f_, self_, largs_List, rargs_List] := Enclose @ Block[{
    arrayLArgs = If[StridedArrayQ[#], Normal[#], #] & /@ largs,
    arrayRArgs = If[StridedArrayQ[#], Normal[#], #] & /@ rargs,
    (* size = LCM @@ (If[StridedArrayQ[#], #["Size"], Times @@ Dimensions[#]] & /@ Join[largs, {self}, rargs]), *)
    (* strides = If[StridedArrayQ[#], #["Strides"], ShapeStrides[Dimensions[#]]] & /@ Join[largs, {self}, rargs], *)
    inputs, result
},
    inputs = Join[arrayLArgs, {Normal[self]}, arrayRArgs];
    (* inputs = Map[With[{dim = Times @@ Dimensions[#]},
        Flatten @ Normal @ If[ dim > 1,
            With[{n = size / dim},
                If[n > 1, Join[Sequence @@ ConstantArray[Normal[#], n], First @ FirstPosition[Dimensions[#], 1, {1}]], {#}]
            ],
            {#}
        ]] &,
        inputs
    ]; *)
    result = NumericArray @ Flatten @ {Confirm @ f[inputs]};
    self["Pointer"] = RawMemoryExport @ result;
    self["Type"] = NumericArrayType[result];
    self["Strides"] = ShapeStrides[self["Shape"]];
    self["Size"] = ShapeStridesSize[self["Shape"], self["Strides"]];
    self
]

reduce[f_, self_, lvl_, OptionsPattern[{"KeepDims" -> False}]] := Enclose @ Block[{
    keepDims = OptionValue["KeepDims"],
    result
},
    result = Confirm @ AggregationLayer[f, Replace[lvl, {l_Integer :> ;; l, lvls : {{_Integer}...} :> Catenate[lvls]}]][Normal[self]];
    result = If[NumericQ[result], NumericArray[{result}], NumericArray[Flatten[result]]];
    self["Pointer"] = RawMemoryExport @ result;
    If[ keepDims,
        self["Shape"] = MapAt[1 &, self["Shape"], LevelSpan[lvl]],

        self["Shape"] = Drop[self["Shape"], lvl]
    ];
    self["Strides"] = ShapeStrides[self["Shape"]];
    self["Size"] = ShapeStridesSize[self["Shape"], self["Strides"]];
    self
]

StridedArray[input_, args___] := If[
    StridedArrayQ[input],
    With[{s = StridedArray @ "$New"[input["NumericArray"], args]},
        s["Shape"] = input["Shape"];
        s["Strides"] = input["Strides"];
        s
    ],
    StridedArray @ "$New"[Replace[input, a_ ? ArrayQ :> NumericArray[a]], args]
]
