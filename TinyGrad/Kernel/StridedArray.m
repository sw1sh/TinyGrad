Package["TinyGrad`"]

PackageExport[StridedArray]
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


Class[StridedArray,

    "$Init"[self_,
        initData : _ ? NumericArrayQ | _ ? NumericQ,
        initStrides : {___Integer} | Automatic : Automatic
    ] :> Enclose @ Block[{
        data,
        type, shape,
        size, strides
    },
        If[ NumericArrayQ[initData],
            data = initData;
            shape = Dimensions[data],
            data = ConfirmBy[NumericArray[{initData}], NumericArrayQ];
            shape = {}
        ];
        data = Flatten[data];
        type = NumericArrayType[data];
        size = ConfirmBy[$TypeByteCounts[type], IntegerQ];
        strides = Replace[initStrides, Automatic :> ShapeStrides[shape]];
        ConfirmAssert[Length[shape] == Length[strides]];
        self["Pointer"] = RawMemoryExport[data];
        ConfirmAssert[self["Pointer"]["Value"]["Type"] === type];
        self["Type"] = type;
        self["Size"] = size;
        self["Shape"] = shape;
        self["Strides"] = strides;

        f_Symbol[largs___, self, rargs___] /; MemberQ[Attributes[f], NumericFunction] ^:=
            elementwise[f, self["$Extend"], {largs}, {rargs}];

        ArrayReshape[self, args___] ^:= reshape[self @ "$Extend", args];

        Cast[self, args___] ^:= cast[self @ "$Extend", args];

        Transpose[self, args___] ^:= self["$Extend"]["Transpose"[args]];


        self
    ],

    "$Properties" -> {"Dimension", "TotalSize", "$Normal", "NumericArray"},

    "Dimension"[self_] :> Times @@ self["Shape"],

    "TotalSize"[self_] :> self["Size"] * self["Dimension"],

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
            {BoxForm`SummaryItem[{"Item Size: ", self["Size"]}]},
            {BoxForm`SummaryItem[{"Total Size: ", self["TotalSize"]}]}
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
    "$Normal"[self_] :> Enclose @ With[{pointer = self["Pointer"], shape = self["Shape"], strides = self["Strides"]},
        ConfirmAssert[Length[shape] === Length[strides]];
        Array[RawMemoryRead[pointer, Total[strides ({##} - 1)]] &, shape]
    ],
    "NumericArray"[self_] :> RawMemoryImport[self["Pointer"], {"NumericArray", self["Dimension"]}],

    "Transpose"[self_, list_List : {2, 1}] :> (self["Transpose"[FindPermutation[list]]]; self),
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

    f_String[self_] /; MemberQ[Attributes[Evaluate @ Symbol[f]], NumericFunction] :> elementwise[ElementwiseLayer[Symbol[f]], self],

    "Empty"[size_, type_] :> StridedArray[NumericArray[ConstantArray[0, size], type]],
    "Arange"[n : _Integer ? NonNegative | Automatic : Automatic, shape : Shape | Automatic : Automatic] :> With[{dim = Times @@ shape},
        StridedArray[ArrayReshape[PadRight[Range @ Replace[n, Automatic -> dim], dim], shape], ShapeStrides[shape]]
    ]
]

PrimeReshape[shape_, strides_ : None] := Block[{factors = Sow[FactorInteger /@ shape], primeShape},
    primeShape = Catenate[Table @@@ Catenate[factors]];
    If[strides === None, Return[primeShape]];
	{
        primeShape,
        Catenate @ MapThread[ShapeStrides[Catenate[Table @@@ #2], #1] &, {strides, factors}]
    }
]

PrimeReshape[a_::[StridedArray]] := (
	{a["Shape"], a["Strides"]} = PrimeReshape[a["Shape"], a["Strides"]]
	a
)

reshape[self_, shape_] := Enclose @ Block[{strides, merge},
    ConfirmAssert[self["Dimension"] == Times @@ shape];
    stides = ShapeStrides[shape];
    merge = mergeShapeStrides[{{shape, stides}, {self["Shape"], self["Strides"]}}];
    self["Shape"] = shape;
    If[ Length[merge] == 1,
        self["Strides"] = merge[[1, 2]],

        self["Strides"] = stides;
        self["Pointer"] = RawMemoryExport @ ConfirmBy[
            NumericArray[
                RawMemoryImport[self["Pointer"], {"NumericArray", self["Dimension"]}],
                self["Type"]
            ],
            NumericArrayQ
        ];
    ];
    self
]

cast[self_, type_, OptionsPattern[{Method -> "Coerce"}]] := Enclose[
    self["Size"] = ConfirmBy[$TypeByteCounts[type], IntegerQ];
    self["Type"] = type;
    self["Pointer"] = RawMemoryExport @ ConfirmBy[NumericArray[RawMemoryImport[self["Pointer"], {"NumericArray", self["Dimension"]}], type, OptionValue[Method]], NumericArrayQ];
    self
]

elementwise[f_, self_, largs_, rargs_] := Enclose @ Block[{
    arrayLArgs = If[StridedArray["$Test"][#], Normal[#], #] & /@ largs,
    arrayRArgs = If[StridedArray["$Test"][#], Normal[#], #] & /@ rargs,
    inputs, result
},
    inputs = Join[arrayLArgs, {Normal @ self}, arrayRArgs];
    result = NumericArray @ Flatten @ Confirm @ FunctionLayer[Apply[f]][inputs];
    self["Pointer"] = RawMemoryExport @ result;
    self["Type"] = NumericArrayType[result];
    self["Strides"] = ShapeStrides[self["Shape"]];
    self
]

reduce[f_, self_, lvl_, OptionsPattern[{"KeepDims" -> False}]] := Enclose @ Block[{
    keepDims = OptionValue["KeepDims"],
    result
},
    result = Confirm @ AggregationLayer[f, lvl][Normal[self]];
    result = If[NumericQ[result], NumericArray[{result}], NumericArray[Flatten[result]]];
    self["Pointer"] = RawMemoryExport @ result;
    If[ keepDims,
        self["Shape"] = MapAt[1 &, self["Shape"], LevelSpan[lvl]],

        self["Shape"] = Drop[self["Shape"], lvl]
    ];
    self["Strides"] = ShapeStrides[self["Shape"]];
    self
]

StridedArray[data_, args___] := StridedArray@ "$New"[If[ArrayQ[data], NumericArray[data], data], args]
