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
            data = ConfirmBy[NumericArray[{initData}], NumericQ];
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

        Transpose[self, args___] ^:= self["$Extend"]["Transpose"[args]];
    ],

    "$Properties" -> {"Dimension", "TotalSize", "$Normal"},

    "Dimension"[self_] :> Times @@ self["Shape"],

    "TotalSize"[self_] :> self["Size"] * self["Dimension"],

    "$Format"[self_, form_] :> BoxForm`ArrangeSummaryBox[
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

    "Transpose"[self_, list_List : {2, 1}] :> (self["Transpose"[FindPermutation[list]]]; self),
    "Transpose"[self_, perm_Cycles] :> (
        self["Shape"] = Permute[self["Shape"], perm];
        self["Strides"] = Permute[self["Strides"], perm];
        self
    ),

    "Reshape"[self_, shape : Shape] :> reshape[self @ "$Extend", shape],

    "Cast"[self_, type_, opts : OptionsPattern[]] :> cast[self @ "$Extend", type, opts],

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

StridedArray[data_, strides_ : Automatic] := Enclose @ StridedArray["$New"[ConfirmBy[NumericArray[data], NumericArrayQ], strides]]

