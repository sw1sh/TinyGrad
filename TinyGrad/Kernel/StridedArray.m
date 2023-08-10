Package["TinyGrad`"]

PackageExport[StridedArray]
PackageExport[ShapeStrides]
PackageExport[$TypeByteCounts]



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

    "Init"[self_,
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

        Transpose[self, args___] ^:= self["Extend"]["Transpose"[args]];
    ],

    "Properties" -> {"TotalSize", "Normal"},

    "TotalSize"[self_] :> Times @@ (self["Size"] * self["Shape"]),

    "Format"[self_, form_] :> BoxForm`ArrangeSummaryBox[
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
    "Normal"[self_] :> Enclose @ With[{pointer = self["Pointer"], shape = self["Shape"], strides = self["Strides"]},
        ConfirmAssert[Length[shape] === Length[strides]];
        Array[RawMemoryRead[pointer, Total[strides ({##} - 1)]] &, shape]
    ],

    "Transpose"[self_, list_ : {2, 1}] :> With[{perm = FindPermutation[list]},
        self["Shape"] = Permute[self["Shape"], perm];
        self["Strides"] = Permute[self["Strides"], perm];
        self
    ],

    "Reshape"[self_, shape : Shape] :> Enclose[
        ConfirmAssert[Times @@ shape == Times @@ self["Shape"]];
        self["Shape"] = shape;
        (* self["Strides"] =  *)
        self
    ],

    "Empty"[size_, type_] :> StridedArray[NumericArray[ConstantArray[0, size], type]],
    "Arange"[n_Integer ? NonNegative, shape : Shape | Automatic : Automatic] :>
        StridedArray[Range[n]] @ If[shape === Automatic, CoIdentity, "Reshape"[shape]]
]

StridedArray[data_, strides_ : Automatic] := Enclose @ StridedArray["New"[ConfirmBy[NumericArray[data], NumericArrayQ], strides]]

