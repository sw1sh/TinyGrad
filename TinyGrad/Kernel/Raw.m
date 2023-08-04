Package["TinyGrad`"]

PackageExport[RawBuffer]



Class[RawBuffer,
    "Init"[self_, size_, type_String, data_ : None] :> (
        self["Size"] = size;
        self["Type"] = type;
        self["Data"] = data;
        self["MemorySize"] = size * $TypeByteCounts[type];
    ),

    "Format"[self_, form_] :> BoxForm`ArrangeSummaryBox[
        "RawBuffer",
        self,
        None,
        {
            BoxForm`MakeSummaryItem[{"Size: ", self["Size"]}, form],
            BoxForm`MakeSummaryItem[{"Type: ", self["Type"]}, form],
            BoxForm`MakeSummaryItem[{"MemorySize: ", self["MemorySize"]}, form]
        },
        {{}},
        form
    ]
]

RawBuffer[args___] := RawBuffer["New"[args]]

