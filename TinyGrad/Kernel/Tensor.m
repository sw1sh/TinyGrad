Package["TinyGrad`"]

PackageExport[Tensor]



Class[Tensor, "Training" -> False, "NoGradient" -> False, "Type" -> "Real32"]

Options[Tensor] = {"Device" -> None, "Type" -> None, "RequiresGradient" -> None}

Tensor[data_,
    device: _String | None : None,
    type : _String | None : None,
    requiresGradient : _ ? BooleanQ | None : None,
    opts : OptionsPattern[]
] :=
    Tensor[data, opts, "Device" -> device, "Type" -> type, "RequiresGradient" -> requiresGradient]

Tensor[data_, OptionsPattern[]] := Tensor["New"[data, Sequence @@ OptionValue[Keys[Options[Tensor]]]]]

Tensor @ "Init"[
    self_,
    initData_,
    device : _String | None : None,
    initType : _String | None : None,
    requiresGradient : _ ? BooleanQ | None : None
] := Enclose @ Block[{
    data = initData,
    type = Replace[initType, None :> Tensor["Type"]]
},
    self["Gradient"] = None;
    self["RequiresGradient"] = requiresGradient;
    self["Context"] = None;

    If[ data["Class"] === LazyBuffer,
        ConfirmAssert[initType === None || type === data["Type"]];
        self["LazyData"] = If[data["Device"] === device, data, data["LoadOp"["FROM", data["Shape"], data["Type"], device, data]]];
        Return[self]
    ];

    If[ MatchQ[data, _Integer | _Real | _Complex],
        self["LazyData"] = LazyBuffer["LoadOp"["CONST", {}, type, device, data]];
        Return[self]
    ];

    data = NumericArray[data, type];
    If[ NumericArrayQ[data],
        data = LazyBuffer["FromCPU"[data]];
        self["LazyData"] = If[data["Device"] === device, data, LazyBuffer["LoadOp"["FROM", data["Shape"], data["Type"], device, data]]];
        Return[self]
    ];

    Failure[<|
        "MessageTemplate" :> "Can't create Tensor from ``",
        "MessageParameters" -> {initData}
    |>]
]

Tensor["Properties"] = {"Device", "Shape", "Type"}

Tensor[(prop : "Device" | "Shape" | "Type")[self_]] := self["LazyData"][prop]

Tensor["Realize"[self_]] := (self["LazyData"]["Realize"[]]; self)

Tensor["Assign"[self_, x_]] := Enclose @ Block[{tensor = Tensor[x, "Type" -> self["Type"]]},
    ConfirmAssert[self["Shape"] === tensor["Shape"] && self["Device"] === tensor["Device"]];
    ConfirmAssert[! x["RequiresGradient"]];
    If[ self["LazyData"]["Realized"] =!= None,
        x["LazyData"]["OutputBuffer"] = self["LazyData"]["Realized"]
    ];
    self["LazyData"] = x["LazyData"];
    self
]

Tensor["Detach"[self_]] := Tensor[self["LazyData"], self["Device"], False]

Tensor["Pad"[self_, pad : {{_Integer, _Integer} ...}, value_ : 0]] :=
    TensorFunction["Pad"] @ "Apply"[self, pad]

Tensor["Eye"[dim_Integer ? Positive, args___]] := Tensor[{1}, args] @* "Pad"[{{0, dim}}] @* "Reshape"[1, dim + 1] @* "Expand"[dim, dim + 1] @* "Reshape"[dim * (dim + 1)] @* "Shrink"[{{0, dim * dim}}] @* "Reshape"[dim, dim]


Tensor["MatMul"[self_, x_Tensor, reverse_ : False]] := If[reverse, x . self, self . x]

Tensor["Format"[self_, form_]] :=
    BoxForm`ArrangeSummaryBox[
        "Tensor",
        self,
        None,
        {
            {BoxForm`SummaryItem[{"Type: ", self["Type"]}]},
            {BoxForm`SummaryItem[{"Shape: ", self["Shape"]}]},
            {BoxForm`SummaryItem[{"Device: ", self["Device"]}]}
        },
        {{}},
        form
    ]

