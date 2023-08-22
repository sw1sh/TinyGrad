Package["TinyGrad`"]

PackageExport[Tensor]

PackageImport["Wolfram`Class`"]



Options[Tensor] = {"Device" -> None, "Type" -> None, "RequiresGradient" -> None}

TensorData = _::[LazyBuffer] | _? ArrayQ | _ ? NumericArrayQ | _ ? NumericQ

Class[Tensor,
    "Training" -> False, "NoGradient" -> False, "Type" -> "Real32", "Device" -> "CPU", "Seed" -> 0,

    "$Init"[NameValuePattern[
        self_,
        Data : TensorData,
        Device : _String | None : None,
        Type : _String | None : None,
        RequiresGradient : _ ? BooleanQ | None : None
    ]] :> Enclose @ Block[{
        data = Data,
        device = Replace[Device, None :> "CPU"],
        type = Replace[Type, None :> Tensor["Type"]]
    },
        If[ Tensor["$Test"][data], Return[data]];
        self["Gradient"] = None;
        self["RequiresGradient"] = RequiresGradient;
        self["Context"] = None;

        Plus[self, ts___] ^:= self["Broadcast"["Add", ts]];
        Times[self, ts___] ^:= self["Broadcast"["Mul", ts]];
        Power[self, ts___] ^:= self["Broadcast"["Pow", ts]];

        Total[self, lvl_ : 1] ^:=
            TensorFunction["Reshape"] @ "Apply"[TensorFunction["Sum"] @ "Apply"[self, "Level" -> lvl], "Shape" -> Drop[self["Shape"], lvl]];

        f_Symbol[self] /; MemberQ[Attributes[f], NumericFunction] ^:= self[SymbolName[f][]];

        If[ LazyBuffer["$Test"][data],
            ConfirmAssert[Type === None || type === data["Type"]];
            self["LazyData"] = If[data["Device"] === device, data, data["LoadOp"["FROM", data["Shape"], data["Type"], device, data]]];
            Return[self]
        ];

        If[ NumericQ[data],
            self["LazyData"] = LazyBuffer["LoadOp"["CONST", {}, type, device, N[data]]];
            Return[self]
        ];

        data = NumericArray[N[data], type];
        If[ NumericArrayQ[data],
            data = LazyBuffer["FromCPU"[data]];
            self["LazyData"] = If[data["Device"] === device, data, LazyBuffer["LoadOp"["FROM", data["Shape"], data["Type"], device, data]]];
            Return[self]
        ];

        Failure[<|
            "MessageTemplate" :> "Can't create Tensor from ``",
            "MessageParameters" -> {Data}
        |>]
    ]
]

Tensor[args___] := Tensor["$New"[args]]

Tensor["$Properties"] = {"Device", "Shape", "Type", "$Normal", "Dimension", "Graph"}

Tensor[(prop : "Device" | "Shape" | "Type")[self_]] := self["LazyData"][prop]

Tensor["Dimension"[self_]] := Times @@ self["Shape"]

Tensor["Realize"[self_]] := Enclose[Confirm @ self["LazyData"]["Realize"[]]; self]

Tensor["Assign"[self_, x_]] := Enclose @ Block[{tensor = Tensor[x, "Type" -> self["Type"]]},
    ConfirmAssert[self["Shape"] === tensor["Shape"] && self["Device"] === tensor["Device"]];
    ConfirmAssert[! tensor["RequiresGradient"]];
    If[ self["LazyData"]["Realized"] =!= None,
        x["LazyData"]["OutputBuffer"] = self["LazyData"]["Realized"]
    ];
    self["LazyData"] = x["LazyData"];
    self
]

Tensor["Detach"[self_]] := Tensor[self["LazyData"], self["Device"], False]

Tensor["$Normal"[self_]] := Normal @ self["LazyData"]

Tensor["To"[self_, device_]] := With[{ret = Tensor[self["LazyData"], device]},
    If[ret["Gradient"] =!= None, ret["Gradient"]["To"[device]]];
    ret
]


Tensor["Reshape"[self_, shape_]] := TensorFunction["Reshape"] @ "Apply"[self, "Shape" -> Replace[shape, -1 :> - self["Dimension"] / Times @@ shape, {1}]]

Tensor["Expand"[self_, shape_]] := TensorFunction["Expand"] @ "Apply"[self, "Shape" -> shape]

Tensor["Pad"[self_, pad : {{_Integer, _Integer} ...}, value_ : 0]] :=
    TensorFunction["Pad"] @ "Apply"[self, "Padding" -> pad]


Tensor["Eye"[dim_Integer ? Positive, args___]] := Tensor[{1}, args] @* "Pad"[{{0, dim}}] @* "Reshape"[1, dim + 1] @* "Expand"[dim, dim + 1] @* "Reshape"[dim * (dim + 1)] @* "Shrink"[{{0, dim * dim}}] @* "Reshape"[dim, dim]


Tensor["MatMul"[self_, x_Tensor, reverse_ : False]] := If[reverse, x . self, self . x]

Tensor["$Format"[self_, form_]] :=
    BoxForm`ArrangeSummaryBox[
        "Tensor",
        self,
        None,
        {
            {BoxForm`SummaryItem[{"Type: ", self["Type"]}]},
            {BoxForm`SummaryItem[{"Shape: ", self["Shape"]}]},
            {BoxForm`SummaryItem[{"Device: ", self["Device"]}]}
        },
        {
            {BoxForm`SummaryItem[{"RequiresGradient: ", self["RequiresGradient"]}]},
            {BoxForm`SummaryItem[{"LazyData: ", self["LazyData"]}]}
        },
        form
    ]

Tensor["Graph"[self_]] := Block[{edges = {}, visited = {}, deepwalk},
    deepwalk[node_] := (
        AppendTo[visited, node];
        Scan[If[! MemberQ[visited, #], AppendTo[edges, node -> #]; deepwalk[#]] &, node["Op"]["Source"]];
    );

    deepwalk[self["LazyData"]];

    Graph[
        visited, edges,
        VertexShapeFunction -> Function[
            Inset[Style[
                    If[#2["RealizedQ"], Framed, Identity] @ If[
                        #2["Op"]["Argument"] === None,
                        #2["OpName"],
                        #2["OpName"][#2["Op"]["Argument"]]
                    ],
                    Black
                ],
                #1,
                #3
            ]
        ],
        GraphLayout -> "LayeredDigraphEmbedding",
        PerformanceGoal -> "Quality"
    ]
]

Tensor["DeepWalk"[self_]] := Block[{nodes = {}, visited = {}, deepwalk},
    deepwalk[node_] := (
        AppendTo[visited, node];
        If[ TensorFunction["$Test"] @ node["Context"],
            Scan[If[! MemberQ[visited, #], deepwalk[#]] &, node["Context"]["Parents"]];
            AppendTo[nodes, node]
        ]
    );

    deepwalk[self];

    nodes
]

Tensor["Backward"[self_]] := Enclose @ Block[{grads},
    ConfirmAssert[self["Shape"] === {}, "Only scalar gradients are currently supported"];
    self["Gradient"] = Tensor[1, "Type" -> self["Type"], "Device" -> self["Device"], "RequiresGradient" -> False];
    Do[
        If[! t0["RequiresGradients"], Continue[]];
        ConfirmAssert[t0["Gradient"] =!= None];
        grads = Replace[
            Developer`ToList[t0["Context"]["Backward"[t0["Gradient"]["LazyData"]]]],
            g : Except[None] :> Tensor[g, "Device" -> self["Device"], "RequiresGradient" -> False],
            {1}
        ];
        MapThread[
            {t, g} |-> If[g =!= None && t["RequiresGradient"],
                ConfirmAssert[t["Shape"] === g["Shape"], StringTemplate["Gradient stape must match tensor shape, `` != ``"][g["Shape"], t["Shape"]]];
                t["Gradient"] = If[t["Gradient"] === None, g, t["Gradient"] + g];
            ],
            {t0["Context"]["Parents"], grads}
        ];
        t0["Context"] =.;
        ,
        {t0, Reverse[self["DeepWalk"[]]]}
    ]
]

Tensor["Cast"[self_, type_]] := If[self["Type"] === type, self, TensorFunction["Cast"] @ "Apply"[self, "Type" -> type]]
Tensor["Float"[self_]] := self["Cast"["Float32"]]
Tensor["Double"[self_]] := self["Cast"["Float64"]]
Tensor["Half"[self_]] := self["Cast"["Float16"]]

Tensor["Contiguous"[self_]] := TensorFunction["Contiguous"] @ "Apply"[self]
Tensor["Log"[self_]] := TensorFunction["Log"] @ "Apply"[self]
Tensor["Log2"[self_]] := TensorFunction["Log"] @ "Apply"[self] / Log[2]
Tensor["Exp"[self_]] := TensorFunction["Exp"] @ "Apply"[self]
Tensor["ReLU"[self_]] := TensorFunction["ReLU"] @ "Apply"[self]
Tensor["Sigmoid"[self_]] := TensorFunction["Sigmoid"] @ "Apply"[self]
Tensor["Sin"[self_]] := TensorFunction["Sin"] @ "Apply"[self]
Tensor["Sqrt"[self_]] := TensorFunction["Sqrt"] @ "Apply"[self]
Tensor["RSqrt"[self_]] := (1 / self)["Sqrt"[]]
Tensor["Cos"[self_]] := (Pi / 2 - self)["Sin"[]]
Tensor["Tan"[self_]] := self@"Sin"[] / self@"Cos"[]

Tensor["Broadcast"[self_, f_, others___]] :=
    Fold[
        Block[{x = #1, y = Tensor[#2, #1["Device"], #1["Type"]], shape},
            If[x["Shape"] === y["Shape"], Return[TensorFunction[f] @ "Apply"[x, y]]];
            xRank = Length[x["Shape"]];
            yRank = Length[y["Shape"]];
            rank = Max[xRank, yRank];
            If[xRank != rank, x = x["Reshape"[Join[ConstantArray[1, rank - xRank], x["Shape"]]]]];
            If[yRank != rank, y = y["Reshape"[Join[ConstantArray[1, rank - yRank], y["Shape"]]]]];
            shape = MapThread[Max, {x["Shape"], y["Shape"]}];
            If[x["Shape"] != shape, x = x["Expand"[shape]]];
            If[y["Shape"] != shape, y = y["Expand"[shape]]];
            TensorFunction[f] @ "Apply"[x, y]
        ] &,
        self,
        {others}
    ]


StaticMethod[
Tensor["LoadOp"[NameValuePattern[op_, size_, device_ : None, type_ : None, arg_ : None], opts___]] :=
    Tensor[
        LazyBuffer @ "LoadOp"[
            op, {size},
            If[type === None, Tensor["Type"], type],
            If[device === None, Tensor["Device"], device],
            arg
        ],
        opts
    ]
]

(* RNG *)
StaticMethod[
Tensor["Rand"[shape : Shape, opts : OptionsPattern[]]] := Tensor["LoadOp"["RAND", Times @@ shape, "arg" -> Tensor["Seed"], opts]] @ "Reshape"[shape]
]