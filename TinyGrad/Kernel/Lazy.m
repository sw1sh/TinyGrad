Package["TinyGrad`"]

PackageExport[LazyBuffer]



Class[LazyBuffer,
    "$Init"[self_, device_String, st_::[ShapeTracker], op_::[LazyOp], type_String, src_ : None] :> (
        {self["ShapeTracker"], self["Device"], self["Op"], self["Type"], self["Realized"]} = {st, device, op, type, src};
        self["OutputBuffer"] = None;
        self["Children"] = {};
        self["Op"] = op;
        self
    ),
    "$Properties" -> {"Shape", "Key", "OpName", "Buffers"},
    "Shape"[self_] :> self["ShapeTracker"]["Shape"],
    "OpName"[self_] :> self["Op"]["Op"],
    "Key"[self_] :> {self["Type"], If[self["Realized"] =!= None, self["Realized"]["Key"], self["Op"]], self["ShapeTracker"]["Key"]}
]


LazyBuffer[device_, shapeTracker_, op_, type_, src_ : None] :=
    LazyBuffer["New"[
        device,
        shapeTracker,
        op,
        type,
        src
    ]]

LazyBuffer["Realize"[self_]] := (
    If[ self["Realized"] === None,
        If[ MemberQ[$LoadOps, self["OpName"]],
            DispatchLoadOp[self["OpName"]][self],
            self["Realized"] = Device[self["Device"]]["Execute"[self["Op"], self]]
        ]
    ];
    self
)

LazyBuffer["LoadOp"[op_, shape_, type_, device_, arg_ : None, src_ : None]] :=
    LazyBuffer[device, ShapeTracker[shape], LazyOp[op, If[src === None, {}, {src}], arg], type]

LazyBuffer["FromCPU"[x : _ ? NumericArrayQ]] :=
    LazyBuffer["CPU", ShapeTracker[Dimensions[x], {View[Dimensions[x]]}], LazyOp["EMPTY", {}], NumericArrayType[x], RawArrayBuffer["FromCPU"[x]]]

LazyBuffer["ConstLike"[self_, val_]] := self @* "LoadOp"["CONST", {}, self["Type"], self["Device"], val] @* "Reshape"[ConstantArray[1, Length[self["Shape"]]]] @* "Expand"[self["Shape"]]

LazyBuffer["ToCPU"[self_]] := self @* "Contiguous"[] @* "Realize"[] @* "Realized"

LazyBuffer["Cast"[self_, type_]] := If[type === self["Type"], self, ElementwiseOp["CAST", self, type]]

LazyBuffer["UnaryOp"[self_, op_]] := ElementwiseOp[op, self]

LazyBuffer["BinaryOp"[self_, op_, y_::[LazyBuffer]]] := ElementwiseOp[op, self, y]

LazyBuffer["TernaryOp"[self_, op_, y_::[LazyBuffer], z_::[LazyBuffer]]] := ElementwiseOp[op, self, y, z]

LazyBuffer["Contiguous"[self_]] := If[
    self["Realized"] =!= None && self["OpName"] === "CONTIGUOUS",
    self,
    LazyBuffer[self["Device"], ShapeTracker[self["Shape"]], LazyOp["CONTIGUOUS", {self}], self["Type"]]
]

LazyBuffer["Permute"[self_, perm_List]] := Block[{},

    If[ perm === Range[Length[self["Shape"]]], Return[self]];
    If[ self["Realized"] =!= None && self["OpName"] === "PERMUTE", Return[self["Op"]["Source"][[1]]["Permute"[self["Op"]["Argument"][[perm]]]]]];
    (* TODO: Optimizations *)
    LazyBuffer[self["Device"], self["ShapeTracker"]["Permute"[perm]], LazyOp["PERMUTE", {self}, perm], self["Type"]]
]

LazyBuffer["Buffers"[self_]] := {self}

LazyBuffer["$Format"[self_, form_]] :=
    BoxForm`ArrangeSummaryBox[
        "LazyBuffer",
        self,
        None,
        {
            BoxForm`SummaryItem[{"Shape: ", self["Shape"]}],
            BoxForm`SummaryItem[{"Type: ", self["Type"]}],
            BoxForm`SummaryItem[{"Op: ", self["Op"]}]
        },
        {{BoxForm`SummaryItem[{"Realized: ", self["Realized"] =!= None}]}},
        form
    ]

Device = <|"CPU" -> CPUBuffer|>


RealizeContiguous[buffer_::[LazyBuffer]] := Block[{
    realized = buffer["Op"]["Source"][[1]]["Realize"[]]["Realized"]
},
    If[
        buffer["Op"]["Source"][[1]]["ShapeTracker"]["ContiguousQ"] &&
        realized["$Class"] =!= RawConst &&
        realized["Size"] == Times @@ buffer["Shape"],

        buffer["Realized"] = realized,

        buffer["Op"] = LazyOp["New"["NOOP", buffer["Op"]["Source"]]]
    ]
]

RealizeCustom[buffer_::[LazyBuffer]] :=
    buffer["Realized"] = buffer["Op"]["Argument"][buffer, Sequence @@ Through[buffer["Op"]["Source"]["Realize"]]]

RealizeEmpty[buffer_::[LazyBuffer]] :=
    buffer["Realized"] = Device[buffer["Device"]]["Buffer"][Times @@ buffer["Shape"], buffer["Type"], Sequence @@ buffer["DeviceExtraArgs"]]

ElementwiseOp[op_, srcs : PatternSequence[x_, ___], arg : Except[_::[LazyBuffer]] : None] := With[{
    device = x["Device"], shape = x["Shape"],
    type = If[op === "CAST", Replace[arg, None :> Tensor["Type"]], Commonest[Through[{srcs}["Type"]]]]
},
    LazyBuffer[device, ShapeTracker[shape], LazyOp[op, {srcs}, arg], type]
]

DispatchLoadOp = <|
    "EMPTY" -> RealizeEmpty,
    "CONTIGUOUS" -> RealizeContiguous
|>