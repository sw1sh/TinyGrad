Package["TinyGrad`"]

PackageExport[LazyBuffer]



Class[LazyBuffer,
    "Init"[self_, device_String, st_::[ShapeTracker], op_::[LazyOp], type_String, src_ : None] :> (
        {self["ShapeTracker"], self["Device"], self["Op"], self["Type"], self["Realized"]} = {st, device, op, type, src};
        self["OutputBuffer"] = None;
        self["Children"] = {};
        self["Op"] = op;
        self
    ),
    "Properties" -> {"Shape", "Key"},
    "Shape"[self_] :> self["ShapeTracker"]["Shape"],
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
        self["Realized"] = Device[self["Device"]]["Execute"[self["Op"], self, Sequence @@ self["DeviceExtraArguments"]]]
    ];
    self
)

LazyBuffer["LoadOp"[op_, shape_, type_, device_, arg_ : None, src_ : None]] :=
    LazyBuffer[device, ShapeTracker[shape], op[If[src === None, {}, {src}], arg], type]

LazyBuffer["FromCPU"[x : _ ? NumericArrayQ]] :=
    LazyBuffer["CPU", ShapeTracker[Dimensions[x], {View[Dimensions[x]]}], LazyOp["EMPTY", {}], NumericArrayType[x]]

LazyBuffer["ConstLike"[self_, val_]] := self @* "LoadOp"["CONST", {}, self["Type"], self["Device"], val] @* "Reshape"[ConstantArray[1, Length[self["Shape"]]]] @* "Expand"[self["Shape"]]

LazyBuffer["ToCPU"[self_]] := self @* "Contiguous"[] @* "Realize"[] @* "Realized"


LazyBuffer["Buffers"[self_]] := {self}

LazyBuffer["Format"[self_, form_]] :=
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


RealizeContiguous[buffer : LazyBuffer["Pattern"]] := Block[{
    realized = buffer["Op"]["Source"][[1]]["Realize"[]]["Realized"]
},
    If[
        buffer["Op"]["Source"][[1]]["ShapeTracker"]["ContiguousQ"] &&
        realized["Class"] =!= RawConst &&
        realized["Size"] == Times @@ buffer["Shape"],

        buffer["Realized"] = realized,

        buffer["Op"] = LazyOp["New"["NOOP", buffer["Op"]["Source"]]]
    ]
]

RealizeCustom[buffer : LazyBuffer["Pattern"]] :=
    buffer["Realized"] = buffer["Op"]["Argument"][buffer, Sequence @@ Through[buffer["Op"]["Source"]["Realize"]]]

RealizeEmpty[buffer : LazyBuffer["Pattern"]] :=
    buffer["Realized"] = Device[buffer["Device"]]["Buffer"][Times @@ buffer["Shape"], buffer["Type"], Sequence @@ buffer["DeviceExtraArgs"]]

