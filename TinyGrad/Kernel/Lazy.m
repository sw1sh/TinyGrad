Package["TinyGrad`"]

PackageExport[LazyBuffer]

PackageImport["Wolfram`Class`"]



Class[LazyBuffer,
    "$Init"[self_, device_String, st_::[ShapeTracker], op_::[LazyOp], type_String, src_ : None] :> (
        {self["ShapeTracker"], self["Device"], self["Op"], self["Type"], self["Realized"]} = {st, device, op, type, src};
        self["OutputBuffer"] = None;
        self["Children"] = {};
        self["Op"] = op;

        Plus[self, y_] ^:= ElementwiseOp["ADD", self, y];
        Subtract[self, y_] ^:= ElementwiseOp["SUB", self, y];
        Times[self, y_] ^:= ElementwiseOp["MUL", self, y];
        Divide[self, y_] ^:= ElementwiseOp["DIV", self, y];
        Power[self, y_] ^:= ElementwiseOp["EXP2", ElementwiseOp["MUL", y, ElementwiseOp["LOG2", self]]];
        Minus[self] ^:= ElementwiseOp["SUB", 0, self];

        self
    ),
    "$StaticMethods" -> {"FromCPU", "LoadOp"},
    "$Properties" -> {"Shape", "Rank", "Key", "OpName", "Buffers", "RealizedQ"},
    "Shape"[self_] :> self["ShapeTracker"]["Shape"],
    "Rank"[self_] :> Length[self["Shape"]],
    "OpName"[self_] :> self["Op"]["Op"],
    "Key"[self_] :> {self["Type"], If[self["Realized"] =!= None, self["Realized"]["Key"], self["Op"]], self["ShapeTracker"]["Key"]},
    "RealizedQ"[self_] :> self["Realized"] =!= None,
    "$Normal"[self_] :> self["ToCPU"[]],
]


LazyBuffer[device_, shapeTracker_, op_, type_, src_ : None] :=
    LazyBuffer["$New"[
        device,
        shapeTracker,
        op,
        type,
        src
    ]]

LazyBuffer::realize = "Failed to realize ``"

LazyBuffer["Realize"[self_]] := Enclose[
    If[ self["Realized"] === None,
        If[ MemberQ[$LoadOps, self["OpName"]],
            Confirm @ DispatchLoadOp[self["OpName"]][self]
        ];
        If[ self["Realized"] === None,
            Scan[Confirm[# @ "Realize"[]] &, self["Op"]["Buffers"]];
            self["Realized"] = Confirm @ Device[self["Device"]]["Execute"[self["Op"], self]]
        ];
    ];
    self,
    (Message[LazyBuffer::realize, self]; #) &
]

LazyBuffer["LoadOp"[op_, shape_, type_, device_, arg_ : None, src_ : None]] :=
    LazyBuffer[device, ShapeTracker[shape], LazyOp[op, If[src === None, {}, {src}], arg], type]

LazyBuffer["FromCPU"[x : _ ? NumericArrayQ]] :=
    LazyBuffer["CPU", ShapeTracker[Dimensions[x], {View[Dimensions[x]]}], LazyOp["EMPTY", {}], NumericArrayType[x], RawArrayBuffer["FromCPU"[x]]]

LazyBuffer["ConstLike"[self_, val_]] := self @* "LoadOp"["CONST", {}, self["Type"], self["Device"], N[val]] @* "Reshape"[ConstantArray[1, Length[self["Shape"]]]] @* "Expand"[self["Shape"]]

LazyBuffer["ToCPU"[self_]] := Enclose @ Block[{realized},
    realized = Confirm[self @* "Contiguous"[] @* "Realize"[]] @* "Realized" @* "ToCPU"[];
    If[Length[self["Shape"]] > 0, ArrayReshape[realized, self["Shape"]], realized]
]

LazyBuffer["Cast"[self_, type_]] := If[type === self["Type"], self, ElementwiseOp["CAST", self, "Argument" -> type]]

LazyBuffer["UnaryOp"[self_, op_]] := ElementwiseOp[op, self]

LazyBuffer["BinaryOp"[self_, op_, y_]] := ElementwiseOp[op, self, y]

LazyBuffer["TernaryOp"[self_, op_, y_, z_]] := ElementwiseOp[op, self, y, z]

LazyBuffer["ReduceOp"[self_, op_, lvl_ : 1]] := With[{shape = MapAt[1 &, self["Shape"], LevelSpan[lvl]]},
     LazyBuffer[self["Device"], ShapeTracker[shape], LazyOp[op, {self}, lvl], self["Type"]]
]

LazyBuffer["Contiguous"[self_]] := If[
    self["Realized"] =!= None && self["OpName"] === "CONTIGUOUS",
    self,
    LazyBuffer[self["Device"], ShapeTracker[self["Shape"]], LazyOp["CONTIGUOUS", {self}], self["Type"]]
]

LazyBuffer["Permute"[self_, perm_List]] := Block[{},

    If[ perm === Range[Length[self["Shape"]]], Return[self]];
    If[ self["Realized"] =!= None && self["OpName"] === "PERMUTE", Return[self["Op"]["Source"][[1]]["Permute"[self["Op"]["Argument"][[perm]]]]]];
    (* TODO: Optimizations *)
    LazyBuffer[self["Device"], self["ShapeTracker"] @* "$Extend" @* "Permute"[perm], LazyOp["PERMUTE", {self}, perm], self["Type"]]
]

LazyBuffer["Expand"[self_, dims_List]] := Block[{},
    If[ dims === self["Shape"], Return[self]];
    If[ self["Realized"] =!= None && self["OpName"] === "EXPAND", Return[self["Op"]["Source"][[1]]["Expand"[dims]]]];
    LazyBuffer[self["Device"], self["ShapeTracker"] @* "$Extend" @* "Expand"[dims], LazyOp["EXPAND", {self}, dims], self["Type"]]
]

LazyBuffer["Reshape"[self_, shape_]] := (
    If[ shape === self["Shape"], Return[self]];
    If[ self["Realized"] =!= None && self["OpName"] === "RESHAPE",
        Return[self["Op"]["Source"][[1]]["Reshape"[shape]]]
    ];
    LazyBuffer[self["Device"], self["ShapeTracker"] @* "$Extend" @* "Reshape"[shape], LazyOp["RESHAPE", {self}, shape], self["Type"]]
)

LazyBuffer["Buffers"[self_]] := {self}

LazyBuffer["$Format"[self_, form_]] :=
    BoxForm`ArrangeSummaryBox[
        "LazyBuffer",
        self,
        None,
        {
            BoxForm`SummaryItem[{"Shape: ", self["Shape"]}],
            BoxForm`SummaryItem[{"Type: ", self["Type"]}],
            BoxForm`SummaryItem[{"Op: ", self["Op"]}],
            BoxForm`SummaryItem[{"Realized: ", self["Realized"] =!= None}]
        },
        {{}},
        form
    ]

Device = <|"CPU" -> CPUBuffer|>


RealizeContiguous[buffer_::[LazyBuffer]] := Enclose @ Block[{
    realized = Confirm[buffer["Op"]["Source"][[1]]["Realize"[]]]["Realized"]
},
    If[
        buffer["Op"]["Source"][[1]]["ShapeTracker"]["ContiguousQ"] &&
        realized["$Class"] =!= RawConst &&
        realized["Size"] == Times @@ buffer["Shape"],

        buffer["Realized"] = realized,

        buffer["Op"] = LazyOp["$New"["NOOP", buffer["Op"]["Source"]]]
    ]
]

RealizeConst[buffer_::[LazyBuffer]] :=
    buffer["Realized"] = Device[buffer["Device"]]["Buffer"]["FromCPU"[StridedArray[buffer["Op"]["Argument"]]]]

RealizeCustom[buffer_::[LazyBuffer]] :=
    buffer["Realized"] = Enclose @ buffer["Op"]["Argument"][buffer, Sequence @@ ConfirmBy[Through[buffer["Op"]["Source"]["Realize"]], AllTrue[Not @* FailureQ]]]

RealizeEmpty[buffer_::[LazyBuffer]] :=
    buffer["Realized"] = Device[buffer["Device"]]["Buffer"][Times @@ buffer["Shape"], buffer["Type"], Sequence @@ buffer["DeviceExtraArgs"]]

ElementwiseOp[op_, inputs : Except[_Rule] .., OptionsPattern[{"Argument" -> None}]] := Enclose @ Block[{
    firstSrc = Confirm @ First[MaximalBy[Select[{inputs}, LazyBuffer["$Test"]], #["Rank"] &], Missing[]],
    device, shape,
    type, srcs
},
    device = firstSrc["Device"];
    shape = firstSrc["Shape"];
    srcs = If[LazyBuffer["$Test"][#], If[#["Shape"] =!= firstSrc["Shape"], #["Expand"[firstSrc["Shape"]]], #], firstSrc["ConstLike"[#]]] & /@ {inputs};
    type = If[op === "CAST", Replace[OptionValue["Argument"], None :> Tensor["Type"]], firstSrc["Type"]];
    LazyBuffer[device, ShapeTracker[shape], LazyOp[op, srcs, OptionValue["Argument"]], type]
]

DispatchLoadOp = <|
    "EMPTY" -> RealizeEmpty,
    "CONTIGUOUS" -> RealizeContiguous,
    "CONST" -> RealizeConst
|>