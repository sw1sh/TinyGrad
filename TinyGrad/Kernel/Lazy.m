Package["TinyGrad`"]

PackageExport[LazyBuffer]

PackageImport["Wolfram`Class`"]



Class[LazyBuffer,
    "$Init"[self_, device_String, st_::[ShapeTracker], op_::[LazyOp], type_String, src_ : None] :> (
        {self["ShapeTracker"], self["Device"], self["Op"], self["Type"], self["Realized"]} = {st, device, op, type, src};
        self["OutputBuffer"] = None;
        self["Op"] = op;
        self["Children"] = {};

        Scan[(#["Children"] //= Append[self]) &, op["Buffers"]];

        Plus[self, y_] ^:= ElementwiseOp["ADD", self, y];
        Subtract[self, y_] ^:= ElementwiseOp["SUB", self, y];
        Times[self, y_] ^:= ElementwiseOp["MUL", self, y];
        Divide[self, y_] ^:= ElementwiseOp["DIV", self, y];
        Power[self, y_] ^:= ElementwiseOp["EXP2", ElementwiseOp["MUL", y, ElementwiseOp["LOG2", self]]];
        Minus[self] ^:= ElementwiseOp["SUB", 0, self];
        Less[self, y_] ^:= ElementwiseOp["CMPLT", self, y];
        Greater[self, y_] ^:= ElementwiseOp["CMPLT", y, self];
        self
    ),
    "$StaticMethods" -> {"FromCPU", "LoadOp"},
    "$Properties" -> {"Shape", "Rank", "Key", "OpName", "Buffers", "RealizedQ"},
    "Shape"[self_] :> self["ShapeTracker"]["Shape"],
    "Rank"[self_] :> Length[self["Shape"]],
    "OpName"[self_] :> self["Op"]["Op"],
    "Key"[self_] :> {self["Type"], If[self["Realized"] =!= None, self["Realized"]["Key"], self["Op"]], self["ShapeTracker"]["Key"]},
    "RealizedQ"[self_] :> self["Realized"] =!= None,
    "$Normal"[self_] :> self["ToCPU"[]]
]


LazyBuffer[args__] := LazyBuffer["$New"[args]]

LazyBuffer::realize = "Failed to realize ``"

LazyBuffer["Realize"[self_]] := Enclose[
    If[ self["Realized"] === None,
        If[ MemberQ[$LoadOps, self["OpName"]],
            Confirm @ DispatchLoadOp[self["OpName"]][self]
        ];
        If[ MemberQ[$ReduceOps, self["OpName"]],
            self["Op"] = Confirm @ RealizeReduceOps[self]
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

LazyBuffer["Const"[self_, val_]] := self @* "LoadOp"["CONST", {}, self["Type"], self["Device"], N[val]] @* "Reshape"[ConstantArray[1, Length[self["Shape"]]]] @* "Expand"[self["Shape"]]

LazyBuffer["ToCPU"[self_]] := Enclose @ Block[{realized},
    realized = Confirm[self @* "Contiguous"[] @* "Realize"[]] @* "Realized" @* "ToCPU"[];
    If[Length[self["Shape"]] > 0, ArrayReshape[realized, self["Shape"]], realized]
]

LazyBuffer["Cast"[self_, type_]] := If[type === self["Type"], self, ElementwiseOp["CAST", self, "Argument" -> type]]

LazyBuffer["Elementwise"[self_, op_, others___]] := ElementwiseOp[op, self, others]

LazyBuffer["ReduceOp"[self_, op_, lvl_ : 1]] := With[{shape = MapAt[1 &, self["Shape"], LevelSpan[lvl]]},
     LazyBuffer[self["Device"], ShapeTracker[shape], LazyOp[op, {self}, lvl], self["Type"]]
]

LazyBuffer["Contiguous"[self_]] := If[
    self["Realized"] =!= None && self["OpName"] === "CONTIGUOUS",
    self,
    LazyBuffer[self["Device"], ShapeTracker[self["Shape"]], LazyOp["CONTIGUOUS", {self}], self["Type"]]
]

LazyBuffer["Permute"[self_, order_List]] := Enclose[

    If[ order === Range[Length[self["Shape"]]], Return[self]];
    If[ self["Realized"] =!= None && self["OpName"] === "PERMUTE", Return[self["Op"]["Source"][[1]]["Permute"[self["Op"]["Argument"][[order]]]]]];
    (* TODO: Optimizations *)
    LazyBuffer[self["Device"], Confirm[ShapeTracker[self["ShapeTracker"]] @ "Permute"[order]], LazyOp["PERMUTE", {self}, order], self["Type"]]
]

LazyBuffer["Expand"[self_, dims_List]] := Enclose[
    If[ dims === self["Shape"], Return[self]];
    If[ self["Realized"] =!= None && self["OpName"] === "EXPAND", Return[self["Op"]["Source"][[1]]["Expand"[dims]]]];
    LazyBuffer[self["Device"], Confirm @ ShapeTracker[self["ShapeTracker"]] @ "Expand"[dims], LazyOp["EXPAND", {self}, dims], self["Type"]]
]

LazyBuffer["Reshape"[self_, shape_]] := Enclose[
    If[ shape === self["Shape"], Return[self]];
    If[ self["Realized"] =!= None && self["OpName"] === "RESHAPE",
        Return[self["Op"]["Source"][[1]]["Reshape"[shape]]]
    ];
    LazyBuffer[self["Device"], Confirm @ ShapeTracker[self["ShapeTracker"]] @ "Reshape"[shape], LazyOp["RESHAPE", {self}, shape], self["Type"]]
]

LazyBuffer["Pad"[self_, padding_ : {{_Integer ? NonNegative, _Integer ? NonNegative} ...}]] := Enclose[
    If[ MatchQ[padding, {{0, 0} ...}], Return[self]];
    If[ self["Realized"] =!= None && self["OpName"] === "PAD",
        Return[self["Op"]["Source"][[1]]["Pad"[self["Op"]["Argument"] + padding]]]
    ];
    LazyBuffer[self["Device"], Confirm @ ShapeTracker[self["ShapeTracker"]] @ "Pad"[padding], LazyOp["PAD", {self}, padding], self["Type"]]
]

LazyBuffer["Shrink"[self_, shrink : {{_Integer ? NonNegative, _Integer ? NonNegative} ...}]] := Enclose[
    If[ ReverseApplied[Subtract] @@@ shrink === shape, Return[self]];
    If[ self["Realized"] =!= None && self["OpName"] === "SHRINK",
        Return[self["Op"]["Source"][[1]]["Shrink"[self["Op"]["Argument"][[All, 1]] + shrink]]]
    ];
    LazyBuffer[self["Device"], Confirm @ ShapeTracker[self["ShapeTracker"]] @ "Shrink"[shrink], LazyOp["SHRINK", {self}, shrink], self["Type"]]
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
            BoxForm`SummaryItem[{"Op: ", InputForm @ self["Op"]}],
            BoxForm`SummaryItem[{"Realized: ", self["Realized"] =!= None}]
        },
        {BoxForm`SummaryItem[{"ShapeTracker: ", self["ShapeTracker"]}]},
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
    buffer["Realized"] = Device[buffer["Device"]]["Buffer"][Times @@ buffer["Shape"], buffer["Type"]]

RealizeRand[buffer_::[LazyBuffer]] :=
    buffer["Realized"] = Device[buffer["Device"]]["Buffer"]["FromCPU"[StridedArray[SeedRandom[buffer["Op"]["Argument"]]; RandomReal[1, buffer["Shape"]]]]]

ElementwiseOp[PatternSequence[op_, inputs___], OptionsPattern[{"Argument" -> None}]] := Enclose @ Block[{
    firstSrc = Confirm @ First[MaximalBy[Select[{inputs}, LazyBuffer["$Test"]], #["Rank"] &], Missing[]],
    device, shape,
    type, srcs
},
    device = firstSrc["Device"];
    shape = firstSrc["Shape"];
    srcs = If[LazyBuffer["$Test"][#], If[#["Shape"] =!= firstSrc["Shape"], #["Expand"[firstSrc["Shape"]]], #], firstSrc["Const"[#]]] & /@ {inputs};
    type = If[op === "CAST", Replace[OptionValue["Argument"], None :> Tensor["Type"]], firstSrc["Type"]];
    LazyBuffer[device, ShapeTracker[shape], LazyOp[op, srcs, OptionValue["Argument"]], type]
]

DispatchLoadOp = <|
    "EMPTY" -> RealizeEmpty,
    "CONTIGUOUS" -> RealizeContiguous,
    "CONST" -> RealizeConst,
    "RAND" -> RealizeRand
|>

RealizeReduceOps[buffer_] := Enclose @ Block[{
    src = buffer["Op"]["Source"][[1]]
},
    If[ ! src["RealizedQ"],
        If[ src["OpName"] === "EXPAND",
            Block[{expanded, reshaped, simplified = None},
                expanded = src["Op"]["Source"][[1]];
                If[ expanded["OpName"] === "RESHAPE",
                    reshaped = expanded["Op"]["Source"][[1]];
                    simplified = simplifySumReshapeExpandSum[buffer, reshaped, src],

                    simplified = simplifySumReshapeExpandSum[buffer, expanded, src]
                ];
                If[simplified =!= None, Return[simplified]];
            ]
        ];
        If[ MemberQ[$BinaryOps, src["OpName"]] && Length[src["Children"]] <= 1,
            If[src["Shape"] === buffer["Shape"], Return[src["Op"]]];
            src = src["Op"]
        ]
    ];
    LazyOp[buffer["OpName"], {src}, buffer["Op"]["Argument"]]
]

simplifySumReshapeExpandSum[buffer_, src_, prevSrc_] := Enclose[
    If[ prevSrc["OpName"] === "EXPAND" &&
        src["OpName"] === "SUM" &&
        src["Shape"] === buffer["Shape"],

        With[{
            shapeDiff = MapThread[If[#1 == #2, Nothing, #1] &, {prevSrc["Shape"], buffer["Shape"]}]
        },
            If[ Length[shapeDiff] == 1,
                Return[LazyOp["MUL", {src, src["Const"[First[shapeDiff]]]}]];
            ]
        ]
    ];
    None
]

