Package["TinyGrad`"]

PackageExport[Tensor]

PackageImport["Wolfram`Class`"]



Options[Tensor] = {"Device" -> None, "Type" -> None, "RequiresGradient" -> None}

TensorData = _::[Tensor] | _::[LazyBuffer] | _? ArrayQ | _ ? NumericArrayQ | _ ? NumericQ

Class[Tensor,
    "Training" -> False, "NoGradient" -> False, "Type" -> "Real32", "Device" -> "CPU", "Seed" -> 0,

    "$Init"[NameValuePattern[
        self_,
        Data : TensorData,
        Device : _String | None : None,
        Type : _String | None : None,
        RequiresGradient : _ ? BooleanQ | None : True
    ]] :> Enclose @ Block[{
        data = Data,
        device = Replace[Device, None :> "CPU"],
        type = Replace[Type, None :> Tensor["Type"]]
    },
        If[ Tensor["$Test"][data],
            self["Gradient"] = data["Gradient"];
            self["RequiresGradient"] = Replace[RequiresGradient, None :> data["RequiresGradient"]];
            self["Context"] = data["Context"];
            data = data["LazyData"];
            ,
            self["Gradient"] = None;
            self["RequiresGradient"] = RequiresGradient;
            self["Context"] = None
        ];

        SetUpValues[self];

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

SetUpValues[self_] := (
    Plus[self, ts___] ^:= Fold[TensorFunction["Add"] @ ("Apply" @@ #1["Broadcast"[#2]]) &, self, {ts}];
    Times[self, ts___] ^:= Fold[TensorFunction["Mul"] @ ("Apply" @@ #1["Broadcast"[#2]]) &, self, {ts}];
    Power[self, ts___] ^:= Fold[TensorFunction["Pow"] @ ("Apply" @@ #1["Broadcast"[#2]]) &, self, {ts}];

    Less[self, t_] ^:= TensorFunction["Less"] @ ("Apply" @@ self["Broadcast"[t, "Reverse" -> False]]);
    Greater[self, t_] ^:= TensorFunction["Less"] @ ("Apply" @@ self["Broadcast"[t, "Reverse" -> True]]);
    LessEqual[self, t_] ^:= 1 - (self > t);
    GreaterEqual[self, t_] ^:= 1 - (self < t);
    Unequal[self, t_] ^:= (self < t) + (self > t);
    Equal[self, t_] ^:= 1 - (self != t);

    If[self, true_, false_] ^:= self["Where"[true, false]];

    Dot[self, w_] ^:= Enclose @ Block[{shape1 = self["Shape"], shape2 = w["Shape"], n1 = self["Rank"], n2 = w["Rank"], i, x, y},
        i = - Min[n2, 2];
        ConfirmAssert[n1 > 0 && n2 > 0];
        ConfirmAssert[shape1[[-1]] === shape2[[i]]];
        x = self @ "Reshape"[Join[shape1[[;; -2]], ConstantArray[1, Min[n1 - 1, n2 - 1, 1]], shape1[[-1 ;;]]]];
        y = w @* "Reshape"[Join[shape2[[;; -3]], ConstantArray[1, Min[n1 - 1, n2 - 1, 1]], shape2[[i ;; ]]]] @* "Transpose"[-1, i];
        (x * y) @ "Sum"[-1]
    ];

    Accumulate[self, axis_Integer : 0] ^:= self @* "Transpose"[axis, -1] @* "Pad2D"[{self["Shape"][[AxisPart[axis]]] - 1, 0}] @* "Pool"[{self["Shape"][[AxisPart[axis]]]}] @* "Sum"[{-1}] @* "Transpose"[axis, -1];

    Transpose[self, arg_ : {2, 1}] ^:= self[Replace[arg, {i_ <-> j_ :> "Transpose"[i - 1, j - 1], order_List :> "Permute"[Ordering[order]], cycles_Cycles :> "Permute"[Ordering[PermutationList[cycles]]]}]];

    Part[self, args___] ^:= Enclose @ Block[{shape = self["Shape"], shrink, axes, result},
        axes = First[Reap[shrink = MapIndexed[
            Confirm @ Replace[#1, {
                Span[i_Integer ? Positive, j_Integer ? Positive] -> {i - 1, j},
                i_Integer ? Positive :> (Sow[#2]; {i - 1, i}),
                All -> {0, shape[[#2[[1]]]]},
                _ -> $Failed
            }] &,
            PadRight[{args}, Length[shape], All]
        ]][[2]], {}];
        result = TensorFunction["Shrink"] @ "Apply"[self, "Shrink" -> shrink];
        If[ Length[axes] > 0,
            TensorFunction["Reshape"] @ "Apply"[result, "Shape" -> Delete[result["Shape"], axes]],
            result
        ]
    ];

    Total[self, lvl_ : 1] ^:=
        TensorFunction["Reshape"] @ "Apply"[TensorFunction["Sum"] @ "Apply"[self, "Level" -> lvl], "Shape" -> Drop[self["Shape"], lvl]];

    D[self, t_] ^:= Enclose[t["Gradient"] = None; Confirm @ self["Backward"[]]; t["Gradient"]];

    f_Symbol[self] /; MemberQ[Attributes[f], NumericFunction] ^:= self[SymbolName[f][]];
)

Tensor[args___] := Tensor["$New"[args]]

Tensor["$Properties"] = {"Device", "Shape", "Type", "$Normal", "Rank", "Dimension", "Graph"}

Tensor[(prop : "Device" | "Shape" | "Type" | "Rank")[self_]] := self["LazyData"][prop]

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

Tensor["Unsqueeze"[self_, axis_Integer : 0]] := self["Reshape"[Join[self["Shape"][[;; AxisPart[axis] - 1]], {1}, self["Shape"][[AxisPart[axis] ;;]]]]]

Tensor["Squeeze"[self_, axis : _Integer | {___Integer} | None : None]] := self["Reshape"[Delete[self["Shape"], List /@ Developer`ToList @ Replace[axis, None :> Catenate @ Position[self["Shape"], 1]]]]]

Tensor["Flatten"[self_, axis_ : 0]] := self["Reshape"[Append[-1] @ self["Shape"][[;; AxisPart[axis] - 1]]]]

Tensor["Expand"[self_, shape_]] := TensorFunction["Expand"] @ "Apply"[self, "Shape" -> shape]

Tensor["Shrink"[self_, shrink : {{_Integer ? NonNegative, _Integer ? NonNegative} ...}]] := If[
    Or @@ Unequal @@@ Thread[{shrink, {0, #} & /@ self["Shape"]}],
    TensorFunction["Shrink"] @ "Apply"[self, "Shrink" -> shrink],
    self
]

Tensor["Pad"[self_, padding : {{_Integer ? NonNegative, _Integer ? NonNegative} ...}, value_ : 0]] := Enclose @ Block[{result},
    If[MatchQ[padding, {{0, 0} ...}], Return[self]];
    result = TensorFunction["Pad"] @ "Apply"[self, "Padding" -> padding];
    If[value == 0, Return[result]];
    result + (value - Tensor["Full"[self["Shape"], value]]["Pad"[padding]])
]

Tensor["Slice"[self_, slice : {({_Integer, _Integer} | All) ...}, value_ : 0]] := Block[{islice, padding, shrink},
    islice = MapThread[Replace[#1, All :> {0, #2}] &, {slice, self["Shape"]}];
    padding = MapThread[{Max[0, - #1[[1]]], Max[0, #1[[2]] - #2]} &, {islice, self["Shape"]}];
    shrink = islice + padding[[All, 1]];
    self @* "Pad"[padding, value] @* "Shrink"[shrink]
]

Tensor["Pad2D"[self_, padding : {_Integer ...}, value_ : 0]] := Enclose @ Block[{slice, n = Quotient[Length[padding], 2]},
    slice = Reverse @ MapThread[{- #1, #2 + #3} &, {padding[[;; ;; 2]], padding[[2 ;; ;; 2]], Reverse[Take[self["Shape"], - n]]}];
    self @ "Slice"[Join[Thread[{0, Drop[self["Shape"], - n]}], slice], value]
]

Tensor["Pool"[self_, k : {__Integer}, stride : _Integer | {__Integer} : 1, dilation : _Integer | {__Integer} : 1]] := Enclose @ Block[{
    shape = self["Shape"], rank = self["Rank"], kRank = Length[k], pRank,
    prefix, slicePrefix, i,
    s, d, o, e, xup
},
    ConfirmAssert[rank >= kRank];

    s = Replace[stride, i_Integer :> ConstantArray[i, kRank]];
    d = Replace[dilation, i_Integer :> ConstantArray[i, kRank]];
    ConfirmAssert[kRank == Length[s] && kRank == Length[d]];

    prefix = shape[[;; - kRank - 1]];
    slicePrefix = Thread[{0, prefix}];
    i = shape[[- kRank ;;]];
    pRank = rank - kRank;

    If[ Or @@ Thread[k > s] || AnyTrue[d, # != 1 &],
        o = Quotient[i - d * (k - 1) - 1, s] + 1;
        e = Ceiling[k * (i + d) / i];

        xup = self @* "Reshape"[Join[prefix, Catenate @ Thread[{1, i}]]] @* "Expand"[Join[prefix, Catenate @ Thread[{e, i}]]] @* "Reshape"[Join[prefix, e * i]];
        (* slide by dilation *)
        xup = xup @ "Slice"[Join[slicePrefix, Thread[{0, k * (i + d)}]]];
        xup = xup @ "Reshape"[Join[prefix, Catenate @ Thread[{k, i + d}]]];
        xup = xup @ "Slice"[Join[slicePrefix, Catenate[Partition[#, 2] & /@ Thread[{0, k, 0, o * s}]]]];
        (* handle stride, and permute to move reduce to the end *)
        xup = xup @ "Reshape"[Join[prefix, Catenate @ Thread[{k, o, s}]]];
        xup = xup @ "Slice"[Join[slicePrefix, Catenate[Partition[#, 2] & /@ Thread[{0, k, 0, o, 0, 1}]]]];
        xup = xup @ "Reshape"[Join[prefix, Catenate @ Thread[{k, o}]]];

        Return[xup @ "Permute"[Join[Range[pRank], pRank + 2 * Range[0, kRank - 1] + 1, pRank + 2 * Range[0, kRank - 1]]]]
    ];
    o = Quotient[i + (s - k), s];
    xup = self @ "Slice"[Join[slicePrefix, Thread[{0, o * s}]]];
    xup = xup @ "Reshape"[Join[prefix, Catenate @ Thread[{o, s}]]];
    xup = xup @ "Slice"[Join[slicePrefix, Catenate[Partition[#, 2] & /@ Thread[{0, o, 0, k}]]]];

    xup @ "Permute"[Join[Range[pRank], pRank + 2 * Range[0, kRank - 1], pRank + 2 * Range[0, kRank - 1] + 1]]
]

Tensor["Conv2D"[NameValuePattern[self_, Weight_, Bias_ : None, Groups_ : 1, Stride_ : 1, Dilation_ : 1, Padding_ : 1]]] := Enclose @ Block[{
    bs, gcin, cout, cin, HW,
    padding = Padding,
    x, ret
},
    {{bs, gcin}, {cout, cin}, HW} = {self["Shape"][[;; 2]], Weight["Shape"][[;; 2]], Weight["Shape"][[3 ;;]]};
    ConfirmAssert[Groups * cin == gcin && self["Rank"] == Weight["Rank"]];
    If[ListQ[padding], ConfirmAssert[Length[padding] == 2 * Length[HW] || Length[padding] == Length[HW]]];
    padding = Which[
        IntegerQ[padding],
        ConstantArray[padding, 2 * Length[HW]],
        Length[padding] == 2 * Length[HW],
        padding,
        True,
        Reverse @ Catenate[{#, #} & /@ padding]
    ];

    x = self["Pad2D"[padding]] @ "Pool"[HW, Stride, Dilation];
    {rcout, oyx} = {Quotient[cout, Groups], x["Shape"][[3 ;; - Length[HW] - 1]]};
    x = x @* "Reshape"[{bs, Groups, cin, 1, Splice @ oyx, Splice @ HW}] @* "Expand"[{bs, Groups, cin, rcout, Splice @ oyx, Splice @ HW}] @* "Permute"[{0, 1, 3, Splice[3 + Range[Length[oyx]]], 2, 3 + Length[oyx] + Range[Length[HW]]}];

    ret = (x * Weight["Reshape"[{1, Groups, rcout, Splice @ ConstantArray[1, Length[oyx]], cin, Splice @ HW}]]) @* "Sum"[- 1 - Range[0, Length[oyx]], True] @* "Reshape"[{bs, cout, Splice @ oyx}];
    If[Bias === None, ret, ret + Bias["Reshape"[{1, -1, Splice @ ConstantArray[1, Length[HW]]}]]]
]

Tensor["Permute"[self_, order_]] := TensorFunction["Permute"] @ "Apply"[self, "Order" -> order]

Tensor["Transpose"[self_, ax1_ : 1, ax2_ : 0]] := self["Permute"[With[{order = Range[self["Rank"]]}, ReplacePart[order, {#1 -> order[[#2]], #2 -> order[[#1]]}] & [AxisPart[ax1], AxisPart[ax2]]]]]


Tensor["MatMul"[self_, x_Tensor, reverse_ : False]] := If[reverse, x . self, self . x]

Tensor["Where"[self_, input_, other_]] := Block[{x, y, z},
    {x, y} = self["Broadcast"[input]];
    {x, z} = x["Broadcast"[other]];
    TensorFunction["Where"] @ ("Apply"[x, ##] & @@ y @ "Broadcast"[z])
]

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
            {BoxForm`SummaryItem[{"LazyData: ", self["LazyData"]}]},
            If[ self["Context"] === None,
                Nothing,
                {BoxForm`SummaryItem[{"Context: ", self["Context"]["$Class"]["$Label"] @@ InputForm /@ self["Context"]["Parents"]}]}
            ]
        },
        form
    ]

Tensor["Graph"[self_, opts___]] := Block[{edges = {}, visited = {}, deepwalk},
    deepwalk[node_] := (
        AppendTo[visited, node];
        Scan[(AppendTo[edges, DirectedEdge[#, node, If[LazyOpQ[#], #["Argument"], #["Shape"]]]]; If[! MemberQ[visited, #], deepwalk[#]]) &, If[LazyOpQ[node], node, node["Op"]]["Source"]];
    );

    deepwalk[self["LazyData"]];

    Graph[
        visited, edges,
        opts,
        VertexShapeFunction -> Function[
            Inset[ClickToCopy[Style[
                With[{op = If[LazyOpQ[#2], #2, #2["Op"]]},
                    Which[LazyOpQ[#2], Framed[#, FrameStyle -> Dashed] &, #2["RealizedQ"], Framed, True, Identity] @ If[
                        op["Argument"] === None,
                        op["OpName"],
                        op["OpName"][op["Argument"] /. _RandomGeneratorState :> "seed"]
                    ]
                ],
                    Black
                ], #2],
                #1,
                #3
            ]
        ],
        EdgeShapeFunction -> "Line",
        EdgeLabels -> "EdgeTag",
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

Tensor["Backward"[self_, value_ : 1]] := Enclose @ Block[{grads},
    ConfirmAssert[self["Shape"] === {}, "Only scalar gradients are currently supported"];
    self["Gradient"] = Tensor[value, "Type" -> self["Type"], "Device" -> self["Device"], "RequiresGradient" -> False];
    Do[
        If[t0["RequiresGradients"] === False, Continue[]];
        ConfirmAssert[t0["Gradient"] =!= None, t0];
        grads = Replace[
            Developer`ToList[t0["Context"]["Backward"[t0["Gradient"]["LazyData"]]]],
            g : Except[None] :> Tensor[g, "Device" -> self["Device"], "RequiresGradient" -> False],
            {1}
        ];
        MapThread[
            {t, g} |-> If[g =!= None && t["RequiresGradient"],
                ConfirmAssert[t["Shape"] === g["Shape"], StringTemplate["Gradient stape must match tensor shape: ``"][t0]];
                t["Gradient"] = If[t["Gradient"] === None, g, t["Gradient"] + g];
                t["Gradient"]["Context"] = t0["Context"]
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

Tensor[(f : "Sum" | "Max")[self_, args___]] := self["Reduce"[f, args]]
Tensor["Min"[self_, args___]] := - (- self)["Max"[args]]

Tensor["_SoftMax"[self_, axis_]] := Block[{m = self - self @ "Max"[axis, True], e},
    e = Exp[m];
    {m, e, e @ "Sum"[axis, True]}
]

Tensor["SoftMax"[self_, axis_ : -1]] := Block[{e, ss},
    {e, ss} = self @ "_SoftMax"[axis][[2 ;;]];
    e / ss
]

Tensor["LogSoftMax"[self_, axis_ : -1]] := Block[{m, e, ss},
    {m, e, ss} = self @ "_SoftMax"[axis];
    m - Log[ss]
]


Tensor["Broadcast"[self_, other_, opts : OptionsPattern[]]] := Enclose @ Block[{
    x = self,
    y = If[Tensor["$Test"][other], other, Confirm @ Tensor[other, self["Device"], self["Type"]]],
    xShape, yShape, shape
},
        If[TrueQ[OptionValue[{opts, "Reverse" -> False}, "Reverse"]], {x, y} = {y, x}];
        If[(xShape = x["Shape"]) === (yShape = y["Shape"]), Return[{x, y}, Block]];
        shapeDelta = Length[xShape] - Length[yShape];
        Which[
            shapeDelta > 0, y = y["Reshape"[Join[ConstantArray[1, shapeDelta], yShape]]],
            shapeDelta < 0, x = x["Reshape"[Join[ConstantArray[1, - shapeDelta], xShape]]]
        ];
        If[(xShape = x["Shape"]) === (yShape = y["Shape"]), Return[{x, y}, Block]];
        shape = MapThread[Max, {xShape, yShape}];
        If[xShape =!= shape, x = x["Expand"[shape]]];
        If[yShape =!= shape, y = y["Expand"[shape]]];
        {x, y}
    ]

Tensor["Reduce"[self_, f_, axis_ : None, keepDim_ : False]] := Block[{
    axes = Developer`ToList @ Replace[axis, None :> Range[0, Length[self["Shape"]] - 1]],
    result
},
    axes = 1 + List /@ Replace[axes, i_ /; i < 0 :> i + Length[self["Shape"]], {1}];
    result = TensorFunction[f] @ "Apply"[self, "Level" -> axes];
    If[keepDim, result, result["Reshape"[Delete[self["Shape"], axes]]]]
]

StaticMethod[
Tensor["LoadOp"[NameValuePattern[op_, size_, device_ : None, type_ : None, arg_ : None]], opts___] :=
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
Tensor["Rand"[shape : Shape], opts___] := Tensor["LoadOp"["RAND", Times @@ shape, "arg" -> $RandomGeneratorState], opts] @ "Reshape"[shape]
]


StaticMethod[
Tensor["Uniform"[NameValuePattern[shape : Shape, low_ : -1.0, high_ : 1.0]], opts___] :=
    (high - low) * Tensor["Rand"[shape], opts] + low
]

StaticMethod[
Tensor["ScaledUniform"[shape : Shape, args___], opts___] :=
    Tensor["Uniform"[shape, args], opts] / Sqrt[Times @@ shape]
]


(* Creation *)

StaticMethod[
Tensor["Full"[shape : Shape, value_], opts___] :=
    Tensor[value, opts] @* "Reshape"[ConstantArray[1, Length[shape]]] @* "Expand"[shape]
]

StaticMethod[
Tensor["Zeros"[shape : Shape], opts___] :=
    Tensor["Full"[shape, 0], opts]
]

StaticMethod[
Tensor["Ones"[shape : Shape], opts___] :=
    Tensor["Full"[shape, 1], opts]
]

StaticMethod[
Tensor["Arange"[From_Integer, To : _Integer | None : None, step_Integer : 1], opts___] := Block[{from, to},
    {from, to} = If[To === None, {0, From}, {From, To}];
    Accumulate[Tensor["Full"[{Ceiling[(to - from) / step]}, step], opts]] + (from - step)
]]

StaticMethod[
Tensor["Eye"[dim_Integer ? Positive], opts___] :=
    Tensor[{1}, opts] @* "Pad"[{{0, dim}}] @* "Reshape"[{1, dim + 1}] @* "Expand"[{dim, dim + 1}] @* "Reshape"[{dim * (dim + 1)}] @* "Shrink"[{{0, dim * dim}}] @* "Reshape"[{dim, dim}]
]


(* Functional NN *)

Tensor["SparseCategoricalCrossEntropy"[self_, Y_, ignoreIndex_ : -1]] := Block[{
    lossMask = Y != ignoreIndex,
    yCounter = Tensor["Arange"[self["Shape"][[-1]]], "Type" -> "Integer32", "Device" -> self["Device"], "RequiresGradient" -> False] @* "Unsqueeze"[0] @* "Expand"[{Y["Dimension"], self["Shape"][[-1]]}],
    y
},
    y = ((yCounter == Y @* "Flatten"[] @* "Reshape"[{-1, 1}]) @ "Where"[-1, 0] * lossMask @ "Reshape"[{-1, 1}]) @ "Reshape"[Append[Y["Shape"], self["Shape"][[-1]]]];
    (self["LogSoftMax"[]] * y)["Sum"[]] / lossMask["Sum"[]]
]
