Package["TinyGrad`"]

PackageExport[TensorFunction]

PackageImport["Wolfram`Class`"]



General::noimpl = "Function `1` not implemented for `2`";

Class[
    TensorFunction,
    "$Init"[self_, device_String, tensors___] :> (
        self["Device"] = device;
        self["RequiresInputGradient"] = Through[{tensors}["RequiresGradient"]];
        self["RequiresGradient"] = If[TrueQ[Or @@ self["RequiresInputGradient"]], True, If[MemberQ[self["RequiresInputGradient"], None], None, False]];
        If[self["RequiresGradient"], self["Parents"] = {tensors}]
    ),
    "Forward"[self_, ___] :> Message[TensorFunction::noimpl, "Forward", self],
    "Backward"[self_, ___] :> Message[TensorFunction::noimpl, "Backward", self],

    "Apply"[fxn_, xs : PatternSequence[x_, ___], opts : OptionsPattern[]] :> Block[{
        ctx = fxn["$New"[x["Device"], xs]], ret
    },
        ret = Tensor[
            ctx["Forward"[Sequence @@ Through[{xs}["LazyData"]], opts]],
            ctx["Device"],
            ctx["RequiresGradient"]
        ];
        If[ctx["RequiresGradient"] && ! Tensor["NoGradient"], ret["Context"] = ctx];
        ret
    ],
    "$ClassMethods" -> {"Apply"}
]


Class["Contiguous" -> TensorFunction,
    "Forward"[_, x_] :> x["Contiguous"[]],
    "Backward"[_, x_] :> x
]

Class["Cast" -> TensorFunction,
    "Forward"[self_, x_, opts : OptionsPattern[]] :> With[{type = OptionValue[{opts}, "Type"]},
        self["InputType"] = type;
        x["Cast"[type]]
    ],
    "Backward"[self_, x_] :> x["Cast"[self["InputType"]]]
]

Class["Add" -> TensorFunction,
    "Forward"[self_, x_, y_] :> x + y,
    "Backward"[self_, grad_] :> {If[self["RequiresInputGradient"][[1]], grad, None], If[self["RequiresInputGradient"][[2]], grad, None]}
]

Class["Sub" -> TensorFunction,
    "Forward"[self_, x_, y_] :> (x - y),
    "Backward"[self_, grad_] :> {If[self["RequiresInputGradient"][[1]], grad, None], If[self["RequiresInputGradient"][[2]], -grad, None]}
]

Class["Mul" -> TensorFunction,
    "Forward"[self_, x_, y_] :> (self["x"] = x; self["y"] = y; x * y),
    "Backward"[self_, grad_] :> {If[self["RequiresInputGradient"][[1]], grad * self["y"], None], If[self["RequiresInputGradient"][[2]], grad * self["x"], None]}
]

Class["Div" -> TensorFunction,
    "Forward"[self_, x_, y_] :> (self["x"] = x; self["y"] = y; x / y),
    "Backward"[self_, grad_] :> {If[self["RequiresInputGradient"][[1]], grad / self["y"], None], If[self["RequiresInputGradient"][[2]], - grad * self["x"] / self["y"] ^ 2, None]}
]

Class["Pow" -> TensorFunction,
    "Forward"[self_, x_, y_] :> (self["x"] = x; self["y"] = y; x ^ y),
    "Backward"[self_, grad_] :> {If[self["RequiresInputGradient"][[1]], grad * self["y"] * self["x"] ^ (self["y"] - 1), None], If[self["RequiresInputGradient"][[2]], grad * Log[self["x"]] * self["x"] ^ self["y"], None]}
]

Class["Sin" -> TensorFunction,
    "Forward"[self_, x_] :> (self["x"] = x; x["UnaryOp"["SIN"]]),
    "Backward"[self_, grad_] :> (self["x"]["ConstLike"[Pi / 2]] - self["x"])["UnaryOp"["SIN"]] * grad
]

Class["ReLU" -> TensorFunction,
    "Forward"[self_, x_] :> (self["Output"] = x["BinaryOp"["MAXIMUM", x["ConstLike"[0]]]]),
    "Backward"[self_, grad_] :> (self["Output"]["ConstLike"[0]] < self["Output"]) * grad
]

Class["Log" -> TensorFunction,
    "Forward"[self_, x_] :> (self["x"] = x; x["UnaryOp"["LOG2"]] * x["ConstLike"[Log[2]]]),
    "Backward"[self_, grad_] :> grad / self["x"]
]

Class["Exp" -> TensorFunction,
    "Forward"[self_, x_] :> (self["Output"] = (x * x["ConstLike"[1 / Log[2]]]) @ "UnaryOp"["EXP2"]),
    "Backward"[self_, grad_] :> self["Output"] * grad
]

Class["Sqrt" -> TensorFunction,
    "Forward"[self_, x_] :> (self["Output"] = x["UnaryOp"["SQRT"]]),
    "Backward"[self_, grad_] :> grad / (self["Output"] * self["Output"]["ConstLike"[2]])
]

Class["Sum" -> TensorFunction,
    "Forward"[self_, x_, opts : OptionsPattern[]] :> With[{lvl = OptionValue[{opts}, "Level"]},
        self["InputShape"] = x["Shape"];
        x["ReduceOp"["SUM", lvl]]
    ],
    "Backward"[self_, grad_] :> grad["Expand"[self["InputShape"]]]
]

Class["Max" -> TensorFunction,
    "Forward"[self_, x_, opts : OptionsPattern[]] :> With[{lvl = OptionValue[{opts}, "Level"]},
        {self["x"], self["Output"]} = {x, x["ReduceOp"["MAX", lvl]]};
        self["Output"]
    ],
    "Backward"[self_, grad_] :> Block[{max, div},
        max = self["x"] @ "ConstLike"[1.0] - (self["x"] < self["Output"] @ "Expand"[self["x"] @ "Shape"]);
        div = max @* "ReduceOp"["SUM", grad @ "Shape"] @* "Expand"[self["x"] @ "Shape"];
        (max / dim) * grad @ "Expand"[self["x"] @ "Shape"]
    ]
]

Class["Less" -> TensorFunction,
    "Forward"[self_, x_, y_] :> (x < y)
]

Class["Reshape" -> TensorFunction,
    "Forward"[self_, x_, opts : OptionsPattern[]] :> With[{shape = OptionValue[{opts}, "Shape"]},
        self["InputShape"] = x["Shape"];
        x @ "Reshape"[shape]
    ],
    "Backward"[self_, grad_] :> grad @ "Reshape"[self["InputShape"]]
]

Class["Expand" -> TensorFunction,
    "Forward"[self_, x_, opts : OptionsPattern[]] :> With[{shape = OptionValue[{opts}, "Shape"]},
        self["InputShape"] = x["Shape"];
        x @ "Expand"[shape]
    ],
    "Backward"[self_, grad_] :> grad @ "ReduceOp"["SUM", Catenate @ Complement[Position[self["InputShape"], 1], Position[grad["Shape"], 1]]]
]

Class["Permute" -> TensorFunction,
    "Forward"[self_, x_, opts : OptionsPattern[]] :> With[{order = OptionValue[{opts}, "Order"]},
        self["InputShape"] = x["Shape"]; x @ "Permute"[order]
    ],
    "Backward"[self_, grad_] :> grad @ "Permute"[PermutationList @ FindPermutation[grad["Shape"], self["InputShape"]]]
]

Class["Pad" -> TensorFunction,
    "Forward"[self_, x_, opts : OptionsPattern[]] :> With[{padding = OptionValue[{opts}, "Padding"]},
        self["Padding"] = MapThread[#2[[1]] + {0, #1} &, {x["Shape"], padding}];
        x @ "Pad"[padding]
    ],
    "Backward"[self_, grad_] :> grad @ "Shrink"[self["Padding"]]
]

Class["Shrink" -> TensorFunction,
    "Forward"[self_, x_, opts : OptionsPattern[]] :> With[{shrink = OptionValue[{opts}, "Shrink"]},
        self["Padding"] = MapThread[{0, #1}  + {1, -1} * #2 &, {x["Shape"], shrink}];
        x @ "Shrink"[shrink]
    ],
    "Backward"[self_, grad_] :> grad @ "Pad"[self["Padding"]]
]

