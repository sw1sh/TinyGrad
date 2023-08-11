Package["TinyGrad`"]

PackageExport[TensorFunction]



General::noimpl = "Function `1` not implemented for `2`";

Class[
    TensorFunction,
    "Init"[self_, device_String, tensors___] :> (
        self["Device"] = device;
        self["RequiresInputGradient"] = Through[{tensors}["RequiresGradient"]];
        self["RequiresGradient"] = If[TrueQ[Or @@ self["RequiresInputGradient"]], True, If[MemberQ[self["RequiresInputGradient"], None], None, False]];
        If[self["RequiresGradient"], self["Parents"] = {tensors}]
    ),
    "Forward"[self_, ___] :> Message[TensorFunction::noimpl, "Forward", self],
    "Backward"[self_, ___] :> Message[TensorFunction::noimpl, "Forward", self],

    "Apply"[fxn_, xs : PatternSequence[x_, ___], opts : OptionsPattern[]] :> Block[{
        ctx = fxn["New"[x["Device"], xs]], ret
    },
        ret = Tensor[
            ctx["Forward"[Sequence @@ Through[{xs}["LazyData"]], opts]],
            ctx["Device"],
            ctx["RequiresGradient"]
        ];
        If[ctx["RequiresGradient"] && ! Tensor["NoGradient"], ret["Context"] = ctx];
        ret
    ],
    "ClassMethods" -> {"Apply"}
]


Class["Contiguous"[TensorFunction],
    "Forward"[_, x_] :> x["Contiguous"[]],
    "Backward"[_, x_] :> x
]

Class["Cast"[TensorFunction],
    "Forward"[self_, x_, opts : OptionsPattern[]] :> With[{type = OptionValue[{opts}, "Type"]},
        self["InputType"] = type;
        x["Cast"[type]]
    ],
    "Backward"[self_, x_] :> x["Cast", self["InputType"]]
]

Class["Sin"[TensorFunction],
    "Forward"[self_, x_] :> (self["x"] = x; x["UnaryOp", "SIN"]),
    "Backward"[self_, grad_] :> self["x"]["ConstLike", Pi / 2]["BinaryOp", "SUB", self["x"]]["UnaryOp", "SIN"]["BinaryOp", "MUL", grad]
]

Class["Reshape"[TensorFunction],
    "Forward"[self_, x_, shape_] :> (self["InputShape"] = x["Shape"]; x @ "Reshape"[shape]),
    "Backward"[self_, grad_] :> grad @ "Reshape"[self["InputShape"]]
]

Class["Permute"[TensorFunction],
    "Forward"[self_, x_, order_] :> (self["InputOrder"] = x[order]; x @ "Permute"[order]),
    "Backward"[self_, grad_] :> grad @ "Permute"[Sort[self["InputOrder"]]]
]

Class["Pad"[TensorFunction],
    "Forward"[self_, x_, pad : {{_Integer, _Integer} ...}] :> (
        self["Padding"] = MapThread[#2[[1]] + {0, #1} &, {x["Shape"], pad}];
        x @ "Pad"[pad]
    ),
    "Backward"[self_, grad_] :> grad @ "Shrink"[self["Padding"]]
]

Class["Shrink"[TensorFunction],
    "Forward"[self_, x_, shrink : {{_Integer, _Integer} ...}] :> (
        self["Padding"] = MapThread[{0, #1}  + {1, -1} * #2 &, {x["Shape"], shrink}];
        x @ "Shrink"[shrink]
    ),
    "Backward"[self_, grad_] :> grad @ "Pad"[self["Padding"]]
]

