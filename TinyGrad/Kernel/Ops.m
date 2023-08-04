Package["TinyGrad`"]

PackageExport[LazyOp]

PackageScope[$UnaryOps]
PackageScope[$BinaryOps]
PackageScope[$ReduceOps]
PackageScope[$TernaryOps]
PackageScope[$LoadOps]
PackageScope[$OpTypes]
PackageScope[$Ops]


$UnaryOps = {"NOOP", "EXP2", "LOG2", "CAST", "SIN", "SQRT", "RECIP"}
$BinaryOps = {"ADD", "SUB", "MUL", "DIV", "CMPEQ", "MAXIMUM", "MOD", "CMPLT"}
$ReduceOps = {"SUM", "MAX"}
$TernaryOps = {"MULACC", "WHERE"}
$LoadOps = {"EMPTY", "RAND", "CONST", "FROM", "CONTIGUOUS", "CUSTOM"}


$OpTypes = {"Unary" -> $UnaryOps, "Binary" -> $BinaryOps, "Reduce" -> $ReduceOps, "Ternary" -> $TernaryOps, "Load" -> $LoadOps}
$Ops = Join @@ Values[$OpTypes]

Op = Alternatives @@ $Ops

LazyOpQ = MatchQ[LazyOp["Pattern"]]

Class[LazyOp,
    "Init"[self_, op : Op, src_, arg_ : None] :> (
        self["Op"] = op;
        self["Source"] = src;
        self["Argument"] = arg;
        self["Buffers"] = Through[src["Buffers"]];

        Equal[left___, self, right___] ^:=
            AllTrue[{left, right}, MatchQ[LoadOp["Pattern"]]] &&
            AllTrue[
                SameQ @@ Through[{left, self, right}[#]] &,
                {"Op", "Source", "Argument"}
            ];
        self
    ),

    "Format"[self_, form_] :> BoxForm`ArrangeSummaryBox[
        "LazyOp",
        self,
        None,
        {
            BoxForm`SummaryItem[{"Op: ", self["Op"]}],
            BoxForm`SummaryItem[{"Source: ", self["Source"]}],
            BoxForm`SummaryItem[{"Argument: ", self["Argument"]}]
        },
        {{}},
        form
    ]
]

LazyOp[args___] := LazyOp["New"[args]]


Class[Interpreted,

    "Init"[self_, buffer_, map : KeyValuePattern[Op -> _], fromLazyBuffer : Automatic, toBuffer : Automatic, fromBuffer : None] :> (
        self["Buffer"] = buffer;
        self["Map"] = map;
        self["FromLazyBuffer"] = Replace[fromLazyBuffer, Automatic -> Function[#["Realized"]]];
        self["FromBuffer"] = If[fromBuffer === None, buffer, fromBuffer];
        self["ToBuffer"] = Replace[toBuffer, Automatic -> Function[#["Buffer"]]];
        self["Synchronize"] = Function[None];
        self["CodeGen"] = None;
    ),

    "Execute"[self_, lazyOp_, output_ : None, context_Symbol : None, args___] :> Enclose @ Block[{
        ast = lazyOp,
        newContext, sources,
        ret
    },
        If[ KeyExistsQ[self["Map"], "MULACC"] && ast["Op"] === "SUM" && MatchQ[ast["Source"][[1]], LazyOp["Pattern"]] && ast["Source"][[1]]["Op"] === "MUL",
            ast = LazyOp["MULACC", ast["Source"][[1]]["Source"], ast["Argument"]];
        ];
        If[context =!= None && KeyExistsQ[context, ast], Return[context[ast]]];
        newContext = If[context === None, <||>, context];
        sources = Map[If[LazyOpQ[#], self[Unevaluated @ "Execute"[#, None, newContext, args]], self["FromLazyBuffer"][#]] &, ast["Source"]];
        ret = self["FromBuffer"][
            self["Map"][ast["Op"]] @@ If[ast["Argument"] === None, Identity, Append[ast["Argument"]]][self["ToBuffer"] /@ sources]
        ];
        If[ context =!= None, context[ast] = ret];
        If[ output =!= None && output["OutputBuffer"] =!= None,
            ConfirmAssert[
                output["OutputBuffer"]["Size"] == ret["Size"] &&
                output["OutputBuffer"]["Type"] == ret["Type"]
            ];
            output["OutputBuffer"]["Data"] = ret["Data"];
            Return[output["OutputBuffer"]]
        ];
        ret
    ]
]
