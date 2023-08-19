Package["TinyGrad`"]

PackageExport[LazyOp]
PackageExport[Interpreted]

PackageScope[$UnaryOps]
PackageScope[$BinaryOps]
PackageScope[$ReduceOps]
PackageScope[$TernaryOps]
PackageScope[$LoadOps]
PackageScope[$MovementOps]
PackageScope[$OpTypes]
PackageScope[$Ops]

PackageImport["Wolfram`Class`"]



$UnaryOps = {"NOOP", "EXP2", "LOG2", "CAST", "SIN", "SQRT", "RECIP"}
$BinaryOps = {"ADD", "SUB", "MUL", "DIV", "CMPEQ", "MAXIMUM", "MOD", "CMPLT"}
$ReduceOps = {"SUM", "MAX"}
$TernaryOps = {"MULACC", "WHERE"}
$LoadOps = {"EMPTY", "RAND", "CONST", "FROM", "CONTIGUOUS", "CUSTOM"}
$MovementOps = {"RESHAPE", "PERMUTE", "EXPAND", "PAD", "SHRINK", "STRIDE"}

$OpTypes = {"Unary" -> $UnaryOps, "Binary" -> $BinaryOps, "Reduce" -> $ReduceOps, "Ternary" -> $TernaryOps, "Load" -> $LoadOps, "Movement" -> $MovementOps}
$Ops = Join @@ Values[$OpTypes]

Op = Alternatives @@ $Ops

LazyOpQ = MatchQ[LazyOp["$Type"]]

Class[LazyOp,
    "$Init"[self_, op : Op, src_, arg_ : None] :> (
        self["Op"] = op;
        self["Source"] = src;
        self["Argument"] = arg;

        Equal[left___, self, right___] ^:=
            AllTrue[{left, right}, MatchQ[LoadOp["$Type"]]] &&
            AllTrue[
                SameQ @@ Through[{left, self, right}[#]] &,
                {"Op", "Source", "Argument"}
            ];
        self
    ),
    "$Properties" -> {"Buffers"},

    "Buffers"[self_] :> Catenate[Through[self["Source"]["Buffers"]]],

    "$Format"[self_, form_] :> BoxForm`ArrangeSummaryBox[
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

LazyOp[op : Op, args___] := LazyOp["$New"[op, args]]


Class[Interpreted,

    "$Init"[self_, buffer_, map : KeyValuePattern[Op -> _], fromLazyBuffer_ : Automatic, toUnderlying_ : Automatic, fromUnderlying_ : None] :> (
        self["Buffer"] = buffer;
        self["Map"] = map;
        self["FromLazyBuffer"] = Replace[fromLazyBuffer, Automatic -> Function[#["Realized"]]];
        self["FromUnderlying"] = If[fromUnderlying === None, buffer, fromUnderlying];
        self["ToUnderlying"] = Replace[toUnderlying, Automatic -> Function[#["Data"]]];
        self["Synchronize"] = Function[None];
        self["CodeGen"] = None;
    ),

    "Execute"[self_, lazyOp_::[LazyOp], output_ : None, context : _ ? Developer`SymbolQ : None, args___] :> Enclose @ Block[{
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
        ConfirmAssert[KeyExistsQ[self["Map"], ast["Op"]], ast["Op"]];
        ret = self["FromUnderlying"][
            self["Map"][ast["Op"]] @@ If[ast["Argument"] === None, Identity, Append[ast["Argument"]]][self["ToUnderlying"] /@ sources]
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
