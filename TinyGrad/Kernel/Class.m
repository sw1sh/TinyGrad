Package["TinyGrad`"]

PackageExport[Class]



NewInstance[cmd : "New" | "Extend", class_, src_, self_, initArgs___] := With[{
    super = If[cmd === "New", self, self["Class"]]
}, With[{
    ref = Replace[Unevaluated[src], {
        name_String :> Unique["$" <> name],
        Automatic | Except[_Symbol] :> Unique["$" <> StringDelete[ToString[Unevaluated[super]], Except[WordCharacter]]]
    }]
},
    If[ cmd === "Extend",
        Language`ExtendedDefinition[ref] =
            Language`ExtendedDefinition[self] /. HoldPattern[self] :> ref
    ];


    If[ (* every instance is also a class, initialize as class first *)
        FailureQ[Class[If[cmd === "Extend", Unevaluated["Init"[ref, super, initArgs]], Unevaluated["Init"[ref, super]]]]] ||
        (* initialize as instance *)
        cmd === "New" && FailureQ[class[Unevaluated["Init"[ref, initArgs]]]],

        DeleteObject[ref];
        Return[$Failed]
    ];

    If[ cmd === "New",
        ref /: DeleteObject[ref] := super["Free"[ref]];

        ref["Label"] = Replace[Unevaluated[src], {
            Automatic :> ToString[Unevaluated[self]],
            sym_Symbol :> SymbolName[Unevaluated[sym]],
            _ :> ToString[Unevaluated[src]]
        }];

        (* can method be any expression? *)
	    ref[method_String[args___]] := super[Unevaluated[method[ref, args]]];

	    ref[prop_String] /; ListQ[super["Properties"]] && MemberQ[super["Properties"], prop] := super[prop[ref]];

        (* Inheritance. Class instances only inherit methods. *)
        If[ self === Class,
            ref[classMethod : _String | _String[___]] := self[Unevaluated[classMethod]],
            ref[args___] := Function[Null, self[##], HoldAll] @@ Unevaluated /@ Hold[args]
        ];

        MakeBoxes[ref, form_] ^:= super["Format"[ref, form]];

        Normal[ref] ^:= ref["Normal"];

        (* Sugar *)
        Composition[ref, calls__] ^:= Fold[Function[Null, #1[Unevaluated[#2]], HoldRest], ref, Unevaluated[{calls}]];

        SetAttributes[ref, {Temporary}];
    ];

    ref
]]

Class["Init"[self_, class_, initValues___]] := Block[{
    initRules = Replace[{initValues}, {lhs : Except[_Rule | _RuleDelayed] :> lhs -> None}, {1}],
    methods = {}
},
    self["Class"] = class;
    self["Test"] = MatchQ[#["Class"], self] &;
    self["Pattern"] = _Symbol ? (self["Test"]);

    Scan[
        Replace[rule_[lhs_, rhs_] :> (
            AppendTo[methods, lhs];
            Replace[rule, {Rule -> Set, RuleDelayed -> SetDelayed}][self[lhs], rhs]
        )],
        initRules
    ];
    self["Methods"] = methods;

    self[(cmd : "New" | "Extend") | (cmd : "New" | "Extend")[initArgs___], src_ : Automatic] :=
        NewInstance[cmd, class, Unevaluated[src], self, initArgs];

    self["Free"[obj_]] := (
        ClearAll[obj]
    );
    If[ ! MatchQ[class, _Symbol] || ! MemberQ[Keys[DownValues[class]], Verbatim[HoldPattern][_["Format"[___]]]],
	    self["Format"[obj_, form___]] := With[{boxes = ToBoxes[Tooltip[Framed[obj["Label"]], HoldForm[DisableFormatting[self]]], form]},
	        InterpretationBox[boxes, obj]
	    ];
	];

    self
]


Class["Init"[Class, Class,
    "Properties" -> {"Normal"}
]]

Class[class_, values___] := Class[Unevaluated["New"[class, values]]]

Class[class : _Symbol | _String, values___] := Class[Unevaluated["New"[class, values]], Unevaluated[class]]

Class[(class : _Symbol | _String)[parent_Symbol], values___] :=
    HoldPattern[parent[class]] = parent["Extend"[values], Unevaluated[class]]

