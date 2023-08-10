Package["TinyGrad`"]

PackageExport[Class]

PackageScope[ClassTest]



NewInstance[cmd : "New" | "Extend", class_, src_, self_, initArgs___] := Enclose @ With[
{
    super = If[cmd === "New", self, self["Class"]]
},
{
    ref = Replace[Unevaluated[src], {
        name_String :> Unique["$" <> name],
        Automatic | Except[_ ? Developer`SymbolQ] :> Unique["$" <> StringDelete[ToString[Unevaluated[super]], Except[WordCharacter]]]
    }]
},
    SetAttributes[ref, {Temporary}];

    (* every instance is also a class, initialize as class first *)
    Confirm @ Class[If[cmd === "Extend", Unevaluated["Init"[ref, super, initArgs]], Unevaluated["Init"[ref, super]]]];

    ref[method_String[args___]] /; ListQ[class["ClassMethods"]] && MemberQ[class["ClassMethods"], method] :=
            ref[Unevaluated[method[ref, args]]];

    If[ cmd === "Extend",
        InheritDefinitions[self, ref]
    ];
    (* initialize only a new instance *)
    If[ cmd === "New",
        Confirm @ class[Unevaluated["Init"[ref, initArgs]]]
    ];

    ref[method_String[args___]] /; ListQ[class["ClassMethods"]] && MemberQ[class["ClassMethods"], method] :=
        ref[Unevaluated[method[ref, args]]];

    If[ cmd === "New",
        ref /: DeleteObject[ref] := super["Free"[ref]];

        ref["Label"] = Replace[Unevaluated[src], {
            Automatic :> ToString[Unevaluated[self]],
            sym_ ? Developer`SymbolQ :> SymbolName[Unevaluated[sym]],
            _ :> ToString[Unevaluated[src]]
        }];

        (* can method be any expression? *)
	    ref[method_String[args___]] := super[Unevaluated[method[ref, args]]];

	    ref[prop_String] /; ListQ[super["Properties"]] && MemberQ[super["Properties"], prop] := super[prop[ref]];

        MakeBoxes[ref, form_] ^:= super["Format"[ref, form]];

        Normal[ref] ^:= ref["Normal"];

        (* Sugar *)
        Composition[ref, calls__] ^:= Fold[Function[Null, #1[Unevaluated[#2]], HoldRest], ref, Unevaluated[{calls}]];

    ];

    ref
]

ClassTest[self_][x_] := With[{class = x["Class"]}, class =!= Unevaluated[x["Class"]] && (MatchQ[class, self] || class =!= Class && ClassTest[self][class])]

Class["Init"[self_, class_, initValues___]] := Block[{
    initRules = Replace[{initValues}, {lhs : Except[_Rule | _RuleDelayed] :> lhs -> None}, {1}],
    methods = {}
},
    self["Class"] = class;
    self["Test"] = ClassTest[self];
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
    If[ ! MatchQ[class, _ ? Developer`SymbolQ] || ! MemberQ[Keys[DownValues[class]], Verbatim[HoldPattern][_["Format"[___]]]],
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

Class[class : _ ? Developer`SymbolQ | _String, values___] := Class[Unevaluated["New"[class, values]], Unevaluated[class]]

Class[(class : _ ? Developer`SymbolQ | _String)[parent_ ? Developer`SymbolQ], values___] :=
    HoldPattern[parent[class]] = parent["Extend"[values], Unevaluated[class]]

