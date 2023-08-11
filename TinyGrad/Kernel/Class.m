Package["TinyGrad`"]

PackageExport[Class]

PackageScope[ClassTest]



NewInstance[cmd : "New" | "Extend", class_, src_, self_, initArgs___] := Enclose @ With[
{
    super = If[cmd === "New", self, self["Class"]]
},
{
    ref = Replace[Unevaluated[src], {
        name_String :> Symbol["TinyGrad`" <> name],
        Automatic | Except[_ ? Developer`SymbolQ] :> Unique["$" <> StringDelete[ToString[Unevaluated[super]], Except[WordCharacter]]]
    }]
},
    SetAttributes[ref, {Temporary}];

    ref["Properties"] = self["Properties"];
    ref["ClassMethods"] = self["ClassMethods"];

    (* every instance is also a class, initialize as class first *)
    Confirm @ Class[If[cmd === "Extend", Unevaluated["Init"[ref, super, initArgs]], Unevaluated["Init"[ref, super]]]];

    If[ cmd === "Extend",
        ref[method_String[args : PatternSequence[arg_, ___]]] /; ref =!= Unevaluated[arg] && ListQ[class["ClassMethods"]] && MemberQ[class["ClassMethods"], method] :=
            ref[Unevaluated[method[ref, args]]]
    ];

    InheritDefinitions[self, ref];

    (* initialize only a new instance *)
    If[ cmd === "New",
        Confirm @ class[Unevaluated["Init"[ref, initArgs]]];

        ref["Label"] = Replace[Unevaluated[src], {
            Automatic :> ToString[Unevaluated[self]],
            sym_ ? Developer`SymbolQ :> SymbolName[Unevaluated[sym]],
            _ :> ToString[Unevaluated[src]]
        }];

        (* can method be any expression? *)
	    ref[method_String[args___]] := If[
            ListQ[super["ClassMethods"]] && MemberQ[super["ClassMethods"], method],
            ref[Unevaluated[method[ref, args]]],
            If[super === Class, $Failed, super[Unevaluated[method[ref, args]]]]
        ];

	    ref[prop_String] /; ListQ[super["Properties"]] && MemberQ[super["Properties"], prop] := super[prop[ref]];

        ref[___] := $Failed
    ];

    DeleteObject[ref] ^:= super["Free"[self]];

    MakeBoxes[ref, form_] ^:= super["Format"[ref, form]];

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

    If[ ! MatchQ[class, _ ? Developer`SymbolQ] || ! MemberQ[Keys[DownValues[class]], Verbatim[HoldPattern][_["Format"[___]]]],
	    self["Format"[obj_, form___]] := With[{boxes = ToBoxes[Tooltip[Framed[obj["Label"]], HoldForm[DisableFormatting[self]]], form]},
	        InterpretationBox[boxes, obj]
	    ];
	];

    self["Free"[obj_]] := (
        ClearAll[obj]
    );

    Normal[self] ^:= self["Normal"];

    (* Sugar *)
    Composition[self, calls__] ^:= Fold[Function[Null, #1[Unevaluated[#2]], HoldRest], self, Unevaluated[{calls}]];

    self
]


Class["Init"[Class, Class, "Normal" -> Class, "Properties" -> {}, "ClassMethods" -> {}]]

Class[class_, values___] := (Echo[InputForm[{class}]]; Class[Unevaluated["New"[class, values]]])

Class[class : _ ? Developer`SymbolQ | _String, values___] := (Echo[InputForm[{class}]]; Class[Unevaluated["New"[class, values]], Unevaluated[class]])

Class[(class : _ ? Developer`SymbolQ | _String)[parent_ ? Developer`SymbolQ], values___] :=
    HoldPattern[parent[class]] = parent["Extend"[values], Unevaluated[class]]

