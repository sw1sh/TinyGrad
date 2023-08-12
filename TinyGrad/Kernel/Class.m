Package["TinyGrad`"]

PackageExport[Class]

PackageScope[ClassTest]
PackageScope[ClassQ]



NewInstance[cmd : "New" | "Extend", self_, src_, initArgs___] := Enclose @ With[
{
    super = If[cmd === "New", self, self["$Class"]]
},
With[{
    ref = Replace[Unevaluated[src], {
        name_String :> Unique[name <> "$"],
        Automatic | Except[_ ? Developer`SymbolQ] :> Unique[StringDelete[ToString[Unevaluated[super]], Except[WordCharacter]] <> "$"]
    }]
},
    SetAttributes[ref, {Temporary}];
	InheritDefinitions[self, ref];


    (* every instance is also a class, initialize as class first *)
    Confirm @ Class[If[cmd === "Extend", Unevaluated["$Init"[ref, super, initArgs]], Unevaluated["$Init"[ref, super]]]];

	ref["$Parent"] = self;

    ref["$Label"] = Replace[Unevaluated[src], {
        Automatic :> ToString[Unevaluated[self]],
        sym_ ? Developer`SymbolQ :> SymbolName[Unevaluated[sym]],
        _ :> ToString[Unevaluated[src]]
    }];

    ref["$Properties"] := self["$Properties"];
    ref["$ClassMethods"] := self["$ClassMethods"];

    If[ cmd === "New",

        (* methods *)
        (* figure out correct reference passing *)
        ref[method_String[args : PatternSequence[arg_, ___] | ___]] /; ListQ[self["$ClassMethods"]] && MemberQ[self["$ClassMethods"], method] && Unevaluated[arg] =!= ref && Unevaluated[arg] =!= ref["$Parent"] :=
            self[Unevaluated[method[ref, args]]];
        If[ self =!= Class,
            ref[method_String[args___]] := self[method[ref, args]]
        ];

        (* properties *)
	    ref[prop_String] /; ListQ[self["$Properties"]] && MemberQ[self["$Properties"], prop] := self[prop[ref]];

        If[ self =!= Class,
			ref[def : _String | _String[___]] := (self[def])
			(* ref[x_] := Missing[x] *)
		];

		(* initialize *)
        Confirm @ self[Unevaluated["$Init"[ref, initArgs]]];

        If[ self === Class,
            ref[method_String[___]] := If[method ==="$Init", ref, Missing[method]]
        ]
        ,

        ref[method_String[ref, args___]] /; ListQ[self["$ClassMethods"]] && MemberQ[self["$ClassMethods"], method] := self[Unevaluated[method[ref, args]]];
        ref[method_String[args : PatternSequence[arg_, ___] | ___]] /; ListQ[self["$ClassMethods"]] && MemberQ[self["$ClassMethods"], method] && Unevaluated[arg] =!= ref && Unevaluated[arg] =!= self :=
            ref[Unevaluated[method[ref, args]]];

    ];

    MakeBoxes[ref, form___] ^:= self["$Class"]["$Format"[ref, form]];

    ref
]]

ClassTest[self_][x_] := With[{super = x["$Parent"]}, super =!= Unevaluated[x["$Parent"]] && (MatchQ[super, self] || super =!= Class && ClassTest[self][super])]

ClassQ[x_] := Unevaluated[x] === Class || Developer`SymbolQ[Unevaluated[x]] && ClassQ[x["$Parent"]]
ClassQ[___] := False

Class["$Init"[self_, class_, initValues___]] := Block[{
    initRules = Replace[{initValues}, {lhs : Except[_Rule | _RuleDelayed] :> lhs -> None}, {1}],
    definitions = {}
},
    self["$Class"] = class;
    self["$Test"] = ClassTest[self];
    self["$Type"] = _Symbol ? (self["$Test"]);

    self[(cmd : "New" | "Extend") | (cmd : "New" | "Extend")[initArgs___], src_ : Automatic] :=
        NewInstance[cmd, self, Unevaluated[src], initArgs];

	self["$Format"[obj_, form___]] :=
        BoxForm`ArrangeSummaryBox[
	        obj["$Label"],
	        obj,
	        None,
	        {
				{BoxForm`SummaryItem[{"Class: ", ToString[obj["$Class"]]}]},
	            {BoxForm`SummaryItem[{"Parent: ", ToString[obj["$Parent"]]}]}
	        },
	        {{BoxForm`SummaryItem[{"Symbol: ", SymbolName[obj]}]}},
	        form
	    ];

    Scan[
        Replace[rule_[lhs_, rhs_] :> (
            AppendTo[definitions, lhs];
            Replace[rule, {Rule -> Set, RuleDelayed -> SetDelayed}][self[lhs], rhs]
        )],
        initRules
    ];
    self["$InitDefinitions"] = Union[definitions, {"$Properties", "$ClassMethods"}];

    Normal[self] ^:= self["$Normal"];

    (* Sugar *)
    Composition[self, calls : PatternSequence[_, __]] ^:= Fold[Function[Null, #1[Unevaluated[#2]], HoldRest], self, Unevaluated[{calls}]];

    self
]


Class["$Init"[Class, Class, "$Normal" -> Class, "$Properties" -> {}, "$ClassMethods" -> {}]];

Class[class : _ ? Developer`SymbolQ | _String, values___] := (Class[Unevaluated["New"[class, values]], Unevaluated[class]])

Class[(class : _ ? Developer`SymbolQ | _String)[parent_ ? Developer`SymbolQ], values___] :=
    HoldPattern[parent[class]] = parent["Extend"[values], Unevaluated[class]]