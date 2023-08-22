Package["TinyGrad`"]

PackageExport[NameValuePattern]
PackageScope[CoIdentity]
PackageScope[LevelSpan]



expr_[CoIdentity] ^:= expr


Unprotect[Interval];
Interval /: Mod[m_Interval, n_Integer] := Interval @ If[Max[m] - Min[m] >= n || Min[m] != Max[m] && Mod[Min[m], n] >= Mod[Max[m], n], {0, n - 1}, {Mod[Min[m], n], Mod[Max[m], n]}]
Interval /: Quotient[m_Interval, n_] := Floor[m / n]
Interval /: QuotientRemainder[m_Interval, n_] := {Quotient[m, n], Mod[m, n]}
Protect[Interval];


LevelSpan = Replace[{{from_, to_} :> from ;; to, {n_} :> {n}, n_ :> ;; n}]


Splits[list_List] := TakeDrop[list, #] & /@ Range[0, Length[list]]

NameValuePattern[args : _Pattern..., kwargs : PatternSequence[(Optional | Rule | RuleDelayed)[_Pattern, ___]...]] :=
    PatternSequence[
        PatternSequence @@ Replace[#1, {
            Verbatim[Optional][Verbatim[Pattern][name_Symbol, p_]] :>
				With[{opt = Pattern @@ Hold[name, Except[_Rule| _RuleDelayed, p]]}, HoldPattern[Optional[opt, Sequence[]]]],
            (Optional | Rule | RuleDelayed)[Verbatim[Pattern][name_Symbol, p_], def_] :>
				With[{opt = Pattern @@ Hold[name, Except[_Rule| _RuleDelayed, p]]}, HoldPattern[Optional[opt, def]]],
            Verbatim[Pattern][name_Symbol, p_] :> Pattern @@ Hold[name, Except[_Rule| _RuleDelayed, p]]
        },
            {1}
        ],
        OrderlessPatternSequence @@ Replace[#2, {
				Verbatim[Optional][p : Verbatim[Pattern][sym_Symbol, _]] :>
					With[{name = SymbolName[Unevaluated[sym]]}, Optional[(Rule | RuleDelayed)[name, p], HoldPattern[name -> Sequence[]]]],
				(head : Optional | Rule | RuleDelayed)[p : Verbatim[Pattern][sym_Symbol, _], def_] :>
					With[{name = SymbolName[Unevaluated[sym]], rule = Replace[head, Optional -> Rule]}, Optional[(Rule | RuleDelayed)[name, p], rule[name, def]]],
	            p : Verbatim[Pattern][sym_Symbol, _] :> (Rule | RuleDelayed)[SymbolName[Unevaluated[sym]], p]
	        },
            {1}
        ]
    ] & @@@ Alternatives @@ Reverse @ Splits[{args, kwargs}] //. {
        (Alternatives | PatternSequence | OrderlessPatternSequence)[] -> Sequence[],
        (Alternatives | PatternSequence | OrderlessPatternSequence)[x_] :> x,
        (h : PatternSequence | OrderlessPatternSequence)[left___, h_[mid___], right___] :> h[left, mid, right],
        (PatternSequence | OrderlessPatternSequence)[(PatternSequence | OrderlessPatternSequence)[mid___]] :> OrderlessPatternSequence[mid]
	} /. (* naming sequences are not necessary, but it helps to avoid a bug in the pattern matcher *)
		o_OrderlessPatternSequence :> $kwargs : o /. p_PatternSequence :> $args : p //
        Longest

