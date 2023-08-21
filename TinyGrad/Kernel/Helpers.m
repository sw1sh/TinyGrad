Package["TinyGrad`"]

PackageScope[CoIdentity]
PackageScope[LevelSpan]



expr_[CoIdentity] ^:= expr


Unprotect[Interval];
Interval /: Mod[m_Interval, n_Integer] := Interval @ If[Max[m] - Min[m] >= n || Min[m] != Max[m] && Mod[Min[m], n] >= Mod[Max[m], n], {0, n - 1}, {Mod[Min[m], n], Mod[Max[m], n]}]
Interval /: Quotient[m_Interval, n_] := Floor[m / n]
Interval /: QuotientRemainder[m_Interval, n_] := {Quotient[m, n], Mod[m, n]}
Protect[Interval];


LevelSpan = Replace[{{from_, to_} :> from ;; to, {n_} :> {n}, n_ :> ;; n}]

