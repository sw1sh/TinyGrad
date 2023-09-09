Package["TinyGrad`"]

PackageExport[NameValuePattern]
PackageScope[CoIdentity]
PackageScope[LevelSpan]
PackageScope[AxisPart]



expr_[CoIdentity] ^:= expr


Unprotect[Interval];
Interval /: Mod[m_Interval, n_Integer] := Interval @ If[Max[m] - Min[m] >= n || Min[m] != Max[m] && Mod[Min[m], n] >= Mod[Max[m], n], {0, n - 1}, {Mod[Min[m], n], Mod[Max[m], n]}]
Interval /: Quotient[m_Interval, n_] := Floor[m / n]
Interval /: QuotientRemainder[m_Interval, n_] := {Quotient[m, n], Mod[m, n]}
Protect[Interval];


LevelSpan = Replace[{{from_Integer, to_Integer} :> from ;; to, {n_Integer} :> {n}, n_Integer :> ;; n}]

AxisPart[i_] := If[i < 0, i, i + 1]

Splits[list_List] := TakeDrop[list, #] & /@ Range[0, Length[list]]

NameValuePattern := NameValuePattern = ResourceFunction["https://www.wolframcloud.com/obj/nikm/DeployedResources/Function/NameValuePattern/"]

