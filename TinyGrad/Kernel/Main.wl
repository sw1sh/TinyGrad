Package["TinyGrad`"]



$DistributedContexts = {"Global`", "TinyGrad`"}


Unprotect[TypeSpecifier]
TypeSpecifier[patt_][type_Symbol] := patt ? (type["Test"])
TypeSpecifier[patt_][type : Except[_String]] := patt ? (MatchQ[type])
Protect[TypeSpecifier]

