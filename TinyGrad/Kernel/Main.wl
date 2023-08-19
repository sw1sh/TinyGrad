Package["TinyGrad`"]

PackageImport["Wolfram`Class`"]



Needs["Wolfram`Class`"]


$DistributedContexts = {"Global`", "TinyGrad`"}


Unprotect[TypeSpecifier]
TypeSpecifier[patt_][type_Symbol] := patt ? (type["$Test"])
TypeSpecifier[patt_][type : Except[_String]] := patt ? (MatchQ[type])
Protect[TypeSpecifier]

If[ Length[PacletFind["Wolfram/Class"]] == 0,
    PacletInstall["Wolfram/Class"];
]

