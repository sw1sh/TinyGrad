Package["TinyGrad`"]

PackageExport[Node]
PackageExport[Variable]

PackageImport["Wolfram`Class`"]



Class[Node,
    "$Init"[self_, value_, min_, max_] :> (
        self["Value"] = value;
        self["Min"] = min;
        self["Max"] = max;

        (* dispatch to class UpValues *)
        self /: f_Symbol[left___, self, right___] /; MemberQ[Attributes[f], NumericFunction] := f[left, Node[self], right];
    )
]

(* Node /: Plus[left___, Node[x_], right___] := VariableSum[left, x, right] *)