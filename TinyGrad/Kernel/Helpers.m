Package["TinyGrad`"]

PackageExport[CoIdentity]
PackageExport[InheritDefinitions]
PackageExport[TraceSteps]
PackageExport[DelayedDefinition]
PackageExport[DelayedBlock]



expr_[CoIdentity] ^:= expr


Unprotect[Interval];
Interval /: Mod[m_Interval, n_Integer] := Interval @ If[Max[m] - Min[m] >= n || Min[m] != Max[m] && Mod[Min[m], n] >= Mod[Max[m], n], {0, n - 1}, {Mod[Min[m], n], Mod[Max[m], n]}]
Interval /: Quotient[m_Interval, n_] := Floor[m / n]
Interval /: QuotientRemainder[m_Interval, n_] := {Quotient[m, n], Mod[m, n]}
Protect[Interval];



SetAttributes[{TraceSteps, DelayedDefinition, DelayedBlock, DelayedBlockSteps}, HoldAll]

$Debug = False;

TraceSteps[expr_, steps_Integer : 1, opts : OptionsPattern[TraceScan]] := Block[{count = 0, res},
	res = TraceScan[
		If[ count >= steps,
			If[$Debug, EchoLabel["Finish"][InputForm[#]]]; Return[#, TraceScan],
			If[$Debug, EchoLabel[count][InputForm[#]]]; count++;
		] &,
		expr,
		opts,
		TraceDepth -> 1
	];
	If[res === Unevaluated[expr], If[MatchQ[Unevaluated[expr], _HoldForm], expr, HoldForm[expr]], If[MatchQ[res, _HoldForm], res, HoldForm[Evaluate @ res]]]
]

DelayedBlockSteps[vars_, expr_, steps_Integer : 1, opts : OptionsPattern[TraceScan]] := Block[{count = 0},
	TraceScan[
		If[ count >= steps,
			If[$Debug, EchoLabel["Finish"][InputForm[#]]]; Return[Block[vars, ReleaseHold @ #], TraceScan],
			If[$Debug, EchoLabel[count][InputForm[#]]]; count++;
		] &,
		expr,
		opts,
		TraceDepth -> 1
	]
]

DelayedDefinition[vars_, expr_, steps_Integer : 1, opts : OptionsPattern[TraceSteps]] := Block[{count = 0, withExpr, blockExpr},
	withExpr = TraceSteps[expr, steps, opts];
	If[$Debug, EchoLabel["Before"] @ InputForm @ withExpr];
	blockExpr = With[vars, Evaluate[withExpr]];
	If[$Debug, EchoLabel["After"] @ InputForm @ blockExpr];
	blockExpr
]

DelayedBlock[a_, b_, expr_, args___] := Module[{c}, With[{tmp = DelayedDefinition[{a = c}, expr, args]},
	If[ (* unevaluated *)
		tmp === (HoldForm[expr] /. a -> c),
		expr,
		(* recurse with default arguments *)
		Function[Null, DelayedBlock[a, b, #], HoldAll] @@ (tmp /. c -> b)
	]
]]

SetAttributes[InheritDefinitions, HoldAll]

InheritDefinitions[a_ ? Developer`SymbolQ, b_ ? Developer`SymbolQ] := Module[{$Override = True},
	(* Inherit DownValues and SubValues *)
	b[args___] := DelayedBlock[a, b, a[args]];

	(* Inherit FormatValues. Needs to handle some internal stuff, hopefull it won't change.
		Evaluate on a parallel kernel, otherwise Trace doesn't work inside MakeBoxes for some mysterious reason *)
	MakeBoxes[b, form___] ^:= Enclose @ ParallelEvaluate[
		DelayedBlock[a, b, MakeBoxes[a, form], 2, TraceInternal -> True, TraceDepth -> Infinity],
		ConfirmMatch[First[Kernels[], First @ LaunchKernels[1]], _KernelObject]
	];

	(* NValues is also tricky *)
	AppendTo[NValues[b], HoldPattern[N[b, args___]] :>
		DelayedBlock[a, b, N[a, args], Evaluate[3 + Length[{args}]], TraceInternal -> True, TraceDepth -> Infinity]];

	(* Inherit Messages *)
	AppendTo[Messages[b], HoldPattern[MessageName[b, tag_]] :> With[{msg = MessageName[a, tag]}, msg /; StringQ[msg]]];

	(* Inherit DefaultValues *)
	DefaultValues[b] = {
		(* arguments for default like Default[b, 2] doesn't work because of a bug *)
		HoldPattern[Default[b, args___]] :> Default[a, args],
		HoldPattern[Options[b, args___]] :> Options[a, args]
	};

	(* Inherit the rest of UpValues only when they're actully defined
		to avoid locking out functions that work with symbols, like Clear, Remove etc.
	*)
	head_[left___, b, right___] /;
		MatchQ[
			Unevaluated[head[left, a, right]],
			Alternatives @@ Keys @ UpValues[a]
		] ^:= DelayedBlock[a, b, head[left, a, right]];

	(* Attributes are copied, no way to inherit it that I know of *)
	Attributes[b] = Attributes[a];
]

