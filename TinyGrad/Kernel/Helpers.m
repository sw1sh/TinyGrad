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


ClearAll[TraceSteps, DelayedDefinition, DelayedBlock]
SetAttributes[{TraceSteps, DelayedDefinition, DelayedBlock}, HoldAll]

TraceSteps[expr_, steps_Integer : 1, opts : OptionsPattern[TraceScan]] := Block[{count = 0, res},
	res = TraceScan[
		If[ count >= steps,
			Return[#, TraceScan],
			count++;
		] &,
		expr,
		opts,
		TraceDepth -> 1
	];
	If[res === Unevaluated[expr], HoldForm[expr], res]
]

DelayedDefinition[vars_, expr_, steps_Integer : 1, opts : OptionsPattern[TraceSteps]] := Block[{count = 0, withExpr, blockExpr},
	withExpr = TraceSteps[expr, steps, opts];
	blockExpr = With[vars, Evaluate[withExpr]];
	blockExpr
]

DelayedBlock[a_, b_, expr_, args___] := Module[{c}, With[{tmp = DelayedDefinition[{a = c}, expr, args]},
	If[ (* unevaluated *)
		tmp === {} || tmp === (HoldForm[expr] /. HoldPattern[a] :> c),
		expr,
		(* recurse with default arguments *)
		Function[Null, DelayedBlock[a, b, #], HoldAll] @@ (tmp /. c :> b)
	]
]]

SetAttributes[InheritDefinitions, HoldAll]

(*$UpValueBlock = True;*)

InheritDefinitions[a_ ? Developer`SymbolQ, b_ ? Developer`SymbolQ] := (
	(* Inherit DownValues and SubValues *)
	b[args___] := DelayedBlock[a, b, a[args]];

	(* Inherit FormatValues. Needs TraceInternal and one more step to go deeper.
		Evaluate on a parallel kernel, otherwise Trace doesn't work inside MakeBoxes for some mysterious reason *)
	MakeBoxes[b, form___] ^:= Enclose @ ParallelEvaluate[
		DelayedBlock[a, b, MakeBoxes[a, form], 2, TraceInternal -> True, TraceDepth -> Infinity],
		ConfirmMatch[First[Kernels[], First @ LaunchKernels[1, ProgressReporting -> None]], _KernelObject],
		DistributedContexts -> Automatic
	];

	(* NValues is also tricky as it evaluates its arguments *)
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
	(*expr : head_[___, b, ___] /; $UpValueBlock ^:= Block[{$UpValueBlock = False, newHoldExpr},
		newHoldExpr = Hold[expr] /. HoldPattern[b] :> a;
		Function[Null, Block[{$UpValueBlock = True}, DelayedBlock[a, b, #]], HoldAll] @@ newHoldExpr /;
		Function[Null, MatchQ[
			Unevaluated[#],
			Alternatives @@ Keys @ UpValues[a]
		], HoldAll] @@ newHoldExpr
	];*)
	head_[left___, b, right___] /; MatchQ[
		Unevaluated[head[left, a, right]],
		Alternatives @@ Keys @ UpValues[a]
	] ^:= DelayedBlock[a, b, head[left, a, right]];

	(* Same for OwnValues *)
	b /;
		MatchQ[
			Unevaluated[a],
			Alternatives @@ Keys @ OwnValues[a]
		] := a;

	(* Attributes are copied, no way to inherit it that I know of *)
	Attributes[b] = Attributes[a];
)