BeginTestSection["Tests"]

Needs["TinyGrad`"]





ApproximatelyEqual[x_,  y_,eps_:1*^-6] := Abs[Total[x - y, All]] < eps

VerificationTest[(* 1 *)
	ArrayQ[Normal[Tensor["Rand"[{5,  2}]]],  2]
	,
	True	
]

VerificationTest[(* 2 *)
	ArrayQ[Normal[Tensor["Rand"[{5,  2}]]["Cast"["Integer8"]]],  2, IntegerQ]
	,
	True	
]

VerificationTest[(* 3 *)
	With[{t = Tensor[{{1,  2, 3},  {4,  5, 6}},  "RequiresGradient" -> True]},  Total[Cos[Sin[t]],  All]["Backward"[]]; Normal[t["Gradient"]]]
	,
	{{-0.4028624892234802,  0.3283699154853821, 0.1392444521188736},  {-0.4487919211387634,  0.23219843208789825, 0.2648090422153473}}	
]

VerificationTest[(* 4 *)
	t = Tensor["Rand"[{4, 5}]]; 
u = Tensor["Rand"[{5, 4}]]; 
ApproximatelyEqual[Normal[t . u], Normal[t] . Normal[u]]
	,
	True	
]

EndTestSection[]
