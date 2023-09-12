BeginTestSection["Tests"]

Needs["TinyGrad`"]





ApproximatelyEqual[x_,  y_,eps_:1*^-6] := Abs[Total[x - y, All]] / Times @@ Dimensions[x] < eps

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
	t = Tensor["Rand"[{4, 5}]]; 
u = Tensor["Rand"[{5, 4}]]; 
ApproximatelyEqual[Normal[t . u], Normal[t] . Normal[u]]
	,
	True	
]

BeginTestSection["Gradient"]

VerificationTest[(* 4 *)
	With[{t = Tensor[{{1,  2, 3},  {4,  5, 6}},  "RequiresGradient" -> True]},  Total[Cos[Sin[t]],  All]["Backward"[]]; Normal[t["Gradient"]]]
	,
	{{-0.4028624892234802,  0.3283699154853821, 0.1392444521188736},  {-0.4487919211387634,  0.23219843208789825, 0.2648090422153473}}	
]

VerificationTest[(* 5 *)
	With[{t=Tensor["Rand"[{4, 5}], "RequiresGradient"->True]}, 
ApproximatelyEqual[Normal@D[Total[t.t\[Transpose], 2], t], FunctionLayer[Function[t, Total[t.t\[Transpose], 2]]][Normal[t], NetPortGradient["t"]]]
]
	,
	True	
]

VerificationTest[(* 6 *)
	x = Tensor["Rand"[{4, 10}]]; 
y = Tensor[{0, 1, 2, 1}]; 
ApproximatelyEqual[Normal[x["SparseCategoricalCrossEntropy"[y]]], CrossEntropyLossLayer["Index"][Association["Input" -> SoftmaxLayer[][Normal[x]], 
    "Target" -> Normal[y] + 1]]]
	,
	True	
]

VerificationTest[(* 7 *)
	trainingData = ResourceData["MNIST", "TrainingData"]; 
Xtrain = Flatten @* ImageData /@ Keys[trainingData]; 
w = Tensor["ScaledUniform"[{784, 128}]]; 
ApproximatelyEqual[Xtrain . Normal[w], Normal[Tensor[Xtrain] . w]]
	,
	True	
]

EndTestSection[]

EndTestSection[]
