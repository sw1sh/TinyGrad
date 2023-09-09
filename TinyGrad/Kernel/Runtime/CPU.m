Package["TinyGrad`"]

PackageExport[RawArrayBuffer]
PackageExport[CPUBuffer]

PackageImport["Wolfram`Class`"]



ShapeToAxis[oldShape : Shape, newShape : Shape] := Enclose[
    ConfirmAssert[Length[oldShape] == Length[newShape]];
    MapIndexed[If[Equal @@ #1, #2[[1]], Nothing] &, Thread[{oldShape, newShape}]]
]

OpFunctionMap = <|
    "ADD" -> Plus, "SUB" -> Subtract, "MUL" -> Times, "DIV" -> Divide,
    "CMPLT" -> Less, "MAXIMUM" -> Function[{x, y}, x["Maximum"[y]]],

    "SUM" -> Function[{x, lvl}, x["$Extend"]["Sum"[lvl, "KeepDims" -> True]]],
    "MAX" -> Function[{x, lvl}, x["$Extend"]["Max"[lvl, "KeepDims" -> True]]],

    "NOOP" -> Function[{x}, x],
    "EXP2" -> (2 ^ # &),
    "LOG2" -> Log2,
    "CAST" -> Function[{x, type}, x["Cast"[type]]],
    "SIN" -> Sin,
    "SQRT" -> Sqrt,
    "CMPEQ" -> Equal,

    "RESHAPE" -> ArrayReshape,
    "SHRINK" -> Function[{x, shrink}, x[[Sequence @@ Span @@@ (shrink + Threaded[{1, 0}])]]],
    "PERMUTE" -> Transpose, "PAD" -> ArrayPad, "EXPAND" -> Function[{x, shape}, x["$Extend"]["Expand"[shape]]],
    "STRIDE" -> Function[{x, strides}, x[[Sequence @@ (;; ;; # & /@ strides)]]],
    "MULACC" -> Function[{x, y, lvl}, (x * y)["Sum"[lvl, "KeepDims" -> True]]],
    "WHERE" -> Function[Null, #1["$Extend"]["Where"[##2]]]
|>

Class[RawArrayBuffer -> RawBuffer,
    "$Init"[self_ , size_, type_, buf_ : None] :> (
        RawBuffer["$Init"[self, size, type, If[buf === None, StridedArray["Empty"[size, type]], buf]]];
        self
    ),
    "FromCPU"[cls_, x_ ? NumericArrayQ] :> cls["$New"[Times @@ Dimensions[x], NumericArrayType[x], StridedArray[x]]],
    "FromCPU"[cls_, x_::[StridedArray]] :> cls["$New"[x["Dimension"], x["Type"], x]],
    "ToCPU"[self_] :> Normal[self["Data"]]
]

CPUBuffer = Interpreted["$New"[RawArrayBuffer, OpFunctionMap, Automatic, Automatic, RawArrayBuffer @* "FromCPU"], CPUBuffer]