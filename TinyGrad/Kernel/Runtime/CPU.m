Package["TinyGrad`"]

PackageExport[CPUBuufer]



ShapeToAxis[oldShape : Shape, newShape : Shape] := Enclose[
    ConfirmAssert[Length[oldShape] == Length[newShape]];
    MapIndexed[If[Equal @@ #1, #2[[1]], Nothing] &, Thread[{oldShape, newShape}]]
]

OpFunctionMap = <|
    "ADD" -> Plus, "SUB" -> Subtract, "MUL" -> Times, "DIV" -> Divide,
    "SUM" -> Function[{x, shape}, If[x["Shape"] =!= shape, x["Sum"[ShapeToAxis[x["Shape"], shape], "KeepDims" -> True]], x]],
    "MAX" -> Function[{x, shape}, If[x["Shape"] =!= shape, x["Max"[ShapeToAxis[x["Shape"], shape], "KeepDims" -> True]], x]],
    "RESHAPE" -> Function[{x, shape}, x["Reshape"[shape]]],
    "SHRINK" -> Function[{x, arg}, x[[Sequence @@ Span @@@ arg]]],

    "NOOP" -> Function[{x}, x],
    "EXP2" -> (2 ^ # &),
    "LOG2" -> Log2,
    "CAST" -> Function[{x, type}, x["Cast"[type, "Copy" -> False]]],
    "SIN" -> Sin,
    "MAXIMUM" -> Max, "CMPEQ" -> Equal,
    "SQRT" -> Sqrt,

    "PERMUTE" -> Transpose, "PAD" -> ArrayPad, "EXPAND" -> Function[{x, shape}, x["Broadcast"[shape]]],
    "STRIDE" -> Function[{x, strides}, x[[Sequence @@ (;; ;; # & /@ strides)]]],
    "MULACC" -> EinsteinSummation,
    "WHERE" -> Function[Null, #1["Where"[##2]]]
|>

Class[StridedArrayBuffer[RawBuffer],
    "Init"[self_ , size_, type_, buf_] :>
        self["Class"]["Init"[size, type, If[buf === None, StridedArray["Empty"[size, type]], buf]]],
    "FromCPU"[cls_, x_] :> cls[x["Size"], x["Type"], x],
    "ToCPU"[self_] :> self["Data"]
]

CPUBuffer = Interpreted["New"[StridedArrayBuffer, OpFunctionMap, Automatic, Automatic, StridedArrayBuffer["FromCPU"[##]] &]]