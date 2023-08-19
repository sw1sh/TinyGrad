Package["TinyGrad`"]

PackageExport[View]
PackageExport[ViewReshape]
PackageExport[ShapeTracker]

PackageExport[ShapeStrides]

PackageScope[Dimension]
PackageScope[Size]
PackageScope[Shape]
PackageScope[Strides]
PackageScope[mergeShapeStrides]

PackageImport["Wolfram`Class`"]



Dimension = _Integer ? NonNegative
Size = _Integer ? Positive
Shape = {Dimension ...}
Strides = {___Integer}


ShapeStrides[shape : Shape, size : Size : 1] :=
    If[ shape === {},
        {},
        MapThread[If[#2 == 1, 0, #1] &, {Reverse[FoldList[Times, size, shape[[-1 ;; 2 ;; -1]]]], shape}]
    ]

ShapeStrides[shape : Shape, strides : Strides] := Enclose @ With[{shapeStrides = Thread[{shape, strides}]},
    ConfirmAssert[Length[shape] == Length[strides]];
    If[shape === {}, Return[{}]];
    Fold[
        If[#1[[-1, 2]] == #2[[1]] * #2[[2]] || #1[[-1, 1]] == 1, ReplacePart[#1, -1 -> {#1[[1]] * #2[[1]], #2[[2]]}], If[#2[[1]] == 1, #1, Append[#1, #2]]] &,
        {First[shapeStrides]},
        Rest[shapeStrides]
    ]
]

ContiguousQ[shape : Shape, strides : Strides] := And @@ MapThread[#2 == #3 || #1 == 1 &, {shape, strides, ShapeStrides[shape]}]

FilterStrides[shape : Shape, strides : Strides] := MapThread[If[#2 == 1, 0, #1] &, {strides, shape}]


ShapeViews[shape_] := {View["$New"[shape]]}


Class[
    View,

    "$Init"[self_, shape_, initStrides_ : None, offset_ : 0, mask_ : None] :> Block[{
        stridesFromShape = ShapeStrides[shape],
        strides, contiguous
    },
        strides = If[initStrides === None, stridesFromShape, FilterStrides[shape, initStrides]];
        contiguous = offset == 0 && ContiguousQ[shape, strides] && mask === None;
        self["Shape"] = shape;
        self["Strides"] = strides;
        self["Offset"] = offset;
        self["Mask"] = mask;
        self["ContiguousQ"] = contiguous;
        self["ShapeStrides"] = ShapeStrides[shape, strides];
        self
    ],

    "Node"[self_, idx : Variable["$Type"] | None : None] :> With[{
        x = Replace[idx, None :> Variable["idx", 0, Times @@ self["Shape"] - 1]]
    },
        Total @ Fold[
            List /* Replace[
                {{acc_, ret_}, {d_, s_}} :>
                    {acc * d, Append[ret, Mod[Quotient[x, acc], d] * s]}
            ],
            {1, {self["Offset"]}},
            Reverse[self["ShapeStrides"]]
        ]
    ],
    "Indices"[self_, idxs_] :> Enclose[
        ConfirmAssert[Length[idsx] == Length[self["Shape"]]];
        Total @ Prepend[self["Offset"]] @
            MapThread[
                If[#2 == 1 || #3 == 0, Nothing, #1 * #3] &,
                {idxs, self["Shape"], self["Strides"]}
            ]
    ],

    "$Format"[self_, form_] :> BoxForm`ArrangeSummaryBox[
        "View",
        self,
        None,
        {
            {BoxForm`MakeSummaryItem[{"Shape: ", self["Shape"]}, form]},
            {BoxForm`MakeSummaryItem[{"Strides: ", self["Strides"]}, form]},
            {BoxForm`MakeSummaryItem[{"Offset: ", self["Offset"]}, form]},
            {BoxForm`MakeSummaryItem[{"Mask: ", self["Mask"]}, form]}
        },
        {
            BoxForm`MakeSummaryItem[{"ContiguousQ: ", self["ContiguousQ"]}, form]
        },
        form
    ]
]

View[shape_, initStrides_ : None, offset_ : 0, mask_ : None] :=
    View @ "$New"[shape, initStrides, offset, mask]

MergeViews[view2_, view1_] := Block[{st, strides},
    If[view2["Mask"] =!= None, Return[None]];
    st = ShapeTracker[view1["Shape"], {view2, view1}];
    strides = st["RealStrides"[]];
    If[MemberQ[strides, None], Return[None]];
    View[view1["Shape"], strides, st["RealOffset"], view1["Mask"]]
]

ViewReshape[view_::[View], newShape : Shape] := Block[{
    shape, mask, strides, offset,
    pos, newPos,
    newView, mergedView, newStrides, newMask
},
    {shape, mask, strides, offset} = view /@ {"Shape", "Mask", "Strides", "Offset"};
    {pos, newPos} = Position[#, Except[1], {1}, Heads -> False] & /@ {shape, newShape};
    If[ Extract[shape, pos] === Extract[newShape, newPos],
        newStrides = ReplacePart[
            Replace[newShape, 1 -> 0, {1}],
            Thread[newPos -> Extract[strides, pos]]
        ];
        newMask = If[
            mask === None,
            None,
            If[
                MemberQ[Thread[{shape, mask}], {1, Except[{0, 1}]}],
                ConstantArray[{0, 0}, Length[newShape]],
                ReplacePart[
                    Replace[newShape, 1 -> {0, 1}, {1}],
                    Thread[newPos -> Extract[mask, pos]]
                ]
            ]
        ];
        Return[{View[newShape, newStrides, offset, newMask], False}]
    ];
    newView = View[newShape, ShapeStrides[newShape]];
    If[view["ContiguousQ"], Return[{newView, False}]];
    mergedView = MergeViews[view, newView];
    If[mergedView =!= None, Return[{mergedView, False}]];
    {newView, True}
]


shapesCompatibleQ[{l_, ls___}, {r_, rs___}] := Which[Divisible[l, r], shapesCompatibleQ[{l / r, ls}, {rs}], Divisible[r, l], shapesCompatibleQ[{ls}, {r / l, rs}], True, False]
shapesCompatibleQ[{1}, {}] := True
shapesCompatibleQ[{}, {1}] := True
shapesCompatibleQ[{}, {}] := True
shapesCompatibleQ[_, _] := False

mergeShapeStrides[ss_] := FixedPoint[
	SequenceReplace[
		s : {{shape1_, strides_}, {shape2_, _}} /; shapesCompatibleQ[shape2, shape1[[Reverse @ Ordering[strides]]]] :> {
			shape1,
			Fold[
                IntegerDigits[#1, MixedRadix[#2[[1]]], Length[#2[[1]]]] . #2[[2]] &,
                FromDigits[UnitVector[Length[shape1], #], MixedRadix[shape1]],
                s
            ] & /@ Range[Length[shape1]]
		}
	],
	ss
]

Class[ShapeTracker,

    "$Init"[self_, shape : (_::[ShapeTracker]) | {___Integer}, views : {_::[View] ...} | None : None] :> (
        self["Views"] = If[views === None, If[MatchQ[shape, ShapeTracker["$Type"]], shape["Views"], ShapeViews[shape]], views];
        self
    ),

    (* "RealStrides"[self_, ignoreValid : False] :> Block[{idxs},
        If[Length[self["Views"]] == 1 && self["Views"][[-1]]["Mask"] === None, Return[self["Views"][[-1]]["Strides"]]];
        idxs = Interval[{0, # - 1}] & /@ self["Shape"];
        self["Views"][[-1]]["Shape"]
    ], *)

    "$Properties" -> {"ContiguousQ", "Shape"},

    "ContiguousQ"[self_] :> Length[self["Views"]] == 1 && self["Views"][[1]]["ContiguousQ"],
    "Shape"[self_] :> self["Views"][[-1]]["Shape"],

    "Permute"[self_, perm_Cycles] :> With[{view = self["Views"][[-1]]},
        self["Views"] = ReplacePart[self["Views"],
            -1 -> View[
                Permute[view["Shape"], perm],
                Permute[view["Strides"], perm],
                view["Offset"],
                If[view["Mask"] === None, None, Permute[view["Mask"], perm]]
            ]
        ]
    ],
    "Permute"[self_, perm_List] :> self["Permute"[FindPermutation[perm]]],

    "Reshape"[self_, shape : Shape] :> Enclose[
        ConfirmAssert[Times @@ shape == Times @@ self["Shape"]];
        With[{
            merge = mergeShapeStrides[{
                {shape, ShapeStrides[shape]},
                {self["Views"][[-1]]["Shape"], self["Views"][[-1]]["Strides"]}
            }]
        },
            If[ Length[merge] == 1,
                self["Views"] = ReplacePart[self["Views"], -1 -> View @@ merge],
                self["Views"] = Append[self["Views"], View @@ merge[[1]]]
            ]
        ];
        self
    ],

    "$Format"[self_, form_] :> BoxForm`ArrangeSummaryBox[
        "ShapeTracker",
        self,
        None,
        {
            {BoxForm`MakeSummaryItem[{"Shape: ", self["Shape"]}, form]},
            {BoxForm`MakeSummaryItem[{"ContiguousQ: ", self["ContiguousQ"]}, form]}
        },
        {
            {BoxForm`MakeSummaryItem[{"Views: ", self["Views"]}, form]}
        },
        form
    ]
]

ShapeTracker[shape_, views_ : None] := ShapeTracker["$New"[shape, views]]

