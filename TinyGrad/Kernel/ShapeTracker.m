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

View[args___] := View @ "$New"[args]

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


mergeShapeStrides[ss_] := FixedPoint[
	SequenceReplace[
		s : {{shape1_, strides1_}, {shape2_, strides2_}} :> With[{
			newStrides = IntegerDigits[UnitVector[Length[shape1], #] . strides1, MixedRadix[shape2], Length[shape2]] . strides2 & /@ Range[Length[shape1]],
			dim = Times @@ shape1 - 1
		},
            If[ IntegerDigits[dim, MixedRadix[shape1], Length[shape1]] . newStrides == dim,
                {shape1, ReplacePart[newStrides, Position[shape1, 1] -> 0]},
                Splice @ ss
            ]
		]
	],
	ss
]

Class[ShapeTracker,

    "$Init"[self_, shape : _::[ShapeTracker] | {___Integer}, views : {_::[View] ...} | None : None] :> (
        self["Views"] = If[views === None, If[ShapeTracker["$Test"][shape], shape["Views"], ShapeViews[shape]], views];
        self
    ),

    (* "RealStrides"[self_, ignoreValid : False] :> Block[{idxs},
        If[Length[self["Views"]] == 1 && self["Views"][[-1]]["Mask"] === None, Return[self["Views"][[-1]]["Strides"]]];
        idxs = Interval[{0, # - 1}] & /@ self["Shape"];
        self["Views"][[-1]]["Shape"]
    ], *)

    "$Properties" -> {"ContiguousQ", "Shape", "Strides", "Offset", "Mask", "Rank", "Dimension"},

    "ContiguousQ"[self_] :> Length[self["Views"]] == 1 && self["Views"][[1]]["ContiguousQ"],
    "Shape"[self_] :> self["Views"][[-1]]["Shape"],
    "Strides"[self_] :> self["Views"][[-1]]["Strides"],
    "Offset"[self_] :> self["Views"][[-1]]["Offset"],
    "Mask"[self_] :> self["Views"][[-1]]["Mask"],
    "Rank"[self_] :> Length[self["Shape"]],
    "Dimesion"[self_] :> Times @@ self["Shape"],

    "Permute"[self_, perm_Cycles] :> Enclose @ With[{view = self["Views"][[-1]]},
        ConfirmAssert[PermutationLength[perm] <= self["Rank"]];
        self["Views"] = ReplacePart[self["Views"],
            -1 -> View[
                Permute[view["Shape"], perm],
                Permute[view["Strides"], perm],
                view["Offset"],
                If[view["Mask"] === None, None, Permute[view["Mask"], perm]]
            ]
        ];
        self
    ],
    "Permute"[self_, order_List] :> self["Permute"[FindPermutation[order]]],

    "Expand"[self_, shape_] :> Enclose[
        ConfirmAssert[Length[self["Shape"]] == Length[shape]];
        ConfirmAssert[And @@ MapThread[#1 == #2 || #2 == 1 && #3 == 0 &, {shape, self["Shape"], self["Strides"]}]];
        self["Views"] = ReplacePart[self["Views"],
            -1 -> View[shape, self["Strides"], self["Offset"], self["Mask"]]
        ];
        self
    ],

    "Reshape"[self_, shape : Shape] :> Enclose[
        ConfirmAssert[Times @@ shape == Times @@ self["Shape"]];
        With[{
            merge = mergeShapeStrides[{
                {shape, ShapeStrides[shape]},
                {self["Views"][[-1]]["Shape"], self["Views"][[-1]]["Strides"]}
            }]
        },
            If[ Length[merge] == 1,
                self["Views"] = ReplacePart[self["Views"], -1 -> View @@ merge[[1]]],
                self["Views"] = Append[self["Views"], View @@ merge[[1]]]
            ]
        ];
        self
    ],

    "Resize"[self_, size_, mask_ : None] :> Block[{
        offset = self["Strides"] . size[[All, 1]],
        nmask = None
    },
        If[ self["Mask"] =!= None,
            nmask = MapThread[{Max[#1[[1]] - #2[[1]], 0], Min[#1[[2]] - #2[[1]], #2[[2]] - #2[[1]]]} &, {self["Mask"], size}]
            If[ mask =!= None,
                nmask = MapThread[{Max[#1[[1]], #2[[1]]], Min[#1[[2]], #2[[2]]]} &, {nmask, mask}]
            ];
        ];
        self["Views"] = ReplacePart[self["Views"],
            -1 -> View[
                ReverseApplied[Subtract] @@@ size,
                self["Strides"],
                self["Offset"] + offset,
                nmask
            ]
        ];
        self
    ],

    "Pad"[self_, padding : {{_Integer ? NonNegative, _Integer ? NonNegative} ...}] :> Enclose[
        ConfirmAssert[Length[padding] == self["Rank"]];
        self["Resize"[Thread[{- #1, self["Shape"] + #2}], Thread[{#1, self["Shape"] + #1}]] & @@ Thread[padding]]
    ],

    "Shrink"[self_, shrink : {{_Integer ? NonNegative, _Integer ? NonNegative} ...}] :> Enclose[
        ConfirmAssert[Length[shrink] == self["Rank"]];
        ConfirmAssert[And @@ MapThread[#2[[1]] >= 0 && #2[[2]] <= #1 &, {self["Shape"], shrink}]];
        self["Resize"[shrink]]
    ],

    "Stride"[self_, mul : {__Integer}] :> Enclose @ Block[{
        strides, newShape, offset, mask
    },
        ConfirmAssert[AllTrue[mul, # != 0 &]];
        strides = mul * self["Strides"];
        newShape = Quotient[self["Shape"] + (Abs[mul] - 1), Abs[mul]];
        offset = (self["Shape"] - 1) . (self["Strides"] * Boole[Thread[mul < 0]]);
        mask = If[
            self["Mask"] === None,
            None,
            MapThread[
                {
                    If[#3 > 0, #1[[1]], #2 - #1[[2]]] + Quotient[Abs[#3] - 1, Abs[#3]],
                    If[#3 > 0, #1[[2]], #2 - #1[[1]]] + Quotient[Abs[#3] - 1, Abs[#3]]
                } &,
                {self["Mask"], self["Shape"], mul}
            ]
        ];
        self["Views"] = ReplacePart[self["Views"], -1 -> View[newShape, strides, self["Offset"] + offset, mask]];
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

