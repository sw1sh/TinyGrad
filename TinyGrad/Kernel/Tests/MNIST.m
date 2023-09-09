Package["TinyGrad`Tests`MNIST`"]

PackageExport[TinyBobNet]

PackageImport["TinyGrad`"]
PackageImport["Wolfram`Class`"]



Class[TinyBobNet,
    "$Init"[self_] :> (
        self["l1"] = Tensor["ScaledUniform"[{784, 128}]];
        self["l2"] = Tensor["ScaledUniform"[{128, 10}]]
    ),
    "Forward"[self_, x_] :> ((x . self["l1"])["ReLU"[]] . self["l2"]) @ "LogSoftMax"[]
]