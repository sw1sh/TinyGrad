Package["TinyGrad`"]

PackageImport["ForeignFunctionInterface`LibFFI`"]

PackageExport[TypeByteCount]



DeclareCompiledComponent[
    "TinyGrad",
    <|
        "InstalledFunctions" -> <|
            TypeByteCount ->
                Function[Typed[type, "InertExpression"],
                    LibFFITypeByteCount[CreateLibFFIType[Cast[type, "FFIType"]]]
                ]
        |>,
        "ExternalLibraries" -> "ForeignFunctionInterface"
    |>
]