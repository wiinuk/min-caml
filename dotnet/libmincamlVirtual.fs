module LibmincamlVirtual

open Asm

let map =
    dict [
        typeof<bool>, Bool
        typeof<char>, Char
        typeof<double>, Float64
        typeof<double>, Float64
        typeof<int>, Int32
        typeof<nativeint>, NativeInt
        typeof<obj>, Object
        typeof<string>, String
    ]

let rec cliTypeOf t =
    let mutable r = Unchecked.defaultof<_>

    if t = typeof<System.Void> then failwith "void is not first class type"
    if map.TryGetValue(t, &r) then r
    elif t.IsArray && t.GetArrayRank() = 1 then t.GetElementType() |> cliTypeOf |> Array
    elif t.IsGenericParameter && not (isNull t.DeclaringMethod) then MethodTypeArgument t.Name
    else

    let rec aux (t: System.Type) =
        if t.IsNested then
            t.Name::aux t.DeclaringType
        else
            [t.Name]

    let kind = if t.IsValueType then type_kind.ValueType else type_kind.Class
    let moduleName = t.Assembly.GetName().Name.Split '.' |> Array.toList
    let nameSpace = t.Namespace.Split '.' |> Array.toList
    let nestedParents = if t.IsNested then aux t.DeclaringType |> List.rev else []
    let typeArgs = if t.IsGenericType then t.GetGenericArguments() |> Seq.map cliTypeOf |> Seq.toList else []
    TypeRef(kind, moduleName, nameSpace, nestedParents, t.Name, typeArgs)

[<RequiresExplicitTypeArguments>]
let clitypeof<'a> = cliTypeOf typeof<'a>

let consoleType = clitypeof<System.Console>
let textWriterType =  clitypeof<System.IO.TextWriter>
let getConsoleError = getProp(Static, textWriterType, consoleType, "Error")

let callStatic(resultType, declaringType, name, typeArgs, args) =
    call(false, Static, resultType, declaringType, Id.L name, typeArgs, args)

let libMethodDefCore (resultType, name, typeArgs, args) (maxStack, locals) opcodes =
    let body = {
        isEntrypoint = false
        maxStack = maxStack
        locals = Map.ofList locals
        opcodes = opcodes @ [Ret]
    }
    methodDef(Public, Static, Some resultType, name, typeArgs, args, body)

let libMethodDef (resultType, name, args) opcodes =
    libMethodDefCore (resultType, name, [], args) (None, []) opcodes

let libConvMethodDef outputType libName inputType convop =
    libMethodDef(outputType, libName, ["x", inputType]) [Ldarg0; convop]

let libReadParseMethodDef outputType libName =
    libMethodDef(outputType, libName, ["_arg1", unitType]) [
        callStatic(Some String, consoleType, "ReadLine", [], [])
        callStatic(Some outputType, outputType, "Parse", [], [String])
    ]

let libMathMethodDef libName mathName =
    callStatic(Some Float64, clitypeof<System.Math>, mathName, [], [Float64])
    |> libConvMethodDef Float64 libName Float64

let (!!) x = MethodTypeArgument x

let decls = [
    libMethodDef(unitType, "min_caml_print_newline", ["_arg1", unitType]) [
        callStatic(None, consoleType, "WriteLine", [], [])
        Ldnull
    ]
    libMethodDef(unitType, "min_caml_print_int", ["x", Int32]) [
        Ldarg0
        callStatic(None, consoleType, "Write", [], [Int32])
        Ldnull
    ]
    libMethodDef(unitType, "min_caml_print_byte", ["x", Int32]) [
        Ldarg0
        ConvOvfU1
        ConvU2
        callStatic(None, consoleType, "Write", [], [Char])
        Ldnull
    ]
    libMethodDef(unitType, "min_caml_prerr_int", ["x", Int32]) [
        getConsoleError
        Ldarg0
        callvirt(false, None, textWriterType, "Write", [Int32])
        Ldnull
    ]
    libMethodDef(unitType, "min_caml_prerr_byte", ["x", Int32]) [
        getConsoleError
        Ldarg0
        ConvOvfU1
        ConvU2
        callvirt(false, None, textWriterType, "Write", [Char])
        Ldnull
    ]
    libMethodDef(unitType, "min_caml_prerr_float", ["x", Float64]) [
        getConsoleError
        Ldarg0
        callvirt(false, None, textWriterType, "Write", [Float64])
        Ldnull
    ]
    libReadParseMethodDef Int32 "min_caml_read_int"
    libReadParseMethodDef Float64 "min_caml_read_float"
    libMethodDefCore(Array !!"T", "min_caml_create_array", ["T"], ["n", Int32; "x", !!"T"])
        (Some 5, [
            "xs", Array !!"T"
            "1", Int32
            "2", Int32
        ]) [
        
        Ldarg0
        Newarr !!"T"
        Stloc "xs"
        LdcI4 0
        Stloc "2"
        Ldarg0
        LdcI4 1
        Sub
        Stloc "1"
        Ldloc "1"
        Ldloc "2"
        Blt <| Id.L "finish"

        Label <| Id.L "loopHead"
        Ldloc "xs"
        Ldloc "2"
        Ldarg "x"
        Stelem !!"T"
        Ldloc "2"
        LdcI4 1
        Add
        Stloc "2"
        Ldloc "2"
        Ldloc "1"
        LdcI4 1
        Add
        BneUn <| Id.L "loopHead"

        Label <| Id.L "finish"
        Ldloc "xs"
    ]
    libMethodDef(Array Float64, "min_caml_create_float_array", ["n", Int32; "x", Float64]) [
        Ldarg0
        Ldarg "x"
        callStatic(Some(Array(MethodArgmentIndex 0)), Virtual.topLevelType, "min_caml_create_array", [Float64], [Int32; MethodArgmentIndex 0])
    ]
    libConvMethodDef Int32 "min_caml_int_of_float" Float64 ConvI4
    libConvMethodDef Int32 "min_caml_truncate" Float64 ConvI4
    libConvMethodDef Float64 "min_caml_float_of_int" Int32 ConvR8

    libMathMethodDef "min_caml_abs_float" "Abs"
    libMathMethodDef "min_caml_sqrt" "Sqrt"
    libMathMethodDef "min_caml_floor" "Floor"
    libMathMethodDef "min_caml_cos" "Cos"
    libMathMethodDef "min_caml_sin" "Sin"
    libMathMethodDef "min_caml_atan" "Atan"
]
