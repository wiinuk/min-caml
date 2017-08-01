module LibmincamlVirtual

open MinCaml.Compiler.Ast
open MinCaml.Compiler.Cli
open AsmType
open Asm

let consoleType = asmtypeof<System.Console>
let textWriterType =  asmtypeof<System.IO.TextWriter>
let getConsoleError = getProp(Static, textWriterType, consoleType, "Error")


let libMethodDefCore (resultType, name, typeArgs, args) (maxStack, locals) opcodes =
    methodDef
        (Public, Static, resultType, Id.L name, typeArgs, args)
        (maxStack, locals)
        (opcodes @ [Ret])

let libMethodDef (resultType, name, args) opcodes =
    libMethodDefCore (Some resultType, name, [], args) (None, []) opcodes

let libUnitMethodDef (name, args) opcodes =
    libMethodDefCore
        (None, name, [], args)
        (None, [])
        opcodes
        // @ [Ldnull]

let libConvMethodDef outputType libName inputType convop =
    libMethodDef(outputType, libName, ["x", inputType]) [Ldarg0; convop]

let libReadParseMethodDef outputType libName =
    libMethodDef(outputType, libName, []) [
        call(Static, Some String, consoleType, "ReadLine", [], [])
        call(Static, Some outputType, outputType, "Parse", [], [String])
    ]

let libMathMethodDef libName mathName =
    call(Static, Some Float64, asmtypeof<System.Math>, mathName, [], [Float64])
    |> libConvMethodDef Float64 libName Float64

let (!!) x = MethodTypeArgument x

let decls = [
    libUnitMethodDef("min_caml_print_newline", []) [
        call(Static, None, consoleType, "WriteLine", [], [])
    ]
    libUnitMethodDef("min_caml_print_int", ["x", Int32]) [
        Ldarg0
        call(Static, None, consoleType, "Write", [], [Int32])
    ]
    libUnitMethodDef("min_caml_print_byte", ["x", Int32]) [
        Ldarg0
        ConvOvfU1
        ConvU2
        call(Static, None, consoleType, "Write", [], [Char])
    ]
    libUnitMethodDef("min_caml_prerr_int", ["x", Int32]) [
        getConsoleError
        Ldarg0
        callvirt(None, textWriterType, "Write", [Int32])
    ]
    libUnitMethodDef("min_caml_prerr_byte", ["x", Int32]) [
        getConsoleError
        Ldarg0
        ConvOvfU1
        ConvU2
        callvirt(None, textWriterType, "Write", [Char])
    ]
    libUnitMethodDef("min_caml_prerr_float", ["x", Float64]) [
        getConsoleError
        Ldarg0
        callvirt(None, textWriterType, "Write", [Float64])
    ]
    libReadParseMethodDef Int32 "min_caml_read_int"
    libReadParseMethodDef Float64 "min_caml_read_float"
    libMethodDefCore(Some(Array !!"T"), "min_caml_create_array", ["T"], ["n", Int32; "x", !!"T"])
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
        call(Static, Some(Array(MethodArgmentIndex 0)), Virtual.topLevelType, "min_caml_create_array", [Float64], [Int32; MethodArgmentIndex 0])
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
