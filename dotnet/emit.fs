module Emit
open Asm
open FSharp.Compatibility.OCaml

let (+=) o s = output_string o s

let newline oc i =
    oc += "\n"
    for _ in 1..i do oc += "    "

let groupCore emptyIfIgnore first emit sep last o = function
    | [] ->
        if emptyIfIgnore then () else
        o += first
        o += last

    | x::xs ->
        o += first
        emit o x
        for x in xs do
            o += sep
            emit o x
        o += last

let groupOrEmpty first emit sep last o xs = groupCore true first emit sep last o xs
let group first emit sep last o xs = groupCore false first emit sep last o xs

// TODO: エスケープ処理
let name oc = function
| "" -> oc += "''"
| x ->
    let isIdentifier =
        String.forall (fun c ->
            ('a' <= c && c <= 'z') ||
            ('A' <= c && c <= 'Z') ||
            c = '_' ||
            ('0' <= c && c <= '9')
        ) x

    if isIdentifier then oc += x
    else fprintf oc "'%s'" x

let rec type' oc = function
    | This -> oc += ".this"
    | Void -> oc += "void"
    | Bool -> oc += "bool"
    | Int32 -> oc += "int32"
    | Float64 -> oc += "float64"
    | Object -> oc += "object"
    | NativeInt -> oc += "native int"
    | Array t -> type' oc t; oc += "[]"
    | TypeArgmentIndex x -> fprintf oc "!%d" x
    | TypeName(kind, moduleName, nameSpace, nestedParents, typeName, typeArgs) ->
        oc += match kind with Class -> "class " | ValueType -> "valuetype "
        groupOrEmpty "[" name "." "]" oc moduleName
        for x in nameSpace do (name oc x; oc += ".")
        for x in nestedParents do (name oc x; oc += "/")
        name oc typeName
        groupOrEmpty "<" type' ", " ">" oc typeArgs
        
let arg oc (x, t) = type' oc <| cliType t; oc += " "; name oc x
let args i oc xs =
    match xs with
    | [] -> oc += "()"
    | _ ->

    newline oc i
    oc += "("
    group "" (fun oc x -> newline oc (i + 1); arg oc x) "," "" oc xs
    newline oc i
    oc += ")"

let methodName oc = function
    | Ctor -> oc += ".ctor"
    | MethodName(Id.L n) -> name oc n

let methodRef oc { call_conv = c; resultType = r; declaringType = t; methodName = n; argTypes = ts } =
    oc += match c with Instance -> "instance " | Static -> ""
    type' oc r
    oc += " "
    type' oc t
    oc += "::"
    methodName oc n
    group "(" type' ", " ")" oc ts

let fieldRef oc { fieldType = ft; declaringType = t; name = Id.L n } =
    type' oc ft
    oc += " "
    type' oc t
    oc += "::"
    name oc n

let ldc_i4 oc = function
    | -1 -> oc += "ldc.i4.m1"
    | 0 -> oc += "ldc.i4.0"
    | 1 -> oc += "ldc.i4.1"
    | 2 -> oc += "ldc.i4.2"
    | 3 -> oc += "ldc.i4.3"
    | 4 -> oc += "ldc.i4.4"
    | 5 -> oc += "ldc.i4.5"
    | 6 -> oc += "ldc.i4.6"
    | 7 -> oc += "ldc.i4.7"
    | 8 -> oc += "ldc.i4.8"
    | x when -128 <= x && x <= 127 -> fprintf oc "ldc.i4.s %d" x
    | x -> fprintf oc "ldc.i4 %d" x

let ldc_r8 oc x =
    if float_of_int (int_of_float x) = x
    then fprintf oc "ldc.r8 %f" x
    else fprintf oc "ldc.r8 0x%016X" <| System.BitConverter.DoubleToInt64Bits x

let rec arrayAccess u1 i4 r8 ref = function
    | Type.Bool -> u1
    | Type.Int -> i4
    | Type.Float -> r8
    | Type.Array _
    | Type.Fun _
    | Type.Unit
    | Type.Tuple _ -> ref
    | Type.Var { contents = Some t } -> arrayAccess u1 i4 r8 ref t
    | Type.Var { contents = None } -> failwith "unexpected type 'Var'"

let ldelem t = arrayAccess "ldelem.u1" "ldelem.i4" "ldelem.r8" "ldelem.ref" t
let stelem t = arrayAccess "stelem.u1" "stelem.i4" "stelem.r8" "stelem.ref" t

/// 命令のアセンブリ生成 (caml2html: emit_gprime)
let opcode oc = function
    | Label(Id.L l) -> name oc l; oc += ":"

    | Dup -> oc += "dup"
    | Pop -> oc += "pop"
    | Add -> oc += "add"
    | Neg -> oc += "neg"
    | Sub -> oc += "sub"
    | Mul -> oc += "mul"
    | Div -> oc += "div"
    | Ldloc_0 -> oc += "ldloc.0"
    | Ldnull -> oc += "ldnull"
    | Ldc_I4 x -> ldc_i4 oc x
    | Ldc_R8 x -> ldc_r8 oc x
    
    | Beq(Id.L l) -> oc += "beq "; name oc l
    | Ble(Id.L l) -> oc += "ble "; name oc l

    | Ldarg l -> oc += "ldarg "; name oc l
    | Ldloc l -> oc += "ldloc "; name oc l
    | Stloc l -> oc += "stloc "; name oc l

    | Call m -> oc += "call "; methodRef oc m
    | Ret -> oc += "ret"

    | Ldelem t -> oc += ldelem t
    | Stelem t -> oc += stelem t
    | Newobj(declaringType, argTypes) ->
        fprintf oc "newobj instance void "
        type' oc declaringType
        oc += "::.ctor"
        group "(" type' ", " ")" oc argTypes

    | Ldfld f -> oc += "ldfld "; fieldRef oc f
    | Stfld f -> oc += "stfld "; fieldRef oc f
    | Callvirt m -> oc += "callvirt "; methodRef oc m
    | Ldftn m -> oc += "ldftn "; methodRef oc m

let custom oc = function
    | { ctor = ctor; args = []; namedArgs = [] } -> methodRef oc ctor

    // TODO:
    | _ -> failwith "not implemented"

let accessNonNested = function
    | Public -> "public "
    | Default -> ""

// .method assembly hidebysig instance int32 '<F>b__0'
// (
//     int32 x
// )
// {
//     .entrypoint
//     .locals (
//         
//     )
//     ...
// }
let methodBody i oc { isEntrypoint = isEntrypoint; locals = locals; opcodes = ops } =
    if isEntrypoint then
        newline oc i
        oc += ".entrypoint"

    match locals with
    | [] -> ()
    | _ ->
        newline oc i
        oc += ".locals "
        args i oc locals

    for op in ops do
        newline oc i
        opcode oc op

let methodDef i oc
    {
        access = a
        callconv = c
        resultType = r
        name = Id.L n
        args = xs
        isForwardref = isForwardref
        body = body
    }
    =

    oc += accessNonNested a
    oc += "hidebysig "
    oc += match c with Instance -> "instance " | Static -> "static "
    type' oc r
    oc += " "
    name oc n
    args i oc xs
    // newline oc i
    // oc += "cil managed"
    oc += if isForwardref then " forwardref" else ""
    newline oc i
    oc += "{"
    methodBody (i + 1) oc body
    newline oc i
    oc += "}"

let fieldDef oc { access = a; fieldType = t; name = Id.L n } =
    oc += accessNonNested a
    type' oc t
    oc += " "
    name oc n
    
let rec classDecl i oc = function
    | Custom x -> oc += ".custom "; custom oc x
    | Method m -> oc += ".method "; methodDef i oc m
    | Field f -> oc += ".field "; fieldDef oc f
    | NestedClass c -> oc += ".class "; classDef true i oc c

and classDef nested i oc
    {
        isSealed = isSealed
        isBeforefieldinit = isBeforefieldinit
        name = Id.L n
        body = body
    }
    =
    if isSealed then oc += "sealed "
    if isBeforefieldinit then oc += "beforefieldinit "
    name oc n
    newline oc i
    oc += "{"
    newline oc (i + 1)
    for d in body do
        classDecl (i + 1) oc d
        newline oc i
    newline oc i
    oc += "}"

let makeEntryPoint { name = n; resultType = resultType } =
    let body = {
        isEntrypoint = true
        locals = []
        opcodes =
        [
            Call <| Asm.methodRef(Static, resultType, Virtual.topLevelType, MethodName n, [])
            Pop
            Ret
        ]
    }
    Method {
        access = Public
        callconv = Static
        resultType = Void
        name = Id.L "Main"
        args = []
        isForwardref = false
        body = body
    }

let f oc (Prog(decls, e)) =
    eprintf "generating assembly...@."

    fprintfn oc ".assembly mincaml_module_0 {}"
    fprintfn oc ".assembly extern mscorlib {}"

    fprintfn oc ".class public abstract sealed beforefieldinit %s" Virtual.topLevelTypeName
    oc += "{"
    newline oc 1
    for d in decls do
        classDecl 1 oc d
        newline oc 1
    classDecl 1 oc <| Method e

    newline oc 1
    classDecl 1 oc <| makeEntryPoint e

    newline oc 0
    fprintfn oc "}"
