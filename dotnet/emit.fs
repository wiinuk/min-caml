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

    let inRange (lo, hi) x = lo <= x && x <= hi

    let isIdStart = function
        | '_' | '`' -> true
        | c -> inRange ('a', 'z') c || inRange ('A', 'Z') c

    let isIdContinue c = isIdStart c || inRange ('0', '9') c
    let rec isIdTail i = x.Length <= i || (isIdContinue x.[i] && isIdTail (i + 1))

    if isIdStart x.[0] && isIdTail 1 then oc += x
    else fprintf oc "'%s'" x

let rec type' oc = function
    | This -> oc += ".this"
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

let resultType oc = function
    | None -> oc += "void"
    | Some t -> type' oc t

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
    resultType oc r
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
    | Ldarg_0 -> oc += "ldarg.0"
    | Ldnull -> oc += "ldnull"
    | Ldc_I4 x -> ldc_i4 oc x
    | Ldc_R8 x -> ldc_r8 oc x

    | Br(Id.L l) -> oc += "br "; name oc l
    | Beq(Id.L l) -> oc += "beq "; name oc l
    | Ble(Id.L l) -> oc += "ble "; name oc l

    | Ldarg l -> oc += "ldarg "; name oc l
    | Ldloc l -> oc += "ldloc "; name oc l
    | Stloc l -> oc += "stloc "; name oc l

    | Call(tail, m) ->
        oc += if tail then "tail. call " else "call "
        methodRef oc m

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
    | Ldsfld f -> oc += "ldsfld "; fieldRef oc f
    | Callvirt(tail, m) ->
        oc += if tail then "tail. callvirt " else "callvirt "
        methodRef oc m

    | Ldftn m -> oc += "ldftn "; methodRef oc m

let opcodes hasTail i oc ops =
    for op in ops do
        newline oc i
        opcode oc op
    
let custom oc x =
    oc += ".custom "

    match x with
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
//     .locals init (
//         
//     )
//     ...
// }
let methodBody i oc { isEntrypoint = isEntrypoint; locals = locals; opcodes = ops } =
    if isEntrypoint then
        newline oc i
        oc += ".entrypoint"

    if not <| List.isEmpty locals then
        newline oc i
        oc += ".locals init "
        args i oc locals

    opcodes true i oc ops

let methodDef i oc
    {
        access = access
        isSpecialname = isSpecialname
        isRtspecialname = isRtspecialname
        callconv = callconv
        resultType = r
        name = name
        args = xs
        isForwardref = isForwardref
        body = body
    }
    =
    oc += ".method "
    oc += accessNonNested access
    oc += "hidebysig "
    if isSpecialname then oc += "specialname "
    if isRtspecialname then oc += "rtspecialname "
    oc += match callconv with Instance -> "instance " | Static -> "static "
    resultType oc r
    oc += " "
    methodName oc name
    args i oc xs

    // 23.1.11[MethodImplAttributes] IL = 0x0000; managed = 0x0000
    // newline oc i
    // oc += "cil managed"
    oc += if isForwardref then " forwardref" else ""

    newline oc i
    oc += "{"
    methodBody (i + 1) oc body
    newline oc i
    oc += "}"

let fieldDef oc { access = a; fieldType = t; name = Id.L n } =
    oc += ".field "
    oc += accessNonNested a
    type' oc t
    oc += " "
    name oc n

let rec classDecl i oc = function
    | Custom x -> custom oc x
    | Method m -> methodDef i oc m
    | Field f -> fieldDef oc f
    | NestedClass c -> classDef true i oc c

and classDef nested i oc
    {
        isSealed = isSealed
        isBeforefieldinit = isBeforefieldinit
        name = Id.L n
        body = decls
    }
    =
    oc += ".class "
    if nested then oc += "nested private "
    if isSealed then oc += "sealed "
    if isBeforefieldinit then oc += "beforefieldinit "
    name oc n
    newline oc i; oc += "{"
    for decl in decls do (newline oc (i + 1); classDecl (i + 1) oc decl)
    newline oc i; oc += "}"

let makeEntryPoint { name = n; resultType = resultType } =
    let body = {
        isEntrypoint = true
        locals = []
        opcodes =
        [
            Call(false, {
                call_conv = Static
                resultType = resultType
                declaringType = Virtual.topLevelType
                methodName = n
                argTypes = []
            })
            Pop
            Ret
        ]
    }
    {
        access = Public
        isSpecialname = false
        isRtspecialname = false
        callconv = Static
        resultType = None
        name = MethodName <| Id.L "Main"
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
    methodDef 1 oc e

    newline oc 1
    methodDef 1 oc <| makeEntryPoint e

    newline oc 0
    fprintfn oc "}"
