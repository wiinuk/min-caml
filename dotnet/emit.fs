module Emit
open Asm
open System

let (+=) o s = output_string o s

let newline oc i =
    oc += "\r\n"
    for _ in 1..i do oc += "    "

let groupCore emptyIfIgnore first emit sep last o xs =
    if Seq.isEmpty xs then
        if emptyIfIgnore then () else
        o += first
        o += last
    else
        let x = Seq.head xs
        let xs = Seq.tail xs
        o += first
        emit o x
        for x in xs do
            o += sep
            emit o x
        o += last

let groupOrEmpty first emit sep last o xs = groupCore true first emit sep last o xs
let group first emit sep last o xs = groupCore false first emit sep last o xs

let hexByte w x = fprintf w "%02x" x
/// (00 01 ...)
let wrapBytes w xs = group "(" hexByte " " ")" w xs

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
    | Char -> oc += "char"
    | Int32 -> oc += "int32"
    | Float64 -> oc += "float64"
    | String -> oc += "string"
    | Object -> oc += "object"
    | NativeInt -> oc += "native int"
    | Array t -> type' oc t; oc += "[]"
    | MethodTypeArgument x -> oc += "!!"; name oc x
    | TypeArgmentIndex x -> fprintf oc "!%d" x
    | MethodArgmentIndex x -> fprintf oc "!!%d" x
    | TypeRef(kind, moduleName, nameSpace, nestedParents, typeName, typeArgs) ->
        oc += match kind with type_kind.Class -> "class " | ValueType -> "valuetype "
        groupOrEmpty "[" name "." "]" oc moduleName
        for x in nameSpace do (name oc x; oc += ".")
        for x in nestedParents do (name oc x; oc += "/")
        name oc typeName
        groupOrEmpty "<" type' ", " ">" oc typeArgs

let resultType oc = function
    | None -> oc += "void"
    | Some t -> type' oc t

let arg oc (x, t) = type' oc t; oc += " "; name oc x
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

let methodRef oc { callconv = c; resultType = r; declaringType = t; methodName = n; typeArgs = typeArgs; argTypes = ts } =
    oc += match c with Instance -> "instance " | Static -> ""
    resultType oc r
    oc += " "
    type' oc t
    oc += "::"
    methodName oc n
    if not <| List.isEmpty typeArgs then group "<" type' ", " ">" oc typeArgs
    group "(" type' ", " ")" oc ts

let fieldRef oc { fieldType = ft; declaringType = t; name = Id.L n } =
    type' oc ft
    oc += " "
    type' oc t
    oc += "::"
    name oc n

let ldcI4 oc = function
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

let ldcR8 oc x =
    oc += "ldc.r8 "

    if Double.IsNaN x || Double.IsInfinity x then

        // TODO: エンディアンを考慮する必要がある?
        wrapBytes oc <| BitConverter.GetBytes x

    else
        // ラウンドトリップ
        fprintf oc "%.17g" x

let rec arrayAccess (u1, u2, i4, r8, i, ref, any) oc = function
    | Bool -> oc += u1
    | Char -> oc += u2
    | Int32 -> oc += i4
    | Float64 -> oc += r8
    | NativeInt -> oc += i
    | Array _
    | String
    | Object
    | TypeRef(kind = type_kind.Class) -> oc += ref

    | This
    | TypeArgmentIndex _
    | MethodArgmentIndex _
    | MethodTypeArgument _
    | TypeRef _ as t -> oc += any; oc += " "; type' oc t

let ldelems = "ldelem.u1", "ldelem.u2", "ldelem.i4", "ldelem.r8", "ldelem.i", "ldelem.ref", "ldelem"
let stelems = "stelem.i1", "stelem.i2", "stelem.i4", "stelem.r8", "stelem.i", "stelem.ref", "stelem"
let ldelem oc t = arrayAccess ldelems oc t
let stelem oc t = arrayAccess stelems oc t

/// 命令のアセンブリ生成 (caml2html: emit_gprime)
let opcode oc = function
    | Label(Id.L l) -> name oc l; oc += ":"

    | Nop -> oc += "nop"
    | Dup -> oc += "dup"
    | Pop -> oc += "pop"
    | Add -> oc += "add"
    | Neg -> oc += "neg"
    | Sub -> oc += "sub"
    | Mul -> oc += "mul"
    | Div -> oc += "div"
    
    | ConvU2 -> oc += "conv.u2"
    | ConvI4 -> oc += "conv.i4"
    | ConvR8 -> oc += "conv.r8"
    | ConvOvfU1 -> oc += "conv.ovf.u1"

    | Ldarg0 -> oc += "ldarg.0"
    | Ldnull -> oc += "ldnull"
    | LdcI4 x -> ldcI4 oc x
    | LdcR8 x -> ldcR8 oc x

    | Br(Id.L l) -> oc += "br "; name oc l
    | BneUn(Id.L l) -> oc += "bne.un "; name oc l
    | Bgt(Id.L l) -> oc += "bgt "; name oc l
    | Blt(Id.L l) -> oc += "blt "; name oc l
    | Brtrue(Id.L l) -> oc += "brtrue "; name oc l
    
    | Ldarg l -> oc += "ldarg "; name oc l
    | Ldloc l -> oc += "ldloc "; name oc l
    | Stloc l -> oc += "stloc "; name oc l

    | Call(tail, m) ->
        oc += if tail then "tail. call " else "call "
        methodRef oc m

    | Ret -> oc += "ret"

    | Newarr t -> oc += "newarr "; type' oc t
    | Ldelem t -> ldelem oc t
    | Stelem t -> stelem oc t

    | Newobj(declaringType, argTypes) ->
        fprintf oc "newobj instance void "
        type' oc declaringType
        oc += "::.ctor"
        group "(" type' ", " ")" oc argTypes

    | Ldfld f -> oc += "ldfld "; fieldRef oc f
    | Stfld f -> oc += "stfld "; fieldRef oc f
    | Ldsfld f -> oc += "ldsfld "; fieldRef oc f
    | Stsfld f -> oc += "stsfld "; fieldRef oc f
    | Callvirt(tail, m) ->
        oc += if tail then "tail. callvirt " else "callvirt "
        methodRef oc m

    | Ldftn m -> oc += "ldftn "; methodRef oc m

let opcodes i oc ops =
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
    | Private -> "private "
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
let methodBody i oc { maxStack = maxStack; isEntrypoint = isEntrypoint; locals = locals; opcodes = ops } =
    match maxStack with
    | None -> ()
    | Some maxStack ->
        newline oc i
        fprintf oc ".maxstack %d" maxStack

    if isEntrypoint then
        newline oc i
        oc += ".entrypoint"

    if not <| List.isEmpty locals then
        newline oc i
        oc += ".locals init "
        args i oc locals

    opcodes i oc ops

let methodDef i oc
    {
        access = access
        isSpecialname = isSpecialname
        isRtspecialname = isRtspecialname
        callconv = callconv
        resultType = r
        name = n
        typeArgs = typeArgs
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
    methodName oc n
    groupOrEmpty "<" name ", " ">" oc typeArgs
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

let fieldDef oc { access = a; callconv = cc; fieldType = t; name = Id.L n } =
    oc += ".field "
    oc += accessNonNested a
    oc += match cc with Static -> "static " | Instance -> ""
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
        decls = decls
    }
    =
    oc += ".class "
    if nested then oc += "nested private "
    if isSealed then oc += "sealed "
    if isBeforefieldinit then oc += "beforefieldinit "
    name oc n
    newline oc i; oc += "{"
    for decl in decls do
        newline oc (i + 1)
        classDecl (i + 1) oc decl
    newline oc i; oc += "}"

let assemblyDef oc { assemblyName = assemblyName; moduleName = moduleName } =
    group ".assembly " name "." " {}" oc assemblyName; newline oc 0

    match moduleName with
    | [] -> ()
    | _ -> group ".module " name "." "" oc moduleName; newline oc 0

let assemblyRef oc = function
    | { name = n; publickeytoken = []; ver = None } ->
        oc += ".assembly extern "; name oc n; oc += " {}"

    | { name = n; publickeytoken = key; ver = ver } ->
        oc += ".assembly extern "; name oc n; newline oc 0
        oc += "{"; newline oc 0
        if not <| List.isEmpty key then
            oc += "    .publickeytoken = "; wrapBytes oc key; newline oc 0
        match ver with
        | None -> ()
        | Some(v1,v2,v3,v4) ->
            fprintf oc "    .ver %d:%d:%d:%d" v1 v2 v3 v4; newline oc 0

        oc += "}"

let decl oc = function
    | AssemblyRef x -> assemblyRef oc x
    | Class x -> classDef false 0 oc x

let f oc (Prog(def, decls)) =
    eprintf "generating assembly...@."
    
    assemblyDef oc def

    for d in decls do
        decl oc d
        newline oc 0
