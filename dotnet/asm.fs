[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "TypeNamesMustBePascalCase")>]
[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "IdentifiersMustNotContainUnderscores")>]
module Asm

type dotted_name = Id.t list
type type_kind = Class | ValueType
type cli_type =

    /// .this
    | This
    /// e.g. !0
    | TypeArgmentIndex of int
    /// e.g. !!0
    | MethodArgmentIndex of int
    /// e.g. !!T
    | MethodTypeArgument of Id.t

    /// sizeof<bool> = 1
    | Bool
    | Char
    | Int32
    | Float64
    | String
    | Object
    /// native int
    | NativeInt
    | Array of cli_type

    /// e.g. class [moduleA.dll]NamespaceA.ClassA/ClassB/Class
    | TypeRef of
        kind: type_kind *
        moduleName: dotted_name *
        nameSpace: Id.t list *
        nestedParents: Id.t list *
        typeName: Id.t *
        typeArgs: cli_type list

let tryTake n xs =
    let rec aux n acc = function
        | xs when n <= 0 -> Some(List.rev acc, xs)
        | [] -> None
        | x::xs -> aux (n - 1) (x::acc) xs
    aux n [] xs

let rec tupleType types =
    let types =
        match tryTake 7 types with
        | None | Some(_, []) -> types
        | Some(types, tail) -> types @ [tupleType tail]

    let arity = List.length types
    TypeRef(Class, ["mscorlib"], ["System"], [], "Tuple`" + string arity, types)

let unitType = TypeRef(Class, ["mscorlib"], ["System"], [], "DBNull", [])

let funType argTypes resultType =
    let name, args =
        match resultType with
        | None -> sprintf "Action`%d" (List.length argTypes), argTypes
        | Some r -> sprintf "Func`%d" (List.length argTypes + 1), argTypes @ [r]
    
    TypeRef(Class, ["mscorlib"], ["System"], [], name, args)

let rec cliType = function
    | Type.Array t -> Array <| cliType t
    | Type.Unit -> unitType
    | Type.Bool -> Bool
    | Type.Int -> Int32
    | Type.Float -> Float64
    | Type.Fun(argTypes, resultType) -> funType (List.map cliType argTypes) <| Some (cliType resultType)
    | Type.Tuple ts -> tupleType <| List.map cliType ts
    | Type.Var { contents = Some t } -> cliType t
    | Type.Var { contents = None } -> failwith "unexpected type 'Var'"


type call_conv = Instance | Static
type method_name =
    | MethodName of Id.l
    | Ctor

type method_ref = {
    callconv: call_conv
    resultType: cli_type option
    declaringType: cli_type
    typeArgs: cli_type list
    methodName: method_name
    argTypes: cli_type list
}

type field_ref = {
    fieldType: cli_type
    declaringType: cli_type
    name: Id.l
}

type t = exp list
and exp =
    | Label of Id.l

    | Ldarg0
    | Ldarg of Id.t
    | Ldloc of Id.t
    | Stloc of Id.t
    | Dup
    | Pop
    | Nop

    | Ldnull
    | LdcI4 of int32
    | LdcR8 of float

    | Neg
    | Add
    | Sub
    | Mul
    | Div

    | ConvU2
    | ConvI4
    | ConvR8
    | ConvOvfU1

    | Br of Id.l
    | BneUn of Id.l
    | Bgt of Id.l
    | Blt of Id.l
    | Brtrue of Id.l

    | Call of isTail: bool * method_ref
    | Ret

    | Newarr of cli_type
    | Ldelem of cli_type
    | Stelem of cli_type

    /// newobj instance void $declaringType::.ctor($argTypes)
    | Newobj of declaringType: cli_type * argTypes: cli_type list
    | Ldfld of field_ref
    | Stfld of field_ref
    | Ldsfld of field_ref
    | Stsfld of field_ref

    /// callvirt instance $resultType $declaringType::$methodName($argTypes)
    | Callvirt of isTail: bool * method_ref
    | Ldftn of method_ref

type accesibility =
    | Public
    | Private
    // class = Private; nested class = NestedPrivate
    | Default

type method_body = {
    maxStack: int option
    isEntrypoint: bool

    /// .locals init (...)
    locals: (Id.t * cli_type) list
    opcodes: t
}

type method_def = {
    access: accesibility
    isSpecialname: bool
    isRtspecialname: bool
    callconv: call_conv
    /// None = void
    resultType: cli_type option
    name: method_name
    typeArgs: Id.t list
    args: (Id.t * cli_type) list
    isForwardref: bool
    body: method_body
}

type custom = {
    ctor: method_ref
    args: unit list
    namedArgs: unit list
}
type field_def = {
    access: accesibility
    callconv: call_conv
    fieldType: cli_type
    name: Id.l
}
type class_decl =
    | Custom of custom
    | Method of method_def
    | Field of field_def
    | NestedClass of class_def

and class_def = {
    access: accesibility
    isAbstract: bool
    isSealed: bool
    isBeforefieldinit: bool
    name: Id.l
    decls: class_decl list
}

type assembly_ref = {
    name: Id.t
    publickeytoken: byte list
    ver: (int * int * int * int) option
}

type assembly_def = {
    assemblyName: dotted_name
    moduleName: dotted_name
}

type decl =
    | AssemblyRef of assembly_ref
    | Class of class_def

type prog = Prog of assembly_def * decl list

let methodRef(callconv, resultType, declaringType, methodName, typeArgs, argTypes) = {
    callconv = callconv
    resultType = resultType
    declaringType = declaringType
    typeArgs = typeArgs
    methodName = MethodName <| Id.L methodName
    argTypes = argTypes
}
let ctorRef(declaringType, argTypes) = {
    callconv = Instance
    resultType = None
    declaringType = declaringType
    typeArgs = []
    methodName = Ctor
    argTypes = argTypes
}

let call(callconv, resultType, declaringType, name, typeArgs, argTypes) =
    Call(false, methodRef(callconv, resultType, declaringType, name, typeArgs, argTypes))

let getProp(callconv, propertyType, declaringType, propertyName) =
    call(callconv, Some propertyType, declaringType, "get_" + propertyName, [], [])

let callvirt(resultType, declaringType, name, argTypes) =
    Callvirt(false, methodRef(Instance, resultType, declaringType, name, [], argTypes))

let ctorDef (access, args) (maxStack, locals) opcodes = {
    access = access
    isSpecialname = true
    isRtspecialname = true
    callconv = Instance
    resultType = None
    name = Ctor
    typeArgs = []
    args = args
    isForwardref = false
    body =
    {
        isEntrypoint = false
        maxStack = maxStack
        locals = locals
        opcodes = opcodes
    }
}

let methodDef (access, callconv, resultType, name, typeArgs, args) (maxStack, locals) opcodes = {
    access = access
    isSpecialname = false
    isRtspecialname = false
    callconv = callconv
    resultType = resultType
    name = MethodName name
    typeArgs = typeArgs
    args = args
    isForwardref = false
    body = 
    {
        isEntrypoint = false
        maxStack = maxStack
        locals = locals
        opcodes = opcodes
    }
}

// type entry_point_arg_type = String Array option
// type entry_point_result_type = Void | Int32 | UInt32
let entryPointDef (access, name, argsName) (maxStack, locals) opcodes = {
    access = access
    isSpecialname = false
    isRtspecialname = false
    callconv = Static
    resultType = None
    name = MethodName name
    typeArgs = []
    args = match argsName with None -> [] | Some n -> [n, Array String]
    isForwardref = false
    body =
    {
        isEntrypoint = true
        maxStack = maxStack
        locals = locals
        opcodes = opcodes
    }
}


let defaultCtor =
    ctorDef (Public, []) (None, []) [
        Ldarg0
        Call(false, ctorRef(Object, []))
        Ret
    ]

let brinst x = Brtrue x

let fieldDef(access, callconv, fieldType, name) = {
    access = access
    callconv = callconv
    fieldType = fieldType
    name = name
}
let fieldRef(fieldType, declaringType, name) = {
    fieldType = fieldType
    declaringType = declaringType
    name = name
}
let fieldSpec(access, callconv, fieldType, declaringType, name) =
    let ref = fieldRef(fieldType, declaringType, name)
    let def = fieldDef(access, callconv, fieldType, name)
    ref, def

let field(access, callconv, fieldType, name) =
    fieldDef(access, callconv, fieldType, name)
    |> Field

type class_kind = Abstract | Sealed | StaticClass | Inheritable
let classDef (access, kind, name) decls = {
    access = access
    isAbstract = match kind with Abstract | StaticClass -> true | Sealed | Inheritable -> false
    isSealed = match kind with Sealed | StaticClass -> true | Abstract | Inheritable -> false
    isBeforefieldinit = true
    name = Id.L name
    decls = decls
}
