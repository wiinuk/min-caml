[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "TypeNamesMustBePascalCase")>]
[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "IdentifiersMustNotContainUnderscores")>]
module Asm

type type_kind = Class | ValueType
type cli_type =

    /// .this
    | This
    /// e.g. !0
    | TypeArgmentIndex of int
    /// e.g. !!0
    | MethodArgmentIndex of int

    /// sizeof<bool> = 1
    | Bool
    | Int32
    | Float64
    | Object
    /// native int
    | NativeInt
    | Array of cli_type

    /// e.g. class [moduleA]NamespaceA.ClassA/ClassB/Class
    | TypeName of
        type_kind *
        moduleName: Id.t list *
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
    TypeName(Class, ["mscorlib"], ["System"], [], "Tuple`" + string arity, types)

let unitType = TypeName(Class, ["mscorlib"], ["System"], [], "DBNull", [])

let funType argTypes resultType =
    let name = sprintf "Func`%d" <| List.length argTypes + 1
    let args = argTypes @ [resultType]
    TypeName(Class, ["mscorlib"], ["System"], [], name, args)

let rec cliType = function
    | Type.Array t -> Array <| cliType t
    | Type.Unit -> unitType
    | Type.Bool -> Bool
    | Type.Int -> Int32
    | Type.Float -> Float64
    | Type.Fun(argTypes, resultType) -> funType (List.map cliType argTypes) (cliType resultType)
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

    | Ldnull
    | LdcI4 of int32
    | LdcR8 of float

    | Neg
    | Add
    | Sub
    | Mul
    | Div

    | Br of Id.l
    | BneUn of Id.l
    | Bgt of Id.l

    | Call of isTail: bool * method_ref
    | Ret

    | Ldelem of Type.t
    | Stelem of Type.t

    /// newobj instance void $declaringType::.ctor($argTypes)
    | Newobj of declaringType: cli_type * argTypes: cli_type list
    | Ldfld of field_ref
    | Stfld of field_ref
    | Ldsfld of field_ref

    /// callvirt instance $resultType $declaringType::$methodName($argTypes)
    | Callvirt of isTail: bool * method_ref
    | Ldftn of method_ref

type accesibility = Public | Default
type method_body = {
    maxStack: int option
    isEntrypoint: bool

    /// .locals init (...)
    locals: Map<Id.t, Type.t>
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
    args: (Id.t * Type.t) list
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
    fieldType: cli_type
    name: Id.l
}
type class_decl =
    | Custom of custom
    | Method of method_def
    | Field of field_def
    | NestedClass of class_def

/// default accessibility
and class_def = {
    isSealed: bool
    isBeforefieldinit: bool
    name: Id.l
    decls: class_decl list
}

type prog = Prog of class_decl list * entrypoint: method_def

let methodRef(callconv, resultType, declaringType, methodName, typeArgs, argTypes) = {
    callconv = callconv
    resultType = resultType
    declaringType = declaringType
    typeArgs = typeArgs
    methodName = MethodName methodName
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

let call(tail, callconv, resultType, declaringType, name, typeArgs, argTypes) =
    Call(tail, methodRef(callconv, resultType, declaringType, name, typeArgs, argTypes))

let getProp(callconv, propertyType, declaringType, propertyName) =
    call(false, callconv, Some propertyType, declaringType, Id.L("get_" + propertyName), [], [])

let ldftn(resultType, declaringType, name, argTypes) =
    Ldftn <| methodRef(Instance, resultType, declaringType, Id.L name, [], argTypes)

let callvirt(tail, resultType, declaringType, name, argTypes) =
    Callvirt(tail, methodRef(Instance, resultType, declaringType, Id.L name, [], argTypes))

let ctorDef(access, args, isForwardref, body) = {
    access = access
    isSpecialname = true
    isRtspecialname = true
    callconv = Instance
    resultType = None
    name = Ctor
    args = args
    isForwardref = isForwardref
    body = body
}

let defaultCtor =
    let body = {
        maxStack = None
        isEntrypoint = false
        locals = Map.empty
        opcodes =
        [
            Ldarg0
            Call(false, ctorRef(Object, []))
            Ret
        ]
    }
    ctorDef(Public, [], false, body)
