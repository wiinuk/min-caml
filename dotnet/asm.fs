[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "TypeNamesMustBePascalCase")>]
[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "IdentifiersMustNotContainUnderscores")>]
module MinCaml.Compiler.Cli.Asm
open MinCaml.Compiler.Ast
open AsmType

type call_conv = Instance | Static
type method_name =
    | MethodName of Id.l
    | Ctor

type method_ref = {
    callconv: call_conv
    resultType: asm_type option
    declaringType: asm_type
    typeArgs: asm_type list
    methodName: method_name
    argTypes: asm_type list
}

type field_ref = {
    fieldType: asm_type
    declaringType: asm_type
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

    | Newarr of asm_type
    | Ldelem of asm_type
    | Stelem of asm_type

    /// newobj instance void $declaringType::.ctor($argTypes)
    | Newobj of declaringType: asm_type * argTypes: asm_type list
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
    locals: (Id.t * asm_type) list
    opcodes: t
}

type method_def = {
    access: accesibility
    isSpecialname: bool
    isRtspecialname: bool
    callconv: call_conv
    /// None = void
    resultType: asm_type option
    name: method_name
    typeArgs: Id.t list
    args: (Id.t * asm_type) list
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
    fieldType: asm_type
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
