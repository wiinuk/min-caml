module MinCaml.Compiler.Cli.AsmType
open MinCaml.Compiler.Ast

type dotted_name = Id.t list
type type_kind = Class | ValueType
type asm_type =

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
    | Array of asm_type

    /// e.g. class [moduleA.dll]NamespaceA.ClassA/ClassB/Class
    | TypeRef of
        kind: type_kind *
        moduleName: dotted_name *
        nameSpace: Id.t list *
        nestedParents: Id.t list *
        typeName: Id.t *
        typeArgs: asm_type list

let tryTake n xs =
    let rec aux n acc = function
        | xs when n <= 0 -> Some(List.rev acc, xs)
        | [] -> None
        | x::xs -> aux (n - 1) (x::acc) xs
    aux n [] xs

let unit = TypeRef(Class, ["mscorlib"], ["System"], [], "DBNull", [])

let rec tuple types =
    let types =
        match tryTake 7 types with
        | None | Some(_, []) -> types
        | Some(types, tail) -> types @ [tuple tail]

    let arity = List.length types
    TypeRef(Class, ["mscorlib"], ["System"], [], "Tuple`" + string arity, types)

let func (argTypes, resultType) =
    let name, args =
        match resultType with
        | None -> sprintf "Action`%d" (List.length argTypes), argTypes
        | Some r -> sprintf "Func`%d" (List.length argTypes + 1), argTypes @ [r]

    TypeRef(Class, ["mscorlib"], ["System"], [], name, args)

let rec asmType = function
    | Type.Array t -> Array <| asmType t
    | Type.Unit -> unit
    | Type.Bool -> Bool
    | Type.Int -> Int32
    | Type.Float -> Float64

    // Unit ˆø”‚Í–³Ž‹
    // Unit –ß‚è’l‚ÌŠÖ”‚Í–ß‚è’l void
    | Type.Fun(argTypes, resultType) -> func <| funcElements (argTypes, resultType)

    | Type.Tuple ts -> tuple <| List.map asmType ts
    | Type.Var { contents = Some t } -> asmType t
    | Type.Var { contents = None } -> failwith "unexpected type 'Var'"

and asmTypeOrVoid = function
    | Type.Unit -> None
    | t -> Some <| asmType t

and funcElements (argTypes, resultType) =
    List.choose asmTypeOrVoid argTypes, asmTypeOrVoid resultType
    
open System.Collections.Generic
let hash kvs = dict kvs |> Dictionary :> IReadOnlyDictionary<_,_>

let knownTypes =
    hash [
        typeof<bool>, Bool
        typeof<char>, Char
        typeof<double>, Float64
        typeof<int>, Int32
        typeof<nativeint>, NativeInt
        typeof<obj>, Object
        typeof<string>, String
    ]

let rec asmTypeOf t =
    let mutable r = Unchecked.defaultof<_>

    if t = typeof<System.Void> then failwith "void is not first class type"
    if knownTypes.TryGetValue(t, &r) then r
    elif t.IsArray && t.GetArrayRank() = 1 then t.GetElementType() |> asmTypeOf |> Array
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
    let typeArgs = if t.IsGenericType then t.GetGenericArguments() |> Seq.map asmTypeOf |> Seq.toList else []
    TypeRef(kind, moduleName, nameSpace, nestedParents, t.Name, typeArgs)

[<RequiresExplicitTypeArguments>]
let asmtypeof<'a> = asmTypeOf typeof<'a>
