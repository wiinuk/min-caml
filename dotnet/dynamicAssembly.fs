module DynamicAssembly
open Asm
open System
open System.Reflection
open System.Reflection.Emit
open System.Collections.Generic
open System.Runtime.CompilerServices

type T = Reflection.TypeAttributes
type M = Reflection.MethodAttributes
type F = Reflection.FieldAttributes
type B = Reflection.BindingFlags
type O = Emit.OpCodes

type members = {
    /// generic method definitions
    methods: Dictionary<string * cli_type list, MethodBuilder>
    ctors: Dictionary<cli_type list, ConstructorBuilder>
    fields: Dictionary<string, FieldBuilder>
    /// generic type definitions
    nestedTypes: Dictionary<string, TypeBuilder>
}

type cli_method_base =
    | ConstructorInfo of ConstructorInfo
    | MethodInfo of MethodInfo

type env = {
    modules: ModuleBuilder list
    thisType: Type option
    methodTypeArgs: (string * Type) list

    entryPoint: MethodBuilder option ref

    typeMembers: Dictionary<TypeBuilder, members>
}
type method_env = {
    env: env
    args: Map<string, uint16>
    locals: Map<string, LocalBuilder>
    labels: Map<string, Label>
}

let membersCore (typeMembers: Dictionary<_,_>) t =
    let mutable r = Unchecked.defaultof<_>
    if typeMembers.TryGetValue(t, &r) then r else
    
    let ms = {
        ctors = Dictionary()
        methods = Dictionary()
        nestedTypes = Dictionary()
        fields = Dictionary()
    }
    typeMembers.Add(t, ms)
    ms
let members { typeMembers = xs } t = membersCore xs t

let private getThis { thisType = this } =
    match this with
    | None -> failwith "require 'this' type"
    | Some t -> t

let resolveDynamicTypeOfModules { modules = modules } name =
    modules
    |> List.tryPick (fun m -> m.GetType name |> Option.ofObj)
    |> function
    | Some(:? TypeBuilder as t) -> t
    | _ -> failwithf "type builder not found: %s" name
    
/// Class<!T>.Method<!!U>(!T, !!U) を Class<!T>.Method<!!U>(!0, !!0) に置き換える
let rec normalizeTypeArgumentsCore methodTypeParams = function
    | Bool
    | Char
    | Int32
    | Float64
    | String
    | Object
    | NativeInt 

    | This
    | TypeArgmentIndex _
    | MethodArgmentIndex _ as t -> t

    | MethodTypeArgument n ->
        try
            methodTypeParams
            |> Seq.findIndex ((=) n)
            |> MethodArgmentIndex
        with
        | :? KeyNotFoundException ->
            failwithf "generic type argments: %A is not found in %A" n methodTypeParams

    | Array t -> normalizeTypeArgumentsCore methodTypeParams t |> cli_type.Array
    | TypeRef(kind, moduleName, nameSpace, nestedParents, typeName, typeArgs) ->
        let typeArgs = List.map (normalizeTypeArgumentsCore methodTypeParams) typeArgs
        TypeRef(kind, moduleName, nameSpace, nestedParents, typeName, typeArgs)

let normalizeTypeArguments { methodTypeArgs = typeArgs } t =
    normalizeTypeArgumentsCore (Seq.map fst typeArgs) t

// 現在の ModuleBuilder#DefineType, TypeBuilder#DefineNestedtype では 型の名前に '.', ',', '+' を含めることができない
let escapeTypeName x =
    if String.forall (function '@' | '.' | '+' | ',' -> false | _ -> true) x then x else

    x
    |> String.collect (function
        | '@' -> "@@"
        | '.' -> "@2eU"
        | '+' -> "@2bU"
        | ',' -> "@2cU"
        | x -> string x
    )
    
let addOrThrow (xs: Dictionary<_,_>) k v =
    try xs.Add(k, v) with
    | :? System.ArgumentException when xs.ContainsKey k ->
        failwithf "duplicated entry. old: %A, new: %A" (k, xs.[k]) (k, v)

let addCtor env parent argTypes x =
    let { ctors = ctors } = members env parent
    let argTypes = List.map (normalizeTypeArguments env) argTypes
    addOrThrow ctors argTypes x

let addField env parent name x =
    let { fields = fields } = members env parent
    addOrThrow fields name x

let addMethod env parent (name, argTypes) x =
    let { methods = methods } = members env parent
    let argTypes = List.map (normalizeTypeArguments env) argTypes
    addOrThrow methods (name, argTypes) x

let addNestedType env parent name x =
    let { nestedTypes = nestedTypes } = membersCore env parent
    addOrThrow nestedTypes (escapeTypeName name) x
    
let getOrThrow (xs: Dictionary<_,_>) k =
    let mutable v = Unchecked.defaultof<_>
    if xs.TryGetValue(k, &v) then v else

    let xs = Seq.map (|KeyValue|) xs
    failwithf "entry not found. key: %A, map: %A" k xs

let findCtor env parent argTypes =
    let { ctors = ctors } = members env parent
    let argTypes = List.map (normalizeTypeArguments env) argTypes
    getOrThrow ctors argTypes

let findField env parent name =
    let { fields = fields } = members env parent
    getOrThrow fields name

let findMethod env parent (name, argTypes) =
    let { methods = methods } = members env parent
    let argTypes = List.map (normalizeTypeArguments env) argTypes
    getOrThrow methods (name, argTypes)

let findNestedType env parent name =
    let { nestedTypes = nestedTypes } = members env parent
    getOrThrow nestedTypes <| escapeTypeName name

let rec resolveType env = function
    | Bool -> typeof<bool>
    | Char -> typeof<char>
    | Int32 -> typeof<int>
    | Float64 -> typeof<double>
    | String -> typeof<string>
    | Object -> typeof<obj>

    // TODO: nativeint = System.IntPtr; native int を指定したい
    | NativeInt -> typeof<nativeint>
    | Array t -> (resolveType env t).MakeArrayType()

    | This -> getThis env
    | TypeArgmentIndex i -> getThis(env).GetGenericTypeDefinition().GetGenericArguments().[i]
    | MethodArgmentIndex i -> snd env.methodTypeArgs.[i]
    | MethodTypeArgument n -> List.find (fun (n', _) -> n = n') env.methodTypeArgs |> snd

    | TypeRef(_, moduleName, nameSpace, nestedParents, typeName, typeArgs) as t ->
        let moduleName = String.concat "." moduleName
        let nameSpace = Seq.map (fun n -> n + ".") nameSpace |> String.concat ""
        let nestedParents = Seq.map (fun n -> n + "+") nestedParents |> String.concat ""
        let fullName = nameSpace + nestedParents + escapeTypeName typeName
        let qualifiedName = if moduleName <> "" then fullName + ", " + moduleName else fullName

        let t =
            match Type.GetType qualifiedName with
            | null -> resolveDynamicTypeOfModules env qualifiedName :> Type
            | t -> t

        if List.isEmpty typeArgs then t else

        let typeArgs = [|for t in typeArgs -> resolveType env t|]
        t.MakeGenericType typeArgs

let resolveField env { declaringType = parent; name = Id.L name } =
    let t = resolveType env parent
    let a = B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance ||| B.Static
    match t with
    | :? TypeBuilder as t -> findField env t name :> FieldInfo
    | _ -> t.GetField(name, a)

let raiseMethodNotFound m = failwithf "method not found; name: %A" m


let resolveMethodBase env m =
    let {
        callconv = cc
        resultType = r
        declaringType = parent
        typeArgs = typeArgs
        methodName = name
        argTypes = argTypes
        } = m

    let typeArgs = List.map (resolveType env) typeArgs
    let t = resolveType env parent
    let env = {
        env with
            methodTypeArgs = List.map (fun t -> "", t) typeArgs
            thisType = Some t
    }
    match name with
    | Ctor ->
        let a = B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance
        match t with
        | :? TypeBuilder as t -> ConstructorInfo <| upcast findCtor env t argTypes
        | _ ->

        let argTypes = [|for t in argTypes -> resolveType env t|]
        match t.GetConstructor(a, null, argTypes, null) with
        | null -> raiseMethodNotFound m
        | m -> ConstructorInfo m

    | MethodName(Id.L name) ->
        let a = B.DeclaredOnly ||| B.Public ||| B.NonPublic
        let a = match cc with Instance -> a ||| B.Instance | Static -> a ||| B.Static
        match t with
        | :? TypeBuilder as t ->
            let m = findMethod env t (name, argTypes)
            if not m.IsGenericMethodDefinition then MethodInfo m else

            MethodInfo <| m.MakeGenericMethod(List.toArray typeArgs)

        | _ ->

        let argTypes = [|for t in argTypes -> resolveType env t|]
        match t.GetMethod(name, a, null, argTypes, null) with
        | null when t.IsGenericType ->
            match t.GetGenericTypeDefinition().GetMethod(name, a, null, argTypes, null)  with
            | null -> raiseMethodNotFound m
            | m -> MethodInfo m
        | null -> raiseMethodNotFound m
        | m -> MethodInfo m

module DeclareTypes =
    let defineType defineType a
        {
            isSealed = isSealed
            isBeforefieldinit = isBeforefieldinit
            name = Id.L name
        }
        =
        let a = if isSealed then a ||| T.Sealed else a
        let a = if isBeforefieldinit then a ||| T.BeforeFieldInit else a
        defineType(escapeTypeName name, a)

    let rec classDecl env t = function
        | Method _
        | Custom _
        | Field _ -> ()
        | NestedClass c -> classDef env (Choice2Of2 t) c

    and classDef env parent ({ access = access; decls = decls; name = Id.L name } as c) =
        let t =
            match parent with
            | Choice1Of2(parent: ModuleBuilder) ->
                let a =
                    match access with
                    | Default -> enum 0
                    | Public -> T.Public
                    | Private -> enum 0
                defineType parent.DefineType a c

            | Choice2Of2(parent: TypeBuilder) ->
                let a =
                    match access with
                    | Default -> T.NestedPrivate
                    | Public -> T.NestedPublic
                    | Private -> T.NestedPrivate
                let t = defineType parent.DefineNestedType a c
                addNestedType env parent name t
                t

        for d in decls do classDecl env t d

    let decl env a = function
        | AssemblyRef _ -> ()
        | Class c -> classDef env (Choice1Of2 a) c

module DeclareMembers =
    let defineParameters defineParameter args =
        args
        |> Seq.iteri (fun i (name, _) ->
            defineParameter(i + 1, ParameterAttributes.None, name)
            |> ignore
        )

    let methodDef env (parent: TypeBuilder)
        {
            access = access
            isSpecialname = isSpecialname
            isRtspecialname = isRtspecialname
            callconv = callconv
            resultType = resultType
            name = name
            typeArgs = typeArgs
            args = args
            isForwardref = isForwardref
        }
        =
        let a =
            match access with
            | Public -> M.Public
            | Private -> M.Private
            | Default -> enum 0

        let a = a ||| M.HideBySig
        let a = if isSpecialname then a ||| M.SpecialName else a
        let a = if isRtspecialname then a ||| M.RTSpecialName else a
        let a = match callconv with Instance -> a | Static -> a ||| M.Static
        
        let argTypes = List.map snd args

        match name with
        | Ctor ->
            let parameterTypes = Seq.map (resolveType env) argTypes |> Seq.toArray
            let c = parent.DefineConstructor(a, CallingConventions.Any, parameterTypes)
            if isForwardref then
                c.SetImplementationFlags MethodImplAttributes.ForwardRef

            defineParameters c.DefineParameter args
            addCtor env parent argTypes c

        | MethodName(Id.L name) ->
            let m = parent.DefineMethod(name, a)
            let env =
                if List.isEmpty typeArgs then env else

                let typeParams = m.DefineGenericParameters(List.toArray typeArgs)
                let thisArgs =
                    Seq.map2 (fun t1 t2 -> t1, t2 :> Type) typeArgs typeParams
                    |> Seq.toList

                { env with methodTypeArgs = thisArgs }

            let parameterTypes = Seq.map (snd >> resolveType env) args |> Seq.toArray      
            m.SetParameters parameterTypes

            let returnType =
                match resultType with
                | None -> typeof<Void>
                | Some t -> resolveType env t
            m.SetReturnType returnType

            if isForwardref then
                m.SetImplementationFlags(MethodImplAttributes.ForwardRef)

            defineParameters m.DefineParameter args
            addMethod env parent (name, argTypes) m

    let fieldDef env (parent: TypeBuilder) { access = a; callconv = cc; fieldType = t; name = Id.L name } =
        let a =
            match a with
            | Public -> F.Public
            | Private -> F.Private
            | Default -> enum 0

        let a =
            match cc with
            | Instance -> a
            | Static -> a ||| F.Static

        let f = parent.DefineField(name, resolveType env t, a)
        addField env parent name f

    let rec classDecl env t = function
        | Custom _ -> ()
        | Method x -> methodDef env t x
        | Field x -> fieldDef env t x
        | NestedClass x -> classDef env (Choice2Of2 t) x

    and classDef env parent { name = Id.L name; decls = decls } =
        let t =
            match parent with
            | Choice1Of2 _ -> resolveDynamicTypeOfModules env name
            | Choice2Of2 t -> findNestedType env t name

        let env = { env with thisType = Some(upcast t) }
        for decl in decls do classDecl env t decl

    let decl env a = function
        | AssemblyRef _ -> ()
        | Class c -> classDef env (Choice1Of2 a) c

module EmitMethods =
    let custom env (t: TypeBuilder) = function
        | { ctor = ctor; args = []; namedArgs = [] } ->
            let ctor =
                match resolveMethodBase env ctor with 
                | MethodInfo m -> failwithf "require constructor; actial: %A" m
                | ConstructorInfo m -> m

            t.SetCustomAttribute(ctor, [||])

        // TODO:
        | _ -> failwith "not implemented"

    let (+=) (g: ILGenerator) op = g.Emit op

    let ldcI4 g = function
        | -1 -> g += O.Ldc_I4_M1
        | 0 -> g += O.Ldc_I4_0
        | 1 -> g += O.Ldc_I4_1
        | 2 -> g += O.Ldc_I4_2
        | 3 -> g += O.Ldc_I4_3
        | 4 -> g += O.Ldc_I4_4
        | 5 -> g += O.Ldc_I4_5
        | 6 -> g += O.Ldc_I4_6
        | 7 -> g += O.Ldc_I4_7
        | 8 -> g += O.Ldc_I4_8
        | x when int SByte.MinValue <= x && x <= int SByte.MaxValue -> g.Emit(O.Ldc_I4_S, uint8 (int8 x))
        | x -> g.Emit(O.Ldc_I4, x)

    let ldarg g = function
        | 0us -> g += O.Ldarg_0
        | 1us -> g += O.Ldarg_1
        | 2us -> g += O.Ldarg_2
        | 3us -> g += O.Ldarg_3
        | x when x <= uint16 Byte.MaxValue -> g.Emit(O.Ldarg_S, uint8 x)
        | x -> g.Emit(O.Ldarg, int16 x)

    let rec arrayAccess (u1, u2, i4, r8, i, ref, any) env g = function
        | Bool -> g += u1
        | Char -> g += u2
        | Int32 -> g += i4
        | Float64 -> g += r8
        | NativeInt -> g += i
        | Array _
        | String
        | Object
        | TypeRef(kind = type_kind.Class) -> g += ref

        | This
        | TypeArgmentIndex _
        | MethodArgmentIndex _
        | MethodTypeArgument _
        | TypeRef _ as t -> g.Emit(any, resolveType env t)

    let ldelems = O.Ldelem_U1, O.Ldelem_U2, O.Ldelem_I4, O.Ldelem_R8, O.Ldelem_I, O.Ldelem_Ref, O.Ldelem
    let stelems = O.Stelem_I1, O.Stelem_I2, O.Stelem_I4, O.Stelem_R8, O.Stelem_I, O.Stelem_Ref, O.Stelem
    let ldelem env t = arrayAccess ldelems env t
    let stelem env t = arrayAccess stelems env t

    let opcode { env = env; args = args; locals = locals; labels = labels } g = function
        | Nop -> g += O.Nop
        | Dup -> g += O.Dup
        | Pop -> g += O.Pop
        | Add -> g += O.Add
        | Neg -> g += O.Neg
        | Sub -> g += O.Sub
        | Mul -> g += O.Mul
        | Div -> g += O.Div
        | ConvU2 -> g += O.Conv_U2
        | ConvI4 -> g += O.Conv_I4
        | ConvR8 -> g += O.Conv_R8
        | ConvOvfU1 -> g += O.Conv_Ovf_U1
        | Ldarg0 -> g += O.Ldarg_0
        | Ldnull -> g += O.Ldnull
        | LdcI4 x -> ldcI4 g x
        | LdcR8 x -> g.Emit(O.Ldc_R8, x)

        | Label(Id.L l) -> g.MarkLabel <| Map.find l labels

        | Br(Id.L l) -> g.Emit(O.Br, Map.find l labels)
        | BneUn(Id.L l) -> g.Emit(O.Bne_Un, Map.find l labels)
        | Bgt(Id.L l) -> g.Emit(O.Bgt, Map.find l labels)
        | Blt(Id.L l) -> g.Emit(O.Blt, Map.find l labels)
        | Brtrue(Id.L l) -> g.Emit(O.Brtrue, Map.find l labels)

        | Ldarg l -> Map.find l args |> ldarg g
        | Ldloc l -> g.Emit(O.Ldloc, Map.find l locals)
        | Stloc l -> g.Emit(O.Stloc, Map.find l locals)

        | Call(tail, m) ->
            if tail then g += O.Tailcall
            match resolveMethodBase env m with
            | MethodInfo x -> g.EmitCall(O.Call, x, null)
            | ConstructorInfo x -> g.Emit(O.Call, x)

        | Ret -> g += O.Ret

        | Newarr t -> g.Emit(O.Newarr, resolveType env t)
        | Ldelem t -> ldelem env g t
        | Stelem t -> stelem env g t
        | Newobj(declaringType, argTypes) ->
            let m = ctorRef(declaringType, argTypes)
            match resolveMethodBase env m with
            | MethodInfo x -> g.Emit(O.Newobj, x)
            | ConstructorInfo x -> g.Emit(O.Newobj, x)

        | Ldfld f -> g.Emit(O.Ldfld, resolveField env f)
        | Stfld f -> g.Emit(O.Stfld, resolveField env f)
        | Ldsfld f -> g.Emit(O.Ldsfld, resolveField env f)
        | Stsfld f -> g.Emit(O.Stsfld, resolveField env f)
        | Callvirt(tail, m) ->
            if tail then g += O.Tailcall
            match resolveMethodBase env m with
            | MethodInfo x -> g.EmitCall(O.Callvirt, x, null)
            | ConstructorInfo x -> g.Emit(O.Callvirt, x)

        | Ldftn m ->
            match resolveMethodBase env m with
            | ConstructorInfo x -> g.Emit(O.Ldftn, x)
            | MethodInfo x -> g.Emit(O.Ldftn, x)

    let methodBody env (g: ILGenerator)
        {
            callconv = cc
            args = args
            body = { locals = locals; opcodes = ops }
        }
        =
        // maxStack は反映されない。ILGenerator が自動計算

        let offset = match cc with Static -> 0 | Instance -> 1
        let args = Seq.mapi (fun i (n, _) -> n, uint16(i + offset)) args |> Map.ofSeq
        let locals = Map.map (fun _ t -> resolveType env t |> g.DeclareLocal) locals
        let labels = Seq.choose (function Label(Id.L l) -> Some(l, g.DefineLabel()) | _ -> None) ops |> Map.ofSeq
        let env = {
            env = env
            args = args
            locals = locals
            labels = labels
        }
        for op in ops do opcode env g op

    let methodDef env parent ({ name = name; typeArgs = typeArgs; args = args; body = body } as method') =
        let argTypes = List.map snd args
        match name with
        | Ctor ->
            let c = findCtor env parent argTypes
            methodBody env (c.GetILGenerator()) method'

        | MethodName(Id.L name) ->
            let m =
                let { methods = methods } = members env parent
                let argTypes = List.map (normalizeTypeArgumentsCore typeArgs) argTypes
                getOrThrow methods (name, argTypes)

            let env =
                if not m.IsGenericMethod then env else

                let typeArgs =
                    m.GetGenericArguments()
                    |> Seq.map (fun t -> t.Name, t)
                    |> Seq.toList

                { env with methodTypeArgs = typeArgs }

            if body.isEntrypoint then
                if Option.isSome !env.entryPoint then
                    failwithf "duplicated entrypoint: %A %A" env.entryPoint m

                env.entryPoint := Some m
                
            let g = m.GetILGenerator()
            methodBody env g method'

    let rec classDecl env t = function
        | Custom x -> custom env t x
        | Method m -> methodDef env t m
        | Field _ -> ()
        | NestedClass c -> classDef env (Choice2Of2 t) c

    and classDef env parent { name = Id.L name; decls = decls } =
        let t =
            match parent with
            | Choice1Of2 _ -> resolveDynamicTypeOfModules env name
            | Choice2Of2 parent -> findNestedType env parent name

        let env = { env with thisType = Some(upcast t) }
        for decl in decls do classDecl env t decl

    let decl env a = function
        | AssemblyRef _ -> ()
        | Class c -> classDef env (Choice1Of2 a) c

let mergeLibMinCaml (Prog(def, decls)) =
    let decls =
        decls
        |> List.map (function
            | Class({ name = Id.L name; decls = decls } as def)
                when name = Virtual.topLevelTypeName ->
                Class { def with decls = List.map Method LibmincamlVirtual.decls @ decls }
            | x -> x
        )
    Prog(def, decls)

type dynamic_assembly_settings = {
    domain: AppDomain
    access: AssemblyBuilderAccess
    directory: string option
    fileName: string option
}

let defineMinCamlAssembly s p =
    let { domain = domain; access = access; directory = directory; fileName = fileName } = s
    let (Prog({ assemblyName = assemblyName; moduleName = moduleName }, decls)) = mergeLibMinCaml p

    let assemblyName = String.concat "." assemblyName
    let moduleName =
        match moduleName with
        | [] -> assemblyName + ".exe"
        | _ -> String.concat "." moduleName

    let a = domain.DefineDynamicAssembly(AssemblyName assemblyName, access, Option.toObj directory)
    let m =
        match fileName with
        | None -> a.DefineDynamicModule moduleName
        | Some fileName -> a.DefineDynamicModule(moduleName, fileName)

    let env = Dictionary()

    // 1. 型の宣言
    for d in decls do DeclareTypes.decl env m d

    let env = {
        entryPoint = ref None
        modules = [m]
        thisType = None
        methodTypeArgs = []
        typeMembers = env
    }

    // 2. ジェネリック制約と継承関係とメンバの宣言
    for d in decls do DeclareMembers.decl env m d

    // 3. カスタム属性とメソッド本体の生成
    for d in decls do EmitMethods.decl env m d
    
    // 4. 型の作成
    for m in env.modules do
        for t in m.GetTypes() do
            match t with
            | :? TypeBuilder as t -> t.CreateType() |> ignore
            | _ -> ()
    
    // 5. エントリーポイントの設定
    match !env.entryPoint with
    | Some m -> a.SetEntryPoint m
    | _ -> ()

    a
