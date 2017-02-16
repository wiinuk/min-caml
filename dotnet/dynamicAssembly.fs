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
    methods: Dictionary<string * cli_type list, MethodBuilder>
    ctors: Dictionary<cli_type list, ConstructorBuilder>
    fields: Dictionary<string, FieldBuilder>
    nestedTypes: Dictionary<string, TypeBuilder>
}

let typeMembersField = ConditionalWeakTable()
let members x =
    let mutable m = Unchecked.defaultof<_>
    if typeMembersField.TryGetValue(x, &m) then m else

    let m = {
        ctors = Dictionary()
        methods = Dictionary()
        nestedTypes = Dictionary()
        fields = Dictionary()
    }
    typeMembersField.Add(x, m)
    m

type TypeBuilder with
    /// extension val
    member x.members = members x

type env = {
    modules: ModuleBuilder list
    thisType: Type option
    thisMethodGenericArgments: Type list
    entryPoint: MethodBuilder option ref
}
type method_env = {
    env: env
    args: Map<string, uint16>
    locals: Map<string, LocalBuilder>
    lavels: Map<string, Label>
}
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

let rec resolveType env = function
    | Int32 -> typeof<int>
    | Bool -> typeof<bool>
    | Float64 -> typeof<double>
    | Object -> typeof<obj>

    // TODO: nativeint = System.IntPtr; native int を指定したい
    | NativeInt -> typeof<nativeint>
    | Array t -> (resolveType env t).MakeArrayType()

    | This -> getThis env
    | TypeArgmentIndex i -> getThis(env).GetGenericTypeDefinition().GetGenericArguments().[i]
    | MethodArgmentIndex i -> env.thisMethodGenericArgments.[i]

    | TypeName(_, moduleName, nameSpace, nestedParents, typeName, typeArgs) as t ->
        let moduleName = String.concat "." moduleName
        let nameSpace = Seq.map (fun n -> n + ".") nameSpace |> String.concat ""
        let nestedParents = Seq.map (fun n -> n + "+") nestedParents |> String.concat ""
        let fullName = nameSpace + nestedParents + typeName
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
    match t.GetField(name, a) with
    | null -> (t :?> TypeBuilder).members.fields.[name] :> FieldInfo
    | m -> m

type cli_method_base =
    | ConstructorBuilder of ConstructorBuilder
    | ConstructorInfo of ConstructorInfo
    | MethodBuilder of MethodBuilder
    | MethodInfo of MethodInfo

let resolveMethodBaseCore env 
    {
        callconv = cc
        resultType = r
        declaringType = parent
        typeArgs = typeArgs
        methodName = name
        argTypes = argTypes
    }
    =
    let t = resolveType env parent
    let argTypes' = [|for t in argTypes -> resolveType env t|]
    match name with
    | Ctor ->
        let a = B.DeclaredOnly ||| B.Public ||| B.NonPublic ||| B.Instance
        match t.GetConstructor(a, null, argTypes', null) with
        | null -> (t :?> TypeBuilder).members.ctors.[argTypes] |> Choice2Of4
        | c -> Choice1Of4 c

    | MethodName(Id.L name) ->
        let a = B.DeclaredOnly ||| B.Public ||| B.NonPublic
        let a = match cc with Instance -> a ||| B.Instance | Static -> a ||| B.Static
        match t.GetMethod(name, a, null, argTypes', null) with
        | null -> (t :?> TypeBuilder).members.methods.[(name, argTypes)] |> Choice4Of4
        | m -> Choice3Of4 m

let resolveMethod env m =
    match resolveMethodBaseCore env m with
    | Choice3Of4 x -> x
    | Choice4Of4 x -> upcast x
    | x -> failwithf "require method: %A" x

let resolveConstructor env m =
    match resolveMethodBaseCore env m with
    | Choice1Of4 x -> x
    | Choice2Of4 x -> upcast x
    | x -> failwithf "require constructor: %A" x

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
        defineType(name, a)

    let rec classDecl t = function
        | Method _
        | Custom _
        | Field _ -> ()
        | NestedClass c -> classDef (Choice2Of2 t) c

    and classDef parent ({ access = access; decls = decls; name = Id.L name } as c) =
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
                    | Default -> enum 0
                    | Public -> T.NestedPublic
                    | Private -> T.NestedPrivate
                let t = defineType parent.DefineNestedType a c
                parent.members.nestedTypes.Add(name, t)
                t

        for d in decls do classDecl t d

    let decl a = function
        | AssemblyRef _ -> ()
        | Class c -> classDef (Choice1Of2 a) c

module DeclareMembers =
    let parameters defineParameter args =
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

        let argTypes = List.map (snd >> cliType) args

        match name with
        | Ctor ->
            let parameterTypes = Seq.map (resolveType env) argTypes |> Seq.toArray
            let c = parent.DefineConstructor(a, CallingConventions.Any, parameterTypes)
            if isForwardref then
                c.SetImplementationFlags MethodImplAttributes.ForwardRef

            parameters c.DefineParameter args
            parent.members.ctors.Add(argTypes, c)

        | MethodName(Id.L name) ->
            let m = parent.DefineMethod(name, a)
            let env = { env with thisMethodGenericArgments = [] }
            let parameterTypes = Seq.map (resolveType env) argTypes |> Seq.toArray           
            let returnType =
                match resultType with
                | None -> typeof<Void>
                | Some t -> resolveType env t

            m.SetParameters parameterTypes
            m.SetReturnType returnType

            if isForwardref then
                m.SetImplementationFlags(MethodImplAttributes.ForwardRef)

            parameters m.DefineParameter args
            parent.members.methods.Add((name, argTypes), m)

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
        parent.members.fields.Add(name, f)

    let rec classDecl env t = function
        | Custom _ -> ()
        | Method x -> methodDef env t x
        | Field x -> fieldDef env t x
        | NestedClass x -> classDef env (Choice2Of2 t) x

    and classDef env parent { name = Id.L name; decls = decls } =
        let t =
            match parent with
            | Choice1Of2 _ -> resolveDynamicTypeOfModules env name
            | Choice2Of2 t -> t.members.nestedTypes.[name]

        let env = { env with thisType = Some(upcast t) }
        for decl in decls do classDecl env t decl

    let decl env a = function
        | AssemblyRef _ -> ()
        | Class c -> classDef env (Choice1Of2 a) c

module EmitMethods =
    let custom env (t: TypeBuilder) = function
        | { ctor = ctor; args = []; namedArgs = [] } ->
            t.SetCustomAttribute(resolveConstructor env ctor, [||])

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

    let ldelem t = arrayAccess O.Ldelem_U1 O.Ldelem_I4 O.Ldelem_R8 O.Ldelem_Ref t
    let stelem t = arrayAccess O.Stelem_I1 O.Stelem_I4 O.Stelem_R8 O.Stelem_Ref t

    let opcode { env = env; args = args; locals = locals; lavels = lavels } g = function
        | Nop -> g += O.Nop
        | Dup -> g += O.Dup
        | Pop -> g += O.Pop
        | Add -> g += O.Add
        | Neg -> g += O.Neg
        | Sub -> g += O.Sub
        | Mul -> g += O.Mul
        | Div -> g += O.Div
        | Ldarg0 -> g += O.Ldarg_0
        | Ldnull -> g += O.Ldnull
        | LdcI4 x -> ldcI4 g x
        | LdcR8 x -> g.Emit(O.Ldc_R8, x)

        | Label(Id.L l) -> g.MarkLabel <| Map.find l lavels

        | Br(Id.L l) -> g.Emit(O.Br, Map.find l lavels)
        | BneUn(Id.L l) -> g.Emit(O.Bne_Un, Map.find l lavels)
        | Bgt(Id.L l) -> g.Emit(O.Bgt, Map.find l lavels)
        | Brtrue(Id.L l) -> g.Emit(O.Brtrue, Map.find l lavels)

        | Ldarg l -> Map.find l args |> ldarg g
        | Ldloc l -> g.Emit(O.Ldloc, Map.find l locals)
        | Stloc l -> g.Emit(O.Stloc, Map.find l locals)

        | Call(tail, m) ->
            if tail then g += O.Tailcall
            g.EmitCall(O.Call, resolveMethod env m, null)

        | Ret -> g += O.Ret

        | Ldelem t -> g += ldelem t
        | Stelem t -> g += stelem t
        | Newobj(declaringType, argTypes) ->
            let m = ctorRef(declaringType, argTypes)
            g.Emit(O.Newobj, resolveConstructor env m)

        | Ldfld f -> g.Emit(O.Ldfld, resolveField env f)
        | Stfld f -> g.Emit(O.Stfld, resolveField env f)
        | Ldsfld f -> g.Emit(O.Ldsfld, resolveField env f)
        | Stsfld f -> g.Emit(O.Stsfld, resolveField env f)
        | Callvirt(tail, m) ->
            if tail then g += O.Tailcall
            g.EmitCall(O.Callvirt, resolveMethod env m, null)

        | Ldftn m ->
            match resolveMethodBaseCore env m with
            | Choice1Of4 x -> g.Emit(O.Ldftn, x)
            | Choice2Of4 x -> g.Emit(O.Ldftn, x)
            | Choice3Of4 x -> g.Emit(O.Ldftn, x)
            | Choice4Of4 x -> g.Emit(O.Ldftn, x)

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
        let locals = Map.map (fun _ t -> cliType t |> resolveType env |> g.DeclareLocal) locals
        let lavels = Seq.choose (function Label(Id.L l) -> Some(l, g.DefineLabel()) | _ -> None) ops |> Map.ofSeq
        let env = {
            env = env
            args = args
            locals = locals
            lavels = lavels
        }
        for op in ops do opcode env g op

    let methodDef env parent ({ name = name; args = args; body = body } as method') =
        let argTypes = List.map (snd >> cliType) args
        match name with
        | Ctor ->
            let c = members(parent).ctors.[argTypes]
            methodBody env (c.GetILGenerator()) method'

        | MethodName(Id.L name) ->
            let m = members(parent).methods.[(name, argTypes)]
            let env =
                if m.IsGenericMethod then
                    { env with
                        thisMethodGenericArgments = List.ofArray <| m.GetGenericArguments()
                    }
                else env

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
            | Choice2Of2 parent -> parent.members.nestedTypes.[name]

        let env = { env with thisType = Some(upcast t) }
        for decl in decls do classDecl env t decl

    let decl env a = function
        | AssemblyRef _ -> ()
        | Class c -> classDef env (Choice1Of2 a) c

let defineMinCamlAssembly (appDomain: AppDomain) (Prog(def, decls)) =
    let { assemblyName = assemblyName; moduleName = moduleName } = def
    let assemblyName = String.concat "." assemblyName
    let moduleName =
        match moduleName with
        | [] -> assemblyName + ".exe"
        | _ -> String.concat "." moduleName

    let a = appDomain.DefineDynamicAssembly(AssemblyName assemblyName, AssemblyBuilderAccess.RunAndCollect)
    let m = a.DefineDynamicModule moduleName

    // 1. 型の宣言
    for d in decls do DeclareTypes.decl m d

    let env = {
        entryPoint = ref None
        modules = [m]
        thisType = None
        thisMethodGenericArgments = []
    }

    // 2. ジェネリック制約と継承関係とメンバの宣言
    for d in decls do DeclareMembers.decl env m d

    // 3. カスタム属性とメソッド本体の生成
    for d in decls do EmitMethods.decl env m d
    
    // 4. エントリーポイントの設定
    match !env.entryPoint with
    | Some m -> a.SetEntryPoint m
    | _ -> ()

    // 5. 型の作成
    for m in env.modules do
        for t in m.GetTypes() do
            match t with
            | :? TypeBuilder as t -> t.CreateType() |> ignore
            | _ -> ()
    
    a
