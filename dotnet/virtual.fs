/// translation into assembly with infinite number of virtual registers
[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "TypeNamesMustBePascalCase")>]
[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "IdentifiersMustNotContainUnderscores")>]
module Virtual

open AsmType
open Asm
module P = Tree

type location =
    | Local
    | Arg
    | VirtualUnit
    | InstanceField
    | This
    | StaticMethodSelf

type global_env = {
    globalCaches: Map<Id.t, field_def> ref
    fundefs: Map<Id.l, P.fundef>
}

type locals = Map<Id.t, Id.t * asm_type> ref
type env = {
    globalEnv: global_env
    vars: Map<Id.t, Type.t * location>
    isTail: bool
    isUnitValue: bool
    methodName: Id.l
    usedLocals: locals
}
let addMany xts l ({ vars = vars } as env) =
    { env with vars = List.fold (fun map (x, t) -> Map.add x (t, l) map) vars xts }

let startupMethodName = "MinCamlStartup"
let entryPointMethodName = "Main"
let topLevelTypeName = "MinCamlGlobal"
let topLevelType = TypeRef(type_kind.Class, [], [], [], topLevelTypeName, [])
let localTypeToAsmType (Id.L n) = TypeRef(type_kind.Class, [], [], [topLevelTypeName], n, [])

type stack = {
    stack: exp list
    maxSize: int
    size: int
}

let delta = function
    | Nop
    | Label _
    | Br _ -> 0

    // -1 or 0
    | Ret -> 0

    | Ldloc _
    | Ldarg0
    | Ldarg _
    | Ldnull
    | LdcI4 _
    | LdcR8 _
    | Ldsfld _
    | Ldftn _ -> 1

    | Stloc _
    | Stsfld _
    | Pop
    | Brtrue _ -> -1

    | Neg
    | Ldfld _
    | Newarr _
    | ConvU2
    | ConvI4
    | ConvR8
    | ConvOvfU1 -> -1 + 1

    | Dup -> -1 + 2

    | BneUn _
    | Bgt _
    | Blt _
    | Stfld _ -> -2

    | Add
    | Sub
    | Mul
    | Div
    | Ldelem _ -> -2 + 1

    | Stelem _ -> -3

    | Call(_, { resultType = rt; argTypes = ts })
    | Callvirt(_, { resultType = rt; argTypes = ts }) -> -(List.length ts) + Option.count rt
    | Newobj(_, ts) -> -(List.length ts) + 1

let (++) { stack = stack; maxSize = maxSize; size = size } x =
    let size = size + delta x
    {
        stack = x::stack
        maxSize = max maxSize size
        size = size
    }

let inline private (+>) x f = f x

let private getArrayElement = function
    | Type.Array t -> t
    | _ -> assert_false()

let private getFunctionElements = function
    | Type.Fun(ts, r) -> ts, r
    | _ -> assert_false()

// デリゲートをキャッシュして使いまわす
// NOTE: デリゲートをキャッシュする操作はスレッドセーフでないが、二重にインスタンスが生成されるぐらいで特に問題ないはず
//
// [cs|
// var @temp = $methodName
// (@temp === null) ? ($methodName = new System.Func<…>(…)) : @temp
// |]
//
// [il|
// ldsfld $methodName   // Func<…>
// dup                  // Func<…>; Func<…>
// brinst 'created'     // (null: Func<…>)
//     ldftn …          // null; ((…) => …)*
//     newobj System.Func<…> // Func<…>
//     dup              // Func<…>; Func<…>
//     stsfld $methodName    // Func<…>
// 'created':       // Func<…>
// |] 
let getOrCreateStaticCachedDelegate env m (Id.L name' as globalFieldName) acc =
    let { globalEnv = { globalCaches = caches } } = env
    let { argTypes = argTypes; resultType = resultType } = m
    let funcType = func(argTypes, resultType)

    let fieldRef, fieldDef = fieldSpec(Private, Static, funcType, asm_type.This, globalFieldName)

    caches := Map.add name' fieldDef !caches

    let created = Id.L <| Id.genid "created"

    acc
    ++Ldsfld fieldRef
    ++Dup
    ++brinst created
    
    // ECMA-335 2012 Ⅲ.4.21
    //
    // デリゲートを作成する時の正当性検証可能な CIL コード
    //
    // dup
    // ldvirtftn $virtualFunction
    // newobj $ctor
    //
    // または
    //
    // ldftn $function
    // newobj $ctor
    ++Ldftn m
    ++Newobj(funcType, [Object; NativeInt])

    ++Dup
    ++Stsfld fieldRef
    ++Label created

let many xs f acc = List.fold (fun acc x -> f x acc) acc xs

let ret { isTail = isTail } acc = if isTail then acc++Ret else acc

let unary = function
    | P.Neg -> Neg

let binary = function
    | P.Add -> Add
    | P.Sub -> Sub
    | P.Mul -> Mul
    | P.Div -> Div

let condition target = function
    | P.Eq -> BneUn target
    | P.Le -> Bgt target

let map = {
    P.add = fun k v map -> Map.add k (v, Local) map
    P.find = fun k map -> Map.find k map |> fst
}

let ldUnit { isUnitValue = isUnitValue } t acc =
    if isUnitValue && Option.isNone t then acc++Ldnull
    else acc

// locals の使用状況を vars から解析して、locals をできるだけ減らす
let allocLocal { usedLocals = locals; vars = vars } x t =
    let asmType = asmType t

    // vars の中になく型が等しい local ( 未使用 local ) を探す
    let l =
        Map.tryPick (fun x' (l', t') ->
            if asmType = t' && not (Map.containsKey x' vars) then Some l'
            else None
        ) !locals
    
    let l =
        match l with
        | Some l -> l
        | None -> Id.gentmp t

    locals := Map.add x (l, asmType) !locals
    l

/// 式の仮想マシンコード生成 (caml2html: virtual_g)
let rec g env x acc =
    match x with
    | P.Unit ->
        if env.isUnitValue then acc++Ldnull+>ret env
        else acc+>ret env

    | P.Int i -> acc++LdcI4 i+>ret env
    | P.Float d -> acc++LdcR8 d+>ret env

    | P.Unary(op, x) -> acc+>nonTail env x++unary op+>ret env
    | P.Binary(x, op, y) -> acc+>nonTail env x+>nonTail env y++binary op+>ret env

    | P.Condition(x, op, y, e1, e2) ->
        let ifTrue = Id.L <| Id.genid "iftrue"
        let acc = acc+>nonTail env x+>nonTail env y++condition ifTrue op+>g env e1

        if env.isTail then
            // ldxxx $x
            // ldxxx $y
            // $op 'iftrue'
            //     $e1
            //
            // 'iftrue':
            //     $e2
            //
            acc++Label ifTrue+>g env e2

        else
            // ldxxx $x
            // ldxxx $y
            // $op 'iftrue'
            //     $e1
            //     br 'endif'
            //
            // 'iftrue':
            //     $e2
            //
            // 'endif':
            let endIf = Id.L <| Id.genid "endif"
            acc++Br endIf++Label ifTrue+>g env e2++Label endIf

    | P.Var x ->
        let acc =
            let t, location = Map.find x env.vars
            match location with
            | Local -> acc++Ldloc(Map.find x !env.usedLocals |> fst)
            | Arg -> acc++Ldarg x
            | VirtualUnit -> acc
            | This -> acc++Ldarg0
            | InstanceField ->
                acc
                ++Ldarg0
                ++Ldfld(fieldRef(asmType t, asm_type.This, Id.L x))

            | StaticMethodSelf ->
                let { env.methodName = name } = env
                let argTypes, resultType = funcElements <| getFunctionElements t
                let m = methodRef(Static, resultType, topLevelType, x, [], argTypes)
                acc
                +>getOrCreateStaticCachedDelegate env m name
                ++Nop

        acc+>ret env

    | P.Seq(e1, e2) ->
        let isVoid =
            P.typeof map env.vars e1
            |> asmTypeOrVoid
            |> Option.isNone

        let acc = nonTail env e1 acc
        let acc = if isVoid then acc else acc++Pop
        g env e2 acc

    // $e1
    // stloc $x
    // $e2
    | P.Let((x, t1), e1, e2) ->
        let acc = acc+>nonTail env e1
        let env = { env with vars = Map.add x (t1, Local) env.vars }
        acc
        ++Stloc(allocLocal env x t1)
        +>g env e2

    // クロージャの生成 (caml2html: virtual_makecls)

    // 静的メソッドから Func<…> を作成
    | P.LetCls((x, t), { P.entry = Id.L l' as l; P.actual_fv = [] }, e2) ->
        let argTypes, resultType = funcElements <| getFunctionElements t
        let m = methodRef(Static, resultType, topLevelType, l', [], argTypes)
        let acc =
            acc
            +>getOrCreateStaticCachedDelegate env m l

        let env = { env with vars = Map.add x (t, Local) env.vars }
        acc
        ++Stloc(allocLocal env x t)
        +>g env e2
        
    // 静的メソッドから Func<…> を作成
    | P.Cls(t, { P.entry = Id.L l' as l; P.actual_fv = [] }) ->
        let argTypes, resultType = funcElements <| getFunctionElements t
        let m = methodRef(Static, resultType, topLevelType, l', [], argTypes)
        acc
        +>getOrCreateStaticCachedDelegate env m l
        +>ret env

    // インスタンスメソッドから Func<…> を作成
    | P.LetCls((x, t), closure, e2) ->
        let acc =
            acc
            +>g env (P.Cls(t, closure))

        let env = { env with vars = Map.add x (t, Local) env.vars }
        acc
        ++Stloc(allocLocal env x t)
        +>g env e2

    | P.Cls(t, { P.entry = l; P.actual_fv = ys }) ->
        // [mincaml|let $x : $($ts -> $r) = let rec $l … = … $ys … in $e2|]

        // [cs|
        // class sealed $l
        // {
        //     public $(typeof ys.[0]) $(name ys[0]);
        //     public $(typeof ys.[1]) $(name ys[1]);
        //     ︙
        //
        //     public $r Invoke($(ts.[0]) …, $(ts.[1]) …, …)
        //     {
        //         $(closure.entry)
        //     }
        // }
        //
        // var @temp_x = new $l();
        //
        // @temp_x.$(name ys.[0]) = $(expr ys.[0]);
        // @temp_x.$(name ys.[1]) = $(expr ys.[1]);
        // ︙
        //
        // var @temp_f = new Func<…>(@temp_x.Invoke);
        //
        // #if useSelf
        // @temp_x.$x = @temp_f;
        // #endif
        //
        // var $x = @temp_f
        // $e2
        // |]

        // [il|
        // .class sealed beforefieldinit $l
        // {
        //     .custom instance void [mscorlib]System.Runtime.CompilerServices.CompilerGeneratedAttribute::.ctor()
        //     .field public class [mscorlib]System.Func`…<$(ts.[0]), $(ts.[1]), …, $r> $x;
        //
        //     .field public $(typeof ys.[0]) $(name ys.[0])
        //     .field public $(typeof ys.[1]) $(name ys.[1])
        //     ︙
        //
        //     .method public hidebysig instance $r Invoke($(ts.[0]) …, $(ts.[1]) …, …) cil managed
        //     {
        //         $(closure.entry)
        //     }
        // }
        //
        // newobj instance void $l::.ctor()
        // // $l
        //
        // dup
        //     // $l; $l
        //     $(expr ys.[0])
        //     // $l; $l; $(typeof ys.[0])
        //     stfld $(typeof ys.[0]) $l::$(name ys.[0])
        // // $l
        // dup
        //     $(expr ys.[1])
        //     stfld $(typeof ys.[1]) $l::$(name ys.[1])
        // ︙
        // // $l
        //
        // #if useSelf
        //     dup
        //     // $l; $l
        //     dup
        //     // $l; $l; $l
        //     ldftn instance $r $l::Invoke($(ts.[0]), $(ts.[1]), …)
        //     // $l; $l; $l; ((…) => $r)*
        //     newobj instance void class System.Func`…<$(ts.[0]), $(ts.[1]), …, $r>::.ctor(object, native int)
        //     // $l; $l; Func`…<…>
        //     stfld class System.Func`…<$(ts.[0]), $(ts.[1]), …, $r> $l::$x
        //     // $l
        //     ldfld class System.Func`…<$(ts.[0]), $(ts.[1]), …, $r> $l::$x
        //     // Func`…<…>
        // #else
        //     ldftn instance $r $l::Invoke($(ts.[0]), $(ts.[1]), …)
        //     // $l; ((…) => $r)*
        //     newobj instance void class System.Func`…<$(ts.[0]), $(ts.[1]), …, $r>::.ctor(object, native int)
        //     // Func`…<…>
        // #endif
        // |]

        let argTypes, resultType = funcElements <| getFunctionElements t
        let funcType = func (argTypes, resultType)
        let closuleType = localTypeToAsmType l

        let acc =
            acc
            ++Newobj(closuleType, [])
            +>many ys (fun (y, e) acc ->
                acc
                ++Dup
                +>nonTail env e
                ++Stfld(fieldRef(asmType <| P.typeof map env.vars e, closuleType, y))
            )

        let { P.useSelf = useSelf } = Map.find l env.globalEnv.fundefs
        if useSelf then
            let selfField = fieldRef(funcType, closuleType, l)
            acc
            ++Dup
            ++Dup

            // ECMA-335 2012 Ⅲ.4.21
            //
            // デリゲートを作成する時の正当性検証可能な CIL コード
            //
            // dup
            // ldvirtftn $virtualFunction
            // newobj $ctor
            //
            // または
            //
            // ldftn $function
            // newobj $ctor
            ++Ldftn(methodRef(Instance, resultType, closuleType, "Invoke", [], argTypes))
            ++Newobj(funcType, [Object; NativeInt])
            ++Stfld selfField
            ++Ldfld selfField
            +>ret env
        else
            acc
            ++Ldftn(methodRef(Instance, resultType, closuleType, "Invoke", [], argTypes))
            ++Newobj(funcType, [Object; NativeInt])
            +>ret env

    // $(ld x)
    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // callvirt instance !$(ys.length) class [mscorlib]System.Func`…<…>::Invoke(!0, !1, …)
    | P.AppCls(x, ys) ->
        let closureType = P.typeof map env.vars x
        let argTypes, resultType = getFunctionElements closureType |> funcElements
        let argLendth = List.length argTypes

        let closureType = asmType closureType
        let resultType = resultType |> Option.map (fun _ -> TypeArgmentIndex argLendth)
        let argTypes = List.init argLendth TypeArgmentIndex

        acc
        +>nonTail env x
        +>nonTailMany env ys
        ++callvirt(resultType, closureType, "Invoke", argTypes)
        +>ldUnit env resultType
        +>ret env

    | P.AppDir((Id.L("min_caml_create_array" as x), t), ys) ->
        let elementType = getFunctionElements t |> snd |> getArrayElement |> asmType
        let et = MethodArgmentIndex 0
        acc
        +>nonTailMany env ys
        ++call(Static, Some (Array et), topLevelType, x, [elementType], [Int32; et])
        +>ret env

    | P.AppDir((Id.L("min_caml_create_float_array" as x), _), ys) ->
        acc
        +>nonTailMany env ys
        ++call(Static, Some (Array Float64), topLevelType, x, [], [Int32; Float64])
        +>ret env

    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // call $(typeof(x).result) MinCamlGlobal::$l($(typeof ys.[0]), $(typeof ys.[1]), …)
    | P.AppDir((Id.L x' as x, t), ys) ->
        let argTypes, resultType = getFunctionElements t |> funcElements

        acc
        +>nonTailMany env ys
        ++Call(env.isTail && x = env.methodName, methodRef(Static, resultType, topLevelType, x', [], argTypes))
        +>ldUnit env resultType
        +>ret env

    // 組の生成 (caml2html: virtual_tuple)
    | P.Tuple xs ->
        // $(ld ys.[0])
        // $(ld ys.[1])
        // ︙
        //
        // newobj instance void class System.Tuple`…<…>::.ctor(…)
        acc
        +>(makeTuple env xs >> fst)
        +>ret env

    // $(ld y)
    // dup
    //     call instance !0 class [mscorlib]System.Tuple`…<…>::get_Item…()
    //     stloc $(fst xys.[0])
    // dup
    //     call instance !1 class [mscorlib]System.Tuple`…<…>::get_Item…()
    //     stloc $(fst xys.[1])
    // ︙
    //
    // $e2
    | P.LetTuple(xts, y, e2) ->
        let acc = acc+>nonTail env y
        let env = addMany xts Local env
        acc
        +>letTuple env xts e2
        +>g env e2

    | P.Get(x, y) ->
        acc
        +>nonTail env x
        +>nonTail env y
        ++Ldelem(P.typeof map env.vars x |> getArrayElement |> asmType)
        +>ret env

    | P.Put(x, y, z) ->
        // $(ld x)
        // $(ld y)
        // $(ld z)
        // $(stelem (elementTypeOf x))

        acc
        +>nonTail env x
        +>nonTail env y
        +>nonTail env z
        ++Stelem(P.typeof map env.vars z |> asmType)
        +>ldUnit env None
        +>ret env

    // .field public static int32[] $x
    //
    // ldsfld $et[] $topLevelType::$x
    | P.ExtArray(Id.L x, et) ->
        let n = Id.L <| "min_caml_" + x
        acc
        ++Ldsfld { fieldType = Array(asmType et); declaringType = topLevelType; name = n }
        +>ret env

and nonTail env x = g { env with isTail = false } x
and nonTailMany env xs acc = many xs (g { env with isTail = false }) acc
and nonTailUnitValueMany env es acc = many es (g { env with isUnitValue = true; isTail = false }) acc


and makeTuple ({ vars = vars } as env) xs acc =
    match tryTake 7 xs with
    | None
    | Some(_, []) ->
        let types = List.map (P.typeof map vars >> asmType) xs
        let tupleType = tuple types
        let argTypes = List.mapi (fun i _ -> TypeArgmentIndex i) types
        acc
        +>nonTailMany env xs
        ++Newobj(tupleType, argTypes), tupleType

    | Some(xs, tail) ->
        let types7 = List.map (P.typeof map vars >> asmType) xs
        let acc = acc+>nonTailMany env xs
        let acc, tailType = makeTuple env tail acc
        let tupleType = TypeRef(type_kind.Class, ["mscorlib"], ["System"], [], "Tuple`8", types7 @ [tailType])
        let argTypes8 = [for i in 0..7 -> TypeArgmentIndex i]
        acc
        ++Newobj(tupleType, argTypes8), tupleType

and letTuple env xts e2 acc =
    let s = P.freeVars e2
    let rec aux xts acc =
        let tupleType = List.map (snd >> asmType) xts |> tuple
        let xts, tail =
            match tryTake 7 xts with
            | None -> xts, []
            | Some(xts, tail) -> xts, tail

        let acc =
            acc
            +>many (List.indexed xts) (fun (i, (x, t)) acc ->
                if not <| Set.contains x s then acc else

                acc
                ++Dup
                ++getProp(Instance, TypeArgmentIndex i, tupleType, "Item" + string (i + 1))
                ++Stloc(allocLocal env x t)
            )

        if List.isEmpty tail then acc else

        acc
        ++getProp(Instance, TypeArgmentIndex 7, tupleType, "Rest")
        +>aux tail

    aux xts acc
    ++Pop

let methodDef genv access callconv resultType name args formalFvs env e =
    let env =
        List.fold (fun env (y, t) ->
            let location = match t with Type.Unit -> VirtualUnit | _ -> Arg
            Map.add y (t, location) env
        ) env args

    let env = List.fold (fun env (z, t) -> Map.add z (t, InstanceField) env) env formalFvs

    let resultType = asmTypeOrVoid resultType

    // Unit 引数を無視
    let args =
        args
        |> List.choose (fun (x, t) ->
            asmTypeOrVoid t
            |> Option.map (fun t -> x, t)
        )

    let locals = ref Map.empty
    let env = { globalEnv = genv; vars = env; isUnitValue = false; isTail = true; usedLocals = locals; methodName = name }
    let stack = { stack = []; maxSize = 8; size = 0 }
    let { stack = opcodes; maxSize = maxStack } = g env e stack
    let maxStack = if maxStack <= 8 then None else Some maxStack
    let locals =
        !locals
        |> Map.toSeq
        |> Seq.map snd
        |> Seq.distinct
        |> Seq.toList

    Asm.methodDef
        (access, callconv, resultType, name, [], args)
        (maxStack, locals)
        (List.rev opcodes)

let compilerGenerated = {
    ctor = ctorRef(asmtypeof<System.Runtime.CompilerServices.CompilerGeneratedAttribute>, [])
    args = []
    namedArgs = []
}

// .class sealed beforefieldinit $x
// {
//     .custom instance void [mscorlib]System.Runtime.CompilerServices.CompilerGeneratedAttribute::.ctor()
//
//     .field public [mscorlib]System.Func`…<$(argType(t).[0]), $(argType(t).[1]), …, $(resultType t)> $x
//     .field public $(snd zts.[0]) $(fst zts.[0])
//     .field public $(snd zts.[1]) $(fst zts.[1])
//     ︙
//
//     .method public hidebysig instance $(resultType t) Invoke
//     (
//         $(snd yts.[0]) $(fst yts.[0]),
//         $(snd yts.[1]) $(fst yts.[1]),
//         ︙
//     )
//     cil managed
//     {
//        .locals init
//        (
//            …
//        )
//        $e
//    }
//
//    .method public hidebysig specialname rtspecialname instance void .ctor()
//    cil managed
//    {
//      ldarg.0
//      call instance void System.Object::.ctor()
//      ret
//    }
// }
let closureClass fundefs { P.name = Id.L x' as x, t; P.args = yts; P.useSelf = useSelf; P.formalFreeVars = zts; P.body = e } =
    let (++) xs x = x::xs

    let funcType = asmType t
    let resultType = getFunctionElements t |> snd
    let acc =
        []
        ++Custom compilerGenerated

    let acc =
        if useSelf then acc++field(Public, Instance, funcType, x)
        else acc

    acc
    +>many zts (fun (z, y) acc -> acc++field(Public, Instance, asmType y, Id.L z))
    ++Method defaultCtor
    ++Method(methodDef fundefs Public Instance resultType (Id.L "Invoke") yts ((x', t)::zts) Map.empty e)
    |> List.rev
    |> classDef(Default, Sealed, x')

// .method public hidebysig static $(resultType t) $x
// (
//     $(snd yts.[0]) $(fst yts.[0]),
//     $(snd yts.[1]) $(fst yts.[1]),
//     ︙
// )
// cil managed
// {
//     .locals
//     (
//         [0] ?type ?name,
//         [1] ?type
//     )
//     $e
// }
let staticMethod fundefs { P.name = Id.L x' as x, t; P.args = yts; P.body = e } =
    let resultType = getFunctionElements t |> snd
    let env = Map.add x' (t, StaticMethodSelf) Map.empty
    methodDef fundefs Public Static resultType x yts [] env e

let entryPoint =
    entryPointDef (Public, Id.L entryPointMethodName, None) (None, []) [
        call(Static, None, topLevelType, startupMethodName, [], [])
        Ret
    ]

// mscorlib は、System.Tuple`... が存在するバージョン 4.0.0.0 以上を指定
let mscorlib = {
    name = "mscorlib"
    publickeytoken = List.ofArray "\xB7\x7A\x5C\x56\x19\x34\xE0\x89"B
    ver = Some(4,0,0,0)
}

/// 関数の仮想マシンコード生成 (caml2html: virtual_h)
let h fundefs = function
    | { P.formalFreeVars = [] } as f -> Method <| staticMethod fundefs f
    | f -> NestedClass <| closureClass fundefs f

let f' (P.Prog(fundefs, e)) =
    let fields = ref Map.empty
    let env = {
        fundefs = List.fold (fun env ({ P.name = name, _ } as f) -> Map.add name f env) Map.empty fundefs
        globalCaches = fields
    }
    let fundefs = List.map (h env) fundefs
    let startup = methodDef env Public Static Type.Unit (Id.L startupMethodName) [] [] Map.empty e

    let fields = Map.toList !fields |> List.map (snd >> Field)

    let assemblyDef = {
        assemblyName = ["MinCamlGlobal"]
        moduleName = []
    }
    let decls = [
        AssemblyRef mscorlib
        Class <| classDef (Public, StaticClass, topLevelTypeName) (
            fields @
            fundefs @
            [
            Method startup
            Method entryPoint
            ]
        )
    ]
    Prog(assemblyDef, decls)

/// プログラム全体の仮想マシンコード生成 (caml2html: virtual_f)
let f p = P.f p |> StackAlloc.f |> f'
