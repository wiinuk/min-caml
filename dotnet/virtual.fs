/// translation into assembly with infinite number of virtual registers
[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "TypeNamesMustBePascalCase")>]
[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "IdentifiersMustNotContainUnderscores")>]
module Virtual

open Asm
module P = Tree

type location =
    | Local
    | Arg
    | InstanceField
    | This
    | StaticMethodSelf

type env = {
    fundefs: Map<Id.l, P.fundef>
    vars: Map<Id.t, Type.t * location>
    isTail: bool
    methodName: Id.l
    usedLocals: Map<Id.t, Type.t> ref
}
let addMany xts l ({ vars = vars } as env) =
    { env with vars = List.fold (fun map (x, t) -> Map.add x (t, l) map) vars xts }

let topLevelTypeName = "MinCamlGlobal"
let topLevelType = TypeName(Class, [], [], [], topLevelTypeName, [])
let entrypointName = Id.L "MinCamlEntryPoint"
let localTypeToCliType (Id.L n) = TypeName(Class, [], [], [topLevelTypeName], n, [])

type stack = {
    stack: exp list
    maxSize: int
    size: int
}

let delta = function
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
    | Pop -> -1

    | Neg
    | Ldfld _ -> -1 + 1

    | Dup -> -1 + 2
    
    | BneUn _
    | Bgt _
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

let (+>) x f = f x

let private getArrayElement = function
    | Type.Array t -> t
    | _ -> assert_false()

let private getFunctionElements = function
    | Type.Fun(ts, r) -> ts, r
    | _ -> assert_false()

let private getCliFunctionElements t =
    let ts, t = getFunctionElements t
    List.map cliType ts, cliType t

let ld { vars = env } id acc =
    let t, location = Map.find id env
    match location with
    | Local -> acc++Ldloc id
    | Arg -> acc++Ldarg id
    | This -> acc++Ldarg0
    | InstanceField ->
        acc
        ++Ldarg0
        ++Ldfld { fieldType = cliType t; declaringType = cli_type.This; name = Id.L id }

    | StaticMethodSelf ->
        let argTypes, resultType = getCliFunctionElements t
        let funcType = funType argTypes resultType

        // TODO: デリゲートをキャッシュして使いまわす
        acc
        ++Ldnull
        ++Ldftn(methodRef(Static, Some resultType, topLevelType, Id.L id, [], argTypes))
        ++Newobj(funcType, [Object; NativeInt])

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

/// 式の仮想マシンコード生成 (caml2html: virtual_g)
let rec g ({ isTail = isTail; usedLocals = locals; vars = vars } as env) x acc =
    match x with
    // TODO: 可能ならば unit型 を void に unit値 を Nop に置き換える
    | P.Unit -> acc++Ldnull+>ret env
    | P.Int i -> acc++LdcI4 i+>ret env
    | P.Float d -> acc++LdcR8 d+>ret env

    | P.Unary(op, x) -> acc+>nonTail env x++unary op+>ret env
    | P.Binary(x, op, y) -> acc+>nonTail env x+>nonTail env y++binary op+>ret env

    | P.Condition(x, op, y, e1, e2) ->
        let ifTrue = Id.L <| Id.genid "iftrue"
        let acc = acc+>nonTail env x+>nonTail env y++condition ifTrue op+>g env e1

        if isTail then
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

    | P.Var x -> acc+>ld env x+>ret env

    | P.Seq(e1, e2) -> nonTail env e1 acc++Pop+>g env e2

    // $e1
    // stloc $x
    // $e2
    | P.Let((x, t1), e1, e2) ->
        locals := Map.add x t1 !locals

        nonTail env e1 acc
        ++Stloc x
        +>g { env with vars = M.add x (t1, Local) vars } e2

    // クロージャの生成 (caml2html: virtual_makecls)

    // TODO: デリゲートをキャッシュして使いまわす
    // 静的メソッドから Func<…> を作成
    | P.MakeCls((x, t), { P.entry = l; P.actual_fv = [] }, e2) ->
        // ldnull
        // ldftn static $(resultType t) $topLevelType::$l($(argType t 0), $(argType t 1), …)
        // newobj instance void class [mscorlib]System.Func`…<$(ts.[0]), $(ts.[1]), …, $r>::.ctor(object, native int)
        // stloc $x
        //
        // $e2

        let argTypes, resultType = getCliFunctionElements t
        let funcType = funType argTypes resultType

        let acc =
            acc
            ++Ldnull

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
            ++Ldftn(methodRef(Static, Some resultType, topLevelType, l, [], argTypes))
            ++Newobj(funcType, [Object; NativeInt])
            ++Stloc x

        locals := Map.add x t !locals
        acc+>g { env with vars = Map.add x (t, Local) vars } e2

    // TODO: デリゲートをキャッシュして使いまわす
    // インスタンスメソッドから Func<…> を作成
    | P.MakeCls((x, t), { P.entry = l; P.actual_fv = ys }, e2) ->
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
        // @temp_x.$(name ys.[0]) = $(expr ys.[0]);
        // @temp_x.$(name ys.[1]) = $(expr ys.[1]);
        // ︙
        //
        // var $x = new Func<…>(@temp_x.Invoke);
        // @temp_x.$x = $x;
        //
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
        //
        // dup
        //     $(expr ys.[0])
        //     stfld $(typeof ys.[0]) $l::$(name ys.[0])
        // dup
        //     $(expr ys.[1])
        //     stfld $(typeof ys.[1]) $l::$(name ys.[1])
        // ︙
        //
        // dup
        // dup
        // ldftn instance $r $l::Invoke($(ts.[0]), $(ts.[1]), …)
        // newobj instance void class [mscorlib]System.Func`…<$(ts.[0]), $(ts.[1]), …, $r>::.ctor(object, native int)
        //
        // stloc $x
        // ldloc $x
        // stfld class [mscorlib]System.Func`…<$(ts.[0]), $(ts.[1]), …, $r> $l::$x
        //
        // $e2
        // |]

        let argTypes, resultType = getCliFunctionElements t
        let funcType = funType argTypes resultType
        let closuleType = localTypeToCliType l

        let acc =
            acc
            ++Newobj(closuleType, [])
            +>many ys (fun (y, e) acc ->
                acc
                ++Dup
                +>nonTail env e
                ++Stfld {
                    fieldType = cliType <| P.typeof map vars e
                    declaringType = closuleType
                    name = y
                }
            )

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
            ++Dup
            ++Ldftn(methodRef(Instance, Some resultType, closuleType, Id.L "Invoke", [], argTypes))
            ++Newobj(funcType, [Object; NativeInt])
            ++Stloc x

        let acc =
            let { P.useSelf = useSelf } = Map.find l env.fundefs
            if useSelf then
                acc
                ++Ldloc x
                ++Stfld {
                    fieldType = funcType
                    declaringType = closuleType
                    name = Id.L x
                }
            else
                acc

                // TODO: 不要な Pop をなくす
                ++Pop

        locals := Map.add x t !locals
        g { env with vars = Map.add x (t, Local) vars } e2 acc

    // $(ld x)
    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // callvirt instance !$(ys.length) class [mscorlib]System.Func`…<…>::Invoke(!0, !1, …)
    | P.AppCls(x, ys) ->
        let closureType = P.typeof map vars x
        let argLendth = getFunctionElements closureType |> fst |> List.length

        acc
        +>nonTail env x
        +>nonTailMany ys env
        ++callvirt(
            false,
            Some <| TypeArgmentIndex argLendth,
            cliType closureType,
            "Invoke",
            List.init argLendth TypeArgmentIndex
        )
        +>ret env

    | P.AppDir((Id.L "min_caml_create_array" as x, t), ys) ->
        let elementType = getFunctionElements t |> snd |> getArrayElement |> cliType
        let et = MethodArgmentIndex 0
        acc
        +>nonTailMany ys env
        ++call(false, Static, Some (Array et), topLevelType, x, [elementType], [Int32; et])
        +>ret env

    | P.AppDir((Id.L "min_caml_create_float_array" as x, _), ys) ->
        acc
        +>nonTailMany ys env
        ++call(false, Static, Some (Array Float64), topLevelType, x, [], [Int32; Float64])
        +>ret env

    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // call $(typeof(x).result) MinCamlGlobal::$l($(typeof ys.[0]), $(typeof ys.[1]), …)
    | P.AppDir((x, t), ys) ->
        let argTypes, resultType = getCliFunctionElements t

        acc
        +>nonTailMany ys env
        ++call(isTail && x = env.methodName, Static, Some resultType, topLevelType, x, [], argTypes)
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
        acc
        +>nonTail env y
        +>letTuple env xts e2
        +>g (addMany xts Local env) e2

    | P.Get(x, y) ->
        acc
        +>nonTail env x
        +>nonTail env y
        ++Ldelem(P.typeof map vars x |> getArrayElement)
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
        ++Stelem(P.typeof map env.vars z)
        ++Ldnull
        +>ret env

    // .field public static int32[] $x
    //
    // ldsfld $et[] $topLevelType::$x
    | P.ExtArray(Id.L x, et) ->
        let n = Id.L <| "min_caml_" + x
        acc
        ++Ldsfld { fieldType = Array(cliType et); declaringType = topLevelType; name = n }
        +>ret env

and nonTail env x = g { env with isTail = false } x
and nonTailMany xs env acc = many xs (g { env with isTail = false }) acc

and makeTuple ({ vars = vars } as env) xs acc =
    match tryTake 7 xs with
    | None
    | Some(_, []) ->
        let types = List.map (P.typeof map vars >> cliType) xs
        let tupleType = tupleType types
        let argTypes = List.mapi (fun i _ -> TypeArgmentIndex i) types
        acc
        +>nonTailMany xs env
        ++Newobj(tupleType, argTypes), tupleType

    | Some(xs, tail) ->
        let types7 = List.map (P.typeof map vars >> cliType) xs
        let acc = acc+>nonTailMany xs env
        let acc, tailType = makeTuple env tail acc
        let tupleType = TypeName(Class, ["mscorlib"], ["System"], [], "Tuple`8", types7 @ [tailType])
        let argTypes8 = [for i in 0..7 -> TypeArgmentIndex i]
        acc
        ++Newobj(tupleType, argTypes8), tupleType

and letTuple { usedLocals = locals } xts e2 acc =
    let s = P.freeVars e2
    let rec aux xts acc =
        let tupleType = List.map (snd >> cliType) xts |> tupleType
        let xts, tail =
            match tryTake 7 xts with
            | None -> xts, []
            | Some(xts, tail) -> xts, tail

        let acc =
            acc
            +>many (List.indexed xts) (fun (i, (x, t)) acc ->
                if not <| Set.contains x s then acc else

                locals := Map.add x t !locals

                acc
                ++Dup
                ++getProp(Instance, TypeArgmentIndex i, tupleType, "Item" + string (i + 1))
                ++Stloc x
            )

        if List.isEmpty tail then acc else

        acc
        ++getProp(Instance, TypeArgmentIndex 7, tupleType, "Rest")
        +>aux tail

    aux xts acc
    ++Pop

let methodDef fundefs access callconv resultType name args formalFvs isEntrypoint env e =
    let env = List.fold (fun env (y, t) -> Map.add y (t, Arg) env) env args
    let env = List.fold (fun env (z, t) -> Map.add z (t, InstanceField) env) env formalFvs

    let locals = ref Map.empty
    let env = { fundefs = fundefs; vars = env; isTail = true; usedLocals = locals; methodName = name }
    let stack = { stack = []; maxSize = 8; size = 0 }
    let { stack = opcodes; maxSize = maxStack } = g env e stack
    let body = {
        maxStack = if maxStack <= 8 then None else Some maxStack
        isEntrypoint = isEntrypoint
        locals = !locals
        opcodes = List.rev opcodes
    }
    {
        access = access
        isSpecialname = false
        isRtspecialname = false
        callconv = callconv
        resultType = Some <| cliType resultType
        name = MethodName name
        args = args
        isForwardref = false
        body = body
    }

let compilerGeneratedAttributeType =
    TypeName(Class, ["mscorlib"], ["System";"Runtime";"CompilerServices"], [], "CompilerGeneratedAttribute", [])

let compilerGenerated = {
    ctor = ctorRef(compilerGeneratedAttributeType, [])
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

    let funcType = cliType t
    let resultType = getFunctionElements t |> snd
    let acc =
        []
        ++Custom compilerGenerated

    let acc =
        if useSelf then acc++Field { access = Public; fieldType = funcType; name = x }
        else acc

    let acc =
        acc
        +>many zts (fun (z, y) acc ->
            acc++Field { access = Public; fieldType = cliType y; name = Id.L z }
        )
        ++Method(methodDef fundefs Public Instance resultType (Id.L "Invoke") yts ((x', t)::zts) false Map.empty e)
        ++Method defaultCtor
    {
        isSealed = true
        isBeforefieldinit = true
        name = x
        decls = List.rev acc
    }

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
    methodDef fundefs Public Static resultType x yts [] false env e

/// 関数の仮想マシンコード生成 (caml2html: virtual_h)
let h fundefs = function
    | { P.formalFreeVars = [] } as f -> Method <| staticMethod fundefs f
    | f -> NestedClass <| closureClass fundefs f

let f' (P.Prog(fundefs, e)) =
    let env = List.fold (fun env ({ P.name = name, _ } as f) -> Map.add name f env) Map.empty fundefs
    let fundefs = List.map (h env) fundefs
    Prog(
        fundefs,
        methodDef env Public Static Type.Unit entrypointName [] [] false Map.empty e
    )

/// プログラム全体の仮想マシンコード生成 (caml2html: virtual_f)
let f p = P.f p |> StackAlloc.f |> f'
