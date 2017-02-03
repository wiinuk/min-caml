/// translation into assembly with infinite number of virtual registers
module Virtual

open Asm

type location =
    | Local
    | Arg
    | InstanceField
    | This
    | StaticMethodSelf

type env = {
    vars: Map<Id.t, Type.t * location>
    isTail: bool
    methodName: Id.l
    locals: Map<Id.t, Type.t> ref
}

let topLevelTypeName = "MinCamlGlobal"
let topLevelType = TypeName(Class, [], [], [], topLevelTypeName, [])
let entrypointName = Id.L "MinCamlEntryPoint"
let localTypeToCliType (Id.L n) = TypeName(Class, [], [], [topLevelTypeName], n, [])

let emptyBody = {
    isEntrypoint = false
    locals = Map.empty
    opcodes = [Ret]
}

let (++) xs x = x::xs
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

let addRet isTail acc = if isTail then acc++Ret else acc

let (|Binary|_|) = function
    | Closure.Add(x, y)
    | Closure.FAdd(x, y) -> Some(Add, x, y)
    | Closure.Sub(x, y)
    | Closure.FSub(x, y) -> Some(Sub, x, y)
    | Closure.FMul(x, y) -> Some(Mul, x, y)
    | Closure.FDiv(x, y) -> Some(Div, x, y)
    | _ -> None

let (|Unary|_|) = function
    | Closure.Neg x
    | Closure.FNeg x -> Some(Neg, x)
    | _ -> None

let (|Conditional|_|) = function
    | Closure.IfEq(x, y, e1, e2) -> Some(BneUn, x, y, e1, e2)
    | Closure.IfLE(x, y, e1, e2) -> Some(Bgt, x, y, e1, e2)
    | _ -> None

let notContains2 k1 k2 e1 e2 =
    let xs1 = Closure.fv e1
    not (Set.contains k1 xs1) &&
    not (Set.contains k2 xs1) &&

    let xs2 = Closure.fv e2
    not (Set.contains k1 xs2) &&
    not (Set.contains k2 xs2)

let notContains k e = not (Set.contains k (Closure.fv e))

let takeLets1 defaultV (|Sentinel|) = function
    | Closure.Let((x, _), e, k) ->
        let rec take xs es = function
            | Closure.Let((x, _), e, k) when List.forall (fun x -> notContains x e) xs ->
                take (x::xs) (e::es) k

            | Sentinel xs es x -> x

        take [x] [e] k

    | _ -> defaultV

let (|AppDir|AppCls|NoApp|) x =
    takeLets1 NoApp (fun xs es -> function
        | Closure.AppDir(f, xs') when List.rev xs = xs' -> AppDir(f, es)
        | Closure.AppCls(f, xs') when List.rev xs = xs' -> AppCls(f, es)
        | _ -> NoApp
    ) x

/// 式の仮想マシンコード生成 (caml2html: virtual_g)
let rec g ({ isTail = isTail; locals = locals; vars = vars } as env) x acc =
    match x with
    | Closure.Unit -> acc++Ldnull+>addRet isTail
    | Closure.Int i -> acc++LdcI4 i+>addRet isTail
    | Closure.Float d -> acc++LdcR8 d+>addRet isTail

    | Unary(op, x) -> acc+>ld env x++op+>addRet isTail
    | Binary(op, x, y) -> acc+>ld env x+>ld env y++op+>addRet isTail
    | Conditional x -> g_branchRelation env x acc
    | Closure.Var x -> acc+>ld env x+>addRet isTail

    // $x1 = $e1
    // $op $x1' // x1 = x1'
    | Closure.Let((x1, _), e1, Unary(op, x1')) when x1 = x1' ->
        let env = { env with isTail = false }
        acc+>g env e1++op

    // $x1 = $e1
    // $x2 = $e2 // e2 の中に x1 を含まない
    // $x1' $op $x2' // x1 = x1' && x2 = x2'
    | Closure.Let((x1, _), e1, Closure.Let((x2, _), e2, Binary(op, x1', x2')))
        when x1 = x1' && x2 = x2' && notContains x1 e2
        ->

        let env = { env with isTail = false }
        acc+>g env e1+>g env e2++op

    // $x1 = $e1
    // $x2 = $e2 // e2 の中に x1 を含まない
    // if $x1' $op $x2' then // x1 = x1' && x2 = x2'
    //     $ifTrue // ifTrue の中に x1 と x2 を含まない
    // else
    //     $ifFalse // ifFalse の中に x1 と x2 を含まない
    | Closure.Let((x1, _), e1, Closure.Let((x2, _), e2, Conditional((op, x1', x2', ifTrue, ifFalse) as c)))
        when x1 = x1' && x2 = x2' && notContains x1 e2 && notContains2 x1 x2 ifTrue ifFalse
        ->

        let env' = { env with isTail = false }
        acc+>g env' e1+>g env' e2+>g_branchRelationTail env (op, e1, e2)

    // $x1 = $e1
    // $x2 = $e2 // e2 の中に x1 を含まない
    // $x3 = $e3 // e3 の中に x1 と x2 を含まない
    // ︙
    // 
    // $f($x1', $x2', $x3', …) // x1 = x1' && x2 = x2' && x3 = x3' && …
    | AppDir((x, t), es) ->
        let argTypes, resultType = getCliFunctionElements t

        acc
        +>many es (g { env with isTail = false })
        ++Call(isTail && x = env.methodName, methodRef(Static, Some resultType, topLevelType, x, [], argTypes))
        +>addRet isTail

    | AppCls(x, es) ->
        let closureType = M.find x vars |> fst
        let argLendth = getFunctionElements closureType |> fst |> List.length

        acc
        +>ld env x
        +>many es (g { env with isTail = false })
        ++callvirt(
            false,
            Some <| TypeArgmentIndex argLendth,
            cliType closureType,
            "Invoke",
            List.init argLendth TypeArgmentIndex
        )
        +>addRet isTail

    // TODO: Syntax.Tuple, Syntax.LetTuple, Syntax.Array, Syntax.Get, Syntax.Put
    | Closure.Tuple xs ->
        takeLets1 [] (function )

    // $e1
    // stloc $x
    // $e2
    | Closure.Let((x, t1), e1, e2) ->
        let acc = g { env with isTail = false } e1 acc++Stloc x
        locals := Map.add x t1 !locals
        g { env with vars = M.add x (t1, Local) vars } e2 acc

    // クロージャの生成 (caml2html: virtual_makecls)

    // TODO: デリゲートをキャッシュして使いまわす
    // 静的メソッドから Func<…> を作成
    | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = [] }, e2) ->
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
            ++Ldftn(methodRef(Static, Some resultType, topLevelType, l, [], argTypes))
            ++Newobj(funcType, [Object; NativeInt])
            ++Stloc x

        locals := Map.add x t !locals
        g { env with vars = Map.add x (t, Local) vars } e2 acc

    // TODO: デリゲートをキャッシュして使いまわす
    // インスタンスメソッドから Func<…> を作成
    | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = ys }, e2) ->
        // [mincaml|let $x : $($ts -> $r) = let rec $l … = … $ys … in $e2|]

        // [cs|
        // class sealed $l
        // {
        //     public $(typeof ys.[0]) $(ys[0]);
        //     public $(typeof ys.[1]) $(ys[1]);
        //     ︙
        //
        //     public $r Invoke($(ts.[0]) …, $(ts.[1]) …, …)
        //     {
        //         $(closure.entry)
        //     }
        // }
        //
        // var @temp_x = new $l();
        // @temp_x.$(ys.[0]) = $(ys.[0]);
        // @temp_x.$(ys.[1]) = $(ys.[1]);
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
        //     .field public $(typeof ys.[0]) $(ys.[0])
        //     .field public $(typeof ys.[1]) $(ys.[1])
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
        //     $(ld ys.[0])
        //     stfld $(typeof ys.[0]) $l::$(ys.[0])
        // dup
        //     $(ld ys.[1])
        //     stfld $(typeof ys.[1]) $l::$(ys.[1])
        // ︙
        //
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
            +>many ys (fun y acc ->
                let yt, _ = Map.find y vars
                acc
                ++Dup
                +>ld env y
                ++Stfld {
                    fieldType = cliType yt
                    declaringType = closuleType
                    name = Id.L y
                }
            )
            ++Dup
            ++Ldftn(methodRef(Instance, Some resultType, closuleType, Id.L "Invoke", [], argTypes))
            ++Newobj(funcType, [Object; NativeInt])
            ++Stloc x
            ++Ldloc x
            ++Stfld {
                fieldType = funcType
                declaringType = closuleType
                name = Id.L x
            }

        locals := Map.add x t !locals
        g { env with vars = Map.add x (t, Local) vars } e2 acc

    // $(ld x)
    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // callvirt instance !$(ys.length) class [mscorlib]System.Func`…<…>::Invoke(!0, !1, …)
    | Closure.AppCls(x, ys) ->
        let closureType = M.find x vars |> fst
        let argLendth = getFunctionElements closureType |> fst |> List.length

        acc
        +>ld env x
        +>g_loadMany ys env
        ++callvirt(
            false,
            Some <| TypeArgmentIndex argLendth,
            cliType closureType,
            "Invoke",
            List.init argLendth TypeArgmentIndex
        )
        +>addRet isTail

    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // call !0[] $topLevelType::$x
    | Closure.AppDir((Id.L "min_caml_create_array" as x, t), ys) ->
        let elementType = getFunctionElements t |> snd |> getArrayElement |> cliType
        let et = MethodArgmentIndex 0
        acc
        +>g_loadMany ys env
        ++Call(false, methodRef(Static, Some (Array et), topLevelType, x, [elementType], [Int32; et]))
        +>addRet isTail

    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // call $(typeof(x).result) MinCamlGlobal::$l($(typeof ys.[0]), $(typeof ys.[1]), …)
    | Closure.AppDir((x, t), ys) ->
        let argTypes, resultType = getCliFunctionElements t

        acc
        +>g_loadMany ys env
        ++Call(isTail && x = env.methodName, methodRef(Static, Some resultType, topLevelType, x, [], argTypes))
        +>addRet isTail

    // 組の生成 (caml2html: virtual_tuple)
    | Closure.Tuple xs ->
        // $(ld ys.[0])
        // $(ld ys.[1])
        // ︙
        //
        // newobj instance void class System.Tuple`…<…>::.ctor(…)
        let types = List.map (fun x -> Map.find x vars |> fst |> cliType) xs

        acc
        +>g_loadMany xs env
        ++Newobj(tupleType types, types)
        +>addRet isTail

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
    | Closure.LetTuple(xts, y, e2) ->
        let s = Closure.fv e2
        let tupleType = List.map snd xts |> Type.Tuple |> cliType

        acc+>
        ld env y+>
        many (List.indexed xts) (fun (i, (x, t)) acc ->
            if not <| Set.contains x s then acc else

            locals := Map.add x t !locals

            let methodName = sprintf "get_Item%d" <| i + 1
            acc
            ++Dup
            ++Call(false, methodRef(Instance, Some <| TypeArgmentIndex i, tupleType, Id.L methodName, [], []))
            ++Stloc x
        )

    // 配列の読み出し (caml2html: virtual_get)
    | Closure.Get(x, y) ->
        // $(ld x)
        // $(ld y)
        // $(ldelem (elementTypeOf x))

        let elementType =
            match M.find x vars |> fst with
            | Type.Array t -> t
            | _ -> assert_false()

        acc+>ld env x+>ld env y++Ldelem elementType+>addRet isTail

    | Closure.Put(x, y, z) ->
        // $(ld x)
        // $(ld y)
        // $(ld z)
        // $(stelem (elementTypeOf x))

        let elementType =
            match M.find x vars |> fst with
            | Type.Array t -> t
            | _ -> assert_false()

        acc+>ld env x+>ld env y+>ld env z++Stelem elementType

    // .field public static int32[] $x
    //
    // ldsfld $et[] $topLevelType::$x
    | Closure.ExtArray(Id.L x, et) ->
        let n = Id.L <| "min_caml_" + x
        acc++Ldsfld { fieldType = Array(cliType et); declaringType = topLevelType; name = n }

    | x -> failwithf "unknown expression %A" x

and g_loadMany xs env acc = many xs (ld env) acc
and g_branchRelationTail ({ isTail = isTail } as env) (op, e1, e2) acc =
    let ifTrue = Id.L <| Id.genid "iftrue"
    let acc = acc++op ifTrue+>g env e2
    if isTail then
        // ldxxx $x
        // ldxxx $y
        // $op 'iftrue'
        //     $e2
        //
        // 'iftrue':
        //     $e1
        //
        acc++Label ifTrue+>g env e1

    else
        // ldxxx $x
        // ldxxx $y
        // $op 'iftrue'
        //     $e2
        //     br 'endif'
        //
        // 'iftrue':
        //     $e1
        //
        // 'endif':
        
        let endIf = Id.L <| Id.genid "endif"
        acc++Br endIf++Label ifTrue+>g env e1++Label endIf

and g_branchRelation ({ vars = vars; isTail = isTail } as env) (op, x, y, e1, e2) acc =
    match M.find x vars |> fst with
    | Type.Bool
    | Type.Int
    | Type.Float -> acc+>ld env x+>ld env y+>g_branchRelationTail env (op, e1, e2)
    | _ -> failwith "operation supported only for bool, int, and float"

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

let methodDef access callconv resultType (Id.L name' as name) args formalFvs isEntrypoint e =
    let funcType = Type.Fun(List.map snd args, resultType)

    let env = List.fold (fun env (y, t) -> Map.add y (t, Arg) env) Map.empty args
    let env = List.fold (fun env (z, t) -> Map.add z (t, InstanceField) env) env formalFvs

    let env =
        let location =
            match callconv with
            | Instance -> InstanceField
            | Static -> StaticMethodSelf

        Map.add name' (funcType, location) env

    let locals = ref Map.empty
    let opcodes = g { vars = env; isTail = true; locals = locals; methodName = name } e [] |> List.rev
    let body = {
        isEntrypoint = isEntrypoint
        locals = !locals
        opcodes = opcodes
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

let compilerGeneratedAttributeType = TypeName(type_kind.Class, ["mscorlib"], ["System";"Runtime";"CompilerServices"], [], "CompilerGeneratedAttribute", [])
let compilerGenerated = {
    ctor = ctorRef(compilerGeneratedAttributeType, [])
    args = []
    namedArgs = []
}

let defaultCtor =
    let body = {
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
let closureClass { Closure.name = x, t; Closure.args = yts; Closure.formal_fv = zts; Closure.body = e } =
    let funcType = cliType t
    let resultType = getFunctionElements t |> snd
    let acc =
        []
        ++Custom compilerGenerated
        ++Field { access = Public; fieldType = funcType; name = x }
        +>many zts (fun (z, y) acc ->
            acc++Field { access = Public; fieldType = cliType y; name = Id.L z }
        )
        ++Method(methodDef Public Instance resultType (Id.L "Invoke") yts zts false e)
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
let staticMethod { Closure.name = x, t; Closure.args = yts; Closure.body = e } =
    let resultType = getFunctionElements t |> snd
    methodDef Public Static resultType x yts [] false e

/// 関数の仮想マシンコード生成 (caml2html: virtual_h)
let h = function
    | { Closure.formal_fv = [] } as f -> Method <| staticMethod f
    | f -> NestedClass <| closureClass f

/// プログラム全体の仮想マシンコード生成 (caml2html: virtual_f)
let f (Closure.Prog(fundefs, e)) =
    let fundefs = List.map h fundefs
    Prog(
        fundefs,
        methodDef Public Static Type.Unit entrypointName [] [] false e
    )
