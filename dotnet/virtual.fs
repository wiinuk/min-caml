/// translation into assembly with infinite number of virtual registers
module Virtual

open Asm

type location =
    | Local
    | Arg
    | InstanceField
    | This

type env = {
    vars: Map<Id.t, Type.t * location>
    isTail: bool
    methodName: Id.l
    locals: (Id.t * Type.t) list ref
}

let topLevelTypeName = "MinCamlGlobal"
let topLevelType = TypeName(Class, [], [], [], topLevelTypeName, [])
let entrypointName = Id.L "MinCamlEntryPoint"
let localTypeToCliType (Id.L n) = TypeName(Class, [], [], [topLevelTypeName], n, [])

let emptyBody = {
    isEntrypoint = false
    locals = []
    opcodes = [Ret]
}

let (++) xs x = x::xs
let (+>) x f = f x

let ld { vars = env } id acc =
    let t, location = Map.find id env
    match location with
    | Local -> acc++Ldloc id
    | Arg -> acc++Ldarg id
    | This -> acc++Ldarg_0
    | InstanceField ->
        acc
        ++Ldarg_0
        ++Ldfld { fieldType = cliType t; declaringType = cli_type.This; name = Id.L id }

let many xs f acc = List.fold f acc xs

let addRet isTail acc = if isTail then acc++Ret else acc

/// 式の仮想マシンコード生成 (caml2html: virtual_g)
let rec g ({ isTail = isTail; locals = locals; vars = vars } as env) acc = function
    | Closure.Unit -> acc++Ldnull+>addRet isTail
    | Closure.Int i -> acc++Ldc_I4 i+>addRet isTail
    | Closure.Float d -> acc++Ldc_R8 d+>addRet isTail
    | Closure.Neg x
    | Closure.FNeg x -> acc+>ld env x++Neg+>addRet isTail
    | Closure.Add(x, y)
    | Closure.FAdd(x, y) -> g_binary env isTail acc Add (x, y)
    | Closure.Sub(x, y)
    | Closure.FSub(x, y) -> g_binary env isTail acc Sub (x, y)
    | Closure.FMul(x, y) -> g_binary env isTail acc Mul (x, y)
    | Closure.FDiv(x, y) -> g_binary env isTail acc Div (x, y)
    | Closure.IfEq(x, y, e1, e2) -> g_branchRelation env acc Beq (x, y, e1, e2)
    | Closure.IfLE(x, y, e1, e2) -> g_branchRelation env acc Ble (x, y, e1, e2)

    | Closure.Var x -> acc+>ld env x+>addRet isTail

    // $e1
    // stloc $x
    // $e2
    | Closure.Let((x, t1), e1, e2) ->
        let acc = g { env with isTail = false } acc e1++Stloc x
        locals := (x, t1)::!locals
        g { env with vars = M.add x (t1, Local) vars } acc e2

    // クロージャの生成 (caml2html: virtual_makecls)
    | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = ys }, e2) ->
        // [mincaml|let $x : $($ts -> $r) = let rec $l … = … $ys … in $e2|] ->
        //
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
        // var $x = new Func<…>(@temp_x.Invoke);
        // @temp_x.$x = $x;
        //
        // @temp_x.$(ys.[0]) = $(ys.[0]);
        // @temp_x.$(ys.[1]) = $(ys.[1]);
        // ︙
        //
        // $e2
        // |] ->
        //
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
        // ldftn instance $r $l::Invoke($(ts.[0]), $(ts.[1]), …)
        // newobj instance void class [mscorlib]System.Func`…<$(ts.[0]), $(ts.[1]), …, $r>::.ctor(object, native int)
        // stloc $x
        // ldloc $x
        // stfld class [mscorlib]System.Func`…<$(ts.[0]), $(ts.[1]), …, $r> $l::$x
        //
        // dup
        //     $(ld ys.[0])
        //     stfld $(typeof ys.[0]) $l::$(ys.[0])
        // dup
        //     $(ld ys.[1])
        //     stfld $(typeof ys.[1]) $l::$(ys.[1])
        // ︙
        //
        //
        // $e2
        // |]

        let argTypes, resultType =
            match t with
            | Type.Fun(ts, r) -> List.map cliType ts, cliType r
            | _ -> assert_false()

        let funcType = cliType t
        let closuleType = localTypeToCliType l
        let acc =
            acc
            ++Newobj(closuleType, [])
            ++ldftn(Some resultType, closuleType, "Invoke", argTypes)
            ++Newobj(funcType, [Object; NativeInt])
            ++Stloc x
            ++Ldloc x
            ++Stfld {
                fieldType = funcType
                declaringType = closuleType
                name = Id.L x
            }
            +>many ys (fun acc y ->
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

        locals := (x, t)::!locals
        g { env with vars = Map.add x (t, Local) vars } acc e2

    // $(ld x)
    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // callvirt instance !$(ys.length) class [mscorlib]System.Func`…<…>::Invoke(!0, !1, …)
    | Closure.AppCls(x, ys) ->
        let closureType = M.find x vars |> fst
        let argLendth =
            match closureType with
            | Type.Fun(xs, _) -> List.length xs
            | _ -> assert_false()

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
    // call $(typeof(x).result) MinCamlGlobal::$l($(typeof ys.[0]), $(typeof ys.[1]), …)
    | Closure.AppDir((x, t), ys) ->
        let argTypes, resultType =
            match t with
            | Type.Fun(argTypes, resultType) -> List.map cliType argTypes, cliType resultType
            | _ -> assert_false()

        acc
        +>g_loadMany ys env
        ++Call(isTail && x = env.methodName, methodRef(Static, Some resultType, topLevelType, x, argTypes))
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
        many (List.indexed xts) (fun acc (i, (x, t)) ->
            if not <| Set.contains x s then acc else

            locals := (x, t)::!locals

            let methodName = sprintf "get_Item%d" <| i + 1
            acc
            ++Dup
            ++Call(false, methodRef(Instance, Some <| TypeArgmentIndex i, tupleType, Id.L methodName, []))
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

and g_loadMany xs env acc = many xs (fun acc x -> ld env x acc) acc
and g_binary env isTail acc op (x, y) = acc+>ld env x+>ld env y++op+>addRet isTail
and g_branchRelation ({ vars = vars; isTail = isTail } as env) acc op (x, y, e1, e2) =
    match M.find x vars |> fst with
    | Type.Bool
    | Type.Int
    | Type.Float ->
        let ifTrue = Id.L <| Id.genid "iftrue"
        let acc = acc+>ld env x+>ld env y++op ifTrue
        let acc = g env acc e2

        if isTail then
            // ldxxx $x
            // ldxxx $y
            // $op 'iftrue'
            //     $e2
            //
            // 'iftrue':
            //     $e1
            //
            let acc = acc++Label ifTrue
            g env acc e1
            
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
            let acc = acc++Br endIf++Label ifTrue
            g env acc e1++Label endIf

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
    let env = Map.add name' (funcType, InstanceField) env

    let locals = ref []
    let opcodes = g { vars = env; isTail = true; locals = locals; methodName = name } [] e
    let body = {
        isEntrypoint = isEntrypoint
        locals = List.rev !locals
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
let h_method { Closure.name = x, t; Closure.args = yts; Closure.body = e } =
    let resultType = match t with Type.Fun(_, t) -> t | _ -> assert_false()
    methodDef Public Static resultType x yts [] false e


let compilerGeneratedAttributeType = TypeName(type_kind.Class, ["mscorlib"], ["System";"Runtime";"CompilerServices"], [], "CompilerGeneratedAttribute", [])
let compilerGenerated = {
    ctor = ctorRef(compilerGeneratedAttributeType, [])
    args = []
    namedArgs = []
}

let defaultCtor =
    let body = {
        isEntrypoint = false
        locals = []
        opcodes =
        [
            Ldarg_0
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
let h_closureClass { Closure.name = x, t; Closure.args = yts; Closure.formal_fv = zts; Closure.body = e } =
    let funcType = cliType t
    let resultType = match t with Type.Fun(_, t) -> t | _ -> assert_false()
    let acc =
        []
        ++Custom compilerGenerated
        ++Field { access = Public; fieldType = funcType; name = x }
        +>many zts (fun acc (z, y) ->
            Field { access = Public; fieldType = cliType y; name = Id.L z }::acc
        )
        ++Method(methodDef Public Instance resultType (Id.L "Invoke") yts zts false e)
        ++Method defaultCtor
    {
        isSealed = true
        isBeforefieldinit = true
        name = x
        body = List.rev acc
    }

/// 関数の仮想マシンコード生成 (caml2html: virtual_h)
let h = function
    | { Closure.formal_fv = [] } as f -> Method <| h_method f
    | f -> NestedClass <| h_closureClass f

/// プログラム全体の仮想マシンコード生成 (caml2html: virtual_f)
let f (Closure.Prog(fundefs, e)) =
    let fundefs = List.map h fundefs
    Prog(
        fundefs,
        methodDef Public Static Type.Unit entrypointName [] [] false e
    )
