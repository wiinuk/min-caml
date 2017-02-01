/// translation into assembly with infinite number of virtual registers
module Virtual

open Asm

type location =
    | Local
    | Arg
    | InstanceField
    | This

let topLevelTypeName = "MinCamlModule"
let topLevelType = TypeName(Class, [], [], [], topLevelTypeName, [])
let entrypointName = Id.L "MinCamlMain"
let localTypeToCliType (Id.L n) = TypeName(Class, [], [], [topLevelTypeName], n, [])

let emptyBody = {
    isEntrypoint = false
    locals = []
    opcodes = []
}
let rec extarrays_t acc = function
    | Closure.IfEq(_, _, e1, e2)
    | Closure.IfLE(_, _, e1, e2)
    | Closure.Let(_, e1, e2) -> extarrays_t (extarrays_t acc e1) e2
    | Closure.MakeCls(_, _, e2)
    | Closure.LetTuple(_, _, e2) -> extarrays_t acc e2
    | Closure.ExtArray(Id.L x, et) ->
        let name = Id.L <| "get_min_caml_" + x
        let methoddef = {
            access = Public
            callconv = Static
            resultType = Type.Array et
            name = name
            args = []
            isForwardref = true
            body = emptyBody
        }
        Map.add name methoddef acc

    | _ -> acc

let extarrays_f acc { Closure.body = e } = extarrays_t acc e

let (++) xs x = x::xs
let (+>) x f = f x

let ld env id acc =
    let t, location = Map.find id env
    match location with
    | Local -> acc++Ldloc id
    | Arg -> acc++Ldarg id
    | This -> acc++Ldloc_0
    | InstanceField ->
        acc
        ++Ldloc_0
        ++Ldfld { fieldType = cliType t; declaringType = cli_type.This; name = Id.L id }

let many xs f acc = List.fold f acc xs

let rec g env locals acc = function (* 式の仮想マシンコード生成 (caml2html: virtual_g) *)
    | Closure.Unit -> acc++Ldnull
    | Closure.Int i -> acc++Ldc_I4 i
    | Closure.Float d -> acc++Ldc_R8 d
    | Closure.Neg x
    | Closure.FNeg x -> acc+>ld env x++Neg
    | Closure.Add(x, y)
    | Closure.FAdd(x, y) -> g_binary env acc Add (x, y)
    | Closure.Sub(x, y)
    | Closure.FSub(x, y) -> g_binary env acc Sub (x, y)
    | Closure.FMul(x, y) -> g_binary env acc Mul (x, y)
    | Closure.FDiv(x, y) -> g_binary env acc Div (x, y)
    | Closure.IfEq(x, y, e1, e2) -> g_branchRelation env locals acc Beq (x, y, e1, e2)
    | Closure.IfLE(x, y, e1, e2) -> g_branchRelation env locals acc Ble (x, y, e1, e2)

    // $e1
    // stloc $x
    // $e2
    | Closure.Let((x, t1), e1, e2) ->
        let acc = g env locals acc e1++Stloc x
        locals := (x, t1)::!locals
        g (M.add x (t1, Local) env) locals acc e2

    | Closure.Var x -> acc+>ld env x

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
            ++ldftn(resultType, closuleType, "Invoke", argTypes)
            ++Newobj(funcType, [Object; NativeInt])
            ++Stloc x
            ++Ldloc x
            ++Stfld {
                fieldType = funcType
                declaringType = closuleType
                name = Id.L x
            }
            +>many ys (fun acc y ->
                let yt, _ = Map.find y env
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
        g (Map.add x (t, Local) env) locals acc e2

    // $(ld x)
    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // callvirt instance !$(ys.length) class [mscorlib]System.Func`…<…>::Invoke(!0, !1, …)
    | Closure.AppCls(x, ys) ->
        let closureType = M.find x env |> fst
        let argLendth =
            match closureType with
            | Type.Fun(xs, _) -> List.length xs
            | _ -> assert_false()

        acc
        +>ld env x
        +>g_loadMany ys env
        ++callvirt(
            TypeArgmentIndex argLendth,
            cliType closureType,
            "Invoke",
            List.init argLendth TypeArgmentIndex
        )

    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // call $(typeof(x).result) MinCamlModule::$l($(typeof ys.[0]), $(typeof ys.[1]), …)
    | Closure.AppDir(Id.L x as x', ys) ->
        let argTypes, resultType =
            match M.find x env |> fst with
            | Type.Fun(argTypes, resultType) -> List.map cliType argTypes, cliType resultType
            | _ -> assert_false()

        acc
        +>g_loadMany ys env
        ++Call(methodRef(Static, resultType, topLevelType, MethodName x', argTypes))

    // 組の生成 (caml2html: virtual_tuple)
    | Closure.Tuple xs ->
        // $(ld ys.[0])
        // $(ld ys.[1])
        // ︙
        //
        // newobj instance void class System.Tuple`…<…>::.ctor(…)
        let types = List.map (fun x -> Map.find x env |> fst |> cliType) xs

        acc
        +>g_loadMany xs env
        ++Newobj(tupleType types, types)

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
            ++Call(methodRef(Instance, TypeArgmentIndex i, tupleType, MethodName(Id.L methodName), []))
            ++Stloc x
        )

    // 配列の読み出し (caml2html: virtual_get)
    | Closure.Get(x, y) ->
        // $(ld x)
        // $(ld y)
        // $(ldelem (elementTypeOf x))

        let elementType =
            match M.find x env |> fst with
            | Type.Array t -> t
            | _ -> assert_false()

        acc+>ld env x+>ld env y++Ldelem elementType

    | Closure.Put(x, y, z) ->
        // $(ld x)
        // $(ld y)
        // $(ld z)
        // $(stelem (elementTypeOf x))

        let elementType =
            match M.find x env |> fst with
            | Type.Array t -> t
            | _ -> assert_false()

        acc+>ld env x+>ld env y+>ld env z++Stelem elementType

    // .method public hidebysig static int32[] get_$x () cil managed forwardref {}
    //
    // call $et[] $topLevelType::get_min_caml_$x()
    | Closure.ExtArray(Id.L x, et) ->
        let n = MethodName(Id.L <| "get_min_caml_" + x)
        acc++Call(methodRef(Static, Array(cliType et), topLevelType, n, []))

and g_loadMany xs env acc = many xs (fun acc x -> ld env x acc) acc
and g_binary env acc op (x, y) = acc+>ld env x+>ld env y++op
and g_branchRelation env locals acc op (x, y, e1, e2) =
    match M.find x env |> fst with
    | Type.Bool
    | Type.Int
    | Type.Float ->
        // ldxxx $x
        // ldxxx $y
        // $op 'iftrue'
        //     $e2
        // 'iftrue':
        //     $e1
        
        let branchTerget = Id.L <| Id.genid "iftrue"
        let acc = acc+>ld env x+>ld env y++op branchTerget
        let acc = g env locals acc e2
        g env locals (Label branchTerget::acc) e1

    | _ -> failwith "operation supported only for bool, int, and float"

let methodDef access callconv resultType (Id.L name' as name) args formalFvs isEntrypoint e =
    let funcType = Type.Fun(List.map snd args, resultType)

    let env = List.fold (fun env (y, t) -> Map.add y (t, Arg) env) Map.empty args
    let env = List.fold (fun env (z, t) -> Map.add z (t, InstanceField) env) env formalFvs
    let env = Map.add name' (funcType, InstanceField) env

    let locals = ref []
    let opcodes = Ret::g env locals [] e
    let body = {
        isEntrypoint = isEntrypoint
        locals = List.rev !locals
        opcodes = List.rev opcodes
    }
    {
        access = access
        callconv = callconv
        resultType = resultType
        name = name
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
// }

let compilerGeneratedAttributeType = TypeName(type_kind.Class, ["mscorlib"], ["System";"Runtime";"CompilerServices"], [], "CompilerGeneratedAttribute", [])
let compilerGenerated = {
    ctor = methodRef(Instance, Void, compilerGeneratedAttributeType, Ctor, [])
    args = []
    namedArgs = []
}

let h_closureClass { Closure.name = x, t; Closure.args = yts; Closure.formal_fv = zts; Closure.body = e } =
    let funcType = cliType t
    let resultType = match t with Type.Fun(_, t) -> t | _ -> assert_false()
    let acc =
        []
        ++Custom compilerGenerated
        ++Field { access = Public; fieldType = funcType; name = x }
        +>many zts (fun acc (z, y) -> Field { access = Public; fieldType = cliType y; name = Id.L z }::acc)
        ++Method (methodDef Public Instance resultType (Id.L "Invoke") yts zts false e)
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
    let extarrays =
        List.fold extarrays_f Map.empty fundefs
        |> Map.toList
        |> List.map (snd >> Method)

    let fundefs = List.map h fundefs

    Prog(
        extarrays @ fundefs,
        methodDef Public Static Type.Unit entrypointName [] [] true e
    )
