/// translation into assembly with infinite number of virtual registers
module internal Virtual

open Asm

let classify xts ini addf addi =
  List.fold_left
    (fun acc (x, t) ->
      match t with
      | Type.Unit -> acc
      | Type.Float -> addf acc x
      | _ -> addi acc x t)
    ini
    xts

let separate xts =
  classify
    xts
    ([], [])
    (fun (int, float) x -> (int, float @ [x]))
    (fun (int, float) x _ -> (int @ [x], float))

let expand xts ini addf addi =
  classify
    xts
    ini
    (fun (offset, acc) x ->
      let offset = align offset in
      (offset + 8, addf x offset acc))
    (fun (offset, acc) x t ->
      (offset + 4, addi x t offset acc))

type class_or_value_type = Class | ValueType
type cli_type =

    /// .this
    | This
    /// e.g. !1
    | TypeArgmentIndex of int

    /// sizeof<bool> = 1
    | Bool
    | Int32
    | Float64
    | Object
    | NativeInt
    | Array of cli_type

    /// e.g. class [moduleA]NamespaceA.ClassA/ClassB/Class
    | TypeName of class_or_value_type * moduleName: Id.t option * nameSpace: Id.t list * nestedParents: Id.t list * typeName: Id.t * typeArgs: cli_type list

let topLevelTypeName = "MinCamlModule"
let topLevelType = TypeName(Class, None, [], [], topLevelTypeName, [])
let localTypeToCliType (Id.L n) = TypeName(Class, None, [], [topLevelTypeName], n, [])

let tupleType types =
    let arity = List.length types
    TypeName(Class, Some "mscorlib", ["System"], [], sprintf "Tuple`%d" arity, types)

let unitType = TypeName(Class, Some "mscorlib", ["System"], [], sprintf "DBNull", [])

let rec cliType = function
    | Type.Array t -> Array <| cliType t
    | Type.Unit -> unitType
    | Type.Bool -> Bool
    | Type.Int -> Int32
    | Type.Float -> Float64
    | Type.Fun(argTypes, resultType) -> 
        let arity = List.length argTypes + 1
        let args = List.map cliType argTypes @ [cliType resultType]
        TypeName(Class, Some "mscorlib", ["System"], [], sprintf "Func`%d" arity, args)

    | Type.Tuple ts -> tupleType <| List.map cliType ts

    | Type.Var { contents = Some t } -> cliType t
    | Type.Var { contents = None } -> failwith "unexpected type 'Var'"

type instance_or_static = Instance | Static

type t =
    | Label of Id.l

    | Ldloc_0
    | Ldarg of Id.t
    | Ldloc of Id.t
    | Stloc of Id.t
    | Dup

    | Ldnull
    | Ldc_I4 of int32
    | Ldc_R8 of float

    | Neg
    | Add
    | Sub
    | Mul
    | Div

    | Beq of Id.l
    | Ble of Id.l

    | Call of instance_or_static * cli_type * cli_type * methodName: Id.l * argTypes: Type.t list

    | Ldelem of Type.t
    | Stelem of Type.t

    /// instance void $declaringType::.ctor($argTypes)
    | Newobj of declaringType: cli_type * argTypes: cli_type list
    | Ldfld of fieldType: Type.t * cli_type * fieldName: Id.l
    | Stfld of fieldType: Type.t * cli_type * fieldName: Id.l

    /// callvirt instance $resultType $declaringType::$methodName($argTypes)
    | Callvirt of resultType: cli_type * declaringType: cli_type * methodName: Id.l * argTypes: cli_type list

    | Ldftn of
        instance_or_static *
        resultType: Type.t *
        declaringType: cli_type *
        methodName: Id.l *
        argTypes: Type.t list

type location =
    | Local
    | Arg

    | InstanceField
    | This

let (++) xs x = x::xs
let (+>) x f = f x

let ld env id acc =
    let t, location = Map.find id env
    match location with
    | Local -> acc++Ldloc id
    | Arg -> acc++Ldarg id
    | This -> acc++Ldloc_0
    | InstanceField -> acc++Ldloc_0++Ldfld(t, cli_type.This, Id.L id)

//let rec ldelem = function
//    | Type.Bool -> Ldelem_U1
//    | Type.Int -> Ldelem_I4
//    | Type.Float -> Ldelem_R8
//    | Type.Array _ -> Ldelem_Ref
//    | Type.Fun _ -> Ldelem_Ref
//    | Type.Unit -> Ldelem_Ref
//    | Type.Tuple _ -> Ldelem_Ref
//    | Type.Var { contents = Some t } -> ldelem t
//    | Type.Var { contents = None } -> failwith "unexpected type 'Var'"

let many xs f acc = List.fold f acc xs

let rec g env acc = function (* 式の仮想マシンコード生成 (caml2html: virtual_g) *)
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
    | Closure.IfEq(x, y, e1, e2) -> g_branchRelation env acc Beq (x, y, e1, e2)
    | Closure.IfLE(x, y, e1, e2) -> g_branchRelation env acc Ble (x, y, e1, e2)

    // $e1
    // stloc $x
    // $e2
    | Closure.Let((x, t1), e1, e2) ->
        let acc = g env acc e1++Stloc x
        g (M.add x (t1, Local) env) acc e2

    | Closure.Var x -> acc+>ld env x

    // クロージャの生成 (caml2html: virtual_makecls)
    | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = ys }, e2) ->
        // [mincaml|let $x : $($ts -> $r) = let rec $l ... = ... $ys ... in $e2|] ->
        //
        // [cs|
        // private class $l
        // {
        //     public $(typeof ys.[0]) $(ys[0]);
        //     public $(typeof ys.[1]) $(ys[1]);
        //     ︙
        //
        //     public $r Invoke($(ts.[0]) ..., $(ts.[1]) ..., ...)
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
        // var $x = new Func<...>(@temp_x.Invoke);
        // $e2
        // |] ->
        //
        // [il|
        // class private auto ansi beforefieldinit $l
        // {
        //     .custom instance void [mscorlib]System.Runtime.CompilerServices.CompilerGeneratedAttribute::.ctor() = (01 00 00 00)
        //     .field public $(typeof ys.[0]) $(ys.[0])
        //     .field public $(typeof ys.[1]) $(ys.[1])
        //     ︙
        //
        //     .method assembly hidebysig instance $r Invoke($(ts.[0]) ..., $(ts.[1]) ..., ...) cil managed
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
        // ldftn instance $r $l::Invoke($(ts.[0]), $(ts.[1]), ...)
        // newobj instance void class [mscorlib]System.Func`...<$(ts.[0]), $(ts.[1]), ..., $r>::.ctor(object, native int)
        // stloc $x
        //
        // $e2
        // |]

        let argTypes, resultType =
            match t with
            | Type.Fun(ts, r) -> ts, r
            | _ -> assert_false()

        let closuleType = localTypeToCliType l
        let acc =
            acc++
            Newobj(closuleType, [])+>
            many ys (fun acc y ->
                let yt, _ = Map.find y env
                acc++Dup+>ld env y++Stfld(yt, closuleType, Id.L y)
            )++
            Ldftn(Instance, resultType, closuleType, Id.L "Invoke", argTypes)++
            Newobj(cliType t, [Object; NativeInt])++
            Stloc x

        g (Map.add x (t, Local) env) acc e2

    // $(ld x)
    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // callvirt instance !$(ys.length) class [mscorlib]System.Func`...<...>::Invoke(!0, !1, ...)
    | Closure.AppCls(x, ys) ->
        let closureType = M.find x env |> fst
        let argLendth =
            match closureType with
            | Type.Fun(xs, _) -> List.length xs
            | _ -> assert_false()

        acc+>
        ld env x+>
        g_loadMany ys env++
        Callvirt(
            TypeArgmentIndex argLendth,
            cliType closureType,
            Id.L "Invoke",
            List.init argLendth TypeArgmentIndex
        )

    // $(ld ys.[0])
    // $(ld ys.[1])
    // ︙
    //
    // call $(typeof(x).result) MinCamlModule::$l($(typeof ys.[0]), $(typeof ys.[1]), ...)
    | Closure.AppDir(Id.L x as x', ys) ->
        let argTypes, resultType =
            match M.find x env |> fst with
            | Type.Fun(argTypes, resultType) -> argTypes, resultType
            | _ -> assert_false()

        acc+>
        g_loadMany ys env++
        Call(Static, cliType resultType, topLevelType, x', argTypes)

    // 組の生成 (caml2html: virtual_tuple)
    | Closure.Tuple xs ->
        // $(ld ys.[0])
        // $(ld ys.[1])
        // ︙
        //
        // newobj instance void class System.Tuple`...<...>::.ctor(...)
        let types = List.map (fun x -> Map.find x env |> fst |> cliType) xs

        acc+>
        g_loadMany xs env++
        Newobj(tupleType types, types)

    // $(ld y)
    // dup
    //     call instance !0 class [mscorlib]System.Tuple`...<...>::get_Item...()
    //     stloc $(fst xys.[0])
    // dup
    //     call instance !1 class [mscorlib]System.Tuple`...<...>::get_Item...()
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

            let methodName = sprintf "get_Item%d" <| i + 1
            acc++
            Dup++
            Call(Instance, TypeArgmentIndex i, tupleType, Id.L methodName, [])
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

    | Closure.ExtArray(Id.L(x)) ->
        // ldsfld int32 ConsoleApplication1.Program::a

        Ans(SetL(Id.L("min_caml_" ^ x)))

and g_binary env acc op (x, y) = acc+>ld env x+>ld env y++op
and g_branchRelation env acc op (x, y, e1, e2) =
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
        let acc = g env acc e2
        g env (Label branchTerget::acc) e1

    | _ -> failwith "operation supported only for bool, int, and float"

and g_loadMany xs env acc = many xs (fun acc x -> ld env x acc) acc

//let rec g env = function (* 式の仮想マシンコード生成 (caml2html: virtual_g) *)
//  | Closure.Unit -> Ans(Nop)
//  | Closure.Int(i) -> Ans(Set(i))
//  | Closure.Float(d) -> Ans(SetF(d))
//  | Closure.Neg(x) -> Ans(Neg(x))
//  | Closure.Add(x, y) -> Ans(Add(x, V(y)))
//  | Closure.Sub(x, y) -> Ans(Sub(x, V(y)))
//  | Closure.FNeg(x) -> Ans(FNegD(x))
//  | Closure.FAdd(x, y) -> Ans(FAddD(x, y))
//  | Closure.FSub(x, y) -> Ans(FSubD(x, y))
//  | Closure.FMul(x, y) -> Ans(FMulD(x, y))
//  | Closure.FDiv(x, y) -> Ans(FDivD(x, y))
//  | Closure.IfEq(x, y, e1, e2) ->
//      (match M.find x env with
//      | Type.Bool | Type.Int -> Ans(IfEq(x, V(y), g env e1, g env e2))
//      | Type.Float -> Ans(IfFEq(x, y, g env e1, g env e2))
//      | _ -> failwith "equality supported only for bool, int, and float")
//
//  | Closure.IfLE(x, y, e1, e2) ->
//      (match M.find x env with
//      | Type.Bool | Type.Int -> Ans(IfLE(x, V(y), g env e1, g env e2))
//      | Type.Float -> Ans(IfFLE(x, y, g env e1, g env e2))
//      | _ -> failwith "inequality supported only for bool, int, and float")
//
//  | Closure.Let((x, t1), e1, e2) ->
//      let e1' = g env e1 in
//      let e2' = g (M.add x t1 env) e2 in
//      concat e1' (x, t1) e2'
//
//  | Closure.Var(x) ->
//      (match M.find x env with
//      | Type.Unit -> Ans(Nop)
//      | Type.Float -> Ans(FMovD(x))
//      | _ -> Ans(Mov(x)))
//  | Closure.MakeCls((x, t), { Closure.entry = l; Closure.actual_fv = ys }, e2) -> (* クロージャの生成 (caml2html: virtual_makecls) *)
//      (* Closureのアドレスをセットしてから、自由変数の値をストア *)
//      let e2' = g (M.add x t env) e2 in
//      let offset, store_fv =
//    expand
//      (List.map (fun y -> (y, M.find y env)) ys)
//      (4, e2')
//      (fun y offset store_fv -> seq(StDF(y, x, C(offset), 1), store_fv))
//      (fun y _ offset store_fv -> seq(St(y, x, C(offset), 1), store_fv)) in
//      Let((x, t), Mov(reg_hp),
//      Let((reg_hp, Type.Int), Add(reg_hp, C(align offset)),
//          let z = Id.genid "l" in
//          Let((z, Type.Int), SetL(l),
//          seq(St(z, x, C(0), 1),
//              store_fv))))
//  | Closure.AppCls(x, ys) ->
//      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
//      Ans(CallCls(x, int, float))
//  | Closure.AppDir(Id.L(x), ys) ->
//      let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
//      Ans(CallDir(Id.L(x), int, float))
//  | Closure.Tuple(xs) -> (* 組の生成 (caml2html: virtual_tuple) *)
//      let y = Id.genid "t" in
//      let (offset, store) =
//    expand
//      (List.map (fun x -> (x, M.find x env)) xs)
//      (0, Ans(Mov(y)))
//      (fun x offset store -> seq(StDF(x, y, C(offset), 1), store))
//      (fun x _ offset store -> seq(St(x, y, C(offset), 1), store)) in
//      Let((y, Type.Tuple(List.map (fun x -> M.find x env) xs)), Mov(reg_hp),
//      Let((reg_hp, Type.Int), Add(reg_hp, C(align offset)),
//          store))
//  | Closure.LetTuple(xts, y, e2) ->
//      let s = Closure.fv e2 in
//      let (offset, load) =
//    expand
//      xts
//      (0, g (M.add_list xts env) e2)
//      (fun x offset load ->
//        if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
//        fletd(x, LdDF(y, C(offset), 1), load))
//      (fun x t offset load ->
//        if not (S.mem x s) then load else (* [XX] a little ad hoc optimization *)
//        Let((x, t), Ld(y, C(offset), 1), load)) in
//      load
//  | Closure.Get(x, y) -> (* 配列の読み出し (caml2html: virtual_get) *)
//      (match M.find x env with
//      | Type.Array(Type.Unit) -> Ans(Nop)
//      | Type.Array(Type.Float) -> Ans(LdDF(x, V(y), 8))
//      | Type.Array(_) -> Ans(Ld(x, V(y), 4))
//      | _ -> assert_false())
//  | Closure.Put(x, y, z) ->
//      (match M.find x env with
//      | Type.Array(Type.Unit) -> Ans(Nop)
//      | Type.Array(Type.Float) -> Ans(StDF(z, x, V(y), 8))
//      | Type.Array(_) -> Ans(St(z, x, V(y), 4))
//      | _ -> assert_false())
//  | Closure.ExtArray(Id.L(x)) -> Ans(SetL(Id.L("min_caml_" ^ x)))

(* 関数の仮想マシンコード生成 (caml2html: virtual_h) *)
let h { Closure.name = (Id.L(x), t); Closure.args = yts; Closure.formal_fv = zts; Closure.body = e } =
  let (int, float) = separate yts in
  let (offset, load) =
    expand
      zts
      (4, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
      (fun z offset load -> fletd(z, LdDF(x, C(offset), 1), load))
      (fun z t offset load -> Let((z, t), Ld(x, C(offset), 1), load)) in
  match t with
  | Type.Fun(_, t2) ->
      { name = Id.L(x); args = yts; body = load; ret = t2 }
  | _ -> assert_false()

(* プログラム全体の仮想マシンコード生成 (caml2html: virtual_f) *)
let f (Closure.Prog(fundefs, e)) =
  let fundefs = List.map h fundefs in
  let e = g M.empty e in
  Prog(fundefs, e)
