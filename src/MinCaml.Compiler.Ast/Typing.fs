(* type inference/reconstruction *)
module MinCaml.Compiler.Ast.Typing
open Syntax

exception Unify of Type.t * Type.t
exception Error of t * Type.t * Type.t

// TODO: internal
let extenv = ref Map.empty

// for pretty printing (and type normalization)
/// 型変数を中身でおきかえる関数
let rec derefTyp = function
    | Type.Fun(t1s, t2) -> Type.Fun(List.map derefTyp t1s, derefTyp t2)
    | Type.Tuple ts -> Type.Tuple(List.map derefTyp ts)
    | Type.Array t -> Type.Array(derefTyp t)
    | Type.Var({ contents = None } as r) ->
        eprintf "uninstantiated type variable detected; assuming int@."
        r := Some Type.Int
        Type.Int

    | Type.Var({ contents = Some(t) } as r) ->
        let t' = derefTyp t
        r := Some(t')
        t'

    | t -> t

let rec derefIdTyp (x, t) = (x, derefTyp t)
let rec derefTerm = function
    | Not(e) -> Not(derefTerm e)
    | Neg(e) -> Neg(derefTerm e)
    | Add(e1, e2) -> Add(derefTerm e1, derefTerm e2)
    | Sub(e1, e2) -> Sub(derefTerm e1, derefTerm e2)
    | Eq(e1, e2) -> Eq(derefTerm e1, derefTerm e2)
    | LE(e1, e2) -> LE(derefTerm e1, derefTerm e2)
    | FNeg(e) -> FNeg(derefTerm e)
    | FAdd(e1, e2) -> FAdd(derefTerm e1, derefTerm e2)
    | FSub(e1, e2) -> FSub(derefTerm e1, derefTerm e2)
    | FMul(e1, e2) -> FMul(derefTerm e1, derefTerm e2)
    | FDiv(e1, e2) -> FDiv(derefTerm e1, derefTerm e2)
    | If(e1, e2, e3) -> If(derefTerm e1, derefTerm e2, derefTerm e3)
    | Let(xt, e1, e2) -> Let(derefIdTyp xt, derefTerm e1, derefTerm e2)
    | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
        let f = {
            name = derefIdTyp xt
            args = List.map derefIdTyp yts
            body = derefTerm e1
        }
        LetRec(f, derefTerm e2)

    | App(e, es) -> App(derefTerm e, List.map derefTerm es)
    | Tuple es -> Tuple(List.map derefTerm es)
    | LetTuple(xts, e1, e2) -> LetTuple(List.map derefIdTyp xts, derefTerm e1, derefTerm e2)
    | Array(e1, e2) -> Array(derefTerm e1, derefTerm e2)
    | Get(e1, e2) -> Get(derefTerm e1, derefTerm e2)
    | Put(e1, e2, e3) -> Put(derefTerm e1, derefTerm e2, derefTerm e3)
    | e -> e

/// occur check
let rec occur r1 = function
    | Type.Fun(t2s, t2) -> List.exists (occur r1) t2s || occur r1 t2
    | Type.Tuple t2s -> List.exists (occur r1) t2s
    | Type.Array t2 -> occur r1 t2
    | Type.Var r2 when r1 == r2 -> true
    | Type.Var { contents = None } -> false
    | Type.Var { contents = Some t2 } -> occur r1 t2
    | _ -> false

/// 型が合うように、型変数への代入をする
let rec unify t1 t2 =
    match t1, t2 with
    | Type.Unit, Type.Unit | Type.Bool, Type.Bool | Type.Int, Type.Int | Type.Float, Type.Float -> ()
    | Type.Fun(t1s, t1'), Type.Fun(t2s, t2') ->
        try List.iter2 unify t1s t2s
        with :? System.ArgumentException -> raise <| Unify(t1, t2)
        unify t1' t2'

    | Type.Tuple t1s, Type.Tuple t2s ->
        try List.iter2 unify t1s t2s
        with :? System.ArgumentException -> raise <| Unify(t1, t2)

    | Type.Array t1, Type.Array t2 -> unify t1 t2
    | Type.Var r1, Type.Var r2 when r1 == r2 -> ()
    | Type.Var { contents = Some t1' }, _ -> unify t1' t2
    | _, Type.Var { contents = Some t2' } -> unify t1 t2'

    // 一方が未定義の型変数の場合
    | Type.Var({ contents = None } as r1), _ ->
        if occur r1 t2 then raise <| Unify(t1, t2)
        r1 := Some t2

    | _, Type.Var({ contents = None } as r2) ->
        if occur r2 t1 then raise <| Unify(t1, t2)
        r2 := Some t1

    | _ -> raise <| Unify(t1, t2)

/// 型推論ルーチン
let rec g env e =
    try
        match e with
        | Unit -> Type.Unit
        | Bool _ -> Type.Bool
        | Int _ -> Type.Int
        | Float _ -> Type.Float
        | Not e -> unify Type.Bool (g env e); Type.Bool
        | Neg e -> unify Type.Int (g env e); Type.Int

        // 足し算（と引き算）の型推論
        | Add(e1, e2) | Sub(e1, e2) ->
            unify Type.Int (g env e1)
            unify Type.Int (g env e2)
            Type.Int

        | FNeg e ->
            unify Type.Float (g env e)
            Type.Float

        | FAdd(e1, e2) | FSub(e1, e2) | FMul(e1, e2) | FDiv(e1, e2) ->
            unify Type.Float (g env e1)
            unify Type.Float (g env e2)
            Type.Float

        | Eq(e1, e2) | LE(e1, e2) ->
            unify (g env e1) (g env e2)
            Type.Bool

        | If(e1, e2, e3) ->
            unify (g env e1) Type.Bool
            let t2 = g env e2
            let t3 = g env e3
            unify t2 t3
            t2

        // letの型推論
        | Let((x, t), e1, e2) ->
            unify t (g env e1)
            g (Map.add x t env) e2

        // 変数の型推論
        | Var x when Map.containsKey x env -> Map.find x env
        | Var x when Map.containsKey x !extenv -> Map.find x !extenv

        // 外部変数の型推論
        | Var x ->
            eprintf "free variable %s assumed as external@." x
            let t = Type.gentyp ()
            extenv := Map.add x t !extenv
            t

        // let recの型推論
        | LetRec({ name = x, t; args = yts; body = e1 }, e2) ->
            let env = Map.add x t env
            unify t <| Type.Fun(List.map snd yts, g (Map.addList yts env) e1)
            g env e2

        // 関数適用の型推論
        | App(e, es) ->
            let t = Type.gentyp ()
            unify (g env e) <| Type.Fun(List.map (g env) es, t)
            t

        | Tuple es -> Type.Tuple <| List.map (g env) es
        | LetTuple(xts, e1, e2) ->
            unify (Type.Tuple(List.map snd xts)) <| g env e1
            g (Map.addList xts env) e2

        // must be a primitive for "polymorphic" typing
        | Array(e1, e2) ->
            unify (g env e1) Type.Int
            Type.Array <| g env e2

        | Get(e1, e2) ->
            let t = Type.gentyp()
            unify (Type.Array t) <| g env e1
            unify Type.Int <| g env e2
            t

        | Put(e1, e2, e3) ->
            let t = g env e3
            unify (Type.Array t) <| g env e1
            unify Type.Int <| g env e2
            Type.Unit

    with
    | Unify(t1, t2) -> raise <| Error(derefTerm e, derefTyp t1, derefTyp t2)

let f e =
    extenv := Map.empty
    try unify Type.Unit <| g Map.empty e
    with Unify _ -> failwith "top level does not have type unit"
    extenv := Map.mapValue derefTyp !extenv
    derefTerm e
