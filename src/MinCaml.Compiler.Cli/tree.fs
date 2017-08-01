[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "TypeNamesMustBePascalCase")>]
[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "IdentifiersMustNotContainUnderscores")>]

/// SSA 形式から、スタック形式の CIL コードに変換しやすい式木への変換
module MinCaml.Compiler.Cli.Tree
open MinCaml.Compiler.Ast

module P = Closure

type unary = | Neg
type binary =
    | Add
    | Sub
    | Mul
    | Div

type condition =
    | Eq
    | Le

type closure = {
    entry: Id.l
    /// field = expr, ...
    actual_fv: (Id.l * t) list
}

and t =
    | Unit
    | Int of int
    | Float of float
    | Unary of unary * t
    | Binary of t * binary * t
    | Condition of t * condition * t * t * t
    | Let of (Id.t * Type.t) * t * t
    | Seq of t * t
    | Var of Id.t
    | Cls of functionType: Type.t * closure
    | LetCls of (Id.t * Type.t) * closure * t
    | AppCls of t * t list
    | AppDir of (Id.l * (* function type *) Type.t) * t list
    | Tuple of t list
    | LetTuple of (Id.t * Type.t) list * t * t
    | Get of t * t
    | Put of t * t * t
    | ExtArray of Id.l * elementType: Type.t

type fundef = {
    name: Id.l * Type.t
    args: (Id.t * Type.t) list
    useSelf: bool
    formalFreeVars: (Id.t * Type.t) list
    body: t
}
type prog = Prog of fundef list * t

let private resultType e = function
    | Type.Fun(_, t) -> t
    | _ -> failwithf "type inference error: %A" e

type map<'k,'v,'m> = {
    /// <exception cref="T:System.Collections.Generic.KeyNotFoundException" />
    find: 'k -> 'm -> 'v
    add: 'k -> 'v -> 'm -> 'm
}

let rec typeof map env = function
    | Unit
    | Put _ -> Type.Unit
    | Int _ -> Type.Int
    | Float _ -> Type.Float
    | Tuple es -> List.map (typeof map env) es |> Type.Tuple

    | Unary(_, e)
    | Binary(e, _, _)
    | Seq(_, e)
    | Condition(_, _, _, e, _) -> typeof map env e

    | Get(e, _) ->
        match typeof map env e with
        | Type.Array t -> t
        | _ -> failwithf "type inference error: %A" e

    | Var x ->
        try map.find x env
        with :? System.Collections.Generic.KeyNotFoundException ->
            failwithf "key not found: %A, env: %A" x env

    | Let((x, t), _, e)
    | LetCls((x, t), _, e) -> typeof map (map.add x t env) e
    | Cls(t, _) -> t

    | AppCls(e, _) as e' -> resultType e' <| typeof map env e
    | AppDir((_, t), _) as e' -> resultType e' t

    | LetTuple(xts, _, e) -> typeof map (List.fold (fun env (x, t) -> map.add x t env) env xts) e
    | ExtArray(_, et) -> Type.Array et

let (-.) xs x = Set.remove x xs

let rec freeVars = function
    | Unit | Int _ | Float _ | ExtArray _ -> Set.empty
    | Var x -> Set.singleton x

    | Unary(_, e) -> freeVars e
    | Binary(e1, _, e2)
    | Get(e1, e2)
    | Seq(e1, e2) -> freeVars e1 + freeVars e2
    | Put(e1, e2, e3) -> freeVars e1 + freeVars e2 + freeVars e3
    | AppCls(e, es) -> freeVars e + Set.unionMany (Seq.map freeVars es)
    | Condition(e1, _, e2, e3, e4) -> freeVars e1 + freeVars e2 + freeVars e3 + freeVars e4
    | AppDir(_, es)
    | Tuple es -> Seq.map freeVars es |> Set.unionMany

    | Let((x, _), e1, scope) -> freeVars scope -. x + freeVars e1
    | LetCls((x, _), { actual_fv = vs }, e) -> Set.unionMany (Seq.map (snd >> freeVars) vs) + freeVars e -. x
    | Cls(_, { actual_fv = vs }) -> Set.unionMany (Seq.map (snd >> freeVars) vs)
    | LetTuple(xts, e, scope) -> freeVars scope - Set.ofSeq (Seq.map fst xts) + freeVars e

let notContains k e = not (Set.contains k (P.fv e))
let notContains2 k1 k2 e1 e2 =
    let xs1 = P.fv e1
    not (Set.contains k1 xs1) &&
    not (Set.contains k2 xs1) &&

    let xs2 = P.fv e2
    not (Set.contains k1 xs2) &&
    not (Set.contains k2 xs2)

let takeLets e =
    let rec takeLetsRev xtes = function
        | P.Let((x, t), e, k) when List.forall (fun (x, _, _) -> notContains x e) xtes ->
            takeLetsRev ((x, t, e)::xtes) k

        | e -> List.rev xtes, e

    takeLetsRev [] e

let addVars xts env = List.fold (fun env (x, t) -> Map.add x t env) env xts

let private arrayElementType = function
    | Type.Array t -> t
    | _ -> failwith "expected: array type"

let notConditionalTypeIfThrow = function
    | Type.Bool
    | Type.Int
    | Type.Float -> ()
    | _ -> failwith "operation supported only for bool, int, and float"

let rec expr env = function
    | P.Unit -> Unit
    | P.Int x -> Int x
    | P.Float x -> Float x
    | P.Add(x1, x2)
    | P.FAdd(x1, x2) -> Binary(Var x1, Add, Var x2)
    | P.Sub(x1, x2)
    | P.FSub(x1, x2) -> Binary(Var x1, Sub, Var x2)
    | P.Neg x
    | P.FNeg x -> Unary(Neg, Var x)
    | P.FMul(x1, x2) -> Binary(Var x1, Mul, Var x2)
    | P.FDiv(x1, x2) -> Binary(Var x1, Div, Var x2)
    | P.IfEq(x1, x2, e1, e2) -> Condition(Var x1, Eq, Var x2, expr env e1, expr env e2)
    | P.IfLE(x1, x2, e1, e2) -> Condition(Var x1, Le, Var x2, expr env e1, expr env e2)

    | P.Var x -> Var x
    | P.AppCls(x, xs) -> AppCls(Var x, List.map Var xs)
    | P.AppDir(Id.L x as x', xs) ->
        let t =
            match Map.tryFind x env with
            | Some t -> t
            | None ->

                // Array.make の糖衣構文 ( Typing.extenv には登録されない )
                match x with
                | "min_caml_create_float_array" -> Type.Fun([Type.Int], Type.Array Type.Float)
                | "min_caml_create_array" -> Type.Fun([Type.Int], Type.Array (Map.find xs.[1] env))
                | _ ->

                // Closure.g で付いた "min_caml_" を除去
                let prefix = "min_caml_"
                if x.StartsWith prefix then Map.find x.[prefix.Length..] !Typing.extenv
                else failwithf "expected: prefix \"min_caml_\""

        AppDir((x', t), List.map Var xs)

    | P.Tuple xs -> Tuple <| List.map Var xs
    | P.Get(x1, x2) -> Get(Var x1, Var x2)
    | P.Put(x1, x2, x3) -> Put(Var x1, Var x2, Var x3)

    | P.ExtArray(Id.L x as x') -> ExtArray(x', Map.find x !Typing.extenv |> arrayElementType)

    | P.LetTuple(xts, x, scope) -> LetTuple(xts, Var x, expr (addVars xts env) scope)
    | P.Let((x1, t1) as xt1, e1, e2) -> Let(xt1, expr env e1, expr (Map.add x1 t1 env) e2)
    | P.MakeCls((x1, t1) as xt1, { Closure.entry = l; Closure.actual_fv = fvs }, e2) ->
        let closure = { entry = l; actual_fv = List.map (fun v -> Id.L v, Var v) fvs }
        let scope = expr (Map.add x1 t1 env) e2
        if List.contains x1 fvs
        then LetCls(xt1, closure, scope)
        else Let((x1, t1), Cls(t1, closure), scope)
            

let fundef env { P.name = Id.L x, _ as name; P.args = args; P.formal_fv = formal_fv; P.body = body } =
    let env = addVars args env |> addVars formal_fv
    let useSelf = Set.contains x <| P.fv body
    {
        name = name
        args = args
        useSelf = useSelf
        formalFreeVars = formal_fv
        body = expr env body
    }

let f (P.Prog(fundefs, main)) =
    let env = List.fold (fun env { P.name = Id.L x, t } -> Map.add x t env) Map.empty fundefs

    Prog(
        List.map (fundef env) fundefs,
        expr env main
    )