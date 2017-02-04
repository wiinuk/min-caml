[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "TypeNamesMustBePascalCase")>]
[<global.System.Diagnostics.CodeAnalysis.SuppressMessageAttribute(
    "NameConventions", "IdentifiersMustNotContainUnderscores")>]
module Stack

module P = Closure

type unary = | Neg
type binary =
    | Add
    | Sub
    | Mul
    | Div
    | Get of Type.t

type condition =
    | Eq
    | Le

type t =
    | Unit
    | Int of int
    | Float of float
    | Unary of unary * t
    | Binary of t * binary * t
    | Condition of t * condition * t * t * t
    | Let of (Id.t * Type.t) * t * t
    | Var of Id.t
    | MakeCls of (Id.t * Type.t) * Closure.closure * t
    | AppCls of t * (* closure type *) Type.t * t list
    | AppDir of (Id.l * (* function type *) Type.t) * t list
    | Tuple of t list * Type.t list
    | LetTuple of (Id.t * Type.t) list * t * t
    | Put of t * (* element type *) Type.t * t * t
    | ExtArray of Id.l * (* element type *) Type.t

type fundef = {
    name: Id.l * Type.t
    args: (Id.t * Type.t) list
    formal_fv: (Id.t * Type.t) list
    body: t
}
type prog = Prog of fundef list * t

let (-.) xs x = Set.remove x xs

let rec freeVars = function
    | Unit | Int _ | Float _ | ExtArray _ -> Set.empty
    | Var x -> Set.singleton x

    | Binary(e1, _, e2) -> freeVars e1 + freeVars e2
    | Unary(_, e) -> freeVars e
    | Put(e1, _, e2, e3) -> freeVars e1 + freeVars e2 + freeVars e3
    | AppCls(e, _, es) -> freeVars e + Set.unionMany (Seq.map freeVars es)
    | Condition(e1, _, e2, e3, e4) -> freeVars e1 + freeVars e2 + freeVars e3 + freeVars e4
    | AppDir(_, es)
    | Tuple(es, _) -> Seq.map freeVars es |> Set.unionMany

    | Let((x, _), e1, scope) -> freeVars scope -. x + freeVars e1
    | MakeCls((x, _), { actual_fv = vs }, e) -> Set.ofList vs + freeVars e -. x
    | LetTuple(xts, e, scope) -> freeVars scope - Set.ofSeq (Seq.map fst xts) + freeVars e

let notContains k e = not (Set.contains k (P.fv e))
let notContains2 k1 k2 e1 e2 =
    let xs1 = P.fv e1
    not (Set.contains k1 xs1) &&
    not (Set.contains k2 xs1) &&

    let xs2 = P.fv e2
    not (Set.contains k1 xs2) &&
    not (Set.contains k2 xs2)

let (|ClosureBinary|_|) env = function
    | P.Add(x, y)
    | P.FAdd(x, y) -> Some(x, Add, y)
    | P.Sub(x, y)
    | P.FSub(x, y) -> Some(x, Sub, y)
    | P.FMul(x, y) -> Some(x, Mul, y)
    | P.FDiv(x, y) -> Some(x, Div, y)
    | P.Get(x, y) ->
        let elementType =
            match Map.find x env with
            | Type.Array t -> t
            | _ -> assert_false()

        Some(x, Get elementType, y)

    | _ -> None

let (|ClosureUnary|_|) = function
    | P.Neg x
    | P.FNeg x -> Some(Neg, x)
    | _ -> None

let (|ClosureCondition|_|) = function
    | P.IfEq(x, y, e1, e2) -> Some(Eq, x, y, e1, e2)
    | P.IfLE(x, y, e1, e2) -> Some(Le, x, y, e1, e2)
    | _ -> None

let takeLets e =
    let rec takeLetsRev xtes = function
        | P.Let((x, t), e, k) when List.forall (fun (x, _, _) -> notContains x e) xtes ->
            takeLetsRev ((x, t, e)::xtes) k

        | e -> List.rev xtes, e

    takeLetsRev [] e

let addVars xts env = List.fold (fun env (x, t) -> Map.add x t env) env xts

let private arrayElementType = function
    | Type.Array t -> t
    | _ -> assert_false()

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
    | P.AppCls(x, xs) -> AppCls(Var x, Map.find x env, List.map Var xs)
    | P.AppDir(x, xs) -> AppDir(x, List.map Var xs)
    | P.Tuple xs -> Tuple(List.map Var xs, List.map (fun x -> Map.find x env) xs)
    | P.Get(x1, x2) -> Binary(Var x1, Map.find x1 env |> arrayElementType |> Get, Var x2)
    | P.Put(x1, x2, x3) -> Put(Var x1, M.find x1 env |> arrayElementType, Var x2, Var x3)

    | P.ExtArray(x, t) -> ExtArray(x, t)

    | P.LetTuple(xts, x, scope) -> LetTuple(xts, Var x, expr (addVars xts env) scope)
    | P.Let((x1, t1) as xt1, e1, e2) -> Let(xt1, expr env e1, expr (Map.add x1 t1 env) e2)
    | P.MakeCls((x1, t1) as xt1, c, e) -> MakeCls(xt1, c, expr (Map.add x1 t1 env) e)

let fundef env { P.name = Id.L l, t as name; P.args = args; P.formal_fv = formal_fv; P.body = body } =
    let env = env |> Map.add l t |> addVars args |> addVars formal_fv
    {
        name = name
        args = args
        formal_fv = formal_fv
        body = expr env body
    }

let f (P.Prog(fundefs, main)) =
    let fundefs, env =
        List.fold (fun (acc, env) ({ P.name = Id.L x, t } as f) ->
            let env = Map.add x t env
            fundef env f::acc, env
        ) ([], Map.empty) fundefs

    Prog(List.rev fundefs, expr env main)