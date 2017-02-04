module StackAlloc
open Stack

type t = One | Zero | Many

let isOneOrZero k e =
    let rec count = function
        | Unit | Int _ | Float _ | ExtArray _ -> 0
        | Var x -> if k = x then 1 else 0

        | Binary(e1, _, e2) | Let(_, e1, e2) | LetTuple(_, e1, e2) -> countMany [e1; e2]
        | Unary(_, e) | MakeCls(_, _, e) -> count e
        | Condition(e1, _, e2, e3, e4) -> countMany [e1; e2; e3; e4]
        | AppCls(e, _, es) -> countMany (e::es)
        | AppDir(_, es) | Tuple(es, _) -> countMany es
        | Put(e1, _, e2, e3) -> countMany [e1; e2; e3]

    and countMany es =
        let rec aux c = function
            | _ when 1 < c -> c
            | [] -> c
            | e::es -> aux (c + count e) es
        aux 0 es

    count e <= 1

let rec isPure = function
    | Unit | Int _ | Float _ | Var _ | ExtArray _ -> true
    | AppCls _ | AppDir _ | Put _ -> false

    | Binary(e1, _, e2)
    | Let(_, e1, e2)
    | LetTuple(_, e1, e2) -> isPure e1 && isPure e2

    | Unary(_, e1)
    | MakeCls(_, _, e1) -> isPure e1
    | Condition(e1, _, e2, e3, e4) -> isPure e1 && isPure e2 && isPure e3 && isPure e4
    | Tuple(es, _) -> List.forall isPure es

let rec expr env = function
    | Let((x1, t1), e1, scope) ->
        let e1 = expr env e1
        if isOneOrZero x1 scope && isPure e1
        then expr (Map.add x1 e1 env) scope
        else Let((x1, t1), expr env e1, expr env scope)

    | Var x as e -> if Map.containsKey x env then Map.find x env else e

    | Unit | Int _ | Float _ | ExtArray _ as e -> e

    | Unary(op, e) -> Unary(op, expr env e)
    | Binary(e1, op, e2) -> Binary(expr env e1, op, expr env e2)
    | Condition(e1, op, e2, e3, e4) -> Condition(expr env e1, op, expr env e2, expr env e3, expr env e4)
    | MakeCls(xt, c, e) -> MakeCls(xt, c, expr env e)
    | AppCls(e, t, es) -> AppCls(expr env e, t, List.map (expr env) es)
    | AppDir(x, es) -> AppDir(x, List.map (expr env) es)
    | Tuple(es, ts) -> Tuple(List.map (expr env) es, ts)
    | LetTuple(xts, e1, e2) -> LetTuple(xts, expr env e1, expr env e2)
    | Put(e1, et, e2, e3) -> Put(expr env e1, et, expr env e2, expr env e3)

let fundef env ({ body = body } as f) = { f with body = expr env body }

let f (Prog(fundefs, main)) =
    Prog(
        List.map (fundef Map.empty) fundefs,
        expr Map.empty main
    )