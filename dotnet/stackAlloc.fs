module StackAlloc
open Tree

let isOneOrZero k e =
    let rec count = function
        | Unit | Int _ | Float _ | ExtArray _ -> 0
        | Var x -> if k = x then 1 else 0

        | Binary(e1, _, e2) | Get(e1, e2) | Let(_, e1, e2) | LetTuple(_, e1, e2) -> countMany [e1; e2]
        | Unary(_, e) -> count e

        | Condition(e1, _, e2, e3, e4) -> countMany [e1; e2; e3; e4]

        | MakeCls(_, { actual_fv = les }, e) -> countMany (e::List.map snd les)
        | AppCls(e, es) -> countMany (e::es)
        | AppDir(_, es) | Tuple es -> countMany es
        | Put(e1, e2, e3) -> countMany [e1; e2; e3]

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
    | LetTuple(_, e1, e2)
    | Get(e1, e2) -> isPure e1 && isPure e2

    | Unary(_, e1) -> isPure e1
    | MakeCls(_, { actual_fv = les }, e1) -> List.forall (snd >> isPure) les && isPure e1
    | Condition(e1, _, e2, e3, e4) -> isPure e1 && isPure e2 && isPure e3 && isPure e4
    | Tuple es -> List.forall isPure es

let rec expr map = function
    | Let((x1, t1), e1, scope) ->
        let e1 = expr map e1
        if isOneOrZero x1 scope && isPure e1
        then expr (Map.add x1 e1 map) scope
        else Let((x1, t1), expr map e1, expr map scope)

    | Var x as e -> if Map.containsKey x map then Map.find x map else e

    | Unit | Int _ | Float _ | ExtArray _ as e -> e

    | Unary(op, e) -> Unary(op, expr map e)
    | Binary(e1, op, e2) -> Binary(expr map e1, op, expr map e2)
    | Condition(e1, op, e2, e3, e4) -> Condition(expr map e1, op, expr map e2, expr map e3, expr map e4)
    | MakeCls(xt, ({ actual_fv = les } as c), e) ->
        let c = { c with actual_fv = List.map (fun (l, e) -> l, expr map e) les }
        MakeCls(xt, c, expr map e)

    | AppCls(e, es) -> AppCls(expr map e, List.map (expr map) es)
    | AppDir(x, es) -> AppDir(x, List.map (expr map) es)
    | Tuple es -> Tuple <| List.map (expr map) es
    | LetTuple(xts, e1, e2) -> LetTuple(xts, expr map e1, expr map e2)
    | Put(e1, e2, e3) -> Put(expr map e1, expr map e2, expr map e3)
    | Get(e1, e2) -> Get(expr map e1, expr map e2)

let fundef ({ body = body } as f) = { f with body = expr Map.empty body }

let f (Prog(fundefs, main)) =
    Prog(
        List.map fundef fundefs,
        expr Map.empty main
    )