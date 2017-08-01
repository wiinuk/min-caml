module MinCaml.Compiler.Ast.Elim
open KNormal

/// 副作用の有無
let rec effect = function
    | Let(_, e1, e2) | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> effect e1 || effect e2
    | LetRec(_, e) | LetTuple(_, _, e) -> effect e
    | App _ | Put _ | ExtFunApp _ -> true
    | _ -> false

/// 不要定義削除ルーチン本体
let rec f = function
    | IfEq(x, y, e1, e2) -> IfEq(x, y, f e1, f e2)
    | IfLE(x, y, e1, e2) -> IfLE(x, y, f e1, f e2)

    // letの場合
    | Let((x, t), e1, e2) ->
        let e1' = f e1
        let e2' = f e2
        if effect e1' || Set.contains x (fv e2') then Let((x, t), e1', e2') else

        eprintf "eliminating variable %s@." x
        e2'

    // let recの場合
    | LetRec({ name = x, t; args = yts; body = e1 }, e2) ->
        let e2' = f e2
        if Set.contains x (fv e2') then LetRec({ name = (x, t); args = yts; body = f e1 }, e2') else

        eprintf "eliminating function %s@." x
        e2'

    | LetTuple(xts, y, e) ->
        let xs = List.map fst xts
        let e' = f e
        let live = fv e'
        if List.exists (fun x -> Set.contains x live) xs then LetTuple(xts, y, e') else

        eprintf "eliminating variables %s@." <| Id.ppList xs
        e'

    | e -> e
