module MinCaml.Compiler.Ast.Inline
open KNormal

/// インライン展開する関数の最大サイズ
// Mainで-inlineオプションによりセットされる
// TODO: internal
let threshold = ref 0

let rec size = function
    | IfEq(_, _, e1, e2)
    | IfLE(_, _, e1, e2)
    | Let(_, e1, e2)
    | LetRec({ body = e1 }, e2) -> 1 + size e1 + size e2
    | LetTuple(_, _, e) -> 1 + size e
    | _ -> 1

/// インライン展開ルーチン本体
let rec g env = function
    | IfEq(x, y, e1, e2) -> IfEq(x, y, g env e1, g env e2)
    | IfLE(x, y, e1, e2) -> IfLE(x, y, g env e1, g env e2)
    | Let(xt, e1, e2) -> Let(xt, g env e1, g env e2)

    // 関数定義の場合
    | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
        let env = if !threshold < size e1 then env else Map.add x (yts, e1) env
        LetRec({ name = (x, t); args = yts; body = g env e1}, g env e2)

    // 関数適用の場合
    | App(x, ys) when Map.containsKey x env ->
        let (zs, e) = Map.find x env
        eprintf "inlining %s@." x
        let env' = List.fold2 (fun env' (z, _) y -> Map.add z y env') Map.empty zs ys
        Alpha.g env' e

    | LetTuple(xts, y, e) -> LetTuple(xts, y, g env e)
    | e -> e

let f e = g Map.empty e
