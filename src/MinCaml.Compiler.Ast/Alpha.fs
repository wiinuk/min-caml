/// rename identifiers to make them unique (alpha-conversion)
module MinCaml.Compiler.Ast.Alpha
open KNormal
open System.Collections.Generic

let find x env = try Map.find x env with :? KeyNotFoundException -> x

/// α変換ルーチン本体
let rec g env = function
    | Unit -> Unit
    | Int i -> Int i
    | Float d -> Float d
    | Neg x -> Neg <| find x env
    | Add(x, y) -> Add(find x env, find y env)
    | Sub(x, y) -> Sub(find x env, find y env)
    | FNeg x -> FNeg <| find x env
    | FAdd(x, y) -> FAdd(find x env, find y env)
    | FSub(x, y) -> FSub(find x env, find y env)
    | FMul(x, y) -> FMul(find x env, find y env)
    | FDiv(x, y) -> FDiv(find x env, find y env)
    | IfEq(x, y, e1, e2) -> IfEq(find x env, find y env, g env e1, g env e2)
    | IfLE(x, y, e1, e2) -> IfLE(find x env, find y env, g env e1, g env e2)

    // letのα変換
    | Let((x, t), e1, e2) ->
        let x' = Id.genid x
        Let((x', t), g env e1, g (Map.add x x' env) e2)

    | Var x -> Var <| find x env

    // let recのα変換
    | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
        let env = Map.add x (Id.genid x) env
        let ys = List.map fst yts
        let env' = Map.addList2 ys (List.map Id.genid ys) env
        let f = {
            name = find x env, t
            args = List.map (fun (y, t) -> find y env', t) yts
            body = g env' e1
        }
        LetRec(f, g env e2)

    | App(x, ys) -> App(find x env, List.map (fun y -> find y env) ys)
    | Tuple xs -> Tuple <| List.map (fun x -> find x env) xs

    // LetTupleのα変換
    | LetTuple(xts, y, e) ->
        let xs = List.map fst xts
        let env' = Map.addList2 xs (List.map Id.genid xs) env
        LetTuple(
            List.map (fun (x, t) -> find x env', t) xts,
            find y env,
            g env' e
        )

    | Get(x, y) -> Get(find x env, find y env)
    | Put(x, y, z) -> Put(find x env, find y env, find z env)
    | ExtArray x -> ExtArray x
    | ExtFunApp(x, ys) -> ExtFunApp(x, List.map (fun y -> find y env) ys)

let f = g Map.empty
