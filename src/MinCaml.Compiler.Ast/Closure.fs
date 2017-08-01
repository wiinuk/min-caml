module MinCaml.Compiler.Ast.Closure

type closure = {
    entry: Id.l
    actualFv : Id.t list
}

/// クロージャ変換後の式
type t =
    | Unit
    | Int of int
    | Float of float
    | Neg of Id.t
    | Add of Id.t * Id.t
    | Sub of Id.t * Id.t
    | FNeg of Id.t
    | FAdd of Id.t * Id.t
    | FSub of Id.t * Id.t
    | FMul of Id.t * Id.t
    | FDiv of Id.t * Id.t
    | IfEq of Id.t * Id.t * t * t
    | IfLE of Id.t * Id.t * t * t
    | Let of (Id.t * Type.t) * t * t
    | Var of Id.t
    | MakeCls of (Id.t * Type.t) * closure * t
    | AppCls of Id.t * Id.t list
    | AppDir of Id.l * Id.t list
    | Tuple of Id.t list
    | LetTuple of (Id.t * Type.t) list * Id.t * t
    | Get of Id.t * Id.t
    | Put of Id.t * Id.t * Id.t
    | ExtArray of Id.l

type fundef = {
    name: Id.l * Type.t
    args: (Id.t * Type.t) list
    formalFv: (Id.t * Type.t) list
    body: t
}

type prog = Prog of fundef list * t

let rec fv = function
  | Unit | Int _ | Float _ | ExtArray _ -> Set.empty
  | Neg x | FNeg x -> Set.singleton x
  | Add(x, y) | Sub(x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> Set.ofList [x; y]
  | IfEq(x, y, e1, e2)
  | IfLE(x, y, e1, e2) -> (fv e1 + fv e2) |> Set.add y |> Set.add x
  | Let((x, _), e1, e2) -> fv e1 + Set.remove x (fv e2)
  | Var x -> Set.singleton x
  | MakeCls((x, _), { actualFv = ys }, e) -> Set.remove x (Set.ofList ys + fv e)
  | AppCls(x, ys) -> Set.ofList (x::ys)
  | AppDir(_, xs) | Tuple xs -> Set.ofList xs
  | LetTuple(xts, y, e) -> Set.add y (fv e - Set.ofList (List.map fst xts))
  | Put(x, y, z) -> Set.ofList [x; y; z]

let internal toplevel = ref []

/// クロージャ変換ルーチン本体
let rec g env known = function
    | KNormal.Unit -> Unit
    | KNormal.Int i -> Int i
    | KNormal.Float d -> Float d
    | KNormal.Neg x -> Neg x
    | KNormal.Add(x, y) -> Add(x, y)
    | KNormal.Sub(x, y) -> Sub(x, y)
    | KNormal.FNeg x -> FNeg x
    | KNormal.FAdd(x, y) -> FAdd(x, y)
    | KNormal.FSub(x, y) -> FSub(x, y)
    | KNormal.FMul(x, y) -> FMul(x, y)
    | KNormal.FDiv(x, y) -> FDiv(x, y)
    | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g env known e1, g env known e2)
    | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g env known e1, g env known e2)
    | KNormal.Let((x, t), e1, e2) -> Let((x, t), g env known e1, g (Map.add x t env) known e2)
    | KNormal.Var x  -> Var x

    // 関数定義の場合
    | KNormal.LetRec({ name = x, t; args = yts; body = e1 }, e2) ->

        // 関数定義let rec x y1 ... yn = e1 in e2の場合は、xに自由変数がない(closureを介さずdirectに呼び出せる)と仮定し、knownに追加してe1をクロージャ変換してみる
        let toplevel_backup = !toplevel
        let env' = Map.add x t env
        let known' = Set.add x known
        let e1' = g (Map.addList yts env') known' e1

        // 本当に自由変数がなかったか、変換結果e1'を確認する
        // 注意: e1'にx自身が変数として出現する場合はclosureが必要!
        //   (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml参照)
        let zs = fv e1' - Set.ofList (List.map fst yts)
        let known', e1' =
            if Set.isEmpty zs then known', e1' else

            // 駄目だったら状態(toplevelの値)を戻して、クロージャ変換をやり直す
            eprintf "free variable(s) %s found in function %s@." (Id.ppList zs) x
            eprintf "function %s cannot be directly applied in fact@." x

            toplevel := toplevel_backup
            let e1' = g (Map.addList yts env') known e1
            known, e1'

        // 自由変数のリスト
        let zs = fv e1' - Set.add x (Set.ofList (List.map fst yts)) |> Set.toList

        // ここで自由変数zの型を引くために引数envが必要
        let zts = List.map (fun z -> (z, Map.find z env')) zs

        // トップレベル関数を追加
        toplevel := { name = Id.L x, t; args = yts; formalFv = zts; body = e1' }::!toplevel

        // xが変数としてe2'に出現するか
        let e2' = g env' known' e2
        if Set.contains x (fv e2') then

            // 出現していたら削除しない
            MakeCls((x, t), { entry = Id.L x; actualFv = zs }, e2')

        else
            // 出現しなければMakeClsを削除
            eprintf "eliminating closure(s) %s@." x
            e2'

    // 関数適用の場合
    | KNormal.App(x, ys) when Set.contains x known ->
        eprintf "directly applying %s@." x
        AppDir(Id.L x, ys)

    | KNormal.App(f, xs) -> AppCls(f, xs)
    | KNormal.Tuple xs -> Tuple xs
    | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (Map.addList xts env) known e)
    | KNormal.Get(x, y) -> Get(x, y)
    | KNormal.Put(x, y, z) -> Put(x, y, z)
    | KNormal.ExtArray x -> ExtArray <| Id.L x
    | KNormal.ExtFunApp(x, ys) -> AppDir(Id.L("min_caml_" + x), ys)

let f e =
    toplevel := []
    let e' = g Map.empty Set.empty e
    Prog(List.rev !toplevel, e')
