module MinCaml.Compiler.Ast.Type

/// MinCamlの型を表現するデータ型
type t =
    | Unit
    | Bool
    | Int
    | Float

    // arguments are uncurried
    | Fun of t list * t

    | Tuple of t list
    | Array of t
    | Var of t option ref

/// 新しい型変数を作る
let gentyp _ = Var <| ref None
