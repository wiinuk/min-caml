module MinCaml.Compiler.Ast.Id

/// 変数の名前
type t = string

/// トップレベル関数やグローバル配列のラベル
type l = L of string

let ppList xs = String.concat " " xs

// TODO: internal
let counter = ref 0
let genid s =
    incr counter
    sprintf "%s.%d" s !counter

let rec ofType = function
  | Type.Unit -> "u"
  | Type.Bool -> "b"
  | Type.Int -> "i"
  | Type.Float -> "d"
  | Type.Fun _ -> "f"
  | Type.Tuple _ -> "t"
  | Type.Array _ -> "a"
  | Type.Var _ -> unreachable

let gentmp typ =
    incr counter
    sprintf "T%s%d" (ofType typ) !counter
