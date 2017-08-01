// TODO: namespace MinCaml.Compiler.Ast
namespace global

[<AutoOpen>]
module ExtraTopLevelOperators =
    let unreachable<'a> = failwith<'a> "unreachable"

[<AutoOpen>]
module Operators =
    let inline (==) l r = LanguagePrimitives.PhysicalEquality l r
    let inline (.()) (xs: _ array) i = xs.[i]
    let inline (.()<-) (xs: _ array) i x = xs.[i] <- x
    
module Map =
    let addList xys env = List.fold (fun env (x, y) -> Map.add x y env) env xys
    let addList2 xs ys env = List.fold2 (fun env x y -> Map.add x y env) env xs ys
    let mapValue f xs = Map.map (fun _ x -> f x) xs

module Set =
    let ofList l = List.fold (fun s e -> Set.add e s) Set.empty l
