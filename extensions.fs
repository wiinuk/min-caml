// TODO: namespace MinCaml.Compiler.Ast
namespace global

module Map =
    let addList xys env = List.fold_left (fun env (x, y) -> Map.add x y env) env xys
    let addList2 xs ys env = List.fold_left2 (fun env x y -> Map.add x y env) env xs ys
    let mapValue f xs = Map.map (fun _ x -> f x) xs

module Set =
    let ofList l = List.fold (fun s e -> Set.add e s) Set.empty l
