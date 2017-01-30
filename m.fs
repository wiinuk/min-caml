module M

let empty = Map.empty
let add k v map = Map.add k v map
let mem k map = Map.containsKey k map
let find k map = Map.find k map
let map f map = Map.map (fun _ v -> f v) map
let remove k map = Map.remove k map

let add_list xys env = List.fold_left (fun env (x, y) -> add x y env) env xys
let add_list2 xs ys env = List.fold_left2 (fun env x y -> add x y env) env xs ys