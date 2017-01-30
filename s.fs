module S

let empty = Set.empty
let singleton x = Set.singleton x
let add x set = Set.add x set
let union ls rs = Set.union ls rs
let remove k set = Set.remove k set
let diff ls rs = Set.difference ls rs
let mem k set = Set.contains k set
let is_empty set = Set.isEmpty set
let elements set = Set.toList set
let inter ls rs = Set.intersect ls rs

let of_list l = List.fold (fun s e -> add e s) empty l