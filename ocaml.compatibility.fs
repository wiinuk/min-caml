namespace global

open FSharp.Compatibility

[<AutoOpen>]
module LanguagePrimitives =
    open System.Diagnostics
    open FSharp.Compatibility.OCaml

    let assert_false() =
        let f = StackFrame(1, true)
        raise <| Assert_failure(f.GetFileName(), f.GetFileLineNumber(), f.GetFileColumnNumber())

[<AutoOpen>]
module Core =
    exception Invalid_argument = OCaml.Core.Invalid_argument
    exception Not_found = OCaml.Core.Not_found
    let inline (~-.) x = (~-) x
    let inline (+.) l r = l + r
    let inline (-.) l r = l - r
    let inline ( *. ) l r = l * r
    let inline (/.) l r = l / r

[<AutoOpen>]
module Pervasives =
    let (==) l r = OCaml.Pervasives.(==) l r
    let open_in s = OCaml.Pervasives.open_in s
    let open_out s = OCaml.Pervasives.open_out s
    let close_in s = OCaml.Pervasives.close_in s
    let close_out s = OCaml.Pervasives.close_out s

    let inline (mod) x y = x % y
    let inline (lsl) x n = x <<< n

    let inline (.()) xs i = Array.get xs i
    let inline (.()<-) xs i x = Array.set xs i x

    let succ x = OCaml.Pervasives.succ x

    let print_int x = OCaml.Pervasives.print_int x
    let print_newline() = OCaml.Pervasives.print_newline()

    let int_of_string x = OCaml.Pervasives.int_of_string x
    let int_of_float x = OCaml.Pervasives.int_of_float x
    let float_of_string x = OCaml.Pervasives.float_of_string x
    let float_of_int x = OCaml.Pervasives.float_of_int x
    let string_of_int x = OCaml.Pervasives.string_of_int x

    let abs_float x = OCaml.Pervasives.abs_float x
    let truncate x = OCaml.Pervasives.int_of_float x

module Format =
    let eprintf format = Printf.eprintf format
    let sprintf format = Printf.sprintf format

module Arg =
    let parse specs other usageText = OCaml.Arg.parse specs other usageText
    let Int x = OCaml.Arg.Int x

module List =
    let fold_left2 f z xs1 xs2 = OCaml.List.fold_left2 f z xs1 xs2
    let fold_left f z xs = OCaml.List.fold_left f z xs
    let mem x xs = OCaml.List.mem x xs
    let hd xs = OCaml.List.hd xs
    let mem_assoc x xs = OCaml.List.mem_assoc x xs

module Array =
    let to_list xs = OCaml.Array.to_list xs
    let make n x = OCaml.Array.make n x

module String =
    let get (x: string) i = x.[i]

module Hashtbl =
    let create n = OCaml.Hashtbl.create n
    let add map k v = OCaml.Hashtbl.add map k v
    let find map k = OCaml.Hashtbl.find map k

