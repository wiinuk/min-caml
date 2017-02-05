[<AutoOpen>]
module LibMinCaml
open System

// prim ops
let (+.) (x: float) y = x + y
let (-.) (x: float) y = x - y
let ( *. ) (x: float) y = x * y
let (/.) (x: float) y = x / y
let (~-.) (x: float) = -x
let (.()) (xs: _ array) i = xs.[i]
let (.()<-) (xs: _ array) i x = xs.[i] <- x

let print_newline() = printfn ""
let print_int x = printf "%d" x
let print_byte x = Checked.byte x |> char |> printf "%c"
let prerr_int x = eprintf "%d" x
let prerr_byte x = Checked.byte x |> char |> eprintf "%c"
let prerr_float x = eprintf "%f" x
let read_int () = Console.ReadLine() |> int32
let read_float () = Console.ReadLine() |> float
let abs_float x = abs<float> x
let sqrt x = sqrt x
let floor x = floor x
let int_of_float x = int<float> x
let truncate x = int<float> x
let float_of_int x = float<int> x
let cos x = cos x
let sin x = sin x
let atan x = atan x

module Array =
    let make n x = Array.create n x
