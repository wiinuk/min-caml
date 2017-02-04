#r "../dotnet/MinCaml.Compiler.Cli/bin/debug/FsLexYacc.Runtime.dll"
#r "../dotnet/MinCaml.Compiler.Cli/bin/debug/FSharp.Compatibility.OCaml.dll"
#r "../dotnet/MinCaml.Compiler.Cli/bin/debug/FSharp.Compatibility.OCaml.LexYacc.dll"
#r "../dotnet/MinCaml.Compiler.Cli/bin/debug/MinCaml.Compiler.Ast.dll"
#r "../dotnet/MinCaml.Compiler.Cli/bin/debug/MinCaml.Compiler.Cli.dll"

/// 最適化処理をくりかえす
let rec iter n e =
    eprintf "iteration %d@." n
    if n = 0 then e else
    let e' =
        Beta.f e
        |> Assoc.f
        |> Inline.f
        |> ConstFold.f
        |> Elim.f

    if e = e' then e
    else iter (n - 1) e'

let closure c l =
    Id.counter := 0
    Typing.extenv := M.empty
    Parser.exp Lexer.token (Lexing.from_string l)
    |> Typing.f
    |> KNormal.f
    |> Alpha.f
    |> iter c
    |> Closure.f

open System.IO

let emit x =
    use w = new StringWriter()
    Emit.f w x
    w.GetStringBuilder().ToString()

let string iter l =
    closure iter l
    |> Virtual.f
    |> Simm.f
    |> RegAlloc.f
    |> emit

module Printer =
    let wrapCore first sep last xs = seq {
        match xs with
        | [] -> yield! first; yield! last
        | t::ts ->
            yield! first
            yield! t
            for t in ts do
                yield! sep
                yield! t
            yield! last
    }
    let wrap first sep last xs = wrapCore [first] [sep] [last] xs
    let wrapTuple = wrap "(" ", " ")"

    let between first last x = seq {
        yield first
        yield! x
        yield last
    }
    let newline i = seq {
        yield "\n"
        for _ in 1..i -> "    "
    }

    let rec type' x = seq {
        match x with
        | Type.Unit -> yield "()"
        | Type.Array t -> yield! between "[" "]" <| type' t
        | Type.Bool -> yield "bool"
        | Type.Int -> yield "int"
        | Type.Float -> yield "float"
        | Type.Fun(ts, t) -> yield! List.map type' ts |> wrapTuple; yield " -> "; yield! type' t
        | Type.Tuple ts -> yield! List.map type' ts |> wrapTuple
        | Type.Var { contents = Some t } -> yield! type' t
        | Type.Var _ -> failwith "unexpected type 'Var'"
    }
    let typed (x, t) = seq { yield x; yield " : "; yield! type' t }


module PrintClosure =
    open Closure
    open Printer

    let rec exp i x = seq {
        match x with
        | Unit -> yield "()"
        | Int x -> yield Operators.string x
        | Float x -> yield Operators.string x

        | Add(x, y) -> yield! [x; " + "; y]
        | Sub(x, y) -> yield! [x; " - "; y]
        | Neg x -> yield! ["-"; x]
        | FNeg x -> yield! ["-."; x]
        | FAdd(x, y) -> yield! [x; " +. "; y]
        | FSub(x, y) -> yield! [x; " -. "; y]
        | FMul(x, y) -> yield! [x; " *. "; y]
        | FDiv(x, y) -> yield! [x; " /. "; y]
        | IfEq(x, y, e1, e2) -> yield! ifRelational " == " i (x, y, e1, e2)
        | IfLE(x, y, e1, e2) -> yield! ifRelational " <= " i (x, y, e1, e2)

        | Let(xt, e1, e2) ->
            yield! typed xt
            yield " ="
            yield! newline (i + 1)
            yield! exp (i + 1) e1
            yield! newline i
            yield! exp i e2

        | Var x -> yield x
        | MakeCls(xt, { entry = Id.L entry; actual_fv = actual_fv }, e2) ->
            yield! typed xt
            yield " = "
            yield entry
            yield! List.map Seq.singleton actual_fv |> wrap "{" ", " "}"
            yield! newline i
            yield! exp i e2

        | AppCls(x, xs) ->
            yield x
            yield "#"
            yield! wrapTuple <| List.map Seq.singleton xs

        | AppDir((Id.L x, t), xs) ->
            yield! between "(" ")" <| typed (x, t)
            yield! wrapTuple <| List.map Seq.singleton xs

        | Tuple xs ->
            yield! wrapTuple <| List.map Seq.singleton xs

        | LetTuple(xs, x, e2) ->
            yield! wrapTuple <| List.map typed xs
            yield " ="
            yield! newline (i + 1)
            yield x
            yield! newline i
            yield! exp i e2

        | Get(xs, i) -> yield sprintf "%s[%s]" xs i
        | Put(xs, i, x) -> yield sprintf "%s[%s] <- %s" xs i x
        | ExtArray(Id.L xs, t) -> yield! between "(extern " ")" <| typed (xs, Type.Array t)
        }
    and ifRelational op i (x, y, e1, e2) = seq {
        yield "if "
        yield x
        yield op
        yield y
        yield " then"
        yield! newline (i + 1)
        yield! exp (i + 1) e1
        yield! newline i
        yield "else"
        yield! newline (i + 1)
        yield! exp (i + 1) e2
        }

    let fundef { name = Id.L name, t; args = args; formal_fv = formal_fv; body = body } = seq {
        yield name
        yield " : "
        yield! type' t
        yield " "
        yield! List.map (typed >> between "(" ")") args |> wrapTuple
        yield " "
        yield! List.map typed formal_fv |> wrap "{" ", " "}"
        yield " ="
        yield! newline 1
        yield! exp 1 body
    }
    let prog (Prog(fundefs, main)) = seq {
        for f in fundefs do
            yield! fundef f
            yield! newline 0
        yield "do"
        yield! newline 1
        yield! exp 1 main
        yield! newline 0
    }

module PrintStack =
    open Stack
    open Printer

    let unary = function
        | Neg -> "-"

    let binary = function
        | Add -> " + "
        | Sub -> " - "
        | Mul -> " * "
        | Div -> " / "
        | Get _ -> " `get` "

    let condition = function
        | Eq -> " == "
        | Le -> " <= "

    let rec exp i x = seq {
        match x with
        | Unit -> yield "()"
        | Int x -> yield Operators.string x
        | Float x -> yield Operators.string x

        | Binary(x, op, y) -> yield! exp i x; yield binary op; yield! exp i y
        | Unary(op, x) -> yield unary op; yield! exp i x
        | Condition(x, op, y, e1, e2) -> yield! ifRelational (condition op) i (x, y, e1, e2)
        | Let(xt, e1, e2) ->
            yield! typed xt
            yield " ="
            yield! newline (i + 1)
            yield! exp (i + 1) e1
            yield! newline i
            yield! exp i e2

        | Var x -> yield x
        | MakeCls(xt, { entry = Id.L entry; actual_fv = actual_fv }, e2) ->
            yield! typed xt
            yield " = "
            yield entry
            yield! List.map Seq.singleton actual_fv |> wrap "{" ", " "}"
            yield! newline i
            yield! exp i e2

        | AppCls(x, _, xs) ->
            yield! exp i x
            yield "#"
            yield! wrapTuple <| List.map (exp i) xs

        | AppDir((Id.L x, t), xs) ->
            yield! between "(" ")" <| typed (x, t)
            yield! wrapTuple <| List.map (exp i) xs

        | Tuple(xs, ts) ->
            yield! wrapTuple <| List.map (exp i) xs

        | LetTuple(xs, x, e2) ->
            yield! wrapTuple <| List.map typed xs
            yield " ="
            yield! newline (i + 1)
            yield! exp i x
            yield! newline i
            yield! exp i e2

        | Put(xs, _, ix, x) ->
            yield! exp i xs
            yield "["
            yield! exp i ix
            yield "] <- "
            yield! exp i x

        | ExtArray(Id.L xs, t) -> yield! between "(extern " ")" <| typed (xs, Type.Array t)
        }

    and ifRelational op i (x, y, e1, e2) = seq {
        yield "if "
        yield! exp i x
        yield op
        yield! exp i y
        yield " then"
        yield! newline (i + 1)
        yield! exp (i + 1) e1
        yield! newline i
        yield "else"
        yield! newline (i + 1)
        yield! exp (i + 1) e2
        }

    let fundef { name = Id.L name, t; args = args; formal_fv = formal_fv; body = body } = seq {
        yield name
        yield " : "
        yield! type' t
        yield " "
        yield! List.map (typed >> between "(" ")") args |> wrapTuple
        yield " "
        yield! List.map typed formal_fv |> wrap "{" ", " "}"
        yield " ="
        yield! newline 1
        yield! exp 1 body
    }
    let prog (Prog(fundefs, main)) = seq {
        for f in fundefs do
            yield! fundef f
            yield! newline 0
        yield "do"
        yield! newline 1
        yield! exp 1 main
        yield! newline 0
    }

string 1 "
let rec ack x y =
  if x <= 0 then y + 1 else
  if y <= 0 then ack (x - 1) 1 else
  ack (x - 1) (ack x (y - 1)) in
print_int (ack 3 10)

"

closure 1000 "
let rec ack x y =
  if x <= 0 then y + 1 else
  if y <= 0 then ack (x - 1) 1 else
  ack (x - 1) (ack x (y - 1)) in
print_int (ack 3 10)

"
|> Stack.f
|> StackAlloc.f |> PrintStack.prog |> String.concat ""
|> Virtual.f'
|> emit

c |> PrintClosure.prog |> String.concat ""

let c' = Closure.Prog([], m)
c'
|> Virtual.f
|> emit

string 0 "f(1 + 2 + 3)"
closure 0 "f(1 + 2 + 3)" |> PrintClosure.prog |> String.concat ""

(*
ack.15 : (int, int) -> int ((x.16 : int), (y.17 : int)) {} =
    Ti4.18 : int =
        0
    if x.16 <= Ti4.18 then
        Ti5.19 : int =
            1
        y.17 + Ti5.19
    else
        Ti6.20 : int =
            0
        if y.17 <= Ti6.20 then
            Ti7.22 : int =
                1
            Ti8.21 : int =
                x.16 - Ti7.22
            Ti9.23 : int =
                1
            (ack.15 : (int, int) -> int)(Ti8.21, Ti9.23)
        else
            Ti10.25 : int =
                1
            Ti11.24 : int =
                x.16 - Ti10.25
            Ti12.28 : int =
                1
            Ti13.27 : int =
                y.17 - Ti12.28
            Ti14.26 : int =
                (ack.15 : (int, int) -> int)(x.16, Ti13.27)
            (ack.15 : (int, int) -> int)(Ti11.24, Ti14.26)
do
    Ti1.30 : int =
        3
    Ti2.31 : int =
        10
    Ti3.29 : int =
        (ack.15 : (int, int) -> int)(Ti1.30, Ti2.31)
    (min_caml_print_int : (int) -> ())(Ti3.29)

///

ack.15 : (int, int) -> int ((x.16 : int), (y.17 : int)) {} =
    if x.16 <= 0 then
        y.17 + 1
    else
        if y.17 <= 0 then
            (ack.15 : (int, int) -> int)(x.16 - 1, 1)
        else
            Ti14.26 : int =
                (ack.15 : (int, int) -> int)(x.16, y.17 - 1)
            (ack.15 : (int, int) -> int)(x.16 - 1, Ti14.26)
do
    Ti3.29 : int =
        (ack.15 : (int, int) -> int)(3, 10)
    (min_caml_print_int : (int) -> ())(Ti3.29)
*)

let ilsource = string 0 """
let rec f x = if x = 0 then x else f (x - 1) in
print_int (f 10)
"""

#r "bin/Debug/MinCaml.Compiler.Test.dll"
open ExtraOperators
cd <| __SOURCE_DIRECTORY__/"bin/debug/sources"
pwd
Test.testOnce "ack" |> Async.RunSynchronously
Test.testOnce "cls-bug2" |> Async.RunSynchronously

let peverify = env"ProgramFiles"/"Microsoft SDKs/Windows/v10.0A/bin/NETFX 4.6.1 Tools/PEVerify.exe"
exe peverify "adder.ml.exe"

File.WriteAllText(Path.Combine(__SOURCE_DIRECTORY__, "test.il"), ilsource)
