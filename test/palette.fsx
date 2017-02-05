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
    let wrapCore emptyIfNonWrap singleIfNonWrap first sep last xs = seq {
        if Seq.isEmpty xs then
            yield! first
            yield! last
        else
            let t = Seq.head xs
            let ts = Seq.tail xs
            yield! first
            yield! t
            for t in ts do
                yield! sep
                yield! t
            yield! last
    }
    let wrap first sep last xs = wrapCore false false [first] [sep] [last] xs
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
        | Type.Fun(ts, t) ->
            yield! List.map type' ts |> wrapCore false true ["("] [", "] [")"]
            yield " => "
            yield! type' t

        | Type.Tuple ts -> yield! List.map type' ts |> wrapTuple
        | Type.Var { contents = Some t } -> yield! type' t
        | Type.Var _ -> failwith "unexpected type 'Var'"
    }
    let typed (x, t) = seq { yield x; yield " : "; yield! type' t }

module ClosurePrinter =
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
            yield " = "
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

        | AppDir(Id.L x, xs) ->
            yield x
            yield! wrapTuple <| List.map Seq.singleton xs

        | Tuple xs ->
            yield! wrapTuple <| List.map Seq.singleton xs

        | LetTuple(xs, x, e2) ->
            yield! wrapTuple <| List.map typed xs
            yield " = "
            yield x
            yield! newline i
            yield! exp i e2

        | Get(xs, i) -> yield sprintf "%s[%s]" xs i
        | Put(xs, i, x) -> yield sprintf "%s[%s] <- %s" xs i x
        | ExtArray(Id.L xs) -> yield sprintf "(extern %s)" xs
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
        yield! typed (name, t)
        yield " "
        yield! List.map typed args |> wrapTuple
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

module TreePrinter =
    open Tree
    open Printer

    let unary = function
        | Neg -> "-"

    let binary = function
        | Add -> " + "
        | Sub -> " - "
        | Mul -> " * "
        | Div -> " / "

    let condition = function
        | Eq -> " == "
        | Le -> " <= "

    let rec isSingleLine = function
        | Unit
        | Int _
        | Float _
        | Var _
        | ExtArray _ -> true

        | Binary(x, _, y) -> isSingleLine x && isSingleLine y
        | Unary(_, x) -> isSingleLine x
        | AppCls(x, xs) -> isSingleLine x && List.forall isSingleLine xs
        | AppDir(_, xs)
        | Tuple xs -> List.forall isSingleLine xs

        | _ -> false

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
            if isSingleLine e1 then
                yield " = "
                yield! exp (i + 1) e1
            else
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
            yield!
                actual_fv
                |> Seq.map (fun (Id.L l, e) -> seq {
                    yield l
                    yield " = "
                    yield! exp (i + 1) e 
                })
                |> wrap "{" ", " "}"

            yield! newline i
            yield! exp i e2

        | AppCls(x, xs) ->
            yield! exp i x
            yield "#"
            yield! wrapTuple <| List.map (exp i) xs

        | AppDir((Id.L x, t), xs) ->
            yield! between "(" ")" <| typed (x, t)
            yield! wrapTuple <| List.map (exp i) xs

        | Tuple xs ->
            yield! wrapTuple <| List.map (exp i) xs

        | LetTuple(xs, x, e2) ->
            yield! wrapTuple <| List.map typed xs
            yield " ="
            yield! newline (i + 1)
            yield! exp i x
            yield! newline i
            yield! exp i e2

        | Get(xs, ix) ->
            yield! exp i xs
            yield "["
            yield! exp i ix
            yield "]"

        | Put(xs, ix, x) ->
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
        yield! typed (name, t)
        yield " "
        yield! List.map typed args |> wrapTuple
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



    Id.counter := 0
    Typing.extenv := M.empty

Asm.tupleType (List.replicate 9 Asm.Int32)

Id.counter := 0
Typing.extenv := M.empty

"
f(1,2,3,4,5,6,7,8,9)

"
|> closure 1000

// |> ClosurePrinter.prog |> String.concat ""
(*
f.9 : (int) => () (n.10 : int) {} =
    Ti3.11 : int = 0
    if Ti3.11 <= n.10 then
        Tu1.12 : () = (min_caml_print_int : (int) => ())(n.10)
        Ti4.14 : int = 1
        a.13 : [(int) => ()] = (min_caml_create_array : (int, float) => [(int) => ()])(Ti4.14, f.9)
        Ti5.16 : int = 0
        Tf6.15 : (int) => () = a.13[Ti5.16]
        Ti7.18 : int = 1
        Ti8.17 : int = n.10 - Ti7.18
        Tf6.15#(Ti8.17)
    else
        ()
do
    f.9 : (int) => () = f.9{}
    Ti2.19 : int = 9
    f.9#(Ti2.19)
*)
|> Tree.f
|> StackAlloc.f

// |> StackPrinter.prog |> String.concat ""
(*
f.9 : (int) => () (n.10 : int) {} =
    if 0 <= n.10 then
        Tu1.12 : () = (min_caml_print_int : (int) => ())(n.10)
        a.13 : [(int) => ()] = (min_caml_create_array : (int, float) => [(int) => ()])(1, f.9)
        a.13 `get` 0#(n.10 - 1)
    else
        ()
do
    f.9 : (int) => () = f.9{}
    f.9#(9)
*)
|> Virtual.f'
|> emit

#r "bin/Debug/MinCaml.Compiler.Test.dll"
open ExtraOperators
cd <| __SOURCE_DIRECTORY__/"bin/debug/sources"
pwd
Test.testOnce "ack" |> Async.RunSynchronously
Test.testOnce "cls-rec" |> Async.RunSynchronously

let peverify = env"ProgramFiles"/"Microsoft SDKs/Windows/v10.0A/bin/NETFX 4.6.1 Tools/PEVerify.exe"
exe peverify "adder.ml.exe"
