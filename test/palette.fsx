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

let closure limit l =
    Id.counter := 0
    Typing.extenv := M.empty
    Parser.exp Lexer.token l
    |> Typing.f
    |> KNormal.f
    |> Alpha.f
    // |> iter limit
    |> Closure.f

let lexbuf writer limit l =
    closure limit l
    |> Virtual.f
//    |> Simm.f
//    |> RegAlloc.f
    |> Emit.f writer

open System.IO

let string s =
    use w = new StringWriter()
    lexbuf w 1000 (Lexing.from_string s)
    w.GetStringBuilder().ToString()

let ilsource = string """
let rec f x = if x = 0 then x else f (x - 1) in
print_int (f 10)
"""

let ilsource = string """
let rec ack x y =
  if x <= 0 then y + 1 else
  if y <= 0 then ack (x - 1) 1 else
  ack (x - 1) (ack x (y - 1)) in
print_int (ack 3 10)
"""

#r "bin/Debug/MinCaml.Compiler.Test.dll"
open ExtraOperators
cd <| __SOURCE_DIRECTORY__/"bin/debug"
pwd
Test.testOnce "ack" |> Async.RunSynchronously
Test.testOnce "adder" |> Async.RunSynchronously

File.WriteAllText(Path.Combine(__SOURCE_DIRECTORY__, "test.il"), ilsource)
