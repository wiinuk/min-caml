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
let rec add a b = a + b in
let rec add3 a b c = a + b + c in
()
"""

let ilsource = string "print_int 10"

File.WriteAllText(Path.Combine(__SOURCE_DIRECTORY__, "test.il"), ilsource)

#r "test.exe"
MinCamlModule.Main()

open Id
open Closure
open Type

Prog(
    [
    {
        name = L"f.4", Fun([Int], Int)
        args = ["x.5", Int]
        formal_fv = ["a.3", Int]
        body =
            Let(
                ("Ti1.6", Int),
                Add("x.5", "a.3"),
                AppCls("f.4", ["Ti1.6"])
            )
    }
    {
        name = L"add.2", Fun([Int], Fun([Int], Int))
        args = ["a.3", Int]
        formal_fv = []
        body =
            MakeCls(
                ("f.4", Fun([Int], Int)),
                {
                    entry = L"f.4"
                    actual_fv = ["a.3"]
                },
                Closure.Var "f.4"
            )
    }
    ],
    Closure.Unit
)

string """
let x = xs.(0) in
()
"""


#load "../fsshell.fsx"
let (/) = path.join
exe (__SOURCE_DIRECTORY__/"../dotnet/min-caml/bin/debug/min-caml.exe") "testtest"
