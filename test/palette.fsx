#r "../packages/FsLexYacc.Runtime.6.1.0/lib/net40/FsLexYacc.Runtime.dll"
#r "../packages/FSharp.Compatibility.OCaml.0.2.0/lib/net40/FSharp.Compatibility.OCaml.dll"
#r "../packages/FSharp.Compatibility.OCaml.LexYacc.0.2.0/lib/net40/FSharp.Compatibility.OCaml.LexYacc.dll"
#r "../bin/debug/MinCaml.Compiler.dll"

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

let lexbuf limit l =
    Id.counter := 0
    Typing.extenv := M.empty
    Parser.exp Lexer.token l
    |> Typing.f
    |> KNormal.f
    |> Alpha.f
    // |> iter limit
    |> Closure.f

let string s = lexbuf 1000 (Lexing.from_string s)

string """
let rec add a =
    let rec f x = f (x + a) in
    f
in
()
"""

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