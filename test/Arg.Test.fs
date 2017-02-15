module Arg.Test
open Arg
open Xunit

let parseMinCamlArgs args =
    let inline' = ref -1
    let limit = ref -1
    let files = ref []
    let specs = [
        "-inline", Int(fun i -> inline' := i), "maximum size of functions inlined"
        "-iter", Int(fun i -> limit := i), "maximum number of optimizations iterated"
    ]
    let other s = files := !files @ [s]
    let r =
        try parse_args (ref 0) args specs other "usage"; Choice1Of3() with
        | Bad m -> Choice2Of3 m
        | Help m -> Choice3Of3 m

    r, !inline', !limit, !files

[<Fact>]
let parseMinCamlArgsValid() =
    let expected = Choice1Of3(), 567, 890, ["a.ml"; "b.ml"; "c.ml"; "d.ml"]
    let actual = parseMinCamlArgs [|"min-caml"; "a.ml"; "-inline"; "12"; "b.ml"; "-iter"; "34"; "-inline"; "567"; "-iter"; "890"; "c.ml"; "d.ml"|]

    Assert.Equal(expected, actual, LanguagePrimitives.FastGenericEqualityComparer)

[<Fact>]
let parseMinCamlArgsHelp() =
    let expected = Choice3Of3 "usage\n\t-inline <int>: maximum size of functions inlined\n\t-iter <int>: maximum number of optimizations iterated\n\t--help: display this list of options\n\t-help: display this list of options\n", -1, -1, []
    let actual = parseMinCamlArgs [|"min-caml"; "-help"|]
    Assert.Equal(expected, actual, LanguagePrimitives.FastGenericEqualityComparer)

[<Fact>]
let parseMinVamlArgsInvalid() =
    let expected = Choice2Of3 "unrecognized argument: -unrecognizedarg\nusage\n\t-inline <int>: maximum size of functions inlined\n\t-iter <int>: maximum number of optimizations iterated\n\t--help: display this list of options\n\t-help: display this list of options\n", -1, -1, []
    let actual = parseMinCamlArgs [|"min-caml"; "-unrecognizedarg"|]
    Assert.Equal(expected, actual, LanguagePrimitives.FastGenericEqualityComparer)
