module Arg
open System
open System.Text
open System.Text.RegularExpressions

type spec =
    | Unit of (unit -> unit)
    | Int of (int -> unit)
    | Set of bool ref
    | Clear of bool ref
    | String of (string -> unit)
    | Float of (float -> unit)
    | Rest of (string -> unit)

exception Bad of string
exception Help of string

type key = string
type doc = string

[<AutoOpen>]
module internal Internal =
    open Microsoft.FSharp.Core.Printf

    type env = {
        specs: (key * spec * doc) list
        other: (string -> unit)
        usage: string

        args: string array
        index: int ref
    }

    let helpMessage specs usage =  
        let b = StringBuilder 100
        bprintf b "%s\n" usage

        for key, spec, document in specs do
            match spec with
            | Unit _
            | Set _
            | Clear _ -> bprintf b "\t%s: %s\n" key document
            | String _ -> bprintf b "\t%s <string>: %s\n" key document
            | Int _ -> bprintf b "\t%s <int>: %s\n" key document
            | Float _ -> bprintf b "\t%s <float>: %s\n" key document
            | Rest _ -> bprintf b "\t%s ...: %s\n" key document

        bprintf b "\t--help: display this list of options\n"
        bprintf b "\t-help: display this list of options\n"
        string b

    let invalidArgPattern = Regex "^(\-.*|/[^/]*)$"
    
    let nextArg { specs = specs; usage = usage; args = xs; index = i } key parse =
        if Array.length xs <= !i + 1 then
            helpMessage specs usage
            |> sprintf "option %s needs an argument.\n%s" key
            |> Bad
            |> raise

        let v = xs.[!i + 1]
        try parse v with
        | _ ->
            helpMessage specs usage
            |> Bad
            |> raise
                 
    let parseAction ({ args = xs; index = i } as env) key = function
        | Unit f -> f(); incr i
        | Set f -> f := true; incr i
        | Clear f -> f := false; incr i
        | String f -> f (nextArg env key id); i := !i + 2
        | Int f -> f (nextArg env key int32); i := !i + 2
        | Float f -> f (nextArg env key float); i := !i + 2
        | Rest f ->
            incr i
            while !i < Array.length xs do
                f xs.[!i]
                incr i

    let rec parseArg ({ specs = specs; usage = usage; other = other; index = i } as env) arg = function
        | (key, spec, _)::_ when key = arg -> parseAction env key spec
        | _::specs -> parseArg env arg specs
        | [] ->

        match arg with
        | "-help"
        | "--help"
        | "-?"
        | "/help"
        | "/?" -> helpMessage specs usage |> Help |> raise
        | _ when invalidArgPattern.IsMatch arg ->
            helpMessage specs usage
            |> sprintf "unrecognized argument: %s\n%s" arg
            |> Bad
            |> raise

        | _ -> other arg; incr i

let parse_args index args specs other usage =
    let env = {
        index = index
        args = args
        specs = specs
        other = other
        usage = usage
    }
    incr index
    while !index < Array.length args do
        parseArg env args.[!index] specs

let parseArgv index args specs other usage =
    try parse_args index args specs other usage with
    | Bad m -> eprintf "%s" m; exit 2
    | Help m -> printf "%s" m; exit 0

let parse specs other usage =
    parseArgv (ref 0) (Environment.GetCommandLineArgs()) specs other usage
