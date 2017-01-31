namespace global

module Lexing =
    open Microsoft.FSharp.Text.Lexing

    let from_string s = LexBuffer<_>.FromString s
    let from_channel is = LexBuffer<_>.FromTextReader is
    let lexeme b = LexBuffer<_>.LexemeString b
    let lexeme_start (b: _ LexBuffer) = b.StartPos.pos_cnum
    let lexeme_end (b: _ LexBuffer) = b.EndPos.pos_cnum

module Parsing =
    open Microsoft.FSharp.Text.Parsing

    let private err() = failwith "You must generate your parser using the '--ml-compatibility' option or call 'Parsing.set_parse_state parseState' in each action before using functions from the Parsing module.  This is because the module uses global state which must be set up for use in each parsing action. Review the notes in the 'Microsoft.FSharp.Compatibility.OCaml.Parsing' module if you are using parsers on multiple threads."

    let mutable private parse_information = { new IParseState with
        member __.GetInput _ = err()
        member __.InputEndPosition _ = err()
        member __.ParserLocalStore = err()
        member __.RaiseError() = err()
        member __.ResultRange = err()
        member __.InputRange _ = err()
        member __.InputStartPosition _ = err()
    }

    let set_parse_state s = parse_information <- s
    let symbol_start_pos () = fst parse_information.ResultRange
    let symbol_end_pos () = snd parse_information.ResultRange
    let rhs_start_pos i = fst <| parse_information.InputRange i
    let rhs_end_pos i = snd <| parse_information.InputRange i

    let symbol_start () = symbol_start_pos().pos_cnum
    let symbol_end () = symbol_end_pos().pos_cnum

namespace Microsoft.FSharp.Compatibility.OCaml.Parsing