namespace global

module Lexing =
    open Microsoft.FSharp.Text.Lexing

    let from_string s = LexBuffer<_>.FromString s
    let from_channel is = LexBuffer<_>.FromTextReader is
    let lexeme b = LexBuffer<_>.LexemeString b
    let lexeme_start (b: _ LexBuffer) = b.StartPos.pos_cnum
    let lexeme_end (b: _ LexBuffer) = b.EndPos.pos_cnum

namespace Microsoft.FSharp.Compatibility.OCaml.Parsing