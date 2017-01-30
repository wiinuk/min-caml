open System.IO
open System.Text

let eucJp = Encoding.GetEncoding "EUC-JP"
let utf8 = UTF8Encoding(encoderShouldEmitUTF8Identifier = false)
let newLine = "\n"

let (/) l r = Path.Combine(l, r)

let convertAndOverwrite path =
    File.WriteAllBytes(path, Encoding.Convert(eucJp, utf8, File.ReadAllBytes path))

Directory.EnumerateFiles(__SOURCE_DIRECTORY__, "*.ml", SearchOption.AllDirectories)
|> Seq.iter convertAndOverwrite

__SOURCE_DIRECTORY__/"parser.mly"
|> convertAndOverwrite

__SOURCE_DIRECTORY__/"lexer.mll"
|> convertAndOverwrite
