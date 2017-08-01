open MinCaml.Compiler.Ast
open MinCaml.Compiler.Cli
open System.IO
open System.Text
open Microsoft.FSharp.Text.Lexing

let limit = ref 1000

let rec iter n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  eprintf "iteration %d@." n;
  if n = 0 then e else
  let e' = Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e)))) in
  if e = e' then e else
  iter (n - 1) e'

let lexbuf outchan l = (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  Typing.extenv := Map.empty;
  Emit.f outchan
    (RegAlloc.f
       (Simm.f
      (Virtual.f
         (Closure.f
        (iter !limit
           (Alpha.f
              (KNormal.f
             (Typing.f
                (Parser.exp Lexer.token l)))))))))

let string s = lexbuf stdout (LexBuffer<_>.FromString s) (* 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)

let file f = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  use inchan = new StreamReader(File.OpenRead(f + ".ml"), Encoding.UTF8, detectEncodingFromByteOrderMarks = false) in
  use outchan = new StreamWriter(File.OpenWrite(f + ".il"), Encoding.UTF8) in
  lexbuf outchan (LexBuffer<_>.FromTextReader inchan);
  
// ここからコンパイラの実行が開始される (caml2html: main_entry)
[<EntryPoint>]
let main args =
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined");
     ("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated")]
    (fun s -> files := !files @ [s])
    ("Mitou Min-Caml Compiler (C) Eijiro Sumii\n" ^
     sprintf "usage: %s [-inline m] [-iter n] ...filenames without \".ml\"..." args.[0]);
  List.iter
    (fun f -> ignore (file f))
    !files;
  0
