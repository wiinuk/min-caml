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
        | Seq(e1, e2) ->
            yield! exp i e1
            yield! newline i
            yield! exp i e2

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

    let fundef { name = Id.L name, t; args = args; formalFreeVars = formal_fv; body = body } = seq {
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

(
    Id.counter := 0;
    Typing.extenv := M.empty;
"
let x = 10 in
let rec f y =
  if y = 0 then 0 else
  x + f (y - 1) in
print_int (f 123)

"
)
|> closure 1000
// |> ClosurePrinter.prog |> String.concat ""
(*
f.8 : (int) => int (y.9 : int) {x.7 : int} =
    Ti3.10 : int = 0
    if y.9 == Ti3.10 then
        0
    else
        Ti4.13 : int = 1
        Ti5.12 : int = y.9 - Ti4.13
        Ti6.11 : int = f.8#(Ti5.12)
        x.7 + Ti6.11
do
    x.7 : int = 10
    f.8 : (int) => int = f.8{x.7}
    Ti1.15 : int = 123
    Ti2.14 : int = f.8#(Ti1.15)
    min_caml_print_int(Ti2.14)
*)
|> Tree.f
|> StackAlloc.f

// |> TreePrinter.prog |> String.concat ""
(*
f.8 : (int) => int (y.9 : int) {x.7 : int} =
    if y.9 == 0 then
        0
    else
        Ti6.11 : int = f.8#(y.9 - 1)
        x.7 + Ti6.11
do
    f.8 : (int) => int = f.8{x.7 = 10}
    Ti2.14 : int = f.8#(123)
    (min_caml_print_int : (int) => ())(Ti2.14)
*)
|> Virtual.f'
|> emit

#r "bin/Debug/MinCaml.Compiler.Test.dll"
open ExtraOperators
cd <| __SOURCE_DIRECTORY__/"bin/debug/sources"
pwd

let peverify = env"ProgramFiles"/"Microsoft SDKs/Windows/v10.0A/bin/NETFX 4.6.1 Tools/peverify.exe"
let ildasm = env"ProgramFiles"/"Microsoft SDKs/Windows/v10.0A/bin/NETFX 4.6.1 Tools/ildasm.exe"
exe ildasm "-help"
//Usage: ildasm [オプション] <ファイル名> [オプション]
//
//出力リダイレクトのオプションです:
//  /OUT=<ファイル名>   GUI ではなくファイルに直接出力します。
//  /TEXT               GUI ではなくコンソール ウィンドウに直接出力します。
//
//  /HTML               HTML 形式の出力です (/OUT オプションでのみ有効)。
//  /RTF                リッチ テキスト形式の出力です (/TEXT オプションでは無効)。
//GUI またはファイルのオプション/コンソール出力 (EXE および DLL ファイルのみ):
//  /BYTES              命令コメントとして実際のバイト数を 16 進数で表示する。
//  /RAWEH              例外処理句を raw 形式で表示します。
//  /TOKENS             クラスおよびメンバーのメタデータ トークンを表示します。
//  /SOURCE             コメントとして元のソース行を表示します。
//  /LINENUM            元のソース行への参照を含みます。
//  /VISIBILITY=<vis>[+<vis>...]    指定された可視性を持つアイテムのみを
//                                  逆アセンブルします。
//                                  (<vis> = PUB | PRI | FAM | ASM | FAA | FOA
//                      | PSC) 
//  /PUBONLY            パブリック アイテムのみを逆アセンブルします (/VIS=PUB と同
//                      様)。
//  /QUOTEALLNAMES      すべての名前を単一引用符内に含めます。
//  /NOCA               カスタム属性を出力しません。
//  /CAVERBAL           Verbal 形式で CA BLOB を出力します (既定 - バイナリ形式)。
//  /NOBAR              逆アセンブル プログレス バー ポップアップ ウィンドウを
//                      非表示にします。
//
//次のオプションはファイル/コンソール出力にのみ有効です:
//EXE および DLL ファイルのオプション:
//  /UTF8               出力 に UTF-8 エンコード (既定 - ANSI) を使用します。
//  /UNICODE            出力に UNICODE エンコードを使用します。
//  /NOIL               IL アセンブラー コード出力をしません。
//  /FORWARD            事前のクラス宣言を使用します。
//  /TYPELIST           型一覧を出力します (往復での型の順序付けを保存するため)。
//  /PROJECT            入力が .winmd ファイルの場合に .NET プロジェクション ビューを表示します。
//  /HEADERS            出力にファイルのヘッダー情報を含めます。
//  /ITEM=<クラス名>[::<メソッド>[(<署名>)]  指定された項目のみを逆アセンブル
//                                           します。
//
//  /STATS              イメージの統計を含めます。
//  /CLASSLIST          モジュールで定義されたクラスの一覧を含めます。
//  /ALL                /HEADER、/BYTES、/STATS、/CLASSLIST、/TOKENS の
//                      コンビネーション
//
//EXE、DLL、OBJ、および LIB ファイルのオプション:
//  /METADATA[=<指定子>] メタデータを表示します。<指定子> は次のとおりです:
//          MDHEADER    メタデータのヘッダー情報とサイズを表示します。
//          HEX         語句と同様に 16 進数でより多くのものを表示します。
//          CSV         レコード数およびヒープ サイズを表示します。
//          UNREX       未解決の外部参照を表示します。
//          SCHEMA      メタデータ ヘッダーおよびスキーマ情報を表示します。
//          RAW         未処理のメタデータ テーブルを表示します。
//          HEAPS       生のヒープを表示します。
//          VALIDATE    メタデータの一貫性を検査します。
//LIB ファイルのみのオプション:
//  /OBJECTFILE=<オブジェクト ファイル名> ライブラリの単一のオブジェクト 
//                                        ファイルのメタデータを表示します。
//
//オプション キーは '-' または '/' です。オプションは最初の 3 文字で認識されます。
//
//例:    ildasm /tok /byt myfile.exe /out=myfile.il
let ilasm = env"windir"/"Microsoft.NET/Framework/v4.0.30319/ilasm.exe"

Test.testOnce "inprod-loop" |> Async.RunSynchronously

childItem.get "*.ml.exe"
    % exe peverify "%A /verbose"

exe ildasm "cls-rec.ml.exe -text"
exe peverify "cls-rec.ml.exe /verbose"


exe ilasm "libmincaml.il matmul.il -out=matmul.ml.exe"

exe "matmul.ml.exe" ""
exe "matmul.fs.exe" ""