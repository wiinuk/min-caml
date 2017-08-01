#r "bin/debug/FsLexYacc.Runtime.dll"
#r "bin/debug/MinCaml.Compiler.Ast.dll"
#r "bin/debug/MinCaml.Compiler.Cli.dll"
#r "bin/debug/MinCaml.Compiler.Test.dll"


open MinCaml.Compiler.Test
open System.IO

let emit x =
    use w = new StringWriter()
    Emit.f w x
    w.Flush()
    w.GetStringBuilder().ToString()

"
a.(0).(0) <- 0;
a.(1).(1) <- 2
"
|> Lexing.from_string
|> Test.parseClosure 1000
// |> ClosurePrinter.prog |> String.concat ""
(*
do
    Ta2.14 : [[int]] = (extern a)
    Ti3.15 : int = 0
    Ta4.13 : [int] = Ta2.14[Ti3.15]
    Ti5.16 : int = 0
    Ti6.17 : int = 0
    Tu1.12 : () = Ta4.13[Ti5.16] <- Ti6.17
    Ta7.19 : [[int]] = (extern a)
    Ti8.20 : int = 1
    Ta9.18 : [int] = Ta7.19[Ti8.20]
    Ti10.21 : int = 1
    Ti11.22 : int = 2
    Ta9.18[Ti10.21] <- Ti11.22
*)
|> Test.closureToTree
|> StackAlloc.f
// |> TreePrinter.prog |> String.concat ""
(*
do
    Ta4.13 = (extern a)[0]
    Ta4.13[0] <- 0
    Ta9.18 = (extern a)[1]
    Ta9.18[1] <- 2
*)
|> Virtual.f'
|> emit


#r "bin/Debug/MinCaml.Compiler.Test.dll"
open ExtraOperators
open System
open System.IO
open System.Reflection.Emit

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

let target = "cls-bug2.ml.exe"
Test.testOnce "cls-bug2" |> Async.RunSynchronously

exe ildasm "%s -text" target
exe peverify "%s -verbose" target

childItem.get "*.ml.exe"
    % exe peverify "%A /verbose"
    
(*

*)