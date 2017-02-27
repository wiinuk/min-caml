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
let rec f x = x + 123 in
let rec g y = f in
print_int ((g 456) 789)
"
|> Lexing.from_string
|> Test.parseClosure 1000
//|> ClosurePrinter.prog |> String.concat ""
(*
f.6 : (int) => int (x.7 : int) {} =
    Ti5.8 : int = 123
    x.7 + Ti5.8
g.9 : (int) => (int) => int (y.10 : int) {f.6 : (int) => int} =
    f.6
do
    f.6 : (int) => int = f.6{}
    g.9 : (int) => (int) => int = g.9{f.6}
    Ti1.13 : int = 456
    Tf2.12 : (int) => int = g.9#(Ti1.13)
    Ti3.14 : int = 789
    Ti4.11 : int = Tf2.12#(Ti3.14)
    min_caml_print_int(Ti4.11)
*)
|> Test.closureToTree
|> StackAlloc.f
//|> TreePrinter.prog |> String.concat ""
(*
f.6 : (int) => int (x.7 : int) {} =
    x.7 + 123
g.9 : (int) => (int) => int (y.10 : int) {f.6 : (int) => int} =
    f.6
do
    f.6 : (int) => int = f.6{}
    g.9 : (int) => (int) => int = g.9{f.6 = f.6}
    Tf2.12 : (int) => int = g.9#(456)
    Ti4.11 : int = Tf2.12#(789)
    (min_caml_print_int : (int) => ())(Ti4.11)
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
テスト名:	Test.testDynamic(sourceML: "join-reg.ml")
テストの完全名:	Test.testDynamic (79b960fb205f2d9f0ae65f21b25b5c8ea72357e6)
テスト ソース:	M:\HOME_pc-2\Source\Repos\min-caml\dotnet\Test.fs : 行 220
テスト成果:	失敗
テスト継続時間:	0:00:00.019

結果  のスタック トレース:	
場所 Microsoft.FSharp.Core.PrintfModule.PrintFormatToStringThenFail@1360.Invoke(String message)
   場所 DynamicAssembly.getOrThrow@146-1.Invoke(IEnumerable`1 arg20) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 146
   場所 DynamicAssembly.getOrThrow[a,b](Dictionary`2 xs, a k) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 146
   場所 DynamicAssembly.findMethod(env env, TypeBuilder parent, String name, FSharpList`1 argTypes) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 160
   場所 DynamicAssembly.resolveMethodBase(env env, method_ref m) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 256
   場所 DynamicAssembly.EmitMethods.opcode@483.Invoke(exp _arg2) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 515
   場所 DynamicAssembly.EmitMethods.methodBody(env env, ILGenerator g, method_def _arg1) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 564
   場所 DynamicAssembly.EmitMethods.methodDef(env env, TypeBuilder parent, method_def _arg1) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 596
   場所 DynamicAssembly.EmitMethods.classDecl(env env, TypeBuilder t, class_decl _arg2) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 600
   場所 DynamicAssembly.EmitMethods.classDef[a](env env, FSharpChoice`2 parent, class_def _arg1) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 611
   場所 DynamicAssembly.EmitMethods.decl[a](env env, a a, decl _arg1) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 615
   場所 DynamicAssembly.defineMinCamlAssembly(dynamic_assembly_settings s, prog p) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\dynamicAssembly.fs:行 674
   場所 Test.compileFileToAssembly(String sourcePath, Int32 iterationCount, dynamic_assembly_settings assemblySettings) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\Test.fs:行 164
   場所 Test.invokeML(String sourceML) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\Test.fs:行 173
   場所 Test.testDynamicOnce(String sourceML) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\Test.fs:行 214
   場所 Test.testDynamic(String sourceML) 場所 M:\HOME_pc-2\Source\Repos\min-caml\dotnet\Test.fs:行 221
結果  のメッセージ:	
System.Exception : entry not found. key: ("f.12", []), map: seq
  [(("min_caml_print_newline", []),
    Name: min_caml_print_newline 
Attributes: 150
Method Signature: Length: 3
Arguments: 0
Signature: 
0  0  1  0  


);
   (("min_caml_print_int", [Int32]),
    Name: min_caml_print_int 
Attributes: 150
Method Signature: Length: 4
Arguments: 0
Signature: 
0  0  1  8  0  


);
   (("min_caml_print_byte", [Int32]),
    Name: min_caml_print_byte 
Attributes: 150
Method Signature: Length: 4
Arguments: 0
Signature: 
0  0  1  8  0  


);
   (("min_caml_prerr_int", [Int32]),
    Name: min_caml_prerr_int 
Attributes: 150
Method Signature: Length: 4
Arguments: 0
Signature: 
0  0  1  8  0  


);
   ...]


*)