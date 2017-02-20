#r "bin/debug/FsLexYacc.Runtime.dll"
#r "bin/debug/MinCaml.Compiler.Ast.dll"
#r "bin/debug/MinCaml.Compiler.Cli.dll"
#r "bin/debug/MinCaml.Compiler.Test.dll"

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

let compileToAsm iter l =
    closure iter l
    |> Virtual.f
    |> Simm.f
    |> RegAlloc.f
    |> emit

"
let rec ack x y =
    if x <= 0 then y + 1 else
    if y <= 0 then ack (x - 1) 1 else
    ack (x - 1) (ack x (y - 1)) in
print_int (ack 3 10)
"

//open System
//open System.Reflection
//open System.Reflection.Emit
//do
//    let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName "test", AssemblyBuilderAccess.ReflectionOnly)
//    let m = a.DefineDynamicModule "test"
//    let t0 = m.DefineType "T0"
//    let m0 = t0.DefineMethod("M0", MethodAttributes.Public ||| MethodAttributes.Static)
//    let [|mt0|] = m0.DefineGenericParameters("MT0")
//    let ``m0<t0>`` = m0.MakeGenericMethod(t0)
//
//    ``m0<t0>``.GetGenericMethodDefinition() = upcast m0
//    ()
//
//#r "MinCamlGlobal.exe"
//MinCamlGlobal.min_caml_create_float_array(10, nan)
//MinCamlGlobal.``ack.15``(2, 2)

let a =
    (
    Id.counter := 0;
    Typing.extenv := Map.empty;
    "
    let rec ack x y =
    if x <= 0 then y + 1 else
    if y <= 0 then ack (x - 1) 1 else
    ack (x - 1) (ack x (y - 1)) in
    print_int (ack 3 10)
    "
    )
    |> closure 0
    |> Tree.f
    |> StackAlloc.f
    |> Virtual.f'
    |> DynamicAssembly.defineMinCamlAssembly {
        domain = System.AppDomain.CurrentDomain
        access = System.Reflection.Emit.AssemblyBuilderAccess.RunAndSave
        directory = Some __SOURCE_DIRECTORY__
        fileName = None
    }

type B = System.Reflection.BindingFlags
typeof<Test.Tester>.Assembly.GetType("Ack")
    .GetConstructors(B.Static)

let w = new System.IO.StringWriter()
System.Console.SetOut w
printfn "test %d %c" 10 'a'

open System
let sandbox =
    let d = AppDomain.CurrentDomain
    AppDomain.CreateDomain("sandbox", d.Evidence, d.SetupInformation)

a.Save "MinCamlGlobal.exe"



a.GetType("MinCamlGlobal").GetMethod("Main").Invoke(null, [||])

let m = a.GetTypes().[0]

m.GetMethods()

(
    Id.counter := 0;
    Typing.extenv := M.empty;
"
let rec f n =
  if n < 0 then () else
  (print_int n;
   let a = Array.make 1 f in
   a.(0) (n - 1)) in
f 9
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

Test.testOnce "ack" |> Async.RunSynchronously

childItem.get "*.ml.exe"
    % exe peverify "%A /verbose"

exe "min-caml" "ack"

let target = __SOURCE_DIRECTORY__/"MinCamlGlobal.exe"
exe ildasm "%s -text" target
exe peverify "%s -verbose" target


exe ilasm "libmincaml.il matmul.il -out=matmul.ml.exe"

exe "matmul.ml.exe" ""
exe "matmul.fs.exe" ""


open System
open System.Reflection
open System.Reflection.Emit

let a = AppDomain.CurrentDomain.DefineDynamicAssembly(AssemblyName "Assembly0", AssemblyBuilderAccess.Run)
let m = a.DefineDynamicModule("Module0")
/// System.Reflection.Emit.ModuleBuilder m = ...

m.DefineType("'Ty.pe0'").Name // "pe0'"
m.DefineType("\"Ty.pe0\"").Name // "pe0\""
m.DefineType("Ty\\.pe0").Name // "pe0"
