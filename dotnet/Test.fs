module Test
open ExtraOperators
open Xunit

//                 - 出力ファイル -
// --out:<file>                   出力ファイルの名前 (短い形式: -o)
// --target:exe                   コンソール実行可能ファイルをビルドします
// --target:winexe                Windows 実行可能ファイルをビルドします
// --target:library               ライブラリをビルドします (短い形式: -a)
// --target:module                別のアセンブリに追加できるモジュールをビルドします
// --delaysign[+|-]               厳密名キーのパブリックな部分のみを使ってアセンブリを遅延署名します
// --doc:<file>                   指定したファイルにアセンブリの xmldoc を書き込みます
// --keyfile:<file>               厳密名キー ファイルを指定します
// --keycontainer:<string>        厳密名キー コンテナーを指定します
// --platform:<string>            このコードが実行されるプラットフォームの制限: x86、Itanium、x64、anycpu32bitpreferred、または anycpu。既定は anycpu です。
// --nooptimizationdata           インライン コンストラクトの実装に必要な最適化情報のみを含めてください。モジュール間のインライン処理を禁止し、バイナリの互換性を改善し
// てください。
// --nointerfacedata              F# 固有のメタデータを含む生成済みアセンブリにリソースを追加しないでください
// --sig:<file>                   アセンブリの推論されたインターフェイスをファイルに出力します
//
//                 - 入力ファイル -
// --reference:<file>             アセンブリを参照します (短い形式: -r)
//
//                 - リソース -
// --win32res:<file>              Win32 リソース ファイル (.res) を指定します
// --win32manifest:<file>         Win32 マニフェスト ファイルを指定します
// --nowin32manifest              既定の Win32 マニフェストを含めないでください
// --resource:<resinfo>           指定したマネージ リソースを埋め込みます
// --linkresource:<resinfo>       指定したリソースをこのアセンブリにリンクします。このとき、リソース情報の形式は <ファイル>[,<文字列名>[,public|private]] です。
//
//                 - コード生成 -
// --debug[+|-]                   デバッグ情報を生成します (短い形式: -g)
// --debug:{full|pdbonly}         デバッグの種類 'full' または 'pdbonly' を指定します ('full' が既定値で、実行中のプログラムにデバッガーをアタッチすることができます)。
//
// --optimize[+|-]                最適化を有効にします (短い形式: -O)
// --tailcalls[+|-]               tail の呼び出しを有効または無効にします
// --crossoptimize[+|-]           モジュール間の最適化を有効または無効にします
//
//                 - エラーと警告 -
// --warnaserror[+|-]             すべての警告をエラーとして報告する
// --warnaserror[+|-]:<warn;...>  指定した警告をエラーとして報告する
// --warn:<n>                     警告レベル (0 ～ 5) を設定します
// --nowarn:<warn;...>            指定の警告メッセージを無効にする
// --warnon:<warn;...>            既定でオフにすることができる特定の警告を有効にします
// --consolecolors[+|-]           警告メッセージとエラー メッセージを色つきで表示します
//
//                 - 言語 -
// --checked[+|-]                 オーバーフロー チェックの生成
// --define:<string>              条件付きコンパイル シンボルを定義します (短い形式: -d)
// --mlcompatibility              ML 互換性に関する警告を無視します
//
//                 - その他 -
// --nologo                       コンパイラーの著作権メッセージを表示しません
// --help                         この使用方法に関するメッセージを表示します (短い形式: -?)
//
//                 - 詳細 -
// --codepage:<n>                 ソース ファイルの読み取りに使用するコードページを指定します
// --utf8output                   UTF-8 エンコードでメッセージを出力します
// --fullpaths                    完全修飾パスを含むメッセージを出力します
// --lib:<dir;...>                ソース ファイルおよびアセンブリの解決に使用する include パスのディレクトリを指定します (短い形式: -I)
// --baseaddress:<address>        ビルドするライブラリのベース アドレス
// --noframework                  既定では、既定の CLI アセンブリを参照しません
// --standalone                   F# ライブラリと、ライブラリに依存するすべての参照 DLL を、生成されるアセンブリへ静的にリンクします
// --staticlink:<file>            指定したアセンブリと、そのアセンブリに依存するすべての参照 DLL を静的にリンクします。DLL 名ではなく、アセンブリ名 (たとえば、mylib)
// を使用してください。
// --pdb:<string>                 出力デバッグ ファイルの名前を指定します
// --simpleresolution             MSBuild の解決ではなく、ディレクトリベースの規則を使用してアセンブリの参照を解決します
// --highentropyva[+|-]           高エントロピ ASLR の有効化
// --subsystemversion:<string>    このアセンブリのサブシステム バージョンを指定してください
// --targetprofile:<string>       このアセンブリのターゲット フレームワーク プロファイルを指定してください。有効な値は mscorlib または netcore です。既定 - mscorlib
// --quotations-debug[+|-]        デバッグ情報を引用符で囲んで生成します
//
// TODO: 参照先を nuget にする
let fsharpc = env"ProgramFiles"/"Microsoft SDKs/F#/4.0/Framework/v4.0/fsc.exe"
// TODO: 参照先を nuget にする
let ilasm = env"windir"/"Microsoft.NET/Framework/v4.0.30319/ilasm.exe"

let (@.) = path.changeExtension

let testOnce sourceML = async {
    let sourceIL = sourceML@."il"
    let binaryML = sourceML@."ml.exe"
    let binaryFS = sourceML@."fs.exe"
    [sourceIL; binaryML; binaryFS] % item.remove

    exe "min-caml" "%s" (sourceML@.null)
    exe ilasm "-nologo -exe -output=%s libmincaml.il %s" binaryML sourceIL
    exe fsharpc "--nologo --mlcompatibility --nooptimizationdata --nointerfacedata --nowarn:0221 -o:%s libmincaml.fs %s" binaryFS (sourceML@."ml")

    let! resultMC = expression.invokeAsync binaryML ""
    let! resultFS = expression.invokeAsync binaryFS ""

    Assert.Equal(resultFS, resultMC)
}

let sourcesDirectory = pwd/"sources"
let sources() =
    cd sourcesDirectory
    gci "*.ml" |> select (fun x -> [|x.Name|])

[<Theory; MemberData "sources">]
let test sourceML =
    cd sourcesDirectory
    testOnce sourceML |> Async.StartAsTask
