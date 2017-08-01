#load "shell.fsx"
open ExtraOperators

/// 使い方: PEverify <イメージ ファイル> [オプション]
///
/// オプション:
/// /IL           PE 構造および IL のみを確認します
/// /MD           PE 構造およびメタデータのみを確認します
/// /TRANSPARENT  Transparent メソッドのみを確認します。
/// /UNIQUE       反復するエラー コードを無視します
/// /HRESULT      エラー コードを 16 進形式で表示します
/// /CLOCK        確認時間を計測および報告します
/// /IGNORE=<16 進コード>[,<16 進コード>...]  指定されたエラー コードを無視します
/// /IGNORE=@<ファイル名>                     <ファイル名> で指定されたエラー コードを無視します
/// /QUIET        ファイルおよび状態のみを表示します。すべてのエラーは表示しません。
/// /VERBOSE      IL 確認のエラー メッセージで追加情報を表示します。
/// /NOLOGO       製品のバージョンおよび著作権情報を表示しません。
///
/// メモ: 既定では、まず MD を確認し、エラーがなければ、IL を確認します。/MD /IL オプションが指定されている場合、IL の確認は MD の確認でエラーが見つかっても行われます。
let peverify = env"ProgramFiles"/"Microsoft SDKs/Windows/v10.0A/bin/NETFX 4.6.1 Tools/PEVerify.exe"

let diagnostic source =
    let temp = System.IO.Path.GetTempFileName()
    try
        host.out "%s --> %s" source temp
        exe "ilasm" "-nologo -quiet -exe -output=%s dotnet/libmincaml.il %s" temp source
        exe peverify "%s /NOLOGO /VERBOSE" temp
        host.out "--------------------------------"
        host.out " "
    finally
        item.remove temp

ChildItem.Get("*.il", Recurse)
    |> Seq.filter (fun x -> x.Name <> "libmincaml.il")
    |> Seq.iter (string >> diagnostic)
