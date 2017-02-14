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



    Id.counter := 0
    Typing.extenv := M.empty

(
    Id.counter := 0;
    Typing.extenv := M.empty;
"
let rec mul l m n a b c =
  let rec loop1 i =
    if i < 0 then () else
    let rec loop2 j =
      if j < 0 then () else
      let rec loop3 k =
	if k < 0 then () else
	(c.(i).(j) <- c.(i).(j) +. a.(i).(k) *. b.(k).(j);
	 loop3 (k - 1)) in
      loop3 (m - 1);
      loop2 (j - 1) in
    loop2 (n - 1);
    loop1 (i - 1) in
  loop1 (l - 1) in
let dummy = Array.make 0 0. in
let rec make m n =
  let mat = Array.make m dummy in
  let rec init i =
    if i < 0 then () else
    (mat.(i) <- Array.make n 0.;
     init (i - 1)) in
  init (m - 1);
  mat in
let a = make 2 3 in
let b = make 3 2 in
let c = make 2 2 in
a.(0).(0) <- 1.; a.(0).(1) <- 2.; a.(0).(2) <- 3.;
a.(1).(0) <- 4.; a.(1).(1) <- 5.; a.(1).(2) <- 6.;
b.(0).(0) <- 7.; b.(0).(1) <- 8.;
b.(1).(0) <- 9.; b.(1).(1) <- 10.;
b.(2).(0) <- 11.; b.(2).(1) <- 12.;
mul 2 3 2 a b c;
print_int (truncate (c.(0).(0)));
print_newline ();
print_int (truncate (c.(0).(1)));
print_newline ();
print_int (truncate (c.(1).(0)));
print_newline ();
print_int (truncate (c.(1).(1)));
print_newline ()
"
)
|> closure 1000
// |> ClosurePrinter.prog |> String.concat ""
(*
loop3.153 : (int) => () (k.154 : int) {a.144 : [[float]], b.145 : [[float]], c.146 : [[float]], i.148 : int, j.151 : int} =
    Ti128.155 : int = 0
    if Ti128.155 <= k.154 then
        Ta129.157 : [float] = c.146[i.148]
        Ta130.160 : [float] = c.146[i.148]
        Td131.159 : float = Ta130.160[j.151]
        Ta132.163 : [float] = a.144[i.148]
        Td133.162 : float = Ta132.163[k.154]
        Ta134.165 : [float] = b.145[k.154]
        Td135.164 : float = Ta134.165[j.151]
        Td136.161 : float = Td133.162 *. Td135.164
        Td137.158 : float = Td131.159 +. Td136.161
        Tu1.156 : () = Ta129.157[j.151] <- Td137.158
        Ti138.167 : int = 1
        Ti139.166 : int = k.154 - Ti138.167
        loop3.153#(Ti139.166)
    else
        ()
loop2.150 : (int) => () (j.151 : int) {a.144 : [[float]], b.145 : [[float]], c.146 : [[float]], i.148 : int, m.142 : int} =
    Ti123.152 : int = 0
    if Ti123.152 <= j.151 then
        loop3.153 : (int) => () = loop3.153{a.144, b.145, c.146, i.148, j.151}
        Ti124.170 : int = 1
        Ti125.169 : int = m.142 - Ti124.170
        Tu2.168 : () = loop3.153#(Ti125.169)
        Ti126.172 : int = 1
        Ti127.171 : int = j.151 - Ti126.172
        loop2.150#(Ti127.171)
    else
        ()
loop1.147 : (int) => () (i.148 : int) {a.144 : [[float]], b.145 : [[float]], c.146 : [[float]], m.142 : int, n.143 : int} =
    Ti118.149 : int = 0
    if Ti118.149 <= i.148 then
        loop2.150 : (int) => () = loop2.150{a.144, b.145, c.146, i.148, m.142}
        Ti119.175 : int = 1
        Ti120.174 : int = n.143 - Ti119.175
        Tu3.173 : () = loop2.150#(Ti120.174)
        Ti121.177 : int = 1
        Ti122.176 : int = i.148 - Ti121.177
        loop1.147#(Ti122.176)
    else
        ()
mul.140 : (int, int, int, [[float]], [[float]], [[float]]) => () (l.141 : int, m.142 : int, n.143 : int, a.144 : [[float]], b.145 : [[float]], c.146 : [[float]]) {} =
    loop1.147 : (int) => () = loop1.147{a.144, b.145, c.146, m.142, n.143}
    Ti116.179 : int = 1
    Ti117.178 : int = l.141 - Ti116.179
    loop1.147#(Ti117.178)
init.187 : (int) => () (i.188 : int) {mat.186 : [[float]], n.185 : int} =
    Ti111.189 : int = 0
    if Ti111.189 <= i.188 then
        Td112.192 : float = 0
        Ta113.191 : [float] = min_caml_create_float_array(n.185, Td112.192)
        Tu4.190 : () = mat.186[i.188] <- Ta113.191
        Ti114.194 : int = 1
        Ti115.193 : int = i.188 - Ti114.194
        init.187#(Ti115.193)
    else
        ()
make.183 : (int, int) => [[float]] (m.184 : int, n.185 : int) {dummy.180 : [float]} =
    mat.186 : [[float]] = min_caml_create_array(m.184, dummy.180)
    init.187 : (int) => () = init.187{mat.186, n.185}
    Ti109.197 : int = 1
    Ti110.196 : int = m.184 - Ti109.197
    Tu5.195 : () = init.187#(Ti110.196)
    mat.186
do
    Ti26.181 : int = 0
    Td27.182 : float = 0
    dummy.180 : [float] = min_caml_create_float_array(Ti26.181, Td27.182)
    make.183 : (int, int) => [[float]] = make.183{dummy.180}
    Ti28.199 : int = 2
    Ti29.200 : int = 3
    a.198 : [[float]] = make.183#(Ti28.199, Ti29.200)
    Ti30.202 : int = 3
    Ti31.203 : int = 2
    b.201 : [[float]] = make.183#(Ti30.202, Ti31.203)
    Ti32.205 : int = 2
    Ti33.206 : int = 2
    c.204 : [[float]] = make.183#(Ti32.205, Ti33.206)
    Ti34.209 : int = 0
    Ta35.208 : [float] = a.198[Ti34.209]
    Ti36.210 : int = 0
    Td37.211 : float = 1
    Tu25.207 : () = Ta35.208[Ti36.210] <- Td37.211
    Ti38.214 : int = 0
    Ta39.213 : [float] = a.198[Ti38.214]
    Ti40.215 : int = 1
    Td41.216 : float = 2
    Tu24.212 : () = Ta39.213[Ti40.215] <- Td41.216
    Ti42.219 : int = 0
    Ta43.218 : [float] = a.198[Ti42.219]
    Ti44.220 : int = 2
    Td45.221 : float = 3
    Tu23.217 : () = Ta43.218[Ti44.220] <- Td45.221
    Ti46.224 : int = 1
    Ta47.223 : [float] = a.198[Ti46.224]
    Ti48.225 : int = 0
    Td49.226 : float = 4
    Tu22.222 : () = Ta47.223[Ti48.225] <- Td49.226
    Ti50.229 : int = 1
    Ta51.228 : [float] = a.198[Ti50.229]
    Ti52.230 : int = 1
    Td53.231 : float = 5
    Tu21.227 : () = Ta51.228[Ti52.230] <- Td53.231
    Ti54.234 : int = 1
    Ta55.233 : [float] = a.198[Ti54.234]
    Ti56.235 : int = 2
    Td57.236 : float = 6
    Tu20.232 : () = Ta55.233[Ti56.235] <- Td57.236
    Ti58.239 : int = 0
    Ta59.238 : [float] = b.201[Ti58.239]
    Ti60.240 : int = 0
    Td61.241 : float = 7
    Tu19.237 : () = Ta59.238[Ti60.240] <- Td61.241
    Ti62.244 : int = 0
    Ta63.243 : [float] = b.201[Ti62.244]
    Ti64.245 : int = 1
    Td65.246 : float = 8
    Tu18.242 : () = Ta63.243[Ti64.245] <- Td65.246
    Ti66.249 : int = 1
    Ta67.248 : [float] = b.201[Ti66.249]
    Ti68.250 : int = 0
    Td69.251 : float = 9
    Tu17.247 : () = Ta67.248[Ti68.250] <- Td69.251
    Ti70.254 : int = 1
    Ta71.253 : [float] = b.201[Ti70.254]
    Ti72.255 : int = 1
    Td73.256 : float = 10
    Tu16.252 : () = Ta71.253[Ti72.255] <- Td73.256
    Ti74.259 : int = 2
    Ta75.258 : [float] = b.201[Ti74.259]
    Ti76.260 : int = 0
    Td77.261 : float = 11
    Tu15.257 : () = Ta75.258[Ti76.260] <- Td77.261
    Ti78.264 : int = 2
    Ta79.263 : [float] = b.201[Ti78.264]
    Ti80.265 : int = 1
    Td81.266 : float = 12
    Tu14.262 : () = Ta79.263[Ti80.265] <- Td81.266
    Ti82.268 : int = 2
    Ti83.269 : int = 3
    Ti84.270 : int = 2
    Tu13.267 : () = mul.140(Ti82.268, Ti83.269, Ti84.270, a.198, b.201, c.204)
    Ti85.275 : int = 0
    Ta86.274 : [float] = c.204[Ti85.275]
    Ti87.276 : int = 0
    Td88.273 : float = Ta86.274[Ti87.276]
    Ti89.272 : int = min_caml_truncate(Td88.273)
    Tu12.271 : () = min_caml_print_int(Ti89.272)
    Tu90.278 : () = ()
    Tu11.277 : () = min_caml_print_newline(Tu90.278)
    Ti91.283 : int = 0
    Ta92.282 : [float] = c.204[Ti91.283]
    Ti93.284 : int = 1
    Td94.281 : float = Ta92.282[Ti93.284]
    Ti95.280 : int = min_caml_truncate(Td94.281)
    Tu10.279 : () = min_caml_print_int(Ti95.280)
    Tu96.286 : () = ()
    Tu9.285 : () = min_caml_print_newline(Tu96.286)
    Ti97.291 : int = 1
    Ta98.290 : [float] = c.204[Ti97.291]
    Ti99.292 : int = 0
    Td100.289 : float = Ta98.290[Ti99.292]
    Ti101.288 : int = min_caml_truncate(Td100.289)
    Tu8.287 : () = min_caml_print_int(Ti101.288)
    Tu102.294 : () = ()
    Tu7.293 : () = min_caml_print_newline(Tu102.294)
    Ti103.299 : int = 1
    Ta104.298 : [float] = c.204[Ti103.299]
    Ti105.300 : int = 1
    Td106.297 : float = Ta104.298[Ti105.300]
    Ti107.296 : int = min_caml_truncate(Td106.297)
    Tu6.295 : () = min_caml_print_int(Ti107.296)
    Tu108.301 : () = ()
    min_caml_print_newline(Tu108.301)
*)
|> Tree.f
|> StackAlloc.f

// |> TreePrinter.prog |> String.concat ""
(*
f.9 : (int) => () (n.10 : int) {} =
    if 0 <= n.10 then
        Tu1.12 : () = (min_caml_print_int : (int) => ())(n.10)
        a.13 : [(int) => ()] = (min_caml_create_array : (int, float) => [(int) => ()])(1, f.9)
        a.13 `get` 0#(n.10 - 1)
    else
        ()
do
    f.9 : (int) => () = f.9{}
    f.9#(9)
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

exe peverify "matmul.ml.exe /verbose"

exe ildasm "matmul.ml.exe -text"

exe ilasm "even-odd.il"

exe "matmul.ml.exe" ""
exe "matmul.fs.exe" ""