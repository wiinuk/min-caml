namespace MinCaml.Compiler.Test

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
        | Cls(_, { entry = Id.L entry; actual_fv = actual_fv }) ->
            yield entry
            yield!
                actual_fv
                |> Seq.map (fun (Id.L l, e) -> seq {
                    yield l
                    yield " = "
                    yield! exp (i + 1) e 
                })
                |> wrap "{" ", " "}"

        | LetCls(xt, { entry = Id.L entry; actual_fv = actual_fv }, e2) ->
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
