module Asm

type type_kind = Class | ValueType
type cli_type =

    /// .this
    | This
    /// e.g. !1
    | TypeArgmentIndex of int

    /// sizeof<bool> = 1
    | Bool
    | Int32
    | Float64
    | Object
    | NativeInt
    | Array of cli_type

    /// e.g. class [moduleA]NamespaceA.ClassA/ClassB/Class
    | TypeName of type_kind * moduleName: Id.t list * nameSpace: Id.t list * nestedParents: Id.t list * typeName: Id.t * typeArgs: cli_type list

let tupleType types =
    let arity = List.length types
    TypeName(Class, ["mscorlib"], ["System"], [], sprintf "Tuple`%d" arity, types)

let unitType = TypeName(Class, ["mscorlib"], ["System"], [], "DBNull", [])

let rec cliType = function
    | Type.Array t -> Array <| cliType t
    | Type.Unit -> unitType
    | Type.Bool -> Bool
    | Type.Int -> Int32
    | Type.Float -> Float64
    | Type.Fun(argTypes, resultType) -> 
        let arity = List.length argTypes + 1
        let args = List.map cliType argTypes @ [cliType resultType]
        TypeName(Class, ["mscorlib"], ["System"], [], sprintf "Func`%d" arity, args)

    | Type.Tuple ts -> tupleType <| List.map cliType ts

    | Type.Var { contents = Some t } -> cliType t
    | Type.Var { contents = None } -> failwith "unexpected type 'Var'"


type call_conv = Instance | Static
type method_name =
    | MethodName of Id.l
    | Ctor

type method_ref = {
    call_conv: call_conv
    resultType: cli_type option
    declaringType: cli_type
    methodName: method_name
    argTypes: cli_type list
}

type field_ref = {
    fieldType: cli_type
    declaringType: cli_type
    name: Id.l
}

type t = exp list
and exp =
    | Label of Id.l

    | Ldarg_0
    | Ldarg of Id.t
    | Ldloc of Id.t
    | Stloc of Id.t
    | Dup
    | Pop

    | Ldnull
    | Ldc_I4 of int32
    | Ldc_R8 of float

    | Neg
    | Add
    | Sub
    | Mul
    | Div

    | Br of Id.l
    | Beq of Id.l
    | Ble of Id.l

    | Call of isTail: bool * method_ref
    | Ret

    | Ldelem of Type.t
    | Stelem of Type.t

    /// newobj instance void $declaringType::.ctor($argTypes)
    | Newobj of declaringType: cli_type * argTypes: cli_type list
    | Ldfld of field_ref
    | Stfld of field_ref
    | Ldsfld of field_ref

    /// callvirt instance $resultType $declaringType::$methodName($argTypes)
    | Callvirt of isTail: bool * method_ref
    | Ldftn of method_ref

let methodRef(call_conv, resultType, declaringType, methodName, argTypes) = {
    call_conv = call_conv
    resultType = resultType
    declaringType = declaringType
    methodName = MethodName methodName
    argTypes = argTypes
}
let ctorRef(declaringType, argTypes) = {
    call_conv = Instance
    resultType = None
    declaringType = declaringType
    methodName = Ctor
    argTypes = argTypes
}
let ldftn(resultType, declaringType, name, argTypes) =
    Ldftn <| methodRef(Instance, resultType, declaringType, Id.L name, argTypes)

let call(tail, callconv, resultType, declaringType, name, argTypes) =
    Call(tail, methodRef(callconv, resultType, declaringType, name, argTypes))

let callvirt(tail, resultType, declaringType, name, argTypes) =
    Callvirt(tail, methodRef(Instance, resultType, declaringType, Id.L name, argTypes))

type accesibility = Public | Default
type method_body = {
    isEntrypoint: bool

    /// .locals init (...)
    locals: (Id.t * Type.t) list
    opcodes: t
}

type method_def = {
    access: accesibility
    isSpecialname: bool
    isRtspecialname: bool
    callconv: call_conv
    /// None = void
    resultType: cli_type option
    name: method_name
    args: (Id.t * Type.t) list
    isForwardref: bool
    body: method_body
}

type custom = {
    ctor: method_ref
    args: unit list
    namedArgs: unit list
}
type field_def = {
    access: accesibility
    fieldType: cli_type
    name: Id.l
}
type class_decl =
    | Custom of custom
    | Method of method_def
    | Field of field_def
    | NestedClass of class_def

/// default accessibility
and class_def = {
    isSealed: bool
    isBeforefieldinit: bool
    name: Id.l
    body: class_decl list
}

type prog = Prog of class_decl list * entrypoint: method_def

//
//type id_or_imm = V of Id.t | C of int
//type t = (* 命令の列 (caml2html: sparcasm_t) *)
//  | Ans of exp
//  | Let of (Id.t * Type.t) * exp * t
//and exp = (* 一つ一つの命令に対応する式 (caml2html: sparcasm_exp) *)
//  | Nop
//  | Set of int
//  | SetF of float
//  | SetL of Id.l
//  | Mov of Id.t
//  | Neg of Id.t
//  | Add of Id.t * id_or_imm
//  | Sub of Id.t * id_or_imm
//  | Ld of Id.t * id_or_imm * int
//  | St of Id.t * Id.t * id_or_imm * int
//  | FMovD of Id.t
//  | FNegD of Id.t
//  | FAddD of Id.t * Id.t
//  | FSubD of Id.t * Id.t
//  | FMulD of Id.t * Id.t
//  | FDivD of Id.t * Id.t
//  | LdDF of Id.t * id_or_imm * int
//  | StDF of Id.t * Id.t * id_or_imm * int
//  | Comment of string
//  (* virtual instructions *)
//  | IfEq of Id.t * id_or_imm * t * t
//  | IfLE of Id.t * id_or_imm * t * t
//  | IfGE of Id.t * id_or_imm * t * t (* 左右対称ではないので必要 *)
//  | IfFEq of Id.t * Id.t * t * t
//  | IfFLE of Id.t * Id.t * t * t
//  (* closure address, integer arguments, and float arguments *)
//  | CallCls of Id.t * Id.t list * Id.t list
//  | CallDir of Id.l * Id.t list * Id.t list
//  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 (caml2html: sparcasm_save) *)
//  | Restore of Id.t (* スタック変数から値を復元 (caml2html: sparcasm_restore) *)
//type fundef = { name : Id.l; args : (Id.t * Type.t) list; body : t; ret : Type.t }
//(* プログラム全体 = 浮動小数点数テーブル + トップレベル関数 + メインの式 (caml2html: sparcasm_prog) *)
//type prog = Prog of fundef list * t
//
//let fletd(x, e1, e2) = Let((x, Type.Float), e1, e2)
//let seq(e1, e2) = Let((Id.gentmp Type.Unit, Type.Unit), e1, e2)
//
//let regs = (* Array.init 16 (fun i -> Printf.sprintf "%%r%d" i) *)
//  [| "%eax"; "%ebx"; "%ecx"; "%edx"; "%esi"; "%edi" |]
//let fregs = Array.init 8 (fun i -> Printf.sprintf "%%xmm%d" i)
//let allregs = Array.to_list regs
//let allfregs = Array.to_list fregs
//let reg_cl = regs.(Array.length regs - 1) (* closure address (caml2html: sparcasm_regcl) *)
//(*
//let reg_sw = regs.(Array.length regs - 1) (* temporary for swap *)
//let reg_fsw = fregs.(Array.length fregs - 1) (* temporary for swap *)
//*)
//let reg_sp = "%ebp" (* stack pointer *)
//let reg_hp = "min_caml_hp" (* heap pointer (caml2html: sparcasm_reghp) *)
//(* let reg_ra = "%eax" (* return address *) *)
//let is_reg x = (String.get x 0 = '%' || x = reg_hp)
//
//let rec type_name = function
//    | Type.Array t -> type_name t ^ "[]"
//    | Type.Bool -> "bool"
//    | Type.Float -> "float64"
//    | Type.Fun(args, result) ->
//        let arity = List.length args + 1 in
//        "class System.Func`" ^ string_of_int arity ^ "<" ^ type_name_many (args @ [result]) ^ ">"
//
//    | Type.Int -> "int32"
//    | Type.Tuple ts ->
//        let arity = List.length ts in
//        "class System.Tuple`" ^ string_of_int arity ^ "<" ^ type_name_many ts ^ ">"
//
//    | Type.Unit -> "object"
//    | Type.Var { contents = Some t } -> type_name t
//    | Type.Var { contents = None } -> failwith "unexpected type 'Var'"
//
//and type_name_many args = String.concat ", " (List.map type_name args)
//
//(* super-tenuki *)
//let rec remove_and_uniq xs = function
//  | [] -> []
//  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
//  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys
//
//(* free variables in the order of use (for spilling) (caml2html: sparcasm_fv) *)
//let fv_id_or_imm = function V(x) -> [x] | _ -> []
//module Fv = struct
//    let rec fv_exp = function
//      | Nop | Set(_) | SetF(_) | SetL(_) | Comment(_) | Restore(_) -> []
//      | Mov(x) | Neg(x) | FMovD(x) | FNegD(x) | Save(x, _) -> [x]
//      | Add(x, y') | Sub(x, y') | Ld(x, y', _) | LdDF(x, y', _) -> x :: fv_id_or_imm y'
//      | St(x, y, z', _) | StDF(x, y, z', _) -> x :: y :: fv_id_or_imm z'
//      | FAddD(x, y) | FSubD(x, y) | FMulD(x, y) | FDivD(x, y) -> [x; y]
//      | IfEq(x, y', e1, e2) | IfLE(x, y', e1, e2) | IfGE(x, y', e1, e2) -> x :: fv_id_or_imm y' @ remove_and_uniq S.empty (fv e1 @ fv e2) (* uniq here just for efficiency *)
//      | IfFEq(x, y, e1, e2) | IfFLE(x, y, e1, e2) -> x :: y :: remove_and_uniq S.empty (fv e1 @ fv e2) (* uniq here just for efficiency *)
//      | CallCls(x, ys, zs) -> x :: ys @ zs
//      | CallDir(_, ys, zs) -> ys @ zs
//    and fv = function
//      | Ans(exp) -> fv_exp exp
//      | Let((x, t), exp, e) ->
//          fv_exp exp @ remove_and_uniq (S.singleton x) (fv e)
//end
//let fv e = remove_and_uniq S.empty (Fv.fv e)
//
//let rec concat e1 xt e2 =
//  match e1 with
//  | Ans(exp) -> Let(xt, exp, e2)
//  | Let(yt, exp, e1') -> Let(yt, exp, concat e1' xt e2)
//
//let align i = (if i mod 8 = 0 then i else i + 4)
