(*
 * Copyright 2016, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure Absyn_Serial =
struct

open Absyn

datatype serial = Nm of string * serial list | Q of string

fun opt_serial f (SOME v) = Nm ("SOME", [f v])
  | opt_serial f NONE = Nm ("NONE", [])

fun list_serial f xs = Nm ("", map f xs)

fun pair_serial nm f g (x, y) = Nm (nm, [f x, g y])

fun b2s true = "true"
  | b2s false = "false"

fun ty_serial f (Signed ity) = Nm ("Signed", [Q (inttyname ity)])
  | ty_serial f (Unsigned ity) = Nm ("Unsigned", [Q (inttyname ity)])
  | ty_serial f Bool = Nm ("Bool", [])
  | ty_serial f PlainChar = Nm ("PlainChar", [])
  | ty_serial f (StructTy s) = Nm ("StructTy", [Q s])
  | ty_serial f (EnumTy so) = Nm ("EnumTy", [opt_serial Q so])
  | ty_serial f (Ptr ty) = Nm ("Ptr", [ty_serial f ty])
  | ty_serial f (Array (ty, co)) = Nm ("Array",
        [ty_serial f ty, opt_serial f co])
  | ty_serial f (Bitfield (b, c)) = Nm ("Bitfield", [Q (b2s b), f c])
  | ty_serial f (Ident s) = Nm ("Ident", [Q s])
  | ty_serial f (Function (ty, xs)) = Nm ("Function", [ty_serial f ty,
    list_serial (ty_serial f) xs])
  | ty_serial f Void = Nm ("Void", [])

val int_ctype_serial = ty_serial (fn i => Q (Int.toString i))

fun radix_string (StringCvt.BIN) = "BIN"
  | radix_string (StringCvt.OCT) = "OCT"
  | radix_string (StringCvt.DEC) = "DEC"
  | radix_string (StringCvt.HEX) = "HEX"

fun literal_serial (STRING_LIT s) = Q s
  | literal_serial (NUMCONST dets) = Nm ("NUMCONST",
    [Q (IntInf.toString (#value dets)), Q (#suffix dets),
        Q (radix_string (#base dets))])

fun vi_serial vi = opt_serial (fn (ty, _) => int_ctype_serial ty) (! vi)

fun expr_serial e = let
in
    Nm (expr_string e,
    case enode e of
      BinOp (t, e, e2) => [Q (binopname t), expr_serial e, expr_serial e2]
    | UnOp (t, e) => [Q (unopname t), expr_serial e]
    | CondExp (e1, e2, e3) => map expr_serial [e1, e2, e3]
    | Constant nc => [literal_serial (node nc)]
    | Var (_, vi) => [vi_serial vi]
    | StructDot (e, s) => [expr_serial e, Q s]
    | ArrayDeref (e1, e2) => map expr_serial [e1, e2]
    | Deref e => [expr_serial e]
    | TypeCast (t, e) => [ty_serial expr_serial (node t), expr_serial e]
    | Sizeof e => [expr_serial e]
    | SizeofTy t => [ty_serial expr_serial (node t)]
    | EFnCall (e, es) => map expr_serial (e :: es)
    | CompLiteral (ty, xs) => [ty_serial expr_serial ty,
        list_serial (pair_serial "" (list_serial desig_serial) init_serial) xs]
    | Arbitrary t => [ty_serial expr_serial t]
    | MKBOOL e => [expr_serial e]
    | _ => [Q "[whoa! Unknown expr type]"]
    )
end
and init_serial (InitE e) = Nm ("InitE", [expr_serial e])
  | init_serial (InitList xs) = Nm ("InitList",
        map (pair_serial "" (list_serial desig_serial) init_serial) xs)
and desig_serial (DesignE e) = Nm ("DesignE", [expr_serial e])
  | desig_serial (DesignFld s) = Nm ("DesignFld", [Q s])

val expr_ctype_serial = ty_serial expr_serial

val varspec_serial = pair_serial "VarSpec" expr_ctype_serial (Q o node)

fun gcc_att_serial (GCC_AttribID s) = Nm ("GCC_AttribID", [Q s])
  | gcc_att_serial (GCC_AttribFn (s, xs)) = Nm ("GCC_AttribFn",
    [Q s, list_serial expr_serial xs])
  | gcc_att_serial (OWNED_BY s) = Nm ("OWNED_BY", [Q s])

fun fnspec_serial (fnspec s) = Nm ("fnspec", [Q (node s)])
  | fnspec_serial (relspec s) = Nm ("relspec", [Q (node s)])
  | fnspec_serial (fn_modifies ss) = Nm ("fn_modifies", map Q ss)
  | fnspec_serial didnt_translate = Nm ("DONT_TRANSLATE", [])
  | fnspec_serial (gcc_attribs atts)
    = Nm ("gcc_attribs", map gcc_att_serial atts)

fun storage_serial SC_EXTERN = Q "SC_EXTERN"
  | storage_serial SC_STATIC = Q "SC_STATIC"
  | storage_serial SC_AUTO = Q "SC_AUTO"
  | storage_serial SC_REGISTER = Q "SC_REGISTER"
  | storage_serial SC_THRD_LOCAL = Q "SC_THRD_LOCAL"

fun decl_serial (VarDecl (ty, s, cls, init, atts))
    = Nm ("VarDecl", [varspec_serial (ty, s),
        list_serial storage_serial cls,
        opt_serial init_serial init, list_serial gcc_att_serial atts])
  | decl_serial (StructDecl (s, xs)) = Nm ("StructDecl", [Q (node s),
        list_serial varspec_serial xs])
  | decl_serial (TypeDecl xs) = Nm ("TypeDecl", map varspec_serial xs)
  | decl_serial (ExtFnDecl dets) = Nm ("ExtFnDecl",
    [varspec_serial (#rettype dets, #name dets),
        list_serial (pair_serial "VarSpecO" expr_ctype_serial
            (opt_serial Q)) (#params dets),
        list_serial fnspec_serial (#specs dets)])
  | decl_serial (EnumDecl (so, xs)) = Nm ("EnumDecl",
        [opt_serial Q (node so), list_serial (pair_serial "EnumElt" (Q o node)
            (opt_serial expr_serial)) xs])

fun stmt_serial s = let
    fun os2s (SOME s) = "Some (" ^ s ^ ")"
      | os2s NONE = "None"
    fun asm_serial1 (so, s, e) = Nm ("A1", [opt_serial Q so, Q s, expr_serial e])
    fun asm_serial2 (b : asmblock) = Nm ("A2", [Q (#head b),
        Nm ("M1", map asm_serial1 (#mod1 b)),
        Nm ("M2", map asm_serial1 (#mod2 b)),
        Nm ("M3", map Q (#mod3 b))])
    fun sw_serial (eos, bis) = Nm ("Sw", [list_serial (opt_serial expr_serial) eos,
        list_serial bi_serial bis])
in
    Nm (stmt_type s,
    case snode s of
      Assign (e, e2) => map expr_serial [e, e2]
    | AssignFnCall (lv, fnm, args) => opt_serial expr_serial lv
        :: map expr_serial (fnm :: args)
    | EmbFnCall (lv, fnm, args) => map expr_serial (lv :: fnm :: args)
    | Block bis => map bi_serial bis
    | Chaos e => [expr_serial e]
    | While (e, s, stmt) => [expr_serial e, opt_serial Q (Option.map node s),
        stmt_serial stmt]
    | Trap (BreakT, stmt) => [Q "Break", stmt_serial stmt]
    | Trap (ContinueT, stmt) => [Q "Continue", stmt_serial stmt]
    | Return e => [opt_serial expr_serial e]
    | ReturnFnCall (e, args) => map expr_serial (e :: args)
    | Break => []
    | Continue => []
    | IfStmt (e, lhs, rhs) => [expr_serial e, stmt_serial lhs, stmt_serial rhs]
    | Switch (e, sws) => expr_serial e :: map sw_serial sws
    | EmptyStmt => []
    | Auxupd s => [Q s]
    | Spec ((a, b), stmts, c) => [Q a, Q b, Q c] @  map stmt_serial stmts
    | AsmStmt dets => [Q (b2s (#volatilep dets)), asm_serial2 (#asmblock dets)]
    | LocalInit e => [expr_serial e]
    | _ => [Q "[whoa!  Unknown stmt type]"]
    )
end
and bi_serial (Absyn.BI_Decl d) = decl_serial (node d)
  | bi_serial (Absyn.BI_Stmt s) = stmt_serial s

fun line_ind 0 s = s
  | line_ind i s = "  " ^ line_ind (i - 1) s
fun lines_serial_ind i (Nm ("", [])) = [line_ind i "[],"]
  | lines_serial_ind i (Nm (s, [])) = [line_ind i (s ^ ",")]
  | lines_serial_ind i (Nm (s, ts)) = [line_ind i (s ^ " [")]
    @ List.concat (map (lines_serial_ind (i + 1)) ts) @ [line_ind i ("],")]
  | lines_serial_ind i (Q s) = [line_ind i ("\"" ^ s ^ "\"")]

fun lines_serial ser = lines_serial_ind 0 ser

end;



