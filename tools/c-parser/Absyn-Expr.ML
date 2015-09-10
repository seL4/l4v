(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure ExprDatatype =
struct

type numliteral_info =
     {value: IntInf.int, suffix : string, base : StringCvt.radix}
     (* use of IntInf makes no difference in Poly, but is useful in mlton *)

type 'a wrap = 'a RegionExtras.wrap
type 'a ctype = 'a CType.ctype

datatype literalconstant_node =
         NUMCONST of numliteral_info
       | STRING_LIT of string
type literalconstant = literalconstant_node wrap

datatype binoptype =
         LogOr | LogAnd | Equals | NotEquals | BitwiseAnd | BitwiseOr
       | BitwiseXOr
       | Lt | Gt | Leq | Geq | Plus | Minus | Times | Divides | Modulus
       | RShift | LShift

datatype unoptype = Negate | Not | Addr | BitNegate

type var_info = (int CType.ctype * more_info) option ref

datatype expr_node =
         BinOp of binoptype * expr * expr
       | UnOp of unoptype * expr
       | CondExp of expr * expr * expr
       | Constant of literalconstant
       | Var of string * var_info
       | StructDot of expr * string
       | ArrayDeref of expr * expr
       | Deref of expr
       | TypeCast of expr ctype wrap * expr
       | Sizeof of expr
       | SizeofTy of expr ctype wrap
       | EFnCall of expr * expr list
       | CompLiteral of expr ctype * (designator list * initializer) list
       | Arbitrary of expr ctype
       | MKBOOL of expr
and expr = E of expr_node wrap
and initializer =
    InitE of expr
  | InitList of (designator list * initializer) list
and designator =
    DesignE of expr
  | DesignFld of string


datatype ecenv =
         CE of {enumenv : (IntInf.int * string option) Symtab.table,
                          (* lookup is from econst name to value and the
                             name of the type it belongs to, if any
                             (they can be anonymous) *)
                typing : expr -> int ctype,
                structsize : string -> int}

end (* struct *)

signature EXPR =
sig

  datatype binoptype = datatype ExprDatatype.binoptype
  datatype unoptype = datatype ExprDatatype.unoptype
  datatype expr_node = datatype ExprDatatype.expr_node
  datatype initializer = datatype ExprDatatype.initializer
  datatype designator = datatype ExprDatatype.designator
  datatype literalconstant_node = datatype ExprDatatype.literalconstant_node
  type expr
  type numliteral_info = ExprDatatype.numliteral_info
  type literalconstant = ExprDatatype.literalconstant

  val unopname : unoptype -> string
  val unop_compare : unoptype * unoptype -> order

  val binopname : binoptype -> string
  val binop_compare : binoptype * binoptype -> order
  val expr_string : expr -> string

  val numconst_type : numliteral_info -> 'a CType.ctype (* can raise Subscript *)
  val eval_litconst : literalconstant -> IntInf.int * 'a CType.ctype

  val enode : expr -> expr_node
  val eleft : expr -> SourcePos.t
  val eright : expr -> SourcePos.t
  val ewrap : expr_node * SourcePos.t * SourcePos.t -> expr
  val ebogwrap : expr_node -> expr
  val eFail : expr * string -> exn
  val expr_compare : expr * expr -> order

  val is_number : expr -> bool
  val fncall_free : expr -> bool
  val eneeds_sc_protection : expr -> bool

  val expr_int : IntInf.int -> expr
  val eval_binop :
      (SourcePos.t * SourcePos.t) ->
      binoptype * (IntInf.int * 'a CType.ctype) * (IntInf.int * 'a CType.ctype) ->
      IntInf.int * 'a CType.ctype


  datatype ecenv = datatype ExprDatatype.ecenv (* "enumerated constant environment" *)
  val eclookup : ecenv -> string -> (IntInf.int * string option) option
  val constify_abtype : ecenv -> expr CType.ctype -> int CType.ctype
  val consteval : ecenv -> expr -> IntInf.int


end

structure Expr : EXPR =
struct

open RegionExtras
open CType
open ExprDatatype

(* can raise Subscript *)
fun numconst_type {value,base,suffix} = let
  val suffix = String.translate (str o Char.toLower) suffix
  val suffixU = CharVector.exists (fn c => c = #"u") suffix
  val suffixLL = String.isPrefix "ll" suffix orelse
                 String.isSuffix "ll" suffix
  val suffixL = (String.isPrefix "l" suffix orelse
                 String.isSuffix "l" suffix)
  val type_index = if suffixLL then 4 else if suffixL then 2 else 0
  (* where to start looking in the typesequence *)
  val typesequence = [Signed Int, Unsigned Int,
                      Signed Long, Unsigned Long,
                      Signed LongLong, Unsigned LongLong]
  fun search i = let
    val candidate = List.nth(typesequence, i)
  in
    if suffixU andalso is_signed candidate then search (i + 1)
    else if base = StringCvt.DEC andalso not suffixU andalso
            not (is_signed candidate)
    then search (i + 1)
    else if imax candidate >= value then candidate
    else search (i + 1)
  end
in
  search type_index
end

fun eval_litconst lc = let
  val fi = IntInf.fromInt
in
  case node lc of
    NUMCONST nc => (#value nc, numconst_type nc)
  | STRING_LIT _ => (Feedback.errorStr'(left lc, right lc,
                                        "Don't evaluate string literals!");
                     (fi 1, Signed Int))
end

fun unopname opn =
    case opn of
        Negate => "-"
      | Not => "!"
      | Addr => "&"
      | BitNegate => "~"
val unop_compare = inv_img_cmp unopname String.compare

fun binopname opn =
    case opn of
      Lt => "<"
    | Gt => ">"
    | Leq => "<="
    | Geq => ">="
    | Equals => "=="
    | NotEquals => "!="
    | LogOr => "||"
    | LogAnd => "&&"
    | Plus => "+"
    | Times => "*"
    | Minus => "-"
    | Divides => "/"
    | BitwiseAnd => "&"
    | BitwiseOr => "|"
    | BitwiseXOr => "^"
    | RShift => ">>"
    | LShift => "<<"
    | Modulus => "%"

val binop_compare = inv_img_cmp binopname String.compare

type var_info = (int ctype * more_info) option ref


fun eleft (E w) = valOf (Region.left (Region.Wrap.region w))
    handle Option => bogus
fun eright (E w) = valOf (Region.right (Region.Wrap.region w))
    handle Option => bogus
fun enode (E w) = node w
fun eregion (E w) = Region.Wrap.region w
fun ewrap (n, l, r) = E (wrap(n,l,r))
fun ebogwrap en = E (bogwrap en)
fun eFail (e, s) = Fail (Region.toString (eregion e) ^ ": " ^ s)

fun fncall_free e =
    case enode e of
      BinOp(_, e1, e2) => fncall_free e1 andalso fncall_free e2
    | UnOp(_, e) => fncall_free e
    | CondExp(e1,e2,e3) => fncall_free e1 andalso fncall_free e2 andalso
                           fncall_free e3
    | StructDot(e, _) => fncall_free e
    | ArrayDeref(e1, e2) => fncall_free e1 andalso fncall_free e2
    | Deref e => fncall_free e
    | TypeCast(_, e) => fncall_free e
    | EFnCall _ => false
    | CompLiteral (_, dilist) => List.all dinit_fncall_free dilist
    | _ => true
and dinit_fncall_free (dis, init) =
    List.all difncall_free dis andalso init_fncall_free init
and difncall_free (DesignE e) = fncall_free e
  | difncall_free (DesignFld _) = true
and init_fncall_free (InitE e) = fncall_free e
  | init_fncall_free (InitList dis) = List.all dinit_fncall_free dis

fun is_number e =
    case enode e of
      Constant litw => (case node litw of NUMCONST _ => true | _ => false)
    | _ => false

fun sint i = {value = i, suffix = "", base = StringCvt.DEC}
fun expr_int i = ebogwrap (Constant (bogwrap (NUMCONST (sint i))))

fun expr_string e =
    case enode e of
      BinOp _ => "BinOp"
    | UnOp _ => "UnOp"
    | CondExp _ => "CondExp"
    | Constant _ => "Constant"
    | Var(nm, _) => "Var" ^ nm
    | StructDot _ => "StructDot"
    | ArrayDeref _ => "ArrayDeref"
    | Deref _ => "Deref"
    | TypeCast _ => "TypeCast"
    | Sizeof _ => "Sizeof"
    | SizeofTy _ => "SizeofTy"
    | EFnCall _ => "EFnCall"
    | CompLiteral _ => "CompLit"
    | Arbitrary _ => "Arbitrary"
    | MKBOOL _ => "MKBOOL"
    | _ => "[whoa! Unknown expr type]"

fun radn r = let
  open StringCvt
in
  case r of
      BIN => 2
    | OCT => 8
    | DEC => 10
    | HEX => 16
end

fun nli_compare (nli1, nli2) = let
  val {value = v1, suffix = s1, base = r1} = nli1
  val {value = v2, suffix = s2, base = r2} = nli2
in
  pair_compare (pair_compare (IntInf.compare, String.compare),
                measure_cmp radn)
               (((v1, s1), r1), ((v2, s2), r2))
end

(* ignores location information *)
fun lc_compare (lc1, lc2) =
    case (node lc1, node lc2) of
        (NUMCONST nli1, NUMCONST nli2) => nli_compare (nli1, nli2)
      | (NUMCONST _, _) => LESS
      | (_, NUMCONST _) => GREATER
      | (STRING_LIT s1, STRING_LIT s2) => String.compare(s1, s2)

fun vi_compare((s1,vi1 : var_info), (s2,vi2)) =
    case String.compare(s1, s2) of
        EQUAL =>
        if vi1 = vi2 then EQUAL
        else option_compare (inv_img_cmp #1 (ctype_compare Int.compare))
                            (!vi1, !vi2)
      | x => x

(* ignores location information *)
fun expr_compare (e1,e2) =
    case String.compare (expr_string e1, expr_string e2) of
        EQUAL =>
        let
        in
          case (enode e1, enode e2) of
              (BinOp(opn1, e11, e12), BinOp(opn2, e21, e22)) =>
              (case binop_compare(opn1,opn2) of
                   EQUAL => list_compare expr_compare ([e11,e12], [e21,e22])
                 | x => x)
            | (UnOp p1, UnOp p2) => pair_compare(unop_compare, expr_compare) (p1, p2)
            | (CondExp(e11,e12,e13), CondExp(e21,e22,e23)) =>
              list_compare expr_compare ([e11,e12,e13], [e21,e22,e23])
            | (Constant lc1, Constant lc2) => lc_compare (lc1, lc2)
            | (Var vi1, Var vi2) => vi_compare (vi1, vi2)
            | (StructDot p1, StructDot p2) =>
              pair_compare (expr_compare, String.compare) (p1,p2)
            | (ArrayDeref p1, ArrayDeref p2) =>
              pair_compare (expr_compare, expr_compare) (p1,p2)
            | (Deref e1, Deref e2) => expr_compare (e1, e2)
            | (TypeCast p1, TypeCast p2) =>
              pair_compare (inv_img_cmp node (ctype_compare expr_compare),
                            expr_compare)
                           (p1, p2)
            | (Sizeof e1, Sizeof e2) => expr_compare (e1, e2)
            | (SizeofTy ty1, SizeofTy ty2) =>
              inv_img_cmp node (ctype_compare expr_compare) (ty1, ty2)
            | (EFnCall(e1, elist1), EFnCall(e2, elist2)) =>
              list_compare expr_compare (e1::elist1, e2::elist2)
            | (CompLiteral p1, CompLiteral p2) =>
              pair_compare (ctype_compare expr_compare,
                            list_compare (pair_compare (list_compare d_cmp, i_cmp)))
                           (p1, p2)
            | (Arbitrary ty1, Arbitrary ty2) => ctype_compare expr_compare (ty1, ty2)
            | (MKBOOL e1, MKBOOL e2) => expr_compare (e1, e2)
            | _ => raise Fail ("expr_compare: can't happen: " ^ expr_string e1)
        end
      | x => x
and d_cmp p =
    case p of
        (DesignE e1, DesignE e2) => expr_compare (e1, e2)
      | (DesignE _, _) => LESS
      | (_, DesignE _) => GREATER
      | (DesignFld fld1, DesignFld fld2) => String.compare (fld1, fld2)
and i_cmp p =
    case p of
        (InitE e1, InitE e2) => expr_compare (e1,e2)
      | (InitE _, _) => LESS
      | (_, InitE _) => GREATER
      | (InitList dil1, InitList dil2) =>
        list_compare (pair_compare (list_compare d_cmp, i_cmp)) (dil1, dil2)

fun bool b = (if b then IntInf.fromInt 1 else IntInf.fromInt 0, Signed Int)

fun safeop (l,r) destty f x = let
  val dmod = imax destty + 1
  val dmin = imin destty
  val result = f x
  val overflow = result >= dmod orelse result < dmin
  val result' = if overflow then (result mod dmod, destty)
                else (result, destty)
in
  if overflow andalso is_signed destty then
    Feedback.errorStr'(l,r,"Signed overflow")
  else ();
  result'
end


fun eval_binop (l, r) (binop, (n1,ty1), (n2,ty2)) = let
  open IntInf
  val destty = case binop of
                 LShift => integer_promotions ty1
               | RShift => integer_promotions ty2
               | _ => arithmetic_conversion (ty1, ty2)
  val safeop = fn f => safeop (l,r) destty f (n1,n2)
in
  case binop of
    Lt => bool (n1 < n2)
  | Gt => bool (n1 > n2)
  | Leq => bool (n1 <= n2)
  | Geq => bool (n1 >= n2)
  | Equals => bool (n1 = n2)
  | NotEquals => bool (n1 <> n2)
  | LogOr => bool (n1 <> 0 orelse n2 <> 0)
  | LogAnd => bool (n1 <> 0 andalso n2 <> 0)
  | Plus => safeop op+
  | Times => safeop op*
  | Minus => safeop op-
  | Divides => safeop (op div)
  | Modulus => safeop (op mod)
  | BitwiseAnd => (andb(n1, n2), destty)
  | BitwiseOr => (orb(n1, n2), destty)
  | BitwiseXOr => (xorb(n1, n2), destty)
  | LShift => (if n2 < 0 orelse n2 >= ty_width destty then
                 Feedback.errorStr'(l,r,"Invalid/overflowing shift")
               else ();
               safeop (fn (n1,n2) => <<(n1, Word.fromInt (toInt n2))))
  | RShift => (if n2 < 0 orelse n2 >= ty_width destty orelse
                  (is_signed destty andalso n1 < 0)
               then
                 Feedback.errorStr'(l,r,"Invalid/overflowing shift")
               else ();
               safeop (fn (n1,n2) => ~>>(n1, Word.fromInt (toInt n2))))
end

val fi = IntInf.fromInt

fun eval_unop (l, r, uop, (n, ty)) = let
  open IntInf
  val destty = integer_promotions ty
in
  case uop of
    Negate => safeop (l,r) destty ~ n
  | Not => bool (n = 0)
  | Addr => (Feedback.errorStr'(l,r, "Can't evaluate address-of in constant \
                                     \expression");
             (fi 0, Signed Int))
  | BitNegate => (notb n, destty)
end


fun eclookup (CE {enumenv,...}) s = Symtab.lookup enumenv s

fun consteval0 (ecenv as CE {enumenv, typing, structsize}) e = let
  val fi = IntInf.fromInt
  val zero = (fi 0, Signed Int)
  fun Fail s = (Feedback.errorStr'(eleft e, eright e, s); zero)
  val consteval = consteval0 ecenv
in
  case enode e of
    BinOp (bop, e1, e2) => eval_binop (eleft e, eright e)
                                      (bop, consteval e1, consteval e2)
  | UnOp (uop, e) => eval_unop (eleft e, eright e, uop, consteval e)
  | Constant lc => eval_litconst lc
  | Var (s,_) => let
    in
      case Symtab.lookup enumenv s of
        NONE => Fail ("Variable "^s^ " can't appear in a constant expression")
      | SOME (v, _) => (v, Signed Int)
    end
  | StructDot _ =>
    Fail "Can't evaluate fieldref in constant expression"
  | ArrayDeref _ =>
    Fail "Can't evaluate array deref in constant expression"
  | Deref _ => Fail "Can't evaluate deref in constant expression"
  | CondExp(g,t,e) => if #1 (consteval g) <> fi 0 then consteval t
                      else consteval e
  | SizeofTy ty => (fi (sizeof structsize (constify_abtype ecenv (node ty))),
                    ImplementationTypes.size_t)
  | Sizeof e0 => (fi (sizeof structsize (typing e0)),
                  ImplementationTypes.size_t)
  | MKBOOL e => bool (#1 (consteval e) <> fi 0)
  | TypeCast(destty, e0) => let
      val (v,_) = consteval e0
    in
      safeop (eleft e, eright e) (node destty) (fn x => x) v
    end
  | _ => Fail ("Unexpected expression form (" ^ expr_string e ^
               ") in consteval")
end
and consteval ecenv e = #1 (consteval0 ecenv e)
and constify_abtype ecenv (ty : expr ctype)  : int ctype = let
  fun recurse ty =
      case ty of
        Array (ty0, SOME sz) => Array (recurse ty0,
                                       SOME (IntInf.toInt (consteval ecenv sz)))
      | Array (ty0, NONE) => Array(recurse ty0, NONE)
      | Ptr ty => Ptr (recurse ty)
      | Signed x => Signed x
      | PlainChar => PlainChar
      | Unsigned x => Unsigned x
      | StructTy s => StructTy s
      | EnumTy x => EnumTy x
      | Bitfield(b,e) => Bitfield (b, IntInf.toInt (consteval ecenv e))
      | Ident s => Ident s
      | Function (retty, args) => Function (recurse retty, map recurse args)
      | Void => Void
      | Bool => Bool
      | _ => raise Fail ("constify_abtype: unexpected type form: "^tyname0 (K "") ty)
in
  recurse ty
end

(* predicates on expressions to determine if they can't be evaluated freely
   when on the rhs of a short-circuiting operator.  *)
fun bop_needs_scprot bop =
    case bop of
      Divides => true
    | Modulus => true
    | RShift => true
    | LShift => true
    | _ => false
fun uop_needs_scprot _ = false

fun eneeds_sc_protection e =
    case enode e of
      BinOp(bop, e1, e2) => bop_needs_scprot bop orelse
                            eneeds_sc_protection e1 orelse
                            eneeds_sc_protection e2
    | UnOp(uop, e) => uop_needs_scprot uop orelse eneeds_sc_protection e
    | CondExp(e1,e2,e3) => List.exists eneeds_sc_protection [e1,e2,e3]
    | Constant _ => false
    | Var _ => false
    | StructDot (e,_) => eneeds_sc_protection e
    | ArrayDeref _ => true (* could try to figure out if the array is
                                    a pointer, but even if it isn't, there
                                    should be bounds checking going on *)
    | Deref _ => true
    | TypeCast (_, e) => eneeds_sc_protection e
    | Sizeof _ => false
    | SizeofTy _ => false
    | EFnCall _ => true
    | CompLiteral (_, dis) => List.exists (i_needs_scprot o #2) dis
    | Arbitrary _ => false
    | _ => raise Fail ("eneeds_sc_protection: can't handle "^expr_string e)
and i_needs_scprot i =
    case i of
      InitE e => eneeds_sc_protection e
    | InitList dis => List.exists (i_needs_scprot o #2) dis

end (* struct *)
