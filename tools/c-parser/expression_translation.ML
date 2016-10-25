(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* code to translate StrictC expressions into "abstract" VCG expressions *)

signature EXPRESSION_TRANSLATION =
sig

  type expr_info
  type ctyp = int Absyn.ctype
  type varinfo =
       (string * Term.typ * ctyp option * CalculateState.var_sort)

  val anal_integer_conversion : bool Config.T

  val zero_term : theory -> ProgramAnalysis.senv -> ctyp -> term

  val ctype_of : expr_info -> ctyp
  val rval_of : expr_info -> term -> term
  val lval_of : expr_info -> (term -> term -> term) option
                (* returned function takes new value and old state;
                   returns new state *)
  val guards_of : expr_info -> (term -> (term * term)) list
  val lguards_of : expr_info -> (term -> (term * term)) list


  val mk_rval : ((term -> term) * ctyp * bool * SourcePos.t * SourcePos.t) ->
                expr_info
                (* term -> term function takes a state (variable) and constructs the
                   term corresponding to the desired (r-)value *)

  val strip_kb : expr_info -> expr_info
                 (* turns an expression that will give rise to an Isabelle bool into
                    one that will give rise to an Isabelle "int" (e.g., word32), with
                    1 coding for true, and 0 coding for false *)
  val mk_isabool : expr_info -> expr_info
                   (* turns an expression that will give rise to an Isabelle word
                      into one that will give rise to an Isabelle bool, which will be
                      false if the original was zero, and true otherwise. *)

  val intprom_ei : theory -> expr_info -> expr_info
  val typecast : (theory * ctyp * expr_info) -> expr_info
  val array_decay : expr_info -> expr_info


  val expr_term : Proof.context -> ProgramAnalysis.csenv ->
                  varinfo TermsTypes.termbuilder ->
                  (MString.t -> varinfo option) -> Absyn.expr -> expr_info

end

structure ExpressionTranslation : EXPRESSION_TRANSLATION =
struct

open Absyn TermsTypes NameGeneration ExpressionTyping Feedback
     ImplementationNumbers

type ctyp = int Absyn.ctype
type varinfo = (string * Term.typ * int ctype option * CalculateState.var_sort)
val bnm = Binding.name


(* ----------------------------------------------------------------------
    The expr_info type

    - the lval component is the (optional) lval calculator,
      it takes two parameters:
        1. a new value to slot into the state
        2. the state into which the new value is to be slotted

      I had thought that we needed an extra initial parameter, "the
      state in which you calculate the lvalue", thinking that this was
      relevant in an assignment such as

        a[i] := f(args)

      where f might modify global variables, of which i might be one.
      But this sort of nastiness has to be BANNED, because allowing it
      would result in a C0 mandated order of evaluation from
      left-to-right that might not be reflected in a C implementation.

    - if the addr component is present, then so too is the lval
      component.  It returns the address of the lvalue, if it has one.

    - the rval component takes a state and returns the value

    - the cty component is the C type of the expression

    - the ibool component is true if the value is "known to be bool",
      i.e.  the type is Signed Int, but the value of the term will be
      an Isabelle boolean.

    - the lguard component is a list of guards that should be applied
      to the current state if this expression is used as an lvalue.

    - the guard component is a list of guards that should be applied
      to the current state.  The return value from such an application is
      a term of type bool such that if the term is false, then the expression
      is trying to do something illegal (such as dividing by zero).  The
      second term is of type c0_errotype and is the sort of the error.

    - the left and right components record the source-origin of the
      expression

   ---------------------------------------------------------------------- *)

datatype expr_info =
     EI of {lval : (term -> term -> term) option,
            addr : (term -> term) option,
            rval : term -> term,
            cty  : int ctype,
            ibool: bool,
            lguard : (term -> term * term) list,
            guard: (term -> term * term) list,
            left : SourcePos.t, right : SourcePos.t }

fun ei_zero cty =
    EI{lval = NONE, addr = NONE,
       rval = (fn _ => Const("0", IntInfo.ity2wty cty)),
       cty = cty,
       ibool = false,
       lguard = [], guard = [],
       left = SourcePos.bogus, right = SourcePos.bogus}

fun ctype_of (EI ei) = #cty ei
fun rval_of (EI ei) = #rval ei
fun addr_of (EI ei) = #addr ei
fun lval_of (EI ei) = #lval ei
fun ibool_of (EI ei) = #ibool ei
fun mk_rval(r,cty,ib,lpos,rpos) =
    EI { lval = NONE, addr = NONE, rval = r, cty = cty,
         ibool = ib, lguard = [], guard = [], left = lpos, right = rpos}
fun add_guards gs (EI {lval,addr,rval,cty,ibool,lguard,guard,left,right}) =
    EI {lval = lval, addr = addr, rval = rval, cty = cty, ibool = ibool,
        lguard = lguard, guard = gs @ guard,
        left = left, right = right}
fun add_guard g = add_guards [g]
fun guards_of (EI ei) = #guard ei
fun add_lguards gs (EI {lval,addr,rval,cty,ibool,lguard,guard,left,right}) =
    EI {lval = lval, addr = addr, rval = rval, cty = cty, ibool = ibool,
        lguard = gs @ lguard, guard = guard, left = left, right = right}
fun lguards_of (EI ei) = #lguard ei
fun add_ei_guards src_ei tgt_ei = tgt_ei |> add_guards (guards_of src_ei)
                                         |> add_lguards (lguards_of src_ei)
fun eileft (EI ei) = #left ei
fun eiright (EI ei) = #right ei

datatype i_res = Known of typ | First

fun literalconstant t : expr_info = let
  val mk_rval = fn (f,x) => mk_rval(f,x,false,left t, right t)
  fun fail() =
      error (SourcePos.toString (left t) ^ " literal is too large!")
in
  case node t of
    NUMCONST nc => let
      val cty = Absyn.numconst_type nc
                handle Subscript => (fail(); Signed Int)
    in
      mk_rval((fn _ => IntInfo.numeral2w cty (#value nc)), cty)
    end
  | STRING_LIT _ =>
    (Feedback.errorStr'(left t,right t,"Don't want to handle string literals!");
     mk_rval((fn _ => IntInfo.numeral2w (Signed Int) 1), Signed Int))
end

fun is_litzero ei =
    ctype_of ei = Signed Int andalso
    (rval_of ei True = IntInfo.numeral2w (Signed Int) 0
     handle Fail _ => false)

(* Given a term-generating function "term_gen_fn" a list of subexpressions
 * "eis", a destination type "result_type" and boolean indicating whether the
 * result is know to be a boolean, construct a new expression combining these
 * sub-expressions. *)
fun lmk_comb_raw (term_gen_fn, eis, result_type, is_result_kb) = let
  (* Construct the Isabelle term from the sub-expressions. *)
  fun new_term s =
        term_gen_fn (map (fn e => rval_of e s) eis)

  (* Caluculate the first and last source position of this expression. *)
  val (l, r) = (eileft (hd eis), eiright (List.last eis))
      handle Empty => (SourcePos.bogus, SourcePos.bogus)
in
  List.foldl
      (fn (old_ei : expr_info, acc_ei : expr_info) => acc_ei |> add_ei_guards old_ei)
      (mk_rval (new_term, result_type, is_result_kb, l, r))
      eis
end

fun lmk_comb(opr,eis,i_resty,resty,reskb) = let
  fun newt s = let
    val ts = map (fn e => rval_of e s) eis
    val tys = map type_of ts
    val ires = case i_resty of Known ty => ty | First => hd tys
    val whole_type = List.foldr op--> ires tys
  in
    List.foldl (fn (t1,t2) => t2 $ t1) (Const(opr, whole_type)) ts
  end
  val (l,r) = (eileft (hd eis), eiright (List.last eis))
      handle Empty => (SourcePos.bogus, SourcePos.bogus)
in
  List.foldl
      (fn (old_ei : expr_info, acc_ei : expr_info) => acc_ei |> add_ei_guards old_ei)
      (mk_rval(newt, resty, reskb, l, r))
      eis
end

fun fmk_comb(f, ei, resty, reskb) =
    mk_rval(f o rval_of ei, resty, reskb, eileft ei, eiright ei) |> add_ei_guards ei


(* "strip known to be bool" - turns something that might have Isabelle
   boolean type back into something that will translate to the Isabelle
   integral type *)
fun strip_kb ei =
    if not (ibool_of ei) then ei
    else let
        fun newt s = let
          val t0 = rval_of ei s
        in
          mk_cond(t0, mk_one IntInfo.int, mk_zero IntInfo.int)
        end
      in
        mk_rval(newt, Signed Int, false, eileft ei, eiright ei) |> add_ei_guards ei
      end

(* this is for converting between pairs of integer types *)
val anal_integer_conversion = let
  val (aicconfig, aicsetup) =
      Attrib.config_bool (bnm "anal_integer_conversion") (K false)
in
  Context.>>(Context.map_theory aicsetup);
  aicconfig
end

fun int_conversion thy newty (ei : expr_info) : expr_info = let
  val oldty = ctype_of ei
in
  if oldty = newty then ei
  else let
      val oldity = TermsTypes.IntInfo.ity2wty oldty
      val newity = TermsTypes.IntInfo.ity2wty newty
      fun tf t = if is_signed oldty then
                   Const(@{const_name "scast"}, oldity --> newity) $ t
                 else
                   Const(@{const_name "ucast"}, oldity --> newity) $ t

      (* strictly, "overflow" here results in an implementation-defined value, or an
         "implementation-defined signal" (???) [6.3.1.3].

         The latter might be a sufficiently scary prospect that we allow for
         guarding against it. *)
      fun mkguard s = let
        val val1 = mk_w2si (rval_of ei s)
        val lower = mk_leq(mk_int_numeral (imin newty), val1)
        val upper = mk_leq(val1, mk_int_numeral (imax newty))
      in
        (mk_conj(lower,upper), signed_overflow_error)
      end
      val guards =
          if Config.get_global thy anal_integer_conversion then
            case newty of
              Signed _ => [mkguard]
            | PlainChar => if imin PlainChar = 0 then [] else [mkguard]
            | _ => []
          else []
    in
      mk_rval (tf o rval_of ei, newty, ibool_of ei, eileft ei, eiright ei)
              |> add_ei_guards ei
              |> add_guards guards
    end
end

fun intprom_ei thy ei = int_conversion thy (integer_promotions (ctype_of ei)) ei

fun arithmetic_conversions thy (ei01, ei02) = let
  val ei1 = if arithmetic_type (ctype_of ei01) then intprom_ei thy ei01
            else (Feedback.errorStr'(eileft ei01, eiright ei01,
                                     "Expression must have arithmetic type.");
                  ei_zero (Signed Int))
  val ei2 = if arithmetic_type (ctype_of ei02) then intprom_ei thy ei02
            else (Feedback.errorStr'(eileft ei02, eiright ei02,
                                     "Expression must have arithmetic type.");
                  ei_zero (Signed Int))
  val commonty = arithmetic_conversion (ctype_of ei1, ctype_of ei2)
in
  (int_conversion thy commonty (strip_kb ei1),
   int_conversion thy commonty (strip_kb ei2),
   commonty)
end

fun mk_isabool ei = let
  val kb = ibool_of ei
  val tf = rval_of ei
  val cty = ctype_of ei
  val (l,r) = (eileft ei, eiright ei)
in
  if kb then ei
  else if ptr_type cty then let
      fun newt s = let
        val t0 = tf s
      in
        mk_neg(mk_eqt(t0, mk_ptr(mk_zero addr_ty, dest_ptr_ty (type_of t0))))
        end
    in
      mk_rval(newt, Signed Int, true, l, r) |> add_ei_guards ei
    end
  else if integer_type cty then let
      fun newt s = let
        val t0 = tf s
      in
        mk_neg(mk_eqt(t0, mk_zero (type_of t0)))
      end
    in
      mk_rval(newt, Signed Int, true, l, r) |> add_ei_guards ei
    end
  else error (SourcePos.toString l ^ " mk_isabool: can't treat "^
              tyname cty^" as bool")
end

fun unop_term thy (unop,l) (ei:expr_info) : expr_info = let
in
  case unop of
    Negate => let
      val ei' = strip_kb (intprom_ei thy ei)
      val rty = ctype_of ei'
      fun mkguard s = let
        val val1 = mk_w2si (rval_of ei' s)
        val result_val = mk_uminus val1
        val lower = mk_leq(mk_int_numeral (imin rty), result_val)
        val upper = mk_leq(result_val, mk_int_numeral (imax rty))
      in
        (mk_conj(lower,upper), signed_overflow_error)
      end
      val newguards =
          case rty of
            Signed _ => [mkguard]
          | _ => []
    in
      lmk_comb(@{const_name "uminus"}, [ei'], First, rty, false)
          |> add_guards newguards
    end
  | Not => let
      val ei' = mk_isabool ei
    in
      lmk_comb(@{const_name "Not"}, [ei'], Known bool, Signed Int, true)
    end
  | Addr => let
    in
      case ctype_of ei of
        Ptr (Function _) => ei
      | _ => (mk_rval(valOf (addr_of ei), Ptr (ctype_of ei), false, l, eiright ei)
                |> add_ei_guards ei
                   handle Option =>
                          error (SourcePos.toString l ^
                                 " taking address of value without one"))
    end
  | BitNegate => let val ei' = strip_kb (intprom_ei thy ei)
                     val _ = tracing("After prom, argument to bitNOT has type "^
                                     tyname (ctype_of ei'))
                     val result =
                         lmk_comb(@{const_name "bitNOT"},
                                  [ei'], First, ctype_of ei', false)
                 in
                   tracing("bitNOT result has type "^tyname (ctype_of result));
                   result
                 end
end handle TYPE (s,tys,tms) => raise TYPE ("unop_term: "^s, tys, tms)

fun array_decay (ei : expr_info) =
    case ctype_of ei of
      Array (elcty, _) => let
        fun rval st = let
          val array_addr =
              valOf (addr_of ei) st
              handle Option =>
                     (Feedback.errorStr'(eileft ei, eiright ei,
                                         "Attempting to cause decay to pointer \
                                         \on array without an address");
                      mk_zero (mk_ptr_ty
                                   (#1 (dest_array_type
                                            (type_of (rval_of ei st))))))

          val addr_ty = type_of array_addr
          val (elty, _) = dest_array_type (dest_ptr_ty addr_ty)
        in
          mk_ptr_coerce (array_addr, mk_ptr_ty elty)
        end
      in
        mk_rval(rval, Ptr elcty, false, eileft ei, eiright ei) |> add_ei_guards ei
      end
    | _ => ei

fun typecast (thy, newtype, ei : expr_info) = let
  val ei = ei |> array_decay |> strip_kb
  val oldtype = ctype_of ei
  val new_ty = CalculateState.ctype_to_typ(thy, newtype)
  fun fail () = error (SourcePos.toString (eileft ei) ^
                       " can't cast from: "^tyname oldtype^" to: "^
                       tyname newtype)
in
  if oldtype = newtype then ei
  else if newtype = Bool then
    if scalar_type oldtype then
      let
        fun rv s = let
          val t0 = rval_of ei s
        in
          mk_cond(mk_neg (mk_eqt(t0, mk_zero (type_of t0))),
                  IntInfo.numeral2w Bool 1,
                  IntInfo.numeral2w Bool 0)
        end
      in
        mk_rval(rv, Bool, false, eileft ei, eiright ei)
               |> add_ei_guards ei
      end
    else fail()
  else if integer_type newtype then
    if integer_type oldtype then int_conversion thy newtype ei
    else if ptr_type oldtype then
      typecast (thy, newtype,
                fmk_comb(mk_ptr_val, ei, ImplementationTypes.ptrval_t, false))
    else fail()
  else if ptr_type newtype then
    if integer_type oldtype then
      fmk_comb((fn t => mk_ptr(t, dest_ptr_ty new_ty)),
               typecast(thy, ImplementationTypes.ptrval_t, ei),
               newtype, false)
    else if ptr_type oldtype then
      lmk_comb(@{const_name "ptr_coerce"}, [ei], Known new_ty, newtype, false)
    else fail()
  else fail()
end

fun boglit i = bogwrap(NUMCONST {value = i, base = StringCvt.DEC, suffix = ""})

fun mk_relbinop thy (opr,sopr,ei1,ei2) = let
  val cty1 = ctype_of ei1
  val cty2 = ctype_of ei2
in
  if integer_type (ctype_of ei1) andalso integer_type (ctype_of ei2) then let
      val (ei1',ei2',rty) = arithmetic_conversions thy (ei1,ei2)
    in
      lmk_comb(if is_signed rty then sopr else opr,
               [ei1', ei2'], Known bool, Signed Int, true)
    end
  else let
      fun couldbe_ptr ei =
          ptr_type (ctype_of ei) orelse is_litzero ei
      fun is_voidptr ei = (ctype_of ei = Ptr Void) orelse is_litzero ei
      fun fail() =
          error (SourcePos.toString (eileft ei1) ^
                 " can't handle comparisons on values of "^tyname cty1^
                 " and "^tyname cty2)
    in
      if couldbe_ptr ei1 andalso couldbe_ptr ei2 then
        if opr = @{const_name "HOL.eq"} then let
            fun vs_coerce ei =
                if ctype_of ei = Ptr Void then ei
                else if ctype_of ei = Signed Int then
                  mk_rval ((fn _ => NULLptr), Ptr Void, false, eileft ei,
                           eiright ei) |> add_ei_guards ei
                else
                  lmk_comb(@{const_name "ptr_coerce"}, [ei],
                           Known (mk_ptr_ty unit), Ptr Void, false)
          in
            if is_voidptr ei1 orelse is_voidptr ei2 then
              lmk_comb(opr, [vs_coerce ei1, vs_coerce ei2], Known bool,
                       Signed Int, true)
            else if cty2 = cty1 then
              lmk_comb(opr, [ei1,ei2], Known bool, Signed Int, true)
            else
              error (SourcePos.toString (eileft ei1) ^
                     "can't equality-test these pointers")
          end
        else if cty2 = cty1 then let
            val opname =
                case opr of
                  @{const_name "less"} => "CTypesBase.ptr_less"
                | @{const_name "less_eq"} => "CTypesBase.ptr_le"
                | _ => raise Fail "binop_term: catastrophic"
          in
            lmk_comb(opname, [ei1,ei2], Known bool, Signed Int, true)
          end
        else fail()
      else fail()
    end
end

fun binop_term thy bop ei1 ei2 : expr_info = let
  val ei1 = array_decay ei1
  val ei2 = array_decay ei2
  fun mk_arithop (opr,ei1, ei2) = let
    val (ei1', ei2', rty) = arithmetic_conversions thy (ei1, ei2)
  in
    lmk_comb(opr, [ei1', ei2'], First, rty, false)
  end
  fun check_signed_binop(c_t, intop, ei1, ei2) = let
    val (ei1', ei2', rty) = arithmetic_conversions thy (ei1, ei2)
    val result = lmk_comb(c_t, [ei1', ei2'], First, rty, false)
    fun mkguard s = let
      val val1 = mk_w2si (rval_of ei1' s)
      val val2 = mk_w2si (rval_of ei2' s)
      val result_val = intop (val1, val2)
      val lower = mk_leq(mk_int_numeral (imin rty), result_val)
      val upper = mk_leq(result_val, mk_int_numeral (imax rty))
    in
      (mk_conj(lower,upper), signed_overflow_error)
    end
    val newguards =
        case ctype_of result of
          Signed _ => [mkguard]
        | PlainChar => if imin PlainChar = 0 then [] else [mkguard]
        | _ => []
  in
    add_guards newguards result
  end
  fun is_result_signed (ei1, ei2) =
    is_signed (arithmetic_conversion (ctype_of ei1, ctype_of ei2))
  fun Fail s = error (SourcePos.toString (eileft ei1) ^ " " ^ s)
in
  case bop of
    LogOr => lmk_comb(@{const_name "HOL.disj"}, [mk_isabool ei1, mk_isabool ei2],
                      Known bool,Signed Int,true)
  | LogAnd => lmk_comb(@{const_name "HOL.conj"}, [mk_isabool ei1, mk_isabool ei2],
                       Known bool,Signed Int,true)
  | Lt => mk_relbinop thy (@{const_name "less"}, @{const_name "word_sless"},
                           ei1, ei2)
  | Gt => mk_relbinop thy (@{const_name "less"}, @{const_name "word_sless"},
                           ei2, ei1)
  | Leq => mk_relbinop thy (@{const_name "less_eq"}, @{const_name "word_sle"},
                            ei1, ei2)
  | Geq => mk_relbinop thy (@{const_name "less_eq"}, @{const_name "word_sle"},
                            ei2, ei1)

  | Equals => let
      val _ = tracing ("EQ_OP("^tyname (ctype_of ei1)^", "
                       ^tyname (ctype_of ei2)^")")
    in
      mk_relbinop thy (@{const_name "HOL.eq"}, @{const_name "HOL.eq"}, ei1, ei2)
    end
  | NotEquals => unop_term thy (Not,eileft ei1) (binop_term thy Equals ei1 ei2)
  | Plus => if ptr_type (ctype_of ei1) then
              if integer_type (ctype_of ei2) then
              let
                val ei2' = intprom_ei thy ei2
              in
                lmk_comb_raw(fn [l,r] =>
                                mk_ptr_add (l, IntInfo.word_to_int (ctype_of ei2') r)
                            | _ => raise Fail "ptr_add can't happen",
                             [ei1, ei2'],
                             ctype_of ei1, false)
              end
              else Fail "adding non-integral to pointer"
            else if ptr_type (ctype_of ei2) then
              if integer_type (ctype_of ei1) then
              let
                val ei1' = intprom_ei thy ei1
              in
                lmk_comb_raw(fn [l,r] =>
                                mk_ptr_add (l, IntInfo.word_to_int (ctype_of ei1') r)
                            | _ => raise Fail "ptr_add can't happen",
                             [ei2, ei1'], ctype_of ei2, false)
              end
              else Fail "adding non-integral to pointer"
            else check_signed_binop(@{const_name "plus"}, mk_plus, ei1, ei2)
  | Minus => if ptr_type (ctype_of ei1) then
               if integer_type (ctype_of ei2) then
                 binop_term thy Plus ei1 (unop_term thy (Negate,eileft ei2) ei2)
               else if ptr_type (ctype_of ei2) then
                 lmk_comb(@{const_name "ptr_sub"}, [ei1, ei2],
                          Known IntInfo.ptrdiff_ity,
                          ImplementationTypes.ptrdiff_t,
                          false)
               else Fail "invalid types to binary subtraction"
             else
               check_signed_binop(@{const_name "minus"}, mk_sub, ei1, ei2)
  | Times => check_signed_binop(@{const_name "times"}, mk_times, ei1, ei2)
  | Divides => let
      fun div_zero_check s = let
        val e2 = rval_of ei2 s
      in
        (mk_neg(mk_eqt(e2,mk_zero (type_of e2))), div_0_error)
      end
    in
      if is_result_signed (ei1, ei2) then
        add_guard div_zero_check (check_signed_binop(@{const_name "sdiv"}, mk_sdiv, ei1, ei2))
      else
        add_guard div_zero_check (mk_arithop(@{const_name "divide"}, ei1, ei2))
    end
  | Modulus => let
      fun div_zero_check s = let
        val e2 = rval_of ei2 s
      in
        (mk_neg(mk_eqt(e2, mk_zero(type_of e2))), div_0_error)
      end
    in
      if is_result_signed (ei1, ei2) then
        add_guard div_zero_check (check_signed_binop(@{const_name "smod"}, mk_smod, ei1, ei2))
      else
        add_guard div_zero_check (mk_arithop(@{const_name "modulo"}, ei1, ei2))
    end
  | BitwiseAnd => mk_arithop(@{const_name "bitAND"}, ei1, ei2)
  | BitwiseOr => mk_arithop(@{const_name "bitOR"}, ei1, ei2)
  | BitwiseXOr => mk_arithop(@{const_name "bitXOR"}, ei1, ei2)
  | LShift => let
      (* "the integer promotions are performed on each of the operands" *)
      val ei1' = intprom_ei thy ei1
      val ei2' = intprom_ei thy ei2
      fun rval (s:term) : term =
          mk_lshift(rval_of ei1' s, IntInfo.ity_to_nat (rval_of ei2' s))
      val res : expr_info =
          mk_rval(rval,ctype_of ei1',false,eileft ei1, eiright ei2)
                 |> add_ei_guards ei1 |> add_ei_guards ei2
      val res = (* add check that the result is not too large *) let
        val nat3_ty = @{typ "nat => nat => nat"}
        val times_t = Const(@{const_name "times"}, nat3_ty)
        val exp_t = Const(@{const_name "power"}, nat3_ty)
        val less_t = Const(@{const_name "less"}, @{typ "nat => nat => bool"})
        val two_t = @{term "2 :: nat"}
        val (ity1, signedp) = case ctype_of ei1' of
                     Signed i => (i, true)
                   | Unsigned i => (i, false)
                   | _ => Fail "Bad type for second argument to left-shift"
        val iwidth = int_sizeof ity1 * CHAR_BIT
        val iwidth_e = literalconstant(boglit iwidth)
        fun signed_guard s =
            (mk_conj(less_t
                       $ (times_t
                            $ IntInfo.ity_to_nat (rval_of ei1' s)
                            $ (exp_t
                                 $ two_t
                                 $ IntInfo.ity_to_nat (rval_of ei2' s)))
                       $ (exp_t
                            $ @{term "2 :: nat"}
                                 $ mk_numeral nat (iwidth - 1)),
                     rval_of (mk_relbinop thy (@{const_name "less_eq"},
                                               @{const_name "word_sle"},
                                               literalconstant (boglit 0),
                                               ei1')) s),
             shift_error)
        fun unsigned_guard s =
            (rval_of (mk_relbinop thy (@{const_name "less"}, @{const_name "word_sless"},
                                       ei2', iwidth_e)) s,
             shift_error)
      in
        add_guard (if signedp then signed_guard else unsigned_guard) res
      end
    in
      case ctype_of ei2' of
        Signed _ => let
          val nz_shift_check : expr_info =
              mk_relbinop thy (@{const_name "less_eq"}, @{const_name "word_sle"},
                               literalconstant (boglit 0), ei2')
          fun shift_checkP chk (s:term) = (rval_of chk s, shift_error)
        in
          res |> add_guard (shift_checkP nz_shift_check)
        end
      | Unsigned _ => res
      | _ => Fail "Bad type for second argument to <<"
    end
  | RShift => let
      (* "the integer promotions are performed on each of the operands" *)
      val ei1' = intprom_ei thy ei1
      val ei2' = intprom_ei thy ei2
      fun rval s =
          mk_rshift(rval_of ei1' s, IntInfo.ity_to_nat (rval_of ei2' s))
      val res =
          mk_rval(rval,ctype_of ei1',false,eileft ei1', eiright ei2')
                 |> add_ei_guards ei1 |> add_ei_guards ei2
      val res = (* add check that second argument is not too large *) let
        val ity1 = case ctype_of ei1' of
                     Signed i => i
                   | Unsigned i => i
                   | _ => Fail "Bad type for first argument to right-shift"
        val iwidth = int_sizeof ity1 * CHAR_BIT
        val szcheck =
            mk_relbinop thy (@{const_name "less"}, @{const_name "word_sless"},
                             ei2', literalconstant(boglit iwidth))
      in
        add_guard (fn s => (rval_of szcheck s, shift_error)) res
      end
      val res = (* possibly add negativity check on second argument *)
          case ctype_of ei2' of
            Signed _ => let
              val shift_check =
                  mk_relbinop thy (@{const_name "less_eq"}, @{const_name "word_sle"},
                                   literalconstant (boglit 0), ei2')
              fun shift_checkP s = (rval_of shift_check s, shift_error)
            in
              add_guard shift_checkP res
            end
          | Unsigned _ => res
          | _ => Fail "Bad type for second argument to right shift"
      val res = (* possibly add negativity check on first argument *)
          case ctype_of ei1' of
            Signed _ => let
              val neg_check =
                  mk_relbinop thy (@{const_name "less_eq"}, @{const_name "word_sle"},
                                   literalconstant (boglit 0), ei1')
              fun negP s = (rval_of neg_check s, shift_error)
            in
              add_guard negP res
            end
          | Unsigned _ => res
          | _ => raise General.Fail "RShift: impossible"
    in
      res
    end
end handle TYPE (s, tys, tms) => raise TYPE("binop_term ("^binopname bop^"): "^
                                            s, tys, tms)


type senv = (string * (string * int ctype) list) list

fun zero_term thy (senv:senv) cty = let
  open CalculateState
in
  (* create a term of the Isabelle type corresponding to cty which is
     everywhere zero at the leaf types *)
    case cty of
      Signed _ => mk_zero (ctype_to_typ(thy, cty))
    | Unsigned _ => mk_zero (ctype_to_typ(thy, cty))
    | PlainChar => mk_zero IntInfo.char
    | Ptr Void => mk_ptr (mk_zero addr_ty, @{typ unit})
    | Ptr cty0 => mk_ptr (mk_zero addr_ty, ctype_to_typ(thy,cty0))
    | StructTy s => let
        val flds = case assoc(senv, s) of
                     NONE => raise Fail ("zero_term: no s. info for "^s)
                   | SOME fs => map #2 fs
        val constructor_nm = Sign.intern_const thy (s ^ "." ^ s)
        val constructor_typ = valOf (Sign.const_type thy constructor_nm)
                              handle Option =>
                                     raise Fail ("Didn't get a type for "^
                                                 constructor_nm)
      in
        List.foldl (fn (fld,acc) => acc $ zero_term thy senv fld)
                   (Const(constructor_nm, constructor_typ))
                   flds
      end
    | Array(ty, _) => let
        val ity = ctype_to_typ(thy, cty)
        val ety = ctype_to_typ(thy, ty)
      in
        Const("Arrays.FCP", (nat --> ety) --> ity) $
             (Abs("_", nat, zero_term thy senv ty))
      end
    | EnumTy _ => mk_zero(ctype_to_typ(thy, Signed Int))
    | _ => raise Fail ("zero_term: can't handle: " ^ tyname cty)
end

fun mk_complit_upd thy cty rootty ((pth,value), ei) = let
  open complit
  fun mk_upds ty upds base =
      case upds of
        [] => K_rec ty $ base
      | idx i :: rest => let
          open Absyn
          val (subtype, _) = dest_array_type ty
          val subresult = mk_upds subtype rest base
        in
          Const("Arrays.fupdate", nat --> type_of subresult --> (ty --> ty)) $
               mk_nat_numeral i $ subresult
        end
      | fld s :: rest => let
          val _ = Feedback.informStr(7, "mk_complit_upd: Field "^s^" in type "^
                                         Syntax.string_of_typ (thy2ctxt thy) ty)
          val recd_ty = case ty of
                          Type(fullname, _) => fullname
                        | _ => raise Fail "mk_complit_upd: bad struct tyname"
          val upd = Sign.intern_const thy
                                      (recd_ty ^ "." ^ suffix Record.updateN s)
          val upd_ty = valOf (Sign.const_type thy upd)
                       handle Option =>
                              raise Fail ("mk_complit_upd: no type for "^upd)
          val subty = #1 (dom_rng (#1 (dom_rng upd_ty)))
          val subresult = mk_upds subty rest base
        in
          Const(upd, upd_ty) $ subresult
        end
  fun rval s = mk_upds rootty pth (rval_of value s) $ (rval_of ei s)
in
  mk_rval(rval, cty, false, eileft ei, eiright ei)
         |> add_ei_guards ei |> add_ei_guards value
end



fun expr_term ctxt cse tbuilders varinfo e : expr_info = let
  val thy = Proof_Context.theory_of ctxt
  val ecenv = ProgramAnalysis.cse2ecenv cse
  val senv = ProgramAnalysis.get_senv cse
  val tyinfo = ProgramAnalysis.cse_typing cse
  val error = fn s => error(SourcePos.toString (eleft e) ^ ": " ^ s)
  val expr_term = expr_term ctxt cse tbuilders varinfo
  val mk_rval = fn (f,cty) => mk_rval(f, cty, false, eleft e, eright e)
  val rval = rval_of
  val TB {var_updator, var_accessor, rcd_updator, rcd_accessor, ...} =
      tbuilders
  fun deref_action (ei : expr_info) : expr_info = let
    val ei = array_decay ei
    val e0_val = rval_of ei
    val heap_vi = (NameGeneration.global_heap_var,
                   MemoryModelExtras.extended_heap_ty,
                   NONE, (* no corresponding C type *)
                   CalculateState.NSGlobal)
    fun c_guard_check s = let
      val ptrval = e0_val s
    in
      (mk_cguard_ptr ptrval, c_guard_error)
    end
    fun check_safety s =
        MemoryModelExtras.check_safety
            {heap = var_accessor heap_vi s, ptrval = e0_val s}
    val cty = case ctype_of ei of
                Ptr x => x
              | _ => error ("deref_action: called on non-ptr value")
    fun rval st =
        MemoryModelExtras.dereference_ptr {heap = var_accessor heap_vi st,
                                           ptrval = e0_val st}
    fun lval value st =
        var_updator
            false
            heap_vi
            (MemoryModelExtras.mk_heap_update_extended
                 (mk_heap_upd (e0_val st, value)))
            st
  in
    EI {lval = SOME lval, addr = SOME e0_val, rval = rval, cty = cty,
        ibool = false, lguard = check_safety :: lguards_of ei,
        guard = c_guard_check :: guards_of ei, left = eileft ei,
        right = eiright ei}
  end
  fun handle_complit (cty : int ctype) dinits = let
    open complit
    fun trans_d (DesignE e) = idx (consteval ecenv e)
      | trans_d (DesignFld s) = fld s

    (* Arguments:
         * levelty is the enclosing type
         * curpath is the leaf-extended path of the "current object" with
           respect to levelty
         * init is the initialiser for the "current object"
    *)
    fun interpret_initializer levelty curpath init =
        case init of
          InitE e => let
            val ei0 = expr_term e
            val e_ty = ctype_of ei0
          in
            if aggregate_type e_ty then let
                (* Though an aggregate the initializer may be for
                   something not an immediate child.
                   This means we have to look along curpath for something
                   of the same type *)
              in
                case find_type levelty senv curpath e_ty of
                  NONE => error ("Leaf initialiser of type " ^ tyname e_ty ^
                                 " doesn't match up with required path")
                | SOME p => ([(p, ei0)], leaf_inc_path levelty senv p)
              end
            else (* e must be a leaf *) let
                val leafty = type_at_path levelty senv curpath
                val ei = typecast (thy, leafty, ei0)
                val p' = leaf_inc_path levelty senv curpath
              in
                ([(curpath, ei)], p')
              end
          end
        | InitList dilist => let
            val ty = type_at_path levelty senv [hd curpath]
            val _ = if not (aggregate_type ty) then
                      Feedback.warnStr'(eleft e, eright e,
                                        "Scalar initialisor in braces")
                    else ()
            val bumped = leaf_inc_path levelty senv [hd curpath]
            val (inits, _) = interpret_dilist ty (SOME (tl curpath)) dilist
          in
            (map (fn (p,ei) => (hd curpath :: p, ei)) inits, bumped)
          end

    and interpret_dilist levelty curpath_opt dinits =
        case dinits of
          [] => ([], curpath_opt)
        | (ds, init) :: rest => let
            val (translated_inits, p_opt) =
                case ds of
                  [] => let
                  in
                    case curpath_opt of
                      NONE => error "Initializer exhausts object"
                    | SOME p => interpret_initializer levelty p init
                  end
                | _ => let
                    val path = map trans_d ds
                    val extended_path = extend_to_leaf levelty senv path
                    val front_path = #1 (split_last path)
                    val levelty' = type_at_path levelty senv front_path
                    val (p_inits, p0_opt) =
                        interpret_initializer levelty'
                                              (List.drop (extended_path,
                                                          length path - 1))
                                              init
                  in
                    (map (fn (p,i) => (front_path @ p, i)) p_inits,
                     Option.map (fn p => front_path @ p) p0_opt)
                  end
            val (more_inits, p_opt) = interpret_dilist levelty p_opt rest
          in
            (translated_inits @ more_inits, p_opt)
          end
  in
    interpret_dilist cty (SOME (extend_to_leaf cty senv [])) dinits
  end
in
  case enode e of
    BinOp(bop, e1, e2) => let
      val e_t1 = expr_term e1
      val e_t2 = expr_term e2
    in
      binop_term thy bop e_t1 e_t2
    end
  | UnOp(uop, e) => unop_term thy (uop, eleft e) (expr_term e)
  | Constant lc => literalconstant lc
  | Var (s, ref extra) => let
      val _ = Feedback.informStr'(5, eleft e, eright e,
                                  "Looking up variable information for " ^ s)
      fun p (x as (ec, is_fn, s)) =
        (Feedback.informStr(5,
                            "Information is: ec = " ^ Bool.toString ec ^
                            ", is_fn = "^Bool.toString is_fn^
                            ", munge_name = "^MString.destPP s);
         x)
      val (ec, is_fn, s) =
          case extra of
              NONE => p (false, false, MString.mk s)
            | SOME (_, MungedVar {munge = s',...}) => p (false, false, s')
            | SOME (_, EnumC) => p (true, false, MString.mk s)
            | SOME (_, FunctionName) => p (false, true, MString.mk s)
      fun mk_ec s = let
        val constname = Sign.intern_const thy s
        fun rval _ = Const(constname, IntInfo.int)
      in
        mk_rval(rval, Signed Int)
      end
    in
      if ec then mk_ec (MString.dest s)
      else if is_fn then
        mk_rval((fn _ => mk_fnptr thy s), Ptr (#1 (valOf extra)))
      else
        case varinfo s of
          SOME (vi as (nm, typ, ctyopt, vsort)) => let
            open CalculateState
            val vsort =
                if Config.get_global thy CalculateState.globals_all_addressed then
                  case vsort of
                    UntouchedGlobal => AddressedGlobal
                  | NSGlobal => AddressedGlobal
                  | _ => vsort
                else vsort
          in
            case vsort of
              AddressedGlobal => let
                val _ = Feedback.informStr'(5, eleft e, eright e,
                                            "Variable " ^ MString.dest s ^
                                            " is an addressed global")
                open NameGeneration CalculateState

                (* FIXME XXX this is disgusting *)
                val nm' = unsuffix "_'" nm

                val fld_cty = valOf ctyopt
                              handle Option => raise Fail "ADGlob without cty"
                val fld_addr = mk_global_addr_ptr (nm', typ)
              in
                deref_action (mk_rval ((fn _ => fld_addr), Ptr fld_cty))
              end
            | UntouchedGlobal => let
                open NameGeneration
                val _ = Feedback.informStr'(5, eleft e, eright e,
                                            "Variable " ^ MString.dest s ^
                                            " is an untouched global")
                val constname =
                    s |> untouched_global_name
                      |> MString.dest
                      |> Consts.intern (Proof_Context.consts_of ctxt)
                val const =
                    Syntax.check_term ctxt (Const(constname,dummyT))
                fun rval _ = const
              in
                mk_rval(rval, valOf ctyopt)
              end
            | _ => let
                (* locals and NSGlobals are treated the same *)
                val _ = Feedback.informStr'(5, eleft e, eright e,
                                            "Variable " ^ MString.dest s ^
                                            " is a local/NSglobal")
                val ownership_guard =
                    case vsort of
                        NSGlobal =>
                        let
                          val owner = case extra of
                                          SOME(_, MungedVar mv) => #owned_by mv
                                        | _ => NONE
                        in
                          case owner of
                              NONE => []
                            | SOME oid =>
                              let
                                open NameGeneration
                                val ownership_vi =
                                    (global_var owned_by_fn_name,
                                     nat,
                                     NONE, (* no corresponding C type *)
                                     CalculateState.NSGlobal)
                                val own_v = var_accessor ownership_vi
                              in
                                [fn s =>
                                    (mk_eqt(own_v s, Free(oid,nat)),
                                     ownership_error)]
                              end
                        end
                      | _ => []
              in
                EI { lval = SOME (var_updator true vi),
                     addr = NONE,
                     rval = var_accessor vi,
                     cty = valOf ctyopt,
                     ibool = false,
                     lguard = ownership_guard,
                     guard = [],
                     left = eleft e,
                     right = eright e}
              end
          end
        | NONE => let
            val _ = warnStr'(eleft e, eright e,
                             "Confused that this code is executing at variable "
                             ^ MString.dest s)
          in
            case eclookup ecenv (MString.dest s) of
              NONE => error (": bad variable reference "^MString.dest s)
            | SOME _ => mk_ec (MString.dest s)
          end
    end
  | CondExp(g,te,ee) => let
      val gi = mk_isabool (expr_term g)
      val g_val = rval gi
      val tei = strip_kb (expr_term te)
      val eei = strip_kb (expr_term ee)
      val common = unify_types (ctype_of tei, ctype_of eei)
      val tei = if ctype_of tei = common then tei else typecast(thy,common,tei)
      val eei = if ctype_of eei = common then eei else typecast(thy,common,eei)
      val te_val = rval tei
      val ee_val = rval eei
      fun doit s = let
        val g_t = g_val s
        val t_t = te_val s
        val e_t = ee_val s
      in
        mk_cond(g_t, t_t, e_t)
      end
    in
      mk_rval(doit, ctype_of tei)
             |> add_ei_guards gi |> add_ei_guards tei |> add_ei_guards eei
    end
  | Deref e0 => deref_action (expr_term e0)
  | ArrayDeref(e1, e2) => let
      val ei1 = expr_term e1
    in
      case ctype_of ei1 of
        Ptr _ => expr_term
                 (ewrap(Deref(ewrap(BinOp(Plus,e1,e2), eleft e1, eright e2)),
                        eleft e1, eright e2))
      | Array(elty, sz) => let
          val (t1_lf, t1_rf) = (lval_of ei1, rval_of ei1)
          val ei2 = expr_term e2
          val in_bounds_guard_ei =
              mk_relbinop thy (@{const_name "less"}, @{const_name "word_sless"},
                               ei2, literalconstant (boglit (valOf sz)))
          fun in_bounds_guard s =
              (rval_of in_bounds_guard_ei s, arraybound_error)
          val in_bounds0 = let
            val gei = mk_relbinop thy
                                  (@{const_name "less_eq"}, @{const_name "word_sle"},
                                   literalconstant (boglit 0), ei2)
            val g = (fn s => (rval_of gei s, arraybound_error))
          in
            case integer_promotions (ctype_of ei2) of
              Signed _ => [g]
            | Unsigned _ => []
            | _ => raise Fail "Invariant failure in 0-ArrayBound guard generation"
          end
          val bounds_guard = in_bounds_guard :: in_bounds0

          val t2_rf = rval (strip_kb ei2)
          fun lval value st = let
            val array_rval = t1_rf st
            val array_ty = type_of array_rval
          in
            valOf t1_lf
                  (mk_array_update_t array_ty $ array_rval $
                                     (IntInfo.ity_to_nat (t2_rf st)) $
                                     value)
                  st
          end
          fun rval st =
              mk_array_nth (t1_rf st, IntInfo.ity_to_nat (t2_rf st))
          val addr =
              case addr_of ei1 of
                NONE => NONE
              | SOME _ => SOME
                              (fn st => let
                                    val ei1' = array_decay ei1
                                  in
                                    rval_of (binop_term thy Plus ei1' ei2) st
                                  end)
        in
          EI { lval = case t1_lf of NONE => NONE | SOME _ => SOME lval,
               addr = addr, rval = rval, cty = elty,
               ibool = false, lguard = lguards_of ei1 @ lguards_of ei2,
               guard = bounds_guard @ guards_of ei1 @ guards_of ei2,
               left = eleft e,
               right = eright e}
        end
      | _ => error "Array dereference with impossible type"
    end
  | StructDot (e0, fld) => let
      val e0_val = expr_term e0
      val e0_r = rval e0_val
      val sname =
          case ctype_of e0_val of
            StructTy s => s
          | _ => error "Expression on left of . doesn't have struct type"
      fun heap_deref a = let
          val struct_ty =
              CalculateState.ctype_to_typ(thy, StructTy sname)
          fun rval st =
              mk_field_lvalue_ptr ctxt
                 (a st,
                  mk_qualified_field_name fld,
                  struct_ty,
                  CalculateState.ctype_to_typ(thy, tyinfo e))
        in
          deref_action (mk_rval(rval, Ptr (tyinfo e)))
        end
      fun addr_of_option f g =
          case addr_of e0_val of
            SOME a => f (heap_deref a)
          | NONE => g
      val addr = addr_of_option addr_of NONE
      val lval = addr_of_option lval_of
          (case lval_of e0_val of
             SOME f => let
                fun lval0 (value : term) st =
                    f (rcd_updator (sname, fld) value (e0_r st)) st
              in
                SOME lval0
              end
           | NONE => NONE)
      fun rval st = addr_of_option (fn x => rval_of x st)
                                   (rcd_accessor (sname, fld) (e0_r st))
      val lguard = lguards_of e0_val
      val guard = guards_of e0_val
    in
      EI {lval = lval, addr = addr, rval = rval,
          cty = addr_of_option ctype_of (tyinfo e),
          ibool = false, lguard = lguard, guard = guard,
          left = eleft e, right = eright e}
    end
  | TypeCast(cty,e0) => typecast (thy, constify_abtype ecenv (node cty),
                                  expr_term e0)
  | Sizeof e0 => let
      val ity = CalculateState.ctype_to_typ (thy, tyinfo e0)
      fun rval _ = IntInfo.nat_to_word ImplementationTypes.size_t
                                       (mk_sizeof (mk_TYPE ity))
    in
      mk_rval (rval, ImplementationTypes.size_t)
    end
  | SizeofTy cty => let
      val ity = CalculateState.ctype_to_typ
                    (thy,constify_abtype ecenv (node cty))
      fun rval _ = IntInfo.nat_to_word ImplementationTypes.size_t
                                       (mk_sizeof (mk_TYPE ity))
    in
      mk_rval(rval, ImplementationTypes.size_t)
    end
  | CompLiteral(cty0, inits) => let
      open complit
      val cty = constify_abtype ecenv cty0
      val (updates,_) = handle_complit cty inits handle Fail s => error s
      val _ =
          informStr (7, "Compound literal updates are: "^
                        String.concat
                            (map (fn (vp,_) => vpl_toString vp ^ ", ") updates))
      val zero_tm = zero_term thy senv cty
      val _ = informStr(7, "Compound literal base zero is: "^
                           Syntax.string_of_term (thy2ctxt thy)
                                                 zero_tm)
      val ei0 = mk_rval((fn _ => zero_tm), cty)
      val typ = CalculateState.ctype_to_typ (thy, cty)
    in
      List.foldl (mk_complit_upd thy cty typ) ei0 updates
    end
  | Arbitrary cty0 => let
      val cty = constify_abtype ecenv cty0
      fun rval _ = mk_arbitrary (CalculateState.ctype_to_typ (thy, cty))
    in
      mk_rval(rval, cty)
    end
  | EFnCall _ => error (SourcePos.toString (eleft e) ^
                        ": there shouldn't be an embedded function call here")
  | MKBOOL e => strip_kb (mk_isabool (expr_term e))
end


end; (* struct *)
