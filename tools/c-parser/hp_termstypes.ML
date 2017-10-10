(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature HP_TERMS_TYPES =
sig

  val StrictC_errortype_ty : typ  (* errors are from failed guards *)
  val c_exntype_ty : typ   (* exns are flow-control interrupts:
                                return, break and continue *)
  val mk_com_ty : typ list -> typ (* list of three elements *)

  val div_0_error : term
  val shift_error : term
  val safety_error : term
  val c_guard_error : term
  val arraybound_error : term
  val signed_overflow_error : term
  val dont_reach_error : term
  val side_effect_error : term
  val ownership_error : term
  val unspecified_syntax_error1 : term
  val unspecified_syntax_error2 : string -> term


  val Continue_exn : term
  val Return_exn : term
  val Break_exn : term

  val list_mk_seq : term list -> term
  val mk_VCGfn_name : theory -> string -> term
  val mk_basic_t : typ list -> term
  val mk_call_t : typ list -> term
  val mk_callreturn : typ -> typ -> term
  val mk_catch_t : typ list -> term
  val mk_cbreak : theory -> typ list -> typ -> term
  val mk_ccatchbrk : theory -> typ list -> typ -> term
  val mk_cond_t : typ list -> term
  val mk_creturn : theory -> typ list -> typ -> term -> term -> term
  val mk_creturn_void : theory -> typ list -> typ -> term
  val mk_dyncall_t : typ list -> term
  val mk_empty_INV : typ -> term
  val mk_guard : term -> term -> term -> term
  val mk_skip_t : typ list -> term
  val mk_Spec : typ list * term -> term
  val mk_specAnno : term -> term -> term -> term
  val mk_switch : term * term -> term
  val mk_throw_t : typ list -> term
  val mk_while_t : typ list -> term


end

structure HP_TermsTypes : HP_TERMS_TYPES =
struct

open IsabelleTermsTypes

val StrictC_errortype_ty = @{typ "CProof.strictc_errortype"}
val c_exntype_ty = @{typ "CProof.c_exntype"}

fun mk_com_ty args = Type("Language.com", args)

fun mk_skip_t tyargs = Const("Language.com.Skip", mk_com_ty tyargs)

val Return_exn = @{const "CProof.c_exntype.Return"}
val Break_exn = @{const "CProof.c_exntype.Break"}
val Continue_exn = @{const "CProof.c_exntype.Continue"}

fun mk_VCGfn_name thy s =
    Const(Sign.intern_const thy (suffix HoarePackage.proc_deco s), int)

fun mk_basic_t tyargs = let
  val statety = hd tyargs
in
  Const(@{const_name "Language.com.Basic"},
        (statety --> statety) --> mk_com_ty tyargs)
end
fun mk_call_t tyargs = let
  val sarg = hd tyargs
  val parg = List.nth (tyargs, 1)
  val sarg2 = sarg --> sarg
  val sarg3 = sarg --> sarg2
  val com_ty = mk_com_ty tyargs
  val s2_to_com = sarg --> (sarg --> com_ty)
in
  Const(@{const_name "Language.call"},
        sarg2 --> (parg --> (sarg3 --> (s2_to_com --> com_ty))))
end

fun mk_dyncall_t tyargs = let
  val sarg = hd tyargs
  val parg = List.nth(tyargs, 1)
  val s2p_arg = sarg --> parg
  val sarg2 = sarg --> sarg
  val sarg3 = sarg --> sarg2
  val com_ty = mk_com_ty tyargs
  val s2_to_com = sarg --> (sarg --> com_ty)
in
  Const(@{const_name "Language.dynCall"},
        sarg2 --> (s2p_arg --> (sarg3 --> (s2_to_com --> com_ty))))
end

fun mk_callreturn globty statety = let
  val svar = Free("s", statety)
  val tvar = Free("t", statety)
  val gupdate = Const(suffix Record.updateN "StateSpace.state.globals",
                      (globty --> globty) --> (statety --> statety))
  val gaccess = Const(@{const_name "StateSpace.state.globals"},
                      statety --> globty)
  val Kupd = K_rec globty $ (gaccess $ tvar)
in
  mk_abs(svar, mk_abs(tvar, gupdate $ Kupd $ svar))
end


fun mk_while_t tyargs = let
  val statety = hd tyargs
  val stateset_ty = mk_set_type statety
  val state_squared_set_ty = mk_set_type (mk_prod_ty (statety, statety))
  val com = mk_com_ty tyargs
in
  Const(@{const_name "Language.whileAnno"},
        stateset_ty --> stateset_ty --> state_squared_set_ty  --> com --> com)
end
fun mk_seq_t tyargs = let
  val comty = mk_com_ty tyargs
in
  Const(@{const_name "Language.com.Seq"}, comty --> (comty --> comty))
end
fun mk_cond_t tyargs = let
  val statety = hd tyargs
  val comty = mk_com_ty tyargs
in
  Const(@{const_name "Language.com.Cond"},
        mk_set_type statety --> (comty --> (comty --> comty)))
end

fun mk_seq(s1, s2) = let
  val ty1 = type_of s1
            handle TYPE (msg, tys, tms) =>
                   raise TYPE ("mk_seq: "^msg, tys, tms)
  val tyargs = case ty1 of
                 Type(_, args) => args
               | _ => raise TYPE ("mk_seq: unexpected type for statement",
                                  [ty1], [s1])
in
  mk_seq_t tyargs $ s1 $ s2
end

fun list_mk_seq stmts =
    case stmts of
      [] => error "list_mk_seq: empty list as argument"
    | s::rest => List.foldl (fn (s', acc) => mk_seq(acc, s')) s rest

fun mk_throw_t tyargs =
    Const(@{const_name "Language.com.Throw"}, mk_com_ty tyargs)
fun mk_catch_t tyargs = let
  val comty = mk_com_ty tyargs
in
  Const(@{const_name "Language.com.Catch"}, comty --> (comty --> comty))
end

fun mk_switch (guard, cases) = let
  val cases_ty = type_of cases
  val cty = dest_list_type cases_ty
  val (_, sty) = dest_prod_ty cty
in
  Const(@{const_name "Language.switch"},
        type_of guard --> cases_ty --> sty) $ guard $ cases
end

fun mk_global_exn_var_update (thy : theory) (statety : Term.typ) : Term.term = let
    val exnvar_ty = (c_exntype_ty --> c_exntype_ty) --> statety --> statety
    val exnvar_name = suffix Record.updateN NameGeneration.global_exn_var
in
    Const (Sign.intern_const thy exnvar_name, exnvar_ty)
end

fun mk_creturn (thy : theory)
               (tyargs : Term.typ list)
               (statety : Term.typ)
               (updf : Term.term)
               (v : Term.term) : Term.term = let
    val exnvar = mk_global_exn_var_update thy statety
in
    Const (@{const_name "CLanguage.creturn"},
           (type_of exnvar) --> (type_of updf) --> (type_of v) --> mk_com_ty tyargs
          ) $ exnvar $ updf $ v
end

fun mk_creturn_void (thy : theory)
                    (tyargs : Term.typ list)
                    (statety : Term.typ) = let
    val exnvar      = mk_global_exn_var_update thy statety
in
    Const (@{const_name "CLanguage.creturn_void"},
           type_of exnvar --> mk_com_ty tyargs) $ exnvar
end

fun mk_cbreak_const (thy : theory)
              (tyargs : Term.typ list)
              (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var_update thy statety
in
    Const (@{const_name "CLanguage.cbreak"}, (type_of exnvar) --> mk_com_ty tyargs)
end

fun mk_cbreak (thy : theory)
              (tyargs : Term.typ list)
              (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var_update thy statety
in
    mk_cbreak_const thy tyargs statety $ exnvar
end

fun mk_global_exn_var (thy : theory) (statety : Term.typ) : Term.term = let
    val exnvar_ty = statety --> c_exntype_ty
    val exnvar_name = NameGeneration.global_exn_var
in
    Const (Sign.intern_const thy exnvar_name, exnvar_ty)
end

fun mk_ccatchbrk (thy : theory)
                 (tyargs : Term.typ list)
                 (statety : Term.typ) = let
    val exnvar  = mk_global_exn_var thy statety
in
    Const (@{const_name "CLanguage.ccatchbrk"}, (type_of exnvar) --> mk_com_ty tyargs) $ exnvar
end

val div_0_error      = @{const "Div_0"}
val c_guard_error    = @{const "C_Guard"}
val safety_error     = @{const "MemorySafety"}
val shift_error      = @{const "ShiftError"}
val side_effect_error= @{const "SideEffects"}
val arraybound_error = @{const "ArrayBounds"}
val signed_overflow_error = @{const "SignedArithmetic"}
val dont_reach_error = @{const "DontReach"}
val unspecified_syntax_error = @{const "UnspecifiedSyntax"}
val ownership_error = @{const "OwnershipError"}

val unspecified_syntax_error1 = @{const "UnspecifiedSyntax"}
fun unspecified_syntax_error2 s = @{const "unspecified_syntax_error"}
    $ mk_string s

fun mk_guard_t tyargs =
    Const(@{const_name "Language.com.Guard"},
          List.last tyargs --> mk_set_type (hd tyargs) -->
          mk_com_ty tyargs --> mk_com_ty tyargs)

fun mk_guard gdset gdtype com = let
  val tyargs =
      case type_of com of
        Type(@{type_name "Language.com"}, args) => args
      | _ => raise Fail "mk_guard: command not of type \"Language.com\""
in
  mk_guard_t tyargs $ gdtype $ gdset $ com
end

fun mk_Spec(styargs, reln) =
    Const(@{const_name "Language.Spec"}, type_of reln --> mk_com_ty styargs) $
    reln


fun mk_specAnno pre body post = let
  val pre_type = type_of pre
  val (bty, stateset_ty) = dom_rng pre_type
  val bvar = case pre of
               Abs(nm, _, _) => nm
             | _ => raise Fail "mk_specAnno: pre not an abstraction"
  val body_type = type_of body
  val specAnno_ty =
      pre_type --> body_type --> pre_type --> pre_type -->
      #2 (dom_rng body_type)
in
  Const(@{const_name "Language.specAnno"}, specAnno_ty) $ pre $ body $ post $
       Abs(bvar, bty, Const("{}", stateset_ty))
end

fun mk_empty_INV ty = mk_collect_t ty $ Abs("x", ty, mk_arbitrary bool)

end
