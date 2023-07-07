(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Top-level AutoCorres theorem.
 *)

theory AutoCorres
imports
  SimplConv
  ExceptionRewrite
  L1Valid
  LocalVarExtract
  L2Peephole
  L2Opt
  TypeStrengthen
  Polish
  TypHeapSimple
  HeapLift
  WordAbstract
  "Monads.Reader_Option_VCG"
  "Eisbach_Tools.Apply_Trace"
  AutoCorresSimpset
  "ML_Utils.MkTermAntiquote"
  "ML_Utils.TermPatternAntiquote"
  keywords "autocorres" :: thy_decl
begin

(* Remove various rules from the default simpset that don't really help. *)
declare word_neq_0_conv [simp del]
declare neq0_conv [simp del]
declare fun_upd_apply[simp del]
declare of_int_and_nat[simp del]

(* Remove wp combinators which are problematic for AutoCorres
   and restore some prior configuration. *)
declare hoare_wp_combsE [wp del, wp_comb del]
declare hoare_wp_combs [wp del, wp_comb del]
declare hoare_wp_state_combsE [wp del, wp_comb del]

lemmas hoare_wp_combsE_autocorres [wp_comb]
    = hoare_vcg_precond_impE hoare_vcg_precond_impE_R validE_validE_R
lemmas hoare_wp_combs_autocorres [wp_comb]
    = hoare_vcg_precond_imp
declare validNF_weaken_pre[wp_comb]
declare validE_NF_weaken_pre[wp_comb]
bundle nf_no_pre
    = validNF_weaken_pre[wp_pre del] validE_NF_weaken_pre[wp_pre del]



(* Machinery for generating final corres thm *)
lemma corresTA_trivial: "corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  apply (auto intro: corresXF_I)
  done

(* Dummy preconditions for more convenient usage *)
lemma L2Tcorres_trivial_from_local_var_extract:
  "L2corres st rx ex P A C \<Longrightarrow> L2Tcorres id A A"
  by (rule L2Tcorres_id)

lemma corresTA_trivial_from_heap_lift:
  "L2Tcorres st A C \<Longrightarrow> corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  by (rule corresTA_trivial)


lemma corresXF_from_L2_call:
  "L2_call c_WA = A \<Longrightarrow> corresXF (\<lambda>s. s) (\<lambda>rv s. rv) y (\<lambda>_. True) A c_WA"
  apply (clarsimp simp: corresXF_def L2_call_def L2_defs)
  apply (monad_eq split: sum.splits)
  apply force
  done

(* The final ac_corres theorem. *)
lemma ac_corres_chain:
"\<lbrakk> L1corres check_termination Gamma c_L1 c;
   L2corres st_L2 rx_L2 (\<lambda>_. ()) P_L2 c_L2 c_L1;
   L2Tcorres st_HL c_HL c_L2;
   corresTA P_WA rx_WA ex_WA c_WA c_HL;
   L2_call c_WA = A
 \<rbrakk> \<Longrightarrow>
  ac_corres (st_HL o st_L2) check_termination Gamma (rx_WA o rx_L2) (P_L2 and (P_WA o st_HL o st_L2)) A c"
  apply (rule ccorresE_corresXF_merge)
       apply (unfold L1corres_alt_def)
       apply assumption
      apply (unfold L2corres_def L2Tcorres_def corresTA_def)
      apply (drule corresXF_from_L2_call)
      apply ((drule (1) corresXF_corresXF_merge)+, assumption)
     apply (clarsimp simp: L2_call_def L2_defs)
     apply (rule handleE'_nothrow_rhs)
     apply simp
    apply clarsimp
   apply clarsimp
  apply clarsimp
  done

(*
 * Functions that don't have a body in the C file (i.e., they are
 * prototyped and called, but are never defined) will be abstracted
 * into a "fail" command by AutoCorres.
 *
 * More accurately, they will be abstracted into:
 *
 *     guard (\<lambda>s. INVALID_FUNCTION)
 *
 * where "INVALID_FUNCTION" is "False").
 *
 * We convert this above form into this alternative definition, so
 * users have a better idea what is going on.
 *)
definition "FUNCTION_BODY_NOT_IN_INPUT_C_FILE \<equiv> fail"

lemma [polish]:
  "guard (\<lambda>s. UNDEFINED_FUNCTION) \<equiv> FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "(FUNCTION_BODY_NOT_IN_INPUT_C_FILE >>= m) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "unknown >>= (\<lambda>x. FUNCTION_BODY_NOT_IN_INPUT_C_FILE) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "unknown >>= (K_bind FUNCTION_BODY_NOT_IN_INPUT_C_FILE) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (monad_eq simp: UNDEFINED_FUNCTION_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def)+

(* Rewrites that will be applied before collecting statistics. *)
lemmas ac_statistics_rewrites =
    (* Setup "L1_seq" to have a sane lines-of-spec measurement. *)
    L1_seq_def bindE_K_bind [THEN eq_reflection]
    (* Convert L2 to standard exception monads. *)
    L2_defs'

(* Utils *)
ML_file "../../lib/set.ML"
ML_file "trace_antiquote.ML"
ML_file "utils.ML"

(* Common data structures *)
ML_file "program_info.ML"
ML_file "function_info.ML"
ML_file "autocorres_trace.ML"
ML_file "autocorres_data.ML"

(* Common control code *)
ML_file "autocorres_util.ML"

(* L1 *)
ML_file "exception_rewrite.ML"
ML_file "simpl_conv.ML"
(* L2 *)
ML_file "prog.ML"
ML_file "l2_opt.ML"
ML_file "local_var_extract.ML"
(* HL *)
ML_file "record_utils.ML"
ML_file "heap_lift_base.ML"
ML_file "heap_lift.ML"
(* WA *)
ML_file "word_abstract.ML"
ML_file "pretty_bound_var_names.ML"
ML_file "monad_convert.ML"
(* TS *)
ML_file "type_strengthen.ML"

ML_file "autocorres.ML"

(* Setup "autocorres" keyword. *)
ML \<open>
  Outer_Syntax.command @{command_keyword "autocorres"}
    "Abstract the output of the C parser into a monadic representation."
    (AutoCorres.autocorres_parser >>
      (Toplevel.theory o (fn (opt, filename) => AutoCorres.do_autocorres opt filename)))
\<close>

end
