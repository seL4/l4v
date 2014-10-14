(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
  "../../lib/OptionMonadWP"
  AutoCorresSimpset
  keywords "autocorres" :: thy_decl
begin

(* Remove various rules from the default simpset that don't really help. *)
declare word_neq_0_conv [simp del]
declare neq0_conv [simp del]
declare fun_upd_apply[simp del]

declare hoare_wp_combsE(4) [wp del, wp_comb del]
declare hoare_wp_combsE(5) [wp del, wp_comb del]
declare hoare_wp_combsE(6) [wp del, wp_comb del]

lemmas [wp del, wp_comb del] = hoare_wp_state_combsE

declare hoare_wp_combs(1)  [wp del, wp_comb del]
declare hoare_wp_combs(3)  [wp del, wp_comb del]

(* Machinery for generating final corres thm *)
lemma corresTA_trivial: "corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  apply (auto simp: corresTA_def intro: corresXF_I)
  done

(* Dummy precondition for more convenient usage *)
lemma corresTA_trivial_from_heap_lift:
  "L2Tcorres st A C \<Longrightarrow> corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  by (rule corresTA_trivial)

lemma corresXF_from_L2_call:
  "L2_call c_WA = A \<Longrightarrow> corresXF (\<lambda>s. s) (\<lambda>rv s. rv) y (\<lambda>_. True) A c_WA"
  apply (clarsimp simp: corresXF_def L2_call_def L2_defs)
  apply (monad_eq split: sum.splits)
  apply force
  done

(* The final ccorres theorem. *)
lemma ccorres_chain:
"\<lbrakk> L1corres Gamma c_L1 c;
   L2corres st_L2 rx_L2 (\<lambda>_. ()) P_L2 c_L2 c_L1;
   L2Tcorres st_HL c_HL c_L2;
   corresTA P_WA rx_WA ex_WA c_WA c_HL;
   L2_call c_WA = A
 \<rbrakk> \<Longrightarrow>
  ccorres (st_HL o st_L2) Gamma (rx_WA o rx_L2) (P_L2 and (P_WA o st_HL o st_L2)) A c"
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

(* Rewrites that will be applied before collecting statistics. *)
lemmas ac_statistics_rewrites =
    (* Setup "L1_seq" to have a sane lines-of-spec measurement. *)
    L1_seq_def bindE_K_bind [THEN eq_reflection]
    (* Convert L2 to standard exception monads. *)
    L2_defs'

ML_file "../../lib/set.ML"
ML_file "autocorres_data.ML"
ML_file "trace_antiquote.ML"
ML_file "mkterm_antiquote.ML"
ML_file "utils.ML"
ML_file "statistics.ML"
ML_file "program_info.ML"
ML_file "function_info.ML"
ML_file "prog.ML"
ML_file "autocorres_util.ML"
ML_file "exception_rewrite.ML"
ML_file "simpl_conv.ML"
ML_file "l2_opt.ML"
ML_file "local_var_extract.ML"
ML_file "record_utils.ML"
ML_file "heap_lift_base.ML"
ML_file "heap_lift.ML"
ML_file "word_abstract.ML"
ML_file "pretty_bound_var_names.ML"
ML_file "monad_convert.ML"
ML_file "type_strengthen.ML"
ML_file "autocorres.ML"

(* Setup "autocorres" keyword. *)
ML {*
  Outer_Syntax.command @{command_spec "autocorres"}
    "Abstract the output of the C parser into a monadic representation."
    (AutoCorres.autocorres_parser >>
      (Toplevel.theory o (fn (opt, filename) => AutoCorres.do_autocorres opt filename)))
*}

end
