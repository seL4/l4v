(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_Cancel
imports Sep_Provers Sep_Tactic_Helpers Sep_Cancel_Set
begin

(* Sep_Cancel performs cancellative elimination of conjuncts *)


lemma sep_curry': "\<lbrakk>(P \<and>* F) s; \<And>s. (Q \<and>* P \<and>* F) s \<Longrightarrow> R s\<rbrakk> \<Longrightarrow> (Q \<longrightarrow>* R) s"
  by (metis (full_types) sep.mult_commute sep_curry)

lemma sep_conj_sep_impl_safe: 
  "(P \<longrightarrow>* P') s \<Longrightarrow> (\<And>s. ((P \<longrightarrow>* P') \<and>* Q) s \<Longrightarrow> (Q') s) \<Longrightarrow> (Q \<longrightarrow>* Q') s" 
  by (rule sep_curry)

lemma  sep_conj_sep_impl_safe': "P s \<Longrightarrow> (\<And>s. (P \<and>* Q) s \<Longrightarrow> (P \<and>* R) s) \<Longrightarrow> (Q \<longrightarrow>* P \<and>* R) s" 
  by (rule sep_curry)

lemma sep_wand_lens_simple: "(\<And>s. T s = (Q \<and>* R) s) \<Longrightarrow> (P \<longrightarrow>* T) s \<Longrightarrow> (P \<longrightarrow>* Q \<and>* R) s"
  by (clarsimp simp: sep_impl_def)

schematic_goal schem_impAny: " (?C \<and>* B) s \<Longrightarrow> A s" by (erule sep_mp)

ML {* 
  fun sep_cancel_tactic ctxt concl  = 
    let val thms = rev (SepCancel_Rules.get ctxt)
        val tac  = assume_tac ctxt ORELSE'
                   eresolve_tac ctxt [@{thm sep_mp}, @{thm sep_conj_empty}, @{thm sep_empty_conj}] ORELSE'
                   sep_erule_tactic ctxt thms
        val direct_tac = eresolve_tac ctxt thms
        val safe_sep_wand_tac = rotator' ctxt (resolve0_tac [@{thm sep_wand_lens_simple}]) (eresolve0_tac [@{thm sep_conj_sep_impl_safe'}])
        fun sep_cancel_tactic_inner true   = sep_erule_full_tac' tac ctxt
          | sep_cancel_tactic_inner false  = sep_erule_full_tac tac ctxt
  in sep_cancel_tactic_inner concl ORELSE'
      eresolve_tac ctxt [@{thm sep_curry'}, @{thm sep_conj_sep_impl_safe}, @{thm sep_imp_empty}, @{thm sep_empty_imp'}] ORELSE'
      safe_sep_wand_tac ORELSE'
      direct_tac
  end

  fun sep_cancel_tactic' ctxt concl =
    let
      val sep_cancel = sep_cancel_tactic ctxt
    in 
      (sep_flatten ctxt THEN_ALL_NEW sep_cancel concl) ORELSE' sep_cancel concl
    end

  fun sep_cancel_method (concl,_) ctxt = SIMPLE_METHOD' (sep_cancel_tactic' ctxt concl)
  
  val sep_cancel_syntax =
    Method.sections [Args.add -- Args.colon >> K (Method.modifier SepCancel_Rules.add @{here})];
  
  val sep_cancel_syntax' =
    Scan.lift (Args.mode "concl") -- sep_cancel_syntax  
*}

method_setup sep_cancel = 
  {* sep_cancel_syntax' >> sep_cancel_method *}  {* Simple elimination of conjuncts *}

end
