(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_MP
imports Sep_Tactic_Helpers Sep_Provers Sep_Cancel_Set
begin

lemma sep_mp_gen: "((Q \<longrightarrow>* R) \<and>* Q') s \<Longrightarrow> (\<And>s. Q' s \<Longrightarrow> Q s) \<Longrightarrow> R s"
  by (clarsimp simp: sep_conj_def sep_impl_def)

lemma sep_mp_frame_gen: "\<lbrakk>((Q \<longrightarrow>* R) \<and>* Q' \<and>* R') s; (\<And>s. Q' s \<Longrightarrow> Q s)\<rbrakk> \<Longrightarrow> (R \<and>* R') s"
    by (metis sep_conj_left_commute sep_globalise sep_mp_frame)

lemma sep_impl_simpl: 
     "(P \<and>* Q \<longrightarrow>* R) s \<Longrightarrow> (P \<longrightarrow>* Q \<longrightarrow>* R) s"
  apply (erule sep_conj_sep_impl)
  apply (erule sep_conj_sep_impl)
  apply (clarsimp simp: sep_conj_assoc)
  apply (erule sep_mp)
done

lemma sep_wand_frame_lens: "((P \<longrightarrow>* Q) \<and>* R) s \<Longrightarrow> (\<And>s. T s = R s) ==> ((P \<longrightarrow>* Q) \<and>* T) s"
  by (metis sep_conj_commute sep_conj_impl1)

ML {*
  fun sep_wand_frame_drule ctxt = 
     let val lens  = dresolve_tac ctxt [@{thm sep_wand_frame_lens}]
         val lens' = dresolve_tac ctxt [@{thm sep_asm_eq}]
         val r = rotator' ctxt
         val sep_cancel_thms = rev (SepCancel_Rules.get ctxt)
      in sep_apply_tactic ctxt (dresolve_tac ctxt [@{thm sep_mp_frame_gen}]) sep_cancel_thms |> r lens |> r lens'
   end; 

   fun sep_mp_solver ctxt  =
    let val sep_mp = sep_apply_tactic ctxt (dresolve0_tac [@{thm sep_mp_gen}]) ((rev o SepCancel_Rules.get) ctxt)
        val taclist = [sep_drule_comb_tac false [@{thm sep_empty_imp}] ctxt,
                       sep_drule_tac sep_mp ctxt,
                       sep_drule_tac (sep_drule_tactic ctxt [@{thm sep_impl_simpl}]) ctxt,
                       sep_wand_frame_drule ctxt ]
        val check = DETERM o (sep_drule_tac (sep_select_tactic (dresolve0_tac [@{thm sep_wand_frame_lens}]) [1] ctxt) ctxt)
         
   in  CHANGED_PROP o (check THEN_ALL_NEW REPEAT_ALL_NEW ( FIRST' taclist) )
   end;
  
   val sep_mp_method = SIMPLE_METHOD' o sep_mp_solver 
*}
 
method_setup sep_mp = {* Scan.succeed sep_mp_method *}

end
