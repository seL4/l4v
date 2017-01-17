(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Interrupt_AC
imports
  Finalise_AC
  (* cap_delete_one *)
begin

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  authorised_irq_ctl_inv :: "'a PAS \<Rightarrow> Invocations_A.irq_control_invocation \<Rightarrow> bool"
where
  "authorised_irq_ctl_inv aag cinv \<equiv>
     case cinv of
         IRQControl word x1 x2 \<Rightarrow> is_subject aag (fst x1) \<and> is_subject aag (fst x2) \<and>
                                  (pasSubject aag, Control, pasIRQAbs aag word) \<in> pasPolicy aag 
        | _ \<Rightarrow> True"

lemma invoke_irq_control_pas_refined:
  "\<lbrace>pas_refined aag and K (authorised_irq_ctl_inv aag irq_ctl_inv)\<rbrace>
     invoke_irq_control irq_ctl_inv
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (cases irq_ctl_inv, simp_all add: arch_invoke_irq_control_def)
  apply (wpsimp wp: cap_insert_pas_refined)
  apply (clarsimp simp: clas_no_asid cap_links_irq_def authorised_irq_ctl_inv_def aag_cap_auth_def)
  done

definition
  authorised_irq_hdl_inv :: "'a PAS \<Rightarrow> Invocations_A.irq_handler_invocation \<Rightarrow> bool"
where
  "authorised_irq_hdl_inv aag hinv \<equiv>
     case hinv of
         irq_handler_invocation.SetIRQHandler word cap x \<Rightarrow> is_subject aag (fst x) \<and> pas_cap_cur_auth aag cap \<and> is_subject_irq aag word
       | irq_handler_invocation.ClearIRQHandler word     \<Rightarrow> is_subject_irq aag word
       | _                                               \<Rightarrow> True"

lemma invoke_irq_handler_pas_refined:
  "\<lbrace>pas_refined aag and K (authorised_irq_hdl_inv aag irq_inv)\<rbrace>
     invoke_irq_handler irq_inv
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases irq_inv, simp_all add: authorised_irq_hdl_inv_def)
  apply (wp cap_insert_pas_refined | strengthen  aag_Control_owns_strg | simp add: pas_refined_wellformed)+
  done

lemma invoke_irq_control_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and K (authorised_irq_ctl_inv aag irq_ctl_inv)\<rbrace>
     invoke_irq_control irq_ctl_inv
   \<lbrace>\<lambda>y. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases irq_ctl_inv, simp_all add: arch_invoke_irq_control_def authorised_irq_ctl_inv_def)
  apply (wp cap_insert_integrity_autarch aag_Control_into_owns_irq | simp | blast)+
  done

lemma integrity_irq_masks [iff]:
  "integrity aag X st (s\<lparr>machine_state := machine_state s \<lparr>irq_masks := v \<rparr>\<rparr>) = integrity aag X st s"
  unfolding integrity_def
  by (simp )

lemma invoke_irq_handler_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and K (authorised_irq_hdl_inv aag irq_inv)\<rbrace>
     invoke_irq_handler irq_inv
   \<lbrace>\<lambda>y. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases irq_inv, simp_all add: authorised_irq_hdl_inv_def)
  apply (rule hoare_pre)
  apply (wp cap_insert_integrity_autarch get_irq_slot_owns dmo_wp | simp add: maskInterrupt_def )+
  done


lemma decode_irq_control_invocation_authorised [wp]:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst slot) \<and> (\<forall>cap \<in> set caps. pas_cap_cur_auth aag cap) \<and>
                         (args \<noteq> [] \<longrightarrow> (pasSubject aag, Control, pasIRQAbs aag (ucast (args ! 0))) \<in> pasPolicy aag))\<rbrace>
  decode_irq_control_invocation info_label args slot caps
  \<lbrace>\<lambda>x s. authorised_irq_ctl_inv aag x\<rbrace>, -"
  unfolding decode_irq_control_invocation_def authorised_irq_ctl_inv_def arch_check_irq_def
  apply (rule hoare_gen_asmE)
  apply (rule hoare_pre)
   apply (simp add: Let_def split del: if_split cong: if_cong)
   apply (wp whenE_throwError_wp hoare_vcg_imp_lift hoare_drop_imps
              | strengthen  aag_Control_owns_strg
              | simp add: o_def del: hoare_True_E_R)+
  apply (cases args, simp_all)
  apply (cases caps, simp_all)
    apply (simp add: ucast_mask_drop)
  apply (auto simp: is_cap_simps cap_auth_conferred_def
                 pas_refined_wellformed
                 pas_refined_all_auth_is_owns aag_cap_auth_def)
  done

lemma decode_irq_handler_invocation_authorised [wp]:
  "\<lbrace>K (is_subject_irq aag irq \<and> (\<forall>cap_slot \<in> set caps. pas_cap_cur_auth aag (fst cap_slot) \<and> is_subject aag (fst (snd cap_slot))))\<rbrace>
  decode_irq_handler_invocation info_label irq caps
  \<lbrace>\<lambda>x s. authorised_irq_hdl_inv aag x\<rbrace>, -"
  unfolding decode_irq_handler_invocation_def authorised_irq_hdl_inv_def
  apply (rule hoare_pre)
   apply (simp add: Let_def split_def split del: if_split cong: if_cong)
   apply wp
  apply (auto dest!: hd_in_set)
  done

end

end
