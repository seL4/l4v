(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Interrupt_AC
imports
  ArchFinalise_AC
begin


definition authorised_irq_hdl_inv :: "'a PAS \<Rightarrow> Invocations_A.irq_handler_invocation \<Rightarrow> bool" where
  "authorised_irq_hdl_inv aag hinv \<equiv>
     case hinv of
         irq_handler_invocation.SetIRQHandler word cap x \<Rightarrow>
                   is_subject aag (fst x) \<and> pas_cap_cur_auth aag cap \<and> is_subject_irq aag word
       | irq_handler_invocation.ClearIRQHandler word     \<Rightarrow> is_subject_irq aag word
       | _                                               \<Rightarrow> True"

lemma emptyable_irq_node:
  "emptyable (interrupt_irq_node s x21, []) s"
  by (simp add:emptyable_def tcb_cnode_index_def)

lemma pas_refined_is_subject_irqD:
  "\<lbrakk> is_subject_irq aag irq; pas_refined aag s \<rbrakk> \<Longrightarrow> is_subject aag (interrupt_irq_node s irq)"
  by (simp add:pas_refined_def irq_map_wellformed_aux_def)


locale Interrupt_AC_1 =
  fixes arch_authorised_irq_ctl_inv :: "'a PAS \<Rightarrow> arch_irq_control_invocation \<Rightarrow> bool"
  assumes arch_invoke_irq_control_pas_refined:
    "\<lbrace>pas_refined (aag :: 'a PAS) and pspace_aligned and valid_vspace_objs and valid_arch_state
                                  and valid_mdb and arch_irq_control_inv_valid irq_ctl_inv
                                  and K (arch_authorised_irq_ctl_inv aag irq_ctl_inv)\<rbrace>
     arch_invoke_irq_control irq_ctl_inv
     \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  and arch_invoke_irq_handler_pas_refined:
    "\<lbrace>pas_refined aag and invs and (\<lambda>s. interrupt_states s x1 \<noteq> IRQInactive)\<rbrace>
     arch_invoke_irq_handler (ACKIrq x1)
     \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  and arch_invoke_irq_control_respects:
    "\<lbrace>integrity aag X st and pas_refined aag and K (arch_authorised_irq_ctl_inv aag acinv)\<rbrace>
     arch_invoke_irq_control acinv
     \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  and arch_invoke_irq_handler_respects:
    "\<lbrace>integrity aag X st and pas_refined aag and einvs\<rbrace>
     arch_invoke_irq_handler (ACKIrq x1)
     \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  and arch_check_irq_inv[wp]:
    "arch_check_irq irq \<lbrace>\<lambda>s :: det_ext state. P s\<rbrace>"
begin

definition authorised_irq_ctl_inv :: "'a PAS \<Rightarrow> Invocations_A.irq_control_invocation \<Rightarrow> bool" where
  "authorised_irq_ctl_inv aag cinv \<equiv>
     case cinv of
       IRQControl irq x1 x2 \<Rightarrow> is_subject aag (fst x1) \<and> is_subject aag (fst x2) \<and>
                               (pasSubject aag, Control, pasIRQAbs aag irq) \<in> pasPolicy aag
     | ArchIRQControl acinv \<Rightarrow> arch_authorised_irq_ctl_inv aag acinv"

lemma invoke_irq_control_pas_refined:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state
                    and valid_mdb and irq_control_inv_valid irq_ctl_inv
                    and K (authorised_irq_ctl_inv aag irq_ctl_inv)\<rbrace>
   invoke_irq_control irq_ctl_inv
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (cases irq_ctl_inv; simp)
  apply (wpsimp wp: cap_insert_pas_refined_not_transferable)
   apply (clarsimp simp: cte_wp_at_caps_of_state clas_no_asid cap_links_irq_def
                         authorised_irq_ctl_inv_def aag_cap_auth_def)
  apply (wp arch_invoke_irq_control_pas_refined)
  apply (clarsimp simp: cte_wp_at_caps_of_state clas_no_asid cap_links_irq_def
                        authorised_irq_ctl_inv_def aag_cap_auth_def)
  done

lemma invoke_irq_handler_pas_refined:
  "\<lbrace>pas_refined (aag :: 'a PAS) and invs and irq_handler_inv_valid irq_inv
                                and K (authorised_irq_hdl_inv aag irq_inv)\<rbrace>
   invoke_irq_handler irq_inv
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases irq_inv, simp_all add: authorised_irq_hdl_inv_def)
    apply (wp arch_invoke_irq_handler_pas_refined)
   apply (wp cap_insert_pas_refined_not_transferable delete_one_caps_of_state
          | strengthen invs_mdb | simp add: cte_wp_at_caps_of_state)+
    apply (rename_tac irq cap slot)
    apply (rule_tac Q =
            "\<lambda> irq_slot. K(irq_slot \<noteq> slot) and invs and emptyable irq_slot
                     and cte_wp_at can_fast_finalise irq_slot
                     and not cte_wp_at is_transferable_cap slot
                     and K(is_subject aag (fst irq_slot))" in hoare_post_imp)
     sorry (* FIXME: broken by touched-addrs -robs
     apply (force simp: cte_wp_at_caps_of_state)
    apply simp
    apply (wp get_irq_slot_different)
   apply (clarsimp simp: emptyable_irq_node cte_wp_at_caps_of_state)
   apply (fastforce simp: interrupt_derived_def is_cap_simps cap_master_cap_def split: cap.splits)
  apply (wp delete_one_caps_of_state | simp add: get_irq_slot_def)+
  apply (fastforce dest: pas_refined_is_subject_irqD)
  done
*)

lemma invoke_irq_control_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and K (authorised_irq_ctl_inv aag irq_ctl_inv)\<rbrace>
   invoke_irq_control irq_ctl_inv
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases irq_ctl_inv)
  subgoal \<comment>\<open>generic case\<close>
    apply (simp add: authorised_irq_ctl_inv_def)
    apply (wp cap_insert_integrity_autarch aag_Control_into_owns_irq | simp | blast)+
    done
  subgoal for arch_irq_ctl_inv \<comment>\<open>arch case\<close>
    apply (wpsimp wp: arch_invoke_irq_control_respects simp: authorised_irq_ctl_inv_def)
    done
  done

lemma invoke_irq_handler_respects:
  "\<lbrace>integrity (aag :: 'a PAS) X st and pas_refined aag and einvs
                                   and K (authorised_irq_hdl_inv aag irq_inv)\<rbrace>
   invoke_irq_handler irq_inv
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (cases irq_inv, simp_all add: authorised_irq_hdl_inv_def)
  by (wpsimp wp: arch_invoke_irq_handler_respects cap_insert_integrity_autarch)+

end


lemma decode_irq_handler_invocation_authorised [wp]:
  "\<lbrace>K (is_subject_irq aag irq \<and> (\<forall>cap_slot \<in> set caps. pas_cap_cur_auth aag (fst cap_slot)
                              \<and> is_subject aag (fst (snd cap_slot))))\<rbrace>
   decode_irq_handler_invocation info_label irq caps
   \<lbrace>\<lambda>x s. authorised_irq_hdl_inv aag x\<rbrace>, -"
  unfolding decode_irq_handler_invocation_def authorised_irq_hdl_inv_def
  apply (rule hoare_pre)
   apply (simp add: Let_def split_def split del: if_split cong: if_cong)
   apply wp
  apply (auto dest!: hd_in_set)
  done


locale Interrupt_AC_2 = Interrupt_AC_1 +
  assumes arch_decode_irq_control_invocation_authorised:
    "\<lbrace>pas_refined aag and
      K (is_subject aag (fst slot) \<and> (\<forall>cap \<in> set caps. pas_cap_cur_auth aag cap) \<and>
         (args \<noteq> [] \<longrightarrow> (pasSubject aag, Control, pasIRQAbs aag (ucast (args ! 0))) \<in> pasPolicy aag))\<rbrace>
     arch_decode_irq_control_invocation info_label args slot caps
     \<lbrace>\<lambda>x s. arch_authorised_irq_ctl_inv aag x\<rbrace>, -"
begin

lemma decode_irq_control_invocation_authorised [wp]:
  "\<lbrace>pas_refined aag and
    K (is_subject aag (fst slot) \<and> (\<forall>cap \<in> set caps. pas_cap_cur_auth aag cap) \<and>
       (args \<noteq> [] \<longrightarrow> (pasSubject aag, Control, pasIRQAbs aag (ucast (args ! 0))) \<in> pasPolicy aag))\<rbrace>
   decode_irq_control_invocation info_label args slot caps
   \<lbrace>\<lambda>x s. authorised_irq_ctl_inv aag x\<rbrace>, -"
  unfolding decode_irq_control_invocation_def authorised_irq_ctl_inv_def
  apply (rule hoare_gen_asmE)
  apply (rule hoare_pre)
   apply (simp add: Let_def split del: if_split cong: if_cong)
   apply (wp arch_decode_irq_control_invocation_authorised
             whenE_throwError_wp hoare_vcg_imp_lift hoare_drop_imps
          | strengthen  aag_Control_owns_strg
          | simp add: o_def del: hoare_True_E_R)+
  apply (cases args, simp_all)
  apply (cases caps, simp_all)
  apply (simp add: ucast_mask_drop)
  apply (auto simp: is_cap_simps cap_auth_conferred_def
                    pas_refined_wellformed
                    pas_refined_all_auth_is_owns aag_cap_auth_def)
  done

end

end
