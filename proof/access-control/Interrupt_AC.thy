(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Interrupt_AC
imports
  Finalise_AC
begin

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  arch_authorised_irq_ctl_inv :: "'a PAS \<Rightarrow> Invocations_A.arch_irq_control_invocation \<Rightarrow> bool"
where
  "arch_authorised_irq_ctl_inv aag cinv \<equiv>
     case cinv of
         (ArchIRQControlIssue irq x1 x2 trigger) \<Rightarrow>
                                 is_subject aag (fst x1) \<and> is_subject aag (fst x2) \<and>
                                 (pasSubject aag, Control, pasIRQAbs aag irq) \<in> pasPolicy aag"

definition
  authorised_irq_ctl_inv :: "'a PAS \<Rightarrow> Invocations_A.irq_control_invocation \<Rightarrow> bool"
where
  "authorised_irq_ctl_inv aag cinv \<equiv>
     case cinv of
         IRQControl irq x1 x2 \<Rightarrow> is_subject aag (fst x1) \<and> is_subject aag (fst x2) \<and>
                                  (pasSubject aag, Control, pasIRQAbs aag irq) \<in> pasPolicy aag
        | ArchIRQControl acinv \<Rightarrow> arch_authorised_irq_ctl_inv aag acinv"

lemma arch_invoke_irq_control_pas_refined:
  "\<lbrace>pas_refined aag and valid_mdb and arch_irq_control_inv_valid irq_ctl_inv and
     K (arch_authorised_irq_ctl_inv aag irq_ctl_inv)\<rbrace>
     arch_invoke_irq_control irq_ctl_inv
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (cases irq_ctl_inv; simp)
  apply (wpsimp wp: cap_insert_pas_refined_not_transferable)
  apply (clarsimp simp: cte_wp_at_caps_of_state clas_no_asid cap_links_irq_def
                        arch_authorised_irq_ctl_inv_def aag_cap_auth_def
                        arch_irq_control_inv_valid_def)
  done

lemma invoke_irq_control_pas_refined:
  "\<lbrace>pas_refined aag and valid_mdb and irq_control_inv_valid irq_ctl_inv
      and K (authorised_irq_ctl_inv aag irq_ctl_inv)\<rbrace>
     invoke_irq_control irq_ctl_inv
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (cases irq_ctl_inv; simp)
  apply (wpsimp wp: cap_insert_pas_refined_not_transferable)
   apply (clarsimp simp: cte_wp_at_caps_of_state clas_no_asid cap_links_irq_def
                         authorised_irq_ctl_inv_def aag_cap_auth_def)
  apply (wp arch_invoke_irq_control_pas_refined)
  apply (clarsimp simp: cte_wp_at_caps_of_state clas_no_asid cap_links_irq_def
                        authorised_irq_ctl_inv_def aag_cap_auth_def)
  done

definition
  authorised_irq_hdl_inv :: "'a PAS \<Rightarrow> Invocations_A.irq_handler_invocation \<Rightarrow> bool"
where
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
  "\<lbrakk>is_subject_irq aag irq ; pas_refined aag s \<rbrakk> \<Longrightarrow> is_subject aag (interrupt_irq_node s irq)"
  by (simp add:pas_refined_def irq_map_wellformed_aux_def)

lemma invoke_irq_handler_pas_refined:
  "\<lbrace>pas_refined aag and invs and irq_handler_inv_valid irq_inv
       and K (authorised_irq_hdl_inv aag irq_inv)\<rbrace>
     invoke_irq_handler irq_inv
   \<lbrace>\<lambda>rv (s::det_ext state). pas_refined aag s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases irq_inv, simp_all add: authorised_irq_hdl_inv_def)
    apply (wp cap_insert_pas_refined_not_transferable delete_one_caps_of_state
          | strengthen invs_mdb aag_Control_owns_strg
          | simp add: pas_refined_wellformed cte_wp_at_caps_of_state)+
    apply (rename_tac irq cap slot)
    apply (rule_tac Q =
            "\<lambda> irq_slot. K(irq_slot \<noteq> slot) and invs and emptyable irq_slot
                     and cte_wp_at can_fast_finalise irq_slot
                     and not cte_wp_at is_transferable_cap slot
                     and K(is_subject aag (fst irq_slot))" in hoare_post_imp)
     apply (force simp: cte_wp_at_caps_of_state)
    apply simp
    apply (wp get_irq_slot_different)

   apply (clarsimp simp: emptyable_irq_node cte_wp_at_caps_of_state)
   apply (fastforce simp: interrupt_derived_def is_cap_simps cap_master_cap_def split: cap.splits)
  apply (wp delete_one_caps_of_state | simp add: get_irq_slot_def)+
  apply (fastforce dest: pas_refined_is_subject_irqD)
  done


lemma invoke_irq_control_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and K (authorised_irq_ctl_inv aag irq_ctl_inv)\<rbrace>
     invoke_irq_control irq_ctl_inv
   \<lbrace>\<lambda>y. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases irq_ctl_inv)
  subgoal \<comment>\<open>generic case\<close>
    apply (simp add: authorised_irq_ctl_inv_def)
    apply (wp cap_insert_integrity_autarch aag_Control_into_owns_irq | simp | blast)+
    done
  subgoal for arch_irq_ctl_inv \<comment>\<open>arch case\<close>
    apply (simp add: arch_authorised_irq_ctl_inv_def authorised_irq_ctl_inv_def)
    apply (case_tac arch_irq_ctl_inv, clarsimp simp add: setIRQTrigger_def)
    apply (wp cap_insert_integrity_autarch aag_Control_into_owns_irq dmo_mol_respects do_machine_op_pas_refined | simp)+
    apply auto
    done
  done

lemma integrity_irq_masks [iff]:
  "integrity aag X st (s\<lparr>machine_state := machine_state s \<lparr>irq_masks := v \<rparr>\<rparr>) = integrity aag X st s"
  unfolding integrity_def
  by simp

lemma invoke_irq_handler_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs and
       K (authorised_irq_hdl_inv aag irq_inv)\<rbrace>
     invoke_irq_handler irq_inv
   \<lbrace>\<lambda>y. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases irq_inv, simp_all add: authorised_irq_hdl_inv_def)
  apply (rule hoare_pre)
  apply (wp cap_insert_integrity_autarch get_irq_slot_owns dmo_wp | simp add: maskInterrupt_def )+
  done

lemma decode_irq_control_invocation_authorised [wp]:
  "\<lbrace>pas_refined aag
      and K (is_subject aag (fst slot)
              \<and> (\<forall>cap \<in> set caps. pas_cap_cur_auth aag cap)
              \<and> (args \<noteq> [] \<longrightarrow>
                  (pasSubject aag, Control, pasIRQAbs aag (ucast (args ! 0))) \<in> pasPolicy aag))\<rbrace>
    decode_irq_control_invocation info_label args slot caps
  \<lbrace>\<lambda>x s. authorised_irq_ctl_inv aag x\<rbrace>, -"
  unfolding decode_irq_control_invocation_def arch_decode_irq_control_invocation_def authorised_irq_ctl_inv_def arch_authorised_irq_ctl_inv_def arch_check_irq_def
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
  "\<lbrace>K (is_subject_irq aag irq
         \<and> (\<forall>cap_slot \<in> set caps. pas_cap_cur_auth aag (fst cap_slot)
                                \<and> is_subject aag (fst (snd cap_slot))))\<rbrace>
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
