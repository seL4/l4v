(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterrupt_AI
imports Interrupt_AI
begin

context Arch begin arch_global_naming

primrec arch_irq_control_inv_valid_real ::
  "arch_irq_control_invocation \<Rightarrow> 'a::state_ext state \<Rightarrow> bool"
  where
  "arch_irq_control_inv_valid_real (ARMIRQControlInvocation irq dest_slot src_slot trigger) =
     (cte_wp_at ((=) cap.NullCap) dest_slot and
      cte_wp_at ((=) cap.IRQControlCap) src_slot and
      ex_cte_cap_wp_to is_cnode_cap dest_slot and
      real_cte_at dest_slot and
      K (irq \<le> maxIRQ))"
| "arch_irq_control_inv_valid_real (IssueSGISignal irq target src_slot sgi_slot) =
     (cte_wp_at ((=) cap.NullCap) sgi_slot and
      cte_wp_at ((=) cap.IRQControlCap) src_slot and
      ex_cte_cap_wp_to is_cnode_cap sgi_slot and
      real_cte_at sgi_slot)"

defs arch_irq_control_inv_valid_def:
  "arch_irq_control_inv_valid \<equiv> arch_irq_control_inv_valid_real"

named_theorems Interrupt_AI_assms

lemma (* decode_irq_control_invocation_inv *)[Interrupt_AI_assms]:
  "\<lbrace>P\<rbrace> decode_irq_control_invocation label args slot caps \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decode_irq_control_invocation_def Let_def arch_check_irq_def range_check_def
                   arch_decode_irq_control_invocation_def whenE_def, safe)
  apply (wp | simp)+
  done

lemma decode_irq_control_valid [Interrupt_AI_assms]:
  "\<lbrace>\<lambda>s. invs s \<and> (\<forall>cap \<in> set caps. s \<turnstile> cap)
        \<and> (\<forall>cap \<in> set caps. is_cnode_cap cap \<longrightarrow>
                (\<forall>r \<in> cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s))
        \<and> cte_wp_at ((=) cap.IRQControlCap) slot s\<rbrace>
     decode_irq_control_invocation label args slot caps
   \<lbrace>irq_control_inv_valid\<rbrace>,-"
  unfolding decode_irq_control_invocation_def arch_decode_irq_control_invocation_def
  supply if_split[split del]
  apply (simp add: Let_def split_def whenE_def arch_check_irq_def range_check_def cong: if_cong)
  apply (wpsimp wp: ensure_empty_stronger simp: cte_wp_at_eq_simp arch_irq_control_inv_valid_def
         | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: linorder_not_less word_le_nat_alt unat_ucast mod_le_nat)
  apply (cases caps; clarsimp simp: cte_wp_at_eq_simp)
  apply (fastforce split: if_split)
  done

lemma get_irq_slot_different_ARCH[Interrupt_AI_assms]:
  "\<lbrace>\<lambda>s. valid_global_refs s \<and> ex_cte_cap_wp_to is_cnode_cap ptr s\<rbrace>
      get_irq_slot irq
   \<lbrace>\<lambda>rv s. rv \<noteq> ptr\<rbrace>"
  apply (simp add: get_irq_slot_def)
  apply wp
  apply (clarsimp simp: valid_global_refs_def valid_refs_def
                        ex_cte_cap_wp_to_def)
  apply (elim allE, erule notE, erule cte_wp_at_weakenE)
  apply (clarsimp simp: global_refs_def is_cap_simps cap_range_def)
  done

lemma is_derived_use_interrupt_ARCH[Interrupt_AI_assms]:
  "(is_ntfn_cap cap \<and> interrupt_derived cap cap') \<longrightarrow> (is_derived m p cap cap')"
  apply (clarsimp simp: is_cap_simps)
  apply (clarsimp simp: interrupt_derived_def is_derived_def)
  apply (clarsimp simp: cap_master_cap_def split: cap.split_asm)
  apply (simp add: is_cap_simps is_pt_cap_def vs_cap_ref_def)
  done

lemma maskInterrupt_invs_ARCH[Interrupt_AI_assms]:
  "\<lbrace>invs and (\<lambda>s. \<not>b \<longrightarrow> interrupt_states s irq \<noteq> IRQInactive)\<rbrace>
   do_machine_op (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (rule maskInterrupt_invs)

crunch plic_complete_claim (* FIXME AARCH64: remove plic_complete_claim *)
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"

lemma dmo_plic_complete_claim[wp]: (* FIXME AARCH64: remove plic_complete_claim *)
  "do_machine_op (plic_complete_claim irq) \<lbrace>invs\<rbrace>"
  apply (wp dmo_invs)
  apply (auto simp: plic_complete_claim_def machine_op_lift_def machine_rest_lift_def in_monad select_f_def)
  done

lemma no_cap_to_obj_with_diff_IRQHandler_ARCH[Interrupt_AI_assms]:
  "no_cap_to_obj_with_diff_ref (IRQHandlerCap irq) S = \<top>"
  by (rule ext, simp add: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state
                          obj_ref_none_no_asid)

lemma (* set_irq_state_valid_cap *)[Interrupt_AI_assms]:
  "\<lbrace>valid_cap cap\<rbrace> set_irq_state IRQSignal irq \<lbrace>\<lambda>rv. valid_cap cap\<rbrace>"
  apply (clarsimp simp: set_irq_state_def)
  apply (wp do_machine_op_valid_cap)
  apply (auto simp: valid_cap_def valid_untyped_def
             split: cap.splits option.splits arch_cap.splits
         split del: if_split)
  done

crunch set_irq_state
  for valid_global_refs[Interrupt_AI_assms]: "valid_global_refs"

lemma deactivateInterrupt_invs:
  "\<lbrace>invs and (\<lambda>s. interrupt_states s irq \<noteq> IRQInactive) and K config_ARM_GIC_V3\<rbrace>
   do_machine_op (deactivateInterrupt irq)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding deactivateInterrupt_def
  by (cases config_ARM_GIC_V3; simp)
     (wpsimp wp: maskInterrupt_invs)

lemma invoke_irq_handler_invs'[Interrupt_AI_assms]:
  assumes dmo_ex_inv[wp]: "\<And>f. \<lbrace>invs and ex_inv\<rbrace> do_machine_op f \<lbrace>\<lambda>rv::unit. ex_inv\<rbrace>"
  assumes cap_insert_ex_inv[wp]: "\<And>cap src dest.
  \<lbrace>ex_inv and invs and K (src \<noteq> dest)\<rbrace>
      cap_insert cap src dest
  \<lbrace>\<lambda>_.ex_inv\<rbrace>"
  assumes cap_delete_one_ex_inv[wp]: "\<And>cap.
   \<lbrace>ex_inv and invs\<rbrace> cap_delete_one cap \<lbrace>\<lambda>_.ex_inv\<rbrace>"
 shows
  "\<lbrace>invs and ex_inv and irq_handler_inv_valid i\<rbrace> invoke_irq_handler i \<lbrace>\<lambda>rv s. invs s \<and> ex_inv s\<rbrace>"
 proof -
   have
   cap_insert_invs_ex_invs[wp]: "\<And>cap src dest. \<lbrace>ex_inv and (invs  and cte_wp_at (\<lambda>c. c = NullCap) dest and valid_cap cap and
   tcb_cap_valid cap dest and
   ex_cte_cap_wp_to (appropriate_cte_cap cap) dest and
   (\<lambda>s. \<forall>r\<in>obj_refs cap.
           \<forall>p'. dest \<noteq> p' \<and> cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') p' s \<longrightarrow>
                cte_wp_at (Not \<circ> is_zombie) p' s \<and> \<not> is_zombie cap) and
   (\<lambda>s. cte_wp_at (is_derived (cdt s) src cap) src s) and
   (\<lambda>s. cte_wp_at (\<lambda>cap'. \<forall>irq\<in>cap_irqs cap - cap_irqs cap'. irq_issued irq s)
         src s) and
   (\<lambda>s. \<forall>t R. cap = ReplyCap t False R \<longrightarrow>
            st_tcb_at awaiting_reply t s \<and> \<not> has_reply_cap t s) and
   K (\<not> is_master_reply_cap cap))\<rbrace>
  cap_insert cap src dest \<lbrace>\<lambda>rv s. invs s \<and> ex_inv s\<rbrace>"
   apply wp
   apply (auto simp: cte_wp_at_caps_of_state)
   done
  show ?thesis
  apply (cases i, simp_all)
    apply (rule conjI; wpsimp wp: deactivateInterrupt_invs maskInterrupt_invs)
   apply (rename_tac irq cap prod)
   apply (rule hoare_pre)
    apply (wp valid_cap_typ [OF cap_delete_one_typ_at])
     apply (strengthen real_cte_tcb_valid)
     apply (wp real_cte_at_typ_valid [OF cap_delete_one_typ_at])
     apply (rule_tac Q'="\<lambda>rv s. is_ntfn_cap cap \<and> invs s
                              \<and> cte_wp_at (is_derived (cdt s) prod cap) prod s"
                in hoare_post_imp)
      apply (clarsimp simp: is_cap_simps is_derived_def cte_wp_at_caps_of_state)
      apply (simp split: if_split_asm)
      apply (simp add: cap_master_cap_def split: cap.split_asm)
      apply (drule cte_wp_valid_cap [OF caps_of_state_cteD] | clarsimp)+
      apply (clarsimp simp: cap_master_cap_simps valid_cap_def obj_at_def is_ntfn is_tcb is_cap_table
                     split: option.split_asm dest!:cap_master_cap_eqDs)
     apply (wp cap_delete_one_still_derived)
    apply simp
        apply (wp get_irq_slot_ex_cte get_irq_slot_different_ARCH hoare_drop_imps)
      apply (clarsimp simp: valid_state_def invs_def appropriate_cte_cap_def
                            is_cap_simps)
      apply (erule cte_wp_at_weakenE, simp add: is_derived_use_interrupt_ARCH)
     apply (wp| simp add: )+
  done
qed

lemma safe_parent_for_arch_IRQControl[simp, intro!]:
  "safe_parent_for_arch (ArchObjectCap (SGISignalCap irq target)) IRQControlCap"
  by (simp add: safe_parent_for_arch_def is_cap_simps)

lemma no_cap_to_obj_with_diff_ref_SGISignalCap[simp, intro!]:
  "no_cap_to_obj_with_diff_ref (ArchObjectCap (SGISignalCap irq target)) S s"
  apply (clarsimp simp add: no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state)
  apply (case_tac cap; simp)
  apply (rename_tac acap, case_tac acap; simp)
  done

lemma valid_cap_SGISignalCap[simp, intro!]:
  "s \<turnstile> ArchObjectCap (SGISignalCap irq target)"
  unfolding valid_cap_def
  by (clarsimp simp: cap_aligned_def word_bits_def)

lemma (* invoke_irq_control_invs *) [Interrupt_AI_assms]:
  "\<lbrace>invs and irq_control_inv_valid i\<rbrace> invoke_irq_control i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i; simp)
   apply (wp cap_insert_simple_invs
          | simp add: IRQHandler_valid is_cap_simps  no_cap_to_obj_with_diff_IRQHandler_ARCH
          | strengthen real_cte_tcb_valid)+
   apply (clarsimp simp: cte_wp_at_caps_of_state
                         is_simple_cap_def is_cap_simps is_pt_cap_def
                         safe_parent_for_def is_simple_cap_arch_def
                         ex_cte_cap_to_cnode_always_appropriate_strg)
  apply (rename_tac irq_control, case_tac irq_control; simp add: arch_irq_control_inv_valid_def)
   apply (wp cap_insert_simple_invs
          | simp add: IRQHandler_valid is_cap_simps  no_cap_to_obj_with_diff_IRQHandler_ARCH
          | strengthen real_cte_tcb_valid)+
   apply (clarsimp simp: cte_wp_at_caps_of_state is_simple_cap_def is_simple_cap_arch_def
                         is_cap_simps is_pt_cap_def safe_parent_for_def
                         ex_cte_cap_to_cnode_always_appropriate_strg)
  apply (wpsimp wp: cap_insert_simple_invs
                simp: cte_wp_at_caps_of_state is_simple_cap_def is_simple_cap_arch_def
                      is_cap_simps  safe_parent_for_def is_irq_control_descendant_def
                      ex_cte_cap_to_cnode_always_appropriate_strg tcb_cap_valid_def obj_at_def
                      is_tcb is_cap_table)
  done


crunch resetTimer
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"

lemma resetTimer_invs_ARCH[Interrupt_AI_assms]:
  "\<lbrace>invs\<rbrace> do_machine_op resetTimer \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="%_ b. underlying_memory b p = underlying_memory m p"
                 in use_valid)
     apply (simp add: resetTimer_def
                      machine_op_lift_def machine_rest_lift_def split_def)
     apply wp
    apply (clarsimp+)[2]
  apply(erule use_valid, wp no_irq_resetTimer no_irq, assumption)
  done

lemma empty_fail_ackInterrupt_ARCH[Interrupt_AI_assms]:
  "empty_fail (ackInterrupt irq)"
  by (wp | simp add: ackInterrupt_def)+

lemma empty_fail_maskInterrupt_ARCH[Interrupt_AI_assms]:
  "empty_fail (maskInterrupt f irq)"
  by (wp | simp add: maskInterrupt_def)+

lemma dmo_st_tcb_cur[wp]:
  "\<lbrace>\<lambda>s. st_tcb_at P (cur_thread s) s\<rbrace> do_machine_op f \<lbrace>\<lambda>rv s. st_tcb_at P (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wp)

lemma dmo_ex_nonz_cap_to[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> do_machine_op f \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  by (rule hoare_lift_Pf[where f=cur_thread]; wp)

lemma conj_imp_strg:
  "P \<Longrightarrow> (A \<longrightarrow> P) \<and> (B \<longrightarrow> P)" by simp

lemma runnable_eq:
  "runnable st = (st = Running \<or> st = Restart)"
  by (cases st; simp)

lemma halted_eq:
  "halted st = (st = Inactive \<or> st = IdleThreadState)"
  by (cases st; simp)

crunch vgic_update, vgic_update_lr, vcpu_update for ex_nonz_cap_to[wp]: "ex_nonz_cap_to p"
  (wp: ex_nonz_cap_to_pres)

lemma vgic_maintenance_invs[wp]:
  "\<lbrace>invs\<rbrace> vgic_maintenance \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding vgic_maintenance_def
  supply if_split[split del] valid_fault_def[simp]
  apply (wpsimp simp: get_gic_vcpu_ctrl_misr_def get_gic_vcpu_ctrl_eisr1_def
                      get_gic_vcpu_ctrl_eisr0_def if_apply_def2
                 wp: thread_get_wp' hoare_vcg_imp_lift' gts_wp hoare_vcg_all_lift
         | wps
         | wp (once) hoare_drop_imp[where f="do_machine_op m" for m]
                   hoare_drop_imp[where f="return $ m" for m]
         | strengthen not_pred_tcb_at_strengthen
         | wp (once) hoare_vcg_imp_lift' gts_wp)+
  apply (frule tcb_at_invs)
  apply (clarsimp simp: runnable_eq halted_eq not_pred_tcb)
  apply (fastforce intro!: st_tcb_ex_cap[where P=active]
                   simp: not_pred_tcb st_tcb_at_def obj_at_def halted_eq)
  done

lemma vppi_event_invs[wp]:
  "\<lbrace>invs\<rbrace> vppi_event irq \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding vppi_event_def
  supply if_split[split del] valid_fault_def[simp]
  apply (wpsimp simp: if_apply_def2
                wp: hoare_vcg_imp_lift' gts_wp hoare_vcg_all_lift maskInterrupt_invs
                cong: vcpu.fold_congs
         | wps
         | strengthen not_pred_tcb_at_strengthen)+
  apply (frule tcb_at_invs)
  apply (clarsimp simp: runnable_eq halted_eq not_pred_tcb)
  apply (fastforce intro!: st_tcb_ex_cap[where P=active]
                   simp: not_pred_tcb st_tcb_at_def obj_at_def halted_eq)
  done

lemma handle_reserved_irq_invs[wp]:
  "\<lbrace>invs\<rbrace> handle_reserved_irq irq \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding handle_reserved_irq_def by (wpsimp simp: non_kernel_IRQs_def)

crunch timer_tick
  for invs[wp]: invs
  (wp: thread_set_invs_trivial[OF ball_tcb_cap_casesI])

lemma (* handle_interrupt_invs *) [Interrupt_AI_assms]:
  "\<lbrace>invs\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: handle_interrupt_def)
  apply (rule conjI; rule impI)
  apply (simp add: do_machine_op_bind empty_fail_ackInterrupt_ARCH empty_fail_maskInterrupt_ARCH)
     apply (wpsimp wp: dmo_maskInterrupt_invs maskInterrupt_invs_ARCH dmo_ackInterrupt
                      send_signal_interrupt_states simp: arch_mask_irq_signal_def)+
     apply (wp get_cap_wp send_signal_interrupt_states )
    apply (rule_tac Q'="\<lambda>rv. invs and (\<lambda>s. st = interrupt_states s irq)" in hoare_post_imp)
     apply (clarsimp simp: ex_nonz_cap_to_def invs_valid_objs)
     apply (intro allI exI, erule cte_wp_at_weakenE)
     apply (clarsimp simp: is_cap_simps)
    apply (wpsimp wp: hoare_drop_imps resetTimer_invs_ARCH
                simp: get_irq_state_def
           | rule conjI)+
 done

lemma sts_arch_irq_control_inv_valid[wp, Interrupt_AI_assms]:
  "\<lbrace>arch_irq_control_inv_valid i\<rbrace>
       set_thread_state t st
   \<lbrace>\<lambda>rv. arch_irq_control_inv_valid i\<rbrace>"
  unfolding arch_irq_control_inv_valid_def
  by (cases i; wpsimp wp: ex_cte_cap_to_pres simp: cap_table_at_typ)

crunch arch_invoke_irq_handler
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"

end

interpretation Interrupt_AI?: Interrupt_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, simp_all add: Interrupt_AI_assms)?)
  qed

end
