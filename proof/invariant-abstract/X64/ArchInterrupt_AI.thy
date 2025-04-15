(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterrupt_AI
imports Interrupt_AI
begin

context Arch begin arch_global_naming

primrec arch_irq_control_inv_valid_real :: "arch_irq_control_invocation \<Rightarrow> 'a::state_ext state \<Rightarrow> bool"
where
  "arch_irq_control_inv_valid_real (IssueIRQHandlerIOAPIC irq dest_slot src_slot
                    ioapic pin level polarity vector) =
                    (cte_wp_at ((=) NullCap) dest_slot and
                    cte_wp_at ((=) IRQControlCap) src_slot and
                    ex_cte_cap_wp_to is_cnode_cap dest_slot and
                    real_cte_at dest_slot and
                    (\<lambda>s. ioapic < x64_num_ioapics (arch_state s)) and
                    K (minUserIRQ \<le> irq \<and> irq \<le> maxUserIRQ \<and>
                       level < 2 \<and> polarity < 2))"
| "arch_irq_control_inv_valid_real (IssueIRQHandlerMSI irq dest_slot src_slot bus dev func handle)
      = (cte_wp_at ((=) NullCap) dest_slot and
                    cte_wp_at ((=) IRQControlCap) src_slot and
                    ex_cte_cap_wp_to is_cnode_cap dest_slot and
                    real_cte_at dest_slot and
                    K (minUserIRQ \<le> irq \<and> irq \<le> maxUserIRQ \<and>
                       bus \<le> maxPCIBus \<and> dev \<le> maxPCIDev \<and> func \<le> maxPCIFunc))"

defs arch_irq_control_inv_valid_def:
  "arch_irq_control_inv_valid \<equiv> arch_irq_control_inv_valid_real"

named_theorems Interrupt_AI_assms

lemma (* decode_irq_control_invocation_inv *)[Interrupt_AI_assms]:
  "\<lbrace>P\<rbrace> decode_irq_control_invocation label args slot caps \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decode_irq_control_invocation_def Let_def arch_check_irq_def
                   arch_decode_irq_control_invocation_def whenE_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp | simp split del: if_split)+
  done

lemma irq_control_inv_valid_ArchIRQControl[simp]:
  "irq_control_inv_valid \<circ> ArchIRQControl = arch_irq_control_inv_valid"
  by auto

context begin

private method cap_hammer = (((drule_tac x="caps ! 0" in bspec)+, (rule nth_mem, fastforce)+),
                        solves \<open>(clarsimp simp: cte_wp_at_eq_simp)\<close>)

private method word_hammer = solves \<open>(clarsimp simp: not_less maxIRQ_def ioapicIRQLines_def
                                    maxPCIDev_def maxPCIBus_def maxPCIFunc_def,
                                    auto?)[1]\<close>

lemma irq_plus_min_ge_min:
  "irq \<le> maxUserIRQ - minUserIRQ \<Longrightarrow>
   minUserIRQ \<le> irq + minUserIRQ"
  apply (clarsimp simp: minUserIRQ_def maxUserIRQ_def)
  apply (subst add.commute)
  apply (rule no_olen_add_nat[THEN iffD2])
  apply (clarsimp simp: unat_ucast word_le_nat_alt)
  done

lemma irq_plus_min_le_max:
  "irq \<le> maxUserIRQ - minUserIRQ \<Longrightarrow>
   irq + minUserIRQ \<le> maxUserIRQ"
  apply (clarsimp simp: minUserIRQ_def maxUserIRQ_def)
  apply (subst add.commute)
  apply (clarsimp simp: Word.le_plus)
  done

private lemma irq_ineq_one:
  "x \<le> 0x6B \<Longrightarrow> 0x10 \<le> UCAST(64 \<rightarrow> 8) x + 0x10"
  by (word_bitwise, clarsimp)

private lemma irq_ineq_two:
  "x \<le> 0x6B \<Longrightarrow> UCAST(64 \<rightarrow> 8) x + 0x10 \<le> 0x7B"
  apply (subgoal_tac "UCAST(64 \<rightarrow> 8) x \<le> 0x6B")
   defer
   apply (erule ucast_mono_le'[where y="0x6B" and 'a=64 and 'b=8,simplified])
  apply (thin_tac "x \<le> 0x6B")
  apply (subst add.commute)
  apply (rule le_plus)
  apply simp+
  done

private lemma irq_ineq_three:
  "(x :: 8 word) \<le> 0x6B \<Longrightarrow> x + 0x10 \<le> 0x7B"
  apply (subst add.commute)
  apply (rule le_plus)
  apply simp+
  done

private lemma irq_ineq_four:
  "(x :: 8 word) \<le> 0x6B \<Longrightarrow> 0x10 \<le> x + 0x10"
  apply (subst word_le_nat_alt)
  apply (subst unat_add_lem')
   apply (subst (asm) word_le_nat_alt)
   apply simp
  apply simp
  done

lemma arch_decode_irq_control_valid[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> (\<forall>cap \<in> set caps. s \<turnstile> cap)
        \<and> (\<forall>cap \<in> set caps. is_cnode_cap cap \<longrightarrow>
                (\<forall>r \<in> cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s))
        \<and> cte_wp_at ((=) cap.IRQControlCap) slot s\<rbrace>
     arch_decode_irq_control_invocation label args slot caps
   \<lbrace>arch_irq_control_inv_valid\<rbrace>,-"
  apply (simp add: arch_decode_irq_control_invocation_def Let_def whenE_def
                   arch_irq_control_inv_valid_def
        split del: if_split
             cong: if_cong)
  apply (rule hoare_pre)
   apply (wp ensure_empty_stronger hoare_vcg_const_imp_liftE_R hoare_vcg_const_imp_lift
          | simp add: cte_wp_at_eq_simp split del: if_split
          | wpc
          | wp hoare_vcg_imp_liftE_R[where P="\<lambda>rv s. \<not> x64_num_ioapics (arch_state s) - 1 < args ! 2"]
          | wp hoare_vcg_imp_liftE_R[where P="\<lambda>rv s. x64_num_ioapics (arch_state s) \<noteq> 0"]
          | wp (once) hoare_drop_imps)+
  apply ( safe; auto simp: word_le_not_less[symmetric] word_leq_minus_one_le
                           irq_plus_min_ge_min irq_plus_min_le_max ioapicIRQLines_def
                           minUserIRQ_def maxUserIRQ_def word_add_le_mono1 word_add_le_mono2
                           word_le_plus irq_ineq_one irq_ineq_two irq_ineq_three irq_ineq_four
        | cap_hammer | word_hammer)+
  done
end

lemma (* decode_irq_control_valid *)[Interrupt_AI_assms]:
  "\<lbrace>\<lambda>s. invs s \<and> (\<forall>cap \<in> set caps. s \<turnstile> cap)
        \<and> (\<forall>cap \<in> set caps. is_cnode_cap cap \<longrightarrow>
                (\<forall>r \<in> cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s))
        \<and> cte_wp_at ((=) cap.IRQControlCap) slot s\<rbrace>
     decode_irq_control_invocation label args slot caps
   \<lbrace>irq_control_inv_valid\<rbrace>,-"
  apply (simp add: decode_irq_control_invocation_def Let_def split_def
                   whenE_def arch_check_irq_def
                 split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply (wp ensure_empty_stronger | simp add: cte_wp_at_eq_simp
                 | wp (once) hoare_drop_imps)+
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
   apply (simp add: do_machine_op_def split_def maskInterrupt_def)
   apply wp
   apply (clarsimp simp: in_monad invs_def valid_state_def all_invs_but_valid_irq_states_for_def
     valid_irq_states_but_def valid_irq_masks_but_def valid_machine_state_def cur_tcb_def valid_irq_states_def valid_irq_masks_def)
  done

lemma no_cap_to_obj_with_diff_IRQHandler_ARCH[Interrupt_AI_assms]:
  "no_cap_to_obj_with_diff_ref (IRQHandlerCap irq) S = \<top>"
  by (rule ext, simp add: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state
                          obj_ref_none_no_asid)

crunch do_machine_op
  for valid_cap: "valid_cap cap"

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

crunch arch_invoke_irq_handler
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"

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
   apply (wp maskInterrupt_invs_ARCH)
    apply simp
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

crunch ioapicMapPinToVector
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"

lemma update_irq_state_invs[wp]:
  "\<lbrace>invs and K (irq \<le> maxIRQ)\<rbrace>
   update_irq_state irq state
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: update_irq_state_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_global_refs_def
                        global_refs_def valid_arch_state_def valid_vspace_objs_def
                        valid_arch_caps_def valid_vs_lookup_def vs_lookup_def vs_lookup_pages_def
                        vs_lookup_pages1_def valid_table_caps_def empty_table_def second_level_tables_def
                        valid_global_objs_def valid_kernel_mappings_def valid_asid_map_def
                        valid_x64_irq_state_def valid_ioports_def all_ioports_issued_def
                        issued_ioports_def word_not_le[symmetric])
  done

lemma no_irq_ioapicMapPinToVector: "no_irq (ioapicMapPinToVector a b c d e)"
  by (wp no_irq | clarsimp simp: no_irq_def ioapicMapPinToVector_def)+

lemmas ioapicMapPinToVector_irq_masks = no_irq[OF no_irq_ioapicMapPinToVector]

lemma dmo_ioapicMapPinToVector[wp]: "\<lbrace>invs\<rbrace> do_machine_op (ioapicMapPinToVector irq b c d e) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: ioapicMapPinToVector_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ ioapicMapPinToVector_irq_masks])
  done

crunch update_irq_state
  for real_cte_at[wp]: "real_cte_at x"
  and cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at Q slot s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and ex_cte_cap_wp_to[wp]: "ex_cte_cap_wp_to a b"
  and valid_objs[wp]: "valid_objs"
  and pspace_distinct[wp]: "pspace_distinct"
  and pspace_aligned[wp]: "pspace_aligned"
  and valid_mdb[wp]: "valid_mdb"
  and kheap[wp]: "\<lambda>s. P (kheap s)"
  (simp: ex_cte_cap_wp_to_def)

lemma arch_invoke_irq_control_invs[wp]:
  "\<lbrace>invs and arch_irq_control_inv_valid i\<rbrace> arch_invoke_irq_control i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: arch_invoke_irq_control_def)
  apply (rule hoare_pre)
   apply (wp cap_insert_simple_invs | wpc
         | simp add: IRQHandler_valid is_cap_simps no_cap_to_obj_with_diff_IRQHandler_ARCH
                     is_cap_simps safe_ioport_insert_triv
         | strengthen real_cte_tcb_valid
         | wps)+
  by (auto simp: cte_wp_at_caps_of_state IRQ_def arch_irq_control_inv_valid_def
                        is_simple_cap_def is_cap_simps is_pt_cap_def
                        safe_parent_for_def
                        maxUserIRQ_def maxIRQ_def order.trans
                        ex_cte_cap_to_cnode_always_appropriate_strg)

lemma (* invoke_irq_control_invs *) [Interrupt_AI_assms]:
  "\<lbrace>invs and irq_control_inv_valid i\<rbrace> invoke_irq_control i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i, simp_all)
  apply (rule hoare_pre)
   apply (wp cap_insert_simple_invs
             | simp add: IRQHandler_valid is_cap_simps  no_cap_to_obj_with_diff_IRQHandler_ARCH
                         is_cap_simps safe_ioport_insert_triv
             | strengthen real_cte_tcb_valid)+
   apply (clarsimp simp: cte_wp_at_caps_of_state
                         is_simple_cap_def is_cap_simps is_pt_cap_def
                         safe_parent_for_def
                         ex_cte_cap_to_cnode_always_appropriate_strg)
  by wp

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

crunch timer_tick
  for invs[wp]: invs
  (wp: thread_set_invs_trivial[OF ball_tcb_cap_casesI])

crunch timer_tick
  for invs[wp]: invs
  (wp: thread_set_invs_trivial[OF ball_tcb_cap_casesI])

lemma (* handle_interrupt_invs *) [Interrupt_AI_assms]:
  "\<lbrace>invs\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: handle_interrupt_def  )
  apply (rule conjI; rule impI)
  apply (simp add: do_machine_op_bind empty_fail_ackInterrupt_ARCH empty_fail_maskInterrupt_ARCH)
     apply (wp dmo_maskInterrupt_invs maskInterrupt_invs_ARCH dmo_ackInterrupt
            | wpc | simp add: arch_mask_irq_signal_def)+
     apply (wp get_cap_wp send_signal_interrupt_states)
    apply (rule_tac Q'="\<lambda>rv. invs and (\<lambda>s. st = interrupt_states s irq)" in hoare_post_imp)
     apply (clarsimp simp: ex_nonz_cap_to_def invs_valid_objs)
     apply (intro allI exI, erule cte_wp_at_weakenE)
     apply (clarsimp simp: is_cap_simps)
    apply (wp hoare_drop_imps resetTimer_invs_ARCH | simp add: get_irq_state_def handle_reserved_irq_def)+
 done

lemma sts_arch_irq_control_inv_valid[wp, Interrupt_AI_assms]:
  "\<lbrace>arch_irq_control_inv_valid i\<rbrace>
       set_thread_state t st
   \<lbrace>\<lambda>rv. arch_irq_control_inv_valid i\<rbrace>"
  apply (simp add: arch_irq_control_inv_valid_def)
  apply (cases i)
   apply (clarsimp)
   apply (wp ex_cte_cap_to_pres | simp add: cap_table_at_typ)+
  done

crunch arch_invoke_irq_handler
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"

end



interpretation Interrupt_AI?: Interrupt_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, simp_all add: Interrupt_AI_assms)?)
  qed

end
