(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
Refinement for interrupt controller operations
*)

theory Interrupt_AI
imports Ipc_AI
begin

definition
  interrupt_derived :: "cap \<Rightarrow> cap \<Rightarrow> bool"
where
 "interrupt_derived cap cap' \<equiv> \<not> is_untyped_cap cap \<longrightarrow> cap_master_cap cap = cap_master_cap cap'
                                    \<and> (cap_badge cap', cap_badge cap) \<in> capBadge_ordering False"

primrec
  irq_handler_inv_valid :: "irq_handler_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "irq_handler_inv_valid (ACKIrq irq) = (\<lambda>s. interrupt_states s irq \<noteq> IRQInactive)"
| "irq_handler_inv_valid (Invocations_A.ClearIRQHandler irq) = \<top>"
| "irq_handler_inv_valid (Invocations_A.SetIRQHandler irq cap cte_ptr)
     = (\<lambda>s. ex_cte_cap_wp_to (is_cnode_cap) cte_ptr s
            \<and> (\<exists>ptr'. cte_wp_at (op = (cap.IRQHandlerCap irq)) ptr' s)
            \<and> cte_wp_at (interrupt_derived cap) cte_ptr s
            \<and> s \<turnstile> cap \<and> is_aep_cap cap)"
| "irq_handler_inv_valid (Invocations_A.SetMode irq trig pol) = \<top>"

primrec
  irq_control_inv_valid :: "irq_control_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "irq_control_inv_valid (Invocations_A.InterruptControl ivk) = \<bottom>"
| "irq_control_inv_valid (Invocations_A.IRQControl irq ptr ptr') =
       (cte_wp_at (op = cap.NullCap) ptr and
        cte_wp_at (op = cap.IRQControlCap) ptr'
        and ex_cte_cap_wp_to is_cnode_cap ptr and real_cte_at ptr
        and K (irq \<le> maxIRQ))"

crunch inv[wp]: decode_irq_handler_invocation "P"
  (simp: crunch_simps)

lemma valid_irq_handlersD:
  "\<lbrakk>cte_wp_at (op = (IRQHandlerCap irq)) (a, b) s; valid_irq_handlers s\<rbrakk>  \<Longrightarrow>
  interrupt_states s irq = IRQNotifyAEP"
  apply(auto simp: valid_irq_handlers_def cte_wp_at_caps_of_state irq_issued_def cap_irqs_def cap_irq_opt_def split: cap.splits)
  done

lemma decode_irq_handler_valid[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> (\<forall>cap \<in> set caps. s \<turnstile> fst cap) \<and> (\<exists>ptr'. cte_wp_at (op = (cap.IRQHandlerCap irq)) ptr' s)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs (fst cap) (interrupt_irq_node s). ex_cte_cap_to r s)
        \<and> (\<forall>cap \<in> set caps. ex_cte_cap_wp_to is_cnode_cap (snd cap) s)
        \<and> (\<forall>cap \<in> set caps. cte_wp_at (interrupt_derived (fst cap)) (snd cap) s)\<rbrace>
     decode_irq_handler_invocation label args irq caps
   \<lbrace>irq_handler_inv_valid\<rbrace>,-"
  apply (simp add: decode_irq_handler_invocation_def Let_def split_def
                  split del: split_if cong: if_cong)
  apply (rule hoare_pre, wp)
  apply (clarsimp simp: neq_Nil_conv)
  apply (fastforce dest: valid_irq_handlersD simp: invs_def valid_state_def)
  done

crunch inv[wp]: is_irq_active "P"

lemma decode_irq_control_invocation_inv[wp]:
  "\<lbrace>P\<rbrace> decode_irq_control_invocation label args slot caps \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decode_irq_control_invocation_def Let_def
                   arch_decode_interrupt_control_def whenE_def, safe)
  apply (wp | simp)+
  done

lemma decode_irq_control_valid[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> (\<forall>cap \<in> set caps. s \<turnstile> cap)
        \<and> (\<forall>cap \<in> set caps. is_cnode_cap cap \<longrightarrow>
                (\<forall>r \<in> cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s))
        \<and> cte_wp_at (op = cap.IRQControlCap) slot s\<rbrace>
     decode_irq_control_invocation label args slot caps
   \<lbrace>irq_control_inv_valid\<rbrace>,-"
  apply (simp add: decode_irq_control_invocation_def Let_def split_def
                   lookup_target_slot_def whenE_def
                   arch_decode_interrupt_control_def
                 split del: split_if cong: if_cong)
  apply (rule hoare_pre)
   apply (wp ensure_empty_stronger | simp add: cte_wp_at_eq_simp
                 | wp_once hoare_drop_imps)+
  apply (clarsimp simp: linorder_not_less word_le_nat_alt unat_ucast
                        maxIRQ_def)
  apply (cases caps, auto)
  done


lemma get_irq_slot_different:
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


lemma is_up_8_32: "is_up (ucast :: word8 \<Rightarrow> word32)"
  by (simp add: is_up_def source_size_def target_size_def word_size)


crunch mdb_inv[wp]: ep_cancel_all "\<lambda>s. P (cdt s)"
  (wp: fast_finalise_lift crunch_wps)

crunch mdb_inv[wp]: aep_cancel_all "\<lambda>s. P (cdt s)"
  (wp: fast_finalise_lift crunch_wps)

crunch mdb_inv[wp]: fast_finalise "\<lambda>s. P (cdt s)"
  (wp: fast_finalise_lift crunch_wps)

crunch mdb_inv[wp]: set_cap "\<lambda>s. P (cdt s)"
  (wp: crunch_wps simp: crunch_simps)

lemma cap_delete_one_still_derived:
  "\<lbrace>\<lambda>s. cte_wp_at (is_derived (cdt s) p' cap) p' s \<and> p \<noteq> p' \<and> valid_mdb s\<rbrace>
     cap_delete_one p
   \<lbrace>\<lambda>rv s. cte_wp_at (is_derived (cdt s) p' cap) p' s\<rbrace>"
  apply (simp add: cap_delete_one_def empty_slot_def unless_def
                   cte_wp_at_caps_of_state set_cdt_def)
  apply (wp hoare_vcg_ex_lift)
  apply (simp split del:split_if)
  apply (wp hoare_vcg_ex_lift get_cap_wp hoare_vcg_all_lift
            hoare_vcg_disj_lift
               | simp only: cte_wp_at_caps_of_state imp_conv_disj
                            cdt_update.caps_of_state_update
                            revokable_update.caps_of_state_update
               | simp)+
     apply (simp add: is_final_cap_def | wp)+
   apply (rule get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state if_apply_def2
             split del: split_if)
  apply (rule_tac x=capa in exI)
  apply (clarsimp simp only: is_derived_def simp_thms
                      split: split_if_asm)
   apply clarsimp
   apply (subst mdb_empty_abs.descendants[unfolded fun_upd_def])
    apply (rule mdb_empty_abs.intro)
    apply (rule vmdb_abs.intro)
    apply simp
   apply simp
  apply auto
  done


lemma real_cte_emptyable_strg:
  "real_cte_at p s \<longrightarrow> emptyable p s"
  by (clarsimp simp: emptyable_def obj_at_def is_tcb is_cap_table)


lemma is_derived_use_interrupt:
  "(is_aep_cap cap \<and> interrupt_derived cap cap') \<longrightarrow> (is_derived m p cap cap')"
  apply (clarsimp simp: is_cap_simps)
  apply (clarsimp simp: interrupt_derived_def is_derived_def)
  apply (clarsimp simp: cap_master_cap_def split: cap.split_asm)
  apply (simp add: is_cap_simps is_pt_cap_def vs_cap_ref_def)
  done


lemma cap_delete_one_cte_cap_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to P ptr\<rbrace> cap_delete_one ptr' \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P ptr\<rbrace>"
  apply (simp add: ex_cte_cap_wp_to_def)
  apply (wp hoare_vcg_ex_lift
            hoare_use_eq_irq_node [OF cap_delete_one_irq_node
                                      cap_delete_one_cte_wp_at_preserved])
  apply (clarsimp simp: can_fast_finalise_def split: cap.split_asm)
  done


lemma get_irq_slot_ex_cte:
  "\<lbrace>\<lambda>s. \<exists>ptr. cte_wp_at (op = (cap.IRQHandlerCap irq)) ptr s \<and> P (cap.IRQHandlerCap irq)\<rbrace>
      get_irq_slot irq
   \<lbrace>ex_cte_cap_wp_to P\<rbrace>"
  apply (simp add: get_irq_slot_def)
  apply wp
  apply (simp add: ex_cte_cap_wp_to_def)
  apply (elim conjE exEI cte_wp_at_weakenE)
  apply clarsimp
  done

lemma maskInterrupt_invs:
  "\<lbrace>invs and (\<lambda>s. interrupt_states s irq \<noteq> IRQInactive)\<rbrace> 
   do_machine_op (maskInterrupt b irq) 
   \<lbrace>\<lambda>rv. invs\<rbrace>"
   apply (simp add: do_machine_op_def split_def maskInterrupt_def)
   apply wp
   apply (clarsimp simp: in_monad invs_def valid_state_def all_invs_but_valid_irq_states_for_def valid_irq_states_but_def valid_irq_masks_but_def valid_machine_state_def cur_tcb_def valid_irq_states_def valid_irq_masks_def)
  done

crunch pspace_aligned[wp]: set_irq_state "pspace_aligned"

crunch pspace_distinct[wp]: set_irq_state "pspace_distinct"

lemma valid_mdb_interrupts[simp]:
  "valid_mdb (interrupt_states_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def mdb_cte_at_def)

crunch valid_mdb[wp]: set_irq_state "valid_mdb"

crunch mdb_cte_wp_at[wp]: set_irq_state "\<lambda>s. cte_wp_at (P (cdt s)) p s"
crunch real_cte_at[wp]: set_irq_state "real_cte_at p"

lemmas set_irq_state_cte_cap_to[wp]
    = ex_cte_cap_to_pres [OF set_irq_state_mdb_cte_wp_at set_irq_state_irq_node]

lemma set_irq_state_issued[wp]:
  "\<lbrace>\<top>\<rbrace> set_irq_state irq_state.IRQNotifyAEP irq \<lbrace>\<lambda>rv. irq_issued irq\<rbrace>"
  apply (simp add: set_irq_state_def irq_issued_def)
  apply wp
  apply clarsimp
  done

lemma IRQHandler_valid:
  "(s \<turnstile> cap.IRQHandlerCap irq) = (irq \<le> maxIRQ)"
  by (simp add: valid_cap_def cap_aligned_def word_bits_conv)




lemma no_cap_to_obj_with_diff_IRQHandler[simp]:
  "no_cap_to_obj_with_diff_ref (cap.IRQHandlerCap irq) S = \<top>"
  by (rule ext, simp add: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state
                          obj_ref_none_no_asid)

lemma set_irq_state_valid_cap[wp]:
  "\<lbrace>valid_cap cap\<rbrace> set_irq_state IRQNotifyAEP irq \<lbrace>\<lambda>rv. valid_cap cap\<rbrace>"
  apply (clarsimp simp: set_irq_state_def)
  apply (wp do_machine_op_valid_cap)
  apply (auto simp: valid_cap_def valid_untyped_def 
             split: cap.splits option.splits arch_cap.splits 
         split del: split_if)
  done

crunch valid_global_refs[wp]: set_irq_state "valid_global_refs"

lemma invoke_irq_handler_invs':
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
   (\<lambda>s. \<forall>t. cap = ReplyCap t False \<longrightarrow>
            st_tcb_at awaiting_reply t s \<and> \<not> has_reply_cap t s) and
   K (\<not> is_master_reply_cap cap))\<rbrace>
  cap_insert cap src dest \<lbrace>\<lambda>rv s. invs s \<and> ex_inv s\<rbrace>"
   apply wp
   apply (auto simp: cte_wp_at_caps_of_state)
   done
  show ?thesis
  apply (cases i, simp_all)
    apply (wp maskInterrupt_invs)
     apply simp
    apply simp
   apply (rename_tac irq cap prod)
   apply (rule hoare_pre)
    apply (wp valid_cap_typ [OF cap_delete_one_typ_at])
     apply (strengthen real_cte_tcb_valid)
     apply (wp real_cte_at_typ_valid [OF cap_delete_one_typ_at])
     apply (rule_tac Q="\<lambda>rv s. is_aep_cap cap \<and> invs s
                              \<and> cte_wp_at (is_derived (cdt s) prod cap) prod s"
                in hoare_post_imp)
      apply (clarsimp simp: is_cap_simps is_derived_def cte_wp_at_caps_of_state)
      apply (simp split: split_if_asm)
      apply (simp add: cap_master_cap_def split: cap.split_asm)
      apply (drule cte_wp_valid_cap [OF caps_of_state_cteD] | clarsimp)+
      apply (clarsimp simp: cap_master_cap_simps valid_cap_def obj_at_def is_aep is_tcb is_cap_table
                     split: option.split_asm dest!:cap_master_cap_eqDs)
     apply (wp cap_delete_one_still_derived)
    apply simp
        apply (wp get_irq_slot_ex_cte get_irq_slot_different hoare_drop_imps)
      apply (clarsimp simp: valid_state_def invs_def appropriate_cte_cap_def
                            is_cap_simps)
      apply (erule cte_wp_at_weakenE, simp add: is_derived_use_interrupt)
     apply (wp| simp add: setInterruptMode_def)+
  done
qed

lemmas invoke_irq_handler_invs[wp] = invoke_irq_handler_invs'[where ex_inv=\<top>, simplified hoare_post_taut, OF TrueI TrueI TrueI,simplified]

lemma invoke_irq_control_invs[wp]:
  "\<lbrace>invs and irq_control_inv_valid i\<rbrace> invoke_irq_control i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i, simp_all)
  apply (rule hoare_pre)
   apply (wp cap_insert_simple_invs
             | simp add: IRQHandler_valid is_cap_simps
             | strengthen real_cte_tcb_valid)+
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        is_simple_cap_def is_cap_simps is_pt_cap_def
                        safe_parent_for_def
                        ex_cte_cap_to_cnode_always_appropriate_strg)
  done

lemma resetTimer_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op resetTimer \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="%_ b. underlying_memory b p = underlying_memory m p"
                 in use_valid)
     apply (simp add: resetTimer_def
                      machine_op_lift_def machine_rest_lift_def split_def)
     apply wp
    apply (clarsimp+)[2]
  apply(erule use_valid, wp no_irq_resetTimer, assumption)
  done

crunch interrupt_states[wp]: update_waiting_aep, async_ipc_cancel, blocked_ipc_cancel "\<lambda>s. P (interrupt_states s)" (wp: mapM_x_wp_inv)

lemma ipc_cancel_noreply_interrupt_states:
  "\<lbrace>\<lambda>s. st_tcb_at (\<lambda>st. st \<noteq> BlockedOnReply) t s \<and> P (interrupt_states s) \<rbrace> ipc_cancel t \<lbrace> \<lambda>_ s. P (interrupt_states s) \<rbrace>"
  apply (simp add: ipc_cancel_def)
  apply (wp | wpc | simp)+
     apply (rule hoare_pre_cont)
    apply (wp)
  apply (rule hoare_pre)
   apply (wp gts_wp)
  apply (auto simp: pred_tcb_at_def obj_at_def)
  done

lemma send_async_ipc_interrupt_states[wp_unsafe]:
  "\<lbrace>\<lambda>s. P (interrupt_states s) \<and> valid_objs s\<rbrace> send_async_ipc a b \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace>"
  apply (simp add: send_async_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_aep_sp])
  apply (rule hoare_pre)
  apply (wp ipc_cancel_noreply_interrupt_states gts_wp hoare_vcg_all_lift thread_get_wp | wpc | simp)+
  apply (clarsimp)
  apply (erule (1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_aep_def obj_at_def is_tcb_def)
  apply (case_tac ko, simp_all)
  apply (auto simp: pred_tcb_at_def obj_at_def receive_blocked_def)
  done


lemma handle_interrupt_invs[wp]:
  "\<lbrace>invs\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: handle_interrupt_def ackInterrupt_def)
  apply (wp maskInterrupt_invs | wpc)+
     apply (wp get_cap_wp send_async_ipc_interrupt_states)
    apply (rule_tac Q="\<lambda>rv. invs and (\<lambda>s. st = interrupt_states s irq)" in hoare_post_imp)
     apply (clarsimp simp: ex_nonz_cap_to_def invs_valid_objs)
     apply (intro allI exI, erule cte_wp_at_weakenE)
     apply (clarsimp simp: is_cap_simps)
    apply (wp hoare_drop_imps | simp add: get_irq_state_def)+
  done

end
