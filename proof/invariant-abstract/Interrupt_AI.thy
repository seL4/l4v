(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Refinement for interrupt controller operations
*)

theory Interrupt_AI
imports ArchIpc_AI
begin

arch_requalify_facts
  arch_post_cap_deletion_mdb_inv
  handle_spurious_irq_invs
  invs_irq_state_independent

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
            \<and> (\<exists>ptr'. cte_wp_at ((=) (cap.IRQHandlerCap irq)) ptr' s)
            \<and> cte_wp_at (interrupt_derived cap) cte_ptr s
            \<and> s \<turnstile> cap \<and> is_ntfn_cap cap)"

consts
  arch_irq_control_inv_valid :: "arch_irq_control_invocation \<Rightarrow> ('a :: state_ext) state \<Rightarrow> bool"

primrec
  irq_control_inv_valid :: "irq_control_invocation \<Rightarrow> 'a::state_ext state \<Rightarrow> bool"
where
  "irq_control_inv_valid (Invocations_A.ArchIRQControl ivk) = (arch_irq_control_inv_valid ivk)"
| "irq_control_inv_valid (Invocations_A.IRQControl irq ptr ptr') =
       (cte_wp_at ((=) cap.NullCap) ptr and
        cte_wp_at ((=) cap.IRQControlCap) ptr'
        and ex_cte_cap_wp_to is_cnode_cap ptr and real_cte_at ptr
        and K (irq \<le> maxIRQ))"


locale Interrupt_AI =
  fixes state_ext_type1 :: "('a :: state_ext) itself"
  assumes decode_irq_control_invocation_inv[wp]:
    "\<And>(P  :: 'a state \<Rightarrow> bool) args slot label caps.
      \<lbrace>P\<rbrace> decode_irq_control_invocation label args slot caps \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes decode_irq_control_valid[wp]:
    "\<And>slot caps label args.
    \<lbrace>\<lambda>s :: 'a state. invs s \<and> (\<forall>cap \<in> set caps. s \<turnstile> cap)
          \<and> (\<forall>cap \<in> set caps. is_cnode_cap cap \<longrightarrow>
                  (\<forall>r \<in> cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s))
          \<and> cte_wp_at ((=) cap.IRQControlCap) slot s\<rbrace>
      decode_irq_control_invocation label args slot caps
    \<lbrace>irq_control_inv_valid\<rbrace>,-"
  assumes get_irq_slot_different:
    "\<And> irq ptr.
    \<lbrace>\<lambda>s :: 'a state. valid_global_refs s \<and> ex_cte_cap_wp_to is_cnode_cap ptr s\<rbrace>
       get_irq_slot irq
    \<lbrace>\<lambda>rv s. rv \<noteq> ptr\<rbrace>"
  assumes is_derived_use_interrupt:
    "\<And> cap cap' m p.
    (is_ntfn_cap cap \<and> interrupt_derived cap cap') \<longrightarrow> (is_derived m p cap cap')"
  assumes maskInterrupt_invs:
    "\<And>b irq.
    \<lbrace>invs and (\<lambda>s :: 'a state. \<not>b \<longrightarrow> interrupt_states s irq \<noteq> IRQInactive)\<rbrace>
      do_machine_op (maskInterrupt b irq)
    \<lbrace>\<lambda>rv. invs\<rbrace>"
  assumes no_cap_to_obj_with_diff_IRQHandler[simp]:
    "\<And> irq S. (no_cap_to_obj_with_diff_ref (IRQHandlerCap irq) S :: 'a state \<Rightarrow> bool)= \<top>"
  assumes set_irq_state_valid_cap[wp]:
    "\<And> cap irq.
    \<lbrace>valid_cap cap :: 'a state \<Rightarrow> bool\<rbrace>
      set_irq_state IRQSignal irq
    \<lbrace>\<lambda>rv. valid_cap cap\<rbrace>"
  assumes set_irq_state_valid_global_refs[wp]:
    "\<And> a b.
    \<lbrace>valid_global_refs :: 'a state \<Rightarrow> bool\<rbrace>
      set_irq_state a b
    \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  assumes invoke_irq_handler_invs':
    "\<And> (ex_inv :: 'a state \<Rightarrow> bool) i.
     \<lbrakk> \<And>f. \<lbrace>invs and ex_inv\<rbrace> do_machine_op f \<lbrace>\<lambda>rv::unit. ex_inv\<rbrace>;
       \<And>cap src dest.
       \<lbrace>ex_inv and invs and K (src \<noteq> dest)\<rbrace>
         cap_insert cap src dest
       \<lbrace>\<lambda>_.ex_inv\<rbrace>;
       \<And>cap. \<lbrace>ex_inv and invs\<rbrace> cap_delete_one cap \<lbrace>\<lambda>_.ex_inv\<rbrace>
     \<rbrakk> \<Longrightarrow>
     \<lbrace>invs and ex_inv and irq_handler_inv_valid i\<rbrace> invoke_irq_handler i \<lbrace>\<lambda>rv s. invs s \<and> ex_inv s\<rbrace>"
  assumes invoke_irq_control_invs[wp]:
    "\<And> i. \<lbrace>invs and irq_control_inv_valid i\<rbrace> invoke_irq_control i \<lbrace>\<lambda>rv. invs :: 'a state \<Rightarrow> bool\<rbrace>"
  assumes resetTimer_invs[wp]:
    "\<lbrace>invs :: 'a state \<Rightarrow> bool\<rbrace> do_machine_op resetTimer \<lbrace>\<lambda>_. invs\<rbrace>"
  assumes empty_fail_ackInterrupt[simp, intro!]:
    "\<And> irq. empty_fail (ackInterrupt irq)"
  assumes empty_fail_maskInterrupt[simp, intro!]:
    "\<And> f irq. empty_fail (maskInterrupt f irq)"
  assumes handle_interrupt_invs [wp]:
    "\<And> irq. \<lbrace>invs :: 'a state \<Rightarrow> bool\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_. invs\<rbrace>"
  assumes sts_arch_irq_control_inv_valid [wp]:
    "\<And>i t st.
      \<lbrace>arch_irq_control_inv_valid i :: 'a state \<Rightarrow> bool\<rbrace>
        set_thread_state t st
      \<lbrace>\<lambda>rv. arch_irq_control_inv_valid i\<rbrace>"

crunch decode_irq_handler_invocation
  for inv[wp]: "P"
  (simp: crunch_simps)

lemma valid_irq_handlersD:
  "\<lbrakk>cte_wp_at ((=) (IRQHandlerCap irq)) (a, b) s; valid_irq_handlers s\<rbrakk>  \<Longrightarrow>
  interrupt_states s irq = IRQSignal"
  apply(auto simp: valid_irq_handlers_def cte_wp_at_caps_of_state irq_issued_def cap_irqs_def cap_irq_opt_def split: cap.splits)
  done

lemma decode_irq_handler_valid[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> (\<forall>cap \<in> set caps. s \<turnstile> fst cap) \<and> (\<exists>ptr'. cte_wp_at ((=) (cap.IRQHandlerCap irq)) ptr' s)
        \<and> (\<forall>cap \<in> set caps. \<forall>r \<in> cte_refs (fst cap) (interrupt_irq_node s). ex_cte_cap_to r s)
        \<and> (\<forall>cap \<in> set caps. ex_cte_cap_wp_to is_cnode_cap (snd cap) s)
        \<and> (\<forall>cap \<in> set caps. cte_wp_at (interrupt_derived (fst cap)) (snd cap) s)\<rbrace>
     decode_irq_handler_invocation label irq caps
   \<lbrace>irq_handler_inv_valid\<rbrace>,-"
  apply (simp add: decode_irq_handler_invocation_def Let_def split_def
                  split del: if_split cong: if_cong)
  apply (rule hoare_pre, wp)
  apply (clarsimp simp: neq_Nil_conv)
  apply (fastforce dest: valid_irq_handlersD simp: invs_def valid_state_def)
  done

crunch is_irq_active
  for inv[wp]: "P"

lemma mod_le:
  "\<lbrakk>b < c;b dvd c\<rbrakk>  \<Longrightarrow> (a mod b \<le> a mod (c::nat))"
  apply (subst mod_mod_cancel[symmetric],simp)
  by simp

lemma is_up_8_32: "is_up (ucast :: word8 \<Rightarrow> word32)"
  by (simp add: is_up_def source_size_def target_size_def word_size)


crunch
  cancel_all_ipc, cancel_all_signals, fast_finalise, set_cap, post_cap_deletion
  for mdb_inv[wp]: "\<lambda>s. P (cdt s)"
  (wp: crunch_wps)

lemma cap_delete_one_still_derived:
  "\<lbrace>\<lambda>s. cte_wp_at (is_derived (cdt s) p' cap) p' s \<and> p \<noteq> p' \<and> valid_mdb s\<rbrace>
     cap_delete_one p
   \<lbrace>\<lambda>rv s. cte_wp_at (is_derived (cdt s) p' cap) p' s\<rbrace>"
  apply (simp add: cap_delete_one_def empty_slot_def unless_def
                   cte_wp_at_caps_of_state set_cdt_def)
  apply (wp hoare_vcg_ex_lift)
  apply (simp split del:if_split)
  apply (wp hoare_vcg_ex_lift get_cap_wp hoare_vcg_all_lift
            hoare_vcg_disj_lift
               | simp only: cte_wp_at_caps_of_state imp_conv_disj
                            cdt_update.caps_of_state_update
                            revokable_update.caps_of_state_update
               | simp)+
     apply (simp add: is_final_cap_def | wp)+
   apply (rule get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state if_apply_def2
             split del: if_split)
  apply (rule_tac x=capa in exI)
  apply (clarsimp simp only: is_derived_def simp_thms
                      split: if_split_asm)
   apply clarsimp
   apply (subst mdb_empty_abs.descendants[unfolded fun_upd_def])
    apply (rule mdb_empty_abs.intro)
    apply (rule vmdb_abs.intro)
    apply simp
   apply simp
  apply auto
  done


lemma cap_delete_one_cte_cap_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to P ptr\<rbrace> cap_delete_one ptr' \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P ptr\<rbrace>"
  apply (simp add: ex_cte_cap_wp_to_def)
  apply (wp hoare_vcg_ex_lift
            hoare_use_eq_irq_node [OF cap_delete_one_irq_node
                                      cap_delete_one_cte_wp_at_preserved])
  apply (clarsimp simp: can_fast_finalise_def split: cap.split_asm)+
  done


lemma get_irq_slot_ex_cte:
  "\<lbrace>\<lambda>s. \<exists>ptr. cte_wp_at ((=) (cap.IRQHandlerCap irq)) ptr s \<and> P (cap.IRQHandlerCap irq)\<rbrace>
      get_irq_slot irq
   \<lbrace>ex_cte_cap_wp_to P\<rbrace>"
  apply (simp add: get_irq_slot_def)
  apply wp
  apply (simp add: ex_cte_cap_wp_to_def)
  apply (elim conjE exEI cte_wp_at_weakenE)
  apply clarsimp
  done

crunch set_irq_state
  for pspace_aligned[wp]: "pspace_aligned"

crunch set_irq_state
  for pspace_distinct[wp]: "pspace_distinct"

lemma valid_mdb_interrupts[simp]:
  "valid_mdb (interrupt_states_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def mdb_cte_at_def)

crunch set_irq_state
  for valid_mdb[wp]: "valid_mdb"

crunch set_irq_state
  for mdb_cte_wp_at[wp]: "\<lambda>s. cte_wp_at (P (cdt s)) p s"
crunch set_irq_state
  for real_cte_at[wp]: "real_cte_at p"

lemmas set_irq_state_cte_cap_to[wp]
    = ex_cte_cap_to_pres [OF set_irq_state_mdb_cte_wp_at set_irq_state_irq_node]

lemma set_irq_state_issued[wp]:
  "\<lbrace>\<top>\<rbrace> set_irq_state irq_state.IRQSignal irq \<lbrace>\<lambda>rv. irq_issued irq\<rbrace>"
  apply (simp add: set_irq_state_def irq_issued_def)
  apply wp
  apply clarsimp
  done

lemma IRQHandler_valid:
  "(s \<turnstile> cap.IRQHandlerCap irq) = (irq \<le> maxIRQ)"
  by (simp add: valid_cap_def cap_aligned_def word_bits_conv)

lemmas (in Interrupt_AI)
  invoke_irq_handler_invs[wp] = invoke_irq_handler_invs'[where ex_inv=\<top>
                                                             , simplified hoare_TrueI
                                                             , OF TrueI TrueI TrueI
                                                             , simplified
                                                        ]

crunch update_waiting_ntfn, cancel_signal, blocked_cancel_ipc
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)" (wp: mapM_x_wp_inv)

lemma cancel_ipc_noreply_interrupt_states:
  "\<lbrace>\<lambda>s. st_tcb_at (\<lambda>st. st \<noteq> BlockedOnReply) t s \<and> P (interrupt_states s) \<rbrace> cancel_ipc t \<lbrace> \<lambda>_ s. P (interrupt_states s) \<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply wpsimp
     apply (rule hoare_pre_cont)
    apply (wp)
   apply (wp gts_wp)+
  apply (auto simp: pred_tcb_at_def obj_at_def)
  done

lemma send_signal_interrupt_states[wp_unsafe]:
  "\<lbrace>\<lambda>s. P (interrupt_states s) \<and> valid_objs s\<rbrace> send_signal a b \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace>"
  apply (simp add: send_signal_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
  apply (wp cancel_ipc_noreply_interrupt_states gts_wp hoare_vcg_all_lift thread_get_wp | wpc | simp)+
  apply (clarsimp)
  apply (erule (1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def is_tcb_def)
  apply (case_tac ko, simp_all)
  apply (auto simp: pred_tcb_at_def obj_at_def receive_blocked_def)
  done

context Interrupt_AI begin

lemma maybe_handle_interrupt_invs[wp]:
  "maybe_handle_interrupt in_kernel \<lbrace>invs :: 'a state \<Rightarrow> _\<rbrace>"
  unfolding maybe_handle_interrupt_def
  by (wpsimp wp: handle_spurious_irq_invs simp: invs_irq_state_independent)

end

end
