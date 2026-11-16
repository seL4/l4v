(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Ipc_DR
imports CNode_DR
begin

context begin interpretation Arch . (*FIXME: arch-split*)

abbreviation
  "thread_is_running y s \<equiv> st_tcb_at ((=) Structures_A.Running) y s"

lemmas [wp] = abs_typ_at_lifts[OF set_simple_ko_typ_at]

declare pbfs_atleast_pageBits [simp]

(* CORRES RULES *)

lemma cte_at_into_opt_cap:
  "cte_at p s = (\<exists>cap. cte_wp_at ((=) cap) p s
        \<and> (fst p \<noteq> idle_thread s \<longrightarrow> opt_cap (transform_cslot_ptr p) (transform s) = Some (transform_cap cap)))"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (safe, simp_all)
  apply (clarsimp simp: caps_of_state_transform_opt_cap)
  done

crunch set_object
  for not_idle[wp]: "not_idle_thread y :: 'a::state_ext state \<Rightarrow> bool"
  (simp: not_idle_thread_def get_object_def wp: dxo_wp_weak)

lemma set_scheduler_action_dcorres:
  "dcorres dc P P' (return ()) (set_scheduler_action sa)"
  by (clarsimp simp: set_scheduler_action_def modify_def get_def put_def bind_def return_def  corres_underlying_def)


lemma tcb_sched_action_transform_inv: "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> tcb_sched_action tcb_sched_enqueue t \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (clarsimp simp: tcb_sched_action_def)
  apply (wp | simp)+
  done

lemma set_scheduler_action_transform_inv:
  "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> set_scheduler_action act \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def)

lemma possible_switch_to_dcorres:
  "dcorres dc P P' (return ()) (possible_switch_to t)"
  apply (clarsimp simp: possible_switch_to_def cong: if_cong)
  apply (rule dcorres_symb_exec_r)+
        apply (rule corres_guard1_imp, rule corres_if_rhs)
          apply (rule tcb_sched_action_dcorres[THEN corres_trivial])
         apply (rule corres_if_rhs)
          apply (rule dcorres_symb_exec_r)+
            apply (rule tcb_sched_action_dcorres[THEN corres_trivial])
           apply (wp set_scheduler_action_transform_inv tcb_sched_action_transform_inv
                 | simp add: reschedule_required_def
                 | wpc
                 | rule set_scheduler_action_dcorres[THEN corres_trivial])+
  done

crunch tcb_sched_action
  for not_idle_thread[wp]: "not_idle_thread a"
  (wp: simp: not_idle_thread_def)

text \<open>ASpec predicate that corresponds to capDL @{const no_pending}.\<close>
definition no_signal_waiters :: "'z::state_ext state \<Rightarrow> bool" where
  "no_signal_waiters s \<equiv>
     \<forall>t. \<not> st_tcb_at (\<lambda>st. receive_blocked st \<or> (\<exists>ntfn. st = BlockedOnNotification ntfn)) t s"

lemma no_pending_transform_no_signal_waiters:
  "\<lbrakk> no_pending (transform s); valid_idle s \<rbrakk> \<Longrightarrow> no_signal_waiters s"
  apply (clarsimp simp: no_signal_waiters_def pred_tcb_at_def obj_at_def)
  apply (rename_tac t tcb)
  apply (frule get_tcb_rev)
  apply (case_tac "t = idle_thread s")
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def receive_blocked_def
                  split: Structures_A.thread_state.splits)
  apply (clarsimp simp: no_pending_def)
  apply (drule_tac x=t in spec)
  apply (simp add: opt_cap_tcb tcb_slot_defs)
  apply (clarsimp simp: is_pending_cap_def infer_tcb_pending_op_def receive_blocked_def
                 split: Structures_A.thread_state.splits)
  done

lemma no_signal_waiters_WaitingNtfn:
  "\<lbrakk> no_signal_waiters s; kheap s p = Some (kernel_object.Notification ntfn);
     ntfn_obj ntfn = WaitingNtfn q; valid_objs s; sym_refs (state_refs_of s) \<rbrakk>
   \<Longrightarrow> False"
  apply (frule (1) valid_objs_valid_ntfn_simp)
  apply (simp add: no_signal_waiters_def)
  apply (drule_tac x="hd q" in spec)
  apply (erule notE)
  apply (rule ntfn_queued_st_tcb_at[where ep=ntfn and ptr=p and rt=NTFNSignal];
         clarsimp simp: obj_at_def valid_ntfn_def)
  done

lemma send_signal_no_waiters_dcorres:
  notes if_split [split del]
  shows
  "dcorres dc \<top> (invs and no_signal_waiters) (return ()) (Ipc_A.send_signal ntfnptr badge)"
  unfolding Ipc_A.send_signal_def invs_def
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp: get_simple_ko_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp: assert_def corres_free_fail partial_inv_def a_type_def the_equality
                  split: Structures_A.kernel_object.splits if_split)
  apply (rule conjI, clarsimp+)
  apply (rename_tac ntfn)
  apply (case_tac "ntfn_obj ntfn"; clarsimp)
    apply (case_tac "ntfn_bound_tcb ntfn"; clarsimp)
     apply (rule corres_guard_imp, rule corres_dummy_set_notification, simp+)[1]
    apply (clarsimp simp: get_thread_state_def thread_get_def gets_the_def gets_def bind_assoc)
    apply (rule dcorres_absorb_get_r)
    apply (clarsimp simp: assert_opt_def corres_free_fail
                    split: Structures_A.kernel_object.splits option.splits)
    apply (rename_tac tcb)
    apply (subgoal_tac "\<not> receive_blocked (tcb_state tcb)")
     apply clarsimp
     apply (rule corres_guard_imp, rule corres_dummy_set_notification, simp+)[1]
    apply (clarsimp simp: no_signal_waiters_def pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
   apply (rule FalseE)
   apply (fastforce elim: no_signal_waiters_WaitingNtfn simp: valid_state_def valid_pspace_def)
  apply (rule corres_guard_imp, rule corres_dummy_set_notification, simp+)[1]
  done

lemma evalMonad_get_extra_cptrs:
  "\<lbrakk>evalMonad (lookup_ipc_buffer False thread) s = Some (Some buf);get_tcb thread s = Some tcb;
    (evalMonad (Ipc_A.get_extra_cptrs (Some buf) (data_to_message_info (arch_tcb_get_registers (tcb_arch tcb) msg_info_register))) s) = Some a
    \<rbrakk>
  \<Longrightarrow> a = (map (to_bl) (cdl_intent_extras $ transform_full_intent (machine_state s) thread tcb))"
  including no_pre
  apply (clarsimp simp:get_extra_cptrs_def)
  apply (clarsimp simp:liftM_def)
  apply (subst (asm) evalMonad_compose)
     apply (rule empty_when_fail_mapM)
     apply (simp add:weak_det_spec_load_word_offs empty_when_fail_load_word_offs)
    apply (rule weak_det_spec_mapM)
    apply (simp add:weak_det_spec_load_word_offs)
   apply (wp mapM_wp,fastforce)
  apply (clarsimp split:option.splits)
  apply (rule_tac x = x2 in arg_cong)
  apply (clarsimp simp:transform_full_intent_def Let_def)
  apply (clarsimp simp:get_ipc_buffer_words_def)
  apply (drule lookup_ipc_buffer_SomeB_evalMonad)
  apply (clarsimp simp:cte_wp_at_cases obj_at_def dest!: get_tcb_SomeD)
  apply (drule sym[where t = "tcb_ipcframe tcb"])
  apply clarsimp
  apply (simp add:mapM_load_word_offs_do_machine_op)
  apply (subst (asm) evalMonad_do_machine_op[symmetric])
    apply (rule weak_det_spec_mapM[OF weak_det_spec_loadWord])
   apply (rule empty_when_fail_mapM)
   apply (clarsimp simp:empty_when_fail_loadWord weak_det_spec_loadWord)
  apply (clarsimp simp:get_tcb_message_info_def arch_tcb_context_get_def arch_tcb_get_registers_def)
  done

lemma dcorres_symb_exec_r_evalMonad:
  assumes wp:"\<And>sa. \<lbrace>(=) sa\<rbrace> f \<lbrace>\<lambda>r. (=) sa\<rbrace>"
  assumes corres:"\<And>rv. evalMonad f s = Some rv \<Longrightarrow> dcorres r P ((=) s) h (g rv)"
  shows "\<lbrakk> empty_when_fail f; weak_det_spec ((=) s) f \<rbrakk> \<Longrightarrow> dcorres r P ((=) s) h (f>>=g)"
  apply (rule_tac Q'="\<lambda>r. (=) s and K_bind (evalMonad f s = Some r)" in corres_symb_exec_r)
     apply (rule dcorres_expand_pfx)
     using corres
     apply (clarsimp simp:corres_underlying_def)
    apply (wp wp, simp, rule evalMonad_wp)
      apply (simp add:wp)+
  done

lemma dcorres_dummy_corrupt_ipc_buffer:
  "dcorres dc (\<top>) (tcb_at y and valid_idle and not_idle_thread y) (corrupt_ipc_buffer y b) (return x)"
  apply (clarsimp simp:corrupt_ipc_buffer_def get_ipc_buffer_def)
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:tcb_at_def)
  apply (subst opt_cap_tcb)
    apply (simp add:not_idle_thread_def assert_opt_def)+
  apply (case_tac "tcb_ipcframe tcb")
             apply simp_all
             apply (rule corres_guard_imp[OF dummy_corrupt_tcb_intent_corres]
               ,(clarsimp simp:not_idle_thread_def tcb_at_def)+)+
  apply (rename_tac arch_cap)
  apply (case_tac "arch_cap")
      apply simp_all
      apply (rule corres_guard_imp[OF dummy_corrupt_tcb_intent_corres]
        ,(clarsimp simp:not_idle_thread_def tcb_at_def)+)+
    apply (clarsimp simp: | rule conjI)+
     apply (rule corres_guard_imp[OF dcorres_dummy_corrupt_frame],clarsimp+)
    apply (clarsimp | rule conjI)+
     apply (rule corres_guard_imp[OF dcorres_dummy_corrupt_frame],clarsimp+)
    apply (rule corres_guard_imp[OF dummy_corrupt_tcb_intent_corres]
      ,(clarsimp simp:not_idle_thread_def tcb_at_def)+)+
  done

lemma dcorres_lookup_extra_caps:
  "\<lbrakk>evalMonad (lookup_ipc_buffer False thread) s = Some buffer; get_tcb thread s = Some t;
    valid_global_refs s; valid_objs s; valid_irq_node s; valid_idle s;
    not_idle_thread thread s\<rbrakk>
    \<Longrightarrow> dcorres (dc \<oplus> (\<lambda>extra extra'. extra = transform_cap_list extra'))
     \<top> ((=) s)
     (Endpoint_D.lookup_extra_caps thread
                                   (cdl_intent_extras (transform_full_intent (machine_state s) thread t)))
     (Ipc_A.lookup_extra_caps thread buffer (data_to_message_info (arch_tcb_get_registers (tcb_arch t) msg_info_register)))"
  apply (clarsimp simp:lookup_extra_caps_def liftE_bindE Endpoint_D.lookup_extra_caps_def)
  apply (rule corres_symb_exec_r)
     apply (rule_tac F = "evalMonad (get_extra_cptrs buffer (data_to_message_info (arch_tcb_get_registers (tcb_arch t) msg_info_register))) s = Some rv"
                     in corres_gen_asm2)
     apply (rule corres_mapME[where S = "{(x,y). x = of_bl y \<and> length y = word_bits}"])
           prefer 3
           apply simp
           apply (rule dcorres_lookup_cap_and_slot[simplified])
            apply (clarsimp simp:transform_cap_list_def)+
       apply wp
       apply simp
      apply (case_tac buffer)
       apply clarsimp
       apply (simp add:transform_full_intent_def Let_def)
       apply (rule get_ipc_buffer_words_empty)
        apply (simp add:obj_at_def)
        apply (erule get_tcb_SomeD)
       apply simp
      apply clarify
      apply (subst evalMonad_get_extra_cptrs)
         apply simp+
     apply (case_tac buffer)
      apply clarsimp
     apply clarify
     apply (drule evalMonad_get_extra_cptrs)
       apply (simp del:get_extra_cptrs.simps add: zip_map_eqv[where g = "\<lambda>x. x",simplified])+
     apply (simp add: word_bits_def del:get_extra_cptrs.simps)
    apply (wp evalMonad_wp)
      apply (case_tac buffer)
       apply (simp add:get_extra_cptrs_def empty_when_fail_simps)+
      apply (simp add:liftM_def)
      apply (rule empty_when_fail_compose)
        apply (simp add:empty_when_fail_simps)+
       apply (rule empty_when_fail_mapM)
       apply (simp add:weak_det_spec_load_word_offs empty_when_fail_load_word_offs)
      apply (rule weak_det_spec_mapM)
      apply (simp add:weak_det_spec_load_word_offs)
     apply (case_tac buffer)
      apply (simp add:get_extra_cptrs_def weak_det_spec_simps)+
     apply (simp add:liftM_def)
     apply (rule weak_det_spec_compose)
      apply (simp add:weak_det_spec_simps)
     apply (rule weak_det_spec_mapM)
     apply (simp add:weak_det_spec_load_word_offs)
    apply (clarsimp simp:valid_state_def valid_pspace_def cur_tcb_def)+
   apply (wp|clarsimp)+
  done

lemmas [simp] = AllowSend_def AllowRecv_def CanModify_def

end

end
