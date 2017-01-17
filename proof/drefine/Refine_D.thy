(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
 * Toplevel capDL refinement theorem.
 *)

theory Refine_D
imports Syscall_DR
begin

context begin interpretation Arch . (*FIXME: arch_split*)

text {*
  Toplevel @{text dcorres} theorem. 
*}

lemma valid_etcbs_sched: "valid_sched s \<longrightarrow> valid_etcbs s" by fastforce

lemma handle_event_invs_and_valid_sched:
  "\<lbrace>invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
      and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace> Syscall_A.handle_event e
  \<lbrace>\<lambda>rv. invs and valid_sched\<rbrace>"
  including no_pre by ((wp he_invs handle_event_valid_sched), simp)

lemma dcorres_call_kernel:
  "dcorres dc \<top>
          (invs and valid_sched and valid_pdpt_objs
             and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)
             and  (\<lambda>s. scheduler_action s = resume_cur_thread))
          (Syscall_D.call_kernel e) (Syscall_A.call_kernel e)"
  apply (simp_all add: Syscall_D.call_kernel_def Syscall_A.call_kernel_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       prefer 2
       apply (rule corres_split_handle [OF _ handle_event_corres])
         prefer 4
         apply (subst bind_return[symmetric])
         apply (rule corres_split)
            apply (rule activate_thread_corres[unfolded fun_app_def])
           apply simp
           apply (rule schedule_dcorres)
          apply (wp schedule_valid_sched | strengthen valid_etcbs_sched)+
        apply (simp add: handle_pending_interrupts_def)
        apply (rule corres_split [OF _ get_active_irq_corres])
          apply (clarsimp simp: when_def split: option.splits)
          apply (rule handle_interrupt_corres)
         apply ((wp | simp)+)[3]
      apply (rule hoare_post_imp_dc2E, rule handle_event_invs_and_valid_sched)
      apply (clarsimp simp: invs_def valid_state_def)
     apply (simp add: conj_comms if_apply_def2
            | wp | strengthen valid_etcbs_sched valid_idle_invs_strg)+
    apply (rule valid_validE2)
      apply (rule hoare_vcg_conj_lift)
       apply (rule he_invs)
      apply (rule handle_event_valid_sched)
     apply (fastforce intro: active_from_running)+

done

end

end
