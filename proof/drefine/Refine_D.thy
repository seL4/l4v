(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Toplevel capDL refinement theorem.
 *)

theory Refine_D
imports Syscall_DR
begin

context begin interpretation Arch . (*FIXME: arch-split*)

text \<open>
  Toplevel @{text dcorres} theorem.
\<close>

lemma handle_event_invs_and_valid_sched:
  "\<lbrace>invs and valid_sched and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)
      and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace> Syscall_A.handle_event e
  \<lbrace>\<lambda>rv. invs and valid_sched :: det_state \<Rightarrow> _\<rbrace>"
  by (wpsimp wp: he_invs handle_event_valid_sched)

lemma dcorres_call_kernel:
  "dcorres dc \<top>
          (invs and valid_sched and valid_pdpt_objs
             and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)
             and  (\<lambda>s. scheduler_action s = resume_cur_thread))
          (Syscall_D.call_kernel e) (Syscall_A.call_kernel e)"
  apply (simp_all add: Syscall_D.call_kernel_def Syscall_A.call_kernel_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule corres_split_handle [OF handle_event_corres])
         prefer 4
         apply (subst bind_return[symmetric])
         apply (rule corres_split)
            apply simp
            apply (rule schedule_dcorres)
           apply (rule activate_thread_corres[unfolded fun_app_def])
          apply (wp schedule_valid_sched)+
        apply (simp add: handle_pending_interrupts_def)
        apply (rule corres_split[OF get_active_irq_corres])
          apply corres_cases_both
           apply (rule dcorres_handle_spurious_irq)
          apply simp
          apply (rule handle_interrupt_corres[simplified dc_def])
         apply wpsimp
        apply wpsimp
        apply (rule hoare_drop_imps) (* getActiveIRQ invs *)
        apply wpsimp
       apply clarsimp (* needs to come before the wp, because goal has schematic post conditions *)
       apply wp
      apply (rule hoare_post_impE_E_dc, rule handle_event_invs_and_valid_sched)
      apply (clarsimp simp: invs_def valid_state_def)
      apply (simp add: conj_comms if_apply_def2 non_kernel_IRQs_def
             | wp handle_spurious_irq_invs
             | wpc
             | strengthen valid_idle_invs_strg)+
    apply (rule valid_validE2)
      apply (rule hoare_vcg_conj_lift)
       apply (rule he_invs)
      apply (rule handle_event_valid_sched)
     apply (fastforce intro: active_from_running simp: valid_sched_def)+
  done

end

end
