(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DomainSepInv
imports
  "ArchIpc_AC" (* for transfer_caps_loop_pres_dest lec_valid_cap' set_simple_ko_get_tcb thread_set_tcb_fault_update_valid_mdb *)
  "Monads.WPBang"
begin

text \<open>
  We define and prove an invariant that is necessary to achieve domain
  separation on seL4. In its strongest form, we require that all IRQs, other than
  those for the timer, are inactive, and that no IRQControl or
  IRQHandler caps are present (to prevent any inactive IRQs from becoming
  active in the future).

  It always requires that there are no domain caps.
\<close>

text \<open>
  When @{term irqs} is @{term False} we require that non-timer IRQs are off permanently.
\<close>
definition domain_sep_inv :: "bool \<Rightarrow> 'a :: state_ext state \<Rightarrow> 'b :: state_ext state \<Rightarrow> bool" where
  "domain_sep_inv irqs st s \<equiv>
    (\<forall>slot. \<not> cte_wp_at ((=) DomainCap) slot s) \<and>
    (irqs \<or> (\<forall>irq slot. \<not> cte_wp_at ((=) IRQControlCap) slot s
                      \<and> \<not> cte_wp_at ((=) (IRQHandlerCap irq)) slot s
                      \<and> interrupt_states s irq \<noteq> IRQSignal
                      \<and> interrupt_states s irq \<noteq> IRQReserved
                      \<and> interrupt_states s = interrupt_states st))"

definition domain_sep_inv_cap where
  "domain_sep_inv_cap irqs cap \<equiv> case cap of
     IRQControlCap \<Rightarrow> irqs
   | IRQHandlerCap irq \<Rightarrow> irqs
   | DomainCap \<Rightarrow> False
   | _ \<Rightarrow> True"

lemma cte_wp_at_not_domain_sep_inv_cap:
  "cte_wp_at (not domain_sep_inv_cap irqs) slot s \<longleftrightarrow>
   ((irqs \<longrightarrow> False) \<and>
    (\<not> irqs \<longrightarrow> (cte_wp_at ((=) IRQControlCap) slot s \<or>
                 (\<exists> irq. cte_wp_at ((=) (IRQHandlerCap irq)) slot s)))) \<or>
   cte_wp_at ((=) DomainCap) slot s"
  apply (rule iffI)
   apply (drule cte_wp_at_norm)
   apply clarsimp
   apply (case_tac c, simp_all add: domain_sep_inv_cap_def pred_neg_def)
   apply (auto elim: cte_wp_at_weakenE split: if_splits)
  done

lemma domain_sep_inv_def2:
  "domain_sep_inv irqs st s =
    ((\<forall>slot. \<not> cte_wp_at ((=) DomainCap) slot s) \<and>
     (irqs \<or> (\<forall>irq slot. \<not> cte_wp_at ((=) IRQControlCap) slot s
                       \<and> \<not> cte_wp_at ((=) (IRQHandlerCap irq)) slot s)) \<and>
     (irqs \<or> (\<forall>irq. interrupt_states s irq \<noteq> IRQSignal
                  \<and> interrupt_states s irq \<noteq> IRQReserved
                  \<and> interrupt_states s = interrupt_states st)))"
  by (fastforce simp: domain_sep_inv_def)

lemma domain_sep_inv_wp:
  assumes nctrl:
    "\<And>slot. \<lbrace>(\<lambda>s. \<not> cte_wp_at (not domain_sep_inv_cap irqs) slot s) and P\<rbrace>
             f
             \<lbrace>\<lambda>_ s. \<not> cte_wp_at (not domain_sep_inv_cap irqs) slot s\<rbrace>"
  assumes irq_pres:
    "\<And>P. \<not> irqs \<Longrightarrow> \<lbrace>(\<lambda>s. P (interrupt_states s)) and R\<rbrace>
                     f
                     \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace>"
  shows
    "\<lbrace>domain_sep_inv irqs st and P and (\<lambda>s. irqs \<or> R s)\<rbrace>
     f
     \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (clarsimp simp: domain_sep_inv_def2 valid_def)
  apply (subst conj_assoc[symmetric])
  apply (rule conjI)
   apply (rule conjI)
    apply (intro allI)
    apply (erule use_valid[OF _ hoare_strengthen_post[OF nctrl]])
     apply (fastforce simp: cte_wp_at_not_domain_sep_inv_cap)
    apply (fastforce simp: cte_wp_at_not_domain_sep_inv_cap)
   apply (fastforce elim!: use_valid[OF _ hoare_strengthen_post[OF nctrl]]
                     simp: cte_wp_at_not_domain_sep_inv_cap)
  apply (case_tac "irqs")
   apply blast
  apply (rule disjI2)
  apply simp
  apply (intro allI conjI)
    apply (erule_tac P1="\<lambda>x. x irq \<noteq> IRQSignal" in use_valid[OF _ irq_pres], assumption)
    apply blast
   apply (erule use_valid[OF _ irq_pres], assumption)
   apply blast
  apply (erule use_valid[OF _ irq_pres], assumption)
  apply blast
  done

lemma domain_sep_inv_triv:
  assumes cte_pres: "\<And>P slot. \<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace> f \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  assumes irq_pres: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace> f \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace>"
  shows "\<lbrace>domain_sep_inv irqs st\<rbrace> f \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (rule domain_sep_inv_wp[where P="\<top>" and R="\<top>", simplified])
  apply (rule cte_pres, rule irq_pres)
  done

lemma domain_sep_inv_updates[simp]:
  "\<And>f. domain_sep_inv irqs st (trans_state f s) = domain_sep_inv irqs st s"
  "\<And>f. domain_sep_inv irqs st (arch_state_update f s) = domain_sep_inv irqs st s"
  "\<And>f. domain_sep_inv irqs st (machine_state_update f s) = domain_sep_inv irqs st s"
  "\<And>f. domain_sep_inv irqs st (is_original_cap_update f s) = domain_sep_inv irqs st s"
  "\<And>f. domain_sep_inv irqs st (cdt_update f s) = domain_sep_inv irqs st s"
  "\<And>f. domain_sep_inv irqs st (scheduler_action_update f s) = domain_sep_inv irqs st s"
  "\<And>f. domain_sep_inv irqs st (domain_index_update f s) = domain_sep_inv irqs st s"
  "\<And>f. domain_sep_inv irqs st (cur_domain_update f s) = domain_sep_inv irqs st s"
  "\<And>f. domain_sep_inv irqs st (domain_time_update f s) = domain_sep_inv irqs st s"
  "\<And>f. domain_sep_inv irqs st (ready_queues_update f s) = domain_sep_inv irqs st s"
  by (simp add: domain_sep_inv_def)+

lemma detype_interrupts_states[simp]:
  "interrupt_states (detype S s) = interrupt_states s"
  by (simp add: detype_def)

lemma detype_domain_sep_inv[simp]:
  "domain_sep_inv irqs st s \<longrightarrow> domain_sep_inv irqs st (detype S s)"
  by (fastforce simp: domain_sep_inv_def)

lemma domain_sep_inv_detype_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. domain_sep_inv irqs st\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. domain_sep_inv irqs st (detype S s)\<rbrace>"
  by (strengthen detype_domain_sep_inv, assumption)

crunch set_extra_badge
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"

(* FIXME: following 3 lemmas clagged from FinalCaps *)
lemma set_cap_neg_cte_wp_at_other_helper':
  "\<lbrakk> oslot \<noteq> slot; ko_at (TCB x) (fst oslot) s;
     tcb_cap_cases (snd oslot) = Some (ogetF, osetF, orestr);
     kheap (s\<lparr>kheap := (kheap s)(fst oslot \<mapsto> TCB (osetF (\<lambda> x. cap) x))\<rparr>) (fst slot) = Some (TCB tcb);
     tcb_cap_cases (snd slot) = Some (getF, setF, restr); P (getF tcb) \<rbrakk>
     \<Longrightarrow> cte_wp_at P slot s"
  apply (case_tac "fst oslot = fst slot")
   apply (rule cte_wp_at_tcbI)
     apply (fastforce split: if_splits simp: obj_at_def)
    apply assumption
   apply (fastforce split: if_splits simp: tcb_cap_cases_def dest: prod_eqI)
  apply (rule cte_wp_at_tcbI)
    apply (fastforce split: if_splits simp: obj_at_def)
   apply assumption
  apply assumption
  done

lemma set_cap_neg_cte_wp_at_other_helper:
  "\<lbrakk> \<not> cte_wp_at P slot s; oslot \<noteq> slot; ko_at (TCB x) (fst oslot) s;
     tcb_cap_cases (snd oslot) = Some (getF, setF, restr) \<rbrakk>
     \<Longrightarrow> \<not> cte_wp_at P slot (s\<lparr>kheap := (kheap s)(fst oslot \<mapsto> TCB (setF (\<lambda> x. cap) x))\<rparr>)"
  apply (rule notI)
  apply (erule cte_wp_atE)
   apply (fastforce elim: notE intro: cte_wp_at_cteI split: if_splits)
  apply (fastforce elim: notE intro: set_cap_neg_cte_wp_at_other_helper')
  done

lemma set_cap_neg_cte_wp_at_other:
  "oslot \<noteq> slot \<Longrightarrow> set_cap cap oslot \<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>"
  unfolding set_cap_def
  apply (wp set_object_wp get_object_wp | wpc | simp add: split_def)+
  apply (intro allI impI conjI)
       apply (rule notI)
       apply (erule cte_wp_atE)
        apply (fastforce split: if_splits dest: prod_eqI elim: notE intro: cte_wp_at_cteI simp: obj_at_def)
       apply (fastforce split: if_splits elim: notE intro: cte_wp_at_tcbI)
      apply (auto dest: set_cap_neg_cte_wp_at_other_helper)
  done

lemma set_cap_neg_cte_wp_at:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s \<and> \<not> P capa\<rbrace>
   set_cap capa slota
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply (case_tac "slot = slota")
   apply simp
   apply (simp add: set_cap_def set_object_def)
   apply (rule hoare_pre)
    apply (wp get_object_wp | wpc)+
   apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  apply (rule hoare_pre)
   apply (rule set_cap_neg_cte_wp_at_other, simp+)
  done

lemma domain_sep_inv_cap_IRQControlCap:
  "\<lbrakk> domain_sep_inv_cap irqs cap; \<not> irqs \<rbrakk> \<Longrightarrow> cap \<noteq> IRQControlCap"
  by (auto simp: domain_sep_inv_cap_def)

lemma domain_sep_inv_cap_IRQHandlerCap:
  "\<lbrakk> domain_sep_inv_cap irqs cap; \<not> irqs \<rbrakk> \<Longrightarrow> cap \<noteq> IRQHandlerCap irq"
  by (auto simp: domain_sep_inv_cap_def)

lemma set_cap_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and K (domain_sep_inv_cap irqs cap)\<rbrace>
   set_cap cap slot
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
   apply (rule domain_sep_inv_wp)
   apply (wp set_cap_neg_cte_wp_at | simp add: pred_neg_def | blast)+
  done

lemma cte_wp_at_domain_sep_inv_cap:
  "\<lbrakk> domain_sep_inv irqs st s; cte_wp_at ((=) cap) slot s \<rbrakk>
     \<Longrightarrow> domain_sep_inv_cap irqs cap"
  apply (case_tac slot)
  apply (auto simp: domain_sep_inv_def domain_sep_inv_cap_def split: cap.splits)
  done

lemma weak_derived_irq_handler:
  "weak_derived (IRQHandlerCap irq) cap \<Longrightarrow> cap = (IRQHandlerCap irq)"
  by (auto simp: weak_derived_def copy_of_def same_object_as_def split: cap.splits if_splits)

(* FIXME: move to CSpace_AI *)
lemma weak_derived_DomainCap:
  "weak_derived c' c \<Longrightarrow> (c' = DomainCap) = (c = DomainCap)"
  apply (clarsimp simp: weak_derived_def)
  apply (erule disjE)
   apply (clarsimp simp: copy_of_def split: if_split_asm)
   apply (auto simp: is_cap_simps same_object_as_def
              split: cap.splits)[1]
  apply simp
  done

lemma cte_wp_at_weak_derived_domain_sep_inv_cap:
  "\<lbrakk> domain_sep_inv irqs st s; cte_wp_at (weak_derived cap) slot s \<rbrakk>
     \<Longrightarrow> domain_sep_inv_cap irqs cap"
  apply (cases slot)
  apply (force simp: domain_sep_inv_def domain_sep_inv_cap_def
              split: cap.splits
               dest: cte_wp_at_norm weak_derived_irq_handler weak_derived_DomainCap)
  done

lemma is_derived_IRQHandlerCap:
  "is_derived m src (IRQHandlerCap irq) cap \<Longrightarrow> (cap = IRQHandlerCap irq)"
  apply (clarsimp simp: is_derived_def)
  apply (case_tac cap, simp_all add: is_cap_simps cap_master_cap_def)
  done

(* FIXME: move to CSpace_AI *)
lemma DomainCap_is_derived:
  "is_derived m src DomainCap cap \<Longrightarrow> cap = DomainCap"
  by (auto simp: is_derived_def is_reply_cap_def is_master_reply_cap_def cap_master_cap_def
          split: cap.splits)

lemma cte_wp_at_is_derived_domain_sep_inv_cap:
  "\<lbrakk> domain_sep_inv irqs st s; cte_wp_at (is_derived (cdt s) slot cap) slot s \<rbrakk>
     \<Longrightarrow> domain_sep_inv_cap irqs cap"
  apply (cases slot)
  apply (fastforce simp: domain_sep_inv_def domain_sep_inv_cap_def
                  split: cap.splits
                   dest: cte_wp_at_norm DomainCap_is_derived is_derived_IRQHandlerCap)
  done

crunch update_cdt
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"

lemma set_untyped_cap_as_full_domain_sep_inv[wp]:
  "set_untyped_cap_as_full a b c \<lbrace>domain_sep_inv irqs st\<rbrace>"
  apply (clarsimp simp: set_untyped_cap_as_full_def)
  apply (rule hoare_pre)
   apply (rule set_cap_domain_sep_inv)
  apply (case_tac a, simp_all add: domain_sep_inv_cap_def)
  done

lemma cap_insert_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and (\<lambda>s. cte_wp_at (is_derived (cdt s) slot cap) slot s)\<rbrace>
   cap_insert cap slot dest_slot
   \<lbrace>\<lambda>_. domain_sep_inv irqs st \<rbrace>"
  apply (simp add: cap_insert_def)
  apply (wpsimp wp: set_cap_domain_sep_inv get_cap_wp set_original_wp dxo_wp_weak)
  apply (blast dest: cte_wp_at_is_derived_domain_sep_inv_cap)
  done

lemma domain_sep_inv_cap_NullCap[simp]:
  "domain_sep_inv_cap irqs NullCap"
  by (simp add: domain_sep_inv_cap_def)

lemma cap_move_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and (\<lambda>s. cte_wp_at (weak_derived cap) slot s)\<rbrace>
   cap_move cap slot dest_slot
   \<lbrace>\<lambda>_. domain_sep_inv irqs st \<rbrace>"
  apply (simp add: cap_move_def)
  apply (wpsimp wp: set_cap_domain_sep_inv get_cap_wp set_original_wp dxo_wp_weak)
  apply (blast dest: cte_wp_at_weak_derived_domain_sep_inv_cap)
  done

lemma set_irq_state_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and (\<lambda>s. stt = interrupt_states s irq)\<rbrace>
   set_irq_state stt irq
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (simp add: set_irq_state_def)
  apply (wp | simp add: do_machine_op_def | wpc)+
  done


locale DomainSepInv_1 =
  fixes state_ext_t :: "'state_ext :: state_ext itself"
  assumes arch_finalise_cap_domain_sep_inv[wp]:
    "arch_finalise_cap c x \<lbrace>\<lambda>s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  and arch_post_cap_deletion_domain_sep_inv[wp]:
    "arch_post_cap_deletion acap \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and init_arch_objects_domain_sep_inv[wp]:
    "init_arch_objects typ dev ptr n sz refs \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and prepare_thread_delete_domain_sep_inv[wp]:
    "prepare_thread_delete t \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and arch_finalise_cap_rv:
    "\<lbrace>\<lambda>_. P (NullCap,NullCap)\<rbrace> arch_finalise_cap c x \<lbrace>\<lambda>rv s :: det_state. P rv\<rbrace>"
  and arch_switch_to_thread_domain_sep_inv[wp]:
    "arch_switch_to_thread t \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs (st :: 'state_ext state) s\<rbrace>"
  and arch_switch_to_idle_thread_domain_sep_inv[wp]:
    "arch_switch_to_idle_thread \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and arch_activate_idle_thread_domain_sep_inv[wp]:
    "arch_activate_idle_thread t \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and arch_mask_irq_signal_domain_sep_inv[wp]:
    "arch_mask_irq_signal irq \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and arch_derive_cap_domain_sep_inv[wp]:
    "\<lbrace>\<top>\<rbrace> arch_derive_cap acap \<lbrace>\<lambda>rv s :: det_state. domain_sep_inv_cap irqs rv\<rbrace>,-"
  and arch_post_modify_registers_domain_sep_inv[wp]:
    "arch_post_modify_registers cur t \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and arch_prepare_set_domain_domain_sep_inv[wp]:
    "arch_prepare_set_domain t new_dom \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and arch_prepare_next_domain_domain_sep_inv[wp]:
    "arch_prepare_next_domain \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and arch_post_set_flags_domain_sep_inv[wp]:
    "arch_post_set_flags t flags \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and handle_arch_fault_reply_domain_sep_inv[wp]:
    "handle_arch_fault_reply vmf thread d ds \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and handle_vm_fault_domain_sep_inv[wp]:
    "handle_vm_fault t vmf_t \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
begin

lemma deleted_irq_handler_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and K irqs\<rbrace>
   deleted_irq_handler irq
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: deleted_irq_handler_def set_irq_state_def)
  apply wp
  apply (simp add: domain_sep_inv_def)
  done

lemma empty_slot_domain_sep_inv:
  "\<lbrace>\<lambda>s. domain_sep_inv irqs st s \<and> (\<not> irqs \<longrightarrow> b = NullCap)\<rbrace>
   empty_slot a b
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  unfolding empty_slot_def post_cap_deletion_def
  by (wpsimp wp: get_cap_wp set_cap_domain_sep_inv set_original_wp dxo_wp_weak
                 hoare_weak_lift_imp deleted_irq_handler_domain_sep_inv)

end


lemma set_simple_ko_neg_cte_wp_at[wp]:
  "set_simple_ko f a b \<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>"
  apply (simp add: set_simple_ko_def)
  apply (wp set_object_wp_strong get_object_wp
         | simp add: partial_inv_def a_type_def split: kernel_object.splits)+
  apply (case_tac "a = fst slot")
   apply (clarsimp split: kernel_object.splits)
   apply (fastforce elim: cte_wp_atE simp: obj_at_def)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunch set_simple_ko
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)

crunch set_thread_state_act
  for neg_cte_wp_at[wp]: "\<lambda>s. \<not> cte_wp_at P c s"

lemma set_thread_state_neg_cte_wp_at[wp]:
  "set_thread_state a b \<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp set_object_wp get_object_wp | simp)+
  apply (case_tac "a = fst slot")
   apply (clarsimp split: kernel_object.splits)
   apply (erule notE)
   apply (erule cte_wp_atE)
    apply (fastforce simp: obj_at_def)
   apply (drule get_tcb_SomeD)
   apply (rule cte_wp_at_tcbI)
     apply simp
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma set_bound_notification_neg_cte_wp_at[wp]:
  "set_bound_notification a b \<lbrace>\<lambda>s. \<not> cte_wp_at P slot s\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wp set_object_wp get_object_wp dxo_wp_weak| simp)+
  apply (case_tac "a = fst slot")
   apply (clarsimp split: kernel_object.splits)
   apply (erule notE)
   apply (erule cte_wp_atE)
    apply (fastforce simp: obj_at_def)
   apply (drule get_tcb_SomeD)
   apply (rule cte_wp_at_tcbI)
     apply simp
    apply assumption
   apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

crunch set_thread_state, set_bound_notification, get_bound_notification
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)

lemma thread_set_domain_sep_inv_triv:
  "\<lbrakk>\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb\<rbrakk>
   \<Longrightarrow> thread_set f t \<lbrace>domain_sep_inv irqs st\<rbrace>"
  by (wpsimp wp: domain_sep_inv_triv thread_set_cte_wp_at_trivial simp: ran_tcb_cap_cases)

lemmas thread_set_tcb_fault_update_domain_sep_inv[wp]
  = thread_set_domain_sep_inv_triv[where f="tcb_fault_update f" for f, simplified ran_tcb_cap_cases, simplified]
lemmas thread_set_tcb_ipc_buffer_update_domain_sep_inv[wp]
  = thread_set_domain_sep_inv_triv[where f="tcb_ipc_buffer_update f" for f, simplified ran_tcb_cap_cases, simplified]
lemmas thread_set_tcb_fault_handler_update_domain_sep_inv[wp]
  = thread_set_domain_sep_inv_triv[where f="tcb_fault_handler_update f" for f, simplified ran_tcb_cap_cases, simplified]
lemmas thread_set_tcb_mcpriority_update_domain_sep_inv[wp]
  = thread_set_domain_sep_inv_triv[where f="tcb_mcpriority_update f" for f, simplified ran_tcb_cap_cases, simplified]
lemmas thread_set_tcb_priority_update_domain_sep_inv[wp]
  = thread_set_domain_sep_inv_triv[where f="tcb_priority_update f" for f, simplified ran_tcb_cap_cases, simplified]
lemmas thread_set_tcb_time_slice_update_domain_sep_inv[wp]
  = thread_set_domain_sep_inv_triv[where f="tcb_time_slice_update f" for f, simplified ran_tcb_cap_cases, simplified]
lemmas thread_set_tcb_domain_update_domain_sep_inv[wp]
  = thread_set_domain_sep_inv_triv[where f="tcb_domain_update f" for f, simplified ran_tcb_cap_cases, simplified]
lemmas thread_set_tcb_registers_caps_merge_default_tcb_domain_sep_inv[wp]
  = thread_set_domain_sep_inv_triv[where f="tcb_registers_caps_merge tcb" for tcb, simplified ran_tcb_cap_cases tcb_registers_caps_merge_def, simplified]
lemmas thread_set_tcb_flags_update_domain_sep_inv[wp]
  = thread_set_domain_sep_inv_triv[where f="tcb_flags_update f" for f, simplified ran_tcb_cap_cases, simplified]

crunch as_user
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: domain_sep_inv_triv)

lemma get_cap_domain_sep_inv_cap:
  "\<lbrace>domain_sep_inv irqs st\<rbrace> get_cap cap \<lbrace>\<lambda>rv s. domain_sep_inv_cap irqs rv\<rbrace>"
  by (wpsimp wp: get_cap_wp simp: cte_wp_at_domain_sep_inv_cap)

crunch cap_swap_for_delete
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: get_cap_domain_sep_inv_cap dxo_wp_weak simp: crunch_simps ignore: cap_swap_ext)

lemma preemption_point_domain_sep_inv[wp]:
  "preemption_point \<lbrace>domain_sep_inv irqs st\<rbrace>"
  by (wp preemption_point_inv | simp)+


context DomainSepInv_1 begin

crunch cap_delete_one
  for domain_sep_inv[wp]: "\<lambda>s. domain_sep_inv irqs  (st :: 'state_ext state) (s :: det_state)"
  (wp: mapM_x_wp' unless_wp dxo_wp_weak simp: crunch_simps)

lemma reply_cancel_ipc_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   reply_cancel_ipc t
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs  (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (simp add: reply_cancel_ipc_def)
  apply wp
   apply (rule hoare_strengthen_post[OF thread_set_tcb_fault_update_domain_sep_inv])
   apply auto
  done

crunch finalise_cap
  for domain_sep_inv[wp]: "\<lambda>s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)"
  (wp: dxo_wp_weak)

lemma finalise_cap_domain_sep_inv_cap:
  "\<lbrace>\<lambda>s. domain_sep_inv_cap irqs cap\<rbrace>
   finalise_cap cap b
   \<lbrace>\<lambda>rv s :: det_state. domain_sep_inv_cap irqs (fst rv)\<rbrace>"
  including classic_wp_pre
  apply (case_tac cap)
             apply (wp | simp add: o_def split del: if_split  split: cap.splits
                       | fastforce split: if_splits simp: domain_sep_inv_cap_def)+
    apply (rule hoare_pre, wp, fastforce)
   apply (rule hoare_pre, simp, wp, fastforce simp: domain_sep_inv_cap_def)
  apply (wpc | wp arch_finalise_cap_rv | simp)+
  done

lemma finalise_cap_returns_NullCap:
  "\<lbrace>\<lambda>s. domain_sep_inv_cap irqs cap\<rbrace>
   finalise_cap cap b
   \<lbrace>\<lambda>rv s :: det_state. \<not> irqs \<longrightarrow> snd rv = NullCap\<rbrace>"
  apply (case_tac cap)
  by (wpsimp wp: arch_finalise_cap_rv simp: o_def domain_sep_inv_cap_def split_del: if_split)+

lemma rec_del_domain_sep_inv':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
         rec_del.simps[simp del]
  shows
  "s \<turnstile> \<lbrace>domain_sep_inv irqs st\<rbrace>
       rec_del call
       \<lbrace>\<lambda>rv s. (case call of (FinaliseSlotCall x y) \<Rightarrow> (y \<or> fst rv) \<longrightarrow> \<not> irqs \<longrightarrow> snd rv = NullCap
                                                | _ \<Rightarrow> True) \<and>
               domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>,
       \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  proof (induct s arbitrary: rule: rec_del.induct, simp_all only: rec_del_fails hoare_fail_any)
  case (1 slot exposed s) show ?case
    apply (simp add: split_def rec_del.simps)
    apply (wpsimp wp: empty_slot_domain_sep_inv
                      drop_spec_validE[OF returnOk_wp]
                      drop_spec_validE[OF liftE_wp])
    apply (rule spec_strengthen_postE[OF "1.hyps"])
    apply fastforce
    done
  next
  case (2 slot exposed s) show ?case
    apply (simp add: rec_del.simps split del: if_split)
    apply (rule hoare_pre_spec_validE)
     apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
            | simp add: split_def split del: if_split)+
           apply (rule spec_strengthen_postE)
            apply (rule "2.hyps", fastforce+)
          apply (rule drop_spec_validE, (wp preemption_point_inv| simp)+)[1]
         apply simp
         apply (rule spec_strengthen_postE)
          apply (rule "2.hyps", fastforce+)
         apply (wp  finalise_cap_domain_sep_inv_cap get_cap_wp
                   finalise_cap_returns_NullCap
                   drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
               |simp split del: if_split
               |wp (once) hoare_drop_imps)+
    apply (blast dest: cte_wp_at_domain_sep_inv_cap)
    done
  next
  case (3 ptr bits n slot s) show ?case
    apply (simp add: rec_del.simps)
    apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp])
    apply (rule hoare_pre_spec_validE)
    apply (wp drop_spec_validE[OF assertE_wp])
    apply (fastforce)
    done
  next
  case (4 ptr bits n slot s) show ?case
    apply (simp add: rec_del.simps)
    apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
              drop_spec_validE[OF assertE_wp] get_cap_wp | simp)+
    apply (rule spec_strengthen_postE[OF "4.hyps"])
     apply (simp add: returnOk_def return_def)
    apply (clarsimp simp: domain_sep_inv_cap_def)
    done
  qed

lemma rec_del_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   rec_del call
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (rule validE_valid)
  apply (rule use_spec)
  apply (rule spec_strengthen_postE[OF rec_del_domain_sep_inv'])
  by fastforce

crunch cap_delete
  for domain_sep_inv[wp]: "\<lambda>s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)"

lemma cap_revoke_domain_sep_inv':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
  shows
  "s \<turnstile> \<lbrace> domain_sep_inv irqs st\<rbrace>
   cap_revoke slot
   \<lbrace> \<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>, \<lbrace> \<lambda>_. domain_sep_inv irqs st\<rbrace>"
  proof(induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
  apply (subst cap_revoke.simps)
  apply (rule hoare_pre_spec_validE)
   apply (wp "1.hyps")
           apply (wp spec_valid_conj_liftE2 | simp)+
           apply (wp drop_spec_validE[OF valid_validE[OF preemption_point_domain_sep_inv]]
                    drop_spec_validE[OF valid_validE[OF cap_delete_domain_sep_inv]]
                    drop_spec_validE[OF assertE_wp] drop_spec_validE[OF returnOk_wp]
                    drop_spec_validE[OF liftE_wp]
                | simp | wp (once) hoare_drop_imps)+
  done
qed

lemmas cap_revoke_domain_sep_inv[wp] = use_spec(2)[OF cap_revoke_domain_sep_inv']

end


lemma cap_move_cte_wp_at_other:
  "\<lbrace>cte_wp_at P slot and K (slot \<noteq> dest_slot \<and> slot \<noteq> src_slot)\<rbrace>
   cap_move cap src_slot dest_slot
   \<lbrace>\<lambda>_. cte_wp_at P slot\<rbrace>"
  unfolding cap_move_def
  by (wpsimp wp: set_cdt_cte_wp_at set_cap_cte_wp_at' dxo_wp_weak hoare_weak_lift_imp set_original_wp)

lemma cte_wp_at_weak_derived_ReplyCap:
  "cte_wp_at ((=) (ReplyCap x False R)) slot s
   \<Longrightarrow> cte_wp_at (weak_derived (ReplyCap x False R)) slot s"
  apply (erule cte_wp_atE)
   apply (rule cte_wp_at_cteI)
      apply assumption
     apply assumption
    apply assumption
   apply simp
  apply (rule cte_wp_at_tcbI)
  apply auto
  done

crunch possible_switch_to
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"

lemma cancel_badged_sends_domain_sep_inv[wp]:
  "cancel_badged_sends epptr badge \<lbrace>domain_sep_inv irqs st\<rbrace>"
  apply (simp add: cancel_badged_sends_def)
  apply (wpsimp wp: mapM_wp | simp add: filterM_mapM | wp (once) hoare_drop_imps)+
  done

lemma create_cap_domain_sep_inv[wp]:
  "create_cap tp sz p dev slot \<lbrace>domain_sep_inv irqs st\<rbrace>"
  apply (simp add: create_cap_def)
  apply (rule hoare_pre)
  apply (wp set_cap_domain_sep_inv dxo_wp_weak | wpc | simp)+
  apply clarsimp
  apply (case_tac tp, simp_all add: domain_sep_inv_cap_def)
  done

lemma retype_region_neg_cte_wp_at_not_domain_sep_inv_cap:
  "retype_region  base n sz ty dev \<lbrace>\<lambda>s. \<not> cte_wp_at (not domain_sep_inv_cap irqs) slot s\<rbrace>"
  apply (rule hoare_pre)
   apply (simp only: retype_region_def retype_addrs_def foldr_upd_app_if fun_app_def K_bind_def)
   apply (wp dxo_wp_weak | simp)+
  apply clarsimp
  apply (case_tac "fst slot \<in> (\<lambda>p. ptr_add base (p * 2 ^ obj_bits_api ty sz)) ` {0..<n}")
   apply clarsimp
   apply (erule cte_wp_atE)
    apply (clarsimp simp: default_object_def empty_cnode_def
                   split: apiobject_type.splits if_splits)
   apply (clarsimp simp: default_object_def default_tcb_def tcb_cap_cases_def
                  split: apiobject_type.splits if_splits)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_tcbI cte_wp_at_cteI)
  done

lemma retype_region_domain_sep_inv[wp]:
  "retype_region base n sz tp dev \<lbrace>domain_sep_inv irqs st\<rbrace>"
  apply (rule domain_sep_inv_wp[where P="\<top>" and R="\<top>", simplified])
   apply (rule retype_region_neg_cte_wp_at_not_domain_sep_inv_cap)
  apply wp
  done

lemma domain_sep_inv_cap_UntypedCap[simp]:
  "domain_sep_inv_cap irqs (UntypedCap dev base sz n)"
  by (simp add: domain_sep_inv_cap_def)

crunch delete_objects
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: domain_sep_inv_detype_lift)


context DomainSepInv_1 begin

crunch finalise_slot, invoke_untyped, send_signal
  for domain_sep_inv[wp]: "\<lambda>s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)"
  (wp: crunch_wps mapME_x_inv_wp simp: crunch_simps mapM_x_def_bak)

lemma invoke_cnode_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_cnode_inv ci\<rbrace>
   invoke_cnode ci
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  unfolding invoke_cnode_def
  apply (case_tac ci)
        apply (wp cap_insert_domain_sep_inv cap_move_domain_sep_inv | simp split del: if_split)+
     apply (rule hoare_pre)
      apply (wpsimp wp: cap_move_domain_sep_inv cap_move_cte_wp_at_other get_cap_wp,
             blast dest: cte_wp_at_weak_derived_domain_sep_inv_cap)+
   apply (wpsimp wp: cap_move_domain_sep_inv get_cap_wp)
   apply (fastforce dest:  cte_wp_at_weak_derived_ReplyCap)
  apply (wp | simp | wpc | rule hoare_pre)+
  done

end


lemma perform_page_invocation_domain_sep_inv_get_cap_helper:
  "\<lbrace>\<top>\<rbrace> get_cap blah \<lbrace>\<lambda>rv s. domain_sep_inv_cap irqs (ArchObjectCap (F rv))\<rbrace>"
  apply (simp add: domain_sep_inv_cap_def)
  apply (rule wp_post_taut)
  done

lemma set_object_tcb_context_update_neg_cte_wp_at:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at P slot s \<and> obj_at ((=) (TCB tcb)) ptr s\<rbrace>
   set_object ptr (TCB (tcb\<lparr>tcb_arch := arch_tcb_context_set X (arch_tcb tcb)\<rparr>))
   \<lbrace>\<lambda>_ s. \<not> cte_wp_at P slot s\<rbrace>"
  apply (wp set_object_wp)
  apply clarsimp
  apply (case_tac "ptr = fst slot")
   apply (erule cte_wp_atE)
    apply (fastforce simp: obj_at_def)
   apply (erule notE)
   apply (clarsimp simp: obj_at_def)
   apply (rule cte_wp_at_tcbI)
      apply simp
     apply (fastforce)
    apply (fastforce simp: tcb_cap_cases_def split: if_splits)
  apply (fastforce elim: cte_wp_atE intro: cte_wp_at_cteI cte_wp_at_tcbI)
  done

lemma set_object_tcb_arch_update_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and obj_at ((=) (TCB tcb)) ptr\<rbrace>
   set_object ptr (TCB (tcb\<lparr>tcb_arch := arch\<rparr>))
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (wp set_object_wp)
  apply (simp add: domain_sep_inv_def fun_upd_def cte_wp_at_caps_of_state)
  apply (fastforce simp: caps_of_state_after_update obj_at_def tcb_cap_cases_def)
  done

lemma dxo_domain_sep_inv[wp]:
  "do_extended_op eop \<lbrace>domain_sep_inv irqs st\<rbrace>"
  by (simp | wp dxo_wp_weak)+

crunch copy_mrs, set_message_info, set_mrs
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: crunch_wps set_object_tcb_arch_update_domain_sep_inv simp: crunch_simps ignore: set_object)

lemma cap_insert_domain_sep_inv':
  "\<lbrace>domain_sep_inv irqs st and K (domain_sep_inv_cap irqs cap)\<rbrace>
   cap_insert cap slot dest_slot
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (simp add: cap_insert_def)
  apply (wp set_cap_domain_sep_inv get_cap_wp dxo_wp_weak | simp split del: if_split)+
  done

lemma domain_sep_inv_cap_max_free_index_update[simp]:
  "domain_sep_inv_cap irqs (max_free_index_update cap) =
   domain_sep_inv_cap irqs cap"
  by (simp add: max_free_index_def free_index_update_def split: cap.splits)

lemma domain_sep_inv_cap_ArchObjectCap[simp]:
  "domain_sep_inv_cap irqs (ArchObjectCap arch_cap)"
  by (simp add: domain_sep_inv_cap_def)

crunch receive_signal, complete_signal
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"

lemma domain_sep_inv_cap_ReplyCap[simp]:
  "domain_sep_inv_cap irqs (ReplyCap param_a param_b param_c)"
  by (simp add: domain_sep_inv_cap_def)

lemma setup_caller_cap_domain_sep_inv[wp]:
  "\<lbrace>domain_sep_inv irqs st\<rbrace>
   setup_caller_cap a b c
   \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  apply (simp add: setup_caller_cap_def split del:if_split)
  apply (wp cap_insert_domain_sep_inv' | simp)+
  done

lemma transfer_caps_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb
        and (\<lambda> s. (\<forall>x\<in>set caps.
               s \<turnstile> fst x) \<and>
              (\<forall>x\<in>set caps.
               cte_wp_at
                (\<lambda>cp. fst x \<noteq> NullCap \<longrightarrow>
                      cp = fst x)
                (snd x) s \<and>
               real_cte_at (snd x) s))\<rbrace>
  transfer_caps mi caps endpoint receiver receive_buffer
  \<lbrace>\<lambda>_. domain_sep_inv irqs st\<rbrace>"
  unfolding transfer_caps_def
  apply (wpsimp wp: transfer_caps_loop_pres_dest cap_insert_domain_sep_inv
                    hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply (fastforce elim: cte_wp_at_weakenE)
  done


context DomainSepInv_1 begin

lemma do_normal_transfer_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb\<rbrace>
   do_normal_transfer sender send_buffer ep badge grant receiver recv_buffer
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  unfolding do_normal_transfer_def
  by (wp transfer_caps_domain_sep_inv hoare_vcg_ball_lift lec_valid_cap' | simp)+

crunch do_fault_transfer
  for domain_sep_inv[wp]: "\<lambda>s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)"

lemma do_ipc_transfer_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb\<rbrace>
   do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  unfolding do_ipc_transfer_def
  apply (wp do_normal_transfer_domain_sep_inv hoare_vcg_all_lift | wpc | wp (once) hoare_drop_imps)+
  apply clarsimp
  done

lemma send_ipc_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb and
    sym_refs \<circ> state_refs_of\<rbrace>
   send_ipc block call badge can_grant can_grant_reply thread epptr
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  unfolding send_ipc_def
  apply (wp setup_caller_cap_domain_sep_inv hoare_vcg_if_lift | wpc | simp split del:if_split)+
        apply (rule_tac Q'="\<lambda> r s. domain_sep_inv irqs st s" in hoare_strengthen_post)
         apply (wp do_ipc_transfer_domain_sep_inv dxo_wp_weak | wpc | simp)+
     apply (wp (once) hoare_drop_imps)
     apply (wp get_simple_ko_wp)+
  apply clarsimp
  apply (fastforce simp: valid_objs_def valid_obj_def obj_at_def ep_q_refs_of_def
                         a_type_def ep_redux_simps neq_Nil_conv valid_ep_def
                   elim: ep_queued_st_tcb_at split: list.splits)
  done

lemma receive_ipc_base_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb and
    sym_refs \<circ> state_refs_of and ko_at (Endpoint ep) epptr \<rbrace>
   receive_ipc_base aag receiver ep epptr rights is_blocking
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (clarsimp cong: endpoint.case_cong thread_get_def get_thread_state_def)
  apply (wp setup_caller_cap_domain_sep_inv dxo_wp_weak | wpc | simp split del: if_split)+
        apply (rule_tac Q'="\<lambda> r s. domain_sep_inv irqs st s" in hoare_strengthen_post)
         apply (wp do_ipc_transfer_domain_sep_inv hoare_vcg_all_lift | wpc | simp)+
     apply (wpsimp wp: hoare_vcg_imp_lift[OF set_simple_ko_get_tcb, unfolded disj_not1]
                       hoare_vcg_all_lift get_simple_ko_wp
                 simp: a_type_def do_nbrecv_failed_transfer_def)+
  apply (fastforce simp: valid_objs_def valid_obj_def obj_at_def
                         ep_redux_simps neq_Nil_conv valid_ep_def
                  split: list.splits)
  done

lemma receive_ipc_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb and sym_refs \<circ> state_refs_of\<rbrace>
   receive_ipc receiver cap is_blocking
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  unfolding receive_ipc_def
  apply (simp add: receive_ipc_def split: cap.splits, clarsimp)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (rule bind_wp[OF _ gbn_sp])
  apply (case_tac ntfnptr, simp)
   apply (wp receive_ipc_base_domain_sep_inv get_simple_ko_wp | simp split: if_split option.splits)+
  done

lemma send_fault_ipc_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb
                           and sym_refs \<circ> state_refs_of
                           and K (valid_fault fault)\<rbrace>
   send_fault_ipc thread fault
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  unfolding send_fault_ipc_def
  apply (rule hoare_gen_asm)+
  apply (wp send_ipc_domain_sep_inv thread_set_valid_objs thread_set_tcb_fault_update_valid_mdb
            thread_set_refs_trivial thread_set_obj_at_impossible hoare_vcg_ex_lift
         | wpc | simp add: Let_def split_def lookup_cap_def valid_tcb_fault_update)+
     apply (wpe get_cap_inv[where P="domain_sep_inv irqs st and valid_objs and valid_mdb
                                                            and sym_refs o state_refs_of"])
     apply (wp | simp)+
  done

crunch do_reply_transfer, handle_fault, reply_from_kernel, restart
  for domain_sep_inv[wp]: "\<lambda>s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)"
  (wp: crunch_wps handle_arch_fault_reply_domain_sep_inv ignore: thread_set)

end

crunch setup_reply_master
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (wp: crunch_wps simp: crunch_simps)

lemma same_object_as_domain_sep_inv_cap:
  "\<lbrakk> same_object_as a cap; domain_sep_inv_cap irqs cap \<rbrakk>
     \<Longrightarrow> domain_sep_inv_cap irqs a"
  by (case_tac a, simp_all add: same_object_as_def domain_sep_inv_cap_def)

lemma checked_cap_insert_domain_sep_inv:
  "check_cap_at a b (check_cap_at c d (cap_insert a b e)) \<lbrace>domain_sep_inv irqs st\<rbrace>"
  apply (wp get_cap_wp cap_insert_domain_sep_inv' | simp add: check_cap_at_def)+
  apply clarsimp
  apply (drule_tac cap=cap in cte_wp_at_domain_sep_inv_cap)
   apply assumption
  apply (erule (1) same_object_as_domain_sep_inv_cap)
  done

crunch bind_notification, set_mcpriority, set_priority
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (ignore: thread_set)


context DomainSepInv_1 begin

crunch invoke_domain, set_flags
  for domain_sep_inv[wp]: "domain_sep_inv irqs (st :: 'state_ext state) :: det_state \<Rightarrow> _"
  (ignore: thread_set)

lemma invoke_tcb_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and tcb_inv_wf tinv\<rbrace>
   invoke_tcb tinv
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (case_tac tinv)
         apply ((wp restart_domain_sep_inv hoare_vcg_if_lift mapM_x_wp[OF _ subset_refl]
                 | wpc | simp split del: if_split add: check_cap_at_def | clarsimp)+)[3]
      defer
      apply ((wp | simp)+)[2]
    (* just NotificationControl and ThreadControl left *)
    apply (rename_tac option)
    apply (case_tac option)
     apply  ((wp | simp)+)[1]
    apply (simp add: split_def cong: option.case_cong)
    apply (wp checked_cap_insert_domain_sep_inv hoare_vcg_all_liftE_R hoare_vcg_all_lift
              hoare_vcg_const_imp_liftE_R cap_delete_domain_sep_inv cap_delete_deletes
              cap_delete_valid_cap cap_delete_cte_at hoare_weak_lift_imp
           | wpc | strengthen
           | simp add: option_update_thread_def emptyable_def tcb_cap_cases_def
                       tcb_cap_valid_def tcb_at_st_tcb_at)+
  done

end


locale DomainSepInv_2 = DomainSepInv_1 state_ext_t
  for state_ext_t :: "'state_ext :: state_ext itself" +
  assumes arch_perform_invocation_domain_sep_inv[wp]:
    "\<lbrace>domain_sep_inv irqs st and valid_arch_inv ai\<rbrace>
     arch_perform_invocation ai
     \<lbrace>\<lambda>_ s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and arch_invoke_irq_handler_domain_sep_inv[wp]:
    "arch_invoke_irq_handler ihi \<lbrace>\<lambda>s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and arch_invoke_irq_control_domain_sep_inv:
    "\<lbrace>domain_sep_inv irqs st and arch_irq_control_inv_valid ivk\<rbrace>
     arch_invoke_irq_control ivk
     \<lbrace>\<lambda>_ s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and handle_hypervisor_fault_domain_sep_inv[wp]:
    "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb and sym_refs \<circ> state_refs_of\<rbrace>
     handle_hypervisor_fault t hf_t
     \<lbrace>\<lambda>_ s :: det_state. domain_sep_inv irqs st s\<rbrace>"
  and handle_reserved_irq_domain_sep_inv[wp]:
    "\<lbrace>domain_sep_inv irqs st and valid_objs and valid_mdb and sym_refs \<circ> state_refs_of\<rbrace>
     handle_reserved_irq irq
     \<lbrace>\<lambda>_ s :: det_state. domain_sep_inv irqs (st :: 'state_ext state) s\<rbrace>"
  and handle_spurious_irq_domain_sep_inv[wp]:
    "handle_spurious_irq \<lbrace>domain_sep_inv irqs st :: det_state \<Rightarrow> _\<rbrace>"
begin

(* when i is AckIRQ the preconditions here contradict each other, which
   is why this lemma is true *)
lemma invoke_irq_handler_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and irq_handler_inv_valid i\<rbrace>
   invoke_irq_handler i
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (case_tac i)
    apply (wp cap_insert_domain_sep_inv' | simp)+
   apply (rename_tac irq cap cslot_ptr s)
   apply (case_tac cap, simp_all add: domain_sep_inv_cap_def)[1]
  apply (wp | clarsimp)+
  done

(* similarly, the preconditions here tend to contradict one another *)
lemma invoke_control_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and irq_control_inv_valid i\<rbrace>
    invoke_irq_control i
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  including classic_wp_pre
  apply (case_tac i)
   apply (case_tac irqs)
    apply (wp cap_insert_domain_sep_inv' | simp )+
    apply (simp add: set_irq_state_def, wp, simp)
    apply (fastforce simp: domain_sep_inv_def domain_sep_inv_cap_def)
   apply (fastforce simp: valid_def domain_sep_inv_def)
  apply simp
  apply (wp arch_invoke_irq_control_domain_sep_inv)
  done

lemma derive_cap_domain_sep_inv_cap:
  "\<lbrace>\<lambda>s. domain_sep_inv_cap irqs cap\<rbrace>
   derive_cap slot cap
   \<lbrace>\<lambda>rv s :: det_state. domain_sep_inv_cap irqs rv\<rbrace>,-"
  apply (simp add: derive_cap_def)
  apply (rule hoare_pre)
  apply (wp | wpc | simp add: )+
  apply auto
  done

lemma perform_invocation_domain_sep_inv':
  "\<lbrace>domain_sep_inv irqs st and valid_invocation iv and valid_objs
                           and valid_mdb and sym_refs \<circ> state_refs_of\<rbrace>
   perform_invocation block call iv
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (case_tac iv)
           apply (wp send_ipc_domain_sep_inv invoke_tcb_domain_sep_inv
                     invoke_cnode_domain_sep_inv invoke_control_domain_sep_inv
                     invoke_irq_handler_domain_sep_inv arch_perform_invocation_domain_sep_inv
                  | simp add: split_def | blast)+
  done

lemma perform_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and valid_invocation iv and invs\<rbrace>
   perform_invocation block call iv
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (rule hoare_weaken_pre[OF perform_invocation_domain_sep_inv'])
  apply auto
  done

lemma handle_invocation_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs and ct_active\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (simp add: handle_invocation_def ts_Restart_case_helper
                   split_def liftE_liftM_liftME liftME_def bindE_assoc)
  apply (wp syscall_valid perform_invocation_domain_sep_inv set_thread_state_runnable_valid_sched
         | simp split del: if_split)+
        apply (rule_tac E'="\<lambda>ft. domain_sep_inv irqs st and valid_objs and sym_refs \<circ> state_refs_of
                                                        and valid_mdb and (\<lambda>y. valid_fault ft)"
                    and Q="Q" and Q'=Q for Q
                     in hoare_strengthen_postE)
         apply (wp | simp | clarsimp)+
      apply (rule_tac E'="\<lambda>ft. domain_sep_inv irqs st and valid_objs and sym_refs \<circ> state_refs_of and
                               valid_mdb and (\<lambda>y. valid_fault (CapFault x False ft))"
                  and Q="Q" and Q'=Q for Q
                   in hoare_strengthen_postE)
        apply (wp lcs_ex_cap_to2 | clarsimp)+
  apply (auto intro: st_tcb_ex_cap simp: ct_in_state_def)
  done

lemma handle_send_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs and ct_active\<rbrace>
   handle_send a
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (simp add: handle_send_def)
  apply (wp handle_invocation_domain_sep_inv)
  done

lemma handle_call_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs and ct_active\<rbrace>
   handle_call
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (simp add: handle_call_def)
  apply (wp handle_invocation_domain_sep_inv)
  done

lemma handle_reply_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs\<rbrace>
   handle_reply
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (simp add: handle_reply_def)
  apply (wp get_cap_wp | wpc)+
  apply auto
  done

crunch delete_caller_cap
  for domain_sep_inv[wp]: "\<lambda>s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)"

end


(* FIXME: clagged from Syscall_AC *)
lemma lookup_slot_for_thread_cap_fault:
  "\<lbrace>invs\<rbrace> lookup_slot_for_thread t s -, \<lbrace>\<lambda>f s. valid_fault (CapFault x y f)\<rbrace>"
  apply (simp add: lookup_slot_for_thread_def)
  apply (wp resolve_address_bits_valid_fault2)
  apply clarsimp
  apply (erule (1) invs_valid_tcb_ctable)
  done

lemma domain_sep_inv_cur_thread_update[simp]:
  "domain_sep_inv irqs st (s\<lparr>cur_thread := X\<rparr>) = domain_sep_inv irqs st s"
  apply (simp add: domain_sep_inv_def)
  done

lemma (in is_extended') domain_sep_inv[wp]: "I (domain_sep_inv irqs st)" by (rule lift_inv, simp)


context DomainSepInv_2 begin

lemma handle_recv_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs\<rbrace>
   handle_recv is_blocking
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (simp add: handle_recv_def Let_def lookup_cap_def split_def)
  apply (wp hoare_vcg_all_lift lookup_slot_for_thread_cap_fault receive_ipc_domain_sep_inv
            delete_caller_cap_domain_sep_inv get_cap_wp get_simple_ko_wp
         | wpc | simp
         | (rule_tac Q'="\<lambda>rv. invs and (\<lambda>s. cur_thread s = thread)" in hoare_strengthen_post, wp,
            clarsimp simp: invs_valid_objs invs_sym_refs))+
     apply (rule_tac Q'="\<lambda>r s. domain_sep_inv irqs st s \<and> invs s \<and>
                               tcb_at thread s \<and> thread = cur_thread s" in hoare_strengthen_postE_R)
      apply wp
     apply ((clarsimp simp add: invs_valid_objs invs_sym_refs
             | intro impI allI conjI
             | rule cte_wp_valid_cap caps_of_state_cteD
             | fastforce simp:  valid_fault_def)+)[1]
    apply (wp delete_caller_cap_domain_sep_inv | simp add: split_def cong: conj_cong)+
    apply (wp | simp add: invs_valid_objs invs_mdb invs_sym_refs tcb_at_invs)+
  done

crunch handle_interrupt, activate_thread, choose_thread, handle_yield
  for domain_sep_inv[wp]: "\<lambda>s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)"
  (wp: crunch_wps ignore: thread_set)

lemma handle_event_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   handle_event ev
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) (s :: det_state)\<rbrace>"
  apply (case_tac ev)
  by (wpsimp wp: handle_send_domain_sep_inv handle_call_domain_sep_inv
                 handle_recv_domain_sep_inv handle_reply_domain_sep_inv
      | strengthen invs_valid_objs invs_mdb invs_sym_refs
      | simp add: valid_fault_def maybe_handle_interrupt_def
      | wp hoare_drop_imps)+

crunch next_domain
  for domain_sep_inv[wp]: "domain_sep_inv irqs st"
  (simp: crunch_simps)

lemma schedule_domain_sep_inv:
  "(schedule :: (unit,det_ext) s_monad) \<lbrace>domain_sep_inv irqs (st :: 'state_ext state)\<rbrace>"
  unfolding schedule_def
  by (wp add: guarded_switch_to_lift hoare_drop_imps
      | wpc | clarsimp simp: get_thread_state_def thread_get_def trans_state_update'[symmetric]
                             schedule_choose_new_thread_def)+

lemma call_kernel_domain_sep_inv:
  "\<lbrace>domain_sep_inv irqs st and invs and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   call_kernel ev :: (unit,det_ext) s_monad
   \<lbrace>\<lambda>_ s. domain_sep_inv irqs (st :: 'state_ext state) s\<rbrace>"
  unfolding call_kernel_def maybe_handle_interrupt_def
  by (wpsimp wp: handle_event_domain_sep_inv schedule_domain_sep_inv
              simp: if_fun_split
      | strengthen invs_valid_objs invs_mdb invs_sym_refs
      | wp hoare_drop_imps)+

end

end
