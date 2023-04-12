(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchCNode_IF
imports CNode_IF
begin

context Arch begin global_naming RISCV64

named_theorems CNode_IF_assms

lemma set_object_globals_equiv:
  "\<lbrace>globals_equiv s and (\<lambda>s. ptr \<noteq> riscv_global_pt (arch_state s)) and
    (\<lambda>t. ptr = idle_thread t
         \<longrightarrow> (\<forall>tcb. kheap t (idle_thread t) = Some (TCB tcb)
                    \<longrightarrow> (\<exists>tcb'. obj = (TCB tcb')
                              \<and> arch_tcb_context_get (tcb_arch tcb) = arch_tcb_context_get (tcb_arch tcb'))) \<and>
             (\<forall>tcb'. obj = (TCB tcb') \<longrightarrow> tcb_at (idle_thread t) t))\<rbrace>
   set_object True ptr obj
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (case_tac "ptr = idle_thread sa")
   apply (clarsimp simp: globals_equiv_def idle_equiv_def tcb_at_def2)
   apply (intro impI conjI allI notI iffI | clarsimp)+
  apply (clarsimp simp: globals_equiv_def idle_equiv_def tcb_at_def2)
  done

lemma set_object_globals_equiv'':
  "\<lbrace>globals_equiv s and (\<lambda> s. ptr \<noteq> riscv_global_pt (arch_state s)) and (\<lambda>t. ptr \<noteq> idle_thread t)\<rbrace>
   set_object True ptr obj
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  by (wpsimp wp: set_object_globals_equiv)

lemma set_cap_globals_equiv':
  "\<lbrace>globals_equiv s and (\<lambda> s. fst p \<noteq> riscv_global_pt (arch_state s))\<rbrace>
   set_cap cap p
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_cap_def
  apply (simp only: split_def)
  apply (wp set_object_globals_equiv hoare_vcg_all_lift get_object_wp | wpc | simp)+
  apply (fastforce simp: obj_at_def is_tcb_def)
  done

lemma set_cap_globals_equiv[CNode_IF_assms]:
  "\<lbrace>globals_equiv s and valid_global_objs and valid_arch_state\<rbrace>
   set_cap cap p
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_cap_def
  apply (simp only: split_def)
  apply (wp set_object_globals_equiv hoare_vcg_all_lift get_object_wp | wpc | simp)+
  apply (fastforce simp: is_tcb_def obj_at_def valid_arch_state_def
                   dest: valid_global_arch_objs_pt_at)
  done

definition irq_at :: "nat \<Rightarrow> (irq \<Rightarrow> bool) \<Rightarrow> irq option" where
  "irq_at pos masks \<equiv> let i = irq_oracle pos in (if i = 0x3F \<or> masks i then None else Some i)"

lemma dmo_getActiveIRQ_wp[CNode_IF_assms]:
  "\<lbrace>\<lambda>s. P (irq_at (irq_state (machine_state s) + 1) (irq_masks (machine_state s)))
          (s\<lparr>machine_state := (machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>)\<rparr>)\<rbrace>
   do_machine_op (getActiveIRQ in_kernel)
   \<lbrace>P\<rbrace>"
  apply (simp add: do_machine_op_def getActiveIRQ_def non_kernel_IRQs_def)
  apply (wp modify_wp | wpc)+
  apply clarsimp
  apply (erule use_valid)
   apply (wp modify_wp)
  apply (auto simp: irq_at_def Let_def split: if_splits)
  done

lemma arch_globals_equiv_irq_state_update[CNode_IF_assms, simp]:
  "arch_globals_equiv ct it kh kh' as as' ms (irq_state_update f ms') =
   arch_globals_equiv ct it kh kh' as as' ms ms'"
  "arch_globals_equiv ct it kh kh' as as' (irq_state_update f ms) ms' =
   arch_globals_equiv ct it kh kh' as as' ms ms'"
  by auto

end


requalify_consts RISCV64.irq_at

global_interpretation CNode_IF_1?: CNode_IF_1 _ irq_at
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact CNode_IF_assms)?)
qed


context Arch begin global_naming RISCV64

lemma is_irq_at_triv[CNode_IF_assms]:
  assumes a: "\<And>P. \<lbrace>(\<lambda>s. P (irq_masks (machine_state s))) and Q\<rbrace>
                   f
                   \<lbrace>\<lambda>rv s. P (irq_masks (machine_state s))\<rbrace>"
  shows "\<lbrace>(\<lambda>s. P (is_irq_at s)) and Q\<rbrace> f \<lbrace>\<lambda>rv s. P (is_irq_at s)\<rbrace>"
  apply (clarsimp simp: valid_def is_irq_at_def irq_at_def Let_def)
  apply (erule use_valid[OF _ a])
  apply simp
  done

lemma is_irq_at_not_masked[CNode_IF_assms]:
  "is_irq_at s irq pos \<Longrightarrow> \<not> irq_masks (machine_state s) irq"
  by (clarsimp simp: is_irq_at_def irq_at_def split: option.splits simp: Let_def split: if_splits)

end


global_interpretation CNode_IF_2?: CNode_IF_2 irq_at
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact CNode_IF_assms)?)
qed


context Arch begin global_naming RISCV64

lemma dmo_getActiveIRQ_reads_respects[CNode_IF_assms]:
  notes gets_ev[wp del]
  shows "reads_respects aag l (invs and only_timer_irq_inv irq st)
                       (do_machine_op (getActiveIRQ in_kernel))"
  apply (rule use_spec_ev)
  apply (rule do_machine_op_spec_reads_respects')
   apply (simp add: getActiveIRQ_def)
   apply (wp irq_state_increment_reads_respects_memory irq_state_increment_reads_respects_device
             gets_ev[where f="irq_oracle \<circ> irq_state"] equiv_valid_inv_conj_lift
             gets_irq_masks_equiv_valid modify_wp
          | simp add: no_irq_def)+
  apply (rule only_timer_irq_inv_determines_irq_masks, blast+)
  done

end


global_interpretation CNode_IF_3?: CNode_IF_3 irq_at
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact CNode_IF_assms)?)
qed

end
