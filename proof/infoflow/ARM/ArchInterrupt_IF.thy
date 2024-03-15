(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterrupt_IF
imports Interrupt_IF
begin

context Arch begin global_naming ARM

named_theorems Interrupt_IF_assms

lemma dmo_deactivateInterrupt_reads_respects:
  "config_ARM_GIC_V3 \<Longrightarrow> reads_respects aag l \<top> (do_machine_op (deactivateInterrupt irq))"
  unfolding deactivateInterrupt_def
  by (simp add: dmo_maskInterrupt_reads_respects)

lemma arch_invoke_irq_handler_reads_respects[Interrupt_IF_assms, wp]:
  "reads_respects_f aag l (silc_inv aag st) (arch_invoke_irq_handler irq)"
  apply (cases irq; wpsimp)
  apply (rule conjI; clarsimp)
   apply (erule reads_respects_f[OF dmo_deactivateInterrupt_reads_respects, where Q=\<top>, simplified])
   apply (wpsimp simp: deactivateInterrupt_def)
  apply (rule reads_respects_f[OF dmo_maskInterrupt_reads_respects, where Q=\<top>, simplified])
  apply wpsimp
  done

lemma arch_invoke_irq_control_reads_respects[Interrupt_IF_assms]:
  "reads_respects aag (l :: 'a subject_label) (K (arch_authorised_irq_ctl_inv aag i))
                  (arch_invoke_irq_control i)"
  apply (cases i; simp add: setIRQTrigger_def)
   apply (wp cap_insert_reads_respects set_irq_state_reads_respects dmo_mol_reads_respects | simp)+
   apply (clarsimp simp: arch_authorised_irq_ctl_inv_def)
  apply (rule pre_ev, wp cap_insert_reads_respects)
  apply (clarsimp simp: arch_authorised_irq_ctl_inv_def)
  done

lemma arch_invoke_irq_control_globals_equiv[Interrupt_IF_assms]:
  "\<lbrace>globals_equiv st and valid_arch_state and valid_global_objs\<rbrace>
   arch_invoke_irq_control ai
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (induct ai;
         wpsimp wp: set_irq_state_globals_equiv set_irq_state_valid_global_objs
                    cap_insert_globals_equiv'' dmo_mol_globals_equiv
               simp: setIRQTrigger_def)
  done

lemma arch_invoke_irq_handler_globals_equiv[Interrupt_IF_assms, wp]:
  "arch_invoke_irq_handler irq \<lbrace>globals_equiv st\<rbrace>"
  by (cases irq;
      wpsimp wp: dmo_no_mem_globals_equiv simp: maskInterrupt_def deactivateInterrupt_def)

end


global_interpretation Interrupt_IF_1?: Interrupt_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Interrupt_IF_assms)?)
qed

end
