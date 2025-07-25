(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterrupt_AC
imports
  Interrupt_AC
begin

context Arch begin arch_global_naming

named_theorems Interrupt_AC_assms

definition arch_authorised_irq_ctl_inv ::
  "'a PAS \<Rightarrow> Invocations_A.arch_irq_control_invocation \<Rightarrow> bool" where
  "arch_authorised_irq_ctl_inv aag cinv \<equiv>
     case cinv of
       ARMIRQControlInvocation irq x1 x2 trigger \<Rightarrow>
         is_subject aag (fst x1) \<and> is_subject aag (fst x2) \<and>
         (pasSubject aag, Control, pasIRQAbs aag irq) \<in> pasPolicy aag
     | IssueSGISignal irq argets x1 x2 \<Rightarrow>
        is_subject aag (fst x1) \<and> is_subject aag (fst x2)"

lemma arch_invoke_irq_control_pas_refined[Interrupt_AC_assms]:
  "\<lbrace>pas_refined aag and valid_mdb and arch_irq_control_inv_valid irq_ctl_inv
                    and K (arch_authorised_irq_ctl_inv aag irq_ctl_inv)\<rbrace>
   arch_invoke_irq_control irq_ctl_inv
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (cases irq_ctl_inv;
         wpsimp wp: cap_insert_pas_refined_not_transferable
                simp: cte_wp_at_caps_of_state clas_no_asid cap_links_irq_def
                      arch_authorised_irq_ctl_inv_def aag_cap_auth_def
                      arch_irq_control_inv_valid_def)
  done

lemma arch_invoke_irq_handler_pas_refined[Interrupt_AC_assms]:
  "\<lbrace>pas_refined aag and invs and (\<lambda>s. interrupt_states s x1 \<noteq> IRQInactive)\<rbrace>
   arch_invoke_irq_handler (ACKIrq x1)
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  by (wpsimp split_del: if_split)

lemma arch_invoke_irq_control_respects[Interrupt_AC_assms]:
  "\<lbrace>integrity aag X st and pas_refined aag and K (arch_authorised_irq_ctl_inv aag acinv)\<rbrace>
   arch_invoke_irq_control acinv
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (case_tac acinv;
         wpsimp wp: cap_insert_integrity_autarch aag_Control_into_owns_irq
                    dmo_mol_respects do_machine_op_pas_refined
                simp: setIRQTrigger_def arch_authorised_irq_ctl_inv_def)
  done

lemma integrity_irq_masks[iff]:
  "integrity aag X st (s\<lparr>machine_state := machine_state s \<lparr>irq_masks := v\<rparr>\<rparr>) =
   integrity aag X st s"
  by (simp add: integrity_def integrity_arch_kh_upds)

lemma arch_invoke_irq_handler_respects[Interrupt_AC_assms]:
  "\<lbrace>integrity aag X st and pas_refined aag and einvs\<rbrace>
   arch_invoke_irq_handler (ACKIrq x1)
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp: deactivateInterrupt_def maskInterrupt_def
               wp: dmo_wp mol_respects split_del: if_split)

declare arch_check_irq_inv[Interrupt_AC_assms]

end


arch_requalify_consts arch_authorised_irq_ctl_inv

global_interpretation Interrupt_AC_1?: Interrupt_AC_1 "arch_authorised_irq_ctl_inv"
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Interrupt_AC_assms)?)
qed


context Arch begin arch_global_naming

lemma arch_decode_irq_control_invocation_authorised[Interrupt_AC_assms]:
  "\<lbrace>pas_refined aag and
    K (is_subject aag (fst slot) \<and> (\<forall>cap \<in> set caps. pas_cap_cur_auth aag cap) \<and>
       (args \<noteq> [] \<longrightarrow> (pasSubject aag, Control, pasIRQAbs aag (ucast (args ! 0))) \<in> pasPolicy aag))\<rbrace>
   arch_decode_irq_control_invocation info_label args slot caps
   \<lbrace>\<lambda>x _. arch_authorised_irq_ctl_inv aag x\<rbrace>, -"
  unfolding decode_irq_control_invocation_def arch_decode_irq_control_invocation_def Let_def
            authorised_irq_ctl_inv_def arch_authorised_irq_ctl_inv_def arch_check_irq_def
  apply (rule hoare_gen_asmE)
  apply (wpsimp wp: weak_if_wp)
  apply (cases args, simp_all)
  apply (cases caps, simp_all)
  apply (auto simp: is_cap_simps cap_auth_conferred_def
                    pas_refined_wellformed
                    pas_refined_all_auth_is_owns aag_cap_auth_def)
  done

end


global_interpretation Interrupt_AC_2?: Interrupt_AC_2 "arch_authorised_irq_ctl_inv"
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Interrupt_AC_assms)?)
qed


end
