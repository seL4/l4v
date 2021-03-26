(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Properties of machine operations.
*)

theory Machine_R
imports Bits_R
begin

definition "irq_state_independent_H (P :: kernel_state \<Rightarrow> bool)\<equiv>
              \<forall>(f :: nat \<Rightarrow> nat) (s :: kernel_state). P s \<longrightarrow> P (s\<lparr>ksMachineState := ksMachineState s
                                \<lparr>irq_state := f (irq_state (ksMachineState s))\<rparr>\<rparr>)"

lemma irq_state_independent_HI[intro!, simp]:
  "\<lbrakk>\<And>s f. P (s\<lparr>ksMachineState := ksMachineState s
              \<lparr>irq_state := f (irq_state (ksMachineState s))\<rparr>\<rparr>) = P s\<rbrakk>
   \<Longrightarrow> irq_state_independent_H P"
  by (simp add: irq_state_independent_H_def)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma dmo_getirq_inv[wp]:
  "irq_state_independent_H P \<Longrightarrow> \<lbrace>P\<rbrace> doMachineOp (getActiveIRQ in_kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: getActiveIRQ_def doMachineOp_def split_def exec_gets
                   select_f_select[simplified liftM_def]
                   select_modify_comm gets_machine_state_modify)
  apply wp
  apply (clarsimp simp: irq_state_independent_H_def in_monad return_def split: if_splits)
  done

lemma getActiveIRQ_masked:
  "\<lbrace>\<lambda>s. valid_irq_masks' table (irq_masks s)\<rbrace> getActiveIRQ in_kernel
  \<lbrace>\<lambda>rv s. \<forall>irq. rv = Some irq \<longrightarrow> table irq \<noteq> IRQInactive\<rbrace>"
  apply (simp add: getActiveIRQ_def)
  apply wp
  apply (clarsimp simp: valid_irq_masks'_def)
  done

lemma dmo_maskInterrupt:
  "\<lbrace>\<lambda>s. P (ksMachineState_update (irq_masks_update (\<lambda>t. t (irq := m))) s)\<rbrace>
  doMachineOp (maskInterrupt m irq) \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: maskInterrupt_def in_monad)
  apply (erule rsubst [where P=P])
  apply simp
  done

lemma dmo_maskInterrupt_True:
  "\<lbrace>invs'\<rbrace> doMachineOp (maskInterrupt True irq) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: invs'_def valid_state'_def valid_dom_schedule'_def)
  apply (simp add: valid_irq_masks'_def valid_machine_state'_def
                   ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma setIRQState_irq_states':
  "\<lbrace>valid_irq_states'\<rbrace>
      setIRQState state irq
   \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  apply (simp add: setIRQState_def setInterruptState_def getInterruptState_def)
  apply (wp dmo_maskInterrupt)
  apply (simp add: valid_irq_masks'_def)
  done

lemma getActiveIRQ_le_maxIRQ:
  "\<lbrace>irqs_masked' and valid_irq_states'\<rbrace> doMachineOp (getActiveIRQ in_kernel) \<lbrace>\<lambda>rv s. \<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (drule use_valid, rule getActiveIRQ_le_maxIRQ')
   prefer 2
   apply simp
  apply (simp add: irqs_masked'_def valid_irq_states'_def)
  done

(* FIXME: follows already from getActiveIRQ_le_maxIRQ *)
lemma getActiveIRQ_neq_Some0xFF:
  "\<lbrace>\<top>\<rbrace> doMachineOp (getActiveIRQ in_kernel) \<lbrace>\<lambda>rv s. rv \<noteq> Some 0x3FF\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  apply (drule use_valid, rule getActiveIRQ_neq_Some0xFF')
   apply auto
  done

end
end
