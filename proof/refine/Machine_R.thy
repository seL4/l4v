(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Properties of machine operations - generic interface.
*)

theory Machine_R
imports ArchBits_R
begin

definition irq_state_independent_H :: "(kernel_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "irq_state_independent_H P \<equiv>
     \<forall>f s. P s \<longrightarrow> P (s\<lparr>ksMachineState :=
                         ksMachineState s\<lparr>irq_state := f (irq_state (ksMachineState s))\<rparr>\<rparr>)"

lemma irq_state_independent_HI[intro!, simp]:
  "\<lbrakk>\<And>s f. P (s\<lparr>ksMachineState :=
                 ksMachineState s\<lparr>irq_state := f (irq_state (ksMachineState s))\<rparr>\<rparr>) = P s\<rbrakk>
   \<Longrightarrow> irq_state_independent_H P"
  by (simp add: irq_state_independent_H_def)

end
