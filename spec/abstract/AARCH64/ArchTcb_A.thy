(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>Architecture-specific TCB functions\<close>

theory ArchTcb_A
imports KHeap_A
begin

context Arch begin arch_global_naming (A)

definition sanitise_register :: "bool \<Rightarrow> register \<Rightarrow> machine_word \<Rightarrow> machine_word" where
  "sanitise_register b r v \<equiv> case r of
     SPSR_EL1 \<Rightarrow> if b \<and> v && 0x1f \<in> {0,4,5} then v else v && 0xf0000000 || 0x140
   | _ \<Rightarrow> v"

definition arch_get_sanitise_register_info :: "obj_ref \<Rightarrow> (bool, 'a::state_ext) s_monad" where
  "arch_get_sanitise_register_info t \<equiv> do
     vcpu \<leftarrow> arch_thread_get tcb_vcpu t;
     return (vcpu \<noteq> None)
   od"

definition arch_post_modify_registers :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'a::state_ext) s_monad" where
  "arch_post_modify_registers cur t \<equiv> return ()"

end
end
