(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "Architecture-specific TCB functions"

theory ArchTcb_A
imports "../KHeap_A"
begin

context Arch begin global_naming RISCV64_A

definition arch_tcb_set_ipc_buffer :: "machine_word \<Rightarrow> vspace_ref \<Rightarrow> (unit, 'a::state_ext) s_monad"
  where
  "arch_tcb_set_ipc_buffer target ptr \<equiv> as_user target $ setRegister TP ptr"

declare arch_tcb_set_ipc_buffer_def [simp]

definition sanitise_register :: "bool \<Rightarrow> register \<Rightarrow> machine_word \<Rightarrow> machine_word"
  where
  "sanitise_register t r v \<equiv> v"

definition arch_get_sanitise_register_info :: "obj_ref \<Rightarrow> (bool, 'a::state_ext) s_monad"
  where
  "arch_get_sanitise_register_info t \<equiv> return False"

definition arch_post_modify_registers :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'a::state_ext) s_monad"
  where
  "arch_post_modify_registers cur t \<equiv> return ()"

end
end
