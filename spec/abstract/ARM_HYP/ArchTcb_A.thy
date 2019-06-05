(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
Arch-specific functions for the abstract model of CSpace.
*)

chapter "Architecture-specific TCB functions"

theory ArchTcb_A
imports "../KHeap_A"
begin

context Arch begin global_naming ARM_A

definition
  arch_tcb_set_ipc_buffer :: "machine_word \<Rightarrow> vspace_ref \<Rightarrow> (unit, 'a::state_ext) s_monad"
where
  "arch_tcb_set_ipc_buffer target ptr \<equiv> as_user target $ setRegister TPIDRURW ptr"

(* Allow most pre-existing proofs to continue to work. *)
declare arch_tcb_set_ipc_buffer_def [simp]

definition
  sanitise_register :: "bool \<Rightarrow> register \<Rightarrow> machine_word \<Rightarrow> machine_word"
where
  "sanitise_register t r v \<equiv> case r of
      CPSR \<Rightarrow>
       if t \<and>
          v && 0x1f \<in> {0x10, 0x11, 0x12, 0x13, 0x17, 0x1b, 0x1f}
            \<comment> \<open>@{text \<open>PMODE_(USER/FIQ/IRQ/SUPERVISOR/ABORT/UNDEFINED/SYSTEM)\<close>}\<close>
       then v
       else (v && 0xf8000000) || 0x150
    | _    \<Rightarrow> v"

definition
  arch_get_sanitise_register_info :: "obj_ref \<Rightarrow> (bool, 'a::state_ext) s_monad"
where
  "arch_get_sanitise_register_info t \<equiv> do
          vcpu \<leftarrow> arch_thread_get tcb_vcpu t;
          return (vcpu \<noteq> None)
   od"

definition
  arch_post_modify_registers :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'a::state_ext) s_monad"
where
  "arch_post_modify_registers cur t \<equiv> return ()"

end
end
