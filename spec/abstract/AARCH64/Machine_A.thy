(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "AARCH64 Machine Instantiation"

theory Machine_A
imports
  "ExecSpec.MachineOps"
begin

context Arch begin arch_global_naming (A)

text \<open>
  The specification is written with abstract type names for object references, user pointers,
  word-based data, cap references, and so on. This theory provides an instantiation of these names
  to concrete types for the AARCH64 architecture. Other architectures may have slightly different
  instantiations.
\<close>

type_synonym obj_ref         = machine_word
type_synonym vspace_ref      = machine_word

type_synonym data            = machine_word
type_synonym cap_ref         = "bool list"
type_synonym length_type     = machine_word

type_synonym asid_low_len    = 9
type_synonym asid_low_index  = "asid_low_len word"

type_synonym asid_high_len   = 7
type_synonym asid_high_index = "asid_high_len word"

type_synonym asid_len        = 16
type_synonym asid_rep_len    = asid_len
type_synonym asid            = "asid_rep_len word"

type_synonym vmid            = "8 word"


text \<open>
  With the definitions above, most conversions between abstract type names boil down to just
  the identity function, some convert from @{text word} to @{typ nat} and others between different
  word sizes using @{const ucast}.
\<close>

definition oref_to_data :: "obj_ref \<Rightarrow> data" where
  "oref_to_data \<equiv> id"

definition data_to_oref :: "data \<Rightarrow> obj_ref" where
  "data_to_oref \<equiv> id"

definition vref_to_data :: "vspace_ref \<Rightarrow> data" where
  "vref_to_data \<equiv> id"

definition data_to_vref :: "data \<Rightarrow> vspace_ref" where
  "data_to_vref \<equiv> id"

definition nat_to_len :: "nat \<Rightarrow> length_type" where
  "nat_to_len \<equiv> of_nat"

definition data_to_nat :: "data \<Rightarrow> nat" where
  "data_to_nat \<equiv> unat"

definition data_to_16 :: "data \<Rightarrow> 16 word" where
  "data_to_16 \<equiv> ucast"

definition data_to_cptr :: "data \<Rightarrow> cap_ref" where
  "data_to_cptr \<equiv> to_bl"

definition combine_ntfn_badges :: "data \<Rightarrow> data \<Rightarrow> data" where
  "combine_ntfn_badges \<equiv> semiring_bit_operations_class.or"

definition combine_ntfn_msgs :: "data \<Rightarrow> data \<Rightarrow> data" where
  "combine_ntfn_msgs \<equiv> semiring_bit_operations_class.or"


text \<open>These definitions will be unfolded automatically in proofs.\<close>
lemmas data_convs [simp] =
  oref_to_data_def data_to_oref_def vref_to_data_def data_to_vref_def
  nat_to_len_def data_to_nat_def data_to_16_def data_to_cptr_def


text \<open>
  The following definitions provide architecture-dependent sizes such as the standard page
  size and capability size of the underlying machine.
\<close>

definition slot_bits :: nat where
  "slot_bits \<equiv> 5"

definition msg_label_bits :: nat where
  [simp]: "msg_label_bits \<equiv> 52"

definition new_context :: "user_context" where
  "new_context \<equiv> UserContext (FPUState (\<lambda>_. 0) 0 0) ((\<lambda>_. 0) (SPSR_EL1 := pstateUser))"

text \<open>
  The lowest virtual address in the kernel window. The kernel reserves the virtual addresses
  from here up in every virtual address space.
\<close>
definition pptr_base :: "machine_word" where
  "pptr_base = Platform.AARCH64.pptrBase"

text "Virtual address space available to users."
definition user_vtop :: "machine_word" where
  "user_vtop = Platform.AARCH64.pptrUserTop"

text \<open>
  Virtual address for start of kernel device mapping region in highest 1GiB of memory.
\<close>
definition kdev_base :: "machine_word" where
  "kdev_base = Platform.AARCH64.kdevBase"

text \<open>
  The virtual address the kernel code is mapped.
\<close>
definition kernel_elf_base :: "vspace_ref" where
  "kernel_elf_base \<equiv> Platform.AARCH64.kernelELFBase"

text \<open>
  Currently an arbitrary aligned address for the idle thread.
  Only has to exist, does not have to match up with the concrete value in C.
\<close>
definition idle_thread_ptr :: vspace_ref where
  "idle_thread_ptr = pptr_base + 0x1000"

(* FIXME: nat_to_cref is not arch specific *)
definition nat_to_cref :: "nat \<Rightarrow> nat \<Rightarrow> cap_ref" where
  "nat_to_cref len n \<equiv> drop (word_bits - len) (to_bl (of_nat n :: machine_word))"

definition msg_info_register :: register where
  "msg_info_register \<equiv> msgInfoRegister"

definition msg_registers :: "register list" where
  "msg_registers \<equiv> msgRegisters"

definition cap_register :: register where
  "cap_register \<equiv> capRegister"

definition badge_register :: register where
  "badge_register \<equiv> badgeRegister"

definition frame_registers :: "register list" where
  "frame_registers \<equiv> frameRegisters"

definition gp_registers :: "register list" where
  "gp_registers \<equiv> gpRegisters"

definition exception_message :: "register list" where
  "exception_message \<equiv> exceptionMessage"

definition syscall_message :: "register list" where
  "syscall_message \<equiv> syscallMessage"

datatype arch_fault
  = VMFault (vm_fault_address : vspace_ref) (vm_fault_arch_data : "machine_word list")
  | VCPUFault (vcpu_hsr : data)
  | VPPIEvent (vppi_irq : irq)
  | VGICMaintenance (vgic_maintenance_data : "data option")


end

arch_requalify_consts (A) idle_thread_ptr

end
