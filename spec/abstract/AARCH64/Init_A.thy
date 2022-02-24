(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* FIXME AARCH64: verbatim setup copy of RISCV64; needs adjustment and validation;
                  only minimal type-check changes performed so far if any *)

chapter "An Initial Kernel State"

theory Init_A
imports
  Retype_A
  "Lib.SplitRule"
begin

context Arch begin global_naming RISCV64_A

text \<open>
  This is not a specification of true kernel initialisation. This theory describes a dummy
  initial state only, to show that the invariants and refinement relation are consistent.
\<close>

(* Some address sufficiently aligned address for one page *)
definition riscv_global_pt_ptr :: obj_ref
  where
  "riscv_global_pt_ptr = pptr_base + 0x2000"

(* Sufficiently aligned for irq type + cte_level_bits *)
definition init_irq_node_ptr :: obj_ref
  where
  "init_irq_node_ptr = pptr_base + 0x3000"

(* The highest user-level virtual address that is still canonical.
   It can be larger than user_vtop, which is the highest address we allow to be mapped.
   We need canonical_user, because the page tables have to have valid mappings there. *)
definition canonical_user :: "vspace_ref" where
  "canonical_user \<equiv> mask canonical_bit"

(* Kernel and ELF window are constructed so that they can be covered with one max_pt_level entry
   each. This is not the layout the real kernel uses, but we are only trying to show that
   the invariants are consistent. *)
(* FIXME AARCH64: TODO
definition init_vspace_uses :: "vspace_ref \<Rightarrow> riscvvspace_region_use"
  where
  "init_vspace_uses p \<equiv>
     if p \<in> {pptr_base ..< pptr_base + (1 << 30)} then RISCVVSpaceKernelWindow
     else if p \<in> {kernel_elf_base ..< kernel_elf_base + (1 << 20)} then RISCVVSpaceKernelELFWindow
     else if p \<le> canonical_user then RISCVVSpaceUserRegion
     else RISCVVSpaceInvalidRegion"
*)


definition init_arch_state :: arch_state
  where
  "init_arch_state \<equiv> \<lparr>
     arm_asid_table = Map.empty,
     arm_us_global_vspace = undefined,
     arm_kernel_vspace = undefined,
     arm_current_vcpu = None,
     arm_gicvcpu_numlistregs = undefined
   \<rparr>"


(* {pptr_base ..< pptr_base + (1 << 30)} is pt index 0x100 at max_pt_level,
   {kernel_elf_base ..< kernel_elf_base + (1 << 20)} comes out to pt index 0x1FE.
   The rest is constructed such that the translation lines up with what the invariants want. *)
definition global_pte :: "pt_index \<Rightarrow> pte"
  where
  "global_pte idx \<equiv>
     if idx = 0x100
     then PagePTE ((ucast (idx && mask (ptTranslationBits False - 1)) << ptTranslationBits False * 2))
                  {} vm_kernel_only
     else if idx = 0x1FE
     then PagePTE (2 << ptTranslationBits False * 2) {} vm_kernel_only
     else InvalidPTE"

definition init_kheap :: kheap
  where
  "init_kheap \<equiv>
    (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << cte_level_bits) = x
           then Some (CNode 0 (empty_cnode 0))
           else None)
    (idle_thread_ptr \<mapsto>
       TCB \<lparr>
         tcb_ctable = NullCap,
         tcb_vtable = NullCap,
         tcb_reply = NullCap,
         tcb_caller = NullCap,
         tcb_ipcframe = NullCap,
         tcb_state = IdleThreadState,
         tcb_fault_handler = replicate word_bits False,
         tcb_ipc_buffer = 0,
         tcb_fault = None,
         tcb_bound_notification = None,
         tcb_mcpriority = minBound,
         tcb_arch = init_arch_tcb
         \<rparr>
    )"

definition init_cdt :: cdt
  where
  "init_cdt \<equiv> Map.empty"

definition init_ioc :: "cslot_ptr \<Rightarrow> bool"
  where
  "init_ioc \<equiv>
   \<lambda>(a,b). (\<exists>obj. init_kheap a = Some obj \<and>
                  (\<exists>cap. cap_of obj b = Some cap \<and> cap \<noteq> cap.NullCap))"

definition init_A_st :: "'z::state_ext state"
  where
  "init_A_st \<equiv> \<lparr>
    kheap = init_kheap,
    cdt = init_cdt,
    is_original_cap = init_ioc,
    cur_thread = idle_thread_ptr,
    idle_thread = idle_thread_ptr,
    machine_state = init_machine_state,
    interrupt_irq_node = \<lambda>irq. init_irq_node_ptr + (ucast irq << cte_level_bits),
    interrupt_states = \<lambda>_. IRQInactive,
    arch_state = init_arch_state,
    exst = ext_init
  \<rparr>"

end
end
