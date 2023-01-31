(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>RISCV64-specific definitions for abstract datatype for the abstract specification\<close>

theory ArchADT_AI
imports
  "Lib.Simulation"
  Invariants_AI
begin
context Arch begin global_naming RISCV64

subsection \<open>Constructing a virtual-memory view\<close>

text \<open>
  This function is used below for helpers that expect a full state, but depend
  only on the heap and arch state.
\<close>
definition state_from_arch :: "kheap \<Rightarrow> arch_state \<Rightarrow> det_ext state" where
  "state_from_arch kh as \<equiv> undefined \<lparr> kheap := kh, arch_state := as \<rparr>"

text \<open>
  Function @{text get_vspace_of_thread} takes three parameters:
  the kernel heap, the architecture-specific state, and
  a thread identifier.
  It returns the identifier of the corresponding virtual address space.
  Note that this function is total.
  If the traversal stops before a page directory can be found
  (e.g. because the VTable entry is not set or a reference has been invalid),
  the function returns the global kernel mapping.

  Looking up the address space for a thread reference involves the following
  steps:

  At first, we check that the reference actually points to a TCB object in
  the kernel heap.
  If so, we check whether the vtable entry of the TCB contains a capability
  to an address space with valid mapping data.
  Note that the mapping data might become stale.
  Hence, we have to follow the mapping data through the ASID table.
\<close>
definition
  get_vspace_of_thread :: "kheap \<Rightarrow> arch_state \<Rightarrow> obj_ref \<Rightarrow> obj_ref"
where
  get_vspace_of_thread_def:
  "get_vspace_of_thread khp astate tcb_ref \<equiv>
   case khp tcb_ref of Some (TCB tcb) \<Rightarrow>
     (case tcb_vtable tcb of
        ArchObjectCap (PageTableCap pt (Some (asid, _))) \<Rightarrow>
          (case vspace_for_asid False asid (state_from_arch khp astate) of
             Some pt' \<Rightarrow> if pt' = pt then pt else riscv_global_pt astate
           | _ \<Rightarrow> riscv_global_pt astate)
        | _ \<Rightarrow>  riscv_global_pt astate)
   | _ \<Rightarrow>  riscv_global_pt astate"


lemma the_arch_cap_simp[simp]: "the_arch_cap (ArchObjectCap x) = x"
  by (simp add: the_arch_cap_def)

lemma vspace_for_asid_state_from_arch[simp]:
  "vspace_for_asid False a (state_from_arch (f_kheap False s) (arch_state s)) =
   vspace_for_asid False a s"
  by (simp add: vspace_for_asid_def pool_for_asid_def obind_def state_from_arch_def
         opt_map_def ta_filter_def vspace_for_pool_def
         split: option.splits)

declare vspace_for_asid_state_from_arch[simplified, simp]

(* NOTE: This statement would clearly be nicer for a partial function
         but later on, we really want the function to be total. *)
lemma get_vspace_of_thread_eq:
  "pt_ref \<noteq> riscv_global_pt (arch_state s) \<Longrightarrow>
   get_vspace_of_thread (kheap s) (arch_state s) tcb_ref = pt_ref \<longleftrightarrow>
   (\<exists>tcb. kheap s tcb_ref = Some (TCB tcb) \<and>
          (\<exists>asid vref. tcb_vtable tcb = ArchObjectCap (PageTableCap pt_ref (Some (asid,vref))) \<and>
                       vspace_for_asid False asid s = Some pt_ref))"
  unfolding get_vspace_of_thread_def
  by (auto split: option.splits kernel_object.splits cap.splits arch_cap.splits)


text \<open>
  The following function is used to extract the architecture-specific objects from the kernel heap.
\<close>

definition pte_info :: "vm_level \<Rightarrow> pte \<rightharpoonup> (machine_word \<times> nat \<times> vm_attributes \<times> vm_rights)" where
  "pte_info level pte \<equiv>
    case pte of
      PagePTE ppn attrs rights \<Rightarrow> Some (addr_from_ppn ppn, pt_bits_left level, attrs, rights)
    | _ \<Rightarrow> None"

text \<open>
  @{text get_page_info} takes the architecture-specific part of the kernel heap,
  a reference to the page directory, and a virtual memory address.
  It returns a tuple containing
  (a) the physical address, where the associated page starts,
  (b) the page table's size in bits, and
  (c) the page attributes (cachable, XNever, etc)
  (d) the access rights (a subset of @{term "{AllowRead, AllowWrite}"}).
\<close>
definition
  get_page_info :: "(obj_ref \<rightharpoonup> arch_kernel_obj) \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<rightharpoonup>
                    (machine_word \<times> nat \<times> vm_attributes \<times> vm_rights)"
where
  "get_page_info aobjs pt_ref vptr \<equiv> (do {
      oassert (canonical_address vptr);
      (level, slot) \<leftarrow> pt_lookup_slot pt_ref vptr;
      pte \<leftarrow> oapply slot;
      K $ pte_info level pte
    }) (\<lambda>p. pte_of p (aobjs |> pt_of))"

text \<open>
  Both functions, @{text ptable_lift} and @{text vm_rights},
  take a kernel state and a virtual address.
  The former returns the physical address, the latter the associated rights.
\<close>
definition ptable_lift :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> machine_word \<rightharpoonup> machine_word" where
  "ptable_lift tcb s \<equiv> \<lambda>addr.
   case_option None (\<lambda>(base, bits, rights). Some (base + (addr && mask bits)))
     (get_page_info (aobjs_of False s) (get_vspace_of_thread (kheap s) (arch_state s) tcb) addr)"

definition ptable_rights :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> machine_word \<Rightarrow> vm_rights" where
  "ptable_rights tcb s \<equiv> \<lambda>addr.
   case_option {} (snd o snd o snd)
      (get_page_info (aobjs_of False s) (get_vspace_of_thread (kheap s) (arch_state s) tcb) addr)"

lemma ptable_lift_Some_canonical_addressD:
  "ptable_lift t s vptr = Some p \<Longrightarrow> canonical_address vptr"
  by (clarsimp simp: ptable_lift_def get_page_info_def below_user_vtop_canonical
              split: if_splits option.splits)

end
end
