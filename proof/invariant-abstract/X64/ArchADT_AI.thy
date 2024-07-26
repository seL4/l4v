(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>X64-specific definitions for abstract datatype for the abstract specification\<close>

theory ArchADT_AI
imports
  "Lib.Simulation"
  Invariants_AI
begin
context Arch begin arch_global_naming

subsection \<open>Constructing a virtual-memory view\<close>

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
        ArchObjectCap (PML4Cap pm_ref (Some asid))
          \<Rightarrow> (case x64_asid_table astate (asid_high_bits_of asid) of
                None \<Rightarrow> x64_global_pml4 astate
              | Some p \<Rightarrow> (case khp p of
                               Some (ArchObj ako) \<Rightarrow>
                                 if (VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool), pm_ref)
                                      \<in> vs_refs_arch ako
                                   then pm_ref
                                   else x64_global_pml4 astate
                             | _ \<Rightarrow> x64_global_pml4 astate))
      | _ \<Rightarrow>  x64_global_pml4 astate)
   | _ \<Rightarrow>  x64_global_pml4 astate"

lemma VSRef_AASIDPool_in_vs_refs:
  "(VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool), r) \<in> vs_refs_arch ko =
   (\<exists>apool. ko = ASIDPool apool \<and> apool (asid_low_bits_of asid) = Some r)"
  by (case_tac ko; simp add: image_def graph_of_def up_ucast_inj_eq)

context
notes vs_refs_arch_def[simp del]
begin

lemma get_vspace_of_thread_def2:
  "get_vspace_of_thread khp astate tcb_ref \<equiv>
        case khp tcb_ref of Some (TCB tcb) \<Rightarrow>
          (case tcb_vtable tcb of
             ArchObjectCap (PML4Cap pm_ref (Some asid))
               \<Rightarrow> if (\<exists>p apool.
                        x64_asid_table astate (asid_high_bits_of asid) = Some p \<and>
                        khp p = Some (ArchObj (ASIDPool apool)) \<and>
                        apool (asid_low_bits_of asid) = Some pm_ref)
                    then pm_ref
                    else x64_global_pml4 astate
           | _ \<Rightarrow>  x64_global_pml4 astate)
        | _ \<Rightarrow>  x64_global_pml4 astate"
  apply (rule eq_reflection)
  apply (clarsimp simp: get_vspace_of_thread_def
                 split: kernel_object.splits option.splits)
  apply (rename_tac tcb)
  apply (case_tac "tcb_vtable tcb",
         simp_all split: cap.splits arch_cap.splits kernel_object.splits
                         arch_kernel_obj.splits option.splits)
  apply (auto simp: VSRef_AASIDPool_in_vs_refs)
  done

lemma the_arch_cap_simp[simp]: "the_arch_cap (ArchObjectCap x) = x"
  by (simp add: the_arch_cap_def)

lemma get_vspace_of_thread_vs_lookup:
  "get_vspace_of_thread (kheap s) (arch_state s) tcb_ref =
   (case kheap s tcb_ref of
      Some (TCB tcb) \<Rightarrow>
        (case tcb_vtable tcb of
           ArchObjectCap (PML4Cap pm_ref (Some asid)) \<Rightarrow>
             if (the (vs_cap_ref (tcb_vtable tcb)) \<rhd> pm_ref) s then pm_ref
             else x64_global_pml4 (arch_state s)
         | _ \<Rightarrow> x64_global_pml4 (arch_state s))
    | _ \<Rightarrow> x64_global_pml4 (arch_state s))"
  apply (clarsimp simp: get_vspace_of_thread_def split: option.splits)
  apply (case_tac "the (kheap s tcb_ref)", simp_all, clarsimp)
  apply (rename_tac tcb)
  apply (case_tac "\<not> is_pml4_cap (tcb_vtable tcb)")
   apply (clarsimp simp: is_pml4_cap_def split: cap.split arch_cap.split)
  apply (clarsimp simp: is_pml4_cap_def vs_cap_ref_def)
  apply (case_tac asid, simp_all, clarsimp)
  apply (intro conjI impI)

   apply (erule vs_lookupE)
   apply (clarsimp simp: vs_asid_refs_def split_def image_def graph_of_def)
   apply (erule rtranclE, simp)
   apply (clarsimp dest!: vs_lookup1D)
   apply (clarsimp simp: vs_refs_def vs_refs_arch_def graph_of_def
                  split: kernel_object.split_asm arch_kernel_obj.split_asm)
   apply (erule rtranclE)
    apply (clarsimp simp: up_ucast_inj_eq obj_at_def vs_refs_def vs_refs_arch_def graph_of_def
                          image_def
                   split: arch_kernel_obj.split_asm)
   apply (clarsimp dest!: vs_lookup1D)
   apply (clarsimp simp: vs_refs_def vs_refs_arch_def graph_of_def
                   split: kernel_object.split_asm arch_kernel_obj.split_asm)

  apply (erule swap)
  apply (clarsimp split: kernel_object.split_asm arch_kernel_obj.split_asm
                         option.split_asm if_split_asm)
  apply (rule vs_lookupI)
   apply (fastforce simp: vs_asid_refs_def image_def graph_of_def)
  apply (rule rtrancl_into_rtrancl)
   apply (rule rtrancl_refl)
  apply (rule vs_lookup1I, (simp add: obj_at_def vs_refs_def vs_refs_arch_def)+)
  done

end

(* NOTE: This statement would clearly be nicer for a partial function
         but later on, we really want the function to be total. *)
lemma get_vspace_of_thread_eq:
  "pm_ref \<noteq> x64_global_pml4 (arch_state s) \<Longrightarrow>
   get_vspace_of_thread (kheap s) (arch_state s) tcb_ref = pm_ref \<longleftrightarrow>
   (\<exists>tcb. kheap s tcb_ref = Some (TCB tcb) \<and>
          (\<exists>asid. tcb_vtable tcb =
                  cap.ArchObjectCap (PML4Cap
                                       pm_ref (Some asid)) \<and>
                  (the (vs_cap_ref_arch (the_arch_cap (tcb_vtable tcb))) \<rhd> pm_ref) s))"
  by (auto simp: get_vspace_of_thread_vs_lookup vs_cap_ref_def
          split: option.splits Structures_A.kernel_object.splits
                 cap.splits arch_cap.splits)


text \<open>Non-monad versions of @{term get_pte} and @{term get_pde}.
  The parameters are:
  \begin{description}
  \item[@{term ahp}] a heap of architecture-specific objects,
  \item[@{term pt_ref}] a page-table reference,
  \item[@{term pd_ref}] a page-directory reference, and
  \item[@{term vptr}] a virtual address.
  \end{description}
\<close>
definition
  "get_pt_entry ahp pt_ref vptr \<equiv>
   case ahp pt_ref of
     Some (PageTable pt) \<Rightarrow>
       Some (pt (ucast ((vptr >> 12) && mask ptTranslationBits)))
   | _ \<Rightarrow> None"

definition
  "get_pd_entry ahp pd_ref vptr \<equiv>
   case ahp pd_ref of
     Some (PageDirectory pd) \<Rightarrow>
       Some (pd (ucast ((vptr >> pd_shift_bits) && mask ptTranslationBits)))
   | _ \<Rightarrow> None"

definition
  "get_pdpt_entry ahp pdpt_ref vptr \<equiv>
   case ahp pdpt_ref of
     Some (PDPointerTable pdpt) \<Rightarrow>
       Some (pdpt (ucast ((vptr >> pdpt_shift_bits) && mask ptTranslationBits)))
   | _ \<Rightarrow> None"

definition
  "get_pml4_entry ahp pm_ref vptr \<equiv>
   case ahp pm_ref of
     Some (PageMapL4 pm) \<Rightarrow>
       Some (pm (ucast ((vptr >> pml4_shift_bits) && mask ptTranslationBits)))
   | _ \<Rightarrow> None"

text \<open>The following function is used to extract the
  architecture-specific objects from the kernel heap\<close>
definition
  "get_arch_obj ==
   case_option None (\<lambda>x. case x of ArchObj a \<Rightarrow> Some a | _ \<Rightarrow> None)"

(* Auxilliary definitions for get_page_info *)
definition
  "get_pt_info ahp pt_ref vptr \<equiv>
   case get_pt_entry ahp pt_ref vptr of
     Some (SmallPagePTE base attrs rights) \<Rightarrow> Some (base, pageBitsForSize X64SmallPage, attrs, rights)
   | _ \<Rightarrow> None"

definition
  "get_pd_info ahp pd_ref vptr \<equiv>
   case get_pd_entry ahp pd_ref vptr of
     Some (PageTablePDE p _ _) \<Rightarrow> get_pt_info ahp (ptrFromPAddr p) vptr
   | Some (LargePagePDE base attrs rights) \<Rightarrow> Some (base, pageBitsForSize X64LargePage, attrs, rights)
   | _ \<Rightarrow> None"

definition
  "get_pdpt_info ahp pdpt_ref vptr \<equiv>
   case get_pdpt_entry ahp pdpt_ref vptr of
     Some (PageDirectoryPDPTE p _ _) \<Rightarrow> get_pd_info ahp (ptrFromPAddr p) vptr
   | Some (HugePagePDPTE base attrs rights) \<Rightarrow> Some (base, pageBitsForSize X64HugePage, attrs, rights)
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
  get_page_info :: "(obj_ref \<rightharpoonup> arch_kernel_obj) \<Rightarrow> obj_ref \<Rightarrow>
                    machine_word \<rightharpoonup> (machine_word \<times> nat \<times> frame_attrs \<times> vm_rights)"
where
  "get_page_info ahp pm_ref vptr \<equiv>
     if canonical_address vptr then
       case get_pml4_entry ahp pm_ref vptr of
           Some (PDPointerTablePML4E p _ _) \<Rightarrow> get_pdpt_info ahp (ptrFromPAddr p) vptr
         | _ \<Rightarrow> None
     else None"

text \<open>
  Both functions, @{text ptable_lift} and @{text vm_rights},
  take a kernel state and a virtual address.
  The former returns the physical address, the latter the associated rights.
\<close>
definition
  ptable_lift :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> machine_word \<rightharpoonup> machine_word" where
  "ptable_lift tcb s \<equiv> \<lambda>addr.
   case_option None (\<lambda>(base, bits, rights). Some (base + (addr && mask bits)))
     (get_page_info (\<lambda>obj. get_arch_obj (kheap s obj))
        (get_vspace_of_thread (kheap s) (arch_state s) tcb) addr)"
definition
  ptable_rights :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> machine_word \<Rightarrow> vm_rights" where
 "ptable_rights tcb s \<equiv> \<lambda>addr.
  case_option {} (snd o snd o snd)
     (get_page_info (\<lambda>obj. get_arch_obj (kheap s obj))
        (get_vspace_of_thread (kheap s) (arch_state s) tcb) addr)"

lemma ptable_lift_Some_canonical_addressD:
  "ptable_lift t s vptr = Some p \<Longrightarrow> canonical_address vptr"
  by (clarsimp simp: ptable_lift_def get_page_info_def split: if_splits)

end
end
