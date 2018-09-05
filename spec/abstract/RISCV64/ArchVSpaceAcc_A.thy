(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
Accessor functions for architecture specific parts of the specification.
*)

chapter "Accessing the RISCV64 VSpace"

theory ArchVSpaceAcc_A
imports "../KHeap_A"
begin

context Arch begin global_naming RISCV64_A

text {*
  This part of the specification is fairly concrete as the machine architecture
  is visible to the user in seL4 and therefore needs to be described.
  The abstraction compared to the implementation is in the data types for
  kernel objects. The interface which is rich in machine details remains the same.
*}

section "Encodings"

text {* The high bits of a virtual ASID. *}
definition asid_high_bits_of :: "asid \<Rightarrow> asid_high_index"
where
  "asid_high_bits_of asid \<equiv> ucast (asid >> asid_low_bits)"

text {* The low bits of a virtual ASID. *}
definition asid_low_bits_of :: "asid \<Rightarrow> asid_low_index"
where
  "asid_low_bits_of asid \<equiv> ucast asid"

lemmas asid_bits_of_defs = asid_high_bits_of_def asid_low_bits_of_def

section "Kernel Heap Accessors"

text {* Manipulate ASID pools, page directories and page tables in the kernel heap. *}
definition get_asid_pool :: "obj_ref \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref, 'z::state_ext) s_monad"
where
  "get_asid_pool ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     case kobj of ArchObj (ASIDPool pool) \<Rightarrow> return pool | _ \<Rightarrow> fail
   od"

definition set_asid_pool :: "obj_ref \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_asid_pool ptr pool \<equiv> do
     v \<leftarrow> get_object ptr;
     assert (case v of ArchObj (ASIDPool p) \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (ArchObj (ASIDPool pool))
   od"

definition get_pt :: "obj_ref \<Rightarrow> (pt_index \<Rightarrow> pte,'z::state_ext) s_monad"
where
  "get_pt ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     case kobj of ArchObj (PageTable pt) \<Rightarrow> return pt | _ \<Rightarrow> fail
   od"

definition set_pt :: "obj_ref \<Rightarrow> (pt_index \<Rightarrow> pte) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_pt ptr pt \<equiv> do
    v \<leftarrow> get_object ptr;
    assert (case v of ArchObj (PageTable _) \<Rightarrow> True | _ \<Rightarrow> False);
    set_object ptr (ArchObj (PageTable pt))
  od"

text {* The following function takes a pointer to a PTE in kernel memory and returns the PTE. *}
definition get_pte :: "obj_ref \<Rightarrow> (pte,'z::state_ext) s_monad"
where
  "get_pte ptr \<equiv> do
     base \<leftarrow> return $ ptr && ~~mask pt_bits;
     offset \<leftarrow> return $ (ptr && mask pt_bits) >> pte_bits;
     pt \<leftarrow> get_pt base;
     return $ pt (ucast offset)
   od"

definition store_pte :: "obj_ref \<Rightarrow> pte \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "store_pte p pte \<equiv> do
    base \<leftarrow> return $ p && ~~mask pt_bits;
    offset \<leftarrow> return $ (p && mask pt_bits) >> pte_bits;
    pt \<leftarrow> get_pt base;
    pt' \<leftarrow> return $ pt (ucast offset := pte);
    set_pt base pt'
  od"


section "Basic Operations"

definition max_pt_level :: nat
where
  "max_pt_level = 2"

definition pt_bits_left :: "nat \<Rightarrow> nat"
where
  "pt_bits_left level = ptTranslationBits * level + pageBits"

definition pt_index :: "nat \<Rightarrow> vspace_ref \<Rightarrow> machine_word"
where
  "pt_index level vptr \<equiv> (vptr >> pt_bits_left level) && mask ptTranslationBits"

text {* The kernel window is mapped into every virtual address space from the
@{term pptr_base} pointer upwards. This function copies the mappings which
create the kernel window into a new top-level page table object. *}

definition copy_global_mappings :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "copy_global_mappings new_pm \<equiv> do
    global_pt \<leftarrow> gets (riscv_global_pt \<circ> arch_state);
    base \<leftarrow> return $ pt_index max_pt_level pptr_base;
    pt_size \<leftarrow> return $ 1 << ptTranslationBits;
    mapM_x (\<lambda>index. do
        offset \<leftarrow> return (index << pte_bits);
        pme \<leftarrow> get_pte (global_pt + offset);
        store_pte (new_pm + offset) pme
    od) [base  .e.  pt_size - 1]
  od"

text {* Walk page tables in software. *}

definition pptr_from_pte :: "pte \<Rightarrow> vspace_ref"
where
  "pptr_from_pte pte \<equiv> ptrFromPAddr (pte_ppn pte << pt_bits)"

definition pt_slot_index :: "nat \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref"
where
  "pt_slot_index level pt_ptr vptr = pt_ptr + (pt_index level vptr << pte_bits)"

definition pte_at_index :: "nat \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (pte, 'z::state_ext) s_monad"
where
  "pte_at_index level pt_ptr vptr \<equiv> get_pte (pt_slot_index level pt_ptr vptr)"

fun
  lookup_pt_slot_from_level :: "nat \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow>
    (nat \<times> vspace_ref, 'z::state_ext) s_monad"
where
  "lookup_pt_slot_from_level level pt_ptr vptr = do
     pte \<leftarrow> pte_at_index level pt_ptr vptr;
     ptr \<leftarrow> return (pptr_from_pte pte);
     if is_PageTablePTE pte \<and> level > 0
       then lookup_pt_slot_from_level (level - 1) ptr vptr
       else return (pt_bits_left level, ptr)
   od"

definition lookup_pt_slot :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (nat \<times> vspace_ref, 'z::state_ext) s_monad"
where
  "lookup_pt_slot = lookup_pt_slot_from_level max_pt_level"

fun
  lookup_pt_from_level :: "nat \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow>
    (machine_word, 'z::state_ext) lf_monad"
where
  "lookup_pt_from_level level pt_ptr vptr target_pt_ptr = doE
     unlessE (0 < level) $ throwError InvalidRoot;
     pte <- liftE $ pte_at_index level pt_ptr vptr;
     unlessE (is_PageTablePTE pte) $ throwError InvalidRoot;
     ptr <- returnOk (pptr_from_pte pte);
     if ptr = target_pt_ptr
       then returnOk $ pt_slot_index (level - 1) ptr vptr
       else lookup_pt_from_level (level - 1) ptr vptr target_pt_ptr
   odE"

end
end
