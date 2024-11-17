(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Accessor functions for architecture specific parts of the specification.
*)

chapter "Accessing the x64 VSpace"

theory ArchVSpaceAcc_A
imports KHeap_A
begin

context Arch begin arch_global_naming (A)

text \<open>
  This part of the specification is fairly concrete as the machine architecture
  is visible to the user in seL4 and therefore needs to be described.
  The abstraction compared to the implementation is in the data types for
  kernel objects. The interface which is rich in machine details remains the same.
\<close>

section "Encodings"

text \<open>The high bits of a virtual ASID.\<close>
definition
  asid_high_bits_of :: "asid \<Rightarrow> asid_high_index" where
  "asid_high_bits_of asid \<equiv> ucast (asid >> asid_low_bits)"

text \<open>The low bits of a virtual ASID.\<close>
definition
  asid_low_bits_of :: "asid \<Rightarrow> asid_low_index" where
  "asid_low_bits_of asid \<equiv> ucast asid"

lemmas asid_bits_of_defs =
  asid_high_bits_of_def asid_low_bits_of_def

section "Kernel Heap Accessors"

text \<open>Manipulate ASID pools, page directories and page tables in the kernel
heap.\<close>
(* declared in Arch as workaround for VER-1099 *)
locale_abbrev aobjs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<rightharpoonup> arch_kernel_obj"
  where
  "aobjs_of \<equiv> \<lambda>s. kheap s |> aobj_of"

definition
  get_asid_pool :: "obj_ref \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref, 'z::state_ext) s_monad" where
  "get_asid_pool ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (ASIDPool pool) \<Rightarrow> return pool
                 | _ \<Rightarrow> fail)
   od"

definition
  set_asid_pool :: "obj_ref \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> (unit, 'z::state_ext) s_monad" where
 "set_asid_pool ptr pool \<equiv> set_object ptr (ArchObj (ASIDPool pool))"

definition
  get_pd :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pde,'z::state_ext) s_monad" where
  "get_pd ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (PageDirectory pd) \<Rightarrow> return pd
                 | _ \<Rightarrow> fail)
   od"

definition
  set_pd :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pde) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pd ptr pd \<equiv> set_object ptr (ArchObj (PageDirectory pd))"

text \<open>The following function takes a pointer to a PDE in kernel memory
  and returns the actual PDE.\<close>
definition
  get_pde :: "obj_ref \<Rightarrow> (pde,'z::state_ext) s_monad" where
  "get_pde ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask pd_bits);
     offset \<leftarrow> return ((ptr && mask pd_bits) >> word_size_bits);
     pd \<leftarrow> get_pd base;
     return $ pd (ucast offset)
   od"

definition
  store_pde :: "obj_ref \<Rightarrow> pde \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pde p pde \<equiv> do
    base \<leftarrow> return (p && ~~mask pd_bits);
    offset \<leftarrow> return ((p && mask pd_bits) >> word_size_bits);
    pd \<leftarrow> get_pd base;
    pd' \<leftarrow> return $ pd (ucast offset := pde);
    set_pd base pd'
  od"


definition
  get_pt :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pte,'z::state_ext) s_monad" where
  "get_pt ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (PageTable pt) \<Rightarrow> return pt
                 | _ \<Rightarrow> fail)
   od"

definition
  set_pt :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pte) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pt ptr pt \<equiv> set_object ptr (ArchObj (PageTable pt))"

text \<open>The following function takes a pointer to a PTE in kernel memory
  and returns the actual PTE.\<close>
definition
  get_pte :: "obj_ref \<Rightarrow> (pte,'z::state_ext) s_monad" where
  "get_pte ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask pt_bits);
     offset \<leftarrow> return ((ptr && mask pt_bits) >> word_size_bits);
     pt \<leftarrow> get_pt base;
     return $ pt (ucast offset)
   od"

definition
  store_pte :: "obj_ref \<Rightarrow> pte \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pte p pte \<equiv> do
    base \<leftarrow> return (p && ~~mask pt_bits);
    offset \<leftarrow> return ((p && mask pt_bits) >> word_size_bits);
    pt \<leftarrow> get_pt base;
    pt' \<leftarrow> return $ pt (ucast offset := pte);
    set_pt base pt'
  od"

definition
  get_pdpt :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pdpte,'z::state_ext) s_monad" where
  "get_pdpt ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (PDPointerTable pt) \<Rightarrow> return pt
                 | _ \<Rightarrow> fail)
   od"

definition
  set_pdpt :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pdpte) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pdpt ptr pt \<equiv> set_object ptr (ArchObj (PDPointerTable pt))"

text \<open>The following function takes a pointer to a PDPTE in kernel memory
  and returns the actual PDPTE.\<close>
definition
  get_pdpte :: "obj_ref \<Rightarrow> (pdpte,'z::state_ext) s_monad" where
  "get_pdpte ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask pdpt_bits);
     offset \<leftarrow> return ((ptr && mask pdpt_bits) >> word_size_bits);
     pt \<leftarrow> get_pdpt base;
     return $ pt (ucast offset)
   od"

definition
  store_pdpte :: "obj_ref \<Rightarrow> pdpte \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pdpte p pte \<equiv> do
    base \<leftarrow> return (p && ~~mask pdpt_bits);
    offset \<leftarrow> return ((p && mask pdpt_bits) >> word_size_bits);
    pt \<leftarrow> get_pdpt base;
    pt' \<leftarrow> return $ pt (ucast offset := pte);
    set_pdpt base pt'
  od"

definition
  get_pml4 :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pml4e,'z::state_ext) s_monad" where
  "get_pml4 ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (PageMapL4 pt) \<Rightarrow> return pt
                 | _ \<Rightarrow> fail)
   od"

definition
  set_pml4 :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pml4e) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pml4 ptr pt \<equiv> set_object ptr (ArchObj (PageMapL4 pt))"

text \<open>The following function takes a pointer to a PML4E in kernel memory
  and returns the actual PML4E.\<close>
definition
  get_pml4e :: "obj_ref \<Rightarrow> (pml4e,'z::state_ext) s_monad" where
  "get_pml4e ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask pml4_bits);
     offset \<leftarrow> return ((ptr && mask pml4_bits) >> word_size_bits);
     pt \<leftarrow> get_pml4 base;
     return $ pt (ucast offset)
   od"

definition
  store_pml4e :: "obj_ref \<Rightarrow> pml4e \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pml4e p pte \<equiv> do
    base \<leftarrow> return (p && ~~mask pml4_bits);
    offset \<leftarrow> return ((p && mask pml4_bits) >> word_size_bits);
    pt \<leftarrow> get_pml4 base;
    pt' \<leftarrow> return $ pt (ucast offset := pte);
    set_pml4 base pt'
  od"


section "Basic Operations"

definition
get_pt_index :: "vspace_ref \<Rightarrow> machine_word" where
"get_pt_index vptr \<equiv> (vptr >> pt_shift_bits) && mask ptTranslationBits"

definition
get_pd_index :: "vspace_ref \<Rightarrow> machine_word" where
"get_pd_index vptr \<equiv> (vptr >> (pd_shift_bits)) && mask ptTranslationBits"

definition
get_pdpt_index :: "vspace_ref \<Rightarrow> machine_word" where
"get_pdpt_index vptr \<equiv> (vptr >> (pdpt_shift_bits)) && mask ptTranslationBits"

definition
get_pml4_index :: "vspace_ref \<Rightarrow> machine_word" where
"get_pml4_index vptr \<equiv> (vptr >> pml4_shift_bits) && mask ptTranslationBits"

text \<open>The kernel window is mapped into every virtual address space from the
@{term pptr_base} pointer upwards. This function copies the mappings which
create the kernel window into a new page directory object.\<close>

definition
copy_global_mappings :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "copy_global_mappings new_pm \<equiv> do
    global_pm \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
    base \<leftarrow> return $ get_pml4_index pptr_base;
    pme_bits \<leftarrow> return word_size_bits;
    pm_size \<leftarrow> return (1 << ptTranslationBits);
    mapM_x (\<lambda>index. do
        offset \<leftarrow> return (index << pme_bits);
        pme \<leftarrow> get_pml4e (global_pm + offset);
        store_pml4e (new_pm + offset) pme
    od) [base  .e.  pm_size - 1]
  od"

text \<open>Walk the page directories and tables in software.\<close>

definition
lookup_pml4_slot :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref" where
"lookup_pml4_slot pm vptr \<equiv> let pm_index = get_pml4_index vptr
                             in pm + (pm_index << word_size_bits)"

definition
lookup_pdpt_slot :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (obj_ref,'z::state_ext) lf_monad" where
"lookup_pdpt_slot pd vptr \<equiv> doE
    pml4_slot \<leftarrow> returnOk (lookup_pml4_slot pd vptr);
    pml4e \<leftarrow> liftE $ get_pml4e pml4_slot;
    (case pml4e of
          PDPointerTablePML4E tab _ _ \<Rightarrow> (doE
            pd \<leftarrow> returnOk (ptrFromPAddr tab);
            pd_index \<leftarrow> returnOk (get_pdpt_index vptr);
            pd_slot \<leftarrow> returnOk (pd + (pd_index << word_size_bits));
            returnOk pd_slot
          odE)
        | _ \<Rightarrow> throwError $ MissingCapability pml4_shift_bits)
 odE"

text \<open>A non-failing version of @{const lookup_pdpt_slot} when the pml4 is already known\<close>
definition
  lookup_pdpt_slot_no_fail :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref"
where
  "lookup_pdpt_slot_no_fail pdpt vptr \<equiv>
     pdpt + (get_pdpt_index vptr << word_size_bits)"

text \<open>The following function takes a page-directory reference as well as
  a virtual address and then computes a pointer to the PDE in kernel memory\<close>
definition
lookup_pd_slot :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (obj_ref,'z::state_ext) lf_monad" where
"lookup_pd_slot pd vptr \<equiv> doE
    pdpt_slot \<leftarrow> lookup_pdpt_slot pd vptr;
    pdpte \<leftarrow> liftE $ get_pdpte pdpt_slot;
    (case pdpte of
          PageDirectoryPDPTE tab _ _ \<Rightarrow> (doE
            pd \<leftarrow> returnOk (ptrFromPAddr tab);
            pd_index \<leftarrow> returnOk (get_pd_index vptr);
            pd_slot \<leftarrow> returnOk (pd + (pd_index << word_size_bits));
            returnOk pd_slot
          odE)
        | _ \<Rightarrow> throwError $ MissingCapability pdpt_shift_bits)
 odE"

text \<open>A non-failing version of @{const lookup_pd_slot} when the pdpt is already known\<close>
definition
  lookup_pd_slot_no_fail :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref"
where
  "lookup_pd_slot_no_fail pd vptr \<equiv>
     pd + (get_pd_index vptr << word_size_bits)"

text \<open>The following function takes a page-directory reference as well as
  a virtual address and then computes a pointer to the PTE in kernel memory.
  Note that the function fails if the virtual address is mapped on a section or
  super section.\<close>
definition
lookup_pt_slot :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (obj_ref,'z::state_ext) lf_monad" where
"lookup_pt_slot vspace vptr \<equiv> doE
    pd_slot \<leftarrow> lookup_pd_slot vspace vptr;
    pde \<leftarrow> liftE $ get_pde pd_slot;
    (case pde of
          PageTablePDE ptab _ _ \<Rightarrow>   (doE
            pt \<leftarrow> returnOk (ptrFromPAddr ptab);
            pt_index \<leftarrow> returnOk (get_pt_index vptr);
            pt_slot \<leftarrow> returnOk (pt + (pt_index << word_size_bits));
            returnOk pt_slot
          odE)
        | _ \<Rightarrow> throwError $ MissingCapability pd_shift_bits)
   odE"

text \<open>A non-failing version of @{const lookup_pt_slot} when the pd is already known\<close>
definition
  lookup_pt_slot_no_fail :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref"
where
  "lookup_pt_slot_no_fail pt vptr \<equiv>
     pt + (get_pt_index vptr << word_size_bits)"

(* FIXME x64-vtd:
text {* The following functions helped us locating the actual iopte *}
definition
  get_iopt :: "obj_ref \<Rightarrow> (16 word \<Rightarrow> iopte,'z::state_ext) s_monad" where
  "get_iopt ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (IOPageTable pt) \<Rightarrow> return pt
                 | _ \<Rightarrow> fail)
   od"

definition
  set_iopt :: "obj_ref \<Rightarrow> (16 word \<Rightarrow> iopte) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_iopt ptr pt \<equiv> do
     kobj \<leftarrow> get_object ptr;
     assert (case kobj of ArchObj (PageTable _) \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (ArchObj (IOPageTable pt))
   od"

definition  get_iopte :: "obj_ref \<Rightarrow> (iopte,'z::state_ext) s_monad" where
  "get_iopte ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask iopt_bits);
     offset \<leftarrow> return ((ptr && mask iopt_bits) >> 2);
     pt \<leftarrow> get_iopt base;
     return $ pt (ucast offset)
   od"

definition
  store_iopte :: "obj_ref \<Rightarrow> iopte \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_iopte p iopte \<equiv> do
    base \<leftarrow> return (p && ~~mask iopt_bits);
    offset \<leftarrow> return ((p && mask iopt_bits) >> 8);
    pt \<leftarrow> get_iopt base;
    pt' \<leftarrow> return $ pt (ucast offset := iopte);
    set_iopt base pt'
  od"

definition
  get_iort :: "obj_ref \<Rightarrow> (16 word \<Rightarrow> iorte,'z::state_ext) s_monad" where
  "get_iort ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (IORootTable pt) \<Rightarrow> return pt
                 | _ \<Rightarrow> fail)
   od"

definition
  set_iort :: "obj_ref \<Rightarrow> (16 word \<Rightarrow> iorte) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_iort ptr pt \<equiv> do
     kobj \<leftarrow> get_object ptr;
     assert (case kobj of ArchObj (IORootTable _) \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (ArchObj (IORootTable pt))
   od"

definition  get_iorte :: "obj_ref \<Rightarrow> (iorte,'z::state_ext) s_monad" where
  "get_iorte ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask iopt_bits);
     offset \<leftarrow> return ((ptr && mask iopt_bits) >> 2);
     pt \<leftarrow> get_iort base;
     return $ pt (ucast offset)
   od"

definition
  store_iorte :: "obj_ref \<Rightarrow> iorte \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_iorte p iorte \<equiv> do
    base \<leftarrow> return (p && ~~mask iopt_bits);
    offset \<leftarrow> return ((p && mask iopt_bits) >> 8);
    rt \<leftarrow> get_iort base;
    rt' \<leftarrow> return $ rt (ucast offset := iorte);
    set_iort base rt'
  od"

definition
  get_ioct :: "obj_ref \<Rightarrow> (16 word \<Rightarrow> iocte,'z::state_ext) s_monad" where
  "get_ioct ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (IOContextTable pt) \<Rightarrow> return pt
                 | _ \<Rightarrow> fail)
   od"

definition
  set_ioct :: "obj_ref \<Rightarrow> (16 word \<Rightarrow> iocte) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_ioct ptr ct \<equiv> do
     kobj \<leftarrow> get_object ptr;
     assert (case kobj of ArchObj (IOContextTable _) \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (ArchObj (IOContextTable ct))
   od"

definition  get_iocte :: "obj_ref \<Rightarrow> (iocte,'z::state_ext) s_monad" where
  "get_iocte ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask iopt_bits);
     offset \<leftarrow> return ((ptr && mask iopt_bits) >> 8);
     ct \<leftarrow> get_ioct base;
     return $ ct (ucast offset)
   od"


definition
  store_iocte :: "obj_ref \<Rightarrow> iocte \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_iocte p iocte \<equiv> do
    base \<leftarrow> return (p && ~~mask iopt_bits);
    offset \<leftarrow> return ((p && mask iopt_bits) >> 8);
    pt \<leftarrow> get_ioct base;
    pt' \<leftarrow> return $ pt (ucast offset := iocte);
    set_ioct base pt'
  od"

definition get_pci_fun :: "io_asid \<Rightarrow> machine_word" where
"get_pci_fun asid \<equiv> fromIntegral asid && 0x7"

definition get_pci_bus :: "io_asid \<Rightarrow> machine_word" where
"get_pci_bus asid \<equiv> fromIntegral $ (asid >> 8) && 0xFF"

definition get_pci_dev :: "io_asid \<Rightarrow> machine_word" where
"get_pci_dev asid \<equiv> fromIntegral $ (asid >> 3) && 0x1F"

definition lookup_io_context_slot :: "io_asid \<Rightarrow> (obj_ref,'z::state_ext) s_monad" where
"lookup_io_context_slot pci_request_id \<equiv> do
    rtptr <- gets (x64_io_root_table \<circ> arch_state);
    root_index <- return $ get_pci_bus pci_request_id;
    rte_ptr <- return $ rtptr + root_index;
    rte <- get_iorte rte_ptr;
    ct_pptr <- return $ ptrFromPAddr (context_table rte);
    cte_ptr <- return $ ((get_pci_dev pci_request_id) << vtd_cte_size_bits)
              || get_pci_fun pci_request_id;
    return $ ct_pptr + ( cte_ptr << vtd_cte_size_bits)
  od"

definition get_vtd_pte_offset ::  "64 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 64 word"
where "get_vtd_pte_offset translation levels_to_resolve levels_remaining \<equiv>
  let lvldiff = levels_to_resolve - levels_remaining
  in (translation >> (vtd_pt_bits * (x64_num_io_pt_levels - 1 - lvldiff)))
      && (mask vtd_pt_bits)"


fun lookup_io_ptr_resolve_levels :: "obj_ref \<Rightarrow> 64 word\<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
 ((obj_ref \<times> nat),'z::state_ext) lf_monad"
where "lookup_io_ptr_resolve_levels iopt_ref translation levels_to_resolve
  levels_remaining = doE
    offset <- returnOk $ get_vtd_pte_offset translation
      levels_to_resolve levels_remaining;
    pte_ptr <- returnOk $ iopt_ref + offset;
    if levels_remaining = 0
      then returnOk $ (pte_ptr, 0)
      else (doE
        iopte <- liftE $ get_iopte pte_ptr;
        slot <- returnOk $ ptrFromPAddr (frame_ptr iopte);
        if (io_pte_rights iopte = vm_read_write)
          then returnOk (pte_ptr, levels_remaining)
          else lookup_io_ptr_resolve_levels slot translation levels_to_resolve
            (levels_remaining - 1)
      odE)
  odE"

definition lookup_io_pt_slot :: "obj_ref \<Rightarrow> 64 word \<Rightarrow>  ((obj_ref \<times> nat),'z::state_ext) lf_monad"
where "lookup_io_pt_slot pte_ref ioaddr \<equiv> lookup_io_ptr_resolve_levels pte_ref  (ioaddr >> pageBits)
  (x64_num_io_pt_levels - 1) (x64_num_io_pt_levels - 1)"

*)


end
end
