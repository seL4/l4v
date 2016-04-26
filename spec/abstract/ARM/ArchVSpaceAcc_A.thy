(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
Accessor functions for architecture specific parts of the specification. 
*)

chapter "Accessing the ARM VSpace"

theory ArchVSpaceAcc_A
imports "../KHeap_A"
begin

context Arch begin global_naming ARM_A

text {* 
  This part of the specification is fairly concrete as the machine architecture
  is visible to the user in seL4 and therefore needs to be described.
  The abstraction compared to the implementation is in the data types for 
  kernel objects. The interface which is rich in machine details remains the same.
*}

section "Encodings"

text {* The high bits of a virtual ASID. *}
definition
  asid_high_bits_of :: "asid \<Rightarrow> word8" where
  "asid_high_bits_of asid \<equiv> ucast (asid >> asid_low_bits)"


section "Kernel Heap Accessors"

text {* Manipulate ASID pools, page directories and page tables in the kernel
heap. *}
definition
  get_asid_pool :: "obj_ref \<Rightarrow> (10 word \<rightharpoonup> obj_ref,'z::state_ext) s_monad" where
  "get_asid_pool ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (ASIDPool pool) \<Rightarrow> return pool
                 | _ \<Rightarrow> fail)
   od"

definition
  set_asid_pool :: "obj_ref \<Rightarrow> (10 word \<rightharpoonup> obj_ref) \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "set_asid_pool ptr pool \<equiv> do
    v \<leftarrow> get_object ptr;
    assert (case v of ArchObj (arch_kernel_obj.ASIDPool p) \<Rightarrow> True | _ \<Rightarrow> False);
    set_object ptr (ArchObj (arch_kernel_obj.ASIDPool pool))
  od"

definition
  get_pd :: "obj_ref \<Rightarrow> (12 word \<Rightarrow> pde,'z::state_ext) s_monad" where
  "get_pd ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (PageDirectory pd) \<Rightarrow> return pd
                 | _ \<Rightarrow> fail)
   od"

definition
  set_pd :: "obj_ref \<Rightarrow> (12 word \<Rightarrow> pde) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pd ptr pd \<equiv> do
     kobj \<leftarrow> get_object ptr;
     assert (case kobj of ArchObj (PageDirectory pd) \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (ArchObj (PageDirectory pd)) 
   od"

text {* The following function takes a pointer to a PDE in kernel memory
  and returns the actual PDE. *}
definition
  get_pde :: "obj_ref \<Rightarrow> (pde,'z::state_ext) s_monad" where
  "get_pde ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask pd_bits);
     offset \<leftarrow> return ((ptr && mask pd_bits) >> 2);
     pd \<leftarrow> get_pd base;
     return $ pd (ucast offset)
   od"

definition
  store_pde :: "obj_ref \<Rightarrow> pde \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pde p pde \<equiv> do
    base \<leftarrow> return (p && ~~mask pd_bits);
    offset \<leftarrow> return ((p && mask pd_bits) >> 2);
    pd \<leftarrow> get_pd base;
    pd' \<leftarrow> return $ pd (ucast offset := pde);
    set_pd base pd'
  od"


definition
  get_pt :: "obj_ref \<Rightarrow> (word8 \<Rightarrow> pte,'z::state_ext) s_monad" where
  "get_pt ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (PageTable pt) \<Rightarrow> return pt
                 | _ \<Rightarrow> fail)
   od"

definition
  set_pt :: "obj_ref \<Rightarrow> (word8 \<Rightarrow> pte) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pt ptr pt \<equiv> do
     kobj \<leftarrow> get_object ptr;
     assert (case kobj of ArchObj (PageTable _) \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (ArchObj (PageTable pt)) 
   od"

text {* The following function takes a pointer to a PTE in kernel memory
  and returns the actual PTE. *}
definition
  get_pte :: "obj_ref \<Rightarrow> (pte,'z::state_ext) s_monad" where
  "get_pte ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask pt_bits);
     offset \<leftarrow> return ((ptr && mask pt_bits) >> 2);
     pt \<leftarrow> get_pt base;
     return $ pt (ucast offset)
   od"

definition
  store_pte :: "obj_ref \<Rightarrow> pte \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pte p pte \<equiv> do
    base \<leftarrow> return (p && ~~mask pt_bits);
    offset \<leftarrow> return ((p && mask pt_bits) >> 2);
    pt \<leftarrow> get_pt base;
    pt' \<leftarrow> return $ pt (ucast offset := pte);
    set_pt base pt'
  od"


section "Basic Operations"

text {* The kernel window is mapped into every virtual address space from the
@{term kernel_base} pointer upwards. This function copies the mappings which
create the kernel window into a new page directory object. *}
definition
copy_global_mappings :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"copy_global_mappings new_pd \<equiv> do
    global_pd \<leftarrow> gets (arm_global_pd \<circ> arch_state);
    pde_bits \<leftarrow> return 2;
    pd_size \<leftarrow> return (1 << (pd_bits - pde_bits));
    mapM_x (\<lambda>index. do
        offset \<leftarrow> return (index << pde_bits);
        pde \<leftarrow> get_pde (global_pd + offset);
        store_pde (new_pd + offset) pde
    od) [kernel_base >> 20  .e.  pd_size - 1] 
od"

text {* Walk the page directories and tables in software. *}

text {* The following function takes a page-directory reference as well as
  a virtual address and then computes a pointer to the PDE in kernel memory *}
definition
lookup_pd_slot :: "word32 \<Rightarrow> vspace_ref \<Rightarrow> word32" where
"lookup_pd_slot pd vptr \<equiv>
    let pd_index = vptr >> 20
    in pd + (pd_index << 2)"

text {* The following function takes a page-directory reference as well as
  a virtual address and then computes a pointer to the PTE in kernel memory.
  Note that the function fails if the virtual address is mapped on a section or
  super section. *}
definition
lookup_pt_slot :: "word32 \<Rightarrow> vspace_ref \<Rightarrow> (word32,'z::state_ext) lf_monad" where
"lookup_pt_slot pd vptr \<equiv> doE
    pd_slot \<leftarrow> returnOk (lookup_pd_slot pd vptr); 
    pde \<leftarrow> liftE $ get_pde pd_slot;
    (case pde of
          PageTablePDE ptab _ _ \<Rightarrow>   (doE
            pt \<leftarrow> returnOk (ptrFromPAddr ptab);
            pt_index \<leftarrow> returnOk ((vptr >> 12) && 0xff);
            pt_slot \<leftarrow> returnOk (pt + (pt_index << 2));
            returnOk pt_slot
          odE)
        | _ \<Rightarrow> throwError $ MissingCapability 20)
odE"


text {* A non-failing version of @{const lookup_pt_slot} when the pd is already known *}
definition 
  lookup_pt_slot_no_fail :: "word32 \<Rightarrow> vspace_ref \<Rightarrow> word32"
where
  "lookup_pt_slot_no_fail pt vptr \<equiv> 
     let pt_index = ((vptr >> 12) && 0xff) 
     in pt + (pt_index << 2)"

end

end
