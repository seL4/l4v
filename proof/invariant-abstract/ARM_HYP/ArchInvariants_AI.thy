(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInvariants_AI
imports InvariantsPre_AI
begin

\<comment> \<open>---------------------------------------------------------------------------\<close>
section "Move this up"

qualify ARM_HYP (in Arch)

(* FIXME: move to spec level *)
(* global data and code of the kernel, not covered by any cap *)
axiomatization
  kernel_data_refs :: "word32 set"

end_qualify

\<comment> \<open>---------------------------------------------------------------------------\<close>
section "ARM-specific invariant definitions"

qualify ARM_HYP (in Arch)
record iarch_tcb =
  itcb_vcpu :: "obj_ref option"
end_qualify

context Arch begin arch_global_naming

definition
  arch_tcb_to_iarch_tcb :: "arch_tcb \<Rightarrow> iarch_tcb"
where
  "arch_tcb_to_iarch_tcb arch_tcb \<equiv> \<lparr> itcb_vcpu = tcb_vcpu arch_tcb \<rparr>"

(* Need one of these simp rules for each field in 'iarch_tcb' *)
lemma arch_tcb_to_iarch_tcb_simps[simp]:
  "itcb_vcpu (arch_tcb_to_iarch_tcb arch_tcb) = tcb_vcpu arch_tcb"
  by (auto simp: arch_tcb_to_iarch_tcb_def)

lemma iarch_tcb_context_set[simp]:
  "arch_tcb_to_iarch_tcb (arch_tcb_context_set p tcb) = arch_tcb_to_iarch_tcb tcb"
  by (auto simp: arch_tcb_to_iarch_tcb_def arch_tcb_context_set_def)

lemma iarch_tcb_set_registers[simp]:
  "arch_tcb_to_iarch_tcb (arch_tcb_set_registers regs arch_tcb)
     = arch_tcb_to_iarch_tcb arch_tcb"
  by (simp add: arch_tcb_to_iarch_tcb_def arch_tcb_set_registers_def)

lemmas vspace_bits_defs = pd_bits_def pde_bits_def pt_bits_def pte_bits_def pageBits_def

(* These simplifications allows us to keep many arch-specific proofs unchanged. *)

lemma arch_cap_fun_lift_expand[simp]:
  "(arch_cap_fun_lift (\<lambda> ac. case ac of
                                ASIDPoolCap obj_ref asid \<Rightarrow> P_ASIDPoolCap obj_ref asid
                              | ASIDControlCap \<Rightarrow> P_ASIDControlCap
                              | PageCap dev obj_ref rights sz vr \<Rightarrow> P_PageCap obj_ref rights sz vr
                              | PageTableCap obj_ref vr \<Rightarrow> P_PageTableCap dev obj_ref vr
                              | PageDirectoryCap obj_ref asid \<Rightarrow> P_PageDirectoryCap obj_ref asid
                              | VCPUCap obj_ref \<Rightarrow> P_VCPUCap obj_ref)
                      F) = (\<lambda>c.
   (case c of
      ArchObjectCap (ASIDPoolCap obj_ref asid) \<Rightarrow> P_ASIDPoolCap obj_ref asid
    | ArchObjectCap (ASIDControlCap) \<Rightarrow> P_ASIDControlCap
    | ArchObjectCap (PageCap dev obj_ref rights sz vr) \<Rightarrow> P_PageCap obj_ref rights sz vr
    | ArchObjectCap (PageTableCap obj_ref vr) \<Rightarrow> P_PageTableCap dev obj_ref vr
    | ArchObjectCap (PageDirectoryCap obj_ref asid) \<Rightarrow> P_PageDirectoryCap obj_ref asid
    | ArchObjectCap (VCPUCap obj_ref) \<Rightarrow> P_VCPUCap obj_ref
    | _ \<Rightarrow> F))"
  apply (rule ext)
  by (simp add: arch_cap_fun_lift_def)

lemma arch_obj_fun_lift_expand[simp]:
  "(arch_obj_fun_lift (\<lambda> ako. case ako of
                                ASIDPool pool \<Rightarrow> P_ASIDPool pool
                              | PageTable pt \<Rightarrow> P_PageTable pt
                              | PageDirectory pd \<Rightarrow> P_PageDirectory pd
                              | DataPage dev s \<Rightarrow> P_DataPage dev s
                              | VCPU v \<Rightarrow> P_VCPU v)
                      F) = (\<lambda>ko.
   (case ko of
      ArchObj (ASIDPool pool) \<Rightarrow> P_ASIDPool pool
    | ArchObj (PageTable pt) \<Rightarrow> P_PageTable pt
    | ArchObj (PageDirectory pd) \<Rightarrow> P_PageDirectory pd
    | ArchObj (DataPage dev s) \<Rightarrow> P_DataPage dev s
    | ArchObj (VCPU v) \<Rightarrow> P_VCPU v
    | _ \<Rightarrow> F))"
  apply (rule ext)
  by (simp only: arch_obj_fun_lift_def)

lemmas aa_type_simps =
  aa_type_def[split_simps arch_kernel_obj.split]

lemmas a_type_def = a_type_def[simplified aa_type_def]

lemmas a_type_simps = a_type_def[split_simps kernel_object.split arch_kernel_obj.split]

definition
  "vmsz_aligned ref sz \<equiv> is_aligned ref (pageBitsForSize sz)"

definition
  "wellformed_mapdata sz \<equiv>
   \<lambda>(asid, vref). 0 < asid \<and> asid \<le> 2^asid_bits - 1
                \<and> vmsz_aligned vref sz \<and> vref < kernel_base"

definition
  wellformed_acap :: "arch_cap \<Rightarrow> bool"
where
  "wellformed_acap ac \<equiv>
   case ac of
     ASIDPoolCap r as
       \<Rightarrow> is_aligned as asid_low_bits \<and> as \<le> 2^asid_bits - 1
   | PageCap dev r rghts sz mapdata \<Rightarrow> rghts \<in> valid_vm_rights \<and>
     case_option True (wellformed_mapdata sz) mapdata
   | PageTableCap r (Some mapdata) \<Rightarrow>
     wellformed_mapdata ARMSection mapdata
   | PageDirectoryCap r (Some asid) \<Rightarrow>
     0 < asid \<and> asid \<le> 2^asid_bits - 1
   | _ \<Rightarrow> True"

lemmas wellformed_acap_simps =
  wellformed_mapdata_def wellformed_acap_def[split_simps arch_cap.split]

definition
  "in_device_frame p \<equiv> \<lambda>s.
   \<exists>sz. typ_at (AArch (ADeviceData sz)) (p && ~~ mask (pageBitsForSize sz)) s"

definition
  "user_mem s \<equiv> \<lambda>p.
  if (in_user_frame p s)
  then Some (underlying_memory (machine_state s) p)
  else None"

definition
  "device_mem s \<equiv> \<lambda>p.
  if (in_device_frame p s)
  then Some p
  else None"

abbreviation "device_region s \<equiv> dom (device_state (machine_state s))"

lemma typ_at_pg_user:
  "typ_at (AArch (AUserData sz)) buf s = ko_at (ArchObj (DataPage False sz)) buf s"
  unfolding obj_at_def
  by (auto simp: a_type_def split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm if_split_asm)

lemma typ_at_pg_device:
  "typ_at (AArch (ADeviceData sz)) buf s = ko_at (ArchObj (DataPage True sz)) buf s"
  unfolding obj_at_def
  by (auto simp: a_type_def split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm if_split_asm)

lemmas typ_at_pg = typ_at_pg_user typ_at_pg_device


(* this time with typ_at. might lead to confusion, but this is how
   the rest should have been defined.. *)
abbreviation
  "asid_pool_at \<equiv> typ_at (AArch AASIDPool)"
abbreviation
  "page_table_at \<equiv> typ_at (AArch APageTable)"
abbreviation
  "page_directory_at \<equiv> typ_at (AArch APageDirectory)"
abbreviation
  "vcpu_at \<equiv> typ_at (AArch AVCPU)" (* ARMHYP *)

definition
  "pde_at p \<equiv> page_directory_at (p && ~~ mask pd_bits)
                  and K (is_aligned p pde_bits)"  (* ARMHYP *)
definition
  "pte_at p \<equiv> page_table_at (p && ~~ mask pt_bits)
                  and K (is_aligned p pte_bits)" (* ARMHYP *)

definition
  valid_arch_cap_ref :: "arch_cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_cap_ref ac s \<equiv> (case ac of
    ASIDPoolCap r as \<Rightarrow> typ_at (AArch AASIDPool) r s
  | ASIDControlCap \<Rightarrow> True
  | PageCap dev r rghts sz mapdata \<Rightarrow> if dev then typ_at (AArch (ADeviceData sz)) r s
                                             else typ_at (AArch (AUserData sz)) r s
  | PageTableCap r mapdata \<Rightarrow> typ_at (AArch APageTable) r s
  | PageDirectoryCap r mapdata\<Rightarrow> typ_at (AArch APageDirectory) r s
  | VCPUCap r \<Rightarrow> typ_at (AArch AVCPU) r s)"

lemmas valid_arch_cap_ref_simps =
  valid_arch_cap_ref_def[split_simps arch_cap.split]

definition
  valid_arch_cap :: "arch_cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_cap ac s \<equiv> (case ac of
    ASIDPoolCap r as \<Rightarrow>
         typ_at (AArch AASIDPool) r s \<and> is_aligned as asid_low_bits
           \<and> as \<le> 2^asid_bits - 1
  | ASIDControlCap \<Rightarrow> True
  | PageCap dev r rghts sz mapdata \<Rightarrow>
    (if dev then (typ_at (AArch (ADeviceData sz)) r s)
            else (typ_at (AArch (AUserData sz)) r s)) \<and>
     rghts \<in> valid_vm_rights \<and>
    (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow> 0 < asid \<and> asid \<le> 2^asid_bits - 1
                                             \<and> vmsz_aligned ref sz \<and> ref < kernel_base)
  | PageTableCap r mapdata \<Rightarrow>
    typ_at (AArch APageTable) r s \<and>
    (case mapdata of None \<Rightarrow> True
       | Some (asid, vref) \<Rightarrow> 0 < asid \<and> asid \<le> 2 ^ asid_bits - 1
                                \<and> vref < kernel_base
                                \<and> is_aligned vref (pageBitsForSize ARMSection))
  | PageDirectoryCap r mapdata \<Rightarrow>
    typ_at (AArch APageDirectory) r s \<and>
    case_option True (\<lambda>asid. 0 < asid \<and> asid \<le> 2^asid_bits - 1) mapdata
  | VCPUCap r \<Rightarrow> typ_at (AArch AVCPU) r s)"

lemmas valid_arch_cap_simps =
  valid_arch_cap_def[split_simps arch_cap.split]

definition
  "is_nondevice_page_cap_arch \<equiv> \<lambda>cap. case cap of
      (PageCap False x xa xb xc) \<Rightarrow>  True
  | _ \<Rightarrow> False"

definition
  "is_nondevice_page_cap \<equiv> \<lambda>c. arch_cap_fun_lift is_nondevice_page_cap_arch False c"

lemmas is_nondevice_page_cap_simps = is_nondevice_page_cap_def[split_simps arch_cap.split cap.split]

primrec
  acap_class :: "arch_cap \<Rightarrow> capclass"
where
  "acap_class (ASIDPoolCap x y)      = PhysicalClass"
| "acap_class (ASIDControlCap)       = ASIDMasterClass"
| "acap_class (PageCap dev x y sz z)     = PhysicalClass"
| "acap_class (PageTableCap x y)     = PhysicalClass"
| "acap_class (PageDirectoryCap x y) = PhysicalClass"
| "acap_class (VCPUCap v)            = PhysicalClass"

definition
  valid_ipc_buffer_cap_arch :: "arch_cap \<Rightarrow> word32 \<Rightarrow> bool"
where
  "valid_ipc_buffer_cap_arch ac bufptr \<equiv>
         case ac of
              (PageCap False ref rghts sz mapdata) \<Rightarrow>
                   is_aligned bufptr msg_align_bits

            | _ \<Rightarrow> False"

declare valid_ipc_buffer_cap_arch_def[simp]

definition
  "valid_ipc_buffer_cap c bufptr \<equiv>
     case c of NullCap \<Rightarrow> True
     | ArchObjectCap acap \<Rightarrow> valid_ipc_buffer_cap_arch acap bufptr
     | _ \<Rightarrow> False"

definition "data_at \<equiv> \<lambda>sz p s. typ_at (AArch (AUserData sz)) p s
  \<or> typ_at (AArch (ADeviceData sz)) p s"

definition
  valid_arch_tcb :: "arch_tcb \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_tcb \<equiv> \<lambda>t s. \<forall>v. tcb_vcpu t = Some v \<longrightarrow> vcpu_at v s"

definition
  valid_arch_idle :: "iarch_tcb \<Rightarrow> bool"
where
  "valid_arch_idle t \<equiv> itcb_vcpu t = None"

primrec
  valid_pte :: "pte \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pte (InvalidPTE) = \<top>"
| "valid_pte (LargePagePTE ptr x y) =
       data_at ARMLargePage (ptrFromPAddr ptr)"
| "valid_pte (SmallPagePTE ptr x y) =
       data_at ARMSmallPage (ptrFromPAddr ptr)"

primrec
  valid_pde :: "pde \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pde (InvalidPDE) = \<top>"
| "valid_pde (SectionPDE ptr x y) =
       data_at ARMSection (ptrFromPAddr ptr)"
| "valid_pde (SuperSectionPDE ptr x z) =
       data_at ARMSuperSection (ptrFromPAddr ptr)"
| "valid_pde (PageTablePDE ptr) =
       typ_at (AArch APageTable) (ptrFromPAddr ptr)"

definition
  valid_vcpu :: "vcpu \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_vcpu v \<equiv> case vcpu_tcb v of
  None \<Rightarrow> \<top>
| Some vt \<Rightarrow> typ_at ATCB vt"

primrec
  valid_vspace_obj :: "arch_kernel_obj \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_vspace_obj (ASIDPool pool) =
   (\<lambda>s. \<forall>x \<in> ran pool. typ_at (AArch APageDirectory) x s)"
| "valid_vspace_obj (PageDirectory pd) =
   (\<lambda>s. \<forall>x. valid_pde (pd x) s)"
| "valid_vspace_obj (PageTable pt) = (\<lambda>s. \<forall>x. valid_pte (pt x) s)"
| "valid_vspace_obj (DataPage dev sz) = \<top>"
| "valid_vspace_obj (VCPU v) = \<top>"

definition
  wellformed_pte :: "pte \<Rightarrow> bool"
where
  "wellformed_pte pte \<equiv> case pte of
     LargePagePTE p attr r \<Rightarrow>
       r \<in> valid_vm_rights \<and> vmsz_aligned p ARMLargePage
   | SmallPagePTE p attr r \<Rightarrow>
       r \<in> valid_vm_rights \<and> vmsz_aligned p ARMSmallPage
   | _ \<Rightarrow> True"

definition
  wellformed_pde :: "pde \<Rightarrow> bool"
where
  "wellformed_pde pde \<equiv> case pde of
     pde.PageTablePDE p \<Rightarrow>
       is_aligned p pt_bits
   | pde.SectionPDE p attr r \<Rightarrow>
       r \<in> valid_vm_rights \<and> vmsz_aligned p ARMSection
   | pde.SuperSectionPDE p attr r \<Rightarrow>
       r \<in> valid_vm_rights \<and> vmsz_aligned p ARMSuperSection
   | _ \<Rightarrow> True"

definition
  wellformed_vspace_obj :: "arch_kernel_obj \<Rightarrow> bool"
where
  "wellformed_vspace_obj ao \<equiv> case ao of
     PageTable pt \<Rightarrow> (\<forall>pte\<in>range pt. wellformed_pte pte)
   | PageDirectory pd \<Rightarrow> (\<forall>pde\<in>range pd. wellformed_pde pde)
   | _ \<Rightarrow> True"

definition
  arch_valid_obj :: "arch_kernel_obj \<Rightarrow>  'z::state_ext state \<Rightarrow> bool"
where
  "arch_valid_obj ao s \<equiv> case ao of
    VCPU v \<Rightarrow> valid_vcpu v s
   | _ \<Rightarrow> wellformed_vspace_obj ao"


lemmas
  wellformed_pte_simps[simp] =
  wellformed_pte_def[split_simps pte.split]

lemmas
  wellformed_pde_simps[simp] =
  wellformed_pde_def[split_simps pde.split]

lemmas
  wellformed_vspace_obj_simps[simp] =
  wellformed_vspace_obj_def[split_simps arch_kernel_obj.split]

lemmas
  arch_valid_obj_simps[simp] =
  arch_valid_obj_def[split_simps arch_kernel_obj.split]

lemma wellformed_arch_pspace: "\<And>ao. \<lbrakk>arch_valid_obj ao s; kheap s = kheap s'\<rbrakk>
          \<Longrightarrow> arch_valid_obj ao s'"
  apply (case_tac ao, simp_all)
  apply (simp add: obj_at_def valid_vcpu_def split: option.splits)
  done


section "Virtual Memory"

definition (* ARMHYP *)
  equal_kernel_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
 "equal_kernel_mappings \<equiv> \<top>"

definition
  pde_ref :: "pde \<Rightarrow> obj_ref option"
where
  "pde_ref pde \<equiv> case pde of
    PageTablePDE ptr\<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

text
\<open>Virtual address space look-ups
In the invariants, (ref \<unrhd> p) is a predicate on states which asserts the existence of a path through
the current virtual address space mappings, that is rooted in the global ASID table.

The ref is of type "vs_ref list", and represents the path through through the virtual address space
mappings. For example, it may look like this:

[VSRef r3 (Some APageTable), VSRef r2 (Some APageDirectory), VSRef r1 (Some AASIDPool), VSRef r0 None]

In this case:
r0 is the index of an entry in the global ASID table,
r1 is the index of an entry in the ASIDPool pointed to by r0,
r2 is the index of a page directory entry in the page directory mapped to the ASID formed by r0 and r1,
r3 is the index of a page table entry in the page table pointed to by r2.

Then, ((ref \<unrhd> p) s) is an assertion that: in state s, p is a pointer (in the kernel address space)
to a Page object mapped into the page table entry r3.

In this example, r0 and r1 are the high and low bits of the ASID. Similarly, r2 and r3 form parts of
the virtual address to which the page is mapped in this address space.

Note that the path is ordered bottom-up, from the object under consideration, up to the global ASID
table entry from which it can be traced.

A "vs_ref list" need not always trace from a Page object, so for example, ([VSRef r0 None] \<unrhd> p) s)
means: in state s, p is a pointer to an ASIDPool object, which was found in entry r0 of the global
ASID table.

There are also assertions of the form (ref \<rhd> p) which are similar, but don't trace any deeper than
page directory entries.\<close>

datatype vs_ref = VSRef word32 "aa_type option"

definition
  vs_ref_aatype :: "vs_ref \<Rightarrow> aa_type option" where
 "vs_ref_aatype vsref \<equiv> case vsref of VSRef x atype \<Rightarrow> atype"

definition
  vs_refs_arch :: "arch_kernel_obj \<Rightarrow> (vs_ref \<times> obj_ref) set" where
  "vs_refs_arch \<equiv> \<lambda>ko. case ko of
    ASIDPool pool \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  | PageDirectory pd \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p)) `
      graph_of (\<lambda>x. pde_ref (pd x))
  | _ \<Rightarrow> {}"

declare vs_refs_arch_def[simp]

definition
  "vs_refs = arch_obj_fun_lift vs_refs_arch {}"

type_synonym vs_chain = "vs_ref list \<times> obj_ref"
type_synonym 'a rel = "('a \<times> 'a) set"

definition
  vs_lookup1 :: "'z::state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup1 s \<equiv> {((rs,p),(rs',p')). \<exists>ko r. ko_at ko p s
                                      \<and> rs' = (r # rs)
                                      \<and> (r, p') \<in> vs_refs ko}"

abbreviation (input)
  vs_lookup_trans :: "'z::state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup_trans s \<equiv> (vs_lookup1 s)^*"

abbreviation
  vs_lookup1_abbr :: "vs_chain \<Rightarrow> vs_chain \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  ("_ \<rhd>1 _" [80,80] 81) where
  "ref \<rhd>1 ref' \<equiv> \<lambda>s. (ref,ref') \<in> vs_lookup1 s"

abbreviation
  vs_lookup_trans_abbr :: "vs_chain \<Rightarrow> vs_chain \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  ("_ \<rhd>* _" [80,80] 81) where
  "ref \<rhd>* ref' \<equiv> \<lambda>s. (ref,ref') \<in> vs_lookup_trans s"

definition
  vs_asid_refs :: "(7 word \<rightharpoonup> obj_ref) \<Rightarrow> vs_chain set"
where
  "vs_asid_refs t \<equiv> (\<lambda>(r,p). ([VSRef (ucast r) None], p)) ` graph_of t"

definition
  vs_lookup :: "'z::state_ext state \<Rightarrow> vs_chain set"
where
  "vs_lookup \<equiv> \<lambda>s. vs_lookup_trans s `` vs_asid_refs (arm_asid_table (arch_state s))"

definition
  second_level_tables :: "'a arch_state_scheme \<Rightarrow> obj_ref list"
where
  "second_level_tables \<equiv> \<lambda>s. []"

end

(* needed for abbreviation *)
arch_requalify_consts vs_lookup

abbreviation
  vs_lookup_abbr
  ("_ \<rhd> _" [80,80] 81) where
  "rs \<rhd> p \<equiv> \<lambda>s. (rs,p) \<in> vs_lookup s"

context Arch begin arch_global_naming

abbreviation
  is_reachable_abbr :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" ("\<exists>\<rhd> _" [80] 81) where
  "\<exists>\<rhd> p \<equiv> \<lambda>s. \<exists>ref. (ref \<rhd> p) s"

(* valid vspace object *)

definition
  valid_vspace_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_vspace_objs \<equiv>
  \<lambda>s. \<forall>p rs ao. (rs \<rhd> p) s \<longrightarrow> ko_at (ArchObj ao) p s \<longrightarrow> valid_vspace_obj ao s"

definition
  pde_ref_pages :: "pde \<Rightarrow> obj_ref option"
where
  "pde_ref_pages pde \<equiv> case pde of
    PageTablePDE ptr \<Rightarrow> Some (ptrFromPAddr ptr)
  | SectionPDE ptr x y \<Rightarrow> Some (ptrFromPAddr ptr)
  | SuperSectionPDE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  pte_ref_pages :: "pte \<Rightarrow> obj_ref option"
where
  "pte_ref_pages pte \<equiv> case pte of
    SmallPagePTE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | LargePagePTE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  vs_refs_pages_arch :: "arch_kernel_obj \<Rightarrow> (vs_ref \<times> obj_ref) set" where
  "vs_refs_pages_arch \<equiv> \<lambda>ko. case ko of
    (ASIDPool pool) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  | (PageDirectory pd) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p)) `
      graph_of (\<lambda>x. pde_ref_pages (pd x))
  | (PageTable pt) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageTable), p)) `
      graph_of (pte_ref_pages o pt)
  | _ \<Rightarrow> {}"

declare vs_refs_pages_arch_def[simp]

definition
  "vs_refs_pages \<equiv> arch_obj_fun_lift vs_refs_pages_arch {}"

definition
  vs_lookup_pages1 :: "'z :: state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup_pages1 s \<equiv> {((rs,p),(rs',p')). \<exists>ko r. ko_at ko p s
                                          \<and> rs' = (r # rs)
                                          \<and> (r, p') \<in> vs_refs_pages ko}"

abbreviation (input)
  vs_lookup_pages_trans :: "'z :: state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup_pages_trans s \<equiv> (vs_lookup_pages1 s)^*"

abbreviation
  vs_lookup_pages1_abbr :: "vs_chain \<Rightarrow> vs_chain \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool"
  ("_ \<unrhd>1 _" [80,80] 81) where
  "ref \<unrhd>1 ref' \<equiv> \<lambda>s. (ref,ref') \<in> vs_lookup_pages1 s"

abbreviation
  vs_lookup_pages_trans_abbr :: "vs_chain \<Rightarrow> vs_chain \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool"
  ("_ \<unrhd>* _" [80,80] 81) where
  "ref \<unrhd>* ref' \<equiv> \<lambda>s. (ref,ref') \<in> vs_lookup_pages_trans s"

definition
  vs_lookup_pages :: "'z ::state_ext state \<Rightarrow> vs_chain set"
where
  "vs_lookup_pages \<equiv> \<lambda>s. vs_lookup_pages_trans s `` vs_asid_refs (arm_asid_table (arch_state s))"


end

(* needed for abbreviation *)
arch_requalify_consts vs_lookup_pages

abbreviation
  vs_lookup_pages_abbr
  ("_ \<unrhd> _" [80,80] 81) where
  "rs \<unrhd> p \<equiv> \<lambda>s. (rs,p) \<in> vs_lookup_pages s"

abbreviation
  is_reachable_pages_abbr :: "obj_ref \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool" ("\<exists>\<unrhd> _" [80] 81) where
  "\<exists>\<unrhd> p \<equiv> \<lambda>s. \<exists>ref. (ref \<unrhd> p) s"


context Arch begin arch_global_naming

definition
  pde_mapping_bits :: "nat"
where
 "pde_mapping_bits \<equiv> pageBitsForSize ARMSection"

definition
  pte_mapping_bits :: "nat"
where
 "pte_mapping_bits \<equiv> pageBitsForSize ARMSmallPage"

definition (* ARMHYP? *)
  valid_pte_kernel_mappings :: "pte \<Rightarrow> vspace_ref
                                   \<Rightarrow> arm_vspace_region_uses \<Rightarrow> bool"
where
 "valid_pte_kernel_mappings pte vref uses \<equiv> case pte of
    InvalidPTE \<Rightarrow>
        \<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}.
                    uses x \<noteq> ArmVSpaceKernelWindow
  | SmallPagePTE ptr atts rghts \<Rightarrow>
        ptrFromPAddr ptr = vref
        \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}. uses x = use)
             \<and> (use = ArmVSpaceKernelWindow
                    \<or> use = ArmVSpaceDeviceWindow))
        \<and> rghts = {}
  | LargePagePTE ptr atts rghts \<Rightarrow>
        ptrFromPAddr ptr = (vref && ~~ mask (pageBitsForSize ARMLargePage))
        \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}. uses x = use)
             \<and> (use = ArmVSpaceKernelWindow
                    \<or> use = ArmVSpaceDeviceWindow))
        \<and> rghts = {}"

definition (* ARMHYP? *)
  valid_pt_kernel_mappings_arch :: "vspace_ref \<Rightarrow> arm_vspace_region_uses \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
where
 "valid_pt_kernel_mappings_arch vref uses \<equiv> \<lambda> obj. case obj of
    PageTable pt \<Rightarrow>
        \<forall>x. valid_pte_kernel_mappings
             (pt x) (vref + (ucast x << pte_mapping_bits)) uses
  | _ \<Rightarrow> False"

declare valid_pt_kernel_mappings_arch_def[simp]

definition (* ARMHYP? *)
  "valid_pt_kernel_mappings vref uses = arch_obj_fun_lift (valid_pt_kernel_mappings_arch vref uses) False"


definition (* ARMHYP? *)
  valid_pde_kernel_mappings :: "pde \<Rightarrow> vspace_ref \<Rightarrow> arm_vspace_region_uses \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "valid_pde_kernel_mappings pde vref uses \<equiv> case pde of
    InvalidPDE \<Rightarrow>
        (\<lambda>s. \<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}.
                    uses x \<noteq> ArmVSpaceKernelWindow)
  | PageTablePDE ptr \<Rightarrow>
        obj_at (valid_pt_kernel_mappings vref uses)
                    (ptrFromPAddr ptr)
  | SectionPDE ptr atts rghts \<Rightarrow>
        (\<lambda>s. ptrFromPAddr ptr = vref
             \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}. uses x = use)
                   \<and> (use = ArmVSpaceKernelWindow
                            \<or> use = ArmVSpaceDeviceWindow))
             \<and> rghts = {})
  | SuperSectionPDE ptr atts rghts \<Rightarrow>
        (\<lambda>s. ptrFromPAddr ptr = (vref && ~~ mask (pageBitsForSize ARMSuperSection))
             \<and> (\<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}.
                   uses x = ArmVSpaceKernelWindow)
             \<and> rghts = {})"

definition (* ARMHYP? *)
  valid_pd_kernel_mappings_arch :: "arm_vspace_region_uses \<Rightarrow> 'z::state_ext state
                                    \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
where
 "valid_pd_kernel_mappings_arch uses \<equiv> \<lambda>s obj.
  case obj of
    PageDirectory pd \<Rightarrow>
      (\<forall>x. valid_pde_kernel_mappings
             (pd x) (ucast x << pde_mapping_bits) uses s)
  | _ \<Rightarrow> False"

declare valid_pd_kernel_mappings_arch_def[simp]

definition (* ARMHYP? *)
  "valid_pd_kernel_mappings uses = (\<lambda>s. arch_obj_fun_lift (valid_pd_kernel_mappings_arch uses s) False)"

definition
  valid_global_vspace_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
 "valid_global_vspace_mappings \<equiv> \<top>"

definition
  valid_ao_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_ao_at p \<equiv> \<lambda>s. \<exists>ao. ko_at (ArchObj ao) p s \<and> (case ao of
    VCPU v \<Rightarrow> valid_vcpu v
  | _ \<Rightarrow> valid_vspace_obj ao) s"

fun
  is_vspace_typ :: "a_type \<Rightarrow> bool"
where
  "is_vspace_typ (AArch AVCPU) = False"
| "is_vspace_typ (AArch  _)    = True"
| "is_vspace_typ  _            = False"

definition
  valid_vso_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_vso_at p \<equiv> \<lambda>s. \<exists>ao. ko_at (ArchObj ao) p s \<and> valid_vspace_obj ao s
                                                     \<and> is_vspace_typ (AArch (aa_type ao))"

definition
  "valid_pde_mappings pde \<equiv> case pde of
    SectionPDE ptr _ _ \<Rightarrow> is_aligned ptr pageBits
  | SuperSectionPDE ptr _ _ \<Rightarrow> is_aligned ptr pageBits
  | _ \<Rightarrow> True"

definition (* ARMHYP+ *)
  "empty_table_arch S \<equiv> \<lambda> ko.
   case ko of
     PageDirectory pd \<Rightarrow>
       \<forall>x. (\<forall>r. pde_ref (pd x) = Some r \<longrightarrow> r \<in> S) \<and>
            valid_pde_mappings (pd x) \<and> (pd x = InvalidPDE)
   | PageTable pt \<Rightarrow> \<forall>x. pt x = InvalidPTE
   | _ \<Rightarrow> False"

declare empty_table_arch_def[simp]

definition
  "empty_table S \<equiv> arch_obj_fun_lift (empty_table_arch S) False"

definition
  "aligned_pte pte \<equiv>
     case pte of
       LargePagePTE p _ _ \<Rightarrow> vmsz_aligned p ARMLargePage
     | SmallPagePTE p _ _ \<Rightarrow> vmsz_aligned p ARMSmallPage
     | _ \<Rightarrow> True"

lemmas aligned_pte_simps[simp] =
       aligned_pte_def[split_simps pte.split]



definition
  valid_global_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_global_objs \<equiv> \<top>"

definition
  valid_asid_table :: "(7 word \<rightharpoonup> obj_ref) \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_asid_table table \<equiv> \<lambda>s. (\<forall>p \<in> ran table. asid_pool_at p s) \<and>
                                inj_on table (dom table)"


definition
  arch_live :: "arch_kernel_obj \<Rightarrow> bool"
where
  "arch_live ao \<equiv> case ao of
    ARM_HYP_A.VCPU v \<Rightarrow> bound (ARM_HYP_A.vcpu_tcb v)
    | _ \<Rightarrow>  False"

definition
  hyp_live :: "kernel_object \<Rightarrow> bool"
where
  "hyp_live ko \<equiv> case ko of
  (TCB tcb) \<Rightarrow> bound (tcb_vcpu (tcb_arch tcb))
| (ArchObj ao) \<Rightarrow> arch_live ao
|  _ \<Rightarrow> False"


definition
  is_vcpu :: "kernel_object \<Rightarrow> bool"
where
  "is_vcpu \<equiv> \<lambda>ko. \<exists>vcpu. ko = ArchObj (VCPU vcpu)"

definition
  valid_arch_state :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_state \<equiv> \<lambda>s.
  valid_asid_table (arm_asid_table (arch_state s)) s \<and>
  (case arm_current_vcpu (arch_state s) of
     Some (v, b) \<Rightarrow> obj_at (is_vcpu and hyp_live) v s
   | _ \<Rightarrow> True) \<and>
  is_inv (arm_hwasid_table (arch_state s)) (option_map fst o arm_asid_map (arch_state s))"

definition
  vs_cap_ref_arch :: "arch_cap \<Rightarrow> vs_ref list option"
where
  "vs_cap_ref_arch \<equiv> \<lambda> cap. case cap of
   ASIDPoolCap _ asid \<Rightarrow>
     Some [VSRef (ucast (asid_high_bits_of asid)) None]
 | PageDirectoryCap _ (Some asid) \<Rightarrow>
     Some [VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageTableCap _ (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef (vptr >> pageBits + pt_bits - pte_bits) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageCap dev word rights ARMSmallPage (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> pageBits) && mask (pt_bits - pte_bits)) (Some APageTable),
           VSRef (vptr >> pageBits + pt_bits - pte_bits) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageCap dev word rights ARMLargePage (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> pageBits) && mask (pt_bits - pte_bits)) (Some APageTable),
           VSRef (vptr >> pageBits + pt_bits - pte_bits) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageCap dev word rights ARMSection (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef (vptr >> pageBits + pt_bits - pte_bits) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageCap dev word rights ARMSuperSection (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef (vptr >> pageBits + pt_bits - pte_bits) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | _ \<Rightarrow> None"

declare vs_cap_ref_arch_def[simp]

definition
  "vs_cap_ref cap \<equiv> arch_cap_fun_lift vs_cap_ref_arch None cap"

definition
  "is_pg_cap cap \<equiv> \<exists>dev p R sz m. cap = ArchObjectCap (PageCap dev p R sz m)"

definition
  "is_pd_cap c \<equiv>
   \<exists>p asid. c = ArchObjectCap (PageDirectoryCap p asid)"

definition
  "is_pt_cap c \<equiv> \<exists>p asid. c = ArchObjectCap (PageTableCap p asid)"

lemma is_arch_cap_simps:
  "is_pg_cap cap = (\<exists>dev p R sz m. cap = (ArchObjectCap (PageCap dev p R sz m)))"
  "is_pd_cap cap = (\<exists>p asid. cap = (ArchObjectCap (PageDirectoryCap p asid)))"
  "is_pt_cap cap = (\<exists>p asid. cap = (ArchObjectCap (PageTableCap p asid)))"
  by (auto simp add: is_pg_cap_def is_pd_cap_def is_pt_cap_def)

definition
  "cap_asid_arch cap \<equiv> case cap of
    PageCap _ _ _ _ (Some (asid, _)) \<Rightarrow> Some asid
  | PageTableCap _ (Some (asid, _)) \<Rightarrow> Some asid
  | PageDirectoryCap _ (Some asid) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

declare cap_asid_arch_def[abs_def, simp]

definition
  "cap_asid cap = arch_cap_fun_lift cap_asid_arch None cap"


  (* needed for retype: if reachable, then cap, if cap then protected by untyped cap.
     strengthened for preservation in cap delete: ref in cap must unmap the right objects *)
definition
  "valid_vs_lookup \<equiv> \<lambda>s. \<forall>p ref. (ref \<unrhd> p) s \<longrightarrow>
  ref \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None] \<and>
  (\<exists>p' cap. (caps_of_state s) p' = Some cap \<and>
            p \<in> obj_refs cap \<and> vs_cap_ref cap = Some ref)"

definition
  global_refs :: "'z::state_ext state \<Rightarrow> obj_ref set"
where
  "global_refs \<equiv> \<lambda>s.
  {idle_thread s, arm_us_global_pd (arch_state s)} \<union>
   range (interrupt_irq_node s)"

definition
  not_kernel_window_arch :: "arch_state \<Rightarrow> obj_ref set"
where
  "not_kernel_window_arch s \<equiv> {x. arm_kernel_vspace s x \<noteq> ArmVSpaceKernelWindow}"

declare not_kernel_window_arch_def[simp]

abbreviation
  not_kernel_window :: "'z::state_ext state \<Rightarrow> obj_ref set"
where
  "not_kernel_window s \<equiv> not_kernel_window_arch (arch_state s)"


  (* needed for map: installing new object should add only one mapping *)
definition
  "valid_table_caps \<equiv> \<lambda>s.
  \<forall>r p cap. (caps_of_state s) p = Some cap \<longrightarrow>
            (is_pd_cap cap \<or> is_pt_cap cap) \<longrightarrow>
            cap_asid cap = None \<longrightarrow>
            r \<in> obj_refs cap \<longrightarrow>
            obj_at (empty_table {}) r s"

  (* needed to preserve valid_table_caps in map *)
definition
  "unique_table_caps \<equiv> \<lambda>cs. \<forall>p p' cap cap'.
  cs p = Some cap \<longrightarrow> cs p' = Some cap' \<longrightarrow>
  cap_asid cap = None \<longrightarrow>
  obj_refs cap' = obj_refs cap \<longrightarrow>
  (is_pd_cap cap \<longrightarrow> is_pd_cap cap' \<longrightarrow> p' = p) \<and>
  (is_pt_cap cap \<longrightarrow> is_pt_cap cap' \<longrightarrow> p' = p)"

definition
  table_cap_ref_arch :: "arch_cap \<Rightarrow> vs_ref list option"
where
  "table_cap_ref_arch \<equiv> \<lambda> cap. case cap of
     ASIDPoolCap _ asid \<Rightarrow>
       Some [VSRef (ucast (asid_high_bits_of asid)) None]
   | PageDirectoryCap _ (Some asid) \<Rightarrow>
       Some [VSRef (asid && mask asid_low_bits) (Some AASIDPool),
             VSRef (ucast (asid_high_bits_of asid)) None]
   | PageTableCap _ (Some (asid, vptr)) \<Rightarrow>
       Some [VSRef (vptr >> pageBits + pt_bits - pte_bits) (Some APageDirectory),
             VSRef (asid && mask asid_low_bits) (Some AASIDPool),
             VSRef (ucast (asid_high_bits_of asid)) None]
   | _ \<Rightarrow> None"

declare table_cap_ref_arch_def[simp]

definition
  "table_cap_ref cap = arch_cap_fun_lift table_cap_ref_arch None cap"

  (* needed to avoid a single page insertion
     resulting in multiple valid lookups *)
definition
  "unique_table_refs \<equiv> \<lambda>cs. \<forall>p p' cap cap'.
  cs p = Some cap \<longrightarrow> cs p' = Some cap' \<longrightarrow>
  obj_refs cap' = obj_refs cap \<longrightarrow>
  table_cap_ref cap' = table_cap_ref cap"

definition
  valid_kernel_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_kernel_mappings \<equiv> \<top>"  (* ARMHYP *)

definition
  "valid_arch_caps \<equiv> valid_vs_lookup and valid_table_caps and
                     (\<lambda>s. unique_table_caps  (caps_of_state s)
                        \<and> unique_table_refs (caps_of_state s))"


text "objects live in the kernel window"
definition
  pspace_in_kernel_window :: "'z::state_ext state \<Rightarrow> bool"
where
 "pspace_in_kernel_window \<equiv> \<lambda>s.
    \<forall>x ko. kheap s x = Some ko \<longrightarrow>
       (\<forall>y \<in> {x .. x + (2 ^ obj_bits ko) - 1}.
             arm_kernel_vspace (arch_state s) y = ArmVSpaceKernelWindow)"

definition
  arch_obj_bits_type :: "aa_type \<Rightarrow> nat"
where
 "arch_obj_bits_type T' \<equiv> (case T' of
    AASIDPool \<Rightarrow> arch_kobj_size (ASIDPool undefined)
  | ADeviceData sz \<Rightarrow> arch_kobj_size (DataPage True sz)
  | AUserData sz \<Rightarrow> arch_kobj_size (DataPage False sz)
  | APageDirectory \<Rightarrow> arch_kobj_size (PageDirectory undefined)
  | APageTable \<Rightarrow> arch_kobj_size (PageTable undefined)
  | AVCPU \<Rightarrow> arch_kobj_size (VCPU undefined))" (* ARMHYP *)

definition
  vspace_at_asid :: "asid \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "vspace_at_asid asid pd \<equiv> \<lambda>s.
         ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd) s"

definition
  valid_asid_map :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_asid_map \<equiv>
   \<lambda>s. dom (arm_asid_map (arch_state s)) \<subseteq> {0 .. mask asid_bits} \<and>
       (\<forall>(asid, hwasid, pd) \<in> graph_of (arm_asid_map (arch_state s)).
            vspace_at_asid asid pd s \<and> asid \<noteq> 0)"

definition
  "valid_arch_mdb r cs \<equiv> True"

declare valid_arch_mdb_def[simp]

section "Lemmas"

lemma vmsz_aligned_ARMSection:
  "vmsz_aligned vref ARMSection = is_aligned vref (pageBitsForSize ARMSection)"
  by (simp add: vmsz_aligned_def pageBitsForSize_def)

lemma valid_arch_cap_def2:
  "valid_arch_cap c s \<equiv> wellformed_acap c \<and> valid_arch_cap_ref c s"
  apply (rule eq_reflection)
  apply (cases c)
    by (auto simp add: wellformed_acap_simps valid_arch_cap_simps
                       valid_arch_cap_ref_simps vmsz_aligned_ARMSection
                split: option.splits)

lemmas vs_ref_aatype_simps[simp] = vs_ref_aatype_def[split_simps vs_ref.split]

lemma vs_lookup1_obj_at:
  "((rs,p) \<rhd>1 (r # rs,p')) s = obj_at (\<lambda>ko. (r, p') \<in> vs_refs ko) p s"
  by (fastforce simp: vs_lookup1_def obj_at_def)

lemma vs_lookup1I:
  "\<lbrakk> ko_at ko p s; (r, p') \<in> vs_refs ko;
          rs' = r # rs \<rbrakk> \<Longrightarrow> ((rs,p) \<rhd>1 (rs',p')) s"
  by (fastforce simp add: vs_lookup1_def)

lemma vs_lookup1D:
  "(x \<rhd>1 y) s \<Longrightarrow> \<exists>rs r p p' ko. x = (rs,p) \<and> y = (r # rs,p')
                          \<and> ko_at ko p s \<and> (r,p') \<in> vs_refs ko"
  by (cases x, cases y) (fastforce simp: vs_lookup1_def)

lemma vs_lookup_pages1D:
  "(x \<unrhd>1 y) s \<Longrightarrow> \<exists>rs r p p' ko. x = (rs,p) \<and> y = (r # rs,p')
                          \<and> ko_at ko p s \<and> (r,p') \<in> vs_refs_pages ko"
  by (cases x, cases y) (fastforce simp: vs_lookup_pages1_def)

lemma vs_lookup1_stateI:
  assumes 1: "(r \<rhd>1 r') s"
  assumes ko: "\<And>ko. ko_at ko (snd r) s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') (snd r) s'"
  shows "(r \<rhd>1 r') s'" using 1 ko
  by (fastforce simp: obj_at_def vs_lookup1_def)

lemma vs_lookup_pages1_stateI2:
  assumes 1: "(r \<unrhd>1 r') s"
  assumes ko: "\<And>ko. \<lbrakk> ko_at ko (snd r) s; vs_refs_pages ko \<noteq> {} \<rbrakk>
               \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') (snd r) s'"
  shows "(r \<unrhd>1 r') s'" using 1 ko
  by (fastforce simp: obj_at_def vs_lookup_pages1_def)

lemma vs_lookup_trans_sub:
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  shows "vs_lookup_trans s \<subseteq> vs_lookup_trans s'"
proof -
  have "vs_lookup1 s \<subseteq> vs_lookup1 s'"
    by (fastforce dest: ko elim: vs_lookup1_stateI)
  thus ?thesis by (rule rtrancl_mono)
qed

lemma vs_lookup_sub:
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup s \<subseteq> vs_lookup s'"
  unfolding vs_lookup_def
  apply (rule Image_mono)
   apply (rule vs_lookup_trans_sub)
   apply (erule ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
  done

lemma vs_lookup_pages1_stateI:
  assumes 1: "(r \<unrhd>1 r') s"
  assumes ko: "\<And>ko. ko_at ko (snd r) s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') (snd r) s'"
  shows "(r \<unrhd>1 r') s'" using 1 ko
  by (fastforce simp: obj_at_def vs_lookup_pages1_def)

lemma vs_lookup_pages_trans_sub:
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow>
                      obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  shows "vs_lookup_pages_trans s \<subseteq> vs_lookup_pages_trans s'"
proof -
  have "vs_lookup_pages1 s \<subseteq> vs_lookup_pages1 s'"
    by (fastforce simp add: ko elim: vs_lookup_pages1_stateI)
  thus ?thesis by (rule rtrancl_mono)
qed

lemma vs_lookup_pages_sub:
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow>
                      obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  assumes table:
    "graph_of (arm_asid_table (arch_state s)) \<subseteq>
     graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup_pages s \<subseteq> vs_lookup_pages s'"
  unfolding vs_lookup_pages_def
  apply (rule Image_mono)
   apply (rule vs_lookup_pages_trans_sub)
   apply (erule ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
  done

lemma vs_lookup_pagesI:
  "\<lbrakk> ref' \<in> vs_asid_refs (arm_asid_table (arch_state s));
     (ref',(ref,p)) \<in> (vs_lookup_pages1 s)^*  \<rbrakk> \<Longrightarrow>
  (ref \<unrhd> p) s"
  by (simp add: vs_lookup_pages_def) blast

lemma vs_lookup_stateI:
  assumes 1: "(ref \<rhd> p) s"
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "(ref \<rhd> p) s'"
  using 1 vs_lookup_sub [OF ko table] by blast


lemma valid_vspace_objsD:
  "\<lbrakk> (ref \<rhd> p) s; ko_at (ArchObj ao) p s; valid_vspace_objs s \<rbrakk> \<Longrightarrow> valid_vspace_obj ao s"
  by (fastforce simp add: valid_vspace_objs_def)

lemma valid_vspace_objs_stateI:
  assumes 1: "valid_vspace_objs s"
  assumes ko: "\<And>ko p. ko_at ko p s' \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s"
  assumes arch: "graph_of (arm_asid_table (arch_state s')) \<subseteq> graph_of (arm_asid_table (arch_state s))"
  assumes vao: "\<And>p ref ao'.
                \<lbrakk> (ref \<rhd> p) s; (ref \<rhd> p) s'; \<forall>ao. ko_at (ArchObj ao) p s \<longrightarrow> valid_vspace_obj ao s;
                  ko_at (ArchObj ao') p s' \<rbrakk> \<Longrightarrow> valid_vspace_obj ao' s'"
  shows "valid_vspace_objs s'"
  using 1 unfolding valid_vspace_objs_def
  apply clarsimp
  apply (frule vs_lookup_stateI)
    apply (erule ko)
   apply (rule arch)
  apply (erule allE, erule impE, fastforce)
  apply (erule (3) vao)
  done

lemma valid_arch_cap_typ:
  assumes P: "\<And>T p. \<lbrace>\<lambda>s. (typ_at (AArch T) p s )\<rbrace> f \<lbrace>\<lambda>rv s. (typ_at (AArch T) p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_arch_cap c s\<rbrace> f \<lbrace>\<lambda>rv s. valid_arch_cap c s\<rbrace>"
  apply (simp add: valid_arch_cap_def)
  apply (case_tac c, simp_all)
  apply (wp P hoare_vcg_ball_lift hoare_vcg_imp_lift hoare_vcg_conj_lift | clarsimp)+
  done

definition is_avcpu_aatyp :: "arch_kernel_obj \<Rightarrow> bool"
where "is_avcpu_aatyp ob \<equiv> aa_type ob = AVCPU"

lemma valid_vspace_obj_typ:
  assumes P: "\<And>p T. \<lbrace>\<lambda>s. (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s.  (typ_at (AArch T) p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_vspace_obj ob s\<rbrace> f \<lbrace>\<lambda>rv s. valid_vspace_obj ob s\<rbrace>"
  apply (cases ob, simp_all add: aa_type_def)
      apply (rule hoare_vcg_const_Ball_lift [OF P])
     apply (rule hoare_vcg_all_lift)
     apply (rename_tac "fun" x)
     apply (case_tac "fun x"; simp_all add: data_at_def hoare_vcg_prop P)
      apply (wp hoare_vcg_disj_lift P)+
    apply (rule hoare_vcg_all_lift)
    apply (rename_tac "fun" x)
    apply (case_tac "fun x";simp_all add: data_at_def hoare_vcg_prop P)
     apply (wp hoare_vcg_disj_lift P)+
done

lemma atyp_at_eq_kheap_obj:
  "typ_at (AArch AASIDPool) p s \<longleftrightarrow> (\<exists>f. kheap s p = Some (ArchObj (ASIDPool f)))"
  "typ_at (AArch APageTable) p s \<longleftrightarrow> (\<exists>pt. kheap s p = Some (ArchObj (PageTable pt)))"
  "typ_at (AArch APageDirectory) p s \<longleftrightarrow> (\<exists>pd. kheap s p = Some (ArchObj (PageDirectory pd)))"
  "typ_at (AArch (AUserData sz)) p s \<longleftrightarrow> (kheap s p = Some (ArchObj (DataPage False sz)))"
  "typ_at (AArch (ADeviceData sz)) p s \<longleftrightarrow> (kheap s p = Some (ArchObj (DataPage True sz)))"
  "typ_at (AArch AVCPU) p s \<longleftrightarrow> (\<exists>v. kheap s p = Some (ArchObj (VCPU v)))" (* ARMHYP *)
  apply (auto simp add: obj_at_def)
  apply (simp_all add: a_type_def
                split: if_split_asm kernel_object.splits arch_kernel_obj.splits)
  done

lemmas kernel_object_exhaust =
  kernel_object.exhaust
    [rotated -1, OF arch_kernel_obj.exhaust, of _ "\<lambda>x. x", simplified]

lemma shows
  aa_type_AASIDPoolE:
  "\<lbrakk>a_type ko = AArch AASIDPool;
    (\<And>ap. ko = ArchObj (ASIDPool ap) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R" and
  aa_type_APageDirectoryE:
  "\<lbrakk>a_type ko = AArch APageDirectory;
    (\<And>pd. ko = ArchObj (PageDirectory pd) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R" and
   aa_type_APageTableE:
  "\<lbrakk>a_type ko = AArch APageTable; (\<And>pt. ko = ArchObj (PageTable pt) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R" and
   aa_type_ADeviceDataE:
  "\<lbrakk>a_type ko = AArch (ADeviceData sz); ko = ArchObj (DataPage True sz) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and
   aa_type_AUserDataE:
  "\<lbrakk>a_type ko = AArch (AUserData sz); ko = ArchObj (DataPage False sz) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and
   aa_type_AVCPUE:
  "\<lbrakk>a_type ko = AArch AVCPU; \<And>v. ko = ArchObj (VCPU v) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" (* ARMHYP *)
by (rule kernel_object_exhaust[of ko]; clarsimp simp add: a_type_simps split: if_split_asm)+

lemmas aa_type_elims[elim!] =
   aa_type_AASIDPoolE aa_type_APageDirectoryE aa_type_APageTableE aa_type_ADeviceDataE aa_type_AUserDataE aa_type_AVCPUE

lemma wellformed_arch_typ:
   assumes P: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
   shows   "\<lbrace>\<lambda>s. arch_valid_obj ao s\<rbrace> f \<lbrace>\<lambda>rv s. arch_valid_obj ao s\<rbrace>"
  apply (cases ao; clarsimp simp: valid_vcpu_def split: option.splits; wp?)
  apply (rule conjI; clarsimp; wp P)
done

lemma valid_vspace_obj_pspaceI:
  "\<lbrakk> valid_vspace_obj obj s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_vspace_obj obj s'"
  apply (cases obj, simp_all)
     apply (simp add: obj_at_def)
    apply (erule allEI)
    apply (rename_tac "fun" x)
    apply (case_tac "fun x", simp_all add: obj_at_def data_at_def)
   apply (erule allEI)
   apply (rename_tac "fun" x)
   apply (case_tac "fun x", simp_all add: obj_at_def data_at_def)
  done

lemmas  pageBitsForSize_simps[simp] =
        pageBitsForSize_def[split_simps vmpage_size.split]

lemma arch_kobj_size_bounded:
  "arch_kobj_size obj < word_bits"
  apply (cases obj, simp_all add: word_bits_conv pageBits_def pt_bits_def pd_bits_def pte_bits_def pde_bits_def vcpu_bits_def)
  apply (rename_tac vmpage_size)
  apply (case_tac vmpage_size, simp_all)
  done

lemma valid_arch_sizes:
  "obj_bits (ArchObj obj) < word_bits"
  by (simp add: arch_kobj_size_bounded)

lemma aobj_bits_T:
  "arch_kobj_size v = arch_obj_bits_type (aa_type v)"
  unfolding arch_obj_bits_type_def aa_type_def
  by (cases v; simp)

lemma idle_global:
  "idle_thread s \<in> global_refs s"
  by (simp add: global_refs_def)

lemma valid_ipc_buffer_cap_null:
  "valid_ipc_buffer_cap NullCap buf"
  by (simp add: valid_ipc_buffer_cap_def)

lemma pageBits_clb_less_word_bits [simp]:
  "pageBits - cte_level_bits < word_bits"
  by (rule less_imp_diff_less, simp)

end

context Arch_pspace_update_eq begin

lemma in_user_frame_update[iff]:
  "in_user_frame p (f s) = in_user_frame p s"
  by (simp add: in_user_frame_def pspace)

lemma in_device_frame_update[iff]:
  "in_device_frame p (f s) = in_device_frame p s"
  by (simp add: in_device_frame_def obj_at_def pspace)

lemma obj_at_update [iff]:
  "obj_at P p (f s) = obj_at P p s"
  by (fastforce intro: obj_at_pspaceI simp: pspace)

lemma valid_asid_table_update [iff]:
  "valid_asid_table t (f s) = valid_asid_table t s"
  by (simp add: valid_asid_table_def)

lemma valid_pte_update [iff]:
  "valid_pte pte (f s) = valid_pte pte s"
  by (cases pte) (auto simp: data_at_def)

lemma valid_pde_update [iff]:
  "valid_pde pde (f s) = valid_pde pde s"
  by (cases pde) (auto simp: data_at_def)

lemma valid_vcpu_update [iff]:
  "valid_vcpu v (f s) = valid_vcpu v s"
  by (case_tac "vcpu_tcb v") (auto simp: valid_vcpu_def)

lemma valid_vspace_obj_update [iff]:
  "valid_vspace_obj ao (f s) = valid_vspace_obj ao s"
  by (cases ao) auto

lemma valid_ao_at_update [iff]:
  "valid_ao_at p (f s) = valid_ao_at p s"
  by (simp add: valid_ao_at_def split: arch_kernel_obj.split)

lemma valid_vso_at_update [iff]:
  "valid_vso_at p (f s) = valid_vso_at p s"
  by (simp add: valid_vso_at_def)

lemma equal_kernel_mappings_update [iff]:
  "equal_kernel_mappings (f s) = equal_kernel_mappings s"
  by (simp add: equal_kernel_mappings_def)

lemma valid_pt_kernel_mappings [iff]:
  "valid_pde_kernel_mappings pde vref uses (f s)
      = valid_pde_kernel_mappings pde vref uses s"
  by (cases pde, simp_all add: valid_pde_kernel_mappings_def)

lemma valid_pd_kernel_mappings [iff]:
  "valid_pd_kernel_mappings uses (f s)
      = valid_pd_kernel_mappings uses s"
  by (rule ext, simp add: valid_pd_kernel_mappings_def)


(* FIXME: Clagged *)
lemma get_cap_update [iff]:
  "(fst (get_cap p (f s)) = {(cap, f s)}) = (fst (get_cap p s) = {(cap, s)})"
  apply (simp add: get_cap_def get_object_def bind_assoc
                   exec_gets split_def assert_def pspace)
  apply (clarsimp simp: fail_def)
  apply (case_tac y, simp_all add: assert_opt_def split: option.splits)
      apply (simp_all add: return_def fail_def assert_def bind_def)
  done

(* FIXME: Clagged *)
lemma caps_of_state_update [iff]:
  "caps_of_state (f s) = caps_of_state s"
  by (rule ext) (auto simp: caps_of_state_def)

lemma arch_valid_obj_update:
  "\<And>ao. b = ArchObj ao \<Longrightarrow> arch_valid_obj ao (f s) = arch_valid_obj ao s"
  apply (case_tac ao;
         clarsimp simp: valid_vcpu_def
                  cong: option.case_cong split: option.splits)
  done

end

context Arch_arch_idle_update_eq begin

lemma global_refs_update [iff]:
  "global_refs (f s) = global_refs s"
  by (simp add: global_refs_def arch idle irq)

end

context Arch_p_arch_update_eq begin

lemma vs_lookup1_update [iff]:
  "vs_lookup1 (f s) = vs_lookup1 s"
  by (simp add: vs_lookup1_def)

lemma vs_lookup_trans_update [iff]:
  "vs_lookup_trans (f s) = vs_lookup_trans s"
  by simp

lemma vs_lookup_update [iff]:
  "vs_lookup (f s) = vs_lookup s"
  by (simp add: vs_lookup_def arch)

lemma vs_lookup_pages1_update [iff]:
  "vs_lookup_pages1 (f s) = vs_lookup_pages1 s"
  by (simp add: vs_lookup_pages1_def)

lemma vs_lookup_pages_trans_update [iff]:
  "vs_lookup_pages_trans (f s) = vs_lookup_pages_trans s"
  by simp

lemma vs_lookup_pages_update [iff]:
  "vs_lookup_pages (f s) = vs_lookup_pages s"
  by (simp add: vs_lookup_pages_def arch)

lemma valid_vs_lookup_update [iff]:
  "valid_vs_lookup (f s) = valid_vs_lookup s"
  by (simp add: valid_vs_lookup_def arch)

lemma valid_table_caps_update [iff]:
  "valid_table_caps (f s) = valid_table_caps s"
  by (simp add: valid_table_caps_def arch)

lemma valid_vspace_objs_update' [iff]:
  "valid_vspace_objs (f s) = valid_vspace_objs s"
  by (simp add: valid_vspace_objs_def)

end

context Arch begin arch_global_naming

lemma global_refs_equiv:
  assumes "idle_thread s = idle_thread s'"
  assumes "interrupt_irq_node s = interrupt_irq_node s'"
  assumes "arm_us_global_pd (arch_state s) = arm_us_global_pd (arch_state s')"
  shows "global_refs s = global_refs s'"
  by (simp add: assms global_refs_def)

lemma global_refs_lift:
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  assumes idle: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  assumes irq: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> f \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (global_refs s) \<rbrace> f \<lbrace>\<lambda>r s. P (global_refs s) \<rbrace>"
  unfolding global_refs_def
  apply (rule hoare_lift_Pf [where f="arch_state", OF _ arch])
  apply (rule hoare_lift_Pf [where f="idle_thread", OF _ idle])
  apply (rule hoare_lift_Pf [where f="interrupt_irq_node", OF _ irq])
  apply (rule hoare_vcg_prop)
  done

lemma valid_arch_state_lift:
  assumes typs: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>_. typ_at (AArch T) p\<rbrace>"
  assumes vcpus: "\<And>p. \<lbrace>obj_at (is_vcpu and hyp_live) p\<rbrace> f \<lbrace>\<lambda>_. obj_at (is_vcpu and hyp_live) p\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>valid_arch_state\<rbrace> f \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (simp add: valid_arch_state_def valid_asid_table_def)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. arch_state s"])
   apply (case_tac "arm_current_vcpu x"; simp add: split_def)
    apply (wp arch vcpus typs hoare_vcg_conj_lift hoare_vcg_const_Ball_lift)+
  done

lemma aobj_at_default_arch_cap_valid:
  assumes "ty \<noteq> ASIDPoolObj"
  assumes "ko_at (ArchObj (default_arch_object ty dev us)) x s"
  shows "valid_arch_cap (arch_default_cap ty x us dev) s"
  using assms
  by (auto elim!: obj_at_weakenE
        simp add: arch_default_cap_def valid_arch_cap_def default_arch_object_def
                  a_type_def
                  valid_vm_rights_def
           split: apiobject_type.splits aobject_type.splits option.splits)

lemma aobj_ref_default:
  "aobj_ref (arch_default_cap x6 x us dev) = Some x"
  by (auto simp add: arch_default_cap_def split: aobject_type.splits)

lemma valid_pde_lift:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_pde pde s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pde pde s\<rbrace>"
  by (cases pde) (simp add: data_at_def | wp x hoare_vcg_disj_lift)+

lemma valid_pte_lift:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_pte pte s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pte pte s\<rbrace>"
  by (cases pte) (simp add: data_at_def | wp x hoare_vcg_disj_lift)+

lemma pde_at_atyp:
  assumes x: "\<And>p T. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows      "\<lbrace>pde_at p\<rbrace> f \<lbrace>\<lambda>rv. pde_at p\<rbrace>"
  by (simp add: pde_at_def | wp x)+

lemma pte_at_atyp:
  assumes x: "\<And>p T. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows      "\<lbrace>pte_at p\<rbrace> f \<lbrace>\<lambda>rv. pte_at p\<rbrace>"
  by (simp add: pte_at_def | wp x)+

lemmas abs_atyp_at_lifts =
  valid_pde_lift valid_pte_lift
  pde_at_atyp pte_at_atyp

lemma page_directory_pde_atI:  (* ARMHYP: x < 2 ^ pageBits? *)
  "\<lbrakk> page_directory_at p s; x < 2 ^ (pd_bits - pde_bits);
         pspace_aligned s \<rbrakk> \<Longrightarrow> pde_at (p + (x << pde_bits)) s"
  apply (clarsimp simp: obj_at_def pde_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def
                 split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self word_bits_conv pd_bits_def)
  apply (subgoal_tac "p = (p + (x << pde_bits) && ~~ mask pd_bits)")
   subgoal by (auto simp add: pd_bits_def)
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: pd_bits_def pageBits_def pde_bits_def)
  apply (simp del: bit_shiftl_iff bit_shiftl_word_iff)
  apply (subst upper_bits_unset_is_l2p_32[unfolded word_bits_conv])
   apply (simp add: pd_bits_def pde_bits_def pageBits_def)
  apply (rule shiftl_less_t2n)
   apply (auto simp add: pd_bits_def pde_bits_def pageBits_def)
  done


lemma page_table_pte_atI:  (* ARMHYP: x < 2 ^ (pt_bits - 2) *)
  "\<lbrakk> page_table_at p s; x < 2^(pt_bits - pte_bits); pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at (p + (x << pte_bits)) s"
  apply (clarsimp simp: obj_at_def pte_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def
                 split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self word_bits_conv pt_bits_def)
  apply (subgoal_tac "p = (p + (x << pte_bits) && ~~ mask pt_bits)")
   subgoal by (auto simp add: pt_bits_def)
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: pt_bits_def pageBits_def pte_bits_def)
  apply (simp del: bit_shiftl_iff bit_shiftl_word_iff)
  apply (subst upper_bits_unset_is_l2p_32[unfolded word_bits_conv])
   apply (simp add: pt_bits_def pageBits_def pte_bits_def)
  apply (rule shiftl_less_t2n)
   apply (auto simp add: pt_bits_def pageBits_def pte_bits_def)
  done

lemma physical_arch_cap_has_ref:
  "(acap_class arch_cap = PhysicalClass) = (\<exists>y. aobj_ref arch_cap = Some y)"
  by (cases arch_cap; simp)


subsection "vs_lookup"

lemma vs_lookup1_ko_at_dest:  (* ARMHYP *)
  "\<lbrakk> ((ref, p) \<rhd>1 (ref', p')) s; ko_at (ArchObj ao) p s; valid_vspace_obj ao s \<rbrakk> \<Longrightarrow>
  \<exists>ao'. ko_at (ArchObj ao') p' s \<and> (\<exists>tp. vs_ref_aatype (hd ref') = Some tp
                                            \<and> aa_type ao = tp)"
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def)
  apply (cases ao, simp_all add: graph_of_def)
   apply clarsimp
   apply (drule bspec, fastforce simp: ran_def)
   apply (clarsimp simp add: aa_type_def obj_at_def)
  apply (clarsimp split: arch_kernel_obj.split_asm if_split_asm)
  apply (simp add: pde_ref_def aa_type_def
            split: pde.splits)
  apply (erule_tac x=a in allE)
  apply (clarsimp simp add: obj_at_def)
  done

lemma vs_lookup1_is_arch:
  "(a \<rhd>1 b) s \<Longrightarrow> \<exists>ao'. ko_at (ArchObj ao') (snd a) s"
  apply (clarsimp simp: vs_lookup1_def)
  apply (case_tac ko, auto simp: vs_refs_def)
  done

lemma vs_lookup_trancl_step:
  "\<lbrakk> r \<in> vs_lookup s; (r, r') \<in> (vs_lookup1 s)^+ \<rbrakk> \<Longrightarrow> r' \<in> vs_lookup s"
  apply (clarsimp simp add: vs_lookup_def)
  apply (drule (1) rtrancl_trancl_trancl)
  apply (drule trancl_into_rtrancl)+
  apply blast
  done

lemma vs_lookup_pages_trancl_step:
  "\<lbrakk> r \<in> vs_lookup_pages s; (r, r') \<in> (vs_lookup_pages1 s)^+ \<rbrakk> \<Longrightarrow> r' \<in> vs_lookup_pages s"
  apply (clarsimp simp add: vs_lookup_pages_def)
  apply (drule (1) rtrancl_trancl_trancl)
  apply (drule trancl_into_rtrancl)+
  apply blast
  done

lemma vs_lookup_step:
  "\<lbrakk> (ref \<rhd> p) s; ((ref, p) \<rhd>1 (ref', p')) s \<rbrakk> \<Longrightarrow> (ref' \<rhd> p') s"
  unfolding vs_lookup_def
  apply clarsimp
  apply (drule rtrancl_trans)
   apply (erule r_into_rtrancl)
  apply blast
  done

lemma vs_lookup_pages_step:
  "\<lbrakk> (ref \<unrhd> p) s; ((ref, p) \<unrhd>1 (ref', p')) s \<rbrakk> \<Longrightarrow> (ref' \<unrhd> p') s"
  unfolding vs_lookup_pages_def
  apply clarsimp
  apply (drule rtrancl_trans)
   apply (erule r_into_rtrancl)
  apply blast
  done

lemma vs_asid_refsI:
  "table asid = Some p \<Longrightarrow>
  ([VSRef (ucast asid) None],p) \<in> vs_asid_refs table"
  by (fastforce simp: vs_asid_refs_def graph_of_def)

(* Non-recursive introduction rules for vs_lookup and vs_lookup_pages
   NOTE: exhaustive if assuming valid_objs and valid_asid_table *)
lemma vs_lookup_atI:
  "arm_asid_table (arch_state s) a = Some p \<Longrightarrow> ([VSRef (ucast a) None] \<rhd> p) s"
  unfolding vs_lookup_def by (drule vs_asid_refsI) fastforce

lemma vs_lookup_apI:
  "\<And>a p\<^sub>1 ap b.
     \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
      kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
      ap b = Some p\<rbrakk>
     \<Longrightarrow> ([VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<rhd> p) s"
  apply (simp add: vs_lookup_def Image_def vs_asid_refs_def graph_of_def)
  apply (intro exI conjI, assumption)
  apply (rule rtrancl_into_rtrancl)
   apply (rule rtrancl_refl)
  apply (fastforce simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def image_def)
  done

lemma vs_lookup_pdI:
  "\<And>a p\<^sub>1 ap b p\<^sub>2 pd c.
     \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
      kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
      ap b = Some p\<^sub>2;
      kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
      pd c = pde.PageTablePDE p\<rbrakk>
     \<Longrightarrow> ([VSRef (ucast c) (Some APageDirectory),
           VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None]
          \<rhd> ptrFromPAddr p) s"
  apply (simp add: vs_lookup_def Image_def vs_asid_refs_def graph_of_def)
  apply (intro exI conjI, assumption)
  apply (rule rtrancl_into_rtrancl)
   apply (rule rtrancl_into_rtrancl)
    apply (rule rtrancl_refl)
   apply (fastforce simp: vs_lookup1_def obj_at_def
                          vs_refs_def graph_of_def image_def)
  apply (simp add: vs_lookup1_def obj_at_def vs_refs_def graph_of_def image_def)
  apply (rule_tac x=c in exI)
  apply (simp add: pde_ref_def)
  done

lemma vs_lookup_pages_vs_lookupI: "(ref \<rhd> p) s \<Longrightarrow> (ref \<unrhd> p) s"
  apply (clarsimp simp: vs_lookup_pages_def vs_lookup_def Image_def
                 elim!: bexEI)
  apply (erule rtrancl.induct, simp_all)
  apply (rename_tac a b c)
  apply (subgoal_tac "(b \<unrhd>1 c) s", erule (1) rtrancl_into_rtrancl)
  apply (thin_tac "x : rtrancl r" for x r)+
  apply (simp add: vs_lookup1_def vs_lookup_pages1_def split_def)
  apply (erule exEI)
  apply clarsimp
  apply (case_tac x, simp_all add: vs_refs_def vs_refs_pages_def
                            split: arch_kernel_obj.splits)
  apply (clarsimp simp: split_def graph_of_def image_def  split: if_split_asm)
  apply (rule_tac x=a in exI, intro conjI)
   apply (simp add: pde_ref_def pde_ref_pages_def
             split: pde.splits)
  apply (rule refl)
  done

lemmas
  vs_lookup_pages_atI = vs_lookup_atI[THEN vs_lookup_pages_vs_lookupI] and
  vs_lookup_pages_apI = vs_lookup_apI[THEN vs_lookup_pages_vs_lookupI]

lemma vs_lookup_pages_pdI:
  "\<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
    kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
    ap b = Some p\<^sub>2;
    kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
    pde_ref_pages (pd c) = Some p\<rbrakk>
   \<Longrightarrow> ([VSRef (ucast c) (Some APageDirectory),
         VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<unrhd> p) s"
  apply (frule (2) vs_lookup_pages_apI)
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def
                      vs_refs_pages_def graph_of_def image_def
               split: if_split_asm)

lemma vs_lookup_pages_ptI:
  "\<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
    kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
    ap b = Some p\<^sub>2;
    kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
    pd c = PageTablePDE addr;
    kheap s (ptrFromPAddr addr) = Some (ArchObj (PageTable pt));
    pte_ref_pages (pt d) = Some p\<rbrakk>
   \<Longrightarrow> ([VSRef (ucast d) (Some APageTable),
         VSRef (ucast c) (Some APageDirectory),
         VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<unrhd> p) s" (* ARMHYP: add VCPU *)
  apply (frule (4) vs_lookup_pdI[THEN vs_lookup_pages_vs_lookupI])
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def
                      vs_refs_pages_def graph_of_def image_def
               split: if_split_asm)

lemma stronger_vspace_objsD_lemma:
  "\<lbrakk>valid_vspace_objs s; r \<in> vs_lookup s; (r,r') \<in> (vs_lookup1 s)\<^sup>+ \<rbrakk>
  \<Longrightarrow> \<exists>ao. ko_at (ArchObj ao) (snd r') s \<and>
          valid_vspace_obj ao s"
  apply (erule trancl_induct)
   apply (frule vs_lookup1_is_arch)
   apply (cases r)
   apply clarsimp
   apply (frule (2) valid_vspace_objsD)
   apply (drule (1) vs_lookup_step)
   apply (drule (2) vs_lookup1_ko_at_dest)
   apply clarsimp
   apply (drule (2) valid_vspace_objsD)
   apply fastforce
  apply clarsimp
  apply (frule (2) vs_lookup1_ko_at_dest)
  apply (drule (1) vs_lookup_trancl_step)
  apply (drule (1) vs_lookup_step)
  apply clarsimp
  apply (drule (2) valid_vspace_objsD)
  apply fastforce
  done

lemma stronger_vspace_objsD:
  "\<lbrakk> (ref \<rhd> p) s;
     valid_vspace_objs s;
     valid_asid_table (arm_asid_table (arch_state s)) s \<rbrakk> \<Longrightarrow>
  \<exists>ao. ko_at (ArchObj ao) p s \<and>
       valid_vspace_obj ao s"
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def graph_of_def)
  apply (clarsimp simp: valid_asid_table_def)
  apply (drule bspec, fastforce simp: ran_def)
  apply (drule rtranclD)
  apply (erule disjE)
   prefer 2
   apply clarsimp
   apply (drule stronger_vspace_objsD_lemma)
     apply (erule vs_lookup_atI)
    apply assumption
   apply clarsimp
  apply clarsimp
  apply (simp add: valid_vspace_objs_def)
  apply (erule_tac x=p in allE)
  apply (erule impE)
   apply (rule exI)
   apply (erule vs_lookup_atI)
  apply (clarsimp simp: obj_at_def)
  done

(* An alternative definition for valid_vspace_objs.

   The predicates valid_asid_table and valid_vspace_objs are very compact
   but sometimes hard to use.
   The lemma below basically unrolls vs_lookup.
   Though less elegant, this formulation better separates the relevant cases. *)
lemma valid_vspace_objs_alt:
  "(\<forall>p\<in>ran (arm_asid_table (arch_state s)). asid_pool_at p s) \<and>
   valid_vspace_objs s \<longleftrightarrow>
   (\<forall>a p. arm_asid_table (arch_state s) a = Some p \<longrightarrow>
          typ_at (AArch AASIDPool) p s) \<and>
   (\<forall>a p\<^sub>1 ap b p.
          arm_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap)) \<longrightarrow>
          ap b = Some p \<longrightarrow> page_directory_at p s) \<and>
   (\<forall>a p\<^sub>1 ap b p\<^sub>2 pd c.
          arm_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap)) \<longrightarrow>
          ap b = Some p\<^sub>2 \<longrightarrow>
          kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd)) \<longrightarrow>
          valid_pde (pd c) s) \<and>
   (\<forall>a p\<^sub>1 ap b p\<^sub>2 pd c addr f w pt.
          arm_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap)) \<longrightarrow>
          ap b = Some p\<^sub>2 \<longrightarrow>
          kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd)) \<longrightarrow>
          pd c = pde.PageTablePDE addr \<longrightarrow>
          kheap s (ptrFromPAddr addr) =
            Some (ArchObj (PageTable pt)) \<longrightarrow>
          (\<forall>d. valid_pte (pt d) s))" (* ARMHYP: add VCPU *)
  apply (intro iffI conjI)
       apply fastforce
      apply (clarsimp simp: obj_at_def)
      apply (thin_tac "Ball S P" for S P)
      apply (frule vs_lookup_atI)
      apply (drule valid_vspace_objsD)
        apply (simp add: obj_at_def)
       apply assumption
      apply (clarsimp simp: obj_at_def ranI)
     apply (clarsimp simp: obj_at_def)
     apply (thin_tac "Ball S P" for S P)
     apply (frule (2) vs_lookup_apI)
     apply (drule valid_vspace_objsD)
       apply (simp add: obj_at_def)
      apply assumption
     apply fastforce
    apply (clarsimp simp: obj_at_def)
    apply (thin_tac "Ball S P" for S P)
    apply (frule (4) vs_lookup_pdI)
    apply (drule valid_vspace_objsD)
      apply (simp add: obj_at_def)
     apply assumption
    apply fastforce
   apply (clarsimp simp: ran_def)
  apply (clarsimp simp: valid_vspace_objs_def vs_lookup_def)
  apply (erule converse_rtranclE)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: obj_at_def ran_def)
  apply (erule converse_rtranclE)
   apply (drule vs_lookup1D)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: obj_at_def)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply fastforce
  apply (erule converse_rtranclE)
   apply (clarsimp dest!: vs_lookup1D)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: obj_at_def)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: graph_of_def  split: if_split_asm)
   apply (drule_tac x=ab in spec)
   apply (clarsimp simp: pde_ref_def obj_at_def
                  split: pde.splits)
  apply (clarsimp dest!: vs_lookup1D)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: vs_refs_def graph_of_def image_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: graph_of_def  split: if_split_asm)
  apply (drule_tac x=ab in spec)
  apply (clarsimp simp: pde_ref_def obj_at_def
                 split: pde.splits)
  done

lemma vs_lookupE:
  "\<lbrakk> (ref \<rhd> p) s;
    \<And>ref' p'. \<lbrakk> (ref',p') \<in> vs_asid_refs (arm_asid_table (arch_state s));
                ((ref',p') \<rhd>* (ref,p)) s \<rbrakk> \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
  by (auto simp: vs_lookup_def)

(* Non-recursive elim rules for vs_lookup and vs_lookup_pages
   NOTE: effectively rely on valid_objs and valid_asid_table *)
lemma vs_lookupE_alt: (* ARMHYP *)
  assumes vl: "(ref \<rhd> p) s"
  assumes va: "valid_vspace_objs s"
  assumes vt: "(\<forall>p\<in>ran (arm_asid_table (arch_state s)). asid_pool_at p s)"
  assumes 0: "\<And>a. arm_asid_table (arch_state s) a = Some p \<Longrightarrow>
                   typ_at (AArch AASIDPool) p s \<Longrightarrow>
                   R [VSRef (ucast a) None] p"
  assumes 1: "\<And>a p\<^sub>1 ap b.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p; page_directory_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 2: "\<And>a p\<^sub>1 ap b p\<^sub>2 pd c.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2;
        kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
        pde_ref (pd c) = Some p; page_table_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast c) (Some APageDirectory),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p" (* ARMHYP: add VCPU? *)
  shows "R ref p"
proof -
  note vao = valid_vspace_objs_alt[THEN iffD1, OF conjI[OF vt va]]
  note vat = vao[THEN conjunct1, rule_format]
  note vap = vao[THEN conjunct2, THEN conjunct1, rule_format]
  note vpd = vao[THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  from vl
  show ?thesis
    apply (clarsimp simp: vs_lookup_def)
    apply (clarsimp simp: Image_def vs_asid_refs_def graph_of_def)
    apply (frule vat)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (1) 0)
    apply (clarsimp simp: vs_refs_def graph_of_def obj_at_def
                   dest!: vs_lookup1D)
    apply (frule (2) vap)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (3) 1)
    apply (clarsimp simp: vs_refs_def graph_of_def obj_at_def
                   dest!: vs_lookup1D  split: if_split_asm)
    apply (frule_tac c= ab in vpd; (assumption|succeed))
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (4) 2)
     apply (simp add: valid_pde_def pde_ref_def split: pde.splits)
    by (clarsimp simp: obj_at_def pde_ref_def vs_refs_def
                split: pde.splits
                dest!: vs_lookup1D)
qed

lemma vs_lookup_pagesE_alt:
  assumes vl: "(ref \<unrhd> p) s"
  assumes va: "valid_vspace_objs s" (* ARMHYP *)
  assumes vt: "(\<forall>p\<in>ran (arm_asid_table (arch_state s)). asid_pool_at p s)"
  assumes 0: "\<And>a. arm_asid_table (arch_state s) a = Some p \<Longrightarrow>
                   typ_at (AArch AASIDPool) p s \<Longrightarrow>
                   R [VSRef (ucast a) None] p"
  assumes 1: "\<And>a p\<^sub>1 ap b.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p; page_directory_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 2: "\<And>a p\<^sub>1 ap b p\<^sub>2 pd c.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2;
        kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
        pde_ref_pages (pd c) = Some p; valid_pde (pd c) s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast c) (Some APageDirectory),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 3: "\<And>a p\<^sub>1 ap b p\<^sub>2 pd c addr pt d.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2;
        kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
        pd c = PageTablePDE addr;
        kheap s (ptrFromPAddr addr) = Some (ArchObj (PageTable pt));
        pte_ref_pages (pt d) = Some p; valid_pte (pt d) s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast d) (Some APageTable),
              VSRef (ucast c) (Some APageDirectory),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  shows "R ref p"
proof -
  note vao = valid_vspace_objs_alt[THEN iffD1, OF conjI[OF vt va]]
  note vat = vao[THEN conjunct1, rule_format]
  note vap = vao[THEN conjunct2, THEN conjunct1, rule_format]
  note vpd = vao[THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  note vpt = vao[THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format]

  from vl
  show ?thesis
    apply (clarsimp simp: vs_lookup_pages_def)
    apply (clarsimp simp: Image_def vs_asid_refs_def graph_of_def)
    apply (frule vat)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (1) 0)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def obj_at_def
                   dest!: vs_lookup_pages1D)
    apply (frule (2) vap)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (3) 1)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def obj_at_def
                   dest!: vs_lookup_pages1D  split: if_split_asm)
    apply (frule_tac c=ab in vpd; (assumption|succeed))
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (5) 2)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def obj_at_def
                          pde_ref_pages_def data_at_def
                   dest!: vs_lookup_pages1D
                   split: if_split_asm pde.splits)
    apply (frule_tac d=ac in vpt, assumption+)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (7) 3)
    apply (auto simp:vs_refs_pages_def graph_of_def obj_at_def
                          pte_ref_pages_def data_at_def
                   dest!: vs_lookup_pages1D
                   split: pte.splits)
    done
qed

lemma valid_asid_tableD:
  "\<lbrakk> T x = Some p; valid_asid_table T s \<rbrakk> \<Longrightarrow> asid_pool_at p s"
  by (auto simp: valid_asid_table_def ran_def)

declare graph_of_empty[simp]

lemma pde_graph_ofI:
  "\<lbrakk>pd x = pde; pde_ref pde = Some v\<rbrakk>
   \<Longrightarrow> (x, v) \<in> graph_of (\<lambda>x. pde_ref (pd x))"
  by (rule graph_ofI, simp)

lemma vs_refs_pdI:
  "\<lbrakk>pd (ucast r) = PageTablePDE x;
   \<forall>n \<ge> 11. n < 32 \<longrightarrow> \<not> r !! n\<rbrakk> \<comment> \<open>ARMHYP\<close>
   \<Longrightarrow> (VSRef r (Some APageDirectory), ptrFromPAddr x)
       \<in> vs_refs (ArchObj (PageDirectory pd))"
  apply (simp add: vs_refs_def)
  apply (rule image_eqI[rotated])
   apply (rule_tac x="ucast r" in pde_graph_ofI)
     apply (simp add: pde_ref_def)+
  apply (simp add: ucast_ucast_mask)
  apply (rule word_eqI)
  apply (simp add: word_size)
  apply (rule ccontr, auto)
  done

lemma aa_type_pdD:
  "aa_type ko = APageDirectory \<Longrightarrow> \<exists>pd. ko = PageDirectory pd"
  by (clarsimp simp: aa_type_def
               split: arch_kernel_obj.splits if_split_asm)

lemma empty_table_pde_refD:
  "\<lbrakk> pde_ref (pd x) = Some r; empty_table S (ArchObj (PageDirectory pd)) \<rbrakk> \<Longrightarrow>
  r \<in> S"
  by (simp add: empty_table_def)


lemma valid_table_caps_pdD: (* ARMHYP? *)
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PageDirectoryCap pd None));
     valid_table_caps s \<rbrakk> \<Longrightarrow>
    obj_at (empty_table {}) pd s"
  apply (clarsimp simp: valid_table_caps_def simp del: split_paired_All)
  apply (erule allE)+
  apply (erule (1) impE)
  apply (fastforce simp add: is_pd_cap_def cap_asid_def)
  done

lemma valid_vs_lookupD:
  "\<lbrakk> (ref \<unrhd> p) s; valid_vs_lookup s \<rbrakk> \<Longrightarrow>
  (\<exists>slot cap. caps_of_state s slot = Some cap \<and> p \<in> obj_refs cap \<and> vs_cap_ref cap = Some ref)"
  by (simp add: valid_vs_lookup_def)

lemma vs_lookup_induct:
  assumes r: "(ref \<rhd> p) s"
  assumes a: "\<And>asid p. \<lbrakk> arm_asid_table (arch_state s) asid = Some p \<rbrakk> \<Longrightarrow> P [VSRef (ucast asid) None] p s"
  assumes s: "\<And>ref p ref' p'. \<lbrakk> (ref \<rhd> p) s; ((ref,p) \<rhd>1 (ref',p')) s; P ref p s \<rbrakk> \<Longrightarrow> P ref' p' s"
  shows "P ref p s"
  using r
  apply (clarsimp simp: vs_lookup_def)
  apply (drule rtranclD)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (frule a)
  apply (erule disjE, simp)
  apply clarsimp
  apply (drule vs_lookup_atI)
  apply (erule trancl_induct2)
   apply (erule (2) s)
  apply (drule (1) vs_lookup_trancl_step)
  apply (erule (2) s)
  done

lemma vs_lookup_pages_induct:
  assumes r: "(ref \<unrhd> p) s"
  assumes a: "\<And>asid p. \<lbrakk> arm_asid_table (arch_state s) asid = Some p \<rbrakk> \<Longrightarrow> P [VSRef (ucast asid) None] p s"
  assumes s: "\<And>ref p ref' p'. \<lbrakk> (ref \<unrhd> p) s; ((ref,p) \<unrhd>1 (ref',p')) s; P ref p s \<rbrakk> \<Longrightarrow> P ref' p' s"
  shows "P ref p s"
  using r
  apply (clarsimp simp: vs_lookup_pages_def)
  apply (drule rtranclD)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (frule a)
  apply (erule disjE, simp)
  apply clarsimp
  apply (drule vs_lookup_pages_atI)
  apply (erule trancl_induct2)
   apply (erule (2) s)
  apply (drule (1) vs_lookup_pages_trancl_step)
  apply (erule (2) s)
  done

lemma vs_ref_order:
  "\<lbrakk> (r \<rhd> p) s; valid_vspace_objs s; valid_arch_state s \<rbrakk>
       \<Longrightarrow> \<exists>tp. r \<noteq> [] \<and> typ_at (AArch tp) p s \<and>
            rev (Some tp # map vs_ref_aatype r)
               \<le> [None, Some AASIDPool, Some APageDirectory, Some APageTable]"
  apply (erule vs_lookup_induct)
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def ranI)
  apply (clarsimp dest!: vs_lookup1D elim!: obj_atE)
  apply (clarsimp simp: vs_refs_def a_type_simps
                 split: kernel_object.split_asm arch_kernel_obj.split_asm
                 dest!: graph_ofD)
   apply (drule valid_vspace_objsD) apply (simp add: obj_at_def) apply (assumption)
   apply (case_tac rs; simp)
   apply (case_tac list; simp add: ranI)
   apply (case_tac lista; simp)
   apply (frule prefix_length_le, clarsimp)
  apply (drule valid_vspace_objsD, simp add: obj_at_def, assumption)
  apply (clarsimp simp: pde_ref_def
                 split: pde.split_asm if_split_asm)
  apply (drule_tac x=a in spec, simp)
  apply (case_tac rs; simp)
  apply (case_tac list; simp)
  apply (case_tac lista; simp)
  apply (frule prefix_length_le, clarsimp)
  done


lemma addrFromPPtr_ptrFromPAddr_id[simp]:
  "addrFromPPtr (ptrFromPAddr x) = x"
by (simp add: addrFromPPtr_def ptrFromPAddr_def)

lemma valid_pte_lift2:
  assumes x: "\<And>T p. \<lbrace>Q and typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_pte pte s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pte pte s\<rbrace>"
  by (cases pte) (simp add: data_at_def | wp x hoare_vcg_disj_lift)+

lemma valid_pde_lift2:
  assumes x: "\<And>T p. \<lbrace>Q and typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_pde pde s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pde pde s\<rbrace>"
  by (cases pde) (simp add: data_at_def | wp x hoare_vcg_disj_lift)+


lemma valid_vspace_obj_typ2:
  assumes P: "\<And>P p T. \<lbrace>\<lambda>s. Q s \<and> P (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Q s \<and> valid_vspace_obj ob s \<rbrace> f \<lbrace>\<lambda>rv s. valid_vspace_obj ob s\<rbrace>"
  by (cases ob; wpsimp wp: hoare_vcg_const_Ball_lift [OF P]
    hoare_vcg_all_lift valid_pte_lift2[unfolded pred_conj_def, OF P]
    P valid_pde_lift2[unfolded pred_conj_def, OF P]
  )

lemma valid_vspace_objsI [intro?]:
  "(\<And>p ao. \<lbrakk> (\<exists>\<rhd> p) s; ko_at (ArchObj ao) p s \<rbrakk> \<Longrightarrow> valid_vspace_obj ao s) \<Longrightarrow> valid_vspace_objs s"
  by (simp add: valid_vspace_objs_def)

lemma vs_lookup1_stateI2:
  assumes 1: "(r \<rhd>1 r') s"
  assumes ko: "\<And>ko. \<lbrakk> ko_at ko (snd r) s; vs_refs ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') (snd r) s'"
  shows "(r \<rhd>1 r') s'" using 1 ko
  by (fastforce simp: obj_at_def vs_lookup1_def)


lemma vs_lookupI:
  "\<lbrakk> ref' \<in> vs_asid_refs (arm_asid_table (arch_state s));
     (ref',(ref,p)) \<in> (vs_lookup1 s)^*  \<rbrakk> \<Longrightarrow>
  (ref \<rhd> p) s"
  by (simp add: vs_lookup_def) blast

lemma vs_lookup1_trans_is_append':
  "(a, b) \<in> (vs_lookup1 s)\<^sup>* \<Longrightarrow> \<exists>zs. fst b = zs @ fst a"
  by (erule rtrancl_induct) (auto dest!: vs_lookup1D)

lemma vs_lookup1_trans_is_append:
  "((xs, a), (ys, b)) \<in> (vs_lookup1 s)\<^sup>* \<Longrightarrow> \<exists>zs. ys = zs @ xs"
  by (drule vs_lookup1_trans_is_append') auto

lemma vs_lookup_trans_ptr_eq':
  "(a, b) \<in> (vs_lookup1 s)\<^sup>* \<Longrightarrow> fst a = fst b \<longrightarrow> snd b = snd a"
  apply (erule rtrancl_induct)
   apply simp
  apply clarsimp
  apply (cases a)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (frule vs_lookup1_trans_is_append)
  apply simp
  done

lemma vs_lookup_trans_ptr_eq:
  "((r,p), (r,p')) \<in> (vs_lookup1 s)\<^sup>* \<Longrightarrow> p = p'"
  by (drule vs_lookup_trans_ptr_eq') simp

lemma vs_lookup_atD:
  "([VSRef (ucast asid) None] \<rhd> p) s \<Longrightarrow> arm_asid_table (arch_state s) asid = Some p"
  apply (simp add: vs_lookup_def)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (drule rtranclD)
  apply (erule disjE)
   apply (clarsimp simp: up_ucast_inj_eq)
  apply clarsimp
  apply (drule tranclD2)
  apply (clarsimp simp: up_ucast_inj_eq)
  apply (drule vs_lookup1D)
  apply (clarsimp simp: vs_refs_def)
  apply (clarsimp split: split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma vs_lookup_atE:
  "([VSRef (ucast asid) None] \<rhd> p) s \<Longrightarrow> (arm_asid_table (arch_state s) asid = Some p \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast dest: vs_lookup_atD)

lemma vs_lookup_2ConsD:
  "((v # v' # vs) \<rhd> p) s \<Longrightarrow> \<exists>p'. ((v'#vs) \<rhd> p') s \<and> ((v' # vs,p') \<rhd>1 (v # v' # vs, p)) s"
  apply (clarsimp simp: vs_lookup_def)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def)
  apply (fastforce simp: vs_lookup1_def)
  done

lemma aa_type_vcpuD:
  "aa_type ko = AVCPU \<Longrightarrow> \<exists>v. ko = VCPU v"
  by (clarsimp simp: aa_type_def
               split: arch_kernel_obj.splits if_split_asm)

lemma global_refs_asid_table_update [iff]:
  "global_refs (s\<lparr>arch_state := arm_asid_table_update f (arch_state s)\<rparr>) = global_refs s"
  by (simp add: global_refs_def)

lemma pspace_in_kernel_window_arch_update[simp]:
  "arm_kernel_vspace (f (arch_state s)) = arm_kernel_vspace (arch_state s)
     \<Longrightarrow> pspace_in_kernel_window (arch_state_update f s) = pspace_in_kernel_window s"
  by (simp add: pspace_in_kernel_window_def)

lemma
  "f = g \<Longrightarrow> (\<forall>x. f x = g x)"
  apply simp
  done



lemmas vs_cap_ref_simps =
       vs_cap_ref_def [simplified vs_cap_ref_arch_def[abs_def] arch_cap_fun_lift_def[abs_def],
       split_simps cap.split arch_cap.split vmpage_size.split]

lemmas table_cap_ref_simps =
       table_cap_ref_def [simplified table_cap_ref_arch_def[abs_def] arch_cap_fun_lift_def[abs_def],
         split_simps cap.split arch_cap.split]

lemma table_cap_ref_vs_cap_ref_eq:
  "table_cap_ref cap = Some ref \<Longrightarrow> table_cap_ref cap' = Some ref \<Longrightarrow>
   vs_cap_ref cap = vs_cap_ref cap'"
  by (auto simp: table_cap_ref_def vs_cap_ref_simps
          split: cap.splits arch_cap.splits option.splits)

lemma vs_cap_ref_eq_imp_table_cap_ref_eq:
  "is_pg_cap cap = is_pg_cap cap' \<Longrightarrow> vs_cap_ref cap = vs_cap_ref cap'
   \<Longrightarrow> table_cap_ref cap = table_cap_ref cap'"
  by (auto simp: is_arch_cap_simps vs_cap_ref_def table_cap_ref_simps
                  arch_cap_fun_lift_def
          split: cap.splits arch_cap.splits vmpage_size.splits option.splits)

lemma valid_vspace_objs_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p s)\<rbrace>"
      and y: "\<And>ao p. \<lbrace>\<lambda>s. \<not> ko_at (ArchObj ao) p s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> ko_at (ArchObj ao) p s\<rbrace>"
  shows      "\<lbrace>valid_vspace_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (simp add: valid_vspace_objs_def)
  apply (wp hoare_vcg_all_lift hoare_convert_imp [OF x])+
  apply (rule hoare_convert_imp [OF y])
  apply (rule valid_vspace_obj_typ [OF z], auto)
  done

lemma wf_acap_rights_update_id [intro!, simp]:
  "\<lbrakk>wellformed_acap cap\<rbrakk> \<Longrightarrow> acap_rights_update (acap_rights cap) cap = cap"
  unfolding wellformed_acap_def acap_rights_update_def
  by (auto split: arch_cap.splits)

lemmas cap_asid_simps [simp] =
  cap_asid_def [simplified, split_simps cap.split arch_cap.split option.split prod.split]


lemma in_user_frame_def:
  "in_user_frame p \<equiv> \<lambda>s.
   \<exists>sz. typ_at (AArch (AUserData sz)) (p && ~~ mask (pageBitsForSize sz)) s"
  apply (rule eq_reflection, rule ext)
  apply (simp add: in_user_frame_def obj_at_def)
  apply (rule_tac f=Ex in arg_cong)
  apply (rule ext, rule iffI)
   apply (simp add: a_type_simps)
  apply clarsimp
  done

lemma in_user_frame_lift:
 assumes typ_at: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>_. typ_at (AArch T) p\<rbrace>"
 shows "\<lbrace>in_user_frame p\<rbrace> f \<lbrace>\<lambda>_. in_user_frame p\<rbrace>"
 unfolding in_user_frame_def
 by (wp hoare_vcg_ex_lift typ_at)

lemma wellformed_vspace_default:
  "wellformed_vspace_obj (default_arch_object aobject_type dev us)"
  unfolding wellformed_vspace_obj_def default_arch_object_def
  by (cases aobject_type; simp)

lemma wellformed_arch_default:
  "arch_valid_obj (default_arch_object aobject_type dev us) s"
  unfolding arch_valid_obj_def default_arch_object_def
  by (cases aobject_type; simp add: default_vcpu_def valid_vcpu_def)

lemma valid_vspace_obj_default':
  "valid_vspace_obj (default_arch_object aobject_type dev us) s"
  unfolding default_arch_object_def
  by (cases aobject_type; simp)


text \<open>arch specific symrefs\<close>

definition
  tcb_vcpu_refs :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "tcb_vcpu_refs atcb \<equiv> case atcb of
     Some vc \<Rightarrow> {(vc, TCBHypRef)}
   | None \<Rightarrow> {}"

definition
  tcb_hyp_refs :: "arch_tcb \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "tcb_hyp_refs atcb \<equiv> tcb_vcpu_refs (tcb_vcpu atcb)"

definition vcpu_tcb_refs :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "vcpu_tcb_refs t \<equiv> case t of
    None \<Rightarrow> {}
  | Some tcb \<Rightarrow> {(tcb, HypTCBRef)}"

lemma tcb_hyp_refs_of_simps[simp]:
  "tcb_hyp_refs atcb = tcb_vcpu_refs (tcb_vcpu atcb)"
  by (auto simp: tcb_hyp_refs_def)

lemma tcb_vcpu_refs_of_simps[simp]:
  "tcb_vcpu_refs (Some vc) = {(vc, TCBHypRef)}"
  "tcb_vcpu_refs None = {}"
  by (auto simp: tcb_vcpu_refs_def)

lemma vcpu_tcb_refs_of_simps[simp]:
  "vcpu_tcb_refs (Some tcb) = {(tcb, HypTCBRef)}"
  "vcpu_tcb_refs None = {}"
  by (auto simp: vcpu_tcb_refs_def)


definition refs_of_a :: "arch_kernel_obj \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "refs_of_a x \<equiv> case x of
   ASIDPool p \<Rightarrow> {}
 | PageTable pt \<Rightarrow> {}
 | PageDirectory pd \<Rightarrow> {}
 | DataPage dev sz \<Rightarrow> {}
 | VCPU v  \<Rightarrow> vcpu_tcb_refs (vcpu_tcb v) "


lemma refs_of_a_simps[simp]:
  "refs_of_a (ASIDPool p) = {}"
  "refs_of_a (PageTable pt) = {}"
  "refs_of_a (PageDirectory pd) = {}"
  "refs_of_a (DataPage dev sz) = {}"
  "refs_of_a (VCPU v) = vcpu_tcb_refs (vcpu_tcb v)"
 by (auto simp: refs_of_a_def)

lemma refs_of_a_rev: (* duplicate? *)
 "(x, HypTCBRef) \<in> refs_of_a ao =
    (\<exists>v. ao = VCPU v \<and> vcpu_tcb v = Some x)"
  by (auto simp: refs_of_a_def vcpu_tcb_refs_def split: arch_kernel_obj.splits option.split)


definition (* refs to arch objects from a kernel object: move to generic? *)
  hyp_refs_of :: "kernel_object \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "hyp_refs_of x \<equiv> case x of
     CNode sz fun      => {}
   | TCB tcb           => tcb_hyp_refs (tcb_arch tcb)
   | Endpoint ep       => {}
   | Notification ntfn => {}
   | ArchObj ao        => refs_of_a ao"

lemma hyp_refs_of_simps[simp]:
  "hyp_refs_of (CNode sz fun) = {}"
  "hyp_refs_of (TCB tcb) = tcb_hyp_refs (tcb_arch tcb)"
  "hyp_refs_of (Endpoint ep) = {}"
  "hyp_refs_of (Notification ntfn) = {}"
  "hyp_refs_of (ArchObj ao) = refs_of_a ao"
  by (auto simp: hyp_refs_of_def)

lemma hyp_refs_of_rev:
 "(x, TCBHypRef) \<in> hyp_refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (tcb_vcpu (tcb_arch tcb) = Some x))"
 "(x, HypTCBRef) \<in> hyp_refs_of ko =
    (\<exists>v. ko = ArchObj (VCPU v) \<and> (vcpu_tcb v = Some x))"
  by (auto simp: hyp_refs_of_def tcb_hyp_refs_def tcb_vcpu_refs_def
                    vcpu_tcb_refs_def refs_of_a_def
              split: kernel_object.splits arch_kernel_obj.splits option.split)


definition
  state_hyp_refs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set"
where
 "state_hyp_refs_of s \<equiv> \<lambda>x. case (kheap s x) of Some ko \<Rightarrow> hyp_refs_of ko | None \<Rightarrow> {}"


lemma in_state_hyp_refs_of:
  "ref \<in> state_hyp_refs_of s p \<longleftrightarrow> (\<exists>ko. kheap s p = Some ko \<and> ref \<in> hyp_refs_of ko)"
  by (simp add: state_hyp_refs_of_def split: option.split)

definition
  state_refs_of_a :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set"
where
 "state_refs_of_a s \<equiv> \<lambda>x. case (kheap s x) of
                            Some ko \<Rightarrow> (case ko of ArchObj ao \<Rightarrow> refs_of_a ao | _ \<Rightarrow> {})
                          | None \<Rightarrow> {}"


lemma state_hyp_refs_of_elemD:
  "\<lbrakk> ref \<in> state_hyp_refs_of s x \<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. ref \<in> hyp_refs_of obj) x s"
  by (clarsimp simp add: state_hyp_refs_of_def obj_at_def
                  split: option.splits)

lemma state_hyp_refs_of_eqD:
  "\<lbrakk> state_hyp_refs_of s x = S; S \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. hyp_refs_of obj = S) x s"
  by (clarsimp simp add: state_hyp_refs_of_def obj_at_def
                  split: option.splits)

lemma obj_at_state_hyp_refs_ofD:
  "obj_at P p s \<Longrightarrow> \<exists>ko. P ko \<and> state_hyp_refs_of s p = hyp_refs_of ko"
  apply (clarsimp simp: obj_at_def state_hyp_refs_of_def)
  apply fastforce
  done

lemma ko_at_state_hyp_refs_ofD:
  "ko_at ko p s \<Longrightarrow> state_hyp_refs_of s p = hyp_refs_of ko"
  by (clarsimp dest!: obj_at_state_hyp_refs_ofD)

lemma hyp_sym_refs_obj_atD:
  "\<lbrakk> obj_at P p s; sym_refs (state_hyp_refs_of s) \<rbrakk> \<Longrightarrow>
     \<exists>ko. P ko \<and> state_hyp_refs_of s p = hyp_refs_of ko \<and>
        (\<forall>(x, tp)\<in>hyp_refs_of ko. obj_at (\<lambda>ko. (p, symreftype tp) \<in> hyp_refs_of ko) x s)"
  apply (drule obj_at_state_hyp_refs_ofD)
  apply (erule exEI, clarsimp)
  apply (drule sym, simp)
  apply (drule(1) sym_refsD)
  apply (erule state_hyp_refs_of_elemD)
  done

lemma hyp_sym_refs_ko_atD:
  "\<lbrakk> ko_at ko p s; sym_refs (state_hyp_refs_of s) \<rbrakk> \<Longrightarrow>
     state_hyp_refs_of s p = hyp_refs_of ko \<and>
     (\<forall>(x, tp)\<in>hyp_refs_of ko.  obj_at (\<lambda>ko. (p, symreftype tp) \<in> hyp_refs_of ko) x s)"
  by (drule(1) hyp_sym_refs_obj_atD, simp)

definition
  "vspace_obj_fun_lift P F c \<equiv> case c of
                                  ArchObj (VCPU vcpu) \<Rightarrow> F |
                                  ArchObj ac \<Rightarrow> P ac       |
                                           _ \<Rightarrow> F"
lemma vspace_obj_fun_lift_expand[simp]:
  "(vspace_obj_fun_lift (\<lambda> ako. case ako of
                                ASIDPool pool \<Rightarrow> P_ASIDPool pool
                              | PageTable pt \<Rightarrow> P_PageTable pt
                              | PageDirectory pd \<Rightarrow> P_PageDirectory pd
                              | DataPage dev s \<Rightarrow> P_DataPage dev s
                              | VCPU v \<Rightarrow> P_VCPU v)
                      F) = (\<lambda>ko.
   (case ko of
      ArchObj (ASIDPool pool) \<Rightarrow> P_ASIDPool pool
    | ArchObj (PageTable pt) \<Rightarrow> P_PageTable pt
    | ArchObj (PageDirectory pd) \<Rightarrow> P_PageDirectory pd
    | ArchObj (DataPage dev s) \<Rightarrow> P_DataPage dev s
    | ArchObj (VCPU v) \<Rightarrow> F
    | _ \<Rightarrow> F))"
  apply (rule ext)
  apply (auto simp: vspace_obj_fun_lift_def split: kernel_object.split arch_kernel_obj.split)
  done

lemma state_hyp_refs_of_pspaceI:
  "\<lbrakk> P (state_hyp_refs_of s); kheap s = kheap s' \<rbrakk> \<Longrightarrow> P (state_hyp_refs_of s')"
  unfolding state_hyp_refs_of_def
  by simp

lemma state_hyp_refs_update[iff]:
  "kheap (f s) = kheap s \<Longrightarrow> state_hyp_refs_of (f s) = state_hyp_refs_of s"
  by (clarsimp simp: state_hyp_refs_of_def
                  split: option.splits cong: option.case_cong)

lemma hyp_refs_of_hyp_live:
  "hyp_refs_of ko \<noteq> {} \<Longrightarrow> hyp_live ko"
  apply (cases ko, simp_all add: hyp_refs_of_def)
   apply (rename_tac tcb_ext)
   apply (simp add: tcb_hyp_refs_def hyp_live_def)
   apply (case_tac "tcb_vcpu (tcb_arch tcb_ext)"; clarsimp simp: tcb_vcpu_refs_def)
  apply (clarsimp simp: hyp_live_def arch_live_def refs_of_a_def vcpu_tcb_refs_def
                  split: arch_kernel_obj.splits option.splits)
  done

lemma hyp_refs_of_hyp_live_iff:
  "hyp_refs_of ko \<noteq> {} = hyp_live ko"
  apply (rule, clarsimp simp: hyp_refs_of_hyp_live)
  apply (cases ko; clarsimp simp add: hyp_live_def arch_live_def split: arch_kernel_obj.splits)
  done

lemma hyp_refs_of_hyp_live_obj:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> P ko; hyp_refs_of ko = {} \<rbrakk> \<Longrightarrow> False \<rbrakk> \<Longrightarrow> obj_at hyp_live p s"
  by (fastforce simp: obj_at_def hyp_refs_of_hyp_live)


(* use tcb_arch_ref to handle obj_refs in tcb_arch: currently there is a vcpu ref only *)

definition tcb_arch_ref :: "tcb \<Rightarrow> obj_ref option"
where "tcb_arch_ref t \<equiv> tcb_vcpu (tcb_arch t)"

lemma valid_tcb_arch_ref_lift:
  "tcb_arch_ref t = tcb_arch_ref t' \<Longrightarrow> valid_arch_tcb (tcb_arch t) = valid_arch_tcb (tcb_arch t')"
  by (simp add: valid_arch_tcb_def tcb_arch_ref_def)

lemma valid_arch_tcb_context_update[simp]:
  "valid_arch_tcb (tcb_context_update f t) = valid_arch_tcb t"
  unfolding valid_arch_tcb_def obj_at_def by simp

lemma valid_arch_arch_tcb_context_set[simp]:
  "valid_arch_tcb (arch_tcb_context_set a t) = valid_arch_tcb t"
  by (simp add: arch_tcb_context_set_def)

lemma tcb_arch_ref_context_update:
  "tcb_arch_ref (t\<lparr>tcb_arch := (arch_tcb_context_set a (tcb_arch t))\<rparr>) = tcb_arch_ref t"
  by (simp add: tcb_arch_ref_def arch_tcb_context_set_def)

lemma tcb_arch_ref_set_registers:
  "tcb_arch_ref (tcb\<lparr>tcb_arch := arch_tcb_set_registers regs (tcb_arch tcb)\<rparr>) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def arch_tcb_context_set_def arch_tcb_set_registers_def)

lemma valid_arch_arch_tcb_set_registers[simp]:
  "valid_arch_tcb (arch_tcb_set_registers a t) = valid_arch_tcb t"
   by (simp add: arch_tcb_set_registers_def)

lemma tcb_arch_ref_ipc_buffer_update: "\<And>tcb.
       tcb_arch_ref (tcb_ipc_buffer_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_mcpriority_update: "\<And>tcb.
       tcb_arch_ref (tcb_mcpriority_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_ctable_update: "\<And>tcb.
       tcb_arch_ref (tcb_ctable_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_vtable_update: "\<And>tcb.
       tcb_arch_ref (tcb_vtable_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_reply_update: "\<And>tcb.
       tcb_arch_ref (tcb_reply_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_caller_update: "\<And>tcb.
       tcb_arch_ref (tcb_caller_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_ipcframe_update: "\<And>tcb.
       tcb_arch_ref (tcb_ipcframe_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_state_update: "\<And>tcb.
       tcb_arch_ref (tcb_state_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_fault_handler_update: "\<And>tcb.
       tcb_arch_ref (tcb_fault_handler_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_fault_update: "\<And>tcb.
       tcb_arch_ref (tcb_fault_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

lemma tcb_arch_ref_bound_notification_update: "\<And>tcb.
       tcb_arch_ref (tcb_bound_notification_update f tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)


lemmas tcb_arch_ref_simps[simp] = tcb_arch_ref_ipc_buffer_update tcb_arch_ref_mcpriority_update
  tcb_arch_ref_ctable_update tcb_arch_ref_vtable_update tcb_arch_ref_reply_update
  tcb_arch_ref_caller_update tcb_arch_ref_ipcframe_update tcb_arch_ref_state_update
  tcb_arch_ref_fault_handler_update tcb_arch_ref_fault_update tcb_arch_ref_bound_notification_update
  tcb_arch_ref_context_update tcb_arch_ref_set_registers

lemma hyp_live_tcb_def: "hyp_live (TCB tcb) = bound (tcb_arch_ref tcb)"
  by (clarsimp simp: hyp_live_def tcb_arch_ref_def)

lemma hyp_live_tcb_simps[simp]:
"\<And>tcb f. hyp_live (TCB (tcb_ipc_buffer_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_mcpriority_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_ctable_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_vtable_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_reply_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_caller_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_ipcframe_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_state_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_fault_handler_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_fault_update f tcb)) = hyp_live (TCB tcb)"
"\<And>tcb f. hyp_live (TCB (tcb_bound_notification_update f tcb)) = hyp_live (TCB tcb)"
  by (simp_all add: hyp_live_tcb_def)


lemma valid_arch_tcb_pspaceI:
  "\<lbrakk> valid_arch_tcb t s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_arch_tcb t s'"
  unfolding valid_arch_tcb_def obj_at_def by (simp)

lemma valid_arch_tcb_typ_at:
  "\<lbrakk> valid_arch_tcb t s; \<And>T p. typ_at T p s \<Longrightarrow> typ_at T p s' \<rbrakk> \<Longrightarrow> valid_arch_tcb t s'"
  by (simp add: valid_arch_tcb_def)

lemma valid_arch_tcb_lift:
  "(\<And>T p. f \<lbrace>typ_at T p\<rbrace>) \<Longrightarrow> f \<lbrace>valid_arch_tcb t\<rbrace>"
  unfolding valid_arch_tcb_def
  by (wp hoare_vcg_all_lift hoare_vcg_imp_lift; simp)


lemma arch_gen_obj_refs_inD:
  "x \<in> arch_gen_obj_refs cap \<Longrightarrow> arch_gen_obj_refs cap = {x}"
  by (simp add: arch_gen_obj_refs_def)

lemma obj_ref_not_arch_gen_ref:
  "x \<in> obj_refs cap \<Longrightarrow> arch_gen_refs cap = {}"
  by (cases cap; simp add: arch_gen_obj_refs_def)

lemma arch_gen_ref_not_obj_ref:
  "x \<in> arch_gen_refs cap \<Longrightarrow> obj_refs cap = {}"
  by (cases cap; simp add: arch_gen_obj_refs_def)

lemma arch_gen_obj_refs_simps[simp]:
  "arch_gen_obj_refs (ASIDPoolCap a b) = {}"
  "arch_gen_obj_refs (PageTableCap c d) = {}"
  "arch_gen_obj_refs (PageDirectoryCap e f) = {}"
  "arch_gen_obj_refs (ASIDControlCap) = {}"
  "arch_gen_obj_refs (PageCap x1 x2 x3 x4 x5) = {}"
  "arch_gen_obj_refs (VCPUCap x6) = {}"
  by (simp add: arch_gen_obj_refs_def)+

lemma same_aobject_same_arch_gen_refs:
  "same_aobject_as ac ac' \<Longrightarrow> arch_gen_obj_refs ac = arch_gen_obj_refs ac'"
  by (clarsimp simp: arch_gen_obj_refs_def split: arch_cap.split_asm)

lemma valid_arch_mdb_eqI:
  assumes "valid_arch_mdb (is_original_cap s) (caps_of_state s)"
  assumes "caps_of_state s = caps_of_state s'"
  assumes "is_original_cap s = is_original_cap s'"
  shows "valid_arch_mdb (is_original_cap s') (caps_of_state s')"
  by (clarsimp)

lemma arch_tcb_context_absorbs[simp]:
  "arch_tcb_context_set uc2 (arch_tcb_context_set uc1 a_tcb) \<equiv> arch_tcb_context_set uc2 a_tcb"
  apply (simp add: arch_tcb_context_set_def)
  done

lemma arch_tcb_context_get_set[simp]:
  "arch_tcb_context_get (arch_tcb_context_set uc a_tcb) = uc"
  apply (simp add: arch_tcb_context_get_def arch_tcb_context_set_def)
  done

lemma vs_lookup_trans_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  shows "vs_lookup_trans s \<subseteq> vs_lookup_trans s'"
proof -
  have "vs_lookup1 s \<subseteq> vs_lookup1 s'"
    by (fastforce dest: ko elim: vs_lookup1_stateI2)
  thus ?thesis by (rule rtrancl_mono)
qed

lemma vs_lookup_pages_trans_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs_pages ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  shows "vs_lookup_pages_trans s \<subseteq> vs_lookup_pages_trans s'"
proof -
  have "vs_lookup_pages1 s \<subseteq> vs_lookup_pages1 s'"
    by (fastforce dest: ko elim: vs_lookup_pages1_stateI2)
  thus ?thesis by (rule rtrancl_mono)
qed

lemmas pte_ref_pages_simps[simp] = pte_ref_pages_def[split_simps pte.split]
lemmas pde_ref_pages_simps[simp] = pde_ref_pages_def[split_simps pde.split]

(* sanity check Arch_Kernel_Config_Lemmas version and shadow original name *)
lemma physBase_aligned[simplified pageBitsForSize_simps]:
  "is_aligned physBase (pageBitsForSize ARMSuperSection)"
  by simp (rule physBase_aligned)

lemma pptrBase_aligned[simplified pageBitsForSize_simps]:
  "is_aligned pptrBase (pageBitsForSize ARMSuperSection)"
  by (simp add: is_aligned_def pptrBase_def)

lemma pptrBaseOffset_aligned[simplified pageBitsForSize_simps]:
  "is_aligned pptrBaseOffset (pageBitsForSize ARMSuperSection)"
  by (auto simp: pptrBaseOffset_def physBase_aligned pptrBase_aligned
           elim: is_aligned_weaken intro: aligned_sub_aligned)

lemma pageBitsForSize_limit[simplified pageBitsForSize_simps, simp]:
  "pageBitsForSize sz \<le> pageBitsForSize ARMSuperSection"
  by (cases sz; simp)

lemma is_aligned_pptrBaseOffset[simplified pageBitsForSize_simps]:
  "is_aligned pptrBaseOffset (pageBitsForSize sz)"
  by (cases sz; clarsimp intro!: is_aligned_weaken[OF pptrBaseOffset_aligned])

lemma is_aligned_addrFromPPtr_n[simplified pageBitsForSize_simps]:
  "\<lbrakk> is_aligned p n; n \<le> (pageBitsForSize ARMSuperSection) \<rbrakk>
   \<Longrightarrow> is_aligned (Platform.ARM_HYP.addrFromPPtr p) n"
  by (auto simp: addrFromPPtr_def
           elim!: aligned_sub_aligned
           intro: is_aligned_weaken pptrBaseOffset_aligned)

lemma is_aligned_addrFromPPtr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (Platform.ARM_HYP.addrFromPPtr p) pageBits"
  by (simp add: is_aligned_addrFromPPtr_n pageBits_def)

lemma is_aligned_ptrFromPAddr_n[simplified pageBitsForSize_simps]:
  "\<lbrakk> is_aligned p n; n \<le> (pageBitsForSize ARMSuperSection)\<rbrakk>
   \<Longrightarrow> is_aligned (ptrFromPAddr p) n"
  by (auto simp: ptrFromPAddr_def
           elim!: aligned_add_aligned
           intro: is_aligned_weaken pptrBaseOffset_aligned)

lemma is_aligned_ptrFromPAddr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (ptrFromPAddr p) pageBits"
  by (simp add: is_aligned_ptrFromPAddr_n pageBits_def)

lemma is_aligned_ptrFromPAddrD[simplified pageBitsForSize_simps]:
  "\<lbrakk> is_aligned (ptrFromPAddr b) a; a \<le> (pageBitsForSize ARMSuperSection)\<rbrakk>
   \<Longrightarrow> is_aligned b a"
  by (simp add: ptrFromPAddr_def)
     (erule is_aligned_addD2, erule is_aligned_weaken[OF pptrBaseOffset_aligned])

end

declare ARM_HYP.arch_tcb_context_absorbs[simp]
declare ARM_HYP.arch_tcb_context_get_set[simp]

setup \<open>Add_Locale_Code_Defs.setup "ARM_HYP"\<close>
setup \<open>Add_Locale_Code_Defs.setup "ARM_HYP_A"\<close>

end
