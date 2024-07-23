(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInvariants_AI
imports InvariantsPre_AI "Eisbach_Tools.Apply_Trace_Cmd"
begin

section "Move this up"

qualify X64 (in Arch)

\<comment> \<open>---------------------------------------------------------------------------\<close>
section "Things to Move Up"

(* FIXME: move to spec level *)
(* global data and code of the kernel, not covered by any cap *)
axiomatization
  kernel_data_refs :: "word64 set"

end_qualify

\<comment> \<open>---------------------------------------------------------------------------\<close>
section "X64-specific invariant definitions"

qualify X64 (in Arch)
(* X64 has no interest for iarch_tcb (introduced for ARM_HYP) ,
    and we consider no non-trivial predicates of iarch_tcb,
    so an unspecified typedecl seems appropriate.
   In contrast to using a unit type, this avoids
    over-simplification of idle_tcb_at predicates,
    which would make it hard to use facts that talk about idle_tcb_at. *)
typedecl iarch_tcb
end_qualify

context Arch begin arch_global_naming

definition
  arch_tcb_to_iarch_tcb :: "arch_tcb \<Rightarrow> iarch_tcb"
where
  "arch_tcb_to_iarch_tcb arch_tcb \<equiv> undefined"

lemma iarch_tcb_context_set[simp]:
  "arch_tcb_to_iarch_tcb (arch_tcb_context_set p tcb) = arch_tcb_to_iarch_tcb tcb"
  by (auto simp: arch_tcb_to_iarch_tcb_def arch_tcb_context_set_def)

lemma iarch_tcb_set_registers[simp]:
  "arch_tcb_to_iarch_tcb (arch_tcb_set_registers regs arch_tcb)
     = arch_tcb_to_iarch_tcb arch_tcb"
  by (simp add: arch_tcb_to_iarch_tcb_def)

(* These simplifications allows us to keep many arch-specific proofs unchanged. *)

lemma arch_cap_fun_lift_expand[simp]:
  "(arch_cap_fun_lift (\<lambda> ac. case ac of
                                ASIDPoolCap obj_ref asid \<Rightarrow> P_ASIDPoolCap obj_ref asid
                              | ASIDControlCap \<Rightarrow> P_ASIDControlCap
                              | PageCap dev obj_ref rights maptyp sz vr \<Rightarrow> P_PageCap dev obj_ref rights maptyp sz vr
                              | PageTableCap obj_ref vr \<Rightarrow> P_PageTableCap obj_ref vr
                              | PageDirectoryCap obj_ref vr \<Rightarrow> P_PageDirectoryCap obj_ref vr
                              | PDPointerTableCap obj_ref vr \<Rightarrow> P_PDPointerTableCap obj_ref vr
                              | PML4Cap obj_ref asid \<Rightarrow> P_PML4Cap obj_ref asid
                              | IOPortCap first lst \<Rightarrow> P_IOPortCap first lst
                              | IOPortControlCap \<Rightarrow> P_IOPortControlCap)
                              \<comment> \<open>FIXME x64-vtd:
                              | IOSpaceCap domn pci \<Rightarrow> P_IOSpaceCap domn pci
                              | IOPageTableCap obj_ref lvl vr \<Rightarrow> P_IOPageTableCap obj_ref lvl vr)
                              \<close>
                      F) = (\<lambda>c.
   (case c of
      ArchObjectCap (ASIDPoolCap obj_ref asid) \<Rightarrow> P_ASIDPoolCap obj_ref asid
    | ArchObjectCap (ASIDControlCap) \<Rightarrow> P_ASIDControlCap
    | ArchObjectCap (PageCap dev obj_ref rights maptyp sz vr) \<Rightarrow> P_PageCap dev obj_ref rights maptyp sz vr
    | ArchObjectCap (PageTableCap obj_ref vr) \<Rightarrow> P_PageTableCap obj_ref vr
    | ArchObjectCap (PageDirectoryCap obj_ref asid) \<Rightarrow> P_PageDirectoryCap obj_ref asid
    | ArchObjectCap (PDPointerTableCap obj_ref vr) \<Rightarrow> P_PDPointerTableCap obj_ref vr
    | ArchObjectCap (PML4Cap obj_ref asid) \<Rightarrow> P_PML4Cap obj_ref asid
    | ArchObjectCap (IOPortCap first lst) \<Rightarrow> P_IOPortCap first lst
    | ArchObjectCap (IOPortControlCap) \<Rightarrow> P_IOPortControlCap
\<comment> \<open>FIXME x64-vtd:
    | ArchObjectCap (IOSpaceCap domn pci) \<Rightarrow> P_IOSpaceCap domn pci
    | ArchObjectCap (IOPageTableCap obj_ref lvl vr) \<Rightarrow> P_IOPageTableCap obj_ref lvl vr
\<close>
    | _ \<Rightarrow> F))"
  apply (rule ext)
  by (simp add: arch_cap_fun_lift_def)

lemma arch_obj_fun_lift_expand[simp]:
  "(arch_obj_fun_lift (\<lambda> ako. case ako of
                                ASIDPool pool \<Rightarrow> P_ASIDPool pool
                              | PageTable pt \<Rightarrow> P_PageTable pt
                              | PageDirectory pd \<Rightarrow> P_PageDirectory pd
                              | DataPage dev s \<Rightarrow> P_DataPage dev s
                              | PDPointerTable pdpt \<Rightarrow> P_PDPT pdpt
                              | PageMapL4 pml \<Rightarrow> P_PML4 pml)
                      F) = (\<lambda>ko.
   (case ko of
      ArchObj (ASIDPool pool) \<Rightarrow> P_ASIDPool pool
    | ArchObj (PageTable pt) \<Rightarrow> P_PageTable pt
    | ArchObj (PageDirectory pd) \<Rightarrow> P_PageDirectory pd
    | ArchObj (DataPage dev s) \<Rightarrow> P_DataPage dev s
    | ArchObj (PDPointerTable pdpt) \<Rightarrow> P_PDPT pdpt
    | ArchObj (PageMapL4 pml) \<Rightarrow> P_PML4 pml
    | _ \<Rightarrow> F))"
  apply (rule ext)
  by (simp only: arch_obj_fun_lift_def)

lemmas aa_type_simps =
  aa_type_def[split_simps arch_kernel_obj.split]

lemmas a_type_def = a_type_def[simplified aa_type_def]

lemmas a_type_simps = a_type_def[split_simps kernel_object.split arch_kernel_obj.split]

definition
  "vmsz_aligned ref sz \<equiv> is_aligned ref (pageBitsForSize sz)"

(* Current x86-64 processors allow the use of only 48 bits of the 64 bits of virtual
   address space provided by the instruction set architecture, and require that the
   most significant 17 bits of any virtual address are identical. *)

definition canonical_address_of :: "48 word \<Rightarrow> obj_ref"
where
  "canonical_address_of x \<equiv> scast x"

definition canonical_address :: "obj_ref \<Rightarrow> bool"
where
  "canonical_address x \<equiv> canonical_address_of (ucast x) = x"

text \<open>An ASID is well-formed if it is within @{term "mask asid_bits"}.\<close>
definition
  asid_wf :: "asid \<Rightarrow> bool"
where
  "asid_wf a \<equiv> a \<le> 2 ^ asid_bits - 1"

(* Alternative definitions for compatibilty with older proofs. *)
lemma asid_wf_def2:
  "asid_wf asid \<equiv> asid \<le> mask asid_bits"
  by (simp add: asid_wf_def mask_def)

lemma asid_wf_def3:
  "asid_wf asid \<equiv> asid && mask asid_bits = asid"
  by (simp add: asid_wf_def2 and_mask_eq_iff_le_mask)

definition
  "wellformed_mapdata size_bits \<equiv>
   \<lambda>(asid, vref). 0 < asid \<and> asid_wf asid
                    \<and> is_aligned vref size_bits
                    \<and> vref < pptr_base
                    \<and> canonical_address vref"

definition
  wellformed_acap :: "arch_cap \<Rightarrow> bool"
where
  "wellformed_acap ac \<equiv>
   case ac of
     ASIDPoolCap r as \<Rightarrow> is_aligned as asid_low_bits \<and> asid_wf as
   | PageCap dev r rghts maptyp sz mapdata \<Rightarrow> rghts \<in> valid_vm_rights \<and>
     case_option (maptyp=VMNoMap) (wellformed_mapdata (pageBitsForSize sz) and (\<lambda>_. maptyp\<noteq>VMNoMap)) mapdata
   | PageTableCap r (Some mapdata) \<Rightarrow>
     wellformed_mapdata pd_shift_bits mapdata
   | PageDirectoryCap r (Some mapdata) \<Rightarrow>
     wellformed_mapdata pdpt_shift_bits mapdata
   | PDPointerTableCap r (Some mapdata) \<Rightarrow>
     wellformed_mapdata pml4_shift_bits mapdata
   | PML4Cap r (Some asid) \<Rightarrow> 0 < asid \<and> asid_wf asid
   | IOPortCap f l \<Rightarrow> f \<le> l
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
  "pd_pointer_table_at \<equiv> typ_at (AArch APDPointerTable)"
abbreviation
  "page_map_l4_at \<equiv> typ_at (AArch APageMapL4)"

abbreviation
  "vspace_table_at p s \<equiv> page_map_l4_at p s \<or> pd_pointer_table_at p s
                         \<or> page_directory_at p s \<or> page_table_at p s"

definition
  "pde_at p \<equiv> page_directory_at (p && ~~ mask pd_bits)
                  and K (is_aligned p 3)"
definition
  "pte_at p \<equiv> page_table_at (p && ~~ mask pt_bits)
                  and K (is_aligned p 3)"
definition
  "pdpte_at p \<equiv> pd_pointer_table_at (p && ~~ mask pdpt_bits)
                   and K (is_aligned p 3)"
definition
  "pml4e_at p \<equiv> page_map_l4_at (p && ~~ mask pml4_bits)
                   and K (is_aligned p 3)"

definition
  valid_arch_cap_ref :: "arch_cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_cap_ref ac s \<equiv> (case ac of
    ASIDPoolCap r as \<Rightarrow> typ_at (AArch AASIDPool) r s
  | ASIDControlCap \<Rightarrow> True
  | IOPortCap first_port last_port \<Rightarrow> True
  | PageCap dev r rghts maptyp sz mapdata \<Rightarrow>
      if dev then typ_at (AArch (ADeviceData sz)) r s
             else typ_at (AArch (AUserData sz)) r s
  | PageTableCap r mapdata \<Rightarrow> typ_at (AArch APageTable) r s
  | PageDirectoryCap r mapdata\<Rightarrow> typ_at (AArch APageDirectory) r s
  | PDPointerTableCap r mapdata \<Rightarrow> typ_at (AArch APDPointerTable) r s
  | PML4Cap r mapdata \<Rightarrow> typ_at (AArch APageMapL4) r s
  | IOPortControlCap \<Rightarrow> True)"

lemmas valid_arch_cap_ref_simps =
  valid_arch_cap_ref_def[split_simps arch_cap.split]

definition
  valid_arch_cap :: "arch_cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_cap ac s \<equiv> (case ac of
    ASIDPoolCap r as \<Rightarrow>
    typ_at (AArch AASIDPool) r s \<and> is_aligned as asid_low_bits \<and> asid_wf as
  | ASIDControlCap \<Rightarrow> True
  | IOPortCap first_port last_port \<Rightarrow> first_port \<le> last_port
  | PageCap dev r rghts maptyp sz mapdata \<Rightarrow>
    (if dev then (typ_at (AArch (ADeviceData sz)) r s)
            else (typ_at (AArch (AUserData sz)) r s)) \<and>
    (rghts \<in> valid_vm_rights) \<and>
    (case_option (maptyp=VMNoMap) (wellformed_mapdata (pageBitsForSize sz) and (\<lambda>_. maptyp\<noteq>VMNoMap)) mapdata)
  | PageTableCap r mapdata \<Rightarrow>
    typ_at (AArch APageTable) r s \<and>
    case_option True (wellformed_mapdata pd_shift_bits) mapdata
  | PageDirectoryCap r mapdata \<Rightarrow>
    typ_at (AArch APageDirectory) r s \<and>
    case_option True (wellformed_mapdata pdpt_shift_bits) mapdata
  | PDPointerTableCap r mapdata \<Rightarrow>
    typ_at (AArch APDPointerTable) r s \<and>
    case_option True (wellformed_mapdata pml4_shift_bits) mapdata
  | PML4Cap r mapdata \<Rightarrow>
    typ_at (AArch APageMapL4) r s \<and>
    case_option True (\<lambda>asid. 0 < asid \<and> asid_wf asid) mapdata
  | IOPortControlCap \<Rightarrow> True)"

lemmas valid_arch_cap_simps =
  valid_arch_cap_def[split_simps arch_cap.split]

definition
  "is_nondevice_page_cap_arch \<equiv> \<lambda>cap. case cap of (PageCap False _ _ _ _ _) \<Rightarrow>  True
                                                 | _ \<Rightarrow> False"

declare is_nondevice_page_cap_arch_def [simp]

definition
  "is_nondevice_page_cap \<equiv> \<lambda>c. arch_cap_fun_lift is_nondevice_page_cap_arch False c"

lemma is_nondevice_page_cap:
  "is_nondevice_page_cap c = (\<exists> p q r s t. c = ArchObjectCap (PageCap False p q r s t))"
  by (auto simp: is_nondevice_page_cap_def split: cap.splits arch_cap.splits)

lemmas is_nondevice_page_cap_simps = is_nondevice_page_cap

primrec
  acap_class :: "arch_cap \<Rightarrow> capclass"
where
  "acap_class (ASIDPoolCap x y)       = PhysicalClass"
| "acap_class (ASIDControlCap)        = ASIDMasterClass"
| "acap_class (PageCap d x y m sz z)  = PhysicalClass"
| "acap_class (PageTableCap x y)      = PhysicalClass"
| "acap_class (PageDirectoryCap x y)  = PhysicalClass"
| "acap_class (PDPointerTableCap x y) = PhysicalClass"
| "acap_class (PML4Cap x y)           = PhysicalClass"
| "acap_class (IOPortCap x y)         = IOPortClass"
| "acap_class (IOPortControlCap)      = IOPortClass"

definition
  valid_ipc_buffer_cap_arch :: "arch_cap \<Rightarrow> machine_word \<Rightarrow> bool"
where
  "valid_ipc_buffer_cap_arch ac bufptr \<equiv>
         case ac of
              (PageCap False ref rghts maptyp sz mapdata) \<Rightarrow>
                   is_aligned bufptr msg_align_bits
            | _ \<Rightarrow> False"

declare valid_ipc_buffer_cap_arch_def[simp]

definition
  "valid_ipc_buffer_cap c bufptr \<equiv>
    case c of
      NullCap \<Rightarrow> True
    | ArchObjectCap acap \<Rightarrow> valid_ipc_buffer_cap_arch acap bufptr
    | _ \<Rightarrow> False"

definition "data_at \<equiv>
  \<lambda>sz p s. typ_at (AArch (AUserData sz)) p s
         \<or> typ_at (AArch (ADeviceData sz)) p s"

definition
  valid_arch_tcb :: "arch_tcb \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_tcb \<equiv> \<lambda>a. \<top>"

definition
  valid_arch_idle :: "iarch_tcb \<Rightarrow> bool"
where
  "valid_arch_idle \<equiv> \<top>"

(* Validity of vspace table entries, defined shallowly. *)

primrec
  valid_pte :: "pte \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pte (InvalidPTE) = \<top>"
| "valid_pte (SmallPagePTE ptr x y) =
       data_at X64SmallPage (ptrFromPAddr ptr)"

primrec
  valid_pde :: "pde \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pde (InvalidPDE) = \<top>"
| "valid_pde (LargePagePDE ptr x y) =
       data_at X64LargePage (ptrFromPAddr ptr)"
| "valid_pde (PageTablePDE ptr x z) =
       typ_at (AArch APageTable) (ptrFromPAddr ptr)"

primrec
  valid_pdpte :: "pdpte \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pdpte (InvalidPDPTE) = \<top>"
| "valid_pdpte (HugePagePDPTE ptr x y) =
       data_at X64HugePage (ptrFromPAddr ptr)"
| "valid_pdpte (PageDirectoryPDPTE ptr x z) =
       typ_at (AArch APageDirectory) (ptrFromPAddr ptr)"

primrec
  valid_pml4e :: "pml4e \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pml4e (InvalidPML4E) = \<top>"
| "valid_pml4e (PDPointerTablePML4E ptr x y) =
       typ_at (AArch APDPointerTable) (ptrFromPAddr ptr)"

(* Validity of vspace table entries, defined deeply. *)

primrec
  valid_pde_rec :: "pde \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pde_rec (InvalidPDE) = \<top>"
| "valid_pde_rec (LargePagePDE p _ _) =
       data_at X64LargePage (ptrFromPAddr p)"
| "valid_pde_rec (PageTablePDE p _ _) =
       (\<lambda>s. \<exists>pt. ako_at (PageTable pt) (ptrFromPAddr p) s \<and> (\<forall>i. valid_pte (pt i) s))"

primrec
  valid_pdpte_rec :: "pdpte \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pdpte_rec (InvalidPDPTE) = \<top>"
| "valid_pdpte_rec (HugePagePDPTE p _ _) =
       data_at X64HugePage (ptrFromPAddr p)"
| "valid_pdpte_rec (PageDirectoryPDPTE p _ _) =
       (\<lambda>s. \<exists>pd. ako_at (PageDirectory pd) (ptrFromPAddr p) s \<and> (\<forall>i. valid_pde_rec (pd i) s))"

primrec
  valid_pml4e_rec :: "pml4e \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pml4e_rec (InvalidPML4E) = \<top>"
| "valid_pml4e_rec (PDPointerTablePML4E p _ _) =
       (\<lambda>s. \<exists>pdpt. ako_at (PDPointerTable pdpt) (ptrFromPAddr p) s \<and> (\<forall>i. valid_pdpte_rec (pdpt i) s))"

(* Kernel mappings in x64 go from pptr base to the top of memory
   but weird x64 conventions to do with having only 48 bits
   of addressible virtual memory mean we need to mask *)
definition
  kernel_mapping_slots :: "9 word set" where
 "kernel_mapping_slots \<equiv> {x. x \<ge> ucast (pptr_base >> pml4_shift_bits)}"

primrec
  valid_vspace_obj :: "arch_kernel_obj \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_vspace_obj (ASIDPool pool) =
   (\<lambda>s. \<forall>x \<in> ran pool. typ_at (AArch APageMapL4) x s)"
| "valid_vspace_obj (PageMapL4 pm) =
   (\<lambda>s. \<forall>x \<in> -kernel_mapping_slots. valid_pml4e (pm x) s)"
| "valid_vspace_obj (PDPointerTable pdpt) = (\<lambda>s. \<forall>x. valid_pdpte (pdpt x) s)"
| "valid_vspace_obj (PageDirectory pd) = (\<lambda>s. \<forall>x. valid_pde (pd x) s)"
| "valid_vspace_obj (PageTable pt) = (\<lambda>s. \<forall>x. valid_pte (pt x) s)"
| "valid_vspace_obj (DataPage dev sz) = \<top>"

(* FIXME x64: check hardware to see if any bits are forbidden *)
definition
  wellformed_pte :: "pte \<Rightarrow> bool"
where
  "wellformed_pte pte \<equiv> case pte of
   SmallPagePTE p attr r \<Rightarrow>
       r \<in> valid_vm_rights \<and> vmsz_aligned p X64SmallPage
   | _ \<Rightarrow> True"

(* FIXME x64: check hardware to see if any bits are forbidden *)
definition
  wellformed_pde :: "pde \<Rightarrow> bool"
where
  "wellformed_pde pde \<equiv> case pde of
   pde.LargePagePDE p attr r \<Rightarrow> r \<in> valid_vm_rights \<and> vmsz_aligned p X64LargePage
 | pde.PageTablePDE p attr r \<Rightarrow> r \<in> valid_vm_rights \<and> is_aligned p table_size
 | _ \<Rightarrow> True"

(* FIXME x64: check hardware to see if any bits are forbidden *)
definition
  wellformed_pdpte :: "pdpte \<Rightarrow> bool"
where
  "wellformed_pdpte pdpte \<equiv> case pdpte of
   pdpte.HugePagePDPTE p attr r \<Rightarrow> r \<in> valid_vm_rights \<and> vmsz_aligned p X64HugePage
 | pdpte.PageDirectoryPDPTE p attr r \<Rightarrow> r \<in> valid_vm_rights \<and> is_aligned p table_size
 | _ \<Rightarrow> True"

(* FIXME x64: check hardware to see if any bits are forbidden *)
definition
  wellformed_pml4e :: "pml4e \<Rightarrow> bool"
where
  "wellformed_pml4e pml4e \<equiv> case pml4e of
  pml4e.PDPointerTablePML4E p attr r \<Rightarrow> r \<in> valid_vm_rights \<and> is_aligned p table_size
 | _ \<Rightarrow> True"

definition
  wellformed_vspace_obj :: "arch_kernel_obj \<Rightarrow> bool"
where
  "wellformed_vspace_obj ao \<equiv> case ao of
     PageTable pt \<Rightarrow> (\<forall>pte\<in>range pt. wellformed_pte pte)
   | PageDirectory pd \<Rightarrow> (\<forall>pde\<in>range pd. wellformed_pde pde)
   | PDPointerTable pdpt \<Rightarrow> (\<forall>pdpte\<in>range pdpt. wellformed_pdpte pdpte)
   | PageMapL4 pm \<Rightarrow> (\<forall>pml4e\<in>range pm. wellformed_pml4e pml4e)
   | _ \<Rightarrow> True"

definition
  arch_valid_obj :: "arch_kernel_obj \<Rightarrow>  'z::state_ext state \<Rightarrow> bool"
where
  "arch_valid_obj ao s \<equiv> wellformed_vspace_obj ao"

lemmas
  wellformed_pte_simps[simp] =
  wellformed_pte_def[split_simps pte.split]

lemmas
  wellformed_pde_simps[simp] =
  wellformed_pde_def[split_simps pde.split]

lemmas
  wellformed_pdpte_simps[simp] =
  wellformed_pdpte_def[split_simps pdpte.split]

lemmas
  wellformed_pml4e_simps[simp] =
  wellformed_pml4e_def[split_simps pml4e.split]

lemmas
  arch_valid_obj_simps[simp] =
  arch_valid_obj_def[split_simps arch_kernel_obj.split]

lemmas
  wellformed_vspace_obj_simps[simp] =
  wellformed_vspace_obj_def[split_simps arch_kernel_obj.split]

lemma wellformed_arch_pspace: "\<And>ao. \<lbrakk>arch_valid_obj ao s; kheap s = kheap s'\<rbrakk>
          \<Longrightarrow> arch_valid_obj ao s'" by simp

section "Virtual Memory"

definition
  equal_kernel_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
 "equal_kernel_mappings \<equiv> \<lambda>s.
    \<forall>x y pm pm'. ko_at (ArchObj (PageMapL4 pm)) x s \<and> ko_at (ArchObj (PageMapL4 pm')) y s
       \<longrightarrow> (\<forall>w \<in> kernel_mapping_slots. pm w = pm' w)"

definition
  pde_ref :: "pde \<Rightarrow> obj_ref option"
where
  "pde_ref pde \<equiv> case pde of
    PageTablePDE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  pdpte_ref :: "pdpte \<Rightarrow> obj_ref option"
where
  "pdpte_ref pde \<equiv> case pde of
    PageDirectoryPDPTE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  pml4e_ref :: "pml4e \<Rightarrow> obj_ref option"
where
  "pml4e_ref p \<equiv> case p of
    PDPointerTablePML4E ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

(* vs_ref is used to keep track of the translations of a given address.
   The first argument is an index into the type of table given by the
   second argument. For example:
     "VSRef x (Some APageTable)"
   indicates that you use index x into the page table level of translation.

   These can be combined into a list to show the provenance of an address.
   For example:
    [VSRef x (Some APageTable), VSRef y (Some APageDirectory),
     VSRef z (Some APDPointerTable), VSRef w (Some APageMapL4),
     VSRef v (Some AASIDPool)]
   shows the full translation from ASIDPool down through four levels of
   page translation. *)
datatype vs_ref = VSRef word64 "aa_type option"

definition
  vs_ref_aatype :: "vs_ref \<Rightarrow> aa_type option" where
 "vs_ref_aatype vsref \<equiv> case vsref of VSRef x atype \<Rightarrow> atype"

definition
  vs_refs_arch :: "arch_kernel_obj \<Rightarrow> (vs_ref \<times> obj_ref) set" where
  "vs_refs_arch \<equiv> \<lambda>ko. case ko of
    ASIDPool pool \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  | PageMapL4 pm \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageMapL4), p)) `
      graph_of (\<lambda>x. if x \<in> kernel_mapping_slots then None else pml4e_ref (pm x))
  | PDPointerTable pdpt \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APDPointerTable), p)) ` graph_of (pdpte_ref \<circ> pdpt)
  | PageDirectory pd \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p)) ` graph_of (pde_ref \<circ> pd)
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
  vs_asid_refs :: "(3 word \<rightharpoonup> obj_ref) \<Rightarrow> vs_chain set"
where
  "vs_asid_refs t \<equiv> (\<lambda>(r,p). ([VSRef (ucast r) None], p)) ` graph_of t"

definition
  vs_lookup :: "'z::state_ext state \<Rightarrow> vs_chain set"
where
  "vs_lookup \<equiv> \<lambda>s. vs_lookup_trans s `` vs_asid_refs (x64_asid_table (arch_state s))"

definition "second_level_tables \<equiv> arch_state.x64_global_pdpts"

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

definition
  valid_vspace_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_vspace_objs \<equiv> \<lambda>s. \<forall>p rs ao. (rs \<rhd> p) s \<longrightarrow> ko_at (ArchObj ao) p s \<longrightarrow> valid_vspace_obj ao s"

definition
  pde_ref_pages :: "pde \<Rightarrow> obj_ref option"
where
  "pde_ref_pages pde \<equiv> case pde of
    PageTablePDE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | LargePagePDE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  pte_ref_pages :: "pte \<Rightarrow> obj_ref option"
where
  "pte_ref_pages pte \<equiv> case pte of
    SmallPagePTE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  pdpte_ref_pages :: "pdpte \<Rightarrow> obj_ref option"
where
  "pdpte_ref_pages pdpte \<equiv> case pdpte of
    HugePagePDPTE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | PageDirectoryPDPTE ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  pml4e_ref_pages :: "pml4e \<Rightarrow> obj_ref option"
where
  "pml4e_ref_pages pml4e \<equiv> case pml4e of
    PDPointerTablePML4E ptr x z \<Rightarrow> Some (ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  vs_refs_pages_arch :: "arch_kernel_obj \<Rightarrow> (vs_ref \<times> obj_ref) set" where
  "vs_refs_pages_arch \<equiv> \<lambda>ko. case ko of
    (ASIDPool pool) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  | (PageMapL4 pm) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageMapL4), p)) `
      graph_of (\<lambda>x. if x \<in> kernel_mapping_slots then None else pml4e_ref_pages (pm x))
  | (PDPointerTable pdpt) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APDPointerTable), p)) `
      graph_of (pdpte_ref_pages \<circ> pdpt)
  | (PageDirectory pd) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p)) `
      graph_of (pde_ref_pages \<circ> pd)
  | (PageTable pt) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageTable), p)) `
      graph_of (pte_ref_pages \<circ> pt)
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
  "vs_lookup_pages \<equiv> \<lambda>s. vs_lookup_pages_trans s `` vs_asid_refs (x64_asid_table (arch_state s))"


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
  "vspace_obj_fun_lift \<equiv> arch_obj_fun_lift"

lemmas vspace_obj_fun_lift_expand[simp]
  = arch_obj_fun_lift_expand[folded vspace_obj_fun_lift_def]

definition
  pde_mapping_bits :: "nat"
where
 "pde_mapping_bits \<equiv> pageBitsForSize X64LargePage"

definition
  pte_mapping_bits :: "nat"
where
 "pte_mapping_bits \<equiv> pageBitsForSize X64SmallPage"

definition
  pdpte_mapping_bits :: "nat"
where
 "pdpte_mapping_bits \<equiv> pageBitsForSize X64HugePage"

definition
  pml4e_mapping_bits :: "nat"
where
  "pml4e_mapping_bits \<equiv> pageBitsForSize X64HugePage + ptTranslationBits"


(* FIXME x64: do we need all these things? *)
definition
  valid_pte_kernel_mappings :: "pte \<Rightarrow> vspace_ref
                                   \<Rightarrow> x64_vspace_region_uses \<Rightarrow> bool"
where
 "valid_pte_kernel_mappings pte vref uses \<equiv> case pte of
    InvalidPTE \<Rightarrow>
        \<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}.
                    uses x \<noteq> X64VSpaceKernelWindow
  | SmallPagePTE ptr atts rghts \<Rightarrow>
        ptrFromPAddr ptr = vref
        \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}. uses x = use)
             \<and> (use \<in> {X64VSpaceKernelWindow, X64VSpaceDeviceWindow}))
        \<and> rghts = {}"

definition
  valid_pt_kernel_mappings_arch :: "vspace_ref \<Rightarrow> x64_vspace_region_uses \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
where
 "valid_pt_kernel_mappings_arch vref uses \<equiv> \<lambda> obj. case obj of
    PageTable pt \<Rightarrow>
        \<forall>x. valid_pte_kernel_mappings
             (pt x) (vref + (ucast x << pte_mapping_bits)) uses
  | _ \<Rightarrow> False"

declare valid_pt_kernel_mappings_arch_def[simp]

definition
  "valid_pt_kernel_mappings vref uses = vspace_obj_fun_lift (valid_pt_kernel_mappings_arch vref uses) False"

definition
  valid_pde_kernel_mappings :: "pde \<Rightarrow> vspace_ref \<Rightarrow> x64_vspace_region_uses \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "valid_pde_kernel_mappings pde vref uses \<equiv> case pde of
    InvalidPDE \<Rightarrow>
        (\<lambda>s. \<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}.
                    uses x \<noteq> X64VSpaceKernelWindow)
  | PageTablePDE ptr _ _ \<Rightarrow>
        obj_at (valid_pt_kernel_mappings vref uses)
                    (ptrFromPAddr ptr)
  | LargePagePDE ptr atts rghts \<Rightarrow>
        (\<lambda>s. ptrFromPAddr ptr = vref
             \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}. uses x = use)
                   \<and> (use \<in> {X64VSpaceKernelWindow, X64VSpaceDeviceWindow}))
             \<and> rghts = {})"

definition
  valid_pd_kernel_mappings_arch :: "vspace_ref \<Rightarrow> x64_vspace_region_uses \<Rightarrow> 'z::state_ext state
                                    \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
where
 "valid_pd_kernel_mappings_arch vref uses \<equiv> \<lambda>s obj.
  case obj of
    PageDirectory pd \<Rightarrow>
      (\<forall>x. valid_pde_kernel_mappings
             (pd x) (vref + (ucast x << pde_mapping_bits)) uses s)
  | _ \<Rightarrow> False"

declare valid_pd_kernel_mappings_arch_def[simp]

definition
  "valid_pd_kernel_mappings vref uses = (\<lambda>s. vspace_obj_fun_lift (valid_pd_kernel_mappings_arch vref uses s) False)"

definition
  valid_pdpte_kernel_mappings :: "pdpte \<Rightarrow> vspace_ref \<Rightarrow> x64_vspace_region_uses \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "valid_pdpte_kernel_mappings pdpte vref uses \<equiv> case pdpte of
    InvalidPDPTE \<Rightarrow>
        (\<lambda>s. \<forall>x \<in> {vref .. vref + 2 ^ pdpte_mapping_bits - 1}.
                    uses x \<noteq> X64VSpaceKernelWindow)
  | PageDirectoryPDPTE ptr _ _ \<Rightarrow>
        (\<lambda>s. obj_at (valid_pd_kernel_mappings vref uses s)
                    (ptrFromPAddr ptr) s)
  | HugePagePDPTE ptr atts rghts \<Rightarrow>
        (\<lambda>s. ptrFromPAddr ptr = vref
             \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pdpte_mapping_bits - 1}. uses x = use)
                   \<and> (use \<in> {X64VSpaceKernelWindow, X64VSpaceDeviceWindow}))
             \<and> rghts = {})"

definition
  valid_pdpt_kernel_mappings_arch :: "vspace_ref \<Rightarrow> x64_vspace_region_uses \<Rightarrow> 'z::state_ext state
                                    \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
where
 "valid_pdpt_kernel_mappings_arch vref uses \<equiv> \<lambda>s obj.
  case obj of
    PDPointerTable pdpt \<Rightarrow>
      (\<forall>x. valid_pdpte_kernel_mappings
             (pdpt x) (vref + (ucast x << pdpte_mapping_bits)) uses s)
  | _ \<Rightarrow> False"

declare valid_pdpt_kernel_mappings_arch_def[simp]

definition
  "valid_pdpt_kernel_mappings vref uses = (\<lambda>s. vspace_obj_fun_lift (valid_pdpt_kernel_mappings_arch vref uses s) False)"

definition
  valid_pml4e_kernel_mappings :: "pml4e \<Rightarrow> vspace_ref \<Rightarrow> x64_vspace_region_uses \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "valid_pml4e_kernel_mappings pml4e vref uses \<equiv> case pml4e of
    InvalidPML4E \<Rightarrow>
        (\<lambda>s. \<forall>x \<in> {vref .. vref + 2 ^ pml4e_mapping_bits - 1}. uses x \<noteq> X64VSpaceKernelWindow)
  | PDPointerTablePML4E ptr _ _ \<Rightarrow>
        (\<lambda>s. obj_at (valid_pdpt_kernel_mappings vref uses s)
                    (ptrFromPAddr ptr) s)"

definition
  valid_pml4_kernel_mappings_arch :: "x64_vspace_region_uses \<Rightarrow> 'z::state_ext state
                                    \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
where
 "valid_pml4_kernel_mappings_arch uses \<equiv> \<lambda>s obj.
  case obj of
    PageMapL4 pm \<Rightarrow>
      (\<forall>x. valid_pml4e_kernel_mappings
             (pm x) (canonical_address_of (ucast x << pml4e_mapping_bits)) uses s)
  | _ \<Rightarrow> False"

declare valid_pml4_kernel_mappings_arch_def[simp]

definition
  "valid_pml4_kernel_mappings uses = (\<lambda>s. vspace_obj_fun_lift (valid_pml4_kernel_mappings_arch uses s) False)"

definition
  valid_global_vspace_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
 "valid_global_vspace_mappings \<equiv> \<lambda>s.
  obj_at (valid_pml4_kernel_mappings (x64_kernel_vspace (arch_state s)) s)
    (x64_global_pml4 (arch_state s)) s"

fun
  is_vspace_typ :: "a_type \<Rightarrow> bool"
where
  "is_vspace_typ (AArch  _)    = True"
| "is_vspace_typ  _            = False"

definition
  valid_vso_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_vso_at p \<equiv> \<lambda>s. \<exists>ao. ko_at (ArchObj ao) p s \<and> valid_vspace_obj ao s"

definition
  valid_ao_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_ao_at p \<equiv> \<lambda>s. \<exists>ao. ko_at (ArchObj ao) p s \<and> valid_vspace_obj ao s"

definition
  "empty_table_arch S \<equiv> \<lambda> ko.
   case ko of
     PageMapL4 pm \<Rightarrow>
       \<forall>x. (\<forall>r. pml4e_ref (pm x) = Some r \<longrightarrow> r \<in> S) \<and>
            (x \<notin> kernel_mapping_slots \<longrightarrow> pm x = InvalidPML4E)
   | PDPointerTable pdpt \<Rightarrow> \<forall>x. pdpt x = InvalidPDPTE
   | PageDirectory pd \<Rightarrow> \<forall>x. pd x = InvalidPDE
   | PageTable pt \<Rightarrow> \<forall>x. pt x = InvalidPTE
   | _ \<Rightarrow> False"

declare empty_table_arch_def[simp]

definition
  "empty_table S \<equiv> arch_obj_fun_lift (empty_table_arch S) False"

definition
  "valid_kernel_mappings_if_pm_arch S \<equiv> \<lambda> ko. case ko of
     (PageMapL4 pm) \<Rightarrow>
        \<forall>x r. pml4e_ref (pm x) = Some r
                  \<longrightarrow> ((r \<in> S) = (x \<in> kernel_mapping_slots))
  | _ \<Rightarrow> True"

declare valid_kernel_mappings_if_pm_arch_def[simp]

definition
  "valid_kernel_mappings_if_pm S \<equiv> arch_obj_fun_lift (valid_kernel_mappings_if_pm_arch S) True"

definition
  "aligned_pte pte \<equiv>
     case pte of
     SmallPagePTE p _ _ \<Rightarrow> vmsz_aligned p X64SmallPage
     | _ \<Rightarrow> True"

lemmas aligned_pte_simps[simp] =
       aligned_pte_def[split_simps pte.split]

definition
  "aligned_pde pde \<equiv>
     case pde of
     LargePagePDE p _ _ \<Rightarrow> vmsz_aligned p X64LargePage
     | _ \<Rightarrow> True"

lemmas aligned_pde_simps[simp] =
       aligned_pde_def[split_simps pde.split]

definition
  "aligned_pdpte pdpte \<equiv>
     case pdpte of
     HugePagePDPTE p _ _ \<Rightarrow> vmsz_aligned p X64HugePage
     | _ \<Rightarrow> True"

lemmas aligned_pdpte_simps[simp] =
       aligned_pdpte_def[split_simps pdpte.split]

(* FIXME x64: this is correct, but do we need the final bit? *)
definition
  valid_global_pdpt :: "(9 word \<Rightarrow> pdpte) \<comment> \<open>*\<Rightarrow> 'z::state_ext state\<close> \<Rightarrow> bool"
where
  "valid_global_pdpt m \<equiv> (\<forall>x\<in>{0 .. 0x1FE}. \<exists>ptr attr R. m x =  HugePagePDPTE ptr attr R)
                             \<and> (\<exists>t attr R. m 0x1FF = PageDirectoryPDPTE t attr R
                                 \<comment> \<open>\<and> t \<in> set (x64_global_pds (arch_state s))\<close>)"

definition
  valid_global_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_global_objs \<equiv>
  \<lambda>s. valid_vso_at (x64_global_pml4 (arch_state s)) s \<and>
           obj_at (empty_table (set (second_level_tables (arch_state s))))
                  (x64_global_pml4 (arch_state s)) s \<and>
      (\<forall>p\<in>set (x64_global_pdpts (arch_state s)).
          \<exists>pdpt. ko_at (ArchObj (PDPointerTable pdpt)) p s \<and>
                  (\<forall>x. aligned_pdpte (pdpt x) \<and>
                       (\<forall>r. pdpte_ref (pdpt x) = Some r
                            \<longrightarrow> r \<in> set (x64_global_pds (arch_state s))))
                  \<and> valid_global_pdpt pdpt) \<and>
      (\<forall>p\<in>set (x64_global_pds (arch_state s)).
          \<exists>pd. ko_at (ArchObj (PageDirectory pd)) p s \<and>
                  (\<forall>x. aligned_pde (pd x) \<and>
                       (\<forall>r. pde_ref (pd x) = Some r
                            \<longrightarrow> r \<in> set (x64_global_pts (arch_state s))))) \<and>
      (\<forall>p\<in>set (x64_global_pts (arch_state s)).
          \<exists>pt. ko_at (ArchObj (PageTable pt)) p s \<and>
                  (\<forall>x. aligned_pte (pt x)))"

definition
  valid_asid_table :: "(3 word \<rightharpoonup> obj_ref) \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_asid_table table \<equiv> \<lambda>s. (\<forall>p \<in> ran table. asid_pool_at p s) \<and>
                                inj_on table (dom table)"

definition
  valid_global_pts :: "'z :: state_ext state \<Rightarrow> bool"
where
  "valid_global_pts \<equiv> \<lambda>s.
   \<forall>p \<in> set (x64_global_pts (arch_state s)). typ_at (AArch APageTable) p s"

definition
  valid_global_pds :: "'z :: state_ext state \<Rightarrow> bool"
where
  "valid_global_pds \<equiv> \<lambda>s.
   \<forall>p \<in> set (x64_global_pds (arch_state s)). typ_at (AArch APageDirectory) p s"

definition
  valid_global_pdpts :: "'z :: state_ext state \<Rightarrow> bool"
where
  "valid_global_pdpts \<equiv> \<lambda>s.
   \<forall>p \<in> set (x64_global_pdpts (arch_state s)). typ_at (AArch APDPointerTable) p s"

definition
  valid_cr3 :: "cr3 \<Rightarrow> bool"
where
  "valid_cr3 r \<equiv> is_aligned (cr3_base_address r) asid_bits
                   \<and> cr3_base_address r \<le> mask (pml4_shift_bits + asid_bits)
                   \<and> asid_wf (cr3_pcid r)"

(* arch_live/hyp_live stub *)

definition
  arch_live :: "arch_kernel_obj \<Rightarrow> bool"
where
  "arch_live ao \<equiv> False"

definition
  hyp_live :: "kernel_object \<Rightarrow> bool"
where
  "hyp_live ko \<equiv> False"

definition
  issued_ioports :: "arch_state \<Rightarrow> io_port set"
where
  "issued_ioports \<equiv> \<lambda>s. Collect (x64_allocated_io_ports s)"

definition
  cap_ioports :: "cap \<Rightarrow> io_port set"
where
  "cap_ioports c \<equiv> case c of ArchObjectCap (IOPortCap f l) \<Rightarrow> {f..l} | _ \<Rightarrow> {}"

definition
  all_ioports_issued :: "(cslot_ptr \<Rightarrow> cap option) \<Rightarrow> arch_state \<Rightarrow> bool"
where
  "all_ioports_issued \<equiv> \<lambda>cs as. \<forall>cap \<in> ran cs. cap_ioports cap \<subseteq> issued_ioports as"

definition
  ioports_no_overlap :: "(cslot_ptr \<Rightarrow> cap option) \<Rightarrow> bool"
where
  "ioports_no_overlap \<equiv> \<lambda>cs. \<forall>cap\<in>ran cs. \<forall>cap' \<in> ran cs.
     cap_ioports cap \<inter> cap_ioports cap' \<noteq> {} \<longrightarrow> cap_ioports cap = cap_ioports cap'"

definition
  valid_ioports :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_ioports \<equiv> \<lambda>s. all_ioports_issued (caps_of_state s) (arch_state s) \<and>
                      ioports_no_overlap (caps_of_state s)"

definition
  valid_x64_irq_state :: "(8 word \<Rightarrow> X64IRQState) \<Rightarrow> bool"
where
  "valid_x64_irq_state irqState \<equiv> \<forall>irq > maxIRQ. irqState irq = IRQFree"

definition
  valid_arch_state :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_state \<equiv> \<lambda>s.
    valid_asid_table (x64_asid_table (arch_state s)) s
      \<and> page_map_l4_at (x64_global_pml4 (arch_state s)) s
      \<and> valid_global_pts s
      \<and> valid_global_pds s
      \<and> valid_global_pdpts s
      \<and> valid_cr3 (x64_current_cr3 (arch_state s))
      \<and> valid_x64_irq_state (x64_irq_state (arch_state s))"

definition
  vs_cap_ref_arch :: "arch_cap \<Rightarrow> vs_ref list option"
where
  "vs_cap_ref_arch \<equiv> \<lambda> cap. case cap of
   ASIDPoolCap _ asid \<Rightarrow>
     Some [VSRef (ucast (asid_high_bits_of asid)) None]
 | PML4Cap _ (Some asid) \<Rightarrow>
     Some [VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PDPointerTableCap _ (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageDirectoryCap _ (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageTableCap _ (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 21) && mask 9) (Some APageDirectory),
           VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageCap dev word rights typ X64SmallPage (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 12) && mask 9) (Some APageTable),
           VSRef ((vptr >> 21) && mask 9) (Some APageDirectory),
           VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageCap dev word rights typ X64LargePage  (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 21) && mask 9) (Some APageDirectory),
           VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageCap dev word rights typ X64HugePage (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | _ \<Rightarrow> None"

declare vs_cap_ref_arch_def[simp]

definition
  "vs_cap_ref cap \<equiv> arch_cap_fun_lift vs_cap_ref_arch None cap"

definition
  "is_pg_cap cap \<equiv> \<exists>dev p R tp sz m. cap = ArchObjectCap (PageCap dev p R tp sz m)"

definition
  "is_page_cap cap \<equiv> \<exists>d p R tp sz m. cap = PageCap d p R tp sz m"

definition
  "is_pml4_cap c \<equiv> \<exists>p asid. c = ArchObjectCap (PML4Cap p asid)"

definition
  "is_pdpt_cap c \<equiv> \<exists>p asid. c = ArchObjectCap (PDPointerTableCap p asid)"

definition
  "is_pd_cap c \<equiv> \<exists>p asid. c = ArchObjectCap (PageDirectoryCap p asid)"

definition
  "is_pt_cap c \<equiv> \<exists>p asid. c = ArchObjectCap (PageTableCap p asid)"

lemmas is_vspace_table_cap_defs = is_pt_cap_def is_pd_cap_def is_pdpt_cap_def is_pml4_cap_def

abbreviation
  "is_vspace_table_cap c \<equiv> is_pt_cap c \<or> is_pd_cap c \<or> is_pdpt_cap c \<or> is_pml4_cap c"

definition
  "is_asid_pool_cap c \<equiv> \<exists>ptr asid. c = ArchObjectCap (ASIDPoolCap ptr asid)"

definition
  "is_ioport_control_cap cap \<equiv> cap = ArchObjectCap IOPortControlCap"

definition
  "is_ioport_cap cap \<equiv> \<exists>f l. cap = ArchObjectCap (IOPortCap f l)"


lemmas is_arch_cap_simps [simplified atomize_eq] =
  is_pg_cap_def is_pd_cap_def is_pt_cap_def is_pdpt_cap_def is_pml4_cap_def is_asid_pool_cap_def
  is_nondevice_page_cap is_ioport_control_cap_def is_ioport_cap_def


definition
  "cap_asid_arch cap \<equiv> case cap of
    PageCap _ _ _ _ _ (Some (asid, _)) \<Rightarrow> Some asid
  | PageTableCap _ (Some (asid, _)) \<Rightarrow> Some asid
  | PageDirectoryCap _ (Some (asid, _)) \<Rightarrow> Some asid
  | PDPointerTableCap _ (Some (asid, _)) \<Rightarrow> Some asid
  | PML4Cap _ (Some asid) \<Rightarrow> Some asid
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
  {idle_thread s, x64_global_pml4 (arch_state s)} \<union>
   range (interrupt_irq_node s) \<union> set (x64_global_pdpts (arch_state s)) \<union>
   set (x64_global_pds (arch_state s)) \<union> set (x64_global_pts (arch_state s))"

definition
  not_kernel_window_arch :: "arch_state \<Rightarrow> obj_ref set"
where
  "not_kernel_window_arch s \<equiv> {x. x64_kernel_vspace s x \<noteq> X64VSpaceKernelWindow}"

declare not_kernel_window_arch_def[simp]

abbreviation
  not_kernel_window :: "'z::state_ext state \<Rightarrow> obj_ref set"
where
  "not_kernel_window s \<equiv> not_kernel_window_arch (arch_state s)"


  (* needed for map: installing new object should add only one mapping *)
(* FIXME x64: more stuff for global pdpt, global pd? *)
definition
  "valid_table_caps \<equiv> \<lambda>s.
  \<forall>r p cap. (caps_of_state s) p = Some cap \<longrightarrow>
            (is_pd_cap cap \<or> is_pt_cap cap \<or> is_pdpt_cap cap \<or> is_pml4_cap cap) \<longrightarrow>
            cap_asid cap = None \<longrightarrow>
            r \<in> obj_refs cap \<longrightarrow>
            obj_at (empty_table (set (second_level_tables (arch_state s)))) r s"

(* needed to preserve valid_table_caps in map
     enforces no sharing of tables *)
definition
  "unique_table_caps \<equiv> \<lambda>cs. \<forall>p p' cap cap'.
  cs p = Some cap \<longrightarrow> cs p' = Some cap' \<longrightarrow>
  cap_asid cap = None \<longrightarrow>
  obj_refs cap' = obj_refs cap \<longrightarrow>
  (is_pd_cap cap \<longrightarrow> is_pd_cap cap' \<longrightarrow> p' = p) \<and>
  (is_pt_cap cap \<longrightarrow> is_pt_cap cap' \<longrightarrow> p' = p) \<and>
  (is_pdpt_cap cap \<longrightarrow> is_pdpt_cap cap' \<longrightarrow> p' = p) \<and>
  (is_pml4_cap cap \<longrightarrow> is_pml4_cap cap' \<longrightarrow> p' = p)"

definition
  table_cap_ref_arch :: "arch_cap \<Rightarrow> vs_ref list option"
where
  "table_cap_ref_arch \<equiv> \<lambda> cap. case cap of
     ASIDPoolCap _ asid \<Rightarrow>
       Some [VSRef (ucast (asid_high_bits_of asid)) None]
 | PML4Cap _ (Some asid) \<Rightarrow>
     Some [VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PDPointerTableCap _ (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageDirectoryCap _ (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | PageTableCap _ (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 21) && mask 9) (Some APageDirectory),
           VSRef ((vptr >> 30) && mask 9) (Some APDPointerTable),
           VSRef ((vptr >> 39) && mask 9) (Some APageMapL4),
           VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
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
  "valid_kernel_mappings \<equiv>
     \<lambda>s. \<forall>ko \<in> ran (kheap s).
          valid_kernel_mappings_if_pm
             (set (second_level_tables (arch_state s))) ko"

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
             x64_kernel_vspace (arch_state s) y = X64VSpaceKernelWindow)"

definition
  arch_obj_bits_type :: "aa_type \<Rightarrow> nat"
where
 "arch_obj_bits_type T' \<equiv> (case T' of
    AASIDPool \<Rightarrow> arch_kobj_size (ASIDPool undefined)
  | ADeviceData sz \<Rightarrow> arch_kobj_size (DataPage True sz)
  | AUserData sz \<Rightarrow> arch_kobj_size (DataPage False sz)
  | APageDirectory \<Rightarrow> arch_kobj_size (PageDirectory undefined)
  | APageTable \<Rightarrow> arch_kobj_size (PageTable undefined)
  | APDPointerTable \<Rightarrow> arch_kobj_size (PDPointerTable undefined)
  | APageMapL4 \<Rightarrow> arch_kobj_size (PageMapL4 undefined))"

definition
  vspace_at_asid :: "asid \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "vspace_at_asid asid pm \<equiv> \<lambda>s.
         ([VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pm) s"


definition
  valid_asid_map :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_asid_map \<equiv> \<lambda>s. True"

definition
  "ioport_revocable r cs \<equiv> \<forall>p. cs p = Some (ArchObjectCap IOPortControlCap) \<longrightarrow> r p"

definition
  "valid_arch_mdb r cs \<equiv> ioport_revocable r cs"


section "Lemmas"

lemma vmsz_aligned_X64LargePage:
  "vmsz_aligned vref X64LargePage = is_aligned vref (pageBitsForSize X64LargePage)"
  by (simp add: vmsz_aligned_def pageBitsForSize_def)

lemma valid_arch_cap_def2:
  "valid_arch_cap c s \<equiv> wellformed_acap c \<and> valid_arch_cap_ref c s"
  apply (rule eq_reflection)
  apply (cases c)
    by (auto simp add: wellformed_acap_simps valid_arch_cap_simps
                       valid_arch_cap_ref_simps
                split: option.splits)

lemmas vs_ref_aatype_simps[simp] = vs_ref_aatype_def[split_simps vs_ref.split]

lemma vs_lookup1_obj_at:
  "((rs,p) \<rhd>1 (r # rs,p')) s = obj_at (\<lambda>ko. (r, p') \<in> vs_refs ko) p s"
  by (fastforce simp: vs_lookup1_def obj_at_def)

lemma vs_lookup1I:
  "\<lbrakk> ko_at ko p s; (r, p') \<in> vs_refs ko;
          rs' = r # rs \<rbrakk> \<Longrightarrow> ((rs,p) \<rhd>1 (rs',p')) s"
  by (fastforce simp add: vs_lookup1_def)

lemma vs_lookup_pages1I:
  "\<lbrakk> ko_at ko p s; (r, p') \<in> vs_refs_pages ko;
          rs' = r # rs \<rbrakk> \<Longrightarrow> ((rs,p) \<unrhd>1 (rs',p')) s"
  by (fastforce simp add: vs_lookup_pages1_def)

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
  assumes table: "graph_of (x64_asid_table (arch_state s)) \<subseteq> graph_of (x64_asid_table (arch_state s'))"
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
    "graph_of (x64_asid_table (arch_state s)) \<subseteq>
     graph_of (x64_asid_table (arch_state s'))"
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
  "\<lbrakk> ref' \<in> vs_asid_refs (x64_asid_table (arch_state s));
     (ref',(ref,p)) \<in> (vs_lookup_pages1 s)^*  \<rbrakk> \<Longrightarrow>
  (ref \<unrhd> p) s"
  by (simp add: vs_lookup_pages_def) blast

lemma vs_lookup_stateI:
  assumes 1: "(ref \<rhd> p) s"
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  assumes table: "graph_of (x64_asid_table (arch_state s)) \<subseteq> graph_of (x64_asid_table (arch_state s'))"
  shows "(ref \<rhd> p) s'"
  using 1 vs_lookup_sub [OF ko table] by blast

lemma valid_vspace_objsD:
  "\<lbrakk> (ref \<rhd> p) s; ko_at (ArchObj ao) p s; valid_vspace_objs s \<rbrakk> \<Longrightarrow> valid_vspace_obj ao s"
  by (fastforce simp add: valid_vspace_objs_def)

lemma valid_vspace_objs_stateI:
  assumes 1: "valid_vspace_objs s"
  assumes ko: "\<And>ko p. ko_at ko p s' \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s"
  assumes arch: "graph_of (x64_asid_table (arch_state s')) \<subseteq> graph_of (x64_asid_table (arch_state s))"
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
  by (wp P hoare_vcg_ball_lift hoare_vcg_imp_lift hoare_vcg_conj_lift | clarsimp)+

lemma valid_vspace_obj_typ:
  assumes P: "\<And>p T. \<lbrace>\<lambda>s. (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s.  (typ_at (AArch T) p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_vspace_obj ob s\<rbrace> f \<lbrace>\<lambda>rv s. valid_vspace_obj ob s\<rbrace>"
  apply (cases ob, simp_all)
       apply (rule hoare_vcg_const_Ball_lift[OF P])
      apply (rule hoare_vcg_all_lift)
      apply (rename_tac "fun" x)
      apply (case_tac "fun x", simp_all add: data_at_def hoare_vcg_prop P)
     apply (wp hoare_vcg_disj_lift P)
    apply (rule hoare_vcg_all_lift)
    apply (rename_tac "fun" x)
    apply (case_tac "fun x", simp_all add: data_at_def hoare_vcg_prop P)
    apply (wp hoare_vcg_disj_lift P)
   apply (rule hoare_vcg_all_lift)
   apply (rename_tac "fun" x)
   apply (case_tac "fun x", simp_all add: data_at_def hoare_vcg_prop P)
   apply (wp hoare_vcg_disj_lift hoare_vcg_const_Ball_lift P)+
  apply (rename_tac "fun" x)
  apply (case_tac "fun x", simp_all add: hoare_vcg_prop P)
  done

lemma atyp_at_eq_kheap_obj:
  "typ_at (AArch AASIDPool) p s \<longleftrightarrow> (\<exists>f. kheap s p = Some (ArchObj (ASIDPool f)))"
  "typ_at (AArch APageTable) p s \<longleftrightarrow> (\<exists>pt. kheap s p = Some (ArchObj (PageTable pt)))"
  "typ_at (AArch APageDirectory) p s \<longleftrightarrow> (\<exists>pd. kheap s p = Some (ArchObj (PageDirectory pd)))"
  "typ_at (AArch APDPointerTable) p s \<longleftrightarrow> (\<exists>pdpt. kheap s p = Some (ArchObj (PDPointerTable pdpt)))"
  "typ_at (AArch APageMapL4) p s \<longleftrightarrow> (\<exists>pm. kheap s p = Some (ArchObj (PageMapL4 pm)))"
  "typ_at (AArch (AUserData sz)) p s \<longleftrightarrow> (kheap s p = Some (ArchObj (DataPage False sz)))"
  "typ_at (AArch (ADeviceData sz)) p s \<longleftrightarrow> (kheap s p = Some (ArchObj (DataPage True sz)))"
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
  aa_type_APageMapL4E:
  "\<lbrakk>a_type ko = AArch APageMapL4;
    (\<And>pm. ko = ArchObj (PageMapL4 pm) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R" and
  aa_type_APDPointerTableE:
  "\<lbrakk>a_type ko = AArch APDPointerTable;
    (\<And>pdpt. ko = ArchObj (PDPointerTable pdpt) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R" and
  aa_type_APageDirectoryE:
  "\<lbrakk>a_type ko = AArch APageDirectory;
    (\<And>pd. ko = ArchObj (PageDirectory pd) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R" and
   aa_type_APageTableE:
  "\<lbrakk>a_type ko = AArch APageTable; (\<And>pt. ko = ArchObj (PageTable pt) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R" and
   aa_type_AUserDataE:
  "\<lbrakk>a_type ko = AArch (AUserData sz); ko = ArchObj (DataPage False sz) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  and
   aa_type_ADeviceDataE:
  "\<lbrakk>a_type ko = AArch (ADeviceData sz); ko = ArchObj (DataPage True sz) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (rule kernel_object_exhaust[of ko]; clarsimp simp add: a_type_simps split: if_split_asm)+

lemmas aa_type_elims[elim!] =
   aa_type_AASIDPoolE aa_type_AUserDataE aa_type_ADeviceDataE
   aa_type_APageDirectoryE aa_type_APageTableE aa_type_APDPointerTableE aa_type_APageMapL4E

lemma wellformed_arch_typ:
   assumes P: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
   shows   "\<lbrace>\<lambda>s. arch_valid_obj ao s\<rbrace> f \<lbrace>\<lambda>rv s. arch_valid_obj ao s\<rbrace>"
  by (cases ao; clarsimp; wp)

lemma valid_vspace_obj_pspaceI:
  "\<lbrakk> valid_vspace_obj obj s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_vspace_obj obj s'"
  apply (cases obj, simp_all add: obj_at_def)
     apply (erule allEI ballEI,
            rename_tac "fun" x,
            case_tac "fun x",
            simp_all add: obj_at_def data_at_def)+
  done

lemmas  pageBitsForSize_simps[simp] =
        pageBitsForSize_def[split_simps vmpage_size.split]

lemma arch_kobj_size_bounded:
  "arch_kobj_size obj < word_bits"
  apply (cases obj, simp_all add: word_bits_conv pageBits_def table_size_def
                                  ptTranslationBits_def word_size_bits_def)
  apply (rename_tac vmpage_size)
  apply (case_tac vmpage_size, simp_all add: pageBits_def ptTranslationBits_def)
  done

lemma valid_arch_sizes:
  "obj_bits (ArchObj obj) < word_bits"
  using arch_kobj_size_bounded word_bits_conv by auto

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

lemma valid_global_pts_update [iff]:
  "x64_global_pts (arch_state (f s)) = x64_global_pts (arch_state s) \<Longrightarrow>
   valid_global_pts (f s) = valid_global_pts s"
  by (simp add: valid_global_pts_def)

lemma valid_global_pds_update [iff]:
  "x64_global_pds (arch_state (f s)) = x64_global_pds (arch_state s) \<Longrightarrow>
   valid_global_pds (f s) = valid_global_pds s"
  by (simp add: valid_global_pds_def)

lemma valid_global_pdpts_update [iff]:
  "x64_global_pdpts (arch_state (f s)) = x64_global_pdpts (arch_state s) \<Longrightarrow>
   valid_global_pdpts (f s) = valid_global_pdpts s"
  by (simp add: valid_global_pdpts_def)

lemma valid_pte_update [iff]:
  "valid_pte pte (f s) = valid_pte pte s"
  by (cases pte) (auto simp: data_at_def)

lemma valid_pde_update [iff]:
  "valid_pde pde (f s) = valid_pde pde s"
  by (cases pde) (auto simp: data_at_def)

lemma valid_pdpte_update [iff]:
  "valid_pdpte pdpte (f s) = valid_pdpte pdpte s"
  by (cases pdpte) (auto simp: data_at_def)

lemma valid_pml4e_update [iff]:
  "valid_pml4e pml4e (f s) = valid_pml4e pml4e s"
  by (cases pml4e) auto

lemma valid_vspace_obj_update [iff]:
  "valid_vspace_obj ao (f s) = valid_vspace_obj ao s"
  by (cases ao) auto

lemma valid_vso_at_update [iff]:
  "valid_vso_at p (f s) = valid_vso_at p s"
  by (simp add: valid_vso_at_def)

lemma valid_ao_at_update [iff]:
  "valid_ao_at p (f s) = valid_ao_at p s"
  by (simp add: valid_ao_at_def)

lemma equal_kernel_mappings_update [iff]:
  "equal_kernel_mappings (f s) = equal_kernel_mappings s"
  by (simp add: equal_kernel_mappings_def)

lemma valid_pt_kernel_mappings [iff]:
  "valid_pde_kernel_mappings pde vref uses (f s)
      = valid_pde_kernel_mappings pde vref uses s"
  by (cases pde, simp_all add: valid_pde_kernel_mappings_def)

lemma valid_pd_kernel_mappings [iff]:
  "valid_pd_kernel_mappings uses vref (f s)
      = valid_pd_kernel_mappings uses vref s"
  by (rule ext, simp add: valid_pd_kernel_mappings_def)

lemma valid_pdpte_kernel_mappings [iff]:
  "valid_pdpte_kernel_mappings pde vref uses (f s)
      = valid_pdpte_kernel_mappings pde vref uses s"
  by (cases pde, simp_all add: valid_pdpte_kernel_mappings_def)

lemma valid_pdpt_kernel_mappings [iff]:
  "valid_pdpt_kernel_mappings uses vref (f s)
      = valid_pdpt_kernel_mappings uses vref s"
  by (rule ext, simp add: valid_pdpt_kernel_mappings_def)

lemma valid_pml4e_kernel_mappings [iff]:
  "valid_pml4e_kernel_mappings pde vref uses (f s)
      = valid_pml4e_kernel_mappings pde vref uses s"
  by (cases pde, simp_all add: valid_pml4e_kernel_mappings_def)

lemma valid_pml4_kernel_mappings [iff]:
  "valid_pml4_kernel_mappings uses (f s)
      = valid_pml4_kernel_mappings uses s"
  by (rule ext, simp add: valid_pml4_kernel_mappings_def)

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
  by clarsimp

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

lemma valid_ioports_update[iff]:
  "valid_ioports (f s) = valid_ioports s"
  by (clarsimp simp: valid_ioports_def arch)

end

context Arch begin arch_global_naming

lemma global_refs_equiv:
  assumes "idle_thread s = idle_thread s'"
  assumes "interrupt_irq_node s = interrupt_irq_node s'"
  assumes "x64_global_pml4 (arch_state s) = x64_global_pml4 (arch_state s')"
  assumes "set (x64_global_pts (arch_state s)) = set (x64_global_pts (arch_state s'))"
  assumes "set (x64_global_pds (arch_state s)) = set (x64_global_pds (arch_state s'))"
  assumes "set (x64_global_pdpts (arch_state s)) = set (x64_global_pdpts (arch_state s'))"
  assumes "ran (x64_asid_table (arch_state s)) = ran (x64_asid_table (arch_state s'))"
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
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>valid_arch_state\<rbrace> f \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (simp add: valid_arch_state_def valid_asid_table_def
                   valid_global_pts_def valid_global_pds_def valid_global_pdpts_def)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. arch_state s"])
   apply (wp arch typs hoare_vcg_conj_lift hoare_vcg_const_Ball_lift)+
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

lemma valid_pml4e_lift:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_pml4e pml4e s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pml4e pml4e s\<rbrace>"
  by (cases pml4e) (simp | wp x)+

lemma valid_pdpte_lift:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_pdpte pdpte s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pdpte pdpte s\<rbrace>"
  by (cases pdpte) (simp add: data_at_def | wp hoare_vcg_disj_lift x)+

lemma valid_pde_lift:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_pde pde s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pde pde s\<rbrace>"
  by (cases pde) (simp add: data_at_def | wp hoare_vcg_disj_lift x)+

lemma valid_pte_lift:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_pte pte s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pte pte s\<rbrace>"
  by (cases pte) (simp add: data_at_def | wp hoare_vcg_disj_lift x)+

lemma pdpte_at_atyp:
  assumes x: "\<And>p T. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows      "\<lbrace>pdpte_at p\<rbrace> f \<lbrace>\<lambda>rv. pdpte_at p\<rbrace>"
  by (simp add: pdpte_at_def | wp x)+

lemma pml4e_at_atyp:
  assumes x: "\<And>p T. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows      "\<lbrace>pml4e_at p\<rbrace> f \<lbrace>\<lambda>rv. pml4e_at p\<rbrace>"
  by (simp add: pml4e_at_def | wp x)+

lemma pde_at_atyp:
  assumes x: "\<And>p T. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows      "\<lbrace>pde_at p\<rbrace> f \<lbrace>\<lambda>rv. pde_at p\<rbrace>"
  by (simp add: pde_at_def | wp x)+

lemma pte_at_atyp:
  assumes x: "\<And>p T. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows      "\<lbrace>pte_at p\<rbrace> f \<lbrace>\<lambda>rv. pte_at p\<rbrace>"
  by (simp add: pte_at_def | wp x)+

lemmas valid_table_entry_lifts =
  valid_pde_lift valid_pte_lift valid_pdpte_lift valid_pml4e_lift

lemmas abs_atyp_at_lifts =
  valid_table_entry_lifts pde_at_atyp pte_at_atyp pdpte_at_atyp pml4e_at_atyp

lemma table_size:
  "table_size = 12"
  by (simp add: table_size_def ptTranslationBits_def word_size_bits_def)

bundle bitsimps =
  table_size_def[simp] word_size_bits_def[simp]
  ptTranslationBits_def[simp] pageBits_def[simp]

context includes bitsimps begin
  lemmas simple_bit_simps       = table_size word_size_bits_def ptTranslationBits_def pageBits_def
  lemmas table_bits_simps       = pml4_bits_def[simplified] pdpt_bits_def[simplified]
                                  pd_bits_def[simplified] pt_bits_def[simplified]
  lemmas table_shift_bits_simps = pml4_shift_bits_def[simplified] pdpt_shift_bits_def[simplified]
                                  pd_shift_bits_def[simplified] pt_shift_bits_def[simplified]

  lemmas bit_simps              = table_bits_simps table_shift_bits_simps simple_bit_simps
end

lemma page_directory_pde_atI:
  "\<lbrakk> page_directory_at p s; x < 2 ^ ptTranslationBits;
         pspace_aligned s \<rbrakk> \<Longrightarrow> pde_at (p + (x << word_size_bits)) s"
  apply (clarsimp simp: obj_at_def pde_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def bit_simps
                 split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self word_bits_conv)
  apply (subgoal_tac "p = (p + (x << word_size_bits) && ~~ mask pd_bits)")
   subgoal by (auto simp: bit_simps)
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: pd_bits_def pageBits_def table_size)
  apply (simp del: bit_shiftl_iff bit_shiftl_word_iff)
  apply (subst upper_bits_unset_is_l2p_64[unfolded word_bits_conv])
   apply (simp add: pd_bits_def pageBits_def table_size)
  apply (rule shiftl_less_t2n)
   apply (simp add: bit_simps)+
  done

lemma page_table_pte_atI:
  "\<lbrakk> page_table_at p s; x < 2^ptTranslationBits; pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at (p + (x << word_size_bits)) s"
  apply (clarsimp simp: obj_at_def pte_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def bit_simps
                 split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self word_bits_conv)
  apply (subgoal_tac "p = (p + (x << word_size_bits) && ~~ mask pt_bits)")
   subgoal by (auto simp: bit_simps)
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: bit_simps)
  apply (simp del: bit_shiftl_iff bit_shiftl_word_iff)
  apply (subst upper_bits_unset_is_l2p_64[unfolded word_bits_conv])
   apply (simp add: bit_simps)
  apply (rule shiftl_less_t2n)
   apply (simp add: bit_simps)+
  done

lemma pd_pointer_table_pdpte_atI:
  "\<lbrakk> pd_pointer_table_at p s; x < 2^ptTranslationBits; pspace_aligned s \<rbrakk> \<Longrightarrow> pdpte_at (p + (x << word_size_bits)) s"
  apply (clarsimp simp: obj_at_def pdpte_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def bit_simps
                 split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self word_bits_conv)
  apply (subgoal_tac "p = (p + (x << word_size_bits) && ~~ mask pdpt_bits)")
   subgoal by (auto simp: bit_simps)
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: bit_simps)
  apply (simp del: bit_shiftl_iff bit_shiftl_word_iff)
  apply (subst upper_bits_unset_is_l2p_64[unfolded word_bits_conv])
   apply (simp add: bit_simps)
  apply (rule shiftl_less_t2n)
   apply (simp add: bit_simps)+
  done

lemma page_map_l4_pml4e_atI:
  "\<lbrakk> page_map_l4_at p s; x < 2^ptTranslationBits; pspace_aligned s \<rbrakk> \<Longrightarrow> pml4e_at (p + (x << word_size_bits)) s"
  apply (clarsimp simp: obj_at_def pml4e_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def bit_simps
                 split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self word_bits_conv)
  apply (subgoal_tac "p = (p + (x << word_size_bits) && ~~ mask pml4_bits)")
   subgoal by (auto simp: bit_simps)
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: bit_simps)
  apply (simp del: bit_shiftl_iff bit_shiftl_word_iff)
  apply (subst upper_bits_unset_is_l2p_64[unfolded word_bits_conv])
   apply (simp add: bit_simps)
  apply (rule shiftl_less_t2n)
   apply (simp add: bit_simps)+
  done

lemma physical_arch_cap_has_ref:
  "(acap_class arch_cap = PhysicalClass) = (\<exists>y. aobj_ref arch_cap = Some y)"
  by (cases arch_cap; simp)


subsection "vs_lookup"

lemma vs_lookup1_ko_at_dest:
  "\<lbrakk> ((ref, p) \<rhd>1 (ref', p')) s; ko_at (ArchObj ao) p s; valid_vspace_obj ao s \<rbrakk> \<Longrightarrow>
  \<exists>ao'. ko_at (ArchObj ao') p' s \<and> (\<exists>tp. vs_ref_aatype (hd ref') = Some tp
                                            \<and> aa_type ao = tp)"
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def)
  apply (cases ao, simp_all add: graph_of_def)
     apply clarsimp
     apply (drule bspec, fastforce simp: ran_def)
     apply (clarsimp simp: aa_type_def obj_at_def)
    apply (clarsimp split: arch_kernel_obj.split_asm if_split_asm)
    apply (simp add: pde_ref_def aa_type_def
              split: pde.splits)
    apply (drule_tac x=a in spec)
    apply (clarsimp simp: valid_pde_def obj_at_def aa_type_def)
   apply (clarsimp split: arch_kernel_obj.split_asm if_split_asm)
   apply (simp add: pdpte_ref_def aa_type_def
             split: pdpte.splits)
   apply (drule_tac x=a in spec)
   apply (clarsimp simp: valid_pdpte_def obj_at_def aa_type_def)
  apply (clarsimp split: arch_kernel_obj.split_asm if_split_asm)
  apply (simp add: pml4e_ref_def aa_type_def
            split: pml4e.splits)
  apply (erule_tac x=a in ballE)
   apply (clarsimp simp: obj_at_def)
  apply simp
  done

lemma vs_refs_vs_refs_pages:
  "r \<in> vs_refs obj \<Longrightarrow> r \<in> vs_refs_pages obj"
  apply (cases obj; simp add: vs_refs_def)
  apply (rename_tac aobj)
  apply (case_tac aobj;
         clarsimp simp: vs_refs_def vs_refs_pages_def graph_of_def image_def
                        pde_ref_def pde_ref_pages_def
                        pdpte_ref_def pdpte_ref_pages_def
                        pml4e_ref_def pml4e_ref_pages_def
                 split: pde.splits pdpte.splits pml4e.splits if_splits)
    apply blast
   apply blast
  apply (frule pml4e.discI; fastforce)
  done

lemma vs_lookup1_vs_lookup_pages1:
  "arc \<in> vs_lookup1 s \<Longrightarrow> arc \<in> vs_lookup_pages1 s"
  apply (clarsimp simp: vs_lookup1_def vs_lookup_pages1_def)
  apply (drule vs_refs_vs_refs_pages)
  by blast

lemma vs_refs_pages_aobj_not_empty:
  "ref \<in> vs_refs_pages ko \<Longrightarrow> \<exists>aobj. ko = ArchObj aobj"
  by (clarsimp simp: vs_refs_pages_def split: kernel_object.splits)

lemmas vs_refs_aobj_not_empty = vs_refs_pages_aobj_not_empty[OF vs_refs_vs_refs_pages]

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
  "x64_asid_table (arch_state s) a = Some p \<Longrightarrow> ([VSRef (ucast a) None] \<rhd> p) s"
  unfolding vs_lookup_def by (drule vs_asid_refsI) fastforce

lemma vs_lookup_apI:
  "\<And>a p\<^sub>1 ap b.
     \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
      kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
      ap b = Some p\<rbrakk>
     \<Longrightarrow> ([VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<rhd> p) s"
  apply (simp add: vs_lookup_def Image_def vs_asid_refs_def graph_of_def)
  apply (intro exI conjI, assumption)
  apply (rule rtrancl_into_rtrancl)
   apply (rule rtrancl_refl)
  apply (fastforce simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def image_def)
  done

lemma vs_lookup_pml4I:
  "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c.
     \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
      kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
      ap b = Some p\<^sub>2;
      kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
      c \<notin> kernel_mapping_slots;
      pm c = pml4e.PDPointerTablePML4E p f w\<rbrakk>
     \<Longrightarrow> ([VSRef (ucast c) (Some APageMapL4),
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
  apply (simp add: pml4e_ref_def ptrFormPAddr_addFromPPtr)
  done

lemma vs_lookup_pdptI:
  "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c pdpt d addr x y.
     \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
      kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
      ap b = Some p\<^sub>2;
      kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
      c \<notin> kernel_mapping_slots;
      pm c = PDPointerTablePML4E addr x y;
      kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
      pdpt d = pdpte.PageDirectoryPDPTE p f w\<rbrakk>
     \<Longrightarrow> ([VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
           VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None]
          \<rhd> ptrFromPAddr p) s"
  apply (frule (5) vs_lookup_pml4I)
  apply (erule vs_lookup_step)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def image_def
                 split: if_split_asm)
  apply (rule_tac x=d in exI)
  by (clarsimp simp: pdpte_ref_def ptrFormPAddr_addFromPPtr)

lemma vs_lookup_pdI:
  "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c pdpt d addr x y e p f w pd.
     \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
      kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
      ap b = Some p\<^sub>2;
      kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
      c \<notin> kernel_mapping_slots;
      pm c = PDPointerTablePML4E addr x y;
      kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
      pdpt d = pdpte.PageDirectoryPDPTE p f w;
      kheap s (ptrFromPAddr p) = Some (ArchObj (PageDirectory pd));
      pd e = pde.PageTablePDE p' f' w'\<rbrakk>
     \<Longrightarrow> ([VSRef (ucast e) (Some APageDirectory),
           VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
           VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None]
          \<rhd> ptrFromPAddr p') s"
  apply (frule (7) vs_lookup_pdptI)
  apply (erule vs_lookup_step)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def image_def
                 split: if_split_asm)
  apply (rule_tac x=e in exI)
  by (clarsimp simp: pde_ref_def ptrFormPAddr_addFromPPtr)

lemma vs_lookup_pages_vs_lookupI: "(ref \<rhd> p) s \<Longrightarrow> (ref \<unrhd> p) s"
  apply (clarsimp simp: vs_lookup_pages_def vs_lookup_def Image_def
                 elim!: bexEI)
  apply (erule rtrancl.induct, simp_all)
  apply (drule vs_lookup1_vs_lookup_pages1)
  apply (erule (1) rtrancl_into_rtrancl)
  done

lemmas
  vs_lookup_pages_atI = vs_lookup_atI[THEN vs_lookup_pages_vs_lookupI] and
  vs_lookup_pages_apI = vs_lookup_apI[THEN vs_lookup_pages_vs_lookupI]

lemma vs_lookup_pages_pml4I:
  "\<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
    kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
    ap b = Some p\<^sub>2;
    kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
    c \<notin> kernel_mapping_slots; pml4e_ref_pages (pm c) = Some p\<rbrakk>
   \<Longrightarrow> ([VSRef (ucast c) (Some APageMapL4),
         VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<unrhd> p) s"
  apply (frule (2) vs_lookup_pages_apI)
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def
                      vs_refs_pages_def graph_of_def image_def
               split: if_split_asm)

lemma vs_lookup_pages_pdptI:
  "\<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
    kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
    ap b = Some p\<^sub>2;
    kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
    c \<notin> kernel_mapping_slots; pm c = PDPointerTablePML4E addr x y;
    kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
    pdpte_ref_pages (pdpt d) = Some p\<rbrakk>
   \<Longrightarrow> ([VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
         VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<unrhd> p) s"
  apply (frule (5) vs_lookup_pml4I[THEN vs_lookup_pages_vs_lookupI])
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def
                      vs_refs_pages_def graph_of_def image_def
               split: if_split_asm)

lemma vs_lookup_pages_pdI:
  "\<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
    kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
    ap b = Some p\<^sub>2;
    kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
    c \<notin> kernel_mapping_slots; pm c = PDPointerTablePML4E addr x y;
    kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
    pdpt d = PageDirectoryPDPTE addr' x' y';
    kheap s (ptrFromPAddr addr') = Some (ArchObj (PageDirectory pd));
    pde_ref_pages (pd e) = Some p\<rbrakk>
   \<Longrightarrow> ([VSRef (ucast e) (Some APageDirectory),
         VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
         VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<unrhd> p) s"
  apply (frule (7) vs_lookup_pdptI[THEN vs_lookup_pages_vs_lookupI])
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def
                      vs_refs_pages_def graph_of_def image_def
               split: if_split_asm)

lemma vs_lookup_pages_ptI:
  "\<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
    kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
    ap b = Some p\<^sub>2;
    kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
    c \<notin> kernel_mapping_slots; pm c = PDPointerTablePML4E addr x y;
    kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
    pdpt d = PageDirectoryPDPTE addr' x' y';
    kheap s (ptrFromPAddr addr') = Some (ArchObj (PageDirectory pd));
    pd e = PageTablePDE addr'' x'' y'';
    kheap s (ptrFromPAddr addr'') = Some (ArchObj (PageTable pt));
    pte_ref_pages (pt f) = Some p\<rbrakk>
   \<Longrightarrow> ([VSRef (ucast f) (Some APageTable), VSRef (ucast e) (Some APageDirectory),
         VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
         VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<unrhd> p) s"
  apply (frule (9) vs_lookup_pdI[THEN vs_lookup_pages_vs_lookupI])
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
   apply (fastforce)
  apply clarsimp
  apply (frule (2) vs_lookup1_ko_at_dest)
  apply (drule (1) vs_lookup_trancl_step)
  apply (drule (1) vs_lookup_step)
  apply clarsimp
  apply (drule (2) valid_vspace_objsD)
   apply (fastforce)
  done

lemma stronger_vspace_objsD:
  "\<lbrakk> (ref \<rhd> p) s;
     valid_vspace_objs s;
     valid_asid_table (x64_asid_table (arch_state s)) s \<rbrakk> \<Longrightarrow>
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

lemma all_valid_pml4e_pdpt_at:
  "\<lbrakk> \<forall>i. valid_pml4e (pm i) s; pm i = PDPointerTablePML4E pdpt_ref attr rights \<rbrakk>
    \<Longrightarrow> typ_at (AArch APDPointerTable) (ptrFromPAddr pdpt_ref) s"
  by (drule spec[where x=i]; simp)

lemma all_valid_pdpte_pd_at:
  "\<lbrakk> \<forall>i. valid_pdpte (pdpt i) s; pdpt i = PageDirectoryPDPTE pd_ref attr rights \<rbrakk>
    \<Longrightarrow> typ_at (AArch APageDirectory) (ptrFromPAddr pd_ref) s"
  by (drule spec[where x=i]; simp)

lemma all_valid_pde_pt_at:
  "\<lbrakk> \<forall>i. valid_pde (pd i) s; pd i = PageTablePDE pt_ref attr rights \<rbrakk>
    \<Longrightarrow> typ_at (AArch APageTable) (ptrFromPAddr pt_ref) s"
  by (drule spec[where x=i]; simp)

(* An alternative definition for valid_vspace_objs.

   The predicates valid_asid_table and valid_vspace_objs are very compact
   but sometimes hard to use.
   The lemma below basically unrolls vs_lookup.
   Though less elegant, this formulation better separates the relevant cases. *)
lemma valid_vspace_objs_alt:
  "(\<forall>p\<in>ran (x64_asid_table (arch_state s)). asid_pool_at p s) \<and>
   valid_vspace_objs s \<longleftrightarrow>
   (\<forall>a p. x64_asid_table (arch_state s) a = Some p \<longrightarrow>
          typ_at (AArch AASIDPool) p s) \<and>
   (\<forall>a p\<^sub>1 ap b p.
          x64_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (ASIDPool ap)) \<longrightarrow>
          ap b = Some p \<longrightarrow> page_map_l4_at p s) \<and>
   (\<forall>a p\<^sub>1 ap b p\<^sub>2 pm c.
          x64_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (ASIDPool ap)) \<longrightarrow>
          ap b = Some p\<^sub>2 \<longrightarrow>
          kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm)) \<longrightarrow>
          c \<notin> kernel_mapping_slots \<longrightarrow> valid_pml4e (pm c) s) \<and>
   (\<forall>a p\<^sub>1 ap b p\<^sub>2 pm c addr f w pdpt.
          x64_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (ASIDPool ap)) \<longrightarrow>
          ap b = Some p\<^sub>2 \<longrightarrow>
          kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm)) \<longrightarrow>
          c \<notin> kernel_mapping_slots \<longrightarrow>
          pm c = PDPointerTablePML4E addr f w \<longrightarrow>
          kheap s (ptrFromPAddr addr) =
            Some (ArchObj (PDPointerTable pdpt)) \<longrightarrow>
          (\<forall>d. valid_pdpte (pdpt d) s)) \<and>
    (\<forall>a p\<^sub>1 ap b p\<^sub>2 pm c addr f w pdpt d addr' f' w' pd.
          x64_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (ASIDPool ap)) \<longrightarrow>
          ap b = Some p\<^sub>2 \<longrightarrow>
          kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm)) \<longrightarrow>
          c \<notin> kernel_mapping_slots \<longrightarrow>
          pm c = PDPointerTablePML4E addr f w \<longrightarrow>
          kheap s (ptrFromPAddr addr) =
            Some (ArchObj (PDPointerTable pdpt)) \<longrightarrow>
          pdpt d = PageDirectoryPDPTE addr' f' w' \<longrightarrow>
          kheap s (ptrFromPAddr addr') =
            Some (ArchObj (PageDirectory pd)) \<longrightarrow>
          (\<forall>e. valid_pde (pd e) s)) \<and>
     (\<forall>a p\<^sub>1 ap b p\<^sub>2 pm c addr f w pdpt d addr' f' w' pd e addr'' f'' w'' pt.
          x64_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (ASIDPool ap)) \<longrightarrow>
          ap b = Some p\<^sub>2 \<longrightarrow>
          kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm)) \<longrightarrow>
          c \<notin> kernel_mapping_slots \<longrightarrow>
          pm c = PDPointerTablePML4E addr f w \<longrightarrow>
          kheap s (ptrFromPAddr addr) =
            Some (ArchObj (PDPointerTable pdpt)) \<longrightarrow>
          pdpt d = PageDirectoryPDPTE addr' f' w' \<longrightarrow>
          kheap s (ptrFromPAddr addr') =
            Some (ArchObj (PageDirectory pd)) \<longrightarrow>
          pd e = PageTablePDE addr'' f'' w'' \<longrightarrow>
          kheap s (ptrFromPAddr addr'') =
            Some (ArchObj (PageTable pt)) \<longrightarrow>
          (\<forall>f. valid_pte (pt f) s))"
  apply (intro iffI conjI)
         apply fastforce
        apply (clarsimp simp: obj_at_def)
        apply (thin_tac "Ball S P" for S P)
        apply (frule vs_lookup_atI)
        apply (drule valid_vspace_objsD)
          apply (simp add: obj_at_def)
         apply assumption
        apply (simp add: obj_at_def ranI)
       apply (clarsimp simp: obj_at_def)
       apply (thin_tac "Ball S P" for S P)
       apply (frule (2) vs_lookup_apI)
       apply (drule valid_vspace_objsD)
         apply (simp add: obj_at_def)
        apply assumption
       apply fastforce
      apply (clarsimp simp: obj_at_def)
      apply (thin_tac "Ball S P" for S P)
      apply (frule (5) vs_lookup_pml4I)
      apply (drule valid_vspace_objsD)
        apply (simp add: obj_at_def)
       apply assumption
      apply fastforce
     apply (clarsimp simp: obj_at_def)
     apply (thin_tac "Ball S P" for S P)
     apply (frule (7) vs_lookup_pdptI)
     apply (drule valid_vspace_objsD)
       apply (simp add: obj_at_def)
      apply assumption
     apply fastforce
    apply (clarsimp simp: obj_at_def)
    apply (thin_tac "Ball S P" for S P)
    apply (frule (9) vs_lookup_pdI)
    apply (drule valid_vspace_objsD)
      apply (simp add: obj_at_def)
     apply assumption
    apply fastforce
   apply (clarsimp simp: ran_def)
  apply (clarsimp simp: valid_vspace_objs_def vs_lookup_def vs_asid_refs_def graph_of_def)
  apply (drule spec, drule spec, erule impE, assumption)+
  apply (clarsimp simp: obj_at_def)
  apply (erule converse_rtranclE)
   apply (clarsimp simp: obj_at_def ran_def)
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def graph_of_def)
  apply (drule spec, drule spec, erule impE, assumption)+
  apply (erule converse_rtranclE)
   apply (clarsimp simp: obj_at_def ran_def)
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def graph_of_def split: if_split_asm)
  apply (drule spec, erule impE, assumption)+
  apply (clarsimp simp: pml4e_ref_def split: pml4e.splits)
  apply (erule converse_rtranclE)
   apply (clarsimp simp: obj_at_def ran_def)
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def graph_of_def pdpte_ref_def split: pdpte.splits)
  apply (drule spec, drule spec, erule impE, rule exI, rule exI, assumption)+
  apply (drule (1) all_valid_pdpte_pd_at)
  apply (erule converse_rtranclE)
   apply (clarsimp simp: obj_at_def ran_def)
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def graph_of_def pde_ref_def split: pde.splits)
  apply (drule spec, drule spec, erule impE, rule exI, rule exI, assumption)
  apply (drule (1) all_valid_pde_pt_at)
  apply (erule converse_rtranclE)
   apply (clarsimp simp: obj_at_def ran_def)
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def)
  done

context begin

private lemma simulate_vs_lookup_pages1_vs_lookup1:
  assumes r: "((rs, p), t) \<in> (vs_lookup_pages1 s)\<^sup>*"
  assumes k: "ko_at ko p s"
  assumes t: "\<And>r p'. (r, p') \<in> vs_refs_pages ko \<Longrightarrow> ((r # rs, p'), t) \<in> (vs_lookup_pages1 s)\<^sup>*
                     \<Longrightarrow> (r, p') \<in> vs_refs ko \<and> ((r # rs, p'), t) \<in> (vs_lookup1 s)\<^sup>*"
  shows "((rs, p), t) \<in> (vs_lookup1 s)\<^sup>*"
  apply (rule rtrancl_simulate_weak[OF r])
  using k t by (clarsimp simp: vs_lookup_pages1_def vs_lookup1_def obj_at_def)

private lemma exI_conj1: "P x \<and> Q \<Longrightarrow> (\<exists>x. P x) \<and> Q" by auto
private lemmas exIs = exI exI_conj1

context
  fixes s :: "'a::state_ext state"
  assumes valid_objs: "valid_vspace_objs s"
  assumes asid_table: "\<forall>p\<in>ran (x64_asid_table (arch_state s)). asid_pool_at p s"
begin

(* Yet another way of breaking down valid_vspace_objs. This one makes it easier
   than valid_vspace_objs_alt to maintain a clean context, since it exposes only
   a single quantifier at a time. *)
lemma valid_vspace_objs_alt2:
  "\<forall> i p\<^sub>0. x64_asid_table (arch_state s) i = Some p\<^sub>0 \<longrightarrow>
           (\<exists> ap. ako_at (ASIDPool ap) p\<^sub>0 s
                  \<and> (\<forall> j p\<^sub>1. ap j = Some p\<^sub>1 \<longrightarrow>
                             (\<exists> pm. ako_at (PageMapL4 pm) p\<^sub>1 s
                                    \<and> (\<forall> k. k \<notin> kernel_mapping_slots \<longrightarrow> valid_pml4e_rec (pm k) s))))"
  using iffD1[OF valid_vspace_objs_alt, OF conjI[OF asid_table valid_objs]]
  apply (clarsimp simp: valid_pml4e_def valid_pdpte_def valid_pde_def valid_pte_def)
  apply (drule_tac x=i in spec; clarsimp simp: obj_at_def)+
  apply (drule_tac x=j in spec; clarsimp simp: obj_at_def pml4e_ref_def split: pml4e.splits)+
  apply (case_tac "pm k"; (drule_tac x=k in spec; clarsimp simp: obj_at_def pdpte_ref_def split: pdpte.splits)+)
  apply (rename_tac l; case_tac "pdpt l"; (drule_tac x=l in spec; clarsimp simp: obj_at_def pde_ref_def split: pde.splits)+)
  apply (rename_tac m; case_tac "pd m"; (drule_tac x=m in spec; clarsimp simp: obj_at_def)+)
  apply (rename_tac n; case_tac "pt n"; drule_tac x=n in spec; clarsimp)
  done

context
  fixes p :: machine_word
  assumes table_objs: "asid_pool_at p s \<or> vspace_table_at p s"
begin

private lemma not_data:
  "((r', p'), r, p) \<in> (vs_lookup_pages1 s)\<^sup>* \<Longrightarrow> data_at sz p' s \<Longrightarrow> P"
  apply (erule converse_rtranclE)
  using table_objs by (auto simp: data_at_def obj_at_def vs_lookup_pages1_def vs_refs_pages_def)

private method not_data =
  (match premises in H: "((VSRef (ucast i) _ # _, _), _) \<in> _\<^sup>*" and J: "\<forall> i. R i" for i R \<Rightarrow>
    \<open>insert spec[of _ i, OF J]\<close>; clarsimp; erule (1) not_data; fail)

private method step =
  (match premises in H[thin]: "((VSRef (ucast i) _ # _, _), _) \<in> _\<^sup>*" and J[thin]: "\<forall> i. R i" for i R \<Rightarrow>
    \<open>match premises in K[thin]: _ (multi) \<Rightarrow>
      \<open>insert spec[of _ i, OF J]; rule exIs[where x=i]; clarsimp simp: K;
       match premises in L[thin]: "ko_at _ _ _" \<Rightarrow> \<open>rule simulate_vs_lookup_pages1_vs_lookup1[OF H L]\<close>\<close>\<close>;
       clarsimp simp: vs_refs_pages_def;
       clarsimp simp: vs_refs_def graph_of_def image_def
                      pml4e_ref_pages_def pml4e_ref_def pdpte_ref_pages_def pdpte_ref_def
                      pde_ref_pages_def pde_ref_def pte_ref_pages_def
               split: pml4e.splits pdpte.splits pde.splits pte.splits if_splits; not_data?)

lemma vs_lookup_vs_lookup_pagesI'': "(r \<unrhd> p) s \<Longrightarrow> (r \<rhd> p) s"
  using valid_vspace_objs_alt2
  by (clarsimp simp: vs_lookup_pages_def vs_lookup_def vs_asid_refs_def graph_of_def Image_def) step+

end
end
end

lemma vs_lookup_vs_lookup_pagesI':
  assumes "(r \<unrhd> p) s"
          "asid_pool_at p s \<or> vspace_table_at p s"
          "valid_vspace_objs s"
          "valid_asid_table (x64_asid_table (arch_state s)) s"
  shows "(r \<rhd> p) s"
  using assms by (simp add: valid_asid_table_def vs_lookup_vs_lookup_pagesI'')

lemma valid_vspace_objsD':
  assumes lkp: "(ref \<unrhd> p) s"
  assumes koa: "ko_at (ArchObj ako) p s"
  assumes vao: "valid_vspace_objs s"
  assumes vat: "valid_asid_table (x64_asid_table (arch_state s)) s"
  shows "valid_vspace_obj ako s"
  proof -
    note lku = vs_lookup_vs_lookup_pagesI'[OF lkp _ vao vat]
    note vao = valid_vspace_objsD[OF lku koa vao]
    show ?thesis using koa
      by - (cases ako; (rule vao; clarsimp simp: obj_at_def a_type_def; fail)?; clarsimp)
  qed

lemma vs_lookup_def2:
  "(ref \<rhd> p) s = ((ref, p) \<in> (vs_lookup1 s)\<^sup>* `` vs_asid_refs (x64_asid_table (arch_state s)))"
  by (simp add: vs_lookup_def)

lemma vs_lookup_pages_def2:
  "(ref \<unrhd> p) s = ((ref, p) \<in> (vs_lookup_pages1 s)\<^sup>* `` vs_asid_refs (x64_asid_table (arch_state s)))"
  by (simp add: vs_lookup_pages_def)


lemma vs_lookupE:
  "\<lbrakk> (ref \<rhd> p) s;
    \<And>ref' p'. \<lbrakk> (ref',p') \<in> vs_asid_refs (x64_asid_table (arch_state s));
                ((ref',p') \<rhd>* (ref,p)) s \<rbrakk> \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
  by (auto simp: vs_lookup_def)

(* Non-recursive elim rules for vs_lookup and vs_lookup_pages
   NOTE: effectively rely on valid_objs and valid_asid_table *)
lemma vs_lookupE_alt:
  assumes vl: "(ref \<rhd> p) s"
  assumes va: "valid_vspace_objs s"
  assumes vt: "(\<forall>p\<in>ran (x64_asid_table (arch_state s)). asid_pool_at p s)"
  assumes 0: "\<And>a. x64_asid_table (arch_state s) a = Some p \<Longrightarrow>
                   typ_at (AArch AASIDPool) p s \<Longrightarrow>
                   R [VSRef (ucast a) None] p"
  assumes 1: "\<And>a p\<^sub>1 ap b.
       \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p; page_map_l4_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 2: "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c.
       \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2;
        kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
        c \<notin> kernel_mapping_slots; pml4e_ref (pm c) = Some p; pd_pointer_table_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast c) (Some APageMapL4),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 3: "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c addr x y pdpt d.
       \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2; kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
        pm c = PDPointerTablePML4E addr x y;
        kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
        c \<notin> kernel_mapping_slots; pdpte_ref (pdpt d) = Some p; page_directory_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 4: "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c addr x y pdpt d addr' x' y' pd e.
       \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2; kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
        pm c = PDPointerTablePML4E addr x y;
        kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
        pdpt d = PageDirectoryPDPTE addr' x' y';
        kheap s (ptrFromPAddr addr') = Some (ArchObj (PageDirectory pd));
        c \<notin> kernel_mapping_slots; pde_ref (pd e) = Some p; page_table_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast e) (Some APageDirectory),
              VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  shows "R ref p"
proof -
  note vao = valid_vspace_objs_alt[THEN iffD1, OF conjI[OF vt va]]
  note vat = vao[THEN conjunct1, rule_format]
  note vap = vao[THEN conjunct2, THEN conjunct1, rule_format]
  note vpm = vao[THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  note vpdpt = vao[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  note vpd = vao[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2,
                 THEN conjunct1, rule_format]
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
    apply (frule (4) vpm)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (5) 2)
     apply (simp add: valid_pml4e_def pml4e_ref_def split: pml4e.splits)+
    apply (clarsimp simp: vs_refs_def graph_of_def obj_at_def
                   dest!: vs_lookup1D
                   split: if_split_asm)
    apply (frule_tac d=ac in vpdpt, assumption+)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (7) 3)
     apply (simp add: valid_pdpte_def pdpte_ref_def split: pdpte.splits)+
    apply (clarsimp simp: vs_refs_def graph_of_def obj_at_def
                   dest!: vs_lookup1D
                   split: if_split_asm)
    apply (frule_tac e=ad in vpd, assumption+)
    apply (erule converse_rtranclE)
     apply (clarsimp)
     apply (erule (9) 4)
     apply (simp add: valid_pde_def pde_ref_def split: pde.splits)+
    by (clarsimp simp: obj_at_def vs_refs_def
                dest!: vs_lookup1D)
qed

lemma vs_lookup_pagesE_alt:
  assumes vl: "(ref \<unrhd> p) s"
  assumes va: "valid_vspace_objs s"
  assumes vt: "(\<forall>p\<in>ran (x64_asid_table (arch_state s)). asid_pool_at p s)"
  assumes 0: "\<And>a. x64_asid_table (arch_state s) a = Some p \<Longrightarrow>
                   typ_at (AArch AASIDPool) p s \<Longrightarrow>
                   R [VSRef (ucast a) None] p"
  assumes 1: "\<And>a p\<^sub>1 ap b.
       \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p; page_map_l4_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 2: "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c.
       \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2;
        kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
        c \<notin> kernel_mapping_slots; pml4e_ref_pages (pm c) = Some p;
        valid_pml4e (pm c) s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast c) (Some APageMapL4),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 3: "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c addr x y pdpt d.
       \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2; kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
        pm c = PDPointerTablePML4E addr x y;
        kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
        c \<notin> kernel_mapping_slots; pdpte_ref_pages (pdpt d) = Some p;
        valid_pdpte (pdpt d) s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 4: "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c addr x y pdpt d addr' x' y' pd e.
       \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2; kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
        pm c = PDPointerTablePML4E addr x y;
        kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
        pdpt d = PageDirectoryPDPTE addr' x' y';
        kheap s (ptrFromPAddr addr') = Some (ArchObj (PageDirectory pd));
        c \<notin> kernel_mapping_slots; pde_ref_pages (pd e) = Some p; valid_pde (pd e) s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast e) (Some APageDirectory),
              VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 5: "\<And>a p\<^sub>1 ap b p\<^sub>2 pm c addr x y pdpt d addr' x' y' pd e addr'' x'' y'' pt f.
       \<lbrakk>x64_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2; kheap s p\<^sub>2 = Some (ArchObj (PageMapL4 pm));
        pm c = PDPointerTablePML4E addr x y;
        kheap s (ptrFromPAddr addr) = Some (ArchObj (PDPointerTable pdpt));
        pdpt d = PageDirectoryPDPTE addr' x' y';
        kheap s (ptrFromPAddr addr') = Some (ArchObj (PageDirectory pd));
        pd e = PageTablePDE addr'' x'' y'';
        kheap s (ptrFromPAddr addr'') = Some (ArchObj (PageTable pt));
        c \<notin> kernel_mapping_slots; pte_ref_pages (pt f) = Some p; valid_pte (pt f) s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast f) (Some APageTable), VSRef (ucast e) (Some APageDirectory),
              VSRef (ucast d) (Some APDPointerTable), VSRef (ucast c) (Some APageMapL4),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  shows "R ref p"
proof -
  note vao = valid_vspace_objs_alt[THEN iffD1, OF conjI[OF vt va]]
  note vat = vao[THEN conjunct1, rule_format]
  note vap = vao[THEN conjunct2, THEN conjunct1, rule_format]
  note vpm = vao[THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  note vpdpt = vao[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  note vpd = vao[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  note vpt = vao[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format]

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
    apply (frule (4) vpm)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (6) 2)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def obj_at_def
                          pml4e_ref_pages_def
                   dest!: vs_lookup_pages1D
                   split: if_split_asm pml4e.splits)
    apply (frule_tac d=ac in vpdpt, assumption+)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (8) 3)
    apply (clarsimp simp:vs_refs_pages_def graph_of_def obj_at_def
                          pdpte_ref_pages_def
                   dest!: vs_lookup_pages1D
                   split: pdpte.splits)
        apply (frule_tac e=ad in vpd, assumption+)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (10) 4)
    apply (clarsimp simp:vs_refs_pages_def graph_of_def obj_at_def
                          pde_ref_pages_def
                   dest!: vs_lookup_pages1D
                   split: pde.splits)
        apply (frule_tac fa=ae in vpt, assumption+)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (12) 5)
    apply (auto simp: vs_refs_pages_def graph_of_def obj_at_def
                      pte_ref_pages_def data_at_def
               dest!: vs_lookup_pages1D
               split: pte.splits)
    done
qed

lemma valid_asid_tableD:
  "\<lbrakk> T x = Some p; valid_asid_table T s \<rbrakk> \<Longrightarrow> asid_pool_at p s"
  by (auto simp: valid_asid_table_def ran_def)

declare graph_of_empty[simp]

lemma pml4e_graph_ofI:
  "\<lbrakk>pm x = pme; x \<notin> kernel_mapping_slots; pml4e_ref pme = Some v\<rbrakk>
   \<Longrightarrow> (x, v) \<in> graph_of (\<lambda>x. if x \<in> kernel_mapping_slots then None
                              else pml4e_ref (pm x))"
  by (rule graph_ofI, simp)

lemma vs_refs_pml4I:
  "\<lbrakk>pm ((ucast (r :: machine_word)) :: 9 word) = PDPointerTablePML4E x a b;
     ucast r \<notin> kernel_mapping_slots; \<forall>n \<ge> 9. n < 64 \<longrightarrow> \<not> r !! n\<rbrakk>
   \<Longrightarrow> (VSRef r (Some APageMapL4), ptrFromPAddr x)
       \<in> vs_refs (ArchObj (PageMapL4 pm))"
  apply (simp add: vs_refs_def)
  apply (rule image_eqI[rotated])
   apply (rule pml4e_graph_ofI)
     apply (simp add: pml4e_ref_def)+
  apply (simp add: ucast_ucast_mask)
  apply (rule word_eqI)
  apply (simp add: word_size)
  apply (rule ccontr, auto)
  done


lemma pde_graph_ofI:
  "\<lbrakk>pd x = pde; pde_ref pde = Some v\<rbrakk> \<Longrightarrow> (x,v) \<in> graph_of (pde_ref \<circ> pd)"
  by (rule graph_ofI) simp

lemma vs_refs_pdI:
  "\<lbrakk>pd ((ucast (r :: machine_word)) :: 9 word) = PageTablePDE x a b;
     \<forall>n \<ge> 9. n < 64 \<longrightarrow> \<not> r !! n\<rbrakk>
   \<Longrightarrow> (VSRef r (Some APageDirectory), ptrFromPAddr x)
       \<in> vs_refs (ArchObj (PageDirectory pd))"
  apply (simp add: vs_refs_def)
  apply (rule image_eqI[rotated])
   apply (rule pde_graph_ofI)
     apply assumption
    apply (simp add: pde_ref_def)
  apply (simp add: ucast_ucast_mask)
  apply (rule word_eqI)
  apply (simp add: word_size)
  apply (rule ccontr, auto)
  done

lemma aa_type_pdD:
  "aa_type ko = APageDirectory \<Longrightarrow> \<exists>pd. ko = PageDirectory pd"
  by (clarsimp simp: aa_type_def
               split: arch_kernel_obj.splits if_split_asm)

lemma empty_table_is_valid:
  "\<lbrakk>empty_table (set (second_level_tables (arch_state s))) (ArchObj ao);
    valid_arch_state s\<rbrakk>
   \<Longrightarrow> valid_vspace_obj ao s"
  by (cases ao, simp_all add: empty_table_def)

lemma empty_table_pml4e_refD:
  "\<lbrakk> pml4e_ref (pm x) = Some r; empty_table S (ArchObj (PageMapL4 pm)) \<rbrakk> \<Longrightarrow>
  r \<in> S"
  by (simp add: empty_table_def)

lemma valid_global_pdptsD:
  "\<lbrakk>r \<in> set (x64_global_pdpts (arch_state s)); valid_global_objs s;  ko_at (ArchObj (PDPointerTable pdpt)) r s\<rbrakk>
    \<Longrightarrow>  (\<forall>x. aligned_pdpte (pdpt x))
             \<and> (\<forall>r. pdpte_ref (pdpt x) = Some r
                     \<longrightarrow> r \<in> set (x64_global_pds (arch_state s)))
             \<and> valid_global_pdpt pdpt"
  apply (clarsimp simp: valid_global_objs_def)
  apply (drule_tac x=r in bspec, assumption)
  by (auto simp: obj_at_def)

lemma valid_table_caps_pdD:
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PageDirectoryCap pd None));
     valid_table_caps s \<rbrakk> \<Longrightarrow>
    obj_at (empty_table (set (second_level_tables (arch_state s)))) pd s"
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
  assumes a: "\<And>asid p. \<lbrakk> x64_asid_table (arch_state s) asid = Some p \<rbrakk> \<Longrightarrow> P [VSRef (ucast asid) None] p s"
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
  assumes a: "\<And>asid p. \<lbrakk> x64_asid_table (arch_state s) asid = Some p \<rbrakk> \<Longrightarrow> P [VSRef (ucast asid) None] p s"
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
               \<le> [None, Some AASIDPool, Some APageMapL4, Some APDPointerTable,
                        Some APageDirectory, Some APageTable]"
  apply (erule vs_lookup_induct)
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def ranI)
  apply (clarsimp dest!: vs_lookup1D elim!: obj_atE)
  apply (clarsimp simp: vs_refs_def a_type_simps
                 split: kernel_object.split_asm arch_kernel_obj.split_asm
                 dest!: graph_ofD)
     apply (drule valid_vspace_objsD, simp add: obj_at_def, assumption)
     apply (case_tac rs; simp)
     apply (case_tac list; simp add: ranI)
     apply (case_tac lista; simp add: ranI)
     apply (case_tac listb; simp)
     apply (case_tac listc; simp)
     apply (frule prefix_length_le, clarsimp)
    apply (drule valid_vspace_objsD, simp add: obj_at_def, assumption)
    apply (clarsimp simp: pde_ref_def split: pde.split_asm)
    apply (drule_tac x=a in spec, simp)
    apply (case_tac rs; simp)
    apply (case_tac list; simp)
    apply (case_tac lista; simp)
    apply (case_tac listb; simp)
    apply (case_tac listc; simp)
    apply (frule prefix_length_le, clarsimp)
   apply (drule valid_vspace_objsD, simp add: obj_at_def, assumption)
   apply (clarsimp simp: pdpte_ref_def split: pdpte.split_asm)
   apply (drule_tac x=a in spec, simp)
   apply (case_tac rs; simp)
   apply (case_tac list; simp)
   apply (case_tac lista; simp)
   apply (case_tac listb; simp)
   apply (case_tac listc; simp)
   apply (frule prefix_length_le, clarsimp)
  apply (drule valid_vspace_objsD, simp add: obj_at_def, assumption)
  apply (clarsimp simp: pml4e_ref_def split: pml4e.split_asm if_split_asm)
  apply (drule_tac x=a in bspec, simp)
  apply (case_tac rs; simp)
  apply (case_tac list; simp)
  apply (case_tac lista; simp)
  apply (case_tac listb; simp)
  apply (case_tac listc; simp)
  apply (frule prefix_length_le, clarsimp)
  done

lemma addrFromPPtr_ptrFromPAddr_id[simp]:
  "addrFromPPtr (ptrFromPAddr x) = x"
by (simp add: addrFromPPtr_def ptrFromPAddr_def)

lemma valid_pte_lift2:
  assumes x: "\<And>T p. \<lbrace>Q and typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_pte pte s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pte pte s\<rbrace>"
  by (cases pte) (simp add: data_at_def | wp hoare_vcg_disj_lift x)+

lemma valid_pde_lift2:
  assumes x: "\<And>T p. \<lbrace>Q and typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_pde pde s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pde pde s\<rbrace>"
  by (cases pde) (simp add: data_at_def | wp hoare_vcg_disj_lift x)+

lemma valid_pdpte_lift2:
  assumes x: "\<And>T p. \<lbrace>Q and typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_pdpte pde s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pdpte pde s\<rbrace>"
  by (cases pde) (simp add: data_at_def | wp hoare_vcg_disj_lift x)+

lemma valid_pml4e_lift2:
  assumes x: "\<And>T p. \<lbrace>Q and typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_pml4e pde s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pml4e pde s\<rbrace>"
  by (cases pde) (simp | wp x)+

lemma valid_vspace_obj_typ2:
  assumes P: "\<And>P p T. \<lbrace>\<lambda>s. Q s \<and> P (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Q s \<and> valid_vspace_obj ob s\<rbrace> f \<lbrace>\<lambda>rv s. valid_vspace_obj ob s\<rbrace>"
  apply (cases ob, simp_all)
        by (wp hoare_vcg_all_lift hoare_vcg_ball_lift valid_pte_lift2 hoare_vcg_const_Ball_lift[OF P]
            valid_pde_lift2 valid_pdpte_lift2 valid_pml4e_lift2 P
           | clarsimp
           | assumption
           | rule hoare_pre)+

lemma valid_vspace_objsI [intro?]:
  "(\<And>p ao. \<lbrakk> (\<exists>\<rhd> p) s; ko_at (ArchObj ao) p s \<rbrakk> \<Longrightarrow> valid_vspace_obj ao s) \<Longrightarrow> valid_vspace_objs s"
  by (simp add: valid_vspace_objs_def)

lemma vs_lookup1_stateI2:
  assumes 1: "(r \<rhd>1 r') s"
  assumes ko: "\<And>ko. \<lbrakk> ko_at ko (snd r) s; vs_refs ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') (snd r) s'"
  shows "(r \<rhd>1 r') s'" using 1 ko
  by (fastforce simp: obj_at_def vs_lookup1_def)


lemma vs_lookupI:
  "\<lbrakk> ref' \<in> vs_asid_refs (x64_asid_table (arch_state s));
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
  "([VSRef (ucast asid) None] \<rhd> p) s \<Longrightarrow> x64_asid_table (arch_state s) asid = Some p"
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
  "([VSRef (ucast asid) None] \<rhd> p) s \<Longrightarrow> (x64_asid_table (arch_state s) asid = Some p \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast dest: vs_lookup_atD)

lemma vs_lookup_2ConsD:
  "((v # v' # vs) \<rhd> p) s \<Longrightarrow> \<exists>p'. ((v'#vs) \<rhd> p') s \<and> ((v' # vs,p') \<rhd>1 (v # v' # vs, p)) s"
  apply (clarsimp simp: vs_lookup_def)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def)
  apply (fastforce simp: vs_lookup1_def)
  done

lemma global_refs_asid_table_update [iff]:
  "global_refs (s\<lparr>arch_state := x64_asid_table_update f (arch_state s)\<rparr>) = global_refs s"
  by (simp add: global_refs_def)

lemma pspace_in_kernel_window_arch_update[simp]:
  "x64_kernel_vspace (f (arch_state s)) = x64_kernel_vspace (arch_state s)
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

lemma wellformed_arch_default:
  "arch_valid_obj (default_arch_object aobject_type dev us) s"
  unfolding arch_valid_obj_def default_arch_object_def
  by (cases aobject_type; simp)

lemma valid_vspace_obj_default':
  "valid_vspace_obj (default_arch_object aobject_type dev us) s"
  unfolding default_arch_object_def
  by (cases aobject_type; simp)

lemma valid_vspace_obj_entryD:
  shows valid_vspace_obj_pml4eD: "\<lbrakk>valid_vspace_obj (PageMapL4 pm) s; pm i = pml4e; i \<notin> kernel_mapping_slots\<rbrakk> \<Longrightarrow> valid_pml4e pml4e s"
    and valid_vspace_obj_pdpteD: "\<lbrakk>valid_vspace_obj (PDPointerTable pdpt) s; pdpt i = pdpte\<rbrakk> \<Longrightarrow> valid_pdpte pdpte s"
    and valid_vspace_obj_pdeD  : "\<lbrakk>valid_vspace_obj (PageDirectory pd) s; pd i = pde\<rbrakk> \<Longrightarrow> valid_pde pde s"
    and valid_vspace_obj_pteD  : "\<lbrakk>valid_vspace_obj (PageTable pt) s; pt i = pte\<rbrakk> \<Longrightarrow> valid_pte pte s"
  by fastforce+

lemmas valid_vspace_objsD_alt'
  = valid_vspace_objsD[simplified obj_at_def, simplified]

lemmas valid_vspace_objs_entryD
  = valid_vspace_obj_entryD[OF valid_vspace_objsD_alt']

lemmas vs_lookup_step_alt
  = vs_lookup_step[OF _ vs_lookup1I[OF _ _ refl], simplified obj_at_def, simplified]

lemma pdpte_graph_ofI:
  "\<lbrakk>pdpt x = pdpte; pdpte_ref pdpte = Some v\<rbrakk> \<Longrightarrow> (x, v) \<in> graph_of (pdpte_ref \<circ> pdpt)"
  by (rule graph_ofI, simp)

lemma vs_refs_pdptI:
  "\<lbrakk>pdpt ((ucast (r :: machine_word)) :: 9 word) = PageDirectoryPDPTE x a b;
     \<forall>n \<ge> 9. n < 64 \<longrightarrow> \<not> r !! n\<rbrakk>
   \<Longrightarrow> (VSRef r (Some APDPointerTable), ptrFromPAddr x) \<in> vs_refs (ArchObj (PDPointerTable pdpt))"
  apply (simp add: vs_refs_def)
  apply (rule image_eqI[rotated])
   apply (erule pdpte_graph_ofI)
   apply (simp add: pdpte_ref_def)
  apply (simp add: ucast_ucast_mask)
  apply (rule word_eqI)
  apply (simp add: word_size)
  apply (rule ccontr, auto)
  done

text \<open>arch specific symrefs\<close> (* hyp_ref stubs : for compatibility with arm-hyp *)

definition
  tcb_hyp_refs :: "arch_tcb \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "tcb_hyp_refs atcb \<equiv> {}"

lemma tcb_hyp_refs_of_simps[simp]: "tcb_hyp_refs atcb = {}"
  by (auto simp: tcb_hyp_refs_def)

definition
  refs_of_a :: "arch_kernel_obj \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "refs_of_a x \<equiv> {}"

lemma refs_of_a_simps[simp]: "refs_of_a ao = {}"
  by (auto simp: refs_of_a_def)

definition
  hyp_refs_of :: "kernel_object \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "hyp_refs_of x \<equiv> case x of
     CNode sz fun      => {}
   | TCB tcb           => tcb_hyp_refs (tcb_arch tcb)
   | Endpoint ep       => {}
   | Notification ntfn => {}
   | ArchObj ao        => refs_of_a ao"

lemma hyp_refs_of_simps[simp]: "hyp_refs_of obj = {}"
  by (auto simp: hyp_refs_of_def split: kernel_object.splits)

definition
  state_hyp_refs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "state_hyp_refs_of s \<equiv> \<lambda>x. case (kheap s x) of Some ko \<Rightarrow> hyp_refs_of ko | None \<Rightarrow> {}"

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
  done

lemma hyp_sym_refs_ko_atD:
  "\<lbrakk> ko_at ko p s; sym_refs (state_hyp_refs_of s) \<rbrakk> \<Longrightarrow>
     state_hyp_refs_of s p = hyp_refs_of ko \<and>
     (\<forall>(x, tp)\<in>hyp_refs_of ko.  obj_at (\<lambda>ko. (p, symreftype tp) \<in> hyp_refs_of ko) x s)"
  by (drule(1) hyp_sym_refs_obj_atD, simp)

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
  done

lemma hyp_refs_of_hyp_live_obj:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> P ko; hyp_refs_of ko = {} \<rbrakk> \<Longrightarrow> False \<rbrakk> \<Longrightarrow> obj_at hyp_live p s"
  by (fastforce simp: obj_at_def hyp_refs_of_hyp_live)

(* use tcb_arch_ref to handle obj_refs in tcb_arch: currently there is a vcpu ref only *)

definition tcb_arch_ref :: "tcb \<Rightarrow> obj_ref option"
where "tcb_arch_ref t \<equiv> None"

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
  by (simp add: tcb_arch_ref_def arch_tcb_set_registers_def)

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
  by (simp add: arch_gen_obj_refs_def split: arch_cap.splits)

lemma obj_ref_not_arch_gen_ref:
  "x \<in> obj_refs cap \<Longrightarrow> arch_gen_refs cap = {}"
  apply (cases cap; simp add: arch_gen_obj_refs_def split: arch_cap.splits)
  by (rename_tac ac, case_tac ac; clarsimp)

lemma same_aobject_same_arch_gen_refs:
  "same_aobject_as ac ac' \<Longrightarrow> arch_gen_obj_refs ac = arch_gen_obj_refs ac'"
  by (clarsimp simp: arch_gen_obj_refs_def split: arch_cap.split_asm)

lemma arch_gen_ref_not_obj_ref:
  "x \<in> arch_gen_refs cap \<Longrightarrow> obj_refs cap = {}"
  by (cases cap; simp add: arch_gen_obj_refs_def split: arch_cap.splits)

lemmas arch_gen_obj_refs_simps[simp] = arch_gen_obj_refs_def[split_simps arch_cap.split]

lemma valid_arch_mdb_eqI:
  assumes "valid_arch_mdb (is_original_cap s) (caps_of_state s)"
  assumes "caps_of_state s = caps_of_state s'"
  assumes "is_original_cap s = is_original_cap s'"
  shows "valid_arch_mdb (is_original_cap s') (caps_of_state s')" using assms
  by (clarsimp simp: valid_arch_mdb_def)



lemma asid_low_bits_of_mask_eq:
  "ucast (asid_low_bits_of asid) = asid && mask asid_low_bits"
  by (simp add: asid_bits_defs asid_bits_of_defs ucast_ucast_mask)

lemmas asid_low_bits_of_p2m1_eq =
  asid_low_bits_of_mask_eq[simplified mask_2pm1]

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

end

declare X64.arch_tcb_context_absorbs[simp]
declare X64.arch_tcb_context_get_set[simp]

setup \<open>Add_Locale_Code_Defs.setup "X64"\<close>
setup \<open>Add_Locale_Code_Defs.setup "X64_A"\<close>

end
