(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* This theory contains the arch-dependent part of invariant definitions.
   Due to the large amount of definitions, we place it before Invariants_H rather than fixing
   constants in locales. *)

theory ArchInvsDefs_H
imports
  InvariantsPre_H
  ArchMove_R
begin

(* disambiguate name clash between Arch and non-arch definitions with same names *)
context Arch begin

lemmas haskell_crunch_def[crunch_def] =
  deriveCap_def finaliseCap_def
  hasCancelSendRights_def sameRegionAs_def isPhysicalCap_def
  sameObjectAs_def updateCapData_def maskCapRights_def
  createObject_def capUntypedPtr_def capUntypedSize_def
  performInvocation_def decodeInvocation_def

context begin global_naming global
requalify_facts (aliasing)
  Retype_H.deriveCap_def Retype_H.finaliseCap_def
  Retype_H.hasCancelSendRights_def Retype_H.sameRegionAs_def Retype_H.isPhysicalCap_def
  Retype_H.sameObjectAs_def Retype_H.updateCapData_def Retype_H.maskCapRights_def
  Retype_H.createObject_def Retype_H.capUntypedPtr_def Retype_H.capUntypedSize_def
  Retype_H.performInvocation_def Retype_H.decodeInvocation_def
end
end

context Arch begin arch_global_naming

abbreviation
  "pde_at' \<equiv> typ_at' (ArchT PDET)"
abbreviation
  "pte_at' \<equiv> typ_at' (ArchT PTET)"
abbreviation
  "pdpte_at' \<equiv> typ_at' (ArchT PDPTET)"
abbreviation
  "pml4e_at' \<equiv> typ_at' (ArchT PML4ET)"

(* hyp_refs *)

definition tcb_hyp_refs' :: "arch_tcb \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_hyp_refs' t \<equiv> {}" \<comment> \<open>no VCPUs on this architecture\<close>

definition refs_of_a' :: "arch_kernel_object \<Rightarrow> (obj_ref \<times> reftype) set" where
  "refs_of_a' x \<equiv> {}"

definition arch_live' :: "arch_kernel_object \<Rightarrow> bool" where
  "arch_live' ao \<equiv> False"

definition hyp_live' :: "kernel_object \<Rightarrow> bool" where
  "hyp_live' ko \<equiv> False"

definition azobj_refs' :: "arch_capability \<Rightarrow> obj_ref set" where
  "azobj_refs' _ = {}"

(* FIXME arch-split: might need to add more here, non-arch-split X64 proofs don't know these yet *)
lemmas [simp] = refs_of_a'_def azobj_refs'_def


section "Valid caps and objects (design spec)"

primrec acapBits :: "arch_capability \<Rightarrow> nat" where
  "acapBits (ASIDPoolCap x y) = asidLowBits + word_size_bits"
| "acapBits ASIDControlCap = asidHighBits + word_size_bits"
| "acapBits (PageCap x y typ sz d z) = pageBitsForSize sz"
| "acapBits (PageTableCap x y) = table_size"
| "acapBits (PageDirectoryCap x y) = table_size"
| "acapBits (PDPointerTableCap x y) = table_size"
| "acapBits (PML4Cap x y) = table_size"
| "acapBits (IOPortCap f l) = 0"
| "acapBits IOPortControlCap = 0"

definition
  page_table_at' :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "page_table_at' x \<equiv> \<lambda>s. is_aligned x ptBits
                      \<and> (\<forall>y < 2 ^ ptTranslationBits. typ_at' (ArchT PTET) (x + (y << word_size_bits)) s)"

definition
  page_directory_at' :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "page_directory_at' x \<equiv> \<lambda>s. is_aligned x pdBits
                      \<and> (\<forall>y < 2 ^ ptTranslationBits. typ_at' (ArchT PDET) (x + (y << word_size_bits)) s)"

definition
  pd_pointer_table_at' :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "pd_pointer_table_at' x \<equiv> \<lambda>s. is_aligned x pdptBits
                      \<and> (\<forall>y < 2 ^ ptTranslationBits. typ_at' (ArchT PDPTET) (x + (y << word_size_bits)) s)"

definition
  page_map_l4_at' :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "page_map_l4_at' x \<equiv> \<lambda>s. is_aligned x pml4Bits
                      \<and> (\<forall>y < 2 ^ ptTranslationBits. typ_at' (ArchT PML4ET) (x + (y << word_size_bits)) s)"

lemmas vspace_table_at'_defs
  = page_table_at'_def page_directory_at'_def pd_pointer_table_at'_def page_map_l4_at'_def

abbreviation
  "asid_pool_at' \<equiv> typ_at' (ArchT ASIDPoolT)"

(* FIXME arch-split: no wellformed_acap' on X64 *)

definition valid_arch_cap' :: "arch_capability \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_cap' acap s \<equiv> case acap
   of ASIDPoolCap pool asid \<Rightarrow>
        typ_at' (ArchT ASIDPoolT) pool s \<and> is_aligned asid asid_low_bits \<and> asid_wf asid
    | ASIDControlCap \<Rightarrow> True
    | PageCap ref rghts t sz d mapdata \<Rightarrow> ref \<noteq> 0 \<and>
        (\<forall>p < 2 ^ (pageBitsForSize sz - pageBits). typ_at' (if d then UserDataDeviceT else UserDataT)
        (ref + p * 2 ^ pageBits) s) \<and>
        (case mapdata of None \<Rightarrow> (t=VMNoMap) | Some (asid, ref) \<Rightarrow>
                (t = VMVSpaceMap) \<and> 0 < asid \<and> asid_wf asid \<and> vmsz_aligned ref sz \<and> ref < pptrBase)
    | PageTableCap ref mapdata \<Rightarrow>
        page_table_at' ref s \<and>
        (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow>
                0 < asid \<and> asid_wf asid \<and> ref < pptrBase)
    | PageDirectoryCap ref mapdata \<Rightarrow>
        page_directory_at' ref s \<and>
        (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow> 0 < asid \<and> asid_wf asid \<and> ref < pptrBase)
    | PDPointerTableCap ref mapdata \<Rightarrow>
        pd_pointer_table_at' ref s \<and>
        (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow> 0 < asid \<and> asid_wf asid \<and> ref < pptrBase)
    | PML4Cap ref mapdata \<Rightarrow>
        page_map_l4_at' ref s \<and>
        case_option True (\<lambda>asid. 0 < asid \<and> asid_wf asid) mapdata
    | IOPortCap first l \<Rightarrow> first \<le> l
    | IOPortControlCap \<Rightarrow> True"

lemmas valid_arch_cap'_simps[simp] =
  valid_arch_cap'_def[split_simps arch_capability.split, simplified]

definition arch_valid_irq :: "irq \<Rightarrow> bool" where
  "arch_valid_irq irq \<equiv> irq \<le> maxIRQ"

(* within the Arch locale, we want automatic expansion of the valid irq conditions *)
lemmas [simp] = arch_valid_irq_def

definition valid_arch_tcb' :: "Structures_H.arch_tcb \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_tcb' \<equiv> \<lambda>t. \<top>"

definition valid_mapping' :: "machine_word \<Rightarrow> vmpage_size \<Rightarrow> bool" where
 "valid_mapping' x sz \<equiv> is_aligned x (pageBitsForSize sz) \<and> ptrFromPAddr x \<noteq> 0"

primrec valid_pte' :: "X64_H.pte \<Rightarrow> bool" where
  "valid_pte' (InvalidPTE) = True"
| "valid_pte' (SmallPagePTE ptr _ _ _ _ _ _ _ _) = valid_mapping' ptr X64SmallPage"

primrec valid_pde' :: "X64_H.pde \<Rightarrow> bool" where
 "valid_pde' (InvalidPDE) = True"
| "valid_pde' (LargePagePDE ptr _ _ _ _ _ _ _ _) = (valid_mapping' ptr X64LargePage)"
| "valid_pde' (PageTablePDE ptr _ _ _ _ _) = is_aligned ptr ptBits"

primrec valid_pdpte' :: "X64_H.pdpte \<Rightarrow> bool" where
 "valid_pdpte' (InvalidPDPTE) = True"
| "valid_pdpte' (HugePagePDPTE ptr _ _ _ _ _ _ _ _) = (valid_mapping' ptr X64HugePage)"
| "valid_pdpte' (PageDirectoryPDPTE ptr _ _ _ _ _) = is_aligned ptr pdBits"

primrec valid_pml4e' :: "X64_H.pml4e \<Rightarrow> bool" where
 "valid_pml4e' (InvalidPML4E) = True"
| "valid_pml4e' (PDPointerTablePML4E ptr _ _ _ _ _) = is_aligned ptr pdptBits"

primrec valid_asid_pool' :: "asidpool \<Rightarrow> bool" where
 "valid_asid_pool' (ASIDPool pool)
     = (dom pool \<subseteq> {0 .. 2^asid_low_bits - 1}
        \<and> 0 \<notin> ran pool \<and> (\<forall>x \<in> ran pool. is_aligned x pml4Bits))"

primrec valid_arch_obj' :: "arch_kernel_object \<Rightarrow> bool" where
  "valid_arch_obj' (KOASIDPool pool) = valid_asid_pool' pool"
| "valid_arch_obj' (KOPDE pde) = valid_pde' pde"
| "valid_arch_obj' (KOPTE pte) = valid_pte' pte"
| "valid_arch_obj' (KOPDPTE pdpte) = valid_pdpte' pdpte"
| "valid_arch_obj' (KOPML4E pml4e) = valid_pml4e' pml4e"

definition pspace_in_kernel_mappings' :: "kernel_state \<Rightarrow> bool" where
 "pspace_in_kernel_mappings' s \<equiv> \<forall>p \<in> dom (ksPSpace s). p \<in> kernel_mappings"

primrec acapClass :: "arch_capability \<Rightarrow> capclass" where
  "acapClass (ASIDPoolCap x y)      = PhysicalClass"
| "acapClass ASIDControlCap         = ASIDMasterClass"
| "acapClass (PageCap x y t sz d z) = PhysicalClass"
| "acapClass (PageTableCap x y)     = PhysicalClass"
| "acapClass (PageDirectoryCap x y) = PhysicalClass"
| "acapClass (PDPointerTableCap x y) = PhysicalClass"
| "acapClass (PML4Cap x y) = PhysicalClass"
| "acapClass (IOPortCap x y) = IOPortClass"
| "acapClass IOPortControlCap = IOPortClass"

(* No arch badges currently on this architecture *)
definition valid_arch_badges :: "capability \<Rightarrow> capability \<Rightarrow> mdbnode \<Rightarrow> bool" where
  "valid_arch_badges cap cap' node' \<equiv> True"

(* No additional arch assumptions about the MDB *)
definition mdb_chunked_arch_assms :: "capability \<Rightarrow> bool" where
  "mdb_chunked_arch_assms cap \<equiv> True"

definition
  isArchFrameCap :: "capability \<Rightarrow> bool"
where
 "isArchFrameCap cap \<equiv> case cap of ArchObjectCap (PageCap ref rghts typ sz d data) \<Rightarrow> True | _ \<Rightarrow> False"

(* FIXME arch-split: compatibility shim, can be removed by arch-wide rename *)
abbreviation (input)
  "isArchPageCap \<equiv> isArchFrameCap"

lemmas isArchPageCap_def = isArchFrameCap_def

definition
  isArchIOPortCap :: "capability \<Rightarrow> bool"
where
  "isArchIOPortCap cap \<equiv> case cap of ArchObjectCap (IOPortCap f l) \<Rightarrow> True | _ \<Rightarrow> False"

definition table_refs' :: "machine_word \<Rightarrow> machine_word set" where
  "table_refs' x \<equiv> (\<lambda>y. x + (y << word_size_bits)) ` {y. y < 2^ptTranslationBits}"

definition global_refs' :: "kernel_state \<Rightarrow> obj_ref set" where
  "global_refs' \<equiv> \<lambda>s.
  {ksIdleThread s} \<union>
   table_refs' (x64KSSKIMPML4 (ksArchState s)) \<union>
   (\<Union>pt \<in> set (x64KSSKIMPDs (ksArchState s)). table_refs' pt) \<union>
   (\<Union>pt \<in> set (x64KSSKIMPTs (ksArchState s)). table_refs' pt) \<union>
   (\<Union>pt \<in> set (x64KSSKIMPDPTs (ksArchState s)). table_refs' pt) \<union>
   range (\<lambda>irq :: irq. irq_node' s + 32 * ucast irq)"

definition valid_asid_table' :: "(asid \<rightharpoonup> machine_word) \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_asid_table' table \<equiv> \<lambda>s. dom table \<subseteq> {0 .. 2^asid_high_bits - 1}
                                 \<and> 0 \<notin> ran table"

primrec valid_cr3' :: "cr3 \<Rightarrow> bool" where
  "valid_cr3' (CR3 addr pcid) = (is_aligned addr asid_bits
                                   \<and> addr \<le> mask (pml4ShiftBits + asid_bits)
                                   \<and> asid_wf pcid)"

definition
  valid_global_pts' :: "machine_word list \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_global_pts' pts \<equiv> \<lambda>s. \<forall>p \<in> set pts. page_table_at' p s"

definition
  valid_global_pds' :: "machine_word list \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_global_pds' pds \<equiv> \<lambda>s. \<forall>p \<in> set pds. page_directory_at' p s"

definition
  valid_global_pdpts' :: "machine_word list \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_global_pdpts' pdpts \<equiv> \<lambda>s. \<forall>p \<in> set pdpts. pd_pointer_table_at' p s"

definition
  valid_x64_irq_state' :: "(8 word \<Rightarrow> x64irqstate) \<Rightarrow> bool"
where
  "valid_x64_irq_state' irqState \<equiv> \<forall>irq > maxIRQ. irqState irq = X64IRQFree"

definition valid_ioapic_2 :: "machine_word \<Rightarrow> (machine_word \<Rightarrow> 8 word) \<Rightarrow> bool" where
  "valid_ioapic_2 num_ioapics ioapic_nirqs \<equiv>
    num_ioapics \<le> of_nat Kernel_Config.maxNumIOAPIC \<and>
    (\<forall>ioapic < num_ioapics. 0 < ioapic_nirqs ioapic) \<and>
    (\<forall>ioapic < num_ioapics. ioapic_nirqs ioapic \<le> ucast ioapicIRQLines) \<and>
    (\<forall>ioapic > of_nat Kernel_Config.maxNumIOAPIC. ioapic_nirqs ioapic = 0)"

abbreviation valid_ioapic where
  "valid_ioapic s \<equiv>
     valid_ioapic_2 (x64KSNumIOAPICs (ksArchState s)) (x64KSIOAPICnIRQs (ksArchState s))"

lemmas valid_ioapic_def = valid_ioapic_2_def

definition valid_arch_state' :: "kernel_state \<Rightarrow> bool" where
  "valid_arch_state' \<equiv> \<lambda>s.
  valid_asid_table' (x64KSASIDTable (ksArchState s)) s \<and>
  valid_cr3' (x64KSCurrentUserCR3 (ksArchState s)) \<and>
  page_map_l4_at' (x64KSSKIMPML4 (ksArchState s)) s \<and>
  valid_global_pds' (x64KSSKIMPDs (ksArchState s)) s \<and>
  valid_global_pdpts' (x64KSSKIMPDPTs (ksArchState s)) s \<and>
  valid_global_pts' (x64KSSKIMPTs (ksArchState s)) s \<and>
  valid_x64_irq_state' (x64KSIRQState (ksArchState s)) \<and>
  valid_ioapic s"

definition cap_ioports' :: "capability \<Rightarrow> ioport set" where
  "cap_ioports' c \<equiv> case c of
    ArchObjectCap (IOPortCap f l) \<Rightarrow> {f..l}
  | _ \<Rightarrow> {}"

definition issued_ioports' :: "Arch.kernel_state \<Rightarrow> ioport set" where
  "issued_ioports' \<equiv> \<lambda>as. Collect (x64KSAllocatedIOPorts as)"

definition all_ioports_issued' :: "(machine_word \<Rightarrow> capability option) \<Rightarrow> Arch.kernel_state \<Rightarrow> bool"
   where
  "all_ioports_issued' \<equiv> \<lambda>cs as. \<forall>cap \<in> ran cs. cap_ioports' cap \<subseteq> issued_ioports' as"

definition archMakeObjectT :: "arch_kernel_object_type \<Rightarrow> kernel_object" where
  "archMakeObjectT atp \<equiv>
     case atp
     of PDET \<Rightarrow> injectKO (makeObject :: pde)
      | PTET \<Rightarrow> injectKO (makeObject :: pte)
      | PDPTET \<Rightarrow> injectKO (makeObject :: pdpte)
      | PML4ET \<Rightarrow> injectKO (makeObject :: pml4e)
      | ASIDPoolT \<Rightarrow> injectKO (makeObject :: asidpool)"

end
end
