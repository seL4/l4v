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

definition canonical_address :: "machine_word \<Rightarrow> bool" where
  "canonical_address \<equiv> \<top>" \<comment> \<open>this concept does not exist on ARM\<close>

(* this architecture does not use kernel_mappings / pspace_in_kernel_mappings *)
definition kernel_mappings :: "machine_word set" where
  "kernel_mappings \<equiv> UNIV"

definition pspace_in_kernel_mappings' :: "kernel_state \<Rightarrow> bool" where
 "pspace_in_kernel_mappings' \<equiv> \<top>"

(* FIXME arch-split: if pspace_in_kernel_mappings becomes part of generic interface,
   check whether having this simp is still beneficial *)
lemmas [simp] = pspace_in_kernel_mappings'_def kernel_mappings_def

abbreviation pde_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pde_at' \<equiv> typ_at' (ArchT PDET)"
abbreviation pte_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pte_at' \<equiv> typ_at' (ArchT PTET)"

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

(* FIXME arch-split: might need to add more here, non-arch-split ARM proofs don't know these yet *)
lemmas [simp] = refs_of_a'_def azobj_refs'_def


section "Valid caps and objects (design spec)"

primrec acapBits :: "arch_capability \<Rightarrow> nat" where
  "acapBits (ASIDPoolCap _ _)       = asidLowBits + word_size_bits"
| "acapBits ASIDControlCap          = asidHighBits + word_size_bits"
| "acapBits (PageCap _ _ _ sz _)   = pageBitsForSize sz"
| "acapBits (PageTableCap x y) = 10"
| "acapBits (PageDirectoryCap x y) = 14"

definition page_table_at' :: "word32 \<Rightarrow> kernel_state \<Rightarrow> bool" where
 "page_table_at' x \<equiv> \<lambda>s. is_aligned x ptBits
                         \<and> (\<forall>y < 2 ^ 8. typ_at' (ArchT PTET) (x + (y << 2)) s)"

definition page_directory_at' :: "word32 \<Rightarrow> kernel_state \<Rightarrow> bool" where
 "page_directory_at' x \<equiv> \<lambda>s. is_aligned x pdBits
                             \<and> (\<forall>y < 2 ^ 12. typ_at' (ArchT PDET) (x + (y << 2)) s)"

lemmas vspace_table_at'_defs = page_table_at'_def page_directory_at'_def

abbreviation asid_pool_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "asid_pool_at' \<equiv> typ_at' (ArchT ASIDPoolT)"

(* FIXME: duplicated with vmsz_aligned *)
definition
  "vmsz_aligned' ref sz \<equiv> is_aligned ref (pageBitsForSize sz)"

definition valid_arch_cap' :: "arch_capability \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_cap' acap s \<equiv> case acap
   of ASIDPoolCap pool asid \<Rightarrow>
      typ_at' (ArchT ASIDPoolT) pool s \<and> is_aligned asid asid_low_bits \<and> asid \<le> 2^asid_bits - 1
    | ASIDControlCap \<Rightarrow> True
    | PageCap d ref rghts sz mapdata \<Rightarrow> ref \<noteq> 0 \<and>
      (\<forall>p < 2 ^ (pageBitsForSize sz - pageBits). typ_at' (if d then UserDataDeviceT else UserDataT)
      (ref + p * 2 ^ pageBits) s) \<and>
      (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow>
              0 < asid \<and> asid \<le> 2 ^ asid_bits - 1 \<and> vmsz_aligned' ref sz \<and> ref < pptrBase)
    | PageTableCap ref mapdata \<Rightarrow>
      page_table_at' ref s \<and>
      (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow>
              0 < asid \<and> asid \<le> 2^asid_bits - 1 \<and> ref < pptrBase)
    | PageDirectoryCap ref mapdata \<Rightarrow>
      page_directory_at' ref s \<and>
      case_option True (\<lambda>asid. 0 < asid \<and> asid \<le> 2^asid_bits - 1) mapdata"

lemmas valid_arch_cap'_simps[simp] =
  valid_arch_cap'_def[split_simps arch_capability.split, simplified]

definition valid_arch_tcb' :: "Structures_H.arch_tcb \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_tcb' \<equiv> \<lambda>t. \<top>"

definition valid_mapping' :: "word32 \<Rightarrow> vmpage_size \<Rightarrow> kernel_state \<Rightarrow> bool" where
 "valid_mapping' x sz s \<equiv> is_aligned x (pageBitsForSize sz)
                          \<and> ptrFromPAddr x \<noteq> 0"

primrec valid_pte' :: "ARM_H.pte \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_pte' (InvalidPTE) = \<top>"
| "valid_pte' (LargePagePTE ptr _ _ _ _) = (valid_mapping' ptr ARMLargePage)"
| "valid_pte' (SmallPagePTE ptr _ _ _ _) = (valid_mapping' ptr ARMSmallPage)"

primrec valid_pde' :: "ARM_H.pde \<Rightarrow> kernel_state \<Rightarrow> bool" where
 "valid_pde' (InvalidPDE) = \<top>"
| "valid_pde' (SectionPDE ptr _ _ _ _ _ _) = (valid_mapping' ptr ARMSection)"
| "valid_pde' (SuperSectionPDE ptr _ _ _ _ _) = (valid_mapping' ptr ARMSuperSection)"
| "valid_pde' (PageTablePDE ptr _ _) = (\<lambda>_. is_aligned ptr ptBits)"

primrec valid_asid_pool' :: "asidpool \<Rightarrow> kernel_state \<Rightarrow> bool" where
 "valid_asid_pool' (ASIDPool pool)
     = (\<lambda>s. dom pool \<subseteq> {0 .. 2^asid_low_bits - 1}
            \<and> 0 \<notin> ran pool \<and> (\<forall>x \<in> ran pool. is_aligned x pdBits))"

primrec valid_arch_obj' :: "arch_kernel_object \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_arch_obj' (KOASIDPool pool) = valid_asid_pool' pool"
| "valid_arch_obj' (KOPDE pde) = valid_pde' pde"
| "valid_arch_obj' (KOPTE pte) = valid_pte' pte"

primrec acapClass :: "arch_capability \<Rightarrow> capclass" where
  "acapClass (ASIDPoolCap x y)      = PhysicalClass"
| "acapClass ASIDControlCap         = ASIDMasterClass"
| "acapClass (PageCap d x y sz z)   = PhysicalClass"
| "acapClass (PageTableCap x y)     = PhysicalClass"
| "acapClass (PageDirectoryCap x y) = PhysicalClass"

definition isArchFrameCap :: "capability \<Rightarrow> bool" where
 "isArchFrameCap cap \<equiv> case cap of ArchObjectCap (PageCap _ _ _ _ _) \<Rightarrow> True | _ \<Rightarrow> False"

(* FIXME arch-split: compatibility shim, can be removed by arch-wide rename *)
abbreviation (input)
  "isArchPageCap \<equiv> isArchFrameCap"

lemmas isArchPageCap_def = isArchFrameCap_def

definition valid_arch_mdb_ctes :: "cte_heap \<Rightarrow> bool" where
  "valid_arch_mdb_ctes \<equiv> \<top>"

definition page_directory_refs' :: "word32 \<Rightarrow> word32 set" where
  "page_directory_refs' x \<equiv> (\<lambda>y. x + (y << 2)) ` {y. y < 2 ^ 12}"

(* Addresses of all PTEs in a VSRoot table at p *)
definition page_table_refs' :: "word32 \<Rightarrow> word32 set" where
  "page_table_refs' x \<equiv> (\<lambda>y. x + (y << 2)) ` {y. y < 2 ^ 8}"

definition global_refs' :: "kernel_state \<Rightarrow> obj_ref set" where
  "global_refs' \<equiv> \<lambda>s.
  {ksIdleThread s} \<union>
   page_directory_refs' (armKSGlobalPD (ksArchState s)) \<union>
   (\<Union>pt \<in> set (armKSGlobalPTs (ksArchState s)). page_table_refs' pt) \<union>
   range (\<lambda>irq :: irq. irq_node' s + (ucast irq << cteSizeBits))"

definition valid_asid_table' :: "(asid \<rightharpoonup> word32) \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_asid_table' table \<equiv> \<lambda>s. dom table \<subseteq> {0 .. 2^asid_high_bits - 1}
                                  \<and> 0 \<notin> ran table"

definition valid_global_pts' :: "word32 list \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_global_pts' pts \<equiv> \<lambda>s. \<forall>p \<in> set pts. page_table_at' p s"

definition valid_asid_map' :: "(word32 \<rightharpoonup> word8 \<times> word32) \<Rightarrow> bool" where
 "valid_asid_map' m \<equiv> inj_on (option_map snd o m) (dom m)
                          \<and> dom m \<subseteq> ({0 .. mask asid_bits} - {0})"

definition
  pd_asid_slot :: word32
where
 "pd_asid_slot \<equiv> 0xff0"

  (* ideally, all mappings above kernel_base are global and kernel-only, and
     of them one particular mapping is clear. at the moment all we can easily say
     is that the mapping is clear. *)
definition valid_pde_mapping_offset' :: "machine_word \<Rightarrow> bool" where
 "valid_pde_mapping_offset' offset \<equiv> offset \<noteq> pd_asid_slot * 4"

definition valid_pde_mapping' :: "word32 \<Rightarrow> pde \<Rightarrow> bool" where
 "valid_pde_mapping' offset pde \<equiv> pde = InvalidPDE \<or> valid_pde_mapping_offset' offset"

definition valid_pde_mappings' :: "kernel_state \<Rightarrow> bool" where
  "valid_pde_mappings' \<equiv> \<lambda>s.
     \<forall>x pde. ko_at' pde x s
          \<longrightarrow> valid_pde_mapping' (x && mask pdBits) pde"

definition valid_arch_state' :: "kernel_state \<Rightarrow> bool" where
  "valid_arch_state' \<equiv> \<lambda>s.
     valid_asid_table' (armKSASIDTable (ksArchState s)) s \<and>
     page_directory_at' (armKSGlobalPD (ksArchState s)) s \<and>
     valid_global_pts' (armKSGlobalPTs (ksArchState s)) s \<and>
     is_inv (armKSHWASIDTable (ksArchState s))
            (option_map fst o armKSASIDMap (ksArchState s)) \<and>
     valid_asid_map' (armKSASIDMap (ksArchState s)) \<and>
     valid_pde_mappings' s"

definition archMakeObjectT :: "arch_kernel_object_type \<Rightarrow> kernel_object" where
  "archMakeObjectT atp \<equiv>
     case atp
     of PDET \<Rightarrow> injectKO (makeObject :: pde)
      | PTET \<Rightarrow> injectKO (makeObject :: pte)
      | ASIDPoolT \<Rightarrow> injectKO (makeObject :: asidpool)"


section "Misc properties not directly included in invariants"

definition
  vs_ptr_align :: "Structures_H.kernel_object \<Rightarrow> nat" where
 "vs_ptr_align obj \<equiv>
  case obj of KOArch (KOPTE (pte.LargePagePTE _ _ _ _ _)) \<Rightarrow> 6
            | KOArch (KOPDE (pde.SuperSectionPDE _ _ _ _ _ _)) \<Rightarrow> 6
            | _ \<Rightarrow> 0"

definition "vs_valid_duplicates' \<equiv> \<lambda>h.
    \<forall>x y. case h x of None \<Rightarrow> True
         | Some ko \<Rightarrow> is_aligned y 2 \<longrightarrow>
              x && ~~ mask (vs_ptr_align ko) = y && ~~ mask (vs_ptr_align ko) \<longrightarrow>
              h x = h y"

end
end
