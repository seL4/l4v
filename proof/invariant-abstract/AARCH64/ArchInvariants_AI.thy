(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInvariants_AI
imports InvariantsPre_AI "Eisbach_Tools.Apply_Trace_Cmd"
begin

context Arch begin global_naming AARCH64

(* compatibility with other architectures, input only *)
abbreviation
  "vs_lookup s \<equiv> \<lambda>level asid vref. vs_lookup_table level asid vref s"

locale_abbrev
  "atyps_of \<equiv> \<lambda>s. aobjs_of s ||> aa_type"

end

\<comment> \<open>---------------------------------------------------------------------------\<close>

section "AARCH64-specific invariant definitions"

qualify AARCH64 (in Arch)
record iarch_tcb =
  itcb_vcpu :: "obj_ref option"
end_qualify

context Arch begin global_naming AARCH64

definition arch_tcb_to_iarch_tcb :: "arch_tcb \<Rightarrow> iarch_tcb" where
  "arch_tcb_to_iarch_tcb arch_tcb \<equiv> \<lparr> itcb_vcpu = tcb_vcpu arch_tcb \<rparr>"

(* Need one of these simp rules for each field in 'iarch_tcb' *)
lemma arch_tcb_to_iarch_tcb_simps[simp]:
  "itcb_vcpu (arch_tcb_to_iarch_tcb arch_tcb) = tcb_vcpu arch_tcb"
  by (auto simp: arch_tcb_to_iarch_tcb_def)

lemma iarch_tcb_context_set[simp]:
  "arch_tcb_to_iarch_tcb (arch_tcb_context_set p tcb) = arch_tcb_to_iarch_tcb tcb"
  by (auto simp: arch_tcb_context_set_def)

lemma iarch_tcb_set_registers[simp]:
  "arch_tcb_to_iarch_tcb (arch_tcb_set_registers regs arch_tcb) = arch_tcb_to_iarch_tcb arch_tcb"
  by (auto simp: arch_tcb_set_registers_def)

(* These simplifications allows us to keep many arch-specific proofs unchanged. *)
lemma arch_cap_fun_lift_expand[simp]:
  "arch_cap_fun_lift (\<lambda>ac. case ac of
                                ASIDPoolCap obj_ref asid \<Rightarrow> P_ASIDPoolCap obj_ref asid
                              | ASIDControlCap \<Rightarrow> P_ASIDControlCap
                              | FrameCap obj_ref rights sz dev vr \<Rightarrow> P_FrameCap obj_ref rights sz dev vr
                              | PageTableCap obj_ref pt_t vr \<Rightarrow> P_PageTableCap obj_ref pt_t vr
                              | VCPUCap obj_ref \<Rightarrow> P_VCPUCap obj_ref)
                      F = (\<lambda>c.
   case c of
      ArchObjectCap (ASIDPoolCap obj_ref asid) \<Rightarrow> P_ASIDPoolCap obj_ref asid
    | ArchObjectCap (ASIDControlCap) \<Rightarrow> P_ASIDControlCap
    | ArchObjectCap (FrameCap obj_ref rights sz dev vr) \<Rightarrow> P_FrameCap obj_ref rights sz dev vr
    | ArchObjectCap (PageTableCap obj_ref pt_t vr) \<Rightarrow> P_PageTableCap obj_ref pt_t vr
    | ArchObjectCap (VCPUCap obj_ref) \<Rightarrow> P_VCPUCap obj_ref
    | _ \<Rightarrow> F)"
  unfolding arch_cap_fun_lift_def by fastforce

lemma arch_cap_fun_lift_Some[simp]:
  "(arch_cap_fun_lift f None cap = Some x) = (\<exists>acap. cap = ArchObjectCap acap \<and> f acap = Some x)"
  by (cases cap; simp)

lemma arch_obj_fun_lift_expand[simp]:
  "arch_obj_fun_lift (\<lambda>ako. case ako of
                                ASIDPool pool \<Rightarrow> P_ASIDPool pool
                              | PageTable pt \<Rightarrow> P_PageTable pt
                              | DataPage dev s \<Rightarrow> P_DataPage dev s
                              | VCPU v \<Rightarrow> P_VCPU v)
                      F = (\<lambda>ko.
   case ko of
      ArchObj (ASIDPool pool) \<Rightarrow> P_ASIDPool pool
    | ArchObj (PageTable pt) \<Rightarrow> P_PageTable pt
    | ArchObj (DataPage dev s) \<Rightarrow> P_DataPage dev s
    | ArchObj (VCPU v) \<Rightarrow> P_VCPU v
    | _ \<Rightarrow> F)"
  unfolding arch_obj_fun_lift_def by fastforce

lemmas aa_type_simps[simp] = aa_type_def[split_simps arch_kernel_obj.split]
lemmas a_type_def = a_type_def[simplified aa_type_def]
lemmas a_type_simps[simp] = a_type_def[split_simps kernel_object.split arch_kernel_obj.split]

section "Virtual Memory Regions"

(* Number of significant bits for canonical addresses in kernel-virtual space *)
type_synonym canonical_len = 48

(* Consistency check *)
lemma "CARD(canonical_len) = canonical_bit + 1"
  by (simp add: canonical_bit_def)

(* Because hyp does not use sign-extension, we don't use canonical addresses with sign extension
   here, but we still need the concept of valid kernel-virtual addresses (pptr). Note that these
   are different to user-virtual addresses (IPAs for hyp). *)
definition canonical_address_of :: "canonical_len word \<Rightarrow> obj_ref" where
  "canonical_address_of x \<equiv> ucast x"

definition canonical_address :: "obj_ref \<Rightarrow> bool" where
  "canonical_address x \<equiv> canonical_address_of (ucast x) = x"

(* All mappable user addresses (for hyp these are IPA, not actual virtual addresses) -- see
   comment at definition of canonical_user *)
definition user_region :: "vspace_ref set" where
  "user_region = {vref. vref \<le> canonical_user}"

definition
  "in_device_frame p \<equiv> \<lambda>s.
     \<exists>sz. typ_at (AArch (ADeviceData sz)) (p && ~~ mask (pageBitsForSize sz)) s"

definition
  "user_mem s \<equiv> \<lambda>p.
     if in_user_frame p s then Some (underlying_memory (machine_state s) p) else None"

definition
  "device_mem s \<equiv> \<lambda>p. if in_device_frame p s then Some p else None"

(* These are user-mapped devices (as opposed to kernel-only device memory) *)
locale_abbrev
  "device_region s \<equiv> dom (device_state (machine_state s))"


definition kernel_window_2 :: "arm_vspace_region_uses \<Rightarrow> obj_ref set" where
  "kernel_window_2 uses \<equiv> {x. uses x = ArmVSpaceKernelWindow}"

locale_abbrev kernel_window :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "kernel_window s \<equiv> kernel_window_2 (arm_kernel_vspace (arch_state s))"

lemmas kernel_window_def = kernel_window_2_def

definition not_kernel_window_2 :: "arm_vspace_region_uses \<Rightarrow> obj_ref set" where
  "not_kernel_window_2 uses \<equiv> - kernel_window_2 uses"

locale_abbrev not_kernel_window :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "not_kernel_window s \<equiv> not_kernel_window_2 (arm_kernel_vspace (arch_state s))"

lemmas not_kernel_window_def = not_kernel_window_2_def

(* Virtual memory window containing kernel device mappings. *)
definition kernel_device_window_2 :: "arm_vspace_region_uses \<Rightarrow> obj_ref set" where
  "kernel_device_window_2 uses \<equiv> {x. uses x = ArmVSpaceDeviceWindow}"

locale_abbrev kernel_device_window :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "kernel_device_window s \<equiv> kernel_device_window_2 (arm_kernel_vspace (arch_state s))"

lemmas kernel_device_window_def = kernel_device_window_2_def

definition kernel_regions_2 :: "arm_vspace_region_uses \<Rightarrow> obj_ref set" where
  "kernel_regions_2 uses \<equiv>
     kernel_window_2 uses \<union> kernel_device_window_2 uses"

locale_abbrev kernel_regions :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "kernel_regions s \<equiv> kernel_regions_2 (arm_kernel_vspace (arch_state s))"

lemmas kernel_regions_def = kernel_regions_2_def

(* There is no user window on hyp, so we later demand that this set is empty *)
definition user_window_2 :: "arm_vspace_region_uses \<Rightarrow> obj_ref set" where
  "user_window_2 uses \<equiv> {x. uses x = ArmVSpaceUserRegion}"

locale_abbrev user_window :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "user_window s \<equiv> user_window_2 (arm_kernel_vspace (arch_state s))"

lemmas user_window_def = user_window_2_def


section "Wellformed Addresses and ASIDs"

(* Note: no alignment check as in other architectures, because we would need to know the PT level. *)
definition wellformed_mapdata :: "asid \<times> vspace_ref \<Rightarrow> bool" where
  "wellformed_mapdata \<equiv> \<lambda>(asid, vref). 0 < asid \<and> vref \<in> user_region"

definition vm_level_aligned :: "obj_ref \<Rightarrow> vm_level \<Rightarrow> bool" where
  "vm_level_aligned ref level \<equiv> is_aligned ref (pt_bits_left level)"

definition vmsz_aligned :: "obj_ref \<Rightarrow> vmpage_size \<Rightarrow> bool" where
  "vmsz_aligned ref sz \<equiv> is_aligned ref (pageBitsForSize sz)"

definition wellformed_acap :: "arch_cap \<Rightarrow> bool" where
  "wellformed_acap ac \<equiv>
   case ac of
     ASIDPoolCap r as \<Rightarrow> is_aligned as asid_low_bits
   | FrameCap r rghts sz dev  mapdata \<Rightarrow>
       rghts \<in> valid_vm_rights \<and>
       case_option True wellformed_mapdata mapdata \<and>
       case_option True (swp vmsz_aligned sz \<circ> snd) mapdata
   | PageTableCap r pt_t (Some mapdata) \<Rightarrow> wellformed_mapdata mapdata
   | _ \<Rightarrow> True"

lemmas wellformed_acap_simps[simp] = wellformed_acap_def[split_simps arch_cap.split]


section "Virtual Memory"

locale_abbrev
  "asid_pool_at \<equiv> typ_at (AArch AASIDPool)"

locale_abbrev
  "pt_at pt_t \<equiv> typ_at (AArch (APageTable pt_t))"

locale_abbrev
  "normal_pt_at \<equiv> pt_at NormalPT_T"

locale_abbrev
  "vspace_pt_at \<equiv> pt_at VSRootPT_T"

definition
  "pte_at pt_t p \<equiv> \<lambda>s. ptes_of s pt_t p \<noteq> None"

locale_abbrev
  "vcpu_at \<equiv> typ_at (AArch AVCPU)"

definition valid_arch_cap_ref :: "arch_cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_arch_cap_ref ac s \<equiv> case ac of
    ASIDPoolCap r as \<Rightarrow> asid_pool_at r s
  | ASIDControlCap \<Rightarrow> True
  | FrameCap r rghts sz dev mapdata \<Rightarrow>
      if dev then typ_at (AArch (ADeviceData sz)) r s
             else typ_at (AArch (AUserData sz)) r s
  | PageTableCap r pt_t mapdata \<Rightarrow> pt_at pt_t r s
  | VCPUCap r \<Rightarrow> vcpu_at r s"

lemmas valid_arch_cap_ref_simps[simp] =
  valid_arch_cap_ref_def[split_simps arch_cap.split]

definition valid_arch_cap :: "arch_cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_arch_cap cap \<equiv> \<lambda>s. wellformed_acap cap \<and> valid_arch_cap_ref cap s"

lemmas valid_arch_cap_simps =
  valid_arch_cap_def[unfolded wellformed_acap_def valid_arch_cap_ref_def,
                     split_simps arch_cap.split, simplified]
definition
  [simp]: "is_nondevice_page_cap_arch \<equiv> \<lambda>cap. is_FrameCap cap \<and> \<not> acap_is_device cap"

definition
  "is_nondevice_page_cap c \<equiv> arch_cap_fun_lift is_nondevice_page_cap_arch False c"

lemma is_nondevice_page_cap:
  "is_nondevice_page_cap c = (\<exists>p q r s t. c = ArchObjectCap (FrameCap p q s False t))"
  by (auto simp: is_nondevice_page_cap_def is_FrameCap_def split: cap.splits arch_cap.splits)

lemmas is_nondevice_page_cap_simps[simp] =
  is_nondevice_page_cap_def[unfolded arch_cap_fun_lift_def is_nondevice_page_cap_arch_def,
                            split_simps arch_cap.split cap.split]

primrec acap_class :: "arch_cap \<Rightarrow> capclass" where
  "acap_class (ASIDPoolCap _ _)     = PhysicalClass"
| "acap_class (ASIDControlCap)      = ASIDMasterClass"
| "acap_class (FrameCap _ _ _ _ _)  = PhysicalClass"
| "acap_class (PageTableCap _ _ _)  = PhysicalClass"
| "acap_class (VCPUCap _)           = PhysicalClass"

definition valid_ipc_buffer_cap_arch :: "arch_cap \<Rightarrow> machine_word \<Rightarrow> bool" where
  [simp]: "valid_ipc_buffer_cap_arch ac bufptr \<equiv>
             is_nondevice_page_cap_arch ac \<and> is_aligned bufptr msg_align_bits"

declare valid_ipc_buffer_cap_arch_def

definition
  "valid_ipc_buffer_cap c bufptr \<equiv>
     case c of
       NullCap \<Rightarrow> True
     | ArchObjectCap acap \<Rightarrow> valid_ipc_buffer_cap_arch acap bufptr
     | _ \<Rightarrow> False"

definition
  "data_at \<equiv> \<lambda>sz p s. typ_at (AArch (AUserData sz)) p s
                       \<or> typ_at (AArch (ADeviceData sz)) p s"

(* Regardless of PA/IPA space size or max_pt_level, the maximum level at which pages can be
   mapped is 2 on AArch64 *)
definition max_page_level :: vm_level where
   "max_page_level = 2"

(* Validity of vspace table entries, defined shallowly. *)
primrec valid_pte :: "vm_level \<Rightarrow> pte \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_pte _ (InvalidPTE) = \<top>"
| "valid_pte level (PagePTE base is_small _ _) =
     (\<lambda>s. data_at (vmsize_of_level level) (ptrFromPAddr base) s
          \<and> level \<le> max_page_level
          \<and> (is_small \<longleftrightarrow> level = 0))"
| "valid_pte level (PageTablePTE ppn) =
     (\<lambda>s. normal_pt_at (ptrFromPAddr (paddr_from_ppn ppn)) s \<and> 0 < level)"

definition pt_range :: "pt \<Rightarrow> pte set" where
  "pt_range pt \<equiv> range (pt_apply pt)"

fun valid_vspace_obj :: "vm_level \<Rightarrow> arch_kernel_obj \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_vspace_obj _ (ASIDPool pool) =
   (\<lambda>s. \<forall>x \<in> ran pool. vspace_pt_at (ap_vspace x) s)"
| "valid_vspace_obj level (PageTable pt) =
   (\<lambda>s. (\<forall>pte \<in> pt_range pt. valid_pte level pte s) \<and> pt_type pt = level_type level)"
| "valid_vspace_obj _ (DataPage _ _) = \<top>" (* already covered by valid_pte *)
| "valid_vspace_obj _ (VCPU _ ) = \<top>" (* not a vspace obj *)

definition vspace_obj_of :: "arch_kernel_obj \<Rightarrow> arch_kernel_obj option" where
  "vspace_obj_of ao \<equiv> if is_VCPU ao then None else Some ao"

locale_abbrev vspace_objs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> arch_kernel_obj option" where
  "vspace_objs_of \<equiv> \<lambda>s. aobjs_of s |> vspace_obj_of"

definition valid_vso_at :: "vm_level \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_vso_at level p \<equiv> \<lambda>s. \<exists>ao. vspace_objs_of s p = Some ao \<and> valid_vspace_obj level ao s"

definition wellformed_pte :: "pte \<Rightarrow> bool" where
  "wellformed_pte pte \<equiv> is_PagePTE pte \<longrightarrow> pte_rights pte \<in> valid_vm_rights"

definition valid_vcpu :: "vcpu \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_vcpu vcpu \<equiv> case_option \<top> (typ_at ATCB) (vcpu_tcb vcpu) "

(* Since the page tables may translate more bits than the IPA address space has, not all mapping
   slots in the top level table can be used. Slots with any of the top "pt_bits_left asid_pool_level
   - ipa_size" bits set correspond to mappings outside of the address space. *)
definition valid_vs_slot_bits :: nat where
  "valid_vs_slot_bits = ptTranslationBits VSRootPT_T - (pt_bits_left asid_pool_level - ipa_size)"

definition invalid_mapping_slots :: "vs_index set" where
  "invalid_mapping_slots \<equiv>
     if valid_vs_slot_bits = 0 then {} else -{idx. idx \<le> mask valid_vs_slot_bits}"

(* In some AArch64 configurations the page tables can theoretically translate more bits than
   are available in the input address space (e.g. 44-bit IPA width, 48 ptbit_bits_left for toplevel.
   We want those inaccessible pte slots in the pt_range to be set to Invalid so that we know there
   can be no junk translations in the table that are impossible on hardware. *)
definition valid_pt_range :: "pt \<Rightarrow> bool" where
  "valid_pt_range pt \<equiv>
    \<forall>vs. pt = VSRootPT vs \<longrightarrow> (\<forall>idx \<in> invalid_mapping_slots. vs idx = InvalidPTE)"

definition arch_valid_obj :: "arch_kernel_obj \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "arch_valid_obj ao s \<equiv> case ao of
     VCPU v \<Rightarrow> valid_vcpu v s
   | PageTable pt \<Rightarrow> valid_pt_range pt \<and> (\<forall>pte\<in>pt_range pt. wellformed_pte pte)
   | _ \<Rightarrow> True"

lemmas arch_valid_obj_simps[simp] = arch_valid_obj_def[split_simps arch_kernel_obj.split]

(* There are no kernel mappings in user tables in hyp *)
definition equal_kernel_mappings :: "'z::state_ext state \<Rightarrow> bool" where
  "equal_kernel_mappings \<equiv> \<top>"

definition pte_ref :: "pte \<Rightarrow> obj_ref option" where
  "pte_ref pte \<equiv> case pte of
    InvalidPTE \<Rightarrow> None
  | PagePTE _ _ _ _ \<Rightarrow> Some (pptr_from_pte pte)
  | PageTablePTE _ \<Rightarrow> Some (pptr_from_pte pte)"

lemmas pte_ref_simps[simp] = pte_ref_def[split_simps pte.split]

definition valid_vspace_objs :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_vspace_objs \<equiv> \<lambda>s.
     \<forall>bot_level asid vref level p ao.
       vs_lookup_table bot_level asid vref s = Some (level, p)
       \<longrightarrow> vref \<in> user_region
       \<longrightarrow> vspace_objs_of s p = Some ao
       \<longrightarrow> valid_vspace_obj level ao s"

(* Mask out the bits that will not be used for lookups down to specified level *)
definition vref_for_level :: "vspace_ref \<Rightarrow> vm_level \<Rightarrow> vspace_ref" where
  "vref_for_level vref level = vref && ~~mask (pt_bits_left level)"

(* Mask out asid_low_bits if a lookup only goes to asid_pool_level *)
definition asid_for_level :: "asid \<Rightarrow> vm_level \<Rightarrow> asid" where
  "asid_for_level asid level \<equiv>
     if level = asid_pool_level then asid && ~~mask asid_low_bits else asid"

locale_abbrev pte_refs_of :: "pt_type \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref option" where
  "pte_refs_of \<equiv> \<lambda>pt_t p s. (ptes_of s pt_t |> pte_ref) p"

(* vs_lookup_slot locates a slot at a given level,
   vs_lookup_target returns the object reference in that slot. *)
definition vs_lookup_target ::
  "vm_level \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> (vm_level \<times> obj_ref) option"
  where
  "vs_lookup_target bot_level asid vref \<equiv> do {
     (level, slot) \<leftarrow> vs_lookup_slot bot_level asid vref;
     ptr \<leftarrow> if level = asid_pool_level
            then vspace_for_pool slot asid \<circ> asid_pools_of
            else pte_refs_of level slot;
     oreturn (level, ptr)
  }"

(* compatibility with other architectures, input only *)
abbreviation
  "vs_lookup_pages s \<equiv> \<lambda>level asid vref. vs_lookup_target level asid vref s"

(* Walk page table until we get to a slot or run out of levels; return obj_ref in slot. *)
definition pt_lookup_target ::
  "vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> ptes_of \<Rightarrow> (vm_level \<times> obj_ref) option" where
  "pt_lookup_target bot_level pt_root vref \<equiv> do {
     (level, slot) \<leftarrow> pt_lookup_slot_from_level max_pt_level bot_level pt_root vref;
     pte \<leftarrow> oapply2 (level_type level) slot;
     p \<leftarrow> K $ pte_ref pte;
     oreturn (level, p)
   }"

(* Translate virtual into physical address by walking page tables.
   Relies on last level being a PagePTE, otherwise returns garbage. *)
definition translate_address :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> ptes_of \<Rightarrow> paddr option" where
  "translate_address pt_root vref = do {
     (level, p) \<leftarrow> pt_lookup_target 0 pt_root vref;
     oassert (is_aligned p (pt_bits_left level));
     let base = addrFromPPtr p;
     let offset = vref && mask (pt_bits_left level);
     oreturn $ base + offset
  }"

definition vs_cap_ref_arch :: "arch_cap \<Rightarrow> (asid \<times> vspace_ref) option" where
  "vs_cap_ref_arch acap \<equiv> case acap of
                            ASIDPoolCap _ asid \<Rightarrow> Some (asid, 0)
                          | ASIDControlCap \<Rightarrow> None
                          | VCPUCap _ \<Rightarrow> None
                          \<comment> \<open>Cover all PageTableCaps/FrameCaps\<close>
                          | _ \<Rightarrow> acap_map_data acap"

lemmas vs_cap_ref_arch_simps[simp] = vs_cap_ref_arch_def [split_simps arch_cap.split]

definition vs_cap_ref :: "cap \<Rightarrow> (asid \<times> vspace_ref) option" where
  "vs_cap_ref cap \<equiv> arch_cap_fun_lift vs_cap_ref_arch None cap"

(* Needed for retype: vs objects that are reachable must have a cap to them.
   Strengthened for preservation in cap delete: ref in cap must unmap the right objects. *)
definition valid_vs_lookup :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_vs_lookup \<equiv> \<lambda>s. \<forall>bot_level level asid vref p.
     vs_lookup_target bot_level asid vref s = Some (level, p) \<longrightarrow>
     vref \<in> user_region \<longrightarrow>
       asid \<noteq> 0 \<and>
       (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                 obj_refs cap = {p} \<and>
                 vs_cap_ref cap = Some (asid, vref_for_level vref level))"

definition valid_asid_pool_caps_2 :: "(cslot_ptr \<rightharpoonup> cap) \<Rightarrow> (asid_high_index \<rightharpoonup> obj_ref) \<Rightarrow> bool"
  where
  "valid_asid_pool_caps_2 caps table \<equiv>
     \<forall>asid p. table asid = Some p \<longrightarrow>
                (\<exists>cptr cap. caps cptr = Some cap \<and>
                            obj_refs cap = {p} \<and>
                            vs_cap_ref cap = Some (ucast asid << asid_low_bits, 0))"

locale_abbrev valid_asid_pool_caps :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_asid_pool_caps \<equiv> \<lambda>s.
     valid_asid_pool_caps_2 (caps_of_state s) (asid_table s)"

lemmas valid_asid_pool_caps_def = valid_asid_pool_caps_2_def

definition empty_pt :: "pt_type \<Rightarrow> pt" where
  "empty_pt pt_t \<equiv> if pt_t = VSRootPT_T then VSRootPT (\<lambda>_. InvalidPTE) else NormalPT (\<lambda>_. InvalidPTE)"

definition valid_table_caps_2 :: "(cslot_ptr \<rightharpoonup> cap) \<Rightarrow> (obj_ref \<rightharpoonup> pt) \<Rightarrow> bool" where
  "valid_table_caps_2 caps pts \<equiv>
   \<forall>r pt_t p. caps p = Some (ArchObjectCap (PageTableCap r pt_t None)) \<longrightarrow>
              pts r = Some (empty_pt pt_t)"

locale_abbrev valid_table_caps :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_table_caps \<equiv> \<lambda>s. valid_table_caps_2 (caps_of_state s) (pts_of s)"

lemmas valid_table_caps_def = valid_table_caps_2_def

definition is_pt_cap :: "cap \<Rightarrow> bool" where
  "is_pt_cap cap \<equiv> arch_cap_fun_lift is_PageTableCap False cap"

definition is_vsroot_cap :: "cap \<Rightarrow> bool" where
  "is_vsroot_cap cap \<equiv>
    arch_cap_fun_lift (\<lambda>acap. is_PageTableCap acap \<and> acap_pt_type acap = VSRootPT_T) False cap"

(* No two PT caps with vs_cap_ref = None may point to the same object, i.e.
   copies of unmapped caps cannot exist. *)
definition unique_table_caps_2 :: "(cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool" where
  "unique_table_caps_2 \<equiv> \<lambda>cs. \<forall>p p' cap cap'.
     cs p = Some cap \<longrightarrow> cs p' = Some cap' \<longrightarrow>
     is_pt_cap cap \<longrightarrow> is_pt_cap cap' \<longrightarrow>
     vs_cap_ref cap = None \<longrightarrow>
     obj_refs cap' = obj_refs cap \<longrightarrow>
     p' = p"

locale_abbrev unique_table_caps :: "'z::state_ext state \<Rightarrow> bool" where
  "unique_table_caps \<equiv> \<lambda>s. unique_table_caps_2 (caps_of_state s)"

lemmas unique_table_caps_def = unique_table_caps_2_def

definition table_cap_ref_arch :: "arch_cap \<Rightarrow> (asid \<times> vspace_ref) option" where
  "table_cap_ref_arch acap \<equiv>
     case acap of
       ASIDPoolCap _ asid \<Rightarrow> Some (asid, 0)
     | PageTableCap _ _ mapdata \<Rightarrow> mapdata
     | _ \<Rightarrow> None"

lemmas table_cap_ref_arch_simps[simp] = table_cap_ref_arch_def[split_simps arch_cap.split]

definition table_cap_ref :: "cap \<Rightarrow> (asid \<times> vspace_ref) option" where
  "table_cap_ref cap = arch_cap_fun_lift table_cap_ref_arch None cap"

(* ASID pool caps and PT caps pointing to the same object must agree on the lookup
   path to that object *)
definition unique_table_refs_2 :: "(cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool" where
  "unique_table_refs_2 \<equiv> \<lambda>cs. \<forall>p p' cap cap'.
     cs p = Some cap \<longrightarrow> cs p' = Some cap' \<longrightarrow>
     obj_refs cap' = obj_refs cap \<longrightarrow>
     table_cap_ref cap' = table_cap_ref cap"

locale_abbrev unique_table_refs :: "'z::state_ext state \<Rightarrow> bool" where
  "unique_table_refs \<equiv> \<lambda>s. unique_table_refs_2 (caps_of_state s)"

lemmas unique_table_refs_def = unique_table_refs_2_def

definition valid_arch_caps :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_arch_caps \<equiv>
     valid_vs_lookup and valid_asid_pool_caps and valid_table_caps
     and unique_table_caps and unique_table_refs"

definition arch_live :: "arch_kernel_obj \<Rightarrow> bool" where
  "arch_live ao \<equiv> case ao of VCPU v \<Rightarrow> bound (vcpu_tcb v) | _ \<Rightarrow>  False"

definition hyp_live :: "kernel_object \<Rightarrow> bool" where
  "hyp_live ko \<equiv> case ko of
     TCB tcb \<Rightarrow> bound (tcb_vcpu (tcb_arch tcb))
   | ArchObj ao \<Rightarrow> arch_live ao
   |  _ \<Rightarrow> False"

(* The TCB link pointers of VCPUs *)
locale_abbrev vcpu_tcbs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> obj_ref option" where
  "vcpu_tcbs_of \<equiv> \<lambda>s. vcpus_of s |> vcpu_tcb"

(* If the TCB link exists, the VCPU is live *)
locale_abbrev vcpu_hyp_live_of :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "vcpu_hyp_live_of \<equiv> \<lambda>s. (\<lambda>_. True) |< vcpu_tcbs_of s"

definition cur_vcpu_2 :: "(obj_ref \<times> bool) option \<Rightarrow> (obj_ref \<Rightarrow> bool) \<Rightarrow> bool" where
  "cur_vcpu_2 \<equiv> \<lambda>cur_vcpu vcpu_hyp_live_of.
     case cur_vcpu of
       Some (v, _) \<Rightarrow> vcpu_hyp_live_of v
     | None \<Rightarrow> True"

locale_abbrev cur_vcpu :: "'z::state_ext state \<Rightarrow> bool" where
  "cur_vcpu \<equiv> \<lambda>s. cur_vcpu_2 (arm_current_vcpu (arch_state s)) (vcpu_hyp_live_of s)"

lemmas cur_vcpu_def = cur_vcpu_2_def

definition pte_rights_of :: "pte \<Rightarrow> rights set" where
  "pte_rights_of pte \<equiv> if is_PagePTE pte then pte_rights pte else {}"

definition global_refs :: "'z::state_ext state \<Rightarrow> obj_ref set" where
  "global_refs \<equiv> \<lambda>s.
     {idle_thread s, arm_us_global_vspace (arch_state s)} \<union>
     range (interrupt_irq_node s)"

definition valid_asid_table_2 :: "(asid_high_index \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> asid_pool) \<Rightarrow> bool"
  where
  "valid_asid_table_2 table pools \<equiv> ran table \<subseteq> dom pools \<and> inj_on table (dom table)"

locale_abbrev valid_asid_table :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_asid_table \<equiv> \<lambda>s. valid_asid_table_2 (asid_table s) (asid_pools_of s)"

lemmas valid_asid_table_def = valid_asid_table_2_def

definition arch_obj_bits_type :: "aa_type \<Rightarrow> nat" where
  "arch_obj_bits_type T \<equiv> case T of
     AASIDPool       \<Rightarrow> arch_kobj_size (ASIDPool undefined)
   | APageTable pt_t \<Rightarrow> arch_kobj_size (PageTable (if pt_t = VSRootPT_T
                                                   then VSRootPT undefined
                                                   else NormalPT undefined))
   | AUserData sz    \<Rightarrow> arch_kobj_size (DataPage False sz)
   | ADeviceData sz  \<Rightarrow> arch_kobj_size (DataPage True sz)
   | AVCPU           \<Rightarrow> arch_kobj_size (VCPU undefined)"

(* AArch64+hyp has a separate static kernel page table tree that is not modelled here and never
   accessed after init. On hyp the kernel lives in a separate address space that uses a separate MMU.
   For non-hyp, seL4 currently shares the address space with the user, but there exists an option
   to use a separate MMU to obtain the same model as on hyp. If we wanted to model non-hyp seL4 in
   the future, we would likely use that option. *)
definition valid_global_vspace_mappings :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_global_vspace_mappings \<equiv> \<top>"

locale_abbrev obj_addrs :: "kernel_object \<Rightarrow> obj_ref \<Rightarrow> obj_ref set" where
  "obj_addrs ko p \<equiv> {p .. p + 2 ^ obj_bits ko - 1}"

(* Objects live in the kernel window *)
definition pspace_in_kernel_window :: "'z::state_ext state \<Rightarrow> bool" where
  "pspace_in_kernel_window \<equiv> \<lambda>s. \<forall>p ko. kheap s p = Some ko \<longrightarrow> obj_addrs ko p \<subseteq> kernel_window s"

definition vspace_at_asid :: "asid \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "vspace_at_asid asid pt \<equiv> \<lambda>s. vspace_for_asid asid s = Some pt"

definition kernel_window_range :: "obj_ref set" where
  "kernel_window_range \<equiv> {pptr_base ..< pptrTop}"

definition valid_uses_2 :: "arm_vspace_region_uses \<Rightarrow> bool" where
  "valid_uses_2 uses \<equiv>
     \<forall>p. (\<not>canonical_address p \<longrightarrow> uses p = ArmVSpaceInvalidRegion)
          \<and> (p \<in> kernel_window_range
             \<longrightarrow> uses p \<in> {ArmVSpaceKernelWindow, ArmVSpaceInvalidRegion})
          \<and> (uses p = ArmVSpaceKernelWindow \<longrightarrow> p \<in> kernel_window_range)
          \<comment> \<open>The kernel device window doesn't occupy the entire region above kdev_base\<close>
          \<and> (kdev_base \<le> p \<longrightarrow> uses p \<in> {ArmVSpaceDeviceWindow, ArmVSpaceInvalidRegion})
          \<comment> \<open>No user window in hyp kernel address space\<close>
          \<and> (user_window_2 uses = {})
      \<comment> \<open>We want the kernel window to be non-empty, and to contain at least @{const pptr_base}\<close>
      \<and> uses pptr_base = ArmVSpaceKernelWindow"

locale_abbrev valid_uses :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_uses \<equiv> \<lambda>s. valid_uses_2 (arm_kernel_vspace (arch_state s))"

lemmas valid_uses_def = valid_uses_2_def

definition vmid_for_asid_2 ::
  "asid \<Rightarrow> (asid_high_index \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> asid_pool, vmid) lookup" where
  "vmid_for_asid_2 asid table \<equiv> do {
     ap_ptr \<leftarrow> K $ table (asid_high_bits_of asid);
     entry_for_pool ap_ptr asid |> ap_vmid
   }"

locale_abbrev vmid_for_asid :: "'z::state_ext state \<Rightarrow> asid \<rightharpoonup> vmid" where
  "vmid_for_asid \<equiv> \<lambda>s asid. vmid_for_asid_2 asid (asid_table s) (asid_pools_of s)"

lemmas vmid_for_asid_def = vmid_for_asid_2_def

(* For name preservation with older proofs *)
abbreviation (input) asid_map :: "'z::state_ext state \<Rightarrow> asid \<rightharpoonup> vmid" where
  "asid_map \<equiv> vmid_for_asid"

locale_abbrev
  "vmid_table s \<equiv> arm_vmid_table (arch_state s)"

(* vmIDs stored in ASID pools form the inverse of the vmid_table *)
definition vmid_inv :: "'z::state_ext state \<Rightarrow> bool" where
  "vmid_inv s \<equiv> is_inv (vmid_table s) (vmid_for_asid s)"

(* The vmID table never stores ASID 0 *)
definition valid_vmid_table_2 :: "(vmid \<rightharpoonup> asid) \<Rightarrow> bool" where
  "valid_vmid_table_2 table \<equiv> \<forall>vmid. table vmid \<noteq> Some 0"

locale_abbrev valid_vmid_table :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_vmid_table s \<equiv> valid_vmid_table_2 (vmid_table s)"

lemmas valid_vmid_table_def = valid_vmid_table_2_def

definition valid_global_arch_objs where
  "valid_global_arch_objs \<equiv> \<lambda>s. vspace_pt_at (global_pt s) s"

(* global_pt is the empty default user-level vspace, corresponding to armKSGlobalUserVSpace in C.
   On HYP platforms, the kernel has its own separate page table.
   We need to know that the user-level table is empty so we can derive that user-level lookups
   fail when there is no other vspace set. *)
definition valid_global_tables_2 :: "(obj_ref \<Rightarrow> pt option) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "valid_global_tables_2 \<equiv> \<lambda>pts global. pts global = Some (empty_pt VSRootPT_T)"

locale_abbrev valid_global_tables :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_global_tables \<equiv> \<lambda>s. valid_global_tables_2 (pts_of s) (global_pt s)"

lemmas valid_global_tables_def = valid_global_tables_2_def

definition valid_arch_state :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_arch_state \<equiv> valid_asid_table and valid_uses and vmid_inv and valid_vmid_table and
                      cur_vcpu and valid_global_arch_objs and valid_global_tables"

(* ---------------------------------------------------------------------------------------------- *)

(* Interface definitions, needed to define concepts needed in generic theories, but not
   necessarily in AARCH64 *)

definition valid_arch_tcb :: "arch_tcb \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_arch_tcb \<equiv> \<lambda>t s. \<forall>v. tcb_vcpu t = Some v \<longrightarrow> vcpu_at v s"

definition valid_arch_idle :: "iarch_tcb \<Rightarrow> bool" where
  "valid_arch_idle t \<equiv> itcb_vcpu t = None"

definition
  "valid_arch_mdb r cs \<equiv> True"

(* not needed for hyp mode *)
definition
  "valid_kernel_mappings \<equiv> \<top>"

(* tcb_arch_ref extracts the obj_refs in tcb_arch; currently only vcpu *)
definition tcb_arch_ref :: "tcb \<Rightarrow> obj_ref option" where
  "tcb_arch_ref t \<equiv> tcb_vcpu (tcb_arch t)"

definition
  tcb_vcpu_refs :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_vcpu_refs atcb \<equiv> case atcb of Some vc \<Rightarrow> {(vc, TCBHypRef)} | None \<Rightarrow> {}"

definition vcpu_tcb_refs :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set" where
  "vcpu_tcb_refs t \<equiv> case t of Some tcb \<Rightarrow> {(tcb, HypTCBRef)} | None \<Rightarrow> {}"

definition tcb_hyp_refs :: "arch_tcb \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_hyp_refs atcb \<equiv> tcb_vcpu_refs (tcb_vcpu atcb)"

definition refs_of_ao :: "arch_kernel_obj \<Rightarrow> (obj_ref \<times> reftype) set" where
  "refs_of_ao ako \<equiv> case ako of
     VCPU v \<Rightarrow> vcpu_tcb_refs (vcpu_tcb v)
   | _ \<Rightarrow> {}"

lemmas refs_of_ao_simps[simp] = refs_of_ao_def[split_simps arch_kernel_obj.split]

(* FIXME: move to generic *)
definition hyp_refs_of :: "kernel_object \<Rightarrow> (obj_ref \<times> reftype) set" where
  "hyp_refs_of x \<equiv> case x of
                     CNode sz fun      \<Rightarrow> {}
                   | TCB tcb           \<Rightarrow> tcb_hyp_refs (tcb_arch tcb)
                   | Endpoint ep       \<Rightarrow> {}
                   | Notification ntfn \<Rightarrow> {}
                   | ArchObj ao        \<Rightarrow> refs_of_ao ao"

lemmas hyp_refs_of_simps[simp] = hyp_refs_of_def[split_simps kernel_object.split]

definition state_hyp_refs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set" where
  "state_hyp_refs_of \<equiv> \<lambda>s p. case_option {} (hyp_refs_of) (kheap s p)"


(* Mostly covered by ASIDPool case of valid_vspace_obj and vmid_inv, but we still need to make sure
   that ASID 0 is never mapped. *)
definition valid_asid_map :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_asid_map \<equiv> \<lambda>s. entry_for_asid 0 s = None"

definition valid_global_objs :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_global_objs \<equiv> \<top>"

definition valid_ioports :: "'z::state_ext state \<Rightarrow> bool" where
  [simp]: "valid_ioports \<equiv> \<top>"


(* This definition is needed as interface for other architectures only.
   In other architectures, S is a set of object references (to global tables) that
   top-level tables may contain. In AARCH64, these table are completely empty *)
definition empty_table_arch :: "obj_ref set \<Rightarrow> arch_kernel_obj \<Rightarrow> bool" where
  "empty_table_arch S \<equiv>
     \<lambda>ko. case ko of PageTable (VSRootPT pt) \<Rightarrow> pt = (\<lambda>_. InvalidPTE) | _ \<Rightarrow> False"

declare empty_table_arch_def[simp]

(* Interface definition, see above *)
definition empty_table :: "obj_ref set \<Rightarrow> kernel_object \<Rightarrow> bool" where
  "empty_table S \<equiv> arch_obj_fun_lift (empty_table_arch S) False"


(* Interface definition, it provides the set (in form of a list) that is
   plugged into empty_table for other architectures, but is unused in AARCH64. *)
definition second_level_tables :: "arch_state \<Rightarrow> obj_ref list" where
  "second_level_tables s = []"

definition
  "cap_asid_arch cap \<equiv> case cap of
    FrameCap _ _ _ _ (Some (asid, _)) \<Rightarrow> Some asid
  | PageTableCap _ _ (Some (asid, _)) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

declare cap_asid_arch_def[abs_def, simp]

definition
  "cap_asid = arch_cap_fun_lift cap_asid_arch None"

(* ---------------------------------------------------------------------------------------------- *)

section "Canonical Addresses"

lemma canonical_address_range:
  "canonical_address x = (x \<le> mask (canonical_bit + 1))"
  by (simp add: canonical_address_def canonical_address_of_def ucast_ucast_mask
                and_mask_eq_iff_le_mask canonical_bit_def)

(* ---------------------------------------------------------------------------------------------- *)

section "Machine Bits and VM Levels"

lemma table_size:
  "table_size pt_t = (if pt_t = VSRootPT_T \<and> config_ARM_PA_SIZE_BITS_40 then 13 else 12)"
  by (simp add: table_size_def ptTranslationBits_def word_size_bits_def pte_bits_def)

bundle machine_bit_simps =
  table_size_def[simp] word_size_bits_def[simp]
  ptTranslationBits_def[simp] pageBits_def[simp]
  pte_bits_def[simp] vcpuBits_def[simp]

context
  includes machine_bit_simps
begin

lemmas simple_bit_simps =
  table_size word_size_bits_def ptTranslationBits_def pageBits_def vcpuBits_def
lemmas table_bits_simps =
  pt_bits_def[simplified] pte_bits_def[unfolded word_size_bits_def] vs_index_bits_def

named_theorems bit_simps

lemmas [bit_simps] = table_bits_simps simple_bit_simps ipa_size_def valid_vs_slot_bits_def

end

lemmas pageBitsForSize_simps[simp] = pageBitsForSize_def[split_simps vmpage_size.split]

lemma pageBitsForSize_bounded[simp,intro!]:
  "pageBitsForSize sz < word_bits"
  including machine_bit_simps by (cases sz; simp add: word_bits_def)

lemma table_size_bounded[simp,intro!]:
  "table_size vs < word_bits"
  including machine_bit_simps by (simp add: word_bits_def)

lemma vcpuBits_bounded[simp,intro!]:
  "vcpuBits < word_bits"
  including machine_bit_simps by (simp add: word_bits_def)

lemma ptTranslationBits_le_machine_word[simplified, simp]:
  "ptTranslationBits pt_t < LENGTH(machine_word_len)"
  by (simp add: bit_simps)

lemma pte_bits_leq_table_size[simp]:
  "pte_bits \<le> table_size pt_t"
  by (simp add: table_size_def)

(* with asid_pool_level normalised to -1, max_pt_level otherwise becomes -2 *)
lemma max_pt_level_def2: "max_pt_level = (if config_ARM_PA_SIZE_BITS_40 then 2 else 3)"
  by (simp add: max_pt_level_def asid_pool_level_def Kernel_Config.config_ARM_PA_SIZE_BITS_40_def)

lemmas level_defs = asid_pool_level_def max_pt_level_def2 max_page_level_def

lemma max_pt_level_gt0[simp]:
  "0 < max_pt_level"
  by (simp add: level_defs)

lemma max_pt_level_enum:
  "level \<le> max_pt_level \<Longrightarrow> if config_ARM_PA_SIZE_BITS_40 then level \<in> {0,1,2} else level \<in> {0,1,2,3}"
  unfolding level_defs Kernel_Config.config_ARM_PA_SIZE_BITS_40_def
  by (cases level rule: vm_level.of_nat_cases) (case_tac m; simp; rename_tac m)+

lemma max_page_level_enum:
  "level \<le> max_page_level \<Longrightarrow> level \<in> {0,1,2}"
  unfolding level_defs
  by (cases level rule: vm_level.of_nat_cases) (case_tac m; simp; rename_tac m)+

lemma asid_pool_level_size:
  "size asid_pool_level = (if config_ARM_PA_SIZE_BITS_40 then 3 else 4)"
proof -
  have m1: "(-1::vm_level) = (if config_ARM_PA_SIZE_BITS_40 then 3 else 4)"
    by (simp add: Kernel_Config.config_ARM_PA_SIZE_BITS_40_def)
  show ?thesis unfolding asid_pool_level_def
   by (simp add: m1)
qed

lemma asid_pool_level_not_0[simp]:
  "asid_pool_level \<noteq> 0"
  by (simp add: asid_pool_level_def)

lemma vm_level_not_less_zero:
  fixes level :: vm_level
  shows "level \<noteq> 0 \<Longrightarrow> level > 0"
  using vm_level.not_less_zero_bit0 neqE by blast

lemma asid_pool_level_neq[simp]:
  "(x \<noteq> asid_pool_level) = (x \<le> max_pt_level)"
proof
  assume "x \<noteq> asid_pool_level"
  hence "x < asid_pool_level"
    unfolding asid_pool_level_def by simp
  thus "x \<le> max_pt_level"
    by (simp add: max_pt_level_def vm_level.leq_minus1_less)
next
  note maxBound_minus_one_bit[simp del]
  assume "x \<le> max_pt_level"
  thus "x \<noteq> asid_pool_level"
    unfolding level_defs by (auto simp: maxBound_size_bit split: if_splits)
qed

lemma asid_pool_level_eq:
  "(x = asid_pool_level) = (\<not> (x \<le> max_pt_level))"
  by (simp flip: asid_pool_level_neq)

lemmas leq_max_pt_level = asid_pool_level_neq[THEN iffD2]

lemma max_pt_level_not_0[simp]:
  "max_pt_level \<noteq> 0"
  by (simp add: max_pt_level_def asid_pool_level_def)

lemma asid_pool_level_max[simp,intro!]:
  "level \<le> asid_pool_level"
  unfolding asid_pool_level_def by simp

lemma asid_pool_level_not_less[simp]:
  "\<not> asid_pool_level < level"
  by (simp add: not_less)

lemma vm_level_less_max_pt_level:
  "((level' :: vm_level) < level) \<Longrightarrow> level' \<le> max_pt_level"
  using asid_pool_level_neq asid_pool_level_not_less by blast

lemma vm_level_less_le_1:
  "\<lbrakk> (level' :: vm_level) < level \<rbrakk> \<Longrightarrow> level' \<le> level' + 1"
  by (fastforce dest: max_pt_level_enum vm_level_less_max_pt_level split: if_split_asm)

lemma asid_pool_level_leq_conv[iff]:
  "(asid_pool_level \<le> level) = (level = asid_pool_level)"
  by (simp add: asid_pool_level_def)

lemma max_pt_level_less_conv[iff]:
  "(max_pt_level < level) = (level = asid_pool_level)"
  using max_pt_level_def not_le by force

lemma max_pt_level_not_asid_pool_level[simp]:
  "max_pt_level \<noteq> asid_pool_level"
  "asid_pool_level \<noteq> max_pt_level"
  by (simp add: asid_pool_level_def)
     (simp add: level_defs)

lemma asid_pool_level_minus:
  "asid_pool_level = -1"
  by (simp add: asid_pool_level_def)

lemma max_pt_level_plus_one:
  "max_pt_level + 1 = asid_pool_level"
  by (simp add: max_pt_level_def)

lemma max_pt_level_less_Suc[iff]:
  "(level < level + 1) = (level \<le> max_pt_level)"
  apply (simp add: vm_level.no_overflow_eq_max_bound max_pt_level_def flip: asid_pool_level_minus)
  by (metis asid_pool_level_max asid_pool_level_neq max_pt_level_def antisym_conv2)

lemma size_level1[simp]:
  "(size level = Suc 0) = (level = (1 :: vm_level))"
proof
  assume "size level = Suc 0"
  hence "size level = size (1::vm_level)" by simp
  thus "level = 1" by (subst (asm) vm_level.size_inj)
qed auto

lemma minus_one_max_pt_level[simp]:
  "(level - 1 = max_pt_level) = (level = asid_pool_level)"
  by (simp add: max_pt_level_def)

lemmas max_pt_level_eq_minus_one = minus_one_max_pt_level[THEN iffD1]

lemma plus_one_eq_asid_pool:
  "(level + 1 = asid_pool_level) = (level = max_pt_level)"
  by (metis add_right_imp_eq max_pt_level_plus_one)

lemma max_inc_pt_level[simp]:
  "level \<le> max_pt_level \<Longrightarrow> max (level + 1) level = level + 1"
  by (simp add: dual_order.strict_implies_order max.commute max_def)

lemma vm_level_le_plus_1_mono:
  "\<lbrakk>level' \<le> level; level \<le> max_pt_level \<rbrakk> \<Longrightarrow> level' + 1 \<le> level + 1"
  by (simp add: vm_level.plus_one_leq le_less_trans)

lemma vm_level_less_plus_1_mono:
  "\<lbrakk> level' < level; level \<le> max_pt_level \<rbrakk> \<Longrightarrow> level' + 1 < level + 1"
  by (simp add: vm_level_le_plus_1_mono dual_order.strict_iff_order)

lemma level_minus_one_max_pt_level[iff]:
  "(level - 1 \<le> max_pt_level) = (0 < level)"
  by (metis max_pt_level_less_Suc vm_level.not_less_zero_bit0 vm_level.pred diff_add_cancel
           not_less_iff_gr_or_eq)

(* Sometimes you need type nat directly in the goal, not vm_level *)
lemma size_max_pt_level:
  "size max_pt_level = (if config_ARM_PA_SIZE_BITS_40 then 2 else 3)"
  by (simp add: level_defs)

lemma pt_bits_left_asid_pool[bit_simps]:
  "pt_bits_left asid_pool_level = (if config_ARM_PA_SIZE_BITS_40 then 40 else 48)"
  by (simp add: pt_bits_left_def bit_simps size_max_pt_level)

(* ---------------------------------------------------------------------------------------------- *)

section \<open>Basic Properties\<close>

lemma not_is_VSRootPT[simp]:
  "(\<forall>x. pt \<noteq> VSRootPT x) = (\<exists>npt. pt = NormalPT npt)"
  by (cases pt; simp)

lemma valid_table_caps_pdD:
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PageTableCap pt pt_t None)); valid_table_caps s \<rbrakk>
  \<Longrightarrow> pts_of s pt = Some (empty_pt pt_t)"
  by (auto simp add: valid_table_caps_def simp del: split_paired_Ex)

lemma addrFromPPtr_ptrFromPAddr_id[simp]:
  "addrFromPPtr (ptrFromPAddr x) = x"
  by (simp add: addrFromPPtr_def ptrFromPAddr_def)

lemma global_refs_asid_table_update [iff]:
  "global_refs (s\<lparr>arch_state := arm_asid_table_update f (arch_state s)\<rparr>) = global_refs s"
  by (simp add: global_refs_def)

lemma pspace_in_kernel_window_arch_update[simp]:
  "arm_kernel_vspace (f (arch_state s)) = arm_kernel_vspace (arch_state s)
     \<Longrightarrow> pspace_in_kernel_window (arch_state_update f s) = pspace_in_kernel_window s"
  by (simp add: pspace_in_kernel_window_def)

lemmas vs_cap_ref_simps[simp] =
         vs_cap_ref_def [simplified vs_cap_ref_arch_def[abs_def] arch_cap_fun_lift_def[abs_def],
                         split_simps cap.split arch_cap.split vmpage_size.split]

lemmas table_cap_ref_simps[simp] =
         table_cap_ref_def [simplified table_cap_ref_arch_def[abs_def] arch_cap_fun_lift_def[abs_def],
                            split_simps cap.split arch_cap.split]

lemmas is_pt_cap_simps [simp] =
         is_pt_cap_def [simplified arch_cap_fun_lift_def[abs_def],
                        split_simps cap.split arch_cap.split]

lemma is_pt_cap_eq:
  "is_pt_cap cap = (\<exists>p pt_t m. cap = ArchObjectCap (PageTableCap p pt_t m))"
  by (auto simp: is_pt_cap_def is_PageTableCap_def)

lemma vs_cap_ref_table_cap_ref_eq:
  "is_pt_cap cap \<Longrightarrow> vs_cap_ref cap = table_cap_ref cap"
  by (cases cap; simp) (rename_tac acap, case_tac acap; simp)

lemma wellformed_arch_pspace:
  "\<lbrakk>arch_valid_obj ao s; kheap s = kheap s'\<rbrakk> \<Longrightarrow> arch_valid_obj ao s'"
  by (cases ao; simp add: arch_valid_obj_def valid_vcpu_def obj_at_def split: option.splits)

lemma pageBitsForSize_pt_bits_left:
  "pageBitsForSize sz = pt_bits_left (level_of_vmsize sz)"
  by (cases sz; simp add: level_of_vmsize_def pt_bits_left_def pageBitsForSize_def asid_pool_level_def)

lemma asid_low_bits_of_mask_eq:
  "ucast (asid_low_bits_of asid) = asid && mask asid_low_bits"
  by (simp add: asid_bits_defs asid_bits_of_defs ucast_ucast_mask)

lemmas asid_low_bits_of_p2m1_eq =
  asid_low_bits_of_mask_eq[simplified mask_2pm1]

lemma arch_kobj_size_bounded[simp, intro!]:
  "arch_kobj_size obj < word_bits"
  by (cases obj; simp)

lemma valid_arch_sizes[simp, intro!]:
  "obj_bits (ArchObj obj) < word_bits"
  using arch_kobj_size_bounded word_bits_conv by auto

lemmas pt_type_simps[simp] = pt_type_def[split_simps pt.split]

lemma pt_type_eq:
  "(VSRootPT_T = pt_type pt) = (\<exists>vs. pt = VSRootPT vs)"
  "(pt_type pt = VSRootPT_T) = (\<exists>vs. pt = VSRootPT vs)"
  "(NormalPT_T = pt_type pt) = (\<exists>npt. pt = NormalPT npt)"
  "(pt_type pt = NormalPT_T) = (\<exists>npt. pt = NormalPT npt)"
  by (cases pt; simp)+

lemma aobj_bits_T:
  "arch_kobj_size v = arch_obj_bits_type (aa_type v)"
  unfolding arch_obj_bits_type_def aa_type_def
  by (cases v) (auto simp: pt_type_eq)

lemma idle_global[simp, intro!]:
  "idle_thread s \<in> global_refs s"
  by (simp add: global_refs_def)

lemma valid_ipc_buffer_cap_null[simp, intro!]:
  "valid_ipc_buffer_cap NullCap buf"
  by (simp add: valid_ipc_buffer_cap_def)

lemma pageBits_clb_less_word_bits[simp, intro!]:
  "pageBits - cte_level_bits < word_bits"
  by (rule less_imp_diff_less, simp)

lemmas valid_arch_cap_def2 = valid_arch_cap_def

lemma valid_arch_cap_ref_lift:
  assumes P: "\<And>T p. f \<lbrace>typ_at (AArch T) p\<rbrace>"
  shows "f \<lbrace>valid_arch_cap_ref acap\<rbrace>"
  unfolding valid_arch_cap_ref_def
  by (cases acap; wpsimp wp: P hoare_vcg_const_imp_lift)

(* In eta-extended form, so typ_at can be unfolded when needed *)
lemma valid_arch_cap_typ:
  assumes P: "\<And>T p. f \<lbrace>\<lambda>s. typ_at (AArch T) p s\<rbrace>"
  shows      "f \<lbrace>valid_arch_cap c\<rbrace>"
  unfolding valid_arch_cap_def
  by (case_tac c; wpsimp wp: P valid_arch_cap_ref_lift)

lemma valid_pte_lift2:
  assumes x: "\<And>T p. T \<noteq> AVCPU \<Longrightarrow> \<lbrace>Q and typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_pte level pte s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pte level pte s\<rbrace>"
  by (cases pte) (simp add: data_at_def | wp hoare_vcg_disj_lift x)+

lemmas valid_pte_lift = valid_pte_lift2[where Q=\<top>, simplified]

lemma valid_vspace_obj_typ2:
  assumes P: "\<And>p T. \<lbrace>\<lambda>s. Q s \<and> typ_at (AArch T) p s\<rbrace> f \<lbrace>\<lambda>rv s. typ_at (AArch T) p s\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_vspace_obj level obj s\<rbrace> f \<lbrace>\<lambda>rv s. valid_vspace_obj level obj s\<rbrace>"
  by (cases obj)
     (wpsimp wp: P hoare_vcg_all_lift hoare_vcg_ball_lift valid_pte_lift2|rule conjI|assumption)+

lemmas valid_vspace_obj_typ = valid_vspace_obj_typ2[where Q=\<top>, simplified]

lemma global_refs_equiv:
  assumes "idle_thread s = idle_thread s'"
  assumes "interrupt_irq_node s = interrupt_irq_node s'"
  assumes "arm_us_global_vspace (arch_state s) = arm_us_global_vspace (arch_state s')"
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

lemmas asid_pool_of_simps[simp] = asid_pool_of_def[split_simps arch_kernel_obj.split]

lemma asid_pool_of_Some[iff]:
  "(asid_pool_of a = Some pool) = (a = ASIDPool pool)"
  by (simp add: asid_pool_of_def split: arch_kernel_obj.splits)

lemmas aobj_of_simps[simp] = aobj_of_def[split_simps kernel_object.split]

lemma aobj_of_Some[iff]:
  "(aobj_of a = Some ao) = (a = ArchObj ao)"
  by (simp add: aobj_of_def split: kernel_object.splits)

lemma aobj_of_None[simp]:
  "(aobj_of ko = None) = (\<not>is_ArchObj ko)"
  "(None = aobj_of ko) = (\<not>is_ArchObj ko)"
  by (cases ko; simp)+

lemmas pt_of_simps[simp] = pt_of_def[split_simps arch_kernel_obj.split]

lemma pt_of_Some[iff]:
  "(pt_of a = Some pt) = (a = PageTable pt)"
  by (simp add: pt_of_def split: arch_kernel_obj.splits)

lemma pt_of_None[simp]:
  "(pt_of ako = None) = (\<not>is_PageTable ako)"
  "(None = pt_of ako) = (\<not>is_PageTable ako)"
  by (cases ako; simp)+

lemmas vcpu_of_simps[simp] = vcpu_of_def[split_simps arch_kernel_obj.split]

lemma vcpu_of_Some[simp]:
  "(vcpu_of ako = Some vcpu) = (ako = VCPU vcpu)"
  by (cases ako; simp)

lemma vcpu_of_None[simp]:
  "(vcpu_of ako = None) = (\<not>is_VCPU ako)"
  "(None = vcpu_of ako) = (\<not>is_VCPU ako)"
  by (cases ako; simp)+

lemma asid_pool_of_None[simp]:
  "(asid_pool_of ako = None) = (\<not>is_ASIDPool ako)"
  "(None = asid_pool_of ako) = (\<not>is_ASIDPool ako)"
  by (cases ako; simp)+

lemma aobjs_of_Some:
  "(aobjs_of s p = Some ao) = (kheap s p = Some (ArchObj ao))"
  by (simp add: in_omonad)

lemma pts_of_Some:
  "(pts_of s p = Some pt) = (aobjs_of s p = Some (PageTable pt))"
  by (simp add: in_omonad)

(* Not [simp], because we don't always want to break the vspace_obj_of abstraction *)
lemma vspace_obj_of_None:
  "(vspace_obj_of ako = None) = is_VCPU ako"
  "(None = vspace_obj_of ako) = is_VCPU ako"
  by (auto simp: vspace_obj_of_def)

(* Not [simp], because we don't always want to break the vspace_obj_of abstraction *)
lemma vspace_obj_of_Some:
  "(vspace_obj_of ako = Some ako') = (ako' = ako \<and> \<not>is_VCPU ako)"
  by (auto simp: vspace_obj_of_def)

lemma vspace_obj_of_simps[simp]:
  "vspace_obj_of (ASIDPool ap) = Some (ASIDPool ap)"
  "vspace_obj_of (PageTable pt) = Some (PageTable pt)"
  "vspace_obj_of (DataPage d sz) = Some (DataPage d sz)"
  "vspace_obj_of (VCPU vcpu) = None"
  by (auto simp: vspace_obj_of_def)

lemma not_VCPU_eq:
  "(\<not>is_VCPU ako) = (is_ASIDPool ako \<or> is_PageTable ako \<or> is_DataPage ako)"
  by (cases ako) auto

declare a_typeE[elim!]

lemma aa_typeE[elim!]:
  "\<lbrakk>aa_type ao = AASIDPool; (\<And>ap. ao = ASIDPool ap \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>aa_type ao = APageTable pt_t; (\<And>pt. \<lbrakk> ao = PageTable pt; pt_t = pt_type pt \<rbrakk> \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>aa_type ao = AUserData sz; ao = DataPage False sz \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>aa_type ao = ADeviceData sz; ao = DataPage True sz \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>aa_type ao = AVCPU; (\<And>vcpu. ao = VCPU vcpu \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  by (cases ao; clarsimp split: if_split_asm)+

lemma atyp_at_eq_kheap_obj:
  "typ_at (AArch AASIDPool) p s \<longleftrightarrow> (\<exists>f. kheap s p = Some (ArchObj (ASIDPool f)))"
  "typ_at (AArch (APageTable pt_t)) p s \<longleftrightarrow> (\<exists>pt. kheap s p = Some (ArchObj (PageTable pt)) \<and> pt_t = pt_type pt)"
  "typ_at (AArch (AUserData sz)) p s \<longleftrightarrow> (kheap s p = Some (ArchObj (DataPage False sz)))"
  "typ_at (AArch (ADeviceData sz)) p s \<longleftrightarrow> (kheap s p = Some (ArchObj (DataPage True sz)))"
  "typ_at (AArch AVCPU) p s \<longleftrightarrow> (\<exists>vcpu. kheap s p = Some (ArchObj (VCPU vcpu)))"
  by (auto simp: obj_at_def)


lemma level_pte_of_pt:
  "(\<exists>pte. level_pte_of pt_t p (pts_of s) = Some pte) =
   (pt_at pt_t (table_base pt_t p) and K (is_aligned p pte_bits)) s"
  apply (clarsimp simp: level_pte_of_def obj_at_def obind_def in_omonad
                  split: option.splits)
  apply (simp add: opt_map_def)
  done

lemma pte_at_def2:
  "pte_at pt_t p = (pt_at pt_t (table_base pt_t p) and K (is_aligned p pte_bits))"
  by (auto simp: pte_at_def level_pte_of_pt)

lemmas pt_apply_def_simps[simp] = pt_apply_def[split_simps pt.split]

lemma level_ptes_of_pts:
  "(level_pte_of pt_t p (pts_of s) = Some pte) =
   (\<exists>pt. pts_of s (table_base pt_t p) = Some pt \<and> pt_apply pt (table_index pt_t p) = pte \<and>
         is_aligned p pte_bits \<and> pt_t = pt_type pt)"
  by (clarsimp simp: level_pte_of_def obj_at_def obind_def in_omonad opt_map_def
               split: option.splits)

lemma ptes_of_Some:
  "(ptes_of s pt_t p = Some pte) =
   (is_aligned p pte_bits \<and>
     (\<exists>pt. pts_of s (table_base pt_t p) = Some pt \<and> pt_t = pt_type pt \<and>
           pt_apply pt (table_index pt_t p) = pte))"
  apply (simp add: map_add_Some_iff level_ptes_of_pts)
  apply (rule iffI; clarsimp simp: level_pte_of_def; rename_tac pt, case_tac pt; clarsimp)
  done

lemma asid_pools_at_eq:
  "asid_pool_at p s \<longleftrightarrow> asid_pools_of s p \<noteq> None"
  by (auto simp: obj_at_def in_opt_map_eq)

lemma pt_at_eq:
  "pt_at pt_t p s \<longleftrightarrow> pts_of s p \<noteq> None \<and> (pt_t = pt_type (the (pts_of s p)))"
  by (auto simp: obj_at_def opt_map_def split: option.splits)

lemma vspace_pt_at_eq:
  "vspace_pt_at p s \<longleftrightarrow> (\<exists>pt. pts_of s p = Some (VSRootPT pt))"
  by (auto simp: obj_at_def in_opt_map_eq pt_type_eq)

lemma valid_asid_tableD:
  "\<lbrakk> asid_table s x = Some p; valid_asid_table s \<rbrakk> \<Longrightarrow> asid_pool_at p s"
  by (auto simp: valid_asid_table_def asid_pools_at_eq)

lemma dom_asid_pools_of_typ:
  "dom (asid_pools_of s) = {p. asid_pool_at p s}"
  by (auto simp: obj_at_def in_opt_map_eq)

lemma dom_asid_pools_of_lift:
  assumes "\<And>T p. f \<lbrace>typ_at (AArch T) p\<rbrace>"
  assumes "\<And>A B. A \<subseteq> B \<Longrightarrow> P A \<Longrightarrow> P B"
  shows "f \<lbrace>\<lambda>s. P (dom (asid_pools_of s))\<rbrace>"
  by (wpsimp wp: hoare_vcg_set_pred_lift_mono assms simp: dom_asid_pools_of_typ)

lemma aobj_at_default_arch_cap_valid:
  assumes "ty \<noteq> ASIDPoolObj"
  assumes "ko_at (ArchObj (default_arch_object ty dev us)) x s"
  shows "valid_arch_cap (arch_default_cap ty x us dev) s"
  using assms
  by (auto elim!: obj_at_weakenE
        simp add: arch_default_cap_def valid_arch_cap_def default_arch_object_def
                  a_type_def valid_vm_rights_def
           split: apiobject_type.splits aobject_type.splits option.splits)

lemmas aobj_ref_default = aobj_ref_arch_cap

lemma acap_rights_update_id [intro!, simp]:
  "wellformed_acap cap \<Longrightarrow> acap_rights_update (acap_rights cap) cap = cap"
  unfolding acap_rights_update_def
  by (auto split: arch_cap.splits option.splits)

lemma in_user_frame_def:
  "in_user_frame p \<equiv> \<lambda>s.
     \<exists>sz. typ_at (AArch (AUserData sz)) (p && ~~ mask (pageBitsForSize sz)) s"
  by (fastforce simp: in_user_frame_def obj_at_def intro!: eq_reflection)

lemma in_user_frame_lift:
  assumes "\<And>T p. f \<lbrace>typ_at (AArch T) p\<rbrace>"
  shows "f \<lbrace>in_user_frame p\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift assms)

lemma valid_vcpu_default[simp]:
  "valid_vcpu default_vcpu s"
  by (simp add: valid_vcpu_def default_vcpu_def)

lemma pt_range_Normal[simp]:
  "pt_range (NormalPT npt) = range npt"
  unfolding pt_range_def
  by (force intro: arg_cong[where f=npt] ucast_down_ucast_id[symmetric] simp: is_down)

lemma pt_range_VSRoot[simp]:
  "pt_range (VSRootPT vs) = range vs"
  unfolding pt_range_def
  by (force intro: arg_cong[where f=vs] ucast_down_ucast_id[symmetric] simp: is_down bit_simps)

lemma pt_apply_pt_range[simp, intro!]:
  "pt_apply pt idx \<in> pt_range pt"
  by (auto simp: pt_range_def)

lemma pt_apply_mask:
  "pt_apply pt (idx && mask (ptTranslationBits (pt_type pt))) = pt_apply pt idx"
  by (cases pt; clarsimp simp: bit_simps ucast_mask_drop)

lemma pt_rangeD:
  "pte \<in> pt_range pt \<Longrightarrow>
   \<exists>idx. idx \<le> mask (ptTranslationBits (pt_type pt)) \<and> pt_apply pt idx = pte"
  by (fastforce simp: pt_range_def intro!: word_and_le1 pt_apply_mask)

lemma wellformed_arch_default[simp]:
  "arch_valid_obj (default_arch_object ao_type dev us) s"
  unfolding arch_valid_obj_def default_arch_object_def
  by (cases ao_type; simp add: wellformed_pte_def valid_pt_range_def)

lemma level_type_max[simp]:
  "level_type max_pt_level = VSRootPT_T"
  by (simp add: level_type_def)

lemma level_type_eq[simp]:
  "(NormalPT_T = level_type level) = (level \<noteq> max_pt_level)"
  "(level_type level = NormalPT_T) = (level \<noteq> max_pt_level)"
  "(VSRootPT_T = level_type level) = (level = max_pt_level)"
  "(level_type level = VSRootPT_T) = (level = max_pt_level)"
  by (simp add: level_type_def)+

lemma level_type_less_max_pt_level:
  "level < max_pt_level \<Longrightarrow> level_type level = NormalPT_T"
  by (clarsimp simp: level_type_def)

lemma ptTranslationBits_NormalPT_T_leq:
  "ptTranslationBits NormalPT_T \<le> ptTranslationBits VSRootPT_T"
  by (simp add: bit_simps)

lemma valid_vspace_obj_default'[simp]:
  "\<lbrakk> ao_type = VSpaceObj \<Longrightarrow> level = max_pt_level;
     ao_type = PageTableObj \<Longrightarrow> level \<noteq> max_pt_level \<rbrakk> \<Longrightarrow>
   valid_vspace_obj level (default_arch_object ao_type dev us) s"
  unfolding default_arch_object_def
  by (cases ao_type; simp)

lemma physical_arch_cap_has_ref:
  "(acap_class arch_cap = PhysicalClass) = (\<exists>y. aobj_ref arch_cap = Some y)"
  by (cases arch_cap; simp)

lemma typ_at_pg_user:
  "typ_at (AArch (AUserData sz)) buf s = ko_at (ArchObj (DataPage False sz)) buf s"
  unfolding obj_at_def by auto

lemma typ_at_pg_device:
  "typ_at (AArch (ADeviceData sz)) buf s = ko_at (ArchObj (DataPage True sz)) buf s"
  unfolding obj_at_def by auto

lemmas typ_at_pg = typ_at_pg_user typ_at_pg_device

lemma state_hyp_refs_of_elemD:
  "\<lbrakk> ref \<in> state_hyp_refs_of s x \<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. ref \<in> hyp_refs_of obj) x s"
  by (clarsimp simp: state_hyp_refs_of_def obj_at_def split: option.splits)

lemma state_hyp_refs_of_eqD:
  "\<lbrakk> state_hyp_refs_of s x = S; S \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. hyp_refs_of obj = S) x s"
  by (clarsimp simp: state_hyp_refs_of_def obj_at_def split: option.splits)

lemma obj_at_state_hyp_refs_ofD:
  "obj_at P p s \<Longrightarrow> \<exists>ko. P ko \<and> state_hyp_refs_of s p = hyp_refs_of ko"
  by (fastforce simp: obj_at_def state_hyp_refs_of_def)

lemma ko_at_state_hyp_refs_ofD:
  "ko_at ko p s \<Longrightarrow> state_hyp_refs_of s p = hyp_refs_of ko"
  by (clarsimp dest!: obj_at_state_hyp_refs_ofD)

lemma hyp_sym_refs_obj_atD:
  "\<lbrakk> obj_at P p s; sym_refs (state_hyp_refs_of s) \<rbrakk>
   \<Longrightarrow> \<exists>ko. P ko \<and> state_hyp_refs_of s p = hyp_refs_of ko \<and>
           (\<forall>(x, tp)\<in>hyp_refs_of ko. obj_at (\<lambda>ko. (p, symreftype tp) \<in> hyp_refs_of ko) x s)"
  apply (drule obj_at_state_hyp_refs_ofD)
  apply (erule exEI, clarsimp)
  apply (drule sym, simp)
  apply (drule (1) sym_refsD)
  apply (erule state_hyp_refs_of_elemD)
  done

lemma hyp_sym_refs_ko_atD:
  "\<lbrakk> ko_at ko p s; sym_refs (state_hyp_refs_of s) \<rbrakk> \<Longrightarrow>
     state_hyp_refs_of s p = hyp_refs_of ko \<and>
     (\<forall>(x, tp)\<in>hyp_refs_of ko.  obj_at (\<lambda>ko. (p, symreftype tp) \<in> hyp_refs_of ko) x s)"
  by (drule(1) hyp_sym_refs_obj_atD, simp)

lemma state_hyp_refs_of_pspaceI:
  "\<lbrakk> P (state_hyp_refs_of s); kheap s = kheap s' \<rbrakk> \<Longrightarrow> P (state_hyp_refs_of s')"
  unfolding state_hyp_refs_of_def by simp

lemma state_hyp_refs_update[iff]:
  "kheap (f s) = kheap s \<Longrightarrow> state_hyp_refs_of (f s) = state_hyp_refs_of s"
  by (clarsimp simp: state_hyp_refs_of_def)

lemma hyp_refs_of_hyp_live:
  "hyp_refs_of ko \<noteq> {} \<Longrightarrow> hyp_live ko"
  by (cases ko)
     (auto simp: hyp_live_def arch_live_def refs_of_ao_def vcpu_tcb_refs_def tcb_hyp_refs_def
                     tcb_vcpu_refs_def hyp_refs_of_def
           split: arch_kernel_obj.splits option.splits)

lemma hyp_refs_of_hyp_live_obj:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> P ko; hyp_refs_of ko = {} \<rbrakk> \<Longrightarrow> False \<rbrakk> \<Longrightarrow> obj_at hyp_live p s"
  by (fastforce simp: obj_at_def hyp_refs_of_hyp_live)

lemma valid_tcb_arch_ref_lift:
  "tcb_arch_ref t = tcb_arch_ref t' \<Longrightarrow> valid_arch_tcb (tcb_arch t) = valid_arch_tcb (tcb_arch t')"
  by (simp add: valid_arch_tcb_def tcb_arch_ref_def)

lemma tcb_arch_ref_simps[simp]:
  "\<And>f. tcb_arch_ref (tcb_ipc_buffer_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_mcpriority_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_ctable_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_vtable_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_reply_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_caller_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_ipcframe_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_state_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_fault_handler_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_fault_update f tcb) = tcb_arch_ref tcb"
  "\<And>f. tcb_arch_ref (tcb_bound_notification_update f tcb) = tcb_arch_ref tcb"
  "tcb_arch_ref (t\<lparr>tcb_arch := (arch_tcb_context_set a (tcb_arch t))\<rparr>) = tcb_arch_ref t"
  "tcb_arch_ref (tcb\<lparr>tcb_arch := arch_tcb_set_registers regs (tcb_arch tcb)\<rparr>) = tcb_arch_ref tcb"
  by (auto simp: tcb_arch_ref_def arch_tcb_set_registers_def arch_tcb_context_set_def)

lemma hyp_live_tcb_def: "hyp_live (TCB tcb) = bound (tcb_arch_ref tcb)"
  by (clarsimp simp: hyp_live_def tcb_arch_ref_def)

lemma hyp_live_tcb_simps[simp]:
  "\<And>f. hyp_live (TCB (tcb_ipc_buffer_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_mcpriority_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_ctable_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_vtable_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_reply_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_caller_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_ipcframe_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_state_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_fault_handler_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_fault_update f tcb)) = hyp_live (TCB tcb)"
  "\<And>f. hyp_live (TCB (tcb_bound_notification_update f tcb)) = hyp_live (TCB tcb)"
  by (simp_all add: hyp_live_tcb_def)

lemma wellformed_arch_typ:
  assumes [wp]: "\<And>T p. f \<lbrace>typ_at T p\<rbrace>"
  shows "f \<lbrace>arch_valid_obj ao\<rbrace>"
  unfolding arch_valid_obj_def valid_vcpu_def
  by (simp split: option.split)
     (cases ao; wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma valid_arch_tcb_pspaceI:
  "\<lbrakk> valid_arch_tcb t s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_arch_tcb t s'"
  unfolding valid_arch_tcb_def obj_at_def by simp

lemma valid_arch_tcb_lift:
  assumes [wp]: "\<And>T p. f \<lbrace>typ_at T p\<rbrace>"
  shows "f \<lbrace>valid_arch_tcb t\<rbrace>"
  unfolding valid_arch_tcb_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)

lemma obj_ref_not_arch_gen_ref:
  "x \<in> obj_refs cap \<Longrightarrow> arch_gen_refs cap = {}"
  by (cases cap; simp add: arch_gen_obj_refs_def)

lemma arch_gen_ref_not_obj_ref:
  "x \<in> arch_gen_refs cap \<Longrightarrow> obj_refs cap = {}"
  by (cases cap; simp add: arch_gen_obj_refs_def)

lemmas arch_gen_obj_refs_simps[simp] = arch_gen_obj_refs_def

lemma arch_gen_obj_refs_inD:
  "x \<in> arch_gen_obj_refs cap \<Longrightarrow> arch_gen_obj_refs cap = {x}"
  by simp

lemma same_aobject_same_arch_gen_refs:
  "same_aobject_as ac ac' \<Longrightarrow> arch_gen_obj_refs ac = arch_gen_obj_refs ac'"
  by simp

lemma valid_arch_mdb_eqI:
  assumes "valid_arch_mdb (is_original_cap s) (caps_of_state s)"
  assumes "caps_of_state s = caps_of_state s'"
  assumes "is_original_cap s = is_original_cap s'"
  shows "valid_arch_mdb (is_original_cap s') (caps_of_state s')" using assms
  by (clarsimp simp: valid_arch_mdb_def)

lemma valid_arch_cap_ref_pspaceI[elim]:
  "\<lbrakk> valid_arch_cap_ref acap s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_arch_cap_ref acap s'"
  unfolding valid_arch_cap_ref_def
  by (auto intro: obj_at_pspaceI split: arch_cap.split)

lemma valid_arch_tcb_context_update[simp]:
  "valid_arch_tcb (tcb_context_update f t) = valid_arch_tcb t"
  unfolding valid_arch_tcb_def obj_at_def by simp

lemma valid_arch_arch_tcb_context_set[simp]:
  "valid_arch_tcb (arch_tcb_context_set a t) = valid_arch_tcb t"
  by (simp add: arch_tcb_context_set_def)

lemma valid_arch_arch_tcb_set_registers[simp]:
  "valid_arch_tcb (arch_tcb_set_registers a t) = valid_arch_tcb t"
  by (simp add: arch_tcb_set_registers_def)

lemma valid_arch_tcb_typ_at:
  "\<lbrakk> valid_arch_tcb t s; \<And>T p. typ_at T p s \<Longrightarrow> typ_at T p s' \<rbrakk> \<Longrightarrow> valid_arch_tcb t s'"
  by (simp add: valid_arch_tcb_def)

lemma user_vtop_ge0[intro!,simp]:
  "0 < user_vtop"
  by (simp add: user_vtop_def pptrUserTop_def pptrBase_def mask_def)

lemma canonical_user_ge0[intro!,simp]:
  "0 < canonical_user"
  by (simp add: canonical_user_def mask_def ipa_size_def)

lemma pptrTop_le_ipa_size:
  "pptrTop \<le> mask ipa_size"
  by (simp add: bit_simps pptrTop_def mask_def)

lemma below_pptrTop_ipa_size:
  "p < pptrTop \<Longrightarrow> p \<le> mask ipa_size"
  using pptrTop_le_ipa_size
  by simp

lemma addrFromPPtr_mask_ipa:
  "\<lbrakk> pptr_base \<le> pt_ptr; pt_ptr < pptrTop \<rbrakk>
   \<Longrightarrow> addrFromPPtr pt_ptr && mask ipa_size = addrFromPPtr pt_ptr"
  using pptrTop_le_ipa_size
  by (simp add: and_mask_eq_iff_le_mask addrFromPPtr_def pptr_base_def pptrBaseOffset_def
                paddrBase_def word_le_imp_diff_le)

lemma pageBits_less_ipa_size[simp]:
  "pageBits < ipa_size"
  by (simp add: bit_simps)

lemmas window_defs =
  kernel_window_def not_kernel_window_def kernel_regions_def
  kernel_device_window_def user_region_def user_window_def

lemma valid_uses_kernel_window:
  "\<lbrakk> valid_uses s; p \<in> kernel_window s \<rbrakk> \<Longrightarrow> p \<in> {pptr_base ..< pptrTop} \<and> canonical_address p"
  unfolding valid_uses_def window_defs
  by (erule_tac x=p in allE) (auto simp: kernel_window_range_def)

lemma kernel_window_bounded:
  "\<lbrakk> p \<in> kernel_window s; valid_uses s \<rbrakk> \<Longrightarrow> p \<in> kernel_window_range"
  by (fastforce dest: valid_uses_kernel_window simp: kernel_window_range_def)

lemma pspace_in_kw_bounded:
  "\<lbrakk> kheap s p = Some ko; pspace_in_kernel_window s; valid_uses s; pspace_aligned s \<rbrakk> \<Longrightarrow>
   p \<in> kernel_window_range"
  unfolding pspace_aligned_def
  apply (drule bspec, fastforce)
  apply (simp add: pspace_in_kernel_window_def)
  apply (erule allE, erule allE, erule (1) impE)
  apply (prop_tac "p \<in> kernel_window s")
   apply (erule set_mp)
   apply (clarsimp simp: is_aligned_no_overflow)
  apply (fastforce dest: kernel_window_bounded)
  done

lemma pt_walk_max_level:
  "pt_walk top_level bot_level pt_ptr vptr ptes = Some (level, p)
  \<Longrightarrow> level \<le> top_level"
  apply (induct top_level arbitrary: pt_ptr)
   apply (simp add: pt_walk.simps in_omonad)
  apply (rotate_tac 1)
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
  apply (drule meta_spec, drule (1) meta_mp)
  apply (drule vm_level.zero_least)
  using vm_level.pred less_trans not_less by blast

lemma pt_walk_min_level:
  "pt_walk top_level bot_level pt_ptr vptr ptes = Some (level, p)
  \<Longrightarrow> min top_level bot_level \<le> level"
  apply (induct top_level arbitrary: pt_ptr)
   apply (simp add: pt_walk.simps in_omonad)
  apply (rotate_tac 1)
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
  apply (drule meta_spec, drule (1) meta_mp)
  apply (auto simp: min_def split: if_split_asm dest: vm_level.minus1_leq)
  done

lemma pt_walk_top:
  "top_level \<le> bot_level \<Longrightarrow> pt_walk top_level bot_level pt vptr ptes = Some (top_level, pt)"
  by (auto simp: pt_walk.simps Let_def)

lemma pt_walk_equal_top_slot_Some:
  "\<lbrakk> ptes (level_type top_level) (pt_slot_offset top_level pt_ptr vptr) =
     ptes (level_type top_level) (pt_slot_offset top_level pt_ptr' vptr);
     pt_walk top_level bot_level pt_ptr vptr ptes = Some (level, p) \<rbrakk> \<Longrightarrow>
   if level = top_level then
     pt_walk top_level bot_level pt_ptr' vptr ptes = Some (level, pt_ptr') \<and> p = pt_ptr
   else
     pt_walk top_level bot_level pt_ptr' vptr ptes = Some (level, p)"
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp: in_omonad pt_walk_top split: if_split_asm)
  apply (erule disjE; clarsimp)
   apply (subgoal_tac "level \<noteq> top_level")
    apply simp
    apply (subst pt_walk.simps)
    apply (clarsimp simp: in_omonad split: if_split_asm)
   apply clarsimp
   apply (blast dest: leD pt_walk_max_level)
  apply (subst pt_walk.simps)
  apply (clarsimp simp: in_omonad)
  apply (blast dest: leD pt_walk_max_level)
  done

lemma pt_walk_equal_top_slot_None:
  "\<lbrakk> ptes (level_type top_level) (pt_slot_offset top_level pt_ptr vptr) =
     ptes (level_type top_level) (pt_slot_offset top_level pt_ptr' vptr);
     pt_walk top_level bot_level pt_ptr' vptr ptes = None \<rbrakk> \<Longrightarrow>
  pt_walk top_level bot_level pt_ptr vptr ptes = None"
  apply (subst (asm) pt_walk.simps)
  apply (subst pt_walk.simps)
  by (auto simp: Let_def obind_def oapply_def oreturn_def oapply2_def split: if_split_asm option.splits)

lemma translate_address_equal_top_slot:
  notes pt_top = pt_walk_equal_top_slot_Some[OF sym, where top_level=max_pt_level, simplified]
  shows "ptes VSRootPT_T (pt_slot_offset max_pt_level pt_ptr vptr) =
           ptes VSRootPT_T (pt_slot_offset max_pt_level pt_ptr' vptr)
         \<Longrightarrow> translate_address pt_ptr vptr ptes = translate_address pt_ptr' vptr ptes"
  supply if_split_asm[split] opt_map_def[simp]
  supply pt_walk_equal_top_slot_None[where top_level=max_pt_level, simplified, dest]
  apply (simp add: translate_address_def obind_def pt_lookup_slot_from_level_def pt_lookup_target_def
            split: option.splits)
  apply ((rule conjI; clarsimp), (frule (1) pt_top)?, fastforce)+
  apply (frule (1) pt_top, fastforce)
  done

lemmas min_max_pt_level[simp] = min_absorb2[where x=max_pt_level]

lemma vs_lookup_min_level:
  "vs_lookup_table bot_level asid vref s = Some (level, p) \<Longrightarrow> bot_level \<le> level"
  by (auto simp: vs_lookup_table_def in_omonad not_le split: if_split_asm dest!: pt_walk_min_level)

lemma pt_bits_left_0[simp]:
  "(pt_bits_left level = pageBits) = (level = 0)"
  by (auto simp: pt_bits_left_def bit_simps)

lemma pt_bits_left_mono:
  "level \<le> level' \<Longrightarrow> pt_bits_left level \<le> pt_bits_left level'"
  using le_diff_conv by (fastforce simp: pt_bits_left_def ptTranslationBits_def)

lemma max_pt_bits_left[simp]:
  "max (pt_bits_left level) (pt_bits_left level') = pt_bits_left (max level level')"
  apply (clarsimp simp: max_def pt_bits_left_mono)
  apply (simp add: not_le)
  apply (drule less_imp_le)
  apply (drule pt_bits_left_mono)
  apply simp
  done

lemma pt_bits_left_plus1:
  "level \<le> max_pt_level \<Longrightarrow>
   pt_bits_left (level + 1) = ptTranslationBits level + pt_bits_left level"
  by (auto simp: pt_bits_left_def plus_one_eq_asid_pool intro: arg_cong)

lemma vref_for_level_idem:
  "level' \<le> level \<Longrightarrow>
   vref_for_level (vref_for_level vref level') level = vref_for_level vref level"
  by (simp add: vref_for_level_def pt_bits_left_mono mask_lower_twice)

lemma vref_for_level_max[simp]:
  "vref_for_level (vref_for_level vref level') level = vref_for_level vref (max level level')"
  by (simp add: vref_for_level_def pt_bits_left_mono neg_mask_twice bit.conj_ac)

lemma vref_for_level_pt_index:
  "vref_for_level vref level = vref_for_level vref' level \<Longrightarrow>
   pt_index level vref = pt_index level vref'"
  by (simp add: pt_index_def vref_for_level_def) (metis mask_shift)

lemma vref_for_level_pt_slot_offset:
  "vref_for_level vref level = vref_for_level vref' level \<Longrightarrow>
   pt_slot_offset level pt vref = pt_slot_offset level pt vref'"
  by (auto simp: pt_slot_offset_def dest: vref_for_level_pt_index)

lemma vref_for_level_eq_mono:
  "\<lbrakk> vref_for_level vref level = vref_for_level vref' level; level \<le> level' \<rbrakk> \<Longrightarrow>
  vref_for_level vref level' = vref_for_level vref' level'"
  unfolding vref_for_level_def
  by (metis (no_types, opaque_lifting) pt_bits_left_mono mask_lower_twice)

lemma vref_for_level_eq_max_mono:
  "\<lbrakk> vref_for_level vref level = vref_for_level vref' level' \<rbrakk> \<Longrightarrow>
  vref_for_level vref (max level level') = vref_for_level vref' (max level level')"
  unfolding vref_for_level_def
  by (metis vref_for_level_def vref_for_level_max max.commute max.idem)

lemma pt_walk_vref_for_level_eq:
  "\<lbrakk> vref_for_level vref (bot_level+1) = vref_for_level vref' (bot_level+1); bot_level \<le> top_level \<rbrakk> \<Longrightarrow>
   pt_walk top_level bot_level pt vref =
   pt_walk top_level bot_level pt vref'"
  apply (rule ext, rename_tac ptes)
  apply (induct top_level arbitrary: pt)
   apply (drule_tac pt=pt in vref_for_level_pt_slot_offset)
   apply (simp add: pt_walk.simps Let_def oapply_def)
   apply (simp add: obind_def oreturn_def split: option.splits)
  apply (case_tac "top_level=bot_level")
   apply (simp add: pt_walk.simps)
  apply (subst pt_walk.simps)
  apply (subst (2) pt_walk.simps)
  apply (simp add: Let_def vm_level.leq_minus1_less)
  apply (drule_tac level'=top_level in vref_for_level_eq_mono)
   apply (simp add: vm_level.plus_one_leq)
  apply (drule_tac pt=pt in vref_for_level_pt_slot_offset)
  apply (clarsimp simp: obind_def split: option.splits)
  done

lemma pt_walk_vref_for_level:
  "\<lbrakk> level \<le> bot_level; bot_level \<le> top_level; top_level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   pt_walk top_level bot_level pt (vref_for_level vref level) =
   pt_walk top_level bot_level pt vref"
  by (meson max_pt_level_less_Suc le_less order_trans vref_for_level_idem pt_walk_vref_for_level_eq)

lemma pt_walk_vref_for_level1:
  "\<lbrakk> level \<le> bot_level; bot_level \<le> top_level; top_level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   pt_walk top_level bot_level pt (vref_for_level vref (level+1)) =
   pt_walk top_level bot_level pt vref"
  by (meson max_pt_level_less_Suc vm_level.plus_one_leq leD leI order.trans vref_for_level_idem
            pt_walk_vref_for_level_eq)

lemma vs_lookup_vref_for_level1:
  "level \<le> bot_level \<Longrightarrow>
   vs_lookup_table bot_level asid (vref_for_level vref (level+1)) = vs_lookup_table bot_level asid vref"
  by (force simp: vs_lookup_table_def pt_walk_vref_for_level1 obind_def split: option.splits)

lemma vs_lookup_vref_for_level:
  "level \<le> bot_level \<Longrightarrow>
   vs_lookup_table bot_level asid (vref_for_level vref level) = vs_lookup_table bot_level asid vref"
  by (force simp: vs_lookup_table_def pt_walk_vref_for_level obind_def split: option.splits)

lemma vspace_for_asid_SomeD:
  "vspace_for_asid asid s = Some pt_ptr
   \<Longrightarrow> \<exists>pool_ptr pool entry. asid_table s (asid_high_bits_of asid) = Some pool_ptr
                            \<and> asid_pools_of s pool_ptr = Some pool
                            \<and> pool (asid_low_bits_of asid) = Some entry
                            \<and> ap_vspace entry = pt_ptr
                            \<and> asid > 0"
  unfolding vspace_for_asid_def
  by (clarsimp simp: entry_for_asid_def pool_for_asid_def entry_for_pool_def vspace_for_pool_def)

lemma vspace_for_asid_SomeI:
  "\<lbrakk> asid_table s (asid_high_bits_of asid) = Some pool_ptr;
     asid_pools_of s pool_ptr = Some pool;
     pool (asid_low_bits_of asid) = Some entry;
     ap_vspace entry = pt_ptr;
     asid > 0 \<rbrakk>
   \<Longrightarrow> vspace_for_asid asid s = Some pt_ptr"
  by (clarsimp simp: entry_for_asid_def pool_for_asid_def entry_for_pool_def vspace_for_pool_def
                     vspace_for_asid_def obind_def)

lemma ptes_of_pts_of:
  "ptes_of s pt_t pte_ptr = Some pte \<Longrightarrow>
    \<exists>pt. pts_of s (pte_ptr && ~~mask (pt_bits pt_t)) = Some pt \<and> pt_t = pt_type pt"
  by (fastforce simp: ptes_of_def in_omonad split: if_split_asm)

lemma level_ptes_of_eqI:
  "pts (table_base pt_t p) = pts' (table_base pt_t p) \<Longrightarrow>
   level_pte_of pt_t p pts = level_pte_of pt_t p pts'"
  by (rule obind_eqI | simp add: level_pte_of_def)+

lemma pte_refs_of_eqI:
  "ptes p = ptes' p \<Longrightarrow> (ptes |> pte_ref) p =  (ptes' |> pte_ref) p"
  by (clarsimp simp: opt_map_def)

lemma pt_index_mask_pt_bits[simp]:
  "(pt_index level vref << pte_bits) && mask (pt_bits level) =
   pt_index level vref << pte_bits"
  by (simp add: pt_index_def pt_bits_def table_size_def shiftl_over_and_dist mask_shiftl_decompose
                bit.conj_ac)

lemma table_base_offset_id:
  "\<lbrakk> is_aligned pt_ptr (pt_bits pt_t); (idx << pte_bits) && mask (pt_bits pt_t) = idx << pte_bits \<rbrakk>
     \<Longrightarrow> table_base pt_t (pt_ptr + (idx << pte_bits)) = pt_ptr"
  by (simp add: is_aligned_mask_out_add_eq mask_eq_x_eq_0[symmetric])

lemma table_base_pt_slot_offset[simp]:
  "is_aligned pt_ptr (pt_bits level) \<Longrightarrow>
   table_base level (pt_slot_offset level pt_ptr vref) = pt_ptr" for level::vm_level
  by (simp add: pt_slot_offset_def table_base_offset_id)

lemma pt_slot_offset_0[simp]:
  "pt_slot_offset level p 0 = p"
  by (clarsimp simp: pt_slot_offset_def pt_index_def)

lemma pt_slot_offset_or_def:
  "is_aligned pt_ptr (pt_bits (level_type level))
   \<Longrightarrow> pt_slot_offset level pt_ptr vptr = pt_ptr || (pt_index level vptr << pte_bits)"
  unfolding pt_slot_offset_def
  apply (rule is_aligned_add_or, assumption)
  apply (subgoal_tac "pt_index level vptr < 2 ^ ptTranslationBits level")
   prefer 2
   apply (simp add: pt_index_def)
   apply (rule and_mask_less', simp add: bit_simps and_mask_less')
  apply (drule shiftl_less_t2n'[where n=pte_bits], auto simp: bit_simps)
  done

lemma valid_global_arch_objs_pt_at[elim!]:
  "valid_global_arch_objs s \<Longrightarrow> vspace_pt_at (global_pt s) s"
  unfolding valid_global_arch_objs_def
  by simp

lemma pool_for_asid_vs_lookup:
  "(vs_lookup_table asid_pool_level asid vref s = Some (level, p)) =
   (pool_for_asid asid s = Some p \<and> level = asid_pool_level)"
  by (auto simp: vs_lookup_table_def in_omonad)

lemma pool_for_asid_validD:
  "\<lbrakk> pool_for_asid asid s = Some p; valid_asid_table s \<rbrakk> \<Longrightarrow> asid_pools_of s p \<noteq> None"
  by (auto simp: in_opt_map_eq valid_asid_table_def pool_for_asid_def)

locale_abbrev asid_of :: "asid_high_index \<Rightarrow> asid_low_index \<Rightarrow> asid" where
  "asid_of high low \<equiv> (ucast high << asid_low_bits) || ucast low"

lemma constructed_asid_low_bits_of[simp]:
  "asid_low_bits_of (asid_of hi_bits lo_bits) = lo_bits"
  by (clarsimp simp: asid_low_bits_of_def asid_bits_defs ucast_or_distrib ucast_ucast_id
                     ucast_shiftl_eq_0)

lemma constructed_asid_high_bits_of[simp]:
  "asid_high_bits_of (asid_of hi_bits lo_bits) = hi_bits"
  apply (clarsimp simp: asid_high_bits_of_def shiftr_over_or_dist asid_bits_defs)
  apply (subst shiftl_shiftr_id, simp)
   apply (fastforce intro: order_less_le_trans ucast_less)
  apply (simp add: ucast_ucast_id ucast_or_distrib)
  apply (rule zero_OR_eq)
  apply (rule ucast_0_I)
  apply (fastforce intro: shiftr_le_0 unat_less_power order_less_le_trans ucast_less)
  done

lemma asid_high_low_inj:
  "\<lbrakk> asid_low_bits_of asid' = asid_low_bits_of asid;
     asid_high_bits_of asid' = asid_high_bits_of asid \<rbrakk>
   \<Longrightarrow> asid' = asid"
  unfolding asid_low_bits_of_def asid_high_bits_of_def
  by (drule word_unat_eq_iff[THEN iffD1])+
     (clarsimp elim!: word_mask_shift_eqI
               simp:  unat_ucast_eq_unat_and_mask asid_low_bits_def shiftr_mask_eq' word_size)

lemma asid_of_high_low_eq[simp, intro!]:
  "asid_of (asid_high_bits_of asid) (asid_low_bits_of asid) = asid"
  by (rule asid_high_low_inj; simp)

lemma pt_walk_level:
  "pt_walk top_level bot_level pt vref ptes = Some (level, p) \<Longrightarrow>
   pt_walk top_level level pt vref ptes = Some (level, p)"
  apply (induct top_level arbitrary: pt)
   apply (simp add: pt_walk.simps)
  apply (subst pt_walk.simps)
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
  apply (drule meta_spec, drule (1) meta_mp)
  by (fastforce simp: vm_level.leq_minus1_less dest: pt_walk_max_level)

lemma vs_lookup_level:
  "vs_lookup_table bot_level asid vref s = Some (level, p) \<Longrightarrow>
   vs_lookup_table level asid vref s = Some (level, p)"
  apply (clarsimp simp: vs_lookup_table_def in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
  apply (frule pt_walk_max_level, simp)
  apply (fastforce intro: pt_walk_level)
  done

lemma vs_lookup_level_vref1:
  "vs_lookup_table bot_level asid vref s = Some (level, p)
   \<Longrightarrow> vs_lookup_table level asid (vref_for_level vref (level+1)) s = Some (level, p)"
  by (simp add: vs_lookup_level vs_lookup_vref_for_level1)

lemma vs_lookup_level_vref:
  "vs_lookup_table bot_level asid vref s = Some (level, p)
   \<Longrightarrow> vs_lookup_table level asid (vref_for_level vref level) s = Some (level, p)"
  by (simp add: vs_lookup_level vs_lookup_vref_for_level)

lemma pt_walk_same[simp]:
  "pt_walk level level p vref = oreturn (level, p)"
  by (auto simp: pt_walk.simps)

lemma vs_lookup_asid_pool:
  "\<lbrakk> vs_lookup_table bot_level asid vref s = Some (asid_pool_level, p); valid_asid_table s \<rbrakk>
  \<Longrightarrow> asid_pools_of s p \<noteq> None"
  by (drule vs_lookup_level)
     (auto dest!: pool_for_asid_validD simp: pool_for_asid_vs_lookup)

lemma pt_lookup_vs_lookup_eq:
  "\<lbrakk> bot_level \<le> max_pt_level; 0 < asid \<rbrakk> \<Longrightarrow>
   vs_lookup_table bot_level asid vref = do {
      pt \<leftarrow> vspace_for_asid asid;
      pt_walk max_pt_level bot_level pt vref \<circ> ptes_of
  }"
  by (auto simp: vs_lookup_table_def vspace_for_asid_def obind_assoc entry_for_asid_def
                 vspace_for_pool_def obind_comp_dist
           intro!: opt_bind_cong)

lemma vspace_for_asid_0:
  "vspace_for_asid asid s = Some pt \<Longrightarrow> 0 < asid"
  by (simp add: vspace_for_asid_def in_omonad entry_for_asid_def split: if_split_asm)

lemma pt_lookup_vs_lookupI:
  "\<lbrakk> vspace_for_asid asid s = Some pt;
     pt_walk max_pt_level bot_level pt vref (ptes_of s) = Some (level, p);
     bot_level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   vs_lookup_table bot_level asid vref s = Some (level, p)"
  by (frule vspace_for_asid_0) (auto simp: pt_lookup_vs_lookup_eq obind_def)

lemma pt_lookup_slot_vs_lookup_slotI:
  "\<lbrakk> vspace_for_asid asid s = Some pt_ptr;
     pt_lookup_slot pt_ptr vref (ptes_of s) = Some (level, slot) \<rbrakk>
   \<Longrightarrow> vs_lookup_slot level asid vref s = Some (level, slot) \<and> level \<le> max_pt_level"
  unfolding pt_lookup_slot_def pt_lookup_slot_from_level_def vs_lookup_slot_def
  apply (clarsimp simp: in_omonad)
  apply (drule (1) pt_lookup_vs_lookupI, simp)
  apply (drule vs_lookup_level)
  apply (fastforce dest: pt_walk_max_level)
  done

lemma vspace_for_asid_vs_lookup:
  "vspace_for_asid asid s = Some pt \<Longrightarrow>
   vs_lookup_table max_pt_level asid 0 s = Some (max_pt_level, pt)"
  by (clarsimp simp: vspace_for_asid_def vs_lookup_table_def entry_for_asid_def vspace_for_pool_def
                     in_omonad pt_walk.simps)

lemma pte_at_eq:
  "pte_at pt_t p s = (ptes_of s pt_t p \<noteq> None)"
  by (auto simp: obj_at_def pte_at_def in_omonad)

lemma vspace_objs_of_Some_projections[simp]:
  "vspace_objs_of s p = Some (ASIDPool pool) \<Longrightarrow> asid_pools_of s p = Some pool"
  "vspace_objs_of s p = Some (PageTable pt) \<Longrightarrow> pts_of s p = Some pt"
  (* no projections for data pages *)
  by (auto simp: in_omonad vspace_obj_of_def split: if_splits)

lemma vspace_objs_of_ako_at_Some:
  "(vspace_objs_of s p = Some (PageTable pt)) = ako_at (PageTable pt) p s"
  by (simp add: obj_at_def in_opt_map_eq vspace_obj_of_Some)

lemma valid_vspace_objsI [intro?]:
  "(\<And>p ao asid vref level.
       \<lbrakk> vs_lookup_table level asid (vref_for_level vref (level+1)) s = Some (level, p);
         vref \<in> user_region;
         vspace_objs_of s p = Some ao \<rbrakk>
       \<Longrightarrow> valid_vspace_obj level ao s)
  \<Longrightarrow> valid_vspace_objs s"
  by (fastforce simp: valid_vspace_objs_def dest: vs_lookup_level_vref1)

lemma canonical_address_0[intro!,simp]:
  "canonical_address 0"
  by (simp add: canonical_address_def canonical_address_of_def)

lemma user_region0[intro!,simp]:
  "0 \<in> user_region"
  by (force simp: user_region_def)

lemma ptpte_level_0_valid_pte:
  "is_PageTablePTE pte \<Longrightarrow> \<not> valid_pte 0 pte s"
  by (cases pte; simp)

lemma pool_for_asid_valid_vspace_objs:
  "\<lbrakk> pool_for_asid asid s = Some p;
     valid_vspace_objs s; valid_asid_table s \<rbrakk>
   \<Longrightarrow> \<exists>pool. asid_pools_of s p = Some pool \<and> valid_vspace_obj asid_pool_level (ASIDPool pool) s"
  unfolding valid_vspace_objs_def
  by (fastforce intro: pool_for_asid_vs_lookup[THEN iffD2]
                 dest: pool_for_asid_validD
                 simp: in_opt_map_eq)

lemma vspace_for_asid_valid_pt:
  "\<lbrakk> vspace_for_asid asid s = Some root_pt;
     valid_vspace_objs s; valid_asid_table s \<rbrakk>
   \<Longrightarrow> \<exists>pt. pts_of s root_pt = Some pt \<and> valid_vspace_obj max_pt_level (PageTable pt) s"
  apply (frule vspace_for_asid_vs_lookup)
  apply (clarsimp simp: vspace_for_asid_def entry_for_asid_def)
  apply (frule (2) pool_for_asid_valid_vspace_objs)
  by (fastforce simp: in_opt_map_eq valid_vspace_objs_def vspace_pt_at_eq entry_for_pool_def)

lemma pt_slot_offset_vref:
  "\<lbrakk> level < level'; is_aligned vref (pt_bits_left level') \<rbrakk> \<Longrightarrow>
   pt_slot_offset level pt_ptr vref = pt_ptr"
  apply (simp add: pt_slot_offset_def pt_index_def pt_bits_left_def)
  apply (rule conjI; clarsimp)
  apply word_eqI
  apply (clarsimp simp: bit_simps size_max_pt_level cong: if_cong)
  apply (prop_tac "size level \<le> size max_pt_level", simp)
  apply (simp add: size_max_pt_level split: if_split_asm)
   apply (erule_tac x="(9 + (9 * size level + n))" in allE,
          (erule impE; clarsimp), simp flip: vm_level.size_less)+
  done

lemma pt_slot_offset_vref_for_level_eq:
  "level < level' \<Longrightarrow> pt_slot_offset level pt_ptr (vref_for_level vref level') = pt_ptr"
  by (simp add: vref_for_level_def pt_slot_offset_vref)

lemma vspace_for_pool_None_upd_idem:
  "vspace_for_pool pool_ptr asid ((asid_pools_of s)(p := None)) = Some table_ptr
   \<Longrightarrow> vspace_for_pool pool_ptr asid (asid_pools_of s) = Some table_ptr"
  by (clarsimp simp: vspace_for_pool_def entry_for_pool_def obind_def split: option.splits if_splits)

lemma vs_lookup_max_pt_levelD:
  "vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, root_pt)
   \<Longrightarrow> \<exists>pool_ptr. pool_for_asid asid s = Some pool_ptr \<and>
                  vspace_for_pool pool_ptr asid (asid_pools_of s) = Some root_pt"
  by (clarsimp simp: vs_lookup_table_def)

lemma vs_lookup_max_pt_levelI:
  "\<lbrakk> pool_for_asid asid s = Some pool_ptr;
     vspace_for_pool pool_ptr asid (asid_pools_of s) = Some root_pt \<rbrakk>
   \<Longrightarrow> vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, root_pt)"
  by (clarsimp simp: vs_lookup_table_def in_omonad)

lemma vs_lookup_table_max_pt_level_SomeD:
  "\<lbrakk> vs_lookup_table max_pt_level asid vref s = Some (level, p) \<rbrakk>
   \<Longrightarrow> \<exists>pool. pool_for_asid asid s = Some pool \<and> vspace_for_pool pool asid (asid_pools_of s) = Some p"
  by (clarsimp simp: vs_lookup_table_def in_omonad)

lemma vs_lookup_max_pt_valid:
  "\<lbrakk> vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, root_pt);
     vref \<in> user_region;
     valid_vspace_objs s; valid_asid_table s \<rbrakk>
   \<Longrightarrow> \<exists>pt. pts_of s root_pt = Some pt \<and>
            valid_vspace_obj max_pt_level (PageTable pt) s \<and>
            pt_type pt = VSRootPT_T"
  apply (frule vs_lookup_max_pt_levelD)
  apply clarsimp
  apply (frule (2) pool_for_asid_valid_vspace_objs)
  by (fastforce simp: in_opt_map_eq valid_vspace_objs_def vspace_pt_at_eq vspace_for_pool_def
                      entry_for_pool_def)

lemma aligned_vref_for_level_eq:
  "is_aligned vref (pt_bits_left level) = (vref_for_level vref level = vref)"
  unfolding vref_for_level_def using is_aligned_neg_mask_eq' by blast

lemma is_aligned_pt_bits_pte_bits:
  "is_aligned p (pt_bits pt_t) \<Longrightarrow> is_aligned p pte_bits"
  by (simp add: bit_simps is_aligned_weaken split: if_splits)

lemma pts_of_ptes_of:
  "\<lbrakk> pts_of s p = Some pt; is_aligned p (pt_bits (pt_type pt)) \<rbrakk> \<Longrightarrow>
   \<exists>pte. ptes_of s (pt_type pt) p = Some pte"
  by (clarsimp simp: ptes_of_Some is_aligned_pt_bits_pte_bits)

lemma pt_index_mask_eq:
  "pt_index level vref && mask (ptTranslationBits level) = pt_index level vref"
  by (simp add: pt_index_def bit_simps)

lemma table_index_mask_eq:
  "table_index pt_t p && mask (ptTranslationBits pt_t) = table_index pt_t p"
  by (auto simp add: pt_bits_def bit_simps mask_shiftr_mask_eq)

lemma pt_apply_upd_eq:
  "pt_type pt = level_type level \<Longrightarrow>
   pt_apply (pt_upd pt (table_index (level_type level) p) pte) (pt_index level vref) =
   (if table_index (level_type level) p = pt_index level vref
    then pte
    else pt_apply pt (pt_index level vref))"
  unfolding pt_apply_def pt_upd_def
  using pt_index_mask_eq[of max_pt_level] pt_index_mask_eq[where level=level and vref=vref]
  using table_index_mask_eq[where pt_t=NormalPT_T] table_index_mask_eq[where pt_t=VSRootPT_T]
  apply (cases pt; clarsimp simp: ucast_eq_mask vs_index_ptTranslationBits pt_index_ptTranslationBits)
  apply (prop_tac "level_type level = NormalPT_T", simp add: level_type_def)
  apply (simp del: level_type_eq add: ptTranslationBits_def)
  done

lemma pt_upd_empty_InvalidPTE[simp]:
  "pt_upd (empty_pt pt_t) idx InvalidPTE = empty_pt pt_t"
  by (auto simp: pt_upd_def empty_pt_def split: pt.splits)

lemma is_aligned_table_base_pte_bits[simp]:
  "is_aligned (table_base vs p) pte_bits"
  unfolding pte_bits_def
  by (simp add: bit_simps is_aligned_neg_mask)

lemma pt_index_bounded[simp, intro!]:
  "pt_index level vref \<le> mask (ptTranslationBits level)"
  by (simp add: pt_index_def word_and_le1)

lemma table_index_plus:
  "\<lbrakk> is_aligned pt_ptr (pt_bits pt_t); i \<le> mask (ptTranslationBits pt_t) \<rbrakk> \<Longrightarrow>
   table_index pt_t (pt_ptr + (i << pte_bits)) = i"
  unfolding is_aligned_mask bit_simps
  apply (cases "pt_t = VSRootPT_T \<and> config_ARM_PA_SIZE_BITS_40"; simp only:)
   by (subst word_plus_and_or_coroll; word_bitwise; simp add: word_size)+

lemma pt_slot_offset_offset[simp]:
  "is_aligned pt (pt_bits level) \<Longrightarrow>
   table_index level (pt_slot_offset level pt vref) = pt_index level vref" for level::vm_level
  unfolding pt_slot_offset_def
  by (simp add: table_index_plus)

lemmas pt_slot_offset_minus_eq =
  pt_slot_offset_vref_for_level_eq[where level="level - 1" for level, simplified]

lemma pt_slot_offset_vref_id[simp]:
  "level' \<le> level \<Longrightarrow>
   pt_slot_offset level pt (vref_for_level vref level') =
   pt_slot_offset level pt vref"
  by (rule vref_for_level_pt_slot_offset) (simp add: max_def)

lemma table_base_plus:
  "\<lbrakk> is_aligned pt_ptr (pt_bits pt_t); i \<le> mask (ptTranslationBits pt_t) \<rbrakk> \<Longrightarrow>
   table_base pt_t (pt_ptr + (i << pte_bits)) = pt_ptr"
  unfolding is_aligned_mask bit_simps
  apply (cases "pt_t = VSRootPT_T \<and> config_ARM_PA_SIZE_BITS_40"; simp only:)
   by (subst word_plus_and_or_coroll; word_bitwise; simp add: word_size)+

lemma vs_lookup_slot_level:
  "vs_lookup_slot bot_level asid vref s = Some (level, p) \<Longrightarrow>
   vs_lookup_slot level asid vref s = Some (level, p)"
  apply (clarsimp simp: vs_lookup_slot_def in_omonad)
  apply (drule vs_lookup_level)
  apply (force split: if_splits)
  done

lemma vs_lookup_target_level:
  "vs_lookup_target bot_level asid vref s = Some (level, p) \<Longrightarrow>
   vs_lookup_target level asid vref s = Some (level, p)"
  apply (clarsimp simp: vs_lookup_target_def in_omonad)
  apply (drule vs_lookup_slot_level)
  apply (auto split: if_splits simp: in_omonad)
  done

lemma vs_lookup_slot_vref_for_level:
  "level \<le> bot_level \<Longrightarrow>
   vs_lookup_slot bot_level asid (vref_for_level vref level) = vs_lookup_slot bot_level asid vref"
  apply (simp add: vs_lookup_slot_def vs_lookup_vref_for_level)
  apply (rule ext, rule obind_eqI, rule refl)
  apply (clarsimp dest!: vs_lookup_min_level)
  done

lemma vs_lookup_target_vref_for_level:
  "level \<le> bot_level \<Longrightarrow>
   vs_lookup_target bot_level asid (vref_for_level vref level) = vs_lookup_target bot_level asid vref"
  by (simp add: vs_lookup_target_def vs_lookup_slot_vref_for_level)

lemma pts_of_ko_at:
  "(pts_of s p = Some pt) = ako_at (PageTable pt) p s"
  by (simp add: obj_at_def in_opt_map_eq)

lemma asid_pools_of_ko_at:
  "(asid_pools_of s p = Some ap) = ako_at (ASIDPool ap) p s"
  by (simp add: obj_at_def in_opt_map_eq)

lemma a_type_ArchObj[simp]:
  "a_type (ArchObj ao) = AArch (aa_type ao)"
  by (simp add: a_type_aa_type)

lemma typ_at_aobjs:
  "typ_at (AArch T) p s = (atyps_of s p = Some T)"
  by (auto simp: obj_at_def in_opt_map_eq)

lemma geq_max_pt_level:
  "(max_pt_level \<le> level) = (level = max_pt_level \<or> level = asid_pool_level)"
  by auto

lemma vs_lookup_asid_pool_level_eq:
  "asid_table s' = asid_table s \<Longrightarrow>
   vs_lookup_table asid_pool_level asid vref s' = vs_lookup_table asid_pool_level asid vref s"
  by (simp add: vs_lookup_table_def obind_def pool_for_asid_def split: option.splits)

lemma vs_lookup_max_pt_level_eq:
  "\<lbrakk> asid_table s' = asid_table s; asid_pools_of s' = asid_pools_of s \<rbrakk> \<Longrightarrow>
   vs_lookup_table max_pt_level asid vref s' = vs_lookup_table max_pt_level asid vref s"
  by (clarsimp simp: vs_lookup_table_def obind_def pool_for_asid_def vspace_for_pool_def pt_walk.simps
              split: option.splits)

lemma pt_lookup_slot_from_level_same[simp]:
  "pt_lookup_slot_from_level level level pt vref = oreturn (level, pt_slot_offset level pt vref)"
  by (auto simp: pt_lookup_slot_from_level_def)

lemma pt_walk_split:
  "\<lbrakk> level \<le> level'; level' \<le> top_level \<rbrakk> \<Longrightarrow>
   pt_walk top_level level pt vref = do {
     (level'', pt) \<leftarrow> pt_walk top_level level' pt vref;
     if level'' = level'
     then pt_walk level' level pt vref
     else oreturn (level'', pt)
   }"
  apply (cases "level' = top_level")
   apply simp
  apply (induct top_level arbitrary: pt; clarsimp)
  apply (subst pt_walk.simps)
  apply (subst (2) pt_walk.simps)
  apply (case_tac "level' = top_level - 1")
   apply (simp add: less_le)
   apply (fastforce simp: obind_assoc intro: opt_bind_cong)
  apply (subgoal_tac "level' < top_level -1")
   apply (fastforce simp: obind_assoc intro: opt_bind_cong)
  apply (meson vm_level.minus1_leq not_le less_le)
  done

lemma pt_walk_split_short:
  "\<lbrakk> level \<le> level'; level' \<le> top_level \<rbrakk> \<Longrightarrow>
   pt_walk top_level level pt vref = do {
     (level'', pt) \<leftarrow> pt_walk top_level level' pt vref;
     pt_walk level'' level pt vref
   }"
  apply (cases "level' = top_level")
   apply simp
  apply (induct top_level arbitrary: pt; clarsimp)
  apply (subst pt_walk.simps)
  apply (subst (2) pt_walk.simps)
  apply (case_tac "level' = top_level - 1")
   apply (clarsimp simp: obind_assoc less_le)
   apply (fastforce simp: obind_def pt_walk.simps intro: opt_bind_cong)
  apply (subgoal_tac "level' < top_level -1")
   apply (clarsimp simp: obind_assoc)
   apply (fastforce simp: obind_def pt_walk.simps intro!: opt_bind_cong)
  apply (meson vm_level.minus1_leq not_le less_le)
  done

lemma pt_walk_split_Some:
  "\<lbrakk> level \<le> level'; level' \<le> top_level \<rbrakk> \<Longrightarrow>
   (pt_walk top_level level pt vref ptes = Some (level, pt')) =
   (\<exists>pt''. pt_walk top_level level' pt vref ptes = Some (level', pt'') \<and>
           pt_walk level' level pt'' vref ptes = Some (level, pt'))"
  apply (subst pt_walk_split; assumption?)
  apply (rule iffI; clarsimp simp: in_obind_eq)
  apply (force dest!: pt_walk_min_level simp: in_obind_eq min_def split: if_split_asm)
  done

lemma vs_lookup_split_max_pt_level:
  "level \<le> max_pt_level \<Longrightarrow>
   vs_lookup_table level asid vref = do {
     (level',pt) \<leftarrow> vs_lookup_table max_pt_level asid vref;
     if level' = max_pt_level
     then pt_walk max_pt_level level pt vref \<circ> ptes_of
     else oreturn (level', pt)
   }"
  by (auto simp: vs_lookup_table_def obind_assoc intro!: opt_bind_cong opt_bind_cong_apply)

lemma vs_lookup_split:
  "\<lbrakk> level \<le> level'; level' \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   vs_lookup_table level asid vref =
   do {
      (level'', pt) \<leftarrow> vs_lookup_table level' asid vref;
      if level'' = level'
      then pt_walk level' level pt vref \<circ> ptes_of
      else oreturn (level'', pt)
    }"
  apply (cases "level' < max_pt_level")
   apply (subst vs_lookup_split_max_pt_level, simp)
   apply (subst (2) vs_lookup_split_max_pt_level, simp)
   apply (simp add: obind_assoc split_def)
   apply (subst pt_walk_split, assumption, assumption)
   apply (simp add: obind_comp_dist split_def if_comp_dist cong: if_cong)
   apply (rule opt_bind_cong, rule refl)
   apply clarsimp
   apply (drule vs_lookup_min_level)
   apply simp
  apply (simp add: not_less)
  apply (subst vs_lookup_split_max_pt_level, simp)
  apply (rule opt_bind_cong, rule refl)
  apply clarsimp
  done

lemma vs_lookup_table_split_last_Some:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); level < max_pt_level \<rbrakk>
   \<Longrightarrow> \<exists>p' pte. vs_lookup_table (level+1) asid vref s = Some (level+1, p')
            \<and> ptes_of s (level+1) (pt_slot_offset (level + 1) p' vref) = Some pte
            \<and> p = pptr_from_pte pte
            \<and> is_PageTablePTE pte"
  apply (clarsimp simp: vs_lookup_table_def in_omonad asid_pool_level_eq
                         vm_level_less_max_pt_level)
  apply (subst (asm) pt_walk_split_Some[where level'="level+1"])
    apply (clarsimp simp add: less_imp_le vm_level.plus_one_leq)+
  apply (subst (asm) (2) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_splits)
  done

lemma vs_lookup_split_max_pt_level_Some:
  "level \<le> max_pt_level \<Longrightarrow>
   (vs_lookup_table level asid vref s = Some (level, p)) =
   (\<exists>pt. vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, pt)
         \<and> pt_walk max_pt_level level pt vref (ptes_of s) = Some (level, p))"
  by (auto simp: vs_lookup_table_def in_omonad not_le split: if_split_asm)

lemma vs_lookup_split_Some:
  "\<lbrakk> level \<le> level'; level' \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   (vs_lookup_table level asid vref s = Some (level, p)) =
   (\<exists>pt. vs_lookup_table level' asid vref s = Some (level', pt)
         \<and> pt_walk level' level pt vref (ptes_of s) = Some (level, p))"
  apply (cases "level' < max_pt_level")
   apply (subst vs_lookup_split_max_pt_level_Some, simp)
   apply (subst (2) vs_lookup_split_max_pt_level_Some, simp)
   apply (subst pt_walk_split_Some; assumption?)
   apply fastforce
  apply (simp add: not_less)
  apply (subst vs_lookup_split_max_pt_level_Some; simp)
  done

lemmas vs_lookup_splitD = vs_lookup_split_Some[rotated, THEN iffD1, rotated -1]

lemma valid_vspace_objsD:
  "\<lbrakk> valid_vspace_objs s;
     vs_lookup_table bot_level asid vref s = Some (level, p);
     vref \<in> user_region; vspace_objs_of s p = Some ao \<rbrakk> \<Longrightarrow>
   valid_vspace_obj level ao s"
  by (simp add: valid_vspace_objs_def)

lemma vspace_for_asid_not_normal_pt:
  "\<lbrakk>vspace_for_asid asid s = Some pt; normal_pt_at pt s; valid_vspace_objs s\<rbrakk> \<Longrightarrow> False"
  apply (drule vspace_for_asid_vs_lookup)
  apply (clarsimp simp: pt_at_eq)
  apply (drule (1) valid_vspace_objsD, simp)
   apply (fastforce simp: in_omonad)
  apply clarsimp
  done

(* A static bound on the size of pt_bits. For PA_40 configurations this is 40 (size of the
   PA/IPA address space). For PA_44 configurations, this is 48, because the page tables can
   theoretically translate 48 bits, even though the PA/IPA space is only 44 bits wide *)
definition pt_bits_left_bound :: nat where
  "pt_bits_left_bound \<equiv> if config_ARM_PA_SIZE_BITS_40 then 40 else 48"

lemma pt_bits_left_bound:
  "pt_bits_left level \<le> pt_bits_left_bound"
  apply (simp add: pt_bits_left_def bit_simps pt_bits_left_bound_def)
  apply (rule conjI, clarsimp simp: level_defs)
  apply clarsimp
  apply (subgoal_tac "size level \<le> size max_pt_level")
   apply (simp only: size_max_pt_level split: if_split_asm; linarith)
  apply (simp add: level_defs)
  done

lemma pt_bits_left_le_max_pt_level:
  "level \<le> max_pt_level \<Longrightarrow> pt_bits_left level \<le> pt_bits_left_bound - ptTranslationBits VSRootPT_T"
  apply (simp add: pt_bits_left_def bit_simps pt_bits_left_bound_def)
  apply (rule conjI, clarsimp)
  apply (subgoal_tac "size level \<le> size max_pt_level")
   apply (simp only: size_max_pt_level split: if_split_asm; clarsimp)
  apply (simp add: level_defs)
  done

lemma user_vtop_leq_canonical_user:
  "user_vtop \<le> canonical_user"
  by (simp add: user_vtop_def pptrUserTop_def canonical_user_def mask_def ipa_size_def)

lemma user_vtop_canonical_user:
  "vref < user_vtop \<Longrightarrow> vref \<le> canonical_user"
  using user_vtop_leq_canonical_user by simp

lemma vref_for_level_asid_pool:
  "vref \<le> canonical_user \<Longrightarrow> vref_for_level vref asid_pool_level = 0"
  apply (clarsimp simp: vref_for_level_def pt_bits_left_def asid_pool_level_size bit_simps max_pt_level_def2
                        canonical_user_def canonical_bit_def and_mask_0_iff_le_mask split: if_split_asm)
  apply (fastforce simp add: mask_def elim: order.trans)
  done

lemma vref_for_level_le:
  "vref_for_level vref level \<le> vref"
  by (simp add: vref_for_level_def word_and_le2)

lemma vref_for_level_user_region:
  "vref \<in> user_region \<Longrightarrow> vref_for_level vref level \<in> user_region"
  using vref_for_level_le[of vref level]
  by (simp add: user_region_def)

lemma aligned_vref_for_level[simp]:
  "is_aligned (vref_for_level vref level) (pt_bits_left level)"
  unfolding vref_for_level_def by simp

lemmas pt_walk_0[simp] = pt_walk.simps[where level=0, simplified]

(* The current definition of pptrBaseOffset comes out to 2^39. The number below is the maximum
   alignment this offset allows. We need this to be greater or equal to pt_bits_left max_pt_level *)
definition pptrBaseOffset_alignment :: nat where
  "pptrBaseOffset_alignment \<equiv> 39"

(* sanity check for size *)
lemma pptrBaseOffset_alignment_pt_bits_left[simp, intro!]:
  "pt_bits_left max_pt_level \<le> pptrBaseOffset_alignment"
  by (simp add: bit_simps pt_bits_left_def pptrBaseOffset_alignment_def size_max_pt_level)

(* sanity check for alignment *)
lemma pptrBaseOffset_aligned[simp, intro!]:
  "is_aligned pptrBaseOffset pptrBaseOffset_alignment"
  by (simp add: pptrBaseOffset_alignment_def pptrBaseOffset_def pptrBase_def paddrBase_def
                is_aligned_def)

lemma is_aligned_addrFromPPtr_n:
  "\<lbrakk> is_aligned p n; n \<le> pptrBaseOffset_alignment \<rbrakk> \<Longrightarrow> is_aligned (addrFromPPtr p) n"
  apply (simp add: addrFromPPtr_def)
  apply (erule aligned_sub_aligned)
   apply (erule is_aligned_weaken[OF pptrBaseOffset_aligned])
  apply (simp add: pptrBaseOffset_alignment_def)
  done

lemma is_aligned_addrFromPPtr[intro!]:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (addrFromPPtr p) pageBits"
  by (simp add: is_aligned_addrFromPPtr_n pageBits_def pptrBaseOffset_alignment_def)

lemma pptrTop_ucast_ppn:
  "\<lbrakk> p < pptrTop; is_aligned p pageBits \<rbrakk> \<Longrightarrow>
   ucast (ucast (p >> pageBits)::ppn) = p >> pageBits"
  apply (drule below_pptrTop_ipa_size)
  apply word_eqI
  using ppn_len_def'[unfolded ppn_len_val]
  by (fastforce dest: bit_imp_le_length)

lemma kernel_window_range_addrFromPPtr:
  "p \<in> kernel_window_range \<Longrightarrow> addrFromPPtr p < pptrTop"
  apply (simp add: kernel_window_range_def addrFromPPtr_def pptrBaseOffset_def
                   paddrBase_def pptr_base_def)
  apply unat_arith
  done

lemma kernel_window_addrFromPPtr:
  "\<lbrakk> p \<in> kernel_window_range; is_aligned p pageBits \<rbrakk> \<Longrightarrow>
   ucast (ucast (addrFromPPtr p >> pageBits)::ppn) = addrFromPPtr p >> pageBits"
  apply (rule pptrTop_ucast_ppn)
   apply (erule kernel_window_range_addrFromPPtr)
  apply (erule is_aligned_addrFromPPtr)
  done

lemma is_aligned_ptrFromPAddr_n:
  "\<lbrakk>is_aligned x sz; sz \<le> pptrBaseOffset_alignment\<rbrakk>
   \<Longrightarrow> is_aligned (ptrFromPAddr x) sz"
  unfolding ptrFromPAddr_def
  apply (erule aligned_add_aligned)
   apply (erule is_aligned_weaken[OF pptrBaseOffset_aligned])
  apply (rule order.refl)
  done

lemma is_aligned_pptrBaseOffset_pt_bits_left:
  "level \<le> max_pt_level \<Longrightarrow> is_aligned pptrBaseOffset (pt_bits_left level)"
  by (blast intro: order_trans pt_bits_left_mono is_aligned_weaken)

lemma is_aligned_ptrFromPAddr_n_eq:
  "level \<le> max_pt_level \<Longrightarrow>
   is_aligned (ptrFromPAddr x) (pt_bits_left level) = is_aligned x (pt_bits_left level)"
  apply (rule iffI)
   apply (simp add: ptrFromPAddr_def)
   apply (erule is_aligned_addD2)
   apply (erule is_aligned_pptrBaseOffset_pt_bits_left)
  apply (blast intro: order_trans pt_bits_left_mono is_aligned_ptrFromPAddr_n)
  done

lemma is_aligned_ptrFromPAddr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (ptrFromPAddr p) pageBits"
  by (simp add: is_aligned_ptrFromPAddr_n pageBits_def pptrBaseOffset_alignment_def)

lemma is_aligned_ptrFromPAddr_pt_bits[intro!]:
  "is_aligned p (pt_bits pt_t) \<Longrightarrow> is_aligned (ptrFromPAddr p) (pt_bits pt_t)"
  by (simp add: is_aligned_ptrFromPAddr_n bit_simps pptrBaseOffset_alignment_def)

lemma pspace_aligned_pts_ofD:
  "\<lbrakk> pspace_aligned s; pts_of s pt_ptr = Some pt \<rbrakk> \<Longrightarrow> is_aligned pt_ptr (pt_bits (pt_type pt))"
  by (fastforce dest: pspace_alignedD simp: in_omonad bit_simps)

lemma is_aligned_pt_slot_offset_pte:
  "is_aligned pt (pt_bits pt_t) \<Longrightarrow> is_aligned (pt_slot_offset level pt vref) pte_bits"
  unfolding pt_slot_offset_def
  by (simp add: is_aligned_add bit_simps is_aligned_weaken is_aligned_shift)

lemma pt_slot_offset_pt_range:
  "\<lbrakk> ptes_of s level (pt_slot_offset level pt vref) = Some pte;
     pts_of s pt = Some ptable; is_aligned pt (pt_bits level) \<rbrakk>
   \<Longrightarrow> pte \<in> pt_range ptable"
  for level::vm_level
  by (clarsimp simp: ptes_of_Some)

lemma ucast_ucast_ppn:
  "ucast (ucast ptr::ppn) = ptr && mask ppn_len" for ptr::obj_ref
  by (simp add: ucast_ucast_mask ppn_len_val)

lemma pte_base_addr_PageTablePTE[simp]:
  "pte_base_addr (PageTablePTE ppn) = paddr_from_ppn ppn"
  by (simp add: pte_base_addr_def)

lemma pptr_from_pte_PagePTE[simp]:
  "pptr_from_pte (PagePTE p is_small attr rights) = ptrFromPAddr p"
  by (simp add: pptr_from_pte_def pte_base_addr_def)

lemma valid_vspace_objs_strongD:
  "\<lbrakk> valid_vspace_objs s;
     vs_lookup_table bot_level asid vref s = Some (level, pt_ptr);
     vref \<in> user_region;
     level \<le> max_pt_level;
     valid_asid_table s; pspace_aligned s \<rbrakk> \<Longrightarrow>
   \<exists>pt. pts_of s pt_ptr = Some pt \<and> valid_vspace_obj level (PageTable pt) s \<and>
        pt_type pt = level_type level"
  supply valid_vspace_obj.simps[simp del]
  apply (drule vs_lookup_level)
  apply (induct level arbitrary: pt_ptr rule: vm_level.from_top_induct[where y="max_pt_level"])
   apply simp
   apply (drule (3) vs_lookup_max_pt_valid, simp)
  apply (rename_tac level pt_ptr)
  apply (frule vs_lookup_splitD, assumption)
   apply (simp add: less_imp_le)
  apply (elim exE)
  apply (drule_tac x=pt in meta_spec)
  apply clarsimp
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_split_asm)
  apply (subst (asm) valid_vspace_obj.simps)
  apply (frule (1) pspace_alignedD)
  apply clarsimp
  apply (drule pt_slot_offset_pt_range, fastforce simp: in_omonad, simp add: pt_bits_def)
  apply (drule (1) bspec)
  apply (clarsimp simp: is_PageTablePTE_def pptr_from_pte_def atyp_at_eq_kheap_obj)
  apply (drule (2) valid_vspace_objsD)
   apply (simp add: in_omonad)
  apply (assumption)
  done

lemma level_type_minus_one:
  "level \<le> max_pt_level \<Longrightarrow> level_type (level - 1) = NormalPT_T"
  by (simp add: level_type_def)

lemma pt_bits_NormalPT_T:
  "pt_bits NormalPT_T = pageBits"
  by (simp add: bit_simps)

lemma pptr_from_pte_aligned:
  "is_PageTablePTE pte \<Longrightarrow> is_aligned (pptr_from_pte pte) pageBits"
  apply (clarsimp simp: is_PageTablePTE_def pptr_from_pte_def paddr_from_ppn_def)
  apply (rule is_aligned_ptrFromPAddr)
  apply (simp add: word_eqI_simps)
  done

lemma pptr_from_pte_aligned_pt_bits:
  "\<lbrakk> level \<le> max_pt_level; is_PageTablePTE pte \<rbrakk> \<Longrightarrow>
   is_aligned (pptr_from_pte pte) (pt_bits (level_type (level - 1)))"
  by (drule level_type_minus_one)
     (simp del: level_type_eq add: pt_bits_NormalPT_T pptr_from_pte_aligned)

lemma pt_walk_is_aligned:
  "\<lbrakk> pt_walk level bot_level p vref' ptes = Some (level', p'); level \<le> max_pt_level;
     is_aligned p (pt_bits level) \<rbrakk>
   \<Longrightarrow> is_aligned p' (pt_bits level')"
  apply (induct level arbitrary: p, simp)
  apply (subst (asm) (2) pt_walk.simps)
  apply (fastforce simp: in_omonad pptr_from_pte_aligned_pt_bits split: if_splits)
  done

lemma vspace_for_pool_is_aligned:
  "\<lbrakk> vspace_for_pool pool_ptr asid (asid_pools_of s) = Some pt_ptr;
     pool_for_asid asid s = Some pool_ptr; vref \<in> user_region;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> is_aligned pt_ptr (pt_bits VSRootPT_T)"
  by (drule valid_vspace_objs_strongD[where bot_level=max_pt_level and level=max_pt_level and
                                            asid=asid];
      fastforce simp: vs_lookup_table_def in_omonad dest: pspace_aligned_pts_ofD)

lemma vs_lookup_table_is_aligned:
  "\<lbrakk> vs_lookup_table bot_level asid vref s = Some (level', pt_ptr);
    level' \<le> max_pt_level; vref \<in> user_region; pspace_aligned s;
    valid_asid_table s; valid_vspace_objs s \<rbrakk>
   \<Longrightarrow> is_aligned pt_ptr (pt_bits level')"
  apply (drule (5) valid_vspace_objs_strongD)
  apply (cases "level' = max_pt_level";
         fastforce dest: pspace_alignedD simp: pt_bits_def in_omonad)
  done

lemma kernel_window_user_region_sane:
  "valid_uses s \<Longrightarrow> kernel_window s \<inter> user_window s = {}"
  unfolding window_defs by auto

lemma pte_ref_def2:
  "pte_ref pte = (if pte = InvalidPTE then None else Some (pptr_from_pte pte))"
  by (cases pte) (auto simp: pptr_from_pte_def)

lemma pt_lookup_slot_from_level_rec:
  "pt_lookup_slot_from_level level bot_level pt vptr = do {
     let slot = pt_slot_offset level pt vptr;
     if bot_level < level
     then do {
       pte \<leftarrow> oapply2 (level_type level) slot;
       if is_PageTablePTE pte
         then pt_lookup_slot_from_level (level - 1) bot_level (pptr_from_pte pte) vptr
         else oreturn (level, slot)
     }
     else oreturn (level, slot)
   }"
  unfolding pt_lookup_slot_from_level_def
  apply (induct level arbitrary: pt)
   apply (simp add: pt_walk.simps)
   apply (simp add: oreturn_def)
  apply (simp (no_asm) add: pt_walk.simps)
  apply (fastforce simp: Let_def obind_assoc intro: opt_bind_cong)
  done

lemma arch_tcb_context_absorbs[simp]:
  "arch_tcb_context_set uc2 (arch_tcb_context_set uc1 a_tcb) \<equiv> arch_tcb_context_set uc2 a_tcb"
  by (simp add: arch_tcb_context_set_def)

lemma arch_tcb_context_get_set[simp]:
  "arch_tcb_context_get (arch_tcb_context_set uc a_tcb) = uc"
  by (simp add: arch_tcb_context_get_def arch_tcb_context_set_def)

lemma pte_at_typ_lift:
  assumes "(\<And>T p. f \<lbrace>typ_at (AArch T) p\<rbrace>)"
  shows "f \<lbrace>pte_at pt_t t\<rbrace>"
  unfolding pte_at_def2
  by (wpsimp wp: assms hoare_vcg_conj_lift hoare_vcg_disj_lift)

lemma entry_for_asid_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (entry_for_asid asid s)\<rbrace>"
  unfolding entry_for_asid_def
  apply (simp add: obind_def pool_for_asid_def o_def split del: if_split)
  apply (rule hoare_lift_Pf[where f=asid_table])
   apply (rule hoare_lift_Pf[where f=asid_pools_of])
    apply (wpsimp wp: assms)+
  done

(* P has a different type here compared to the lemma above *)
lemma swp_entry_for_asid_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (\<lambda>asid. entry_for_asid asid s)\<rbrace>"
  unfolding entry_for_asid_def
  apply (simp add: obind_def pool_for_asid_def o_def split del: if_split)
  apply (rule hoare_lift_Pf[where f=asid_table])
   apply (rule hoare_lift_Pf[where f=asid_pools_of])
    apply (wpsimp wp: assms)+
  done

lemma vmid_inv_ap_lift:
  assumes ap[wp]: "(\<And>P. f \<lbrace> \<lambda>s. P (asid_pools_of s) \<rbrace>)"
  assumes arch[wp]: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>vmid_inv\<rbrace>"
  unfolding vmid_inv_def
  apply (rule hoare_lift_Pf[where f=arch_state, rotated], rule arch)
  apply wpsimp
  done

definition is_vcpu :: "kernel_object \<Rightarrow> bool" where
  "is_vcpu \<equiv> \<lambda>ko. \<exists>vcpu. ko = ArchObj (VCPU vcpu)"

lemma obj_at_vcpu_hyp_live_of_s:
  "obj_at (is_vcpu and hyp_live) p s = vcpu_hyp_live_of s p"
  by (auto simp: obj_at_def in_omonad is_vcpu_def hyp_live_def arch_live_def)

lemma obj_at_vcpu_hyp_live_of:
  "obj_at (is_vcpu and hyp_live) p = (\<lambda>s. vcpu_hyp_live_of s p)"
  using obj_at_vcpu_hyp_live_of_s by blast

lemma cur_vcpu_typ_lift:
  assumes vcpus: "\<And>P. f \<lbrace>\<lambda>s. P (vcpu_tcbs_of s)\<rbrace>"
  assumes arch: "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>cur_vcpu\<rbrace>"
  by (rule hoare_lift_Pf[OF vcpus arch])

lemmas abs_atyp_at_lifts =
  valid_pte_lift valid_vspace_obj_typ valid_arch_cap_ref_lift in_user_frame_lift
  valid_arch_cap_typ pte_at_typ_lift

lemma vspace_for_asid_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  unfolding vspace_for_asid_def
  apply (simp add: obind_def pool_for_asid_def o_def split del: if_split)
  apply (rule hoare_lift_Pf[where f=asid_table])
   apply (rule hoare_lift_Pf[where f=asid_pools_of])
    apply (wpsimp wp: assms entry_for_asid_lift split: option.splits split_del: if_split)+
  done

lemma valid_global_arch_objs_lift:
  assumes "\<And>P. f \<lbrace> \<lambda>s. P (global_pt s) \<rbrace>"
  assumes "\<And>p. f \<lbrace> vspace_pt_at p \<rbrace>"
  shows "f \<lbrace> valid_global_arch_objs \<rbrace>"
  unfolding valid_global_arch_objs_def
  by (rule hoare_lift_Pf; rule assms)

lemma valid_arch_state_lift_arch:
  assumes atyp[wp]: "\<And>T p. f \<lbrace> typ_at (AArch T) p\<rbrace>"
  assumes aobjs[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s) \<rbrace>"
  assumes aps[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (pts_of s) \<rbrace>"
  assumes vcpus[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (vcpu_hyp_live_of s)\<rbrace>"
  assumes arch[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>valid_arch_state\<rbrace>"
  apply (simp add: pred_conj_def valid_arch_state_def valid_asid_table_def)
  apply (rule hoare_lift_Pf[where f="arch_state", rotated], rule arch)
  apply (wpsimp wp: dom_asid_pools_of_lift)
    apply blast
   apply (wpsimp wp: vcpus cur_vcpu_typ_lift vmid_inv_ap_lift valid_global_arch_objs_lift)+
  done

lemma aobjs_of_atyp_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace>"
  by (wpsimp simp: typ_at_aobjs wp: assms)

lemma aobjs_of_vcpu_lift:
  assumes [wp]: "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  shows "\<And>p. f \<lbrace>obj_at (is_vcpu and hyp_live) p\<rbrace>"
  by (wpsimp simp: obj_at_vcpu_hyp_live_of)

(* the pt_of projection is not available in generic spec, so we limit what we export
   to a dependency on arch objects *)
lemma valid_arch_state_lift:
  assumes aobjs[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  assumes [wp]: "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift_arch; fastforce intro: aobjs_of_atyp_lift assms)

lemma asid_high_bits_of_and_mask[simp]:
  "asid_high_bits_of (asid && ~~ mask asid_low_bits || ucast (asid_low::asid_low_index)) =
   asid_high_bits_of asid"
  apply (simp add: asid_high_bits_of_def asid_low_bits_def)
  apply word_bitwise
  apply (simp add: word_size)
  done

lemma asid_low_bits_of_and_mask[simp]:
  "asid_low_bits_of (asid && ~~ mask asid_low_bits || ucast (asid_low::asid_low_index)) = asid_low"
  apply (simp add: asid_low_bits_of_def asid_low_bits_def)
  apply word_bitwise
  apply (simp add: word_size)
  done

lemma pool_for_asid_and_mask[simp]:
  "pool_for_asid (asid && ~~ mask asid_low_bits || ucast (asid_low::asid_low_index)) s =
   pool_for_asid asid s"
  by (simp add: pool_for_asid_def)

lemma vs_lookup_table_ap_step:
  "\<lbrakk> vs_lookup_table asid_pool_level asid vref s = Some (asid_pool_level, p);
     asid_pools_of s p = Some ap; \<exists>ap_idx. ap ap_idx = Some entry \<rbrakk> \<Longrightarrow>
   \<exists>asid'. vs_lookup_target asid_pool_level asid' vref s = Some (asid_pool_level, ap_vspace entry)"
  apply (clarsimp simp: vs_lookup_target_def vs_lookup_slot_def in_omonad ran_def)
  apply (rule_tac x="asid && ~~mask asid_low_bits || ucast ap_idx" in exI)
  apply (fastforce simp: vs_lookup_table_def vspace_for_pool_def entry_for_pool_def in_omonad)
  done

locale_abbrev vref_for_index :: "machine_word \<Rightarrow> vm_level \<Rightarrow> vspace_ref" where
  "vref_for_index idx level \<equiv> idx << pt_bits_left level"

locale_abbrev vref_for_level_idx :: "vspace_ref \<Rightarrow> machine_word \<Rightarrow> vm_level \<Rightarrow> vspace_ref" where
  "vref_for_level_idx vref idx level \<equiv> vref_for_level vref (level+1) || vref_for_index idx level"

lemma pt_index_vref_for_level[simp]:
  "\<lbrakk> level \<le> max_pt_level; idx \<le> mask (ptTranslationBits level) \<rbrakk> \<Longrightarrow>
  pt_index level (vref_for_level vref (level + 1) || vref_for_index idx level) = idx"
  using pt_bits_left_bound[of "level"]
  apply (simp add: pt_index_def vref_for_level_def pt_bits_left_bound_def)
  apply word_eqI
  by (auto simp: bit_simps pt_bits_left_def size_max_pt_level plus_one_eq_asid_pool split: if_split_asm)

lemma table_index_pt_slot_offset:
  "\<lbrakk> level \<le> max_pt_level; is_aligned p (pt_bits level);
     idx \<le> mask (ptTranslationBits level) \<rbrakk> \<Longrightarrow>
   table_index level (pt_slot_offset level p (vref_for_level_idx vref idx level)) = idx"
  by simp

lemma vs_lookup_vref_for_level_eq1:
  "vref_for_level vref' (bot_level+1) = vref_for_level vref (bot_level+1) \<Longrightarrow>
   vs_lookup_table bot_level asid vref' = vs_lookup_table bot_level asid vref"
  apply (rule ext)
  apply (clarsimp simp: vs_lookup_table_def obind_def split: option.splits)
  apply (rule conjI; clarsimp)+
  apply (erule pt_walk_vref_for_level_eq[THEN fun_cong])
  apply simp
  done

lemma vref_for_level_idx[simp]:
  "\<lbrakk> level \<le> max_pt_level; idx \<le> mask (ptTranslationBits level) \<rbrakk> \<Longrightarrow>
   vref_for_level (vref_for_level_idx vref idx level) (level + 1) =
   vref_for_level vref (level + 1)"
  apply (simp add: vref_for_level_def pt_bits_left_def plus_one_eq_asid_pool)
  apply (rule conjI, clarsimp)
  apply (rule conjI; clarsimp; word_eqI_solve simp: bit_simps level_defs dest: bit_imp_possible_bit)
  done

lemma vref_for_level_nth[simp]:
  "vref_for_level vref level !! n = (vref !! n \<and> pt_bits_left level \<le> n \<and> n < size vref)"
  by (auto simp: vref_for_level_def word_eqI_simps)

lemma vref_for_level_user_regionD:
  "\<lbrakk> vref_for_level vref level \<in> user_region; level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> vref \<in> user_region"
  using vref_for_level_le[of vref level]
  apply (clarsimp simp: user_region_def vref_for_level_def)
  apply (drule pt_bits_left_le_max_pt_level)
  apply (unfold pt_bits_left_bound_def)
  apply word_bitwise
  by (clarsimp simp: word_size not_less bit_simps canonical_user_def
               split: if_split_asm)

lemma vref_for_level_idx_canonical_user:
  "\<lbrakk> vref \<le> canonical_user; level \<le> max_pt_level;
     idx \<le> mask (ptTranslationBits level);
     level = max_pt_level \<longrightarrow> ucast idx \<notin> invalid_mapping_slots \<rbrakk> \<Longrightarrow>
   vref_for_level_idx vref idx level \<le> canonical_user"
  apply (clarsimp simp: canonical_user_def le_mask_high_bits ipa_size_def word_size split: if_split_asm)
   apply (cases "level = max_pt_level")
    apply (simp add: bit_simps pt_bits_left_def size_max_pt_level asid_pool_level_eq word_size)
    apply (frule bit_imp_possible_bit)
    apply simp
   apply (simp add: bit_simps pt_bits_left_def size_max_pt_level asid_pool_level_eq)
   apply (frule bit_imp_possible_bit)
   apply simp
   apply (drule xt1(11), simp)
   apply (subst (asm) vm_level.size_less[symmetric])
   apply (simp add: size_max_pt_level)
  apply (cases "level = max_pt_level")
   apply (clarsimp simp: bit_simps pt_bits_left_def size_max_pt_level asid_pool_level_eq word_size)
   apply (frule bit_imp_possible_bit)
   apply simp
   apply (prop_tac "idx \<le> mask valid_vs_slot_bits")
    apply (fastforce simp: invalid_mapping_slots_def bit_simps le_mask_high_bits word_size)
   apply (simp add: bit_simps le_mask_high_bits word_size)
  apply (simp add: bit_simps pt_bits_left_def size_max_pt_level asid_pool_level_eq word_size)
  apply (frule bit_imp_possible_bit)
  apply (drule xt1(11), simp)
  apply (subst (asm) vm_level.size_less[symmetric])
  apply (simp add: size_max_pt_level)
  done

lemma vs_lookup_table_pt_step:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); vref \<in> user_region;
     pts_of s p = Some pt; is_aligned p (pt_bits level); level \<le> max_pt_level;
     pte \<in> pt_range pt; pte_ref pte = Some p'; pt_type pt = level_type level;
     valid_pt_range pt \<rbrakk> \<Longrightarrow>
   \<exists>vref'. vs_lookup_target level asid vref' s = Some (level, p') \<and>
           vref' \<in> user_region"
  apply (drule pt_rangeD, erule exE)
  apply (rename_tac idx)
  apply (rule_tac x="vref_for_level_idx vref idx level" in exI)
  apply (simp add: vs_lookup_target_def vs_lookup_slot_def in_omonad)
  apply (rule conjI)
   apply (rule_tac x="pt_slot_offset level p (vref_for_level_idx vref idx level)" in exI)
   apply (rule conjI, clarsimp)
   apply (rule conjI)
    apply (rule_tac x=level in exI)
    apply (rule_tac x=p in exI)
    apply clarsimp
    apply (rule conjI, clarsimp)
    apply (subst vs_lookup_vref_for_level_eq1)
     prefer 2
     apply assumption
    apply simp
   apply (fastforce simp: ptes_of_Some in_omonad is_aligned_pt_slot_offset_pte
                          table_index_pt_slot_offset split: if_split_asm)
  apply (prop_tac "level = max_pt_level \<longrightarrow> ucast idx \<notin> invalid_mapping_slots")
   apply (cases pt; clarsimp simp: valid_pt_range_def)
  apply (simp add: user_region_def vref_for_level_idx_canonical_user)
  done

lemma pte_rights_PagePTE[simp]:
  "pte_rights_of (PagePTE b sm attr r) = r"
  by (simp add: pte_rights_of_def)

lemma pt_lookup_slot_max_pt_level:
  "pt_lookup_slot pt_ptr vref ptes = Some (level, slot) \<Longrightarrow> level \<le> max_pt_level"
  by (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def dest!: pt_walk_max_level)

lemma pageBitsForSize_vmpage_size_of_level[simp]:
  "level \<le> max_page_level \<Longrightarrow> pageBitsForSize (vmsize_of_level level) = pt_bits_left level"
  by (drule max_page_level_enum) (auto simp: vmsize_of_level_def pt_bits_left_def level_defs)

lemma vs_lookup_slot_table:
  "level \<le> max_pt_level \<Longrightarrow>
   vs_lookup_slot level asid vref s = Some (level, pt_slot) =
   (\<exists>pt_ptr. vs_lookup_table level asid vref s = Some (level, pt_ptr) \<and>
             pt_slot = pt_slot_offset level pt_ptr vref)"
  by (clarsimp simp: vs_lookup_slot_def in_omonad) fastforce

lemmas vs_lookup_slot_vref_for_level_eq[simp] = vs_lookup_slot_vref_for_level[OF order_refl]
lemmas vs_lookup_target_vref_for_level_eq[simp] = vs_lookup_target_vref_for_level[OF order_refl]

lemma pool_for_asid_asid_for_level[simp]:
  "pool_for_asid (asid_for_level asid level) = pool_for_asid asid"
  by (clarsimp simp: pool_for_asid_def asid_for_level_def asid_high_bits_of_def mask_shift)

lemma vs_lookup_asid_for_level[simp]:
  "vs_lookup_table level (asid_for_level asid level) vref = vs_lookup_table level asid vref"
  apply (simp add: vs_lookup_table_def)
  apply (rule ext, rule obind_eqI, rule refl)
  apply (clarsimp simp: asid_for_level_def)
  done

lemma vs_lookup_slot_asid_for_level[simp]:
  "vs_lookup_slot level (asid_for_level asid level) vref = vs_lookup_slot level asid vref"
  by (simp add: vs_lookup_slot_def)

lemma vs_lookup_table_eq_lift:
  "\<lbrakk> pts_of s' = pts_of s;
     asid_pools_of s' = asid_pools_of s;
     pool_for_asid asid s' = pool_for_asid asid s \<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref s' = vs_lookup_table level asid vref s"
  unfolding vs_lookup_table_def
  by (auto simp: obind_def split: option.splits)

lemma aobjs_of_non_aobj_upd:
  "\<lbrakk> kheap s p = Some ko; \<not> is_ArchObj ko; \<not> is_ArchObj ko' \<rbrakk>
   \<Longrightarrow> (kheap s)(p \<mapsto> ko') |> aobj_of = aobjs_of s"
  by (rule ext)
     (auto simp: opt_map_def is_ArchObj_def aobj_of_def split: kernel_object.splits if_split_asm)

lemma pool_for_asid_kheap_upd[simp]:
  "pool_for_asid asid (s\<lparr>kheap := kheap'\<rparr>) = pool_for_asid asid s"
  by (simp add: pool_for_asid_def)

lemma valid_vspace_objs_strong_slotD:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, slot); vref \<in> user_region;
     level \<le> max_pt_level;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> \<exists>pte. ptes_of s level slot = Some pte \<and> valid_pte level pte s"
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (rename_tac pt_ptr)
  apply (drule (5) valid_vspace_objs_strongD)
  apply (clarsimp simp: in_omonad ptes_of_Some)
  apply (frule (1) pspace_alignedD, clarsimp)
  apply (fastforce simp: is_aligned_pt_slot_offset_pte simp flip: pt_bits_def)
  done

lemma pt_bits_left_inj[simp]:
  "(pt_bits_left level' = pt_bits_left level) = (level' = level)"
  apply (intro iffI; clarsimp?)
  apply (clarsimp simp: pt_bits_left_def bit_simps
                 split: if_splits)
     by (metis vm_level.size_less_eq diff_is_0_eq' mult_zero_right right_diff_distrib' sum_imp_diff
               zero_neq_numeral)+

lemma pt_walk_stopped:
  "\<lbrakk> pt_walk top_level level top_ptr vref (ptes_of s) = Some (level', pt_ptr);
     level < level'; level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> \<exists>pte. ptes_of s level' (pt_slot_offset level' pt_ptr vref) = Some pte \<and> \<not> is_PageTablePTE pte"
  apply (induct top_level arbitrary: top_ptr; clarsimp)
  apply (subst (asm) (2) pt_walk.simps)
  apply (clarsimp split: if_split_asm)
  done

lemma vs_lookup_table_stopped:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level', pt_ptr); level' \<noteq> level;
    level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
  \<exists>pte. ptes_of s level' (pt_slot_offset level' pt_ptr vref) = Some pte \<and> \<not>is_PageTablePTE pte"
  apply (clarsimp simp: vs_lookup_table_def split: if_split_asm)
  apply (frule pt_walk_min_level)
  apply (clarsimp simp: min_def split: if_split_asm)
  apply (fastforce dest: pt_walk_stopped)
  done

lemma valid_arch_state_asid_table:
  "valid_arch_state s \<Longrightarrow> valid_asid_table s"
  by (simp add: valid_arch_state_def)

lemma valid_arch_state_global_arch_objs[elim!]:
  "valid_arch_state s \<Longrightarrow> valid_global_arch_objs s"
  by (simp add: valid_arch_state_def)

(* VCPU and related symrefs *)

lemma aa_type_vcpuD:
  "aa_type ko = AVCPU \<Longrightarrow> \<exists>v. ko = VCPU v"
  by (clarsimp simp: aa_type_def
               split: arch_kernel_obj.splits if_split_asm)

lemma tcb_hyp_refs_of_simps[simp]:
  "tcb_hyp_refs atcb = tcb_vcpu_refs (tcb_vcpu atcb)"
  by (auto simp: tcb_hyp_refs_def)

lemma tcb_vcpu_refs_of_simps[simp]:
  "tcb_vcpu_refs (Some vc) = {(vc, TCBHypRef)}"
  "tcb_vcpu_refs None = {}"
  by (auto simp: tcb_vcpu_refs_def)

lemma vcpu_tcb_refs_of_simps[simp]:
  "vcpu_tcb_refs (Some tcb) = {(tcb, HypTCBRef)}"
  by (auto simp: vcpu_tcb_refs_def)

lemma hyp_refs_of_rev:
 "(x, TCBHypRef) \<in> hyp_refs_of ko = (\<exists>tcb. ko = TCB tcb \<and> (tcb_vcpu (tcb_arch tcb) = Some x))"
 "(x, HypTCBRef) \<in> hyp_refs_of ko = (\<exists>v. ko = ArchObj (VCPU v) \<and> (vcpu_tcb v = Some x))"
  by (auto simp: hyp_refs_of_def tcb_hyp_refs_def tcb_vcpu_refs_def
                 vcpu_tcb_refs_def refs_of_ao_def
           split: kernel_object.splits arch_kernel_obj.splits option.split)

lemma valid_asid_map_lift_strong:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  shows "f \<lbrace>valid_asid_map\<rbrace>"
  by (wpsimp simp: valid_asid_map_def wp: entry_for_asid_lift assms)

end

locale Arch_asid_table_update_eq = Arch +
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes asid_table: "asid_table (f s) = asid_table s"

locale Arch_p_asid_table_update_eq = Arch_pspace_update_eq + Arch_asid_table_update_eq


context Arch_pspace_update_eq begin

lemma oreturn_state_update[simp]:
  "oreturn x (f s) = oreturn x s"
  by (simp add: oreturn_def)

lemma obj_at_update [iff]:
  "obj_at P p (f s) = obj_at P p s"
  by (fastforce intro: obj_at_pspaceI simp: pspace)

lemma in_user_frame_update[iff]:
  "in_user_frame p (f s) = in_user_frame p s"
  by (simp add: in_user_frame_def pspace)

lemma in_device_frame_update[iff]:
  "in_device_frame p (f s) = in_device_frame p s"
  by (simp add: in_device_frame_def obj_at_def pspace)

lemma valid_pte_update [iff]:
  "valid_pte level pte (f s) = valid_pte level pte s"
  by (cases pte) (auto simp: data_at_def)

lemma valid_vspace_obj_update [iff]:
  "valid_vspace_obj level ao (f s) = valid_vspace_obj level ao s"
  by (cases ao) auto

lemma valid_vcpu_update [iff]:
  "valid_vcpu v (f s) = valid_vcpu v s"
  by (case_tac "vcpu_tcb v") (auto simp: valid_vcpu_def)

lemma valid_vso_at_update [iff]:
  "valid_vso_at level p (f s) = valid_vso_at level p s"
  by (simp add: valid_vso_at_def pspace)

(* FIXME: move to generic *)
lemma get_cap_update [iff]:
  "(fst (get_cap p (f s)) = {(cap, f s)}) = (fst (get_cap p s) = {(cap, s)})"
  apply (simp add: get_cap_def get_object_def bind_assoc
                   exec_gets split_def assert_def pspace)
  apply (clarsimp simp: fail_def)
  apply (case_tac y, simp_all add: assert_opt_def split: option.splits)
      apply (simp_all add: return_def fail_def assert_def bind_def)
  done

(* FIXME: move to generic *)
lemma caps_of_state_update [iff]:
  "caps_of_state (f s) = caps_of_state s"
  by (rule ext) (auto simp: caps_of_state_def)

lemma arch_valid_obj_update:
  "\<And>ao. b = ArchObj ao \<Longrightarrow> arch_valid_obj ao (f s) = arch_valid_obj ao s"
  by (clarsimp simp: arch_valid_obj_def split: arch_kernel_obj.splits)

lemma aobjs_of_update[iff]:
  "aobjs_of (f s) = aobjs_of s"
  by (simp add: pspace)

lemma ptes_of_update[iff]:
  "ptes_of (f s) = ptes_of s"
  by simp

end

context Arch_arch_idle_update_eq begin

lemma global_refs_update [iff]:
  "global_refs (f s) = global_refs s"
  by (simp add: global_refs_def arch idle irq)

end

context Arch_p_asid_table_update_eq begin

lemma pool_for_asid_update[iff]:
  "pool_for_asid asid (f s) = pool_for_asid asid s"
  by (simp add: pool_for_asid_def asid_table)

lemma entry_for_asid_update[iff]:
  "entry_for_asid asid (f s) =  entry_for_asid asid s"
  by (simp add: entry_for_asid_def obind_def oassert_def oreturn_def pspace
           split: option.splits)

lemma vspace_for_asid_update[iff]:
  "vspace_for_asid asid (f s) =  vspace_for_asid asid s"
  by (simp add: vspace_for_asid_def obind_def split: option.splits)

lemma vspace_at_asid_update[iff]:
  "vspace_at_asid asid pt (f s) =  vspace_at_asid asid pt s"
  by (simp add: vspace_at_asid_def)

lemma vmid_for_asid_update[iff]:
  "vmid_for_asid (f s) asid = vmid_for_asid s asid"
  by (simp add: asid_table)

lemma vs_lookup_update [iff]:
  "vs_lookup_table bot_level asid vptr (f s) = vs_lookup_table bot_level asid vptr s"
  by (auto simp: vs_lookup_table_def pspace asid_table obind_def split: option.splits)

lemma vs_lookup_slot_update[iff]:
  "vs_lookup_slot bot_level asid vref (f s) = vs_lookup_slot bot_level asid vref s"
  by (auto simp: vs_lookup_slot_def obind_def split: option.splits)

lemma vs_lookup_target_update[iff]:
  "vs_lookup_target bot_level asid vref (f s) = vs_lookup_target bot_level asid vref s"
  by (simp add: vs_lookup_target_def obind_def pspace split: option.splits)

lemma valid_vs_lookup_update [iff]:
  "valid_vs_lookup (f s) = valid_vs_lookup s"
  by (simp add: valid_vs_lookup_def asid_table)

lemma valid_table_caps_update [iff]:
  "valid_table_caps (f s) = valid_table_caps s"
  by (simp add: valid_table_caps_def asid_table pspace)

lemma valid_asid_table_update [iff]:
  "valid_asid_table (f s) = valid_asid_table s"
  by (simp add: valid_asid_table_def asid_table pspace)

lemma equal_kernel_mappings_update [iff]:
  "equal_kernel_mappings (f s) = equal_kernel_mappings s"
  by (simp add: equal_kernel_mappings_def pspace)

lemma valid_vspace_objs_update [iff]:
  "valid_vspace_objs (f s) = valid_vspace_objs s"
  by (simp add: valid_vspace_objs_def pspace)

lemma valid_arch_caps_update [iff]:
  "valid_arch_caps (f s) = valid_arch_caps s"
  by (simp add: valid_arch_caps_def asid_table)

end

context Arch_arch_update_eq begin

lemma valid_vmid_table_update[iff]:
  "valid_vmid_table (f s) = valid_vmid_table s"
  by (simp add: arch)

end

context Arch_p_arch_update_eq begin

sublocale Arch_p_asid_table_update_eq
  by unfold_locales (simp add: arch)

lemma valid_ioports_update[iff]:
  "valid_ioports (f s) = valid_ioports s"
  by simp

lemma cur_vcpu_update [iff]:
  "cur_vcpu (f s) = cur_vcpu s"
  by (simp add: arch)

lemma vmid_inv_update [iff]:
  "vmid_inv (f s) = vmid_inv s"
  by (simp add: vmid_inv_def arch is_inv_def swp_def)

lemma valid_global_arch_objs_update [iff]:
  "valid_global_arch_objs (f s) = valid_global_arch_objs s"
  by (simp add: valid_global_arch_objs_def arch)

end

declare AARCH64.arch_tcb_context_absorbs[simp]
declare AARCH64.arch_tcb_context_get_set[simp]

setup \<open>Add_Locale_Code_Defs.setup "AARCH64"\<close>
setup \<open>Add_Locale_Code_Defs.setup "AARCH64_A"\<close>

end
