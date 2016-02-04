(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchInvariants_AI
imports "../LevityCatch_AI"
begin

section "Move this up"

qualify ARM

-- ---------------------------------------------------------------------------
section "Things to Move Up"

(* FIXME: move to spec level *)
(* global data and code of the kernel, not covered by any cap *)
axiomatization
  kernel_data_refs :: "word32 set"

end_qualify

-- ---------------------------------------------------------------------------
section "ARM-specific invariant definitions"

context ARM begin

lemmas aa_type_simps =
  aa_type_def[split_simps arch_kernel_obj.split]


definition
  aobj_at :: "(arch_kernel_obj \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "aobj_at P ref s \<equiv> \<exists>ko. kheap s ref = Some (ArchObj ko) \<and> P ko"

abbreviation
  "ako_at k \<equiv> aobj_at (op = k)"

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
     Arch_Structs_A.ASIDPoolCap r as
       \<Rightarrow> is_aligned as asid_low_bits \<and> as \<le> 2^asid_bits - 1
   | Arch_Structs_A.PageCap r rghts sz mapdata \<Rightarrow> rghts \<in> valid_vm_rights \<and>
     case_option True (wellformed_mapdata sz) mapdata
   | Arch_Structs_A.PageTableCap r (Some mapdata) \<Rightarrow>
     wellformed_mapdata ARMSection mapdata
   | Arch_Structs_A.PageDirectoryCap r (Some asid) \<Rightarrow>
     0 < asid \<and> asid \<le> 2^asid_bits - 1
   | _ \<Rightarrow> True"

lemmas wellformed_acap_simps =
  wellformed_mapdata_def wellformed_acap_def[split_simps arch_cap.split]

abbreviation
  "atyp_at T \<equiv> aobj_at (\<lambda>ob. aa_type ob = T)"

(* this time with typ_at. might lead to confusion, but this is how
   the rest should have been defined.. *)
abbreviation
  "asid_pool_at \<equiv> atyp_at AASIDPool"
abbreviation
  "page_table_at \<equiv> atyp_at APageTable"
abbreviation
  "page_directory_at \<equiv> atyp_at APageDirectory"

definition
  "pde_at p \<equiv> page_directory_at (p && ~~ mask pd_bits)
                  and K (is_aligned p 2)"
definition
  "pte_at p \<equiv> page_table_at (p && ~~ mask pt_bits)
                  and K (is_aligned p 2)"

definition
  valid_arch_cap_ref :: "arch_cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_cap_ref ac s \<equiv> (case ac of
    Arch_Structs_A.ASIDPoolCap r as \<Rightarrow> atyp_at AASIDPool r s
  | Arch_Structs_A.ASIDControlCap \<Rightarrow> True
  | Arch_Structs_A.PageCap r rghts sz mapdata \<Rightarrow> atyp_at (AIntData sz) r s
  | Arch_Structs_A.PageTableCap r mapdata \<Rightarrow> atyp_at APageTable r s
  | Arch_Structs_A.PageDirectoryCap r mapdata\<Rightarrow> atyp_at APageDirectory r s)"

lemmas valid_arch_cap_ref_simps =
  valid_arch_cap_ref_def[split_simps arch_cap.split]

definition
  valid_arch_cap :: "arch_cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_cap ac s \<equiv> (case ac of
    Arch_Structs_A.ASIDPoolCap r as \<Rightarrow>
         atyp_at AASIDPool r s \<and> is_aligned as asid_low_bits
           \<and> as \<le> 2^asid_bits - 1
  | Arch_Structs_A.ASIDControlCap \<Rightarrow> True
  | Arch_Structs_A.PageCap r rghts sz mapdata \<Rightarrow>
    atyp_at (AIntData sz) r s \<and> rghts \<in> valid_vm_rights \<and>
    (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow> 0 < asid \<and> asid \<le> 2^asid_bits - 1
                                             \<and> vmsz_aligned ref sz \<and> ref < kernel_base)
  | Arch_Structs_A.PageTableCap r mapdata \<Rightarrow>
    atyp_at APageTable r s \<and>
    (case mapdata of None \<Rightarrow> True
       | Some (asid, vref) \<Rightarrow> 0 < asid \<and> asid \<le> 2 ^ asid_bits - 1
                                \<and> vref < kernel_base
                                \<and> is_aligned vref (pageBitsForSize ARMSection))
  | Arch_Structs_A.PageDirectoryCap r mapdata \<Rightarrow>
    atyp_at APageDirectory r s \<and>
    case_option True (\<lambda>asid. 0 < asid \<and> asid \<le> 2^asid_bits - 1) mapdata)"

lemmas valid_arch_cap_simps =
  valid_arch_cap_def[split_simps arch_cap.split]

primrec
  acap_class :: "arch_cap \<Rightarrow> capclass"
where
  "acap_class (arch_cap.ASIDPoolCap x y)      = PhysicalClass"
| "acap_class (arch_cap.ASIDControlCap)       = ASIDMasterClass"
| "acap_class (arch_cap.PageCap x y sz z)     = PhysicalClass"
| "acap_class (arch_cap.PageTableCap x y)     = PhysicalClass"
| "acap_class (arch_cap.PageDirectoryCap x y) = PhysicalClass"

definition
  valid_ipc_buffer_cap :: "cap \<Rightarrow> word32 \<Rightarrow> bool"
where
  "valid_ipc_buffer_cap c bufptr \<equiv>
         case c of
              cap.ArchObjectCap (arch_cap.PageCap ref rghts sz mapdata) \<Rightarrow>
                   is_aligned bufptr msg_align_bits

            | _ \<Rightarrow> True"

primrec
  valid_pte :: "Arch_Structs_A.pte \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pte (Arch_Structs_A.InvalidPTE) = \<top>"
| "valid_pte (Arch_Structs_A.LargePagePTE ptr x y) =
   (\<lambda>s. is_aligned ptr pageBits \<and>
        atyp_at (AIntData ARMLargePage) (Platform.ptrFromPAddr ptr) s)"
| "valid_pte (Arch_Structs_A.SmallPagePTE ptr x y) =
   (\<lambda>s. is_aligned ptr pageBits \<and>
        atyp_at (AIntData ARMSmallPage) (Platform.ptrFromPAddr ptr) s)"

primrec
  valid_pde :: "Arch_Structs_A.pde \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pde (Arch_Structs_A.InvalidPDE) = \<top>"
| "valid_pde (Arch_Structs_A.SectionPDE ptr x y z) =
   (\<lambda>s. is_aligned ptr pageBits \<and>
        atyp_at (AIntData ARMSection) (Platform.ptrFromPAddr ptr) s)"
| "valid_pde (Arch_Structs_A.SuperSectionPDE ptr x z) =
   (\<lambda>s. is_aligned ptr pageBits \<and>
        atyp_at (AIntData ARMSuperSection)
               (Platform.ptrFromPAddr ptr) s)"
| "valid_pde (Arch_Structs_A.PageTablePDE ptr x z) =
   (atyp_at APageTable (Platform.ptrFromPAddr ptr))"


definition
  kernel_mapping_slots :: "12 word set" where
 "kernel_mapping_slots \<equiv> {x. x \<ge> ucast (kernel_base >> 20)}"

primrec
  valid_arch_obj :: "arch_kernel_obj \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_obj (Arch_Structs_A.ASIDPool pool) =
   (\<lambda>s. \<forall>x \<in> ran pool. atyp_at  APageDirectory x s)"
| "valid_arch_obj (Arch_Structs_A.PageDirectory pd) =
   (\<lambda>s. \<forall>x \<in> -kernel_mapping_slots. valid_pde (pd x) s)"
| "valid_arch_obj (Arch_Structs_A.PageTable pt) = (\<lambda>s. \<forall>x. valid_pte (pt x) s)"
| "valid_arch_obj (DataPage sz) = \<top>"

definition
  wellformed_pte :: "Arch_Structs_A.pte \<Rightarrow> bool"
where
  "wellformed_pte pte \<equiv> case pte of
     Arch_Structs_A.pte.LargePagePTE p attr r \<Rightarrow>
       ParityEnabled \<notin> attr \<and> r \<in> valid_vm_rights
   | Arch_Structs_A.pte.SmallPagePTE p attr r \<Rightarrow>
       ParityEnabled \<notin> attr \<and> r \<in> valid_vm_rights
   | _ \<Rightarrow> True"

definition
  wellformed_pde :: "Arch_Structs_A.pde \<Rightarrow> bool"
where
  "wellformed_pde pde \<equiv> case pde of
     Arch_Structs_A.pde.PageTablePDE p attr mw \<Rightarrow> attr \<subseteq> {ParityEnabled}
   | Arch_Structs_A.pde.SectionPDE p attr mw r \<Rightarrow> r \<in> valid_vm_rights
   | Arch_Structs_A.pde.SuperSectionPDE p attr r \<Rightarrow> r \<in> valid_vm_rights
   | _ \<Rightarrow> True"

definition
  wellformed_arch_obj :: "arch_kernel_obj \<Rightarrow> bool"
where
  "wellformed_arch_obj ao \<equiv> case ao of
     PageTable pt \<Rightarrow> (\<forall>pte\<in>range pt. wellformed_pte pte)
   | PageDirectory pd \<Rightarrow> (\<forall>pde\<in>range pd. wellformed_pde pde)
   | _ \<Rightarrow> True"

section "Virtual Memory"

definition
  equal_kernel_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
 "equal_kernel_mappings \<equiv> \<lambda>s.
    \<forall>x y pd pd'. ako_at (PageDirectory pd) x s
         \<and> ako_at (PageDirectory pd') y s
       \<longrightarrow> (\<forall>w \<in> kernel_mapping_slots. pd w = pd' w)"

definition
  pde_ref :: "Arch_Structs_A.pde \<Rightarrow> obj_ref option"
where
  "pde_ref pde \<equiv> case pde of
    Arch_Structs_A.PageTablePDE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

datatype vs_ref = VSRef word32 "aa_type option"

definition
  vs_ref_atype :: "vs_ref \<Rightarrow> aa_type option" where
 "vs_ref_atype vsref \<equiv> case vsref of VSRef x atype \<Rightarrow> atype"

definition
  vs_refs :: "arch_kernel_obj \<Rightarrow> (vs_ref \<times> obj_ref) set" where
  "vs_refs \<equiv> \<lambda>ko. case ko of
    (Arch_Structs_A.ASIDPool pool) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  | (Arch_Structs_A.PageDirectory pd) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p)) `
      graph_of (\<lambda>x. if x \<in> kernel_mapping_slots then None else pde_ref (pd x))
  | _ \<Rightarrow> {}"

type_synonym vs_chain = "vs_ref list \<times> obj_ref"
type_synonym 'a rel = "('a \<times> 'a) set"

definition
  vs_lookup1 :: "'z::state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup1 s \<equiv> {((rs,p),(rs',p')). \<exists>ko r. ako_at ko p s
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
  vs_asid_refs :: "(word8 \<rightharpoonup> obj_ref) \<Rightarrow> vs_chain set"
where
  "vs_asid_refs t \<equiv> (\<lambda>(r,p). ([VSRef (ucast r) None], p)) ` graph_of t"

definition
  vs_lookup :: "'z::state_ext state \<Rightarrow> vs_chain set"
where
  "vs_lookup \<equiv> \<lambda>s. vs_lookup_trans s `` vs_asid_refs (arm_asid_table (arch_state s))"

abbreviation
  vs_lookup_abbr :: "vs_ref list \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  ("_ \<rhd> _" [80,80] 81) where
  "rs \<rhd> p \<equiv> \<lambda>s. (rs,p) \<in> vs_lookup s"

abbreviation
  is_reachable_abbr :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" ("\<exists>\<rhd> _" [80] 81) where
  "\<exists>\<rhd> p \<equiv> \<lambda>s. \<exists>ref. (ref \<rhd> p) s"

definition
  valid_arch_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_objs \<equiv> \<lambda>s. \<forall>p rs ao. (rs \<rhd> p) s \<longrightarrow> ako_at ao p s \<longrightarrow> valid_arch_obj ao s"

definition
  pde_ref_pages :: "Arch_Structs_A.pde \<Rightarrow> obj_ref option"
where
  "pde_ref_pages pde \<equiv> case pde of
    Arch_Structs_A.PageTablePDE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | Arch_Structs_A.SectionPDE ptr x y z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | Arch_Structs_A.SuperSectionPDE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  pte_ref_pages :: "Arch_Structs_A.pte \<Rightarrow> obj_ref option"
where
  "pte_ref_pages pte \<equiv> case pte of
    Arch_Structs_A.SmallPagePTE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | Arch_Structs_A.LargePagePTE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  vs_refs_pages :: "arch_kernel_obj \<Rightarrow> (vs_ref \<times> obj_ref) set" where
  "vs_refs_pages \<equiv> \<lambda>ko. case ko of
    (Arch_Structs_A.ASIDPool pool) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  | (Arch_Structs_A.PageDirectory pd) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p)) `
      graph_of (\<lambda>x. if x \<in> kernel_mapping_slots then None else pde_ref_pages (pd x))
  | (Arch_Structs_A.PageTable pt) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageTable), p)) `
      graph_of (pte_ref_pages o pt)
  | _ \<Rightarrow> {}"

definition
  vs_lookup_pages1 :: "'z :: state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup_pages1 s \<equiv> {((rs,p),(rs',p')). \<exists>ko r. ako_at ko p s
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

abbreviation
  vs_lookup_pages_abbr :: "vs_ref list \<Rightarrow> obj_ref \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool"
  ("_ \<unrhd> _" [80,80] 81) where
  "rs \<unrhd> p \<equiv> \<lambda>s. (rs,p) \<in> vs_lookup_pages s"

abbreviation
  is_reachable_pages_abbr :: "obj_ref \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool" ("\<exists>\<unrhd> _" [80] 81) where
  "\<exists>\<unrhd> p \<equiv> \<lambda>s. \<exists>ref. (ref \<unrhd> p) s"

definition
  pde_mapping_bits :: "nat"
where
 "pde_mapping_bits \<equiv> pageBitsForSize ARMSection"

definition
  pte_mapping_bits :: "nat"
where
 "pte_mapping_bits \<equiv> pageBitsForSize ARMSmallPage"

definition
  valid_pte_kernel_mappings :: "Arch_Structs_A.pte \<Rightarrow> vspace_ref
                                   \<Rightarrow> arm_vspace_region_uses \<Rightarrow> bool"
where
 "valid_pte_kernel_mappings pte vref uses \<equiv> case pte of
    Arch_Structs_A.InvalidPTE \<Rightarrow>
        \<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}.
                    uses x \<noteq> ArmVSpaceKernelWindow
  | Arch_Structs_A.SmallPagePTE ptr atts rghts \<Rightarrow>
        Platform.ptrFromPAddr ptr = vref
        \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}. uses x = use)
             \<and> (use = ArmVSpaceKernelWindow
                    \<or> use = ArmVSpaceDeviceWindow))
        \<and> rghts = {}
  | Arch_Structs_A.LargePagePTE ptr atts rghts \<Rightarrow>
        Platform.ptrFromPAddr ptr = (vref && ~~ mask (pageBitsForSize ARMLargePage))
        \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}. uses x = use)
             \<and> (use = ArmVSpaceKernelWindow
                    \<or> use = ArmVSpaceDeviceWindow))
        \<and> rghts = {}"

definition
  valid_pt_kernel_mappings :: "vspace_ref \<Rightarrow> arm_vspace_region_uses \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
where
 "valid_pt_kernel_mappings vref uses obj \<equiv> case obj of
    PageTable pt \<Rightarrow>
        \<forall>x. valid_pte_kernel_mappings
             (pt x) (vref + (ucast x << pte_mapping_bits)) uses
  | _ \<Rightarrow> False"

definition
  valid_pde_kernel_mappings :: "Arch_Structs_A.pde \<Rightarrow> vspace_ref \<Rightarrow> arm_vspace_region_uses \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "valid_pde_kernel_mappings pde vref uses \<equiv> case pde of
    Arch_Structs_A.InvalidPDE \<Rightarrow>
        (\<lambda>s. \<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}.
                    uses x \<noteq> ArmVSpaceKernelWindow)
  | Arch_Structs_A.PageTablePDE ptr _ _ \<Rightarrow>
        aobj_at (valid_pt_kernel_mappings vref uses)
                    (Platform.ptrFromPAddr ptr)
  | Arch_Structs_A.SectionPDE ptr atts _ rghts \<Rightarrow>
        (\<lambda>s. Platform.ptrFromPAddr ptr = vref
             \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}. uses x = use)
                   \<and> (use = ArmVSpaceKernelWindow
                            \<or> use = ArmVSpaceDeviceWindow))
             \<and> rghts = {})
  | Arch_Structs_A.SuperSectionPDE ptr atts rghts \<Rightarrow>
        (\<lambda>s. Platform.ptrFromPAddr ptr = (vref && ~~ mask (pageBitsForSize ARMSuperSection))
             \<and> (\<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}.
                   uses x = ArmVSpaceKernelWindow)
             \<and> rghts = {})"

definition
  valid_pd_kernel_mappings :: "arm_vspace_region_uses \<Rightarrow> 'z::state_ext state
                                    \<Rightarrow> arch_kernel_obj \<Rightarrow> bool"
where
 "valid_pd_kernel_mappings uses \<equiv> \<lambda>s obj.
  case obj of
    PageDirectory pd \<Rightarrow>
      (\<forall>x. valid_pde_kernel_mappings
             (pd x) (ucast x << pde_mapping_bits) uses s)
  | _ \<Rightarrow> False"

definition
  valid_global_pd_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
 "valid_global_pd_mappings \<equiv> \<lambda>s.
  aobj_at (valid_pd_kernel_mappings (arm_kernel_vspace (arch_state s)) s)
    (arm_global_pd (arch_state s)) s"

definition
  valid_ao_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_ao_at p \<equiv> \<lambda>s. \<exists>ao. ako_at ao p s \<and> valid_arch_obj ao s"

definition
  "valid_pde_mappings pde \<equiv> case pde of
    Arch_Structs_A.SectionPDE ptr _ _ _ \<Rightarrow> is_aligned ptr pageBits
  | Arch_Structs_A.SuperSectionPDE ptr _ _ \<Rightarrow> is_aligned ptr pageBits
  | _ \<Rightarrow> True"

definition
  "empty_table S ko \<equiv>
   case ko of
     Arch_Structs_A.PageDirectory pd \<Rightarrow>
       \<forall>x. (\<forall>r. pde_ref (pd x) = Some r \<longrightarrow> r \<in> S) \<and>
            valid_pde_mappings (pd x) \<and>
            (x \<notin> kernel_mapping_slots \<longrightarrow> pd x = Arch_Structs_A.InvalidPDE)
   | Arch_Structs_A.PageTable pt \<Rightarrow>
         pt = (\<lambda>x. Arch_Structs_A.InvalidPTE)
   | _ \<Rightarrow> False"

definition
  "valid_kernel_mappings_if_pd S ko \<equiv> case ko of
    ArchObj (Arch_Structs_A.PageDirectory pd) \<Rightarrow>
        \<forall>x r. pde_ref (pd x) = Some r
                  \<longrightarrow> ((r \<in> S) = (x \<in> kernel_mapping_slots))
  | _ \<Rightarrow> True"

definition
  "aligned_pte pte \<equiv>
     case pte of
       Arch_Structs_A.LargePagePTE p _ _ \<Rightarrow> vmsz_aligned p ARMLargePage
     | Arch_Structs_A.SmallPagePTE p _ _ \<Rightarrow> vmsz_aligned p ARMSmallPage
     | _ \<Rightarrow> True"

lemmas aligned_pte_simps[simp] =
       aligned_pte_def[split_simps Arch_Structs_A.pte.split]


definition
  valid_global_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_global_objs \<equiv>
  \<lambda>s. valid_ao_at (arm_global_pd (arch_state s)) s \<and>
           aobj_at (empty_table (set (arm_global_pts (arch_state s))))
                  (arm_global_pd (arch_state s)) s \<and>
      (\<forall>p\<in>set (arm_global_pts (arch_state s)).
          \<exists>pt. ako_at (PageTable pt) p s \<and> (\<forall>x. aligned_pte (pt x)))"

definition
  valid_asid_table :: "(word8 \<rightharpoonup> obj_ref) \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_asid_table table \<equiv> \<lambda>s. (\<forall>p \<in> ran table. asid_pool_at p s) \<and>
                                inj_on table (dom table)"

definition
  valid_global_pts :: "'z :: state_ext state \<Rightarrow> bool"
where
  "valid_global_pts \<equiv> \<lambda>s.
   \<forall>p \<in> set (arm_global_pts (arch_state s)). atyp_at APageTable p s"
(* this property now follows from valid_global_objs:
   "valid_global_objs s \<Longrightarrow> valid_global_pts s" *)

definition
  valid_arch_state :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_state \<equiv> \<lambda>s.
  atyp_at (AIntData ARMSmallPage) (arm_globals_frame (arch_state s)) s \<and>
  valid_asid_table (arm_asid_table (arch_state s)) s \<and>
  page_directory_at (arm_global_pd (arch_state s)) s \<and>
  valid_global_pts s \<and>
  is_inv (arm_hwasid_table (arch_state s))
             (option_map fst o arm_asid_map (arch_state s))"

definition
  vs_cap_ref :: "arch_cap \<Rightarrow> vs_ref list option"
where
  "vs_cap_ref cap \<equiv> case cap of
   Arch_Structs_A.ASIDPoolCap _ asid \<Rightarrow>
     Some [VSRef (ucast (asid_high_bits_of asid)) None]
 | Arch_Structs_A.PageDirectoryCap _ (Some asid) \<Rightarrow>
     Some [VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Arch_Structs_A.PageTableCap _ (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Arch_Structs_A.PageCap word rights ARMSmallPage (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 12) && mask 8) (Some APageTable),
           VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Arch_Structs_A.PageCap word rights ARMLargePage (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef ((vptr >> 12) && mask 8) (Some APageTable),
           VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Arch_Structs_A.PageCap word rights ARMSection (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Arch_Structs_A.PageCap word rights ARMSuperSection (Some (asid, vptr)) \<Rightarrow>
     Some [VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | _ \<Rightarrow> None"

definition
  "is_pg_cap cap \<equiv> \<exists>p R sz m. cap =
   arch_cap.PageCap p R sz m"

definition
  "is_pd_cap c \<equiv>
   \<exists>p asid. c = arch_cap.PageDirectoryCap p asid"

definition
  "is_pt_cap c \<equiv> \<exists>p asid. c = arch_cap.PageTableCap p asid"

definition
  "cap_asid cap \<equiv> case cap of
    Arch_Structs_A.PageCap _ _ _ (Some (asid, _)) \<Rightarrow> Some asid
  | Arch_Structs_A.PageTableCap _ (Some (asid, _)) \<Rightarrow> Some asid
  | Arch_Structs_A.PageDirectoryCap _ (Some asid) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

definition
  arch_caps_of_state :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> arch_cap option"
where
 "arch_caps_of_state s \<equiv> (\<lambda>p. if (\<exists>acap. fst (get_cap p s) = {(ArchObjectCap acap, s)})
                         then Some (THE acap. fst (get_cap p s) = {(ArchObjectCap acap, s)})
                         else None)"

  (* needed for retype: if reachable, then cap, if cap then protected by untyped cap.
     strengthened for preservation in cap delete: ref in cap must unmap the right objects *)
definition
  "valid_vs_lookup \<equiv> \<lambda>s. \<forall>p ref. (ref \<unrhd> p) s \<longrightarrow>
  ref \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None] \<and>
  (\<exists>p' acap. arch_caps_of_state s p' = Some acap \<and>
            aobj_ref acap = Some p \<and> vs_cap_ref acap = Some ref)"

definition
  global_refs :: "'z::state_ext state \<Rightarrow> obj_ref set"
where
  "global_refs \<equiv> \<lambda>s.
  {idle_thread s, arm_globals_frame (arch_state s), arm_global_pd (arch_state s)} \<union>
   range (interrupt_irq_node s) \<union>
   set (arm_global_pts (arch_state s))"

definition
  kernel_window :: "'z::state_ext state \<Rightarrow> obj_ref set"
where
  "kernel_window s \<equiv> {x. arm_kernel_vspace (arch_state s) x \<noteq> ArmVSpaceKernelWindow}"


  (* needed for map: installing new object should add only one mapping *)
definition
  "valid_table_caps \<equiv> \<lambda>s.
  \<forall>r p acap. arch_caps_of_state s p = Some acap \<longrightarrow>
            (is_pd_cap acap \<or> is_pt_cap acap) \<longrightarrow>
            cap_asid acap = None \<longrightarrow>
            aobj_ref acap = Some r \<longrightarrow>
            aobj_at (empty_table (set (arm_global_pts (arch_state s)))) r s"

  (* needed to preserve valid_table_caps in map *)
definition
  "unique_table_caps \<equiv> \<lambda>cs. \<forall>p p' cap cap'.
  cs p = Some cap \<longrightarrow> cs p' = Some cap' \<longrightarrow>
  cap_asid cap = None \<longrightarrow>
  aobj_ref cap' = aobj_ref cap \<longrightarrow>
  (is_pd_cap cap \<longrightarrow> is_pd_cap cap' \<longrightarrow> p' = p) \<and>
  (is_pt_cap cap \<longrightarrow> is_pt_cap cap' \<longrightarrow> p' = p)"

definition
  table_cap_ref :: "arch_cap \<Rightarrow> vs_ref list option"
where
  "table_cap_ref cap \<equiv> case cap of
     Arch_Structs_A.ASIDPoolCap _ asid \<Rightarrow>
       Some [VSRef (ucast (asid_high_bits_of asid)) None]
   | Arch_Structs_A.PageDirectoryCap _ (Some asid) \<Rightarrow>
       Some [VSRef (asid && mask asid_low_bits) (Some AASIDPool),
             VSRef (ucast (asid_high_bits_of asid)) None]
   | Arch_Structs_A.PageTableCap _ (Some (asid, vptr)) \<Rightarrow>
       Some [VSRef (vptr >> 20) (Some APageDirectory),
             VSRef (asid && mask asid_low_bits) (Some AASIDPool),
             VSRef (ucast (asid_high_bits_of asid)) None]
   | _ \<Rightarrow> None"

  (* needed to avoid a single page insertion
     resulting in multiple valid lookups *)
definition
  "unique_table_refs \<equiv> \<lambda>cs. \<forall>p p' cap cap'.
  cs p = Some cap \<longrightarrow> cs p' = Some cap' \<longrightarrow>
  aobj_ref cap' = aobj_ref cap \<longrightarrow>
  table_cap_ref cap' = table_cap_ref cap"

definition
  valid_kernel_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_kernel_mappings \<equiv>
     \<lambda>s. \<forall>ko \<in> ran (kheap s).
          valid_kernel_mappings_if_pd
             (set (arm_global_pts (arch_state s))) ko"

definition
  "valid_arch_caps \<equiv> valid_vs_lookup and valid_table_caps and
                     (\<lambda>s. unique_table_caps (arch_caps_of_state s)
                        \<and> unique_table_refs (arch_caps_of_state s))"

definition
  "valid_machine_state \<equiv>
   \<lambda>s. \<forall>p. in_user_frame p (s::'z::state_ext state) \<or> underlying_memory (machine_state s) p = 0"

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
    AASIDPool \<Rightarrow> arch_kobj_size (Arch_Structs_A.ASIDPool undefined)
  | AIntData sz \<Rightarrow> arch_kobj_size (DataPage sz)
  | APageDirectory \<Rightarrow> arch_kobj_size (Arch_Structs_A.PageDirectory undefined)
  | APageTable \<Rightarrow> arch_kobj_size (Arch_Structs_A.PageTable undefined))"

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

lemmas vs_ref_atype_simps[simp] = vs_ref_atype_def[split_simps vs_ref.split]

lemma vs_lookup1_obj_at:
  "((rs,p) \<rhd>1 (r # rs,p')) s = aobj_at (\<lambda>ko. (r, p') \<in> vs_refs ko) p s"
  by (fastforce simp: vs_lookup1_def aobj_at_def)

lemma vs_lookup1I:
  "\<lbrakk> ako_at ko p s; (r, p') \<in> vs_refs ko;
          rs' = r # rs \<rbrakk> \<Longrightarrow> ((rs,p) \<rhd>1 (rs',p')) s"
  by (fastforce simp add: vs_lookup1_def)

lemma vs_lookup1D:
  "(x \<rhd>1 y) s \<Longrightarrow> \<exists>rs r p p' ko. x = (rs,p) \<and> y = (r # rs,p')
                          \<and> ako_at ko p s \<and> (r,p') \<in> vs_refs ko"
  by (cases x, cases y) (fastforce simp: vs_lookup1_def)

lemma vs_lookup_pages1D:
  "(x \<unrhd>1 y) s \<Longrightarrow> \<exists>rs r p p' ko. x = (rs,p) \<and> y = (r # rs,p')
                          \<and> ako_at ko p s \<and> (r,p') \<in> vs_refs_pages ko"
  by (cases x, cases y) (fastforce simp: vs_lookup_pages1_def)

lemma vs_lookup1_stateI:
  assumes 1: "(r \<rhd>1 r') s"
  assumes ko: "\<And>ko. ako_at ko (snd r) s \<Longrightarrow> aobj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') (snd r) s'"
  shows "(r \<rhd>1 r') s'" using 1 ko
  by (fastforce simp: aobj_at_def vs_lookup1_def)

lemma vs_lookup_trans_sub:
  assumes ko: "\<And>ko p. ako_at ko p s \<Longrightarrow> aobj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  shows "vs_lookup_trans s \<subseteq> vs_lookup_trans s'"
proof -
  have "vs_lookup1 s \<subseteq> vs_lookup1 s'"
    by (fastforce dest: ko elim: vs_lookup1_stateI)
  thus ?thesis by (rule rtrancl_mono)
qed

lemma vs_lookup_sub:
  assumes ko: "\<And>ko p. ako_at ko p s \<Longrightarrow> aobj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
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
  assumes ko: "\<And>ko. ako_at ko (snd r) s \<Longrightarrow> aobj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') (snd r) s'"
  shows "(r \<unrhd>1 r') s'" using 1 ko
  by (fastforce simp: aobj_at_def vs_lookup_pages1_def)

lemma vs_lookup_pages_trans_sub:
  assumes ko: "\<And>ko p. ako_at ko p s \<Longrightarrow>
                      aobj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  shows "vs_lookup_pages_trans s \<subseteq> vs_lookup_pages_trans s'"
proof -
  have "vs_lookup_pages1 s \<subseteq> vs_lookup_pages1 s'"
    by (fastforce simp add: ko elim: vs_lookup_pages1_stateI)
  thus ?thesis by (rule rtrancl_mono)
qed

lemma vs_lookup_pages_sub:
  assumes ko: "\<And>ko p. ako_at ko p s \<Longrightarrow>
                      aobj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
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
  assumes ko: "\<And>ko p. ako_at ko p s \<Longrightarrow> aobj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "(ref \<rhd> p) s'"
  using 1 vs_lookup_sub [OF ko table] by blast

lemma valid_arch_objsD:
  "\<lbrakk> (ref \<rhd> p) s; ako_at ao p s; valid_arch_objs s \<rbrakk> \<Longrightarrow> valid_arch_obj ao s"
  by (fastforce simp add: valid_arch_objs_def)

(* should work for unmap and non-arch ops *)
lemma valid_arch_objs_stateI:
  assumes 1: "valid_arch_objs s"
  assumes ko: "\<And>ko p. ako_at ko p s' \<Longrightarrow> aobj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s"
  assumes arch: "graph_of (arm_asid_table (arch_state s')) \<subseteq> graph_of (arm_asid_table (arch_state s))"
  assumes vao: "\<And>p ref ao'.
                \<lbrakk> (ref \<rhd> p) s; (ref \<rhd> p) s'; \<forall>ao. ako_at ao p s \<longrightarrow> valid_arch_obj ao s;
                  ako_at ao' p s' \<rbrakk> \<Longrightarrow> valid_arch_obj ao' s'"
  shows "valid_arch_objs s'"
  using 1 unfolding valid_arch_objs_def
  apply clarsimp
  apply (frule vs_lookup_stateI)
    apply (erule ko)
   apply (rule arch)
  apply (erule allE, erule impE, fastforce)
  apply (erule (3) vao)
  done

lemma aobj_at_pspaceI:
  "\<lbrakk> aobj_at P ref s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> aobj_at P ref s'"
  by (simp add: aobj_at_def)


lemma valid_arch_cap_atyp:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (atyp_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (atyp_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_arch_cap c s\<rbrace> f \<lbrace>\<lambda>rv s. valid_arch_cap c s\<rbrace>"
  apply (simp add: valid_arch_cap_def)
  apply (case_tac c, simp_all)
  by (wp P)

lemma valid_arch_obj_atyp:
  assumes P: "\<And>P p T. \<lbrace>\<lambda>s. P (atyp_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (atyp_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_arch_obj ob s\<rbrace> f \<lbrace>\<lambda>rv s. valid_arch_obj ob s\<rbrace>"
  apply (cases ob, simp_all)
     apply (rule hoare_vcg_const_Ball_lift [OF P])
    apply (rule hoare_vcg_all_lift)
    apply (rename_tac "fun" x)
    apply (case_tac "fun x", simp_all add: hoare_vcg_prop P)
  apply (rule hoare_vcg_ball_lift)
  apply (rename_tac "fun" x)
  apply (case_tac "fun x", simp_all add: hoare_vcg_prop P)
  apply (rule P)
  done

lemma atyp_at_eq_kheap_obj:
  "atyp_at AASIDPool p s \<longleftrightarrow>
   (\<exists>f. kheap s p = Some (ArchObj (Arch_Structs_A.ASIDPool f)))"
  "atyp_at APageTable p s \<longleftrightarrow>
   (\<exists>pt. kheap s p = Some (ArchObj (PageTable pt)))"
  "atyp_at APageDirectory p s \<longleftrightarrow>
   (\<exists>pd. kheap s p = Some (ArchObj (PageDirectory pd)))"
  "atyp_at (AIntData sz) p s \<longleftrightarrow>
   (kheap s p = Some (ArchObj (DataPage sz)))"
apply (auto simp add: aobj_at_def)
apply (simp_all add: aa_type_def split: split_if_asm  arch_kernel_obj.splits)
done

lemma aa_type_AASIDPoolE:
  "\<lbrakk>aa_type ko = AASIDPool;
    (\<And>ap. ko = (arch_kernel_obj.ASIDPool ap) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (case_tac ko, simp_all add: aa_type_simps split: split_if_asm)

lemma aa_type_APageDirectoryE:
  "\<lbrakk>aa_type ko = APageDirectory;
    (\<And>pd. ko = PageDirectory pd \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (case_tac ko, simp_all add: aa_type_simps split: split_if_asm)

lemma aa_type_APageTableE:
  "\<lbrakk>aa_type ko = APageTable; (\<And>pt. ko = PageTable pt \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (case_tac ko, simp_all add: aa_type_simps split: split_if_asm)

lemma aa_type_AIntDataE:
  "\<lbrakk>aa_type ko = AIntData sz; ko = DataPage sz \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: aa_type_simps split: split_if_asm)



lemmas a_type_elims[elim!] =
   aa_type_AASIDPoolE aa_type_APageDirectoryE aa_type_APageTableE aa_type_AIntDataE

end

end
