(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "AARCH64-Specific Data Types"

theory Arch_Structs_A
imports
  "ExecSpec.Arch_Structs_B"
  ExceptionTypes_A
  VMRights_A
  ExecSpec.Arch_Kernel_Config_Lemmas
begin

context begin interpretation Arch .
lemmas [code] = pageBits_def ipa_size_def
end

context Arch begin global_naming AARCH64_A

text \<open>
  This theory provides architecture-specific definitions and datatypes including
  architecture-specific capabilities and objects.
\<close>

section \<open>Architecture-specific capabilities\<close>

text \<open>
  The AARCH64 kernel supports capabilities for ASID pools and an ASID controller capability,
  along with capabilities for virtual memory mappings.
\<close>

datatype arch_cap =
    ASIDPoolCap
      (acap_obj : obj_ref)
      (acap_asid_base : asid)
  | ASIDControlCap
  | FrameCap
      (acap_obj : obj_ref)
      (acap_rights : cap_rights)
      (acap_fsize : vmpage_size)
      (acap_is_device : bool)
      (acap_map_data : "(asid \<times> vspace_ref) option")
  | PageTableCap
      (acap_obj : obj_ref)
      (acap_pt_type : pt_type)
      (acap_map_data : "(asid \<times> vspace_ref) option")
  | VCPUCap
      (acap_obj : obj_ref)


text \<open>Update the mapping data saved in a frame or page table capability.\<close>
definition update_map_data :: "arch_cap \<Rightarrow> (asid \<times> vspace_ref) option \<Rightarrow> arch_cap" where
  "update_map_data cap m \<equiv> case cap of
     FrameCap p R sz dev _  \<Rightarrow> FrameCap p R sz dev m
   | PageTableCap p t _ \<Rightarrow> PageTableCap p t m"


section \<open>Architecture-specific objects\<close>

subsection \<open>Page tables\<close>

(* This datatype does not match up with the executable spec directly:
   This one here models all "things" one can set on a page entry.
   The attributes accessible to users are the ones returned by attribs_from_word. *)
datatype vm_attribute = Global | Execute | Device
type_synonym vm_attributes = "vm_attribute set"

text \<open>
  The C field @{text base_addr} for next-level tables of @{text PagePTE}s is a 36 bit field-high
  value, i.e., a 48-bit word with the bottom 12 bits always set to 0. (They must be 0 due to
  alignment). Since Arm does not specify a name, we are re-using the RISC-V name @{text ppn}
  (physical page number) for the concept of encoding only the significant bits of this address.

  In addition to the bottom 12 bits being 0 (where 12 = @{const pageBits}), we also know that
  the base address of the next level table is a physical address and therefore has the same width
  as intermediate physical addresses (@{const ipa_size}). We can therefore be more precise in the
  encoding here: the significant bits of the next-level page table address go from @{const ipa_size}
  at the top to @{const pageBits} at the bottom. Similar to the ppn on RISC-V we store a word
  of that size, and shift by @{const pageBits} to get the address. This encodes both a size invariant
  and an alignment invariant in the type, which functions like @{text pt_walk} rely on.

  To provide the same field name as in C, we define @{text pte_base_addr} as the main accessor
  function.\<close>
value_type ppn_len = "ipa_size - pageBits"
type_synonym ppn = "ppn_len word"

text \<open>This lemma encodes @{typ ppn_len} value above as a term, so we can use it generically:\<close>
lemma ppn_len_def':
  "ppn_len = ipa_size - pageBits"
  by (simp add: ppn_len_def pageBits_def ipa_size_def Kernel_Config.config_ARM_PA_SIZE_BITS_40_def)

datatype pte =
    InvalidPTE
  | PagePTE
      (pte_page_addr : paddr)
      (pte_is_small_page : bool)
      (pte_attr : vm_attributes)
      (pte_rights : vm_rights)
  | PageTablePTE
      (pte_ppn : ppn)

definition paddr_from_ppn :: "ppn \<Rightarrow> paddr" where
  "paddr_from_ppn addr \<equiv> ucast addr << pageBits"

definition pte_base_addr :: "pte \<Rightarrow> paddr" where
  "pte_base_addr pte \<equiv>
    if is_PageTablePTE pte then paddr_from_ppn (pte_ppn pte) else pte_page_addr pte"

definition ppn_from_pptr :: "obj_ref \<Rightarrow> ppn" where
  "ppn_from_pptr p = ucast (addrFromPPtr p >> pageBits)"

(* Sanity check for page table type sizes -- ptTranslationBits not yet available at definition site *)
lemma vs_index_ptTranslationBits:
  "ptTranslationBits VSRootPT_T = LENGTH(vs_index_len)"
  by (simp add: ptTranslationBits_def vs_index_bits_def)

lemma pt_index_ptTranslationBits:
  "ptTranslationBits NormalPT_T = LENGTH(pt_index_len)"
  by (simp add: ptTranslationBits_def)

(* This could also be a record, but we expect further alternatives to be added for SMMU *)
datatype asid_pool_entry = ASIDPoolVSpace (ap_vmid : "vmid option") (ap_vspace : obj_ref)

type_synonym asid_pool = "asid_low_index \<rightharpoonup> asid_pool_entry"

datatype pt =
    VSRootPT (the_vs : "vs_index \<Rightarrow> pte")
  | NormalPT (the_pt : "pt_index \<Rightarrow> pte")

definition pt_type :: "pt \<Rightarrow> pt_type" where
  "pt_type pt \<equiv> case pt of VSRootPT _ \<Rightarrow> VSRootPT_T | NormalPT _ \<Rightarrow> NormalPT_T"

subsection \<open>VCPU\<close>

type_synonym virq = machine_word

end

qualify AARCH64_A (in Arch)

record  gic_vcpu_interface =
  vgic_hcr  :: word32
  vgic_vmcr :: word32
  vgic_apr  :: word32
  vgic_lr   :: "nat \<Rightarrow> AARCH64_A.virq"

record vcpu =
  vcpu_tcb  :: "obj_ref option"
  vcpu_vgic :: "gic_vcpu_interface"
  vcpu_regs :: "vcpureg \<Rightarrow> machine_word"
  vcpu_vppi_masked :: "vppievent_irq \<Rightarrow> bool"
  vcpu_vtimer :: virt_timer

end_qualify

context Arch begin global_naming AARCH64_A

definition "vcpu_sctlr vcpu \<equiv> vcpu_regs vcpu VCPURegSCTLR"

definition default_gic_vcpu_interface :: gic_vcpu_interface where
  "default_gic_vcpu_interface \<equiv> \<lparr>
      vgic_hcr  = vgicHCREN,
      vgic_vmcr = 0,
      vgic_apr  = 0,
      vgic_lr   = \<lambda>_. 0
   \<rparr>"

definition
  default_vcpu :: vcpu where
  "default_vcpu \<equiv> \<lparr>
      vcpu_tcb    = None,
      vcpu_vgic   = default_gic_vcpu_interface,
      vcpu_regs   = (\<lambda>_. 0) (VCPURegSCTLR := sctlrDefault),
      vcpu_vppi_masked = (\<lambda>_. False),
      vcpu_vtimer = VirtTimer 0
   \<rparr>"

(* produce discriminators and selectors even though no field names are mentioned *)
datatype (discs_sels) arch_kernel_obj =
    ASIDPool asid_pool
  | PageTable pt
  | DataPage bool vmpage_size
  | VCPU vcpu

definition asid_pool_of :: "arch_kernel_obj \<rightharpoonup> asid_pool" where
  "asid_pool_of ko \<equiv> case ko of ASIDPool pool \<Rightarrow> Some pool | _ \<Rightarrow> None"

definition pt_of :: "arch_kernel_obj \<rightharpoonup> pt" where
  "pt_of ko \<equiv> case ko of PageTable pt \<Rightarrow> Some pt | _ \<Rightarrow> None"

definition vcpu_of :: "arch_kernel_obj \<rightharpoonup> vcpu" where
  "vcpu_of ko \<equiv> case ko of VCPU vcpu \<Rightarrow> Some vcpu | _ \<Rightarrow> None"

definition pte_bits :: nat where
  "pte_bits = word_size_bits"

definition table_size :: "pt_type \<Rightarrow> nat" where
  "table_size pt_t = ptTranslationBits pt_t + pte_bits"

definition pt_bits :: "pt_type \<Rightarrow> nat" where
  "pt_bits pt_t \<equiv> table_size pt_t"

(* sanity check *)
lemma ppn_len:
  "LENGTH(ppn_len) = ipa_size - pt_bits NormalPT_T"
  by (simp add: pt_bits_def table_size_def ptTranslationBits_def pte_bits_def word_size_bits_def
                ipa_size_def Kernel_Config.config_ARM_PA_SIZE_BITS_40_def)

primrec arch_obj_size :: "arch_cap \<Rightarrow> nat" where
  "arch_obj_size (ASIDPoolCap _ _) = pageBits"
| "arch_obj_size ASIDControlCap = 0"
| "arch_obj_size (FrameCap _ _ sz _ _) = pageBitsForSize sz"
| "arch_obj_size (PageTableCap _ pt_t _ ) = table_size pt_t"
| "arch_obj_size (VCPUCap _) = vcpuBits"

fun arch_cap_is_device :: "arch_cap \<Rightarrow> bool" where
  "arch_cap_is_device (FrameCap _ _ _ is_dev _) = is_dev"
| "arch_cap_is_device _ = False"

definition cte_level_bits :: nat where
  "cte_level_bits \<equiv> 5"

definition tcb_bits :: nat where
  "tcb_bits \<equiv> 11"

definition endpoint_bits :: nat where
  "endpoint_bits \<equiv> 4"

definition ntfn_bits :: nat where
  "ntfn_bits \<equiv> 5"

definition untyped_min_bits :: nat where
  "untyped_min_bits \<equiv> 4"

definition untyped_max_bits :: nat where
  "untyped_max_bits \<equiv> 47"

primrec arch_kobj_size :: "arch_kernel_obj \<Rightarrow> nat" where
  "arch_kobj_size (ASIDPool _) = pageBits"
| "arch_kobj_size (PageTable pt) = table_size (pt_type pt)"
| "arch_kobj_size (DataPage _ sz) = pageBitsForSize sz"
| "arch_kobj_size (VCPU _) = vcpuBits"

fun aobj_ref :: "arch_cap \<rightharpoonup> obj_ref" where
  "aobj_ref ASIDControlCap = None"
| "aobj_ref c = Some (acap_obj c)"

definition acap_rights_update :: "cap_rights \<Rightarrow> arch_cap \<Rightarrow> arch_cap" where
  "acap_rights_update R acap \<equiv>
    case acap of
      FrameCap ref cR sz dev as \<Rightarrow> FrameCap ref (validate_vm_rights R) sz dev as
    | _ \<Rightarrow> acap"


section \<open>Architecture-specific object types and default objects\<close>

datatype aobject_type =
    SmallPageObj
  | LargePageObj
  | HugePageObj
  | PageTableObj
  | VSpaceObj
  | ASIDPoolObj (* used internally, not on API level *)
  | VCPUObj

definition arch_is_frame_type :: "aobject_type \<Rightarrow> bool" where
  "arch_is_frame_type aobj \<equiv> case aobj of
     SmallPageObj \<Rightarrow> True
   | LargePageObj \<Rightarrow> True
   | HugePageObj \<Rightarrow> True
   | _ \<Rightarrow> False"

definition arch_default_cap :: "aobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> arch_cap" where
  "arch_default_cap tp r n dev \<equiv> case tp of
     SmallPageObj \<Rightarrow> FrameCap r vm_read_write ARMSmallPage dev None
   | LargePageObj \<Rightarrow> FrameCap r vm_read_write ARMLargePage dev None
   | HugePageObj  \<Rightarrow> FrameCap r vm_read_write ARMHugePage dev None
   | PageTableObj \<Rightarrow> PageTableCap r NormalPT_T None
   | VSpaceObj    \<Rightarrow> PageTableCap r VSRootPT_T None
   | VCPUObj      \<Rightarrow> VCPUCap r
   | ASIDPoolObj  \<Rightarrow> ASIDPoolCap r 0" (* unused, but nicer properties when defined *)

definition default_arch_object :: "aobject_type \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> arch_kernel_obj" where
  "default_arch_object tp dev n \<equiv> case tp of
     SmallPageObj \<Rightarrow> DataPage dev ARMSmallPage
   | LargePageObj \<Rightarrow> DataPage dev ARMLargePage
   | HugePageObj  \<Rightarrow> DataPage dev ARMHugePage
   | PageTableObj \<Rightarrow> PageTable (NormalPT (\<lambda>_. InvalidPTE))
   | VSpaceObj    \<Rightarrow> PageTable (VSRootPT (\<lambda>_. InvalidPTE))
   | VCPUObj \<Rightarrow> VCPU default_vcpu
   | ASIDPoolObj  \<Rightarrow> ASIDPool Map.empty"

type_synonym arm_vspace_region_uses = "vspace_ref \<Rightarrow> arm_vspace_region_use"

text \<open>
  The number of levels over all virtual memory tables.
  For AARCH64 in hyp without @{const config_ARM_PA_SIZE_BITS_40}, we have four page table
  levels plus the ASID pool level.

  The top level (with the highest number) contains ASID pools, the next levels contain the
  top-level page tables, and level 1 page tables. The bottom-level page tables (level 0)
  contains only InvalidPTEs or PagePTEs.
\<close>
value_type vm_level = "if config_ARM_PA_SIZE_BITS_40 then 4 else (5::int)"

definition asid_pool_level :: vm_level where
  "asid_pool_level = maxBound"

definition max_pt_level :: vm_level where
  "max_pt_level = asid_pool_level - 1"

definition level_type :: "vm_level \<Rightarrow> pt_type" where
  "level_type level \<equiv> if level = max_pt_level then VSRootPT_T else NormalPT_T"

declare [[coercion_enabled]]
declare [[coercion level_type]]

end

qualify AARCH64_A (in Arch)

section \<open>Architecture-specific state\<close>

record arch_state =
  arm_asid_table :: "asid_high_index \<rightharpoonup> obj_ref"
  arm_kernel_vspace :: "AARCH64_A.arm_vspace_region_uses"
  arm_vmid_table :: "AARCH64_A.vmid \<rightharpoonup> asid"
  arm_next_vmid :: AARCH64_A.vmid
  arm_us_global_vspace :: "obj_ref"
  arm_current_vcpu    :: "(obj_ref \<times> bool) option"
  arm_gicvcpu_numlistregs :: nat


end_qualify

context Arch begin global_naming AARCH64_A

section "Type declarations for invariant definitions"

datatype aa_type =
    AASIDPool
  | APageTable (a_pt_t : pt_type)
  | AVCPU
  | AUserData vmpage_size
  | ADeviceData vmpage_size

definition aa_type :: "arch_kernel_obj \<Rightarrow> aa_type" where
  "aa_type ao \<equiv> case ao of
     PageTable pt    \<Rightarrow> APageTable (pt_type pt)
   | DataPage dev sz \<Rightarrow> if dev then ADeviceData sz else AUserData sz
   | ASIDPool _      \<Rightarrow> AASIDPool
   | VCPU _          \<Rightarrow> AVCPU"

definition badge_bits :: nat where
  "badge_bits \<equiv> 64"

end

section "Arch-specific TCB"

qualify AARCH64_A (in Arch)

text \<open> Arch-specific part of a TCB: this must have at least a field for user context. \<close>
record arch_tcb =
  tcb_context :: user_context
  tcb_vcpu    :: "obj_ref option"

end_qualify

context Arch begin global_naming AARCH64_A

definition default_arch_tcb :: arch_tcb where
  "default_arch_tcb \<equiv> \<lparr>tcb_context = new_context, tcb_vcpu = None\<rparr>"

text \<open>
  Accessors for @{text "tcb_context"} inside @{text "arch_tcb"}. These are later used to
  implement @{text as_user}, i.e.\ need to be compatible with @{text user_monad}.
\<close>
definition arch_tcb_context_set :: "user_context \<Rightarrow> arch_tcb \<Rightarrow> arch_tcb" where
  "arch_tcb_context_set uc a_tcb \<equiv> a_tcb \<lparr> tcb_context := uc \<rparr>"

definition arch_tcb_context_get :: "arch_tcb \<Rightarrow> user_context" where
  "arch_tcb_context_get a_tcb \<equiv> tcb_context a_tcb"

text \<open>
  Accessors for the user register part of the @{text "arch_tcb"}.
  (Because @{typ "register \<Rightarrow> machine_word"} might not be equal to @{typ user_context}).
\<close>
definition arch_tcb_set_registers :: "(register \<Rightarrow> machine_word) \<Rightarrow> arch_tcb \<Rightarrow> arch_tcb" where
  "arch_tcb_set_registers regs a_tcb \<equiv>
    a_tcb \<lparr> tcb_context := UserContext (fpu_state (tcb_context a_tcb)) regs \<rparr>"

definition arch_tcb_get_registers :: "arch_tcb \<Rightarrow> register \<Rightarrow> machine_word" where
  "arch_tcb_get_registers a_tcb \<equiv> user_regs (tcb_context a_tcb)"

end
end
