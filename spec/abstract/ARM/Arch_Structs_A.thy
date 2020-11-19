(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
ARM specific data types
*)

chapter "ARM-Specific Data Types"

theory Arch_Structs_A
imports
  "ExecSpec.Arch_Structs_B"
  ExceptionTypes_A
  VMRights_A
  ExecSpec.Arch_Kernel_Config_Lemmas
begin

context Arch begin global_naming ARM_A

text \<open>
This theory provides architecture-specific definitions and datatypes
including architecture-specific capabilities and objects.
\<close>

section \<open>Architecture-specific virtual memory\<close>

text \<open>An ASID is simply a word.\<close>
type_synonym asid = "word32"

datatype vm_attribute = ParityEnabled | PageCacheable | Global | XNever
type_synonym vm_attributes = "vm_attribute set"

section \<open>Architecture-specific capabilities\<close>

text \<open>The ARM kernel supports capabilities for ASID pools and an ASID controller capability,
along with capabilities for page directories, page tables, and page mappings.\<close>

datatype arch_cap =
   ASIDPoolCap obj_ref asid
 | ASIDControlCap
 | PageCap bool obj_ref cap_rights vmpage_size "(asid * vspace_ref) option"
 | PageTableCap obj_ref "(asid * vspace_ref) option"
 | PageDirectoryCap obj_ref "asid option"

lemmas arch_cap_cases =
  arch_cap.induct[where arch_cap=x and P="\<lambda>x'. x = x' \<longrightarrow> P x'" for x P, simplified, rule_format]

lemmas arch_cap_cases_asm =
arch_cap.induct[where arch_cap=x and P="\<lambda>x'. x = x' \<longrightarrow> P x' \<longrightarrow> R" for P R x,
  simplified, rule_format, rotated -1]

definition
  is_page_cap :: "arch_cap \<Rightarrow> bool" where
  "is_page_cap c \<equiv> \<exists>x0 x1 x2 x3 x4. c = PageCap x0 x1 x2 x3 x4"

definition
  asid_high_bits :: nat where
  "asid_high_bits \<equiv> 7"
definition
  asid_low_bits :: nat where
  "asid_low_bits \<equiv> 10 :: nat"
definition
  asid_bits :: nat where
  "asid_bits \<equiv> 17 :: nat"

section \<open>Architecture-specific objects\<close>

text \<open>This section gives the types and auxiliary definitions for the
architecture-specific objects: a page directory entry (@{text "pde"})
contains either an invalid entry, a page table reference, a section
reference, or a super-section reference; a page table entry contains
either an invalid entry, a large page, or a small page mapping;
finally, an architecture-specific object is either an ASID pool, a
page table, a page directory, or a data page used to model user
memory.
\<close>

datatype pde =
   InvalidPDE
 | PageTablePDE obj_ref vm_attributes machine_word
 | SectionPDE obj_ref vm_attributes machine_word cap_rights
 | SuperSectionPDE obj_ref vm_attributes cap_rights

datatype pte =
   InvalidPTE
 | LargePagePTE obj_ref vm_attributes cap_rights
 | SmallPagePTE obj_ref vm_attributes cap_rights

datatype arch_kernel_obj =
   ASIDPool "10 word \<rightharpoonup> obj_ref"
 | PageTable "word8 \<Rightarrow> pte"
 | PageDirectory "12 word \<Rightarrow> pde"
 | DataPage bool vmpage_size

lemmas arch_kernel_obj_cases =
  arch_kernel_obj.induct[where arch_kernel_obj=x and P="\<lambda>x'. x = x' \<longrightarrow> P x'" for x P,
                         simplified, rule_format]

lemmas arch_kernel_obj_cases_asm =
  arch_kernel_obj.induct[where arch_kernel_obj=x and P="\<lambda>x'. x = x' \<longrightarrow> P x' \<longrightarrow> R" for P R x,
                         simplified, rule_format, rotated -1]

definition cte_level_bits :: nat where
  "cte_level_bits \<equiv> 4"

primrec
  arch_obj_size :: "arch_cap \<Rightarrow> nat"
where
  "arch_obj_size (ASIDPoolCap p as) = pageBits"
| "arch_obj_size ASIDControlCap = 0"
| "arch_obj_size (PageCap dev x rs sz as4) = pageBitsForSize sz"
| "arch_obj_size (PageDirectoryCap x as2) = 14"
| "arch_obj_size (PageTableCap x as3) = 10"

primrec
  arch_cap_is_device :: "arch_cap \<Rightarrow> bool"
where
  "arch_cap_is_device (PageCap dev x rs sz as4) = dev"
| "arch_cap_is_device ASIDControlCap = False"
| "arch_cap_is_device (ASIDPoolCap p as) = False"
| "arch_cap_is_device (PageTableCap x as3) = False"
| "arch_cap_is_device (PageDirectoryCap x as2) = False"

definition tcb_bits :: nat where
  "tcb_bits \<equiv> 10"

definition endpoint_bits :: nat where
  "endpoint_bits \<equiv> 4"

definition ntfn_bits :: nat where
  "ntfn_bits \<equiv> 4"

definition untyped_min_bits :: nat where
  "untyped_min_bits \<equiv> 4"

definition untyped_max_bits :: nat where
  "untyped_max_bits \<equiv> 29"

primrec
  arch_kobj_size :: "arch_kernel_obj \<Rightarrow> nat"
where
  "arch_kobj_size (ASIDPool p) = pageBits"
| "arch_kobj_size (PageTable pte) = 10"
| "arch_kobj_size (PageDirectory pde) = 14"
| "arch_kobj_size (DataPage dev sz) = pageBitsForSize sz"

primrec
  aobj_ref :: "arch_cap \<rightharpoonup> obj_ref"
where
  "aobj_ref (ASIDPoolCap p as) = Some p"
| "aobj_ref ASIDControlCap = None"
| "aobj_ref (PageCap dev x rs sz as4) = Some x"
| "aobj_ref (PageDirectoryCap x as2) = Some x"
| "aobj_ref (PageTableCap x as3) = Some x"

primrec (nonexhaustive)
  acap_rights :: "arch_cap \<Rightarrow> cap_rights"
where
 "acap_rights (PageCap dev x rs sz as) = rs"

definition
  acap_rights_update :: "cap_rights \<Rightarrow> arch_cap \<Rightarrow> arch_cap" where
 "acap_rights_update rs ac \<equiv> case ac of
    PageCap dev x rs' sz as \<Rightarrow> PageCap dev x (validate_vm_rights rs) sz as
  | _                   \<Rightarrow> ac"

section \<open>Architecture-specific object types and default objects\<close>

datatype
  aobject_type =
    SmallPageObj
  | LargePageObj
  | SectionObj
  | SuperSectionObj
  | PageTableObj
  | PageDirectoryObj
  | ASIDPoolObj

definition
  arch_is_frame_type :: "aobject_type \<Rightarrow> bool"
where
  "arch_is_frame_type aobj \<equiv> case aobj of
         SmallPageObj \<Rightarrow> True
       | LargePageObj \<Rightarrow> True
       | SectionObj \<Rightarrow> True
       | SuperSectionObj \<Rightarrow> True
       | _ \<Rightarrow> False"

definition
  arch_default_cap :: "aobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> arch_cap" where
 "arch_default_cap tp r n dev \<equiv> case tp of
  SmallPageObj \<Rightarrow> PageCap dev r vm_read_write ARMSmallPage None
  | LargePageObj \<Rightarrow> PageCap dev r vm_read_write ARMLargePage None
  | SectionObj \<Rightarrow> PageCap dev r vm_read_write ARMSection None
  | SuperSectionObj \<Rightarrow> PageCap dev r vm_read_write ARMSuperSection None
  | PageTableObj \<Rightarrow> PageTableCap r None
  | PageDirectoryObj \<Rightarrow> PageDirectoryCap r None
  | ASIDPoolObj \<Rightarrow> ASIDPoolCap r 0" (* unused *)

definition
  default_arch_object :: "aobject_type \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> arch_kernel_obj" where
 "default_arch_object tp dev n \<equiv> case tp of
    SmallPageObj \<Rightarrow> DataPage dev ARMSmallPage
  | LargePageObj \<Rightarrow> DataPage dev ARMLargePage
  | SectionObj \<Rightarrow> DataPage dev ARMSection
  | SuperSectionObj \<Rightarrow> DataPage dev ARMSuperSection
  | PageTableObj \<Rightarrow> PageTable (\<lambda>x. InvalidPTE)
  | PageDirectoryObj \<Rightarrow> PageDirectory (\<lambda>x. InvalidPDE)
  | ASIDPoolObj \<Rightarrow> ASIDPool (\<lambda>_. None)"

type_synonym hw_asid = word8

type_synonym arm_vspace_region_uses = "vspace_ref \<Rightarrow> arm_vspace_region_use"

section \<open>Architecture-specific state\<close>

text \<open>The architecture-specific state for the ARM model
consists of the first level of the ASID table (@{text "arm_asid_table"}), a
map from hardware ASIDs to seL4 ASIDs (@{text "arm_hwasid_table"}),
the next hardware ASID to preempt (@{text "arm_next_asid"}), the
inverse map from seL4 ASIDs to hardware ASIDs (first component of
@{text "arm_asid_map"}), and the address of the page directory and
page tables mapping the shared address space, along with a description
of this space (@{text "arm_global_pd"}, @{text "arm_global_pts"}, and
@{text "arm_kernel_vspace"} respectively).

Hardware ASIDs are only ever associated with seL4 ASIDs that have a
currently active page directory. The second component of
@{text "arm_asid_map"} values is the address of that page directory.
\<close>

end

qualify ARM_A (in Arch)

record arch_state =
  arm_asid_table    :: "7 word \<rightharpoonup> obj_ref"
  arm_hwasid_table  :: "ARM_A.hw_asid \<rightharpoonup> ARM_A.asid"
  arm_next_asid     :: ARM_A.hw_asid
  arm_asid_map      :: "ARM_A.asid \<rightharpoonup> (ARM_A.hw_asid \<times> obj_ref)"
  arm_global_pd     :: obj_ref
  arm_global_pts    :: "obj_ref list"
  arm_kernel_vspace :: ARM_A.arm_vspace_region_uses

end_qualify

context Arch begin global_naming ARM_A

definition
  pd_bits :: "nat" where
  "pd_bits \<equiv> pageBits + 2"

definition
  pt_bits :: "nat" where
  "pt_bits \<equiv> pageBits - 2"


section "Type declarations for invariant definitions"

datatype aa_type =
    AASIDPool
  | APageTable
  | APageDirectory
  | AUserData vmpage_size
  | ADeviceData vmpage_size

definition aa_type :: "arch_kernel_obj \<Rightarrow> aa_type"
where
 "aa_type ao \<equiv> (case ao of
           PageTable pt             \<Rightarrow> APageTable
         | PageDirectory pd         \<Rightarrow> APageDirectory
         | DataPage dev sz          \<Rightarrow> if dev then ADeviceData sz else AUserData sz
         | ASIDPool f               \<Rightarrow> AASIDPool)"


text \<open>For implementation reasons the badge word has differing amounts of bits\<close>
definition
  badge_bits :: nat where
  badge_bits_def [simp]: "badge_bits \<equiv> 28"
end

section "Arch-specific tcb"


qualify ARM_A (in Arch)

(* arch specific part of tcb: this must have a field for user context *)
record arch_tcb =
 tcb_context       :: user_context

end_qualify

context Arch begin global_naming ARM_A

definition
  default_arch_tcb :: arch_tcb where
  "default_arch_tcb \<equiv> \<lparr>
      tcb_context    = new_context\<rparr>"

text \<open>
  Accessors for @{text "tcb_context"} inside @{text "arch_tcb"}. These are later used to
  implement @{text as_user}, i.e.\ need to be compatible with @{text user_monad}.\<close>
definition
  arch_tcb_context_set :: "user_context \<Rightarrow> arch_tcb \<Rightarrow> arch_tcb"
where
  "arch_tcb_context_set uc a_tcb \<equiv> a_tcb \<lparr> tcb_context := uc \<rparr>"

definition
  arch_tcb_context_get :: "arch_tcb \<Rightarrow> user_context"
where
  "arch_tcb_context_get a_tcb \<equiv> tcb_context a_tcb"

(* FIXME: the following means that we break the set/getRegister abstraction
          and should move some of this into the machine interface (same as X64) *)
text \<open>
  Accessors for the user register part of the @{text "arch_tcb"}.
  (Because @{typ "register \<Rightarrow> machine_word"} might not be equal to @{typ user_context}).\<close>
definition
  arch_tcb_set_registers :: "(register \<Rightarrow> machine_word) \<Rightarrow> arch_tcb \<Rightarrow> arch_tcb"
where
  "arch_tcb_set_registers regs a_tcb \<equiv>
    a_tcb \<lparr> tcb_context := UserContext (fpu_state (tcb_context a_tcb)) regs \<rparr>"

definition
  arch_tcb_get_registers :: "arch_tcb \<Rightarrow> register \<Rightarrow> machine_word"
where
  "arch_tcb_get_registers a_tcb \<equiv> user_regs (tcb_context a_tcb)"

end

end
