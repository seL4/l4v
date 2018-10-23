(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "RISCV64-Specific Data Types"

theory Arch_Structs_A
imports
  "ExecSpec.Arch_Structs_B"
  "../ExceptionTypes_A"
  "../VMRights_A"
begin

context Arch begin global_naming RISCV64_A

text \<open>
  This theory provides architecture-specific definitions and datatypes including
  architecture-specific capabilities and objects.
\<close>

section \<open>Architecture-specific capabilities\<close>

text \<open>
  The RISCV64 kernel supports capabilities for ASID pools and an ASID controller capability,
  along with capabilities for virtual memory mappings.
\<close>

datatype arch_cap =
    ASIDPoolCap (acap_obj : obj_ref) (acap_asid_base : asid)
  | ASIDControlCap
  | FrameCap
      (acap_obj : obj_ref)
      (acap_rights : cap_rights)
      (acap_fsize : vmpage_size)
      (acap_is_device : bool)
      (acap_map_data : "(asid \<times> vspace_ref) option")
  | PageTableCap (acap_obj : obj_ref) (acap_map_data : "(asid \<times> vspace_ref) option")


text \<open>Update the mapping data saved in a frame or page table capability.\<close>
definition update_map_data :: "arch_cap \<Rightarrow> (asid \<times> vspace_ref) option \<Rightarrow> arch_cap"
  where
  "update_map_data cap m \<equiv> case cap of
     FrameCap p R sz dev _  \<Rightarrow> FrameCap p R sz dev m
   | PageTableCap p _ \<Rightarrow> PageTableCap p m"


section \<open>Architecture-specific objects\<close>

(* This datatype does not match up with the executable spec directly:
   This one here models all "things" one can set on a page or page table entry.
   The attributes accessible to users are the ones returned by attribs_from_word,
   the ones not applicable to page tables are returned by page_only_attrs. *)
datatype vm_attribute = Global | Execute | User
type_synonym vm_attributes = "vm_attribute set"

definition page_only_attrs :: "vm_attributes"
  where
  "page_only_attrs = {Global}"

datatype pte =
    InvalidPTE
  | PagePTE (pte_ppn : machine_word) (pte_attr : vm_attributes) (pte_rights : vm_rights)
  | PageTablePTE (pte_ppn : machine_word) (pte_attr : vm_attributes)

type_synonym pt_index_len = 9
type_synonym pt_index = "pt_index_len word"

text \<open>Sanity check:\<close>
lemma "LENGTH(pt_index_len) = ptTranslationBits"
  by (simp add: ptTranslationBits_def)

type_synonym asid_pool = "asid_low_index \<rightharpoonup> obj_ref"
type_synonym pt = "pt_index \<Rightarrow> pte"

(* produce discriminators and selectors even though no field names are mentioned *)
datatype (discs_sels) arch_kernel_obj =
    ASIDPool asid_pool
  | PageTable pt
  | DataPage bool vmpage_size

definition asid_pool_of :: "arch_kernel_obj \<rightharpoonup> asid_pool"
  where
  "asid_pool_of ko \<equiv> case ko of ASIDPool pool \<Rightarrow> Some pool | _ \<Rightarrow> None"

definition pt_of :: "arch_kernel_obj \<rightharpoonup> pt"
  where
  "pt_of ko \<equiv> case ko of PageTable pt \<Rightarrow> Some pt | _ \<Rightarrow> None"

definition pte_bits :: nat
  where
  "pte_bits = word_size_bits"

definition table_size :: nat
  where
  "table_size = ptTranslationBits + pte_bits"

definition pt_bits :: "nat"
  where
  "pt_bits \<equiv> table_size"

primrec arch_obj_size :: "arch_cap \<Rightarrow> nat"
  where
  "arch_obj_size (ASIDPoolCap _ _) = pageBits"
| "arch_obj_size ASIDControlCap = 0"
| "arch_obj_size (FrameCap _ _ sz _ _) = pageBitsForSize sz"
| "arch_obj_size (PageTableCap _ _ ) = table_size"

fun arch_cap_is_device :: "arch_cap \<Rightarrow> bool"
  where
  "arch_cap_is_device (FrameCap _ _ _ is_dev _) = is_dev"
| "arch_cap_is_device _ = False"

definition cte_level_bits :: nat
  where
  "cte_level_bits \<equiv> 5"

definition tcb_bits :: nat
  where
  "tcb_bits \<equiv> 11"

definition endpoint_bits :: nat
  where
  "endpoint_bits \<equiv> 4"

definition ntfn_bits :: nat
  where
  "ntfn_bits \<equiv> 5"

definition untyped_min_bits :: nat
  where
  "untyped_min_bits \<equiv> 4"

definition untyped_max_bits :: nat
  where
  "untyped_max_bits \<equiv> 47"

primrec arch_kobj_size :: "arch_kernel_obj \<Rightarrow> nat"
  where
  "arch_kobj_size (ASIDPool _) = pageBits"
| "arch_kobj_size (PageTable _) = table_size"
| "arch_kobj_size (DataPage _ sz) = pageBitsForSize sz"

fun aobj_ref :: "arch_cap \<rightharpoonup> obj_ref"
  where
  "aobj_ref ASIDControlCap = None"
| "aobj_ref c = Some (acap_obj c)"

definition acap_rights_update :: "cap_rights \<Rightarrow> arch_cap \<Rightarrow> arch_cap"
  where
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
  | ASIDPoolObj

definition arch_is_frame_type :: "aobject_type \<Rightarrow> bool"
  where
  "arch_is_frame_type aobj \<equiv> aobj \<noteq> PageTableObj"

definition arch_default_cap :: "aobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> arch_cap"
  where
  "arch_default_cap tp r n dev \<equiv> case tp of
     SmallPageObj \<Rightarrow> FrameCap r vm_read_write RISCVSmallPage dev None
   | LargePageObj \<Rightarrow> FrameCap r vm_read_write RISCVLargePage dev None
   | HugePageObj  \<Rightarrow> FrameCap r vm_read_write RISCVHugePage dev None
   | PageTableObj \<Rightarrow> PageTableCap r None
   | ASIDPoolObj  \<Rightarrow> ASIDPoolCap r 0" (* unused, but nicer properties when defined *)

definition default_arch_object :: "aobject_type \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> arch_kernel_obj"
  where
  "default_arch_object tp dev n \<equiv> case tp of
     SmallPageObj \<Rightarrow> DataPage dev RISCVSmallPage
   | LargePageObj \<Rightarrow> DataPage dev RISCVLargePage
   | HugePageObj  \<Rightarrow> DataPage dev RISCVHugePage
   | PageTableObj \<Rightarrow> PageTable (\<lambda>_. InvalidPTE)
   | ASIDPoolObj  \<Rightarrow> ASIDPool Map.empty"

type_synonym riscv_vspace_region_uses = "vspace_ref \<Rightarrow> riscvvspace_region_use"

end

qualify RISCV64_A (in Arch)

section \<open>Architecture-specific state\<close>

record arch_state =
  riscv_asid_table :: "asid_high_index \<rightharpoonup> obj_ref"
  riscv_global_pt :: obj_ref
  riscv_kernel_vspace :: "obj_ref \<Rightarrow> RISCV64_H.riscvvspace_region_use"

end_qualify

context Arch begin global_naming RISCV64_A

section "Type declarations for invariant definitions"

datatype aa_type =
    AASIDPool
  | APageTable
  | AUserData vmpage_size
  | ADeviceData vmpage_size

definition aa_type :: "arch_kernel_obj \<Rightarrow> aa_type"
  where
  "aa_type ao \<equiv> case ao of
     PageTable pt    \<Rightarrow> APageTable
   | DataPage dev sz \<Rightarrow> if dev then ADeviceData sz else AUserData sz
   | ASIDPool f      \<Rightarrow> AASIDPool"

definition badge_bits :: nat
  where
  "badge_bits \<equiv> 64"

end

section "Arch-specific TCB"

qualify RISCV64_A (in Arch)

text \<open> Arch-specific part of a TCB: this must have at least a field for user context. \<close>
record arch_tcb =
  tcb_context :: user_context

end_qualify

context Arch begin global_naming RISCV64_A

definition default_arch_tcb :: arch_tcb
  where
  "default_arch_tcb \<equiv> \<lparr>tcb_context = new_context\<rparr>"

text \<open>
  Accessors for @{text "tcb_context"} inside @{text "arch_tcb"}. These are later used to
  implement @{text as_user}, i.e.\ need to be compatible with @{text user_monad}.
\<close>
definition arch_tcb_context_set :: "user_context \<Rightarrow> arch_tcb \<Rightarrow> arch_tcb"
  where
  "arch_tcb_context_set uc a_tcb \<equiv> a_tcb \<lparr> tcb_context := uc \<rparr>"

definition arch_tcb_context_get :: "arch_tcb \<Rightarrow> user_context"
  where
  "arch_tcb_context_get a_tcb \<equiv> tcb_context a_tcb"

text \<open>
  Accessors for the user register part of the @{text "arch_tcb"}.
  (Because @{typ "register \<Rightarrow> machine_word"} might not be equal to @{typ user_context}).
\<close>
definition arch_tcb_set_registers :: "(register \<Rightarrow> machine_word) \<Rightarrow> arch_tcb \<Rightarrow> arch_tcb"
  where
  "arch_tcb_set_registers regs a_tcb \<equiv> a_tcb \<lparr> tcb_context := UserContext regs \<rparr>"

definition arch_tcb_get_registers :: "arch_tcb \<Rightarrow> register \<Rightarrow> machine_word"
  where
  "arch_tcb_get_registers a_tcb \<equiv> user_regs (tcb_context a_tcb)"

end
end
