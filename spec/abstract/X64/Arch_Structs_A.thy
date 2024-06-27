(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "x64-Specific Data Types"

theory Arch_Structs_A
imports
  "ExecSpec.Arch_Structs_B"
  ExceptionTypes_A
  VMRights_A
  ExecSpec.Arch_Kernel_Config_Lemmas
begin

context Arch begin global_naming X64_A

text \<open>
This theory provides architecture-specific definitions and datatypes
including architecture-specific capabilities and objects.
\<close>

section \<open>Architecture-specific virtual memory\<close>

type_synonym io_port = "16 word"
type_synonym io_asid = "16 word"

section \<open>Architecture-specific capabilities\<close>

text \<open>The x64 kernel supports capabilities for ASID pools and an ASID controller capability,
along with capabilities for IO ports and spaces, as well as virtual memory mappings.\<close>

datatype arch_cap =
   ASIDPoolCap (acap_asid_pool : obj_ref) (acap_asid_base : asid)
 | ASIDControlCap
 | IOPortCap (acap_io_port_first_port : io_port) (acap_io_port_last_port : io_port)
 | IOPortControlCap
(* FIXME x64-vtd:
 | IOSpaceCap (cap_io_domain_id : "16 word") (cap_io_pci_device : "io_asid option")
 | IOPageTableCap (cap_iopt_base_ptr : obj_ref) (cap_io_pt_level : nat) (cap_iopt_mapped_address : "(io_asid * vspace_ref) option")
*)
 | PageCap bool obj_ref (acap_rights : cap_rights) vmmap_type vmpage_size "(asid * vspace_ref) option"
 | PageTableCap obj_ref "(asid * vspace_ref) option"
 | PageDirectoryCap obj_ref "(asid * vspace_ref) option"
 | PDPointerTableCap obj_ref "(asid * vspace_ref) option"
 | PML4Cap obj_ref "asid option"

(* cr3 Stuff *)
datatype cr3 = cr3 obj_ref asid

primrec
  cr3_base_address :: "cr3 \<Rightarrow> obj_ref"
where
  "cr3_base_address (cr3 addr _) = addr"

primrec
  cr3_pcid :: "cr3 \<Rightarrow> asid"
where
  "cr3_pcid (cr3 _ pcid) = pcid"

section \<open>Architecture-specific objects\<close>

datatype table_attr = Accessed | CacheDisabled | WriteThrough | ExecuteDisable
type_synonym table_attrs = "table_attr set"

datatype frame_attr = PTAttr table_attr | Global | PAT | Dirty
type_synonym frame_attrs = "frame_attr set"

datatype pml4e
     = InvalidPML4E
     | PDPointerTablePML4E
         (pml4_table : obj_ref)
         (pml4e_attrs : table_attrs)
         (pml4e_rights : vm_rights)

datatype pdpte
     = InvalidPDPTE
     | PageDirectoryPDPTE
         (pdpt_table : obj_ref)
         (pdpt_table_attrs : table_attrs)
         (pdpt_rights : vm_rights)
     | HugePagePDPTE
         (pdpt_frame : obj_ref)
         (pdpt_frame_attrs : frame_attrs)
         (pdpt_rights : vm_rights)

datatype pde
      = InvalidPDE
      | PageTablePDE
         obj_ref
         (pt_attrs : table_attrs)
         (pde_rights : cap_rights)
      | LargePagePDE
         obj_ref
         (pde_page_attrs : frame_attrs)
         (pde_rights: cap_rights)

datatype pte
      = InvalidPTE
      | SmallPagePTE
         (pte_frame: obj_ref)
         (pte_frame_attrs : frame_attrs)
         (pte_rights : cap_rights)


datatype vm_page_entry = VMPTE pte | VMPDE pde | VMPDPTE pdpte

datatype translation_type = NotTranslated | Translated

datatype iocte =
   InvalidIOCTE
 | VTDCTE
   (domain_id : word16)
   (res_mem_reg: bool)
   (address_width: nat)
   (next_level_ptr: obj_ref)
   (translation_type: translation_type)
   (iocte_present : bool)

datatype iopte =
   InvalidIOPTE
 | VTDPTE
   (frame_ptr : obj_ref)
   (io_pte_rights  : vm_rights)

datatype iorte =
   InvalidIORTE
 | VTDRTE
   (context_table : obj_ref)
   (iorte_present : bool)

datatype arch_kernel_obj =
   ASIDPool "9 word \<rightharpoonup> obj_ref"
 | PageTable "9 word \<Rightarrow> pte"
 | PageDirectory "9 word \<Rightarrow> pde"
 | PDPointerTable "9 word \<Rightarrow> pdpte"
 | PageMapL4 "9 word \<Rightarrow> pml4e"
 | DataPage bool vmpage_size
(* FIXME x64-vtd:
 | IORootTable "16 word \<Rightarrow> iorte"
 | IOContextTable "16 word \<Rightarrow> iocte"
 | IOPageTable "16 word \<Rightarrow> iopte" *)

definition table_size :: nat where
  "table_size = ptTranslationBits + word_size_bits"

definition iotable_size :: nat where
  "iotable_size = ptTranslationBits + 2*word_size_bits"

definition cte_level_bits :: nat where
  "cte_level_bits \<equiv> 5"

primrec
  arch_obj_size :: "arch_cap \<Rightarrow> nat"
where
  "arch_obj_size (ASIDPoolCap _ _) = pageBits"
| "arch_obj_size ASIDControlCap = 0"
| "arch_obj_size (IOPortCap _ _) = 0"
| "arch_obj_size IOPortControlCap = 0"
(* FIXME x64-vtd:
| "arch_obj_size (IOSpaceCap _ _) = 0"
| "arch_obj_size (IOPageTableCap _ _ _) = iotable_size" *)
| "arch_obj_size (PageCap _ _ _ _ sz _) = pageBitsForSize sz"
| "arch_obj_size (PageTableCap _ _) = table_size"
| "arch_obj_size (PageDirectoryCap _ _) = table_size"
| "arch_obj_size (PDPointerTableCap _ _) = table_size"
| "arch_obj_size (PML4Cap _ _) = table_size"

primrec
  arch_cap_is_device :: "arch_cap \<Rightarrow> bool"
where
  "arch_cap_is_device (ASIDPoolCap _ _) = False"
| "arch_cap_is_device ASIDControlCap = False"
| "arch_cap_is_device (IOPortCap _ _) = False"
| "arch_cap_is_device IOPortControlCap = False"
(* FIXME x64-vtd:
| "arch_cap_is_device (IOSpaceCap _ _) = False"
| "arch_cap_is_device (IOPageTableCap _ _ _) = False" *)
| "arch_cap_is_device (PageCap is_dev _ _ _ _ _) = is_dev"
| "arch_cap_is_device (PageTableCap _ _) = False"
| "arch_cap_is_device (PageDirectoryCap _ _) = False"
| "arch_cap_is_device (PDPointerTableCap _ _) = False"
| "arch_cap_is_device (PML4Cap _ _) = False"

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

primrec
  arch_kobj_size :: "arch_kernel_obj \<Rightarrow> nat"
where
  "arch_kobj_size (ASIDPool _) = pageBits"
| "arch_kobj_size (PageTable _) = table_size"
| "arch_kobj_size (PageDirectory _) = table_size"
| "arch_kobj_size (PDPointerTable _) = table_size"
| "arch_kobj_size (PageMapL4 _) = table_size"
| "arch_kobj_size (DataPage _ sz) = pageBitsForSize sz"

primrec
  aobj_ref :: "arch_cap \<rightharpoonup> obj_ref"
where
  "aobj_ref (ASIDPoolCap x _) = Some x"
| "aobj_ref ASIDControlCap = None"
| "aobj_ref (IOPortCap _ _) = None"
| "aobj_ref IOPortControlCap = None"
(* FIXME x64-vtd:
| "aobj_ref (IOSpaceCap _ _) = None"
| "aobj_ref (IOPageTableCap x _ _) = Some x" *)
| "aobj_ref (PageCap _ x _ _ _ _) = Some x"
| "aobj_ref (PageDirectoryCap x _) = Some x"
| "aobj_ref (PageTableCap x _) = Some x"
| "aobj_ref (PDPointerTableCap x _) = Some x"
| "aobj_ref (PML4Cap x _) = Some x"


definition
  acap_rights_update :: "cap_rights \<Rightarrow> arch_cap \<Rightarrow> arch_cap" where
 "acap_rights_update rs ac \<equiv> case ac of
    PageCap dev x rs' m sz as \<Rightarrow> PageCap dev x (validate_vm_rights rs) m sz as
  | _                   \<Rightarrow> ac"

section \<open>Architecture-specific object types and default objects\<close>

datatype
  aobject_type =
    SmallPageObj
  | LargePageObj
  | HugePageObj
  | PageTableObj
  | PageDirectoryObj
  | PDPTObj
  | PML4Obj
  | ASIDPoolObj

datatype X64IRQState =
   IRQFree
 | IRQReserved
 | IRQMSI
      (MSIBus : machine_word)
      (MSIDev : machine_word)
      (MSIFunc : machine_word)
      (MSIHandle : machine_word)
 | IRQIOAPIC
      (IRQioapic : machine_word)
      (IRQPin : machine_word)
      (IRQLevel : machine_word)
      (IRQPolarity : machine_word)
      (IRQMasked : bool)

definition
  arch_is_frame_type :: "aobject_type \<Rightarrow> bool"
where
  "arch_is_frame_type aobj \<equiv> case aobj of
         SmallPageObj \<Rightarrow> True
       | LargePageObj \<Rightarrow> True
       | HugePageObj \<Rightarrow> True
       | _ \<Rightarrow> False"

definition
  arch_default_cap :: "aobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> arch_cap" where
 "arch_default_cap tp r n dev \<equiv> case tp of
    SmallPageObj \<Rightarrow> PageCap dev r vm_read_write VMNoMap X64SmallPage None
  | LargePageObj \<Rightarrow> PageCap dev r vm_read_write VMNoMap X64LargePage None
  | HugePageObj \<Rightarrow> PageCap dev r vm_read_write VMNoMap X64HugePage None
  | PageTableObj \<Rightarrow> PageTableCap r None
  | PageDirectoryObj \<Rightarrow> PageDirectoryCap r None
  | PDPTObj \<Rightarrow> PDPointerTableCap r None
  | PML4Obj \<Rightarrow> PML4Cap r None
  | ASIDPoolObj \<Rightarrow> ASIDPoolCap r 0" (* unused *)

definition
  default_arch_object :: "aobject_type \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> arch_kernel_obj" where
 "default_arch_object tp dev n \<equiv> case tp of
    SmallPageObj \<Rightarrow> DataPage dev X64SmallPage
  | LargePageObj \<Rightarrow> DataPage dev X64LargePage
  | HugePageObj \<Rightarrow> DataPage dev X64HugePage
  | PageTableObj \<Rightarrow> PageTable (\<lambda>x. InvalidPTE)
  | PageDirectoryObj \<Rightarrow> PageDirectory (\<lambda>x. InvalidPDE)
  | PDPTObj \<Rightarrow> PDPointerTable (\<lambda>x. InvalidPDPTE)
  | PML4Obj \<Rightarrow> PageMapL4 (\<lambda>x. InvalidPML4E)
  | ASIDPoolObj \<Rightarrow> ASIDPool (\<lambda>_. None)"

type_synonym x64_vspace_region_uses = "vspace_ref \<Rightarrow> x64vspace_region_use"

end

qualify X64_A (in Arch)

section \<open>Architecture-specific state\<close>

record arch_state =
  x64_asid_table            :: "3 word \<rightharpoonup> obj_ref"
  x64_global_pml4           :: obj_ref
  x64_kernel_vspace         :: X64_A.x64_vspace_region_uses
  x64_global_pts            :: "obj_ref list"
  x64_global_pdpts          :: "obj_ref list"
  x64_global_pds            :: "obj_ref list"
  x64_current_cr3           :: "X64_A.cr3"
  x64_allocated_io_ports    :: "X64_A.io_port \<Rightarrow> bool"
  x64_num_ioapics           :: "64 word"
  x64_ioapic_nirqs          :: "machine_word \<Rightarrow> 8 word"
  x64_irq_state             :: "8 word \<Rightarrow> X64_A.X64IRQState"

(* FIXME x64-vtd:
  x64_num_io_domain_bits    :: "16 word"
  x64_first_valid_io_domain :: "16 word"
  x64_num_io_domain_id_bits :: "32 word"
  x64_io_root_table         :: obj_ref *)

end_qualify

context Arch begin global_naming X64_A

definition
  pd_shift_bits :: "nat" where
  "pd_shift_bits \<equiv> pageBits + ptTranslationBits"

definition
  pt_shift_bits :: "nat" where
  "pt_shift_bits \<equiv> pageBits"

definition
  pdpt_shift_bits :: "nat" where
  "pdpt_shift_bits \<equiv> pageBits + ptTranslationBits + ptTranslationBits"

definition
  pml4_shift_bits :: "nat" where
  "pml4_shift_bits \<equiv> pageBits + ptTranslationBits + ptTranslationBits + ptTranslationBits"

definition
  pt_bits :: "nat" where
  "pt_bits \<equiv> table_size"

definition
  pd_bits :: "nat" where
  "pd_bits \<equiv> table_size"

definition
  pdpt_bits :: "nat" where
  "pdpt_bits \<equiv> table_size"

definition
  pml4_bits :: "nat" where
  "pml4_bits \<equiv> table_size"

definition
  iopt_bits :: "nat" where
  "iopt_bits \<equiv> iotable_size"

definition
  vtd_cte_size_bits :: "nat" where
  "vtd_cte_size_bits \<equiv> 8"

definition
  vtd_pt_bits :: "nat" where
  "vtd_pt_bits \<equiv> iotable_size"

definition
  x64_num_io_pt_levels :: "nat" where
  "x64_num_io_pt_levels \<equiv> 4"

section "Type declarations for invariant definitions"

(* FIXME x64-vtd: add *)
datatype aa_type =
    AASIDPool
  | APageTable
  | APageDirectory
  | APDPointerTable
  | APageMapL4
  | AUserData vmpage_size
  | ADeviceData vmpage_size

(* FIXME x64-vtd: add *)
definition aa_type :: "arch_kernel_obj \<Rightarrow> aa_type"
where
 "aa_type ao \<equiv> (case ao of
           PageTable pt             \<Rightarrow> APageTable
         | PageDirectory pd         \<Rightarrow> APageDirectory
         | DataPage dev sz          \<Rightarrow> if dev then ADeviceData sz else AUserData sz
         | ASIDPool f               \<Rightarrow> AASIDPool
         | PDPointerTable pdpt      \<Rightarrow> APDPointerTable
         | PageMapL4 pm             \<Rightarrow> APageMapL4)"

text \<open>For implementation reasons the badge word has differing amounts of bits\<close>
definition
  badge_bits :: nat where
  "badge_bits \<equiv> 64"

end

section "Arch-specific TCB"

qualify X64_A (in Arch)

text \<open> Arch-specific part of a TCB: this must have at least a field for user context. \<close>
record arch_tcb =
  tcb_context :: user_context

end_qualify

context Arch begin global_naming X64_A

definition
  default_arch_tcb :: arch_tcb where
  "default_arch_tcb \<equiv> \<lparr>tcb_context = new_context\<rparr>"

text \<open> Accessors for @{text "tcb_context"} inside @{text "arch_tcb"}.
  These are later used to implement @{text as_user}, i.e.\ need to be
  compatible with @{text user_monad}.\<close>
definition
  arch_tcb_context_set :: "user_context \<Rightarrow> arch_tcb \<Rightarrow> arch_tcb"
where
  "arch_tcb_context_set uc a_tcb \<equiv> a_tcb \<lparr> tcb_context := uc \<rparr>"

definition
  arch_tcb_context_get :: "arch_tcb \<Rightarrow> user_context"
where
  "arch_tcb_context_get a_tcb \<equiv> tcb_context a_tcb"

(* FIXME: the following means that we break the set/getRegister abstraction
          and should move some of this into the machine interface *)
text \<open>
 Accessors for the user register part of the @{text "arch_tcb"}.
 (Because @{typ "register \<Rightarrow> machine_word"} may not be equal to @{typ user_context}).
\<close>
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
