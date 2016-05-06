(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
Arch-specific functions for the abstract model of CSpace.
*)

chapter "ArchCSpace"

theory ArchCSpace_A
imports
  ArchVSpace_A
begin

context Arch begin global_naming X64_A

text {* For some purposes capabilities to physical objects are treated
differently to others. *}
definition
  arch_is_physical :: "arch_cap \<Rightarrow> bool" where
  "arch_is_physical cap \<equiv> case cap of ASIDControlCap \<Rightarrow> False | _ \<Rightarrow> True"

text {* Check whether the second capability is to the same object or an object
contained in the region of the first one. *}
fun
  arch_same_region_as :: "arch_cap \<Rightarrow> arch_cap \<Rightarrow> bool"
where
  "arch_same_region_as (PageCap r R t s m) (PageCap r' R' t' s' m') =
   (let
     topA = r + (1 << pageBitsForSize s) - 1;
     topB = r' + (1 << pageBitsForSize s') - 1
   in r \<le> r' \<and> topA \<ge> topB \<and> r' \<le> topB)"
| "arch_same_region_as (PageTableCap r _) c = (is_PageTableCap c \<and> aobj_ref c = Some r)"
| "arch_same_region_as (PageDirectoryCap r _) c = (is_PageDirectoryCap c \<and> aobj_ref c = Some r)"
| "arch_same_region_as (PDPointerTableCap r _) c = (is_PDPointerTableCap c \<and> aobj_ref c = Some r)"
| "arch_same_region_as (PML4Cap r _) c = (is_PML4Cap c \<and> aobj_ref c = Some r)"
| "arch_same_region_as (IOPageTableCap r _ _) c = (is_IOPageTableCap c \<and> aobj_ref c = Some r)"
| "arch_same_region_as ASIDControlCap c = (c = ASIDControlCap)"
| "arch_same_region_as (ASIDPoolCap r _) c = (is_ASIDPoolCap c \<and> aobj_ref c = Some r)"
| "arch_same_region_as (IOSpaceCap d_id pci_d) c = (is_IOSpaceCap c \<and> cap_io_pci_device c = pci_d)"
  --"FIXME: should this also check domain id equality? C kernel does not"
| "arch_same_region_as (IOPortCap frst lst) c = (is_IOPortCap c)"
  --"FIXME: would an interval check make sense here?"
| "arch_same_region_as _ _ = False"

text {* Check whether two arch capabilities are to the same object. *}
definition
  same_aobject_as :: "arch_cap \<Rightarrow> arch_cap \<Rightarrow> bool" where
 "same_aobject_as cp cp' \<equiv>
   (case (cp, cp') of
      (PageCap ref _ _ pgsz _,PageCap ref' _ _ pgsz' _)
          \<Rightarrow> (ref, pgsz) = (ref', pgsz')
              \<and> ref \<le> ref + 2 ^ pageBitsForSize pgsz - 1
    | _ \<Rightarrow> arch_same_region_as cp cp')"

text {* Only caps with sufficient rights can be recycled. *}
definition
  arch_has_recycle_rights :: "arch_cap \<Rightarrow> bool" where
  "arch_has_recycle_rights cap \<equiv> case cap of
     PageCap _ R _ _ _ \<Rightarrow> {AllowRead,AllowWrite} \<subseteq> R
   | _ \<Rightarrow> True"

end
end
