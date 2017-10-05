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

definition cnode_guard_size_bits :: "nat"
where
  "cnode_guard_size_bits \<equiv> 6"

definition cnode_padding_bits :: "nat"
where
  "cnode_padding_bits \<equiv> 2"

text {* On a user request to modify a cnode capability, extract new guard bits and guard. *}
definition
  update_cnode_cap_data :: "data \<Rightarrow> nat \<times> data" where
 "update_cnode_cap_data w \<equiv>
    let
      guard_bits = 58;
      guard_size' = unat ((w >> cnode_padding_bits) && mask cnode_guard_size_bits);
      guard'' = (w >> (cnode_padding_bits + cnode_guard_size_bits)) && mask guard_bits
    in (guard_size', guard'')"

text {* For some purposes capabilities to physical objects are treated
differently to others. *}
definition
  arch_is_physical :: "arch_cap \<Rightarrow> bool" where
  "arch_is_physical cap \<equiv> case cap of
                            ASIDControlCap \<Rightarrow> False
                          | IOPortCap _ _ \<Rightarrow> False
                          | _ \<Rightarrow> True"

text {* Check whether the second capability is to the same object or an object
contained in the region of the first one. *}
fun
  arch_same_region_as :: "arch_cap \<Rightarrow> arch_cap \<Rightarrow> bool"
where
  "arch_same_region_as (PageCap dev r R t s m) c' =
   (\<exists> dev' r' R' t' s' m'. c' = PageCap dev' r' R' t' s' m' \<and>
   (let
      topA = r + (1 << pageBitsForSize s) - 1;
      topB = r' + (1 << pageBitsForSize s') - 1
    in r \<le> r' \<and> topA \<ge> topB \<and> r' \<le> topB))"
| "arch_same_region_as (PageTableCap r _) c' = (\<exists>r' d'. c' = PageTableCap r' d' \<and> r = r')"
| "arch_same_region_as (PageDirectoryCap r _) c' = (\<exists>r' d'. c' = PageDirectoryCap r' d' \<and> r = r')"
| "arch_same_region_as (PDPointerTableCap r _) c' = (\<exists>r' d'. c' = PDPointerTableCap r' d' \<and> r = r')"
| "arch_same_region_as (PML4Cap r _) c' = (\<exists>r' d'. c' = PML4Cap r' d' \<and> r = r')"
| "arch_same_region_as ASIDControlCap c' = (c' = ASIDControlCap)"
| "arch_same_region_as (ASIDPoolCap r _) c' = (\<exists>r' d'. c' = ASIDPoolCap r' d' \<and> r = r')"
(* FIXME x64-vtd: *)
(*
| "arch_same_region_as (IOPageTableCap r _ _) c = (is_IOPageTableCap c \<and> aobj_ref c = Some r)"
| "arch_same_region_as (IOSpaceCap d_id pci_d) c = (is_IOSpaceCap c \<and> cap_io_pci_device c = pci_d)"
  --"FIXME: should this also check domain id equality? C kernel does not"
*)
| "arch_same_region_as (IOPortCap frst lst) c' =
   (\<exists>frst' lst'. c' = IOPortCap frst' lst' \<and> frst \<le> frst' \<and> lst' \<le> lst \<and> frst' \<le> lst')"

text {* Check whether two arch capabilities are to the same object. *}
definition
  same_aobject_as :: "arch_cap \<Rightarrow> arch_cap \<Rightarrow> bool" where
 "same_aobject_as cp cp' \<equiv>
   (case (cp, cp') of
      (PageCap dev ref _ _ pgsz _, PageCap dev' ref' _ _ pgsz' _)
          \<Rightarrow> (dev, ref, pgsz) = (dev', ref', pgsz')
              \<and> ref \<le> ref + 2 ^ pageBitsForSize pgsz - 1
    | (IOPortCap f l, IOPortCap f' l') \<Rightarrow>
             (f,l) = (f',l') \<and> (f \<le> l)
    | _ \<Rightarrow> arch_same_region_as cp cp')"

(* Proofs don't want to see this definition *)
declare same_aobject_as_def[simp]

end
end
