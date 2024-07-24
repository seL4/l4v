(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Architecture-specific Functions for CSpace"

theory ArchCSpace_A
imports
  ArchVSpace_A
begin

context Arch begin arch_global_naming (A)

definition cnode_guard_size_bits :: "nat"
  where
  "cnode_guard_size_bits \<equiv> 6"

definition cnode_padding_bits :: "nat"
  where
  "cnode_padding_bits \<equiv> 0"

text \<open>On a user request to modify a CNode capability, extract new guard bits and guard.\<close>
definition update_cnode_cap_data :: "data \<Rightarrow> nat \<times> data"
  where
  "update_cnode_cap_data w \<equiv>
    let
      guard_bits = 58;
      guard_size' = unat ((w >> cnode_padding_bits) && mask cnode_guard_size_bits);
      guard'' = (w >> (cnode_padding_bits + cnode_guard_size_bits)) && mask guard_bits
    in (guard_size', guard'')"

text \<open>For some purposes capabilities to physical objects are treated differently to others.\<close>
definition arch_is_physical :: "arch_cap \<Rightarrow> bool"
  where
  "arch_is_physical cap \<equiv> case cap of ASIDControlCap \<Rightarrow> False | _ \<Rightarrow> True"

text \<open>
  Check whether the second capability is to the same object or an object
  contained in the region of the first one.
\<close>
fun arch_same_region_as :: "arch_cap \<Rightarrow> arch_cap \<Rightarrow> bool"
  where
  "arch_same_region_as (FrameCap r _ sz _ _) c' =
   (is_FrameCap c' \<and>
     (let
        r' = acap_obj c';
        sz' = acap_fsize c';
        topA = r + (1 << pageBitsForSize sz) - 1;
        topB = r' + (1 << pageBitsForSize sz') - 1
      in r \<le> r' \<and> topA \<ge> topB \<and> r' \<le> topB))"
| "arch_same_region_as (PageTableCap r _) c' = (\<exists>r' d'. c' = PageTableCap r' d' \<and> r = r')"
| "arch_same_region_as ASIDControlCap c' = (c' = ASIDControlCap)"
| "arch_same_region_as (ASIDPoolCap r _) c' = (\<exists>r' d'. c' = ASIDPoolCap r' d' \<and> r = r')"


text \<open>Check whether two arch capabilities are to the same object.\<close>
definition same_aobject_as :: "arch_cap \<Rightarrow> arch_cap \<Rightarrow> bool"
  where
  "same_aobject_as cap cap' \<equiv>
     case (cap, cap') of
       (FrameCap ref _ sz dev _, FrameCap ref' _ sz' dev' _) \<Rightarrow>
         (dev, ref, sz) = (dev', ref', sz') \<and> ref \<le> ref + 2 ^ pageBitsForSize sz - 1
     | _ \<Rightarrow> arch_same_region_as cap cap'"

declare same_aobject_as_def[simp]

definition arch_is_cap_revocable :: "cap \<Rightarrow> cap \<Rightarrow> bool"
  where
  "arch_is_cap_revocable new_cap src_cap \<equiv> False"

end
end
