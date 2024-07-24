(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Arch-specific functions for the abstract model of CSpace.
*)

chapter "ArchCSpace"

theory ArchCSpace_A
imports
  ArchVSpace_A
begin
context Arch begin global_naming ARM_HYP_A

definition cnode_guard_size_bits :: "nat"
where
  cnode_guard_size_bits_def [simp]: "cnode_guard_size_bits \<equiv> 5"

definition cnode_padding_bits :: "nat"
where
  cnode_padding_bits_def [simp]: "cnode_padding_bits \<equiv> 3"

text \<open>On a user request to modify a cnode capability, extract new guard bits and guard.\<close>
definition
  update_cnode_cap_data :: "data \<Rightarrow> nat \<times> data" where
 "update_cnode_cap_data w \<equiv>
    let
      guard_bits = 18;
      guard_size' = unat ((w >> cnode_padding_bits) && mask cnode_guard_size_bits);
      guard'' = (w >> (cnode_padding_bits + cnode_guard_size_bits)) && mask guard_bits
    in (guard_size', guard'')"


text \<open>For some purposes capabilities to physical objects are treated
differently to others.\<close>
definition
  arch_is_physical :: "arch_cap \<Rightarrow> bool" where
  "arch_is_physical cap \<equiv> case cap of ASIDControlCap \<Rightarrow> False | _ \<Rightarrow> True"

text \<open>Check whether the second capability is to the same object or an object
contained in the region of the first one.\<close>
fun
  arch_same_region_as :: "arch_cap \<Rightarrow> arch_cap \<Rightarrow> bool"
where
  "arch_same_region_as (PageCap dev r R s x) (PageCap dev' r' R' s' x') =
   (let
     topA = r + (1 << pageBitsForSize s) - 1;
     topB = r' + (1 << pageBitsForSize s') - 1
   in r \<le> r' \<and> topA \<ge> topB \<and> r' \<le> topB)"
| "arch_same_region_as (PageTableCap r x) (PageTableCap r' x') = (r' = r)"
| "arch_same_region_as (PageDirectoryCap r x) (PageDirectoryCap r' x') = (r' = r)"
| "arch_same_region_as ASIDControlCap ASIDControlCap = True"
| "arch_same_region_as (ASIDPoolCap r a) (ASIDPoolCap r' a') = (r' = r)"
| "arch_same_region_as (VCPUCap r) (VCPUCap r') = (r' = r)"
| "arch_same_region_as _ _ = False"


text \<open>Check whether two arch capabilities are to the same object.\<close>
definition
  same_aobject_as :: "arch_cap \<Rightarrow> arch_cap \<Rightarrow> bool" where
 "same_aobject_as cp cp' \<equiv>
   (case (cp, cp') of
      (PageCap dev ref _ pgsz _,PageCap dev' ref' _ pgsz' _)
          \<Rightarrow> (dev, ref, pgsz) = (dev', ref', pgsz')
              \<and> ref \<le> ref + 2 ^ pageBitsForSize pgsz - 1
    | _ \<Rightarrow> arch_same_region_as cp cp')"

(* Proofs don't want to see this definition *)
declare same_aobject_as_def[simp]

definition
  arch_is_cap_revocable :: "cap \<Rightarrow> cap \<Rightarrow> bool"
where
  "arch_is_cap_revocable c c' \<equiv> False"

end
end
