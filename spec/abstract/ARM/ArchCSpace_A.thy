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
context Arch begin global_naming ARM_A

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
  "arch_same_region_as (PageCap r R s x) (PageCap r' R' s' x') =
   (let
     topA = r + (1 << pageBitsForSize s) - 1;
     topB = r' + (1 << pageBitsForSize s') - 1
   in r \<le> r' \<and> topA \<ge> topB \<and> r' \<le> topB)"
| "arch_same_region_as (PageTableCap r x) (PageTableCap r' x') = (r' = r)"
| "arch_same_region_as (PageDirectoryCap r x) (PageDirectoryCap r' x') = (r' = r)"
| "arch_same_region_as ASIDControlCap ASIDControlCap = True"
| "arch_same_region_as (ASIDPoolCap r a) (ASIDPoolCap r' a') = (r' = r)"
| "arch_same_region_as _ _ = False"


text {* Check whether two arch capabilities are to the same object. *}
definition
  same_aobject_as :: "arch_cap \<Rightarrow> arch_cap \<Rightarrow> bool" where
 "same_aobject_as cp cp' \<equiv>
   (case (cp, cp') of
      (PageCap ref _ pgsz _,PageCap ref' _ pgsz' _)
          \<Rightarrow> (ref, pgsz) = (ref', pgsz')
              \<and> ref \<le> ref + 2 ^ pageBitsForSize pgsz - 1
    | _ \<Rightarrow> arch_same_region_as cp cp')"

(* Proofs don't want to see this definition *)
declare same_aobject_as_def[simp]

text {* Only caps with sufficient rights can be recycled. *}
definition
  arch_has_recycle_rights :: "arch_cap \<Rightarrow> bool" where
  "arch_has_recycle_rights cap \<equiv> case cap of
     PageCap _ R _ _ \<Rightarrow> {AllowRead,AllowWrite} \<subseteq> R
   | _ \<Rightarrow> True"

end
end
