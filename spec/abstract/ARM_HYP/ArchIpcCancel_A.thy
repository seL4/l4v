(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
Arch Functions for cancelling IPC.
*)

chapter {* Arch IPC Cancelling *}


theory ArchIpcCancel_A
imports "../CSpaceAcc_A"
begin

context Arch begin global_naming ARM_A

text {* Actions to be taken after a cap is deleted *}
definition
  arch_post_cap_deletion :: "arch_cap \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "arch_post_cap_deletion _ \<equiv> return ()"

text {* Arch specific generic object references not covered by generic references *}
datatype arch_gen_obj_ref = unit

definition
  arch_gen_obj_refs :: "arch_cap \<Rightarrow> arch_gen_obj_ref set"
where
  "arch_gen_obj_refs _ = {}"

definition
  arch_cap_cleanup_opt :: "arch_cap \<Rightarrow> cap"
where
  "arch_cap_cleanup_opt ac \<equiv> NullCap"

end
end
