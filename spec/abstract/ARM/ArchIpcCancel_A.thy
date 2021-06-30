(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Arch Functions for cancelling IPC.
*)

chapter \<open>Arch IPC Cancelling\<close>


theory ArchIpcCancel_A
imports "../Sporadic_A"
begin

context Arch begin global_naming ARM_A

text \<open>Actions to be taken after a cap is deleted\<close>
definition
  arch_post_cap_deletion :: "arch_cap \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "arch_post_cap_deletion _ \<equiv> return ()"

text \<open>Arch specific generic object references not covered by generic references\<close>
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
