(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "Architecture specific Retype definitions"

theory ArchRetype_A
imports
  ArchVSpaceAcc_A
  ArchInvocation_A
begin

context Arch begin global_naming RISCV64_A

text \<open>
  This is a placeholder function. We may wish to extend the specification
  with explicitly tagging kernel data regions in memory.
\<close>
definition reserve_region :: "obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "reserve_region ptr byteLength is_kernel \<equiv> return ()"

text \<open>Initialise architecture-specific objects.\<close>

definition init_arch_objects ::
  "apiobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> obj_ref list \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "init_arch_objects new_type ptr num_objects obj_sz refs \<equiv> return ()"

definition empty_context :: user_context
  where
  "empty_context \<equiv> UserContext (\<lambda>_. 0)"

definition init_arch_tcb :: arch_tcb
  where
  "init_arch_tcb \<equiv> \<lparr> tcb_context = empty_context \<rparr>"

end
end
