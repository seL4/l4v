(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Functions for fault handling.
*)

chapter \<open>arch fault related functions\<close>

theory ArchFault_A
imports Structures_A Tcb_A
begin

context Arch begin arch_global_naming (A)

fun make_arch_fault_msg :: "arch_fault \<Rightarrow> obj_ref \<Rightarrow> (data \<times> data list,'z::state_ext) s_monad"
where
 "make_arch_fault_msg (VMFault vptr archData) thread = do
     pc \<leftarrow> as_user thread getRestartPC;
     return (6, pc # vptr # archData) od"

definition
  handle_arch_fault_reply :: "arch_fault \<Rightarrow> obj_ref \<Rightarrow> data \<Rightarrow> data list \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "handle_arch_fault_reply vmf thread x y \<equiv> return True"


end

end
