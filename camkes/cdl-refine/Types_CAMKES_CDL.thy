(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Types_CAMKES_CDL imports
  "CamkesAdlSpec.Types_CAMKES"
  "CamkesAdlSpec.Library_CAMKES"
  "DSpec.Syscall_D"
begin

(* placeholder for things to fill in *)
abbreviation "TODO \<equiv> undefined"

text \<open>A CAmkES system is completely specified by its top-level assembly definition.\<close>
type_synonym camkes_state = assembly

text \<open>
  Symbolic names for capability slots.
  XXX: Move this to DSpec?
\<close>
definition cspace :: cdl_cnode_index
  where "cspace \<equiv> 0"
definition vspace :: cdl_cnode_index
  where "vspace \<equiv> 1"
definition reply_slot :: cdl_cnode_index
  where "reply_slot \<equiv> 2"
definition caller_slot :: cdl_cnode_index
  where "caller_slot \<equiv> 3"
definition ipc_buffer_slot :: cdl_cnode_index
  where "ipc_buffer_slot \<equiv> 4"
definition fault_ep_slot :: cdl_cnode_index
  where "fault_ep_slot \<equiv> 5"

definition
  instance_names :: "camkes_state \<Rightarrow> string list"
where
  "instance_names spec \<equiv> map fst (components (composition spec))"

end
