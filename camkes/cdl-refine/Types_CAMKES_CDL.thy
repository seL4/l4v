(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Types_CAMKES_CDL imports
  "../adl-spec/Types_CAMKES"
  "../adl-spec/Library_CAMKES"
  "../../spec/capDL/Syscall_D"
begin

(* placeholder for things to fill in *)
abbreviation "TODO \<equiv> undefined"

text {* A CAmkES system is completely specified by its top-level assembly definition. *}
type_synonym camkes_state = assembly

text {*
  Symbolic names for capability slots.
  XXX: Move this to DSpec?
*}
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
