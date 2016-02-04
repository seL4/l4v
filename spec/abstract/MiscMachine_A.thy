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
Utilities for the machine level which are not machine-dependent.
*)

chapter "Machine Accessor Functions"

theory MiscMachine_A
imports "./$L4V_ARCH/Machine_A" "../machine/MachineExports"
begin

unqualify_types (in "$L4V_ARCH")
  user_context 
  register 
  data 
  obj_ref
  asid_index
  asid_pool_index
  cap_ref
  length_type
  vspace_ref
  data_offset


unqualify_consts (in "$L4V_ARCH")
  "nat_to_cref :: nat \<Rightarrow> nat \<Rightarrow> cap_ref"
  "msg_info_register :: register"
  "msg_registers :: register list"
  "cap_register :: register"
  "badge_register :: register"
  "frame_registers :: register list"
  "gp_registers :: register list"
  "exception_message :: register list"
  "syscall_message :: register list"

  "new_context :: user_context"
  "slot_bits :: nat"
  "oref_to_data   :: obj_ref \<Rightarrow> data"
  "data_to_oref   :: data \<Rightarrow> obj_ref"
  "vref_to_data   :: vspace_ref \<Rightarrow> data"
  "data_to_vref   :: data \<Rightarrow> vspace_ref"
  "nat_to_len     :: nat \<Rightarrow> length_type"
  "data_to_nat    :: data \<Rightarrow> nat"
  "data_to_16     :: data \<Rightarrow> 16 word"
  "data_to_cptr :: data \<Rightarrow> cap_ref"
  "data_offset_to_nat :: data_offset \<Rightarrow> nat"
  "combine_ntfn_badges :: data \<Rightarrow> data \<Rightarrow> data"
  "combine_ntfn_msgs :: data \<Rightarrow> data \<Rightarrow> data" 


type_synonym 'a user_monad = "(user_context, 'a) nondet_monad"

definition
  get_register :: "register \<Rightarrow> data user_monad" where
  "get_register r \<equiv> gets (\<lambda>uc. uc r)"

definition
  set_registers :: "(register \<Rightarrow> data) \<Rightarrow> unit user_monad" where
  "set_registers \<equiv> put"

definition
  set_register :: "register \<Rightarrow> data \<Rightarrow> unit user_monad" where
  "set_register r v \<equiv> modify (\<lambda>uc. uc (r := v))"


end
