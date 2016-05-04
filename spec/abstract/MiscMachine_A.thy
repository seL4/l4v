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

context begin interpretation Arch .

requalify_types
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

requalify_consts
  nat_to_cref
  msg_info_register
  msg_registers
  cap_register
  badge_register
  frame_registers
  gp_registers
  exception_message
  syscall_message

  new_context
  slot_bits
  oref_to_data
  data_to_oref
  vref_to_data
  data_to_vref
  nat_to_len
  data_to_nat
  data_to_16
  data_to_cptr
  data_offset_to_nat
  combine_ntfn_badges
  

end


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
