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

header "Machine Accessor Functions"

theory MiscMachine_A
imports ARM_Machine_A
begin

text {* Miscellaneous definitions of constants used in modelling machine
operations. *}

definition
  nat_to_cref :: "nat \<Rightarrow> nat \<Rightarrow> cap_ref" where
  "nat_to_cref ln n \<equiv> drop (word_bits - ln)
                           (to_bl (of_nat n :: machine_word))"

type_synonym user_context = "register \<Rightarrow> data"
type_synonym 'a user_monad = "(user_context, 'a) nondet_monad"

definition
 "msg_info_register \<equiv> msgInfoRegister"
definition
 "msg_registers \<equiv> msgRegisters"
definition
 "cap_register \<equiv> capRegister"
definition
 "badge_register \<equiv> badgeRegister"
definition
 "frame_registers \<equiv> frameRegisters"
definition
 "gp_registers \<equiv> gpRegisters"
definition
 "exception_message \<equiv> exceptionMessage"
definition
 "syscall_message \<equiv> syscallMessage"

definition
  new_context :: "user_context" where
  "new_context \<equiv> (\<lambda>r. 0) (CPSR := 0x150)"

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
