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
Types and operations to access the underlying machine, instantiated
for ARM. 
*)

chapter "ARM Machine Instantiation"

theory Machine_A
imports
  "../../machine/$L4V_ARCH/MachineTypes"
begin

context Arch begin global_naming ARM_A

text {*
  The specification is written with abstract type names for object
  references, user pointers, word-based data, cap references, and so
  on. This theory provides an instantiation of these names to concrete 
  types for the ARM architecture. Other architectures may have slightly
  different instantiations.
*}
type_synonym obj_ref            = machine_word
type_synonym vspace_ref         = machine_word
type_synonym data_offset        = "12 word"

type_synonym data               = machine_word
type_synonym cap_ref            = "bool list"
type_synonym length_type        = machine_word
type_synonym asid_pool_index    = "10 word"
type_synonym asid_index         = "8 word" (* FIXME: better name? *)

text {* With the definitions above, most conversions between abstract
type names boil down to just the identity function, some convert from
@{text word} to @{typ nat} and others between different word sizes
using @{const ucast}. *}
definition
  oref_to_data   :: "obj_ref \<Rightarrow> data" where
  "oref_to_data \<equiv> id"

definition
  data_to_oref   :: "data \<Rightarrow> obj_ref" where
  "data_to_oref \<equiv> id"

definition
  vref_to_data   :: "vspace_ref \<Rightarrow> data" where
  "vref_to_data \<equiv> id"

definition
  data_to_vref   :: "data \<Rightarrow> vspace_ref" where
  "data_to_vref \<equiv> id"

definition
  nat_to_len     :: "nat \<Rightarrow> length_type" where
  "nat_to_len \<equiv> of_nat"

definition
  data_to_nat    :: "data \<Rightarrow> nat" where
  "data_to_nat \<equiv> unat"

definition
  data_to_16     :: "data \<Rightarrow> 16 word" where
  "data_to_16 \<equiv> ucast"

definition
  data_to_cptr :: "data \<Rightarrow> cap_ref" where
  "data_to_cptr \<equiv> to_bl"

definition
  data_offset_to_nat :: "data_offset \<Rightarrow> nat" where
  "data_offset_to_nat \<equiv> unat"

definition
  combine_ntfn_badges :: "data \<Rightarrow> data \<Rightarrow> data" where
  "combine_ntfn_badges \<equiv> bitOR"

definition
  combine_ntfn_msgs :: "data \<Rightarrow> data \<Rightarrow> data" where
  "combine_ntfn_msgs \<equiv> bitOR"


text {* These definitions will be unfolded automatically in proofs. *}
lemmas data_convs [simp] =
  oref_to_data_def data_to_oref_def vref_to_data_def data_to_vref_def
  nat_to_len_def data_to_nat_def data_to_16_def data_to_cptr_def 
  data_offset_to_nat_def


text {* The following definitions provide architecture-dependent sizes
  such as the standard page size and capability size of the underlying
  machine. 
*}
definition 
  slot_bits :: nat where
  "slot_bits \<equiv> 4"

type_synonym user_context = "register \<Rightarrow> data"

definition
  new_context :: "user_context" where
  "new_context \<equiv> (\<lambda>r. 0) (CPSR := 0x150)"

text {* Miscellaneous definitions of constants used in modelling machine
operations. *}

definition
  nat_to_cref :: "nat \<Rightarrow> nat \<Rightarrow> cap_ref" where
  "nat_to_cref ln n \<equiv> drop (word_bits - ln)
                           (to_bl (of_nat n :: machine_word))"

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


end

end
