(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchInvocationLabels_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Architecture-specific Invocation Labels"

theory ArchInvocationLabels_H
imports
  "../../../lib/Word_Lib/Enumeration"
  "../../machine/Setup_Locale"
begin
context Arch begin global_naming X64_H

text {*
  An enumeration of arch-specific system call labels.
*}

datatype arch_invocation_label =
    X64PDPTMap
  | X64PDPTUnmap
  | X64PageDirectoryMap
  | X64PageDirectoryUnmap
  | X64PageTableMap
  | X64PageTableUnmap
  | X64IOPageTableMap
  | X64IOPageTableUnmap
  | X64PageMap
  | X64PageRemap
  | X64PageUnmap
  | X64PageMapIO
  | X64PageGetAddress
  | X64ASIDControlMakePool
  | X64ASIDPoolAssign
  | X64IOPortIn8
  | X64IOPortIn16
  | X64IOPortIn32
  | X64IOPortOut8
  | X64IOPortOut16
  | X64IOPortOut32
  | X64IRQIssueIRQHandlerIOAPIC
  | X64IRQIssueIRQHandlerMSI


end

context begin interpretation Arch .
requalify_types arch_invocation_label
end

context Arch begin global_naming X64_H

end
qualify X64_H (in Arch) 
(* arch_invocation_label instance proofs *)
(*<*)
instantiation arch_invocation_label :: enum begin
interpretation Arch .
definition
  enum_arch_invocation_label: "enum_class.enum \<equiv> 
    [ 
      X64PDPTMap,
      X64PDPTUnmap,
      X64PageDirectoryMap,
      X64PageDirectoryUnmap,
      X64PageTableMap,
      X64PageTableUnmap,
      X64IOPageTableMap,
      X64IOPageTableUnmap,
      X64PageMap,
      X64PageRemap,
      X64PageUnmap,
      X64PageMapIO,
      X64PageGetAddress,
      X64ASIDControlMakePool,
      X64ASIDPoolAssign,
      X64IOPortIn8,
      X64IOPortIn16,
      X64IOPortIn32,
      X64IOPortOut8,
      X64IOPortOut16,
      X64IOPortOut32,
      X64IRQIssueIRQHandlerIOAPIC,
      X64IRQIssueIRQHandlerMSI
    ]"


definition
  "enum_class.enum_all (P :: arch_invocation_label \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: arch_invocation_label \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_arch_invocation_label enum_all_arch_invocation_label_def enum_ex_arch_invocation_label_def)
  by fast+
end

instantiation arch_invocation_label :: enum_alt
begin
interpretation Arch .
definition
  enum_alt_arch_invocation_label: "enum_alt \<equiv> 
    alt_from_ord (enum :: arch_invocation_label list)"
instance ..
end

instantiation arch_invocation_label :: enumeration_both
begin
interpretation Arch .
instance by (intro_classes, simp add: enum_alt_arch_invocation_label)
end

(*>*)
end_qualify
context Arch begin global_naming X64_H


end
end
