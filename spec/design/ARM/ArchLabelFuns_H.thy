(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Architecture-specific Invocation Label Functions"

theory ArchLabelFuns_H
imports "../InvocationLabels_H"
begin
context Arch begin global_naming ARM_H
text {*
  Arch-specific functions on invocation labels
*}

definition
isPDFlushLabel :: "invocation_label \<Rightarrow> bool"
where
"isPDFlushLabel x\<equiv> (case x of
        ArchInvocationLabel ARMPDClean_Data \<Rightarrow>   True
      | ArchInvocationLabel ARMPDInvalidate_Data \<Rightarrow>   True
      | ArchInvocationLabel ARMPDCleanInvalidate_Data \<Rightarrow>   True
      | ArchInvocationLabel ARMPDUnify_Instruction \<Rightarrow>   True
      | _ \<Rightarrow>   False
      )"

definition
isPageFlushLabel :: "invocation_label \<Rightarrow> bool"
where
"isPageFlushLabel x\<equiv> (case x of
        ArchInvocationLabel ARMPageClean_Data \<Rightarrow>   True
      | ArchInvocationLabel ARMPageInvalidate_Data \<Rightarrow>   True
      | ArchInvocationLabel ARMPageCleanInvalidate_Data \<Rightarrow>   True
      | ArchInvocationLabel ARMPageUnify_Instruction \<Rightarrow>   True
      | _ \<Rightarrow>   False
      )"


end
end
