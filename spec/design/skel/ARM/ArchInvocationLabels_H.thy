(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Architecture-specific Invocation Labels"

theory ArchInvocationLabels_H
imports
    "Word_Lib.Enumeration"
    Setup_Locale
begin
context Arch begin arch_global_naming (H)

text \<open>
  An enumeration of arch-specific system call labels.
\<close>

#INCLUDE_HASKELL SEL4/API/InvocationLabels/ARM.lhs CONTEXT ARM_H ONLY ArchInvocationLabel

end

(* not possible to move this requalification to generic, since enum instance proofs must
   be done outside of Arch locale *)
arch_requalify_types (H)
  arch_invocation_label

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/API/InvocationLabels/ARM.lhs CONTEXT ARM_H instanceproofs ONLY ArchInvocationLabel

end
end
