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
context Arch begin global_naming ARM_H

text \<open>
  An enumeration of arch-specific system call labels.
\<close>

#INCLUDE_HASKELL SEL4/API/InvocationLabels/ARM.lhs CONTEXT ARM_H ONLY ArchInvocationLabel

end

context begin interpretation Arch .
requalify_types arch_invocation_label
end

context Arch begin global_naming ARM_H

#INCLUDE_HASKELL SEL4/API/InvocationLabels/ARM.lhs CONTEXT ARM_H instanceproofs ONLY ArchInvocationLabel

end
end
