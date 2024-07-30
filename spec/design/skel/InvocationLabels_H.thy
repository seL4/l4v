(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Kernel Invocation Labels"

theory InvocationLabels_H
imports ArchInvocationLabels_H
begin

text \<open>
  An enumeration of all system call labels.
\<close>

#INCLUDE_HASKELL SEL4/API/InvocationLabels.lhs ArchLabels= ONLY GenInvocationLabels InvocationLabel
#INCLUDE_HASKELL SEL4/API/InvocationLabels.lhs instanceproofs

end
