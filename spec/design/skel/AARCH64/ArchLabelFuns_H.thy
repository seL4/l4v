(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Architecture-specific Invocation Label Functions"

theory ArchLabelFuns_H
imports InvocationLabels_H
begin
context Arch begin arch_global_naming (H)

text \<open>
  Arch-specific functions on invocation labels
\<close>

#INCLUDE_HASKELL SEL4/API/Invocation/AARCH64.hs CONTEXT AARCH64_H \
  ONLY isVSpaceFlushLabel isPageFlushLabel

end
end
