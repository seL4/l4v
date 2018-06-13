(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "Architecture-specific Invocation Labels"

theory ArchInvocationLabels_H
imports
  "Word_Lib.Enumeration"
  "../../machine/Setup_Locale"
begin
context Arch begin global_naming RISCV64_H

text {*
  An enumeration of arch-specific system call labels.
*}

#INCLUDE_HASKELL SEL4/API/InvocationLabels/RISCV64.hs CONTEXT RISCV64_H ONLY ArchInvocationLabel

end

context begin interpretation Arch .
requalify_types arch_invocation_label
end

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/API/InvocationLabels/RISCV64.hs CONTEXT RISCV64_H instanceproofs ONLY ArchInvocationLabel

end
end
