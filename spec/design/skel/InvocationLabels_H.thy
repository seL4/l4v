(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Kernel Invocation Labels"

theory InvocationLabels_H
imports "$L4V_ARCH/ArchInvocationLabels_H"
begin

unqualify_types (in Arch)
  arch_invocation_label

text {*
  An enumeration of all system call labels.
*}

#INCLUDE_HASKELL SEL4/API/InvocationLabels.lhs ArchLabels= ONLY InvocationLabel
#INCLUDE_HASKELL SEL4/API/InvocationLabels.lhs instanceproofs

end
