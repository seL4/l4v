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
imports "../../../lib/Enumeration"
begin

text {*
  An enumeration of arch-specific system call labels.
*}

#INCLUDE_HASKELL SEL4/API/InvocationLabels/ARM.lhs ONLY ArchInvocationLabel 
#INCLUDE_HASKELL SEL4/API/InvocationLabels/ARM.lhs instanceproofs ONLY ArchInvocationLabel

end
