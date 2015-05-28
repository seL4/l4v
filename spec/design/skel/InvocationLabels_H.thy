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
imports "../../lib/Enumeration"
begin

text {*
  An enumeration of all system call labels.
*}

#INCLUDE_HASKELL SEL4/API/Invocation.lhs ONLY InvocationLabel isPDFlush isPageFlush
#INCLUDE_HASKELL SEL4/API/Invocation.lhs instanceproofs ONLY InvocationLabel

end
