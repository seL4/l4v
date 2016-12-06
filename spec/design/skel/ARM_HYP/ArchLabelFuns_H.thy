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
context Arch begin global_naming ARM_HYP_H
text {*
  Arch-specific functions on invocation labels
*}

#INCLUDE_HASKELL SEL4/API/Invocation/ARM_HYP.lhs CONTEXT ARM_HYP_H ONLY isPDFlushLabel isPageFlushLabel

end
end
