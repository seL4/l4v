(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "VCPU"

theory VCPU_H
imports Hardware_H "../Structures_H"
  "../Invocations_H"
  "../TCB_H"
begin
context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs CONTEXT ARM_HYP_H
#INCLUDE_HASKELL SEL4/Object/VCPU/ARM_HYP.lhs CONTEXT ARM_HYP_H ArchInv=

end
end
