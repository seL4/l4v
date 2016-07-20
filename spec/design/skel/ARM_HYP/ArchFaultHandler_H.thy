(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Fault Handlers"

theory ArchFaultHandler_H
imports "../TCB_H" "../Structures_H"
begin

context Arch begin global_naming ARM_HYP_H


#INCLUDE_HASKELL_PREPARSE SEL4/API/Failures/ARM_HYP.lhs

#INCLUDE_HASKELL SEL4/API/Faults/ARM_HYP.lhs decls_only
#INCLUDE_HASKELL SEL4/API/Faults/ARM_HYP.lhs bodies_only

end


end
