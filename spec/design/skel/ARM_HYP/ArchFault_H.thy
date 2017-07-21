(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
  VSpace lookup code.
*)

theory ArchFault_H
imports "../Types_H"
(*  "../KI_Decls_H"
  ArchVSpaceDecls_H *)
begin
context Arch begin global_naming ARM_HYP_H


#INCLUDE_HASKELL SEL4/API/Failures/ARM.lhs CONTEXT ARM_HYP_H decls_only
#INCLUDE_HASKELL SEL4/API/Failures/ARM.lhs CONTEXT ARM_HYP_H bodies_only


end
end
