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
	 The fault datatype. 
*)

chapter "Fault Structures"

theory Fault_H
imports Types_H
begin

#INCLUDE_HASKELL_PREPARSE SEL4/API/Types.lhs
#INCLUDE_HASKELL SEL4/API/Failures.lhs decls_only
#INCLUDE_HASKELL SEL4/API/Failures.lhs bodies_only

end
