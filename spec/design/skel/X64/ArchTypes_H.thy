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
   Types visible in the API. 
*)

chapter "Arch-dependant Types visible in the API"

theory ArchTypes_H
imports
  State_H
  Hardware_H
  "../../../lib/Lib"
begin

context X64 begin

#INCLUDE_HASKELL SEL4/API/Types/Universal.lhs all_bits

#INCLUDE_HASKELL SEL4/API/Types/X64.lhs CONTEXT X64
#INCLUDE_HASKELL SEL4/API/Types/X64.lhs CONTEXT X64 instanceproofs 

end (* context X64 *) 

end
