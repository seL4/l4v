(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(* This theory serves as a top-level theory for testing InfoFlow.
   It should import everything that we want tested as part of building the
   InfoFlow image.
*)

theory InfoFlow_Image_Toplevel
imports
  Noninterference
  Noninterference_Base_Refinement
  PolicyExample
  PolicySystemSAC
  ExampleSystemPolicyFlows
  Example_Valid_State
begin
end
