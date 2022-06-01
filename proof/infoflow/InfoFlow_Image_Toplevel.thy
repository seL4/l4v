(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* This theory serves as a top-level theory for testing InfoFlow.
   It should import everything that we want tested as part of building the
   InfoFlow image.
*)

theory InfoFlow_Image_Toplevel
imports
  ArchNoninterference
  Noninterference_Base_Refinement
  PolicyExample
  PolicySystemSAC
  ExampleSystemPolicyFlows
  Example_Valid_State
begin
end
