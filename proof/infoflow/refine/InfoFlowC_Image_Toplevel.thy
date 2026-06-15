(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* This theory serves as a top-level theory for testing InfoFlowC.
   It should import everything that we want tested as part of building the
   InfoFlowC image.
*)

theory InfoFlowC_Image_Toplevel
imports
  Noninterference_Refinement
  Example_Valid_StateH
begin
end
