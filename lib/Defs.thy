(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Resurrect old "defs" command which was removed in Isabelle 2016.
 * Should be replaced with overloading..definition..end blocks. *)

theory Defs
imports Main
keywords "defs" :: thy_decl and "consts'" :: thy_decl
begin

ML_file "defs.ML"

end
