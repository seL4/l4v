(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Resurrect old "defs" command which was removed in Isabelle 2016.
 * Should be replaced with overloading..definition..end blocks. *)

theory Defs
imports Main
keywords "defs" :: thy_decl and "consts'" :: thy_decl
begin

ML_file "defs.ML"

end

