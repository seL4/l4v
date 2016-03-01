(*
 * @TAG(BSD)
 *
 *)

(* Resurrect old "defs" command which was removed in Isabelle 2016. 
 * Should be replaced with overloading..definition..end blocks. *)

theory Defs
imports Main
keywords "defs" :: thy_decl
begin

ML_file "defs.ML"

end

