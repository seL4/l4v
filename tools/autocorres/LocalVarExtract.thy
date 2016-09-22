(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Transform the state of a L1 monad to remove local variables, lifting them to
 * Isabelle's logic.
 *)

theory LocalVarExtract
imports SimplConv L2Defs
begin

(* These are used to translate unsimplified L1_specs. *)
lemma Collect_prod_inter:
  "{(s, t). P s t} \<inter> {(s, t). Q s t} = {(s, t). P s t \<and> Q s t}"
  by (fastforce intro: set_eqI)

lemma Collect_prod_union:
  "{(s, t). P s t} \<union> {(s, t). Q s t} = {(s, t). P s t \<or> Q s t}"
  by (fastforce intro: set_eqI)

end
