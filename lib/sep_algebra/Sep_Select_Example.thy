(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_Select_Example
imports Sep_Select
begin

lemma sep_select: "(A \<and>* B \<and>* C \<and>* D) s \<Longrightarrow> (A \<and>* B \<and>* C \<and>* D) s"
  apply (sep_select 2)       (* moves the 2nd conjunct in the conclusions to the front *) 
  apply (sep_select 2 3 4 1) (* we can reorder multiple conjuncts at once *)
  apply (sep_select 2 3 4)   (* the list can be partial *)
  apply (sep_select_asm 3 4) (* sep_select_asm works for the assumptions *)
  oops

end
