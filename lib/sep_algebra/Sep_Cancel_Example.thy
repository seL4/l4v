(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_Cancel_Example
imports Sep_Cancel
begin

(* sep_cancel performs cancellative elimination of conjuncts using the sep_cancel set. 
   This is fairly similar to sep_erule_full sep_cancel. *)

lemma "(A \<and>* B \<and>* C \<and>* D) s \<Longrightarrow> (C \<and>* D \<and>* A \<and>* B) s"
  apply sep_cancel
  apply sep_cancel
  done

end
