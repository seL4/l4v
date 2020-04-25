(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
