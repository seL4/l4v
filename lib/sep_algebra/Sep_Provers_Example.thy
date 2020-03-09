(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sep_Provers_Example
imports Sep_Provers
begin

axiomatization
  Moo :: "'a :: stronger_sep_algebra => bool" and
  Bar :: "'a :: stronger_sep_algebra => bool"
where  Moo_Bar : "Moo s \<Longrightarrow> Bar s"

(* sep_rule is 'rule' with rotations of the conjuncts in the conclusions *)
lemma "(A \<and>* B \<and>* C \<and>* Bar) s"
  apply (sep_rule Moo_Bar)
  oops

(* sep_drule is 'drule' with rotations of the conjuncts in the assumptions *)
lemma "(A \<and>* B \<and>* C \<and>* Moo) s \<Longrightarrow> R"
  apply (sep_drule Moo_Bar)
  oops

(* sep_erule is 'erule' with rotations of the conjuncts in either the assumptions,
   the conclusions, or both. These are sep_erule, sep_erule_concl, and sep_erule_full respectively
    *)
lemma "(A \<and>* B \<and>* C \<and>* Moo) s \<Longrightarrow> (A \<and>* B \<and>* C \<and>* Bar) s"
   (* In this case we need to rotate both, so we use sep_erule_full *)
  apply (sep_erule_full Moo_Bar)
  apply (assumption)
  done

axiomatization where Moo_Bar_R: "(Moo \<and>* R) s \<Longrightarrow> (Bar \<and>* R) s"

(* When we have theorems with the frame explicitly mentioned, we have to invoke our tactics with
   (direct) option *)

lemma "(A \<and>* B \<and>* C \<and>* Moo) s \<Longrightarrow> (A \<and>* B \<and>* C \<and>* Bar) s"
  apply (sep_erule_full (direct) Moo_Bar_R)
  done

end
