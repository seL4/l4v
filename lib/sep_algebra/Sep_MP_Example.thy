(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_MP_Example
imports Sep_MP
begin

lemma "((P \<and>* Q \<and>* R \<longrightarrow>* B) \<and>* P \<and>* A \<and>* R \<and>* Q) s \<Longrightarrow> (A \<and>* B) s"
  (* sep_mp attempts to solve goals that could be solved by careful use of the sep_mp theorem *)
  apply (sep_mp)
  apply (clarsimp simp: sep_conj_ac)
  done

(* Sep_mp uses the sep_cancel set to solve goals *)

axiomatization
  Moo :: "'a :: stronger_sep_algebra => bool" and
  Bar :: "'a :: stronger_sep_algebra => bool"
where  Moo_Bar[sep_cancel] : "Moo s \<Longrightarrow> Bar s" 


lemma "((Bar \<and>* Q \<and>* R \<longrightarrow>* B) \<and>* Moo \<and>* A \<and>* R \<and>* Q) s \<Longrightarrow> (A \<and>* B) s"
  apply (sep_mp)
  apply (clarsimp simp: sep_conj_ac)
  done

end
