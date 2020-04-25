(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sep_Solve_Example
imports Sep_Solve
begin

(* sep_solve invokes sep_cancel and sep_mp repeatedly to solve the goal, and fails if it can't
   completely discharge it *)
axiomatization
  Moo :: "'a :: stronger_sep_algebra => bool" and
  Bar :: "'a :: stronger_sep_algebra => bool"
where  Moo_Bar[sep_cancel] : "Moo s \<Longrightarrow> Bar s"

lemma "((Bar \<and>* Q \<and>* R \<longrightarrow>* B) \<and>* Moo \<and>* A \<and>* R \<and>* Q) s \<Longrightarrow> (A \<and>* B) s"
  apply (sep_solve)
  done

(* encouraging better proof style with different command for schematics in assumption *)

schematic_goal "((Bar \<and>* Q \<and>* R \<longrightarrow>* B) \<and>* Moo \<and>* A \<and>* R \<and>* ?Q) s \<Longrightarrow> (A \<and>* B) s"
  apply (sep_schem)
  done

end
