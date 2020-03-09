(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Collects general lemmas in the capDL refinement proof.
   Those should eventually be moved to Lib.

   Also defines a single entry point for all drefine theories
   in which global simpset and notation changes can be made.
*)

theory Lemmas_D
imports
  "DBaseRefine.Include_D"
  MoreHOL
  MoreCorres
  "ExecSpec.InvocationLabels_H"
begin

no_notation bind_drop (infixl ">>" 60)

declare fun_upd_restrict_conv[simp del]

(* FIXME: move *)
lemma nonempty_pick_in:
  "a \<noteq> {} \<Longrightarrow> pick a \<in> a"
  by (metis all_not_in_conv someI_ex)

lemma pick_singleton[simp]:
  "pick {a} = a"
  apply (rule ccontr)
  apply (cut_tac nonempty_pick_in)
   apply fastforce
  apply fastforce
  done

(* FIXME: eventually move to AInvs *)
lemma is_tcb_TCB[simp]: "is_tcb (TCB t)"
  by (simp add: is_tcb)

declare dxo_wp_weak[wp del]
declare is_aligned_no_overflow[simp]

end
