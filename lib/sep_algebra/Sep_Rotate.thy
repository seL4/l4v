(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sep_Rotate
imports Sep_Select
begin

(* We can build rotators on the basis of selectors *)

ML \<open>
(* generic rotator *)

fun range lo hi =
  let
    fun r lo = if lo > hi then [] else lo::r (lo+1)
  in r lo end

fun rotator lens tactic ctxt i st =
  let
    val len  = case Seq.pull ((lens THEN' resolve0_tac [@{thm iffI}]) i st) of
                 NONE => 0
               | SOME (thm, _) => conj_length ctxt (Thm.cprem_of thm i)
    val nums = range 1 len
    val selector = sep_select_tactic lens
    val tac' = map (fn x => selector [x] ctxt THEN' tactic) nums
  in
    (selector [1] ctxt THEN' FIRST' tac') i st
  end

fun rotator' ctxt lens tactic = rotator lens tactic ctxt

fun sep_apply_tactic ctxt lens_tac thms = lens_tac THEN' eresolve_tac ctxt thms
\<close>

end
