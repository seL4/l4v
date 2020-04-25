(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sep_Util
imports
  Sep_Algebra_L4v
  "HOL-Eisbach.Eisbach"
begin

(* The sep_simp, sep_flatten, and sep_map tactics. *)

ML \<open>
fun all_rotator lens tactic ctxt i st =
  let
    val len = case Seq.pull ((lens THEN' resolve0_tac [@{thm iffI}]) i st) of
                NONE => 0
              | SOME (thm, _) => conj_length ctxt (Thm.cprem_of thm i)
    val nums = range 1 len
    val selector = sep_select_tactic lens
    val tac' = map (fn x => selector [x] ctxt THEN' tactic) nums
    val every = fold (fn x => fn y => x THEN_ALL_NEW TRY o y) tac' (K all_tac)
  in
    (selector [1] ctxt THEN' every THEN' (TRY o selector (rev nums) ctxt)) i st
  end

fun sep_all tac ctxt =
  let fun r lens tactic = rotator lens tactic ctxt
  in
    (TRY o sep_flatten ctxt) THEN' (tac |> r (sep_asm_select ctxt))
  end

fun sep_simp thms ctxt =
   let val ctxt' = ctxt addsimps thms
       val clarsimp' = CHANGED_PROP o clarsimp_tac ctxt'
 in REPEAT_ALL_NEW (sep_all clarsimp' ctxt)
end

fun sep_simp_method (thms : thm list) ctxt = SIMPLE_METHOD' (sep_simp thms ctxt)
\<close>

method_setup sep_flatten = \<open>
  Scan.succeed (SIMPLE_METHOD' o sep_flatten)
\<close>

(* sep_flatten is a tactic to apply the associativity rule for separating conjunction,
   and nothing else. *)

method_setup sep_simp = \<open>
 Attrib.thms >> sep_simp_method
\<close>

(* sep_simp repeatedly applies clarsimp, rotating the premises in-between invocations,
   until it cannot apply. *)

method sep_map uses thms = ((sep_drule thms, sep_flatten?)+)[1]

(* sep_map attempts to apply a rule destructively to each conjunct that matches. *)

end