(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Bitwise tactic for Signed Words"

theory Bitwise_Signed
imports
  "HOL-Library.Word"
  Bitwise
  Signed_Words
begin

ML \<open>fun bw_tac_signed ctxt = let
  val (ss, sss) = Word_Bitwise_Tac.expand_word_eq_sss
  val sss = nth_map 2 (fn ss => put_simpset ss ctxt addsimps @{thms len_signed} |> simpset_of) sss
in
    foldr1 (op THEN_ALL_NEW)
      ((CHANGED o safe_full_simp_tac (put_simpset ss ctxt)) ::
        map (fn ss => safe_full_simp_tac (put_simpset ss ctxt)) sss)
  end;
\<close>

method_setup word_bitwise_signed =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (bw_tac_signed ctxt 1))\<close>
  "decomposer for word equalities and inequalities into bit propositions on concrete word lengths"

end
