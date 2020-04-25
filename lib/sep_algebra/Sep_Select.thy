(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sep_Select
imports Separation_Algebra
begin

ML_file "sep_tactics.ML"

ML\<open>
  structure SepSelect_Rules = Named_Thms (
    val name = @{binding "sep_select"}
    val description = "sep_select rules"
  )
\<close>
setup SepSelect_Rules.setup

ML \<open>
  structure SepSelectAsm_Rules = Named_Thms (
    val name = @{binding "sep_select_asm"}
    val description = "sep_select_asm rules"
  )
\<close>
setup SepSelectAsm_Rules.setup

ML \<open>
  fun sep_selects_tactic ns ctxt =
    sep_select_tactic (resolve_tac ctxt (SepSelect_Rules.get ctxt)) ns ctxt

  fun sep_select_asms_tactic ns ctxt =
    sep_select_tactic (dresolve_tac ctxt (SepSelectAsm_Rules.get ctxt)) ns ctxt
\<close>

method_setup sep_select_asm = \<open>
  Scan.lift (Scan.repeat Parse.int) >>
    (fn ns => fn ctxt => SIMPLE_METHOD' (sep_select_asms_tactic ns ctxt))
\<close> "Reorder assumptions"

method_setup sep_select = \<open>
  Scan.lift (Scan.repeat Parse.int) >>
    (fn ns => fn ctxt => SIMPLE_METHOD' (sep_selects_tactic ns ctxt))
\<close> "Reorder conclusions"

lemma sep_eq [sep_select]: "(\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> T s \<Longrightarrow> (P \<and>* R) s" by clarsimp
lemma sep_asm_eq [sep_select_asm]: "(P \<and>* R) s \<Longrightarrow> (\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> T s" by clarsimp

ML \<open>
  (* export method form of these two for use outisde this entry *)

  fun sep_select_method lens ns ctxt =
    SIMPLE_METHOD' (sep_select_tactic lens ns ctxt)

  fun sep_select_generic_method asm thms ns ctxt =
    sep_select_method (if asm then dresolve_tac ctxt thms else resolve_tac ctxt thms) ns ctxt
\<close>

method_setup sep_select_gen = \<open>
  Attrib.thms --| Scan.lift Args.colon -- Scan.lift (Scan.repeat Parse.int) -- Scan.lift (Args.mode "asm") >>
    (fn ((lens, ns), asm) => sep_select_generic_method asm lens ns)
\<close>

end
