(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Simp_No_Conditional

imports Main

begin

text \<open>
Simplification without conditional rewriting. Setting the simplifier depth
limit to zero prevents attempts at conditional rewriting. This should make
the simplifier faster and more predictable on average. It may be particularly
useful in derived tactics and methods to avoid situations where the simplifier
repeatedly attempts and fails a conditional rewrite.

As always, there are caveats. Failing to perform a simple conditional rewrite
may open the door to expensive alternatives. Various simprocs which are
conditional in nature will not be deactivated.
\<close>

ML \<open>

structure Simp_No_Conditional = struct

val set_no_cond = Config.put Raw_Simplifier.simp_depth_limit 0

val simp_tac = Simplifier.simp_tac o set_no_cond
val asm_simp_tac = Simplifier.asm_simp_tac o set_no_cond
val full_simp_tac = Simplifier.full_simp_tac o set_no_cond
val asm_full_simp_tac = Simplifier.asm_full_simp_tac o set_no_cond

val clarsimp_tac = Clasimp.clarsimp_tac o set_no_cond
val auto_tac = Clasimp.auto_tac o set_no_cond

fun mk_method secs tac
    = Method.sections secs >> K (SIMPLE_METHOD' o tac)
val mk_clasimp_method = mk_method Clasimp.clasimp_modifiers

fun mk_clasimp_all_method tac =
    Method.sections Clasimp.clasimp_modifiers >> K (SIMPLE_METHOD o tac)

val simp_method = mk_method Simplifier.simp_modifiers
    (CHANGED_PROP oo asm_full_simp_tac)
val clarsimp_method = mk_clasimp_method (CHANGED_PROP oo clarsimp_tac)
val auto_method = mk_clasimp_all_method (CHANGED_PROP o auto_tac)

end

\<close>

method_setup simp_no_cond = \<open>Simp_No_Conditional.simp_method\<close>
    "Simplification with no conditional simplification."

method_setup clarsimp_no_cond = \<open>Simp_No_Conditional.clarsimp_method\<close>
    "Clarsimp with no conditional simplification."

method_setup auto_no_cond = \<open>Simp_No_Conditional.auto_method\<close>
    "Auto with no conditional simplification."

end
