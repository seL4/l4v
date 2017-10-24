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

theory Eval_Bool

imports Try_Methods

begin

text {* The eval_bool method/simproc uses the code generator setup to
reduce terms of boolean type to True or False. Reducing booleans to
True or False is nearly always desirable, and is a fairly good heuristic
for when to make use of definitions/code-equations. *}

ML {*
structure Eval_Bool = struct

exception Failure

fun eval ctxt ct = let
    val t = Thm.term_of ct
    val _ = Term.fold_aterms (fn Free _ => raise Failure
      | Var _ => raise Failure | _ => ignore) t ()
    val is_bool = member (op aconv) [@{term True}, @{term False}]
    val _ = not (is_bool t) orelse raise Failure
    val ev = the (try (Code_Simp.dynamic_conv ctxt) ct)
  in if is_bool (Thm.term_of (Thm.rhs_of ev))
    then SOME ev else NONE end
  handle Failure => NONE | Option => NONE

val simproc = Simplifier.make_simproc @{context} "eval_bool"
  { lhss = [@{term "b :: bool"}], proc = K eval }

end
*}

method_setup eval_bool = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD'
    (CHANGED o simp_tac (clear_simpset ctxt
        addsimprocs [Eval_Bool.simproc])))\<close>
    "use code generator setup to simplify booleans in goals to True or False"

add_try_method eval_bool

text {* Testing. *}
definition
  eval_bool_test_seq :: "int list"
where
  "eval_bool_test_seq = [2, 3, 4, 5, 6, 7, 8]"

lemma
  "eval_bool_test_seq ! 4 = 6 \<and> (3 :: nat) < 4
    \<and> sorted eval_bool_test_seq"
  by eval_bool

end