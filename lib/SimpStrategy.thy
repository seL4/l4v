(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory SimpStrategy
imports Main
begin

text \<open>
Support for defining alternative simplifier strategies for some parts of terms
or some premises of rewrite rules. The "name" parameter to the simp_strategy
constant is used to identify which simplification strategy should be used on
this term. Note that, although names have type nat, it is safe for them to all
be defined as 0. The important thing is that the simplifier doesn't know they're
equal.
\<close>

definition
  simp_strategy :: "nat \<Rightarrow> ('a :: {}) \<Rightarrow> 'a"
where
  "simp_strategy name x \<equiv> x"

text \<open>
This congruence rule forbids the simplifier from simplifying the arguments of
simp_strategy normally.
\<close>

lemma simp_strategy_cong[cong]:
  "simp_strategy name x = simp_strategy name x"
  by simp

text \<open>
This strategy, or rather lack thereof, can be used to forbid simplification.
\<close>

definition
  NoSimp :: nat
where "NoSimp = 0"

text \<open>
This strategy indicates that a boolean subterm should be simplified only by
using explicit assumptions of the simpset.
\<close>

definition
  ByAssum :: nat
where "ByAssum = 0"

lemma Eq_TrueI_ByAssum:
  "P \<Longrightarrow> simp_strategy ByAssum P \<equiv> True"
  by (simp add: simp_strategy_def)

simproc_setup simp_strategy_ByAssum ("simp_strategy ByAssum b") =
  \<open>K (fn ss => fn ct => let
      val b = Thm.dest_arg ct
      val t = Thm.instantiate ([],[((("P",0),@{typ bool}), b)])
        @{thm Eq_TrueI_ByAssum}
      val prems = Raw_Simplifier.prems_of ss
    in get_first (try (fn p => p RS t)) prems end)\<close>

lemma ByAssum:
  "simp_strategy ByAssum P \<Longrightarrow> P"
  by (simp add: simp_strategy_def)

lemma simp_ByAssum_test:
  "P \<Longrightarrow> simp_strategy ByAssum P"
  by simp

text \<open>
Generic framework for instantiating a simproc which simplifies within a
simp_strategy with a given simpset.

The boolean determines whether simp_strategy Name True should be rewritten
to True.
\<close>

lemma simp_strategy_Eq_True:
  "simp_strategy name True \<equiv> True"
  by (simp add: simp_strategy_def)

ML \<open>
fun simp_strategy_True_conv ct = case Thm.term_of ct of
    (Const (@{const_name simp_strategy}, _) $ _ $ @{term True})
      => Thm.instantiate ([], [((("name",0), @{typ nat}), Thm.dest_arg1 ct)])
          @{thm simp_strategy_Eq_True}
  | _ => Conv.all_conv ct

fun new_simp_strategy thy (name : term) ss rewr_True =
let
  val ctxt = Proof_Context.init_global thy;
  val ss = Simplifier.make_simproc ctxt ("simp_strategy_" ^ fst (dest_Const name))
    {lhss = [@{term simp_strategy} $ name $ @{term x}],
     proc = (fn _ => fn ctxt' => fn ct =>
        ct
        |> (Conv.arg_conv (Simplifier.rewrite (put_simpset ss ctxt'))
          then_conv (if rewr_True then simp_strategy_True_conv
                      else Conv.all_conv))
        |> (fn c => if Thm.is_reflexive c then NONE else SOME c))
     }
in
  ss
end
\<close>

end
