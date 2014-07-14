(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory BenchBasics
  imports Benchmark
begin

lemma five_less_than_ten: "(5 :: nat) < 10"
  by simp

lemma p_or_not_p: "p \<or> \<not> p"
  by blast

lemma twelve_equals_six_plus_six: "(12 = (6 + 6 :: nat))"
  by simp

lemma twelve_equals_six_plus_six': "(12 = (6 + 6 :: nat)) \<equiv> True"
  by simp

lemma true_conj1: "True \<and> P \<equiv> P"
  by simp

lemma disj_flip: "(a \<or> b) = (b \<or> a)"
  by (rule disj_commute)

lemma disj_flip': "a \<or> b \<equiv> b \<or> a"
  apply (rule eq_reflection)
  apply (rule disj_commute)
  done

ML_file "bench_basics.ML"

end

