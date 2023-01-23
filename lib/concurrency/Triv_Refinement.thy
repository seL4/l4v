(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory Triv_Refinement

imports
  "Monads.TraceMonadVCG"
  "Monads.Strengthen"

begin

text \<open>This is a simple (almost trivial) definition of refinement,
which simply resolves nondeterminism to a smaller set of options.\<close>
definition
  triv_refinement :: "('s,'a) tmonad \<Rightarrow> ('s,'a) tmonad \<Rightarrow> bool"
where
  "triv_refinement aprog cprog = (\<forall>s. cprog s \<subseteq> aprog s)"

lemma triv_refinement_mono_bind:
  "triv_refinement a c \<Longrightarrow> triv_refinement (a >>= b) (c >>= b)"
  "(\<forall>x. triv_refinement (b x) (d x)) \<Longrightarrow> triv_refinement (a >>= b) (a >>= d)"
   apply (simp add: triv_refinement_def bind_def)
   apply (intro allI UN_mono; simp)
  apply (simp only: triv_refinement_def bind_def2 split_def)
  apply (intro Un_mono allI order_refl UN_mono image_mono)
  apply simp
  done

lemma triv_refinement_trans:
  "triv_refinement f g \<Longrightarrow> triv_refinement g h
    \<Longrightarrow> triv_refinement f h"
  by (auto simp add: triv_refinement_def)

lemma triv_refinement_bind:
  "triv_refinement a c
    \<Longrightarrow> (\<forall>x. triv_refinement (b x) (d x))
    \<Longrightarrow> triv_refinement (bind a b) (bind c d)"
  by (metis triv_refinement_mono_bind triv_refinement_trans)

lemma triv_refinement_mono_parallel:
  "triv_refinement a b \<Longrightarrow> triv_refinement (parallel a c) (parallel b c)"
  apply (simp add: triv_refinement_def parallel_def split_def)
  apply blast
  done

lemma triv_refinement_mono_parallel':
  "triv_refinement a b \<Longrightarrow> triv_refinement (parallel c a) (parallel c b)"
  apply (simp add: triv_refinement_def parallel_def split_def)
  apply blast
  done

lemma triv_refinement_parallel:
  "triv_refinement a b
    \<Longrightarrow> triv_refinement c d
    \<Longrightarrow> triv_refinement (parallel a c) (parallel b d)"
  by (metis triv_refinement_mono_parallel triv_refinement_mono_parallel'
    triv_refinement_trans)

lemma select_subset:
  "(select S s \<subseteq> select S' s') = (S \<subseteq> S' \<and> (S \<noteq> {} \<longrightarrow> s = s'))"
  by (auto simp add: select_def)

lemma triv_refinement_select:
  "S' \<subseteq> S \<Longrightarrow> triv_refinement (select S) (select S')"
  by (simp add: triv_refinement_def select_subset)

lemma triv_refinement_select_eq:
  "triv_refinement (select S) (select S') = (S' \<subseteq> S)"
  by (simp add: triv_refinement_def select_subset)

lemma triv_refinement_rely:
  "(\<And>s0 s. R' s0 s \<Longrightarrow> R s0 s) \<Longrightarrow>
   triv_refinement (rely f R s0) (rely f R' s0)"
  unfolding rely_def triv_refinement_def rely_cond_def
  by auto

lemma triv_refinement_rely2:
  "triv_refinement f g \<Longrightarrow>
   triv_refinement (rely f R s0) (rely g R s0)"
  unfolding rely_def triv_refinement_def rely_cond_def
  by auto

lemma rely_rely_triv_refinement:
 "(\<And>s0 s. R s0 s \<Longrightarrow> R' s0 s) \<Longrightarrow>
 triv_refinement (rely f R' s0) (rely (rely f R s0) R' s0)"
  by (clarsimp simp: triv_refinement_def rely_def parallel_def)

lemma validI_triv_refinement:
  "triv_refinement f g
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>
    \<Longrightarrow> prefix_closed g
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding rely_def triv_refinement_def validI_def
  by fastforce

lemma valid_triv_refinement:
  "triv_refinement f g
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> g \<lbrace>Q\<rbrace>"
  unfolding rely_def triv_refinement_def valid_def mres_def
  by (fastforce elim: image_eqI[rotated])

lemma triv_refinement_refl:
  "triv_refinement f f"
  by (simp add: triv_refinement_def)

lemma triv_refinement_select_concrete_All:
  "\<forall>x \<in> S. triv_refinement aprog (cprog x)
    \<Longrightarrow> triv_refinement aprog (select S >>= cprog)"
  by (auto simp add: triv_refinement_def bind_def select_def)

lemma triv_refinement_select_abstract_x:
  "x \<in> S \<Longrightarrow> triv_refinement (aprog x) cprog
    \<Longrightarrow> triv_refinement (select S >>= aprog) cprog"
  by (auto simp add: triv_refinement_def bind_def select_def)

lemmas triv_refinement_elemD
    = triv_refinement_def[THEN iffD1, rule_format, THEN subsetD]

end
