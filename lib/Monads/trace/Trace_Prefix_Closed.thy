(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_Prefix_Closed
  imports
    Trace_No_Trace
    Trace_Monad_Equations
    WPSimp
begin

subsection "Prefix Closed"

definition prefix_closed :: "('s, 'a) tmonad \<Rightarrow> bool" where
  "prefix_closed f = (\<forall>s. \<forall>x xs. (x # xs) \<in> fst ` f s \<longrightarrow> (xs, Incomplete) \<in> f s)"

lemmas prefix_closedD1 = prefix_closed_def[THEN iffD1, rule_format]

lemma in_fst_snd_image_eq:
  "x \<in> fst ` S = (\<exists>y. (x, y) \<in> S)"
  "y \<in> snd ` S = (\<exists>x. (x, y) \<in> S)"
  by (auto elim: image_eqI[rotated])

lemma in_fst_snd_image:
  "(x, y) \<in> S \<Longrightarrow> x \<in> fst ` S"
  "(x, y) \<in> S \<Longrightarrow> y \<in> snd ` S"
  by (auto simp: in_fst_snd_image_eq)

lemmas prefix_closedD = prefix_closedD1[OF _ in_fst_snd_image(1)]

lemma no_trace_prefix_closed:
  "no_trace f \<Longrightarrow> prefix_closed f"
  by (auto simp add: prefix_closed_def dest: no_trace_emp)


subsection \<open>Rules\<close>

lemma prefix_closed_bind:
  "\<lbrakk>prefix_closed f; \<forall>x. prefix_closed (g x)\<rbrakk> \<Longrightarrow> prefix_closed (f >>= g)"
  apply (subst prefix_closed_def, clarsimp simp: bind_def)
  apply (auto simp: Cons_eq_append_conv split: tmres.split_asm
             dest!: prefix_closedD[rotated];
         fastforce elim: rev_bexI)
  done

lemmas prefix_closed_bind[rule_format, wp_split]

lemma prefix_closed_put_trace_elem[iff]:
  "prefix_closed (put_trace_elem x)"
  by (clarsimp simp: prefix_closed_def put_trace_elem_def)

lemma prefix_closed_return[iff]:
  "prefix_closed (return x)"
  by (simp add: prefix_closed_def return_def)

lemma prefix_closed_put_trace[iff]:
  "prefix_closed (put_trace tr)"
  by (induct tr; clarsimp simp: prefix_closed_bind)

lemma prefix_closed_select[iff]:
  "prefix_closed (select S)"
  by (simp add: prefix_closed_def select_def image_def)

lemma prefix_closed_mapM[rule_format, wp_split]:
  "(\<forall>x \<in> set xs. prefix_closed (f x)) \<Longrightarrow> prefix_closed (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (clarsimp simp: mapM_Cons)
  apply (intro prefix_closed_bind allI; clarsimp)
  done

lemmas modify_prefix_closed[simp] = no_trace_prefix_closed[OF no_trace_all(3)]

lemmas await_prefix_closed[simp] = Await_sync_twp[THEN validI_prefix_closed]

lemma repeat_n_prefix_closed[intro!]:
  "prefix_closed f \<Longrightarrow> prefix_closed (repeat_n n f)"
  apply (induct n; simp)
  apply (auto intro: prefix_closed_bind)
  done

lemma repeat_prefix_closed[intro!]:
  "prefix_closed f \<Longrightarrow> prefix_closed (repeat f)"
  apply (simp add: repeat_def)
  apply (rule prefix_closed_bind; clarsimp)
  done

lemma parallel_prefix_closed[wp_split]:
  "\<lbrakk>prefix_closed f; prefix_closed g\<rbrakk>
   \<Longrightarrow> prefix_closed (parallel f g)"
  apply (subst prefix_closed_def, clarsimp simp: parallel_def)
  apply (subst (asm) zip.zip_Cons)
  apply (clarsimp split: list.splits)
  apply (drule(1) prefix_closedD)+
  apply fastforce
  done

end