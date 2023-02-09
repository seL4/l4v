(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory Plus2_Prefix
imports
  Lib.Lib
  Prefix_Refinement
begin

section \<open>The plus2 example.\<close>

text \<open>
This example presents an application of prefix refinement
to solve the plus2 verification problem.

The function below can be proven to do two increments per
instance when grouped in parallel. But RG-reasoning doesn't
work well for this proof, since the state change (+1) performed
by the counterparts must be allowed by the rely, which must be
transitively closed, allowing any number of (+1) operations,
which is far too general.

We address the issue with a ghost variable which records the number
of increments by each thread. We use prefix refinement to relate the
program with ghost variable to the initial program.
\<close>

definition
  "plus2 \<equiv> do env_steps; modify ((+) (1 :: nat));
    interference; modify ((+) 1); interference od"

section \<open>The ghost-extended program.\<close>

record
  plus2_xstate =
    mainv :: nat
    threadv :: "nat \<Rightarrow> nat"

definition
  point_update :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b))"
where
  "point_update x fup f = f (x := fup (f x))"

definition
  "plus2_x tid \<equiv> do env_steps;
    modify (mainv_update ((+) 1) o threadv_update (point_update tid ((+) 1)));
    interference;
    modify (mainv_update ((+) 1) o threadv_update (point_update tid ((+) 1)));
    interference
  od"

section \<open>Verifying the extended @{term plus2}.\<close>
text \<open>The RG-reasoning needed to verify the @{term plus2_x} program.\<close>
definition
  "plus2_inv tids s = (mainv s = sum (threadv s) tids)"

definition
  "plus2_rel tids fix_tids s0 s
    = ((plus2_inv tids s0 \<longrightarrow> plus2_inv tids s) \<and> (\<forall>tid \<in> fix_tids. threadv s tid = threadv s0 tid))"

lemma plus2_rel_trans[simp]:
  "rtranclp (plus2_rel tids ftids) = plus2_rel tids ftids"
  apply (rule rtranclp_id2)
   apply (simp add: plus2_rel_def)
  apply (clarsimp simp: plus2_rel_def)
  done

lemma plus2_inv_Suc[simp]:
  "tid \<in> tids \<Longrightarrow> finite tids
    \<Longrightarrow> plus2_inv tids (mainv_update Suc (threadv_update (point_update tid Suc) s))
        = plus2_inv tids s"
  apply (simp add: plus2_inv_def point_update_def)
  apply (simp add: sum.If_cases[where h=f and g=f and P="(=) tid" and A="tids" for f x, simplified])
  done

theorem plus2_x_property:
  "\<lbrace>\<lambda>s0 s. plus2_inv tids s \<and> threadv s tid = 0 \<and> s = s0 \<and> tid \<in> tids \<and> finite tids\<rbrace>,\<lbrace>plus2_rel tids {tid}\<rbrace>
    plus2_x tid \<lbrace>plus2_rel tids (- {tid})\<rbrace>,\<lbrace>\<lambda>_ _ s. plus2_inv tids s \<and> threadv s tid = 2\<rbrace>"
  apply (simp add: plus2_x_def)
  apply (rule validI_weaken_pre)
   apply wp
  apply clarsimp
  apply (clarsimp simp: plus2_rel_def point_update_def)
  done

corollary plus2_x_parallel:
  "\<lbrace>\<lambda>s0 s. mainv s = 0 \<and> (\<forall>tid \<in> {1, 2}. threadv s tid = 0) \<and> s = s0\<rbrace>,\<lbrace>\<lambda>a b. a = b\<rbrace>
    parallel (plus2_x 1) (plus2_x 2) \<lbrace>\<lambda>s0 s. True\<rbrace>,\<lbrace>\<lambda>_ s0 s. mainv s = 4\<rbrace>"
  apply (rule validI_weaken_pre)
   apply (rule validI_strengthen_post)
    apply ((rule rg_validI plus2_x_property[where tids="{1, 2}"])+; simp add: plus2_rel_def le_fun_def)
   apply (clarsimp simp: plus2_inv_def)
  apply (clarsimp simp add: plus2_inv_def)
  done

section \<open>Mapping across prefix refinement.\<close>
text \<open>Proving prefix refinement of @{term plus2} and @{term plus2_x} and
deriving the final result.\<close>

lemma env_stable:
  "env_stable AR R (\<lambda>s t. t = mainv s) (\<lambda>s t. t = mainv s) \<top>"
  apply (simp add: env_stable_def rely_stable_def env_rely_stable_iosr_def)
  apply (simp add: plus2_xstate.splits)
  done

abbreviation(input)
  "p_refn rvr P Q AR R \<equiv> prefix_refinement (\<lambda>s t. t = mainv s) (\<lambda>s t. t = mainv s)
    (\<lambda>s t. t = mainv s) rvr P Q AR R"

theorem pfx_refn_plus2_x:
  "p_refn (\<top>\<top>) (=) (\<top>\<top>) AR R (plus2_x tid) plus2"
  apply (simp add: plus2_x_def plus2_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule pfx_refn_bind prefix_refinement_interference
         prefix_refinement_env_steps allI
         pfx_refn_modifyT env_stable
       | simp
       | wp)+
  done

lemma par_tr_fin_plus2_x:
  "par_tr_fin_principle (plus2_x tid)"
  by (simp add: plus2_x_def par_tr_fin_interference par_tr_fin_bind)

lemma prefix_closed_plus2:
  "prefix_closed plus2"
  apply (simp add: plus2_def)
  apply (rule validI_prefix_closed_T, rule validI_weaken_pre, wp)
  apply simp
  done

theorem plus2_parallel:
  "\<lbrace>\<lambda>s0 s. s = 0 \<and> s = s0\<rbrace>,\<lbrace>\<lambda>a b. a = b\<rbrace>
    parallel plus2 plus2 \<lbrace>\<lambda>s0 s. True\<rbrace>,\<lbrace>\<lambda>_ s0 s. s = 4\<rbrace>"
  apply (rule_tac sr="\<lambda>s t. t = mainv s" in prefix_refinement_validI)
  apply (rule prefix_refinement_parallel_triv;
      ((rule par_tr_fin_plus2_x prefix_closed_plus2)?))
       apply (rule pfx_refn_plus2_x[where tid=1])
      apply (rule pfx_refn_plus2_x[where tid=2])
     apply clarsimp
     apply (rule validI_strengthen_post)
      apply (rule plus2_x_parallel[simplified])
     apply clarsimp
    apply (clarsimp simp: plus2_xstate.splits)
    apply (strengthen exI[where x="f(1 := x, 2 := y)" for f x y])
    apply simp
   apply clarsimp
  apply (intro parallel_prefix_closed prefix_closed_plus2)
  done

section \<open>Generalising\<close>
text \<open>Just for fun, generalise to arbitrarily many
copies of the @{term plus2} program.\<close>

lemma plus2_x_n_parallel_induct:
  "n > 0 \<Longrightarrow> n \<le> N \<Longrightarrow>
  \<lbrace>\<lambda>s0 s. plus2_inv {..< N} s \<and> (\<forall>i < N. threadv s i = 0) \<and> s = s0\<rbrace>,\<lbrace>plus2_rel {..< N} {..< n}\<rbrace>
    fold parallel (map plus2_x [1 ..< n]) (plus2_x 0) \<lbrace>plus2_rel {..< N} ( - {..< n})\<rbrace>,\<lbrace>\<lambda>_ _ s.
        plus2_inv {..< N} s \<and> (\<forall>i < n. threadv s i = 2)\<rbrace>"
  apply (induct n)
   apply simp
  apply (case_tac n)
   apply (simp only: lessThan_Suc)
   apply simp
   apply (rule validI_weaken_pre, rule plus2_x_property)
   apply clarsimp
  apply (clarsimp split del: if_split)
  apply (rule validI_weaken_pre, rule validI_strengthen_post,
    rule rg_validI, rule plus2_x_property[where tids="{..< N}"],
    assumption, (clarsimp simp: plus2_rel_def)+)
   apply (auto dest: less_Suc_eq[THEN iffD1])[1]
  apply clarsimp
  done

theorem plus2_x_n_parallel:
  "n > 0 \<Longrightarrow>
  \<lbrace>\<lambda>s0 s. mainv s = 0 \<and> (\<forall>i < n. threadv s i = 0) \<and> s = s0\<rbrace>,\<lbrace>plus2_rel {..< n} {..< n}\<rbrace>
    fold parallel (map plus2_x [1 ..< n]) (plus2_x 0) \<lbrace>\<lambda>s0 s. True\<rbrace>,\<lbrace>\<lambda>_ _ s. mainv s = (n * 2)\<rbrace>"
  apply (rule validI_weaken_pre, rule validI_strengthen_post,
      rule validI_strengthen_guar, erule plus2_x_n_parallel_induct)
     apply simp
    apply simp
   apply (clarsimp simp: plus2_inv_def)
  apply (clarsimp simp: plus2_inv_def)
  done

lemma par_tr_fin_principle_parallel:
  "par_tr_fin_principle f \<Longrightarrow> par_tr_fin_principle g
    \<Longrightarrow> par_tr_fin_principle (parallel f g)"
  apply (subst par_tr_fin_principle_def, clarsimp simp: parallel_def3)
  apply (drule(1) par_tr_fin_principleD)+
  apply (clarsimp simp: neq_Nil_conv)
  done

lemma fold_parallel_par_tr_fin_principle[where xs="rev xs" for xs, simplified]:
  "\<forall>x \<in> insert x (set xs). par_tr_fin_principle x
    \<Longrightarrow> par_tr_fin_principle (fold parallel (rev xs) x)"
  by (induct xs, simp_all add: par_tr_fin_principle_parallel)

lemma fold_parallel_prefix_closed[where xs="rev xs" for xs, simplified]:
  "\<forall>x \<in> insert x (set xs). prefix_closed x
    \<Longrightarrow> prefix_closed (fold parallel (rev xs) x)"
  by (induct xs, simp_all add: parallel_prefix_closed)

lemma bipred_disj_top_eq:
  "(Rel or (\<lambda>_ _. True)) = (\<lambda>_ _. True)"
  "((\<lambda>_ _. True) or Rel) = (\<lambda>_ _. True)"
  by auto

lemma fold_parallel_pfx_refn_induct:
  "list_all2 (prefix_refinement sr sr sr (\<lambda>_ _. True) P Q (\<top>\<top>) (\<top>\<top>)) xs ys
    \<Longrightarrow> prefix_refinement sr sr sr (\<lambda>_ _. True) P Q (\<top>\<top>) (\<top>\<top>) x y
    \<Longrightarrow> \<forall>x \<in> set (x # xs). par_tr_fin_principle x
    \<Longrightarrow> \<forall>y \<in> set (y # ys). prefix_closed y
    \<Longrightarrow> prefix_refinement sr sr sr (\<lambda>_ _. True) P Q (\<top>\<top>) (\<top>\<top>)
        (fold parallel (rev xs) x) (fold parallel (rev ys) y)"
  apply (induct rule: list_all2_induct; simp)
  apply (rule prefix_refinement_parallel_triv[simplified bipred_disj_top_eq]; simp?)
   apply (clarsimp simp: fold_parallel_par_tr_fin_principle
                         fold_parallel_prefix_closed)+
  done

lemmas fold_parallel_pfx_refn
    = fold_parallel_pfx_refn_induct[where xs="rev xs" and ys="rev ys" for xs ys, simplified]

theorem plus2_n_parallel:
  "n > 0
    \<Longrightarrow> \<lbrace>\<lambda>s0 s. s = 0 \<and> s = s0\<rbrace>,\<lbrace>\<lambda>a b. a = b\<rbrace>
        fold parallel (replicate (n - 1) plus2) plus2 \<lbrace>\<lambda>s0 s. True\<rbrace>,\<lbrace>\<lambda>_ s0 s. s = n * 2\<rbrace>"
  apply (rule_tac sr="\<lambda>s t. t = mainv s" in prefix_refinement_validI)
      apply (rule prefix_refinement_weaken_rely,
      rule_tac xs="map plus2_x [1 ..< n]" in fold_parallel_pfx_refn)
           apply (clarsimp simp: list_all2_conv_all_nth)
           apply (rule pfx_refn_plus2_x)
          apply (rule pfx_refn_plus2_x[where tid=0])
         apply (simp add: par_tr_fin_plus2_x)
        apply (simp add: prefix_closed_plus2)
       apply (simp add: le_fun_def)
      apply (simp add: le_fun_def)
     apply simp
     apply (rule validI_strengthen_post, rule plus2_x_n_parallel[simplified], simp)
     apply clarsimp
    apply (clarsimp simp: plus2_xstate.splits exI[where x="\<lambda>_. 0"])
   apply clarsimp
   apply (rule exI, strengthen refl)
   apply (clarsimp simp: plus2_rel_def plus2_inv_def)
  apply (rule fold_parallel_prefix_closed)
  apply (simp add: prefix_closed_plus2)
  done

end
