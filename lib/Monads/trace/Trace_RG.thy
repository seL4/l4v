(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_RG
  imports
    Trace_VCG
    Trace_Monad_Equations
    Trace_No_Trace
begin

section \<open>Rely-Guarantee Logic\<close>

subsection \<open>Validity\<close>

text \<open>
  This section defines a Rely_Guarantee logic for partial correctness for
  the interference trace monad.

  The logic is defined semantically. Rules work directly on the
  validity predicate.

  In the interference trace monad, RG validity is a quintuple of precondition,
  rely, monad, guarantee, and postcondition. The precondition is a function
  from initial state to current state to bool (a state predicate), the rely and
  guarantee are functions from state before to state after to bool, and the
  postcondition is a function from return value to last state in the trace to
  final state to bool. A quintuple is valid if for all initial and current
  states that satisfy the precondition and all traces that satisfy the rely,
  all of the pssible self steps performed by the monad satisfy the guarantee
  and all of the result values and result states that are returned by the monad
  satisfy the postcondition. Note that if the computation returns an empty
  trace and no successful results then the quintuple is trivially valid. This
  means @{term "assert P"} does not require us to prove that @{term P} holds,
  but rather allows us to assume @{term P}! Proving non-failure is done via a
  separate predicate and calculus (see Trace_No_Fail).\<close>

primrec trace_steps :: "(tmid \<times> 's) list \<Rightarrow> 's \<Rightarrow> (tmid \<times> 's \<times> 's) set" where
    "trace_steps (elem # trace) s0 = {(fst elem, s0, snd elem)} \<union> trace_steps trace (snd elem)"
  | "trace_steps [] s0 = {}"

lemma trace_steps_nth:
  "trace_steps xs s0 = (\<lambda>i. (fst (xs ! i), (if i = 0 then s0 else snd (xs ! (i - 1))), snd (xs ! i))) ` {..< length xs}"
proof (induct xs arbitrary: s0)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  show ?case
    apply (simp add: lessThan_Suc_eq_insert_0 Cons image_image nth_Cons')
    apply (intro arg_cong2[where f=insert] refl image_cong)
    apply simp
    done
qed

text \<open>rg_pred type: Rely-Guaranty predicates (state before => state after => bool)\<close>
type_synonym 's rg_pred = "'s \<Rightarrow> 's \<Rightarrow> bool"

text \<open>Abbreviations for trivial postconditions (taking three arguments):\<close>
abbreviation(input)
  toptoptop :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" ("\<top>\<top>\<top>") where
  "\<top>\<top>\<top> \<equiv> \<lambda>_ _ _. True"

abbreviation(input)
  botbotbot :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" ("\<bottom>\<bottom>\<bottom>") where
  "\<bottom>\<bottom>\<bottom> \<equiv> \<lambda>_ _ _. False"

text \<open>
  Test whether the environment steps in @{text tr} satisfy the rely condition @{text R},
  assuming that @{text s0s} was the initial state before the first step in the trace.\<close>
definition rely_cond :: "'s rg_pred \<Rightarrow> 's \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> bool" where
  "rely_cond R s0s tr = (\<forall>(ident, s0, s) \<in> trace_steps (rev tr) s0s. ident = Env \<longrightarrow> R s0 s)"

text \<open>
  Test whether the self steps in @{text tr} satisfy the guarantee condition @{text G},
  assuming that @{text s0s} was the initial state before the first step in the trace.\<close>
definition guar_cond :: "'s rg_pred \<Rightarrow> 's \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> bool" where
  "guar_cond G s0s tr = (\<forall>(ident, s0, s) \<in> trace_steps (rev tr) s0s. ident = Me \<longrightarrow> G s0 s)"

lemma rg_empty_conds[simp]:
  "rely_cond R s0s []"
  "guar_cond G s0s []"
  by (simp_all add: rely_cond_def guar_cond_def)

text \<open>
  @{text "rely f R s0s"} constructs a new function from @{text f}, where the environment
  steps are constrained by @{text R} and @{text s0s} was the initial state before the first
  step in the trace.\<close>
definition rely :: "('s, 'a) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> 's \<Rightarrow> ('s, 'a) tmonad" where
  "rely f R s0s \<equiv> (\<lambda>s. f s \<inter> ({tr. rely_cond R s0s tr} \<times> UNIV))"

definition prefix_closed :: "('s, 'a) tmonad \<Rightarrow> bool" where
  "prefix_closed f = (\<forall>s. \<forall>x xs. (x # xs) \<in> fst ` f s \<longrightarrow> (xs, Incomplete) \<in> f s)"

definition validI ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's rg_pred \<Rightarrow> ('s,'a) tmonad \<Rightarrow> 's rg_pred \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)") where
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> \<equiv>
     prefix_closed f
     \<and> (\<forall>s0 s tr res. P s0 s \<and> (tr, res) \<in> (rely f R s0 s)
         \<longrightarrow> guar_cond G s0 tr
           \<and> (\<forall>rv s'. res = Result (rv, s') \<longrightarrow> Q rv (last_st_tr tr s0) s'))"

(*
text \<open>Validity for exception monad with interferences. Not as easy to phrase
 as we need to \<close>
definition validIE :: "('s, 'a + 'b) tmonad \<Rightarrow>
             's rg_pred \<Rightarrow>
             's rg_pred \<Rightarrow> 's rg_pred \<Rightarrow>
             ('b \<Rightarrow> 's rg_pred) \<Rightarrow>
             ('a \<Rightarrow> 's rg_pred) \<Rightarrow> bool"
 ("_ //PRE _//RELY _//GUAR _//POST _//EXC _" [59,0,0,0,0,0] 60) where
  "validIE f P R G Q E \<equiv> f SAT [P,R,G,\<lambda>v. case v of Inr r \<Rightarrow> Q r | Inl e \<Rightarrow> E e]"

abbreviation (input)
  validIEsat :: "('s, 'a + 'b) tmonad \<Rightarrow>
             's rg_pred \<Rightarrow>
             's rg_pred \<Rightarrow> 's rg_pred \<Rightarrow>
             ('b \<Rightarrow> 's rg_pred) \<Rightarrow>
             ('a \<Rightarrow> 's rg_pred) \<Rightarrow> bool"
  ("_ //SAT [_, _, _, _, _]" [59,0,0,0,0,0] 60)
  where
  "validIEsat f P R G Q E \<equiv> validIE f P R G Q E"
 *)

lemma in_rely:
  "\<lbrakk> (tr, res) \<in> f s; rely_cond R s0s tr \<rbrakk> \<Longrightarrow> (tr, res) \<in> rely f R s0s s"
  by (simp add: rely_def)

lemmas validI_D =
  validI_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, rule_format,
             OF _ conjI, OF _ _ in_rely]
lemmas validI_GD = validI_D[THEN conjunct1]
lemmas validI_rvD = validI_D[THEN conjunct2, rule_format, rotated -1, OF refl]
lemmas validI_prefix_closed = validI_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct1]
lemmas validI_prefix_closed_T =
  validI_prefix_closed[where P="\<lambda>_ _. False" and R="\<lambda>_ _. False" and G="\<lambda>_ _. True"
                         and Q="\<lambda>_ _ _. True"]

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


section \<open>Lemmas\<close>

lemma validI_weaken_pre:
  "\<lbrakk>\<lbrace>P'\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<And>s0 s. P s0 s \<Longrightarrow> P' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (simp add: validI_def, blast)

lemma rely_weaken:
  "\<lbrakk>\<forall>s0 s. R s0 s \<longrightarrow> R' s0 s; (tr, res) \<in> rely f R s s0\<rbrakk>
   \<Longrightarrow> (tr, res) \<in> rely f R' s s0"
  by (simp add: rely_def rely_cond_def, blast)

lemma validI_weaken_rely:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R'\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<forall>s0 s. R s0 s \<longrightarrow> R' s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: validI_def)
  by (metis rely_weaken)

lemmas validI_pre[wp_pre] =
  validI_weaken_pre
  validI_weaken_rely

lemma validI_strengthen_post:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace>; \<forall>v s0 s. Q' v s0 s \<longrightarrow> Q v s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (simp add: validI_def)

lemma validI_strengthen_guar:
  "\<lbrakk>\<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G'\<rbrace>, \<lbrace>Q\<rbrace>; \<forall>s0 s. G' s0 s \<longrightarrow> G s0 s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>, \<lbrace>Q\<rbrace>"
  by (force simp: validI_def guar_cond_def)


subsection \<open>Setting up the precondition case splitter.\<close>

(* FIXME: this needs adjustment, case_prod Q is unlikely to unify *)
lemma wpc_helper_validI:
  "(\<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>) \<Longrightarrow> wpc_helper (P, P', P'') (case_prod Q, Q', Q'') (\<lbrace>curry P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>)"
  by (clarsimp simp: wpc_helper_def elim!: validI_weaken_pre)

wpc_setup "\<lambda>m. \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> m \<lbrace>G\<rbrace>,\<lbrace>S\<rbrace>" wpc_helper_validI


subsection \<open>RG Logic Rules\<close>

lemma trace_steps_append:
  "trace_steps (xs @ ys) s
   = trace_steps xs s \<union> trace_steps ys (last_st_tr (rev xs) s)"
  by (induct xs arbitrary: s, simp_all add: last_st_tr_def hd_append)

lemma rely_cond_append:
  "rely_cond R s (xs @ ys) = (rely_cond R s ys \<and> rely_cond R (last_st_tr ys s) xs)"
  by (simp add: rely_cond_def trace_steps_append ball_Un conj_comms)

lemma guar_cond_append:
  "guar_cond G s (xs @ ys) = (guar_cond G s ys \<and> guar_cond G (last_st_tr ys s) xs)"
  by (simp add: guar_cond_def trace_steps_append ball_Un conj_comms)

lemma prefix_closed_bind:
  "\<lbrakk>prefix_closed f; \<forall>x. prefix_closed (g x)\<rbrakk> \<Longrightarrow> prefix_closed (f >>= g)"
  apply (subst prefix_closed_def, clarsimp simp: bind_def)
  apply (auto simp: Cons_eq_append_conv split: tmres.split_asm
             dest!: prefix_closedD[rotated];
         fastforce elim: rev_bexI)
  done

lemmas prefix_closed_bind[rule_format, wp_split]

lemma last_st_tr_append[simp]:
  "last_st_tr (tr @ tr') s = last_st_tr tr (last_st_tr tr' s)"
  by (simp add: last_st_tr_def hd_append)

lemma last_st_tr_Nil[simp]:
  "last_st_tr [] s = s"
  by (simp add: last_st_tr_def)

lemma last_st_tr_Cons[simp]:
  "last_st_tr (x # xs) s = snd x"
  by (simp add: last_st_tr_def)

lemma no_trace_last_st_tr:
  "\<lbrakk>no_trace f; (tr, res) \<in> f s\<rbrakk> \<Longrightarrow> last_st_tr tr s0 = s0"
  by (fastforce simp: no_trace_def)

lemma no_trace_rely_cond:
  "\<lbrakk>no_trace f; (tr, res) \<in> f s\<rbrakk> \<Longrightarrow> rely_cond R s0 tr"
  by (fastforce simp: no_trace_def rely_cond_def)

lemma bind_twp[wp_split]:
  "\<lbrakk> \<And>r. \<lbrace>Q' r\<rbrace>,\<lbrace>R\<rbrace> g r \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q'\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f >>= (\<lambda>r. g r) \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (subst validI_def, rule conjI)
   apply (blast intro: prefix_closed_bind validI_prefix_closed)
  apply (clarsimp simp: bind_def rely_def)
  apply (drule(2) validI_D)
   apply (clarsimp simp: rely_cond_append split: tmres.split_asm)
  apply (clarsimp split: tmres.split_asm)
  apply (drule meta_spec, frule(2) validI_D)
   apply (clarsimp simp: rely_cond_append split: if_split_asm)
  apply (clarsimp simp: guar_cond_append)
  done

lemma trace_steps_rev_drop_nth:
  "trace_steps (rev (drop n tr)) s
   = (\<lambda>i. (fst (rev tr ! i), (if i = 0 then s else snd (rev tr ! (i - 1))),
           snd (rev tr ! i))) ` {..< length tr - n}"
  apply (simp add: trace_steps_nth)
  apply (intro image_cong refl)
  apply (simp add: rev_nth)
  done

lemma prefix_closed_drop:
  "\<lbrakk>(tr, res) \<in> f s; prefix_closed f\<rbrakk> \<Longrightarrow> \<exists>res'. (drop n tr, res') \<in> f s"
proof (induct n arbitrary: res)
  case 0 then show ?case by auto
next
  case (Suc n)
  have drop_1: "\<And>tr res. (tr, res) \<in> f s \<Longrightarrow> \<exists>res'. (drop 1 tr, res') \<in> f s"
    by (case_tac tr; fastforce dest: prefix_closedD[rotated] intro: Suc)
  show ?case
    using Suc.hyps[OF Suc.prems]
    by (metis drop_1[simplified] drop_drop add_0 add_Suc)
qed

lemma validI_GD_drop:
  "\<lbrakk> \<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>, \<lbrace>Q\<rbrace>; P s0 s; (tr, res) \<in> f s;
     rely_cond R s0 (drop n tr) \<rbrakk>
   \<Longrightarrow> guar_cond G s0 (drop n tr)"
  apply (drule prefix_closed_drop[where n=n], erule validI_prefix_closed)
  apply (auto dest: validI_GD)
  done

lemma parallel_prefix_closed[wp_split]:
  "\<lbrakk>prefix_closed f; prefix_closed g\<rbrakk>
   \<Longrightarrow> prefix_closed (parallel f g)"
  apply (subst prefix_closed_def, clarsimp simp: parallel_def)
  apply (case_tac f_steps; clarsimp)
  apply (drule(1) prefix_closedD)+
  apply fastforce
  done

lemma rely_cond_drop:
  "rely_cond R s0 xs \<Longrightarrow> rely_cond R s0 (drop n xs)"
  using rely_cond_append[where xs="take n xs" and ys="drop n xs"]
  by simp

lemma rely_cond_is_drop:
  "\<lbrakk>rely_cond R s0 xs; (ys = drop (length xs - length ys) xs)\<rbrakk>
   \<Longrightarrow> rely_cond R s0 ys"
  by (metis rely_cond_drop)

lemma bounded_rev_nat_induct:
  "\<lbrakk>(\<And>n. N \<le> n \<Longrightarrow> P n); \<And>n. \<lbrakk>n < N; P (Suc n)\<rbrakk> \<Longrightarrow> P n\<rbrakk>
   \<Longrightarrow> P n"
  by (induct diff\<equiv>"N - n" arbitrary: n; simp)

lemma drop_n_induct:
  "\<lbrakk>P []; \<And>n. \<lbrakk>n < length xs; P (drop (Suc n) xs)\<rbrakk> \<Longrightarrow> P (drop n xs)\<rbrakk>
   \<Longrightarrow> P (drop n xs)"
  by (induct len\<equiv>"length (drop n xs)" arbitrary: n xs; simp)

lemma guar_cond_Cons_eq:
  "guar_cond R s0 (x # xs)
   = (guar_cond R s0 xs \<and> (fst x \<noteq> Env \<longrightarrow> R (last_st_tr xs s0) (snd x)))"
  by (cases "fst x"; simp add: guar_cond_def trace_steps_append conj_comms)

lemma guar_cond_Cons:
  "\<lbrakk>guar_cond R s0 xs; fst x \<noteq> Env \<longrightarrow> R (last_st_tr xs s0) (snd x)\<rbrakk>
   \<Longrightarrow> guar_cond R s0 (x # xs)"
  by (simp add: guar_cond_Cons_eq)

lemma guar_cond_drop_Suc_eq:
  "n < length xs
   \<Longrightarrow> guar_cond R s0 (drop n xs) = (guar_cond R s0 (drop (Suc n) xs)
       \<and> (fst (xs ! n) \<noteq> Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))))"
  apply (rule trans[OF _ guar_cond_Cons_eq])
  apply (simp add: Cons_nth_drop_Suc)
  done

lemma guar_cond_drop_Suc:
  "\<lbrakk>guar_cond R s0 (drop (Suc n) xs);
    fst (xs ! n) \<noteq> Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))\<rbrakk>
   \<Longrightarrow> guar_cond R s0 (drop n xs)"
  by (case_tac "n < length xs"; simp add: guar_cond_drop_Suc_eq)

lemma rely_cond_Cons_eq:
  "rely_cond R s0 (x # xs)
   = (rely_cond R s0 xs \<and> (fst x = Env \<longrightarrow> R (last_st_tr xs s0) (snd x)))"
  by (simp add: rely_cond_def trace_steps_append conj_comms)

lemma rely_cond_Cons:
  "\<lbrakk>rely_cond R s0 xs; fst x = Env \<longrightarrow> R (last_st_tr xs s0) (snd x)\<rbrakk>
   \<Longrightarrow> rely_cond R s0 (x # xs)"
  by (simp add: rely_cond_Cons_eq)

lemma rely_cond_drop_Suc_eq:
  "n < length xs
   \<Longrightarrow> rely_cond R s0 (drop n xs) = (rely_cond R s0 (drop (Suc n) xs)
       \<and> (fst (xs ! n) = Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))))"
  apply (rule trans[OF _ rely_cond_Cons_eq])
  apply (simp add: Cons_nth_drop_Suc)
  done

lemma rely_cond_drop_Suc:
  "\<lbrakk>rely_cond R s0 (drop (Suc n) xs);
    fst (xs ! n) = Env \<longrightarrow> R (last_st_tr (drop (Suc n) xs) s0) (snd (xs ! n))\<rbrakk>
   \<Longrightarrow> rely_cond R s0 (drop n xs)"
  by (cases "n < length xs"; simp add: rely_cond_drop_Suc_eq)

lemma last_st_tr_map_zip_hd:
  "\<lbrakk>length flags = length tr; tr \<noteq> [] \<longrightarrow> snd (f (hd flags, hd tr)) = snd (hd tr)\<rbrakk>
   \<Longrightarrow> last_st_tr (map f (zip flags tr)) = last_st_tr tr"
  apply (cases tr; simp)
  apply (cases flags; simp)
  apply (simp add: fun_eq_iff)
  done

lemma last_st_tr_drop_map_zip_hd:
  "\<lbrakk>length flags = length tr;
    n < length tr \<longrightarrow> snd (f (flags ! n, tr ! n)) = snd (tr ! n)\<rbrakk>
   \<Longrightarrow> last_st_tr (drop n (map f (zip flags tr))) = last_st_tr (drop n tr)"
  apply (simp add: drop_map drop_zip)
  apply (rule last_st_tr_map_zip_hd; clarsimp)
  apply (simp add: hd_drop_conv_nth)
  done

lemma last_st_tr_map_zip:
  "\<lbrakk>length flags = length tr; \<forall>fl tmid s. snd (f (fl, (tmid, s))) = s\<rbrakk>
   \<Longrightarrow> last_st_tr (map f (zip flags tr)) = last_st_tr tr"
  apply (erule last_st_tr_map_zip_hd)
  apply (clarsimp simp: neq_Nil_conv)
  done

lemma parallel_rely_induct:
  assumes preds: "(tr, v) \<in> parallel f g s" "Pf s0 s" "Pg s0 s"
  and validI: "\<lbrace>Pf\<rbrace>,\<lbrace>Rf\<rbrace> f' \<lbrace>Gf\<rbrace>,\<lbrace>Qf\<rbrace>"
     "\<lbrace>Pg\<rbrace>,\<lbrace>Rg\<rbrace> g' \<lbrace>Gg\<rbrace>,\<lbrace>Qg\<rbrace>"
     "f s \<subseteq> f' s" "g s \<subseteq> g' s"
  and compat: "R \<le> Rf" "R \<le> Rg" "Gf \<le> G" "Gg \<le> G" "Gf \<le> Rg" "Gg \<le> Rf"
  and rely: "rely_cond R s0 (drop n tr)"
  shows
    "\<exists>tr_f tr_g. (tr_f, v) \<in> f s \<and> (tr_g, v) \<in> g s
       \<and> rely_cond Rf s0 (drop n tr_f) \<and> rely_cond Rg s0 (drop n tr_g)
       \<and> map snd tr_f = map snd tr \<and> map snd tr_g = map snd tr
       \<and> (\<forall>i \<le> length tr. last_st_tr (drop i tr_g) s0 = last_st_tr (drop i tr_f) s0)
       \<and> guar_cond G s0 (drop n tr)"
  (is "\<exists>ys zs. _ \<and> _ \<and> ?concl ys zs")
proof -
  obtain ys zs where tr: "tr = map parallel_mrg (zip ys zs)"
    and all2: "list_all2 (\<lambda>y z. (fst y = Env \<or> fst z = Env) \<and> snd y = snd z) ys zs"
    and ys: "(ys, v) \<in> f s" and zs: "(zs, v) \<in> g s"
    using preds
    by (clarsimp simp: parallel_def2)
  note len[simp] = list_all2_lengthD[OF all2]

  have ys': "(ys, v) \<in> f' s" and zs': "(zs, v) \<in> g' s"
    using ys zs validI by auto

  note rely_f_step = validI_GD_drop[OF validI(1) preds(2) ys' rely_cond_drop_Suc]
  note rely_g_step = validI_GD_drop[OF validI(2) preds(3) zs' rely_cond_drop_Suc]

  note snd[simp] = list_all2_nthD[OF all2, THEN conjunct2]

  have "?concl ys zs"
    using rely tr all2 rely_f_step rely_g_step
    apply (induct n rule: bounded_rev_nat_induct)
     apply (subst drop_all, assumption)
     apply clarsimp
     apply (simp add: list_all2_conv_all_nth last_st_tr_def drop_map[symmetric]
                      hd_drop_conv_nth hd_append)
     apply (fastforce simp: split_def intro!: nth_equalityI)
    apply clarsimp
    apply (erule_tac x=n in meta_allE)+
    apply (drule meta_mp, erule rely_cond_is_drop, simp)
    apply (subst(asm) rely_cond_drop_Suc_eq[where xs="map f xs" for f xs], simp)
    apply (clarsimp simp: last_st_tr_drop_map_zip_hd if_split[where P="\<lambda>x. x = Env"]
                          split_def)
    apply (intro conjI; (rule guar_cond_drop_Suc rely_cond_drop_Suc, assumption))
      apply (auto simp: guar_cond_drop_Suc_eq last_st_tr_drop_map_zip_hd
                 intro: compat[THEN predicate2D])
    done

  thus ?thesis
    using ys zs
    by auto
qed

lemmas parallel_rely_induct0 = parallel_rely_induct[where n=0, simplified]

lemma rg_validI:
  assumes validI: "\<lbrace>Pf\<rbrace>,\<lbrace>Rf\<rbrace> f \<lbrace>Gf\<rbrace>,\<lbrace>Qf\<rbrace>"
     "\<lbrace>Pg\<rbrace>,\<lbrace>Rg\<rbrace> g \<lbrace>Gg\<rbrace>,\<lbrace>Qg\<rbrace>"
  and compat: "R \<le> Rf" "R \<le> Rg" "Gf \<le> G" "Gg \<le> G" "Gf \<le> Rg" "Gg \<le> Rf"
  shows "\<lbrace>Pf and Pg\<rbrace>,\<lbrace>R\<rbrace> parallel f g \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv. Qf rv and Qg rv\<rbrace>"
  apply (clarsimp simp: validI_def rely_def pred_conj_def
                        parallel_prefix_closed validI[THEN validI_prefix_closed])
  apply (drule(3) parallel_rely_induct0[OF _ _ _ validI order_refl order_refl compat])
  apply clarsimp
  apply (drule(2) validI[THEN validI_rvD])+
  apply (simp add: last_st_tr_def)
  done

lemma rely_prim[simp]:
  "rely (\<lambda>s. insert (v s) (f s)) R s0 = (\<lambda>s. {x. x = v s \<and> rely_cond R s0 (fst x)} \<union> (rely f R s0 s))"
  "rely (\<lambda>s. {}) R s0 = (\<lambda>_. {})"
  by (auto simp: rely_def prod_eq_iff)

lemma prefix_closed_put_trace_elem[iff]:
  "prefix_closed (put_trace_elem x)"
  by (clarsimp simp: prefix_closed_def put_trace_elem_def)

lemma prefix_closed_return[iff]:
  "prefix_closed (return x)"
  by (simp add: prefix_closed_def return_def)

lemma prefix_closed_put_trace[iff]:
  "prefix_closed (put_trace tr)"
  by (induct tr; clarsimp simp: prefix_closed_bind)

lemma put_trace_eq_drop:
  "put_trace xs s
   = ((\<lambda>n. (drop n xs, if n = 0 then Result ((), s) else Incomplete)) ` {.. length xs})"
  apply (induct xs)
   apply (clarsimp simp: return_def)
  apply (clarsimp simp: put_trace_elem_def bind_def)
  apply (simp add: atMost_Suc_eq_insert_0 image_image)
  apply (rule equalityI; clarsimp)
   apply (split if_split_asm; clarsimp)
   apply (auto intro: image_eqI[where x=0])[1]
  apply (rule rev_bexI, simp)
  apply clarsimp
  done

lemma put_trace_res:
  "(tr, res) \<in> put_trace xs s
   \<Longrightarrow> \<exists>n. tr = drop n xs \<and> n \<le> length xs
         \<and> res = (case n of 0 \<Rightarrow> Result ((), s) | _ \<Rightarrow> Incomplete)"
  apply (clarsimp simp: put_trace_eq_drop)
  apply (case_tac n; auto intro: exI[where x=0])
  done

lemma put_trace_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>n. rely_cond R s0 (drop n xs) \<longrightarrow> guar_cond G s0 (drop n xs))
     \<and> (rely_cond R s0 xs \<longrightarrow> Q () (last_st_tr xs s0) s)\<rbrace>,\<lbrace>R\<rbrace>
   put_trace xs
   \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (clarsimp simp: validI_def rely_def)
  apply (drule put_trace_res)
  apply (clarsimp; clarsimp split: nat.split_asm)
  done

lemmas put_trace_elem_twp = put_trace_twp[where xs="[x]" for x, simplified]

lemma prefix_closed_select[iff]:
  "prefix_closed (select S)"
  by (simp add: prefix_closed_def select_def image_def)

lemma rely_cond_rtranclp:
  "rely_cond R s (map (Pair Env) xs) \<Longrightarrow> rtranclp R s (last_st_tr (map (Pair Env) xs) s)"
  apply (induct xs arbitrary: s rule: rev_induct)
   apply simp
  apply (clarsimp simp add: rely_cond_def)
  apply (erule converse_rtranclp_into_rtranclp)
  apply simp
  done


subsection \<open>Setting up the @{method wp} method\<close>

(* Attempt to define triple_judgement to use valid_validI_wp as wp_comb rule.
   It doesn't work. It seems that wp_comb rules cannot take more than 1 assumption *)
lemma validI_is_triple[wp_trip]:
  "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>
   = triple_judgement (\<lambda>(s0, s). prefix_closed f \<longrightarrow> P s0 s) f
                      (\<lambda>(s0,s) f. prefix_closed f \<and> (\<forall>tr res. (tr, res) \<in> rely f R s0 s
                          \<longrightarrow> guar_cond G s0 tr
                              \<and> (\<forall>rv s'. res = Result (rv, s') \<longrightarrow> Q rv (last_st_tr tr s0) s')))"
  apply (simp add: triple_judgement_def validI_def )
  apply (cases "prefix_closed f"; fastforce)
  done

lemma no_trace_prefix_closed:
  "no_trace f \<Longrightarrow> prefix_closed f"
  by (auto simp add: prefix_closed_def dest: no_trace_emp)

lemma validI_valid_no_trace_eq:
  "no_trace f \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace> = (\<forall>s0. \<lbrace>P s0\<rbrace> f \<lbrace>\<lambda>v. Q v s0\<rbrace>)"
  apply (rule iffI)
   apply (fastforce simp: rely_def validI_def valid_def mres_def
                    dest: no_trace_emp)
  apply (clarsimp simp: rely_def validI_def valid_def mres_def no_trace_prefix_closed)
  apply (fastforce simp: eq_snd_iff dest: no_trace_emp)
  done

lemma valid_validI_wp[wp_comb]:
  "\<lbrakk>no_trace f; \<And>s0. \<lbrace>P s0\<rbrace> f \<lbrace>\<lambda>v. Q v s0 \<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  by (clarsimp simp: validI_valid_no_trace_eq)


lemma env_steps_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>s'. R\<^sup>*\<^sup>* s0 s' \<longrightarrow> Q () s' s') \<and> Q () s0 s\<rbrace>,\<lbrace>R\<rbrace> env_steps \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: interference_def env_steps_def)
  apply wp
  apply (clarsimp simp: guar_cond_def trace_steps_rev_drop_nth rev_nth)
  apply (drule rely_cond_rtranclp)
  apply (clarsimp simp add: last_st_tr_def hd_append)
  done

lemma interference_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>s'. R\<^sup>*\<^sup>* s s' \<longrightarrow> Q () s' s') \<and> G s0 s\<rbrace>,\<lbrace>R\<rbrace> interference \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: interference_def commit_step_def del: put_trace.simps)
  apply wp
  apply clarsimp
  apply (simp add: drop_Cons nat.split rely_cond_def guar_cond_def)
  done

(* what Await does if we haven't committed our step is a little
   strange. this assumes we have, which means s0 = s. we should
   revisit this if we find a use for Await when this isn't the
   case *)
lemma Await_sync_twp:
  "\<lbrace>\<lambda>s0 s. s = s0 \<and> (\<forall>x. R\<^sup>*\<^sup>* s0 x \<and> c x \<longrightarrow> Q () x x)\<rbrace>,\<lbrace>R\<rbrace> Await c \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: Await_def split_def)
  apply wp
  apply clarsimp
  apply (clarsimp simp: guar_cond_def trace_steps_rev_drop_nth rev_nth)
  apply (drule rely_cond_rtranclp)
  apply (simp add: o_def)
  done

lemma mres_union:
  "mres (a \<union> b) = mres a \<union> mres b"
  by (simp add: mres_def image_Un)

lemma mres_Failed_empty:
  "mres ((\<lambda>xs. (xs, Failed)) ` X ) = {}"
  "mres ((\<lambda>xs. (xs, Incomplete)) ` X ) = {}"
  by (auto simp add: mres_def image_def)

lemma det_set_option_eq:
  "(\<Union>a\<in>m. set_option (snd a)) = {(r, s')} \<Longrightarrow>
       (ts, Some (rr, ss)) \<in> m \<Longrightarrow> rr = r \<and> ss = s'"
  by (metis UN_I option.set_intros prod.inject singleton_iff snd_conv)

lemma det_set_option_eq':
  "(\<Union>a\<in>m. set_option (snd a)) = {(r, s')} \<Longrightarrow>
       Some (r, s') \<in> snd ` m"
  using image_iff by fastforce

lemma validI_name_pre:
  "prefix_closed f \<Longrightarrow>
  (\<And>s0 s. P s0 s \<Longrightarrow> \<lbrace>\<lambda>s0' s'. s0' = s0 \<and> s' = s\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>)
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  unfolding validI_def
  by metis

lemma validI_well_behaved':
  "\<lbrakk>prefix_closed f; \<lbrace>P\<rbrace>,\<lbrace>R'\<rbrace> f \<lbrace>G'\<rbrace>,\<lbrace>Q\<rbrace>; R \<le> R'; G' \<le> G\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (subst validI_def, clarsimp)
  apply (clarsimp simp add: rely_def)
  apply (drule (2)  validI_D)
   apply (fastforce simp: rely_cond_def guar_cond_def)+
  done

lemmas validI_well_behaved = validI_well_behaved'[unfolded le_fun_def, simplified]

lemma prefix_closed_mapM[rule_format, wp_split]:
  "(\<forall>x \<in> set xs. prefix_closed (f x)) \<Longrightarrow> prefix_closed (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def)
  apply (clarsimp simp: mapM_Cons)
  apply (intro prefix_closed_bind allI; clarsimp)
  done

lemmas bind_promote_If =
  if_distrib[where f="\<lambda>f. bind f g" for g]
  if_distrib[where f="\<lambda>g. bind f g" for f]

lemma bind_promote_If2:
  "do x \<leftarrow> f; if P then g x else h x od
   = (if P then bind f g else bind f h)"
  by simp

lemma exec_put_trace[unfolded K_bind_def]:
  "(do put_trace xs; f od) s
   = (\<Union>n \<in> {n. 0 < n \<and> n \<le> length xs}. {(drop n xs, Incomplete)})
     \<union> ((\<lambda>(a, b). (a @ xs, b)) ` f s)"
  apply (simp add: put_trace_eq_drop bind_def)
  apply (safe; (clarsimp split: if_split_asm)?;
         fastforce intro: bexI[where x=0] rev_bexI)
  done

lemma UN_If_distrib:
  "(\<Union>x \<in> S. if P x then A x else B x)
   = ((\<Union>x \<in> S \<inter> {x. P x}. A x) \<union> (\<Union>x \<in> S \<inter> {x. \<not> P x}. B x))"
  by (fastforce split: if_split_asm)

lemma Await_redef:
  "Await P = do
     s1 \<leftarrow> select {s. P s};
     env_steps;
     s \<leftarrow> get;
     select (if P s then {()} else {})
   od"
  apply (simp add: Await_def env_steps_def bind_assoc)
  apply (cases "{s. P s} = {}")
   apply (simp add: select_def bind_def get_def)
  apply (rule ext)
  apply (simp add: exec_get select_bind_UN put_then_get_then)
  apply (simp add: bind_promote_If2 if_distribR if_distrib[where f=select])
  apply (simp add: exec_put_trace cong: if_cong)
  apply (simp add: put_def bind_def select_def cong: if_cong)
  apply (strengthen equalityI)
  apply clarsimp
  apply (strengthen exI[where x="s # xs" for s xs])
  apply (strengthen exI[where x="Suc n" for n])
  apply simp
  apply blast
  done

lemma eq_Me_neq_Env:
  "(x = Me) = (x \<noteq> Env)"
  by (cases x; simp)

lemma validI_invariant_imp:
  assumes v: "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
    and P: "\<forall>s0 s. P s0 s \<longrightarrow> I s0"
    and R: "\<forall>s0 s. I s0 \<longrightarrow> R s0 s \<longrightarrow> I s"
    and G: "\<forall>s0 s. I s0 \<longrightarrow> G s0 s \<longrightarrow> I s"
  shows "\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>s0 s. I s0 \<and> I s \<and> G s0 s\<rbrace>,\<lbrace>\<lambda>rv s0 s. I s0 \<and> Q rv s0 s\<rbrace>"
proof -
  { fix tr s0 i
    assume r: "rely_cond R s0 tr" and g: "guar_cond G s0 tr"
      and I: "I s0"
    hence imp: "\<forall>(_, s, s') \<in> trace_steps (rev tr) s0. I s \<longrightarrow> I s'"
      apply (clarsimp simp: guar_cond_def rely_cond_def)
      apply (drule(1) bspec)+
      apply (clarsimp simp: eq_Me_neq_Env)
      apply (metis R G)
      done
    hence "i < length tr \<longrightarrow> I (snd (rev tr ! i))"
      using I
      apply (induct i)
       apply (clarsimp simp: neq_Nil_conv[where xs="rev tr" for tr, simplified])
      apply clarsimp
      apply (drule bspec, fastforce simp add: trace_steps_nth)
      apply simp
      done
  }
  note I = this
  show ?thesis
    using v
    apply (clarsimp simp: validI_def rely_def imp_conjL)
    apply (drule spec2, drule(1) mp)+
    apply clarsimp
    apply (frule P[rule_format])
    apply (clarsimp simp: guar_cond_def trace_steps_nth I last_st_tr_def
                          hd_append last_rev[symmetric]
                          last_conv_nth rev_map)
    done
qed

lemma validI_guar_post_conj_lift:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G1\<rbrace>,\<lbrace>Q1\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G2\<rbrace>,\<lbrace>Q2\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>s0 s. G1 s0 s \<and> G2 s0 s\<rbrace>,\<lbrace>\<lambda>rv s0 s. Q1 rv s0 s \<and> Q2 rv s0 s\<rbrace>"
  apply (frule validI_prefix_closed)
  apply (subst validI_def, clarsimp simp: rely_def)
  apply (drule(3) validI_D)+
  apply (auto simp: guar_cond_def)
  done

lemmas modify_prefix_closed[simp] =
  modify_wp[THEN valid_validI_wp[OF no_trace_all(3)], THEN validI_prefix_closed]
lemmas await_prefix_closed[simp] = Await_sync_twp[THEN validI_prefix_closed]

lemma repeat_prefix_closed[intro!]:
  "prefix_closed f \<Longrightarrow> prefix_closed (repeat f)"
  apply (simp add: repeat_def)
  apply (rule prefix_closed_bind; clarsimp)
  apply (rename_tac n)
  apply (induct_tac n; simp)
  apply (auto intro: prefix_closed_bind)
  done

lemma rely_cond_True[simp]:
  "rely_cond \<top>\<top> s0 tr = True"
  by (clarsimp simp: rely_cond_def)

lemma guar_cond_True[simp]:
  "guar_cond \<top>\<top> s0 tr = True"
  by (clarsimp simp: guar_cond_def)

lemma validI_valid_wp:
  "\<lbrakk>\<lbrace>P\<rbrace>,\<lbrace>\<top>\<top>\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>rv _ s. Q rv s\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P s0\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto simp: rely_def validI_def valid_def mres_def)

lemma validI_triv_valid_eq:
  "prefix_closed f \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>\<top>\<top>\<rbrace> f \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>\<lambda>rv _ s. Q rv s\<rbrace> = (\<forall>s0. \<lbrace>\<lambda>s. P s0 s\<rbrace> f \<lbrace>Q\<rbrace>)"
  by (fastforce simp: rely_def validI_def valid_def mres_def image_def)

end