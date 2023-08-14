(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory Atomicity_Lib

imports
  Prefix_Refinement
  Monads.Trace_Det
begin

text \<open>This library introduces a number of proofs about the question of
atomicity refinement, particularly in combination with the existing
prefix refinement notion. It introduces an additional notion of refinement
which left-composes with prefix refinement and can be used to rearrange
operations around interference points.
\<close>

abbreviation
  "interferences \<equiv> repeat interference"

lemma triv_refinement_Await_env_steps:
  "triv_refinement env_steps (Await P)"
  apply (simp add: Await_def env_steps_def)
  apply (rule triv_refinement_mono_bind allI triv_refinement_select)+
  apply simp
  done

lemmas prefix_refinement_env_steps_Await
    = prefix_refinement_triv_refinement_conc[OF
        prefix_refinement_env_steps triv_refinement_Await_env_steps]

lemma pfx_refn_interferences:
  " env_stable AR R sr iosr (\<lambda>t. True)
    \<Longrightarrow> prefix_refinement sr iosr iosr (\<top>\<top>) (\<top>\<top>) (\<top>\<top>) AR R interferences interferences"
  apply (rule prefix_refinement_repeat)
    apply (erule prefix_refinement_interference)
   apply wp
   apply simp
  apply wp
  apply simp
  done

lemma repeat_n_validI:
  "\<lbrace>I\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. I\<rbrace>
    \<Longrightarrow> \<lbrace>I\<rbrace>,\<lbrace>R\<rbrace> repeat_n n f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. I\<rbrace>"
  apply (induct n)
   apply wpsimp+
  done

lemma repeat_validI:
  "\<lbrace>I\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. I\<rbrace>
    \<Longrightarrow> \<lbrace>I\<rbrace>,\<lbrace>R\<rbrace> repeat f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_. I\<rbrace>"
  apply (simp add: repeat_def)
  apply (wpsimp wp: repeat_n_validI)
  done

lemma interferences_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>s'. R\<^sup>*\<^sup>* s s' \<longrightarrow> Q () s' s') \<and> G s0 s \<and> reflp G \<and> Q () s0 s\<rbrace>,\<lbrace>R\<rbrace> interferences \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  (is "\<lbrace>?P\<rbrace>,\<lbrace>R\<rbrace> ?f \<lbrace>G\<rbrace>,\<lbrace>?Q\<rbrace>")
  apply (rule validI_strengthen_post, rule repeat_validI)
   apply wp
   apply (clarsimp simp: reflpD[where R=G])
   apply (metis rtranclp_trans)
  apply simp
  done

lemma repeat_pre_triv_refinement[simplified]:
  "triv_refinement (repeat f) (do f; repeat f od)"
  apply (simp add: repeat_def select_early)
  apply (rule triv_refinement_select_concrete_All; clarsimp)
  apply (rule_tac x="Suc x" in triv_refinement_select_abstract_x; simp)
  apply (rule triv_refinement_refl)
  done

lemma repeat_none_triv_refinement:
  "triv_refinement (repeat f) (return ())"
  apply (simp add: repeat_def)
  apply (rule_tac x="0" in triv_refinement_select_abstract_x; simp)
  apply (rule triv_refinement_refl)
  done

lemmas repeat_triv_refinement_consume_1
    = triv_refinement_trans[OF triv_refinement_mono_bind(1),
        OF repeat_pre_triv_refinement, simplified bind_assoc,
        OF triv_refinement_mono_bind(2), simplified]

lemmas repeat_one_triv_refinement
    = repeat_triv_refinement_consume_1[where b=return and d=return,
        simplified, OF repeat_none_triv_refinement]

schematic_goal prefix_refinement_interferences_split:
  "prefix_refinement sr isr osr rvr P Q AR R ?aprog cprog
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q AR R
                          (do y <- interferences; aprog od) cprog"
  apply (rule prefix_refinement_triv_refinement_abs)
   apply (rule  triv_refinement_mono_bind)
   apply (rule triv_refinement_trans)
    apply (rule repeat_pre_triv_refinement)
   apply (rule triv_refinement_mono_bind[rule_format], rule repeat_one_triv_refinement)
  apply (simp add: bind_assoc)
  done

text \<open>Suppressing interference points. The constant below discards
the self actions within a trace and filters out traces in which the
environment acts. This reduces both env_steps and interference to
noops.
\<close>

definition
  detrace :: "('s, 'a) tmonad \<Rightarrow> ('s, 'a) tmonad"
where
  "detrace f = (\<lambda>s. (\<lambda>(tr, res). ([], res))
     ` (f s \<inter> ({tr. Env \<notin> fst ` set tr} \<times> {res. res \<noteq> Incomplete})))"

lemma detrace_UN:
  "detrace (\<lambda>s. \<Union>x \<in> S s. f x s)
    = (\<lambda>s. \<Union>x \<in> S s. detrace (f x) s)"
  apply (simp add: detrace_def)
  apply (rule ext; fastforce)
  done

lemma detrace_bind:
  "detrace (f >>= (\<lambda>x. g x)) = (detrace f >>= (\<lambda>x. detrace (g x)))"
  apply (simp add: bind_def)
  apply (simp add: detrace_UN)
  apply (simp add: bind_def detrace_def image_UN)
  apply (rule ext, safe)
   apply (rule UN_I, erule IntI)
    apply (clarsimp split: tmres.split_asm)
   apply (clarsimp split: tmres.split_asm)
   apply fastforce
  apply (erule UN_I)
  apply (clarsimp split: tmres.split_asm)
  apply fastforce
  done

lemma det_detrace_eq:
  "det f \<Longrightarrow> detrace f = f"
  apply (clarsimp simp: det_def detrace_def)
  apply (rule ext, drule_tac x=s in spec)
  apply clarsimp
  done

lemmas detrace_return = return_det[THEN det_detrace_eq, simp]
lemmas detrace_get = get_det[THEN det_detrace_eq, simp]
lemmas detrace_gets = det_gets[THEN det_detrace_eq, simp]
lemmas detrace_put = put_det[THEN det_detrace_eq, simp]
lemmas detrace_modify = det_modify[THEN det_detrace_eq, simp]

lemma detrace_select[simp]:
  "detrace (select S) = select S"
  by (rule ext, auto simp add: select_def detrace_def image_image)

lemma detrace_put_trace_elem:
  "detrace (put_trace_elem (tmid, s)) = (if tmid = Env
    then (\<lambda>_. {}) else return ())"
  by (simp add: put_trace_elem_def detrace_def return_def)

lemma detrace_put_trace:
  "detrace (put_trace xs) = (if Env \<in> fst ` set xs
    then (\<lambda>_. {}) else return ())"
  apply (induct xs; simp)
  apply (clarsimp simp: detrace_bind detrace_put_trace_elem)
  apply (simp add: bind_def)
  done

lemma detrace_repeat_n:
  "detrace (repeat_n n f) = repeat_n n (detrace f)"
  by (induct n; simp add: detrace_bind)

lemma detrace_repeat:
  "detrace (repeat f) = repeat (detrace f)"
  by (simp add: repeat_def detrace_repeat_n detrace_bind)

lemma detrace_env_step:
  "detrace env_step = (\<lambda>_. {})"
  apply (simp add: env_step_def detrace_bind detrace_put_trace_elem)
  apply (simp add: bind_def select_def)
  done

lemma repeat_n_nothing:
  "repeat_n n (\<lambda>_. {}) = (if n = 0 then return () else (\<lambda>_. {}))"
  by (induct n; simp add: bind_def)

lemma repeat_nothing:
  "repeat (\<lambda>_. {}) = return ()"
  by (simp add: repeat_def bind_def select_def repeat_n_nothing
                Sigma_def if_distribR UN_If_distrib return_def
           cong del: image_cong_simp)

lemma detrace_env_steps:
  "detrace env_steps = return ()"
  by (simp add: env_steps_repeat detrace_repeat detrace_env_step repeat_nothing)

lemma detrace_interference:
  "detrace interference = return ()"
  apply (simp add: interference_def detrace_bind commit_step_def
                   detrace_env_steps detrace_put_trace_elem)
  apply (simp add: bind_def get_def)
  done

text \<open>Decomposition of environment and program actions by strict
separation, possibly relevant for ``recovering'' atomicity.\<close>

lemma equivp_compare_f:
  "equivp (\<lambda>x y. f x = f y)"
  by (simp add: equivp_def fun_eq_iff, metis)

definition
  fst_split_eq :: "('s \<Rightarrow> ('e \<times> 'p)) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool)"
where
  "fst_split_eq f = (\<lambda>s s'. fst (f s) = fst (f s'))"

definition
  snd_split_eq :: "('s \<Rightarrow> ('e \<times> 'p)) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool)"
where
  "snd_split_eq f = (\<lambda>s s'. snd (f s) = snd (f s'))"

lemma equivp_split_eqs:
  "equivp (fst_split_eq f)"
  "equivp (snd_split_eq f)"
  by (simp_all add: fst_split_eq_def snd_split_eq_def equivp_compare_f)

text \<open>One way of defining the "diamond" pattern in which two state
changes commute. Depends on a way of splitting the state into domains,
in which state changes can be observed to impact only certain domains.
This can define a unique way of reordering operations that impact
disjoint sets of domains.\<close>

type_synonym
  ('s, 'd) domain_split = "'s \<Rightarrow> 'd \<Rightarrow> 's"

definition
  dom_s_match :: "('s, 'd) domain_split \<Rightarrow> 'd set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
where
  "dom_s_match ds D s s' = (\<forall>d \<in> D. ds s' d = ds s d)"

lemma dom_s_match_refl:
  "dom_s_match ds D s s"
  by (simp add: dom_s_match_def)

lemma dom_s_match_equivp:
  "equivp (dom_s_match ds D)"
  apply (intro equivpI reflpI dom_s_match_refl)
   apply (rule sympI, simp add: dom_s_match_def)
  apply (rule transpI, simp add: dom_s_match_def)
  done

lemma dom_s_match_mono:
  "dom_s_match ds D s s' \<Longrightarrow> D' \<subseteq> D
    \<Longrightarrow> dom_s_match ds D' s s'"
  by (auto simp add: dom_s_match_def)

definition
  diamond :: "('s, 'd) domain_split \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
where
  "diamond ds s sa sb sab = (\<forall>d. (ds sab d = ds sa d \<and> ds sb d = ds s d)
        \<or> (ds sab d = ds sb d \<and> ds sa d = ds s d))"

lemma diamond_flips:
  "diamond ds s sa sb sab \<Longrightarrow> diamond ds sb sab s sa"
  "diamond ds s sa sb sab \<Longrightarrow> diamond ds sa s sab sb"
  by (auto simp add: diamond_def, metis+)

lemma diamond_diag_flip:
  "diamond ds s sa sb sab \<Longrightarrow> diamond ds s sb sa sab"
  by (simp add: diamond_def, metis)

definition
  domains_complete :: "('s, 'd) domain_split \<Rightarrow> bool"
where
  "domains_complete ds = (\<forall>s s'. (\<forall>d. ds s d = ds s' d) \<longrightarrow> s = s')"

lemmas domains_completeD = domains_complete_def[THEN iffD1, rule_format]

lemma diamond_unique:
  "domains_complete ds \<Longrightarrow> diamond ds s sa sb sab
    \<Longrightarrow> diamond ds s sa sb sab' \<Longrightarrow> sab = sab'"
  apply (erule domains_completeD)
  apply (simp add: diamond_def)
  apply metis
  done

lemma diamond_uniques_other:
  "domains_complete ds \<Longrightarrow> diamond ds s sa sb sab
    \<Longrightarrow> diamond ds s sa sb' sab \<Longrightarrow> sb = sb'"
  "domains_complete ds \<Longrightarrow> diamond ds s sa sb sab
    \<Longrightarrow> diamond ds s sa' sb sab \<Longrightarrow> sa = sa'"
  "domains_complete ds \<Longrightarrow> diamond ds s sa sb sab
    \<Longrightarrow> diamond ds s' sa sb sab \<Longrightarrow> s = s'"
  by (metis diamond_unique diamond_flips)+

lemmas diamond_uniques = diamond_unique diamond_uniques_other

lemma dom_s_match_diamond:
  "dom_s_match ds D s sa \<Longrightarrow> diamond ds s sa sb sab
    \<Longrightarrow> dom_s_match ds D sb sab"
  apply (simp add: dom_s_match_def diamond_def)
  apply metis
  done

lemma diamond_trans:
  "diamond ds s sa sb sab \<Longrightarrow> diamond ds sb sab sc sac \<Longrightarrow> diamond ds s sa sc sac"
  by (simp add: diamond_def, metis)

lemma diamond_trans_eq:
  "diamond ds s sa sb sab \<Longrightarrow> (diamond ds sb sab = diamond ds s sa)"
  by (simp add: fun_eq_iff, metis diamond_trans diamond_flips)

text \<open>
A notion of refinement by traces related under a state relation. Simpler
than @{term prefix_refinement}, and left-composes with
@{term prefix_refinement}.

We'll use this notion to show how the concrete side of a @{term prefix_refinement}
hypothesis can be reordered to better match its specification, in particular
how interference points can be moved.
\<close>

definition
  rel_tr_refinement :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 's rg_pred
    \<Rightarrow> bool \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> ('s, 'a) tmonad \<Rightarrow>  bool"
where
  "rel_tr_refinement sr P R commit f g = (\<forall>tr res s s0. P s
    \<longrightarrow> (tr, res) \<in> f s \<longrightarrow> rely_cond R s0 tr \<longrightarrow> (commit \<longrightarrow> s0 = s)
    \<longrightarrow> (\<exists>tr'. (tr', res) \<in> g s \<and> rely_cond R s0 tr'
                \<and> list_all2 (rel_prod (=) sr) tr tr'))"

lemma rely_cond_equiv_s:
  "rely_cond R s0 tr
    \<Longrightarrow> (\<And>s. tr \<noteq> [] \<Longrightarrow> last tr = (Env, s) \<Longrightarrow> R s0 s \<Longrightarrow> R s0' s)
    \<Longrightarrow> rely_cond R s0' tr"
  apply (cases tr rule: rev_cases)
   apply simp
  apply (clarsimp simp: rely_cond_append rely_cond_def[where tr="Cons x xs" for x xs])
  done

lemmas rel_tr_refinementD = rel_tr_refinement_def[THEN iffD1, rule_format]

lemma rel_tr_refinement_refl:
  "reflp sr
    \<Longrightarrow> rel_tr_refinement sr P R C f f"
  apply (clarsimp simp: rel_tr_refinement_def)
  apply (intro exI, rule conjI, assumption)
  apply (simp add: list_all2_same rel_prod_sel reflpD)
  done

lemma rel_tr_refinement_drop_C:
  "rel_tr_refinement sr P R False f g
    \<Longrightarrow> rel_tr_refinement sr P R C f g"
  by (clarsimp simp: rel_tr_refinement_def)

lemma rel_tr_refinement_trans:
  "transp sr
    \<Longrightarrow> rel_tr_refinement sr P R C f g
    \<Longrightarrow> rel_tr_refinement sr P R C g h
    \<Longrightarrow> rel_tr_refinement sr P R C f h"
  apply (subst rel_tr_refinement_def, clarsimp)
  apply (drule(3) rel_tr_refinementD, clarsimp+)
  apply (drule(3) rel_tr_refinementD, clarsimp+)
  apply (intro exI, rule conjI, assumption, clarsimp)
  apply (erule(1) list_all2_trans[rotated])
  apply clarsimp
  apply (metis transpD)
  done

lemma list_all2_matching_tr_pfx:
  "list_all2 (rel_prod (=) (\<lambda>cs cs'. \<forall>as. sr as cs = sr as cs')) tr tr'
    \<Longrightarrow> matching_tr_pfx sr atr tr = matching_tr_pfx sr atr tr'"
  apply (simp add: matching_tr_pfx_def list_all2_lengthD matching_tr_def)
  apply (intro conj_cong; simp?)
  apply (clarsimp simp: list_all2_conv_all_nth rel_prod_sel split_def)
  apply (simp add: rev_nth)
  done

lemma is_matching_fragment_list_all2:
  "is_matching_fragment sr osr rvr tr' res s0 R s f
    \<Longrightarrow> list_all2 (rel_prod (=) (\<lambda>cs cs'. \<forall>as. sr as cs = sr as cs')) tr tr'
    \<Longrightarrow> is_matching_fragment sr osr rvr tr res s0 R s f"
  apply (clarsimp simp: is_matching_fragment_def)
  apply (subst(asm) list_all2_is_me[symmetric], assumption, simp)
  apply (simp add: list_all2_matching_tr_pfx list_all2_lengthD)
  done

lemma pfx_refinement_use_rel_tr_refinement:
  "rel_tr_refinement tr_r Q R False g g'
    \<Longrightarrow> \<forall>s t t'. tr_r t t' \<longrightarrow> sr s t = sr s t'
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q' AR R f g'
    \<Longrightarrow> prefix_refinement sr isr osr rvr P (\<lambda>s0. Q and Q' s0) AR R f g"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule(3) rel_tr_refinementD, simp)
  apply clarsimp
  apply (drule(5) prefix_refinementD)
  apply clarsimp
  apply (rule exI, rule conjI[rotated], assumption)
  apply (erule is_matching_fragment_list_all2)
  apply (erule list_all2_mono)
  apply clarsimp
  done

lemma pfx_refinement_use_rel_tr_refinement_equivp:
  "rel_tr_refinement sr Q R False g g'
    \<Longrightarrow> equivp sr
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q' AR R f g'
    \<Longrightarrow> prefix_refinement sr isr osr rvr P (\<lambda>s0. Q and Q' s0) AR R f g"
  apply (erule pfx_refinement_use_rel_tr_refinement, simp_all)
  apply (metis equivpE sympD transpD)
  done

definition
  not_env_steps_first :: "('s, 'a) tmonad \<Rightarrow> bool"
where
  "not_env_steps_first f = (\<forall>tr res s. (tr, res) \<in> f s \<longrightarrow> tr \<noteq> [] \<longrightarrow> fst (last tr) = Me)"

lemmas not_env_steps_firstD = not_env_steps_first_def[THEN iffD1, rule_format]

lemma not_env_steps_first_bind:
  "not_env_steps_first f
    \<Longrightarrow> \<forall>x. not_env_steps_first (g x)
    \<Longrightarrow> not_env_steps_first (do x \<leftarrow> f; g x od)"
  apply (subst not_env_steps_first_def, clarsimp)
  apply (erule elem_bindE)
   apply (simp add: not_env_steps_firstD)
  apply (clarsimp simp: last_append)
  apply (auto elim: not_env_steps_firstD[rotated])
  done

lemma not_env_steps_first_no_trace:
  "no_trace f \<Longrightarrow> not_env_steps_first f"
  by (fastforce simp add: not_env_steps_first_def dest: no_trace_emp)

lemma not_env_steps_first_interference:
  "not_env_steps_first interference"
  apply (simp add: interference_def commit_step_def bind_def get_def
                   return_def put_trace_elem_def)
  apply (clarsimp simp: not_env_steps_first_def)
  done

lemmas not_env_steps_first_simple
    = no_trace_all[THEN not_env_steps_first_no_trace]

lemma not_env_steps_first_repeat_n:
  "not_env_steps_first f \<Longrightarrow> not_env_steps_first (repeat_n n f)"
  by (induct n; simp add: not_env_steps_first_bind not_env_steps_first_simple)

lemma not_env_steps_first_repeat:
  "not_env_steps_first f \<Longrightarrow> not_env_steps_first (repeat f)"
  by (simp add: repeat_def not_env_steps_first_bind
                   not_env_steps_first_repeat_n not_env_steps_first_simple)

lemmas not_env_steps_first_all = not_env_steps_first_interference
    not_env_steps_first_bind[rule_format] not_env_steps_first_repeat_n
    not_env_steps_first_repeat not_env_steps_first_simple

lemma rel_tr_refinement_bind_left_general:
  "reflp sr
    \<Longrightarrow> (\<forall>x. not_env_steps_first (h x)) \<or> (\<forall>s s' t. sr s s' \<longrightarrow> R s t = R s' t)
    \<Longrightarrow> rel_tr_refinement sr P R C f g
    \<Longrightarrow> rel_tr_refinement sr P R C (f >>= (\<lambda>x. h x)) (g >>= h)"
  apply (subst rel_tr_refinement_def, clarsimp)
  apply (erule elem_bindE)
   apply (drule(3) rel_tr_refinementD, simp)
   apply (clarsimp simp: bind_def)
   apply (strengthen bexI[mk_strg I _ E], simp)
   apply auto[1]
  apply (clarsimp simp: rely_cond_append)
  apply (drule(3) rel_tr_refinementD, simp)
  apply (clarsimp simp: bind_def)
  apply (simp add: image_def)
  apply (strengthen bexI[mk_strg I _ E] | simp)+
  apply (simp add: list_all2_append rely_cond_append
                   list_all2_same reflpD[where R=sr] rel_prod_sel
        split del: if_split)
  apply (erule rely_cond_equiv_s)
  apply (erule disjE)
   apply (drule spec, drule(2) not_env_steps_firstD)
   apply (clarsimp simp: neq_Nil_conv list_all2_Cons1 split: if_split_asm)
  apply (clarsimp simp: neq_Nil_conv list_all2_Cons1 last_st_tr_def hd_append
                 split: if_split_asm)
  done

lemmas rel_tr_refinement_bind_left
    = rel_tr_refinement_bind_left_general[OF _ disjI1]

lemma rel_tr_refinement_bind_right_general:
  "reflp sr
    \<Longrightarrow> \<forall>x. rel_tr_refinement sr Q R C' (g x) (h x)
    \<Longrightarrow> \<lbrace>\<lambda>s0 s. (C \<longrightarrow> s0 = s) \<and> P s\<rbrace>,\<lbrace>R\<rbrace> f
        \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_ s0 s. (C' \<longrightarrow> s0 = s) \<and> Q s\<rbrace>
    \<Longrightarrow> rel_tr_refinement sr P R C (f >>= (\<lambda>x. g x)) (f >>= h)"
  apply (subst rel_tr_refinement_def, clarsimp)
  apply (erule elem_bindE)
   apply (clarsimp simp: bind_def)
   apply (strengthen bexI[mk_strg I _ E], simp)
   apply (auto simp: list_all2_same reflpD[where R=sr])[1]
  apply (clarsimp simp: rely_cond_append)
  apply (drule validI_D, erule(1) conjI, assumption+, clarsimp)
  apply (drule spec, drule(3) rel_tr_refinementD,
    simp add: hd_append hd_map split: if_split_asm)
  apply (clarsimp simp: bind_def)
  apply (simp add: image_def)
  apply (strengthen bexI[mk_strg I _ E] | simp)+
  apply (simp add: list_all2_append list_all2_lengthD)
  apply (simp add: rely_cond_append list_all2_same reflpD[where R=sr] rel_prod_sel
        split del: if_split)
  done

lemmas validI_triv' = validI_weaken_pre[OF validI_triv, simplified]
lemmas rel_tr_refinement_bind_right
    = rel_tr_refinement_bind_right_general[where C'=False, simplified]

lemma rel_tr_refinement_comm_repeat_n[simplified K_bind_def]:
  "equivp sr
    \<Longrightarrow> rel_tr_refinement sr P R C (do f; g od) (do x \<leftarrow> g; f; return x od)
    \<Longrightarrow> not_env_steps_first f \<or> (\<forall>s s' t. sr s s' \<longrightarrow> R s t = R s' t)
    \<Longrightarrow> \<lbrace>\<lambda>s0 s. (C \<longrightarrow> s0 = s) \<and> P s\<rbrace>,\<lbrace>R\<rbrace> f
        \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_ s0 s. (C \<longrightarrow> s0 = s) \<and> P s\<rbrace>
    \<Longrightarrow> rel_tr_refinement sr P R C
        (do repeat_n n f; g od)
        (do x \<leftarrow> g; repeat_n n f; return x od)"
  apply (induct n)
   apply simp
   apply (rule rel_tr_refinement_refl)
   apply (metis equivpE)
  apply (simp add: bind_assoc repeat_n_plus[where m=1, simplified])
  apply (rule rel_tr_refinement_trans)
    apply (metis equivpE)
   apply (rule rel_tr_refinement_bind_right_general[rule_format])
     apply (metis equivpE)
    apply assumption
   apply (rule validI_weaken_pre, wp repeat_n_validI)
   apply simp
  apply (drule_tac h="\<lambda>x. do f; return x od"
      in rel_tr_refinement_bind_left_general[rotated 2])
    apply (metis equivpE)
   apply (auto intro!: not_env_steps_first_all)[1]
  apply (simp add: bind_assoc)
  done

lemma rel_tr_refinement_comm_repeat[simplified K_bind_def]:
  "equivp sr
    \<Longrightarrow> rel_tr_refinement sr P R C (do f; g od) (do x \<leftarrow> g; f; return x od)
    \<Longrightarrow> not_env_steps_first f \<or> (\<forall>s s' t. sr s s' \<longrightarrow> R s t = R s' t)
    \<Longrightarrow> \<lbrace>\<lambda>s0 s. (C \<longrightarrow> s0 = s) \<and> P s\<rbrace>,\<lbrace>R\<rbrace> f
        \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_ s0 s. (C \<longrightarrow> s0 = s) \<and> P s\<rbrace>
    \<Longrightarrow> rel_tr_refinement sr P R C
        (do repeat f; g od)
        (do x \<leftarrow> g; repeat f; return x od)"
  apply (simp add: repeat_def select_early bind_assoc)
  apply (rule rel_tr_refinement_bind_right_general[rule_format])
    apply (metis equivpE)
   apply (erule(1) rel_tr_refinement_comm_repeat_n, simp+)
  apply (rule validI_weaken_pre, wp, simp)
  done

lemma rel_tr_refinement_rev_comm_repeat_n[simplified K_bind_def]:
  "equivp sr
    \<Longrightarrow> rel_tr_refinement sr P R C (do x \<leftarrow> g; f; return x od) (do f; g od)
    \<Longrightarrow> not_env_steps_first f \<or> (\<forall>s s' t. sr s s' \<longrightarrow> R s t = R s' t)
    \<Longrightarrow> \<lbrace>\<lambda>s0 s. (C \<longrightarrow> s0 = s) \<and> P s\<rbrace>,\<lbrace>R\<rbrace> f
        \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_ s0 s. (C \<longrightarrow> s0 = s) \<and> P s\<rbrace>
    \<Longrightarrow> rel_tr_refinement sr P R C
        (do x \<leftarrow> g; repeat_n n f; return x od)
        (do repeat_n n f; g od)"
  apply (induct n)
   apply simp
   apply (rule rel_tr_refinement_refl)
   apply (metis equivpE)
  apply (simp add: bind_assoc repeat_n_plus[where m=1, simplified])
  apply (rule rel_tr_refinement_trans)
    apply (metis equivpE)
   prefer 2
   apply (rule rel_tr_refinement_bind_right_general[rule_format])
     apply (metis equivpE)
    apply assumption
   apply (rule validI_weaken_pre, wp repeat_n_validI)
   apply simp
  apply (drule_tac h="\<lambda>x. do f; return x od"
      in rel_tr_refinement_bind_left_general[rotated 2])
    apply (metis equivpE)
   apply (auto intro!: not_env_steps_first_all)[1]
  apply (simp add: bind_assoc)
  done

lemma rel_tr_refinement_rev_comm_repeat[simplified K_bind_def]:
  "equivp sr
    \<Longrightarrow> rel_tr_refinement sr P R C (do x \<leftarrow> g; f; return x od) (do f; g od)
    \<Longrightarrow> not_env_steps_first f \<or> (\<forall>s s' t. sr s s' \<longrightarrow> R s t = R s' t)
    \<Longrightarrow> \<lbrace>\<lambda>s0 s. (C \<longrightarrow> s0 = s) \<and> P s\<rbrace>,\<lbrace>R\<rbrace> f
        \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_ s0 s. (C \<longrightarrow> s0 = s) \<and> P s\<rbrace>
    \<Longrightarrow> rel_tr_refinement sr P R C
        (do x \<leftarrow> g; repeat f; return x od)
        (do repeat f; g od)"
  apply (simp add: repeat_def select_early bind_assoc)
  apply (rule rel_tr_refinement_bind_right_general[rule_format])
    apply (metis equivpE)
   apply (erule(1) rel_tr_refinement_rev_comm_repeat_n, simp+)
  apply (rule validI_weaken_pre, wp, simp)
  done

lemma alternative_distrib_lhs_bind:
  "(f \<sqinter> g) >>= h = ((f >>= h) \<sqinter> (g >>= h))"
  by (simp add: bind_def alternative_def)

lemma shuttle_modify_commit_step[simplified K_bind_def]:
  "\<forall>s. sr s (f s) \<Longrightarrow> rel_tr_refinement sr P R C
    (do x \<leftarrow> commit_step; modify f od) (do x \<leftarrow> modify f; commit_step od)"
  apply (simp add: rel_tr_refinement_def commit_step_def
                   put_trace_elem_def bind_def get_def return_def modify_def put_def)
  apply (simp add: rely_cond_def)
  done

lemma shuttle_gets_commit_step[simplified K_bind_def]:
  "reflp sr \<Longrightarrow> rel_tr_refinement sr P R C
    (do x \<leftarrow> commit_step; gets f od) (do x \<leftarrow> gets f; commit_step; return x od)"
  apply (simp add: rel_tr_refinement_def commit_step_def
                   put_trace_elem_def bind_def get_def return_def gets_def)
  apply (simp add: rely_cond_def reflpD)
  done

lemma shuttle_modify_interference[simplified K_bind_def]:
  assumes sr: "\<forall>s. sr s (f s)" (*FIXME add P as in next lemma*)
    and P_stable: "\<forall>s t. P s \<longrightarrow> R s t \<longrightarrow> P t"
    and R: "\<forall>s0 s. P s0 \<longrightarrow> R s0 s \<longrightarrow> R (f s0) (f s)"
  shows
  "rel_tr_refinement sr P R C
        (do interference; modify f od)
        (do modify f; interference od)"
proof -
  have list_all2_map:
    "\<And>xs. list_all2 (rel_prod (=) sr) xs (map (apsnd f) xs)"
    by (clarsimp simp add: list_all2_map2 list_all2_same sr)
  have rely_cond:
    "\<And>xs. \<forall>s. P s \<longrightarrow> rely_cond R s (map (Pair Env) xs)
                  \<longrightarrow> rely_cond R (f s) (map (apsnd f o Pair Env) xs)"
    apply (induct_tac xs rule: rev_induct; simp add: rely_cond_append)
    apply clarsimp
    apply (rule conjI[rotated])
     apply (frule_tac t=x in P_stable[rule_format])
      apply (clarsimp simp: rely_cond_def)
     apply (drule spec, drule(1) mp, drule(1) mp)
     apply (clarsimp simp: rely_cond_def)
    apply (clarsimp simp: rely_cond_def R)
    done
  show ?thesis
    apply (clarsimp simp: rel_tr_refinement_def)
    apply (clarsimp simp: bind_def commit_step_def get_def return_def
                          put_trace_elem_def modify_def put_def
                          interference_def env_steps_def select_def
                          )
    apply (erule disjE; clarsimp)
    apply (simp add: put_trace_eq_drop)
    apply (clarsimp; split if_split_asm)
     apply (clarsimp simp: image_Union)
     apply (rule exI, strengthen list_all2_map)
     apply (clarsimp simp: rely_cond_append)
     apply (frule(1) rely_cond[rule_format])
     apply simp
     apply (simp add: rely_cond_append rely_cond_Cons)
     apply (rule exI[where x="map f xs" for xs])
     apply (simp add: o_def, strengthen refl)
     apply (simp add: last_st_tr_def hd_append hd_map)
    apply (clarsimp simp: Sigma_def image_Union)
    apply (rule exI, strengthen list_all2_map)
    apply (clarsimp simp: rely_cond_append drop_map)
    apply (frule(1) rely_cond[rule_format])
    apply (simp add: rely_cond_append rely_cond_Cons)
    apply (rule exI[where x="map f xs" for xs])
    apply (simp add: drop_map[symmetric] o_def)
    apply auto
    done
qed

lemma last_st_tr_in_set:
  "last_st_tr (map (Pair x) ss') s \<in> set (ss' @ [s])"
  by (clarsimp simp: last_st_tr_def o_def hd_append)

lemma rshuttle_modify_interference[simplified K_bind_def]:
  assumes sr: "\<forall>s. P s \<longrightarrow> sr (f s) s"
    and P_stable: "\<forall>s t. P s \<longrightarrow> R s t \<longrightarrow> P t"
    and R: "\<forall>s0 s. R (f s0) s \<longrightarrow> P s0 \<longrightarrow> (\<exists>s_pre. s = f s_pre \<and> R s0 s_pre)"
  shows
  "rel_tr_refinement sr P R C
        (do modify f; interference od)
        (do interference; modify f od)"
proof -
  have last_st_tr: "\<And>s ss. last_st_tr (map (Pair Env \<circ> f) ss) (f s)
        = f (last_st_tr (map (Pair Env) ss) s)"
    by (simp add: last_st_tr_def hd_append hd_map)
  { fix s ss s'
  have rely_cond_P_stable[rule_format]:
    "P s \<longrightarrow> rely_cond R s (map (Pair Env) ss)
           \<longrightarrow> s' \<in> set (ss @ [s]) \<longrightarrow> P s'"
    apply (induct ss arbitrary: s' rule: list.induct)
     apply simp
    apply clarsimp
    apply (clarsimp simp: rely_cond_Cons_eq P_stable)
    apply (erule P_stable[rule_format, rotated])
    apply (case_tac x2; simp add: last_st_tr_in_set)
    done
  } note rely_cond_P_stable = this
  have rely_cond_ex:
    "\<And>s ss. rely_cond R (f s) (map (Pair Env) ss) \<longrightarrow> P s
        \<longrightarrow> (\<exists>ss'. rely_cond R s (map (Pair Env) ss') \<and> ss = map f ss')"
    apply (induct_tac ss)
     apply simp
    apply (clarsimp simp: rely_cond_Cons_eq last_st_tr)
    apply (frule R[rule_format], erule(1) rely_cond_P_stable, rule last_st_tr_in_set)
    apply (strengthen exI[where x="x # xs" for x xs])
    apply (simp add: rely_cond_Cons_eq)
    apply blast
    done
  show ?thesis
    apply (clarsimp simp: rel_tr_refinement_def)
    apply (clarsimp simp: bind_def commit_step_def get_def return_def
                          put_trace_elem_def modify_def put_def
                          interference_def env_steps_def select_def
                          )
    apply (erule disjE; clarsimp)
    apply (clarsimp simp: put_trace_eq_drop)
    apply (split if_split_asm)
     apply (clarsimp simp: image_Union rely_cond_append rely_cond_Cons_eq)
     apply (drule(1) rely_cond_ex[rule_format], clarsimp)
     apply (strengthen exI[where x="map (Pair Env) ss @ [(Me, x)]" for ss x], simp)
     apply (simp add: rely_cond_append rely_cond_Cons)
     apply (strengthen list_all2_appendI, simp)
     apply (simp add: list_all2_map1 list_all2_map2)
     apply (intro exI, strengthen sr[rule_format] list_all2_same[THEN iffD2])
     apply (simp add: sr last_st_tr rely_cond_P_stable)
     apply blast
    apply (clarsimp simp: image_Union rely_cond_append rely_cond_Cons_eq)
    apply (simp add: drop_map)
    apply (drule(1) rely_cond_ex[rule_format], clarsimp)
    apply (strengthen exI[where x="(map (Pair Env) ss @ [(Me, x)])" for n ss x], simp)
    apply (strengthen list_all2_appendI, simp)
    apply (simp add: list_all2_map1 list_all2_map2)
    apply (intro exI, strengthen sr[rule_format] list_all2_same[THEN iffD2])
    apply (simp add: sr last_st_tr rely_cond_append rely_cond_Cons_eq rely_cond_P_stable)
    apply (strengthen bexI[where x=1], simp)
    apply (strengthen exI[where x="x # xs" for x xs], simp)
    apply blast
    done
qed

lemma shuttle_gets_env_step[simplified K_bind_def]:
  "reflp sr \<Longrightarrow> \<forall>s t. P s \<longrightarrow> R s t \<longrightarrow> f s = f t
    \<Longrightarrow> rel_tr_refinement sr P R True
        (do x \<leftarrow> env_step; gets f od) (do x \<leftarrow> gets f; env_step; return x od)"
  apply (simp add: rel_tr_refinement_def env_step_def select_def
                   put_trace_elem_def bind_def get_def return_def gets_def put_def)
  apply (clarsimp simp: rely_cond_def reflpD)
  done

lemmas prefix_closed_interference[simp] = interference_twp[THEN validI_prefix_closed]

lemma env_step_twp[wp]:
  "\<lbrace>\<lambda>s0 s. (\<forall>s'. R s0 s' \<longrightarrow> Q () s' s')\<rbrace>,\<lbrace>R\<rbrace> env_step \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (simp add: env_step_def)
  apply (rule validI_weaken_pre)
   apply (wp put_trace_elem_twp)
  apply (clarsimp simp: rely_cond_def drop_Cons' guar_cond_def)
  done

lemma shuttle_modify_interferences[simplified K_bind_def]:
  "equivp sr \<Longrightarrow> \<forall>s. sr s (f s) \<Longrightarrow> \<forall>s t. P s \<longrightarrow> R s t \<longrightarrow> R (f s) (f t)
    \<Longrightarrow> not_env_steps_first g
    \<Longrightarrow> \<forall>s t. P s \<longrightarrow> R\<^sup>*\<^sup>* s t \<longrightarrow> P t
    \<Longrightarrow> rel_tr_refinement sr P R C
        (do x \<leftarrow> interferences; modify f; g od) (do x \<leftarrow> modify f; interferences; g od)"
  apply (simp only: bind_assoc[symmetric])
  apply (rule rel_tr_refinement_bind_left_general)
    apply (metis equivpE)
   apply simp
  apply (rule rel_tr_refinement_drop_C)
  apply (rule rel_tr_refinement_comm_repeat[where g="modify f", simplified])
     apply assumption
    apply (rule shuttle_modify_interference, (simp add: r_into_rtranclp)+)
   apply (simp add: not_env_steps_first_interference)
  apply (rule validI_weaken_pre, wp, simp)
  done

lemmas shuttle_modify_interferences_flat
    = shuttle_modify_interferences[where g="return ()", simplified]

lemma rshuttle_modify_interferences[simplified K_bind_def]:
  "equivp sr \<Longrightarrow> \<forall>s. sr (f s) s
    \<Longrightarrow> \<forall>s0 s. R (f s0) s \<longrightarrow> P s0 \<longrightarrow> (\<exists>s_pre. s = f s_pre \<and> R s0 s_pre)
    \<Longrightarrow> not_env_steps_first g
    \<Longrightarrow> \<forall>s t. P s \<longrightarrow> R\<^sup>*\<^sup>* s t \<longrightarrow> P t
    \<Longrightarrow> rel_tr_refinement sr P R C
        (do x \<leftarrow> modify f; interferences; g od)
        (do x \<leftarrow> interferences; modify f; g od)"
  apply (simp only: bind_assoc[symmetric])
  apply (rule rel_tr_refinement_bind_left_general)
    apply (metis equivpE)
   apply simp
  apply (rule rel_tr_refinement_drop_C)
  apply (rule rel_tr_refinement_rev_comm_repeat[where g="modify f", simplified])
     apply assumption
    apply (rule rshuttle_modify_interference, (simp add: r_into_rtranclp)+)
   apply (simp add: not_env_steps_first_interference)
  apply (rule validI_weaken_pre, wp)
  apply simp
  done

lemma shuttle_gets_interference[simplified K_bind_def]:
  "equivp sr \<Longrightarrow> \<forall>s t. P s \<longrightarrow> R s t \<longrightarrow> f s = f t
    \<Longrightarrow> (\<forall>s s' t. sr s s' \<longrightarrow> R s t = R s' t)
    \<Longrightarrow> \<forall>s t. P s \<longrightarrow> R\<^sup>*\<^sup>* s t \<longrightarrow> P t
    \<Longrightarrow> rel_tr_refinement sr P R C
        (do x \<leftarrow> interference; gets f od) (do x \<leftarrow> gets f; interference; return x od)"
  apply (simp add: interference_def bind_assoc env_steps_repeat)
  apply (rule rel_tr_refinement_trans)
    apply (metis equivpE)
   apply (rule rel_tr_refinement_bind_right_general[where C'=True and Q=P])
     apply (metis equivpE)
    apply (rule allI)
    apply (rule rel_tr_refinement_comm_repeat, assumption)
      apply (rule shuttle_gets_env_step)
       apply (metis equivpE)
      apply simp
     apply simp
    apply (rule validI_weaken_pre, wp)
    apply (clarsimp simp: r_into_rtranclp)
   apply (simp add: commit_step_def, rule validI_weaken_pre, wp put_trace_elem_twp)
   apply (simp add: drop_Cons' guar_cond_def)
  apply (rule shuttle_gets_commit_step[THEN
    rel_tr_refinement_bind_left_general[rotated -1], simplified bind_assoc return_bind])
    apply (metis equivpE)
   apply (metis equivpE)
  apply simp
  done

lemma shuttle_gets_interferences[simplified K_bind_def]:
  "equivp sr \<Longrightarrow> \<forall>s t. P s \<longrightarrow> R s t \<longrightarrow> f s = f t
    \<Longrightarrow> (\<forall>s s' t. sr s s' \<longrightarrow> R s t = R s' t)
    \<Longrightarrow> \<forall>s t. P s \<longrightarrow> R\<^sup>*\<^sup>* s t \<longrightarrow> P t
    \<Longrightarrow> rel_tr_refinement sr P R C
        (do interferences; x \<leftarrow> gets f; g x od) (do x \<leftarrow> gets f; interferences; g x od)"
  apply (rule rel_tr_refinement_trans)
    apply (metis equivpE)
   apply (simp only: bind_assoc[symmetric] K_bind_def)
   apply (rule rel_tr_refinement_bind_left_general)
     apply (metis equivpE)
    apply simp
   apply (rule rel_tr_refinement_comm_repeat, assumption)
     apply (rule shuttle_gets_interference; simp)
     apply simp
    apply (rule validI_weaken_pre, wp, simp)
   apply wpsimp
  apply (simp add: bind_assoc)
  apply (rule rel_tr_refinement_refl)
  apply (metis equivpE)
  done

lemmas shuttle_gets_interferences_flat
    = shuttle_gets_interferences[where g = return, simplified]

definition
  adjust_tr_relation :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> bool"
where
  "adjust_tr_relation tr_r sr = (equivp tr_r \<and> (\<forall>s t t'. tr_r t t' \<longrightarrow> sr s t = sr s t'))"

lemma adjust_tr_relation_equivp:
  "equivp sr
    \<Longrightarrow> adjust_tr_relation sr sr"
  apply (simp add: adjust_tr_relation_def)
  apply (metis equivpE sympD transpD)
  done

lemma prefix_refinement_i_modify_split:
  "adjust_tr_relation tr_r sr
    \<Longrightarrow> \<forall>s t. isr s t \<longrightarrow> P s \<longrightarrow> Q t \<longrightarrow> intsr (f s) (g t)
    \<Longrightarrow> \<forall>s. tr_r s (g s)
    \<Longrightarrow> \<forall>s t. R s t \<longrightarrow> R (g s) (g t)
    \<Longrightarrow> not_env_steps_first b
    \<Longrightarrow> prefix_refinement sr intsr osr rvr' P' Q' AR R
        d (do x \<leftarrow> interferences; b od)
    \<Longrightarrow> prefix_refinement sr isr osr rvr' (\<lambda>s0 s. P s \<and> P' s0 (f s)) (\<lambda>s0 s. Q s \<and> Q' s0 (g s)) AR R
        (do z \<leftarrow> modify f; d od)
        (do x \<leftarrow> interferences; y \<leftarrow> modify g; b od)"
  apply (clarsimp simp: adjust_tr_relation_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule pfx_refinement_use_rel_tr_refinement[where tr_r=tr_r and Q=\<top>])
      apply (rule shuttle_modify_interferences, simp+)
    apply (rule prefix_refinement_bind[where intsr=intsr])
       apply (rule prefix_refinement_modify, assumption)
      apply assumption
     apply wp+
   apply simp
  apply simp
  done

end
