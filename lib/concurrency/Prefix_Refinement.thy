(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory Prefix_Refinement

imports
  Triv_Refinement
  "Monads.Trace_Lemmas"

begin

section \<open>Definition of prefix fragment refinement.\<close>

text \<open>
This is a notion of refinement/simulation making use of prefix closure.
For a concrete program to refine an abstract program, then for every
trace of the concrete program there must exist a well-formed fragment
of the abstract program that matches (according to the simulation
relation) but which leaves enough decisions available to the abstract
environment to permit parallel composition.
\<close>

text \<open>
Fragments must be self-closed, or enabled. Certain incomplete traces
must be possible to extend by a program step.
\<close>
definition
  self_closed :: "((tmid \<times> 's) list \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> bool"
where
  "self_closed cond s f = (\<forall>xs. (xs, Incomplete) \<in> f s
    \<longrightarrow> cond xs \<longrightarrow> (\<exists>s'. (Me, s') # xs \<in> fst ` f s))"

lemmas self_closedD = self_closed_def[THEN iffD1, rule_format]

text \<open>
Fragments must be environment-closed. Certain incomplete traces
must be possible to extend by any environment step that is
compatible with some condition.
\<close>
definition
  env_closed :: "((tmid \<times> 's) list \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> bool"
where
  "env_closed cond s f = (\<forall>xs s'. (xs, Incomplete) \<in> f s
    \<longrightarrow> cond xs s' \<longrightarrow> ((Env, s') # xs) \<in> fst ` f s)"

lemmas env_closedD = env_closed_def[THEN iffD1, rule_format]

lemma env_closed_strengthen_cond:
  "env_closed P s f
    \<Longrightarrow> (\<forall>xs s. Q xs s \<longrightarrow> P xs s)
    \<Longrightarrow> env_closed Q s f"
  by (simp add: env_closed_def)

text \<open>
Two traces match according to some state relation if they match at every step.
\<close>
definition
  matching_tr :: "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> (tmid \<times> 't) list \<Rightarrow> bool"
where
  "matching_tr sr = list_all2 (\<lambda>(aid, as) (cid, cs). aid = cid \<and> sr as cs)"

definition
  matching_tr_pfx :: "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> (tmid \<times> 't) list \<Rightarrow> bool"
where
  "matching_tr_pfx sr atr ctr = (length atr \<le> length ctr
    \<and> matching_tr sr (rev atr) (take (length atr) (rev ctr)))"

abbreviation
  "matching_tr_tmids_pfx \<equiv> matching_tr_pfx (\<lambda>_ _. True)"

abbreviation(input)
  "matching_self_cond ctr \<equiv> (\<lambda>xs. length xs < length ctr \<and> fst (rev ctr ! length xs) = Me)"

abbreviation(input)
  "matching_env_cond sr ctr s0 R \<equiv> (\<lambda>xs s. matching_tr_pfx sr ((Env, s) # xs) ctr
                \<and> rely_cond R s0 ((Env, s) # xs))"

text \<open>
The collection of properties a fragment must have to match some concrete
trace. It must be prefix, self and environment closed, nonempty, and all
outcomes must be matching. The outcomes (trace and result) must match
the rely condition, the concrete trace (or a prefix), and must either be
a matching result or @{term Incomplete} if a prefix.
\<close>
definition
  is_matching_fragment :: "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool)
        \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (tmid \<times> 't) list \<Rightarrow> ('t, 'b) tmres
        \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> bool"
where
  "is_matching_fragment sr osr rvr ctr cres s0 R s f
    = ((prefix_closed f
        \<and> self_closed (matching_self_cond ctr) s f
        \<and> env_closed (matching_env_cond sr ctr s0 R) s f)
        \<and> (f s \<noteq> {})
        \<and> (\<forall>(tr, res) \<in> f s. rely_cond R s0 tr
            \<and> matching_tr_pfx sr tr ctr
            \<and> (length tr < length ctr \<longrightarrow> res = Incomplete)
            \<and> (length tr = length ctr \<longrightarrow> rel_tmres osr rvr res cres)))"

lemmas is_matching_fragmentD = is_matching_fragment_def[THEN iffD1, rule_format]

lemmas is_matching_fragment_wf = is_matching_fragmentD[THEN conjunct1]
lemmas is_matching_fragment_prefix_closed = is_matching_fragment_wf[THEN conjunct1]
lemmas is_matching_fragment_self_closed = is_matching_fragment_wf[THEN conjunct2, THEN conjunct1]
lemmas is_matching_fragment_env_closed = is_matching_fragment_wf[THEN conjunct2, THEN conjunct2]
lemmas is_matching_fragment_defD
    = is_matching_fragmentD[THEN conjunct2, THEN conjunct1, rule_format]
lemmas is_matching_fragment_trD
    = is_matching_fragmentD[THEN conjunct2, THEN conjunct2,
        rule_format, where x="(tr, res)" for tr res, simplified, rule_format]

text \<open>
Prefix fragment refinement. Given the initial conditions, every concrete outcome
(trace and result) must have a matching fragment which is a simple refinement of
the abstract program.
\<close>
definition
  prefix_refinement :: "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool)
    \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool)
    \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool)
    \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> ('t, 'b) tmonad \<Rightarrow> bool"
where
  "prefix_refinement sr isr osr rvr P Q AR R aprog cprog
    = (\<forall>s s0 t0 t. isr s t \<longrightarrow> P s0 s \<longrightarrow> sr s0 t0 \<longrightarrow> Q t0 t
    \<longrightarrow> (\<forall>(ctr, cres) \<in> cprog t.
        rely_cond R t0 ctr \<longrightarrow> (\<exists>f. is_matching_fragment sr osr rvr ctr cres s0 AR s f
            \<and> triv_refinement aprog f)))"

abbreviation
  "pfx_refn sr rvr P \<equiv> prefix_refinement sr sr sr rvr P"

lemmas prefix_refinementD = prefix_refinement_def[THEN iffD1, rule_format]
lemmas split_iffD1 = Product_Type.split[THEN iffD1]
lemmas pfx_refnD = prefix_refinementD
lemmas pfx_refnD2 = pfx_refnD[THEN split_iffD1[where a=tr and b=res for tr res], rule_format]

lemma matching_tr_pfx_aCons:
  "matching_tr_pfx sr ((tmid, s) # atr) ctr
    = (\<exists>s'. length atr < length ctr \<and> rev ctr ! length atr = (tmid, s')
        \<and> sr s s' \<and> matching_tr_pfx sr atr ctr)"
  apply (simp add: matching_tr_pfx_def matching_tr_def Suc_le_eq
                   list_all2_conv_all_nth less_Suc_eq all_conj_distrib)
  apply (simp add: nth_append prod_eq_iff)
  apply auto
  done

lemma rely_cond_hd:
  "rely_cond R s0 xs \<Longrightarrow> xs \<noteq> []
    \<Longrightarrow> fst (hd xs) = Env \<longrightarrow> R (last_st_tr (tl xs) s0) (snd (hd xs))"
  by (clarsimp simp: rely_cond_def neq_Nil_conv trace_steps_append
              split: if_split_asm)

lemma diff_Suc_eq_if:
  "(Suc n - m) = (if m \<le> n then Suc (n - m) else 0)"
  by auto

lemma rely_cond_nth:
  "rely_cond R s0 tr \<Longrightarrow> n < length tr
    \<Longrightarrow> fst (rev tr ! n) = Env \<longrightarrow> R ((if n = 0 then s0 else snd (rev tr ! (n - 1)))) (snd (rev tr ! n))"
  by (simp add: rely_cond_def trace_steps_rev_drop_nth[where n=0, simplified])

lemma is_matching_fragment_Nil:
  "is_matching_fragment sr osr rvr ctr cres s0 R s f
    \<Longrightarrow> [] \<in> fst ` f s"
  apply (clarsimp simp: is_matching_fragment_def)
  apply (clarsimp simp only: set_eq_iff empty_iff simp_thms not_all)
  apply (drule(1) prefix_closed_drop[where tr=tr and n="length tr" for tr])
  apply (clarsimp simp add: in_fst_snd_image)
  done

section \<open>Implications\<close>
text \<open>
The notions of matching fragment and prefix refinement we have defined
allow us to prove the existence of a matching trace in the abstract
program.
\<close>
theorem matching_fragment_matching_tr:
  assumes match: "is_matching_fragment sr osr rvr ctr cres s0 R' s f"
  and rely: "rely_cond R t0 ctr"
  and sr0: "sr s0 t0"
  and sr: "(\<forall>s t t'. sr s t \<longrightarrow> R t t' \<longrightarrow> (\<exists>s'. sr s' t' \<and> R' s s'))"
  shows "\<exists>(atr, ares) \<in> f s. matching_tr sr atr ctr
                    \<and> rel_tmres osr rvr ares cres
                    \<and> rely_cond R' s0 atr"
proof -

  note pfx_closed = is_matching_fragment_prefix_closed[OF match]
  note f_prop = is_matching_fragment_trD[OF match]
  note env_closed = is_matching_fragment_env_closed[OF match]
  note self_closed = is_matching_fragment_self_closed[OF match]

  note pfx_closedD = pfx_closed[THEN prefix_closedD]

  have extend:
    "\<And>tmid s' tr res. ((tmid, s') # tr, res) \<in> f s \<Longrightarrow> rely_cond R' s0 tr
        \<Longrightarrow> \<exists>x res. (x # tr, res) \<in> f s \<and> rely_cond R' s0 (x # tr)"
    apply (case_tac tmid)
     apply (fastforce simp: rely_cond_Cons)
    apply (frule f_prop[OF pfx_closedD], clarsimp)
    apply (frule f_prop, clarsimp simp: matching_tr_pfx_aCons)
    apply (frule rely_cond_nth[rotated], rule rely, simp)
    apply (drule_tac s="last_st_tr tr s0" in sr[rule_format, rotated])
     apply (clarsimp simp: sr0 neq_Nil_conv matching_tr_pfx_aCons)
    apply clarsimp
    apply (rename_tac t' s'_rely)
    apply (drule_tac s'="s'_rely" in env_closedD[where f=f, OF env_closed, OF prefix_closedD[OF pfx_closed]])
     apply (clarsimp simp: matching_tr_pfx_aCons rely_cond_Cons_eq)
    apply clarsimp
    apply (fastforce intro!: rely_cond_Cons)
    done

  have extend2:
    "\<And>tr res. (tr, res) \<in> f s \<Longrightarrow> rely_cond R' s0 tr
        \<Longrightarrow> length tr < length ctr
        \<Longrightarrow> \<exists>x res. (x # tr, res) \<in> f s \<and> rely_cond R' s0 (x # tr)"
    apply (frule f_prop, clarsimp)
    apply (case_tac "fst (rev ctr ! length tr)")
     apply (frule self_closed[THEN self_closedD], simp)
     apply (fastforce intro: rely_cond_Cons)
    apply (frule rely_cond_nth[rotated], rule rely, simp)
    apply (drule_tac s="last_st_tr tr s0" in sr[rule_format, rotated])
     apply (clarsimp simp: sr0 neq_Nil_conv matching_tr_pfx_aCons)
    apply clarsimp
    apply (drule_tac s'=s' in env_closedD[OF env_closed])
     apply (simp add: matching_tr_pfx_aCons prod_eq_iff rely_cond_Cons)
    apply (fastforce intro: rely_cond_Cons)
    done

  { fix n
    have "\<exists>(tr, res) \<in> f s. (n \<le> length ctr \<longrightarrow> length tr = n)
        \<and> rely_cond R' s0 tr"
      apply (induct n)
       apply (cut_tac f=f in is_matching_fragment_Nil;
          (rule sr0 match)?)
       apply fastforce
      apply clarsimp
      apply (case_tac "\<not> (Suc n \<le> length ctr)")
       apply fastforce
      apply clarsimp
      apply (drule(1) extend2, simp)
      apply (fastforce elim: rev_bexI)
      done
  }
  note induct = this[rule_format]
  show ?thesis
    using induct[where n="length ctr"]
    apply clarsimp
    apply (rule rev_bexI, assumption)
    apply clarsimp
    apply (frule is_matching_fragment_trD[OF match])
    apply (clarsimp simp: matching_tr_pfx_def matching_tr_def)
    done
qed

corollary matching_fragment_matching_tr_trivR:
  assumes match: "is_matching_fragment sr osr rvr ctr cres s0 R s f"
  and sr: "(\<forall>s t t'. sr s t \<longrightarrow> (\<exists>s'. sr s' t' \<and> R s s'))"
  and srx: "sr s0 t0"
  shows "\<exists>(atr, ares) \<in> f s. matching_tr sr atr ctr
                    \<and> rel_tmres osr rvr ares cres"
  using matching_fragment_matching_tr[where R="\<lambda>_ _. True",
        OF match _ srx]
  by (auto simp add: rely_cond_def sr)

theorem prefix_refinement_rely_cond_trD:
  assumes preds: "prefix_refinement sr isr osr rvr P Q R' R aprog cprog"
    "isr s t" "P s0 s" "Q t0 t" "(ctr, cres) \<in> cprog t"
    "rely_cond R t0 ctr" "sr s0 t0"
  and sr: "(\<forall>s t t'. sr s t \<longrightarrow> R t t' \<longrightarrow> (\<exists>s'. sr s' t' \<and> R' s s'))"
  shows "\<exists>(atr, ares) \<in> aprog s. matching_tr sr atr ctr
                    \<and> rel_tmres osr rvr ares cres
                    \<and> rely_cond R' s0 atr"
proof -
  obtain f where subs: "f s \<subseteq> aprog s"
      and match: "is_matching_fragment sr osr rvr ctr cres s0 R' s f"
    using prefix_refinementD[OF preds(1-3) _ preds(4-5)] preds(6-)
    by (auto simp add: triv_refinement_def)
  show ?thesis
    using matching_fragment_matching_tr[OF match _ _ sr] preds subs
    by blast
qed

lemma rely_cond_True:
  "rely_cond (\<lambda>_ _. True) = (\<lambda>_ _. True)"
  by (simp add: rely_cond_def fun_eq_iff)

section \<open>Compositionality.\<close>
text \<open>The crucial rules for proving prefix refinement
of parallel and sequential compositions.\<close>

lemma ball_set_zip_conv_nth:
  "(\<forall>x \<in> set (zip ys zs). P x)
    = (\<forall>n. n < length ys \<longrightarrow> n < length zs \<longrightarrow> P (ys ! n, zs ! n))"
  by (auto simp add: Ball_def in_set_zip)

definition
  par_tr_fin_principle :: "('s, unit) tmonad \<Rightarrow> bool"
where
  "par_tr_fin_principle f = (\<forall>s tr s'. (tr, Result ((), s')) \<in> f s \<longrightarrow> s' = last_st_tr tr s \<and> tr \<noteq> [])"

lemmas par_tr_fin_principleD = par_tr_fin_principle_def[THEN iffD1, rule_format]

lemma tr_in_parallel:
  "(tr, res) \<in> parallel f g s
    \<Longrightarrow> \<exists>f_tr g_tr. (f_tr, res) \<in> f s \<and> (g_tr, res) \<in> g s
        \<and> (tr, res) \<in> parallel (K {(f_tr, res)}) (K {(g_tr, res)}) s"
  apply (clarsimp simp: parallel_def)
  apply fastforce
  done

lemma matching_env_closedD:
  "(tr, res) \<in> f s
    \<Longrightarrow> is_matching_fragment sr osr rvr ctr cres s0 R s f
    \<Longrightarrow> length tr < length ctr
    \<Longrightarrow> fst (rev ctr ! length tr) = Env
    \<Longrightarrow> sr s' (snd (rev ctr ! length tr))
    \<Longrightarrow> R (last_st_tr tr s0) s'
    \<Longrightarrow> (Env, s') # tr \<in> fst ` f s"
  apply (frule(1) is_matching_fragment_trD, clarsimp)
  apply (erule(1) env_closedD[OF is_matching_fragment_env_closed])
  apply (clarsimp simp: matching_tr_pfx_aCons rely_cond_Cons_eq prod_eq_iff)
  done

lemma par_tr_fin_fragment:
  "par_tr_fin_principle f
    \<Longrightarrow> (tr, res) \<in> f s
    \<Longrightarrow> is_matching_fragment sr osr rvr ctr cres s0 R s f
    \<Longrightarrow> res = (case (length ctr - length tr, cres)
          of (0, Failed) \<Rightarrow> Failed
           | (0, Result _) \<Rightarrow> Result ((), last_st_tr tr s)
           | _ \<Rightarrow> Incomplete)"
  apply (frule(1) is_matching_fragment_trD)
  apply (cases "length tr < length ctr")
   apply (clarsimp split: nat.split)
  apply (clarsimp simp: matching_tr_pfx_def)
  apply (erule tmres.rel_cases; clarsimp)
  apply (frule(1) par_tr_fin_principleD)
  apply (clarsimp simp: neq_Nil_conv)
  done

lemma par_tr_fragment_in_parallel:
  "par_tr_fin_principle f
    \<Longrightarrow> par_tr_fin_principle g
    \<Longrightarrow> is_matching_fragment sr osr rvr ctr1 cres s0 R s f
    \<Longrightarrow> is_matching_fragment sr osr' rvr ctr2 cres s0 R' s g
    \<Longrightarrow> length ctr1 = length ctr2
    \<Longrightarrow> \<exists>f_steps res'. length f_steps = length tr
        \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then id else Env, s)) (zip f_steps tr), res) \<in> f s
        \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then Env else id, s)) (zip f_steps tr), res') \<in> g s
    \<Longrightarrow> (tr, res) \<in> parallel f g s"
  apply (clarsimp simp: parallel_def)
  apply (rule_tac x=f_steps in exI, clarsimp)
  apply (drule(2) par_tr_fin_fragment)+
  apply (simp only: list_all2_lengthD)
  apply (clarsimp split: nat.split_asm tmres.split_asm)
  apply (simp add: last_st_tr_def o_def split_def)
  done

lemma par_tr_fragment_parallel_def:
  "par_tr_fin_principle f
    \<Longrightarrow> par_tr_fin_principle g
    \<Longrightarrow> is_matching_fragment sr osr rvr ctr1 cres s0 R s f
    \<Longrightarrow> is_matching_fragment sr osr' rvr ctr2 cres s0 R' s g
    \<Longrightarrow> length ctr1 = length ctr2
    \<Longrightarrow> parallel f g s = {(tr, res). \<exists>f_steps res'. length f_steps = length tr
        \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then id else Env, s)) (zip f_steps tr), res) \<in> f s
        \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then Env else id, s)) (zip f_steps tr), res') \<in> g s}"
  apply (rule equalityI; clarsimp)
   apply (auto simp: parallel_def)[1]
  apply (erule(4) par_tr_fragment_in_parallel)
  apply blast
  done

lemmas list_all2_rev_nthD
    = list_all2_nthD[OF list_all2_rev[THEN iffD2], simplified]

definition
  forward_enabled :: "'s rg_pred \<Rightarrow> bool"
where
  "forward_enabled P = (\<forall>s_pre. \<exists>s. P s_pre s)"

lemmas forward_enabledD = forward_enabled_def[THEN iffD1, rule_format]

lemma forward_enabled_mono:
  "P \<le> Q \<Longrightarrow> forward_enabled P \<Longrightarrow> forward_enabled Q"
  by (fastforce simp: forward_enabled_def le_fun_def)

lemma forward_enabled_reflp:
  "reflp P \<Longrightarrow> forward_enabled P"
  by (auto simp add: reflp_def forward_enabled_def)

lemma par_tr_fin_principle_triv_refinement:
  "par_tr_fin_principle aprog
    \<Longrightarrow> triv_refinement aprog cprog
    \<Longrightarrow> par_tr_fin_principle cprog"
  by (fastforce simp: par_tr_fin_principle_def triv_refinement_def)

lemma matching_tr_pfx_parallel_zip:
  "matching_tr_pfx sr a_pfx a_tr
    \<Longrightarrow> matching_tr_pfx sr b_pfx b_tr
    \<Longrightarrow> length a_pfx = length b_pfx
    \<Longrightarrow> list_all2 (\<lambda>y z. (fst y = Env \<or> fst z = Env) \<and> snd y = snd z) a_tr b_tr
    \<Longrightarrow> matching_tr_pfx sr (map parallel_mrg (zip a_pfx b_pfx)) (map parallel_mrg (zip a_tr b_tr))"
  apply (clarsimp simp: matching_tr_pfx_def matching_tr_def list_all2_lengthD)
  apply (clarsimp simp: list_all2_conv_all_nth)
  apply (clarsimp simp: rev_map split_def zip_rev[symmetric])
  done

lemma drop_sub_Suc_is_Cons:
  "n = length xs \<Longrightarrow> m < length xs \<Longrightarrow> drop (n - Suc m) xs = (rev xs ! m) # drop (n - m) xs"
  apply (rule nth_equalityI; clarsimp)
  apply (clarsimp simp add: nth_Cons' rev_nth)
  done

lemma le_sub_eq_0:
  "((x :: nat) \<le> x - y) = (x = 0 \<or> y = 0)"
  by arith

lemmas rely_cond_append_split
    = rely_cond_append[where xs="take n xs" and ys="drop n xs" for n xs, simplified]
lemmas guar_cond_append_split
    = guar_cond_append[where xs="take n xs" and ys="drop n xs" for n xs, simplified]

lemma validI_drop_next_G:
  "\<lbrakk> \<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>, \<lbrace>Q\<rbrace>; P s0 s; (tr, res) \<in> f s;
        rely_cond R s0 (drop (n - m) tr); n = length tr; m < length tr \<rbrakk>
    \<Longrightarrow> fst (rev tr ! m) \<noteq> Env
        \<longrightarrow> G (last_st_tr (rev (take m (rev tr))) s0) (snd (rev tr ! m))"
  apply clarify
  apply (drule(2) validI_GD_drop[where n="n - Suc m"])
   apply (simp add: drop_sub_Suc_is_Cons)
   apply (rule rely_cond_Cons; simp)
  apply (subst(asm) guar_cond_append_split[where n=1])
  apply (simp add: take_Suc Suc_diff_Suc)
  apply (simp add: guar_cond_def take_rev hd_drop_conv_nth
                   eq_Me_neq_Env rev_nth)
  done

lemma tr_in_parallel_validI:
  assumes elem: "(tr, res) \<in> parallel (K {(f_tr, res)}) (K {(g_tr, res)}) s"
  and trs: "(f_tr, res) \<in> f s" "(g_tr, res) \<in> g s"
  and validI: "\<lbrace>P\<rbrace>, \<lbrace>E or Gg\<rbrace> f \<lbrace>Gf\<rbrace>, \<lbrace>Q\<rbrace>" "\<lbrace>P\<rbrace>, \<lbrace>E or Gf\<rbrace> g \<lbrace>Gg\<rbrace>, \<lbrace>Q2\<rbrace>"
  and P: "P s0 s" and rel: "rely_cond E s0 tr"
  shows "rely_cond (E or Gg) s0 f_tr \<and> rely_cond (E or Gf) s0 g_tr"
  using parallel_rely_induct0[where R=E and G="\<top>\<top>", OF elem _ _ validI, OF P P]
  by (clarsimp simp: rel trs predicate2I)

lemma env_closed_parallel_fragment:
  "is_matching_fragment sr osr rvr ctr1 cres1 s0 (E or Gg) s f
    \<Longrightarrow> is_matching_fragment sr osr' rvr ctr2 cres2 s0 (E or Gf) s g
    \<Longrightarrow> par_tr_fin_principle f
    \<Longrightarrow> par_tr_fin_principle g
    \<Longrightarrow> cres1 = cres2 \<Longrightarrow> length ctr1 = length ctr2
    \<Longrightarrow> \<forall>s xs. Q xs s \<longrightarrow> (sr s (snd (rev ctr1 ! length xs)))
        \<and> (sr s (snd (rev ctr2 ! length xs)))
        \<and> length xs < length ctr2
        \<and> fst (rev ctr1 ! length xs) = Env
        \<and> fst (rev ctr2 ! length xs) = Env
        \<and> E (last_st_tr xs s0) s
    \<Longrightarrow> env_closed Q s (parallel f g)"
  apply (subst env_closed_def, clarsimp)
  apply (frule is_matching_fragment_prefix_closed[where f=f])
  apply (frule is_matching_fragment_prefix_closed[where f=g])
  apply (subst(asm) parallel_def, clarsimp simp: length_Suc_conv)
  apply (strengthen in_fst_snd_image)
  apply (simp add: par_tr_fragment_parallel_def)
  apply (strengthen exI[where x="x # xs" for x xs])
  apply (frule(1) is_matching_fragment_trD[where f=f])
  apply (frule(1) is_matching_fragment_trD[where f=g])
  apply (clarsimp simp: matching_tr_pfx_aCons rely_cond_Cons_eq
                        last_st_tr_map_zip pred_disj_def)
  apply (drule spec2, drule(1) mp[where P="Q xs s" for xs s])
  apply clarsimp
  apply (drule_tac s'=s' in env_closedD[where f=f, OF is_matching_fragment_env_closed, rotated];
    simp?)
   apply (simp add: matching_tr_pfx_aCons rely_cond_Cons_eq last_st_tr_map_zip prod_eq_iff)
  apply (drule_tac s'=s' in env_closedD[where f=g, OF is_matching_fragment_env_closed, rotated];
    simp?)
   apply (simp add: matching_tr_pfx_aCons rely_cond_Cons_eq last_st_tr_map_zip prod_eq_iff)
  apply clarsimp
  apply blast
  done

lemma self_closed_parallel_fragment:
  notes if_split[split del]
  shows
  "is_matching_fragment sr osr rvr ctr1 cres1 s0 (E or Gg) s f
    \<Longrightarrow> is_matching_fragment sr osr' rvr ctr2 cres2 s0 (E or Gf) s g
    \<Longrightarrow> par_tr_fin_principle f
    \<Longrightarrow> par_tr_fin_principle g
    \<Longrightarrow> list_all2 (\<lambda>y z. (fst y = Env \<or> fst z = Env) \<and> snd y = snd z) ctr1 ctr2
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>E or Gg\<rbrace> f \<lbrace>Gf\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>E or Gf\<rbrace> g \<lbrace>Gg\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>
    \<Longrightarrow> P s0 s
    \<Longrightarrow> cres1 = cres2
    \<Longrightarrow> Q = (\<lambda>xs. length xs < length ctr1 \<and> (fst (rev ctr1 ! length xs) \<noteq> Env
            \<or> fst (rev ctr2 ! length xs) \<noteq> Env))
    \<Longrightarrow> self_closed Q s (parallel f g)"
  apply (subst self_closed_def, clarsimp)
  apply (subst(asm) parallel_def, clarsimp)
  apply (frule list_all2_lengthD[symmetric])
  apply (strengthen in_fst_snd_image)
  apply (simp add: par_tr_fragment_parallel_def)
  apply (strengthen exI[where x="x # xs" for x xs])
  apply (clarsimp simp: length_Suc_conv)
  apply (frule(1) list_all2_rev_nthD, clarsimp)
  apply (case_tac "fst (rev ctr1 ! length xs) = Env"; simp)
   apply (frule is_matching_fragment_self_closed[where f=g],
     drule(1) self_closedD, simp add: eq_Me_neq_Env)
   apply (thin_tac "v \<in> g s" for v s)
   apply clarsimp
   apply (frule(1) is_matching_fragment_trD[where f=g])
   apply clarsimp
   apply (frule(3) validI_GD[where f=g])
   apply (clarsimp simp: guar_cond_Cons_eq matching_tr_pfx_aCons)
   apply (drule_tac s'=s' in matching_env_closedD[where f=f], simp+)
    apply (simp add: last_st_tr_map_zip)
   apply (clarsimp simp: ex_bool_eq del: disjCI)
   apply (blast intro: in_fst_snd_image)
  (* pretty much identical proof for symmetric case. sad. *)
  apply (frule is_matching_fragment_self_closed[where f=f],
    drule(1) self_closedD, simp add: eq_Me_neq_Env)
  apply (thin_tac "v \<in> f s" for v s)
  apply clarsimp
  apply (frule(1) is_matching_fragment_trD[where f=f])
  apply clarsimp
  apply (frule(3) validI_GD[where f=f])
  apply (clarsimp simp: guar_cond_Cons_eq matching_tr_pfx_aCons)
  apply (drule_tac s'=s' in matching_env_closedD[where f=g], simp+)
   apply (simp add: last_st_tr_map_zip)
  apply (clarsimp simp: ex_bool_eq del: disjCI)
  apply (blast intro: in_fst_snd_image)
  done

lemma is_matching_fragment_validI_disj:
  "is_matching_fragment sr osr rvr b_tr bd_res s0 R s f
    \<Longrightarrow> triv_refinement g f
    \<Longrightarrow> G = \<top>\<top> \<or> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>"
  apply (frule is_matching_fragment_prefix_closed)
  apply (erule disjE)
   apply (simp add: validI_def guar_cond_def)
  apply (erule(2) validI_triv_refinement)
  done

lemma rely_prefix_closed:
  "prefix_closed f \<Longrightarrow> prefix_closed (rely f R s0)"
  apply (subst prefix_closed_def, clarsimp simp: rely_def rely_cond_Cons_eq)
  apply (erule(1) prefix_closedD)
  done

lemma rely_self_closed:
  "self_closed P s f \<Longrightarrow> self_closed P s (rely f R s0)"
  apply (subst self_closed_def, clarsimp simp: rely_def rely_cond_Cons_eq)
  apply (drule(2) self_closedD)
  apply (fastforce simp: rely_cond_Cons_eq)
  done

lemma rely_env_closed:
  "env_closed P s f
    \<Longrightarrow> (\<forall>xs s. P' xs s \<longrightarrow> rely_cond R s0 xs \<longrightarrow> P xs s \<and> R (last_st_tr xs s0) s)
    \<Longrightarrow> env_closed P' s (rely f R s0)"
  apply (subst env_closed_def, clarsimp simp: rely_def)
  apply (drule_tac s'=s' in env_closedD, assumption)
   apply simp
  apply (clarsimp simp: image_def)
  apply (fastforce intro: rely_cond_Cons rev_bexI)
  done

theorem prefix_refinement_parallel:
  "prefix_refinement sr isr osr rvr P Q (AE or Gc) (E or Gd) a b
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q (AE or Ga) (E or Gb) c d
    \<Longrightarrow> par_tr_fin_principle a
    \<Longrightarrow> par_tr_fin_principle c
    \<Longrightarrow> \<lbrace>Q\<rbrace>,\<lbrace>E or Gd\<rbrace> b \<lbrace>Gb\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>
    \<Longrightarrow> \<lbrace>Q\<rbrace>,\<lbrace>E or Gb\<rbrace> d \<lbrace>Gd\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>
    \<Longrightarrow> (Ga = \<top>\<top> \<and> Gc = \<top>\<top>)
        \<or> (\<lbrace>P\<rbrace>,\<lbrace>AE or Gc\<rbrace> a \<lbrace>Ga\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>
            \<and> \<lbrace>P\<rbrace>,\<lbrace>AE or Ga\<rbrace> c \<lbrace>Gc\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>)
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q AE E (parallel a c) (parallel b d)"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule tr_in_parallel, clarify)
  apply (frule(6) tr_in_parallel_validI)
  apply (clarsimp simp: parallel_def3)
  apply (rename_tac b_tr d_tr bd_res)
  apply (drule(5) prefix_refinementD)+
  apply clarsimp
  apply (rename_tac f_a f_c)
  apply (rule_tac x="rely (parallel f_a f_c) AE s0" in exI)
  apply (rule conjI[rotated])
   apply (simp add: parallel_def3 triv_refinement_def rely_def)
   apply blast
  apply (subst is_matching_fragment_def, clarsimp)
  apply (frule(1) is_matching_fragment_validI_disj[where g=a and G=Ga], blast)
  apply (frule(1) is_matching_fragment_validI_disj[where g=c and G=Gc], blast)
  apply (intro conjI parallel_prefix_closed rely_prefix_closed rely_self_closed,
    simp_all add: is_matching_fragment_prefix_closed)
     apply (rule self_closed_parallel_fragment,
        (assumption | erule par_tr_fin_principle_triv_refinement[rotated])+)
      apply simp
     apply (frule list_all2_lengthD)
     apply (simp add: list_all2_lengthD eq_Me_neq_Env rev_nth split_def fun_eq_iff
                cong: conj_cong)
    apply (rule rely_env_closed[where P=P and P'=P for P, rotated])
     apply (simp add: rely_cond_Cons_eq)
    apply (rule env_closed_parallel_fragment,
        (assumption | erule par_tr_fin_principle_triv_refinement[rotated])+)
      apply simp
     apply (simp add: list_all2_lengthD)
    apply (clarsimp simp: matching_tr_pfx_aCons rev_map split_def
                          zip_rev[symmetric] list_all2_lengthD[symmetric]
                          rely_cond_Cons_eq)
    apply (frule list_all2_lengthD)
    apply (drule(1) list_all2_rev_nthD, simp)
    apply (simp split: if_split_asm)
   apply (simp add: rely_def par_tr_fragment_parallel_def list_all2_lengthD
                    par_tr_fin_principle_triv_refinement set_eq_iff)
   apply (strengthen exI[where x=Nil] in_fst_snd_image)+
   apply (simp add: is_matching_fragment_Nil[simplified image_def Bex_def, simplified])
  apply (clarsimp simp: parallel_def3 rely_def)
  apply (drule(1) is_matching_fragment_trD)+
  apply (clarsimp simp: list_all2_lengthD)
  apply (rule matching_tr_pfx_parallel_zip; assumption?)
  apply (simp add: list_all2_lengthD)
  done

lemma validI_triv':
  "prefix_closed f \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>"
  by (simp add: validI_def guar_cond_def)
lemmas validI_triv = validI_triv'[where P="\<top>\<top>"]

lemmas prefix_refinement_parallel_ART
    = prefix_refinement_parallel[OF _ _ _ _ _ _ disjI1[OF conjI, OF refl refl]]
lemmas prefix_refinement_parallel_triv
    = prefix_refinement_parallel_ART[OF _ _ _ _ validI_triv' validI_triv']
lemmas prefix_refinement_parallel'
    = prefix_refinement_parallel[OF _ _ _ _ _ _ disjI2[OF conjI]]

lemma pfx_trace_set_allD:
  "\<forall>n. \<forall>v\<in>set (take n xs). P n v \<Longrightarrow> v \<in> set (take n xs)
    \<Longrightarrow> P n v"
  by simp

lemma prefix_closed_UNION:
   "(\<forall>s' x. x \<in> S s' \<longrightarrow> prefix_closed (f x))
    \<Longrightarrow> prefix_closed (\<lambda>s. \<Union>x \<in> S s. f x s)"
  apply (simp add: prefix_closed_def)
  apply (blast intro: in_fst_snd_image)
  done

lemma is_matching_fragment_UNION:
  "(\<forall>x. x \<in> S s \<longrightarrow> is_matching_fragment sr osr rvr ctr cres s0 R s (f x))
    \<Longrightarrow> (\<forall>s' x. x \<in> S s' \<longrightarrow> prefix_closed (f x))
    \<Longrightarrow> S s \<noteq> {}
    \<Longrightarrow> is_matching_fragment sr osr rvr ctr cres s0 R s (\<lambda>s. \<Union>x \<in> S s. f x s)"
  apply (clarsimp simp: is_matching_fragment_def prefix_closed_UNION)
  apply (intro conjI impI)
   apply (clarsimp simp: self_closed_def split_def in_fst_snd_image_eq)
   apply blast
  apply (clarsimp simp: env_closed_def split_def in_fst_snd_image_eq)
  apply blast
  done

definition
  mbind :: "('s, 'a) tmonad \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> ('s, 'b) tmonad) \<Rightarrow>
           's \<Rightarrow> ('s, 'b) tmonad"
  where
  "mbind f g s0 \<equiv> \<lambda>s. \<Union>(xs, r) \<in> (f s). case r of Failed \<Rightarrow> {(xs, Failed)}
    | Incomplete \<Rightarrow> {(xs, Incomplete)}
    | Result (rv, s) \<Rightarrow> fst_upd (\<lambda>ys. ys @ xs) ` g (last_st_tr xs s0) rv s"

lemma self_closed_mbind:
  "is_matching_fragment sr osr rvr ctr cres s0 R s f
    \<Longrightarrow> (\<forall>tr x s'. (tr, Result (x, s')) \<in> f s
        \<longrightarrow> self_closed (\<lambda>xs. length xs < length ctr' \<and> fst (rev ctr' ! length xs) = Me) s'
            (g (last_st_tr tr s0) x) \<and> [] \<in> fst ` g (last_st_tr tr s0) x s')
    \<Longrightarrow> Q = matching_self_cond (ctr' @ ctr)
    \<Longrightarrow> cres = Incomplete \<longrightarrow> ctr' = []
    \<Longrightarrow> self_closed Q s (mbind f g s0)"
  apply (frule is_matching_fragment_self_closed)
  apply (subst self_closed_def, clarsimp simp: mbind_def)
  apply (rename_tac tr res)
  apply (strengthen in_fst_snd_image, simp)
  apply (frule(1) is_matching_fragment_trD)
  apply (case_tac "length tr < length ctr")
   apply clarsimp
   apply (drule(1) self_closedD)
    apply (simp add: trans[OF nth_append if_P])
   apply clarsimp
   apply (thin_tac "(x, Incomplete) \<in> S" for x S)
   apply (strengthen rev_bexI[mk_strg I E])
   apply (clarsimp split: tmres.split)
   apply (fastforce elim: image_eqI[rotated] intro: in_mres)
  apply (clarsimp simp: matching_tr_pfx_def)
  apply (erule tmres.rel_cases; clarsimp)
  apply (drule spec2, drule spec, drule(1) mp)
  apply clarsimp
  apply (drule(1) self_closedD)
   apply (simp add: trans[OF nth_append if_not_P])
  apply (strengthen rev_bexI[mk_strg I E])
  apply simp
  apply (fastforce elim: image_eqI[rotated])
  done

lemma matching_tr_pfx_rhs_is_extend:
  fixes ys ys'
  defines "N == length ys' - length ys"
  shows
  "matching_tr_pfx sr xs ys
    \<Longrightarrow> length xs \<le> length ys \<longrightarrow> drop N ys' = ys
    \<Longrightarrow> matching_tr_pfx sr xs ys'"
  apply (clarsimp simp: matching_tr_pfx_def)
  apply (rule context_conjI)
   apply simp
  apply (simp add: matching_tr_def list_all2_conv_all_nth
                   min_def)
  apply (clarsimp simp: rev_nth)
  done

lemma matching_tr_pfx_rhs_is_drop:
  fixes ys ys'
  defines "N == length ys - length ys'"
  shows
  "matching_tr_pfx sr xs ys
    \<Longrightarrow> drop N ys = ys'
    \<Longrightarrow> length xs \<le> length ys'
    \<Longrightarrow> matching_tr_pfx sr xs ys'"
  apply (clarsimp simp: matching_tr_pfx_def)
  apply (simp add: matching_tr_def list_all2_conv_all_nth
                   min_def)
  apply (clarsimp simp: rev_nth)
  done

lemma env_closed_mbind:
  "is_matching_fragment sr osr rvr ctr' cres s0 R s f
    \<Longrightarrow> \<forall>tr x s'. (tr, Result (x, s')) \<in> f s
        \<longrightarrow> env_closed (matching_env_cond sr ctr'' (last_st_tr tr s0) R) s' (g (last_st_tr tr s0) x)
            \<and> [] \<in> fst ` g (last_st_tr tr s0) x s'
    \<Longrightarrow> (if cres \<in> {Incomplete, Failed} then ctr = ctr' else ctr = ctr'' @ ctr')
    \<Longrightarrow> Q = matching_env_cond sr ctr s0 R
    \<Longrightarrow> env_closed Q s (mbind f g s0)"
  apply (simp add: if_bool_eq_conj)
  apply (subst env_closed_def, clarsimp simp: mbind_def)
  apply (strengthen in_fst_snd_image, simp)
  apply (rename_tac f_tr f_res s')
  apply (case_tac "f_res = Incomplete")
   apply (frule(1) is_matching_fragment_trD)
   apply clarsimp
   apply (drule is_matching_fragment_env_closed)
   apply (drule_tac s'=s' in env_closedD, assumption)
    apply (clarsimp simp: matching_tr_pfx_aCons matching_tr_pfx_def)
    apply (cases cres; clarsimp)
   apply clarsimp
   apply (strengthen bexI[where x="(x # xs, r)" for x xs r, mk_strg I _ E])
   apply (simp split: tmres.split)
   apply clarsimp
   apply (drule spec2, drule spec, drule(1) mp)
   apply clarsimp
   apply (strengthen image_eqI[mk_strg I _ E])
   apply simp
  apply (frule(1) is_matching_fragment_trD)
  apply (case_tac f_res; clarsimp)
  apply (cases cres; clarsimp simp: matching_tr_pfx_def)
  apply (strengthen bexI[mk_strg I _ E], simp)
  apply (drule spec2, drule spec, drule(1) mp)+
  apply clarsimp
  apply (drule_tac s'=s' in env_closedD, assumption)
   apply (simp add: rely_cond_append rely_cond_Cons_eq matching_tr_pfx_aCons)
   apply (clarsimp simp: nth_append)
   apply (clarsimp simp: matching_tr_def list_all2_append)
  apply clarsimp
  apply (fastforce elim: image_eqI[rotated])
  done

lemma mbind_prefix_closed:
  "prefix_closed f
    \<Longrightarrow> \<forall>tr x s' s. (tr, Result (x, s')) \<in> f s \<longrightarrow> prefix_closed (g (last_st_tr tr s0) x)
   \<Longrightarrow> prefix_closed (mbind f g s0)"
  apply (subst prefix_closed_def, clarsimp simp: mbind_def)
  apply (split tmres.split_asm; clarsimp;
        (drule(1) prefix_closedD, fastforce elim: rev_bexI)?)
  apply (simp add: Cons_eq_append_conv, safe)
   apply (drule(1) prefix_closedD)
   apply (fastforce elim: rev_bexI)
  apply (drule spec2, drule mp, blast)
  apply (erule rev_bexI, clarsimp)
  apply (drule(1) prefix_closedD)
  apply fastforce
  done

lemma is_matching_fragment_mbind:
  "is_matching_fragment sr intsr rvr ctr cres s0 R s f_a
    \<Longrightarrow> \<forall>tr x s'. (tr, Result (x, s')) \<in> f_a s
        \<longrightarrow> is_matching_fragment sr osr rvr' ctr' cres' (last_st_tr tr s0) R s' (f_b (last_st_tr tr s0) x)
    \<Longrightarrow> \<forall>s0' x. prefix_closed (f_b s0' x)
    \<Longrightarrow> ctr'' = ctr' @ ctr
    \<Longrightarrow> cres'' = (case cres of Failed \<Rightarrow> Failed | Incomplete \<Rightarrow> Incomplete | _ \<Rightarrow> cres')
    \<Longrightarrow> (cres = Incomplete \<or> cres = Failed) \<longrightarrow> ctr' = []
    \<Longrightarrow> is_matching_fragment sr osr rvr' ctr'' cres'' s0 R s
        (mbind f_a f_b s0)"
  apply (subst is_matching_fragment_def, clarsimp)
  apply (strengthen env_closed_mbind[where ctr''=ctr', mk_strg I E]
                    mbind_prefix_closed
                    self_closed_mbind[where ctr'="ctr'", mk_strg I E])
  apply (simp add: conj_comms if_bool_eq_conj mres_def split del: if_split)
  apply (intro conjI allI impI; clarsimp?;
    (blast intro: is_matching_fragment_prefix_closed
                  is_matching_fragment_env_closed
                  is_matching_fragment_Nil
                  is_matching_fragment_self_closed
            dest: post_by_hoare)?)
   apply (clarsimp simp: mbind_def)
   apply (frule_tac s=s in is_matching_fragment_defD)
   apply (drule ex_in_conv[THEN iffD2], clarsimp)
   apply (drule(1) bspec)
   apply (rename_tac res; case_tac res; clarsimp)
   apply (drule spec2, drule spec, drule(1) mp)
   apply (fastforce dest: is_matching_fragment_defD)
  apply (clarsimp simp: mbind_def)
  apply (drule(1) is_matching_fragment_trD)
  apply (clarsimp simp: matching_tr_pfx_def split: tmres.split_asm)
  apply (drule spec2, drule spec, drule(1) mp)
  apply (drule(1) is_matching_fragment_trD)
  apply (clarsimp simp: matching_tr_pfx_def matching_tr_def
                        list_all2_appendI rely_cond_append)
  done

lemma is_matching_fragment_mbind_union:
  "is_matching_fragment sr intsr rvr ctr cres s0 R s f_a
    \<Longrightarrow> ctr'' = ctr' @ ctr
    \<Longrightarrow> cres'' = (case cres of Failed \<Rightarrow> Failed | Incomplete \<Rightarrow> Incomplete | _ \<Rightarrow> cres')
    \<Longrightarrow> cres = Incomplete \<or> cres = Failed \<longrightarrow> ctr' = []
    \<Longrightarrow> \<forall>tr x s'. (tr, Result (x, s')) \<in> f_a s
        \<longrightarrow> (\<exists>f. is_matching_fragment sr osr rvr' ctr' cres' (last_st_tr tr s0) R s' f
                \<and> triv_refinement (aprog x) f)
    \<Longrightarrow> is_matching_fragment sr osr rvr' ctr'' cres'' s0 R s
        (mbind f_a (\<lambda>s0' rv s. \<Union>f \<in> {f. is_matching_fragment sr osr rvr' ctr' cres' s0' R s f
                    \<and> triv_refinement (aprog rv) f}. f s) s0)"
  apply (rule is_matching_fragment_mbind; assumption?)
   apply clarsimp
   apply (rule is_matching_fragment_UNION)
     apply clarsimp
    apply (clarsimp simp: is_matching_fragment_prefix_closed)
   apply clarsimp
  apply clarsimp
  apply (rule prefix_closed_UNION)
  apply (clarsimp simp: is_matching_fragment_prefix_closed)
  done

lemma is_matching_fragment_mresD:
  "is_matching_fragment sr osr rvr ctr cres s0 R s f
    \<Longrightarrow> (x, s') \<in> mres (f s)
    \<Longrightarrow> \<exists>y s''. cres = Result (y, s'') \<and> osr s' s'' \<and> rvr x y"
  apply (clarsimp simp: mres_def)
  apply (frule(1) is_matching_fragment_trD)
  apply (clarsimp simp: matching_tr_pfx_def)
  apply (erule tmres.rel_cases; clarsimp)
  done

lemma matching_tr_pfx_sr_hd_append:
  "matching_tr_pfx sr tr tr'
    \<Longrightarrow> sr s0 t0
    \<Longrightarrow> length tr \<ge> length tr'
    \<Longrightarrow> sr (hd (map snd tr @ [s0])) (hd (map snd tr' @ [t0]))"
  apply (clarsimp simp: matching_tr_pfx_def matching_tr_def)
  apply (erule list.rel_cases; clarsimp)
  done

lemma matching_tr_pfx_last_st_tr:
  "matching_tr_pfx sr tr tr'
    \<Longrightarrow> sr s0 t0
    \<Longrightarrow> length tr \<ge> length tr'
    \<Longrightarrow> sr (last_st_tr tr s0) (last_st_tr tr' t0)"
  apply (clarsimp simp: matching_tr_pfx_def matching_tr_def)
  apply (erule list.rel_cases; clarsimp)
  done

lemma validI_relyT_mresD:
  "\<lbrace>P'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>P''\<rbrace>
    \<Longrightarrow> (rv, s') \<in> mres (f s)
    \<Longrightarrow> P' s0 s
    \<Longrightarrow> \<exists>s0'. P'' rv s0' s'"
  apply (clarsimp simp: mres_def)
  apply (drule(2) validI_rvD)
   apply (simp add: rely_cond_def)
  apply blast
  done

theorem prefix_refinement_bind_general[rule_format]:
  "prefix_refinement sr isr intsr rvr P Q AR R a c
    \<Longrightarrow> (\<forall>x y. rvr x y \<longrightarrow> prefix_refinement sr intsr osr rvr' (P'' x) (Q'' y) AR R (b x) (d y))
    \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>AR\<rbrace> a \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>P''\<rbrace> \<or> \<lbrace>\<lambda>s. \<exists>s0. P' s0 s\<rbrace> a \<lbrace>\<lambda>rv s. \<forall>s0. P'' rv s0 s\<rbrace>
    \<Longrightarrow> \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>Q''\<rbrace>
    \<Longrightarrow> prefix_refinement sr isr osr rvr' (P and P') (Q and Q') AR R (a >>= b) (c >>= d)"
  apply (subst prefix_refinement_def, clarsimp simp: bind_def)
  apply (rename_tac c_tr c_res cd_tr cd_res)
  apply (drule(5) prefix_refinementD, simp)
  apply (drule mp)
   apply (erule rely_cond_is_drop, clarsimp split: tmres.split_asm)
  apply clarsimp
  apply (rename_tac f_a)
  apply (case_tac "c_res = Incomplete \<or> c_res = Failed")
   apply (intro exI conjI)
    apply (rule_tac ctr'=Nil and cres'=Failed and f_b="\<lambda>_ _ _. {}"
        in is_matching_fragment_mbind, assumption, simp_all add: prefix_closed_def)[1]
      apply clarsimp
      apply (frule is_matching_fragment_mresD, erule in_mres)
      apply clarsimp
     apply (clarsimp split: tmres.split_asm)
    apply (clarsimp split: tmres.split_asm)
   apply (clarsimp simp: triv_refinement_def mbind_def)
   apply (rule rev_bexI, drule spec, erule(1) subsetD)
   apply (clarsimp split: tmres.split_asm)
  apply (clarsimp split: tmres.split_asm)
  apply (frule(2) validI_rvD, simp add: rely_cond_append)
  apply (intro exI conjI)
   apply (rule is_matching_fragment_mbind_union[where aprog="b"],
      assumption, simp_all)[1]
   apply clarsimp
   apply (frule is_matching_fragment_mresD, erule in_mres)
   apply (clarsimp simp: mres_def)
   apply (frule(1) is_matching_fragment_trD)
   apply clarsimp
   apply (rule prefix_refinementD[where x="(a, b)" for a b, simplified, rule_format],
      blast, simp_all)[1]
     prefer 2
     apply (erule(1) matching_tr_pfx_last_st_tr)
     apply simp
    apply (erule disjE)
     apply (drule(1) validI_rvD[OF validI_triv_refinement],
         erule is_matching_fragment_prefix_closed, assumption+)
    apply (drule(2) use_valid[OF in_mres valid_triv_refinement], blast, simp)
   apply (clarsimp simp: rely_cond_append hd_append hd_map cong: if_cong)
  apply (clarsimp simp: triv_refinement_def mbind_def)
  apply (rule rev_bexI, drule spec, erule(1) subsetD)
  apply (clarsimp split: tmres.split_asm)
  apply (rule image_eqI[where x="(a, b)" for a b], simp)
  apply blast
  done

section \<open>Using prefix refinement.\<close>
text \<open>
Using prefix refinement to map the validI Hoare quadruple
(precond/rely/guarantee/postcond). Proofs of quadruples for
abstract programs imply related quadruples for concrete
programs.
\<close>

lemma list_all2_all_trace_steps:
  assumes P: "\<forall>x\<in>trace_steps (rev tr) s0. P x"
  and lR': "list_all2 (\<lambda>(aid, as) (cid, cs). aid = cid \<and> R' as cs) tr' tr"
  and R': "R' s0' s0"
  and Q: "\<forall>idn as1 as2 cs1 cs2. R' as1 cs1 \<longrightarrow> R' as2 cs2
    \<longrightarrow> P (idn, cs1, cs2) \<longrightarrow> Q (idn, as1, as2)"
  shows "\<forall>x\<in>trace_steps (rev tr') s0'. Q x"
proof -
  note lR'' = lR'[simplified trans[OF list_all2_rev[symmetric] list_all2_conv_all_nth],
    simplified split_def, THEN conjunct2, rule_format]
  note len[simp] = lR'[THEN list_all2_lengthD]
  show ?thesis
    using P R'
    apply (clarsimp simp: trace_steps_nth)
    apply (drule_tac x=x in bspec, simp)
    apply (frule lR''[simplified])
    apply (cut_tac i="x - 1" in lR'', simp)
    apply (auto simp: Q)
    done
qed

theorem prefix_refinement_validI:
  "prefix_refinement sr isr osr rvr prP' prP R' R f g
    \<Longrightarrow> \<lbrace>P'\<rbrace>,\<lbrace>R'\<rbrace>
        f \<lbrace>\<lambda>s0 s. \<forall>cs0 cs. sr s0 cs0 \<and> sr s cs \<longrightarrow> G cs0 cs\<rbrace>,\<lbrace>\<lambda>rv
                s0 s. \<forall>rv' cs0 cs. sr s0 cs0 \<and> osr s cs \<and> rvr rv rv' \<longrightarrow> Q rv' cs0 cs\<rbrace>
    \<Longrightarrow> \<forall>t0 t. P t0 t \<longrightarrow> (\<exists>s0 s. P' s0 s \<and> prP' s0 s \<and> prP t0 t \<and> isr s t \<and> sr s0 t0)
    \<Longrightarrow> \<forall>s0 t0 t. sr s0 t0 \<and> R t0 t \<longrightarrow> (\<exists>s. R' s0 s \<and> sr s t)
    \<Longrightarrow> prefix_closed g
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (subst validI_def, clarsimp simp: rely_def)
  apply (drule spec2, drule(1) mp, clarsimp)
  apply (drule(6) prefix_refinement_rely_cond_trD[where R'=R', simplified])
    apply blast
  apply clarsimp
  apply (rule conjI)
   apply (frule(3) validI_GD)
   apply (simp add: guar_cond_def matching_tr_def)
   apply (erule_tac R'="\<lambda>cs s. sr s cs" in list_all2_all_trace_steps)
     apply (clarsimp simp: list_all2_conv_all_nth split_def)
    apply simp
   apply clarsimp
  apply clarsimp
  apply (erule tmres.rel_cases; clarsimp)
  apply (drule(1) validI_rvD, simp add: rely_def)
   apply simp
  apply (case_tac tr; clarsimp simp: list_all2_Cons2 matching_tr_def)
  done

lemmas prefix_refinement_validI' = prefix_refinement_validI[OF _ validI_strengthen_guar, OF _ validI_strengthen_post]

section \<open>Building blocks.\<close>
text \<open>
Prefix refinement rules for various basic constructs.
\<close>

lemma prefix_refinement_weaken_pre:
  "prefix_refinement sr isr osr rvr P' Q' AR R f g
    \<Longrightarrow> \<forall>s s0. P s0 s \<longrightarrow> P' s0 s
    \<Longrightarrow> (\<forall>s t s0 t0. isr s t \<longrightarrow> sr s0 t0 \<longrightarrow> P s0 s \<longrightarrow> Q t0 t \<longrightarrow> Q' t0 t)
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q AR R f g"
 by (fastforce simp: prefix_refinement_def)

lemma prefix_refinement_name_pre:
  "(\<And>s s0 t t0. isr s t \<Longrightarrow> sr s0 t0 \<Longrightarrow> P s0 s \<Longrightarrow> Q t0 t
    \<Longrightarrow> prefix_refinement sr isr osr rvr (\<lambda>s0' s'. s0' = s0 \<and> s' = s) (\<lambda>t0' t'. t0' = t0 \<and> t' = t) AR R f g)
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q AR R f g"
  by (fastforce simp: prefix_refinement_def)

lemma prefix_refinement_bind_v[rule_format]:
  "prefix_refinement sr isr intsr rvr P Q AR R a c
    \<Longrightarrow> (\<forall>x y. rvr x y \<longrightarrow> prefix_refinement sr intsr osr rvr' (\<lambda>s0. P'' x) (Q'' y) AR R (b x) (d y))
    \<Longrightarrow> \<lbrace>P'\<rbrace> a \<lbrace>P''\<rbrace> \<Longrightarrow> \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>Q''\<rbrace>
    \<Longrightarrow> prefix_refinement sr isr osr rvr' (\<lambda>s0. P s0 and P') (Q and Q') AR R (a >>= b) (c >>= d)"
  apply (rule prefix_refinement_weaken_pre,
    rule prefix_refinement_bind_general[where P'="\<lambda>_. P'"])
       apply assumption
      apply (elim allE, erule(1) mp)
     apply (rule disjI2)
     apply simp
    apply assumption
   apply clarsimp
  apply clarsimp
  done

lemmas prefix_refinement_bind
    = prefix_refinement_bind_general[OF _ _ disjI1]

lemma default_prefix_refinement_ex:
  "is_matching_fragment sr osr rvr ctr cres s0 R s
            (\<lambda>s. aprog s \<inter> ({tr'. length tr' \<le> length ctr} \<times> UNIV))
    \<Longrightarrow> \<exists>f. is_matching_fragment sr osr rvr ctr cres s0 R s f
            \<and> triv_refinement aprog f"
  apply (intro exI conjI, assumption)
  apply (simp add: triv_refinement_def)
  done

lemma default_prefix_refinement_ex_match_iosr_R:
  "is_matching_fragment sr osr rvr ctr cres s0 R s
            (rely (\<lambda>s. aprog s \<inter> ({tr'. matching_tr_pfx iosr tr' ctr} \<times> UNIV)) R s0)
    \<Longrightarrow> \<exists>f. is_matching_fragment sr osr rvr ctr cres s0 R s f
            \<and> triv_refinement aprog f"
  apply (intro exI conjI, assumption)
  apply (clarsimp simp add: triv_refinement_def rely_def)
  done

lemma is_matching_fragment_no_trace:
  "is_matching_fragment sr osr rvr [] cres s0 R s (\<lambda>s. {([], ares s)})
    = rel_tmres osr rvr (ares s) cres"
  by (simp add: is_matching_fragment_def prefix_closed_def
                self_closed_def env_closed_def
                matching_tr_pfx_def matching_tr_def)

lemma prefix_refinement_return_imp:
  "(\<forall>s s0 t0 t. P s0 s \<and> Q t0 t \<and> isr s t \<longrightarrow> rvr rv rv' \<and> osr s t)
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q AR R (return rv) (return rv')"
  apply (clarsimp simp: prefix_refinement_def)
  apply (rule default_prefix_refinement_ex)
  apply (auto simp add: return_def is_matching_fragment_no_trace)
  done

abbreviation(input)
  "dc2 \<equiv> (\<lambda>_ _. True)"

abbreviation
  "pfx_refnT sr rvr \<equiv> pfx_refn sr rvr (\<lambda>_ _. True) dc2"

lemma pfx_refn_return:
  "rvr rv rv'
    \<Longrightarrow> pfx_refnT sr rvr AR R (return rv) (return rv')"
  by (rule prefix_refinement_return_imp, simp)

lemma prefix_refinement_get:
  "prefix_refinement sr iosr iosr iosr dc2 dc2 AR R get get"
  apply (clarsimp simp: prefix_refinement_def get_def)
  apply (rule default_prefix_refinement_ex)
  apply (simp add: is_matching_fragment_no_trace)
  done

lemma prefix_refinement_put:
  "osr s t \<Longrightarrow> prefix_refinement sr isr osr dc2 dc2 dc2 AR R (put s) (put t)"
  apply (clarsimp simp: prefix_refinement_def put_def)
  apply (rule default_prefix_refinement_ex)
  apply (simp add: is_matching_fragment_no_trace)
  done

lemma prefix_refinement_select:
  "(\<forall>x \<in> T. \<exists>y \<in> S. rvr y x)
    \<Longrightarrow> prefix_refinement sr iosr iosr rvr dc2 dc2 AR R (select S) (select T)"
  apply (clarsimp simp: prefix_refinement_def select_def)
  apply (drule(1) bspec, clarsimp)
  apply (rule_tac x="return y" in exI)
  apply (simp add: is_matching_fragment_def self_closed_def env_closed_def return_def
                   prefix_closed_def matching_tr_pfx_def matching_tr_def)
  apply (auto simp add: triv_refinement_def return_def image_def)
  done

lemma Int_insert_left2:
  "(insert a B \<inter> C) = ((if a \<in> C then {a} else {}) \<union> (B \<inter> C))"
  by auto

definition
  rely_stable :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> bool"
where
  "rely_stable R sr Q = (\<forall>s t t'. Q t \<and> sr s t \<and> R t t' \<longrightarrow> Q t' \<and> (\<exists>s'. sr s' t'))"

lemmas rely_stableD = rely_stable_def[THEN iffD1, simplified imp_conjL, rule_format]

definition
  env_rely_stable_iosr :: "'s rg_pred \<Rightarrow> 't rg_pred
    \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> bool"
where
  "env_rely_stable_iosr AR R sr iosr Q
    = (\<forall>s0 t0 s t. Q t0 \<longrightarrow> iosr s0 t0 \<longrightarrow> R t0 t \<longrightarrow> AR s0 s \<longrightarrow> sr s t \<longrightarrow> iosr s t)"

lemmas env_rely_stable_iosrD = env_rely_stable_iosr_def[THEN iffD1, rule_format]

definition
  env_stable :: "'s rg_pred \<Rightarrow> 't rg_pred
    \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> bool"
where
  "env_stable AR R sr iosr Q = (rely_stable R sr Q
    \<and> env_rely_stable_iosr AR R sr iosr Q \<and> iosr \<le> sr)"

definition
  abs_rely_stable :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool"
where
  "abs_rely_stable R P = (\<forall>s s'. P s \<and> R s s' \<longrightarrow> P s')"

lemmas abs_rely_stableD = abs_rely_stable_def[THEN iffD1, simplified imp_conjL, rule_format]

lemma abs_rely_stableT:
  "abs_rely_stable AR \<top>"
  by (simp add: abs_rely_stable_def)

lemma rely_stable_rtranclp:
  "rely_stable R sr Q
    \<Longrightarrow> sr s t \<Longrightarrow> Q t
    \<Longrightarrow> rtranclp R t t'
    \<Longrightarrow> Q t'"
  apply (rotate_tac 3, induct arbitrary: s rule: converse_rtranclp_induct)
   apply simp
  apply (clarsimp simp: rely_stable_def)
  apply metis
  done

lemma abs_rely_stable_rtranclp:
  "abs_rely_stable R P
    \<Longrightarrow> P s \<Longrightarrow> rtranclp R s s'
    \<Longrightarrow> P s'"
  apply (rotate_tac 2, induct rule: converse_rtranclp_induct)
   apply simp
  apply (clarsimp simp: abs_rely_stable_def)
  done

lemma prefix_refinement_env_step:
  assumes env_stable: "env_stable AR R sr iosr Q"
  shows "prefix_refinement sr iosr iosr dc2 (\<lambda>s0 s. s0 = s) (\<lambda>t0 t. t0 = t \<and> Q t0)
    AR R env_step env_step"
proof -
  have P: "\<And>S. {xs. length xs = Suc 0} = (\<lambda>x. [x]) ` UNIV"
    apply (safe, simp_all)
    apply (case_tac x, auto)
    done

  have st: "rely_stable R sr Q" and est: "env_rely_stable_iosr AR R sr iosr Q"
    and sr: "iosr \<le> sr"
    using env_stable
    by (auto simp: env_stable_def)

  show ?thesis
    apply (simp add: env_step_def P)
    apply (clarsimp simp: prefix_refinement_def get_def select_def P
                          bind_def return_def put_def put_trace_elem_def Sigma_def)
    apply (strengthen default_prefix_refinement_ex_match_iosr_R[where iosr=iosr])
    apply (simp add: is_matching_fragment_def rely_cond_def rely_def)
    apply (simp add: matching_tr_pfx_def matching_tr_def)
    apply (simp only: UN_extend_simps Int_insert_left2)
    apply (simp add: is_matching_fragment_def UN_If_distrib)
    apply (intro conjI allI impI;
        simp add: prefix_closed_def in_fst_snd_image_eq self_closed_def
                  matching_tr_pfx_def matching_tr_def
                  env_closed_def)
     apply (metis env_rely_stable_iosrD[OF est])
    apply clarsimp
    apply (auto dest: rely_stableD[OF st] predicate2D[OF sr])[1]
    done
qed

lemma prefix_refinement_repeat_n:
  "prefix_refinement sr iosr iosr (\<lambda>_ _. True) P Q AR R f g
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>AR\<rbrace> f \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>
    \<Longrightarrow> \<lbrace>\<lambda>t0 t. Q t0 t \<and> (\<exists>s0 s. sr s0 t0 \<and> iosr s t)\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>
    \<Longrightarrow> prefix_refinement sr iosr iosr (\<lambda>_ _. True) P Q AR R (repeat_n n f) (repeat_n n g)"
  apply (induct n)
   apply (simp add: prefix_refinement_return_imp)
  apply (rule prefix_refinement_weaken_pre)
    apply simp
   apply (rule prefix_refinement_bind, assumption+)
   apply simp
  apply auto
  done

lemma prefix_refinement_env_n_steps:
  assumes env_stable: "env_stable AR R sr iosr Q"
  shows "prefix_refinement sr iosr iosr (\<lambda>_ _. True)
        (=) (\<lambda>t0 t. t0 = t \<and> Q t0) AR R (env_n_steps n) (env_n_steps n)"
  apply (rule prefix_refinement_repeat_n)
    apply (rule prefix_refinement_env_step[OF env_stable])
   apply (simp add: env_step_def)
   apply (wp put_trace_elem_twp)
   apply (clarsimp simp: guar_cond_def)
  apply (simp add: env_step_def)
  apply (wp put_trace_elem_twp)+
  apply simp
  apply (clarsimp simp: guar_cond_def length_Suc_conv)
  apply (cut_tac env_stable[unfolded env_stable_def])
  apply (clarsimp simp: rely_cond_def)
  apply (drule(3) rely_stableD)
  apply simp
  done

lemma prefix_refinement_repeat:
  "prefix_refinement sr iosr iosr (\<lambda>_ _. True) P Q AR R f g
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>AR\<rbrace> f \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>
    \<Longrightarrow> \<lbrace>\<lambda>t0 t. Q t0 t \<and> (\<exists>s0 s. sr s0 t0 \<and> iosr s t)\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>
    \<Longrightarrow> prefix_refinement sr iosr iosr (\<lambda>_ _. True) P Q AR R (repeat f) (repeat g)"
  apply (simp add: repeat_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind, rule prefix_refinement_select[where rvr="(=)"])
       apply simp
      apply simp
      apply (rule prefix_refinement_repeat_n, assumption+)
      apply (rule validI_weaken_pre, assumption, simp)
     apply (wp select_wp)
    apply wp
   apply clarsimp
  apply clarsimp
  done

lemma prefix_refinement_env_steps:
  "env_stable AR R sr iosr Q
    \<Longrightarrow> prefix_refinement sr iosr iosr (\<lambda>_ _. True)
        (=) (\<lambda>t0 t. t0 = t \<and> Q t0) AR R env_steps env_steps"
  apply (simp add: env_steps_repeat)
  apply (rule prefix_refinement_repeat)
    apply (erule prefix_refinement_env_step)
   apply (simp add: env_step_def)
   apply (wp put_trace_elem_twp)
   apply (clarsimp simp: guar_cond_def)
  apply (simp add: env_step_def)
  apply (wp put_trace_elem_twp)
  apply simp
  apply (clarsimp simp: guar_cond_def length_Suc_conv)
  apply (clarsimp simp: rely_cond_def env_stable_def)
  apply (blast dest: rely_stableD)
  done

lemma prefix_refinement_commit_step:
  "\<forall>s t. isr s t \<longrightarrow> sr s t \<and> osr s t
    \<Longrightarrow> prefix_refinement sr isr osr (\<lambda>_ _. True) (\<top>\<top>) (\<top>\<top>) AR R commit_step commit_step"
  apply (clarsimp simp: prefix_refinement_def)
  apply (rule default_prefix_refinement_ex)
  apply (simp add: commit_step_def bind_def get_def return_def put_trace_elem_def)
  apply (erule disjE)
   apply (simp add: is_matching_fragment_no_trace)
  apply (clarsimp simp: is_matching_fragment_def)
  apply (simp add: prefix_closed_def self_closed_def env_closed_def)
  apply (simp add: matching_tr_pfx_def matching_tr_def rely_cond_def)
  done

lemma prefix_refinement_weaken_srs:
  "prefix_refinement sr isr osr r P Q AR R f g
    \<Longrightarrow> isr' \<le> isr \<Longrightarrow> osr \<le> osr' \<Longrightarrow> sr \<le> sr
    \<Longrightarrow> prefix_refinement sr isr' osr' r P Q AR R f g"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule(1) predicate2D)
  apply (drule(5) prefix_refinementD)
  apply clarsimp
  apply (rule exI, rule conjI[rotated], assumption)
  apply (clarsimp simp: is_matching_fragment_def)
  apply (drule(1) bspec, clarsimp)
  apply (erule tmres.rel_cases; clarsimp)
  apply (erule(1) predicate2D)
  done

lemma prefix_refinement_interference:
  "env_stable AR R sr iosr Q
    \<Longrightarrow> prefix_refinement sr iosr iosr (\<lambda>_ _. True) \<top>\<top> (\<lambda>t0 t. Q t) AR R interference interference"
  apply (simp add: interference_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind[where intsr=iosr])
       apply (rule prefix_refinement_commit_step)
       apply (simp add: env_stable_def le_fun_def)
      apply (erule prefix_refinement_env_steps)
     apply (simp add: commit_step_def del: put_trace.simps)
     apply wp
    apply (simp add: commit_step_def del: put_trace.simps)
    apply wp
   apply (simp add: guar_cond_def)
  apply (clarsimp simp: guar_cond_def)
  done

lemma mapM_x_Cons:
  "mapM_x f (x # xs) = do f x; mapM_x f xs od"
  by (simp add: mapM_x_def sequence_x_def)

lemmas prefix_refinement_bind_sr = prefix_refinement_bind[where sr=sr
    and intsr=sr for sr]
lemmas prefix_refinement_bind_isr = prefix_refinement_bind[where isr=isr
    and intsr=isr for isr]
lemmas pfx_refn_bind = prefix_refinement_bind_v[where sr=sr
    and isr=sr and osr=sr and intsr=sr for sr]
lemmas pfx_refn_bindT
    = pfx_refn_bind[where P'="\<top>" and Q'="\<lambda>_ _. True", OF _ _ hoare_post_taut validI_triv,
        simplified pred_conj_def, simplified]

lemma prefix_refinement_assume_pre:
  "(P \<Longrightarrow> prefix_refinement sr isr osr rvr P' Q' AR R f g)
    \<Longrightarrow> prefix_refinement sr isr osr rvr (P' and (\<lambda>_ _. P)) Q' AR R f g"
  "(P \<Longrightarrow> prefix_refinement sr isr osr rvr P' Q' AR R f g)
    \<Longrightarrow> prefix_refinement sr isr osr rvr P' (Q' and (\<lambda>_ _. P)) AR R f g"
  by (auto simp: prefix_refinement_def)

lemma prefix_refinement_modify:
  "\<forall>s t. isr s t \<longrightarrow> P s \<longrightarrow> Q t \<longrightarrow> osr (f s) (g t)
    \<Longrightarrow> prefix_refinement sr isr osr (\<lambda>_ _. True) (\<lambda>_. P) (\<lambda>_. Q) AR R (modify f) (modify g)"
  apply (simp add: modify_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind[where intsr=isr, OF prefix_refinement_get])
      apply (rule_tac P="P x" in prefix_refinement_assume_pre(1))
      apply (rule_tac P="Q y" in prefix_refinement_assume_pre(2))
      apply (rule prefix_refinement_put, simp)
     apply wp+
   apply clarsimp
  apply clarsimp
  done

lemmas pfx_refn_modifyT = prefix_refinement_modify[where P="\<top>" and Q="\<top>"]

lemmas prefix_refinement_get_pre
    = prefix_refinement_bind[OF prefix_refinement_get _
        valid_validI_wp[OF _ get_sp] valid_validI_wp[OF _ get_sp],
    simplified pred_conj_def no_trace_all, simplified]

lemma prefix_refinement_gets:
  "\<forall>s t. iosr s t \<and> P s \<and> Q t \<longrightarrow> rvr (f s) (f' t)
    \<Longrightarrow> prefix_refinement sr iosr iosr rvr (\<lambda>_. P) (\<lambda>_. Q) AR R (gets f) (gets f')"
  apply (simp add: gets_def)
  apply (rule prefix_refinement_get_pre)
  apply (rule prefix_refinement_return_imp)
  apply simp
  done

lemma prefix_refinement_fail:
  "prefix_refinement sr isr osr rvr \<top>\<top> \<top>\<top> AR R fail fail"
  apply (clarsimp simp: prefix_refinement_def fail_def)
  apply (rule default_prefix_refinement_ex)
  apply (simp add: is_matching_fragment_no_trace)
  done

lemma prefix_refinement_assert:
  "P = P' \<Longrightarrow> prefix_refinement sr iosr iosr \<top>\<top> \<top>\<top> \<top>\<top> AR R (assert P) (assert P')"
  by (simp add: assert_def prefix_refinement_fail prefix_refinement_return_imp)

lemma par_tr_fin_bind:
  "(\<forall>x. par_tr_fin_principle (g x)) \<Longrightarrow> par_tr_fin_principle (f >>= g)"
  apply (clarsimp simp: par_tr_fin_principle_def bind_def)
  apply (clarsimp split: tmres.split_asm)
  apply (fastforce simp: last_st_tr_def hd_append)
  done

lemma par_tr_fin_add_env_n_steps:
  "par_tr_fin_principle f
    \<Longrightarrow> par_tr_fin_principle (do x \<leftarrow> f; env_n_steps n od)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  define f' where "f' \<equiv> (do x \<leftarrow> f; env_n_steps n od)"
  from Suc have f': "par_tr_fin_principle f'"
    by (simp add: f'_def)

  hence "par_tr_fin_principle (do x \<leftarrow> f'; env_n_steps 1 od)"
    by (clarsimp simp: par_tr_fin_principle_def env_step_def
                       bind_def select_def get_def put_def length_Suc_conv
                       return_def put_trace_elem_def
                split: tmres.split_asm)

  then show ?case
    by (simp add: repeat_n_plus[where m="Suc 0", simplified, symmetric]
                     f'_def bind_assoc)
qed

lemma par_tr_fin_commit_step:
  "par_tr_fin_principle commit_step"
  by (simp add: par_tr_fin_principle_def commit_step_def
                bind_def get_def return_def put_trace_elem_def
         split: tmres.split)

lemma par_tr_fin_interference:
  "par_tr_fin_principle interference"
  apply (simp add: interference_def env_steps_repeat repeat_def select_early)
  apply (rule par_tr_fin_bind[rule_format])
  apply (rule par_tr_fin_add_env_n_steps)
  apply (rule par_tr_fin_commit_step)
  done

lemma prefix_refinement_triv_refinement_abs:
  "triv_refinement f f'
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q AR R f' g
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q AR R f g"
  apply (clarsimp simp: prefix_refinement_def)
  apply (strengthen triv_refinement_trans[mk_strg I E])
  apply fastforce
  done

lemma prefix_refinement_triv_refinement_conc:
  "prefix_refinement sr isr osr rvr P Q AR R f g'
    \<Longrightarrow> triv_refinement g' g
    \<Longrightarrow> prefix_refinement sr isr osr rvr P Q AR R f g"
  apply (clarsimp simp: prefix_refinement_def triv_refinement_def)
  apply blast
  done

lemmas prefix_refinement_triv_pre
    = Pure.asm_rl[where psi="prefix_refinement sr isr osr rvr
        (\<lambda>_ _. True) (\<lambda>_ _. True) AR R f g"] for sr isr osr rvr AR R f g

lemma prefix_refinement_mapM:
  "list_all2 xyr xs ys
    \<Longrightarrow> (\<forall>x y. x \<in> set xs \<longrightarrow> y \<in> set ys \<longrightarrow> xyr x y
        \<longrightarrow> prefix_refinement sr intsr intsr rvr P Q AR R (f x) (g y))
    \<Longrightarrow> (\<forall>x. x \<in> set xs \<longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>AR\<rbrace> f x \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>)
    \<Longrightarrow> (\<forall>y. y \<in> set ys \<longrightarrow> \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> g y \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>)
    \<Longrightarrow> prefix_refinement sr intsr intsr (list_all2 rvr) P Q AR R (mapM f xs) (mapM g ys)"
  apply (induct xs ys rule: list_all2_induct)
   apply (simp add: mapM_def sequence_def prefix_refinement_return_imp)
  apply (clarsimp simp add: mapM_Cons all_conj_distrib imp_conjR)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind, assumption)
      apply (rule prefix_refinement_bind, assumption)
        apply (rule prefix_refinement_triv_pre, rule prefix_refinement_return_imp, simp)
       apply (wp validI_triv)+
      apply (blast intro: validI_prefix_closed)
     apply (wp validI_triv | simp add: pred_conj_def
        | blast dest: validI_prefix_closed)+
  done

lemma prefix_refinement_weaken_rel:
  "prefix_refinement sr isr osr r P Q AR R f g
    \<Longrightarrow> \<forall>rv rv'. r rv rv' \<longrightarrow> r' rv rv'
    \<Longrightarrow> prefix_refinement sr isr osr r' P Q AR R f g"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule(5) prefix_refinementD, clarsimp)
  apply (rule exI, rule conjI[rotated], assumption)
  apply (clarsimp simp: is_matching_fragment_def)
  apply (drule(1) bspec, clarsimp)
  apply (erule tmres.rel_cases; clarsimp)
  done

lemma rely_cond_mono:
  "R \<le> R' \<Longrightarrow> rely_cond R \<le> rely_cond R'"
  by (simp add: le_fun_def rely_cond_def split_def)

lemma is_matching_fragment_add_rely:
  "is_matching_fragment sr osr r ctr cres s0 AR s f
    \<Longrightarrow> AR' \<le> AR
    \<Longrightarrow> is_matching_fragment sr osr r ctr cres s0 AR' s (rely f AR' s0)"
  apply (frule is_matching_fragment_Nil)
  apply (clarsimp simp: is_matching_fragment_def rely_prefix_closed
                        rely_self_closed)
  apply (intro conjI)
    apply (erule rely_env_closed)
    apply (frule rely_cond_mono)
    apply (simp add: le_fun_def rely_cond_Cons_eq)
   apply (fastforce simp: rely_def)
  apply (auto simp: rely_def)[1]
  done

lemma prefix_refinement_weaken_rely:
  "prefix_refinement sr isr osr r P Q AR R f g
    \<Longrightarrow> R' \<le> R \<Longrightarrow> AR' \<le> AR
    \<Longrightarrow> prefix_refinement sr isr osr r P Q AR' R' f g"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule(3) prefix_refinementD, assumption+)
  apply (clarsimp simp: rely_cond_def split_def le_fun_def)
  apply (rule exI, rule conjI, erule is_matching_fragment_add_rely)
   apply (simp add: le_fun_def)
  apply (auto simp add: triv_refinement_def rely_def)
  done

text \<open>Using prefix refinement as an in-place calculus, permitting
multiple applications at the same level.\<close>

lemmas trivial = imp_refl[rule_format]

lemma matching_tr_transp:
  "transp sr \<Longrightarrow> transp (matching_tr sr)"
  apply (simp add: matching_tr_def)
  apply (rule list.rel_transp)
  apply (rule transpI; clarsimp)
  apply (metis transp_def)
  done

lemma matching_tr_symp:
  "symp sr \<Longrightarrow> symp (matching_tr sr)"
  apply (simp add: matching_tr_def rel_prod_conv[symmetric])
  apply (intro list.rel_symp prod.rel_symp; simp?)
  apply (simp add: sympI)
  done

lemma list_all2_is_me:
  "list_all2 P tr tr'
    \<Longrightarrow> \<forall>x y. P x y \<longrightarrow> fst x = fst y
    \<Longrightarrow> (n < length tr \<and> fst (rev tr ! n) = Me)
        = (n < length tr' \<and> fst (rev tr' ! n) = Me)"
  apply (rule conj_cong, simp add: list_all2_lengthD)
  apply (frule list_all2_rev_nthD, simp add: list_all2_lengthD)
  apply (cases "rev tr ! n", cases "rev tr' ! n", auto)
  done

lemma is_matching_fragment_trans:
  assumes assms:
    "is_matching_fragment sr osr (=) h_tr h_res t0 R' t frag_g"
    "(g_tr, g_res) \<in> frag_g t" "length g_tr = length h_tr"
    "is_matching_fragment sr osr (=) g_tr g_res s0 R s frag_f"
  assumes sr: "equivp sr" "equivp osr"
  shows "is_matching_fragment sr osr (=) h_tr h_res s0 R s frag_f"
proof -
  have matching_tr1:
    "matching_tr sr (rev g_tr) (rev h_tr)"
    using assms
    by (auto simp: is_matching_fragment_def matching_tr_pfx_def)
  hence matching_tr:
    "\<And>n. matching_tr sr (take n (rev g_tr)) (take n (rev h_tr))"
    by (simp add: matching_tr_def)
  have matching:
    "\<And>xs. matching_tr_pfx sr xs g_tr = matching_tr_pfx sr xs h_tr"
    apply (rule equivpE, rule sr)
    apply (simp add: matching_tr_pfx_def assms)
    apply (rule conj_cong; simp?)
    apply (strengthen iffI)
    apply (metis matching_tr transpD[OF matching_tr_transp]
                 sympD[OF matching_tr_symp])
    done
  note is_me = matching_tr1[unfolded matching_tr_def, simplified,
    THEN list_all2_is_me, symmetric]
  show ?thesis using assms
    apply (clarsimp simp: is_matching_fragment_def matching is_me)
    apply (drule(1) bspec)+
    apply clarsimp
    apply (erule tmres.rel_cases | clarsimp)+
    apply (rule equivpE, rule sr(2))
    apply (metis transpD)
    done
qed

lemma matching_tr_rely_cond:
  "matching_tr sr (rev tr) (rev tr')
    \<Longrightarrow> rely_cond R s0 tr
    \<Longrightarrow> sr s0 t0
    \<Longrightarrow> rely_cond (\<lambda>t0 t. \<exists>s0 s. sr s0 t0 \<and> sr s t \<and> R s0 s) t0 tr'"
  apply (simp add: matching_tr_def)
  apply (induct arbitrary: s0 t0 rule: list_all2_induct)
   apply simp
  apply (clarsimp simp: rely_cond_def trace_steps_append last_st_tr_def hd_append)
  apply (intro conjI impI; clarsimp)
   apply blast
  apply (clarsimp simp: neq_Nil_conv list_all2_Cons2)
  apply blast
  done

lemma prefix_refinement_in_place_trans:
  "prefix_refinement sr isr osr (=) P (\<lambda>_ _. True) AR (\<lambda>t0 t. \<exists>s0 s. sr s0 t0 \<and> sr s t \<and> R s0 s) f g
    \<Longrightarrow> prefix_refinement sr isr osr (=) (\<lambda>_ _. True) Q AR R g h
    \<Longrightarrow> equivp sr \<Longrightarrow> equivp osr \<Longrightarrow> equivp isr
    \<Longrightarrow> (\<forall>s t t'. sr s t \<longrightarrow> R t t' \<longrightarrow> (\<exists>s'. sr s' t' \<and> AR s s'))
    \<Longrightarrow> prefix_refinement sr isr osr (=) P Q AR R f h"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule_tac s=t and t=t and ?t0.0=t0 and cprog=h in pfx_refnD;
      assumption?)
    apply (metis equivp_reflp_symp_transp reflpD)
   apply metis
  apply clarsimp
  apply (rename_tac h_tr h_res frag_g)
  apply (rule_tac x="\<lambda>s. \<Union>(tr, res) \<in> frag_g t \<inter> ({tr. length tr = length h_tr} \<times> UNIV).
    \<Union>frag_f \<in> {frag_f. is_matching_fragment sr osr (=) tr res s0 AR s frag_f
                \<and> triv_refinement f frag_f}. frag_f s" in exI)
  apply (rule conjI)
   apply (rule is_matching_fragment_UNION)
     apply clarsimp
     apply (rename_tac g_tr g_res)
     apply (rule is_matching_fragment_UNION)
       apply clarsimp
       apply (erule(1) is_matching_fragment_trans; simp)
      apply (clarsimp simp: is_matching_fragment_def)
     apply clarsimp
     apply (drule(1) triv_refinement_elemD)
     apply (frule(1) is_matching_fragment_trD)
     apply (clarsimp simp: matching_tr_pfx_def)
     apply (drule matching_tr_symp[THEN sympD, rotated], metis equivp_reflp_symp_transp)
     apply (drule(1) matching_tr_rely_cond)
      apply (erule equivp_reflp)
     apply (fastforce elim: pfx_refnD2)
    apply clarsimp
    apply (rule prefix_closed_UNION)
    apply (clarsimp simp: is_matching_fragment_def)
   apply (drule(2) matching_fragment_matching_tr, simp)
   apply (clarsimp simp: matching_tr_def dest!: list_all2_lengthD)
   apply blast
  apply (clarsimp simp: triv_refinement_def)
  apply blast
  done

lemma prefix_refinement_Await:
  "env_stable AR R sr iosr Q
    \<Longrightarrow> abs_rely_stable AR P
    \<Longrightarrow> \<forall>s t. P s \<longrightarrow> Q t \<longrightarrow> iosr s t \<longrightarrow> G' t \<longrightarrow> G s
    \<Longrightarrow> (\<exists>s. G' s) \<longrightarrow> (\<exists>s. G s)
    \<Longrightarrow> prefix_refinement sr iosr iosr (\<lambda>_ _. True) (\<lambda>s0 s. s0 = s \<and> P s)
                (\<lambda>t0 t. t0 = t \<and> Q t) AR R
            (Await G) (Await G')"
   apply (simp add: Await_redef)
   apply (rule prefix_refinement_weaken_pre)
     apply (rule prefix_refinement_bind[where intsr=iosr]
             prefix_refinement_select[where rvr="\<lambda>s s'. G s = G' s'"]
             prefix_refinement_env_steps
         | simp add: if_split[where P="\<lambda>S. x \<in> S" for x] split del: if_split
         | (rule prefix_refinement_get, rename_tac s s',
            rule_tac P="P s" in prefix_refinement_assume_pre(1),
            rule_tac P="Q s'" in prefix_refinement_assume_pre(2))
         |  (rule prefix_refinement_select[where rvr=dc2])
         | wp)+
   apply clarsimp
   apply (erule(2) abs_rely_stable_rtranclp)
  apply (clarsimp simp: env_stable_def)
  apply (erule(3) rely_stable_rtranclp)
  done

end
