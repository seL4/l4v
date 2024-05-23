(*
 * Copyright 2024, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory Prefix_Refinement

imports
  Monads.Trace_Empty_Fail
  Triv_Refinement
  Monads.Trace_Reader_Option
  Monads.Trace_Sat
begin

section \<open>Definition of prefix fragment refinement\<close>

text \<open>
  This is a notion of refinement/simulation making use of prefix closure.
  For a concrete program to refine an abstract program, for every
  trace of the concrete program there must exist a well-formed fragment
  of the abstract program that matches (according to the simulation
  relation) but which leaves enough decisions available to the abstract
  environment to permit parallel composition.\<close>

text \<open>
  Fragments must be self-closed, or enabled. Certain incomplete traces
  must be possible to extend by a program step.\<close>
definition self_closed :: "((tmid \<times> 's) list \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> bool" where
  "self_closed cond s f =
     (\<forall>xs. (xs, Incomplete) \<in> f s \<longrightarrow> cond xs \<longrightarrow> (\<exists>s'. (Me, s') # xs \<in> fst ` f s))"

lemmas self_closedD = self_closed_def[THEN iffD1, rule_format]

text \<open>
  Fragments must be environment-closed. Certain incomplete traces
  must be possible to extend by any environment step that is
  compatible with some condition.\<close>
definition env_closed :: "((tmid \<times> 's) list \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> bool" where
  "env_closed cond s f =
     (\<forall>xs s'. (xs, Incomplete) \<in> f s \<longrightarrow> cond xs s' \<longrightarrow> ((Env, s') # xs) \<in> fst ` f s)"

lemmas env_closedD = env_closed_def[THEN iffD1, rule_format]

lemma env_closed_strengthen_cond:
  "\<lbrakk>env_closed P s f; \<forall>xs s. Q xs s \<longrightarrow> P xs s\<rbrakk> \<Longrightarrow> env_closed Q s f"
  by (simp add: env_closed_def)

text \<open>Two traces match according to some state relation if they match at every step.\<close>
definition matching_tr :: "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> (tmid \<times> 't) list \<Rightarrow> bool" where
  "matching_tr sr = list_all2 (\<lambda>(aid, as) (cid, cs). aid = cid \<and> sr as cs)"

definition matching_tr_pfx ::
  "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> (tmid \<times> 's) list \<Rightarrow> (tmid \<times> 't) list \<Rightarrow> bool"
  where
  "matching_tr_pfx sr atr ctr =
     (length atr \<le> length ctr \<and> matching_tr sr (rev atr) (take (length atr) (rev ctr)))"

abbreviation
  "matching_tr_tmids_pfx \<equiv> matching_tr_pfx (\<lambda>_ _. True)"

abbreviation (input)
  "matching_self_cond ctr \<equiv> (\<lambda>xs. length xs < length ctr \<and> fst (rev ctr ! length xs) = Me)"

abbreviation (input)
  "matching_env_cond sr ctr s0 R \<equiv>
     (\<lambda>xs s. matching_tr_pfx sr ((Env, s) # xs) ctr \<and> rely_cond R s0 ((Env, s) # xs))"

text \<open>
  The collection of properties a fragment must have to match some concrete
  trace. It must be prefix, self and environment closed, nonempty, and all
  outcomes must be matching. The outcomes (trace and result) must match
  the rely condition, the concrete trace (or a prefix), and must either be
  a matching result or @{term Incomplete} if a prefix.\<close>
definition is_matching_fragment ::
  "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (tmid \<times> 't) list \<Rightarrow>
   ('t, 'b) tmres \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> ('s, 'a) tmonad \<Rightarrow> bool"
  where
  "is_matching_fragment sr osr rvr ctr cres s0 R s f
     = ((prefix_closed f
         \<and> self_closed (matching_self_cond ctr) s f
         \<and> env_closed (matching_env_cond sr ctr s0 R) s f)
        \<and> f s \<noteq> {}
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
    = is_matching_fragmentD[THEN conjunct2, THEN conjunct2, rule_format,
                            where x="(tr, res)" for tr res, simplified, rule_format]

text \<open>
  Prefix fragment refinement. Given the initial conditions, every concrete outcome
  (trace and result) must have a matching fragment which is a simple refinement of
  the abstract program.\<close>
\<comment> \<open>FIXME: do we want to be able to assume non-failure of the abstract program.\<close>
\<comment> \<open>FIXME: should we have an option for showing non-failure of the concrete program.\<close>
\<comment> \<open>FIXME: corres uses a set for the state relation, this uses a predicate. Do we care?\<close>
definition prefix_refinement ::
  "('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
   ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow>
   ('s, 'a) tmonad \<Rightarrow> ('t, 'b) tmonad \<Rightarrow> bool"
  where
  "prefix_refinement sr isr osr rvr AR R P Q aprog cprog
    = (\<forall>s s0 t0 t. isr s t \<longrightarrow> P s0 s \<longrightarrow> sr s0 t0 \<longrightarrow> Q t0 t
         \<longrightarrow> (\<forall>(ctr, cres) \<in> cprog t.
                rely_cond R t0 ctr \<longrightarrow>
                  (\<exists>f. is_matching_fragment sr osr rvr ctr cres s0 AR s f
                       \<and> triv_refinement aprog f)))"

abbreviation
  "pfx_refn sr \<equiv> prefix_refinement sr sr sr"

section \<open>Base case facts about refinement\<close>

lemmas prefix_refinementD = prefix_refinement_def[THEN iffD1, rule_format]
lemmas split_iffD1 = Product_Type.split[THEN iffD1]
lemmas pfx_refnD = prefix_refinementD
lemmas pfx_refnD2 = pfx_refnD[THEN split_iffD1[where a=tr and b=res for tr res], rule_format]

lemma prefix_refinement_False:
  "prefix_refinement sr isr osr rvr AR R P \<bottom>\<bottom> f g"
  by (clarsimp simp: prefix_refinement_def)

lemma prefix_refinement_False':
  "prefix_refinement sr isr osr rvr AR R \<bottom>\<bottom> Q f g"
  by (clarsimp simp: prefix_refinement_def)

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
  "\<lbrakk>rely_cond R s0 xs; xs \<noteq> []\<rbrakk>
   \<Longrightarrow> fst (hd xs) = Env \<longrightarrow> R (last_st_tr (tl xs) s0) (snd (hd xs))"
  by (clarsimp simp: rely_cond_def neq_Nil_conv trace_steps_append
              split: if_split_asm)

lemma rely_cond_nth:
  "\<lbrakk>rely_cond R s0 tr; n < length tr\<rbrakk>
   \<Longrightarrow> fst (rev tr ! n) = Env \<longrightarrow> R ((if n = 0 then s0 else snd (rev tr ! (n - 1)))) (snd (rev tr ! n))"
  by (simp add: rely_cond_def trace_steps_rev_drop_nth[where n=0, simplified])

lemma is_matching_fragment_Nil:
  "is_matching_fragment sr osr rvr ctr cres s0 R s f \<Longrightarrow> [] \<in> fst ` f s"
  apply (clarsimp simp: is_matching_fragment_def)
  apply (clarsimp simp only: set_eq_iff empty_iff simp_thms not_all)
  apply (drule(1) prefix_closed_drop[where tr=tr and n="length tr" for tr])
  apply (clarsimp simp: in_fst_snd_image)
  done

\<comment> \<open>FIXME: it would be good to show this but it needs more thought to determine how best to handle
          the case where the concrete function has failing traces that do not satisy the rely.
lemma prefix_refinement_propagate_no_fail:
  "\<lbrakk>prefix_refinement sr isr osr rvr AR R P Q f f';
    \<forall>s0. no_fail (P s0) f; \<forall>t0 t. Q t0 t \<longrightarrow> (\<exists>s0 s. P s0 s \<and> sr s0 t0 \<and> isr s t)\<rbrakk>
   \<Longrightarrow> \<forall>t0. no_fail (Q t0) f'"
  apply (clarsimp simp: prefix_refinement_def no_fail_def failed_def)
  apply (erule allE, erule allE, erule (1) impE)
  apply clarsimp
  apply ((drule spec)+, (drule (1) mp)+)
  apply (drule (1) bspec, clarsimp)
  oops\<close>

\<comment> \<open>FIXME: this needs some sort of assumption saying that the rely R does not lead to an empty set
          of results.
lemma prefix_refinement_serial:
  "\<lbrakk>prefix_refinement sr isr osr rvr AR R P Q f f'; empty_fail f'; no_fail Q' f';
    \<And>t0 t. Q t0 t \<Longrightarrow> Q' t\<rbrakk>
   \<Longrightarrow> \<forall>s0 s. (\<exists>t0 t. isr s t \<and> P s0 s \<and> sr s0 t0 \<and> Q t0 t) \<longrightarrow> mres (f s) \<noteq> {}"
  apply (clarsimp simp: prefix_refinement_def empty_fail_def)
  apply (drule no_failD, fastforce)
  apply (drule_tac x=t in spec, drule mp; simp?)
  apply ((drule spec)+, (drule (1) mp)+)
  apply (clarsimp simp: mres_def vimage_def)
  apply (drule (1) bspec)
  apply clarsimp
  oops\<close>

lemma is_matching_fragment_no_trace:
  "is_matching_fragment sr osr rvr [] cres s0 R s (\<lambda>s. {([], ares s)})
   = rel_tmres osr rvr (ares s) cres"
  by (simp add: is_matching_fragment_def prefix_closed_def self_closed_def env_closed_def
                matching_tr_pfx_def matching_tr_def)

\<comment> \<open>Singleton trace monads must have an empty trace to be prefix_closed\<close>
lemma prefix_refinement_singleton:
  "prefix_refinement sr isr osr rvr AR R P Q (\<lambda>s. {([], res s)}) (\<lambda>s. {([], cres s)})
   = (\<forall>s0 s t0 t. isr s t \<longrightarrow> P s0 s \<longrightarrow> sr s0 t0 \<longrightarrow> Q t0 t
          \<longrightarrow> rel_tmres osr rvr (res s) (cres t))"
  (is "prefix_refinement _ _ _ _ _ _ _ _ ?f _ = _")
  apply (rule iffI; clarsimp simp: prefix_refinement_def)
   apply ((drule spec)+, (drule (1) mp)+)
   apply clarsimp
   apply (subgoal_tac "f s = ?f s")
    prefer 2
    apply (clarsimp simp: triv_refinement_def fun_eq_iff)
    apply (drule_tac x=s in spec, drule subset_singletonD)
    apply (clarsimp simp: is_matching_fragment_def)
   apply (drule_tac tr="[]" and res="res s" in is_matching_fragment_trD)
    apply clarsimp
   apply clarsimp
  apply ((drule spec)+, (drule (1) mp)+)
  apply (rule_tac x="?f" in exI)
  apply (clarsimp simp: is_matching_fragment_no_trace)
  done

lemma prefix_refinement_no_trace:
  "no_trace g
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g
       = (\<forall>s0 s t0 t. isr s t \<longrightarrow> P s0 s \<longrightarrow> sr s0 t0 \<longrightarrow> Q t0 t
            \<longrightarrow> (\<forall>cres \<in> snd ` (g t). \<exists>(tr, res) \<in> (f s). tr = [] \<and> rel_tmres osr rvr res cres))"
  apply (rule iffI; clarsimp simp: prefix_refinement_def; drule (1) no_traceD; clarsimp)
   apply ((drule spec)+, (drule (1) mp)+)
   apply (drule (1) bspec, clarsimp)
   apply (frule_tac s=s in is_matching_fragment_defD)
   apply (clarsimp simp: ex_in_conv[symmetric])
   apply (drule (1) is_matching_fragment_trD)
   apply (clarsimp simp: matching_tr_pfx_def matching_tr_def)
   apply (drule (1) triv_refinement_elemD)
   apply (rule_tac x= "([], ba)" in bexI; clarsimp)
  apply ((drule spec)+, (drule (1) mp)+)
  apply (drule (1) bspec, clarsimp)
  apply (rename_tac gres fres)
  apply (rule_tac x="\<lambda>s'. if s'=s then {([],fres)} else {}" in exI)
  apply (auto simp: is_matching_fragment_def prefix_closed_def self_closed_def env_closed_def
                    matching_tr_pfx_def matching_tr_def triv_refinement_def)
  done

lemma prefix_refinement_no_trace':
  "\<lbrakk>no_trace g;
    \<And>s0 s t0 t. \<lbrakk>isr s t; P s0 s; sr s0 t0; Q t0 t\<rbrakk>
                \<Longrightarrow> (\<forall>cres \<in> snd ` (g t). \<exists>(tr, res) \<in> (f s). tr = [] \<and> rel_tmres osr rvr res cres)\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
  by (simp add: prefix_refinement_no_trace)

section \<open>Building blocks\<close>
text \<open>Prefix refinement rules for basic constructs.\<close>

lemma default_prefix_refinement_ex:
  "is_matching_fragment sr osr rvr ctr cres s0 R s
     (\<lambda>s. aprog s \<inter> ({tr'. length tr' \<le> length ctr} \<times> UNIV))
   \<Longrightarrow> \<exists>f. is_matching_fragment sr osr rvr ctr cres s0 R s f \<and> triv_refinement aprog f"
  apply (intro exI conjI, assumption)
  apply (simp add: triv_refinement_def)
  done

lemma default_prefix_refinement_ex_match_iosr_R:
  "is_matching_fragment sr osr rvr ctr cres s0 R s
     (rely (\<lambda>s. aprog s \<inter> ({tr'. matching_tr_pfx iosr tr' ctr} \<times> UNIV)) R s0)
   \<Longrightarrow> \<exists>f. is_matching_fragment sr osr rvr ctr cres s0 R s f \<and> triv_refinement aprog f"
  apply (intro exI conjI, assumption)
  apply (clarsimp simp: triv_refinement_def rely_def)
  done

lemma prefix_refinement_return_imp:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>P s0 s; Q t0 t; isr s t\<rbrakk> \<Longrightarrow> rvr rv rv' \<and> osr s t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q (return rv) (return rv')"
  apply (clarsimp simp: prefix_refinement_def)
  apply (rule default_prefix_refinement_ex)
  apply (clarsimp simp: return_def is_matching_fragment_no_trace)
  done

lemma prefix_refinement_get_imp:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>P s0 s; Q t0 t; isr s t\<rbrakk> \<Longrightarrow> rvr s t \<and> osr s t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q get get"
  apply (clarsimp simp: prefix_refinement_def)
  apply (rule default_prefix_refinement_ex)
  apply (clarsimp simp: get_def is_matching_fragment_no_trace)
  done

lemma prefix_refinement_gets_imp:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>P s0 s; Q t0 t; isr s t\<rbrakk> \<Longrightarrow> rvr (f s) (g t) \<and> osr s t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q (gets f) (gets g)"
  apply (clarsimp simp: prefix_refinement_def)
  apply (rule default_prefix_refinement_ex)
  apply (clarsimp simp: simpler_gets_def is_matching_fragment_no_trace)
  done

lemma prefix_refinement_returnOk_imp:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>P s0 s; Q t0 t; isr s t\<rbrakk> \<Longrightarrow> rvr (Inr rv) (Inr rv') \<and> osr s t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q (returnOk rv) (returnOk rv')"
  by (simp add: returnOk_def prefix_refinement_return_imp)

lemma prefix_refinement_throwError_imp:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>P s0 s; Q t0 t; isr s t\<rbrakk> \<Longrightarrow> rvr (Inl e) (Inl e') \<and> osr s t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q (throwError e) (throwError e')"
  by (simp add: throwError_def prefix_refinement_return_imp)


section \<open>Implications\<close>
text \<open>
  The notions of matching fragment and prefix refinement we have defined
  allow us to prove the existence of a matching trace in the abstract
  program.\<close>
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
  shows "\<exists>(atr, ares) \<in> f s. matching_tr sr atr ctr \<and> rel_tmres osr rvr ares cres"
  using matching_fragment_matching_tr[where R="\<lambda>_ _. True", OF match _ srx]
  by (auto simp: rely_cond_def sr)

theorem prefix_refinement_rely_cond_trD:
  assumes preds: "prefix_refinement sr isr osr rvr AR R P Q aprog cprog"
    "isr s t" "P s0 s" "Q t0 t" "(ctr, cres) \<in> cprog t"
    "rely_cond R t0 ctr" "sr s0 t0"
  and sr: "(\<forall>s t t'. sr s t \<longrightarrow> R t t' \<longrightarrow> (\<exists>s'. sr s' t' \<and> AR s s'))"
  shows "\<exists>(atr, ares) \<in> aprog s. matching_tr sr atr ctr
                    \<and> rel_tmres osr rvr ares cres
                    \<and> rely_cond AR s0 atr"
proof -
  obtain f where subs: "f s \<subseteq> aprog s"
      and match: "is_matching_fragment sr osr rvr ctr cres s0 AR s f"
    using prefix_refinementD[OF preds(1-3) _ preds(4-5)] preds(6-)
    by (auto simp add: triv_refinement_def)
  show ?thesis
    using matching_fragment_matching_tr[OF match _ _ sr] preds subs
    by blast
qed

section \<open>Using prefix refinement\<close>
text \<open>
  Using prefix refinement to map the validI Hoare quadruple
  (precond/rely/guarantee/postcond). Proofs of quadruples for
  abstract programs imply related quadruples for concrete
  programs.\<close>

lemma list_all2_all_trace_steps:
  assumes P: "\<forall>x\<in>trace_steps (rev tr) s0. P x"
  and lR': "list_all2 (\<lambda>(aid, as) (cid, cs). aid = cid \<and> R' as cs) tr tr'"
  and R': "R' s0 s0'"
  and Q: "\<forall>idn as1 as2 cs1 cs2. R' as1 cs1 \<longrightarrow> R' as2 cs2
            \<longrightarrow> P (idn, as1, as2) \<longrightarrow> Q (idn, cs1, cs2)"
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
  "\<lbrakk>prefix_refinement sr isr osr rvr AR R prP' prP f g;
    \<lbrace>P'\<rbrace>,\<lbrace>AR\<rbrace> f \<lbrace>G'\<rbrace>,\<lbrace>Q'\<rbrace>;
    \<And>t0 t. P t0 t \<Longrightarrow> (\<exists>s0 s. P' s0 s \<and> prP' s0 s \<and> prP t0 t \<and> isr s t \<and> sr s0 t0);
    \<And>s0 t0 t. \<lbrakk>sr s0 t0; R t0 t\<rbrakk> \<Longrightarrow> (\<exists>s. AR s0 s \<and> sr s t);
    \<And>s0 t0 s t. \<lbrakk>G' s0 s; sr s0 t0; sr s t\<rbrakk> \<Longrightarrow> G t0 t;
    \<And>rv rv' s0 t0 s t. \<lbrakk>Q' rv s0 s; sr s0 t0; osr s t; rvr rv rv'\<rbrakk> \<Longrightarrow> Q rv' t0 t; prefix_closed g\<rbrakk>
    \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (subst validI_def, clarsimp simp: rely_def)
  apply (drule meta_spec2, drule(1) meta_mp, clarsimp)
  apply (drule(6) prefix_refinement_rely_cond_trD[where AR=AR, simplified])
   apply blast
  apply clarsimp
  apply (rule conjI)
   apply (frule(3) validI_GD)
   apply (simp add: guar_cond_def matching_tr_def)
   apply (erule_tac R'="\<lambda>s cs. sr s cs" in list_all2_all_trace_steps)
     apply (clarsimp simp: list_all2_conv_all_nth split_def)
    apply simp
   apply clarsimp
  apply clarsimp
  apply (erule tmres.rel_cases; clarsimp)
  apply (drule(1) validI_rvD, simp add: rely_def)
   apply simp
  apply (case_tac tr; clarsimp simp: list_all2_Cons2 matching_tr_def)
  done

section \<open>Weakening rules\<close>

named_theorems pfx_refn_pre
(* Introduce schematic prefix_refinement guards; fail if already schematic *)
method pfx_refn_pre0 = WP_Pre.pre_tac pfx_refn_pre
(* Optionally introduce schematic prefix_refinement guards *)
method pfx_refn_pre = pfx_refn_pre0?

lemma stronger_prefix_refinement_weaken_pre[pfx_refn_pre]:
  "\<lbrakk>prefix_refinement sr isr osr rvr AR R P' Q' f g;
    \<And>s t s0 t0. \<lbrakk>isr s t; sr s0 t0; P s0 s; Q t0 t\<rbrakk> \<Longrightarrow> P' s0 s;
    \<And>s t s0 t0. \<lbrakk>isr s t; sr s0 t0; P s0 s; Q t0 t\<rbrakk> \<Longrightarrow> Q' t0 t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
 by (fastforce simp: prefix_refinement_def)

lemma prefix_refinement_weaken_pre:
  "\<lbrakk>prefix_refinement sr isr osr rvr AR R P' Q' f g;
    \<And>s s0. P s0 s \<Longrightarrow> P' s0 s; \<And>t t0. Q t0 t \<Longrightarrow> Q' t0 t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
  by pfx_refn_pre

lemma prefix_refinement_weaken_pre1:
  "\<lbrakk>prefix_refinement sr isr osr rvr AR R P' Q f g; \<And>s s0. P s0 s \<Longrightarrow> P' s0 s\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
  by pfx_refn_pre

lemma prefix_refinement_weaken_pre2:
  "\<lbrakk>prefix_refinement sr isr osr rvr AR R P Q' f g; \<And>t t0. Q t0 t \<Longrightarrow> Q' t0 t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
  by pfx_refn_pre

lemma prefix_refinement_weaken_srs:
  "\<lbrakk>prefix_refinement sr isr osr r AR R P Q f g; isr' \<le> isr; osr \<le> osr'; sr \<le> sr\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr' osr' r AR R P Q f g"
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

named_theorems pfx_refn_rvr_pre
(* Introduce schematic return value relation, fail if already schematic *)
method pfx_refn_rvr_pre = WP_Pre.pre_tac pfx_refn_rvr_pre

lemma prefix_refinement_weaken_rvr[pfx_refn_rvr_pre]:
  "\<lbrakk>prefix_refinement sr isr osr rvr AR R P Q f g; \<And>rv rv'. rvr rv rv' \<Longrightarrow> rvr' rv rv'\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr' AR R P Q f g"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule(5) prefix_refinementD, clarsimp)
  apply (rule exI, rule conjI[rotated], assumption)
  apply (clarsimp simp: is_matching_fragment_def)
  apply (drule(1) bspec, clarsimp)
  apply (erule tmres.rel_cases; clarsimp)
  done

lemma prefix_closed_rely:
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
  "\<lbrakk>env_closed P s f;
    \<And>xs s. \<lbrakk>P' xs s; rely_cond R s0 xs\<rbrakk> \<Longrightarrow> P xs s \<and> R (last_st_tr xs s0) s\<rbrakk>
   \<Longrightarrow> env_closed P' s (rely f R s0)"
  apply (subst env_closed_def, clarsimp simp: rely_def)
  apply (drule_tac s'=s' in env_closedD, assumption)
   apply simp
  apply (clarsimp simp: image_def)
  apply (fastforce intro: rely_cond_Cons rev_bexI)
  done

lemma rely_cond_mono:
  "R \<le> R' \<Longrightarrow> rely_cond R \<le> rely_cond R'"
  by (simp add: le_fun_def rely_cond_def split_def)

lemma is_matching_fragment_add_rely:
  "\<lbrakk>is_matching_fragment sr osr r ctr cres s0 AR s f; AR' \<le> AR\<rbrakk>
   \<Longrightarrow> is_matching_fragment sr osr r ctr cres s0 AR' s (rely f AR' s0)"
  apply (frule is_matching_fragment_Nil)
  apply (clarsimp simp: is_matching_fragment_def prefix_closed_rely
                        rely_self_closed)
  apply (intro conjI)
    apply (erule rely_env_closed)
    apply (frule rely_cond_mono)
    apply (simp add: le_fun_def rely_cond_Cons_eq)
   apply (fastforce simp: rely_def)
  apply (auto simp: rely_def)[1]
  done

named_theorems pfx_refn_rely_pre
(* Introduce schematic rely relations, fail if already schematic *)
method pfx_refn_rely_pre = WP_Pre.pre_tac pfx_refn_rely_pre

lemma prefix_refinement_weaken_rely[pfx_refn_rely_pre]:
  "\<lbrakk>prefix_refinement sr isr osr r AR R P Q f g; R' \<le> R; AR' \<le> AR\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr r AR' R' P Q f g"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule(3) prefix_refinementD, assumption+)
  apply (clarsimp simp: rely_cond_def split_def le_fun_def)
  apply (rule exI, rule conjI, erule is_matching_fragment_add_rely)
   apply (simp add: le_fun_def)
  apply (auto simp add: triv_refinement_def rely_def)
  done


section \<open>Inserting assumptions to be proved later\<close>

lemma prefix_refinement_req:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>sr s0 t0; isr s t; P s0 s; Q t0 t\<rbrakk> \<Longrightarrow> F;
    F \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
  by (auto simp: prefix_refinement_def)

lemma prefix_refinement_gen_asm:
  "\<lbrakk>P \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P' Q' f g\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R (P' and (\<lambda>_ _. P)) Q' f g"
  by (auto simp: prefix_refinement_def)

lemma prefix_refinement_gen_asm2:
  "\<lbrakk>P \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P' Q' f g\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P' (Q' and (\<lambda>_ _. P)) f g"
  by (auto simp: prefix_refinement_def)

lemmas prefix_refinement_gen_asms = prefix_refinement_gen_asm prefix_refinement_gen_asm2

lemma prefix_refinement_assume_pre:
  "\<lbrakk>\<And>s s0 t t0. \<lbrakk>isr s t; sr s0 t0; P s0 s; Q t0 t\<rbrakk> \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
  by (fastforce simp: prefix_refinement_def)

lemma prefix_refinement_name_pre:
  "\<lbrakk>\<And>s s0 t t0.
      \<lbrakk>isr s t; sr s0 t0; P s0 s; Q t0 t\<rbrakk>
      \<Longrightarrow> prefix_refinement sr isr osr rvr AR R
                            (\<lambda>s0' s'. s0' = s0 \<and> s' = s) (\<lambda>t0' t'. t0' = t0 \<and> t' = t) f g\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
  by (fastforce simp: prefix_refinement_def)


section \<open>Compositionality\<close>
text \<open>The crucial rules for proving prefix refinement of parallel and sequential compositions.\<close>

lemma ball_set_zip_conv_nth:
  "(\<forall>x \<in> set (zip ys zs). P x) = (\<forall>n. n < length ys \<longrightarrow> n < length zs \<longrightarrow> P (ys ! n, zs ! n))"
  by (auto simp: Ball_def in_set_zip)

definition par_tr_fin_principle :: "('s, unit) tmonad \<Rightarrow> bool" where
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
  "\<lbrakk>(tr, res) \<in> f s; is_matching_fragment sr osr rvr ctr cres s0 R s f;
    length tr < length ctr; fst (rev ctr ! length tr) = Env;
    sr s' (snd (rev ctr ! length tr)); R (last_st_tr tr s0) s'\<rbrakk>
   \<Longrightarrow> (Env, s') # tr \<in> fst ` f s"
  apply (frule(1) is_matching_fragment_trD, clarsimp)
  apply (erule(1) env_closedD[OF is_matching_fragment_env_closed])
  apply (clarsimp simp: matching_tr_pfx_aCons rely_cond_Cons_eq prod_eq_iff)
  done

lemma par_tr_fin_fragment:
  "\<lbrakk>par_tr_fin_principle f; (tr, res) \<in> f s; is_matching_fragment sr osr rvr ctr cres s0 R s f\<rbrakk>
   \<Longrightarrow> res = (case (length ctr - length tr, cres) of
                  (0, Failed) \<Rightarrow> Failed
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
  "\<lbrakk>par_tr_fin_principle f; par_tr_fin_principle g;
    is_matching_fragment sr osr rvr ctr1 cres s0 R s f;
    is_matching_fragment sr osr' rvr ctr2 cres s0 R' s g;
    length ctr1 = length ctr2;
    \<exists>f_steps res'. length f_steps = length tr
      \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then id else Env, s)) (zip f_steps tr), res) \<in> f s
      \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then Env else id, s)) (zip f_steps tr), res') \<in> g s\<rbrakk>
   \<Longrightarrow> (tr, res) \<in> parallel f g s"
  apply (clarsimp simp: parallel_def)
  apply (rule_tac x=f_steps in exI, clarsimp)
  apply (drule(2) par_tr_fin_fragment)+
  apply (simp only: list_all2_lengthD)
  apply (clarsimp split: nat.split_asm tmres.split_asm)
  apply (simp add: last_st_tr_def o_def split_def)
  done

lemma par_tr_fragment_parallel_def:
  "\<lbrakk>par_tr_fin_principle f; par_tr_fin_principle g;
    is_matching_fragment sr osr rvr ctr1 cres s0 R s f;
    is_matching_fragment sr osr' rvr ctr2 cres s0 R' s g;
    length ctr1 = length ctr2\<rbrakk>
   \<Longrightarrow> parallel f g s = {(tr, res). \<exists>f_steps res'. length f_steps = length tr
       \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then id else Env, s)) (zip f_steps tr), res) \<in> f s
       \<and> (map (\<lambda>(f_step, (id, s)). (if f_step then Env else id, s)) (zip f_steps tr), res') \<in> g s}"
  apply (rule equalityI; clarsimp)
   apply (auto simp: parallel_def)[1]
  apply (erule(4) par_tr_fragment_in_parallel)
  apply blast
  done

lemmas list_all2_rev_nthD = list_all2_nthD[OF list_all2_rev[THEN iffD2], simplified]

definition forward_enabled :: "'s rg_pred \<Rightarrow> bool" where
  "forward_enabled P = (\<forall>s_pre. \<exists>s. P s_pre s)"

lemmas forward_enabledD = forward_enabled_def[THEN iffD1, rule_format]

lemma forward_enabled_mono:
  "\<lbrakk>P \<le> Q; forward_enabled P\<rbrakk> \<Longrightarrow> forward_enabled Q"
  by (fastforce simp: forward_enabled_def le_fun_def)

lemma forward_enabled_reflp:
  "reflp P \<Longrightarrow> forward_enabled P"
  by (auto simp: reflp_def forward_enabled_def)

lemma par_tr_fin_principle_triv_refinement:
  "\<lbrakk>par_tr_fin_principle aprog; triv_refinement aprog cprog\<rbrakk>
   \<Longrightarrow> par_tr_fin_principle cprog"
  by (fastforce simp: par_tr_fin_principle_def triv_refinement_def)

lemma matching_tr_pfx_parallel_zip:
  "\<lbrakk>matching_tr_pfx sr a_pfx a_tr; matching_tr_pfx sr b_pfx b_tr;
    length a_pfx = length b_pfx;
    list_all2 (\<lambda>y z. (fst y = Env \<or> fst z = Env) \<and> snd y = snd z) a_tr b_tr\<rbrakk>
   \<Longrightarrow> matching_tr_pfx sr (map parallel_mrg (zip a_pfx b_pfx)) (map parallel_mrg (zip a_tr b_tr))"
  apply (clarsimp simp: matching_tr_pfx_def matching_tr_def list_all2_lengthD)
  apply (clarsimp simp: list_all2_conv_all_nth)
  apply (clarsimp simp: rev_map split_def zip_rev[symmetric])
  done

lemma drop_sub_Suc_is_Cons:
  "\<lbrakk>n = length xs; m < length xs\<rbrakk> \<Longrightarrow> drop (n - Suc m) xs = (rev xs ! m) # drop (n - m) xs"
  apply (rule nth_equalityI; clarsimp)
  apply (clarsimp simp: nth_Cons' rev_nth)
  done

lemmas rely_cond_append_split =
  rely_cond_append[where xs="take n xs" and ys="drop n xs" for n xs, simplified]
lemmas guar_cond_append_split =
  guar_cond_append[where xs="take n xs" and ys="drop n xs" for n xs, simplified]

lemma validI_drop_next_G:
  "\<lbrakk>\<lbrace>P\<rbrace>, \<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>, \<lbrace>Q\<rbrace>; P s0 s; (tr, res) \<in> f s; rely_cond R s0 (drop (n - m) tr);
    n = length tr; m < length tr\<rbrakk>
   \<Longrightarrow> fst (rev tr ! m) \<noteq> Env \<longrightarrow> G (last_st_tr (rev (take m (rev tr))) s0) (snd (rev tr ! m))"
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
  "\<lbrakk>is_matching_fragment sr osr rvr ctr1 cres1 s0 (E or Gg) s f;
    is_matching_fragment sr osr' rvr ctr2 cres2 s0 (E or Gf) s g;
    par_tr_fin_principle f; par_tr_fin_principle g;
    cres1 = cres2; length ctr1 = length ctr2;
    \<forall>s xs. Q xs s \<longrightarrow> (sr s (snd (rev ctr1 ! length xs)))
      \<and> (sr s (snd (rev ctr2 ! length xs)))
      \<and> length xs < length ctr2
      \<and> fst (rev ctr1 ! length xs) = Env
      \<and> fst (rev ctr2 ! length xs) = Env
      \<and> E (last_st_tr xs s0) s\<rbrakk>
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
  "\<lbrakk>is_matching_fragment sr osr rvr ctr1 cres1 s0 (E or Gg) s f;
    is_matching_fragment sr osr' rvr ctr2 cres2 s0 (E or Gf) s g;
    par_tr_fin_principle f; par_tr_fin_principle g;
    list_all2 (\<lambda>y z. (fst y = Env \<or> fst z = Env) \<and> snd y = snd z) ctr1 ctr2;
    \<lbrace>P\<rbrace>,\<lbrace>E or Gg\<rbrace> f \<lbrace>Gf\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>; \<lbrace>P\<rbrace>,\<lbrace>E or Gf\<rbrace> g \<lbrace>Gg\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>;
    P s0 s; cres1 = cres2;
    Q = (\<lambda>xs. length xs < length ctr1 \<and> (fst (rev ctr1 ! length xs) \<noteq> Env
              \<or> fst (rev ctr2 ! length xs) \<noteq> Env))\<rbrakk>
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
  "\<lbrakk>is_matching_fragment sr osr rvr b_tr bd_res s0 R s f; triv_refinement g f;
    G = \<top>\<top> \<or> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>R\<rbrace> f \<lbrace>G\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>"
  apply (frule is_matching_fragment_prefix_closed)
  apply (erule disjE)
   apply wpsimp
  apply (erule(2) validI_triv_refinement)
  done

theorem prefix_refinement_parallel:
  "\<lbrakk>prefix_refinement sr isr osr rvr (AE or Gc) (E or Gd) P Q a b;
    prefix_refinement sr isr osr rvr (AE or Ga) (E or Gb) P Q c d;
    par_tr_fin_principle a; par_tr_fin_principle c;
    \<lbrace>Q\<rbrace>,\<lbrace>E or Gd\<rbrace> b \<lbrace>Gb\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>; \<lbrace>Q\<rbrace>,\<lbrace>E or Gb\<rbrace> d \<lbrace>Gd\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>;
    (Ga = \<top>\<top> \<and> Gc = \<top>\<top>)
    \<or> (\<lbrace>P\<rbrace>,\<lbrace>AE or Gc\<rbrace> a \<lbrace>Ga\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace> \<and> \<lbrace>P\<rbrace>,\<lbrace>AE or Ga\<rbrace> c \<lbrace>Gc\<rbrace>,\<lbrace>\<lambda>_ _ _. True\<rbrace>)\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AE E P Q (parallel a c) (parallel b d)"
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
  apply (intro conjI prefix_closed_parallel prefix_closed_rely rely_self_closed,
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

lemmas prefix_refinement_parallel_ART
  = prefix_refinement_parallel[OF _ _ _ _ _ _ disjI1[OF conjI, OF refl refl]]
lemmas prefix_refinement_parallel_triv
  = prefix_refinement_parallel_ART[where Gb="\<top>\<top>" and Gd="\<top>\<top>", simplified]
lemmas prefix_refinement_parallel'
  = prefix_refinement_parallel[OF _ _ _ _ _ _ disjI2[OF conjI]]

lemma pfx_trace_set_allD:
  "\<lbrakk>\<forall>n. \<forall>v\<in>set (take n xs). P n v; v \<in> set (take n xs)\<rbrakk> \<Longrightarrow> P n v"
  by simp

lemma prefix_closed_UNION:
  "\<lbrakk>\<forall>s' x. x \<in> S s' \<longrightarrow> prefix_closed (f x)\<rbrakk> \<Longrightarrow> prefix_closed (\<lambda>s. \<Union>x \<in> S s. f x s)"
  apply (simp add: prefix_closed_def)
  apply (blast intro: in_fst_snd_image)
  done

lemma is_matching_fragment_UNION:
  "\<lbrakk>\<forall>x. x \<in> S s \<longrightarrow> is_matching_fragment sr osr rvr ctr cres s0 R s (f x);
    \<forall>s' x. x \<in> S s' \<longrightarrow> prefix_closed (f x); S s \<noteq> {}\<rbrakk>
   \<Longrightarrow> is_matching_fragment sr osr rvr ctr cres s0 R s (\<lambda>s. \<Union>x \<in> S s. f x s)"
  apply (clarsimp simp: is_matching_fragment_def prefix_closed_UNION)
  apply (intro conjI impI)
   apply (clarsimp simp: self_closed_def split_def in_fst_snd_image_eq)
   apply blast
  apply (clarsimp simp: env_closed_def split_def in_fst_snd_image_eq)
  apply blast
  done

\<comment> \<open>
  This is a variant of @{term Trace_Monad.bind}, that is used to build up the fragment required
  for proving @{text prefix_refinement_bind_general}.\<close>
definition mbind ::
  "('s, 'a) tmonad \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> ('s, 'b) tmonad) \<Rightarrow> 's \<Rightarrow> ('s, 'b) tmonad"
  where
  "mbind f g s0 \<equiv> \<lambda>s. \<Union>(xs, r) \<in> (f s).
     case r of
         Failed \<Rightarrow> {(xs, Failed)}
       | Incomplete \<Rightarrow> {(xs, Incomplete)}
       | Result (rv, s) \<Rightarrow> fst_upd (\<lambda>ys. ys @ xs) ` g (last_st_tr xs s0) rv s"

lemma self_closed_mbind:
  "\<lbrakk>is_matching_fragment sr osr rvr ctr cres s0 R s f;
    \<forall>tr x s'. (tr, Result (x, s')) \<in> f s
      \<longrightarrow> self_closed (\<lambda>xs. length xs < length ctr' \<and> fst (rev ctr' ! length xs) = Me) s'
                      (g (last_st_tr tr s0) x)
          \<and> [] \<in> fst ` g (last_st_tr tr s0) x s';
    Q = matching_self_cond (ctr' @ ctr); cres = Incomplete \<longrightarrow> ctr' = []\<rbrakk>
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
    "\<lbrakk>matching_tr_pfx sr xs ys; length xs \<le> length ys \<longrightarrow> drop N ys' = ys\<rbrakk>
     \<Longrightarrow> matching_tr_pfx sr xs ys'"
  apply (clarsimp simp: matching_tr_pfx_def)
  apply (rule context_conjI)
   apply simp
  apply (simp add: matching_tr_def list_all2_conv_all_nth min_def)
  apply (clarsimp simp: rev_nth)
  done

lemma matching_tr_pfx_rhs_is_drop:
  fixes ys ys'
  defines "N == length ys - length ys'"
  shows
    "\<lbrakk>matching_tr_pfx sr xs ys; drop N ys = ys'; length xs \<le> length ys'\<rbrakk>
     \<Longrightarrow> matching_tr_pfx sr xs ys'"
  apply (clarsimp simp: matching_tr_pfx_def)
  apply (simp add: matching_tr_def list_all2_conv_all_nth min_def)
  apply (clarsimp simp: rev_nth)
  done

lemma env_closed_mbind:
  "\<lbrakk>is_matching_fragment sr osr rvr ctr' cres s0 R s f;
    \<forall>tr x s'. (tr, Result (x, s')) \<in> f s
      \<longrightarrow> env_closed (matching_env_cond sr ctr'' (last_st_tr tr s0) R) s' (g (last_st_tr tr s0) x)
          \<and> [] \<in> fst ` g (last_st_tr tr s0) x s';
    if cres \<in> {Incomplete, Failed} then ctr = ctr' else ctr = ctr'' @ ctr';
    Q = matching_env_cond sr ctr s0 R\<rbrakk>
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

lemma prefix_closed_mbind:
  "\<lbrakk>prefix_closed f; \<forall>tr x s' s. (tr, Result (x, s')) \<in> f s \<longrightarrow> prefix_closed (g (last_st_tr tr s0) x)\<rbrakk>
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
  "\<lbrakk>is_matching_fragment sr intsr rvr ctr cres s0 R s f_a;
    \<forall>tr x s'. (tr, Result (x, s')) \<in> f_a s
      \<longrightarrow> is_matching_fragment sr osr rvr' ctr' cres' (last_st_tr tr s0) R s' (f_b (last_st_tr tr s0) x);
    \<forall>s0' x. prefix_closed (f_b s0' x);
    ctr'' = ctr' @ ctr;
    cres'' = (case cres of Failed \<Rightarrow> Failed | Incomplete \<Rightarrow> Incomplete | _ \<Rightarrow> cres');
    (cres = Incomplete \<or> cres = Failed) \<longrightarrow> ctr' = []\<rbrakk>
   \<Longrightarrow> is_matching_fragment sr osr rvr' ctr'' cres'' s0 R s (mbind f_a f_b s0)"
  apply (subst is_matching_fragment_def, clarsimp)
  apply (strengthen env_closed_mbind[where ctr''=ctr', mk_strg I E]
                    prefix_closed_mbind
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
  "\<lbrakk>is_matching_fragment sr intsr rvr ctr cres s0 R s f_a;
    ctr'' = ctr' @ ctr;
    cres'' = (case cres of Failed \<Rightarrow> Failed | Incomplete \<Rightarrow> Incomplete | _ \<Rightarrow> cres');
    cres = Incomplete \<or> cres = Failed \<longrightarrow> ctr' = [];
    \<forall>tr x s'. (tr, Result (x, s')) \<in> f_a s
        \<longrightarrow> (\<exists>f. is_matching_fragment sr osr rvr' ctr' cres' (last_st_tr tr s0) R s' f
                \<and> triv_refinement (aprog x) f)\<rbrakk>
   \<Longrightarrow> is_matching_fragment sr osr rvr' ctr'' cres'' s0 R s
         (mbind f_a
            (\<lambda>s0' rv s. \<Union>f \<in> {f. is_matching_fragment sr osr rvr' ctr' cres' s0' R s f
                                  \<and> triv_refinement (aprog rv) f}. f s)
            s0)"
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
  "\<lbrakk>is_matching_fragment sr osr rvr ctr cres s0 R s f; (x, s') \<in> mres (f s)\<rbrakk>
   \<Longrightarrow> \<exists>y s''. cres = Result (y, s'') \<and> osr s' s'' \<and> rvr x y"
  apply (clarsimp simp: mres_def)
  apply (frule(1) is_matching_fragment_trD)
  apply (clarsimp simp: matching_tr_pfx_def)
  apply (erule tmres.rel_cases; clarsimp)
  done

lemma matching_tr_pfx_sr_hd_append:
  "\<lbrakk>matching_tr_pfx sr tr tr'; sr s0 t0; length tr \<ge> length tr'\<rbrakk>
   \<Longrightarrow> sr (hd (map snd tr @ [s0])) (hd (map snd tr' @ [t0]))"
  apply (clarsimp simp: matching_tr_pfx_def matching_tr_def)
  apply (erule list.rel_cases; clarsimp)
  done

lemma matching_tr_pfx_last_st_tr:
  "\<lbrakk>matching_tr_pfx sr tr tr'; sr s0 t0; length tr \<ge> length tr'\<rbrakk>
   \<Longrightarrow> sr (last_st_tr tr s0) (last_st_tr tr' t0)"
  apply (clarsimp simp: matching_tr_pfx_def matching_tr_def)
  apply (erule list.rel_cases; clarsimp)
  done

\<comment> \<open>FIXME: do we want to follow the corres naming pattern and use split instead of bind?\<close>
theorem prefix_refinement_bind_general:
  "\<lbrakk>prefix_refinement sr isr intsr rvr' AR R P Q a c;
    \<And>rv rv'. rvr' rv rv' \<Longrightarrow> prefix_refinement sr intsr osr rvr AR R (P'' rv) (Q'' rv') (b rv) (d rv');
    \<lbrace>P'\<rbrace>,\<lbrace>AR\<rbrace> a \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>P''\<rbrace> \<or> \<lbrace>\<lambda>s. \<exists>s0. P' s0 s\<rbrace> a \<lbrace>\<lambda>rv s. \<forall>s0. P'' rv s0 s\<rbrace>;
    \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>Q''\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R (P and P') (Q and Q') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
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
             in is_matching_fragment_mbind,
           assumption, simp_all add: prefix_closed_def)[1]
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

section \<open>Derivative splitting rules\<close>

lemma prefix_refinement_bind_v:
  "\<lbrakk>prefix_refinement sr isr intsr rvr' AR R P Q a c;
    \<And>rv rv'. rvr' rv rv' \<Longrightarrow> prefix_refinement sr intsr osr rvr AR R (\<lambda>_. P'' rv) (Q'' rv') (b rv) (d rv');
    \<lbrace>P'\<rbrace> a \<lbrace>P''\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>Q''\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R (\<lambda>s0. P s0 and P') (Q and Q') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  apply (rule prefix_refinement_weaken_pre,
         rule prefix_refinement_bind_general[where P'="\<lambda>_. P'"])
       apply assumption
      apply (elim meta_allE, erule(1) meta_mp)
     apply (rule disjI2)
     apply simp
    apply assumption
   apply clarsimp
  apply clarsimp
  done

lemmas prefix_refinement_bind = prefix_refinement_bind_general[OF _ _ disjI1]

lemmas prefix_refinement_bind_sr = prefix_refinement_bind[where sr=sr and intsr=sr for sr]
lemmas prefix_refinement_bind_isr = prefix_refinement_bind[where isr=isr and intsr=isr for isr]
lemmas pfx_refn_bind =
  prefix_refinement_bind_v[where sr=sr and isr=sr and osr=sr and intsr=sr for sr]
lemmas pfx_refn_bindT =
  pfx_refn_bind[where P'="\<top>" and Q'="\<lambda>_ _. True", OF _ _ hoare_post_taut twp_post_taut,
                simplified pred_conj_def, simplified]

\<comment> \<open>FIXME: these are copied from Corres_UL.thy, move somewhere that they can be shared\<close>
primrec rel_sum_comb ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a + 'c \<Rightarrow> 'b + 'd \<Rightarrow> bool)" (infixl "\<oplus>" 95)
  where
    "(f \<oplus> g) (Inr x) y = (\<exists>y'. y = Inr y' \<and> (g x y'))"
  | "(f \<oplus> g) (Inl x) y = (\<exists>y'. y = Inl y' \<and> (f x y'))"

lemma rel_sum_comb_r2[simp]:
  "(f \<oplus> g) x (Inr y) = (\<exists>x'. x = Inr x' \<and> g x' y)"
  apply (case_tac x, simp_all)
  done

lemma rel_sum_comb_l2[simp]:
  "(f \<oplus> g) x (Inl y) = (\<exists>x'. x = Inl x' \<and> f x' y)"
  apply (case_tac x, simp_all)
  done

lemma prefix_refinement_bindE_general:
  "\<lbrakk>prefix_refinement sr isr intsr (f \<oplus> rvr') AR R P Q a c;
    \<And>rv rv'. rvr' rv rv' \<Longrightarrow> prefix_refinement sr intsr osr (f \<oplus> rvr) AR R (P'' rv) (Q'' rv') (b rv) (d rv');
    \<lbrace>P'\<rbrace>,\<lbrace>AR\<rbrace> a \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>P''\<rbrace>,\<lbrace>E\<rbrace> \<or> \<lbrace>\<lambda>s. \<exists>s0. P' s0 s\<rbrace> a \<lbrace>\<lambda>rv s. \<forall>s0. P'' rv s0 s\<rbrace>,\<lbrace>\<lambda>rv s. \<forall>s0. E rv s0 s\<rbrace>;
    \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>Q''\<rbrace>,\<lbrace>E'\<rbrace>;
    \<And>rv s0 s rv' t0 t. \<lbrakk>E rv s0 s; E' rv' t0 t; intsr s t\<rbrakk> \<Longrightarrow> osr s t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr (f \<oplus> rvr) AR R (P and P') (Q and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E (\<lambda>rv'. d rv'))"
  apply (unfold bindE_def validIE_def validE_def)
  apply (erule prefix_refinement_bind_general)
    defer
    apply (erule disj_forward; assumption?)
    apply (fastforce simp: valid_def split_def split: sum.splits)
   apply assumption
  apply (case_tac rv; clarsimp simp: lift_def)
  apply (rule prefix_refinement_throwError_imp)
  apply clarsimp
  done

lemma prefix_refinement_bindE_v:
  "\<lbrakk>prefix_refinement sr isr intsr (f \<oplus> rvr') AR R P Q a c;
    \<And>rv rv'. rvr' rv rv' \<Longrightarrow> prefix_refinement sr intsr osr (f \<oplus> rvr) AR R (\<lambda>_. P'' rv) (Q'' rv') (b rv) (d rv');
    \<lbrace>P'\<rbrace> a \<lbrace>P''\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>Q''\<rbrace>,\<lbrace>E'\<rbrace>;
    \<And>rv s rv' t0 t. \<lbrakk>E rv s; E' rv' t0 t; intsr s t\<rbrakk> \<Longrightarrow> osr s t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr (f \<oplus> rvr) AR R (\<lambda>s0. P s0 and P') (Q and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E (\<lambda>rv'. d rv'))"
  apply (rule prefix_refinement_weaken_pre,
         rule prefix_refinement_bindE_general[where P'="\<lambda>_. P'"and E="\<lambda>rv _. E rv"])
        apply assumption
       apply (elim meta_allE, erule(1) meta_mp)
      apply (rule disjI2)
      apply simp
     apply assumption
    apply clarsimp
   apply clarsimp
  apply clarsimp
  done

lemmas prefix_refinement_bindE = prefix_refinement_bindE_general[OF _ _ disjI1]

lemmas prefix_refinement_bindE_sr = prefix_refinement_bindE[where sr=sr and intsr=sr for sr]
lemmas prefix_refinement_bindE_isr = prefix_refinement_bindE[where isr=isr and intsr=isr for isr]
lemmas pfx_refn_bindE =
  prefix_refinement_bindE_v[where sr=sr and isr=sr and osr=sr and intsr=sr for sr, where E="\<top>\<top>" and E'="\<top>\<top>\<top>",
                            atomized, simplified, rule_format] (*this sequence of attributes removes a trivial assumption*)
lemmas pfx_refn_bindET =
  pfx_refn_bindE[where P'="\<top>" and Q'="\<lambda>_ _. True", OF _ _ hoareE_TrueI twp_post_tautE,
                simplified pred_conj_def, simplified]

lemma prefix_refinement_handle:
  "\<lbrakk>prefix_refinement sr isr osr (rvr'' \<oplus> rvr) AR R P Q a c;
    \<And>ft ft'. rvr'' ft ft' \<Longrightarrow> prefix_refinement sr osr osr (rvr' \<oplus> rvr) AR R (E ft) (E' ft') (b ft) (d ft');
    \<lbrace>P'\<rbrace>,\<lbrace>AR\<rbrace> a -,-,\<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> c -, -,\<lbrace>E'\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr (rvr' \<oplus> rvr) AR R (P and P') (Q and Q') (a <handle> (\<lambda>ft. b ft)) (c <handle> (\<lambda>ft'. d ft'))"
  apply (simp add: handleE_def handleE'_def validIE_def)
  apply (erule prefix_refinement_bind)
    defer
    apply assumption+
  apply (case_tac v; clarsimp)
  apply (rule prefix_refinement_return_imp)
  apply clarsimp
  done

lemma prefix_refinement_catch:
  "\<lbrakk>prefix_refinement sr isr osr (rvr' \<oplus> rvr) AR R P Q a c;
    \<And>ft ft'. rvr' ft ft' \<Longrightarrow> prefix_refinement sr osr osr rvr AR R (E ft) (E' ft') (b ft) (d ft');
    \<lbrace>P'\<rbrace>,\<lbrace>AR\<rbrace> a -,-,\<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> c -, -,\<lbrace>E'\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R (P and P') (Q and Q') (a <catch> (\<lambda>ft. b ft)) (c <catch> (\<lambda>ft'. d ft'))"
  apply (simp add: catch_def validIE_def)
  apply (erule prefix_refinement_bind)
    defer
    apply assumption+
  apply (case_tac x; clarsimp)
  apply (rule prefix_refinement_return_imp)
  apply clarsimp
  done

lemma prefix_refinement_handle_elseE:
  "\<lbrakk>prefix_refinement sr isr osr (fr' \<oplus> rvr') AR R P Q a c;
    \<And>ft ft'. fr' ft ft' \<Longrightarrow> prefix_refinement sr osr osr (fr \<oplus> rvr) AR R (E ft) (E' ft') (b ft) (d ft');
    \<And>rv rv'. rvr' rv rv' \<Longrightarrow> prefix_refinement sr osr osr (fr \<oplus> rvr) AR R (P'' rv) (Q'' rv') (f rv) (g rv');
    \<lbrace>P'\<rbrace>,\<lbrace>AR\<rbrace> a -,\<lbrace>P''\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace>,\<lbrace>R\<rbrace> c -, \<lbrace>Q''\<rbrace>,\<lbrace>E'\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr (fr \<oplus> rvr) AR R (P and P') (Q and Q')
                         (a <handle> (\<lambda>ft. b ft) <else> (\<lambda>rv. f rv)) (c <handle> (\<lambda>ft'. d ft') <else> (\<lambda>rv. g rv))"
  apply (simp add: handle_elseE_def validIE_def)
  apply (erule prefix_refinement_bind)
    defer
    apply assumption+
  apply (case_tac v; clarsimp)
  done

lemmas prefix_refinement_bind_eqr = prefix_refinement_bind[where rvr'="(=)", simplified]
lemmas prefix_refinement_bind_eqrE = prefix_refinement_bindE[where rvr'="(=)", simplified]

\<comment> \<open>FIXME: these are copied from Corres_UL.thy, move somewhere that they can be shared\<close>
definition
 "dc \<equiv> \<lambda>rv rv'. True"

lemma dc_simp[simp]: "dc a b"
  by (simp add: dc_def)

lemma dc_o_simp1[simp]: "dc \<circ> f = dc"
  by (simp add: dc_def o_def)

lemma dc_o_simp2[simp]: "dc x \<circ> f = dc x"
  by (simp add: dc_def o_def)

lemma unit_dc_is_eq:
  "(dc::unit\<Rightarrow>_\<Rightarrow>_) = (=)"
  by (fastforce simp: dc_def)

lemma prefix_refinement_bind_nor:
  "\<lbrakk>prefix_refinement sr isr intsr dc AR R P Q a c;
    prefix_refinement sr intsr osr rvr AR R P'' Q'' b d;
    \<lbrace>P'\<rbrace>, \<lbrace>AR\<rbrace> a -, \<lbrace>\<lambda>_. P''\<rbrace>; \<lbrace>Q'\<rbrace>, \<lbrace>R\<rbrace> c -, \<lbrace>\<lambda>_. Q''\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R (P and P') (Q and Q') (a >>= (\<lambda>_. b)) (c >>= (\<lambda>_. d))"
  by (rule prefix_refinement_bind; assumption)

lemma prefix_refinement_bind_norE:
  "\<lbrakk>prefix_refinement sr isr intsr (f \<oplus> dc) AR R P Q a c;
    prefix_refinement sr intsr osr (f \<oplus> rvr) AR R P'' Q'' b d;
    \<lbrace>P'\<rbrace>, \<lbrace>AR\<rbrace> a -, \<lbrace>\<lambda>_. P''\<rbrace>, \<lbrace>E\<rbrace>; \<lbrace>Q'\<rbrace>, \<lbrace>R\<rbrace> c -, \<lbrace>\<lambda>_. Q''\<rbrace>, \<lbrace>E'\<rbrace>;
    \<And>rv s0 s rv' t0 t. \<lbrakk>E rv s0 s; E' rv' t0 t; intsr s t\<rbrakk> \<Longrightarrow> osr s t\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr (f \<oplus> rvr) AR R (P and P') (Q and Q') (a >>=E (\<lambda>_. b)) (c >>=E (\<lambda>_. d))"
  by (rule prefix_refinement_bindE; assumption)

lemmas prefix_refinement_bind_mapr = prefix_refinement_bind[where rvr'="(=) \<circ> g" for g, simplified]
lemmas prefix_refinement_bind_maprE = prefix_refinement_bindE[where rvr'="(=) \<circ> g" for g, simplified]


section \<open>Rules for walking prefix refinement into basic constructs\<close>

lemma prefix_refinement_if:
  "\<lbrakk>G = G'; prefix_refinement sr isr osr rvr AR R P Q a c;
    prefix_refinement sr isr osr rvr AR R P' Q' b d \<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R
               (if G then P else P') (if G' then Q else Q')
               (if G then a else b) (if G' then c else d)"
  by simp

\<comment> \<open>FIXME: copied from Word_Lib.Many_More, where would be a good spot to put it?\<close>
lemma if_apply_def2:
  "(if P then F else G) = (\<lambda>x y. (P \<longrightarrow> F x y) \<and> (\<not> P \<longrightarrow> G x y))"
  by simp

\<comment> \<open>FIXME: this could have slightly better bound variable names if written out, should we just do
           that and avoid the previous FIXME?\<close>
lemmas prefix_refinement_if2 = prefix_refinement_if[unfolded if_apply_def2]

lemma prefix_refinement_when:
  "\<lbrakk>G = G'; prefix_refinement sr isr isr rvr AR R P Q a c; rvr () ()\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr isr rvr AR R (\<lambda>x y. G \<longrightarrow> P x y) (\<lambda>x y. G' \<longrightarrow> Q x y)
         (when G a) (when G' c)"
  unfolding when_def
  apply clarsimp
  apply (rule prefix_refinement_return_imp)
  apply simp
  done

lemma prefix_refinement_whenE:
  "\<lbrakk>G = G'; prefix_refinement sr isr isr (f \<oplus> rvr) AR R P Q a c; rvr () ()\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr isr (f \<oplus> rvr) AR R (\<lambda>x y. G \<longrightarrow> P x y) (\<lambda>x y. G' \<longrightarrow> Q x y)
         (whenE G a) (whenE G' c)"
  unfolding whenE_def returnOk_def
  apply clarsimp
  apply (rule prefix_refinement_return_imp)
  apply simp
  done

lemma prefix_refinement_unless:
  "\<lbrakk>G = G'; prefix_refinement sr isr isr rvr AR R P Q a c; rvr () ()\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr isr rvr AR R (\<lambda>x y. \<not> G \<longrightarrow> P x y) (\<lambda>x y. \<not> G' \<longrightarrow> Q x y)
         (unless G a) (unless G' c)"
  by (simp add: unless_def prefix_refinement_when)

lemma prefix_refinement_unlessE:
  "\<lbrakk>G = G'; prefix_refinement sr isr isr (f \<oplus> rvr) AR R P Q a c; rvr () ()\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr isr (f \<oplus> rvr) AR R (\<lambda>x y. \<not> G \<longrightarrow> P x y) (\<lambda>x y. \<not> G' \<longrightarrow> Q x y)
         (unlessE G a) (unlessE G' c)"
  by (simp add: unlessE_whenE prefix_refinement_whenE)

lemma prefix_refinement_if_r:
  "\<lbrakk>G' \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q a c;
    \<not>G' \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q' a d \<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R
               P (if G' then Q else Q')
               a (if G' then c else d)"
  by simp

lemma prefix_refinement_if3:
  "\<lbrakk>G = G'; G' \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q a c;
    \<not>G' \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P' Q' b d \<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R
               (if G then P else P') (if G' then Q else Q')
               (if G then a else b) (if G' then c else d)"
  by simp

lemma prefix_refinement_if_strong:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>sr s0 t0; isr s t; P'' s0 s; Q'' t0 t\<rbrakk> \<Longrightarrow> G = G';
    \<lbrakk>G; G'\<rbrakk> \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q a c;
    \<lbrakk>\<not>G; \<not>G'\<rbrakk> \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P' Q' b d \<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R
               (P'' and (if G then P else P')) (Q'' and (if G' then Q else Q'))
               (if G then a else b) (if G' then c else d)"
  by (fastforce simp: prefix_refinement_def)


\<comment> \<open>FIXME: Put more thought into whether we want this section, and if not what alternative rules
          would we want. The comment copied from Corres_UL suggests we might not want them.
          They would be a fair bit more complicated to prove for prefix_refinement.\<close>
section \<open>Some equivalences about liftM and other useful simps\<close>

(* These rules are declared [simp], which in hindsight was not a good decision, because they
   change the return relation which often is schematic when these rules apply in the goal.
   In those circumstances it is usually safer to unfold liftM_def and proceed with the resulting
   substituted term.

   (We leave the [simp] attribute here, because too many proofs now depend on it)
*)
(*
lemma prefix_refinement_liftM_simp[simp]:
  "prefix_refinement sr isr osr rvr AR R P P' (liftM t f) g =
   prefix_refinement sr isr osr (rvr \<circ> t) AR R P P' f g"
  by (auto simp: prefix_refinement_def triv_refinement_def in_liftM)

lemma prefix_refinement_liftM2_simp[simp]:
  "prefix_refinement sr isr osr rvr AR R P P' f (liftM t g) =
   prefix_refinement sr isr osr (\<lambda>x. rvr x \<circ> t) AR R P P' f g"
  by (fastforce simp: prefix_refinement_def in_liftM)

lemma prefix_refinement_liftE_rel_sum[simp]:
 "prefix_refinement sr isr osr (f \<oplus> rvr) AR R P P' (liftE m) (liftE m') =
  prefix_refinement sr isr osr rvr AR R P P' m m'"
  by (simp add: liftE_liftM o_def)

lemmas corres_liftE_lift = corres_liftE_rel_sum[THEN iffD2]*)


section \<open>Support for proving correspondence to noop with hoare triples\<close>

lemma prefix_refinement_noop:
  assumes P: "\<And>s0 s. P s0 s \<Longrightarrow> \<lbrace>\<lambda>t. isr s t \<and> Q t\<rbrace> f \<lbrace>\<lambda>rv t. osr s t \<and> rvr x rv\<rbrace>"
  assumes nt: "no_trace f"
  assumes nf: "\<And>s0 s. P s0 s \<Longrightarrow> no_fail (\<lambda>t. isr s t \<and> Q t) f"
  shows "prefix_refinement sr isr osr rvr AR R P (\<lambda>_. Q) (return x) f"
  apply (subst prefix_refinement_no_trace)
   apply (rule nt)
  apply clarsimp
  apply (frule P)
  apply (insert nf)
  apply (insert nt)
  apply (clarsimp simp: valid_def no_fail_def no_trace_def return_def mres_def failed_def image_def)
  apply (case_tac b; fastforce)
  done

lemma prefix_refinement_noopE:
  assumes P: "\<And>s0 s. P s0 s \<Longrightarrow> \<lbrace>\<lambda>t. isr s t \<and> Q t\<rbrace> f \<lbrace>\<lambda>rv t. osr s t \<and> rvr x rv\<rbrace>,\<lbrace>\<bottom>\<bottom>\<rbrace>"
  assumes nt: "no_trace f"
  assumes nf: "\<And>s0 s. P s0 s \<Longrightarrow> no_fail (\<lambda>t. isr s t \<and> Q t) f"
  shows "prefix_refinement sr isr osr (frvr \<oplus> rvr) AR R P (\<lambda>_. Q) (returnOk x) f"
proof -
  have Q: "\<And>P f Q E. \<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. case_sum (\<lambda>e. E e s) (\<lambda>r. Q r s) r\<rbrace>"
    by (simp add: validE_def)
  thus ?thesis
    apply (simp add: returnOk_def)
    apply (rule prefix_refinement_noop)
      apply (rule hoare_strengthen_post)
       apply (rule Q)
       apply (rule P)
       apply assumption
      apply (simp split: sum.splits)
     apply (rule nt)
    apply (erule nf)
    done
qed

lemma prefix_refinement_noop2:
  assumes f: "\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<exists>\<lbrace>\<lambda>_. (=) s\<rbrace>"
  assumes g: "\<And>t. Q t \<Longrightarrow> \<lbrace>(=) t\<rbrace> g \<lbrace>\<lambda>_. (=) t\<rbrace>"
  assumes nt: "no_trace f" "no_trace g"
  assumes nf: "no_fail P f" "no_fail Q g"
  shows "prefix_refinement sr iosr iosr dc AR R (\<lambda>_. P) (\<lambda>_. Q) f g"
  apply (subst prefix_refinement_no_trace)
   apply (rule nt)
  apply clarsimp
  apply (insert nt)
  apply (insert nf)
  apply (clarsimp simp: no_trace_def no_fail_def failed_def image_def)
  apply (subgoal_tac "\<exists>(r, s')\<in>mres (f s). rel_tmres iosr dc (Result (r, s')) b")
   apply (case_tac b; fastforce simp: mres_def intro: rev_bexI)
  apply (rule use_exs_valid)
   apply (rule exs_hoare_post_imp[rotated])
    apply (erule f)
   apply (case_tac b; clarsimp)
     apply fastforce
    apply fastforce
   apply (subgoal_tac "ba = t")
    apply simp
   apply (rule sym)
   apply (rule use_valid[OF _ g], erule in_mres)
    apply simp+
  done


section \<open>Support for dividing correspondence along logical boundaries\<close>

lemma prefix_refinement_disj_division:
  "\<lbrakk>S \<or> T; S \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q x y;
    T \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P' Q' x y\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R
                         (\<lambda>s0 s. (S \<longrightarrow> P s0 s) \<and> (T \<longrightarrow> P' s0 s)) (\<lambda>s0 s. (S \<longrightarrow> Q s0 s) \<and> (T \<longrightarrow> Q' s0 s)) x y"
  by (safe; pfx_refn_pre, simp+)

lemma prefix_refinement_weaker_disj_division:
  "\<lbrakk>S \<or> T; S \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q x y;
    T \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P' Q' x y\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R (P and P') (Q and Q') x y"
  by (pfx_refn_pre, rule prefix_refinement_disj_division, simp+)

lemma prefix_refinement_symmetric_bool_cases:
  "\<lbrakk>S = T; \<lbrakk>S; T\<rbrakk> \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g;
    \<lbrakk>\<not>S; \<not>T\<rbrakk> \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P' Q' f g\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R (\<lambda>s0 s. (S \<longrightarrow> P s0 s) \<and> (\<not>S \<longrightarrow> P' s0 s))
                                             (\<lambda>s0 s. (T \<longrightarrow> Q s0 s) \<and> (\<not>T \<longrightarrow> Q' s0 s))
                                             f g"
  by (cases S, simp_all)

text \<open>Support for symbolically executing into the guards and manipulating them\<close>

lemma prefix_refinement_symb_exec_l:
  assumes z: "\<And>rv. prefix_refinement sr isr osr rvr AR R (\<lambda>_. P' rv) Q (x rv) y"
  assumes x: "\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> m \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>rv s. P' rv s\<rbrace>"
  assumes nf: "no_fail P m"
  assumes nt: "no_trace m"
  shows      "prefix_refinement sr isr osr rvr AR R (\<lambda>_. P) Q (m >>= (\<lambda>rv. x rv)) y"
  apply pfx_refn_pre
    apply (subst gets_bind_ign[symmetric], rule prefix_refinement_bind[OF _ z])
      apply (rule prefix_refinement_noop2)
           apply (erule x)
          apply (rule gets_wp)
         apply (rule nt)
        apply (rule no_trace_gets)
       apply (rule nf)
      apply (rule no_fail_gets)
     apply (rule valid_validI_wp[OF nt y])
    apply wp
   apply simp+
  done

lemma prefix_refinement_symb_exec_r:
  assumes z: "\<And>rv. prefix_refinement sr isr osr rvr AR R P (\<lambda>_. Q' rv) x (y rv)"
  assumes y: "\<lbrace>Q\<rbrace> m \<lbrace>Q'\<rbrace>"
  assumes x: "\<And>s. Q s \<Longrightarrow> \<lbrace>(=) s\<rbrace> m \<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes nf: "no_fail Q m"
  assumes nt: "no_trace m"
  shows      "prefix_refinement sr isr osr rvr AR R P (\<lambda>_. Q) x (m >>= (\<lambda>rv. y rv))"
  apply pfx_refn_pre
    apply (subst gets_bind_ign[symmetric], rule prefix_refinement_bind[OF _ z])
      apply (rule prefix_refinement_noop2)
           apply (clarsimp simp: simpler_gets_def exs_valid_def mres_def vimage_def)
          apply (erule x)
         apply (rule no_trace_gets)
        apply (rule nt)
       apply (rule no_fail_gets)
      apply (rule nf)
     apply wp
    apply (rule valid_validI_wp[OF nt y])
   apply simp+
  done

lemma prefix_refinement_symb_exec_r_conj:
  assumes z: "\<And>rv. prefix_refinement sr isr osr rvr AR R P (\<lambda>_. Q' rv) x (y rv)"
  assumes y: "\<lbrace>Q\<rbrace> m \<lbrace>Q'\<rbrace>"
  assumes x: "\<And>s. \<lbrace>\<lambda>s'. isr s s' \<and> S s'\<rbrace> m \<lbrace>\<lambda>rv s'. isr s s'\<rbrace>"
  assumes nf: "\<And>s. no_fail (\<lambda>t. isr s t \<and> S t) m"
  assumes nt: "no_trace m"
  shows      "prefix_refinement sr isr osr rvr AR R P (\<lambda>_. S and Q) x (m >>= (\<lambda>rv. y rv))"
proof -
  have P: "prefix_refinement sr isr isr dc AR R \<top>\<top> (\<lambda>_. S) (return undefined) m"
    apply (rule prefix_refinement_noop)
      apply (simp add: x nt nf)+
    done
  show ?thesis
    apply pfx_refn_pre
      apply (subst return_bind[symmetric], rule prefix_refinement_bind[OF P])
        apply (rule z)
       apply wp
      apply (rule valid_validI_wp[OF nt y])
     apply simp+
    done
qed

\<comment> \<open>FIXME: improve automation of this proof\<close>
lemma prefix_refinement_bind_return_r:
  "prefix_refinement sr isr osr (\<lambda>x y. rvr x (h y)) AR R P Q f g \<Longrightarrow>
   prefix_refinement sr isr osr rvr AR R P Q f (do x \<leftarrow> g; return (h x) od)"
  apply (clarsimp simp: prefix_refinement_def bind_def return_def)
  apply ((drule spec)+, (drule (1) mp)+)
  apply (drule (1) bspec, clarsimp)
  apply (subgoal_tac "aa=a")
   prefer 2
   apply (fastforce split: tmres.splits)
  apply clarsimp
  apply (rule_tac x=fa in exI)
  apply (clarsimp simp: is_matching_fragment_def split: tmres.splits)
    apply (case_tac b; fastforce)
   apply (case_tac b; fastforce)
  apply (case_tac bc; fastforce)
  done

lemma prefix_refinement_symb_exec_l':
  "\<lbrakk>prefix_refinement sr isr isr dc AR R P P' f (return ());
    \<And>rv. prefix_refinement sr isr osr rvr AR R (Q rv) P' (g rv) h;
    \<And>s0. \<lbrace>P s0\<rbrace> f \<lbrace>\<lambda>rv. Q rv s0\<rbrace>; no_trace f\<rbrakk>
    \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P P' (f >>= g) h"
  apply (drule prefix_refinement_bind)
     apply assumption
    apply (erule valid_validI_wp)
    apply assumption
   apply wp
  apply clarsimp
  done


section \<open>Building blocks\<close>

lemma prefix_refinement_triv_pre:
  "prefix_refinement sr isr osr rvr AR R \<top>\<top> \<top>\<top> f g
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R \<top>\<top> \<top>\<top> f g"
  by assumption

\<comment> \<open>FIXME: Need to work out the best fragment to provide for prefix_refinement_trivial.
          Defining and using prefix_close like this is one option but might be more work than needed.\<close>
\<comment> \<open>definition prefix_close_set ::
  "((tmid \<times> 's) list \<times> ('s, 'a) tmres) set \<Rightarrow> ((tmid \<times> 's) list \<times> ('s, 'a) tmres) set"
  where
  "prefix_close_set f = {(xs, Incomplete). (\<exists>xs' \<in> fst ` f. \<exists>n\<le>length xs'. drop n xs' = xs)} \<union> f"

definition prefix_close :: "('a, 'b) tmonad \<Rightarrow> ('a, 'b) tmonad" where
  "prefix_close f \<equiv> \<lambda>s. prefix_close_set (f s)"

lemma drop_Suc_eq:
  "drop n xs = y # ys \<Longrightarrow> drop (Suc n) xs = ys"
  by (auto simp: drop_Suc drop_tl)

lemma prefix_close_set_closed:
  "x # xs \<in> fst ` prefix_close_set (f s) \<Longrightarrow> (xs, Incomplete) \<in> prefix_close_set (f s)"
  unfolding prefix_close_set_def
  apply safe
   apply (rule_tac x=aa in bexI)
    apply (rule_tac x="Suc n" in exI)
    apply (fastforce intro!: Suc_leI le_neq_trans elim!: drop_Suc_eq[OF sym])
   apply (auto simp: image_def intro!: bexI)[1]
  apply (rule_tac x=a in bexI)
   apply (rule_tac x="Suc 0" in exI)
   apply fastforce
  apply (auto simp: image_def intro!: bexI)[1]
  done

lemma prefix_close_closed:
  "prefix_closed (prefix_close f)"
  unfolding prefix_closed_def prefix_close_def
  by (auto simp: prefix_close_set_closed)

lemma triv_refinement_prefix_close:
  "\<lbrakk>prefix_closed f; triv_refinement f g\<rbrakk> \<Longrightarrow> triv_refinement f (prefix_close g)"
  apply (clarsimp simp: triv_refinement_def)
  oops

lemma prefix_refinement_trivial:
  "prefix_closed f \<Longrightarrow> pfx_refn (=) (=) R R \<top>\<top> \<top>\<top> f f"
  apply (clarsimp simp: prefix_refinement_def)
  apply (rule_tac x="prefix_close (\<lambda>s'. if s'=s then {(a,b)} else {})" in exI)
  apply (clarsimp simp: triv_refinement_def)
apply (auto simp: is_matching_fragment_def prefix_closed_def self_closed_def env_closed_def
                matching_tr_pfx_def matching_tr_def)[1]
oops\<close>

abbreviation
  "pfx_refnT sr rvr AR R \<equiv> pfx_refn sr rvr AR R \<top>\<top> \<top>\<top>"

lemma prefix_refinement_returnTT:
  "rvr rv rv' \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R \<top>\<top> \<top>\<top> (return rv) (return rv')"
  by (rule prefix_refinement_return_imp, simp)

lemma prefix_refinement_get:
  "prefix_refinement sr iosr iosr iosr AR R \<top>\<top> \<top>\<top> get get"
  by (rule prefix_refinement_get_imp, simp)

lemma prefix_refinement_put_imp:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>sr s0 t0; isr s t; P s0 s; Q t0 t\<rbrakk> \<Longrightarrow> osr s' t'\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr dc AR R P Q (put s') (put t')"
  apply (clarsimp simp: prefix_refinement_def)
  apply (rule default_prefix_refinement_ex)
  apply (clarsimp simp: put_def is_matching_fragment_no_trace)
  done

lemma prefix_refinement_put:
  "osr s t \<Longrightarrow> prefix_refinement sr isr osr dc AR R \<top>\<top> \<top>\<top> (put s) (put t)"
  by (rule prefix_refinement_put_imp, simp)

lemma prefix_refinement_modify:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>sr s0 t0; isr s t; P s0 s; Q t0 t\<rbrakk> \<Longrightarrow> osr (f s) (g t)\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr dc AR R P Q (modify f) (modify g)"
  apply (simp add: modify_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind[where intsr=isr, OF prefix_refinement_get])
      apply (rule_tac P="\<lambda>s0 _. P s0 s" and Q="\<lambda>s0 _. Q s0 sa" in prefix_refinement_put_imp)
      apply wpsimp+
  done

lemmas prefix_refinement_modifyT =
  prefix_refinement_modify[where P="\<top>\<top>" and Q="\<top>\<top>", simplified]

lemmas pfx_refn_modifyT =
  prefix_refinement_modifyT[where sr=sr and isr=sr and osr=sr for sr]

lemmas prefix_refinement_get_pre =
  prefix_refinement_bind[OF prefix_refinement_get _ valid_validI_wp[OF _ get_sp]
                            valid_validI_wp[OF _ get_sp],
                         simplified pred_conj_def, simplified]

lemma prefix_refinement_gets:
  "\<lbrakk>\<And>s t. \<lbrakk>iosr s t; P s; Q t\<rbrakk> \<Longrightarrow> rvr (f s) (f' t)\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R (\<lambda>_. P) (\<lambda>_. Q) (gets f) (gets f')"
  apply (simp add: gets_def)
  apply (rule prefix_refinement_get_pre)
  apply (rule prefix_refinement_return_imp)
  apply simp
  done

lemma prefix_refinement_fail:
  "prefix_refinement sr isr osr rvr AR R \<top>\<top> \<top>\<top> fail fail"
  apply (clarsimp simp: prefix_refinement_def fail_def)
  apply (rule default_prefix_refinement_ex)
  apply (simp add: is_matching_fragment_no_trace)
  done

lemma prefix_refinement_returnOkTT:
  "rvr rv rv' \<Longrightarrow> prefix_refinement sr iosr iosr (rvr' \<oplus> rvr) AR R \<top>\<top> \<top>\<top> (returnOk rv) (returnOk rv')"
  by (rule prefix_refinement_returnOk_imp, simp)

lemma prefix_refinement_throwErrorTT:
  "rvr e e' \<Longrightarrow> prefix_refinement sr iosr iosr (rvr \<oplus> rvr') AR R \<top>\<top> \<top>\<top> (throwError e) (throwError e')"
  by (rule prefix_refinement_throwError_imp, simp)

lemma prefix_refinement_select:
  "\<lbrakk>\<forall>x \<in> T. \<exists>y \<in> S. rvr y x\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R \<top>\<top> \<top>\<top> (select S) (select T)"
  apply (clarsimp simp: prefix_refinement_def select_def)
  apply (drule(1) bspec, clarsimp)
  apply (rule_tac x="return y" in exI)
  apply (simp add: is_matching_fragment_def self_closed_def env_closed_def return_def
                   prefix_closed_def matching_tr_pfx_def matching_tr_def)
  apply (auto simp add: triv_refinement_def return_def image_def)
  done

lemma prefix_refinement_assert:
  "P = P' \<Longrightarrow> prefix_refinement sr iosr iosr dc AR R \<top>\<top> \<top>\<top> (assert P) (assert P')"
  by (simp add: assert_def prefix_refinement_fail prefix_refinement_return_imp)

lemma prefix_refinement_assert_opt:
  "\<lbrakk>rel_option rvr v v'\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R \<top>\<top> \<top>\<top> (assert_opt v) (assert_opt v')"
  by (auto simp: assert_opt_def prefix_refinement_fail prefix_refinement_return_imp
          split: option.splits)

lemma prefix_refinement_assertE:
  "P = P' \<Longrightarrow> prefix_refinement sr iosr iosr dc AR R \<top>\<top> \<top>\<top> (assertE P) (assertE P')"
  by (simp add: assertE_def prefix_refinement_fail prefix_refinement_returnOk_imp)

lemma prefix_refinement_gets_the:
  "\<lbrakk>\<And>s t. \<lbrakk>iosr s t; P s; Q t\<rbrakk> \<Longrightarrow> rel_option rvr (f s) (g t)\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R (\<lambda>_. P) (\<lambda>_. Q) (gets_the f) (gets_the g)"
  apply (simp add: gets_the_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind[where rvr'="rel_option rvr"])
       apply (rule prefix_refinement_gets[where P=P and Q=Q])
       apply simp
      apply (erule prefix_refinement_assert_opt)
     apply wpsimp+
  done

lemma prefix_refinement_gets_map:
  "\<lbrakk>\<And>s t. \<lbrakk>iosr s t; P s; Q t\<rbrakk> \<Longrightarrow> rel_option rvr (f s p) (g t q)\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R (\<lambda>_. P) (\<lambda>_. Q) (gets_map f p) (gets_map g q)"
  apply (subst gets_the_oapply_comp[symmetric])+
  apply (rule prefix_refinement_gets_the)
  apply simp
  done

lemma prefix_refinement_throw_opt:
  "\<lbrakk>\<And>s t. \<lbrakk>iosr s t; P s; Q t\<rbrakk> \<Longrightarrow> rvr ex ex' \<and> rel_option rvr' x x'\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr (rvr \<oplus> rvr') AR R (\<lambda>_. P) (\<lambda>_. Q) (throw_opt ex x) (throw_opt ex' x')"
  apply (simp add: throw_opt_def)
  apply (cases x; cases x')
     apply (clarsimp simp: prefix_refinement_throwError_imp)
    apply (fastforce simp: prefix_refinement_def)
   apply (fastforce simp: prefix_refinement_def)
  apply (clarsimp simp: prefix_refinement_returnOk_imp)
  done

lemma prefix_refinement_alternate1:
  "prefix_refinement sr iosr iosr rvr AR R P Q a c \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R P Q (a \<sqinter> b) c"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule(6) pfx_refnD2, clarsimp)
  apply (fastforce intro: triv_refinement_trans[rotated] triv_refinement_alternative1)
  done

lemma prefix_refinement_alternate2:
  "prefix_refinement sr iosr iosr rvr AR R P Q b c \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R P Q (a \<sqinter> b) c"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule(6) pfx_refnD2, clarsimp)
  apply (fastforce intro: triv_refinement_trans[rotated] triv_refinement_alternative2)
  done

lemma prefix_refinement_either_alternate1:
  "\<lbrakk>prefix_refinement sr iosr iosr rvr AR R P Q a c; prefix_refinement sr iosr iosr rvr AR R P' Q b c\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R (P or P') Q (a \<sqinter> b) c"
  apply (subst prefix_refinement_def, clarsimp simp del: imp_disjL)
  apply (erule disjE)
   apply (drule(6) pfx_refnD2, clarsimp)
   apply (fastforce intro: triv_refinement_trans[rotated] triv_refinement_alternative1)
  apply (drule(6) pfx_refnD2, clarsimp)
  apply (fastforce intro: triv_refinement_trans[rotated] triv_refinement_alternative2)
  done

lemma prefix_refinement_either_alternate2:
  "\<lbrakk>prefix_refinement sr iosr iosr rvr AR R P Q a c; prefix_refinement sr iosr iosr rvr AR R P Q' b c\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr rvr AR R P (Q or Q') (a \<sqinter> b) c"
  apply (subst prefix_refinement_def, clarsimp simp del: imp_disjL)
  apply (erule disjE)
   apply (drule(6) pfx_refnD2, clarsimp)
   apply (fastforce intro: triv_refinement_trans[rotated] triv_refinement_alternative1)
  apply (drule(6) pfx_refnD2, clarsimp)
  apply (fastforce intro: triv_refinement_trans[rotated] triv_refinement_alternative2)
  done

lemma is_matching_fragment_restrict:
  "is_matching_fragment sr osr rvr ctr cres s0 R s f
   \<Longrightarrow> is_matching_fragment sr osr rvr ctr cres s0 R s (\<lambda>s'. if s'=s then f s else {})"
  by (simp add: is_matching_fragment_def prefix_closed_def self_closed_def env_closed_def
                matching_tr_pfx_def matching_tr_def)

lemma triv_refinement_restrict:
  "triv_refinement f (\<lambda>s'. if s'=s then f s else {})"
  by (clarsimp simp: triv_refinement_def)

\<comment> \<open>FIXME: corres rules for condition don't exist, so maybe we don't bother with this. It feels
          like it shouldn't be this hard to prove, but providing correct fragments is frustrating.
          It might make it easier to instantiate if the exists was wrapped in a new definition.\<close>
lemma prefix_refinement_condition_strong:
  "\<lbrakk>\<And>s0 s t0 t. \<lbrakk>sr s0 t0; isr s t; P'' s0 s; Q'' t0 t\<rbrakk> \<Longrightarrow> C s = C' t;
    prefix_refinement sr isr osr rvr AR R P Q a c;
    prefix_refinement sr isr osr rvr AR R P' Q' b d \<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R
               (P'' and (\<lambda>s0 s. if C s then P s0 s else P' s0 s))
               (Q'' and (\<lambda>s0 s. if C' s then Q s0 s else Q' s0 s))
               (condition C a b) (condition C' c d)"
  apply (clarsimp simp: condition_def)
  apply (auto simp: prefix_refinement_def  simp del: not_ex )
     apply (erule notE)
     apply (drule spec | drule (1) mp | drule (1) bspec)+
     apply clarsimp
     apply (rule_tac x="\<lambda>s'. if s'=s then f s else {}" in exI)
     apply (clarsimp simp: triv_refinement_def is_matching_fragment_restrict)
    apply (drule spec | drule (1) mp | drule (1) bspec)+
    apply clarsimp
    apply (rule_tac x="\<lambda>s'. if s'=s then f s else {}" in exI)
    apply (clarsimp simp: triv_refinement_def is_matching_fragment_restrict)
   apply (drule spec | drule (1) mp | drule (1) bspec)+
   apply clarsimp
   apply (rule_tac x="\<lambda>s'. if s'=s then f s else {}" in exI)
   apply (clarsimp simp: triv_refinement_def is_matching_fragment_restrict)
  apply (drule spec | drule (1) mp | drule (1) bspec)+
  apply clarsimp
  apply (rule_tac x="\<lambda>s'. if s'=s then f s else {}" in exI)
  apply (clarsimp simp: triv_refinement_def is_matching_fragment_restrict)
  done

lemma prefix_refinement_mapM[rule_format]:
  "\<lbrakk>list_all2 xyr xs ys;
    \<forall>x y. x \<in> set xs \<longrightarrow> y \<in> set ys \<longrightarrow> xyr x y
          \<longrightarrow> prefix_refinement sr intsr intsr rvr AR R P Q (f x) (g y);
    \<forall>x. x \<in> set xs \<longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>AR\<rbrace> f x \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>;
    \<forall>y. y \<in> set ys \<longrightarrow> \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> g y \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr intsr intsr (list_all2 rvr) AR R P Q (mapM f xs) (mapM g ys)"
  apply (induct xs ys rule: list_all2_induct)
   apply (simp add: mapM_def sequence_def prefix_refinement_return_imp)
  apply (clarsimp simp: mapM_Cons all_conj_distrib imp_conjR)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind, assumption)
      apply (rule prefix_refinement_bind, assumption)
        apply (rule prefix_refinement_triv_pre, rule prefix_refinement_return_imp, simp)
       apply wp
       apply fastforce
     apply (simp | wp | blast dest: validI_prefix_closed)+
  done

lemma prefix_refinement_mapME[rule_format]:
  "\<lbrakk>list_all2 xyr xs ys;
    \<forall>x y. x \<in> set xs \<longrightarrow> y \<in> set ys \<longrightarrow> xyr x y
          \<longrightarrow> prefix_refinement sr intsr intsr (F \<oplus> rvr) AR R P Q (f x) (g y);
    \<forall>x. x \<in> set xs \<longrightarrow> \<lbrace>P\<rbrace>,\<lbrace>AR\<rbrace> f x \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>;
    \<forall>y. y \<in> set ys \<longrightarrow> \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> g y \<lbrace>\<lambda>_ _. True\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr intsr intsr (F \<oplus> list_all2 rvr) AR R P Q (mapME f xs) (mapME g ys)"
  apply (induct xs ys rule: list_all2_induct)
   apply (simp add: mapME_def sequenceE_def prefix_refinement_returnOk_imp)
  apply (clarsimp simp add: mapME_Cons all_conj_distrib imp_conjR)
  apply (rule prefix_refinement_weaken_pre)
    apply (unfold bindE_def validE_def)
    apply (rule prefix_refinement_bind, assumption)
      apply (case_tac rv)
       apply (clarsimp simp: prefix_refinement_throwError_imp)
      apply clarsimp
      apply (rule prefix_refinement_bind, assumption)
        apply (rule prefix_refinement_triv_pre)
        apply (case_tac rv)
         apply (clarsimp simp: prefix_refinement_throwError_imp)
        apply (clarsimp simp: prefix_refinement_returnOk_imp)
       apply (simp | wp | blast dest: validI_prefix_closed)+
  done


section \<open>Some prefix_refinement rules for monadic combinators\<close>

\<comment> \<open>FIXME: naming of these lemmas\<close>
lemma ifM_prefix_refinement:
  assumes   test: "prefix_refinement sr isr isr (=) AR R A A' test test'"
  and          l: "prefix_refinement sr isr osr rvr AR R P P' a a'"
  and          r: "prefix_refinement sr isr osr rvr AR R Q Q' b b'"
  and  abs_valid: "\<lbrace>B\<rbrace>,\<lbrace>AR\<rbrace> test -,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> P s0 s\<rbrace>"
                  "\<lbrace>C\<rbrace>,\<lbrace>AR\<rbrace> test -,\<lbrace>\<lambda>c s0 s. \<not> c \<longrightarrow> Q s0 s\<rbrace>"
  and conc_valid: "\<lbrace>B'\<rbrace>,\<lbrace>R\<rbrace> test' -,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> P' s0 s\<rbrace>"
                  "\<lbrace>C'\<rbrace>,\<lbrace>R\<rbrace> test' -,\<lbrace>\<lambda>c s0 s. \<not> c \<longrightarrow> Q' s0 s\<rbrace>"
  shows "prefix_refinement sr isr osr rvr AR R (A and B and C) (A' and B' and C')
           (ifM test a b) (ifM test' a' b')"
  unfolding ifM_def
  apply pfx_refn_pre
    apply (rule prefix_refinement_bind[OF test])
      apply (erule prefix_refinement_if[OF _ l r])
     apply (wpsimp wp: abs_valid conc_valid rg_vcg_if_lift2)+
  done

lemmas ifM_prefix_refinement' =
  ifM_prefix_refinement[where A=A and B=A and C=A for A,
                        where A'=A' and B'=A' and C'=A' for A', simplified]

lemma orM_prefix_refinement:
  "\<lbrakk>prefix_refinement sr isr isr (=) AR R A A' a a'; prefix_refinement sr isr isr (=) AR R C C' b b';
    \<lbrace>B\<rbrace>,\<lbrace>AR\<rbrace> a -,\<lbrace>\<lambda>c s0 s. \<not> c \<longrightarrow> C s0 s\<rbrace>; \<lbrace>B'\<rbrace>,\<lbrace>R\<rbrace> a' -,\<lbrace>\<lambda>c s0 s. \<not> c \<longrightarrow> C' s0 s\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr isr (=) AR R (A and B) (A' and B') (orM a b) (orM a' b')"
  unfolding orM_def
  apply pfx_refn_pre
    apply (rule ifM_prefix_refinement[where P="\<top>\<top>" and P'="\<top>\<top>"])
          apply (wpsimp | fastforce simp: prefix_refinement_return_imp)+
  done

lemmas orM_prefix_refinement' =
  orM_prefix_refinement[where A=A and B=A for A, simplified, where A'=A' and B'=A' for A', simplified]

lemma andM_prefix_refinement:
  "\<lbrakk>prefix_refinement sr isr isr (=) AR R A A' a a'; prefix_refinement sr isr isr (=) AR R C C' b b';
    \<lbrace>B\<rbrace>,\<lbrace>AR\<rbrace> a -,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> C s0 s\<rbrace>; \<lbrace>B'\<rbrace>,\<lbrace>R\<rbrace> a' -,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> C' s0 s\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr isr (=) AR R (A and B) (A' and B') (andM a b) (andM a' b')"
  unfolding andM_def
  apply pfx_refn_pre
    apply (rule ifM_prefix_refinement[where Q="\<top>\<top>" and Q'="\<top>\<top>"])
          apply (wpsimp | fastforce simp: prefix_refinement_return_imp)+
  done

lemma notM_prefix_refinement:
  "\<lbrakk>prefix_refinement sr isr isr (=) AR R G G' a a'; prefix_closed a; prefix_closed a'\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr isr (=) AR R G G' (notM a) (notM a')"
  unfolding notM_def
  apply pfx_refn_pre
    apply (erule prefix_refinement_bind)
      apply (rule prefix_refinement_returnTT)
      apply wpsimp+
  done

lemma whenM_prefix_refinement:
  "\<lbrakk>prefix_refinement sr isr isr (=) AR R A A' a a'; prefix_refinement sr isr isr dc AR R C C' b b';
    \<lbrace>B\<rbrace>,\<lbrace>AR\<rbrace> a -,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> C s0 s\<rbrace>; \<lbrace>B'\<rbrace>,\<lbrace>R\<rbrace> a' -,\<lbrace>\<lambda>c s0 s. c \<longrightarrow> C' s0 s\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr isr dc AR R (A and B) (A' and B') (whenM a b) (whenM a' b')"
  unfolding whenM_def
  apply pfx_refn_pre
    apply (rule ifM_prefix_refinement[where Q="\<top>\<top>" and Q'="\<top>\<top>"])
          apply (wpsimp | fastforce simp: prefix_refinement_return_imp)+
  done


section \<open>prefix_refinement rules for env_step, commit_step, interference and Await\<close>
\<comment> \<open>FIXME: better name for section\<close>

lemma Int_insert_left2:
  "(insert a B \<inter> C) = ((if a \<in> C then {a} else {}) \<union> (B \<inter> C))"
  by auto

definition rely_stable :: "('t \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> bool" where
  "rely_stable R sr Q = (\<forall>s t t'. Q t \<and> sr s t \<and> R t t' \<longrightarrow> Q t' \<and> (\<exists>s'. sr s' t'))"

lemmas rely_stableD = rely_stable_def[THEN iffD1, simplified imp_conjL, rule_format]

definition env_rely_stable_iosr ::
  "'s rg_pred \<Rightarrow> 't rg_pred \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "env_rely_stable_iosr AR R sr iosr Q =
     (\<forall>s0 t0 s t. Q t0 \<longrightarrow> iosr s0 t0 \<longrightarrow> R t0 t \<longrightarrow> AR s0 s \<longrightarrow> sr s t \<longrightarrow> iosr s t)"

lemmas env_rely_stable_iosrD = env_rely_stable_iosr_def[THEN iffD1, rule_format]

definition env_stable ::
  "'s rg_pred \<Rightarrow> 't rg_pred \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 't \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "env_stable AR R sr iosr Q = (rely_stable R sr Q \<and> env_rely_stable_iosr AR R sr iosr Q \<and> iosr \<le> sr)"

definition abs_rely_stable :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" where
  "abs_rely_stable R P = (\<forall>s s'. P s \<and> R s s' \<longrightarrow> P s')"

lemmas abs_rely_stableD = abs_rely_stable_def[THEN iffD1, simplified imp_conjL, rule_format]

lemma abs_rely_stableT:
  "abs_rely_stable AR \<top>"
  by (simp add: abs_rely_stable_def)

lemma rely_stable_rtranclp:
  "\<lbrakk>rely_stable R sr Q; sr s t; Q t; rtranclp R t t'\<rbrakk> \<Longrightarrow> Q t'"
  apply (rotate_tac 3, induct arbitrary: s rule: converse_rtranclp_induct)
   apply simp
  apply (clarsimp simp: rely_stable_def)
  apply metis
  done

lemma abs_rely_stable_rtranclp:
  "\<lbrakk>abs_rely_stable R P; P s; rtranclp R s s'\<rbrakk> \<Longrightarrow> P s'"
  apply (rotate_tac 2, induct rule: converse_rtranclp_induct)
   apply simp
  apply (clarsimp simp: abs_rely_stable_def)
  done

lemma prefix_refinement_env_step:
  assumes env_stable: "env_stable AR R sr iosr Q"
  shows "prefix_refinement sr iosr iosr dc AR R (\<lambda>s0 s. s0 = s) (\<lambda>t0 t. t0 = t \<and> Q t0)
           env_step env_step"
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
  "\<lbrakk>prefix_refinement sr iosr iosr dc AR R P Q f g; \<lbrace>P\<rbrace>,\<lbrace>AR\<rbrace> f \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>;
    \<lbrace>\<lambda>t0 t. Q t0 t \<and> (\<exists>s0 s. sr s0 t0 \<and> iosr s t)\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr dc AR R P Q (repeat_n n f) (repeat_n n g)"
  apply (induct n)
   apply (simp add: prefix_refinement_return_imp)
  apply pfx_refn_pre
    apply simp
    apply (rule prefix_refinement_bind, assumption+)
   apply simp
  apply auto
  done

lemma prefix_refinement_env_n_steps:
  assumes env_stable: "env_stable AR R sr iosr Q"
  shows "prefix_refinement sr iosr iosr dc AR R
           (=) (\<lambda>t0 t. t0 = t \<and> Q t0) (env_n_steps n) (env_n_steps n)"
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
  "\<lbrakk>prefix_refinement sr iosr iosr dc AR R P Q f g; \<lbrace>P\<rbrace>,\<lbrace>AR\<rbrace> f \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>\<lambda>_. P\<rbrace>;
    \<lbrace>\<lambda>t0 t. Q t0 t \<and> (\<exists>s0 s. sr s0 t0 \<and> iosr s t)\<rbrace>,\<lbrace>R\<rbrace> g \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr dc AR R P Q (repeat f) (repeat g)"
  apply (simp add: repeat_def)
  apply (rule prefix_refinement_weaken_pre)
    apply (rule prefix_refinement_bind, rule prefix_refinement_select[where rvr="(=)"])
       apply simp
      apply simp
      apply (rule prefix_refinement_repeat_n, assumption+)
      apply (rule rg_weaken_pre, assumption, simp)
     apply wp
    apply wp
   apply clarsimp
  apply clarsimp
  done

lemma prefix_refinement_env_steps:
  "env_stable AR R sr iosr Q
   \<Longrightarrow> prefix_refinement sr iosr iosr dc AR R (=) (\<lambda>t0 t. t0 = t \<and> Q t0) env_steps env_steps"
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
   \<Longrightarrow> prefix_refinement sr isr osr dc AR R (\<top>\<top>) (\<top>\<top>) commit_step commit_step"
  apply (clarsimp simp: prefix_refinement_def)
  apply (rule default_prefix_refinement_ex)
  apply (simp add: commit_step_def bind_def get_def return_def put_trace_elem_def)
  apply (erule disjE)
   apply (simp add: is_matching_fragment_no_trace)
  apply (clarsimp simp: is_matching_fragment_def)
  apply (simp add: prefix_closed_def self_closed_def env_closed_def)
  apply (simp add: matching_tr_pfx_def matching_tr_def rely_cond_def)
  done

lemma prefix_refinement_interference:
  "env_stable AR R sr iosr Q
   \<Longrightarrow> prefix_refinement sr iosr iosr dc AR R \<top>\<top> (\<lambda>t0 t. Q t) interference interference"
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

lemma prefix_refinement_Await:
  "\<lbrakk>env_stable AR R sr iosr Q; abs_rely_stable AR P;
    \<forall>s t. P s \<longrightarrow> Q t \<longrightarrow> iosr s t \<longrightarrow> G' t \<longrightarrow> G s;
    (\<exists>s. G' s) \<longrightarrow> (\<exists>s. G s)\<rbrakk>
   \<Longrightarrow> prefix_refinement sr iosr iosr (\<lambda>_ _. True) AR R (\<lambda>s0 s. s0 = s \<and> P s) (\<lambda>t0 t. t0 = t \<and> Q t)
                         (Await G) (Await G')"
  apply (simp add: Await_redef)
  apply pfx_refn_pre
    apply (rule prefix_refinement_bind[where intsr=iosr]
                prefix_refinement_select[where rvr="\<lambda>s s'. G s = G' s'"]
                prefix_refinement_env_steps
           | simp add: if_split[where P="\<lambda>S. x \<in> S" for x] split del: if_split
           | (rule prefix_refinement_get, rename_tac s s',
              rule_tac P="P s" in prefix_refinement_gen_asm,
              rule_tac P="Q s'" in prefix_refinement_gen_asm2)
           | (rule prefix_refinement_select[where rvr="\<top>\<top>"])
           | wp)+
   apply clarsimp
   apply (erule(2) abs_rely_stable_rtranclp)
  apply (clarsimp simp: env_stable_def)
  apply (erule(3) rely_stable_rtranclp)
  done


section \<open>FIXME: name for this section\<close>

lemma par_tr_fin_bind:
  "(\<forall>x. par_tr_fin_principle (g x)) \<Longrightarrow> par_tr_fin_principle (f >>= g)"
  apply (clarsimp simp: par_tr_fin_principle_def bind_def)
  apply (clarsimp split: tmres.split_asm)
  apply (fastforce simp: last_st_tr_def hd_append)
  done

lemma par_tr_fin_add_env_n_steps:
  "par_tr_fin_principle f \<Longrightarrow> par_tr_fin_principle (do x \<leftarrow> f; env_n_steps n od)"
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
  "\<lbrakk>triv_refinement f f'; prefix_refinement sr isr osr rvr AR R P Q f' g\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
  apply (clarsimp simp: prefix_refinement_def)
  apply (strengthen triv_refinement_trans[mk_strg I E])
  apply fastforce
  done

lemma prefix_refinement_triv_refinement_conc:
  "\<lbrakk>prefix_refinement sr isr osr rvr AR R P Q f g'; triv_refinement g' g\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr rvr AR R P Q f g"
  apply (clarsimp simp: prefix_refinement_def triv_refinement_def)
  apply blast
  done


section \<open>
  Using prefix refinement as an in-place calculus, permitting multiple applications at the
  same level\<close>

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
  "\<lbrakk>list_all2 P tr tr'; \<forall>x y. P x y \<longrightarrow> fst x = fst y\<rbrakk>
   \<Longrightarrow> (n < length tr \<and> fst (rev tr ! n) = Me) = (n < length tr' \<and> fst (rev tr' ! n) = Me)"
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
    apply (metis matching_tr transpD[OF matching_tr_transp] sympD[OF matching_tr_symp])
    done
  note is_me = matching_tr1[unfolded matching_tr_def, simplified, THEN list_all2_is_me, symmetric]
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
  "\<lbrakk>matching_tr sr (rev tr) (rev tr'); rely_cond R s0 tr; sr s0 t0\<rbrakk>
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
  "\<lbrakk>prefix_refinement sr isr osr (=) AR (\<lambda>t0 t. \<exists>s0 s. sr s0 t0 \<and> sr s t \<and> R s0 s) P (\<lambda>_ _. True) f g;
    prefix_refinement sr isr osr (=) AR R (\<lambda>_ _. True) Q g h;
    equivp sr; equivp osr; equivp isr;
    \<forall>s t t'. sr s t \<longrightarrow> R t t' \<longrightarrow> (\<exists>s'. sr s' t' \<and> AR s s')\<rbrakk>
   \<Longrightarrow> prefix_refinement sr isr osr (=) AR R P Q f h"
  apply (subst prefix_refinement_def, clarsimp)
  apply (drule_tac s=t and t=t and ?t0.0=t0 and cprog=h in pfx_refnD;
         assumption?)
    apply (metis equivp_reflp_symp_transp reflpD)
   apply metis
  apply clarsimp
  apply (rename_tac h_tr h_res frag_g)
  apply (rule_tac x="\<lambda>s. \<Union>(tr, res) \<in> frag_g t \<inter> ({tr. length tr = length h_tr} \<times> UNIV).
                           \<Union>frag_f \<in> {frag_f. is_matching_fragment sr osr (=) tr res s0 AR s frag_f
                                               \<and> triv_refinement f frag_f}.
                             frag_f s"
               in exI)
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

end
