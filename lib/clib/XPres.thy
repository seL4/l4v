(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory XPres
imports SIMPL_Lemmas
begin

(* FIXME: move *)
lemmas trivial = TrueE[OF TrueI]

(* Intended to be used to calculate `z` from `b`, `x` and `y`. *)
definition xpres_eq_If :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "xpres_eq_If b x y z \<equiv> z = (if b then x else y)"

lemma xpres_eq_If_False:
  "xpres_eq_If False x y y"
  by (simp add: xpres_eq_If_def)

lemma xpres_eq_If_True:
  "xpres_eq_If True x y x"
  by (simp add: xpres_eq_If_def)

lemmas xpres_eq_If_rules = xpres_eq_If_False xpres_eq_If_True

(* Intended to be used to calculate `abnormal` by syntactic analysis of `c`.
   `abnormal` should be true if syntactic analysis of `c` shows that `c`
   never terminates normally. Note that this does not imply that `c` necessarily
   terminates abruptly. *)
definition xpres_abnormal where
  "xpres_abnormal \<Gamma> c abnormal \<equiv> \<forall>s t. abnormal \<longrightarrow> \<not> \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t"

lemma xpres_abnormalD:
  assumes "xpres_abnormal \<Gamma> c abnormal"
  assumes "abnormal"
  assumes "\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t"
  shows False
  using assms by (auto simp: xpres_abnormal_def)

lemma xpres_abnormalI:
  assumes "\<And>s t. \<lbrakk>abnormal; \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t\<rbrakk> \<Longrightarrow> False"
  shows "xpres_abnormal \<Gamma> c abnormal"
  using assms by (auto simp: xpres_abnormal_def)

lemma xpres_abnormal_trivial:
  "xpres_abnormal \<Gamma> c False"
  by (auto simp: xpres_abnormal_def)

lemma xpres_abnormal_throw:
  "xpres_abnormal \<Gamma> Throw True"
  by (auto simp: xpres_abnormal_def elim!: exec_elim_cases)

lemma xpres_abnormal_creturn:
  "xpres_abnormal \<Gamma> (creturn rtu xfu v) True"
  by (auto simp: xpres_abnormal_def creturn_def elim!: exec_elim_cases)

lemma xpres_abnormal_creturn_void:
  "xpres_abnormal \<Gamma> (creturn_void rtu) True"
  by (auto simp: xpres_abnormal_def creturn_void_def elim!: exec_elim_cases)

lemma xpres_abnormal_cbreak:
  "xpres_abnormal \<Gamma> (cbreak rtu) True"
  by (auto simp: xpres_abnormal_def cbreak_def elim!: exec_elim_cases)

lemma xpres_abnormal_guard:
  assumes "xpres_abnormal \<Gamma> c abnormal"
  shows "xpres_abnormal \<Gamma> (Guard f g c) abnormal"
  apply (rule xpres_abnormalI)
  apply (erule exec_elim_cases; clarsimp; erule (1) assms[THEN xpres_abnormalD])
  done

lemma xpres_abnormal_seq:
  assumes C: "xpres_abnormal \<Gamma> c C"
             "xpres_abnormal \<Gamma> d D"
  assumes S: "xpres_eq_If C True D S"
  shows "xpres_abnormal \<Gamma> (Seq c d) S"
  apply (rule xpres_abnormalI)
  apply (erule exec_elim_cases; clarsimp)
  apply (frule Normal_result, clarsimp, rename_tac s s')
  apply (clarsimp simp: S[unfolded xpres_eq_If_def] if_bool_simps)
  apply (erule disjE; erule (1) C[THEN xpres_abnormalD])
  done

lemma xpres_abnormal_cond:
  assumes C: "xpres_abnormal \<Gamma> c C"
             "xpres_abnormal \<Gamma> d D"
  assumes S: "xpres_eq_If C D False S" (* S = (C \<and> D) *)
  shows "xpres_abnormal \<Gamma> (Cond b c d) S"
  apply (rule xpres_abnormalI)
  apply (clarsimp simp: S[unfolded xpres_eq_If_def] if_bool_simps)
  apply (erule exec_elim_cases; clarsimp; erule (1) C[THEN xpres_abnormalD])
  done

lemma xpres_abnormal_call:
  assumes "\<And>s t. xpres_abnormal \<Gamma> (ret s t) abnormal"
  shows "xpres_abnormal \<Gamma> (call i f reset ret) abnormal"
  using assms by (auto simp: xpres_abnormal_def elim: exec_call_Normal_elim)

lemmas xpres_abnormal_rules
  = xpres_abnormal_creturn xpres_abnormal_creturn_void xpres_abnormal_cbreak xpres_abnormal_guard
    xpres_abnormal_seq xpres_abnormal_cond xpres_abnormal_call

(* Intended to be used to calculate `pres_norm`, `pres_abr` and `abnormal`
   by syntactic analysis of `c`.

   Input parameters:
   - c: the program under consideration.
   - xf: a function that extracts the value of a particular variable from the state.
   - v: the presumed value of the variable prior to executing `c`.

   Ouptut parameters:
   - pres_norm: true if syntactic analysis of `c` shows that the variable
     still has the value `v` whenever `c` terminates normally.
   - pres_abr: true if syntactic analysis of `c` shows that the variable
     still has the value `v` whenever `c` terminates abruptly.
   - abormal: true if syntactic analysis shows that `c` never terminates normally. *)
definition xpres_strong ::
  "('s,'p,'f) body \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> ('s,'p,'f) com \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
  where
  "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal
   \<equiv> (\<forall>s t. (\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t \<longrightarrow> \<not> abnormal \<and> (pres_norm \<longrightarrow> xf s = v \<longrightarrow> xf t = v))
          \<and> (\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Abrupt t \<longrightarrow> pres_abr \<longrightarrow> xf s = v \<longrightarrow> xf t = v))
      \<and> (abnormal \<longrightarrow> pres_norm)"

(* For compatibility with older proofs. *)
abbreviation "xpres \<Gamma> xf v c \<equiv> xpres_strong \<Gamma> xf v c True True False"

lemma xpres_def:
  "xpres \<Gamma> xf v c \<equiv> \<forall>s t. \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> t
                          \<longrightarrow> xf s = v \<longrightarrow> (\<forall>t'. t = Normal t' \<or> t = Abrupt t' \<longrightarrow> xf t' = v)"
  by (auto simp: xpres_strong_def atomize_eq)

lemma xpres_strongI:
  assumes "\<And>s t. \<lbrakk>pres_norm; \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t; xf s = v\<rbrakk> \<Longrightarrow> xf t = v"
  assumes "\<And>s t. \<lbrakk>pres_abr; \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Abrupt t; xf s = v\<rbrakk> \<Longrightarrow> xf t = v"
  assumes "\<And>s t. \<lbrakk>abnormal; \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t\<rbrakk> \<Longrightarrow> False"
  assumes "abnormal \<Longrightarrow> pres_norm"
  shows "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal"
  unfolding xpres_strong_def
  by (intro allI impI conjI notI; erule assms)

lemma xpres_strong_abnormalD:
  "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal \<Longrightarrow> abnormal \<Longrightarrow> pres_norm"
  by (simp add: xpres_strong_def)

lemma xpresI:
  "\<lbrakk>\<And>s t t'. \<lbrakk>\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> t; xf s = v; t = Normal t' \<or> t = Abrupt t' \<rbrakk> \<Longrightarrow> xf t' = v\<rbrakk> \<Longrightarrow>
  xpres \<Gamma> xf v c"
  unfolding xpres_def by auto

lemma xpres_strong_abnormal_iff:
  "xpres_strong \<Gamma> xf v c abnormal False abnormal \<longleftrightarrow> xpres_abnormal \<Gamma> c abnormal"
  by (auto simp: xpres_strong_def xpres_abnormal_def)

lemma xpres_skip:
  "xpres \<Gamma> xf v Skip"
  by (rule xpresI; erule exec_Normal_elim_cases; simp)

lemma xpres_strong_basic':
  assumes rl: "\<And>s. pres_norm \<Longrightarrow> xf s = v \<Longrightarrow> xf (f s) = v"
  shows "xpres_strong \<Gamma> xf v (Basic f) pres_norm pres_abr False"
  by (rule xpres_strongI; simp?; erule exec_Normal_elim_cases; clarsimp simp: rl)

lemmas xpres_strong_basic = xpres_strong_basic'[where pres_abr=True]
lemmas xpres_basic = xpres_strong_basic[where pres_norm=True, simplified]

lemma xpres_basic_False:
  "xpres_strong \<Gamma> xf v (Basic f) False True False"
  by (rule xpres_strong_basic, simp)

lemma xpres_exec_Normal:
  assumes "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal"
  assumes pres_norm
  assumes "\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t"
  assumes "xf s = v"
  shows "xf t = v"
  using assms unfolding xpres_strong_def
  apply -
  by (drule (1) mp | erule allE conjE trivial)+

lemma xpres_exec_Abrupt:
  assumes xp: "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal"
  assumes pa: pres_abr
  assumes ex: "\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Abrupt t"
  assumes xf: "xf s = v"
  shows   "xf t = v"
  using assms unfolding xpres_strong_def
  apply -
  by (drule (1) mp | erule allE conjE trivial)+

lemma xpres_exec_abnormal:
  assumes "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal"
  assumes abnormal
  assumes "\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t"
  shows "False"
  using assms unfolding xpres_strong_def
  apply -
  by (drule (1) mp | erule allE conjE notE)+

lemmas xpres_execs = xpres_exec_Normal xpres_exec_Abrupt

(* If `b` never produces a `Normal` result, then we vacuously have that whenever
   the sequence results in a `Normal` state, then `xf` is preserved. Together with
   the rule for `Cond`, this is useful in situations like this:
     IF condition THEN
       \<acute>xf := modified_value ;;
       return
     FI ;;
     // here, `xf` is still preserved.  *)
lemma xpres_strong_seq:
  assumes xpa: "xpres_strong \<Gamma> xf v c c_pres_norm c_pres_abr c_abnormal"
  assumes xpb: "xpres_strong \<Gamma> xf v d d_pres_norm d_pres_abr d_abnormal"
  notes xps = xpa xpb
  \<comment> \<open>abnormal \<longleftrightarrow> c_abnormal \<or> d_abnormal\<close>
  \<comment> \<open>pres_norm \<longleftrightarrow> c_pres_norm \<and> d_pres_norm \<or> abnormal\<close>
  \<comment> \<open>pres_abr \<longleftrightarrow> c_pres_abr \<and> c_pres_norm \<and> d_pres_abr \<or> c_abnormal \<and> c_pres_abr\<close>
  assumes ifs: "xpres_eq_If c_abnormal True d_abnormal abnormal"
               "xpres_eq_If c_pres_norm d_pres_norm False cd_pres_norm"
               "xpres_eq_If cd_pres_norm True abnormal pres_norm"
               "xpres_eq_If c_pres_norm d_pres_abr False c_norm_d_pres_abr"
               "xpres_eq_If c_pres_abr c_norm_d_pres_abr False cd_pres_abr"
               "xpres_eq_If c_abnormal c_pres_abr False c_abnormal_pres_abr"
               "xpres_eq_If cd_pres_abr True c_abnormal_pres_abr pres_abr"
  shows "xpres_strong \<Gamma> xf v (c ;; d) pres_norm pres_abr abnormal"
  unfolding ifs[simplified xpres_eq_If_def if_bool_simps]
  apply (rule xpres_strongI
         ; simp?
         ; erule exec_Normal_elim_cases
         ; erule Normal_resultE Abrupt_resultE
         ; simp
         ; elim disjE conjE exec_elim_cases)
          apply (all \<open>(drule (1) xps[THEN xpres_exec_abnormal], simp)?\<close>)
     apply (all \<open>(drule (2) xpres_execs[OF xpa])\<close>, simp_all)
   apply (all \<open>(erule (2) xpres_execs[OF xpb])\<close>)
  done

lemma xpres_seq:
  assumes xpa: "xpres \<Gamma> xf v a"
  assumes xpb: "xpres \<Gamma> xf v b"
  shows "xpres \<Gamma> xf v (a ;; b)"
  by (rule xpres_strong_seq[OF xpa xpb] xpres_eq_If_rules)+

lemma xpres_strong_while0:
  assumes ex: "\<Gamma>\<turnstile> \<langle>d,s\<rangle> \<Rightarrow> t"
  and     xp: "xpres_strong \<Gamma> xf v a pres_norm pres_abr abnormal"
  and      d: "d = While b a"
  and      s: "s \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. xf s = v}"
  and      t: "pres_norm \<and> t = Normal t' \<or> pres_norm \<and> pres_abr \<and> t = Abrupt t'"
  shows    "xf t' = v"
  using ex d s t
proof (induct)
  case (WhileTrue s' b' c' t u)
  hence eqs: "b' = b" "c' = a" and xfs: "xf s' = v" by auto
  {
    fix w
    assume tv: "t = Normal w" and "\<Gamma> \<turnstile> \<langle>a, Normal s'\<rangle> \<Rightarrow> Normal w" and pres_norm

    have ?thesis
    proof (rule WhileTrue.hyps(5))
      have "xf w = v" by (rule xpres_exec_Normal) fact+
      thus "t \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. xf s = v}" using tv
        by simp
    qed fact+
  } moreover
  {
    fix w
    assume tv: "t = Abrupt w" and "\<Gamma> \<turnstile> \<langle>a, Normal s'\<rangle> \<Rightarrow> Abrupt w" and pres_abr
    have ?thesis
    proof (rule WhileTrue.hyps(5))
      have "xf w = v" by (rule xpres_exec_Abrupt) fact+
      thus "t \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. xf s = v}" using tv
        by simp
    qed fact+
  } ultimately
  show ?thesis using WhileTrue.prems(3) WhileTrue.hyps(2) WhileTrue.hyps(4) unfolding eqs
  apply -
  by (elim disjE conjE; simp; erule Normal_resultE Abrupt_resultE; simp)
qed auto

lemma xpres_strong_while:
  assumes xp: "xpres_strong \<Gamma> xf v x pres_norm pres_abr abnormal"
  assumes pa: "xpres_eq_If pres_norm pres_abr False pres_abr'"
  shows   "xpres_strong \<Gamma> xf v (While b x) pres_norm pres_abr' False"
  unfolding pa[simplified xpres_eq_If_def if_bool_simps]
  apply (rule xpres_strongI)
  apply (erule xpres_strong_while0[OF _ xp refl]; simp)+
  by auto

lemmas xpres_while
  = xpres_strong_while[OF _ xpres_eq_If_True, where pres_abr=True and abnormal=False, simplified]

lemma xpres_strong_xpres_abnormalI:
  assumes abn: "xpres_strong \<Gamma> xf v c' pres_norm pres_abr' abnormal"
  assumes "\<And>s t. \<lbrakk>pres_norm; \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t; xf s = v\<rbrakk> \<Longrightarrow> xf t = v"
  assumes "\<And>s t. \<lbrakk>pres_abr; \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Abrupt t; xf s = v\<rbrakk> \<Longrightarrow> xf t = v"
  assumes "\<And>s t. \<lbrakk>abnormal; \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t\<rbrakk> \<Longrightarrow> False"
  shows "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal"
  by (rule xpres_strongI[OF _ _ _ xpres_strong_abnormalD[OF abn]]; erule assms trivial; assumption)

lemma xpres_strong_call_hoarep_gen:
  assumes mod: "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/F s\<^esub> (P s) Call f (Q s),(A s)"
  assumes ret: "\<And>s t. xf s = v \<Longrightarrow> i s \<in> P (x s) \<longrightarrow> t \<in> Q (x s) \<or> t \<in> A (x s) \<Longrightarrow> xf (reset s t) = v"
  assumes xpr: "\<And>s t. xpres_strong \<Gamma> xf v (ret s t) pres_norm pres_abr abnormal"
  shows "xpres_strong \<Gamma> xf v (call i f reset ret) pres_norm pres_abr abnormal"
  apply (rule xpres_strong_xpres_abnormalI[OF xpr]; simp?; erule exec_call_Normal_elim; simp?)
     apply (erule (1) xpres_execs[OF xpr])
     apply (erule ret)
     apply (frule (1) hoarep_exec_call_body[OF mod], fastforce)
    apply (erule (1) xpres_execs[OF xpr])
    apply (erule ret)
    apply (frule (1) hoarep_exec_call_body[OF mod], fastforce)
   apply (erule ret)
   apply (frule (1) hoarep_exec_call_body[OF mod], fastforce)
  apply (erule (1) xpres_exec_abnormal[OF xpr])
  done

lemmas xpres_call = xpres_strong_call_hoarep_gen[OF hoarep_false_pre_gen, simplified]
lemmas xpres_call_hoarep = xpres_strong_call_hoarep_gen[where P="\<lambda>s. {s}" and x=i and i=i for i, simplified]

lemma xpres_strong_catch:
  assumes xpc: "xpres_strong \<Gamma> xf v c c_pres_norm c_pres_abr c_abnormal"
  assumes xpd: "xpres_strong \<Gamma> xf v d d_pres_norm d_pres_abr d_abnormal"
  notes xps = xpc xpd
  \<comment> \<open>abnormal \<longleftrightarrow> c_abnormal \<and> d_abnormal\<close>
  \<comment> \<open>pres_norm \<longleftrightarrow> abnormal \<or> c_pres_norm \<and> c_pres_abr \<and> d_pres_norm\<close>
  \<comment> \<open>pres_abr \<longleftrightarrow> c_pres_abr \<and> c_pres_abr\<close>
  assumes rew: "xpres_eq_If c_abnormal d_abnormal False abnormal"
               "xpres_eq_If c_pres_norm c_pres_abr False c_pres_norm_abr"
               "xpres_eq_If c_pres_norm_abr d_pres_norm False cd_pres_norm"
               "xpres_eq_If abnormal True cd_pres_norm pres_norm"
               "xpres_eq_If c_pres_abr d_pres_abr False pres_abr"
  shows "xpres_strong \<Gamma> xf v (Catch c d) pres_norm pres_abr abnormal"
  unfolding rew[simplified xpres_eq_If_def if_bool_simps]
  apply (rule xpres_strongI; simp?; erule exec_Normal_elim_cases; simp?; (elim disjE conjE)?)
          apply (all \<open>(drule (1) xps[THEN xpres_exec_abnormal], simp)?\<close>)
     apply (all \<open>drule (2) xpres_execs[OF xpc], assumption?\<close>)
   apply (all \<open>drule (2) xpres_execs[OF xpd], assumption\<close>)
  done

lemma xpres_catch:
  assumes "xpres \<Gamma> xf v b"
  assumes "xpres \<Gamma> xf v c"
  shows "xpres \<Gamma> xf v (Catch b c)"
  by (rule xpres_strong_catch[OF assms] xpres_eq_If_rules)+

lemma xpres_strong_guard:
  assumes "xpres_strong \<Gamma> xf v c pres_norm pres_abr abnormal"
  shows "xpres_strong \<Gamma> xf v (Guard f g c) pres_norm pres_abr abnormal"
  apply (rule xpres_strong_xpres_abnormalI[OF assms]; erule exec_Normal_elim_cases; simp?)
     apply (all \<open>drule (1) xpres_execs[OF assms] assms[THEN xpres_exec_abnormal]; simp\<close>)
  done

lemmas xpres_guard = xpres_strong_guard[where pres_norm=True and pres_abr=True and abnormal=False]

lemma xpres_strong_cond:
  assumes xpc: "xpres_strong \<Gamma> xf v c c_pres_norm c_pres_abr c_abnormal"
  assumes xpd: "xpres_strong \<Gamma> xf v d d_pres_norm d_pres_abr d_abnormal"
  notes xps = xpc xpd
  \<comment> \<open>pres_norm \<longleftrightarrow> abnormal \<or> c_pres_norm \<and> d_pres_norm \<or> c_abnormal \<and> d_pres_norm \<or> c_pres_norm \<and> d_abnormal\<close>
  \<comment> \<open>pres_abr \<longleftrightarrow> c_pres_abr \<and> d_pres_abr\<close>
  \<comment> \<open>abnormal \<longleftrightarrow> c_abnormal \<and> d_abnormal\<close>
  assumes rew: "xpres_eq_If c_abnormal d_abnormal False abnormal"
               "xpres_eq_If c_pres_norm d_pres_norm False cd_pres_norm"
               "xpres_eq_If c_abnormal d_pres_norm False ca_pres_norm"
               "xpres_eq_If c_pres_norm d_abnormal False da_pres_norm"
               "xpres_eq_If ca_pres_norm True da_pres_norm cda_pres_norm"
               "xpres_eq_If cd_pres_norm True cda_pres_norm pres_norm'"
               "xpres_eq_If abnormal True pres_norm' pres_norm"
               "xpres_eq_If c_pres_abr d_pres_abr False pres_abr"
  shows "xpres_strong \<Gamma> xf v (Cond x c d) pres_norm pres_abr abnormal"
  unfolding rew[simplified xpres_eq_If_def if_bool_simps]
  apply (rule xpres_strongI; simp?; erule exec_Normal_elim_cases; elim disjE conjE)
             apply (all \<open>(drule (1) xps[THEN xpres_exec_abnormal], simp)?\<close>)
       apply (all \<open>(erule (2) xpres_execs[OF xpc] xpres_execs[OF xpd])\<close>)
  done

lemma xpres_cond:
  assumes "xpres \<Gamma> xf v a"
  assumes "xpres \<Gamma> xf v b"
  shows "xpres \<Gamma> xf v (Cond x a b)"
  by (rule xpres_strong_cond[OF assms] xpres_eq_If_rules)+

lemma xpres_strong_throw':
  shows   "xpres_strong \<Gamma> xf v Throw True True abnormal"
  by (rule xpres_strongI; simp?; erule exec_Normal_elim_cases; simp)

lemmas xpres_strong_throw = xpres_strong_throw'[where abnormal=True]
lemmas xpres_throw = xpres_strong_throw'[where abnormal=False]

lemma xpres_strong_creturn':
  assumes xfu: "\<And>s f. pres_abr \<Longrightarrow> xf (xfu f s) = xf s"
  and xfg: "\<And>s f. pres_abr \<Longrightarrow> xf (exnu f s) = xf s"
  shows   "xpres_strong \<Gamma> xf v (creturn exnu xfu v') True pres_abr abnormal"
  unfolding creturn_def
  by (rule xpres_strongI; clarsimp elim!: exec_Normal_elim_cases simp: xfu xfg)

lemmas xpres_strong_creturn = xpres_strong_creturn'[where pres_abr=True and abnormal=True, simplified]
lemmas xpres_strong_creturn_False = xpres_strong_creturn'[where pres_abr=False and abnormal=True, simplified]
lemmas xpres_creturn = xpres_strong_creturn'[where pres_abr=True and abnormal=False, simplified]

lemma xpres_strong_creturn_void':
  assumes xfg: "\<And>s f. pres_abr \<Longrightarrow> xf (exnu f s) = xf s"
  shows   "xpres_strong \<Gamma> xf v (creturn_void exnu) True pres_abr abnormal"
  unfolding creturn_void_def
  by (rule xpres_strongI; clarsimp elim!: exec_Normal_elim_cases simp: xfg)

lemmas xpres_strong_creturn_void = xpres_strong_creturn_void'[where pres_abr=True and abnormal=True, simplified]
lemmas xpres_strong_creturn_void_False = xpres_strong_creturn_void'[where pres_abr=False and abnormal=True, simplified]
lemmas xpres_creturn_void = xpres_strong_creturn_void'[where pres_abr=True and abnormal=False, simplified]

lemma xpres_strong_cbreak':
  assumes xfg: "\<And>s f. pres_abr \<Longrightarrow> xf (exnu f s) = xf s"
  shows   "xpres_strong \<Gamma> xf v (cbreak exnu) True pres_abr abnormal"
  unfolding cbreak_def
  by (rule xpres_strongI; clarsimp elim!: exec_Normal_elim_cases simp add: xfg)

lemmas xpres_strong_cbreak = xpres_strong_cbreak'[where pres_abr=True and abnormal=True, simplified]
lemmas xpres_strong_cbreak_False = xpres_strong_cbreak'[where pres_abr=False and abnormal=True, simplified]
lemmas xpres_cbreak = xpres_strong_cbreak'[where pres_abr=True and abnormal=False, simplified]

lemma xpres_catchbrk_C:
  shows   "xpres \<Gamma> xf v (ccatchbrk exnu)"
  unfolding ccatchbrk_def
  by (rule xpresI; fastforce elim!: exec_Normal_elim_cases)

lemma xpres_strong_lvar_nondet_init:
  assumes xfg: "\<And>s f. pres_norm \<Longrightarrow> xf (st f s) = xf s"
  shows   "xpres_strong \<Gamma> xf v (lvar_nondet_init gt st) pres_norm True False"
  by (auto intro!: xpres_strongI elim!: exec_Normal_elim_cases simp: xfg lvar_nondet_init_def)

lemmas xpres_lvar_nondet_init_False = xpres_strong_lvar_nondet_init[where pres_norm=False, simplified]
lemmas xpres_lvar_nondet_init = xpres_strong_lvar_nondet_init[where pres_norm=True, simplified]

(* We ignore DynCom and Call and (for now) Spec.  The first two are covered by xpres_call *)
lemmas xpres_rules = xpres_skip xpres_basic xpres_seq xpres_while
  xpres_call xpres_catch xpres_skip xpres_guard xpres_cond xpres_throw
  xpres_creturn xpres_creturn_void xpres_cbreak xpres_catchbrk_C
  xpres_lvar_nondet_init

end
