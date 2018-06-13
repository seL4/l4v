(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory XPres
imports SIMPL_Lemmas
begin

(* We don't really care if the computation gets stuck or faults, only that xf isn't changed *)
definition
  xpres :: "('s \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('i \<rightharpoonup> ('s, 'i, 'x) com) \<Rightarrow> ('s, 'i, 'x) com \<Rightarrow> bool"
where
  "xpres xf v \<Gamma> c \<equiv> \<forall>s t. \<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> t
  \<longrightarrow> s \<in> Normal ` {s. xf s = v}
  \<longrightarrow> (\<forall>t'. t = Normal t' \<or> t = Abrupt t' \<longrightarrow> xf t' = v)"

lemma xpresI:
  "\<lbrakk>\<And>s t t'. \<lbrakk>\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> t; xf s = v; t = Normal t' \<or> t = Abrupt t' \<rbrakk> \<Longrightarrow> xf t' = v\<rbrakk> \<Longrightarrow>
  xpres xf v \<Gamma> c"
  unfolding xpres_def by auto

(* Sometimes it's easier to reason syntactically --- the two are more or less equivalent, under the assumption
  that c doesn't fault or get stuck *)
lemma xpres_hoareI:
  "\<Gamma> \<turnstile> {s. xf s = v } c {s. xf s = v} \<Longrightarrow> xpres xf v \<Gamma> c"
  apply (rule xpresI)
  apply (drule hoare_sound)
  apply (simp add:HoarePartialDef.valid_def cvalid_def)
  apply (drule spec, drule spec, drule (1) mp)
  apply clarsimp
  done

lemma xpres_skip:
  "xpres xf v \<Gamma> Skip"
  apply (rule xpres_hoareI)
  apply rule
  done

lemma xpres_basic:
  assumes rl: "\<And>s. xf s = v \<Longrightarrow> xf (f s) = v"
  shows "xpres xf v \<Gamma> (Basic f)"
  apply (rule xpresI)
  apply (drule rl)
  apply (erule exec_Normal_elim_cases)
  apply clarsimp
  done

lemma xpres_exec0:
  assumes xp: "xpres xf v \<Gamma> c"
  and     ex: "\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> y"
  and     xy: "y = Normal s' \<or> y = Abrupt s'"
  and     xf: "xf s = v"
  shows   "xf s' = v"
  using xp ex xy xf
  unfolding xpres_def
  apply -
  apply (drule spec, drule spec, drule (1) mp)
  apply (erule disjE)
   apply (drule mp, simp)
   apply simp
  apply (drule mp, simp)
  apply simp
  done

lemma xpres_exec:
  assumes xp: "xpres xf v \<Gamma> c"
  and     ex: "\<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal s'"
  and     xf: "xf s = v"
  shows   "xf s' = v"
  using xp ex xf by (auto intro: xpres_exec0)

lemma xpresD:
  assumes xf: "xf s = v"
  and     xp: "xpres xf v \<Gamma> a"
  and     ex: "\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> Normal s'"
  shows   "xf s' = v"
  by (rule xpres_exec [OF xp ex]) fact+

lemma xpres_abruptD:
  assumes xf: "xf s = v"
  and     xp: "xpres xf v \<Gamma> a"
  and     ex: "\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> Abrupt s'"
  shows   "xf s' = v"
  by (rule xpres_exec0 [OF xp ex], simp) fact+

lemma xpres_seq:
  assumes xa: "xpres xf v \<Gamma> a"
  and     xb: "xpres xf v \<Gamma> b"
  shows   "xpres xf v \<Gamma> (a ;; b)"
  apply (rule xpresI)
  apply (erule exec_Normal_elim_cases)
  apply (erule disjE)
   apply simp
   apply (erule Normal_resultE)
   apply simp
   apply (drule (1) xpresD [OF _ xa])
   apply (erule (1) xpresD [OF _ xb])
  apply simp
  apply (erule Abrupt_resultE)
   apply simp
   apply (drule (1) xpresD [OF _ xa])
   apply (erule (1) xpres_abruptD [OF _ xb])
  apply simp
  apply (drule Abrupt_end, rule refl)
  apply simp
  apply (erule (1) xpres_abruptD [OF _ xa])
  done

lemma xpres_while0:
  assumes ex: "\<Gamma>\<turnstile> \<langle>d,s\<rangle> \<Rightarrow> t"
  and     xp: "xpres xf v \<Gamma> a"
  and      d: "d = While b a"
  and      s: "s \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. xf s = v}"
  and      t: "t = Normal t' \<or> t = Abrupt t'"
  shows    "xf t' = v"
  using ex d s t
proof (induct)
  case (WhileTrue s' b' c' t u)
  hence eqs: "b' = b" "c' = a" and xfs: "xf s' = v" by auto

  {
    fix w
    assume tv: "t = Normal w" and "\<Gamma> \<turnstile> \<langle>a, Normal s'\<rangle> \<Rightarrow> Normal w"

    have ?thesis
    proof (rule WhileTrue.hyps(5))
      have "xf w = v" using xfs xp by (rule xpresD) fact+
      thus "t \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. xf s = v}" using tv
        by simp
    qed fact+
  } moreover
  {
    fix w
    assume tv: "t = Abrupt w" and "\<Gamma> \<turnstile> \<langle>a, Normal s'\<rangle> \<Rightarrow> Abrupt w"
    have ?thesis
    proof (rule WhileTrue.hyps(5))
      have "xf w = v" using xfs xp by (rule xpres_abruptD) fact+
      thus "t \<in> Normal ` {s. xf s = v} \<union> Abrupt ` {s. xf s = v}" using tv
        by simp
    qed fact+
  } ultimately
  show ?thesis using WhileTrue.prems(3) WhileTrue.hyps(2) WhileTrue.hyps(4) eqs
  apply -
  apply (erule disjE)
   apply simp
   apply (erule Normal_resultE)
   apply simp
  apply simp
  apply (erule Abrupt_resultE)
  apply simp
  apply simp
  done
qed auto

lemma xpres_while:
  assumes xp: "xpres xf v \<Gamma> x"
  shows   "xpres xf v \<Gamma> (While b x)"
  apply (rule xpresI)
  apply (erule xpres_while0 [OF _ xp refl])
   apply simp
  apply simp
  done

lemma xpres_call:
  assumes ret: "\<And>s t. xf s = v \<Longrightarrow> xf (r s t) = v"
  and      xp: "\<And>s t. xpres xf v \<Gamma> (c s t)"
  shows    "xpres xf v \<Gamma> (call i f r c)"
  apply (rule xpresI)
  apply (erule exec_call_Normal_elim)
      apply (erule (1) xpres_exec0 [OF xp])
      apply (erule ret)
     apply simp
     apply (erule subst, erule ret)
    apply simp
   apply simp
  apply simp
  done

lemma xpres_catch:
  assumes xpb: "xpres xf v \<Gamma> b"
  and     xpc: "xpres xf v \<Gamma> c"
  shows    "xpres xf v \<Gamma> (Catch b c)"
  apply (rule xpresI)
  apply (erule exec_Normal_elim_cases)
   apply (drule (1) xpres_abruptD [OF _ xpb])
   apply (erule (2) xpres_exec0 [OF xpc])
  apply (erule (2) xpres_exec0 [OF xpb])
  done

lemma xpres_guard:
  assumes xp: "xpres xf v \<Gamma> c"
  shows   "xpres xf v \<Gamma> (Guard f g c)"
  apply (rule xpresI)
  apply (erule exec_Normal_elim_cases)
   apply (erule (2) xpres_exec0 [OF xp])
  apply simp
  done

lemma xpres_cond:
  assumes xpa: "xpres xf v \<Gamma> a"
  and     xpb: "xpres xf v \<Gamma> b"
  shows   "xpres xf v \<Gamma> (Cond x a b)"
  apply (rule xpresI)
  apply (erule exec_Normal_elim_cases)
   apply (erule (2) xpres_exec0 [OF xpa])
  apply (erule (2) xpres_exec0 [OF xpb])
  done

lemma xpres_throw:
  shows   "xpres xf v \<Gamma> Throw"
  apply (rule xpresI)
  apply (erule exec_Normal_elim_cases)
  apply simp
  done

lemma xpres_creturn:
  assumes xfu: "\<And>s f. xf (xfu f s) = xf s"
  and xfg: "\<And>s f. xf (exnu f s) = xf s"
  shows   "xpres xf v \<Gamma> (creturn exnu xfu v')"
  unfolding creturn_def
  apply (rule xpresI)
  apply (clarsimp elim!: exec_Normal_elim_cases simp add: xfg xfu)+
  done

lemma xpres_creturn_void:
  assumes xfg: "\<And>s f. xf (exnu f s) = xf s"
  shows   "xpres xf v \<Gamma> (creturn_void exnu)"
  unfolding creturn_void_def
  apply (rule xpresI)
  apply (clarsimp elim!: exec_Normal_elim_cases simp add: xfg)
  done

lemma xpres_cbreak:
  assumes xfg: "\<And>s f. xf (exnu f s) = xf s"
  shows   "xpres xf v \<Gamma> (cbreak exnu)"
  unfolding cbreak_def
  apply (rule xpresI)
  apply (clarsimp elim!: exec_Normal_elim_cases simp add: xfg)
  done

lemma xpres_catchbrk_C:
  shows   "xpres xf v \<Gamma> (ccatchbrk exnu)"
  unfolding ccatchbrk_def
  apply (rule xpresI)
  apply (fastforce elim!: exec_Normal_elim_cases)
  done

lemma xpres_lvar_nondet_init:
  assumes xfg: "\<And>s f. xf (st f s) = xf s"
  shows   "xpres xf v \<Gamma> (lvar_nondet_init gt st)"
  apply (rule xpresI)
  apply (simp add: lvar_nondet_init_def)
  apply (auto elim!: exec_Normal_elim_cases simp add: xfg)
  done

(* We ignore DynCom and Call and (for now) Spec.  The first two are covered by xpres_call *)
lemmas xpres_rules = xpres_skip xpres_basic xpres_seq xpres_while
  xpres_call xpres_catch xpres_skip xpres_guard xpres_cond xpres_throw
  xpres_creturn xpres_creturn_void xpres_cbreak xpres_catchbrk_C
  xpres_lvar_nondet_init

end
