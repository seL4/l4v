(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory SimplRewrite
imports
  "CTranslationNICTA"
  "Lib.SplitRule"
  "HOL-Eisbach.Eisbach"
begin

primrec
  add_statefn :: "('s \<Rightarrow> 's) \<Rightarrow> ('s, 'x, 'e) com \<Rightarrow> ('s, 'x, 'e) com"
where
    "add_statefn f (Call x) = Call x"
  | "add_statefn f (Seq c d) = Seq (add_statefn f c) (add_statefn f d)"
  | "add_statefn f (Catch c d) = Catch (add_statefn f c) (add_statefn f d)"
  | "add_statefn f Throw = Throw"
  | "add_statefn f (Guard F S c) = Guard F {s. f s \<in> S} (add_statefn f c)"
  | "add_statefn f (DynCom c_fn) = DynCom (\<lambda>s. add_statefn f (c_fn (f s)))"
  | "add_statefn f (While S c) = While {s. f s \<in> S} (add_statefn f c)"
  | "add_statefn f (Cond S c c') = Cond {s. f s \<in> S} (add_statefn f c) (add_statefn f c')"
  | "add_statefn f (Spec R) = Spec {(a, b). (f a, f b) \<in> R}"
  | "add_statefn f (Basic g) = Basic (\<lambda>s. inv f (g (f s)))"
  | "add_statefn f Skip = Skip"

lemma add_statefn_id1:
  "add_statefn id x = x"
  by (induct x, simp_all add: inv_id[simplified id_def])

lemma add_statefn_id[simp]:
  "add_statefn id = id"
  by (rule ext, simp add: add_statefn_id1)

lemma add_statefn_comp:
  "\<lbrakk> inv (g o f) = inv f o inv g \<rbrakk>
     \<Longrightarrow> add_statefn f (add_statefn g x) = add_statefn (g o f) x"
  by (induct x, simp_all add: o_def)

definition
 "add_statefn_xstate f xs \<equiv> case xs of
    Normal s \<Rightarrow> Normal (f s) | Abrupt s \<Rightarrow> Abrupt (f s) | _ \<Rightarrow> xs"

lemmas add_statefn_xstate_simps[simp]
    = add_statefn_xstate_def[split_simps xstate.split]

lemma isAbr_add_statefn_xstate[simp]:
  "isAbr (add_statefn_xstate f xs) = isAbr xs"
  by (cases xs, simp_all)

lemma add_statefn_xstate_comp:
  "add_statefn_xstate f (add_statefn_xstate g xs) = add_statefn_xstate (f o g) xs"
  by (cases xs, simp_all)

lemma add_statefn_xstate_id[simp]:
  "add_statefn_xstate id = id"
  by (simp add: add_statefn_xstate_def fun_eq_iff split: xstate.split)

lemma add_statefn_exec1:
  assumes bij: "bij f"
  shows "\<Gamma> \<turnstile> \<langle>c, xs\<rangle> \<Rightarrow> t
        \<Longrightarrow> (map_option (add_statefn (inv f)) o \<Gamma>) \<turnstile> \<langle>add_statefn (inv f) c,
                 add_statefn_xstate f xs\<rangle> \<Rightarrow> add_statefn_xstate f t"
proof (induct rule: exec.induct)

  case Basic show ?case
    apply simp
    apply (rule_tac P="exec G c xs" for G c xs in subst[rotated], rule exec.Basic)
    apply (simp add: inv_inv_eq bij inv_f_f bij_is_inj)
    done

qed (auto intro: exec.intros simp: inv_f_f[OF bij_is_inj, OF bij]
       surj_f_inv_f[OF bij_is_surj, OF bij])

lemma add_statefn_exec:
  assumes bij: "bij f"
  shows "\<Gamma> \<turnstile> \<langle>add_statefn f c, xs\<rangle> \<Rightarrow> t
    = (map_option (add_statefn (inv f)) o \<Gamma>) \<turnstile> \<langle>c, add_statefn_xstate f xs\<rangle>
         \<Rightarrow> add_statefn_xstate f t"
  apply (rule iffI)
   apply (drule add_statefn_exec1[OF bij])
   apply (simp add: add_statefn_comp surj_iff[THEN iffD1]
                    bij_is_surj[OF bij] inv_inv_eq bij)
  apply (drule add_statefn_exec1[OF bij_imp_bij_inv, OF bij])
  apply (simp add: inv_inv_eq bij add_statefn_xstate_comp
                   bij_is_inj[OF bij])
  apply (simp add: o_def option.map_comp add_statefn_comp
                   surj_iff[THEN iffD1] bij_is_surj[OF bij])
  apply (simp add: add_statefn_comp inj_iff[THEN iffD1]
                   bij_is_inj[OF bij] inv_inv_eq bij)
  apply (simp add: map_option_case)
  done

definition
  exec_simulates :: "'s set \<Rightarrow> 's set \<Rightarrow>
        ('s, 'x, 'e) com \<Rightarrow> ('s, 'x, 'e) com \<Rightarrow> bool"
where
 "exec_simulates S T a b =
    (\<forall>s \<in> S. \<forall>\<Gamma> t. \<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> t
            \<longrightarrow> \<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> t \<or> (\<exists>ft. \<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> Fault ft)
                         \<or> (\<exists>t' \<in> - T. \<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> Normal t'))"

lemma exec_simulates_refl:
  "exec_simulates S T c c"
  by (simp add: exec_simulates_def)

lemma exec_simulatesD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> t; exec_simulates S T a b; s \<in> S \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> t \<or> (\<exists>ft. \<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> Fault ft)
         \<or> (\<exists>t' \<in> - T. \<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> Normal t')"
  unfolding exec_simulates_def by auto

definition
  spec_simulates :: "('x \<rightharpoonup> ('s, 'x, 'e) com) \<Rightarrow> ('x \<rightharpoonup> ('s, 'x, 'e) com) \<Rightarrow> bool"
where
 "spec_simulates G G' = (\<forall>x. (G x = None) = (G' x = None)
    \<and> (\<forall>b b'. G x = Some b \<and> G' x = Some b' \<longrightarrow> exec_simulates UNIV UNIV b b'))"

lemma spec_simulates_to_exec_simulates:
  "\<lbrakk> G \<turnstile> \<langle>a, xs\<rangle> \<Rightarrow> t; spec_simulates G G' \<rbrakk>
    \<Longrightarrow> G' \<turnstile> \<langle>a, xs\<rangle> \<Rightarrow> t \<or> (\<exists>ft. G' \<turnstile> \<langle>a, xs\<rangle> \<Rightarrow> Fault ft)"
proof (induct rule: exec.induct)

  case (Call p bdy s t)
  show ?case using Call
    apply clarsimp
    apply (frule_tac x=p in spec_simulates_def[THEN iffD1, rule_format])
    apply (clarsimp simp: exec_simulates_def)
    apply (rule exec.Call, simp)
    apply (blast intro: exec.intros)
    done

next

  case (CallUndefined p)
  show ?case using CallUndefined
    apply clarsimp
    apply (frule_tac x=p in spec_simulates_def[THEN iffD1, rule_format])
    apply (fastforce intro: exec.CallUndefined)
    done

qed (auto intro: exec.intros, (force intro: exec.intros)+)

theorem
  spec_simulates_refinement:
  "\<lbrakk> spec_simulates G G'; exec_simulates P Q a b;
        G' \<turnstile> P b Q, A \<rbrakk>
       \<Longrightarrow> G \<turnstile> P a Q, A"
  apply (drule hoare_sound)
  apply (rule hoare_complete)
  apply (clarsimp simp: HoarePartialDef.cvalid_def
                        HoarePartialDef.valid_def)
  apply (rule ccontr)
  apply (drule(1) exec_simulatesD, simp)
  apply ((auto | drule(1) spec_simulates_to_exec_simulates)+)
  done

definition
  exec_statefn_simulates :: "('s \<Rightarrow> 's) \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow>
        ('s, 'x, 'e) com \<Rightarrow> ('s, 'x, 'e) com \<Rightarrow> bool"
where
 "exec_statefn_simulates f S T a b =
    (\<forall>s \<in> S. \<forall>\<Gamma> t. \<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> t
            \<longrightarrow> (map_option (add_statefn (inv f)) o \<Gamma>) \<turnstile> \<langle>b, Normal (f s)\<rangle> \<Rightarrow> add_statefn_xstate f t
                  \<or> (\<exists>ft. (map_option (add_statefn (inv f)) o \<Gamma>) \<turnstile> \<langle>b, Normal (f s)\<rangle> \<Rightarrow> Fault ft)
                  \<or> (\<exists>t' \<in> - T. (map_option (add_statefn (inv f)) o \<Gamma>) \<turnstile> \<langle>b, Normal (f s)\<rangle> \<Rightarrow> Normal (f t')))"

lemma exec_statefn_simulatesD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> t; exec_statefn_simulates f S T a b; s \<in> S \<rbrakk>
    \<Longrightarrow> (map_option (add_statefn (inv f)) o \<Gamma>) \<turnstile> \<langle>b, Normal (f s)\<rangle> \<Rightarrow> add_statefn_xstate f t
                  \<or> (\<exists>ft. (map_option (add_statefn (inv f)) o \<Gamma>) \<turnstile> \<langle>b, Normal (f s)\<rangle> \<Rightarrow> Fault ft)
                  \<or> (\<exists>t' \<in> - T. (map_option (add_statefn (inv f)) o \<Gamma>) \<turnstile> \<langle>b, Normal (f s)\<rangle> \<Rightarrow> Normal (f t'))"
  unfolding exec_statefn_simulates_def by auto

lemmas exec_statefn_simulatesI
    = exec_statefn_simulates_def[THEN iffD2, rule_format]

lemma exec_statefn_simulates_refl:
  "exec_statefn_simulates id S T c c"
  by (simp add: exec_statefn_simulates_def map_option.id)

lemma exec_statefn_simulates_via_statefn:
  "bij f \<Longrightarrow>
   exec_statefn_simulates f S T a b = exec_simulates S T a (add_statefn f b)"
  apply (simp add: exec_statefn_simulates_def exec_simulates_def)
  apply (simp add: add_statefn_exec bij_imp_bij_inv)
  done

definition
 "spec_statefn_simulates f G G' = (\<forall>x. (G x = None) = (G' x = None)
    \<and> (\<forall>b b'. G x = Some b \<and> G' x = Some b' \<longrightarrow> exec_statefn_simulates f UNIV UNIV b b'))"

lemma spec_statefn_simulates_via_statefn:
  "bij f \<Longrightarrow> spec_statefn_simulates f G G'
      = spec_simulates G (map_option (add_statefn f) o G')"
  apply (simp add: spec_statefn_simulates_def spec_simulates_def)
  apply (rule arg_cong[where f=All, OF ext])
  apply (rule HOL.conj_cong[OF refl])
  apply (safe, simp_all add: exec_statefn_simulates_via_statefn)
  done

theorem
  spec_statefn_simulates_refinement:
  "\<lbrakk> spec_statefn_simulates f G G';
          exec_statefn_simulates f {s. f s \<in> P} {s. f s \<in> Q} a b;
          G' \<turnstile> P b Q, A; bij f \<rbrakk>
       \<Longrightarrow> G \<turnstile> {s. f s \<in> P} a {s. f s \<in> Q}, {s. f s \<in> A}"
  apply (simp add: spec_statefn_simulates_via_statefn
                   exec_statefn_simulates_via_statefn)
  apply (erule spec_simulates_refinement)
   apply (simp add: Compl_Collect)
  apply (drule hoare_sound)
  apply (rule hoare_complete)
  apply (clarsimp simp: HoarePartialDef.cvalid_def
                        HoarePartialDef.valid_def
                        add_statefn_exec)
  apply (simp add: o_def option.map_comp)
  apply (simp add: add_statefn_comp surj_iff[THEN iffD1, OF bij_is_surj]
                   inv_inv_eq)
  apply (simp add: map_option_case)
  apply (case_tac t, auto)
  done

primrec
  com_initial_guards :: "('s, 'x, 'e) com \<Rightarrow> 's set"
where
  "com_initial_guards (a ;; b) = com_initial_guards a"
| "com_initial_guards (Guard F G c) = G \<inter> com_initial_guards c"
| "com_initial_guards Skip = UNIV"
| "com_initial_guards Throw = UNIV"
| "com_initial_guards (Basic f) = UNIV"
| "com_initial_guards (Spec r) = UNIV"
| "com_initial_guards (Cond S a b) = UNIV"
| "com_initial_guards (While S c) = UNIV"
| "com_initial_guards (Call f) = UNIV"
| "com_initial_guards (DynCom fn) = UNIV"
| "com_initial_guards (Catch a b) = UNIV"

lemma com_initial_guards_extra_simps[simp]:
  "com_initial_guards (whileAnno S I V c) = UNIV"
  "com_initial_guards (creturn exn_upd rv_upd rv) = UNIV"
  "com_initial_guards (creturn_void exn_upd) = UNIV"
  "com_initial_guards (call init f ret save) = UNIV"
  "com_initial_guards (cbreak exn_upd) = UNIV"
  "com_initial_guards (ccatchbrk exn) = UNIV"
  by (simp_all add: whileAnno_def creturn_def creturn_void_def
                    call_def block_def cbreak_def ccatchbrk_def)

lemmas com_initial_guards_all_simps
    = com_initial_guards.simps com_initial_guards_extra_simps

primrec
  com_final_guards :: "'s set \<Rightarrow> ('s, 'x, 'e) com \<Rightarrow> 's set"
where
  "com_final_guards S (a ;; b) = com_final_guards UNIV b"
| "com_final_guards S (Guard F G c) = com_final_guards (S \<inter> G) c"
| "com_final_guards S Skip = S"
| "com_final_guards S Throw = UNIV"
| "com_final_guards S (Basic f) = UNIV"
| "com_final_guards S (Spec r) = UNIV"
| "com_final_guards S (Cond C a b) = UNIV"
| "com_final_guards S (While C c) = UNIV"
| "com_final_guards S (Call f) = UNIV"
| "com_final_guards S (DynCom fn) = UNIV"
| "com_final_guards S (Catch a b) = UNIV"

lemma com_final_guards_extra_simps[simp]:
  "com_final_guards S (whileAnno C I V c) = UNIV"
  "com_final_guards S (creturn exn_upd rv_upd rv) = UNIV"
  "com_final_guards S (creturn_void exn_upd) = UNIV"
  "com_final_guards S (call init f ret save) = UNIV"
  "com_final_guards S (cbreak exn_upd) = UNIV"
  "com_final_guards S (ccatchbrk exn) = UNIV"
  by (simp_all add: whileAnno_def creturn_def creturn_void_def
                    call_def block_def cbreak_def ccatchbrk_def)

lemmas com_final_guards_all_simps
    = com_final_guards.simps com_final_guards_extra_simps

lemma exec_not_in_initial_guards:
  "\<lbrakk> s \<notin> com_initial_guards c \<rbrakk>
      \<Longrightarrow> \<exists>ft. \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Fault ft"
  apply (induct c, simp_all)
   apply clarsimp
   apply (blast intro: exec.Seq exec.FaultProp)
  apply (blast intro: exec.GuardFault exec.Guard)
  done

lemma exec_in_final_guards_induct:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>c, x\<rangle> \<Rightarrow> y \<rbrakk>
      \<Longrightarrow> \<forall>s t S. x = Normal s \<and> y = Normal t \<and> s \<in> S
            \<longrightarrow> t \<in> com_final_guards S c"
  apply (induct rule: exec.induct, simp_all)
  apply (case_tac s', simp_all)
  apply (auto elim: exec_Normal_elim_cases)
  done

lemma exec_in_final_guards:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal t \<rbrakk>
      \<Longrightarrow> t \<in> com_final_guards UNIV c"
  by (drule exec_in_final_guards_induct, simp)

lemma exec_statefn_simulates_Seq:
  "\<lbrakk> exec_statefn_simulates f S {s. f s \<in> com_initial_guards d} a b;
       exec_statefn_simulates f UNIV T c d \<rbrakk>
        \<Longrightarrow> exec_statefn_simulates f S T (a ;; c) (b ;; d)"
  apply (rule exec_statefn_simulatesI)
  apply (erule exec.cases, simp_all)
  apply clarsimp
  apply (drule(2) exec_statefn_simulatesD)
  apply (elim disjE exE)
    apply (case_tac s', simp_all)[1]
       apply (drule(1) exec_statefn_simulatesD, simp)
       apply (auto intro: exec.Seq)[1]
      apply ((force elim: exec.Seq exec.cases notE)+)[4]
  apply clarsimp
  apply (rule ccontr, frule_tac \<Gamma>="map_option (add_statefn (inv f)) \<circ> \<Gamma>"
            in exec_not_in_initial_guards, clarsimp)
  apply (blast intro: exec.Seq)
  done

lemma exec_statefn_simulates_Cond:
  "\<lbrakk> \<And>s. s \<in> S \<Longrightarrow> (s \<in> C) = (f s \<in> C'); exec_statefn_simulates f (S \<inter> C) T a b;
            exec_statefn_simulates f (S \<inter> - C) T c d \<rbrakk>
        \<Longrightarrow> exec_statefn_simulates f S T (Cond C a c) (Cond C' b d)"
  apply atomize
  apply (rule exec_statefn_simulatesI)
  apply (erule exec.cases, simp_all)
   apply clarsimp
   apply (drule spec, drule(1) mp, simp)
   apply (drule(1) exec_statefn_simulatesD, simp)
   apply (auto intro: exec.CondTrue)[1]
  apply clarsimp
  apply (drule spec, drule(1) mp, simp)
  apply (drule(1) exec_statefn_simulatesD, simp)
  apply (auto intro: exec.CondFalse)[1]
  done

lemma exec_While_not_in_state_lemma:
  "\<lbrakk> \<forall>t'\<in>- T. \<not> \<Gamma> \<turnstile> \<langle>While C' b,Normal s\<rangle> \<Rightarrow> Normal (f t');
     \<forall>ft. \<not> \<Gamma> \<turnstile> \<langle>While C' b,Normal s\<rangle> \<Rightarrow> Fault ft \<rbrakk>
     \<Longrightarrow> (s \<in> com_initial_guards b \<or> s \<notin> f ` (- T))"
  apply (rule ccontr, clarsimp)
  apply (drule_tac \<Gamma>=\<Gamma> in exec_not_in_initial_guards)
  apply (blast intro: exec.WhileTrue exec.WhileFalse)
  done

lemma exec_statefn_simulates_While_lemma:
  assumes sim: "exec_statefn_simulates f C
        {s. f s \<in> S \<and> (f s \<in> com_initial_guards b \<or> f s \<notin> f ` (- T))} a b"
  assumes eq: "\<And>s. \<lbrakk> f s \<in> S; f s \<in> com_initial_guards b \<or> f s \<notin> f ` (- T) \<rbrakk>
    \<Longrightarrow> s \<in> C = (f s \<in> C')"
  assumes subs: "com_final_guards UNIV b \<subseteq> S"
  shows "\<lbrakk> \<Gamma> \<turnstile> \<langle>bdy, xs\<rangle> \<Rightarrow> t \<rbrakk>
            \<Longrightarrow> \<forall>s. bdy = While C a \<and> xs = Normal s \<and> f s \<in> S
                \<longrightarrow> (map_option (add_statefn (inv f)) o \<Gamma>)
                         \<turnstile> \<langle>While C' b, Normal (f s)\<rangle> \<Rightarrow> add_statefn_xstate f t
                   \<or> (\<exists>ft. (map_option (add_statefn (inv f)) o \<Gamma>)
                         \<turnstile> \<langle>While C' b,Normal (f s)\<rangle> \<Rightarrow> Fault ft)
                   \<or> (\<exists>t' \<in> - T. (map_option (add_statefn (inv f)) o \<Gamma>)
                         \<turnstile> \<langle>While C' b,Normal (f s)\<rangle> \<Rightarrow> Normal (f t'))"
  apply (induct rule: exec.induct, simp_all)
   apply clarsimp
   apply (rule ccontr)
   apply (frule exec_While_not_in_state_lemma, simp)
   apply (drule(1) eq[rotated])
   apply (drule(1) exec_statefn_simulatesD[OF _ sim])
   apply (simp add: o_def)
   apply (elim disjE exE)
     apply (case_tac s', simp_all)
        apply (blast intro: exec.WhileTrue
                 exec_in_final_guards[THEN subsetD[OF subs]])[1]
       apply (erule exec.cases, simp_all)[1]
       apply (blast intro: exec.WhileTrue)[1]
      apply (erule exec.cases, simp_all)[1]
      apply (blast intro: exec.WhileTrue)
     apply (erule exec.cases, simp_all)[1]
     apply (blast intro: exec.WhileTrue)[1]

    apply (case_tac s', simp_all)
       apply (blast intro: exec.WhileTrue)
      apply (erule exec.cases, simp_all)[1]
      apply (blast intro: exec.WhileTrue)
     apply (erule exec.cases, simp_all)
     apply (blast intro: exec.WhileTrue)
    apply (erule exec.cases, simp_all)[1]
    apply (blast intro: exec.WhileTrue)

   apply (clarsimp simp: Bex_def exec_in_final_guards[THEN subsetD[OF subs]])
   apply (drule_tac \<Gamma>="map_option (add_statefn (inv f)) \<circ> \<Gamma>"
             in exec_not_in_initial_guards)
   apply (clarsimp simp: o_def)
   apply (blast intro: exec.WhileTrue exec.WhileFalse)

  apply clarsimp
  apply (rule ccontr, frule exec_While_not_in_state_lemma, simp)

  apply (cut_tac s=s in eq)
  apply (auto intro: exec.WhileFalse)
  done

lemma exec_statefn_simulates_While:
  assumes bij: "bij f" shows
  "\<lbrakk> \<And>s. \<lbrakk> s \<in> S \<or> f s \<in> com_final_guards UNIV b;
            f s \<in> com_initial_guards b \<or> s \<in> T \<rbrakk>
            \<Longrightarrow> s \<in> C = (f s \<in> C');
       exec_statefn_simulates f C {s. (s \<in> S \<or> f s \<in> com_final_guards UNIV b)
            \<and> (f s \<in> com_initial_guards b \<or> s \<in> T)} a b \<rbrakk>
        \<Longrightarrow> exec_statefn_simulates f S T (While C a) (While C' b)"
  apply (rule exec_statefn_simulatesI)
  apply (rule_tac S="f ` S \<union> com_final_guards UNIV b"
           in exec_statefn_simulates_While_lemma[rule_format])
      apply (auto simp add: inj_image_mem_iff[OF bij_is_inj, OF bij])
  done

lemma exec_statefn_simulates_Catch:
  "\<lbrakk> exec_statefn_simulates f S UNIV a b; exec_statefn_simulates f UNIV T c d \<rbrakk>
        \<Longrightarrow> exec_statefn_simulates f S T (Catch a c) (Catch b d)"
  apply (rule exec_statefn_simulatesI)
  apply (erule exec.cases, simp_all)
   apply clarsimp
   apply (drule(2) exec_statefn_simulatesD)
   apply (elim disjE exE)
     apply (drule(1) exec_statefn_simulatesD, simp)
     apply (auto intro: exec.intros)[1]
    apply (fastforce intro: exec.intros)
   apply (fastforce intro: exec.intros)
  apply (drule(2) exec_statefn_simulatesD)
  apply (fastforce intro: exec.intros)
  done

lemma exec_statefn_simulates_Guard_rhs:
  "exec_statefn_simulates f (S \<inter> {s. f s \<in> G}) T a b
    \<Longrightarrow> exec_statefn_simulates f S T a (Guard E G b)"
  apply (rule exec_statefn_simulatesI)
  apply (case_tac "f s \<in> G")
   apply (drule(1) exec_statefn_simulatesD, simp)
   apply (auto intro: exec.intros)
  done

lemma exec_statefn_simulates_Guard_lhs:
  "\<lbrakk> S \<subseteq> G; exec_statefn_simulates f S T a b \<rbrakk>
     \<Longrightarrow> exec_statefn_simulates f S T (Guard E G a) b"
  apply (rule exec_statefn_simulatesI)
  apply (erule exec.cases, simp_all)
   apply (drule(1) exec_statefn_simulatesD, simp)
   apply (auto intro: exec.intros)
  done

lemmas exec_statefn_simulates_whileAnno
    = exec_statefn_simulates_While[folded whileAnno_def[where I=I and V=V]] for I V

lemma exec_statefn_simulates_Basic:
  "\<lbrakk> \<And>s. \<lbrakk> s \<in> S; g (fn s) \<notin> fn ` (- T) \<rbrakk> \<Longrightarrow> fn (f s) = g (fn s) \<rbrakk>
      \<Longrightarrow> exec_statefn_simulates fn S T (Basic f) (Basic g)"
  apply atomize
  apply (rule exec_statefn_simulatesI)
  apply (erule exec.cases, simp_all, clarsimp)
  apply (drule spec, drule(1) mp)
  apply (drule mp)
   apply clarsimp
   apply (metis exec.Basic Compl_iff)
  apply clarsimp
  apply (blast intro: exec.Basic)
  done

lemma exec_statefn_simulates_Call:
  "bij f \<Longrightarrow> exec_statefn_simulates f S T (Call c) (Call c)"
  apply (rule exec_statefn_simulatesI)
  apply (intro disjI1)
  apply (erule exec.cases, simp_all)
   apply (rule exec.intros, simp)
   apply (simp add: add_statefn_exec bij_imp_bij_inv option.map_comp o_def
                    inv_inv_eq)
   apply (simp add: add_statefn_comp
                    inj_iff[THEN iffD1, OF bij_is_inj] inv_inv_eq bij_imp_bij_inv
                    map_option_case inv_f_f[OF bij_is_inj] add_statefn_xstate_comp)
  apply (fastforce intro: exec.intros)
  done

lemma exec_statefn_simulates_DynCom:
  "\<lbrakk> \<And>s. s \<in> S \<Longrightarrow> exec_statefn_simulates f S T (g s) (h (f s)) \<rbrakk>
      \<Longrightarrow> exec_statefn_simulates f S T (DynCom g) (DynCom h)"
  apply atomize
  apply (clarsimp simp add: exec_statefn_simulates_def)
  apply (erule exec.cases, simp_all)
  apply (fastforce intro: exec.intros)
  done

lemma exec_statefn_simulates_Skip_Throw:
  "exec_statefn_simulates f S T Skip Skip"
  "exec_statefn_simulates f S T Throw Throw"
  apply (simp_all add: exec_statefn_simulates_def)
  apply (fastforce elim: exec.cases intro: exec.intros)+
  done

lemma exec_statefn_simulates_call:
  "\<lbrakk> bij f; \<And>s. s \<in> S \<Longrightarrow> f (init1 s) = init2 (f s);
            \<And>s t. f (ret1 s t) = ret2 (f s) (f t);
            \<And>s t. exec_statefn_simulates f UNIV T (save1 s t) (save2 (f s) (f t)) \<rbrakk>
      \<Longrightarrow> exec_statefn_simulates f S T (call init1 c ret1 save1) (call init2 c ret2 save2)"
  apply (simp add: call_def block_def)
  apply (intro exec_statefn_simulates_Seq exec_statefn_simulates_Catch
               exec_statefn_simulates_DynCom
               exec_statefn_simulates_Basic exec_statefn_simulates_Call
               exec_statefn_simulates_Skip_Throw)
  apply simp+
  done

lemma exec_statefn_simulates_creturn_void:
  "\<lbrakk> \<And>inn s. s \<in> S \<Longrightarrow> f (exn_upd inn s) = exn_upd' inn (f s) \<rbrakk>
      \<Longrightarrow> exec_statefn_simulates f S T (creturn_void exn_upd)
                (creturn_void exn_upd')"
  apply (simp add: creturn_void_def)
  apply (intro exec_statefn_simulates_Seq exec_statefn_simulates_Basic
               exec_statefn_simulates_Skip_Throw | simp)+
  done

lemma exec_statefn_simulates_creturn:
  "\<lbrakk> \<And>inn s. f (exn_upd inn s) = exn_upd' inn (f s);
       \<And>inn s. s \<in> S \<Longrightarrow> f (rv_upd inn s) = rv_upd' inn (f s);
       \<And>inn s. s \<in> S \<Longrightarrow> rv s = rv' (f s) \<rbrakk>
      \<Longrightarrow> exec_statefn_simulates f S T (creturn exn_upd rv_upd rv)
                (creturn exn_upd' rv_upd' rv')"
  apply (simp add: creturn_def)
  apply (intro exec_statefn_simulates_Seq exec_statefn_simulates_Basic
               exec_statefn_simulates_Skip_Throw | simp)+
  done

lemma exec_statefn_simulates_cbreak:
  "\<lbrakk> \<And>inn s. s \<in> S \<Longrightarrow> f (exn_upd inn s) = exn_upd' inn (f s) \<rbrakk>
      \<Longrightarrow> exec_statefn_simulates f S T (cbreak exn_upd)
                (cbreak exn_upd')"
  apply (simp add: cbreak_def)
  apply (intro exec_statefn_simulates_Seq exec_statefn_simulates_Basic
               exec_statefn_simulates_Skip_Throw | simp)+
  done

lemma exec_statefn_simulates_ccatchbrk:
  "\<lbrakk> \<And>s. s \<in> S \<Longrightarrow> exn' (f s) = exn s \<rbrakk>
      \<Longrightarrow> exec_statefn_simulates f S T (ccatchbrk exn)
                (ccatchbrk exn')"
  apply (simp add: ccatchbrk_def)
  apply (intro exec_statefn_simulates_Cond
               exec_statefn_simulates_Skip_Throw | simp)+
  done

lemma exec_statefn_simulates_Spec:
  "\<lbrakk> bij f; \<And>s. \<lbrakk> s \<in> S; \<forall>t. (f s, f t) \<in> R' \<longrightarrow> t \<in> T \<rbrakk>
            \<Longrightarrow> \<forall>t. ((s, t) \<in> R) = ((f s, f t) \<in> R') \<rbrakk>
      \<Longrightarrow> exec_statefn_simulates f S T (Spec R) (Spec R')"
  apply (rule exec_statefn_simulatesI)
  apply (erule exec_Normal_elim_cases, simp_all)
   apply (blast intro: exec.Spec)
  apply (case_tac "\<forall>t. (f s, f t) \<in> R' \<longrightarrow> t \<in> T")
   apply clarsimp
   apply (subgoal_tac "\<forall>t. (f s, f (inv f t)) \<notin> R'")
    apply (simp add: surj_f_inv_f bij_is_surj)
    apply (blast intro: exec.SpecStuck)
   apply clarsimp
  apply (blast intro: exec.Spec)
  done

lemmas exec_statefn_simulates_comI
    = exec_statefn_simulates_refl
      exec_statefn_simulates_Seq exec_statefn_simulates_Cond
      exec_statefn_simulates_While exec_statefn_simulates_whileAnno
      exec_statefn_simulates_Catch
      exec_statefn_simulates_Guard_rhs
      exec_statefn_simulates_Guard_lhs
      exec_statefn_simulates_Call exec_statefn_simulates_call
      exec_statefn_simulates_Skip_Throw
      exec_statefn_simulates_Basic
      exec_statefn_simulates_creturn
      exec_statefn_simulates_creturn_void
      exec_statefn_simulates_cbreak
      exec_statefn_simulates_ccatchbrk
      exec_statefn_simulates_Spec

lemma exec_statefn_simulates_additional_Guards:
  "exec_statefn_simulates f S T a (b ;; Guard F (G \<inter> G') c)
        \<Longrightarrow> exec_statefn_simulates f S T a (b ;; Guard F G (Guard F' G' c))"
  apply (rule exec_statefn_simulatesI)
  apply (drule(2) exec_statefn_simulatesD)
  apply (elim disjE exE)
    apply (erule exec_Normal_elim_cases)
    apply (case_tac s', auto elim!: exec_Normal_elim_cases,
           (blast intro: exec.Seq exec.Guard exec.GuardFault)+)[1]
   apply (erule exec_Normal_elim_cases)
   apply (case_tac s', auto elim!: exec_Normal_elim_cases,
          (blast intro: exec.Seq exec.Guard exec.GuardFault)+)[1]
  apply (clarsimp elim!: exec_Normal_elim_cases)
  apply (case_tac s', auto elim!: exec_Normal_elim_cases,
         (blast intro: exec.Seq exec.Guard exec.GuardFault)+)[1]
  done

lemma exec_statefn_simulates_additional_Guarded_Skip:
  "exec_statefn_simulates f S (T \<inter> {s. f s \<in> G}) a b
        \<Longrightarrow> exec_statefn_simulates f S T a (b ;; Guard F G Skip)"
  apply (rule exec_statefn_simulatesI)
  apply (drule(2) exec_statefn_simulatesD)
  apply (elim disjE exE)
    apply (case_tac t, auto elim!: exec_Normal_elim_cases,
           (blast intro: exec.Seq exec.Skip exec.Guard exec.GuardFault)+)[1]
   apply (case_tac t, auto elim!: exec_Normal_elim_cases,
          (blast intro: exec.Seq exec.Skip exec.Guard exec.GuardFault)+)[1]
  apply (blast intro: exec.Seq exec.Skip exec.Guard exec.GuardFault)
  done

lemmas exec_statefn_simulates_additionals
    = exec_statefn_simulates_additional_Guarded_Skip
      exec_statefn_simulates_additional_Guards

inductive
  guards_adjust_by_invariant :: "'s set \<Rightarrow> 's set \<Rightarrow>
        ('s, 'x, 'e) com \<Rightarrow> ('s, 'x, 'e) com \<Rightarrow> bool"
where
    gabi_Skip: "guards_adjust_by_invariant S T Skip Skip"
  | gabi_Guard: "\<lbrakk> S \<inter> T \<inter> G = S \<inter> T \<inter> G';
                guards_adjust_by_invariant S (T \<inter> G) c c' \<rbrakk>
        \<Longrightarrow> guards_adjust_by_invariant S T (Guard F G c) (Guard F G' c')"
  | gabi_Basic: "\<lbrakk> \<And>s. \<lbrakk> s \<in> S; s \<in> T \<rbrakk> \<Longrightarrow> f s \<in> S \<rbrakk>
        \<Longrightarrow> guards_adjust_by_invariant S T (Basic f) (Basic f)"
  | gabi_Spec: "\<lbrakk> \<And>s t. \<lbrakk> s \<in> S; s \<in> T; (s, t) \<in> R \<rbrakk> \<Longrightarrow> t \<in> S \<rbrakk>
        \<Longrightarrow> guards_adjust_by_invariant S T (Spec R) (Spec R)"
  | gabi_Seq: "\<lbrakk> guards_adjust_by_invariant S T c d;
                    guards_adjust_by_invariant S UNIV c' d' \<rbrakk>
        \<Longrightarrow> guards_adjust_by_invariant S T (Seq c c') (Seq d d')"
  | gabi_Cond: "\<lbrakk> guards_adjust_by_invariant S T c d;
                    guards_adjust_by_invariant S T c' d' \<rbrakk>
        \<Longrightarrow> guards_adjust_by_invariant S T (Cond C c c') (Cond C d d')"
  | gabi_While: "\<lbrakk> guards_adjust_by_invariant S UNIV c d \<rbrakk>
        \<Longrightarrow> guards_adjust_by_invariant S T (While C c) (While C d)"
  | gabi_Call :"guards_adjust_by_invariant S T (Call proc) (Call proc)"
  | gabi_Dyncom :"\<lbrakk> \<And>s. \<lbrakk> s \<in> S; s \<in> T \<rbrakk> \<Longrightarrow>
                    guards_adjust_by_invariant S T (f s) (f' s) \<rbrakk>
        \<Longrightarrow> guards_adjust_by_invariant S T (DynCom f) (DynCom f')"
  | gabi_Throw: "guards_adjust_by_invariant S T Throw Throw"
  | gabi_Catch: "\<lbrakk> guards_adjust_by_invariant S T c d;
                    guards_adjust_by_invariant S UNIV c' d' \<rbrakk>
        \<Longrightarrow> guards_adjust_by_invariant S T (Catch c c') (Catch d d')"

definition
  context_gabi :: "'s set \<Rightarrow>
        ('x \<rightharpoonup> ('s, 'x, 'e) com) \<Rightarrow> ('x \<rightharpoonup> ('s, 'x, 'e) com) \<Rightarrow> bool"
where
  "context_gabi S G G' = (\<forall>x. (G x = None) = (G' x = None)
    \<and> (G x \<noteq> None \<longrightarrow> guards_adjust_by_invariant S UNIV (the (G x)) (the (G' x))))"

definition
  xstate_inv_set :: "'s set \<Rightarrow> ('s, 'e) xstate set"
where
  "xstate_inv_set S = {xs. case xs of Normal s \<Rightarrow> s \<in> S
            | Abrupt s \<Rightarrow> s \<in> S | _ \<Rightarrow> True}"

lemmas xstate_inv_set_simps
    = xstate_inv_set_def[THEN eqset_imp_iff, simplified,
            split_simps xstate.split]

lemma xstate_inv_set_UNIV:
  "xstate_inv_set UNIV = UNIV"
  by (simp add: xstate_inv_set_def split: xstate.split)

method gs_simple_cases =
  (simp_all add: xstate_inv_set_simps,
   ((erule guards_adjust_by_invariant.cases, simp_all)[1],
     clarsimp simp: xstate_inv_set_simps,
     (fastforce intro: exec.intros guards_adjust_by_invariant.intros)[1])+)

method gs_case methods m uses g_def =
  ((erule guards_adjust_by_invariant.cases; simp),
   clarsimp simp: g_def xstate_inv_set_simps,
   m,
   auto intro: exec.intros guards_adjust_by_invariant.intros)[1]

lemma gabi_simulation:
  "\<lbrakk> G \<turnstile> \<langle>c, xs\<rangle> \<Rightarrow> xs';
        guards_adjust_by_invariant S T c c';
        xs \<in> xstate_inv_set (S \<inter> T); context_gabi S G G' \<rbrakk>
    \<Longrightarrow> G' \<turnstile> \<langle>c', xs\<rangle> \<Rightarrow> xs' \<and> xs' \<in> xstate_inv_set S"
proof (induct arbitrary: c' T rule: exec.induct)
  case (Call proc bdy s t)
  show ?case using Call.prems Call.hyps
    by - (gs_case \<open>drule_tac x=proc in spec\<close> g_def: context_gabi_def)
next
  case (CallUndefined proc s t)
  show ?case using CallUndefined.prems CallUndefined.hyps
    by - (gs_case \<open>drule_tac x=proc in spec\<close> g_def: context_gabi_def)
next
  case (WhileTrue s S c s' t)
  show ?case using WhileTrue.prems WhileTrue.hyps
    by - (gs_case \<open>(erule_tac x=UNIV in meta_allE)+\<close>)
qed gs_simple_cases


end
