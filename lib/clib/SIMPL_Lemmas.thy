(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory SIMPL_Lemmas
imports
  "Lib.HaskellLemmaBucket"
  "CTranslationNICTA"
begin

lemma Cond_true:
  "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> P t Q, A \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (P \<inter> b) Cond b t f Q, A"
  apply (rule hoare_complete)
  apply (drule hoare_sound)
  apply (clarsimp simp: HoarePartialDef.cvalid_def HoarePartialDef.valid_def)
  apply (erule exec_Normal_elim_cases)
   apply fastforce
  apply simp
  done

lemma Cond_false:
  "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> P f Q, A \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> (P \<inter> - b) Cond b t f Q, A"
  apply (rule hoare_complete)
  apply (drule hoare_sound)
  apply (clarsimp simp: HoarePartialDef.cvalid_def HoarePartialDef.valid_def)
  apply (erule exec_Normal_elim_cases)
   apply simp
  apply fastforce
  done

lemma update_desc_def_ext:
  "update_desc x y = (\<lambda>d. \<lparr>field_access = field_access d \<circ> x, field_update = \<lambda>bs v. y (field_update d bs (x v)) v\<rparr>)"
  apply (rule ext)
  apply (simp add: update_desc_def)
  done

lemma adjust_ti_adjust_ti:
  "adjust_ti (adjust_ti t xf xfu) xf' xfu' = adjust_ti t (xf \<circ> xf') (\<lambda>c a. xfu' (xfu c (xf' a)) a)"
  unfolding adjust_ti_def
  by (simp add: map_td_map comp_def update_desc_def_ext)

lemma fg_cons_comp:
  assumes fg: "fg_cons xf xfu"
  and     fg': "fg_cons xf' xfu'"
  shows "fg_cons (xf \<circ> xf') (\<lambda>c a. xfu' (xfu c (xf' a)) a)"
  using fg fg' unfolding fg_cons_def
  by clarsimp

(* Generalise *)
lemma hoarep_Int:
  fixes P' :: "'a set" and P :: "'a set"
  assumes s1: "\<Gamma> \<turnstile> P c Q"
  and     s2: "\<Gamma> \<turnstile> P' c Q'"
  shows   "\<Gamma> \<turnstile> (P \<inter> P') c (Q \<inter> Q')"
  using s1 s2
  apply -
  apply (rule hoare_complete)
  apply (drule hoare_sound)+
  apply (clarsimp simp add: cvalid_def HoarePartialDef.valid_def)
  apply (drule spec, drule spec, drule (1) mp)
  apply (drule spec, drule spec, drule (1) mp)
  apply fastforce
  done


lemma Normal_result:
  "\<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> Normal t' \<Longrightarrow> \<exists>t. s = Normal t"
proof (induct c arbitrary: s)
  case While
  thus ?case
    by - (erule exec_elim_cases, simp_all)
qed (fastforce elim: exec_elim_cases)+

lemma Normal_resultE:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> Normal t'; \<And>t. \<lbrakk> \<Gamma> \<turnstile> \<langle>c, Normal t\<rangle> \<Rightarrow> Normal t'; s = Normal t\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (frule Normal_result)
  apply auto
  done

lemma Abrupt_result:
  "\<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> Abrupt t' \<Longrightarrow> \<exists>t. s = Normal t \<or> s = Abrupt t"
proof (induct c arbitrary: s)
  case While
  thus ?case
    by - (erule exec_elim_cases, simp_all)
qed (fastforce elim: exec_elim_cases)+

lemma Abrupt_resultE [consumes 1, case_names normal abrupt]:
  "\<lbrakk>\<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> Abrupt t';
  \<And>t. \<lbrakk>\<Gamma> \<turnstile> \<langle>c, Normal t\<rangle> \<Rightarrow> Abrupt t'; s = Normal t \<rbrakk> \<Longrightarrow> P;
  \<And>t. \<lbrakk>\<Gamma> \<turnstile> \<langle>c, Abrupt t\<rangle> \<Rightarrow> Abrupt t'; s = Abrupt t \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (frule Abrupt_result)
  apply auto
  done

lemma Fault_result:
  assumes ex: "\<Gamma> \<turnstile> \<langle>a, s\<rangle> \<Rightarrow> t"
  and      t: "t = Fault f"
  shows    "s = Fault f \<or> (\<exists>s'. s = Normal s')"
  using ex t by induct auto

lemma Fault_resultE:
  assumes ex: "\<Gamma> \<turnstile> \<langle>a, s\<rangle> \<Rightarrow> Fault f"
  and     r1: "\<lbrakk> \<Gamma> \<turnstile> \<langle>a, Fault f\<rangle> \<Rightarrow> Fault f; s = Fault f \<rbrakk> \<Longrightarrow> P"
  and     r2: "\<And>s'. \<lbrakk> \<Gamma> \<turnstile> \<langle>a, Normal s'\<rangle> \<Rightarrow> Fault f; s = Normal s'\<rbrakk> \<Longrightarrow> P"
  shows   P
  using ex
  apply -
  apply (frule Fault_result [OF _ refl])
  apply (erule disjE)
   apply (rule r1, simp_all)
  apply (erule exE)
  apply (rule r2, simp_all)
  done

lemma Stuck_result:
  assumes ex: "\<Gamma> \<turnstile> \<langle>a, s\<rangle> \<Rightarrow> t"
  and      t: "t = Stuck"
  shows    "s = Stuck \<or> (\<exists>s'. s = Normal s')"
  using ex t by induct auto

lemma Stuck_resultE:
  assumes ex: "\<Gamma> \<turnstile> \<langle>a, s\<rangle> \<Rightarrow> Stuck"
  and     r1: "\<lbrakk> \<Gamma> \<turnstile> \<langle>a, Stuck\<rangle> \<Rightarrow> Stuck; s = Stuck \<rbrakk> \<Longrightarrow> P"
  and     r2: "\<And>s'. \<lbrakk> \<Gamma> \<turnstile> \<langle>a, Normal s'\<rangle> \<Rightarrow> Stuck; s = Normal s'\<rbrakk> \<Longrightarrow> P"
  shows   P
  using ex
  apply -
  apply (frule Stuck_result [OF _ refl])
  apply (erule disjE)
   apply (rule r1, simp_all)
  apply (erule exE)
  apply (rule r2, simp_all)
  done

(* This is essentially semantic equivalence, assuming equality of xf and v at s *)

definition
  "ceqv \<Gamma> xf v s s' a b \<equiv>
  xf s = v \<longrightarrow> (\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> s') = (\<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> s')"

lemma ceqvI:
  assumes rl: "xf s = v \<Longrightarrow> (\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> s') = (\<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> s')"
  shows   "ceqv \<Gamma> xf v s s' a b"
  using rl  unfolding ceqv_def by auto

lemma ceqvD1:
  assumes lhs: "\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> s'"
  and     xf:  "xf s = v"
  and     ceq: "ceqv \<Gamma> xf v s s' a b"
  shows   "\<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> s'"
  using ceq xf lhs unfolding ceqv_def by auto

lemma ceqvD2:
  assumes lhs: "\<Gamma> \<turnstile> \<langle>b, Normal s\<rangle> \<Rightarrow> s'"
  and     xf:  "xf s = v"
  and     ceq: "ceqv \<Gamma> xf v s s' a b"
  shows   "\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> s'"
  using ceq xf lhs unfolding ceqv_def by auto

lemma ceqv_sym [sym]:
  "ceqv \<Gamma> xf' rv' t t' c c' \<Longrightarrow> ceqv \<Gamma> xf' rv' t t' c' c"
  unfolding ceqv_def by auto

lemma exec_eq_is_valid_eq0:
  fixes P :: "'a set"
  assumes eq: "\<And>t t'. (\<Gamma> \<turnstile> \<langle>a, Normal t\<rangle> \<Rightarrow> t') = (\<Gamma> \<turnstile> \<langle>a', Normal t\<rangle> \<Rightarrow> t')"
  and     vl: "\<Gamma> \<turnstile> P a Q"
  shows   "\<Gamma> \<turnstile> P a' Q"
  using vl
  apply -
  apply (drule hoare_sound)
  apply (rule hoare_complete)
  apply (simp add: HoarePartialDef.valid_def cvalid_def)
  apply (intro allI impI)
  apply clarsimp
  apply (subst (asm) eq [symmetric])
  apply (drule spec, drule spec, drule (1) mp)
  apply simp
  done

lemma exec_eq_is_valid_eq:
  fixes P :: "'a set"
  assumes eq: "\<And>t t'. (\<Gamma> \<turnstile> \<langle>a, Normal t\<rangle> \<Rightarrow> t') = (\<Gamma> \<turnstile> \<langle>a', Normal t\<rangle> \<Rightarrow> t')"
  shows     vl: "(\<Gamma> \<turnstile> P a Q) = (\<Gamma> \<turnstile> P a' Q)"
  apply rule
   apply (erule exec_eq_is_valid_eq0 [OF eq])
  apply (erule exec_eq_is_valid_eq0 [OF eq [symmetric]])
  done

lemma Int_eq_symmetric:
  "A \<inter> {s. x s = y s} = A \<inter> {s. y s = x s}"
  by auto

lemma ceqv_refl:
  "ceqv \<Gamma> xf' rv' t t' c c"
  unfolding ceqv_def by auto

lemma ceqv_trans:
  "\<lbrakk> ceqv \<Gamma> xf' rv' t t' c c'; ceqv \<Gamma> xf' rv' t t' c' c'' \<rbrakk> \<Longrightarrow> ceqv \<Gamma> xf' rv' t t' c c''"
  unfolding ceqv_def by auto

(* A bit yuck, might be better to define the other way around *)
definition
  "semantic_equiv \<Gamma> \<equiv> ceqv \<Gamma> (\<lambda>_. ()) ()"

lemma semantic_equiv_sym:
  "semantic_equiv \<Gamma> s s' a b = semantic_equiv \<Gamma> s s' b a"
  unfolding semantic_equiv_def by (auto intro: ceqv_sym)

lemma semantic_equivI:
  "(\<Gamma>\<turnstile> \<langle>a,Normal s\<rangle> \<Rightarrow> s' = \<Gamma>\<turnstile> \<langle>b,Normal s\<rangle> \<Rightarrow> s') \<Longrightarrow> semantic_equiv \<Gamma> s s' a b"
  unfolding semantic_equiv_def by (auto intro: ceqvI)

lemmas semantic_equivD1 = ceqvD1 [where xf = "\<lambda>_. ()" and v = "()", folded semantic_equiv_def]
lemmas semantic_equivD2 = ceqvD2 [where xf = "\<lambda>_. ()" and v = "()", folded semantic_equiv_def]

lemma Guard_Seq_semantic_equiv:
  "semantic_equiv \<Gamma> s s' (Guard F S c ;; d) (Guard F S (c ;; d))"
  by (auto elim!: exec_Normal_elim_cases intro: semantic_equivI exec.intros)

lemma exec_Seq_cong:
  "\<lbrakk> \<And>s''. \<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> s'' = \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s'';
     \<And>s''. \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Normal s''
         \<Longrightarrow> \<Gamma> \<turnstile> \<langle>b, Normal s''\<rangle> \<Rightarrow> s' = \<Gamma> \<turnstile> \<langle>d, Normal s''\<rangle> \<Rightarrow> s' \<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile> \<langle>a ;; b, Normal s\<rangle> \<Rightarrow> s' = \<Gamma> \<turnstile> \<langle>c ;; d, Normal s\<rangle> \<Rightarrow> s'"
  apply (rule iffI)
   apply (erule exec_Normal_elim_cases)
   apply (case_tac "s'a", auto elim!: exec_elim_cases intro: exec.intros)[1]
  apply (erule exec_Normal_elim_cases)
  apply (case_tac "s'a", auto elim!: exec_elim_cases intro: exec.intros)[1]
  done

lemma exec_While_cong':
  assumes c: "\<And>s s'. \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s' = \<Gamma> \<turnstile> \<langle>c', Normal s\<rangle> \<Rightarrow> s'"
  assumes w: "\<Gamma> \<turnstile> \<langle>v, Normal s\<rangle> \<Rightarrow> s'"
  assumes eq: "v = While S c" "v' = While S c'"
  shows      "\<Gamma> \<turnstile> \<langle>v', Normal s\<rangle> \<Rightarrow> s'"
  using w eq
  apply (induct, simp_all)
   apply (rule exec.intros, assumption)
    apply (simp add: c)
   apply simp
  apply (rule exec.intros, assumption)
  done

lemma exec_While_cong:
  "\<lbrakk> \<And>s s'. \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s' = \<Gamma> \<turnstile> \<langle>c', Normal s\<rangle> \<Rightarrow> s' \<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile> \<langle>While S c, Normal s\<rangle> \<Rightarrow> s' = \<Gamma> \<turnstile> \<langle>While S c', Normal s\<rangle> \<Rightarrow> s'"
  apply (rule iffI)
   apply (erule(1) exec_While_cong'[OF _ _ refl refl])
  apply (erule(1) exec_While_cong'[OF sym _ refl refl])
  done

lemma exec_Guard_UNIV_simp:
  "\<Gamma> \<turnstile> \<langle>Guard F UNIV c, Normal s\<rangle> \<Rightarrow> s' = \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s'"
  by (auto elim!: exec_Normal_elim_cases intro: exec.intros)

lemma exec_Seq_Skip_simps:
  "\<Gamma> \<turnstile> \<langle>Skip ;; c, Normal s\<rangle> \<Rightarrow> s' = \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s'"
  "\<Gamma> \<turnstile> \<langle>c ;; Skip, Normal s\<rangle> \<Rightarrow> s' = \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> s'"
  apply (rule iffI)
    apply (clarsimp elim!: exec_Normal_elim_cases exec_elim_cases)
   apply (fastforce intro: exec.intros)
  apply (rule iffI)
   apply (clarsimp elim!: exec_Normal_elim_cases exec_elim_cases)
   apply (case_tac s'a, auto elim!: exec_elim_cases)[1]
  apply (case_tac s', auto intro: exec.intros)
  done

lemma exec_normal:
  assumes asms: "s' \<in> P'"
  and     ce: "\<Gamma> \<turnstile> \<langle>c, Normal s'\<rangle> \<Rightarrow> Normal t'"
  and valid': "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> P' c Q', A'"
  shows   "t' \<in> Q'"
  using valid' ce asms
  apply -
  apply (drule hoare_sound)
  apply (clarsimp elim: exec_Normal_elim_cases
    simp: NonDetMonad.bind_def cvalid_def split_def HoarePartialDef.valid_def)
  apply (drule spec, drule spec, drule (1) mp)
  apply auto
  done

lemma exec_abrupt:
  assumes asms: "s' \<in> P'"
  and     ce: "\<Gamma> \<turnstile> \<langle>c, Normal s'\<rangle> \<Rightarrow> Abrupt t'"
  and valid': "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> P' c Q', A'"
  shows   "t' \<in> A'"
  using valid' ce asms
  apply -
  apply (drule hoare_sound)
  apply (clarsimp elim: exec_Normal_elim_cases
    simp: NonDetMonad.bind_def cvalid_def split_def HoarePartialDef.valid_def)
  apply (drule spec, drule spec, drule (1) mp)
  apply auto
  done


(* Used so we don't simp it in ctac *)
definition
  "guard_is_UNIV r xf Q \<equiv> \<forall>s rv. r rv (xf s) \<longrightarrow> s \<in> Q rv (xf s)"

lemma guard_is_UNIVI:
  "(\<And>s rv. r rv (xf s) \<Longrightarrow> s \<in> Q rv (xf s)) \<Longrightarrow> guard_is_UNIV r xf Q"
  unfolding guard_is_UNIV_def by simp

lemma guard_is_UNIVD:
  "\<lbrakk> guard_is_UNIV r xf Q; r rv (xf s) \<rbrakk> \<Longrightarrow> s \<in> Q rv (xf s)"
  unfolding guard_is_UNIV_def by auto

definition
  isNormal::"('s,'f) xstate \<Rightarrow> bool"
where
  "isNormal S \<equiv> \<exists>s. S=Normal s"

lemma isNormal_simps:
  "isNormal (Normal s) = True"
  "isNormal (Abrupt s) = False"
  "isNormal (Fault f) = False"
  "isNormal Stuck = False"
  by (auto simp add: isNormal_def)


lemma hoarep_revert:
  "Gamm \<turnstile> P (call (\<lambda>s. s) fnname (\<lambda>a b. b) (\<lambda>i t. Basic (\<lambda>s. s))) Q,R
     \<Longrightarrow> Gamm \<turnstile> P (Call fnname) Q,R"
  apply (rule hoare_complete)
  apply (drule hoare_sound)
  apply (simp add: cvalid_def HoarePartialDef.valid_def)
  apply (erule allEI)+
  apply (rule impI, drule mp)
   apply (erule exec.cases, simp_all)[1]
    apply (case_tac ta, simp_all)[1]
       apply (erule exec_call)
        apply simp
       apply (rule exec.intros)
      apply (erule exec_callAbrupt, simp_all)[1]
     apply (erule exec_callFault, simp_all)[1]
    apply (erule exec_callStuck, simp_all)[1]
   apply (erule exec_callUndefined)
  apply simp
  done


end
