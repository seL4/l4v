(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CCorresLemmas
imports CCorres_Rewrite
begin

lemma ccorres_rel_imp2:
  "\<lbrakk> ccorres_underlying sr \<Gamma> r' xf' arrel' axf' P P' hs a b;
        \<And>rv s. \<lbrakk> r' rv (xf' s) \<rbrakk> \<Longrightarrow> r rv (xf s);
        \<And>rv s. \<lbrakk> arrel' rv (axf' s); hs \<noteq> [] \<rbrakk> \<Longrightarrow> arrel rv (axf s) \<rbrakk>
     \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a b"
  apply (rule ccorresI', erule(5) ccorresE)
  apply simp
  apply (erule rev_bexI)
  apply (simp add: unif_rrel_def split: if_split_asm)
  apply (cases "hs = []", simp_all)
  done

lemma ccorres_nohs:
  "ccorres_underlying sr \<Gamma> r xf r xf P P' [] a b
      \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a b"
  apply (rule ccorres_handlers_weaken)
  apply (erule ccorres_rel_imp2, simp+)
  done

lemma ccorres_from_vcg_throws:
  "(\<forall>\<sigma>. \<Gamma> \<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> srel}
  c
  {}, {s. \<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> srel \<and> arrel rv (axf s)})
  \<Longrightarrow> ccorres_underlying srel \<Gamma> r xf arrel axf P P' (SKIP # hs) a c"
  apply (rule ccorresI')
  apply (drule_tac x = s in spec)
  apply (drule hoare_sound)
  apply (simp add: HoarePartialDef.valid_def cvalid_def)
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (drule spec, drule spec, drule (1) mp)
    apply (clarsimp dest!: exec_handlers_SkipD
                     simp: split_def unif_rrel_simps elim!: bexI [rotated])
   apply clarsimp
   apply (drule spec, drule spec, drule (1) mp)
   apply clarsimp
  apply simp
  done

lemma ccorres_liftE_Seq:
  assumes cc: "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs (a >>= b) (c ;; d)"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs (liftE a >>=E b) (c ;; d)"
  apply (simp add: liftE_bindE cc)
  done

declare snd_return [simp]
declare snd_throwError [simp]
declare snd_lift_Inr [simp]
declare snd_lift_Inl [simp]

lemma exec_handlers_Hoare_Post:
  "\<lbrakk> exec_handlers_Hoare \<Gamma> P c Q' A'; Q' \<subseteq> Q; A' \<subseteq> A \<rbrakk>
      \<Longrightarrow> exec_handlers_Hoare \<Gamma> P c Q A"
  apply (simp add: exec_handlers_Hoare_def
             split del: if_split)
  apply (elim allEI)
  apply (simp split: if_split_asm)
   apply blast+
  done

lemma ccorres_can't_happen:
  "ccorres_underlying st \<Gamma> r xf arrel axf \<bottom> G hs a b"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_gen_asm [where P = False])
    apply simp
  apply simp
  done

lemma ccorres_can't_happen2:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G {} hs a b"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_gen_asm2 [where P = False])
    apply simp
  apply simp
  done

lemmas ccorres_can't_happen_both = ccorres_can't_happen [where G = "{}"]
declare ccorres_can't_happen_both


lemma exec_handlers_Hoare_from_vcg_might_fail:
  "\<lbrakk> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> P c Q, A; UNIV \<subseteq> A' \<rbrakk>
    \<Longrightarrow> exec_handlers_Hoare \<Gamma> P (c # hs) Q A'"
  apply (clarsimp simp: exec_handlers_Hoare_def
             split del: if_split split: if_split_asm)
   apply (erule exec_handlers.cases, simp_all)
    apply (case_tac hsa, simp_all)
     apply (erule exec_handlers.cases, simp_all)
    apply (frule exec_handlers_Cons_le, simp)
   apply (drule hoare_sound)
   apply (clarsimp simp: cvalid_def HoarePartialDef.valid_def)
   apply fastforce
  apply blast
  done

lemmas exec_handlers_Hoare_from_vcg_might_fail_UNIV
    = exec_handlers_Hoare_from_vcg_might_fail[where A=UNIV, OF _ subset_refl]

lemma ccorres_rel_imp_guard:
  fixes Q' :: "'a set"
  assumes x: "ccorres_underlying sr \<Gamma> r' xf' arrel axf P P' hs f g"
  and     y: "\<And>x s s'. \<lbrakk> (s, s') \<in> sr; R x s; s' \<in> R'; r' x (xf' s') \<rbrakk> \<Longrightarrow> r x (xf s')"
  and valid:  "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>"
  and valid': "\<Gamma> \<turnstile> Q' g R', R'"
  and wfh:   "\<And>t t' n. \<Gamma>\<turnstile>\<^sub>h \<langle>hs,t\<rangle> \<Rightarrow> (n, Normal t') \<Longrightarrow> t = t'"
  shows      "ccorres_underlying sr \<Gamma> r xf arrel axf (P and Q) (P' \<inter> Q') hs f g"
  using x
  apply -
  apply (rule ccorresI')
  apply clarsimp
  apply (erule (5) ccorresE)
  apply (frule (1) use_valid [OF _ valid])
  apply simp
  apply (clarsimp elim!: bexI [rotated] simp: unif_rrel_def)
  apply (erule y, simp_all)
  apply (frule exec_handlers_Hoare_NormalD[rotated 2])
     apply simp
    apply (rule exec_handlers_Hoare_from_vcg_might_fail[OF valid' order_refl])
   apply assumption+
  done

lemma ccorres_if_cond_throws:
  fixes e :: 'e
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> Q s \<and> Q' s' \<longrightarrow> P = (s' \<in> P')"
  and     ac: "P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf R R' (SKIP # hs) a c"
  and     bd: "\<not> P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf U U' (SKIP # hs) b d"
  and cthrows: "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> PT' c {}, UNIV" \<comment> \<open>c always throws\<close>
  shows  "ccorres_underlying sr \<Gamma> r xf arrel axf
          (Q and (\<lambda>s. P \<longrightarrow> R s) and (\<lambda>s. \<not> P \<longrightarrow> U s))
          (Collect Q' \<inter> {s. (s \<in> P' \<longrightarrow> s \<in> R' \<inter> PT') \<and> (s \<notin> P' \<longrightarrow> s \<in> U')})
          (SKIP # hs)
          (if P then a else b) (Cond P' c SKIP ;; d)"
  (is "ccorres_underlying sr \<Gamma> r xf arrel axf ?G ?G' ?hs ?a ?c")
proof (cases P)
  case True

  thus ?thesis
    apply simp
    apply (rule ccorres_guard_imp2)
    apply (rule ccorres_split_throws)
    apply (rule ccorres_cond_true [OF ac [OF True]])
    apply (rule HoarePartial.Cond [where P = "P' \<inter> PT'", OF _ cthrows])
    apply clarsimp
    apply (rule HoarePartial.Skip)
    apply (rule subset_refl)
    apply (clarsimp simp: abs [rule_format, OF conjI])
    done
next
  case False

  thus ?thesis
    apply simp
    apply (rule ccorres_guard_imp2)
    apply (rule ccorres_add_return)
    apply (rule ccorres_split_nothrow)
    apply (rule ccorres_cond_false)
       apply (rule ccorres_return_Skip)
      apply (rule ceqv_refl)
     apply (rule bd [OF False])
    apply wp
   apply simp
   apply (rule Cond_false)
   apply (rule HoarePartial.Skip [OF subset_refl])
   apply (clarsimp simp: abs [rule_format, OF conjI])
   done
qed

lemma ccorres_if_cond_throws2:
  fixes e :: 'e
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> Q s \<and> Q' s' \<longrightarrow> (\<not> P) = (s' \<in> P')"
  and     ac: "\<not> P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf R R' (SKIP # hs) a c"
  and     bd: "P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf U U' (SKIP # hs) b d"
  and cthrows: "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> PT' c {}, UNIV" \<comment> \<open>c always throws\<close>
  shows  "ccorres_underlying sr \<Gamma> r xf arrel axf
          (Q and (\<lambda>s. \<not> P \<longrightarrow> R s) and (\<lambda>s. P \<longrightarrow> U s))
          (Collect Q' \<inter> {s. (s \<in> P' \<longrightarrow> s \<in> R' \<inter> PT') \<and> (s \<notin> P' \<longrightarrow> s \<in> U')})
          (SKIP # hs)
          (if P then b else a) (Cond P' c SKIP ;; d)"
  apply (subst if_swap)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_if_cond_throws [OF abs ac bd cthrows])
    apply assumption
   apply simp
  apply clarsimp
  done



lemma ccorres_cond:
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> R s \<longrightarrow> P  = (s' \<in> P') "
  and     c1: "ccorres_underlying sr \<Gamma> r xf arrel axf Pt Rt hs a c"
  and     c2: "ccorres_underlying sr \<Gamma> r xf arrel axf Pf Rf hs b c'"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf (R and (\<lambda>s. P \<longrightarrow> Pt s) and (\<lambda>s. \<not> P \<longrightarrow> Pf s)) ((Rt \<inter> P') \<union> (Rf \<inter> - P')) hs (if P then a else b) (Cond P' c c')"
  apply (rule ccorresI')
  apply (erule UnE)
   apply (drule exec_handlers_semantic_equivD1 [where b = c])
    apply (rule semantic_equivI)
    apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondTrue)
(* the following works but takes a while:
   apply (insert abs)
   apply (fastforce elim: ccorresE [OF c1] elim!: bexI [rotated])
*)
   apply (rule ccorresE [OF c1])
        apply assumption
       apply (insert abs)
       apply fastforce
      apply fastforce
     apply fastforce
    apply simp
   apply (fastforce elim!: bexI [rotated])

  apply (drule exec_handlers_semantic_equivD2 [where b = c'])
   apply (rule semantic_equivI)
   apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondFalse)

(* the following works but takes a while:
  apply (fastforce elim: ccorresE [OF c2] elim!: bexI [rotated]) *)
  apply (rule ccorresE [OF c2])
       apply assumption
      apply (insert abs, fastforce)
     apply fastforce
    apply fastforce
   apply simp
  apply (fastforce elim!: bexI[rotated])
  done

lemma ccorres_split_when_throwError_cond:
  fixes e :: 'e
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> Q s \<and> Q' s' \<longrightarrow> P = (s' \<in> P')"
  and     cc: "P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf ar axf
                        R R' (SKIP # hs) (throwError e) c"
  and     bd: "\<not> P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf ar axf
                        U U' (SKIP # hs) b d"
  and cthrows: "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> PT' c {}, UNIV" \<comment> \<open>c always throws\<close>
  shows  "ccorres_underlying sr \<Gamma> r xf ar axf
          (Q and (\<lambda>s. P \<longrightarrow> R s) and (\<lambda>s. \<not> P \<longrightarrow> U s))
          (Collect Q' \<inter> {s. (s \<in> P' \<longrightarrow> s \<in> R' \<inter> PT') \<and> (s \<notin> P' \<longrightarrow> s \<in> U')})
          (SKIP # hs)
          (whenE P (throwError e) >>=E (\<lambda>_. b)) (Cond P' c SKIP ;; d)"
  apply (subst whenE_bindE_throwError_to_if)
  apply (rule ccorres_if_cond_throws [OF abs cc bd cthrows])
   apply assumption
  apply assumption
  done

lemmas ccorres_split_unless_throwError_cond
  = ccorres_split_when_throwError_cond
      [where P = "\<not> P" for P, folded unlessE_whenE, simplified not_not]
declare ccorres_split_unless_throwError_cond

lemma ccorres_returnOk_skip:
  "ccorres_underlying sr \<Gamma> r xf arrel axf \<top>
     {s. r (Inr v) (xf s)} hs (returnOk v) Skip"
  using ccorres_return_Skip'
  by (simp add: returnOk_def)

lemma exec_handlers_less:
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>h \<langle>hs, s'\<rangle> \<Rightarrow> (n, t); t \<notin> range Abrupt \<rbrakk>
       \<Longrightarrow> n < length hs"
  by (induct rule: exec_handlers.induct, simp_all)

lemma exec_handlers_less2:
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>h \<langle>hs, s'\<rangle> \<Rightarrow> (n, t); t \<notin> range Abrupt \<rbrakk>
       \<Longrightarrow> \<exists>v. length hs - n = Suc v"
  apply (drule(1) exec_handlers_less)
  apply (case_tac "length hs - n", simp_all)
  done

lemma ccorres_seq_skip:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (Skip ;; c)
       = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a c"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.intros)
  done

lemma ccorres_expand_while_iff:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (Cond P (c ;; While P c) Skip) =
   ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (While P c)"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.intros)
  done

abbreviation
  "ccorresG rf_sr \<Gamma> r xf \<equiv> ccorres_underlying rf_sr \<Gamma> r xf r xf"

lemma exec_handlers_Hoare_call_Basic:
  "\<lbrakk> \<forall>s' t x. s' \<in> P \<longrightarrow> g s' t (ret s' t) \<in> Q; UNIV \<subseteq> A \<rbrakk> \<Longrightarrow>
    exec_handlers_Hoare \<Gamma> P (call initfn p ret (\<lambda>x y. Basic (g x y)) # hs) Q A"
  apply (clarsimp simp: exec_handlers_Hoare_def
             split del: if_split)
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (erule exec_call_Normal_elim, simp_all)[1]
     apply (auto elim!: exec_Normal_elim_cases)[1]
    apply (frule exec_handlers_less2, clarsimp+)
    apply (clarsimp simp: subset_iff split: if_split_asm)
   apply (auto elim!: exec_Normal_elim_cases
                      exec_call_Normal_elim)
  done

lemmas ccorres_seq_simps [simp] =
  ccorres_seq_cond_empty ccorres_seq_cond_univ ccorres_seq_skip

(* FIXME: Move *)
lemma fg_consD1:
  "fg_cons xf (xfu \<circ> (\<lambda>x _. x)) \<Longrightarrow> xf (xfu (\<lambda>_. v) s) = v"
  unfolding fg_cons_def
  by simp

lemma exec_handlers_BasicD [dest?]:
  assumes eh: "\<Gamma> \<turnstile>\<^sub>h \<langle>Basic g # hs, s\<rangle> \<Rightarrow> (n, s')"
  shows "s' = Normal (g s)"
  using eh
  by (auto elim: exec_Normal_elim_cases  exec_handlers.cases)

lemma ccorres_add_True:
  "ccorres_underlying rf_sr \<Gamma> r xf arrel axf P (P' \<inter> {s. True}) hs a c \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> r xf arrel axf P P' hs a c"
  by simp

lemma ccorres_add_UNIV_Int:
  "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G (UNIV \<inter> G') hs a c \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' hs a c"
  by simp

lemma Collect_const_mem:
  "(x \<in> (if P then UNIV else {})) = P"
  by simp

(* FIXME: MOVE *)
lemma ccorres_cond_univ_iff:
  "ccorres_underlying sr Gamm r xf arrel axf G G' hs a (Cond UNIV x y) = ccorres_underlying sr Gamm r xf arrel axf G G' hs a x"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.intros)
  done

(* FIXME: MOVE *)
lemma ccorres_cond_empty_iff:
  "ccorres_underlying sr Gamm r xf arrel axf G G' hs a (Cond {} y x) = ccorres_underlying sr Gamm r xf arrel axf G G' hs a x"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.intros)
  done

lemmas ccorres_cond_iffs = ccorres_cond_empty_iff ccorres_cond_univ_iff

lemma vcg_no_global_inv:
  assumes Pginv: "\<And>x t. x \<in> P \<Longrightarrow> g x t (x\<lparr>globals := globals t\<rparr>) \<in> P"
  and        st: "\<forall>Z. \<Gamma>\<turnstile> UNIV Call f UNIV"
  shows "\<Gamma> \<turnstile> P (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>x y. Basic (g x y))) P"
  apply (rule HoarePartial.ProcSpecNoAbrupt [OF _ _ st])
    apply simp
    prefer 2
    apply (intro allI)
    apply (rule HoarePartial.Basic)
    apply (rule subset_refl)
   apply clarsimp
   apply (erule Pginv)
   done

lemma liftt_if:
  "lift_t g hdv = (\<lambda>p. if (snd hdv),g \<Turnstile>\<^sub>t p then Some (h_val (fst hdv) p) else None)"
  apply (cases hdv)
  apply (simp add: lift_t_if split_def cong: if_cong)
  done


(* pspace updates *)

lemma clift_h_t_validD:
  "lift_t g hp p = Some x \<Longrightarrow> snd hp,g \<Turnstile>\<^sub>t p"
  apply (cases hp, simp)
  apply (erule lift_t_h_t_valid)
  done

(* Tests *)

lemma sep_conj_dom:
  "((\<lambda>s. dom s = X) \<and>\<^sup>* (\<lambda>s. dom s = Y)) = (\<lambda>s. dom s = X \<union> Y \<and> X \<inter> Y = {})"
  unfolding sep_conj_def
  apply (rule ext)
  apply rule
   apply (clarsimp simp: map_disj_def)
  apply (rule_tac x = "s |` X" in exI)
  apply (rule_tac x = "s |` Y" in exI)
  apply (clarsimp simp: map_disj_def Int_Un_distrib2)
  apply (simp add: Int_ac heap_merge_restrict_dom_un Un_ac)
  done

lemma Diff_Diff_Un_eq: "(A - B) - C = A - (B \<union> C)"
  by (simp add: Diff_eq Int_ac)

lemma Diff_Diff_Un: "(A - B - C) \<union> B = A - C \<union> B"
  apply (simp add: Diff_eq)
  apply (subst Un_Int_distrib2)
  apply (subst Un_Int_distrib2)
  apply (simp add: Compl_partition2)
  apply (rule Un_Int_distrib2 [symmetric])
  done

lemma Diff_Subset_Un_UNIV:
  assumes subset: "B \<subseteq> B'"
  shows "(- B \<union> B') = UNIV"
proof -
  from subset obtain X where "B' = B \<union> X"
    by auto
  thus ?thesis
    by (simp add: Compl_partition2 Un_assoc [symmetric])
qed

lemma Diff_Diff_Subset_cancel: "B \<subseteq> B' \<Longrightarrow> (A - B - C) \<union> B' = A - C \<union> B'"
  apply (simp add: Diff_eq)
  apply (subst Un_Int_distrib2)
  apply (subst Un_Int_distrib2)
  apply (simp add: Diff_Subset_Un_UNIV)
  apply (rule Un_Int_distrib2 [symmetric])
  done

lemma Diff_Diff_Un_Diff: "(A - B - C) \<union> (B - D) =
  ((A - C) \<union> B) \<inter> (A - B - C \<union> - D)" (is "?LHS = ?RHS")
proof -
  have "?LHS = (A - B - C) \<union> (B \<inter> - D)" by (simp add: Diff_eq)
  also have "\<dots> = ?RHS"
    by (simp add: Un_Int_distrib Diff_Diff_Subset_cancel)
  finally show ?thesis .
qed

lemmas lift_t_h_val = lift_t_lift [unfolded CTypesDefs.lift_def, simplified]

(* adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x)) *)
lemma lift_t_field_h_val:
  fixes pa :: "'a :: mem_type ptr"
  assumes fl: "(field_lookup (typ_info_t TYPE('a)) f 0) \<equiv> Some (t, m')"
  and   eu: "export_uinfo t = typ_uinfo_t TYPE('b :: mem_type)"
  shows "clift (h, d) pa = Some v \<Longrightarrow> h_val h (Ptr &(pa\<rightarrow>f) :: 'b :: mem_type ptr) = from_bytes (access_ti\<^sub>0 t v)"
  using fl eu
  apply -
  apply (rule lift_t_h_val [where g=c_guard])
  apply (erule (2) lift_t_mono [OF meta_eq_to_obj_eq])
  apply (rule c_guard_mono)
  done

lemma fl_sub_typ:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a :: c_type)) f 0 = Some (t, n); export_uinfo t = typ_uinfo_t TYPE('b :: c_type) \<rbrakk>
  \<Longrightarrow> TYPE ('b) \<le>\<^sub>\<tau> TYPE ('a)"
  unfolding sub_typ_def
  apply (simp add: typ_simps)
  apply (drule td_set_field_lookupD)
  apply (drule td_set_export_uinfoD)
  apply simp
  apply (erule exI)
  done

lemma lift_t_super_update:
  fixes p :: "'a :: mem_type ptr" and v :: "'b :: mem_type"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  and    eu: "export_uinfo s = typ_uinfo_t TYPE('b)"
  and    lp: "lift_t g (h, d) p = Some v'"
  shows "lift_t g (heap_update (Ptr &(p\<rightarrow>f)) v h, d)
  = lift_t g (h, d)(p \<mapsto> field_update (field_desc s) (to_bytes_p v) v')"
  using fl eu lp
  apply -
  apply (rule trans [OF lift_t_super_field_update super_field_update_lookup])
     apply (erule (1) h_t_valid_mono [OF _ _ guard_mono_True, rule_format])
      apply (erule lift_t_h_t_valid)
     apply (erule (1) fl_sub_typ)
     apply assumption
   apply simp
  apply assumption
  done

declare fg_cons_comp [simp]

lemma lift_t_update_fld_other2:
  fixes val :: "'b :: packed_type" and ptr :: "'a :: packed_type ptr"
  assumes   fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, m')"
  and     disj: "typ_uinfo_t TYPE('c :: mem_type) \<bottom>\<^sub>t typ_uinfo_t TYPE('a)"
  and       eu: "export_uinfo t = typ_uinfo_t TYPE('b)"
  and       cl: "clift (hp,d) ptr = Some z"
  shows "(clift (heap_update (Ptr &(ptr\<rightarrow>f)) val hp, d)) = (clift (hp, d) :: 'c :: mem_type typ_heap)"
  (is "?LHS = ?RHS")
proof -
  from cl have "c_guard ptr" by (rule lift_t_g)
  hence "?LHS = clift (heap_update ptr (update_ti t (to_bytes_p val) (h_val hp ptr)) hp, d)" using eu
    by (simp add: packed_heap_super_field_update [OF fl])

  also have "... = ?RHS" using cl disj
    by (rule typ_rewrs(5))

  finally show ?thesis .
qed

(* FIXME: MOVE *)
lemma ccorres_Call_call_for_vcg:
  "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' hs a (call id f (\<lambda>s t. t) (\<lambda>s t. Basic id)) \<Longrightarrow>
  ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' hs a (Call f)"
  apply (erule iffD1 [OF ccorres_semantic_equiv, rotated -1])
  apply (rule semantic_equivI)
  apply (rule iffI)
   apply (erule exec_call_Normal_elim)
       apply (erule exec_Normal_elim_cases)+
       apply (simp, erule (1) exec.Call)+
   apply simp
   apply (erule exec.intros)
  apply (erule exec_Normal_elim_cases)
   apply (case_tac s')
      apply simp
      apply (erule exec_call)
       apply simp
      apply (rule exec.Basic [where f = id, simplified])
     apply (clarsimp elim!: exec_callAbrupt)
    apply (clarsimp elim!: exec_callFault)
   apply (clarsimp elim!: exec_callStuck)
  apply (clarsimp elim!: exec_callUndefined)
  done

lemma ccorres_assertE:
  assumes rl: "P \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf G G' hs f c"
  shows "ccorres_underlying sr Gamm r xf arrel axf G G' hs (assertE P >>=E (\<lambda>_. f)) c"
  by (simp add: assertE_def ccorres_fail' rl)

lemma ccorres_assert2:
  "\<lbrakk> P \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf G G' hs (f ()) c \<rbrakk>
      \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf
              (\<lambda>s. P \<longrightarrow> G s) {s. P \<longrightarrow> s \<in> G'} hs (assert P >>= f) c"
  by (cases P, simp_all add: ccorres_fail')

lemma ccorres_stateAssert:
  "ccorres_underlying sr Gamm r xf arrel axf P P' hs (a ()) c \<Longrightarrow>
   ccorres_underlying sr Gamm r xf arrel axf (\<lambda>s. Q s \<longrightarrow> P s) P' hs (stateAssert Q [] >>= a) c"
  apply (rule ccorres_guard_imp [OF ccorres_symb_exec_l])
       apply simp
      apply (clarsimp simp: stateAssert_def)
      apply (wp, simp)[1]
     apply (clarsimp simp: stateAssert_def)
     apply wp[1]
    apply (simp add: empty_fail_stateAssert)
   apply clarsimp
  apply clarsimp
  done

lemma ccorres_if_lhs:
  "\<lbrakk> P \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf Q S hs f conc;
     \<not> P \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf R T hs g conc \<rbrakk>
   \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf (\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not> P \<longrightarrow> R s))
                      {s. (P \<longrightarrow> s \<in> S) \<and> (\<not> P \<longrightarrow> s \<in> T)}
          hs (if P then f else g) conc"
  by (simp split: if_split)

lemma ccorres_if_bindE:
  "ccorres_underlying sr Gamm r xf arrel axf G G' hs (if a then (b >>=E f) else (c >>=E f)) d
  \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf G G' hs ((if a then b else c) >>=E f) d"
  by (simp split: if_split_asm)

lemma ccorres_liftE:
  fixes \<Gamma>
  assumes cc: "ccorresG sr \<Gamma> (\<lambda> rv. r (Inr rv)) xf P P' hs a c"
  shows   "ccorresG sr \<Gamma> r xf P P' hs (liftE a) c"
  using cc
  by (fastforce split: xstate.splits
                simp: liftE_def ccorres_underlying_def bind_def' return_def unif_rrel_def)

lemma ccorres_if_bind:
  "ccorres_underlying sr Gamm r xf arrel axf G G' hs (if a then (b >>= f) else (c >>= f)) d
  \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf G G' hs ((if a then b else c) >>= f) d"
  by (simp split: if_split_asm)

lemma ccorres_Cond_rhs:
  "\<lbrakk> P \<Longrightarrow> ccorres_underlying sr Gamm rvr xf arrel axf Q S hs absf f;
     \<not> P \<Longrightarrow> ccorres_underlying sr Gamm rvr xf arrel axf R T hs absf g \<rbrakk>
   \<Longrightarrow> ccorres_underlying sr Gamm rvr xf arrel axf (\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not> P \<longrightarrow> R s))
                      {s. (P \<longrightarrow> s \<in> S) \<and> (\<not> P \<longrightarrow> s \<in> T)}
          hs absf (Cond {s. P} f g)"
  by (cases P, simp_all add: ccorres_cond_iffs)

lemma ccorres_Cond_rhs_Seq:
  "\<lbrakk> P \<Longrightarrow> ccorres_underlying sr Gamm rvr xf arrel axf Q S hs absf (f ;; h);
     \<not> P \<Longrightarrow> ccorres_underlying sr Gamm rvr xf arrel axf R T hs absf (g ;; h) \<rbrakk>
   \<Longrightarrow> ccorres_underlying sr Gamm rvr xf arrel axf (\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not> P \<longrightarrow> R s))
                      {s. (P \<longrightarrow> s \<in> S) \<and> (\<not> P \<longrightarrow> s \<in> T)}
          hs absf (Cond {s. P} f g ;; h)"
  by (cases P, simp_all add: ccorres_cond_iffs)

lemma ccorres_guard_from_wp:
  "\<lbrakk> \<lbrace>\<lambda>s. \<not> P s \<rbrace> a \<lbrace>\<lambda>_ _. False\<rbrace>; empty_fail a; ccorres_underlying sr Gamm rvr xf arrel axf G G' hs a c \<rbrakk> \<Longrightarrow>
  ccorres_underlying sr Gamm rvr xf arrel axf (\<lambda>s. P s \<longrightarrow> G s) G' hs a c"
  apply (rule ccorresI')
  apply (simp add: empty_fail_def)
  apply (drule_tac x = s in spec)
  apply (case_tac "P s")
   apply simp
   apply (erule (5) ccorresE)
   apply fastforce
  apply (clarsimp simp: not_empty_eq)
  apply (drule (2) use_valid)
  apply simp
  done

lemma ccorres_guard_from_wp_bind:
  "\<lbrakk> \<lbrace>\<lambda>s. \<not> P s \<rbrace> a \<lbrace>\<lambda>_ _. False\<rbrace>; empty_fail a; ccorres_underlying sr Gamm rvr xf arrel axf G G' hs (a >>= b) c \<rbrakk> \<Longrightarrow>
  ccorres_underlying sr Gamm rvr xf arrel axf (\<lambda>s. P s \<longrightarrow> G s) G' hs (a >>= b) c"
  apply (rule ccorresI')
  apply (simp add: empty_fail_def)
  apply (drule_tac x = s in spec)
  apply (case_tac "P s")
   apply simp
   apply (erule (5) ccorresE)
   apply fastforce
  apply (drule not_snd_bindI1)
  apply (clarsimp simp: not_empty_eq)
  apply (drule (2) use_valid)
  apply simp
  done

lemma ccorres_disj_division:
  "\<lbrakk> P \<or> Q; P \<Longrightarrow> ccorres_underlying sr G r xf ar axf R S hs a c;
            Q \<Longrightarrow> ccorres_underlying sr G r xf ar axf T U hs a c \<rbrakk>
     \<Longrightarrow> ccorres_underlying sr G r xf ar axf
             (\<lambda>s. (P \<longrightarrow> R s) \<and> (Q \<longrightarrow> T s)) {s. (P \<longrightarrow> s \<in> S) \<and> (Q \<longrightarrow> s \<in> U)}
                hs a c"
  apply (erule disjE, simp_all)
   apply (auto elim!: ccorres_guard_imp)
  done

lemma disj_division_bool: "b \<or> \<not> b" by simp

lemmas ccorres_case_bools2 = ccorres_disj_division [OF disj_division_bool]

lemma ceqv_tuple:
  "\<lbrakk> ceqv \<Gamma> xfa va s s' x y; ceqv \<Gamma> xfb vb s s' y z \<rbrakk>
        \<Longrightarrow> ceqv \<Gamma> (\<lambda>s. (xfa s, xfb s)) (va, vb) s s' x z"
  by (simp add: ceqv_def)

lemma ceqv_tuple2:
  "\<lbrakk> ceqv \<Gamma> xfa (fst v) s s' x y; ceqv \<Gamma> xfb (snd v) s s' y z \<rbrakk>
        \<Longrightarrow> ceqv \<Gamma> (\<lambda>s. (xfa s, xfb s)) v s s' x z"
  by (cases v, simp add: ceqv_tuple)

lemma ccorres_inst:
  "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs h c
     \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs h c"
  by simp

lemmas ccorres_splitE
    = ccorres_master_splitE[OF _ refl _ _ _ exec_handlers_Hoare_from_vcg_might_fail_UNIV]

lemmas ccorres_splitE_novcg
    = ccorres_master_splitE[OF _ refl _ _ _ exec_handlers_Hoare_UNIV]

lemma ccorres_cross_over_guard:
  "ccorres_underlying sr Gamm rvr xf arrel axf P' Q hs af cf \<Longrightarrow>
      ccorres_underlying sr Gamm rvr xf arrel axf (P and P') {s'. \<forall>s. (s, s') \<in> sr \<and> P s \<longrightarrow> s' \<in> Q} hs af cf"
  apply (erule ccorres_guard_imp2)
  apply clarsimp
  done

(* FIXME replace any usage of ccorres_cross_over_guard that does not refer to state with this lemma,
   as it doesn't create spurious (s, s') \<in> rf_sr assumptions *)
lemma ccorres_cross_over_guard_no_st:
  "ccorres_underlying sr Gamm rvr xf arrel axf P' Q hs af cf \<Longrightarrow>
      ccorres_underlying sr Gamm rvr xf arrel axf (K P and P') {s'. P \<longrightarrow> s' \<in> Q} hs af cf"
  apply (erule ccorres_guard_imp2)
  apply clarsimp
  done

lemma sequence_x_sequence:
  "sequence_x xs = (sequence xs >>= (\<lambda>_. return ()))"
  by (induct xs, simp_all add: sequence_def sequence_x_def Let_def
                               bind_assoc)

lemma sequence_Cons:
  "sequence (x # xs) = do v \<leftarrow> x; vs \<leftarrow> sequence xs; return (v # vs) od"
  by (simp add: sequence_def Let_def)

lemma ccorres_sequence_while_genQ':
  fixes i :: "nat" and xf :: "('s, 't) state_scheme \<Rightarrow> ('c :: len) word"
  assumes one: "\<And>n ys. \<lbrakk> n < length xs \<rbrakk> \<Longrightarrow>
                    ccorresG rf_sr \<Gamma> (\<lambda>rv rv'. r' (ys @ [rv]) rv') xf'
                            (F (n * j)) ({s. xf s = of_nat (i + n * j) \<and> r' ys (xf' s)} \<inter> Q) hs
                            (xs ! n) body"
  and      pn: "\<And>n. P n = (n < of_nat (i + length xs * j))"
  and   bodyi: "\<forall>s. xf s < of_nat (i + length xs * j)
    \<longrightarrow> \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> ({s} \<inter> Q) body {t. xf t = xf s \<and> xf_update (\<lambda>_. xf t + of_nat j) t \<in> Q}"
  and      hi: "\<And>n. Suc n < length xs \<Longrightarrow> \<lbrace> F (n * j) \<rbrace> (xs ! n) \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>"
  and     lxs: "i + length xs * j < 2 ^ len_of TYPE('c)"
  and      xf: "\<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s"
  and     xf': "\<forall>s f. xf' (xf_update f s) = (xf' s)"
  and rf_sr_xf: "\<And>s r f. (s, r) \<in> rf_sr \<Longrightarrow> (s, xf_update f r) \<in> rf_sr"
  and       j: " j > 0"
  shows  "ccorresG rf_sr \<Gamma> (\<lambda>rv (i', rv'). r' rv rv' \<and> i' = of_nat (i + length xs * of_nat j))
                  (\<lambda>s. (xf s, xf' s))
                  (\<lambda>s. P 0 \<longrightarrow> F 0 s) ({s. xf s = of_nat i \<and> r' [] (xf' s)} \<inter> Q) hs
                  (sequence xs)
                  (While {s. P (xf s)}
                     (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s)))"
  (is "ccorresG rf_sr \<Gamma> ?r' ?xf' ?G (?G' \<inter> _) hs (sequence xs) ?body")
proof -
  define init_xs where "init_xs \<equiv> xs"

  have rl: "xs = drop (length init_xs - length xs) init_xs" unfolding init_xs_def
    by fastforce

  note pn' = pn [folded init_xs_def]
  note one' = one [folded init_xs_def]
  note hi'  = hi [folded init_xs_def]
  note lxs' = lxs [folded init_xs_def]

  let ?Q  = "\<lambda>xs s. xs \<noteq> [] \<longrightarrow> F ((length init_xs - length xs) * j) s"
  let ?Q' = "\<lambda>xs zs. {s. (xf s) = of_nat (i + (length init_xs - length xs) * j)
                         \<and> r' zs (xf' s)} \<inter> Q"
  let ?r'' = "\<lambda>zs rv (i', rv'). r' (zs @ rv) rv'
                   \<and> i' = of_nat (i + length init_xs * j)"

  have "\<forall>zs. ccorresG rf_sr \<Gamma> (?r'' zs) ?xf'
             (?Q xs) (?Q' xs zs) hs
             (sequence xs) ?body"
  using rl
  proof (induct xs)
    case Nil
    thus ?case
      apply clarsimp
      apply (rule iffD1 [OF ccorres_expand_while_iff])
      apply (simp add: sequence_def ccorres_cond_iffs)
      apply (rule ccorres_guard_imp2)
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_Skip')
      apply (simp add: pn')
      done
  next
    case (Cons y ys)

    from Cons.prems have ly: "length (y # ys) \<le> length init_xs" by simp
    hence ln: "(length init_xs - length ys) = Suc (length init_xs - length (y # ys))"  by simp
    hence yv: "y = init_xs ! (length init_xs - length (y # ys))" using Cons.prems
      by (fastforce simp add: drop_Suc_nth not_le)

    have lt0: "0 < length init_xs" using ly by clarsimp
    hence ly': "length init_xs - length (y # ys) < length init_xs" by simp

    note one'' = one'[OF ly', simplified yv[symmetric]]

    have ys_eq: "ys = drop (length init_xs - length ys) init_xs"
      using ln Cons.prems
        by (fastforce simp add: drop_Suc_nth not_le)
    note ih = Cons.hyps [OF ys_eq, rule_format]

    note hi'' = hi' [where n="(length init_xs - length (y # ys))", folded yv]

    from Cons.prems
    have neq_Nil: "init_xs \<noteq> []" by clarsimp
    with ly
    have ys_xs: "length ys < length init_xs" by clarsimp
    hence hi''':
      "ys\<noteq>[] \<Longrightarrow>
      \<lbrace>F ((length init_xs - length (y # ys)) * j)\<rbrace> y \<lbrace>\<lambda>_. F (Suc (length init_xs - length (y # ys)) * j)\<rbrace>"
      apply -
      apply (rule hi'')
      apply simp
      apply (clarsimp simp: neq_Nil_conv)
      apply arith
      done

    show ?case
      using lxs'
      apply (clarsimp simp: sequence_Cons)
      apply (rule ccorres_guard_imp2)
       apply (rule iffD1 [OF ccorres_expand_while_iff])
       apply (rule ccorres_cond_true)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_split_nothrow)
           apply (rule_tac ys="zs" in one'')
          apply (rule ceqv_refl)
         apply (rule ccorres_symb_exec_r)
           apply (simp only: liftM_def[symmetric] ccorres_liftM_simp
                             o_def)
           apply (rule ccorres_rel_imp, rule_tac zs="zs @ [rv]" in ih)
           apply clarsimp
          apply vcg
         apply (rule conseqPre)
          apply vcg
         apply (clarsimp simp: xf rf_sr_xf)
        apply (subst ln)
        apply (rule hoare_impI)
        apply (rule hi''')
        apply simp
       apply (simp add: xf')
       apply (rule HoarePartialDef.Conseq [where P = "{s. P (xf s) \<and> xf s + of_nat j = of_nat (i + (length init_xs - length ys) * of_nat j)} \<inter> Q"])
       apply (intro ballI exI)
       apply (rule conjI)
        apply (rule_tac s=s in bodyi[rule_format])
        apply (clarsimp simp: pn)
       apply (clarsimp simp: xf)
      apply (clarsimp simp: ln pn')
      apply (subst of_nat_mult [symmetric])+
      apply (subst of_nat_add [symmetric])+
      apply (rule of_nat_mono_maybe)
       apply (simp add: word_bits_conv)
      apply (simp add: j)
      apply (rule diff_Suc_less [OF lt0])
      done
  qed
  thus ?thesis using lxs
    apply (auto simp: init_xs_def dest!: spec[where x=Nil]
                simp: j pn word_less_nat_alt neq_Nil_conv unat_word_ariths unat_of_nat push_mods
            elim!: ccorres_guard_imp2)
    done
qed

lemma inl_rrel_inl_rrel:
  "inl_rrel (inl_rrel r) = inl_rrel r"
  by (intro ext, simp add: inl_rrel_def split: sum.split)


lemma ccorres_abstract_h_val:
  fixes p :: "'a :: c_type ptr"
  shows "(\<And>rv. P rv \<Longrightarrow> ccorres_underlying sr Gamm rvr xf arrel axf G (G' rv) hs a c) \<Longrightarrow>
  ccorres_underlying sr Gamm rvr xf arrel axf G ({s. P ((f::'a \<Rightarrow> ('b::{type})) s) \<longrightarrow> s \<in> G' (f s)} \<inter> {s. P (f s)}) hs a c"
  apply (rule ccorres_tmp_lift1 [where P = P])
  apply (clarsimp simp: Collect_conj_eq [symmetric])
  apply (fastforce intro: ccorres_guard_imp)
  done

lemma ccorres_abstract_cslift:
  fixes p :: "'a :: c_type ptr"
  shows "(\<And>rv. P rv \<Longrightarrow> ccorres_underlying sr Gamm rvr xf arrel axf G (G' rv) hs a c) \<Longrightarrow>
  ccorres_underlying sr Gamm rvr xf arrel axf G ({s. P ((f::'a \<Rightarrow> ('b::{type})) s) \<longrightarrow> s \<in> G' (f s)} \<inter> {s. P (f s)}) hs a c"
  apply (erule ccorres_abstract_h_val)
  done

lemma ccorres_cond2:
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> R s \<longrightarrow> P  = (s' \<in> P') "
  and     c1: "ccorres_underlying sr \<Gamma> r xf arrel axf Pt Rt hs a c"
  and     c2: "ccorres_underlying sr \<Gamma> r xf arrel axf Pf Rf hs b c'"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf (R and (\<lambda>s. P \<longrightarrow> Pt s) and (\<lambda>s. \<not> P \<longrightarrow> Pf s))
                    {s. (s \<in> P' \<longrightarrow> s \<in> Rt) \<and> (s \<notin> P' \<longrightarrow> s \<in> Rf)} hs (if P then a else b) (Cond P' c c')"
  apply (rule ccorresI')
  apply clarsimp
  apply (case_tac " s' \<in> P'", clarsimp)
   apply (drule exec_handlers_semantic_equivD1 [where b = c])
    apply (rule semantic_equivI)
    apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondTrue)
(* the following works but takes a while:
   apply (insert abs)
   apply (fastforce elim: ccorres_underlyingE [OF c1] elim!: bexI [rotated])
*)
   apply (rule ccorresE [OF c1])
       apply assumption
      apply (insert abs)
      apply fastforce
     apply fastforce
     apply fastforce
    apply simp
   apply (fastforce elim!: bexI [rotated])
  apply clarsimp
  apply (drule exec_handlers_semantic_equivD2 [where b = c'])
   apply (rule semantic_equivI)
   apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondFalse)

(* the following works but takes a while:
  apply (fastforce elim: ccorres_underlyingE [OF c2] elim!: bexI [rotated]) *)
  apply (rule ccorresE [OF c2])
      apply assumption
     apply (insert abs, fastforce)
    apply fastforce
    apply fastforce
   apply simp
  apply (fastforce elim!: bexI[rotated])
  done

lemma ccorres_expand_while_iff_Seq:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (Cond P (c ;; While P c ;; c') c') =
   ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (While P c ;; c')"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.intros)
  done

lemma ccorres_expand_while_iff_Seq2:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (c'' ;; Cond P (c ;; While P c ;; c') c') =
   ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (c'' ;; While P c ;; c')"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.intros
              | erule exec_elim_cases)+
  done

lemma ccorres_seq_skip':
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (c ;; Skip)
       = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a c"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (case_tac s', auto elim!: exec_elim_cases intro: exec.intros)
  done


lemma ccorres_cond2':
  "\<lbrakk>\<forall>s s'. (s, s') \<in> sr \<and> R s \<longrightarrow> (\<not> P) = (s' \<in> P');
     ccorres_underlying sr \<Gamma> r xf ar axf Pt Rt hs a c;
  ccorres_underlying sr \<Gamma> r xf ar axf Pf Rf hs b c'\<rbrakk>
  \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf ar axf  (R and (\<lambda>s. \<not> P \<longrightarrow> Pt s) and (\<lambda>s. P \<longrightarrow> Pf s))
  {s. (s \<in> P' \<longrightarrow> s \<in> Rt) \<and> (s \<notin> P' \<longrightarrow> s \<in> Rf)} hs (if P then b else a)
  (Cond P' c c')"
  apply (subst if_flip [symmetric])
  apply (rule ccorres_guard_imp2)
  apply (erule (2) ccorres_cond2)
  apply clarsimp
  done

lemmas ccorres_handlers_weaken2 = ccorres_nohs

lemma ccorres_abstract_cleanup:
  "ccorres_underlying sr \<Gamma> r xf ar axf G G' hs a c \<Longrightarrow>
   ccorres_underlying sr \<Gamma> r xf ar axf G ({s. s \<in> S \<longrightarrow> s \<in> G'} \<inter> S) hs a c"
   by (fastforce intro: ccorres_guard_imp)

lemma ccorres_from_vcg_split_throws:
  "\<lbrakk> \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> R' c {},UNIV;
     \<And>\<sigma>. \<Gamma> \<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> sr}
              c UNIV,
         {s. \<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> sr \<and> arrel rv (axf s)} \<rbrakk>
    \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P (P' \<inter> R') (SKIP # hs) a (c ;; d)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_split_throws[rotated], assumption)
   apply (rule ccorres_from_vcg_throws[where P=P and P'="P' \<inter> R'"])
   apply (rule allI)
   apply (erule_tac x=\<sigma> in meta_allE)
   apply (rule conseqPost)
     apply (erule HoarePartialProps.Merge_PostConj [OF conseqPre])
        apply clarsimp
       apply assumption
      apply simp
     apply clarsimp
    apply simp
   apply simp
  apply simp
  done

lemma ccorres_symb_exec_l3:
  "\<lbrakk> \<And>rv. ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv) hs (f rv) c;
     \<And>s. \<lbrace>(=) s\<rbrace> m \<lbrace>\<lambda>r. (=) s\<rbrace>; \<lbrace>G\<rbrace> m \<lbrace>Q\<rbrace>; empty_fail m\<rbrakk>
  \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf G {s'. \<forall>rv. s' \<in> Q' rv}
                  hs (m >>= f) c"
  apply (rule ccorres_guard_imp2, erule ccorres_symb_exec_l)
     apply assumption+
  apply simp
  done

lemma ccorres_add_returnOk:
  "ccorres_underlying Gamm sr rvr xf arrel axf hs P P' (a >>=E returnOk) c
     \<Longrightarrow> ccorres_underlying Gamm sr rvr xf arrel axf hs P P' a c"
  by simp

lemmas ccorres_when
    = ccorres_cond2[OF _ _ ccorres_return_Skip[where a="()"], folded when_def]

lemma ccorres_Guard_True:
  "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a c
   \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F \<lbrace>True\<rbrace> c)"
   by (simp, ccorres_rewrite, assumption)

lemma ccorres_Guard_True_Seq:
  "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (c ;; d)
   \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F \<lbrace>True\<rbrace> c ;; d)"
   by (simp, ccorres_rewrite, assumption)

end
