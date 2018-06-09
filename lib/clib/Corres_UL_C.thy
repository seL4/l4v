(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* This theory is a general framework for refinement on C programs.
   It is in this directory rather than lib/ because it refers to parts
   of the translated state space of the kernel for convenience.
*)

theory Corres_UL_C
imports
  "LemmaBucket_C"
  "Lib.LemmaBucket"
  "SIMPL_Lemmas"
begin

declare word_neq_0_conv [simp del]

(* The HoarePartialDef theorems are used extensively
   (as opposed to their HoareTotalDef counterparts, which aren't used much).
   We can give most their long names, but conseqPre is used over 400 times,
   so for these cases we override the namespaces *)
lemmas conseqPre = HoarePartialDef.conseqPre
lemmas conseqPost = HoarePartialDef.conseqPost

inductive_set
  exec_handlers :: "('s, 'p, 'e) body \<Rightarrow> ('s \<times> ('s, 'p, 'e) com list \<times> nat \<times> ('s, 'e) xstate) set"
and
  exec_handlers_syn :: "[('s, 'p, 'e) body, ('s, 'p, 'e) com list, 's, nat \<times> ('s, 'e) xstate]
               \<Rightarrow> bool" ("_\<turnstile>\<^sub>h \<langle>_,_\<rangle> \<Rightarrow> _"  [60,20,98,98] 89)
  for \<Gamma> :: "('s, 'p, 'e) body"
where
  "\<Gamma> \<turnstile>\<^sub>h \<langle>hs,s\<rangle> \<Rightarrow> ns' == (s, hs, ns') \<in> exec_handlers \<Gamma>"
  | EHAbrupt: "\<lbrakk>\<Gamma> \<turnstile> \<langle>h, Normal s\<rangle> \<Rightarrow> Abrupt z; \<Gamma> \<turnstile>\<^sub>h \<langle>hs, z\<rangle> \<Rightarrow> (n, t) \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>h \<langle>h # hs, s\<rangle> \<Rightarrow> (n, t)"
  | EHOther: "\<lbrakk>\<Gamma> \<turnstile> \<langle>h, Normal s\<rangle> \<Rightarrow> t; \<not> isAbr t\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>h \<langle>h # hs, s\<rangle> \<Rightarrow> (length hs, t)"
  | EHEmpty: "\<Gamma> \<turnstile>\<^sub>h \<langle>[], s\<rangle> \<Rightarrow> (0, Abrupt s)"

lemma exec_handlers_use_hoare_nothrow:
  assumes valid': "E \<turnstile>\<^bsub>/F\<^esub> R' c Q', {}"
  and         ce: "E \<turnstile>\<^sub>h \<langle>c # hs, s'\<rangle> \<Rightarrow> (n, t)"
  and       asms: "s' \<in> R'"
  shows   "(t \<in> Normal ` Q' \<or> t \<in> Fault ` F) \<and> n = length hs"
  using valid' ce asms
  apply -
  apply (drule hoare_sound)
  apply (clarsimp elim: exec_Normal_elim_cases
    simp: NonDetMonad.bind_def cvalid_def split_def HoarePartialDef.valid_def)
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (drule spec, drule spec, drule (1) mp)
    apply fastforce
   apply clarsimp
  apply simp
  done


definition
  unif_rrel :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 'b)
                             \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 'c)
                             \<Rightarrow> 'a \<Rightarrow> 't \<Rightarrow> bool"
where
 "unif_rrel f rrel xf arrel axf \<equiv> \<lambda>x s.
    if f then rrel x (xf s) else arrel x (axf s)"

lemma unif_rrel_simps:
  "unif_rrel True rrel xf arrel axf = (\<lambda>x s. rrel x (xf s))"
  "unif_rrel False rrel xf arrel axf = (\<lambda>x s. arrel x (axf s))"
  by (simp add: unif_rrel_def)+

definition
  ccorres_underlying :: "(('s \<times> 't) set) \<Rightarrow>  ('p \<Rightarrow> ('t, 'p, 'e) com option)
                        \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 'b)
                        \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 'c)
                        \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('t set)
                        \<Rightarrow> ('t, 'p, 'e) com list
                        \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('t, 'p, 'e) com \<Rightarrow> bool"
where
  "ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs \<equiv>
   \<lambda>m c. \<forall>(s, s') \<in> srel. G s \<and> s' \<in> G' \<and> \<not> snd (m s) \<longrightarrow>
  (\<forall>n t. \<Gamma> \<turnstile>\<^sub>h \<langle>c # hs, s'\<rangle> \<Rightarrow> (n, t) \<longrightarrow>
   (case t of
         Normal s'' \<Rightarrow> (\<exists>(r, t) \<in> fst (m s). (t, s'') \<in> srel
                            \<and> unif_rrel (n = length hs) rrel xf arrel axf r s'')
       | _ \<Rightarrow> False))"

declare isNormal_simps [simp]

lemma ccorresI [case_names fail nofail]:
  assumes fc:
  "\<And>s s' n z. \<lbrakk>(s, s') \<in> sr; G s; s' \<in> G'; \<not> snd (m s); \<Gamma> \<turnstile>\<^sub>h \<langle>c # hs, s'\<rangle> \<Rightarrow> (n, z); isAbr z \<or> isFault z \<or> z = Stuck \<rbrakk>
  \<Longrightarrow> False"
  and nfc: "\<And>n t' s s'. \<lbrakk>(s, s') \<in> sr; G s; s' \<in> G'; \<Gamma> \<turnstile>\<^sub>h \<langle>c # hs, s'\<rangle> \<Rightarrow> (n, Normal t'); \<not> snd (m s)\<rbrakk>
  \<Longrightarrow> (\<exists>(r, t) \<in> fst (m s). (t, t') \<in> sr \<and> unif_rrel (n = length hs) rrel xf arrel axf r t')"
  shows "ccorres_underlying sr \<Gamma> rrel xf arrel axf G G' hs m c"
  unfolding ccorres_underlying_def
  apply -
  apply clarsimp
  apply (case_tac t)
     apply simp
     apply (erule(4) nfc)
    apply simp
    apply (erule (4) fc)
    apply simp
   apply simp
   apply (erule (4) fc)
   apply simp
  apply simp
  apply (erule (4) fc)
  apply simp
  done

lemma ccorresI':
  assumes rl: "\<And>s s' n z. \<lbrakk>(s, s') \<in> srel; G s; s' \<in> G'; \<Gamma> \<turnstile>\<^sub>h \<langle>c # hs, s'\<rangle> \<Rightarrow> (n, z); \<not> snd (m s)\<rbrakk> \<Longrightarrow>
  (\<exists>t'. z = Normal t' \<and> (\<exists>(r, t) \<in> fst (m s). (t, t') \<in> srel \<and> unif_rrel (n = length hs) rrel xf arrel axf r t'))"
  shows "ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs m c"
  unfolding ccorres_underlying_def
  apply -
  apply clarsimp
  apply (drule (4) rl)
  apply (case_tac t)
     apply simp
    apply simp
   apply simp
  apply simp
  done

lemma exec_handlers_Cons_le[simplified]:
  "\<Gamma> \<turnstile>\<^sub>h \<langle>h # hs, s'\<rangle> \<Rightarrow> (n, t) \<Longrightarrow> n \<le> length (tl (h # hs))"
  by (induct rule: exec_handlers.induct, simp_all)

lemma exec_handlers_le:
  "\<Gamma> \<turnstile>\<^sub>h \<langle>hs, s'\<rangle> \<Rightarrow> (n, t) \<Longrightarrow> n \<le> length hs"
  by (induct rule: exec_handlers.induct, simp_all)

lemma ccorresE:
  assumes cc: "ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs m c"
  and ps: "(s, s') \<in> srel" "G s" "s' \<in> G'"  "\<not> snd (m s)" "\<Gamma>\<turnstile>\<^sub>h \<langle>c#hs , s'\<rangle> \<Rightarrow> (n, x)"
  and nc: "\<And>t' r t. \<lbrakk>x = Normal t'; (r, t) \<in> fst (m s); (t, t') \<in> srel;
                           unif_rrel (n = length hs) rrel xf arrel axf r t';
                           n \<le> length hs \<rbrakk> \<Longrightarrow> P"
  shows P
  using cc ps nc unfolding ccorres_underlying_def
  apply clarsimp
  apply (drule (1) bspec)
  apply simp
  apply (elim allE, drule (1) mp)
  apply (cases x)
     apply (clarsimp dest!: exec_handlers_Cons_le)
    apply simp
   apply simp
  apply simp
  done

lemma ccorres_empty_handler_abrupt:
  assumes cc: "ccorres_underlying sr \<Gamma> rrel xf' arrel axf P P' [] a c"
  and   asms: "(s, s') \<in> sr" "P s" "s' \<in> P'" "\<not> snd (a s)"
  and     eh: "\<Gamma> \<turnstile> \<langle>c, Normal s'\<rangle> \<Rightarrow> t"
  shows   "\<not> isAbr t"
  using cc asms eh
  apply -
  apply rule
  apply (erule isAbrE)
  apply simp
  apply (drule EHAbrupt [OF _ EHEmpty])
  apply (erule (5) ccorresE)
  apply simp
  done

lemma ccorres_empty_handler_abrupt':
  assumes cc: "ccorres_underlying sr \<Gamma> rrel xf' arrel axf P P' [] a c"
  and   asms: "(s, s') \<in> sr" "P s" "s' \<in> P'" "\<not> snd (a s)"
  and     eh: "\<Gamma> \<turnstile>\<^sub>h \<langle>c # hs, s'\<rangle> \<Rightarrow> (n, t)"
  shows   "\<not> isAbr t"
  using cc asms eh
  apply -
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (frule (5) ccorres_empty_handler_abrupt)
    apply simp
   apply simp
  apply simp
  done

lemma ccorres_handlers_weaken:
  assumes cul: "ccorres_underlying sr \<Gamma> rrel xf arrel axf P P' [] a c"
  shows   "ccorres_underlying sr \<Gamma> rrel xf arrel axf P P' hs a c"
  using cul
  apply -
  apply (rule ccorresI')
  apply (frule (5) ccorres_empty_handler_abrupt')
  apply (erule exec_handlers.cases)
  apply clarsimp
   apply (erule (4) ccorresE)
     apply (erule EHAbrupt [OF _ EHEmpty])
    apply simp
   apply clarsimp
   apply (erule (4) ccorresE)
    apply (erule (1) EHOther)
   apply clarsimp
   apply (erule bexI [rotated], simp)
  apply simp
  done

lemma ccorres_from_vcg0:
  "(\<forall>\<sigma>. \<Gamma> \<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> srel}
          c
        {s. \<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> srel \<and> rrel rv (xf s)})
  \<Longrightarrow> ccorres_underlying srel \<Gamma> rrel xf arrel axf P P' hs a c"
  apply (rule ccorresI')
  apply (drule_tac x = s in spec)
  apply (drule hoare_sound)
  apply (clarsimp simp add: HoarePartialDef.valid_def cvalid_def)
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (drule spec, drule spec, drule (1) mp)
    apply clarsimp
   apply clarsimp
   apply (drule spec, drule spec, drule (1) mp)
   apply clarsimp
   apply (erule bexI [rotated])
   apply (simp add: unif_rrel_simps)
  apply simp
  done

lemmas ccorres_from_vcg = ccorres_from_vcg0 [THEN ccorres_handlers_weaken]

lemma ccorres_from_vcg_nofail0:
  "(\<forall>\<sigma>. \<Gamma> \<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> srel \<and> \<not> snd (a \<sigma>)}
  c
  {s. \<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> srel \<and> rrel rv (xf s)})
  \<Longrightarrow> ccorres_underlying srel \<Gamma> rrel xf arrel axf P P' [] a c"
  apply (rule ccorresI')
  apply (drule_tac x = s in spec)
  apply (drule hoare_sound)
  apply (simp add: HoarePartialDef.valid_def cvalid_def)
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (drule spec, drule spec, drule (1) mp)
    apply clarsimp
   apply clarsimp
   apply (drule spec, drule spec, drule (1) mp)
   apply clarsimp
   apply (erule bexI [rotated])
   apply (simp add: unif_rrel_simps)
  apply simp
  done

lemmas ccorres_from_vcg_nofail2
  = ccorres_from_vcg_nofail0 [THEN ccorres_handlers_weaken]


lemma ccorres_from_vcg_nofail:
  "(\<forall>\<sigma>. \<Gamma> \<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> srel}
  c
  {s. \<not> snd (a \<sigma>) \<longrightarrow> (\<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> srel \<and> rrel rv (xf s))})
  \<Longrightarrow> ccorres_underlying srel \<Gamma> rrel xf arrel axf P P' hs a c"
  apply (rule ccorres_from_vcg_nofail2)
  apply (erule allEI)
  apply (case_tac "snd (a \<sigma>)", simp_all)
  apply (rule hoare_complete, simp add: HoarePartialDef.valid_def)
  done


lemma ccorres_to_vcg:
  "ccorres_underlying srel \<Gamma> rrel xf arrel axf P P' [] a c \<Longrightarrow>
  (\<forall>\<sigma>. \<not> snd (a \<sigma>) \<longrightarrow> \<Gamma> \<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> srel}
  c
  {s. (\<exists>(rv, \<sigma>') \<in> fst (a \<sigma>). (\<sigma>', s) \<in> srel \<and> rrel rv (xf s))})"
  apply -
  apply rule
  apply (rule impI)
  apply (rule hoare_complete)
  apply (simp add: HoarePartialDef.valid_def cvalid_def)
  apply (intro impI allI)
  apply clarsimp
  apply (frule (5) ccorres_empty_handler_abrupt)
  apply (erule (4) ccorresE)
   apply (erule (1) EHOther)
  apply clarsimp
  apply rule
   apply simp
  apply (fastforce simp: unif_rrel_simps)
  done

lemma exec_handlers_Seq_cases0':
  assumes eh: "\<Gamma> \<turnstile>\<^sub>h \<langle>h, s\<rangle> \<Rightarrow> (n, t)"
  and     hv: "h = (a ;; b) # hs"
  and     r1: "\<And>z t'. \<lbrakk>\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> t';  \<Gamma> \<turnstile> \<langle>b, t'\<rangle> \<Rightarrow> z;
  ((\<not> isAbr z \<or> hs = []) \<and> n = length hs \<and> z = t) \<or> (\<exists>q. z = Abrupt q \<and> \<Gamma> \<turnstile>\<^sub>h \<langle>hs, q\<rangle> \<Rightarrow> (n, t));  \<not> isAbr t'  \<rbrakk> \<Longrightarrow> P"
  and     r2: "\<And>t'. \<lbrakk>\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> Abrupt t'; \<Gamma> \<turnstile>\<^sub>h \<langle>hs, t'\<rangle> \<Rightarrow> (n, t) \<rbrakk> \<Longrightarrow> P"
  shows P
  using eh hv r1 r2
proof induct
  case (EHOther h s t hs')
  hence ex: "\<Gamma> \<turnstile> \<langle>a ;; b, Normal s\<rangle> \<Rightarrow> t" by simp
  then obtain t'' where ae: "\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> t''" and be: "\<Gamma> \<turnstile> \<langle>b, t''\<rangle> \<Rightarrow> t"
    by (auto elim: exec_Normal_elim_cases)

  have r: "\<And>z t'. \<lbrakk>\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> t';  \<Gamma> \<turnstile> \<langle>b, t'\<rangle> \<Rightarrow> z;
    ((\<not> isAbr z \<or> hs = []) \<and> length hs' = length hs \<and> z = t) \<or> (\<exists>q. z = Abrupt q \<and> \<Gamma> \<turnstile>\<^sub>h \<langle>hs, q\<rangle> \<Rightarrow> (length hs', t));  \<not> isAbr t' \<rbrakk> \<Longrightarrow> P"
    by fact+

  show ?case
  proof (rule r)
    show "\<not> isAbr t''" using EHOther(2) be
      by (cases t) (auto elim: Normal_resultE Fault_resultE Stuck_resultE)

    show "((\<not> isAbr t \<or> hs = []) \<and> length hs' = length hs \<and> t = t)
        \<or> (\<exists>q. t = Abrupt q \<and> \<Gamma>\<turnstile>\<^sub>h \<langle>hs,q\<rangle> \<Rightarrow> (length hs', t))" using EHOther by simp
  qed fact+
next
  case (EHAbrupt h s z hs' n t)
  hence ex: "\<Gamma> \<turnstile> \<langle>a ;; b, Normal s\<rangle> \<Rightarrow> Abrupt z" and hs: "hs' = hs" by simp_all

  have ra: "\<And>z t'. \<lbrakk>\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> t';  \<Gamma> \<turnstile> \<langle>b, t'\<rangle> \<Rightarrow> z;
    ((\<not> isAbr z \<or> hs = []) \<and> n = length hs \<and> z = t) \<or> (\<exists>q. z = Abrupt q \<and> \<Gamma> \<turnstile>\<^sub>h \<langle>hs, q\<rangle> \<Rightarrow> (n, t));  \<not> isAbr t' \<rbrakk> \<Longrightarrow> P"
    by fact+
  have rb: "\<And>t'. \<lbrakk>\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> Abrupt t'; \<Gamma> \<turnstile>\<^sub>h \<langle>hs, t'\<rangle> \<Rightarrow> (n, t) \<rbrakk> \<Longrightarrow> P"
    by fact+

  {
    assume "\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> Abrupt z"
    hence ?case
    proof (rule rb)
      show "\<Gamma>\<turnstile>\<^sub>h \<langle>hs,z\<rangle> \<Rightarrow> (n, t)" by (fold hs) fact+
    qed
  } moreover
  {
    fix s''
    assume "\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> Normal s''" and
      "\<Gamma> \<turnstile> \<langle>b, Normal s''\<rangle> \<Rightarrow> Abrupt z"

    hence ?case
    proof (rule ra)
      show "((\<not> isAbr (Abrupt z) \<or> hs = []) \<and> n = length hs \<and> Abrupt z = t)
               \<or> (\<exists>q. Abrupt z = Abrupt q \<and> \<Gamma>\<turnstile>\<^sub>h \<langle>hs,q\<rangle> \<Rightarrow> (n, t))" using EHAbrupt(2)
        by (simp add: hs)

      show "\<not> isAbr (Normal s'')" by simp
    qed
  } ultimately show ?case using ex
    apply -
    apply (erule exec_Normal_elim_cases)
    apply (erule Abrupt_resultE)
    apply simp
    apply simp
    apply (drule Abrupt_end [OF _ refl])
    apply simp
    done
next
  case (EHEmpty s)
  thus ?case by simp
qed

lemma exec_handlers_Seq_cases' [consumes 1, case_names NotAbrupt Abrupt]:
  assumes eh: "\<Gamma> \<turnstile>\<^sub>h \<langle>(a ;; b) # hs, s\<rangle> \<Rightarrow> (n, t)"
  and     r1: "\<And>z t'. \<lbrakk>\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> t';  \<Gamma> \<turnstile> \<langle>b, t'\<rangle> \<Rightarrow> z;
  ((\<not> isAbr z \<or> hs = []) \<and> n = length hs \<and> z = t) \<or> (\<exists>q. z = Abrupt q \<and> \<Gamma> \<turnstile>\<^sub>h \<langle>hs, q\<rangle> \<Rightarrow> (n, t));  \<not> isAbr t' \<rbrakk> \<Longrightarrow> P"
  and     r2: "\<And>t'. \<lbrakk>\<Gamma> \<turnstile> \<langle>a, Normal s\<rangle> \<Rightarrow> Abrupt t'; \<Gamma> \<turnstile>\<^sub>h \<langle>hs, t'\<rangle> \<Rightarrow> (n, t) \<rbrakk> \<Longrightarrow> P"
  shows P
  using eh r1 r2
  by (rule exec_handlers_Seq_cases0' [OF _ refl], auto)

lemma ccorres_abstract_fail:
  assumes fl: "\<And>s. P s \<Longrightarrow> snd (a s)"
  shows  "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a c"
  apply (rule ccorresI')
  apply (drule fl)
  apply simp
  done

lemma ccorres_fail':
  "ccorres_underlying sr \<Gamma> rvr xf arrel axf P P' hs fail cfn"
  by (simp add: ccorres_underlying_def fail_def)

lemma ccorres_fail:
  "ccorres_underlying sr \<Gamma> rvr xf arrel axf \<top> UNIV hs fail cfn"
  by (rule ccorres_fail')

lemma ccorres_assert:
  assumes rl: "P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs f c"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs (assert P >>= (\<lambda>_. f)) c"
  apply (cases P)
   apply (simp add: assert_def)
   apply (erule rl)
  apply (simp add: ccorres_fail')
  done

definition
  exec_handlers_Hoare :: "('p \<Rightarrow> ('t, 'p, 'e) com option) \<Rightarrow>
           ('t set) \<Rightarrow> ('t, 'p, 'e) com list \<Rightarrow> ('t set) \<Rightarrow> ('t set) \<Rightarrow> bool"
where
 "exec_handlers_Hoare \<Gamma> P cs Q A \<equiv>
      \<forall>s n t. \<Gamma> \<turnstile>\<^sub>h \<langle>cs, s\<rangle> \<Rightarrow> (n, t)
               \<longrightarrow> s \<in> P \<longrightarrow> t \<notin> Normal ` (if n = length cs - 1 then - Q else - A)"

definition
  ccHoarePost :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> 'b) \<Rightarrow>
                  ('a \<Rightarrow> 'b \<Rightarrow> 't set) \<Rightarrow> ('t set)"
where
 "ccHoarePost r' xf' Q'
      \<equiv> {s. \<forall>rv. r' rv (xf' s) \<longrightarrow> s \<in> Q' rv (xf' s)}"

lemma exec_handlers_Hoare_single_from_vcg:
  "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> P c Q, A \<Longrightarrow> exec_handlers_Hoare \<Gamma> P [c] Q A"
  apply (drule hoare_sound)
  apply (simp add: cvalid_def HoarePartialDef.valid_def
                   exec_handlers_Hoare_def)
  apply (auto elim!: exec_handlers.cases)
  done

lemma exec_handlers_Hoare_from_vcg_nofail:
  "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> P c Q \<Longrightarrow> exec_handlers_Hoare \<Gamma> P (c # cs) Q A"
  apply (drule hoare_sound)
  apply (simp add: cvalid_def HoarePartialDef.valid_def
                   exec_handlers_Hoare_def split del: if_split)
  apply (clarsimp split del: if_split)
  apply (erule exec_handlers.cases, auto)
  done

lemma exec_handlers_Hoare_from_vcg_fails:
  "\<lbrakk> \<Gamma> \<turnstile>\<^bsub>/F\<^esub> P c {},UNIV; UNIV \<subseteq> A \<rbrakk> \<Longrightarrow> exec_handlers_Hoare \<Gamma> P (c # cs) Q A"
  apply (drule hoare_sound)
  apply (simp add: cvalid_def HoarePartialDef.valid_def
                   exec_handlers_Hoare_def split del: if_split)
  apply (clarsimp split del: if_split)
  apply (erule exec_handlers.cases, simp_all)
   apply (cases cs)
    apply (auto elim!: exec_handlers.cases)[1]
   apply clarsimp
   apply (frule exec_handlers_Cons_le)
   apply auto
  done

lemma exec_handlers_Hoare_NormalD:
  "\<lbrakk> exec_handlers_Hoare \<Gamma> P cs Q A; s \<in> P; \<Gamma>  \<turnstile>\<^sub>h \<langle>cs, s\<rangle> \<Rightarrow> (n, Normal t); n = length cs - 1 \<rbrakk>
       \<Longrightarrow> t \<in> Q"
  by (fastforce simp add: exec_handlers_Hoare_def)

lemma exec_handlers_Hoare_CatchD:
  "\<lbrakk> exec_handlers_Hoare \<Gamma> P cs Q A; s \<in> P; \<Gamma>  \<turnstile>\<^sub>h \<langle>cs, s\<rangle> \<Rightarrow> (n, Normal a); n \<noteq> length cs - 1 \<rbrakk>
       \<Longrightarrow> a \<in> A"
  by (fastforce simp add: exec_handlers_Hoare_def)

lemma ccorres_master_split:
  assumes ac: "ccorres_underlying sr \<Gamma> r' xf' arrel' axf' P P' hs' a c"
  and    hsw: "hs' \<noteq> [] \<Longrightarrow> hs' = hs"
  and     bd: "\<And>rv. ccorres_underlying sr \<Gamma> r xf arrel axf (R rv) (R' rv) hs (b rv) d"
  and  abort: "\<And>rv. hs' \<noteq> [] \<Longrightarrow> ccorres_underlying sr \<Gamma> arrel axf arrel axf (E rv) (E' rv)
                                      [] (b rv) Skip"
  and  valid: "\<lbrace>Q\<rbrace> a \<lbrace>\<lambda>rv. R rv and E rv\<rbrace>"
  and valid': "exec_handlers_Hoare \<Gamma> Q' (c # hs) (ccHoarePost r' xf' (\<lambda>a b. R' a))
                               {s. hs' \<noteq> [] \<longrightarrow> s \<in> ccHoarePost arrel' axf' (\<lambda>a b. E' a)}"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf (P and Q) (P' \<inter> Q') hs (a >>= (\<lambda>rv. b rv)) (c ;; d)"
  apply (rule ccorresI')
  apply (erule exec_handlers_Seq_cases')
   apply (clarsimp simp add: bind_def)
   apply (erule(3) ccorresE [OF ac])
    apply (erule(1) EHOther)
   apply simp
   apply (frule exec_handlers_Hoare_NormalD[OF valid'])
     apply (erule EHOther, simp)
    apply simp
   apply (frule(1) use_valid [OF _ valid])
   apply (clarsimp simp: unif_rrel_simps ccHoarePost_def)
   apply (drule spec, drule(1) mp)
   apply (erule_tac x=z in ccorresE [OF bd], assumption+)
     apply (clarsimp simp: split_def image_image)
     apply force
    apply (case_tac "isAbr za")
     apply (clarsimp elim!: isAbrE)
     apply (erule EHAbrupt)
     apply (erule disjE)
      apply clarsimp
      apply (rule EHEmpty)
     apply assumption
    apply (simp add: isAbr_def)
    apply (erule EHOther)
    apply (clarsimp simp: isAbr_def split_def)
   apply (clarsimp simp: split_def)
   apply force
  apply (clarsimp simp: bind_def)
  apply (cases "hs' = []")
   apply (erule(3) ccorresE [OF ac])
    apply simp
    apply (erule EHAbrupt, rule EHEmpty)
   apply simp
  apply (frule hsw)
  apply (erule(3) ccorresE [OF ac])
   apply simp
   apply (erule(1) EHAbrupt)
  apply (frule(1) use_valid [OF _ valid])
  apply (cases hs, simp_all)[1]
  apply (frule exec_handlers_Cons_le)
  apply (frule exec_handlers_Hoare_CatchD[OF valid'])
    apply (erule EHAbrupt)
    apply simp
   apply clarsimp
  apply (simp add: unif_rrel_simps ccHoarePost_def)
  apply (elim conjE)
  apply (drule spec, drule(1) mp)
  apply (rule ccorresE [OF abort], simp, assumption+)
    apply (clarsimp simp: split_def image_image)
    apply force
   apply (rule EHOther)
    apply (rule exec.intros)
   apply simp
  apply (clarsimp simp add: unif_rrel_simps split_def)
  apply force
  done

lemma ccorres_empty:
  "ccorres_underlying sr \<Gamma> r xf arrel axf P {} hs a c"
  apply (rule ccorresI')
  apply simp
  done

lemma ccorres_False:
  "ccorres_underlying sr \<Gamma> r xf arrel axf (\<lambda>s. False) P' hs a c"
  apply (rule ccorresI')
  apply simp
  done

lemmas ccorres_master_split_hs = ccorres_master_split [OF _ refl]

lemmas ccorres_master_split_nohs
    = ccorres_master_split [where hs'=Nil and E = "\<lambda>_ _. True", simplified]

lemma stronger_ccorres_guard_imp:
  assumes x: "ccorres_underlying sr \<Gamma> r xf arrel axf Q Q' hs f g"
  assumes y: "\<And>s s'. \<lbrakk> A s; s' \<in> A'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> Q s"
  assumes z: "\<And>s s'. \<lbrakk> A s; s' \<in> A'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> s' \<in> Q'"
  shows      "ccorres_underlying sr \<Gamma> r xf arrel axf A A' hs f g"
  using x
  apply -
  apply (rule ccorresI')
  apply (erule (1) ccorresE)
      apply (erule (2) y)
     apply (erule (2) z)
   apply assumption
  apply auto
  done

lemma ccorres_guard_imp:
  assumes x: "ccorres_underlying sr \<Gamma> r xf arrel axf Q Q' hs f g"
  assumes y: "\<And>s. A s \<Longrightarrow> Q s" "\<And>s. s \<in> A' \<Longrightarrow> s \<in> Q'" (* Do we prefer using subset? *)
  shows      "ccorres_underlying sr \<Gamma> r xf arrel axf A A' hs f g"
  apply (rule stronger_ccorres_guard_imp)
    apply (rule x)
   apply (simp add: y)+
  done

lemma ccorres_split_nothrow':
  fixes R' :: "'a set"
  assumes ac: "ccorres_underlying sr \<Gamma> r' xf' dc axf P P' hs a c"
  and     bd: "\<And>rv. ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' \<inter> {s. r' rv (xf' s)}) hs (b rv) d"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>"
  and valid': "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> R' c Q'"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) (P' \<inter> R') hs (a >>= (\<lambda>rv. b rv)) (c ;; d)"
  using ac valid valid'
  apply -
  apply (erule ccorres_master_split_hs)
     apply (rule bd)
    apply (rule ccorres_empty[where P=\<top>])
   apply simp
  apply (rule exec_handlers_Hoare_from_vcg_nofail)
  apply (erule conseqPost)
   apply (clarsimp simp: ccHoarePost_def)
  apply simp
  done

lemma ccorres_add_return:
  "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs (return () >>= (\<lambda>_. a)) c
      \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a c"
  by simp

lemma ccorres_add_return2:
  "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs (a >>= (\<lambda>x. return x)) c
      \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a c"
  by simp

lemma ccorres_return:
  assumes P:  "\<And>s. R s \<Longrightarrow>
     E \<turnstile> (R' \<inter> {s'. (s, s') \<in> sr}) f {s'. (s, s') \<in> sr \<and> r x (xf s')}"
  shows "ccorres_underlying sr E r xf arrel axf R R' hs (return x) f"
  apply (rule ccorresI')
  apply (frule P)
  apply (drule (1) exec_handlers_use_hoare_nothrow)
   apply clarsimp
  apply (clarsimp simp: return_def unif_rrel_simps)
  done

lemma ccorres_return_Skip':
  shows  "ccorres_underlying sr \<Gamma> r xf arrel axf \<top> (UNIV \<inter> {s. r a (xf s)}) hs
                             (return a) SKIP"
  apply (rule ccorres_return)
  apply simp
  apply (rule HoarePartial.Skip)
  apply clarsimp
  done

lemma ccorres_return_Skip:
  shows  "ccorres_underlying sr \<Gamma> dc xf arrel axf \<top> UNIV hs (return a) SKIP"
  by (rule ccorres_return_Skip'[where r=dc, simplified])


lemma ccorres_split_throws:
  assumes ac: "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a c"
  and valid': "\<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> R' c {}, UNIV" (* Always throws *)
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf P (P' \<inter> R') hs a (c ;; d)"
  apply (rule ccorres_add_return2)
  apply (rule ccorres_guard_imp,
         rule ccorres_master_split_hs[OF ac])
       apply (rule ccorres_empty[where P=\<top>])
      apply (rule ccorres_return_Skip')
     apply wp
    apply clarsimp
    apply (rule exec_handlers_Hoare_from_vcg_fails [OF valid'])
    apply (simp add: ccHoarePost_def)
   apply simp
  apply simp
  done

lemma ccorres_Un:
  assumes pt: "ccorres_underlying sr \<Gamma> r xf arrel axf P PT hs a c"
  and     pn: "ccorres_underlying sr \<Gamma> r xf arrel axf P PN hs a c"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf P (PT \<union> PN) hs a c"
  using pt pn
  apply -
  apply (rule ccorresI)
   apply (erule UnE)
    apply (erule (5) ccorresE)
    apply simp
   apply (erule (5) ccorresE)
   apply simp
   apply (erule UnE)
    apply (erule (5) ccorresE)
    apply (erule bexI [rotated], clarsimp)
   apply (erule (5) ccorresE)
   apply (erule bexI [rotated], clarsimp)
   done

lemma ccorres_throw:
  assumes abh: "ccorres_underlying sr \<Gamma> arrel axf arrel axf P P' hs a h"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf P P' (h#hs) a Throw"
  apply (rule ccorresI')
  apply (erule exec_handlers.cases, simp_all)
   apply (erule exec_Normal_elim_cases)
   apply clarsimp
   apply (frule exec_handlers_Cons_le)
   apply (rule ccorresE [OF abh], assumption+)
   apply (simp add: unif_rrel_def split_def)
   apply (erule rev_bexI, simp)
  apply (erule exec_Normal_elim_cases)
  apply simp
  done

lemma ccorres_split_throw:
  assumes abh: "ccorres_underlying sr \<Gamma> arrel axf arrel axf P P' hs a h"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf P P' (h#hs) a (Throw ;; d)"
  apply (rule ccorres_guard_imp, rule ccorres_split_throws)
    apply (rule ccorres_throw[OF abh])
    apply (rule HoarePartial.Throw)
    apply (rule order_refl)
   apply simp+
  done


lemma ccorres_tmp_lift1:
  assumes rl: "\<And>rv'. P rv'
  \<Longrightarrow> ccorres_underlying srel \<Gamma> rrel xf arrel axf G (G' \<inter> {s. xf' s = rv'}) hs m c"
  shows "ccorres_underlying srel \<Gamma> rrel xf arrel axf G (G' \<inter> {s. P (xf' s)}) hs m c"
  by (auto intro!: ccorresI dest!: rl elim: ccorresE)

lemma ceqvhD1:
  assumes lhs: "\<Gamma> \<turnstile>\<^sub>h \<langle>a # hs, s\<rangle> \<Rightarrow> (n, s')"
  and     xf:  "xf s = v"
  and     ceq: "\<And>s'. ceqv \<Gamma> xf v s s' a b"
  shows   "\<Gamma> \<turnstile>\<^sub>h \<langle>b # hs, s\<rangle> \<Rightarrow> (n, s')"
  using lhs xf
  apply -
  apply (ind_cases "\<Gamma> \<turnstile>\<^sub>h \<langle>a # hs, s\<rangle> \<Rightarrow> (n, s')")
   apply (rule EHAbrupt)
    apply (erule (1) ceqvD1 [OF _ _ ceq])
   apply assumption
  apply simp
  apply (rule EHOther)
   apply (erule (1) ceqvD1 [OF _ _ ceq])
  apply assumption
  done

lemmas ceqvhD2 = ceqvhD1 [OF _ _ ceqv_sym]

lemma ccorres_tmp_lift2:
  assumes rl: "\<And>t t'. ceqv \<Gamma> xf' rv' t t' c c'"
  and c: "ccorres_underlying srel \<Gamma> rrel xf arrel axf G (G'' rv') hs m c'"
  and geq: "G'' rv' \<inter> {s. rv' = xf' s} = G' \<inter> {s. rv' = xf' s}"
  shows "ccorres_underlying srel \<Gamma> rrel xf arrel axf G (G' \<inter> {s. xf' s = rv'}) hs m c"
  using c
  apply -
  apply (rule ccorresI')
   apply (erule (2) ccorresE)
     apply (subst (asm) Int_eq_symmetric)
     apply (subst (asm) geq [symmetric])
     apply fastforce
    apply assumption
   apply simp
   apply (erule conjE)+
   apply (erule (1) ceqvhD1 [OF _ _ rl])
   apply simp
  apply fastforce
  done

lemma ccorres_init_tmp_lift2:
  assumes rl: "\<And>t t'. ceqv \<Gamma> xf' rv' t t' c c'"
  and c: "ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs m c'"
  shows "ccorres_underlying srel \<Gamma> rrel xf arrel axf G (G' \<inter> {s. xf' s = rv'}) hs m c"
  using c
  apply -
  apply (rule ccorresI')
   apply (erule (2) ccorresE)
     apply fastforce
    apply assumption
    apply simp
    apply (erule conjE)+
    apply (erule (1) ceqvhD1 [OF _ _ rl])
   apply simp
  apply fastforce
  done

lemma ccorres_Call:
  assumes ge: "\<Gamma> f = Some (Catch bdy Skip)"
  and    cul: "ccorres_underlying sr \<Gamma> r xf r xf P P' (Skip # hs) a bdy"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a (Call f)"
  using ge cul
  apply -
  apply (rule ccorresI')
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (erule exec_Normal_elim_cases | simp)+
   apply clarsimp
   apply (erule exec_Normal_elim_cases | simp)+
     apply (erule (4) ccorresE)
      apply (erule EHAbrupt, rule EHOther)
       apply (rule exec.Skip)
      apply simp
     apply (simp add: unif_rrel_simps)
     apply fastforce
    apply (erule (4) ccorresE)
     apply (erule (1) EHOther)
    apply (simp add: unif_rrel_simps)
    apply fastforce
   apply simp
  apply simp
  done

lemma ccorres_call:
  assumes  cul: "ccorres_underlying sr \<Gamma> r xf' rrel xf' P (i ` P') [] a (Call f)"
  and      gsr: "\<And>a b x s t. (x, t) \<in> sr \<Longrightarrow> (x, g a b (clean s t)) \<in> sr"
  and      res: "\<And>a s t rv. r rv (xf' t) \<Longrightarrow> r rv (xf (g a t (clean s t)))"
  and      ist: "\<And>x s. (x, s) \<in> sr \<Longrightarrow> (x, i s) \<in> sr"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a (call i f clean (\<lambda>x y. Basic (g x y)))"
  apply (rule ccorresI')
  apply (erule exec_handlers.cases, simp_all)[1]
   apply clarsimp
   apply (erule exec_call_Normal_elim, simp_all)[1]
    apply (clarsimp elim!: exec_Normal_elim_cases)
   apply (rule ccorresE[OF cul ist], assumption+, simp+)
    apply (rule EHAbrupt)
     apply (erule(1) exec.Call)
    apply (rule EHEmpty)
   apply simp
  apply clarsimp
  apply (erule exec_call_Normal_elim, simp_all)[1]
     apply (clarsimp elim!: exec_Normal_elim_cases)
     apply (rule ccorresE[OF cul ist], assumption+, simp+)
      apply (rule EHOther, erule(1) exec.Call)
      apply simp
     apply (simp add: unif_rrel_simps)
     apply (erule rev_bexI)
     apply (simp add: gsr res)
    apply (rule ccorresE[OF cul ist], assumption+, simp+)
     apply (rule EHOther, erule(1) exec.Call)
     apply simp
    apply simp
   apply (rule ccorresE[OF cul ist], assumption+, simp+)
    apply (rule EHOther, erule(1) exec.Call)
    apply simp
   apply simp
  apply (rule ccorresE[OF cul ist], assumption+, simp+)
   apply (rule EHOther, erule exec.CallUndefined)
   apply simp
  apply simp
  done

declare semantic_equivD1 [dest]
declare semantic_equivD2 [dest]

lemma exec_handlers_semantic_equiv0:
  assumes se: "\<And>s'. semantic_equiv \<Gamma> s s' a b"
  and     eh: "\<Gamma> \<turnstile>\<^sub>h \<langle>a # hs, s\<rangle> \<Rightarrow> (n, t)"
  shows   "\<Gamma> \<turnstile>\<^sub>h \<langle>b # hs,s\<rangle> \<Rightarrow> (n, t)"
  using se eh
  apply -
  apply (erule ceqvhD1 [where xf = "\<lambda>_. ()" and v = "()", folded semantic_equiv_def])
   apply simp
  apply assumption
  done

lemmas exec_handlers_semantic_equivD1 = exec_handlers_semantic_equiv0 [rotated]
lemmas exec_handlers_semantic_equivD2
  = exec_handlers_semantic_equiv0 [OF iffD1 [OF semantic_equiv_sym], rotated]

lemma exec_handlers_semantic_equiv:
  assumes se: "\<And>s'. semantic_equiv \<Gamma> s s' a b"
  shows   "\<Gamma> \<turnstile>\<^sub>h \<langle>a # hs, s\<rangle> \<Rightarrow> (n, t) = \<Gamma> \<turnstile>\<^sub>h \<langle>b # hs,s\<rangle> \<Rightarrow> (n, t)"
  using se
  apply -
  apply rule
   apply (erule (1) exec_handlers_semantic_equiv0)
  apply (subst (asm) semantic_equiv_sym)
  apply (erule (1) exec_handlers_semantic_equiv0)
  done

lemma ccorres_semantic_equiv0:
  assumes rl: "\<And>s s'. s \<in> G' \<Longrightarrow> semantic_equiv \<Gamma> s s' c c'"
  and      c: "ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs m c"
  shows    "ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs m c'"
  using c rl
  apply -
  apply (rule ccorresI')
  apply (erule (4) ccorresE)
  apply (erule exec_handlers_semantic_equivD2)
   apply assumption
  apply (clarsimp elim!: bexI [rotated])
  done

lemmas ccorres_semantic_equivD1  = ccorres_semantic_equiv0 [rotated]
lemmas ccorres_semantic_equivD2
  = ccorres_semantic_equiv0 [OF iffD1 [OF semantic_equiv_sym], rotated]

(* This is so we can get the name --- if it is done at lemmas, it uses the
  (nameless) RHS *)
declare ccorres_semantic_equivD1
declare ccorres_semantic_equivD2

lemma ccorres_semantic_equiv:
  assumes rl: "\<And>s s'. s \<in> G' \<Longrightarrow> semantic_equiv \<Gamma> s s' c c'"
  shows "ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs m c =
  ccorres_underlying srel \<Gamma> rrel xf arrel axf G G' hs m c'"
  using rl
  apply -
  apply rule
   apply (erule (1) ccorres_semantic_equiv0)
  apply (subst (asm) semantic_equiv_sym)
  apply (erule (1) ccorres_semantic_equiv0)
  done

lemmas ccorres_exec_cong = ccorres_semantic_equiv [OF semantic_equivI]

definition
  "exec_While \<Gamma> S c s s' \<equiv> exec \<Gamma> (While S c) s s'"

(* nearly works - can't get simplifier to use both the While and Seq rules *)
lemmas ccorres_exec_congs = ccorres_exec_cong exec_While_cong[folded exec_While_def] exec_Seq_cong
lemmas exec_eq_simps = exec_Guard_UNIV_simp exec_Seq_Skip_simps

lemma test_ccorres_exec_congs:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a
         (Guard F UNIV Skip ;; While S (c ;; Guard F UNIV Skip))
   = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (While S c)"
  apply (simp add: exec_eq_simps cong: ccorres_exec_congs)
  oops

lemma exec_handlers_assoc:
  "E \<turnstile>\<^sub>h \<langle>(c1;; (c2 ;; c3)) # hs, s\<rangle> \<Rightarrow> (n, t) = E \<turnstile>\<^sub>h \<langle>(c1;;c2;;c3) # hs,s\<rangle> \<Rightarrow> (n, t)"
  apply (rule exec_handlers_semantic_equiv)
  apply (rule semantic_equivI)
  apply (rule exec_assoc)
  done

lemma ccorres_rhs_assoc:
  assumes cc: "ccorres_underlying sr E r xf arrel axf G G' hs a (c ;; (d ;; e))"
  shows "ccorres_underlying sr E r xf arrel axf G G' hs a (c ;; d ;; e)"
  using cc
  apply (rule ccorres_semantic_equivD1)
  apply (rule semantic_equivI)
  apply (rule exec_assoc)
  done

lemma ccorres_rhs_assoc2:
  "ccorres_underlying sr E r xf arrel axf G G' hs a ((c ;; c') ;; c'')
  \<Longrightarrow> ccorres_underlying sr E r xf arrel axf G G' hs a (c ;; (c' ;; c''))"
  apply (erule iffD2 [OF ccorres_semantic_equiv, rotated])
  apply (rule semantic_equivI)
  apply (rule exec_assoc)
  done

lemma ccorres_basic_srnoop:
  assumes asm: "ccorres_underlying sr E r xf arrel axf G G' hs a c"
  and   gsr: "\<And>s s'. (s, s') \<in> sr \<Longrightarrow> (s, g s') \<in> sr"
  and   gG: "\<And>s'. s' \<in> G' \<Longrightarrow> g s' \<in> G'"
  shows "ccorres_underlying sr E r xf arrel axf G G' hs a (Basic g ;; c)"
  using asm
  apply -
  apply (rule ccorresI')
  apply clarsimp
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (erule exec_Normal_elim_cases)
    apply (erule exec_Normal_elim_cases)
    apply simp
    apply (erule (4) ccorresE [OF _ gsr _ gG])
     apply (erule (1) EHAbrupt)
    apply clarsimp
    apply (erule bexI [rotated])
    apply simp
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
   apply (erule exec_Normal_elim_cases)
   apply simp
   apply (erule (4) ccorresE [OF _ gsr _ gG])
    apply (erule (1) EHOther)
   apply clarsimp
    apply (erule bexI [rotated])
    apply simp
  apply simp
  done


lemma ccorres_symb_exec_r:
  assumes cul: "ccorres_underlying sr E r xf arrel axf R Q' hs a y"
  and     ex:  "E \<turnstile> R' m Q', {}"
  and   pres:  "\<And>s. R s \<Longrightarrow> E \<turnstile> (R' \<inter> {s'. (s, s') \<in> sr}) m {s'. (s, s') \<in> sr}"
  shows "ccorres_underlying sr E r xf arrel axf R R' hs a (m ;; y)"
  apply -
  apply (rule ccorres_guard_imp)
  apply (subst return_bind [symmetric, where f = "\<lambda>x. a"], rule ccorres_split_nothrow')
       apply (rule ccorres_return [where r = "\<lambda>x y. True"])
       apply (drule pres, simp)
      apply (rule ccorres_guard_imp)
        apply (rule cul)
       apply assumption
      apply simp
     apply wp
    apply (rule ex)
   apply simp
  apply simp
  done


(* Throw stuff *)

lemma ccorres_rel_imp:
  assumes x: "ccorres_underlying sr \<Gamma> r' xf' r' xf' P P' hs f g"
  assumes y: "\<And>x y. r' x (xf' y) \<Longrightarrow> r x (xf y)"
  shows      "ccorres_underlying sr \<Gamma> r xf r xf P P' hs f g"
  using x
  apply -
  apply (rule ccorresI')
   apply (erule (5) ccorresE)
  apply clarsimp
  apply (erule bexI [rotated])
  apply (simp add: y unif_rrel_def)
  done

lemma ccorres_liftM_simp [simp]:
  "(ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs (liftM t f) g)
    = (ccorres_underlying sr \<Gamma> (r \<circ> t) xf (arrel \<circ> t) axf P P' hs f g)"
  apply rule
   apply (rule ccorresI')
   apply (erule (3) ccorresE)
     apply clarsimp
    apply assumption
   apply (clarsimp simp add: liftM_def bind_def return_def)
   apply (erule bexI [rotated])
   apply (simp add: unif_rrel_def)
  apply (rule ccorresI')
  apply simp
  apply (erule (5) ccorresE)
  apply (simp add: liftM_def NonDetMonad.bind_def return_def)
  apply (erule bexI [rotated])
  apply (simp add: unif_rrel_def split: if_split_asm)
  done

lemma ccorres_cond_weak:
  assumes c1: "ccorres_underlying sr \<Gamma> r xf arrel axf Pt Rt hs a c"
  and     c2: "ccorres_underlying sr \<Gamma> r xf arrel axf Pf Rf hs a c'"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf (Pt and Pf) ((Rt \<inter> b) \<union> (Rf \<inter> -b)) hs a (Cond b  c c')"
  apply (rule ccorresI')
  apply (erule UnE)
   apply (drule exec_handlers_semantic_equivD1 [where b = c])
    apply (rule semantic_equivI)
    apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondTrue)
   apply (fastforce elim: ccorresE [OF c1] elim!: bexI [rotated])
  apply (drule exec_handlers_semantic_equivD2 [where b = c'])
   apply (rule semantic_equivI)
   apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondFalse)
  apply (fastforce elim: ccorresE [OF c2] elim!: bexI [rotated])
  done

lemma ccorres_cond_empty:
  assumes c2: "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a c'"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a (Cond {} c c')"
  apply (rule ccorres_guard_imp)
  apply (rule ccorres_cond_weak [OF _ c2])
    apply (rule ccorres_empty)
   apply simp
  apply simp
  done

lemma ccorres_cond_univ:
  assumes c1: "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a c"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf P P' hs a (Cond UNIV c c')"
  apply (rule ccorres_guard_imp)
  apply (rule ccorres_cond_weak [OF c1])
    apply (rule ccorres_empty)
   apply simp
  apply simp
  done

lemma ccorres_Guard:
  assumes cc: "ccorres_underlying sr \<Gamma> r xf arrel axf A C' hs a c"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf A (C' \<inter> S) hs a (Guard F S c)"
  using cc
  apply -
  apply (rule ccorresI')
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (erule exec_Normal_elim_cases)
     apply (erule (4) ccorresE)
      apply (erule (1) EHAbrupt)
     apply (clarsimp elim!: bexI [rotated])
    apply clarsimp
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
    apply (erule (4) ccorresE)
     apply (erule (1) EHOther)
    apply (clarsimp elim!: bexI [rotated])
   apply clarsimp
  apply simp
  done

lemma ccorres_Guard_Seq:
  assumes cc: "ccorres_underlying sr \<Gamma> r xf arrel axf A C' hs a (c ;; d)"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf A (C' \<inter> S) hs a (Guard F S c ;; d)"
  apply (rule ccorres_semantic_equivD2 [OF _ Guard_Seq_semantic_equiv])
  apply (rule ccorres_Guard [OF cc])
  done

lemma ccorres_cond_const:
  assumes c1: "P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf Pt Rt hs a c"
  and     c2: "\<not> P \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf Pf Rf hs a c'"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf ((\<lambda>s. P \<longrightarrow> Pt s) and (\<lambda>s. \<not> P \<longrightarrow> Pf s)) ((Rt \<inter> {_. P}) \<union> (Rf \<inter> {_. \<not> P})) hs a (Cond {_. P} c c')"
  apply (rule ccorresI')
  apply (erule UnE)
   apply (drule exec_handlers_semantic_equivD1 [where b = c])
    apply (rule semantic_equivI)
    apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondTrue)
   apply (fastforce elim: ccorresE [OF c1] elim!: bexI [rotated])
  apply (drule exec_handlers_semantic_equivD2 [where b = c'])
   apply (rule semantic_equivI)
   apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondFalse)
  apply (fastforce elim: ccorresE [OF c2] elim!: bexI [rotated])
  done




lemmas in_monad_pre' = in_whenE [where v = r for r] in_liftE [where v = r for r]
                  in_bind in_returnOk [where v' = r for r] in_throwError [where v = r for r]
                  in_assertE in_assert in_return in_assert_opt
                  in_get in_gets in_put in_when [where v = r for r]
                  in_modify [where v = r for r]

lemmas in_monad' = in_monad_pre' [where r = "fst r" and s' = "snd r" for r, simplified surjective_pairing [symmetric]]

declare not_snd_bindI1 [intro?]
declare not_snd_bindI2 [intro?]

lemma ccorres_symb_exec_l:
  assumes cc: "\<And>rv. ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv) hs (f rv) c"
  and   pres: "\<And>s. \<lbrace>(=) s\<rbrace> m \<lbrace>\<lambda>r. (=) s\<rbrace>"
  and    val: "\<lbrace>G\<rbrace> m \<lbrace>Q\<rbrace>"
  and     ef: "empty_fail m"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf G {s'. \<forall>rv s. (s, s') \<in> sr \<and> Q rv s \<longrightarrow> s' \<in> Q' rv} hs (m >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorresI')
  apply (frule not_snd_bindI1)
  apply (erule empty_fail_not_snd [OF _ ef, THEN exE])
  apply (case_tac x)
  apply simp
  apply (frule (1) use_valid [OF _  val])
  apply (frule use_valid [OF _ pres])
   apply (rule refl)
  apply simp
  apply (rule ccorresE [OF cc], assumption+)
     apply fastforce
    apply (erule (1) not_snd_bindI2)
   apply assumption
  apply (clarsimp simp: bind_def split: prod.splits)
  apply (erule (1) my_BallE)
  apply (erule bexI [rotated])
  apply force
  done

lemma ccorres_symb_exec_l':
  assumes cc: "\<And>rv. ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) G' hs (f rv) c"
  and     v1: "\<And>s. NonDetMonad.valid ((=) s) m (\<lambda>r. (=) s)"
  and     v2: "NonDetMonad.valid G m Q"
  and     ef: "empty_fail m"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs (m >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_symb_exec_l [OF cc v1 v2 ef])
   apply simp+
  done

lemma ccorres_symb_exec_l2:
  assumes cc: "\<And>rv. ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv) hs (f rv) c"
  and     v1: "\<And>s. G s \<Longrightarrow> exs_valid ((=) s) m (\<lambda>r. (=) s)"
  and     v2: "NonDetMonad.valid G m Q"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf G {s'. \<forall>rv s. (s, s') \<in> sr \<and> Q rv s \<longrightarrow> s' \<in> Q' rv} hs (m >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorresI')
  apply (frule use_exs_valid [OF v1])
   apply (rule refl)
  apply clarsimp
  apply (frule (1) use_valid [OF _ v2])
  apply (drule (1) not_snd_bindD)
  apply (rule ccorresE [OF cc])
       apply assumption
      apply assumption
     apply (drule spec, erule mp)
     apply fastforce
    apply simp
   apply assumption
  apply (fastforce simp: in_monad')
  done

lemma exec_handlers_SkipD:
  "\<Gamma>\<turnstile>\<^sub>h \<langle>SKIP # hs, s\<rangle> \<Rightarrow> (n, s') \<Longrightarrow> s' = Normal s \<and> n = length hs"
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (erule exec_Normal_elim_cases)
    apply simp
   apply clarsimp
   apply (erule exec_Normal_elim_cases)
   apply simp
   apply simp
   done

lemma ccorres_trim_redundant_throw':
  assumes cc: "ccorres_underlying sr \<Gamma> arrel axf arrel axf G G' (SKIP # hs) a c"
  and    xfg: "\<And>s. axf (f s) = axf s"
  and    sr:  "\<And>t t'. (t, t') \<in> sr \<Longrightarrow> (t, f t') \<in> sr"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf G G' (SKIP # hs)
              a (c;; Basic f;; THROW)"
  apply (rule ccorres_rhs_assoc)
  apply (rule ccorresI')
  apply clarsimp
  apply (erule exec_handlers_Seq_cases')
   apply simp
   apply (erule disjE)
    \<comment> \<open>Non-abrupt case\<close>
    apply clarsimp
    apply (erule_tac x = "t'" in ccorresE [OF cc])
        apply assumption
       apply assumption
      apply assumption
     apply (erule (1) EHOther)
    apply simp
    apply (erule exec_Normal_elim_cases | simp)+
   \<comment> \<open>Abrupt case\<close>
   apply clarsimp
   apply (erule_tac x = "t'" in ccorresE [OF cc])
       apply assumption
      apply assumption
     apply assumption
    apply (erule (1) EHOther)
   apply clarsimp
   apply (frule exec_handlers_Cons_le)
   apply (erule exec_Normal_elim_cases | simp)+
   apply (frule exec_handlers_SkipD)
   apply (clarsimp simp: xfg unif_rrel_simps elim!: bexI [rotated] sr)
  apply (frule exec_handlers_SkipD)
  apply (erule_tac x = "Normal t'" in ccorresE [OF cc])
      apply assumption
     apply assumption
    apply assumption
   apply (erule EHAbrupt)
   apply simp
  apply (clarsimp simp: xfg unif_rrel_simps elim!: bexI [rotated])
  done

lemma ccorres_req:
  assumes eq: "\<And>s s'. \<lbrakk> (s, s') \<in> sr; G s; s' \<in> G' \<rbrakk> \<Longrightarrow> F"
  and     rl: "F \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a c"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a c"
  apply (rule ccorresI')
  apply clarsimp
  apply (frule (2) eq [THEN rl])
  apply (erule (5) ccorresE)
  apply fastforce
  done

lemma ccorres_gen_asm:
  assumes rl: "P \<Longrightarrow> ccorres_underlying \<Gamma> sr r xf arrel axf G G' hs a c"
  shows   "ccorres_underlying \<Gamma> sr r xf arrel axf (G and (\<lambda>_. P)) G' hs a c"
  apply (rule ccorres_req)
   prefer 2
   apply (rule ccorres_guard_imp)
   apply (erule rl)
    apply simp+
    done

lemma ccorres_gen_asm2:
  assumes rl: "P \<Longrightarrow> ccorres_underlying \<Gamma> sr r xf arrel axf G G' hs a c"
  shows   "ccorres_underlying \<Gamma> sr r xf arrel axf G (G' \<inter> {_. P}) hs a c"
  apply (rule ccorres_req)
   prefer 2
   apply (rule ccorres_guard_imp)
   apply (erule rl)
    apply (simp split: if_split_asm)+
    done

lemma ccorres_guard_imp2:
  assumes cc: "ccorres_underlying sr \<Gamma> r xf arrel axf Q Q' hs f g"
  and     rl: "\<And>s s'. \<lbrakk> (s, s') \<in> sr; A s; s' \<in> A' \<rbrakk> \<Longrightarrow> Q s \<and> s' \<in> Q'"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf A A' hs f g"
  using cc
  apply -
  apply (rule ccorresI')
  apply (frule (2) rl)
  apply (erule conjE)
  apply (erule (5) ccorresE)
  apply (fastforce elim: bexI [rotated])
  done


lemma ccorres_cond_both:
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> R s \<longrightarrow> P s = (s' \<in> P')"
  and     c1: "ccorres_underlying sr \<Gamma> r xf arrel axf Pt Rt hs a c"
  and     c2: "ccorres_underlying sr \<Gamma> r xf arrel axf Pf Rf hs a c'"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf (R and (\<lambda>s. P s \<longrightarrow> Pt s) and (\<lambda>s. \<not> P s \<longrightarrow> Pf s)) ((Rt \<inter> P') \<union> (Rf \<inter> - P')) hs a (Cond P' c c')"
  apply (rule ccorresI')
  apply (erule UnE)
   apply (drule exec_handlers_semantic_equivD1 [where b = c])
    apply (rule semantic_equivI)
    apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondTrue)
   apply (fastforce simp: abs elim: ccorresE [OF c1] elim!: bexI [rotated])
  apply (drule exec_handlers_semantic_equivD2 [where b = c'])
   apply (rule semantic_equivI)
   apply (fastforce elim: exec_Normal_elim_cases intro: exec.CondFalse)
  apply (fastforce simp: abs elim: ccorresE [OF c2] elim!: bexI [rotated])
  done

lemma ccorres_abstract:
  assumes ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and       cc: "\<And>rv'. ccorres_underlying sr \<Gamma> r xf arrel axf G (G' rv') hs a (d' rv')"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf G {s. s \<in> G' (xf' s)} hs a d"
  apply (rule ccorresI')
  apply (erule (1) ccorresE [OF cc])
     apply simp
    apply assumption
   apply (erule ceqvhD1 [OF _ refl ceqv])
  apply (clarsimp elim!: bexI [rotated])
  done

lemma ccorres_split_nothrow:
  fixes R' :: "'a set"
  assumes ac: "ccorres_underlying sr \<Gamma> r' xf' r' xf' P P' hs a c"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. r' rv rv' \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' rv')"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>"
  and valid': "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> R' c {s. \<forall>rv. r' rv (xf' s) \<longrightarrow> s \<in> Q' rv (xf' s)}"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) (P' \<inter> R') hs (a >>= (\<lambda>rv. b rv)) (c ;; d)"
  apply (rule ccorres_master_split_hs[OF ac])
     apply (rule ccorres_abstract[OF ceqv])
     apply (rule_tac P="r' rv rv'" in ccorres_gen_asm2)
     apply (erule bd)
    apply (rule ccorres_empty[where P=\<top>])
   apply (simp add: valid)
  apply (rule exec_handlers_Hoare_from_vcg_nofail)
  apply (rule conseqPost, rule valid')
   apply (clarsimp simp: ccHoarePost_def)
  apply simp
  done



(* We use composition here (over something like xf'') so that we can detect hand-rolled
   corres lemmas --- otherwise, there is no real way. *)

lemma ccorres_split_nothrow_record:
  fixes R' :: "'a set"
  assumes ac: "ccorres_underlying sr \<Gamma> r' (xfr \<circ> xf') r' (xfr \<circ> xf') P P' hs a c"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. r' rv rv' \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' (xfru (\<lambda>_. rv') oldv))"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>"
  and valid': "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> R' c {s. xf' s = xfru (\<lambda>_. (xfr \<circ> xf') s) oldv \<and> (\<forall>rv. r' rv ((xfr \<circ> xf') s) \<longrightarrow> (s \<in> Q' rv ((xfr \<circ> xf') s)))}"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) (P' \<inter> R') hs (a >>= (\<lambda>rv. b rv)) (c ;; d)"
  apply (rule ccorres_master_split_hs[OF ac])
     apply (rule ccorres_abstract [OF ceqv])
     apply (rule_tac P="d' rv' = d' (xfru (\<lambda>_. (xfr rv')) oldv)" in ccorres_gen_asm2)
     apply (rule_tac P="r' rv (xfr rv')" in ccorres_gen_asm2)
     apply simp
     apply (erule bd)
    apply (rule ccorres_empty[where P=\<top>])
   apply (simp add: valid)
  apply (rule exec_handlers_Hoare_from_vcg_nofail)
  apply (rule conseqPost[OF valid'])
   apply (clarsimp simp: ccHoarePost_def)
  apply simp
  done

lemma ccorres_move_Guard_Seq:
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> P s \<and> P' s' \<longrightarrow> G' s'"
  and      cc: "ccorres_underlying sr \<Gamma> r xf arrel axf A C' hs a (c ;; d)"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf (A and P) (C' \<inter> Collect P') hs a (Guard F (Collect G') c ;; d)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_Guard_Seq [OF cc])
  apply simp
  apply (rule abs [rule_format])
  apply fastforce
  done

lemma ccorres_move_Guard:
  assumes abs: "\<forall>s s'. (s, s') \<in> sr \<and> P s \<and> P' s' \<longrightarrow> G' s'"
  and      cc: "ccorres_underlying sr \<Gamma> r xf arrel axf A C' hs a c"
  shows   "ccorres_underlying sr \<Gamma> r xf arrel axf (A and P) (C' \<inter> Collect P') hs a (Guard F (Collect G') c)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_Guard [OF cc])
  apply simp
  apply (rule abs [rule_format])
  apply fastforce
  done

section "novcg"

lemma ccorres_to_vcg':
  "\<lbrakk> ccorres_underlying srel \<Gamma> rrel xf arrel axf P P' [] a c; \<not> snd (a \<sigma>) \<rbrakk> \<Longrightarrow>
    \<Gamma>\<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> srel} c
       {s. \<exists>(rv, \<sigma>')\<in>fst (a \<sigma>). (\<sigma>', s) \<in> srel \<and> rrel rv (xf s)}"
  apply (drule  ccorres_to_vcg)
  apply clarsimp
  done

lemma exec_handlers_Hoare_UNIV:
  "guard_is_UNIV r xf Q \<Longrightarrow>
   exec_handlers_Hoare \<Gamma> UNIV cs (ccHoarePost r xf Q) UNIV"
  by (clarsimp simp: exec_handlers_Hoare_def ccHoarePost_def
                     guard_is_UNIV_def)

lemmas ccorres_master_split_nohs_UNIV
    = ccorres_master_split_nohs [OF _ _ _ exec_handlers_Hoare_UNIV, simplified]

lemma ccorres_split_nothrow_novcg:
  fixes R' :: "'a set"
  assumes ac: "ccorres_underlying sr \<Gamma> r' xf' r' xf' P P' [] a c"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. r' rv rv' \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' rv')"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>"
  and  novcg: "guard_is_UNIV r' xf' Q'"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) P' hs (a >>= (\<lambda>rv. b rv)) (c ;; d)"
  apply (rule ccorres_master_split_nohs_UNIV)
     apply (rule ac)
    apply (rule ccorres_abstract[OF ceqv])
    apply (rule ccorres_gen_asm2)
    apply (erule bd)
   apply (simp add: valid)
  apply (cut_tac novcg, simp add: guard_is_UNIV_def)
  done

lemma ccorres_split_nothrow_record_novcg:
  fixes R' :: "'a set"
  assumes ac: "ccorres_underlying sr \<Gamma> r' (xfr \<circ> xf') r' (xfr \<circ> xf') P P' [] a c"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. r' rv rv' \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' (xfru (\<lambda>_. rv') oldv))"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>"
  and  novcg: "guard_is_UNIV r' (xfr \<circ> xf') Q'"
  \<comment> \<open>This might cause problems \<dots> has to be preserved across c in vcg case, but we can't do that\<close>
  and xfoldv: "\<And>s. xf' s = xfru (\<lambda>_. (xfr \<circ> xf') s) oldv"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) P' hs (a >>= (\<lambda>rv. b rv)) (c ;; d)"
  apply (rule ccorres_master_split_nohs_UNIV)
     apply (rule ac)
    apply (rule ccorres_abstract[OF ceqv])
    apply (rule_tac P="d' rv' = d' (xfru (\<lambda>_. (xfr rv')) oldv)" in ccorres_gen_asm2)
    apply (rule_tac P="r' rv (xfr rv')" in ccorres_gen_asm2)
    apply simp
    apply (erule bd)
   apply (rule valid)
  apply (simp add: xfoldv[symmetric, unfolded o_def])
  apply (cut_tac novcg, clarsimp simp: guard_is_UNIV_def)
  done

definition
  inl_rrel :: "('e + 'c \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('e + 'a \<Rightarrow> 'b \<Rightarrow> bool)" where
 "inl_rrel rrel \<equiv> \<lambda>x. case x of Inl e \<Rightarrow> rrel (Inl e) | _ \<Rightarrow> \<bottom>"

definition
  inr_rrel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('e + 'a \<Rightarrow> 'b \<Rightarrow> bool)" where
 "inr_rrel rrel \<equiv> \<lambda>x. case x of Inr rv \<Rightarrow> rrel rv | _ \<Rightarrow> \<bottom>"

lemma inl_inr_rrel_simps[simp]:
  "inl_rrel rrel' (Inl e) = rrel' (Inl e)"
  "inr_rrel rrel (Inr rv) = rrel rv"
  "inl_rrel rrel' (Inr rv) = \<bottom>"
  "inr_rrel rrel (Inl rv) = \<bottom>"
  by (simp add: inl_rrel_def inr_rrel_def)+

lemma inl_inrE:
  "\<lbrakk> inl_rrel rrel' v ex; \<And>e. \<lbrakk> v = Inl e; rrel' (Inl e) ex \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  "\<lbrakk> inr_rrel rrel v rv; \<And>r. \<lbrakk> v = Inr r; rrel r rv \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (simp add: inl_rrel_def inr_rrel_def split: sum.split_asm)+

lemma ccorres_master_splitE:
  fixes a :: "('s, 'e + 'a) nondet_monad"
  and xf' :: "'t \<Rightarrow> 'b"
  assumes pre: "ccorres_underlying sr \<Gamma> (inr_rrel r') xf' (inl_rrel arrel) axf P P' hs' a c"
  assumes hsw: "hs' \<noteq> [] \<Longrightarrow> hs' = hs"
  assumes ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  assumes post: "\<And>rv rv'. r' rv rv'
                    \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' rv')"
  assumes hoare: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>,-"
                 "exec_handlers_Hoare \<Gamma> R' (c # hs)
                    (ccHoarePost (inr_rrel r' :: ('e + 'a \<Rightarrow> 'b \<Rightarrow> bool)) xf' (\<lambda>v. Q' (theRight v))) UNIV"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) (P' \<inter> R') hs
             (a >>=E (\<lambda>rv. b rv)) (c ;; d)"
  unfolding bindE_def
  apply (rule_tac R="\<lambda>rv s. (case rv of Inl _ \<Rightarrow> True | Inr rv' \<Rightarrow> Q rv' s)"
             and R'="\<lambda>rv. {s. s \<in> (Q' (theRight rv) (xf' s) \<inter> {s'. inr_rrel r' rv (xf' s)})}"
              and E="\<lambda>rv. \<top>"
             and E'="\<lambda>rv. {s. s \<in> ({s'. inl_rrel arrel rv (axf s')}
                                    \<inter> {s'. inl_rrel arrel rv (axf s)})}"
                in ccorres_master_split [OF pre])
      apply (erule hsw)
     apply (rule ccorres_abstract[OF ceqv])
     apply (rule ccorres_gen_asm2)
     apply (clarsimp elim!: inl_inrE simp: lift_def)
     apply (erule post)
    apply (rule_tac xf'=axf in ccorres_abstract, rule ceqv_refl)
    apply (rule ccorres_gen_asm2)
    apply (clarsimp simp: lift_def throwError_def
                   elim!: inl_inrE)
    apply (rule ccorres_return_Skip'[simplified])
   apply (rule hoare_strengthen_post, rule hoare[unfolded validE_R_def validE_def])
   apply simp
  apply (simp add: ccHoarePost_def inl_rrel_def split: sum.split)
  apply (rule hoare[unfolded ccHoarePost_def])
  done

lemma ccorres_symb_exec_r_rv_abstract:
  "\<lbrakk>  \<And>s. \<Gamma>\<turnstile> (R' \<inter> {s'. R s \<and> (s, s') \<in> sr}) c ({s'. (s, s') \<in> sr} \<inter> {s. F (xf' s)});
        \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' y (y' rv');
        \<And>rv'. F rv' \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P (Q rv') hs a (y' rv');
        \<Gamma> \<turnstile>\<^bsub>/Ft\<^esub> P' c {s. \<forall>rv. F (xf' s) \<longrightarrow> s \<in> Q (xf' s)} \<rbrakk>
       \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) (P' \<inter> R') hs a (c;;y)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return,
          rule_tac r'="\<lambda>rv rv'. F rv'" and xf'=xf'
                in ccorres_split_nothrow)
       apply (rule_tac P'=R' in ccorres_from_vcg[where P=R])
       apply (clarsimp simp add: return_def Int_def conj_comms)
      apply assumption
     apply fastforce
    apply wp
   apply simp
  apply simp
  done

lemma ccorres_symb_exec_r_known_rv:
  "\<lbrakk>  \<And>s. \<Gamma>\<turnstile> (R' \<inter> {s'. R s \<and> (s, s') \<in> sr}) c ({s'. (s, s') \<in> sr} \<inter> {s. xf' s = val});
        \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' y (y' rv');
        ccorres_underlying sr \<Gamma> r xf arrel axf P Q hs a (y' val);
        \<Gamma> \<turnstile>\<^bsub>/Ft\<^esub> P' c {s. \<forall>rv. (xf' s) = val \<longrightarrow> s \<in> Q} \<rbrakk>
       \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) (P' \<inter> R') hs a (c;;y)"
  by (rule_tac F="\<lambda>rv'. rv' = val" and xf'=xf'
          in ccorres_symb_exec_r_rv_abstract,
       simp_all)

lemma ccorres_symb_exec_r_abstract_UNIV:
  "\<lbrakk>  \<And>s. \<Gamma>\<turnstile> (R' \<inter> {s'. R s \<and> (s, s') \<in> sr}) m ({s'. (s, s') \<in> sr} \<inter> {s. F (xf' s)});
        \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' y (y' rv');
        \<And>rv'. F rv' \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf P (Q rv') hs a (y' rv');
        guard_is_UNIV (\<lambda>rv rv'. F rv') xf' (\<lambda>rv. Q) \<rbrakk>
       \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) R' hs a (m;;y)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return,
          rule_tac r'="\<lambda>rv rv'. F rv'" and xf'=xf'
                in ccorres_split_nothrow_novcg)
       apply (rule_tac P'=R' in ccorres_from_vcg[where P=R])
       apply (clarsimp simp add: return_def Int_def conj_comms)
      apply assumption
     apply fastforce
    apply wp
   apply (simp add: guard_is_UNIV_def)
  apply simp
  done

lemma ccorres_symb_exec_r_known_rv_UNIV:
  "\<lbrakk>  \<And>s. \<Gamma>\<turnstile> (R' \<inter> {s'. R s \<and> (s, s') \<in> sr}) m ({s'. (s, s') \<in> sr} \<inter> {s. xf' s = val});
        \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' y (y' rv');
        ccorres_underlying sr \<Gamma> r xf arrel axf P Q hs a (y' val); guard_is_UNIV (\<lambda>rv rv'. rv' = val) xf' (\<lambda>rv rv'. Q) \<rbrakk>
       \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) R' hs a (m;;y)"
  by (rule_tac F="\<lambda>rv'. rv' = val" and xf'=xf'
          in ccorres_symb_exec_r_abstract_UNIV,
       simp_all)

lemma ccorres_seq_cond_raise:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (Cond S x y ;; c)
    = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (Cond S (x ;; c) (y ;; c))"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.intros)
  done

lemma ccorres_seq_cond_empty:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (Cond {} x y ;; c) = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (y ;; c)"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.intros)
  done

lemma ccorres_seq_cond_univ:
  "ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (Cond UNIV x y ;; c) = ccorres_underlying sr \<Gamma> r xf arrel axf G G' hs a (x ;; c)"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.intros)
  done

lemma ccorres_cond_true:
  "ccorres_underlying sr \<Gamma> r xf arrel axf R R' hs a c \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf R (R' \<inter> P) hs a (Cond P c d)"
  apply (rule ccorres_guard_imp2)
  apply (erule ccorres_cond_weak)
   apply (rule ccorres_gen_asm2 [where P = False])
   apply simp
  apply simp
  done

lemma ccorres_cond_false:
  "ccorres_underlying sr \<Gamma> r xf arrel axf R R' hs a d
     \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf R (R' \<inter> - P) hs a (Cond P c d)"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_cond_weak)
   apply (rule ccorres_gen_asm2 [where P = False])
    apply simp
   apply simp
  apply simp
  done

lemma ccorres_cond_false_seq:
  "ccorres_underlying sr \<Gamma> r xf arrel axf R R' hs a (d ;; e)
     \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf R (R' \<inter> - P) hs a (Cond P c d ;; e)"
  apply (simp add: ccorres_seq_cond_raise)
  apply (erule ccorres_cond_false)
  done

lemma ccorres_cond_true_seq:
  "ccorres_underlying sr \<Gamma> r xf arrel axf R R' hs a (c ;; e)
     \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf R (R' \<inter> P) hs a (Cond P c d ;; e)"
  apply (simp add: ccorres_seq_cond_raise)
  apply (erule ccorres_cond_true)
  done

lemma ccorres_Catch:
  "ccorres_underlying sr \<Gamma> r xf r xf P P' (d#hs) a c \<Longrightarrow>
  ccorres_underlying sr \<Gamma> r xf r xf P P' hs a (Catch c d)"
  apply (clarsimp simp: ccorres_underlying_def split_def)
  apply (drule (1) bspec)
  apply clarsimp
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (erule_tac x=na in allE)
    apply (erule_tac x=ta in allE)
    apply (erule impE)
     apply (erule exec_elim_cases, simp_all)[1]
     apply (erule EHAbrupt)
     apply (erule EHAbrupt)
     apply simp
    apply (clarsimp split: xstate.splits)
    apply (simp add: unif_rrel_def)
    apply fastforce
   apply clarsimp
   apply (erule exec_elim_cases, simp_all)[1]
    apply (erule_tac x="length hs" in allE)
    apply (erule_tac x=ta in allE)
    apply (erule impE)
     apply (erule EHAbrupt)
     apply (erule (1) EHOther)
    apply (clarsimp simp: unif_rrel_def split: xstate.splits)
   apply (erule_tac x="length (d#hs)" in allE)
   apply (erule_tac x=ta in allE)
   apply (erule impE)
    apply (erule (1) EHOther)
   apply (clarsimp simp: unif_rrel_def split: xstate.splits)
  apply clarsimp
  done

lemma ccorres_cond_seq:
  "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (Cond Q (c;;d) (c';;d)) \<Longrightarrow>
   ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H (Cond Q c c';; d)"
  apply (erule ccorres_semantic_equivD2)
  apply (simp only: semantic_equiv_def)
  apply (clarsimp simp: ceqv_def)
  apply (rule iffI)
   apply (erule exec_elim_cases, simp_all)[1]
   apply (erule exec_elim_cases, simp_all)[1]
    apply (erule exec.CondTrue)
    apply (erule (1) exec.Seq)
   apply (erule exec.CondFalse)
   apply (erule (1) exec.Seq)
  apply (erule exec_elim_cases, simp_all)[1]
   apply (erule exec_elim_cases, simp_all)[1]
   apply (rule exec.Seq)
    apply (erule exec.CondTrue)
    apply assumption
   apply assumption
  apply (erule exec_elim_cases, simp_all)[1]
  apply (rule exec.Seq)
   apply (erule exec.CondFalse)
   apply assumption
  apply assumption
  done

lemma ccorres_assume_pre:
  assumes "\<And>s. P s \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf r' xf' (P and (\<lambda>s'. s' = s)) P' hs H C"
  shows "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H C"
  apply (clarsimp simp: ccorres_underlying_def)
  apply (frule assms)
  apply (simp add: ccorres_underlying_def)
  apply blast
  done

lemma ccorres_name_pre:
  "(\<And>s. P s \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf r' xf' (\<lambda>s'. s' = s) P' hs H C)
    \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf r' xf'  P P' hs H C"
   apply (rule ccorres_assume_pre)
   apply (rule ccorres_guard_imp)
     apply fastforce
    apply simp
   apply simp
   done

(* using subst bind_assoc[symmetric] works, but causes flex-flex pairs in ccorres proofs
   using simp won't create flex-flex pairs, but will rearrange everything *)
lemma ccorres_lhs_assoc:
  assumes cc: "ccorres_underlying sr E r xf arrel axf G G' hs (m >>= f >>= g) c"
  shows "ccorres_underlying sr E r xf arrel axf G G' hs (do x \<leftarrow> m; f x >>= g od) c"
  using cc by (simp add: bind_assoc)

(* FIXME: move *)
lemma ccorres_grab_asm:
  "(Q \<Longrightarrow> ccorres_underlying sr G rr xf ar ax P P' hs f g) \<Longrightarrow>
   ccorres_underlying sr G rr xf ar ax (P and K Q) P' hs f g"
  by (fastforce simp: ccorres_underlying_def)

end
