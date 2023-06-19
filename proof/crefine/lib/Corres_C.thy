(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Corres_C
imports
  "CLib.CCorresLemmas"
  SR_lemmas_C
begin

abbreviation
  "return_C \<equiv> CLanguage.creturn global_exn_var_'_update"
lemmas return_C_def = creturn_def

abbreviation
  "return_void_C \<equiv> CLanguage.creturn_void global_exn_var_'_update"
lemmas return_void_C_def = creturn_void_def

abbreviation
  "break_C \<equiv> CLanguage.cbreak global_exn_var_'_update"
lemmas breakk_C_def = cbreak_def

abbreviation
  "catchbrk_C \<equiv> CLanguage.ccatchbrk global_exn_var_'"
lemmas catchbrk_C_def = ccatchbrk_def

(* This is to avoid typing this all the time \<dots> *)
abbreviation (in kernel)
  "modifies_spec f \<equiv> \<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call f {t. t may_not_modify_globals s}"

section "Error monad"

(* Dealing with THROW in a nice fashion --- it is always going to be catching break or skip at the end of the function.
   In retrospect, if ccatchbrk is always if ... then SKIP else THROW we are OK without the globals_update thing *)

definition
  wfhandlers :: "rf_com list \<Rightarrow> bool"
where
  "wfhandlers hs \<equiv> \<forall>\<Gamma> s t n. global_exn_var_' s = Return
                      \<and> \<Gamma> \<turnstile>\<^sub>h \<langle>hs, s\<rangle> \<Rightarrow> (n, t) \<longrightarrow> t = Normal s"

lemma wfhandlers_ccatchbrk:
  "wfhandlers (catchbrk_C # hs) = wfhandlers hs"
  unfolding wfhandlers_def ccatchbrk_def
  apply rule
   apply (intro allI impI)
   apply (drule_tac x = \<Gamma> in spec)
   apply ((drule spec)+, erule mp)
   apply simp
   apply (rule EHAbrupt)
    apply rule
     apply simp
    apply rule
   apply fastforce
  apply (intro allI impI)
  apply (drule_tac x = \<Gamma> in spec)
  apply ((drule spec)+, erule mp)
  apply simp
  apply (erule conjE)
  apply (erule exec_handlers.cases)
     apply (fastforce elim: exec_Normal_elim_cases)+
     done

lemma wfhandlers_skip:
  "wfhandlers (SKIP # hs)"
  unfolding wfhandlers_def
  apply (intro allI impI)
  apply (erule conjE)
  apply (erule exec_handlers.cases)
    apply (auto elim: exec_Normal_elim_cases)
    done

lemmas wfhandlers_simps [simp] = wfhandlers_skip wfhandlers_ccatchbrk

lemma wfhandlersD:
  "\<lbrakk>wfhandlers hs; \<Gamma> \<turnstile>\<^sub>h \<langle>hs, s\<rangle> \<Rightarrow> (n, t); global_exn_var_' s = Return\<rbrakk> \<Longrightarrow> t = Normal s"
  unfolding wfhandlers_def by auto

record 'b exxf =
  exflag :: machine_word
  exstate :: errtype
  exvalue :: 'b

definition
  liftxf :: "(cstate \<Rightarrow> errtype) \<Rightarrow> ('a \<Rightarrow> machine_word) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (cstate \<Rightarrow> 'a) \<Rightarrow> cstate \<Rightarrow> 'b exxf"
  where
  "liftxf et ef vf xf \<equiv> \<lambda>s. \<lparr> exflag = ef (xf s), exstate = et s, exvalue = vf (xf s) \<rparr>"

lemma exflag_liftxf [simp]:
  "exflag (liftxf es sf vf xf s) = sf (xf s)"
  unfolding liftxf_def by simp

lemma exstate_liftxf [simp]:
  "exstate (liftxf es sf vf xf s) = es s"
  unfolding liftxf_def by simp

lemma exvalue_liftxf [simp]:
  "exvalue (liftxf es sf vf xf s) = vf (xf s)"
  unfolding liftxf_def by simp


(* This is more or less ccorres specific, so it goes here *)

primrec
  crel_sum_comb :: "('a \<Rightarrow> machine_word \<Rightarrow> errtype \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'b \<Rightarrow> bool)
                        \<Rightarrow> ('a + 'c \<Rightarrow> 'b exxf \<Rightarrow> bool)" (infixl "\<currency>" 95)
where
  "(f \<currency> g) (Inr x) y = (exflag y = scast EXCEPTION_NONE \<and> g x (exvalue y))"
| "(f \<currency> g) (Inl x) y = (exflag y \<noteq> scast EXCEPTION_NONE \<and> f x (exflag y) (exstate y))"

lemma ccorres_split_nothrowE:
  fixes R' :: "cstate set"
  assumes ac: "ccorres_underlying sr \<Gamma>
                    (f' \<currency> r') (liftxf es ef' vf' xf')
                    (f' \<currency> r') (liftxf es ef' vf' xf')
                    P P' hs a c"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. \<lbrakk> r' rv (vf' rv'); ef' rv' = scast EXCEPTION_NONE \<rbrakk>
            \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' rv')"
  and    err: "\<And>err rv' err'. \<lbrakk>ef' rv' \<noteq> scast EXCEPTION_NONE; f' err (ef' rv') err' \<rbrakk>
            \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (QE err) (Q'' err rv' err') hs
                     (throwError err) (d' rv')"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>,\<lbrace>QE\<rbrace>"
  and valid': "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> R' c ({s. (ef' (xf' s) = scast EXCEPTION_NONE \<longrightarrow> (\<forall>rv. r' rv (vf' (xf' s)) \<longrightarrow> s \<in> Q' rv (xf' s))) \<and>
  (ef' (xf' s) \<noteq> scast EXCEPTION_NONE \<longrightarrow> (\<forall>err. f' err (ef' (xf' s)) (es s) \<longrightarrow> s \<in> Q'' err (xf' s) (es s)))})" (is "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> R' c {s. ?Q'' s}")
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) (P' \<inter> R') hs
               (a >>=E (\<lambda>rv. b rv)) (c ;; d)"
  unfolding bindE_def
  apply (rule_tac R="case_sum QE Q"
             and R'="\<lambda>rv. {s. s \<in> case_sum QE' QR' rv (xf' s)}" for QE' QR'
           in ccorres_master_split_hs)
      apply (rule ac)
     apply (rule ccorres_abstract[OF ceqv])
     apply (case_tac rv, simp_all add: lift_def)
      apply (rule ccorres_abstract[where xf'=es, OF ceqv_refl])
      apply (rule ccorres_gen_asm2)
      apply (rule ccorres_gen_asm2)
      apply (rule_tac err'=rv'a in err)
      apply assumption+
     apply (rule ccorres_gen_asm2)
     apply (rule ccorres_gen_asm2)
     apply (erule(1) bd)
    apply (rule ccorres_empty[where P=\<top>])
   apply (rule hoare_strengthen_post, rule valid[unfolded validE_def])
   apply (simp split: sum.split_asm)
  apply (rule exec_handlers_Hoare_Post,
         rule exec_handlers_Hoare_from_vcg_nofail[OF valid', where A="{}"])
  apply (auto simp: ccHoarePost_def split: sum.split)
  done

lemma ccorres_split_nothrow_novcgE:
  fixes R' :: "cstate set"
  assumes ac: "ccorres_underlying sr \<Gamma>
                   (f' \<currency> r') (liftxf es ef' vf' xf')
                   (f' \<currency> r') (liftxf es ef' vf' xf')
                   P P' [] a c"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. \<lbrakk> r' rv (vf' rv'); ef' rv' = scast EXCEPTION_NONE \<rbrakk>
                \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' rv')"
  and    err: "\<And>err rv' err'. \<lbrakk> ef' rv' \<noteq> scast EXCEPTION_NONE; f' err (ef' rv') err' \<rbrakk>
                \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf
                     (QE err) (Q'' err rv' err') hs (throwError err) (d' rv')"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>,\<lbrace>QE\<rbrace>"
  and  novcg: "guard_is_UNIV (\<lambda>rv rv'. r' rv (vf' rv'))
                                 xf' (\<lambda>rv rv'. {s. ef' rv' = scast EXCEPTION_NONE \<longrightarrow> s \<in> Q' rv rv'})"
  \<comment> \<open>hack\<close>
  and  novcg_err: "\<And>err. guard_is_UNIV (\<lambda>rv. f' err (ef' rv)) es
                              (\<lambda>rv rv'. {s. ef' (xf' s) \<noteq> scast EXCEPTION_NONE \<longrightarrow> s \<in> Q'' err rv rv'})"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) P' hs (a >>=E (\<lambda>rv. b rv)) (c ;; d)"
  unfolding bindE_def
  apply (rule_tac R="case_sum QE Q"
             and R'="\<lambda>rv. {s. s \<in> case_sum QE' QR' rv (xf' s)}" for QE' QR'
           in ccorres_master_split_nohs_UNIV)
     apply (rule ac)
    apply (rule ccorres_abstract[OF ceqv])
    apply (case_tac rv, simp_all add: lift_def)
     apply (rule ccorres_abstract[where xf'=es, OF ceqv_refl])
     apply (rule ccorres_gen_asm2)
     apply (rule ccorres_gen_asm2)
     apply (rule_tac err'=rv'a in err)
     apply assumption+
    apply (rule ccorres_gen_asm2)
    apply (rule ccorres_gen_asm2)
    apply (erule(1) bd)
   apply (rule hoare_strengthen_post, rule valid[unfolded validE_def])
   apply (simp split: sum.split_asm)
  apply (insert novcg novcg_err)
  apply (clarsimp simp: guard_is_UNIV_def split: sum.split)
  done

\<comment> \<open>Unit would be more appropriate, but the record package will rewrite xfdc to ().
   This can happen even when protected by a cong rule, as seen in the following example.
definition
  "xfdc \<equiv> \<lambda>(t :: cstate). ()"
lemma
  "\<And>x b. \<lbrakk>snd x = b\<rbrakk>
   \<Longrightarrow> ccorres_underlying rf_sr \<Gamma>
         (\<lambda>a b. dc a b) (\<lambda>a. xfdc a) dc xfdc
         \<top> UNIV [SKIP] a c"
  supply ccorres_weak_cong[cong]
  apply clarify
  oops\<close>
definition
  "xfdc (t :: cstate) \<equiv> (0 :: nat)"

lemma xfdc_equal[simp]:
  "xfdc t = xfdc s"
  unfolding xfdc_def by simp

lemmas ccorres_split_nothrow_novcg_dc
    = ccorres_split_nothrow_novcg[where r'=dc and xf'=xfdc, OF _ ceqv_refl]

abbreviation
  "exfdc \<equiv> liftxf undefined (\<lambda>_. scast EXCEPTION_NONE) id xfdc"

lemma ccorres_return_C':
  assumes xfc: "\<And>s. (xf (global_exn_var_'_update (\<lambda>_. Return) (xfu (\<lambda>_. v s) s))) = v s"
  and     wfh: "wfhandlers hs"
  and     srv: "\<And>s s'. (s, s') \<in> sr \<Longrightarrow>
  (s, global_exn_var_'_update (\<lambda>_. Return) (xfu (\<lambda>_. v s') s')) \<in> sr"
  shows "ccorres_underlying sr \<Gamma> r rvxf arrel xf \<top> {s. arrel rv (v s)} hs
               (return rv) (return_C xfu v)"
  using wfh
  unfolding creturn_def
  apply -
  apply (rule ccorresI')
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (clarsimp elim!: exec_Normal_elim_cases)
    apply (drule (1) wfhandlersD)
     apply simp
    apply (frule exec_handlers_less2, clarsimp)
    apply (clarsimp simp: return_def unif_rrel_def xfc)
    apply (auto elim!: srv)[1]
   apply (clarsimp elim!: exec_Normal_elim_cases)
  apply simp
  done

lemma ccorres_return_CE':
  assumes xfc: "\<And>s. xf (global_exn_var_'_update (\<lambda>_. Return)
                       (xfu (\<lambda>_. v s) s)) = v s"
  and     wfh: "wfhandlers hs"
  and     srv: "\<And>s s'. (s, s') \<in> sr \<Longrightarrow> (s, global_exn_var_'_update (\<lambda>_. Return) (xfu (\<lambda>_. v s') s')) \<in> sr"
  shows   "ccorres_underlying sr \<Gamma> rvr rvxf (f \<currency> r) (liftxf es sf vf xf)
    \<top> {s. sf (v s) = scast EXCEPTION_NONE \<and> r rv (vf (v s))} hs
    (returnOk rv) (return_C xfu v)"
  using wfh
  unfolding creturn_def
  apply -
  apply (rule ccorresI')
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (clarsimp elim!: exec_Normal_elim_cases)
    apply (drule (1) wfhandlersD)
     apply simp
    apply (simp add: returnOk_def return_def)
    apply (drule exec_handlers_less2, clarsimp+)
    apply (auto simp: unif_rrel_def xfc elim!: srv)[1]
   apply (clarsimp elim!: exec_Normal_elim_cases)
  apply simp
  done

lemma ccorres_return_C_errorE':
  assumes xfc: "\<And>s. xf (global_exn_var_'_update (\<lambda>_. Return) (xfu (\<lambda>_. v s) s)) = v s"
  and     esc: "\<And>s. es (global_exn_var_'_update (\<lambda>_. Return) (xfu (\<lambda>_. v s) s)) = es s"
  and     wfh: "wfhandlers hs"
  and     srv: "\<And>s s'. (s, s') \<in> sr \<Longrightarrow> (s, global_exn_var_'_update (\<lambda>_. Return) (xfu (\<lambda>_. v s') s')) \<in> sr"
  shows   "ccorres_underlying sr \<Gamma> rvr rvxf (f \<currency> r) (liftxf es sf vf xf)
    \<top> {s. sf (v s) \<noteq> scast EXCEPTION_NONE \<and> f rv (sf (v s)) (es s)} hs
    (throwError rv) (return_C xfu v)"
  using wfh
  unfolding creturn_def
  apply -
  apply (rule ccorresI')
  apply (erule exec_handlers.cases)
    apply clarsimp
    apply (clarsimp elim!: exec_Normal_elim_cases)
    apply (drule (1) wfhandlersD)
     apply simp
    apply (simp add: throwError_def return_def)
    apply (drule exec_handlers_less2, clarsimp+)
    apply (auto simp: unif_rrel_def xfc esc elim!: srv)[1]
   apply (clarsimp elim!: exec_Normal_elim_cases)
  apply simp
  done

context kernel
begin


abbreviation
  "ccorres r xf \<equiv> ccorres_underlying rf_sr \<Gamma> r xf r xf"

lemma ccorres_basic_srnoop:
  assumes asm: "ccorres_underlying rf_sr Gamm r xf arrel axf G G' hs a c"
  and   gsr: "\<And>s'. globals (g s') = globals s'"
  and   gG: "\<And>s'. s' \<in> G' \<Longrightarrow> g s' \<in> G'"
  shows "ccorres_underlying rf_sr Gamm r xf arrel axf G G' hs a (Basic g ;; c)"
  using asm unfolding rf_sr_def
  apply (rule ccorres_basic_srnoop)
   apply (simp add: gsr)
  apply (erule gG)
  done

lemma ccorres_basic_srnoop2:
  assumes gsr: "\<And>s'. globals (g s') = globals s'"
  assumes asm: "ccorres_underlying rf_sr Gamm r xf arrel axf G G' hs a c"
  shows "ccorres_underlying rf_sr Gamm r xf arrel axf G {s. g s \<in> G'} hs a (Basic g ;; c)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_r)
     apply (rule asm)
    apply vcg
   apply (rule conseqPre, vcg, clarsimp simp: rf_sr_def gsr)
  apply clarsimp
  done


(* The naming convention here is that xf', xfr, and xfru are the terms we instantiate *)
lemma ccorres_call:
  assumes  cul: "ccorres_underlying rf_sr \<Gamma> r xf'' r xf'' A C' [] a (Call f)"
  and      ggl: "\<And>x y s. globals (g x y s) = globals s"
  and      xfg: "\<And>a s t. (xf' (g a t (s\<lparr>globals := globals t\<rparr>))) = xf'' t"
  and      igl: "\<And>s. globals (i s) = globals s"
  shows "ccorres_underlying rf_sr \<Gamma> r xf' arrel axf
          A {s. i s \<in> C'} hs a (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>x y. Basic (g x y)))"
  using cul
  unfolding rf_sr_def
  apply -
  apply (rule ccorres_call)
     apply (erule ccorres_guard_imp)
      apply simp
     apply clarsimp
    apply (simp add: ggl)
   apply (simp add: xfg)
  apply (clarsimp simp: igl)
  done

lemma ccorres_callE:
  "\<lbrakk> ccorres_underlying rf_sr \<Gamma> r (liftxf es sf vf xf'')
                               r (liftxf es sf vf xf'') A C' [] a (Call f);
     \<And>x y s. globals (g x y s) = globals s;
     \<And>a s t. es (g a t (s\<lparr>globals := globals t\<rparr>)) = es t;
     \<And>a s t. xf' (g a t (s\<lparr>globals := globals t\<rparr>)) = xf'' t;
     \<And>s. globals (i s) = globals s
  \<rbrakk>
  \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> r (liftxf es sf vf xf') arrel axf A {s. i s \<in> C'} hs a
        (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>x y. Basic (g x y)))"
  apply (erule ccorres_call)
    apply assumption
   apply (simp add: liftxf_def)
  apply assumption
  done

lemma ccorres_call_record:
  assumes  cul: "ccorres_underlying rf_sr \<Gamma> r xf'' r xf'' A C' [] a (Call f)"
  and      ggl: "\<And>f s. globals (xfu' f s) = globals s"
  and    xfxfu: "\<And>v s. xf' (xfu' (\<lambda>_. v) s) = v"
  and  xfrxfru: "\<And>v s. xfr (xfru (\<lambda>_. v) s) = v"
  and      igl: "\<And>s. globals (i s) = globals s"
  shows "ccorres_underlying rf_sr \<Gamma> r (xfr \<circ> xf') arrel axf
           A {s. i s \<in> C'} hs a (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>)
        (\<lambda>_ t. Basic (xfu' (\<lambda>_. xfru (\<lambda>_. xf'' t) oldv))))"
  apply (rule ccorres_call)
     apply (rule cul)
    apply (rule ggl)
   apply (simp add: xfrxfru xfxfu)
  apply (rule igl)
  done

lemmas ccorres_split_nothrow_call = ccorres_split_nothrow [OF ccorres_call]
lemmas ccorres_split_nothrow_callE = ccorres_split_nothrowE [OF ccorres_callE]

lemma ccorres_split_nothrow_call_novcg:
  assumes ac: "ccorres r' xf'' P P' [] a (Call f)"
  and     gg: "\<And>x y s. globals (g x y s) = globals s"
  and   xfxf: "\<And>a s t. xf' (g a t (s\<lparr>globals := globals t\<rparr>)) = xf'' t"
  and     gi: "\<And>s. globals (i s) = globals s"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. r' rv rv' \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' rv')"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>"
  shows "ccorres_underlying rf_sr \<Gamma> r xf arrel axf (P and R) ({s. i s \<in> P'} \<inter>
             {s'. (\<forall>t rv. r' rv (xf'' t) \<longrightarrow> g s' t (s'\<lparr>globals := globals t\<rparr>) \<in> Q' rv (xf'' t))})
            hs (a >>= (\<lambda>rv. b rv))
         (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>x y. Basic (g x y)) ;; d)" (is "ccorres_underlying rf_sr \<Gamma> r xf arrel axf ?P (?Q1 \<inter> ?Q2) hs ?A ?B")
  apply (rule ccorres_master_split_nohs)
     apply (rule ccorres_call [OF ac])
       apply (rule gg)
      apply (rule xfxf)
     apply (rule gi)
    apply (rule ccorres_abstract[OF ceqv])
    apply (rule ccorres_gen_asm2)
    apply (erule bd)
   apply (simp add: valid)
  apply (rule exec_handlers_Hoare_call_Basic)
   apply (clarsimp simp: ccHoarePost_def xfxf)
  apply simp
  done

definition
  errstate :: "cstate \<Rightarrow> errtype"
where
  "errstate s \<equiv> \<lparr> errfault = seL4_Fault_lift (current_fault_' (globals s)),
                  errlookup_fault = lookup_fault_lift (current_lookup_fault_' (globals s)),
                  errsyscall = current_syscall_error_' (globals s) \<rparr>"

lemma errlookup_fault_errstate [simp]:
  "errlookup_fault (errstate s) = lookup_fault_lift (current_lookup_fault_' (globals s))"
  unfolding errstate_def
  by simp

lemma errfault_errstate [simp]:
  "errfault (errstate s) = seL4_Fault_lift (current_fault_' (globals s))"
  unfolding errstate_def
  by simp

lemma errsyscall_errstate [simp]:
  "errsyscall (errstate s) = (current_syscall_error_' (globals s))"
  unfolding errstate_def
  by simp

lemma errstate_state_update [simp]:
  assumes f: "\<And>s. current_fault_' (globals (g s)) = current_fault_' (globals s)"
  and    lf: "\<And>s. current_lookup_fault_' (globals (g s)) = current_lookup_fault_' (globals s)"
  and    se: "\<And>s. current_syscall_error_' (globals (g s)) = current_syscall_error_' (globals s)"
  shows  "errstate (g s) = errstate s"
  by (simp add: f lf se errstate_def)

lemma ccorres_split_nothrow_call_novcgE:
  assumes ac: "ccorres (f' \<currency> r') (liftxf errstate ef' vf' xf'') P P' [] a (Call f)"
  and     gg: "\<And>x y s. globals (g x y s) = globals s"
  and   xfxf: "\<And>a s t. xf' (g a t (s\<lparr>globals := globals t\<rparr>)) = xf'' t"
  and     gi: "\<And>s. globals (i s) = globals s"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. \<lbrakk>r' rv (vf' rv'); ef' rv' = scast EXCEPTION_NONE\<rbrakk>
                  \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> (fl \<currency> r) xf arrel axf
                           (Q rv) (Q' rv rv') hs (b rv) (d' rv')"
  and    err: "\<And>err rv' err'. \<lbrakk>ef' rv' \<noteq> scast EXCEPTION_NONE; f' err (ef' rv') err'\<rbrakk>
                  \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> (fl \<currency> r) xf arrel axf
                           (QE err) (Q'' err rv' err') hs (throwError err) (d' rv')"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>, \<lbrace>QE\<rbrace>"
  shows "ccorres_underlying rf_sr \<Gamma> (fl \<currency> r) xf arrel axf (P and R) ({s. i s \<in> P'} \<inter>
  {s. \<forall>t.  (ef' (xf'' t) = scast EXCEPTION_NONE \<longrightarrow> (\<forall>rv. r' rv (vf' (xf'' t)) \<longrightarrow> g s t (s\<lparr>globals := globals t\<rparr>) \<in> Q' rv (xf'' t))) \<and>
            (ef' (xf'' t) \<noteq> scast EXCEPTION_NONE \<longrightarrow>
              (\<forall>err. f' err (ef' (xf'' t)) (errstate t) \<longrightarrow> g s t (s\<lparr>globals := globals t\<rparr>) \<in> Q'' err (xf'' t) (errstate t)))}
  ) hs (a >>=E b) (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>x y. Basic (g x y));;
 d)" (is "ccorres_underlying rf_sr \<Gamma> ?r ?xf arrel axf ?P (?Q1 \<inter> ?Q2) hs ?A ?B")
  unfolding bindE_def
  apply (rule_tac R="case_sum QE Q"
             and R'="\<lambda>rv. {s. s \<in> case_sum QE' QR' rv (xf' s)}" for QE' QR'
               in ccorres_master_split_nohs)
     apply (rule ccorres_callE [OF ac])
        apply (rule gg)
       apply (rule errstate_state_update)
         apply (simp add: gg)+
      apply (rule xfxf)
     apply (rule gi)
    apply (rule ccorres_abstract[OF ceqv])
    apply (case_tac rv, simp_all add: lift_def)
     apply (rule_tac xf'=errstate in ccorres_abstract[OF ceqv_refl])
     apply (rule ccorres_gen_asm2)
     apply (rule ccorres_gen_asm2)
     apply (erule_tac err'1=rv'a in err, assumption)
    apply (rule ccorres_gen_asm2)
    apply (rule ccorres_gen_asm2)
    apply (erule(1) bd)
   apply (rule hoare_strengthen_post)
    apply (rule valid [unfolded validE_def])
   apply (simp split: sum.split_asm)
  apply (rule exec_handlers_Hoare_call_Basic)
   apply (clarsimp simp: ccHoarePost_def xfxf gg errstate_def
                  split: sum.split)
  apply simp
  done

lemma ccorres_split_nothrow_call_record:
  assumes ac: "ccorres r' xf'' P P' [] a (Call f)"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. r' rv rv' \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' (xfru (\<lambda>_. rv') oldv))"
  and      ggl: "\<And>f s. globals (xfu' f s) = globals s"
  and    xfxfu: "\<And>v s. xf' (xfu' (\<lambda>_. v) s) = v"
  and  xfrxfru: "\<And>v s. xfr (xfru (\<lambda>_. v) s) = v"
  and      igl: "\<And>s. globals (i s) = globals s"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>"
  and  valid': "\<Gamma> \<turnstile>\<^bsub>/F\<^esub> R' call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>_ t. Basic (xfu' (\<lambda>_. xfru (\<lambda>_. xf'' t) oldv)))
       {s. xf' s = xfru (\<lambda>_. (xfr \<circ> xf') s) oldv \<and> (\<forall>rv. r' rv ((xfr \<circ> xf') s) \<longrightarrow> s \<in> Q' rv ((xfr \<circ> xf') s))}"
  shows "ccorres_underlying rf_sr \<Gamma> r xf arrel axf (P and R) ({s. i s \<in> P'} \<inter> R') hs (a >>= (\<lambda>rv. b rv)) (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>)
                (\<lambda>_ t. Basic (xfu' (\<lambda>_. xfru (\<lambda>_. xf'' t) oldv))) ;; d)"
  using ac ggl xfxfu xfrxfru igl ceqv
  apply (rule  ccorres_split_nothrow_record [OF ccorres_call_record])
    apply (erule bd)
   apply (rule valid)
  apply (rule valid')
  done

lemma ccorres_split_nothrow_call_record_novcg:
  assumes ac: "ccorres r' xf'' P P' [] a (Call f)"
  and   ceqv: "\<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv')"
  and     bd: "\<And>rv rv'. r' rv rv' \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' (xfru (\<lambda>_. rv') oldv))"
  and      ggl: "\<And>f s. globals (xfu' f s) = globals s"
  and    xfxfu: "\<And>v s. xf' (xfu' (\<lambda>_. v) s) = v"
  and  xfrxfru: "\<And>v s. xfr (xfru (\<lambda>_. v) s) = v"
  and      igl: "\<And>s. globals (i s) = globals s"
  and  valid: "\<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>"
  and  novcg: "guard_is_UNIV r' (xfr \<circ> xf') Q'"
  \<comment> \<open>This might cause problems \<dots> has to be preserved across c in vcg case, but we can't do that\<close>
  and xfoldv: "\<And>s. xf' s = xfru (\<lambda>_. (xfr \<circ> xf') s) oldv"
  shows "ccorres_underlying rf_sr \<Gamma> r xf arrel axf (P and R) ({s. i s \<in> P'}) hs (a >>= (\<lambda>rv. b rv)) (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>)
                (\<lambda>_ t. Basic (xfu' (\<lambda>_. xfru (\<lambda>_. xf'' t) oldv))) ;; d)"
  using ac ggl xfxfu xfrxfru igl ceqv
  apply (rule  ccorres_split_nothrow_record_novcg [OF ccorres_call_record])
    apply (erule bd)
   apply (rule valid)
  apply (rule novcg)
  apply (rule xfoldv)
  done

lemma ccorres_return_C:
  assumes xf1: "\<And>s f. xf (global_exn_var_'_update f (xfu (\<lambda>_. v s) s)) = v s"
  and     xfu: "\<And>s f. globals (xfu f s) = globals s"
  and     wfh: "wfhandlers hs"
  shows "ccorres_underlying rf_sr \<Gamma> r rvxf arrel xf \<top> {s. arrel rv (v s)}
               hs (return rv) (return_C xfu v)"
  apply (rule ccorres_guard_imp2, rule ccorres_return_C')
     apply (simp add: xf1)
    apply (rule wfh)
   apply (simp add: xfu rf_sr_def cong: cstate_relation_only_t_hrs)
  apply simp
  done

lemma ccorres_return_CE:
  assumes xf1: "\<And>s f. xf (global_exn_var_'_update f (xfu (\<lambda>_. v s) s)) = v s"
  and     xfu: "\<And>s f. globals (xfu f s) = globals s"
  and     wfh: "wfhandlers hs"
  shows "ccorres_underlying rf_sr \<Gamma> rvr rxf (f \<currency> r) (liftxf es sf vf xf)
  \<top> {s. sf (v s) = scast EXCEPTION_NONE \<and> r rv (vf (v s))} hs
  (returnOk rv) (return_C xfu v)"
  apply (rule ccorres_guard_imp2, rule ccorres_return_CE')
     apply (simp add: xf1)
    apply (rule wfh)
   apply (simp add: xfu rf_sr_def cong: cstate_relation_only_t_hrs)
  apply simp
  done

lemma ccorres_return_C_errorE:
  assumes xfc: "\<And>s. xf (global_exn_var_'_update (\<lambda>_. Return) (xfu (\<lambda>_. v s) s)) = v s"
  and     esc: "\<And>s. es (global_exn_var_'_update (\<lambda>_. Return) (xfu (\<lambda>_. v s) s)) = es s"
  and     xfu: "\<And>s f. globals (xfu f s) = globals s"
  and     wfh: "wfhandlers hs"
  shows   "ccorres_underlying rf_sr \<Gamma> rvr rvxf (f \<currency> r) (liftxf es sf vf xf)
    \<top> {s. sf (v s) \<noteq> scast EXCEPTION_NONE \<and> f rv (sf (v s)) (es s)} hs
    (throwError rv) (return_C xfu v)"
  apply (rule ccorres_guard_imp2, rule ccorres_return_C_errorE')
      apply (rule xfc)
     apply (rule esc)
    apply (rule wfh)
   apply (simp add: xfu rf_sr_def cong: cstate_relation_only_t_hrs)
  apply simp
  done


(* Generalise *)
(* c can't fail here, so no /F *)
lemma ccorres_noop:
  assumes nop: "\<forall>s. \<Gamma> \<turnstile> {s} c {t. t may_not_modify_globals s}"
  shows "ccorres_underlying rf_sr \<Gamma> dc xf arrel axf \<top> UNIV hs (return ()) c"
  apply (rule ccorres_from_vcg, rule allI, simp add: return_def)
  apply (rule HoarePartial.conseq_exploit_pre)
  apply simp
  apply (intro allI impI)
  apply (rule HoarePartial.conseq)
     apply (rule nop)
    apply clarsimp
    apply (erule iffD1 [OF rf_sr_upd, rotated -1])
    apply (clarsimp simp: meq_def mex_def)+
  done

lemma ccorres_noop_spec:
  assumes  s: "\<forall>s. \<Gamma> \<turnstile> (P s) c (R s), (A s)"
  and    nop: "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/F\<^esub> {s} c {t. t may_not_modify_globals s}"
  shows "ccorres_underlying rf_sr \<Gamma> dc xf arrel axf \<top> {s. s \<in> P s} hs (return ()) c"
  apply (rule ccorres_from_vcg, rule allI, simp add: return_def)
  apply (rule HoarePartial.conseq_exploit_pre)
  apply simp
  apply (intro allI impI)
  apply (rule HoarePartial.conseq)
   apply (rule allI)
   apply (rule HoarePartialProps.Merge_PostConj)
      apply (rule_tac P = "{s} \<inter> P s" in conseqPre)
      apply (rule_tac x = s in spec [OF s])
       apply clarsimp
     apply (rule_tac x = s in spec [OF nop])
    apply simp
   apply clarsimp
  apply clarsimp
  apply (erule iffD2 [OF rf_sr_upd, rotated -1])
    apply (clarsimp simp: meq_def mex_def)+
  done


(* FIXME: MOVE *)
lemma ccorres_symb_exec_r2:
  assumes cul: "ccorres_underlying rf_sr \<Gamma> r xf arrel axf R Q' hs a d"
  and     ex:  "\<Gamma> \<turnstile> R' c Q'"
  and   pres:  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/F\<^esub> {s} c {t. t may_not_modify_globals s}"
  shows "ccorres_underlying rf_sr \<Gamma> r xf arrel axf R R' hs a (c ;; d)"
  apply (rule ccorres_add_return)
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_split_nothrow')
      apply (rule ccorres_noop_spec)
       apply (rule allI)
       apply (rule ex)
      apply (rule pres)
     apply simp
     apply (rule cul)
    apply wp
   apply (rule HoarePartialProps.augment_Faults [OF ex])
   apply simp
  apply simp
  done

lemma ccorres_trim_redundant_throw:
  "\<lbrakk>ccorres_underlying rf_sr \<Gamma> arrel axf arrel axf G G' (SKIP # hs) a c;
          \<And>s f. axf (global_exn_var_'_update f s) = axf s \<rbrakk>
  \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' (SKIP # hs)
          a (c;; Basic (global_exn_var_'_update (\<lambda>_. Return));; THROW)"
  apply -
  apply (rule ccorres_trim_redundant_throw')
    apply simp
   apply simp
  apply (simp add: rf_sr_upd_safe)
  done

end


lemmas in_magnitude_check' =
  in_magnitude_check [where v = "fst z" and s' = "snd z" for z, folded surjective_pairing]


(* Defined in terms of access_ti for convenience *)

lemma fd_cons_update_accessD:
  "\<lbrakk> fd_cons_update_access d n; length bs = n \<rbrakk> \<Longrightarrow> field_update d (field_access d v bs) v = v"
  unfolding fd_cons_update_access_def by simp

lemma fd_cons_access_updateD:
  "\<lbrakk> fd_cons_access_update d n; length bs = n; length bs' = n\<rbrakk> \<Longrightarrow> field_access d (field_update d bs v) bs' = field_access d (field_update d bs v') bs'"
  unfolding fd_cons_access_update_def by clarsimp

context kernel
begin

(* Tests *)

lemma cte_C_cap_C_tcb_C':
  fixes val :: "cap_C" and ptr :: "cte_C ptr"
  assumes cl: "clift hp ptr = Some z"
  shows "(clift (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>[''cap_C''])) val) hp)) =
  (clift hp :: tcb_C typ_heap)"
  using cl
  by (simp add: typ_heap_simps)

lemma cte_C_cap_C_update:
  fixes val :: "cap_C" and ptr :: "cte_C ptr"
  assumes  cl: "clift hp ptr = Some z"
  shows "(clift (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>[''cap_C''])) val) hp)) =
  clift hp(ptr \<mapsto> cte_C.cap_C_update (\<lambda>_. val) z)"
  using cl
  by (simp add: clift_field_update)

abbreviation
  "modifies_heap_spec f \<equiv> \<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call f {t. t may_only_modify_globals s in [t_hrs]}"

(* Used for bitfield lemmas.  Note that this doesn't follow the usual schematic merging: we generally need concrete G and G' *)
lemma ccorres_from_spec_modifies_heap:
  assumes spec: "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. P s\<rbrace> Call f {t. Q s t}"
  and      mod: "modifies_heap_spec f"
  and      xfg: "\<And>f s. xf (globals_update f s) = xf s"
  and    Pimp: "\<And>s s'. \<lbrakk> G s; s' \<in> G'; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> P s'"
  and     rl: "\<And>s s' t'. \<lbrakk>G s; s' \<in> G'; (s, s') \<in> rf_sr; Q s' t'\<rbrakk>
            \<Longrightarrow> \<exists>(rv, t) \<in> fst (a s).
                  (t, t'\<lparr>globals := globals s'\<lparr>t_hrs_' := t_hrs_' (globals t')\<rparr>\<rparr>) \<in> rf_sr
                       \<and> r rv (xf t')"
  shows "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' [] a (Call f)"
  apply (rule ccorres_Call_call_for_vcg)
   apply (rule ccorres_from_vcg)
   apply (rule allI, rule conseqPre)
   apply (rule HoarePartial.ProcModifyReturnNoAbr
                    [where return' = "\<lambda>s t. t\<lparr> globals := globals s\<lparr>t_hrs_' := t_hrs_' (globals t) \<rparr>\<rparr>"])
     apply (rule HoarePartial.ProcSpecNoAbrupt [OF _ _ spec])
      apply (rule subset_refl)
     apply vcg
    prefer 2
    apply (rule mod)
   apply (clarsimp simp: mex_def meq_def)
  apply (clarsimp simp: split_beta Pimp)
  apply (subst bex_cong [OF refl])
   apply (rule arg_cong2 [where f = "(\<and>)"])
  apply (rule_tac y = "t\<lparr>globals := globals x\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>" in rf_sr_upd, simp_all)
  apply (drule (3) rl)
  apply (clarsimp simp: xfg elim!: bexI [rotated])
  done

(* Used for bitfield lemmas *)
lemma ccorres_from_spec_modifies:
  assumes spec: "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. P s\<rbrace> Call f {t. Q s t}"
  and      mod: "modifies_spec f"
  and      xfg: "\<And>f s. xf (globals_update f s) = xf s"
  and    Pimp: "\<And>s s'. \<lbrakk> G s; s' \<in> G'; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> P s'"
  and     rl: "\<And>s s' t'. \<lbrakk>G s; s' \<in> G'; (s, s') \<in> rf_sr; Q s' t'\<rbrakk>
                 \<Longrightarrow> \<exists>(rv, t) \<in> fst (a s). (t, s') \<in> rf_sr \<and> r rv (xf t')"
  shows "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' [] a (Call f)"
  apply (rule ccorres_Call_call_for_vcg)
   apply (rule ccorres_from_vcg)
   apply (rule allI, rule conseqPre)
   apply (rule HoarePartial.ProcModifyReturnNoAbr
             [where return' = "\<lambda>s t. t\<lparr> globals := globals s \<rparr>"])
     apply (rule HoarePartial.ProcSpecNoAbrupt [OF _ _ spec])
      apply (rule subset_refl)
     apply vcg
    prefer 2
    apply (rule mod)
   apply (clarsimp simp: mex_def meq_def)
  apply (clarsimp simp: split_beta Pimp)
  apply (subst bex_cong [OF refl])
   apply (rule arg_cong2 [where f = "(\<and>)"])
  apply (rule_tac y = "x" in rf_sr_upd, simp_all)
  apply (drule (3) rl)
  apply (clarsimp simp: xfg elim!: bexI [rotated])
  done

lemma ccorres_trim_return:
  assumes fg: "\<And>s. xfu (\<lambda>_. axf s) s = s"
  and    xfu: "\<And>f s. axf (global_exn_var_'_update f s) = axf s"
  and     cc: "ccorres_underlying rf_sr \<Gamma> arrel axf arrel axf G G' (SKIP # hs) a c"
  shows "ccorres_underlying rf_sr \<Gamma> r xf arrel axf G G' (SKIP # hs) a (c ;; return_C xfu axf)"
  using fg unfolding creturn_def
  apply -
  apply (rule ccorres_rhs_assoc2)+
  apply (rule ccorres_trim_redundant_throw)
   apply (clarsimp split del: if_split)
   apply (rule iffD2 [OF ccorres_semantic_equiv, OF _ cc])
   apply (rule semantic_equivI)
   apply (case_tac s')
   apply (auto elim!: exec_Normal_elim_cases exec_elim_cases intro!: exec.intros)[4]
  apply (rule xfu)
  done

lemma rf_sr_globals_exn_var:
  "((s, global_exn_var_'_update f s') \<in> rf_sr)
       = ((s, s') \<in> rf_sr)"
  by (rule rf_sr_upd, simp_all)

lemma ccorres_trim_returnE:
  assumes fg: "\<And>s. xfu (\<lambda>_. axf s) s = s"
  and    xfu: "\<And>f s. axf (global_exn_var_'_update f s) = axf s"
  and     cc: "ccorres r (liftxf errstate ef vf axf)
                    G G' (SKIP # hs) a c"
  shows "ccorres_underlying rf_sr \<Gamma> rvr rvxf r (liftxf errstate ef vf axf)
                    G G' (SKIP # hs) a (c ;; return_C xfu axf)"
  unfolding creturn_def
  apply (rule ccorres_rhs_assoc2)+
  apply (rule ccorres_trim_redundant_throw')
    apply (simp add: fg)
    apply (rule iffD2 [OF ccorres_semantic_equiv, OF _ cc])
    apply (rule semantic_equivI)
    apply (case_tac s')
    apply (auto elim!: exec_Normal_elim_cases exec_elim_cases intro!: exec.intros)[4]
   apply (simp add: liftxf_def xfu)
  apply (simp add: rf_sr_globals_exn_var)
  done

lemma ccorres_sequence_while_genQ:
  fixes i :: "nat" and xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes one: "\<And>n ys. \<lbrakk> n < length xs \<rbrakk> \<Longrightarrow>
                    ccorres (\<lambda>rv rv'. r' (ys @ [rv]) rv') xf'
                            (F (n * j)) ({s. xf s = of_nat (i + n * j) \<and> r' ys (xf' s)} \<inter> Q) hs
                            (xs ! n) body"
  and      pn: "\<And>n. P n = (n < of_nat (i + length xs * j))"
  and   bodyi: "\<forall>s. xf s < of_nat (i + length xs * j)
      \<longrightarrow> \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> ({s} \<inter> Q) body {t. xf t = xf s \<and> xf_update (\<lambda>x. xf t + of_nat j) t \<in> Q}"
  and      hi: "\<And>n. Suc n < length xs \<Longrightarrow> \<lbrace> F (n * j) \<rbrace> (xs ! n) \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>"
  and     lxs: "i + length xs * j< 2 ^ len_of TYPE('c)"
  and      xf: "\<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s"
  and     xf': "\<forall>s f. xf' (xf_update f s) = (xf' s)"
  and       j: "j > 0"
  shows  "ccorres (\<lambda>rv (i', rv'). r' rv rv' \<and> i' = of_nat (i + length xs * of_nat j))
                  (\<lambda>s. (xf s, xf' s))
                  (\<lambda>s. P 0 \<longrightarrow> F 0 s) ({s. xf s = of_nat i \<and> r' [] (xf' s)} \<inter> Q) hs
                  (sequence xs)
                  (While {s. P (xf s)}
                     (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s)))"
  (is "ccorres ?r' ?xf' ?G (?G' \<inter> _) hs (sequence xs) ?body")
  apply (rule ccorres_sequence_while_genQ' [OF one pn bodyi hi lxs xf xf'])
     apply simp
    apply simp
   apply (clarsimp simp: rf_sr_def xf)
  apply (simp add: j)
  done

lemma ccorres_sequence_while_gen':
  fixes i :: "nat" and xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes one: "\<And>n ys. \<lbrakk> n < length xs \<rbrakk> \<Longrightarrow>
                    ccorres (\<lambda>rv rv'. r' (ys @ [rv]) rv') xf'
                            (F (n * j)) {s. xf s = of_nat (i + n * j) \<and> r' ys (xf' s)} hs
                            (xs ! n) body"
  and      pn: "\<And>n. P n = (n < of_nat (i + length xs * j))"
  and   bodyi: "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} body {t. xf t = xf s}"
  and      hi: "\<And>n. Suc n < length xs \<Longrightarrow> \<lbrace> F (n * j) \<rbrace> (xs ! n) \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>"
  and     lxs: "i + length xs * j< 2 ^ len_of TYPE('c)"
  and      xf: "\<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s"
  and     xf': "\<forall>s f. xf' (xf_update f s) = (xf' s)"
  and       j: "j > 0"
  shows  "ccorres (\<lambda>rv (i', rv'). r' rv rv' \<and> i' = of_nat (i + length xs * of_nat j))
                  (\<lambda>s. (xf s, xf' s))
                  (F 0) ({s. xf s = of_nat i \<and> r' [] (xf' s)}) hs
                  (sequence xs)
                  (While {s. P (xf s)}
                     (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s)))"
  (is "ccorres ?r' ?xf' ?G ?G' hs (sequence xs) ?body")
  using assms
  apply -
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_sequence_while_genQ [where Q=UNIV])
  apply (assumption|simp)+
  done

lemma ccorres_sequence_x_while_genQ':
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  shows
  "\<lbrakk>\<And>n. n < length xs \<Longrightarrow> ccorres dc xfdc (F (n * j)) ({s. xf s = of_nat (i + n * j)} \<inter> Q) hs (xs ! n) body;
    \<And>n. P n = (n < of_nat (i + length xs * j));
    \<forall>s. xf s < of_nat (i + length xs * j)
        \<longrightarrow> \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> ({s} \<inter> Q) body {t. xf t = xf s \<and> xf_update (\<lambda>x. xf t + of_nat j) t \<in> Q};
    \<And>n. Suc n < length xs \<Longrightarrow> \<lbrace>F (n * j)\<rbrace> xs ! n \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>; i + length xs * j < 2 ^ len_of TYPE('c);
    \<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s; j > 0 \<rbrakk>
    \<Longrightarrow> ccorres (\<lambda>rv i'. i' = of_nat (i + length xs * of_nat j)) xf (\<lambda>s. P 0 \<longrightarrow> F 0 s) ({s. xf s = of_nat i} \<inter> Q) hs
       (NonDetMonad.sequence_x xs)
       (While {s. P (xf s)} (body;;
                 Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s)))"
  apply (simp add: sequence_x_sequence liftM_def[symmetric]
                   ccorres_liftM_simp)
  apply (rule ccorres_rel_imp)
   apply (rule ccorres_sequence_while_genQ
                   [where xf'=xfdc and r'=dc and xf_update=xf_update, simplified],
          (simp add: dc_def cong: ccorres_all_cong)+)
  done

lemma ccorres_sequence_x_while_gen':
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  shows
  "\<lbrakk>\<And>n ys. n < length xs \<Longrightarrow> ccorres dc xfdc (F (n * j)) {s. xf s = of_nat (i + n * j)} hs (xs ! n) body;
    \<And>n. P n = (n < of_nat (i + length xs * j)); \<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} body {t. xf t = xf s};
    \<And>n. Suc n < length xs \<Longrightarrow> \<lbrace>F (n * j)\<rbrace> xs ! n \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>; i + length xs * j < 2 ^ len_of TYPE('c);
    \<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s; 0 < j \<rbrakk>
    \<Longrightarrow> ccorres (\<lambda>rv i'. i' = of_nat (i + length xs * of_nat j)) xf (F 0) {s. xf s = of_nat i} hs
       (NonDetMonad.sequence_x xs)
       (While {s. P (xf s)} (body;;
                 Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s)))"
  apply (simp add: sequence_x_sequence liftM_def[symmetric]
                   ccorres_liftM_simp)
  apply (rule ccorres_rel_imp)
   apply (rule ccorres_sequence_while_gen'
                   [where xf'=xfdc and r'=dc and xf_update=xf_update, simplified],
          (simp add: dc_def cong: ccorres_all_cong)+)
  done

lemma i_xf_for_sequence:
  "\<forall>s f. i_' (i_'_update f s) = f (i_' s) \<and> globals (i_'_update f s) = globals s"
  by simp

lemma ccorres_sequence_x_while_genQ:
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes one: "\<forall>n < length xs. ccorres dc xfdc (F (n * j) ) ({s. xf s = of_nat n * of_nat j} \<inter> Q) hs (xs ! n) body"
  and      pn: "\<And>n. P n = (n < of_nat (length xs * j))"
  and   bodyi: "\<forall>s. xf s < of_nat (length xs * j)
    \<longrightarrow> \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> ({s} \<inter> Q) body {t. xf t = xf s \<and> xf_update (\<lambda>x. xf t + of_nat j) t \<in> Q}"
  and      hi: "\<And>n. Suc n < length xs \<Longrightarrow> \<lbrace> F (n * j) \<rbrace> (xs ! n) \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>"
  and     lxs: "length xs * j < 2 ^ len_of TYPE('c)"
  and      xf: "\<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s"
  and       j: "0 < j"
  shows  "ccorres (\<lambda>rv rv'. rv' = of_nat (length xs) * of_nat j) xf (\<lambda>s. P 0 \<longrightarrow> F 0 s)
                  {s. xf_update (\<lambda>_. 0) s \<in> Q} hs
                  (sequence_x xs)
                  (Basic (\<lambda>s. xf_update (\<lambda>_. 0) s);;
          (While {s. P (xf s)}
              (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s))))"
  apply (rule ccorres_symb_exec_r)
    apply (rule ccorres_rel_imp)
     apply (rule ccorres_sequence_x_while_genQ' [where i=0 and xf_update=xf_update and Q=Q, simplified])
           apply (simp add: assms hi[simplified])+
   apply (rule conseqPre, vcg)
   apply (clarsimp simp add: xf)
  apply (rule conseqPre, vcg)
  apply (simp add: xf rf_sr_def)
  done

lemma ccorres_sequence_x_while_gen:
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes one: "\<forall>n < length xs. ccorres dc xfdc (F (n * j)) {s. xf s = of_nat n * of_nat j} hs (xs ! n) body"
  and      pn: "\<And>n. P n = (n < of_nat (length xs * j))"
  and   bodyi: "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} body {t. xf t = xf s}"
  and      hi: "\<And>n. Suc n < length xs \<Longrightarrow> \<lbrace> F (n * j) \<rbrace> (xs ! n) \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>"
  and     lxs: "length xs * j < 2 ^ len_of TYPE('c)"
  and      xf: "\<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s"
  and       j: "0 < j"
  shows  "ccorres (\<lambda>rv rv'. rv' = of_nat (length xs) * of_nat j) xf (F 0) UNIV hs
                  (sequence_x xs)
                  (Basic (\<lambda>s. xf_update (\<lambda>_. 0) s);;
          (While {s. P (xf s)}
              (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s))))"
  apply (rule ccorres_symb_exec_r)
    apply (rule ccorres_rel_imp)
     apply (rule ccorres_sequence_x_while_gen' [where i=0 and xf_update=xf_update, simplified])
           apply (simp add: assms hi[simplified])+
   apply vcg
   apply (simp add: xf)
  apply vcg
  apply (simp add: xf rf_sr_def)
  done

lemma ccorres_mapM_x_while_gen:
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes rl: "\<forall>n. n < length xs \<longrightarrow> ccorres dc xfdc (F (n * j)) {s. xf s = of_nat n * of_nat j} hs (f (xs ! n)) body"
  and  guard: "\<And>n. P n = (n < of_nat (length xs * j))"
  and  bodyi: "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} body {s'. xf s' = xf s}"
  and  hi: "\<And>n. Suc n < length xs \<Longrightarrow> \<lbrace>F (n * j)\<rbrace> f (xs ! n) \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>"
  and  wb: "length xs * j < 2 ^ len_of TYPE('c)"
  and  xf: "\<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s"
  and   j: "0 < j"
  shows  "ccorres (\<lambda>rv rv'. rv' = of_nat (length xs) * of_nat j) xf (F (0 :: nat)) UNIV hs
                  (mapM_x f xs)
                  (Basic (\<lambda>s. xf_update (\<lambda>_. 0) s);;
          (While {s. P (xf s)}
              (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s))))"
  unfolding mapM_x_def
  apply (rule ccorres_rel_imp)
   apply (rule ccorres_sequence_x_while_gen[where xf_update=xf_update])
         apply (simp add: assms hi[simplified])+
  done

lemma ccorres_mapM_x_while_genQ:
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes rl: "\<forall>n. n < length xs \<longrightarrow> ccorres dc xfdc (F (n * j)) ({s. xf s = of_nat n * of_nat j} \<inter> Q) hs (f (xs ! n)) body"
  and  guard: "\<And>n. P n = (n < of_nat (length xs * j))"
  and  bodyi: "\<forall>s. xf s < of_nat (length xs * j)
    \<longrightarrow> \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> ({s} \<inter> Q) body {t. xf t = xf s \<and> xf_update (\<lambda>x. xf t + of_nat j) t \<in> Q}"
  and  hi: "\<And>n. Suc n < length xs \<Longrightarrow> \<lbrace>F (n * j)\<rbrace> f (xs ! n) \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>"
  and  wb: "length xs * j < 2 ^ len_of TYPE('c)"
  and  xf: "\<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s"
  and   j: "0 < j"
  shows  "ccorres (\<lambda>rv rv'. rv' = of_nat (length xs) * of_nat j) xf (\<lambda>s. P 0 \<longrightarrow> F (0 :: nat) s)
                  {s. xf_update (\<lambda>_. 0) s \<in> Q} hs
                  (mapM_x f xs)
                  (Basic (\<lambda>s. xf_update (\<lambda>_. 0) s);;
          (While {s. P (xf s)}
              (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s))))"
  unfolding mapM_x_def
  apply (rule ccorres_rel_imp)
   apply (rule ccorres_sequence_x_while_genQ[where xf_update=xf_update])
         apply (simp add: assms hi[simplified])+
  done

lemma ccorres_mapM_x_while_gen':
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes rl: "\<forall>n. n < length xs \<longrightarrow>
                   ccorres dc xfdc (F (n * j)) {s. xf s = of_nat (i + n * j)} hs (f (xs ! n)) body"
  and  guard: "\<And>n. P n = (n < of_nat (i + length xs * j))"
  and  bodyi: "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} body {s'. xf s' = xf s}"
  and  hi: "\<And>n. Suc n < length xs \<Longrightarrow> \<lbrace>F (n *j)\<rbrace> f (xs ! n) \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>"
  and  wb: "i + length xs * j < 2 ^ len_of TYPE('c)"
  and  xf: "\<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s"
  and   j: "0 < j"
  shows  "ccorres (\<lambda>rv rv'. rv' = of_nat (i + length xs * j)) xf
                  (F (0 :: nat)) {s. xf s = of_nat i} hs
                  (mapM_x f xs)
                  (While {s. P (xf s)}
                     (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s)))"
  unfolding mapM_x_def
  apply (rule ccorres_rel_imp)
   apply (rule ccorres_sequence_x_while_gen'[where xf_update=xf_update])
         apply (clarsimp simp only: length_map nth_map rl)
        apply (simp add: assms hi[simplified])+
  done

lemma ccorres_zipWithM_x_while_genQ:
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes rl: "\<forall>n. n < length xs \<and> n < length ys \<longrightarrow> ccorres dc xfdc (F (n * j)) ({s. xf s = of_nat n * of_nat j} \<inter> Q)
      hs (f (xs ! n) (ys ! n)) body"
  and  guard: "\<And>n. P n = (n < of_nat (min (length xs) (length ys)) * of_nat j)"
  and  bodyi: "\<forall>s. xf s < of_nat (min (length xs) (length ys)) * of_nat j
    \<longrightarrow> \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> ({s} \<inter> Q) body {t. xf t = xf s \<and> xf_update (\<lambda>x. xf t + of_nat j) t \<in> Q}"
  and  hi: "\<And>n. Suc n < length xs \<and> Suc n < length ys \<Longrightarrow> \<lbrace>F (n * j)\<rbrace> f (xs ! n) (ys ! n) \<lbrace>\<lambda>_. F (Suc n * j)\<rbrace>"
  and  wb: "min (length xs) (length ys) * j < 2 ^ len_of TYPE('c)"
  and  xf: "\<forall>s f. xf (xf_update f s) = f (xf s) \<and> globals (xf_update f s) = globals s"
  and   j: "0 < j"
  shows  "ccorres (\<lambda>rv rv'. rv' = of_nat (min (length xs) (length ys) * j)) xf
                  (F (0 :: nat)) {s. xf_update (\<lambda>_. 0) s \<in> Q} hs
                  (zipWithM_x f xs ys)
                  (Basic (\<lambda>s. xf_update (\<lambda>_. 0) s);;
          (While {s. P (xf s)}
              (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + of_nat j) s))))"
  unfolding zipWithM_x_def
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_rel_imp [OF ccorres_sequence_x_while_genQ[where F=F, OF _ _ _ _ _ xf j]];
           simp)
        apply (simp add: zipWith_nth)
        apply (rule rl)
       apply (rule guard)
      apply (rule bodyi)
     apply (simp add: zipWith_nth hi[simplified])
    apply (rule wb)
   apply simp+
  done

\<comment> \<open>Temporarily remove ccorres_weak_cong, so that the following lemmas can be constructed
    with simplified return relations.
    We do not use ccorres_all_cong due to it causing unexpected eta-expansion.\<close>
context
notes ccorres_weak_cong[cong del]
begin
lemmas ccorres_sequence_x_while'
    = ccorres_sequence_x_while_gen' [OF _ _ _ _ _ i_xf_for_sequence, folded word_bits_def,
                                     where j=1, simplified]

lemmas ccorres_sequence_x_while
    = ccorres_sequence_x_while_gen [OF _ _ _ _ _ i_xf_for_sequence, folded word_bits_def,
                                    where j=1, simplified]

lemmas ccorres_sequence_x_whileQ
    = ccorres_sequence_x_while_genQ [OF _ _ _ _ _ i_xf_for_sequence, folded word_bits_def,
                                     where j=1, simplified]

lemmas ccorres_mapM_x_while
    = ccorres_mapM_x_while_gen [OF _ _ _ _ _ i_xf_for_sequence, folded word_bits_def,
                                where j=1, simplified]

lemmas ccorres_mapM_x_whileQ
    = ccorres_mapM_x_while_genQ [OF _ _ _ _ _ i_xf_for_sequence, folded word_bits_def,
                                 where j=1, simplified]

lemmas ccorres_mapM_x_while'
    = ccorres_mapM_x_while_gen' [OF _ _ _ _ _ i_xf_for_sequence, folded word_bits_def,
                                 where j=1, simplified]

lemmas ccorres_zipWithM_x_while_gen = ccorres_zipWithM_x_while_genQ[where Q=UNIV, simplified]

lemmas ccorres_zipWithM_x_while
    = ccorres_zipWithM_x_while_gen[OF _ _ _ _ _ i_xf_for_sequence, folded word_bits_def,
                                   where j=1, simplified]
end

end

lemma ccorres_sequenceE_while_gen_either_way:
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes one: "\<And>n ys. \<lbrakk> n < length xs; n = length ys \<rbrakk> \<Longrightarrow>
                    ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv rv'. r' (ys @ [rv]) rv')) xf'
                            (inl_rrel arrel) axf
                            (F n) (Q \<inter> {s. xf s = xfrel n \<and> r' ys (xf' s)}) hs
                            (xs ! n) body"
  and      pn: "\<And>n. (n < length xs \<longrightarrow> P (xfrel n)) \<and> \<not> P (xfrel (length xs))"
  and xfrel_u: "\<And>n. xfrel_upd (xfrel n) = xfrel (Suc n)"
  and   bodyi: "\<And>s. s \<in> Q \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} body (Q \<inter> {t. xf t = xf s}), UNIV"
  and      hi: "\<And>n. n < length xs \<Longrightarrow> \<lbrace> F n \<rbrace> (xs ! n) \<lbrace>\<lambda>_. F (Suc n)\<rbrace>,-"
  and      xf: "\<forall>s f. xf (xf_update f s) = f (xf s)"
  and     xf': "\<forall>s f. xf' (xf_update f s) = (xf' s)
                               \<and> ((xf_update f s \<in> Q) = (s \<in> Q))
                               \<and> (\<forall>s'. ((s', xf_update f s) \<in> sr) = ((s', s) \<in> sr))"
  shows  "ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv (i', rv'). r' rv rv' \<and> i' = xfrel (length xs)))
                  (\<lambda>s. (xf s, xf' s)) arrel axf
                  (F 0) (Q \<inter> {s. xf s = xfrel 0 \<and> r' [] (xf' s)}) hs
                  (sequenceE xs)
                  (While {s. P (xf s)}
                     (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xfrel_upd (xf s)) s)))"
  (is "ccorres_underlying sr \<Gamma> (inr_rrel ?r') ?xf' arrel axf ?G ?G' hs (sequenceE xs) ?body")
proof -
  define init_xs where "init_xs \<equiv> xs"

  have rl: "xs = drop (length init_xs - length xs) init_xs" unfolding init_xs_def
    by fastforce

  note pn' = pn [folded init_xs_def]
  note one' = one [folded init_xs_def]
  note hi'  = hi [folded init_xs_def]

  let ?Q  = "\<lambda>xs. F (length init_xs - length xs)"
  let ?Q' = "\<lambda>xs zs. Q \<inter> {s. (xf s) = xfrel (length init_xs - length xs)
                         \<and> r' zs (xf' s)}"
  let ?r'' = "\<lambda>zs rv (i', rv'). r' (zs @ rv) rv'
                   \<and> i' = xfrel (length init_xs)"

  have "\<forall>zs. length zs = length init_xs - length xs \<longrightarrow>
             ccorres_underlying sr \<Gamma> (inr_rrel (?r'' zs)) ?xf' (inl_rrel arrel) axf
             (?Q xs) (?Q' xs zs) hs
             (sequenceE xs) ?body"
  using rl
  proof (induct xs)
    case Nil
    thus ?case
      apply clarsimp
      apply (rule iffD1 [OF ccorres_expand_while_iff])
      apply (simp add: sequenceE_def returnOk_def)
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

    note hi'' = hi' [OF ly', folded yv]

    show ?case
      apply (clarsimp simp: sequenceE_Cons)
      apply (rule ccorres_guard_imp2)
       apply (rule iffD1 [OF ccorres_expand_while_iff])
       apply (rule ccorres_cond_true)
       apply (rule ccorres_rhs_assoc)+
       apply (rule ccorres_splitE)
           apply simp
           apply (rule_tac ys="zs" in one'')
           apply simp
          apply (rule ceqv_refl)
         apply (rule ccorres_symb_exec_r)
           apply (simp add: liftME_def[symmetric] liftME_liftM)
           apply (rule ccorres_rel_imp2, rule_tac zs="zs @ [rv]" in ih)
             apply (cut_tac ly, simp)
            apply (clarsimp elim!: inl_inrE)
           apply (clarsimp elim!: inl_inrE)
          apply vcg
         apply (rule conseqPre)
          apply vcg
         apply (clarsimp simp: xf xf')
        apply (subst ln)
        apply (rule hi'')
       apply (rule HoarePartialDef.Conseq [where P = "Q \<inter> {s. xfrel_upd (xf s) = xfrel (length init_xs - length ys)}"])
       apply (intro ballI exI)
       apply (rule conjI)
        apply (rule_tac s=s in bodyi)
        apply simp
       apply (clarsimp simp: xf xf' ccHoarePost_def elim!: inl_inrE)
      apply (clarsimp simp: ln pn' xfrel_u diff_Suc_less[OF lt0])
      done
  qed
  thus ?thesis
    by (clarsimp simp: init_xs_def dest!: spec[where x=Nil]
                elim!: ccorres_rel_imp2 inl_inrE
                 cong: ccorres_all_cong)
 qed

lemma ccorres_sequenceE_while_down:
  fixes xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes one: "\<And>n ys. \<lbrakk> n < length xs; n = length ys \<rbrakk> \<Longrightarrow>
                    ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv rv'. r' (ys @ [rv]) rv')) xf'
                            (inl_rrel arrel) axf
                            (F n) (Q \<inter> {s. xf s = (startv - of_nat n) \<and> r' ys (xf' s)}) hs
                            (xs ! n) body"
  and      pn: "\<And>n. (n < length xs \<longrightarrow> P (startv - of_nat n)) \<and> \<not> P (startv - of_nat (length xs))"
  and   bodyi: "\<And>s. s \<in> Q \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} body (Q \<inter> {t. xf t = xf s}), UNIV"
  and      hi: "\<And>n. n < length xs \<Longrightarrow> \<lbrace> F n \<rbrace> (xs ! n) \<lbrace>\<lambda>_. F (Suc n)\<rbrace>,-"
  and      xf: "\<forall>s f. xf (xf_update f s) = f (xf s)"
  and     xf': "\<forall>s f. xf' (xf_update f s) = (xf' s)
                               \<and> ((xf_update f s \<in> Q) = (s \<in> Q))
                               \<and> (\<forall>s'. ((s', xf_update f s) \<in> sr) = ((s', s) \<in> sr))"
  shows  "ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv (i', rv'). r' rv rv' \<and> i' = (startv - of_nat (length xs))))
                  (\<lambda>s. (xf s, xf' s)) arrel axf
                  (F 0) (Q \<inter> {s. xf s = (startv - of_nat 0) \<and> r' [] (xf' s)}) hs
                  (sequenceE xs)
                  (While {s. P (xf s)}
                     (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s - 1) s)))"
  (is "ccorres_underlying sr \<Gamma> (inr_rrel ?r') ?xf' arrel axf ?G ?G' hs (sequenceE xs) ?body")
  by (rule ccorres_sequenceE_while_gen_either_way
                   [OF one, where xf_update=xf_update],
      simp_all add: bodyi hi xf xf' pn)

lemma ccorres_sequenceE_while_gen':
  fixes i :: "nat" and xf :: "globals myvars \<Rightarrow> ('c :: len) word"
  assumes one: "\<And>n ys. \<lbrakk> n < length xs; n = length ys \<rbrakk> \<Longrightarrow>
                    ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv rv'. r' (ys @ [rv]) rv')) xf'
                            (inl_rrel arrel) axf
                            (F n) (Q \<inter> {s. xf s = of_nat (i + n) \<and> r' ys (xf' s)}) hs
                            (xs ! n) body"
  and      pn: "\<And>n. P n = (n < of_nat (i + length xs))"
  and   bodyi: "\<And>s. s \<in> Q \<Longrightarrow> \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} body (Q \<inter> {t. xf t = xf s}), UNIV"
  and      hi: "\<And>n. n < length xs \<Longrightarrow> \<lbrace> F n \<rbrace> (xs ! n) \<lbrace>\<lambda>_. F (Suc n)\<rbrace>,-"
  and     lxs: "i + length xs < 2 ^ len_of TYPE('c)"
  and      xf: "\<forall>s f. xf (xf_update f s) = f (xf s)"
  and     xf': "\<forall>s f. xf' (xf_update f s) = (xf' s)
                               \<and> ((xf_update f s \<in> Q) = (s \<in> Q))
                               \<and> (\<forall>s'. ((s', xf_update f s) \<in> sr) = ((s', s) \<in> sr))"
  shows  "ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv (i', rv'). r' rv rv' \<and> i' = of_nat (i + length xs)))
                  (\<lambda>s. (xf s, xf' s)) arrel axf
                  (F 0) (Q \<inter> {s. xf s = of_nat i \<and> r' [] (xf' s)}) hs
                  (sequenceE xs)
                  (While {s. P (xf s)}
                     (body ;; Basic (\<lambda>s. xf_update (\<lambda>_. xf s + 1) s)))"
  (is "ccorres_underlying sr \<Gamma> (inr_rrel ?r') ?xf' arrel axf ?G ?G' hs (sequenceE xs) ?body")
  apply (rule ccorres_sequenceE_while_gen_either_way
                   [OF one, where xf_update=xf_update, simplified add_0_right],
         simp_all add: bodyi hi lxs xf xf' pn)
  apply clarsimp
  apply (simp only: Abs_fnat_hom_add, rule of_nat_mono_maybe)
   apply (rule lxs)
  apply simp
  done

lemma ccorres_sequenceE_while:
  fixes axf :: "globals myvars \<Rightarrow> 'e" shows
  "\<lbrakk>\<And>ys. length ys < length xs \<Longrightarrow>
        ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv rv'. r' (ys @ [rv]) rv')) xf'
                            (inl_rrel arrel) axf
                            (F (length ys)) (Q \<inter> {s. i_' s = of_nat (length ys) \<and> r' ys (xf' s)}) hs
                            (xs ! length ys) body;
    \<And>n. P n = (n < of_nat (length xs));
    \<And>s. s \<in> Q \<Longrightarrow> \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} body (Q \<inter> {t. i_' t = i_' s}),UNIV;
    \<And>n. n < length xs \<Longrightarrow> \<lbrace>F n\<rbrace> xs ! n \<lbrace>\<lambda>_. F (Suc n)\<rbrace>, -;
     length xs < 2 ^ word_bits;
     \<forall>s f. xf' (i_'_update f s) = xf' s
                 \<and> ((i_'_update f s \<in> Q) = (s \<in> Q))
                 \<and> (\<forall>s'. ((s', i_'_update f s) \<in> sr) = ((s', s) \<in> sr)) \<rbrakk>
    \<Longrightarrow> ccorres_underlying sr \<Gamma> (inr_rrel (\<lambda>rv (i', rv'). r' rv rv' \<and> i' = of_nat (length xs)))
                  (\<lambda>s. (i_' s, xf' s)) arrel axf
                  (F 0) (Q \<inter> {s. r' [] (xf' s)}) hs
          (sequenceE xs)
          (Basic (\<lambda>s. i_'_update (\<lambda>_. 0) s) ;;
           While {s. P (i_' s)} (body;;
             Basic (\<lambda>s. i_'_update (\<lambda>_. i_' s + 1) s)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_r)
     apply (rule ccorres_rel_imp2)
       apply (rule ccorres_sequenceE_while_gen'[where i=0, simplified, where xf_update=i_'_update],
              (assumption | simp)+)
         apply (simp add: word_bits_def)
        apply simp+
    apply vcg
   apply (rule conseqPre, vcg)
   apply clarsimp
  apply simp
  done

context kernel begin

lemma ccorres_split_nothrow_novcg_case_sum:
  "\<lbrakk>ccorresG sr \<Gamma> (f' \<currency> r') (liftxf es ef' vf' xf') P P' [] a c;
    \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv');
    \<And>rv rv'. \<lbrakk> r' rv (vf' rv'); ef' rv' = scast EXCEPTION_NONE \<rbrakk>
             \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' rv');
    \<And>err rv' err'.
        \<lbrakk> ef' rv' \<noteq> scast EXCEPTION_NONE; f' err (ef' rv') err' \<rbrakk>
             \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (QE err) (Q'' err rv' err') hs (e err) (d' rv');
    \<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>, \<lbrace>QE\<rbrace>; guard_is_UNIV (\<lambda>rv rv'. r' rv (vf' rv')) xf'
                               (\<lambda>rv rv'. {s. ef' rv' = scast EXCEPTION_NONE \<longrightarrow> s \<in> Q' rv rv'});
    \<And>err. guard_is_UNIV (\<lambda>rv. f' err (ef' rv)) es
             (\<lambda>rv rv'. {s. ef' (xf' s) \<noteq> scast EXCEPTION_NONE \<longrightarrow> s \<in> Q'' err rv rv'})\<rbrakk>
      \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) P' hs (a >>= case_sum e b) (c;;d)"
  apply (rule_tac R="case_sum QE Q" and R'="case_sum QE' QR'" for QE' QR'
              in ccorres_master_split_nohs_UNIV)
     apply assumption
    apply (case_tac rv, simp_all)[1]
     apply (erule ccorres_abstract)
     apply (rule ccorres_abstract[where xf'=es], rule ceqv_refl)
     apply (rule_tac P="ef' rv' \<noteq> scast EXCEPTION_NONE" in ccorres_gen_asm2)
     apply (rule_tac P="f' aa (ef' rv') rv'a" in ccorres_gen_asm2)
     apply assumption
    apply (erule ccorres_abstract)
    apply (rule_tac P="r' ba (vf' rv')" in ccorres_gen_asm2)
    apply (rule_tac P="ef' rv' = scast EXCEPTION_NONE" in ccorres_gen_asm2)
    apply assumption
   apply (simp add: validE_def)
   apply (erule hoare_strengthen_post, simp split: sum.split_asm)
  apply (clarsimp simp: guard_is_UNIV_def
                 split: sum.split)
  done

lemma ccorres_split_nothrow_case_sum:
  "\<lbrakk>ccorresG sr \<Gamma> (f' \<currency> r') (liftxf es ef' vf' xf') P P' hs a c;
    \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' d (d' rv');
    \<And>rv rv'. \<lbrakk> r' rv (vf' rv'); ef' rv' = scast EXCEPTION_NONE \<rbrakk>
             \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (Q rv) (Q' rv rv') hs (b rv) (d' rv');
    \<And>err rv' err'.
        \<lbrakk> ef' rv' \<noteq> scast EXCEPTION_NONE; f' err (ef' rv') err' \<rbrakk>
             \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (QE err) (Q'' err rv' err') hs (e err) (d' rv');
    \<lbrace>R\<rbrace> a \<lbrace>Q\<rbrace>, \<lbrace>QE\<rbrace>; \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> R' c {s. (\<forall>rv'. ef' (xf' s) = scast EXCEPTION_NONE \<longrightarrow> r' rv' (vf' (xf' s))
                                                 \<longrightarrow>  s \<in> Q' rv' (xf' s))
                                   \<and> (\<forall>ft. ef' (xf' s) \<noteq> scast EXCEPTION_NONE \<longrightarrow> f' ft (ef' (xf' s)) (es s)
                                                 \<longrightarrow> s \<in> Q'' ft (xf' s) (es s))} \<rbrakk>
      \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf (P and R) (P' \<inter> R') hs (a >>= case_sum e b) (c;;d)"
  apply (erule_tac R="case_sum QE Q" and R'="case_sum QE' QR'" for QE' QR'
           in ccorres_master_split_hs)
     apply (case_tac rv, simp_all)[1]
      apply (erule ccorres_abstract)
      apply (rule ccorres_abstract[where xf'=es], rule ceqv_refl)
      apply (rule_tac P="ef' rv' \<noteq> scast EXCEPTION_NONE" in ccorres_gen_asm2)
      apply (rule_tac P="f' aa (ef' rv') rv'a" in ccorres_gen_asm2)
      apply assumption
     apply (erule ccorres_abstract)
     apply (rule_tac P="r' ba (vf' rv')" in ccorres_gen_asm2)
     apply (rule_tac P="ef' rv' = scast EXCEPTION_NONE" in ccorres_gen_asm2)
     apply assumption
    apply (rule ccorres_empty[where P=\<top>])
   apply (simp add: validE_def)
   apply (erule hoare_strengthen_post, simp split: sum.split_asm)
  apply (drule exec_handlers_Hoare_from_vcg_nofail)
  apply (erule exec_handlers_Hoare_Post [OF _ _ subset_refl])
  apply (clarsimp simp: ccHoarePost_def split: sum.split)
  done

end

text \<open>@{method ccorres_rewrite} support for discarding everything after @{term creturn}.\<close>

lemma never_continues_creturn [C_simp_throws]:
  "never_continues \<Gamma> (creturn rtu xfu v)"
  by (auto simp: never_continues_def creturn_def elim: exec_elim_cases)

lemma never_continues_creturn_void [C_simp_throws]:
  "never_continues \<Gamma> (creturn_void rtu)"
  by (auto simp: never_continues_def creturn_void_def elim: exec_elim_cases)

lemma
  "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
      (c1 ;; (c2 ;; c3 ;; (creturn rtu xfu v ;; c4 ;; c5) ;; c6 ;; c7))"
  apply ccorres_rewrite
  apply (match conclusion in "ccorres_underlying sr \<Gamma> r xf r' xf' P P' hs H
                               (c1 ;; (c2 ;; c3 ;; creturn rtu xfu v))" \<Rightarrow> \<open>-\<close>)
  oops

end
