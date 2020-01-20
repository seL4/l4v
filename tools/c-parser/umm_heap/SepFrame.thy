(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* License: BSD, terms see file ./LICENSE *)

theory SepFrame
imports SepTactic
begin

class heap_state_type'

instance heap_state_type' \<subseteq> type ..

consts
  hst_mem :: "'a::heap_state_type' \<Rightarrow> heap_mem"
  hst_mem_update :: "(heap_mem \<Rightarrow> heap_mem) \<Rightarrow> 'a::heap_state_type' \<Rightarrow> 'a"
  hst_htd :: "'a::heap_state_type' \<Rightarrow> heap_typ_desc"
  hst_htd_update :: "(heap_typ_desc \<Rightarrow> heap_typ_desc) \<Rightarrow> 'a::heap_state_type' \<Rightarrow> 'a"

class heap_state_type = heap_state_type' +
  assumes hst_htd_htd_update [simp]: "hst_htd (hst_htd_update d s) = d (hst_htd s)"
  assumes hst_mem_mem_update [simp]: "hst_mem (hst_mem_update h s) = h (hst_mem s)"
  assumes hst_htd_mem_update [simp]: "hst_htd (hst_mem_update h s) = hst_htd s"
  assumes hst_mem_htd_update [simp]: "hst_mem (hst_htd_update d s) = hst_mem s"

translations
  "s\<lparr> hst_mem := x\<rparr>" <= "CONST hst_mem_update (K_record x) s"
  "s\<lparr> hst_htd := x\<rparr>" <= "CONST hst_htd_update (K_record x) s"

definition lift_hst :: "'a::heap_state_type' \<Rightarrow> heap_state" where
  "lift_hst s \<equiv> lift_state (hst_mem s,hst_htd s)"

definition point_eq_mod :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "point_eq_mod f g X \<equiv> \<forall>x. x \<notin> X \<longrightarrow> f x = g x"

definition exec_fatal :: "('s,'b,'c) com \<Rightarrow> ('s,'b,'c) body \<Rightarrow> 's \<Rightarrow> bool" where
  "exec_fatal C \<Gamma> s \<equiv> (\<exists>f. \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Fault f) \<or> (\<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Stuck)"

definition restrict_htd :: "'s::heap_state_type' \<Rightarrow> s_addr set \<Rightarrow> 's" where
  "restrict_htd s X \<equiv> s\<lparr> hst_htd := restrict_s (hst_htd s) X \<rparr>"

definition restrict_safe_OK ::
  "'s \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('s,'c) xstate) \<Rightarrow> s_addr set \<Rightarrow> ('s::heap_state_type','b,'c) com \<Rightarrow>
     ('s,'b,'c) body \<Rightarrow> bool" where
  "restrict_safe_OK s t f X C \<Gamma> \<equiv>
      \<Gamma> \<turnstile> \<langle>C,(Normal (restrict_htd s X))\<rangle> \<Rightarrow> f (restrict_htd t X) \<and>
      point_eq_mod (lift_state (hst_mem t,hst_htd t)) (lift_state (hst_mem s,hst_htd s)) X"

definition restrict_safe ::
  "'s \<Rightarrow> ('s,'c) xstate \<Rightarrow> ('s::heap_state_type','b,'c) com \<Rightarrow> ('s,'b,'c) body \<Rightarrow> bool" where
  "restrict_safe s t C \<Gamma> \<equiv>
     \<forall>X. (case t of
            Normal t' \<Rightarrow> restrict_safe_OK s t' Normal X C \<Gamma>
          | Abrupt t' \<Rightarrow> restrict_safe_OK s t' Abrupt X C \<Gamma>
          | _ \<Rightarrow> False) \<or>
         exec_fatal C \<Gamma> (restrict_htd s X)"

definition mem_safe :: "('s::{heap_state_type',type},'b,'c) com \<Rightarrow> ('s,'b,'c) body \<Rightarrow> bool" where
  "mem_safe C \<Gamma> \<equiv> \<forall>s t. \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> t \<longrightarrow> restrict_safe s t C \<Gamma>"

definition point_eq_mod_safe ::
  "'s::{heap_state_type',type} set \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> s_addr \<Rightarrow> 'c) \<Rightarrow> bool" where
  "point_eq_mod_safe P f g \<equiv> \<forall>s X. restrict_htd s X \<in> P \<longrightarrow> point_eq_mod (g (f s)) (g s) X"

definition comm_restrict :: "('s::{heap_state_type',type} \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> s_addr set \<Rightarrow> bool" where
  "comm_restrict f s X \<equiv> f (restrict_htd s X) = restrict_htd (f s) X"

definition comm_restrict_safe :: "'s set \<Rightarrow> ('s::{heap_state_type',type} \<Rightarrow> 's) \<Rightarrow> bool" where
  "comm_restrict_safe P f \<equiv> \<forall>s X. restrict_htd s X \<in> P \<longrightarrow> comm_restrict f s X"

definition htd_ind :: "('a::{heap_state_type',type} \<Rightarrow> 'b) \<Rightarrow> bool" where
  "htd_ind f \<equiv> \<forall>x s. f s = f (hst_htd_update x s)"

definition mono_guard :: "'s::{heap_state_type',type} set \<Rightarrow> bool" where
  "mono_guard P \<equiv> \<forall>s X. restrict_htd s X \<in> P \<longrightarrow> s \<in> P"

definition expr_htd_ind :: "'s::{heap_state_type',type} set \<Rightarrow> bool" where
  "expr_htd_ind P \<equiv> \<forall>d s. s\<lparr> hst_htd := d \<rparr> \<in> P = (s \<in> P)"

primrec intra_safe :: "('s::heap_state_type','b,'c) com \<Rightarrow>  bool"
where
  "intra_safe Skip = True"
| "intra_safe (Basic f) = (comm_restrict_safe UNIV f \<and>
      point_eq_mod_safe UNIV f (\<lambda>s. lift_state (hst_mem s,hst_htd s)))"
| "intra_safe (Spec r) = (\<forall>\<Gamma>. mem_safe (Spec r) (\<Gamma> :: ('s,'b,'c) body))"
| "intra_safe (Seq C D) = (intra_safe C \<and> intra_safe D)"
| "intra_safe (Cond P C D) = (expr_htd_ind P \<and> intra_safe C \<and> intra_safe D)"
| "intra_safe (While P C) = (expr_htd_ind P \<and> intra_safe C)"
| "intra_safe (Call p) = True"
| "intra_safe (DynCom f) = (htd_ind f \<and> (\<forall>s. intra_safe (f s)))"
| "intra_safe (Guard f P C) = (mono_guard P \<and> (case C of
      Basic g \<Rightarrow> comm_restrict_safe P g \<and>
                 point_eq_mod_safe P g (\<lambda>s. lift_state (hst_mem s,hst_htd s))
      | _ \<Rightarrow> intra_safe C))"
| "intra_safe Throw = True"
| "intra_safe (Catch C D) = (intra_safe C \<and> intra_safe D)"

instance state_ext :: (heap_state_type',type) heap_state_type' ..

overloading
  hs_mem_state \<equiv> hst_mem
  hs_mem_update_state \<equiv> hst_mem_update
  hs_htd_state \<equiv> hst_htd
  hs_htd_update_state \<equiv> hst_htd_update
begin
  definition hs_mem_state [simp]: "hs_mem_state \<equiv> hst_mem \<circ> globals"
  definition hs_mem_update_state [simp]: "hs_mem_update_state \<equiv> globals_update \<circ> hst_mem_update"
  definition hs_htd_state[simp]: "hs_htd_state \<equiv> hst_htd \<circ> globals"
  definition hs_htd_update_state [simp]: "hs_htd_update_state \<equiv> globals_update \<circ> hst_htd_update"
end

instance state_ext :: (heap_state_type,type) heap_state_type
  by intro_classes auto

primrec
  intra_deps :: "('s','b,'c) com \<Rightarrow> 'b set"
where
  "intra_deps Skip = {}"
| "intra_deps (Basic f) = {}"
| "intra_deps (Spec r) = {}"
| "intra_deps (Seq C D) = (intra_deps C \<union> intra_deps D)"
| "intra_deps (Cond P C D) = (intra_deps C \<union> intra_deps D)"
| "intra_deps (While P C) = intra_deps C"
| "intra_deps (Call p) = {p}"
| "intra_deps (DynCom f) = \<Union>{intra_deps (f s) | s. True}"
| "intra_deps (Guard f P C) = intra_deps C"
| "intra_deps Throw = {}"
| "intra_deps (Catch C D) = (intra_deps C \<union> intra_deps D)"


inductive_set
  proc_deps :: "('s','b,'c) com \<Rightarrow> ('s,'b,'c) body \<Rightarrow> 'b set"
  for "C" :: "('s','b,'c) com"
  and "\<Gamma>" :: "('s,'b,'c) body"
where
  "x \<in> intra_deps C \<Longrightarrow> x \<in> proc_deps C \<Gamma>"
| "\<lbrakk> x \<in> proc_deps C \<Gamma>; \<Gamma> x = Some D; y \<in> intra_deps D \<rbrakk> \<Longrightarrow> y \<in> proc_deps C \<Gamma>"

text \<open>----\<close>

lemma point_eq_mod_refl [simp]:
  "point_eq_mod f f X"
  by (simp add: point_eq_mod_def)

lemma point_eq_mod_subs:
  "\<lbrakk> point_eq_mod f g Y; Y \<subseteq> X \<rbrakk> \<Longrightarrow> point_eq_mod f g X"
  by (force simp: point_eq_mod_def)

lemma point_eq_mod_trans:
  "\<lbrakk> point_eq_mod x y X; point_eq_mod y z X \<rbrakk> \<Longrightarrow> point_eq_mod x z X"
  by (force simp: point_eq_mod_def)

lemma mem_safe_NormalD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Normal t; mem_safe C \<Gamma>;
      \<not> exec_fatal C \<Gamma> (restrict_htd s X) \<rbrakk> \<Longrightarrow>
      (\<Gamma> \<turnstile> \<langle>C,(Normal (restrict_htd s X))\<rangle> \<Rightarrow> Normal (restrict_htd t X) \<and>
       point_eq_mod (lift_state (hst_mem t,hst_htd t))
          (lift_state (hst_mem s,hst_htd s)) X)"
  by (force simp: mem_safe_def restrict_safe_def restrict_safe_OK_def)

lemma mem_safe_AbruptD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Abrupt t; mem_safe C \<Gamma>;
      \<not> exec_fatal C \<Gamma> (restrict_htd s X) \<rbrakk> \<Longrightarrow>
      (\<Gamma> \<turnstile> \<langle>C,(Normal (restrict_htd s X))\<rangle> \<Rightarrow> Abrupt (restrict_htd t X) \<and>
       point_eq_mod (lift_state (hst_mem t,hst_htd t))
          (lift_state (hst_mem s,hst_htd s)) X)"
  by (force simp: mem_safe_def restrict_safe_def restrict_safe_OK_def)

lemma mem_safe_FaultD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Fault f; mem_safe C \<Gamma> \<rbrakk> \<Longrightarrow>
      exec_fatal C \<Gamma> (restrict_htd s X)"
  by (force simp: mem_safe_def restrict_safe_def)

lemma mem_safe_StuckD:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Stuck; mem_safe C \<Gamma> \<rbrakk> \<Longrightarrow>
      exec_fatal C \<Gamma> (restrict_htd s X)"
  by (force simp: mem_safe_def restrict_safe_def)

lemma lift_state_d_restrict [simp]:
  "lift_state (h,(restrict_s d X)) = lift_state (h,d) |` X"
  by (auto simp: lift_state_def restrict_map_def restrict_s_def split: s_heap_index.splits)

lemma dom_merge_restrict [simp]:
  "(x ++ y) |` dom y = y"
  by (rule map_add_restrict_dom_right)

lemma dom_compl_restrict [simp]:
  "x |` (UNIV - dom x) = Map.empty"
  by (force simp: restrict_map_def)

lemma lift_state_point_eq_mod:
  "\<lbrakk> point_eq_mod (lift_state (h,d)) (lift_state (h',d')) X \<rbrakk> \<Longrightarrow>
      lift_state (h,d) |` (UNIV - X) =
          lift_state (h',d') |` (UNIV - X)"
  by (auto simp: point_eq_mod_def restrict_map_def)

lemma htd_'_update_ind [simp]:
  "htd_ind f \<Longrightarrow> f (hst_htd_update x s) = f s"
  by (simp add: htd_ind_def)

lemma sep_frame':
  assumes orig_spec:  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. P (f \<acute>(\<lambda>x. x)) (lift_hst \<acute>(\<lambda>x. x))\<rbrace>
                               C
                               \<lbrace>Q (g s \<acute>(\<lambda>x. x)) (lift_hst \<acute>(\<lambda>x. x))\<rbrace>"
      and hi_f: "htd_ind f" and hi_g: "htd_ind g"
      and hi_g': "\<forall>s. htd_ind (g s)"
      and safe: "mem_safe (C::('s::heap_state_type,'b,'c) com) \<Gamma>"
  shows "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x))) (lift_hst \<acute>(\<lambda>x. x))\<rbrace>
                 C
                 \<lbrace>(Q (g s \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h s)) (lift_hst \<acute>(\<lambda>x. x))\<rbrace>"
proof (rule, rule hoare_complete, simp only: valid_def, clarify)
  fix ta x
  assume ev: "\<Gamma>\<turnstile> \<langle>C,Normal x\<rangle> \<Rightarrow> ta" and
      pre: "(P (f x) \<and>\<^sup>* R (h x)) (lift_hst x)"
  then obtain s\<^sub>0 and s\<^sub>1 where pre_P: "P (f x) s\<^sub>0" and pre_R: "R (h x) s\<^sub>1" and
      disj: "s\<^sub>0 \<bottom> s\<^sub>1" and m: "lift_hst x = s\<^sub>1 ++ s\<^sub>0"
    by (clarsimp simp: sep_conj_def map_ac_simps)
  with orig_spec hi_f have nofault: "\<not> exec_fatal C \<Gamma>
      (restrict_htd x (dom s\<^sub>0))"
    by (force simp: exec_fatal_def image_def lift_hst_def cvalid_def valid_def
                    restrict_htd_def
              dest: hoare_sound)
  show "ta \<in> Normal ` {t. (Q (g x t) \<and>\<^sup>* R (h x)) (lift_hst t)}"
  proof (cases ta)
    case (Normal s)
    moreover from this ev safe nofault have ev': "\<Gamma> \<turnstile>
        \<langle>C,Normal (x\<lparr> hst_htd := (restrict_s (hst_htd x) (dom s\<^sub>0)) \<rparr>)\<rangle> \<Rightarrow>
           Normal (s\<lparr> hst_htd := (restrict_s (hst_htd s) (dom s\<^sub>0)) \<rparr>)" and
        "point_eq_mod (lift_state (hst_mem s,hst_htd s))
            (lift_state (hst_mem x,hst_htd x)) (dom s\<^sub>0)"
      by (auto simp: restrict_htd_def dest: mem_safe_NormalD)
    moreover from this m disj have "s\<^sub>1 = lift_hst s |` (UNIV - dom s\<^sub>0)"
      apply(clarsimp simp: lift_hst_def)
      apply(subst lift_state_point_eq_mod)
       apply(fastforce dest: sym)
      apply(simp add: lift_hst_def lift_state_point_eq_mod map_add_restrict)
      apply(subst restrict_map_subdom, auto dest: map_disjD)
      done
    ultimately show ?thesis using orig_spec hi_f hi_g hi_g' pre_P pre_R m
      by (force simp: cvalid_def valid_def image_def lift_hst_def
                      map_disj_def
                intro: sep_conjI dest: hoare_sound)
  next
    case (Abrupt s) with ev safe nofault orig_spec pre_P hi_f m show ?thesis
      by - (simp, drule spec, drule hoare_sound, drule_tac X="dom s\<^sub>0" in
            mem_safe_AbruptD, assumption+,
            force simp: valid_def cvalid_def lift_hst_def restrict_htd_def)
  next
    case (Fault f) with ev safe nofault show ?thesis
      by (force dest: mem_safe_FaultD)
  next
    case Stuck with ev safe nofault show ?thesis
      by (force dest: mem_safe_StuckD)
  qed
qed

lemma sep_frame:
  "\<lbrakk> k = (\<lambda>s. (hst_mem s,hst_htd s));
      \<forall>s. \<Gamma> \<turnstile> \<lbrace>s. P (f \<acute>(\<lambda>x. x)) (lift_state (k \<acute>(\<lambda>x. x)))\<rbrace>
              C
              \<lbrace>Q (g s \<acute>(\<lambda>x. x)) (lift_state (k \<acute>(\<lambda>x. x)))\<rbrace>;
      htd_ind f; htd_ind g; \<forall>s. htd_ind (g s);
      mem_safe (C::('s::heap_state_type,'b,'c) com) \<Gamma> \<rbrakk> \<Longrightarrow>
      \<forall>s. \<Gamma> \<turnstile> \<lbrace>s. (P (f \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h \<acute>(\<lambda>x. x))) (lift_state (k \<acute>(\<lambda>x. x)))\<rbrace>
               C
               \<lbrace>(Q (g s \<acute>(\<lambda>x. x)) \<and>\<^sup>* R (h s)) (lift_state (k \<acute>(\<lambda>x. x)))\<rbrace>"
  apply(simp only:)
  apply(fold lift_hst_def)
  apply(erule (4) sep_frame')
  done


lemma point_eq_mod_safe [simp]:
  "\<lbrakk> point_eq_mod_safe P f g; restrict_htd s X \<in> P; x \<notin> X \<rbrakk> \<Longrightarrow>
      g (f s) x = (g s) x"
  apply(simp add: point_eq_mod_safe_def point_eq_mod_def)
  apply(case_tac x, force)
  done

lemma comm_restrict_safe [simp]:
  "\<lbrakk> comm_restrict_safe P f; restrict_htd s X \<in> P \<rbrakk> \<Longrightarrow>
        restrict_htd (f s ) X = f (restrict_htd s X)"
  by (simp add: comm_restrict_safe_def comm_restrict_def)

lemma mono_guardD:
  "\<lbrakk> mono_guard P; restrict_htd s X \<in> P \<rbrakk> \<Longrightarrow> s \<in> P"
  by (unfold mono_guard_def, fast)

lemma expr_htd_ind:
  "expr_htd_ind P \<Longrightarrow> restrict_htd s X \<in> P = (s \<in> P)"
  by (simp add: expr_htd_ind_def restrict_htd_def)

(* exec.intros without those already declared as [intro] *)
lemmas exec_other_intros = exec.intros(1-3) exec.intros(5-14) exec.intros(16-17) exec.intros(19-)

lemma exec_fatal_Seq:
  "exec_fatal C \<Gamma> s \<Longrightarrow> exec_fatal (C;;D) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_Seq2:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Normal t; exec_fatal D \<Gamma> t \<rbrakk> \<Longrightarrow> exec_fatal (C;;D) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_Cond:
  "exec_fatal (Cond P C D) \<Gamma> s = (if s \<in> P then exec_fatal C \<Gamma> s else
      exec_fatal D \<Gamma> s)"
  by (force simp: exec_fatal_def intro: exec_other_intros
            elim: exec_Normal_elim_cases)

lemma exec_fatal_While:
  "\<lbrakk> exec_fatal C \<Gamma> s; s \<in> P \<rbrakk> \<Longrightarrow> exec_fatal (While P C) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros
            elim: exec_Normal_elim_cases)

lemma exec_fatal_While2:
  "\<lbrakk> exec_fatal (While P C) \<Gamma> t; \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Normal t; s \<in> P \<rbrakk> \<Longrightarrow>
      exec_fatal (While P C) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros
            elim: exec_Normal_elim_cases)

lemma exec_fatal_Call:
  "\<lbrakk> \<Gamma> p = Some C; exec_fatal C \<Gamma> s \<rbrakk> \<Longrightarrow> exec_fatal (Call p) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_DynCom:
  "exec_fatal (f s) \<Gamma> s \<Longrightarrow> exec_fatal (DynCom f) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_Guard:
  "exec_fatal (Guard f P C) \<Gamma> s = (s \<in> P \<longrightarrow> exec_fatal C \<Gamma> s)"
proof (cases "s \<in> P")
  case True thus ?thesis
    by (force simp: exec_fatal_def intro: exec_other_intros
              elim: exec_Normal_elim_cases)
next
  case False thus ?thesis
    by (force simp: exec_fatal_def intro: exec_other_intros)
qed

lemma restrict_safe_Guard:
  assumes restrict: "restrict_safe s t C \<Gamma>"
  shows "restrict_safe s t (Guard f P C) \<Gamma>"
proof (cases t)
  case (Normal s) with restrict show ?thesis
    by (force simp: restrict_safe_def restrict_safe_OK_def exec_fatal_Guard
              intro: exec_other_intros)
next
  case (Abrupt s) with restrict show ?thesis
    by (force simp: restrict_safe_def restrict_safe_OK_def exec_fatal_Guard
              intro: exec_other_intros)
next
  case (Fault f) with restrict show ?thesis
    by (force simp: restrict_safe_def exec_fatal_Guard)
next
  case Stuck with restrict show ?thesis
    by (force simp: restrict_safe_def exec_fatal_Guard)
qed

lemma restrict_safe_Guard2:
  "\<lbrakk> s \<notin> P; mono_guard P \<rbrakk> \<Longrightarrow> restrict_safe s (Fault f) (Guard f P C) \<Gamma>"
  by (force simp: restrict_safe_def exec_fatal_def intro: exec_other_intros
            dest: mono_guardD)

lemma exec_fatal_Catch:
  "exec_fatal C \<Gamma> s \<Longrightarrow> exec_fatal (TRY C CATCH D END) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma exec_fatal_Catch2:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>C,Normal s\<rangle> \<Rightarrow> Abrupt t; exec_fatal D \<Gamma> t \<rbrakk> \<Longrightarrow>
      exec_fatal (TRY C CATCH D END) \<Gamma> s"
  by (force simp: exec_fatal_def intro: exec_other_intros)

lemma intra_safe_restrict [rule_format]:
  assumes safe_env: "\<And>n C. \<Gamma> n = Some C \<Longrightarrow> intra_safe C" and
      exec: "\<Gamma> \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
  shows "\<forall>s'. s = Normal s' \<longrightarrow> intra_safe C \<longrightarrow> restrict_safe s' t C \<Gamma>"
using exec
proof induct
  case (Skip s) thus ?case
    by (force simp: restrict_safe_def restrict_safe_OK_def intro: exec_other_intros)
next
  case (Guard s' P C t f) show ?case
  proof (cases "\<exists>g. C = Basic g")
    case False with Guard show ?thesis
      by - (clarsimp, split com.splits, auto dest: restrict_safe_Guard)
  next
    case True with Guard show ?thesis
      by (cases t) (force simp: restrict_safe_def restrict_safe_OK_def
                                point_eq_mod_safe_def exec_fatal_Guard
                          intro: exec_other_intros
                          elim: exec_Normal_elim_cases,
                    (fast elim: exec_Normal_elim_cases)+)
  qed
next
  case (GuardFault C f P s) thus ?case
    by (force dest: restrict_safe_Guard2)
next
  case (FaultProp C f) thus ?case by simp
next
  case (Basic f s) thus ?case
    by (force simp: restrict_safe_def restrict_safe_OK_def point_eq_mod_safe_def
              intro: exec_other_intros)
next
  case (Spec r s t) thus ?case
    by (fastforce simp: mem_safe_def intro: exec.Spec)
next
  case (SpecStuck r s) thus ?case
    by (simp add: exec.SpecStuck mem_safe_StuckD restrict_safe_def)
next
  case (Seq C s sa D ta) show ?case
  proof (cases sa)
    case (Normal s') with Seq show ?thesis
      by (cases ta)
         (clarsimp simp: restrict_safe_def restrict_safe_OK_def,
          (drule_tac x=X in spec)+, auto intro: exec_other_intros point_eq_mod_trans
                                               exec_fatal_Seq exec_fatal_Seq2)+
  next
    case (Abrupt s') with Seq show ?thesis
      by (force simp: restrict_safe_def restrict_safe_OK_def
                intro: exec_other_intros dest: exec_fatal_Seq
                elim: exec_Normal_elim_cases)
  next
    case (Fault f) with Seq show ?thesis
      by (force simp: restrict_safe_def dest: exec_fatal_Seq
                elim: exec_Normal_elim_cases)
  next
    case Stuck with Seq show ?thesis
      by (force simp: restrict_safe_def dest: exec_fatal_Seq
                elim: exec_Normal_elim_cases)
  qed
next
  case (CondTrue s P C t D) thus ?case
    by (cases t)
       (auto simp: restrict_safe_def restrict_safe_OK_def exec_fatal_Cond
             intro: exec_other_intros dest: expr_htd_ind split: if_split_asm)
next
  case (CondFalse s P C t D) thus ?case
    by (cases t)
       (auto simp: restrict_safe_def restrict_safe_OK_def exec_fatal_Cond
             intro: exec_other_intros dest: expr_htd_ind split: if_split_asm)
next
  case (WhileTrue P C s s' t) show ?case
  proof (cases s')
    case (Normal sa) with WhileTrue show ?thesis
      by (cases t)
         (clarsimp simp: restrict_safe_def restrict_safe_OK_def,
          (drule_tac x=X in spec)+, auto simp: expr_htd_ind intro: exec_other_intros
               point_eq_mod_trans exec_fatal_While exec_fatal_While2)+
  next
    case (Abrupt sa) with WhileTrue show ?thesis
      by (force simp: restrict_safe_def restrict_safe_OK_def expr_htd_ind
                intro: exec_other_intros exec_fatal_While
                elim: exec_Normal_elim_cases)
  next
    case (Fault f) with WhileTrue show ?thesis
      by (force simp: restrict_safe_def expr_htd_ind intro: exec_fatal_While)
  next
    case Stuck with WhileTrue show ?thesis
      by (force simp: restrict_safe_def expr_htd_ind intro: exec_fatal_While)
  qed
next
  case (WhileFalse P C s) thus ?case
    by (force simp: restrict_safe_def restrict_safe_OK_def expr_htd_ind
              intro: exec_other_intros)
next
  case (Call C p s t) with safe_env show ?case
    by (cases t)
       (auto simp: restrict_safe_def restrict_safe_OK_def
             intro: exec_fatal_Call exec_other_intros)
next
  case (CallUndefined p s) thus ?case
    by (force simp: restrict_safe_def exec_fatal_def intro: exec_other_intros)

next
  case (StuckProp C) thus ?case by simp
next
  case (DynCom f s t) thus ?case
    by (cases t)
       (auto simp: restrict_safe_def restrict_safe_OK_def
                   restrict_htd_def
             intro!: exec_other_intros exec_fatal_DynCom)
next
  case (Throw s) thus ?case
    by (force simp: restrict_safe_def restrict_safe_OK_def intro: exec_other_intros)
next
  case (AbruptProp C s) thus ?case by simp
next
  case (CatchMatch C D s s' t) thus ?case
    by (cases t)
       (clarsimp simp: restrict_safe_def, drule_tac x=X in spec,
        auto simp: restrict_safe_OK_def intro: exec_other_intros point_eq_mod_trans
             dest: exec_fatal_Catch exec_fatal_Catch2)+
next
  case (CatchMiss C s t D) thus ?case
    by (cases t)
       (clarsimp simp: restrict_safe_def, drule_tac x=X in spec,
        auto simp: restrict_safe_OK_def intro: exec_other_intros
             dest: exec_fatal_Catch)+
qed

lemma intra_mem_safe:
  "\<lbrakk> \<And>n C. \<Gamma> n = Some C \<Longrightarrow> intra_safe C; intra_safe C \<rbrakk> \<Longrightarrow> mem_safe C \<Gamma>"
  by (force  simp: mem_safe_def intro: intra_safe_restrict)

lemma point_eq_mod_safe_triv:
  "(\<And>s. g (f s) = g s) \<Longrightarrow> point_eq_mod_safe P f g"
  by (simp add: point_eq_mod_safe_def point_eq_mod_def)

lemma comm_restrict_safe_triv:
  "(\<And>s X. f (s\<lparr> hst_htd := restrict_s (hst_htd s) X \<rparr>) =
      (f s)\<lparr> hst_htd := restrict_s (hst_htd (f s)) X \<rparr>) \<Longrightarrow> comm_restrict_safe P f"
  by (force simp: comm_restrict_safe_def comm_restrict_def restrict_htd_def)

lemma mono_guard_UNIV [simp]:
  "mono_guard UNIV"
  by (force simp: mono_guard_def)

lemma mono_guard_triv:
  "(\<And>s X. s\<lparr> hst_htd := X \<rparr> \<in> g \<Longrightarrow> s \<in> g) \<Longrightarrow> mono_guard g"
  by (unfold mono_guard_def, unfold restrict_htd_def, fast)

lemma mono_guard_triv2:
  "(\<And>s X. s\<lparr> hst_htd := X \<rparr> \<in> g = ((s::'a::heap_state_type') \<in> g)) \<Longrightarrow>
      mono_guard g"
  by (unfold mono_guard_def, unfold restrict_htd_def, fast)

lemma dom_restrict_s:
  "x \<in> dom_s (restrict_s d X) \<Longrightarrow> x \<in> dom_s d \<and> x \<in> X"
  by (auto simp: restrict_s_def dom_s_def split: if_split_asm)

lemma mono_guard_ptr_safe:
  "\<lbrakk> \<And>s. d s = hst_htd (s::'a::heap_state_type); htd_ind p \<rbrakk> \<Longrightarrow>
      mono_guard {s. ptr_safe (p s) (d s)}"
  by (auto simp: mono_guard_def ptr_safe_def restrict_htd_def dest: subsetD dom_restrict_s)

lemma point_eq_mod_safe_ptr_safe_update:
  "\<lbrakk> d = (hst_htd::'a::heap_state_type \<Rightarrow> heap_typ_desc);
      m = (\<lambda>s. hst_mem_update (heap_update (p s) ((v s)::'b::mem_type)) s);
      h = hst_mem; k = (\<lambda>s. lift_state (h s,d s)); htd_ind p \<rbrakk> \<Longrightarrow>
      point_eq_mod_safe {s. ptr_safe (p s) (d s)} m k"
  apply (clarsimp simp: point_eq_mod_safe_def point_eq_mod_def ptr_safe_def heap_update_def
                        restrict_htd_def lift_state_def
                  intro!: heap_update_nmem_same
                  split: s_heap_index.splits)
  apply(subgoal_tac "(a,SIndexVal) \<in> s_footprint (p s)")
   apply(drule (1) subsetD)
   apply(drule dom_restrict_s, clarsimp)
  apply(drule intvlD, clarsimp)
  apply(erule s_footprintI2)
  done

lemma field_ti_s_sub_typ:
  "field_lookup (export_uinfo (typ_info_t TYPE('b::mem_type))) f 0 = Some (typ_uinfo_t TYPE('a),b) \<Longrightarrow>
      s_footprint ((Ptr &(p\<rightarrow>f))::'a::mem_type ptr) \<subseteq> s_footprint (p::'b ptr)"
  by (drule field_ti_s_sub) (simp add: s_footprint_def)

lemma ptr_safe_mono:
  "\<lbrakk> ptr_safe (p::'a::mem_type ptr) d; field_lookup (typ_info_t TYPE('a)) f 0
      = Some (t,n); export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
      ptr_safe ((Ptr &(p\<rightarrow>f))::'b::mem_type ptr) d"
  unfolding ptr_safe_def
  by (drule field_lookup_export_uinfo_Some) (auto dest: field_ti_s_sub_typ)

lemma point_eq_mod_safe_ptr_safe_update_fl:
  "\<lbrakk> d = (hst_htd::'a::heap_state_type \<Rightarrow> heap_typ_desc);
      m = (\<lambda>s. hst_mem_update (heap_update (Ptr &((p s)\<rightarrow>f)) ((v s)::'b::mem_type)) s);
      h = hst_mem; k = (\<lambda>s. lift_state (h s,d s)); htd_ind p;
      field_lookup (typ_info_t TYPE('c)) f 0 = Some (t,n);
      export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
      point_eq_mod_safe {s. ptr_safe ((p::'a \<Rightarrow> 'c::mem_type ptr) s) (d s)} m k"
  apply(drule (3) point_eq_mod_safe_ptr_safe_update)
   apply(fastforce simp: htd_ind_def)
  apply(fastforce simp: point_eq_mod_safe_def intro!: ptr_safe_mono)
  done

context
begin

private method m =
  (clarsimp simp: ptr_retyp_d_eq_snd ptr_retyp_footprint list_map_eq,
   erule notE,
   drule intvlD, clarsimp,
   (rule s_footprintI; assumption?),
   subst (asm) unat_of_nat,
   (subst (asm) mod_less; assumption?),
   subst len_of_addr_card,
   erule less_trans,
   simp)

lemma point_eq_mod_safe_ptr_safe_tag:
  "\<lbrakk> d = (hst_htd::'a::heap_state_type \<Rightarrow> heap_typ_desc); h = hst_mem;
     m = (\<lambda>s. hst_htd_update (ptr_retyp (p s)) s);
     k = (\<lambda>s. lift_state (h s,d s));
     htd_ind p \<rbrakk> \<Longrightarrow>
   point_eq_mod_safe {s. ptr_safe ((p s)::'b::mem_type ptr) (d s)} m k"
  supply if_split_asm[split]
  apply(clarsimp simp: point_eq_mod_safe_def point_eq_mod_def ptr_safe_def)
  apply(subgoal_tac "(a,b) \<notin> s_footprint (p (restrict_htd s X))")
   prefer 2
   apply(fastforce simp: restrict_htd_def dest: dom_restrict_s)
  apply(clarsimp simp: restrict_htd_def  lift_state_def split: s_heap_index.split option.splits)
  apply (safe; m?)
    apply(fastforce simp: ptr_retyp_d_eq_fst dest!: intvlD dest: s_footprintI2)
   apply(fastforce simp: ptr_retyp_d_eq_fst)
  apply(subst (asm) ptr_retyp_d_eq_snd, clarsimp)
  done

end

lemma comm_restrict_safe_ptr_safe_tag:
  fixes d::"'a::heap_state_type \<Rightarrow> heap_typ_desc"
  assumes
    fun_d: "d = hst_htd" and
    fun_upd: "m = (\<lambda>s. hst_htd_update (ptr_retyp (p s)) s)" and
    ind: "htd_ind p" and
    upd: "\<And>d d' (s::'a).
               hst_htd_update (d s) (hst_htd_update (d' s) s) = hst_htd_update ((d s) \<circ> (d' s)) s"
  shows "comm_restrict_safe {s. ptr_safe ((p s)::'b::mem_type ptr) (d s)} m"
proof (simp only: comm_restrict_safe_def comm_restrict_def, auto)
  fix s X
  assume "ptr_safe (p (restrict_htd s X)) (d (restrict_htd s X))"
  moreover from ind
  have p: "p (restrict_htd s X) = p s"
    by (simp add:  restrict_htd_def)
  ultimately
  have "ptr_retyp (p s) (restrict_s (hst_htd s) X) = restrict_s (ptr_retyp (p s) (hst_htd s))  X"
    using fun_d
    apply -
    apply(rule ext)
    apply(clarsimp simp: point_eq_mod_safe_def point_eq_mod_def ptr_safe_def restrict_htd_def)
    apply(case_tac "x \<notin> {ptr_val (p s)..+size_of TYPE('b)}")
     apply(clarsimp simp: ptr_retyp_d restrict_map_def restrict_s_def)
     apply(subst ptr_retyp_d; simp)
    apply(clarsimp simp: ptr_retyp_footprint restrict_map_def restrict_s_def)
    apply(subst ptr_retyp_footprint, simp)
    apply(rule conjI)
     apply(subgoal_tac "(x,SIndexVal) \<in> s_footprint (p s)")
      apply(fastforce simp: dom_s_def)
     apply(fastforce dest: intvlD elim: s_footprintI2)
    apply(rule ext)
    apply(clarsimp simp: map_add_def list_map_eq)
    apply(subgoal_tac "(x,SIndexTyp y) \<in> s_footprint (p s)")
     apply(fastforce simp: dom_s_def split: if_split_asm)
    apply(drule intvlD, clarsimp)
    apply(rule s_footprintI; assumption?)
    apply(metis len_of_addr_card less_trans max_size mod_less word_unat.eq_norm)
    done
  hence "((ptr_retyp (p s) \<circ> (\<lambda>x _. x) (restrict_s (hst_htd s) X)::heap_typ_desc \<Rightarrow> heap_typ_desc) =
              (\<lambda>x _. x) (restrict_s (ptr_retyp (p s) (hst_htd s)) X))"
    by - (rule ext, simp)
  moreover from upd have "hst_htd_update (ptr_retyp (p s))
        (hst_htd_update ((\<lambda>x _. x) (restrict_s (hst_htd s) X)) s) =
         hst_htd_update (((ptr_retyp (p s)) \<circ> ((\<lambda>x _. x) (restrict_s (hst_htd s) X)))) s" .
  moreover from upd
  have
    "hst_htd_update ((\<lambda>x _. x) (restrict_s (ptr_retyp (p s) (hst_htd s)) X))
                    (hst_htd_update (ptr_retyp (p s)) s) =
     hst_htd_update (((\<lambda>x _. x) (restrict_s ((ptr_retyp (p s) (hst_htd s))) X)) \<circ> (ptr_retyp (p s))) s" .
  ultimately show "m (restrict_htd s X) = restrict_htd (m s) X" using fun_d fun_upd upd p
    by (simp add: restrict_htd_def o_def)
qed

lemmas intra_sc = hrs_comm comp_def hrs_htd_update_htd_update
  point_eq_mod_safe_triv comm_restrict_safe_triv mono_guard_triv2
  mono_guard_ptr_safe point_eq_mod_safe_ptr_safe_update
  point_eq_mod_safe_ptr_safe_tag comm_restrict_safe_ptr_safe_tag
  point_eq_mod_safe_ptr_safe_update_fl

declare expr_htd_ind_def [iff]
declare htd_ind_def [iff]

lemma proc_deps_Skip [simp]:
  "proc_deps Skip \<Gamma> = {}"
  by (force elim: proc_deps.induct)

lemma proc_deps_Basic [simp]:
  "proc_deps (Basic f) \<Gamma> = {}"
  by (force elim: proc_deps.induct)

lemma proc_deps_Spec [simp]:
  "proc_deps (Spec r) \<Gamma> = {}"
  by (force elim: proc_deps.induct)

lemma proc_deps_Seq [simp]:
  "proc_deps (Seq C D) \<Gamma> = proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
proof
  show "proc_deps (C;; D) \<Gamma> \<subseteq> proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
    by - (rule, erule proc_deps.induct, auto intro: proc_deps.intros)
next
  show "proc_deps C \<Gamma> \<union> proc_deps D \<Gamma> \<subseteq> proc_deps (C;; D) \<Gamma>"
    by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+
qed

lemma proc_deps_Cond [simp]:
  "proc_deps (Cond P C D) \<Gamma> = proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
proof
  show "proc_deps (Cond P C D) \<Gamma> \<subseteq> proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
    by (rule, erule proc_deps.induct, auto intro: proc_deps.intros)
next
  show "proc_deps C \<Gamma> \<union> proc_deps D \<Gamma> \<subseteq> proc_deps (Cond P C D) \<Gamma>"
    by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+
qed

lemma proc_deps_While [simp]:
  "proc_deps (While P C) \<Gamma> = proc_deps C \<Gamma>"
  by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+

lemma proc_deps_Guard [simp]:
  "proc_deps (Guard f P C) \<Gamma> = proc_deps C \<Gamma>"
  by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+

lemma proc_deps_Throw [simp]:
  "proc_deps Throw \<Gamma> = {}"
  by (force elim: proc_deps.induct)

lemma proc_deps_Catch [simp]:
  "proc_deps (Catch  C D) \<Gamma> = proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
proof
  show "proc_deps (Catch C D) \<Gamma> \<subseteq> proc_deps C \<Gamma> \<union> proc_deps D \<Gamma>"
    by (rule, erule proc_deps.induct, auto intro: proc_deps.intros)
next
  show "proc_deps C \<Gamma> \<union> proc_deps D \<Gamma> \<subseteq> proc_deps (Catch C D) \<Gamma>"
    by auto (erule proc_deps.induct, auto intro: proc_deps.intros)+
qed

lemma proc_deps_Call [simp]:
  "proc_deps (Call p) \<Gamma> = {p} \<union> (case \<Gamma> p of Some C \<Rightarrow>
      proc_deps C (\<Gamma>(p := None)) | _ \<Rightarrow> {})" (is "?X = ?Y \<union> ?Z")
proof
  note proc_deps.intros[intro]
  show "?X \<subseteq> ?Y \<union> ?Z"
    by (rule subsetI, erule proc_deps.induct, fastforce)
       (rename_tac x D y, case_tac "x = p"; fastforce split: option.splits)
next
  show "?Y \<union> ?Z \<subseteq> ?X"
  proof (clarsimp, rule)
    show "p \<in> ?X" by (force intro: proc_deps.intros)
  next
    show "?Z \<subseteq> ?X"
      by (split option.splits, rule, force intro: proc_deps.intros)
         (clarify, erule proc_deps.induct;
          force intro: proc_deps.intros split: if_split_asm)
  qed
qed

lemma proc_deps_DynCom [simp]:
  "proc_deps (DynCom f) \<Gamma> = \<Union>{proc_deps (f s) \<Gamma> | s. True}"
  by (rule equalityI; clarsimp; erule proc_deps.induct; force intro: proc_deps.intros)

lemma proc_deps_restrict:
  "proc_deps C \<Gamma> \<subseteq> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>"
proof
  fix xa
  assume mem: "xa \<in> proc_deps C \<Gamma>"
  hence "\<forall>p. xa \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>" (is "?X")
  using mem
  proof induct
    fix x
    assume "x \<in> intra_deps C"
    thus "\<forall>p. x \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>"
      by (force intro: proc_deps.intros)
  next
    fix D x y
    assume x:
      "x \<in> proc_deps C \<Gamma>"
      "x \<in> proc_deps C \<Gamma> \<Longrightarrow> \<forall>p. x \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>"
      "\<Gamma> x = Some D"
      "y \<in> intra_deps D"
      "y \<in> proc_deps C \<Gamma>"
    show "\<forall>p. y \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>"
    proof clarify
      fix p
      assume y: "y \<notin> proc_deps (Call p) \<Gamma>"
      show "y \<in> proc_deps C (\<Gamma>(p := None))"
      proof (cases "x=p")
        case True with x y show ?thesis
          by (force intro: proc_deps.intros)
      next
        case False with x y show ?thesis
          by (clarsimp, drule_tac x=p in spec)
             (auto intro: proc_deps.intros split: option.splits)
      qed
    qed
  qed
  thus "xa \<in> proc_deps C (\<Gamma>(p := None)) \<union> proc_deps (Call p) \<Gamma>" by simp
qed

lemma exec_restrict:
  assumes exec: "\<Gamma>' \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
  shows "\<And>\<Gamma> X. \<lbrakk> \<Gamma>' = \<Gamma> |` X; proc_deps C \<Gamma> \<subseteq> X \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
using exec
proof induct
  case (Call p C s t)
  thus ?case
    using proc_deps_restrict [of C \<Gamma> p] by (force intro: exec_other_intros)
qed (force intro: exec_other_intros)+

lemma exec_restrict2:
  assumes exec: "\<Gamma> \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
  shows "\<And>X. proc_deps C \<Gamma> \<subseteq> X \<Longrightarrow> \<Gamma> |` X \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
using exec
proof induct
  case (Call p C s t) thus ?case
  using proc_deps_restrict [of C \<Gamma> p]
    by (auto intro!: exec_other_intros split: option.splits)
next
  case (DynCom f s t) thus ?case
    by - (rule exec.intros, simp, blast)
qed (auto intro: exec_other_intros)

lemma exec_restrict_eq:
  "\<Gamma> |` proc_deps C \<Gamma> \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t = \<Gamma> \<turnstile> \<langle>C,s\<rangle> \<Rightarrow> t"
  by (fast intro: exec_restrict exec_restrict2)

lemma mem_safe_restrict:
  "mem_safe C \<Gamma> = mem_safe C (\<Gamma> |` proc_deps C \<Gamma>)"
  by (auto simp: mem_safe_def restrict_safe_def restrict_safe_OK_def
                 exec_restrict_eq exec_fatal_def
           split: xstate.splits)

end
