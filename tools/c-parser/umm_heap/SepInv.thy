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

theory SepInv
imports SepCode
begin

(* FIXME: temporary hack for compatability - should generalise earlier proofs
   to avoid all the duplication in here *)

definition inv_footprint :: "'a::c_type ptr \<Rightarrow> heap_assert" where
  "inv_footprint p \<equiv>
     \<lambda>s. dom s = {(x,y). x \<in> {ptr_val p..+size_of TYPE('a)}} - s_footprint p"

text \<open>
  Like in Separation.thy, these arrows are defined using bsub and esub but
  have an \emph{input} syntax abbreviation with just sub.
  See original comment there for justification.
\<close>

definition
  sep_map_inv :: "'a::c_type ptr \<Rightarrow> 'a ptr_guard \<Rightarrow> 'a \<Rightarrow> heap_assert" ("_ \<mapsto>\<^sup>i\<^bsub>_\<^esub> _" [56,0,51] 56)
where
  "p \<mapsto>\<^sup>i\<^bsub>g\<^esub> v \<equiv> p \<mapsto>\<^sub>g v \<and>\<^sup>* inv_footprint p"

notation (input)
  sep_map_inv ("_ \<mapsto>\<^sup>i\<^sub>_ _" [56,1000,51] 56)

definition
  sep_map_any_inv :: "'a ::c_type ptr \<Rightarrow> 'a ptr_guard \<Rightarrow> heap_assert" ("_ \<mapsto>\<^sup>i\<^bsub>_\<^esub> -" [56,0] 56)
where
  "p \<mapsto>\<^sup>i\<^bsub>g\<^esub> - \<equiv> p \<mapsto>\<^sub>g - \<and>\<^sup>* inv_footprint p"

notation (input)
  sep_map_any_inv ("_ \<mapsto>\<^sup>i\<^sub>_ -" [56,0] 56)

definition
  sep_map'_inv :: "'a::c_type ptr \<Rightarrow> 'a ptr_guard \<Rightarrow> 'a \<Rightarrow> heap_assert" ("_ \<hookrightarrow>\<^sup>i\<^bsub>_\<^esub> _" [56,0,51] 56)
where
  "p \<hookrightarrow>\<^sup>i\<^bsub>g\<^esub> v \<equiv> p \<hookrightarrow>\<^sub>g v \<and>\<^sup>* inv_footprint p"

notation (input)
  sep_map'_inv ("_ \<hookrightarrow>\<^sup>i\<^sub>_ _" [56,1000,51] 56)

definition
  sep_map'_any_inv :: "'a::c_type ptr \<Rightarrow> 'a ptr_guard \<Rightarrow> heap_assert" ("_ \<hookrightarrow>\<^sup>i\<^bsub>_\<^esub> -" [56,0] 56)
where
  "p \<hookrightarrow>\<^sup>i\<^bsub>g\<^esub> - \<equiv> p \<hookrightarrow>\<^sub>g - \<and>\<^sup>* inv_footprint p"

notation (input)
  sep_map'_any_inv ("_ \<hookrightarrow>\<^sup>i\<^sub>_ -" [56,0] 56)

definition
  tagd_inv :: "'a ptr_guard \<Rightarrow> 'a::c_type ptr \<Rightarrow> heap_assert" (infix "\<turnstile>\<^sub>s\<^sup>i" 100)
where
  "g \<turnstile>\<^sub>s\<^sup>i p \<equiv> g \<turnstile>\<^sub>s p \<and>\<^sup>* inv_footprint p"

text \<open>----\<close>

lemma sep_map'_g:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g v) s \<Longrightarrow> g p"
  unfolding sep_map'_inv_def by (fastforce dest: sep_conjD sep_map'_g_exc)

lemma sep_map'_unfold:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g v) = ((p \<hookrightarrow>\<^sup>i\<^sub>g v) \<and>\<^sup>* sep_true)"
  by (simp add: sep_map'_inv_def sep_map'_def sep_conj_ac)

lemma sep_map'_any_unfold:
  "(i \<hookrightarrow>\<^sup>i\<^sub>g -) = ((i \<hookrightarrow>\<^sup>i\<^sub>g -) \<and>\<^sup>* sep_true)"
  apply(rule ext, simp add: sep_map'_any_inv_def sep_map'_any_def sep_conj_ac)
  apply(rule iffI)
   apply(subst sep_conj_com)
   apply(subst sep_conj_assoc)+
   apply(erule (1) sep_conj_impl)
   apply(clarsimp simp: sep_conj_ac)
   apply(subst (asm) sep_map'_unfold_exc, subst sep_conj_com)
   apply(subst sep_conj_exists, fast)
  apply(subst (asm) sep_conj_com)
  apply(subst (asm) sep_conj_assoc)+
  apply(erule (1) sep_conj_impl)
  apply(subst sep_map'_unfold_exc)
  apply(subst (asm) sep_conj_exists, fast)
  done

lemma sep_map'_conjE1:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. P s \<Longrightarrow> (i \<hookrightarrow>\<^sup>i\<^sub>g v) s \<rbrakk> \<Longrightarrow> (i \<hookrightarrow>\<^sup>i\<^sub>g v) s"
  by (subst sep_map'_unfold, erule sep_conj_impl, simp+)

lemma sep_map'_conjE2:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. Q s \<Longrightarrow> (i \<hookrightarrow>\<^sup>i\<^sub>g v) s \<rbrakk> \<Longrightarrow> (i \<hookrightarrow>\<^sup>i\<^sub>g v) s"
  by (subst (asm) sep_conj_com, erule sep_map'_conjE1, simp)

lemma sep_map'_any_conjE1:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. P s \<Longrightarrow> (i \<hookrightarrow>\<^sup>i\<^sub>g -) s \<rbrakk> \<Longrightarrow> (i \<hookrightarrow>\<^sup>i\<^sub>g -) s"
  by (subst sep_map'_any_unfold, erule sep_conj_impl, simp+)

lemma sep_map'_any_conjE2:
  "\<lbrakk> (P \<and>\<^sup>* Q) s; \<And>s. Q s \<Longrightarrow> (i \<hookrightarrow>\<^sup>i\<^sub>g -) s \<rbrakk> \<Longrightarrow> (i \<hookrightarrow>\<^sup>i\<^sub>g -) s"
  by (subst (asm) sep_conj_com, erule sep_map'_any_conjE1, simp)

lemma sep_map_any_old:
  "(p \<mapsto>\<^sup>i\<^sub>g -) = (\<lambda>s. \<exists>v. (p \<mapsto>\<^sup>i\<^sub>g v) s)"
  by (simp add: sep_map_inv_def sep_map_any_inv_def sep_map_any_def sep_conj_ac sep_conj_exists)

lemma sep_map'_old:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g v) = ((p \<mapsto>\<^sup>i\<^sub>g v) \<and>\<^sup>* sep_true)"
  by (simp add: sep_map'_inv_def sep_map_inv_def sep_map'_def sep_conj_ac)

lemma sep_map'_any_old:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g -) = (\<lambda>s. \<exists>v. (p \<hookrightarrow>\<^sup>i\<^sub>g v) s)"
  by (simp add: sep_map'_inv_def sep_map'_any_inv_def sep_map'_any_def sep_conj_exists)

lemma sep_map_sep_map' [simp]:
  "(p \<mapsto>\<^sup>i\<^sub>g v) s \<Longrightarrow> (p \<hookrightarrow>\<^sup>i\<^sub>g v) s"
  unfolding sep_map_inv_def sep_map'_inv_def sep_map'_def
  apply(simp add: sep_conj_ac)
  apply(subst sep_conj_com)
  apply(simp add: sep_conj_assoc sep_conj_impl sep_conj_sep_true)
  done

lemmas guardI = sep_map'_g[OF sep_map_sep_map']

lemma sep_map_anyI [simp]:
  "(p \<mapsto>\<^sup>i\<^sub>g v) s \<Longrightarrow> (p \<mapsto>\<^sup>i\<^sub>g -) s"
  by (fastforce simp: sep_map_any_inv_def sep_map_inv_def sep_map_any_def sep_conj_ac
                elim: sep_conj_impl)

lemma sep_map_anyD:
  "(p \<mapsto>\<^sup>i\<^sub>g -) s \<Longrightarrow> \<exists>v. (p \<mapsto>\<^sup>i\<^sub>g v) s"
  apply(simp add: sep_map_any_def sep_map_any_inv_def sep_map_inv_def sep_conj_ac)
  apply(subst (asm) sep_conj_com)
  apply(clarsimp simp: sep_conj_exists sep_conj_ac)
  done

lemma sep_conj_mapD:
  "((i \<mapsto>\<^sup>i\<^sub>g v) \<and>\<^sup>* P) s \<Longrightarrow> (i \<hookrightarrow>\<^sup>i\<^sub>g v) s \<and> ((i \<mapsto>\<^sup>i\<^sub>g -) \<and>\<^sup>* P) s"
  by (simp add: sep_conj_impl sep_map'_conjE2 sep_conj_ac)

lemma sep_map'_ptr_safe:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g (v::'a::mem_type)) (lift_state (h,d)) \<Longrightarrow> ptr_safe p d"
  unfolding sep_map'_inv_def
  apply(rule sep_map'_ptr_safe_exc)
  apply(subst sep_map'_unfold_exc)
  apply(fastforce elim: sep_conj_impl)
  done

lemmas sep_map_ptr_safe = sep_map'_ptr_safe[OF sep_map_sep_map']

lemma sep_map_any_ptr_safe:
  fixes p::"'a::mem_type ptr"
  shows "(p \<mapsto>\<^sup>i\<^sub>g -) (lift_state (h, d)) \<Longrightarrow> ptr_safe p d"
  by (blast dest: sep_map_anyD intro: sep_map_ptr_safe)

lemma sep_heap_update':
  "(g \<turnstile>\<^sub>s\<^sup>i p \<and>\<^sup>* (p \<mapsto>\<^sup>i\<^sub>g v \<longrightarrow>\<^sup>* P)) (lift_state (h,d)) \<Longrightarrow>
      P (lift_state (heap_update p (v::'a::mem_type) h,d))"
  apply(rule_tac g=g in sep_heap_update'_exc)
  apply(unfold tagd_inv_def)
  apply(subst (asm) sep_conj_assoc)+
  apply(erule (1) sep_conj_impl)
  apply(subst (asm) sep_map_inv_def)
  apply(simp add: sep_conj_ac)
  apply(drule sep_conjD, clarsimp)
  apply(rule sep_implI, clarsimp)
  apply(drule sep_implD)
  apply(drule_tac x="s\<^sub>0 ++ s'" in spec)
  apply(simp add: map_disj_com map_add_disj)
  apply(clarsimp simp: map_disj_com)
  apply(erule notE)
  apply(erule (1) sep_conjI)
   apply(simp add: map_disj_com)
  apply(subst map_add_com; simp)
  done

lemma tagd_g:
  "(g \<turnstile>\<^sub>s\<^sup>i p \<and>\<^sup>* P) s \<Longrightarrow> g p"
  by (auto simp: tagd_inv_def tagd_def dest!: sep_conjD elim: s_valid_g)

lemma tagd_ptr_safe:
  "(g \<turnstile>\<^sub>s\<^sup>i p \<and>\<^sup>* sep_true) (lift_state (h,d)) \<Longrightarrow> ptr_safe p d"
  apply(rule tagd_ptr_safe_exc)
  apply(unfold tagd_inv_def)
  apply(subst (asm) sep_conj_assoc)
  apply(erule (1) sep_conj_impl)
  apply simp
  done

lemma sep_map_tagd:
  "(p \<mapsto>\<^sup>i\<^sub>g (v::'a::mem_type)) s \<Longrightarrow> (g \<turnstile>\<^sub>s\<^sup>i p) s"
  apply(unfold sep_map_inv_def tagd_inv_def)
  apply(erule sep_conj_impl)
   apply(erule sep_map_tagd_exc)
  apply assumption
  done

lemma sep_map_any_tagd:
  "(p \<mapsto>\<^sup>i\<^sub>g -) s \<Longrightarrow> (g \<turnstile>\<^sub>s\<^sup>i (p::'a::mem_type ptr)) s"
  by (clarsimp dest!: sep_map_anyD, erule sep_map_tagd)

lemma sep_heap_update:
  "\<lbrakk> (p \<mapsto>\<^sup>i\<^sub>g - \<and>\<^sup>* (p \<mapsto>\<^sup>i\<^sub>g v \<longrightarrow>\<^sup>* P)) (lift_state (h,d)) \<rbrakk> \<Longrightarrow>
      P (lift_state (heap_update p (v::'a::mem_type) h,d))"
  by (force intro: sep_heap_update' dest: sep_map_anyD sep_map_tagd
            elim: sep_conj_impl)

lemma sep_heap_update_global':
  "(g \<turnstile>\<^sub>s\<^sup>i p \<and>\<^sup>* R) (lift_state (h,d)) \<Longrightarrow>
      ((p \<mapsto>\<^sup>i\<^sub>g v) \<and>\<^sup>* R) (lift_state (heap_update p (v::'a::mem_type) h,d))"
  by (rule sep_heap_update', erule sep_conj_sep_conj_sep_impl_sep_conj)

lemma sep_heap_update_global:
  "(p \<mapsto>\<^sup>i\<^sub>g - \<and>\<^sup>* R) (lift_state (h,d)) \<Longrightarrow>
      ((p \<mapsto>\<^sup>i\<^sub>g v) \<and>\<^sup>* R) (lift_state (heap_update p (v::'a::mem_type) h,d))"
  by (fast intro: sep_heap_update_global' sep_conj_impl sep_map_any_tagd)

lemma sep_heap_update_global_super_fl_inv:
  "\<lbrakk> (p \<mapsto>\<^sup>i\<^sub>g u \<and>\<^sup>* R) (lift_state (h,d));
      field_lookup (typ_info_t TYPE('b::mem_type)) f 0 = Some (t,n);
      export_uinfo t = (typ_uinfo_t TYPE('a)) \<rbrakk> \<Longrightarrow>
      ((p \<mapsto>\<^sup>i\<^sub>g update_ti_t t (to_bytes_p v) u) \<and>\<^sup>* R)
      (lift_state (heap_update (Ptr &(p\<rightarrow>f)) (v::'a::mem_type) h,d))"
  apply(unfold sep_map_inv_def)
  apply(simp only: sep_conj_assoc)
  apply(erule (2) sep_heap_update_global_super_fl)
  done

lemma sep_map'_inv:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g v) s \<Longrightarrow> (p \<hookrightarrow>\<^sub>g v) s"
  apply(unfold sep_map'_inv_def)
  apply(subst sep_map'_unfold_exc)
  apply(erule (1) sep_conj_impl, simp)
  done

lemma sep_map'_lift:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g (v::'a::mem_type)) (lift_state (h,d)) \<Longrightarrow> lift h p = v"
  apply(drule sep_map'_inv)
  apply(erule sep_map'_lift_exc)
  done

lemma sep_map_lift:
  "((p::'a::mem_type ptr) \<mapsto>\<^sup>i\<^sub>g -) (lift_state (h,d)) \<Longrightarrow>
        (p \<mapsto>\<^sup>i\<^sub>g lift h p) (lift_state (h,d))"
  apply(frule sep_map_anyD)
  apply clarsimp
  apply(frule sep_map_sep_map')
  apply(drule sep_map'_lift)
  apply simp
  done

lemma sep_map_lift_wp:
  "\<lbrakk> \<exists>v. (p \<mapsto>\<^sup>i\<^sub>g v \<and>\<^sup>* (p \<mapsto>\<^sup>i\<^sub>g v \<longrightarrow>\<^sup>* P v)) (lift_state (h,d)) \<rbrakk>
      \<Longrightarrow> P (lift h (p::'a::mem_type ptr)) (lift_state (h,d))"
  apply clarsimp
  apply(subst sep_map'_lift [where g=g and d=d])
   apply(subst sep_map'_inv_def)
   apply(subst sep_map'_def)
   apply(subst sep_conj_assoc)+
   apply(subst sep_conj_com[where P=sep_true])
   apply(subst sep_conj_assoc [symmetric])
   apply(erule sep_conj_impl)
    apply(simp add: sep_map_inv_def)
   apply simp
  apply(rule_tac P="p \<mapsto>\<^sup>i\<^sub>g v" and Q="P v" in sep_conj_impl_same)
  apply(unfold sep_map_inv_def)
  apply(erule (2) sep_conj_impl)
  done

lemma sep_map'_anyI [simp]:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g v) s \<Longrightarrow> (p \<hookrightarrow>\<^sup>i\<^sub>g -) s"
  apply(unfold sep_map'_inv_def sep_map'_any_inv_def)
  apply(erule sep_conj_impl)
   apply(erule sep_map'_anyI_exc)
  apply assumption
  done

lemma sep_map'_anyD:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g -) s \<Longrightarrow> \<exists>v. (p \<hookrightarrow>\<^sup>i\<^sub>g v) s"
  unfolding sep_map'_inv_def sep_map'_any_inv_def sep_map'_any_def
  by (clarsimp simp: sep_conj_exists)

lemma sep_map'_lift_rev:
  "\<lbrakk> lift h p = (v::'a::mem_type); (p \<hookrightarrow>\<^sup>i\<^sub>g -) (lift_state (h,d)) \<rbrakk> \<Longrightarrow>
      (p \<hookrightarrow>\<^sup>i\<^sub>g v) (lift_state (h,d))"
  by (fastforce dest: sep_map'_anyD simp: sep_map'_lift)

lemma sep_map'_any_g:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g -) s \<Longrightarrow> g p"
  by (blast dest: sep_map'_anyD intro: sep_map'_g)

lemma any_guardI:
  "(p \<mapsto>\<^sup>i\<^sub>g -) s \<Longrightarrow> g p"
  by (drule sep_map_anyD) (blast intro: guardI)

lemma sep_map_sep_map_any:
  "(p \<mapsto>\<^sup>i\<^sub>g v) s \<Longrightarrow> (p \<mapsto>\<^sup>i\<^sub>g -) s"
  by (rule sep_map_anyI)


lemma sep_lift_exists:
  fixes p :: "'a::mem_type ptr"
  assumes ex: "((\<lambda>s. \<exists>v. (p \<hookrightarrow>\<^sup>i\<^sub>g v) s \<and> P v s) \<and>\<^sup>* Q) (lift_state (h,d))"
  shows "(P (lift h p) \<and>\<^sup>* Q) (lift_state (h,d))"
proof -
  from ex obtain v where "((\<lambda>s. (p \<hookrightarrow>\<^sup>i\<^sub>g v) s \<and> P v s) \<and>\<^sup>* Q)
      (lift_state (h,d))"
    by (subst (asm) sep_conj_exists, clarsimp)
  thus ?thesis
    by (force simp: sep_map'_lift sep_conj_ac
              dest: sep_map'_conjE2 dest!: sep_conj_conj)
qed

lemma sep_map_dom:
  "(p \<mapsto>\<^sup>i\<^sub>g (v::'a::c_type)) s \<Longrightarrow> dom s = {(a,b). a \<in> {ptr_val p..+size_of TYPE('a)}}"
  unfolding sep_map_inv_def
  by (drule sep_conjD, clarsimp)
     (auto dest!: sep_map_dom_exc elim: s_footprintD simp: inv_footprint_def)

lemma sep_map'_dom:
  "(p \<hookrightarrow>\<^sup>i\<^sub>g (v::'a::mem_type)) s \<Longrightarrow> (ptr_val p,SIndexVal) \<in> dom s"
  unfolding sep_map'_inv_def
  by (drule sep_conjD, clarsimp) (drule sep_map'_dom_exc, clarsimp)

lemma sep_map'_inj:
  "\<lbrakk> (p \<hookrightarrow>\<^sup>i\<^sub>g (v::'a::c_type)) s; (p \<hookrightarrow>\<^sup>i\<^sub>h v') s \<rbrakk> \<Longrightarrow> v=v'"
  by (drule sep_map'_inv)+ (drule (2) sep_map'_inj_exc)

lemma ptr_retyp_sep_cut':
  fixes p::"'a::mem_type ptr"
  assumes sc: "(sep_cut' (ptr_val p) (size_of TYPE('a)) \<and>\<^sup>* P)
      (lift_state (h,d))" and "g p"
  shows "(g \<turnstile>\<^sub>s\<^sup>i p \<and>\<^sup>* P) (lift_state (h,(ptr_retyp p d)))"
proof -
  from sc
  obtain s\<^sub>0 and s\<^sub>1
    where "s\<^sub>0 \<bottom> s\<^sub>1" and "lift_state (h,d) = s\<^sub>1 ++ s\<^sub>0"
      and "P s\<^sub>1" and d: "dom s\<^sub>0 = {(a,b). a \<in> {ptr_val p..+size_of TYPE('a)}}"
      and k: "dom s\<^sub>0 \<subseteq> dom_s d"
    by (auto dest!: sep_conjD sep_cut'_dom simp: dom_lift_state_dom_s [where h=h,symmetric])
  moreover from this
  have "lift_state (h, ptr_retyp p d) = s\<^sub>1 ++ lift_state (h, ptr_retyp p d) |` (dom s\<^sub>0)"
    apply -
    apply(rule ext, rename_tac x)
    apply(case_tac "x \<in> dom s\<^sub>0")
     apply(case_tac "x \<in> dom s\<^sub>1")
      apply(fastforce simp: map_disj_def)
     apply(subst map_add_com)
      apply(fastforce simp: map_disj_def)
     apply(clarsimp simp: map_add_def split: option.splits)
    apply(case_tac x, clarsimp)
    apply(clarsimp simp: lift_state_ptr_retyp_d merge_dom2)
    done
  moreover have "g p" by fact
  with d k have "(g \<turnstile>\<^sub>s\<^sup>i p) (lift_state (h, ptr_retyp p d) |` dom s\<^sub>0)"
    apply(clarsimp simp: lift_state_ptr_retyp_restrict sep_conj_ac tagd_inv_def)
    apply(rule_tac s\<^sub>0="lift_state (h,d) |` ({(a, b). a \<in> {ptr_val p..+size_of TYPE('a)}} - s_footprint p)"
                   in sep_conjI)
       apply(fastforce simp: inv_footprint_def)
      apply(erule_tac h=h in ptr_retyp_tagd_exc)
     apply(fastforce  simp: map_disj_def)
    apply(subst map_add_comm[of "lift_state (h, ptr_retyp p empty_htd)"])
     apply force
    apply(rule ext)
    apply(clarsimp simp: map_add_def split: option.splits)
    by (metis (mono_tags) Diff_iff dom_ptr_retyp_empty_htd non_dom_eval_eq restrict_in_dom restrict_out)
  ultimately show ?thesis
    by - (rule_tac s\<^sub>0="(lift_state (h,ptr_retyp p d))|`dom s\<^sub>0" and s\<^sub>1=s\<^sub>1 in sep_conjI,
          auto simp: map_disj_def)
qed

lemma ptr_retyp_sep_cut'_wp:
  "\<lbrakk> (sep_cut' (ptr_val p) (size_of TYPE('a)) \<and>\<^sup>* (g \<turnstile>\<^sub>s\<^sup>i p \<longrightarrow>\<^sup>* P))
      (lift_state (h,d)); g (p::'a::mem_type ptr) \<rbrakk>
      \<Longrightarrow> P (lift_state (h,(ptr_retyp p d)))"
  by (rule_tac P="g \<turnstile>\<^sub>s\<^sup>i p" and Q=P in sep_conj_impl_same) (simp add: ptr_retyp_sep_cut')

lemma tagd_dom:
  "(g \<turnstile>\<^sub>s\<^sup>i p) s \<Longrightarrow> dom s = {(a,b). a \<in> {ptr_val (p::'a::c_type ptr)..+size_of TYPE('a)}}"
  unfolding tagd_inv_def
  by (drule sep_conjD, clarsimp)
     (auto simp: inv_footprint_def dest!: tagd_dom_exc elim: s_footprintD)

lemma tagd_dom_p:
  "(g \<turnstile>\<^sub>s\<^sup>i p) s \<Longrightarrow> (ptr_val (p::'a::mem_type ptr),SIndexVal) \<in> dom s"
  by (drule tagd_dom) clarsimp


end
