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

theory SepCode
imports
  Separation
  "../Simpl/Vcg"
begin

definition
  singleton_t :: "'a::c_type ptr \<Rightarrow> 'a \<Rightarrow> heap_state"
where
  "singleton_t p v \<equiv> lift_state (heap_update p v (\<lambda>x. 0), (ptr_retyp p empty_htd))"

definition
  tagd :: "'a ptr_guard \<Rightarrow> 'a::c_type ptr \<Rightarrow> heap_assert" (infix "\<turnstile>\<^sub>s" 100)
where
  "g \<turnstile>\<^sub>s p \<equiv> \<lambda>s. s,g \<Turnstile>\<^sub>s p \<and> dom s = s_footprint p"

definition
  field_footprint :: "'a::c_type ptr \<Rightarrow> qualified_field_name \<Rightarrow> (addr \<times> s_heap_index) set"
where
  "field_footprint p f \<equiv> s_footprint_untyped (ptr_val p + of_nat (field_offset TYPE('a) f)) (export_uinfo (field_typ TYPE('a) f))"

definition
  fs_footprint :: "'a::c_type ptr \<Rightarrow> qualified_field_name set \<Rightarrow> (addr \<times> s_heap_index) set"
where
  "fs_footprint p F \<equiv> \<Union>{field_footprint p f | f. f \<in> F}"

definition fields :: "'a::c_type itself \<Rightarrow> qualified_field_name set" where
  "fields t \<equiv> {f. field_lookup (typ_info_t TYPE('a)) f 0 \<noteq> None}"

definition
  mfs_sep_map :: "'a::c_type ptr \<Rightarrow> 'a ptr_guard \<Rightarrow> qualified_field_name set \<Rightarrow> 'a \<Rightarrow> heap_assert"
  ("_ \<mapsto>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _" [56,0,0,51] 56)
where
  "p \<mapsto>\<^bsub>g\<^esub>\<^bsup>F\<^esup> v \<equiv> \<lambda>s. lift_typ_heap g (singleton_t p v ++ s) p = Some v \<and>
      F \<subseteq> fields TYPE('a) \<and>
      dom s = s_footprint p - fs_footprint p F \<and> wf_heap_val s"

notation (input)
  mfs_sep_map ("_ \<mapsto>\<^sub>_\<^sup>_ _" [56,0,1000,51] 56)

definition
  disjoint_fn :: "qualified_field_name \<Rightarrow> qualified_field_name set \<Rightarrow> bool"
where
  "disjoint_fn f F \<equiv> \<forall>f'\<in>F. \<not> f \<le> f' \<and> \<not> f' \<le> f"

definition
  sep_cut' :: "addr \<Rightarrow> nat \<Rightarrow> (s_addr,'b) map_assert"
where
  "sep_cut' p n \<equiv> \<lambda>s. dom s = {(x,y). x \<in> {p..+n}}"

definition
  sep_cut :: "addr \<Rightarrow> addr_bitsize word \<Rightarrow> (s_addr,'b) map_assert"
where
  "sep_cut x y \<equiv> sep_cut' x (unat y)"

text {* ---- *}

(* FIXME MOVE *)
lemma heap_list_h_eq:
  "\<And>p. \<lbrakk> x \<in> {p..+q}; q < addr_card; heap_list h q p = heap_list h' q p \<rbrakk>
      \<Longrightarrow> h x = h' x"
proof (induct q)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case by (force dest: intvl_neq_start)
qed

lemma s_footprint_intvl:
  "(a, SIndexVal) \<in> s_footprint p = (a \<in> {ptr_val (p::'a::c_type ptr)..+size_of TYPE('a)})"
apply(auto simp: s_footprint_def s_footprint_untyped_def)
 apply(rule intvlI)
 apply(simp add: size_of_def)
apply(drule intvlD, clarsimp)
apply(simp add: size_of_def)
apply fast
done

lemma singleton_t_dom [simp]:
  "dom (singleton_t p (v::'a::mem_type)) = s_footprint p"
apply(auto simp: singleton_t_def lift_state_def s_footprint_intvl split: s_heap_index.splits  if_split_asm option.splits)
apply(rule ccontr)
   apply(simp add: ptr_retyp_None)
  prefer 2
  apply(simp add: ptr_retyp_footprint)
 prefer 2
 apply(frule s_footprintD2)
 apply(frule s_footprintD)
 apply(simp add: ptr_retyp_footprint)
apply(case_tac "a \<in> {ptr_val p..+size_of TYPE('a)}")
 apply(simp add: ptr_retyp_footprint)
 apply(simp add: list_map_eq split: if_split_asm)
 apply(drule intvlD, clarsimp)
 apply(rule s_footprintI)
  apply(subst (asm) word_unat.eq_norm)
  apply(subst (asm) mod_less)
  apply(subst len_of_addr_card)
  apply(erule less_trans)
  apply(rule max_size)
  apply(simp add: map_le_def)
 apply assumption
apply(simp add: ptr_retyp_None)
done

lemma heap_update_merge:
  assumes val: "d,g \<Turnstile>\<^sub>t p"
  shows "lift_state ((heap_update p (v::'a::mem_type) h),d)
            = lift_state (h,d) ++ singleton p v h d" (is "?x = ?y")
proof (rule ext, cases)
  fix x
  assume c: "x \<in> dom (singleton p v h d)"
  with val have "lift_state ((heap_update_list (ptr_val p)
      (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p))) h),d) x = singleton p v h d x"
apply(subst (asm) singleton_dom)
 apply fast
apply(cases x)
apply(auto simp: heap_list_update_to_bytes singleton_def lift_state_def
                    heap_update_def
                split: option.splits s_heap_index.splits)
done
  with c show "?x x = ?y x" by (force simp: heap_update_def dest: domD)
next
  fix x
  assume nc: "x \<notin> dom (singleton p v h d)"
  with val show "?x x = ?y x"
apply -
apply(cases x)
apply(auto simp: lift_state_def heap_update_def map_add_def split: option.splits s_heap_index.splits)
apply(rule heap_update_nmem_same)
apply clarsimp
apply(subgoal_tac "(a,SIndexVal) \<in> dom (singleton p v h d)")
 apply fast
apply(simp add: singleton_dom)
apply(drule intvlD, clarsimp)
apply(rule s_footprintI2)
apply simp
done
qed

lemma tagd_dom_exc:
  "(g \<turnstile>\<^sub>s p) s \<Longrightarrow> dom s = s_footprint p"
  by (clarsimp simp: tagd_def)

lemma tagd_dom_p_exc:
  "(g \<turnstile>\<^sub>s p) s \<Longrightarrow> (ptr_val (p::'a::mem_type ptr),SIndexVal) \<in> dom s"
apply(drule tagd_dom_exc)
apply(clarsimp)
done

lemma tagd_g_exc:
  "(g \<turnstile>\<^sub>s p \<and>\<^sup>* P) s \<Longrightarrow> g p"
  by (drule sep_conjD, force simp: tagd_def elim: s_valid_g)

lemma sep_map_tagd_exc:
  "(p \<mapsto>\<^sub>g (v::'a::mem_type)) s \<Longrightarrow> (g \<turnstile>\<^sub>s p) s"
  by (clarsimp simp: sep_map_def tagd_def lift_typ_heap_s_valid)

lemma sep_map_any_tagd_exc:
  "(p \<mapsto>\<^sub>g -) s \<Longrightarrow> (g \<turnstile>\<^sub>s (p::'a::mem_type ptr)) s"
  by (clarsimp dest!: sep_map_anyD_exc, erule sep_map_tagd_exc)

lemma ptr_retyp_tagd_exc:
  "g (p::'a::mem_type ptr) \<Longrightarrow>
      (g \<turnstile>\<^sub>s p) (lift_state (h, ptr_retyp p empty_htd))"
apply(simp add: tagd_def ptr_retyp_s_valid lift_state_dom)
apply(auto simp: lift_state_def split: s_heap_index.splits if_split_asm option.splits)
   apply(case_tac "a \<in> {ptr_val p..+size_of TYPE('a)}")
    apply(drule intvlD, clarsimp)
    apply(rule s_footprintI2, simp)
   apply(subst (asm) ptr_retyp_None)
    apply simp+
  apply(case_tac "a \<in> {ptr_val p..+size_of TYPE('a)}")
   apply(subst (asm) ptr_retyp_footprint)
    apply simp
   apply(drule intvlD, clarsimp)
   apply(subst (asm )word_unat.eq_norm)
   apply(subst (asm) mod_less)
    apply(subst len_of_addr_card)
    apply(erule less_trans)
    apply simp
   apply(subst (asm) list_map_eq)
   apply(clarsimp split: if_split_asm)
   apply(erule (1) s_footprintI)
  apply(simp add: ptr_retyp_None)
 apply(case_tac "a \<in> {ptr_val p..+size_of TYPE('a)}")
  apply(simp add: ptr_retyp_footprint)
 apply(drule s_footprintD)
 apply simp
apply(case_tac "a \<in> {ptr_val p..+size_of TYPE('a)}")
 apply(subst (asm) ptr_retyp_footprint)
  apply simp
 apply(drule intvlD, clarsimp)
 apply(subst (asm )word_unat.eq_norm)
 apply(subst (asm) mod_less)
  apply(subst len_of_addr_card)
  apply(erule less_trans)
  apply simp
 apply(subst (asm) list_map_eq)
 apply(clarsimp split: if_split_asm)
 apply(drule s_footprintD2)
 apply simp
 apply(subst (asm) unat_of_nat)
 apply(subst (asm) mod_less)
  apply(subst len_of_addr_card)
  apply(erule less_trans, simp)
 apply simp
apply(drule s_footprintD)
apply simp
done

lemma singleton_dom_proj_d [simp]:
  "(g \<turnstile>\<^sub>s p) s \<Longrightarrow> dom (singleton p (v::'a::mem_type) h (proj_d s)) = dom s"
apply(clarsimp simp: tagd_def)
apply(subst singleton_dom)
 apply(simp add: s_valid_def)+
done

lemma singleton_d_restrict_eq:
  "restrict_s d (s_footprint p) = restrict_s d' (s_footprint p)
      \<Longrightarrow> singleton p v h d = singleton p (v::'a::mem_type) h d'"
apply(clarsimp simp: singleton_def)
apply(rule ext)
apply(case_tac "x \<in> s_footprint p")
 prefer 2 apply simp
apply(case_tac x, clarsimp)
apply(drule_tac x=aa in fun_cong)
apply(auto simp: s_footprint_restrict lift_state_def
           split: s_heap_index.splits if_split_asm option.splits) (* FIXME! *)
      apply(clarsimp simp: restrict_s_def)
     apply(clarsimp simp: restrict_s_def)
    apply(clarsimp simp: restrict_s_def)
    apply(drule_tac x="x2" in fun_cong)
    apply clarsimp
   apply(clarsimp simp: restrict_s_def)
   apply(drule_tac x="x2" in fun_cong)
   apply clarsimp
  apply(clarsimp simp: restrict_s_def)
  apply(drule_tac x="x2" in fun_cong)
  apply clarsimp
 apply(clarsimp simp: restrict_s_def)
 apply(drule_tac x="x2" in fun_cong)
 apply clarsimp
apply(clarsimp simp: restrict_s_def)
apply(drule_tac x="x2" in fun_cong)
apply clarsimp
done


lemma sep_heap_update'_exc:
  assumes sep: "(g \<turnstile>\<^sub>s p \<and>\<^sup>* (p \<mapsto>\<^sub>g v \<longrightarrow>\<^sup>* P)) (lift_state (h,d))"
  shows "P (lift_state (heap_update p (v::'a::mem_type) h,d))"
proof -
  from sep obtain s\<^sub>0 s\<^sub>1 where disj: "s\<^sub>0 \<bottom> s\<^sub>1" and
      merge: "lift_state (h,d) = s\<^sub>1 ++ s\<^sub>0" and
      l: "(g \<turnstile>\<^sub>s p) s\<^sub>0" and r: "(p \<mapsto>\<^sub>g v \<longrightarrow>\<^sup>* P) s\<^sub>1" by (force dest: sep_conjD)
  moreover hence "s\<^sub>1 \<bottom> singleton p v h (proj_d s\<^sub>0)"
apply(clarsimp simp: map_disj_def)
apply fast
done
  moreover from l have "g p" by (force simp: tagd_def elim: s_valid_g)
  moreover from merge l have "lift_state (h,d),g \<Turnstile>\<^sub>s p"
    by (force simp: tagd_def intro: s_valid_heap_merge_right)
  hence "d,g \<Turnstile>\<^sub>t p" by (simp add: h_t_s_valid)
  moreover from l have "s\<^sub>0 ++ singleton p v h (proj_d s\<^sub>0) = singleton p v h (proj_d s\<^sub>0)"
    by (force simp: map_add_dom_eq singleton_dom dest: tagd_dom_exc)
  moreover from l merge have "s\<^sub>1 ++ singleton p v h (proj_d s\<^sub>0) = s\<^sub>1 ++ s\<^sub>0 ++ singleton p v h d"
apply -
apply(clarsimp simp: tagd_def)
apply(rule ext)
apply(case_tac x, clarsimp simp: restrict_map_def)
apply(simp add: s_valid_def)
apply(drule_tac v=v and h=h in singleton_dom)
apply(drule_tac x="(aa,ba)" in fun_cong)
apply(case_tac "(aa,ba) \<in> s_footprint p")
 apply(subgoal_tac "(s\<^sub>1 ++ singleton p v h (proj_d s\<^sub>0)) (aa, ba) = singleton p v h d (aa, ba)")
  apply(clarsimp simp: map_add_def s_valid_def split: option.splits)
   apply force
  apply(rule exI, rule sym, assumption)
 apply(clarsimp simp: map_add_def split: option.splits)
  apply(force)
 apply(rule, clarsimp)
  apply force
 apply clarsimp
 apply(clarsimp simp: lift_state_def map_add_def  split: option.splits s_heap_index.splits if_split_asm)
  apply(clarsimp simp: singleton_def lift_state_def split: if_split_asm)
 apply(clarsimp simp: singleton_def lift_state_def split: if_split_asm option.splits)
 apply(clarsimp simp: proj_d_def)
apply(auto simp: map_add_def singleton_def split: option.splits)
done
  ultimately show ?thesis
apply -
apply(drule sep_implD, drule_tac x="singleton p v h (proj_d s\<^sub>0)" in spec)
apply clarsimp
apply(subst heap_update_merge)
 apply fast
apply(subst (asm) sep_map_singleton)
 apply(clarsimp simp: tagd_def s_valid_def)
apply clarsimp
done
qed

lemma sep_heap_update_exc:
  "\<lbrakk> (p \<mapsto>\<^sub>g - \<and>\<^sup>* (p \<mapsto>\<^sub>g v \<longrightarrow>\<^sup>* P)) (lift_state (h,d)) \<rbrakk> \<Longrightarrow>
      P (lift_state (heap_update p (v::'a::mem_type) h,d))"
  by (force intro: sep_heap_update'_exc dest: sep_map_anyD_exc sep_map_tagd_exc
            elim: sep_conj_impl)

lemma sep_heap_update_global'_exc:
  "(g \<turnstile>\<^sub>s p \<and>\<^sup>* R) (lift_state (h,d)) \<Longrightarrow>
      ((p \<mapsto>\<^sub>g v) \<and>\<^sup>* R) (lift_state (heap_update p (v::'a::mem_type) h,d))"
  by (rule sep_heap_update'_exc, erule sep_conj_sep_conj_sep_impl_sep_conj)

lemma sep_heap_update_global_exc:
  "(p \<mapsto>\<^sub>g - \<and>\<^sup>* R) (lift_state (h,d)) \<Longrightarrow>
      ((p \<mapsto>\<^sub>g v) \<and>\<^sup>* R) (lift_state (heap_update p (v::'a::mem_type) h,d))"
  by (fast intro: sep_heap_update_global'_exc sep_conj_impl sep_map_any_tagd_exc)

lemma sep_heap_update_global_exc2:
  "(p \<mapsto>\<^sub>g u \<and>\<^sup>* R) (lift_state (h,d)) \<Longrightarrow>
      ((p \<mapsto>\<^sub>g v) \<and>\<^sup>* R) (lift_state (heap_update p (v::'a::mem_type) h,d))"
apply(rule sep_heap_update_global_exc)
apply(subst sep_map_any_def)
apply(subst sep_conj_exists)
apply fast
done

lemma heap_update_mem_same_point [rule_format]:
  "\<forall>p h h'. q \<in> {p..+length v} \<longrightarrow> length v < addr_card \<longrightarrow>
      heap_update_list p v h q = v ! unat (q - p)"
apply(induct_tac v)
 apply simp
apply clarsimp
apply(case_tac "p=q")
 apply simp
 apply(subst heap_update_list_same [where k=1, simplified])
  apply simp
 apply simp
apply(drule_tac x="p+1" in spec)
apply(erule impE)
 apply(drule (1) intvl_neq_start)
 apply simp
apply simp
apply(subgoal_tac "unat (q - p) = unat (1::32 word) + unat (q - (p + 1))")
 apply(simp)
apply(subgoal_tac "q - (p + 1) = (q-p) - 1")
 apply(simp only:)
apply(subst unat_minus_one)
  apply simp+
 apply(subgoal_tac "unat (q - p) \<noteq> 0")
  apply simp
 apply clarsimp
 apply(subst unat_gt_0)
 apply simp+
done

lemma heap_update_list_value:
  "length v < addr_card \<Longrightarrow>
   heap_update_list p v h q =
   (if q \<in> {p..+length v} then v!unat (q-p) else h q)"
by (auto simp add: heap_update_nmem_same heap_update_mem_same_point
            split: if_split)

lemma heap_update_list_value':
  "length xs < addr_card \<Longrightarrow>
   heap_update_list ptr xs hp x
      = (if unat (x - ptr) < length xs
           then xs ! unat (x - ptr)
           else hp x)"
apply (simp only: heap_update_list_value addr_card_def card_word)
apply (rule if_cong)
  apply simp_all
apply (rule iffI)
 apply (drule intvlD, clarsimp simp add: unat_of_nat)
apply (simp add: intvl_def unat_arith_simps(4) unat_of_nat split: if_split_asm)
 apply (rule_tac x="unat x - unat ptr" in exI, simp)
apply (rule_tac x="unat x + 2^addr_bitsize - unat ptr" in exI)
apply (cut_tac x=ptr in unat_lt2p)
apply (simp add: unat_arith_simps unat_of_nat)
done

lemma heap_list_h_eq2 [rule_format]:
  "\<forall>p. (\<forall>x. x \<in> {p..+n} \<longrightarrow> h x = h' x) \<longrightarrow>
    heap_list h n p = heap_list h' n p"
apply(induct_tac n)
 apply simp
apply clarsimp
apply rule
 apply(thin_tac "All P" for P)
 apply(drule_tac x=p in spec)
 apply(erule impE)
  apply(rule intvl_self)
  apply simp+
apply(drule_tac x="p+1" in spec)
apply(erule impE)
 apply clarsimp
 apply(drule_tac x=x in spec)
 apply(erule impE)
  apply(rule intvl_plus_sub_Suc)
  apply simp+
done

lemma map_td_f_eq':
  "(f=g) \<longrightarrow> (map_td f t = map_td g t)"
  "(f=g) \<longrightarrow> (map_td_struct f st = map_td_struct g st)"
  "(f=g) \<longrightarrow> (map_td_list f ts = map_td_list g ts)"
  "(f=g) \<longrightarrow> (map_td_pair f x = map_td_pair g x)"
apply(induct t and st and ts and x)
     apply auto
done

lemma map_td_f_eq:
  "f=g \<Longrightarrow> map_td f t = map_td g t"
  by (erule arg_cong)

lemma sep_map'_lift_exc:
  "(p \<hookrightarrow>\<^sub>g (v::'a::mem_type)) (lift_state (h,d)) \<Longrightarrow> lift h p = v"
  by - (frule sep_map'_lift_typ_heapD, simp add: lift_t lift_t_lift)

lemma sep_map_lift_wp_exc:
  "\<lbrakk> \<exists>v. (p \<mapsto>\<^sub>g v \<and>\<^sup>* (p \<mapsto>\<^sub>g v \<longrightarrow>\<^sup>* P v)) (lift_state (h,d)) \<rbrakk>
      \<Longrightarrow> P (lift h (p::'a::mem_type ptr)) (lift_state (h,d))"
apply clarsimp
apply(subst sep_map'_lift_exc)
 apply(subst sep_map'_def)
 apply(erule sep_conj_impl)
  apply assumption
 apply simp
apply(rule_tac P="p \<mapsto>\<^sub>g v" and Q="P v" in sep_conj_impl_same)
apply(erule (2) sep_conj_impl)
done


lemma sep_map_lift_exc:
  "((p::'a::mem_type ptr) \<mapsto>\<^sub>g -) (lift_state (h,d)) \<Longrightarrow>
      (p \<mapsto>\<^sub>g lift h p) (lift_state (h,d))"
 by (clarsimp simp: sep_map_any_def)
    (frule sep_map_sep_map'_exc, drule sep_map'_lift_exc, simp)

lemma sep_map'_lift_rev_exc:
  "\<lbrakk> lift h p = (v::'a::mem_type); (p \<hookrightarrow>\<^sub>g -) (lift_state (h,d)) \<rbrakk> \<Longrightarrow>
      (p \<hookrightarrow>\<^sub>g v) (lift_state (h,d))"
  by (clarsimp simp: sep_map'_any_def)
     (frule sep_map'_lift_exc, simp)

(* FIXME: can be made more flexible when generalised separation conjunction
   is added *)
lemma sep_lift_exists_exc:
  fixes p :: "'a::mem_type ptr"
  assumes ex: "((\<lambda>s. \<exists>v. (p \<hookrightarrow>\<^sub>g  v) s \<and> P v s) \<and>\<^sup>* Q) (lift_state (h,d))"
  shows "(P (lift h p) \<and>\<^sup>* Q) (lift_state (h,d))"
proof -
  from ex obtain v where "((\<lambda>s. (p \<hookrightarrow>\<^sub>g  v) s \<and> P v s) \<and>\<^sup>* Q)
      (lift_state (h,d))"
    by (subst (asm) sep_conj_exists, clarsimp)
  thus ?thesis
    by (force simp: sep_map'_lift_exc sep_conj_ac
        dest: sep_map'_conjE2_exc dest!: sep_conj_conj)
qed

lemma merge_dom:
  "x \<in> dom s \<Longrightarrow> (t ++ s) x = s x"
  by (force simp: map_add_def)

lemma merge_dom2:
  "x \<notin> dom s \<Longrightarrow> (t ++ s) x = t x"
  by (force simp: map_add_def split: option.splits)

lemma fs_footprint_empty [simp]:
  "fs_footprint p {} = {}"
  by (auto simp: fs_footprint_def)

lemma fs_footprint_un:
  "fs_footprint p (insert f F) = fs_footprint p {f} \<union> fs_footprint p F"
  by (auto simp: fs_footprint_def)

lemma proj_d_restrict_map_le:
  "snd (proj_d (s |` X) x) \<subseteq>\<^sub>m snd (proj_d s x)"
apply(clarsimp simp: map_le_def proj_d_def restrict_map_def
               split: option.splits if_split_asm)
done

lemma SIndexVal_conj_setcomp_simp [simp]:
  "{x. snd x = SIndexVal \<and> x \<notin> s_footprint_untyped p t}
      = {(x,SIndexVal) | x. x \<notin> {p..+size_td t}}"
apply(auto simp: s_footprint_untyped_def)
 apply(drule intvlD, clarsimp)
 apply force
apply(erule notE)
apply(erule intvlI)
done

lemma heap_list_s_restrict_same [rule_format]:
  "\<forall>p. {(x,SIndexVal) | x. x \<in> {p..+n}} \<subseteq> X \<longrightarrow> heap_list_s (s |` X) n p = heap_list_s s n p"
apply(induct_tac n)
 apply(simp add: heap_list_s_def)
apply(clarsimp simp: heap_list_s_def)
apply rule
 apply(simp add: proj_h_def restrict_map_def)
 apply clarsimp
 apply(subgoal_tac "p \<in> {p..+Suc n}")
  apply fast
 apply(rule intvl_self)
 apply simp
apply(drule_tac x="p+1" in spec)
apply clarsimp
apply(subgoal_tac "{p + 1..+n} \<subseteq> {p..+Suc n}")
 apply fast
apply clarsimp
apply(rule intvl_plus_sub_Suc)
apply simp
done

lemma heap_list_s_restrict_fs_footprint:
  "field_lookup (typ_info_t TYPE('a::c_type)) f 0 = Some (t,n) \<Longrightarrow>
      heap_list_s (s |` fs_footprint p {f}) (size_td t) &(p\<rightarrow>f)
          = heap_list_s s (size_td t) &((p::'a ptr)\<rightarrow>f)"
apply(simp add: fs_footprint_def field_footprint_def field_offset_def)
apply(subst heap_list_s_restrict_same)
 apply(clarsimp simp add: s_footprint_untyped_def field_size_def field_lvalue_def field_offset_def field_ti_def)
 apply(drule intvlD, clarsimp)
  apply(simp add: field_typ_def field_typ_untyped_def)
  apply fast
apply simp
done

lemma heap_list_proj_h_disj [rule_format]:
  "\<forall>p. {(x,SIndexVal) | x. x \<in> {p..+n}} \<inter> dom s\<^sub>1 = {} \<longrightarrow>
      heap_list (proj_h (s\<^sub>0 ++ s\<^sub>1)) n p = heap_list (proj_h s\<^sub>0) n p"
apply(induct_tac n)
 apply simp
apply clarsimp
apply rule
 apply(clarsimp simp: proj_h_def split: option.splits)
 apply(rule, clarsimp)
  apply(subgoal_tac "p \<in> {p..+Suc n}")
   apply fast
  apply(rule intvl_self, simp)
 apply clarsimp
 apply(erule disjE)
  apply(subgoal_tac "p \<in> {p..+Suc n}")
   apply fast
  apply(rule intvl_self, simp)
 apply clarsimp
apply(drule_tac x="p+1" in spec)
 apply(erule impE)
 apply(subgoal_tac "{p + 1..+n} \<subseteq> {p..+Suc n}")
   apply fast
 apply clarsimp
 apply(rule intvl_plus_sub_Suc)
 apply simp
apply simp
done

lemma heap_list_proj_h_sub [rule_format]:
  "\<forall>p. {(x,SIndexVal) | x. x \<in> {p..+n}} \<subseteq> dom s\<^sub>1 \<longrightarrow>
      heap_list (proj_h (s\<^sub>0 ++ s\<^sub>1)) n p = heap_list (proj_h s\<^sub>1) n p"
apply(induct_tac n)
 apply simp
apply clarsimp
apply rule
 apply(clarsimp simp: proj_h_def split: option.splits)
 apply(subgoal_tac "p \<in> {p..+Suc n}")
  apply force
 apply(rule intvl_self, simp)
apply(drule_tac x="p+1" in spec)
 apply(erule impE)
 apply(subgoal_tac "{p + 1..+n} \<subseteq> {p..+Suc n}")
   apply fast
 apply clarsimp
 apply(rule intvl_plus_sub_Suc)
 apply simp
apply simp
done


lemma heap_list_s_map_add_super_update_bs:
  "\<lbrakk> {x. (x,SIndexVal) \<in> dom s\<^sub>1} = {p+of_nat k..+z}; k + z \<le> n; n < addr_card \<rbrakk>
      \<Longrightarrow> heap_list_s (s\<^sub>0 ++ s\<^sub>1) n p = super_update_bs (heap_list_s s\<^sub>1 z (p+of_nat k)) (heap_list_s s\<^sub>0 n p) k"
apply(auto simp: super_update_bs_def heap_list_s_def)
apply(subgoal_tac "heap_list (proj_h (s\<^sub>0 ++ s\<^sub>1)) (k + z + (n - (k+z))) p =
       take k (heap_list (proj_h s\<^sub>0) n p) @
       heap_list (proj_h s\<^sub>1) z (p + of_nat k) @
       drop (k + z) (heap_list (proj_h s\<^sub>0) n p)")
 apply simp
apply(subst heap_list_split2)
apply(subst heap_list_split2)
apply simp
apply rule
 apply(subst take_heap_list_le)
  apply simp
 apply(subst heap_list_proj_h_disj)
  apply(insert init_intvl_disj [of k z p])
  apply simp
  apply fast
 apply simp
apply rule
 apply(subst heap_list_proj_h_sub)
  apply fast
 apply simp
apply(subst drop_heap_list_le)
 apply simp
apply simp
apply(subst heap_list_proj_h_disj)
 apply(insert final_intvl_disj [of k z n p])
 apply fast
apply simp
done

lemma s_footprint_untyped_dom_SIndexVal:
  "dom s = s_footprint_untyped p t \<Longrightarrow>
      {x. (x,SIndexVal) \<in> dom s} = {p..+size_td t}"
apply(clarsimp simp: s_footprint_untyped_def)
apply auto
 apply(erule intvlI)
apply(drule intvlD, force)
done

lemma field_ti_s_sub:
  "field_lookup (export_uinfo (typ_info_t TYPE('b::mem_type))) f 0 = Some (a,b) \<Longrightarrow>
      s_footprint_untyped &(p\<rightarrow>f) a \<subseteq> s_footprint (p::'b ptr)"
apply(clarsimp simp: field_ti_def s_footprint_def s_footprint_untyped_def split: option.splits)
apply(simp add: field_lvalue_def field_offset_def typ_uinfo_t_def)
apply(rule_tac x="b+x" in exI)
apply simp
apply(simp add: field_offset_untyped_def)
apply(drule td_set_field_lookupD)
apply(frule td_set_offset_size)
apply(drule_tac k=x in typ_slice_td_set)
apply simp
apply(auto simp: prefix_def less_eq_list_def)
done

lemma wf_heap_val_map_add [simp]:
  "\<lbrakk> wf_heap_val s\<^sub>0; wf_heap_val s\<^sub>1 \<rbrakk> \<Longrightarrow> wf_heap_val (s\<^sub>0 ++ s\<^sub>1)"
apply(unfold wf_heap_val_def)
apply auto
done

lemma of_nat_lt_size_of:
  "\<lbrakk> ((of_nat x)::addr) = of_nat y + of_nat z; x < size_of TYPE('a::mem_type);
      y + z < size_of TYPE('a) \<rbrakk> \<Longrightarrow> x = y+z"
apply(subst (asm) Abs_fnat_homs)
apply(subst (asm) word_unat.norm_eq_iff [symmetric])
apply(simp only: len_of_addr_card)
apply(subst (asm) mod_less)
 apply(erule less_trans)
 apply simp
apply(subst (asm) mod_less)
 apply(erule less_trans)
 apply simp+
done

lemma proj_d_map_add:
  "snd (proj_d s\<^sub>1 p) n = Some k \<Longrightarrow> snd (proj_d (s\<^sub>0 ++ s\<^sub>1) p) n = Some k"
apply(auto simp: proj_d_def split: option.splits)
done

lemma proj_d_map_add2:
  "fst (proj_d s\<^sub>1 p) \<Longrightarrow> fst (proj_d (s\<^sub>0 ++ s\<^sub>1) p)"
apply(auto simp: proj_d_def split: option.splits)
done


lemma heap_list_s_restrict_disj_same [rule_format]:
  "\<forall>p. dom s \<inter> (UNIV - X) = {} \<longrightarrow> heap_list_s (s |` X) n p = heap_list_s s n p"
apply(induct_tac n)
 apply(simp add: heap_list_s_def)
apply(clarsimp simp: heap_list_s_def)
apply(simp add: proj_h_def restrict_map_def split: option.splits)
apply clarsimp
apply fast
done

lemma UNIV_minus_inter:
  "(X - Y) \<inter> (X \<inter> (X - Y) - Z) = X - (Y \<union> Z)"
apply fast
done

lemma restrict_un_map:
  "f |` (X \<union> Y) = f |` X |` Y"
apply(auto simp add: restrict_map_def)
apply(rule ext)
apply auto
oops

lemma sep_map_mfs_sep_map_empty:
  "(p \<mapsto>\<^sub>g (v::'a::mem_type)) = (p \<mapsto>\<^sub>g\<^sup>({}) v)"
  by (auto simp: sep_map_def mfs_sep_map_def map_add_dom_eq)

lemma fd_cons_double_update:
  "\<lbrakk> fd_cons t; length bs = length  bs' \<rbrakk> \<Longrightarrow>
      update_ti_t t bs (update_ti_t t bs' v) = update_ti_t t bs v"
apply(simp add: fd_cons_def Let_def fd_cons_double_update_def fd_cons_desc_def)
done

lemma fd_cons_update_access:
  "\<lbrakk> fd_cons t; length bs = size_td t \<rbrakk> \<Longrightarrow>
      update_ti_t t (access_ti t v bs) v = v"
apply(simp add: fd_cons_def Let_def fd_cons_update_access_def fd_cons_desc_def)
done

lemma fd_cons_length:
  "\<lbrakk> fd_cons t; length bs = size_td t \<rbrakk> \<Longrightarrow>
      length (access_ti t v bs) = size_td t"
apply(simp add: fd_cons_def Let_def  fd_cons_desc_def fd_cons_length_def access_ti\<^sub>0_def)
done

lemma fd_cons_length_p:
  "fd_cons t \<Longrightarrow>
      length (access_ti\<^sub>0 t v) = size_td t"
apply(simp add: fd_cons_length access_ti\<^sub>0_def)
done

lemma fd_cons_update_normalise:
  "\<lbrakk> fd_cons t; length bs = size_td t \<rbrakk> \<Longrightarrow>
      update_ti_t t ((norm_desc (field_desc t) (size_td t)) bs) v = update_ti_t t bs v"
apply(clarsimp simp: fd_cons_def Let_def fd_cons_desc_def)
apply(drule (3) fd_cons_update_normalise)
apply(clarsimp simp: fd_cons_update_normalise_def)
done

lemma field_footprint_SIndexVal:
  "field_lookup (typ_info_t TYPE('a::c_type)) f 0 = Some (t, n) \<Longrightarrow>
      {x. (x, SIndexVal) \<in> field_footprint (p::'a ptr) f} =
          {ptr_val p + of_nat n..+size_td t}"
apply(auto simp: field_footprint_def s_footprint_untyped_def field_typ_def field_typ_untyped_def intro: intvlI)
apply(drule intvlD, clarsimp)
done

lemma fs_footprint_subset:
  "F \<subseteq> fields TYPE('a::mem_type) \<Longrightarrow>
      fs_footprint (p::'a ptr) F \<subseteq> s_footprint p"
apply(unfold fs_footprint_def field_footprint_def)
apply(clarsimp  simp: fields_def)
apply(drule (1) subsetD)
apply clarsimp
apply(frule field_lookup_export_uinfo_Some)
apply(drule field_ti_s_sub)
apply(unfold field_lvalue_def)
apply(subst (asm) field_lookup_offset_eq)
 apply assumption
apply(clarsimp simp: field_typ_def field_typ_untyped_def)
apply(drule subsetD)
 apply assumption+
done

lemma length_heap_list_s [simp]:
  "length (heap_list_s s n p) = n"
  by (clarsimp simp: heap_list_s_def)

lemma heap_list_proj_h_restrict [rule_format]:
  "\<forall>p. {p..+n} \<subseteq> {x. (x,SIndexVal) \<in> X} \<longrightarrow>
      heap_list (proj_h (s |` X)) n p = heap_list (proj_h s) n p"
apply(induct_tac n)
 apply clarsimp
apply clarsimp
apply rule
 apply(subst proj_h_restrict)
  apply(subgoal_tac "p \<in> {p..+Suc n}")
   apply(drule (1) subsetD)
   apply clarsimp
  apply(rule intvl_self)
  apply simp
 apply simp
apply(drule_tac x="p+1" in spec)
apply(erule impE)
 apply clarsimp
 apply(subgoal_tac "x \<in> {p..+Suc n}")
  apply fast
 apply(rule intvl_plus_sub_Suc)
 apply simp+
done

lemma heap_list_proj_h_lift_state:
  "{p..+n} \<subseteq> {x. fst (d x)} \<Longrightarrow>
      heap_list (proj_h (lift_state (h,d))) n p = heap_list h n p"
apply(rule heap_list_h_eq2)
apply(subst proj_h_lift_state)
 apply fast
apply simp
done

lemma heap_list_rpbs [rule_format]:
  "\<forall>p. heap_list (\<lambda>x. 0) n p = replicate n 0"
apply(induct_tac n)
 apply simp
apply simp
done

lemma field_access_take_drop:
  "\<forall>s m n f. field_lookup t f m = Some (s,n) \<longrightarrow> wf_fd t \<longrightarrow>
      take (size_td s) (drop (n - m) (access_ti\<^sub>0 t v)) =
        access_ti\<^sub>0 s v"
  "\<forall>s m n f. field_lookup_struct st f m = Some (s,n) \<longrightarrow> wf_fd_struct st \<longrightarrow>
      take (size_td s) (drop (n - m) (access_ti_struct st v (replicate (size_td_struct st) 0))) =
        access_ti\<^sub>0 s v"
  "\<forall>s m n f. field_lookup_list ts f m = Some (s,n) \<longrightarrow> wf_fd_list ts \<longrightarrow>
      take (size_td s) (drop (n - m) (access_ti_list ts v (replicate (size_td_list ts) 0))) =
        access_ti\<^sub>0 s v"
  "\<forall>s m n f. field_lookup_pair x f m = Some (s,n) \<longrightarrow> wf_fd_pair x \<longrightarrow>
      take (size_td s) (drop (n - m) (access_ti_pair x v (replicate (size_td_pair x) 0))) =
        access_ti\<^sub>0 s v"
apply(induct t and st and ts and x)
     apply(auto simp: access_ti\<^sub>0_def)
 apply(thin_tac "All P" for P)+
 apply(subst (asm) take_all)
  apply(drule wf_fd_cons_structD)
  apply(clarsimp simp: fd_cons_struct_def fd_cons_desc_def fd_cons_length_def)
 apply simp
apply(clarsimp simp: min_def)
apply(drule wf_fd_cons_pairD)
apply(clarsimp simp: fd_cons_pair_def fd_cons_desc_def fd_cons_length_def)
apply(clarsimp split: option.splits)
 apply(subst drop_all)
  apply clarsimp
  apply(drule field_lookup_offset_le, clarsimp)
  apply(case_tac dt_pair)
  apply(clarsimp simp: fd_cons_length_def)
  apply arith
 apply simp
 apply(rotate_tac -3)
 apply(drule_tac x=s in spec)
 apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
 apply(drule_tac x=n in spec)
 apply(erule impE)
  apply fast
 apply(drule sym, clarsimp)
 apply(subgoal_tac "(size_td_pair dt_pair - (n - m)) = 0")
  apply simp
  apply(case_tac dt_pair, simp)
 apply(drule field_lookup_offset_le, clarsimp)
 apply(case_tac dt_pair, simp)
apply(subgoal_tac "(size_td s - (size_td_pair dt_pair - (n - m))) = 0")
 prefer 2
 apply clarsimp
 apply(drule td_set_pair_field_lookup_pairD)
 apply(drule td_set_pair_offset_size_m)
 apply simp
apply simp
apply(drule_tac x=s in spec)
apply(drule_tac x=m in spec)
apply(drule_tac x=n in spec)
apply clarsimp
done

lemma field_access_take_dropD:
  "\<lbrakk> field_lookup t f 0 = Some (s,n); wf_lf (lf_set t []); wf_desc t \<rbrakk> \<Longrightarrow>
      take (size_td s) (drop n (access_ti\<^sub>0 t v)) =
        access_ti\<^sub>0 s v"
apply(insert field_access_take_drop(1) [of t v])
apply clarsimp
apply(drule (1) wf_lf_fdp)
apply(drule (1) wf_fdp_fdD)
apply(drule_tac x=s in spec)
apply(drule_tac x=0 in spec)
apply(drule_tac x=n in spec)
apply simp
apply(erule impE, fast)
apply simp
done

lemma singleton_t_field:
  "field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (t, n) \<Longrightarrow>
     heap_list_s (singleton_t p v |` fs_footprint p {f}) (size_td t)
         (ptr_val p + of_nat n) = access_ti\<^sub>0 t v"
apply(clarsimp simp: heap_list_s_def singleton_def singleton_t_def)
apply(subst heap_list_proj_h_restrict)
 apply clarsimp
 apply(subgoal_tac "fs_footprint p {f} \<subseteq> s_footprint p")
  apply(clarsimp simp: fs_footprint_def)
  apply(drule_tac p=p in field_footprint_SIndexVal)
  apply fast
 apply(rule fs_footprint_subset)
 apply(clarsimp simp: fields_def)
apply(subst heap_list_proj_h_lift_state)
 apply clarsimp
 apply(frule_tac p=p in field_tag_sub)
 apply(clarsimp simp: field_lvalue_def)
 apply(drule (1) subsetD)
 apply(drule_tac d=empty_htd in ptr_retyp_footprint)
 apply simp
apply(clarsimp simp: access_ti\<^sub>0_def heap_update_def)
apply(subst heap_list_update_list)
 apply clarsimp
 apply(simp add: size_of_def)
 apply(erule field_lookup_offset_size)
apply(clarsimp simp: to_bytes_def heap_list_rpbs size_of_def)
apply(drule_tac v=v in field_access_take_dropD)
  apply simp+
apply(clarsimp simp: access_ti\<^sub>0_def)
done

lemma field_lookup_fd_consD:
  "field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (t,n) \<Longrightarrow> fd_cons t"
apply(erule fd_consistentD)
apply simp
done

lemma s_valid_map_add:
  "\<lbrakk> s,g \<Turnstile>\<^sub>s p; t,g' \<Turnstile>\<^sub>s p \<rbrakk> \<Longrightarrow> (s ++ t |` X),g \<Turnstile>\<^sub>s p"
apply(auto simp: s_valid_def h_t_valid_def valid_footprint_def Let_def)
 apply(clarsimp simp: map_le_def)
 apply(simp add: proj_d_map_add_snd)
 apply(rule, clarsimp+)
 apply(subst proj_d_restrict_map_snd)
  apply simp+
apply(subst proj_d_map_add_fst)
apply(clarsimp split: if_split_asm)
apply(subst proj_d_restrict_map_fst)
 apply simp+
done

lemma singleton_t_s_valid:
  "g p \<Longrightarrow> singleton_t p (v::'a::mem_type),g \<Turnstile>\<^sub>s p"
apply(simp add: singleton_t_def)
apply(subst h_t_s_valid)
apply(erule ptr_retyp_h_t_valid)
done


lemma sep_map_mfs_sep_map:
  "\<lbrakk> (p \<mapsto>\<^sub>g\<^sup>F v) s; field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n) \<rbrakk> \<Longrightarrow>
      (p \<mapsto>\<^sub>g\<^sup>({f}\<union>F) (v::'a::mem_type)) (s |` (dom s - fs_footprint p {f}))"
apply(clarsimp simp: mfs_sep_map_def)
apply(rule conjI)
 defer
 apply(subst fs_footprint_un[where F=F])
 apply(clarsimp simp: fields_def)
 apply fast
apply(clarsimp simp: lift_typ_heap_if split: if_split_asm)
apply(rule, clarsimp)
 apply(subgoal_tac "(singleton_t p v ++
           s |` (s_footprint p - fs_footprint p F - fs_footprint p {f})) =
     (singleton_t p v ++ s) ++ (singleton_t p v |` fs_footprint p {f})")
  apply clarsimp
  apply(subst heap_list_s_map_add_super_update_bs)
     apply clarsimp
     apply(subgoal_tac "fs_footprint p {f} \<subseteq> s_footprint p")
      apply(subgoal_tac "{x. (x, SIndexVal) \<in> fs_footprint p {f}} = {ptr_val p + of_nat n..+size_td t}")
       apply fast
      apply(clarsimp simp: fs_footprint_def)
      apply(erule field_footprint_SIndexVal)
     apply(rule fs_footprint_subset)
     apply(clarsimp simp: fields_def)
    apply(clarsimp simp: size_of_def)
    apply(subst ac_simps)
    apply(rule td_set_offset_size)
    apply(erule td_set_field_lookupD)
   apply simp
  apply(clarsimp simp: from_bytes_def)
  apply(frule_tac v="(heap_list_s (singleton_t p v |` fs_footprint p {f}) (size_td t)
            (ptr_val p + of_nat n))" and bs="(heap_list_s (singleton_t p v ++ s) (size_of TYPE('a))
            (ptr_val p))" and w=undefined
        in fi_fu_consistentD)
     apply simp
    apply(simp add: size_of_def)
   apply simp
  apply simp
  apply(simp add: singleton_t_field)
  apply(clarsimp simp: access_ti\<^sub>0_def)
  apply(subst fd_cons_update_access)
    apply(erule field_lookup_fd_consD)
   apply simp+
 apply(subst map_add_restrict_sub)
   apply simp
  apply assumption
 apply simp
apply(subgoal_tac "(singleton_t p v ++
           s |` (s_footprint p - fs_footprint p F - fs_footprint p {f})) =
     (singleton_t p v ++ s) ++ (singleton_t p v |` fs_footprint p {f})")
 apply clarsimp
 apply(erule s_valid_map_add)
 apply(simp add: singleton_t_def)
 apply(fold singleton_t_def)
 apply(rule singleton_t_s_valid)
 apply(rule ptr_retyp_h_t_valid)
 apply fast
apply(subst map_add_restrict_sub)
  apply simp
 apply assumption
apply simp
done

lemma disjoint_fn_disjoint:
  "\<lbrakk> disjoint_fn f F; F \<subseteq> fields TYPE('a::mem_type);
      field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n) \<rbrakk> \<Longrightarrow>
      fs_footprint (p::'a ptr) F \<inter> field_footprint p f = {}"
apply(auto simp: fs_footprint_def)
apply(auto simp: field_footprint_def s_footprint_untyped_def field_typ_def field_typ_untyped_def fields_def)
 apply(drule (1) subsetD, clarsimp)
 apply(drule (1) fa_fu_lookup_disj_interD)
    apply(clarsimp simp: disj_fn_def disjoint_fn_def)
   apply simp+
  apply(subgoal_tac "size_of TYPE('a) < addr_card")
   apply(simp only: size_of_def)
  apply simp
 apply(subgoal_tac "of_nat n + of_nat x \<in> {of_nat n..+size_td t}")
  apply(subgoal_tac "of_nat b + of_nat xa \<in> {of_nat b..+size_td a}")
   apply force
  apply(rule intvlI, assumption)+
apply(drule (1) subsetD, clarsimp)
apply(drule (1) fa_fu_lookup_disj_interD)
  apply(clarsimp simp: disj_fn_def disjoint_fn_def)
  apply simp+
 apply(subgoal_tac "size_of TYPE('a) < addr_card")
  apply(simp only: size_of_def)
 apply simp
apply(subgoal_tac "of_nat n + of_nat x \<in> {of_nat n..+size_td t}")
 apply(subgoal_tac "of_nat b + of_nat xa \<in> {of_nat b..+size_td a}")
  apply force
 apply(rule intvlI, assumption)+
done


lemma sep_map_mfs_sep_map2:
  "\<lbrakk>field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (s, n);
       disjoint_fn f F; guard_mono g g';
       export_uinfo s = typ_uinfo_t TYPE('b); ((p::'a ptr) \<mapsto>\<^sub>g\<^sup>F v) x\<rbrakk>
        \<Longrightarrow> (Ptr &(p\<rightarrow>f) \<mapsto>\<^sub>g' ((from_bytes (access_ti\<^sub>0 s v))::'b::mem_type))
            (x |` field_footprint p f)"
apply(clarsimp simp: mfs_sep_map_def sep_map_def)
apply rule
 defer
 apply(clarsimp simp: field_footprint_def field_lvalue_def)
 apply(clarsimp simp: s_footprint_def field_typ_def field_typ_untyped_def)
 apply(subgoal_tac "{f} \<subseteq> fields TYPE('a)")
  apply(drule_tac p=p in fs_footprint_subset[where F="{f}"])
  apply(rotate_tac -1)
  apply(subst (asm) fs_footprint_def)
  apply(clarsimp simp: field_footprint_def)
  apply(clarsimp simp: s_footprint_def field_typ_def field_typ_untyped_def)
  apply(subgoal_tac "fs_footprint p F \<inter> s_footprint_untyped (ptr_val p + of_nat n) (typ_uinfo_t TYPE('b)) = {}")
   apply blast
  apply(drule_tac p=p in disjoint_fn_disjoint, assumption+)
  apply(simp add: field_footprint_def field_typ_def field_typ_untyped_def)
  apply simp
 apply(clarsimp simp: fields_def)
apply(subgoal_tac "field_footprint p f = s_footprint ((Ptr &(p\<rightarrow>f))::'b ptr)")
 prefer 2
 apply(clarsimp simp: field_footprint_def s_footprint_def field_lvalue_def typ_uinfo_t_def field_typ_def field_typ_untyped_def)
apply simp
apply(frule lift_typ_heap_mono)
   apply assumption+
apply(clarsimp simp: lift_typ_heap_if split: if_split_asm)
apply(rule, clarsimp)
 apply(subst (asm) heap_list_s_heap_merge_right[where p="&(p\<rightarrow>f)"])
   apply assumption+
apply(erule s_valid_heap_merge_right2)
apply simp
apply(frule_tac p=p in disjoint_fn_disjoint, assumption+)
apply(subgoal_tac "fs_footprint p {f} \<subseteq> s_footprint p")
 prefer 2
 apply(rule fs_footprint_subset)
 apply(clarsimp simp: fields_def)
apply(fastforce simp: fs_footprint_def)
done

lemma export_size_of:
  "export_uinfo t = typ_uinfo_t TYPE('a) \<Longrightarrow>
    size_of TYPE('a::c_type) = size_td t"
apply(simp add: size_of_def)
apply(subst typ_uinfo_size [symmetric])
apply(drule sym)
apply simp
done

lemma sep_map_field_unfold:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n);
      disjoint_fn f F; guard_mono g g';
      export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
      (p \<mapsto>\<^sub>g\<^sup>F v) = (p \<mapsto>\<^sub>g\<^sup>({f}\<union>F) (v::'a::mem_type) \<and>\<^sup>*
          Ptr (&(p\<rightarrow>f)) \<mapsto>\<^sub>g' ((from_bytes (access_ti\<^sub>0 t v))::'b::mem_type))"
apply(rule ext)
apply rule
 apply(rule_tac s\<^sub>0="x |` (dom x - fs_footprint p {f})" and
     s\<^sub>1="x |` fs_footprint p {f}" in sep_conjI)
    apply(erule (1) sep_map_mfs_sep_map)
   apply(clarsimp simp: fs_footprint_def)
   apply(erule (4) sep_map_mfs_sep_map2)
  apply(clarsimp simp: map_disj_def)
  apply fast
 apply clarsimp
apply(drule sep_conjD, clarsimp)
apply(clarsimp simp: mfs_sep_map_def sep_map_def)
apply rule
 apply(subst map_ac_simps)
 apply(subst map_add_com [where h\<^sub>0=s\<^sub>1])
  apply(simp add: map_ac_simps)
 apply(subst map_add_assoc)
 apply(clarsimp simp: lift_typ_heap_if split: if_split_asm)
 apply(rule, clarsimp)
  apply(subst heap_list_s_map_add_super_update_bs)
     apply(subst s_footprint_untyped_dom_SIndexVal)
      apply(clarsimp simp: s_footprint_def)
      apply fast
     apply(clarsimp simp: field_lvalue_def)
     apply fast
    apply(drule field_lookup_offset_size)
    apply(drule export_size_of)
    apply(simp add: size_of_def)
   apply simp
  apply(clarsimp simp: from_bytes_def)
  apply(frule_tac v="heap_list_s s\<^sub>1 (size_td (typ_info_t TYPE('b)))
               (ptr_val p + of_nat n)" and bs="(heap_list_s (singleton_t p v ++ s\<^sub>0) (size_of TYPE('a))
               (ptr_val p))" and w=undefined in fi_fu_consistentD)
     apply simp+
    apply(simp add: size_of_def)
   apply simp
   apply(drule export_size_of, simp add: size_of_def)
  apply simp
  apply(subst fd_cons_update_normalise [symmetric])
    apply(erule field_lookup_fd_consD)
   apply simp
   apply(drule export_size_of, simp add: size_of_def)
  apply(simp add: norm_desc_def)
  apply(drule_tac f="access_ti\<^sub>0 (typ_info_t TYPE('b))" in arg_cong)
  apply(drule_tac f="\<lambda>bs. update_ti_t t bs v" in arg_cong)
  apply(subst (asm) wf_fd_norm_tuD [symmetric])
    apply simp
   apply(simp add: size_of_def)
  apply(subst (asm) wf_fd_norm_tuD [symmetric])
    apply simp
   apply(subst fd_cons_length_p)
    apply(erule field_lookup_fd_consD)
   apply(drule export_size_of, simp add: size_of_def)
  apply(subgoal_tac "export_uinfo (typ_info_t TYPE('b)) = typ_uinfo_t TYPE('b)")
   prefer 2
   apply(simp add: typ_uinfo_t_def)
  apply simp
  apply(drule sym, simp)
  apply(subst (asm) wf_fd_norm_tuD)
    apply(erule wf_fd_field_lookupD, simp)
   apply simp
   apply(drule sym, drule export_size_of)
   apply(simp add: size_of_def)
  apply(simp add: access_ti\<^sub>0_def)
  apply(clarsimp simp: field_lvalue_def)
  apply(simp add: size_of_def)
  apply(subst wf_fd_norm_tuD)
    apply(erule wf_fd_field_lookupD, simp)
   apply(subst fd_cons_length)
     apply(erule field_lookup_fd_consD)
    apply simp
   apply simp
  apply(subgoal_tac "update_ti_t t (norm_desc (field_desc t) (size_td t) (access_ti t v (replicate (size_td t) 0))) v = v")
   apply(simp add: norm_desc_def)
   apply(simp add: access_ti\<^sub>0_def)
  apply(subst fd_cons_update_normalise)
    apply(erule field_lookup_fd_consD)
   apply(subst fd_cons_length)
     apply(erule field_lookup_fd_consD)
    apply simp
   apply simp
  apply(subst fd_cons_update_access)
    apply(erule field_lookup_fd_consD)
   apply simp
  apply simp
 prefer 2
 apply(subst fs_footprint_un)
 apply(subst fs_footprint_def)
 apply(clarsimp simp: field_footprint_def s_footprint_def field_lvalue_def field_typ_def field_typ_untyped_def)
 apply(drule_tac p=p in disjoint_fn_disjoint)
   apply assumption+
 apply(clarsimp simp: field_footprint_def s_footprint_def field_lvalue_def field_typ_def field_typ_untyped_def)
 apply(subgoal_tac "{f} \<subseteq> fields TYPE('a)")
  apply(drule_tac p=p in fs_footprint_subset[where F="{f}"])
  apply(clarsimp simp: s_footprint_def)
  apply(fastforce simp: fs_footprint_def field_footprint_def s_footprint_def
                       field_typ_def field_typ_untyped_def field_lvalue_def)
 apply(clarsimp simp: fields_def)
apply(clarsimp simp: s_valid_def h_t_valid_def valid_footprint_def Let_def)
apply(rule, clarsimp simp: map_le_def)
 apply(subst proj_d_map_add_snd[where t=s\<^sub>1])
 apply(clarsimp split: if_split_asm)
 apply(frule s_footprintD2)
 apply(drule s_footprintD)
 apply(drule_tac x=y in spec)
 apply clarsimp
 apply(drule_tac x=a in bspec)
  apply clarsimp
 apply(drule intvlD, clarsimp simp: field_lvalue_def)
 apply(drule_tac x=k in spec)
  apply(clarsimp simp add: size_of_def)
 apply(drule_tac x=a in bspec)
  apply clarsimp
  apply(subst (asm) unat_of_nat)
  apply(subst (asm) mod_less)
   apply(subst len_of_addr_card)
   apply(erule less_trans)
   apply(subgoal_tac "size_of TYPE('b) < addr_card", simp only:size_of_def)
   apply simp
  apply simp
 apply(simp add: ac_simps)
 apply(rotate_tac -1)
 apply(drule sym)
 apply simp
 apply(drule sym[where s="Some s" for s])
 apply simp
 apply(drule field_lookup_export_uinfo_Some)
 apply(drule td_set_field_lookupD)
 apply(frule_tac k=k in typ_slice_td_set)
  apply simp
 apply simp
 apply(simp add: typ_uinfo_t_def)
 apply(subgoal_tac "y=n+k")
  apply(simp add: strict_prefix_def)
  apply clarsimp
  apply(subst (asm) unat_of_nat)
  apply(subst (asm) mod_less)
   apply(subst len_of_addr_card)
   apply(erule less_trans)
   apply(subgoal_tac "size_of TYPE('b) < addr_card", simp only:size_of_def)
   apply simp
  apply (clarsimp simp: prefix_eq_nth)
 apply(drule_tac f=unat in arg_cong)
 apply(rotate_tac -1)
 apply(subst (asm) unat_of_nat)
 apply(subst (asm) mod_less)
  apply(subst len_of_addr_card)
  apply(erule less_trans)
  apply(subgoal_tac "size_of TYPE('a) < addr_card", simp only:size_of_def)
  apply simp
 apply(subst (asm) Abs_fnat_hom_add)
 apply(subst (asm) unat_of_nat)
 apply(subst (asm) mod_less)
  apply(subst len_of_addr_card)
  apply(drule td_set_offset_size)
  apply simp
  apply(rule_tac y="size_td (typ_info_t TYPE('a))" in le_less_trans)
   apply simp
  apply(subgoal_tac "size_of TYPE('a) < addr_card", simp only:size_of_def)
  apply simp
 apply simp
apply(subst proj_d_map_add_fst)
apply(clarsimp split: if_split_asm)
apply(drule s_footprintD, clarsimp)
apply(drule intvlD, clarsimp simp: field_lvalue_def)
apply(fastforce simp: size_of_def ac_simps)
done

lemma disjoint_fn_empty [simp]:
  "disjoint_fn f {}"
  by (simp add: disjoint_fn_def)

lemma sep_map_field_map':
  "\<lbrakk> ((p::'a::mem_type ptr) \<mapsto>\<^sub>g v) s; field_lookup (typ_info_t TYPE('a)) f 0
      = Some (d,n); export_uinfo d = typ_uinfo_t TYPE('b);
      guard_mono g g' \<rbrakk> \<Longrightarrow>
      ((Ptr (&(p\<rightarrow>f))::'b::mem_type ptr) \<hookrightarrow>\<^sub>g' from_bytes (access_ti\<^sub>0 d v)) s"
apply(frule sep_map_g)
apply(subst (asm) sep_map_mfs_sep_map_empty)
apply(subst (asm) sep_map_field_unfold)
    apply fast
   apply simp
  apply assumption+
apply(clarsimp simp: sep_map'_def sep_conj_ac)
apply(erule sep_conj_impl)
 apply simp
apply simp
done

lemma fd_cons_access_update_p:
  "\<lbrakk> fd_cons t; length bs = size_td t \<rbrakk> \<Longrightarrow>
      access_ti\<^sub>0 t (update_ti_t t bs v) = access_ti\<^sub>0 t (update_ti_t t bs w)"
apply(simp add: fd_cons_def Let_def fd_cons_access_update_def fd_cons_desc_def access_ti\<^sub>0_def)
done

lemma length_to_bytes_p [simp]:
  "length (to_bytes_p (v::'a)) = size_of TYPE('a::mem_type)"
  by (simp add: to_bytes_p_def)

lemma inv_p [simp]:
  "from_bytes (to_bytes_p v) = (v::'a::mem_type)"
  by (simp add: to_bytes_p_def)

lemma singleton_SIndexVal:
  "x \<in> {ptr_val p..+size_of TYPE('a)} \<Longrightarrow>
      singleton_t p (v::'a::mem_type) (x,SIndexVal) = Some (SValue (to_bytes_p v ! unat (x - ptr_val p)))"
apply(auto simp: singleton_def singleton_t_def)
apply(auto simp: lift_state_def)
 apply(clarsimp simp: heap_update_def)
 apply(subst heap_update_mem_same_point)
   apply simp
  apply simp
 apply(simp add: to_bytes_p_def heap_list_rpbs)
apply(subst ptr_retyp_d_eq_fst)
apply simp
done

lemma access_ti\<^sub>0:
  "access_ti s v (replicate (size_td s) 0) = access_ti\<^sub>0 s v"
apply(simp add: access_ti\<^sub>0_def)
done

lemma fd_cons_mem_type [simp]:
  "fd_cons (typ_info_t TYPE('a::mem_type))"
apply(rule wf_fd_consD)
apply simp
done

lemma norm_tu_rpbs:
  "wf_fd t \<Longrightarrow>
    norm_tu (export_uinfo t) (access_ti\<^sub>0 t v) = access_ti\<^sub>0 t v"
apply(subst wf_fd_norm_tuD)
  apply assumption
 apply(subst fd_cons_length_p)
  apply(erule wf_fd_consD)
 apply simp
apply(subst fd_cons_access_update_p [where w=v])
  apply(erule wf_fd_consD)
 apply(subst fd_cons_length_p)
  apply(erule wf_fd_consD)
 apply simp
apply(simp add: access_ti\<^sub>0_def)
apply(subst fd_cons_update_access)
  apply(erule wf_fd_consD)
 apply simp+
done

lemma heap_list_s_singleton_t_field_update:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (s, n);
      export_uinfo s = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
      heap_list_s (singleton_t p (update_ti_t s (to_bytes_p w) v)) (size_td s)
          (ptr_val (p::'a::mem_type ptr) + of_nat n) = (to_bytes_p (w::'b::mem_type))"
apply(auto simp: singleton_t_def singleton_def)
apply(subst heap_list_s_heap_list_dom)
 apply clarsimp
 apply(frule_tac p=p in field_tag_sub)
 apply(clarsimp simp: field_lvalue_def)
 apply(drule (1) subsetD)
 apply(drule_tac n="size_of TYPE('a)" in intvlD, clarsimp)
 apply(erule s_footprintI2)
apply(simp add: heap_update_def)
apply(subst heap_list_update_list)
 apply simp
 apply(drule field_lookup_offset_size)
 apply(simp add: size_of_def)
apply(frule_tac v="(update_ti_t s (to_bytes_p w) v)" in field_access_take_dropD)
  apply simp+
apply(simp add: access_ti\<^sub>0_def to_bytes_def heap_list_rpbs size_of_def to_bytes_p_def)
apply(simp add: access_ti\<^sub>0)
apply(subst fd_cons_access_update_p [where w=undefined])
  apply(erule field_lookup_fd_consD)
 apply(subst fd_cons_length_p)
  apply simp
 apply(drule export_size_of, simp add: size_of_def)
apply(subst wf_fd_norm_tuD [symmetric])
  apply(erule wf_fd_field_lookupD)
  apply simp
 apply(subst fd_cons_length_p)
  apply simp
 apply(drule export_size_of, simp add: size_of_def)
apply simp
apply(simp add: typ_uinfo_t_def)
apply(rule norm_tu_rpbs)
apply simp
done

lemma field_access_update_nth_disj:
  "\<forall>m f s n x bs bs'. field_lookup t f m = Some (s,n) \<longrightarrow> x < size_td t \<longrightarrow>
      (x < n - m \<or> x \<ge> (n - m) + size_td s) \<longrightarrow> wf_fd t \<longrightarrow> length bs = size_td s \<longrightarrow> length bs' = size_td t \<longrightarrow>
      access_ti t (update_ti_t s bs v) bs' ! x
          = access_ti t v bs' ! x"
  "\<forall>m f s n x bs bs'. field_lookup_struct  st f m = Some (s,n) \<longrightarrow> x < size_td_struct st \<longrightarrow>
      (x < n -  m \<or> x \<ge> (n - m) + size_td s) \<longrightarrow> wf_fd_struct st \<longrightarrow>length bs = size_td s \<longrightarrow> length bs' = size_td_struct st \<longrightarrow>
      access_ti_struct st (update_ti_t s bs v) bs' ! x
          = access_ti_struct st v bs' ! x"
  "\<forall>m f s n x bs bs'. field_lookup_list ts f m = Some (s,n) \<longrightarrow> x < size_td_list ts \<longrightarrow>
      (x < n -  m \<or> x \<ge> (n - m) + size_td s) \<longrightarrow> wf_fd_list ts \<longrightarrow>length bs = size_td s \<longrightarrow> length bs' = size_td_list ts \<longrightarrow>
      access_ti_list ts (update_ti_t s bs v) bs' ! x
          = access_ti_list ts v bs' ! x"
  "\<forall>m f s n x bs bs'. field_lookup_pair y f m = Some (s,n) \<longrightarrow> x < size_td_pair y \<longrightarrow>
      (x < n -  m \<or> x \<ge> (n - m) + size_td s) \<longrightarrow> wf_fd_pair y \<longrightarrow>length bs = size_td s \<longrightarrow> length bs' = size_td_pair y \<longrightarrow>
      access_ti_pair y (update_ti_t s bs v) bs' ! x
          = access_ti_pair y v bs' ! x"
apply(induct t and st and ts and y)
     apply clarsimp
    apply clarsimp
   apply clarsimp
  apply clarsimp
 prefer 2
 apply clarsimp
apply clarify
apply(clarsimp split: if_split_asm)
apply(clarsimp split: option.splits)

 apply(rotate_tac -3)
 apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
 apply(drule_tac x=f in spec)
 apply(drule_tac x=s in spec)
 apply(rotate_tac -1)
 apply(drule_tac x=n in spec)

 apply clarsimp
 apply(rotate_tac -1)
 apply(drule_tac x="x - size_td_pair dt_pair" in spec)
 apply(frule field_lookup_fa_fu_rhs_listD)
   apply simp
  apply assumption
 apply(clarsimp simp: fa_fu_ind_def)
 apply(subgoal_tac "access_ti_pair dt_pair (update_ti_t s bs v) (take (size_td_pair dt_pair) bs') =
                    access_ti_pair dt_pair v (take (size_td_pair dt_pair) bs')")
  prefer 2
  apply (fastforce simp: min_def)
 apply(clarsimp simp: nth_append)
 apply(subgoal_tac "length
               (access_ti_pair dt_pair v
                 (take (size_td_pair dt_pair) bs')) = size_td_pair dt_pair")
  apply simp
  prefer 2
  apply(drule wf_fd_cons_pairD)
  apply(clarsimp simp: fd_cons_pair_def fd_cons_desc_def fd_cons_length_def)
 apply(erule impE)
  apply simp
 apply(case_tac dt_pair, simp+)
 apply(rename_tac a b)
 apply(drule_tac x=bs in spec)
 apply(drule_tac x="drop (size_td a) bs'" in spec)
 apply clarsimp
 apply(frule field_lookup_offset_le)
 apply clarsimp
 apply(drule td_set_list_field_lookup_listD)
 apply(drule td_set_list_offset_size_m)
 apply clarsimp
 apply(erule disjE)
  apply arith
 apply arith
apply(frule field_lookup_fa_fu_rhs_pairD, simp)
 apply assumption
apply(clarsimp simp: fa_fu_ind_def)
apply(subgoal_tac "length (access_ti_pair dt_pair (update_ti_t s bs v)
            (take (size_td_pair dt_pair) bs')) = size_td_pair dt_pair")
 apply(subgoal_tac "length (access_ti_pair dt_pair v
            (take (size_td_pair dt_pair) bs')) = size_td_pair dt_pair")
  apply(clarsimp simp: nth_append)
  apply(drule_tac x=m in spec)
  apply(drule_tac x=f in spec)
  apply(drule_tac x=s in spec)
  apply(drule_tac x=n in spec)
  apply clarsimp
  apply(drule_tac x=x in spec)
  apply clarsimp
  apply(drule_tac x=bs in spec)
  apply(drule_tac x="take (size_td_pair dt_pair) bs'" in spec)
  apply(clarsimp simp: min_def split: if_split_asm)
 apply(drule wf_fd_cons_pairD)
 apply(clarsimp simp: fd_cons_pair_def fd_cons_desc_def fd_cons_length_def)
apply(drule wf_fd_cons_pairD)
apply(clarsimp simp: fd_cons_pair_def fd_cons_desc_def fd_cons_length_def)
done

lemma field_access_update_nth_disjD:
  "\<lbrakk> field_lookup t f m = Some (s,n); x < size_td t;
      (x < n - m \<or> x \<ge> (n - m) + size_td s);  wf_fd t;
      length bs = size_td s; length bs' = size_td t \<rbrakk> \<Longrightarrow>
      access_ti t (update_ti_t s bs v) bs' ! x
          = access_ti t v bs' ! x"
apply(simp add: field_access_update_nth_disj)
done

lemma intvl_cut:
  "\<lbrakk> (x::addr) \<in> {p..+m}; x \<notin> {p+of_nat k..+n}; m < addr_card \<rbrakk> \<Longrightarrow>
      unat (x - p) < k \<or> k + n \<le> unat (x - p)"
apply(drule intvlD, clarsimp)
apply(subst unat_of_nat, subst mod_less, subst len_of_addr_card)
 apply(erule (1) less_trans)
apply(subst (asm) unat_of_nat, subst (asm) mod_less, subst len_of_addr_card)
 apply(erule (1) less_trans)
apply(rule ccontr)
apply(erule notE)
apply(subgoal_tac "\<exists>z. ka = k + z")
 prefer 2
 apply(rule_tac x="ka - k" in exI)
 apply simp
apply clarsimp
apply(simp add: add.assoc [symmetric])
apply(rule intvlI)
apply simp
done

lemma singleton_t_mask_out:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a::mem_type)) f 0 = Some (s,n);
      export_uinfo s = typ_uinfo_t TYPE('b);
      K = (UNIV - s_footprint_untyped &(p\<rightarrow>f) (export_uinfo s)) \<rbrakk> \<Longrightarrow>
    singleton_t p (update_ti_t s (to_bytes_p (w::'b::mem_type)) (v::'a)) |` K =
   singleton_t p v |` K"
apply(rule ext)
apply simp
apply(auto simp: restrict_map_def)
apply(simp add: singleton_t_def singleton_def)
apply(auto simp: lift_state_def restrict_map_def split: s_heap_index.splits)
apply(simp add: heap_update_def)
apply(simp add: to_bytes_def access_ti\<^sub>0 heap_list_rpbs size_of_def)
apply(subst heap_update_mem_same_point)
  apply(subst fd_cons_length_p)
   apply simp
  apply(rule ccontr)
  apply(subst (asm) ptr_retyp_None)
   apply(simp add: size_of_def)
  apply simp
 apply(subst fd_cons_length_p)
  apply simp
 apply(subgoal_tac "size_of TYPE('a) < addr_card")
  apply(simp only: size_of_def)
 apply simp
apply(subst heap_update_mem_same_point)
  apply(subst fd_cons_length_p)
   apply simp
  apply(rule ccontr)
  apply(subst (asm) ptr_retyp_None)
   apply(simp add: size_of_def)
  apply simp
 apply(subst fd_cons_length_p)
  apply simp
 apply(subgoal_tac "size_of TYPE('a) < addr_card")
  apply(simp only: size_of_def)
 apply simp
apply(simp add: access_ti\<^sub>0_def)
apply(rule field_access_update_nth_disjD)
     apply assumption
    apply(subst (asm) ptr_retyp_d_eq_fst)
    apply(clarsimp simp: empty_htd_def split: if_split_asm)
    apply(drule intvlD, clarsimp)
    apply(subst unat_of_nat)
    apply(subst mod_less)
     apply(subst len_of_addr_card)
     apply(erule less_trans)
     apply simp
    apply(simp add: size_of_def)
   apply simp
   apply(subst (asm) ptr_retyp_d_eq_fst)
   apply(clarsimp simp: empty_htd_def split: if_split_asm)
   apply(drule_tac k="of_nat n" and n="size_td s" in intvl_cut)
     prefer 2
     apply simp
    apply(clarsimp simp: s_footprint_untyped_def field_lvalue_def)
    apply(drule intvlD, clarsimp)
    apply(drule export_size_of, simp add: size_of_def)
   apply simp
  apply simp+
 apply(drule export_size_of, simp add: size_of_def)
apply simp
done

lemma singleton_t_SIndexTyp:
  "singleton_t p v (x,SIndexTyp n) = singleton_t p undefined (x,SIndexTyp n)"
apply(auto simp: singleton_t_def singleton_def restrict_map_def lift_state_def)
done

lemma proj_d_singleton_t:
  "proj_d (singleton_t p (v::'a::mem_type) ++ x) = proj_d (singleton_t p undefined ++ x)"
apply(rule ext)
apply(auto simp: proj_d_def)
  apply(subgoal_tac "dom (singleton_t p undefined ) = dom (singleton_t p v )")
   apply blast
  apply simp
 apply(subgoal_tac "dom (singleton_t p undefined ) = dom (singleton_t p v )")
  apply blast
 apply simp
apply(rule ext)
apply(auto simp: split: option.splits)
  apply(subgoal_tac "dom (singleton_t p undefined ) = dom (singleton_t p v )")
   apply blast
  apply simp
 apply(subgoal_tac "dom (singleton_t p undefined ) = dom (singleton_t p v )")
  apply blast
 apply simp
apply(subst (asm) singleton_t_SIndexTyp)
apply simp
done

lemma from_bytes_heap_list_s_update:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n);
     export_uinfo s = typ_uinfo_t TYPE('b);
     dom x = s_footprint p - fs_footprint p F; f \<in> F \<rbrakk> \<Longrightarrow>
      from_bytes (heap_list_s (singleton_t p (update_ti_t s (to_bytes_p (w::'b::mem_type)) (v::'a::mem_type)) ++ x) (size_of TYPE('a)) (ptr_val p))  =
        update_ti_t s (to_bytes_p w) (from_bytes (heap_list_s (singleton_t p v ++ x) (size_of TYPE('a)) (ptr_val p)))"
apply(subst map_add_restrict_UNIV [where X="s_footprint_untyped (&(p\<rightarrow>f)) (export_uinfo s)" and h="singleton_t p v"])
  apply(clarsimp simp: fs_footprint_def field_footprint_def field_lvalue_def)
  apply(thin_tac "dom x = X" for X)
  apply(clarsimp simp: field_typ_def field_typ_untyped_def)
  apply force
 apply simp
apply(subst heap_list_s_map_add_super_update_bs [where k=n and z="size_td s"])
   apply simp
   apply rule
    apply clarsimp
    apply(clarsimp simp: s_footprint_untyped_def field_lvalue_def)
    apply(drule s_footprintD)
    apply(rule intvlI)
    apply(drule export_size_of, simp add: size_of_def)
   apply clarsimp
   apply rule
    apply(frule_tac p=p in field_tag_sub)
    apply(clarsimp simp: field_lvalue_def)
    apply(drule (1) subsetD)
    apply(drule_tac n="size_of TYPE('a)" in intvlD, clarsimp)
    apply(erule s_footprintI2)
   apply(drule intvlD, clarsimp)
   apply(clarsimp simp: s_footprint_untyped_def field_lvalue_def)
   apply(rule_tac x=k in exI)
   apply simp
   apply(drule export_size_of, simp add: size_of_def)
  apply(drule field_lookup_offset_size)
  apply(simp add: size_of_def)
 apply simp
apply(clarsimp simp: from_bytes_def)
apply(frule_tac v="(heap_list_s
            (singleton_t p (update_ti_t s (to_bytes_p w) v) |`
             s_footprint_untyped &(p\<rightarrow>f) (export_uinfo s))
            (size_td s) (ptr_val p + of_nat n))" and
  bs="(heap_list_s
            (singleton_t p (update_ti_t s (to_bytes_p w) v) |`
             (UNIV - s_footprint_untyped &(p\<rightarrow>f) (export_uinfo s)) ++
             singleton_t p v |`
             s_footprint_untyped &(p\<rightarrow>f) (typ_uinfo_t TYPE('b)) ++
             x)
            (size_of TYPE('a)) (ptr_val p))" and
  w=undefined in fi_fu_consistentD)
   apply(simp add: size_of_def)+
apply(subst heap_list_s_restrict)
 apply clarsimp
 apply(drule intvlD, clarsimp)
 apply(subst s_footprint_untyped_def)
 apply(clarsimp simp: field_lvalue_def)
 apply(rule_tac x=k in exI)
 apply simp
 apply(drule export_size_of, simp add: size_of_def)
apply(subst heap_list_s_singleton_t_field_update)
  apply assumption+
apply(subst singleton_t_mask_out)
   apply assumption+
 apply simp
apply(subst map_add_restrict_comp_left)
apply simp
done

lemma mfs_sep_map_field_update:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n); f \<in> F;
      export_uinfo s = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
      (p \<mapsto>\<^sub>g\<^sup>F update_ti_t s (to_bytes_p (w::'b::mem_type)) v) = (p \<mapsto>\<^sub>g\<^sup>F update_ti_t s (to_bytes_p (u::'b::mem_type)) (v::'a::mem_type))"
apply(rule ext)
apply(auto simp: mfs_sep_map_def lift_typ_heap_if)
   prefer 2
   apply(subst from_bytes_heap_list_s_update)
       apply assumption+
   apply(subst (asm) from_bytes_heap_list_s_update)
      apply assumption+
   apply(drule_tac f="update_ti_t s (to_bytes_p w)" in arg_cong)
   apply(subst (asm) fd_cons_double_update)
     apply(erule field_lookup_fd_consD)
    apply simp
   apply(subst (asm) fd_cons_double_update)
     apply(erule field_lookup_fd_consD)
    apply simp
   apply simp
  apply(subst from_bytes_heap_list_s_update)
      apply assumption+
  apply(subst (asm) from_bytes_heap_list_s_update)
     apply assumption+
  apply(drule_tac f="update_ti_t s (to_bytes_p u)" in arg_cong)
  apply(subst (asm) fd_cons_double_update)
    apply(erule field_lookup_fd_consD)
   apply simp
  apply(subst (asm) fd_cons_double_update)
    apply(erule field_lookup_fd_consD)
   apply simp
  apply simp
 apply(clarsimp simp: s_valid_def)
 apply(subst (asm) proj_d_singleton_t)
 apply(subst (asm) proj_d_singleton_t[where v="update_ti_t s (to_bytes_p u) v"])
 apply simp
apply(clarsimp simp: s_valid_def)
apply(subst (asm) proj_d_singleton_t)
apply(subst (asm) proj_d_singleton_t[where v="update_ti_t s (to_bytes_p u) v"])
apply simp
done

lemma mfs_sep_map_field_update_v:
  " \<lbrakk>field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n); f \<in> F;
     disjoint_fn f (F - {f}); guard_mono g g';
     export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk>
    \<Longrightarrow>
       p \<mapsto>\<^sub>g\<^sup>F update_ti_t t (to_bytes_p (w::'b::mem_type)) (v::'a::mem_type) = p \<mapsto>\<^sub>g\<^sup>F v"
apply(subst mfs_sep_map_field_update [where u="from_bytes (access_ti\<^sub>0 t v)"])
   apply assumption
  apply simp+
apply(simp add: to_bytes_p_def to_bytes_def from_bytes_def access_ti\<^sub>0 size_of_def)
apply(subst wf_fd_norm_tuD [symmetric])
  apply simp
 apply(subst fd_cons_length_p)
  apply(erule field_lookup_fd_consD)
 apply(drule export_size_of, simp add: size_of_def)
apply(rotate_tac -1)
apply(drule sym)
apply(simp add: typ_uinfo_t_def)
apply(subgoal_tac "norm_tu (typ_uinfo_t TYPE('b)) = norm_bytes TYPE('b)")
 prefer 2
 apply(simp add: norm_bytes_def typ_uinfo_t_def)
apply(clarsimp simp: norm_bytes_def)
apply(subst wf_fd_norm_tuD)
  apply(erule wf_fd_field_lookupD)
  apply simp
 apply(subst fd_cons_length_p)
  apply(erule field_lookup_fd_consD)
 apply simp
apply(subst fd_cons_access_update_p [where w=v])
  apply(erule field_lookup_fd_consD)
 apply(subst fd_cons_length_p)
  apply(erule field_lookup_fd_consD)
 apply simp
apply(simp add: access_ti\<^sub>0_def)
apply(subst fd_cons_update_access)
  apply(erule field_lookup_fd_consD)
 apply simp
apply(subst fd_cons_update_access)
  apply(erule field_lookup_fd_consD)
 apply simp
apply simp
done

lemma sep_map_field_fold:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n);
      f \<in> F; disjoint_fn f (F - {f}); guard_mono g g';
      export_uinfo t = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
      (p \<mapsto>\<^sub>g\<^sup>F (v::'a::mem_type) \<and>\<^sup>*
          Ptr &(p\<rightarrow>f) \<mapsto>\<^bsub>g'\<^esub> (w::'b::mem_type))
      = p \<mapsto>\<^sub>g\<^sup>(F - {f}) (update_ti_t t (to_bytes_p w) v)"
apply(subst sep_map_field_unfold, assumption, assumption+)
apply simp
apply(subst fd_cons_access_update_p [where w=undefined])
  apply(erule field_lookup_fd_consD)
 apply simp
 apply(drule export_size_of, simp add: size_of_def)
apply(subst wf_fd_norm_tuD [symmetric])
  apply(erule wf_fd_field_lookupD)
  apply simp+
 apply(drule export_size_of, simp add: size_of_def)
apply simp
apply(subgoal_tac "norm_tu (typ_uinfo_t TYPE('b)) = norm_bytes TYPE('b)")
 prefer 2
 apply(simp add: norm_bytes_def typ_uinfo_t_def)
apply (simp add: sep_conj_ac)
apply(subst norm)
 apply simp+
apply(subst mfs_sep_map_field_update_v)
     apply assumption+
    apply fast
   apply simp
  apply assumption+
apply(subgoal_tac "insert f  F = F")
 apply simp
apply fast
done

lemma norm_bytes:
  "length bs = size_of TYPE('a) \<Longrightarrow>
      to_bytes_p ((from_bytes bs)::'a) = norm_bytes TYPE('a::mem_type) bs"
apply(simp add: norm_bytes_def)
apply(subst wf_fd_norm_tuD)
  apply simp
 apply(simp add: size_of_def)
apply(simp add: to_bytes_p_def size_of_def from_bytes_def to_bytes_def access_ti\<^sub>0_def)
done

lemma sep_heap_update_global_super_fl:
  "\<lbrakk> (p \<mapsto>\<^sub>g u \<and>\<^sup>* R) (lift_state (h,d));
      field_lookup (typ_info_t TYPE('b::mem_type)) f 0 = Some (t,n);
      export_uinfo t = (typ_uinfo_t TYPE('a)) \<rbrakk> \<Longrightarrow>
      ((p \<mapsto>\<^sub>g update_ti_t t (to_bytes_p v) u) \<and>\<^sup>* R)
      (lift_state (heap_update (Ptr &(p\<rightarrow>f)) (v::'a::mem_type) h,d))"
apply(subst sep_map_mfs_sep_map_empty)
apply(subst sep_map_field_unfold [where g'="\<lambda>x. True"])
     apply assumption
   apply simp
  apply(simp add: guard_mono_def)
 apply  assumption
apply simp
apply(subst fd_cons_access_update_p [where w=undefined])
  apply(erule field_lookup_fd_consD)
  apply simp
 apply(simp add: export_size_of)
apply(subst wf_fd_norm_tuD [symmetric])
  apply(erule wf_fd_field_lookupD, simp)
 apply(simp add: export_size_of)
apply simp
apply(subgoal_tac "norm_tu (typ_uinfo_t TYPE('a)) = norm_bytes TYPE('a)")
 prefer 2
 apply(simp add: norm_bytes_def typ_uinfo_t_def)
apply(simp add: norm sep_conj_ac)
apply(subst sep_conj_com)
apply(subst sep_conj_assoc)+
apply(rule sep_heap_update_global_exc2 [where u="from_bytes (access_ti\<^sub>0 t u)"])
apply(simp add: sep_conj_ac)
apply(subst sep_conj_com)
apply(subst sep_map_field_fold)
     apply assumption
    apply simp+
  apply(simp add: guard_mono_def)
 apply assumption
apply simp
apply(subst  sep_map_mfs_sep_map_empty [symmetric])
apply(subst fd_cons_double_update)
  apply(erule field_lookup_fd_consD)
 apply simp
apply(subst norm_bytes)
 apply(subst fd_cons_length_p)
  apply(erule field_lookup_fd_consD)
 apply(simp add: export_size_of)
apply(simp add: norm_bytes_def typ_uinfo_t_def)
apply(rotate_tac -1)
apply(drule sym)
apply simp
apply(subst wf_fd_norm_tuD)
  apply(erule wf_fd_field_lookupD, simp)
 apply(subst fd_cons_length_p)
  apply(erule field_lookup_fd_consD)
 apply simp
apply(subst fd_cons_access_update_p [where w=u])
  apply(erule field_lookup_fd_consD)
 apply(subst fd_cons_length_p)
  apply(erule field_lookup_fd_consD)
 apply simp
apply(simp add: access_ti\<^sub>0_def)
apply(subst fd_cons_update_access)
  apply(erule field_lookup_fd_consD)
 apply simp
apply(subst fd_cons_update_access)
  apply(erule field_lookup_fd_consD)
 apply simp
apply(simp add: sep_conj_com)
done

lemma sep_cut'_dom:
  "sep_cut' x y s \<Longrightarrow> dom s = {(a,b). a \<in> {x..+y}}"
  by (simp add: sep_cut'_def)

lemma dom_exact_sep_cut':
  "dom_exact (sep_cut' x y)"
  by (force intro!: dom_exactI dest!: sep_cut'_dom)

lemma dom_lift_state_dom_s [simp]:
  "dom (lift_state (h,d)) = dom_s d"
apply(auto simp: lift_state_def dom_s_def split: s_heap_index.splits if_split_asm option.splits)
apply fast
done

lemma dom_ptr_retyp_empty_htd [simp]:
  "dom (lift_state (h,ptr_retyp (p::'a::mem_type ptr) empty_htd)) = s_footprint p"
apply simp
done

lemma ptr_retyp_sep_cut'_exc:
  fixes p::"'a::mem_type ptr"
  assumes sc: "(sep_cut' (ptr_val p) (size_of TYPE('a)) \<and>\<^sup>* P)
      (lift_state (h,d))" and "g p"
  shows "(g \<turnstile>\<^sub>s p \<and>\<^sup>* sep_true \<and>\<^sup>* P) (lift_state (h,(ptr_retyp p d)))"
proof -
  from sc obtain s\<^sub>0 and s\<^sub>1 where "s\<^sub>0 \<bottom> s\<^sub>1" and "lift_state (h,d) = s\<^sub>1 ++ s\<^sub>0"
      and "P s\<^sub>1" and d: "dom s\<^sub>0 = {(a,b). a \<in> {ptr_val p..+size_of TYPE('a)}}"
    by (fast dest: sep_conjD sep_cut'_dom)
  moreover hence "lift_state (h, ptr_retyp p d) = s\<^sub>1 ++
      lift_state (h, ptr_retyp p d) |` dom s\<^sub>0"
apply -
apply(rule ext, case_tac "x \<in> dom s\<^sub>0")
 apply(case_tac "x \<in> dom s\<^sub>1")
  apply(clarsimp simp: map_disj_def)
  apply fast
 apply(subst map_add_com)
  apply(clarsimp simp: map_disj_def)
  apply fast
 apply(clarsimp simp: map_add_def split: option.splits)
apply(case_tac x, clarsimp)
apply(clarsimp simp: lift_state_ptr_retyp_d merge_dom2)
done
  moreover have "g p" by fact
  with d have "(g \<turnstile>\<^sub>s p \<and>\<^sup>* sep_true) (lift_state (h, ptr_retyp p d) |` dom s\<^sub>0)"
apply (auto simp: lift_state_ptr_retyp_restrict sep_conj_ac intro: ptr_retyp_tagd_exc)
apply(rule_tac s\<^sub>0="lift_state (h,d) |` ({(a, b). a \<in> {ptr_val p..+size_of TYPE('a)}} - s_footprint p)" in sep_conjI)
   apply (simp add: sep_conj_ac)
  apply(erule_tac h=h in ptr_retyp_tagd_exc)
 apply(clarsimp  simp: map_disj_def)
 apply fast
apply(subst map_add_com[where h\<^sub>0="lift_state (h, ptr_retyp p empty_htd)"])
 apply (simp add: map_disj_def)
 apply fast
apply(rule ext)
apply(auto simp: map_add_def split: option.splits)
apply(subgoal_tac "(a,b) \<notin> s_footprint p")
 apply(clarsimp simp: restrict_map_def)
apply(subgoal_tac "s_footprint p = dom (lift_state (h, ptr_retyp p empty_htd) )")
 apply(simp only:)
 apply fast
apply simp
done
ultimately show ?thesis
apply -
apply(subst sep_conj_assoc [symmetric])
apply(rule_tac s\<^sub>0="(lift_state (h,ptr_retyp p d))|`dom s\<^sub>0" and s\<^sub>1=s\<^sub>1 in
          sep_conjI, auto simp: map_disj_def)
done
qed

lemma sep_cut_dom:
  "sep_cut x y s \<Longrightarrow> dom s = {(a,b). a \<in> {x..+unat y}}"
  by (force simp: sep_cut_def dest: sep_cut'_dom)

lemma sep_cut_0 [simp]:
  "sep_cut p 0 = \<box>"
  apply (rule ext)
  apply (auto simp: sep_cut'_def sep_cut_def sep_emp_def None_com split_def)
  done

lemma heap_merge_restrict_dom_un:
  "dom s = P \<union> Q \<Longrightarrow> (s|`P) ++ (s|`Q) = s"
  by (force simp: map_add_def restrict_map_def split: option.splits)

lemma sep_cut_split:
  assumes sc: "sep_cut p y s" and le: "x \<le> y"
  shows "(sep_cut p x \<and>\<^sup>* sep_cut (p + x) (y - x)) s"
proof (rule_tac s\<^sub>0="s|`{(a,b). a \<in> {p..+unat x}}" and s\<^sub>1="s|`({(a,b). a \<in> {p..+unat y}} - {(a,b). a \<in> {p..+unat x}})"
    in sep_conjI)
  from sc le show "sep_cut p x (s |` {(a,b). a \<in> {p..+unat x}})"
    by (force simp: sep_cut_def sep_cut'_def word_le_nat_alt
              dest: intvl_start_le)
next
  from sc le show "sep_cut (p + x) (y - x) (s |` ({(a,b). a \<in> {p..+unat y}} -
      {(a,b). a \<in> {p..+unat x}}))"
    by (force simp: sep_cut_def sep_cut'_def intvl_sub_eq)
next
  show "s |` {(a,b). a \<in> {p..+unat x}} \<bottom> s |` ({(a,b). a \<in> {p..+unat y}} - {(a,b). a \<in> {p..+unat x}})"
    by (force simp: map_disj_def)
next
  from sc le show "s = s |` ({(a,b). a \<in> {p..+unat y}} - {(a,b). a \<in> {p..+unat x}}) ++ s |` {(a,b). a \<in> {p..+unat x}}"
    by (simp add: sep_cut_def sep_cut'_def, subst heap_merge_restrict_dom_un)
       (auto simp: word_le_nat_alt dest: intvl_start_le)
qed

lemma tagd_ptr_safe_exc:
  "(g \<turnstile>\<^sub>s p \<and>\<^sup>* sep_true) (lift_state (h,d)) \<Longrightarrow> ptr_safe p d"
apply(clarsimp simp: ptr_safe_def sep_conj_ac sep_conj_def, drule tagd_dom_exc)
apply(drule_tac x="(a,b)" in fun_cong)
apply(auto simp: map_ac_simps lift_state_def sep_conj_ac split: option.splits s_heap_index.splits if_split_asm)
   apply(clarsimp simp: dom_s_def sep_conj_ac)
  apply(subst (asm) merge_dom)
   apply fast
  apply force
 apply(subst (asm) merge_dom)
  apply fast
 apply force
apply(clarsimp simp: dom_s_def)
done

lemma sep_map'_ptr_safe_exc:
  "(p \<hookrightarrow>\<^sub>g (v::'a::mem_type)) (lift_state (h,d)) \<Longrightarrow> ptr_safe p d"
  by (force simp: sep_map'_def intro: sep_conj_impl tagd_ptr_safe_exc
            dest: sep_map_tagd_exc)

end
