(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TcbQueue_C
imports Ctac_lemmas_C
begin

context kernel
begin

lemma tcb_at_not_NULL:
  assumes tat: "tcb_at' t s"
  shows "tcb_ptr_to_ctcb_ptr t \<noteq> NULL"
proof
  assume "tcb_ptr_to_ctcb_ptr t = NULL"
  with tat have "tcb_at' (ctcb_ptr_to_tcb_ptr NULL) s"
    apply -
    apply (erule subst)
    apply simp
    done

  hence "is_aligned (ctcb_ptr_to_tcb_ptr NULL) tcbBlockSizeBits"
    by (rule tcb_aligned')

  moreover have "ctcb_ptr_to_tcb_ptr NULL !! ctcb_size_bits"
    unfolding ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs
    by simp
  ultimately show False by (simp add: is_aligned_nth ctcb_offset_defs objBits_defs)
qed

lemma distinct_cons_nth:
  assumes dxs: "distinct xs"
  and      ln: "n < length xs"
  and      x: "x \<notin> set xs"
  shows    "(x # xs) ! n \<noteq> xs ! n"
proof
  assume n: "(x # xs) ! n = xs ! n"
  have ln': "n < length (x # xs)" using ln by simp
  have sln: "Suc n < length (x # xs)" using ln by simp

  from n have "(x # xs) ! n = (x # xs) ! Suc n" by simp
  moreover have "distinct (x # xs)" using dxs x by simp
  ultimately show False
    unfolding distinct_conv_nth
    apply -
    apply (drule spec, drule mp [OF _ ln'])
    apply (drule spec, drule mp [OF _ sln])
    apply simp
    done
qed

lemma distinct_nth:
  assumes dist: "distinct xs"
  and     ln: "n < length xs"
  and     lm: "m < length xs"
  shows   "(xs ! n = xs ! m) = (n = m)"
  using dist ln lm
  apply (cases "n = m")
   apply simp
  apply (clarsimp simp: distinct_conv_nth)
  done

lemma distinct_nth_cons:
  assumes dist: "distinct xs"
  and     xxs: "x \<notin> set xs"
  and     ln: "n < length xs"
  and     lm: "m < length xs"
  shows   "((x # xs) ! n = xs ! m) = (n = Suc m)"
proof (cases "n = Suc m")
  case True
  thus ?thesis by simp
next
  case False

  have ln': "n < length (x # xs)" using ln by simp
  have lm': "Suc m < length (x # xs)" using lm by simp

  have "distinct (x # xs)" using dist xxs by simp
  thus ?thesis using False
    unfolding distinct_conv_nth
    apply -
    apply (drule spec, drule mp [OF _ ln'])
    apply (drule spec, drule mp [OF _ lm'])
    apply clarsimp
    done
qed

lemma distinct_nth_cons':
  assumes dist: "distinct xs"
  and     xxs: "x \<notin> set xs"
  and     ln: "n < length xs"
  and     lm: "m < length xs"
  shows   "(xs ! n = (x # xs) ! m) = (m = Suc n)"
proof (cases "m = Suc n")
  case True
  thus ?thesis by simp
next
  case False

  have ln': "Suc n < length (x # xs)" using ln by simp
  have lm': "m < length (x # xs)" using lm by simp

  have "distinct (x # xs)" using dist xxs by simp
  thus ?thesis using False
    unfolding distinct_conv_nth
    apply -
    apply (drule spec, drule mp [OF _ ln'])
    apply (drule spec, drule mp [OF _ lm'])
    apply clarsimp
    done
qed

lemma nth_first_not_member:
  assumes xxs: "x \<notin> set xs"
  and     ln: "n < length xs"
  shows   "((x # xs) ! n = x) = (n = 0)"
  using xxs ln
  apply (cases n)
   apply simp
  apply clarsimp
  done

lemma distinct_remove1_take_drop:
  "\<lbrakk> distinct ls; n < length ls \<rbrakk> \<Longrightarrow> remove1 (ls ! n) ls = (take n ls) @ drop (Suc n) ls"
proof (induct ls arbitrary: n)
  case Nil thus ?case by simp
next
  case (Cons x xs n)

  show ?case
  proof (cases n)
    case 0
    thus ?thesis by simp
  next
    case (Suc m)

    hence "((x # xs) ! n) \<noteq> x" using Cons.prems by clarsimp
    thus ?thesis using Suc Cons.prems by (clarsimp simp add: Cons.hyps)
  qed
qed


definition
  "upd_unless_null \<equiv> \<lambda>p v f. if p = NULL then f else fun_upd f p (Some v)"

lemma upd_unless_null_cong_helper:
  "\<And>p p' v mp S. \<lbrakk> p' \<in> tcb_ptr_to_ctcb_ptr ` S; ctcb_ptr_to_tcb_ptr p \<notin> S \<rbrakk> \<Longrightarrow> (upd_unless_null p v mp) p' = mp p'"
  unfolding upd_unless_null_def
  apply simp
  apply (intro impI conjI)
  apply (erule imageE)
  apply hypsubst
  apply (simp only: ctcb_ptr_to_ctcb_ptr)
  apply blast
  done

lemma ctcb_ptr_to_tcb_ptr_aligned:
  assumes al: "is_aligned (ctcb_ptr_to_tcb_ptr ptr) tcbBlockSizeBits"
  shows   "is_aligned (ptr_val ptr) ctcb_size_bits"
proof -
  have "is_aligned (ptr_val (tcb_ptr_to_ctcb_ptr (ctcb_ptr_to_tcb_ptr ptr))) ctcb_size_bits"
    unfolding tcb_ptr_to_ctcb_ptr_def using al
    apply simp
    apply (erule aligned_add_aligned)
    apply (unfold ctcb_offset_defs, rule is_aligned_triv)
    apply (simp add: word_bits_conv objBits_defs)+
    done
  thus ?thesis by simp
qed

lemma ctcb_size_bits_ge_4: "4 \<le> ctcb_size_bits"
  by (simp add: ctcb_size_bits_def)

lemma cvariable_relation_upd_const:
  "m x \<noteq> None
    \<Longrightarrow> cvariable_array_map_relation (m (x \<mapsto> y)) (\<lambda>x. n)
        = cvariable_array_map_relation m (\<lambda>x. n)"
  by (auto simp: fun_eq_iff cvariable_array_map_relation_def)

lemma ptr_span_ctcb_subset:
  "is_aligned p tcbBlockSizeBits \<Longrightarrow> ptr_span (tcb_ptr_to_ctcb_ptr p) \<subseteq> {p .. p + 2^tcbBlockSizeBits-1}"
  apply (simp add: tcb_ptr_to_ctcb_ptr_def ctcb_offset_def)
  apply (frule aligned_add_aligned[where m=ctcb_size_bits, OF _ is_aligned_triv],
         simp add: objBits_defs ctcb_size_bits_def)
  apply (subst upto_intvl_eq'; clarsimp)
   apply (erule is_aligned_no_wrap', simp add: ctcb_size_bits_def)
  apply (rule conjI)
   apply (erule is_aligned_no_wrap', simp add: objBits_defs ctcb_size_bits_def)
  apply (cut_tac word_add_le_mono1[where k=p and j="2^tcbBlockSizeBits-1"])
    apply (simp add: field_simps)
   apply (simp add: objBits_defs ctcb_size_bits_def)
  apply (subst field_simps, subst unat_plus_simple[where x=p, THEN iffD1, symmetric])
   apply (erule is_aligned_no_overflow')
  apply (rule unat_lt2p)
  done

(* FIXME: move *)
lemma tcb_at'_non_kernel_data_ref:
  "pspace_domain_valid s \<Longrightarrow> tcb_at' p s \<Longrightarrow> ptr_span (tcb_ptr_to_ctcb_ptr p) \<inter> kernel_data_refs = {}"
  apply (rule disjoint_subset[OF ptr_span_ctcb_subset])
   apply (erule tcb_aligned')
  apply (drule map_to_tcbs_from_tcb_at)
  apply (clarsimp simp: pspace_domain_valid_def map_comp_def split: option.splits)
  apply (drule spec, drule spec, drule (1) mp)
  apply (simp add: objBits_simps add_mask_fold)
  done

lemmas tcb_at'_non_kernel_data_ref'
  = tcb_at'_non_kernel_data_ref[OF invs'_pspace_domain_valid]

(* FIXME: move near tag_disj_via_td_name *)
lemma tag_not_less_via_td_name:
  assumes ta: "typ_name (typ_info_t TYPE('a)) \<noteq> pad_typ_name"
  assumes tina: "typ_name (typ_info_t TYPE('a)) \<notin> td_names (typ_info_t TYPE('b))"
  shows   "\<not> typ_uinfo_t TYPE('a::c_type) < typ_uinfo_t TYPE('b::c_type)"
  using assms
  by (auto simp: sub_typ_proper_def typ_tag_lt_def typ_simps dest: td_set_td_names)

(* FIXME: move *)
lemma td_set_map_td_commute[rule_format]:
  "\<forall>i. td_set (map_td f t) i = apfst (map_td f) ` td_set t i"
  "\<forall>i. td_set_struct (map_td_struct f st) i = apfst (map_td f) ` td_set_struct st i"
  "\<forall>i. td_set_list (map_td_list f ts) i = apfst (map_td f) ` td_set_list ts i"
  "\<forall>i. td_set_pair (map_td_pair f tp') i = apfst (map_td f) ` td_set_pair tp' i"
  apply (induct t and st and ts and tp')
  apply simp_all
  apply (case_tac dt_pair; clarsimp simp: image_Un)
  done

(* FIXME: move *)
lemma td_set_export_uinfo_eq:
  "td_set (export_uinfo t) i = apfst export_uinfo ` td_set t i"
  unfolding export_uinfo_def by (rule td_set_map_td_commute)

(* FIXME: move *)
lemma td_set_adjust_ti_eq:
  "td_set (adjust_ti t a b) i = apfst (\<lambda>t. adjust_ti t a b) ` td_set t i"
  unfolding adjust_ti_def by (rule td_set_map_td_commute)

(* FIXME: move *)
lemma td_set_list_app:
  "td_set_list (ts @ ts') i = td_set_list ts i \<union> td_set_list ts' (i + size_td_list ts)"
  apply (induct ts arbitrary: i, simp)
  apply (rename_tac p ps i, case_tac p, simp add: Un_assoc field_simps)
  done

(* FIXME: move *)
lemma apfst_comp:
  "apfst f \<circ> apfst g = apfst (f \<circ> g)"
  by auto

lemma td_set_offset_wf[rule_format]:
  fixes td :: "'a typ_desc"
    and st :: "'a typ_struct"
    and ts :: "('a typ_desc, char list) dt_pair list"
    and tp :: "('a typ_desc, char list) dt_pair"
  shows "\<forall>s n m. (s, n) \<in> td_set td m \<longrightarrow> m \<le> n"
        "\<forall>s n m. (s, n) \<in> td_set_struct st m \<longrightarrow> m \<le> n"
        "\<forall>s n m. (s, n) \<in> td_set_list ts m \<longrightarrow> m \<le> n"
        "\<forall>s n m. (s, n) \<in> td_set_pair tp m \<longrightarrow> m \<le> n"
  apply (induct td and st and ts and tp)
  apply simp_all
  apply (case_tac dt_pair; fastforce)
  done

lemma field_lookup_offset_wf[rule_format]:
  fixes td :: "'a typ_desc"
    and st :: "'a typ_struct"
    and ts :: "('a typ_desc, char list) dt_pair list"
    and tp :: "('a typ_desc, char list) dt_pair"
  shows "\<forall>s n m f. field_lookup td f m = Some (s, n) \<longrightarrow> m \<le> n"
        "\<forall>s n m f. field_lookup_struct st f m = Some (s, n) \<longrightarrow> m \<le> n"
        "\<forall>s n m f. field_lookup_list ts f m = Some (s, n) \<longrightarrow> m \<le> n"
        "\<forall>s n m f. field_lookup_pair tp f m = Some (s, n) \<longrightarrow> m \<le> n"
  apply (induct td and st and ts and tp)
  apply simp_all
  apply (fastforce split: option.splits)+
  done

lemma td_set_field_lookup_wf[rule_format]:
  fixes td :: "'a typ_desc"
    and st :: "'a typ_struct"
    and ts :: "('a typ_desc, char list) dt_pair list"
    and tp :: "('a typ_desc, char list) dt_pair"
  shows "\<forall>k m. wf_desc td \<longrightarrow> k \<in> td_set td m \<longrightarrow> (\<exists>f. field_lookup td f m = Some k)"
        "\<forall>k m. wf_desc_struct st \<longrightarrow> k \<in> td_set_struct st m \<longrightarrow> (\<exists>f. field_lookup_struct st f m = Some k)"
        "\<forall>k m. wf_desc_list ts \<longrightarrow> k \<in> td_set_list ts m \<longrightarrow> (\<exists>f. field_lookup_list ts f m = Some k)"
        "\<forall>k m. wf_desc_pair tp \<longrightarrow> k \<in> td_set_pair tp m \<longrightarrow> (\<exists>f. field_lookup_pair tp f m = Some k)"
  using td_set_field_lookup'[of td st ts tp]
  apply -
  apply (clarsimp, frule td_set_offset_wf, drule spec, drule spec, drule spec, drule mp,
         erule rsubst[where P="\<lambda>n. (s,n) \<in> td_set" for s td_set], subst add_diff_inverse_nat,
         simp add: not_less, simp, simp)+
  done

lemma td_set_image_field_lookup:
  "wf_desc td \<Longrightarrow> k \<in> f ` td_set td m \<Longrightarrow> (\<exists>fn. option_map f (field_lookup td fn m) = Some k)"
  "wf_desc_struct st \<Longrightarrow> k \<in> f ` td_set_struct st m \<Longrightarrow> (\<exists>fn. option_map f (field_lookup_struct st fn m) = Some k)"
  "wf_desc_list ts \<Longrightarrow> k \<in> f ` td_set_list ts m \<Longrightarrow> (\<exists>fn. option_map f (field_lookup_list ts fn m) = Some k)"
  "wf_desc_pair tp' \<Longrightarrow> k \<in> f ` td_set_pair tp' m \<Longrightarrow> (\<exists>fn. option_map f (field_lookup_pair tp' fn m) = Some k)"
  by (fastforce simp: image_def dest: td_set_field_lookup_wf)+

lemma field_lookup_td_set[rule_format]:
  fixes td :: "'a typ_desc"
    and st :: "'a typ_struct"
    and ts :: "('a typ_desc, char list) dt_pair list"
    and tp :: "('a typ_desc, char list) dt_pair"
  shows "\<forall>k m f. field_lookup td f m = Some k \<longrightarrow> k \<in> td_set td m"
        "\<forall>k m f. field_lookup_struct st f m = Some k \<longrightarrow> k \<in> td_set_struct st m"
        "\<forall>k m f. field_lookup_list ts f m = Some k \<longrightarrow> k \<in> td_set_list ts m"
        "\<forall>k m f. field_lookup_pair tp f m = Some k \<longrightarrow> k \<in> td_set_pair tp m"
  using td_set_field_lookup_rev'[of td st ts tp]
  apply -
  apply (clarsimp, frule field_lookup_offset_wf, drule spec, drule spec, drule spec, drule mp,
         rule exI, erule rsubst[where P="\<lambda>n. f = Some (s,n)" for f s], subst add_diff_inverse_nat,
         simp add: not_less, simp, simp)+
  done

lemma field_lookup_list_Some:
  assumes "wf_desc_list ts"
  assumes "field_lookup_list ts (fn # fns') m = Some (s, n)"
  shows "\<exists>td' m'. field_lookup_list ts [fn] m = Some (td', m') \<and> field_lookup td' fns' m' = Some (s, n)"
  using assms
  apply (induct ts arbitrary: m, simp)
  apply (rename_tac tp ts m, case_tac tp)
  apply (clarsimp split: if_splits option.splits simp: field_lookup_list_None)
  done

lemma field_lookup_Some_cases:
  assumes "wf_desc td"
  assumes "field_lookup td fns m = Some (s,n)"
  shows "case fns of
              [] \<Rightarrow> s = td \<and> m = n
            | fn # fns' \<Rightarrow> \<exists>td' m'. field_lookup td [fn] m = Some (td',m')
                                  \<and> field_lookup td' fns' m' = Some (s,n)"
  using assms
  apply (cases fns; simp)
  apply (cases td, rename_tac fn fns' st tn, clarsimp)
  apply (case_tac st; clarsimp simp: field_lookup_list_Some)
  done

lemma field_lookup_SomeE:
  assumes lookup: "field_lookup td fns m = Some (s,n)"
  assumes wf: "wf_desc td"
  assumes nil: "\<lbrakk> fns = []; s = td; m = n \<rbrakk> \<Longrightarrow> P"
  assumes some: "\<And>fn fns' td' m'. \<lbrakk> fns = fn # fns'; field_lookup td [fn] m = Some (td',m');
                                      field_lookup td' fns' m' = Some (s,n) \<rbrakk> \<Longrightarrow> P"
  shows P
  using field_lookup_Some_cases[OF wf lookup]
  by (cases fns) (auto simp add: nil some)

lemmas typ_combine_simps =
  ti_typ_pad_combine_def[where tag="TypDesc st tn" for st tn]
  ti_typ_combine_def[where tag="TypDesc st tn" for st tn]
  ti_pad_combine_def[where tag="TypDesc st tn" for st tn]
  align_td_array' size_td_array
  CompoundCTypes.field_names_list_def
  empty_typ_info_def
  final_pad_def padup_def
  align_of_def

bundle typ_combine_bundle =
  typ_combine_simps[simp]
  if_weak_cong[cong]

schematic_goal tcb_C_typ_info_unfold:
  "typ_info_t (?t :: tcb_C itself) = TypDesc ?st ?tn"
  including typ_combine_bundle by (simp add: tcb_C_typ_info tcb_C_tag_def)

schematic_goal arch_tcb_C_typ_info_unfold:
  "typ_info_t (?t :: arch_tcb_C itself) = TypDesc ?st ?tn"
  including typ_combine_bundle by (simp add: arch_tcb_C_typ_info arch_tcb_C_tag_def)

schematic_goal user_context_C_typ_info_unfold:
  "typ_info_t (?t :: user_context_C itself) = TypDesc ?st ?tn"
  including typ_combine_bundle by (simp add: user_context_C_typ_info user_context_C_tag_def)

lemma rf_sr_tcb_update:
  "\<lbrakk> (s, s') \<in> rf_sr;
     ko_at' tcb thread s;
     t_hrs_' (globals t) = hrs_mem_update (heap_update (tcb_ptr_to_ctcb_ptr thread) ctcb)
                                          (t_hrs_' (globals s'));
     (\<forall>x\<in>ran tcb_cte_cases. (\<lambda>(getF, setF). getF tcb' = getF tcb) x);
     ctcb_relation tcb' ctcb
   \<rbrakk>
  \<Longrightarrow> (s\<lparr>ksPSpace := (ksPSpace s)(thread \<mapsto> KOTCB tcb')\<rparr>,
       t'\<lparr>globals := globals s'\<lparr>t_hrs_' := t_hrs_' (globals t)\<rparr>\<rparr>) \<in> rf_sr"
  unfolding rf_sr_def state_relation_def cstate_relation_def cpspace_relation_def
  apply (clarsimp simp: Let_def update_tcb_map_tos map_to_ctes_upd_tcb_no_ctes
                        heap_to_user_data_def)
  apply (frule (1) cmap_relation_ko_atD)
  apply (erule obj_atE')
  apply clarsimp
  apply (clarsimp simp: map_comp_update projectKO_opt_tcb cvariable_relation_upd_const
                        typ_heap_simps')
  apply (intro conjI)
     subgoal by (clarsimp simp: cmap_relation_def map_comp_update projectKO_opts_defs inj_eq)
    subgoal
      by (clarsimp simp: map_comp_update projectKO_opt_sc typ_heap_simps' refill_buffer_relation_def)
   subgoal by (clarsimp simp: carch_state_relation_def typ_heap_simps')
  by (simp add: cmachine_state_relation_def)

lemmas rf_sr_tcb_update2 = rf_sr_obj_update_helper[OF rf_sr_tcb_update, simplified]

end
end
