(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory TypHeapLimits
  imports CParser.TypHeapLib
begin

definition
  states_all_but_typs_eq :: "char list set \<Rightarrow> heap_raw_state \<Rightarrow> heap_raw_state \<Rightarrow> bool"
where
 "states_all_but_typs_eq names hrs hrs'
    = (hrs_htd hrs = hrs_htd hrs'
        \<and> (\<forall>x. hrs_mem hrs x = hrs_mem hrs' x
             \<or> (\<exists>p td. x \<in> {p ..+ size_td td} \<and> td_names td \<subseteq> names
                    \<and> typ_name td \<noteq> pad_typ_name
                    \<and> valid_footprint (hrs_htd hrs) p td)))"

lemma heap_list_eq_from_region_eq:
  "\<forall>x \<in> {p ..+ n}. hp x = hp' x
    \<Longrightarrow> heap_list hp n p = heap_list hp' n p"
  apply (induct n arbitrary: p)
   apply simp
  apply (simp add: intvl_def)
  apply (frule_tac x=p in spec, drule mp, rule_tac x=0 in exI,
         simp+)
  apply (erule meta_allE, erule meta_mp)
  apply clarsimp
  apply (drule spec, erule mp)
  apply (rule_tac x="Suc k" in exI)
  apply simp
  done

lemma states_all_but_typs_eq_clift:
  "\<lbrakk> states_all_but_typs_eq names hrs hrs';
      \<forall>x \<in> td_names (typ_info_t TYPE('a)). x \<notin> names;
      typ_name (typ_info_t TYPE('a)) \<noteq> pad_typ_name \<rbrakk>
     \<Longrightarrow> (clift hrs :: (_ \<rightharpoonup> ('a :: c_type))) = clift hrs'"
  apply (rule ext, simp add: lift_t_def)
  apply (cases hrs, cases hrs', clarsimp)
  apply (simp add: lift_typ_heap_def restrict_map_def)
  apply (simp add: s_valid_def proj_d_lift_state
                   states_all_but_typs_eq_def hrs_htd_def
                   hrs_mem_def)
  apply clarsimp
  apply (simp add: heap_list_s_heap_list h_t_valid_def)
  apply (subst heap_list_eq_from_region_eq, simp_all)
  apply clarsimp
  apply (drule spec, erule disjE, assumption)
  apply clarsimp
  apply (drule(1) valid_footprint_neq_disjoint)
    apply (clarsimp simp: typ_uinfo_t_def typ_tag_lt_def
                          typ_tag_le_def)
    apply (force dest: td_set_td_names
                intro: td_set_td_names[OF td_set_self])
   apply (clarsimp simp: field_of_def typ_uinfo_t_def)
   apply (force dest: td_set_td_names
               intro: td_set_td_names[OF td_set_self])
  apply (simp add: size_of_def)
  apply blast
  done

lemma states_all_but_typs_eq_refl:
  "states_all_but_typs_eq names hrs hrs"
  by (simp add: states_all_but_typs_eq_def)

lemma states_all_but_typs_eq_trans:
  "states_all_but_typs_eq names hrs hrs'
     \<Longrightarrow> states_all_but_typs_eq names hrs' hrs''
     \<Longrightarrow> states_all_but_typs_eq names hrs hrs''"
  apply (clarsimp simp add: states_all_but_typs_eq_def
                  del: disjCI)
  apply (drule_tac x=x in spec)+
  apply clarsimp
  done

lemma states_all_but_typs_eq_update:
  "\<lbrakk> hrs_htd hrs \<Turnstile>\<^sub>t (ptr :: ('a :: c_type) ptr);
      td_names (typ_info_t TYPE('a)) \<subseteq> names;
      typ_name (typ_info_t TYPE('a)) \<noteq> pad_typ_name;
      wf_fd (typ_info_t TYPE('a)) \<rbrakk>
        \<Longrightarrow>
   states_all_but_typs_eq names hrs
    (hrs_mem_update (heap_update ptr v) hrs)"
  apply (clarsimp simp: states_all_but_typs_eq_def hrs_mem_update
                   del: disjCI)
  apply (subst disj_commute, rule disjCI)
  apply (rule_tac x="ptr_val ptr" in exI)
  apply (rule_tac x="typ_uinfo_t TYPE('a)" in exI)
  apply (simp add: typ_uinfo_t_def h_t_valid_def heap_update_def)
  apply (rule ccontr)
  apply (subst(asm) heap_update_nmem_same)
   apply (simp add: to_bytes_def length_fa_ti)
   apply (subst length_fa_ti, simp_all add: size_of_def)
  done

end
