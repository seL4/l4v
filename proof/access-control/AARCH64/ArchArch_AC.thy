(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchArch_AC
imports Arch_AC
begin

text\<open>

Arch-specific access control.

\<close>

context Arch begin arch_global_naming

named_theorems Arch_AC_assms

lemma set_mrs_state_vrefs[Arch_AC_assms, wp]:
  "set_mrs thread buf msgs \<lbrace>\<lambda>s :: det_state. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_mrs_def split_def set_object_def get_object_def split del: if_split)
  apply (wpsimp wp: gets_the_wp get_wp put_wp mapM_x_wp'
              simp: zipWithM_x_mapM_x split_def store_word_offs_def
         split_del: if_split)
  apply (subst (asm) state_vrefs_tcb_upd[symmetric])
   apply (auto simp: fun_upd_def get_tcb_def tcb_at_def)
  done

lemma mul_add_word_size_lt_msg_align_bits_ofnat[Arch_AC_assms]:
  "\<lbrakk> p < 2 ^ (msg_align_bits - word_size_bits); k < word_size \<rbrakk>
     \<Longrightarrow> of_nat p * of_nat word_size + k < (2 :: obj_ref) ^ msg_align_bits"
  apply (rule is_aligned_add_less_t2n[where n=word_size_bits])
     apply (simp_all add: msg_align_bits' word_size_word_size_bits is_aligned_mult_triv2)
   apply (simp_all add: word_size_word_size_bits word_size_bits_def)
  apply (erule word_less_power_trans_ofnat[where k=3 and m=10, simplified], simp)
  done

lemma zero_less_word_size[Arch_AC_assms, simp]:
    "0 < (word_size :: obj_ref)"
  by (simp add: word_size_def)

declare set_mrs_state_hyp_refs_of[Arch_AC_assms]
declare storeWord_respects[Arch_AC_assms]

end


global_interpretation Arch_AC_1?: Arch_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Arch_AC_assms)?)
qed


context Arch begin arch_global_naming

definition level_of_table :: "obj_ref \<Rightarrow> 'z :: state_ext state \<Rightarrow> vm_level"
  where
  "level_of_table p s \<equiv>
     GREATEST lvl. \<exists>asid vref. vref \<in> user_region \<and> vs_lookup_table lvl asid vref s = Some (lvl, p)"

lemma level_of_table_vs_lookup_table:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     ptes_of s pt_t p = Some pte; level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk>
     \<Longrightarrow> level_of_table p s = level"
  apply (subst level_of_table_def)
  apply (rule Greatest_equality, fastforce)
  apply (case_tac "y = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid)
  apply (fastforce dest: vs_lookup_table_unique_level)
  done

lemma vs_lookup_slot_level_of_slot:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, p);
     ptes_of s pt_t p = Some pte; level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk>
     \<Longrightarrow> level_of_slot asid vref p s = level"
  apply (subst level_of_slot_def)
  apply (rule Greatest_equality)
   apply clarsimp
  apply (case_tac "y = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid)
  apply (fastforce dest: vs_lookup_slot_unique_level)
  done

lemma pool_for_asid_vs_lookupD:
  "pool_for_asid asid s = Some p \<Longrightarrow>
   vs_lookup_table asid_pool_level asid vref s = Some (asid_pool_level, p)"
  by (simp add: pool_for_asid_vs_lookup)

lemma vs_lookup_table_vref_independent:
  "\<lbrakk> vs_lookup_table level asid vref s = opt; level \<ge> max_pt_level \<rbrakk>
     \<Longrightarrow> vs_lookup_table level asid vref' s = opt"
  by (cases "level = asid_pool_level"; clarsimp simp: vs_lookup_table_def)

lemma state_vrefs_store_NonPageTablePTE:
  "\<lbrakk> invs s; is_aligned p pte_bits; vs_lookup_slot level asid vref s = Some (level, p);
     vref \<in> user_region; \<not> is_PageTablePTE pte; pts_of s (table_base (pt_type pt) p) = Some pt \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := (kheap s)(table_base (pt_type pt) p \<mapsto>
                                     ArchObj (PageTable (pt_upd pt (table_index (pt_type pt) p) pte))
                                    )\<rparr>) =
         (\<lambda>x. if \<exists>level' vref'. vref_for_level vref' (level + 1) = vref_for_level vref (level + 1) \<and>
                                vref' \<in> user_region \<and> p = pt_slot_offset level (table_base (pt_type pt) p) vref' \<and>
                                pt_walk level level' (table_base (pt_type pt) p) vref' (ptes_of s) = Some (level',x)
              then (if x = table_base (pt_type pt) p
                    then vs_refs_aux level (PageTable (pt_upd pt (table_index (pt_type pt) p) pte))
                    else {})
              else state_vrefs s x)"
  apply (rule all_ext)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce simp: vs_lookup_slot_def vs_lookup_table_def
                          ptes_of_Some pts_of_Some aobjs_of_Some
                    dest: pool_for_asid_no_pte)
  apply (frule vs_lookup_slot_level_type)
         apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)+
  apply (prop_tac "ptes_of s (pt_type pt) p \<noteq> None")
   apply (drule valid_vspace_objs_strong_slotD; clarsimp simp: ptes_of_Some pts_of_Some aobjs_of_Some)
  apply (frule vs_lookup_slot_table_base; clarsimp split del: if_split)
  apply (subst (asm) ptes_of_Some)
  apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp split del: if_split)
  apply safe
   apply (subst (asm) state_vrefs_def)+
   apply (clarsimp split: option.splits split del: if_split)
   apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and s'="kheap_update _ s" and p=p])
             apply ((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                             intro: ptes_of_pts_of_upd
                              dest: pte_ptr_eq split: if_splits
                    | clarsimp simp: opt_map_def fun_upd_def split: option.splits)+; fail)+

   apply (frule pts_of_ptes_of; clarsimp)
   apply (case_tac "x = table_base (pt_type pt) p"; clarsimp)
    apply (case_tac "lvl = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid[OF vs_lookup_level, where pt_t="pt_type pt"]
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some split: if_splits)
    apply (fastforce dest: vs_lookup_table_unique_level[OF vs_lookup_level]
                     elim: allE[where x=level] split: if_splits)
   apply (clarsimp split: if_splits)
    apply (case_tac "level' = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
    apply (frule vs_lookup_slot_level_of_slot)
        apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some split: option.splits)
       apply fastforce+
    apply (subst (asm) vs_lookup_slot_table_unfold)
       apply fastforce+
    apply clarsimp
    apply (metis (no_types, lifting) vs_lookup_slot_table_unfold vs_lookup_slot_unique_level)
   apply (rule conjI; clarsimp)
    apply (case_tac "level' < level")
     apply (subst (asm) vs_lookup_vref_for_level_eq1, rule sym, assumption)
     apply (frule (2) vs_lookup_table_extend)
     apply (case_tac "lvl = asid_pool_level")
      apply (fastforce dest: vs_lookup_table_pt_at vs_lookup_asid_pool
                       simp: asid_pools_of_ko_at obj_at_def)
     apply (frule_tac level=lvl in vs_lookup_level)
     apply (drule (1) vs_lookup_table_unique_level, rule refl)
          apply fastforce+
     apply (frule vm_level.plus_one_leq)
     apply (erule_tac x=level in allE)
     apply (subst (asm) vs_lookup_slot_vref_for_level[symmetric], assumption)
     apply (frule_tac bot_level=bot in vs_lookup_min_level)
     apply (fastforce simp: vs_lookup_slot_vref_for_level vs_lookup_slot_table_unfold)
    apply (subst (asm) pt_walk.simps, clarsimp)
   apply (fastforce simp: state_vrefs_def opt_map_def)
  apply (prop_tac "level_of_slot asid vref p s = level")
   apply (fastforce simp: vs_lookup_slot_table_unfold  ptes_of_Some intro: vs_lookup_slot_level_of_slot)
  apply (clarsimp split: if_splits)
   apply (rule state_vrefsD)
      apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
                apply ((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                                 intro: ptes_of_pts_of_upd
                                  dest: pte_ptr_eq split: if_splits
                        | clarsimp simp: opt_map_def fun_upd_def split: option.splits)+; fail)+
  apply (case_tac "x = table_base (pt_type pt) p")
   apply (fastforce elim: allE[where x=level])
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule_tac level=lvl and asid=asida and vref=vrefa in state_vrefsD)
     apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
               apply ((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                                intro: ptes_of_pts_of_upd
                                 dest: pte_ptr_eq split: if_splits
                       | clarsimp simp: opt_map_def fun_upd_def split: option.splits)+; fail)+
     apply (clarsimp split: if_splits)
     apply (intro conjI; clarsimp)
      apply (case_tac "level' = asid_pool_level")
       apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
      apply (case_tac "lvl < level")
       apply (drule_tac bot_level=bot in vs_lookup_level)
       apply (subst (asm) vs_lookup_split_Some, erule dual_order.strict_implies_order)
        apply fastforce
       apply (frule vs_lookup_slot_level_type)
              apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)+
       apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
       apply (drule (1) vs_lookup_table_unique_level; fastforce)
      apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
      apply (metis vs_lookup_slot_table vs_lookup_slot_unique_level)
     apply (fastforce dest: vs_lookup_level)
    apply (fastforce simp: aobjs_of_Some opt_map_def)
   apply clarsimp
  apply clarsimp
  done

lemma state_vrefs_store_NonPageTablePTE':
  "\<lbrakk> invs s; is_aligned p pte_bits; \<not> is_PageTablePTE pte;
     pts_of s (table_base (pt_type pt) p) = Some pt;
     \<forall>level asid vref. vref \<in> user_region \<longrightarrow> vs_lookup_slot level asid vref s \<noteq> Some (level, p) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := (kheap s)(table_base (pt_type pt) p \<mapsto>
                                     ArchObj (PageTable (pt_upd pt (table_index (pt_type pt) p) pte))
                                    )\<rparr>) =
         (\<lambda>x. if x = table_base (pt_type pt) p \<and> (\<exists>level. \<exists>\<rhd> (level, table_base (pt_type pt) p) s)
              then vs_refs_aux (level_of_table (table_base (pt_type pt) p) s)
                               (PageTable (pt_upd pt (table_index (pt_type pt) p) pte))
              else state_vrefs s x)"
  apply (rule all_ext)
  apply safe
   apply (frule pts_of_ptes_of; clarsimp)
   apply (subst (asm) state_vrefs_def)+
   apply (clarsimp split: option.splits split del: if_split)
   apply (clarsimp split: if_split_asm option.splits split del: if_split)
    apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
              apply ((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                              intro: ptes_of_pts_of_upd
                               dest: pte_ptr_eq split: if_splits
                     | clarsimp simp: opt_map_def fun_upd_def split: option.splits)+; fail)+
    apply (clarsimp split: if_splits)
    apply (drule vs_lookup_level)
    apply (rule conjI; clarsimp)
    apply (case_tac "level = asid_pool_level")
     apply (clarsimp simp: ptes_of_Some pts_of_Some)
     apply (fastforce dest: vs_lookup_table_pt_at vs_lookup_asid_pool
                      simp: asid_pools_of_ko_at obj_at_def opt_map_def)
    apply (case_tac "lvl = asid_pool_level")
      apply (fastforce dest: vs_lookup_table_pt_at vs_lookup_asid_pool
                       simp: asid_pools_of_ko_at obj_at_def)
    apply (subst level_of_table_vs_lookup_table[where pt_t="pt_type pt"]; fastforce)
   apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
             apply ((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                                           intro: ptes_of_pts_of_upd
                                            dest: pte_ptr_eq split: if_splits
                                  | clarsimp simp: opt_map_def fun_upd_def split: option.splits)+; fail)+
   apply (fastforce simp: state_vrefs_def aobjs_of_Some)
  apply (clarsimp split: if_splits)
   apply (case_tac "level = asid_pool_level")
     apply (clarsimp simp: ptes_of_Some pts_of_Some)
     apply (fastforce dest: vs_lookup_table_pt_at vs_lookup_asid_pool
                      simp: asid_pools_of_ko_at obj_at_def opt_map_def)
   apply (subst (asm) level_of_table_vs_lookup_table[where pt_t="pt_type pt"])
        apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)+
   apply (rule state_vrefsD)
      apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
                apply ((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                                                          intro: ptes_of_pts_of_upd
                                                           dest: pte_ptr_eq split: if_splits
                                                 | clarsimp simp: opt_map_def fun_upd_def split: option.splits)+; fail)+
  apply (case_tac "x = table_base (pt_type pt) p")
   apply (fastforce dest: vs_lookup_level simp: state_vrefs_def)
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule state_vrefsD)
     apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
               apply ((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                                                                        intro: ptes_of_pts_of_upd
                                                                         dest: pte_ptr_eq split: if_splits
                                                               | clarsimp simp: opt_map_def fun_upd_def split: option.splits)+; fail)+
  done

(* FIXME: make this less ugly *)
lemma state_vrefs_store_NonPageTablePTE_wp:
  "\<lbrace>\<lambda>s. invs s \<and> \<not> is_PageTablePTE pte \<and>
        (\<forall>pt. pts_of s (table_base pt_t p) = Some pt \<and> pt_t = pt_type pt \<and> is_aligned p pte_bits \<longrightarrow>
              (if \<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region
               then (\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region \<and>
                                       P (\<lambda>x. (if \<exists>level' vref'. vref_for_level vref' (level + 1) = vref_for_level vref (level + 1) \<and>
                                                                 vref' \<in> user_region \<and> p = pt_slot_offset level (table_base pt_t p) vref' \<and>
                                                                 pt_walk level level' (table_base pt_t p) vref' (ptes_of s) = Some (level', x)
                                               then (if x = table_base pt_t p
                                                     then vs_refs_aux level (PageTable (pt_upd pt (table_index pt_t p) pte))
                                                     else {})
                                               else state_vrefs s x)))
               else P (\<lambda>x. (if x = table_base pt_t p \<and> (\<exists>level. \<exists>\<rhd> (level, table_base pt_t p) s)
                            then vs_refs_aux (level_of_table (table_base pt_t p) s) (PageTable (pt_upd pt (table_index pt_t p) pte))
                            else state_vrefs s x))))\<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (case_tac "\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and>
                                     vref \<in> user_region")
   apply clarsimp
   apply (erule_tac x=pt in allE)
   apply (subst state_vrefs_store_NonPageTablePTE)
         apply fastforce+
    apply (clarsimp simp: obj_at_def pts_of_Some aobjs_of_Some)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
   apply (clarsimp simp: pts_of_Some aobjs_of_Some obj_at_def)
   apply (case_tac "levela = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
   apply (drule (1) vs_lookup_slot_unique_level)
         apply fastforce+
   apply clarsimp
   apply (frule_tac level'="level+1" in vref_for_level_eq_mono)
    apply (fastforce intro: vm_level_less_le_1)
   apply clarsimp
  apply (erule_tac x=pt in allE)
  apply (subst state_vrefs_store_NonPageTablePTE'; fastforce simp: obj_at_def aobjs_of_Some pts_of_Some)
  done

lemma store_pte_thread_st_auth[wp]:
  "store_pte pt_t p pte \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: get_tcb_def thread_st_auth_def tcb_states_of_state_def obj_at_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma store_pte_thread_bound_ntfns[wp]:
  "store_pte pt_t p pte \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: get_tcb_def thread_bound_ntfns_def  obj_at_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma store_pte_domains_of_state[wp]:
  "store_pte pt_t p pte \<lbrace>\<lambda>s. P (domains_of_state s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (erule_tac P=P in back_subst)
  apply (auto simp: domains_of_state_aux.simps etcbs_of'_def obj_at_def split: if_splits)
  done

lemma mapM_x_store_pte_caps_of_state[wp]:
  "mapM_x (swp (store_pte pt_t) InvalidPTE) slots \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

lemma state_bits_to_policy_refs_subseteq:
  "\<And>cdt. \<lbrakk> x \<in> state_bits_to_policy caps ts tbn cdt vrefs hrefs;
           caps = caps'; ts = ts'; tbn = tbn'; cdt = cdt';
           \<forall>x. vrefs x \<subseteq> vrefs' x; \<forall>x. hrefs x \<subseteq> hrefs' x \<rbrakk>
           \<Longrightarrow> x \<in> state_bits_to_policy caps' ts' tbn' cdt' vrefs' hrefs'"
  apply (cases x; clarsimp)
  apply (erule state_bits_to_policy.cases)
  by (fastforce elim: state_bits_to_policy.intros)+

lemma state_asids_to_policy_vrefs_subseteq:
  "\<lbrakk> x \<in> state_asids_to_policy_aux aag caps asid_tab vrefs; caps = caps';
     \<forall>x. vrefs x \<subseteq> state_vrefs s x; \<forall>x y. asid_tab x = Some y \<longrightarrow> asid_table s x = Some y \<rbrakk>
     \<Longrightarrow> x \<in> state_asids_to_policy_aux aag caps' (asid_table s) (state_vrefs s)"
  apply (cases x; clarsimp)
  apply (erule state_asids_to_policy_aux.cases; fastforce intro: state_asids_to_policy_aux.intros)
  done

lemma vs_lookup_table_subseteq:
    "\<lbrakk> vs_lookup_table bot_level asid vref s' = Some (lvl,ptr);
       \<forall>pptr. pool_for_asid asid s' = Some pptr \<longrightarrow> pool_for_asid asid s = Some pptr;
       \<forall>pptr vref. vspace_for_pool pptr asid (asid_pools_of s') = Some vref
               \<longrightarrow> vspace_for_pool pptr asid (asid_pools_of s) = Some vref;
       ptes_of s' = ptes_of s \<rbrakk>
   \<Longrightarrow> vs_lookup_table bot_level asid vref s = Some (lvl,ptr)"
   by (auto simp: vs_lookup_table_def in_obind_eq split: if_splits)

lemma vs_refs_aux_subseteq:
  assumes "\<forall>asid vref. vspace_for_pool 0 asid (K (asid_pool_of ao')) = Some vref
                   \<longrightarrow> vspace_for_pool 0 asid (K (asid_pool_of ao)) = Some vref"
  and "\<forall>idx vref. option_map (swp pt_apply idx) (pt_of ao') = Some vref
              \<longrightarrow> option_map (swp pt_apply idx) (pt_of ao) = Some vref"
  and "aa_type ao' = aa_type ao"
  shows "vs_refs_aux lvl ao' \<subseteq> vs_refs_aux lvl ao"
  apply (insert assms)
  apply (case_tac ao'; case_tac ao;
         clarsimp simp: vs_refs_aux_def graph_of_def image_iff pt_type_def
                 split: pt.splits if_splits)
    apply (erule_tac x="ucast ac" in allE)
    apply (fastforce simp: asid_low_bits_of_def vspace_for_pool_def
                           entry_for_pool_def in_obind_eq ucast_ucast_id)
   apply (erule_tac x="ucast ac" in allE)
   apply (intro exI conjI; fastforce simp: ucast_ucast_id vs_index_bits_def)
  apply (erule_tac x="ucast ac" in allE)
  apply (intro exI conjI; fastforce simp: ucast_ucast_id vs_index_bits_def)
  done

lemma state_vrefs_subseteq:
  assumes "typs_of s' x = typs_of s x"
    and "pts_of s' = pts_of s"
    and "\<forall>pptr asid. pool_for_asid asid s' = Some pptr \<longrightarrow> pool_for_asid asid s = Some pptr"
    and "\<forall>pptr asid vref. vspace_for_pool pptr asid (asid_pools_of s') = Some vref
               \<longrightarrow> vspace_for_pool pptr asid (asid_pools_of s) = Some vref"
  shows "state_vrefs s' x \<subseteq> state_vrefs s x"
  apply (subst state_vrefs_def)
  using assms(1) apply clarsimp
  apply (case_tac "vspace_objs_of s x")
   apply (fastforce simp: opt_map_def a_type_def
                   split: option.splits arch_kernel_obj.splits kernel_object.splits if_splits)[1]
  apply (prop_tac "vs_refs_aux lvl ao \<subseteq> vs_refs_aux lvl ac")
   apply (rule vs_refs_aux_subseteq)
     using assms(4)
     apply (fastforce simp: opt_map_def aa_type_def vspace_for_pool_def entry_for_pool_def obind_def
                     split: option.splits arch_kernel_obj.splits)
    using assms(2)
    apply (clarsimp simp: in_opt_map_eq fun_eq_iff)
    apply (erule_tac x=x in allE)
    apply (fastforce simp: opt_map_def aa_type_def split: if_splits arch_kernel_obj.splits)
   apply (fastforce simp: opt_map_def aa_type_def
                   split: option.splits arch_kernel_obj.splits)
  apply (rule_tac state_vrefsD)
     apply (erule vs_lookup_table_subseteq)
  using assms by fastforce+

lemma pas_refined_subseteq:
  "\<lbrakk> pas_refined aag s; caps_of_state s' = caps_of_state s;
     \<forall>x y. asid_table s' x = Some y \<longrightarrow> asid_table s x = Some y;
     \<forall>x. state_vrefs s' x \<subseteq> state_vrefs s x; \<forall>x. state_hyp_refs_of s' x \<subseteq> state_hyp_refs_of s x;
     interrupt_irq_node s' = interrupt_irq_node s;
     domains_of_state s' = domains_of_state s; thread_st_auth s' = thread_st_auth s;
     thread_bound_ntfns s' = thread_bound_ntfns s; cdt s' = cdt s \<rbrakk>
     \<Longrightarrow> pas_refined aag s'"
  apply (auto simp: pas_refined_def)
   apply (clarsimp simp: state_objs_to_policy_def)
   apply (erule subsetD)
   apply (clarsimp simp: auth_graph_map_def)
   apply (rule exI, rule conjI, rule refl)+
   apply (erule state_bits_to_policy_refs_subseteq; clarsimp)
  apply (erule subsetD, rule state_asids_to_policy_vrefs_subseteq, auto)
  done

lemma store_InvalidPTE_state_objs_in_policy:
  "\<lbrace>\<lambda>s. state_objs_in_policy aag s \<and> invs s\<rbrace>
   store_pte pt_t p InvalidPTE
   \<lbrace>\<lambda>_ s. state_objs_in_policy aag s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp: state_objs_to_policy_def pred_conj_def)
   apply wps
   apply (rule state_vrefs_store_NonPageTablePTE_wp)
  apply (intro conjI; fastforce?)
  apply (intro allI impI)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (intro exI conjI)
     apply assumption
    apply clarsimp
   apply (clarsimp simp: state_objs_to_policy_def)
   apply (erule subsetD)
   apply (clarsimp simp: auth_graph_map_def)
   apply (rule exI, rule conjI, rule refl)+
   apply (erule state_bits_to_policy_refs_subseteq; clarsimp)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
   apply (frule vs_lookup_slot_level_type)
          apply (fastforce simp: ptes_of_Some)+
   apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
   apply (erule state_vrefsD)
     apply (fastforce simp: pts_of_Some vspace_objs_of_Some obj_at_def)
    apply clarsimp
   apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits pt.splits)
  apply (clarsimp simp: state_objs_to_policy_def)
  apply (erule subsetD)
  apply (clarsimp simp: auth_graph_map_def)
  apply (rule exI, rule conjI, rule refl)+
  apply (erule state_bits_to_policy_refs_subseteq; clarsimp)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid[where pt_t=pt_t]
                    simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
  apply (frule level_of_table_vs_lookup_table[where pt_t=pt_t])
      apply (fastforce dest: vs_lookup_slot_no_asid[where pt_t=pt_t]
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)+
  apply (erule state_vrefsD)
    apply (fastforce simp: pts_of_Some vspace_objs_of_Some obj_at_def)
   apply clarsimp
   apply (auto simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits pt.splits)
   apply fastforce
  apply fastforce
  done

lemma store_InvalidPTE_state_asids_to_policy:
  "\<lbrace>\<lambda>s. state_asids_to_policy aag s \<subseteq> pasPolicy aag \<and> invs s\<rbrace>
   store_pte pt_t p InvalidPTE
   \<lbrace>\<lambda>_ s. state_asids_to_policy aag s \<subseteq> pasPolicy aag\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp: state_objs_to_policy_def pred_conj_def)
   apply wps
   apply (rule state_vrefs_store_NonPageTablePTE_wp)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (intro exI conjI)
     apply assumption
    apply clarsimp
   apply clarsimp
   apply (erule subsetD)
   apply (erule state_asids_to_policy_vrefs_subseteq; clarsimp)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
   apply (frule vs_lookup_slot_level_type)
          apply (fastforce simp: ptes_of_Some)+
   apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
   apply (erule state_vrefsD)
     apply (fastforce simp: pts_of_Some vspace_objs_of_Some obj_at_def)
    apply clarsimp
   apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits pt.splits)
  apply (erule subsetD)
  apply (erule state_asids_to_policy_vrefs_subseteq; clarsimp)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid[where pt_t=pt_t]
                    simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
  apply (frule level_of_table_vs_lookup_table[where pt_t=pt_t])
      apply (fastforce dest: vs_lookup_slot_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)+
  apply (erule state_vrefsD)
    apply (fastforce simp: pts_of_Some vspace_objs_of_Some obj_at_def)
   apply clarsimp
  apply (auto simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits pt.splits)
   apply fastforce
  apply fastforce
  done

lemma mapM_x_swp_store_InvalidPTE_pas_refined:
  "\<lbrace>pas_refined aag and invs and
    (\<lambda>s. \<forall>x \<in> set slots. table_base pt_t x \<notin> global_refs s \<and>
                         (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base pt_t x)))\<rbrace>
   mapM_x (swp (store_pte pt_t) InvalidPTE) slots
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
  supply state_asids_to_policy_arch_def[simp del]
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp[where S="set slots"])
    apply (simp add: pas_refined_def)
    apply (wpsimp wp: store_InvalidPTE_state_objs_in_policy store_InvalidPTE_state_asids_to_policy
                      store_pte_invs hoare_vcg_const_Ball_lift hoare_vcg_all_lift)
    apply (auto simp: wellformed_pte_def)
  done

lemma mapM_swp_store_pte_invs_unmap:
  "\<lbrace>\<lambda>s. invs s \<and> pte = InvalidPTE \<and> table_base pt_t p \<notin> global_refs s
               \<and> (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base pt_t p))\<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp wp: store_pte_invs simp: wellformed_pte_def)

lemma store_pte_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> invs s \<and> table_base pt_t p \<notin> global_refs s \<and>
        (\<exists>slot pt_t ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base pt_t p) pt_t ref)))\<rbrace>
   store_pte pt_t p InvalidPTE
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  supply state_asids_to_policy_arch_def[simp del]
  apply (clarsimp simp: pas_refined_def)
  apply (wpsimp wp: store_InvalidPTE_state_objs_in_policy store_InvalidPTE_state_asids_to_policy)
  done

crunch invalidate_tlb_by_asid
  for pas_refined[wp]: "pas_refined aag"

lemma unmap_page_table_pas_refined:
 "\<lbrace>pas_refined aag and invs and K (vaddr \<in> user_region)\<rbrace>
  unmap_page_table asid vaddr pt
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding unmap_page_table_def
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp pt_lookup_from_level_wrp store_pte_invs_unmap
                    store_pte_pas_refined hoare_vcg_imp_lift' hoare_vcg_ball_lift hoare_vcg_all_lift)
  apply (rule_tac x=asid in exI)
  apply clarsimp
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid)
  apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: reachable_page_table_not_global)
   apply (frule vs_lookup_table_pt_at; clarsimp?)
   apply (drule vs_lookup_table_valid_cap; clarsimp?)
   apply (fastforce simp: valid_cap_def valid_arch_cap_def valid_arch_cap_ref_def obj_at_def
                    dest: caps_of_state_valid split: cap.splits arch_cap.splits)
  done

crunch unmap_page_table
  for cdt[wp]: "\<lambda>s. P (cdt s)"

definition authorised_page_table_inv :: "'a PAS \<Rightarrow> page_table_invocation \<Rightarrow> bool" where
  "authorised_page_table_inv aag pti \<equiv>
   case pti of PageTableMap cap cslot pte slot level \<Rightarrow>
                 is_subject aag (fst cslot) \<and> is_subject aag (table_base (level_type level) slot) \<and>
                 pas_cap_cur_auth aag (ArchObjectCap cap)
             | PageTableUnmap cap cslot \<Rightarrow>
                 is_subject aag (fst cslot) \<and>
                 aag_cap_auth aag (pasSubject aag) (ArchObjectCap cap) \<and>
                 (\<forall>p pt_t asid vspace_ref. cap = PageTableCap p pt_t (Some (asid, vspace_ref))
                                      \<longrightarrow> is_subject_asid aag asid \<and>
                                          (\<forall>x \<in> set [p, p + 2 ^ pte_bits .e. p + 2 ^ (pt_bits pt_t) - 1].
                                                             is_subject aag (table_base pt_t x)))"

lemma perform_pt_inv_unmap_pas_refined:
 "\<lbrace>pas_refined aag and invs and valid_pti (PageTableUnmap cap ct_slot)
                            and K (authorised_page_table_inv aag (PageTableUnmap cap ct_slot))\<rbrace>
  perform_pt_inv_unmap cap ct_slot
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pt_inv_unmap_def
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp)
        apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)
       apply wps
       apply (rule hoare_vcg_all_lift[OF hoare_vcg_imp_lift'[OF mapM_x_wp_inv]], wpsimp wp: mapM_x_wp_inv)
       apply (rule hoare_vcg_conj_lift[OF hoare_strengthen_post[OF mapM_x_swp_store_InvalidPTE_pas_refined]], assumption)
       apply (wpsimp wp: pt_lookup_from_level_wrp store_pte_invs_unmap store_pte_pas_refined
                         mapM_x_wp_inv unmap_page_table_pas_refined
                         hoare_vcg_imp_lift' hoare_vcg_ball_lift hoare_vcg_all_lift)+
  apply (rule conjI)
   apply (fastforce simp: is_PageTableCap_def authorised_page_table_inv_def
                          valid_pti_def update_map_data_def cte_wp_at_caps_of_state)
  apply (clarsimp simp: is_PageTableCap_def authorised_page_table_inv_def valid_arch_cap_def
                        valid_pti_def cte_wp_at_caps_of_state update_map_data_def aag_cap_auth_def
                        cap_auth_conferred_def arch_cap_auth_conferred_def wellformed_mapdata_def
                        cap_links_asid_slot_def cap_links_irq_def is_transferable.simps)
  apply (prop_tac "table_base NormalPT_T x = acap_obj cap")
   apply (drule (1) caps_of_state_aligned_page_table)
   apply (simp only: is_aligned_neg_mask_eq')
   apply (clarsimp simp: add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule neg_mask_mono_le[where n="pt_bits NormalPT_T"])
   apply (drule neg_mask_mono_le[where n="pt_bits NormalPT_T"])
   apply (fastforce dest: plus_mask_AND_NOT_mask_eq)
  apply (rule conjI; clarsimp)
   apply (fastforce simp: cte_wp_at_caps_of_state cap_range_def
                    dest: invs_valid_global_refs valid_global_refsD)
  apply (frule vspace_for_asid_target)
  apply (drule valid_vs_lookupD; clarsimp)
  apply (drule (1) unique_table_refsD[rotated]; clarsimp)
  apply (clarsimp simp: obj_at_def)
  apply (drule (1) cap_to_pt_is_pt_cap_and_type)
    apply (fastforce simp: in_omonad obj_at_def)
   apply (fastforce intro: valid_objs_caps)
  apply (clarsimp simp: is_cap_simps)
  done

lemma vs_lookup_PageTablePTE:
  "\<lbrakk> vs_lookup_table level asid vref s' = Some (lvl', pt);
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s;
     invalid_pte_at pt_t p s; ptes_of s' = (ptes_of s)(pt_t,p \<mapsto> pte); is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s; asid_table s' = asid_table s;
     vref \<in> user_region;
     pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T); pt \<noteq> pptr_from_pte pte \<rbrakk>
     \<Longrightarrow> \<exists>level' \<ge> level. vs_lookup_table level' asid vref s = Some (lvl', pt)"
  apply (induct level arbitrary: lvl' pt rule: vm_level.from_top_full_induct[where y=max_pt_level])
   apply (fastforce simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  apply (rule_tac x=lvl' in exI)
  apply (frule vs_lookup_min_level, clarsimp)
  apply (drule vs_lookup_level)
  apply (case_tac "lvl' < max_pt_level")
   apply (frule vs_lookup_table_split_last_Some; clarsimp)
   apply (erule_tac x="lvl'+1" in allE)
   apply (drule mp)
    apply (fastforce elim: le_less_trans dest: vm_level_less_plus_1_mono)
   apply (erule_tac x="lvl'+1" in allE)
   apply clarsimp
   apply (frule (1) subst[where P="\<lambda>ptes. _ ptes = (_ :: pte option)"])
   apply (clarsimp simp: fun_upd2_apply split: if_splits)
   apply (cases pte; clarsimp)
   apply (drule mp)
    apply clarsimp
    apply (case_tac "(lvl' + 1) + 1 \<le> max_pt_level")
     apply (fastforce simp: add_ac ptes_of_Some dest!: pptr_from_pte_aligned_pt_bits[where pte=pte])
    apply (prop_tac "is_aligned (pptr_from_pte pte) (pt_bits (level_type (lvl' + 1)))")
     apply (fastforce simp: geq_max_pt_level plus_one_eq_asid_pool max_pt_level_plus_one[symmetric]
                            vs_lookup_max_pt_level_eq[where s=s and s'=s'] less_imp_neq not_le add_ac
                      dest: vs_lookup_table_is_aligned[where pt_ptr="pptr_from_pte (PageTablePTE _)"])
    apply (clarsimp simp: ptes_of_Some)
   apply (cases pte; clarsimp)
   apply (drule_tac bot_level=level' in vs_lookup_level)
   apply (subst vs_lookup_split_Some)
     prefer 3
     apply (rule exI, rule conjI, assumption)
     apply (frule_tac P="\<lambda>x. x" and level1=lvl' and level'1="lvl'+1"
                   in subst[OF vs_lookup_split_Some, rotated 2])
       apply (fastforce dest: vm_level_less_le_1)
      apply (fastforce dest: vm_level_less_max_pt_level vm_level_less_plus_1_mono)
     apply clarsimp
     apply (subst (asm) pt_walk.simps)
     apply (clarsimp simp: obind_def)
     apply (subst pt_walk.simps)
     apply (clarsimp split: if_splits option.splits simp: obind_def)
    apply (fastforce dest: vm_level_less_le_1)
   apply (fastforce dest: vm_level_less_max_pt_level vm_level_less_plus_1_mono)
  apply (case_tac "lvl' = asid_pool_level")
   apply (auto simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  done

lemma vs_lookup_PageTablePTE':
  "\<lbrakk> vs_lookup_table level asid vref s = Some (lvl', pt);
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s;
     invalid_pte_at pt_t p s; ptes_of s' = (ptes_of s)(pt_t, p \<mapsto> pte); is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s; asid_table s' = asid_table s; vref \<in> user_region  \<rbrakk>
     \<Longrightarrow> \<exists>level' \<ge> level. vs_lookup_table level' asid vref s' = Some (lvl', pt)"
  apply (induct level arbitrary: lvl' pt rule: vm_level.from_top_full_induct[where y=max_pt_level])
   apply (fastforce simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  apply (rule_tac x=lvl' in exI)
  apply (frule vs_lookup_min_level, clarsimp)
  apply (drule vs_lookup_level)
  apply (case_tac "lvl' < max_pt_level")
   apply (frule vs_lookup_table_split_last_Some; clarsimp)
   apply (erule_tac x="lvl'+1" in allE)
   apply (drule mp)
    apply (fastforce elim: le_less_trans dest: vm_level_less_plus_1_mono)
   apply (erule_tac x="lvl'+1" in allE)
   apply clarsimp
   apply (drule_tac bot_level=level' in vs_lookup_level)
   apply (subst vs_lookup_split_Some)
     prefer 3
     apply (rule exI, rule conjI, assumption)
     apply (frule_tac P="\<lambda>x. x" and level1=lvl' and level'1="lvl'+1"
                   in subst[OF vs_lookup_split_Some, rotated 2])
       apply (fastforce dest: vm_level_less_le_1)
      apply (fastforce dest: vm_level_less_max_pt_level vm_level_less_plus_1_mono)
     apply clarsimp
     apply (subst (asm) pt_walk.simps)
     apply (clarsimp simp: obind_def split: if_splits)
     apply (subst pt_walk.simps)
     apply (clarsimp simp: obind_def split: if_splits)
     apply (cases pte; clarsimp)
     apply (frule is_aligned_pt[rotated])
      apply (erule vs_lookup_table_pt_at; fastforce)
     apply (clarsimp split: option.splits)
     apply (rule context_conjI)
      apply (clarsimp simp: fun_upd2_def)
     apply clarsimp
      apply (clarsimp simp: fun_upd2_def split: if_splits)
     apply (clarsimp simp: invalid_pte_at_def ptes_of_Some pts_of_Some aobjs_of_Some)
    apply (fastforce dest: vm_level_less_le_1)
   apply (fastforce dest: vm_level_less_max_pt_level vm_level_less_plus_1_mono)
  apply (case_tac "lvl' = asid_pool_level")
   apply (auto simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  done

lemma state_vrefs_store_PageTablePTE:
  assumes "invs s"
  and "is_aligned p pte_bits"
  and "vs_lookup_slot level asid vref s = Some (level, p)"
  and "vref \<in> user_region"
  and "is_PageTablePTE pte"
  and "invalid_pte_at (pt_type pt) p s"
  and "pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T)"
  and "the (pte_ref pte) \<noteq> table_base (pt_type pt) p"
  and "(kheap s)(table_base (pt_type pt) p) = Some (ArchObj (PageTable pt))"
  shows "state_vrefs (s\<lparr>kheap := (kheap s)(table_base (pt_type pt) p \<mapsto>
                                 ArchObj (PageTable (pt_upd pt (table_index (pt_type pt) p) pte)))\<rparr>) =
         (\<lambda>x. if x = table_base (pt_type pt) p
              then vs_refs_aux level (PageTable (pt_upd pt (table_index (pt_type pt) p) pte))
              else state_vrefs s x)"
  (is "state_vrefs ?s' = _")
  using assms
  apply -
  apply (rule all_ext)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce simp: vs_lookup_slot_def vs_lookup_table_def
                          ptes_of_Some pts_of_Some aobjs_of_Some
                    dest: pool_for_asid_no_pte split: if_splits)
  apply safe
   apply (clarsimp simp: state_vrefs_def opt_map_def split: option.splits)
   apply (case_tac "x = pptr_from_pte pte")
    apply (clarsimp simp: pte_ref_def2 split: if_splits)
    apply (fastforce simp: empty_pt_def vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits pt.splits)
   apply (drule_tac s=s and pte=pte and p=p in vs_lookup_PageTablePTE)
              apply (((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                                intro: ptes_of_pts_of_upd
                                 dest: pte_ptr_eq split: if_splits
                       | clarsimp simp: opt_map_def fun_upd_def split: option.splits)+; fail)+)[11]
   apply clarsimp
   apply (drule vs_lookup_level)
   apply (case_tac "lvl = asid_pool_level")
    apply (fastforce dest: vs_lookup_asid_pool simp: asid_pools_of_ko_at obj_at_def)
  apply (frule vs_lookup_slot_level_type)
          apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)+
   apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
   apply (fastforce dest: vs_lookup_table_unique_level split: if_splits)
  apply (clarsimp simp: state_vrefs_def opt_map_def)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_asid_pool simp: asid_pools_of_ko_at obj_at_def)
  apply (frule vs_lookup_slot_level_type)
          apply ((fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)+)[7]
  apply (frule vs_lookup_slot_table_base)
     apply clarsimp+
  apply (case_tac "x = table_base (pt_type pt) p"; clarsimp)
   apply (drule_tac pte=pte and s'="?s'" in vs_lookup_PageTablePTE')
              apply (((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                              intro: ptes_of_pts_of_upd
                               dest: pte_ptr_eq split: if_splits
                     | clarsimp simp: opt_map_def fun_upd_def fun_upd2_def split: if_splits option.splits)+; fail)+)[10]
  apply (drule_tac level=bot and pte=pte and s'="?s'" in vs_lookup_PageTablePTE')
              apply (((fastforce simp: ptes_of_pts_of_upd ptes_of_Some pts_of_Some aobjs_of_Some
                              intro: ptes_of_pts_of_upd
                               dest: pte_ptr_eq split: if_splits
                     | clarsimp simp: opt_map_def fun_upd_def fun_upd2_def split: if_splits option.splits)+; fail)+)[10]
  done

lemma state_vrefs_store_PageTablePTE_wp:
  "\<lbrace>\<lambda>s. invs s \<and> is_PageTablePTE pte \<and> invalid_pte_at pt_t p s \<and>
        pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T) \<and> the (pte_ref pte) \<noteq> table_base pt_t p \<and>
        (\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region \<and>
                           (\<forall>pt. pts_of s (table_base pt_t p) = Some pt \<and> pt_t = pt_type pt \<and> is_aligned p pte_bits \<longrightarrow>
                                 P (\<lambda>x. if x = table_base (pt_type pt) p
                                        then vs_refs_aux level (PageTable (pt_upd pt (table_index (pt_type pt) p) pte))
                                        else state_vrefs s x)))\<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (subst state_vrefs_store_PageTablePTE; simp?)
   apply (fastforce simp: fun_upd_def fun_upd2_def obj_at_def state_vrefs_store_PageTablePTE split: if_splits)
  apply (clarsimp simp: pts_of_Some aobjs_of_Some obj_at_def)
  done

lemma pt_apply_def2:
  "pt_apply pt = (\<lambda>idx. case pt of NormalPT npt \<Rightarrow> npt (ucast idx) | VSRootPT vs \<Rightarrow> vs (ucast idx))"
  by (fastforce simp: pt_apply_def)

lemma pt_apply_upd_eq':
  "pt_apply (pt_upd pt idx pte) idx' =
   (if idx && mask (ptTranslationBits (pt_type pt)) = idx' && mask (ptTranslationBits (pt_type pt))
    then pte else pt_apply pt idx')"
  by (fastforce simp: pt_apply_def pt_upd_def ucast_ucast_mask vs_index_bits_def ptTranslationBits_def
                dest: arg_cong[where f="UCAST(vs_index_len \<rightarrow> 64)"] arg_cong[where f="UCAST(9 \<rightarrow> 64)"]
               intro: ucast_up_inj[where 'b=64]
               split: pt.splits)

(* FIXME AARCH64: replace vs_refs_aux with this definition *)
lemma vs_refs_aux_def2:
  "vs_refs_aux level = (\<lambda>ko. case ko of
     ASIDPool pool \<Rightarrow> (\<lambda>(r,p). (p, ucast r, AASIDPool, Control)) ` graph_of (option_map ap_vspace o pool)
   | PageTable pt \<Rightarrow> \<Union>(r,(p, sz, auth)) \<in> graph_of (pte_ref2 level o pt_apply pt).
                       (\<lambda>(p, a). (p, r && mask (ptTranslationBits (pt_type pt)), APageTable (pt_type pt), a))
                       ` (ptr_range p sz \<times> auth)
   | _ \<Rightarrow> {})"
  apply (rule ext)+
  apply (rule equalityI)
   apply (clarsimp simp: vs_refs_aux_def )
   apply (case_tac ko; clarsimp)
   apply (case_tac x2; clarsimp simp: pt_apply_def2)
    apply (clarsimp simp: graph_of_def image_iff)
    apply (rule_tac x="UCAST(vs_index_len \<rightarrow> 64) ac" in exI)
    apply (fastforce simp: ucast_and_mask_drop ucast_ucast_id vs_index_bits_def ptTranslationBits_def)
   apply (clarsimp simp: graph_of_def image_iff)
   apply (rule_tac x="UCAST(9 \<rightarrow> 64) ac" in exI)
   apply (fastforce simp: ucast_and_mask_drop ucast_ucast_id vs_index_bits_def ptTranslationBits_def)
  apply (clarsimp simp: vs_refs_aux_def)
  apply (case_tac ko; clarsimp)
  apply (case_tac x2; clarsimp simp: pt_apply_def2)
   apply (fastforce simp: graph_of_def image_iff ucast_ucast_mask vs_index_bits_def ptTranslationBits_def)
  apply (fastforce simp: graph_of_def image_iff ucast_ucast_mask vs_index_bits_def ptTranslationBits_def)
  done

lemma perform_pt_inv_map_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and valid_pti (PageTableMap acap (a, b) pte p level)
                    and K (authorised_page_table_inv aag (PageTableMap acap (a, b) pte p level))\<rbrace>
   perform_pt_inv_map acap (a,b) pte p level
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pt_inv_map_def
  apply (rule hoare_gen_asm)
  apply (wpsimp simp: pas_refined_def state_objs_to_policy_def)
    apply (wps | wpsimp wp: state_vrefs_store_PageTablePTE_wp arch_update_cap_invs_map
                            vs_lookup_slot_lift set_cap_arch_obj_neg set_cap_state_vrefs
                            hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift')+
  apply (clarsimp simp: invs_psp_aligned invs_vspace_objs invs_arch_state
                        valid_pti_def cte_wp_at_cte_at)
  apply (case_tac acap; clarsimp)
  apply (intro conjI; (solves \<open>simp add: pas_refined_def\<close>)?)
     apply (fastforce simp: cte_wp_at_caps_of_state vs_cap_ref_def
                            is_arch_update_def cap_master_cap_def
                     split: arch_cap.splits)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (fastforce dest: caps_of_state_valid
                    simp: vs_cap_ref_def is_arch_update_def cap_master_cap_def
                          valid_cap_def cap_aligned_def valid_arch_cap_def
                   split: cap.splits arch_cap.splits)
   apply (clarsimp simp: vs_lookup_slot_def split: if_splits)
    apply (fastforce dest: pool_for_asid_no_pte simp: vs_lookup_table_def invalid_pte_at_def)
   apply (frule (2) vs_lookup_table_is_aligned; clarsimp)
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap_and_type, simp, fastforce intro: valid_objs_caps)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (clarsimp simp: is_cap_simps is_arch_update_def cap_master_cap_def
                  split: cap.splits arch_cap.splits)
   apply (drule (1) unique_table_refsD[rotated]; fastforce simp: table_cap_ref_def)
  apply (intro exI conjI; (simp | clarsimp))
  apply (intro conjI)
    apply (clarsimp simp: pas_refined_def cte_wp_at_caps_of_state auth_graph_map_def)
    apply (erule state_bits_to_policy.cases)
           apply (clarsimp simp: is_arch_update_def cap_master_cap_def state_objs_to_policy_def
                          split: if_splits cap.splits arch_cap.splits option.splits;
                  fastforce dest: sbta_caps simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
          apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def split: if_splits)
         apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
        apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
       apply (clarsimp simp: state_objs_to_policy_def is_arch_update_def cap_master_cap_def)
       apply (drule_tac caps="caps_of_state s" in sbta_cdt;
              fastforce elim: is_transferable.cases split: if_splits)
      apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)
     apply (clarsimp split: if_splits)
      apply (clarsimp simp: authorised_page_table_inv_def split: arch_kernel_obj.splits)
      apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
      apply (cases pte; clarsimp)
      apply (clarsimp simp: vs_refs_aux_def2 graph_of_def)
      apply (clarsimp simp: pt_apply_upd_eq' split: if_splits)
       apply (clarsimp simp: pte_ref2_def pptr_from_pte_def)
      apply (erule subsetD)
      apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
      apply (rule_tac x="table_base (pt_type pt) p" in exI, rule conjI, erule sym)
      apply (rule exI, rule conjI, rule refl)
      apply (rule sbta_vref)
      apply (case_tac "level = asid_pool_level")
       apply (fastforce dest: pool_for_asid_no_pte
                        simp: vs_lookup_slot_def vs_lookup_table_def invalid_pte_at_def)
      apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
      apply (erule state_vrefsD)
        apply (fastforce simp: pts_of_Some vspace_objs_of_Some obj_at_def)
       apply clarsimp
      apply (fastforce simp: vs_refs_aux_def2 graph_of_def)
     (* slow ~60s *)
     apply (clarsimp simp: is_arch_update_def cap_master_cap_def
                    split: cap.splits arch_cap.splits option.splits)
     apply (fastforce dest: sbta_vref simp: pas_refined_def auth_graph_map_def state_objs_to_policy_def)
    apply (clarsimp simp: is_arch_update_def cap_master_cap_def
                   split: cap.splits arch_cap.splits option.splits)
    apply (fastforce simp: sbta_href pas_refined_def auth_graph_map_def state_objs_to_policy_def)
   apply (clarsimp simp: pas_refined_def)
   apply (erule state_asids_to_policy_aux.cases)
     apply (clarsimp simp: cte_wp_at_caps_of_state split: if_splits)
      apply (clarsimp simp: authorised_page_table_inv_def aag_cap_auth_def
                            cap_auth_conferred_def arch_cap_auth_conferred_def
                            cap_links_asid_slot_def label_owns_asid_slot_def)
     apply (fastforce dest: sata_asid)
    apply (clarsimp split: if_splits)
     apply (fastforce dest!: state_asids_to_policy_aux.intros simp: vs_refs_aux_def split: pt.splits)
    apply (fastforce dest!: sata_asid_lookup)
   apply (fastforce dest!: sata_asidpool)
  apply (clarsimp simp: pas_refined_def)
  apply (erule state_irqs_to_policy_aux.cases)
  apply (clarsimp split: if_splits)
  apply (fastforce dest: sita_controlled)
  done

lemma perform_page_table_invocation_pas_refined:
  "\<lbrace>pas_refined aag and invs and valid_pti iv and K (authorised_page_table_inv aag iv)\<rbrace>
   perform_page_table_invocation iv
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_page_table_invocation_def
  apply wpsimp
   apply (wpsimp wp: perform_pt_inv_unmap_pas_refined perform_pt_inv_map_pas_refined)+
  apply (case_tac iv; clarsimp)
  done

lemma set_asid_pool_thread_st_auth[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: thread_st_auth_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

lemma set_asid_pool_thread_bound_ntfns[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm option.split)
  done

crunch set_asid_pool
  for integrity_autarch: "integrity aag X st"
  (wp: crunch_wps)

lemma store_pte_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag (table_base pt_t p))\<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp set_object_integrity_autarch)
  apply simp
  done

lemma integrity_arch_state[simp]:
  "\<lbrakk> arm_asid_table v = arm_asid_table (arch_state s);
     arm_current_vcpu v = arm_current_vcpu (arch_state s);
     arm_gicvcpu_numlistregs v = arm_gicvcpu_numlistregs (arch_state s) \<rbrakk>
     \<Longrightarrow> integrity aag X st (s\<lparr>arch_state := v\<rparr>) = integrity aag X st s"
  by (simp add: integrity_def integrity_asids_def integrity_hyp_def integrity_fpu_def)

lemma integrity_arm_kernel_vspace[iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>arm_kernel_vspace := v\<rparr>)\<rparr>) =
   integrity aag X st s"
  by simp

lemma is_subject_trans:
  "\<lbrakk> is_subject aag x; pas_refined aag s;
     (pasObjectAbs aag x, Control, pasObjectAbs aag y) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> is_subject aag y"
  by (subst aag_has_Control_iff_owns[symmetric]; simp)

lemma is_subject_asid_trans:
  "\<lbrakk> is_subject_asid aag x; pas_refined aag s;
     (pasASIDAbs aag x, Control, pasObjectAbs aag y) \<in> pasPolicy aag \<rbrakk>
     \<Longrightarrow> is_subject aag y"
  by (subst aag_has_Control_iff_owns[symmetric]; simp)

lemma pt_walk_is_subject:
  "\<lbrakk> pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     pt_walk level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     vs_lookup_table level asid vptr s = Some (level, pt_ptr);
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag pt"
  apply (induct level arbitrary: pt_ptr; clarsimp)
  apply (erule_tac x="pptr_from_pte (the (ptes_of s (level_type level) (pt_slot_offset level pt_ptr vptr)))"
                in meta_allE)
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp: obind_def split: if_splits option.splits)
  apply (drule meta_mp)
   apply (erule vs_lookup_table_extend)
    apply (subst pt_walk.simps, clarsimp simp: obind_def)
   apply clarsimp
  apply (erule meta_mp)
  apply (subst (asm) ptes_of_Some)
  apply (frule vs_lookup_table_is_aligned; clarsimp)
  apply (erule (1) is_subject_trans)
  apply (clarsimp simp: pas_refined_def auth_graph_map_def)
  apply (erule subsetD, clarsimp)
  apply (rule exI conjI refl sta_vref)+
  apply (erule state_vrefsD)
    apply (fastforce simp: vspace_objs_of_Some pts_of_Some)
   apply clarsimp
  apply (clarsimp simp: vs_refs_aux_def2  graph_of_def)
  apply (rule_tac x="pt_index level vptr" in exI)
  apply (fastforce simp: pptr_from_pte_def pte_ref2_def split: pte.splits)
  done

lemma pt_lookup_slot_from_level_is_subject:
  "\<lbrakk> pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     pt_lookup_slot_from_level level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     (\<exists>asid. vs_lookup_table level asid vptr s = Some (level, pt_ptr));
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag (table_base (level_type level') pt)"
  apply (clarsimp simp: pt_lookup_slot_from_level_def)
  apply (frule vs_lookup_table_is_aligned, fastforce+)
  apply (frule pt_walk_is_aligned, fastforce+)
  apply (frule pt_walk_is_subject, fastforce+)
  done

lemma pt_lookup_from_level_is_subject:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        is_subject aag pt_ptr \<and> level \<le> max_pt_level \<and> vref \<in> user_region \<and>
        (\<exists>asid. vs_lookup_table level asid vref s = Some (level, pt_ptr))\<rbrace>
   pt_lookup_from_level level pt_ptr vref pt
   \<lbrace>\<lambda>(rv,lvl) _. is_subject aag (table_base (level_type lvl) rv)\<rbrace>, -"
  apply (wpsimp wp: pt_lookup_from_level_wp)
  apply (erule_tac level=level and bot_level=levela and pt_ptr=pt_ptr and vptr=vref
                in pt_lookup_slot_from_level_is_subject)
  by (auto simp: pt_lookup_slot_from_level_def obind_def)

crunch invalidateTranslationASID, cleanByVA_PoU
  for vcpu_state[wp]: "\<lambda>ms. P (vcpu_state ms)"
  and fpu_state[wp]: "\<lambda>ms. P (fpu_state ms)"

lemma unmap_page_table_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs
                       and K (is_subject_asid aag asid \<and> vaddr \<in> user_region)\<rbrace>
   unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding unmap_page_table_def invalidate_tlb_by_asid_def
  apply (wpsimp wp: dmo_no_mem_respects store_pte_respects Nondet_VCG.hoare_vcg_all_liftE
              simp: imp_conjR
         | rule hoare_strengthen_postE_R[OF pt_lookup_from_level_is_subject], fastforce
         | rule hoare_vcg_conj_elimE hoare_vcg_conj_liftE_R hoare_drop_imps)+
  apply (intro conjI; clarsimp?)
   apply (rule aag_Control_into_owns[rotated], assumption)
   apply (drule sym)
   apply (clarsimp simp: vspace_for_asid_def entry_for_asid_def obj_at_def pas_refined_def)
   apply (erule_tac A="state_asids_to_policy_aux _ _ _ _" in subsetD)
   apply (rule sata_asid_lookup)
    apply (simp add:  vspace_for_pool_def pool_for_asid_def)
   apply (clarsimp simp: entry_for_pool_def vspace_for_pool_def)
   apply (drule pool_for_asid_vs_lookupD)
   apply (erule state_vrefsD)
     apply (fastforce simp: vspace_objs_of_Some aobjs_of_Some asid_pools_of_ko_at obj_at_def)
    apply assumption
   apply (clarsimp simp: vs_refs_aux_def)
   apply (fastforce simp: vs_refs_aux_def graph_of_def asid_low_bits_of_mask_eq[symmetric]
                          word_size ucast_ucast_b is_up_def source_size_def target_size_def)
  apply (fastforce dest: vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup])
  done

lemma perform_page_table_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and valid_pti page_table_invocation
                       and K (authorised_page_table_inv aag page_table_invocation)\<rbrace>
   perform_page_table_invocation page_table_invocation
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: perform_page_table_invocation_def perform_pt_inv_map_def perform_pt_inv_unmap_def
             cong: page_table_invocation.case_cong option.case_cong prod.case_cong
                   cap.case_cong arch_cap.case_cong)
  apply (cases page_table_invocation; clarsimp)
   apply (wpsimp wp: set_cap_integrity_autarch store_pte_respects
               simp: authorised_page_table_inv_def cleanByVA_PoU_def)
  apply (rename_tac cap fst_cslot_ptr snd_cslot_ptr)
  apply (wpsimp wp: set_cap_integrity_autarch simp:cleanCacheRange_PoU_def)
     apply (rule_tac I="\<lambda>s. integrity aag X st s \<and> is_subject aag fst_cslot_ptr \<and> is_PageTableCap cap"
                  in mapM_x_inv_wp; clarsimp)
      apply (rule_tac P="\<lambda>s. integrity aag X st s \<and> is_PageTableCap cap" in hoare_vcg_conj_lift)
       apply (wpsimp wp: store_pte_respects)
       apply (clarsimp simp: authorised_page_table_inv_def)
       apply (case_tac cap; clarsimp)
       apply (metis add_mask_fold)
      apply (wpsimp wp: unmap_page_table_respects)+
  apply (clarsimp simp: authorised_page_table_inv_def valid_pti_def valid_arch_cap_def
                        wellformed_acap_def wellformed_mapdata_def
                 split: arch_cap.splits)
  done

lemma perform_pg_inv_get_addr_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs\<rbrace>
   perform_pg_inv_get_addr ptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_get_addr_def
  by wp auto

lemma store_pte_vmid_for_asid[wp]:
  " store_pte pt_t p pte
   \<lbrace>\<lambda>s. P (vmid_for_asid s asid)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp set_object_wp)
  by (auto simp: obj_at_def opt_map_def vmid_for_asid_def obind_def entry_for_pool_def
          split: if_splits option.splits)

lemma unmap_page_pas_refined:
  "\<lbrace>pas_refined aag and invs and K (vptr \<in> user_region)\<rbrace>
   unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding unmap_page_def invalidate_tlb_by_asid_va_def cleanByVA_PoU_def
  apply (clarsimp simp: conj_ac | wpsimp wp: set_cap_pas_refined_not_transferable hoare_vcg_all_lift
                                             hoare_vcg_imp_lift' get_cap_wp store_pte_pas_refined
                                             store_pte_valid_arch_state_unreachable)+
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
  apply (drule vs_lookup_slot_level)
  apply (case_tac "x = asid_pool_level")
   apply (fastforce dest: vs_lookup_slot_no_asid)
  apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
  apply (intro conjI)
    apply (clarsimp simp: reachable_page_table_not_global)
   apply (frule vs_lookup_table_pt_at; clarsimp?)
   apply (drule vs_lookup_table_valid_cap; clarsimp?)
   apply (fastforce simp: valid_cap_def valid_arch_cap_def valid_arch_cap_ref_def obj_at_def
                    dest: caps_of_state_valid split: cap.splits arch_cap.splits)
  done

definition authorised_slots :: "'a PAS \<Rightarrow> pte \<times> obj_ref \<times> vm_level \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
 "authorised_slots aag m s \<equiv> case m of (pte, slot, lvl) \<Rightarrow>
    (\<forall>level asid vref x.
       vs_lookup_slot level asid vref s = Some (level, slot) \<longrightarrow>
       vref \<in> user_region \<longrightarrow>
       level \<le> max_pt_level \<longrightarrow>
       pte_ref2 level pte = Some x \<longrightarrow>
         (\<forall>a \<in> snd (snd x). \<forall>p \<in> ptr_range (fst x) (fst (snd x)). aag_has_auth_to aag a p)) \<and>
    is_subject aag (table_base (level_type lvl) slot)"

definition authorised_page_inv :: "'a PAS \<Rightarrow> page_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
  "authorised_page_inv aag pgi s \<equiv> case pgi of
     PageMap cap ptr slots \<Rightarrow> pas_cap_cur_auth aag (ArchObjectCap cap) \<and>
                              is_subject aag (fst ptr) \<and> authorised_slots aag slots s
   | PageUnmap cap ptr \<Rightarrow> pas_cap_cur_auth aag (ArchObjectCap cap) \<and> is_subject aag (fst ptr)
   | _ \<Rightarrow> True"

lemma perform_pg_inv_unmap_pas_refined:
   "\<lbrace>pas_refined aag and invs and valid_page_inv (PageUnmap cap ct_slot)
                     and authorised_page_inv aag (PageUnmap cap ct_slot)\<rbrace>
    perform_pg_inv_unmap cap ct_slot
    \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_unmap_def
  apply (strengthen invs_psp_aligned invs_vspace_objs invs_arch_state
         | wpsimp wp: unmap_page_pas_refined set_cap_pas_refined_not_transferable
                      unmap_page_invs get_cap_wp hoare_vcg_all_lift hoare_vcg_imp_lift)+
  apply (fastforce simp: authorised_page_inv_def valid_page_inv_def valid_arch_cap_def
                         cte_wp_at_caps_of_state update_map_data_def aag_cap_auth_def
                         cap_auth_conferred_def arch_cap_auth_conferred_def
                         cap_links_asid_slot_def cap_links_irq_def wellformed_mapdata_def)
  done

lemma set_cap_vs_lookup_slot[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (vs_lookup_slot level asid vref s)\<rbrace> "
  apply (clarsimp simp: vs_lookup_slot_def obind_def)
  apply (rule hoare_pre)
   apply (rule hoare_lift_Pf3[where f="\<lambda>s level asid vref. vs_lookup_table level asid vref s"])
    apply (clarsimp split: option.splits)
    apply wpsimp
   apply wpsimp
  apply (auto split: if_splits)
  done

crunch set_cap
  for level_of_table[wp]: "\<lambda>s. P (level_of_table p s)"
  (simp: level_of_table_def)

lemma set_cap_authorised_page_inv[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (authorised_page_inv aag (PageMap cap ct_slot entries) s)\<rbrace> "
  apply (clarsimp simp: authorised_page_inv_def authorised_slots_def)
  apply (rule hoare_pre)
   apply wps
   apply wp
  apply clarsimp
  done

lemma set_cap_same_ref[wp]:
  "set_cap param_a param_b \<lbrace>\<lambda>s. P (same_ref pte_slot cap s)\<rbrace> "
  apply (case_tac pte_slot; clarsimp)
  apply (clarsimp simp: same_ref_def)
  apply (rule hoare_pre)
   apply wps
   apply wp
  apply clarsimp
  done

lemma perform_pg_inv_map_pas_refined:
  "\<lbrace>pas_refined aag and invs and valid_page_inv (PageMap cap ct_slot (pte,slot,level))
                    and authorised_page_inv aag (PageMap cap ct_slot (pte,slot,level))\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot level
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_map_def invalidate_tlb_by_asid_va_def cleanCacheRange_PoU_def cleanByVA_PoU_def
  apply wp
        apply wpsimp
       apply wp
      apply (wpsimp wp: hoare_vcg_if_lift hoare_vcg_imp_lift)
     apply (rule_tac Q'="\<lambda>_. pas_refined aag" in hoare_strengthen_post)
      apply (simp add: pas_refined_def state_objs_to_policy_def)
      apply wp
      apply wps
      apply (rule state_vrefs_store_NonPageTablePTE_wp)
     apply (clarsimp simp: pas_refined_def)
    apply (rule_tac Q'="\<lambda>_. invs and pas_refined aag and K (\<not> is_PageTablePTE pte)
                                 and authorised_page_inv aag (PageMap cap ct_slot (pte,slot,level))
                                 and same_ref (pte,slot,level) (ArchObjectCap cap)"
                 in hoare_strengthen_post[rotated])
     apply (clarsimp simp: pas_refined_def)
     apply (rule conjI)
      apply clarsimp
      apply (intro exI, rule conjI, assumption)
      apply clarsimp
      apply (rule conjI)
       prefer 2
       apply clarsimp
       apply (erule_tac A="state_asids_to_policy_aux _ _ _ _" in subsetD)
       apply (erule state_asids_to_policy_aux.cases)
         apply (fastforce dest: sata_asid)
        apply (clarsimp simp: cte_wp_at_caps_of_state)
        apply (clarsimp simp only: split: if_splits)
         apply (clarsimp simp: vs_refs_aux_def split: pt.splits)
        apply (erule sata_asid_lookup)
        apply assumption
       apply (fastforce dest: sata_asidpool)
      apply (clarsimp simp: auth_graph_map_def authorised_page_inv_def)
      apply (erule state_bits_to_policy.cases)
             apply (fastforce dest: sbta_caps simp: state_objs_to_policy_def)
            apply (fastforce dest: sbta_untyped simp: state_objs_to_policy_def)
           apply (fastforce dest: sbta_ts simp: state_objs_to_policy_def)
          apply (fastforce dest: sbta_bounds simp: state_objs_to_policy_def)
         apply (fastforce dest: sbta_cdt simp: state_objs_to_policy_def)
        apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)
       apply (clarsimp split: if_split_asm)
        apply (clarsimp simp: vs_refs_aux_def)
        apply (case_tac "levela = asid_pool_level")
         apply (fastforce dest!: vs_lookup_slot_no_asid
                           simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
        apply (clarsimp simp: pt_upd_def split: pt.splits)
         apply (clarsimp simp: graph_of_def split: if_split_asm)
          apply (case_tac pte; clarsimp simp: authorised_slots_def)
         apply (clarsimp simp: same_ref_def)
         apply (drule (1) vs_lookup_slot_unique_level; clarsimp)
         apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
         apply (erule subsetD)
         apply (clarsimp simp: state_objs_to_policy_def)
         apply (rule exI, rule conjI, rule refl)+
         apply (rule sbta_vref)
         apply (erule state_vrefsD)
           apply (fastforce simp: ptes_of_Some pts_of_Some vspace_objs_of_Some obj_at_def)
          apply fastforce
         apply (fastforce simp: vs_refs_aux_def graph_of_def)
        apply (clarsimp simp: graph_of_def split: if_split_asm)
         apply (case_tac pte; clarsimp simp: authorised_slots_def level_type_def)
        apply (clarsimp simp: same_ref_def)
        apply (drule (1) vs_lookup_slot_unique_level; clarsimp)
        apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
        apply (erule subsetD)
        apply (clarsimp simp: state_objs_to_policy_def level_type_def)
        apply (rule exI, rule conjI, rule refl)+
        apply (rule sbta_vref)
        apply (erule state_vrefsD)
          apply (fastforce simp: ptes_of_Some pts_of_Some vspace_objs_of_Some obj_at_def)
         apply fastforce
        apply (fastforce simp: vs_refs_aux_def graph_of_def)
       apply (fastforce dest: sbta_vref simp: state_objs_to_policy_def)
      apply (fastforce simp: sbta_href state_objs_to_policy_def)
     apply (clarsimp simp: same_ref_def)
    apply (wpsimp wp: arch_update_cap_invs_map set_cap_pas_refined_not_transferable)
   apply wp
  apply (clarsimp simp: valid_page_inv_def authorised_page_inv_def cte_wp_at_caps_of_state
                        is_frame_cap_def is_arch_update_def cap_master_cap_def
                 split: arch_cap.splits)
  apply (rule conjI)
   apply (fastforce dest: vs_lookup_slot_unique_level simp: same_ref_def parent_for_refs_def)
  apply (fastforce dest: vs_lookup_slot_unique_level caps_of_state_valid
                   simp: valid_arch_cap_def valid_cap_def cap_aligned_def)
  done

lemma perform_page_invocation_pas_refined:
  "\<lbrace>pas_refined aag and invs and authorised_page_inv aag pgi and valid_page_inv pgi\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_page_invocation_def perform_flush_def
  apply (wpsimp wp: perform_pg_inv_map_pas_refined perform_pg_inv_unmap_pas_refined)
  apply auto
  done

lemma unmap_page_respects:
  "\<lbrace>integrity aag X st and pspace_aligned and valid_vspace_objs and valid_arch_state
                       and K (is_subject_asid aag asid) and pas_refined aag
                       and K (vptr \<in> user_region)\<rbrace>
   unmap_page sz asid vptr pptr
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_page_def swp_def cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wpsimp wp: store_pte_respects
                     hoare_drop_imps[where Q="\<lambda>rv. integrity aag X st"]
               simp: is_aligned_mask[symmetric] cleanByVA_PoU_def
                     invalidate_tlb_by_asid_va_def invalidateTranslationSingle_def
          | wp (once) hoare_drop_imps
          | wp (once) hoare_drop_imps[where Q'="\<lambda>rv s. rv"])+
  apply (clarsimp simp: pt_lookup_slot_def)
  apply (frule pt_lookup_slot_from_level_is_subject)
          apply (fastforce simp: valid_arch_state_asid_table
                           dest: vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup])+
   apply (erule (1) is_subject_asid_trans)
   apply (clarsimp simp: pas_refined_def entry_for_asid_def entry_for_pool_def vspace_for_asid_def)
   apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
   apply (rule sata_asid_lookup)
    apply (fastforce simp: pool_for_asid_def)
   apply (frule pool_for_asid_vs_lookupD)
   apply (erule state_vrefsD)
     apply (fastforce simp: vspace_for_pool_def opt_map_def split: option.splits)
    apply assumption
   apply (fastforce simp: vs_refs_aux_def graph_of_def asid_low_bits_of_mask_eq[symmetric] word_size
                          ucast_ucast_b ucast_up_ucast_id is_up_def source_size_def target_size_def)
  apply simp
  done

lemma set_cap_vmid_for_asid[wp]:
  "set_cap cap cslot
   \<lbrace>\<lambda>s. P (vmid_for_asid s asid)\<rbrace>"
  apply (simp add: set_cap_def)
  apply (wpsimp wp: get_object_wp set_object_wp)
  by (auto simp: obj_at_def opt_map_def vmid_for_asid_def obind_def entry_for_pool_def
          split: if_splits option.splits)

crunch isb, dsb
  for vcpu_state[wp]: "\<lambda>s. P (vcpu_state s)"
  and fpu_state[wp]: "\<lambda>s. P (fpu_state s)"

lemma perform_page_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and authorised_page_inv aag pgi
                       and valid_page_inv pgi and valid_vspace_objs
                       and pspace_aligned and valid_vspace_objs and valid_arch_state
                       and is_subject aag  \<circ> cur_thread\<rbrace>
   perform_page_invocation pgi
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
proof -
  have set_tl_subset_mp: "\<And>xs a. a \<in> set (tl xs) \<Longrightarrow> a \<in> set xs" by (case_tac xs; clarsimp)
  show ?thesis
    apply (unfold authorised_page_inv_def)
    apply (simp add: perform_page_invocation_def mapM_discarded swp_def valid_page_inv_def
                     valid_unmap_def authorised_page_inv_def authorised_slots_def
                     perform_pg_inv_map_def perform_pg_inv_unmap_def
                     invalidate_tlb_by_asid_va_def invalidateTranslationSingle_def
                     cleanByVA_PoU_def perform_flush_def do_flush_def
              split: page_invocation.split sum.split
                     arch_cap.split option.split, safe)
        apply ((wp set_cap_integrity_autarch unmap_page_respects
                   mapM_x_and_const_wp[OF store_pte_respects] store_pte_respects
                   hoare_vcg_if_lift hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_disj_lift
               | elim conjE
               | clarsimp dest!: set_tl_subset_mp split del: if_split
               | wpc)+)
      apply (rule conjI)
       apply (case_tac m; clarsimp)
       apply (clarsimp simp: aag_cap_auth_def cte_wp_at_caps_of_state)
       apply (prop_tac "a \<in> acap_asid' (FrameCap r R sz dev (Some (a,b)))", clarsimp)
       apply (drule (1) sata_asid[where aag=aag])
       apply (clarsimp simp: pas_refined_def)
       apply (drule (1) subsetD)
       apply (fastforce dest: aag_wellformed_Control)
      apply (fastforce simp: valid_arch_cap_def wellformed_mapdata_def split: if_splits)
     apply (wpsimp wp: set_mrs_integrity_autarch set_message_info_integrity_autarch dmo_no_mem_respects
                 simp: ipc_buffer_has_auth_def perform_pg_inv_get_addr_def)+
    done
qed

lemma asid_table_entry_update_integrity:
 "\<lbrace>\<lambda>s. integrity aag X st s \<and> atable = arm_asid_table (arch_state s)
                            \<and> (\<forall>v. vopt = Some v \<longrightarrow> is_subject aag v)
                            \<and> (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
                                       \<longrightarrow> is_subject_asid aag asid')\<rbrace>
  modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := atable(asid_high_bits_of asid := vopt)\<rparr>\<rparr>)
  \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp: integrity_def integrity_asids_def integrity_hyp_def integrity_fpu_def)

definition authorised_asid_control_inv :: "'a PAS \<Rightarrow> asid_control_invocation \<Rightarrow> bool" where
 "authorised_asid_control_inv aag aci \<equiv>
  case aci of MakePool frame slot parent base \<Rightarrow>
    is_subject aag (fst slot) \<and> is_aligned frame pageBits \<and>
    (\<forall>asid. is_subject_asid aag asid) \<and> is_subject aag (fst parent) \<and>
            (\<forall>x \<in> {frame..frame + 2 ^ pageBits - 1}. is_subject aag x)"

lemma perform_asid_control_invocation_respects:
  "\<lbrace>integrity aag X st and invs and valid_aci aci and K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (wpc, simp)
   apply (wpsimp wp: hoare_weak_lift_imp set_cap_integrity_autarch asid_table_entry_update_integrity
                     cap_insert_integrity_autarch retype_region_integrity[where sz=12]
                     delete_objects_valid_vspace_objs delete_objects_valid_arch_state)
  apply (clarsimp simp: authorised_asid_control_inv_def ptr_range_def add.commute range_cover_def
                        obj_bits_api_def default_arch_object_def pageBits_def word_bits_def)
  apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
  apply (clarsimp simp: and_mask_eq_iff_shiftr_0 mask_zero word_size_bits_def)
  apply (frule is_aligned_no_overflow_mask)
  apply (clarsimp simp: mask_def)
  done

lemma state_vrefs_asid_pool_map:
  "\<lbrakk> ako_at (ASIDPool Map.empty) frame s; asid_table s (asid_high_bits_of base) = None \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := \<lambda>a. if a = asid_high_bits_of base
                                                                           then Some frame
                                                                           else asid_table s a\<rparr>\<rparr>)
         = state_vrefs s"
  apply (rule all_ext)
  apply clarsimp
  apply safe
   apply (subst (asm) state_vrefs_def, clarsimp)
   apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
    apply (clarsimp simp: vs_lookup_table_def pool_for_asid_def vspace_for_pool_def entry_for_pool_def
                          graph_of_def obj_at_def vs_refs_aux_def aobjs_of_Some vspace_objs_of_Some
                   split: if_splits)
   apply (subst (asm) asid_update.vs_lookup_table[simplified fun_upd_def])
    apply (clarsimp simp: asid_update_def asid_pools_of_ko_at)
   apply (clarsimp split: if_splits)
   apply (erule (3) state_vrefsD)
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
   apply (clarsimp simp: vs_lookup_table_def pool_for_asid_def)
  apply (rule_tac level=bot and asid=asid and vref=vref in state_vrefsD)
     apply (subst asid_update.vs_lookup_table[simplified fun_upd_def])
      apply (clarsimp simp: asid_update_def asid_pools_of_ko_at)
     apply fastforce
    apply (fastforce simp: aobjs_of_Some)
   apply clarsimp
  apply clarsimp
  done

lemma pas_refined_asid_control_helper:
  "authorised_asid_control_inv aag (MakePool frame slot parent base) \<Longrightarrow>
  \<lbrace>\<lambda>s. pas_refined aag s \<and> ko_at (ArchObj (ASIDPool Map.empty)) frame s
                         \<and> asid_table s (asid_high_bits_of base) = None\<rbrace>
  do asid_table <- gets asid_table;
     asid_table' <- return (asid_table(asid_high_bits_of base \<mapsto> frame));
     modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := asid_table'\<rparr>\<rparr>)
  od
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding pas_refined_def
  apply wpsimp
  apply (rule conjI)
   apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
   apply (erule state_bits_to_policy.cases)
          apply (fastforce dest: sbta_caps)
         apply (fastforce dest: sbta_untyped)
        apply (fastforce dest: sbta_ts)
       apply (fastforce dest: sbta_bounds)
      apply (fastforce dest: sbta_cdt)
     apply (fastforce dest: sbta_cdt_transferable)
    apply (fastforce dest: sbta_vref simp: state_vrefs_asid_pool_map)
   apply (fastforce simp: sbta_href state_vrefs_asid_pool_map)
  apply clarsimp
  apply (erule state_asids_to_policy_aux.cases)
    apply (fastforce dest: sata_asid)
   apply (subst (asm) state_vrefs_asid_pool_map; clarsimp)
   apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
    apply (clarsimp simp: state_vrefs_def aobjs_of_Some vspace_objs_of_Some obj_at_def vs_refs_aux_def graph_of_def)
   apply (drule sata_asid_lookup[rotated]; fastforce)
  apply (clarsimp split: if_splits)
   apply (fastforce simp: authorised_asid_control_inv_def is_aligned_no_overflow aag_wellformed_refl)
  apply (fastforce dest: sata_asidpool)
  done

lemma perform_asid_control_invocation_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and valid_aci aci and ct_active
                    and K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: perform_asid_control_invocation_def )
  apply wpc
   apply (rule pas_refined_asid_control_helper bind_wp hoare_K_bind)+
         apply (wp cap_insert_pas_refined' hoare_weak_lift_imp | simp)+
      apply ((wp retype_region_pas_refined'[where sz=pageBits]
                 hoare_vcg_ex_lift hoare_vcg_all_lift hoare_weak_lift_imp hoare_wp_combs hoare_drop_imp
                 retype_region_invs_extras(1)[where sz = pageBits]
                 retype_region_invs_extras(4)[where sz = pageBits]
                 retype_region_invs_extras(6)[where sz = pageBits]
                 retype_region_invs_extras(7)[where sz = pageBits]
                 retype_region_cte_at_other'[where sz=pageBits]
                 max_index_upd_invs_simple max_index_upd_caps_overlap_reserved
                 hoare_vcg_ex_lift set_cap_cte_wp_at hoare_vcg_disj_lift set_free_index_valid_pspace
                 set_cap_descendants_range_in set_cap_no_overlap get_cap_wp set_cap_caps_no_overlap
                 hoare_vcg_all_lift hoare_weak_lift_imp retype_region_invs_extras
                 set_cap_pas_refined_not_transferable arch_update_cap_valid_mdb
             | simp add: do_machine_op_def region_in_kernel_window_def cte_wp_at_neg2)+)[3]
   apply (rename_tac frame slot parent base )
   apply (case_tac slot, rename_tac slot_ptr slot_idx)
   apply (case_tac parent, rename_tac parent_ptr parent_idx)
   apply (rule_tac Q'="\<lambda>rv s.
             (\<exists>idx. cte_wp_at ((=) (UntypedCap False frame pageBits idx)) parent s) \<and>
             (\<forall>x\<in>ptr_range frame pageBits. is_subject aag x) \<and>
             pas_refined aag s \<and> pas_cur_domain aag s \<and>
             pspace_no_overlap_range_cover frame pageBits s \<and>
             invs s \<and> asid_table s (asid_high_bits_of base) = None \<and>
             descendants_range_in {frame..(frame && ~~ mask pageBits) + 2 ^ pageBits - 1} parent s \<and>
             range_cover frame pageBits (obj_bits_api (ArchObject ASIDPoolObj) 0) (Suc 0) \<and>
             is_subject aag slot_ptr \<and> is_subject aag parent_ptr \<and> is_subject aag frame \<and>
             pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap frame base)) \<and>
             (\<forall>x. asid_high_bits_of x = asid_high_bits_of base \<longrightarrow> is_subject_asid aag x)"
             in hoare_strengthen_post)
    apply (wp add: delete_objects_pspace_no_overlap hoare_vcg_ex_lift
                   delete_objects_descendants_range_in delete_objects_invs_ex
                   delete_objects_pas_refined
              del: Untyped_AI.delete_objects_pspace_no_overlap
           | simp add: )+
   apply clarsimp
   apply (rename_tac s idx)
   apply (frule untyped_cap_aligned, simp add: invs_valid_objs)
   apply (clarsimp simp: cte_wp_at_def aag_cap_auth_def ptr_range_def pas_refined_refl
                         cap_links_asid_slot_def cap_links_irq_def obj_bits_api_def
                         default_arch_object_def retype_addrs_def conj_ac
                         invs_psp_aligned invs_valid_pspace invs_vspace_objs invs_arch_state)
   apply (rule conjI, force intro: descendants_range_caps_no_overlapI simp: cte_wp_at_def)
   apply (rule conjI, clarsimp simp: max_free_index_def)
   apply (prop_tac "valid_cap (UntypedCap False frame pageBits idx) s")
    apply (clarsimp simp: get_cap_caps_of_state)
    apply (simp add: Untyped_AI.caps_of_state_valid)
   apply (clarsimp simp: free_index_of_def max_free_index_def valid_cap_def)
   apply (rule conjI)
    apply (cut_tac s=s and ptr="(parent_ptr, parent_idx)" in cap_refs_in_kernel_windowD)
      apply ((fastforce simp: caps_of_state_def cap_range_def)+)[3]
   apply (fastforce simp: x_power_minus_1 is_aligned_no_overflow')
  apply (clarsimp simp: valid_aci_def authorised_asid_control_inv_def cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (drule untyped_slots_not_in_untyped_range)
        apply (erule empty_descendants_range_in)
       apply (simp add: cte_wp_at_caps_of_state)
      apply simp
     apply simp
    apply (rule subset_refl)
   apply simp
  apply (frule_tac x=x in bspec)
   apply (simp add: is_aligned_no_overflow)
  apply (clarsimp simp: ptr_range_def invs_psp_aligned invs_valid_objs aag_cap_auth_def
                        descendants_range_def2 empty_descendants_range_in
                        pas_refined_refl cap_links_asid_slot_def label_owns_asid_slot_def
                        cap_links_irq_def range_cover_def obj_bits_api_def pageBits_def
                        default_arch_object_def and_mask_eq_iff_shiftr_0 mask_zero)
  apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
  apply (intro conjI; fastforce intro: empty_descendants_range_in)
  done

definition authorised_asid_pool_inv :: "'a PAS \<Rightarrow> asid_pool_invocation \<Rightarrow> bool" where
 "authorised_asid_pool_inv aag api \<equiv>
  case api of Assign asid pool_ptr ct_slot \<Rightarrow>
    is_subject aag pool_ptr \<and> is_subject aag (fst ct_slot) \<and> is_subject_asid aag asid"

lemma perform_asid_pool_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and valid_apinv api
                       and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (unfold perform_asid_pool_invocation_def store_asid_pool_entry_def)
  apply (wpsimp wp: set_asid_pool_integrity_autarch get_cap_wp
                    set_cap_integrity_autarch hoare_drop_imps)
  apply (clarsimp simp: authorised_asid_pool_inv_def)
  done

lemma store_pte_state_vrefs_unreachable:
  "\<lbrace>\<lambda>s. P (state_vrefs s) \<and> pspace_aligned s \<and> valid_vspace_objs s \<and>
        valid_asid_table s \<and> (\<forall>level. \<not> \<exists>\<rhd> (level, table_base pt_t p) s)\<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (wpsimp simp: store_pte_def set_pt_def wp: set_object_wp)
  apply (erule rsubst[where P=P])
  apply (rule all_ext)
  apply (rule allI, rename_tac x)
  apply safe
   apply (subst (asm) state_vrefs_def, clarsimp)
   apply (rule state_vrefsD)
      apply (subst vs_lookup_table_unreachable_upd_idem; fastforce)
     apply (drule vs_lookup_level)
     apply (prop_tac "x \<noteq> table_base pt_t p", clarsimp)
     apply (fastforce simp: fun_upd_def aobjs_of_Some opt_map_def)
    apply clarsimp
   apply fastforce
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule state_vrefsD)
     apply (subst (asm) vs_lookup_table_unreachable_upd_idem; fastforce)
    apply (prop_tac "x \<noteq> table_base pt_t p")
     apply (subst (asm) vs_lookup_table_unreachable_upd_idem; fastforce dest: vs_lookup_level)
    apply (fastforce simp: fun_upd_def aobjs_of_Some)
   apply clarsimp
  apply clarsimp
  done

lemma store_asid_pool_entry_state_vrefs:
  "\<lbrace>\<lambda>s. P (\<lambda>x. if x = pool_ptr
               then vs_refs_aux asid_pool_level (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid
                                                               then Some (ASIDPoolVSpace None pt_base)
                                                               else the (asid_pools_of s pool_ptr) a))
               else if x = pt_base
               then vs_refs_aux max_pt_level (the (vspace_objs_of s x))
               else state_vrefs s x) \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        pool_for_asid asid s = Some pool_ptr \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<exists>pt. pts_of s pt_base = Some (empty_pt VSRootPT_T))\<rbrace>
   store_asid_pool_entry pool_ptr asid (Some (ASIDPoolVSpace None pt_base))
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding store_asid_pool_entry_def set_asid_pool_def
  apply (wpsimp wp: set_object_wp get_cap_wp)
  apply (erule rsubst[where P=P])
  apply (rule all_ext)
  apply (clarsimp split del: if_split)
  apply (prop_tac "is_aligned pt_base (pt_bits (pt_type (empty_pt VSRootPT_T)))")
   apply (fastforce elim: pspace_aligned_pts_ofD dest: invs_psp_aligned)
  apply safe
   apply (clarsimp split: if_splits)
     apply (frule pool_for_asid_vs_lookupD)
     apply (rule_tac level=asid_pool_level in state_vrefsD)
        apply (simp only: fun_upd_def)
        apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
          apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at
                                 valid_apinv_def asid_low_bits_of_def )
         apply fastforce
        apply fastforce
       apply fastforce
      apply (fastforce simp: ako_asid_pools_of)
     apply (clarsimp simp: ako_asid_pools_of)
    apply (rule_tac level=max_pt_level and vref=0 in state_vrefsD)
       apply (simp only: fun_upd_def)
       apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
         apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at
                                valid_apinv_def asid_low_bits_of_def aobjs_of_Some)
        apply clarsimp
       apply fastforce
      apply (fastforce simp: vspace_objs_of_Some pts_of_Some)
     apply (fastforce simp: pts_of_Some)
    apply (clarsimp simp: vspace_obj_of_def opt_map_def split: option.splits)
   apply (clarsimp simp: obj_at_def)
   apply (subst (asm) state_vrefs_def, clarsimp)
   apply (rename_tac asida vref)
   apply (rule_tac asid=asida in state_vrefsD)
      apply (simp only: fun_upd_def)
      apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
        apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at obj_at_def
                               valid_apinv_def asid_low_bits_of_def aobjs_of_Some)
       apply fastforce
      apply (prop_tac "asid \<noteq> asida")
       apply (fastforce simp: vs_lookup_table_def entry_for_pool_def vspace_for_pool_def
                              asid_pools_of_ko_at obj_at_def
                       split: if_splits)
      apply fastforce
     apply fastforce
    apply fastforce
   apply clarsimp
  apply (subst (asm) state_vrefs_def, clarsimp split del: if_split)
  apply (simp only: fun_upd_def)
  apply (subst (asm) asid_pool_map.vs_lookup_table[simplified fun_upd_def])
    apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at
                           valid_apinv_def asid_low_bits_of_def aobjs_of_Some)
   apply clarsimp
  apply (case_tac "x = pool_ptr")
   apply (prop_tac "asid_pools_of s pool_ptr = Some rv")
    apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)
   apply (clarsimp simp: vs_refs_aux_def)
  apply (case_tac "asida = asid \<and> bot \<le> max_pt_level"; clarsimp)
  apply (clarsimp simp: vspace_obj_of_def opt_map_def split: option.splits)
  apply (case_tac "x = pt_base")
   apply (fastforce dest: vs_lookup_level)
  apply clarsimp
  apply (fastforce simp: state_vrefs_def vspace_obj_of_def opt_map_def split: option.splits)
  done

crunch store_asid_pool_entry
  for irq_map_wellformed[wp]: "\<lambda>s. P (irq_map_wellformed aag s)"
  and tcb_domain_map_wellformed[wp]: "\<lambda>s. P (tcb_domain_map_wellformed aag s)"
  and state_irqs_to_policy[wp]: "\<lambda>s. P (state_irqs_to_policy aag s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and thread_st_auth[wp]: "\<lambda>s. P (thread_st_auth s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"
  and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"

lemma store_asid_pool_entry_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        pool_for_asid asid s = Some pool_ptr \<and> is_subject aag pool_ptr \<and>
        is_subject aag pt_base \<and> is_subject_asid aag asid \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<exists>pt. pts_of s pt_base = Some (empty_pt VSRootPT_T))\<rbrace>
   store_asid_pool_entry pool_ptr asid (Some (ASIDPoolVSpace None pt_base))
   \<lbrace>\<lambda>_ s. pas_refined aag s\<rbrace>"
  apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply wps
   apply (wp store_asid_pool_entry_state_vrefs store_asid_pool_entry_state_vrefs)
  apply (clarsimp simp: auth_graph_map_def)
  apply (frule (1) pool_for_asid_validD)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (erule state_bits_to_policy.cases)
          apply (fastforce simp: state_objs_to_policy_def dest: sbta_caps)
         apply (fastforce simp: state_objs_to_policy_def dest: sbta_untyped)
        apply (fastforce simp: state_objs_to_policy_def dest: sbta_ts)
       apply (fastforce simp: state_objs_to_policy_def dest: sbta_bounds)
      apply (fastforce simp: state_objs_to_policy_def dest: sbta_cdt)
     apply (fastforce simp: state_objs_to_policy_def dest: sbta_cdt_transferable)
    apply (case_tac "ptr = pool_ptr")
     apply (clarsimp simp: vs_refs_aux_def graph_of_def aag_wellformed_refl split: if_splits)
     apply (erule subsetD)
     apply clarsimp
     apply (rule_tac x=pool_ptr in exI, clarsimp)
     apply (rule exI, rule conjI, rule refl)
     apply (rule sbta_vref)
     apply (drule pool_for_asid_vs_lookupD)
     apply (erule_tac vref=0 in state_vrefsD)
       apply (fastforce simp: asid_pools_of_ko_at aobjs_of_ako_at_Some vspace_objs_of_Some)
      apply clarsimp
     apply (fastforce simp: vs_refs_aux_def graph_of_def)
    apply (fastforce simp: vs_refs_aux_def empty_pt_def vspace_obj_of_def opt_map_def
                           graph_of_def pts_of_Some pte_ref2_def
                     dest: sbta_vref split: if_splits option.splits)
   apply (fastforce simp: state_objs_to_policy_def sbta_href)
  apply (erule state_asids_to_policy_aux.cases)
    apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
    apply (fastforce dest: sata_asid)
   apply (case_tac "poolptr = pool_ptr")
    apply (clarsimp simp: vs_refs_aux_def graph_of_def obj_at_def split: if_splits)
     apply (clarsimp simp: pool_for_asid_def asid_pools_of_ko_at valid_asid_table_def inj_on_def)
     apply (drule_tac x="asid_high_bits_of asid" in bspec, clarsimp)
     apply (drule_tac x="asid_high_bits_of asida" in bspec, clarsimp)
     apply clarsimp
     apply (drule asid_high_low_inj[rotated])
      apply (simp add: asid_low_bits_of_mask_eq[symmetric])
      apply (prop_tac "is_up UCAST(9 \<rightarrow> 16) \<and> is_up UCAST(9 \<rightarrow> 64)")
       apply (clarsimp simp: is_up_def source_size_def target_size_def word_size)
      apply (clarsimp simp: ucast_ucast_b)
      apply (metis ucast_up_ucast_id)
     apply (fastforce simp: aag_wellformed_refl)
    apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
    apply (rule sata_asid_lookup, fastforce)
    apply (frule pool_for_asid_vs_lookupD)
    apply (erule_tac vref=0 in state_vrefsD)
      apply (fastforce simp: asid_pools_of_ko_at aobjs_of_ako_at_Some vspace_objs_of_Some)
     apply simp
    apply (fastforce simp: vs_refs_aux_def graph_of_def)
   apply (case_tac "poolptr = pt_base")
    apply (fastforce simp: vs_refs_aux_def pts_of_Some empty_pt_def vspace_obj_of_def opt_map_def
                    split: option.splits)
   apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
   apply (fastforce simp: sata_asid_lookup)
  apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
  apply (fastforce simp: sata_asidpool)
  done

lemma perform_asid_pool_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and valid_apinv api and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)
  apply (strengthen invs_psp_aligned invs_vspace_objs valid_arch_state_asid_table invs_arch_state |
         wpsimp simp: ako_asid_pools_of
                  wp: store_asid_pool_entry_pas_refined set_cap_pas_refined get_cap_wp
                      arch_update_cap_invs_map hoare_vcg_all_lift hoare_vcg_imp_lift')+
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_apinv_def cong: conj_cong)
  apply (clarsimp simp: is_PageTableCap_def is_ArchObjectCap_def)
  apply (clarsimp simp: authorised_asid_pool_inv_def is_arch_update_def update_map_data_def
                        is_cap_simps cap_master_cap_def asid_bits_of_defs
                 split: option.splits)
  apply (intro conjI)
      apply (fastforce dest: cap_cur_auth_caps_of_state pas_refined_refl
                       simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                             cap_links_asid_slot_def label_owns_asid_slot_def cap_links_irq_def)
     apply (fastforce dest: caps_of_state_valid
                      simp: update_map_data_def valid_cap_def cap_aligned_def wellformed_mapdata_def)
    apply (fastforce dest: cap_cur_auth_caps_of_state pas_refined_Control
                     simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
   apply (frule (1) caps_of_state_valid)
   apply (clarsimp simp: valid_cap_def)
   apply (clarsimp simp: obj_at_def)
   apply (rename_tac asid' pool_ptr a b acap_obj level asid vref pt)
   apply (drule (1) vs_lookup_table_valid_cap; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap_and_type)
     apply (simp add: pts_of_Some aobjs_of_Some)
    apply (fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp simp: is_cap_simps)
  apply (fastforce dest: invs_valid_table_caps simp: valid_table_caps_def is_vsroot_cap_def )
  done

crunch do_flush
  for vcpu_state[wp]: "\<lambda>s. P (vcpu_state s)"
  and fpu_state[wp]: "\<lambda>s. P (fpu_state s)"

lemma perform_vspace_invocation_respects[wp]:
  "perform_vspace_invocation iv \<lbrace>integrity aag X st\<rbrace>"
  unfolding perform_vspace_invocation_def perform_flush_def
  by (wpsimp wp: dmo_no_mem_respects)

crunch perform_vspace_invocation
  for pas_refined[wp]: "pas_refined aag"

\<comment> \<open>Integrity minus integrity_hyp\<close>

definition integrity_no_hyp ::
  "'a PAS \<Rightarrow> obj_ref set \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "integrity_no_hyp aag X s s' \<equiv>
     integrity_obj_state aag (pasMayActivate aag) {pasSubject aag} s s' \<and>
     integrity_cdt_state aag {pasSubject aag} s s' \<and>
     (\<forall>x. cdt_list_integrity aag (cdt s) (tcb_states_of_state s) x (cdt_list s x) (cdt_list s' x)) \<and>
     (\<forall>x. integrity_interrupts aag {pasSubject aag} x
            (interrupt_irq_node s x, interrupt_states s x)
            (interrupt_irq_node s' x, interrupt_states s' x)) \<and>
     (\<forall>d p. integrity_ready_queues aag {pasSubject aag} (pasDomainAbs aag d)
              (ready_queues s d p) (ready_queues s' d p)) \<and>
     (\<forall>x. memory_integrity X aag x (tcb_states_of_state s) (tcb_states_of_state s')
            (auth_ipc_buffers s) (underlying_memory (machine_state s) x)
            (underlying_memory (machine_state s') x)) \<and>
     (\<forall>x. integrity_device aag {pasSubject aag} x (tcb_states_of_state s)
            (tcb_states_of_state s') (device_state (machine_state s) x)
            (device_state (machine_state s') x)) \<and>
     (\<forall>x a. integrity_asids aag {pasSubject aag} x a s s') \<and>
     (\<forall>x. integrity_fpu aag {pasSubject aag} x s s')"

lemma integrity_no_hyp_absorb:
  "integrity aag X st s = (integrity_no_hyp aag X st s \<and> (\<forall>x. integrity_hyp aag {pasSubject aag} x st s))"
  by (auto simp: integrity_def integrity_no_hyp_def)

lemma dmo_no_mem_integrity_no_hyp:
  assumes p: "\<And>P. mop \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes q: "\<And>P. mop \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  assumes r: "\<And>P. mop \<lbrace>\<lambda>ms. P (fpu_state ms)\<rbrace>"
  shows "do_machine_op mop \<lbrace>integrity_no_hyp aag X st\<rbrace>"
  unfolding tcb_states_of_state_def get_tcb_def integrity_no_hyp_def
            integrity_fpu_def integrity_fpu_def integrity_asids_def
  by (wpsimp wp: dmo_machine_state_lift | wps assms)+

lemma tcb_states_of_state_fun_upd:
  "map_option tcb_state (get_tcb p s) = (case val of TCB tcb \<Rightarrow> Some (tcb_state tcb) | _ \<Rightarrow> None)
   \<Longrightarrow> tcb_states_of_state (s\<lparr>kheap := (kheap s)(p \<mapsto> val)\<rparr>) = tcb_states_of_state s"
  by (fastforce simp: tcb_states_of_state_def get_tcb_def split: kernel_object.splits)

lemma thread_st_auth_fun_upd:
  "map_option tcb_state (get_tcb p s) = (case val of TCB tcb \<Rightarrow> Some (tcb_state tcb) | _ \<Rightarrow> None)
   \<Longrightarrow> thread_st_auth (s\<lparr>kheap := (kheap s)(p \<mapsto> val)\<rparr>) = thread_st_auth s"
  by (auto simp: tcb_states_of_state_fun_upd thread_st_auth_def)

lemma thread_bound_ntfns_fun_upd:
  "map_option tcb_bound_notification (get_tcb p s) =
   (case val of TCB tcb \<Rightarrow> Some (tcb_bound_notification tcb) | _ \<Rightarrow> None)
   \<Longrightarrow> thread_bound_ntfns (s\<lparr>kheap := (kheap s)(p \<mapsto> val)\<rparr>) = thread_bound_ntfns s"
  by (fastforce simp: thread_bound_ntfns_def get_tcb_def split: kernel_object.splits)

lemma vcpu_update_integrity_no_hyp:
  "vcpu_update vr f \<lbrace>integrity_no_hyp aag X st\<rbrace>"
  unfolding vcpu_update_def readVCPUHardwareReg_def integrity_no_hyp_def
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (erule_tac x=vr in allE)
  apply (auto elim!: tro_trans_spec trfpu_trans trasids_trans
               simp: integrity_asids_def integrity_fpu_def fpu_of_state_def in_opt_map_eq
                     tcb_states_of_state_fun_upd get_tcb_def obj_at_def
             intro!: tro_arch arch_troa_vcpu)
  done

lemma integrity_no_hyp_arm_current_vcpu[simp]:
  "integrity_no_hyp aag X st (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := v\<rparr>\<rparr>) =
   integrity_no_hyp aag X st s"
  by (simp add: integrity_no_hyp_def integrity_asids_def integrity_fpu_def)

crunch readVCPUHardwareReg, writeVCPUHardwareReg, read_cntpct,
       check_export_arch_timer, maskInterrupt, setHCR, setSCTLR, enableFpuEL01,
       set_gic_vcpu_ctrl_hcr, set_gic_vcpu_ctrl_vmcr, set_gic_vcpu_ctrl_apr, set_gic_vcpu_ctrl_lr,
       get_gic_vcpu_ctrl_hcr, get_gic_vcpu_ctrl_vmcr, get_gic_vcpu_ctrl_apr, get_gic_vcpu_ctrl_lr
  for fpu_state[wp]: "\<lambda>s. P (fpu_state s)"

crunch vcpu_switch
  for integrity_no_hyp[wp]: "integrity_no_hyp aag X st"
  (wp: dmo_no_mem_integrity_no_hyp crunch_wps)

\<comment> \<open>VCPU Projections\<close>

definition vcpu_proj where
  "vcpu_proj regs lrs hcr vmcr apr vcpu_ptr s \<equiv> case vcpus_of s vcpu_ptr of
     None \<Rightarrow> None
   | Some vcpu \<Rightarrow> Some (vcpu\<lparr>vcpu_vtimer := undefined,
                             vcpu_regs := \<lambda>reg. if reg = VCPURegCNTVOFF then undefined
                                                else if reg \<in> regs then vcpu_regs vcpu reg
                                                else vcpu_regs (vcpu_state (machine_state s)) reg,
                             vcpu_vgic := (vcpu_vgic vcpu)
                               \<lparr>vgic_hcr := if hcr then vgic_hcr (vcpu_vgic vcpu)
                                            else vgic_hcr (vcpu_vgic (vcpu_state (machine_state s))),
                                vgic_vmcr := if vmcr then vgic_vmcr (vcpu_vgic vcpu)
                                             else vgic_vmcr (vcpu_vgic (vcpu_state (machine_state s))),
                                vgic_apr := if apr then vgic_apr (vcpu_vgic vcpu)
                                            else vgic_apr (vcpu_vgic (vcpu_state (machine_state s))),
                                vgic_lr := \<lambda>r. if r \<ge> (arm_gicvcpu_numlistregs (arch_state s)) then undefined
                                               else if r \<in> lrs then vgic_lr (vcpu_vgic vcpu) r
                                               else vgic_lr (vcpu_vgic (vcpu_state (machine_state s))) r\<rparr>\<rparr>)"

abbreviation (input)
  "vtimerRegs \<equiv> {VCPURegCNTV_CTL,VCPURegCNTV_CVAL,VCPURegCNTVOFF,VCPURegCNTKCTL_EL1}"
abbreviation (input)
  "savedWhenDisabledRegs \<equiv> {VCPURegSCTLR,VCPURegCPACR} \<union> vtimerRegs"

lemma savedWhenDisabledRegs_def:
  "savedWhenDisabledRegs = Collect vcpuRegSavedWhenDisabled"
  by (auto simp: vcpuRegSavedWhenDisabled_def split: vcpureg.splits)

lemma vcpu_proj_of_state:
  "vcpu_of_state (vcpu_state (machine_state s)) vcpu
                 (arm_gicvcpu_numlistregs (arch_state s)) (vcpus_of s) vr =
   (if vcpu = Some (vr,True) then vcpu_proj {} {} False False False vr s
    else if vcpu = Some (vr,False) then vcpu_proj savedWhenDisabledRegs {} True False False vr s
    else vcpu_proj UNIV UNIV True True True vr s)"
  unfolding savedWhenDisabledRegs_def vcpu_proj_def vcpu_of_state_def
  by (auto split: option.splits)

lemma dmo_lift_vcpu_proj:
  assumes r: "\<And>P. mop \<lbrace>\<lambda>ms. P (vcpu_state ms)\<rbrace>"
  shows "do_machine_op mop \<lbrace>\<lambda>s. P (vcpu_proj r l h v a vr s)\<rbrace>"
  unfolding vcpu_proj_def
  apply (rule hoare_weaken_pre)
   apply (wps r | wp dmo_machine_state_lift | simp)+
  done

crunch maskInterrupt, read_cntpct, setHCR, get_gic_vcpu_ctrl_lr
  for vcpu_state[wp]: "\<lambda>ms. P (vcpu_state ms)"

crunch get_gic_vcpu_ctrl_hcr, get_gic_vcpu_ctrl_vmcr, get_gic_vcpu_ctrl_apr
  for inv[wp]: P

\<comment> \<open>VGIC\<close>

lemma get_gic_vcpu_ctrl_rvs[wp]:
 "\<lbrace>\<top>\<rbrace> do_machine_op get_gic_vcpu_ctrl_hcr
  \<lbrace>\<lambda>hcr s. hcr = vgic_hcr (vcpu_vgic (vcpu_state (machine_state s)))\<rbrace>"

 "\<lbrace>\<top>\<rbrace> do_machine_op get_gic_vcpu_ctrl_apr
  \<lbrace>\<lambda>apr s. apr = vgic_apr (vcpu_vgic (vcpu_state (machine_state s)))\<rbrace>"

 "\<lbrace>\<top>\<rbrace> do_machine_op get_gic_vcpu_ctrl_vmcr
  \<lbrace>\<lambda>vmcr s. vmcr = vgic_vmcr (vcpu_vgic (vcpu_state (machine_state s)))\<rbrace>"
  unfolding get_gic_vcpu_ctrl_hcr_def get_gic_vcpu_ctrl_apr_def get_gic_vcpu_ctrl_vmcr_def
  by (wpsimp wp: dmo_wp)+

lemma get_lr_rv[wp]:
 "\<lbrace>\<lambda>s. n < arm_gicvcpu_numlistregs (arch_state s) \<and> valid_arch_state s\<rbrace>
  do_machine_op (get_gic_vcpu_ctrl_lr (word_of_nat n))
  \<lbrace>\<lambda>hcr s. hcr = vgic_lr (vcpu_vgic (vcpu_state (machine_state s))) n\<rbrace>"
  unfolding get_gic_vcpu_ctrl_lr_def
  by (wpsimp wp: dmo_wp simp: valid_arch_state_def valid_numlistregs_def unat_of_nat64)

lemma set_gic_vcpu_ctrl_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj r l True v a p s \<and>
        (\<forall>vcpu. vopt = Some vcpu \<and> \<not>h \<longrightarrow> val = vgic_hcr (vcpu_vgic vcpu))\<rbrace>
   do_machine_op (set_gic_vcpu_ctrl_hcr val)
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"

  "\<lbrace>\<lambda>s. vopt = vcpu_proj r l h True a p s \<and>
        (\<forall>vcpu. vopt = Some vcpu \<and> \<not>v \<longrightarrow> val = vgic_vmcr (vcpu_vgic vcpu))\<rbrace>
   do_machine_op (set_gic_vcpu_ctrl_vmcr val)
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"

  "\<lbrace>\<lambda>s. vopt = vcpu_proj r l h v True p s \<and>
        (\<forall>vcpu. vopt = Some vcpu \<and> \<not>a \<longrightarrow> val = vgic_apr (vcpu_vgic vcpu))\<rbrace>
   do_machine_op (set_gic_vcpu_ctrl_apr val)
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  unfolding set_gic_vcpu_ctrl_hcr_def set_gic_vcpu_ctrl_vmcr_def set_gic_vcpu_ctrl_apr_def
  by (wpsimp wp: dmo_wp simp: vcpu_proj_def)+

lemma set_lr_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj r (insert n l) h v a p s \<and>
        n < arm_gicvcpu_numlistregs (arch_state s) \<and>
        (\<forall>v. vopt = Some v \<and> n \<notin> l \<longrightarrow> w = vgic_lr (vcpu_vgic v) n) \<and>
        valid_arch_state s\<rbrace>
   do_machine_op (set_gic_vcpu_ctrl_lr (word_of_nat n) w)
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  unfolding set_gic_vcpu_ctrl_lr_def vcpu_proj_def valid_arch_state_def valid_numlistregs_def
  apply (wpsimp wp: dmo_wp)
  apply (auto intro!: vcpu.equality gic_vcpu_interface.equality
              simp: unat_of_nat64 split: if_splits option.split_asm)
  done

lemma set_lrs_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj r UNIV h v a p s \<and> valid_arch_state s \<and>
        ls = [0..<arm_gicvcpu_numlistregs (arch_state s)] \<and>
        (\<forall>v. vcpus_of s p = Some v \<and> l \<noteq> UNIV \<longrightarrow> f = vgic_lr (vcpu_vgic v))\<rbrace>
   do_machine_op (mapM (\<lambda>p. set_gic_vcpu_ctrl_lr (word_of_nat (fst p)) (snd p)) (map (\<lambda>i. (i, f i)) ls))
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  (is "valid (\<lambda>s. ?V UNIV s \<and> ?I s) _ _")
  apply (rule valid_return_unit)
  apply (simp add: dom_mapM comp_def mapM_x_mapM[symmetric])
  apply (wpsimp wp: mapM_x_inv_wp2[where I="?I" and V="\<lambda>rs s. ?V ((fst ` set rs) \<union> l) s"])
   apply (auto dest: set_mono_suffix simp: vcpu_proj_def image_iff split: option.splits)
  done

lemma vgic_update_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj r l (h \<and> vr \<noteq> p) v a p s \<and>
        val = vgic_hcr (vcpu_vgic (vcpu_state (machine_state s)))\<rbrace>
   vgic_update vr (vgic_hcr_update (\<lambda>_. val))
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"

  "\<lbrace>\<lambda>s. vopt = vcpu_proj r l h (v \<and> vr \<noteq> p) a p s \<and>
        val = vgic_vmcr (vcpu_vgic (vcpu_state (machine_state s)))\<rbrace>
   vgic_update vr (vgic_vmcr_update (\<lambda>_. val))
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"

  "\<lbrace>\<lambda>s. vopt = vcpu_proj r l h v (a \<and> vr \<noteq> p) p s \<and>
        val = vgic_apr (vcpu_vgic (vcpu_state (machine_state s)))\<rbrace>
   vgic_update vr (vgic_apr_update (\<lambda>_. val))
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  unfolding vgic_update_def vcpu_update_def vcpu_proj_def
  by (wp set_vcpu_wp get_vcpu_wp, fastforce)+

lemma save_lr_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj r (if vr = p then l - {n} else l) h v a p s \<and>
        irq = vgic_lr (vcpu_vgic (vcpu_state (machine_state s))) n \<and>
        n < arm_gicvcpu_numlistregs (arch_state s)\<rbrace>
   vgic_update_lr vr n irq
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  unfolding vgic_update_lr_def vgic_update_def vcpu_update_def
  apply (wp set_vcpu_wp get_vcpu_wp)
  apply (auto intro!: vcpu.equality gic_vcpu_interface.equality
                simp: vcpu_proj_def split: option.splits if_splits)
  done

lemma save_lrs_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj r (if vr = p then {} else l) h v a p s \<and>
        ls = [0..<arm_gicvcpu_numlistregs (arch_state s)] \<and> valid_arch_state s\<rbrace>
   mapM (\<lambda>r. do_machine_op (get_gic_vcpu_ctrl_lr (word_of_nat r)) >>= vgic_update_lr vr r) ls
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
   (is "valid (\<lambda>s. ?V {} s \<and> ?I s) _ _")
  apply (rule valid_return_unit)
  apply (fold mapM_x_mapM)
  apply (wpsimp wp: dmo_lift_vcpu_proj mapM_x_inv_wp2[where I="?I" and V="\<lambda>rs s. ?V (l - set rs) s"])
   apply (auto intro: arg_cong dest: set_mono_suffix)[1]
  apply (auto simp: vcpu_proj_def)
  done

\<comment> \<open>Disable/Save\<close>

lemma vcpu_save_reg_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj (if vr = p then r - {reg} else r) h v a lr p s\<rbrace>
   vcpu_save_reg vr reg
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r h v a lr p s\<rbrace>"
  unfolding vcpu_save_reg_def vcpu_update_def readVCPUHardwareReg_def
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp dmo_wp)
  apply (fastforce intro: vcpu.equality simp: vcpu_proj_def)
  done

lemma vcpu_save_reg_range_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj (if vr = p then (r - set [from .e. to]) else r) l h v a p s\<rbrace>
   vcpu_save_reg_range vr from to
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  (is "valid (\<lambda>s. ?V [_ .e. _] s) _ _")
  unfolding vcpu_save_reg_range_def
  by (wpsimp wp: mapM_x_inv_wp2[where I=\<top> and V="?V"] simp: Diff_insert[symmetric])

lemma modify_reg_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj r l h v a p s \<and> reg \<in> r\<rbrace>
   do_machine_op (modify (vcpu_state_update (vcpu_regs_update (\<lambda>r. r(reg := f r)))))
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  apply (wpsimp wp: dmo_wp simp: vcpu_proj_def)
  apply (fastforce intro: vcpu.equality split: option.splits)
  done

lemma vtimer_update_vcpu_proj:
  "vcpu_update vr (vcpu_vtimer_update (\<lambda>_. VirtTimer cntpct))
   \<lbrace>\<lambda>s. vopt = vcpu_proj r h v a lr p s\<rbrace>"
  unfolding vcpu_update_def
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (auto simp: vcpu_proj_def)
  done

lemma save_virt_timer_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj (if vr = p then r - vtimerRegs else r) l h v a p s \<and> vtimerRegs \<subseteq> r\<rbrace>
   save_virt_timer vr
   \<lbrace>\<lambda>rv s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  by (wpsimp wp: vtimer_update_vcpu_proj vcpu_save_reg_vcpu_proj modify_reg_vcpu_proj
           simp: save_virt_timer_def dmo_distr Diff_insert[symmetric]
                 writeVCPUHardwareReg_def check_export_arch_timer_def
          split: if_split_asm split_del: if_split
      | wp dmo_lift_vcpu_proj)+

lemma vcpu_disable_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj (if vcpu = Some p then r - savedWhenDisabledRegs else r) l
                         (vcpu \<noteq> Some p) v a p s \<and> savedWhenDisabledRegs \<subseteq> r \<and> h\<rbrace>
   vcpu_disable vcpu
   \<lbrace>\<lambda>rv s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  supply if_split[split del] if_split_asm[split]
  apply (case_tac vcpu; simp add: vcpu_disable_def enableFpuEL01_def setSCTLR_def dmo_distr)
  by (wpsimp wp: vcpu_save_reg_vcpu_proj modify_reg_vcpu_proj
           simp: insert_commute Diff_insert[symmetric] | wp dmo_lift_vcpu_proj)+

lemma vcpu_save_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. (if vr \<noteq> p then vopt = vcpu_proj r l h v a p s
         else if b then vopt = vcpu_proj {} {} False False False p s
         else vopt = vcpu_proj savedWhenDisabledRegs {} h False False p s) \<and>
        r = UNIV \<and> arm_current_vcpu (arch_state s) = Some (vr,b) \<and> valid_arch_state s\<rbrace>
   vcpu_save (Some (vr,b))
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  apply (wpsimp wp: save_virt_timer_vcpu_proj hoare_weak_lift_imp dmo_lift_vcpu_proj
              simp: vcpu_save_def if_fun_split split_del: if_split)
  by (auto intro: vcpureg.exhaust intro!: arg_cong[where f="\<lambda>x. _ (vcpu_proj x)"]
            simp: enum_vcpureg upto_enum_def toEnum_def fromEnum_def)

\<comment> \<open>Enable/Restore\<close>

lemma vcpu_write_CNTVOFF_vcpu_proj[wp]:
  "vcpu_write_reg vr VCPURegCNTVOFF offset
   \<lbrace>\<lambda>s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  unfolding vcpu_write_reg_def vcpu_update_def vcpu_proj_def
  by (wpsimp wp: set_vcpu_wp get_vcpu_wp)

lemma vcpu_restore_reg_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj (insert reg r) l h v a p s \<and> (vr \<noteq> p \<longrightarrow> reg \<in> r)\<rbrace>
   vcpu_restore_reg vr reg
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  unfolding vcpu_restore_reg_def writeVCPUHardwareReg_def vcpu_proj_def
  apply (wpsimp wp: get_vcpu_wp dmo_wp)
  apply (auto intro!: vcpu.equality gic_vcpu_interface.equality split: if_splits option.splits)
  done

lemma restore_virt_timer_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj (vtimerRegs \<union> r) l h v a p s \<and> (vr \<noteq> p \<longrightarrow> vtimerRegs \<subseteq> r)\<rbrace>
   restore_virt_timer vr
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  by (wpsimp wp: dmo_lift_vcpu_proj simp: restore_virt_timer_def insert_commute)

lemma vcpu_enable_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj (savedWhenDisabledRegs \<union> r) l True v a p s \<and> (vr \<noteq> p \<longrightarrow> h \<and> r = UNIV)\<rbrace>
   vcpu_enable vr
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  by (wpsimp simp: vcpu_enable_def dmo_distr wp: get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift
      | wp dmo_lift_vcpu_proj | fastforce simp: vcpu_proj_def insert_commute)+

lemma vcpu_restore_reg_range_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj (set [from .e. to] \<union> r) l h v a p s \<and> (vr \<noteq> p \<longrightarrow> r = UNIV)\<rbrace>
   vcpu_restore_reg_range vr from to
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  (is "valid (\<lambda>s. ?V [_ .e. _] s) _ _")
  unfolding vcpu_restore_reg_range_def
  by (wpsimp wp: mapM_x_inv_wp2[where I=\<top> and V="?V"])

lemma vcpu_restore_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj UNIV UNIV True True True p s \<and> valid_arch_state s \<and>
        (if vr \<noteq> p then r = UNIV \<and> l = UNIV \<and> h \<and> v \<and> a else r = {} \<and> l = {} \<and> \<not>h \<and> \<not>v \<and> \<not>a)\<rbrace>
   vcpu_restore vr
   \<lbrace>\<lambda>_ s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  apply (wpsimp wp: get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift
              simp: vcpu_restore_def dmo_distr split_del: if_split
         | wp dmo_lift_vcpu_proj)+
  apply (rule conjI)
   apply (auto intro!: arg_cong[where f="\<lambda>x. _ (vcpu_proj x)"] intro: vcpureg.exhaust
                 simp: enum_vcpureg upto_enum_def toEnum_def fromEnum_def)[1]
  apply (clarsimp simp: vcpu_proj_def split: if_splits)
  done

\<comment> \<open>Switch/Invalidate\<close>

lemma vcpu_proj_arch_state_update[simp]:
  "arm_gicvcpu_numlistregs (f (arch_state s)) = arm_gicvcpu_numlistregs (arch_state s)
   \<Longrightarrow> vcpu_proj r l h v a p (arch_state_update f s) = vcpu_proj r l h v a p s"
  by (simp add: vcpu_proj_def)

crunch vcpu_switch
  for arm_gicvcpu_numlistregs[wp]: "\<lambda>s. P (arm_gicvcpu_numlistregs (arch_state s))"

lemma vcpu_switch_integrity_hyp[wp]:
  "\<lbrace>integrity_hyp aag subjects x st and valid_arch_state\<rbrace>
   vcpu_switch vr
   \<lbrace>\<lambda>_. integrity_hyp aag subjects x st\<rbrace>"
  unfolding integrity_hyp_def vcpu_integrity_def vcpu_switch_def vcpu_proj_of_state
  supply if_split[split del] if_split[where P="\<lambda>v. _ = v", simp]
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' | wp dmo_lift_vcpu_proj)+
  apply (auto simp: insert_commute split: if_splits)
  done

lemma vcpu_switch_respects:
  "\<lbrace>integrity aag X st and valid_arch_state\<rbrace>
   vcpu_switch vopt
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding integrity_no_hyp_absorb by (wpsimp wp: hoare_vcg_all_lift)

crunch vcpu_invalidate_active
  for integrity_no_hyp[wp]: "integrity_no_hyp aag X st"
  and arm_gicvcpu_numlistregs[wp]: "\<lambda>s. P (arm_gicvcpu_numlistregs (arch_state s))"

lemma vcpu_invalidate_active_integrity_hyp[wp]:
  "\<lbrace>\<lambda>s. integrity_hyp aag subjects x st s \<and>
        (\<exists>v b. arm_current_vcpu (arch_state s) = Some (v,b) \<and> pasObjectAbs aag v \<in> subjects)\<rbrace>
   vcpu_invalidate_active
   \<lbrace>\<lambda>_. integrity_hyp aag subjects x st\<rbrace>"
  unfolding vcpu_invalidate_active_def integrity_hyp_def vcpu_integrity_def vcpu_proj_of_state
  supply if_split[split del] if_split[where P="\<lambda>v. _ = v", simp]
  apply (wpsimp wp: vcpu_disable_vcpu_proj hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply fastforce
  done

lemma vcpu_invalidate_active_respects[wp]:
  "\<lbrace>\<lambda>s. integrity aag X st s \<and> (\<exists>v b. arm_current_vcpu (arch_state s) = Some (v,b) \<and> is_subject aag v)\<rbrace>
   vcpu_invalidate_active
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding integrity_no_hyp_absorb by (wpsimp wp: hoare_vcg_all_lift)

\<comment> \<open>Flush\<close>

lemma vcpu_invalidate_active_vcpu_proj[wp]:
  "\<lbrace>\<lambda>s. vopt = vcpu_proj r l True v a p s \<and> savedWhenDisabledRegs \<subseteq> r \<and> h\<rbrace>
   vcpu_invalidate_active
   \<lbrace>\<lambda>rv s. vopt = vcpu_proj r l h v a p s\<rbrace>"
  supply if_split[split del] if_split_asm[split]
  unfolding vcpu_invalidate_active_def
  by wpsimp

lemma vcpu_flush_integrity_hyp[wp]:
  "\<lbrace>integrity_hyp aag subjects x st and valid_arch_state\<rbrace>
   vcpu_flush
   \<lbrace>\<lambda>_. integrity_hyp aag subjects x st\<rbrace>"
  unfolding integrity_hyp_def vcpu_integrity_def vcpu_flush_def vcpu_proj_of_state
  supply if_split[split del] if_split[where P="\<lambda>v. _ = v", simp]
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift'
                    hoare_pre_cont[where f=vcpu_invalidate_active and P="\<lambda>_ s. arm_current_vcpu (arch_state s) = Some x" for x]
         | strengthen None_Some_strg)+
  apply (fastforce split: if_splits)
  done

crunch vcpu_flush
  for integrity_no_hyp[wp]: "integrity_no_hyp aag X st"

lemma vcpu_flush_respects[wp]:
  "\<lbrace>integrity aag X st and valid_arch_state\<rbrace>
   vcpu_flush
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding integrity_no_hyp_absorb by (wpsimp wp: hoare_vcg_all_lift)

crunch vcpu_flush_if_current
  for respects[wp]: "integrity aag X st"
  (wp: arch_thread_get_wp simp: crunch_simps)


lemma arch_thread_set_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag ptr)\<rbrace>
    arch_thread_set f ptr
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding arch_thread_set_def
  by (wpsimp wp: set_object_integrity_autarch)

lemma dissociate_vcpu_tcb_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag vcpu \<and> is_subject aag tcb)\<rbrace>
   dissociate_vcpu_tcb vcpu tcb
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding dissociate_vcpu_tcb_def set_vcpu_def get_vcpu_def arch_thread_get_def
  by (wpsimp wp: as_user_integrity_autarch set_object_integrity_autarch
                 arch_thread_set_integrity_autarch)

crunch vcpu_invalidate_active
  for vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"
  (simp: vcpu_invalidate_active_def vcpu_disable_def)

lemma thread_set_vcpus_of[wp]:
  "thread_set f tptr \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (erule_tac P=P in rsubst)
  apply (fastforce simp: get_tcb_def opt_map_def split: option.splits kernel_object.splits)
  done

lemma dissociate_vcpu_tcb_vcpus_of:
  "\<lbrace>\<lambda>s. P ((vcpus_of s)(v := Some ((the (vcpus_of s v))\<lparr>vcpu_tcb := None\<rparr>)))\<rbrace>
   dissociate_vcpu_tcb v tcb
   \<lbrace>\<lambda>_ s. P (vcpus_of s)\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  by (wpsimp wp: as_user_wp_thread_set_helper hoare_drop_imps get_vcpu_wp simp: fun_upd_def)

crunch vcpu_update
  for integrity_autarch: "integrity aag X st"

lemma associated_tcb_is_subject:
  "\<lbrakk> pas_refined aag s; vcpus_of s v = Some vcpu; vcpu_tcb vcpu = Some t; is_subject aag v \<rbrakk>
     \<Longrightarrow> is_subject aag t"
  apply (subgoal_tac "(v, Control, t) \<in> state_objs_to_policy s")
  by (fastforce simp: sbta_href state_objs_to_policy_def state_hyp_refs_of_def opt_map_def
                dest: pas_refined_mem is_subject_trans split: option.splits)+

lemma associated_vcpu_is_subject:
  "\<lbrakk> pas_refined aag s; get_tcb t s = Some tcb; tcb_vcpu (tcb_arch tcb) = Some v; is_subject aag t \<rbrakk>
     \<Longrightarrow> is_subject aag v"
  apply (subgoal_tac "(t, Control, v) \<in> state_objs_to_policy s")
  by (fastforce simp: sbta_href state_objs_to_policy_def state_hyp_refs_of_def get_tcb_def
                dest: pas_refined_mem is_subject_trans split: option.splits kernel_object.splits)+

lemma associate_vcpu_tcb_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and valid_arch_state
                       and K (is_subject aag vcpu \<and> is_subject aag tcb)\<rbrace>
   associate_vcpu_tcb vcpu tcb
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding associate_vcpu_tcb_def
  apply (wpsimp wp: vcpu_switch_respects set_vcpu_integrity_autarch hoare_drop_imps
                    arch_thread_set_integrity_autarch dissociate_vcpu_tcb_respects get_vcpu_wp)
    apply (rule_tac Q'="\<lambda>_ s. integrity aag X st s \<and> valid_arch_state s \<and>
                              is_subject aag vcpu \<and> is_subject aag tcb \<and>
                              (\<forall>v x. vcpus_of s vcpu = Some v \<and> vcpu_tcb v = Some x \<longrightarrow> is_subject aag x)"
                 in hoare_strengthen_post)
     apply (wpsimp wp: dissociate_vcpu_tcb_respects dissociate_vcpu_tcb_vcpus_of arch_thread_get_wp)+
  apply (fastforce intro: associated_vcpu_is_subject associated_tcb_is_subject
                    simp: get_tcb_def obj_at_def opt_map_def
                   split: option.splits)
  done

lemma dmo_no_mem_integrity_autarch:
  assumes p: "\<And>P. mop \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes q: "\<And>P. mop \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  assumes r: "\<And>P. mop \<lbrace>\<lambda>ms. P (fpu_state ms)\<rbrace>"
  shows "\<lbrace>\<lambda>s. integrity aag X st s \<and>
              (\<exists>v b. arm_current_vcpu (arch_state s) = Some (v,b) \<and> is_subject aag v)\<rbrace>
         do_machine_op mop
         \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding integrity_no_hyp_absorb integrity_no_hyp_def integrity_asids_def
            integrity_fpu_def tcb_states_of_state_def get_tcb_def
  apply (rule hoare_weaken_pre)
   apply (rule hoare_wp_combs)
    apply (wps assms)
    apply (wp dmo_machine_state_lift assms)
   apply (wpsimp simp: do_machine_op_def)
  apply clarsimp
  apply (erule allE, erule trhyp_trans)
  apply (auto simp: integrity_hyp_def vcpu_integrity_def vcpu_of_state_def split: option.splits)
  done

lemma invoke_vcpu_inject_irq_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag vcpu)\<rbrace>
   invoke_vcpu_inject_irq vcpu index vir
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding invoke_vcpu_inject_irq_def set_gic_vcpu_ctrl_lr_def vgic_update_lr_def vgic_update_def
  by (wpsimp wp: vcpu_update_integrity_autarch dmo_no_mem_integrity_autarch)

lemma invoke_vcpu_read_register_respects:
  "invoke_vcpu_read_register vcpu reg \<lbrace>integrity aag X st\<rbrace>"
  unfolding invoke_vcpu_read_register_def read_vcpu_register_def readVCPUHardwareReg_def
  by wpsimp

lemma invoke_vcpu_write_register_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag vcpu)\<rbrace>
   invoke_vcpu_write_register vcpu reg val
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding invoke_vcpu_write_register_def write_vcpu_register_def
            vcpu_write_reg_def writeVCPUHardwareReg_def
  apply (wpsimp wp: vcpu_update_integrity_autarch dmo_no_mem_integrity_autarch)
  apply (clarsimp split: option.splits)
  done

lemma invoke_vcpu_ack_vppi_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag vcpu)\<rbrace>
   invoke_vcpu_ack_vppi vcpu vppi
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding invoke_vcpu_ack_vppi_def
  by (wpsimp wp: vcpu_update_integrity_autarch)


definition authorised_vcpu_inv where
  "authorised_vcpu_inv aag iv \<equiv>
   case iv of VCPUSetTCB vcpu tcb \<Rightarrow> is_subject aag vcpu \<and> is_subject aag tcb
            | VCPUInjectIRQ vcpu index vir \<Rightarrow> is_subject aag vcpu
            | VCPUReadRegister vcpu reg \<Rightarrow> is_subject aag vcpu
            | VCPUWriteRegister vcpu reg val \<Rightarrow> is_subject aag vcpu
            | VCPUAckVPPI vcpu vppi \<Rightarrow> is_subject aag vcpu"

lemma perform_vcpu_invocation_respects:
  "\<lbrace>integrity aag X st and K (authorised_vcpu_inv aag iv) and pas_refined aag
                       and invs and valid_vcpu_invocation iv and is_subject aag \<circ> cur_thread\<rbrace>
   perform_vcpu_invocation iv
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding perform_vcpu_invocation_def
  apply (wpsimp wp: associate_vcpu_tcb_respects invoke_vcpu_ack_vppi_respects invoke_vcpu_inject_irq_respects
                    invoke_vcpu_read_register_respects invoke_vcpu_write_register_respects)
  apply (auto simp: authorised_vcpu_inv_def)
  done

lemma set_vcpu_thread_bound_ntfns[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp)
  apply (erule_tac P=P in rsubst)
  apply (rule ext)
  apply (clarsimp simp: thread_bound_ntfns_def get_tcb_def obj_at_def)
  done

lemma arch_thread_set_thread_bound_ntfns[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  apply (erule_tac P=P in rsubst)
  apply (rule ext)
  apply (clarsimp simp: thread_bound_ntfns_def get_tcb_def obj_at_def)
  done

lemma set_vcpu_thread_st_auth[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp)
  apply (erule_tac P=P in rsubst)
  apply (rule ext)
  apply (clarsimp simp: thread_st_auth_def tcb_states_of_state_def get_tcb_def obj_at_def)
  done

lemma arch_thread_thread_st_auth[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  apply (erule_tac P=P in rsubst)
  apply (rule ext)
  apply (clarsimp simp: thread_st_auth_def tcb_states_of_state_def get_tcb_def obj_at_def)
  done

crunch perform_vcpu_invocation, vcpu_flush
  for irq_map_wellformed[wp]: "irq_map_wellformed aag"
  and state_irqs_to_policy[wp]: "\<lambda>s. P (state_irqs_to_policy aag s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and domains_of_state[wp]: "\<lambda>s. P (domains_of_state s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and tcb_bound_notification[wp]: "\<lambda>s. P (thread_bound_ntfns s)"
  and thread_st_auth[wp]: "\<lambda>s. P (thread_st_auth s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_vcpu_valid_asid_table[wp]:
  "set_vcpu p v \<lbrace>valid_asid_table\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp)
  apply (clarsimp simp: obj_at_def opt_map_def)
  done

lemma arch_thread_set_valid_asid_table[wp]:
  "arch_thread_set f t \<lbrace>valid_asid_table\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  apply (clarsimp simp: get_tcb_def obj_at_def opt_map_def
                 split: option.splits kernel_object.splits)
  done

lemma as_user_asid_pools_of[wp]:
  "as_user t f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  apply (erule_tac P=P in rsubst)
  apply (fastforce simp: get_tcb_def opt_map_def split: option.splits)
  done

lemma as_user_valid_asid_table[wp]:
  "as_user t f \<lbrace>valid_asid_table\<rbrace>"
  apply (rule hoare_lift_Pf[where f=asid_table])
   apply (rule hoare_lift_Pf[where f=asid_pools_of])
    apply wpsimp+
  done

lemma set_vcpu_vspace_objs_of[wp]:
  "set_vcpu p vcpu \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp)
  apply (clarsimp simp: opt_map_def typ_at_eq_kheap_obj)
  done

lemma thread_set_vspace_objs_of[wp]:
  "thread_set f tptr \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  unfolding thread_set_def
  apply (wpsimp wp: set_object_wp)
  apply (erule_tac P=P in rsubst)
  apply (fastforce simp: get_tcb_def opt_map_def split: option.splits kernel_object.splits)
  done

lemma arch_thread_set_vspace_objs_of[wp]:
  "arch_thread_set f tptr \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  apply (fastforce simp: get_tcb_def opt_map_def split: option.splits kernel_object.splits)
  done

lemma state_vrefs_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  unfolding state_vrefs_def
  apply (rule hoare_weaken_pre)
   apply (wps assms)
   apply (wpsimp wp: assms vs_lookup_vspace_objs_lift)+
  done

crunch perform_vcpu_invocation
  for vspace_objs_of[wp]: "\<lambda>s. P (vspace_objs_of s)"
  (wp: crunch_wps as_user_wp_thread_set_helper)

crunch set_vcpu, arch_thread_set, vgic_update, vcpu_switch,
       vcpu_flush, perform_vcpu_invocation
  for state_vrefs[wp]: "\<lambda>s. P (state_vrefs s)"
  (wp: state_vrefs_lift)

lemma set_vcpu_None_pas_refined[wp]:
  "set_vcpu vr (v\<lparr>vcpu_tcb := None\<rparr>) \<lbrace>pas_refined aag\<rbrace>"
  unfolding pas_refined_def state_objs_to_policy_def
  apply (rule hoare_weaken_pre)
   apply wps
   apply (wp set_vcpu_wp)
  apply (fastforce simp: auth_graph_map_def state_bits_to_policy_refs_subseteq state_hyp_refs_of_def)
  done

lemma arch_thread_set_vcpu_None_pas_refined[wp]:
  "arch_thread_set (tcb_vcpu_update (\<lambda>_. None)) tptr \<lbrace>pas_refined aag\<rbrace>"
  unfolding pas_refined_def state_objs_to_policy_def
  apply (rule hoare_weaken_pre)
   apply wps
   apply (wp arch_thread_set_wp)
  apply (fastforce simp: auth_graph_map_def state_bits_to_policy_refs_subseteq state_hyp_refs_of_def)
  done

lemma vcpu_invalidate_active_state_hyp_refs_of[wp]:
  "vcpu_invalidate_active \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: vcpu_invalidate_active_def vcpu_disable_def)

crunch vcpu_invalidate_active
  for pas_refined[wp]: "pas_refined aag"
  (wp: crunch_wps simp: pas_refined_def state_objs_to_policy_def ignore: vcpu_invalidate_active)

lemma dissociate_vcpu_tcb_pas_refined[wp]:
  "dissociate_vcpu_tcb vr t \<lbrace>pas_refined aag\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  by (wpsimp wp: as_user_pas_refined get_vcpu_wp arch_thread_get_wp)

lemma vcpu_update_state_hyp_refs:
  "(\<And>vcpu. vcpu_tcb (f vcpu) = vcpu_tcb vcpu)
   \<Longrightarrow> vcpu_update vr f \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding vcpu_update_def
  apply (wp set_vcpu_wp get_vcpu_wp)
  by (fastforce simp: state_hyp_refs_of_def opt_map_def obj_at_def
                elim: rsubst[where P=P] split: if_splits)

crunch vcpu_switch, vcpu_flush
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (wp: crunch_wps vcpu_update_state_hyp_refs)

crunch vcpu_switch, vcpu_flush
  for pas_refined[wp]: "pas_refined aag"
  (simp: pas_refined_def state_objs_to_policy_def ignore: vcpu_switch vcpu_flush)

lemma associate_vcpu_tcb_pas_refined:
  "\<lbrace>pas_refined aag and K (is_subject aag vr \<and> is_subject aag t)\<rbrace>
   associate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding associate_vcpu_tcb_def K_bind_def
  apply (rule bind_wp_fwd_skip, solves wpsimp)+
  apply wpsimp
    apply (unfold pas_refined_def state_objs_to_policy_def state_asids_to_policy_arch_def)
    apply (wps | wp set_vcpu_wp arch_thread_set_wp)+
  apply clarsimp
  apply (case_tac "a = pasSubject aag \<and> b = pasSubject aag")
   apply (simp add: aag_wellformed_refl)
  apply (erule subsetD)
  apply (clarsimp simp: auth_graph_map_def)
  apply (rule exI, rule conjI, rule refl)+
  apply (erule state_bits_to_policy.cases)
         apply (fastforce elim: state_bits_to_policy.intros)+
  apply (fastforce simp: sbta_href state_hyp_refs_of_def obj_at_def get_tcb_def
                  split: if_splits option.splits kernel_object.splits)
  done


definition authorised_arch_inv :: "'a PAS \<Rightarrow> arch_invocation \<Rightarrow> det_state \<Rightarrow> bool" where
 "authorised_arch_inv aag ai s \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> authorised_page_table_inv aag pti
   | InvokePage pgi \<Rightarrow> authorised_page_inv aag pgi s
   | InvokeASIDControl aci \<Rightarrow> authorised_asid_control_inv aag aci
   | InvokeASIDPool api \<Rightarrow> authorised_asid_pool_inv aag api
   | InvokeVCPU vi \<Rightarrow> authorised_vcpu_inv aag vi
   | InvokeVSpace vi \<Rightarrow> True
   | InvokeSGISignal _ \<Rightarrow> True
   | InvokeSMCCall _ \<Rightarrow> True"

lemma sendSGI_respects[wp]:
  "do_machine_op (sendSGI irq target) \<lbrace>integrity aag X st\<rbrace>"
  unfolding sendSGI_def
  by (wpsimp wp: dmo_mol_respects)

lemma doSMC_mip_respects[wp]:
  "do_machine_op (doSMC_mop args) \<lbrace>integrity aag X st\<rbrace>"
  unfolding doSMC_mop_def
  by (wpsimp wp: dmo_mol_respects simp: do_machine_op_bind)

crunch perform_sgi_invocation, perform_smc_invocation
  for pas_refined [wp]: "pas_refined aag"
  and respects [wp]: "integrity aag X st"
  (ignore: do_machine_op)

crunch vcpu_write_reg
  for state_vrefs[wp]: "\<lambda>s. P (state_vrefs s)"
  and pas_refined[wp]: "pas_refined aag"
  (wp: vcpu_update_state_hyp_refs state_vrefs_lift
   simp: pas_refined_def state_objs_to_policy_def ignore: vcpu_write_reg)

crunch vgic_update
  for pas_refined[wp]: "pas_refined aag"
  (simp: pas_refined_def state_objs_to_policy_def ignore: vgic_update)

crunch invoke_vcpu_inject_irq, invoke_vcpu_read_register, invoke_vcpu_write_register
  for pas_refined[wp]: "pas_refined aag"

crunch invoke_vcpu_ack_vppi
  for state_vrefs[wp]: "\<lambda>s. P (state_vrefs s)"
  and state_hyp_refs[wp]: "\<lambda>s. P (state_hyp_refs_of s)"

crunch invoke_vcpu_ack_vppi
  for pas_refined[wp]: "pas_refined aag"
  (wp: vcpu_update_state_hyp_refs state_vrefs_lift
   simp: pas_refined_def state_objs_to_policy_def ignore: invoke_vcpu_ack_vppi)

lemma perform_vcpu_invocation_pas_refined[wp]:
  "\<lbrace>pas_refined aag and K (authorised_vcpu_inv aag iv)\<rbrace>
   perform_vcpu_invocation iv
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_vcpu_invocation_def authorised_vcpu_inv_def
  by (wpsimp wp: associate_vcpu_tcb_pas_refined)

lemma invoke_arch_respects[Arch_AC_assms]:
  "\<lbrace>integrity aag X st and authorised_arch_inv aag ai and pas_refined aag and invs
                       and valid_arch_inv ai and is_subject aag \<circ> cur_thread\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: arch_perform_invocation_def)
  apply (wpsimp wp: perform_page_table_invocation_respects perform_page_invocation_respects
                    perform_asid_control_invocation_respects perform_asid_pool_invocation_respects
                    perform_vspace_invocation_respects perform_vcpu_invocation_respects)
  apply (auto simp: authorised_arch_inv_def valid_arch_inv_def)
  done

lemma invoke_arch_pas_refined[Arch_AC_assms]:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and ct_active
                    and valid_arch_inv ai and authorised_arch_inv aag ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: arch_perform_invocation_def valid_arch_inv_def)
  apply (wpsimp wp: perform_page_table_invocation_pas_refined perform_asid_pool_invocation_pas_refined
                    perform_page_invocation_pas_refined perform_asid_control_invocation_pas_refined)
  apply (auto simp: authorised_arch_inv_def)
  done

lemma vspace_for_asid_is_subject:
  "\<lbrakk> vspace_for_asid a s = Some xaa; pas_refined aag s; valid_asid_table s; is_subject_asid aag a \<rbrakk>
     \<Longrightarrow> is_subject aag xaa"
  apply (frule vspace_for_asid_vs_lookup)
  apply (clarsimp simp: vspace_for_asid_def entry_for_asid_def)
  apply (frule pool_for_asid_vs_lookupD)
  apply (clarsimp simp: vspace_for_pool_def entry_for_pool_def pool_for_asid_def asid_pools_of_ko_at )
  apply (frule_tac pdptr = "(ap_vspace v'a)" and vrefs="state_vrefs s" and a=Control in sata_asid_lookup)
   apply (fastforce simp: vs_refs_aux_def graph_of_def asid_low_bits_of_mask_eq[symmetric]
                          ucast_ucast_b is_up_def opt_map_def source_size_def target_size_def
                          word_size pas_refined_def obj_at_def
                    dest: aag_wellformed_Control
                  intro!: state_vrefsD)+
  done

lemma decode_page_table_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_PageTableCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                          aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                          is_subject aag (fst slot) \<and>
                                          (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_page_table_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (clarsimp simp: is_PageTableCap_def)
  apply (rename_tac x xa)
  apply (unfold decode_page_table_invocation_def decode_pt_inv_map_def authorised_arch_inv_def)
  apply (wpsimp simp: Let_def is_final_cap_def if_fun_split)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rename_tac x t m s)
  apply (prop_tac "\<forall>y \<in> set [x, x + 2 ^ pte_bits .e. x + 2 ^ pt_bits t - 1]. table_base t y = x")
   apply (drule (1) caps_of_state_aligned_page_table)
   apply (clarsimp simp only: is_aligned_neg_mask_eq' add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule_tac n="pt_bits t" in neg_mask_mono_le)
   apply (drule_tac n="pt_bits t" in neg_mask_mono_le)
   apply (fastforce dest: plus_mask_AND_NOT_mask_eq)
  apply (intro conjI; clarsimp)
   apply (clarsimp simp: authorised_page_table_inv_def)
   apply (case_tac excaps; clarsimp)
   apply (rule conjI)
    apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
    apply (subst table_base_pt_slot_offset)
     apply (fastforce simp: cte_wp_at_caps_of_state
                      dest: caps_of_state_aligned_page_table pt_walk_is_aligned)
    apply (frule vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup, simplified])
    apply (erule pt_walk_is_subject[rotated 4]; fastforce intro: vspace_for_asid_is_subject
                                                           simp: user_vtop_leq_canonical_user
                                                                 user_region_def)
   apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                         cap_links_asid_slot_def label_owns_asid_slot_def cap_links_irq_def)
  apply (auto simp: caps_of_state_pasObjectAbs_eq authorised_page_table_inv_def
                    cap_auth_conferred_def arch_cap_auth_conferred_def)
  done

lemma decode_fr_inv_flush_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_FrameCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                     aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                     is_subject aag (fst slot) \<and>
                                     (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_fr_inv_flush label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
  unfolding authorised_arch_inv_def authorised_page_inv_def decode_fr_inv_flush_def Let_def
  by wpsimp

lemma decode_asid_control_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (cap = ASIDControlCap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                           aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                           is_subject aag (fst slot) \<and>
                                           (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_asid_control_invocation label msg slot cap excaps
   \<lbrace>authorised_arch_inv aag\<rbrace>, -"
  unfolding decode_asid_control_invocation_def authorised_arch_inv_def authorised_asid_control_inv_def
  apply wpsimp
  apply (cases excaps; cases "tl excaps"; clarsimp simp: aag_cap_auth_def cte_wp_at_caps_of_state)
  apply (fastforce dest: caps_of_state_valid[where cap="UntypedCap _ _ _ _"] pas_refined_Control
                   simp: valid_cap_def cap_aligned_def is_cap_simps cap_auth_conferred_def)
  done

lemma decode_asid_pool_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_ASIDPoolCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                         aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                         is_subject aag (fst slot) \<and>
                                         (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_asid_pool_invocation label msg slot cap excaps
   \<lbrace>authorised_arch_inv aag\<rbrace>, -"
  unfolding decode_asid_pool_invocation_def authorised_arch_inv_def Let_def
  apply wpsimp
  apply (erule swap[where P="authorised_asid_pool_inv _ _"])
  apply (cases excaps; clarsimp)
  apply (clarsimp simp: authorised_asid_pool_inv_def is_ASIDPoolCap_def
                        pas_refined_def state_objs_to_policy_def auth_graph_map_def)
  apply (rule conjI)
   apply (drule subsetD)
    apply (fastforce dest!: sbta_caps
                      simp: obj_refs_def cte_wp_at_caps_of_state
                            cap_auth_conferred_def arch_cap_auth_conferred_def)
   apply (fastforce dest: aag_wellformed_Control)
  apply (erule allE, erule mp)
  apply (fastforce dest: caps_of_state_valid asid_high_bits_of_add_ucast
                   simp: cte_wp_at_caps_of_state valid_cap_def)
  done

lemma decode_fr_inv_map_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_FrameCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                     aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                     is_subject aag (fst slot) \<and>
                                     (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_fr_inv_map label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
  unfolding decode_fr_inv_map_def Let_def fun_app_def
  apply (wpsimp wp: check_vp_wpR whenE_throwError_wp)+
  apply (subst imp_conjL[symmetric])
  apply (subst imp_disjL[symmetric])
  apply (rule impI)
  apply clarsimp
  apply (prop_tac "msg ! 0 \<in> user_region")
   apply (prop_tac "\<not> user_vtop < msg ! 0 + mask (pageBitsForSize xb) \<longrightarrow> msg!0 \<in> user_region")
    apply (fastforce intro: dual_order.trans user_vtop_leq_canonical_user is_aligned_no_overflow_mask
                      simp: user_region_def vmsz_aligned_def not_less)
   apply (fastforce dest: cte_wp_valid_cap simp: valid_cap_def wellformed_mapdata_def)
  apply (cases excaps, clarsimp)
  apply (drule_tac x="excaps ! 0" in bspec, clarsimp)+
  apply (clarsimp simp: authorised_arch_inv_def authorised_page_inv_def authorised_slots_def
                        aag_cap_auth_def cap_links_asid_slot_def cap_links_irq_def pte_ref2_def
                        make_user_pte_def cap_auth_conferred_def arch_cap_auth_conferred_def)
  apply (rule conjI)
   apply (frule (1) pt_lookup_slot_vs_lookup_slotI, clarsimp)
   apply (drule (1) vs_lookup_slot_unique_level; clarsimp)
   apply (fastforce simp: cte_wp_at_caps_of_state make_user_pte_def pte_ref2_def
                          vspace_cap_rights_to_auth_def validate_vm_rights_def
                          mask_vm_rights_def vm_read_only_def vm_kernel_only_def
                   split: if_splits)
  apply (fastforce elim: pt_lookup_slot_from_level_is_subject[rotated 4]
                  intro: vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup]
                         pas_refined_Control[symmetric]
                   simp: pt_lookup_slot_def)
  done

lemma decode_frame_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_FrameCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                     aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                     is_subject aag (fst slot) \<and>
                                     (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_frame_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>,-"
  unfolding decode_frame_invocation_def
  by (wpsimp wp: decode_fr_inv_flush_authorised decode_fr_inv_map_authorised
           simp: authorised_arch_inv_def authorised_page_inv_def)

lemma decode_vspace_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_PageTableCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                          aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                          is_subject aag (fst slot) \<and>
                                          (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_vspace_invocation label msg slot cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>, -"
  unfolding decode_vspace_invocation_def decode_vs_inv_flush_def authorised_arch_inv_def Let_def
  by wpsimp

lemma decode_vcpu_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (is_VCPUCap cap \<and> (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                                          aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                                          is_subject aag (fst slot) \<and>
                                          (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))\<rbrace>
   decode_vcpu_invocation label msg cap excaps
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>, -"
  unfolding decode_vcpu_invocation_def decode_vcpu_set_tcb_def
            decode_vcpu_inject_irq_def decode_vcpu_read_register_def
            decode_vcpu_write_register_def decode_vcpu_ack_vppi_def authorised_arch_inv_def
  apply (rule hoare_gen_asmE)
  apply (rule_tac Q'="\<lambda>rv s. \<exists>x. rv = InvokeVCPU x \<and> authorised_vcpu_inv aag x"
               in hoare_strengthen_postE_R[rotated], clarsimp)
  apply wpsimp
  apply (fastforce elim: caps_of_state_pasObjectAbs_eq
                   simp: authorised_vcpu_inv_def cte_wp_at_caps_of_state
                         cap_auth_conferred_def arch_cap_auth_conferred_def)
  done

lemma decode_sgi_signal_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and K (is_SGISignalCap cap)\<rbrace>
   decode_sgi_signal_invocation cap
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>, -"
  unfolding decode_sgi_signal_invocation_def authorised_arch_inv_def
  by wpsimp

lemma decode_smc_invocation_authorised[wp]:
  "\<lbrace>invs and pas_refined aag and K (is_SMCCap acap)\<rbrace>
   decode_smc_invocation label args acap
   \<lbrace>\<lambda>rv. authorised_arch_inv aag rv\<rbrace>, -"
  unfolding decode_smc_invocation_def authorised_arch_inv_def
  by wpsimp

lemma decode_arch_invocation_authorised[Arch_AC_assms]:
  "\<lbrace>invs and pas_refined aag and cte_wp_at ((=) (ArchObjectCap cap)) slot
         and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
         and K (\<forall>(cap, slot) \<in> {(ArchObjectCap cap, slot)} \<union> set excaps.
                  aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and>
                  is_subject aag (fst slot) \<and>
                  (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v))\<rbrace>
   arch_decode_invocation label msg x_slot slot cap excaps
   \<lbrace>authorised_arch_inv aag\<rbrace>, -"
  unfolding arch_decode_invocation_def
  apply (wpsimp wp: decode_page_table_invocation_authorised decode_asid_pool_invocation_authorised
                    decode_asid_control_invocation_authorised decode_frame_invocation_authorised
                    decode_vcpu_invocation_authorised decode_vspace_invocation_authorised
                    decode_sgi_signal_invocation_authorised)
  apply auto
  done

lemma authorised_arch_inv_sa_update[Arch_AC_assms]:
  "authorised_arch_inv aag i (scheduler_action_update (\<lambda>_. act) s) =
   authorised_arch_inv aag i s"
  by (clarsimp simp: authorised_arch_inv_def authorised_page_inv_def authorised_slots_def
              split: arch_invocation.splits page_invocation.splits)

crunch set_thread_state_act
  for authorised_arch_inv[wp]: "authorised_arch_inv aag i"
  (simp: authorised_arch_inv_sa_update)

lemma set_thread_state_authorised_arch_inv[Arch_AC_assms,wp]:
  "set_thread_state ref ts \<lbrace>authorised_arch_inv aag i\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: authorised_arch_inv_def)
  apply (case_tac i; clarsimp)
  apply (clarsimp simp: authorised_page_inv_def authorised_slots_def split: page_invocation.splits)
  apply (erule_tac x=level in allE)
  apply (erule_tac x=asid in allE)
  apply (erule_tac x=vref in allE)
  apply (drule mp)
   apply (fastforce elim: subst[OF vs_lookup_table_eq_lift, rotated -1]
                    simp: vs_lookup_slot_table get_tcb_def opt_map_def
                   split: option.splits kernel_object.splits if_splits)+
  done

end

arch_requalify_consts authorised_arch_inv

global_interpretation Arch_AC_2?: Arch_AC_2 aag authorised_arch_inv for aag
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Arch_AC_assms)?)
qed

end
