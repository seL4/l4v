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

context Arch begin global_naming RISCV64

named_theorems Arch_AC_assms

lemma set_mrs_state_vrefs[Arch_AC_assms, wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
   set_mrs thread buf msgs
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_mrs_def split_def set_object_def get_object_def split del: if_split)
  apply (wpsimp wp: gets_the_wp get_wp put_wp mapM_x_wp'
              simp: zipWithM_x_mapM_x split_def store_word_offs_def
         split_del: if_split)
  apply (subst state_vrefs_eqI)
        prefer 7
        apply assumption
       apply (clarsimp simp: opt_map_def)
      apply (fastforce simp: opt_map_def aobj_of_def)
     apply clarsimp
    apply (auto simp: valid_arch_state_def)
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

end


global_interpretation Arch_AC_1?: Arch_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Arch_AC_assms)
qed


context Arch begin global_naming RISCV64

definition level_of_table :: "obj_ref \<Rightarrow> 'z :: state_ext state \<Rightarrow> vm_level"
  where
  "level_of_table p s \<equiv>
     GREATEST lvl. \<exists>asid vref. vref \<in> user_region \<and> vs_lookup_table lvl asid vref s = Some (lvl, p)"

lemma level_of_table_vs_lookup_table:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     ptes_of s p = Some pte; level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk>
     \<Longrightarrow> level_of_table p s = level"
  apply (subst level_of_table_def)
  apply (rule Greatest_equality, fastforce)
  apply (case_tac "y = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid)
  apply (fastforce dest: vs_lookup_table_unique_level)
  done

lemma vs_lookup_slot_level_of_slot:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, p);
     ptes_of s p = Some pte; level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk>
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
     vref \<in> user_region; \<not> is_PageTablePTE pte;
     kheap s (table_base p) = Some (ArchObj (PageTable pt)) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p
                                                                        then pte
                                                                        else pt a)))
                                     else kheap s a\<rparr>) =
         (\<lambda>x. if \<exists>level' vref'. vref_for_level vref' (level + 1) = vref_for_level vref (level + 1) \<and>
                                vref' \<in> user_region \<and> p = pt_slot_offset level (table_base p) vref' \<and>
                                pt_walk level level' (table_base p) vref' (ptes_of s) = Some (level',x)
              then (if x = table_base p
                    then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                    else {})
              else state_vrefs s x)"
  apply (rule all_ext)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce simp: vs_lookup_slot_def vs_lookup_table_def
                          ptes_of_Some pts_of_Some aobjs_of_Some
                    dest: pool_for_asid_no_pte)
  apply (prop_tac "ptes_of s p \<noteq> None")
   apply (drule valid_vspace_objs_strong_slotD; clarsimp split del: if_split)
  apply (frule vs_lookup_slot_table_base; clarsimp split del: if_split)
  apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp split del: if_split)
  apply safe
   apply (subst (asm) state_vrefs_def opt_map_def)+
   apply (clarsimp split: option.splits split del: if_split)
   apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and s'="kheap_update _ s" and p=p])
          apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                 opt_map_def pte_of_def obind_def
                           dest: pte_ptr_eq)+
   apply (case_tac "x = table_base p"; clarsimp)
    apply (case_tac "lvl = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid[OF vs_lookup_level]
                      simp: ptes_of_Some pts_of_Some aobjs_of_Some split: if_splits)
    apply (fastforce dest: vs_lookup_table_unique_level[OF vs_lookup_level]
                     elim: allE[where x=level] split: if_splits)
   apply (clarsimp split: if_splits)
    apply (case_tac "level' = asid_pool_level")
     apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
    apply (frule vs_lookup_slot_level_of_slot)
        apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some split: option.splits)
       apply fastforce+
    apply (subst (asm) vs_lookup_slot_table_unfold; fastforce)
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
     apply (frule bit0.plus_one_leq)
     apply (erule_tac x=level in allE)
     apply (subst (asm) vs_lookup_slot_vref_for_level[symmetric], assumption)
     apply (frule_tac bot_level=bot in vs_lookup_min_level)
     apply (fastforce simp: vs_lookup_slot_vref_for_level vs_lookup_slot_table_unfold)
    apply (subst (asm) pt_walk.simps, clarsimp)
   apply (fastforce simp: state_vrefs_def opt_map_def)
  apply (prop_tac "level_of_slot asid vref p s = level")
   apply (fastforce simp: vs_lookup_slot_table_unfold vs_lookup_slot_level_of_slot)
  apply (clarsimp split: if_splits)
   apply (rule state_vrefsD)
      apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
             apply (fastforce dest: pte_ptr_eq
                              simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                    opt_map_def pte_of_def obind_def)+
  apply (case_tac "x = table_base p")
   apply (fastforce elim: allE[where x=level])
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule_tac level=lvl and asid=asida and vref=vrefa in state_vrefsD)
     apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
            apply (fastforce dest: pte_ptr_eq
                             simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                   opt_map_def pte_of_def obind_def)+
     apply (clarsimp split: if_splits)
     apply (intro conjI; clarsimp)
      apply (case_tac "level' = asid_pool_level")
       apply (fastforce dest: vs_lookup_slot_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
      apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
      apply (case_tac "lvl < level")
       apply (drule_tac bot_level=bot in vs_lookup_level)
       apply (subst (asm) vs_lookup_split_Some, erule dual_order.strict_implies_order)
        apply fastforce
       apply (drule (1) vs_lookup_table_unique_level; fastforce)
      apply (metis vs_lookup_slot_table vs_lookup_slot_unique_level)
     apply (fastforce dest: vs_lookup_level)
    apply (fastforce simp: aobjs_of_Some opt_map_def)
   apply clarsimp
  apply clarsimp
  done

lemma state_vrefs_store_NonPageTablePTE':
  "\<lbrakk> invs s; is_aligned p pte_bits; \<not> is_PageTablePTE pte;
     kheap s (table_base p) = Some (ArchObj (PageTable pt));
     \<forall>level asid vref. vref \<in> user_region \<longrightarrow> vs_lookup_slot level asid vref s \<noteq> Some (level, p) \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>kheap := \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p
                                                                        then pte
                                                                        else pt a)))
                                     else kheap s a\<rparr>) =
         (\<lambda>x. if x = table_base p \<and> (\<exists>level. \<exists>\<rhd> (level, table_base p) s)
              then vs_refs_aux (level_of_table (table_base p) s) (PageTable (\<lambda>a. if a = table_index p
                                                                                 then pte
                                                                                 else pt a))
              else state_vrefs s x)"
  apply (rule all_ext)
  apply safe
   apply (subst (asm) state_vrefs_def opt_map_def)+
   apply (clarsimp split: option.splits split del: if_split)
   apply (clarsimp split: if_split_asm option.splits split del: if_split)
    apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
           apply (fastforce dest: pte_ptr_eq
                            simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                  opt_map_def pte_of_def obind_def)+
    apply (clarsimp split: if_splits)
    apply (drule vs_lookup_level)
    apply (rule conjI; clarsimp)
    apply (case_tac "level = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
    apply (case_tac "lvl = asid_pool_level")
     apply (fastforce dest: vs_lookup_table_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
    apply (subst level_of_table_vs_lookup_table; fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)
   apply (subst (asm) vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte])
          apply (fastforce dest: pte_ptr_eq
                           simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                 opt_map_def pte_of_def obind_def)+
   apply (fastforce simp: state_vrefs_def aobjs_of_Some)
  apply (clarsimp split: if_splits)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_table_no_asid simp: ptes_of_Some pts_of_Some aobjs_of_Some)
   apply (subst (asm) level_of_table_vs_lookup_table)
        apply (fastforce simp: ptes_of_Some pts_of_Some aobjs_of_Some)+
   apply (rule state_vrefsD)
      apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
             apply ((fastforce dest: pte_ptr_eq
                               simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                     opt_map_def pte_of_def obind_def)+)[7]
      apply auto[1]
     apply (fastforce simp: aobjs_of_Some opt_map_def)
    apply clarsimp
   apply clarsimp
  apply (case_tac "x = table_base p")
   apply (fastforce dest: vs_lookup_level simp: state_vrefs_def)
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule state_vrefsD)
     apply (subst vs_lookup_non_PageTablePTE[where s=s and p=p and pte=pte ])
            apply ((fastforce dest: pte_ptr_eq
                              simp: ptes_of_Some pts_of_Some aobjs_of_Some
                                    opt_map_def pte_of_def obind_def)+)[7]
     apply auto[1]
    apply (fastforce simp: aobjs_of_Some opt_map_def split: option.splits)
   apply clarsimp
  apply clarsimp
  done

(* FIXME AC: make this less ugly *)
lemma state_vrefs_store_NonPageTablePTE_wp:
  "\<lbrace>\<lambda>s. invs s \<and> \<not> is_PageTablePTE pte \<and>
        (\<forall>pt. ako_at (PageTable pt) (table_base p) s \<and> is_aligned p pte_bits \<longrightarrow>
              (if \<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region
               then (\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region \<and>
                                       P (\<lambda>x. (if \<exists>level' vref'. vref_for_level vref' (level + 1) = vref_for_level vref (level + 1) \<and>
                                                                 vref' \<in> user_region \<and> p = pt_slot_offset level (table_base p) vref' \<and>
                                                                 pt_walk level level' (table_base p) vref' (ptes_of s) = Some (level', x)
                                               then (if x = table_base p
                                                     then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                                                     else {})
                                               else state_vrefs s x)))
               else P (\<lambda>x. (if x = table_base p \<and> (\<exists>level. \<exists>\<rhd> (level, table_base p) s)
                            then vs_refs_aux (level_of_table (table_base p) s) (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
                            else state_vrefs s x))))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (case_tac "\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and>
                                     vref \<in> user_region")
   apply (erule_tac x=pt in allE)
   apply (clarsimp simp: fun_upd_def)
   apply (subst state_vrefs_store_NonPageTablePTE)
         apply fastforce+
    apply (clarsimp simp: obj_at_def)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
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
  apply (clarsimp simp: fun_upd_def)
  apply (subst state_vrefs_store_NonPageTablePTE'; fastforce simp: obj_at_def)
  done

lemma store_pte_thread_st_auth[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: get_tcb_def thread_st_auth_def tcb_states_of_state_def obj_at_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma store_pte_thread_bound_ntfns[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: get_tcb_def thread_bound_ntfns_def  obj_at_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma store_pte_domains_of_state[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (domains_of_state s)\<rbrace>"
  unfolding store_pte_def set_pt_def by (wpsimp wp: set_object_wp)

lemma mapM_x_store_pte_caps_of_state[wp]:
  "mapM_x (swp store_pte InvalidPTE) slots \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

lemma state_bits_to_policy_vrefs_subseteq:
  "\<And>cdt. \<lbrakk> x \<in> state_bits_to_policy caps ts tbn cdt vrefs; caps = caps';
           ts = ts'; tbn = tbn'; cdt = cdt'; \<forall>x. vrefs x \<subseteq> state_vrefs s x \<rbrakk>
           \<Longrightarrow> x \<in> state_bits_to_policy caps'  ts' tbn' cdt' (state_vrefs s)"
  apply (cases x; clarsimp)
  apply (erule state_bits_to_policy.cases; fastforce intro: state_bits_to_policy.intros)
  done

lemma state_asids_to_policy_vrefs_subseteq:
  "\<lbrakk> x \<in> state_asids_to_policy_aux aag caps asid_tab vrefs; caps = caps';
     \<forall>x. vrefs x \<subseteq> state_vrefs s x; \<forall>x y. asid_tab x = Some y \<longrightarrow> asid_table s x = Some y \<rbrakk>
     \<Longrightarrow> x \<in> state_asids_to_policy_aux aag caps' (asid_table s) (state_vrefs s)"
  apply (cases x; clarsimp)
  apply (erule state_asids_to_policy_aux.cases; fastforce intro: state_asids_to_policy_aux.intros)
  done

lemma store_InvalidPTE_state_objs_in_policy:
  "\<lbrace>\<lambda>s. state_objs_in_policy aag s \<and> invs s \<and> table_base p \<notin> global_refs s \<and>
        ((\<exists>a. vspace_for_asid a s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots)\<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_ s. state_objs_in_policy aag s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp: state_objs_to_policy_def pred_conj_def)
   apply wps
   apply (rule state_vrefs_store_NonPageTablePTE_wp)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (intro exI conjI)
     apply assumption
    apply clarsimp
   apply (clarsimp simp: state_objs_to_policy_def)
   apply (erule subsetD)
   apply (clarsimp simp: auth_graph_map_def)
   apply (rule exI, rule conjI, rule refl)+
   apply (erule state_bits_to_policy_vrefs_subseteq; clarsimp)
   apply (case_tac "level = asid_pool_level")
    apply (fastforce dest: vs_lookup_slot_no_asid
                     simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
   apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
   apply (erule state_vrefsD)
     apply (fastforce simp: aobjs_of_Some obj_at_def)
    apply clarsimp
   apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits)
  apply (clarsimp simp: state_objs_to_policy_def)
  apply (erule subsetD)
  apply (clarsimp simp: auth_graph_map_def)
  apply (rule exI, rule conjI, rule refl)+
  apply (erule state_bits_to_policy_vrefs_subseteq; clarsimp)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid
                    simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
  apply (frule level_of_table_vs_lookup_table)
      apply (fastforce dest: vs_lookup_slot_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)+
  apply (erule state_vrefsD)
    apply (fastforce simp: aobjs_of_Some obj_at_def)
   apply clarsimp
  apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits)
  done

lemma store_InvalidPTE_state_asids_to_policy:
  "\<lbrace>\<lambda>s. state_asids_to_policy aag s \<subseteq> pasPolicy aag \<and> invs s \<and> table_base p \<notin> global_refs s \<and>
        ((\<exists>a. vspace_for_asid a s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots)\<rbrace>
   store_pte p InvalidPTE
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
   apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
   apply (erule state_vrefsD)
     apply (fastforce simp: aobjs_of_Some obj_at_def)
    apply clarsimp
   apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits)
  apply (erule subsetD)
  apply (erule state_asids_to_policy_vrefs_subseteq; clarsimp)
  apply (case_tac "level = asid_pool_level")
   apply (fastforce dest: vs_lookup_table_no_asid
                    simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
  apply (frule level_of_table_vs_lookup_table)
      apply (fastforce dest: vs_lookup_slot_no_asid
                       simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)+
  apply (erule state_vrefsD)
    apply (fastforce simp: aobjs_of_Some obj_at_def)
   apply clarsimp
  apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def split: if_splits)
  done

lemma mapM_x_swp_store_InvalidPTE_pas_refined:
  "\<lbrace>pas_refined aag and invs and
    (\<lambda>s. \<forall>x \<in> set slots. table_base x \<notin> global_refs s \<and>
                         (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base x)))\<rbrace>
   mapM_x (swp store_pte InvalidPTE) slots
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
  "\<lbrace>\<lambda>s. invs s \<and> pte = InvalidPTE \<and> table_base p \<notin> global_refs s
               \<and> (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base p))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp wp: store_pte_invs simp: wellformed_pte_def)

lemma store_pte_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> invs s \<and> table_base p \<notin> global_refs s \<and>
        (\<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) ref))) \<and>
        ((\<exists>asid. vspace_for_asid asid s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots)\<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  supply state_asids_to_policy_arch_def[simp del]
  apply (clarsimp simp: pas_refined_def)
  apply (wpsimp wp: store_InvalidPTE_state_objs_in_policy store_InvalidPTE_state_asids_to_policy)
  done

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
  apply (metis vs_lookup_table_vspace user_region_slots is_aligned_neg_mask2 pt_slot_offset_offset)
  done

crunches unmap_page_table
  for cdt[wp]: "\<lambda>s. P (cdt s)"

definition authorised_page_table_inv :: "'a PAS \<Rightarrow> page_table_invocation \<Rightarrow> bool" where
  "authorised_page_table_inv aag pti \<equiv>
   case pti of PageTableMap cap cslot_ptr pde obj_ref \<Rightarrow>
                 is_subject aag (fst cslot_ptr) \<and> is_subject aag (obj_ref && ~~ mask pt_bits) \<and>
                 pas_cap_cur_auth aag (ArchObjectCap cap)
             | PageTableUnmap cap cslot_ptr \<Rightarrow>
                 is_subject aag (fst cslot_ptr) \<and>
                 aag_cap_auth aag (pasSubject aag) (ArchObjectCap cap) \<and>
                 (\<forall>p asid vspace_ref. cap = PageTableCap p (Some (asid, vspace_ref))
                                      \<longrightarrow> is_subject_asid aag asid \<and>
                                          (\<forall>x \<in> set [p, p + 2 ^ pte_bits .e. p + 2 ^ pt_bits - 1].
                                                             is_subject aag (x && ~~ mask pt_bits)))"

lemma perform_pt_inv_unmap_pas_refined:
 "\<lbrace>pas_refined aag and invs and valid_pti (PageTableUnmap cap ct_slot)
                            and K (authorised_page_table_inv aag (PageTableUnmap cap ct_slot))\<rbrace>
  perform_pt_inv_unmap cap ct_slot
  \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pt_inv_unmap_def
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp)
       apply (strengthen invs_psp_aligned invs_vspace_objs invs_arch_state)
       apply wps
       apply (rule hoare_vcg_all_lift[OF hoare_vcg_imp_lift'[OF mapM_x_wp_inv]], wpsimp wp: mapM_x_wp_inv)
       apply (rule hoare_vcg_conj_lift[OF hoare_strengthen_post[OF mapM_x_swp_store_InvalidPTE_pas_refined]], assumption)
       apply (rule hoare_vcg_conj_lift[OF hoare_strengthen_post[OF mapM_x_swp_store_pte_invs_unmap]], assumption)
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
  apply (prop_tac "table_base x = acap_obj cap")
   apply (drule (1) caps_of_state_aligned_page_table)
   apply (simp only: is_aligned_neg_mask_eq')
   apply (clarsimp simp: add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (fastforce dest: plus_mask_AND_NOT_mask_eq)
  apply (rule conjI; clarsimp)
   apply (fastforce simp: cte_wp_at_caps_of_state cap_range_def
                    dest: invs_valid_global_refs valid_global_refsD)
  apply (frule vspace_for_asid_target)
  apply (drule valid_vs_lookupD; clarsimp)
  apply (drule (1) unique_table_refsD[rotated]; clarsimp)
  apply (drule (1) cap_to_pt_is_pt_cap)
    apply (clarsimp simp: in_omonad obj_at_def)
   apply (fastforce intro: valid_objs_caps)
  apply (clarsimp simp: is_cap_simps)
  done

lemma vs_lookup_PageTablePTE:
  "\<lbrakk> vs_lookup_table level asid vref s' = Some (lvl', pt);
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s;
     invalid_pte_at p s; ptes_of s' = ptes_of s (p \<mapsto> pte); is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s; asid_table s' = asid_table s;
     vref \<in> user_region;
     pts_of s (the (pte_ref pte)) = Some empty_pt; pt \<noteq> pptr_from_pte pte \<rbrakk>
     \<Longrightarrow> \<exists>level' \<ge> level. vs_lookup_table level' asid vref s = Some (lvl', pt)"
  apply (induct level arbitrary: lvl' pt rule: bit0.from_top_full_induct[where y=max_pt_level])
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
   apply (frule subst[where s="ptes_of s'" and P="\<lambda>ptes. ptes _ = _"])
    apply assumption
   apply (drule mp, fastforce simp: pte_ref_def2 ptes_of_Some split: if_splits)
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
     apply (clarsimp split: if_splits simp: obind_def)
    apply (fastforce dest: vm_level_less_le_1)
   apply (fastforce dest: vm_level_less_max_pt_level vm_level_less_plus_1_mono)
  apply (case_tac "lvl' = asid_pool_level")
   apply (auto simp: geq_max_pt_level vs_lookup_table_def pool_for_asid_def obind_def)
  done

lemma vs_lookup_PageTablePTE':
  "\<lbrakk> vs_lookup_table level asid vref s = Some (lvl', pt);
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s;
     invalid_pte_at p s; ptes_of s' = ptes_of s (p \<mapsto> pte); is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s; asid_table s' = asid_table s; vref \<in> user_region  \<rbrakk>
     \<Longrightarrow> \<exists>level' \<ge> level. vs_lookup_table level' asid vref s' = Some (lvl', pt)"
  apply (induct level arbitrary: lvl' pt rule: bit0.from_top_full_induct[where y=max_pt_level])
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
  and "invalid_pte_at p s"
  and "pts_of s (the (pte_ref pte)) = Some empty_pt"
  and "the (pte_ref pte) \<noteq> table_base p"
  and "kheap s (table_base p) = Some (ArchObj (PageTable pt))"
  shows "state_vrefs (s\<lparr>kheap := \<lambda>a. if a = table_base p
                                     then Some (ArchObj (PageTable (\<lambda>a. if a = table_index p
                                                                        then pte
                                                                        else pt a)))
                                     else kheap s a\<rparr>) =
         (\<lambda>x. if x = table_base p
              then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p then pte else pt a))
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
    apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def)
   apply (drule_tac s=s and pte=pte and p=p in vs_lookup_PageTablePTE)
              apply (fastforce simp: pts_of_Some aobjs_of_Some opt_map_def pte_of_def obind_def
                               dest: pte_ptr_eq)+
   apply clarsimp
   apply (drule vs_lookup_level)
   apply (case_tac "lvl = asid_pool_level")
    apply (fastforce dest: vs_lookup_asid_pool  simp: asid_pools_of_ko_at obj_at_def)
   apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
   apply (fastforce dest: vs_lookup_table_unique_level split: if_splits)
  apply (clarsimp simp: state_vrefs_def opt_map_def)
  apply (frule vs_lookup_slot_table_base)
     apply clarsimp+
  apply (case_tac "x = table_base p"; clarsimp)
   apply (drule_tac pte=pte and s'="?s'" in vs_lookup_PageTablePTE';
          fastforce dest: pte_ptr_eq simp: pts_of_Some aobjs_of_Some opt_map_def pte_of_def obind_def)
  apply (drule_tac level=bot and pte=pte and s'="?s'" in vs_lookup_PageTablePTE';
         fastforce dest: pte_ptr_eq simp: pts_of_Some aobjs_of_Some opt_map_def pte_of_def obind_def)
  done

lemma state_vrefs_store_PageTablePTE_wp:
  "\<lbrace>\<lambda>s. invs s \<and> is_PageTablePTE pte \<and> invalid_pte_at p s \<and>
        pts_of s (the (pte_ref pte)) = Some empty_pt \<and> the (pte_ref pte) \<noteq> table_base p \<and>
        (\<exists>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<and> vref \<in> user_region \<and>
                           (\<forall>pt. ako_at (PageTable pt) (table_base p) s \<longrightarrow>
                                 P (\<lambda>x. if x = table_base p
                                        then vs_refs_aux level (PageTable (\<lambda>a. if a = table_index p
                                                                               then pte
                                                                               else pt a))
                                        else state_vrefs s x)))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (fastforce simp: fun_upd_def obj_at_def state_vrefs_store_PageTablePTE)
  done

lemma perform_pt_inv_map_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and valid_pti (PageTableMap acap (a, b) pte p)
                    and K (authorised_page_table_inv aag (PageTableMap acap (a, b) pte p))\<rbrace>
   perform_pt_inv_map acap (a,b) pte p
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
   apply (frule (1) cap_to_pt_is_pt_cap, simp, fastforce intro: valid_objs_caps)
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
      apply (drule_tac caps="caps_of_state s" in sbta_cdt; fastforce elim: is_transferable.cases
                                                                    split: if_splits)
     apply (fastforce dest: sbta_cdt_transferable simp: state_objs_to_policy_def)
    apply (clarsimp split: if_splits)
     apply (clarsimp simp: authorised_page_table_inv_def vs_refs_aux_def split: arch_kernel_obj.splits)
     apply (erule swap)
     apply (clarsimp simp: graph_of_def pte_ref2_def split: if_split_asm)
      apply (cases pte; clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
     apply (erule subsetD)
     apply (clarsimp simp: auth_graph_map_def state_objs_to_policy_def)
     apply (rule_tac x="table_base p" in exI, rule conjI, erule sym)
     apply (rule exI, rule conjI, rule refl)
     apply (rule sbta_vref)
     apply (case_tac "level = asid_pool_level")
      apply (fastforce dest: pool_for_asid_no_pte
                       simp: vs_lookup_slot_def vs_lookup_table_def invalid_pte_at_def)
     apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
     apply (erule state_vrefsD)
       apply (fastforce simp: aobjs_of_Some obj_at_def)
      apply clarsimp
     apply (fastforce simp: vs_refs_aux_def graph_of_def pte_ref2_def)
    apply (clarsimp simp: is_arch_update_def cap_master_cap_def
                   split: cap.splits arch_cap.splits option.splits)
    apply (fastforce dest: sbta_vref simp: pas_refined_def auth_graph_map_def state_objs_to_policy_def)
   apply (clarsimp simp: pas_refined_def)
   apply (erule state_asids_to_policy_aux.cases)
     apply (clarsimp simp: cte_wp_at_caps_of_state split: if_splits)
      apply (clarsimp simp: authorised_page_table_inv_def aag_cap_auth_def
                            cap_auth_conferred_def arch_cap_auth_conferred_def
                            cap_links_asid_slot_def label_owns_asid_slot_def)
     apply (fastforce dest: sata_asid)
    apply (clarsimp split: if_splits)
     apply (fastforce dest!: state_asids_to_policy_aux.intros simp: vs_refs_aux_def)
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

(* FIXME move to AInvs *)
lemma store_pte_ekheap[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp)
  apply simp
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

(* FIXME move to AInvs *)
lemma set_asid_pool_ekheap[wp]:
  "set_asid_pool p pool \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp | simp)+
  done

crunch integrity_autarch: set_asid_pool "integrity aag X st"
  (wp: crunch_wps)

lemma store_pte_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag (table_base p))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp set_object_integrity_autarch)
  apply simp
  done

lemma integrity_arch_state[iff]:
  "riscv_asid_table v = riscv_asid_table (arch_state s)
   \<Longrightarrow> integrity aag X st (s\<lparr>arch_state := v\<rparr>) = integrity aag X st s"
  unfolding integrity_def by simp

lemma integrity_riscv_global_pts[iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>riscv_global_pts := v\<rparr>)\<rparr>) =
   integrity aag X st s"
  unfolding integrity_def by simp

lemma integrity_riscv_kernel_vspace[iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>riscv_kernel_vspace := v\<rparr>)\<rparr>) =
   integrity aag X st s"
  unfolding integrity_def by simp

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
  apply (erule_tac x="pptr_from_pte (the (ptes_of s (pt_slot_offset level pt_ptr vptr)))" in meta_allE)
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp: obind_def split: if_splits option.splits)
  apply (drule meta_mp)
   apply (erule vs_lookup_table_extend)
    apply (subst pt_walk.simps, clarsimp simp: obind_def)
   apply clarsimp
  apply (erule meta_mp)
  apply (frule vs_lookup_table_pt_at; clarsimp simp: pt_at_eq)
  apply (erule (1) is_subject_trans)
  apply (clarsimp simp: pas_refined_def auth_graph_map_def)
  apply (erule subsetD, clarsimp)
  apply (rule exI conjI refl sta_vref)+
  apply (erule state_vrefsD)
    apply (fastforce simp: pts_of_Some)
   apply clarsimp
  apply (frule_tac pt_ptr=pt_ptr in pspace_aligned_pts_ofD, simp)
  apply (clarsimp simp: ptes_of_def obind_def is_PageTablePTE_def vs_refs_aux_def split: option.splits)
  apply (drule_tac g=y and f="pte_ref2 level" in graph_of_comp)
   apply (fastforce simp: pte_ref2_def)
  apply (fastforce simp: aobjs_of_Some pts_of_Some pptr_from_pte_def
                   dest: table_index_max_level_slots
                   elim: rev_bexI bexI_minus[rotated]
                 intro!: pts_of_Some_alignedD)
  done

lemma pt_lookup_slot_from_level_is_subject:
  "\<lbrakk> pas_refined aag s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     pt_lookup_slot_from_level level bot_level pt_ptr vptr (ptes_of s) = Some (level', pt);
     (\<exists>asid. vs_lookup_table level asid vptr s = Some (level, pt_ptr));
     level \<le> max_pt_level; vptr \<in> user_region; is_subject aag pt_ptr \<rbrakk>
     \<Longrightarrow> is_subject aag (table_base pt)"
  by (fastforce dest: pt_walk_is_aligned vs_lookup_table_is_aligned pt_walk_is_subject
                simp: pt_lookup_slot_from_level_def obind_def split: option.splits)

lemma pt_lookup_from_level_is_subject:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        is_subject aag pt_ptr \<and> level \<le> max_pt_level \<and> vref \<in> user_region \<and>
        (\<exists>asid. vs_lookup_table level asid vref s = Some (level, pt_ptr))\<rbrace>
   pt_lookup_from_level level pt_ptr vref pt
   \<lbrace>\<lambda>rv _. is_subject aag (table_base rv)\<rbrace>, -"
  apply (wpsimp wp: pt_lookup_from_level_wp)
  apply (erule_tac level=level and bot_level=levela and pt_ptr=pt_ptr and vptr=vref
                in pt_lookup_slot_from_level_is_subject)
  by (auto simp: pt_lookup_slot_from_level_def obind_def)

lemma unmap_page_table_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs
                       and K (is_subject_asid aag asid \<and> vaddr \<in> user_region)\<rbrace>
   unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: unmap_page_table_def sfence_def)
  apply (wpsimp wp: pt_lookup_from_level_is_subject dmo_mol_respects hoare_vcg_conj_liftE_weaker
                    store_pte_respects pt_lookup_from_level_wrp[where Q="\<lambda>_. integrity aag X st"]
         | wp (once) hoare_drop_imps hoare_vcg_E_elim)+
  apply (intro conjI; clarsimp)
    apply fastforce
   apply (rule aag_Control_into_owns[rotated], assumption)
   apply (drule sym)
   apply (clarsimp simp: vspace_for_asid_def obj_at_def pas_refined_def)
   apply (erule_tac A="state_asids_to_policy_aux _ _ _ _" in subsetD)
   apply (rule sata_asid_lookup)
    apply (simp add: vspace_for_pool_def pool_for_asid_def)
   apply (clarsimp simp: vspace_for_pool_def)
   apply (drule pool_for_asid_vs_lookupD)
   apply (erule state_vrefsD)
     apply (fastforce simp: aobjs_of_Some asid_pools_of_ko_at obj_at_def)
    apply assumption
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
               simp: authorised_page_table_inv_def sfence_def)
  apply (rename_tac cap fst_cslot_ptr snd_cslot_ptr)
  apply (wpsimp wp: set_cap_integrity_autarch)
     apply (rule_tac I="\<lambda>s. integrity aag X st s \<and> is_subject aag fst_cslot_ptr \<and> is_PageTableCap cap"
                  in mapM_x_inv_wp; clarsimp)
      apply (rule_tac P="\<lambda>s. integrity aag X st s \<and> is_PageTableCap cap" in hoare_vcg_conj_lift)
       apply (wpsimp wp: store_pte_respects)
       apply (clarsimp simp: authorised_page_table_inv_def)
       apply (case_tac cap; clarsimp)
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
  by wpsimp

lemma unmap_page_pas_refined:
  "\<lbrace>pas_refined aag and invs and K (vptr \<in> user_region)\<rbrace>
   unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding unmap_page_def
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
  apply (metis vs_lookup_table_vspace user_region_slots is_aligned_neg_mask2 pt_slot_offset_offset)
  done

definition authorised_slots :: "'a PAS \<Rightarrow> pte \<times> obj_ref \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
 "authorised_slots aag m s \<equiv> case m of (pte, slot) \<Rightarrow>
    (\<forall>level asid vref x.
       vs_lookup_slot level asid vref s = Some (level, slot) \<longrightarrow>
       vref \<in> user_region \<longrightarrow>
       level \<le> max_pt_level \<longrightarrow>
       pte_ref2 level pte = Some x \<longrightarrow>
         (\<forall>a \<in> snd (snd x). \<forall>p \<in> ptr_range (fst x) (fst (snd x)). aag_has_auth_to aag a p)) \<and>
                                                                   is_subject aag (table_base slot)"

definition authorised_page_inv :: "'a PAS \<Rightarrow> page_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow>  bool" where
  "authorised_page_inv aag pgi s \<equiv> case pgi of
     PageMap cap ptr slots \<Rightarrow> pas_cap_cur_auth aag (ArchObjectCap cap) \<and>
                              is_subject aag (fst ptr) \<and> authorised_slots aag slots s
   | PageUnmap cap ptr \<Rightarrow> pas_cap_cur_auth aag (ArchObjectCap cap) \<and> is_subject aag (fst ptr)
   | PageGetAddr ptr \<Rightarrow> True"

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

crunches set_cap
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
  "\<lbrace>pas_refined aag and invs and valid_page_inv (PageMap cap ct_slot (pte,slot))
                    and authorised_page_inv aag (PageMap cap ct_slot (pte,slot))\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding perform_pg_inv_map_def
  apply (wpsimp simp: simp: pas_refined_def state_objs_to_policy_def)
    apply (subst conj_commute, subst conj_commute)
    apply clarsimp
    apply (rule hoare_vcg_conj_lift, wpsimp)
    apply wps
    apply (rule state_vrefs_store_NonPageTablePTE_wp)
   apply (rule_tac Q="\<lambda>_. invs and pas_refined aag and K (\<not> is_PageTablePTE pte)
                               and authorised_page_inv aag (PageMap cap ct_slot (pte,slot))
                               and same_ref (pte,slot) (ArchObjectCap cap)"
                in hoare_strengthen_post[rotated])
    apply (clarsimp simp: pas_refined_def)
    apply (rule conjI)
     apply clarsimp
     apply (intro exI, rule conjI, assumption)
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (erule_tac A="state_asids_to_policy_aux _ _ _ _" in subsetD)
      apply (erule state_asids_to_policy_aux.cases)
        apply (fastforce dest: sata_asid)
       apply (clarsimp simp: cte_wp_at_caps_of_state)
       apply (clarsimp simp only: split: if_splits)
        apply (clarsimp simp: vs_refs_aux_def)
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
      apply (clarsimp simp: vs_refs_aux_def graph_of_def)
      apply (erule_tac P="_ \<in> _" in swap)
      apply (case_tac "level = asid_pool_level")
       apply (fastforce dest!: vs_lookup_slot_no_asid
                         simp: ptes_of_Some pts_of_Some aobjs_of_Some obj_at_def)
      apply (clarsimp split: if_split_asm)
       apply (case_tac pte; clarsimp simp: authorised_slots_def)
      apply (subst (asm) vs_lookup_slot_table_unfold; clarsimp)
      apply (erule subsetD)
      apply (clarsimp simp: state_objs_to_policy_def)
      apply (rule exI, rule conjI, rule refl)+
      apply (rule sbta_vref)
      apply (erule state_vrefsD)
        apply (fastforce simp: aobjs_of_Some obj_at_def)
       apply fastforce
      apply (fastforce simp: vs_refs_aux_def graph_of_def)
     apply (fastforce dest: sbta_vref simp: state_objs_to_policy_def)
    apply (clarsimp simp: same_ref_def)
   apply (wpsimp wp: arch_update_cap_invs_map set_cap_pas_refined_not_transferable)
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
  apply (simp add: perform_page_invocation_def)
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
               simp: sfence_def  is_aligned_mask[symmetric]
          | wp (once) hoare_drop_imps
                      mapM_set''[where f="(\<lambda>a. store_pte a InvalidPTE)"
                                   and I="\<lambda>x s. is_subject aag (x && ~~ mask pt_bits)"
                                   and Q="integrity aag X st"]
          | wp (once) hoare_drop_imps[where R="\<lambda>rv s. rv"])+
  apply (clarsimp simp: pt_lookup_slot_def)
  apply (frule pt_lookup_slot_from_level_is_subject)
          apply (fastforce simp: valid_arch_state_asid_table
                           dest: vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup])+
   apply (erule (1) is_subject_asid_trans)
   apply (clarsimp simp: pas_refined_def vspace_for_asid_def vspace_for_pool_def)
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
                     perform_pg_inv_map_def perform_pg_inv_unmap_def sfence_def
              split: page_invocation.split sum.split
                     arch_cap.split option.split, safe)
       apply ((wp set_cap_integrity_autarch unmap_page_respects
                  mapM_x_and_const_wp[OF store_pte_respects] store_pte_respects
              | elim conjE
              | clarsimp dest!: set_tl_subset_mp
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
    apply (wpsimp wp: set_mrs_integrity_autarch set_message_info_integrity_autarch
                simp: ipc_buffer_has_auth_def perform_pg_inv_get_addr_def)
    done
qed

lemma integrity_asid_table_entry_update':
  "\<lbrakk> integrity aag X st s; atable = riscv_asid_table (arch_state s); is_subject aag v;
     (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid \<longrightarrow> is_subject_asid aag asid') \<rbrakk>
     \<Longrightarrow> integrity aag X st (s\<lparr>arch_state :=
                               arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid_high_bits_of asid
                                                                    then (Some v)
                                                                    else atable a\<rparr>\<rparr>)"
  by (clarsimp simp: integrity_def)

lemma asid_table_entry_update_integrity:
 "\<lbrace>integrity aag X st and (\<lambda>s. atable = riscv_asid_table (arch_state s)) and K (is_subject aag v)
                      and K (\<forall>asid'. asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of asid
                                     \<longrightarrow> is_subject_asid aag asid')\<rbrace>
  modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := atable(asid_high_bits_of asid := Some v)\<rparr>\<rparr>)
  \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by wpsimp (blast intro: integrity_asid_table_entry_update')

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
   apply (wpsimp wp: set_cap_integrity_autarch cap_insert_integrity_autarch
                     asid_table_entry_update_integrity retype_region_integrity[where sz=12]
                     hoare_weak_lift_imp delete_objects_valid_vspace_objs delete_objects_valid_arch_state)
  apply (clarsimp simp: authorised_asid_control_inv_def ptr_range_def add.commute range_cover_def
                        obj_bits_api_def default_arch_object_def pageBits_def word_bits_def)
  apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
  apply (clarsimp simp: and_mask_eq_iff_shiftr_0 mask_zero word_size_bits_def)
  apply (frule is_aligned_no_overflow_mask)
  apply (clarsimp simp: mask_def)
  done

lemma state_vrefs_asid_pool_map:
  "\<lbrakk> ako_at (ASIDPool Map.empty) frame s; asid_table s (asid_high_bits_of base) = None \<rbrakk>
     \<Longrightarrow> state_vrefs (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := \<lambda>a. if a = asid_high_bits_of base
                                                                           then Some frame
                                                                           else asid_table s a\<rparr>\<rparr>)
         = state_vrefs s"
  apply (rule all_ext)
  apply clarsimp
  apply safe
   apply (subst (asm) state_vrefs_def, clarsimp)
   apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
    apply (clarsimp simp: vs_lookup_table_def pool_for_asid_def vspace_for_pool_def graph_of_def
                          asid_pools_of_ko_at obj_at_def vs_refs_aux_def aobjs_of_Some
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
  do asid_table <- gets (riscv_asid_table \<circ> arch_state);
     asid_table' <- return (asid_table(asid_high_bits_of base \<mapsto> frame));
     modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := asid_table'\<rparr>\<rparr>)
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
  apply clarsimp
  apply (erule state_asids_to_policy_aux.cases)
    apply (fastforce dest: sata_asid)
  apply (subst (asm) state_vrefs_asid_pool_map; clarsimp)
  apply (case_tac "asid_high_bits_of asid = asid_high_bits_of base")
  apply (clarsimp simp: state_vrefs_def aobjs_of_Some obj_at_def vs_refs_aux_def graph_of_def)
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
   apply (rule pas_refined_asid_control_helper hoare_seq_ext hoare_K_bind)+
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
   apply (rule_tac Q="\<lambda>rv s.
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
    apply (simp add: page_bits_def)
    apply (wp add: delete_objects_pspace_no_overlap hoare_vcg_ex_lift
                   delete_objects_descendants_range_in delete_objects_invs_ex
                   delete_objects_pas_refined
              del: Untyped_AI.delete_objects_pspace_no_overlap
           | simp add: page_bits_def)+
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
   apply (simp add: page_bits_def)
  apply (frule_tac x=x in bspec)
   apply (simp add: is_aligned_no_overflow)
  apply (clarsimp simp: ptr_range_def invs_psp_aligned invs_valid_objs aag_cap_auth_def
                        descendants_range_def2 empty_descendants_range_in page_bits_def
                        pas_refined_refl cap_links_asid_slot_def label_owns_asid_slot_def
                        cap_links_irq_def range_cover_def obj_bits_api_def pageBits_def
                        default_arch_object_def and_mask_eq_iff_shiftr_0 mask_zero)
  apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
  apply (intro conjI; fastforce intro: empty_descendants_range_in)
  done

lemma copy_global_mappings_integrity:
  "\<lbrace>integrity aag X st and K (is_aligned x pt_bits \<and> is_subject aag x)\<rbrace>
   copy_global_mappings x
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copy_global_mappings_def)
  apply (wp mapM_x_wp[OF _ subset_refl] store_pte_respects)
    apply (simp only: pt_index_def)
    apply (subst table_base_offset_id)
      apply simp
     apply (clarsimp simp: pte_bits_def word_size_bits_def pt_bits_def
                           table_size_def ptTranslationBits_def mask_def)
     apply (word_bitwise, fastforce)
    apply clarsimp
   apply wpsimp+
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
  apply (wpsimp wp: set_asid_pool_integrity_autarch get_cap_wp set_cap_integrity_autarch
                    copy_global_mappings_integrity hoare_drop_imps)
  apply (clarsimp simp: authorised_asid_pool_inv_def valid_apinv_def cte_wp_at_caps_of_state is_cap_simps)
  apply (rule conjI)
   apply (rule is_aligned_pt; fastforce simp: valid_cap_def dest: caps_of_state_valid)
  apply (frule_tac ptr="(a,b)" in sbta_caps)
    apply simp
   apply (simp add: cap_auth_conferred_def arch_cap_auth_conferred_def)
  apply (erule_tac x=a in is_subject_trans, assumption)
  apply (fastforce simp: pas_refined_def auth_graph_map_def state_objs_to_policy_def)
  done

lemma store_pte_state_vrefs_unreachable:
  "\<lbrace>\<lambda>s. P (state_vrefs s) \<and> pspace_aligned s \<and> valid_vspace_objs s \<and>
        valid_asid_table s \<and> (\<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s)\<rbrace>
   store_pte p pte
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
     apply (prop_tac "x \<noteq> table_base p", clarsimp)
     apply (fastforce simp: fun_upd_def aobjs_of_Some opt_map_def)
    apply clarsimp
   apply fastforce
  apply (subst (asm) state_vrefs_def, clarsimp)
  apply (rule state_vrefsD)
     apply (subst (asm) vs_lookup_table_unreachable_upd_idem; fastforce)
    apply (prop_tac "x \<noteq> table_base p")
     apply (subst (asm) vs_lookup_table_unreachable_upd_idem; fastforce dest: vs_lookup_level)
    apply (fastforce simp: fun_upd_def aobjs_of_Some)
   apply clarsimp
  apply clarsimp
  done

lemma copy_global_mappings_state_vrefs:
  "\<lbrace>\<lambda>s. P (state_vrefs s) \<and> invs s \<and> is_aligned pt_ptr pt_bits \<and> (\<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)\<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding copy_global_mappings_def
  apply clarsimp
  apply wp
    apply (rule_tac Q="\<lambda>_ s. P (state_vrefs s) \<and> pspace_aligned s \<and> valid_vspace_objs s \<and>
                             valid_asid_table s \<and> unique_table_refs s \<and> valid_vs_lookup s \<and>
                             valid_objs s \<and> is_aligned pt_ptr pt_bits \<and> is_aligned global_pt pt_bits \<and>
                             (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (pt_ptr)) s) \<and>
                             (\<forall>level. \<not> \<exists>\<rhd> (level, table_base (global_pt)) s)"
                 in hoare_strengthen_post[rotated], clarsimp)
    apply (wpsimp wp: store_pte_state_vrefs_unreachable store_pte_valid_vs_lookup_unreachable
                      store_pte_vs_lookup_table_unreachable store_pte_valid_vspace_objs
                      hoare_vcg_all_lift hoare_vcg_imp_lift' mapM_x_wp')
    apply (prop_tac "table_base (pt_ptr + (x << pte_bits)) = pt_ptr \<and>
                     table_base (global_pt + (x << pte_bits)) = global_pt")
     apply (metis mask_2pm1 table_base_plus)
    apply (fastforce simp: valid_objs_caps ptes_of_wellformed_pte)
   apply wpsimp+
  apply (simp add: invs_valid_global_vspace_mappings)
  apply (intro conjI; clarsimp)
  apply (frule invs_valid_global_arch_objs)
  apply (frule valid_global_arch_objs_pt_at)
  using not_in_global_refs_vs_lookup apply fastforce
  done

crunches copy_global_mappings
  for tcb_domain_map_wellformed[wp]: "\<lambda>s. P (tcb_domain_map_wellformed aag s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and thread_st_auth[wp]: "\<lambda>s. P (thread_st_auth s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"
  (wp: crunch_wps)

lemma copy_global_mappings_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> invs s \<and> is_aligned pt_ptr pt_bits \<and> (\<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)\<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wps)
   apply (wpsimp wp: copy_global_mappings_state_vrefs)+
  done

lemma store_asid_pool_entry_state_vrefs:
  "\<lbrace>\<lambda>s. P (\<lambda>x. if x = pool_ptr
               then vs_refs_aux asid_pool_level (ASIDPool (\<lambda>a. if a = asid_low_bits_of asid
                                                               then Some pt_base
                                                               else the (asid_pools_of s pool_ptr) a))
               else if x = pt_base
               then vs_refs_aux max_pt_level (the (aobjs_of s x))
               else state_vrefs s x) \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        pool_for_asid asid s = Some pool_ptr \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<exists>pt. pts_of s pt_base = Some pt \<and> kernel_mappings_only pt s)\<rbrace>
   store_asid_pool_entry pool_ptr asid (Some pt_base)
   \<lbrace>\<lambda>_ s. P (state_vrefs s)\<rbrace>"
  unfolding store_asid_pool_entry_def set_asid_pool_def
  apply (wpsimp wp: set_object_wp get_cap_wp)
  apply (erule rsubst[where P=P])
  apply (rule all_ext)
  apply (clarsimp split del: if_split)
  apply (prop_tac "is_aligned pt_base pt_bits")
   apply (fastforce elim: pspace_aligned_pts_ofD dest: invs_psp_aligned)
  apply safe
   apply (clarsimp split: if_splits)
     apply (frule pool_for_asid_vs_lookupD)
     apply (rule_tac level=asid_pool_level in state_vrefsD)
        apply (simp only: fun_upd_def)
        apply (subst asid_pool_map.vs_lookup_table[simplified fun_upd_def])
          apply (fastforce simp: asid_pool_map_def asid_pools_of_ko_at
                                 valid_apinv_def asid_low_bits_of_def aobjs_of_Some)
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
      apply (fastforce simp: pts_of_Some)
     apply (fastforce simp: pts_of_Some)
    apply (fastforce simp: pts_of_Some)
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
       apply (fastforce simp: vs_lookup_table_def vspace_for_pool_def asid_pools_of_ko_at obj_at_def
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
   apply (prop_tac "asid_pools_of s pool_ptr = Some pool")
    apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)
   apply (clarsimp simp: vs_refs_aux_def)
  apply (case_tac "asida = asid \<and> bot \<le> max_pt_level"; clarsimp)
  apply (case_tac "x = pt_base")
   apply (fastforce dest: vs_lookup_level)
  apply (fastforce simp: state_vrefs_def)
  done

crunches store_asid_pool_entry
  for irq_map_wellformed[wp]: "\<lambda>s. P (irq_map_wellformed aag s)"
  and tcb_domain_map_wellformed[wp]: "\<lambda>s. P (tcb_domain_map_wellformed aag s)"
  and state_irqs_to_policy[wp]: "\<lambda>s. P (state_irqs_to_policy aag s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and cdt[wp]: "\<lambda>s. P (cdt s)"
  and thread_st_auth[wp]: "\<lambda>s. P (thread_st_auth s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"

lemma store_asid_pool_entry_pas_refined:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<and>
        pool_for_asid asid s = Some pool_ptr \<and> is_subject aag pool_ptr \<and>
        is_subject aag pt_base \<and> is_subject_asid aag asid \<and>
        (\<forall>level. \<not>\<exists>\<rhd> (level, pt_base) s) \<and>
        (\<forall>pool. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> pool (asid_low_bits_of asid) = None) \<and>
        (\<exists>pt. pts_of s pt_base = Some pt \<and> kernel_mappings_only pt s)\<rbrace>
   store_asid_pool_entry pool_ptr asid (Some pt_base)
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
      apply (simp add: asid_pools_of_ko_at aobjs_of_ako_at_Some)
     apply clarsimp
    apply (fastforce simp: vs_refs_aux_def graph_of_def)
   apply (fastforce simp: vs_refs_aux_def kernel_mappings_only_def
                          graph_of_def pts_of_Some pte_ref2_def
                    dest: sbta_vref split: if_splits)
  apply (erule state_asids_to_policy_aux.cases)
    apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
    apply (fastforce dest: sata_asid)
   apply (case_tac "poolptr = pool_ptr")
    apply (clarsimp simp: vs_refs_aux_def graph_of_def obj_at_def split: if_splits)
     apply (clarsimp simp: pool_for_asid_def asid_pools_of_ko_at valid_asid_table_def inj_on_def)
     apply (drule_tac x="asid_high_bits_of asid" in bspec, clarsimp)
     apply (drule_tac x="asid_high_bits_of asida" in bspec, clarsimp)
     apply clarsimp
     apply (drule asid_high_low)
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
      apply (simp add: asid_pools_of_ko_at aobjs_of_ako_at_Some)
     apply simp
    apply (fastforce simp: vs_refs_aux_def graph_of_def)
   apply (case_tac "poolptr = pt_base")
    apply (clarsimp simp: vs_refs_aux_def pts_of_Some)
   apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
   apply (fastforce simp: sata_asid_lookup)
  apply (erule subsetD[where A="state_asids_to_policy_aux _ _ _ _"])
  apply (fastforce simp: sata_asidpool)
  done


lemma copy_global_mappings_vs_lookup_table_noteq:
  "\<lbrace>\<lambda>s. vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr) \<and> invs s \<and>
        is_aligned pt_ptr pt_bits \<and> vref \<in> user_region \<and> (\<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s)\<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr)\<rbrace>"
  unfolding copy_global_mappings_def
  apply clarsimp
  apply wp
    apply (rule_tac Q="\<lambda>_. pspace_aligned and valid_vspace_objs and valid_asid_table and
                           unique_table_refs and valid_vs_lookup and valid_objs and
                           (\<lambda>s. vs_lookup_table level asid vref s \<noteq> Some (level, pt_ptr) \<and>
                                vref \<in> user_region \<and> is_aligned pt_ptr pt_bits \<and>
                                (\<forall>level. \<not> \<exists>\<rhd> (level, table_base pt_ptr) s))"
                 in hoare_strengthen_post[rotated], clarsimp)
    apply (wpsimp wp: mapM_x_wp' store_pte_valid_vspace_objs store_pte_vs_lookup_table_unreachable
                      store_pte_valid_vs_lookup_unreachable hoare_vcg_all_lift hoare_vcg_imp_lift')
    apply (metis valid_objs_caps ptes_of_wellformed_pte mask_2pm1 table_base_plus)
   apply wpsimp
  apply fastforce
  done

lemma perform_asid_pool_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and valid_apinv api and K (authorised_asid_pool_inv aag api)\<rbrace>
   perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)
  apply (strengthen invs_psp_aligned invs_vspace_objs valid_arch_state_asid_table invs_arch_state |
         wpsimp simp: ako_asid_pools_of
                  wp: copy_global_mappings_invs copy_global_mappings_pas_refined
                      copy_global_mappings_copies copy_global_mappings_vs_lookup_table_noteq
                      store_asid_pool_entry_pas_refined set_cap_pas_refined get_cap_wp
                      arch_update_cap_invs_map hoare_vcg_all_lift hoare_vcg_imp_lift')+
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_apinv_def cong: conj_cong)
  apply (clarsimp simp: is_PageTableCap_def is_ArchObjectCap_def)
  apply (clarsimp split: option.splits)
  apply (clarsimp simp: authorised_asid_pool_inv_def)
  apply (prop_tac "(\<forall>x xa xb. vs_lookup_table x xa xb s = Some (x, x41) \<longrightarrow> xb \<notin> user_region)")
   apply (frule (1) caps_of_state_valid)
   apply (clarsimp simp: valid_cap_def)
   apply (clarsimp simp: obj_at_def)
   apply (rename_tac asid' pool_ptr a b acap_obj level asid vref pt)
   apply (drule (1) vs_lookup_table_valid_cap; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp add: pts_of_Some aobjs_of_Some, fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (clarsimp simp: is_cap_simps)
  apply (clarsimp simp: is_arch_update_def update_map_data_def is_cap_simps cap_master_cap_def asid_bits_of_defs)
  apply (intro conjI)
         apply (fastforce dest: cap_cur_auth_caps_of_state pas_refined_refl
                          simp: update_map_data_def aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                               cap_links_asid_slot_def label_owns_asid_slot_def cap_links_irq_def)
        apply (fastforce dest: caps_of_state_valid
                         simp: update_map_data_def valid_cap_def cap_aligned_def wellformed_mapdata_def)
       apply (fastforce dest: caps_of_state_aligned_page_table)
      apply (fastforce dest: unique_table_capsD[rotated])
     apply (fastforce dest: cap_not_in_valid_global_refs)
    apply (fastforce dest: cap_cur_auth_caps_of_state pas_refined_Control
                     simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
   apply fastforce
  apply (fastforce dest: invs_valid_table_caps simp: valid_table_caps_def)
  done


definition authorised_arch_inv :: "'a PAS \<Rightarrow> arch_invocation \<Rightarrow> 's :: state_ext state \<Rightarrow> bool" where
 "authorised_arch_inv aag ai s \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> authorised_page_table_inv aag pti
   | InvokePage pgi \<Rightarrow> authorised_page_inv aag pgi s
   | InvokeASIDControl aci \<Rightarrow> authorised_asid_control_inv aag aci
   | InvokeASIDPool api \<Rightarrow> authorised_asid_pool_inv aag api"

lemma invoke_arch_respects:
  "\<lbrace>integrity aag X st and authorised_arch_inv aag ai and
    pas_refined aag and invs and valid_arch_inv ai and is_subject aag \<circ> cur_thread\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: arch_perform_invocation_def)
  apply (wpsimp wp: perform_page_table_invocation_respects perform_page_invocation_respects
                    perform_asid_control_invocation_respects perform_asid_pool_invocation_respects)
  apply (auto simp: authorised_arch_inv_def valid_arch_inv_def)
  done

lemma invoke_arch_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and ct_active
                    and valid_arch_inv ai and authorised_arch_inv aag ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: arch_perform_invocation_def valid_arch_inv_def)
  apply (wpsimp wp: perform_page_table_invocation_pas_refined perform_asid_pool_invocation_pas_refined
                    perform_page_invocation_pas_refined perform_asid_control_invocation_pas_refined)+
  apply (auto simp: authorised_arch_inv_def)
  done

lemma vspace_for_asid_is_subject:
  "\<lbrakk> vspace_for_asid a s = Some xaa; pas_refined aag s; valid_asid_table s; is_subject_asid aag a \<rbrakk>
     \<Longrightarrow> is_subject aag xaa"
  apply (frule vspace_for_asid_vs_lookup)
  apply (clarsimp simp: vspace_for_asid_def)
  apply (frule pool_for_asid_vs_lookupD)
  apply (frule (1) pool_for_asid_validD)
  apply (clarsimp simp: vspace_for_pool_def pool_for_asid_def asid_pools_of_ko_at obj_at_def)
  apply (frule_tac vrefs="state_vrefs s" in sata_asid_lookup)
   apply (rule_tac level=asid_pool_level and asid=a and vref=0 in state_vrefsD)
  by (fastforce simp: aobjs_of_Some vs_refs_aux_def graph_of_def asid_low_bits_of_mask_eq[symmetric]
                      ucast_ucast_b is_up_def source_size_def target_size_def word_size pas_refined_def
                dest: aag_wellformed_Control)+

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
  apply (prop_tac "\<forall>y \<in> set [x, x + 2 ^ pte_bits .e. x + 2 ^ pt_bits - 1]. table_base y = x")
   apply (drule (1) caps_of_state_aligned_page_table)
   apply (clarsimp simp only: is_aligned_neg_mask_eq' add_mask_fold)
   apply (drule subsetD[OF upto_enum_step_subset], clarsimp)
   apply (drule neg_mask_mono_le[where n=pt_bits])
   apply (drule neg_mask_mono_le[where n=pt_bits])
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
                                                           simp: user_vtop_canonical_user
                                                                 user_region_def)
   apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                         cap_links_asid_slot_def label_owns_asid_slot_def cap_links_irq_def)
  apply (auto simp: caps_of_state_pasObjectAbs_eq authorised_page_table_inv_def
                    cap_auth_conferred_def arch_cap_auth_conferred_def)
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
  unfolding decode_frame_invocation_def authorised_arch_inv_def decode_fr_inv_map_def
  apply (wpsimp wp: check_vp_wpR simp: Let_def authorised_page_inv_def)
  apply (rule conj_imp_strg)
  apply (cases excaps; clarsimp)
  apply (clarsimp simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def
                        cap_links_asid_slot_def cap_links_irq_def authorised_slots_def)
  apply (prop_tac "msg ! 0 \<in> user_region")
   apply (fastforce dest: not_le_imp_less user_vtop_canonical_user
                    elim: dual_order.trans is_aligned_no_overflow_mask
                    simp: user_region_def vmsz_aligned_def)
  apply (rule conjI)
   apply (frule (1) pt_lookup_slot_vs_lookup_slotI, clarsimp)
   apply (drule (1) vs_lookup_slot_unique_level; clarsimp)
   apply (clarsimp simp: cte_wp_at_caps_of_state make_user_pte_def pte_ref2_def split: if_splits)
   apply (subst (asm) ptrFromPAddr_addr_from_ppn[OF is_aligned_pageBitsForSize_table_size])
    apply (fastforce dest: caps_of_state_valid
                     simp: valid_cap_def cap_aligned_def pageBitsForSize_pt_bits_left)
   apply (fastforce simp: vspace_cap_rights_to_auth_def mask_vm_rights_def validate_vm_rights_def
                          vm_kernel_only_def vm_read_only_def
                   split: if_splits)
  apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
  apply (subst table_base_pt_slot_offset)
   apply (fastforce simp: cte_wp_at_caps_of_state
                    dest: caps_of_state_aligned_page_table pt_walk_is_aligned)
  apply (frule vs_lookup_table_vref_independent[OF vspace_for_asid_vs_lookup, simplified])
  apply (erule pt_walk_is_subject[rotated 4]; fastforce intro: vspace_for_asid_is_subject)
  done

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
  apply (cases excaps; clarsimp)
  apply (rename_tac excaps_tail)
  apply (case_tac excaps_tail; clarsimp)
  apply (clarsimp simp: aag_cap_auth_def cte_wp_at_caps_of_state)
  apply (drule (1) caps_of_state_valid[where cap="UntypedCap _ _ _ _"])
  apply (fastforce simp: valid_cap_def cap_aligned_def is_cap_simps cap_auth_conferred_def
                   dest: pas_refined_Control)
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
  apply (clarsimp simp: authorised_asid_pool_inv_def is_ASIDPoolCap_def)
  apply (rule conjI)
   apply (clarsimp simp: pas_refined_def state_objs_to_policy_def auth_graph_map_def)
   apply (drule subsetD)
    apply (fastforce dest!: sbta_caps
                      simp: obj_refs_def cte_wp_at_caps_of_state
                            cap_auth_conferred_def arch_cap_auth_conferred_def)
   apply (fastforce dest: aag_wellformed_Control)
  apply (erule allE, erule mp)
  apply (fastforce dest: caps_of_state_valid asid_high_bits_of_add_ucast
                   simp: cte_wp_at_caps_of_state valid_cap_def)
  done

lemma decode_arch_invocation_authorised:
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
                    decode_asid_control_invocation_authorised decode_frame_invocation_authorised)
  apply auto
  done

lemma authorised_arch_inv_sa_update:
  "authorised_arch_inv aag i (scheduler_action_update (\<lambda>_. act) s) =
   authorised_arch_inv aag i s"
  by (clarsimp simp: authorised_arch_inv_def authorised_page_inv_def authorised_slots_def
              split: arch_invocation.splits page_invocation.splits)

lemma set_thread_state_authorised_arch_inv[wp]:
  "set_thread_state ref ts \<lbrace>authorised_arch_inv aag i\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: dxo_wp_weak)
     apply (clarsimp simp: authorised_arch_inv_def authorised_page_inv_def authorised_slots_def
                    split: arch_invocation.splits page_invocation.splits)
    apply (wpsimp wp: set_object_wp)+
  apply (clarsimp simp: authorised_arch_inv_def authorised_page_inv_def
                        authorised_slots_def vs_lookup_slot_def obind_def
                 split: arch_invocation.splits page_invocation.splits if_splits option.splits)
  apply (clarsimp simp: vs_lookup_table_def obind_def vspace_for_pool_def
                 split: option.splits if_splits)
  apply (subgoal_tac "(\<lambda>p. pte_of p ((pts_of s)(ref := None))) = ptes_of s")
   apply fastforce
  apply (fastforce simp: pte_of_def obind_def pts_of_Some aobjs_of_Some get_tcb_def
                  split: option.splits)
  done

end


context begin interpretation Arch .

requalify_facts
  invoke_arch_pas_refined
  invoke_arch_respects
  decode_arch_invocation_authorised
  authorised_arch_inv_sa_update
  set_thread_state_authorised_arch_inv

requalify_consts
  authorised_arch_inv

end

declare authorised_arch_inv_sa_update[simp]
declare set_thread_state_authorised_arch_inv[wp]

end
