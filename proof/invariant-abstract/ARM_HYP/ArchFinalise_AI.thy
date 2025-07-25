(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalise_AI
imports Finalise_AI
begin

context Arch begin

named_theorems Finalise_AI_assms

crunch prepare_thread_delete
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps)

declare prepare_thread_delete_caps_of_state [Finalise_AI_assms]

arch_global_naming

lemma valid_global_refs_asid_table_udapte [iff]:
  "valid_global_refs (s\<lparr>arch_state := arm_asid_table_update f (arch_state s)\<rparr>) =
  valid_global_refs s"
  by (simp add: valid_global_refs_def global_refs_def)

lemma reachable_pg_cap_cdt_update[simp]:
  "reachable_pg_cap x (cdt_update f s) = reachable_pg_cap x s"
  by (simp add: reachable_pg_cap_def)

lemma reachable_pg_cap_is_original_cap_update [simp]:
  "reachable_pg_cap x (is_original_cap_update f s) = reachable_pg_cap x s"
  by (simp add: reachable_pg_cap_def)

lemma reachable_pg_cap_update[simp]:
  "reachable_pg_cap cap' (trans_state f s) = reachable_pg_cap cap' s"
  by (simp add:reachable_pg_cap_def vs_lookup_pages_def
    vs_lookup_pages1_def obj_at_def)

lemma vs_lookup_pages_eq:
  "\<lbrakk>valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s;
    valid_cap cap s; table_cap_ref cap = Some vref; oref \<in> obj_refs cap\<rbrakk>
   \<Longrightarrow> (vref \<unrhd> oref) s = (vref \<rhd> oref) s"
  apply (clarsimp simp: table_cap_ref_def arch_cap_fun_lift_def
                        vs_lookup_pages_eq_at[symmetric, THEN fun_cong]
                        vs_lookup_pages_eq_ap[symmetric, THEN fun_cong]
                 split: cap.splits arch_cap.splits option.splits)
  apply (rule iffI[rotated, OF vs_lookup_pages_vs_lookupI], assumption)
  apply (simp add: valid_cap_def)
  apply (erule vs_lookup_vs_lookup_pagesI', clarsimp+)
  done

lemma nat_to_cref_unat_of_bl':
  "\<lbrakk> length xs < 32; n = length xs \<rbrakk> \<Longrightarrow>
   nat_to_cref n (unat (of_bl xs :: machine_word)) = xs"
  apply (simp add: nat_to_cref_def word_bits_def)
  apply (rule nth_equalityI)
   apply simp
  apply clarsimp
  apply (subst to_bl_nth)
   apply (simp add: word_size)
  apply (simp add: word_size)
  apply (simp add: test_bit_of_bl rev_nth)
  apply fastforce
  done

lemmas nat_to_cref_unat_of_bl = nat_to_cref_unat_of_bl' [OF _ refl]

lemma invs_arm_asid_table_unmap:
  "invs s \<and> is_aligned base asid_low_bits \<and> base \<le> mask asid_bits
       \<and> (\<forall>x\<in>set [0.e.2 ^ asid_low_bits - 1]. arm_asid_map (arch_state s) (base + x) = None)
       \<and> tab = arm_asid_table (arch_state s)
     \<longrightarrow> invs (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
  apply (strengthen valid_asid_map_unmap valid_vspace_objs_unmap_strg
                    valid_vs_lookup_unmap_strg valid_arch_state_unmap_strg)
  apply (simp add: valid_irq_node_def valid_kernel_mappings_def)
  apply (simp add: valid_table_caps_def valid_machine_state_def valid_global_objs_def
                   valid_global_vspace_mappings_def)
  done

lemma delete_asid_pool_invs[wp]:
  "\<lbrace>invs and K (base \<le> mask asid_bits)\<rbrace>
     delete_asid_pool base pptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: delete_asid_pool_def)
  apply wp
  apply (strengthen invs_arm_asid_table_unmap)
  apply simp
  apply (rule hoare_vcg_conj_lift,
           (rule mapM_invalidate[where ptr=pptr])?,
           ((wpsimp wp: mapM_wp' simp: if_apply_def2)+)[1])+
    apply wp+
  apply (clarsimp simp: is_aligned_mask[symmetric])
  apply (rule conjI)
   apply (rule vs_lookupI)
    apply (erule vs_asid_refsI)
   apply simp
  apply clarsimp
  done

lemma delete_asid_invs[wp]:
  "\<lbrace>invs and K (asid \<le> mask asid_bits)\<rbrace>
     delete_asid asid pd
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: delete_asid_def cong: option.case_cong)
  apply (wpsimp wp: set_asid_pool_invs_unmap)+
     apply (simp add: invalidate_asid_entry_def invalidate_asid_def invalidate_hw_asid_entry_def)
     apply (wp load_hw_asid_wp)+
    apply (simp add: flush_space_def)
    apply (wpsimp wp: load_hw_asid_wp)+
  apply (subgoal_tac "valid_asid_table (arm_asid_table (arch_state s)) s")
   prefer 2
   apply fastforce
  apply (clarsimp simp: valid_asid_table_def)
  apply (rule conjI)
   apply clarsimp
   apply (subgoal_tac "asid_high_bits_of asid = asid_high_bits_of asida")
    prefer 2
    apply (fastforce elim!: inj_onD)
   apply (drule asid_low_high_bits', simp)
     apply (simp add: mask_def)
    apply (simp add: mask_def)
   apply blast
  apply clarsimp
  apply (subgoal_tac "asid_high_bits_of asid = asid_high_bits_of asida")
   prefer 2
   apply (fastforce elim!: inj_onD)
  apply (drule asid_low_high_bits', simp)
    apply (simp add: mask_def)
   apply (simp add: mask_def)
  apply blast
  done

crunch page_table_mapped
  for invs: "invs"

lemma delete_asid_pool_unmapped[wp]:
  "\<lbrace>\<top>\<rbrace>
     delete_asid_pool asid poolptr
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> poolptr) s\<rbrace>"
  apply (simp add: delete_asid_pool_def)
  apply wp
      apply (rule hoare_strengthen_post[where Q'="\<lambda>_. \<top>"])
      apply wp
     defer
     apply wp+
   apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                  dest!: graph_ofD)
   apply (erule rtranclE)
    apply (simp add: up_ucast_inj_eq)
   apply (drule vs_lookup1D)
   apply clarsimp
   apply (clarsimp simp: vs_refs_def
                  split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits
                  dest!: graph_ofD)
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: graph_ofD
                 split: if_split_asm)
  apply (erule rtranclE)
   apply (simp add: up_ucast_inj_eq)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (clarsimp simp: vs_refs_def
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits
                 dest!: graph_ofD)
 done

lemma set_asid_pool_unmap:
  "\<lbrace>[VSRef highbits None] \<rhd> poolptr\<rbrace>
     set_asid_pool poolptr (pool(lowbits := None))
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (ucast lowbits) (Some AASIDPool),
                   VSRef highbits None] \<rhd> x) s\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup1_def obj_at_def up_ucast_inj_eq)
  apply (fastforce simp: vs_refs_def up_ucast_inj_eq
                 dest!: graph_ofD)
  done

lemma delete_asid_unmapped[wp]:
  "\<lbrace>\<top>\<rbrace>
      delete_asid asid pd
   \<lbrace>\<lambda>rv s.  \<not> ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                VSRef (ucast (asid_high_bits_of asid)) None]  \<rhd> pd) s\<rbrace>"
  apply (simp add: delete_asid_def
                   mask_asid_low_bits_ucast_ucast
             cong: option.case_cong)
  apply (wp set_asid_pool_unmap load_hw_asid_wp | wpc)+
  apply simp
  apply (intro allI conjI impI)
    apply (fastforce simp: vs_lookup_def vs_asid_refs_def up_ucast_inj_eq
                   dest!: graph_ofD vs_lookup1_rtrancl_iterations
                          vs_lookup1D)
   apply (erule vs_lookup_atI)
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def up_ucast_inj_eq
                 dest!: graph_ofD vs_lookup1_rtrancl_iterations
                        vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def up_ucast_inj_eq
                 dest!: graph_ofD)
  done

lemma set_pt_tcb_at:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pt a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: simpler_set_pt_def valid_def obj_at_def)

lemma set_pd_tcb_at:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pd a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: simpler_set_pd_def valid_def obj_at_def)

lemma set_vcpu_tcb_at_arch: (* generalise? this holds except when the ko is a vcpu *)
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace>
      set_vcpu p v
        \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (wp set_vcpu_nonvcpu_at; auto)

crunch vcpu_switch
  for tcb_at_arch: "\<lambda>s. P (ko_at (TCB tcb) t s)"
    (simp: crunch_simps when_def
       wp: crunch_wps set_vcpu_tcb_at_arch)

crunch unmap_page
  for tcb_at_arch: "\<lambda>s. P (ko_at (TCB tcb) t s)"
    (simp: crunch_simps wp: crunch_wps set_pt_tcb_at set_pd_tcb_at ignore: set_object)

lemmas unmap_page_tcb_at = unmap_page_tcb_at_arch

lemma unmap_page_tcb_cap_valid:
  "\<lbrace>\<lambda>s. tcb_cap_valid cap r s\<rbrace>
    unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>rv s. tcb_cap_valid cap r s\<rbrace>"
  apply (rule tcb_cap_valid_typ_st)
    apply wp
   apply (simp add: pred_tcb_at_def2)
  apply (wp unmap_page_tcb_at hoare_vcg_ex_lift hoare_vcg_all_lift)+
  done


lemma (* replaceable_cdt_update *)[simp,Finalise_AI_assms]:
  "replaceable (cdt_update f s) = replaceable s"
  by (fastforce simp: replaceable_def tcb_cap_valid_def)

lemma (* replaceable_revokable_update *)[simp,Finalise_AI_assms]:
  "replaceable (is_original_cap_update f s) = replaceable s"
  by (fastforce simp: replaceable_def is_final_cap'_def2 tcb_cap_valid_def)

lemma (* replaceable_more_update *) [simp,Finalise_AI_assms]:
  "replaceable (trans_state f s) sl cap cap' = replaceable s sl cap cap'"
  by (simp add: replaceable_def)

lemma (* obj_ref_ofI *) [Finalise_AI_assms]: "obj_refs cap = {x} \<Longrightarrow> obj_ref_of cap = x"
  by (case_tac cap, simp_all) (rename_tac arch_cap, case_tac arch_cap, simp_all)

lemma (* empty_slot_invs *) [Finalise_AI_assms]:
  "\<lbrace>\<lambda>s. invs s \<and> cte_wp_at (replaceable s sl cap.NullCap) sl s \<and>
        emptyable sl s \<and>
        (info \<noteq> NullCap \<longrightarrow> post_cap_delete_pre info ((caps_of_state s) (sl \<mapsto> NullCap)))\<rbrace>
     empty_slot sl info
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: empty_slot_def set_cdt_def bind_assoc cong: if_cong)
  apply (wp post_cap_deletion_invs)
        apply (simp add: invs_def valid_state_def valid_mdb_def2)
        apply (wp replace_cap_valid_pspace set_cap_caps_of_state2
                  replace_cap_ifunsafe get_cap_wp
                  set_cap_idle valid_irq_node_typ set_cap_typ_at
                  set_cap_irq_handlers set_cap_valid_arch_caps
                  set_cap_cap_refs_respects_device_region_NullCap
                  | simp add: trans_state_update[symmetric] del: trans_state_update fun_upd_apply split del: if_split )+
  apply (clarsimp simp: is_final_cap'_def2 simp del: fun_upd_apply)
  apply (clarsimp simp: conj_comms invs_def valid_state_def valid_mdb_def2)
  apply (subgoal_tac "mdb_empty_abs s")
   prefer 2
   apply (rule mdb_empty_abs.intro)
   apply (rule vmdb_abs.intro)
   apply (simp add: valid_mdb_def swp_def cte_wp_at_caps_of_state conj_comms)
  apply (clarsimp simp: untyped_mdb_def mdb_empty_abs.descendants mdb_empty_abs.no_mloop_n
                        valid_pspace_def cap_range_def)
  apply (clarsimp simp: untyped_inc_def mdb_empty_abs.descendants mdb_empty_abs.no_mloop_n)
  apply (simp add: ut_revocable_def cur_tcb_def valid_irq_node_def
                   no_cap_to_obj_with_diff_ref_Null)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_cte_at)
  apply (rule conjI)
   apply (clarsimp simp: irq_revocable_def)
  apply (rule conjI)
   apply (clarsimp simp: reply_master_revocable_def)
  apply (thin_tac "info \<noteq> NullCap \<longrightarrow> P info" for P)
  apply (rule conjI)
   apply (clarsimp simp: valid_machine_state_def)
  apply (rule conjI)
   apply (clarsimp simp:descendants_inc_def mdb_empty_abs.descendants)
  apply (rule conjI)
   apply (clarsimp simp: reply_mdb_def)
   apply (rule conjI)
    apply (unfold reply_caps_mdb_def)[1]
    apply (rule allEI, assumption)
    apply (fold reply_caps_mdb_def)[1]
    apply (case_tac "sl = ptr", simp)
    apply (simp add: fun_upd_def split del: if_split del: split_paired_Ex)
    apply (erule allEI, rule impI, erule(1) impE)
    apply (erule exEI)
    apply (simp, rule ccontr)
    apply (erule(5) emptyable_no_reply_cap)
    apply simp
   apply (unfold reply_masters_mdb_def)[1]
   apply (elim allEI)
   apply (clarsimp simp: mdb_empty_abs.descendants)
  apply (rule conjI)
   apply (simp add: valid_ioc_def)
  apply (rule conjI)
   apply (clarsimp simp: tcb_cap_valid_def
                  dest!: emptyable_valid_NullCapD)
  apply (rule conjI)
   apply (clarsimp simp: mdb_cte_at_def cte_wp_at_caps_of_state)
   apply (cases sl)
   apply (rule conjI, clarsimp)
    apply (subgoal_tac "cdt s \<Turnstile> (ab,bb) \<rightarrow> (ab,bb)")
     apply (simp add: no_mloop_def)
    apply (rule r_into_trancl)
    apply (simp add: cdt_parent_of_def)
   apply fastforce
  apply (clarsimp simp: cte_wp_at_caps_of_state replaceable_def
                        vs_cap_ref_simps table_cap_ref_simps
                   del: allI)
  apply (case_tac "is_final_cap' cap s")
   apply auto[1]
  apply (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state)
  done

lemma dom_tcb_cap_cases_lt_ARCH [Finalise_AI_assms]:
  "dom tcb_cap_cases = {xs. length xs = 3 \<and> unat (of_bl xs :: machine_word) < 5}"
  apply (rule set_eqI, rule iffI)
   apply clarsimp
   apply (simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1 split: if_split_asm)
  apply clarsimp
  apply (frule tcb_cap_cases_lt)
  apply (clarsimp simp: nat_to_cref_unat_of_bl')
  done

lemma (* unbind_notification_final *) [wp,Finalise_AI_assms]:
  "\<lbrace>is_final_cap' cap\<rbrace> unbind_notification t \<lbrace> \<lambda>rv. is_final_cap' cap\<rbrace>"
  unfolding unbind_notification_def
  apply (wp final_cap_lift thread_set_caps_of_state_trivial hoare_drop_imps
       | wpc | simp add: tcb_cap_cases_def)+
  done

lemma dissociate_vcpu_tcb_final_cap[wp]:
  "\<lbrace>is_final_cap' cap\<rbrace> dissociate_vcpu_tcb v t \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  by (wpsimp simp: is_final_cap'_def2 cte_wp_at_caps_of_state)

lemma prepare_thread_delete_final[wp]:
  "\<lbrace>is_final_cap' cap\<rbrace> prepare_thread_delete t \<lbrace> \<lambda>rv. is_final_cap' cap\<rbrace>"
  unfolding prepare_thread_delete_def
  apply (wp  hoare_drop_imps
       | wpc | clarsimp simp add: tcb_cap_cases_def)+
  done

lemma (* finalise_cap_cases1 *)[Finalise_AI_assms]:
  "\<lbrace>\<lambda>s. final \<longrightarrow> is_final_cap' cap s
         \<and> cte_wp_at ((=) cap) slot s\<rbrace>
     finalise_cap cap final
   \<lbrace>\<lambda>rv s. fst rv = cap.NullCap
         \<and> snd rv = (if final then cap_cleanup_opt cap else NullCap)
         \<and> (snd rv \<noteq> NullCap \<longrightarrow> is_final_cap' cap s)
     \<or>
       is_zombie (fst rv) \<and> is_final_cap' cap s
        \<and> snd rv = NullCap
        \<and> appropriate_cte_cap (fst rv) = appropriate_cte_cap cap
        \<and> cte_refs (fst rv) = cte_refs cap
        \<and> gen_obj_refs (fst rv) = gen_obj_refs cap
        \<and> obj_size (fst rv) = obj_size cap
        \<and> fst_cte_ptrs (fst rv) = fst_cte_ptrs cap
        \<and> vs_cap_ref cap = None\<rbrace>"
  apply (cases cap, simp_all split del: if_split cong: if_cong)
            apply ((wp suspend_final_cap[where sl=slot]
                      deleting_irq_handler_final[where slot=slot]
                      | simp add: o_def is_cap_simps fst_cte_ptrs_def
                                  dom_tcb_cap_cases_lt_ARCH tcb_cnode_index_def
                                  can_fast_finalise_def
                                  appropriate_cte_cap_def gen_obj_refs_def
                                  vs_cap_ref_def cap_cleanup_opt_def
                      | intro impI TrueI ext conjI)+)[11]
  apply (simp add: arch_finalise_cap_def split del: if_split)
  apply (rule hoare_pre)
   apply (wpsimp simp: cap_cleanup_opt_def arch_cap_cleanup_opt_def)+
  done

crunch dissociate_vcpu_tcb
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps unless_def assertE_def
        ignore: do_machine_op set_object) (* ARMHYP fix *)

crunch arch_finalise_cap
  for typ_at[wp,Finalise_AI_assms]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps unless_def assertE_def
        ignore: maskInterrupt set_object) (* ARMHYP fix *)

crunch prepare_thread_delete
  for typ_at[wp,Finalise_AI_assms]: "\<lambda>s. P (typ_at T p s)"

lemma vcpu_set_tcb_at[wp]: "\<lbrace>\<lambda>s. tcb_at p s\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_ s. tcb_at p s\<rbrace>"
  apply (simp add: tcb_at_typ)
  apply wp
  done

crunch dissociate_vcpu_tcb
  for tcb_at[wp]: "\<lambda>s. tcb_at p s"
  (wp: crunch_wps)

crunch prepare_thread_delete
  for tcb_at[wp]: "\<lambda>s. tcb_at p s"

lemma (* finalise_cap_new_valid_cap *)[wp,Finalise_AI_assms]:
  "\<lbrace>valid_cap cap\<rbrace> finalise_cap cap x \<lbrace>\<lambda>rv. valid_cap (fst rv)\<rbrace>"
  apply (cases cap, simp_all)
            apply (wp suspend_valid_cap prepare_thread_delete_typ_at
                     | simp add: o_def valid_cap_def cap_aligned_def
                                 valid_cap_Null_ext
                           split del: if_split
                     | clarsimp | rule conjI)+
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
  apply (wp|simp add: o_def valid_cap_def cap_aligned_def
                 split del: if_split|clarsimp|wpc)+
  done

lemma hoare_split: "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q r and Q' r\<rbrace>"
  by (auto simp: valid_def)

lemma get_vcpu_ko: "\<lbrace>Q\<rbrace> get_vcpu p \<lbrace>\<lambda>rv s. ko_at (ArchObj (VCPU rv)) p s \<and> Q s\<rbrace>"
  unfolding get_vcpu_def
  apply wpsimp
   apply (rule hoare_allI)
   apply (subst eq_commute)
   apply (subst (2) eq_commute)
   apply clarsimp
   apply (rule hoare_drop_imp)+
   apply (subst conj_commute)
   apply (wp get_object_sp[simplified pred_conj_def], simp)
  done

lemma vcpu_invalidate_tcbs_inv[wp]:
  "\<lbrace>obj_at (\<lambda>tcb. \<exists>t'. tcb = TCB t' \<and> P t') t\<rbrace>
    vcpu_invalidate_active \<lbrace>\<lambda>rv. obj_at (\<lambda>tcb. \<exists>t'. tcb = TCB t' \<and> P t') t\<rbrace>"
  unfolding vcpu_invalidate_active_def vcpu_disable_def by wpsimp

lemma sym_refs_vcpu_None:
  assumes sym_refs: "sym_refs (state_hyp_refs_of s)"
  assumes tcb: "ko_at (TCB tcb) t s" "tcb_vcpu (tcb_arch tcb) = Some vr"
  shows "sym_refs (state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_arch := tcb_vcpu_update Map.empty (tcb_arch tcb)\<rparr>),
                                       vr \<mapsto> ArchObj (VCPU (vcpu_tcb_update Map.empty v)))\<rparr>))"
    (is "sym_refs (state_hyp_refs_of ?s')")
proof -
  from tcb
  have t: "state_hyp_refs_of s t = {(vr,TCBHypRef)}"
    by (simp add: state_hyp_refs_of_def obj_at_def)
  moreover
  from t
  have "(t,HypTCBRef) \<in> state_hyp_refs_of s vr"
    using sym_refsD [of vr _ _ t, OF _ sym_refs] by auto
  hence vr: "state_hyp_refs_of s vr = {(t,HypTCBRef)}"
    by (auto simp: state_hyp_refs_of_def hyp_refs_of_def tcb_vcpu_refs_def vcpu_tcb_refs_def
                   refs_of_def refs_of_a_def
            split: option.splits kernel_object.splits arch_kernel_obj.splits)
  moreover
  from sym_refs vr
  have "\<And>x r rt. \<lbrakk> (r, rt) \<in> state_hyp_refs_of s x; x \<noteq> t \<rbrakk> \<Longrightarrow> r \<noteq> vr"
    by (auto dest: sym_refsD)
  moreover
  from sym_refs t
  have "\<And>x r rt. \<lbrakk> (r, rt) \<in> state_hyp_refs_of s x; x \<noteq> vr \<rbrakk> \<Longrightarrow> r \<noteq> t"
    by (auto dest: sym_refsD)
  ultimately
  have "sym_refs ((state_hyp_refs_of s) (vr := {}, t := {}))"
    using sym_refs unfolding sym_refs_def by (clarsimp simp: split_def)
  moreover
  have "state_hyp_refs_of ?s' = (state_hyp_refs_of s) (vr := {}, t := {})"
    unfolding state_hyp_refs_of_def by (rule ext) simp
  ultimately
  show ?thesis by simp
qed

lemma dissociate_vcpu_tcb_sym_refs_hyp[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace> dissociate_vcpu_tcb vr t \<lbrace>\<lambda>rv s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: dissociate_vcpu_tcb_def arch_get_sanitise_register_info_def)
  apply (wp arch_thread_set_wp set_vcpu_wp)
       apply (rule_tac Q'="\<lambda>_ s. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_vcpu (tcb_arch tcb) = Some vr) t s
                             \<and> sym_refs (state_hyp_refs_of s)" in hoare_post_imp)
        apply clarsimp
        apply (clarsimp simp: get_tcb_Some_ko_at obj_at_def sym_refs_vcpu_None split: if_splits)
       apply (wp get_vcpu_wp arch_thread_get_wp)+
  apply clarsimp
  apply (rule conjI, clarsimp simp: obj_at_def)
  apply clarsimp
  apply (clarsimp simp: get_tcb_Some_ko_at obj_at_def sym_refs_vcpu_None split: if_splits)
  done

crunch dissociate_vcpu_tcb
  for valid_objs[wp]: "valid_objs"
  (wp: crunch_wps simp: crunch_simps valid_obj_def valid_vcpu_def ignore: arch_thread_set)

lemma set_vcpu_unlive_hyp[wp]:
 "\<lbrace>\<lambda>s. vr \<noteq> t \<longrightarrow> obj_at (Not \<circ> hyp_live) t s\<rbrace>
  set_vcpu vr (vcpu_tcb_update Map.empty v) \<lbrace>\<lambda>rv. obj_at (Not \<circ> hyp_live) t\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp)
  apply (clarsimp simp: obj_at_def hyp_live_def arch_live_def)
  done

lemma as_user_unlive_hyp[wp]:
  "\<lbrace>obj_at (Not \<circ> hyp_live) vr\<rbrace> as_user t f \<lbrace>\<lambda>_. obj_at (Not \<circ> hyp_live) vr\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_def hyp_live_def get_tcb_Some_ko_at arch_tcb_context_set_def)

lemma dissociate_vcpu_tcb_unlive_hyp_vr[wp]:
  "\<lbrace>\<top>\<rbrace> dissociate_vcpu_tcb vr t \<lbrace> \<lambda>_. obj_at (Not \<circ> hyp_live) vr\<rbrace>"
  unfolding dissociate_vcpu_tcb_def arch_get_sanitise_register_info_def
  by (wpsimp wp: get_vcpu_wp hoare_vcg_const_imp_lift hoare_drop_imps)

lemma dissociate_vcpu_tcb_unlive_hyp_t[wp]:
  "\<lbrace>\<top>\<rbrace> dissociate_vcpu_tcb vr t \<lbrace> \<lambda>_. obj_at (Not \<circ> hyp_live) t\<rbrace>"
  unfolding dissociate_vcpu_tcb_def arch_get_sanitise_register_info_def
  by (wpsimp wp: hoare_vcg_const_imp_lift hoare_drop_imps get_vcpu_wp)

lemma set_vcpu_unlive0[wp]:
 "\<lbrace>obj_at (Not \<circ> live0) t\<rbrace> set_vcpu vr v \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) t\<rbrace>"
  by (wpsimp wp: set_vcpu_wp simp: obj_at_def)

lemma as_user_unlive0[wp]:
  "\<lbrace>obj_at (Not \<circ> live0) vr\<rbrace> as_user t f \<lbrace>\<lambda>_. obj_at (Not \<circ> live0) vr\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_def live0_def get_tcb_Some_ko_at arch_tcb_context_set_def)

lemma o_def_not: "obj_at (\<lambda>a. \<not> P a) t s =  obj_at (Not o P) t s"
  by (simp add: obj_at_def)

crunch dissociate_vcpu_tcb
  for unlive0: "obj_at (Not \<circ> live0) t"
  (wp: crunch_wps simp: o_def_not ignore: arch_thread_set)

lemma set_vcpu_if_live_then_nonz_cap_same_refs:
  "\<lbrace>if_live_then_nonz_cap and obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of (ArchObj (VCPU v))) p\<rbrace>
     set_vcpu p v \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_vcpu_def)
  including unfold_objects
  apply (wpsimp wp: set_object_iflive[THEN hoare_set_object_weaken_pre]
              simp: a_type_def live_def hyp_live_def arch_live_def)
  apply (rule if_live_then_nonz_capD; simp)
  apply (clarsimp simp: live_def hyp_live_def arch_live_def,
         clarsimp simp: vcpu_tcb_refs_def split: option.splits)
  done

lemma vgic_update_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> vgic_update vcpuptr f \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  unfolding vgic_update_def vcpu_update_def
  apply (wp set_vcpu_if_live_then_nonz_cap_same_refs get_vcpu_wp)
  apply (clarsimp simp: obj_at_def)
  done

lemma vcpu_save_reg_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> vcpu_save_reg vcpuptr r \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  unfolding vcpu_save_reg_def vcpu_update_def
  apply (wpsimp wp: set_vcpu_if_live_then_nonz_cap_same_refs get_vcpu_wp
                    hoare_vcg_imp_lift hoare_vcg_all_lift)
  apply (simp add: obj_at_def)
  done

lemma vcpu_update_regs_if_live_then_nonz_cap[wp]:
  "vcpu_update vcpu_ptr (vcpu_regs_update f) \<lbrace>if_live_then_nonz_cap\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp wp: set_vcpu_if_live_then_nonz_cap_same_refs get_vcpu_wp)
     (simp add: obj_at_def)

lemma vcpu_write_if_live_then_nonz_cap[wp]:
  "vcpu_write_reg vcpu_ptr reg val \<lbrace>if_live_then_nonz_cap\<rbrace>"
  unfolding vcpu_write_reg_def by (wpsimp cong: vcpu.fold_congs)

lemma vcpu_update_vtimer_if_live_then_nonz_cap[wp]:
  "vcpu_update vcpu_ptr (vcpu_vtimer_update f) \<lbrace>if_live_then_nonz_cap\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp wp: set_vcpu_if_live_then_nonz_cap_same_refs get_vcpu_wp)
     (simp add: obj_at_def)

crunch vcpu_disable, vcpu_invalidate_active
  for if_live_then_nonz_cap[wp]: if_live_then_nonz_cap
  (ignore: vcpu_update)

lemma dissociate_vcpu_tcb_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> dissociate_vcpu_tcb vr t \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  unfolding dissociate_vcpu_tcb_def arch_get_sanitise_register_info_def
  by (wpsimp wp: get_vcpu_wp arch_thread_get_wp hoare_drop_imps)

lemma vcpu_invalidate_active_ivs[wp]: "\<lbrace>invs\<rbrace> vcpu_invalidate_active \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding vcpu_invalidate_active_def
  by (wpsimp simp: cur_vcpu_at_def | strengthen invs_current_vcpu_update')+

crunch dissociate_vcpu_tcb
  for cur_tcb[wp]: "cur_tcb"
  (wp: crunch_wps)

crunch dissociate_vcpu_tcb
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps)

crunch dissociate_vcpu_tcb
  for cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
  (wp: crunch_wps cap_refs_respects_device_region_dmo
   simp: crunch_simps read_cntpct_def get_cntv_off_64_def get_cntv_cval_64_def maskInterrupt_def
   ignore: do_machine_op)

crunch dissociate_vcpu_tcb
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  (wp: crunch_wps)

crunch dissociate_vcpu_tcb
  for cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
  (wp: crunch_wps simp: crunch_simps)

crunch dissociate_vcpu_tcb
  for pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  (wp: crunch_wps)

lemma valid_asid_map_arm_current_vcpu_update[simp]:
  "valid_asid_map (s\<lparr>arch_state := arm_current_vcpu_update f (arch_state s)\<rparr>) = valid_asid_map s"
  by (simp add: valid_asid_map_def vspace_at_asid_def vs_lookup_def vs_lookup1_def)

crunch dissociate_vcpu_tcb
  for valid_asid_map[wp]: "valid_asid_map"
  (wp: crunch_wps)

crunch dissociate_vcpu_tcb
  for equal_kernel_mappings[wp]: "equal_kernel_mappings"
  (wp: crunch_wps)

crunch dissociate_vcpu_tcb
  for valid_kernel_mappings[wp]: "valid_kernel_mappings"
  (wp: crunch_wps)

crunch dissociate_vcpu_tcb
  for valid_arch_caps[wp]: "valid_arch_caps"
  (wp: crunch_wps)

crunch dissociate_vcpu_tcb
  for valid_vspace_objs[wp]: "valid_vspace_objs"
  (wp: crunch_wps)

crunch dissociate_vcpu_tcb
  for valid_irq_handlers[wp]: "valid_irq_handlers"
  (wp: crunch_wps ignore: do_machine_op)

lemma as_user_valid_irq_node[wp]:
  "\<lbrace>valid_irq_node\<rbrace> as_user t f \<lbrace>\<lambda>_. valid_irq_node\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_irq_node_def get_tcb_Some_ko_at obj_at_def is_cap_table)
  by (metis kernel_object.distinct(1) option.inject)

crunch dissociate_vcpu_tcb
  for valid_irq_node[wp]: "valid_irq_node"
  (wp: crunch_wps)

lemma dmo_valid_irq_states:
  "(\<And>P. \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_masks s)\<rbrace>) \<Longrightarrow>
    \<lbrace>valid_irq_states\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_irq_states\<rbrace>"
  unfolding valid_irq_states_def do_machine_op_def
  apply (rule hoare_lift_Pf [where f="\<lambda>s. irq_masks (machine_state s)"])
   apply wpsimp+
  apply (erule use_valid; assumption)
  done

lemma dmo_machine_state_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P (machine_state s)\<rbrace> do_machine_op f \<lbrace>\<lambda>rv s. Q rv (machine_state s)\<rbrace>"
  unfolding do_machine_op_def by wpsimp (erule use_valid; assumption)

lemma dmo_maskInterrupt_True_valid_irq_states[wp]:
  "do_machine_op (maskInterrupt True irq) \<lbrace>valid_irq_states\<rbrace>"
  unfolding valid_irq_states_def do_machine_op_def maskInterrupt_def
  apply wpsimp
  apply (erule use_valid)
   apply (wpsimp simp: valid_irq_masks_def)+
  done

crunch vcpu_save_reg, vgic_update, vcpu_disable
  for valid_irq_states[wp]: valid_irq_states
  and in_user_frame[wp]: "in_user_frame p"
  (wp: dmo_maskInterrupt_True_valid_irq_states dmo_valid_irq_states
   simp: get_cntv_off_64_def get_cntv_cval_64_def set_gic_vcpu_ctrl_hcr_def get_gic_vcpu_ctrl_hcr_def
         readVCPUHardwareReg_def writeVCPUHardwareReg_def setHCR_def setSCTLR_def getSCTLR_def
         isb_def dsb_def read_cntpct_def maskInterrupt_def check_export_arch_timer_def)

lemma dmo_writeVCPUHardwareReg_valid_machine_state[wp]:
  "do_machine_op (writeVCPUHardwareReg r v) \<lbrace>valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift writeVCPUHardwareReg_underlying_memory
                 dmo_machine_state_lift)

lemma dmo_check_export_arch_timer_valid_machine_state[wp]:
  "do_machine_op check_export_arch_timer \<lbrace>valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift dmo_machine_state_lift
                 check_export_arch_timer_underlying_memory)

crunch vgic_update, vcpu_update, vcpu_write_reg, vcpu_save_reg, save_virt_timer
  for in_user_frame[wp]: "in_user_frame p"
  and valid_machine_state[wp]: valid_machine_state
  and underlying_memory[wp]: "\<lambda>s. P (underlying_memory (machine_state s))"
  (simp: readVCPUHardwareReg_def read_cntpct_def get_cntv_off_64_def get_cntv_cval_64_def
   wp: writeVCPUHardwareReg_underlying_memory_pred dmo_machine_state_lift
       check_export_arch_timer_underlying_memory_pred
   ignore: do_machine_op)

lemma vcpu_disable_valid_machine_state[wp]:
  "\<lbrace>valid_machine_state\<rbrace> vcpu_disable vcpu_opt \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding vcpu_disable_def valid_machine_state_def
  by (wpsimp wp: dmo_machine_state_lift hoare_vcg_all_lift hoare_vcg_disj_lift
             simp: isb_def setHCR_def setSCTLR_def set_gic_vcpu_ctrl_hcr_def getSCTLR_def
                   get_gic_vcpu_ctrl_hcr_def dsb_def writeVCPUHardwareReg_def maskInterrupt_def)

lemma valid_arch_state_vcpu_update_str:
  "valid_arch_state s \<Longrightarrow> valid_arch_state (s\<lparr>arch_state := arm_current_vcpu_update Map.empty (arch_state s)\<rparr>)"
  by (simp add: valid_arch_state_def)

lemma valid_global_refs_vcpu_update_str:
  "valid_global_refs s \<Longrightarrow> valid_global_refs (s\<lparr>arch_state := arm_current_vcpu_update f (arch_state s)\<rparr>)"
  by (simp add: valid_global_refs_def global_refs_def)

lemma set_vcpu_None_valid_arch[wp]:
  "\<lbrace>valid_arch_state and (\<lambda>s. \<forall>a. arm_current_vcpu (arch_state s) \<noteq> Some (vr, a))\<rbrace>
  set_vcpu vr (vcpu_tcb_update Map.empty v) \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (wp set_vcpu_wp)
  apply (clarsimp simp: valid_arch_state_def)
  apply (rule conjI)
   apply (fastforce simp: valid_asid_table_def obj_at_def)
  apply (clarsimp simp: obj_at_def split: option.splits)
  done

lemma dissociate_vcpu_valid_arch[wp]:
  "\<lbrace>valid_arch_state\<rbrace> dissociate_vcpu_tcb vr t \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding dissociate_vcpu_tcb_def vcpu_invalidate_active_def arch_get_sanitise_register_info_def
  by (wpsimp wp: get_vcpu_wp arch_thread_get_wp
       | strengthen valid_arch_state_vcpu_update_str | wp (once) hoare_drop_imps)+

lemma as_user_valid_irq_states[wp]:
  "\<lbrace>valid_irq_states\<rbrace> as_user t f \<lbrace>\<lambda>rv. valid_irq_states\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: get_tcb_Some_ko_at obj_at_def valid_irq_states_def)

lemma as_user_ioc[wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (is_original_cap s)\<rbrace>"
  unfolding as_user_def by (wpsimp wp: set_object_wp)

lemma as_user_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> as_user t f \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  unfolding valid_ioc_def by (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift)

lemma dissociate_vcpu_tcb_invs[wp]: "\<lbrace>invs\<rbrace> dissociate_vcpu_tcb vr t \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (simp add: pred_conj_def)
  apply (rule hoare_vcg_conj_lift[rotated])+
  apply (wpsimp wp: weak_if_wp get_vcpu_wp arch_thread_get_wp as_user_only_idle
         | simp add: dissociate_vcpu_tcb_def vcpu_invalidate_active_def arch_get_sanitise_register_info_def
         | strengthen valid_arch_state_vcpu_update_str valid_global_refs_vcpu_update_str
         | simp add: vcpu_disable_def valid_global_vspace_mappings_def valid_global_objs_def
         | wp (once) hoare_drop_imps)+
  done

crunch vcpu_finalise
  for invs[wp]: invs
  (ignore: dissociate_vcpu_tcb)

lemma arch_finalise_cap_invs' [wp,Finalise_AI_assms]:
  "\<lbrace>invs and valid_cap (ArchObjectCap cap)\<rbrace>
     arch_finalise_cap cap final
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (wp unmap_page_invs | wpc)+
  apply (clarsimp simp: valid_cap_def cap_aligned_def)
  apply (auto simp: mask_def vmsz_aligned_def)
  done

lemma set_vcpu_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> set_vcpu vr (vcpu_tcb_update Map.empty v) \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) vr\<rbrace>"
  apply (wp set_vcpu_wp)
  apply (clarsimp simp: obj_at_def live_def hyp_live_def arch_live_def)
  done

lemma as_user_unlive[wp]:
  "\<lbrace>obj_at (Not \<circ> live) vr\<rbrace> as_user t f \<lbrace>\<lambda>_. obj_at (Not \<circ> live) vr\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_def live_def hyp_live_def get_tcb_Some_ko_at arch_tcb_context_set_def)


lemma dissociate_vcpu_tcb_unlive_v:
  "\<lbrace>\<top>\<rbrace> dissociate_vcpu_tcb vr t \<lbrace> \<lambda>_. obj_at (Not \<circ> live) vr\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  by (wpsimp wp: arch_thread_set_unlive_other get_vcpu_wp arch_thread_get_wp hoare_drop_imps
           simp:  bind_assoc)

lemma vcpu_finalise_unlive:
  "\<lbrace>\<top>\<rbrace> vcpu_finalise r \<lbrace> \<lambda>_. obj_at (Not \<circ> live) r \<rbrace>"
  apply (wpsimp simp: vcpu_finalise_def wp: dissociate_vcpu_tcb_unlive_v get_vcpu_wp)
  apply (auto simp: obj_at_def live_def hyp_live_def arch_live_def)
  done

lemma arch_finalise_cap_vcpu:
  notes strg = tcb_cap_valid_imp_NullCap
               vcpu_finalise_unlive[simplified o_def]
  notes simps = replaceable_def
                is_cap_simps vs_cap_ref_def
                no_cap_to_obj_with_diff_ref_Null o_def
  notes wps = hoare_drop_imp[where Q'="%_. is_final_cap' cap" for cap]
              valid_cap_typ
  shows
  "cap = VCPUCap r \<Longrightarrow> \<lbrace>\<lambda>s. s \<turnstile> cap.ArchObjectCap cap \<and>
          x = is_final_cap' (cap.ArchObjectCap cap) s \<and>
          pspace_aligned s \<and> valid_vspace_objs s \<and> valid_objs s \<and>
          valid_asid_table (arm_asid_table (arch_state s)) s\<rbrace>
     arch_finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) (cap.ArchObjectCap cap)\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
  apply (wp wps | simp add: simps reachable_pg_cap_def| wpc | strengthen strg)+
  done


lemma obj_at_not_live_valid_arch_cap_strg [Finalise_AI_assms]:
  "(s \<turnstile> ArchObjectCap cap \<and> aobj_ref cap = Some r \<and> \<not> typ_at (AArch AVCPU) r s)
        \<longrightarrow> obj_at (\<lambda>ko. \<not> live ko) r s"
  by (clarsimp simp: live_def valid_cap_def obj_at_def a_type_arch_live valid_cap_simps
                     hyp_live_def arch_live_def
              split: arch_cap.split_asm if_splits)

lemma obj_at_not_live_valid_arch_cap_strg' [Finalise_AI_assms]:
  "(s \<turnstile> ArchObjectCap cap \<and> aobj_ref cap = Some r \<and> cap \<noteq> VCPUCap r)
        \<longrightarrow> obj_at (\<lambda>ko. \<not> live ko) r s"
  by (clarsimp simp: live_def valid_cap_def obj_at_def
                     hyp_live_def arch_live_def
              split: arch_cap.split_asm if_splits)

lemma arch_finalise_cap_replaceable1:
  notes strg = tcb_cap_valid_imp_NullCap
               obj_at_not_live_valid_arch_cap_strg[where cap=cap]
  notes simps = replaceable_def and_not_not_or_imp
                vs_lookup_pages_eq_at[THEN fun_cong, symmetric]
                vs_lookup_pages_eq_ap[THEN fun_cong, symmetric]
                is_cap_simps vs_cap_ref_def
                no_cap_to_obj_with_diff_ref_Null o_def
  notes wps = hoare_drop_imp[where Q'="%_. is_final_cap' cap" for cap]
              unmap_page_table_unmapped3 valid_cap_typ
  assumes X: "\<forall>r. cap \<noteq> VCPUCap r"
  shows
    "\<lbrace>\<lambda>s. s \<turnstile> cap.ArchObjectCap cap \<and>
          x = is_final_cap' (cap.ArchObjectCap cap) s \<and>
          pspace_aligned s \<and> valid_vspace_objs s \<and> valid_objs s \<and>
          valid_asid_table (arm_asid_table (arch_state s)) s\<rbrace>
     arch_finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) (cap.ArchObjectCap cap)\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (simp add: simps split: option.splits vmpage_size.splits)
   apply (wp wps
          | strengthen strg
          | simp add: simps reachable_pg_cap_def live_def
          | wpc)+
     (* unmap_page case is a bit unpleasant *)
     apply (strengthen cases_conj_strg[where P="\<not> is_final_cap' cap s" for cap s, simplified])
     apply (rule hoare_post_imp, clarsimp split: vmpage_size.split, assumption)
     apply (simp add: vspace_bits_defs)
     apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift hoare_vcg_const_imp_lift
               unmap_page_tcb_cap_valid unmap_page_page_unmapped
                   unmap_page_section_unmapped)[1]
    apply (wp wps
           | strengthen strg imp_and_strg tcb_cap_valid_imp_NullCap
           | simp add: simps is_master_reply_cap_def reachable_pg_cap_def
           | wpc)+
  apply (intro conjI; clarsimp split: cap.splits arch_cap.splits vmpage_size.splits)
  by (auto simp: valid_cap_def obj_at_def simps is_master_reply_cap_def
                    a_type_def data_at_def vspace_bits_defs X
             elim!: tcb_cap_valid_imp_NullCap[rule_format, rotated]
             split: cap.splits arch_cap.splits vmpage_size.splits)


lemma (* deleting_irq_handler_slot_not_irq_node *)[Finalise_AI_assms]:
  "\<lbrace>if_unsafe_then_cap and valid_global_refs
           and cte_wp_at (\<lambda>cp. cap_irqs cp \<noteq> {}) sl\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv s. (interrupt_irq_node s irq, []) \<noteq> sl\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply wp
  apply clarsimp
  apply (drule(1) if_unsafe_then_capD)
   apply clarsimp
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (drule cte_refs_obj_refs_elem)
  apply (erule disjE)
   apply simp
   apply (drule(1) valid_global_refsD[OF _ caps_of_state_cteD])
    prefer 2
    apply (erule notE, simp add: cap_range_def, erule disjI2)
   apply (simp add: global_refs_def)
  apply (clarsimp simp: appropriate_cte_cap_def split: cap.split_asm)
  done

lemma no_cap_to_obj_with_diff_ref_finalI_ARCH[Finalise_AI_assms]:
  "\<lbrakk> cte_wp_at ((=) cap) p s; is_final_cap' cap s;
            obj_refs cap' = obj_refs cap \<rbrakk>
      \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' {p} s"
  apply (case_tac "obj_refs cap = {}")
   apply (case_tac "cap_irqs cap = {}")
    apply (case_tac "arch_gen_refs cap = {}")
     apply (simp add: is_final_cap'_def)
     apply (case_tac cap, simp_all add: gen_obj_refs_def)
    apply ((clarsimp simp add: no_cap_to_obj_with_diff_ref_def
                              cte_wp_at_caps_of_state
                              vs_cap_ref_def
                       dest!: obj_ref_none_no_asid[rule_format])+)[2]
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        is_final_cap'_def2
              simp del: split_paired_All)
  apply (frule_tac x=p in spec)
  apply (drule_tac x="(a, b)" in spec)
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        gen_obj_refs_Int)
  done

lemma (* suspend_no_cap_to_obj_ref *)[wp,Finalise_AI_assms]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (simp add: no_cap_to_obj_with_diff_ref_def
                   cte_wp_at_caps_of_state)
  apply (wp suspend_caps_of_state)
  apply (clarsimp simp: table_cap_ref_simps
                 dest!: obj_ref_none_no_asid[rule_format])
  done

lemma dissociate_vcpu_tcb_no_cap_to_obj_ref[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     dissociate_vcpu_tcb v t
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  by (wpsimp simp: no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state)

lemma prepare_thread_delete_no_cap_to_obj_ref[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     prepare_thread_delete t
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  unfolding prepare_thread_delete_def by wpsimp

lemma prepare_thread_delete_unlive_hyp:
  "\<lbrace>\<top>\<rbrace> prepare_thread_delete ptr \<lbrace>\<lambda>rv. obj_at (Not \<circ> hyp_live) ptr\<rbrace>"
  apply (simp add: prepare_thread_delete_def)
  apply (wpsimp wp: hoare_vcg_imp_lift arch_thread_get_wp)
  apply (clarsimp simp: obj_at_def is_tcb_def hyp_live_def)
  done

lemma prepare_thread_delete_unlive0:
  "\<lbrace>obj_at (Not \<circ> live0) ptr\<rbrace> prepare_thread_delete ptr \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) ptr\<rbrace>"
  apply (simp add: prepare_thread_delete_def set_thread_state_def set_object_def)
  apply (wpsimp wp: dissociate_vcpu_tcb_unlive0| simp only: obj_at_exst_update)+
  done

lemma prepare_thread_delete_unlive[wp]:
  "\<lbrace>obj_at (Not \<circ> live0) ptr\<rbrace> prepare_thread_delete ptr \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (rule_tac Q'="\<lambda>rv. obj_at (Not \<circ> live0) ptr and obj_at (Not \<circ> hyp_live) ptr" in hoare_strengthen_post)
  apply (wpsimp wp: hoare_vcg_conj_lift prepare_thread_delete_unlive_hyp prepare_thread_delete_unlive0)+
  apply (clarsimp simp: obj_at_def, case_tac ko, simp_all add: is_tcb_def live_def arch_tcb_live_def)
  done

lemma arch_finalise_cap_replaceable:
  shows
    "\<lbrace>\<lambda>s. s \<turnstile> cap.ArchObjectCap cap \<and>
          x = is_final_cap' (cap.ArchObjectCap cap) s \<and>
          pspace_aligned s \<and> valid_vspace_objs s \<and> valid_objs s \<and>
          valid_asid_table (arm_asid_table (arch_state s)) s\<rbrace>
     arch_finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) (cap.ArchObjectCap cap)\<rbrace>"
  by (cases cap; simp add: arch_finalise_cap_vcpu arch_finalise_cap_replaceable1)

lemma finalise_cap_replaceable [Finalise_AI_assms]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s \<and> valid_mdb s
        \<and> cte_wp_at ((=) cap) sl s \<and> valid_objs s \<and> sym_refs (state_refs_of s)
        \<and> (cap_irqs cap \<noteq> {} \<longrightarrow> if_unsafe_then_cap s \<and> valid_global_refs s)
        \<and> (is_arch_cap cap \<longrightarrow> pspace_aligned s \<and>
                               valid_vspace_objs s \<and>
                               valid_arch_state s \<and>
                               valid_arch_caps s)\<rbrace>
     finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) cap\<rbrace>"
  apply (cases "is_arch_cap cap")
   apply (clarsimp simp: is_cap_simps)
   apply (wp arch_finalise_cap_replaceable)
   apply (clarsimp simp: replaceable_def reachable_pg_cap_def
                         o_def cap_range_def valid_arch_state_def
                         ran_tcb_cap_cases is_cap_simps
                         gen_obj_refs_subset vs_cap_ref_def
                         all_bool_eq)
  by (cases cap;
        simp add: replaceable_def reachable_pg_cap_def is_arch_cap_def
             split del: if_split;
        ((wp suspend_unlive[unfolded o_def]
             suspend_final_cap[where sl=sl]
             prepare_thread_delete_unlive[unfolded o_def]
             unbind_maybe_notification_not_bound
             get_simple_ko_ko_at unbind_notification_valid_objs
          | clarsimp simp: o_def dom_tcb_cap_cases_lt_ARCH
                           ran_tcb_cap_cases is_cap_simps
                           cap_range_def unat_of_bl_length
                           can_fast_finalise_def
                           gen_obj_refs_subset
                           vs_cap_ref_def
                           valid_ipc_buffer_cap_def
                     dest!: tcb_cap_valid_NullCapD
                     split: Structures_A.thread_state.split_asm
          | simp cong: conj_cong
          | simp cong: rev_conj_cong add: no_cap_to_obj_with_diff_ref_Null
          | (strengthen tcb_cap_valid_imp_NullCap tcb_cap_valid_imp', wp)
          | rule conjI
          | erule cte_wp_at_weakenE tcb_cap_valid_imp'[rule_format, rotated -1]
          | erule(1) no_cap_to_obj_with_diff_ref_finalI_ARCH
          | (wp (once) hoare_drop_imps,
                     wp (once) cancel_all_ipc_unlive[unfolded o_def]
                    cancel_all_signals_unlive[unfolded o_def])
          | ((wp (once) hoare_drop_imps)?,
             (wp (once) hoare_drop_imps)?,
             wp (once) deleting_irq_handler_empty)
          | wpc
          | simp add: valid_cap_simps is_nondevice_page_cap_simps)+))

lemma (* deleting_irq_handler_cte_preserved *)[Finalise_AI_assms]:
  assumes x: "\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap"
  shows "\<lbrace>cte_wp_at P p\<rbrace> deleting_irq_handler irq \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_cte_wp_at_preserved | simp add: x)+
  done

crunch dissociate_vcpu_tcb
  for cte_wp_at[wp,Finalise_AI_assms]: "\<lambda>s. P (cte_wp_at P' p s)"
  (simp: crunch_simps assertE_def wp: crunch_wps set_object_cte_at)

crunch prepare_thread_delete
  for cte_wp_at[wp,Finalise_AI_assms]: "\<lambda>s. P (cte_wp_at P' p s)"
  (simp: crunch_simps assertE_def wp: crunch_wps set_object_cte_at)

crunch arch_finalise_cap
  for cte_wp_at[wp,Finalise_AI_assms]: "\<lambda>s. P (cte_wp_at P' p s)"
  (simp: crunch_simps assertE_def wp: crunch_wps set_object_cte_at)
end

interpretation Finalise_AI_1?: Finalise_AI_1
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_assms)?)
  qed

context Arch begin arch_global_naming

lemma fast_finalise_replaceable[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s
     \<and> cte_wp_at ((=) cap) sl s \<and> valid_asid_table (arm_asid_table (arch_state s)) s
     \<and> valid_mdb s \<and> valid_objs s \<and> sym_refs (state_refs_of s)\<rbrace>
     fast_finalise cap x
   \<lbrace>\<lambda>rv s. cte_wp_at (replaceable s sl cap.NullCap) sl s\<rbrace>"
  apply (cases "cap_irqs cap = {}")
   apply (simp add: fast_finalise_def2)
   apply wp
    apply (rule hoare_strengthen_post)
     apply (rule hoare_vcg_conj_lift)
      apply (rule finalise_cap_replaceable[where sl=sl])
     apply (rule finalise_cap_equal_cap[where sl=sl])
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply wp
   apply (clarsimp simp: is_cap_simps can_fast_finalise_def)
  apply (clarsimp simp: cap_irqs_def cap_irq_opt_def split: cap.split_asm)
  done

lemma (* cap_delete_one_invs *) [Finalise_AI_assms,wp]:
  "\<lbrace>invs and emptyable ptr\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def is_final_cap_def)
  apply (rule hoare_pre)
  apply (wp empty_slot_invs get_cap_wp)
  apply clarsimp
  apply (drule cte_wp_at_valid_objs_valid_cap, fastforce+)
  done

end

interpretation Finalise_AI_2?: Finalise_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_assms)?)
  qed

context Arch begin arch_global_naming

crunch
  vcpu_update, vgic_update, vcpu_disable, vcpu_restore, vcpu_save_reg_range, vgic_update_lr,
  vcpu_save, vcpu_switch
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps subset_refl)

crunch prepare_thread_delete
  for irq_node[Finalise_AI_assms,wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

crunch arch_finalise_cap
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps wp: crunch_wps)

crunch
  delete_asid_pool, delete_asid, unmap_page_table, unmap_page, vcpu_invalidate_active
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"
  (simp: crunch_simps wp: crunch_wps test)

crunch arch_finalise_cap
  for pred_tcb_at[wp_unsafe]: "pred_tcb_at proj P t"
  (simp: crunch_simps wp: crunch_wps)

lemma tcb_cap_valid_pagetable:
  "tcb_cap_valid (ArchObjectCap (PageTableCap word (Some v))) slot
    = tcb_cap_valid (ArchObjectCap (PageTableCap word None)) slot"
  apply (rule ext)
  apply (simp add: tcb_cap_valid_def tcb_cap_cases_def is_nondevice_page_cap_arch_def
                   is_cap_simps valid_ipc_buffer_cap_def is_nondevice_page_cap_simps
                   is_valid_vtable_root_def
            split: Structures_A.thread_state.split)
  done


lemma store_pde_unmap_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table {}) word s\<rbrace>
    store_pde pd_slot InvalidPDE
   \<lbrace>\<lambda>rv s. obj_at (empty_table {}) word s\<rbrace>"
  apply (clarsimp simp: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def empty_table_def pde_ref_def valid_pde_mappings_def)
  done

crunch find_free_hw_asid, store_hw_asid, load_hw_asid, set_vm_root_for_flush, page_table_mapped, invalidate_tlb_by_asid
  for empty[wp]: "\<lambda>s. P (obj_at (empty_table {}) word s)"

lemma set_vcpu_empty[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (empty_table {}) word s)\<rbrace> set_vcpu p v \<lbrace>\<lambda>_ s. P (obj_at (empty_table {}) word s)\<rbrace>"
  apply (rule set_vcpu.vsobj_at)
  apply (clarsimp simp: vspace_obj_pred_def empty_table_def
                 split: kernel_object.splits arch_kernel_obj.splits)
  done

crunch
  vcpu_update, vgic_update, vcpu_disable, vcpu_restore, vcpu_save_reg_range, vgic_update_lr,
  vcpu_save, vcpu_switch
  for empty[wp]: "\<lambda>s. P (obj_at (empty_table {}) word s)"
  (wp: crunch_wps subset_refl)

lemma store_pte_unmap_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table {}) word s\<rbrace>
    store_pte xa InvalidPTE
   \<lbrace>\<lambda>rv s. obj_at (empty_table {}) word s\<rbrace>"
  apply (wp get_object_wp | simp add: store_pte_def set_pt_def set_object_def)+
  apply (clarsimp simp: obj_at_def empty_table_def)
  done

crunch invalidate_tlb_by_asid
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"

lemma invalidate_tlb_by_asid_pspace_aligned:
  "\<lbrace>pspace_aligned\<rbrace> invalidate_tlb_by_asid aa \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: invalidate_tlb_by_asid_def load_hw_asid_def | wp | wpc)+
  done

crunch invalidate_tlb_by_asid, page_table_mapped
  for cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"

lemma flush_table_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table {}) word s\<rbrace>
    flush_table ac aa b word
   \<lbrace>\<lambda>rv s. obj_at (empty_table {}) word s\<rbrace>"
  apply (clarsimp simp: flush_table_def set_vm_root_def)
  apply (wp do_machine_op_obj_at arm_context_switch_P_obj_at whenE_wp hoare_drop_imp
    | wpc
    | simp
    | wps)+
  apply (rename_tac pd x y)
  apply (rule_tac Q="\<lambda>pd' s.
              (if pd \<noteq> pd'
               then (\<lambda>s. obj_at
                         (empty_table {}) word
                         s)
               else (\<lambda>_. True))
               s \<and>
              (if pd \<noteq> pd' then \<lambda>s. True
               else (\<lambda>s. obj_at
                         (empty_table {}) word
                         s))
               s"
    and Q'="\<lambda>_ s. obj_at (empty_table {}) word s"
    in hoare_strengthen_postE_R)
  prefer 2 apply simp
  apply (wp find_pd_for_asid_inv mapM_wp
    | simp
    | wpc
    | rule_tac Q'="\<lambda>_ s. obj_at (empty_table {}) word s" in hoare_strengthen_post)+
  done

lemma unmap_page_table_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table {}) word s\<rbrace>
    unmap_page_table aa b word
   \<lbrace>\<lambda>rv s. obj_at (empty_table {}) word s\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (wp store_pde_unmap_empty flush_table_empty page_table_mapped_empty | simp | wpc)+
  done

lemma mapM_x_store_pte_valid_vspace_objs:
  "\<lbrace>invs and (\<lambda>s. \<exists>p' cap. caps_of_state s p' = Some cap \<and> is_pt_cap cap \<and>
    (\<forall>x \<in> set pteptrs. x && ~~ mask pt_bits \<in> obj_refs cap)) \<rbrace>
    mapM_x (\<lambda>p. store_pte p InvalidPTE) pteptrs
   \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (rule hoare_strengthen_post, rule mapM_x_wp')
   apply wp
   apply (fastforce simp: is_pt_cap_def)+
  done

lemma mapM_x_swp_store_empty_table_set:
  "\<lbrace>page_table_at p
    and pspace_aligned
    and K ((UNIV :: (9 word) set) \<subseteq> (\<lambda>sl. ucast ((sl && mask pt_bits) >> 3)) ` set slots
                       \<and> (\<forall>x\<in>set slots. x && ~~ mask pt_bits = p))\<rbrace>
    mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace>\<lambda>rv s. obj_at (empty_table (S s)) p s\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_swp_store_empty_table)
  apply (clarsimp simp: obj_at_def empty_table_def)
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits option.splits)
  apply (clarsimp simp add: valid_pde_mappings_def pde_ref_def)
  done

definition
  replaceable_or_arch_update
where
  "replaceable_or_arch_update \<equiv> \<lambda>s slot cap cap'.
   if is_pg_cap cap then is_arch_update cap cap' \<and>
        (\<forall>vref. vs_cap_ref cap' = Some vref \<longrightarrow>
          vs_cap_ref cap = Some vref \<and>
          obj_refs cap = obj_refs cap' \<or>
          (\<forall>oref\<in>obj_refs cap'. \<not> (vref \<unrhd> oref) s))
   else replaceable s slot cap cap'"

lemma is_final_cap_pt_asid_eq:
  "is_final_cap' (ArchObjectCap (PageTableCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PageTableCap p x)) s"
  apply (clarsimp simp: is_final_cap'_def gen_obj_refs_def)
  done

lemma is_final_cap_pd_asid_eq:
  "is_final_cap' (ArchObjectCap (PageDirectoryCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PageDirectoryCap p x)) s"
  apply (clarsimp simp: is_final_cap'_def gen_obj_refs_def)
  done

lemma cte_wp_at_obj_refs_singleton_page_table:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PageTableCap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at ((=) (ArchObjectCap (PageTableCap p asid))) (a,b) s"
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma cte_wp_at_obj_refs_singleton_page_directory:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PageDirectoryCap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at
            ((=) (ArchObjectCap (PageDirectoryCap p asid))) (a,b) s"
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma final_cap_pt_slot_eq:
  "\<lbrakk>is_final_cap' (ArchObjectCap (PageTableCap p asid)) s;
    cte_wp_at ((=) (ArchObjectCap (PageTableCap p asid'))) slot s;
    cte_wp_at ((=) (ArchObjectCap (PageTableCap p asid''))) slot' s\<rbrakk> \<Longrightarrow>
   slot' = slot"
  apply (clarsimp simp:is_final_cap'_def2)
  apply (case_tac "(a,b) = slot'")
   apply (case_tac "(a,b) = slot")
    apply simp
   apply (erule_tac x="fst slot" in allE)
   apply (erule_tac x="snd slot" in allE)
   apply (clarsimp simp: gen_obj_refs_def cap_irqs_def cte_wp_at_def)
  apply (erule_tac x="fst slot'" in allE)
  apply (erule_tac x="snd slot'" in allE)
  apply (clarsimp simp: gen_obj_refs_def cap_irqs_def cte_wp_at_def)
  done

lemma final_cap_pd_slot_eq:
  "\<lbrakk>is_final_cap' (ArchObjectCap (PageDirectoryCap p asid)) s;
    cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap p asid'))) slot s;
    cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap p asid''))) slot' s\<rbrakk>
  \<Longrightarrow> slot' = slot"
  apply (clarsimp simp:is_final_cap'_def2)
  apply (case_tac "(a,b) = slot'")
   apply (case_tac "(a,b) = slot")
    apply simp
   apply (erule_tac x="fst slot" in allE)
   apply (erule_tac x="snd slot" in allE)
   apply (clarsimp simp: gen_obj_refs_def cap_irqs_def cte_wp_at_def)
  apply (erule_tac x="fst slot'" in allE)
  apply (erule_tac x="snd slot'" in allE)
  apply (clarsimp simp: gen_obj_refs_def cap_irqs_def cte_wp_at_def)
  done

lemma is_arch_update_reset_page:
  "is_arch_update
     (ArchObjectCap (PageCap dev p r sz m))
     (ArchObjectCap (PageCap dev p r' sz m'))"
  apply (simp add: is_arch_update_def is_arch_cap_def cap_master_cap_def)
  done

lemma replaceable_reset_pt:
  "\<lbrakk>cap = PageTableCap p m \<and>
   cte_wp_at ((=) (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table {}) p s\<rbrakk> \<Longrightarrow>
   replaceable s slot (ArchObjectCap (PageTableCap p None))
                      (ArchObjectCap cap)"
  apply (elim conjE)
  apply (cases m, simp_all add: replaceable_def gen_obj_refs_def cap_range_def
                                is_cap_simps tcb_cap_valid_pagetable)
  apply (rule conjI)
   apply (frule is_final_cap_pt_asid_eq) defer
   apply clarsimp
   apply (drule cte_wp_at_obj_refs_singleton_page_table)
   apply (erule exE)
   apply (drule_tac x="asid" in is_final_cap_pt_asid_eq)
   apply (drule final_cap_pt_slot_eq)
     apply simp_all
  apply (rule_tac
    cap="(cap.ArchObjectCap cap)"
    in  no_cap_to_obj_with_diff_ref_finalI)
  apply simp_all
  done

crunch vcpu_finalise
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
   (wp: crunch_wps)

crunch arch_finalise_cap
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
   (wp: crunch_wps simp: crunch_simps)

lemma set_vm_root_empty[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (empty_table {}) p s)\<rbrace> set_vm_root v \<lbrace>\<lambda>_ s. P (obj_at (empty_table {}) p s) \<rbrace>"
  apply (simp add: set_vm_root_def)
  apply wpsimp+
     apply (clarsimp simp: if_apply_def2)
     apply (wpsimp+ | rule hoare_conjI[rotated] hoare_drop_imp hoare_allI)+
  done

crunch invalidate_tlb_by_asid
  for obj_at[wp]: "\<lambda>s. P' (obj_at P p s)"
  (wp: whenE_wp simp: crunch_simps)

lemma set_asid_pool_empty[wp]:
  "\<lbrace>obj_at (empty_table {}) word\<rbrace> set_asid_pool x2 pool' \<lbrace>\<lambda>xb. obj_at (empty_table {}) word\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  apply (wpsimp wp: set_object_wp_strong simp: a_type_def)
  apply (clarsimp simp: empty_table_def)
  done

lemma delete_asid_empty_table_pd:
  "\<lbrace>\<lambda>s. page_directory_at word s
      \<and> obj_at (empty_table {}) word s\<rbrace>
    delete_asid a word
   \<lbrace>\<lambda>_ s. obj_at (empty_table {}) word s\<rbrace>"
   apply (simp add: delete_asid_def)
   apply wpsimp+
   done

lemma page_directory_at_def2:
  "page_directory_at p s = (\<exists>pd. ko_at (ArchObj (PageDirectory pd)) p s)"
  apply (simp add: a_type_def obj_at_def)
  apply (rule iffI)
   apply (erule exE)
   apply (case_tac ko, simp_all add: if_split_eq1)
   apply (rename_tac arch_kernel_obj)
   apply (case_tac arch_kernel_obj, simp_all split: if_splits)
  apply (erule exE)
  apply (rule_tac x="ArchObj (PageDirectory pd)" in exI)
  apply simp
  done

definition
  pde_wp_at :: "(pde \<Rightarrow> bool) \<Rightarrow> word32 \<Rightarrow> 11 word \<Rightarrow> 'z state \<Rightarrow> bool"
  where
  "pde_wp_at P ptr slot s \<equiv>
     (case (kheap s ptr) of
         Some (ArchObj (PageDirectory pd)) \<Rightarrow> P (pd slot)
       | _ \<Rightarrow> False)"

lemma store_pde_pde_wp_at:
  "\<lbrace>\<top>\<rbrace>
   store_pde p x
   \<lbrace>\<lambda>_. pde_wp_at
         (\<lambda>pde. pde = x) (p && ~~ mask pd_bits) (ucast (p && mask pd_bits >> 3))\<rbrace>"
  apply (wp
    | simp add: store_pde_def set_pd_def set_object_def get_object_def
                obj_at_def pde_wp_at_def vspace_bits_defs)+
  done

lemma store_pde_pde_wp_at2:
  "\<lbrace>pde_wp_at (\<lambda>pde. pde = pde.InvalidPDE) ptr slot\<rbrace>
   store_pde p' InvalidPDE
   \<lbrace>\<lambda>_. pde_wp_at (\<lambda>pde. pde = InvalidPDE) ptr slot\<rbrace>"
  apply (wp
    | simp add: store_pde_def set_pd_def set_object_def get_object_def
                obj_at_def pde_wp_at_def
    | clarsimp)+
  done

lemma obj_at_empty_tableI:
  "invs s \<and>
  (\<forall>x. pde_wp_at (\<lambda>pde. pde = InvalidPDE) p x s)
  \<Longrightarrow> obj_at (empty_table {}) p s"
  apply safe
  apply (simp add: obj_at_def empty_table_def pde_wp_at_def)
  (* Boring cases *)
  apply (case_tac "\<exists>ko. kheap s p = Some ko")
   apply (erule exE) apply (rule_tac x=ko in exI)
   apply (rule conjI)
    apply assumption
   apply (case_tac ko)
       apply ((erule_tac x="ucast (kernel_base >> 21) - 1" in allE,
         simp add: kernel_base_def)+)[4]
   apply (rename_tac arch_kernel_obj)
   apply (case_tac arch_kernel_obj) defer 3
      apply ((erule_tac x="ucast (kernel_base >> 21) - 1" in allE,
         simp add: kernel_base_def)+)[5]
   (* Interesting case *)
  apply (rename_tac "fun")
  apply clarsimp
  apply (clarsimp simp add: valid_pde_mappings_def pde_ref_def)
  done

lemma pd_shifting_again3:
  "is_aligned pd pd_bits \<Longrightarrow> ((ucast (ae :: 11 word) << 3) + (pd :: word32) && ~~ mask pd_bits) = pd"
  apply (subst add.commute)
  apply (rule pd_shifting_again)
  apply assumption
  done

lemma pd_shifting_again4: "is_aligned (pd::word32) pd_bits \<Longrightarrow>
  (ucast (ae::11 word) << 3) + pd && mask pd_bits = (ucast ae << 3)"
  apply (subst add.commute)
  apply (simp add:shiftl_t2n mask_add_aligned)
  apply (rule less_mask_eq)
  apply (rule word_less_power_trans[where k = 3, simplified])
  apply (rule less_le_trans[OF ucast_less])
    apply (simp add:vspace_bits_defs)+
  done

lemma pd_shifting_again5:
  "\<lbrakk>is_aligned (pd :: word32) pd_bits;(sl::word32) = ucast (ae::11 word)\<rbrakk> \<Longrightarrow>
  ucast ((sl << 3) + pd && mask pd_bits >> 3) = ae"
  apply simp
  apply (frule_tac pd=pd and ae=ae in pd_shifting_again4)
  apply simp
  apply (cut_tac x="ucast ae :: word32" and n=3 in shiftl_shiftr_id)
    apply ((simp add: word_bits_def less_le_trans[OF ucast_less])+)[2]
  apply (simp add:ucast_bl)
  apply (subst word_rep_drop)
    apply simp
  done

lemma pd_shifting_global_refs:
  "\<lbrakk>is_aligned pd pd_bits;
    ae \<le> (kernel_base >> 21) - 1; pd \<notin> global_refs s\<rbrakk>
   \<Longrightarrow> ((ae::word32) << 3) + pd && ~~ mask pd_bits \<notin> global_refs s"
  apply (cut_tac pd="pd" and ae="ucast ae" in pd_shifting_again3)
   apply simp
  apply (simp add: ucast_bl word_rep_drop of_drop_to_bl word_size)
  apply (insert and_mask_eq_iff_le_mask[where n=11 and w=ae, THEN iffD2])
  apply (frule_tac z="mask 11" in order_trans)
   apply (simp add: mask_def kernel_base_def)
  apply simp
  done

lemma word_aligned_pt_slots:
  "\<lbrakk>is_aligned word pt_bits;
    x \<in> set [word , word + 4 .e. word + 2 ^ pt_bits - 1]\<rbrakk>
  \<Longrightarrow> x && ~~ mask pt_bits = word"
  apply (simp add: pt_bits_def pageBits_def)
  apply (drule subsetD[OF upto_enum_step_subset])
  apply (frule_tac ptr'=x in mask_in_range)
  apply simp
  done

lemma ucast_less_shiftl_helper3:
  "\<lbrakk> len_of TYPE('b) + 3 < len_of TYPE('a); 2 ^ (len_of TYPE('b) + 3) \<le> n\<rbrakk>
    \<Longrightarrow> (ucast (x :: 'b::len word) << 3) < (n :: 'a::len word)"
  apply (erule order_less_le_trans[rotated])
  using ucast_less[where x=x and 'a='a]
  apply (simp only: shiftl_t2n field_simps)
  apply (rule word_less_power_trans2; simp)
  done

lemma pt_shifting:
  "\<lbrakk>is_aligned (pt::word32) pt_bits\<rbrakk>
   \<Longrightarrow> pt + (ucast (ae :: 9 word) << 3) && mask pt_bits
      = (ucast (ae :: 9 word) << 3)"
  apply (rule conjunct1, erule is_aligned_add_helper)
  apply (rule ucast_less_shiftl_helper3)
   apply (simp add: word_bits_def)
  apply (simp add: vspace_bits_defs)
  done

lemma word32_ucast_enumerates_word8:
  "\<lbrakk>is_aligned (word :: word32) pt_bits\<rbrakk>
  \<Longrightarrow> (x :: 9 word) \<in> (\<lambda>sl. ucast (sl && mask pt_bits >> 3))
     ` set [word , word + 8 .e. word + 2 ^ pt_bits - 1]"
  apply (rule_tac x="word + (ucast x << 3)" in image_eqI)
   apply (frule_tac ae="x" in pt_shifting)
   apply simp
   apply (rule sym)
   apply (rule pd_casting_shifting)
   apply (simp add: word_size len32)
  apply (clarsimp simp: upto_enum_step_def)
  apply (rule conjI)
   apply (subgoal_tac
     " word + 2 ^ pt_bits - 1 \<ge> word", simp)
   apply (rule is_aligned_no_overflow)
    apply (simp, simp add: pt_bits_def pageBits_def word_bits_def)
  apply clarsimp
  apply (rule_tac x="ucast x" in image_eqI)
   apply (simp add: word_shift_by_3 vspace_bits_defs)
  apply (clarsimp simp: vspace_bits_defs)
  apply (rule order_trans)
   apply (rule word_le_minus_one_leq)
   apply (rule ucast_less)
   apply simp+
  done

lemma caps_of_state_aligned_page_table:
  "\<lbrakk>caps_of_state s slot =
  Some (ArchObjectCap (PageTableCap word option));
  invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pt_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pt_bits_def pageBits_def)
  done

lemma caps_of_state_aligned_page_directory:
  "\<lbrakk>caps_of_state s slot =
  Some (ArchObjectCap (PageDirectoryCap word option));
  invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pd_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pd_bits_def pageBits_def)
  done
end

lemma invs_valid_arch_capsI:
  "invs s \<Longrightarrow> valid_arch_caps s"
  by (simp add: invs_def valid_state_def)

context Arch begin arch_global_naming

lemma arch_finalise_case_no_lookup:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_objs and
    valid_cap (cap.ArchObjectCap acap) and (\<lambda>s. valid_asid_table (arm_asid_table (arch_state s)) s)
    and K (aobj_ref acap = Some w \<and> is_final)\<rbrace>
  arch_finalise_cap acap is_final
  \<lbrace>\<lambda>rv s. (\<forall>vs. vs_cap_ref (cap.ArchObjectCap acap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> w) s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
   apply (simp add: arch_finalise_cap_def)
   apply (wpc | wp delete_asid_pool_unmapped hoare_vcg_imp_lift
                   unmap_page_table_unmapped3
              | simp add: vs_cap_ref_simps
                          vs_lookup_pages_eq_at[THEN fun_cong, symmetric]
                          vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])+
     apply (wp hoare_vcg_all_lift unmap_page_unmapped hoare_weak_lift_imp)
    apply (wpc|wp unmap_page_table_unmapped3 delete_asid_unmapped
      |simp add:vs_cap_ref_def
      vs_lookup_pages_eq_at[THEN fun_cong,symmetric]
      vs_lookup_pages_eq_ap[THEN fun_cong,symmetric])+
   apply (auto simp: valid_cap_simps valid_arch_state_def data_at_def vspace_bits_defs
              split: vmpage_size.split)
   apply ((case_tac x; simp)+)[4]
   (* apply (auto simp add: tcb_at_typ obj_at_def is_cap_table_def)+ *)
   done

lemma arch_finalise_pt_pd_empty:
  "\<lbrace>(\<lambda>s. obj_at (empty_table {}) ptr s) and valid_cap (cap.ArchObjectCap acap) and
    K ((is_pt_cap (cap.ArchObjectCap acap) \<or> is_pd_cap (cap.ArchObjectCap acap)) \<and> aobj_ref acap = Some ptr)\<rbrace>
  arch_finalise_cap acap final
  \<lbrace>\<lambda>rv s. obj_at (empty_table {}) ptr s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: is_cap_simps arch_finalise_cap_def)
   apply (rule hoare_pre)
   apply (wp unmap_page_table_empty | wpc)+
   apply clarsimp
  apply (clarsimp simp: is_cap_simps arch_finalise_cap_def)
  apply (rule hoare_pre)
  apply (wp unmap_page_table_empty delete_asid_empty_table_pd | wpc)+
  apply (clarsimp simp: valid_cap_def)
  done

lemma do_machine_op_reachable_pg_cap[wp]:
  "\<lbrace>\<lambda>s. P (reachable_pg_cap cap s)\<rbrace>
   do_machine_op mo
   \<lbrace>\<lambda>rv s. P (reachable_pg_cap cap s)\<rbrace>"
  apply (simp add:reachable_pg_cap_def,wp)
  done

lemma replaceable_or_arch_update_pg:
  " (case (vs_cap_ref (ArchObjectCap (PageCap dev word fun vm_pgsz y))) of None \<Rightarrow> True | Some ref \<Rightarrow> \<not> (ref \<unrhd> word) s)
  \<longrightarrow> replaceable_or_arch_update s slot (ArchObjectCap (PageCap dev word fun vm_pgsz None))
                (ArchObjectCap (PageCap dev word fun vm_pgsz y))"
  unfolding replaceable_or_arch_update_def
  apply (auto simp: is_cap_simps is_arch_update_def cap_master_cap_simps)
  done

lemma store_pde_vspace_objs_invalid:
  "\<lbrace>valid_vspace_objs\<rbrace> store_pde p InvalidPDE \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (wp store_pde_arch_objs_unmap)
  apply (simp add: pde_ref_def)
  done

crunch invalidate_tlb_by_asid
  for valid_cap: "valid_cap cap"
crunch page_table_mapped
  for inv: "P"
crunch invalidate_tlb_by_asid
  for valid_objs[wp]: "valid_objs"
crunch do_machine_op
  for valid_asid_table[wp]: "\<lambda>s. valid_asid_table (arm_asid_table (arch_state s)) s"

lemma mapM_x_swp_store_invalid_pte_invs:
  "\<lbrace>invs and (\<lambda>s. \<exists>slot. cte_wp_at
             (\<lambda>c. (\<lambda>x. x && ~~ mask pt_bits) ` set slots \<subseteq> obj_refs c \<and>
                  is_pt_cap c) slot s)\<rbrace>
  mapM_x (\<lambda>x. store_pte x InvalidPTE) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add:
    mapM_x_swp_store_pte_invs[unfolded swp_def,
      where pte=InvalidPTE, simplified])

lemma mapM_x_swp_store_invalid_pde_invs:
  "\<lbrace>invs and
   (\<lambda>s. \<forall>sl\<in>set slots. sl && ~~ mask pd_bits \<notin> global_refs s)\<rbrace>
     mapM_x (\<lambda>x. store_pde x InvalidPDE) slots
   \<lbrace>\<lambda>rv. invs \<rbrace>"
  apply (simp add:mapM_x_mapM)
  apply (wp mapM_swp_store_pde_invs_unmap[unfolded swp_def,
              where pde=InvalidPDE, simplified])
  done

crunch prepare_thread_delete
  for invs[wp]: invs
  (ignore: set_object)

lemma (* finalise_cap_invs *)[Finalise_AI_assms]:
  shows "\<lbrace>invs and cte_wp_at ((=) cap) slot\<rbrace> finalise_cap cap x \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases cap, simp_all split del: if_split)
         apply (wp cancel_all_ipc_invs cancel_all_signals_invs unbind_notification_invs
                   unbind_maybe_notification_invs
                  | simp add: o_def split del: if_split cong: if_cong
                  | wpc )+
      apply clarsimp (* thread *)
      apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp)
      apply (clarsimp simp: valid_cap_def)
      apply (frule(1) valid_global_refsD[OF invs_valid_global_refs])
       apply (simp add: global_refs_def, rule disjI1, rule refl)
      apply (simp add: cap_range_def)
     apply (wp deleting_irq_handler_invs  | simp | intro conjI impI)+
  apply (auto dest: cte_wp_at_valid_objs_valid_cap)
  done

lemma (* finalise_cap_irq_node *)[Finalise_AI_assms]:
"\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> finalise_cap a b \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  apply (case_tac a,simp_all)
  apply (wp | clarsimp)+
  done

lemmas (*arch_finalise_cte_irq_node *) [wp,Finalise_AI_assms]
    = hoare_use_eq_irq_node [OF arch_finalise_cap_irq_node arch_finalise_cap_cte_wp_at]

lemma (* deleting_irq_handler_st_tcb_at *) [Finalise_AI_assms]:
  "\<lbrace>st_tcb_at P t and K (\<forall>st. simple st \<longrightarrow> P st)\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_st_tcb_at)
  apply simp
  done

lemma irq_node_global_refs_ARCH [Finalise_AI_assms]:
  "interrupt_irq_node s irq \<in> global_refs s"
  by (simp add: global_refs_def)

lemma (* get_irq_slot_fast_finalisable *)[wp,Finalise_AI_assms]:
  "\<lbrace>invs\<rbrace> get_irq_slot irq \<lbrace>cte_wp_at can_fast_finalise\<rbrace>"
  apply (simp add: get_irq_slot_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_irq_node_def)
  apply (drule spec[where x=irq], drule cap_table_at_cte_at[where offset="[]"])
   apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (case_tac "cap = cap.NullCap")
   apply (simp add: can_fast_finalise_def)
  apply (frule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
   apply simp
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  apply (drule cte_wp_at_norm, clarsimp)
  apply (drule(1) valid_global_refsD [OF _ _ irq_node_global_refs_ARCH[where irq=irq]])
  apply (case_tac c, simp_all)
     apply (clarsimp simp: cap_range_def)
    apply (clarsimp simp: cap_range_def)
   apply (clarsimp simp: appropriate_cte_cap_def can_fast_finalise_def split: cap.split_asm)
  apply (clarsimp simp: cap_range_def)
  done

lemma (* replaceable_or_arch_update_same *) [Finalise_AI_assms]:
  "replaceable_or_arch_update s slot cap cap"
  by (clarsimp simp: replaceable_or_arch_update_def
                replaceable_def is_arch_update_def is_cap_simps)

lemma (* replace_cap_invs_arch_update *)[Finalise_AI_assms]:
  "\<lbrace>\<lambda>s. cte_wp_at (replaceable_or_arch_update s p cap) p s
        \<and> invs s
        \<and> cap \<noteq> cap.NullCap
        \<and> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s
        \<and> s \<turnstile> cap\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  apply (simp add:replaceable_or_arch_update_def)
  apply (cases "is_pg_cap cap")
   apply (wp hoare_pre_disj[OF arch_update_cap_invs_unmap_page arch_update_cap_invs_map])
   apply (simp add:replaceable_or_arch_update_def replaceable_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps gen_obj_refs_def
                         cap_master_cap_simps is_arch_update_def)
  apply (wp replace_cap_invs)
  apply simp
  done

lemma dmo_tcb_cap_valid_ARCH [Finalise_AI_assms]:
  "\<lbrace>\<lambda>s. P (tcb_cap_valid cap ptr s)\<rbrace> do_machine_op mop \<lbrace>\<lambda>_ s. P (tcb_cap_valid cap ptr s)\<rbrace>"
  apply (simp add: tcb_cap_valid_def no_cap_to_obj_with_diff_ref_def)
  apply (rule hoare_pre)
  apply wps
  apply wp
  apply simp
  done

lemma (* dmo_replaceable_or_arch_update *) [Finalise_AI_assms,wp]:
  "\<lbrace>\<lambda>s. replaceable_or_arch_update s slot cap cap'\<rbrace>
    do_machine_op mo
  \<lbrace>\<lambda>r s. replaceable_or_arch_update s slot cap cap'\<rbrace>"
  unfolding replaceable_or_arch_update_def replaceable_def no_cap_to_obj_with_diff_ref_def
            replaceable_final_arch_cap_def replaceable_non_final_arch_cap_def
  apply (rule hoare_pre)
  apply (wps dmo_tcb_cap_valid_ARCH do_machine_op_reachable_pg_cap)
  apply (rule hoare_vcg_prop)
  apply auto
  done

end

arch_requalify_consts replaceable_or_arch_update

interpretation Finalise_AI_3?: Finalise_AI_3
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_assms)?)
  qed

context Arch begin arch_global_naming

lemma typ_at_data_at_wp:
  assumes typ_wp: "\<And>a.\<lbrace>typ_at a p \<rbrace> g \<lbrace>\<lambda>s. typ_at a p\<rbrace>"
  shows "\<lbrace>data_at b p\<rbrace> g \<lbrace>\<lambda>s. data_at b p\<rbrace>"
  apply (simp add: data_at_def)
  apply (wp typ_wp hoare_vcg_disj_lift)
  done

end

interpretation Finalise_AI_4?: Finalise_AI_4
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_assms)?)
  qed

context Arch begin arch_global_naming

lemma set_asid_pool_obj_at_ptr:
  "\<lbrace>\<lambda>s. P (ArchObj (arch_kernel_obj.ASIDPool mp))\<rbrace>
     set_asid_pool ptr mp
   \<lbrace>\<lambda>rv s. obj_at P ptr s\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  done

lemma valid_arch_state_table_strg:
  "valid_arch_state s \<and> asid_pool_at p s \<and>
   Some p \<notin> arm_asid_table (arch_state s) ` (dom (arm_asid_table (arch_state s)) - {x}) \<longrightarrow>
   valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(x \<mapsto> p)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def ran_def split: option.split)
  apply (rule conjI; clarsimp)
   apply (rule conjI, fastforce)
   apply (erule inj_on_fun_upd_strongerI)
   apply simp
  apply (rule conjI, fastforce)
  apply (erule inj_on_fun_upd_strongerI)
  apply simp
  done

lemma valid_table_caps_table [simp]:
  "valid_table_caps (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := arm_asid_table'\<rparr>\<rparr>) = valid_table_caps s"
  by (simp add: valid_table_caps_def)

lemma valid_kernel_mappings [iff]:
  "valid_kernel_mappings (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := arm_asid_table'\<rparr>\<rparr>) = valid_kernel_mappings s"
  by (simp add: valid_kernel_mappings_def)

lemma vs_asid_refs_updateD:
  "(ref', p') \<in> vs_asid_refs (table (x \<mapsto> p))
  \<Longrightarrow> (ref',p') \<in> vs_asid_refs table \<or> (ref' = [VSRef (ucast x) None] \<and> p' = p)"
  apply (clarsimp simp: vs_asid_refs_def graph_of_def split: if_split_asm)
  apply (rule_tac x="(a,p')" in image_eqI)
   apply auto
  done

lemma vs_lookup1_arch [simp]:
  "vs_lookup1 (arch_state_update f s) = vs_lookup1 s"
  by (simp add: vs_lookup1_def)

lemma vs_lookup_empty_table:
  "(rs \<rhd> q)
  (s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj (ASIDPool Map.empty)),
     arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(x \<mapsto> p)\<rparr>\<rparr>) \<Longrightarrow>
   (rs \<rhd> q) s \<or> (rs = [VSRef (ucast x) None] \<and> q = p)"
  apply (erule vs_lookupE)
  apply clarsimp
  apply (drule vs_asid_refs_updateD)
  apply (erule disjE)
   apply (drule rtranclD)
   apply (erule disjE)
    apply clarsimp
    apply (fastforce simp: vs_lookup_def)
   apply clarsimp
   apply (drule trancl_sub_lift [rotated])
    prefer 2
    apply (rule vs_lookup_trancl_step)
     prefer 2
     apply assumption
    apply (fastforce simp: vs_lookup_def)
   apply (clarsimp simp: obj_at_def vs_lookup1_def vs_refs_def
                  split: if_split_asm)
  apply clarsimp
  apply (drule rtranclD)
  apply (erule disjE)
   apply clarsimp
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def)
  done

lemma vs_lookup_pages_empty_table:
  "(rs \<unrhd> q)
  (s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj (ASIDPool Map.empty)),
     arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(x \<mapsto> p)\<rparr>\<rparr>) \<Longrightarrow>
   (rs \<unrhd> q) s \<or> (rs = [VSRef (ucast x) None] \<and> q = p)"
  apply (subst (asm) vs_lookup_pages_def)
  apply (clarsimp simp: Image_def)
  apply (drule vs_asid_refs_updateD)
  apply (erule disjE)
   apply (drule rtranclD)
   apply (erule disjE)
    apply clarsimp
    apply (fastforce simp: vs_lookup_pages_def)
   apply clarsimp
   apply (drule trancl_sub_lift [rotated])
    prefer 2
    apply (rule vs_lookup_pages_trancl_step)
     prefer 2
     apply assumption
    apply (fastforce simp: vs_lookup_pages_def)
   apply (clarsimp simp: obj_at_def vs_lookup_pages1_def vs_refs_pages_def
                  split: if_split_asm)
  apply clarsimp
  apply (drule rtranclD)
  apply (erule disjE)
   apply clarsimp
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup_pages1D)
  apply (clarsimp simp: obj_at_def vs_refs_pages_def)
  done

lemma set_asid_pool_empty_table_objs:
  "\<lbrace>valid_vspace_objs and asid_pool_at p\<rbrace>
  set_asid_pool p Map.empty
   \<lbrace>\<lambda>rv s. valid_vspace_objs
             (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table :=
                (arm_asid_table (arch_state s))(asid_high_bits_of word2 \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def valid_vspace_objs_def
                  simp del: fun_upd_apply
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule valid_vspace_obj_same_type)
    prefer 2
    apply simp
   prefer 2
   apply (simp add: a_type_def)
  apply (clarsimp simp add: a_type_def split: if_split_asm)
  apply (erule_tac x=pa in allE)
  apply (erule impE)
   apply (drule vs_lookup_empty_table)
   apply fastforce
  apply simp
  done

lemma set_asid_pool_empty_table_lookup:
  "\<lbrace>valid_vs_lookup and asid_pool_at p and
    (\<lambda>s. \<exists>p'. caps_of_state s p' = Some (ArchObjectCap (ASIDPoolCap p base)))\<rbrace>
  set_asid_pool p Map.empty
   \<lbrace>\<lambda>rv s. valid_vs_lookup
             (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table :=
                (arm_asid_table (arch_state s))(asid_high_bits_of base \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def valid_vs_lookup_def
                  simp del: fun_upd_apply)
  apply (drule vs_lookup_pages_empty_table)
  apply (erule disjE)
   apply (fastforce simp: caps_of_state_after_update[folded fun_upd_apply]
                         obj_at_def)
  apply clarsimp
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (simp add: caps_of_state_after_update [folded fun_upd_apply] obj_at_def)
  apply (simp add: vs_cap_ref_def)
  done

lemma set_asid_pool_empty_valid_asid_map:
  "\<lbrace>\<lambda>s. valid_asid_map s \<and> asid_pool_at p s
       \<and> (\<forall>asid'. \<not> ([VSRef asid' None] \<rhd> p) s)
       \<and> (\<forall>p'. \<not> ([VSRef (ucast (asid_high_bits_of base)) None] \<rhd> p') s)\<rbrace>
       set_asid_pool p Map.empty
   \<lbrace>\<lambda>rv s. valid_asid_map (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table :=
                 (arm_asid_table (arch_state s))(asid_high_bits_of base \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: valid_asid_map_def vspace_at_asid_def
                 dest!: graph_ofD
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  apply (drule bspec, erule graph_ofI)
  apply (clarsimp dest!: vs_lookup_2ConsD vs_lookup1D)
  apply (case_tac "p = pa")
   apply simp
  apply (clarsimp elim!: vs_lookup_atE)
  apply (rule vs_lookupI[rotated])
   apply (rule r_into_rtrancl)
   apply (rule_tac p=pa in vs_lookup1I)
     apply (simp add: obj_at_def)
    apply assumption
   apply simp
  apply (rule vs_asid_refsI)
  apply clarsimp
  apply (drule vs_asid_refsI)
  apply (drule vs_lookupI, rule rtrancl_refl)
  apply simp
  done

lemma set_asid_pool_invs_table:
  "\<lbrace>\<lambda>s. invs s \<and> asid_pool_at p s
       \<and> (\<exists>p'. caps_of_state s p' = Some (ArchObjectCap (ASIDPoolCap p base)))
       \<and> (\<not> ([VSRef (ucast (asid_high_bits_of base)) None] \<rhd> p) s)
       \<and> (\<forall>p'. \<not> ([VSRef (ucast (asid_high_bits_of base)) None] \<rhd> p') s)\<rbrace>
       set_asid_pool p Map.empty
  \<lbrace>\<lambda>x s. invs (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table :=
                 (arm_asid_table (arch_state s))(asid_high_bits_of base \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_caps_def)
  apply (rule hoare_pre)
   apply (wp valid_irq_node_typ set_asid_pool_typ_at
             set_asid_pool_empty_table_objs
             valid_irq_handlers_lift set_asid_pool_empty_table_lookup
             set_asid_pool_empty_valid_asid_map
          | simp add: valid_global_objs_def valid_global_vspace_mappings_def
          | strengthen valid_arch_state_table_strg)+
  apply (clarsimp simp: conj_comms)
  apply (rule context_conjI)
   apply clarsimp
   apply (frule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
   apply clarsimp
   apply (drule obj_ref_elemD)
   apply (frule(2) unique_table_refsD,
          unfold obj_refs.simps aobj_ref.simps option.simps,
          assumption)
   apply (clarsimp simp:vs_cap_ref_def table_cap_ref_def
     split:cap.split_asm arch_cap.split_asm if_splits)
  apply clarsimp
  apply (drule vs_asid_refsI)
  apply (drule vs_lookupI, rule rtrancl_refl)
  apply simp
  done

lemma delete_asid_pool_unmapped2:
  "\<lbrace>\<lambda>s. (base' = base \<and> ptr' = ptr)
         \<or> \<not> ([VSRef (ucast (asid_high_bits_of base')) None] \<rhd> ptr') s\<rbrace>
     delete_asid_pool base ptr
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (ucast (asid_high_bits_of base')) None] \<rhd> ptr') s\<rbrace>"
  (is "valid ?P ?f (\<lambda>rv. ?Q)")
  apply (cases "base = base' \<and> ptr = ptr'")
   apply simp
   apply (wp delete_asid_pool_unmapped)
  apply (simp add: delete_asid_pool_def)
  apply wp
     apply (rule_tac Q'="\<lambda>rv s. ?Q s \<and> asid_table = arm_asid_table (arch_state s)"
                in hoare_post_imp)
      apply (clarsimp simp: fun_upd_def[symmetric])
      apply (drule vs_lookup_clear_asid_table[rule_format])
      apply simp
     apply (wp mapM_wp')+
     apply clarsimp
    apply wp+
  apply fastforce
  done

lemma page_table_mapped_wp_weak:
  "\<lbrace>\<lambda>s. Q None s \<and> (\<forall>x. Q (Some x) s)\<rbrace>
     page_table_mapped asid vptr pt
   \<lbrace>Q\<rbrace>"
  (is "\<lbrace>?P\<rbrace> page_table_mapped asid vptr pt \<lbrace>Q\<rbrace>")
  apply (simp add: page_table_mapped_def)
  apply (rule hoare_pre)
   apply (wp get_pde_wp | wpc)+
   apply (rule_tac Q'="\<lambda>_. ?P" in hoare_strengthen_postE_R)
    apply wp
   apply clarsimp
  apply simp
  done

crunch invalidate_tlb_by_asid
  for global_refs_invs[wp]: "\<lambda>s. P (global_refs s)"


lemma page_table_pte_atE:
  "\<lbrakk> page_table_at p s; x < 2 ^ pt_bits;
             (x >> 3) << 3 = x; pspace_aligned s \<rbrakk>
       \<Longrightarrow> pte_at (p + x) s"
  apply (drule page_table_pte_atI[where x="x >> 3"], simp_all add: vspace_bits_defs)
  apply (rule shiftr_less_t2n[of _ 3 9, simplified], simp)
  done

crunch invalidate_tlb_by_asid
  for aligned[wp]: "pspace_aligned"

crunch invalidate_tlb_by_asid
  for valid_arch_state[wp]: "valid_arch_state"

crunch unmap_page_table, invalidate_tlb_by_asid,
  page_table_mapped, store_pte, delete_asid_pool, copy_global_mappings
  for valid_cap[wp]: "valid_cap c"
  (wp: mapM_wp_inv mapM_x_wp' simp: crunch_simps)

lemmas vcpu_finalise_typ_ats [wp] = abs_typ_at_lifts [OF vcpu_finalise_typ_at]
lemmas delete_asid_typ_ats [wp] = abs_typ_at_lifts [OF delete_asid_typ_at]

lemma arch_finalise_cap_valid_cap [wp]:
  "\<lbrace>valid_cap c\<rbrace> arch_finalise_cap cap b \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (wp | wpc | clarsimp simp: split: arch_cap.split option.split bool.split | safe)+
  done

lemmas clearMemory_invs [wp,Finalise_AI_assms]
    = clearMemory_invs

lemma valid_idle_has_null_cap_ARCH[Finalise_AI_assms]:
  "\<lbrakk> if_unsafe_then_cap s; valid_global_refs s; valid_idle s; valid_irq_node s\<rbrakk>
   \<Longrightarrow> caps_of_state s (idle_thread s, v) = Some cap
   \<Longrightarrow> cap = NullCap"
  apply (rule ccontr)
  apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
   apply clarsimp
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (frule(1) valid_global_refsD2)
  apply (case_tac capa, simp_all add: cap_range_def global_refs_def)[1]
  apply (clarsimp simp: valid_irq_node_def valid_idle_def pred_tcb_at_def
                        obj_at_def is_cap_table_def)
  apply (rename_tac word tcb)
  apply (drule_tac x=word in spec, simp)
  done

lemma (* zombie_cap_two_nonidles *)[Finalise_AI_assms]:
  "\<lbrakk> caps_of_state s ptr = Some (Zombie ptr' zbits n); invs s \<rbrakk>
       \<Longrightarrow> fst ptr \<noteq> idle_thread s \<and> ptr' \<noteq> idle_thread s"
  apply (frule valid_global_refsD2, clarsimp+)
  apply (simp add: cap_range_def global_refs_def)
  apply (cases ptr, auto dest: valid_idle_has_null_cap_ARCH[rotated -1])[1]
  done

lemma arch_derive_cap_notzombie[wp]:
  "\<lbrace>\<top>\<rbrace> arch_derive_cap acap \<lbrace>\<lambda>rv s. \<not> is_zombie rv\<rbrace>, -"
  by (cases acap; wpsimp simp: arch_derive_cap_def is_zombie_def o_def)

lemma arch_derive_cap_notIRQ[wp]:
  "\<lbrace>\<top>\<rbrace> arch_derive_cap cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.IRQControlCap\<rbrace>,-"
  by (cases cap; wpsimp simp: arch_derive_cap_def o_def)

end

interpretation Finalise_AI_5?: Finalise_AI_5
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_assms)?)
  qed

end
