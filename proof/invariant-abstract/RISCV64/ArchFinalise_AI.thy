(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
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
  "valid_global_refs (s\<lparr>arch_state := riscv_asid_table_update f (arch_state s)\<rparr>) =
  valid_global_refs s"
  by (simp add: valid_global_refs_def global_refs_def)

lemma nat_to_cref_unat_of_bl':
  "\<lbrakk> length xs < 64; n = length xs \<rbrakk> \<Longrightarrow>
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

lemma riscv_global_pt_asid_table_update[simp]:
  "riscv_global_pt (arch_state s\<lparr>riscv_asid_table := atable\<rparr>) = riscv_global_pt (arch_state s)"
  by (simp add: riscv_global_pt_def)

lemma equal_kernel_mappings_asid_table_unmap:
  "equal_kernel_mappings s
   \<Longrightarrow> equal_kernel_mappings (s\<lparr>arch_state := arch_state s
                                \<lparr>riscv_asid_table := (asid_table s)(i := None)\<rparr>\<rparr>)"
  unfolding equal_kernel_mappings_def
  apply clarsimp
  apply (erule_tac x=asid in allE)
  apply (erule_tac x=pt_ptr in allE)
  apply (clarsimp simp: fun_upd_def)
  apply (erule impE)
   subgoal by (clarsimp simp: vspace_for_asid_def in_omonad pool_for_asid_def split: if_splits)
  apply (clarsimp simp: has_kernel_mappings_def)
  done

lemma invs_riscv_asid_table_unmap:
  "invs s \<and> is_aligned base asid_low_bits
       \<and> tab = riscv_asid_table (arch_state s)
     \<longrightarrow> invs (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
  apply (strengthen valid_asid_map_unmap valid_vspace_objs_unmap_strg
                    valid_vs_lookup_unmap_strg valid_arch_state_unmap_strg)
  apply (simp add: valid_irq_node_def valid_kernel_mappings_def)
  apply (simp add: valid_table_caps_def valid_machine_state_def valid_global_objs_def
                   valid_asid_pool_caps_def equal_kernel_mappings_asid_table_unmap)
  done

lemma delete_asid_pool_invs[wp]:
  "delete_asid_pool base pptr \<lbrace>invs\<rbrace>"
  unfolding delete_asid_pool_def
  supply fun_upd_apply[simp del]
  apply wpsimp
  apply (strengthen invs_riscv_asid_table_unmap)
  apply (simp add: asid_low_bits_of_def asid_low_bits_def ucast_zero_is_aligned)
  done

lemma do_machine_op_pool_for_asid[wp]:
  "do_machine_op f \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  by (wpsimp simp: pool_for_asid_def)

lemma do_machine_op_vspace_for_asid[wp]:
  "do_machine_op f \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  by (wpsimp simp: vspace_for_asid_def obind_def
             wp: conjI hoare_vcg_all_lift hoare_vcg_imp_lift'
             split: option.splits)

lemma set_vm_root_pool_for_asid[wp]:
  "set_vm_root pt \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  by (wpsimp simp: set_vm_root_def wp: get_cap_wp)

lemma set_vm_root_vspace_for_asid[wp]:
  "set_vm_root pt \<lbrace> \<lambda>s. P (vspace_for_asid asid s) \<rbrace>"
  by (wpsimp simp: set_vm_root_def wp: get_cap_wp)

lemma clearExMonitor_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (hwASIDFlush a) \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp wp: dmo_invs
             simp: hwASIDFlush_def machine_op_lift_def
                   machine_rest_lift_def in_monad select_f_def)

lemma delete_asid_invs[wp]:
  "\<lbrace> invs and valid_asid_table and pspace_aligned \<rbrace>delete_asid asid pd \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: delete_asid_def cong: option.case_cong)
  apply (wpsimp wp: set_asid_pool_invs_unmap)
  apply blast
  done

lemma delete_asid_pool_unmapped[wp]:
  "\<lbrace>\<lambda>s. True \<rbrace>
     delete_asid_pool asid poolptr
   \<lbrace>\<lambda>_ s. pool_for_asid asid s \<noteq> Some poolptr \<rbrace>"
  unfolding delete_asid_pool_def
  by (wpsimp simp: pool_for_asid_def)

lemma set_asid_pool_unmap:
  "\<lbrace>\<lambda>s. pool_for_asid asid s = Some poolptr \<rbrace>
   set_asid_pool poolptr (pool(asid_low_bits_of asid := None))
   \<lbrace>\<lambda>rv s. vspace_for_asid asid s = None \<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_wp)
  by (simp add: pool_for_asid_def vspace_for_asid_def vspace_for_pool_def obind_def in_omonad
         split: option.splits)

lemma delete_asid_unmapped:
  "\<lbrace>\<lambda>s. vspace_for_asid asid s = Some pt\<rbrace>
   delete_asid asid pt
   \<lbrace>\<lambda>_ s. vspace_for_asid asid s = None\<rbrace>"
  unfolding delete_asid_def
  apply (simp cong: option.case_cong)
  apply (wpsimp wp: set_asid_pool_unmap)
  apply (clarsimp simp: vspace_for_asid_def pool_for_asid_def vspace_for_pool_def
                        obind_def in_omonad obj_at_def
                 split: option.splits)
  done

lemma set_pt_tcb_at:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pt a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (wpsimp simp: set_pt_def obj_at_def wp: set_object_wp)

crunch unmap_page
  for tcb_at_arch: "\<lambda>s. P (ko_at (TCB tcb) t s)"
    (simp: crunch_simps wp: crunch_wps set_pt_tcb_at ignore: set_object)

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
  by (fastforce simp: replaceable_def tcb_cap_valid_def
                      reachable_frame_cap_def reachable_target_def)

lemma (* replaceable_revokable_update *)[simp,Finalise_AI_assms]:
  "replaceable (is_original_cap_update f s) = replaceable s"
  by (fastforce simp: replaceable_def is_final_cap'_def2 tcb_cap_valid_def
                      reachable_frame_cap_def reachable_target_def)

lemma (* replaceable_more_update *) [simp,Finalise_AI_assms]:
  "replaceable (trans_state f s) sl cap cap' = replaceable s sl cap cap'"
  by (simp add: replaceable_def reachable_frame_cap_def reachable_target_def)

lemma reachable_target_trans_state[simp]:
  "reachable_target ref p (trans_state f s) = reachable_target ref p s"
  by (clarsimp simp: reachable_target_def split_def)

lemma reachable_frame_cap_trans_state[simp]:
  "reachable_frame_cap cap (trans_state f s) = reachable_frame_cap cap s"
  by (simp add: reachable_frame_cap_def)

lemmas [Finalise_AI_assms] = obj_refs_obj_ref_of (* used under name obj_ref_ofI *)

lemma (* empty_slot_invs *) [Finalise_AI_assms]:
  "\<lbrace>\<lambda>s. invs s \<and> cte_wp_at (replaceable s sl cap.NullCap) sl s \<and>
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
               | simp add: trans_state_update[symmetric]
                      del: trans_state_update fun_upd_apply
                      split del: if_split)+
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
   apply (clarsimp simp: valid_arch_mdb_def)
  apply (rule conjI)
   apply (clarsimp simp: irq_revocable_def)
  apply (rule conjI)
  apply (thin_tac "info \<noteq> NullCap \<longrightarrow> P info" for P)
   apply (clarsimp simp: valid_machine_state_def)
  apply (rule conjI)
   apply (clarsimp simp:descendants_inc_def mdb_empty_abs.descendants)
  apply (rule conjI)
   apply (simp add: valid_ioc_def)
  apply (rule conjI)
   apply (fastforce simp: tcb_cap_valid_def
                  dest!: valid_NullCapD)
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
                        reachable_frame_cap_def reachable_target_def
                   del: allI)
  apply (case_tac "is_final_cap' cap s")
   apply auto[1]
  apply (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state)
  by fastforce

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

lemma prepare_thread_delete_final[wp]:
  "\<lbrace>is_final_cap' cap\<rbrace> prepare_thread_delete t \<lbrace> \<lambda>rv. is_final_cap' cap\<rbrace>"
  unfolding prepare_thread_delete_def by wp

lemma length_and_unat_of_bl_length:
  "(length xs = x \<and> unat (of_bl xs :: 'a::len word) < 2 ^ x) = (length xs = x)"
  by (auto simp: unat_of_bl_length)

lemmas unbind_from_sc_final_cap[wp] =
    final_cap_lift [OF unbind_from_sc_caps_of_state]

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
            apply ((wp suspend_final_cap[where sl=slot] get_simple_ko_wp
                      deleting_irq_handler_final[where slot=slot]
                      | simp add: o_def is_cap_simps fst_cte_ptrs_def
                                  dom_tcb_cap_cases_lt_ARCH tcb_cnode_index_def
                                  can_fast_finalise_def length_and_unat_of_bl_length
                                  appropriate_cte_cap_def gen_obj_refs_def
                                  vs_cap_ref_def cap_cleanup_opt_def
                      | intro impI TrueI ext conjI)+)[13]
  apply (simp add: arch_finalise_cap_def split del: if_split)
  apply (rule hoare_pre)
   apply (wpsimp simp: cap_cleanup_opt_def arch_cap_cleanup_opt_def)+
  done

crunch arch_finalise_cap
  for typ_at[wp,Finalise_AI_assms]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps unless_def assertE_def
        ignore: maskInterrupt set_object)

crunch prepare_thread_delete
  for typ_at[wp,Finalise_AI_assms]: "\<lambda>s. P (typ_at T p s)"

crunch prepare_thread_delete
  for tcb_at[wp]: "\<lambda>s. tcb_at p s"

lemma (* finalise_cap_new_valid_cap *)[wp,Finalise_AI_assms]:
  "\<lbrace>valid_cap cap\<rbrace> finalise_cap cap x \<lbrace>\<lambda>rv. valid_cap (fst rv)\<rbrace>"
  apply (cases cap; simp)
            apply (wp suspend_valid_cap prepare_thread_delete_typ_at
                     | simp add: o_def valid_cap_def cap_aligned_def
                                 valid_cap_Null_ext
                           split del: if_split
                     | clarsimp | rule conjI)+
  (* ArchObjectCap *)
  apply (wpsimp wp: o_def valid_cap_def cap_aligned_def
                 split_del: if_split
         | clarsimp simp: arch_finalise_cap_def)+
  done

lemma hoare_split: "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q r and Q' r\<rbrace>"
  by (auto simp: valid_def)

lemma as_user_unlive_hyp[wp]:
  "\<lbrace>obj_at (Not \<circ> hyp_live) vr\<rbrace> as_user t f \<lbrace>\<lambda>_. obj_at (Not \<circ> hyp_live) vr\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_def hyp_live_def arch_tcb_context_set_def)

lemma as_user_unlive0[wp]:
  "\<lbrace>obj_at (Not \<circ> live0) vr\<rbrace> as_user t f \<lbrace>\<lambda>_. obj_at (Not \<circ> live0) vr\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_def arch_tcb_context_set_def dest!: get_tcb_SomeD)

lemma o_def_not: "obj_at (\<lambda>a. \<not> P a) t s =  obj_at (Not o P) t s"
  by (simp add: obj_at_def)

lemma as_user_valid_irq_node[wp]:
  "\<lbrace>valid_irq_node\<rbrace> as_user t f \<lbrace>\<lambda>_. valid_irq_node\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_irq_node_def obj_at_def is_cap_table dest!: get_tcb_SomeD)
  by (metis kernel_object.distinct(1) option.inject)

lemma dmo_machine_state_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P (machine_state s)\<rbrace> do_machine_op f \<lbrace>\<lambda>rv s. Q rv (machine_state s)\<rbrace>"
  unfolding do_machine_op_def by wpsimp (erule use_valid; assumption)

lemma as_user_valid_irq_states[wp]:
  "\<lbrace>valid_irq_states\<rbrace> as_user t f \<lbrace>\<lambda>rv. valid_irq_states\<rbrace>"
  unfolding as_user_def
  by (wpsimp wp: set_object_wp simp: obj_at_def valid_irq_states_def)

lemma as_user_ioc[wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (is_original_cap s)\<rbrace>"
  unfolding as_user_def by (wpsimp wp: set_object_wp)

lemma as_user_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> as_user t f \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  unfolding valid_ioc_def by (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift)

lemma arch_finalise_cap_invs' [wp,Finalise_AI_assms]:
  "\<lbrace>invs and valid_cap (ArchObjectCap cap)\<rbrace>
     arch_finalise_cap cap final
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (wp unmap_page_invs | wpc)+
  apply (clarsimp simp: valid_cap_def cap_aligned_def)
  apply (auto simp: mask_def vmsz_aligned_def wellformed_mapdata_def)
  done

lemma as_user_unlive[wp]:
  "\<lbrace>obj_at (Not \<circ> live) vr\<rbrace> as_user t f \<lbrace>\<lambda>_. obj_at (Not \<circ> live) vr\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_def live_def hyp_live_def arch_tcb_context_set_def dest!: get_tcb_SomeD)

lemma obj_at_not_live_valid_arch_cap_strg [Finalise_AI_assms]:
  "(s \<turnstile> ArchObjectCap cap \<and> aobj_ref cap = Some r)
        \<longrightarrow> obj_at (\<lambda>ko. \<not> live ko) r s"
  by (clarsimp simp: valid_cap_def obj_at_def valid_arch_cap_ref_def
                     a_type_arch_live live_def hyp_live_def
              split: arch_cap.split_asm if_splits)

crunch set_vm_root
  for ptes_of[wp]: "\<lambda>s. P (ptes_of s)"
  and asid_pools_of[wp]: "\<lambda>s. P (asid_pools_of s)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  (simp: crunch_simps)

lemma set_vm_root_vs_lookup_target[wp]:
  "set_vm_root tcb \<lbrace>\<lambda>s. P (vs_lookup_target level asid vref s)\<rbrace>"
  by (wpsimp wp: vs_lookup_target_lift)

lemma vs_lookup_target_no_asid_pool:
  "\<lbrakk>asid_pool_at ptr s; valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
    vs_lookup_target level asid 0 s = Some (level, ptr)\<rbrakk>
   \<Longrightarrow> False"
  apply (clarsimp simp: vs_lookup_target_def split: if_split_asm)
   apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def obj_at_def)
   apply (frule (1) pool_for_asid_validD, clarsimp)
   apply (subst (asm) pool_for_asid_vs_lookup[symmetric, where vref=0 and level=asid_pool_level, simplified])
   apply (drule (1) valid_vspace_objsD; simp add: in_omonad)
   apply (fastforce simp: vspace_for_pool_def in_omonad obj_at_def ran_def)
  apply (rename_tac pt_ptr)
  apply (clarsimp simp: vs_lookup_slot_def obj_at_def split: if_split_asm)
  apply (clarsimp simp: in_omonad)
  apply (frule (1) vs_lookup_table_is_aligned; clarsimp?)
  apply (clarsimp simp: ptes_of_def)
  apply (drule (1) valid_vspace_objsD; simp add: in_omonad)
  apply (simp add: is_aligned_mask)
  apply (drule_tac x=0 in bspec)
   apply (clarsimp simp: kernel_mapping_slots_def pptr_base_def pptrBase_def pt_bits_left_def
                         bit_simps level_defs canonical_bit_def)
  apply (clarsimp simp: pte_ref_def data_at_def obj_at_def split: pte.splits)
  done


lemma delete_asid_pool_not_target[wp]:
  "\<lbrace>asid_pool_at ptr and valid_vspace_objs and valid_asid_table and pspace_aligned\<rbrace>
   delete_asid_pool asid ptr
   \<lbrace>\<lambda>rv s. vs_lookup_target level asid 0 s \<noteq> Some (level, ptr)\<rbrace>"
  unfolding delete_asid_pool_def
  supply fun_upd_apply[simp del]
  apply wpsimp
  apply (rule conjI; clarsimp)
   apply (frule vs_lookup_target_no_asid_pool[of _ _ level asid]; assumption?)
   apply (erule vs_lookup_target_clear_asid_table)
  apply (erule (4) vs_lookup_target_no_asid_pool)
  done

lemma delete_asid_pool_not_reachable[wp]:
  "\<lbrace>asid_pool_at ptr and valid_vspace_objs and valid_asid_table and pspace_aligned\<rbrace>
   delete_asid_pool asid ptr
   \<lbrace>\<lambda>rv s. \<not> reachable_target (asid, 0) ptr s\<rbrace>"
  unfolding reachable_target_def by (wpsimp wp: hoare_vcg_all_lift)

lemmas reachable_frame_cap_simps =
  reachable_frame_cap_def[unfolded is_frame_cap_def arch_cap_fun_lift_def, split_simps cap.split]

lemma vs_lookup_slot_non_PageTablePTE:
  "\<lbrakk> ptes_of s p \<noteq> None; ptes_of s' = (ptes_of s)(p \<mapsto> pte); \<not> is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s;
     asid_table s' = asid_table s; valid_asid_table s; pspace_aligned s\<rbrakk>
  \<Longrightarrow> vs_lookup_slot level asid vref s' =
      (if \<exists>level'. vs_lookup_slot level' asid vref s = Some (level', p) \<and> level < level'
       then vs_lookup_slot (level_of_slot asid vref p s) asid vref s
       else vs_lookup_slot level asid vref s)"
  apply clarsimp
  apply (rule conjI; clarsimp;
           (simp (no_asm) add: vs_lookup_slot_def obind_def,
            (subst vs_lookup_non_PageTablePTE; simp),
            fastforce split: option.splits))
  done

lemma unmap_page_table_pool_for_asid[wp]:
  "unmap_page_table asid vref pt \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  unfolding unmap_page_table_def by (wpsimp simp: pool_for_asid_def)

lemma unmap_page_table_unreachable:
  "\<lbrace> pt_at pt and valid_asid_table and valid_vspace_objs and pspace_aligned
     and unique_table_refs and valid_vs_lookup and (\<lambda>s. valid_caps (caps_of_state s) s)
     and K (0 < asid \<and> vref \<in> user_region)
     and (\<lambda>s. vspace_for_asid asid s \<noteq> Some pt) \<rbrace>
   unmap_page_table asid vref pt
   \<lbrace>\<lambda>_ s. \<not> reachable_target (asid, vref) pt s\<rbrace>"
  unfolding reachable_target_def
  apply (wpsimp wp: hoare_vcg_all_lift unmap_page_table_not_target)
  apply (drule (1) pool_for_asid_validD)
  apply (clarsimp simp: obj_at_def in_omonad)
  done

lemma unmap_page_unreachable:
  "\<lbrace> data_at pgsz pptr and valid_asid_table and valid_vspace_objs and pspace_aligned
     and unique_table_refs and valid_vs_lookup and (\<lambda>s. valid_caps (caps_of_state s) s)
     and K (0 < asid \<and> vref \<in> user_region) \<rbrace>
   unmap_page pgsz asid vref pptr
   \<lbrace>\<lambda>rv s. \<not> reachable_target (asid, vref) pptr s\<rbrace>"
  unfolding reachable_target_def
  apply (wpsimp wp: hoare_vcg_all_lift unmap_page_not_target)
  apply (drule (1) pool_for_asid_validD)
  apply (clarsimp simp: obj_at_def data_at_def in_omonad)
  done

lemma set_asid_pool_pool_for_asid[wp]:
  "set_asid_pool ptr pool \<lbrace>\<lambda>s. P (pool_for_asid asid' s)\<rbrace>"
  unfolding pool_for_asid_def by wpsimp

lemma delete_asid_pool_for_asid[wp]:
  "delete_asid asid pt \<lbrace>\<lambda>s. P (pool_for_asid asid' s)\<rbrace>"
  unfolding delete_asid_def by wpsimp

lemma delete_asid_no_vs_lookup_target:
  "\<lbrace>\<lambda>s. vspace_for_asid asid s = Some pt\<rbrace>
   delete_asid asid pt
   \<lbrace>\<lambda>rv s. vs_lookup_target level asid vref s \<noteq> Some (level, pt)\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (prop_tac "0 < asid")
   apply (clarsimp simp: vspace_for_asid_def)
  apply (rule hoare_strengthen_post, rule delete_asid_unmapped)
  apply (clarsimp simp: vs_lookup_target_def split: if_split_asm)
   apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def split: if_split_asm)
   apply (clarsimp simp: vspace_for_asid_def obind_def)
  apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def split: if_split_asm)
  apply (clarsimp simp: vspace_for_asid_def obind_def)
  done

lemma delete_asid_unreachable:
  "\<lbrace>\<lambda>s. vspace_for_asid asid s = Some pt \<and> pt_at pt s \<and> valid_asid_table s \<rbrace>
   delete_asid asid pt
   \<lbrace>\<lambda>_ s. \<not> reachable_target (asid, vref) pt s\<rbrace>"
  unfolding reachable_target_def
  apply (wpsimp wp: hoare_vcg_all_lift delete_asid_no_vs_lookup_target)
  apply (drule (1) pool_for_asid_validD)
  apply (clarsimp simp: obj_at_def in_omonad)
  done

(* FIXME: move to ArchInvariants or similar *)
lemma FrameCap_data_at:
  "s \<turnstile> ArchObjectCap (FrameCap r R vmsz d m) \<Longrightarrow> data_at vmsz r s"
  by (simp add: valid_cap_def obj_at_def data_at_def split: if_splits)

lemma arch_finalise_cap_replaceable[wp]:
  notes simps = replaceable_def and_not_not_or_imp
                is_cap_simps vs_cap_ref_def tcb_cap_valid_imp_NullCap
                no_cap_to_obj_with_diff_ref_Null o_def
                reachable_frame_cap_simps
  notes wps = hoare_drop_imp[where Q'="%_. is_final_cap' cap" for cap]
              valid_cap_typ  unmap_page_unreachable unmap_page_table_unreachable
              delete_asid_unreachable
  shows
    "\<lbrace>\<lambda>s. s \<turnstile> cap.ArchObjectCap cap \<and>
          x = is_final_cap' (cap.ArchObjectCap cap) s \<and>
          pspace_aligned s \<and> valid_vspace_objs s \<and> valid_objs s \<and> valid_asid_table s \<and>
          valid_arch_caps s\<rbrace>
     arch_finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) (cap.ArchObjectCap cap)\<rbrace>"
  apply (simp add: arch_finalise_cap_def simps split: option.splits vmpage_size.splits)
  apply (wp wps |
         strengthen obj_at_not_live_valid_arch_cap_strg[where cap=cap] |
         simp add: simps |
         wpc)+
  by (clarsimp simp: valid_objs_caps valid_arch_caps_def valid_cap_def wellformed_mapdata_def data_at_def
      | rule conjI)+


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
  apply (clarsimp dest!: obj_ref_none_no_asid[rule_format])
  done

lemma prepare_thread_delete_no_cap_to_obj_ref[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     prepare_thread_delete t
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  unfolding prepare_thread_delete_def by wpsimp

lemma prepare_thread_delete_unlive_hyp:
  "\<lbrace>obj_at \<top> ptr\<rbrace> prepare_thread_delete ptr \<lbrace>\<lambda>rv. obj_at (Not \<circ> hyp_live) ptr\<rbrace>"
  apply (simp add: prepare_thread_delete_def)
  apply (wpsimp simp: obj_at_def is_tcb_def hyp_live_def)
  done

lemma prepare_thread_delete_unlive0:
  "\<lbrace>obj_at (Not \<circ> live0) ptr\<rbrace> prepare_thread_delete ptr \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) ptr\<rbrace>"
  by (simp add: prepare_thread_delete_def)

lemma prepare_thread_delete_unlive[wp]:
  "\<lbrace>obj_at (Not \<circ> live0) ptr\<rbrace> prepare_thread_delete ptr \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (rule_tac Q'="\<lambda>rv. obj_at (Not \<circ> live0) ptr and obj_at (Not \<circ> hyp_live) ptr" in hoare_strengthen_post)
  apply (wpsimp wp: hoare_vcg_conj_lift prepare_thread_delete_unlive_hyp prepare_thread_delete_unlive0)
   apply (clarsimp simp: obj_at_def)
  apply (fastforce simp: obj_at_def live_def arch_tcb_live_def
                  split: kernel_object.splits)
  done

lemma set_thread_state_not_live:
  "\<lbrace>bound_tcb_at ((=) None) t and bound_sc_tcb_at ((=) None) t
    and bound_yt_tcb_at ((=) None) t\<rbrace>
   set_thread_state t Inactive
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) t\<rbrace>"
  by (wpsimp simp: set_thread_state_def obj_at_def pred_tcb_at_def get_tcb_def live_def hyp_live_def
                   arch_tcb_live_def
             wp: set_object_wp)

lemma sched_context_cancel_yield_to_unlive:
  "\<lbrace>bound_tcb_at ((=) None) t and bound_sc_tcb_at ((=) None) t and st_tcb_at ((=) Inactive) t\<rbrace>
   sched_context_cancel_yield_to t
   \<lbrace>\<lambda>_. obj_at (Not \<circ> live) t\<rbrace>"
  apply (clarsimp simp: sched_context_cancel_yield_to_def)
  apply (rule bind_wp[OF _ gyt_sp])
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def update_sched_context_def get_object_def
                      pred_tcb_at_def obj_at_def get_tcb_def live_def hyp_live_def arch_tcb_live_def)
  done

lemma suspend_unlive':
  "\<lbrace>bound_tcb_at ((=) None) t and bound_sc_tcb_at ((=) None) t\<rbrace>
   suspend t
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) t\<rbrace>"
  unfolding suspend_def
  apply (simp flip: bind_assoc)
  apply (rule bind_wp[OF sched_context_cancel_yield_to_unlive])
  apply (simp add: bind_assoc)
  apply (wpsimp wp: get_object_wp cancel_ipc_bound_sc_tcb_at_None)
  done

method hammer = ((clarsimp simp: o_def dom_tcb_cap_cases_lt_ARCH
                                 ran_tcb_cap_cases is_cap_simps
                                 cap_range_def prepare_thread_delete_def
                                 can_fast_finalise_def
                                 gen_obj_refs_subset
                                 vs_cap_ref_def
                                 valid_ipc_buffer_cap_def valid_fault_handler_def
                           dest!: tcb_cap_valid_NullCapD
                           split: Structures_A.thread_state.split_asm
                   | simp cong: conj_cong
                   | simp cong: rev_conj_cong add: no_cap_to_obj_with_diff_ref_Null
                   | (strengthen tcb_cap_valid_imp_NullCap tcb_cap_valid_imp', wp)
                   | erule cte_wp_at_weakenE tcb_cap_valid_imp'[rule_format, rotated -1]
                   | erule(1) no_cap_to_obj_with_diff_ref_finalI_ARCH
                   | ((wp (once) hoare_drop_imps)?,
                      (wp (once) hoare_drop_imps)?,
                      wp (once) deleting_irq_handler_empty)
                   | simp add: valid_cap_simps)+)[1]

lemma finalise_cap_replaceable [Finalise_AI_assms]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s
        \<and> cte_wp_at ((=) cap) sl s \<and> invs s
        \<and> (cap_irqs cap \<noteq> {} \<longrightarrow> if_unsafe_then_cap s \<and> valid_global_refs s)
        \<and> (is_arch_cap cap \<longrightarrow> pspace_aligned s \<and>
                               valid_vspace_objs s \<and>
                               valid_arch_state s \<and>
                               valid_arch_caps s)\<rbrace>
     finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) cap\<rbrace>"
  apply (cases "is_arch_cap cap")
   apply (clarsimp simp: is_cap_simps)
   apply wp
   apply (clarsimp simp: replaceable_def reachable_frame_cap_def
                         o_def cap_range_def valid_arch_state_def
                         ran_tcb_cap_cases is_cap_simps
                         gen_obj_refs_subset vs_cap_ref_def)
  apply (cases cap; simp add: replaceable_def reachable_frame_cap_def
                         split del: if_split)
               \<comment> \<open>NullCap\<close>
               apply (rule hoare_pre)
                apply (wpsimp, clarsimp)
              \<comment> \<open>untyped\<close>
              apply (wpsimp)
              apply hammer
             \<comment> \<open>endpoint\<close>
             apply ((wpsimp
                    | hammer
                    | (wp (once) hoare_drop_imps,
                       wp (once) reply_unlink_sc_not_live'[unfolded o_def]
                                 cancel_all_ipc_unlive[unfolded o_def]
                                 cancel_all_signals_unlive[unfolded o_def]))+)[2]
             apply fastforce
           \<comment> \<open>ntfn\<close>
            apply ((wpsimp wp: unbind_maybe_notification_not_live_helper sched_context_maybe_unbind_ntfn_not_bound_sc
                    | hammer
                    | (wp (once) hoare_drop_imps, wp (once) reply_unlink_sc_not_live'[unfolded o_def]
                            cancel_all_ipc_unlive[unfolded o_def]
                            cancel_all_signals_unlive[unfolded o_def]))+)[1]
           \<comment> \<open>reply\<close>
           apply ((wpsimp wp: unbind_maybe_notification_not_live_helper sched_context_maybe_unbind_ntfn_not_bound_sc | hammer)+)[1]
                     apply (wp (once) hoare_drop_imps, rule hoare_vcg_conj_lift,
                             wp (once) cancel_ipc_unlive_reply_receive[unfolded o_def], hammer)
                    apply ((wpsimp wp: gts_wp get_simple_ko_wp | hammer | wp (once) hoare_drop_imps, rule hoare_vcg_conj_lift,
                             wp (once) cancel_ipc_unlive_reply_receive[unfolded o_def] reply_remove_unlive[unfolded o_def])+)[9]
           apply (auto simp: obj_at_def is_cap_simps ran_tcb_cap_cases valid_ipc_buffer_cap_def pred_tcb_at_def
                             live_def live_reply_def vs_cap_ref_def no_cap_to_obj_with_diff_ref_Null
                             invs_reply_tcb_None_reply_sc_None
                      intro: valid_NullCapD
                      dest!: reply_tcb_state_refs)[1]
          \<comment> \<open>Cnode\<close>
          apply ((wpsimp | hammer)+)[1]
          apply (rule conjI)
           apply (clarsimp simp: obj_at_def)
           apply (case_tac ko; clarsimp simp: is_cap_table_def[split_simps kernel_object.split] live_def)
          apply (rule conjI, clarsimp simp: unat_of_bl_length)
          apply (rule conjI, clarsimp)
           apply (erule tcb_cap_valid_imp'[rule_format, rotated -1])
           apply hammer
          apply hammer
         \<comment> \<open>tcb\<close>
         apply ((wpsimp wp: suspend_final_cap suspend_unlive'[unfolded o_def]
                            unbind_from_sc_bound_sc_tcb_at
                 | hammer | rule conjI)+)[1]
        \<comment> \<open>domain\<close>
        apply ((wpsimp | hammer)+)[1]
       \<comment> \<open>schedcontext\<close>
       apply ((wpsimp wp: sched_context_unbind_ntfn_unbinds
                         sched_context_unbind_all_tcbs_unbinds
                         finalise_cap_replaceable_helper
                   simp: no_cap_to_idle_sc_ptr
              | hammer
              | wp (once) sched_context_unbind_yield_from_not_live[unfolded o_def]
              | wp (once) hoare_drop_imps; wp (once) hoare_vcg_conj_lift,
                wp (once) sched_context_set_inactive_not_live[unfolded o_def])+)[1]
     \<comment> \<open>schedcontrol\<close>
      apply ((wpsimp | hammer)+)[1]
     \<comment> \<open>irqcontrol\<close>
     apply ((wpsimp | hammer)+)[1]
    \<comment> \<open>irqhandler\<close>
    apply ((wpsimp | hammer)+)[1]
    apply fastforce
   \<comment> \<open>zombie\<close>
   apply ((wpsimp | hammer)+)[1]
  \<comment> \<open>arch\<close>
  apply (clarsimp simp: is_cap_simps)
  done

lemma (* deleting_irq_handler_cte_preserved *)[Finalise_AI_assms]:
  assumes x: "\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap"
  shows "\<lbrace>cte_wp_at P p\<rbrace> deleting_irq_handler irq \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_cte_wp_at_preserved | simp add: x)+
  done

crunch prepare_thread_delete, arch_finalise_cap
  for cte_wp_at[wp, Finalise_AI_assms]: "\<lambda>s. P (cte_wp_at P' p s)"
  and cur[wp, Finalise_AI_assms]: "\<lambda>s. P (cur_thread s)"
  (simp: crunch_simps assertE_def wp: crunch_wps set_object_cte_at
   ignore: arch_thread_set)

end

interpretation Finalise_AI_1?: Finalise_AI_1
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_assms)?)
qed

context Arch begin arch_global_naming

lemma fast_finalise_replaceable[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s \<and> cte_wp_at ((=) cap) sl s \<and> invs s\<rbrace>
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
  "\<lbrace>invs\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def is_final_cap_def)
  apply (rule hoare_pre)
  apply (wp empty_slot_invs get_cap_wp fast_finalise_invs)
  apply (clarsimp simp del: split_paired_Ex)
  apply (intro conjI; fastforce?)
  apply (drule cte_wp_at_valid_objs_valid_cap, fastforce+)
  done

end

interpretation Finalise_AI_2?: Finalise_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_assms)?)
  qed

context Arch begin arch_global_naming

crunch prepare_thread_delete
  for irq_node[Finalise_AI_assms,wp]: "\<lambda>s. P (interrupt_irq_node s)"

crunch arch_finalise_cap
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps wp: crunch_wps)

crunch
  delete_asid_pool, delete_asid, unmap_page_table, unmap_page
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"
  (simp: crunch_simps wp: crunch_wps test)

crunch arch_finalise_cap
  for pred_tcb_at[wp_unsafe]: "pred_tcb_at proj P t"
  (simp: crunch_simps wp: crunch_wps)

definition
  replaceable_or_arch_update :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> bool" where
  "replaceable_or_arch_update \<equiv> \<lambda>s slot cap cap'.
   if is_frame_cap cap
   then is_arch_update cap cap' \<and>
        (\<forall>asid vref. vs_cap_ref cap' = Some (asid,vref) \<longrightarrow>
           vs_cap_ref cap = Some (asid,vref) \<and>
           obj_refs cap = obj_refs cap' \<or>
           (\<forall>oref\<in>obj_refs cap'. \<forall>level. vs_lookup_target level asid vref s \<noteq> Some (level, oref)))
   else replaceable s slot cap cap'"

lemma is_final_cap_pt_asid_eq:
  "is_final_cap' (ArchObjectCap (PageTableCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PageTableCap p x)) s"
  apply (clarsimp simp: is_final_cap'_def gen_obj_refs_def)
  done

lemma is_final_cap_pd_asid_eq:
  "is_final_cap' (ArchObjectCap (PageTableCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PageTableCap p x)) s"
  by (rule is_final_cap_pt_asid_eq)

lemma cte_wp_at_obj_refs_singleton_page_table:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PageTableCap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at ((=) (ArchObjectCap (PageTableCap p asid))) (a,b) s"
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

lemma is_arch_update_reset_page:
  "is_arch_update
     (ArchObjectCap (FrameCap p r sz dev m))
     (ArchObjectCap (FrameCap p r' sz dev m'))"
  apply (simp add: is_arch_update_def is_arch_cap_def cap_master_cap_def)
  done

context notes if_cong[cong] begin
crunch arch_finalise_cap
 for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
   (wp: crunch_wps simp: crunch_simps)
end

lemma set_vm_root_empty[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (empty_table S) p s)\<rbrace> set_vm_root v \<lbrace>\<lambda>_ s. P (obj_at (empty_table S) p s) \<rbrace>"
  apply (simp add: set_vm_root_def)
  apply (wpsimp wp: get_cap_wp)
  done

lemma ucast_less_shiftl_helper3:
  "\<lbrakk> len_of TYPE('b) + 3 < len_of TYPE('a); 2 ^ (len_of TYPE('b) + 3) \<le> n\<rbrakk>
    \<Longrightarrow> (ucast (x :: 'b::len word) << 3) < (n :: 'a::len word)"
  apply (erule order_less_le_trans[rotated])
  using ucast_less[where x=x and 'a='a]
  apply (simp only: shiftl_t2n field_simps)
  apply (rule word_less_power_trans2; simp)
  done

lemma caps_of_state_aligned_page_table:
  "\<lbrakk>caps_of_state s slot = Some (ArchObjectCap (PageTableCap word option)); invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pt_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pt_bits_def pageBits_def)
  done

end

lemma invs_valid_arch_capsI:
  "invs s \<Longrightarrow> valid_arch_caps s"
  by (simp add: invs_def valid_state_def)

context Arch begin arch_global_naming

lemma do_machine_op_reachable_pg_cap[wp]:
  "\<lbrace>\<lambda>s. P (reachable_frame_cap cap s)\<rbrace>
   do_machine_op mo
   \<lbrace>\<lambda>rv s. P (reachable_frame_cap cap s)\<rbrace>"
  apply (simp add:reachable_frame_cap_def reachable_target_def)
  apply (wp_pre, wps dmo.vs_lookup_pages, wpsimp)
  apply simp
  done

lemma replaceable_or_arch_update_pg:
  " (case (vs_cap_ref (ArchObjectCap (FrameCap word fun vm_pgsz dev y))) of None \<Rightarrow> True | Some (asid,vref) \<Rightarrow>
     \<forall>level. vs_lookup_target level asid vref s \<noteq> Some (level, word))
  \<longrightarrow> replaceable_or_arch_update s slot (ArchObjectCap (FrameCap word fun vm_pgsz dev None))
                (ArchObjectCap (FrameCap word fun vm_pgsz dev y))"
  unfolding replaceable_or_arch_update_def
  apply (auto simp: is_cap_simps is_arch_update_def cap_master_cap_simps)
  done


crunch prepare_thread_delete
  for invs[wp]: invs
  (ignore: set_object)

lemma (* finalise_cap_invs *)[Finalise_AI_assms]:
  "\<lbrace>invs and cte_wp_at ((=) cap) slot\<rbrace> finalise_cap cap x \<lbrace>\<lambda>_ s. invs s\<rbrace>"
  apply (cases cap, simp_all split del: if_split)
               prefer 7
               apply (wpsimp wp: suspend_invs unbind_notification_invs)
               apply (frule (1) cte_wp_valid_cap[OF _ invs_valid_objs])
               apply (fastforce simp: invs_def valid_state_def valid_idle_def cap_range_def
                                      valid_cap_def2 valid_cap_ref_simps
                               dest!: valid_global_refsD)
              apply (wp cancel_all_ipc_invs cancel_all_signals_invs gts_wp
                        unbind_maybe_notification_invs get_simple_ko_wp  reply_remove_invs
                        sched_context_unbind_yield_from_invs
                    | simp add: o_def split del: if_split cong: if_cong
                    | wpc
                    | solves \<open>clarsimp dest!: no_cap_to_idle_sc_ptr\<close>
                    | solves \<open> clarsimp,
                               (frule (2) reply_tcb_state_refs[OF _ invs_valid_objs invs_sym_refs],
                                fastforce simp: obj_at_def),
                                (auto simp: reply_tcb_reply_at_def pred_tcb_at_def obj_at_def)\<close>)+
  apply clarsimp
  apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp)
  apply (clarsimp simp: valid_cap_def)
  done

lemma (* finalise_cap_irq_node *)[Finalise_AI_assms]:
  "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> finalise_cap a b \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  supply if_cong[cong]
  apply (case_tac a; simp)
         apply (wpsimp wp: hoare_drop_imps simp: o_def)+
  done

lemmas (*arch_finalise_cte_irq_node *) [wp,Finalise_AI_assms]
    = hoare_use_eq_irq_node [OF arch_finalise_cap_irq_node arch_finalise_cap_cte_wp_at]

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
  apply (cases "is_frame_cap cap")
   apply (wp hoare_pre_disj[OF arch_update_cap_invs_unmap_page arch_update_cap_invs_map])
   apply (simp add:replaceable_or_arch_update_def replaceable_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps gen_obj_refs_def
                         cap_master_cap_simps is_arch_update_def)
  apply (wp replace_cap_invs)
  apply simp
  done

lemma dmo_pred_tcb_at[wp]:
  "do_machine_op mop \<lbrace>\<lambda>s. P (pred_tcb_at f Q t s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma dmo_tcb_cap_valid_ARCH [Finalise_AI_assms]:
  "do_machine_op mop \<lbrace>\<lambda>s. P (tcb_cap_valid cap ptr s)\<rbrace>"
  apply (simp add: tcb_cap_valid_def no_cap_to_obj_with_diff_ref_def)
  apply (wp_pre, wps, rule hoare_vcg_prop)
  apply simp
  done

lemma dmo_vs_lookup_target[wp]:
  "do_machine_op mop \<lbrace>\<lambda>s. P (vs_lookup_target level asid vref s)\<rbrace>"
  by (rule dmo.vs_lookup_pages)

lemma dmo_reachable_target[wp]:
  "do_machine_op mop \<lbrace>\<lambda>s. P (reachable_target ref p s)\<rbrace>"
  apply (simp add: reachable_target_def split_def)
  apply (wp_pre, wps, wp)
  apply simp
  done

lemma (* dmo_replaceable_or_arch_update *) [Finalise_AI_assms,wp]:
  "\<lbrace>\<lambda>s. replaceable_or_arch_update s slot cap cap'\<rbrace>
    do_machine_op mo
  \<lbrace>\<lambda>r s. replaceable_or_arch_update s slot cap cap'\<rbrace>"
  unfolding replaceable_or_arch_update_def replaceable_def no_cap_to_obj_with_diff_ref_def
            replaceable_final_arch_cap_def replaceable_non_final_arch_cap_def
  supply if_cong[cong]
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

locale_abbrev
  "asid_table_update asid ap s \<equiv>
     s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (asid_table s)(asid \<mapsto> ap)\<rparr>\<rparr>"

lemma valid_table_caps_table [simp]:
  "valid_table_caps (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := table'\<rparr>\<rparr>) = valid_table_caps s"
  by (simp add: valid_table_caps_def)

lemma valid_kernel_mappings [iff]:
  "valid_kernel_mappings (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := table'\<rparr>\<rparr>) = valid_kernel_mappings s"
  by (simp add: valid_kernel_mappings_def)

crunch unmap_page_table, store_pte, delete_asid_pool, copy_global_mappings
  for valid_cap[wp]: "valid_cap c"
  (wp: mapM_wp_inv mapM_x_wp' simp: crunch_simps)

lemmas delete_asid_typ_ats[wp] = abs_typ_at_lifts [OF delete_asid_typ_at]

lemma arch_finalise_cap_valid_cap[wp]:
  "arch_finalise_cap cap b \<lbrace>valid_cap c\<rbrace>"
  unfolding arch_finalise_cap_def
  by (wpsimp split: arch_cap.split option.split bool.split)

lemmas clearMemory_invs[wp,Finalise_AI_assms] = clearMemory_invs

lemma valid_idle_has_null_cap_ARCH[Finalise_AI_assms]:
  "\<lbrakk> if_unsafe_then_cap s; valid_global_refs s; valid_idle s; valid_irq_node s;
    caps_of_state s (idle_thread s, v) = Some cap \<rbrakk>
   \<Longrightarrow> cap = NullCap"
  apply (rule ccontr)
  apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
   apply clarsimp
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (frule(1) valid_global_refsD2)
  apply (case_tac capa, simp_all add: cap_range_def global_refs_def)[1]
  apply (clarsimp simp: valid_irq_node_def valid_idle_def pred_tcb_at_def
                        obj_at_def is_cap_table_def)
  apply (rename_tac word tcb sc)
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
