(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalise_AI
imports Finalise_AI
begin

context Arch begin

named_theorems Finalise_AI_asms

lemma obj_at_not_live_valid_arch_cap_strg [Finalise_AI_asms]:
  "(s \<turnstile> ArchObjectCap cap \<and> aobj_ref cap = Some r)
        \<longrightarrow> obj_at (\<lambda>ko. \<not> live ko) r s"
  by (clarsimp simp: valid_cap_def obj_at_def
                     a_type_arch_live live_def hyp_live_def
              split: arch_cap.split_asm if_splits)

global_naming X64

lemma valid_global_refs_asid_table_udapte [iff]:
  "valid_global_refs (s\<lparr>arch_state := x64_asid_table_update f (arch_state s)\<rparr>) =
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

(* FIXME x64: this needs stuff about equality between vs_lookup and vs_lookup_pages
              for PageMapL4, PDPTs *)
lemma vs_lookup_pages_eq:
  "\<lbrakk>valid_vspace_objs s; valid_asid_table (x64_asid_table (arch_state s)) s;
    valid_cap cap s; table_cap_ref cap = Some vref; oref \<in> obj_refs cap\<rbrakk>
   \<Longrightarrow> (vref \<unrhd> oref) s = (vref \<rhd> oref) s"
  apply (clarsimp simp: table_cap_ref_def
                        vs_lookup_pages_eq_at[symmetric, THEN fun_cong]
                        vs_lookup_pages_eq_ap[symmetric, THEN fun_cong]
                 split: cap.splits arch_cap.splits option.splits)
  apply (rule iffI[rotated, OF vs_lookup_pages_vs_lookupI], assumption, (simp add: valid_cap_def),
           (erule vs_lookup_vs_lookup_pagesI', clarsimp+))+
  done

lemma nat_to_cref_unat_of_bl':
  "\<lbrakk> length xs < word_bits; n = length xs \<rbrakk> \<Longrightarrow>
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

lemma invs_x64_asid_table_unmap:
  "invs s \<and> is_aligned base asid_low_bits
       \<and> tab = x64_asid_table (arch_state s)
     \<longrightarrow> invs (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
  apply (strengthen valid_vspace_objs_unmap_strg
                    valid_vs_lookup_unmap_strg valid_arch_state_unmap_strg)
  apply (simp add: valid_irq_node_def valid_kernel_mappings_def
                   valid_global_objs_arch_update valid_asid_map_def)
  apply (simp add: valid_table_caps_def valid_machine_state_def second_level_tables_def)
  apply (simp add: valid_ioports_def all_ioports_issued_def issued_ioports_def)
  done

lemma delete_asid_pool_invs[wp]:
  "\<lbrace>invs\<rbrace> delete_asid_pool base pptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: delete_asid_pool_def)
  apply wp
      apply (strengthen invs_x64_asid_table_unmap)
      apply (wpsimp wp: mapM_wp', simp)
     apply (wp+)[3]
  apply (clarsimp simp: ucast_zero_is_aligned asid_bits_of_defs asid_bits_defs)
  done

lemma delete_asid_invs[wp]:
  "\<lbrace>invs\<rbrace> delete_asid asid pd \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: delete_asid_def cong: option.case_cong)
  apply (wpsimp wp: set_asid_pool_invs_unmap)
  done

crunch vs_lookup[wp]: set_vm_root "\<lambda>s. P (vs_lookup s)"
  (wp: crunch_wps simp: crunch_simps vs_lookup_arch_update)

lemma delete_asid_pool_unmapped[wp]:
  "\<lbrace>\<top>\<rbrace>
     delete_asid_pool asid poolptr
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> poolptr) s\<rbrace>"
  apply (simp add: delete_asid_pool_def)
  apply wp
    apply (rule hoare_strengthen_post [where Q="\<lambda>_. \<top>"])
     apply wp+
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
   \<lbrace>\<lambda>rv s.  \<not> ([VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
                VSRef (ucast (asid_high_bits_of asid)) None]  \<rhd> pd) s\<rbrace>"
  apply (simp add: delete_asid_def
                   mask_asid_low_bits_ucast_ucast
             cong: option.case_cong)
  apply (wp set_asid_pool_unmap hoare_vcg_all_lift hoare_vcg_imp_lift hw_asid_invalidate_vs_lookup
           | wpc
           | simp add: if_apply_def2 split del: if_split)+
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

lemma set_pt_tcb_at_arch[simplified, wp]:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pt a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: valid_def obj_at_def set_object_def get_object_def
                     in_monad a_type_simps set_arch_obj_simps)

lemma set_pd_tcb_at_arch[simplified, wp]:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pd a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: valid_def obj_at_def set_object_def get_object_def
                     in_monad a_type_simps set_arch_obj_simps)

lemma set_pdpt_tcb_at_arch[simplified, wp]:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pdpt a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: valid_def obj_at_def set_object_def get_object_def
                     in_monad a_type_simps set_arch_obj_simps)

lemma set_pml4_tcb_at_arch[simplified, wp]:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pml4 a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: valid_def obj_at_def set_object_def get_object_def
                     in_monad a_type_simps set_arch_obj_simps)

crunch tcb_at_arch: unmap_page "\<lambda>s. P (ko_at (TCB tcb) t s)"
    (simp: crunch_simps wp: crunch_wps ignore: set_pt set_pd set_pdpt)

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

global_naming Arch

lemma (* replaceable_cdt_update *)[simp,Finalise_AI_asms]:
  "replaceable (cdt_update f s) = replaceable s"
  by (fastforce simp: replaceable_def tcb_cap_valid_def)

lemma (* replaceable_revokable_update *)[simp,Finalise_AI_asms]:
  "replaceable (is_original_cap_update f s) = replaceable s"
  by (fastforce simp: replaceable_def is_final_cap'_def2 tcb_cap_valid_def)

lemma (* replaceable_more_update *) [simp,Finalise_AI_asms]:
  "replaceable (trans_state f s) sl cap cap' = replaceable s sl cap cap'"
  by (simp add: replaceable_def)

lemma (* obj_ref_ofI *) [Finalise_AI_asms]: "obj_refs cap = {x} \<Longrightarrow> obj_ref_of cap = x"
  by (case_tac cap, simp_all) (rename_tac arch_cap, case_tac arch_cap, simp_all)

lemma (* empty_slot_invs *) [Finalise_AI_asms]:
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
                  set_cap_ioports_no_new_ioports
      | simp add: trans_state_update[symmetric]
             del: trans_state_update fun_upd_apply
       split del: if_split )+
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
   apply (clarsimp simp: valid_arch_mdb_def ioport_revocable_def)
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

lemma dom_tcb_cap_cases_lt_ARCH [Finalise_AI_asms]:
  "dom tcb_cap_cases = {xs. length xs = 3 \<and> unat (of_bl xs :: machine_word) < 5}"
  apply (rule set_eqI, rule iffI)
   apply clarsimp
   apply (simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1 split: if_split_asm)
  apply clarsimp
  apply (frule tcb_cap_cases_lt)
  apply (clarsimp simp: nat_to_cref_unat_of_bl'[simplified word_bits_def])
  done

lemma (* unbind_notification_final *) [wp,Finalise_AI_asms]:
  "\<lbrace>is_final_cap' cap\<rbrace> unbind_notification t \<lbrace> \<lambda>rv. is_final_cap' cap\<rbrace>"
  unfolding unbind_notification_def
  apply (wp final_cap_lift thread_set_caps_of_state_trivial hoare_drop_imps
       | wpc | simp add: tcb_cap_cases_def)+
  done

crunch is_final_cap'[wp]: prepare_thread_delete "is_final_cap' cap"

lemma (* finalise_cap_cases1 *)[Finalise_AI_asms]:
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
                                  can_fast_finalise_def cap_cleanup_opt_def
                                  appropriate_cte_cap_def gen_obj_refs_eq
                                  vs_cap_ref_def unat_of_bl_length
                      | intro impI TrueI ext conjI
                      | (match conclusion in "{x} \<times> _ = {x} \<times> _" for x
                                     \<Rightarrow> \<open>fastforce simp: unat_of_bl_length\<close>))+)[11]
  apply (simp add: arch_finalise_cap_def split del: if_split)
  apply (wpsimp simp: cap_cleanup_opt_def arch_cap_cleanup_opt_def)+
  done

crunch typ_at_arch[wp,Finalise_AI_asms]: arch_finalise_cap, prepare_thread_delete "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps unless_def assertE_def
        ignore: maskInterrupt )

crunch valid_cap[wp]: prepare_thread_delete "valid_cap cap"
crunch tcb_at[wp]: prepare_thread_delete "tcb_at p"
crunch cte_wp_at[wp, Finalise_AI_asms]: prepare_thread_delete "\<lambda>s. P (cte_wp_at P' p s)"
crunch irq_node[wp, Finalise_AI_asms]: prepare_thread_delete "\<lambda>s. P (interrupt_irq_node s)"
crunch caps_of_state[wp, Finalise_AI_asms]: prepare_thread_delete "\<lambda>s. P (caps_of_state s)"

crunch device_state_inv[wp]: nativeThreadUsingFPU, switchFpuOwner "\<lambda>ms. P (device_state ms)"

lemma dmo_nativeThreadUsingFPU[wp]: "\<lbrace>invs\<rbrace> do_machine_op (nativeThreadUsingFPU thread) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: nativeThreadUsingFPU_def machine_op_lift_def
                            machine_rest_lift_def split_def | wp)+)[3]
  apply (erule (1) use_valid[OF _ nativeThreadUsingFPU_irq_masks])
  done

lemma dmo_switchFpuOwner[wp]: "\<lbrace>invs\<rbrace> do_machine_op (switchFpuOwner thread cpu) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: switchFpuOwner_def machine_op_lift_def
                            machine_rest_lift_def split_def | wp)+)[3]
  apply (erule (1) use_valid[OF _ switchFpuOwner_irq_masks])
  done

crunch invs[wp]: prepare_thread_delete invs
  (ignore: do_machine_op)

lemma (* finalise_cap_new_valid_cap *)[wp,Finalise_AI_asms]:
  "\<lbrace>valid_cap cap\<rbrace> finalise_cap cap x \<lbrace>\<lambda>rv. valid_cap (fst rv)\<rbrace>"
  apply (cases cap, simp_all)
            apply (wp suspend_valid_cap
                     | simp add: o_def valid_cap_def cap_aligned_def
                                 valid_cap_Null_ext
                           split del: if_split
                     | clarsimp | rule conjI)+
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
  apply (wp|simp add: o_def valid_cap_def cap_aligned_def
                 split del: if_split|clarsimp|wpc)+
  done

lemma (* arch_finalise_cap_invs *)[wp,Finalise_AI_asms]:
  "\<lbrace>invs and valid_cap (ArchObjectCap cap)\<rbrace>
     arch_finalise_cap cap final
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (wp unmap_page_invs | wpc)+
  apply (clarsimp simp: valid_cap_def cap_aligned_def)
  apply (auto simp: mask_def wellformed_mapdata_def)
  done

lemma arch_finalise_cap_replaceable[wp]:
  notes strg = tcb_cap_valid_imp_NullCap
               obj_at_not_live_valid_arch_cap_strg[where cap=cap]
  notes simps = replaceable_def and_not_not_or_imp
                vs_lookup_pages_eq_at[THEN fun_cong, symmetric]
                vs_lookup_pages_eq_ap[THEN fun_cong, symmetric]
                is_cap_simps vs_cap_ref_def
                no_cap_to_obj_with_diff_ref_Null o_def
  notes wps = hoare_drop_imp[where R="%_. is_final_cap' cap" for cap]
               valid_cap_typ unmap_page_vs_lookup_pages_small
               unmap_page_vs_lookup_pages_large unmap_page_vs_lookup_pages_huge
  shows
    "\<lbrace>\<lambda>s. s \<turnstile> cap.ArchObjectCap cap \<and>
          x = is_final_cap' (cap.ArchObjectCap cap) s \<and>
          pspace_aligned s \<and> valid_vspace_objs s \<and> valid_objs s \<and>
          valid_arch_state s\<rbrace>
     arch_finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) (cap.ArchObjectCap cap)\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (simp add: simps split: option.splits vmpage_size.splits)
   apply (wp wps
          | strengthen strg
          | simp add: simps reachable_pg_cap_def
          | wpc)+
     (* unmap_page case is a bit unpleasant *)
     apply (strengthen cases_conj_strg[where P="\<not> is_final_cap' cap s" for cap s, simplified])
     apply (rule hoare_post_imp, clarsimp split: vmpage_size.split, assumption)
     apply simp
     apply ((wp hoare_vcg_disj_lift hoare_vcg_all_lift hoare_vcg_const_imp_lift
               unmap_page_tcb_cap_valid)[1],
             (wp wps unmap_pt_vs_lookup_pages
              unmap_pd_vs_lookup_pages unmap_pdpt_vs_lookup_pages
           | strengthen strg imp_and_strg tcb_cap_valid_imp_NullCap
           | simp add: simps is_master_reply_cap_def reachable_pg_cap_def
           | wpc)+)+ (* long *)
  apply (auto simp: obj_at_def data_at_def wellformed_mapdata_def valid_cap_def
             split: cap.splits arch_cap.splits option.splits vmpage_size.splits)
  done

global_naming Arch
lemma (* deleting_irq_handler_slot_not_irq_node *)[Finalise_AI_asms]:
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

lemma no_cap_to_obj_with_diff_ref_finalI_ARCH[Finalise_AI_asms]:
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

lemma (* suspend_no_cap_to_obj_ref *)[wp,Finalise_AI_asms]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (simp add: no_cap_to_obj_with_diff_ref_def
                   cte_wp_at_caps_of_state)
  apply (wp suspend_caps_of_state)
  apply (clarsimp simp: table_cap_ref_simps
                 dest!: obj_ref_none_no_asid[rule_format])
  done

lemma suspend_unlive':
  "\<lbrace>bound_tcb_at ((=) None) t and valid_mdb and valid_objs and tcb_at t \<rbrace>
      suspend t
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) t\<rbrace>"
  apply (simp add: suspend_def set_thread_state_def set_object_def get_object_def)
  supply hoare_vcg_if_split[wp_split del] if_split[split del]
  apply (wp | simp only: obj_at_exst_update)+
     apply (simp add: obj_at_def live_def hyp_live_def)
     apply (rule_tac Q="\<lambda>_. bound_tcb_at ((=) None) t" in hoare_strengthen_post)
      supply hoare_vcg_if_split[wp_split]
      apply wp
     apply (auto simp: pred_tcb_def2)[1]
    apply (simp flip: if_split)
    apply wpsimp+
  done

crunch obj_at[wp]: fpu_thread_delete
  "\<lambda>s. P' (obj_at P p s)"
  (wp: whenE_wp simp: crunch_simps)

lemma (* fpu_thread_delete_no_cap_to_obj_ref *)[wp,Finalise_AI_asms]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     fpu_thread_delete thread
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  by (wpsimp simp: no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state)

lemma finalise_cap_replaceable [Finalise_AI_asms]:
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
   apply wp
   apply (clarsimp simp: replaceable_def reachable_pg_cap_def
            o_def cap_range_def valid_arch_state_def
            ran_tcb_cap_cases is_cap_simps
            gen_obj_refs_subset vs_cap_ref_def
            all_bool_eq)
  apply ((cases cap;
      simp add: replaceable_def reachable_pg_cap_def
                       split del: if_split;
      rule hoare_pre),

    (wp suspend_unlive'[unfolded o_def]
        suspend_final_cap[where sl=sl]
        unbind_maybe_notification_not_bound
        get_simple_ko_ko_at hoare_vcg_conj_lift
        unbind_notification_valid_objs
      | clarsimp simp: o_def dom_tcb_cap_cases_lt_ARCH
                        ran_tcb_cap_cases is_cap_simps
                        cap_range_def prepare_thread_delete_def
                        can_fast_finalise_def
                        gen_obj_refs_subset
                        vs_cap_ref_def unat_of_bl_length
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
      | simp add: valid_cap_simps is_nondevice_page_cap_simps)+)
  done

lemma (* deleting_irq_handler_cte_preserved *)[Finalise_AI_asms]:
  assumes x: "\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap"
  shows "\<lbrace>cte_wp_at P p\<rbrace> deleting_irq_handler irq \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_cte_wp_at_preserved | simp add: x)+
  done

lemma set_asid_pool_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_asid_pool ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update a_type_simps)


crunch cte_wp_at[wp,Finalise_AI_asms]: arch_finalise_cap "\<lambda>s. P (cte_wp_at P' p s)"
  (simp: crunch_simps assertE_def set_arch_obj_simps
     wp: set_aobject_cte_wp_at crunch_wps set_object_cte_at
   ignore: set_object)

end

interpretation Finalise_AI_1?: Finalise_AI_1
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming X64

lemma fast_finalise_replaceable[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s
     \<and> cte_wp_at ((=) cap) sl s \<and> valid_asid_table (x64_asid_table (arch_state s)) s
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

global_naming Arch
lemma (* cap_delete_one_invs *) [Finalise_AI_asms,wp]:
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
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming X64

lemma flush_table_irq_node: "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> flush_table a b c d \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  apply (simp add: flush_table_def)
  apply (wp mapM_x_wp' | wpc | simp | rule hoare_pre)+
  done

lemma flush_table_pred_tcb_at: "\<lbrace>\<lambda>s. pred_tcb_at proj P t s\<rbrace> flush_table a b c d \<lbrace>\<lambda>_ s. pred_tcb_at proj P t s\<rbrace>"
  apply (simp add: flush_table_def)
  apply (wp mapM_x_wp' | wpc | simp | rule hoare_pre)+
  done

crunch irq_node[wp]: arch_finalise_cap "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

crunch pred_tcb_at[wp]: arch_finalise_cap "pred_tcb_at proj P t"
  (simp: crunch_simps set_arch_obj_simps wp: crunch_wps set_aobject_pred_tcb_at
   ignore: set_object)

lemma tcb_cap_valid_pagetable:
  "tcb_cap_valid (ArchObjectCap (PageTableCap word (Some v))) slot
    = tcb_cap_valid (ArchObjectCap (PageTableCap word None)) slot"
  apply (rule ext)
  apply (simp add: tcb_cap_valid_def tcb_cap_cases_def is_valid_vtable_root_def
                   is_cap_simps valid_ipc_buffer_cap_def
            split: Structures_A.thread_state.split)
  done

lemma tcb_cap_valid_pagedirectory:
  "tcb_cap_valid (ArchObjectCap (PageDirectoryCap word (Some v))) slot
    = tcb_cap_valid (ArchObjectCap (PageDirectoryCap word None)) slot"
  apply (rule ext)
  apply (simp add: tcb_cap_valid_def tcb_cap_cases_def is_valid_vtable_root_def
                   is_cap_simps valid_ipc_buffer_cap_def
            split: Structures_A.thread_state.split)
  done

lemma tcb_cap_valid_pdpt:
  "tcb_cap_valid (ArchObjectCap (PDPointerTableCap word (Some v))) slot
    = tcb_cap_valid (ArchObjectCap (PDPointerTableCap word None)) slot"
  apply (rule ext)
  apply (simp add: tcb_cap_valid_def tcb_cap_cases_def is_valid_vtable_root_def
                   is_cap_simps valid_ipc_buffer_cap_def
            split: Structures_A.thread_state.split)
  done

lemma store_pde_unmap_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    store_pde pd_slot InvalidPDE
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (clarsimp simp: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def empty_table_def pde_ref_def)
  done

lemma store_pte_unmap_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    store_pte xa InvalidPTE
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (wp get_object_wp | simp add: store_pte_def set_pt_def set_object_def)+
  apply (clarsimp simp: obj_at_def empty_table_def)
  done

lemma store_pdpte_unmap_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    store_pdpte pd_slot InvalidPDPTE
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (clarsimp simp: store_pdpte_def set_arch_obj_simps set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def empty_table_def pdpte_ref_def)
  done

lemma store_pml4e_unmap_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    store_pml4e pd_slot InvalidPML4E
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (clarsimp simp: store_pml4e_def set_arch_obj_simps set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def empty_table_def pml4e_ref_def)
  done

lemma flush_table_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    flush_table ac aa word b
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (clarsimp simp: flush_table_def set_vm_root_def)
  apply (wp do_machine_op_obj_at  whenE_wp mapM_x_wp'
    | wpc
    | simp
    | wps
    | rule hoare_pre)+
  done

crunch empty[wp]: flush_all, invalidate_page_structure_cache_asid, lookup_pt_slot, set_vm_root,
                  hw_asid_invalidate
  "\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s"
  (wp: crunch_wps simp: crunch_simps)

lemma unmap_page_table_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    unmap_page_table aa b word
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (wp store_pde_unmap_empty flush_table_empty  | simp | wpc | wp (once) hoare_drop_imps)+
  done

lemma unmap_pd_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    unmap_pd aa b word
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (simp add: unmap_pd_def)
  apply (wp store_pdpte_unmap_empty flush_table_empty  | simp | wpc | wp (once) hoare_drop_imps)+
  done

lemma unmap_pdpt_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    unmap_pdpt aa b word
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (simp add: unmap_pdpt_def)
  apply (wp store_pml4e_unmap_empty flush_table_empty  | simp | wpc | wp (once) hoare_drop_imps)+
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

lemma is_final_cap_pdpt_asid_eq:
  "is_final_cap' (ArchObjectCap (PDPointerTableCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PDPointerTableCap p x)) s"
  apply (clarsimp simp: is_final_cap'_def gen_obj_refs_Int)
  done

lemma is_final_cap_pml4_asid_eq:
  "is_final_cap' (ArchObjectCap (PML4Cap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PML4Cap p x)) s"
  apply (clarsimp simp: is_final_cap'_def gen_obj_refs_Int)
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

lemma cte_wp_at_obj_refs_singleton_pdpt:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PDPointerTableCap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at
            ((=) (ArchObjectCap (PDPointerTableCap p asid))) (a,b) s"
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma cte_wp_at_obj_refs_singleton_pml4:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PML4Cap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at
            ((=) (ArchObjectCap (PML4Cap p asid))) (a,b) s"
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

lemma final_cap_pdpt_slot_eq:
  "\<lbrakk>is_final_cap' (ArchObjectCap (PDPointerTableCap p asid)) s;
    cte_wp_at ((=) (ArchObjectCap (PDPointerTableCap p asid'))) slot s;
    cte_wp_at ((=) (ArchObjectCap (PDPointerTableCap p asid''))) slot' s\<rbrakk>
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

lemma final_cap_pml4_slot_eq:
  "\<lbrakk>is_final_cap' (ArchObjectCap (PML4Cap p asid)) s;
    cte_wp_at ((=) (ArchObjectCap (PML4Cap p asid'))) slot s;
    cte_wp_at ((=) (ArchObjectCap (PML4Cap p asid''))) slot' s\<rbrakk>
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
     (ArchObjectCap (PageCap d p r typ sz m))
     (ArchObjectCap (PageCap d p r' typ sz m'))"
  apply (simp add: is_arch_update_def is_arch_cap_def cap_master_cap_def)
  done

lemma replaceable_reset_pt:
  "\<lbrakk>cap = PageTableCap p m \<and>
   cte_wp_at ((=) (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table (set (second_level_tables (arch_state s)))) p s\<rbrakk> \<Longrightarrow>
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

lemma replaceable_reset_pd:
  "\<lbrakk>cap = PageDirectoryCap p m \<and>
   cte_wp_at ((=) (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table (set (second_level_tables (arch_state s)))) p s\<rbrakk> \<Longrightarrow>
   replaceable s slot (ArchObjectCap (PageDirectoryCap p None))
                      (ArchObjectCap cap)"
  apply (elim conjE)
  apply (cases m, simp_all add: replaceable_def gen_obj_refs_def cap_range_def is_cap_simps
                           tcb_cap_valid_pagedirectory)
  apply (rule conjI)
   apply (frule is_final_cap_pd_asid_eq) defer
   apply clarsimp
   apply (drule cte_wp_at_obj_refs_singleton_page_directory)
   apply (erule exE)
   apply (drule_tac x="asid" in is_final_cap_pd_asid_eq)
   apply (drule final_cap_pd_slot_eq)
     apply simp_all
  apply (rule_tac
    cap="ArchObjectCap cap"
    in  no_cap_to_obj_with_diff_ref_finalI)
  apply simp_all
  done

lemma replaceable_reset_pdpt:
  "\<lbrakk>cap = PDPointerTableCap p m \<and>
   cte_wp_at ((=) (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table (set (second_level_tables (arch_state s)))) p s\<rbrakk> \<Longrightarrow>
   replaceable s slot (ArchObjectCap (PDPointerTableCap p None))
                      (ArchObjectCap cap)"
  apply (elim conjE)
  apply (cases m, simp_all add: replaceable_def gen_obj_refs_def cap_range_def is_cap_simps
                           tcb_cap_valid_pdpt)
  apply (rule conjI)
   apply (frule is_final_cap_pdpt_asid_eq) defer
   apply clarsimp
   apply (drule cte_wp_at_obj_refs_singleton_pdpt)
   apply (erule exE)
   apply (drule_tac x="asid" in is_final_cap_pdpt_asid_eq)
   apply (drule final_cap_pdpt_slot_eq)
     apply simp_all
  apply (rule_tac
    cap="ArchObjectCap cap"
    in  no_cap_to_obj_with_diff_ref_finalI)
  apply simp_all
  done

crunch caps_of_state [wp]: arch_finalise_cap "\<lambda>s. P (caps_of_state s)"
   (wp: crunch_wps simp: crunch_simps)

crunch obj_at[wp]: invalidate_page_structure_cache_asid, hw_asid_invalidate
  "\<lambda>s. P' (obj_at P p s)"
  (wp: whenE_wp simp: crunch_simps)

crunch x64_global_pdpts[wp]: invalidate_page_structure_cache_asid, hw_asid_invalidate
  "\<lambda>s. P' (x64_global_pdpts (arch_state s))"
  (wp: whenE_wp simp: crunch_simps)

lemma delete_asid_empty_table_pml4:
  "\<lbrace>\<lambda>s. page_map_l4_at word s
      \<and> obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    delete_asid a word
   \<lbrace>\<lambda>_ s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (simp add: delete_asid_def)
  apply (wpsimp wp: set_object_at_obj simp: set_arch_obj_simps | wps)+
  apply (clarsimp simp: obj_at_def empty_table_def)
  done

lemma page_map_l4_at_def2:
  "page_map_l4_at p s = (\<exists>pd. ko_at (ArchObj (PageMapL4 pd)) p s)"
  apply (simp add: a_type_def obj_at_def)
  apply (rule iffI)
   apply (erule exE)
   apply (case_tac ko, simp_all split: if_splits)
   apply (rename_tac arch_kernel_obj)
   apply (case_tac arch_kernel_obj, simp_all split: if_splits)
  apply (erule exE)
  apply (rule_tac x="ArchObj (PageMapL4 pd)" in exI)
  apply simp
  done

lemma
  shows pd_pointer_table_at_def2: "pd_pointer_table_at p s = (\<exists> pdpt. ako_at (PDPointerTable pdpt) p s)"
    and page_directory_at_def2: "page_directory_at p s = (\<exists> pd. ako_at (PageDirectory pd) p s)"
    and page_table_at_def2: "page_table_at p s = (\<exists> pt. ako_at (PageTable pt) p s)"
  by (auto simp: obj_at_def) (auto simp: a_type_def)

definition
  pml4e_wp_at :: "(pml4e \<Rightarrow> bool) \<Rightarrow> machine_word \<Rightarrow> 9 word \<Rightarrow> 'z state \<Rightarrow> bool"
  where
  "pml4e_wp_at P ptr slot s \<equiv>
     (case (kheap s ptr) of
         Some (ArchObj (PageMapL4 pd)) \<Rightarrow> P (pd slot)
       | _ \<Rightarrow> False)"

lemma store_pml4e_pml4e_wp_at:
  "\<lbrace>\<top>\<rbrace>
   store_pml4e p x
   \<lbrace>\<lambda>_. pml4e_wp_at
         (\<lambda>pde. pde = x) (p && ~~ mask pml4_bits) (ucast (p && mask pml4_bits >> word_size_bits))\<rbrace>"
  apply (wp
    | simp add: store_pml4e_def set_pml4_def set_object_def get_object_def
                obj_at_def pml4e_wp_at_def a_type_simps aa_type_simps)+
  done

lemma store_pml4e_pml4e_wp_at2:
  "\<lbrace>pml4e_wp_at (\<lambda>pde. pde = pml4e.InvalidPML4E) ptr slot\<rbrace>
   store_pml4e p' InvalidPML4E
   \<lbrace>\<lambda>_. pml4e_wp_at (\<lambda>pde. pde = InvalidPML4E) ptr slot\<rbrace>"
  apply (wp
    | simp add: store_pml4e_def set_pml4_def set_object_def get_object_def
                obj_at_def pml4e_wp_at_def
    | clarsimp)+
  done

lemma obj_at_empty_tableI:
  "invs s \<and>
  (\<forall>x. x \<notin> kernel_mapping_slots \<longrightarrow>
      pml4e_wp_at (\<lambda>pde. pde = InvalidPML4E) p x s)
  \<Longrightarrow> obj_at (empty_table (set (second_level_tables (arch_state s)))) p s"
  apply safe
  apply (simp add: obj_at_def empty_table_def pml4e_wp_at_def)
  (* Boring cases *)
  apply (case_tac "\<exists>ko. kheap s p = Some ko")
   apply (erule exE)
   apply (rule_tac x=ko in exI)
   apply (rule conjI)
    apply assumption
   apply (case_tac ko)
       apply ((erule_tac x="ucast (pptr_base >> pml4_shift_bits) - 1" in allE,
         simp add: pptr_base_def kernel_mapping_slots_def pptrBase_def bit_simps)+)[4]
   apply (rename_tac arch_kernel_obj)
   apply (case_tac arch_kernel_obj) defer 5
      apply ((erule_tac x="ucast (pptr_base >> pml4_shift_bits) - 1" in allE,
         simp add: pptr_base_def pptrBase_def bit_simps kernel_mapping_slots_def)+)[6]
   (* Interesting case *)
  apply (rename_tac "fun")
  apply clarsimp
  apply (erule_tac x=x in allE)
  apply (case_tac "x \<notin> kernel_mapping_slots")
   apply (simp add:)
  apply simp
  apply (simp add: invs_def valid_state_def valid_kernel_mappings_def
                    valid_kernel_mappings_if_pm_def)
  apply (erule conjE)+
  apply (erule_tac x="ArchObj (PageMapL4 fun)" in ballE)
   apply simp
  apply (simp add: ran_def)
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

lemma caps_of_state_aligned_pdpt:
  "\<lbrakk>caps_of_state s slot =
  Some (ArchObjectCap (PDPointerTableCap word option));
  invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pdpt_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pdpt_bits_def pageBits_def)
  done

lemma caps_of_state_aligned_pml4:
  "\<lbrakk>caps_of_state s slot =
  Some (ArchObjectCap (PML4Cap word option));
  invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pml4_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pml4_bits_def pageBits_def)
  done
end

lemma invs_valid_arch_capsI:
  "invs s \<Longrightarrow> valid_arch_caps s"
  by (simp add: invs_def valid_state_def)

context Arch begin global_naming X64 (*FIXME: arch_split*)

lemma all_Some_the_strg: "f b = None \<or> P (the (f b)) \<longrightarrow> (\<forall>a. f b = Some a \<longrightarrow> P a)"
  by auto

lemma vs_cap_ref_PageCap_Some_None[simp]:
  "(vs_cap_ref (ArchObjectCap (PageCap d p R typ sz (Some v))) = None) = False"
  by (case_tac sz; simp add: vs_cap_ref_simps split_def)

lemma vs_cap_ref_PageCap_None_Some[simp]:
  "\<And>y. (vs_cap_ref (ArchObjectCap (PageCap d p R typ sz None)) = Some y) = False"
  by (case_tac sz; simp add: vs_cap_ref_simps split_def)

lemma arch_finalise_case_no_lookup:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_objs and
    valid_cap (cap.ArchObjectCap acap) and valid_arch_state
    and K (aobj_ref acap = Some w \<and> is_final)\<rbrace>
  arch_finalise_cap acap is_final
  \<lbrace>\<lambda>rv s. (\<forall>vs. vs_cap_ref (cap.ArchObjectCap acap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> w) s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
   apply (simp add: arch_finalise_cap_def)
   apply (wpc | wp delete_asid_pool_unmapped hoare_vcg_imp_lift
                  unmap_page_vs_lookup_pages_pre
                  unmap_pt_vs_lookup_pages unmap_pd_vs_lookup_pages
                  unmap_pdpt_vs_lookup_pages
              | simp add: vs_cap_ref_simps
                          vs_lookup_pages_eq_at[THEN fun_cong, symmetric]
                          vs_lookup_pages_eq_ap[THEN fun_cong, symmetric]
              | strengthen all_Some_the_strg)+
   apply (auto simp: valid_cap_simps vs_cap_ref_simps data_at_def wellformed_mapdata_def
              split: vmpage_size.split if_splits)
   done

lemma arch_finalise_vtable_empty:
  "\<lbrace>(\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) ptr s)
       and valid_cap (cap.ArchObjectCap acap) and
       K ((is_pt_cap (cap.ArchObjectCap acap) \<or> is_pd_cap (cap.ArchObjectCap acap)
           \<or> is_pdpt_cap (cap.ArchObjectCap acap) \<or> is_pml4_cap (cap.ArchObjectCap acap))
            \<and> aobj_ref acap = Some ptr)\<rbrace>
   arch_finalise_cap acap final
  \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) ptr s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: is_cap_simps arch_finalise_cap_def)
   apply (rule hoare_pre)
   apply (wp unmap_page_table_empty | wpc)+
   apply clarsimp
  apply (clarsimp simp: is_cap_simps arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (wp unmap_page_table_empty delete_asid_empty_table_pml4 unmap_pd_empty unmap_pdpt_empty | wpc
          | clarsimp)+
  apply (auto simp: valid_cap_def split: arch_cap.splits)
  done

lemma do_machine_op_reachable_pg_cap[wp]:
  "\<lbrace>\<lambda>s. P (reachable_pg_cap cap s)\<rbrace>
   do_machine_op mo
   \<lbrace>\<lambda>rv s. P (reachable_pg_cap cap s)\<rbrace>"
  apply (simp add:reachable_pg_cap_def,wp)
  done

lemma replaceable_or_arch_update_pg:
  " (case (vs_cap_ref (ArchObjectCap (PageCap dev word fun typ vm_pgsz y))) of None \<Rightarrow> True | Some ref \<Rightarrow> \<not> (ref \<unrhd> word) s)
  \<longrightarrow> replaceable_or_arch_update s slot (ArchObjectCap (PageCap dev word fun typ vm_pgsz None))
                (ArchObjectCap (PageCap dev word fun typ vm_pgsz y))"
  unfolding replaceable_or_arch_update_def
  apply (auto simp: is_cap_simps is_arch_update_def cap_master_cap_simps)
  done

crunch valid_cap: invalidate_page_structure_cache_asid, hw_asid_invalidate "valid_cap cap"
crunch valid_asid_table[wp]: do_machine_op
  "\<lambda>s. valid_asid_table (x64_asid_table (arch_state s)) s"

global_naming Arch

lemma (* finalise_cap_invs *)[Finalise_AI_asms]:
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

lemma (* finalise_cap_irq_node *)[Finalise_AI_asms]:
"\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> finalise_cap a b \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  apply (case_tac a,simp_all)
  apply (wp | clarsimp)+
  done

lemmas (*arch_finalise_cte_irq_node *) [wp,Finalise_AI_asms]
    = hoare_use_eq_irq_node [OF arch_finalise_cap_irq_node arch_finalise_cap_cte_wp_at]

lemma (* deleting_irq_handler_st_tcb_at *) [Finalise_AI_asms]:
  "\<lbrace>st_tcb_at P t and K (\<forall>st. simple st \<longrightarrow> P st)\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_st_tcb_at)
  apply simp
  done

lemma irq_node_global_refs_ARCH [Finalise_AI_asms]:
  "interrupt_irq_node s irq \<in> global_refs s"
  by (simp add: global_refs_def)

lemma (* get_irq_slot_fast_finalisable *)[wp,Finalise_AI_asms]:
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

lemma (* replaceable_or_arch_update_same *) [Finalise_AI_asms]:
  "replaceable_or_arch_update s slot cap cap"
  by (clarsimp simp: replaceable_or_arch_update_def
                replaceable_def is_arch_update_def is_cap_simps)

lemma (* replace_cap_invs_arch_update *)[Finalise_AI_asms]:
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

crunch pred_tcb_at_P [wp]: hw_asid_invalidate "\<lambda>s. P (pred_tcb_at proj Q p s)"

lemma dmo_tcb_cap_valid_ARCH [Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. P (tcb_cap_valid cap ptr s)\<rbrace> do_machine_op mop \<lbrace>\<lambda>_ s. P (tcb_cap_valid cap ptr s)\<rbrace>"
  apply (simp add: tcb_cap_valid_def no_cap_to_obj_with_diff_ref_def)
  apply (rule hoare_pre)
  apply wps
  apply wp
  apply simp
  done

lemma (* dmo_replaceable_or_arch_update *) [Finalise_AI_asms,wp]:
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

context begin interpretation Arch .
requalify_consts replaceable_or_arch_update
end

interpretation Finalise_AI_3?: Finalise_AI_3
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

interpretation Finalise_AI_4?: Finalise_AI_4
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming X64

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
   Some p \<notin> x64_asid_table (arch_state s) ` (dom (x64_asid_table (arch_state s)) - {x}) \<longrightarrow>
   valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table (arch_state s)(x \<mapsto> p)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def ran_def)
  apply (rule conjI, fastforce)
  apply (erule inj_on_fun_upd_strongerI)
  apply simp
  done

lemma valid_table_caps_table [simp]:
  "valid_table_caps (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table'\<rparr>\<rparr>) = valid_table_caps s"
  by (simp add: valid_table_caps_def second_level_tables_def)

lemma valid_global_objs_table [simp]:
  "valid_global_objs (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table'\<rparr>\<rparr>) = valid_global_objs s"
  by (simp add: valid_global_objs_def second_level_tables_def)

lemma valid_kernel_mappings [iff]:
  "valid_kernel_mappings (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table'\<rparr>\<rparr>) = valid_kernel_mappings s"
  by (simp add: valid_kernel_mappings_def second_level_tables_def)

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
  (s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (ASIDPool Map.empty)),
     arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table (arch_state s)(x \<mapsto> p)\<rparr>\<rparr>) \<Longrightarrow>
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
  (s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (ASIDPool Map.empty)),
     arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table (arch_state s)(x \<mapsto> p)\<rparr>\<rparr>) \<Longrightarrow>
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
             (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table :=
                x64_asid_table (arch_state s)(asid_high_bits_of word2 \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
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
             (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table :=
                x64_asid_table (arch_state s)(asid_high_bits_of base \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
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

lemma valid_ioports_asid_table_upd[iff]:
  "valid_ioports
         (s\<lparr>arch_state := arch_state s
              \<lparr>x64_asid_table := x64_asid_table (arch_state s)
                 (asid_high_bits_of base \<mapsto> p)\<rparr>\<rparr>) = valid_ioports s"
  by (clarsimp simp: valid_ioports_def all_ioports_issued_def issued_ioports_def)

lemma set_asid_pool_invs_table:
  "\<lbrace>\<lambda>s. invs s \<and> asid_pool_at p s
       \<and> (\<exists>p'. caps_of_state s p' = Some (ArchObjectCap (ASIDPoolCap p base)))
       \<and> (\<not> ([VSRef (ucast (asid_high_bits_of base)) None] \<rhd> p) s)
       \<and> (\<forall>p'. \<not> ([VSRef (ucast (asid_high_bits_of base)) None] \<rhd> p') s)\<rbrace>
       set_asid_pool p Map.empty
  \<lbrace>\<lambda>x s. invs (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table :=
                 x64_asid_table (arch_state s)(asid_high_bits_of base \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_caps_def valid_asid_map_def)
  apply (wp valid_irq_node_typ set_asid_pool_typ_at
            set_asid_pool_empty_table_objs valid_ioports_lift
            valid_irq_handlers_lift set_asid_pool_empty_table_lookup
          | strengthen valid_arch_state_table_strg)+
  apply clarsimp
  apply (drule vs_asid_refsI)
  apply (drule vs_lookupI, rule rtrancl_refl)
  apply (frule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply clarsimp
  apply (drule obj_ref_elemD)
  apply (frule(2) unique_table_refsD,
         unfold obj_refs.simps aobj_ref.simps option.simps,
         assumption)
  apply (clarsimp simp: vs_cap_ref_def table_cap_ref_def
                 split: cap.split_asm arch_cap.split_asm)
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
      apply (rule_tac Q="\<lambda>rv s. ?Q s \<and> asid_table = x64_asid_table (arch_state s)"
                 in hoare_post_imp)
       apply (clarsimp simp: fun_upd_def[symmetric])
       apply (drule vs_lookup_clear_asid_table[rule_format])
       apply simp
      apply (wp mapM_wp')+
      apply clarsimp
     apply wp+
  apply fastforce
  done

crunch x64_global_pml4[wp]: hw_asid_invalidate, invalidate_page_structure_cache_asid
           "\<lambda>s. P (x64_global_pml4(arch_state s))"

lemma page_table_pte_atE:
  "\<lbrakk> page_table_at p s; x < 2 ^ pt_bits;
             (x >> word_size_bits) << word_size_bits = x; pspace_aligned s \<rbrakk>
       \<Longrightarrow> pte_at (p + x) s"
  apply (drule page_table_pte_atI[where x="x >> word_size_bits"], simp_all)
  apply (subst mask_eq_iff_w2p[symmetric])
   apply (simp add: pt_bits_def word_size bit_simps)
  apply (rule word_eqI)
  apply (clarsimp simp add: nth_shiftr)
  apply (drule_tac x="word_size_bits + n" in word_eqD [OF less_mask_eq])
  apply (auto simp: bit_simps)
  done

crunch valid_cap [wp]: unmap_page_table,
  store_pte, delete_asid_pool, copy_global_mappings,
  arch_finalise_cap
  "valid_cap c"
  (wp: mapM_wp_inv mapM_x_wp' crunch_wps simp: crunch_simps set_arch_obj_simps
   ignore: set_object)

lemmas clearMemory_invs[wp, Finalise_AI_asms] = clearMemory_invs

lemma valid_idle_has_null_cap_ARCH[Finalise_AI_asms]:
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

lemma (* zombie_cap_two_nonidles *)[Finalise_AI_asms]:
  "\<lbrakk> caps_of_state s ptr = Some (Zombie ptr' zbits n); invs s \<rbrakk>
       \<Longrightarrow> fst ptr \<noteq> idle_thread s \<and> ptr' \<noteq> idle_thread s"
  apply (frule valid_global_refsD2, clarsimp+)
  apply (simp add: cap_range_def global_refs_def)
  apply (cases ptr, auto dest: valid_idle_has_null_cap_ARCH[rotated -1])[1]
  done

lemma safe_ioport_insert_not_ioport:
  "\<not>is_ioport_cap cap \<Longrightarrow> safe_ioport_insert cap cap' s"
  by (clarsimp simp: is_cap_simps safe_ioport_insert_def cap_ioports_def split: cap.splits arch_cap.splits)

lemmas safe_ioport_insert_simps[simp] = safe_ioport_insert_not_ioport[where cap="ReplyCap a False b" for a b, simplified is_cap_simps, simplified]

lemma cap_insert_ioports_not:
  "\<lbrace>valid_ioports and K (\<not> is_ioport_cap cap \<and> dest \<noteq> src)\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  apply (simp add: cap_insert_def)
  apply (wp get_cap_wp set_cap_ioports_no_new_ioports set_untyped_cap_as_full_ioports
            set_untyped_cap_as_full_cte_wp_at
         | wpc | simp split del: if_split)+
  apply (case_tac cap; clarsimp simp: is_cap_simps cte_wp_at_caps_of_state)
  apply (case_tac x12; clarsimp)
  done

lemma setup_caller_cap_ioports:
  "\<lbrace>valid_ioports\<rbrace> setup_caller_cap a b c \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  by (wpsimp simp: setup_caller_cap_def is_cap_simps wp: cap_insert_ioports_not
             split_del: if_split)

crunches set_mrs, as_user, set_message_info, copy_mrs, make_arch_fault_msg
  for ioports[wp]: valid_ioports
  (wp: crunch_wps valid_ioports_lift simp: crunch_simps ignore: set_object)

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
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

end
