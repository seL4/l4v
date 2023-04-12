(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchUserOp_IF
imports UserOp_IF
begin

context Arch begin global_naming RISCV64

definition ptable_lift_s where
  "ptable_lift_s s \<equiv> ptable_lift (cur_thread s) s"

definition ptable_rights_s where
  "ptable_rights_s s \<equiv> ptable_rights (cur_thread s) s"

(* FIXME: move to ADT_AI.thy *)
definition ptable_attrs :: "obj_ref \<Rightarrow> 's :: state_ext state \<Rightarrow> obj_ref \<Rightarrow> vm_attributes" where
 "ptable_attrs tcb s \<equiv>
    \<lambda>addr. case_option {} (fst o snd o snd)
             (get_page_info (aobjs_of False s) (get_vspace_of_thread (kheap s) (arch_state s) tcb) addr)"

definition ptable_attrs_s :: "'s :: state_ext state \<Rightarrow> obj_ref \<Rightarrow> vm_attributes" where
 "ptable_attrs_s s \<equiv> ptable_attrs (cur_thread s) s"

definition ptable_xn_s where
  "ptable_xn_s s \<equiv> \<lambda>addr. Execute \<notin> ptable_attrs_s s addr"


type_synonym user_state_if = "user_context \<times> user_mem \<times> device_state"

text \<open>
  A user transition gives back a possible event that is the next
  event the user wants to perform
\<close>
type_synonym user_transition_if =
  "obj_ref \<Rightarrow> vm_mapping \<Rightarrow> mem_rights \<Rightarrow> (obj_ref \<Rightarrow> bool) \<Rightarrow>
   user_state_if \<Rightarrow> (event option \<times> user_state_if) set"


definition do_user_op_if ::
  "user_transition_if \<Rightarrow> user_context \<Rightarrow> (event option \<times> user_context,'z::state_ext) s_monad" where
  "do_user_op_if uop tc =
   do
      \<comment> \<open>Get the page rights of each address (ReadOnly, ReadWrite, None, etc).\<close>
      pr \<leftarrow> gets ptable_rights_s;

      \<comment> \<open>Fetch the execute bits of the current thread's page mappings.\<close>
      pxn \<leftarrow> gets (\<lambda>s x. pr x \<noteq> {} \<and> ptable_xn_s s x);

      \<comment> \<open>Get the mapping from virtual to physical addresses.\<close>
      pl \<leftarrow> gets (\<lambda>s. restrict_map (ptable_lift_s s) {x. pr x \<noteq> {}});

      allow_read \<leftarrow> return  {y. EX x. pl x = Some y \<and> AllowRead \<in> pr x};
      allow_write \<leftarrow> return  {y. EX x. pl x = Some y \<and> AllowWrite \<in> pr x};

      \<comment> \<open>Get the current thread.\<close>
      t \<leftarrow> gets cur_thread;

      \<comment> \<open>Generate user memory by throwing away anything from global
         memory that the user doesn't have access to. (The user must
         have both (1) a mapping to the page; (2) that mapping has the
         AllowRead right.\<close>
      um \<leftarrow> gets (\<lambda>s. (user_mem s) \<circ> ptrFromPAddr);
      dm \<leftarrow> gets (\<lambda>s. (device_mem s) \<circ> ptrFromPAddr);
      ds \<leftarrow> gets (device_state \<circ> machine_state);

      \<comment> \<open>Non-deterministically execute one of the user's operations.\<close>
      u \<leftarrow> return (uop t pl pr pxn (tc, um|`allow_read, (ds \<circ> ptrFromPAddr)|` allow_read));
      assert (u \<noteq> {});
      (e,(tc',um',ds')) \<leftarrow> select u;

      \<comment> \<open>Update the changes the user made to memory into our model.
         We ignore changes that took place where they didn't have
         write permissions. (uop shouldn't be doing that --- if it is,
         uop isn't correctly modelling real hardware.)\<close>
      do_machine_op (user_memory_update (((um' |` allow_write) \<circ> addrFromPPtr) |` (-(dom ds))));

      do_machine_op (device_memory_update (((ds' |` allow_write) \<circ> addrFromPPtr) |` (dom ds)));

      return (e,tc')
   od"


named_theorems UserOp_IF_assms

lemma arch_globals_equiv_underlying_memory_update[UserOp_IF_assms, simp]:
  "arch_globals_equiv ct it kh kh' as as' (underlying_memory_update f ms) ms' =
   arch_globals_equiv ct it kh kh' as as' ms ms'"
  "arch_globals_equiv ct it kh kh' as as' ms (underlying_memory_update f ms') =
   arch_globals_equiv ct it kh kh' as as' ms ms'"
  by auto

lemma arch_globals_equiv_device_state_update[UserOp_IF_assms, simp]:
  "arch_globals_equiv ct it kh kh' as as' (device_state_update f ms) ms' =
   arch_globals_equiv ct it kh kh' as as' ms ms'"
  "arch_globals_equiv ct it kh kh' as as' ms (device_state_update f ms') =
   arch_globals_equiv ct it kh kh' as as' ms ms'"
  by auto

end


requalify_types RISCV64.user_transition_if

global_interpretation UserOp_IF_1?: UserOp_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact UserOp_IF_assms)?)
qed


context Arch begin global_naming RISCV64

lemma requiv_get_pt_of_thread_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; is_subject aag (cur_thread s);
     pt_ref \<noteq> riscv_global_pt (arch_state s); pt_ref' \<noteq> riscv_global_pt (arch_state s');
     get_vspace_of_thread (kheap s) (arch_state s) (cur_thread s) = pt_ref;
     get_vspace_of_thread (kheap s') (arch_state s') (cur_thread s') = pt_ref' \<rbrakk>
     \<Longrightarrow> pt_ref = pt_ref'"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (subgoal_tac "aag_can_read aag (cur_thread s)")
   apply (clarsimp simp: get_vspace_of_thread_eq)
  apply simp
  done

lemma requiv_get_pt_entry_eq:
  "\<lbrakk> reads_equiv aag s t; invs s; pas_refined aag s; is_subject aag pt; vref \<in> user_region;
     \<exists>asid vref. vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, pt) \<rbrakk>
     \<Longrightarrow> pt_lookup_slot pt vref (ptes_of False s) = pt_lookup_slot pt vref (ptes_of False t)"
  apply (clarsimp simp: pt_lookup_slot_def)
  apply (clarsimp simp: pt_lookup_slot_from_level_def)
  apply (frule_tac pt=pt and vptr=vref in pt_walk_reads_equiv[where bot_level=0])
          apply clarsimp+
    apply (fastforce simp: reads_equiv_f_def)
   apply (fastforce elim: vs_lookup_table_vref_independent)
  apply (clarsimp simp: obind_def split: option.splits)
  done

lemma requiv_get_page_info_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; invs s; is_subject aag pt; x \<notin> kernel_mappings;
     \<exists>asid. vs_lookup_table max_pt_level asid x s = Some (max_pt_level, pt) \<rbrakk>
     \<Longrightarrow> get_page_info (aobjs_of False s) pt x = get_page_info (aobjs_of False s') pt x"
sorry (* broken by timeprot -scottb
  apply (clarsimp simp: get_page_info_def obind_def)
  apply (subgoal_tac "pt_lookup_slot pt x (ptes_of s) = pt_lookup_slot pt x (ptes_of s')")
   apply (clarsimp split: option.splits)
   apply (case_tac "pt_lookup_slot pt x (ptes_of s') = Some (a, b)"; clarsimp)
   apply (frule_tac ptr=b in ptes_of_reads_equiv[rotated])
    apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
    apply (prop_tac "ba = bb", clarsimp simp: pt_slot_offset_def)
    apply (frule pt_walk_is_aligned)
     apply (erule vs_lookup_table_is_aligned; clarsimp simp: canonical_not_kernel_is_user)
    apply (erule pt_walk_is_subject, (fastforce simp: canonical_not_kernel_is_user)+)
  apply (rule requiv_get_pt_entry_eq; fastforce simp: canonical_not_kernel_is_user)
  done
*)

lemma requiv_vspace_of_thread_global_pt:
  "\<lbrakk> reads_equiv aag s s'; is_subject aag (cur_thread s); invs s; pas_refined aag s;
     get_vspace_of_thread (kheap s) (arch_state s) (cur_thread s) = global_pt s \<rbrakk>
     \<Longrightarrow> get_vspace_of_thread (kheap s') (arch_state s') (cur_thread s') = global_pt s'"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (prop_tac "aag_can_read aag (cur_thread s)", simp)
  apply (clarsimp simp: get_vspace_of_thread_def
                 split: option.split kernel_object.splits cap.splits arch_cap.splits)
  apply (rename_tac tcb word word' word'')
  apply (subgoal_tac "aag_can_read_asid aag word'")
   apply (subgoal_tac "s \<turnstile> ArchObjectCap (PageTableCap word (Some (word',word'')))")
    apply (clarsimp simp: equiv_asids_def equiv_asid_def valid_cap_def obind_def
                          vspace_for_asid_def vspace_for_pool_def pool_for_asid_def)
    apply (clarsimp simp: word_gt_0 typ_at_eq_kheap_obj)
    apply (drule_tac x=word' in spec)
    apply (case_tac "word' = 0"; clarsimp)
    apply (clarsimp simp: asid_pools_of_ko_at obj_at_def asid_low_bits_of_def opt_map_def
                   split: option.splits)
    apply (frule valid_global_arch_objs_global_ptD[OF invs_valid_global_arch_objs])
    apply (drule invs_valid_global_refs)
    apply (drule_tac ptr="((cur_thread s), tcb_cnode_index 1)" in valid_global_refsD2[rotated])
     apply (subst caps_of_state_tcb_cap_cases)
       apply (simp add: get_tcb_def)
      apply (simp add: dom_tcb_cap_cases[simplified])
     apply simp
    apply (simp add: cap_range_def global_refs_def)
   apply (cut_tac s=s and t="cur_thread s" and tcb=tcb in objs_valid_tcb_vtable)
     apply (fastforce simp: invs_valid_objs get_tcb_def)+
  apply (subgoal_tac "(pasObjectAbs aag (cur_thread s), Control, pasASIDAbs aag word')
                        \<in> state_asids_to_policy aag s")
   apply (frule pas_refined_Control_into_is_subject_asid)
    apply (fastforce simp: pas_refined_def)
   apply simp
  apply (cut_tac aag=aag and ptr="(cur_thread s, tcb_cnode_index 1)" in sata_asid)
    prefer 3
    apply (simp add: caps_of_state_tcb_cap_cases get_tcb_def dom_tcb_cap_cases[simplified])+
  done

lemma vspace_for_asid_get_vspace_of_thread:
  "get_vspace_of_thread (kheap s) (arch_state s) ct \<noteq> global_pt s
   \<Longrightarrow> \<exists>asid. vspace_for_asid False asid s = Some (get_vspace_of_thread (kheap s) (arch_state s) ct)"
  by (fastforce simp: get_vspace_of_thread_def
               split: option.splits kernel_object.splits cap.splits arch_cap.splits)

lemma pt_of_thread_same_agent:
  "\<lbrakk> pas_refined aag s; is_subject aag tcb_ptr;
     get_vspace_of_thread (kheap s) (arch_state s) tcb_ptr = pt; pt \<noteq> global_pt s \<rbrakk>
     \<Longrightarrow> pasObjectAbs aag tcb_ptr = pasObjectAbs aag pt"
  apply (rule_tac aag="pasPolicy aag" in aag_wellformed_Control[rotated])
   apply (fastforce simp: pas_refined_def)
  apply (rule pas_refined_mem[rotated], simp)
  apply (clarsimp simp: get_vspace_of_thread_eq)
  apply (cut_tac ptr="(tcb_ptr, tcb_cnode_index 1)" in sbta_caps)
     prefer 4
     apply (simp add: state_objs_to_policy_def)
    apply (subst caps_of_state_tcb_cap_cases)
      apply (simp add: get_tcb_def)
     apply (simp add: dom_tcb_cap_cases[simplified])
    apply simp
   apply (simp add: obj_refs_def)
  apply (simp add: cap_auth_conferred_def arch_cap_auth_conferred_def)
  done

lemma requiv_ptable_rights_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s';
     is_subject aag (cur_thread s); invs s; invs s' \<rbrakk>
     \<Longrightarrow> ptable_rights_s s = ptable_rights_s s'"
  sorry (* broken by timeprot -scottb
  apply (simp add: ptable_rights_s_def)
  apply (rule ext)
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_rights_def split: option.splits)
   apply (rule conjI; clarsimp)
    apply (frule some_get_page_info_kmapsD;
           fastforce dest: invs_arch_state vspace_for_asid_get_vspace_of_thread
                     simp: valid_arch_state_def kernel_mappings_canonical)
   apply (frule some_get_page_info_kmapsD)
              apply (auto dest: invs_arch_state vspace_for_asid_get_vspace_of_thread
                          simp: valid_arch_state_def kernel_mappings_canonical)[12]
   apply (frule_tac r=b in some_get_page_info_kmapsD)
              apply (auto dest: invs_arch_state vspace_for_asid_get_vspace_of_thread
                          simp: valid_arch_state_def kernel_mappings_canonical)[12]
  apply (case_tac "get_vspace_of_thread (kheap s) (arch_state s) (cur_thread s) =
                   riscv_global_pt (arch_state s)")
   apply (frule requiv_vspace_of_thread_global_pt)
       apply (auto)[4]
   apply (fastforce dest: get_page_info_gpd_kmaps[rotated, rotated]
                    simp: ptable_rights_def invs_valid_global_objs invs_arch_state
                   split: option.splits)+
  apply (case_tac "get_vspace_of_thread (kheap s') (arch_state s') (cur_thread s') =
                   riscv_global_pt (arch_state s')")
   apply (drule reads_equiv_sym)
   apply (frule requiv_vspace_of_thread_global_pt; fastforce simp: reads_equiv_def)
  apply (simp add: ptable_rights_def)
  apply (frule requiv_get_pt_of_thread_eq)
        apply (auto)[6]
  apply (frule pt_of_thread_same_agent, simp+)
  apply (subst requiv_get_page_info_eq, simp+)
   apply (drule sym[where s="get_vspace_of_thread _ _ _"], clarsimp)
   apply (fastforce dest: get_vspace_of_thread_reachable elim: vs_lookup_table_vref_independent)+
  done
*)

lemma requiv_ptable_attrs_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s';
     is_subject aag (cur_thread s); invs s; invs s'; ptable_rights_s s x \<noteq> {} \<rbrakk>
     \<Longrightarrow> ptable_attrs_s s x = ptable_attrs_s s' x"
  sorry (* broken by timeprot -scottb
  apply (simp add: ptable_attrs_s_def ptable_rights_s_def)
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_attrs_def split: option.splits)
   apply (rule conjI)
    apply clarsimp
    apply (frule some_get_page_info_kmapsD)
               apply (auto simp: vspace_for_asid_get_vspace_of_thread ptable_rights_def)[12]
   apply clarsimp
   apply (frule some_get_page_info_kmapsD)
              apply (auto dest: invs_arch_state vspace_for_asid_get_vspace_of_thread
                          simp: valid_arch_state_def kernel_mappings_canonical ptable_rights_def)[12]
  apply (case_tac "get_vspace_of_thread (kheap s) (arch_state s) (cur_thread s) =
                   riscv_global_pt (arch_state s)")
   apply (frule requiv_vspace_of_thread_global_pt)
       apply (fastforce+)[4]
   apply (clarsimp simp: ptable_attrs_def split: option.splits)
   apply (rule conjI)
    apply clarsimp
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply ((fastforce simp: invs_valid_global_objs invs_arch_state)+)[3]
   apply clarsimp
   apply (rule conjI)
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply ((fastforce simp: invs_valid_global_objs invs_arch_state)+)[3]
   apply clarsimp
   apply (frule get_page_info_gpd_kmaps[rotated, rotated])
     apply ((fastforce simp: invs_valid_global_objs invs_arch_state)+)[3]
  apply (case_tac "get_vspace_of_thread (kheap s') (arch_state s') (cur_thread s') =
                   riscv_global_pt (arch_state s')")
   apply (drule reads_equiv_sym)
   apply (frule requiv_vspace_of_thread_global_pt)
       apply ((fastforce simp: reads_equiv_def)+)[5]
  apply (simp add: ptable_attrs_def)
  apply (frule requiv_get_pt_of_thread_eq, simp+)[1]
  apply (frule pt_of_thread_same_agent, simp+)[1]
  apply (subst requiv_get_page_info_eq, simp+)
   apply (drule sym[where s="get_vspace_of_thread _ _ _"], clarsimp)
   apply (fastforce dest: get_vspace_of_thread_reachable elim: vs_lookup_table_vref_independent)+
  done
*)

lemma requiv_ptable_lift_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s'; invs s;
     invs s'; is_subject aag (cur_thread s); ptable_rights_s s x \<noteq> {} \<rbrakk>
     \<Longrightarrow> ptable_lift_s s x = ptable_lift_s s' x"
  sorry (* broken by timeprot -scottb
  apply (simp add: ptable_lift_s_def ptable_rights_s_def)
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_lift_def split: option.splits)
   apply (rule conjI)
    apply clarsimp
    apply (frule some_get_page_info_kmapsD)
               apply (auto simp: vspace_for_asid_get_vspace_of_thread ptable_rights_def)[12]
   apply clarsimp
   apply (frule some_get_page_info_kmapsD)
              apply (auto dest: invs_arch_state vspace_for_asid_get_vspace_of_thread
                          simp: valid_arch_state_def kernel_mappings_canonical ptable_rights_def)[12]
  apply (case_tac "get_vspace_of_thread (kheap s) (arch_state s) (cur_thread s) =
                   riscv_global_pt (arch_state s)")
   apply (frule requiv_vspace_of_thread_global_pt)
       apply (fastforce+)[4]
   apply (clarsimp simp: ptable_lift_def split: option.splits)
   apply (rule conjI)
    apply clarsimp
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply ((fastforce simp: invs_valid_global_objs invs_arch_state)+)[3]
   apply clarsimp
   apply (rule conjI)
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply ((fastforce simp: invs_valid_global_objs invs_arch_state)+)[3]
   apply clarsimp
   apply (frule get_page_info_gpd_kmaps[rotated, rotated])
     apply ((fastforce simp: invs_valid_global_objs invs_arch_state)+)[3]
  apply (case_tac "get_vspace_of_thread (kheap s') (arch_state s') (cur_thread s') =
                   riscv_global_pt (arch_state s')")
   apply (drule reads_equiv_sym)
   apply (frule requiv_vspace_of_thread_global_pt)
       apply ((fastforce simp: reads_equiv_def)+)[5]
  apply (simp add: ptable_lift_def)
  apply (frule requiv_get_pt_of_thread_eq, simp+)[1]
  apply (frule pt_of_thread_same_agent, simp+)[1]
  apply (subst requiv_get_page_info_eq, simp+)
   apply (drule sym[where s="get_vspace_of_thread _ _ _"], clarsimp)
   apply (fastforce dest: get_vspace_of_thread_reachable elim: vs_lookup_table_vref_independent)+
  done
*)

lemma requiv_ptable_xn_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s';
     is_subject aag (cur_thread s); invs s; invs s'; ptable_rights_s s x \<noteq> {} \<rbrakk>
     \<Longrightarrow> ptable_xn_s s x = ptable_xn_s s' x"
  by (simp add: ptable_xn_s_def requiv_ptable_attrs_eq)

lemma data_at_obj_range:
  "\<lbrakk> data_at sz ptr s; pspace_aligned s; valid_objs s \<rbrakk>
     \<Longrightarrow> ptr + (offset && mask (pageBitsForSize sz)) \<in> obj_range ptr (ArchObj (DataPage dev sz))"
  apply (clarsimp simp: data_at_def)
  apply (elim disjE)
   apply (clarsimp simp: obj_at_def)
   apply (drule (2) ptr_in_obj_range)
   apply (clarsimp simp: obj_bits_def obj_range_def)
   apply fastforce
  apply (clarsimp simp: obj_at_def)
  apply (drule (2) ptr_in_obj_range)
  apply (clarsimp simp: obj_bits_def obj_range_def)
  apply fastforce
  done

lemma obj_range_data_for_cong:
  "obj_range ptr (ArchObj (DataPage dev sz')) = obj_range ptr (ArchObj (DataPage False sz'))"
  by (simp add: obj_range_def)

lemma pspace_distinct_def':
  "pspace_distinct \<equiv>
     \<lambda>s. \<forall>x y ko ko'. kheap s x = Some ko \<and> kheap s y = Some ko' \<and> x \<noteq> y
                      \<longrightarrow> obj_range x ko \<inter> obj_range y ko' = {}"
  by (auto simp: pspace_distinct_def obj_range_def field_simps)

lemma data_at_disjoint_equiv:
  "\<lbrakk> ptr' \<noteq> ptr;data_at sz' ptr' s; data_at sz ptr s; valid_objs s; pspace_aligned s;
     pspace_distinct s; ptr' \<in> obj_range ptr (ArchObj (DataPage dev sz)) \<rbrakk>
     \<Longrightarrow> False"
  apply (frule (2) data_at_obj_range[where offset = 0,simplified])
  apply (clarsimp simp: data_at_def obj_at_def)
  apply (elim disjE)
  by (clarsimp dest!: spec simp: obj_at_def pspace_distinct_def'
      , erule impE, erule conjI2[OF conjI2], (fastforce+)[2]
      , fastforce cong: obj_range_data_for_cong)+

lemma is_aligned_pptrBaseOffset:
  "is_aligned pptrBaseOffset (pageBitsForSize sz)"
  by (case_tac sz, simp_all add: pptrBaseOffset_def paddrBase_def pageBits_def canonical_bit_def
                                 ptTranslationBits_def pptrBase_def is_aligned_def)

lemma ptrFromPAddr_mask_simp:
  "ptrFromPAddr z && ~~ mask (pageBitsForSize l) =
   ptrFromPAddr (z && ~~ mask (pageBitsForSize l))"
  apply (simp add: ptrFromPAddr_def field_simps)
  apply (subst mask_out_add_aligned[OF is_aligned_pptrBaseOffset])
  apply simp
  done

lemma pageBitsForSize_le_canonical_bit:
  "pageBitsForSize sz \<le> canonical_bit"
  by (cases sz, simp_all add: pageBits_def ptTranslationBits_def canonical_bit_def)

lemma data_at_same_size:
  assumes dat_sz':
    "data_at sz' (ptrFromPAddr base) s"
  and dat_sz:
    "data_at sz
       (ptrFromPAddr (base + (x && mask (pageBitsForSize sz'))) && ~~ mask (pageBitsForSize sz)) s"
  and vs:
    "pspace_distinct s" "pspace_aligned s" "valid_objs s"
  shows "sz' = sz"
proof -
  from dat_sz' and dat_sz
  have trivial:
    "sz' \<noteq> sz
     \<Longrightarrow> ptrFromPAddr (base + (x && mask (pageBitsForSize sz'))) && ~~ mask (pageBitsForSize sz) \<noteq>
         ptrFromPAddr base"
    by (auto simp: data_at_def obj_at_def)
  have sz_equiv: "(pageBitsForSize sz = pageBitsForSize sz') = (sz' = sz)"
    by (clarsimp simp: pageBitsForSize_def ptTranslationBits_def split: vmpage_size.splits)
  show ?thesis
    apply (rule sz_equiv[THEN iffD1])
    apply (rule ccontr)
    apply (drule neq_iff[THEN iffD1])
    using dat_sz' dat_sz vs
    apply (cut_tac trivial) prefer 2
     apply (fastforce simp: sz_equiv)
    apply (frule(1) data_at_aligned)
    apply (elim disjE)
     apply (erule(5) data_at_disjoint_equiv)
     apply (unfold obj_range_def)
     apply (rule mask_in_range[THEN iffD1])
      apply (simp add: obj_bits_def)+
     apply (simp add: mask_lower_twice ptrFromPAddr_mask_simp)
     apply (rule arg_cong[where f = ptrFromPAddr])
     apply (subst (asm) is_aligned_ptrFromPAddr_n_eq[OF pageBitsForSize_le_canonical_bit])
     apply (subst neg_mask_add_aligned[OF _ and_mask_less'])
       apply simp
      apply (fastforce simp: pbfs_less_wb'[unfolded word_bits_def,simplified])
     apply (simp add: is_aligned_neg_mask_eq)
    apply (drule not_sym)
    apply (erule(5) data_at_disjoint_equiv)
    apply (unfold obj_range_def)
    apply (rule mask_in_range[THEN iffD1])
     apply (simp add: obj_bits_def is_aligned_neg_mask)+
    apply (simp add: mask_lower_twice ptrFromPAddr_mask_simp)
    apply (rule arg_cong[where f = ptrFromPAddr])
    apply (subst (asm) is_aligned_ptrFromPAddr_n_eq[OF pageBitsForSize_le_canonical_bit])
    apply (rule sym)
    apply (subst mask_lower_twice[symmetric])
     apply (erule less_imp_le_nat)
    apply (rule arg_cong[where f = "\<lambda>x. x && ~~ mask z" for z])
    apply (subst neg_mask_add_aligned[OF _ and_mask_less'])
      apply simp
     apply (fastforce simp: pbfs_less_wb'[unfolded word_bits_def,simplified])
    apply simp
    done
qed

lemma level_le_2_cases:
  "(level :: vm_level) \<le> 2 \<Longrightarrow> level = 0 \<or> level = 1 \<or> level = 2"
  apply clarsimp
  apply (erule_tac P="level=2" in swap)
  apply (subst (asm) order.order_iff_strict)
  apply (erule disjE_R)
   apply (clarsimp simp: order.strict_implies_not_eq)
   apply (induct level; clarsimp)
   apply (drule meta_mp)
    apply (erule order.strict_implies_not_eq)
   apply (drule meta_mp)
    apply (rule bit0.minus_one_leq_less)
     apply (erule order.strict_implies_order)
    apply (erule bit0.zero_least)
   apply clarsimp
  apply clarsimp
  done

lemma ptable_lift_data_consistant:
  assumes vs: "valid_state s"
  and pt_lift: "ptable_lift t s x = Some ptr"
  and dat: "data_at sz ((ptrFromPAddr ptr) && ~~ mask (pageBitsForSize sz)) s"
  and misc: "get_vspace_of_thread (kheap s) (arch_state s) t \<noteq> riscv_global_pt (arch_state s)"
            "x \<notin> kernel_mappings"
  shows "ptable_lift t s (x && ~~ mask (pageBitsForSize sz)) =
         Some (ptr && ~~ mask (pageBitsForSize sz))"
proof -
  have vs': "valid_objs s \<and> valid_arch_state s \<and> valid_vspace_objs s
                          \<and> pspace_distinct s \<and> pspace_aligned s"
    using vs by (simp add: valid_state_def valid_pspace_def)
  thus ?thesis
  sorry (* broken by timeprot -scottb
    using pt_lift dat vs'
    apply (clarsimp simp: ptable_lift_def split: option.splits)
    apply (clarsimp simp: get_page_info_def simp: obind_def split: option.splits)
    apply (rule exE[OF vspace_for_asid_get_vspace_of_thread[OF misc(1)]])
    apply (rename_tac level pt pde asid)
    apply (case_tac pde; clarsimp simp: pte_info_def)
    apply (frule pt_lookup_slot_max_pt_level)
    apply (frule vspace_for_asid_vs_lookup)
    apply (frule canonical_not_kernel_is_user[OF misc(2)])
    apply (frule_tac level=level in valid_vspace_objs_pte)
      apply clarsimp
     apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
     apply (fastforce simp: table_base_pt_slot_offset[OF vs_lookup_table_is_aligned]
                      dest: valid_arch_state_asid_table dest!: pt_lookup_vs_lookupI
                     intro: vs_lookup_level)
    apply (erule disjE[OF _  _ FalseE])
     prefer 2
     apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def in_omonad pt_walk.simps)
     apply (clarsimp split: if_splits)
      apply (fastforce dest: pt_walk_max_level simp: max_pt_level_def2)
     apply (subst (asm) table_index_max_level_slots; clarsimp?)
     apply (fastforce dest: vs_lookup_table_is_aligned valid_arch_state_asid_table)
    apply (clarsimp simp: valid_pte_def)
    apply (frule data_at_same_size; simp?)
    apply (prop_tac "pt_lookup_slot (get_vspace_of_thread (kheap s) (arch_state s) t)
                                    (vref_for_level x level) (ptes_of s) = Some (level, pt)")
     apply (case_tac "level = max_pt_level"; clarsimp)
      apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def in_omonad)
      apply (subst (asm) pt_lookup_vs_lookup_eq)
        apply clarsimp
       apply (clarsimp simp: vspace_for_asid_def)
      apply (clarsimp simp: pt_walk.simps)
      apply (fastforce dest: pt_walk_max_level simp: max_pt_level_def2 in_omonad)
     apply (fold vref_for_level_def)
     apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def in_omonad)
     apply (rule exI)
     apply (subst pt_walk_vref_for_level_eq[where vref'=x])
       apply (fastforce dest: level_le_2_cases le_neq_trans simp: max_pt_level_def2 max_def)
      apply clarsimp
     apply fastforce
    apply (fastforce simp: vref_for_level_def is_aligned_mask_out_add_eq mask_AND_NOT_mask
                           pt_bits_left_le_canonical is_aligned_ptrFromPAddr_n_eq
                     elim: canonical_vref_for_levelI[unfolded vref_for_level_def]
                     dest: data_at_aligned)
    done
*)
qed

lemma ptable_rights_data_consistant:
  assumes vs: "valid_state s"
  and pt_lift: "ptable_lift t s x = Some ptr"
  and dat: "data_at sz ((ptrFromPAddr ptr) && ~~ mask (pageBitsForSize sz)) s"
  and misc: "get_vspace_of_thread (kheap s) (arch_state s) t \<noteq>
             riscv_global_pt (arch_state s)" "x \<notin> kernel_mappings"
  shows "ptable_rights t s (x && ~~ mask (pageBitsForSize sz)) = ptable_rights t s x"
proof -
  have vs': "valid_objs s \<and> valid_arch_state s \<and> valid_vspace_objs s
                          \<and> pspace_distinct s \<and> pspace_aligned s"
    using vs by (simp add: valid_state_def valid_pspace_def)
  thus ?thesis
  sorry (* broken by timeprot -scottb
    using pt_lift dat vs'
    apply (clarsimp simp: ptable_rights_def ptable_lift_def split: option.splits)
    apply (clarsimp simp: get_page_info_def simp: obind_def split: option.splits)
    apply (rule exE[OF vspace_for_asid_get_vspace_of_thread[OF misc(1)]])
    apply (rename_tac level pt pde asid)
    apply (case_tac pde; clarsimp simp: pte_info_def)
    apply (frule pt_lookup_slot_max_pt_level)
    apply (frule vspace_for_asid_vs_lookup)
    apply (frule canonical_not_kernel_is_user[OF misc(2)])
    apply (frule_tac level=level in valid_vspace_objs_pte)
      apply clarsimp
     apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
     apply (fastforce simp: table_base_pt_slot_offset[OF vs_lookup_table_is_aligned]
                      dest: valid_arch_state_asid_table dest!: pt_lookup_vs_lookupI
                     intro: vs_lookup_level)
    apply (erule disjE[OF _  _ FalseE])
     prefer 2
     apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def in_omonad pt_walk.simps)
     apply (clarsimp split: if_splits)
      apply (fastforce dest: pt_walk_max_level simp: max_pt_level_def2)
     apply (subst (asm) table_index_max_level_slots; clarsimp?)
     apply (fastforce dest: vs_lookup_table_is_aligned valid_arch_state_asid_table)
    apply (clarsimp simp: valid_pte_def)
    apply (frule data_at_same_size; simp?)
    apply (prop_tac "pt_lookup_slot (get_vspace_of_thread (kheap s) (arch_state s) t)
                                    (vref_for_level x level) (ptes_of s) = Some (level, pt)")
     apply (case_tac "level = max_pt_level"; clarsimp)
      apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def in_omonad)
      apply (subst (asm) pt_lookup_vs_lookup_eq)
        apply clarsimp
       apply (clarsimp simp: vspace_for_asid_def)
      apply (clarsimp simp: pt_walk.simps)
      apply (fastforce dest: pt_walk_max_level simp: max_pt_level_def2 in_omonad)
     apply (fold vref_for_level_def)
     apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def in_omonad)
     apply (rule exI)
     apply (subst pt_walk_vref_for_level_eq[where vref'=x])
       apply (fastforce dest: level_le_2_cases le_neq_trans simp: max_pt_level_def2 max_def)
      apply clarsimp
     apply fastforce
    apply (clarsimp simp: vref_for_level_def)
    apply (fastforce dest: canonical_vref_for_levelI[unfolded vref_for_level_def]
                     simp: pt_bits_left_le_canonical )
    done
*)
qed


lemma user_op_access_data_at:
  "\<lbrakk> invs s; pas_refined aag s; is_subject aag tcb; ptable_lift tcb s x = Some ptr;
     data_at sz ((ptrFromPAddr ptr) && ~~ mask (pageBitsForSize sz)) s;
     auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x) \<rbrakk>
     \<Longrightarrow> (pasObjectAbs aag tcb, auth,
          pasObjectAbs aag (ptrFromPAddr (ptr && ~~ mask (pageBitsForSize sz)))) \<in> pasPolicy aag"
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_lift_def ptable_rights_def split: option.splits)
   apply (frule some_get_page_info_kmapsD)
              apply (fastforce dest: invs_arch_state invs_equal_kernel_mappings
                               simp: valid_arch_state_def vspace_for_asid_get_vspace_of_thread
                                     kernel_mappings_canonical vspace_cap_rights_to_auth_def)+
  apply (case_tac "get_vspace_of_thread (kheap s) (arch_state s) tcb = riscv_global_pt (arch_state s)")
   apply (clarsimp simp: ptable_lift_def ptable_rights_def split: option.splits)
   apply (frule get_page_info_gpd_kmaps[rotated, rotated])
     apply (fastforce simp: invs_valid_global_objs invs_arch_state)+
  apply (frule (2) ptable_lift_data_consistant[rotated 2])
    apply fastforce
   apply fastforce
  apply (frule (2) ptable_rights_data_consistant[rotated 2])
    apply fastforce
   apply fastforce
  apply (erule (3) user_op_access)
  apply simp
  done

lemma user_frame_at_equiv:
  "\<lbrakk> typ_at (AArch (AUserData sz)) p s; equiv_for P kheap s s'; P p \<rbrakk>
     \<Longrightarrow> typ_at (AArch (AUserData sz)) p s'"
  by (clarsimp simp: equiv_for_def obj_at_def)

lemma device_frame_at_equiv:
  "\<lbrakk> typ_at (AArch (ADeviceData sz)) p s; equiv_for P kheap s s'; P p \<rbrakk>
     \<Longrightarrow> typ_at (AArch (ADeviceData sz)) p s'"
  by (clarsimp simp: equiv_for_def obj_at_def)

lemma typ_at_user_data_at:
  "typ_at (AArch (AUserData sz)) p s \<Longrightarrow> data_at sz p s"
  by (simp add: data_at_def)

lemma typ_at_device_data_at:
  "typ_at (AArch (ADeviceData sz)) p s \<Longrightarrow> data_at sz p s"
  by (simp add: data_at_def)

lemma requiv_device_mem_eq:
  "\<lbrakk> reads_equiv aag s s'; globals_equiv s s'; invs s; invs s';
     is_subject aag (cur_thread s); AllowRead \<in> ptable_rights_s s x;
     ptable_lift_s s x = Some y; pas_refined aag s; pas_refined aag s' \<rbrakk>
     \<Longrightarrow> device_mem s (ptrFromPAddr y) = device_mem s' (ptrFromPAddr y)"
  apply (simp add: device_mem_def)
  apply (rule conjI)
   apply (erule reads_equivE)
   apply (clarsimp simp: in_device_frame_def)
   apply (rule exI)
   apply (rule device_frame_at_equiv)
     apply assumption+
   apply (erule_tac f="underlying_memory" in equiv_forE)
   apply (frule_tac auth=Read in user_op_access_data_at[where s=s])
        apply (fastforce simp: ptable_lift_s_def ptable_rights_s_def vspace_cap_rights_to_auth_def
               | intro typ_at_device_data_at)+
   apply (rule reads_read)
   apply (fastforce simp: ptrFromPAddr_mask_simp)
  apply clarsimp
  apply (frule requiv_ptable_rights_eq, fastforce+)
  apply (frule requiv_ptable_lift_eq, fastforce+)
  apply (clarsimp simp: globals_equiv_def)
  apply (erule notE)
  apply (erule reads_equivE)
  apply (clarsimp simp: in_device_frame_def)
  apply (rule exI)
  apply (rule device_frame_at_equiv)
    apply assumption+
   apply (erule_tac f="underlying_memory" in equiv_forE)
   apply (erule equiv_symmetric[THEN iffD1])
  apply (frule_tac auth=Read in user_op_access_data_at[where s=s'])
       apply (fastforce simp: ptable_lift_s_def ptable_rights_s_def vspace_cap_rights_to_auth_def
              | intro typ_at_device_data_at)+
  apply (rule reads_read)
  apply (fastforce simp: ptrFromPAddr_mask_simp)
  done

lemma requiv_user_mem_eq:
  "\<lbrakk> reads_equiv aag s s'; globals_equiv s s'; invs s; invs s';
     is_subject aag (cur_thread s); AllowRead \<in> ptable_rights_s s x;
     ptable_lift_s s x = Some y; pas_refined aag s; pas_refined aag s' \<rbrakk>
     \<Longrightarrow> user_mem s (ptrFromPAddr y) = user_mem s' (ptrFromPAddr y)"
  apply (simp add: user_mem_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule context_conjI')
    apply (erule reads_equivE)
    apply (clarsimp simp: in_user_frame_def)
    apply (rule exI)
    apply (rule user_frame_at_equiv)
      apply assumption+
    apply (erule_tac f="underlying_memory" in equiv_forE)
    apply (frule_tac auth=Read in user_op_access_data_at[where s = s])
         apply (fastforce simp: ptable_lift_s_def ptable_rights_s_def vspace_cap_rights_to_auth_def
                | intro typ_at_user_data_at)+
    apply (rule reads_read)
    apply (fastforce simp: ptrFromPAddr_mask_simp)
   apply clarsimp
   apply (subgoal_tac "aag_can_read aag (ptrFromPAddr y)")
    apply (erule reads_equivE)
    apply clarsimp
    apply (erule_tac f="underlying_memory" in equiv_forE)
    apply simp
   apply (frule_tac auth=Read in user_op_access)
       apply (fastforce simp: ptable_lift_s_def ptable_rights_s_def vspace_cap_rights_to_auth_def)+
   apply (rule reads_read)
   apply simp
  apply (frule requiv_ptable_rights_eq, fastforce+)
  apply (frule requiv_ptable_lift_eq, fastforce+)
  apply (clarsimp simp: globals_equiv_def)
  apply (erule notE)
  apply (erule reads_equivE)
  apply (clarsimp simp: in_user_frame_def)
  apply (rule exI)
  apply (rule user_frame_at_equiv)
    apply assumption+
   apply (erule_tac f="underlying_memory" in equiv_forE)
   apply (erule equiv_symmetric[THEN iffD1])
  apply (frule_tac auth=Read in user_op_access_data_at[where s=s'])
       apply (fastforce simp: ptable_lift_s_def ptable_rights_s_def vspace_cap_rights_to_auth_def
              | intro typ_at_user_data_at)+
  apply (rule reads_read)
  apply (fastforce simp: ptrFromPAddr_mask_simp)
  done

lemma ptable_rights_imp_frameD:
  "\<lbrakk> ptable_lift t s x = Some y;valid_state s;ptable_rights t s x \<noteq> {} \<rbrakk>
     \<Longrightarrow> \<exists>sz. data_at sz (ptrFromPAddr y && ~~ mask (pageBitsForSize sz)) s"
  apply (subst (asm) addrFromPPtr_ptrFromPAddr_id[symmetric])
  apply (drule ptable_rights_imp_frame)
    apply simp+
   apply (rule addrFromPPtr_ptrFromPAddr_id[symmetric])
  apply (auto simp: in_user_frame_def in_device_frame_def
             dest!: spec typ_at_user_data_at typ_at_device_data_at)
  done

lemma requiv_user_device_eq:
  "\<lbrakk> reads_equiv aag s s'; globals_equiv s s'; invs s; invs s';
     is_subject aag (cur_thread s); AllowRead \<in> ptable_rights_s s x;
     ptable_lift_s s x = Some y; pas_refined aag s; pas_refined aag s' \<rbrakk>
     \<Longrightarrow> device_state (machine_state s) (ptrFromPAddr y) =
         device_state (machine_state s') (ptrFromPAddr y)"
  apply (simp add: ptable_lift_s_def)
  apply (frule ptable_rights_imp_frameD)
    apply fastforce
   apply (fastforce simp: ptable_rights_s_def)
  apply (erule reads_equivE)
  apply clarsimp
  apply (erule_tac f="device_state" in equiv_forD)
  apply (frule_tac auth=Read in user_op_access_data_at[where s = s])
       apply ((fastforce simp: ptable_lift_s_def ptable_rights_s_def vspace_cap_rights_to_auth_def
               | intro typ_at_user_data_at)+)[6]
  apply (rule reads_read)
  apply (frule_tac auth=Read in user_op_access)
      apply (fastforce simp: ptable_lift_s_def ptable_rights_s_def vspace_cap_rights_to_auth_def)+
  done


definition context_matches_state where
  "context_matches_state pl pr pxn ms s \<equiv> case ms of (um, ds) \<Rightarrow>
     pl = ptable_lift_s s |` {x. pr x \<noteq> {}} \<and>
     pr = ptable_rights_s s \<and>
     pxn = (\<lambda>x. pr x \<noteq> {} \<and> ptable_xn_s s x) \<and>
     um = (user_mem s \<circ> ptrFromPAddr) |` {y. \<exists>x. pl x = Some y \<and> AllowRead \<in> pr x} \<and>
     ds = (device_state (machine_state s) \<circ> ptrFromPAddr) |`
          {y. \<exists>x. pl x = Some y \<and> AllowRead \<in> pr x}"


lemma do_user_op_reads_respects_g:
  notes split_paired_All[simp del]
  shows
    "(\<forall>pl pr pxn tc ms s. P tc s \<and> context_matches_state pl pr pxn ms s
                          \<longrightarrow> (\<exists>x. uop (cur_thread s) pl pr pxn (tc, ms) = {x}))
     \<Longrightarrow> reads_respects_g aag l (pas_refined aag and invs and is_subject aag \<circ> cur_thread
                                                 and (\<lambda>s. cur_thread s \<noteq> idle_thread s) and P tc)
                          (do_user_op_if uop tc)"
  apply (simp add: do_user_op_if_def)
  apply (rule use_spec_ev)
  apply (rule spec_equiv_valid_add_asm)
  apply (rule spec_equiv_valid_add_rel[OF _ reads_equiv_g_refl])
  apply (rule spec_equiv_valid_add_rel'[OF _ affects_equiv_refl])
  apply (rule spec_equiv_valid_inv_gets[where proj=id,simplified])
   apply (clarsimp simp: reads_equiv_g_def)
   apply (rule requiv_ptable_rights_eq,simp+)[1]
  apply (rule spec_equiv_valid_inv_gets[where proj=id,simplified])
   apply (rule ext)
   apply (clarsimp simp: reads_equiv_g_def)
   apply (case_tac "ptable_rights_s st x = {}", simp)
   apply simp
   apply (rule requiv_ptable_xn_eq,simp+)[1]
  apply (rule spec_equiv_valid_inv_gets[where proj=id,simplified])
   apply (subst expand_restrict_map_eq,clarsimp)
   apply (clarsimp simp: reads_equiv_g_def)
   apply (rule requiv_ptable_lift_eq,simp+)[1]
  apply (rule spec_equiv_valid_inv_gets[where proj=id,simplified])
   apply (clarsimp simp: reads_equiv_g_def)
   apply (rule requiv_cur_thread_eq,fastforce)
  apply (rule spec_equiv_valid_inv_gets_more[where proj="\<lambda>m. dom m \<inter> cw"
                                               and projsnd="\<lambda>m. m |` cr" for cr and cw])
   apply (rule context_conjI')
    apply (subst expand_restrict_map_eq)
    apply (clarsimp simp: reads_equiv_g_def restrict_map_def)
    apply (rule requiv_user_mem_eq)
            apply simp+
   apply fastforce
  apply (rule spec_equiv_valid_inv_gets[where proj = "\<lambda>x. ()", simplified])
  apply (rule spec_equiv_valid_inv_gets_more[where proj = "\<lambda>m. (m \<circ> ptrFromPAddr) |` cr" for cr])
   apply (rule conjI)
    apply (subst expand_restrict_map_eq)
    apply (clarsimp simp: restrict_map_def reads_equiv_g_def)
    apply (rule requiv_user_device_eq)
            apply simp+
   apply (clarsimp simp: globals_equiv_def reads_equiv_g_def)
  apply (rule spec_equiv_valid_guard_imp)
   apply (wpsimp wp: dmo_user_memory_update_reads_respects_g dmo_device_state_update_reads_respects_g
                     dmo_device_state_update_reads_respects_g select_ev select_wp dmo_wp)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule spec)+
   apply (erule impE)
    prefer 2
    apply assumption
   apply (clarsimp simp: context_matches_state_def comp_def  reads_equiv_g_def globals_equiv_def)
  apply (clarsimp simp: reads_equiv_g_def globals_equiv_def)
  done

definition valid_vspace_objs_if where
  "valid_vspace_objs_if \<equiv> \<top>"

declare valid_vspace_objs_if_def[simp]

end

requalify_consts
  RISCV64.do_user_op_if
  RISCV64.valid_vspace_objs_if
  RISCV64.context_matches_state

requalify_facts
  RISCV64.do_user_op_reads_respects_g

end
