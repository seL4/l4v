(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchUserOp_IF
imports UserOp_IF
begin

context Arch begin global_naming ARM

definition ptable_lift_s where
  "ptable_lift_s s \<equiv> ptable_lift (cur_thread s) s"

definition ptable_rights_s where
  "ptable_rights_s s \<equiv> ptable_rights (cur_thread s) s"

(* FIXME: move to ADT_AI.thy *)
definition ptable_attrs :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> word32 \<Rightarrow> vm_attributes" where
 "ptable_attrs tcb s \<equiv>
    \<lambda>addr. case_option {} (fst o snd o snd)
             (get_page_info (\<lambda>obj. get_arch_obj (kheap s obj))
                            (get_pd_of_thread (kheap s) (arch_state s) tcb) addr)"

definition ptable_attrs_s :: "'z state \<Rightarrow> obj_ref \<Rightarrow> vm_attributes" where
 "ptable_attrs_s s \<equiv> ptable_attrs (cur_thread s) s"

definition ptable_xn_s where
  "ptable_xn_s s \<equiv>  \<lambda>addr. XNever \<in> ptable_attrs_s s addr"

definition getExMonitor :: "exclusive_monitors machine_monad" where
  "getExMonitor \<equiv> gets exclusive_state"

definition setExMonitor :: "exclusive_monitors \<Rightarrow> unit machine_monad" where
  "setExMonitor es \<equiv> modify (\<lambda>ms. ms\<lparr>exclusive_state := es\<rparr>)"


type_synonym user_state_if = "user_context \<times> user_mem \<times> device_state \<times> exclusive_monitors"

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

      \<comment> \<open>Fetch the 'execute never' bits of the current thread's page mappings.\<close>
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

      es \<leftarrow> do_machine_op getExMonitor;

      \<comment> \<open>Non-deterministically execute one of the user's operations.\<close>
      u \<leftarrow> return (uop t pl pr pxn (tc, um|`allow_read, (ds \<circ> ptrFromPAddr)|` allow_read, es));
      assert (u \<noteq> {});
      (e,(tc',um',ds',es')) \<leftarrow> select u;

      \<comment> \<open>Update the changes the user made to memory into our model.
         We ignore changes that took place where they didn't have
         write permissions. (uop shouldn't be doing that --- if it is,
         uop isn't correctly modelling real hardware.)\<close>
      do_machine_op (user_memory_update (((um' |` allow_write) \<circ> addrFromPPtr) |` (-(dom ds))));

      do_machine_op (device_memory_update (((ds' |` allow_write) \<circ> addrFromPPtr) |` (dom ds)));

      \<comment> \<open>Update exclusive monitor state used by the thread.\<close>
      do_machine_op (setExMonitor es');

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

context begin interpretation Arch .

requalify_types user_transition_if

end


global_interpretation UserOp_IF_1?: UserOp_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact UserOp_IF_assms)?)
qed


context Arch begin global_naming ARM

lemma requiv_get_pd_of_thread_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; is_subject aag (cur_thread s);
     pd_ref \<noteq> arm_global_pd (arch_state s); pd_ref' \<noteq> arm_global_pd (arch_state s');
     get_pd_of_thread (kheap s) (arch_state s) (cur_thread s) = pd_ref;
     get_pd_of_thread (kheap s') (arch_state s') (cur_thread s') = pd_ref' \<rbrakk>
     \<Longrightarrow> pd_ref = pd_ref'"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (subgoal_tac "aag_can_read aag (cur_thread s)")
   apply (clarsimp simp: get_pd_of_thread_eq)
  apply simp
  done

lemma requiv_get_pt_entry_eq:
  "\<lbrakk> reads_equiv aag s s'; is_subject aag pt \<rbrakk>
     \<Longrightarrow> get_pt_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pt x =
         get_pt_entry (\<lambda>obj. get_arch_obj (kheap s' obj)) pt x"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (subgoal_tac "aag_can_read aag pt")
   apply (simp add: get_pt_entry_def split: option.splits)
  apply (simp add: reads_lrefl)
  done

lemma requiv_get_pt_info_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; is_subject aag pt \<rbrakk>
     \<Longrightarrow> get_pt_info (\<lambda>obj. get_arch_obj (kheap s obj)) pt x =
         get_pt_info (\<lambda>obj. get_arch_obj (kheap s' obj)) pt x"
  apply (simp add: get_pt_info_def)
  apply (subst requiv_get_pt_entry_eq, simp+)
  done

lemma requiv_get_pd_entry_eq:
  "\<lbrakk> reads_equiv aag s s'; is_subject aag pd \<rbrakk>
     \<Longrightarrow> get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pd x =
         get_pd_entry (\<lambda>obj. get_arch_obj (kheap s' obj)) pd x"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (subgoal_tac "aag_can_read aag pd")
   apply (simp add: get_pd_entry_def split: option.splits)
  apply simp
  done

lemma requiv_get_page_info_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; is_subject aag pd; x \<notin> kernel_mappings \<rbrakk>
     \<Longrightarrow> get_page_info (\<lambda>obj. get_arch_obj (kheap s obj)) pd x =
         get_page_info (\<lambda>obj. get_arch_obj (kheap s' obj)) pd x"
  apply (simp add: get_page_info_def)
  apply (subst requiv_get_pd_entry_eq[symmetric], simp+)
  apply (clarsimp split: option.splits pde.splits)
  apply (frule pt_in_pd_same_agent, fastforce+)
  apply (rule requiv_get_pt_info_eq, simp+)
  done

lemma requiv_pd_of_thread_global_pd:
  "\<lbrakk> reads_equiv aag s s'; is_subject aag (cur_thread s); invs s; pas_refined aag s;
     get_pd_of_thread (kheap s) (arch_state s) (cur_thread s) = arm_global_pd (arch_state s) \<rbrakk>
     \<Longrightarrow> get_pd_of_thread (kheap s') (arch_state s') (cur_thread s') = arm_global_pd (arch_state s')"
  apply (erule reads_equivE)
  apply (erule equiv_forE)
  apply (subgoal_tac "aag_can_read aag (cur_thread s)")
   prefer 2
   apply simp
  apply (clarsimp simp: get_pd_of_thread_def2
                 split: option.splits kernel_object.splits cap.splits arch_cap.splits)
  apply (rename_tac tcb word word' p apool)
  apply (subgoal_tac "aag_can_read_asid aag word'")
   apply (subgoal_tac "s \<turnstile> ArchObjectCap (PageDirectoryCap word (Some word'))")
    apply (clarsimp simp: equiv_asids_def equiv_asid_def valid_cap_def)
    apply (drule_tac x=word' in spec)
    apply (clarsimp simp: word_gt_0 typ_at_eq_kheap_obj)
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
    apply simp
   apply (subst caps_of_state_tcb_cap_cases)
     apply (simp add: get_tcb_def)
    apply (simp add: dom_tcb_cap_cases[simplified])+
  done

lemma requiv_ptable_rights_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s';
     is_subject aag (cur_thread s); invs s; invs s' \<rbrakk>
     \<Longrightarrow> ptable_rights_s s = ptable_rights_s s'"
  apply (simp add: ptable_rights_s_def)
  apply (rule ext)
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_rights_def split: option.splits)
   apply (rule conjI)
    apply clarsimp
    apply (frule some_get_page_info_kmapsD)
       apply ((fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                               vspace_cap_rights_to_auth_def)+)[4]
   apply clarsimp
   apply (frule some_get_page_info_kmapsD)
      apply ((fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                              vspace_cap_rights_to_auth_def)+)[4]
   apply clarsimp
   apply (frule_tac r=b in some_get_page_info_kmapsD)
      apply ((fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                              vspace_cap_rights_to_auth_def)+)[4]
  apply (case_tac "get_pd_of_thread (kheap s) (arch_state s) (cur_thread s) =
                   arm_global_pd (arch_state s)")
   apply (frule requiv_pd_of_thread_global_pd)
       apply (fastforce+)[4]
   apply (clarsimp simp: ptable_rights_def split: option.splits)
   apply (rule conjI)
    apply clarsimp
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply ((fastforce simp: invs_valid_global_objs invs_arch_state)+)[3]
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (frule get_page_info_gpd_kmaps[rotated, rotated])
      apply ((fastforce simp: invs_valid_global_objs invs_arch_state)+)[3]
   apply clarsimp
   apply (frule get_page_info_gpd_kmaps[rotated, rotated])
     apply ((fastforce simp: invs_valid_global_objs invs_arch_state)+)[3]
  apply (case_tac "get_pd_of_thread (kheap s') (arch_state s') (cur_thread s') =
                   arm_global_pd (arch_state s')")
   apply (drule reads_equiv_sym)
   apply (frule requiv_pd_of_thread_global_pd)
       apply ((fastforce simp: reads_equiv_def)+)[5]
  apply (simp add: ptable_rights_def)
  apply (frule requiv_get_pd_of_thread_eq)
        apply (fastforce+)[6]
  apply (frule pd_of_thread_same_agent, simp+)
  apply (subst requiv_get_page_info_eq, simp+)
  done

lemma requiv_ptable_attrs_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s';
     is_subject aag (cur_thread s); invs s; invs s'; ptable_rights_s s x \<noteq> {} \<rbrakk>
     \<Longrightarrow> ptable_attrs_s s x = ptable_attrs_s s' x"
  apply (simp add: ptable_attrs_s_def ptable_rights_s_def)
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_attrs_def split: option.splits)
   apply (rule conjI)
    apply clarsimp
    apply (frule some_get_page_info_kmapsD)
       apply ((fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                               vspace_cap_rights_to_auth_def ptable_rights_def)+)[4]
   apply clarsimp
   apply (frule some_get_page_info_kmapsD)
      apply ((fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                              vspace_cap_rights_to_auth_def ptable_rights_def)+)[4]
  apply (case_tac "get_pd_of_thread (kheap s) (arch_state s) (cur_thread s) =
                   arm_global_pd (arch_state s)")
   apply (frule requiv_pd_of_thread_global_pd)
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
  apply (case_tac "get_pd_of_thread (kheap s') (arch_state s') (cur_thread s') =
                   arm_global_pd (arch_state s')")
   apply (drule reads_equiv_sym)
   apply (frule requiv_pd_of_thread_global_pd)
       apply ((fastforce simp: reads_equiv_def)+)[5]
  apply (simp add: ptable_attrs_def)
  apply (frule requiv_get_pd_of_thread_eq, simp+)[1]
  apply (frule pd_of_thread_same_agent, simp+)[1]
  apply (subst requiv_get_page_info_eq, simp+)[1]
  done

lemma requiv_ptable_lift_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s'; invs s;
     invs s'; is_subject aag (cur_thread s); ptable_rights_s s x \<noteq> {} \<rbrakk>
     \<Longrightarrow> ptable_lift_s s x = ptable_lift_s s' x"
  apply (simp add: ptable_lift_s_def ptable_rights_s_def)
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_lift_def split: option.splits)
   apply (rule conjI)
    apply clarsimp
    apply (frule some_get_page_info_kmapsD)
       apply ((fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                               vspace_cap_rights_to_auth_def ptable_rights_def)+)[4]
   apply clarsimp
   apply (frule some_get_page_info_kmapsD)
      apply ((fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                              vspace_cap_rights_to_auth_def ptable_rights_def)+)[4]
  apply (case_tac "get_pd_of_thread (kheap s) (arch_state s) (cur_thread s) =
                   arm_global_pd (arch_state s)")
   apply (frule requiv_pd_of_thread_global_pd)
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
  apply (case_tac "get_pd_of_thread (kheap s') (arch_state s') (cur_thread s') =
                   arm_global_pd (arch_state s')")
   apply (drule reads_equiv_sym)
   apply (frule requiv_pd_of_thread_global_pd)
       apply ((fastforce simp: reads_equiv_def)+)[5]
  apply (simp add: ptable_lift_def)
  apply (frule requiv_get_pd_of_thread_eq, simp+)[1]
  apply (frule pd_of_thread_same_agent, simp+)[1]
  apply (subst requiv_get_page_info_eq, simp+)[1]
  done

lemma requiv_ptable_xn_eq:
  "\<lbrakk> reads_equiv aag s s'; pas_refined aag s; pas_refined aag s';
     is_subject aag (cur_thread s); invs s; invs s'; ptable_rights_s s x \<noteq> {} \<rbrakk>
     \<Longrightarrow> ptable_xn_s s x = ptable_xn_s s' x"
  by (simp add: ptable_xn_s_def requiv_ptable_attrs_eq)

lemma mask_shift_le:
  "z \<le> y \<Longrightarrow> (x :: 'a :: len word) && ~~ mask z >> y = x >> y"
proof -
  assume le: "z \<le> y"
  have shifttwice: "\<And>(x :: 'a :: len word). x >> y = x >> z >> y - z"
    by (simp add: shiftr_shiftr le)
  show ?thesis
    apply (subst shifttwice)
    apply simp
    apply (simp add: shiftr_shiftr le)
    done
qed

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

lemma ptrFromPAddr_mask_simp:
  "ptrFromPAddr z && ~~ mask (pageBitsForSize l) =
   ptrFromPAddr (z && ~~ mask (pageBitsForSize l))"
  apply (simp add: ptrFromPAddr_def field_simps)
  apply (subst mask_out_add_aligned[OF is_aligned_pptrBaseOffset])
  apply simp
  done

lemma pageBitsForSize_le_t24:
  "pageBitsForSize sz \<le> 24"
  by (cases sz, simp_all)

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
    by (clarsimp simp: pageBitsForSize_def split: vmpage_size.splits)
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
     apply (drule is_aligned_ptrFromPAddrD[OF _ pageBitsForSize_le_t24])
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
    apply (drule is_aligned_ptrFromPAddrD[OF _ pageBitsForSize_le_t24])
    apply (subst mask_lower_twice[symmetric])
     apply (erule less_imp_le_nat)
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

lemma valid_pdpt_align_ptD:
  "\<lbrakk> kheap s ptr = Some (ArchObj (PageTable pt)); valid_pdpt_objs s; pt a = entry \<rbrakk>
     \<Longrightarrow> is_aligned a (pte_range_sz entry)"
  apply (drule (1) valid_pdpt_objs_ptD)
  apply (clarsimp simp: entries_align_def)
  done

lemma valid_pdpt_align_pdD:
  "\<lbrakk> kheap s ptr = Some (ArchObj (PageDirectory pd));valid_pdpt_objs s; pd a = entry \<rbrakk>
     \<Longrightarrow> is_aligned a (pde_range_sz entry)"
  apply (drule (1) valid_pdpt_objs_pdD)
  apply (clarsimp simp: entries_align_def)
  done

lemma valid_vspace_objsD2:
  "\<lbrakk> (\<exists>\<rhd> p) s; ko_at (ArchObj ao) p s; valid_vspace_objs s \<rbrakk>
     \<Longrightarrow> valid_vspace_obj ao s"
  by (clarsimp simp: valid_vspace_objsD)

lemma ptable_lift_data_consistant:
  assumes vs: "valid_state s"
  and vpdpt: "valid_pdpt_objs s"
  and pt_lift: "ptable_lift t s x = Some ptr"
  and dat: "data_at sz ((ptrFromPAddr ptr) && ~~ mask (pageBitsForSize sz)) s"
  and misc: "get_pd_of_thread (kheap s) (arch_state s) t \<noteq> arm_global_pd (arch_state s)"
            "x \<notin> kernel_mappings"
  shows "ptable_lift t s (x && ~~ mask (pageBitsForSize sz)) =
         Some (ptr && ~~ mask (pageBitsForSize sz))"
proof -
  have aligned_stuff:
    "is_aligned (ucast ((x >> 12) && mask 8) :: word8) 4 \<Longrightarrow> (x && ~~ mask 16 >> 12) = x >> 12"
    by (simp add: is_aligned_mask mask_def) word_bitwise
  have aligned_stuff':
    "is_aligned ((ucast (x >> 20)):: 12 word) 4 \<Longrightarrow> x && ~~ mask 24 >> 20 = x >> 20"
    by (simp add: is_aligned_mask mask_def) word_bitwise
  have vs': "valid_objs s \<and> valid_vspace_objs s \<and> pspace_distinct s \<and> pspace_aligned s"
    using vs by (simp add: valid_state_def valid_pspace_def)
  have x_less_kb: "x < kernel_base"
    using misc by (simp add: kernel_mappings_def) (* FIXME: any rules exists already ? *)
  thus ?thesis
    using pt_lift dat vs'
    apply (clarsimp simp: ptable_rights_def ptable_lift_def split: option.splits)
    apply (clarsimp simp: get_page_info_def split: option.splits)
    apply (rename_tac base sz' attrs rights pde)
    apply (case_tac pde,simp_all)
      apply (clarsimp simp: get_pd_entry_def split: arch_kernel_obj.split_asm option.splits)
      apply (clarsimp simp: get_pt_info_def get_arch_obj_def get_pt_entry_def
                     split: option.splits arch_kernel_obj.split_asm kernel_object.splits)
      apply (rename_tac pd_base vmattr mw pd pt)
      apply (cut_tac get_pd_of_thread_reachable[OF misc(1)])
      apply (frule(1) valid_vspace_objsD2[rotated,unfolded obj_at_def,simplified],simp)
      apply simp
      apply (drule bspec)
       apply (rule Compl_iff[THEN iffD2])
       apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
      apply (clarsimp simp: valid_pde_def obj_at_def a_type_def)
      apply (case_tac "pt (ucast ((x >> 12) && mask 8))",simp_all)
       apply (frule valid_vspace_objsD2[where p = "ptrFromPAddr p" for p,
                                        rotated,unfolded obj_at_def,simplified], simp)
        apply (rule exI)
        apply (erule vs_lookup_step)
        apply (simp add: vs_lookup1_def lookup_pd_slot_def Let_def
                         pd_shifting pd_shifting_dual obj_at_def)
        apply (rule_tac x="VSRef (x>>20) (Some APageDirectory)" in exI)
        apply (rule context_conjI,simp)
        apply (erule vs_refs_pdI)
         apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
        apply (intro allI impI)
        apply (simp add: nth_shiftr)
        apply (rule bang_big[simplified])
        apply (simp add: word_size)
       apply (frule (1) valid_pdpt_align_ptD[OF _ vpdpt])
       apply simp
       apply (drule_tac x="(ucast ((x >> 12) && mask 8))" in spec)
       apply (frule data_at_same_size[where sz=sz and sz'=ARMLargePage,rotated,simplified], simp+)
       apply (clarsimp simp: mask_shift_le get_pt_info_def get_pt_entry_def
                             get_arch_obj_def entries_align_def aligned_stuff mask_AND_NOT_mask
                      dest!: data_at_aligned is_aligned_ptrFromPAddrD[where a = 16,simplified])
       apply (simp add: neg_mask_add_aligned[OF _ and_mask_less'] is_aligned_neg_mask_eq)
      apply (frule valid_vspace_objsD2[where p = "ptrFromPAddr p" for p,
                                       rotated,unfolded obj_at_def,simplified], simp)
       apply (rule exI)
       apply (erule vs_lookup_step)
       apply (simp add: vs_lookup1_def lookup_pd_slot_def Let_def
                        pd_shifting pd_shifting_dual obj_at_def)
       apply (rule_tac x="VSRef (x>>20) (Some APageDirectory)" in exI)
       apply (rule context_conjI,simp)
       apply (erule vs_refs_pdI)
        apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
       apply (intro allI impI)
       apply (simp add: nth_shiftr)
       apply (rule bang_big[simplified])
       apply (simp add: word_size)
      apply (frule(1) valid_pdpt_align_ptD[OF _ vpdpt])
      apply simp
      apply (drule_tac x="(ucast ((x >> 12) && mask 8))" in spec)
      apply (frule data_at_same_size[where sz=sz and sz'=ARMSmallPage,rotated,simplified], simp+)
      apply (clarsimp simp: mask_shift_le get_pt_info_def get_pt_entry_def get_arch_obj_def
                            neg_mask_add_aligned[OF _ and_mask_less'] mask_AND_NOT_mask
                     dest!: data_at_aligned is_aligned_ptrFromPAddrD[where a = 12,simplified])
     apply (clarsimp simp: get_pd_entry_def get_arch_obj_def
                    split: arch_kernel_obj.split_asm option.splits)
     apply (clarsimp simp: get_pt_entry_def
                    split: option.splits arch_kernel_obj.split_asm kernel_object.splits)
     apply (rename_tac pd_base vmattr mw pd caprights)
     apply (cut_tac get_pd_of_thread_reachable[OF misc(1)])
     apply (frule(1) valid_vspace_objsD2[rotated,unfolded obj_at_def,simplified],simp)
     apply simp
     apply (drule bspec)
      apply (rule Compl_iff[THEN iffD2])
      apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
     apply (clarsimp simp: valid_pde_def obj_at_def)
     apply (frule(1) valid_pdpt_align_pdD[OF _ vpdpt])
     apply (frule data_at_same_size[where sz=sz and sz'=ARMSection,rotated,simplified], simp+)
    apply (clarsimp simp: aligned_stuff' neg_mask_add_aligned[OF _ and_mask_less'] mask_AND_NOT_mask
                   dest!: data_at_aligned is_aligned_ptrFromPAddrD[where a = 20,simplified])
    apply (clarsimp simp: get_pd_entry_def get_arch_obj_def
                   split: arch_kernel_obj.split_asm option.splits)
    apply (clarsimp simp: get_pt_entry_def
                   split: option.splits arch_kernel_obj.split_asm kernel_object.splits)
    apply (rename_tac pd_base vmattr rights pd)
    apply (cut_tac get_pd_of_thread_reachable[OF misc(1)])
    apply (frule(1) valid_vspace_objsD2[rotated,unfolded obj_at_def,simplified],simp)
    apply simp
    apply (drule bspec)
     apply (rule Compl_iff[THEN iffD2])
     apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
    apply (clarsimp simp: valid_pde_def obj_at_def)
    apply (frule(1) valid_pdpt_align_pdD[OF _ vpdpt])
    apply (frule data_at_same_size[where sz=sz and sz'=ARMSuperSection,rotated,simplified], simp+)
    apply (clarsimp simp: aligned_stuff' neg_mask_add_aligned[OF _ and_mask_less'] mask_AND_NOT_mask
                   dest!: data_at_aligned is_aligned_ptrFromPAddrD[where a = 24,simplified])
    done
qed

lemma ptable_rights_data_consistant:
  assumes vs: "valid_state s"
  and vpdpt: "valid_pdpt_objs s"
  and pt_lift: "ptable_lift t s x = Some ptr"
  and dat: "data_at sz ((ptrFromPAddr ptr) && ~~ mask (pageBitsForSize sz)) s"
  and misc: "get_pd_of_thread (kheap s) (arch_state s) t \<noteq>
             arm_global_pd (arch_state s)" "x \<notin> kernel_mappings"
  shows "ptable_rights t s (x && ~~ mask (pageBitsForSize sz)) = ptable_rights t s x"
proof -
  have aligned_stuff:
    "is_aligned (ucast ((x >> 12) && mask 8) :: word8) 4 \<Longrightarrow> (x && ~~ mask 16 >> 12) = x >> 12"
    by (simp add: is_aligned_mask mask_def) word_bitwise
  have aligned_stuff':
    "is_aligned ((ucast (x >> 20)):: 12 word) 4 \<Longrightarrow> x && ~~ mask 24 >> 20 = x >> 20"
    by (simp add: is_aligned_mask mask_def) word_bitwise
  have vs': "valid_objs s \<and> valid_vspace_objs s \<and> pspace_distinct s \<and> pspace_aligned s"
    using vs
    by (simp add: valid_state_def valid_pspace_def)
  have x_less_kb: "x < kernel_base"
    using misc
    by (simp add: kernel_mappings_def) (* FIXME: any rules exists already ? *)
  thus ?thesis
    using pt_lift dat vs'
    apply (clarsimp simp: ptable_rights_def ptable_lift_def split: option.splits)
    apply (clarsimp simp: get_page_info_def split: option.splits)
    apply (rename_tac base sz' attrs rights pde)
    apply (case_tac pde, simp_all)
      apply (clarsimp simp: get_pd_entry_def split: arch_kernel_obj.split_asm option.splits)
      apply (clarsimp simp: get_pt_info_def get_arch_obj_def get_pt_entry_def
                     split: option.splits arch_kernel_obj.split_asm kernel_object.splits)
      apply (rename_tac pd_base vmattr mw pd pt)
      apply (cut_tac get_pd_of_thread_reachable[OF misc(1)])
      apply (frule (1) valid_vspace_objsD2[rotated,unfolded obj_at_def,simplified],simp)
      apply simp
      apply (drule bspec)
       apply (rule Compl_iff[THEN iffD2])
       apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
      apply (clarsimp simp: valid_pde_def obj_at_def a_type_def)
      apply (case_tac "pt (ucast ((x >> 12) && mask 8))",simp_all)
       apply (frule valid_vspace_objsD2[where p = "ptrFromPAddr p" for p,
                                        rotated,unfolded obj_at_def,simplified], simp)
        apply (rule exI)
        apply (erule vs_lookup_step)
        apply (simp add: vs_lookup1_def lookup_pd_slot_def Let_def
                         pd_shifting pd_shifting_dual obj_at_def)
        apply (rule_tac x = "VSRef (x>>20) (Some APageDirectory)" in exI)
        apply (rule context_conjI,simp)
        apply (erule vs_refs_pdI)
         apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
        apply (intro allI impI)
        apply (simp add: nth_shiftr)
        apply (rule bang_big[simplified])
        apply (simp add: word_size)
       apply (frule (1) valid_pdpt_align_ptD[OF _ vpdpt])
       apply simp
       apply (drule_tac x="(ucast ((x >> 12) && mask 8))" in spec)
       apply (frule data_at_same_size[where sz=sz and sz'=ARMLargePage,rotated,simplified], simp+)
       apply (clarsimp simp: mask_shift_le get_pt_info_def get_pt_entry_def
                             get_arch_obj_def entries_align_def aligned_stuff mask_AND_NOT_mask
                      dest!: data_at_aligned is_aligned_ptrFromPAddrD[where a=16,simplified])
      apply (frule valid_vspace_objsD2[where p = "ptrFromPAddr p" for p,
                                       rotated,unfolded obj_at_def,simplified], simp)
       apply (rule exI)
       apply (erule vs_lookup_step)
       apply (simp add: vs_lookup1_def lookup_pd_slot_def Let_def
                        pd_shifting pd_shifting_dual obj_at_def)
       apply (rule_tac x = "VSRef (x>>20) (Some APageDirectory)" in exI)
       apply (rule context_conjI,simp)
       apply (erule vs_refs_pdI)
        apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
       apply (intro allI impI)
       apply (simp add: nth_shiftr)
       apply (rule bang_big[simplified])
       apply (simp add: word_size)
      apply (frule(1) valid_pdpt_align_ptD[OF _ vpdpt])
      apply simp
      apply (drule_tac x="(ucast ((x >> 12) && mask 8))" in spec)
      apply (frule data_at_same_size[where sz=sz and sz'=ARMSmallPage,rotated,simplified], simp+)
      apply (clarsimp simp: mask_shift_le get_pt_info_def get_pt_entry_def get_arch_obj_def
                     dest!: data_at_aligned is_aligned_ptrFromPAddrD[where a=12,simplified])
     apply (clarsimp simp: get_pd_entry_def get_arch_obj_def
                    split: arch_kernel_obj.split_asm option.splits)
     apply (clarsimp simp: get_pt_entry_def
                    split: option.splits arch_kernel_obj.split_asm kernel_object.splits)
     apply (rename_tac pd_base vmattr mw pd caprights)
     apply (cut_tac get_pd_of_thread_reachable[OF misc(1)])
     apply (frule(1) valid_vspace_objsD2[rotated,unfolded obj_at_def,simplified],simp)
     apply simp
     apply (drule bspec)
      apply (rule Compl_iff[THEN iffD2])
      apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
     apply (clarsimp simp: valid_pde_def obj_at_def)
     apply (frule(1) valid_pdpt_align_pdD[OF _ vpdpt])
     apply (frule data_at_same_size[where sz = sz and sz' = ARMSection,rotated,simplified],
          clarsimp+)
    apply (clarsimp simp: get_pd_entry_def get_arch_obj_def
                   split: arch_kernel_obj.split_asm option.splits)
    apply (clarsimp simp: get_pt_entry_def
                   split: option.splits arch_kernel_obj.split_asm kernel_object.splits)
    apply (rename_tac pd_base vmattr rights pd)
    apply (cut_tac get_pd_of_thread_reachable[OF misc(1)])
    apply (frule (1) valid_vspace_objsD2[rotated,unfolded obj_at_def,simplified],simp)
    apply simp
    apply (drule bspec)
     apply (rule Compl_iff[THEN iffD2])
     apply (rule kernel_mappings_kernel_mapping_slots[OF misc(2)])
    apply (clarsimp simp: valid_pde_def obj_at_def)
    apply (frule(1) valid_pdpt_align_pdD[OF _ vpdpt])
    apply (frule data_at_same_size[where sz=sz and sz'=ARMSuperSection,rotated,simplified], simp+)
    apply (clarsimp simp: aligned_stuff' neg_mask_add_aligned[OF _ and_mask_less'] mask_AND_NOT_mask
                   dest!: data_at_aligned is_aligned_ptrFromPAddrD[where a = 24,simplified])
    done
qed

lemma user_op_access_data_at:
  "\<lbrakk> invs s; valid_pdpt_objs s;pas_refined aag s; is_subject aag tcb; ptable_lift tcb s x = Some ptr;
     data_at sz ((ptrFromPAddr ptr) && ~~ mask (pageBitsForSize sz)) s;
     auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x) \<rbrakk>
     \<Longrightarrow> (pasObjectAbs aag tcb, auth,
          pasObjectAbs aag (ptrFromPAddr (ptr && ~~ mask (pageBitsForSize sz)))) \<in> pasPolicy aag"
  apply (case_tac "x \<in> kernel_mappings")
   apply (clarsimp simp: ptable_lift_def ptable_rights_def split: option.splits)
   apply (frule some_get_page_info_kmapsD)
      apply (fastforce simp: invs_valid_global_pd_mappings invs_equal_kernel_mappings
                             vspace_cap_rights_to_auth_def)+
  apply (case_tac "get_pd_of_thread (kheap s) (arch_state s) tcb = arm_global_pd (arch_state s)")
   apply (clarsimp simp: ptable_lift_def ptable_rights_def split: option.splits)
   apply (frule get_page_info_gpd_kmaps[rotated, rotated])
     apply (fastforce simp: invs_valid_global_objs invs_arch_state)+
  apply (frule (3) ptable_lift_data_consistant[rotated 2])
    apply fastforce
   apply fastforce
  apply (frule (3) ptable_rights_data_consistant[rotated 2])
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
  "\<lbrakk> reads_equiv aag s s'; globals_equiv s s'; invs s; invs s'; valid_pdpt_objs s;
     valid_pdpt_objs s'; is_subject aag (cur_thread s); AllowRead \<in> ptable_rights_s s x;
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
  "\<lbrakk> reads_equiv aag s s'; globals_equiv s s'; invs s; invs s'; valid_pdpt_objs s;
     valid_pdpt_objs s'; is_subject aag (cur_thread s); AllowRead \<in> ptable_rights_s s x;
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
  "\<lbrakk> reads_equiv aag s s'; globals_equiv s s'; invs s; invs s'; valid_pdpt_objs s;
     valid_pdpt_objs s'; is_subject aag (cur_thread s); AllowRead \<in> ptable_rights_s s x;
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
  "context_matches_state pl pr pxn ms s \<equiv> case ms of (um, ds, es) \<Rightarrow>
     pl = ptable_lift_s s |` {x. pr x \<noteq> {}} \<and>
     pr = ptable_rights_s s \<and>
     pxn = (\<lambda>x. pr x \<noteq> {} \<and> ptable_xn_s s x) \<and>
     um = (user_mem s \<circ> ptrFromPAddr) |` {y. \<exists>x. pl x = Some y \<and> AllowRead \<in> pr x} \<and>
     ds = (device_state (machine_state s) \<circ> ptrFromPAddr) |`
          {y. \<exists>x. pl x = Some y \<and> AllowRead \<in> pr x} \<and>
     es = exclusive_state (machine_state s)"


lemma dmo_setExMonitor_reads_respects_g:
  "reads_respects_g aag l \<top> (do_machine_op (setExMonitor es))"
  apply (simp add: setExMonitor_def)
  apply (wp dmo_ev ev_modify)
  apply (auto simp: reads_equiv_g_def reads_equiv_def affects_equiv_def states_equiv_for_def
                    equiv_for_def equiv_asids_def equiv_asid_def globals_equiv_def idle_equiv_def
             split: if_splits)
  done

lemma dmo_getExMonitor_reads_respects_g:
  "reads_respects_g aag l (\<lambda>s. cur_thread s \<noteq> idle_thread s) (do_machine_op getExMonitor)"
  apply (simp add: getExMonitor_def)
  apply (wp dmo_ev gets_ev'')
  apply (clarsimp simp: reads_equiv_g_def globals_equiv_def)
  done

lemma getExMonitor_wp[wp]:
  "\<lbrace>\<lambda>ms. P (exclusive_state ms) ms\<rbrace> getExMonitor \<lbrace>P\<rbrace>"
  by (simp add: getExMonitor_def | wp)+


definition valid_vspace_objs_if where
  "valid_vspace_objs_if \<equiv> valid_pdpt_objs"

declare valid_vspace_objs_if_def[simp]


lemma do_user_op_reads_respects_g:
  notes split_paired_All[simp del]
  shows
    "(\<forall>pl pr pxn tc ms s. P tc s \<and> context_matches_state pl pr pxn ms s
                                \<longrightarrow> (\<exists>x. uop (cur_thread s) pl pr pxn (tc, ms) = {x}))
     \<Longrightarrow> reads_respects_g aag l (pas_refined aag and invs and valid_vspace_objs_if
                                                 and is_subject aag \<circ> cur_thread
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
                     dmo_setExMonitor_reads_respects_g dmo_device_state_update_reads_respects_g
                     select_ev dmo_getExMonitor_reads_respects_g dmo_wp)
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

end

context begin interpretation Arch .

requalify_consts
  do_user_op_if
  valid_vspace_objs_if
  context_matches_state

requalify_facts
  do_user_op_reads_respects_g

end

end
