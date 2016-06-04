(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchUntyped_AI
imports "../Untyped_AI"
begin

context Arch begin global_naming ARM

named_theorems Untyped_AI_assms

lemma of_bl_nat_to_cref[Untyped_AI_assms]:
    "\<lbrakk> x < 2 ^ bits; bits < 32 \<rbrakk>
      \<Longrightarrow> (of_bl (nat_to_cref bits x) :: word32) = of_nat x"
  apply (clarsimp intro!: less_mask_eq
                  simp: nat_to_cref_def of_drop_to_bl
                        word_size word_less_nat_alt word_bits_def)
  apply (subst unat_of_nat)
  apply (erule order_le_less_trans [OF mod_less_eq_dividend])
  done


lemma cnode_cap_ex_cte[Untyped_AI_assms]:
  "\<lbrakk> is_cnode_cap cap; cte_wp_at (\<lambda>c. \<exists>m. cap = mask_cap m c) p s;
     (s::'state_ext::state_ext state) \<turnstile> cap; valid_objs s; pspace_aligned s \<rbrakk> \<Longrightarrow>
    ex_cte_cap_wp_to is_cnode_cap (obj_ref_of cap, nat_to_cref (bits_of cap) x) s"
  apply (simp only: ex_cte_cap_wp_to_def)
  apply (rule exI, erule cte_wp_at_weakenE)
  apply (clarsimp simp: is_cap_simps bits_of_def)
  apply (case_tac c, simp_all add: mask_cap_def cap_rights_update_def)
  apply (clarsimp simp: nat_to_cref_def word_bits_def)
  apply (erule(2) valid_CNodeCapE)
  apply (simp add: word_bits_def cte_level_bits_def)
  done



lemma inj_on_nat_to_cref[Untyped_AI_assms]:
  "bits < 32 \<Longrightarrow> inj_on (nat_to_cref bits) {..< 2 ^ bits}"
  apply (rule inj_onI)
  apply (drule arg_cong[where f="\<lambda>x. replicate (32 - bits) False @ x"]) 
  apply (subst(asm) word_bl.Abs_inject[where 'a=32, symmetric])
    apply (simp add: nat_to_cref_def word_bits_def)
   apply (simp add: nat_to_cref_def word_bits_def)
  apply (simp add: of_bl_rep_False of_bl_nat_to_cref)
  apply (erule word_unat.Abs_eqD)
   apply (simp only: unats_def mem_simps)
   apply (erule order_less_le_trans)
   apply (rule power_increasing, simp+)
  apply (simp only: unats_def mem_simps)
  apply (erule order_less_le_trans)
  apply (rule power_increasing, simp+)
  done

  
lemma data_to_obj_type_sp[Untyped_AI_assms]:
  "\<lbrace>P\<rbrace> data_to_obj_type x \<lbrace>\<lambda>ts (s::'state_ext::state_ext state). ts \<noteq> ArchObject ASIDPoolObj \<and> P s\<rbrace>, -"
  unfolding data_to_obj_type_def
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply clarsimp
  apply (simp add: arch_data_to_obj_type_def split: split_if_asm)
  done

lemma dui_inv_wf[wp, Untyped_AI_assms]:
  "\<lbrace>invs and cte_wp_at (op = (cap.UntypedCap w sz idx)) slot 
     and (\<lambda>(s::'state_ext::state_ext state). \<forall>cap \<in> set cs. is_cnode_cap cap 
                      \<longrightarrow> (\<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s))
    and (\<lambda>s. \<forall>x \<in> set cs. s \<turnstile> x)\<rbrace>
     decode_untyped_invocation label args slot (cap.UntypedCap w sz idx) cs
   \<lbrace>valid_untyped_inv\<rbrace>,-"
proof -
  have inj: "\<And>node_cap s. \<lbrakk>is_cnode_cap node_cap; 
    unat (args ! 5) \<le> 2 ^ bits_of node_cap - unat (args ! 4);valid_cap node_cap s\<rbrakk> \<Longrightarrow>
    inj_on (Pair (obj_ref_of node_cap) \<circ> nat_to_cref (bits_of node_cap))
                      {unat (args ! 4)..<unat (args ! 4) + unat (args ! 5)}"
    apply (simp add:comp_def)
    apply (rule inj_on_split)
    apply (rule subset_inj_on [OF inj_on_nat_to_cref])
     apply (clarsimp simp: is_cap_simps bits_of_def valid_cap_def 
       word_bits_def cap_aligned_def)
     apply clarsimp
     apply (rule less_le_trans)
      apply assumption
     apply (simp add:le_diff_conv2)
    done
  have nasty_strengthen:
    "\<And>S a f s. (\<forall>x\<in>S. cte_wp_at (op = cap.NullCap) (a, f x) s)
    \<Longrightarrow> cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) slot s
    \<longrightarrow> slot \<notin> (Pair a \<circ> f) ` S"
    by (auto simp:cte_wp_at_caps_of_state)
  show ?thesis
  apply (simp add: decode_untyped_invocation_def unlessE_def[symmetric]
                   unlessE_whenE
           split del: split_if)
  apply (rule validE_R_sp[OF whenE_throwError_sp]
              validE_R_sp[OF data_to_obj_type_sp]
              validE_R_sp[OF dui_sp_helper] validE_R_sp[OF map_ensure_empty])+
  apply clarsimp
  apply (rule hoare_pre)
  apply (wp whenE_throwError_wp[THEN validE_validE_R] check_free_index_wp
            map_ensure_empty_wp)
  apply (clarsimp simp: distinct_map cases_imp_eq)
  apply (subgoal_tac "s \<turnstile> node_cap")
   prefer 2
   apply (erule disjE)
    apply (drule bspec [where x = "cs ! 0"],clarsimp)+
    apply fastforce
   apply clarsimp
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (drule(1) caps_of_state_valid[rotated])+
   apply (clarsimp simp:is_cap_simps diminished_def mask_cap_def 
     cap_rights_update_def ,simp split:cap.splits)
  apply (subgoal_tac "\<forall>r\<in>cte_refs node_cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s")
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (frule(1) caps_of_state_valid[rotated])
   apply (clarsimp simp:not_less)
   apply (frule(2) inj)
   apply (clarsimp simp:comp_def)
   apply (frule(1) caps_of_state_valid)
   apply (simp add: nasty_strengthen[unfolded o_def] cte_wp_at_caps_of_state)
   apply (intro conjI)
    apply (intro impI)
    apply (frule range_cover_stuff[where rv = 0 and sz = sz])
     apply ((fastforce dest!:valid_cap_aligned simp:cap_aligned_def)+)[4]
    apply (clarsimp simp:valid_cap_simps cap_aligned_def)
    apply (frule alignUp_idem[OF is_aligned_weaken,where a = w])
      apply (erule range_cover.sz)
     apply (simp add:range_cover_def)
    apply (clarsimp simp:get_free_ref_def is_aligned_neg_mask_eq empty_descendants_range_in)
    apply (drule_tac x = "(obj_ref_of node_cap,nat_to_cref (bits_of node_cap) slota)" in bspec)
     apply (clarsimp simp:is_cap_simps nat_to_cref_def word_bits_def
       bits_of_def valid_cap_simps cap_aligned_def)+
   apply (frule(1) range_cover_stuff[where sz = sz])
     apply (clarsimp dest!:valid_cap_aligned simp:cap_aligned_def word_bits_def)+
    apply simp+
   apply (clarsimp simp:get_free_ref_def)
   apply (frule cte_wp_at_caps_descendants_range_inI
     [where ptr = w and sz = sz and idx = 0 and cref = slot])
       subgoal by (clarsimp simp:cte_wp_at_caps_of_state is_aligned_neg_mask_eq)
      subgoal by simp
     subgoal by (simp add:range_cover_def word_bits_def)
    subgoal by (simp add:is_aligned_neg_mask_eq)
   apply (clarsimp)
   apply (erule disjE)
    apply (drule_tac x= "cs!0" in bspec)
     subgoal by clarsimp
    subgoal by simp
   apply (clarsimp simp:cte_wp_at_caps_of_state ex_cte_cap_wp_to_def)
   apply (rule_tac x=aa in exI,rule exI,rule exI)
   apply (rule conjI, assumption)
    by (clarsimp simp:diminished_def is_cap_simps mask_cap_def
      cap_rights_update_def , simp split:cap.splits )
qed

lemma asid_bits_ge_0: 
  "(0::word32) < 2 ^ asid_bits" by (simp add: asid_bits_def)

lemma retype_ret_valid_caps_captable[Untyped_AI_assms]:
  "\<lbrakk>pspace_no_overlap ptr sz (s::'state_ext::state_ext state) \<and> 0 < us \<and> range_cover ptr sz (obj_bits_api CapTableObject us) n \<and> ptr \<noteq> 0
       \<rbrakk>
         \<Longrightarrow> \<forall>y\<in>{0..<n}. s
                \<lparr>kheap := foldr (\<lambda>p kh. kh(p \<mapsto> default_object CapTableObject us)) (map (\<lambda>p. ptr_add ptr (p * 2 ^ obj_bits_api CapTableObject us)) [0..<n])
                           (kheap s)\<rparr> \<turnstile> CNodeCap (ptr_add ptr (y * 2 ^ obj_bits_api CapTableObject us)) us []"
by ((clarsimp simp:valid_cap_def default_object_def cap_aligned_def 
        cte_level_bits_def slot_bits_def is_obj_defs well_formed_cnode_n_def empty_cnode_def
        dom_def arch_default_cap_def ptr_add_def | rule conjI | intro conjI obj_at_foldr_intro imageI
      | rule is_aligned_add_multI[OF _ le_refl],
        (simp add:range_cover_def word_bits_def obj_bits_api_def slot_bits_def)+)+)[1]

lemma retype_ret_valid_caps_aobj[Untyped_AI_assms]:
  "\<And>ptr sz (s::'state_ext::state_ext state) x6 us n. 
  \<lbrakk>pspace_no_overlap ptr sz s \<and> x6 \<noteq> ASIDPoolObj \<and> 
  range_cover ptr sz (obj_bits_api (ArchObject x6) us) n \<and> ptr \<noteq> 0\<rbrakk>
            \<Longrightarrow> \<forall>y\<in>{0..<n}. s
                   \<lparr>kheap := foldr (\<lambda>p kh. kh(p \<mapsto> default_object (ArchObject x6) us)) (map (\<lambda>p. ptr_add ptr (p * 2 ^ obj_bits_api (ArchObject x6) us)) [0..<n])
                              (kheap s)\<rparr> \<turnstile> ArchObjectCap (ARM_A.arch_default_cap x6 (ptr_add ptr (y * 2 ^ obj_bits_api (ArchObject x6) us)) us)"
  apply (rename_tac aobject_type us n)
  apply (case_tac aobject_type)
by (clarsimp simp:valid_cap_def default_object_def cap_aligned_def 
        cte_level_bits_def slot_bits_def is_obj_defs well_formed_cnode_n_def empty_cnode_def
        dom_def arch_default_cap_def ptr_add_def | intro conjI obj_at_foldr_intro
        imageI valid_vm_rights_def
      | rule is_aligned_add_multI[OF _ le_refl]
      | fastforce simp:range_cover_def obj_bits_api_def
        default_arch_object_def valid_vm_rights_def  word_bits_def a_type_def)+


lemma retype_region_ranges'_aobj[Untyped_AI_assms]: "\<And>x p aobj.
       \<lbrakk>range_cover ptr sz (arch_kobj_size (default_arch_object aobj us)) n; p < n;
        Some x =
        aobj_ref
         (arch_default_cap aobj
           (ptr + of_nat p * 2 ^ (arch_kobj_size (default_arch_object aobj us))) us)\<rbrakk>
       \<Longrightarrow> ptr + of_nat p * 2 ^ (arch_kobj_size (default_arch_object aobj us)) \<le> x \<and>
            x \<le> ptr + of_nat p * 2 ^ (arch_kobj_size (default_arch_object aobj us)) +
                 2 ^ (arch_kobj_size (default_arch_object aobj us)) -
                 1"
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type)
        apply (simp_all add: aobj_ref_def arch_default_cap_def p_assoc_help)
by ((rule is_aligned_no_wrap'[OF is_aligned_add_multI[OF _ le_refl refl]],
          (simp add:range_cover_def )+)[1])+

lemma retype_region_distinct_sets_aobj[Untyped_AI_assms]: "\<And>x y x6.
       \<lbrakk>range_cover ptr sz (obj_bits_api tp us) n; x \<in> set [0..<n]; y \<in> set [0..<n]; x \<noteq> y;
        of_nat y * 2 ^ obj_bits_api tp us \<noteq> of_nat x *  (2::word32) ^ obj_bits_api tp us; tp = ArchObject x6\<rbrakk>
       \<Longrightarrow> cap_range (default_cap tp (ptr_add ptr (x * 2 ^ obj_bits_api tp us)) us) \<inter>
            cap_range (default_cap tp (ptr_add ptr (y * 2 ^ obj_bits_api tp us)) us) =
            {}"
       apply (simp add:cap_range_def ptr_add_def)+
    apply (case_tac x6)
by (simp add:ptr_add_def aobj_ref_def arch_default_cap_def neq_commute)+


lemma copy_global_mappings_hoare_lift:(*FIXME: arch_split  \<rightarrow> these do not seem to be used globally *)
  assumes wp: "\<And>ptr val. \<lbrace>Q\<rbrace> store_pde ptr val \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows       "\<lbrace>Q\<rbrace> copy_global_mappings pd \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply (wp mapM_x_wp' wp)
  done

declare [[show_types=true]]
lemma init_arch_objects_hoare_lift:
  assumes wp: "\<And>oper. \<lbrace>(P::'state_ext::state_ext state\<Rightarrow>bool)\<rbrace> do_machine_op oper \<lbrace>\<lambda>rv :: unit. Q\<rbrace>"
              "\<And>ptr val. \<lbrace>P\<rbrace> store_pde ptr val \<lbrace>\<lambda>rv. P\<rbrace>"
  shows       "\<lbrace>P and Q\<rbrace> init_arch_objects tp ptr sz us adds \<lbrace>\<lambda>rv. Q\<rbrace>"
proof -
  have pres: "\<And>oper. \<lbrace>P and Q\<rbrace> do_machine_op oper \<lbrace>\<lambda>rv :: unit. Q\<rbrace>"
             "\<lbrace>P and Q\<rbrace> return () \<lbrace>\<lambda>rv. Q\<rbrace>"
    by (wp wp | simp)+
  show ?thesis
    apply (simp add: init_arch_objects_def create_word_objects_def
                  pres reserve_region_def
           split: Structures_A.apiobject_type.split
                  aobject_type.split)
    apply clarsimp
    apply (rule hoare_pre)
     apply (wp mapM_x_wp' copy_global_mappings_hoare_lift wp)
    apply simp
    done
qed

lemma cap_refs_in_kernel_windowD2:
  "\<lbrakk> cte_wp_at P p (s::'state_ext::state_ext state); cap_refs_in_kernel_window s \<rbrakk>
       \<Longrightarrow> \<exists>cap. P cap \<and> region_in_kernel_window (cap_range cap) s"
  apply (clarsimp simp: cte_wp_at_caps_of_state region_in_kernel_window_def)
  apply (drule(1) cap_refs_in_kernel_windowD)
  apply fastforce
  done

lemma init_arch_objects_descendants_range[wp,Untyped_AI_assms]:
  "\<lbrace>\<lambda>(s::'state_ext::state_ext state). descendants_range x cref s \<rbrace> init_arch_objects ty ptr n us y
          \<lbrace>\<lambda>rv s. descendants_range x cref s\<rbrace>"
  apply (simp add:descendants_range_def)
  apply (rule hoare_pre)
   apply (wp retype_region_mdb init_arch_objects_hoare_lift)
    apply (wps do_machine_op_mdb)
    apply (wp hoare_vcg_ball_lift)
   apply (rule hoare_pre)
    apply (wps store_pde_mdb_inv)
    apply wp
   apply simp
  apply fastforce
  done

lemma init_arch_objects_caps_overlap_reserved[wp,Untyped_AI_assms]:
  "\<lbrace>\<lambda>(s::'state_ext::state_ext state). caps_overlap_reserved S s\<rbrace>
   init_arch_objects ty ptr n us y
   \<lbrace>\<lambda>rv s. caps_overlap_reserved S s\<rbrace>"
  apply (simp add:caps_overlap_reserved_def)
  apply (rule hoare_pre)
   apply (wp retype_region_mdb init_arch_objects_hoare_lift)
  apply fastforce
  done

lemma retype_region_descendants_range_ret_aobj[Untyped_AI_assms]:
  "\<And>(s::'state_ext::state_ext state) p a b cap aobject_type.
       \<lbrakk>pspace_no_overlap ptr sz s; valid_pspace s;
        range_cover ptr sz (obj_bits_api ty us) n; p < n;
        (a, b) \<in> descendants_of cref (cdt s);
        caps_of_state s (a, b) = Some cap;
        ptr + of_nat p * 2 ^ obj_bits_api ty us
        \<le> ptr + of_nat p * 2 ^ obj_bits_api ty us +
           2 ^ obj_bits_api ty us - 1;
        ty = ArchObject aobject_type\<rbrakk>
       \<Longrightarrow> cap_range (default_cap ty (ptr_add ptr (p * 2 ^ obj_bits_api ty us)) us)
           \<subseteq> {ptr + of_nat p * 2 ^ obj_bits_api ty us..ptr
                  + of_nat p * 2 ^ obj_bits_api ty us
                  + 2 ^ obj_bits_api ty us - 1}"
apply (simp add:cap_range_def ptr_add_def obj_bits_api_def)
by (case_tac aobject_type,
    simp_all add:cap_range_def aobj_ref_def arch_default_cap_def default_arch_object_def)

lemma set_untyped_cap_invs_simple[Untyped_AI_assms]:
  "\<lbrace>\<lambda>s. descendants_range_in {ptr .. ptr+2^sz - 1} cref s \<and> pspace_no_overlap ptr sz s \<and> invs s 
  \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz \<and> obj_ref_of c = ptr) cref s \<and> idx \<le> 2^ sz\<rbrace>
  set_cap (cap.UntypedCap ptr sz idx) cref
 \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:cte_wp_at_caps_of_state invs_def valid_state_def)
  apply (rule hoare_pre)
  apply (wp set_free_index_valid_pspace_simple set_cap_valid_mdb_simple
    set_cap_idle update_cap_ifunsafe)
  apply (simp add:valid_irq_node_def)
  apply wps
  apply (wp hoare_vcg_all_lift set_cap_irq_handlers set_cap_arch_objs set_cap_valid_arch_caps
    set_cap.valid_global_objs set_cap_irq_handlers cap_table_at_lift_valid set_cap_typ_at )
  apply (clarsimp simp:cte_wp_at_caps_of_state is_cap_simps)
  apply (intro conjI,clarsimp)
        apply (rule ext,clarsimp simp:is_cap_simps)
       apply (clarsimp split:cap.splits simp:is_cap_simps appropriate_cte_cap_def)
      apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
       apply clarsimp
      apply (clarsimp simp:is_cap_simps ex_cte_cap_wp_to_def appropriate_cte_cap_def cte_wp_at_caps_of_state)
     apply (clarsimp dest!:valid_global_refsD2 simp:cap_range_def)
    apply (simp add:valid_irq_node_def)
   apply (clarsimp simp:valid_irq_node_def)
  apply (clarsimp simp:no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state vs_cap_ref_def)
  apply (case_tac cap)
   apply (simp_all add:vs_cap_ref_def table_cap_ref_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap)
   apply simp_all
  apply (clarsimp simp:cap_refs_in_kernel_window_def
              valid_refs_def simp del:split_paired_All)
  apply (drule_tac x = cref in spec)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply fastforce
  done


lemma pbfs_atleast_pageBits':
  "pageBits \<le> pageBitsForSize sz"by (cases sz, simp_all add: pageBits_def)


lemma pbfs_less_wb':
  "pageBitsForSize sz < word_bits"by (cases sz, simp_all add: word_bits_conv pageBits_def)

lemma delete_objects_rewrite[Untyped_AI_assms]:
  "\<lbrakk>2\<le> sz; sz\<le> word_bits;ptr && ~~ mask sz = ptr\<rbrakk> \<Longrightarrow> delete_objects ptr sz = 
    do y \<leftarrow> modify (clear_um {ptr + of_nat k |k. k < 2 ^ sz});
    modify (detype {ptr && ~~ mask sz..ptr + 2 ^ sz - 1})
    od"
  apply (clarsimp simp:delete_objects_def freeMemory_def word_size_def)
  apply (subgoal_tac "is_aligned (ptr &&~~ mask sz) sz")
  apply (subst mapM_storeWord_clear_um)
  apply (simp)
  apply simp
  apply (simp add:range_cover_def)
  apply clarsimp
  apply (rule is_aligned_neg_mask)
  apply simp
  done

declare store_pde_pred_tcb_at [wp]

lemma invoke_untyped_st_tcb_at[Untyped_AI_assms]: (*FIXME: move *)
  "\<lbrace>(invs::'state_ext::state_ext state\<Rightarrow>bool) and st_tcb_at (P and (Not \<circ> inactive) and (Not \<circ> idle)) t
         and ct_active and valid_untyped_inv ui\<rbrace>
     invoke_untyped ui
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (cases ui, simp add: mapM_x_def[symmetric]
                  split del: split_if)
  apply (rename_tac cslot_ptr word1 word2 apiobject_type nat list)
  apply (rule hoare_name_pre_state)
  apply (clarsimp)
  apply (wp mapM_x_wp[OF _ subset_refl] get_cap_wp
            retype_region_st_tcb_at set_cap_no_overlap
            init_arch_objects_hoare_lift set_cap_valid_objs
        | simp add:split_def)+
   apply (rule_tac P = "2\<le> sz \<and> sz \<le> word_bits" in hoare_gen_asm(1))
   apply (rule_tac P = "cap = cap.UntypedCap word2 sz idx" in hoare_gen_asm(1))
   apply (clarsimp simp:bits_of_def delete_objects_rewrite)
   apply (wp get_cap_wp)
  apply (clarsimp simp: conj_comms freeMemory_def invs_psp_aligned invs_valid_objs)
  apply (frule caps_of_state_valid)
   apply (simp add:cte_wp_at_caps_of_state)
  apply (intro conjI)
   apply (clarsimp)
   apply (subgoal_tac "cap = cap.UntypedCap (word2 && ~~ mask sz) sz idx")
   apply (intro conjI)
          apply (erule pred_tcb_weakenE,simp)
         apply (simp add:bits_of_def)
         apply (erule(3) cte_wp_at_pspace_no_overlapI[OF _ _ _ range_cover.sz(1)
             [where 'a=32, folded word_bits_def]])
        apply (clarsimp simp:cte_wp_at_caps_of_state bits_of_def shiftl_t2n add_minus_neg_mask)
       apply (simp add:bits_of_def)
       apply (erule(3) cte_wp_at_pspace_no_overlapI[OF _ _ _ range_cover.sz(1)
           [where 'a=32, folded word_bits_def]])
      apply (clarsimp simp:cte_wp_at_caps_of_state bits_of_def shiftl_t2n add_minus_neg_mask)
     apply (simp add: valid_untyped_cap_inc field_simps bits_of_def add_minus_neg_mask shiftl_t2n)
    apply (clarsimp simp:cte_wp_at_caps_of_state)
    apply (drule(1) tcb_cap_valid_caps_of_stateD[OF _ invs_valid_objs])
    apply (simp cong:tcb_cap_valid_untyped_cong add:bits_of_def)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply clarsimp
  apply (rule conjI)
   apply (simp add:valid_cap_simps cap_aligned_def)
  apply (rule conjI)
   apply (erule pred_tcb_weakenE,simp)
  apply (rule conjI)
   apply (simp add:valid_cap_simps cap_aligned_def)
  apply (rule context_conjI)
   apply (simp add: cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
    apply (clarsimp split: Structures_A.thread_state.splits)
   apply (drule ex_nonz_cap_to_overlap)
    apply ((simp add:cte_wp_at_caps_of_state
            is_cap_simps descendants_range_def2)+)[5]
  apply (rule conjI)
   apply (simp add:bits_of_def)
  apply ((frule detype_invariants,(clarsimp
    simp: invs_psp_aligned bits_of_def invs_valid_objs
    cte_wp_at_caps_of_state descendants_range_def2)+)[1])+
  apply (cut_tac cap' = "cap.UntypedCap word2 sz idx" and cap = "cap.UntypedCap word2 sz idx"
    and ptr = "(a,b)" and s = sa in detype_locale.valid_cap)
     apply (simp add:detype_locale_def cte_wp_at_caps_of_state
       descendants_range_def2 invs_untyped_children)
    apply (erule(1) caps_of_state_valid[rotated])
   apply (simp add:obj_reply_refs_def)
  apply (subgoal_tac "{word2 + of_nat k |k. k < 2 ^ sz} = {word2 ..word2 + 2^sz - 1}")
   prefer 2
   apply (subst intvl_range_conv)
     apply (subgoal_tac "is_aligned (word2 && ~~ mask sz) sz")
      apply simp
     apply (rule is_aligned_neg_mask,simp)
    apply (simp add:valid_cap_simps cap_aligned_def word_bits_def)
   apply simp
  apply (clarsimp simp:invs_psp_aligned invs_valid_objs)
  apply (clarsimp simp:detype_clear_um_independent)
  apply (intro conjI)
    apply (rule detype_valid_untyped)
       apply simp
      apply simp
     apply simp
    apply (clarsimp simp:cte_wp_at_caps_of_state range_cover.unat_of_nat_n_shift)
    apply (subst mult.commute)
    apply (rule nat_le_power_trans[OF range_cover.range_cover_n_le(2)])
     apply assumption
    apply (erule range_cover.sz(2))
   apply (erule pspace_no_overlap_detype)
    apply (simp add:invs_psp_aligned invs_valid_objs)+
  apply (rule_tac c1 = idx in subst[OF tcb_cap_valid_untyped_cong])
    apply assumption
   apply simp
  apply (clarsimp simp:cte_wp_at_caps_of_state bits_of_def)
  apply (drule(1) tcb_cap_valid_caps_of_stateD[OF _ invs_valid_objs])
  apply (clarsimp simp:tcb_cap_valid_def)
 done


(* nonempty_table *)
definition
  nonempty_table :: "word32 set \<Rightarrow> Structures_A.kernel_object \<Rightarrow> bool"
where
 "nonempty_table S ko \<equiv>
    (a_type ko = AArch APageTable \<or> a_type ko = AArch APageDirectory)
       \<and> \<not> empty_table S ko"

lemma reachable_pg_cap_exst_update[simp]:
  "reachable_pg_cap x (trans_state f (s::'state_ext::state_ext state)) = reachable_pg_cap x s"
  by (simp add:reachable_pg_cap_def vs_lookup_pages_def
    vs_lookup_pages1_def obj_at_def)

lemma create_cap_valid_arch_caps[wp, Untyped_AI_assms]:
  "\<lbrace>valid_arch_caps
      and valid_cap (default_cap tp oref sz)
      and (\<lambda>(s::'state_ext::state_ext state). \<forall>r\<in>obj_refs (default_cap tp oref sz).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
      and cte_wp_at (op = cap.NullCap) cref
      and K (tp \<noteq> ArchObject ASIDPoolObj)\<rbrace>
     create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: create_cap_def set_cdt_def)
  apply (wp set_cap_valid_arch_caps hoare_vcg_disj_lift
      hoare_vcg_conj_lift hoare_vcg_all_lift hoare_vcg_imp_lift
    | simp add: trans_state_update[symmetric] del: trans_state_update split_paired_All split_paired_Ex imp_disjL split del: split_if)+
  apply (clarsimp simp del: split_paired_All split_paired_Ex
                            imp_disjL
                      simp: cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                         cte_wp_at_caps_of_state)
   apply (case_tac "\<exists>x. x \<in> obj_refs cap")
    apply (clarsimp dest!: obj_ref_elemD)
    apply (case_tac cref, fastforce)
   apply (simp add: obj_ref_none_no_asid)
  apply (rule conjI)
   apply (auto simp: is_cap_simps valid_cap_def
                     obj_at_def nonempty_table_def a_type_simps)[1]
  apply (clarsimp simp del: imp_disjL)
  apply (case_tac "\<exists>x. x \<in> obj_refs cap")
   apply (clarsimp dest!: obj_ref_elemD)
   apply fastforce
  apply (auto simp: is_cap_simps)[1]
  done

lemma create_cap_cap_refs_in_kernel_window[wp, Untyped_AI_assms]:
  "\<lbrace>cap_refs_in_kernel_window and cte_wp_at (\<lambda>c. cap_range (default_cap tp oref sz) \<subseteq> cap_range c) p\<rbrace>
     create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) cap_refs_in_kernel_windowD)
  apply blast
  done

(**)

crunch irq_node[wp]: store_pde "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

(* make these available in the generic theory? *)
lemma init_arch_objects_irq_node[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> init_arch_objects tp ptr bits us refs \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
  by (wp init_arch_objects_hoare_lift, simp)

lemma init_arch_objects_excap[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace> init_arch_objects tp ptr bits us refs \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  by (wp ex_cte_cap_to_pres init_arch_objects_irq_node init_arch_objects_cte_wp_at)
(**)

crunch nonempty_table[wp]: do_machine_op
  "\<lambda>s. P' (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)"

lemma store_pde_weaken:
  "\<lbrace>\<lambda>s. page_directory_at (p && ~~ mask pd_bits) s \<longrightarrow> P s\<rbrace> store_pde p e \<lbrace>Q\<rbrace> =
   \<lbrace>P\<rbrace> store_pde p e \<lbrace>Q\<rbrace>"
  apply (rule iffI)
   apply (simp add: valid_def)
   apply (erule allEI)
   apply clarsimp
  apply (simp add: valid_def)
  apply (erule allEI)
  apply clarsimp
  apply (rule use_valid, assumption)
   apply (simp add: store_pde_def set_pd_def set_object_def)
   apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (drule bspec, assumption)
  apply (simp add: simpler_store_pde_def obj_at_def fun_upd_def
            split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  done

lemma store_pde_nonempty_table:
  "\<lbrace>\<lambda>s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
           \<and> (\<forall>rf. pde_ref pde = Some rf \<longrightarrow>
                   rf \<in> set (arm_global_pts (arch_state s)))
           \<and> ucast (pde_ptr && mask pd_bits >> 2) \<in> kernel_mapping_slots
           \<and> valid_pde_mappings pde\<rbrace>
     store_pde pde_ptr pde
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def nonempty_table_def a_type_def)
  apply (clarsimp simp add: empty_table_def)
  done

lemma store_pde_global_global_objs:
  "\<lbrace>\<lambda>s. valid_global_objs s
           \<and> (\<forall>rf. pde_ref pde = Some rf \<longrightarrow>
                   rf \<in> set (arm_global_pts (arch_state s)))
           \<and> ucast (pde_ptr && mask pd_bits >> 2) \<in> kernel_mapping_slots
           \<and> valid_pde_mappings pde\<rbrace>
   store_pde pde_ptr pde
   \<lbrace>\<lambda>rv s. valid_global_objs s\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def fun_upd_def[symmetric])
proof -
  fix s pd
  assume vg: "valid_global_objs s"
     and gr: "\<forall>rf. pde_ref pde = Some rf \<longrightarrow>
                   rf \<in> set (arm_global_pts (arch_state s))"
     and uc: "ucast (pde_ptr && mask pd_bits >> 2) \<in> kernel_mapping_slots"
     and vp: "valid_pde_mappings pde"
     and pd: "kheap s (pde_ptr && ~~ mask pd_bits) =
              Some (ArchObj (PageDirectory pd))"
  let ?ko' = "ArchObj (PageDirectory
                         (pd(ucast (pde_ptr && mask pd_bits >> 2) := pde)))"
  let ?s' = "s\<lparr>kheap := kheap s(pde_ptr && ~~ mask pd_bits \<mapsto> ?ko')\<rparr>"
  have typ_at: "\<And>T p. typ_at T p s \<Longrightarrow> typ_at T p ?s'"
    using pd
    by (clarsimp simp: obj_at_def a_type_def)
  have valid_pde: "\<And>pde. valid_pde pde s \<Longrightarrow> valid_pde pde ?s'"
    by (case_tac pdea, simp_all add: typ_at)
  have valid_pte: "\<And>pte. valid_pte pte s \<Longrightarrow> valid_pte pte ?s'"
    by (case_tac pte, simp_all add: typ_at)
  have valid_ao_at: "\<And>p. valid_ao_at p s \<Longrightarrow> valid_ao_at p ?s'"
    using pd uc
    apply (clarsimp simp: valid_ao_at_def obj_at_def)
    apply (intro conjI impI allI)
      apply (clarsimp simp: valid_pde vp)
    apply (case_tac ao, simp_all add: typ_at valid_pde valid_pte)
    done
  have empty:
    "\<And>p. obj_at (empty_table (set (arm_global_pts (arch_state s)))) p s
          \<Longrightarrow> obj_at (empty_table (set (arm_global_pts (arch_state s)))) p ?s'"
    using pd gr vp uc
    by (clarsimp simp: obj_at_def empty_table_def)
  show "valid_global_objs ?s'"
    using vg pd
    apply (clarsimp simp add: valid_global_objs_def valid_ao_at empty)
    apply (fastforce simp add: obj_at_def)
    done
qed

lemma valid_arch_state_global_pd:
  "\<lbrakk> valid_arch_state s; pspace_aligned s \<rbrakk>
    \<Longrightarrow> obj_at (\<lambda>ko. \<exists>pd. ko = ArchObj (PageDirectory pd)) (arm_global_pd (arch_state s)) s
           \<and> is_aligned (arm_global_pd (arch_state s)) pd_bits"
  apply (clarsimp simp: valid_arch_state_def a_type_def
                        pd_aligned pd_bits_def pageBits_def
                 elim!: obj_at_weakenE)
  apply (clarsimp split: Structures_A.kernel_object.split_asm
                         arch_kernel_obj.split_asm split_if_asm)
  done

lemma pd_shifting':
  "is_aligned (pd :: word32) pd_bits \<Longrightarrow> pd + (vptr >> 20 << 2) && ~~ mask pd_bits = pd"
  by (rule pd_shifting, simp add: pd_bits_def pageBits_def)

lemma copy_global_mappings_nonempty_table:
  "is_aligned pd pd_bits \<Longrightarrow>
   \<lbrace>\<lambda>s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s) \<and>
        valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s\<rbrace>
   copy_global_mappings pd
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table
                        (set (arm_global_pts (arch_state s)))) r s) \<and>
           valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp[where S="{x. kernel_base >> 20 \<le> x \<and>
                                      x < 2 ^ (pd_bits - 2)}"])
    apply (wp get_pde_wp hoare_vcg_ball_lift
              store_pde_weaken[THEN iffD2,OF store_pde_nonempty_table]
              store_pde_weaken[THEN iffD2,OF store_pde_global_global_objs]
           | simp)+
    apply clarsimp
    apply (subst (asm) is_aligned_add_helper[THEN conjunct2])
      apply (clarsimp simp: valid_arch_state_def pspace_aligned_def dom_def
                            obj_at_def)
      apply (drule_tac x="arm_global_pd (arch_state s)" in spec, erule impE,
             fastforce)
      apply (simp add: pd_bits_def pageBits_def)
     apply (erule shiftl_less_t2n)
     apply (simp add: pd_bits_def pageBits_def)
    apply (clarsimp simp: valid_arch_state_def valid_global_objs_def obj_at_def
                          empty_table_def)
    apply (simp add: kernel_mapping_slots_def)
    apply (subst is_aligned_add_helper[THEN conjunct1], assumption)
     apply (erule shiftl_less_t2n)
     apply (simp add: pd_bits_def pageBits_def)
    apply (simp add: kernel_base_shift_cast_le[symmetric] ucast_ucast_mask)
    apply (subst shiftl_shiftr_id)
      apply simp
     apply (simp add: word_less_nat_alt pd_bits_def pageBits_def)
    apply (subst less_mask_eq)
     apply (simp add: pd_bits_def pageBits_def)
    apply assumption
   apply (clarsimp simp: pd_bits_def)
  apply simp
  done


lemma mapM_copy_global_mappings_nonempty_table[wp]:
  "\<lbrace>(\<lambda>s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
        \<and> valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s) and
    K (\<forall>pd\<in>set pds. is_aligned pd pd_bits)\<rbrace>
   mapM_x copy_global_mappings pds
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp', rule copy_global_mappings_nonempty_table)
   apply simp_all
  done

(**)
lemma init_arch_objects_nonempty_table[wp]:
  "\<lbrace>(\<lambda>s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
         \<and> valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s) and
    K (tp = ArchObject PageDirectoryObj \<longrightarrow>
         (\<forall>pd\<in>set refs. is_aligned pd pd_bits))\<rbrace>
        init_arch_objects tp ptr bits us refs
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: init_arch_objects_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp add: create_word_objects_def reserve_region_def)+
  done


lemma nonempty_table_caps_of[Untyped_AI_assms]:
  "nonempty_table S ko \<Longrightarrow> caps_of ko = {}"
  by (auto simp: caps_of_def cap_of_def nonempty_table_def a_type_def
          split: Structures_A.kernel_object.split split_if_asm)


lemma nonempty_default[simp, Untyped_AI_assms]:
  "tp \<noteq> Untyped \<Longrightarrow> \<not> nonempty_table S (default_object tp us)"
  apply (case_tac tp, simp_all add: default_object_def nonempty_table_def
                                    a_type_def)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type, simp_all add: default_arch_object_def)
   apply (simp_all add: empty_table_def pde_ref_def valid_pde_mappings_def)
  done

(**)

lemma set_pd_cte_wp_at_iin[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at (P' (interrupt_irq_node s)) p s)\<rbrace>
   set_pd q pd
   \<lbrace>\<lambda>_ s. P (cte_wp_at (P' (interrupt_irq_node s)) p s)\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def cte_wp_at_caps_of_state
           split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (subst caps_of_state_after_update)
   apply (simp add: obj_at_def)+
  done

crunch cte_wp_at_iin[wp]: init_arch_objects
  "\<lambda>s. P (cte_wp_at (P' (interrupt_irq_node s)) p s)"
  (ignore: clearMemory wp: crunch_wps)

lemma init_arch_objects_ex_cte_cap_wp_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace>
   init_arch_objects tp ptr no us orefs
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  by (simp add: ex_cte_cap_wp_to_def) (wp hoare_vcg_ex_lift)

end


locale invoke_untyped_proofs_arch = 
  invoke_untyped_proofs s cref ptr tp us slots sz idx + Arch
  for s :: "'state_ext :: state_ext state"
  and  cref ptr tp us slots sz idx

lemma (in invoke_untyped_proofs_arch) kernel_window_inv[simp]: 
  "\<forall>x\<in>usable_range.
  arm_kernel_vspace (arch_state s) x = ArmVSpaceKernelWindow"
  using cte_wp_at misc
  apply (clarsimp simp:cte_wp_at_caps_of_state invs_def valid_state_def)
  apply (erule(1) cap_refs_in_kernel_windowD[THEN bspec])
  apply (simp add:blah cap_range_def)
  apply clarsimp
  apply (erule order_trans[OF word_and_le2])
  done 

(* invoke_untyp_invs proof: in-proof assumptions and haves *)
locale invoke_untyp_invs_retype_assms_arch = 
  invoke_untyp_invs_retype_assms state_ext_t Q + Arch
  for state_ext_t :: "'state_ext::state_ext itself"
  and Q :: "'state_ext state \<Rightarrow> bool"
begin
lemma gen_pd_align[simp]:
      "\<And>pd. tp = ArchObject PageDirectoryObj \<Longrightarrow> 
             is_aligned pd pd_bits = is_aligned pd (obj_bits_api tp us)"
by (simp add: obj_bits_api_def default_arch_object_def
                    pd_bits_def pageBits_def)


lemma range_cover_pd[simp]:
      "(tp = ArchObject PageDirectoryObj \<longrightarrow>
        range_cover ptr sz (obj_bits_api (ArchObject PageDirectoryObj) us)
                    (length slots))"
using cover by clarsimp

lemma pf_arch :
   "invoke_untyped_proofs_arch (s::'state_ext state) (cref,oref) ptr tp us slots sz idx"
      using  cte_wp_at desc_range misc cover vslot 
      apply (clarsimp simp:invoke_untyped_proofs_arch_def invoke_untyped_proofs_def cte_wp_at_caps_of_state)
      apply (drule(1) bspec)
      apply (clarsimp elim!:ex_cte_cap_wp_to_weakenE)
      done

lemmas msimp[simp] = misc neg_mask_add_mask
end

global_interpretation Untyped_AI? : Untyped_AI
  where nonempty_table = ARM.nonempty_table
 proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (unfold_locales; fact Untyped_AI_assms)
qed


(* invoke_untyp_invs proof *)
context invoke_untyp_invs_assumptions begin

interpretation Arch .

lemma invoke_untyp_invs'' : 
  "\<lbrace>(invs ::'state_ext::state_ext state \<Rightarrow> bool) and Q and valid_untyped_inv ui and ct_active\<rbrace> 
  invoke_untyped ui \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  apply (cases ui, simp split del: split_if del:invoke_untyped.simps)
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp del:split_paired_All split_paired_Ex split_paired_Ball invoke_untyped.simps)
  apply (rename_tac cref oref ptr tp us slots s sz idx)
  proof -
    fix cref oref ptr tp us slots s sz idx
    assume cte_wp_at : "cte_wp_at (\<lambda>c. c = cap.UntypedCap (ptr && ~~ mask sz) sz idx) (cref,oref) (s::'state_ext::state_ext state)"
     have cte_at: "cte_wp_at (op = (cap.UntypedCap (ptr && ~~ mask sz) sz idx)) (cref,oref) s" (is "?cte_cond s")
       using cte_wp_at by (simp add:cte_wp_at_caps_of_state)
    assume desc_range: "ptr = ptr && ~~ mask sz \<longrightarrow> descendants_range_in {ptr..ptr + 2 ^ sz - 1} (cref,oref) s"
    assume  misc     : "distinct slots" "tp = CapTableObject \<longrightarrow> 0 < (us::nat)"
      " tp = Untyped \<longrightarrow> 4 \<le> (us::nat)"
      " idx \<le> unat (ptr && mask sz) \<or> ptr = ptr && ~~ mask sz"
      " invs s" "Q s" "tp \<noteq> ArchObject ASIDPoolObj"
      " \<forall>slot\<in>set slots. cte_wp_at (op = cap.NullCap) slot s \<and> ex_cte_cap_wp_to is_cnode_cap slot s \<and> real_cte_at slot s"
      " ct_active s"
    assume cover     : "range_cover ptr sz (obj_bits_api tp us) (length slots)"
    assume vslot : "slots\<noteq> []"

interpret invoke_untyp_invs_retype_assms_arch cref oref ptr tp us slots s sz idx
  apply (unfold_locales; fact?)
  apply (auto simp add: cover[simplified range_cover_def, simplified])
done  

  note kernel_window_inv[simp] = invoke_untyped_proofs_arch.kernel_window_inv[OF pf_arch]

  show "\<lbrace>op = s\<rbrace> invoke_untyped 
        (Invocations_A.untyped_invocation.Retype (cref, oref) (ptr && ~~ mask sz) ptr tp us slots) 
        \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
      using misc cover

      apply (simp add:mapM_x_def[symmetric])
      apply (case_tac "ptr && ~~ mask sz \<noteq> ptr")
       apply (simp add: cte_wp_at_conj ball_conj_distrib
              | wp_trace hoare_vcg_const_Ball_lift set_tuple_pick
                   retype_region_ex_cte_cap_to [where sz = sz] 
                   retype_region_obj_ref_range [where sz = sz]
                   hoare_vcg_all_lift
                     [of _ _ "%a _ p. \<forall>b. ~ cte_wp_at P (a,b) p" for P]
                   hoare_vcg_all_lift
                     [of _ _ "%b _ p. ~ cte_wp_at P (a,b) p" for P a]
                   retype_region_not_cte_wp_at [where sz = sz]
                   init_arch_objects_invs_from_restricted 
                   retype_ret_valid_caps [where sz = sz]
                   retype_region_global_refs_disjoint [where sz = sz]
                   retype_region_post_retype_invs [where sz = sz]
                   retype_region_cte_at_other[where sz = sz]
                   retype_region_invs_extras[where sz = sz]
                   retype_region_ranges [where sz = sz]
                   retype_region_caps_reserved [where sz = sz]
                   retype_region_distinct_sets [where sz = sz]
                   create_caps_invs
                   retype_region_descendants_range_ret[where sz = sz]
                   retype_region_obj_at_other2
                     [where P="is_cap_table n" for n]
                   distinct_tuple_helper)+
         apply ((wp hoare_vcg_const_imp_lift hoare_drop_imp
                    retype_region_invs_extras[where sz = sz]
                    retype_region_aligned_for_init[where sz = sz] | simp)+)[1]
        apply (clarsimp simp:conj_comms,simp cong:conj_cong)
        apply (simp add:ball_conj_distrib conj_comms)
        apply (strengthen imp_consequent invs_mdb invs_valid_pspace
               | clarsimp simp:conj_comms)+
        apply (rule_tac P = "cap = cap.UntypedCap (ptr && ~~ mask sz) sz idx"
                     in hoare_gen_asm)
        apply (simp add:bits_of_def region_in_kernel_window_def)
        apply (wp set_cap_no_overlap hoare_vcg_ball_lift
                  set_cap_free_index_invs_spec
                  set_cap_cte_wp_at set_cap_descendants_range_in
                  set_cap_caps_no_overlap
                  set_untyped_cap_caps_overlap_reserved set_cap_cte_cap_wp_to)
        apply (wp set_cap_cte_wp_at_neg hoare_vcg_all_lift get_cap_wp)
       apply (insert cte_wp_at)
       apply (clarsimp simp:cte_wp_at_caps_of_state untyped_range.simps)
       apply (insert misc) 
       apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
       apply (clarsimp simp:cte_wp_at_caps_of_state untyped_range.simps)
       apply (intro conjI)
                  apply (clarsimp simp:field_simps range_cover_unat shiftl_t2n)
                 apply (fastforce)+
             apply (clarsimp dest!:retype_addrs_subset_ptr_bits slots_invD)
             apply (drule(1) subsetD)
             apply (simp add:p_assoc_help)
            apply (erule subset_trans[OF range_cover_subset'])
             apply (simp add:vslot)
            apply (clarsimp simp:blah word_and_le2)
            apply (clarsimp simp: blah field_simps add.assoc[symmetric]
                                 shiftl_t2n add.commute 
                          dest!: idx_compare'')+
           apply simp+
          apply (simp add:Int_ac)
          apply (erule disjoint_subset2[rotated])
          apply (clarsimp simp:blah word_and_le2)
         apply (rule refl)
        apply (clarsimp simp:obj_at_def)
        apply (drule(1) pspace_no_overlap_obj_range
                        [OF ps_no_overlap _ subset_refl])
        apply (drule p_in_obj_range)
          apply (simp add:misc invs_psp_aligned invs_valid_objs)+
        apply blast
       apply clarsimp
       apply (drule untyped_mdb_descendants_range)
             apply (simp add:misc invs_mdb)+
           apply (rule descendants_range)
          apply (clarsimp simp:blah word_and_le2)
         apply assumption+
       apply simp
      apply (simp add: cte_wp_at_conj ball_conj_distrib
             | wp hoare_vcg_const_Ball_lift set_tuple_pick
                  retype_region_ex_cte_cap_to [where sz = sz] 
                  retype_region_obj_ref_range [where sz = sz]
                  hoare_vcg_all_lift
                    [of _ _ "%a _ p. \<forall>b. ~ cte_wp_at P (a,b) p" for P]
                  hoare_vcg_all_lift
                    [of _ _ "%b _ p. ~ cte_wp_at P (a,b) p" for P a]
                  retype_region_not_cte_wp_at [where sz = sz]
                  init_arch_objects_invs_from_restricted 
                  retype_ret_valid_caps [where sz = sz]
                  retype_region_global_refs_disjoint [where sz = sz]
                  retype_region_post_retype_invs [where sz = sz]
                  retype_region_cte_at_other[where sz = sz]
                  retype_region_invs_extras[where sz = sz]
                  retype_region_ranges [where sz = sz]
                  retype_region_caps_reserved [where sz = sz]
                  retype_region_distinct_sets [where sz = sz]
                  create_caps_invs
                  retype_region_descendants_range_ret[where sz = sz]
                  retype_region_obj_at_other2
                    [where P="is_cap_table n" for n]
                  distinct_tuple_helper)+
         apply ((wp hoare_vcg_const_imp_lift hoare_drop_imp
                    retype_region_invs_extras[where sz = sz]
                    retype_region_aligned_for_init[where sz = sz] | simp)+)[1]
        apply (clarsimp simp:conj_comms,simp cong:conj_cong)
        apply (simp add:ball_conj_distrib conj_comms)
        apply (strengthen imp_consequent invs_mdb invs_valid_pspace
               | clarsimp simp:conj_comms)+
        apply (rule_tac P = "cap = cap.UntypedCap ptr sz idx" in hoare_gen_asm)
        apply (simp add:bits_of_def region_in_kernel_window_def)
        apply (wp set_cap_no_overlap hoare_vcg_ball_lift
                  set_untyped_cap_invs_simple
                  set_cap_cte_wp_at set_cap_descendants_range_in
                  set_cap_caps_no_overlap set_untyped_cap_caps_overlap_reserved
                  set_cap_cte_cap_wp_to)
        apply (wp set_cap_cte_wp_at_neg hoare_vcg_all_lift)
       apply (rule_tac P = "cap = cap.UntypedCap ptr sz idx \<and> sz \<le> word_bits 
                            \<and> 2 \<le> sz" in hoare_gen_asm)
       apply (clarsimp simp:delete_objects_rewrite bits_of_def)
       apply (wp get_cap_wp)
      apply (insert cte_wp_at)
      apply (clarsimp simp:cte_wp_at_caps_of_state untyped_range.simps)
      apply (insert misc descendants_range cref_inv cte_at subset_stuff
        detype_locale detype_descendants_range_in detype_invs kernel_window_inv)
      apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
      apply (clarsimp simp:cte_wp_at_caps_of_state invs_valid_objs
        untyped_range.simps bits_of_def conj_comms)
      apply (frule caps_of_state_valid[rotated])
       apply simp
      apply (frule valid_cap_aligned)
      apply (clarsimp simp:cap_aligned_def detype_clear_um_independent
        intvl_range_conv Int_ac valid_cap_simps)
      apply (intro conjI)
                     apply (clarsimp simp:field_simps range_cover_unat shiftl_t2n)
                    apply ((fastforce)+)[3]
                   apply (clarsimp dest!:retype_addrs_subset_ptr_bits slots_invD)
                   apply (drule(1) subsetD)
                   apply (simp add:p_assoc_help)
                  apply (clarsimp simp: intvl_range_conv[where 'a=32, folded word_bits_def] 
                             dest!:slots_invD)+
                 apply (subst detype_clear_um_independent[symmetric])
                 apply (simp add:detype_Q[simplified])
                apply (rule pspace_no_overlap_detype)
               apply (rule caps_of_state_valid)
                apply simp+
              apply (simp add:invs_psp_aligned invs_valid_objs)+
            apply (rule caps_no_overlap_detype[OF caps_no_overlap])
           apply (frule is_aligned_neg_mask_eq'[THEN iffD2])
           apply (clarsimp simp:blah field_simps add.commute shiftl_t2n is_aligned_mask)
           apply (drule idx_compare'''[rotated])
            apply (clarsimp simp:is_aligned_mask)
           apply (simp add:not_less[symmetric])
          apply (clarsimp dest!:slots_invD)+
          apply (erule cap_to_protected[OF _ _ ])
            apply (fastforce simp:cte_wp_at_caps_of_state)
           apply (simp add:descendants_range_def2 blah)
          apply simp
         apply (clarsimp dest!:slots_invD)+
        apply (simp add:detype_def Int_ac clear_um_def)
       apply (erule descendants_range_in_subseteq)
       apply (simp add:subset_stuff)
      apply (frule is_aligned_neg_mask_eq'[THEN iffD2])
      apply clarsimp
      apply (drule untyped_mdb_descendants_range)
            apply (simp add:misc invs_mdb)+
         apply (clarsimp simp:blah)
        apply assumption+
    apply simp
    done
qed

end

lemmas invoke_untyp_invs' = 
  invoke_untyp_invs_assumptions.invoke_untyp_invs''[simplified invoke_untyp_invs_assumptions_def]

lemmas invoke_untyp_invs[wp] = 
  invoke_untyp_invs'[where Q=\<top>,simplified hoare_post_taut, simplified]

end