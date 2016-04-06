(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
ARM VSpace refinement
*)

theory VSpace_AI
imports "./$L4V_ARCH/ArchVSpace_AI"
begin
context Arch begin

unqualify_consts
  glob_vs_refs
  pspace_in_kernel_window



end









lemma set_mrs_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_mrs t buf mrs \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_mrs_def zipWithM_x_mapM split_def
                   store_word_offs_def set_object_def
              cong: option.case_cong
              split del: split_if)
  apply (wp hoare_vcg_split_case_option)
    apply (rule mapM_wp [where S=UNIV, simplified])
    apply (wp | simp)+
  apply (clarsimp simp: obj_at_def a_type_def
                  dest!: get_tcb_SomeD)
  done


lemma set_mrs_tcb[wp]:
  "\<lbrace> tcb_at t \<rbrace> set_mrs receiver recv_buf mrs \<lbrace>\<lambda>rv. tcb_at t \<rbrace>"
  by (simp add: tcb_at_typ, wp)


lemma set_mrs_ntfn_at[wp]:
  "\<lbrace> ntfn_at p \<rbrace> set_mrs receiver recv_buf mrs \<lbrace>\<lambda>rv. ntfn_at p \<rbrace>"
  by (simp add: ntfn_at_typ, wp)


lemmas set_mrs_redux =
   set_mrs_def bind_assoc[symmetric]
   thread_set_def[simplified, symmetric]

lemma storeWord_invs[wp]:
  "\<lbrace>in_user_frame p and invs\<rbrace> do_machine_op (storeWord p w) \<lbrace>\<lambda>rv. invs\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>l sz. l<4 \<Longrightarrow> p && mask 2 = 0 \<Longrightarrow>
       p+l && ~~ mask (pageBitsForSize sz) = p && ~~ mask (pageBitsForSize sz)"
  proof -
    fix l sz
    assume al: "p && mask 2 = 0"
    assume "(l::word32) < 4" hence less: "l<2^2" by simp
    have le: "2 \<le> pageBitsForSize sz" by (case_tac sz, simp_all)
    show "?thesis l sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=2, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs)
    apply (clarsimp simp: storeWord_def invs_def valid_state_def)
    apply (fastforce simp: valid_machine_state_def in_user_frame_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore
             split: split_if_asm)
    done
qed

lemma set_mrs_invs[wp]:
  "\<lbrace> invs and tcb_at receiver \<rbrace> set_mrs receiver recv_buf mrs \<lbrace>\<lambda>rv. invs \<rbrace>"
  apply (simp add: set_mrs_redux)
  apply wp
   apply (rule_tac P="invs" in hoare_triv)
   apply (case_tac recv_buf)
    apply simp
   apply (simp add: zipWithM_x_mapM split del: split_if)
   apply wp
   apply (rule mapM_wp)
    apply (simp add: split_def store_word_offs_def)
    apply (wp storeWord_invs)
    apply simp
   apply blast
  apply (wp thread_set_invs_trivial)
  apply (auto simp: tcb_cap_cases_def)
  done

lemma set_mrs_thread_set_dmo:
  assumes ts: "\<And>c. \<lbrace>P\<rbrace> thread_set (\<lambda>tcb. tcb\<lparr>tcb_context := c tcb\<rparr>) r \<lbrace>\<lambda>rv. Q\<rbrace>"
  assumes dmo: "\<And>x y. \<lbrace>Q\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> set_mrs r t mrs \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (simp add: set_mrs_redux)
  apply (case_tac t)
   apply simp
   apply wp
   apply (rule ts)
  apply (simp add: zipWithM_x_mapM store_word_offs_def split_def
              split del: split_if)
  apply (wp mapM_wp dmo)
    apply simp
   apply blast
  apply (rule ts)
  done

lemma set_mrs_st_tcb [wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_mrs r t' mrs \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (rule set_mrs_thread_set_dmo) 
   apply (rule thread_set_no_change_tcb_pred)
   apply (simp add: tcb_to_itcb_def)
  apply wp
  done

lemma perform_page_invs [wp]:
  "\<lbrace>invs and valid_page_inv pi\<rbrace> perform_page_invocation pi \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases pi, simp_all)
     -- "PageMap"
     apply (rename_tac asid cap cslot_ptr sum)
     apply clarsimp
     apply (rule hoare_pre)
      apply (wp get_master_pte_wp get_master_pde_wp mapM_swp_store_pde_invs_unmap store_pde_invs_unmap' hoare_vcg_const_imp_lift hoare_vcg_all_lift set_cap_arch_obj arch_update_cap_invs_map
             | wpc 
             | simp add: pte_check_if_mapped_def pde_check_if_mapped_def del: fun_upd_apply 
             | subst cte_wp_at_caps_of_state)+
       apply (wp_once hoare_drop_imp)
       apply (wp arch_update_cap_invs_map)
       apply (rule hoare_vcg_conj_lift)
        apply (rule hoare_lift_Pf[where f=vs_lookup, OF _ set_cap_vs_lookup])
        apply (rule_tac f="valid_pte xa" in hoare_lift_Pf[OF _ set_cap_valid_pte_stronger])
        apply wp
       apply (rule hoare_lift_Pf2[where f=vs_lookup, OF _ set_cap_vs_lookup])
       apply ((wp dmo_ccr_invs arch_update_cap_invs_map
                 hoare_vcg_const_Ball_lift
                 hoare_vcg_const_imp_lift hoare_vcg_all_lift set_cap_typ_at
                 hoare_vcg_ex_lift hoare_vcg_ball_lift set_cap_arch_obj
                 set_cap_vs_lookup 
              | wpc | simp add: same_refs_def del: fun_upd_apply split del: split_if
              | subst cte_wp_at_caps_of_state)+)
      apply (wp_once hoare_drop_imp)
      apply (wp arch_update_cap_invs_map hoare_vcg_ex_lift set_cap_arch_obj)
     apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state neq_Nil_conv
                           valid_slots_def empty_refs_def parent_for_refs_def
                 simp del: fun_upd_apply del: exE
                    split: sum.splits)
      apply (rule conjI)
       apply (clarsimp simp: is_cap_simps is_arch_update_def
                             cap_master_cap_simps
                      dest!: cap_master_cap_eqDs)
      apply clarsimp
      apply (rule conjI)
       apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
       apply (rule conjI)
        apply (clarsimp simp: is_arch_update_def is_pt_cap_def is_pg_cap_def
                              cap_master_cap_def image_def
                        split: Structures_A.cap.splits arch_cap.splits)
       apply (clarsimp simp: is_pt_cap_def cap_asid_def image_def neq_Nil_conv Collect_disj_eq
                      split: Structures_A.cap.splits arch_cap.splits option.splits)
      apply (rule conjI)
       apply (drule same_refs_lD)
       apply clarsimp
       apply fastforce
      apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
      apply (clarsimp simp: is_arch_update_def
                            cap_master_cap_def is_cap_simps
                     split: Structures_A.cap.splits arch_cap.splits)
     apply (rule conjI)
      apply (erule exEI)
      apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
      apply (clarsimp simp: is_arch_update_def
                            cap_master_cap_def is_cap_simps
                     split: Structures_A.cap.splits arch_cap.splits)
     apply (rule conjI)
      apply (rule_tac x=a in exI, rule_tac x=b in exI, rule_tac x=cap in exI)
      apply (clarsimp simp: same_refs_def)
     apply (rule conjI)
      apply (clarsimp simp: pde_at_def obj_at_def
                            caps_of_state_cteD'[where P=\<top>, simplified])
      apply (drule_tac cap=capc and ptr="(aa,ba)"
                    in valid_global_refsD[OF invs_valid_global_refs])
        apply assumption+
      apply (clarsimp simp: cap_range_def)
     apply (clarsimp)
     apply (rule conjI)
      apply (clarsimp simp: pde_at_def obj_at_def a_type_def)
      apply (clarsimp split: Structures_A.kernel_object.split_asm
                            split_if_asm Arch_Structs_A.arch_kernel_obj.splits)
     apply (erule ballEI)
     apply (clarsimp simp: pde_at_def obj_at_def
                            caps_of_state_cteD'[where P=\<top>, simplified])
     apply (drule_tac cap=capc and ptr="(aa,ba)"
                    in valid_global_refsD[OF invs_valid_global_refs])
       apply assumption+
     apply (drule_tac x=sl in imageI[where f="\<lambda>x. x && ~~ mask pd_bits"])
     apply (drule (1) subsetD)
     apply (clarsimp simp: cap_range_def)
   -- "PageRemap"
    apply (rule hoare_pre)
     apply (wp get_master_pte_wp get_master_pde_wp hoare_vcg_ex_lift mapM_x_swp_store_pde_invs_unmap
              | wpc | simp add: pte_check_if_mapped_def pde_check_if_mapped_def 
              | (rule hoare_vcg_conj_lift, rule_tac slots=x2a in store_pde_invs_unmap'))+
    apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state
                          valid_slots_def empty_refs_def neq_Nil_conv
                    split: sum.splits)
     apply (clarsimp simp: parent_for_refs_def same_refs_def is_cap_simps cap_asid_def split:option.splits)
     apply (rule conjI, fastforce)
     apply (rule conjI)
      apply clarsimp
      apply (rule_tac x=ac in exI, rule_tac x=bc in exI, rule_tac x=capa in exI)
      apply clarsimp
      apply (erule (2) ref_is_unique[OF _ _ reachable_page_table_not_global])
              apply (simp_all add: invs_def valid_state_def valid_arch_state_def
                                   valid_arch_caps_def valid_pspace_def valid_objs_caps)[9]
     apply fastforce
    apply( frule valid_global_refsD2)
     apply (clarsimp simp: cap_range_def parent_for_refs_def)+
    apply (rule conjI, rule impI)
     apply (rule exI, rule exI, rule exI)
     apply (erule conjI)
     apply clarsimp
    apply (rule conjI, rule impI)
     apply (rule_tac x=ac in exI, rule_tac x=bc in exI, rule_tac x=capa in exI)
     apply (clarsimp simp: same_refs_def pde_ref_def pde_ref_pages_def
                valid_pde_def invs_def valid_state_def valid_pspace_def)
     apply (drule valid_objs_caps)
     apply (clarsimp simp: valid_caps_def)
     apply (drule spec, drule spec, drule_tac x=capa in spec, drule (1) mp)
     apply (case_tac aa, simp_all)
      apply ((clarsimp simp: valid_cap_def obj_at_def a_type_def is_ep_def
                             is_ntfn_def is_cap_table_def is_tcb_def
                             is_pg_cap_def
                     split: cap.splits Structures_A.kernel_object.splits
                            split_if_asm
                            Arch_Structs_A.arch_kernel_obj.splits option.splits
                            arch_cap.splits)+)[2]
    apply (clarsimp simp: pde_at_def obj_at_def a_type_def)
    apply (rule conjI)
     apply clarsimp
     apply (drule_tac ptr="(ab,bb)" in
            valid_global_refsD[OF invs_valid_global_refs caps_of_state_cteD])
       apply simp+
     apply force
    apply (erule ballEI)
    apply clarsimp
    apply (drule_tac ptr="(ab,bb)" in
            valid_global_refsD[OF invs_valid_global_refs caps_of_state_cteD])
      apply simp+
    apply force
   -- "PageUnmap"
   apply (rename_tac arch_cap cslot_ptr)
   apply (rule hoare_pre)
    apply (wp dmo_invs arch_update_cap_invs_unmap_page get_cap_wp
              hoare_vcg_const_imp_lift | wpc | simp)+
      apply (rule_tac Q="\<lambda>_ s. invs s \<and>
                               cte_wp_at (\<lambda>c. is_pg_cap c \<and>
                                 (\<forall>ref. vs_cap_ref c = Some ref \<longrightarrow>
                                        \<not> (ref \<unrhd> obj_ref_of c) s)) cslot_ptr s"
                   in hoare_strengthen_post)
       prefer 2
       apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps
                             update_map_data_def
                             is_arch_update_def cap_master_cap_simps)
       apply (drule caps_of_state_valid, fastforce)
       apply (clarsimp simp: valid_cap_def cap_aligned_def vs_cap_ref_def
                      split: option.splits vmpage_size.splits cap.splits)
      apply (simp add: cte_wp_at_caps_of_state)
      apply (wp unmap_page_invs hoare_vcg_ex_lift hoare_vcg_all_lift
                hoare_vcg_imp_lift unmap_page_unmapped)
   apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: is_arch_diminished_def)
   apply (drule (2) diminished_is_update')
   apply (clarsimp simp: is_cap_simps cap_master_cap_simps is_arch_update_def
                         update_map_data_def cap_rights_update_def
                         acap_rights_update_def)
   using valid_validate_vm_rights[simplified valid_vm_rights_def]
   apply (auto simp: valid_cap_def cap_aligned_def mask_def vs_cap_ref_def
                   split: vmpage_size.splits option.splits)[1]
  -- "PageFlush"
  apply (rule hoare_pre)
   apply (wp dmo_invs set_vm_root_for_flush_invs
             hoare_vcg_const_imp_lift hoare_vcg_all_lift
          | simp)+
    apply (rule hoare_pre_imp[of _ \<top>], assumption)
    apply (clarsimp simp: valid_def)
    apply (thin_tac "p \<in> fst (set_vm_root_for_flush a b s)" for p a b)
    apply(safe)
     apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
            in use_valid)
       apply ((clarsimp | wp)+)[3]
    apply(erule use_valid, wp no_irq_do_flush, assumption)
   apply(wp set_vm_root_for_flush_invs | simp add: valid_page_inv_def tcb_at_invs)+
  done

locale asid_pool_map =
  fixes s ap pool asid pdp pd s'
  defines "(s' :: ('a::state_ext) state) \<equiv>
           s\<lparr>kheap := kheap s(ap \<mapsto> ArchObj (Arch_Structs_A.ASIDPool
                                               (pool(asid \<mapsto> pdp))))\<rparr>"
  assumes ap:  "kheap s ap = Some (ArchObj (Arch_Structs_A.ASIDPool pool))"
  assumes new: "pool asid = None"
  assumes pd:  "kheap s pdp = Some (ArchObj (PageDirectory pd))"
  assumes pde: "empty_table (set (arm_global_pts (arch_state s)))
                            (ArchObj (PageDirectory pd))"
begin

definition 
  "new_lookups \<equiv>
   {((rs,p),(rs',p')). rs' = VSRef (ucast asid) (Some AASIDPool) # rs \<and>
                       p = ap \<and> p' = pdp}"

lemma vs_lookup1:
  "vs_lookup1 s' = vs_lookup1 s \<union> new_lookups"
  using pde pd new ap
  apply (clarsimp simp: vs_lookup1_def new_lookups_def)
  apply (rule set_eqI)
  apply (clarsimp simp: obj_at_def s'_def vs_refs_def graph_of_def)
  apply (rule iffI)
   apply (clarsimp simp: image_def split: split_if_asm)
   apply fastforce
  apply fastforce
  done

lemma vs_lookup_trans:
  "(vs_lookup1 s')^* = (vs_lookup1 s)^* \<union> (vs_lookup1 s)^* O new_lookups^*"
  using pd pde
  apply (simp add: vs_lookup1)
  apply (rule union_trans)
  apply (subst (asm) new_lookups_def)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def
                        empty_table_def pde_ref_def
                 split: split_if_asm)
  done

lemma arch_state [simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)

lemma new_lookups_rtrancl:
  "new_lookups^* = Id \<union> new_lookups"
  using ap pd
  apply -
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (erule rtrancl_induct2)
    apply clarsimp
   apply (clarsimp del: disjCI)
   apply (erule disjE)
    apply clarsimp
   apply (thin_tac "x \<in> R^*" for x R)
   apply (subgoal_tac "False", simp+)
   apply (clarsimp simp: new_lookups_def)
  apply (erule disjE, simp+)
  done

lemma vs_lookup:
  "vs_lookup s' = vs_lookup s \<union> new_lookups^* `` vs_lookup s"
  unfolding vs_lookup_def
  by (simp add: vs_lookup_trans rel_comp_Image Un_Image)

lemma vs_lookup2:
  "vs_lookup s' = vs_lookup s \<union> (new_lookups `` vs_lookup s)"
  by (auto simp add: vs_lookup new_lookups_rtrancl)

lemma vs_lookup_pages1:
  "vs_lookup_pages1 s' = vs_lookup_pages1 s \<union> new_lookups"
  using pde pd new ap
  apply (clarsimp simp: vs_lookup_pages1_def new_lookups_def)
  apply (rule set_eqI)
  apply (clarsimp simp: obj_at_def s'_def vs_refs_pages_def graph_of_def)
  apply (rule iffI)
   apply (clarsimp simp: image_def split: split_if_asm)
   apply fastforce
  apply fastforce
  done

lemma vs_lookup_pages_trans:
  "(vs_lookup_pages1 s')^* =
   (vs_lookup_pages1 s)^* \<union> (vs_lookup_pages1 s)^* O new_lookups^*"
  using pd pde
  apply (simp add: vs_lookup_pages1)
  apply (rule union_trans)
  apply (subst (asm) new_lookups_def)
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                        graph_of_def empty_table_def pde_ref_pages_def
                 split: split_if_asm)
  done

lemma vs_lookup_pages:
  "vs_lookup_pages s' =
   vs_lookup_pages s \<union> new_lookups^* `` vs_lookup_pages s"
  unfolding vs_lookup_pages_def
  by (simp add: vs_lookup_pages_trans rel_comp_Image Un_Image)

lemma vs_lookup_pages2:
  "vs_lookup_pages s' = vs_lookup_pages s \<union> (new_lookups `` vs_lookup_pages s)"
  by (auto simp add: vs_lookup_pages new_lookups_rtrancl)

end

lemma not_kernel_slot_not_global_pt: 
  "\<lbrakk>pde_ref (pd x) = Some p; x \<notin> kernel_mapping_slots;
    kheap s p' = Some (ArchObj (PageDirectory pd)); valid_kernel_mappings s\<rbrakk>
   \<Longrightarrow> p \<notin> set (arm_global_pts (arch_state s))"
  apply (clarsimp simp: valid_kernel_mappings_def valid_kernel_mappings_if_pd_def)
   apply (drule_tac x="ArchObj (PageDirectory pd)" in bspec)
    apply ((fastforce simp: ran_def)+)[1]
   apply (simp split: arch_kernel_obj.split_asm)
  done

lemma set_asid_pool_arch_objs_map:
  "\<lbrace>valid_arch_objs and valid_arch_state and valid_global_objs and
    valid_kernel_mappings and
    ko_at (ArchObj (Arch_Structs_A.ASIDPool pool)) ap and 
    K (pool asid = None) and
    \<exists>\<rhd> ap and page_directory_at pd and 
    (\<lambda>s. obj_at (empty_table (set (arm_global_pts (arch_state s)))) pd s) \<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. valid_arch_objs\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (frule (2) valid_arch_objsD)
  apply (clarsimp simp: valid_arch_objs_def simp del: valid_arch_obj.simps)
  apply (case_tac "p = ap")
   apply (clarsimp simp: obj_at_def
               simp del: fun_upd_apply valid_arch_obj.simps)
   apply (clarsimp simp: ran_def)
   apply (case_tac "a = asid")
    apply clarsimp
    apply (rule typ_at_same_type)
      apply (simp add: obj_at_def a_type_simps)
     prefer 2
     apply assumption
    apply (simp add: a_type_def)
   apply clarsimp
   apply (erule allE, erule impE, rule exI, assumption)+
   apply (erule typ_at_same_type)
    prefer 2
    apply assumption
   apply (simp add: a_type_def)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (frule (3) asid_pool_map.intro)
  apply (subst (asm) asid_pool_map.vs_lookup, assumption)
  apply clarsimp
  apply (erule disjE)
   apply (erule_tac x=p in allE, simp)
   apply (erule impE, blast)
   apply (erule valid_arch_obj_same_type)
    apply (simp add: obj_at_def a_type_def)
   apply (simp add: a_type_def)
  apply (clarsimp simp: asid_pool_map.new_lookups_rtrancl)
  apply (erule disjE)
   apply clarsimp
   apply (erule_tac x=p in allE, simp)
   apply (erule impE, blast)
   apply (erule valid_arch_obj_same_type)
    apply (simp add: obj_at_def a_type_def)
   apply (simp add: a_type_def)
  apply (clarsimp simp: asid_pool_map.new_lookups_def empty_table_def)
  done

lemma obj_at_not_pt_not_in_global_pts:
  "\<lbrakk> obj_at P p s; valid_arch_state s; valid_global_objs s; \<And>pt. \<not> P (ArchObj (PageTable pt)) \<rbrakk>
          \<Longrightarrow> p \<notin> set (arm_global_pts (arch_state s))"
  apply (rule notI, drule(1) valid_global_ptsD)
  apply (clarsimp simp: obj_at_def)
  done

lemma set_asid_pool_valid_arch_caps_map:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_global_objs and valid_objs
    and valid_arch_objs and ko_at (ArchObj (Arch_Structs_A.ASIDPool pool)) ap
    and (\<lambda>s. \<exists>rf. (rf \<rhd> ap) s \<and> (\<exists>ptr cap. caps_of_state s ptr = Some cap
                                   \<and> pd \<in> obj_refs cap \<and> vs_cap_ref cap = Some ((VSRef (ucast asid) (Some AASIDPool)) # rf))
                              \<and> (VSRef (ucast asid) (Some AASIDPool) # rf \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None]))
    and page_directory_at pd 
    and (\<lambda>s. obj_at (empty_table (set (arm_global_pts (arch_state s)))) pd s) 
    and K (pool asid = None)\<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (frule obj_at_not_pt_not_in_global_pts[where p=pd], clarsimp+)
   apply (simp add: a_type_def)
  apply (frule obj_at_not_pt_not_in_global_pts[where p=ap], clarsimp+)
  apply (clarsimp simp: obj_at_def valid_arch_caps_def
                        caps_of_state_after_update)
  apply (clarsimp simp: a_type_def
                 split: Structures_A.kernel_object.split_asm split_if_asm
                        arch_kernel_obj.split_asm)
  apply (frule(3) asid_pool_map.intro)
  apply (simp add: fun_upd_def[symmetric])
  apply (rule conjI)
   apply (simp add: valid_vs_lookup_def
                    caps_of_state_after_update[folded fun_upd_def]
                    obj_at_def)
   apply (subst asid_pool_map.vs_lookup_pages2, assumption)
   apply simp
   apply (clarsimp simp: asid_pool_map.new_lookups_def)
   apply (frule(2) vs_lookup_vs_lookup_pagesI, simp add: valid_arch_state_def)
   apply (drule(2) ref_is_unique)
        apply (simp add: valid_vs_lookup_def)
       apply clarsimp+
     apply (simp add: valid_arch_state_def)
    apply (rule valid_objs_caps, simp)
   apply fastforce
  apply (simp add: valid_table_caps_def
                   caps_of_state_after_update[folded fun_upd_def] obj_at_def
              del: imp_disjL)
  apply (clarsimp simp del: imp_disjL)
  apply (drule(1) caps_of_state_valid_cap)+
  apply (auto simp add: valid_cap_def is_pt_cap_def is_pd_cap_def obj_at_def
                        a_type_def)[1]
  done

lemma set_asid_pool_asid_map:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (Arch_Structs_A.ASIDPool pool)) ap    
    and K (pool asid = None)\<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: pd_at_asid_def)
  apply (drule vs_lookup_2ConsD)
  apply clarsimp
  apply (erule vs_lookup_atE)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (case_tac "p'=ap")
   apply (clarsimp simp: obj_at_def)
   apply (rule vs_lookupI)
    apply (clarsimp simp: vs_asid_refs_def graph_of_def)
    apply fastforce
   apply (rule r_into_rtrancl)
   apply (rule_tac r="VSRef (a && mask asid_low_bits) (Some AASIDPool)" in vs_lookup1I) 
     apply (simp add: obj_at_def)
    apply (simp add: vs_refs_def graph_of_def)
    apply fastforce
   apply simp
  apply (rule vs_lookupI)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def)
   apply fastforce
  apply (rule r_into_rtrancl)
  apply (rule vs_lookup1I)
    apply (simp add: obj_at_def)
   apply simp
  apply simp
  done

lemma set_asid_pool_invs_map:
  "\<lbrace>invs and ko_at (ArchObj (Arch_Structs_A.ASIDPool pool)) ap 
    and (\<lambda>s. \<exists>rf. (rf \<rhd> ap) s \<and> (\<exists>ptr cap. caps_of_state s ptr = Some cap
                                  \<and> pd \<in> obj_refs cap \<and> vs_cap_ref cap = Some ((VSRef (ucast asid) (Some AASIDPool)) # rf))
                              \<and> (VSRef (ucast asid) (Some AASIDPool) # rf \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None]))
    and page_directory_at pd 
    and (\<lambda>s. obj_at (empty_table (set (arm_global_pts (arch_state s)))) pd s) 
    and K (pool asid = None)\<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre, wp valid_irq_node_typ set_asid_pool_typ_at set_asid_pool_arch_objs_map valid_irq_handlers_lift
                            set_asid_pool_valid_arch_caps_map set_asid_pool_asid_map)
  apply clarsimp
  apply auto
  done

lemma perform_asid_pool_invs [wp]:
  "\<lbrace>invs and valid_apinv api\<rbrace> perform_asid_pool_invocation api \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: perform_asid_pool_invocation_def split: asid_pool_invocation.splits)
  apply (wp arch_update_cap_invs_map set_asid_pool_invs_map 
            get_cap_wp set_cap_typ_at empty_table_lift
            set_cap_obj_at_other
               |wpc|simp|wp_once hoare_vcg_ex_lift)+
  apply (clarsimp simp: valid_apinv_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps cap_master_cap_simps)
  apply (frule caps_of_state_cteD)
  apply (drule cte_wp_valid_cap, fastforce)
  apply (simp add: valid_cap_def cap_aligned_def)
  apply (clarsimp simp: cap_asid_def split: option.splits)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
  apply clarsimp
  apply (rule conjI)
   apply (erule vs_lookup_atE)
   apply clarsimp
   apply (drule caps_of_state_cteD)
   apply (clarsimp simp: cte_wp_at_cases obj_at_def)
  apply (rule conjI)
   apply (rule exI)
   apply (rule conjI, assumption)
   apply (rule conjI)
    apply (rule_tac x=a in exI)
    apply (rule_tac x=b in exI)
    apply (clarsimp simp: vs_cap_ref_def mask_asid_low_bits_ucast_ucast)
   apply (clarsimp simp: asid_low_bits_def[symmetric] ucast_ucast_mask
                         word_neq_0_conv[symmetric])
   apply (erule notE, rule asid_low_high_bits, simp_all)[1]
   apply (simp add: asid_high_bits_of_def)
  apply (rule conjI)
   apply (erule(1) valid_table_caps_pdD [OF _ invs_pd_caps])
  apply (rule conjI)
   apply clarsimp
   apply (drule caps_of_state_cteD)
   apply (clarsimp simp: obj_at_def cte_wp_at_cases a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done

lemma invs_aligned_pdD:
  "\<lbrakk> pspace_aligned s; valid_arch_state s \<rbrakk> \<Longrightarrow> is_aligned (arm_global_pd (arch_state s)) pd_bits"
  apply (clarsimp simp: valid_arch_state_def)
  apply (drule (1) pd_aligned)
  apply (simp add: pd_bits_def pageBits_def)
  done

end
