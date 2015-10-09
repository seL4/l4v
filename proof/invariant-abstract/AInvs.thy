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
The main theorem
*)

theory AInvs
imports PDPTEntries_AI ADT_AI
begin

lemma st_tcb_at_nostate_upd:
  "\<lbrakk> get_tcb t s = Some y; tcb_state y = tcb_state y' \<rbrakk> \<Longrightarrow>
  st_tcb_at P t' (s \<lparr>kheap := kheap s(t \<mapsto> TCB y')\<rparr>) = st_tcb_at P t' s"
  by (clarsimp simp add: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma pred_tcb_at_upd_apply:
  "pred_tcb_at proj P t (s\<lparr>kheap := p'\<rparr>) =
  pred_tcb_at proj P t (s\<lparr>kheap := (kheap s)(t := p' t)\<rparr>)"
  by (simp add: pred_tcb_at_def obj_at_def)


text {* The top-level invariance *}

lemma akernel_invs:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
  (call_kernel e) :: (unit,unit) s_monad
  \<lbrace>\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>"
  apply wp
   apply (simp add: call_kernel_def)
   apply (wp activate_invs | simp add: invs_irq_state_independent)+
   apply (auto simp: active_from_running)
  done

lemma akernel_invs_det_ext:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
  (call_kernel e) :: (unit,det_ext) s_monad
  \<lbrace>\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>"
  apply wp
   apply (simp add: call_kernel_def)
   apply (wp activate_invs | simp add: invs_irq_state_independent)+
   apply (auto simp: active_from_running)
  done

(* FIXME: move *)
lemma ct_running_machine_op:
  "\<lbrace>ct_running\<rbrace> do_machine_op f \<lbrace>\<lambda>_. ct_running\<rbrace>"
  apply (simp add: ct_in_state_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_lift_Pf [where f=cur_thread])
  by wp

lemma kernel_entry_invs:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
  (kernel_entry e us) :: (register \<Rightarrow> 32 word,unit) s_monad
  \<lbrace>\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>"
  apply (simp add: kernel_entry_def)
  by (wp akernel_invs thread_set_invs_trivial thread_set_ct_running select_wp
         ct_running_machine_op static_imp_wp
      | clarsimp simp add: tcb_cap_cases_def)+


(* FIXME: move to Lib.thy *)
lemma Collect_subseteq:
  "{x. P x} <= {x. Q x} \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q x)"
  by auto

definition
  "kernel_mappings \<equiv> {x. x \<ge> kernel_base}"

lemma kernel_mappings_slots_eq:
  "p \<in> kernel_mappings \<longleftrightarrow> ucast (p >> 20) \<in> kernel_mapping_slots"
  apply (simp add: kernel_mappings_def kernel_mapping_slots_def word_le_nat_alt
                   shiftr_20_unat_ucast unat_ucast_kernel_base_rshift)
  apply (fold word_le_nat_alt)
  apply (rule iffI)
   apply (simp add: le_shiftr)
  apply (simp add: kernel_base_def)
  apply word_bitwise
  done

lemma valid_global_pd_mappingsE:
  "\<lbrakk>valid_global_pd_mappings s;
    \<And>pd. \<lbrakk>kheap s (arm_global_pd (arch_state s)) =
             Some (ArchObj (PageDirectory pd));
           \<forall>x. valid_pd_kernel_mappings (arm_kernel_vspace (arch_state s)) s
                 (ArchObj (PageDirectory pd))\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  apply (clarsimp simp add: valid_global_pd_mappings_def obj_at_def)
  apply (case_tac ko, simp_all add: valid_pd_kernel_mappings_def
                             split: arch_kernel_obj.splits)
  done

(* NOTE: we could probably add "is_aligned b (pageBitsForSize sz)"
         if we assumed "valid_global_objs s", additionally. *)
lemma some_get_page_info_kmapsD:
  "\<lbrakk>get_page_info (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ref p = Some (b, a, attr, r);
    p \<in> kernel_mappings; valid_global_pd_mappings s; equal_kernel_mappings s\<rbrakk>
   \<Longrightarrow> (\<exists>sz. pageBitsForSize sz = a) \<and> r = {}"
   apply (clarsimp simp: get_page_info_def get_pd_entry_def get_arch_obj_def
                         kernel_mappings_slots_eq
                  split: option.splits Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
   apply (erule valid_global_pd_mappingsE)
   apply (clarsimp simp: equal_kernel_mappings_def obj_at_def)
   apply (drule_tac x=pd_ref in spec,
          drule_tac x="arm_global_pd (arch_state s)" in spec, simp)
   apply (drule bspec, assumption)
   apply (clarsimp simp: valid_pd_kernel_mappings_def pde_mapping_bits_def)
   apply (drule_tac x="ucast (p >> 20)" in spec)
   apply (clarsimp simp: get_page_info_def get_pd_entry_def get_arch_obj_def
                         get_pt_info_def get_pt_entry_def
                         kernel_mappings_slots_eq
                  split: option.splits Structures_A.kernel_object.splits
                         arch_kernel_obj.splits
                         ARM_Structs_A.pde.splits ARM_Structs_A.pte.splits)
      apply (rule conjI, rule_tac x=ARMLargePage in exI, simp)
      apply (simp add: valid_pde_kernel_mappings_def obj_at_def
                       valid_pt_kernel_mappings_def)
      apply (drule_tac x="ucast ((p >> 12) && mask 8)" in spec)
      apply (clarsimp simp: valid_pte_kernel_mappings_def)
     apply (rule conjI, rule_tac x=ARMSmallPage in exI, simp)
     apply (simp add: valid_pde_kernel_mappings_def obj_at_def
                      valid_pt_kernel_mappings_def)
     apply (drule_tac x="ucast ((p >> 12) && mask 8)" in spec)
     apply (clarsimp simp: valid_pte_kernel_mappings_def)
    apply (rule conjI, rule_tac x=ARMSection in exI, simp)
    apply (simp add: valid_pde_kernel_mappings_def)
   apply (rule conjI, rule_tac x=ARMSuperSection in exI, simp)
   apply (simp add: valid_pde_kernel_mappings_def)
   done

lemma get_page_info_gpd_kmaps:
  "\<lbrakk>valid_global_objs s; valid_arch_state s;
    get_page_info (\<lambda>obj. get_arch_obj (kheap s obj))
                  (arm_global_pd (arch_state s)) p = Some (b, a, attr, r)\<rbrakk>
   \<Longrightarrow> p \<in> kernel_mappings"
   apply (clarsimp simp: valid_global_objs_def valid_arch_state_def)
   apply (thin_tac "Ball x y" for x y)
   apply (thin_tac "typ_at data gframe s" for data gframe)
   apply (clarsimp simp add: obj_at_def valid_ao_at_def)
   apply (clarsimp simp: empty_table_def kernel_mappings_slots_eq)
   apply (drule_tac x="ucast (p >> 20)" in spec)
   apply (rule ccontr, simp)
   apply (clarsimp simp: get_page_info_def get_pd_entry_def get_arch_obj_def
                  split: option.splits arch_kernel_obj.splits)
   done

lemma get_pd_of_thread_reachable:
  "get_pd_of_thread (kheap s) (arch_state s) t \<noteq> arm_global_pd (arch_state s)
   \<Longrightarrow> (\<exists>\<rhd> get_pd_of_thread (kheap s) (arch_state s) t) s"
  by (auto simp: get_pd_of_thread_vs_lookup
          split: Structures_A.kernel_object.splits split_if_asm option.splits
                 cap.splits arch_cap.splits)

lemma is_aligned_ptrFromPAddrD:
"\<lbrakk>is_aligned (Platform.ptrFromPAddr b) a; a \<le> 24\<rbrakk> \<Longrightarrow> is_aligned b a"
  apply (clarsimp simp:Platform.ptrFromPAddr_def physMappingOffset_def kernelBase_addr_def physBase_def)
  apply (erule is_aligned_addD2)
  apply (rule is_aligned_weaken[where x = 24])
   apply (simp add:is_aligned_def)
  apply simp
  done

lemma some_get_page_info_umapsD:
  "\<lbrakk>get_page_info (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ref p = Some (b, a, attr, r);
    (\<exists>\<rhd> pd_ref) s; p \<notin> kernel_mappings; valid_arch_objs s; pspace_aligned s;
    valid_asid_table (arm_asid_table (arch_state s)) s; valid_objs s\<rbrakk>
   \<Longrightarrow> (\<exists>sz. pageBitsForSize sz = a \<and> is_aligned b a \<and>
             typ_at (AArch (AIntData sz)) (Platform.ptrFromPAddr b) s)"
  apply (clarsimp simp: get_page_info_def get_pd_entry_def get_arch_obj_def
                        kernel_mappings_slots_eq
                 split: option.splits Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (frule (1) valid_arch_objsD[rotated 2])
   apply (simp add: obj_at_def)
  apply (simp add: valid_arch_obj_def)
  apply (drule bspec, simp)
  apply (simp split: ARM_Structs_A.pde.splits)
     apply (rename_tac rs pd pt_ref rights w)
     apply (subgoal_tac
        "((rs, pd_ref) \<rhd>1
          (VSRef (ucast (ucast (p >> 20))) (Some APageDirectory) # rs,
           Platform.ptrFromPAddr pt_ref)) s")
     prefer 2
     apply (rule vs_lookup1I[rotated 2], simp)
      apply (simp add: obj_at_def)
     apply (simp add: vs_refs_def pde_ref_def image_def graph_of_def)
     apply (rule exI, rule conjI, simp+)
    apply (frule (1) vs_lookup_step)
    apply (drule (2) stronger_arch_objsD[where ref="x # xs" for x xs])
    apply clarsimp
    apply (case_tac ao, simp_all add: a_type_simps obj_at_def)[1]
    apply (simp add: get_pt_info_def get_pt_entry_def)
    apply (drule_tac x="(ucast ((p >> 12) && mask 8))" in spec)
    apply (clarsimp simp: obj_at_def valid_arch_obj_def
      split: ARM_Structs_A.pte.splits)
     apply (clarsimp simp: pspace_aligned_def)
     apply (drule_tac x = "(Platform.ptrFromPAddr b)" in  bspec, fastforce)
     apply (drule is_aligned_ptrFromPAddrD)
      apply simp
     apply (clarsimp simp:a_type_simps)
    apply (clarsimp simp: pspace_aligned_def)
    apply (drule_tac x = "(Platform.ptrFromPAddr b)" in  bspec, fastforce)
    apply (drule is_aligned_ptrFromPAddrD)
     apply simp
    apply (clarsimp simp:a_type_simps)
   apply (clarsimp simp: pspace_aligned_def obj_at_def)
   apply (drule_tac x = "(Platform.ptrFromPAddr b)" in  bspec, fastforce)
   apply (drule is_aligned_ptrFromPAddrD)
    apply simp
   apply (clarsimp simp:a_type_simps)
  apply (clarsimp simp: pspace_aligned_def obj_at_def)
  apply (drule_tac x = "(Platform.ptrFromPAddr b)" in  bspec, fastforce)
  apply (drule is_aligned_ptrFromPAddrD)
   apply simp
   apply (clarsimp simp:a_type_simps)
  done

lemma ptable_rights_imp_user_frame:
  assumes "valid_state s"
  shows "ptable_rights t s x \<noteq> {} \<Longrightarrow>
         ptable_lift t s x = Some (Platform.addrFromPPtr y) \<Longrightarrow>
         in_user_frame y s"
  apply (clarsimp simp: ptable_rights_def ptable_lift_def in_user_frame_def
                 split: option.splits)
  apply (rename_tac b a r)
  apply (case_tac "x \<in> kernel_mappings")
   apply (frule (1) some_get_page_info_kmapsD)
     using assms
     apply (clarsimp simp add: valid_state_def)
    using assms
    apply (clarsimp simp add: valid_state_def)
   apply simp
  apply (frule some_get_page_info_umapsD)
       apply (rule get_pd_of_thread_reachable)
       apply clarsimp
       apply (frule get_page_info_gpd_kmaps[rotated 2])
          using assms
          apply (simp_all add: valid_state_def valid_pspace_def
                               valid_arch_state_def)
  apply clarsimp
  apply (frule is_aligned_add_helper[OF _ and_mask_less',
                                     THEN conjunct2, of _ _ x])
   apply (simp only: pbfs_less_wb'[simplified word_bits_def])
  apply (clarsimp simp: Platform.ptrFromPAddr_def Platform.addrFromPPtr_def
                        field_simps)
  apply (rule_tac x=sz in exI)
  apply (subst add.assoc[symmetric])
  apply (subst is_aligned_add_helper)
    apply (erule aligned_add_aligned)
      apply (case_tac sz, simp_all add: physMappingOffset_def
                            kernelBase_addr_def physBase_def is_aligned_def)[1]
     apply (case_tac sz, simp_all add: word_bits_conv)[1]
   apply (rule and_mask_less')
   apply (case_tac sz, simp_all add: word_bits_conv)[1]
  apply simp
  done

lemma do_user_op_invs:
  "\<lbrace>invs and ct_running\<rbrace>
   do_user_op f tc
   \<lbrace>\<lambda>_. invs and ct_running\<rbrace>"
  apply (simp add: do_user_op_def split_def)
  apply (wp ct_running_machine_op select_wp dmo_invs)
  apply (auto simp: user_mem_def user_memory_update_def simpler_modify_def
                    restrict_map_def invs_def cur_tcb_def
             elim!: ptable_rights_imp_user_frame
             split: option.splits split_if_asm)
  done

end
