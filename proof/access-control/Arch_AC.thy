(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_AC
imports Retype_AC
begin

context begin interpretation Arch . (*FIXME: arch_split*)

text\<open>

Arch-specific access control.

\<close>

lemma store_pde_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag (p && ~~ mask pd_bits)) \<rbrace>
     store_pde p pde
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: store_pde_def set_pd_def)
  apply (wp get_object_wp set_object_integrity_autarch)
  apply simp
  done

lemma store_pte_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag (p && ~~ mask pt_bits)) \<rbrace>
     store_pte p pte
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp set_object_integrity_autarch)
  apply simp
  done

lemma integrity_arch_state [iff]:
  "\<lbrakk>arm_asid_table v = arm_asid_table (arch_state s)\<rbrakk> \<Longrightarrow>
   integrity aag X st (s\<lparr>arch_state := v\<rparr>) = integrity aag X st s"
  unfolding integrity_def
  by (simp )

lemma integrity_arm_asid_map [iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>arm_asid_map := v\<rparr>)\<rparr>) = integrity aag X st s"
  unfolding integrity_def
  by (simp )

lemma integrity_arm_hwasid_table [iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>arm_hwasid_table := v\<rparr>)\<rparr>) = integrity aag X st s"
  unfolding integrity_def
  by (simp )

lemma integrity_arm_next_asid [iff]:
  "integrity aag X st (s\<lparr>arch_state := ((arch_state s)\<lparr>arm_next_asid := v\<rparr>)\<rparr>) = integrity aag X st s"
  unfolding integrity_def
  by (simp )

declare dmo_mol_respects [wp]

crunch respects[wp]: arm_context_switch "integrity X aag st"
  (simp: dmo_bind_valid dsb_def isb_def writeTTBR0_def invalidateLocalTLB_ASID_def
         setHardwareASID_def set_current_pd_def
 ignore: do_machine_op)

crunch respects[wp]: set_vm_root "integrity X aag st"
    (wp: crunch_wps
   simp: set_current_pd_def isb_def dsb_def writeTTBR0_def dmo_bind_valid crunch_simps
 ignore: do_machine_op)

crunch respects[wp]: set_vm_root_for_flush "integrity X aag st"
  (wp: crunch_wps simp: set_current_pd_def crunch_simps ignore: do_machine_op)

crunch respects[wp]: flush_table "integrity X aag st"
  (wp: crunch_wps simp: invalidateLocalTLB_ASID_def crunch_simps ignore: do_machine_op)

crunch respects[wp]: page_table_mapped "integrity X aag st"

lemma kheap_eq_state_vrefsD:
  "kheap s p = Some ko \<Longrightarrow> state_vrefs s p = vs_refs_no_global_pts ko"
  by (simp add: state_vrefs_def)

lemma kheap_eq_state_vrefs_pas_refinedD:
  "\<lbrakk> kheap s p = Some ko;
       (p', r, t, a) \<in> vs_refs_no_global_pts ko; pas_refined aag s \<rbrakk>
    \<Longrightarrow> (pasObjectAbs aag p, a, pasObjectAbs aag p') \<in> pasPolicy aag"
  apply (drule kheap_eq_state_vrefsD)
  apply (erule pas_refined_mem[OF sta_vref, rotated])
  apply simp
  done

lemma find_pd_for_asid_authority1:
  "\<lbrace>pas_refined aag\<rbrace>
      find_pd_for_asid asid
   \<lbrace>\<lambda>pd s. (pasASIDAbs aag asid, Control, pasObjectAbs aag pd) \<in> pasPolicy aag\<rbrace>,-"
  apply (rule hoare_pre)
   apply (simp add: find_pd_for_asid_def)
   apply (wp | wpc)+
  apply (clarsimp simp: obj_at_def pas_refined_def)
  apply (erule subsetD, erule sata_asid_lookup)
  apply (simp add: state_vrefs_def vs_refs_no_global_pts_def image_def)
  apply (rule rev_bexI, erule graph_ofI)
  apply (simp add: mask_asid_low_bits_ucast_ucast)
  done

lemma find_pd_for_asid_authority2:
  "\<lbrace>\<lambda>s. \<forall>pd. (\<forall>aag. pas_refined aag s \<longrightarrow> (pasASIDAbs aag asid, Control, pasObjectAbs aag pd) \<in> pasPolicy aag)
           \<and> (pspace_aligned s \<and> valid_vspace_objs s \<longrightarrow> is_aligned pd pd_bits)
           \<and> (\<exists>\<rhd> pd) s
           \<longrightarrow> Q pd s\<rbrace> find_pd_for_asid asid \<lbrace>Q\<rbrace>, -"
  (is "\<lbrace>?P\<rbrace> ?f \<lbrace>Q\<rbrace>,-")
  apply (clarsimp simp: validE_R_def validE_def valid_def imp_conjL[symmetric])
  apply (frule in_inv_by_hoareD[OF find_pd_for_asid_inv], clarsimp)
  apply (drule spec, erule mp)
  apply (simp add: use_validE_R[OF _ find_pd_for_asid_authority1]
                   use_validE_R[OF _ find_pd_for_asid_aligned_pd_bits]
                   use_validE_R[OF _ find_pd_for_asid_lookup])
  done

lemma find_pd_for_asid_pd_slot_authorised [wp]:
  "\<lbrace>pas_refined aag and K (is_subject_asid aag asid) and pspace_aligned and valid_vspace_objs\<rbrace>
  find_pd_for_asid asid
  \<lbrace>\<lambda>rv s. is_subject aag (lookup_pd_slot rv vptr && ~~ mask pd_bits) \<rbrace>, -"
  apply (wp find_pd_for_asid_authority2)
  apply (clarsimp simp: lookup_pd_slot_pd)
  apply (fastforce dest: pas_refined_Control)
  done

lemma unmap_page_table_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs
         and K (is_subject_asid aag asid \<and> vaddr < kernel_base)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_page_table_def page_table_mapped_def )
  apply (rule hoare_pre)
   apply (wp store_pde_respects page_table_mapped_wp_weak get_pde_wp
             hoare_vcg_all_lift_R dmo_mol_respects
        | wpc
        | simp add: cleanByVA_PoU_def
        | wp (once) hoare_drop_imps)+
  apply auto
  done

definition
  authorised_page_table_inv :: "'a PAS \<Rightarrow> page_table_invocation \<Rightarrow> bool"
where
  "authorised_page_table_inv aag pti \<equiv> case pti of
     page_table_invocation.PageTableMap cap cslot_ptr pde obj_ref \<Rightarrow>
         is_subject aag (fst cslot_ptr) \<and> is_subject aag (obj_ref && ~~ mask pd_bits)
       \<and> (case_option True (is_subject aag o fst) (pde_ref2 pde))
       \<and> pas_cap_cur_auth aag cap
   | page_table_invocation.PageTableUnmap cap cslot_ptr \<Rightarrow>
       is_subject aag (fst cslot_ptr) \<and> aag_cap_auth aag (pasSubject aag) cap
         \<and> (\<forall>p asid vspace_ref. cap = cap.ArchObjectCap (arch_cap.PageTableCap p (Some (asid, vspace_ref)))
                \<longrightarrow> is_subject_asid aag asid
                \<and> (\<forall>x \<in> set [p , p + 4 .e. p + 2 ^ pt_bits - 1]. is_subject aag (x && ~~ mask pt_bits)))"

lemma perform_page_table_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs
          and valid_pti page_table_invocation
          and K (authorised_page_table_inv aag page_table_invocation)\<rbrace>
     perform_page_table_invocation page_table_invocation
   \<lbrace>\<lambda>s. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: perform_page_table_invocation_def
             cong: page_table_invocation.case_cong option.case_cong prod.case_cong
                   cap.case_cong arch_cap.case_cong)
  apply (rule hoare_pre)
  apply (wp store_pde_respects set_cap_integrity_autarch store_pte_respects unmap_page_table_respects mapM_wp'
       | wpc
       | simp add: mapM_x_mapM authorised_page_table_inv_def cleanByVA_PoU_def)+
  apply (auto simp: valid_pti_def valid_cap_simps)
  done

crunch arm_asid_table_inv [wp]: unmap_page_table "\<lambda>s. P (arm_asid_table (arch_state s))"
 (wp: crunch_wps simp: crunch_simps)

lemma clas_update_map_data_strg:
  "(is_pg_cap cap \<or> is_pt_cap cap) \<longrightarrow> cap_links_asid_slot aag p (cap.ArchObjectCap (update_map_data (the_arch_cap cap) None))"
  unfolding cap_links_asid_slot_def
  by (fastforce simp: is_cap_simps update_map_data_def)

lemmas pte_ref_simps = pte_ref_def[split_simps pte.split]

lemmas store_pde_pas_refined_simple
    = store_pde_pas_refined[where pde=InvalidPDE, simplified pde_ref_simps, simplified]

crunch pas_refined[wp]: unmap_page_table "pas_refined aag"
  (wp: crunch_wps store_pde_pas_refined_simple
      simp: crunch_simps pde_ref_simps)

lemma pde_ref_pde_ref2:
  "\<lbrakk> pde_ref x = Some v; pde_ref2 x = Some v' \<rbrakk> \<Longrightarrow> v' = (v, 0, {Control})"
  unfolding pde_ref_def pde_ref2_def
  by (cases x, simp_all)

lemma ptr_range_0 [simp]: "ptr_range (p :: word32) 0 = {p}"
  unfolding ptr_range_def by simp

lemma mask_PTCap_eq:
  "(ArchObjectCap (PageTableCap a b) = mask_cap R cap) = (cap = ArchObjectCap (PageTableCap a b))"
  by (auto simp: mask_cap_def cap_rights_update_def acap_rights_update_def
           split: arch_cap.splits cap.splits bool.splits)


(* FIXME MOVE *)
crunch cdt[wp]: unmap_page_table "\<lambda>s. P (cdt s)"
  (simp: crunch_simps wp: crunch_wps)

(* FIXME MOVE *)
lemma is_transferable_ArchCap[simp]:
  "\<not> is_transferable
        (Some (ArchObjectCap cap))"
  using is_transferable.simps by simp



lemma is_transferable_is_arch_update:
  "is_arch_update cap cap' \<Longrightarrow> is_transferable (Some cap) = is_transferable (Some cap')"
  using is_transferable.simps is_arch_cap_def is_arch_update_def cap_master_cap_def
  by (simp split: cap.splits arch_cap.splits)

lemma perform_page_table_invocation_pas_refined [wp]:
  "\<lbrace> pas_refined aag and valid_pti page_table_invocation
     and K (authorised_page_table_inv aag page_table_invocation)\<rbrace>
     perform_page_table_invocation page_table_invocation
   \<lbrace>\<lambda>s. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: perform_page_table_invocation_def
             cong: page_table_invocation.case_cong option.case_cong prod.case_cong
                   cap.case_cong arch_cap.case_cong)
  apply (rule hoare_pre)
  apply (wp get_cap_wp mapM_wp' store_pte_cte_wp_at do_machine_op_cte_wp_at
            hoare_vcg_all_lift set_cap_pas_refined_not_transferable
        | (wp hoare_vcg_imp_lift, unfold disj_not1)
        | wpc
        | simp add: mapM_x_mapM authorised_page_table_inv_def imp_conjR
                    pte_ref_simps
        | wps
        | blast)+
  apply (cases page_table_invocation)
   apply (fastforce simp: cte_wp_at_caps_of_state Option.is_none_def
                          is_transferable_is_arch_update[symmetric]
                          valid_pti_def is_cap_simps pas_refined_refl auth_graph_map_def2
                    dest: pde_ref_pde_ref2)
  apply (rename_tac s pt_cap page_cslot)
  apply (case_tac page_cslot)
  apply (rename_tac page_ptr page_slot)
  apply (case_tac "\<exists>pt_ptr mapping. pt_cap = ArchObjectCap (PageTableCap pt_ptr mapping)")
   prefer 2
   apply fastforce
  apply (elim exE)
  apply clarsimp
  apply (rename_tac page_cap)
  apply (subgoal_tac
            "cte_wp_at ((=) page_cap) (page_ptr, page_slot) s \<longrightarrow>
             cte_wp_at (\<lambda>c. \<not> is_transferable (Some c)) (page_ptr, page_slot) s \<and>
             pas_cap_cur_auth aag
                (cap.ArchObjectCap (update_map_data (the_arch_cap page_cap) None))")
   apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule (1) cap_cur_auth_caps_of_state)
   apply simp
  apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state mask_PTCap_eq)
  apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def update_map_data_def
                        is_page_cap_def cap_links_asid_slot_def cap_links_irq_def aag_cap_auth_def)
  done

definition
  authorised_slots :: "'a PAS \<Rightarrow> pte \<times> (obj_ref list) + pde \<times> (obj_ref list) \<Rightarrow> bool"
where
 "authorised_slots aag m \<equiv> case m of
    Inl (pte, slots) \<Rightarrow> (\<forall>x. pte_ref pte = Some x \<longrightarrow> (\<forall>a \<in> (snd (snd x)). \<forall>p \<in> ptr_range (fst x) (fst (snd x)).(aag_has_auth_to aag a p)))
           \<and> (\<forall>x \<in> set slots. is_subject aag (x && ~~ mask pt_bits))
  | Inr (pde, slots) \<Rightarrow> (\<forall>x. pde_ref2 pde = Some x \<longrightarrow> (\<forall>a \<in> (snd (snd x)). \<forall>p \<in> ptr_range (fst x) (fst (snd x)). (aag_has_auth_to aag a p)))
           \<and> (\<forall>x \<in> set slots. is_subject aag (x && ~~ mask pd_bits))"

definition
  authorised_page_inv :: "'a PAS \<Rightarrow> page_invocation \<Rightarrow> bool"
where
  "authorised_page_inv aag pgi \<equiv> case pgi of
     PageMap asid cap ptr slots \<Rightarrow>
       pas_cap_cur_auth aag cap \<and> is_subject aag (fst ptr) \<and> authorised_slots aag slots
   | PageUnmap cap ptr \<Rightarrow> pas_cap_cur_auth aag (Structures_A.ArchObjectCap cap) \<and> is_subject aag (fst ptr)
   | PageFlush typ start end pstart pd asid \<Rightarrow> True
   | PageGetAddr ptr \<Rightarrow> True"

crunch respects[wp]: lookup_pt_slot "integrity X aag st"

lemma ptrFromPAddr_inj: "inj ptrFromPAddr"
  by (auto intro: injI simp: ptrFromPAddr_def)

lemma vs_refs_no_global_pts_pdI:
  "\<lbrakk>pd (ucast r) = PageTablePDE x a b;
    ((ucast r)::12 word) < ucast (kernel_base >> 20) \<rbrakk> \<Longrightarrow>
        (ptrFromPAddr x, r && mask 12, APageDirectory, Control)
          \<in> vs_refs_no_global_pts (ArchObj (PageDirectory pd))"
  apply(clarsimp simp: vs_refs_no_global_pts_def)
  apply (drule_tac f=pde_ref2 in arg_cong, simp add: pde_ref_simps o_def)
  apply (rule rev_bexI, rule DiffI, erule graph_ofI)
   apply simp
  apply (clarsimp simp: ucast_ucast_mask )
  done

lemma aag_has_auth_to_Control_eq_owns:
  "pas_refined aag s \<Longrightarrow> aag_has_auth_to aag Control p = is_subject aag p"
  by (auto simp: pas_refined_refl elim: aag_Control_into_owns)

lemma lookup_pt_slot_authorised:
  "\<lbrace>\<exists>\<rhd> pd and valid_vspace_objs and pspace_aligned and pas_refined aag
            and K (is_subject aag pd) and K (is_aligned pd 14 \<and> vptr < kernel_base)\<rbrace>
    lookup_pt_slot pd vptr
  \<lbrace>\<lambda>rv s. is_subject aag (rv && ~~ mask pt_bits)\<rbrace>, -"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp | wpc)+
  apply (subgoal_tac "is_aligned pd pd_bits")
   apply (clarsimp simp: lookup_pd_slot_pd)
   apply (drule(2) valid_vspace_objsD)
   apply (clarsimp simp: obj_at_def)
   apply (drule kheap_eq_state_vrefs_pas_refinedD)
     apply (erule vs_refs_no_global_pts_pdI)
     apply (drule(1) less_kernel_base_mapping_slots)
     apply (simp add: kernel_mapping_slots_def)
    apply assumption
   apply (simp add: aag_has_auth_to_Control_eq_owns)
   apply (drule_tac f="\<lambda>pde. valid_pde pde s" in arg_cong, simp)
   apply (clarsimp simp: obj_at_def less_kernel_base_mapping_slots)
   apply (erule pspace_alignedE, erule domI)
   apply (simp add: pt_bits_def pageBits_def)
   apply (subst is_aligned_add_helper, assumption)
    apply (rule shiftl_less_t2n)
     apply (rule order_le_less_trans, rule word_and_le1, simp)
    apply simp
   apply simp
  apply (simp add: pd_bits_def pageBits_def)
  done

lemma is_aligned_6_masks:
  fixes p :: word32
  shows
  "\<lbrakk> is_aligned p 6; bits = pt_bits \<or> bits = pd_bits \<rbrakk>
        \<Longrightarrow> \<forall>x \<in> set [0, 4 .e. 0x3C]. x + p && ~~ mask bits = p && ~~ mask bits"
  apply clarsimp
  apply (drule subsetD[OF upto_enum_step_subset])
  apply (subst mask_lower_twice[symmetric, where n=6])
   apply (auto simp add: pt_bits_def pageBits_def pd_bits_def)[1]
  apply (subst add.commute, subst is_aligned_add_helper, assumption)
   apply (simp add: order_le_less_trans)
  apply simp
  done

lemma lookup_pt_slot_authorised2:
  "\<lbrace>\<exists>\<rhd> pd and K (is_subject aag pd) and
    K (is_aligned pd 14 \<and> is_aligned vptr 16 \<and> vptr < kernel_base) and
    valid_vspace_objs and valid_arch_state and equal_kernel_mappings and
    valid_global_objs and pspace_aligned and pas_refined aag\<rbrace>
    lookup_pt_slot pd vptr
  \<lbrace>\<lambda>rv s.  \<forall>x\<in>set [0 , 4 .e. 0x3C]. is_subject aag (x + rv && ~~ mask pt_bits)\<rbrace>, -"
  apply (clarsimp simp: validE_R_def valid_def validE_def
                 split: sum.split)
  apply (frule use_validE_R[OF _ lookup_pt_slot_authorised])
   apply fastforce
  apply (frule use_validE_R[OF _ lookup_pt_slot_is_aligned_6])
   apply (fastforce simp add: vmsz_aligned_def pd_bits_def pageBits_def)
  apply (simp add: is_aligned_6_masks)
  done

lemma lookup_pt_slot_authorised3:
  "\<lbrace>\<exists>\<rhd> pd and K (is_subject aag pd) and
    K (is_aligned pd 14 \<and> is_aligned vptr 16 \<and> vptr < kernel_base) and
    valid_vspace_objs and valid_arch_state and equal_kernel_mappings and
    valid_global_objs and pspace_aligned and pas_refined aag\<rbrace>
    lookup_pt_slot pd vptr
  \<lbrace>\<lambda>rv s.  \<forall>x\<in>set [rv , rv + 4 .e. rv + 0x3C]. is_subject aag (x && ~~ mask pt_bits)\<rbrace>, -"
  apply (rule hoare_post_imp_R [where Q' = "\<lambda>rv s. is_aligned rv 6 \<and> (\<forall>x\<in>set [0 , 4 .e. 0x3C]. is_subject aag (x + rv && ~~ mask pt_bits))"])
  apply (rule hoare_pre)
  apply (wp lookup_pt_slot_is_aligned_6 lookup_pt_slot_authorised2)
   apply (fastforce simp: vmsz_aligned_def pd_bits_def pageBits_def)
  apply simp
  apply (simp add: p_0x3C_shift)
  done

lemma mapM_set':
  assumes ip: "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>I x and I y\<rbrace> f x \<lbrace>\<lambda>_. I y\<rbrace>"
  and   rl: "\<And>s. (\<forall>x \<in> set xs. I x s) \<Longrightarrow> P s"
  shows "\<lbrace>\<lambda>s. (\<forall>x \<in> set xs. I x s)\<rbrace> mapM f xs \<lbrace>\<lambda>_. P\<rbrace>"
  apply (rule hoare_post_imp [OF rl])
   apply assumption
  apply (rule mapM_set)
    apply (rule hoare_pre)
     apply (rule hoare_vcg_ball_lift)
     apply (erule (1) ip)
    apply clarsimp
   apply (rule hoare_pre)
    apply (rule ip)
     apply assumption
    apply assumption
   apply clarsimp
  apply (rule hoare_pre)
   apply (rule ip)
    apply simp+
  done

lemma mapM_set'':
  assumes ip: "\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs \<rbrakk> \<Longrightarrow> \<lbrace>I x and I y and Q\<rbrace> f x \<lbrace>\<lambda>_. I y and Q\<rbrace>"
  and   rl: "\<And>s. (\<forall>x \<in> set xs. I x s) \<and> Q s \<Longrightarrow> P s"
  shows "\<lbrace>\<lambda>s. (\<forall>x \<in> set xs. I x s) \<and> Q s\<rbrace> mapM f xs \<lbrace>\<lambda>_. P\<rbrace>"
  apply (rule hoare_post_imp [OF rl])
   apply assumption
  apply (cases "xs = []")
   apply (simp add: mapM_Nil)
  apply (rule hoare_pre)
   apply (rule mapM_set' [where I = "\<lambda>x s. I x s \<and> Q s"])
    apply (rule hoare_pre)
     apply (rule ip [simplified pred_conj_def])
      apply simp_all
  apply (clarsimp simp add: neq_Nil_conv)
  done

crunch respects [wp]: flush_page "integrity aag X st"
  (simp: invalidateLocalTLB_VAASID_def ignore: do_machine_op)

lemma find_pd_for_asid_pd_owned[wp]:
  "\<lbrace>pas_refined aag and K (is_subject_asid aag asid)\<rbrace>
  find_pd_for_asid asid
  \<lbrace>\<lambda>rv s. is_subject aag rv\<rbrace>,-"
  apply (wp find_pd_for_asid_authority2)
  apply (auto simp: aag_has_auth_to_Control_eq_owns)
  done

lemmas store_pte_pas_refined_simple
   = store_pte_pas_refined[where pte=InvalidPTE, simplified pte_ref_simps, simplified]

crunch pas_refined[wp]: unmap_page "pas_refined aag"
  (wp: crunch_wps store_pde_pas_refined_simple store_pte_pas_refined_simple
       simp: crunch_simps)

lemma unmap_page_respects:
  "\<lbrace>integrity aag X st and K (is_subject_asid aag asid) and pas_refined aag and pspace_aligned and valid_vspace_objs
        and K (vmsz_aligned vptr sz \<and> vptr < kernel_base)\<rbrace>
    unmap_page sz asid vptr pptr
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_page_def swp_def cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp store_pte_respects store_pde_respects
             hoare_drop_imps[where Q="\<lambda>rv. integrity aag X st"]
             lookup_pt_slot_authorised
                   | wpc
                   | simp add: is_aligned_6_masks is_aligned_mask[symmetric] cleanByVA_PoU_def
                   | wp (once) hoare_drop_imps
                     mapM_set'' [where f = "(\<lambda>a. store_pte a InvalidPTE)" and I = "\<lambda>x s. is_subject aag (x && ~~ mask pt_bits)" and Q = "integrity aag X st"]
                     mapM_set'' [where f = "(\<lambda>a. store_pde a InvalidPDE)" and I = "\<lambda>x s. is_subject aag (x && ~~ mask pd_bits)" and Q = "integrity aag X st"]
                   | wp (once) hoare_drop_imps[where R="\<lambda>rv s. rv"])+
  done

(* FIXME: MOVE *)
lemma less_shiftr:
  shows "\<lbrakk> x < y; is_aligned y n \<rbrakk> \<Longrightarrow> x >> n < y >> n"
  apply (simp add: word_less_nat_alt shiftr_div_2n')
  apply (subst td_gal_lt[symmetric])
   apply simp
  apply (subst dvd_div_mult_self)
   apply (simp add: is_aligned_def)
  apply simp
  done

lemma kernel_base_aligned_20:
  "is_aligned kernel_base 20"
  apply(simp add: kernel_base_def is_aligned_def)
  done

(* FIXME: CLAG *)
lemmas do_machine_op_bind =
    submonad_bind [OF submonad_do_machine_op submonad_do_machine_op
                      submonad_do_machine_op]

lemma mol_mem[wp]:
  "\<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace> machine_op_lift mop \<lbrace>\<lambda>rv ms. P (underlying_memory ms)\<rbrace>"
  by (simp add: machine_op_lift_def machine_rest_lift_def split_def | wp)+

lemma mol_dvs[wp]:
  "\<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> machine_op_lift mop \<lbrace>\<lambda>rv ms. P (device_state ms)\<rbrace>"
  by (simp add: machine_op_lift_def machine_rest_lift_def split_def | wp)+

lemmas do_flush_defs = cleanCacheRange_RAM_def cleanCacheRange_PoC_def cleanCacheRange_PoU_def invalidateCacheRange_RAM_def cleanInvalidateCacheRange_RAM_def branchFlushRange_def invalidateCacheRange_I_def

lemma do_flush_respects[wp]:
  "\<lbrace>integrity aag X st\<rbrace> do_machine_op (do_flush typ start end pstart)
    \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (cases "typ")
     apply (wp dmo_no_mem_respects | simp add: do_flush_def cache_machine_op_defs do_flush_defs)+
     done

lemma invalidate_tlb_by_asid_respects[wp]:
  "\<lbrace>integrity aag X st\<rbrace> invalidate_tlb_by_asid asid
    \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: invalidate_tlb_by_asid_def)
  apply (wp dmo_no_mem_respects | wpc | simp add: invalidateLocalTLB_ASID_def )+
  done

lemma invalidate_tlb_by_asid_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> invalidate_tlb_by_asid asid \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  by (wp dmo_no_mem_respects | wpc | simp add: invalidate_tlb_by_asid_def invalidateLocalTLB_ASID_def)+

lemma as_user_pas_refined[wp]:
  "\<lbrace>\<lambda>s. pas_refined aag s\<rbrace> as_user t f \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply wps
   apply wp
  apply simp
  done

crunch pas_refined[wp]: set_message_info "pas_refined aag"

(* FIXME: move *)
lemma set_message_info_mdb[wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> set_message_info thread info \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  unfolding set_message_info_def by wp

crunch state_vrefs[wp]: do_machine_op "\<lambda>s::'z::state_ext state. P (state_vrefs s)"

crunch thread_states[wp]: do_machine_op "\<lambda>s. P (thread_states s)"

(* FIXME: move *)
lemma set_mrs_state_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_mrs_def split_def set_object_def get_object_def split del: if_split)
  apply (wp gets_the_wp get_wp put_wp mapM_x_wp'
       | wpc
       | simp split del: if_split add: zipWithM_x_mapM_x split_def store_word_offs_def)+
  apply (auto simp: obj_at_def state_vrefs_def get_tcb_ko_at
             elim!: rsubst[where P=P, OF _ ext]
             split: if_split_asm simp: vs_refs_no_global_pts_def)
  done

(* FIXME: move *)
lemma set_mrs_thread_states[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: set_mrs_def split_def set_object_def get_object_def split del: if_split)
  apply (wp gets_the_wp get_wp put_wp mapM_x_wp'
       | wpc
       | simp split del: if_split add: zipWithM_x_mapM_x split_def store_word_offs_def)+
  apply (clarsimp simp: fun_upd_def[symmetric] thread_states_preserved)
  done

lemma set_mrs_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_mrs_def split_def set_object_def get_object_def split del: if_split)
  apply (wp gets_the_wp get_wp put_wp mapM_x_wp' dmo_wp
       | wpc
       | simp split del: if_split add: zipWithM_x_mapM_x split_def store_word_offs_def no_irq_storeWord)+
  apply (clarsimp simp: fun_upd_def[symmetric] thread_bound_ntfns_preserved )
  done

lemma set_mrs_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp | wps)+
  apply (clarsimp dest!: auth_graph_map_memD)
  done

crunch integrity_autarch: set_message_info "integrity aag X st"

lemma dmo_storeWord_respects_Write:
  "\<lbrace>integrity aag X st and K (\<forall>p' \<in> ptr_range p 2. aag_has_auth_to aag Write p')\<rbrace>
  do_machine_op (storeWord p v)
  \<lbrace>\<lambda>a. integrity aag X st\<rbrace>"
  apply (rule hoare_pre)
  apply (wp dmo_wp storeWord_respects)
  apply simp
  done

(* c.f.  auth_ipc_buffers *)
definition
  ipc_buffer_has_auth :: "'a PAS \<Rightarrow> word32 \<Rightarrow> word32 option \<Rightarrow> bool"
where
   "ipc_buffer_has_auth aag thread \<equiv>
    case_option True (\<lambda>buf'. is_aligned buf' msg_align_bits \<and> (\<forall>x \<in> ptr_range buf' msg_align_bits. (pasObjectAbs aag thread, Write, pasObjectAbs aag x) \<in> pasPolicy aag))"

lemma ipc_buffer_has_auth_wordE:
  "\<lbrakk> ipc_buffer_has_auth aag thread (Some buf); p \<in> ptr_range (buf + off) sz; is_aligned off sz; sz \<le> msg_align_bits; off < 2 ^ msg_align_bits \<rbrakk>
  \<Longrightarrow> (pasObjectAbs aag thread, Write, pasObjectAbs aag p) \<in> pasPolicy aag"
  unfolding ipc_buffer_has_auth_def
  apply clarsimp
  apply (erule bspec)
  apply (erule (4) set_mp [OF ptr_range_subset])
  done


lemma is_aligned_word_size_2 [simp]:
  "is_aligned (p * of_nat word_size) 2"
  unfolding word_size_def
  by (simp add: is_aligned_mult_triv2 [where n = 2, simplified] word_bits_conv)



lemma mul_word_size_lt_msg_align_bits_ofnat:
  "p < 2 ^ (msg_align_bits - 2) \<Longrightarrow> of_nat p * of_nat word_size < (2 :: word32) ^ msg_align_bits"
  unfolding word_size_def
  apply simp
  apply (rule word_less_power_trans_ofnat [where k = 2, simplified])
  apply (simp_all add: msg_align_bits word_bits_conv)
  done

lemma store_word_offs_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag thread \<and> ipc_buffer_has_auth aag thread (Some buf) \<and> r < 2 ^ (msg_align_bits - 2))\<rbrace>
   store_word_offs buf r v
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: store_word_offs_def)
  apply (rule hoare_pre)
   apply (wp dmo_storeWord_respects_Write)
  apply clarsimp
  apply (drule (1) ipc_buffer_has_auth_wordE)
     apply simp
    apply (simp add: msg_align_bits)
   apply (erule mul_word_size_lt_msg_align_bits_ofnat)
  apply simp
  done

lemma set_mrs_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag thread \<and>  ipc_buffer_has_auth aag thread buf)\<rbrace>
     set_mrs thread buf msgs
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: set_mrs_def split del: if_split)
  apply (wp gets_the_wp get_wp put_wp mapM_x_wp' store_word_offs_integrity_autarch [where aag = aag and thread = thread]
       | wpc
       | simp split del: if_split add: split_def zipWithM_x_mapM_x )+
    apply (clarsimp elim!: in_set_zipE split: if_split_asm)
    apply (rule order_le_less_trans [where y = msg_max_length])
     apply (fastforce simp add: le_eq_less_or_eq)
    apply (simp add: msg_max_length_def msg_align_bits)
   apply simp
   apply (wp set_object_integrity_autarch hoare_drop_imps hoare_vcg_all_lift)+
  apply simp
  done

lemma perform_page_invocation_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and K (authorised_page_inv aag pgi) and valid_page_inv pgi and valid_vspace_objs and pspace_aligned and is_subject aag  \<circ> cur_thread\<rbrace>
     perform_page_invocation pgi
   \<lbrace>\<lambda>s. integrity aag X st\<rbrace>"
proof -
  (* does not work as elim rule with clarsimp, which hammers Ball in concl. *)
  have set_tl_subset_mp: "\<And>xs a. a \<in> set (tl xs) \<Longrightarrow> a \<in> set xs" by (case_tac xs,clarsimp+)
  have hd_valid_slots:
    "\<And>a xs s. valid_slots (Inl (a, xs)) s \<Longrightarrow> hd xs \<in> set xs"
    "\<And>a xs s. valid_slots (Inr (a, xs)) s \<Longrightarrow> hd xs \<in> set xs"
    by (simp_all add: valid_slots_def)

  show ?thesis
  apply (simp add: perform_page_invocation_def mapM_discarded swp_def
                   valid_page_inv_def valid_unmap_def
                   authorised_page_inv_def authorised_slots_def
            split: page_invocation.split sum.split
                   arch_cap.split option.split,
         safe)
        apply (wp set_cap_integrity_autarch unmap_page_respects
                  mapM_x_and_const_wp[OF store_pte_respects] store_pte_respects
                  mapM_x_and_const_wp[OF store_pde_respects] store_pde_respects
             | elim conjE hd_valid_slots[THEN bspec[rotated]]
             | clarsimp dest!:set_tl_subset_mp
             | wpc )+
   apply (clarsimp simp: cte_wp_at_caps_of_state cap_rights_update_def
                         acap_rights_update_def update_map_data_def is_pg_cap_def
                         valid_page_inv_def valid_cap_simps
                  dest!: cap_master_cap_eqDs)
   apply (drule (1) clas_caps_of_state)
   apply (simp add: cap_links_asid_slot_def label_owns_asid_slot_def)
   apply (auto dest: pas_refined_Control)[1]
  apply (wp set_mrs_integrity_autarch set_message_info_integrity_autarch | simp add: ipc_buffer_has_auth_def)+
  done
qed

(* FIXME MOVE *)
crunch cdt[wp]: unmap_page "\<lambda>s. P (cdt s)"
  (simp: crunch_simps wp: crunch_wps)


lemma perform_page_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and K (authorised_page_inv aag pgi) and valid_page_inv pgi\<rbrace>
     perform_page_invocation pgi
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_page_invocation_def mapM_discarded
    valid_page_inv_def valid_unmap_def swp_def
    authorised_page_inv_def authorised_slots_def
    cong: page_invocation.case_cong sum.case_cong)
  apply (rule hoare_pre)
   apply wpc
      apply (wp set_cap_pas_refined unmap_page_pas_refined case_sum_wp  case_prod_wp
                mapM_x_and_const_wp [OF store_pte_pas_refined] mapM_x_and_const_wp [OF store_pde_pas_refined]
             hoare_vcg_all_lift hoare_vcg_const_imp_lift get_cap_wp
            | (wp hoare_vcg_imp_lift, unfold disj_not1)
            | strengthen clas_update_map_data_strg
            | wpc
            | wps
            | simp)+
  apply (case_tac pgi)
      apply ((force simp: valid_slots_def pte_ref_def cte_wp_at_caps_of_state
                          is_transferable_is_arch_update[symmetric]
                          pde_ref2_def auth_graph_map_mem pas_refined_refl
                   split: sum.splits)+)[2]
    apply (clarsimp simp: cte_wp_at_caps_of_state is_transferable_is_arch_update[symmetric]
                          pte_ref_def pde_ref2_def is_cap_simps is_pg_cap_def)
    apply (frule(1) cap_cur_auth_caps_of_state, simp)
    apply (intro impI conjI;
           clarsimp; (* NB: for speed *)
           clarsimp simp: update_map_data_def clas_no_asid aag_cap_auth_def
                          cap_auth_conferred_def arch_cap_auth_conferred_def
                          vspace_cap_rights_to_auth_def cli_no_irqs is_pg_cap_def
                          pte_ref_def[simplified aag_cap_auth_def])+
  done

definition
  authorised_asid_control_inv :: "'a PAS \<Rightarrow> asid_control_invocation \<Rightarrow> bool"
where
 "authorised_asid_control_inv aag aci \<equiv> case aci of
     asid_control_invocation.MakePool frame slot parent base \<Rightarrow>
       is_subject aag (fst slot) \<and> is_aligned frame pageBits \<and> (\<forall>asid. is_subject_asid aag asid) \<and> is_subject aag (fst parent) \<and>
       (\<forall>x \<in> {frame..frame + 2 ^ pageBits - 1}. is_subject aag x)"


lemma integrity_arm_asid_table_entry_update':
  "\<lbrakk>integrity aag X st s; atable = arm_asid_table (arch_state s);
       (\<forall>asid'.
                    asid' \<noteq> 0 \<and>
                    asid_high_bits_of asid' = asid_high_bits_of asid \<longrightarrow>
                    is_subject_asid aag asid')\<rbrakk> \<Longrightarrow>
       integrity aag X st
           (s\<lparr>arch_state := arch_state s
                \<lparr>arm_asid_table :=
                   \<lambda>a. if a = asid_high_bits_of asid then v
                       else atable a\<rparr>\<rparr>)"
  apply(clarsimp simp: integrity_def integrity_asids_def)
  done

lemma arm_asid_table_entry_update_integrity[wp]:
 "\<lbrace>integrity aag X st and (\<lambda> s. atable = arm_asid_table (arch_state s)) and K (\<forall>asid'.
                    asid' \<noteq> 0 \<and>
                    asid_high_bits_of asid' = asid_high_bits_of asid \<longrightarrow>
                    is_subject_asid aag asid')\<rbrace>
 modify
        (\<lambda>s. s\<lparr>arch_state := arch_state s
                 \<lparr>arm_asid_table := atable
                    (asid_high_bits_of asid := v)\<rparr>\<rparr>)
  \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (wp| simp)+
  apply (blast intro: integrity_arm_asid_table_entry_update')
  done

lemma perform_asid_control_invocation_respects:
  "\<lbrace>integrity aag X st and K (authorised_asid_control_inv aag aci)\<rbrace>
     perform_asid_control_invocation aci
   \<lbrace>\<lambda>s. integrity aag X st\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (rule hoare_pre)
   apply (wpc, simp)
   apply (wp set_cap_integrity_autarch cap_insert_integrity_autarch retype_region_integrity[where sz=12] static_imp_wp | simp)+
  apply (clarsimp simp: authorised_asid_control_inv_def
                        ptr_range_def page_bits_def add.commute
                        range_cover_def obj_bits_api_def default_arch_object_def
                        pageBits_def word_bits_def)
  apply(subst is_aligned_neg_mask_eq[THEN sym], assumption)
  apply(simp add: and_mask_eq_iff_shiftr_0 mask_zero)
  done

lemma pas_refined_set_asid_strg:
  "pas_refined aag s \<and> is_subject aag pool \<and> (\<forall>asid. asid_high_bits_of asid = base \<longrightarrow> is_subject_asid aag asid)
    \<longrightarrow>
  pas_refined aag (s\<lparr>arch_state := arch_state s \<lparr>arm_asid_table := (arm_asid_table (arch_state s))(base \<mapsto> pool)\<rparr>\<rparr>)"
  apply (clarsimp simp: pas_refined_def state_objs_to_policy_def)
  apply (erule state_asids_to_policy_aux.cases, simp_all split: if_split_asm)
      apply (auto intro: state_asids_to_policy_aux.intros auth_graph_map_memI[OF sbta_vref]
                 intro!: pas_refined_refl[simplified pas_refined_def state_objs_to_policy_def])
  done


(* FIXME: copied from Detype_R. *)
lemma gets_modify_comm2:
  "\<forall>s. g (f s) = g s \<Longrightarrow>
   (do x \<leftarrow> modify f; y \<leftarrow> gets g; m x y od) =
   (do y \<leftarrow> gets g; x \<leftarrow> modify f; m x y od)"
  apply (rule ext)
  apply (drule spec)
  by (rule gets_modify_comm)
lemma dmo_detype_comm:
  assumes "empty_fail f"
  shows "do_machine_op f >>= (\<lambda>s. modify (detype S)) =
         modify (detype S) >>= (\<lambda>s. do_machine_op f)"
proof -
  have machine_state_detype: "\<forall>s. machine_state (detype S s) = machine_state s"
    by (simp add: detype_def)
  have detype_msu_independent:
    "\<And>f. detype S \<circ> machine_state_update f = machine_state_update f \<circ> detype S"
    by (simp add: detype_def ext)
  from assms
  show ?thesis
    apply (simp add: do_machine_op_def split_def bind_assoc)
    apply (simp add: gets_modify_comm2[OF machine_state_detype])
    apply (rule arg_cong_bind1)
    apply (simp add: empty_fail_def select_f_walk[OF empty_fail_modify]
                     modify_modify detype_msu_independent)
    done
qed

(* FIXME: copied from Detype_R. *)
lemma empty_fail_freeMemory: "empty_fail (freeMemory ptr bits)"
  by (simp add: freeMemory_def mapM_x_mapM ef_storeWord)

(* FIXME: copied from Detype_R. *)
lemma delete_objects_def2:
  "delete_objects ptr bits \<equiv>
   do modify (detype {ptr..ptr + 2 ^ bits - 1});
      do_machine_op (freeMemory ptr bits)
   od"
  by (rule eq_reflection)
     (simp add: delete_objects_def dmo_detype_comm[OF empty_fail_freeMemory])

lemma delete_objects_pspace_no_overlap:
  "\<lbrace> pspace_aligned and valid_objs and
     (\<lambda> s. \<exists> idx. cte_wp_at ((=) (UntypedCap dev ptr sz idx)) slot s)\<rbrace>
    delete_objects ptr sz
   \<lbrace>\<lambda>rv. pspace_no_overlap_range_cover ptr sz\<rbrace>"
  unfolding delete_objects_def do_machine_op_def
  apply(wp | simp add: split_def detype_machine_state_update_comm)+
  apply(clarsimp)
  apply(rule pspace_no_overlap_detype)
   apply(auto dest: cte_wp_at_valid_objs_valid_cap)
  done


lemma delete_objects_invs_ex:
  "\<lbrace>(\<lambda>s. \<exists>slot dev f.
         cte_wp_at ((=) (UntypedCap dev ptr bits f)) slot s \<and>
         descendants_range (UntypedCap dev ptr bits f) slot s) and
   invs and
   ct_active\<rbrace>
  delete_objects ptr bits \<lbrace>\<lambda>_. invs\<rbrace>"
  apply(clarsimp simp: valid_def)
  apply(erule use_valid)
  apply wp
  apply auto
  done


lemma perform_asid_control_invocation_pas_refined [wp]:
  notes delete_objects_invs[wp del]
  shows
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and valid_aci aci and ct_active and
    K (authorised_asid_control_inv aag aci)\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (rule hoare_pre)
   apply (wp cap_insert_pas_refined' static_imp_wp
        | strengthen pas_refined_set_asid_strg
        | wpc
        | simp add: delete_objects_def2 fun_upd_def[symmetric])+
      apply (wp retype_region_pas_refined'[where sz=pageBits]
                hoare_vcg_ex_lift hoare_vcg_all_lift static_imp_wp hoare_wp_combs hoare_drop_imp
                retype_region_invs_extras(4)[where sz = pageBits]
            | simp add: do_machine_op_def split_def cte_wp_at_neg2)+
      apply (wp retype_region_cte_at_other'[where sz=pageBits]
                max_index_upd_invs_simple max_index_upd_caps_overlap_reserved
                hoare_vcg_ex_lift set_cap_cte_wp_at hoare_vcg_disj_lift set_free_index_valid_pspace
                set_cap_descendants_range_in set_cap_no_overlap get_cap_wp set_cap_caps_no_overlap
                hoare_vcg_all_lift static_imp_wp retype_region_invs_extras
                set_cap_pas_refined_not_transferable
            | simp add: do_machine_op_def split_def cte_wp_at_neg2 region_in_kernel_window_def)+
   apply (rename_tac frame slot parent base cap)
   apply (case_tac slot, rename_tac slot_ptr slot_idx)
   apply (case_tac parent, rename_tac parent_ptr parent_idx)
   apply (rule_tac Q="\<lambda>rv s.
             (\<exists>idx. cte_wp_at ((=) (UntypedCap False frame pageBits idx)) parent s) \<and>
             (\<forall>x\<in>ptr_range frame pageBits. is_subject aag x) \<and>
             pas_refined aag s \<and>
             pas_cur_domain aag s \<and>
             pspace_no_overlap_range_cover frame pageBits s \<and>
             invs s \<and>
             descendants_range_in
               {frame..(frame && ~~ mask pageBits) + 2 ^ pageBits - 1} parent s \<and>
             range_cover frame pageBits
               (obj_bits_api (ArchObject ASIDPoolObj) 0) (Suc 0) \<and>
             is_subject aag slot_ptr \<and>
             is_subject aag parent_ptr \<and>
             pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap frame base)) \<and>
             is_subject aag frame \<and>
             (\<forall>x. asid_high_bits_of x = asid_high_bits_of base \<longrightarrow>
                 is_subject_asid aag x)"
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
                         cap_links_asid_slot_def cap_links_irq_def
                         obj_bits_api_def default_arch_object_def retype_addrs_def)
   apply (rule conjI, force intro: descendants_range_caps_no_overlapI
                             simp: cte_wp_at_def)
   apply (rule conjI)
    apply (cut_tac s=s and ptr="(parent_ptr, parent_idx)" in cap_refs_in_kernel_windowD)
      apply ((fastforce simp add: caps_of_state_def cap_range_def)+)[3]
   apply (rule conjI, force simp: field_simps)
   apply (rule conjI, fastforce)
   apply (fastforce dest: caps_of_state_valid
                    simp: caps_of_state_def free_index_of_def
                          max_free_index_def valid_cap_def)
  apply (clarsimp simp: valid_aci_def authorised_asid_control_inv_def)
  apply (rename_tac frame slot_ptr slot_idx parent_ptr parent_idx base)
  apply (subgoal_tac "is_aligned frame pageBits")
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (rule conjI)
    apply (drule untyped_slots_not_in_untyped_range)
         apply (erule empty_descendants_range_in)
        apply (simp add: cte_wp_at_caps_of_state)
       apply simp
      apply (rule refl)
     apply (rule subset_refl)
    apply (simp add: page_bits_def)
   apply (clarsimp simp: ptr_range_def invs_psp_aligned invs_valid_objs
                         descendants_range_def2 empty_descendants_range_in page_bits_def)
   apply ((strengthen refl | simp)+)?
   apply (rule conjI, fastforce)
   apply (rule conjI, fastforce intro: empty_descendants_range_in)
   apply (rule conjI)
    apply (clarsimp simp: range_cover_def obj_bits_api_def default_arch_object_def)
    apply (subst is_aligned_neg_mask_eq[THEN sym], assumption)
    apply (simp add: and_mask_eq_iff_shiftr_0 pageBits_def mask_zero)
   apply (clarsimp simp: aag_cap_auth_def pas_refined_refl)
   apply (drule_tac x=frame in bspec)
    apply (simp add: is_aligned_no_overflow)
   apply (clarsimp simp: pas_refined_refl cap_links_asid_slot_def
                         label_owns_asid_slot_def cap_links_irq_def)
  apply (fastforce dest: cte_wp_at_valid_objs_valid_cap simp: valid_cap_def cap_aligned_def)
  done

lemma set_asid_pool_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag ptr)\<rbrace>
     set_asid_pool ptr pool
   \<lbrace>\<lambda>s. integrity aag X st\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_integrity_autarch)
  apply simp
  done

definition
  authorised_asid_pool_inv :: "'a PAS \<Rightarrow> asid_pool_invocation \<Rightarrow> bool"
where
 "authorised_asid_pool_inv aag api \<equiv> case api of
     asid_pool_invocation.Assign asid pool_ptr ct_slot \<Rightarrow>
       is_subject aag pool_ptr \<and> is_subject aag (fst ct_slot)
          \<and> asid \<noteq> 0
          \<and> (\<forall>asid'. asid_high_bits_of asid' = asid_high_bits_of asid \<and> asid' \<noteq> 0
                     \<longrightarrow> is_subject_asid aag asid')"

lemma perform_asid_pool_invocation_respects:
  "\<lbrace>integrity aag X st and K (authorised_asid_pool_inv aag api)\<rbrace>
     perform_asid_pool_invocation api
   \<lbrace>\<lambda>s. integrity aag X st\<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)
  apply (rule hoare_pre)
  apply (wp set_asid_pool_respects get_cap_wp set_cap_integrity_autarch
       | wpc
       | simp)+
  apply (auto iff: authorised_asid_pool_inv_def)
  done

lemma is_subject_asid_into_loas:
  "\<lbrakk> is_subject_asid aag asid; pas_refined aag s \<rbrakk> \<Longrightarrow> label_owns_asid_slot aag (pasSubject aag) asid"
  unfolding label_owns_asid_slot_def
  by (clarsimp simp: pas_refined_refl)

lemma asid_pool_into_aag:
  "\<lbrakk>kheap s p = Some (ArchObj (arch_kernel_obj.ASIDPool pool)); pool r = Some p'; pas_refined aag s \<rbrakk>
  \<Longrightarrow> (pasObjectAbs aag p, Control, pasObjectAbs aag p') \<in> pasPolicy aag"
  apply (rule pas_refined_mem [rotated], assumption)
  apply (rule sta_vref)
  apply (fastforce simp add: state_vrefs_def vs_refs_no_global_pts_def intro!: graph_ofI)
  done

lemma asid_pool_uniqueness:
  "\<lbrakk> ([VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> p) s;
      arm_asid_table (arch_state s) (asid_high_bits_of asid') = Some p;
       invs s; \<forall>pt. \<not> ko_at (ArchObj (PageTable pt)) p s \<rbrakk>
      \<Longrightarrow> asid_high_bits_of asid' = asid_high_bits_of asid"
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply (drule vs_lookup_atI, drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply (clarsimp dest!: obj_ref_elemD)
  apply (drule(1) unique_table_refsD[where cps="caps_of_state s", rotated])
    apply simp
   apply (clarsimp simp: vs_cap_ref_def table_cap_ref_def up_ucast_inj_eq
                  split: vmpage_size.splits option.splits cap.splits arch_cap.splits)+
  done

lemma perform_asid_pool_invocation_pas_refined [wp]:
  "\<lbrace>pas_refined aag and invs and valid_apinv api and K (authorised_asid_pool_inv aag api)\<rbrace>
     perform_asid_pool_invocation api
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: perform_asid_pool_invocation_def)
  apply (rule hoare_pre)
  apply (wp get_cap_auth_wp[where aag = aag] set_cap_pas_refined_not_transferable | wpc)+
  apply (clarsimp simp: authorised_asid_pool_inv_def cap_links_asid_slot_def
                        is_subject_asid_into_loas aag_cap_auth_def)
  apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def
                        is_cap_simps is_page_cap_def auth_graph_map_mem
                        pas_refined_all_auth_is_owns pas_refined_refl cli_no_irqs
                        cte_wp_at_caps_of_state
                 dest!: graph_ofD)
  apply (clarsimp split: if_split_asm)
   apply (clarsimp simp add: pas_refined_refl auth_graph_map_def2
                             mask_asid_low_bits_ucast_ucast[symmetric]
                             valid_apinv_def obj_at_def)
   apply (drule(2) asid_pool_uniqueness)
    apply (simp add: obj_at_def)
   apply (case_tac "asid = 0"; simp add: pas_refined_refl)
   apply (simp add: asid_low_high_bits[rotated, OF arg_cong[where f=ucast]])
  apply (clarsimp simp: obj_at_def)
  apply (frule (2) asid_pool_into_aag)
  apply (drule kheap_eq_state_vrefsD)
  apply (clarsimp simp: auth_graph_map_def2 pas_refined_refl)
  apply (clarsimp simp: pas_refined_def vs_refs_no_global_pts_def)
  apply (erule subsetD, erule state_asids_to_policy_aux.intros,
         simp add: split_def, rule image_eqI[rotated], erule graph_ofI)
  apply simp
  done

definition
  authorised_page_directory_inv :: "'a PAS \<Rightarrow> page_directory_invocation \<Rightarrow> bool"
where
  "authorised_page_directory_inv aag pdi \<equiv> True"

definition
  authorised_arch_inv :: "'a PAS \<Rightarrow> arch_invocation \<Rightarrow> bool"
where
 "authorised_arch_inv aag ai \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> authorised_page_table_inv aag pti
   | InvokePageDirectory pdi \<Rightarrow> authorised_page_directory_inv aag pdi
   | InvokePage pgi \<Rightarrow> authorised_page_inv aag pgi
   | InvokeASIDControl aci \<Rightarrow> authorised_asid_control_inv aag aci
   | InvokeASIDPool api \<Rightarrow> authorised_asid_pool_inv aag api"

crunch respects [wp]: perform_page_directory_invocation "integrity aag X st"
  (ignore: do_machine_op)

lemma invoke_arch_respects:
  "\<lbrace>integrity aag X st and K (authorised_arch_inv aag ai) and
    pas_refined aag and invs and valid_arch_inv ai and is_subject aag \<circ> cur_thread\<rbrace>
     arch_perform_invocation ai
   \<lbrace>\<lambda>s. integrity aag X st\<rbrace>"
  apply (simp add: arch_perform_invocation_def)
  apply (rule hoare_pre)
  apply (wp perform_page_table_invocation_respects perform_page_invocation_respects
           perform_asid_control_invocation_respects perform_asid_pool_invocation_respects
       | wpc)+
  apply (auto simp: authorised_arch_inv_def valid_arch_inv_def)
  done

crunch pas_refined [wp]: perform_page_directory_invocation "pas_refined aag"

lemma invoke_arch_pas_refined:
  "\<lbrace>pas_refined aag and pas_cur_domain aag and invs and ct_active and valid_arch_inv ai and K (authorised_arch_inv aag ai)\<rbrace>
     arch_perform_invocation ai
   \<lbrace>\<lambda>s. pas_refined aag\<rbrace>"
  apply (simp add: arch_perform_invocation_def valid_arch_inv_def)
  apply (rule hoare_pre)
  apply (wp | wpc)+
  apply (fastforce simp add: authorised_arch_inv_def)
  done

lemma create_mapping_entries_authorised_slots [wp]:
  "\<lbrace>\<exists>\<rhd> pd and invs and pas_refined aag
    and K (is_subject aag pd
           \<and> is_aligned pd pd_bits
           \<and> vmsz_aligned vptr vmpage_size
           \<and> vptr < kernel_base
           \<and> (\<forall>a\<in>vspace_cap_rights_to_auth rights.
                  \<forall>p\<in>ptr_range (ptrFromPAddr base) (pageBitsForSize vmpage_size).
                      aag_has_auth_to aag a p))\<rbrace>
    create_mapping_entries base vptr vmpage_size rights attrib pd
  \<lbrace>\<lambda>rv s. authorised_slots aag rv\<rbrace>, -"
  unfolding authorised_slots_def
  apply (rule hoare_gen_asmE)
  apply (cases vmpage_size)
     apply (wp lookup_pt_slot_authorised
                 | simp add: pte_ref_simps | fold validE_R_def)+
     apply (auto simp: pd_bits_def pageBits_def)[1]
    apply (wp lookup_pt_slot_authorised2
          | simp add: pte_ref_simps largePagePTE_offsets_def
          | fold validE_R_def)+
    apply (auto simp: pd_bits_def pageBits_def vmsz_aligned_def)[1]
   apply (wp | simp)+
   apply (auto simp: pde_ref2_def lookup_pd_slot_pd)[1]
  apply (wp | simp add: superSectionPDE_offsets_def)+
  apply (auto simp: pde_ref2_def vmsz_aligned_def lookup_pd_slot_add_eq)
  done

lemma x_t2n_sub_1_neg_mask:
  "\<lbrakk> is_aligned x n; n \<le> m \<rbrakk>
     \<Longrightarrow> x + 2 ^ n - 1 && ~~ mask m = x && ~~ mask m"
  apply (erule is_aligned_get_word_bits)
   apply (rule trans, rule mask_lower_twice[symmetric], assumption)
   apply (subst add_diff_eq[symmetric], subst is_aligned_add_helper, assumption)
    apply simp+
  apply (simp add: mask_def power_overflow)
  done

lemma pageBitsForSize_le_t28:
  "pageBitsForSize sz \<le> 28"
  by (cases sz, simp_all)

lemma pageBitsForSize_le_t29:
  "pageBitsForSize sz \<le> 29"
  by (cases sz, simp_all)

lemmas vmsz_aligned_t2n_neg_mask
    = x_t2n_sub_1_neg_mask[OF _ pageBitsForSize_le_t29, folded vmsz_aligned_def]

lemma decode_arch_invocation_authorised:
  "\<lbrace>invs and pas_refined aag
        and cte_wp_at ((=) (cap.ArchObjectCap cap)) slot
        and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
        and K (\<forall>(cap, slot) \<in> {(cap.ArchObjectCap cap, slot)} \<union> set excaps.
                      aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and> is_subject aag (fst slot)
                   \<and> (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v))\<rbrace>
     arch_decode_invocation label msg x_slot slot cap excaps
   \<lbrace>\<lambda>rv s. authorised_arch_inv aag rv\<rbrace>,-"
  unfolding arch_decode_invocation_def authorised_arch_inv_def aag_cap_auth_def
  apply (rule hoare_pre)
   apply (simp add: split_def Let_def
     cong: cap.case_cong arch_cap.case_cong if_cong option.case_cong split del: if_split)

   apply (wp select_wp whenE_throwError_wp check_vp_wpR
             find_pd_for_asid_authority2
           | wpc
           | simp add: authorised_asid_control_inv_def authorised_page_inv_def
                       authorised_page_directory_inv_def
                  del: hoare_True_E_R
                  split del: if_split)+
  apply (clarsimp simp: authorised_asid_pool_inv_def authorised_page_table_inv_def
                        neq_Nil_conv invs_psp_aligned invs_vspace_objs cli_no_irqs)
  apply (drule cte_wp_valid_cap, clarsimp+)
  apply (cases cap; simp)
      \<comment> \<open>asid pool\<close>
     apply (find_goal \<open>match premises in "cap = ASIDPoolCap _ _" \<Rightarrow> succeed\<close>)
     subgoal for s obj_ref asid
       by (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def is_page_cap_def
                          pas_refined_all_auth_is_owns asid_high_bits_of_add_ucast valid_cap_simps)
     \<comment> \<open>ControlCap\<close>
    apply (find_goal \<open>match premises in "cap = ASIDControlCap" \<Rightarrow> succeed\<close>)
    subgoal
      apply (clarsimp simp: neq_Nil_conv split_def valid_cap_simps)
      apply (cases excaps, solves simp)
      apply (clarsimp simp: neq_Nil_conv aag_has_auth_to_Control_eq_owns)
      apply (drule cte_wp_at_valid_objs_valid_cap, clarsimp)
      apply (clarsimp simp: valid_cap_def cap_aligned_def)
      apply (clarsimp simp: is_cap_simps cap_auth_conferred_def
                            pas_refined_all_auth_is_owns aag_cap_auth_def)
      done
   \<comment> \<open>PageCap\<close>
   apply (find_goal \<open>match premises in "cap = PageCap _ _ _ _ _" \<Rightarrow> succeed\<close>)
   subgoal for s is_dev obj_ref cap_rights vmpage_size mapping
     apply (clarsimp simp: valid_cap_simps cli_no_irqs)
     apply (cases "invocation_type label"; (solves \<open>simp\<close>)?)
     apply (find_goal \<open>match premises in "_ = ArchInvocationLabel _" \<Rightarrow> succeed\<close>)
     apply (rename_tac archlabel)
     apply (case_tac archlabel; (solves \<open>simp\<close>)?)
       \<comment> \<open>Map\<close>
      apply (find_goal \<open>match premises in "_ = ARMPageMap" \<Rightarrow> succeed\<close>)
      subgoal
       apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def is_cap_simps is_page_cap_def
                             pas_refined_all_auth_is_owns)
       apply (rule conjI)
        apply (clarsimp simp: is_page_cap_def pas_refined_all_auth_is_owns
                              aag_cap_auth_def cli_no_irqs cap_links_asid_slot_def)
        apply (simp only: linorder_not_le kernel_base_less_observation
                          vmsz_aligned_t2n_neg_mask simp_thms)
         apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def
                               vspace_cap_rights_to_auth_def mask_vm_rights_def
                               validate_vm_rights_def vm_read_only_def vm_kernel_only_def)
        apply clarsimp
        apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def aag_cap_auth_def
                               cli_no_irqs vspace_cap_rights_to_auth_def mask_vm_rights_def
                              validate_vm_rights_def vm_read_only_def vm_kernel_only_def)
       done
     \<comment> \<open>Unmap\<close>
     subgoal by (simp add: aag_cap_auth_def cli_no_irqs)
     done
  \<comment> \<open>PageTableCap\<close>
  apply (find_goal \<open>match premises in "cap = PageTableCap _ _" \<Rightarrow> succeed\<close>)
  subgoal for s word option
    apply (cases "invocation_type label"; (solves \<open>simp\<close>)?)
    apply (find_goal \<open>match premises in "_ = ArchInvocationLabel _" \<Rightarrow> succeed\<close>)
    apply (rename_tac archlabel)
    apply (case_tac archlabel; (solves \<open>simp\<close>)?)
     \<comment> \<open>PTMap\<close>
     apply (find_goal \<open>match premises in "_ = ARMPageTableMap" \<Rightarrow> succeed\<close>)
     apply (clarsimp simp: aag_cap_auth_def cli_no_irqs cap_links_asid_slot_def
                           cap_auth_conferred_def arch_cap_auth_conferred_def is_page_cap_def
                           pde_ref2_def pas_refined_all_auth_is_owns pas_refined_refl
                           pd_shifting[folded pd_bits_14])
    \<comment> \<open>Unmap\<close>
    apply (find_goal \<open>match premises in "_ = ARMPageTableUnmap" \<Rightarrow> succeed\<close>)
    subgoal
      apply (clarsimp simp: aag_cap_auth_def cli_no_irqs cap_links_asid_slot_def
                            cap_auth_conferred_def arch_cap_auth_conferred_def is_page_cap_def
                            pde_ref2_def pas_refined_all_auth_is_owns pas_refined_refl)
      apply (subgoal_tac "x && ~~ mask pt_bits = word")
       apply simp
      apply (clarsimp simp: valid_cap_simps cap_aligned_def split: if_split_asm)
      apply (subst (asm) upto_enum_step_subtract)
      apply (subgoal_tac "is_aligned word pt_bits")
       apply (simp add: is_aligned_no_overflow)
      apply (simp add: pt_bits_def pageBits_def)
      apply simp
      apply (subst (asm) upto_enum_step_red [where us = 2, simplified])
      apply (simp add: pt_bits_def pageBits_def word_bits_conv)
      apply (simp add: pt_bits_def pageBits_def word_bits_conv)
      apply clarsimp
      apply (subst is_aligned_add_helper)
      apply (simp add: pt_bits_def pageBits_def)
      apply (erule word_less_power_trans_ofnat [where k = 2, simplified])
        apply (simp add: pt_bits_def pageBits_def)
       apply (simp add: pt_bits_def pageBits_def word_bits_conv)
      apply simp
      done
    done
  done

crunch pas_refined[wp]: invalidate_asid_entry "pas_refined aag"
  (wp: crunch_wps simp: crunch_simps)

crunch pas_refined[wp]: flush_space "pas_refined aag"
  (wp: crunch_wps simp: crunch_simps)

lemma delete_asid_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> delete_asid asid pd \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: delete_asid_def)
  apply (wp | wpc)+
  apply (clarsimp simp add: split_def Ball_def obj_at_def)
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD graph_ofD)
   apply (erule pas_refined_mem[OF sta_vref, rotated])
   apply (fastforce simp: state_vrefs_def vs_refs_no_global_pts_def
                         image_def graph_of_def split: if_split_asm)
  apply (clarsimp simp: pas_refined_def dest!: graph_ofD)
  apply (erule subsetD, erule state_asids_to_policy_aux.intros)
  apply (fastforce simp: state_vrefs_def vs_refs_no_global_pts_def
                        graph_of_def image_def split: if_split_asm)
  done

lemma delete_asid_pool_pas_refined [wp]:
  "\<lbrace>pas_refined aag\<rbrace> delete_asid_pool param_a param_b \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  unfolding delete_asid_pool_def
  apply (wp | wpc | simp)+
  apply (rule_tac Q = "\<lambda>_ s. pas_refined aag s \<and> asid_table = arm_asid_table (arch_state s)" in hoare_post_imp)
  apply clarsimp
  apply (erule pas_refined_clear_asid)
  apply (wp mapM_wp' | simp)+
  done

crunch respects[wp]: invalidate_asid_entry "integrity aag X st"

crunch respects[wp]: flush_space "integrity aag X st"
  (ignore: do_machine_op simp: invalidateLocalTLB_ASID_def cleanCaches_PoU_def dsb_def clean_D_PoU_def invalidate_I_PoU_def do_machine_op_bind)

lemma delete_asid_pool_respects[wp]:
  "\<lbrace> integrity aag X st and K (\<forall>asid'.
            asid' \<noteq> 0 \<and> asid_high_bits_of asid' = asid_high_bits_of x \<longrightarrow>
            is_subject_asid aag asid')\<rbrace>
   delete_asid_pool x y
   \<lbrace> \<lambda>_. integrity aag X st \<rbrace>"
  unfolding delete_asid_pool_def
  apply simp
  apply (wp mapM_wp[OF _ subset_refl] | simp)+
  done


lemma pas_refined_asid_mem:
  "\<lbrakk> v \<in> state_asids_to_policy aag s; pas_refined aag s \<rbrakk>
         \<Longrightarrow> v \<in> pasPolicy aag"
  by (auto simp add: pas_refined_def)


lemma set_asid_pool_respects_clear:
  "\<lbrace>(\<lambda>s. \<forall>pool'. ko_at (ArchObj (arch_kernel_obj.ASIDPool pool')) ptr s
              \<longrightarrow> asid_pool_integrity {pasSubject aag} aag pool' pool)
            and integrity aag X st\<rbrace>
     set_asid_pool ptr pool \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong
              simp: obj_at_def a_type_def
             split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm if_splits)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def)
  apply (rule tro_arch; fastforce simp: arch_integrity_obj_atomic.simps)
  done

lemma delete_asid_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and invs and K (is_subject aag pd)\<rbrace>
     delete_asid asid pd
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  by (wpsimp wp: set_asid_pool_respects_clear hoare_vcg_all_lift
           simp: obj_at_def pas_refined_refl delete_asid_def asid_pool_integrity_def)

end

end
