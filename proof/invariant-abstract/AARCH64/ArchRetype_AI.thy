(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 Arch-specific retype invariants
*)

theory ArchRetype_AI
imports Retype_AI
begin

context Arch begin global_naming AARCH64

named_theorems Retype_AI_assms

lemma arch_kobj_size_cong[Retype_AI_assms]:
"\<lbrakk>a = a1; c=c1\<rbrakk> \<Longrightarrow> arch_kobj_size (default_arch_object a b c)
  = arch_kobj_size (default_arch_object a1 b1 c1)"
  by (simp add: default_arch_object_def split: aobject_type.splits)


lemma clearMemoryVM_return[simp, Retype_AI_assms]:
  "clearMemoryVM a b = return ()"
  by (simp add: clearMemoryVM_def)

lemma slot_bits_def2 [Retype_AI_assms]: "slot_bits = cte_level_bits"
  by (simp add: slot_bits_def cte_level_bits_def)

definition
  "no_gs_types \<equiv> UNIV - {CapTableObject,
                         ArchObject SmallPageObj, ArchObject LargePageObj, ArchObject HugePageObj,
                         ArchObject PageTableObj, ArchObject VSpaceObj}"

lemma no_gs_types_simps [simp, Retype_AI_assms]:
  "Untyped \<in> no_gs_types"
  "TCBObject \<in> no_gs_types"
  "EndpointObject \<in> no_gs_types"
  "NotificationObject \<in> no_gs_types"
  "ArchObject ASIDPoolObj \<in> no_gs_types"
  by (simp_all add: no_gs_types_def)

lemma retype_region_ret_folded [Retype_AI_assms]:
  "\<lbrace>\<top>\<rbrace> retype_region y n bits ty dev
   \<lbrace>\<lambda>r s. r = retype_addrs y ty n bits\<rbrace>"
  unfolding retype_region_def
  apply (simp add: pageBits_def)
  apply wp
   apply (simp add:retype_addrs_def)
  done

crunches init_arch_objects
  for pspace_aligned[wp]:  "pspace_aligned"
  and pspace_distinct[wp]: "pspace_distinct"
  and mdb_inv[wp]: "\<lambda>s. P (cdt s)"
  and valid_mdb[wp]: "valid_mdb"
  and cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (ignore: clearMemory wp: crunch_wps)

crunch mdb_inv[wp]: store_pte "\<lambda>s. P (cdt s)"
  (ignore: clearMemory wp: crunch_wps)

lemma valid_vspace_objs_pte:
  "\<lbrakk> ptes_of s pt_t p = Some pte; valid_vspace_objs s; \<exists>\<rhd> (level, table_base pt_t p) s \<rbrakk>
   \<Longrightarrow> valid_pte level pte s \<or> level = max_pt_level \<and> table_index pt_t p \<in> kernel_mapping_slots"
  apply (clarsimp simp: ptes_of_def in_opt_map_eq)
  apply (drule (2) valid_vspace_objsD)
   apply (fastforce simp: in_opt_map_eq)
  apply simp
  done

lemma get_pte_valid[wp]:
  "\<lbrace>valid_vspace_objs and \<exists>\<rhd> (level, table_base pt_t p) and
    K (level = max_pt_level \<longrightarrow> ucast (table_index pt_t p) \<notin> invalid_mapping_slots)\<rbrace>
   get_pte pt_t p
   \<lbrace>valid_pte level\<rbrace>"
  by wpsimp (fastforce dest: valid_vspace_objs_pte)

lemma get_pte_wellformed[wp]:
  "\<lbrace>valid_objs\<rbrace> get_pte pt_t p \<lbrace>\<lambda>rv _. wellformed_pte rv\<rbrace>"
  apply wpsimp
  apply (fastforce simp: valid_objs_def dom_def valid_obj_def ptes_of_def in_opt_map_eq)
  done

crunch valid_objs[wp]: init_arch_objects "valid_objs"
  (ignore: clearMemory wp: crunch_wps)

crunch valid_arch_state[wp]: init_arch_objects "valid_arch_state"
  (ignore: clearMemory set_object wp: crunch_wps)

lemmas init_arch_objects_valid_cap[wp] = valid_cap_typ [OF init_arch_objects_typ_at]

lemmas init_arch_objects_cap_table[wp] = cap_table_at_lift_valid [OF init_arch_objects_typ_at]

crunch device_state_inv[wp]: clearMemory "\<lambda>ms. P (device_state ms)"
  (wp: mapM_x_wp ignore_del: clearMemory)

crunch pspace_respects_device_region[wp]: reserve_region pspace_respects_device_region
crunch cap_refs_respects_device_region[wp]: reserve_region cap_refs_respects_device_region

crunch invs [wp]: reserve_region "invs"

lemma dmo_eq_kernel_restricted [wp, Retype_AI_assms]:
  "\<lbrace>\<lambda>s. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>
       do_machine_op m
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>"
  unfolding do_machine_op_def equal_kernel_mappings_def
  by (wpsimp simp: in_omonad vspace_for_asid_def pool_for_asid_def)

definition
  "post_retype_invs_check tp \<equiv> False"

declare post_retype_invs_check_def[simp]

end


context begin interpretation Arch .
requalify_consts post_retype_invs_check
end

definition
  post_retype_invs :: "apiobject_type \<Rightarrow> obj_ref list \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "post_retype_invs tp refs \<equiv>
      if post_retype_invs_check tp
        then all_invs_but_equal_kernel_mappings_restricted (set refs)
        else invs"

global_interpretation Retype_AI_post_retype_invs?: Retype_AI_post_retype_invs
  where post_retype_invs_check = post_retype_invs_check
    and post_retype_invs = post_retype_invs
  by (unfold_locales; fact post_retype_invs_def)


context Arch begin global_naming AARCH64

lemma init_arch_objects_invs_from_restricted:
  "\<lbrace>post_retype_invs new_type refs
         and (\<lambda>s. global_refs s \<inter> set refs = {})
         and K (\<forall>ref \<in> set refs. is_aligned ref (obj_bits_api new_type obj_sz))\<rbrace>
     init_arch_objects new_type ptr bits obj_sz refs
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: init_arch_objects_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_Ball_lift
             valid_irq_node_typ
                  | wpc)+
  apply (auto simp: post_retype_invs_def)
  done


lemma obj_bits_api_neq_0 [Retype_AI_assms]:
  "ty \<noteq> Untyped \<Longrightarrow> 0 < obj_bits_api ty us"
  unfolding obj_bits_api_def
  by (clarsimp simp: slot_bits_def default_arch_object_def bit_simps
               split: apiobject_type.splits aobject_type.splits)

end


global_interpretation Retype_AI_slot_bits?: Retype_AI_slot_bits
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; fact Retype_AI_assms)
  qed


context Arch begin global_naming AARCH64

lemma valid_untyped_helper [Retype_AI_assms]:
  assumes valid_c : "s  \<turnstile> c"
  and   cte_at  : "cte_wp_at ((=) c) q s"
  and     tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  and   cover  : "range_cover ptr sz (obj_bits_api ty us) n"
  and   range  : "is_untyped_cap c \<Longrightarrow> usable_untyped_range c \<inter> {ptr..ptr + of_nat (n * 2 ^ (obj_bits_api ty us)) - 1} = {}"
  and     pn   : "pspace_no_overlap_range_cover ptr sz s"
  and     cn   : "caps_no_overlap ptr sz s"
  and     vp   : "valid_pspace s"
  shows "valid_cap c
           (s\<lparr>kheap := \<lambda>x. if x \<in> set (retype_addrs ptr ty n us) then Some (default_object ty dev us) else kheap s x\<rparr>)"
  (is "valid_cap c ?ns")
  proof -
  have obj_at_pres: "\<And>P x. obj_at P x s \<Longrightarrow> obj_at P x ?ns"
  by (clarsimp simp: obj_at_def dest: domI)
   (erule pspace_no_overlapC [OF pn _ _ cover vp])
  note blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff
  have cover':"range_cover ptr sz (obj_bits (default_object ty dev us)) n"
    using cover tyunt
    by (clarsimp simp:obj_bits_dev_irr)

  show ?thesis
  using cover valid_c range usable_range_emptyD[where cap = c] cte_at
  apply (clarsimp simp: valid_cap_def valid_arch_cap_ref_def elim!: obj_at_pres
                 split: cap.splits option.splits arch_cap.splits)
    defer
    apply (fastforce elim!: obj_at_pres)
   apply (fastforce elim!: obj_at_pres)
  apply (rename_tac word nat1 nat2)
  apply (clarsimp simp:valid_untyped_def is_cap_simps obj_at_def split:if_split_asm)
   apply (thin_tac "\<forall>x. Q x" for Q)
   apply (frule retype_addrs_obj_range_subset_strong[where dev=dev, OF _ _ tyunt])
    apply (simp add: obj_bits_dev_irr tyunt)
   apply (frule usable_range_subseteq)
    apply (simp add:is_cap_simps)
   apply (clarsimp simp:cap_aligned_def split:if_split_asm)
   apply (frule aligned_ranges_subset_or_disjoint)
    apply (erule retype_addrs_aligned[where sz = sz])
      apply (simp add: range_cover_def)
     apply (simp add: range_cover_def word_bits_def)
    apply (simp add: range_cover_def)
   apply (clarsimp simp: default_obj_range Int_ac tyunt
                  split: if_split_asm)
   apply (elim disjE)
    apply (drule(2) subset_trans[THEN disjoint_subset2])
    apply (drule Int_absorb2)+
    apply (simp add:is_cap_simps free_index_of_def)
   apply simp
   apply (drule(1) disjoint_subset2[rotated])
   apply (simp add:Int_ac)
  apply (thin_tac "\<forall>x. Q x" for Q)
  apply (frule retype_addrs_obj_range_subset[OF _ cover' tyunt])
  apply (clarsimp simp:cap_aligned_def)
  apply (frule aligned_ranges_subset_or_disjoint)
   apply (erule retype_addrs_aligned[where sz = sz])
     apply (simp add: range_cover_def)
    apply (simp add: range_cover_def word_bits_def)
   apply (simp add: range_cover_def)
  apply (clarsimp simp: default_obj_range Int_ac tyunt
                 split: if_split_asm)
  apply (erule disjE)
   apply (simp add: cte_wp_at_caps_of_state)
   apply (drule cn[unfolded caps_no_overlap_def,THEN bspec,OF ranI])
   apply (simp add: p_assoc_help[symmetric])
   apply (erule impE)
    apply blast (* set arith *)
   apply blast (* set arith *)
  apply blast (* set arith  *)
  done
  qed

lemma valid_default_arch_tcb:
  "\<And>s. valid_arch_tcb default_arch_tcb s"
  by (simp add: default_arch_tcb_def valid_arch_tcb_def)

end


global_interpretation Retype_AI_valid_untyped_helper?: Retype_AI_valid_untyped_helper
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; fact Retype_AI_assms)
  qed


locale retype_region_proofs_arch
  = retype_region_proofs s ty us ptr sz n ps s' dev
  + Arch
  for s :: "'state_ext :: state_ext state"
  and ty us ptr sz n ps s' dev


context retype_region_proofs begin

interpretation Arch .

lemma valid_cap:
  assumes cap:
    "(s::'state_ext state) \<turnstile> cap \<and> untyped_range cap \<inter> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} = {}"
  shows "s' \<turnstile> cap"
  proof -
  note blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff
  have cover':"range_cover ptr sz (obj_bits (default_object ty dev us)) n"
    using cover tyunt
    by (clarsimp simp: obj_bits_dev_irr)
  show ?thesis
    unfolding valid_cap_def
    using cap
    apply (case_tac cap)
               apply (simp_all add: valid_cap_def obj_at_pres cte_at_pres valid_arch_cap_ref_def
                               split: option.split_asm arch_cap.split_asm option.splits)
    apply (clarsimp simp add: valid_untyped_def ps_def s'_def)
    apply (rule conjI)
     apply clarsimp
     apply (drule disjoint_subset [OF retype_addrs_obj_range_subset [OF _ cover' tyunt]])
      apply (simp add: Int_ac p_assoc_help[symmetric])
     apply simp
    apply clarsimp
    apply (drule disjoint_subset [OF retype_addrs_obj_range_subset [OF _ cover' tyunt]])
     apply (simp add: Int_ac p_assoc_help[symmetric])
    apply simp
    done
  qed

lemma valid_global_refs:
  "valid_global_refs s \<Longrightarrow> valid_global_refs s'"
  apply (simp add: valid_global_refs_def valid_refs_def global_refs_def idle_s')
  apply (simp add: cte_retype cap_range_def)
  done

lemma asid_pools:
  "asid_pools_of s p = Some pool \<Longrightarrow> asid_pools_of s' p = Some pool"
  by (clarsimp simp: in_opt_map_eq s'_def ps_def)
     (erule pspace_no_overlapC [OF orth _ _ cover vp])

lemma asid_pools_of':
  "asid_pools_of s' p = Some ap \<Longrightarrow>
   asid_pools_of s p = Some ap \<or> ap = Map.empty \<and> p \<in> set (retype_addrs ptr ty n us)"
  apply (clarsimp simp: in_opt_map_eq s'_def ps_def split: if_split_asm)
  apply (auto simp: default_object_def default_arch_object_def empty_pt_def tyunt
              split: apiobject_type.splits aobject_type.splits)
  done

lemma pts_of:
  "pts_of s p = Some pt \<Longrightarrow> pts_of s' p = Some pt"
  by (clarsimp simp: in_opt_map_eq s'_def ps_def)
     (erule pspace_no_overlapC [OF orth _ _ cover vp])

lemma pts_of':
  "pts_of s' p = Some pt \<Longrightarrow>
   pts_of s p = Some pt \<or> pt = (empty_pt (pt_type pt)) \<and> p \<in> set (retype_addrs ptr ty n us)"
  apply (clarsimp simp: in_opt_map_eq s'_def ps_def split: if_split_asm)
  apply (auto simp: default_object_def default_arch_object_def empty_pt_def tyunt
              split: apiobject_type.splits aobject_type.splits)
  done

lemma valid_asid_table:
  "valid_asid_table s \<Longrightarrow> valid_asid_table s'"
  unfolding valid_asid_table_def by (auto simp: asid_pools)

lemma valid_global_arch_objs:
  "valid_global_arch_objs s \<Longrightarrow> valid_global_arch_objs s'"
  by (fastforce simp: valid_global_arch_objs_def pt_at_eq pts_of)

lemma ptes_of:
  "ptes_of s pt_t p = Some pte \<Longrightarrow> ptes_of s' pt_t p = Some pte"
  by (auto simp: level_pte_of_def obind_def pts_of if_option split: option.splits)

lemma default_empty:
  "default_object ty dev us = ArchObj (PageTable pt) \<Longrightarrow> pt = (empty_pt (pt_type pt))"
  by (auto simp: default_object_def default_arch_object_def empty_pt_def tyunt
           split: apiobject_type.splits aobject_type.splits)

lemma ptes_of':
  "ptes_of s' pt_t p = Some pte \<Longrightarrow> ptes_of s pt_t p = Some pte \<or> pte = InvalidPTE"
  by (cases pt_t;
      fastforce simp: level_pte_of_def in_omonad s'_def ps_def split: if_splits dest: default_empty)

lemma pt_walk:
  "pt_walk top_level bot_level pt vref (ptes_of s) = Some (level, p) \<Longrightarrow>
   pt_walk top_level bot_level pt vref (ptes_of s') = Some (level, p)"
  apply (induct top_level arbitrary: pt)
   apply simp
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_splits)
   prefer 2
   apply (subst pt_walk.simps)
   apply (simp add: in_omonad)
  apply (erule disjE; clarsimp)
   prefer 2
   apply (subst pt_walk.simps)
   apply (simp add: in_omonad)
   apply (rule_tac x=v' in exI)
   apply (simp add: ptes_of)
  apply (drule ptes_of)
  apply (subst pt_walk.simps)
  apply (simp add: in_omonad)
  done

lemma pt_walk':
  "pt_walk top_level level pt vref (ptes_of s') = Some (level, p) \<Longrightarrow>
   pt_walk top_level level pt vref (ptes_of s) = Some (level, p)"
  apply (induct top_level arbitrary: pt)
   apply simp
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_splits)
  apply (erule disjE; clarsimp)
  apply (drule ptes_of')
  apply (subst pt_walk.simps)
  apply (fastforce simp add: in_omonad)
  done

lemma pt_walk_eq[simp]:
  "(pt_walk top_level level pt_ptr vptr (ptes_of s') = Some (level, p)) =
   (pt_walk top_level level pt_ptr vptr (ptes_of s) = Some (level, p))"
  apply (rule iffI)
   apply (erule pt_walk')
  apply (erule pt_walk)
  done

lemma global_no_retype:
  "\<lbrakk> pt_ptr \<in> global_refs s; valid_global_refs s \<rbrakk> \<Longrightarrow> pt_ptr \<notin> set (retype_addrs ptr ty n us)"
  using dev retype_addrs_subset_ptr_bits[OF cover]
  by (fastforce simp: valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)

lemma global_pts_no_retype:
  "valid_global_refs s \<Longrightarrow> global_pt s \<notin> set (retype_addrs ptr ty n us)"
  by (erule global_no_retype[rotated], simp add: valid_global_refs_def)

lemma vcpu_hyp_live_of':
  "vcpu_hyp_live_of s' = vcpu_hyp_live_of s"
  apply (clarsimp simp: in_opt_map_eq s'_def ps_def split: if_split_asm)
  apply (clarsimp del: ext intro!: ext split: option.splits)
  apply (rule iffI; clarsimp simp: in_omonad split: if_splits)
   apply (fastforce simp: default_object_def default_arch_object_def default_vcpu_def tyunt
                    split: apiobject_type.splits aobject_type.splits)
  apply (erule (1) pspace_no_overlapC[OF orth _ _ cover vp])
  done

lemma dom_vmid_for_asid[simplified]:
  "dom (vmid_for_asid s') = dom (vmid_for_asid s)"
  apply (clarsimp simp: dom_def s'_def ps_def obj_at_def vmid_for_asid_def in_omonad
                  split: if_split_asm)
  apply (rule set_eqI)
  apply (rule iffI; clarsimp simp: entry_for_pool_def in_omonad split: if_split_asm)
   apply (fastforce simp: default_object_def default_arch_object_def default_vcpu_def tyunt
                    split: apiobject_type.splits aobject_type.splits)
  apply (fastforce elim: pspace_no_overlapC[OF orth _ _ cover vp])
  done

lemma vmid_inv':
  "vmid_inv s \<Longrightarrow> vmid_inv s'"
  by (clarsimp simp: vmid_inv_def is_inv_def dom_vmid_for_asid)
     (fastforce simp: s'_def ps_def vmid_for_asid_def entry_for_pool_def in_omonad
                elim!: pspace_no_overlapC[OF orth _ _ cover vp])

lemma valid_global_tables':
  "valid_global_tables s \<Longrightarrow> valid_global_tables s'"
  unfolding valid_global_tables_2_def
  by (simp add: pts_of)

lemma valid_arch_state:
  "valid_arch_state s \<Longrightarrow> valid_arch_state s'"
  apply (simp add: valid_arch_state_def valid_asid_table vcpu_hyp_live_of' vmid_inv'
                   valid_global_arch_objs valid_global_tables'
              del: arch_state)
  apply simp
  done

lemma vspace_for_pool1:
  "(vspace_for_pool asid p (asid_pools_of s) = Some pt) \<Longrightarrow>
   vspace_for_pool asid p (asid_pools_of s') = Some pt"
  by (simp add: vspace_for_pool_def entry_for_pool_def asid_pools obind_def split: option.splits)

lemma vspace_for_pool2:
  "vspace_for_pool asid p (asid_pools_of s') = Some pt \<Longrightarrow>
   vspace_for_pool asid p (asid_pools_of s) = Some pt"
  apply (clarsimp simp: vspace_for_pool_def entry_for_pool_def in_omonad s'_def ps_def
                  split: if_split_asm)
  apply (clarsimp simp: default_object_def default_arch_object_def tyunt
                  split: apiobject_type.splits aobject_type.splits)
  done

lemma vspace_for_pool[simp]:
  "(vspace_for_pool asid p (asid_pools_of s') = Some pt) =
   (vspace_for_pool asid p (asid_pools_of s) = Some pt)"
  by (rule iffI, erule vspace_for_pool2, erule vspace_for_pool1)

lemma vs_lookup_table':
  "(vs_lookup_table level asid vref s' = Some (level, p)) =
   (vs_lookup_table level asid vref s = Some (level, p))"
  by (fastforce simp: vs_lookup_table_def in_omonad pool_for_asid_def split: if_split_asm)

lemma vs_lookup_target':
  "(vs_lookup_target level asid vref s' = Some (level,p)) =
   (vs_lookup_target level asid vref s = Some (level,p))"
  unfolding vs_lookup_target_def vs_lookup_slot_def
  supply vs_lookup_table'[simp]
  apply (clarsimp simp: in_omonad)
  apply (cases "level = asid_pool_level"; clarsimp)
   apply fastforce
  apply (rule iffI; clarsimp simp: asid_pool_level_eq)
   apply (fastforce dest: ptes_of')
  apply (fastforce dest: ptes_of)
  done

lemma wellformed_default_obj[Retype_AI_assms]:
   "\<lbrakk> ptr' \<notin> set (retype_addrs ptr ty n us);
      kheap s ptr' = Some (ArchObj ao); arch_valid_obj ao s\<rbrakk> \<Longrightarrow>
    arch_valid_obj ao s'"
  by (cases ao; clarsimp elim!: obj_at_pres simp: valid_vcpu_def
                         split: arch_kernel_obj.splits option.splits)+

end


context retype_region_proofs_arch begin

lemma hyp_refs_eq:
  "state_hyp_refs_of s' = state_hyp_refs_of s"
  unfolding s'_def ps_def
  apply (rule ext)
  apply (clarsimp simp: state_hyp_refs_of_def orthr split: option.splits)
  apply (cases ty; simp add: tyunt default_object_def default_tcb_def hyp_refs_of_def tcb_hyp_refs_def
                             default_arch_tcb_def)
  apply (clarsimp simp: refs_of_ao_def vcpu_tcb_refs_def default_arch_object_def default_vcpu_def
                  split: aobject_type.splits)
  done

lemma obj_at_valid_pte:
  "\<lbrakk>valid_pte level pte s; \<And>P p. obj_at P p s \<Longrightarrow> obj_at P p s'\<rbrakk>
   \<Longrightarrow> valid_pte level pte s'"
  apply (cases pte, simp_all add: valid_pte_def data_at_def)
  apply (clarsimp | elim disjE)+
  done

lemma valid_global_vspace_mappings:
  "valid_global_vspace_mappings s'"
  unfolding valid_global_vspace_mappings_def by simp

end


context retype_region_proofs begin

interpretation retype_region_proofs_arch ..

lemma valid_vspace_obj_pres:
  "valid_vspace_obj level ao s \<Longrightarrow> valid_vspace_obj level ao s'"
  by (cases ao; simp add: obj_at_pres)
     (fastforce intro: obj_at_valid_pte simp: obj_at_pres)

lemma valid_vspace_objs':
  assumes va: "valid_vspace_objs s"
  assumes asid: "valid_asid_table s"
  assumes pspace: "pspace_aligned s"
  shows "valid_vspace_objs s'"
proof
  fix level p ao asid vref
  assume p: "vs_lookup_table level asid (vref_for_level vref (level + 1)) s' = Some (level, p)"
  assume vref: "vref \<in> user_region"
  assume vsp: "vspace_objs_of s' p = Some ao"

  { assume "level = asid_pool_level"
    hence "valid_vspace_obj level ao s'" using va p vref vsp asid
      apply (simp add: vs_lookup_table')
      apply (frule (1) vs_lookup_asid_pool)
      apply (rule valid_vspace_obj_pres)
      apply (auto dest!: valid_vspace_objsD
                  simp: s'_def ps_def opt_map_def vref_for_level_user_region
                  split: option.splits if_split_asm
                  elim!: pspace_no_overlapC[OF orth _ _ cover vp])
      done
  }
  moreover {
    assume "level \<le> max_pt_level"
    hence "valid_vspace_obj level ao s'" using va p vref vsp pspace asid
      apply (simp add: vs_lookup_table')
      apply (drule (1) valid_vspace_objs_strongD; simp add: vref_for_level_user_region)
      apply (clarsimp simp: opt_map_def split: option.splits)
      apply (subst (asm) s'_def, subst (asm) ps_def)
      apply (clarsimp simp: split: if_split_asm)
       apply (erule (1) pspace_no_overlapC[OF orth _ _ cover vp])
      apply (fastforce intro: obj_at_valid_pte[OF _ obj_at_pres])
      done
  }
  ultimately show "valid_vspace_obj level ao s'"
    by fastforce
qed

sublocale retype_region_proofs_gen?: retype_region_proofs_gen
  by (unfold_locales,
        auto simp: hyp_refs_eq[simplified s'_def ps_def]
                  wellformed_default_obj[simplified s'_def ps_def]
                  valid_default_arch_tcb)

end


context Arch begin global_naming AARCH64

lemma unique_table_caps_null:
  "unique_table_caps_2 (null_filter caps)
       = unique_table_caps_2 caps"
  apply (simp add: unique_table_caps_def)
  apply (intro iff_allI)
  apply (clarsimp simp: null_filter_def)
  done


lemma unique_table_refs_null:
  "unique_table_refs_2 (null_filter caps)
       = unique_table_refs_2 caps"
  apply (simp only: unique_table_refs_def)
  apply (intro iff_allI)
  apply (clarsimp simp: null_filter_def)
  apply (auto dest!: obj_ref_none_no_asid[rule_format]
               simp: table_cap_ref_def)
  done


definition
  region_in_kernel_window :: "obj_ref set \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "region_in_kernel_window S \<equiv> \<lambda>s. S \<subseteq> kernel_window s"

lemma pspace_respects_device_regionI:
  assumes uat: "\<And>ptr sz. kheap s ptr = Some (ArchObj (DataPage False sz))
                \<Longrightarrow> obj_range ptr (ArchObj $ DataPage False sz) \<subseteq> - device_region s"
      and dat: "\<And>ptr sz. kheap s ptr = Some (ArchObj (DataPage True sz))
                \<Longrightarrow> obj_range ptr (ArchObj $ DataPage True sz) \<subseteq> device_region s"
      and inv:  "pspace_aligned s" "valid_objs s"
  shows "pspace_respects_device_region s"

  apply (simp add: pspace_respects_device_region_def,intro conjI)
  apply (rule subsetI)
   apply (clarsimp simp: dom_def user_mem_def obj_at_def in_user_frame_def split: if_split_asm)
   apply (frule uat)
   apply (cut_tac ko = "(ArchObj (DataPage False sz))" in p_in_obj_range_internal[OF _ inv])
    prefer 2
    apply (fastforce simp: obj_bits_def)
   apply simp
  apply (rule subsetI)
  apply (clarsimp simp: dom_def device_mem_def obj_at_def in_device_frame_def split: if_split_asm)
  apply (frule dat)
  apply (cut_tac ko = "(ArchObj (DataPage True sz))" in p_in_obj_range_internal[OF _ inv])
  prefer 2
   apply (fastforce simp: obj_bits_def)
  apply simp
  done

lemma obj_range_respect_device_range:
  "\<lbrakk>kheap s ptr = Some (ArchObj (DataPage dev sz));pspace_aligned s\<rbrakk> \<Longrightarrow>
  obj_range ptr (ArchObj $ DataPage dev sz) \<subseteq> (if dev then dom (device_mem s) else dom (user_mem s))"
  apply (drule(1) pspace_alignedD[rotated])
  apply (clarsimp simp: user_mem_def in_user_frame_def obj_at_def obj_range_def device_mem_def in_device_frame_def)
  apply (intro impI conjI)
   apply clarsimp
   apply (rule exI[where x = sz])
   apply (simp add: mask_in_range[symmetric,THEN iffD1] a_type_def)
  apply clarsimp
  apply (rule exI[where x = sz])
  apply (simp add: mask_in_range[symmetric,THEN iffD1] a_type_def)
  done

lemma pspace_respects_device_regionD:
  assumes inv:  "pspace_aligned s" "valid_objs s" "pspace_respects_device_region s"
  shows uat: "\<And>ptr sz. kheap s ptr = Some (ArchObj (DataPage False sz))
                \<Longrightarrow> obj_range ptr (ArchObj $ DataPage False sz) \<subseteq> - device_region s"
      and dat: "\<And>ptr sz. kheap s ptr = Some (ArchObj (DataPage True sz))
                \<Longrightarrow> obj_range ptr (ArchObj $ DataPage True sz) \<subseteq> device_region s"
  using inv
  apply (simp_all add: pspace_respects_device_region_def)
  apply (rule subsetI)
   apply (drule obj_range_respect_device_range[OF _ inv(1)])
   apply (clarsimp split: if_splits)
   apply (drule(1) subsetD[rotated])
   apply (drule(1) subsetD[rotated])
   apply (simp add: dom_def)
  apply (rule subsetI)
  apply (drule obj_range_respect_device_range[OF _ inv(1)])
  apply (clarsimp split: if_splits)
  apply (drule(1) subsetD[rotated])
  apply (drule(1) subsetD[rotated])
   apply (simp add: dom_def)
  done


lemma default_obj_dev:
  "\<lbrakk>ty \<noteq> Untyped;default_object ty dev us = ArchObj (DataPage dev' sz)\<rbrakk> \<Longrightarrow> dev = dev'"
  by (clarsimp simp: default_object_def default_arch_object_def
              split: apiobject_type.split_asm aobject_type.split_asm)

end


lemma cap_range_respects_device_region_cong[cong]:
  "device_state (machine_state s) = device_state (machine_state s')
  \<Longrightarrow> cap_range_respects_device_region cap s = cap_range_respects_device_region cap s'"
  by (clarsimp simp: cap_range_respects_device_region_def)


context begin interpretation Arch .
requalify_consts region_in_kernel_window
end


context retype_region_proofs_arch begin

lemmas unique_table_caps_eq
    = arg_cong[where f=unique_table_caps_2, OF null_filter,
               simplified unique_table_caps_null]

lemmas unique_table_refs_eq
    = arg_cong[where f=unique_table_refs_2, OF null_filter,
               simplified unique_table_refs_null]

lemma valid_table_caps:
  "valid_table_caps s \<Longrightarrow> valid_table_caps s'"
  unfolding valid_table_caps_def
  by (fastforce dest: caps_retype[rotated] intro: pts_of)

lemma caps_of_state':
  "caps_of_state s p = Some cap \<Longrightarrow> caps_of_state s' p = Some cap"
  by (fastforce simp: F cte_wp_at_cases s'_def ps_def orthr)

lemma valid_vs_lookup:
  "valid_vs_lookup s \<Longrightarrow> valid_vs_lookup s'"
  unfolding valid_vs_lookup_def
  apply clarsimp
  apply (drule vs_lookup_target_level)
  by (fastforce simp: vs_lookup_target' intro: caps_of_state')

lemma valid_asid_pool_caps:
  "valid_asid_pool_caps s \<Longrightarrow> valid_asid_pool_caps s'"
  by (fastforce intro: caps_of_state' simp: valid_asid_pool_caps_def)

lemma valid_arch_caps:
  "valid_arch_caps s \<Longrightarrow> valid_arch_caps s'"
  by (clarsimp simp add: valid_arch_caps_def null_filter valid_table_caps valid_vs_lookup
                         vs_lookup_target' unique_table_caps_eq unique_table_refs_eq
                         valid_asid_pool_caps
               simp del: arch_state)

lemma valid_kernel_mappings:
  "valid_kernel_mappings s \<Longrightarrow> valid_kernel_mappings s'"
  by (simp add: valid_kernel_mappings_def s'_def ball_ran_eq ps_def)

lemma valid_asid_map:
  "valid_asid_map s \<Longrightarrow> valid_asid_map s'"
  apply (clarsimp simp: valid_asid_map_def entry_for_asid_def obind_None_eq pool_for_asid_def
                        entry_for_pool_def)
  apply (fastforce dest!: asid_pools_of')
  done

lemma vspace_for_asid:
  "vspace_for_asid asid s' = Some pt \<Longrightarrow> vspace_for_asid asid s = Some pt"
  apply (clarsimp simp: s'_def ps_def vspace_for_asid_def entry_for_asid_def pool_for_asid_def
                        in_omonad entry_for_pool_def
                  split: if_split_asm)
  apply (fastforce simp: default_object_def default_arch_object_def tyunt
                   split: apiobject_type.splits aobject_type.splits)
  done

lemma equal_kernel_mappings:
  "equal_kernel_mappings s'"
  by (simp add: equal_kernel_mappings_def)

lemma pspace_in_kernel_window:
  "\<lbrakk> pspace_in_kernel_window (s :: 'state_ext state);
     region_in_kernel_window {ptr .. (ptr &&~~ mask sz) + 2 ^ sz - 1} s \<rbrakk>
          \<Longrightarrow> pspace_in_kernel_window s'"
  apply (simp add: pspace_in_kernel_window_def s'_def ps_def)
  apply (clarsimp simp: region_in_kernel_window_def
                   del: ballI)
  apply (drule retype_addrs_mem_subset_ptr_bits[OF cover tyunt])
  apply (fastforce simp: field_simps obj_bits_dev_irr tyunt)
  done

lemma pspace_respects_device_region:
  assumes psp_resp_dev: "pspace_respects_device_region s"
      and cap_refs_resp_dev: "cap_refs_respects_device_region s"
  shows "pspace_respects_device_region s'"
  proof -
    note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff
          atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  show ?thesis
  apply (cut_tac vp)
  apply (rule pspace_respects_device_regionI)
     apply (clarsimp simp add: pspace_respects_device_region_def s'_def ps_def
                        split: if_split_asm )
      apply (drule retype_addrs_obj_range_subset[OF _ _ tyunt])
       using cover tyunt
       apply (simp add: obj_bits_api_def3 split: if_splits)
      apply (frule default_obj_dev[OF tyunt],simp)
      apply (drule(1) subsetD)
      apply (rule exE[OF dev])
      apply (drule cap_refs_respects_device_region_cap_range[OF _ cap_refs_resp_dev])
      apply (fastforce split: if_splits)
     apply (drule pspace_respects_device_regionD[OF _ _ psp_resp_dev, rotated -1])
       apply fastforce
      apply fastforce
     apply fastforce
    apply (clarsimp simp add: pspace_respects_device_region_def s'_def ps_def
                       split: if_split_asm )
     apply (drule retype_addrs_obj_range_subset[OF _ _ tyunt])
      using cover tyunt
      apply (simp add: obj_bits_api_def4 split: if_splits)
     apply (frule default_obj_dev[OF tyunt],simp)
      apply (drule(1) subsetD)
      apply (rule exE[OF dev])
      apply (drule cap_refs_respects_device_region_cap_range[OF _ cap_refs_resp_dev])
      apply (fastforce split: if_splits)
     apply (drule pspace_respects_device_regionD[OF _ _ psp_resp_dev, rotated -1])
       apply fastforce
      apply fastforce
     apply fastforce
  using valid_pspace
  apply fastforce+
  done
qed



lemma cap_refs_respects_device_region:
  assumes psp_resp_dev: "pspace_respects_device_region s"
      and cap_refs_resp_dev: "cap_refs_respects_device_region s"
  shows "cap_refs_respects_device_region s'"
  using cap_refs_resp_dev
  apply (clarsimp simp: cap_refs_respects_device_region_def
              simp del: split_paired_All split_paired_Ex)
  apply (drule_tac x = "(a,b)" in spec)
  apply (erule notE)
  apply (subst(asm) cte_retype)
   apply (simp add: cap_range_respects_device_region_def cap_range_def)
  apply (clarsimp simp: cte_wp_at_caps_of_state s'_def dom_def)
  done


lemma vms:
  "valid_machine_state s \<Longrightarrow> valid_machine_state s'"
  apply (simp add: s'_def ps_def valid_machine_state_def in_user_frame_def)
  apply (rule allI, erule_tac x=p in allE, clarsimp)
  apply (rule_tac x=sz in exI, clarsimp simp: obj_at_def orthr)
  done

end


context retype_region_proofs begin

interpretation retype_region_proofs_arch ..

lemma post_retype_invs:
  "\<lbrakk> invs s; region_in_kernel_window {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} s \<rbrakk>
        \<Longrightarrow> post_retype_invs ty (retype_addrs ptr ty n us) s'"
  using equal_kernel_mappings valid_global_vspace_mappings
  apply (clarsimp simp: invs_def post_retype_invs_def valid_state_def
                     unsafe_rep2 null_filter valid_idle
                     valid_reply_caps valid_reply_masters
                     valid_global_refs valid_arch_state
                     valid_irq_node_def obj_at_pres
                     valid_arch_caps valid_global_objs_def
                     valid_vspace_objs'[OF _ valid_arch_state_asid_table valid_pspace_aligned2]
                     valid_irq_handlers
                     valid_mdb_rep2 mdb_and_revokable
                     valid_pspace cur_tcb only_idle
                     valid_kernel_mappings valid_asid_map
                     valid_ioc vms
                     pspace_in_kernel_window
                     pspace_respects_device_region
                     cap_refs_respects_device_region
                     cap_refs_in_kernel_window valid_irq_states
               split: if_split_asm)
  done

(* ML \<open>val pre_ctxt_1 = @{context}\<close> *)

sublocale retype_region_proofs_invs?: retype_region_proofs_invs
  where region_in_kernel_window = region_in_kernel_window
    and post_retype_invs_check = post_retype_invs_check
    and post_retype_invs = post_retype_invs
  using post_retype_invs valid_cap valid_global_refs valid_arch_state
        valid_vspace_objs'[OF _ invs_valid_asid_table invs_psp_aligned]
  by unfold_locales (auto simp: s'_def ps_def)

(* local_setup \<open>note_new_facts pre_ctxt_1\<close> *)

lemmas post_retype_invs_axioms = retype_region_proofs_invs_axioms

end


context Arch begin global_naming AARCH64

named_theorems Retype_AI_assms'

lemma invs_post_retype_invs [Retype_AI_assms']:
  "invs s \<Longrightarrow> post_retype_invs ty refs s"
  by (clarsimp simp: post_retype_invs_def)

lemmas equal_kernel_mappings_trans_state
  = more_update.equal_kernel_mappings_update

lemmas retype_region_proofs_assms [Retype_AI_assms']
  = retype_region_proofs.post_retype_invs_axioms

end


global_interpretation Retype_AI?: Retype_AI
  where no_gs_types = AARCH64.no_gs_types
    and post_retype_invs_check = post_retype_invs_check
    and post_retype_invs = post_retype_invs
    and region_in_kernel_window = region_in_kernel_window
  proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact Retype_AI_assms)?)
     (simp add: Retype_AI_axioms_def Retype_AI_assms')
  qed


context Arch begin global_naming AARCH64

lemma retype_region_plain_invs:
  "\<lbrace>invs and caps_no_overlap ptr sz and pspace_no_overlap_range_cover ptr sz
      and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
      and region_in_kernel_window {ptr .. (ptr &&~~ mask sz) + 2 ^ sz - 1}
      and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
      and K (ty = Structures_A.CapTableObject \<longrightarrow> 0 < us)
      and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty dev \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_strengthen_post[OF retype_region_post_retype_invs])
  apply (simp add: post_retype_invs_def)
  done


lemma storeWord_um_eq_0:
  "storeWord x 0 \<lbrace>\<lambda>m. underlying_memory m p = 0\<rbrace>"
  by (wpsimp simp: storeWord_def word_rsplit_0 upto_rec1 word_bits_def)

lemma clearMemory_um_eq_0:
  "\<lbrace>\<lambda>m. underlying_memory m p = 0\<rbrace>
    clearMemory ptr bits
   \<lbrace>\<lambda>_ m. underlying_memory m p = 0\<rbrace>"
  apply (clarsimp simp: clearMemory_def)
  including no_pre apply (wpsimp wp: mapM_x_wp_inv)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps storeWord_um_eq_0)
  apply (fastforce simp: ignore_failure_def split: if_split_asm)
  done

lemma invs_irq_state_independent:
  "invs (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = invs s"
  by (clarsimp simp: irq_state_independent_A_def invs_def
                     valid_state_def valid_pspace_def valid_mdb_def valid_ioc_def valid_idle_def
                     only_idle_def if_unsafe_then_cap_def valid_reply_caps_def
                     valid_reply_masters_def valid_global_refs_def valid_arch_state_def
                     valid_irq_node_def valid_irq_handlers_def valid_machine_state_def
                     valid_vspace_objs_def valid_arch_caps_def
                     valid_kernel_mappings_def equal_kernel_mappings_def
                     valid_asid_map_def vspace_at_asid_def
                     pspace_in_kernel_window_def cap_refs_in_kernel_window_def
                     cur_tcb_def sym_refs_def state_refs_of_def state_hyp_refs_of_def
                     swp_def valid_irq_states_def
              split: option.split)

crunch irq_masks_inv[wp]: storeWord, clearMemory "\<lambda>s. P (irq_masks s)"
  (wp: crunch_wps ignore_del: storeWord clearMemory)

crunch underlying_mem_0[wp]: clearMemory "\<lambda>s. underlying_memory s p = 0"
  (wp: crunch_wps storeWord_um_eq_0 ignore_del: clearMemory)

lemma clearMemory_invs:
  "\<lbrace>invs\<rbrace> do_machine_op (clearMemory w sz) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs1)
  apply clarsimp
  apply (intro conjI impI allI)
   apply (clarsimp simp: invs_def valid_state_def)
   apply (erule_tac p=p in valid_machine_stateE)
   apply (clarsimp simp: use_valid[OF _ clearMemory_underlying_mem_0])
  apply (clarsimp simp: use_valid[OF _ clearMemory_irq_masks_inv[where P="(=) v" for v], OF _ refl])
  done

lemma caps_region_kernel_window_imp:
  "caps_of_state s p = Some cap
    \<Longrightarrow> cap_refs_in_kernel_window s
    \<Longrightarrow> S \<subseteq> cap_range cap
    \<Longrightarrow> region_in_kernel_window S s"
  apply (simp add: region_in_kernel_window_def)
  apply (drule(1) cap_refs_in_kernel_windowD)
  apply blast
  done

crunch irq_node[wp]: init_arch_objects "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

lemma init_arch_objects_excap:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace>
      init_arch_objects tp ptr bits us refs
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to P p s\<rbrace>"
  by (wp ex_cte_cap_to_pres)

crunch pred_tcb_at[wp]: init_arch_objects "pred_tcb_at proj P t"
  (wp: crunch_wps)

lemma valid_arch_mdb_detype:
  "valid_arch_mdb (is_original_cap s) (caps_of_state s) \<Longrightarrow>
            valid_arch_mdb (is_original_cap (detype (untyped_range cap) s))
         (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
  by (auto simp: valid_arch_mdb_def)

lemmas init_arch_objects_wps
    = init_arch_objects_cte_wp_at
      init_arch_objects_valid_cap
      init_arch_objects_cap_table
      init_arch_objects_excap
      init_arch_objects_pred_tcb_at

end

end
