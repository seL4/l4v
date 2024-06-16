(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchArch_AI
imports Arch_AI
begin

unbundle l4v_word_context

context Arch begin global_naming RISCV64

definition
  "valid_aci aci \<equiv> case aci of MakePool frame slot parent base \<Rightarrow>
     \<lambda>s. cte_wp_at (\<lambda>c. c = NullCap) slot s \<and> real_cte_at slot s \<and>
         ex_cte_cap_wp_to is_cnode_cap slot s \<and>
         slot \<noteq> parent \<and>
         cte_wp_at (\<lambda>cap. \<exists>idx. cap = UntypedCap False frame pageBits idx) parent s \<and>
         descendants_of parent (cdt s) = {} \<and>
         is_aligned base asid_low_bits \<and>
         asid_table s (asid_high_bits_of base) = None"

lemma safe_parent_strg:
  "cte_wp_at (\<lambda>cap. cap = UntypedCap False frame pageBits idx) p s \<and>
   descendants_of p (cdt s) = {} \<and>
   valid_objs s
  \<longrightarrow>
  cte_wp_at (safe_parent_for (cdt s) p
             (ArchObjectCap (ASIDPoolCap frame base)))
             p s"
  apply (clarsimp simp: cte_wp_at_caps_of_state safe_parent_for_def is_physical_def arch_is_physical_def)
  apply (rule is_aligned_no_overflow)
  apply (drule (1) caps_of_state_valid_cap)
  apply (clarsimp simp: valid_cap_def cap_aligned_def)
  done

lemma range_cover_full:
  "\<lbrakk>is_aligned ptr sz; sz<word_bits\<rbrakk> \<Longrightarrow> range_cover (ptr::machine_word) sz sz (Suc 0)"
   by (clarsimp simp:range_cover_def unat_eq_0 le_mask_iff[symmetric] word_and_le1 word_bits_def)


definition
  valid_arch_inv :: "arch_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_inv ai \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> valid_pti pti
   | InvokePage pgi \<Rightarrow> valid_page_inv pgi
   | InvokeASIDControl aci \<Rightarrow> valid_aci aci
   | InvokeASIDPool api \<Rightarrow> valid_apinv api"

lemma check_vp_wpR [wp]:
  "\<lbrace>\<lambda>s. vmsz_aligned w sz \<longrightarrow> P () s\<rbrace>
  check_vp_alignment sz w \<lbrace>P\<rbrace>, -"
  apply (simp add: check_vp_alignment_def unlessE_whenE cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp whenE_wp|wpc)+
  apply (simp add: vmsz_aligned_def)
  done


lemma check_vp_inv: "\<lbrace>P\<rbrace> check_vp_alignment sz w \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: check_vp_alignment_def unlessE_whenE cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp whenE_wp|wpc)+
  apply simp
  done


lemma p2_low_bits_max:
  "(2 ^ asid_low_bits - 1) = (max_word :: asid_low_index)"
  by (simp add: asid_low_bits_def)

lemma dom_ucast_eq:
  "is_aligned y asid_low_bits \<Longrightarrow>
   (- dom (\<lambda>a::asid_low_index. p (ucast a :: machine_word)) \<inter> {x. ucast x + (y::RISCV64_A.asid) \<noteq> 0} = {}) =
   (- dom p \<inter> {x. x \<le> 2 ^ asid_low_bits - 1 \<and> x + ucast y \<noteq> 0} = {})"
  apply safe
   apply clarsimp
   apply (rule ccontr)
   apply (erule_tac x="ucast x" in in_emptyE)
   apply (clarsimp simp: p2_low_bits_max)
   apply (rule conjI)
    apply (clarsimp simp: ucast_ucast_mask)
    apply (subst (asm) less_mask_eq)
    apply (rule word_less_sub_le [THEN iffD1])
      apply (simp add: word_bits_def)
     apply (simp add: asid_low_bits_def)
    apply simp
   apply (clarsimp simp: mask_2pm1[symmetric] ucast_ucast_mask2 is_down is_aligned_mask)
   apply (frule and_mask_eq_iff_le_mask[THEN iffD2])
   apply (simp add: asid_low_bits_def)
   apply (erule notE)
   apply (subst word_plus_and_or_coroll)
    apply word_eqI_solve
   apply (subst (asm) word_plus_and_or_coroll; word_bitwise, clarsimp simp: word_size)
  apply (clarsimp simp: p2_low_bits_max)
  apply (rule ccontr)
  apply simp
  apply (erule_tac x="ucast x" in in_emptyE)
  apply clarsimp
  apply (rule conjI, blast)
  apply (rule conjI)
   apply (rule word_less_sub_1)
   apply (rule order_less_le_trans)
    apply (rule ucast_less, simp)
   apply (simp add: asid_low_bits_def)
  apply clarsimp
  apply (erule notE)
  apply (simp add: is_aligned_mask asid_low_bits_def)
  apply (subst word_plus_and_or_coroll)
   apply word_eqI_solve
  apply (subst (asm) word_plus_and_or_coroll)
   apply (word_bitwise, clarsimp simp: word_size)
  apply (word_bitwise)
  done


lemma asid_high_bits_max_word:
  "(2 ^ asid_high_bits - 1) = (max_word :: asid_high_index)"
  by (simp add: asid_high_bits_def)


lemma dom_ucast_eq_8:
  "(- dom (\<lambda>a::asid_high_index. p (ucast a::machine_word)) = {}) =
   (- dom p \<inter> {x. x \<le> 2 ^ asid_high_bits - 1} = {})"
  apply safe
   apply clarsimp
   apply (rule ccontr)
   apply (erule_tac x="ucast x" in in_emptyE)
   apply (clarsimp simp: asid_high_bits_max_word)
   apply (clarsimp simp: ucast_ucast_mask)
   apply (subst (asm) less_mask_eq)
   apply (rule word_less_sub_le [THEN iffD1])
     apply (simp add: word_bits_def)
    apply (simp add: asid_high_bits_def)
   apply simp
  apply (clarsimp simp: asid_high_bits_max_word)
  apply (rule ccontr)
  apply simp
  apply (erule_tac x="ucast x" in in_emptyE)
  apply clarsimp
  apply (rule conjI, blast)
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
  apply (rule ucast_less, simp)
  apply (simp add: asid_high_bits_def)
  done


lemma ucast_fst_hd_assocs:
  assumes "- dom (\<lambda>x::asid_low_index. pool (ucast x)) \<inter> {x. ucast x + (a::RISCV64_A.asid) \<noteq> 0} \<noteq> {}"
  assumes "is_aligned a asid_low_bits"
  shows
    "fst (hd [(x, y) \<leftarrow> assocs pool. x \<le> 2 ^ asid_low_bits - 1 \<and> x + ucast a \<noteq> 0 \<and> y = None]) +
           (ucast a :: machine_word) =
       ucast (UCAST(asid_low_len \<rightarrow> asid_len)
         (fst (hd [(x, y) \<leftarrow> assocs (\<lambda>a. pool (ucast a)). ucast x + a \<noteq> 0 \<and> y = None])) + a)"
proof -
  have [unfolded word_bits_def, simplified, simp]: "asid_low_bits < word_bits"
    by (simp add: asid_low_bits_def word_bits_def)
  have [unfolded asid_low_bits_def, simplified, simp]:
    "x && mask asid_low_bits = x"
    if "x < 2^asid_low_bits" for x::machine_word
    using that by (simp add: le_mask_iff_lt_2n[THEN iffD1, symmetric] word_le_mask_eq)
  have [unfolded asid_bits_def asid_low_bits_def, simplified, simp]:
    "x && mask asid_bits = x"
    if "x < 2^asid_low_bits" for x::machine_word
  proof -
    have "mask asid_low_bits \<le> (mask asid_bits :: machine_word)"
      by (simp add: mask_def asid_low_bits_def asid_bits_def)
    with that show ?thesis
      by (simp add: le_mask_iff_lt_2n[THEN iffD1, symmetric] word_le_mask_eq)
  qed
  have [unfolded asid_bits_def asid_low_bits_def, simplified, simp]:
    "(x + ucast a \<noteq> 0) = (ucast x + a \<noteq> 0)"
    if "x < 2^asid_low_bits" for x::machine_word
  proof -
    from that have "x \<le> mask asid_low_bits" by (simp add: le_mask_iff_lt_2n[THEN iffD1, symmetric])
    with `is_aligned a asid_low_bits`
    show ?thesis
      apply (subst word_and_or_mask_aligned2; simp add: is_aligned_ucastI)
      apply (subst word_and_or_mask_aligned2, assumption, erule ucast_le_maskI)
      apply (simp add: asid_low_bits_def)
      apply word_bitwise
      apply simp
      done
  qed

  from assms show ?thesis
    apply (simp add: ucast_assocs[unfolded o_def])
    apply (simp add: filter_map split_def)
    apply (simp cong: conj_cong add: ucast_ucast_mask2 is_down)
    apply (simp add: asid_low_bits_def minus_one_norm)
    apply (subgoal_tac "P" for P)  (* cut_tac but more awesome *)
     apply (subst hd_map, assumption)
     apply (simp add: ucast_ucast_mask2 is_down)
     apply (drule hd_in_set)
     apply clarsimp
     apply (subst ucast_add_mask_aligned; assumption?)
      apply (rule ucast_le_maskI)
      apply (simp add: mask_def word_le_make_less)
     apply (simp add: ucast_ucast_mask cong: conj_cong)
    apply (simp add: assocs_empty_dom_comp null_def split_def)
    apply (simp add: ucast_assocs[unfolded o_def] filter_map split_def)
    apply (simp cong: conj_cong add: ucast_ucast_mask2 is_down)
    done
qed


crunches
  perform_page_table_invocation, perform_page_invocation, perform_asid_pool_invocation
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps)

lemmas perform_page_table_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_page_table_invocation_typ_at]

lemmas perform_page_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_page_invocation_typ_at]

lemmas perform_asid_pool_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_asid_pool_invocation_typ_at]

lemma perform_asid_control_invocation_tcb_at:
  "\<lbrace>invs and valid_aci aci and st_tcb_at active p and
    K (\<forall>w a b c. aci = asid_control_invocation.MakePool w a b c \<longrightarrow> w \<noteq> p)\<rbrace>
  perform_asid_control_invocation aci
  \<lbrace>\<lambda>rv. tcb_at p\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (cases aci)
  apply clarsimp
  apply (wp |simp)+
    apply (wp obj_at_delete_objects retype_region_obj_at_other2  hoare_vcg_const_imp_lift|assumption)+
  apply (intro impI conjI)
    apply (clarsimp simp: retype_addrs_def obj_bits_api_def default_arch_object_def image_def ptr_add_def)
   apply (clarsimp simp: st_tcb_at_tcb_at)+
  apply (frule st_tcb_ex_cap)
    apply fastforce
   apply (clarsimp split: Structures_A.thread_state.splits)
   apply auto[1]
  apply (clarsimp simp: ex_nonz_cap_to_def valid_aci_def)
  apply (frule invs_untyped_children)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (erule_tac ptr="(aa,ba)" in untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
      apply (simp add: cte_wp_at_caps_of_state)
     apply simp
    apply (simp add:cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: zobj_refs_to_obj_refs)
   apply (erule(1) in_empty_interE)
    apply (clarsimp simp:page_bits_def)
  apply simp
  done


lemma ucast_asid_high_btis_of_le [simp]:
  "ucast (asid_high_bits_of w) \<le> (2 ^ asid_high_bits - 1 :: machine_word)"
  apply (simp add: asid_high_bits_of_def)
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
  apply (rule ucast_less)
   apply simp
  apply (simp add: asid_high_bits_def)
  done


lemma invoke_arch_tcb:
  "\<lbrace>invs and valid_arch_inv ai and st_tcb_at active tptr\<rbrace>
  arch_perform_invocation ai
  \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  apply (simp add: arch_perform_invocation_def)
  apply (cases ai; simp; (wp; clarsimp simp add: st_tcb_at_tcb_at)?)
  apply (wp perform_asid_control_invocation_tcb_at)
  apply (clarsimp simp add: valid_arch_inv_def)
  apply (clarsimp simp: valid_aci_def)
  apply (frule st_tcb_ex_cap)
    apply fastforce
   apply (clarsimp split: Structures_A.thread_state.splits)
   apply auto[1]
  apply (clarsimp simp: ex_nonz_cap_to_def)
  apply (frule invs_untyped_children)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (erule_tac ptr="(aa,ba)" in untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
      apply (simp add: cte_wp_at_caps_of_state)+
    apply fastforce
   apply (clarsimp simp: zobj_refs_to_obj_refs cte_wp_at_caps_of_state)
   apply (drule_tac p="(aa,ba)" in caps_of_state_valid_cap, fastforce)
   apply (clarsimp simp: valid_cap_def cap_aligned_def)
   apply (drule_tac x=tptr in base_member_set, simp)
    apply (simp add: pageBits_def field_simps del: atLeastAtMost_iff)
   apply (metis (no_types) orthD1 x_power_minus_1)
  apply simp
  done

end


locale asid_update = Arch +
  fixes ap asid_hi s s'
  assumes ko: "asid_pools_of s ap = Some Map.empty"
  assumes empty: "asid_table s asid_hi = None"
  defines "s' \<equiv> s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (asid_table s)(asid_hi \<mapsto> ap)\<rparr>\<rparr>"
begin

lemma aobjs_of[simp]:
  "aobjs_of s' = aobjs_of s"
  unfolding s'_def by simp

lemma vspace_for_pool_ap[simp]:
  "vspace_for_pool ap asid (asid_pools_of s) = None"
  using ko by (simp add: vspace_for_pool_def obind_def)

lemma asid_hi_pool_for_asid:
  "asid_high_bits_of asid = asid_hi \<Longrightarrow> pool_for_asid asid s = None"
  using empty by (simp add: pool_for_asid_def)

lemma asid_hi_pool_for_asid':
  "asid_high_bits_of asid = asid_hi \<Longrightarrow> pool_for_asid asid s' = Some ap"
  by (simp add: pool_for_asid_def s'_def)

lemma asid_hi_vs_lookup_table:
  "asid_high_bits_of asid = asid_hi \<Longrightarrow> vs_lookup_table asid_pool_level asid vref s = None"
  by (simp add: asid_hi_pool_for_asid vs_lookup_table_def obind_def)

lemma vs_lookup_table:
  "vs_lookup_table level asid vref s' =
     (if asid_high_bits_of asid = asid_hi \<and> level = asid_pool_level
      then Some (asid_pool_level, ap)
      else vs_lookup_table level asid vref s)"
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vs_lookup_table_def in_omonad asid_hi_pool_for_asid')
  apply (clarsimp simp: vs_lookup_table_def)
  apply (cases "asid_high_bits_of asid = asid_hi"; simp)
   apply (clarsimp simp: obind_def asid_hi_pool_for_asid' asid_hi_pool_for_asid)
  apply (rule obind_eqI)
   apply (simp add: s'_def pool_for_asid_def)
  apply (clarsimp simp: obind_def split: option.splits)
  done

lemma vs_lookup_slot:
  "vs_lookup_slot level asid vref s' =
     (if asid_high_bits_of asid = asid_hi \<and> level = asid_pool_level
      then Some (asid_pool_level, ap)
      else vs_lookup_slot level asid vref s)"
  apply (simp add: vs_lookup_slot_def)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: obind_def vs_lookup_table)
  apply (rule obind_eqI)
   apply (clarsimp simp: vs_lookup_table)
  apply (clarsimp simp: obind_def split: option.splits)
  done

lemma vs_lookup_target[simp]:
  "vs_lookup_target level asid vref s' = vs_lookup_target level asid vref s"
  apply (cases "asid_high_bits_of asid = asid_hi \<and> level = asid_pool_level")
   apply (simp add: vs_lookup_target_def vs_lookup_slot_def obind_def vs_lookup_table
                    asid_hi_vs_lookup_table
               split: option.splits)
  apply (clarsimp simp: vs_lookup_target_def)
  apply (rule obind_eqI)
   apply (clarsimp simp: vs_lookup_slot)
  apply (clarsimp simp: obind_def split: option.splits)
  done

lemma obj_at [simp]:
  "obj_at P p s' = obj_at P p s"
  by (simp add: s'_def)

lemma valid_pte[simp]:
  "valid_pte level pte s' = valid_pte level pte s"
  by (cases pte; simp add: data_at_def)

lemma valid_vspace_obj[simp]:
  "valid_vspace_obj level ao s' = valid_vspace_obj level ao s"
  by (cases ao; simp)

lemma vspace_objs':
  "valid_vspace_objs s \<Longrightarrow> valid_vspace_objs s'"
  using ko
  apply (clarsimp simp: valid_vspace_objs_def vs_lookup_table)
  apply (clarsimp simp: in_omonad)
  done

lemma global_objs':
  "valid_global_objs s \<Longrightarrow> valid_global_objs s'"
  by (simp add: valid_global_objs_def)

lemma caps_of_state_s':
  "caps_of_state s' = caps_of_state s"
  by (rule caps_of_state_pspace, simp add: s'_def)

lemma valid_vs_lookup[simp]:
  "valid_vs_lookup s' = valid_vs_lookup s"
  by (clarsimp simp: valid_vs_lookup_def caps_of_state_s')

lemma valid_table_caps':
  "valid_table_caps s \<Longrightarrow> valid_table_caps s'"
  by (simp add: valid_table_caps_def caps_of_state_s' s'_def)

lemma valid_asid_pool_caps':
  "\<lbrakk> valid_asid_pool_caps s;
     \<exists>ptr cap. caps_of_state s ptr = Some cap
     \<and> obj_refs cap = {ap} \<and> vs_cap_ref cap = Some (ucast asid_hi << asid_low_bits, 0) \<rbrakk>
  \<Longrightarrow> valid_asid_pool_caps s'"
  unfolding valid_asid_pool_caps_def by (clarsimp simp: s'_def)

lemma valid_arch_caps:
  "\<lbrakk> valid_arch_caps s;
     \<exists>ptr cap. caps_of_state s ptr = Some cap
     \<and> obj_refs cap = {ap} \<and> vs_cap_ref cap = Some (ucast asid_hi << asid_low_bits, 0) \<rbrakk>
  \<Longrightarrow> valid_arch_caps s'"
  apply (simp add: valid_arch_caps_def valid_table_caps' valid_asid_pool_caps')
  apply (simp add: caps_of_state_s')
  done

lemma valid_asid_map':
  "valid_asid_map s \<Longrightarrow> valid_asid_map s'"
  by (clarsimp simp: valid_asid_map_def)

lemma vspace_for_asid[simp]:
  "vspace_for_asid asid s' = vspace_for_asid asid s"
  using ko empty
  by (clarsimp simp: vspace_for_asid_def obind_def pool_for_asid_def s'_def vspace_for_pool_def
               split: option.splits)

lemma global_pt[simp]:
  "global_pt s' = global_pt s"
  by (simp add: s'_def)

lemma equal_kernel_mappings:
  "equal_kernel_mappings s' = equal_kernel_mappings s"
  by (simp add: equal_kernel_mappings_def has_kernel_mappings_def)

end


context Arch begin global_naming RISCV64

lemma valid_arch_state_strg:
  "valid_arch_state s \<and> ap \<notin> ran (asid_table s) \<and> asid_pool_at ap s \<longrightarrow>
   valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (asid_table s)(asid \<mapsto> ap)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def)
  apply (clarsimp simp: valid_asid_table_def ran_def)
  apply (fastforce intro!: inj_on_fun_updI simp: asid_pools_at_eq)
  done


lemma valid_vs_lookup_at_upd_strg:
  "valid_vs_lookup s \<and>
   asid_pools_of s ap = Some Map.empty \<and>
   asid_table s asid = None
   \<longrightarrow>
   valid_vs_lookup (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (asid_table s)(asid \<mapsto> ap)\<rparr>\<rparr>)"
  apply clarsimp
  apply (prop_tac "asid_update ap asid s", (unfold_locales; assumption))
  apply (simp add: asid_update.valid_vs_lookup)
  done

lemma valid_asid_pool_caps_upd_strg:
  "valid_asid_pool_caps s \<and>
   asid_pools_of s ap = Some Map.empty \<and>
   asid_table s asid = None \<and>
   (\<exists>ptr cap. caps_of_state s ptr = Some cap
     \<and> obj_refs cap = {ap} \<and> vs_cap_ref cap = Some (ucast asid << asid_low_bits, 0))
   \<longrightarrow>
   valid_asid_pool_caps_2 (caps_of_state s) ((asid_table s)(asid \<mapsto> ap))"
  apply clarsimp
  apply (prop_tac "asid_update ap asid s", (unfold_locales; assumption))
  apply (fastforce dest: asid_update.valid_asid_pool_caps')
  done

lemma retype_region_ap[wp]:
  "\<lbrace>\<top>\<rbrace>
  retype_region ap (Suc 0) 0 (ArchObject ASIDPoolObj) dev
  \<lbrace>\<lambda>_ s. asid_pools_of s ap = Some Map.empty\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule retype_region_obj_at)
    apply simp
   apply simp
  apply (clarsimp simp: retype_addrs_def obj_bits_api_def default_arch_object_def)
  apply (clarsimp simp: obj_at_def default_object_def default_arch_object_def in_omonad)
  done


lemma retype_region_ako[wp]:
  "\<lbrace>\<top>\<rbrace> retype_region ap (Suc 0) 0 (ArchObject ASIDPoolObj) dev \<lbrace>\<lambda>_. ako_at (ASIDPool Map.empty) ap\<rbrace>"
  apply (rule hoare_strengthen_post, rule retype_region_ap)
  apply (simp add: obj_at_def in_omonad)
  done

lemma retype_region_ap':
  "\<lbrace>\<top>\<rbrace> retype_region ap (Suc 0) 0 (ArchObject ASIDPoolObj) dev \<lbrace>\<lambda>rv. asid_pool_at ap\<rbrace>"
  apply (rule hoare_strengthen_post, rule retype_region_ap)
  apply (simp add: asid_pools_at_eq)
  done


lemma no_cap_to_obj_with_diff_ref_null_filter:
  "no_cap_to_obj_with_diff_ref cap S
     = (\<lambda>s. \<forall>c \<in> ran (null_filter (caps_of_state s) |` (- S)).
             obj_refs c = obj_refs cap
                 \<longrightarrow> table_cap_ref c = table_cap_ref cap)"
  apply (simp add: no_cap_to_obj_with_diff_ref_def
                   ball_ran_eq cte_wp_at_caps_of_state)
  apply (simp add: Ball_def)
  apply (intro iff_allI ext)
  apply (simp add: restrict_map_def null_filter_def)
  apply (auto dest!: obj_ref_none_no_asid[rule_format]
               simp: table_cap_ref_def)
  done


lemma retype_region_no_cap_to_obj:
  "\<lbrace>valid_pspace and valid_mdb
             and caps_overlap_reserved {ptr..ptr + 2 ^ obj_bits_api ty us - 1}
             and caps_no_overlap ptr sz
             and pspace_no_overlap_range_cover ptr sz
             and no_cap_to_obj_with_diff_ref cap S
             and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c. up_aligned_area ptr sz \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
             and K (ty = CapTableObject \<longrightarrow> 0 < us)
             and K (range_cover ptr sz (obj_bits_api ty us) 1) \<rbrace>
     retype_region ptr 1 us ty dev
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: no_cap_to_obj_with_diff_ref_null_filter)
  apply (wp retype_region_caps_of | simp)+
  apply fastforce
  done


lemma valid_table_caps_asid_upd [iff]:
  "valid_table_caps (s\<lparr>arch_state := (riscv_asid_table_update f (arch_state s))\<rparr>) =
   valid_table_caps s"
  by (simp add: valid_table_caps_def second_level_tables_def)

lemma set_cap_reachable_pg_cap:
  "set_cap cap' slot \<lbrace>\<lambda>s. P (reachable_frame_cap cap s)\<rbrace>"
  unfolding reachable_frame_cap_def reachable_target_def vs_lookup_target_def
  apply (clarsimp simp: in_omonad vs_lookup_slot_def vs_lookup_table_def)
  apply (wp_pre, wps, wp)
  apply simp
  done

lemma set_cap_reachable_target[wp]:
  "set_cap cap slot \<lbrace>\<lambda>s. P (reachable_target ref p s)\<rbrace>"
  apply (clarsimp simp: reachable_target_def split_def)
  apply (wp_pre, wps, wp)
  apply simp
  done

lemma cap_insert_simple_arch_caps_ap:
  "\<lbrace>valid_arch_caps and (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s)
     and no_cap_to_obj_with_diff_ref cap {dest}
     and (\<lambda>s. asid_table s (asid_high_bits_of asid) = None \<and> asid_pools_of s ap = Some Map.empty)
     and K (cap = ArchObjectCap (ASIDPoolCap ap asid) \<and> is_aligned asid asid_low_bits) \<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv s. valid_arch_caps (s\<lparr>arch_state := arch_state s
                       \<lparr>riscv_asid_table := (asid_table s)(asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: cap_insert_def update_cdt_def set_cdt_def valid_arch_caps_def
                   set_untyped_cap_as_full_def bind_assoc)
  apply (strengthen valid_vs_lookup_at_upd_strg valid_asid_pool_caps_upd_strg)
  apply (wp get_cap_wp set_cap_valid_vs_lookup set_cap_arch_obj
            set_cap_valid_table_caps hoare_vcg_all_lift
          | simp split del: if_split)+
       apply (simp add: F)
       apply (rule_tac P = "cte_wp_at ((=) src_cap) src" in set_cap_orth)
       apply (wp hoare_vcg_imp_lift hoare_vcg_ball_lift set_free_index_final_cap hoare_vcg_all_lift
                 hoare_vcg_disj_lift set_cap_reachable_pg_cap set_cap.vs_lookup_pages
              | clarsimp)+
      apply (wp set_cap_arch_obj set_cap_valid_table_caps hoare_vcg_ball_lift
                get_cap_wp hoare_weak_lift_imp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
   apply (rule_tac x="fst dest" in exI)
   apply (rule_tac x="snd dest" in exI)
   apply (simp add: asid_high_bits_shl)
  apply (rule conjI)
   apply (simp add: unique_table_caps_def is_cap_simps)
  apply (subst unique_table_refs_def)
  apply (intro allI impI)
  apply (simp split: if_split_asm)
    apply (simp add: no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state)
   apply (simp add: no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state)
  apply (erule (3) unique_table_refsD)
  done

lemma valid_asid_map_asid_upd_strg:
  "valid_asid_map s \<and>
   asid_pools_of s ap = Some Map.empty \<and>
   asid_table s asid = None \<longrightarrow>
   valid_asid_map (asid_table_update asid ap s)"
  by (simp add: valid_asid_map_def)

lemma valid_vspace_objs_asid_upd_strg:
  "valid_vspace_objs s \<and>
   asid_pools_of s ap = Some Map.empty \<and>
   asid_table s asid = None \<longrightarrow>
   valid_vspace_objs (asid_table_update asid ap s)"
  apply clarsimp
  apply (prop_tac "asid_update ap asid s", (unfold_locales; assumption))
  apply (erule (1) asid_update.vspace_objs')
  done

lemma valid_global_objs_asid_upd_strg:
  "valid_global_objs s \<and>
   asid_pools_of s ap = Some Map.empty \<and>
   asid_table s asid = None \<longrightarrow>
   valid_global_objs (asid_table_update asid ap s)"
  by (clarsimp simp: valid_global_objs_def)

lemma equal_kernel_mappings_asid_upd_strg:
  "equal_kernel_mappings s \<and>
   asid_pools_of s ap = Some Map.empty \<and>
   asid_table s asid = None \<longrightarrow>
   equal_kernel_mappings (asid_table_update asid ap s)"
  apply clarsimp
  apply (prop_tac "asid_update ap asid s", (unfold_locales; assumption))
  apply (simp add: asid_update.equal_kernel_mappings)
  done

lemma safe_parent_cap_is_device:
  "safe_parent_for m p cap pcap \<Longrightarrow> cap_is_device cap = cap_is_device pcap"
  by (simp add: safe_parent_for_def)

lemma cap_insert_ioports_ap:
  "\<lbrace>valid_ioports and (\<lambda>s. cte_wp_at (\<lambda>cap'. safe_ioport_insert cap cap' s) dest s) and
        K (is_ap_cap cap)\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  by wpsimp

crunches cap_insert
  for aobjs_of[wp]: "\<lambda>s. P (aobjs_of s)"
  (wp: crunch_wps)

lemma cap_insert_ap_invs:
  "\<lbrace>invs and valid_cap cap and tcb_cap_valid cap dest and
    ex_cte_cap_wp_to (appropriate_cte_cap cap) dest and
    cte_wp_at (\<lambda>c. c = NullCap) dest and
    no_cap_to_obj_with_diff_ref cap {dest} and
    (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s) and
    K (cap = ArchObjectCap (ASIDPoolCap ap asid)) and
   (\<lambda>s. \<forall>irq \<in> cap_irqs cap. irq_issued irq s) and
   ko_at (ArchObj (ASIDPool Map.empty)) ap and
   (\<lambda>s. ap \<notin> ran (riscv_asid_table (arch_state s)) \<and>
        asid_table s (asid_high_bits_of asid) = None)\<rbrace>
  cap_insert cap src dest
  \<lbrace>\<lambda>rv s. invs (s\<lparr>arch_state := arch_state s
                       \<lparr>riscv_asid_table := ((riscv_asid_table \<circ> arch_state) s)(asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (strengthen valid_arch_state_strg valid_vspace_objs_asid_upd_strg
                    equal_kernel_mappings_asid_upd_strg valid_asid_map_asid_upd_strg
                    valid_global_objs_asid_upd_strg)
  apply (simp cong: conj_cong)
  apply (rule hoare_pre)
   apply (wp cap_insert_simple_mdb cap_insert_iflive
             cap_insert_zombies cap_insert_ifunsafe cap_insert_ioports_ap
             cap_insert_valid_global_refs cap_insert_idle
             valid_irq_node_typ cap_insert_simple_arch_caps_ap)
  apply (clarsimp simp: is_simple_cap_def cte_wp_at_caps_of_state is_cap_simps)
  apply (frule safe_parent_cap_is_device)
  apply (drule safe_parent_cap_range)
  apply (simp add: is_simple_cap_arch_def)
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp: obj_at_def a_type_def in_omonad)
   apply (clarsimp simp: valid_cap_def)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule_tac p="(a,b)" in caps_of_state_valid_cap, fastforce)
  apply (auto simp: obj_at_def is_tcb_def is_cap_table_def
                    valid_cap_def [where c="cap.Zombie a b x" for a b x]
              dest: obj_ref_is_tcb obj_ref_is_cap_table split: option.splits)
  done

lemma max_index_upd_no_cap_to:
  "\<lbrace>\<lambda>s. no_cap_to_obj_with_diff_ref cap {slot} s \<and>
        cte_wp_at ((=) ucap) cref s \<and> is_untyped_cap ucap\<rbrace>
   set_cap (max_free_index_update ucap) cref
   \<lbrace>\<lambda>rv s. no_cap_to_obj_with_diff_ref cap {slot} s \<rbrace>"
  apply (clarsimp simp:no_cap_to_obj_with_diff_ref_def)
  apply (wp hoare_vcg_ball_lift set_cap_cte_wp_at_neg)
  apply (clarsimp simp:cte_wp_at_caps_of_state free_index_update_def is_cap_simps)
  apply (drule_tac x = cref in bspec)
   apply clarsimp
  apply (clarsimp simp:table_cap_ref_def)
  done

lemma perform_asid_control_invocation_pred_tcb_at:
  "\<lbrace>\<lambda>s. pred_tcb_at proj Q t s \<and> st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t s
        \<and> ct_active s \<and> invs s \<and> valid_aci aci s\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. pred_tcb_at proj Q t\<rbrace>"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (rule hoare_name_pre_state)
  apply (subgoal_tac "is_aligned word1 page_bits")
   prefer 2
   apply (clarsimp simp: valid_aci_def cte_wp_at_caps_of_state)
   apply (drule(1) caps_of_state_valid[rotated])+
   apply (simp add:valid_cap_simps cap_aligned_def page_bits_def)
  apply (subst delete_objects_rewrite)
     apply (simp add:page_bits_def word_bits_def pageBits_def word_size_bits_def)+
   apply (simp add:is_aligned_neg_mask_eq)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at[where sz=page_bits] set_cap_no_overlap|simp)+
     apply (strengthen invs_valid_objs invs_psp_aligned)
     apply (clarsimp simp:conj_comms)
     apply (wp max_index_upd_invs_simple get_cap_wp)+
  apply (clarsimp simp: valid_aci_def)
  apply (frule intvl_range_conv)
   apply (simp add:word_bits_def page_bits_def pageBits_def)
  apply (clarsimp simp:detype_clear_um_independent page_bits_def is_aligned_neg_mask_eq)
  apply (rule conjI)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (simp only: field_simps)
   apply (rule pspace_no_overlap_detype')
     apply (rule caps_of_state_valid_cap)
      apply (simp add:page_bits_def)+
    apply (simp add:invs_valid_objs invs_psp_aligned)+
  apply (rule conjI)
   apply (frule st_tcb_ex_cap)
     apply clarsimp
    apply (clarsimp split: Structures_A.thread_state.splits)
   apply (clarsimp simp: ex_nonz_cap_to_def)
   apply (frule invs_untyped_children)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (erule_tac ptr="(aa,ba)" in untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
       apply (simp add: cte_wp_at_caps_of_state)+
      apply fastforce
    apply (clarsimp simp: zobj_refs_to_obj_refs)
    apply (fastforce simp:page_bits_def)
   apply simp
  apply (clarsimp simp:obj_bits_api_def arch_kobj_size_def cte_wp_at_caps_of_state
    default_arch_object_def empty_descendants_range_in)
  apply (frule_tac cap = "(cap.UntypedCap False word1 pageBits idx)"
    in detype_invariants[rotated 3],clarsimp+)
    apply (simp add:cte_wp_at_caps_of_state
      empty_descendants_range_in descendants_range_def2)+
  apply (thin_tac "x = Some cap.NullCap" for x)+
  apply (drule(1) caps_of_state_valid_cap[OF _ invs_valid_objs])
  apply (intro conjI)
    apply (clarsimp simp:valid_cap_def cap_aligned_def range_cover_full
     invs_psp_aligned invs_valid_objs page_bits_def)
   apply (erule pspace_no_overlap_detype)
  apply (auto simp:page_bits_def detype_clear_um_independent)
  done

lemma perform_asid_control_invocation_st_tcb_at:
  "\<lbrace>st_tcb_at (P and (Not \<circ> inactive) and (Not \<circ> idle)) t
    and ct_active and invs and valid_aci aci\<rbrace>
   perform_asid_control_invocation aci
   \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  apply (wpsimp wp: perform_asid_control_invocation_pred_tcb_at)
  apply (fastforce simp: pred_tcb_at_def obj_at_def)
  done

lemma set_cap_idx_up_aligned_area:
  "\<lbrace>K (\<exists>idx. pcap = UntypedCap dev ptr pageBits idx) and cte_wp_at ((=) pcap) slot
      and valid_objs\<rbrace> set_cap (max_free_index_update pcap) slot
  \<lbrace>\<lambda>rv s. (\<exists>slot. cte_wp_at (\<lambda>c. up_aligned_area ptr pageBits \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)\<rbrace>"
  apply (rule hoare_pre)
  apply (wp hoare_vcg_ex_lift set_cap_cte_wp_at)
  apply (rule_tac x = slot in exI)
  apply clarsimp
  apply (frule(1) cte_wp_valid_cap)
  apply (clarsimp simp: cte_wp_at_caps_of_state p_assoc_help valid_cap_def valid_untyped_def
                        cap_aligned_def)
  done

primrec(nonexhaustive)
  get_untyped_cap_idx :: "cap \<Rightarrow> nat"
where
  "get_untyped_cap_idx (UntypedCap dev ref sz idx) = idx"

lemma aci_invs':
  assumes Q_ignores_arch[simp]: "\<And>f s. Q (arch_state_update f s) = Q s"
  assumes Q_ignore_machine_state[simp]: "\<And>f s. Q (machine_state_update f s) = Q s"
  assumes Q_detype[simp]: "\<And>f s. Q (detype f s) = Q s"
  assumes cap_insert_Q: "\<And>cap src dest. \<lbrace>Q and invs and K (src \<noteq> dest)\<rbrace>
                            cap_insert cap src dest
                           \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes retype_region_Q[wp]:"\<And>a b c d e. \<lbrace>Q\<rbrace> retype_region a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes set_cap_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_cap a b \<lbrace>\<lambda>_.Q\<rbrace>"
  shows "\<lbrace>invs and Q and ct_active and valid_aci aci\<rbrace> perform_asid_control_invocation aci \<lbrace>\<lambda>y s. invs s \<and> Q s\<rbrace>"
proof -
  have cap_insert_invsQ:
       "\<And>cap src dest ap asid.
        \<lbrace>Q and (invs and valid_cap cap and tcb_cap_valid cap dest and
         ex_cte_cap_wp_to (appropriate_cte_cap cap) dest and
         cte_wp_at (\<lambda>c. c = NullCap) dest and
         no_cap_to_obj_with_diff_ref cap {dest} and
         (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s) and
         K (cap = ArchObjectCap (ASIDPoolCap ap asid)) and
         (\<lambda>s. \<forall>irq\<in>cap_irqs cap. irq_issued irq s) and
         ko_at (ArchObj (ASIDPool Map.empty)) ap and
         (\<lambda>s. ap \<notin> ran (asid_table s) \<and> asid_table s (asid_high_bits_of asid) = None))\<rbrace>
         cap_insert cap src dest
        \<lbrace>\<lambda>rv s.
           invs
             (s\<lparr>arch_state := arch_state s
                 \<lparr>riscv_asid_table := ((riscv_asid_table \<circ> arch_state) s)
                    (asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>) \<and>
           Q
             (s\<lparr>arch_state := arch_state s
                 \<lparr>riscv_asid_table := ((riscv_asid_table \<circ> arch_state) s)
                    (asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)\<rbrace>"
    apply (wp cap_insert_ap_invs)
     apply simp
     apply (rule hoare_pre)
      apply (rule cap_insert_Q, assumption)
    apply (auto simp: cte_wp_at_caps_of_state)
    done
  show ?thesis
    apply (clarsimp simp: perform_asid_control_invocation_def valid_aci_def
                    split: asid_control_invocation.splits)
    apply (rename_tac word1 a b aa ba word2)
    apply (rule hoare_pre)
     apply (wp hoare_vcg_const_imp_lift)
         apply (wp cap_insert_invsQ hoare_vcg_ex_lift | simp)+
        apply (simp add: valid_cap_def |
               strengthen real_cte_tcb_valid safe_parent_strg
                          invs_vobjs_strgs
                          ex_cte_cap_to_cnode_always_appropriate_strg)+
        apply (wp hoare_vcg_const_imp_lift set_free_index_invs
                  retype_region_plain_invs[where sz = pageBits]
                  retype_cte_wp_at[where sz = pageBits] hoare_vcg_ex_lift
                  retype_region_obj_at_other3[where P="is_cap_table n" and sz = pageBits for n]
                  retype_region_ex_cte_cap_to[where sz = pageBits]
                  retype_region_ap[simplified]
                  retype_region_ap'[simplified]
                  retype_region_no_cap_to_obj[where sz = pageBits,simplified]
               | simp del: split_paired_Ex)+
       apply (strengthen invs_valid_objs invs_psp_aligned
              invs_mdb invs_valid_pspace
              exI[where x="case aci of MakePool frame slot parent base \<Rightarrow> parent"]
              exI[where x="case aci of MakePool frame slot parent base \<Rightarrow> parent",
                simplified]
              caps_region_kernel_window_imp[where
                p = "case aci of MakePool frame slot parent base \<Rightarrow> parent"]
              invs_cap_refs_in_kernel_window)+
       apply (wp set_cap_caps_no_overlap set_cap_no_overlap get_cap_wp
                 max_index_upd_caps_overlap_reserved max_index_upd_invs_simple
                 set_cap_cte_cap_wp_to set_cap_cte_wp_at max_index_upd_no_cap_to
              | simp split del: if_split | wp (once) hoare_vcg_ex_lift)+
     apply (rule_tac P = "is_aligned word1 page_bits" in hoare_gen_asm)
     apply (subst delete_objects_rewrite)
        apply (simp add:page_bits_def pageBits_def word_size_bits_def)
       apply (simp add:page_bits_def pageBits_def word_bits_def)
      apply (simp add: page_bits_def)
     apply wp
    apply (clarsimp simp: cte_wp_at_caps_of_state if_option_Some
               split del: if_split)
    apply (frule_tac cap = "(cap.UntypedCap False word1 pageBits idx)"
                     in detype_invariants[rotated 3],clarsimp+)
       apply (simp add:cte_wp_at_caps_of_state)+
     apply (simp add:descendants_range_def2 empty_descendants_range_in)
    apply (simp add:invs_mdb invs_valid_pspace invs_psp_aligned invs_valid_objs)
    apply (clarsimp dest!:caps_of_state_cteD)
    apply (frule(1) unsafe_protected[where p=t and p'=t for t])
        apply (simp add:empty_descendants_range_in)+
      apply fastforce
     apply clarsimp
    apply (frule_tac p = "(aa,ba)" in cte_wp_valid_cap)
     apply fastforce
    apply (clarsimp simp: detype_clear_um_independent obj_bits_api_def arch_kobj_size_def
                          default_arch_object_def conj_comms)
    apply (rule conjI)
     apply (clarsimp simp:valid_cap_simps cap_aligned_def page_bits_def not_le)
    apply (simp add:empty_descendants_range_in)
    apply (frule valid_cap_aligned)
    apply (clarsimp simp: cap_aligned_def)
    apply (subst caps_no_overlap_detype[OF descendants_range_caps_no_overlapI],
           assumption, simp,
           simp add: empty_descendants_range_in)
    apply (frule pspace_no_overlap_detype, clarify+)
    apply (frule intvl_range_conv[where bits = pageBits])
     apply (simp add:pageBits_def word_bits_def)
    apply (clarsimp simp: page_bits_def)
    apply (frule(1) ex_cte_cap_protects)
        apply (simp add:empty_descendants_range_in)
       apply fastforce
      apply (rule subset_refl)
     apply fastforce
    apply (clarsimp simp: field_simps)
    apply (intro conjI impI;
           simp add: free_index_of_def valid_cap_simps valid_untyped_def
                     empty_descendants_range_in range_cover_full clear_um_def max_free_index_def;
           clarsimp simp:valid_untyped_def valid_cap_simps)
       apply (clarsimp simp: cte_wp_at_caps_of_state)
      apply (erule(1) cap_to_protected)
       apply (simp add:empty_descendants_range_in descendants_range_def2)+
     apply (drule invs_arch_state)+
     apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
     apply (drule (1) subsetD)+
     apply (clarsimp simp: in_opt_map_eq)
     apply (erule notE, erule is_aligned_no_overflow)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def)
    apply (thin_tac "cte_wp_at ((=) cap.NullCap) p s" for p s)
    apply (subst(asm) eq_commute,
           erule(1) untyped_children_in_mdbE[where cap="cap.UntypedCap dev p bits idx" for dev p bits idx,
                                             simplified, rotated])
      apply (simp add: is_aligned_no_overflow)
     apply simp
    apply clarsimp
  done

qed


lemmas aci_invs[wp] =
  aci_invs'[where Q=\<top>,simplified hoare_TrueI, OF refl refl refl TrueI TrueI TrueI,simplified]

lemma invoke_arch_invs[wp]:
  "\<lbrace>invs and ct_active and valid_arch_inv ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases ai, simp_all add: valid_arch_inv_def arch_perform_invocation_def)
  apply (wp|simp)+
  done

lemma sts_aobjs_of[wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_wp)
  apply (erule rsubst[where P=P])
  apply (auto dest!: get_tcb_SomeD simp: opt_map_def split: option.splits)
  done

crunches set_thread_state
  for pool_for_asid[wp]: "\<lambda>s. P (pool_for_asid asid s)"
  (wp: assert_inv)

lemma sts_vspace_for_asid[wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  apply (simp add: vspace_for_asid_def obind_def split: option.splits)
  apply (rule conjI; wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)
  done

lemma sts_vspace_at_asid[wp]:
  "set_thread_state t st \<lbrace>vspace_at_asid asid pd\<rbrace>"
  unfolding vspace_at_asid_def by wpsimp

lemma sts_valid_slots_inv[wp]:
  "set_thread_state t st \<lbrace>valid_slots m\<rbrace>"
  unfolding valid_slots_def
  apply (cases m)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' sts_typ_ats)
  apply fastforce
  done

lemma sts_same_ref[wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. P (same_ref ref cap s)\<rbrace>"
  unfolding same_ref_def by (cases ref) (wpsimp simp: vs_lookup_slot_def in_omonad)

lemma sts_valid_page_inv[wp]:
  "set_thread_state t st \<lbrace>valid_page_inv page_invocation\<rbrace>"
  unfolding valid_page_inv_def
  apply (cases page_invocation)
    apply (wpsimp wp: sts_typ_ats hoare_vcg_ex_lift hoare_vcg_disj_lift | wps)+
  done

crunches set_thread_state
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"

lemma sts_vs_lookup_slot[wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. P (vs_lookup_slot level asid vref s)\<rbrace>"
  by (simp add: vs_lookup_slot_def obind_def split: option.splits) wpsimp

lemma sts_valid_vspace_table_inv[wp]:
  "set_thread_state t st \<lbrace>valid_pti i\<rbrace>"
  unfolding valid_pti_def
  by (cases i; wpsimp wp: sts_typ_ats hoare_vcg_ex_lift hoare_vcg_all_lift
                      simp: invalid_pte_at_def aobjs_of_ako_at_Some[symmetric])

lemma sts_valid_arch_inv:
  "set_thread_state t st \<lbrace>valid_arch_inv ai\<rbrace>"
  apply (cases ai; simp add: valid_arch_inv_def; wp?)
   apply (rename_tac asid_control_invocation)
   apply (case_tac asid_control_invocation)
   apply (clarsimp simp: valid_aci_def cte_wp_at_caps_of_state)
   apply (rule hoare_pre, wp hoare_vcg_ex_lift cap_table_at_typ_at)
   apply clarsimp
  apply (clarsimp simp: valid_apinv_def split: asid_pool_invocation.splits)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift set_thread_state_ko)
  apply (clarsimp simp: is_tcb_def)
  done


crunch_ignore (add: select_ext find_vspace_for_asid)


crunches arch_decode_invocation
  for inv[wp]: "P"
  (wp: crunch_wps select_ext_weak_wp simp: crunch_simps)


declare lookup_slot_for_cnode_op_cap_to [wp]


lemma shiftr_irrelevant:
  "x < 2 ^ asid_low_bits \<Longrightarrow> is_aligned (y :: machine_word) asid_low_bits \<Longrightarrow>
    x + y >> asid_low_bits = y >> asid_low_bits"
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: is_aligned_nth)
   apply (drule(1) nth_bounded)
    apply (simp add: asid_low_bits_def word_bits_def)
   apply simp
  apply (rule word_eqI)
  apply (simp add: nth_shiftr)
  apply safe
  apply (drule(1) nth_bounded)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply simp
  done


declare mask_shift [simp]
declare word_less_sub_le [simp del]
declare ptrFormPAddr_addFromPPtr [simp]


lemma le_user_vtop_less_pptr_base[simp]:
  "x \<le> user_vtop \<Longrightarrow> x < pptr_base"
  using dual_order.strict_trans2 by blast

lemmas le_user_vtop_canonical_address = below_user_vtop_canonical[simp]

lemma ptrFromPAddr_addr_from_ppn:
  "is_aligned pt_ptr table_size \<Longrightarrow>
   ptrFromPAddr (addr_from_ppn (ucast (addrFromPPtr pt_ptr >> pageBits))) = pt_ptr"
  apply (simp add: addr_from_ppn_def ucast_ucast_mask bit_simps)
  apply (frule is_aligned_addrFromPPtr[simplified bit_simps])
  apply (simp add: aligned_shiftr_mask_shiftl mask_len_id[where 'a=machine_word_len, simplified])
  done

lemma ptrFromPAddr_addr_from_ppn':
  "is_aligned pt_ptr pt_bits \<Longrightarrow>
   ptrFromPAddr (addr_from_ppn (ucast (addrFromPPtr pt_ptr >> pt_bits))) = pt_ptr"
  using ptrFromPAddr_addr_from_ppn by (simp add: bit_simps)

lemma is_aligned_pageBitsForSize_table_size:
  "is_aligned p (pageBitsForSize vmpage_size) \<Longrightarrow> is_aligned p table_size"
  apply (erule is_aligned_weaken)
  apply (simp add: pbfs_atleast_pageBits[unfolded bit_simps] bit_simps)
  done

lemma vmsz_aligned_vref_for_level:
  "\<lbrakk> vmsz_aligned vref sz; pt_bits_left level = pageBitsForSize sz \<rbrakk> \<Longrightarrow>
   vref_for_level vref level = vref"
  by (simp add: vref_for_level_def vmsz_aligned_def)

lemma vs_lookup_slot_pte_at:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, pt_slot);
     vref \<in> user_region; level \<le> max_pt_level; invs s \<rbrakk> \<Longrightarrow>
   pte_at pt_slot s"
  apply (clarsimp simp: pte_at_eq vs_lookup_slot_table_unfold in_omonad)
  apply (drule valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (clarsimp simp: ptes_of_def in_omonad)
 (* pt_slot equation does not want to substitute in clarsimp, because rhs mentions pt_slot *)
  apply (rule subst[where P="\<lambda>pt_slot. is_aligned pt_slot pte_bits"], rule sym, assumption)
  apply (thin_tac "pt_slot = t" for t)
  apply (clarsimp simp: pt_slot_offset_def)
  apply (rule is_aligned_add; simp add: is_aligned_shift)
  done

lemma vmpage_size_of_level_pt_bits_left:
  "\<lbrakk> pt_bits_left level = pageBitsForSize vmpage_size; level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   vmpage_size_of_level level = vmpage_size"
  by (cases vmpage_size; simp add: vmpage_size_of_level_def pt_bits_left_def bit_simps) auto

lemma is_PagePTE_make_user[simp]:
  "is_PagePTE (make_user_pte p attr R) \<or> make_user_pte p attr R = InvalidPTE"
  by (auto simp: is_PagePTE_def make_user_pte_def)

lemma decode_fr_inv_map_wf[wp]:
  "arch_cap = FrameCap p rights vmpage_size dev option \<Longrightarrow>
   \<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at ((=) (ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s)\<rbrace>
   decode_fr_inv_map label args slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>,-"
  unfolding decode_fr_inv_map_def Let_def
  apply (wpsimp wp: check_vp_wpR split_del: if_split)
  apply (clarsimp simp: valid_arch_inv_def valid_page_inv_def neq_Nil_conv)
  apply (rename_tac s pt_ptr asid vref ab ba ys pt_slot level)
  apply (prop_tac "args!0 \<in> user_region")
   apply (clarsimp simp: user_region_def not_le)
   apply (rule user_vtop_canonical_user)
   apply (erule aligned_add_mask_lessD)
   apply (simp add: vmsz_aligned_def)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def is_cap_simps cap_master_cap_simps)
  apply (thin_tac "Ball S P" for S P)
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI, clarsimp)
  apply (clarsimp simp: valid_arch_cap_def valid_cap_def cap_aligned_def wellformed_mapdata_def)
  apply (frule is_aligned_pageBitsForSize_table_size)
  apply (frule (3) vs_lookup_slot_table_base)
  apply (clarsimp simp: same_ref_def make_user_pte_def ptrFromPAddr_addr_from_ppn)
  (* FIXME RISCV: remove duplication due to PagePTE/InvalidPTE cases: *)
  apply (rule conjI; clarsimp)
   apply (rule strengthen_imp_same_first_conj[OF conjI])
    apply (rule_tac x=level in exI)
    apply (rule_tac x="args!0" in exI)
    apply (fastforce simp: vmsz_aligned_vref_for_level)
   apply (rule strengthen_imp_same_first_conj[OF conjI])
    apply (clarsimp simp: valid_slots_def make_user_pte_def wellformed_pte_def
                          ptrFromPAddr_addr_from_ppn)
    apply (rename_tac level' asid' vref')
    apply (frule (3) vs_lookup_slot_table_base)
    apply (prop_tac "level' \<le> max_pt_level")
     apply (drule_tac level=level in valid_vspace_objs_strongD[rotated]; clarsimp)
     apply (rule ccontr, clarsimp simp: not_le)
     apply (drule vs_lookup_asid_pool; clarsimp)
     apply (clarsimp simp: in_omonad)
    apply (drule (1) vs_lookup_table_unique_level; clarsimp)
    apply (simp add: vs_lookup_slot_pte_at data_at_def vmpage_size_of_level_pt_bits_left
              split: if_split_asm)
   apply (rule strengthen_imp_same_first_conj[OF conjI])
    apply (clarsimp simp: wellformed_mapdata_def vspace_for_asid_def)
   apply (clarsimp simp: parent_for_refs_def)
   apply (frule (3) vs_lookup_slot_table_base)
   apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD; clarsimp simp: vmsz_aligned_vref_for_level)
   apply (subgoal_tac "is_pt_cap cap")
    apply (force simp: is_cap_simps)
   apply (fastforce dest: cap_to_pt_is_pt_cap intro: valid_objs_caps)
  apply (rule strengthen_imp_same_first_conj[OF conjI])
   apply (rule_tac x=level in exI)
   apply (rule_tac x="args!0" in exI)
   apply (fastforce simp: vmsz_aligned_vref_for_level)
  apply (rule strengthen_imp_same_first_conj[OF conjI])
   apply (clarsimp simp: valid_slots_def make_user_pte_def wellformed_pte_def
                         ptrFromPAddr_addr_from_ppn)
   apply (rename_tac level' asid' vref')
   apply (frule (3) vs_lookup_slot_table_base)
   apply (prop_tac "level' \<le> max_pt_level")
    apply (drule_tac level=level in valid_vspace_objs_strongD[rotated]; clarsimp)
    apply (rule ccontr, clarsimp simp: not_le)
    apply (drule vs_lookup_asid_pool; clarsimp)
    apply (clarsimp simp: in_omonad)
   apply (drule (1) vs_lookup_table_unique_level; clarsimp)
   apply (simp add: vs_lookup_slot_pte_at data_at_def vmpage_size_of_level_pt_bits_left
             split: if_split_asm)
  apply (rule strengthen_imp_same_first_conj[OF conjI])
   apply (clarsimp simp: wellformed_mapdata_def vspace_for_asid_def)
  apply (clarsimp simp: parent_for_refs_def)
  apply (frule (3) vs_lookup_slot_table_base)
  apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (drule (1) vs_lookup_table_target)
  apply (drule valid_vs_lookupD; clarsimp simp: vmsz_aligned_vref_for_level)
  apply (subgoal_tac "is_pt_cap cap")
   apply (force simp: is_cap_simps)
  apply (fastforce dest: cap_to_pt_is_pt_cap intro: valid_objs_caps)
  done

lemma decode_frame_invocation_wf[wp]:
  "arch_cap = FrameCap word rights vmpage_size dev option \<Longrightarrow>
   \<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at ((=) (ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s)\<rbrace>
   decode_frame_invocation label args slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>,-"
  unfolding decode_frame_invocation_def
  by (wpsimp simp: valid_arch_inv_def valid_page_inv_def cte_wp_at_caps_of_state
                   is_cap_simps valid_arch_cap_def valid_cap_def
                   valid_unmap_def wellformed_mapdata_def vmsz_aligned_def
            split: option.split)

lemma neg_mask_user_region:
  "p \<in> user_region \<Longrightarrow> p && ~~mask n \<in> user_region"
  apply (simp add: user_region_def canonical_user_def bit.conj_ac
              flip: and_mask_0_iff_le_mask)
  apply (subst bit.conj_assoc[symmetric])
  apply simp
  done

lemma decode_pt_inv_map_wf[wp]:
  "arch_cap = PageTableCap pt_ptr pt_map_data \<Longrightarrow>
   \<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at ((=) (ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s)\<rbrace>
    decode_pt_inv_map label args slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>,-"
  unfolding decode_pt_inv_map_def Let_def
  apply wpsimp
  apply (clarsimp simp: valid_arch_inv_def valid_pti_def pte_at_eq invalid_pte_at_def
                        wellformed_pte_def valid_cap_def cte_wp_at_caps_of_state)
  apply (rename_tac p level)
  apply (prop_tac "args!0 \<in> user_region")
   apply (simp add: wellformed_mapdata_def user_region_def user_vtop_canonical_user)
  apply (rule conjI, clarsimp simp: valid_arch_cap_def wellformed_mapdata_def vspace_for_asid_def
                                    neg_mask_user_region)
  apply (rule conjI, clarsimp simp: is_arch_update_def is_cap_simps cap_master_cap_simps)
  apply (simp add: ptrFromPAddr_addr_from_ppn cap_aligned_def)
  apply (drule (1) pt_lookup_slot_vs_lookup_slotI)
  apply (rule_tac x=level in exI, simp add: vm_level_not_less_zero)
  apply (clarsimp simp: obj_at_def)
  apply (rule conjI, clarsimp)
  apply (drule valid_table_caps_pdD, clarsimp)
  apply (clarsimp simp: in_omonad)
  apply (rule_tac x="args!0" in exI)
  apply (simp add: vref_for_level_def)
  done

lemma decode_page_table_invocation_wf[wp]:
  "arch_cap = PageTableCap pt_ptr pt_map_data \<Longrightarrow>
   \<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at ((=) (ArchObjectCap arch_cap)) slot and real_cte_at slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s)\<rbrace>
    decode_page_table_invocation label args slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>,-"
  unfolding decode_page_table_invocation_def is_final_cap_def
  apply (wpsimp simp: valid_arch_inv_def valid_pti_def valid_arch_cap_def valid_cap_def
                      cte_wp_at_caps_of_state is_cap_simps)
  apply (rule conjI; clarsimp)
  done

lemma cte_wp_at_eq_simp:
  "cte_wp_at ((=) cap) = cte_wp_at (\<lambda>c. c = cap)"
  by (force intro: arg_cong [where f=cte_wp_at])

lemma asid_low_hi_cast:
  "is_aligned asid_hi asid_low_bits \<Longrightarrow>
   ucast (ucast asid_low + (asid_hi::asid)) = (asid_low :: asid_low_index)"
  apply (simp add: is_aligned_nth asid_low_bits_def)
  apply (subst word_plus_and_or_coroll; word_eqI_solve)
  done

lemma decode_asid_pool_invocation_wf[wp]:
  "arch_cap = ASIDPoolCap ap asid \<Longrightarrow>
   \<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at ((=) (ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s) and
    (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> (fst x))\<rbrace>
   decode_asid_pool_invocation label args slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>, -"
  unfolding decode_asid_pool_invocation_def Let_def
  apply wpsimp
  apply (rule ccontr, erule notE[where P="valid_arch_inv i s" for i s])
  apply (clarsimp simp: valid_arch_inv_def valid_apinv_def pool_for_asid_def word_neq_0_conv
                        cte_wp_at_caps_of_state neq_Nil_conv obj_at_def in_omonad valid_cap_def
                        asid_low_hi_cast asid_high_bits_of_add_ucast)
  done

lemma decode_asid_control_invocation_wf[wp]:
  "arch_cap = ASIDControlCap \<Longrightarrow>
   \<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at ((=) (ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s) and
    (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> (fst x))\<rbrace>
   decode_asid_control_invocation label args slot ASIDControlCap excaps
   \<lbrace>valid_arch_inv\<rbrace>, -"
  unfolding decode_asid_control_invocation_def valid_arch_inv_def
  apply (simp add: Let_def split_def cong: if_cong split del: if_split)
  apply ((wp whenE_throwError_wp check_vp_wpR ensure_empty_stronger
         | wpc | simp add: valid_arch_inv_def valid_aci_def is_aligned_shiftl_self)+)[1]
          apply (rule_tac Q'= "\<lambda>rv. real_cte_at rv
                                     and ex_cte_cap_wp_to is_cnode_cap rv
                                     and (\<lambda>s. descendants_of (snd (excaps!0)) (cdt s) = {})
                                     and cte_wp_at (\<lambda>c. \<exists>idx. c = UntypedCap False frame pageBits idx) (snd (excaps!0))
                                     and (\<lambda>s. riscv_asid_table (arch_state s) free = None)"
                  in hoare_strengthen_postE_R)
           apply (simp add: lookup_target_slot_def)
           apply wp
          apply (clarsimp simp: cte_wp_at_def)
         apply (wpsimp wp: ensure_no_children_sp select_ext_weak_wp whenE_throwError_wp)+
  apply (rule conjI, fastforce)
  apply (cases excaps, simp)
  apply (case_tac list, simp)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (simp add: ex_cte_cap_wp_to_def)
   apply (rule_tac x=ac in exI)
   apply (rule_tac x=ba in exI)
   apply (clarsimp simp add: cte_wp_at_caps_of_state)
  apply (clarsimp simp add: cte_wp_at_caps_of_state)
  done

lemma arch_decode_inv_wf[wp]:
  "\<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at ((=) (ArchObjectCap arch_cap)) slot and real_cte_at slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s) and
    (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> (fst x))\<rbrace>
     arch_decode_invocation label args x_slot slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>,-"
  unfolding arch_decode_invocation_def by wpsimp fastforce

declare word_less_sub_le [simp]

crunches
  perform_page_table_invocation, perform_page_invocation, perform_asid_pool_invocation
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps)

lemma arch_pinv_st_tcb_at:
  "\<lbrace>invs and valid_arch_inv ai and ct_active and
    st_tcb_at (P and (Not \<circ> inactive) and (Not \<circ> idle)) t\<rbrace>
     arch_perform_invocation ai
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (cases ai; simp add: arch_perform_invocation_def valid_arch_inv_def)
  apply (wp perform_asid_control_invocation_st_tcb_at; fastforce elim!: pred_tcb_weakenE)+
  done

end


context begin interpretation Arch .

requalify_consts
  valid_arch_inv

requalify_facts
  invoke_arch_tcb
  invoke_arch_invs
  sts_valid_arch_inv
  arch_decode_inv_wf
  arch_pinv_st_tcb_at

end

declare invoke_arch_invs[wp]
declare arch_decode_inv_wf[wp]

end
