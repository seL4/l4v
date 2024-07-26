(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchArch_AI
imports Arch_AI
begin

context Arch begin arch_global_naming

definition
  "valid_aci aci \<equiv> case aci of MakePool frame slot parent base \<Rightarrow>
  \<lambda>s. cte_wp_at (\<lambda>c. c = cap.NullCap) slot s \<and> real_cte_at slot s \<and>
  ex_cte_cap_wp_to is_cnode_cap slot s \<and>
  slot \<noteq> parent \<and>
  cte_wp_at (\<lambda>cap. \<exists>idx. cap = UntypedCap False frame pageBits idx ) parent s \<and>
  descendants_of parent (cdt s) = {} \<and>
  is_aligned base asid_low_bits \<and> base \<le> 2^asid_bits - 1 \<and>
  arm_asid_table (arch_state s) (asid_high_bits_of base) = None"

definition
  "valid_vcpu_invocation vi \<equiv> case vi of
       VCPUSetTCB vcpu_ptr tcb_ptr \<Rightarrow> vcpu_at vcpu_ptr and tcb_at tcb_ptr and
                                      ex_nonz_cap_to vcpu_ptr and ex_nonz_cap_to tcb_ptr
                                      and (\<lambda>s. tcb_ptr \<noteq> idle_thread s)
     | VCPUInjectIRQ vcpu_ptr index virq \<Rightarrow> vcpu_at vcpu_ptr
     | VCPUReadRegister vcpu_ptr reg \<Rightarrow> vcpu_at vcpu_ptr
     | VCPUWriteRegister vcpu_ptr reg val \<Rightarrow> vcpu_at vcpu_ptr
     | VCPUAckVPPI vcpu_ptr vppi \<Rightarrow> vcpu_at vcpu_ptr"

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


lemma asid_low_bits_pageBits:
  "Suc (Suc asid_low_bits) = pageBits"
  by (simp add: pageBits_def asid_low_bits_def)


(* 32-bit instance of Detype_AI.range_cover_full *)
lemma range_cover_full:
  "\<lbrakk>is_aligned ptr sz;sz<word_bits\<rbrakk> \<Longrightarrow> range_cover (ptr::word32) sz sz (Suc 0)"
   by (clarsimp simp:range_cover_def unat_eq_0 le_mask_iff[symmetric] word_and_le1 word_bits_def)


definition
  valid_arch_inv :: "arch_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_inv \<equiv> \<lambda>ai. case ai of
     InvokePageTable pti \<Rightarrow>
       valid_pti pti
   | InvokePageDirectory pdi \<Rightarrow>
       valid_pdi pdi
   | InvokePage pinv \<Rightarrow>
       valid_page_inv pinv
   | InvokeASIDControl aci \<Rightarrow>
       valid_aci aci
   | InvokeASIDPool ap \<Rightarrow>
       valid_apinv ap
   | InvokeVCPU vi \<Rightarrow>
       valid_vcpu_invocation vi"


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
  "(2 ^ asid_low_bits - 1) = (max_word :: 10 word)"
  by (simp add: asid_low_bits_def)


lemma dom_ucast_eq:
  "(- dom (\<lambda>a::asid_low_index. p (ucast a::machine_word)) \<inter> {x. ucast x + y \<noteq> 0} = {}) =
   (- dom p \<inter> {x. x \<le> 2 ^ asid_low_bits - 1 \<and> x + y \<noteq> 0} = {})"
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
   apply (clarsimp simp: ucast_ucast_mask)
   apply (subst (asm) less_mask_eq)
   apply (rule word_less_sub_le [THEN iffD1])
     apply (simp add: word_bits_def)
    apply (simp add: asid_low_bits_def)
   apply simp
  apply (clarsimp simp: p2_low_bits_max)
  apply (rule ccontr)
  apply simp
  apply (erule_tac x="ucast x" in in_emptyE)
  apply clarsimp
  apply (rule conjI, blast)
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
  apply (rule ucast_less, simp)
  apply (simp add: asid_low_bits_def)
  done


lemma asid_high_bits_max_word:
  "(2 ^ asid_high_bits - 1 :: 7 word) = max_word"
  by (simp add: asid_high_bits_def)


lemma dom_ucast_eq_7:
  "(- dom (\<lambda>a::7 word. p (ucast a::word32)) \<inter> {x. x \<le> 2 ^ asid_high_bits - 1} = {}) =
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
  "- dom (\<lambda>x. pool (ucast (x::asid_low_index)::machine_word)) \<inter> {x. ucast x + (w::machine_word) \<noteq> 0} \<noteq> {}
  \<Longrightarrow>
  fst (hd [(x, y)\<leftarrow>assocs pool . x \<le> 2 ^ asid_low_bits - 1 \<and> x + w \<noteq> 0 \<and> y = None]) =
  ucast (fst (hd [(x, y)\<leftarrow>assocs (\<lambda>a::asid_low_index. pool (ucast a)) .
                          x \<le> 2 ^ asid_low_bits - 1 \<and>
                          ucast x + w \<noteq> 0 \<and> y = None]))"
  apply (simp add: ucast_assocs[unfolded o_def])
  apply (simp add: filter_map split_def)
  apply (simp cong: conj_cong add: ucast_ucast_len)
  apply (simp add: asid_low_bits_def minus_one_norm)
  apply (simp add: ord_le_eq_trans [OF word_n1_ge])
  apply (simp add: word_le_make_less)
  apply (subgoal_tac "P" for P)  (* cut_tac but more awesome *)
   apply (subst hd_map, assumption)
   apply simp
   apply (rule sym, rule ucast_ucast_len)
   apply (drule hd_in_set)
   apply simp
  apply (simp add: assocs_empty_dom_comp null_def split_def)
  apply (simp add: ucast_assocs[unfolded o_def] filter_map split_def)
  apply (simp cong: conj_cong add: ucast_ucast_len)
  done


crunch perform_page_table_invocation, perform_page_invocation,
         perform_asid_pool_invocation, perform_page_directory_invocation
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps)

crunch perform_vcpu_invocation
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps)

lemmas perform_page_table_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_page_table_invocation_typ_at]

lemmas perform_page_directory_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_page_directory_invocation_typ_at]

lemmas perform_page_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_page_invocation_typ_at]

lemmas perform_asid_pool_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_asid_pool_invocation_typ_at]

lemmas perform_vcpu_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_vcpu_invocation_typ_at]
(* ARMHYP FIXME this is not enough, add appropriate lifting rule to abs_typ_at_lifts *)

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
  "ucast (asid_high_bits_of w) \<le> (2 ^ asid_high_bits - 1 :: word32)"
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
  apply (cases ai, simp_all)
      apply (wp, clarsimp simp: st_tcb_at_tcb_at)+
    defer
    apply (wp, clarsimp simp: st_tcb_at_tcb_at)
   defer
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
     apply (simp add: vspace_bits_defs field_simps del: atLeastAtMost_iff)
    apply (metis (no_types) orthD1 x_power_minus_1)
   apply simp
  apply wp
  apply (clarsimp simp: st_tcb_at_def tcb_at_def obj_at_def is_tcb_def)
  done

end


locale asid_update = Arch +
  fixes ap asid s s'
  assumes ko: "ko_at (ArchObj (ASIDPool Map.empty)) ap s"
  assumes empty: "arm_asid_table (arch_state s) asid = None"
  defines "s' \<equiv> s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(asid \<mapsto> ap)\<rparr>\<rparr>"


context asid_update begin

lemma vs_lookup1' [simp]:
  "vs_lookup1 s' = vs_lookup1 s"
  by (simp add: vs_lookup1_def s'_def)


lemma vs_lookup_pages1' [simp]:
  "vs_lookup_pages1 s' = vs_lookup_pages1 s"
  by (simp add: vs_lookup_pages1_def s'_def)


lemma vs_asid_refs' [simp]:
  "vs_asid_refs (arm_asid_table (arch_state s')) =
  vs_asid_refs (arm_asid_table (arch_state s)) \<union> {([VSRef (ucast asid) None], ap)}"
  apply (simp add: s'_def)
  apply (rule set_eqI)
  apply (rule iffI)
   apply (auto simp: vs_asid_refs_def split: if_split_asm)[1]
  apply clarsimp
  apply (erule disjE)
   apply (auto simp: vs_asid_refs_def)[1]
  apply (subst (asm) vs_asid_refs_def)
  apply (clarsimp dest!: graph_ofD)
  apply (rule vs_asid_refsI)
  apply (clarsimp simp: empty)
  done


lemma vs_lookup':
  "vs_lookup s' = vs_lookup s \<union> {([VSRef (ucast asid) None], ap)}"
  using ko
  apply (simp add: vs_lookup_def)
  apply (rule rtrancl_insert)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def)
  done


lemma vs_lookup_pages':
  "vs_lookup_pages s' = vs_lookup_pages s \<union> {([VSRef (ucast asid) None], ap)}"
  using ko
  apply (simp add: vs_lookup_pages_def)
  apply (rule rtrancl_insert)
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def)
  done

lemma obj_at [simp]:
  "obj_at P p s' = obj_at P p s"
  by (simp add: s'_def)

lemma vs_lookup_neq: "\<lbrakk>(rs \<rhd> p) s' ; p \<noteq> ap\<rbrakk> \<Longrightarrow>  (rs \<rhd> p) s"
   by (clarsimp simp: vs_lookup')

lemma vspace_objs':
  "valid_vspace_objs s \<Longrightarrow> valid_vspace_objs s'"
  using ko
  apply (clarsimp simp: valid_vspace_objs_def)
  apply (erule_tac x=p in allE)
  apply (case_tac "p = ap";
         case_tac ao;
         fastforce simp: obj_at_def s'_def
                   intro: vs_lookup_neq)
  done

lemma caps_of_state_s':
  "caps_of_state s' = caps_of_state s"
  by (rule caps_of_state_pspace, simp add: s'_def)


lemma valid_vs_lookup':
  "\<lbrakk> valid_vs_lookup s;
     \<exists>ptr cap. caps_of_state s ptr = Some cap
     \<and> ap \<in> obj_refs cap \<and> vs_cap_ref cap = Some [VSRef (ucast asid) None] \<rbrakk>
  \<Longrightarrow> valid_vs_lookup s'"
  by (clarsimp simp: valid_vs_lookup_def caps_of_state_s' vs_lookup_pages')


lemma valid_table_caps':
  "\<lbrakk> valid_table_caps s \<rbrakk>
        \<Longrightarrow> valid_table_caps s'"
  apply (simp add: valid_table_caps_def caps_of_state_s')
  done


lemma valid_arch_caps:
  "\<lbrakk> valid_arch_caps s;
     \<exists>ptr cap. caps_of_state s ptr = Some cap
     \<and> ap \<in> obj_refs cap \<and> vs_cap_ref cap = Some [VSRef (ucast asid) None] \<rbrakk>
  \<Longrightarrow> valid_arch_caps s'"
  by (simp add: valid_arch_caps_def caps_of_state_s'
                valid_table_caps' valid_vs_lookup')


lemma valid_asid_map':
  "valid_asid_map s \<Longrightarrow> valid_asid_map s'"
  using empty
  apply (clarsimp simp: valid_asid_map_def s'_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: vspace_at_asid_def)
  apply (drule vs_lookup_2ConsD)
  apply clarsimp
  apply (erule vs_lookup_atE)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (rule vs_lookupI[rotated])
   apply (rule r_into_rtrancl)
   apply (rule vs_lookup1I)
     apply (fastforce simp: obj_at_def)
    apply assumption
   apply simp
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply fastforce
  done

end


context Arch begin arch_global_naming

lemma valid_arch_state_strg:
  "valid_arch_state s \<and> ap \<notin> ran (arm_asid_table (arch_state s)) \<and> asid_pool_at ap s \<longrightarrow>
   valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(asid \<mapsto> ap)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def split: option.split)
  apply (clarsimp simp: valid_asid_table_def ran_def)
  apply (fastforce intro!: inj_on_fun_updI)
  done


lemma valid_vs_lookup_at_upd_strg:
  "valid_vs_lookup s \<and>
   ko_at (ArchObj (ASIDPool Map.empty)) ap s \<and>
   arm_asid_table (arch_state s) asid = None \<and>
   (\<exists>ptr cap. caps_of_state s ptr = Some cap \<and> ap \<in> obj_refs cap \<and>
              vs_cap_ref cap = Some [VSRef (ucast asid) None])
   \<longrightarrow>
   valid_vs_lookup (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(asid \<mapsto> ap)\<rparr>\<rparr>)"
  apply clarsimp
  apply (subgoal_tac "asid_update ap asid s")
   prefer 2
   apply unfold_locales[1]
    apply assumption+
  apply (erule (1) asid_update.valid_vs_lookup')
  apply fastforce
  done


lemma retype_region_ap:
  "\<lbrace>\<top>\<rbrace>
  retype_region ap 1 0 (ArchObject ASIDPoolObj) dev
  \<lbrace>\<lambda>_. ko_at (ArchObj (arch_kernel_obj.ASIDPool Map.empty)) ap\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule retype_region_obj_at)
    apply simp
   apply simp
  apply (clarsimp simp: retype_addrs_def obj_bits_api_def default_arch_object_def)
  apply (clarsimp simp: obj_at_def default_object_def default_arch_object_def)
  done


lemma retype_region_ap':
  "\<lbrace>\<top>\<rbrace> retype_region ap 1 0 (ArchObject ASIDPoolObj) dev \<lbrace>\<lambda>rv. asid_pool_at ap\<rbrace>"
  apply (rule hoare_strengthen_post, rule retype_region_ap)
  apply (clarsimp simp: a_type_def elim!: obj_at_weakenE)
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
             and K (ty = Structures_A.CapTableObject \<longrightarrow> 0 < us)
             and K (range_cover ptr sz (obj_bits_api ty us) 1) \<rbrace>
     retype_region ptr 1 us ty dev
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: no_cap_to_obj_with_diff_ref_null_filter)
  apply (wp retype_region_caps_of | simp)+
  apply fastforce
  done


lemma valid_table_caps_asid_upd [iff]:
  "valid_table_caps (s\<lparr>arch_state := (arm_asid_table_update f (arch_state s))\<rparr>) =
   valid_table_caps s"
  by (simp add: valid_table_caps_def)


lemma vs_asid_ref_upd:
  "([VSRef (ucast (asid_high_bits_of asid')) None] \<rhd> ap')
    (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)
  = (if asid_high_bits_of asid' = asid_high_bits_of asid
    then ap' = ap
    else ([VSRef (ucast (asid_high_bits_of asid')) None] \<rhd> ap') s)"
  by (fastforce intro: vs_lookup_atI elim: vs_lookup_atE)


lemma vs_asid_ref_eq:
  "([VSRef (ucast asid) None] \<rhd> ap) s
  = (arm_asid_table (arch_state s) asid = Some ap)"
  by (fastforce elim: vs_lookup_atE intro: vs_lookup_atI)


lemma set_cap_reachable_pg_cap:
  "\<lbrace>\<lambda>s. P (reachable_pg_cap cap s)\<rbrace> set_cap x y \<lbrace>\<lambda>_ s. P (reachable_pg_cap cap s)\<rbrace>"
  by (unfold reachable_pg_cap_def, wp hoare_vcg_ex_lift set_cap.vs_lookup_pages)


lemma cap_insert_simple_arch_caps_ap:
  "\<lbrace>valid_arch_caps and (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s)
     and no_cap_to_obj_with_diff_ref cap {dest}
     and (\<lambda>s. arm_asid_table (arch_state s) (asid_high_bits_of asid) = None)
     and ko_at (ArchObj (ASIDPool Map.empty)) ap
     and K (cap = ArchObjectCap (ASIDPoolCap ap asid)) \<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv s. valid_arch_caps (s\<lparr>arch_state := arch_state s
                       \<lparr>arm_asid_table := (arm_asid_table (arch_state s))(asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: cap_insert_def update_cdt_def set_cdt_def valid_arch_caps_def
    set_untyped_cap_as_full_def bind_assoc)
  apply (strengthen valid_vs_lookup_at_upd_strg)
  apply (wp get_cap_wp set_cap_valid_vs_lookup set_cap_arch_obj
            set_cap_valid_table_caps hoare_vcg_all_lift
          | simp split del: if_split)+
       apply (rule_tac P = "cte_wp_at ((=) src_cap) src" in set_cap_orth)
       apply (wp hoare_vcg_imp_lift hoare_vcg_ball_lift set_free_index_final_cap
                 hoare_vcg_disj_lift set_cap_reachable_pg_cap set_cap.vs_lookup_pages
              | clarsimp)+
      apply (wp set_cap_arch_obj set_cap_valid_table_caps hoare_vcg_ball_lift
                get_cap_wp hoare_weak_lift_imp set_cap_empty_tables[simplified second_level_tables_def, simplified])+
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
   apply (rule_tac x="fst dest" in exI)
   apply (rule_tac x="snd dest" in exI)
   apply simp
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
   ko_at (ArchObj (ASIDPool Map.empty)) ap s \<and>
   arm_asid_table (arch_state s) asid = None \<longrightarrow>
   valid_asid_map (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(asid \<mapsto> ap)\<rparr>\<rparr>)"
  apply clarsimp
  apply (subgoal_tac "asid_update ap asid s")
   prefer 2
   apply unfold_locales[1]
    apply assumption+
  apply (erule (1) asid_update.valid_asid_map')
  done

lemma valid_vspace_objs_asid_upd_strg:
  "valid_vspace_objs s \<and>
   ko_at (ArchObj (ASIDPool Map.empty)) ap s \<and>
   arm_asid_table (arch_state s) asid = None \<longrightarrow>
   valid_vspace_objs (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(asid \<mapsto> ap)\<rparr>\<rparr>)"
  apply clarsimp
  apply (subgoal_tac "asid_update ap asid s")
   prefer 2
   apply unfold_locales[1]
    apply assumption+
  apply (erule (1) asid_update.vspace_objs')
  done

lemma safe_parent_cap_is_device:
  "safe_parent_for m p cap pcap \<Longrightarrow> cap_is_device cap = cap_is_device pcap"
  by (simp add: safe_parent_for_def)

lemma cap_insert_ap_invs:
  "\<lbrace>invs and valid_cap cap and tcb_cap_valid cap dest and
    ex_cte_cap_wp_to (appropriate_cte_cap cap) dest and
    cte_wp_at (\<lambda>c. c = NullCap) dest and
    no_cap_to_obj_with_diff_ref cap {dest} and
    (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s) and
    K (cap = ArchObjectCap (ASIDPoolCap ap asid)) and
   (\<lambda>s. \<forall>irq \<in> cap_irqs cap. irq_issued irq s) and
   ko_at (ArchObj (ASIDPool Map.empty)) ap and
   (\<lambda>s. ap \<notin> ran (arm_asid_table (arch_state s)) \<and>
        arm_asid_table (arch_state s) (asid_high_bits_of asid) = None)\<rbrace>
  cap_insert cap src dest
  \<lbrace>\<lambda>rv s. invs (s\<lparr>arch_state := arch_state s
                       \<lparr>arm_asid_table := ((arm_asid_table \<circ> arch_state) s)(asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)\<rbrace>"

  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (strengthen valid_arch_state_strg valid_vspace_objs_asid_upd_strg
                    valid_asid_map_asid_upd_strg )
  apply (simp cong: conj_cong)
  apply (rule hoare_pre)
   apply (wpsimp wp: cap_insert_simple_mdb cap_insert_iflive
             cap_insert_zombies cap_insert_ifunsafe
             cap_insert_valid_global_refs cap_insert_idle
             valid_irq_node_typ cap_insert_simple_arch_caps_ap
             simp: valid_global_objs_def valid_global_vspace_mappings_def)
  apply (clarsimp simp: is_simple_cap_def cte_wp_at_caps_of_state is_cap_simps)
  apply (frule safe_parent_cap_is_device)
  apply (drule safe_parent_cap_range)
  apply (simp add: cap_range_def)
  apply (rule conjI)
  apply clarsimp
   apply (drule_tac p="(a,b)" in caps_of_state_valid_cap, fastforce)
   apply (auto simp: obj_at_def is_tcb_def is_cap_table_def a_type_def
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
     apply (simp add:page_bits_def word_bits_def word_size_bits_def pageBits_def)+
   apply (simp add:is_aligned_neg_mask_eq)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at set_cap_no_overlap|simp)+
    apply (strengthen invs_valid_objs invs_psp_aligned)
    apply (clarsimp simp:conj_comms)
    apply (wp max_index_upd_invs_simple get_cap_wp)+
  apply (clarsimp simp: valid_aci_def)
  apply (frule intvl_range_conv)
   apply (simp add:word_bits_def page_bits_def pageBits_def)
  apply (clarsimp simp:detype_clear_um_independent page_bits_def is_aligned_neg_mask_eq)
  apply (rule conjI)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (rule pspace_no_overlap_detype)
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
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        p_assoc_help valid_cap_def valid_untyped_def cap_aligned_def)
  done

primrec(nonexhaustive)  get_untyped_cap_idx :: "cap \<Rightarrow> nat"
where "get_untyped_cap_idx (UntypedCap dev ref sz idx) = idx"


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
         (\<lambda>s. ap \<notin> ran (arm_asid_table (arch_state s)) \<and>
         arm_asid_table (arch_state s) (asid_high_bits_of asid) = None))\<rbrace>
         cap_insert cap src dest
        \<lbrace>\<lambda>rv s.
           invs
             (s\<lparr>arch_state := arch_state s
                 \<lparr>arm_asid_table := ((arm_asid_table \<circ> arch_state) s)
                    (asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>) \<and>
           Q
             (s\<lparr>arch_state := arch_state s
                 \<lparr>arm_asid_table := ((arm_asid_table \<circ> arch_state) s)
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
      apply (simp)
     apply wp
    apply (clarsimp simp: cte_wp_at_caps_of_state if_option_Some
                          if_bool_simps
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
    apply (rule conjI, clarsimp simp:valid_cap_simps cap_aligned_def page_bits_def not_le)+
    apply clarsimp
    apply (simp add:empty_descendants_range_in)
    apply (frule valid_cap_aligned)
    apply (clarsimp simp: cap_aligned_def)
    apply (subst caps_no_overlap_detype[OF descendants_range_caps_no_overlapI],
           assumption, simp, simp add: empty_descendants_range_in)
    apply (frule pspace_no_overlap_detype, clarify+)
    apply (frule intvl_range_conv[where bits = pageBits])
     apply (simp add:pageBits_def word_bits_def)
    apply (simp)
    apply (clarsimp simp: page_bits_def)
    apply (frule(1) ex_cte_cap_protects)
        apply (simp add:empty_descendants_range_in)
       apply fastforce
      apply (rule subset_refl)
     apply fastforce
    apply (clarsimp simp: field_simps)
    apply (intro conjI impI,
           simp_all add: free_index_of_def valid_cap_simps valid_untyped_def empty_descendants_range_in
                         range_cover_full clear_um_def max_free_index_def,
           (clarsimp simp:valid_untyped_def valid_cap_simps)+)[1]

       apply (simp add: cte_wp_at_def)

      apply (erule(1) cap_to_protected)
       apply (simp add:empty_descendants_range_in descendants_range_def2)+

     apply clarsimp
     apply (drule invs_arch_state)+
     apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
     apply (drule (1) bspec)+
     apply clarsimp
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

lemmas aci_invs[wp] = aci_invs'[where Q=\<top>,simplified hoare_TrueI, OF refl refl refl TrueI TrueI TrueI,simplified]

lemma obj_at_upd2:
  "obj_at P t' (s\<lparr>kheap := (kheap s)(t \<mapsto> v, x \<mapsto> v')\<rparr>) =
   (if t' = x then P v' else obj_at P t' (s\<lparr>kheap := (kheap s)(t \<mapsto> v)\<rparr>))"
  by (simp add: obj_at_update obj_at_def)

lemma vcpu_invalidate_active_hyp_refs_empty[wp]:
  "\<lbrace>obj_at (\<lambda>ko. hyp_refs_of ko = {}) p\<rbrace> vcpu_invalidate_active \<lbrace>\<lambda>r. obj_at (\<lambda>ko. hyp_refs_of ko = {}) p\<rbrace>"
  unfolding vcpu_invalidate_active_def vcpu_disable_def by wpsimp

lemma as_user_hyp_refs_empty[wp]:
  "\<lbrace>obj_at (\<lambda>ko. hyp_refs_of ko = {}) p\<rbrace> as_user t f \<lbrace>\<lambda>r. obj_at (\<lambda>ko. hyp_refs_of ko = {}) p\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: get_tcb_Some_ko_at obj_at_def arch_tcb_context_set_def)

lemma dissociate_vcpu_tcb_obj_at_hyp_refs[wp]:
  "\<lbrace>\<lambda>s. p \<notin> {t, vr} \<longrightarrow> obj_at (\<lambda>ko. hyp_refs_of ko = {}) p s \<rbrace>
     dissociate_vcpu_tcb t vr
   \<lbrace>\<lambda>rv s. obj_at (\<lambda>ko. hyp_refs_of ko = {}) p s\<rbrace>"
  unfolding dissociate_vcpu_tcb_def
  apply (cases "p \<notin> {t, vr}"; clarsimp)
   apply (wp arch_thread_set_wp set_vcpu_wp)
        apply (clarsimp simp: obj_at_upd2 obj_at_update)
        apply (wp hoare_drop_imp get_vcpu_wp)+
   apply (clarsimp simp: obj_at_upd2 obj_at_update)
  apply (erule disjE;
          (wp arch_thread_set_wp set_vcpu_wp
          | clarsimp simp: obj_at_upd2 obj_at_update)+)
  done

lemma associate_vcpu_tcb_sym_refs_hyp[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace> associate_vcpu_tcb vr t \<lbrace>\<lambda>rv s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: associate_vcpu_tcb_def)
  apply (wp arch_thread_set_wp set_vcpu_wp | clarsimp)+
      apply (rule_tac P="\<lambda>s. ko_at (ArchObj (VCPU v)) vr s \<and>
                             obj_at (\<lambda>ko. hyp_refs_of ko = {} ) t s  \<and>
                             sym_refs (state_hyp_refs_of s)"
                          in hoare_triv)
      apply (rule_tac Q'="\<lambda>rv s. obj_at (\<lambda>ko. hyp_refs_of ko = {} ) vr s \<and>
                                obj_at (\<lambda>ko. hyp_refs_of ko = {} ) t s  \<and>
                                sym_refs (state_hyp_refs_of s)"
                             in hoare_post_imp)
       apply (clarsimp dest!: get_tcb_SomeD simp: obj_at_def)
       apply (clarsimp simp add: sym_refs_def)
       apply (case_tac "x = t"; case_tac "x = vr"; clarsimp simp add: state_hyp_refs_of_def obj_at_def
                                                                 dest!: get_tcb_SomeD)
       apply fastforce
      apply (rule hoare_pre)
       apply (wp | wpc | clarsimp)+
      apply (simp add: obj_at_def)
     apply (wp  get_vcpu_ko | wpc | clarsimp)+
   apply (rule_tac Q'="\<lambda>rv s. (\<exists>t'. obj_at (\<lambda>tcb. tcb = TCB t' \<and> rv = tcb_vcpu (tcb_arch t')) t s) \<and>
                             sym_refs (state_hyp_refs_of s)"
                          in hoare_post_imp)
    apply (clarsimp simp: obj_at_def)
   apply (wp arch_thread_get_tcb)
  apply simp
  done

lemma arch_thread_set_inv_neq:
  "\<lbrace>obj_at P p and K (t \<noteq> p)\<rbrace> arch_thread_set f t \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  unfolding arch_thread_set_def by (wpsimp wp: set_object_wp) (simp add: obj_at_def)

lemma live_vcpu [simp]:
  "live (ArchObj (VCPU (v\<lparr>vcpu_tcb := Some tcb\<rparr>)))"
  by (simp add: live_def hyp_live_def arch_live_def)

lemma ex_nonz_cap_to_vcpu_udpate[simp]:
  "ex_nonz_cap_to t (s\<lparr>arch_state := arm_current_vcpu_update f (arch_state s)\<rparr>) = ex_nonz_cap_to t s"
  by (simp add: ex_nonz_cap_to_def)

lemma caps_of_state_VCPU_update:
  "vcpu_at a s \<Longrightarrow> caps_of_state (s\<lparr>kheap := (kheap s)(a \<mapsto> ArchObj (VCPU b))\<rparr>) = caps_of_state s"
  by (rule ext) (auto simp: caps_of_state_cte_wp_at cte_wp_at_cases obj_at_def)

lemma set_vcpu_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to t\<rbrace> set_vcpu a b \<lbrace>\<lambda>_. ex_nonz_cap_to t\<rbrace>"
  apply (wp set_vcpu_wp)
  apply (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state caps_of_state_VCPU_update)
  done

lemma caps_of_state_tcb_arch_update:
  "ko_at (TCB y) t' s \<Longrightarrow> caps_of_state (s\<lparr>kheap := (kheap s)(t' \<mapsto> TCB (y\<lparr>tcb_arch := f (tcb_arch y)\<rparr>))\<rparr>) = caps_of_state s"
  by (rule ext) (auto simp: caps_of_state_cte_wp_at cte_wp_at_cases obj_at_def tcb_cap_cases_def)

lemma arch_thread_set_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to t\<rbrace> arch_thread_set f t' \<lbrace>\<lambda>_. ex_nonz_cap_to t\<rbrace>"
  apply (wp arch_thread_set_wp)
  apply clarsimp
  apply (clarsimp simp: ex_nonz_cap_to_def get_tcb_Some_ko_at cte_wp_at_caps_of_state
                        caps_of_state_tcb_arch_update)
  done

crunch dissociate_vcpu_tcb
  for ex_nonz_cap_to[wp]: "ex_nonz_cap_to t"
  (wp: crunch_wps)

crunch vcpu_switch
  for if_live_then_nonz_cap[wp]: if_live_then_nonz_cap
  (wp: crunch_wps)

lemma associate_vcpu_tcb_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to vcpu and ex_nonz_cap_to tcb\<rbrace>
    associate_vcpu_tcb vcpu tcb \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  unfolding associate_vcpu_tcb_def
  by (wpsimp wp: arch_thread_set_inv_neq hoare_disjI1 get_vcpu_wp hoare_vcg_all_lift hoare_drop_imps)

lemma set_vcpu_valid_arch_Some[wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_vcpu vcpu (v\<lparr>vcpu_tcb := Some tcb\<rparr>) \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (wp set_vcpu_wp)
  apply (clarsimp simp: valid_arch_state_def)
  apply (rule conjI)
   apply (fastforce simp: valid_asid_table_def obj_at_def)
  apply (clarsimp simp: obj_at_def is_vcpu_def hyp_live_def arch_live_def split: option.splits)
  done

lemma valid_global_objs_vcpu_update_str:
  "valid_global_objs s \<Longrightarrow> valid_global_objs (s\<lparr>arch_state := arm_current_vcpu_update f (arch_state s)\<rparr>)"
  by (simp add: valid_global_objs_def)

lemma valid_global_vspace_mappings_vcpu_update_str:
  "valid_global_vspace_mappings s \<Longrightarrow> valid_global_vspace_mappings (s\<lparr>arch_state := arm_current_vcpu_update f (arch_state s)\<rparr>)"
  by (simp add: valid_global_vspace_mappings_def)

lemma arm_current_vcpu_update_valid_global_vspace_mappings[simp]:
  "valid_global_vspace_mappings (s\<lparr>arch_state := arm_current_vcpu_update f (arch_state s)\<rparr>)
   = valid_global_vspace_mappings s"
  by (clarsimp simp: valid_global_vspace_mappings_def global_refs_def
              split: kernel_object.splits option.splits)

crunch associate_vcpu_tcb
  for pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and zombies_final[wp]: zombies_final
  and sym_refs_state_refs_of[wp]: "\<lambda>s. sym_refs (state_refs_of s)"
  and valid_mdb[wp]: valid_mdb
  and valid_ioc[wp]: valid_ioc
  and only_idle[wp]: only_idle
  and if_unsafe_then_cap[wp]: if_unsafe_then_cap
  and valid_reply_caps[wp]: valid_reply_caps
  and valid_reply_masters[wp]: valid_reply_masters
  and valid_irq_node[wp]: valid_irq_node
  and valid_irq_handlers[wp]: valid_irq_handlers
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and cur_tcb[wp]: cur_tcb
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_arch_caps[wp]: valid_arch_caps
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and valid_asid_map[wp]: valid_asid_map
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  (wp: crunch_wps dmo_valid_irq_states device_region_dmos simp: crunch_simps)

crunch vcpu_switch
  for valid_idle[wp]: valid_idle
  (wp: crunch_wps)

lemma associate_vcpu_tcb_valid_idle[wp]:
  "\<lbrace>valid_idle and (\<lambda>s. tcb \<noteq> idle_thread s)\<rbrace> associate_vcpu_tcb vcpu tcb \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (clarsimp simp: associate_vcpu_tcb_def)
  by (wp hoare_vcg_all_lift
      | wp (once) hoare_drop_imps
      | wpc
      | simp add: dissociate_vcpu_tcb_def vcpu_invalidate_active_def)+

lemma arm_current_vcpu_update_valid_global_refs[simp]:
  "valid_global_refs (s\<lparr>arch_state := arm_current_vcpu_update f (arch_state s)\<rparr>) = valid_global_refs s"
  by (clarsimp simp: valid_global_refs_def global_refs_def
              split: kernel_object.splits option.splits)

crunch associate_vcpu_tcb
  for valid_global_refs[wp]: valid_global_refs
  (wp: crunch_wps)

crunch vcpu_restore_reg
  for valid_irq_states[wp]: valid_irq_states
  (wp: crunch_wps dmo_valid_irq_states simp: writeVCPUHardwareReg_def)

lemma is_irq_active_sp:
  "\<lbrace>P\<rbrace> get_irq_state irq \<lbrace>\<lambda>rv s. P s \<and> (rv = interrupt_states s irq)\<rbrace>"
  by (wpsimp simp: get_irq_state_def)

lemma restore_virt_timer_valid_irq_states[wp]:
  "restore_virt_timer vcpu_ptr \<lbrace>valid_irq_states\<rbrace>"
  apply (clarsimp simp: restore_virt_timer_def is_irq_active_def liftM_def)
  apply (repeat_unless \<open>rule bind_wp[OF _ is_irq_active_sp]\<close>
                       \<open>rule bind_wp_fwd_skip,
                        wpsimp wp: dmo_valid_irq_states
                             simp: isb_def setHCR_def set_cntv_cval_64_def read_cntpct_def
                                   set_cntv_off_64_def\<close>)
  apply (wpsimp simp: do_machine_op_def is_irq_active_def get_irq_state_def)
  apply (clarsimp simp: valid_irq_states_def valid_irq_masks_def maskInterrupt_def in_monad)
  done

crunch vcpu_switch
  for valid_irq_states[wp]: valid_irq_states
  (wp: crunch_wps dmo_valid_irq_states set_gic_vcpu_ctrl_hcr_irq_masks
       set_gic_vcpu_ctrl_vmcr_irq_masks set_gic_vcpu_ctrl_lr_irq_masks
       set_gic_vcpu_ctrl_apr_irq_masks
   simp: get_gic_vcpu_ctrl_lr_def get_gic_vcpu_ctrl_apr_def get_gic_vcpu_ctrl_vmcr_def
         get_gic_vcpu_ctrl_hcr_def maskInterrupt_def isb_def setHCR_def)

lemma associate_vcpu_tcb_valid_irq_states[wp]:
  "associate_vcpu_tcb vcpu tcb \<lbrace>valid_irq_states\<rbrace>"
  apply (clarsimp simp: associate_vcpu_tcb_def)
  by (wp hoare_vcg_all_lift
      | wp (once) hoare_drop_imps
      | wpc
      | simp add: dissociate_vcpu_tcb_def vcpu_invalidate_active_def)+

crunch associate_vcpu_tcb
  for cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  (wp: crunch_wps cap_refs_respects_device_region_dmo
   simp: set_cntv_cval_64_def read_cntpct_def set_cntv_off_64_def
         get_irq_state_def maskInterrupt_def)

lemma arm_current_vcpu_update_valid_global_objs[simp]:
  "valid_global_objs (s\<lparr>arch_state := arm_current_vcpu_update f (arch_state s)\<rparr>) = valid_global_objs s"
  by (clarsimp simp: valid_global_objs_def)

crunch associate_vcpu_tcb
  for valid_global_objs[wp]: valid_global_objs
  (wp: crunch_wps device_region_dmos)

lemma set_vcpu_tcb_Some_hyp_live[wp]:
  "\<lbrace>\<top>\<rbrace> set_vcpu vcpu (v\<lparr>vcpu_tcb := Some tcb\<rparr>) \<lbrace>\<lambda>_. obj_at hyp_live vcpu\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp)
  apply (clarsimp simp: obj_at_def hyp_live_def arch_live_def)
  done

lemma associate_vcpu_tcb_valid_arch_state[wp]:
  "associate_vcpu_tcb vcpu tcb \<lbrace>valid_arch_state\<rbrace>"
  apply (clarsimp simp: associate_vcpu_tcb_def)
  apply (wpsimp wp: vcpu_switch_valid_arch)
        apply (rule_tac Q'="\<lambda>_. valid_arch_state and obj_at hyp_live vcpu" in hoare_post_imp)
         apply fastforce
        apply wpsimp
       apply (wpsimp wp: arch_thread_set.valid_arch_state)
      apply (wpsimp wp: arch_thread_set_wp)+
  done

lemma dmo_valid_machine_state[wp]:
  "do_machine_op (set_cntv_cval_64 w) \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op read_cntpct \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op (set_cntv_off_64 w') \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op (maskInterrupt m irq) \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op (setHCR word) \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op isb \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op dsb \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op (set_gic_vcpu_ctrl_hcr f) \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op (set_gic_vcpu_ctrl_lr n w'') \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op (set_gic_vcpu_ctrl_apr w''') \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op (set_gic_vcpu_ctrl_vmcr w''') \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op (get_gic_vcpu_ctrl_lr w'''') \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op get_gic_vcpu_ctrl_apr \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op get_gic_vcpu_ctrl_vmcr \<lbrace>valid_machine_state\<rbrace>"
  "do_machine_op get_gic_vcpu_ctrl_hcr \<lbrace>valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def set_cntv_cval_64_def read_cntpct_def set_cntv_off_64_def
            maskInterrupt_def setHCR_def set_gic_vcpu_ctrl_hcr_def set_gic_vcpu_ctrl_lr_def
            set_gic_vcpu_ctrl_apr_def set_gic_vcpu_ctrl_vmcr_def get_gic_vcpu_ctrl_lr_def
            get_gic_vcpu_ctrl_apr_def get_gic_vcpu_ctrl_vmcr_def get_gic_vcpu_ctrl_hcr_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift dmo_machine_state_lift)+

crunch restore_virt_timer, vcpu_restore_reg_range, vcpu_save_reg_range, vgic_update_lr
  for valid_machine_state[wp]: valid_machine_state
  (wp: crunch_wps ignore: do_machine_op)

lemma vcpu_enable_valid_machine_state[wp]:
  "vcpu_enable vcpu \<lbrace>valid_machine_state\<rbrace>"
  apply (simp add: vcpu_enable_def)
  by (wpsimp | subst do_machine_op_bind | simp add: isb_def)+

crunch vcpu_restore, vcpu_save
  for valid_machine_state[wp]: valid_machine_state
  (wp: mapM_wp_inv simp: do_machine_op_bind dom_mapM empty_fail_cond ignore: do_machine_op)

crunch associate_vcpu_tcb
  for valid_machine_state[wp]: valid_machine_state
  (wp: crunch_wps ignore: do_machine_op simp: get_gic_vcpu_ctrl_lr_def do_machine_op_bind)

lemma associate_vcpu_tcb_valid_objs[wp]:
  "\<lbrace>valid_objs and vcpu_at vcpu\<rbrace>
   associate_vcpu_tcb vcpu tcb
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  by (wp arch_thread_get_wp
      | wp (once) hoare_drop_imps
      | wpc
      | clarsimp simp: associate_vcpu_tcb_def valid_obj_def[abs_def] valid_vcpu_def
      | simp add: obj_at_def)+

lemma associate_vcpu_tcb_invs[wp]:
  "\<lbrace>invs and ex_nonz_cap_to vcpu and ex_nonz_cap_to tcb and vcpu_at vcpu and (\<lambda>s. tcb \<noteq> idle_thread s)\<rbrace>
   associate_vcpu_tcb vcpu tcb
   \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def)

lemma set_vcpu_regs_update[wp]:
  "\<lbrace>invs and valid_obj p (ArchObj (VCPU vcpu)) and
    obj_at (\<lambda>ko'. hyp_refs_of ko' = vcpu_tcb_refs (vcpu_tcb vcpu)) p\<rbrace>
  set_vcpu p (vcpu_regs_update f vcpu) \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding invs_def valid_state_def
  by (wpsimp wp: set_vcpu_valid_pspace set_vcpu_valid_arch_eq_hyp)

lemma write_vcpu_register_invs[wp]:
  "\<lbrace>invs\<rbrace> write_vcpu_register vcpu reg val \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding write_vcpu_register_def
  by wpsimp

lemma vgic_update_valid_pspace[wp]:
  "\<lbrace>valid_pspace\<rbrace> vgic_update vcpuptr f \<lbrace>\<lambda>_. valid_pspace\<rbrace>"
  unfolding vgic_update_def vcpu_update_def
  apply (wpsimp wp: set_vcpu_valid_pspace get_vcpu_wp simp: valid_vcpu_def)
  apply (fastforce simp: obj_at_def dest!: valid_pspace_vo)
  done

crunch invoke_vcpu_inject_irq, vcpu_read_reg
  for invs[wp]: invs (ignore: do_machine_op)

lemma invoke_vcpu_ack_vppi_invs[wp]:
  "invoke_vcpu_ack_vppi vcpu_ptr vppi \<lbrace>invs\<rbrace>"
  unfolding invoke_vcpu_ack_vppi_def by (wpsimp cong: vcpu.fold_congs)

lemma perform_vcpu_invs[wp]:
  "\<lbrace>invs and valid_vcpu_invocation vi\<rbrace> perform_vcpu_invocation vi \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: perform_vcpu_invocation_def valid_vcpu_invocation_def)
  apply (wpsimp simp: invoke_vcpu_read_register_def read_vcpu_register_def
                      invoke_vcpu_write_register_def)
  done

lemma invoke_arch_invs[wp]:
  "\<lbrace>invs and ct_active and valid_arch_inv ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases ai, simp_all add: valid_arch_inv_def arch_perform_invocation_def)
  apply (wp perform_vcpu_invs |simp)+
  done


lemma sts_empty_pde [wp]:
  "\<lbrace>empty_pde_at p\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. empty_pde_at p\<rbrace>"
  apply (simp add: empty_pde_at_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift set_thread_state_ko)
  apply (clarsimp simp: is_tcb_def)
  done


lemma sts_pd_at_asid [wp]:
  "\<lbrace>vspace_at_asid asid pd\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. vspace_at_asid asid pd\<rbrace>"
  apply (simp add: vspace_at_asid_def)
  apply wp
  done


lemma sts_same_refs_inv[wp]:
  "\<lbrace>\<lambda>s. same_refs m cap s\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. same_refs m cap s\<rbrace>"
  by (cases m, (clarsimp simp: same_refs_def, wp)+)


lemma sts_valid_slots_inv[wp]:
  "\<lbrace>valid_slots m\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  by (cases m, (clarsimp simp: valid_slots_def, wp hoare_vcg_ball_lift sts.vs_lookup sts_typ_ats)+)


lemma sts_valid_page_inv[wp]:
"\<lbrace>valid_page_inv page_invocation\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_page_inv page_invocation\<rbrace>"
  by (cases page_invocation,
       (wp hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_disj_lift sts_typ_ats
        | clarsimp simp: valid_page_inv_def same_refs_def
        | wps)+)


lemma sts_valid_pdi_inv[wp]:
  "\<lbrace>valid_pdi page_directory_invocation\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_pdi page_directory_invocation\<rbrace>"
  apply (cases page_directory_invocation)
   apply (wp | simp add: valid_pdi_def)+
  done


lemma sts_valid_vcpu_invocation_inv:
  "\<lbrace>valid_vcpu_invocation vcpu_invocation\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_vcpu_invocation vcpu_invocation\<rbrace>"
  unfolding valid_vcpu_invocation_def by (cases vcpu_invocation; wpsimp)

lemma sts_valid_arch_inv:
  "\<lbrace>valid_arch_inv ai\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_arch_inv ai\<rbrace>"
  apply (cases ai, simp_all add: valid_arch_inv_def)
     apply (rename_tac page_table_invocation)
     apply (case_tac page_table_invocation, simp_all add: valid_pti_def)[1]
      apply ((wp valid_pde_lift set_thread_state_valid_cap
                 hoare_vcg_all_lift hoare_vcg_const_imp_lift
                 hoare_vcg_ex_lift set_thread_state_ko
                 sts_typ_ats set_thread_state_cte_wp_at
               | clarsimp simp: is_tcb_def)+)[4]
   apply (rename_tac asid_control_invocation)
   apply (case_tac asid_control_invocation)
   apply (clarsimp simp: valid_aci_def cte_wp_at_caps_of_state)
   apply (rule hoare_pre, wp hoare_vcg_ex_lift cap_table_at_typ_at)
   apply clarsimp
  apply (clarsimp simp: valid_apinv_def split: asid_pool_invocation.splits)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift set_thread_state_ko)
  apply (clarsimp simp: is_tcb_def, wp sts_valid_vcpu_invocation_inv)
  done

crunch ensure_safe_mapping, create_mapping_entries
  for inv[wp]: "P"
  (wp: crunch_wps mapME_x_inv_wp)

crunch_ignore (add: select_ext)

crunch arch_decode_invocation
  for inv[wp]: "P"
  (wp: crunch_wps select_ext_weak_wp simp: crunch_simps)


lemma create_mappings_empty [wp]:
  "\<lbrace>\<top>\<rbrace> create_mapping_entries base vptr vmsz R A pd \<lbrace>\<lambda>m s. empty_refs m\<rbrace>, -"
  apply (cases vmsz, simp_all add: empty_refs_def)
    apply (wpsimp simp: pde_ref_def)+
  done


lemma empty_pde_atI:
  "\<lbrakk> ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s;
     pd (ucast (p && mask pd_bits >> 3)) = InvalidPDE \<rbrakk> \<Longrightarrow>
   empty_pde_at p s"
  by (fastforce simp add: vspace_bits_defs empty_pde_at_def)


declare lookup_slot_for_cnode_op_cap_to [wp]


lemma shiftr_irrelevant:
  "x < 2 ^ asid_low_bits \<Longrightarrow> is_aligned (y :: word32) asid_low_bits \<Longrightarrow>
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

lemma map_up_enum_0x78:
  "is_aligned (r::32 word) 7 \<Longrightarrow> map (\<lambda>x. x + r) [0 , 8 .e. 0x78] = [r, r + 8 .e. r + 0x78]"
  apply (simp add: upto_enum_step_def upto_enum_def not_less)
  apply (drule is_aligned_no_overflow')
  apply simp
  apply (erule word_plus_mono_right2)
  apply simp
  done

lemma create_mapping_entries_parent_for_refs:
  "\<lbrace>invs and \<exists>\<rhd> pd and page_directory_at pd
           and K (is_aligned pd pd_bits) and K (vmsz_aligned vptr pgsz)
           and K (vptr < kernel_base)\<rbrace>
    create_mapping_entries ptr vptr pgsz
                 rights attribs pd
   \<lbrace>\<lambda>rv s. \<exists>a b. cte_wp_at (parent_for_refs rv) (a, b) s\<rbrace>, -"
  apply (rule hoare_gen_asmE)+
  apply (cases pgsz,
         simp_all add: vmsz_aligned_def largePagePTE_offsets_def superSectionPDE_offsets_def
                       pte_bits_def pde_bits_def)
     apply (rule hoare_pre)
      apply wp
      apply (rule hoare_strengthen_postE_R, rule lookup_pt_slot_cap_to)
      apply (elim exEI)
      apply (clarsimp simp: cte_wp_at_caps_of_state parent_for_refs_def)
     apply simp
    apply (rule hoare_pre)
     apply wp
     apply (rule hoare_strengthen_postE_R)
      apply (rule lookup_pt_slot_cap_to_multiple1)
     apply (elim conjE exEI cte_wp_at_weakenE)
     apply (clarsimp simp: cte_wp_at_caps_of_state parent_for_refs_def
                           subset_iff p_0x3C_shift map_up_enum_0x78)
    apply simp
   apply (rule hoare_pre, wp)
   apply (clarsimp dest!:vs_lookup_pages_vs_lookupI)
   apply (drule valid_vs_lookupD, clarsimp)
   apply (simp, elim exEI)
   apply (clarsimp simp: cte_wp_at_caps_of_state parent_for_refs_def
                         lookup_pd_slot_def Let_def)
   apply (subst pd_shifting, simp add: pd_bits_def pageBits_def pde_bits_def)
   apply (clarsimp simp: vs_cap_ref_def
                  split: cap.split_asm arch_cap.split_asm option.split_asm)
     apply (auto simp: valid_cap_def obj_at_def is_cap_simps cap_asid_def
                dest!: caps_of_state_valid_cap split:if_splits)[3]
     apply (frule(1) caps_of_state_valid)
     apply (clarsimp simp:valid_cap_def obj_at_def)
   apply (simp add:is_cap_simps)
  apply (rule hoare_pre, wp)
  apply (clarsimp dest!:vs_lookup_pages_vs_lookupI)
  apply (drule valid_vs_lookupD, clarsimp)
  apply (simp, elim exEI)
  apply (clarsimp simp: cte_wp_at_caps_of_state parent_for_refs_def)
  apply (rule conjI)
   apply (simp add: subset_eq)
   apply (clarsimp simp: lookup_pd_slot_add_eq)
  apply (clarsimp simp: vs_cap_ref_def
                 split: cap.split_asm arch_cap.split_asm option.split_asm)
       apply (auto simp: valid_cap_def obj_at_def is_cap_simps cap_asid_def
             dest!: caps_of_state_valid_cap split:if_splits)[3]
   apply (frule(1) caps_of_state_valid)
   apply (clarsimp simp:valid_cap_def obj_at_def)
  apply (simp add:is_cap_simps)
  done


lemma find_pd_for_asid_shifting_voodoo:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace>
     find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. v >> 21 = rv + (v >> 21 << 3) && mask pd_bits >> 3\<rbrace>,-"
  apply (rule hoare_strengthen_postE_R,
         rule find_pd_for_asid_aligned_pd, simp add: vspace_bits_defs)
  apply (subst pd_shifting_dual[simplified vspace_bits_defs, simplified], simp)
  apply (rule word_eqI)
  apply (simp add: nth_shiftr nth_shiftl word_size)
  apply safe
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done


lemma find_pd_for_asid_ref_offset_voodoo:
  "\<lbrace>pspace_aligned and valid_vspace_objs and
         K (ref = [VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                  VSRef (ucast (asid_high_bits_of asid)) None])\<rbrace>
      find_pd_for_asid asid
   \<lbrace>\<lambda>rv. (ref \<rhd> (rv + (v >> 21 << 3) && ~~ mask pd_bits))\<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (rule_tac Q'="\<lambda>rv s. is_aligned rv 14 \<and> (ref \<rhd> rv) s"
               in hoare_strengthen_postE_R)
   apply (simp add: ucast_ucast_mask
                    mask_asid_low_bits_ucast_ucast)
   apply (fold asid_low_bits_def)
   apply (rule hoare_pre, wp find_pd_for_asid_lookup_ref)
   apply (simp add: vspace_bits_defs)
  apply (simp add: pd_shifting[simplified vspace_bits_defs, simplified] vspace_bits_defs)
  done


declare asid_high_bits_of_shift [simp]
declare mask_shift [simp]
declare word_less_sub_le [simp del]
declare ptrFormPAddr_addFromPPtr [simp]


lemma vs_lookup_and_unique_refs:
  "\<lbrakk>(ref \<rhd> p) s; caps_of_state s cptr = Some cap; table_cap_ref cap = Some ref';
    p \<in> obj_refs cap; valid_vs_lookup s; unique_table_refs (caps_of_state s)\<rbrakk>
   \<Longrightarrow> ref = ref'"
  apply (frule_tac ref=ref in valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], assumption)
  apply clarsimp
  apply (frule_tac cap'=capa in unique_table_refsD)
     apply simp+
   apply (case_tac capa, simp_all)
        apply ((case_tac cap, simp_all)+)[6]
     apply (clarsimp simp add: table_cap_ref_def vs_cap_ref_def split: cap.splits arch_cap.splits option.splits)
  done


lemma create_mapping_entries_same_refs:
  "\<lbrace>valid_arch_state and valid_vspace_objs and valid_vs_lookup and (\<lambda>s. unique_table_refs (caps_of_state s))
    and pspace_aligned and valid_objs and valid_kernel_mappings and \<exists>\<rhd> pd and
    (\<lambda>s. \<exists>dev pd_cap pd_cptr. cte_wp_at ((=) pd_cap) pd_cptr s
          \<and> pd_cap = ArchObjectCap (PageDirectoryCap pd (Some asid))) and
    page_directory_at pd and K (vaddr < kernel_base \<and> (cap = (ArchObjectCap (PageCap dev p rights' pgsz (Some (asid, vaddr))))))\<rbrace>
   create_mapping_entries (addrFromPPtr p) vaddr pgsz rights attribs pd
   \<lbrace>\<lambda>rv s. same_refs rv cap s\<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (cases pgsz, simp_all add: lookup_pt_slot_def)
     apply (wp get_pde_wp | wpc)+
     apply (clarsimp simp: lookup_pd_slot_def)
     apply (frule (1) pd_aligned)
     apply (simp add: pd_shifting)
     apply (simp add: vaddr_segment_nonsense2 pageBits_def pt_bits_def pte_bits_def pde_bits_def)
     apply (frule (2) valid_vspace_objsD[rotated], simp)
     apply (erule_tac x="ucast (vaddr >> 21)" in allE)
     apply (simp, drule (1) pt_aligned)
     apply (clarsimp simp: same_refs_def vs_cap_ref_def split: option.splits)
     apply (simp add: vaddr_segment_nonsense4 shiftl_shiftr_id mask_def[of 9]
                      less_trans[OF and_mask_less'[where n=9, unfolded mask_def, simplified]]
                      word_bits_def pageBits_def
                      vaddr_segment_nonsense3)
     apply (rule conjI, simp add: mask_def pt_bits_def pte_bits_def)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (frule (1) vs_lookup_and_unique_refs)
         apply (simp_all add: table_cap_ref_def obj_refs_def)[4]
     apply (frule_tac p=pd and p'="ptrFromPAddr x" in vs_lookup_step)
      apply (clarsimp simp: vs_lookup1_def)
      apply (rule exI, erule conjI)
      apply (rule exI[where x="VSRef (vaddr >> 21) (Some APageDirectory)"])
      apply (rule conjI, rule refl)
      apply (simp add: vs_refs_def)
      apply (rule_tac x="(ucast (vaddr >> 21), ptrFromPAddr x)" in image_eqI)
       apply (simp add: ucast_ucast_len[OF shiftr_less_t2n'] graph_of_def)
      apply (clarsimp simp:graph_of_def)
      apply (simp add: pde_ref_def)
     apply simp
     apply (drule (1) ref_is_unique)
           apply (simp add: ptrFromPAddr_def)
          apply (simp_all add: pde_ref_def valid_arch_state_def valid_objs_caps pt_bits_def)[8]
    apply (wp get_pde_wp | wpc)+
    apply (clarsimp simp: lookup_pd_slot_def)
    apply (frule (1) pd_aligned)
    apply (simp add: pd_shifting)
    apply (simp add: vaddr_segment_nonsense2 pageBits_def pt_bits_def pte_bits_def pde_bits_def)
    apply (frule (2) valid_vspace_objsD[rotated], simp)
    apply (erule_tac x="ucast (vaddr >> 21)" in allE)
    apply (simp, drule (1) pt_aligned)
    apply (simp add: largePagePTE_offsets_def pte_bits_def)
    apply (clarsimp simp: same_refs_def vs_cap_ref_def upto_enum_step_def upto_enum_word upt_conv_Cons)
    apply (simp add: vaddr_segment_nonsense4 shiftl_shiftr_id
                     less_trans[OF and_mask_less'[where n=9, unfolded mask_def, simplified]]
                     word_bits_def pageBits_def  mask_def [of 9]
                     vaddr_segment_nonsense3)
    apply (simp add: pt_bits_def pte_bits_def)
    apply (rule conjI, simp add: mask_def)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (frule (1) vs_lookup_and_unique_refs)
        apply (simp_all add: table_cap_ref_def obj_refs_def)[4]
    apply (frule_tac p=pd and p'="ptrFromPAddr x" in vs_lookup_step)
     apply (clarsimp simp: vs_lookup1_def)
     apply (rule exI, erule conjI)
     apply (rule exI[where x="VSRef (vaddr >> 21) (Some APageDirectory)"])
     apply (rule conjI, rule refl)
     apply (simp add: vs_refs_def)
     apply (rule_tac x="(ucast (vaddr >> 21), ptrFromPAddr x)" in image_eqI)
      apply (simp add: ucast_ucast_len[OF shiftr_less_t2n'] graph_of_def)
     apply (clarsimp simp:graph_of_def)
     apply (simp add: pde_ref_def)
    apply simp
    apply (drule (1) ref_is_unique)
          apply (simp add: ptrFromPAddr_def)
         apply (simp_all add: pde_ref_def valid_arch_state_def valid_objs_caps)[8]
   apply (wp get_pde_wp returnOKE_R_wp | wpc)+
   apply (clarsimp simp: lookup_pd_slot_def)
   apply (frule (1) pd_aligned)
   apply (clarsimp simp: same_refs_def vs_cap_ref_def pde_ref_pages_def)
   apply (simp add: vaddr_segment_nonsense vaddr_segment_nonsense2
                    pageBits_def pt_bits_def pte_bits_def pde_bits_def)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (frule (1) vs_lookup_and_unique_refs)
       apply (simp_all add: table_cap_ref_def obj_refs_def)[4]
   apply (drule (1) ref_is_unique)
         apply (simp_all add: valid_arch_state_def valid_objs_caps)[7]
  apply (wp returnOKE_R_wp | wpc)+
  apply (clarsimp simp: lookup_pd_slot_def)
  apply (frule (1) pd_aligned)
  apply (simp add: superSectionPDE_offsets_def pde_bits_def pageBits_def pt_bits_def)
  apply (clarsimp simp: same_refs_def vs_cap_ref_def pde_ref_pages_def upto_enum_step_def upto_enum_word upt_conv_Cons)
  apply (simp add: vaddr_segment_nonsense vaddr_segment_nonsense2 pageBits_def pt_bits_def)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule (1) vs_lookup_and_unique_refs)
      apply (simp_all add: table_cap_ref_def obj_refs_def)[4]
  apply (drule (1) ref_is_unique)
        apply (clarsimp simp: obj_at_def a_type_def valid_arch_state_def)
       apply (simp_all add: valid_arch_state_def valid_objs_caps)
  done


lemma create_mapping_entries_same_refs_ex:
  "\<lbrace>valid_arch_state and valid_vspace_objs and valid_vs_lookup and (\<lambda>s. unique_table_refs (caps_of_state s))
    and pspace_aligned and valid_objs and valid_kernel_mappings and \<exists>\<rhd> pd and
    (\<lambda>s. \<exists>dev pd_cap pd_cptr asid rights'. cte_wp_at ((=) pd_cap) pd_cptr s
          \<and> pd_cap = cap.ArchObjectCap (arch_cap.PageDirectoryCap pd (Some asid))
          \<and> page_directory_at pd s \<and> vaddr < kernel_base \<and> (cap = (cap.ArchObjectCap (arch_cap.PageCap dev p rights' pgsz (Some (asid, vaddr))))))\<rbrace>
   create_mapping_entries (Platform.ARM_HYP.addrFromPPtr p) vaddr pgsz rights attribs pd
   \<lbrace>\<lambda>rv s. same_refs rv cap s\<rbrace>,-"
  apply (clarsimp simp: validE_R_def validE_def valid_def split: sum.split)
  apply (erule use_validE_R[OF _ create_mapping_entries_same_refs])
  apply fastforce
  done


lemma find_pd_for_asid_lookup_pd_wp:
  "\<lbrace> \<lambda>s. valid_vspace_objs s \<and> (\<forall>pd. vspace_at_asid asid pd s \<and> page_directory_at pd s
    \<and> (\<exists>\<rhd> pd) s \<longrightarrow> Q pd s) \<rbrace> find_pd_for_asid asid \<lbrace> Q \<rbrace>, -"
  apply (rule hoare_strengthen_postE_R)
   apply (rule hoare_vcg_conj_liftE_R[OF find_pd_for_asid_page_directory])
   apply (rule hoare_vcg_conj_liftE_R[OF find_pd_for_asid_lookup, simplified])
   apply (rule hoare_vcg_conj_liftE_R[OF find_pd_for_asid_pd_at_asid, simplified])
   apply (wp (once) find_pd_for_asid_inv)
  apply auto
  done


lemma aligned_sum_less_kernel_base:
  "vmsz_aligned p sz
    \<Longrightarrow> (p + 2 ^ pageBitsForSize sz - 1 < kernel_base) = (p < kernel_base)"
  apply (rule iffI)
   apply (rule le_less_trans)
    apply (rule is_aligned_no_overflow)
    apply (simp add: vmsz_aligned_def)
   apply simp
  apply (simp add:field_simps[symmetric])
  apply (erule gap_between_aligned)
    apply (simp add: vmsz_aligned_def)+
   apply (case_tac sz,simp_all add:kernel_base_def is_aligned_def)+
  done

lemma find_pd_for_asid_pde_unfolded[wp]:
  "\<lbrace>valid_vspace_objs and pspace_aligned\<rbrace>
  find_pd_for_asid asid
  \<lbrace>\<lambda>pd. pde_at (pd + (vptr >> 21 << 3))\<rbrace>, -"
  apply (rule hoare_strengthen_postE_R, rule find_pd_for_asid_pde)
  apply (simp add: pageBits_def pt_bits_def pde_bits_def)
  done

lemma arch_decode_inv_wf[wp]:
  "\<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at ((=) (ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s)\<rbrace>
     arch_decode_invocation label args cap_index slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>,-"
  supply if_split[split del]
  apply (cases arch_cap)
       apply (rename_tac word1 word2)
       apply (simp add: arch_decode_invocation_def Let_def decode_mmu_invocation_def split_def cong: if_cong)
       apply (rule hoare_pre)
        apply ((wp whenE_throwError_wp check_vp_wpR ensure_empty_stronger select_ext_weak_wp|
                wpc|
                simp add: valid_arch_inv_def valid_apinv_def)+)[1]
       apply (simp add: if_apply_def2 valid_apinv_def)
       apply (intro allI impI ballI)
       apply (elim conjE exE)
       apply simp
       apply (clarsimp simp: dom_def neq_Nil_conv)
       apply (thin_tac "Ball S P" for S P)+
       apply (clarsimp simp: valid_cap_def)
       apply (rule conjI)
        apply (clarsimp simp: obj_at_def)
        apply (subgoal_tac "ucast (ucast xa + word2) = xa")
         apply simp
        apply (simp add: is_aligned_nth)
        apply (subst word_plus_and_or_coroll)
         apply (rule word_eqI)
         apply (clarsimp simp: word_size word_bits_def nth_ucast)
         apply (drule test_bit_size)
         apply (simp add: word_size asid_low_bits_def)
        apply (rule word_eqI)
        apply (clarsimp simp: word_size word_bits_def nth_ucast)
        apply (auto simp: asid_low_bits_def)[1]
       apply (rule conjI)
        apply (clarsimp simp add: cte_wp_at_caps_of_state)
        apply (rename_tac c c')
        apply (frule_tac cap="(ArchObjectCap (PageDirectoryCap xb None))" in caps_of_state_valid,
               assumption)
        apply (clarsimp simp: is_pd_cap_def cap_rights_update_def acap_rights_update_def)
       apply (clarsimp simp: word_neq_0_conv)
       apply (rule conjI)
        apply (subst field_simps, erule is_aligned_add_less_t2n)
          apply (simp add: asid_low_bits_def)
          apply (rule ucast_less[where 'b=10, simplified], simp)
         apply (simp add: asid_low_bits_def asid_bits_def)
        apply (simp add: asid_bits_def)
       apply (drule vs_lookup_atI)
       apply (subst asid_high_bits_of_add_ucast, assumption)
       apply assumption
      apply (simp add: arch_decode_invocation_def Let_def split_def decode_mmu_invocation_def
                 cong: if_cong)
      apply (rule hoare_pre)
       apply ((wp whenE_throwError_wp check_vp_wpR ensure_empty_stronger|
               wpc|
               simp add: valid_arch_inv_def valid_aci_def is_aligned_shiftl_self)+)[1]
              apply (rule_tac Q'=
                         "\<lambda>rv. real_cte_at rv and
                               ex_cte_cap_wp_to is_cnode_cap rv and
                               (\<lambda>s. descendants_of (snd (excaps!0)) (cdt s) = {}) and
                               cte_wp_at (\<lambda>c. \<exists>idx. c = (cap.UntypedCap False frame pageBits idx)) (snd (excaps!0)) and
                               (\<lambda>s. arm_asid_table (arch_state s) free = None)"
                         in hoare_strengthen_postE_R)
               apply (simp add: lookup_target_slot_def)
               apply wp
              apply (clarsimp simp: cte_wp_at_def)
              apply (rule conjI, clarsimp)
              apply (rule shiftl_less_t2n)
               apply (rule order_less_le_trans, rule ucast_less, simp)
               apply (simp add: asid_bits_def asid_low_bits_def)
              apply (simp add: asid_bits_def)
             apply simp
             apply (wp ensure_no_children_sp select_ext_weak_wp whenE_throwError_wp|wpc | simp)+
      apply clarsimp
      apply (rule conjI, fastforce)
      apply (cases excaps, simp)
      apply (case_tac list, simp)
      apply clarsimp
      apply (rule conjI)
       apply (drule cte_wp_at_norm, clarsimp, drule cte_wp_valid_cap, fastforce)+
       apply assumption
      apply (rule conjI)
       apply clarsimp
       apply (simp add: ex_cte_cap_wp_to_def)
       apply (rule_tac x=ac in exI)
       apply (rule_tac x=ba in exI)
       apply (clarsimp simp add: cte_wp_at_caps_of_state)
      apply (clarsimp simp add: cte_wp_at_caps_of_state)
     apply (clarsimp simp: cap_rights_update_def)
     apply (simp add: arch_decode_invocation_def Let_def split_def decode_mmu_invocation_def
                cong: if_cong)
     apply (cases "invocation_type label = ArchInvocationLabel ARMPageMap")
      apply (rename_tac word rights vmpage_size option)
      apply simp
      apply (wpsimp wp: whenE_throwError_wp check_vp_wpR create_mapping_entries_parent_for_refs
                        find_pd_for_asid_pd_at_asid create_mapping_entries_valid_slots
                        create_mapping_entries_same_refs_ex hoare_vcg_ex_lift_R hoare_vcg_disj_lift_R
                        hoare_vcg_const_imp_liftE_R find_pd_for_asid_lookup_pd_wp
                  simp: valid_arch_inv_def valid_page_inv_def is_pg_cap_def
                        cte_wp_at_caps_of_state[where P="\<lambda>c. same_refs rv c s" for rv s])
      apply (clarsimp simp: neq_Nil_conv)
      apply (frule cte_wp_valid_cap[where p="(a, b)" for a b], clarsimp)
      apply (frule cte_wp_valid_cap[where p=slot], clarsimp)
      apply (clarsimp simp: cte_wp_at_caps_of_state mask_cap_def)
      apply (clarsimp simp: cap_rights_update_def acap_rights_update_def
                     split: cap.splits arch_cap.splits if_splits)
      apply (rename_tac page_size mapped_data)
      apply (intro conjI allI impI;
             (clarsimp simp: invs_implies valid_cap_simps cap_aligned_def valid_kernel_mappings_def
                             aligned_sum_less_kernel_base[symmetric] asid_bits_def mask_def
                             is_arch_update_def cap_master_cap_simps is_arch_cap_def data_at_def
                             vmsz_aligned_def is_aligned_addrFromPPtr_n vs_cap_ref_def
                             cte_wp_at_caps_of_state is_cap_simps
                      split: if_splits vmpage_size.split);
              fastforce)
     apply (cases "invocation_type label = ArchInvocationLabel ARMPageUnmap")
      apply simp
      apply (rule hoare_pre, wp)
      apply (clarsimp simp: valid_arch_inv_def valid_page_inv_def)
      apply (thin_tac "Ball S P" for S P)
      apply (clarsimp split: option.split)
      apply (clarsimp simp: valid_cap_def cap_aligned_def)
      apply (simp add: valid_unmap_def)
      apply (fastforce simp: vmsz_aligned_def elim: is_aligned_weaken intro!: pbfs_atleast_pageBits)
     apply (cases "isPageFlushLabel (invocation_type label)")
      apply simp
      apply (rule hoare_pre)
       apply (wp whenE_throwError_wp hoare_weak_lift_imp hoare_drop_imps)
         apply (simp add: valid_arch_inv_def valid_page_inv_def)
         apply (wp find_pd_for_asid_pd_at_asid | wpc)+
      apply (clarsimp simp: valid_cap_def mask_def)
     apply simp
     apply (cases "invocation_type label = ArchInvocationLabel ARMPageGetAddress")
      apply simp
      apply (rule hoare_pre, wp)
      apply (clarsimp simp: valid_arch_inv_def valid_page_inv_def)
     apply (rule hoare_pre, wp)
     apply (simp)
    apply (simp add: arch_decode_invocation_def Let_def split_def
                     is_final_cap_def decode_mmu_invocation_def
               cong: if_cong)
    apply (rename_tac word option)
    apply (rule hoare_pre)
     apply ((wp whenE_throwError_wp check_vp_wpR get_master_pde_wp hoare_vcg_all_liftE_R
             | wpc
             | simp add: valid_arch_inv_def valid_pti_def unlessE_whenE vs_cap_ref_def
                  split: if_split
             | rule_tac x="fst p" in hoare_imp_eq_substR
             | wp (once) hoare_vcg_ex_lift_R)+)[1]
          apply (rule_tac Q'="\<lambda>a b. ko_at (ArchObj (PageDirectory pd))
                                    (a + (args ! 0 >> 21 << 3) && ~~ mask pd_bits) b \<longrightarrow>
                                    pd (ucast (a + (args ! 0 >> 21 << 3) && mask pd_bits >> 3)) =
                                    InvalidPDE \<longrightarrow> L word option p pd a b" for L in hoare_strengthen_postE_R[rotated])
           apply (intro impI)
           apply (erule impE)
            apply (clarsimp simp: pageBits_def pde_bits_def pt_bits_def)
           apply (erule impE)
            apply (clarsimp simp: pageBits_def pde_bits_def pt_bits_def split:pde.splits)
           apply assumption
          apply ((wp whenE_throwError_wp hoare_vcg_all_liftE_R
                     find_pd_for_asid_lookup_slot [unfolded lookup_pd_slot_def Let_def]
                     find_pd_for_asid_ref_offset_voodoo find_pd_for_asid_shifting_voodoo
                     find_pd_for_asid_inv
                  | wpc
                  | simp add: valid_arch_inv_def valid_pti_def unlessE_whenE empty_pde_atI
                              vs_cap_ref_def pageBits_def pt_bits_def pde_bits_def
                  | wp (once) hoare_drop_imps hoare_vcg_ex_lift_R)+)[6]
    apply (clarsimp simp: is_cap_simps if_apply_def2)
    apply (rule conjI)
     apply clarsimp
     apply (rule conjI, fastforce)
     apply (rule conjI, fastforce)
     apply (clarsimp simp: neq_Nil_conv)
     apply (thin_tac "Ball S P" for S P)
     apply (rule conjI)
      apply (clarsimp simp: valid_cap_def cap_aligned_def
                            pte_bits_def pt_bits_def is_aligned_addrFromPPtr_n)
     apply (rule conjI)
      apply (clarsimp simp: valid_cap_def cap_aligned_def)
     apply (rule conjI)
      apply (drule cte_wp_at_norm, clarsimp, drule cte_wp_valid_cap, fastforce)+
      apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
      apply (clarsimp simp: valid_cap_def cap_aligned_def
                            pt_bits_def pageBits_def
                            linorder_not_le
                            order_le_less_trans[OF word_and_le2])
     apply (rule conjI)
      apply (clarsimp simp add: cte_wp_at_caps_of_state)
      apply (drule (1) caps_of_state_valid[rotated])
      apply clarsimp
      apply (clarsimp simp: cap_master_cap_def is_arch_update_def)
      apply (clarsimp simp: cap_asid_def cap_rights_update_def acap_rights_update_def is_cap_simps
                     split: option.split)
     apply (rule conjI, fastforce)
     apply (rule conjI, fastforce)
     apply (clarsimp simp: pde_ref_def)
     apply (frule invs_pd_caps)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (frule (1) caps_of_state_valid[rotated])
     apply (clarsimp simp: cap_rights_update_def acap_rights_update_def valid_cap_def)
     apply (drule (2) valid_table_caps_ptD)
     apply (rule conjI, fastforce)+
     apply (clarsimp simp: kernel_vsrefs_def)
     apply fastforce
    apply (clarsimp simp: cte_wp_at_def is_cap_simps
                          valid_arch_inv_def valid_pti_def)
   apply (simp add: arch_decode_invocation_def Let_def decode_mmu_invocation_def cong: if_cong)
   apply (cases "isPDFlushLabel (invocation_type label)")
    apply simp
    apply (rule hoare_pre)
     apply (wp whenE_throwError_wp hoare_weak_lift_imp hoare_drop_imp | wpc | simp)+
           apply (simp add: resolve_vaddr_def)
           apply (wp get_master_pte_wp get_master_pde_wp whenE_throwError_wp | wpc | simp)+
         apply (clarsimp simp: valid_arch_inv_def valid_pdi_def)+
         apply (rule_tac Q'="\<lambda>pd' s. vspace_at_asid x2 pd' s \<and> x2 \<le> mask asid_bits \<and> x2 \<noteq> 0" in hoare_strengthen_postE_R)
          apply wp
         apply clarsimp
        apply (wp | wpc)+
    apply (clarsimp simp: valid_cap_def mask_def)
   apply (clarsimp, wp throwError_validE_R)

(* VCPU *)
  apply (rename_tac vcpu_ptr)
  apply (clarsimp simp: arch_decode_invocation_def decode_vcpu_invocation_def)
  apply (cases "invocation_type label"; (simp, wp?))
  apply (rename_tac arch_iv)
  apply (case_tac "arch_iv"; (simp, wp?))
      apply (simp add: decode_vcpu_set_tcb_def)
      apply (rule hoare_pre, wpsimp)
      apply (clarsimp simp: valid_arch_inv_def valid_vcpu_invocation_def)
      apply (rename_tac tcb_ptr)
      apply (frule_tac c="ThreadCap tcb_ptr" in cte_wp_valid_cap, fastforce)
      apply (simp add: valid_cap_def)
      apply (cases slot)
      apply (clarsimp simp: ex_nonz_cap_to_def)
      apply (rule conjI, fastforce elim: cte_wp_at_weakenE)
      apply (rule conjI, fastforce elim: cte_wp_at_weakenE)
      apply (clarsimp dest!: invs_valid_global_refs simp:  cte_wp_at_caps_of_state)
      apply (drule_tac ?cap="ThreadCap (idle_thread s)" in valid_global_refsD2, assumption)
      apply (simp add:global_refs_def cap_range_def)
     apply (simp add: decode_vcpu_inject_irq_def)
     apply (rule hoare_pre, wpsimp simp: whenE_def wp: get_vcpu_wp)
     apply (clarsimp simp: valid_arch_inv_def valid_vcpu_invocation_def obj_at_def)
    apply (simp add: decode_vcpu_read_register_def)
    apply (rule hoare_pre, wpsimp)
    apply (clarsimp simp: valid_arch_inv_def valid_cap_def valid_vcpu_invocation_def)
   apply (simp add: decode_vcpu_write_register_def)
   apply (rule hoare_pre, wpsimp)
   apply (clarsimp simp: valid_arch_inv_def valid_cap_def valid_vcpu_invocation_def)
  apply (simp add: decode_vcpu_ack_vppi_def arch_check_irq_def)
  apply (rule hoare_pre, wpsimp)
  apply (clarsimp simp: valid_arch_inv_def valid_cap_def valid_vcpu_invocation_def)
  done


declare word_less_sub_le [simp]

crunch associate_vcpu_tcb
  for pred_tcb_at[wp_unsafe]: "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps)

crunch vcpu_read_reg, vcpu_write_reg, invoke_vcpu_inject_irq
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"

lemma perform_vcpu_invocation_pred_tcb_at[wp_unsafe]:
  "\<lbrace>pred_tcb_at proj P t and K (proj_not_field proj tcb_arch_update)\<rbrace>
     perform_vcpu_invocation iv
   \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: perform_vcpu_invocation_def)
  apply (rule hoare_pre)
  apply (wp associate_vcpu_tcb_pred_tcb_at | wpc
        | clarsimp simp: invoke_vcpu_read_register_def
                         read_vcpu_register_def
                         invoke_vcpu_write_register_def
                         write_vcpu_register_def
                         invoke_vcpu_ack_vppi_def)+
  done

crunch perform_page_table_invocation, perform_page_invocation,
           perform_asid_pool_invocation,
           perform_page_directory_invocation
  for pred_tcb_at: "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps)


lemma arch_pinv_st_tcb_at:
  "\<lbrace>invs and valid_arch_inv ai and ct_active and
    st_tcb_at (P and (Not \<circ> inactive) and (Not \<circ> idle)) t\<rbrace>
     arch_perform_invocation ai
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (cases ai, simp_all add: arch_perform_invocation_def valid_arch_inv_def)
      apply (wp perform_page_table_invocation_pred_tcb_at,
             fastforce elim!: pred_tcb_weakenE)
      apply (wp perform_page_directory_invocation_pred_tcb_at, fastforce elim: pred_tcb_weakenE)
     apply (wp perform_page_invocation_pred_tcb_at, fastforce elim!: pred_tcb_weakenE)
    apply (wp perform_asid_control_invocation_st_tcb_at,
           fastforce elim!: pred_tcb_weakenE)
   apply (wp perform_asid_pool_invocation_pred_tcb_at,
          fastforce elim!: pred_tcb_weakenE)
  apply (wp perform_vcpu_invocation_pred_tcb_at,
         fastforce elim!: pred_tcb_weakenE)
  done

end

end
