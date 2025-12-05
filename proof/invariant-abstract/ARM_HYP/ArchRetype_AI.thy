(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 Arch-specific retype invariants
*)

theory ArchRetype_AI
imports Retype_AI
begin

context Arch begin arch_global_naming

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
  "no_gs_types \<equiv> UNIV - {Structures_A.CapTableObject,
     ArchObject SmallPageObj, ArchObject LargePageObj,
     ArchObject SectionObj, ArchObject SuperSectionObj}"

lemma no_gs_types_simps [simp, Retype_AI_assms]:
  "Untyped \<in> no_gs_types"
  "TCBObject \<in> no_gs_types"
  "EndpointObject \<in> no_gs_types"
  "NotificationObject \<in> no_gs_types"
  "ArchObject PageTableObj \<in> no_gs_types"
  "ArchObject PageDirectoryObj \<in> no_gs_types"
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

declare store_pde_state_refs_of [wp]


(* These also prove facts about copy_global_mappings *)
crunch init_arch_objects
  for pspace_aligned[wp]:  "pspace_aligned"
  and pspace_distinct[wp]: "pspace_distinct"
  and mdb_inv[wp]: "\<lambda>s. P (cdt s)"
  and valid_mdb[wp]: "valid_mdb"
  and cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (ignore: clearMemory wp: crunch_wps)

crunch store_pde
  for mdb_inv[wp]: "\<lambda>s. P (cdt s)"
  (ignore: clearMemory wp: crunch_wps)

lemma mdb_cte_at_store_pde[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>
   store_pde y pde
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
done

lemma get_pde_valid[wp]:
  "\<lbrace>valid_vspace_objs
    and \<exists>\<rhd> (x && ~~mask pd_bits)\<rbrace>
   get_pde x
   \<lbrace>valid_pde\<rbrace>"
  apply (simp add: get_pde_def)
  apply wp
  apply clarsimp
  apply (drule (2) valid_vspace_objsD)
  apply simp
  done

lemma get_master_pde_valid[wp]:
  "\<lbrace>valid_vspace_objs
    and \<exists>\<rhd> (x && ~~mask pd_bits)\<rbrace>
   get_master_pde x
   \<lbrace>valid_pde\<rbrace>"
  apply (simp add: get_master_pde_def get_pde_def)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift | wpc)+
     defer
     apply (clarsimp simp: mask_lower_twice pd_bits_def pageBits_def)+
  apply (drule sym)
  apply (drule (1) ko_at_obj_congD, clarsimp)
  apply (drule (2) valid_vspace_objsD)
  apply simp
  done


lemma get_pde_wellformed[wp]:
  "\<lbrace>valid_objs\<rbrace> get_pde x \<lbrace>\<lambda>rv _. wellformed_pde rv\<rbrace>"
  apply (simp add: get_pde_def)
  apply wp
  apply (fastforce simp add: valid_objs_def dom_def obj_at_def valid_obj_def)
  done

crunch init_arch_objects
  for valid_objs[wp]: "valid_objs"
  (ignore: clearMemory wp: crunch_wps)

lemma set_pd_arch_state[wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_pd ptr val \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (rule set_pd_valid_arch)

crunch init_arch_objects
  for valid_arch_state[wp]: "valid_arch_state"
  (ignore: clearMemory set_object wp: crunch_wps)

lemmas init_arch_objects_valid_cap[wp] = valid_cap_typ [OF init_arch_objects_typ_at]

lemmas init_arch_objects_cap_table[wp] = cap_table_at_typ_at [OF init_arch_objects_typ_at]

crunch clearMemory
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
  (wp: mapM_x_wp ignore_del: clearMemory)

crunch reserve_region
  for pspace_respects_device_region[wp]: pspace_respects_device_region
crunch reserve_region
  for cap_refs_respects_device_region[wp]: cap_refs_respects_device_region

crunch reserve_region
  for invs[wp]: "invs"

crunch copy_global_mappings
  for iflive[wp]: "if_live_then_nonz_cap"
  (wp: crunch_wps)

crunch copy_global_mappings
  for zombies[wp]: "zombies_final"
  (wp: crunch_wps)

crunch copy_global_mappings
  for state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  (wp: crunch_wps)

crunch copy_global_mappings
  for valid_idle[wp]: "valid_idle"
  (wp: crunch_wps)

crunch copy_global_mappings
  for only_idle[wp]: "only_idle"
  (wp: crunch_wps)

crunch copy_global_mappings
  for ifunsafe[wp]: "if_unsafe_then_cap"
  (wp: crunch_wps)

crunch copy_global_mappings
  for reply_caps[wp]: "valid_reply_caps"
  (wp: crunch_wps)

crunch copy_global_mappings
  for reply_masters[wp]: "valid_reply_masters"
  (wp: crunch_wps)

crunch copy_global_mappings
  for valid_global[wp]: "valid_global_refs"
  (wp: crunch_wps)

crunch copy_global_mappings
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

crunch copy_global_mappings
  for irq_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

crunch copy_global_mappings
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps)

crunch copy_global_mappings
  for pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  (wp: crunch_wps)

crunch copy_global_mappings
  for cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
  (wp: crunch_wps)

crunch copy_global_mappings
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  (wp: crunch_wps)

crunch copy_global_mappings
  for cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
  (wp: crunch_wps)


lemma glob_vs_refs_add_one':
  "glob_vs_refs (ArchObj (PageDirectory (pd(p := pde)))) =
   glob_vs_refs (ArchObj (PageDirectory pd))
   - Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref (pd p))
   \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref pde)"
  apply (simp add: glob_vs_refs_def)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp del: disjCI dest!: graph_ofD split: if_split_asm)
   apply (rule disjI1)
   apply (rule conjI)
    apply (rule_tac x="(aa, ba)" in image_eqI)
     apply simp
    apply (simp add:  graph_of_def)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp dest!: graph_ofD)
   apply (rule_tac x="(aa,ba)" in image_eqI)
    apply simp
   apply (clarsimp simp: graph_of_def)
  apply clarsimp
  apply (rule_tac x="(p,x)" in image_eqI)
   apply simp
  apply (clarsimp simp: graph_of_def)
  done


lemma store_pde_map_global_valid_arch_caps:
  "\<lbrace>valid_arch_caps and valid_objs and valid_vspace_objs
     and valid_arch_state
     and K (valid_pde_mappings pde)
     and K (VSRef (p && mask pd_bits >> 3) (Some APageDirectory)
                \<in> kernel_vsrefs)
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p
             \<longrightarrow> p \<in> {})\<rbrace>
      store_pde p pde
   \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  apply (simp add: kernel_vsrefs_def)
  done


lemma store_pde_map_global_valid_vspace_objs:
  "\<lbrace>valid_vspace_objs and valid_arch_state
     and K (VSRef (p && mask pd_bits >> 3) (Some APageDirectory)
                \<in> kernel_vsrefs)\<rbrace>
        store_pde p pde
   \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (simp add: kernel_vsrefs_def)
  done


lemma store_pde_valid_kernel_mappings_map_global:
  "\<lbrace>valid_kernel_mappings and valid_arch_state
     and K (VSRef (p && mask pd_bits >> 2) (Some APageDirectory)
                \<in> kernel_vsrefs)
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p
             \<longrightarrow> p \<in> {})\<rbrace>
     store_pde p pde
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: kernel_vsrefs_def)
  done


crunch store_pde
  for valid_asid_map[wp]: "valid_asid_map"

crunch store_pde
  for cur[wp]: "cur_tcb"

lemma mapM_x_store_pde_eq_kernel_mappings_restr:
  "pd \<in> S \<and> is_aligned pd pd_bits \<and> is_aligned pd' pd_bits
        \<and> set xs \<subseteq> {..< 2 ^ (pd_bits - 3)}
     \<Longrightarrow>
   \<lbrace>\<lambda>s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>)\<rbrace>
     mapM_x (\<lambda>idx. get_pde (pd' + (idx << 3)) >>=
                   store_pde (pd + (idx << 3))) xs
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>)
               \<and> (\<forall>x \<in> set xs.
                    (\<exists>pdv pdv'. ko_at (ArchObj (PageDirectory pdv)) pd s
                      \<and> ko_at (ArchObj (PageDirectory pdv')) pd' s
                      \<and> pdv (ucast x) = pdv' (ucast x)))\<rbrace>"
  apply (induct xs rule: rev_induct, simp_all add: mapM_x_Nil mapM_x_append mapM_x_singleton)
  apply (erule bind_wp_fwd)
  apply (simp add: store_pde_def set_pd_def set_object_def cong: bind_cong)
  apply (wp get_object_wp get_pde_wp)
  apply (clarsimp simp: obj_at_def split del: if_split)
  apply (frule shiftl_less_t2n)
   apply (simp add: vspace_bits_defs)
  apply (simp add: is_aligned_add_helper split del: if_split)
  apply (cut_tac x=x and n=3 in shiftl_shiftr_id)
    apply (simp add: word_bits_def)
   apply (simp add: word_bits_def vspace_bits_defs)
   apply (erule order_less_le_trans, simp)
  apply (clarsimp simp: fun_upd_def[symmetric] is_aligned_add_helper vspace_bits_defs)
  done


lemma copy_global_equal_kernel_mappings_restricted:
  "is_aligned pd pd_bits \<Longrightarrow>
   \<lbrace>\<lambda>s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- (insert pd S)) \<rparr>)
              \<and> pspace_aligned s \<and> valid_arch_state s\<rbrace>
     copy_global_mappings pd
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>)\<rbrace>"
  apply (simp add: copy_global_mappings_def equal_kernel_mappings_def, wp)
  done

lemma store_pde_valid_ioc[wp]:
 "\<lbrace>valid_ioc\<rbrace> store_pde ptr pde \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (simp add: store_pde_def, wp) simp


lemma store_pde_vms[wp]:
 "\<lbrace>valid_machine_state\<rbrace> store_pde ptr pde \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (simp add: store_pde_def, wp) clarsimp

crunch store_pde
  for valid_irq_states[wp]: "valid_irq_states"

lemma copy_global_invs_mappings_restricted:
  "\<lbrace>(\<lambda>s. all_invs_but_equal_kernel_mappings_restricted (insert pd S) s)
          and (\<lambda>s. insert pd S \<inter> global_refs s = {})
          and K (is_aligned pd pd_bits)\<rbrace>
     copy_global_mappings pd
   \<lbrace>\<lambda>rv. all_invs_but_equal_kernel_mappings_restricted S\<rbrace>"
  apply (simp add: copy_global_mappings_def equal_kernel_mappings_def, wp, auto)
  done

lemma copy_global_mappings_valid_ioc[wp]:
 "\<lbrace>valid_ioc\<rbrace> copy_global_mappings pd \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (simp add: copy_global_mappings_def)

lemma copy_global_mappings_vms[wp]:
 "\<lbrace>valid_machine_state\<rbrace> copy_global_mappings pd \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (simp add: copy_global_mappings_def)

lemma copy_global_mappings_invs:
  "\<lbrace>invs and (\<lambda>s. pd \<notin> global_refs s)
         and K (is_aligned pd pd_bits)\<rbrace>
     copy_global_mappings pd \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (fold all_invs_but_equal_kernel_mappings_restricted_eq)
  apply (rule hoare_pre, rule copy_global_invs_mappings_restricted)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def
                        restrict_map_def)
  done

crunch copy_global_mappings
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)

lemma mapM_copy_global_invs_mappings_restricted:
  "\<lbrace>\<lambda>s. all_invs_but_equal_kernel_mappings_restricted (set pds) s
            \<and> (set pds \<inter> global_refs s = {})
            \<and> (\<forall>pd \<in> set pds. is_aligned pd pd_bits)\<rbrace>
     mapM_x copy_global_mappings pds
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (fold all_invs_but_equal_kernel_mappings_restricted_eq)
  apply (induct pds, simp_all only: mapM_x_Nil mapM_x_Cons K_bind_def)
   apply (wp, simp)
  apply (rule bind_wp, assumption, thin_tac "P" for P)
  apply (rule hoare_conjI)
   apply (rule hoare_pre, rule copy_global_invs_mappings_restricted)
   apply clarsimp
  apply (rule hoare_pre, wp)
  apply clarsimp
  done


lemma dmo_eq_kernel_restricted [wp, Retype_AI_assms]:
  "\<lbrace>\<lambda>s. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>
       do_machine_op m
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (simp add: equal_kernel_mappings_def obj_at_def)
  done


definition
  "post_retype_invs_check tp \<equiv> tp = ArchObject PageDirectoryObj"

declare post_retype_invs_check_def[simp]

end

arch_requalify_consts post_retype_invs_check

definition
  post_retype_invs :: "apiobject_type \<Rightarrow> word32 list \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "post_retype_invs tp refs \<equiv>
      if post_retype_invs_check tp
        then all_invs_but_equal_kernel_mappings_restricted (set refs)
        else invs"

global_interpretation Retype_AI_post_retype_invs?: Retype_AI_post_retype_invs
  where post_retype_invs_check = post_retype_invs_check
    and post_retype_invs = post_retype_invs
  by (unfold_locales; fact post_retype_invs_def)


context Arch begin arch_global_naming

lemma dmo_mapM_x_ccr_invs[wp]:
  "\<lbrace>invs\<rbrace>
   do_machine_op (mapM_x (\<lambda>ptr. cleanCacheRange_PoU ptr (w ptr) (addrFromPPtr ptr)) xs)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: mapM_x_mapM do_machine_op_return_foo)
  apply (rule hoare_pre)
  apply (subst dom_mapM)
    apply ((simp add:clearMemory_def
      | wp empty_fail_cleanCacheRange_PoU ef_storeWord
      empty_fail_mapM_x empty_fail_bind)+)[1]
   apply (wp mapM_wp' | clarsimp)+
  done


lemma init_arch_objects_invs_from_restricted:
  "\<lbrace>post_retype_invs new_type refs
         and (\<lambda>s. global_refs s \<inter> set refs = {})
         and K (\<forall>ref \<in> set refs. is_aligned ref (obj_bits_api new_type obj_sz))\<rbrace>
     init_arch_objects new_type dev ptr bits obj_sz refs
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: init_arch_objects_def split del: if_split)
  apply (wpsimp wp: mapM_copy_global_invs_mappings_restricted dmo_invs_lift
                    mapM_x_wp'[where f="\<lambda>r. do_machine_op (m r)" for m])
  apply (auto simp: post_retype_invs_def default_arch_object_def
                    pd_bits_def pageBits_def obj_bits_api_def
                    global_refs_def)
  done


lemma obj_bits_api_neq_0 [Retype_AI_assms]:
  "ty \<noteq> Untyped \<Longrightarrow> 0 < obj_bits_api ty us"
  unfolding obj_bits_api_def
  by (clarsimp simp: slot_bits_def default_arch_object_def vspace_bits_defs vcpu_bits_def
               split: Structures_A.apiobject_type.splits aobject_type.splits)


lemma vs_lookup_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup s \<subseteq> vs_lookup s'"
  unfolding vs_lookup_def
  apply (rule Image_mono)
   apply (rule vs_lookup_trans_sub2)
   apply (erule (1) ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
  done


lemma vs_lookup_pages_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs_pages ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup_pages s \<subseteq> vs_lookup_pages s'"
  unfolding vs_lookup_pages_def
  apply (rule Image_mono)
   apply (rule vs_lookup_pages_trans_sub2)
   apply (erule (1) ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
  done

end


global_interpretation Retype_AI_slot_bits?: Retype_AI_slot_bits
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; fact Retype_AI_assms)
  qed


context Arch begin arch_global_naming

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
           (s\<lparr>kheap := \<lambda>x. if x \<in> set (retype_addrs ptr ty n us) then Some (default_object ty dev us (cur_domain s)) else kheap s x\<rparr>)"
  (is "valid_cap c ?ns")
  proof -
  have obj_at_pres: "\<And>P x. obj_at P x s \<Longrightarrow> obj_at P x ?ns"
  by (clarsimp simp: obj_at_def dest: domI)
   (erule pspace_no_overlapC [OF pn _ _ cover vp])
  note blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff
  have cover':"range_cover ptr sz (obj_bits (default_object ty dev us (cur_domain s))) n"
    using cover tyunt
    by (clarsimp simp:obj_bits_dev_irr)

  show ?thesis
  using cover valid_c range usable_range_emptyD[where cap = c] cte_at
  apply (clarsimp simp: valid_cap_def elim!: obj_at_pres
                 split: cap.splits option.splits arch_cap.splits)
      defer
     apply (fastforce elim!: obj_at_pres)
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
  have cover':"range_cover ptr sz (obj_bits (default_object ty dev us (cur_domain s))) n"
    using cover tyunt
    by (clarsimp simp: obj_bits_dev_irr)
  show ?thesis
  using cap
  apply (case_tac cap)
    unfolding valid_cap_def
             apply (simp_all add: valid_cap_def obj_at_pres cte_at_pres
                           split: option.split_asm arch_cap.split_asm option.splits)
     apply (clarsimp simp add: valid_untyped_def ps_def s'_def)
     apply (intro conjI)
      apply clarsimp
      apply (drule disjoint_subset [OF retype_addrs_obj_range_subset [OF _ cover' tyunt]])
       apply (simp add: Int_ac p_assoc_help[symmetric])
      apply fastforce
     apply clarsimp
     apply (drule disjoint_subset [OF retype_addrs_obj_range_subset [OF _ cover' tyunt]])
      apply (simp add: Int_ac p_assoc_help[symmetric])
     apply fastforce
    using cover tyunt
    apply (simp add: obj_bits_api_def2 split: Structures_A.apiobject_type.splits)
        apply (fastforce elim!: obj_at_pres)+
  done
  qed

lemma valid_global_refs:
  "valid_global_refs s \<Longrightarrow> valid_global_refs s'"
  apply (simp add: valid_global_refs_def valid_refs_def global_refs_def idle_s')
  apply (simp add: cte_retype cap_range_def)
  done

lemma valid_cur_fpu':
  "valid_cur_fpu s \<Longrightarrow> valid_cur_fpu s'"
  by (clarsimp simp: valid_cur_fpu_def)

lemma valid_arch_state:
  "valid_arch_state s \<Longrightarrow> valid_arch_state s'"
  by (clarsimp simp: valid_arch_state_def obj_at_pres
                     valid_asid_table_def split: option.split)

lemma vs_refs_default [simp]:
  "vs_refs (default_object ty dev us d) = {}"
  by (simp add: default_object_def default_arch_object_def tyunt vs_refs_def
                o_def pde_ref_def graph_of_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)

lemma vs_refs_pages_default [simp]:
  "vs_refs_pages (default_object ty dev us d) = {}"
  by (simp add: default_object_def default_arch_object_def tyunt vs_refs_pages_def
                o_def pde_ref_pages_def pte_ref_pages_def graph_of_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)

lemma vs_lookup':
  "vs_lookup s' = vs_lookup s"
  apply (rule order_antisym)
   apply (rule vs_lookup_sub2)
    apply (clarsimp simp: obj_at_def s'_def ps_def split: if_split_asm)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: obj_at_def s'_def ps_def split: if_split_asm dest!: orthr)
  apply simp
  done

lemma vs_lookup_pages':
  "vs_lookup_pages s' = vs_lookup_pages s"
  apply (rule order_antisym)
   apply (rule vs_lookup_pages_sub2)
    apply (clarsimp simp: obj_at_def s'_def ps_def split: if_split_asm)
   apply simp
  apply (rule vs_lookup_pages_sub)
   apply (clarsimp simp: obj_at_def s'_def ps_def split: if_split_asm dest!: orthr)
  apply simp
  done

(* ARMHYP move *)
lemma hyp_refs_eq:
  "ARM_HYP.state_hyp_refs_of s' = ARM_HYP.state_hyp_refs_of s"
  unfolding s'_def ps_def
  apply (rule ext)
  apply (clarsimp simp: state_hyp_refs_of_def orthr split: option.splits)
  apply (cases ty; simp add: tyunt default_object_def default_tcb_def hyp_refs_of_def tcb_hyp_refs_def
                                 default_arch_tcb_def)
  apply (rename_tac ao)
  apply (clarsimp simp: refs_of_a_def ARM_HYP.vcpu_tcb_refs_def default_arch_object_def
                        ARM_HYP_A.default_vcpu_def
                  split: aobject_type.splits)
  done

lemma wellformed_default_obj[Retype_AI_assms]:
   "\<lbrakk> ptra \<notin> set (retype_addrs ptr ty n us);
        kheap s ptra = Some (ArchObj x5); arch_valid_obj x5 s\<rbrakk> \<Longrightarrow>
          arch_valid_obj x5 s'"
  apply (clarsimp simp: arch_valid_obj_def valid_vcpu_def
                  elim!:obj_at_pres
                  split: arch_kernel_obj.splits option.splits)
  done

end


context retype_region_proofs_arch begin

lemma obj_at_valid_pte:
  "\<lbrakk>valid_pte pte s; \<And>P p. obj_at P p s \<Longrightarrow> obj_at P p s'\<rbrakk>
   \<Longrightarrow> valid_pte pte s'"
  apply (cases pte, simp_all add: valid_pte_def data_at_def)
  apply (clarsimp | elim disjE)+
  done

lemma obj_at_valid_pde:
  "\<lbrakk>valid_pde pde s; \<And>P p. obj_at P p s \<Longrightarrow> obj_at P p s'\<rbrakk>
   \<Longrightarrow> valid_pde pde s'"
  apply (cases pde, simp_all add: valid_pte_def data_at_def)
  apply (clarsimp | elim disjE)+
  done


end


context retype_region_proofs begin

interpretation retype_region_proofs_arch ..

lemma valid_vspace_objs':
  assumes va: "valid_vspace_objs s"
  shows "valid_vspace_objs s'"
proof
  fix p ao
  assume p: "(\<exists>\<rhd> p) s'"
  assume "ko_at (ArchObj ao) p s'"
  hence "ko_at (ArchObj ao) p s \<or> ArchObj ao = default_object ty dev us (cur_domain s)"
    by (simp add: ps_def obj_at_def s'_def split: if_split_asm)
  moreover
  { assume "ArchObj ao = default_object ty dev us (cur_domain s)" with tyunt
    have "valid_vspace_obj ao s'" by (rule valid_vspace_obj_default)
  }
  moreover
  { assume "ko_at (ArchObj ao) p s"
    with va p
    have "valid_vspace_obj ao s"
      by (auto simp: vs_lookup' elim: valid_vspace_objsD)
    hence "valid_vspace_obj ao s'"
      apply (cases ao, simp_all add: obj_at_pres)
       apply (erule allEI)
       apply (erule (1) obj_at_valid_pte[OF _ obj_at_pres])
      apply (erule allEI)
      apply (erule (1) obj_at_valid_pde[OF _ obj_at_pres])
      done
  }
  ultimately
  show "valid_vspace_obj ao s'" by blast
qed


sublocale retype_region_proofs_gen?: retype_region_proofs_gen
  by (unfold_locales,
        auto simp: hyp_refs_eq[simplified s'_def ps_def]
                  wellformed_default_obj[simplified s'_def ps_def]
                  valid_default_arch_tcb)

end


context Arch begin arch_global_naming

definition
  valid_vs_lookup2 :: "(vs_ref list \<times> word32) set \<Rightarrow> word32 set \<Rightarrow> (cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
 "valid_vs_lookup2 lookup S caps \<equiv>
    \<forall>p ref. (ref, p) \<in> lookup \<longrightarrow>
          ref \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None] \<and>
         (\<exists>p' cap. caps p' = Some cap \<and> p \<in> obj_refs cap \<and> vs_cap_ref cap = Some ref)"


lemma valid_vs_lookup_def2:
  "valid_vs_lookup s = valid_vs_lookup2
         (vs_lookup_pages s) {}
         (null_filter (caps_of_state s))"
  apply (simp add: valid_vs_lookup_def valid_vs_lookup2_def)
  apply (intro iff_allI imp_cong[OF refl] disj_cong[OF refl]
               iff_exI conj_cong[OF refl])
  apply (auto simp: null_filter_def)
  done


lemma unique_table_caps_null:
  "unique_table_caps (null_filter s)
       = unique_table_caps s"
  apply (simp add: unique_table_caps_def)
  apply (intro iff_allI)
  apply (clarsimp simp: null_filter_def)
  done


lemma unique_table_refs_null:
  "unique_table_refs (null_filter s)
       = unique_table_refs s"
  apply (simp only: unique_table_refs_def)
  apply (intro iff_allI)
  apply (clarsimp simp: null_filter_def)
  apply (auto dest!: obj_ref_none_no_asid[rule_format]
               simp: table_cap_ref_def)
  done


definition
  region_in_kernel_window :: "word32 set \<Rightarrow> 'z state \<Rightarrow> bool"
where
 "region_in_kernel_window S \<equiv>
     \<lambda>s. \<forall>x \<in> S. arm_kernel_vspace (arch_state s) x = ArmVSpaceKernelWindow"

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
  "\<lbrakk>ty \<noteq> Untyped;default_object ty dev us d = ArchObj (DataPage dev' sz)\<rbrakk> \<Longrightarrow> dev = dev'"
  by (clarsimp simp: default_object_def default_arch_object_def
              split: apiobject_type.split_asm aobject_type.split_asm)

end


lemma cap_range_respects_device_region_cong[cong]:
  "device_state (machine_state s) = device_state (machine_state s')
  \<Longrightarrow> cap_range_respects_device_region cap s = cap_range_respects_device_region cap s'"
  by (clarsimp simp: cap_range_respects_device_region_def)


arch_requalify_consts region_in_kernel_window

context retype_region_proofs_arch begin

lemmas unique_table_caps_eq
    = arg_cong[where f=unique_table_caps, OF null_filter,
               simplified unique_table_caps_null]

lemmas unique_table_refs_eq
    = arg_cong[where f=unique_table_refs, OF null_filter,
               simplified unique_table_refs_null]

lemma valid_table_caps:
  "valid_table_caps s \<Longrightarrow> valid_table_caps s'"
  apply (simp add: valid_table_caps_def
              del: imp_disjL)
  apply (elim allEI, intro impI, simp)
  apply (frule caps_retype[rotated])
   apply clarsimp
  apply (rule obj_at_pres)
  apply simp
  done

lemma valid_arch_caps:
  "valid_arch_caps s \<Longrightarrow> valid_arch_caps s'"
  by (clarsimp simp add: valid_arch_caps_def null_filter
                         valid_vs_lookup_def2 vs_lookup_pages'
                         unique_table_caps_eq
                         unique_table_refs_eq
                         valid_table_caps)

lemma valid_vspace_obj_pres:
  "valid_vspace_obj ao s \<Longrightarrow> valid_vspace_obj ao s'"
  apply (cases ao, simp_all)
    apply (simp add: obj_at_pres)
   apply (erule allEI)
   apply (erule (1) obj_at_valid_pte[OF _ obj_at_pres])
  apply (erule allEI)
  apply (erule (1) obj_at_valid_pde[OF _ obj_at_pres])
  done

lemma valid_kernel_mappings:
  "valid_kernel_mappings s \<Longrightarrow> valid_kernel_mappings s'"
  apply (simp add: valid_kernel_mappings_def s'_def
                   ball_ran_eq ps_def)
  done

lemma valid_asid_map:
  "valid_asid_map s \<Longrightarrow> valid_asid_map s'"
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: vspace_at_asid_def)
  apply (drule vs_lookup_2ConsD)
  apply clarsimp
  apply (erule vs_lookup_atE)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (drule obj_at_pres)
  apply (fastforce simp: vs_asid_refs_def graph_of_def
                  intro: vs_lookupI vs_lookup1I)
  done

lemma equal_kernel_mappings:
  "equal_kernel_mappings s \<Longrightarrow>
      if ty = ArchObject PageDirectoryObj
      then equal_kernel_mappings
           (s'\<lparr>kheap := kheap s' |` (- set (retype_addrs ptr ty n us))\<rparr>)
      else equal_kernel_mappings s'"
  apply (simp add: equal_kernel_mappings_def)
  done

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
      apply (drule retype_addrs_obj_range_subset[OF _ _ tyunt, where d'="cur_domain s"])
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
     apply (drule retype_addrs_obj_range_subset[OF _ _ tyunt, where d'="cur_domain s"])
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
  using equal_kernel_mappings
  by (clarsimp simp: invs_def post_retype_invs_def valid_state_def
                     unsafe_rep2 null_filter valid_idle
                     valid_reply_caps valid_reply_masters
                     valid_global_refs valid_arch_state valid_cur_fpu'
                     valid_irq_node_def obj_at_pres
                     valid_arch_caps valid_global_objs_def
                     valid_vspace_objs' valid_irq_handlers
                     valid_mdb_rep2 mdb_and_revokable
                     valid_pspace cur_tcb only_idle
                     valid_kernel_mappings valid_asid_map
                     valid_ioc vms valid_global_vspace_mappings_def
                     pspace_in_kernel_window
                     pspace_respects_device_region
                     cap_refs_respects_device_region
                     cap_refs_in_kernel_window valid_irq_states
               split: if_split_asm)

(* ML \<open>val pre_ctxt_1 = @{context}\<close> *)

sublocale retype_region_proofs_invs?: retype_region_proofs_invs
  where region_in_kernel_window = region_in_kernel_window
    and post_retype_invs_check = post_retype_invs_check
    and post_retype_invs = post_retype_invs
  using post_retype_invs valid_cap valid_global_refs valid_arch_state valid_vspace_objs'
  by unfold_locales (auto simp: s'_def ps_def)

(* local_setup \<open>note_new_facts pre_ctxt_1\<close> *)

lemmas post_retype_invs_axioms = retype_region_proofs_invs_axioms

end


context Arch begin arch_global_naming

named_theorems Retype_AI_assms'

lemma invs_post_retype_invs [Retype_AI_assms']:
  "invs s \<Longrightarrow> post_retype_invs ty refs s"
  apply (clarsimp simp: post_retype_invs_def invs_def valid_state_def)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def
                        restrict_map_def)
  done

lemmas equal_kernel_mappings_trans_state
  = more_update.equal_kernel_mappings_update

lemmas retype_region_proofs_assms [Retype_AI_assms']
  = retype_region_proofs.post_retype_invs_axioms

end


global_interpretation Retype_AI?: Retype_AI
  where no_gs_types = ARM_HYP.no_gs_types
    and post_retype_invs_check = post_retype_invs_check
    and post_retype_invs = post_retype_invs
    and region_in_kernel_window = region_in_kernel_window
  proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact Retype_AI_assms)?)
     (simp add: Retype_AI_axioms_def Retype_AI_assms')
  qed


context Arch begin arch_global_naming

lemma retype_region_plain_invs:
  "\<lbrace>invs and caps_no_overlap ptr sz and pspace_no_overlap_range_cover ptr sz
      and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
      and region_in_kernel_window {ptr .. (ptr &&~~ mask sz) + 2 ^ sz - 1}
      and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
      and K (ty = Structures_A.CapTableObject \<longrightarrow> 0 < us)
      and K (range_cover ptr sz (obj_bits_api ty us) n)
      and K (ty \<noteq> ArchObject PageDirectoryObj)\<rbrace>
      retype_region ptr n us ty dev \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post[OF retype_region_post_retype_invs])
  apply (simp add: post_retype_invs_def)
  done


lemma storeWord_um_eq_0:
  "\<lbrace>\<lambda>m. underlying_memory m p = 0\<rbrace>
    storeWord x 0
   \<lbrace>\<lambda>_ m. underlying_memory m p = 0\<rbrace>"
  by (simp add: storeWord_def word_rsplit_0 word_bits_conv | wp)+


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


lemma cleanCacheRange_PoU_um_inv[wp]:
  "\<lbrace>\<lambda>m. P (underlying_memory m)\<rbrace>
    cleanCacheRange_PoU ptr w p
   \<lbrace>\<lambda>_ m. P (underlying_memory m)\<rbrace>"
  by (simp add: cleanCacheRange_PoU_def cleanByVA_PoU_def machine_op_lift_def machine_rest_lift_def
                split_def | wp)+

lemma invs_irq_state_independent:
  "invs (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = invs s"
  apply (clarsimp simp: irq_state_independent_A_def invs_def
      valid_state_def valid_pspace_def valid_mdb_def valid_ioc_def valid_idle_def
      only_idle_def if_unsafe_then_cap_def valid_reply_caps_def
      valid_reply_masters_def valid_global_refs_def valid_arch_state_def
      valid_irq_node_def valid_irq_handlers_def valid_machine_state_def
      valid_vspace_objs_def valid_arch_caps_def
      valid_kernel_mappings_def equal_kernel_mappings_def
      valid_asid_map_def vspace_at_asid_def
      pspace_in_kernel_window_def cap_refs_in_kernel_window_def
      cur_tcb_def sym_refs_def state_refs_of_def state_hyp_refs_of_def
      swp_def valid_irq_states_def split: option.split)
  done

crunch cleanByVA, cleanCacheRange_PoC, dsb, cleanCacheRange_PoC, cleanL2Range, cleanByVA_PoU,
  storeWord, clearMemory
  for irq_masks_inv[wp]: "\<lambda>s. P (irq_masks s)"
  (wp: crunch_wps
   ignore_del: cleanByVA_PoU storeWord clearMemory cleanL2Range cleanCacheRange_PoC dsb cleanByVA)

crunch clearMemory
  for underlying_mem_0[wp]: "\<lambda>s. underlying_memory s p = 0"
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

crunch init_arch_objects
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

lemma init_arch_objects_excap:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace>
      init_arch_objects tp dev ptr bits us refs
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to P p s\<rbrace>"
  by (wp ex_cte_cap_to_pres)

crunch init_arch_objects
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"
  (wp: crunch_wps)

lemma valid_arch_mdb_detype:
  "valid_arch_mdb (is_original_cap s) (caps_of_state s) \<Longrightarrow>
            valid_arch_mdb (is_original_cap (detype (untyped_range cap) s))
         (\<lambda>p. if fst p \<in> untyped_range cap then None else caps_of_state s p)"
  by auto

lemmas init_arch_objects_wps
    = init_arch_objects_cte_wp_at
      init_arch_objects_valid_cap
      init_arch_objects_cap_table
      init_arch_objects_excap
      init_arch_objects_pred_tcb_at

end

end
