(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchRetype_AC
imports Retype_AC
begin


lemma invs_mdb_cte':
  "invs s \<Longrightarrow> mdb_cte_at (\<lambda>p. \<exists>c. caps_of_state s p = Some c \<and> NullCap \<noteq> c) (cdt s)"
  by (drule invs_mdb) (simp add: valid_mdb_def2)


context retype_region_proofs begin interpretation Arch .

lemma vs_refs_no_global_pts_default[simp]:
  "vs_refs_no_global_pts (default_object ty dev us) = {}"
  by (simp add: default_object_def default_arch_object_def tyunt
                vs_refs_no_global_pts_def pde_ref2_def pte_ref_def
                o_def
         split: apiobject_type.splits aobject_type.splits)

lemma vrefs_eq: "state_vrefs s' = state_vrefs s"
  apply (rule ext)
  apply (simp add: s'_def state_vrefs_def ps_def orthr split: option.split)
  done

end


context retype_region_proofs' begin interpretation Arch .

lemma pas_refined:
  "\<lbrakk> invs s; pas_refined aag s \<rbrakk> \<Longrightarrow> pas_refined aag s'"
  apply (erule pas_refined_state_objs_to_policy_subset)
     apply (simp add: state_objs_to_policy_def refs_eq vrefs_eq mdb_and_revokable)
     apply (rule subsetI, rename_tac x, case_tac x, simp)
     apply (erule state_bits_to_policy.cases)
            apply (solves \<open>auto intro!: sbta_caps intro: caps_retype split: cap.split\<close>)
           apply (solves \<open>auto intro!: sbta_untyped intro: caps_retype split: cap.split\<close>)
          apply (blast intro: state_bits_to_policy.intros)
         apply (blast intro: state_bits_to_policy.intros)
        apply (force intro!: sbta_cdt
                       dest: caps_of_state_pres invs_mdb_cte'[THEN mdb_cte_atD[rotated]])
       apply (force intro!: sbta_cdt_transferable
                      dest: caps_of_state_pres invs_mdb_cte'[THEN mdb_cte_atD[rotated]])
      apply (simp add: vrefs_eq)
      apply (blast intro: state_bits_to_policy.intros)
     apply (simp add: vrefs_eq)
     apply (force elim!: state_asids_to_policy_aux.cases
                 intro: state_asids_to_policy_aux.intros caps_retype
                 split: cap.split
                 dest: sata_asid[OF caps_retype, rotated])
    apply clarsimp
    apply (erule state_irqs_to_policy_aux.cases)
    apply (solves\<open>auto intro!: sita_controlled intro: caps_retype split: cap.split\<close>)
   apply (rule domains_of_state)
  apply simp
  done

end


context Arch begin global_naming ARM_A

named_theorems Retype_AC_assms

declare retype_region_proofs.vrefs_eq[Retype_AC_assms]
declare retype_region_proofs'.pas_refined[Retype_AC_assms]

crunch set_pd
  for integrity_autarch: "integrity aag X st"
  (wp: crunch_wps simp: crunch_simps)

lemma store_pde_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag (p && ~~ mask pd_bits))\<rbrace>
   store_pde p pde
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp: store_pde_def wp: set_pd_integrity_autarch)

(* Borrowed from part of copy_global_mappings_nonempty_table in Untyped_R.thy *)
lemma copy_global_mappings_index_subset:
  "set [kernel_base >> 20.e.2 ^ (pd_bits - 2) - 1] \<subseteq> {x. \<exists>y. x = y >> 20}"
  apply clarsimp
  apply (rule_tac x="x << 20" in exI)
  apply (subst shiftl_shiftr1, simp)
  apply (simp add: word_size)
  apply (rule sym, rule less_mask_eq)
  apply (simp add: word_leq_minus_one_le pd_bits_def pageBits_def)
  done

lemma copy_global_mappings_integrity:
  "is_aligned x pd_bits
   \<Longrightarrow> \<lbrace>integrity aag X st and K (is_subject aag x)\<rbrace>
       copy_global_mappings x
       \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copy_global_mappings_def)
  apply (wp mapM_x_wp[OF _ subset_refl] store_pde_respects)+
    apply (drule subsetD[OF copy_global_mappings_index_subset])
    apply (fastforce simp: pd_shifting')
   apply wpsimp+
  done

lemma state_vrefs_detype[Retype_AC_assms, dest]:
  "x \<in> state_vrefs (detype R s) p \<Longrightarrow> x \<in> state_vrefs s p"
  unfolding state_vrefs_def
  by (clarsimp simp: detype_def split: if_splits)

lemma sata_detype[Retype_AC_assms]:
  "state_asids_to_policy aag (detype R s) \<subseteq> state_asids_to_policy aag s"
  apply (clarsimp)
  apply (erule state_asids_to_policy_aux.induct)
  apply (auto intro: state_asids_to_policy_aux.intros split: if_split_asm)
  done

lemma word_size_bits_untyped_min_bits[Retype_AC_assms]: "word_size_bits \<le> untyped_min_bits"
  by (simp add: word_size_bits_def untyped_min_bits_def)

lemma word_size_bits_resetChunkBits[Retype_AC_assms]: "word_size_bits \<le> resetChunkBits"
  by (simp add: word_size_bits_def Kernel_Config.resetChunkBits_def)

lemma clas_default_cap[Retype_AC_assms]:
  "tp \<noteq> ArchObject ASIDPoolObj \<Longrightarrow> cap_links_asid_slot aag p (default_cap tp p' sz dev)"
  unfolding cap_links_asid_slot_def
  apply (cases tp, simp_all)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type, simp_all add: arch_default_cap_def)
  done

lemma cli_default_cap[Retype_AC_assms]:
  "tp \<noteq> ArchObject ASIDPoolObj \<Longrightarrow> cap_links_irq aag p (default_cap tp p' sz dev)"
  unfolding cap_links_irq_def
  apply (cases tp, simp_all)
  done

lemma aobj_refs'_default'[Retype_AC_assms]:
  "is_aligned oref (obj_bits_api (ArchObject tp) sz)
   \<Longrightarrow> aobj_ref' (arch_default_cap tp oref sz dev) \<subseteq> ptr_range oref (obj_bits_api (ArchObject tp) sz)"
  by (cases tp; simp add: arch_default_cap_def ptr_range_memI obj_bits_api_def default_arch_object_def)

lemma pd_shifting_dual':
  "is_aligned (pd::word32) pd_bits
   \<Longrightarrow> pd + (vptr >> 20 << 2) && mask pd_bits = vptr >> 20 << 2"
  apply (subst (asm) pd_bits_def)
  apply (subst (asm) pageBits_def)
  apply (simp add: pd_shifting_dual)
  done

lemma empty_table_update_from_arm_global_pts:
  "\<lbrakk>valid_global_objs s; kernel_base >> 20 \<le> y >> 20; y >> 20 \<le> 2 ^ (pd_bits - 2) - 1;
    is_aligned pd pd_bits; obj_at (empty_table (set (second_level_tables (arch_state s)))) pd s;
    kheap s (arm_global_pd (arch_state s)) = Some (ArchObj (PageDirectory pda)) \<rbrakk>
    \<Longrightarrow> (\<forall>pdb. ko_at (ArchObj (PageDirectory pdb)) pd s
               \<longrightarrow> empty_table (set (second_level_tables (arch_state s)))
                               (ArchObj (PageDirectory (pdb(ucast (y >> 20) := pda (ucast (y >> 20)))))))"
  by (clarsimp simp: obj_at_def valid_global_objs_def empty_table_def)

lemma copy_global_mappings_pas_refined:
  "is_aligned pd pd_bits
   \<Longrightarrow> \<lbrace>pas_refined aag and valid_kernel_mappings and valid_arch_state
                        and valid_global_objs and valid_global_refs and pspace_aligned\<rbrace>
       copy_global_mappings pd
       \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply wp
    (* Use \<circ> to avoid wp filtering out the global_pd condition here
       TODO: see if we can clean this up *)
    apply (rule_tac Q'="\<lambda>rv s. is_aligned global_pd pd_bits \<and>
                              (global_pd = (arm_global_pd \<circ> arch_state) s \<and>
                               valid_kernel_mappings s \<and> valid_arch_state s \<and>
                               valid_global_objs s \<and> valid_global_refs s \<and> pas_refined aag s)"
                 in hoare_strengthen_post)
     apply (rule mapM_x_wp[OF _ subset_refl])
     apply (rule bind_wp)
      apply (unfold o_def)
    (* Use [1] so wp doesn't filter out the global_pd condition *)
      apply (wp store_pde_pas_refined store_pde_valid_kernel_mappings_map_global)[1]
     apply (frule subsetD[OF copy_global_mappings_index_subset])
     apply (rule hoare_gen_asm[simplified K_def pred_conj_def conj_commute])
     apply (simp add: get_pde_def)
     apply (subst kernel_vsrefs_kernel_mapping_slots[symmetric])
     apply wp
     apply (clarsimp simp: get_pde_def pd_shifting' pd_shifting_dual' triple_shift_fun)
     apply (subst (asm) obj_at_def, erule exE, erule conjE)
     apply (rotate_tac -1, drule sym, simp)
     apply (frule (1) valid_kernel_mappingsD[folded obj_at_def])
     apply (clarsimp simp: kernel_mapping_slots_def shiftr_20_less pde_ref_def
                           global_refs_def empty_table_update_from_arm_global_pts)
    apply fastforce
   apply (rule gets_wp)
  apply (simp, blast intro: invs_aligned_pdD)
  done

lemma copy_global_invs_mappings_restricted':
  "pd \<in> S
   \<Longrightarrow> \<lbrace>all_invs_but_equal_kernel_mappings_restricted S and (\<lambda>s. S \<inter> global_refs s = {})
                                                        and K (is_aligned pd pd_bits)\<rbrace>
       copy_global_mappings pd
       \<lbrace>\<lambda>_. all_invs_but_equal_kernel_mappings_restricted S\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (rule copy_global_invs_mappings_restricted)
  apply (simp add: insert_absorb)
  done

lemma init_arch_objects_pas_refined[Retype_AC_assms]:
  "\<lbrace>pas_refined aag and post_retype_invs tp refs and (\<lambda>s. \<forall> x\<in>set refs. x \<notin> global_refs s)
                    and K (\<forall>ref \<in> set refs. is_aligned ref (obj_bits_api tp obj_sz))\<rbrace>
   init_arch_objects tp ptr bits obj_sz refs
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases tp)
       apply (simp_all add: init_arch_objects_def)
       apply (wp | simp)+
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type, simp_all)
        apply ((simp | wp)+)[5]
   apply wp
    apply (rule_tac Q'="\<lambda>rv. pas_refined aag and
                            all_invs_but_equal_kernel_mappings_restricted (set refs) and
                            (\<lambda>s. \<forall>x \<in> set refs. x \<notin> global_refs s)" in hoare_strengthen_post)
     apply (wp mapM_x_wp[OF _ subset_refl])
     apply ((wp copy_global_mappings_pas_refined copy_global_invs_mappings_restricted'
                copy_global_mappings_global_refs_inv copy_global_invs_mappings_restricted'
             | fastforce simp: obj_bits_api_def default_arch_object_def pd_bits_def pageBits_def)+)[2]
   apply (wp dmo_invs hoare_vcg_const_Ball_lift valid_irq_node_typ
         | fastforce simp: post_retype_invs_def)+
  done

lemma region_in_kernel_window_preserved:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "\<And>S. f \<lbrace>region_in_kernel_window S\<rbrace>"
  apply (clarsimp simp: valid_def region_in_kernel_window_def)
  apply (erule use_valid)
  apply (rule assms)
  apply simp
  done

(* proof clagged from Retype_AI.clearMemory_vms *)
lemma freeMemory_vms:
  "valid_machine_state s \<Longrightarrow>
   \<forall>x\<in>fst (freeMemory ptr bits (machine_state s)). valid_machine_state (s\<lparr>machine_state := snd x\<rparr>)"
  apply (clarsimp simp: valid_machine_state_def disj_commute[of "in_user_frame p s" for p s])
  apply (drule_tac x=p in spec, simp)
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = 0"
                in use_valid[where P=P and Q="\<lambda>_. P" for P], simp_all)
  apply (simp add: freeMemory_def machine_op_lift_def machine_rest_lift_def split_def)
  apply (wp hoare_drop_imps | simp | wp mapM_x_wp_inv)+
   apply (simp add: storeWord_def | wp)+
   apply (simp add: word_rsplit_0 word_bits_conv)+
  done

lemma dmo_freeMemory_vms:
  "do_machine_op (freeMemory ptr bits) \<lbrace>valid_machine_state\<rbrace>"
  apply (unfold do_machine_op_def)
  apply (wp modify_wp freeMemory_vms | simp add: split_def)+
  done

lemma freeMemory_valid_irq_states:
  "freeMemory ptr bits \<lbrace>\<lambda>ms. valid_irq_states (s\<lparr>machine_state := ms\<rparr>)\<rbrace>"
  unfolding freeMemory_def
  by (wp mapM_x_wp[OF _ subset_refl] storeWord_valid_irq_states)

crunch freeMemory
  for pspace_respects_device_region[wp]: "\<lambda>ms. P (device_state ms)"
  (wp: crunch_wps)

lemma dmo_freeMemory_invs[Retype_AC_assms]:
  "do_machine_op (freeMemory ptr bits) \<lbrace>invs\<rbrace>"
  apply (simp add: do_machine_op_def invs_def valid_state_def cur_tcb_def | wp | wpc)+
  apply (clarsimp)
  apply (frule_tac P1="(=) (device_state (machine_state s))"
                in use_valid[OF _ freeMemory_pspace_respects_device_region])
   apply simp
  apply simp
  apply (rule conjI)
   apply (erule use_valid[OF _ freeMemory_valid_irq_states], simp)
  apply (drule freeMemory_vms)
  apply auto
  done

crunch delete_objects
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"
  (ignore: do_machine_op freeMemory)

lemma init_arch_objects_pas_cur_domain[Retype_AC_assms, wp]:
  "init_arch_objects tp ptr n us refs \<lbrace>pas_cur_domain aag\<rbrace>"
  by wp

lemma retype_region_pas_cur_domain[Retype_AC_assms, wp]:
  "retype_region ptr n us tp dev \<lbrace>pas_cur_domain aag\<rbrace>"
  by wp

lemma reset_untyped_cap_pas_cur_domain[Retype_AC_assms, wp]:
  "reset_untyped_cap src_slot \<lbrace>pas_cur_domain aag\<rbrace>"
  by wp

lemma arch_data_to_obj_type_not_ASIDPoolObj[Retype_AC_assms, simp]:
  "arch_data_to_obj_type v \<noteq> Some ASIDPoolObj"
  by (clarsimp simp: arch_data_to_obj_type_def)

lemma data_to_nat_of_nat[Retype_AC_assms, simp]:
  "of_nat (data_to_nat x) = x"
  by simp

lemma nonzero_data_to_nat_simp[Retype_AC_assms]:
  "0 < data_to_nat x \<Longrightarrow> 0 < x"
  by (auto dest: word_of_nat_less)

lemma storeWord_integrity_autarch:
  "\<lbrace>\<lambda>ms. integrity aag X st (s\<lparr>machine_state := ms\<rparr>) \<and>
         (is_aligned p 2 \<longrightarrow> (\<forall>p' \<in> ptr_range p 2. is_subject aag p'))\<rbrace>
   storeWord p v
   \<lbrace>\<lambda>_ ms. integrity aag X st (s\<lparr>machine_state := ms\<rparr>)\<rbrace>"
  unfolding storeWord_def
  apply wp
  apply (auto simp: integrity_def is_aligned_mask [symmetric]
            intro!: trm_lrefl ptr_range_memI ptr_range_add_memI)
  done

(* TODO: proof has mainly been copied from dmo_clearMemory_respects *)
lemma dmo_freeMemory_respects[Retype_AC_assms]:
  "\<lbrace>integrity aag X st and K (is_aligned ptr bits \<and> bits < word_bits \<and> word_size_bits \<le> bits \<and>
                              (\<forall>p \<in> ptr_range ptr bits. is_subject aag p))\<rbrace>
   do_machine_op (freeMemory ptr bits)
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding do_machine_op_def freeMemory_def
  apply (simp add: split_def)
  apply wp
  apply clarsimp
  apply (erule use_valid)
   apply (wpsimp wp: mol_respects mapM_x_wp' storeWord_integrity_autarch)
   apply (clarsimp simp: word_size_def word_bits_def word_size_bits_def
                         upto_enum_step_shift_red[where us=2, simplified])
   apply (erule bspec)
   apply (erule set_mp [rotated])
   apply (rule ptr_range_subset)
      apply simp
     apply (simp add: is_aligned_mult_triv2 [where n = 2, simplified])
    apply assumption
   apply (erule word_less_power_trans_ofnat [where k = 2, simplified])
    apply assumption
   apply simp
  apply simp
  done

lemma storeWord_respects:
  "\<lbrace>\<lambda>ms. integrity aag X st (s\<lparr>machine_state := ms\<rparr>) \<and>
         (\<forall>p' \<in> ptr_range p word_size_bits. aag_has_auth_to aag Write p')\<rbrace>
   storeWord p v
   \<lbrace>\<lambda>_ ms. integrity aag X st (s\<lparr>machine_state := ms\<rparr>)\<rbrace>"
  unfolding storeWord_def word_size_bits_def
  apply wp
  apply (auto simp: integrity_def is_aligned_mask [symmetric]
            intro!: trm_write ptr_range_memI ptr_range_add_memI)
  done

lemma dmo_clearMemory_respects'[Retype_AC_assms]:
  "\<lbrace>integrity aag X st and
    K (is_aligned ptr bits \<and> bits < word_bits \<and> word_size_bits \<le> bits \<and>
       (\<forall>p \<in> ptr_range ptr bits. aag_has_auth_to aag Write p))\<rbrace>
   do_machine_op (clearMemory ptr (2 ^ bits))
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding do_machine_op_def clearMemory_def
  apply (simp add: split_def cleanCacheRange_PoU_def)
  apply wp
  apply clarsimp
  apply (erule use_valid)
   apply wp
    apply (simp add: cleanCacheRange_RAM_def cleanCacheRange_PoC_def cacheRangeOp_def cleanL2Range_def
                     cleanByVA_def split_def dsb_def)
    apply (wp mol_respects mapM_x_wp' storeWord_respects)+
   apply (simp add: word_size_bits_def)
   apply (clarsimp simp: word_size_def word_bits_def upto_enum_step_shift_red[where us=2, simplified])
   apply (erule bspec)
   apply (erule set_mp [rotated])
   apply (rule ptr_range_subset)
      apply simp
     apply (simp add: is_aligned_mult_triv2 [where n = 2, simplified])
    apply assumption
   apply (erule word_less_power_trans_ofnat [where k = 2, simplified])
    apply assumption
   apply simp
  apply simp
  done

lemma dmo_cacheRangeOp_lift:
  "(\<And>a b. do_machine_op (oper a b) \<lbrace>P\<rbrace>)
   \<Longrightarrow> do_machine_op (cacheRangeOp oper x y z) \<lbrace>P\<rbrace>"
  by (wpsimp wp: dmo_mapM_x_wp_inv simp: cacheRangeOp_def)

lemma dmo_cleanCacheRange_PoU_respects [wp]:
  "do_machine_op (cleanCacheRange_PoU vstart vend pstart) \<lbrace>integrity aag X st\<rbrace>"
  by (wpsimp wp: dmo_cacheRangeOp_lift simp: cleanCacheRange_PoU_def cleanByVA_PoU_def)

lemma dmo_mapM_x_cleanCacheRange_PoU_integrity:
  "do_machine_op (mapM_x (\<lambda>x. cleanCacheRange_PoU (f x) (g x) (h x)) refs) \<lbrace>integrity aag X st\<rbrace>"
  by (wp dmo_mapM_x_wp_inv)

lemma init_arch_objects_integrity[Retype_AC_assms]:
  "\<lbrace>integrity aag X st and K (\<forall>x\<in>set refs. is_subject aag x)
                       and K (\<forall>ref \<in> set refs. is_aligned ref (obj_bits_api new_type obj_sz))\<rbrace>
   init_arch_objects new_type ptr num_objects obj_sz refs
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (cases new_type; simp add: init_arch_objects_def split del: if_split)
  apply (wpsimp wp: mapM_x_wp[OF _ subset_refl] copy_global_mappings_integrity
                    dmo_mapM_x_cleanCacheRange_PoU_integrity
              simp: obj_bits_api_def default_arch_object_def pd_bits_def pageBits_def)
  done

lemma integrity_asids_detype[Retype_AC_assms]:
  assumes refs: "\<forall>r\<in>refs. pasObjectAbs aag r \<in> subjects"
  shows
    "integrity_asids aag subjects x a (detype refs s) s' =
     integrity_asids aag subjects x a s s'"
    "integrity_asids aag subjects x a s (detype refs s') =
     integrity_asids aag subjects x a s s'"
  by auto

lemma retype_region_integrity_asids[Retype_AC_assms]:
  "\<lbrakk> range_cover ptr sz (obj_bits_api typ o_bits) n; typ \<noteq> Untyped;
     \<forall>x\<in>up_aligned_area ptr sz. is_subject aag x; integrity_asids aag {pasSubject aag} x a s st \<rbrakk>
     \<Longrightarrow> integrity_asids aag {pasSubject aag} x a s
           (st\<lparr>kheap := \<lambda>a. if a \<in> (\<lambda>x. ptr_add ptr (x * 2 ^ obj_bits_api typ o_bits)) ` {0 ..< n}
                            then Some (default_object typ dev o_bits)
                            else kheap s a\<rparr>)"
  by clarsimp

end

global_interpretation Retype_AC_1?: Retype_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Retype_AC_assms | wpsimp))
qed


context begin interpretation Arch .

requalify_facts storeWord_respects

end

end
