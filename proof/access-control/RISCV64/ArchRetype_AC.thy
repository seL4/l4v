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

lemma state_vrefs_eq:
  "\<lbrakk> valid_vspace_objs s; valid_arch_state s \<rbrakk>
     \<Longrightarrow> state_vrefs s' = state_vrefs s"
  apply (insert dev vp)
  apply (intro ext subset_antisym subsetI)
   apply (clarsimp simp: state_vrefs_def)
   apply (frule vs_lookup_level)
   apply (simp add: vs_lookup_table')
   apply (prop_tac "kheap s x = kheap s' x")
    apply (clarsimp simp: s'_def ps_def split: if_splits)
    apply (case_tac "lvl > max_pt_level")
     apply (fastforce simp: valid_arch_state_def opt_map_def orthr
                      dest: vs_lookup_asid_pool
                     split: option.splits)
    apply (fastforce simp: valid_arch_state_def valid_pspace_def obj_at_def orthr
                    dest!: vs_lookup_table_pt_at )
   apply (fastforce simp: opt_map_def)
  apply (clarsimp simp: state_vrefs_def)
  apply (frule vs_lookup_level)
  apply (prop_tac "kheap s x = kheap s' x")
   apply (clarsimp simp: s'_def ps_def split: if_splits)
   apply (case_tac "lvl > max_pt_level")
    apply (fastforce simp: valid_arch_state_def opt_map_def orthr
                     dest: vs_lookup_asid_pool
                    split: option.splits)
   apply (fastforce simp: valid_arch_state_def valid_pspace_def obj_at_def orthr
                   dest!: vs_lookup_table_pt_at )
  apply (fastforce simp: opt_map_def vs_lookup_table'[symmetric])
  done

end


context retype_region_proofs' begin interpretation Arch .

lemma pas_refined:
  "\<lbrakk> invs s; pas_refined aag s \<rbrakk> \<Longrightarrow> pas_refined aag s'"
  apply (erule pas_refined_state_objs_to_policy_subset)
      apply (simp add: state_objs_to_policy_def refs_eq  mdb_and_revokable)
      apply (subst state_vrefs_eq; fastforce?)
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
      apply (blast intro: state_bits_to_policy.intros)
     apply (subst state_vrefs_eq; fastforce?)
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


context Arch begin global_naming RISCV64

named_theorems Retype_AC_assms

declare retype_region_proofs'.pas_refined[Retype_AC_assms]

lemma aobjs_of_detype[simp]:
  "(aobjs_of (detype S s) p = Some aobj) = (p \<notin> S \<and> aobjs_of s p = Some aobj)"
  by (simp add: in_omonad detype_def)

lemma pts_of_detype[simp]:
  "(pts_of (detype S s) p = Some pt) = (p \<notin> S \<and> pts_of s p = Some pt)"
  by (simp add: in_omonad detype_def)

lemma ptes_of_detype_Some[simp]:
  "(ptes_of (detype S s) p = Some pte) = (table_base p \<notin> S \<and> ptes_of s p = Some pte)"
  by (simp add: in_omonad ptes_of_def detype_def)

lemma asid_pools_of_detype:
  "asid_pools_of (detype S s) = (\<lambda>p. if p\<in>S then None else asid_pools_of s p)"
  by (rule ext) (simp add: detype_def opt_map_def)

lemma asid_pools_of_detype_Some[simp]:
  "(asid_pools_of (detype S s) p = Some ap) = (p \<notin> S \<and> asid_pools_of s p = Some ap)"
  by (simp add: in_omonad detype_def)

lemma pool_for_asid_detype_Some[simp]:
  "(pool_for_asid asid (detype S s) = Some p) = (pool_for_asid asid s = Some p)"
  by (simp add: pool_for_asid_def)

lemma vspace_for_pool_detype_Some[simp]:
  "(vspace_for_pool ap asid (\<lambda>p. if p \<in> S then None else pools p) = Some p) =
   (ap \<notin> S \<and> vspace_for_pool ap asid pools = Some p)"
  by (simp add: vspace_for_pool_def obind_def split: option.splits)

lemma vspace_for_asid_detype_Some[simp]:
  "(vspace_for_asid asid (detype S s) = Some p) =
   ((\<exists>ap. pool_for_asid asid s = Some ap \<and> ap \<notin> S) \<and> vspace_for_asid asid s = Some p)"
  apply (simp add: vspace_for_asid_def obind_def asid_pools_of_detype split: option.splits)
  apply (auto simp: pool_for_asid_def)
  done

lemma pt_walk_detype:
  "pt_walk level bot_level pt_ptr vref (ptes_of (detype S s)) = Some (bot_level, p) \<Longrightarrow>
   pt_walk level bot_level pt_ptr vref (ptes_of s) = Some (bot_level, p)"
  apply (induct level arbitrary: pt_ptr)
   apply (subst pt_walk.simps, simp)
  apply (subst pt_walk.simps)
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
  apply (drule meta_spec, drule (1) meta_mp)
  apply fastforce
  done

lemma vs_lookup_table:
  "vs_lookup_table level asid vref (detype S s) = Some (level, p) \<Longrightarrow>
   vs_lookup_table level asid vref s = Some (level, p)"
  apply (clarsimp simp: vs_lookup_table_def in_omonad obind_def asid_pools_of_detype
                 split: if_split_asm option.split_asm)
  apply (rule conjI)
   apply clarsimp
  apply (subst pt_walk_detype)
   apply simp
  apply simp
  done

lemma state_vrefs_detype[Retype_AC_assms, dest]:
  "x \<in> state_vrefs (detype R s) p \<Longrightarrow> x \<in> state_vrefs s p"
  apply (clarsimp simp: state_vrefs_def)
  apply (frule vs_lookup_level)
  apply (drule vs_lookup_table)
  apply fastforce
  done

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

crunch init_arch_objects
  for inv[wp]: P

lemma region_in_kernel_window_preserved:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "\<And>S. f \<lbrace>region_in_kernel_window S\<rbrace>"
  apply (clarsimp simp: valid_def region_in_kernel_window_def)
  apply (erule use_valid)
  apply (rule assms)
  apply fastforce
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
   apply (simp add: word_rsplit_0 upto.simps word_bits_def)
  apply simp
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
         (is_aligned p word_size_bits \<longrightarrow> (\<forall>p' \<in> ptr_range p word_size_bits. is_subject aag p'))\<rbrace>
   storeWord p v
   \<lbrace>\<lambda>_ ms. integrity aag X st (s\<lparr>machine_state := ms\<rparr>)\<rbrace>"
  unfolding storeWord_def
  apply wp
  by (auto simp: upto.simps integrity_def is_aligned_mask [symmetric] word_size_bits_def word_bits_def
            intro!: trm_lrefl ptr_range_memI ptr_range_add_memI)

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
   apply (clarsimp simp: word_size_def word_size_bits_def word_bits_def
                         upto_enum_step_shift_red[where us=3, simplified])
   apply (erule bspec)
   apply (erule set_mp [rotated])
   apply (rule ptr_range_subset)
      apply simp
     apply (simp add: is_aligned_mult_triv2 [where n = 3, simplified])
    apply assumption
   apply (erule word_less_power_trans_ofnat [where k = 3, simplified])
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
  by (auto simp: upto.simps integrity_def is_aligned_mask [symmetric] word_bits_def
            intro!: trm_write ptr_range_memI ptr_range_add_memI)

lemma dmo_clearMemory_respects'[Retype_AC_assms]:
  "\<lbrace>integrity aag X st and
    K (is_aligned ptr bits \<and> bits < word_bits \<and> word_size_bits \<le> bits \<and>
       (\<forall>p \<in> ptr_range ptr bits. aag_has_auth_to aag Write p))\<rbrace>
   do_machine_op (clearMemory ptr (2 ^ bits))
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding do_machine_op_def clearMemory_def
  apply (simp add: split_def )
  apply wp
  apply clarsimp
  apply (erule use_valid)
    apply (wp mol_respects mapM_x_wp' storeWord_respects)+
   apply (simp add: word_size_bits_def)
   apply (clarsimp simp: word_size_def word_bits_def upto_enum_step_shift_red[where us=3, simplified])
   apply (erule bspec)
   apply (erule set_mp [rotated])
   apply (rule ptr_range_subset)
      apply simp
     apply (simp add: is_aligned_mult_triv2 [where n = 3, simplified])
    apply assumption
   apply (erule word_less_power_trans_ofnat [where k = 3, simplified])
    apply assumption
   apply simp
  apply simp
  done

lemma integrity_asids_detype[Retype_AC_assms]:
  assumes refs: "\<forall>r\<in>refs. pasObjectAbs aag r \<in> subjects"
  shows
    "integrity_asids aag subjects x a (detype refs s) s' =
     integrity_asids aag subjects x a s s'"
    "integrity_asids aag subjects x a s (detype refs s') =
     integrity_asids aag subjects x a s s'"
  by (auto simp: detype_def refs opt_map_def)

lemma retype_region_integrity_asids[Retype_AC_assms]:
  "\<lbrakk> range_cover ptr sz (obj_bits_api typ o_bits) n; typ \<noteq> Untyped;
     \<forall>x\<in>up_aligned_area ptr sz. is_subject aag x; integrity_asids aag {pasSubject aag} x a s st \<rbrakk>
     \<Longrightarrow> integrity_asids aag {pasSubject aag} x a s
           (st\<lparr>kheap := \<lambda>a. if a \<in> (\<lambda>x. ptr_add ptr (x * 2 ^ obj_bits_api typ o_bits)) ` {0 ..< n}
                            then Some (default_object typ dev o_bits)
                            else kheap s a\<rparr>)"
  apply (clarsimp simp: opt_map_def)
  apply (case_tac "x \<in> up_aligned_area ptr sz"; clarsimp)
  apply (fastforce intro: tro_lrefl tre_lrefl
                    dest: retype_addrs_subset_ptr_bits[simplified retype_addrs_def]
                    simp: image_def p_assoc_help power_sub)
  done

end


global_interpretation Retype_AC_1?: Retype_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact Retype_AC_assms | wpsimp wp: init_arch_objects_inv)?)
qed

requalify_facts RISCV64.storeWord_respects

end
