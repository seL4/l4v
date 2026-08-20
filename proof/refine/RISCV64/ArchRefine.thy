(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Main abstract-to-design refinement theorem - architecture-specific proofs *)

theory ArchRefine
imports
  Refine
begin

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for Refine locale *)

text \<open>User memory content is the same on both levels\<close>
lemma typ_at_AUserDataI:
  "\<lbrakk> typ_at (AArch (AUserData sz)) p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s'; n < 2 ^ (pageBitsForSize sz - pageBits) \<rbrakk>
   \<Longrightarrow> typ_at' UserDataT (p + n * 2 ^ pageBits) s'"
  apply (clarsimp simp add: obj_at_def a_type_def)
  apply (simp split: Structures_A.kernel_object.split_asm
                     arch_kernel_obj.split_asm split: if_split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp)
  apply (drule_tac x = "p + n * 2 ^ pageBits" in spec)
  apply (drule_tac x = "\<lambda>_ obj. obj = KOUserData" in spec)
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def)
  apply (rule exI [where x = KOUserData])
  apply (drule mp)
   apply (rule exI [where x = n])
   apply (simp add: shiftl_t2n)
  apply (clarsimp simp: pspace_aligned'_def)
  apply (drule (1) bspec [OF _ domI])
  apply (clarsimp simp: objBits_simps)
  apply (fastforce  dest!: pspace_distinctD'  simp: objBits_simps)
  done

lemma typ_at_ADeviceDataI:
  "\<lbrakk> typ_at (AArch (ADeviceData sz)) p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s'; n < 2 ^ (pageBitsForSize sz - pageBits) \<rbrakk>
   \<Longrightarrow> typ_at' UserDataDeviceT (p + n * 2 ^ pageBits) s'"
  apply (clarsimp simp add: obj_at_def a_type_def )
  apply (simp split: Structures_A.kernel_object.split_asm
                     arch_kernel_obj.split_asm split: if_split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp)
  apply (drule_tac x = "p + n * 2 ^ pageBits" in spec)
  apply (drule_tac x = "\<lambda>_ obj. obj = KOUserDataDevice" in spec)
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def)
  apply (rule exI [where x = KOUserDataDevice])
  apply (drule mp)
   apply (rule exI [where x = n])
   apply (simp add: shiftl_t2n)
  apply (clarsimp simp: pspace_aligned'_def)
  apply (drule (1) bspec [OF _ domI])
  apply (clarsimp simp: objBits_simps)
  apply (fastforce  dest!: pspace_distinctD'  simp: objBits_simps)
  done

lemma typ_at_UserDataI:
  "\<lbrakk> typ_at' UserDataT (p && ~~ mask pageBits) s';
     pspace_relation (kheap s) (ksPSpace s'); pspace_aligned s \<rbrakk>
   \<Longrightarrow> \<exists>sz. typ_at (AArch (AUserData sz)) (p && ~~ mask (pageBitsForSize sz)) s"
  apply (clarsimp simp: exists_disj obj_at'_def typ_at'_def ko_wp_at'_def)
  apply (frule (1) in_related_pspace_dom)
  apply (clarsimp simp: pspace_dom_def)
  apply (clarsimp simp: pspace_relation_def dom_def)
  apply (erule allE, erule impE, blast)
  apply clarsimp
  apply (drule (1) bspec)
  apply clarsimp
  apply (subst mask_lower_twice [where n = pageBits, OF pbfs_atleast_pageBits, symmetric])
  apply (clarsimp simp: obj_relation_cuts_def2 pte_relation_def other_aobj_relation_def
                        cte_relation_def other_obj_relation_def tcb_relation_cut_def
              split: Structures_A.kernel_object.split_asm
                     Structures_H.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (rename_tac vmpage_size n)
  apply (rule_tac x = vmpage_size in exI)
  apply (subst conjunct2 [OF is_aligned_add_helper])
    apply (drule (1) pspace_alignedD)
    apply simp
   apply (simp add: shiftl_t2n mult_ac)
   apply (erule word_less_power_trans2 [OF _ pbfs_atleast_pageBits])
   apply (case_tac vmpage_size, simp_all add: word_bits_conv bit_simps)[1]
  apply (simp add: obj_at_def  a_type_def)
  done

lemma typ_at_DeviceDataI:
  "\<lbrakk> typ_at' UserDataDeviceT (p && ~~ mask pageBits) s';
     pspace_relation (kheap s) (ksPSpace s'); pspace_aligned s \<rbrakk>
   \<Longrightarrow> \<exists>sz. typ_at (AArch (ADeviceData sz)) (p && ~~ mask (pageBitsForSize sz)) s"
  apply (clarsimp simp: exists_disj obj_at'_def typ_at'_def ko_wp_at'_def)
  apply (frule (1) in_related_pspace_dom)
  apply (clarsimp simp: pspace_dom_def)
  apply (clarsimp simp: pspace_relation_def dom_def)
  apply (erule allE, erule impE, blast)
  apply clarsimp
  apply (drule (1) bspec)
  apply clarsimp
  apply (subst mask_lower_twice [where n = pageBits, OF pbfs_atleast_pageBits, symmetric])
  apply (clarsimp simp: obj_relation_cuts_def2 pte_relation_def other_aobj_relation_def
                        cte_relation_def other_obj_relation_def tcb_relation_cut_def
              split: Structures_A.kernel_object.split_asm
                     Structures_H.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (rename_tac vmpage_size n)
  apply (rule_tac x = vmpage_size in exI)
  apply (subst conjunct2 [OF is_aligned_add_helper])
    apply (drule (1) pspace_alignedD)
    apply simp
   apply (simp add: shiftl_t2n mult_ac)
   apply (erule word_less_power_trans2 [OF _ pbfs_atleast_pageBits])
   apply (case_tac vmpage_size, simp_all add: word_bits_conv bit_simps)[1]
  apply (simp add: obj_at_def  a_type_def)
  done

lemma and_mask_pbfs_shiftr_pageBits_limit:
  "p && mask (pageBitsForSize sz) >> pageBits < 2 ^ (pageBitsForSize sz - pageBits)" for p :: obj_ref
  apply (rule shiftr_less_t2n')
   apply (simp add: pbfs_atleast_pageBits mask_twice)
  apply (case_tac sz; simp add: bit_simps)
  done

lemma p_and_not_mask_pbfs_add_mask_pbfs_eq:
  "(p && ~~ mask (pageBitsForSize sz)) + (p && mask (pageBitsForSize sz) >> pageBits) * 2 ^ pageBits
   = p && ~~ mask pageBits"
  for p :: obj_ref
  by (simp flip: shiftl_t2n'
           add: shiftr_shiftl1 mask_out_add_aligned is_aligned_neg_mask pbfs_atleast_pageBits
                word_plus_and_or_coroll2 add.commute)

lemma pointerInUserData_relation[Arch_assms]:
  "\<lbrakk> (s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
   \<Longrightarrow> pointerInUserData p s' = in_user_frame p s"
  apply (simp add: pointerInUserData_def in_user_frame_def)
  apply (rule iffI)
   apply (erule typ_at_UserDataI; clarsimp simp: valid_state_def)
  apply clarsimp
  apply (drule_tac sz=sz and n="(p && mask (pageBitsForSize sz)) >> pageBits"
                in typ_at_AUserDataI [where s = s and s' = s'])
      apply (fastforce simp: valid_state'_def and_mask_pbfs_shiftr_pageBits_limit)+
  apply (erule arg_cong[where f="\<lambda>p. typ_at' _ p s'", THEN iffD1, rotated])
  apply (simp add: p_and_not_mask_pbfs_add_mask_pbfs_eq)
  done

lemma pointerInDeviceData_relation[Arch_assms]:
  "\<lbrakk> (s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
   \<Longrightarrow> pointerInDeviceData p s' = in_device_frame p s"
  apply (simp add: pointerInDeviceData_def in_device_frame_def)
  apply (rule iffI)
   apply (erule typ_at_DeviceDataI; clarsimp simp: valid_state_def)
  apply clarsimp
  apply (drule_tac sz=sz and n="(p && mask (pageBitsForSize sz)) >> pageBits"
               in typ_at_ADeviceDataI[where s=s and s'=s'])
      apply (fastforce simp: valid_state'_def and_mask_pbfs_shiftr_pageBits_limit)+
  apply (erule arg_cong[where f="\<lambda>p. typ_at' _ p s'", THEN iffD1, rotated])
  apply (simp add: p_and_not_mask_pbfs_add_mask_pbfs_eq)
  done

lemma user_mem_relation[Arch_assms]:
  "\<lbrakk>(s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
   \<Longrightarrow> user_mem' s' = user_mem s"
  by (rule ext)
     (clarsimp simp: user_mem_def user_mem'_def pointerInUserData_relation pointerInDeviceData_relation
                     state_relation_def)

lemma device_mem_relation[Arch_assms]:
  "\<lbrakk>(s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
   \<Longrightarrow> device_mem' s' = device_mem s"
  by (rule ext)
     (clarsimp simp: device_mem_def device_mem'_def pointerInUserData_relation
                     pointerInDeviceData_relation)

lemma arch_activate_thread_sched_act[Arch_assms]:
  "\<lbrace>ct_in_state activatable and (\<lambda>s. P (scheduler_action s))\<rbrace>
   arch_activate_idle_thread t
   \<lbrace>\<lambda>rs s. P (scheduler_action (s::det_state))\<rbrace>"
  by (wpsimp simp: arch_activate_idle_thread_def)

lemma valid_list_init[Arch_assms, simp]:
  "valid_list init_A_st"
  by (simp add: valid_list_2_def init_A_st_def ext_init_def init_cdt_def)

lemma valid_sched_init[Arch_assms, simp]:
  "valid_sched init_A_st"
  apply (simp add: valid_sched_def init_A_st_def ext_init_def)
  apply (clarsimp simp: init_kheap_def st_tcb_at_kh_def obj_at_kh_def
                    obj_at_def idle_thread_ptr_def
                    valid_queues_2_def ct_not_in_q_def not_queued_def
                    valid_sched_action_def is_activatable_def init_irq_node_ptr_def
                    init_global_pt_def riscv_global_pt_ptr_def
                    ct_in_cur_domain_2_def valid_blocked_2_def valid_idle_etcb_def
                    etcb_at'_def etcbs_of'_def)
  done

lemma valid_domain_list_init[Arch_assms, simp]:
  "valid_domain_list init_A_st"
  by (simp add: init_A_st_def ext_init_def valid_domain_list_def)

lemma valid_domain_time_init[Arch_assms, simp]:
  "0 < domain_time init_A_st"
  by (simp add: init_A_st_def)

lemma sched_act_init[Arch_assms, simp]:
  "scheduler_action init_A_st = resume_cur_thread"
  by (simp add: init_A_st_def)

(* nothing extra needed on this architecture *)
defs fastpathKernelAssertions_def:
  "fastpathKernelAssertions \<equiv> \<lambda>s. True"

lemma fastpathKernelAssertions_cross[Arch_assms]:
  "\<lbrakk> (s,s') \<in> state_relation; invs s; valid_arch_state' s'\<rbrakk> \<Longrightarrow> fastpathKernelAssertions s'"
  unfolding fastpathKernelAssertions_def
  by clarsimp

(* interface lemma, no vs duplicates on this architecture *)
lemma callKernel_valid_duplicates'[Arch_assms]:
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
    (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
    (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s)\<rbrace>
   callKernel e
   \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by wpsimp

(* interface lemma, no vs duplicates on this architecture *)
lemma doUserOp_valid_duplicates'[Arch_assms]:
  "doUserOp f tc \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by wpsimp

(* interface lemma, no vs duplicates on this architecture *)
lemma checkActiveIRQ_valid_duplicates'[Arch_assms]:
  "checkActiveIRQ \<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  by wpsimp

lemma tcb_hyp_refs'_atcbContextSet[Arch_assms, simp]:
  "tcb_hyp_refs' (atcbContextSet tc atcb) = tcb_hyp_refs' atcb"
  by (simp add: atcbContextSet_def)

lemma ptable_lift_abs_state[Arch_assms, simp]:
  "ptable_lift t (abs_state s) = ptable_lift t s"
  by (simp add: ptable_lift_def abs_state_def)

lemma ptable_rights_abs_state[Arch_assms, simp]:
  "ptable_rights t (abs_state s) = ptable_rights t s"
  by (simp add: ptable_rights_def abs_state_def)

lemma arch_tcb_relation_arch_context_set[Arch_assms]:
  "arch_tcb_relation atcb atcb'
   \<Longrightarrow> arch_tcb_relation (arch_tcb_context_set tc atcb) (atcbContextSet tc atcb')"
  by (simp add: arch_tcb_relation_def arch_tcb_context_set_def atcbContextSet_def)

lemma arch_tcb_relation_arch_context_get[Arch_assms]:
  "arch_tcb_relation atcb atcb' \<Longrightarrow> arch_tcb_context_get atcb = atcbContextGet atcb'"
  by (simp add: arch_tcb_relation_def arch_tcb_context_get_def atcbContextGet_def)

lemmas Refine_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

interpretation Refine?: Refine
proof goal_cases
  case 1 show ?case by (intro_locales; (unfold_locales; (fact RISCV64.Refine_assms)?)?)
qed

end
