(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   The main theorem
*)

theory Refine
imports
  KernelInit_R
  ADT_H
  InitLemmas
  PageTableDuplicates
begin

context begin interpretation Arch . (*FIXME: arch_split*)

text \<open>User memory content is the same on both levels\<close>
lemma typ_at_AUserDataI:
  "\<lbrakk> typ_at (AArch (AUserData sz)) p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s'; n < 2 ^ (pageBitsForSize sz - pageBits) \<rbrakk>
        \<Longrightarrow> typ_at' UserDataT (p + n * 2 ^ pageBits) s'"
  apply (clarsimp simp add: obj_at_def a_type_def )
  apply (simp split: Structures_A.kernel_object.split_asm
                     arch_kernel_obj.split_asm split: if_split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp)
  apply (drule_tac x = "p + n * 2 ^ pageBits" in spec)
  apply (drule_tac x = "\<lambda>_ obj. obj = KOUserData" in spec)
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  apply (rule exI [where x = KOUserData])
  apply (drule mp)
   apply (rule exI [where x = n])
   apply simp
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
  apply (clarsimp simp: obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)
  apply (rule exI [where x = KOUserDataDevice])
  apply (drule mp)
   apply (rule exI [where x = n])
   apply simp
  apply (clarsimp simp: pspace_aligned'_def)
  apply (drule (1) bspec [OF _ domI])
  apply (clarsimp simp: objBits_simps)
  apply (fastforce  dest!: pspace_distinctD'  simp: objBits_simps)
  done

lemma typ_at_UserDataI:
  "\<lbrakk> typ_at' UserDataT (p && ~~ mask pageBits) s';
     pspace_relation (kheap s) (ksPSpace s'); pspace_aligned s \<rbrakk>
  \<Longrightarrow> \<exists>sz. typ_at (AArch (AUserData sz)) (p && ~~ mask (pageBitsForSize sz)) s"
  apply (clarsimp simp: exists_disj obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)

  apply (frule (1) in_related_pspace_dom)
  apply (clarsimp simp: pspace_dom_def)
  apply (clarsimp simp: pspace_relation_def dom_def)
  apply (erule allE, erule impE, blast)
  apply clarsimp
  apply (drule (1) bspec)
  apply clarsimp
  apply (subst mask_lower_twice [where n = pageBits, OF pbfs_atleast_pageBits, symmetric])
  apply (clarsimp simp: obj_relation_cuts_def2 pte_relation_def
                        cte_relation_def other_obj_relation_def
                        pde_relation_def tcb_relation_cut_def
              split: Structures_A.kernel_object.split_asm
                     Structures_H.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (rename_tac vmpage_size n)
  apply (rule_tac x = vmpage_size in exI)
  apply (subst conjunct2 [OF is_aligned_add_helper])
    apply (drule (1) pspace_alignedD)
    apply simp
   apply (erule word_less_power_trans2 [OF _ pbfs_atleast_pageBits])
   apply (case_tac vmpage_size, simp_all add: word_bits_conv)[1]
  apply (simp add: obj_at_def  a_type_def)
  done

lemma typ_at_DeviceDataI:
  "\<lbrakk> typ_at' UserDataDeviceT (p && ~~ mask pageBits) s';
     pspace_relation (kheap s) (ksPSpace s'); pspace_aligned s \<rbrakk>
  \<Longrightarrow> \<exists>sz. typ_at (AArch (ADeviceData sz)) (p && ~~ mask (pageBitsForSize sz)) s"
  apply (clarsimp simp: exists_disj obj_at'_def typ_at'_def ko_wp_at'_def
                        projectKOs)

  apply (frule (1) in_related_pspace_dom)
  apply (clarsimp simp: pspace_dom_def)
  apply (clarsimp simp: pspace_relation_def dom_def)
  apply (erule allE, erule impE, blast)
  apply clarsimp
  apply (drule (1) bspec)
  apply clarsimp
  apply (subst mask_lower_twice [where n = pageBits, OF pbfs_atleast_pageBits, symmetric])
  apply (clarsimp simp: obj_relation_cuts_def2 pte_relation_def
                        cte_relation_def other_obj_relation_def
                        pde_relation_def tcb_relation_cut_def
              split: Structures_A.kernel_object.split_asm
                     Structures_H.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (rename_tac vmpage_size n)
  apply (rule_tac x = vmpage_size in exI)
  apply (subst conjunct2 [OF is_aligned_add_helper])
    apply (drule (1) pspace_alignedD)
    apply simp
   apply (erule word_less_power_trans2 [OF _ pbfs_atleast_pageBits])
   apply (case_tac vmpage_size, simp_all add: word_bits_conv)[1]
  apply (simp add: obj_at_def  a_type_def)
  done

lemma pointerInUserData_relation:
  "\<lbrakk> (s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
   \<Longrightarrow> pointerInUserData p s' = in_user_frame p s"
  apply (simp add: pointerInUserData_def in_user_frame_def)
  apply (rule iffI)
   apply (erule typ_at_UserDataI, (clarsimp simp: valid_state_def)+)[1]
  apply clarsimp
  apply (drule_tac sz = sz and
                   n = "(p && mask (pageBitsForSize sz)) >> pageBits"
    in typ_at_AUserDataI [where s = s and s' = s'])
      apply (fastforce simp: valid_state'_def)+
   apply (rule shiftr_less_t2n')
    apply (simp add: pbfs_atleast_pageBits mask_twice)
   apply (case_tac sz, simp_all)[1]
  apply (subgoal_tac "(p && ~~ mask (pageBitsForSize sz)) + (p && mask (pageBitsForSize sz) >> pageBits) * 2 ^ pageBits = (p && ~~ mask pageBits)")
   apply simp
  apply (subst mult.commute)
  apply (subst shiftl_t2n [symmetric])
  apply (simp add: shiftr_shiftl1)
  apply (subst mask_out_add_aligned)
   apply (rule is_aligned_neg_mask)
   apply (simp add: pbfs_atleast_pageBits)
  apply (subst add.commute)
  apply (simp add: word_plus_and_or_coroll2)
  done

lemma pointerInDeviceData_relation:
  "\<lbrakk> (s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
   \<Longrightarrow> pointerInDeviceData p s' = in_device_frame p s"
  apply (simp add: pointerInDeviceData_def in_device_frame_def)
  apply (rule iffI)
   apply (erule typ_at_DeviceDataI, (clarsimp simp: valid_state_def)+)[1]
  apply clarsimp
  apply (drule_tac sz = sz and
                   n = "(p && mask (pageBitsForSize sz)) >> pageBits"
    in typ_at_ADeviceDataI [where s = s and s' = s'])
      apply (fastforce simp: valid_state'_def)+
   apply (rule shiftr_less_t2n')
    apply (simp add: pbfs_atleast_pageBits mask_twice)
   apply (case_tac sz, simp_all)[1]
  apply (subgoal_tac "(p && ~~ mask (pageBitsForSize sz)) + (p && mask (pageBitsForSize sz) >> pageBits) * 2 ^ pageBits = (p && ~~ mask pageBits)")
   apply simp
  apply (subst mult.commute)
  apply (subst shiftl_t2n [symmetric])
  apply (simp add: shiftr_shiftl1)
  apply (subst mask_out_add_aligned)
   apply (rule is_aligned_neg_mask)
   apply (simp add: pbfs_atleast_pageBits)
  apply (subst add.commute)
  apply (simp add: word_plus_and_or_coroll2)
  done

lemma user_mem_relation:
  "\<lbrakk>(s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
   \<Longrightarrow> user_mem' s' = user_mem s"
  apply (rule ext)
  apply (clarsimp simp: user_mem_def user_mem'_def pointerInUserData_relation pointerInDeviceData_relation)
  apply (simp add: state_relation_def)
  done

lemma device_mem_relation:
  "\<lbrakk>(s,s') \<in> state_relation; valid_state' s'; valid_state s\<rbrakk>
   \<Longrightarrow> device_mem' s' = device_mem s"
  apply (rule ext)
  apply (clarsimp simp: device_mem_def device_mem'_def pointerInUserData_relation
     pointerInDeviceData_relation)
  done

lemma absKState_correct:
assumes invs: "einvs (s :: det_ext state)" and invs': "invs' s'"
assumes rel: "(s,s') \<in> state_relation"
shows "absKState s' = abs_state s"
  using assms
  apply (intro state.equality, simp_all add: absKState_def abs_state_def)
           apply (rule absHeap_correct, clarsimp+)
           apply (clarsimp elim!: state_relationE)
          apply (rule absCDT_correct, clarsimp+)
         apply (rule absIsOriginalCap_correct, clarsimp+)
        apply (simp add: state_relation_def)
       apply (simp add: state_relation_def)
      apply (clarsimp simp:  user_mem_relation invs_def invs'_def)
      apply (simp add: state_relation_def)
     apply (rule absInterruptIRQNode_correct, simp add: state_relation_def)
    apply (rule absInterruptStates_correct, simp add: state_relation_def)
   apply (rule absArchState_correct, simp)
  apply (rule absExst_correct, simp+)
  done

text \<open>The top-level invariance\<close>

lemma set_thread_state_sched_act:
  "\<lbrace>(\<lambda>s. runnable state) and (\<lambda>s. P (scheduler_action s))\<rbrace>
  set_thread_state thread state
  \<lbrace>\<lambda>rs s. P (scheduler_action (s::det_state))\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply wp
    apply (simp add: set_thread_state_ext_def)
    apply wp
       apply (rule hoare_pre_cont)
      apply (rule_tac Q="\<lambda>rv. (\<lambda>s. runnable ts) and (\<lambda>s. P (scheduler_action s))"
              in hoare_strengthen_post)
       apply wp
      apply force
     apply (wp gts_st_tcb_at)+
     apply (rule_tac Q="\<lambda>rv. st_tcb_at ((=) state) thread and (\<lambda>s. runnable state) and (\<lambda>s. P (scheduler_action s))" in hoare_strengthen_post)
     apply (simp add: st_tcb_at_def)
     apply (wp obj_set_prop_at)+
    apply (force simp: st_tcb_at_def obj_at_def)
  apply wp
  apply clarsimp
  done

lemma activate_thread_sched_act:
  "\<lbrace>ct_in_state activatable and (\<lambda>s. P (scheduler_action s))\<rbrace>
  activate_thread
  \<lbrace>\<lambda>rs s. P (scheduler_action (s::det_state))\<rbrace>"
  by (simp add: activate_thread_def set_thread_state_def arch_activate_idle_thread_def
      | (wp set_thread_state_sched_act gts_wp)+ | wpc)+

lemma schedule_sched_act_rct[wp]:
  "\<lbrace>\<top>\<rbrace> Schedule_A.schedule
  \<lbrace>\<lambda>rs (s::det_state). scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding Schedule_A.schedule_def
  by (wpsimp)

lemma call_kernel_sched_act_rct[wp]:
  "\<lbrace>einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)
     and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
  call_kernel e
  \<lbrace>\<lambda>rs (s::det_state). scheduler_action s = resume_cur_thread\<rbrace>"
  apply (simp add: call_kernel_def)
  apply (wp activate_thread_sched_act | simp)+
  apply (clarsimp simp: active_from_running)
  done

lemma kernel_entry_invs:
  "\<lbrace>einvs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)
    and (\<lambda>s. 0 < domain_time s) and valid_domain_list and (ct_running or ct_idle)
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>
  kernel_entry e us
  \<lbrace>\<lambda>rv. einvs and (\<lambda>s. ct_running s \<or> ct_idle s)
    and (\<lambda>s. 0 < domain_time s) and valid_domain_list
    and (\<lambda>s. scheduler_action s = resume_cur_thread)\<rbrace>"
  apply (rule_tac Q="\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s) and valid_sched and
                           (\<lambda>s. 0 < domain_time s) and valid_domain_list and
                           valid_list and (\<lambda>s. scheduler_action s = resume_cur_thread)"
            in hoare_post_imp)
   apply clarsimp
  apply (simp add: kernel_entry_def)
  apply (wp akernel_invs_det_ext call_kernel_valid_sched thread_set_invs_trivial
            thread_set_ct_running thread_set_not_state_valid_sched
            hoare_vcg_disj_lift ct_in_state_thread_state_lift thread_set_no_change_tcb_state
            call_kernel_domain_time_inv_det_ext call_kernel_domain_list_inv_det_ext
            hoare_weak_lift_imp
      | clarsimp simp add: tcb_cap_cases_def active_from_running)+
  done

definition
  "full_invs \<equiv> {((tc, s :: det_ext state), m, e). einvs s \<and>
                                 (ct_running s \<or> ct_idle s) \<and>
                                 (m = KernelMode \<longrightarrow> e \<noteq> None) \<and>
                                 (m = UserMode \<longrightarrow> ct_running s) \<and>
                                 (m = IdleMode \<longrightarrow> ct_idle s) \<and>
                                 (e \<noteq> None \<and> e \<noteq> Some Interrupt \<longrightarrow> ct_running s) \<and>
                                 0 < domain_time s \<and> valid_domain_list s \<and>
                                 (scheduler_action s = resume_cur_thread)}"

lemma do_user_op_valid_list:"\<lbrace>valid_list\<rbrace> do_user_op f tc \<lbrace>\<lambda>_. valid_list\<rbrace>"
  unfolding do_user_op_def
  apply (wp | simp add: split_def)+
  done

lemma do_user_op_valid_sched:"\<lbrace>valid_sched\<rbrace> do_user_op f tc \<lbrace>\<lambda>_. valid_sched\<rbrace>"
  unfolding do_user_op_def
  apply (wp | simp add: split_def)+
  done

lemma do_user_op_sched_act:
  "\<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> do_user_op f tc \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>"
  unfolding do_user_op_def
  apply (wp | simp add: split_def)+
  done

lemma do_user_op_invs2:
  "\<lbrace>einvs  and ct_running and (\<lambda>s. scheduler_action s = resume_cur_thread)
    and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>
  do_user_op f tc
   \<lbrace>\<lambda>_. (einvs  and ct_running and (\<lambda>s. scheduler_action s = resume_cur_thread))
        and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>"
  apply (rule_tac Q="\<lambda>_. valid_list and valid_sched and
   (\<lambda>s. scheduler_action s = resume_cur_thread) and (invs and ct_running) and
   (\<lambda>s. 0 < domain_time s) and valid_domain_list"
   in hoare_strengthen_post)
  apply (wp do_user_op_valid_list do_user_op_valid_sched do_user_op_sched_act
    do_user_op_invs | simp | force)+
  done

lemmas ext_init_def = ext_init_det_ext_ext_def ext_init_unit_def

lemma valid_list_init[simp]:
  "valid_list init_A_st"
  by (simp add: valid_list_2_def init_A_st_def ext_init_def init_cdt_def)

lemmas valid_list_inits[simp] = valid_list_init[simplified]

lemma valid_sched_init[simp]:
  "valid_sched init_A_st"
  apply (simp add: valid_sched_def init_A_st_def ext_init_def)
  apply (clarsimp simp: valid_etcbs_def init_kheap_def st_tcb_at_kh_def obj_at_kh_def
                    obj_at_def is_etcb_at_def idle_thread_ptr_def init_globals_frame_def
                    valid_queues_2_def ct_not_in_q_def not_queued_def
                    valid_sched_action_def is_activatable_def us_global_pd_ptr_def
                    ct_in_cur_domain_2_def valid_blocked_2_def valid_idle_etcb_def etcb_at'_def default_etcb_def)
  done

lemma valid_domain_list_init[simp]:
  "valid_domain_list init_A_st"
  by (simp add: init_A_st_def ext_init_def valid_domain_list_def)

lemma akernel_invariant:
  "ADT_A uop \<Turnstile> full_invs"
  unfolding full_invs_def
  apply (rule invariantI)
   apply (clarsimp simp: ADT_A_def subset_iff)
   apply (frule bspec[OF akernel_init_invs])
   apply (simp add: Let_def Init_A_def)
   apply (simp add: init_A_st_def ext_init_def)
  apply (clarsimp simp: ADT_A_def global_automaton_def)

  apply (rename_tac tc' s' mode' e' tc s mode e)
  apply (elim disjE)
             apply ((clarsimp simp: kernel_call_A_def
                   | drule use_valid[OF _ kernel_entry_invs])+)[2]
           apply ((clarsimp simp: do_user_op_A_def monad_to_transition_def
                                  check_active_irq_A_def
                 | drule use_valid[OF _ do_user_op_invs2]
                 | drule use_valid[OF _ check_active_irq_invs_just_running])+)[2]
         apply ((clarsimp simp add: check_active_irq_A_def
               | drule use_valid[OF _ check_active_irq_invs])+)[1]
        apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
       apply ((clarsimp simp add: do_user_op_A_def check_active_irq_A_def
             | drule use_valid[OF _ do_user_op_invs2]
             | drule use_valid[OF _ check_active_irq_invs_just_running])+)[1]
      apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
     apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)
    apply ((clarsimp simp add: check_active_irq_A_def
         | drule use_valid[OF _ check_active_irq_invs])+)[1]
   apply ((clarsimp simp add: check_active_irq_A_def
        | drule use_valid[OF _ check_active_irq_invs_just_idle])+)[1]
  apply ((clarsimp simp add: check_active_irq_A_def
        | drule use_valid[OF _ check_active_irq_invs])+)[1]
  done

lemma ckernel_invs:
  "\<lbrace>invs' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
               (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) and
               (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
  callKernel e
  \<lbrace>\<lambda>rs. (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
    and (invs' and (ct_running' or ct_idle'))\<rbrace>"
  apply (simp add: callKernel_def)
  apply (rule hoare_pre)
   apply (wp activate_invs' activate_sch_act schedule_sch
             schedule_sch_act_simple he_invs' schedule_invs' hoare_vcg_if_lift3
             hoare_drop_imp[where R="\<lambda>_. kernelExitAssertions"]
          | simp add: no_irq_getActiveIRQ
          | strengthen non_kernel_IRQs_strg[where Q=True, simplified], simp cong: conj_cong)+
  done

(* abstract and haskell have identical domain list fields *)
abbreviation valid_domain_list' :: "'a kernel_state_scheme \<Rightarrow> bool" where
  "valid_domain_list' \<equiv> \<lambda>s. valid_domain_list_2 (ksDomSchedule s)"

lemmas valid_domain_list'_def = valid_domain_list_2_def

lemma fastpathKernelAssertions_cross:
  "\<lbrakk> (s,s') \<in> state_relation; invs s; valid_arch_state' s'\<rbrakk> \<Longrightarrow> fastpathKernelAssertions s'"
  unfolding fastpathKernelAssertions_def
  by simp

(* this is only needed for callKernel, where we have invs' on concrete side *)
lemma corres_cross_over_fastpathKernelAssertions:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> invs s; \<And>s'. Q s' \<Longrightarrow> invs' s';
     corres r P (Q and fastpathKernelAssertions) f g \<rbrakk> \<Longrightarrow>
   corres r P Q f g"
  by (rule corres_cross_over_guard[where Q="Q and fastpathKernelAssertions"])
     (fastforce elim: fastpathKernelAssertions_cross)+

defs kernelExitAssertions_def:
  "kernelExitAssertions s \<equiv> 0 < ksDomainTime s \<and> valid_domain_list' s"

lemma callKernel_domain_time_left:
  "\<lbrace> \<top> \<rbrace> callKernel e \<lbrace>\<lambda>_ s. 0 < ksDomainTime s \<and> valid_domain_list' s \<rbrace>"
  unfolding callKernel_def kernelExitAssertions_def by wpsimp

lemma kernelEntry_invs':
  "\<lbrace> invs' and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running' s) and
           (ct_running' or ct_idle') and
           (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
           (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
           (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list' \<rbrace>
  kernelEntry e tc
  \<lbrace>\<lambda>rs. (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
         (invs' and (ct_running' or ct_idle')) and
         (\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and
         (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list' \<rbrace>"
  apply (simp add: kernelEntry_def)
  apply (wp ckernel_invs callKernel_valid_duplicates' callKernel_domain_time_left
            threadSet_invs_trivial threadSet_ct_running'
            TcbAcc_R.dmo_invs' callKernel_domain_time_left
            hoare_weak_lift_imp
         | clarsimp simp: user_memory_update_def no_irq_def tcb_at_invs' atcbContextSet_def
                          valid_domain_list'_def)+
  done

lemma absKState_correct':
  "\<lbrakk>einvs s; invs' s'; (s,s') \<in> state_relation\<rbrakk>
   \<Longrightarrow> absKState s' = abs_state s"
  apply (intro state.equality, simp_all add: absKState_def abs_state_def)
           apply (rule absHeap_correct)
               apply (clarsimp simp: valid_state_def valid_pspace_def)+
           apply (clarsimp dest!: state_relationD)
          apply (rule absCDT_correct)
                apply (clarsimp simp: valid_state_def valid_pspace_def
                                      valid_state'_def valid_pspace'_def)+
         apply (rule absIsOriginalCap_correct, clarsimp+)
        apply (simp add: state_relation_def)
       apply (simp add: state_relation_def)
      apply (clarsimp simp: user_mem_relation invs_def invs'_def)
      apply (simp add: state_relation_def)
     apply (rule absInterruptIRQNode_correct, simp add: state_relation_def)
    apply (rule absInterruptStates_correct, simp add: state_relation_def)
   apply (erule absArchState_correct)
  apply (rule absExst_correct, simp, assumption+)
  done

lemma ptable_lift_abs_state[simp]:
  "ptable_lift t (abs_state s) = ptable_lift t s"
  by (simp add: ptable_lift_def abs_state_def)

lemma ptable_rights_abs_state[simp]:
  "ptable_rights t (abs_state s) = ptable_rights t s"
  by (simp add: ptable_rights_def abs_state_def)

lemma ptable_rights_imp_UserData:
  assumes invs: "einvs s" and invs': "invs' s'"
  assumes rel: "(s,s') : state_relation"
  assumes rights: "ptable_rights t (absKState s') x \<noteq> {}"
  assumes trans:
    "ptable_lift t (absKState s') x = Some (ARM_HYP.addrFromPPtr y)"
  shows "pointerInUserData y s' \<or> pointerInDeviceData y s'"
proof -
  from invs invs' rel have [simp]: "absKState s' = abs_state s"
    by - (rule absKState_correct', simp_all)
  from invs have valid: "valid_state s" by auto
  from invs' have valid': "valid_state' s'" by auto
  have "in_user_frame y s \<or> in_device_frame y s "
    by (rule ptable_rights_imp_frame[OF valid rights[simplified]
                                             trans[simplified]])
  thus ?thesis
   by (auto simp add: pointerInUserData_relation[OF rel valid' valid]
     pointerInDeviceData_relation[OF rel valid' valid])
qed

abbreviation
  "ex_abs G \<equiv> ex_abs_underlying state_relation G"

lemma ex_abs_def:
  "ex_abs G \<equiv> \<lambda>s'. \<exists>s. ((s :: (det_ext) state),s') \<in> state_relation \<and> G s"
  by (auto simp add: ex_abs_underlying_def[abs_def])

lemma device_update_invs':
  "\<lbrace>invs'\<rbrace>doMachineOp (device_memory_update ds)
   \<lbrace>\<lambda>_. invs'\<rbrace>"
   apply (simp add: doMachineOp_def device_memory_update_def simpler_modify_def select_f_def
                    gets_def get_def bind_def valid_def return_def)
   by (clarsimp simp: invs'_def valid_state'_def valid_irq_states'_def valid_machine_state'_def)

crunches doMachineOp
  for ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"

lemma doUserOp_invs':
  "\<lbrace>invs' and ex_abs einvs and
    (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running' and
    (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list'\<rbrace>
   doUserOp f tc
   \<lbrace>\<lambda>_. invs' and
        (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and ct_running' and
        (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list'\<rbrace>"
  apply (simp add: doUserOp_def split_def ex_abs_def)
  apply (wp device_update_invs'
    | (wp (once) dmo_invs', wpsimp simp: no_irq_modify device_memory_update_def
                                       user_memory_update_def))+
  apply (clarsimp simp: user_memory_update_def simpler_modify_def
                        restrict_map_def
                 split: option.splits)
  apply (frule ptable_rights_imp_UserData[rotated 2], auto)
  done

lemma doUserOp_valid_duplicates':
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
   doUserOp f tc
   \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: doUserOp_def split_def)
  apply (wp dmo_invs')
  apply clarsimp
  done

lemma None_drop:
  "P \<Longrightarrow> x = None \<longrightarrow> P"
  by simp

lemma Ex_Some_conv:
  "((\<exists>y. x = Some y) \<longrightarrow> P x) = (\<forall>y. x = Some y \<longrightarrow> P (Some y))"
  by auto

text \<open>The top-level correspondence\<close>

lemma kernel_corres':
  "corres dc (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle)
               and (\<lambda>s. scheduler_action s = resume_cur_thread))
             (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle') and
              (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
              (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
             (call_kernel event)
             (do _ \<leftarrow> runExceptT $
                      handleEvent event `~catchError~`
                        (\<lambda>_. withoutPreemption $ do
                               irq <- doMachineOp (getActiveIRQ True);
                               when (isJust irq) $ handleInterrupt (fromJust irq)
                             od);
                 _ \<leftarrow> ThreadDecls_H.schedule;
                 activateThread
              od)"
  unfolding call_kernel_def callKernel_def
  apply (simp add: call_kernel_def callKernel_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule corres_split_handle[OF handleEvent_corres])
         apply simp
         apply (rule corres_split[OF corres_machine_op])
            apply (rule corres_underlying_trivial)
            apply (rule no_fail_getActiveIRQ)
           apply clarsimp
           apply (rule_tac x=irq in option_corres)
            apply (rule_tac P=\<top> and P'=\<top> in corres_inst)
            apply (simp add: when_def)
           apply (rule corres_when[simplified dc_def], simp)
           apply simp
           apply (rule handleInterrupt_corres[simplified dc_def])
          apply simp
          apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift simp: schact_is_rct_def)[1]
         apply simp
         apply (rule_tac Q="\<lambda>irq s. irq \<notin> Some ` non_kernel_IRQs \<and> invs' s \<and>
                              (\<forall>irq'. irq = Some irq' \<longrightarrow>
                                 intStateIRQTable (ksInterruptState s ) irq' \<noteq> IRQInactive)"
                      in hoare_post_imp)
          apply clarsimp
         apply (wp doMachineOp_getActiveIRQ_IRQ_active handle_event_valid_sched | simp)+
       apply (rule_tac Q="\<lambda>_. \<top>" and E="\<lambda>_. invs'" in hoare_post_impErr)
         apply wpsimp+
       apply (simp add: invs'_def valid_state'_def)
      apply (rule corres_split[OF schedule_corres])
        apply (rule activateThread_corres)
       apply (wp schedule_invs' hoare_vcg_if_lift2 dmo_getActiveIRQ_non_kernel
              | simp cong: rev_conj_cong | strengthen None_drop | subst Ex_Some_conv)+
     apply (rule_tac Q="\<lambda>_. valid_sched and invs and valid_list" and E="\<lambda>_. valid_sched and invs and valid_list"
            in hoare_post_impErr)
       apply (wp handle_event_valid_sched hoare_vcg_if_lift3
              | simp
              | strengthen non_kernel_IRQs_strg[where Q=True, simplified], simp cong: conj_cong)+
   apply (clarsimp simp: active_from_running schact_is_rct_def)
  apply (clarsimp simp: active_from_running')
  done

lemma kernel_corres:
  "corres dc (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and (ct_running or ct_idle) and
              (\<lambda>s. scheduler_action s = resume_cur_thread) and
              (\<lambda>s. 0 < domain_time s \<and> valid_domain_list s))
             (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and (ct_running' or ct_idle') and
              (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
              (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
             (call_kernel event) (callKernel event)"
  unfolding callKernel_def K_bind_def
  apply (rule corres_cross_over_fastpathKernelAssertions, blast+)
  apply (rule corres_stateAssert_r)
  apply (rule corres_guard_imp)
    apply (rule corres_add_noop_lhs2)
    apply (simp only: bind_assoc[symmetric])
    apply (rule corres_split[where r'=dc and
                                   R="\<lambda>_ s. 0 < domain_time s \<and> valid_domain_list s" and
                                   R'="\<lambda>_. \<top>"])
       apply (simp only: bind_assoc)
       apply (rule kernel_corres')
      apply (rule corres_bind_return2, rule corres_stateAssert_assume_stronger)
       apply simp
      apply (simp add: kernelExitAssertions_def state_relation_def)
     apply (wp call_kernel_domain_time_inv_det_ext call_kernel_domain_list_inv_det_ext)
    apply wp
   apply clarsimp
  apply clarsimp
  done

lemma user_mem_corres:
  "corres (=) invs invs' (gets (\<lambda>x. g (user_mem x))) (gets (\<lambda>x. g (user_mem' x)))"
  by (clarsimp simp add: gets_def get_def return_def bind_def
                         invs_def invs'_def
                         corres_underlying_def user_mem_relation)

lemma device_mem_corres:
  "corres (=) invs invs' (gets (\<lambda>x. g (device_mem x))) (gets (\<lambda>x. g (device_mem' x)))"
  by (clarsimp simp add: gets_def get_def return_def bind_def
                         invs_def invs'_def
                         corres_underlying_def device_mem_relation)

lemma entry_corres:
  "corres (=) (einvs and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running s) and
                  (\<lambda>s. 0 < domain_time s) and valid_domain_list and (ct_running or ct_idle) and
                  (\<lambda>s. scheduler_action s = resume_cur_thread))
                 (invs' and (\<lambda>s. event \<noteq> Interrupt \<longrightarrow> ct_running' s) and
                  (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list' and (ct_running' or ct_idle') and
                  (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread) and
                  (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
          (kernel_entry event tc) (kernelEntry event tc)"
  apply (simp add: kernel_entry_def kernelEntry_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule corres_split)
         apply simp
         apply (rule threadset_corresT; simp?)
            apply (simp add: tcb_relation_def arch_tcb_relation_def
                             arch_tcb_context_set_def atcbContextSet_def)
           apply (clarsimp simp: tcb_cap_cases_def)
          apply (clarsimp simp: tcb_cte_cases_def)
         apply (simp add: exst_same_def)
        apply (rule corres_split[OF kernel_corres])
          apply (rule corres_split_eqr[OF getCurThread_corres])
            apply (rule threadGet_corres)
            apply (simp add: tcb_relation_def arch_tcb_relation_def
                             arch_tcb_context_get_def atcbContextGet_def)
           apply wp+
         apply (rule hoare_strengthen_post, rule akernel_invs_det_ext,
                simp add: invs_def valid_state_def valid_pspace_def cur_tcb_def)
        apply (rule hoare_strengthen_post, rule ckernel_invs, simp add: invs'_def cur_tcb'_def)
       apply ((wp thread_set_invs_trivial thread_set_ct_running
                  thread_set_not_state_valid_sched hoare_weak_lift_imp
                  hoare_vcg_disj_lift ct_in_state_thread_state_lift
               | simp add: tcb_cap_cases_def thread_set_no_change_tcb_state schact_is_rct_def)+)[1]
      apply (simp add: pred_conj_def cong: conj_cong)
      apply (wp threadSet_invs_trivial threadSet_ct_running'
                 hoare_weak_lift_imp hoare_vcg_disj_lift
              | simp add: ct_in_state'_def atcbContextSet_def
              | (wps, wp threadSet_st_tcb_at2))+
   apply (fastforce simp: invs_def cur_tcb_def)
  apply (clarsimp simp: ct_in_state'_def)
  done

lemma corres_gets_machine_state:
  "corres (=) \<top> \<top> (gets (f \<circ> machine_state)) (gets (f \<circ> ksMachineState))"
  by (clarsimp simp: gets_def corres_underlying_def
                     in_monad bind_def get_def return_def state_relation_def)

lemma do_user_op_corres:
  "corres (=) (einvs and ct_running)
                 (invs' and (%s. ksSchedulerAction s = ResumeCurrentThread) and
                  ct_running')
          (do_user_op f tc) (doUserOp f tc)"
  apply (simp add: do_user_op_def doUserOp_def split_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule_tac r'="(=)" and P=einvs and P'=invs' in corres_split)
         apply (fastforce dest: absKState_correct [rotated])
        apply (rule_tac r'="(=)" and P=einvs and P'=invs' in corres_split)
           apply (fastforce dest: absKState_correct [rotated])
          apply (rule_tac r'="(=)" and P=invs and P'=invs' in corres_split)
             apply (rule user_mem_corres)
            apply (rule_tac r'="(=)" and P=invs and P'=invs' in corres_split)
               apply (rule device_mem_corres)
              apply (rule_tac r'="(=)" in corres_split)
                 apply (rule corres_gets_machine_state)
                apply (rule_tac F = "dom (rvb \<circ> addrFromPPtr)  \<subseteq> - dom rvd" in corres_gen_asm)
                apply (rule_tac F = "dom (rvc \<circ> addrFromPPtr)  \<subseteq> dom rvd" in corres_gen_asm)
                apply simp
                apply (rule_tac r'="(=)" in corres_split[OF corres_select])
                   apply simp
                  apply (rule corres_underlying_split[OF corres_machine_op])
                     apply simp
                     apply (rule corres_underlying_trivial)
                     apply (simp add: user_memory_update_def)
                     apply (wp | simp)+
                    apply (rule corres_underlying_split[OF corres_machine_op,where Q = dc and Q'=dc])
                       apply (rule corres_underlying_trivial)
                       apply (wp | simp add: dc_def device_memory_update_def)+
   apply (clarsimp simp: invs_def valid_state_def pspace_respects_device_region_def)
  apply fastforce
  done

lemma ct_running_related:
  "\<lbrakk> (a, c) \<in> state_relation; ct_running' c \<rbrakk>
     \<Longrightarrow> ct_running a"
  apply (clarsimp simp: ct_in_state_def ct_in_state'_def
                        curthread_relation)
  apply (frule(1) st_tcb_at_coerce_abstract)
  apply (erule st_tcb_weakenE)
  apply (case_tac st, simp_all)[1]
  done

lemma ct_idle_related:
  "\<lbrakk> (a, c) \<in> state_relation; ct_idle' c \<rbrakk>
     \<Longrightarrow> ct_idle a"
  apply (clarsimp simp: ct_in_state_def ct_in_state'_def
                        curthread_relation)
  apply (frule(1) st_tcb_at_coerce_abstract)
  apply (erule st_tcb_weakenE)
  apply (case_tac st, simp_all)[1]
  done

definition
  "full_invs' \<equiv> {((tc,s),m,e). invs' s \<and> vs_valid_duplicates' (ksPSpace s) \<and>
                          ex_abs (einvs::det_ext state \<Rightarrow> bool) s \<and>
                          ksSchedulerAction s = ResumeCurrentThread \<and>
                          (ct_running' s \<or> ct_idle' s) \<and>
                          (m = KernelMode \<longrightarrow> e \<noteq> None) \<and>
                          (m = UserMode \<longrightarrow> ct_running' s) \<and>
                          (m = IdleMode \<longrightarrow> ct_idle' s) \<and>
                          (e \<noteq> None \<and> e \<noteq> Some Interrupt \<longrightarrow> ct_running' s) \<and>
                          0 < ksDomainTime s \<and> valid_domain_list' s}"

lemma checkActiveIRQ_valid_duplicates':
  "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
   checkActiveIRQ
   \<lbrace>\<lambda>_ s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add: checkActiveIRQ_def)
  apply wp
  done

lemma check_active_irq_corres':
  "corres (=) \<top> \<top> (check_active_irq) (checkActiveIRQ)"
  apply (simp add: check_active_irq_def checkActiveIRQ_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_machine_op[OF corres_underlying_trivial], where R="\<lambda>_. \<top>" and R'="\<lambda>_. \<top>"])
       apply simp
      apply (rule no_fail_getActiveIRQ)
     apply (wp | simp )+
  done

lemma check_active_irq_corres:
  "corres (=)
    (invs and (ct_running or ct_idle) and einvs and (\<lambda>s. scheduler_action s = resume_cur_thread)
     and (\<lambda>s. 0 < domain_time s) and valid_domain_list)
    (invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)
      and (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list' and (ct_running' or ct_idle')
      and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
    (check_active_irq) (checkActiveIRQ)"
  apply (rule corres_guard_imp)
    apply (rule check_active_irq_corres', auto)
  done

lemma checkActiveIRQ_just_running_corres:
  "corres (=)
    (invs and ct_running and einvs and (\<lambda>s. scheduler_action s = resume_cur_thread)
      and (\<lambda>s. 0 < domain_time s) and valid_domain_list)
    (invs' and ct_running' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
      and (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list'
      and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
    (check_active_irq) (checkActiveIRQ)"
  apply (rule corres_guard_imp)
    apply (rule check_active_irq_corres', auto)
  done

lemma checkActiveIRQ_just_idle_corres:
  "corres (=)
    (invs and ct_idle and einvs and (\<lambda>s. scheduler_action s = resume_cur_thread)
      and (\<lambda>s. 0 < domain_time s)  and valid_domain_list)
    (invs' and ct_idle' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))
      and (\<lambda>s. 0 < ksDomainTime s) and valid_domain_list'
      and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread))
    (check_active_irq) (checkActiveIRQ)"
  apply (rule corres_guard_imp)
    apply (rule check_active_irq_corres', auto)
  done

lemma checkActiveIRQ_invs':
  "\<lbrace>invs' and ex_abs invs and (ct_running' or ct_idle')
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   checkActiveIRQ
   \<lbrace>\<lambda>_. invs' and (ct_running' or ct_idle')
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>"
  apply (simp add: checkActiveIRQ_def ex_abs_def)
  apply (wp dmo_invs' | simp)+
  done

lemma checkActiveIRQ_invs'_just_running:
  "\<lbrace>invs' and ex_abs invs and ct_running'
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   checkActiveIRQ
   \<lbrace>\<lambda>_. invs' and ct_running'
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>"
  apply (simp add: checkActiveIRQ_def)
  apply (wp | simp)+
  done

lemma checkActiveIRQ_invs'_just_idle:
  "\<lbrace>invs' and ex_abs invs and ct_idle'
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>
   checkActiveIRQ
   \<lbrace>\<lambda>_. invs' and ct_idle'
    and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread)\<rbrace>"
  apply (simp add: checkActiveIRQ_def)
  apply (wp | simp)+
  done

lemma sched_act_rct_related:
  "\<lbrakk> (a, c) \<in> state_relation; ksSchedulerAction c = ResumeCurrentThread\<rbrakk>
     \<Longrightarrow> scheduler_action a = resume_cur_thread"
  by (case_tac "scheduler_action a", simp_all add: state_relation_def)

lemma domain_time_rel_eq:
  "(a, c) \<in> state_relation \<Longrightarrow> P (ksDomainTime c) = P (domain_time a)"
  by (clarsimp simp: state_relation_def)

lemma domain_list_rel_eq:
  "(a, c) \<in> state_relation \<Longrightarrow> P (ksDomSchedule c) = P (domain_list a)"
  by (clarsimp simp: state_relation_def)

lemma ckernel_invariant:
  "ADT_H uop \<Turnstile> full_invs'"
  unfolding full_invs'_def
  supply word_neq_0_conv[simp]
  supply domain_time_rel_eq[simp] domain_list_rel_eq[simp]
  apply (rule invariantI)
   apply (clarsimp simp add: ADT_H_def)
   apply (subst conj_commute, simp)
   apply (rule conjI)
    apply (drule ckernel_init_valid_duplicates'[rule_format], simp)
   apply (rule conjI)
    apply (frule init_refinement[simplified subset_eq, THEN bspec])
    apply (clarsimp simp: ex_abs_def lift_state_relation_def)
    apply (frule akernel_init_invs[THEN bspec])
    apply (rule_tac x = s in exI)
    apply (clarsimp simp: Init_A_def)
   apply (insert ckernel_init_invs)[1]
   apply clarsimp
   apply (frule ckernel_init_sch_norm)
   apply (frule ckernel_init_ctr)
   apply (frule ckernel_init_domain_time)
   apply (frule ckernel_init_domain_list)
   apply (fastforce simp: Init_H_def valid_domain_list'_def)
  apply (clarsimp simp: ADT_A_def ADT_H_def global_automaton_def)

  apply (erule_tac P="a \<and> (\<exists>x. b x)" for a b in disjE)

  apply (clarsimp simp: kernel_call_H_def)

   apply (drule use_valid[OF _ valid_corres_combined
                            [OF kernel_entry_invs entry_corres],
                            OF _ kernelEntry_invs'[THEN hoare_weaken_pre]])
     subgoal by fastforce
    apply (fastforce simp: ex_abs_def sch_act_simple_def ct_running_related ct_idle_related
                           sched_act_rct_related)
   apply (clarsimp simp: kernel_call_H_def)
   subgoal by (fastforce simp: ex_abs_def sch_act_simple_def ct_running_related ct_idle_related
                              sched_act_rct_related)

  apply (erule_tac P="a \<and> b" for a b in disjE)
   apply (clarsimp simp add: do_user_op_H_def monad_to_transition_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_duplicates')
     apply (rule valid_corres_combined[OF do_user_op_invs2 corres_guard_imp2[OF do_user_op_corres]])
      apply clarsimp
     apply (rule doUserOp_invs'[THEN hoare_weaken_pre])
     apply (fastforce simp: ex_abs_def)
    apply (clarsimp simp: ex_abs_def, rule_tac x=s in exI,
            clarsimp simp: ct_running_related sched_act_rct_related)
   apply (clarsimp simp: ex_abs_def)
   apply (fastforce simp: ex_abs_def ct_running_related sched_act_rct_related)

  apply (erule_tac P="a \<and> b \<and> c \<and> (\<exists>x. d x)" for a b c d in disjE)
   apply (clarsimp simp add: do_user_op_H_def monad_to_transition_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule doUserOp_valid_duplicates')
     apply (rule valid_corres_combined[OF do_user_op_invs2 corres_guard_imp2[OF do_user_op_corres]])
      apply clarsimp
     apply (rule doUserOp_invs'[THEN hoare_weaken_pre])
     apply (fastforce simp: ex_abs_def)
    apply (fastforce simp: ex_abs_def ct_running_related sched_act_rct_related)
   apply (fastforce simp: ex_abs_def)

  apply (erule_tac P="a \<and> b" for a b in disjE)
   apply (clarsimp simp: check_active_irq_H_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_duplicates')
     apply (rule valid_corres_combined[OF check_active_irq_invs_just_running checkActiveIRQ_just_running_corres])
     apply (rule checkActiveIRQ_invs'_just_running[THEN hoare_weaken_pre])
     apply (fastforce simp: ex_abs_def)
    apply (fastforce simp: ex_abs_def ct_running_related sched_act_rct_related)
   apply (fastforce simp: ex_abs_def)

  apply (erule_tac P="a \<and> b" for a b in disjE)
   apply (clarsimp simp: check_active_irq_H_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
      apply (rule checkActiveIRQ_valid_duplicates')
     apply (rule valid_corres_combined[OF check_active_irq_invs_just_idle checkActiveIRQ_just_idle_corres])
     apply (rule checkActiveIRQ_invs'_just_idle[THEN hoare_weaken_pre])
     apply clarsimp
     apply (fastforce simp: ex_abs_def)
    apply (fastforce simp: ex_abs_def ct_idle_related sched_act_rct_related)
   apply (fastforce simp: ex_abs_def)

  apply (clarsimp simp: check_active_irq_H_def)
   apply (drule use_valid)
     apply (rule hoare_vcg_conj_lift)
     apply (rule checkActiveIRQ_valid_duplicates')
    apply (rule valid_corres_combined[OF check_active_irq_invs check_active_irq_corres])
    apply (rule checkActiveIRQ_invs'[THEN hoare_weaken_pre])
    apply clarsimp
     apply (fastforce simp: ex_abs_def)
   apply (fastforce simp: ex_abs_def ct_running_related ct_idle_related sched_act_rct_related)
  apply (fastforce simp: ex_abs_def)
  done

text \<open>The top-level theorem\<close>

lemma fw_sim_A_H:
  "LI (ADT_A uop)
      (ADT_H uop)
      (lift_state_relation state_relation)
      (full_invs \<times> full_invs')"
  apply (unfold LI_def full_invs_def full_invs'_def)
  apply (simp add: ADT_H_def ADT_A_def)
  apply (intro conjI)
    apply (rule init_refinement)
   apply (clarsimp simp: rel_semi_def relcomp_unfold in_lift_state_relation_eq)
   apply (rename_tac tc ak m ev tc' ck' m' ev' ck)
   apply (simp add: global_automaton_def)

   apply (erule_tac P="a \<and> (\<exists>x. b x)" for a b in disjE)
    apply (clarsimp simp add: kernel_call_H_def kernel_call_A_def)
    apply (rule rev_mp, rule_tac tc=tc and event=x in entry_corres)
    apply (clarsimp simp: corres_underlying_def)
    apply (drule (1) bspec)
    apply (clarsimp simp: sch_act_simple_def)
    apply (drule (1) bspec)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (rule_tac x=b in exI)
     apply (rule conjI)
      apply (rule impI, simp)
     apply (frule (2) ct_running_related)
    apply clarsimp
    apply (rule_tac x=b in exI)
    apply (drule use_valid, rule kernelEntry_invs')
     apply (simp add: sch_act_simple_def)
    apply clarsimp
    apply (frule (1) ct_idle_related)
    apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def)

   apply (erule_tac P="a \<and> b" for a b in disjE)
    apply (clarsimp simp: do_user_op_H_def do_user_op_A_def monad_to_transition_def)
    apply (rule rev_mp, rule_tac tc1=tc and f1=uop and P="ct_running and einvs" in corres_guard_imp2[OF do_user_op_corres])
     apply simp
    apply (clarsimp simp add: corres_underlying_def)
    apply (drule (1) bspec, clarsimp)
    apply (drule (1) bspec, clarsimp)
    apply fastforce

   apply (erule_tac P="a \<and> b \<and> c \<and> (\<exists>x. d x)" for a b c d in disjE)
    apply (clarsimp simp: do_user_op_H_def do_user_op_A_def monad_to_transition_def)
    apply (rule rev_mp, rule_tac tc1=tc and f1=uop and P="ct_running and einvs" in corres_guard_imp2[OF do_user_op_corres])
     apply simp
    apply (clarsimp simp add: corres_underlying_def)
    apply (drule (1) bspec, clarsimp)
    apply (drule (1) bspec, clarsimp)
    apply fastforce

   apply (erule_tac P="a \<and> b" for a b in disjE)
    apply (clarsimp simp: check_active_irq_H_def check_active_irq_A_def)
    apply (rule rev_mp, rule check_active_irq_corres)
    apply (clarsimp simp: corres_underlying_def)
    apply fastforce

   apply (erule_tac P="a \<and> b" for a b in disjE)
    apply (clarsimp simp: check_active_irq_H_def check_active_irq_A_def)
    apply (rule rev_mp, rule check_active_irq_corres)
    apply (clarsimp simp: corres_underlying_def)
    apply fastforce

   apply (clarsimp simp: check_active_irq_H_def check_active_irq_A_def)
   apply (rule rev_mp, rule check_active_irq_corres)
   apply (clarsimp simp: corres_underlying_def)
    apply fastforce

  apply (clarsimp simp: absKState_correct dest!: lift_state_relationD)
  done

theorem refinement:
  "ADT_H uop \<sqsubseteq> ADT_A uop"
  apply (rule sim_imp_refines)
  apply (rule L_invariantI)
    apply (rule akernel_invariant)
   apply (rule ckernel_invariant)
  apply (rule fw_sim_A_H)
  done

end

end
