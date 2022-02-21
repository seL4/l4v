(*
 * Copyright 2022, ???
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchVCPU_AI
imports AInvs
begin

context Arch begin global_naming ARM_HYP (*FIXME: arch_split*)

definition active_cur_vcpu_of :: "'z::state_ext state \<Rightarrow> obj_ref option" where
  "active_cur_vcpu_of s \<equiv>
     case arm_current_vcpu (arch_state s) of Some (vr, True) \<Rightarrow> Some vr
                                           | _  \<Rightarrow> None"

abbreviation "arch_tcb_at \<equiv> pred_tcb_at itcb_arch"

definition cur_vcpu_valid :: "'z::state_ext state \<Rightarrow> bool" where
  "cur_vcpu_valid s \<equiv> arch_tcb_at (\<lambda>a. itcb_vcpu a = active_cur_vcpu_of s) (cur_thread s) s"

lemma cur_vcpu_valid_lift:
  assumes active_cur_vcpu_of: "\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  and arch_tcb_of_cur_thread: "\<And>P. f \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  shows "f \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: cur_vcpu_valid_def valid_def)
  using use_valid[OF _ active_cur_vcpu_of] use_valid[OF _ arch_tcb_of_cur_thread]
  by (fastforce simp: active_cur_vcpu_of_def)

lemma cur_vcpu_valid_lift_weak:
  assumes arch_state: "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  and arch_tcb_of_cur_thread: "\<And>P. f \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  shows "f \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (rule cur_vcpu_valid_lift)
   apply (clarsimp simp: valid_def)
   using use_valid[OF _ arch_state] apply (fastforce simp: active_cur_vcpu_of_def)
  apply (fastforce simp: arch_tcb_of_cur_thread)
  done

lemma cur_vcpu_valid_lift_cur_thread_update:
  assumes arch_state: "\<And>P. f \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  and arch_tcb_of_cur_thread: "\<And>P. f \<lbrace>\<lambda>s. arch_tcb_at P t s\<rbrace>"
  shows "f \<lbrace>\<lambda>s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: cur_vcpu_valid_def valid_def)
  using use_valid[OF _ arch_state] use_valid[OF _ arch_tcb_of_cur_thread]
  by (fastforce simp: active_cur_vcpu_of_def)

lemma as_user_cur_vcpu_valid[wp]:
  "as_user tptr f \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: as_user_def active_cur_vcpu_of_def)
  apply (rule cur_vcpu_valid_lift)
   apply (wpsimp wp: select_f_wp set_object_wp)
   apply (fastforce simp: active_cur_vcpu_of_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma machine_state_update_active_cur_vcpu_of[simp]:
  "P (active_cur_vcpu_of (s\<lparr>machine_state := ms\<rparr>)) = P (active_cur_vcpu_of s)"
  by (fastforce simp: active_cur_vcpu_of_def)

crunches do_machine_op
  for cur_vcpu_valid_cur_thread_update[wp]: "\<lambda>s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)"
  and cur_vcpu_valid[wp]: "\<lambda>s. cur_vcpu_valid s"
  (wp: cur_vcpu_valid_lift_cur_thread_update cur_vcpu_valid_lift crunch_wps)

lemma vcpu_save_reg_cur_vcpu_valid[wp]:
  "vcpu_save_reg vr reg \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: vcpu_save_reg_def vcpu_update_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
  done

lemma vcpu_write_reg_cur_vcpu_valid[wp]:
  "vcpu_write_reg vr reg val \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: vcpu_write_reg_def vcpu_update_def)
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
  done

lemma save_virt_timer_cur_vcpu_valid[wp]:
  "save_virt_timer vcpu_timer \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: save_virt_timer_def vcpu_update_def)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
  done

lemma vgic_update_cur_vcpu_valid[wp]:
  "vgic_update vr f \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: vgic_update_def vcpu_update_def)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
  done

lemma vcpu_disable_cur_vcpu_valid[wp]:
  "vcpu_disable vo \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: vcpu_disable_def)
  apply (rule hoare_seq_ext_skip, wpsimp)+
  apply wpsimp
  done

crunches do_machine_op
  for arch_tcb_at_cur_thread[wp]: "\<lambda>s. arch_tcb_at P (cur_thread s) s"
  (wp: cur_vcpu_valid_lift crunch_wps simp: active_cur_vcpu_of_def simp: crunch_simps)

lemma set_vcpu_arch_tcb_at_cur_thread[wp]:
  "set_vcpu ptr vcpu \<lbrace>\<lambda>s. arch_tcb_at P (cur_thread s) s\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp get_vcpu_wp)
  apply (clarsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def pred_tcb_at_def obj_at_def)
  done

crunches vcpu_disable, vcpu_restore, vcpu_save_reg_range, vgic_update_lr, vcpu_save, set_vm_root
  for arch_tcb_at_cur_thread[wp]: "\<lambda>s. arch_tcb_at P (cur_thread s) s"
  (wp: crunch_wps simp: active_cur_vcpu_of_def simp: crunch_simps active_cur_vcpu_of_def)

crunches vcpu_update, do_machine_op, invalidate_hw_asid_entry, invalidate_asid
  for active_cur_vcpu_of[wp]: "\<lambda>s. P (active_cur_vcpu_of s)"
  (wp: crunch_wps simp: active_cur_vcpu_of_def simp: crunch_simps active_cur_vcpu_of_def)

crunches vcpu_restore, do_machine_op, vcpu_save_reg, vgic_update, save_virt_timer
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift crunch_wps mapM_x_wp_inv simp: active_cur_vcpu_of_def crunch_simps)

lemma vcpu_save_reg_active_cur_vcpu_of[wp]:
  "vcpu_save_reg a b \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: vcpu_save_reg_def)

crunches vcpu_save_reg_range, vcpu_save_reg_range, vgic_update_lr, vcpu_enable, vcpu_save
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (wp: cur_vcpu_valid_lift crunch_wps mapM_x_wp_inv simp: active_cur_vcpu_of_def crunch_simps)

lemma switch_vcpu_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. arch_tcb_at (\<lambda>a. itcb_vcpu a = v) t s\<rbrace>
   vcpu_switch v
   \<lbrace>\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: vcpu_switch_def)
  apply (cases v; clarsimp)
   apply (rule hoare_seq_ext[OF _ gets_sp], rename_tac cur_vcpu)
   apply (case_tac cur_vcpu; clarsimp)
    apply (wpsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def)
   apply (clarsimp simp: when_def)
   apply (intro conjI impI)
    apply (rule hoare_seq_ext_skip, wpsimp)
    apply (wpsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def)
   apply (wpsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def)
  apply (rule hoare_seq_ext[OF _ gets_sp], rename_tac cur_vcpu)
  apply (case_tac cur_vcpu; clarsimp)
   apply (rule hoare_seq_ext_skip, wpsimp)
   apply (wpsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def)
  apply (intro conjI impI)
   apply (rule hoare_seq_ext_skip, solves wpsimp)+
   apply (wpsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def)
  apply (clarsimp simp: when_def)
  apply (intro conjI impI)
   apply (rule hoare_seq_ext_skip, solves wpsimp)+
   apply (wpsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def)
  apply (wpsimp simp: cur_vcpu_valid_def active_cur_vcpu_of_def)
  done

lemma store_hw_asid_active_cur_vcpu_of[wp]:
  "store_hw_asid pd asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: store_hw_asid_def find_pd_for_asid_assert_def active_cur_vcpu_of_def)

lemma find_free_hw_asid_active_cur_vcpu_of[wp]:
  "find_free_hw_asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  apply (clarsimp simp: find_free_hw_asid_def find_pd_for_asid_assert_def)
  apply (intro hoare_seq_ext[OF _ gets_inv])
  apply (clarsimp split: option.splits)
  apply (rule hoare_seq_ext_skip, wpsimp)+
   apply (clarsimp simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def)
  apply (wpsimp simp: find_pd_for_asid_assert_def)
  done

lemma arm_context_switch_active_cur_vcpu_of[wp]:
  "arm_context_switch pd asid \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  apply (clarsimp simp: arm_context_switch_def get_hw_asid_def)
  apply (wpsimp wp: load_hw_asid_wp)
  done

lemma set_vm_root_active_cur_vcpu_of[wp]:
  "set_vm_root tcb \<lbrace>\<lambda>s. P (active_cur_vcpu_of s)\<rbrace>"
  by (wpsimp simp: set_vm_root_def find_pd_for_asid_def find_pd_for_asid_def
               wp: get_cap_wp)

crunches set_vm_root
  for cur_vcpu_valid[wp]: "\<lambda>s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)"
  (wp: cur_vcpu_valid_lift_cur_thread_update crunch_wps mapM_x_wp_inv
   simp: active_cur_vcpu_of_def crunch_simps)

lemma arch_switch_to_thread_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s\<rbrace>
   arch_switch_to_thread t
   \<lbrace>\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: arch_switch_to_thread_def)
  apply (rule hoare_seq_ext[OF _ gets_the_sp])
  apply wpsimp
  by (fastforce simp: active_cur_vcpu_of_def pred_tcb_at_def obj_at_def cur_vcpu_valid_def get_tcb_def
               split: option.splits kernel_object.splits)

lemma switch_to_thread_cur_vcpu_valid[wp]:
  "switch_to_thread t \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: switch_to_thread_def)
  apply (rule hoare_seq_ext[OF _ get_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (subst bind_assoc[symmetric])
  apply (wp modify_wp)
    apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def active_cur_vcpu_of_def)
   apply wpsimp
  apply (wpsimp simp: cur_vcpu_valid_def)
  done

lemma arch_switch_to_idle_thread_cur_vcpu_valid[wp]:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> valid_idle s \<and> t = idle_thread s\<rbrace>
   arch_switch_to_idle_thread
   \<lbrace>\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>)\<rbrace>"
  apply (clarsimp simp: arch_switch_to_idle_thread_def)
  apply wpsimp
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def valid_arch_idle_def)
  done

lemma switch_to_idle_thread_cur_vcpu_valid[wp]:
  "\<lbrace>cur_vcpu_valid and valid_idle\<rbrace>
   switch_to_idle_thread
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  by (wpsimp simp: switch_to_idle_thread_def)

\<comment> \<open>A variant which works nicely with subgoals that do not contain schematics\<close>
lemmas hoare_vcg_conj_lift_pre_fix
  = hoare_vcg_conj_lift[where P=R and P'=R for R, simplified]

lemma dissociate_vcpu_ccb_cur_vcpu_valid:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   dissociate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: dissociate_vcpu_tcb_def)
  apply (clarsimp simp: arch_thread_get_def)
  apply (rule hoare_seq_ext[OF _ gets_the_sp])
  apply (clarsimp simp: get_vcpu_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (simp flip: bind_assoc)
  apply (rule hoare_seq_ext)
   apply wpsimp
  apply (simp add: bind_assoc)
  apply (clarsimp simp: when_def)
  apply (intro conjI impI)
   prefer 2
   apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
   apply (fastforce simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
                          get_tcb_def
                   split: if_splits option.splits bool.splits)
  apply (clarsimp simp: vcpu_invalidate_active_def bind_assoc)
  apply (rule hoare_seq_ext[OF _ gets_sp], rename_tac cur_vcpu)
  apply (case_tac cur_vcpu; clarsimp)
   apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
  apply (rename_tac active)
  apply (case_tac active; clarsimp)
   prefer 2
   apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
   apply (fastforce simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
                   split: if_splits)
  apply (rule_tac B="\<lambda>_ s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)
                           \<and> arch_tcb_at (\<lambda>itcb. itcb_vcpu itcb = Some vr) t s
                           \<and> arm_current_vcpu (arch_state s) = Some (vr, True)"
               in hoare_seq_ext[rotated])
   apply (clarsimp simp: pred_conj_def)
   apply (intro hoare_vcg_conj_lift_pre_fix; (solves wpsimp)?)
   apply wpsimp
   apply (fastforce simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def get_tcb_def
                   split: kernel_object.splits option.splits)
  apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
  apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def
                 split: if_splits kernel_object.splits option.splits)
  apply (prop_tac "(t, HypTCBRef) \<in> hyp_refs_of (ArchObj (VCPU v))")
   apply (clarsimp simp: sym_refs_def state_hyp_refs_of_def)
   apply (fastforce split: option.splits)
  apply (fastforce simp: sym_refs_def state_hyp_refs_of_def vcpu_tcb_refs_def
                  split: option.splits)
  done

lemma associate_vcpu_tcb_cur_vcpu_valid:
  "\<lbrace>\<lambda>s. cur_vcpu_valid s \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
   associate_vcpu_tcb vr t
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (clarsimp simp: associate_vcpu_tcb_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip)
   apply (wpsimp wp: dissociate_vcpu_ccb_cur_vcpu_valid)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext_skip)
   apply (wpsimp wp: dissociate_vcpu_ccb_cur_vcpu_valid)
  apply (rule_tac P="\<lambda>s. t \<noteq> cur_thread s" in hoare_pre_tautI)
   apply (subst bind_assoc[symmetric])
   apply (rule_tac B="\<lambda>_ s. cur_vcpu_valid s \<and> t \<noteq> cur_thread s" in hoare_seq_ext[rotated])
    apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
    apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def active_cur_vcpu_of_def)
   apply (rule hoare_seq_ext[OF _ gets_sp])
   apply (clarsimp simp: when_def)
   apply (intro conjI impI)
    apply (fastforce intro: hoare_weaken_pre hoare_pre_cont)
   apply wpsimp
  apply (rule_tac Q="\<lambda>_ s. cur_vcpu_valid (s\<lparr>cur_thread := t\<rparr>) \<and> t = cur_thread s" in hoare_post_imp)
   apply fastforce
  apply (wpsimp wp: arch_thread_set_wp set_vcpu_wp)
  apply (clarsimp simp: cur_vcpu_valid_def pred_tcb_at_def obj_at_def)
  done

lemma set_thread_state_cur_vcpu_valid[wp]:
  "set_thread_state ref ts \<lbrace>cur_vcpu_valid\<rbrace>"
  apply (rule cur_vcpu_valid_lift_weak)
   apply wpsimp
  apply (clarsimp simp: set_thread_state_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma activate_thread_cur_vcpu_valid[wp]:
  "activate_thread \<lbrace>cur_vcpu_valid\<rbrace>"
  unfolding activate_thread_def arch_activate_idle_thread_def
  by (wpsimp wp: gts_wp)

crunches tcb_sched_action
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (simp: cur_vcpu_valid_def active_cur_vcpu_of_def tcb_sched_action_def set_tcb_queue_def
         get_tcb_queue_def)

crunches schedule_choose_new_thread
  for cur_vcpu_valid[wp]: cur_vcpu_valid
  (simp: crunch_simps cur_vcpu_valid_def active_cur_vcpu_of_def wp: crunch_wps)

lemma schedule_cur_vcpu_valid_det_ext[wp]:
  "\<lbrace>cur_vcpu_valid and valid_idle\<rbrace>
   (schedule :: (unit,det_ext) s_monad)
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (simp add: Schedule_A.schedule_def schedule_switch_thread_fastfail_def ethread_get_when_def
                   ethread_get_def)
  by (wpsimp wp: hoare_drop_imps gts_wp )

lemma schedule_cur_vcpu_valid[wp]:
  "\<lbrace>cur_vcpu_valid and valid_idle\<rbrace>
   (schedule :: (unit,unit) s_monad)
   \<lbrace>\<lambda>_. cur_vcpu_valid\<rbrace>"
  apply (simp add: Schedule_A.schedule_def allActiveTCBs_def)
  by (wpsimp wp: alternative_wp  select_wp)

end

end