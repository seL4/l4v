(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchSchedule_AI
imports "../Schedule_AI"
begin

context Arch begin global_naming ARM

named_theorems Schedule_AI_asms

lemma dmo_mapM_storeWord_0_invs[wp,Schedule_AI_asms]:
  "valid invs (do_machine_op (mapM (\<lambda>p. storeWord p 0) S)) (\<lambda>_. invs)"
  apply (simp add: dom_mapM ef_storeWord)
  apply (rule mapM_UNIV_wp)
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def cur_tcb_def
                        valid_machine_state_def)
  apply (rule conjI)
   apply(erule use_valid[OF _ storeWord_valid_irq_states], simp)
  apply (erule use_valid)
   apply (simp add: storeWord_def word_rsplit_0)
   apply wp
  apply simp
  done

global_naming ARM (*FIXME: arch_split*)
lemma set_vm_root_kheap_arch_state[wp]:
  "\<lbrace>\<lambda>s. P (kheap s) (arm_globals_frame (arch_state s))\<rbrace> set_vm_root a
   \<lbrace>\<lambda>_ s. P (kheap s) (arm_globals_frame (arch_state s))\<rbrace>" (is "valid ?P _ _")
  apply (simp add: set_vm_root_def arm_context_switch_def)
  apply (wp | wpcw | simp add: arm_context_switch_def get_hw_asid_def
           store_hw_asid_def find_pd_for_asid_assert_def find_free_hw_asid_def
           invalidate_hw_asid_entry_def invalidate_asid_def load_hw_asid_def)+
     apply (simp add: whenE_def, intro conjI impI)
      apply (wp, simp add: returnOk_def validE_E_def validE_def)+
    apply (simp add: whenE_def, intro conjI[rotated] impI)
     apply (wp | simp add: returnOk_def validE_E_def validE_def)+
    apply (wp | simp add: throwError_def validE_R_def validE_def)+
done  
  
lemma clearExMonitor_invs [wp]:
  "\<lbrace>invs\<rbrace> do_machine_op clearExMonitor \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply (clarsimp simp: clearExMonitor_def machine_op_lift_def
                        machine_rest_lift_def in_monad select_f_def)
  done
  
global_naming Arch  

lemma arch_stt_invs [wp,Schedule_AI_asms]:
  "\<lbrace>invs\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply wp
  apply (simp add: in_user_frame_def obj_at_def)
  apply (wp hoare_vcg_ex_lift)
  apply (rule_tac x=ARMSmallPage in exI)
  apply (clarsimp simp add: invs_def valid_state_def valid_arch_state_def
           valid_pspace_def pspace_aligned_def obj_at_def dom_def)
  apply (drule spec, erule impE, fastforce)
  apply (clarsimp simp: is_aligned_neg_mask_eq a_type_simps)
  done  

lemma arch_stt_tcb [wp,Schedule_AI_asms]:
  "\<lbrace>tcb_at t'\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. tcb_at t'\<rbrace>"
  apply (simp add: arch_switch_to_thread_def) 
  apply (wp)
  done
  
lemma arch_stt_runnable[Schedule_AI_asms]:
  "\<lbrace>st_tcb_at runnable t\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>r . st_tcb_at runnable t\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply wp
  done  
  
lemma stit_invs [wp,Schedule_AI_asms]:
  "\<lbrace>invs\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply wp
    apply (rule invs_upd_cur_valid)
     apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_idle_def pred_tcb_at_tcb_at)
  apply (clarsimp simp: in_user_frame_def valid_arch_state_def)
  apply (rule_tac x=ARMSmallPage in exI)
  apply (clarsimp simp: obj_at_def)
  apply (drule_tac addr="arm_globals_frame (arch_state s)" in valid_pspace_aligned, simp)
  apply (drule is_aligned_neg_mask_eq, simp add: a_type_def)
  done
  
lemma stit_activatable[Schedule_AI_asms]:
  "\<lbrace>invs\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply (wp | simp add: ct_in_state_def)+
  apply (clarsimp simp: invs_def valid_state_def cur_tcb_def valid_idle_def
                 elim!: pred_tcb_weaken_strongerE)
  done  
  
lemma stt_invs [wp,Schedule_AI_asms]:
  "\<lbrace>invs\<rbrace> switch_to_thread t' \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply wp
     apply (simp add: trans_state_update[symmetric] del: trans_state_update)
    apply (rule_tac Q="\<lambda>_. invs and tcb_at t'" in hoare_strengthen_post, wp)
    apply (clarsimp simp: invs_def valid_state_def valid_idle_def
                          valid_irq_node_def valid_machine_state_def)
    apply (fastforce simp: cur_tcb_def obj_at_def
                     elim: valid_pspace_eqI ifunsafe_pspaceI)
   apply wp
  apply clarsimp
  apply (simp add: is_tcb_def)
  done
end

interpretation Schedule_AI_U?: Schedule_AI_U
  proof goal_cases
  interpret Arch .
  case 1 show ?case 
  by (intro_locales; (unfold_locales; fact Schedule_AI_asms)?) 
  qed

interpretation Schedule_AI?: Schedule_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case 
  by (intro_locales; (unfold_locales; fact Schedule_AI_asms)?) 
  qed

end