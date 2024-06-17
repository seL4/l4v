(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
The main theorem
*)

theory AInvs
imports ArchAInvsPre
begin

lemma st_tcb_at_nostate_upd:
  "\<lbrakk> get_tcb t s = Some y; tcb_state y = tcb_state y' \<rbrakk> \<Longrightarrow>
  st_tcb_at P t' (s \<lparr>kheap := (kheap s)(t \<mapsto> TCB y')\<rparr>) = st_tcb_at P t' s"
  by (clarsimp simp add: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma pred_tcb_at_upd_apply:
  "pred_tcb_at proj P t (s\<lparr>kheap := p'\<rparr>) =
  pred_tcb_at proj P t (s\<lparr>kheap := (kheap s)(t := p' t)\<rparr>)"
  by (simp add: pred_tcb_at_def obj_at_def)


text \<open>The top-level invariance\<close>

lemma akernel_invs:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
  (call_kernel e) :: (unit,unit) s_monad
  \<lbrace>\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>"
  unfolding call_kernel_def
  by (wpsimp wp: activate_invs simp: active_from_running)

lemma akernel_invs_det_ext:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
  (call_kernel e) :: (unit,det_ext) s_monad
  \<lbrace>\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>"
  unfolding call_kernel_def
  by (wpsimp wp: activate_invs simp: active_from_running)

lemma kernel_entry_invs:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
  (kernel_entry e us) :: (user_context,unit) s_monad
  \<lbrace>\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>"
  apply (simp add: kernel_entry_def)
  apply (wp akernel_invs thread_set_invs_trivial thread_set_ct_in_state
         do_machine_op_ct_in_state hoare_weak_lift_imp hoare_vcg_disj_lift
      | clarsimp simp add: tcb_cap_cases_def)+
  done

lemma device_update_invs:
  "\<lbrace>invs and (\<lambda>s. (dom ds) \<subseteq>  (device_region s))\<rbrace> do_machine_op (device_memory_update ds)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: do_machine_op_def device_memory_update_def simpler_modify_def select_f_def
                   gets_def get_def bind_def valid_def return_def)
  apply (clarsimp simp: invs_def valid_state_def valid_irq_states_def valid_machine_state_def
                        cur_tcb_def pspace_respects_device_region_def cap_refs_respects_device_region_def
                  cong: user_mem_dom_cong
              simp del: split_paired_All)
  apply (clarsimp cong: device_mem_dom_cong simp:cap_range_respects_device_region_def
              simp del: split_paired_All split_paired_Ex)
  apply (intro conjI)
    apply fastforce
   apply fastforce
  apply (clarsimp simp del: split_paired_All split_paired_Ex)
  apply (drule_tac x = "(a,b)" in spec)
  apply (erule notE)
  apply (erule cte_wp_at_weakenE)
  apply clarsimp
  by (fastforce split: if_splits) (* takes 20 secs *)

crunch user_memory_update
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"

lemma dom_restrict_plus_eq:
  "a \<inter> b \<union> b = b"
  by auto

lemma user_memory_update[wp]:
  "\<lbrace>\<lambda>s. P (device_region s) \<rbrace> do_machine_op (user_memory_update a)
   \<lbrace>\<lambda>rv s. P (device_region s)\<rbrace>"
  by (simp add: do_machine_op_def user_memory_update_def simpler_modify_def
                valid_def bind_def gets_def return_def get_def select_f_def)


lemma do_user_op_invs:
  "\<lbrace>invs and ct_running\<rbrace>
   do_user_op f tc
   \<lbrace>\<lambda>_. invs and ct_running\<rbrace>"
  apply (simp add: do_user_op_def split_def)
  apply (wp device_update_invs)
  apply (wp do_machine_op_ct_in_state dmo_invs | simp add:dom_restrict_plus_eq)+
  apply (clarsimp simp: user_memory_update_def simpler_modify_def
                        restrict_map_def invs_def cur_tcb_def
                 split: option.splits if_split_asm)
  apply (frule ptable_rights_imp_frame)
     apply fastforce+
  apply (clarsimp simp: valid_state_def device_frame_in_device_region)
  done

end
