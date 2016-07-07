(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
The main theorem
*)

theory AInvs
imports "./$L4V_ARCH/ArchAInvsPre"
begin

lemma st_tcb_at_nostate_upd:
  "\<lbrakk> get_tcb t s = Some y; tcb_state y = tcb_state y' \<rbrakk> \<Longrightarrow>
  st_tcb_at P t' (s \<lparr>kheap := kheap s(t \<mapsto> TCB y')\<rparr>) = st_tcb_at P t' s"
  by (clarsimp simp add: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma pred_tcb_at_upd_apply:
  "pred_tcb_at proj P t (s\<lparr>kheap := p'\<rparr>) =
  pred_tcb_at proj P t (s\<lparr>kheap := (kheap s)(t := p' t)\<rparr>)"
  by (simp add: pred_tcb_at_def obj_at_def)

text {* The top-level invariance *}

lemma akernel_invs:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
  (call_kernel e) :: (unit,unit) s_monad
  \<lbrace>\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>"
  apply wp
   apply (simp add: call_kernel_def)
   apply (wp activate_invs | simp)+
   apply (auto simp: active_from_running)
  done

lemma akernel_invs_det_ext:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
  (call_kernel e) :: (unit,det_ext) s_monad
  \<lbrace>\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>"
  apply wp
   apply (simp add: call_kernel_def)
   apply (wp activate_invs | simp)+
   apply (auto simp: active_from_running)
  done

(* FIXME: move *)
lemma ct_running_machine_op:
  "\<lbrace>ct_running\<rbrace> do_machine_op f \<lbrace>\<lambda>_. ct_running\<rbrace>"
  apply (simp add: ct_in_state_def pred_tcb_at_def obj_at_def)
  apply (rule hoare_lift_Pf [where f=cur_thread])
  by wp

lemma kernel_entry_invs:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s)\<rbrace>
  (kernel_entry e us) :: (register \<Rightarrow> 32 word,unit) s_monad
  \<lbrace>\<lambda>rv. invs and (\<lambda>s. ct_running s \<or> ct_idle s)\<rbrace>"
  apply (simp add: kernel_entry_def)
  by (wp akernel_invs thread_set_invs_trivial thread_set_ct_running select_wp
         ct_running_machine_op static_imp_wp
      | clarsimp simp add: tcb_cap_cases_def)+

(* FIXME: move to Lib.thy *)
lemma Collect_subseteq:
  "{x. P x} <= {x. Q x} \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q x)"
  by auto

lemma do_user_op_invs:
  "\<lbrace>invs and ct_running\<rbrace>
   do_user_op f tc
   \<lbrace>\<lambda>_. invs and ct_running\<rbrace>"
  apply (simp add: do_user_op_def split_def)
  apply (wp ct_running_machine_op select_wp dmo_invs)
  apply (auto simp: user_mem_def user_memory_update_def simpler_modify_def
                    restrict_map_def invs_def cur_tcb_def
             elim!: ptable_rights_imp_user_frame
             split: option.splits split_if_asm)
  done

end
