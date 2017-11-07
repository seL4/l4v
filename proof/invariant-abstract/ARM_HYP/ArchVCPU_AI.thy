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

theory ArchVCPU_AI
imports "AInvs"
begin

text {* The top-level invariance *}

definition "cur_vcpu_to_tcb_vcpu cur_vcpu = 
  (case cur_vcpu of
   Some (vcpu, True) \<Rightarrow> Some vcpu
  | _ \<Rightarrow> None)"

lemma get_tcb_ex_invs:
  "invs s \<Longrightarrow> \<exists>tcb. get_tcb (cur_thread s) s = Some tcb"
 by (drule tcb_at_invs, simp add: tcb_at_def)

definition
  arch_vcpu_tcb_valid :: "'z::state_ext state \<Rightarrow> bool" where  
  "arch_vcpu_tcb_valid  s \<equiv>
    ARM_A.tcb_vcpu (tcb_arch (the (get_tcb (cur_thread s) s))) = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu (arch_state s))"

lemma arch_vcpu_tcb_valid_trans_st[simp]:
 "arch_vcpu_tcb_valid (trans_state f s) = arch_vcpu_tcb_valid s"
 by (simp add: trans_state_def arch_vcpu_tcb_valid_def get_tcb_def)

lemma arch_vcpu_tcb_valid_set_obj_not_cur_thread:
  "\<lbrace>arch_vcpu_tcb_valid and (op \<noteq> addr) o cur_thread\<rbrace> set_object addr obj \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  unfolding set_object_def 
  apply wpsimp
  unfolding arch_vcpu_tcb_valid_def get_tcb_def
  apply simp
  done

lemma arch_vcpu_tcb_valid_set_obj_cur_thread:
  "\<lbrace>invs and arch_vcpu_tcb_valid and (op = addr) o cur_thread and (\<lambda>_. is_tcb obj) 
    and (\<lambda>s. ARM_A.tcb_vcpu (tcb_arch (case obj of TCB tcb \<Rightarrow> tcb)) = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu (arch_state s)))
    \<rbrace> set_object addr obj \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  unfolding set_object_def 
  apply wpsimp
  unfolding arch_vcpu_tcb_valid_def get_tcb_def
  apply (case_tac obj; clarsimp simp: is_tcb_def)
  done

lemma
 "\<lbrace>invs and arch_vcpu_tcb_valid\<rbrace> activate_thread \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
unfolding activate_thread_def 
 apply wpsimp
unfolding set_thread_state_def 
 apply (wpsimp wp: arch_vcpu_tcb_valid_set_obj_cur_thread)
unfolding as_user_def
 apply (wpsimp wp: arch_vcpu_tcb_valid_set_obj_cur_thread)
oops

lemma schedule_invs:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid \<rbrace>
  (schedule) :: (unit,unit) s_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding schedule_def 
using activate_invs
oops
(*
crunch blah[wp]: call_kernel arch_vcpu_tcb_valid
 (simp: get_tcb_ex_invs arch_vcpu_tcb_valid_def)
*)
theorem akernel_arch_vcpu_tcb_valid_inv:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid \<rbrace>
  (call_kernel e) :: (unit,unit) s_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding call_kernel_def arch_vcpu_tcb_valid_def
  apply (wpsimp wp: activate_invs simp: active_from_running get_tcb_ex_invs)
oops

end
