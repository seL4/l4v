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
imports AInvs.ArchDetSchedSchedule_AI
begin

(* FIXME MOVE *)
lemma is_tcb_TCB[simp]:
  "is_tcb (TCB x)"
 by (simp add: is_tcb_def)

context Arch begin global_naming ARM_A

text {* The top-level invariance *}

definition
  "cur_vcpu_to_tcb_vcpu cur_vcpu =
    (case cur_vcpu of
       Some (vcpu, True) \<Rightarrow> Some vcpu
    | _ \<Rightarrow> None)"

(*

lemma get_tcb_ex_invs:
  "invs s \<Longrightarrow> \<exists>tcb. get_tcb (cur_thread s) s = Some tcb"
 by (drule tcb_at_invs, simp add: tcb_at_def)

lemmas cur_tcb_tcb = cur_tcb_def[simplified atomize_eq, THEN iffD1, THEN tcb_at_ko_at]

definition
  arch_vcpu_tcb_valid :: "'z::state_ext state \<Rightarrow> bool" where
  "arch_vcpu_tcb_valid  s \<equiv>
    ARM_A.tcb_vcpu (tcb_arch (the (get_tcb (cur_thread s) s)))
       = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu (arch_state s))"

lemma "\<forall>tcb. ko_at (TCB tcb) (cur_thread s) \<longrightarrow> P tcb

 obj_at (\<lambda>obj. \<exists>t. obj = TCB t \<longrightarrow>
                       ARM_A.tcb_vcpu (tcb_arch t) = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu (arch_state s))
                      ) (cur_thread s) s"


lemma "obj_at (\<lambda>obj. \<exists>t. obj = TCB t \<longrightarrow>
                       ARM_A.tcb_vcpu (tcb_arch t) = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu (arch_state s))
                      ) (cur_thread s) s"
*)
definition
  arch_vcpu_tcb_valid_obj :: "arch_state \<Rightarrow> kernel_object \<Rightarrow> bool" where
  "arch_vcpu_tcb_valid_obj as obj \<equiv>
     \<forall>t. obj = TCB t \<longrightarrow>
           ARM_A.tcb_vcpu (tcb_arch t) = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu as)"


definition
  arch_vcpu_tcb_valid :: "'z::state_ext state \<Rightarrow> bool" where
  "arch_vcpu_tcb_valid s \<equiv>
    obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) (cur_thread s) s"

lemmas arch_vcpu_tcb_valid_kheap_unfold =
         arch_vcpu_tcb_valid_def
         arch_vcpu_tcb_valid_obj_def
         obj_at_def
         get_tcb_ko_at

lemma arch_vcpu_tcb_valid_trans_st[simp]:
 "arch_vcpu_tcb_valid (trans_state f s) = arch_vcpu_tcb_valid s"
 "arch_vcpu_tcb_valid (trans_state f s\<lparr>cur_thread := cur\<rparr>) = arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)"
 by (simp add: trans_state_def arch_vcpu_tcb_valid_def obj_at_def cur_tcb_def)+

lemma arch_vcpu_tcb_validE:
  "\<lbrakk> arch_vcpu_tcb_valid s ;
     arch_state s = arch_state t ;
     kheap s (cur_thread s) = kheap t (cur_thread t) \<rbrakk>
   \<Longrightarrow> arch_vcpu_tcb_valid t"
  apply (clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def cur_tcb_def)
 done

lemma lift_arch_vcpu_tcb_valid:
  "\<lbrakk> \<And>P. \<lbrace>\<lambda>s.  P (kheap s (cur_thread s)) \<rbrace> f \<lbrace>\<lambda>_ s.  P (kheap s (cur_thread s))\<rbrace>;
     \<And>Q. \<lbrace>\<lambda>s.  Q (arch_state s) \<rbrace> f \<lbrace>\<lambda>_ s.  Q (arch_state s)\<rbrace> \<rbrakk>
 \<Longrightarrow> \<lbrace>arch_vcpu_tcb_valid \<rbrace> f \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  apply (unfold valid_def)
  apply clarsimp
  apply (erule arch_vcpu_tcb_validE)
   apply (drule_tac x="op = (arch_state s)" in meta_spec)
   apply fastforce
  apply (drule_tac x="op = (kheap s (cur_thread s))" in meta_spec)
  apply fastforce
 done


lemma set_object_not_cur_thread_arch_vcpu_tcb_valid:
  "\<lbrace>arch_vcpu_tcb_valid and (op \<noteq> addr) \<circ> cur_thread\<rbrace> set_object addr obj \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: set_object_def arch_vcpu_tcb_valid_def)
  apply (clarsimp simp: cur_tcb_def obj_at_def)
  done

lemma set_object_cur_thread_arch_vcpu_tcb_valid:
  "\<lbrace>arch_vcpu_tcb_valid and (op = addr) \<circ> cur_thread and (\<lambda>_. is_tcb obj)
    and (\<lambda>s. ARM_A.tcb_vcpu (tcb_arch (case obj of TCB tcb \<Rightarrow> tcb))
               = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu (arch_state s)))
    \<rbrace> set_object addr obj \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: set_object_def arch_vcpu_tcb_valid_def)
  apply (clarsimp simp: cur_tcb_def obj_at_def arch_vcpu_tcb_valid_obj_def)
  done

lemmas set_object_arch_vcpu_tcb_valid =
         hoare_pre_disj[OF set_object_not_cur_thread_arch_vcpu_tcb_valid
                           set_object_cur_thread_arch_vcpu_tcb_valid]
(*
thm  ArchVCPU_AI.as_user_arch_vcpu
 crunch arch_vcpu[wp]:  as_user "arch_vcpu_tcb_valid"
  (ignore:
   wp: set_object_arch_vcpu_tcb_valid
   simp: obj_at_def  arch_vcpu_tcb_valid_def ARM_A.arch_tcb_context_set_def
   is_tcb_def get_tcb_def)
thm  ArchVCPU_AI.as_user_arch_vcpu
*)

lemma as_user_arch_vcpu_tcb_valid[wp]:
  "\<lbrace>arch_vcpu_tcb_valid \<rbrace> as_user tcb_ptr f \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_arch_vcpu_tcb_valid)
  apply (clarsimp simp:  arch_vcpu_tcb_valid_kheap_unfold arch_tcb_context_set_def)
  done

lemma set_thread_state_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>arch_vcpu_tcb_valid\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  unfolding set_thread_state_def
  apply (wpsimp wp: set_object_arch_vcpu_tcb_valid dxo_wp_weak)
  apply (clarsimp simp: arch_vcpu_tcb_valid_kheap_unfold)
  done

lemma activate_thread_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>arch_vcpu_tcb_valid\<rbrace> activate_thread \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding activate_thread_def
  by (wpsimp wp: gts_wp simp: ARM_A.arch_activate_idle_thread_def)

lemma do_machine_op_arch_vcpu_tcb_valid[wp]:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid (g s) \<rbrace> do_machine_op f \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid (g s)\<rbrace>"
 unfolding do_machine_op_def
 apply wpsimp
 apply (clarsimp simp add: cur_tcb_def obj_at_def arch_vcpu_tcb_valid_def)
apply (rule_tac x=ko in exI)

sorry

lemma vcpu_switch_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)\<rbrace>
   vcpu_switch (ARM_A.tcb_vcpu (tcb_arch xd))
  \<lbrace>\<lambda>xa s. arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)\<rbrace>"
  apply (clarsimp simp add: vcpu_switch_def split: option.splits)
  apply (rule conjI; clarsimp)
  apply (wpsimp simp: ARM_A.vcpu_disable_def)
sorry

lemma blah:
  "tcb_at cur s \<Longrightarrow> arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>) \<Longrightarrow> (\<exists>y. get_tcb cur s = Some y) "
 apply (clarsimp simp add: arch_vcpu_tcb_valid_kheap_unfold is_tcb_def )
 apply (clarsimp split: kernel_object.splits)
 done

lemma
 "\<lbrace>\<lambda>s. (\<exists>y. get_tcb cur s = Some y) \<longrightarrow> arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)\<rbrace>
  arm_context_switch x51 x2
  \<lbrace>\<lambda>xa s. (\<exists>y. get_tcb cur s = Some y) \<longrightarrow> arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)\<rbrace>"
  unfolding arm_context_switch_def
  apply wpsimp
 oops

lemma set_vm_root_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid_obj (arch_state s) obj \<and> ko_at obj cur s \<rbrace>
     set_vm_root cur
   \<lbrace>\<lambda>x s. arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)\<rbrace>"
 unfolding set_vm_root_def
 apply_trace (wpsimp wp: vcpu_switch_arch_vcpu_tcb_valid)
oops

lemma arch_switch_to_thread_arch_vcpu_tcb_valid_obj:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid_obj (arch_state s) obj \<and> ko_at obj cur s \<rbrace>
      arch_switch_to_thread cur
   \<lbrace>\<lambda>a s. arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)\<rbrace>"
 unfolding arch_switch_to_thread_def
 apply wpsimp
 sorry

lemma switch_to_thread_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace> switch_to_thread cur \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
 unfolding switch_to_thread_def
 apply wpsimp
 apply (wpsimp wp: dxo_wp_weak assert_wp get_wp arch_switch_to_thread_arch_vcpu_tcb_valid_obj)
 sorry

lemma switch_to_idle_thread_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
sorry

lemma schedule_arch_vcpu_tcb_valid:
  "\<lbrace>(\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid \<rbrace>
  (schedule) :: (unit, unit) s_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding schedule_def
  apply (wpsimp wp: alternative_wp dxo_wp_weak assert_wp switch_to_thread_arch_vcpu_tcb_valid )
  apply (rule lift_arch_vcpu_tcb_valid; wpsimp wp: select_wp)
  apply (rule lift_arch_vcpu_tcb_valid; wpsimp wp: gets_wp simp: allActiveTCBs_gets)
  apply (wpsimp wp: gets_wp)
  apply (wpsimp wp: alternative_wp gets_wp switch_to_idle_thread_arch_vcpu_tcb_valid return_wp)
  apply (wpsimp wp: )
done
(*
crunch blah[wp]: call_kernel arch_vcpu_tcb_valid
 (simp: get_tcb_ex_invs arch_vcpu_tcb_valid_def)
*)
theorem akernel_arch_vcpu_tcb_valid_inv:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid \<rbrace>
  (call_kernel e) :: (unit,unit) s_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding call_kernel_def
  apply (wpsimp wp: schedule_arch_vcpu_tcb_valid activate_invs simp: active_from_running )
oops

end
