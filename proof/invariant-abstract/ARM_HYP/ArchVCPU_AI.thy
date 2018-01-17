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

lemma do_machine_op_arch_vcpu_tcb_valid_imp:
  "(\<And>s x. arch_state (g (s\<lparr>machine_state := x\<rparr>)) = arch_state (g s)) \<Longrightarrow> 
   (\<And>s x. cur_thread (g (s\<lparr>machine_state := x\<rparr>)) = cur_thread (g s)) \<Longrightarrow> 
   (\<And>s x. kheap (g (s\<lparr>machine_state := x\<rparr>)) (cur_thread (g s)) = kheap (g s) (cur_thread (g s))) \<Longrightarrow>
   (\<And>s x. P (s\<lparr>machine_state := x\<rparr>) = P s) \<Longrightarrow>
  \<lbrace>\<lambda>s. P s \<longrightarrow> arch_vcpu_tcb_valid (g s) \<rbrace> do_machine_op f \<lbrace>\<lambda>_ s. P s \<longrightarrow> arch_vcpu_tcb_valid (g s)\<rbrace>"
  unfolding do_machine_op_def
  by (wpsimp simp: arch_vcpu_tcb_valid_kheap_unfold)

lemmas do_machine_op_arch_vcpu_tcb_valid =
          do_machine_op_arch_vcpu_tcb_valid_imp[where P="\<top>", simplified]

lemma vcpu_switch_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. \<exists>obj. arch_vcpu_tcb_valid_obj (arch_state s) (TCB xd) \<and> ko_at obj cur s\<rbrace>
   vcpu_switch (ARM_A.tcb_vcpu (tcb_arch xd))
  \<lbrace>\<lambda>xa s. arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)\<rbrace>"
  apply (clarsimp simp add: vcpu_switch_def split: option.splits)
  apply (rule conjI; clarsimp)
  apply (wpsimp simp: ARM_A.vcpu_disable_def)
  apply (wpsimp wp: do_machine_op_arch_vcpu_tcb_valid)+
sorry

lemma blah:
  "tcb_at cur s \<Longrightarrow> arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>) \<Longrightarrow> (\<exists>y. get_tcb cur s = Some y) "
 apply (clarsimp simp add: arch_vcpu_tcb_valid_kheap_unfold is_tcb_def )
 apply (clarsimp split: kernel_object.splits)
 done

lemma 
  "tcb_at cur s \<Longrightarrow> (\<exists>obj. arch_vcpu_tcb_valid_obj (arch_state s) obj \<and> ko_at obj cur s) \<Longrightarrow>
   arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)"
 by (clarsimp simp: arch_vcpu_tcb_valid_kheap_unfold)

lemma set_vm_root_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid_obj ((arch_state s)\<lparr>ARM_A.arm_current_vcpu:= x\<rparr>) obj \<and> ko_at obj cur s \<rbrace>
     set_vm_root cur
   \<lbrace>\<lambda>x s. arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)\<rbrace>"
 unfolding set_vm_root_def
 apply_trace (wpsimp wp: vcpu_switch_arch_vcpu_tcb_valid do_machine_op_arch_vcpu_tcb_valid)
 apply (wpsimp wp: do_machine_op_arch_vcpu_tcb_valid gets_wp vcpu_switch_arch_vcpu_tcb_valid)+
 apply (fold tcb_at_def)

sorry

lemma arch_switch_to_thread_arch_vcpu_tcb_valid_obj:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid_obj (arch_state s) obj \<and> ko_at obj cur s \<rbrace>
      arch_switch_to_thread cur
   \<lbrace>\<lambda>a s. arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)\<rbrace>"
 unfolding arch_switch_to_thread_def
 apply wpsimp
 sorry

lemma switch_to_thread_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at cur s  \<rbrace> switch_to_thread cur \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
 unfolding switch_to_thread_def
 apply wpsimp
 apply (wpsimp wp: dxo_wp_weak assert_wp get_wp )
 apply (wpsimp wp: arch_switch_to_thread_arch_vcpu_tcb_valid_obj)
 apply (wpsimp wp: arch_switch_to_thread_arch_vcpu_tcb_valid_obj dxo_wp_weak assert_wp get_wp )+ 
 apply (erule (1) conjI[rotated])
 sorry

lemma obj_set_prop_not_at: 
 "\<lbrace>\<lambda>s. obj_at P p1 s \<and> p1 \<noteq> p2 \<rbrace> set_object p2 obj \<lbrace>\<lambda>rv. obj_at P p1\<rbrace>"
 by (wpsimp simp: set_object_def obj_at_def)

lemma vcpu_switch_idle_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. tcb_at thread s \<and> idle_thread s = thread  \<rbrace>
     vcpu_switch None
  \<lbrace>\<lambda>y s. tcb_at thread s \<rbrace>"
 by (wpsimp simp: vcpu_switch_def vcpu_disable_def)

lemma set_vcpu_obj_at_wp:
  "\<lbrace> \<lambda>s. obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> tcb_vcpu (tcb_arch t) = None) thread s \<rbrace>
           set_vcpu x1
            (x\<lparr>vcpu_vgic := vcpu_vgic x\<lparr>vgic_hcr := xa\<rparr>,
                 vcpu_regs := \<lambda>a. if a = VCPURegSCTLR then xb else vcpu_regs x a\<rparr>) 
           \<lbrace>\<lambda>xc. obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> tcb_vcpu (tcb_arch t) = None) thread\<rbrace>"
 apply (case_tac "x1 = thread")
 apply (wpsimp wp: obj_set_prop_at simp: set_vcpu_def)
 apply (wpsimp wp: obj_set_prop_at simp: set_vcpu_def)
 apply (rule obj_set_prop_not_at)
 apply wpsimp
 apply (wpsimp wp: get_object_wp)
 apply clarsimp
done

lemma 
 "\<lbrace>\<lambda>s. if vcpu = None then obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> ARM_A.tcb_vcpu (tcb_arch t)  = None) thread s
       else
   obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow>
                           ARM_A.tcb_vcpu (tcb_arch t) =
                              cur_vcpu_to_tcb_vcpu (map_option (\<lambda>v. (v, True)) vcpu))
               thread s
         \<rbrace>
     vcpu_switch vcpu
   \<lbrace>\<lambda>xa s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) thread s\<rbrace>"
 apply (simp add: vcpu_switch_def)
  apply (wpsimp simp: vcpu_switch_def vcpu_disable_def)
 apply (unfold arch_vcpu_tcb_valid_obj_def)
 apply (simp add: arch_vcpu_tcb_valid_obj_def cur_vcpu_to_tcb_vcpu_def)
 apply (wpsimp wp: set_vcpu_obj_at_wp)
 apply (rule do_machine_op_obj_at)+
 oops

lemma set_vm_root_idle_vcpu_tcb_valid:
 "\<And>v. \<lbrace>\<lambda>s. x = idle_thread s \<and> tcb_at x s \<and> v = (idle_thread s)\<rbrace>
    set_vm_root x
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) v s\<rbrace>"
 apply (simp add: set_vm_root_def)
 apply (wpsimp simp: set_vm_root_def)
sorry
 
lemma vcpu_switch_tcb_at:
"\<lbrace>\<lambda>s. (tcb_at t s)\<rbrace> vcpu_switch x \<lbrace>\<lambda>_ s. (tcb_at t s)\<rbrace>"
  apply (clarsimp simp add: tcb_at_def get_tcb_Some_ko_at valid_def)
  apply (cut_tac tcb=tcb in vcpu_switch_tcb_at_arch[where P="\<lambda>v .v", where t=t and param_a=x])
  apply (fastforce simp: valid_def)
 done

lemma arch_switch_to_idle_thread_vcpu_tcb_valid:
 "\<And>v. \<lbrace>\<lambda>s. tcb_at (idle_thread s) s \<and> v = (idle_thread s)\<rbrace>
    arch_switch_to_idle_thread 
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) v s\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  apply (wpsimp simp: arch_vcpu_tcb_valid_def arch_switch_to_idle_thread_def )
  apply (wpsimp wp: set_vm_root_idle_vcpu_tcb_valid)
  apply (wpsimp wp: gets_wp)
  apply simp
  apply (wps)
  apply (wpsimp wp: vcpu_switch_tcb_at)
  apply assumption
  done

lemma switch_to_idle_thread_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (idle_thread s) s \<rbrace>
     switch_to_idle_thread
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
 unfolding switch_to_idle_thread_def
 by (wpsimp wp: arch_switch_to_idle_thread_vcpu_tcb_valid  simp : arch_vcpu_tcb_valid_def) 

lemma getActiveTCB_Some_tcb_at[simp]:
 "getActiveTCB r s = Some y \<Longrightarrow> tcb_at r s"
 by (simp add: tcb_at_def getActiveTCB_def split: option.splits )

lemma idle_thread_tcb_at_invs:
  "invs s \<Longrightarrow> tcb_at (idle_thread s) s"
  apply (drule invs_valid_idle)
  apply (clarsimp simp add:  valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma schedule_arch_vcpu_tcb_valid:
  "\<lbrace>(\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid and invs\<rbrace>
  (schedule) :: (unit, unit) s_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding schedule_def
  apply (wpsimp wp: alternative_wp dxo_wp_weak assert_wp)
        apply (wpsimp wp: switch_to_thread_arch_vcpu_tcb_valid)
       apply (wpsimp wp: switch_to_thread_arch_vcpu_tcb_valid)
      apply (rule hoare_conj[unfolded bipred_conj_def])
       apply (wpsimp wp: select_wp)+
     apply (wpsimp wp:  simp: allActiveTCBs_gets)
     apply assumption
    apply (wpsimp wp: gets_wp)
   apply (wpsimp wp: gets_wp return_wp alternative_wp switch_to_idle_thread_arch_vcpu_tcb_valid)
  apply (clarsimp simp: tcb_at_invs idle_thread_tcb_at_invs)
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

