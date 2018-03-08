(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchVCPU_AI
imports AInvs.ArchDetSchedSchedule_AI
begin

(* FIXME MOVE *)
lemma is_tcb_TCB[simp]:
  "\<And>x.   is_tcb (TCB x)"
  "\<And>x y. \<not>is_tcb (CNode x y)"
  "\<And>x.   \<not>is_tcb (Endpoint x)"
  "\<And>x.   \<not>is_tcb (Notification x)"
  "\<And>x.   \<not>is_tcb (ArchObj x)"
 by (simp add: is_tcb_def)+

context Arch begin global_naming ARM_A

text {*
 The @{term arch_vcpu_tcb_valid} invariant ensures that the
 VCPU object reference in the current thread is always the
 same as the VCPU referenced by the global state.
 For global state @{term s}, the VCPU reference is obtain with
 @{term "ARM_A.arm_current_vcpu (arch_state s)"} and is of type
 @{typ "(obj_ref \<times> bool) option"}.
 The bool indicates whether the VCPU is active.
 When False, the current thread must have no VCPU reference.
 Otherwise, the global VCPU reference must equal the one in the
 current thread.
*}

definition
  "cur_vcpu_to_tcb_vcpu cur_vcpu =
    (case cur_vcpu of
       Some (vcpu, True) \<Rightarrow> Some vcpu
    | _ \<Rightarrow> None)"

definition
  arch_vcpu_tcb_valid_obj :: "arch_state \<Rightarrow> kernel_object \<Rightarrow> bool" where
  "arch_vcpu_tcb_valid_obj as obj \<equiv>
     \<forall>t. obj = TCB t \<longrightarrow>
           ARM_A.tcb_vcpu (tcb_arch t) = cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu as)"

definition
  arch_vcpu_tcb_valid :: "'z::state_ext state \<Rightarrow> bool" where
  "arch_vcpu_tcb_valid s \<equiv>
    obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) (cur_thread s) s"

text {*
{@term "valid_arch_idle"} should be included in @{term invs} (global abstract spec invariant).
*}
definition
 valid_arch_idle :: "'z::state_ext state \<Rightarrow> bool" where
 "valid_arch_idle s \<equiv>
    obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> ARM_A.tcb_vcpu (tcb_arch t) = None) (idle_thread s) s"

lemmas arch_vcpu_tcb_valid_kheap_unfold =
         arch_vcpu_tcb_valid_def
         arch_vcpu_tcb_valid_obj_def
         obj_at_def
         get_tcb_ko_at

lemma arch_vcpu_tcb_valid_trans_st[simp]:
 "arch_vcpu_tcb_valid (trans_state f s) = arch_vcpu_tcb_valid s"
 "arch_vcpu_tcb_valid (trans_state f s\<lparr>cur_thread := cur\<rparr>) = arch_vcpu_tcb_valid (s\<lparr>cur_thread := cur\<rparr>)"
 " arch_vcpu_tcb_valid (trans_state f s\<lparr>is_original_cap := (is_original_cap s)(dest := x)\<rparr>) =
       arch_vcpu_tcb_valid (s\<lparr>is_original_cap := (is_original_cap s)(dest := x)\<rparr>)"
 by (simp add: trans_state_def arch_vcpu_tcb_valid_def obj_at_def cur_tcb_def)+

definition
 "cur_thread_tcb_vcpu s \<equiv> ARM_A.tcb_vcpu (tcb_arch (the (get_tcb (cur_thread s) s)))"

lemma arch_vcpu_tcb_validE:
  "\<lbrakk> arch_vcpu_tcb_valid s ;
     ARM_A.arm_current_vcpu (arch_state s) = ARM_A.arm_current_vcpu (arch_state t) ;
     cur_thread_tcb_vcpu s = cur_thread_tcb_vcpu t;
     tcb_at (cur_thread s) s;
     tcb_at (cur_thread t) t \<rbrakk>
   \<Longrightarrow> arch_vcpu_tcb_valid t"
  apply (clarsimp simp: arch_vcpu_tcb_valid_def tcb_at_def )
  apply (clarsimp simp: arch_vcpu_tcb_valid_obj_def obj_at_def get_tcb_ko_at cur_thread_tcb_vcpu_def)
 done

lemma lift_arch_vcpu_tcb_valid:
  "\<lbrakk> \<And>P. \<lbrace>\<lambda>s. P (cur_thread_tcb_vcpu s) \<rbrace> f \<lbrace>\<lambda>_ s. P (cur_thread_tcb_vcpu s) \<rbrace> ;
     \<And>Q. \<lbrace>\<lambda>s. Q (arch_state s) \<rbrace> f \<lbrace>\<lambda>_ s.  Q (arch_state s)\<rbrace>;
     \<lbrace>\<lambda>s. tcb_at (cur_thread s) s \<rbrace> f \<lbrace>\<lambda>_ s.  tcb_at (cur_thread s) s \<rbrace> \<rbrakk>
 \<Longrightarrow> \<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<rbrace> f \<lbrace>\<lambda>_. arch_vcpu_tcb_valid\<rbrace>"
  apply (unfold valid_def)
  apply clarsimp
  apply (erule arch_vcpu_tcb_validE)
     apply (rename_tac s r s')
     apply (drule_tac x="op = (arch_state s)" in meta_spec) 
     apply fastforce
    apply (rename_tac s r s')
    apply (drule_tac x="op = (tcb_vcpu (tcb_arch (the (get_tcb (cur_thread s) s))) )" in meta_spec)
    apply (fastforce simp: cur_thread_tcb_vcpu_def)
   apply fastforce+
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

lemma do_machine_op_lift:
  "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>machine_state := x\<rparr>)) \<Longrightarrow>
    \<lbrace>\<lambda>s. P s \<rbrace> do_machine_op f \<lbrace>\<lambda>r s. P s\<rbrace>"
  unfolding do_machine_op_def
  by (wpsimp simp: arch_vcpu_tcb_valid_kheap_unfold)

lemma do_machine_op_res_lift:
  "\<And>r. (\<And>r r' s x. P r s \<Longrightarrow> P r' (s\<lparr>machine_state := x\<rparr>)) \<Longrightarrow>
    \<lbrace>\<lambda>s. P r s \<rbrace> do_machine_op f \<lbrace>\<lambda>r s. P r s\<rbrace>"
  unfolding do_machine_op_def
  by (wpsimp simp: arch_vcpu_tcb_valid_kheap_unfold)

lemma do_machine_op_arch_vcpu_tcb_valid_imp:
  "(\<And>s x. arch_state (g (s\<lparr>machine_state := x\<rparr>)) = arch_state (g s)) \<Longrightarrow>
   (\<And>s x. cur_thread (g (s\<lparr>machine_state := x\<rparr>)) = cur_thread (g s)) \<Longrightarrow>
   (\<And>s x. kheap (g (s\<lparr>machine_state := x\<rparr>)) (cur_thread (g s)) = kheap (g s) (cur_thread (g s))) \<Longrightarrow>
   (\<And>s x. P (s\<lparr>machine_state := x\<rparr>) = P s) \<Longrightarrow>
  \<lbrace>\<lambda>s. P s \<longrightarrow> arch_vcpu_tcb_valid (g s) \<rbrace>
   do_machine_op f
  \<lbrace>\<lambda>_ s. P s \<longrightarrow> arch_vcpu_tcb_valid (g s)\<rbrace>"
  unfolding do_machine_op_def
  by (wpsimp simp: arch_vcpu_tcb_valid_kheap_unfold)

lemmas do_machine_op_arch_vcpu_tcb_valid =
          do_machine_op_arch_vcpu_tcb_valid_imp[where P="\<top>", simplified]

lemma obj_set_prop_not_at:
 "\<lbrace>\<lambda>s. P (obj_at P' p1 s) \<and> p1 \<noteq> p2 \<rbrace> set_object p2 obj \<lbrace>\<lambda>rv s. P (obj_at P' p1 s)\<rbrace>"
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

(*cleanup maybe*)
lemma set_vcpu_obj_at_tcb_arch: (* generalise? this holds except when the ko is a vcpu *)
  "\<lbrace>\<lambda>s. P (obj_at (\<lambda>a. \<forall>tcb. a = TCB tcb \<longrightarrow> P' tcb) t s) \<rbrace>
      set_vcpu p v
   \<lbrace>\<lambda>_ s. P (obj_at (\<lambda>a. \<forall>tcb. a = TCB tcb \<longrightarrow> P' tcb) t s) \<rbrace>"
  apply (rule hoare_assume_pre)
  apply (clarsimp simp add: set_vcpu_def)
  including no_pre apply wpsimp
    prefer 3
    apply (rule get_object_sp)
   prefer 2
   apply (rule assert_sp)
  apply (simp add: set_object_def valid_def split_def
              split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp add: in_get in_bind in_put obj_at_def)
  done

crunch obj_at_tcb_arch:
  vcpu_save, vcpu_restore, vcpu_disable, arm_context_switch
  "\<lambda>s.  P (obj_at (\<lambda>a. \<forall>tcb. a = TCB tcb \<longrightarrow> P' tcb) t s)"
  (simp: crunch_simps ko_at_vcpu_helper wp: crunch_wps set_vcpu_obj_at_tcb_arch)

lemma vcpu_switch_obj_at_arch_vcpu_tcb_valid_obj:
 "\<lbrace>\<lambda>s. obj_at (\<lambda>obj. \<forall>t. obj = TCB t \<longrightarrow> ARM_A.tcb_vcpu (tcb_arch t) = vcpu) thread s \<rbrace>
     vcpu_switch vcpu
   \<lbrace>\<lambda>xa s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) thread s\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (wpsimp simp: vcpu_switch_def vcpu_disable_def  )
         apply (unfold arch_vcpu_tcb_valid_obj_def)
         apply (simp add: arch_vcpu_tcb_valid_obj_def cur_vcpu_to_tcb_vcpu_def)
         apply (wpsimp wp: set_vcpu_obj_at_wp)
        apply (rule do_machine_op_obj_at)+
      apply (wp get_vcpu_wp)
     apply (rule do_machine_op_lift)
     apply clarsimp
    apply (wpsimp wp: get_wp)
   apply (wpsimp wp: vcpu_save_obj_at_tcb_arch)
  apply (case_tac vcpu; clarsimp simp: cur_vcpu_to_tcb_vcpu_def)
  done

lemma vcpu_switch_None_wp:
 "\<lbrace>\<top>\<rbrace>
     vcpu_switch None
   \<lbrace>\<lambda>r s. cur_vcpu_to_tcb_vcpu (ARM_A.arm_current_vcpu (arch_state s)) = None \<rbrace>"
 by (wpsimp simp: vcpu_switch_def vcpu_disable_def cur_vcpu_to_tcb_vcpu_def )

lemma vcpu_switch_valid_arch_idle_wp:
 "\<lbrace>valid_arch_idle\<rbrace>
     vcpu_switch vcpu
  \<lbrace>\<lambda>r s. valid_arch_idle s\<rbrace>"
 apply (wpsimp simp: vcpu_switch_def vcpu_disable_def cur_vcpu_to_tcb_vcpu_def )
       apply (rule do_machine_op_lift; clarsimp simp: valid_arch_idle_def)
      apply (rename_tac obj_ref x2 y)
      apply wpsimp
          apply (rule do_machine_op_lift; clarsimp simp: valid_arch_idle_def)
         apply (wpsimp wp: set_vcpu_wp)
        apply (rule do_machine_op_res_lift; clarsimp simp: valid_arch_idle_def)
        apply (rename_tac s xc, case_tac "idle_thread s = obj_ref"; simp add: obj_at_def)
       apply (rule do_machine_op_res_lift; clarsimp simp: valid_arch_idle_def)
       apply (rename_tac s xb, case_tac "idle_thread s = obj_ref"; simp add: obj_at_def)
      apply (wpsimp wp: get_vcpu_wp)
     apply (rename_tac obj_ref x2)
     apply (rule do_machine_op_lift; clarsimp simp: valid_arch_idle_def)
     apply (simp add: obj_at_def)
    apply (wpsimp wp: gets_wp)
   apply (wpsimp wp: gets_wp)
     apply (simp add: valid_arch_idle_def)
     apply wps
     apply (wpsimp wp: vcpu_restore_obj_at[where P="\<lambda>x. x"])
    apply wpsimp
      apply (simp add: valid_arch_idle_def)
      apply wps
      apply (wpsimp wp: vcpu_restore_obj_at[where P="\<lambda>x. x"])
     apply wps
     apply (wpsimp wp: vcpu_save_obj_at_tcb_arch)
    apply (wpsimp wp: )
     apply (simp add: valid_arch_idle_def)
     apply wps
     apply (wpsimp wp: vcpu_enable_obj_at)
    apply (rule do_machine_op_lift; clarsimp)
   apply (wpsimp wp:gets_wp)
  apply (case_tac vcpu; clarsimp simp: valid_arch_idle_def)
  apply (rename_tac s obj_ref v)
  apply (case_tac "idle_thread s = obj_ref"; clarsimp simp: obj_at_def)
 done

lemma store_hw_asid_lift:
  assumes aam: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>))"
  and     aht: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table:= x\<rparr>\<rparr>))"
  shows "\<lbrace>\<lambda>s. P s \<rbrace> store_hw_asid a b \<lbrace>\<lambda>_ s. P s\<rbrace>"
  unfolding store_hw_asid_def
  apply (wpsimp simp: find_pd_for_asid_assert_def find_pd_for_asid_assert_def find_pd_for_asid_def)
  apply (drule aam)
  apply (drule aht)
  apply simp
  done

lemma invalidate_asid_lift:
 "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>)) \<Longrightarrow>
  \<lbrace>\<lambda>s. P s \<rbrace> invalidate_asid asid \<lbrace>\<lambda>r s. P s\<rbrace>"
  by (wpsimp simp: invalidate_asid_def )

lemma find_free_hw_asid_lift:
  assumes ms:"(\<And>s x. P s \<Longrightarrow> P (s\<lparr>machine_state := x\<rparr>))"
  and     aam: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>))"
  and     aht: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table:= x\<rparr>\<rparr>))"
  and     ana: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid:= x\<rparr>\<rparr>))"
  shows "\<lbrace>\<lambda>s. P s \<rbrace> find_free_hw_asid \<lbrace>\<lambda>_ s. P s\<rbrace>"
  apply (wpsimp simp: find_free_hw_asid_def invalidate_hw_asid_entry_def )
       apply (rule do_machine_op_lift)
       apply clarsimp
       apply (rename_tac hw_asid_table next_asid s x)
       apply (drule_tac x=x in ms)
       apply (drule_tac x="\<lambda>a. if a = next_asid then None else arm_hwasid_table (arch_state s) a" in aht)
       apply (erule rsubst[where P=P])
       apply clarsimp
      apply clarsimp
      apply (rule invalidate_asid_lift)
      apply (drule_tac x=x in aam)
      apply (erule rsubst[where P=P])
      apply clarsimp
     apply wpsimp
    apply (wpsimp wp: gets_wp)+
  apply (drule_tac x="arm_next_asid (arch_state s) + 1" in ana)
  apply (drule_tac x="\<lambda>a. if a = arm_next_asid (arch_state s) then None else arm_hwasid_table (arch_state s) a" in aht)
  apply (erule rsubst[where P=P])
  apply clarsimp
  done

lemma get_hw_asid_lift:
  assumes ms:"(\<And>s x. P s \<Longrightarrow> P (s\<lparr>machine_state := x\<rparr>))"
  and     aam: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>))"
  and     aht: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table:= x\<rparr>\<rparr>))"
  and     ana: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid:= x\<rparr>\<rparr>))"
  shows "\<lbrace>\<lambda>s. P s \<rbrace> get_hw_asid asid \<lbrace>\<lambda>_ s. P s\<rbrace>"
  unfolding get_hw_asid_def
  apply (wpsimp simp: arch_vcpu_tcb_valid_kheap_unfold wp: store_hw_asid_lift)
       apply (simp add: aam )
      apply (simp add: aht)
     apply (rule find_free_hw_asid_lift)
        apply (simp add: assms)+
    apply (wpsimp )
   apply clarsimp
   apply (wpsimp wp: load_hw_asid_wp)
  apply assumption
  done

lemma  arm_context_switch_lift:
  assumes ms:"(\<And>s x. P s \<Longrightarrow> P (s\<lparr>machine_state := x\<rparr>))"
  and     aam: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_map:= x\<rparr>\<rparr>))"
  and     aht: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_hwasid_table:= x\<rparr>\<rparr>))"
  and     ana: "(\<And>s x. P s \<Longrightarrow> P (s\<lparr>arch_state := arch_state s\<lparr>arm_next_asid:= x\<rparr>\<rparr>))"
  shows "\<lbrace>P\<rbrace> arm_context_switch pd asid \<lbrace>\<lambda>xb s. P s\<rbrace>"
  apply (wpsimp simp: arm_context_switch_def)
    apply (rule do_machine_op_lift)
    apply (erule ms)
   apply (rule get_hw_asid_lift)
      apply (erule ms aam aht ana)+
    apply assumption
  done

lemma find_pd_for_asid_lift:
  assumes E: "\<And>e s e'. E e s \<Longrightarrow> E e' s"
  and     P: "\<And> s r y. P r s \<Longrightarrow> P y s"
  shows "\<And>r e. \<lbrace>\<lambda>s. P r s \<and> E e s \<rbrace> find_pd_for_asid asid \<lbrace>\<lambda>r s. P r s\<rbrace>, \<lbrace>\<lambda>r s. E r s\<rbrace>"
  apply (simp add: find_pd_for_asid_def)
  apply wpsimp
  apply (fastforce elim: E P)
  done

lemma get_tcb_st_eq[simp]:
 "get_tcb x (s\<lparr>machine_state := xa\<rparr>) = get_tcb x s"
 "get_tcb x (s\<lparr>arch_state := as\<rparr>) = get_tcb x s"
 by (simp add: get_tcb_def)+

lemma hoare_whenE_throwError_wp:
"(\<And>s. Q s \<Longrightarrow> P \<Longrightarrow> E e s) \<Longrightarrow> (\<And>s. Q s \<Longrightarrow> R () s)  \<Longrightarrow> \<lbrace>Q\<rbrace> whenE P (throwError e) \<lbrace>R\<rbrace>, \<lbrace>E\<rbrace>"
  unfolding whenE_def
  by wpsimp

lemma arch_vcpu_tcb_valid_machine_state[simp]:
  "arch_vcpu_tcb_valid s \<Longrightarrow> arch_vcpu_tcb_valid (s\<lparr>machine_state := xb\<rparr>)"
 by (clarsimp simp: arch_vcpu_tcb_valid_def)

lemma obj_at_vcpu_tcb_valid_arch_st_upd[simp]:
  "\<And>x. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s \<Longrightarrow>
     obj_at (arch_vcpu_tcb_valid_obj (arch_state s\<lparr>arm_asid_map := x\<rparr>)) cur s"
  "\<And>x. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s \<Longrightarrow>
     obj_at (arch_vcpu_tcb_valid_obj (arch_state s\<lparr>arm_hwasid_table := x\<rparr>)) cur s"
  "\<And>x. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s \<Longrightarrow>
     obj_at (arch_vcpu_tcb_valid_obj (arch_state s\<lparr>arm_next_asid := x\<rparr>)) cur s"
  by (clarsimp simp: obj_at_def arch_vcpu_tcb_valid_obj_def)+

lemma set_vm_root_idle_vcpu_tcb_valid:
 "\<And>v. \<lbrace>\<lambda>s. x = idle_thread s \<and> tcb_at x s \<and> v = (idle_thread s) \<and>
            valid_arch_idle s \<and>
            cur_vcpu_to_tcb_vcpu (arm_current_vcpu (arch_state s)) = None \<rbrace>
    set_vm_root x
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) v s \<rbrace>"
  apply (simp add: set_vm_root_def)
  apply (wpsimp wp: vcpu_switch_obj_at_arch_vcpu_tcb_valid_obj )
        apply (rule arm_context_switch_lift; clarsimp)
      apply wpsimp
       apply (rule arm_context_switch_lift; clarsimp)
      apply (wpsimp wp: hoare_whenE_throwError_wp)
     apply (rule find_pd_for_asid_lift ; clarsimp)
      apply wpsimp
      apply wps
   apply (rule hoare_conjI, rule hoare_drop_imp, wpsimp)+
  apply wpsimp
  apply (wpsimp wp: get_cap_wp)
         apply (rule vcpu_switch_obj_at_arch_vcpu_tcb_valid_obj)
  apply wpsimp
  apply clarsimp
 done

lemma vcpu_switch_tcb_at:
"\<lbrace>\<lambda>s. (tcb_at t s)\<rbrace> vcpu_switch x \<lbrace>\<lambda>_ s. (tcb_at t s)\<rbrace>"
  apply (clarsimp simp add: tcb_at_def get_tcb_Some_ko_at valid_def)
  apply (rename_tac tcb)
  apply (cut_tac tcb=tcb in vcpu_switch_tcb_at_arch[where P="\<lambda>v .v", where t=t and param_a=x])
  apply (fastforce simp: valid_def)
 done

lemma arch_switch_to_idle_thread_vcpu_tcb_valid:
 "\<And>v. \<lbrace>\<lambda>s. tcb_at (idle_thread s) s \<and> v = idle_thread s
           \<and> arch_vcpu_tcb_valid s \<and> valid_arch_idle s\<rbrace>
    arch_switch_to_idle_thread
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) v s\<rbrace>"
  apply (simp add: arch_switch_to_idle_thread_def)
  apply (wpsimp simp: arch_vcpu_tcb_valid_def arch_switch_to_idle_thread_def )
  apply (wpsimp wp: set_vm_root_idle_vcpu_tcb_valid)
  apply (wpsimp wp: gets_wp)
  apply simp
  apply (wps)
  apply (wpsimp wp: vcpu_switch_tcb_at  vcpu_switch_None_wp)
  apply (wpsimp wp: vcpu_switch_valid_arch_idle_wp vcpu_switch_tcb_at vcpu_switch_None_wp)
  apply simp
  done

lemma switch_to_idle_thread_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (idle_thread s) s \<and> valid_arch_idle s\<rbrace>
     switch_to_idle_thread
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
 unfolding switch_to_idle_thread_def
 by (wpsimp wp: arch_switch_to_idle_thread_vcpu_tcb_valid  simp: arch_vcpu_tcb_valid_def)

lemma getActiveTCB_Some_tcb_at[simp]:
 "getActiveTCB r s = Some y \<Longrightarrow> tcb_at r s"
 by (simp add: tcb_at_def getActiveTCB_def split: option.splits )

lemma idle_thread_tcb_at_invs:
  "invs s \<Longrightarrow> tcb_at (idle_thread s) s"
  apply (drule invs_valid_idle)
  apply (clarsimp simp add:  valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma set_vm_root_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. tcb_at cur s \<and> arch_vcpu_tcb_valid s \<rbrace>
    set_vm_root cur
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s\<rbrace>"
 unfolding set_vm_root_def
  apply (wpsimp wp: vcpu_switch_obj_at_arch_vcpu_tcb_valid_obj)
            apply (rule arm_context_switch_lift; clarsimp)
           apply wpsimp
           apply (rule arm_context_switch_lift; clarsimp)
          apply wpsimp
         apply (wpsimp wp: hoare_whenE_throwError_wp)
        apply (wpsimp wp: hoare_whenE_throwError_wp)
       apply (rule find_pd_for_asid_lift ; clarsimp)
      apply wpsimp
     apply (wpsimp wp: get_cap_wp)
    apply wpsimp
   apply clarsimp
   apply (wpsimp wp: hoare_allI hoare_drop_imp vcpu_switch_obj_at_arch_vcpu_tcb_valid_obj)
  apply (wpsimp)
  apply (clarsimp simp add: arch_vcpu_tcb_valid_def arch_vcpu_tcb_valid_obj_def tcb_at_def)
  done

lemma arch_switch_to_thread_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. tcb_at cur s \<and> arch_vcpu_tcb_valid s\<rbrace>
    arch_switch_to_thread cur
  \<lbrace>\<lambda>x s. obj_at (arch_vcpu_tcb_valid_obj (arch_state s)) cur s\<rbrace>"
 unfolding arch_switch_to_thread_def
  apply (wpsimp wp: )
   apply (wpsimp wp: set_vm_root_vcpu_tcb_valid)
  apply assumption
 done

lemma switch_to_thread_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at cur s \<rbrace> switch_to_thread cur \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
 unfolding switch_to_thread_def
  apply wpsimp
     apply (wpsimp wp: dxo_wp_weak assert_wp get_wp )
    apply (simp add: arch_vcpu_tcb_valid_def)
    apply (wpsimp wp: arch_switch_to_thread_vcpu_tcb_valid)
   apply (wpsimp wp: arch_switch_to_thread_vcpu_tcb_valid dxo_wp_weak assert_wp get_wp)+
  done

lemma schedule_arch_vcpu_tcb_valid:
  "\<lbrace>(\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid and valid_arch_idle and invs\<rbrace>
    schedule :: (unit, unit) s_monad
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

lemma cur_thread_tcbp_vcpu_trans_state[simp]:
"cur_thread_tcb_vcpu (trans_state f s) = cur_thread_tcb_vcpu s"
  by (simp add: cur_thread_tcb_vcpu_def trans_state_def get_tcb_def)

lemma set_simple_ko_arch_vcpu_tcb_valid_helper:
  "(\<And>s::'a::state_ext state. P s \<Longrightarrow>  cur_thread_tcb_vcpu s = cur_thread_tcb_vcpu (s\<lparr>kheap := kheap s(r \<mapsto> t x)\<rparr>)) \<Longrightarrow>
   (\<And>s::'a::state_ext state. P s \<Longrightarrow> arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s) \<Longrightarrow>
   \<lbrace>P\<rbrace> (set_simple_ko t r x ::  ('a::state_ext state, unit) nondet_monad )\<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def wp: set_object_wp get_object_wp)
  apply (drule_tac x=s in meta_spec)+
  apply (rule conjI; clarsimp)
   apply (erule arch_vcpu_tcb_validE)
      apply (clarsimp simp: arm_current_vcpu_def)
     apply (clarsimp simp: cur_thread_tcb_vcpu_def )
   apply (case_tac "cur_thread s = r"; clarsimp simp add: obj_at_def)
  apply (case_tac "cur_thread s = r"; clarsimp simp add: obj_at_def)
  apply (erule arch_vcpu_tcb_validE)
     apply (clarsimp simp: arm_current_vcpu_def)
    apply (clarsimp simp: cur_thread_tcb_vcpu_def )
   apply (rename_tac s' ep, case_tac "cur_thread s' = r"; clarsimp simp add: obj_at_def)+
 done

lemma set_simple_ko_arch_vcpu_tcb_valid:
  "(\<And>s::'a::state_ext state.  cur_thread_tcb_vcpu s = cur_thread_tcb_vcpu (s\<lparr>kheap := kheap s(r \<mapsto> t x)\<rparr>)) \<Longrightarrow>
   \<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s\<rbrace> (set_simple_ko t r x ::  ('a::state_ext state, unit) nondet_monad )\<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  by (rule set_simple_ko_arch_vcpu_tcb_valid_helper; simp)

lemma set_simple_ko_not_obj_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. (arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s) \<and> r \<noteq> cur_thread s \<rbrace> (set_simple_ko t r x ::  ('a::state_ext state, unit) nondet_monad )\<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
 apply (wpsimp wp: set_simple_ko_arch_vcpu_tcb_valid_helper[where P="\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s  \<and> r \<noteq> cur_thread s"])
  apply (simp add: cur_thread_tcb_vcpu_def get_tcb_def)+
done
lemma set_thread_state_obj_at_prop_not_at:
" \<lbrace>\<lambda>s. ref \<noteq> ref' \<and> P (obj_at P' ref' s)\<rbrace> set_thread_state ref ts \<lbrace>\<lambda>rv s. P (obj_at P' ref' s)\<rbrace>"
  by (wpsimp simp: set_thread_state_def wp: dxo_wp_weak obj_set_prop_not_at)


lemma set_message_info_arch_vcpu_tcb_valid[wp]:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace> set_message_info receiver x \<lbrace>\<lambda>y. arch_vcpu_tcb_valid\<rbrace>"
  by (wpsimp simp: set_message_info_def)

lemma set_extra_badge_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace> set_extra_badge buffer badge n \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: set_extra_badge_def store_word_offs_def)
     apply (rule do_machine_op_arch_vcpu_tcb_valid; simp)
    apply (wpsimp wp: assert_wp)
   apply (wpsimp wp:)
  apply clarsimp
  done

lemma update_cdt_arch_vcpu_tcb_valid[wp]:
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace> update_cdt f \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid s\<rbrace>"
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid (s\<lparr>is_original_cap := (is_original_cap s)(a:=b)\<rparr>) \<rbrace> update_cdt f \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid (s\<lparr>is_original_cap := (is_original_cap s)(a:=b)\<rparr>)\<rbrace>"
  by (wpsimp wp: gets_wp simp: arch_vcpu_tcb_valid_def update_cdt_def set_cdt_def)+

lemma set_cap_arch_vcpu_tcb_valid[wp]:
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s\<rbrace> set_cap cap p \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid s\<rbrace>"
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid (s\<lparr>is_original_cap := (is_original_cap s)(a:=b)\<rparr>) \<and> tcb_at (cur_thread s) s\<rbrace>
   set_cap cap p
   \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid (s\<lparr>is_original_cap := (is_original_cap s)(a:=b)\<rparr>)\<rbrace>"
  by (wpsimp wp:set_object_wp get_object_wp simp: set_cap_def,
      rename_tac x y z,
      case_tac "x = cur_thread s"; clarsimp simp: arch_vcpu_tcb_valid_def obj_at_def arch_vcpu_tcb_valid_obj_def)+

lemma cap_insert_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>_ s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (simp add: cap_insert_def)
  apply (wpsimp wp:dxo_wp_weak set_cap_tcb simp: set_untyped_cap_as_full_def | rule conjI | wps)+
  apply (simp add:  arch_vcpu_tcb_valid_def )
  apply wpsimp
  apply (simp add:  arch_vcpu_tcb_valid_def )
  apply clarsimp
  apply (rule conjI; clarsimp?)+
  apply wpsimp
  apply (wps, wpsimp wp: set_cap_tcb)
  apply clarsimp
  apply (simp add:  arch_vcpu_tcb_valid_def )
  apply wpsimp
  apply (simp add:  arch_vcpu_tcb_valid_def )
  apply (rule conjI; clarsimp?)+
  apply wpsimp
  apply (wps, wpsimp wp: set_cap_tcb)
  apply (simp add:  arch_vcpu_tcb_valid_def )
apply wpsimp
  apply (simp add:  arch_vcpu_tcb_valid_def )
apply wpsimp
  apply (wpsimp wp: hoare_drop_imps get_cap_wp )  
  apply (wpsimp wp: hoare_drop_imps get_cap_wp )  
  apply (clarsimp simp: arch_vcpu_tcb_valid_def)
done

lemma setup_caller_cap_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s\<rbrace>
     setup_caller_cap sender receiver
   \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: setup_caller_cap_def wp: cap_insert_arch_vcpu_tcb_valid set_thread_state_arch_vcpu_tcb_valid)
  apply wps
  apply (wpsimp wp: set_thread_state_tcb_at)
  apply simp
  done

(* FIXME cleanup *)
lemma transfer_caps_loop_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s\<rbrace>
   transfer_caps_loop ep rcv_buffer n caps slots mi
  \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  apply (induct caps arbitrary: slots n mi, simp)
   apply wpsimp
  apply (clarsimp simp: Let_def split_def whenE_def
                  cong: if_cong list.case_cong
             split del: if_split)
  apply (wpsimp | rule conjI)+
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
              derive_cap_is_derived_foo
             hoare_drop_imps      
        | assumption | simp split del: if_split)+
  apply wps
  apply (wpsimp wp: set_extra_badge_arch_vcpu_tcb_valid set_extra_badge_typ_ats)
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
              derive_cap_is_derived_foo
             hoare_drop_imps      
        | assumption | simp split del: if_split)+
  apply wps
  apply (wpsimp wp: cap_insert_arch_vcpu_tcb_valid cap_insert_tcb)
  apply wpsimp
  apply wpsimp
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
              derive_cap_is_derived_foo
             hoare_drop_imps      
        | assumption | simp split del: if_split)+
done



lemma transfer_cap_arch_vcpu_tcb_valid:
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<rbrace> transfer_caps mi caps ep receiver recv_buffer \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  by (wpsimp simp: transfer_caps_def wp: transfer_caps_loop_arch_vcpu_tcb_valid )

lemma store_word_offs_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
   store_word_offs x2a xa xb 
  \<lbrace>\<lambda>buf_mrs. arch_vcpu_tcb_valid\<rbrace>"
  apply (unfold arch_vcpu_tcb_valid_def)
  apply (rule hoare_pre)
   apply wps
   apply (wpsimp wp: store_word_offs_obj_at_P)
  apply assumption
done

lemma copy_mrs_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s\<rbrace>
    copy_mrs sender sbuf receiver rbuf n
  \<lbrace>\<lambda>mrs_transferred s. arch_vcpu_tcb_valid s\<rbrace>"
  by (wpsimp simp: copy_mrs_def wp: mapM_wp' store_word_offs_arch_vcpu_tcb_valid)

lemma do_normal_transfer_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<rbrace>
   do_normal_transfer sender send_buffer ep badge grant receiver recv_buffer
  \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s \<rbrace>"
  apply (wpsimp simp: do_normal_transfer_def wp: set_message_info_arch_vcpu_tcb_valid 
            transfer_cap_arch_vcpu_tcb_valid copy_mrs_arch_vcpu_tcb_valid
              )
  apply wps
  apply (wpsimp wp: copy_mrs_tcb)
  apply wpsimp
  apply (wpsimp wp: hoare_drop_imps)
  apply clarsimp
done

lemma zipWithM_x_inv':
  assumes step: "\<And>x y. \<lbrace>P\<rbrace> m x y \<lbrace>\<lambda>rv. P\<rbrace>"
  shows " \<lbrace>P\<rbrace> zipWithM_x m xs ys \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct ys arbitrary:xs)
  apply (simp add: zipWithM_x_def sequence_x_def zipWith_def)
  apply (case_tac xs ;clarsimp)
  apply (wpsimp wp: step simp: zipWithM_x_def zipWith_def sequence_x_def)
  apply (rename_tac y ys x xs)
  apply (drule_tac x=xs in meta_spec)
  apply (wpsimp wp: step simp: zipWithM_x_def zipWith_def sequence_x_def)
  done

lemma set_mrs_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. (arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s)\<rbrace>
    set_mrs thread buf msgs
  \<lbrace>\<lambda>sent. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: set_mrs_def  wp:  )
  apply (rule conjI; clarsimp simp: )
  apply (wpsimp wp: zipWithM_x_inv')
  apply (wpsimp wp: store_word_offs_arch_vcpu_tcb_valid)
  apply simp
  apply (wpsimp wp: zipWithM_x_inv')
  apply (wpsimp wp: store_word_offs_arch_vcpu_tcb_valid)
  apply simp
  apply simp
  apply (wpsimp wp: set_object_wp)
  apply wpsimp  
  apply clarsimp
  apply (clarsimp simp: arch_vcpu_tcb_valid_def arch_vcpu_tcb_valid_obj_def arch_tcb_context_set_def obj_at_def)
  apply (simp add: is_tcb_def get_tcb_def split: kernel_object.splits)
done

lemma make_fault_msg_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s\<rbrace>
   make_fault_msg f sender 
  \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid s\<rbrace>"
  apply (case_tac f ; wpsimp)
  apply (rule conjI;clarsimp)
  apply wpsimp
  apply (rule hoare_pre)
  apply wpsimp
  apply simp
  apply (rename_tac x, case_tac x; wpsimp wp: do_machine_op_arch_vcpu_tcb_valid)
done


lemma do_fault_transfer_arch_vcpu_tcb_valid:
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<rbrace>
  do_fault_transfer badge sender receiver buf
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: do_fault_transfer_def
           wp:  hoare_drop_imps make_fault_msg_tcb_at
               set_mrs_arch_vcpu_tcb_valid  make_fault_msg_arch_vcpu_tcb_valid)
  apply (wps)
  apply wpsimp
  apply wpsimp
  apply (wpsimp wp: hoare_drop_imps)
  apply wpsimp
done

lemma do_ipc_transfer_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<rbrace>
   do_ipc_transfer sender ep badge grant receiver
  \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s \<rbrace>"
  by (wpsimp simp: do_ipc_transfer_def wp: do_normal_transfer_arch_vcpu_tcb_valid
        do_fault_transfer_arch_vcpu_tcb_valid)

lemma send_ipc_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<and> tcb_at thread s \<and> ep_at epptr s\<rbrace>
   send_ipc block call badge can_grant thread epptr
  \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  apply (wpsimp simp: send_ipc_def wp: )
  apply (wpsimp wp: set_simple_ko_not_obj_arch_vcpu_tcb_valid)
  apply wps
  apply (wpsimp wp: set_thread_state_arch_vcpu_tcb_valid set_thread_state_tcb_at)
  apply wpsimp
  apply wpsimp
  apply (wpsimp wp: set_simple_ko_not_obj_arch_vcpu_tcb_valid)
  apply wps
  apply (wpsimp wp: set_thread_state_arch_vcpu_tcb_valid set_thread_state_tcb_at)
apply wpsimp
apply (wpsimp wp: setup_caller_cap_arch_vcpu_tcb_valid)
  apply (simp add: if_apply_def2)
  apply (wpsimp wp: hoare_drop_imps)
 apply (wpsimp wp:dxo_wp_weak)
  apply wps
  apply (wpsimp wp: set_thread_state_arch_vcpu_tcb_valid set_thread_state_tcb_at)
  apply (wpsimp wp: )
  apply wps
  apply (wpsimp wp: do_ipc_transfer_arch_vcpu_tcb_valid)
  apply wpsimp+
  apply (wpsimp wp: hoare_drop_imps)
  apply wpsimp
  apply wps
  apply (wpsimp wp: set_simple_ko_not_obj_arch_vcpu_tcb_valid)
  apply (wpsimp wp: hoare_drop_imps hoare_vcg_all_lift)
  apply (clarsimp simp: obj_at_def is_ep)
done

lemma thread_set_tcb_fault_upd_arch_vcpu_tcb_valid:
 "\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some fault)) tptr \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s \<rbrace>"
  apply (wpsimp simp: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply wpsimp
  apply (clarsimp simp: arch_vcpu_tcb_valid_def)
  apply (case_tac "tptr = cur_thread s" )
  apply (clarsimp simp: arch_vcpu_tcb_valid_obj_def obj_at_def get_tcb_def split:kernel_object.splits )+
done

lemma thread_set_ep_at:
  "\<lbrace>\<lambda>s. tcb_at tptr s \<and> ep_at epptr s\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. ep_at epptr\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp simp: is_ep is_tcb)
  apply (case_tac "epptr = tptr"; clarsimp simp: obj_at_def is_ep)
done

lemma send_fault_ipc_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. valid_objs s \<and> arch_vcpu_tcb_valid s \<and> tcb_at (cur_thread s) s \<and> tcb_at tptr s\<rbrace>
     send_fault_ipc tptr fault
   \<lbrace>\<lambda>r. arch_vcpu_tcb_valid\<rbrace>"
  apply (simp add: send_fault_ipc_def)
  apply (wpsimp simp: Let_def)
  apply (wpsimp simp: send_fault_ipc_def Let_def wp: send_ipc_arch_vcpu_tcb_valid
        thread_set_tcb_fault_upd_arch_vcpu_tcb_valid)
  apply wps
  apply (wpsimp wp: thread_set_tcb_fault_upd_arch_vcpu_tcb_valid thread_set_ep_at)
  apply wpsimp+
  apply (rule hoare_post_imp_R[where Q'="\<lambda>r s. arch_vcpu_tcb_valid s \<and> valid_cap r s \<and> tcb_at (cur_thread s) s \<and> tcb_at tptr s"])
  apply wpsimp
  apply (clarsimp simp: valid_cap_def)
  apply wpsimp
  apply clarsimp
done

lemma send_fault_ipc_arch_vcpu_tcb_valid:
  "\<lbrace>\<lambda>s. valid_objs (s\<lparr>kheap := kheap s(thread \<mapsto> TCB (the (get_tcb thread s)\<lparr>tcb_state := Inactive\<rparr>))\<rparr>) \<and>
         arch_vcpu_tcb_valid (s\<lparr>kheap := kheap s(thread \<mapsto> TCB (the (get_tcb thread s)\<lparr>tcb_state := Inactive\<rparr>))\<rparr>) \<and>
         tcb_at (cur_thread s) s \<and> tcb_at tptr s\<rbrace>
     send_fault_ipc tptr fault
   \<lbrace>\<lambda>r s. arch_vcpu_tcb_valid (s\<lparr>kheap := kheap s(thread \<mapsto> TCB (the (get_tcb thread s)\<lparr>tcb_state := Inactive\<rparr>))\<rparr>)\<rbrace>"
  apply (simp add: send_fault_ipc_def)
  apply (wpsimp simp: Let_def)
  apply (wpsimp simp: send_fault_ipc_def Let_def wp: send_ipc_arch_vcpu_tcb_valid
        thread_set_tcb_fault_upd_arch_vcpu_tcb_valid)
  apply wps
  apply (wpsimp wp: thread_set_tcb_fault_upd_arch_vcpu_tcb_valid thread_set_ep_at)
  apply wpsimp+
  apply (rule hoare_post_imp_R[where Q'="\<lambda>r s. arch_vcpu_tcb_valid s \<and> valid_cap r s \<and> tcb_at (cur_thread s) s \<and> tcb_at tptr s"])
  apply wpsimp
  apply (clarsimp simp: valid_cap_def)
  apply wpsimp
  apply clarsimp
done

lemma handle_call_cur_thread_tcb_vcpu:
"\<lbrace>\<lambda>s. arch_vcpu_tcb_valid s \<and> valid_objs s \<and> tcb_at (cur_thread s) s \<rbrace> handle_call 
         \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s\<rbrace>, \<lbrace>\<lambda>rv s. arch_vcpu_tcb_valid s\<rbrace>"
 apply (wpsimp simp: handle_call_def handle_invocation_def syscall_def handle_fault_def 
                  handle_double_fault_def set_thread_state_def
               wp: dxo_wp_weak set_object_wp send_fault_ipc_arch_vcpu_tcb_valid)
  apply (wpsimp wp: hoare_drop_imps)

oops

lemma handle_event_arch_vcpu_tcb_valid:
"\<lbrace>(\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid and valid_arch_idle and invs\<rbrace>
    (handle_event e) :: (interrupt + unit, unit) s_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"

oops
apply (case_tac e ; clarsimp)
apply (rename_tac x)
apply (case_tac x; clarsimp)
  apply (wpsimp wp: lift_arch_vcpu_tcb_valid)
find_theorems arch_vcpu_tcb_valid name:lift
oops

theorem akernel_arch_vcpu_tcb_valid_inv:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and arch_vcpu_tcb_valid and valid_arch_idle \<rbrace>
    call_kernel e :: (unit,unit) s_monad
  \<lbrace>\<lambda>rv. arch_vcpu_tcb_valid \<rbrace>"
  unfolding call_kernel_def
  apply (wpsimp wp: schedule_arch_vcpu_tcb_valid activate_invs simp: active_from_running )
oops

end

