(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory EmptyFail_AI
imports Tcb_AI
begin

lemmas [wp] = empty_fail_bind empty_fail_bindE empty_fail_get empty_fail_modify
              empty_fail_whenEs empty_fail_when empty_fail_gets empty_fail_assertE
              empty_fail_error_bits empty_fail_mapM_x empty_fail_mapM empty_fail_sequence_x
              ef_ignore_failure ef_machine_op_lift
lemmas empty_fail_error_bits[simp]

lemma sequence_empty_fail[wp]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> empty_fail m) \<Longrightarrow> empty_fail (sequence ms)"
  apply (induct ms)
   apply (simp add: sequence_def | wp)+
   done

lemma sequenceE_empty_fail[wp]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> empty_fail m) \<Longrightarrow> empty_fail (sequenceE ms)"
  apply (induct ms)
   apply (simp add: sequenceE_def | wp)+
   done

lemma sequenceE_x_empty_fail[wp]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> empty_fail m) \<Longrightarrow> empty_fail (sequenceE_x ms)"
  apply (induct ms)
   apply (simp add: sequenceE_x_def | wp)+
   done

lemma mapME_empty_fail[wp]:
  "(\<And>x. empty_fail (m x)) \<Longrightarrow> empty_fail (mapME m xs)"
  by (clarsimp simp: mapME_def image_def | wp)+

lemma mapME_x_empty_fail[wp]:
  "(\<And>x. empty_fail (f x)) \<Longrightarrow> empty_fail (mapME_x f xs)"
  by (clarsimp simp: mapME_x_def | wp)+

lemma filterM_empty_fail[wp]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> empty_fail (P m)) \<Longrightarrow> empty_fail (filterM P ms)"
  apply (induct ms)
   apply (simp | wp)+
   done

lemma zipWithM_x_empty_fail[wp]:
  "(\<And>x y. empty_fail (f x y)) \<Longrightarrow> empty_fail (zipWithM_x f xs ys)"
  by (clarsimp simp: zipWithM_x_def zipWith_def | wp)+

lemma zipWithM_empty_fail[wp]:
  "(\<And>x y. empty_fail (f x y)) \<Longrightarrow> empty_fail (zipWithM f xs ys)"
  by (clarsimp simp: zipWithM_def zipWith_def | wp)+

lemma handle'_empty_fail[wp]:
  "\<lbrakk>empty_fail f; \<And>e. empty_fail (handler e)\<rbrakk> \<Longrightarrow> empty_fail (f <handle2> handler)"
  apply (simp add: handleE'_def | wp)+
  apply (case_tac x, simp_all)
  done

lemma handle_empty_fail[wp]:
  "\<lbrakk>empty_fail f; \<And>e. empty_fail (handler e)\<rbrakk> \<Longrightarrow> empty_fail (f <handle> handler)"
  by (simp add: handleE_def | wp)+

lemma lookup_error_on_failure_empty_fail[wp]:
  "empty_fail f \<Longrightarrow> empty_fail (lookup_error_on_failure a f)"
  by (simp add: lookup_error_on_failure_def | wp)+

lemma empty_on_failure_empty_fail[wp]:
  "empty_fail f \<Longrightarrow> empty_fail (empty_on_failure f)"
  by (simp add: empty_on_failure_def catch_def split: sum.splits | wp)+

lemma unify_failure_empty_fail[wp]:
  "empty_fail f \<Longrightarrow> empty_fail (unify_failure f)"
  by (simp add: unify_failure_def | wp)+

lemma split_if_empty_fail[wp]:
  "\<lbrakk>P \<Longrightarrow> empty_fail f; \<not> P \<Longrightarrow> empty_fail g\<rbrakk> \<Longrightarrow> empty_fail (if P then f else g)"
  by simp

lemma const_on_failure_empty_fail[wp]:
  "empty_fail f \<Longrightarrow> empty_fail (const_on_failure a f)"
  by (simp add: const_on_failure_def catch_def split: sum.splits | wp)+

lemma liftME_empty_fail[simp]:
  "empty_fail (liftME f m) = empty_fail m"
  apply (simp add: liftME_def)
  apply (rule iffI)
   apply (simp add: bindE_def)
   apply (drule empty_fail_bindD1)
   apply (simp | wp)+
   done

lemma select_empty_fail[wp]:
  "S \<noteq> {} \<Longrightarrow> empty_fail (select S)"
  by (simp add: empty_fail_def select_def)

lemma select_f_empty_fail[wp]:
  "(fst S = {} \<Longrightarrow> snd S) \<Longrightarrow> empty_fail (select_f S)"
  by (simp add: select_f_def empty_fail_def)

lemma select_ext_empty_fail:
  "S \<noteq> {} \<Longrightarrow> empty_fail (select_ext a S)"
  by (simp add: select_ext_def | wp)+

lemma do_extended_op_empty_fail[wp]:
  "empty_fail (do_extended_op f)"
  apply(simp add: do_extended_op_def)
  apply (wp | simp add: mk_ef_def split_def)+
  done

lemma do_machine_op_empty_fail[wp]:
  "empty_fail f \<Longrightarrow> empty_fail (do_machine_op f)"
  apply (simp add: do_machine_op_def | wp)+
   apply (simp add: empty_fail_def)
  apply (simp add: split_def)
  done

lemma throw_on_false_empty_fail[wp]:
  "empty_fail f \<Longrightarrow> empty_fail (throw_on_false ex f)"
  by (simp add: throw_on_false_def | wp)+

lemma without_preemption_empty_fail[wp]:
  "empty_fail f \<Longrightarrow> empty_fail (without_preemption f)"
  by simp

lemma put_empty_fail[wp]:
  "empty_fail (put f)"
  by (simp add: put_def empty_fail_def)


crunch_ignore (empty_fail)
  (add: bind bindE lift liftE liftM when whenE unless unlessE return fail assert_opt
        mapM mapM_x sequence_x catch handleE invalidateTLB_ASID_impl
        invalidateTLB_VAASID_impl cleanByVA_impl cleanByVA_PoU_impl invalidateByVA_impl
        invalidateByVA_I_impl invalidate_I_PoU_impl cleanInvalByVA_impl branchFlush_impl
        clean_D_PoU_impl cleanInvalidate_D_PoC_impl cleanInvalidateL2Range_impl
        invalidateL2Range_impl cleanL2Range_impl flushBTAC_impl writeContextID_impl
        isb_impl dsb_impl dmb_impl setHardwareASID_impl writeTTBR0_impl do_extended_op
        cacheRangeOp)

crunch (empty_fail) empty_fail[wp]: set_object, gets_the, get_register, get_cap
  (simp: split_def kernel_object.splits)

lemma check_cap_at_empty_fail[wp]:
  "empty_fail m \<Longrightarrow> empty_fail (check_cap_at cap slot m)"
  by (simp add: check_cap_at_def | wp)+

lemma as_user_empty_fail[wp]:
  "empty_fail f \<Longrightarrow> empty_fail (as_user t f)"
  apply (simp add: as_user_def | wp)+
   apply (simp add: empty_fail_def)
  apply (case_tac xa)
  apply (simp | wp)+
  done

crunch (empty_fail) empty_fail[wp]: get_message_info
  (simp: split_def kernel_object.splits)

lemma cap_fault_on_failure_empty_fail[wp]:
  "empty_fail f \<Longrightarrow> empty_fail (cap_fault_on_failure a b f)"
  by (simp add: cap_fault_on_failure_def | wp)+

lemma syscall_empty_fail[wp]:
  "\<lbrakk>empty_fail a; \<And>x. empty_fail (b x); \<And>x. empty_fail (c x);
    \<And>x. empty_fail (d x); \<And>x. empty_fail (e x)\<rbrakk>
    \<Longrightarrow> empty_fail (syscall a b c d e)"
  by (simp add: syscall_def split: sum.splits | wp | intro impI allI)+

definition spec_empty_fail where
  "spec_empty_fail m s \<equiv> fst (m s) = {} \<longrightarrow> snd (m s)"

lemma drop_spec_empty_fail:
  "empty_fail m \<Longrightarrow> spec_empty_fail m s"
  by (simp add: empty_fail_def spec_empty_fail_def)

lemma spec_empty_fail_bind:
  "\<lbrakk>spec_empty_fail f s; \<And>x. empty_fail (g x)\<rbrakk>
    \<Longrightarrow> spec_empty_fail (f >>= g) s"
  by (fastforce simp: bind_def spec_empty_fail_def empty_fail_def image_def split_def split_paired_Bex intro: prod_eqI)

lemma spec_empty_fail_bindE:
  "\<lbrakk>spec_empty_fail f s; \<And>x. empty_fail (g x)\<rbrakk>
    \<Longrightarrow> spec_empty_fail (f >>=E g) s"
  by (fastforce simp: bindE_def lift_def split: sum.splits intro: spec_empty_fail_bind)

lemma spec_empty_fail_bind':
  "\<lbrakk>spec_empty_fail f s; \<And>x s'. (x, s') \<in> fst (f s) \<Longrightarrow> spec_empty_fail (g x) s'\<rbrakk>
    \<Longrightarrow> spec_empty_fail (f >>= g) s"
  by (fastforce simp: bind_def spec_empty_fail_def image_def split_def split_paired_Bex intro: prod_eqI)

lemma spec_empty_fail_bindE':
  "\<lbrakk>spec_empty_fail f s; \<And>x s'. (Inr x, s') \<in> fst (f s) \<Longrightarrow> spec_empty_fail (g x) s'\<rbrakk>
    \<Longrightarrow> spec_empty_fail (f >>=E g) s"
  apply (simp add: bindE_def)
  apply (rule spec_empty_fail_bind')
   apply simp
  apply (clarsimp simp: lift_def split: sum.splits | rule conjI | wp drop_spec_empty_fail)+
  done

lemma spec_empty_returnOk: "spec_empty_fail (returnOk x) s"
  apply (rule drop_spec_empty_fail)
  apply simp
  done

lemma spec_empty_whenE: "spec_empty_fail f s \<Longrightarrow> spec_empty_fail (whenE P f) s"
  apply (simp add: whenE_def)
  apply (clarsimp simp: spec_empty_returnOk)
  done


lemma use_spec_empty_fail: "(\<And>s. spec_empty_fail f s) \<Longrightarrow> empty_fail f"
  apply (simp add: empty_fail_def spec_empty_fail_def)
  done


lemma resolve_address_bits_spec_empty_fail:
  notes spec_empty_fail_bindE'[wp_split]        
  shows
  "spec_empty_fail (resolve_address_bits slot) s"
unfolding resolve_address_bits_def
proof (induct arbitrary: s rule: resolve_address_bits'.induct)
  case (1 z cap cref s')
  show ?case
    apply (simp add: resolve_address_bits'.simps)
    apply (case_tac cap,(wp | simp del: resolve_address_bits'.simps | intro impI conjI | rule "1.hyps" | rule drop_spec_empty_fail | simp add: whenE_def in_monad | force)+)
    done
 qed

lemmas resolve_address_bits_empty_fail[wp] =
       resolve_address_bits_spec_empty_fail[THEN use_spec_empty_fail]

crunch (empty_fail) empty_fail[wp]: loadWord, load_word_offs

lemma get_extra_cptrs_empty_fail[wp]:
  "empty_fail (get_extra_cptrs a b)"
  apply (simp add: get_extra_cptrs_def)
  apply (cases a)
   apply (simp | wp)+
   done

crunch_ignore (empty_fail)
  (add: cap_insert_ext empty_slot_ext create_cap_ext cap_swap_ext cap_move_ext
        reschedule_required switch_if_required_to attempt_switch_to set_thread_state_ext
        OR_choice OR_choiceE set_priority timer_tick)

crunch (empty_fail) empty_fail[wp]: storeWord, set_register, lookup_slot_for_cnode_op,
                   getRestartPC, decode_untyped_invocation, get_mrs, range_check,
                   handle_fault
  (simp: kernel_object.splits option.splits arch_cap.splits cap.splits endpoint.splits
         bool.splits list.splits thread_state.splits split_def catch_def sum.splits
         Let_def wp: zipWithM_x_empty_fail)

crunch (empty_fail)empty_fail[wp]: lookup_source_slot,lookup_pivot_slot

lemma decode_cnode_invocation_empty_fail[wp]:
  "empty_fail (decode_cnode_invocation a b c d)"
  by (simp add: decode_cnode_invocation_def split: invocation_label.splits list.splits | wp | intro impI conjI allI)+

lemma decode_read_registers_empty_fail[wp]:
  "empty_fail (decode_read_registers data (ThreadCap p))"
  by (simp add: decode_read_registers_def split: list.splits cap.splits | wp | intro allI impI conjI)+ 

lemma decode_write_registers_empty_fail[wp]:
  "empty_fail (decode_write_registers data (ThreadCap p))"
  by (simp add: decode_write_registers_def split: list.splits cap.splits | wp | intro allI impI conjI)+

lemma decode_copy_registers_empty_fail[wp]:
  "empty_fail (decode_copy_registers data (ThreadCap p) ec)"
  by (simp add: decode_copy_registers_def split: list.splits cap.splits | wp | intro allI impI conjI)+

lemma alternative_empty_fail[wp]:
  "empty_fail f \<or> empty_fail g \<Longrightarrow> empty_fail (f OR g)"
  by (auto simp: alternative_def empty_fail_def)

lemma OR_choice_empty_fail[wp]:
  "\<lbrakk>empty_fail f; empty_fail g\<rbrakk> \<Longrightarrow> empty_fail (OR_choice c f g)"
  by (simp add: OR_choice_def mk_ef_def split_def | wp)+

crunch (empty_fail) empty_fail[wp]: decode_tcb_configure, decode_bind_notification, decode_unbind_notification
  (simp: cap.splits arch_cap.splits split_def)

lemma decode_tcb_invocation_empty_fail[wp]:
  "empty_fail (decode_tcb_invocation a b (ThreadCap p) d e)"
  apply (simp add: decode_tcb_invocation_def split: invocation_label.splits | wp | intro conjI impI)+
  done

crunch (empty_fail) empty_fail[wp]: find_pd_for_asid, get_master_pde, check_vp_alignment,
                   create_mapping_entries, ensure_safe_mapping, get_asid_pool, resolve_vaddr
  (simp: kernel_object.splits arch_kernel_obj.splits option.splits pde.splits pte.splits)

lemmas empty_fail_return[wp]

lemma arch_decode_ARMASIDControlMakePool_empty_fail:
  "invocation_type label = ARMASIDControlMakePool
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  apply (simp add: arch_decode_invocation_def Let_def)
  apply (intro impI conjI allI)
   apply (simp add: isPageFlush_def isPDFlush_def split: arch_cap.splits)+
   apply (rule impI)
   apply (simp add: split_def)
   apply wp
    apply simp
   apply (subst bindE_assoc[symmetric])
   apply (rule empty_fail_bindE)
    apply (fastforce simp: empty_fail_def whenE_def throwError_def select_ext_def bindE_def bind_def return_def returnOk_def lift_def liftE_def fail_def gets_def get_def assert_def select_def split: split_if_asm)
   apply (simp add: Let_def split: cap.splits arch_cap.splits option.splits | wp | intro conjI impI allI)+
   done

lemma arch_decode_ARMASIDPoolAssign_empty_fail:
  "invocation_type label = ARMASIDPoolAssign
    \<Longrightarrow> empty_fail (arch_decode_invocation label b c d e f)"
  apply (simp add: arch_decode_invocation_def split_def Let_def isPageFlush_def isPDFlush_def split: arch_cap.splits cap.splits option.splits | intro impI allI)+
  apply (rule empty_fail_bindE)
   apply simp
  apply (rule empty_fail_bindE)
   apply ((simp | wp)+)[1]
  apply (rule empty_fail_bindE)
   apply ((simp | wp)+)[1]
  apply (rule empty_fail_bindE)
   apply ((simp | wp)+)[1]
  apply (subst bindE_assoc[symmetric])
  apply (rule empty_fail_bindE)
   apply (fastforce simp: empty_fail_def whenE_def throwError_def select_def bindE_def bind_def return_def returnOk_def lift_def liftE_def select_ext_def select_def gets_def get_def assert_def fail_def)
  apply wp
  done

lemma arch_decode_invocation_empty_fail[wp]:
  "empty_fail (arch_decode_invocation label b c d e f)"
  apply (case_tac "invocation_type label")
  prefer 43  
  prefer 44
  apply ((simp add: arch_decode_ARMASIDControlMakePool_empty_fail arch_decode_ARMASIDPoolAssign_empty_fail)+)[2]  
  by ((simp add: arch_decode_invocation_def Let_def split: arch_cap.splits cap.splits option.splits | wp | intro conjI impI allI)+)

crunch (empty_fail) empty_fail[wp]: maskInterrupt, empty_slot, setInterruptMode,
    setHardwareASID, setCurrentPD, finalise_cap, preemption_point,
    cap_swap_for_delete, decode_invocation
  (simp: Let_def catch_def split_def OR_choiceE_def mk_ef_def option.splits endpoint.splits
         notification.splits thread_state.splits sum.splits cap.splits arch_cap.splits
         kernel_object.splits vmpage_size.splits pde.splits bool.splits list.splits)

crunch (empty_fail) empty_fail[wp]: setRegister, setNextPC

lemma rec_del_spec_empty_fail:
  "spec_empty_fail (rec_del call) s"
proof (induct rule: rec_del.induct, simp_all only: drop_spec_empty_fail[OF empty_fail] rec_del_fails)
  case (1 slot exposed s)
  show ?case
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply (rule spec_empty_fail_bindE)
     apply (simp add: "1.hyps")
    apply (wp | simp)+
    done
next
  case (2 slot exposed s)
  show ?case
    apply (subst rec_del.simps)
    apply (rule spec_empty_fail_bindE')
     apply ((wp drop_spec_empty_fail | simp)+)[1]
    apply (simp | intro conjI impI)+
     apply (wp drop_spec_empty_fail)[1]
    apply (rule spec_empty_fail_bindE')
     apply ((wp drop_spec_empty_fail | simp)+)[1]
    apply (rule spec_empty_fail_bindE')
     apply ((wp drop_spec_empty_fail | simp)+)[1]
    apply (simp add: split_def | intro conjI impI)+
       apply ((wp drop_spec_empty_fail | simp)+)[3]
    apply (rule spec_empty_fail_bindE')
     apply ((wp drop_spec_empty_fail | simp)+)[1]
    apply (rule spec_empty_fail_bindE')
     apply (rule "2.hyps", simp+)
    apply (rule spec_empty_fail_bindE')
     apply (wp drop_spec_empty_fail)[1]
    apply (rule "2.hyps", simp+)
    done
next
  case 3
  show ?case
    apply (simp | wp drop_spec_empty_fail)+
    done
next
  case (4 ptr bits n slot s)
  show ?case
    apply (subst rec_del.simps)
    apply (rule spec_empty_fail_bindE')
     apply (wp drop_spec_empty_fail)[1]
    apply (rule spec_empty_fail_bindE)
     apply (rule "4.hyps", assumption+)
    apply (wp | simp)+
    done
qed

lemma rec_del_empty_fail[wp]:
  "empty_fail (rec_del call)"
  apply (simp add: empty_fail_def)
  apply (rule allI)
  apply (rule rec_del_spec_empty_fail[simplified spec_empty_fail_def])
  done

crunch (empty_fail) empty_fail[wp]: cap_delete

lemma cap_revoke_spec_empty_fail:
  "spec_empty_fail (cap_revoke slot) s"
proof (induct rule: cap_revoke.induct)
  case (1 slot)
  show ?case
    apply (subst cap_revoke.simps)
    apply (rule spec_empty_fail_bindE', ((wp drop_spec_empty_fail | simp)+)[1])+
    apply (simp add: whenE_def | intro conjI impI)+
      apply (rule spec_empty_fail_bindE',
               ((wp drop_spec_empty_fail select_ext_empty_fail | simp)+)[1])+
      apply (rule "1.hyps", simp+)
     apply (wp drop_spec_empty_fail)
     done
qed

lemma cap_revoke_empty_fail[wp]:
  "empty_fail (cap_revoke slot)"
  apply (simp add: empty_fail_def)
  apply (rule allI)
  apply (rule cap_revoke_spec_empty_fail[simplified spec_empty_fail_def])
  done

lemma clearExMonitor_empty_fail[wp]:
  "empty_fail clearExMonitor"
  by (simp add: clearExMonitor_def)

crunch (empty_fail) empty_fail[wp]: choose_thread

crunch (empty_fail) empty_fail: allActiveTCBs

lemma schedule_empty_fail[wp]:
  "empty_fail (schedule :: (unit,unit) s_monad)"
  apply (simp add: schedule_def)
  apply wp
  apply (rule disjI2)
   apply wp
  done

crunch (empty_fail) empty_fail[wp]: set_scheduler_action, next_domain, reschedule_required
  (simp: scheduler_action.split)

lemma schedule_empty_fail'[wp]:
  "empty_fail (schedule :: (unit,det_ext) s_monad)"
  apply (simp add: schedule_def)
  apply (wp | clarsimp split: scheduler_action.splits| 
            intro impI conjI)+
  done

crunch (empty_fail) empty_fail[wp]: handle_event,activate_thread
  (simp: cap.splits arch_cap.splits split_def invocation_label.splits Let_def
         kernel_object.splits arch_kernel_obj.splits option.splits pde.splits pte.splits
         bool.splits apiobject_type.splits aobject_type.splits notification.splits
         thread_state.splits endpoint.splits catch_def sum.splits cnode_invocation.splits
         page_table_invocation.splits page_invocation.splits asid_control_invocation.splits
         asid_pool_invocation.splits arch_invocation.splits irq_state.splits syscall.splits
         flush_type.splits page_directory_invocation.splits
   ignore: resetTimer_impl)

lemma call_kernel_empty_fail: "empty_fail ((call_kernel a) :: (unit,det_ext) s_monad)"
  apply (simp add: call_kernel_def)
  apply (wp schedule_empty_fail | simp add: empty_fail_error_bits)+
  done

lemma call_kernel_empty_fail': "empty_fail ((call_kernel a) :: (unit,unit) s_monad)"
  apply (simp add: call_kernel_def)
  apply (wp schedule_empty_fail | simp add: empty_fail_error_bits)+
  done

end
