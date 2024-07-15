(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IRQMasks_IF
imports "Access.ArchDomainSepInv"
begin

abbreviation irq_masks_of_state :: "det_ext state \<Rightarrow> irq \<Rightarrow> bool" where
  "irq_masks_of_state s \<equiv> irq_masks (machine_state s)"

lemma detype_irq_masks[simp]:
  "irq_masks (machine_state (detype S s)) = irq_masks_of_state s"
  by (simp add: detype_def)

crunch cap_insert
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps)

lemma invoke_irq_handler_irq_masks:
  "\<lbrace>domain_sep_inv False st and (\<lambda>s. (\<exists>ptr'. cte_wp_at ((=) (IRQHandlerCap irq)) ptr' s))\<rbrace>
   invoke_irq_handler blah
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  by (clarsimp simp: valid_def domain_sep_inv_def)

lemma empty_slot_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and K (irq_opt = NullCap)\<rbrace>
   empty_slot slot irq_opt
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wpsimp simp: empty_slot_def post_cap_deletion_def)
  done

lemma spec_strengthen_errE:
  "\<lbrakk> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E'\<rbrace>; \<And>s r. E' s r \<Longrightarrow> E s r \<rbrakk>
     \<Longrightarrow> s \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  by (auto simp: spec_validE_def validE_def valid_def split: sum.splits)

crunch create_cap
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
crunch cap_swap_for_delete
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"


locale IRQMasks_IF_1 =
  fixes state_t :: "'s :: state_ext state"
  assumes resetTimer_irq_masks[wp]:
    "resetTimer \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>"
  and storeWord_irq_masks[wp]:
    "storeWord x y \<lbrace>\<lambda>s. P (irq_masks s)\<rbrace>"
  and delete_objects_irq_masks[wp]:
    "delete_objects ptr bits \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and invoke_untyped_irq_masks[wp]:
    "invoke_untyped ui \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and finalise_cap_irq_masks[wp]:
    "finalise_cap cap final \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and send_signal_irq_masks[wp]:
    "send_signal ntfnptr badge \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and handle_vm_fault_irq_masks[wp]:
    "handle_vm_fault t vmft \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and handle_hypervisor_fault_irq_masks[wp]:
    "handle_hypervisor_fault t hvft \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and handle_interrupt_irq_masks:
    "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False (st :: 's state) and K (irq \<le> maxIRQ)\<rbrace>
     handle_interrupt irq
     \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  and arch_invoke_irq_control_irq_masks:
    "\<lbrace>domain_sep_inv False st and arch_irq_control_inv_valid ivk\<rbrace>
     arch_invoke_irq_control ivk
     \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  and dmo_getActiveIRQ_irq_masks[wp]:
    "do_machine_op (getActiveIRQ in_kernel) \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and dmo_getActiveIRQ_return_axiom[wp]:
    "\<lbrace>\<top>\<rbrace>
     do_machine_op (getActiveIRQ in_kernel)
     \<lbrace>\<lambda>rv s :: det_state. (\<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ)\<rbrace>"
  and activate_thread_irq_masks[wp]:
    "activate_thread \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and schedule_irq_masks[wp]:
    "schedule \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
begin

crunch set_extra_badge
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps dmo_wp)

crunch send_ipc
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps simp: crunch_simps ignore: const_on_failure rule: transfer_caps_loop_pres)

(* Clagged from re_del_domain_sep_inv' -- would Dan's annotations be good here? *)
lemma rec_del_irq_masks':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del] rec_del.simps[simp del]
  shows "s \<turnstile> \<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
             rec_del call
             \<lbrace>\<lambda>a s. (case call of (FinaliseSlotCall x y) \<Rightarrow> y \<or> fst a \<longrightarrow> snd a = NullCap
                                | _ \<Rightarrow> True) \<and>
                    domain_sep_inv False st s \<and> P (irq_masks_of_state s)\<rbrace>,
             \<lbrace>\<lambda>_. domain_sep_inv False st and (\<lambda>s. P (irq_masks_of_state s))\<rbrace>"
proof (induct s arbitrary: rule: rec_del.induct, simp_all only: rec_del_fails hoare_fail_any)
  case (1 slot exposed s) show ?case
    apply (wpsimp wp: empty_slot_domain_sep_inv empty_slot_irq_masks
                      drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp]
                simp: split_def rec_del.simps)
    apply (fastforce intro: spec_strengthen_postE[OF "1.hyps", simplified])
    done
next
  case (2 slot exposed s) show ?case
    apply (simp add: rec_del.simps split del: if_split)
    apply (rule hoare_pre_spec_validE)
     apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
            | simp add: split_def split del: if_split)+
           apply (rule spec_strengthen_postE)
            apply (rule "2.hyps"[simplified], fastforce+)
          apply (rule drop_spec_validE, (wp preemption_point_inv | simp)+)[1]
         apply simp
         apply (rule spec_strengthen_postE)
          apply (rule "2.hyps"[simplified], fastforce+)
        apply (wp finalise_cap_domain_sep_inv_cap get_cap_wp
                  finalise_cap_returns_NullCap[where irqs=False, simplified]
                  drop_spec_validE[OF liftE_wp] set_cap_domain_sep_inv
               | simp split del: if_split
               | wp (once) hoare_drop_imps)+
    apply (blast dest: cte_wp_at_domain_sep_inv_cap)
    done
next
  case (3 ptr bits n slot s) show ?case
    apply (simp add: rec_del.simps)
    apply (wp drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp])
    apply (rule hoare_pre_spec_validE)
     apply (wp drop_spec_validE[OF assertE_wp])
    apply fastforce
    done
next
  case (4 ptr bits n slot s) show ?case
    apply (simp add: rec_del.simps)
    apply (wpsimp wp: drop_spec_validE[OF returnOk_wp] drop_spec_validE[OF liftE_wp]
                      set_cap_domain_sep_inv drop_spec_validE[OF assertE_wp] get_cap_wp)
    apply (rule spec_strengthen_postE[OF "4.hyps", simplified])
     apply (simp add: returnOk_def return_def)
    apply (clarsimp simp: domain_sep_inv_cap_def)
    done
qed

lemma rec_del_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   rec_del call
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>, \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply (rule use_spec)
  apply (rule hoare_pre_spec_validE)
   apply (rule spec_strengthen_postE)
    apply (rule spec_strengthen_errE[OF rec_del_irq_masks'])
    apply auto
  done

lemma cap_delete_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   cap_delete blah
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>,\<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  by (simp add: cap_delete_def) (wpsimp wp: rec_del_irq_masks)

lemma invoke_irq_control_irq_masks:
  "\<lbrace>domain_sep_inv False (st :: 's state) and irq_control_inv_valid ivk\<rbrace>
   invoke_irq_control ivk
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply (cases ivk)
   apply (clarsimp simp: irq_control_inv_valid_def domain_sep_inv_def valid_def)
  apply (clarsimp simp: arch_invoke_irq_control_irq_masks)
  done

end


crunch cancel_ipc
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps simp: crunch_simps)

crunch restart, set_mcpriority
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"

crunch bind_notification, unbind_notification
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: dmo_wp crunch_wps no_irq simp: crunch_simps)

crunch suspend
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"

lemma checked_insert_irq_masks[wp]:
  "check_cap_at a b (check_cap_at c d (cap_insert e f g)) \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  by (wpsimp simp: check_cap_at_def)

crunch cap_move
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"

lemma preemption_point_irq_masks[wp]:
  "preemption_point \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  by (wp preemption_point_inv, simp+)

crunch cancel_badged_sends
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps dmo_wp no_irq unless_wp
   simp: filterM_mapM crunch_simps no_irq_clearMemory
   ignore: filterM)


context IRQMasks_IF_1 begin

lemma cap_revoke_irq_masks':
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
  shows "s \<turnstile> \<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
             cap_revoke slot
             \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>, \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
proof (induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
    apply (subst cap_revoke.simps)
    apply (rule hoare_pre_spec_validE)
     apply (wp "1.hyps")
            apply (wp spec_valid_conj_liftE2 | simp)+
            apply (wp drop_spec_validE[OF valid_validE[OF preemption_point_irq_masks]]
                      drop_spec_validE[OF valid_validE[OF preemption_point_domain_sep_inv]]
                      cap_delete_domain_sep_inv cap_delete_irq_masks
                      drop_spec_validE[OF assertE_wp] drop_spec_validE[OF returnOk_wp]
                      drop_spec_validE[OF liftE_wp]
                      drop_spec_validE[OF  hoare_vcg_conj_liftE1]
                   | simp | wp (once) hoare_drop_imps)+
    apply fastforce
    done
qed

lemmas cap_revoke_irq_masks = use_spec(2)[OF cap_revoke_irq_masks']

lemma finalise_slot_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st\<rbrace>
   finalise_slot p e
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  by (simp add: finalise_slot_def | wp rec_del_irq_masks)+

lemma invoke_cnode_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and valid_cnode_inv ci\<rbrace>
   invoke_cnode ci
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  unfolding invoke_cnode_def
  apply (cases ci)
  by (wpsimp wp: cap_move_irq_masks cap_insert_irq_masks hoare_vcg_all_lift hoare_drop_imps
                 cap_revoke_irq_masks[where st=st] cap_delete_irq_masks[where st=st]
      split_del: if_split)+

crunch handle_fault
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (simp: crunch_simps wp: crunch_wps)

crunch reply_from_kernel
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (simp: crunch_simps wp: crunch_wps)

end


fun irq_of_handler_inv where
  "irq_of_handler_inv (ACKIrq irq) = irq" |
  "irq_of_handler_inv (ClearIRQHandler irq) = irq" |
  "irq_of_handler_inv (SetIRQHandler irq _ _) = irq"

crunch invoke_domain
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"

lemma decode_invocation_IRQHandlerCap:
  "\<lbrace>cte_wp_at ((=) cap) slot\<rbrace>
   decode_invocation label args cap_index slot cap blah
   \<lbrace>\<lambda>rv s. \<forall>x. rv = InvokeIRQHandler x
               \<longrightarrow> (\<exists>a b. cte_wp_at ((=) (IRQHandlerCap (irq_of_handler_inv x))) (a, b) s)\<rbrace>, -"
  apply (simp add: decode_invocation_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc | simp add: o_def)+
       apply (rule hoare_strengthen_postE_R[where Q'="\<top>\<top>"])
        apply wp
       apply (clarsimp simp: uncurry_def)
      apply (wp | wpc | simp add: decode_irq_handler_invocation_def o_def split del: if_split)+
  apply (safe | simp add: op_equal | rule exI[where x="fst slot"] exI[where x="snd slot"])+
  done

lemma handle_yield_irq_masks_of_state[wp]:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False st and invs\<rbrace>
   handle_yield
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  by (wpsimp simp: handle_yield_def)


locale IRQMasks_IF_2 = IRQMasks_IF_1 state_t
  for state_t :: "'s :: state_ext state" +
  assumes do_reply_transfer_irq_masks[wp]:
    "do_reply_transfer sender receiver slot grant \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and arch_perform_invocation_irq_masks[wp]:
    "arch_perform_invocation i \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  and invoke_tcb_irq_masks:
    "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False (st :: 's state) and tcb_inv_wf tinv\<rbrace>
     invoke_tcb tinv
     \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
begin

lemma perform_invocation_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and
    (\<lambda>s. (\<forall>blah. oper = InvokeIRQHandler blah
                 \<longrightarrow> (\<exists>ptr'. cte_wp_at ((=) (IRQHandlerCap (irq_of_handler_inv blah))) ptr' s))) and
    domain_sep_inv False (st :: 's state) and valid_invocation oper\<rbrace>
   perform_invocation blocking calling oper
   \<lbrace>\<lambda>_ s. P (irq_masks_of_state s)\<rbrace>"
  apply (cases oper)
  by (wpsimp wp: invoke_tcb_irq_masks invoke_cnode_irq_masks[where st=st]
                 invoke_irq_control_irq_masks[where st=st]
                 invoke_irq_handler_irq_masks[where st=st]
      | fastforce)+

lemma handle_invocation_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False (st :: 's state) and invs\<rbrace>
   handle_invocation calling blocking
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  apply (simp add: handle_invocation_def ts_Restart_case_helper split_def
                   liftE_liftM_liftME liftME_def bindE_assoc)
  apply (wp hoare_weak_lift_imp syscall_valid perform_invocation_irq_masks[where st=st]
            hoare_vcg_all_lift hoare_vcg_ex_lift decode_invocation_IRQHandlerCap
         | simp add: invs_valid_objs)+
  done

crunch handle_reply
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"

crunch handle_recv
  for irq_masks[wp]: "\<lambda>s. P (irq_masks_of_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma handle_event_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False (st :: 's state) and invs\<rbrace>
   handle_event ev
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  apply ((case_tac ev, rename_tac syscall, case_tac syscall);
         (solves \<open>(simp add: handle_send_def handle_call_def
                   | wp handle_invocation_irq_masks[where st=st]
                        handle_interrupt_irq_masks[where st=st]
                         hoare_vcg_all_lift
                   | wpc
                   | wp (once) hoare_drop_imps)+\<close>)?)
  apply simp
  apply (wp handle_interrupt_irq_masks[where st=st] | wpc | simp)+
   apply (rule_tac Q'="\<lambda>rv s. P (irq_masks_of_state s) \<and> domain_sep_inv False st s \<and>
                             (\<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ)" in hoare_strengthen_post)
    apply wpsimp+
  done

lemma call_kernel_irq_masks:
  "\<lbrace>(\<lambda>s. P (irq_masks_of_state s)) and domain_sep_inv False (st :: 's state) and einvs
                                   and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   call_kernel ev
   \<lbrace>\<lambda>rv s. P (irq_masks_of_state s)\<rbrace>"
  apply (simp add: call_kernel_def)
  apply (wp handle_interrupt_irq_masks[where st=st])+
    apply (rule_tac Q'="\<lambda>rv s. P (irq_masks_of_state s) \<and> domain_sep_inv False st s \<and>
                              (\<forall>x. rv = Some x \<longrightarrow> x \<le> maxIRQ)" in hoare_strengthen_post)
     apply (wp | simp)+
   apply (rule_tac Q="\<lambda>x s. P (irq_masks_of_state s) \<and> domain_sep_inv False st s"
               and F="E" for E in hoare_strengthen_postE)
     apply (rule valid_validE)
     apply (wp handle_event_irq_masks[where st=st] valid_validE[OF handle_event_domain_sep_inv]
            | simp)+
  done

end

end
