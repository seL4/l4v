(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Interrupt_DR
imports Ipc_DR
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma decode_irq_control_error_corres:
  "\<not> (\<exists> ui. (Some (IrqControlIntent ui)) = (transform_intent (invocation_type label) args)) \<Longrightarrow>
     dcorres (dc \<oplus> anyrel) \<top> \<top>
      (throwError e)
      (Decode_A.decode_irq_control_invocation label args slot (map fst excaps))"
  apply (unfold decode_irq_control_invocation_def)
  apply (cases "invocation_type label"; simp add: arch_decode_irq_control_invocation_def)
   apply (simp add: transform_intent_def transform_intent_issue_irq_handler_def split: list.splits)
  done

(* Interrupt Control Invocations *)

primrec (nonexhaustive)
  translate_irq_control_invocation :: "Invocations_A.irq_control_invocation \<Rightarrow> cdl_irq_control_invocation"
where
 "translate_irq_control_invocation (IRQControl irq p slot) =
    IssueIrqHandler irq (transform_cslot_ptr slot) (transform_cslot_ptr p)"
(* no equation for arch irq control, because it cannot occur *)

definition
  cdl_irq_control_invocation_relation :: "cdl_irq_control_invocation \<Rightarrow> Invocations_A.irq_control_invocation \<Rightarrow> bool"
where
  "cdl_irq_control_invocation_relation x y \<equiv> x = translate_irq_control_invocation y"

lemma decode_irq_control_corres:
  "\<lbrakk> Some (IrqControlIntent ui) = transform_intent (invocation_type label') args';
     cap = transform_cap cap';
     cap' = cap.IRQControlCap;
     slot = transform_cslot_ptr slot';
     excaps = transform_cap_list excaps' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> cdl_irq_control_invocation_relation)
     \<top>
     (valid_objs and (\<lambda>s. \<forall>e \<in> set excaps'. valid_cap (fst e) s) and valid_global_refs and valid_idle and valid_etcbs)
     (Interrupt_D.decode_irq_control_invocation cap slot excaps ui)
     (Decode_A.decode_irq_control_invocation label' args' slot' (map fst excaps'))"
  apply (unfold Interrupt_D.decode_irq_control_invocation_def Decode_A.decode_irq_control_invocation_def 
                arch_check_irq_def)
  apply (cases "invocation_type label' = IRQIssueIRQHandler")
   apply clarsimp
   apply (simp add: transform_intent_def transform_intent_issue_irq_handler_def
                    split: list.splits)
   apply (rule conjI)
    prefer 2 -- "error case"
    apply clarsimp
    apply (rule corres_guard_imp)
      apply (rule dcorres_alternative_throw)
     apply (rule TrueI)
    apply (rule TrueI)
   apply (clarsimp simp: Let_def)
   apply (rule dcorres_whenE_throwError_abstract')
    apply (rule corres_guard_imp, rule dcorres_alternative_throw)
     apply (rule TrueI)
    apply (rule TrueI)
   apply (rule dcorres_symb_exec_rE)
     apply (rule dcorres_whenE_throwError_abstract')
      apply (rule corres_guard_imp)
        apply (rule dcorres_alternative_throw)
       apply (rule TrueI)
      apply (rule TrueI)
     apply (simp add: get_index_def transform_cap_list_def throw_on_none_def)
     apply (cases "excaps' = []", simp_all)
     apply (rule corres_alternative_throw_splitE)
          apply (rule corres_alternate1)
          apply (rule lookup_slot_for_cnode_op_corres)
             apply simp+
           apply (clarsimp simp: split_def,simp)
         apply (rule corres_throw_skip_r)
           apply (rule corres_alternate1)
           apply (rule corres_returnOk [where P=\<top> and P'=\<top>])
           apply (simp add: cdl_irq_control_invocation_relation_def)
           apply (subst ucast_mask_drop)
            apply simp
           apply simp
          apply wp[1]
         apply simp
        apply (wp+)[3]
     apply simp
     apply (rule hoare_pre, wp)
     apply simp
    apply wp
    apply (cases excaps', auto)[1]
   apply wp[1]
  apply (clarsimp simp: arch_decode_irq_control_invocation_def transform_intent_def)
  apply (rule corres_guard_imp)
    apply (cases ui)
     apply (auto simp: dcorres_alternative_throw)
  done

(* Interrupt Handler Invocations *)

lemma decode_irq_handler_error_corres:
  "\<not> (\<exists> ui. (Some (IrqHandlerIntent ui)) = (transform_intent (invocation_type label') undefined)) \<Longrightarrow>
     dcorres (dc \<oplus> anyrel) \<top> \<top>
      (throwError e)
      (Decode_A.decode_irq_handler_invocation label' x' excaps')"
  by (auto simp: Decode_A.decode_irq_handler_invocation_def transform_intent_def split: list.splits )

primrec
  translate_irq_handler_invocation :: "Invocations_A.irq_handler_invocation \<Rightarrow> cdl_irq_handler_invocation"
where
  "translate_irq_handler_invocation (ACKIrq irq) =
     AckIrq irq"
| "translate_irq_handler_invocation (Invocations_A.SetIRQHandler irq cap slot) =
     SetIrqHandler irq (transform_cap cap) (transform_cslot_ptr slot)"
| "translate_irq_handler_invocation (Invocations_A.ClearIRQHandler irq) =
     ClearIrqHandler irq"


definition
  cdl_irq_handler_invocation_relation :: "cdl_irq_handler_invocation \<Rightarrow> Invocations_A.irq_handler_invocation \<Rightarrow> bool"
where
  "cdl_irq_handler_invocation_relation x y \<equiv> x = translate_irq_handler_invocation y"

lemma decode_irq_handler_corres:
  "\<And> slot. \<lbrakk> Some (IrqHandlerIntent ui) = transform_intent (invocation_type label') args';
     cap = transform_cap (Structures_A.IRQHandlerCap x');
     excaps = transform_cap_list excaps' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> cdl_irq_handler_invocation_relation) \<top> \<top>
     (Interrupt_D.decode_irq_handler_invocation cap slot excaps ui)
     (Decode_A.decode_irq_handler_invocation label' x' excaps')"
  apply (unfold Interrupt_D.decode_irq_handler_invocation_def Decode_A.decode_irq_handler_invocation_def)
  apply (cases "invocation_type label' = IRQAckIRQ")
   apply (simp add: transform_intent_def cdl_cap_irq_def assert_opt_def
                    returnOk_liftE[symmetric])
   apply (rule corres_alternate1)
   apply (rule dcorres_returnOk)
   apply (simp add: cdl_irq_handler_invocation_relation_def
                    translate_irq_handler_invocation_def)
  apply (cases "invocation_type label' = IRQSetIRQHandler")
   apply (simp add: transform_intent_def cdl_cap_irq_def)
   apply (rule conjI)
    prefer 2 -- "excaps' = []"
    apply (clarsimp intro!: corres_alternate2)
   apply (clarsimp simp: neq_Nil_conv)
   apply (rule conjI)
    prefer 2
    apply (clarsimp intro!: corres_alternate2)
   apply clarsimp
   apply (rule corres_alternate1)
   apply (simp add: get_index_def transform_cap_list_def
                    throw_on_none_def assert_opt_def
                    returnOk_liftE[symmetric])
   apply (clarsimp simp: is_cap_simps)
   apply (rule dcorres_returnOk)
   apply (simp add: cdl_irq_handler_invocation_relation_def
                    translate_irq_handler_invocation_def)
  apply (cases "invocation_type label' = IRQClearIRQHandler")
   apply (simp add: transform_intent_def cdl_cap_irq_def assert_opt_def
                    returnOk_liftE[symmetric])
   apply (rule corres_alternate1)
   apply (rule dcorres_returnOk)
   apply (simp add: cdl_irq_handler_invocation_relation_def
                    translate_irq_handler_invocation_def)
  apply (cases ui, auto simp: dcorres_alternative_throw)
  done

lemma option_get_cap_corres:
  "ptr' = transform_cslot_ptr ptr \<Longrightarrow>
   dcorres (\<lambda>rv rv'. rv = Some (transform_cap rv')) \<top>
   (valid_idle and not_idle_thread (fst ptr) and valid_etcbs)
     (gets (KHeap_D.opt_cap ptr'))
     (CSpaceAcc_A.get_cap ptr)"
  apply (case_tac ptr)
  apply (clarsimp simp:CSpaceAcc_A.get_cap_def[simplified tcb_cnode_map_def] gets_def get_object_def gets_the_def bind_assoc)
  apply (rule dcorres_get)
  apply (clarsimp simp:assert_def corres_free_fail assert_opt_def)
  apply (case_tac y)
      apply (simp_all add:assert_def corres_free_fail)
   apply (rename_tac "fun")
   apply (case_tac "fun b")
    apply (simp add:corres_free_fail)
   apply clarsimp
   apply (subst cap_slot_cnode_property_lift, assumption, simp_all)[1]
    apply fastforce
   apply (clarsimp simp: transform_cap_def)
  apply (clarsimp simp:transform_tcb_slot_simp[simplified])
  apply (rename_tac tcb)
  apply (subgoal_tac "get_tcb a x = Some tcb")
   apply (frule(1) valid_etcbs_get_tcb_get_etcb)
   apply (clarsimp simp:lift_simp not_idle_thread_def)
  apply (clarsimp simp: get_tcb_def)
  done

lemma maskInterrupt_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> maskInterrupt a x \<lbrace>\<lambda>x ms. underlying_memory ms = m\<rbrace>"
  by (simp add:maskInterrupt_def | wp)+

lemma ackInterrupt_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> ackInterrupt x \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  by (simp add:ackInterrupt_def | wp)+

lemma resetTimer_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> resetTimer \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  apply (simp add:resetTimer_def machine_op_lift_def)
  apply (simp add:machine_rest_lift_def ignore_failure_def split_def)
  apply wp
  apply (clarsimp simp:valid_def simpler_modify_def)
  done

lemma valid_state_get_cap_wp:
  "\<lbrace>valid_state\<rbrace> CSpaceAcc_A.get_cap xa \<lbrace>\<lambda>rv s. (is_ntfn_cap rv \<longrightarrow> ntfn_at (obj_ref_of rv) s)\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: is_cap_simps)
  apply (drule cte_wp_valid_cap)
   apply (fastforce simp: valid_state_def)
  apply (clarsimp simp: valid_cap_def)
  done

lemma handle_interrupt_corres_branch:
  "dcorres dc \<top> \<top> (return ())
             (do y \<leftarrow> do_machine_op (maskInterrupt True x);
                 do_machine_op (ackInterrupt x)
              od)"
   apply (rule corres_dummy_return_pl)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF _ dcorres_machine_op_noop])
       apply (clarsimp simp:dc_def[symmetric])
       apply (rule dcorres_machine_op_noop)
   apply (wp|clarsimp)+
done

lemma irq_state_IRQSignal_NullCap:
  "\<lbrakk> caps_of_state s (interrupt_irq_node s irq, []) \<noteq> None;
     interrupt_states s irq \<noteq> irq_state.IRQSignal;
     if_unsafe_then_cap s; valid_global_refs s;
     valid_irq_node s; valid_irq_handlers s \<rbrakk>
      \<Longrightarrow> caps_of_state s (interrupt_irq_node s irq, []) = Some cap.NullCap"
  apply (rule ccontr, clarsimp)
  apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
    apply simp
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (frule(1) valid_global_refsD2)
  apply (case_tac cap, simp_all add: cap_range_def global_refs_def)
  apply (safe, simp_all)
  apply (clarsimp simp: valid_irq_node_def inj_on_eq_iff[where f="interrupt_irq_node s"])
  apply (simp add: valid_irq_handlers_def)
  apply (drule bspec, erule ranI)
  apply (simp add: irq_issued_def)
  done

lemma transform_domain_time_update[iff]:
  "transform (s\<lparr>domain_time := a\<rparr>) = transform s"
  by (auto simp: transform_def transform_cdt_def transform_current_thread_def transform_asid_table_def transform_objects_def)

lemma dec_domain_time_transform: "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> dec_domain_time \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  by (clarsimp simp: dec_domain_time_def | wp)+

lemma thread_set_time_slice_transform: "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> thread_set_time_slice tptr time \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (clarsimp simp: thread_set_time_slice_def ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: transform_def transform_objects_def transform_cdt_def transform_current_thread_def transform_asid_table_def)
  apply (rule_tac y="\<lambda>ptr. map_option (transform_object (machine_state s) ptr ((ekheap s |` (- {idle_thread s})) ptr)) ((kheap s |` (- {idle_thread s})) ptr)" in arg_cong)
  apply (rule ext)
  apply (rule_tac y="transform_object (machine_state s) ptr ((ekheap s |` (- {idle_thread s})) ptr)" in arg_cong)
  apply (rule ext)
  apply (clarsimp simp: transform_object_def transform_tcb_def restrict_map_def get_etcb_def split: option.splits Structures_A.kernel_object.splits)
  done

lemma timer_tick_dcorres: "dcorres dc P P' (return ()) timer_tick"
  apply (rule corres_noop)
   apply (simp add: timer_tick_def reschedule_required_def set_scheduler_action_def etcb_at_def split: option.splits | wp tcb_sched_action_transform dec_domain_time_transform thread_set_time_slice_transform | wpc | wp_once hoare_vcg_all_lift hoare_drop_imps)+
  done

lemma handle_interrupt_corres:
  "dcorres dc \<top> (invs and valid_etcbs) (Interrupt_D.handle_interrupt x) (Interrupt_A.handle_interrupt x)"
  including no_pre
  apply (clarsimp simp:Interrupt_A.handle_interrupt_def)
  apply (clarsimp simp:get_irq_state_def gets_def bind_assoc)
  apply (rule conjI; rule impI)
   apply (subst Interrupt_D.handle_interrupt_def, simp)
   apply (subst Retype_AI.do_machine_op_bind)
     apply (rule maskInterrupt_empty_fail)
    apply (rule ackInterrupt_empty_fail)
   using corres_guard2_imp handle_interrupt_corres_branch apply blast
  apply (rule dcorres_absorb_get_r)+
  apply (clarsimp split:irq_state.splits simp:corres_free_fail | rule conjI)+
   apply (simp add:Interrupt_D.handle_interrupt_def bind_assoc)
   apply (rule corres_guard_imp)
     apply (rule_tac Q'="op=s'" in corres_split[OF _ dcorres_get_irq_slot])
       apply (rule_tac R'="\<lambda>rv.  (\<lambda>s. (is_ntfn_cap rv \<longrightarrow> ntfn_at (obj_ref_of rv) s)) and invs and valid_etcbs"
          in corres_split[OF _ option_get_cap_corres])
          apply (case_tac rv'a)
                     prefer 4
                     apply (simp_all add:when_def)
                  apply (clarsimp simp:transform_cap_def when_def is_ntfn_cap_def | rule conjI)+
                   apply (rule corres_dummy_return_l)
                   apply (rule corres_underlying_split [where P'="\<lambda>rv. \<top>" and P = "\<lambda>rv. \<top>"])
                      apply (rule corres_guard_imp[OF send_signal_corres])
                        apply (simp+)
                   apply (clarsimp simp:handle_interrupt_corres_branch dc_def[symmetric])+
                  apply (simp add: corres_guard_imp[OF handle_interrupt_corres_branch])+
       apply (clarsimp simp:transform_cap_def when_def is_ntfn_cap_def
                   split:arch_cap.splits)+
           apply (simp add: corres_guard_imp[OF handle_interrupt_corres_branch])+
      apply (wp valid_state_get_cap_wp|simp add:get_irq_slot_def)+
    apply (clarsimp simp:invs_def )
    apply (rule irq_node_image_not_idle,simp_all add:valid_state_def)
   apply (simp add:invs_def valid_state_def)
  apply (clarsimp simp:Interrupt_D.handle_interrupt_def gets_def)
  apply (rule conjI; rule impI)
   apply (rule dcorres_absorb_get_l)+
   apply (clarsimp simp:CSpace_D.get_irq_slot_def)
   apply (subgoal_tac "caps_of_state s'b (interrupt_irq_node s'b x,[])\<noteq> None")
    apply (drule irq_state_IRQSignal_NullCap)
         apply ((simp add:invs_def valid_state_def)+)
    apply (frule caps_of_state_transform_opt_cap)
      apply clarsimp
     apply clarsimp
     apply (drule(1) irq_node_image_not_idle[where y = x])
     apply (clarsimp simp:not_idle_thread_def)
    apply (clarsimp simp:transform_cslot_ptr_def)
    apply (subgoal_tac "cdl_irq_node (transform s'b) x = (interrupt_irq_node s'b x)")
     apply clarsimp
     apply (rule corres_guard_imp,rule corres_dummy_return_pl)
       apply (simp add: bind_assoc)
       apply (rule dcorres_rhs_noop_above[OF timer_tick_dcorres])
       apply (rule dcorres_symb_exec_r[OF dcorres_machine_op_noop])
       apply (wp dmo_dwp hoare_TrueI| simp)+
   apply (clarsimp simp:transform_def invs_def valid_state_def dest!: valid_irq_node_cte_at_irq_slot)+
   apply (simp add:cte_wp_at_caps_of_state)
  apply (rule dcorres_absorb_get_l)+
  apply (clarsimp simp:CSpace_D.get_irq_slot_def handle_reserved_irq_def)
  apply (subgoal_tac "caps_of_state s'b (interrupt_irq_node s'b x,[])\<noteq> None")
   apply (drule irq_state_IRQSignal_NullCap)
        apply ((simp add:invs_def valid_state_def)+)
   apply (frule caps_of_state_transform_opt_cap)
     apply clarsimp
    apply clarsimp
    apply (drule(1) irq_node_image_not_idle[where y = x])
    apply (clarsimp simp:not_idle_thread_def)
   apply (clarsimp simp:transform_cslot_ptr_def)
   apply (subgoal_tac "cdl_irq_node (transform s'b) x = (interrupt_irq_node s'b x)")
    apply clarsimp
    apply (rule corres_guard_imp)
      apply (rule dcorres_machine_op_noop)
      apply wp
   apply (clarsimp simp:transform_def invs_def valid_state_def dest!: valid_irq_node_cte_at_irq_slot)+
  apply (simp add:cte_wp_at_caps_of_state)
  done

lemma set_irq_state_original:
  "\<lbrace>\<lambda>s. P (is_original_cap s slot)\<rbrace> set_irq_state a b
         \<lbrace>\<lambda>rv s. P (is_original_cap s slot)\<rbrace>"
  by (clarsimp simp:set_irq_state_def | wp)+

lemma set_irq_state_dwp:
  "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace>
         set_irq_state irq_state.IRQSignal word \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (simp add:set_irq_state_def)
  apply (wp do_machine_op_wp)
    apply clarsimp
    apply (wp maskInterrupt_underlying_memory)+
  apply (clarsimp simp:transform_def transform_objects_def transform_cdt_def
                       transform_current_thread_def transform_asid_table_def)
  done

lemma dcorres_invoke_irq_control:
  "dcorres dc \<top> (invs and irq_control_inv_valid irq_control_invocation and valid_etcbs)
    (Interrupt_D.invoke_irq_control (translate_irq_control_invocation irq_control_invocation))
    (Interrupt_A.invoke_irq_control irq_control_invocation)"
  apply (case_tac irq_control_invocation)
   apply (simp_all add:arch_invoke_irq_control_def corres_free_fail)
  apply (rename_tac word p1 p2)
  apply (clarsimp simp:liftE_def bind_assoc)
  apply (rule dcorres_symb_exec_r_strong)
    apply (simp add:Interrupt_D.invoke_irq_control_def)
    apply (rule corres_dummy_return_l)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF corres_trivial])
         apply (rule corres_free_return)
        apply (subgoal_tac "IrqHandlerCap word = transform_cap (cap.IRQHandlerCap word)")
         apply (simp only:)
         apply (rule insert_cap_child_corres)
        apply (simp add:transform_cap_def)
       apply (wp|clarsimp)+
    apply simp
   apply (simp add:valid_cap_def cap_aligned_def word_bits_def)
   apply (rule hoare_pre)
    apply (rule hoare_vcg_conj_lift)
     apply (rule_tac Q = "\<lambda>r s. cte_wp_at (op = cap.IRQControlCap) (aa,ba) s
        \<and> is_original_cap s (aa, ba)" in hoare_strengthen_post)
      apply (wp set_irq_state_cte_wp_at set_irq_state_original)
     apply (simp add:cte_wp_at_def should_be_parent_of_def)
    apply (simp add: not_idle_thread_def)
    apply wp
    apply (strengthen invs_valid_idle invs_mdb)
    apply (wp set_irq_state_invs)
   apply (clarsimp simp:invs_def valid_state_def valid_pspace_def)
   apply (rule conjI)
    apply (clarsimp simp:cte_wp_at_caps_of_state)
    apply (erule irq_revocableD)
    apply (simp add:caps_of_state_cteD invs_def valid_state_def valid_pspace_def valid_mdb_def)
   apply (rule conjI)
    apply (drule ex_cte_cap_wp_to_not_idle, auto simp: not_idle_thread_def)[1]
   apply (drule_tac p = "(aa,ba)" in if_unsafe_then_capD)
     apply clarsimp
    apply simp
   apply (drule_tac r = "(aa,ba)" in ex_cte_cap_wp_to_not_idle)
       apply (clarsimp simp:not_idle_thread_def)+
  apply (wp set_irq_state_dwp,simp)
  done

lemma op_eq_simp: "(op = y) = (\<lambda>x. x = y)" by auto

lemma get_irq_slot_not_idle_wp:
  "\<lbrace>valid_idle and valid_irq_node \<rbrace> KHeap_A.get_irq_slot word \<lbrace>\<lambda>rv. not_idle_thread (fst rv)\<rbrace>"
  apply (clarsimp simp:get_irq_slot_def)
  apply (rule irq_node_image_not_idle)
   apply simp+
  done

lemma get_irq_slot_ex_cte_cap_wp_to:
  "\<lbrace>\<lambda>s. valid_irq_node s \<and> (\<exists>slot. cte_wp_at (op = (cap.IRQHandlerCap w)) slot s)\<rbrace> KHeap_A.get_irq_slot w
           \<lbrace>\<lambda>rv s. (ex_cte_cap_wp_to (\<lambda>a. True) rv s) \<rbrace>"
  apply (clarsimp simp:get_irq_slot_def)
  apply (clarsimp simp:ex_cte_cap_wp_to_def valid_irq_node_def)
  apply (rule exI)+
  apply (erule cte_wp_at_weakenE)
  apply clarsimp
  done

crunch is_original[wp] : fast_finalise "\<lambda>s. is_original_cap s slot"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps)

lemma cap_delete_one_original:
  "slot \<noteq> slot' \<Longrightarrow> \<lbrace>\<lambda>s. is_original_cap s slot\<rbrace> cap_delete_one slot'
            \<lbrace>\<lambda>r s. is_original_cap s slot\<rbrace>"
  apply (clarsimp simp:cap_delete_one_def unless_def)
  apply (wp hoare_when_wp)
     apply (clarsimp simp:empty_slot_def)
     apply wp
         apply (clarsimp simp:set_cdt_def)
         apply (wp dxo_wp_weak | clarsimp)+
  done

lemma cte_wp_at_neq_slot_set_cap:
  "slot\<noteq> slot'  \<Longrightarrow> \<lbrace>cte_wp_at P slot and cte_at slot'\<rbrace>
            CSpaceAcc_A.set_cap cap.NullCap slot' \<lbrace>\<lambda>rv. cte_wp_at P slot\<rbrace>"
  apply (wp set_cap_cte_wp_at_cases)
  apply (clarsimp simp:cte_wp_at_def)
  done

lemma cte_wp_at_neq_slot_cap_delete_one:
  "slot\<noteq> slot' \<Longrightarrow> \<lbrace>cte_wp_at P slot\<rbrace> cap_delete_one slot'
            \<lbrace>\<lambda>rv. cte_wp_at P slot\<rbrace>"
  apply (clarsimp simp:cap_delete_one_def unless_def)
  apply (wp hoare_when_wp)
      apply (clarsimp simp:empty_slot_def)
      apply (wp cte_wp_at_neq_slot_set_cap)
           apply clarsimp
           apply (wp dxo_wp_weak | simp)+
         apply (clarsimp simp:set_cdt_def)
         apply (wp | clarsimp)+
      apply (rule_tac Q = "\<lambda>r s. cte_wp_at P slot s \<and> cte_at slot' s" in hoare_strengthen_post)
       apply (rule hoare_vcg_conj_lift)
        apply wp_once
       apply (wp get_cap_cte)
      apply (clarsimp|wp)+
  done

lemma cap_delete_one_not_idle [wp]:
  "\<lbrace>not_idle_thread t\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_. not_idle_thread t\<rbrace>"
  apply (simp add: not_idle_thread_def)
  apply wp
  done

lemma is_ntfn_capD:
  "is_ntfn_cap cap \<Longrightarrow> \<exists>ptr b rights. cap = cap.NotificationCap ptr b rights"
  by (case_tac cap,simp_all)

lemma dcorres_invoke_irq_handler:
  "dcorres dc \<top> (invs and irq_handler_inv_valid irq_handler_invocation and valid_etcbs)
          (Interrupt_D.invoke_irq_handler
            (translate_irq_handler_invocation irq_handler_invocation))
          (Interrupt_A.invoke_irq_handler irq_handler_invocation)"
  apply (case_tac irq_handler_invocation)
(* ACKIrq *)
    apply (clarsimp simp:Interrupt_D.invoke_irq_handler_def)
    apply (rule corres_dummy_return_r)
    apply (rule dcorres_symb_exec_r_strong)
      apply (rule corres_free_return[where P'=\<top> ])
     apply wp
    apply (wp do_machine_op_wp,clarsimp)
     apply (wp maskInterrupt_underlying_memory|clarsimp simp:Interrupt_D.invoke_irq_handler_def)+
   (* SetIRQHandler *)
   apply (rule dcorres_expand_pfx)
   apply (clarsimp dest!:is_ntfn_capD simp:valid_cap_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF _ dcorres_get_irq_slot])
       apply (rule_tac F="irq_slot\<noteq> (a,b)" in corres_gen_asm2)
       apply simp
       apply (rule corres_split[OF _ delete_cap_simple_corres])
         apply (subst alternative_com)
         apply (rule dcorres_insert_cap_combine,simp)
        apply wp
       apply (wp delete_one_deletes[unfolded op_eq_simp[symmetric]])
       apply (wp cte_wp_at_neq_slot_cap_delete_one)
        apply simp
       apply (wp cte_wp_at_neq_slot_cap_delete_one)
       apply (strengthen invs_valid_idle invs_valid_objs)
       apply (wp delete_one_invs)
     apply (simp add:valid_cap_def)
     apply (wp get_irq_slot_not_idle_wp get_irq_slot_ex_cte_cap_wp_to)
     apply (wp get_irq_slot_different get_irq_slot_not_idle_wp)
    apply simp+
   apply (clarsimp simp:invs_valid_idle invs_irq_node interrupt_derived_def)
   apply (frule_tac p = "(a,b)" in if_unsafe_then_capD)
     apply clarsimp+
    apply (clarsimp simp: cte_wp_at_caps_of_state invs_valid_global_refs is_cap_simps
                          cap_master_cap_simps interrupt_derived_def dest!:cap_master_cap_eqDs)+
   apply (drule ex_cte_cap_wp_to_not_idle)
       apply clarsimp+
  (* ClearIRQHandler *)
  apply (clarsimp simp: Interrupt_D.invoke_irq_handler_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ dcorres_get_irq_slot])
      apply (clarsimp)
      apply (rule delete_cap_simple_corres)
     apply (wp get_irq_slot_not_idle_wp,clarsimp)+
  apply (clarsimp simp:invs_def valid_state_def)
  done

end

end
