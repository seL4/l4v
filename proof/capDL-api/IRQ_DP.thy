(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory IRQ_DP
imports TCB_DP
begin

lemma delete_cap_simple_format:
  "\<lbrace><ptr \<mapsto>c cap \<and>* R>  and K (\<not> ep_related_cap cap)\<rbrace> (\<lambda>s. delete_cap_simple ptr s) \<lbrace>\<lambda>_. <ptr \<mapsto>c NullCap \<and>* R>\<rbrace>"
  apply (clarsimp simp: pred_conj_def)
  apply (rule delete_cap_simple_wp)
done

lemma sep_map_i_cdl_irq: "<irq \<mapsto>irq irq_obj \<and>* R> s \<Longrightarrow> cdl_irq_node s irq = irq_obj"
  apply (clarsimp simp: sep_map_c_def sep_map_irq_def sep_conj_def sep_state_projection_def plus_sep_state_def sep_state_add_def)
  apply (clarsimp simp: map_add_def)
  apply (drule fun_cong[where x=irq])
  apply (clarsimp split: option.splits)
  apply (clarsimp simp: sep_disj_sep_state_def sep_state_disj_def)
  by (metis (lifting) fun_upd_same map_disj_None_left' option.distinct(1))

lemma sep_map_i_map_c:
  "<irq \<mapsto>irq irq_obj \<and>* (irq_obj, 0) \<mapsto>c cap \<and>* R> s \<Longrightarrow>
   <irq \<mapsto>irq irq_obj \<and>* (get_irq_slot irq s \<mapsto>c cap) \<and>* R> s"
 by (frule sep_map_i_cdl_irq, clarsimp simp: get_irq_slot_def)


lemma invoke_irq_handler_clear_handler_wp:
  "\<lbrace>< irq \<mapsto>irq obj \<and>* (obj, 0) \<mapsto>c cap \<and>* R> and K (\<not> ep_related_cap cap)\<rbrace>
      invoke_irq_handler (ClearIrqHandler irq)
   \<lbrace>\<lambda>_. < irq \<mapsto>irq obj \<and>* (obj, 0) \<mapsto>c NullCap \<and>* R> \<rbrace>"
  apply (clarsimp simp: invoke_irq_handler_def, wp)
   apply (sep_wp delete_cap_simple_format[where cap=cap])+
  apply (safe)
   apply (frule sep_map_i_cdl_irq, clarsimp simp: get_irq_slot_def)
   apply (sep_solve)
  apply (clarsimp)
  done

lemma invoke_irq_handler_set_handler_wp:
       "\<lbrace>< irq \<mapsto>irq obj \<and>* (obj, 0) \<mapsto>c cap' \<and>* R> and
         K (\<not> ep_related_cap cap' \<and> \<not> is_untyped_cap cap)\<rbrace>
        invoke_irq_handler (SetIrqHandler irq cap slot)
       \<lbrace>\<lambda>_. < irq \<mapsto>irq obj \<and>* (obj, 0) \<mapsto>c cap \<and>* R> \<rbrace>"
  apply (clarsimp simp: invoke_irq_handler_def, wp)
     apply (wp alternative_wp)
      apply (wp sep_wp: insert_cap_child_wp insert_cap_sibling_wp)+
    apply (sep_wp delete_cap_simple_format[where cap=cap'])+
  apply (safe)
   apply (clarsimp)
   apply (frule sep_map_i_cdl_irq, clarsimp simp: get_irq_slot_def)
   apply (sep_solve)
  apply (clarsimp)
  done

lemma invoke_irq_control_issue_handler_wp:
       "\<lbrace> <(dest_slot) \<mapsto>c cap \<and>* R> \<rbrace>
        invoke_irq_control (IssueIrqHandler irq control_slot dest_slot)
       \<lbrace>\<lambda>_. < (dest_slot) \<mapsto>c (IrqHandlerCap irq) \<and>* R> \<rbrace>"
  apply (clarsimp simp: invoke_irq_control_def, wp sep_wp: insert_cap_child_wp)
  apply (clarsimp)
   apply (sep_safe,sep_solve)
done


lemma decode_invocation_irq_ack_rv':
"\<lbrace>\<lambda>s. P (AckIrq (the $ cdl_cap_irq cap)) s \<rbrace>
decode_irq_handler_invocation cap cap_ref caps (IrqHandlerAckIntent)
\<lbrace>P\<rbrace>, -"
  apply (clarsimp simp: decode_irq_handler_invocation_def)
  apply (wp alternativeE_R_wp)
  apply (clarsimp)
done

lemma decode_invocation_irq_clear_rv':
"\<lbrace>\<lambda>s. P (ClearIrqHandler (the $ cdl_cap_irq cap)) s \<rbrace>
decode_irq_handler_invocation cap cap_ref caps (IrqHandlerClearIntent)
\<lbrace>P\<rbrace>, -"
  apply (clarsimp simp: decode_irq_handler_invocation_def)
  apply (wp alternativeE_R_wp)
  apply (clarsimp)
done

lemma irq_inner_lemma: "\<lbrace>\<lambda>s. P i s \<and> a = (NotificationCap x y z) \<rbrace> case a of NotificationCap x xa xb \<Rightarrow> returnOk () | _ \<Rightarrow> throw \<lbrace>P\<rbrace>, -"
  apply (unfold validE_R_def)
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp)
  apply (wp, clarsimp)
done


(* Move next to hoare_gen_asm_conj *)
lemma validE_R_gen_asm_conj:
  "(P \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>, -) \<Longrightarrow> \<lbrace>\<lambda>s. P' s \<and> P\<rbrace> f \<lbrace>Q\<rbrace>, -"
  by (fastforce simp: validE_R_def validE_def valid_def)


lemma decode_invocation_irq_endpoint_rv':
"\<lbrace>\<lambda>s. P (SetIrqHandler (the $ cdl_cap_irq cap) endpoint_cap endpoint_ptr) s \<and> caps = [(endpoint_cap, endpoint_ptr)]@xs \<and>
  is_ntfn_cap endpoint_cap   \<rbrace>
decode_irq_handler_invocation cap cap_ref caps (IrqHandlerSetEndpointIntent)
\<lbrace>P\<rbrace>, -"
  apply (rule validE_R_gen_asm_conj)
  apply (clarsimp simp: decode_irq_handler_invocation_def)
  apply (wp alternativeE_R_wp | wpc)+
    apply (clarsimp split: cdl_cap.splits, safe)
     apply ((wp throw_on_none_rv)+, clarsimp simp: get_index_def)
  apply simp
  done

lemma decode_irq_control_issue_irq_rv:
"\<lbrace>\<lambda>s. P (IssueIrqHandler irq target_ref (cap_object root_cap, offset index r)) s \<and>
        caps = (root_cap, root_ptr)#xs \<and> (unat depth) \<le> word_bits \<and> 0 < (unat depth) \<and>
         <\<box> (r, (unat depth)) : root_cap index \<mapsto>u cap \<and>* R> s\<rbrace>
           decode_irq_control_invocation target target_ref caps (IrqControlIssueIrqHandlerIntent irq index depth) \<lbrace>P\<rbrace>, -"
  apply (clarsimp simp: decode_irq_control_invocation_def)
  apply (wp alternativeE_R_wp lookup_slot_for_cnode_op_rvu'[where cap=cap and r=r] throw_on_none_rv)
  apply (clarsimp simp: get_index_def)
  apply (sep_solve)
done

schematic_goal lookup_extra_caps_once_wp: "\<lbrace>?P\<rbrace> lookup_extra_caps root_tcb_id [endpoint_cptr] \<lbrace>Q\<rbrace>, \<lbrace>Q'\<rbrace>"
apply (clarsimp simp: lookup_extra_caps_def mapME_def sequenceE_def, wp)
   apply (rule lookup_cap_and_slot_rvu)
done

lemma reset_cap_cdl_cap_irq: "reset_cap_asid c = IrqHandlerCap irq \<Longrightarrow> the (cdl_cap_irq c) = irq"
  apply (clarsimp simp: reset_cap_asid_def cdl_cap_irq_def the_def split: cdl_cap.splits)
done

lemma not_memory_reset: "\<not> is_memory_cap (reset_cap_asid cap) \<Longrightarrow> reset_cap_asid cap = cap "
  apply (clarsimp simp: is_memory_cap_def reset_cap_asid_def split:cdl_cap.splits)
done

lemma not_ep_related_reset_cap_asid: "reset_cap_asid c = IrqControlCap \<Longrightarrow> \<not>ep_related_cap c"
  apply (clarsimp simp: reset_cap_asid_def ep_related_cap_def split: cdl_cap.splits)
done

lemma reset_cap_asid_control: "reset_cap_asid c = reset_cap_asid cap \<Longrightarrow> is_irqcontrol_cap cap \<Longrightarrow> is_irqcontrol_cap c"
  apply (clarsimp simp: reset_cap_asid_def is_irqcontrol_cap_def split: cdl_cap.splits)
done



(* Note: the cap from the TCB and the cap in the CNode, both pointing to the root CNode, should be different,
   but this breaks the proof.*)
lemma seL4_IRQHandler_IRQControl_Get_helper:
 assumes unify : "irq_cap = IrqHandlerCap irq \<and>
                  target_index = offset node_index root_size \<and>
                  root_index = offset croot root_size \<and>
                  control_index = offset control_cap root_size \<and>
                  target_ptr = (cap_object root_cap, target_index) \<and>
                  control_ptr = (cap_object root_cap, control_index) \<and>
                  root_ptr = (cap_object root_cap, root_index) \<and>
                  root_tcb  = Tcb t"
shows "\<lbrace>\<guillemotleft>root_tcb_id \<mapsto>f root_tcb  \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>* irq \<mapsto>irq obj \<and>*
         cap_object root_cap \<mapsto>f CNode (empty_cnode root_size) \<and>*
         (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cap \<and>*
          control_ptr \<mapsto>c c_cap \<and>* target_ptr \<mapsto>c target_cap \<and>* root_ptr \<mapsto>c root_cap \<and>* R  \<guillemotright>
              and K ( \<not> ep_related_cap c_cap  \<and> one_lvl_lookup root_cap word_bits root_size \<and>
              one_lvl_lookup root_cap (unat node_depth) root_size \<and>
              guard_equal root_cap node_index (unat node_depth) \<and>
              guard_equal root_cap croot word_bits  \<and>
              guard_equal root_cap control_cap word_bits \<and>
              guard_equal root_cap node_index word_bits \<and>
              unat node_depth \<le> word_bits \<and> 0 < unat node_depth \<and>
              is_irqcontrol_cap c_cap \<and> is_cnode_cap root_cap \<and> is_cnode_cap root_cap)\<rbrace>
        seL4_IRQControl_Get control_cap irq croot node_index node_depth
        \<lbrace>\<lambda>fail s. \<guillemotleft> root_tcb_id \<mapsto>f root_tcb \<and>*
       (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
       \<comment> \<open>Root CNode.\<close>
       cap_object root_cap \<mapsto>f CNode (empty_cnode root_size) \<and>*
       \<comment> \<open>Cap to the root CNode.\<close>
       (root_tcb_id, tcb_cspace_slot) \<mapsto>c root_cap \<and>*
       irq \<mapsto>irq obj \<and>* control_ptr \<mapsto>c c_cap \<and>* target_ptr \<mapsto>c irq_cap \<and>* root_ptr \<mapsto>c root_cap \<and>* R\<guillemotright> s\<rbrace>"
  apply (simp add: seL4_IRQControl_Get_def sep_state_projection2_def)
  apply (rule hoare_pre)
   apply (wp do_kernel_op_pull_back)
   apply (rule call_kernel_with_intent_allow_error_helper
                [where check = True and Perror = \<top> and intent_op = "(IrqControlIntent (IrqControlIssueIrqHandlerIntent irq node_index node_depth))" and tcb = t and intent_cptr = control_cap and intent_extra = "[croot]" ,simplified])
                apply (clarsimp)
               apply (rule set_cap_wp[sep_wand_wp])
              apply (rule mark_tcb_intent_error_sep_inv)
             apply (wp (once))
            apply (rule corrupt_ipc_buffer_sep_inv)
           apply (wp (once))
          apply (rule_tac P = "(iv = (InvokeIrqControl $ (IssueIrqHandler irq control_ptr (cap_object root_cap, offset node_index root_size))))" in  hoare_gen_asmEx)
          apply (clarsimp simp: unify)
          apply (wp invoke_irq_control_issue_handler_wp[sep_wand_wp])
         apply (wp set_cap_wp[sep_wand_wp])
        apply (rule_tac P = "c=IrqControlCap" in hoare_gen_asmEx, simp)
        apply (simp add:  decode_invocation_def, wp)
         apply (rule_tac P = "irq_control_intent=IrqControlIssueIrqHandlerIntent irq node_index node_depth" in hoare_gen_asmE, simp)
         apply (wp decode_irq_control_issue_irq_rv[where root_cap=root_cap and root_ptr=root_ptr and xs ="[]" and r = root_size, simplified ])
        apply (simp)
        apply (unfold throw_opt_def get_irq_control_intent_def, simp)
        apply (rule returnOk_wp)
       apply (rule lookup_extra_caps_once_wp[where cap'=root_cap and r=root_size, simplified user_pointer_at_def])
      apply (rule lookup_cap_and_slot_rvu[where cap'=c_cap and r=root_size, simplified user_pointer_at_def])
    apply (wp  hoare_vcg_imp_lift hoare_vcg_all_lift
          update_thread_intent_update)
   apply (clarsimp)
   apply (rule conjI)
    apply (erule allE impE)+
     apply fastforce
    apply (erule conjE allE impE)+
     apply (fastforce)
    apply (clarsimp)
   apply (rule conjI)
    apply (erule allE impE)+
     apply fastforce
    apply (erule conjE allE impE)+
     apply (fastforce)
    apply (clarsimp)
   apply (sep_solve)
  apply (intro impI conjI allI)
        apply (clarsimp)
       apply (clarsimp)
      apply (intro impI conjI allI)
             apply (sep_solve)
           apply (clarsimp simp: unify)
           apply (sep_cancel)+
           apply (intro impI conjI allI)
            apply sep_solve
           apply (clarsimp simp: unify)
           apply sep_solve
          apply (clarsimp simp: unify)
          apply fastforce
         apply (clarsimp simp: unify)
         apply (metis is_cnode_cap_not_memory_cap not_memory_cap_reset_asid')
        apply (clarsimp simp: unify)
        apply fastforce
       apply (clarsimp simp: user_pointer_at_def Let_unfold sep_conj_assoc unify)
       apply sep_solve
      apply (drule reset_cap_asid_control, assumption, clarsimp simp: is_irqcontrol_cap_def)
     apply (clarsimp simp: user_pointer_at_def Let_unfold sep_conj_assoc unify)
     apply sep_solve
    apply (clarsimp simp: unify)
    apply (drule reset_cap_asid_ep_related_cap)
    apply clarsimp
   apply (clarsimp simp: user_pointer_at_def Let_unfold sep_conj_assoc unify)
   apply sep_solve
  apply (clarsimp simp: unify)
  apply sep_solve
done

lemma obj_tcb_simp [simp]:
  "is_tcb tcb \<Longrightarrow> Tcb (obj_tcb tcb) = tcb"
  by (clarsimp simp: obj_tcb_def is_tcb_def split: cdl_object.splits)

lemma seL4_IRQHandler_IRQControl_Get:
  "\<lbrace>\<guillemotleft>root_tcb_id \<mapsto>f root_tcb  \<and>*
    (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
     irq \<mapsto>irq irq_id \<and>*
     cnode_id  \<mapsto>f CNode (empty_cnode root_size) \<and>*
    (cnode_id, control_index) \<mapsto>c IrqControlCap \<and>*
    (cnode_id, root_index) \<mapsto>c cnode_cap \<and>*
    (cnode_id, target_index) \<mapsto>c target_cap \<and>* R\<guillemotright>
     and K (is_tcb root_tcb \<and>
            is_cnode_cap cnode_cap \<and>
            is_cnode_cap cnode_cap \<and>
            cnode_id      = cap_object cnode_cap \<and>
            target_index  = offset node_index root_size \<and>
            root_index    = offset croot root_size \<and>
            control_index = offset control_cap root_size \<and>
            one_lvl_lookup cnode_cap word_bits root_size \<and>
            one_lvl_lookup cnode_cap (unat node_depth) root_size \<and>
            guard_equal cnode_cap node_index (unat node_depth) \<and>
            guard_equal cnode_cap croot word_bits  \<and>
            guard_equal cnode_cap control_cap word_bits \<and>
            guard_equal cnode_cap node_index word_bits \<and>
            unat node_depth \<le> word_bits \<and> 0 < unat node_depth)\<rbrace>
     seL4_IRQControl_Get control_cap irq croot node_index node_depth
  \<lbrace>\<lambda>fail.
    \<guillemotleft>root_tcb_id \<mapsto>f root_tcb \<and>*
    (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    \<comment> \<open>Cap to the root CNode.\<close>
    (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
     irq \<mapsto>irq irq_id \<and>*
    \<comment> \<open>Root CNode.\<close>
     cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
    (cnode_id, control_index) \<mapsto>c IrqControlCap \<and>*
    (cnode_id, root_index) \<mapsto>c cnode_cap \<and>*
    (cnode_id, target_index) \<mapsto>c IrqHandlerCap irq \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm, elim conjE)
  apply (sep_wp seL4_IRQHandler_IRQControl_Get_helper [where t="obj_tcb root_tcb"])
  apply (rule conjI, simp)+
  apply simp
  apply simp
  apply (rule conjI)
   apply sep_solve
  apply (clarsimp simp: is_irqcontrol_cap_def ep_related_cap_def split: cdl_cap.splits)
  done





lemma seL4_IRQHandler_SetEndpoint_wp_helper:
 assumes unify : "irq_cap = IrqHandlerCap irq \<and>
                  offset endpoint_cptr root_size = irq_handler_slot \<and> endpoint_ptr = (cnode_id, irq_handler_slot) \<and>
                  irq_ptr = (cnode_id, offset irq_handler_cap root_size) \<and>
                  root_tcb  = Tcb t \<and>
                  cnode_id = cap_object cnode_cap"

shows "\<lbrace>\<guillemotleft>root_tcb_id \<mapsto>f root_tcb  \<and>* (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>* irq \<mapsto>irq obj \<and>* (obj, 0) \<mapsto>c cap' \<and>*
         cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>* (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap  \<and>* (endpoint_ptr) \<mapsto>c endpoint_cap \<and>* irq_ptr \<mapsto>c irq_cap \<and>* R \<guillemotright>
              and K (\<not> ep_related_cap cap' \<and> \<not> ep_related_cap irq_cap \<and> \<not>is_untyped_cap endpoint_cap \<and> \<not>is_memory_cap endpoint_cap \<and> one_lvl_lookup cnode_cap word_bits root_size \<and>
              guard_equal cnode_cap endpoint_cptr word_bits \<and> is_ntfn_cap endpoint_cap \<and>
              guard_equal cnode_cap irq_handler_cap word_bits \<and>
              is_cnode_cap cnode_cap \<and> is_irqhandler_cap irq_cap  )\<rbrace>
        seL4_IRQHandler_SetEndpoint irq_handler_cap endpoint_cptr
        \<lbrace>\<lambda>fail s. \<guillemotleft> root_tcb_id \<mapsto>f root_tcb \<and>*
       (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*

       \<comment> \<open>Root CNode.\<close>
       cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
       \<comment> \<open>Cap to the root CNode.\<close>
       (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
       (endpoint_ptr) \<mapsto>c endpoint_cap \<and>*
       irq \<mapsto>irq obj \<and>* (obj, 0) \<mapsto>c endpoint_cap \<and>* irq_ptr \<mapsto>c irq_cap \<and>* R\<guillemotright> s\<rbrace>"
  apply (simp add: seL4_IRQHandler_SetEndpoint_def sep_state_projection2_def)
  apply (rule hoare_pre)
   apply (wp do_kernel_op_pull_back)
   apply (rule call_kernel_with_intent_allow_error_helper
                [where check = True and Perror = \<top> and intent_op = "(IrqHandlerIntent IrqHandlerSetEndpointIntent)" and tcb = t and intent_cptr = irq_handler_cap and intent_extra = "[endpoint_cptr]" ,simplified])
                apply (clarsimp)
               apply (rule set_cap_wp[sep_wand_wp])
              apply (rule mark_tcb_intent_error_sep_inv)
             apply (wp (once))
            apply (rule corrupt_ipc_buffer_sep_inv)
           apply (wp (once))
          apply (rule_tac P = "(iv = (InvokeIrqHandler $ SetIrqHandler (the $ cdl_cap_irq irq_cap) endpoint_cap endpoint_ptr))" in  hoare_gen_asmEx)
          apply (clarsimp)
          apply (wp)
          apply (wp sep_wp: invoke_irq_handler_set_handler_wp)
         apply (wp sep_wp: set_cap_wp)
        apply (rule_tac P = "c=irq_cap" in hoare_gen_asmEx, simp)
        apply (simp add: unify decode_invocation_def)
        apply (wp)
         apply (rule_tac P = "x = (IrqHandlerSetEndpointIntent)" in hoare_gen_asmE, simp)
         apply (wp decode_invocation_irq_endpoint_rv'[where endpoint_cap=endpoint_cap and endpoint_ptr = endpoint_ptr and xs = "[]"])
        apply (unfold throw_opt_def get_irq_handler_intent_def, simp)
        apply (rule returnOk_wp)
       apply (rule lookup_extra_caps_once_wp[where cap'=endpoint_cap and r=root_size])
      apply (rule lookup_cap_and_slot_rvu[where cap'=irq_cap and r=root_size])
     apply (wp hoare_vcg_ball_lift hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_all_lift update_thread_intent_update)
    apply (clarsimp)
    apply (rule conjI)
     apply (erule allE impE)+
      apply fastforce
     apply (erule conjE allE impE)+
      apply (fastforce)
     apply (clarsimp)
    apply (rule conjI)
     apply (erule allE impE)+
      apply fastforce
     apply (erule conjE allE impE)+
      apply (fastforce)
     apply (clarsimp)
    apply (sep_solve)
   apply (clarsimp)
   apply (intro impI conjI)
     apply (clarsimp simp: unify)
     apply (intro impI conjI allI)
           apply (sep_solve)
          apply (sep_cancel)+
          apply (intro impI conjI allI)
            apply (sep_cancel)+
            apply (frule reset_cap_cdl_cap_irq )
            apply (clarsimp simp: unify )
            apply (sep_cancel)+
            apply (safe)
            apply (sep_solve)
           apply (sep_cancel)+
           apply (erule sep_map_c_asid_reset'' )
           apply (clarsimp simp: unify the_def )
          apply (clarsimp simp: unify)
         apply (clarsimp simp: not_memory_reset)
         apply (fastforce)
        defer
        apply (clarsimp simp: user_pointer_at_def Let_unfold sep_conj_assoc unify)
        apply (sep_cancel)+
       apply (metis ep_related_cap_reset_simp)
      apply (sep_cancel)+
      apply (clarsimp simp: user_pointer_at_def Let_unfold sep_conj_assoc unify)
      apply sep_solve
     apply (clarsimp simp: unify)
     apply sep_solve
  apply (clarsimp dest!: reset_cap_asid_simps2)
done

lemma seL4_IRQHandler_SetEndpoint_wp:
  "\<lbrace>\<guillemotleft>root_tcb_id \<mapsto>f root_tcb \<and>*
    (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    \<comment> \<open>Root CNode.\<close>
     cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
    \<comment> \<open>Cap to the root CNode.\<close>
    (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
    (cnode_id, endpoint_slot) \<mapsto>c endpoint_cap \<and>*
     irq \<mapsto>irq irq_id \<and>*
    (irq_id, 0) \<mapsto>c old_cap \<and>*
    (cnode_id, irq_handler_slot) \<mapsto>c IrqHandlerCap irq \<and>* R \<guillemotright>
     and K (
     is_tcb root_tcb \<and>
     cnode_id = cap_object cnode_cap \<and>

     is_ntfn_cap endpoint_cap \<and>
     is_cnode_cap cnode_cap \<and>

     \<not> ep_related_cap old_cap \<and>

     one_lvl_lookup cnode_cap word_bits root_size \<and>
     guard_equal cnode_cap endpoint_cptr word_bits \<and>
     guard_equal cnode_cap irq_handler_cptr word_bits \<and>
     offset endpoint_cptr root_size = endpoint_slot \<and>
     offset irq_handler_cptr root_size = irq_handler_slot)\<rbrace>
    seL4_IRQHandler_SetEndpoint irq_handler_cptr endpoint_cptr
  \<lbrace>\<lambda>fail. \<guillemotleft>root_tcb_id \<mapsto>f root_tcb \<and>*
    (root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>*
    \<comment> \<open>Root CNode.\<close>
     cnode_id \<mapsto>f CNode (empty_cnode root_size) \<and>*
    \<comment> \<open>Cap to the root CNode.\<close>
    (root_tcb_id, tcb_cspace_slot) \<mapsto>c cnode_cap \<and>*
    (cnode_id, endpoint_slot) \<mapsto>c endpoint_cap \<and>*
     irq \<mapsto>irq irq_id \<and>*
    (irq_id, 0) \<mapsto>c endpoint_cap \<and>*
    (cnode_id, irq_handler_slot) \<mapsto>c IrqHandlerCap irq \<and>* R\<guillemotright>\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp seL4_IRQHandler_SetEndpoint_wp_helper [where irq_handler_slot=endpoint_slot
                                                     and cap'=old_cap and t="obj_tcb root_tcb"], simp)
  apply (rule pred_conjI)
   apply sep_solve
  apply clarsimp
  apply (case_tac endpoint_cap, simp_all add: is_memory_cap_def cap_type_def)
  apply (case_tac old_cap, simp_all add: ep_related_cap_def cap_type_def)
  done

end
