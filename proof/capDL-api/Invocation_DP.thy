(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Invocation_DP
imports KHeap_DP RWHelper_DP
begin

crunch cdl_current_domain[wp]: update_available_range, generate_object_ids, update_thread,
                               mark_tcb_intent_error, corrupt_ipc_buffer, insert_cap_sibling,
                               insert_cap_child, move_cap, invoke_irq_control, invoke_irq_handler
                                                    "\<lambda>s. P (cdl_current_domain s)"
(wp: crunch_wps unless_wp simp: split_def corrupt_intents_def)

crunch cdl_irq_node [wp]:  corrupt_ipc_buffer "\<lambda>s. P (cdl_irq_node s)"
(wp: crunch_wps simp: corrupt_intents_def)
crunch cdl_irq_node [wp]:  mark_tcb_intent_error "\<lambda>s. P (cdl_irq_node s)"
(wp: crunch_wps)

lemma all_scheduable_tcbs_corrupt[simp]:
  "all_scheduable_tcbs (cdl_objects (corrupt_intents xa x s)) = all_scheduable_tcbs (cdl_objects s)"
  apply (simp add:all_scheduable_tcbs_def object_at_heap_def)
  apply (intro set_eqI iffI)
   apply (clarsimp simp:corrupt_intents_def tcb_scheduable_def
     split:option.splits cdl_object.splits if_splits)
  apply (clarsimp simp:corrupt_intents_def
    map_add_def tcb_scheduable_def)
  done

lemma single_scheduable_tcb:
  "all_scheduable_tcbs (cdl_objects s) = {cur_thread}
  \<Longrightarrow> \<exists>tcb. cdl_objects s cur_thread = Some tcb \<and> (
    (object_slots tcb) tcb_pending_op_slot = Some RunningCap
    \<or> (object_slots tcb) tcb_pending_op_slot = Some RestartCap)"
  by (fastforce simp: all_scheduable_tcbs_def slots_of_def
                      tcb_scheduable_def object_slots_def opt_cap_def
                      object_at_heap_def
               dest!: singleton_eqD)

(*FIXME: dup *)
lemma intent_reset_projection[simp]:
  "intent_reset (intent_reset a) = intent_reset a"
  by (simp add:intent_reset_def split:cdl_object.splits)

lemma asid_reset_intent_reset_switch:
  "asid_reset (intent_reset x) = intent_reset (asid_reset x)"
  apply (cut_tac object_clean_def2[unfolded Fun.comp_def,simplified,symmetric])
  apply (drule_tac x = x in fun_cong)
  apply (simp add:object_clean_def)
  done

lemma reset_cap_twice[simp]:
  "reset_cap_asid \<circ>\<^sub>M (reset_cap_asid \<circ>\<^sub>M x)
  =  reset_cap_asid \<circ>\<^sub>M x"
  apply (rule ext)
  apply (clarsimp simp:reset_cap_asid_def)
  apply (simp split:cdl_cap.splits option.splits)
  done

lemma asid_reset_twice[simp]:
  "(asid_reset (asid_reset x)) = asid_reset x"
  by (case_tac x,
    simp_all add:asid_reset_def
    update_slots_def object_slots_def)

lemma object_clean_twice[simp]:
  "object_clean (object_clean x) = object_clean x"
  by (clarsimp simp:object_clean_def asid_reset_intent_reset_switch)

(* The following should be correct once we rule the intent out of our lift function *)
lemma sep_nonimpact_valid_lift:
  assumes non_intent_impact:
   "\<And>ptr P A. \<lbrace>\<lambda>s. A (object_at (\<lambda>obj. P (object_clean obj)) ptr s)\<rbrace>
    f \<lbrace>\<lambda>rv s. A (object_at (\<lambda>obj. P (object_clean obj)) ptr s)\<rbrace>"
  assumes non_irq_node_impact:
   "\<And>ptr P A. \<lbrace>\<lambda>s. A (cdl_irq_node s)\<rbrace> f \<lbrace>\<lambda>rv s. A (cdl_irq_node s)\<rbrace>"
  shows
   "\<lbrace>\<lambda>s. < Q >  s\<rbrace> f \<lbrace>\<lambda>rv s. < Q > s\<rbrace>"
  apply (clarsimp simp: valid_def sep_state_projection_def Let_def
                        sep_state_add_def sep_disj_sep_state_def
                        sep_state_disj_def
                        map_option_case
                 split: if_split_asm option.splits sep_state.splits)
  apply (erule rsubst [where P=Q])
  apply clarsimp
  apply (rule conjI)
   apply (rule ext)+
   apply (clarsimp split:option.splits)
   apply (intro conjI impI allI)
    apply (drule_tac P1 ="\<lambda>x. True" and A1 = "\<lambda>x. \<not>x" in use_valid[OF _ non_intent_impact])
     apply (simp add:object_at_def)+
    apply (drule_tac P1 ="\<lambda>x. True" and A1 = "\<lambda>x. x" in use_valid[OF _ non_intent_impact])
    apply (fastforce simp:object_at_def)+
   apply (drule_tac P1 ="\<lambda>x. object_clean x = object_clean x2" and
                    A1 = "\<lambda>x. x" in use_valid[OF _ non_intent_impact])
    apply (fastforce simp:object_at_def)
   apply (clarsimp simp: object_at_def object_slots_object_clean
                         object_project_def
                  split: cdl_component_id.splits)
  apply (rule ext)+
  apply (clarsimp split:option.splits)
  apply (drule_tac A1 = "\<lambda>x. x = (cdl_irq_node s)" in use_valid[OF _ non_irq_node_impact])
   apply simp
  apply simp
  done

lemma mark_tcb_intent_error_sep_inv[wp]:
  "\<lbrace>\<lambda>s. < P >  s\<rbrace>
  mark_tcb_intent_error thread b
  \<lbrace>\<lambda>rv s. < P > s\<rbrace>"
  apply (rule sep_nonimpact_valid_lift)
   apply (simp add:mark_tcb_intent_error_def update_thread_def
     set_object_def)
   apply (wp | wpc | simp add:set_object_def)+
   apply (clarsimp simp: object_at_def object_clean_def intent_reset_def
                         object_slots_def asid_reset_def update_slots_def)
  apply wp
  done

lemma corrupt_tcb_intent_sep_helper[wp]:
  "\<lbrace>\<lambda>s. A (object_at (\<lambda>obj. P (object_clean obj)) ptr s)\<rbrace> corrupt_tcb_intent thread
  \<lbrace>\<lambda>rv s. A (object_at (\<lambda>obj. P (object_clean obj)) ptr s)\<rbrace>"
   apply (simp add:corrupt_tcb_intent_def update_thread_def
     set_object_def)
   apply (wp | wpc | simp add:set_object_def)+
   apply (clarsimp simp:object_at_def)
   apply (simp add:object_clean_def intent_reset_def
     object_slots_def asid_reset_def update_slots_def)
  done


lemma corrupt_tcb_intent_sep_inv[wp]:
  "\<lbrace>\<lambda>s. < P >  s\<rbrace>
  corrupt_tcb_intent thread
  \<lbrace>\<lambda>rv s. < P > s\<rbrace>"
  by (rule sep_nonimpact_valid_lift; wp)

lemma corrupt_frame_sep_helper[wp]:
  "\<lbrace>\<lambda>s. A (object_at (\<lambda>obj. P (object_clean obj)) ptr s)\<rbrace>
  corrupt_frame a \<lbrace>\<lambda>rv s. A (object_at (\<lambda>obj. P (object_clean obj)) ptr s)\<rbrace>"
  apply (simp add:corrupt_frame_def)
  apply wp
  apply (clarsimp simp:corrupt_intents_def object_at_def
    map_add_def split:option.splits cdl_object.splits)
  apply (simp add:object_clean_def intent_reset_def
     object_slots_def asid_reset_def update_slots_def)
  done

crunch inv [wp]:  get_ipc_buffer "P"
(wp: crunch_wps)

lemma corrupt_ipc_buffer_sep_inv[wp]:
  "\<lbrace>\<lambda>s. < P > s\<rbrace>
    corrupt_ipc_buffer cur_thread p
   \<lbrace>\<lambda>rv s. < P > s\<rbrace>"
  apply (rule sep_nonimpact_valid_lift)
   apply (simp add:corrupt_ipc_buffer_def)
   apply (wp hoare_drop_imps | wpc | simp)+
  done

lemma update_thread_intent_update:
  "\<lbrace>\<lambda>s. < P > s\<rbrace>
   update_thread cur_thread (cdl_tcb_intent_update f)
   \<lbrace>\<lambda>rv s. < P > s\<rbrace>"
  apply (rule sep_nonimpact_valid_lift)
   apply (simp add:update_thread_def set_object_def get_thread_def)
   apply (wp  | wpc | simp add:object_at_def
     intent_reset_def set_object_def)+
   apply (simp add:object_clean_def intent_reset_def
     object_slots_def asid_reset_def update_slots_def)
   apply fastforce
  apply wp
  done

(* Following is the helper rules we used to prove properties about do_kernel_op *)

lemma liftE_wp_no_exception:
  "\<lbrakk>\<And>r. \<lbrace>P' r\<rbrace> g r \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>;\<lbrace>P\<rbrace>f\<lbrace>\<lambda>r. P' r\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> liftE f >>=E g \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
  apply (simp add:liftE_bindE validE_def)
  including no_pre apply wp
   apply assumption
  apply simp
  done

lemma handle_event_no_exception:
  "\<lbrace>P\<rbrace> handle_event  (SyscallEvent SysCall) \<lbrace>\<lambda>r. Q\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>
   \<Longrightarrow> \<lbrace>P\<rbrace> handle_event (SyscallEvent SysCall) <handle> handler \<lbrace>\<lambda>r. Q\<rbrace>"
  apply (rule validE_cases_valid)
  including no_pre apply (wp)
   apply (rule hoare_FalseE)
  apply simp
  done

lemma syscall_valid_helper:
  "\<lbrakk> \<And>x xa. \<lbrace>Qa x xa\<rbrace> perform_syscall_fn xa \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>r. Inv\<rbrace>;
     \<And>r. \<lbrace>Qi r\<rbrace>arg_decode_fn r \<lbrace>Qa r\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>;
    \<lbrace>P\<rbrace>cap_decoder_fn \<lbrace>Qi\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>
   \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace>syscall cap_decoder_fn decode_error_handler
    arg_decode_fn arg_error_handler_fn
    perform_syscall_fn
   \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>r. Inv\<rbrace>"
  apply (simp add:syscall_def)
  apply (rule hoare_vcg_handle_elseE)
    apply simp
   apply simp
  apply (rule hoare_vcg_handle_elseE)
    apply fastforce
   apply (rule hoare_FalseE)
  apply auto
  done

lemma no_exception_conj:
  "\<lbrakk>\<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>;\<lbrace>P'\<rbrace>f\<lbrace>Q'\<rbrace>,-\<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace>f\<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
  apply (clarsimp simp add:validE_def validE_R_def valid_def)
  apply (drule_tac x = s in spec)+
  apply clarsimp
  apply (drule(1) bspec)+
  apply (auto split:sum.splits)
  done

lemma no_exception_conj':
  "\<lbrakk>\<lbrace>P'\<rbrace>f\<lbrace>Q\<rbrace>,-; \<lbrace>P\<rbrace>f\<lbrace>Q'\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace>f\<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
  apply (clarsimp simp add:validE_def validE_R_def valid_def)
  apply (drule_tac x = s in spec)+
  apply clarsimp
  apply (drule(1) bspec)+
  apply (auto split:sum.splits)
  done

crunch inv[wp]: decode_untyped_invocation P
  (wp: crunch_wps mapME_x_inv_wp unlessE_wp simp: crunch_simps throw_on_none_def)

crunch inv[wp]: decode_irq_handler_invocation P
  (wp: crunch_wps simp: liftE_bindE throw_on_none_def)

crunch inv[wp]: decode_tcb_invocation P
  (wp: crunch_wps simp: liftE_bindE throw_on_none_def)

crunch inv[wp]: decode_domain_invocation P
  (wp:crunch_wps simp: liftE_bindE throw_on_none_def)

crunch inv[wp]: decode_irq_control_invocation P
  (wp: crunch_wps simp: liftE_bindE throw_on_none_def)

crunch inv[wp]: decode_asid_control_invocation P
  (wp: crunch_wps ignore: returnOk simp: liftE_bindE throw_on_none_def)

crunch inv[wp]: lookup_cap_and_slot P
  (wp:crunch_wps resolve_address_bits_wp)

crunch inv[wp]: decode_page_invocation P
  (wp: crunch_wps resolve_address_bits_wp simp: throw_on_none_def)

lemma decode_page_table_invocation_inv[wp]:
  "\<lbrace>P\<rbrace> decode_page_table_invocation a b c d \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add:decode_page_table_invocation_def)
  apply (rule hoare_pre)
   apply (wpc|wp |simp add:throw_on_none_def)+
  done

lemma decode_page_directory_invocation_inv[wp]:
  "\<lbrace>P\<rbrace> decode_page_directory_invocation a b c d \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add:decode_page_directory_invocation_def)
  apply (rule hoare_pre)
   apply (wpc|wp |simp add:throw_on_none_def)+
  done

lemma decode_asid_pool_invocation_inv[wp]:
  "\<lbrace>P\<rbrace> decode_asid_pool_invocation a b c d \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add:decode_asid_pool_invocation_def)
  apply (rule hoare_pre)
   apply (wpc|wp |simp add:throw_on_none_def)+
  done

lemma decode_invocation_inv[wp]:
  "\<lbrace>P\<rbrace> decode_invocation a b c d\<lbrace>\<lambda>_. P\<rbrace>, -"
  apply (simp add:decode_invocation_def)
  apply (case_tac a,simp_all)
  apply (rule hoare_pre, (wp | simp add:throw_opt_def | wpc | intro conjI impI)+)+
  done

crunch inv[wp]: lookup_extra_caps P
  (wp:crunch_wps mapME_wp' resolve_address_bits_wp ignore: mapME)

lemma nonep_invocation_simps:
  "nonep_invocation (InvokeUntyped a) = True"
  by (simp add:nonep_invocation_def)

lemma decode_invocation_nonep:
  "\<lbrace>\<lambda>s. \<not> ep_related_cap cap \<rbrace>
   decode_invocation cap cap_ref extra_caps intent
   \<lbrace>\<lambda>rv s. nonep_invocation rv\<rbrace>, -"
  apply (simp add: decode_invocation_def)
  apply (wpsimp simp: o_def nonep_invocation_def wp: wp_post_tauts)
  apply (auto simp: ep_related_cap_def)
  done

lemma ep_related_cap_reset_simp[simp]:
  "ep_related_cap (reset_cap_asid x) = ep_related_cap x"
  apply (case_tac x)
  apply (auto simp:reset_cap_asid_def ep_related_cap_def)
  done

lemma liftE_wp_split_r:
  "\<lbrakk>\<And>r. \<lbrace>P' r\<rbrace> g r \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>r. R\<rbrace>;\<lbrace>P\<rbrace>f\<lbrace>\<lambda>r. P' r\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> liftE f >>=E g \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>r. R\<rbrace>"
  apply (simp add:liftE_bindE validE_def)
  including no_pre
  apply wp
   apply assumption
  apply simp
  done

lemma wp_no_exception_seq_r:
  assumes validE_g: "\<And>r. \<lbrace>P' r\<rbrace> g r \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
      and validE_f: "\<lbrace>P\<rbrace>f\<lbrace>\<lambda>r. P' r\<rbrace>,\<lbrace>\<lambda>r. Inv\<rbrace>"
  shows "\<lbrace>P\<rbrace> f >>=E g \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>r. Inv\<rbrace>"
  apply (rule hoare_pre)
  apply (rule bindE_wp)
    apply (rule hoare_strengthen_postE[OF validE_g])
     apply simp
    apply simp
   apply (wp validE_f)
  apply simp
  done

lemmas
  wp_no_exception_seq = wp_no_exception_seq_r[where Inv = "\<lambda>s. False"]

lemma handle_event_syscall_no_decode_exception:
  assumes set_cap_hold: "\<lbrace>Rm \<rbrace>set_cap (cur_thread, tcb_pending_op_slot) RunningCap \<lbrace>\<lambda>r. Q\<rbrace>"

  and decode_invocation_no_exception:
      "\<And>c ref cs. \<lbrace> Pd cs c ref \<rbrace> decode_invocation c ref cs intent_op
       \<lbrace> Ps \<rbrace>, \<lbrace>\<lambda>xa s. False\<rbrace>"
  and lookup_extra_caps_exec:
  "\<And>r. \<lbrace> Pd1 (fst r) (snd r) \<rbrace> lookup_extra_caps cur_thread  intent_extra
       \<lbrace> \<lambda>xa s. Pd xa (fst r) (snd r) s \<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
  and lookup_cap_and_slot_exec:
      "\<lbrace> Pd2 \<rbrace> lookup_cap_and_slot cur_thread intent_cptr
       \<lbrace> \<lambda>r s. Pd1 (fst r) (snd r) s \<and> \<not> ep_related_cap (fst r) \<rbrace>, \<lbrace>\<lambda>y s. False \<rbrace>"

  and  non_ep_cap:
      "\<lbrace> Pd2 \<rbrace> lookup_cap_and_slot cur_thread intent_cptr
       \<lbrace> \<lambda>rv s. \<not> ep_related_cap (fst rv) \<rbrace>, -"
  and mark_tcb_intent_error_hold: "\<lbrace> Ra \<rbrace>mark_tcb_intent_error cur_thread False \<lbrace>\<lambda>r. Rm\<rbrace>"
  and corrupt_ipc_buffer_hold: "\<lbrace> Rb \<rbrace>corrupt_ipc_buffer cur_thread True \<lbrace>\<lambda>r. Ra\<rbrace>"
  and perform_invocation_hold: "\<And>iv. \<lbrace>PIV iv\<rbrace> perform_invocation True True iv
    \<lbrace>\<lambda>rv s. Rb s \<and> <(cur_thread, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* sep_true > s\<rbrace>, \<lbrace>\<lambda>r. Inv'\<rbrace>"
  and set_restart_cap_hold: "\<And>iv. \<lbrace>Ps iv\<rbrace> set_cap (cur_thread, tcb_pending_op_slot) RestartCap \<lbrace>\<lambda>r. PIV iv\<rbrace>"
  shows "\<lbrace>(\<lambda>s. cdl_current_thread s = Some cur_thread)
   and Pd2
   and tcb_at'
     (\<lambda>tcb. cdl_intent_op (cdl_tcb_intent tcb) = Some intent_op \<and>
            cdl_intent_cap (cdl_tcb_intent tcb) = intent_cptr \<and>
            cdl_intent_extras (cdl_tcb_intent tcb) = intent_extra) cur_thread
   \<rbrace> handle_event (SyscallEvent SysCall)
   \<lbrace>\<lambda>r. Q\<rbrace>,\<lbrace>\<lambda>y. Inv'\<rbrace>"
  apply (simp add:handle_event_def handle_syscall_def handle_invocation_def)
  apply (rule liftE_wp_split_r)+
    apply (rule syscall_valid_helper)
      apply (rule liftE_wp_split_r)+
       apply (rule wp_no_exception_seq_r)
        apply (rule liftE_wp_no_exception)
         apply (rule whenE_wp)
         apply simp
         apply wp
           apply (rule_tac P = "y = cur_thread" in hoare_gen_asm)
           apply simp
           apply (rule set_cap_hold)
          apply (rule_tac P = "y = cur_thread" in hoare_gen_asm)
          apply simp
          apply (rule mark_tcb_intent_error_hold)
         apply (rule_tac P = "y = cur_thread" in hoare_gen_asm)
         apply simp
         apply (rule corrupt_ipc_buffer_hold)
        apply (wp has_restart_cap_sep_wp[where cap = RestartCap])[1]
       apply (rule_tac P = "y = cur_thread" in hoare_gen_asmEx)
       apply (simp add:conj_comms)
       apply (rule perform_invocation_hold)
      apply (rule_tac P = "y = cur_thread" in hoare_gen_asm)
      apply simp
      apply (wp hoare_vcg_conj_lift set_restart_cap_hold)[1]
     apply (rule_tac P = " \<not> ep_related_cap (fst yb)
       \<and> cdl_intent_op (cdl_tcb_intent ya) = Some intent_op \<and> y = cur_thread"
       in hoare_gen_asmEx)
     apply (simp add:split_def)
     apply (rule decode_invocation_no_exception)
    apply (rule wp_no_exception_seq)+
     apply (simp add:split_def)
     apply (rule wp_no_exception_seq)
      apply (simp add:returnOk_liftE)
      apply wp[1]
     apply (rule_tac P = " y = cur_thread \<and>
       cdl_intent_extras (cdl_tcb_intent ya) = intent_extra" in hoare_gen_asmEx)
     apply simp
     apply (rule hoare_strengthen_postE[OF no_exception_conj])
        apply (rule_tac r = yb in lookup_extra_caps_exec)
       prefer 2
       apply (elim conjE)
       apply (simp add:Fun.comp_def)
      apply wp[1]
     apply simp
    apply (rule_tac P = "(cdl_intent_cap (cdl_tcb_intent ya)) = intent_cptr
       \<and> y = cur_thread"
       in hoare_gen_asmEx)
    apply (rule hoare_strengthen_postE[OF no_exception_conj])
       apply simp
       apply (rule lookup_cap_and_slot_exec)
      prefer 2
      apply (elim conjE)
       apply simp
      apply simp
     apply wp
    apply simp
   apply (wp non_ep_cap get_thread_sep_wp get_thread_inv | simp)+
   apply (clarsimp simp:object_at_def)
  done

crunch cdl_current_thread [wp]:  delete_cap_simple "\<lambda>s. P (cdl_current_thread s)"
  (wp: crunch_wps simp: split_def unless_def)

crunch cdl_current_thread [wp]:  mark_tcb_intent_error "\<lambda>s. P (cdl_current_thread s)"
  (wp: crunch_wps simp: split_def unless_def)

crunch cdl_current_thread [wp]:  corrupt_ipc_buffer "\<lambda>s. P (cdl_current_thread s)"
  (wp: crunch_wps simp: split_def unless_def corrupt_frame_def corrupt_intents_def)

crunch cdl_current_thread [wp]:  invoke_irq_control, invoke_irq_handler "\<lambda>s. P (cdl_current_thread s)"


lemma corrupt_tcb_intent_all_active_tcbs[wp]:
  "\<lbrace>\<lambda>s. P (all_scheduable_tcbs (cdl_objects s)) \<rbrace>
    corrupt_tcb_intent thread
  \<lbrace>\<lambda>rv s. P (all_scheduable_tcbs (cdl_objects s)) \<rbrace>"
  apply (rule sep_inv_to_all_scheduable_tcbs)
  apply wp
  done

lemma corrupt_ipc_buffer_active_tcbs[wp]:
  "\<lbrace>\<lambda>s. P (all_scheduable_tcbs (cdl_objects s)) \<rbrace>
    corrupt_ipc_buffer thread p
  \<lbrace>\<lambda>rv s. P (all_scheduable_tcbs (cdl_objects s)) \<rbrace>"
  apply (rule sep_inv_to_all_scheduable_tcbs)
  apply wp
  done

lemma update_thread_wp:
  "\<lbrace>tcb_at' (\<lambda>tcb. P (f tcb)) thread\<rbrace> update_thread thread f
  \<lbrace>\<lambda>rv. tcb_at' P thread \<rbrace>"
  apply (simp add:update_thread_def)
  apply (wp|wpc | simp add:set_object_def)+
   apply (simp add:object_at_def)
  apply (clarsimp simp:object_at_def)
  done

crunch inv[wp]: thread_has_error P

crunch inv[wp]: has_restart_cap P

definition
  "no_pending s \<equiv> \<forall>oid cap.
     opt_cap (oid,tcb_pending_op_slot) s = Some cap \<longrightarrow> \<not> is_pending_cap cap"

lemma send_signal_no_pending:
  "\<lbrace>P and no_pending\<rbrace>
     send_signal thread
  \<lbrace>\<lambda>r. P\<rbrace>"
  apply (simp add: send_signal_def send_signal_bound_def)
  apply (rule hoare_pre)
  apply (wp | wpc)+
     apply (rule hoare_pre_cont)
    apply (rule_tac P = "waiters = {}" in hoare_gen_asm)
    apply (clarsimp simp: option_select_def)
    apply wp+
      apply (rule hoare_pre_cont)
     apply wp+
  apply (clarsimp simp: get_waiting_ntfn_recv_threads_def get_waiting_sync_bound_ntfn_threads_def
                        no_pending_def opt_cap_def)
  apply (intro allI impI conjI)
   apply (drule_tac x = x in spec)
   apply (clarsimp simp: slots_of_def object_slots_def is_pending_cap_def)
  apply (drule_tac x = x in spec)
  apply (clarsimp simp: slots_of_def object_slots_def is_pending_cap_def)
  done

crunch invs[wp]: get_active_irq P
  (wp: crunch_wps)

lemma handle_pending_interrupts_no_ntf_cap:
  "\<lbrace>P and no_pending\<rbrace>
     handle_pending_interrupts
  \<lbrace>\<lambda>r. P\<rbrace>"
  apply (simp add: handle_pending_interrupts_def)
  apply (rule hoare_pre)
   apply (wp send_signal_no_pending
           | wpc
           | simp add: option_select_def handle_interrupt_def split del: if_split)+
   apply (wp hoare_drop_imps hoare_vcg_all_lift)
  apply simp
  done

lemma call_kernel_with_intent_no_fault_helper:
  assumes unify: "cdl_intent_op intent = Some intent_op \<and>
  cdl_intent_cap intent = intent_cptr \<and> cdl_intent_extras intent = intent_extra"

  and set_cap_hold: "\<lbrace>R\<rbrace>set_cap (root_tcb_id, tcb_pending_op_slot) RunningCap \<lbrace>\<lambda>r. Q\<rbrace>"
  and mark_tcb_intent_error_hold: "\<lbrace>Ra\<rbrace>mark_tcb_intent_error root_tcb_id False \<lbrace>\<lambda>r. R\<rbrace>"
  and corrupt_ipc_buffer_hold: "\<lbrace>Rb\<rbrace>corrupt_ipc_buffer root_tcb_id True \<lbrace>\<lambda>r. Ra\<rbrace>"

  and perform_invocation_hold: "\<And>iv. \<lbrace>PIV iv\<rbrace> perform_invocation True True iv
     \<lbrace>\<lambda>rv s. (cdl_current_thread s = Some root_tcb_id
            \<and> cdl_current_domain s = minBound
      \<and> <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* (\<lambda>s. True)> s
      \<and> Rb s)\<rbrace>, \<lbrace>\<lambda>r s. tcb_at'
                       (\<lambda>tcb. cdl_intent_op (cdl_tcb_intent tcb) = Some intent_op \<and>
                          cdl_intent_cap (cdl_tcb_intent tcb) = cdl_intent_cap intent \<and>
                          cdl_intent_extras (cdl_tcb_intent tcb) = cdl_intent_extras intent)
                       root_tcb_id s \<and>
                   cdl_current_thread s = Some root_tcb_id \<and>
                   cdl_current_domain s = minBound \<and> no_pending s \<and> Pd2 s\<rbrace>"
  and set_restart_cap_hold: "\<And>iv.
    \<lbrace>\<lambda>s. Ps iv s \<rbrace> set_cap (root_tcb_id, tcb_pending_op_slot) RestartCap \<lbrace>\<lambda>r. PIV iv\<rbrace>"

  and decode_invocation_no_exception:
      "\<And>c ref cs. \<lbrace> Pd cs c ref \<rbrace> decode_invocation c ref cs intent_op
       \<lbrace> Ps \<rbrace>, \<lbrace>\<lambda>xa s. False\<rbrace>"
  and lookup_extra_caps_exec:
  "\<And>r. \<lbrace> Pd1 (fst r) (snd r) \<rbrace> lookup_extra_caps root_tcb_id  intent_extra
       \<lbrace> \<lambda>xa s. Pd xa (fst r) (snd r) s \<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
  and lookup_cap_and_slot_exec:
      "\<lbrace> Pd2 \<rbrace> lookup_cap_and_slot root_tcb_id intent_cptr
       \<lbrace> \<lambda>r s. Pd1 (fst r) (snd r) s \<and> \<not> ep_related_cap (fst r) \<rbrace>, \<lbrace>\<lambda>y s. False \<rbrace>"
  and  non_ep_cap:
      "\<lbrace> Pd2 \<rbrace> lookup_cap_and_slot root_tcb_id intent_cptr
       \<lbrace> \<lambda>rv s. \<not> ep_related_cap (fst rv) \<rbrace>, -"

  and upd_thread:
    "\<lbrace>P\<rbrace> update_thread root_tcb_id  (cdl_tcb_intent_update (\<lambda>x. intent))
     \<lbrace>\<lambda>rv s. Pd2 s\<rbrace>"

  shows
  "\<lbrace>\<lambda>s. tcb_at' \<top> root_tcb_id s \<and>
    (cdl_current_thread s = Some root_tcb_id \<and> cdl_current_domain s = minBound \<longrightarrow> P s)\<rbrace>
   call_kernel_with_intent intent False \<lbrace>\<lambda>r. Q\<rbrace>"
  using unify
  apply (simp add:call_kernel_with_intent_def)
  apply wp
        apply (rule_tac P = "thread_ptr = root_tcb_id" in hoare_gen_asm)
        apply (simp add:call_kernel_loop_def)
        apply (rule_tac Q = "\<lambda>r s. cdl_current_thread s = Some root_tcb_id
                               \<and> cdl_current_domain s = minBound \<longrightarrow> Q s
               " in hoare_strengthen_post[rotated])
         apply fastforce
        apply clarsimp
        apply wp
           apply (rule hoare_vcg_imp_lift)
            apply (wpc|wp hoare_vcg_imp_lift|simp cong: if_cong)+
            apply (rule hoare_pre_cont)
           apply (wp has_restart_cap_sep_wp[where cap = RunningCap])[1]
          apply wp
         apply (rule_tac Q = "\<lambda>r s. cdl_current_thread s = Some root_tcb_id
                              \<and> cdl_current_domain s = minBound \<longrightarrow> (Q s
                              \<and>  <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>* (\<lambda>s. True)> s)"
                in hoare_strengthen_post)
          apply (rule schedule_no_choice_wp)
         apply fastforce
        apply (rule whileLoop_wp[where
                I = "\<lambda>rv s. case rv of Inl _ \<Rightarrow> (tcb_at'
                     (\<lambda>tcb. cdl_intent_op (cdl_tcb_intent tcb) = Some intent_op \<and>
                            cdl_intent_cap (cdl_tcb_intent tcb) = cdl_intent_cap intent \<and>
                            cdl_intent_extras (cdl_tcb_intent tcb) = cdl_intent_extras intent)
                            root_tcb_id s
                     \<and> cdl_current_thread s = Some root_tcb_id
                     \<and> cdl_current_domain s = minBound \<and> Pd2 s)
                | Inr rv \<Rightarrow> Q (Inr rv) s" and Q=Q for Q, rotated])
         apply (case_tac r, simp_all)[1]
        apply (simp add: validE_def[symmetric])
        apply (wp handle_pending_interrupts_no_ntf_cap)
         apply (rule handle_event_syscall_no_decode_exception
                   [where cur_thread = root_tcb_id
                      and intent_op = intent_op
                      and intent_cptr = intent_cptr
                      and intent_extra = intent_extra])
                 apply (wp set_cap_wp set_cap_all_scheduable_tcbs
                         set_cap_hold delete_cap_simple_wp[where cap = RestartCap])[1]
                apply (rule decode_invocation_no_exception)
               apply (rule lookup_extra_caps_exec)
              apply (rule lookup_cap_and_slot_exec)
             apply (rule non_ep_cap)
            apply ((wp corrupt_ipc_buffer_sep_inv corrupt_ipc_buffer_active_tcbs
                 mark_tcb_intent_error_hold corrupt_ipc_buffer_hold | simp)+)[2]
          apply (rule hoare_strengthen_postE[OF perform_invocation_hold])
           apply (fastforce simp:sep_state_projection_def sep_any_def
             sep_map_c_def sep_conj_def)
          apply simp
         apply (wp set_restart_cap_hold)
        apply (clarsimp split: sum.split_asm)
       apply (rule_tac P = "thread_ptr = root_tcb_id" in hoare_gen_asm)
       apply simp
       apply (wp upd_thread update_thread_wp)+
  apply auto
  done


lemma invoke_cnode_insert_cap:
  "\<lbrace>\<lambda>s. < dest_slot \<mapsto>c - \<and>* R> s \<and> \<not> is_untyped_cap cap'  \<rbrace>
  invoke_cnode (InsertCall cap' src_slot dest_slot)
  \<lbrace>\<lambda>rv s. <dest_slot \<mapsto>c cap' \<and>* R> s\<rbrace>,\<lbrace>\<lambda>r s. Q\<rbrace>"
  apply (simp add:validE_def)
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:invoke_cnode_def liftE_bindE validE_def[symmetric])
  apply (wpsimp wp: insert_cap_sibling_wp insert_cap_child_wp)
  done

lemma invoke_cnode_move_wp:
  "\<lbrace><dest \<mapsto>c - \<and>* src \<mapsto>c cap \<and>* R>\<rbrace> invoke_cnode (MoveCall cap' src dest)
  \<lbrace>\<lambda>_. <dest \<mapsto>c cap' \<and>* src \<mapsto>c NullCap \<and>* R>\<rbrace>"
  apply (simp add:invoke_cnode_def)
  apply (wp move_cap_wp)
  done

lemma decode_invocation_simps:
  "is_cnode_cap cap
    \<Longrightarrow> decode_invocation cap cap_ref caps (CNodeIntent intent)
    = liftME InvokeCNode (decode_cnode_invocation cap cap_ref caps intent)"
  by (clarsimp simp: decode_invocation_def get_cnode_intent_def
                     throw_opt_def cap_type_def
              split: cdl_cap.splits)

lemma liftME_wp:
  "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>r. Q (f r)\<rbrace>,\<lbrace>Q'\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> liftME f m \<lbrace>Q\<rbrace>,\<lbrace>Q'\<rbrace>"
  apply wp
   apply (simp add:Fun.comp_def)
  apply assumption
  done

lemma sep_normal_conj_absorb:
  "(<A \<and>* sep_true> s \<and> <A \<and>* B> s)  = <A \<and>* B> s"
  by (auto intro:sep_conj_sep_true_right)

lemma sep_normal_conj_absorb':
  "(<A \<and>* sep_true > s \<and> < C \<and>* A \<and>* B > s) = < C \<and>* A \<and>* B> s"
  apply (subst sep_conj_left_commute)
  apply (simp add:sep_normal_conj_absorb)
  apply (simp add:sep_conj_left_commute)
  done

lemma cnode_cap_non_ep_related:
  "is_cnode_cap cap \<Longrightarrow> \<not> ep_related_cap cap"
  by (clarsimp simp: cap_type_def ep_related_cap_def split:cdl_cap.splits)

lemma update_thread_cnode_at:
  "\<lbrace>object_at(\<lambda>x. x = CNode cnode) ptr\<rbrace>
  update_thread cur_thread content
  \<lbrace>\<lambda>rv. object_at (\<lambda>x. x = CNode cnode) ptr \<rbrace>"
  apply (simp add:update_thread_def get_thread_def set_object_def)
  apply (wp|wpc|simp add: object_at_def set_object_def)+
  apply auto
  done

lemma cdl_cur_thread_detype:
  "cdl_current_thread (detype m s) = cdl_current_thread s"
  by (simp add:detype_def)

crunch cdl_current_thread[wp]: reset_untyped_cap "\<lambda>s. P (cdl_current_thread s)"
  (wp: mapME_x_inv_wp whenE_wp simp: cdl_cur_thread_detype crunch_simps)

lemmas helper = valid_validE_E[OF reset_untyped_cap_cdl_current_thread]

crunch cdl_current_thread[wp]: invoke_untyped "\<lambda>s. P (cdl_current_thread s)"
  (wp: mapM_x_wp' crunch_wps unless_wp helper
       simp:cdl_cur_thread_detype crunch_simps)

crunch cdl_current_thread[wp]: move_cap "\<lambda>s. P (cdl_current_thread s)"
  (wp: mapM_x_wp' crunch_wps unless_wp
   simp:crunch_simps)

lemma cnode_insert_cap_cdl_current_thread:
  "\<lbrace>\<lambda>s. P (cdl_current_thread s)  \<rbrace>
  invoke_cnode (InsertCall a b c)
  \<lbrace>\<lambda>rv s. P (cdl_current_thread s)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:
    invoke_cnode_def liftE_bindE validE_def[symmetric])
  apply (rule hoare_pre)
  apply (wp | simp | wpc)+
  done

lemma cnode_move_cap_cdl_current_thread:
  "\<lbrace>\<lambda>s. P (cdl_current_thread s)  \<rbrace>
  invoke_cnode (MoveCall a b c)
  \<lbrace>\<lambda>rv s. P (cdl_current_thread s)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:
    invoke_cnode_def liftE_bindE validE_def[symmetric])
  apply (rule hoare_pre)
  apply (wp | simp | wpc)+
  done

lemma sep_any_imp_c'_conj:
 "< slot \<mapsto>c cap \<and>* R> s \<Longrightarrow> < slot \<mapsto>c - \<and>* R> s"
  by sep_solve

lemma cnode_non_ep:
  "is_cnode_cap cap \<Longrightarrow> \<not> ep_related_cap cap"
  by (simp add: cap_type_def ep_related_cap_def
         split: cdl_cap.splits)

lemma reset_cap_asid_cnode_cap_cong:
  "\<lbrakk>reset_cap_asid cap = reset_cap_asid cap'\<rbrakk>
  \<Longrightarrow> is_cnode_cap cap = is_cnode_cap cap'"
  by (case_tac cap,
       simp_all add: cap_type_def reset_cap_asid_def
              split: cdl_cap.splits)

lemma is_exclusive_cap_update_cap[simp]:
  "safe_for_derive (update_cap_data_det data cap) = safe_for_derive cap"
  by (case_tac cap,
      simp_all add: update_cap_data_det_def update_cap_badge_def
                    safe_for_derive_def badge_update_def guard_update_def)

lemma cnode_cap_reset_asid:
  "is_cnode_cap cap \<Longrightarrow> (reset_cap_asid cap) = cap"
  by (unfold cap_type_def,
      simp add: reset_cap_asid_def
         split: cdl_cap.splits cdl_object_type.splits)

lemma is_cnode_cap_guard_equal:
  "is_cnode_cap x \<Longrightarrow> guard_equal (reset_cap_asid x) = guard_equal x"
  apply (rule ext)+
  by (unfold cap_type_def, simp add:guard_equal_def  Let_def cap_guard_size_def
    reset_cap_asid_def split:cdl_cap.splits)

lemma valid_src_cap_has_type[simp]:
  "cap_type cap = Some type
  \<Longrightarrow> valid_src_cap (default_cap type ids (cnode_cap_size cap) dev)
  = valid_src_cap cap"
  apply (rule ext)
  apply (clarsimp simp: default_cap_def valid_src_cap_def
                        is_cnode_cap_simps
                  split: cdl_cap.splits cdl_object_type.splits)
  apply (clarsimp simp: cap_type_def cnode_cap_size_def)
  done

lemma exclusive_cap_has_type[simp]:
  "cap_type cap = Some type
  \<Longrightarrow> safe_for_derive (default_cap type ids sz dev) = safe_for_derive cap"
  by (fastforce simp: default_cap_def
                      cap_type_def safe_for_derive_def
               split: cdl_cap.splits)

lemma is_untyped_cap_derived[simp]:
  "is_untyped_cap (derived_cap cap) = (is_untyped_cap cap)"
  by (case_tac cap, simp_all add:derived_cap_def cap_type_def)

lemma cap_type_cdl_update_cnode_cap_data [simp]:
  "cap_type (cdl_update_cnode_cap_data cap data) = cap_type cap"
  by (clarsimp simp: cap_type_def cdl_update_cnode_cap_data_def split: cdl_cap.splits)

lemma cap_type_guard_update [simp]:
  "cap_type (guard_update cap data) = cap_type cap"
  by (clarsimp simp: cap_type_def guard_update_def split: cdl_cap.splits)

lemma cap_type_badge_update [simp]:
  "cap_type (badge_update data cap) = cap_type cap"
  by (clarsimp simp: badge_update_def)

lemma cap_type_update_cap_data_det [simp]:
  "cap_type (update_cap_data_det data cap) = cap_type cap"
  by (auto simp: update_cap_data_det_def
          split: cdl_cap.splits)

lemma safe_for_derive_not_untyped:
  "safe_for_derive cap \<Longrightarrow> \<not> is_untyped_cap cap"
  by (clarsimp simp: safe_for_derive_def cap_type_def
              split: cdl_cap.splits)

(* These lemmas are not cong rules,
   but were declared as such and sometimes work as cong rules.
   This should get deleted, eventually.
*)
lemmas cap_type_bad_cong =
 cap_object_reset_cap_asid reset_cap_asid_cap_type
 reset_cap_asid_ep_related_cap cap_rights_reset_cap_asid
 valid_src_cap_asid_cong cap_has_type_asid_cong
 reset_cap_asid_cnode_cap_cong


definition "tcb_has_error
  \<equiv> object_at (\<lambda>obj. case obj of Tcb x \<Rightarrow> cdl_intent_error (cdl_tcb_intent x) = True | _ \<Rightarrow> False)"

lemma mark_tcb_intent_error_no_error:
  "\<lbrace>\<top> \<rbrace> mark_tcb_intent_error thread_ptr True \<lbrace>\<lambda>r s. \<not> tcb_has_error thread_ptr s \<longrightarrow> Q r s\<rbrace>"
  apply (simp add:mark_tcb_intent_error_def tcb_has_error_def)
  apply (simp add:object_at_def update_thread_def
    gets_the_def gets_def )
  apply (wp|wpc|simp add:set_object_def)+
  done

lemma mark_tcb_intent_error_no_error':
  "\<lbrace>\<top> \<rbrace> mark_tcb_intent_error thread_ptr False \<lbrace>\<lambda>r s. \<not> tcb_has_error thread_ptr s\<rbrace>"
  apply (simp add:mark_tcb_intent_error_def update_thread_def
    gets_the_def set_object_def)
  apply (wp|wpc|simp add:set_object_def)+
  apply (clarsimp simp: tcb_has_error_def object_at_def)
  done

lemma syscall_valid_helper_allow_error:
  "\<lbrakk> \<And>x xa. \<lbrace>Qa x xa \<rbrace> perform_syscall_fn xa
     \<lbrace>\<lambda>r. Q and (\<lambda>s. \<not> tcb_has_error thread_ptr s)\<rbrace>, \<lbrace>\<lambda>r. Inv\<rbrace>;
     \<And>r. \<lbrace>Qi r\<rbrace>arg_decode_fn r \<lbrace>Qa r\<rbrace>, \<lbrace>\<lambda>ret. P\<rbrace>;
    \<lbrace>Pre\<rbrace>cap_decoder_fn \<lbrace>Qi\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>;
    \<lbrace>P\<rbrace>mark_tcb_intent_error thread_ptr True \<lbrace>\<lambda>rv s. P s\<rbrace>;
    \<lbrace>P\<rbrace> corrupt_ipc_buffer thread_ptr True \<lbrace>\<lambda>ya. P\<rbrace>;
    \<And>s. Pre s \<Longrightarrow> P s
   \<rbrakk> \<Longrightarrow>
   \<lbrace>Pre and (\<lambda>s. \<not> tcb_has_error thread_ptr s) \<rbrace>syscall cap_decoder_fn decode_error_handler
    arg_decode_fn
    (do ya \<leftarrow> corrupt_ipc_buffer thread_ptr True;
        mark_tcb_intent_error thread_ptr True
    od)
    perform_syscall_fn
   \<lbrace>\<lambda>r s. (\<not> tcb_has_error thread_ptr s \<longrightarrow> Q s)
       \<and>  (tcb_has_error thread_ptr s \<longrightarrow> P s)\<rbrace>,\<lbrace>\<lambda>r. Inv\<rbrace>"
  apply (simp add:syscall_def)
  apply (rule hoare_vcg_handle_elseE)
    apply (erule hoare_pre)
    apply simp
   apply simp
  apply (rule hoare_vcg_handle_elseE)
    apply assumption
   including no_pre apply wp
    apply (wp mark_tcb_intent_error_no_error)
    apply (rule hoare_drop_imp,simp)
   apply simp
  apply (rule hoare_strengthen_postE)
    apply fastforce
   apply simp
  apply simp
  done


lemma tcb_has_error_set_cap:
  "\<lbrace> (\<lambda>s. P (tcb_has_error p s)) and K (snd slot \<noteq> tcb_ipcbuffer_slot) \<rbrace> set_cap slot cap
  \<lbrace>\<lambda>ya s. P (tcb_has_error p s)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (rule_tac Q = "\<lambda>r s'. tcb_has_error p s' = tcb_has_error p s" in
    hoare_strengthen_post)
  apply (simp add:set_cap_def
    gets_the_def set_object_def
    split_def)
  apply (wp|wpc|simp)+
  apply (clarsimp simp:tcb_has_error_def
    object_at_def,simp split:cdl_object.split_asm)
  apply (intro conjI impI)
   apply (simp add:update_slots_def
     has_slots_def
     object_slots_def
     split:cdl_object.splits)+
  done


lemma handle_event_syscall_allow_error:
  assumes set_cap_hold: "\<lbrace>Rm \<rbrace>set_cap (cur_thread, tcb_pending_op_slot) RunningCap \<lbrace>\<lambda>r. Q\<rbrace>"

  and decode_invocation_allow_error:
      "\<And>c ref cs. \<lbrace> Pd cs c ref \<rbrace> decode_invocation c ref cs intent_op
       \<lbrace> Ps \<rbrace>, \<lbrace>\<lambda>r. Perror\<rbrace>"
  and lookup_extra_caps_exec:
  "\<And>r. \<lbrace> Pd1 (fst r) (snd r) \<rbrace> lookup_extra_caps cur_thread  intent_extra
       \<lbrace> \<lambda>xa s. Pd xa (fst r) (snd r) s \<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
  and lookup_cap_and_slot_exec:
      "\<lbrace> Pd2 \<rbrace> lookup_cap_and_slot cur_thread intent_cptr
       \<lbrace> \<lambda>r s. Pd1 (fst r) (snd r) s \<and> \<not> ep_related_cap (fst r) \<rbrace>, \<lbrace>\<lambda>y s. False \<rbrace>"

  and  non_ep_cap:
      "\<lbrace> Pd2 \<rbrace> lookup_cap_and_slot cur_thread intent_cptr
       \<lbrace> \<lambda>rv s. \<not> ep_related_cap (fst rv) \<rbrace>, -"
  and mark_tcb_intent_error_hold: "\<lbrace> Ra \<rbrace>mark_tcb_intent_error cur_thread False \<lbrace>\<lambda>r. Rm\<rbrace>"
             "\<lbrace>Perror\<rbrace> mark_tcb_intent_error cur_thread True \<lbrace>\<lambda>rv. Perror\<rbrace>"
  and corrupt_ipc_buffer_hold: "\<lbrace> Rb \<rbrace>corrupt_ipc_buffer cur_thread True \<lbrace>\<lambda>r. Ra\<rbrace>"
             "\<lbrace>Perror\<rbrace> corrupt_ipc_buffer cur_thread True \<lbrace>\<lambda>ya. Perror\<rbrace>"

  and perform_invocation_hold: "\<And>iv. \<lbrace>PIV iv\<rbrace> perform_invocation True True iv
    \<lbrace>\<lambda>rv s. Rb s \<and> <(cur_thread, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* sep_true > s\<rbrace>, \<lbrace>\<lambda>r. Inv\<rbrace>"
  and set_restart_cap_hold: "\<And>iv. \<lbrace>Ps iv\<rbrace> set_cap (cur_thread, tcb_pending_op_slot) RestartCap \<lbrace>\<lambda>r. PIV iv\<rbrace>"
  and error_imp: "\<And>s. Pd2 s \<Longrightarrow>  cdl_current_thread s = Some cur_thread \<and> Perror s"
  shows "\<lbrace> Pd2
   and tcb_at'
     (\<lambda>tcb. cdl_intent_op (cdl_tcb_intent tcb) = Some intent_op \<and>
            cdl_intent_cap (cdl_tcb_intent tcb) = intent_cptr \<and>
            cdl_intent_extras (cdl_tcb_intent tcb) = intent_extra \<and>
            cdl_intent_error (cdl_tcb_intent tcb) = False) cur_thread
   \<rbrace> handle_event (SyscallEvent SysCall)
   \<lbrace>\<lambda>r s.  (\<not> tcb_has_error cur_thread s \<longrightarrow> Q s)
  \<and> (tcb_has_error cur_thread s \<longrightarrow> Perror s)\<rbrace>,\<lbrace>\<lambda>y. Inv\<rbrace>"
  apply (simp add:handle_event_def handle_syscall_def
    handle_invocation_def when_def)
  apply (rule liftE_wp_split_r)+
    apply (rule_tac P = "y = cur_thread" in hoare_gen_asmEx)
    apply simp
     apply (rule_tac P = "cdl_intent_op (cdl_tcb_intent ya) = Some intent_op
       \<and> (cdl_intent_cap (cdl_tcb_intent ya)) = intent_cptr
       \<and>  cdl_intent_extras (cdl_tcb_intent ya) = intent_extra"
       in hoare_gen_asmEx)
    apply simp
    apply (rule syscall_valid_helper_allow_error)
      apply (rule liftE_wp_split_r)+
       apply (rule wp_no_exception_seq_r)
        apply (rule liftE_wp_no_exception)
         apply (rule whenE_wp)
         apply (simp)
         apply wp
           apply (rule_tac P = "y = cur_thread" in hoare_gen_asm)
           apply simp
           apply (wp set_cap_hold tcb_has_error_set_cap)
          apply (rule_tac P = "y = cur_thread" in hoare_gen_asm)
          apply (simp add:tcb_pending_op_slot_def tcb_ipcbuffer_slot_def)
          apply (wp mark_tcb_intent_error_hold mark_tcb_intent_error_no_error')
         apply simp
         apply (rule corrupt_ipc_buffer_hold)
        apply (wp has_restart_cap_sep_wp[where cap = RestartCap])[1]
       apply (rule_tac P = "y = cur_thread" in hoare_gen_asmEx)
       apply (simp add:conj_comms)
       apply (rule perform_invocation_hold)
      apply (rule_tac P = "y = cur_thread" in hoare_gen_asm)
      apply simp
      apply (wp hoare_vcg_conj_lift set_restart_cap_hold)[1]
     apply simp
     apply (rule_tac P = " \<not> ep_related_cap (fst r)
       \<and> cdl_intent_op (cdl_tcb_intent ya) = Some intent_op"
       in hoare_gen_asmEx)
     apply (simp add:split_def)
     apply (rule decode_invocation_allow_error)
    apply (rule wp_no_exception_seq)+
     apply (simp add:split_def)
     apply (rule wp_no_exception_seq)
      apply (simp add:returnOk_liftE)
      apply wp[1]
     apply simp
     apply (rule_tac P = "
       cdl_intent_extras (cdl_tcb_intent ya) = intent_extra" in hoare_gen_asmEx)
     apply simp
     apply (rule hoare_strengthen_postE[OF no_exception_conj])
        apply (rule_tac r = r in lookup_extra_caps_exec)
       prefer 2
       apply (elim conjE)
       apply (simp add:Fun.comp_def)
      apply wp[1]
     apply simp
    apply simp
   apply (rule lookup_cap_and_slot_exec)
      apply (wp mark_tcb_intent_error_hold
        corrupt_ipc_buffer_hold |
        simp add:error_imp)+
    apply (wp non_ep_cap get_thread_sep_wp get_thread_inv | simp)+
   apply (clarsimp simp:object_at_def tcb_has_error_def error_imp)
  done

lemma thread_has_error_wp:
  "\<lbrace> \<lambda>s. Q (tcb_has_error thread_ptr s) s\<rbrace>
  thread_has_error thread_ptr \<lbrace>\<lambda>has_error s. Q has_error s\<rbrace>"
  apply (clarsimp simp:thread_has_error_def get_thread_def
    gets_the_def tcb_has_error_def)
  apply (wp|wpc)+
  apply (clarsimp simp: object_at_def)
  done

lemma call_kernel_with_intent_allow_error_helper:
  assumes unify: "cdl_intent_op intent = Some intent_op \<and>
  cdl_intent_cap intent = intent_cptr \<and> cdl_intent_extras intent = intent_extra"
  and set_cap_hold: "\<lbrace>R\<rbrace>set_cap (root_tcb_id, tcb_pending_op_slot) RunningCap \<lbrace>\<lambda>r. Q\<rbrace>"
  and mark_tcb_intent_error_hold: "\<lbrace>Ra\<rbrace>mark_tcb_intent_error root_tcb_id False \<lbrace>\<lambda>r. R\<rbrace>"
                                  "\<lbrace>Perror\<rbrace>mark_tcb_intent_error root_tcb_id True \<lbrace>\<lambda>r. Perror\<rbrace>"
  and corrupt_ipc_buffer_hold: "\<lbrace>Rb\<rbrace>corrupt_ipc_buffer root_tcb_id True \<lbrace>\<lambda>r. Ra\<rbrace>"
                               "\<lbrace>Perror\<rbrace>corrupt_ipc_buffer root_tcb_id True \<lbrace>\<lambda>r. Perror\<rbrace>"

  and perform_invocation_hold: "\<And>iv. \<lbrace>PIV iv\<rbrace> perform_invocation True True iv
     \<lbrace>\<lambda>rv s.  (cdl_current_thread s = Some root_tcb_id
               \<and> cdl_current_domain s = minBound
               \<and> <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RestartCap \<and>* (\<lambda>s. True)> s
               \<and> Rb s)\<rbrace>,  \<lbrace>\<lambda>r s. tcb_at'
                       (\<lambda>tcb. cdl_intent_op (cdl_tcb_intent tcb) = Some intent_op \<and>
                          cdl_intent_cap (cdl_tcb_intent tcb) = cdl_intent_cap intent \<and>
                          cdl_intent_extras (cdl_tcb_intent tcb) = cdl_intent_extras intent \<and>
                          cdl_intent_error (cdl_tcb_intent tcb) = False)
                       root_tcb_id s \<and>
                   cdl_current_thread s = Some root_tcb_id \<and>
                   cdl_current_domain s = minBound \<and> no_pending s \<and> Pd2 s\<rbrace>"
  and set_restart_cap_hold: "\<And>iv.
    \<lbrace>\<lambda>s. Ps iv s \<rbrace> set_cap (root_tcb_id, tcb_pending_op_slot) RestartCap \<lbrace>\<lambda>r. PIV iv\<rbrace>"

  and decode_invocation_allow_error:
      "\<And>c ref cs. \<lbrace> Pd cs c ref \<rbrace> decode_invocation c ref cs intent_op
       \<lbrace> Ps \<rbrace>, \<lbrace>\<lambda>r s. Perror s
          \<and> cdl_current_thread s = Some root_tcb_id
          \<and> cdl_current_domain s = minBound
          \<and> <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>* (\<lambda>s. True)> s \<rbrace>
"
  and lookup_extra_caps_exec:
  "\<And>r. \<lbrace> Pd1 (fst r) (snd r) \<rbrace> lookup_extra_caps root_tcb_id  intent_extra
       \<lbrace> \<lambda>xa s. Pd xa (fst r) (snd r) s \<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
  and lookup_cap_and_slot_exec:
      "\<lbrace> Pd2 \<rbrace> lookup_cap_and_slot root_tcb_id intent_cptr
       \<lbrace> \<lambda>r s. Pd1 (fst r) (snd r) s \<and> \<not> ep_related_cap (fst r) \<rbrace>, \<lbrace>\<lambda>y s. False \<rbrace>"
  and upd_thread:
    "\<lbrace>P\<rbrace> update_thread root_tcb_id  (cdl_tcb_intent_update (\<lambda>x. intent))
     \<lbrace>\<lambda>rv s. Pd2 s\<rbrace>"
  and error_imp: "\<And>s. Pd2 s \<Longrightarrow> (cdl_current_thread s = Some root_tcb_id)
  \<and> cdl_current_domain s = minBound
  \<and> <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
    \<and>* (root_tcb_id) \<mapsto>f (Tcb tcb) \<and>* (\<lambda>s. True)> s
  \<and> Perror s"
  shows
  "\<lbrace>\<lambda>s. \<not> cdl_intent_error intent
  \<and> ((cdl_current_thread s = Some root_tcb_id \<and> cdl_current_domain s = minBound) \<longrightarrow> P s)
  \<and> <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap
  \<and>* (root_tcb_id) \<mapsto>f (Tcb tcb) \<and>* (\<lambda>s. True)> s
   \<rbrace>  call_kernel_with_intent intent check \<lbrace>\<lambda>r s. ((\<not> r \<or> check) \<longrightarrow> Q s)
     \<and> ((r \<and> \<not> check) \<longrightarrow> Perror s) \<rbrace>"
  using unify
  apply (simp add:call_kernel_with_intent_def)
  apply (wp thread_has_error_wp)
        apply (simp add:call_kernel_loop_def)
        apply (rule_tac P = "thread_ptr = root_tcb_id" in hoare_gen_asm)
        apply (rule_tac Q = "\<lambda>r s. (cdl_current_thread s = Some root_tcb_id
                                    \<and> cdl_current_domain s = minBound) \<longrightarrow>
                                       (\<not>tcb_has_error (the (cdl_current_thread s)) s \<longrightarrow> Q s) \<and>
                                       (tcb_has_error (the (cdl_current_thread s)) s \<longrightarrow> Perror s)"
                        in hoare_strengthen_post[rotated])
         apply (fastforce simp: error_imp)
        apply wp (* fragile , do not know why *)
           apply (rule hoare_vcg_imp_lift[where P' = "\<lambda>s. cdl_current_thread s \<noteq> Some root_tcb_id
                                                          \<or> cdl_current_domain s \<noteq> minBound"])
            apply (rule hoare_pre,(wp hoare_vcg_imp_lift|wpc|simp cong: if_cong)+)[1]
           apply (wp | wpc | simp)+
            apply (rule hoare_pre_cont)
           apply (wp has_restart_cap_sep_wp[where cap = RunningCap])+
         apply simp
         apply (rule_tac current_thread1=root_tcb_id and current_domain1=minBound in
                         hoare_strengthen_post[OF schedule_no_choice_wp])
         apply (clarsimp, assumption)
        apply clarsimp
        apply (rule_tac Q =
               "\<lambda>r a. (\<not> tcb_has_error root_tcb_id a \<longrightarrow> (Q a
                            \<and> cdl_current_thread a = Some root_tcb_id
                            \<and> cdl_current_domain a = minBound
                            \<and> <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>* (\<lambda>s. True)> a))
                            \<and> (tcb_has_error root_tcb_id a \<longrightarrow> (Perror a
                            \<and> cdl_current_thread a = Some root_tcb_id
                            \<and> cdl_current_domain a = minBound
                            \<and> <(root_tcb_id, tcb_pending_op_slot) \<mapsto>c RunningCap \<and>* (\<lambda>s. True)> a))"
               in hoare_strengthen_post[rotated])
         apply fastforce
        apply (rule whileLoop_wp[where
                I = "\<lambda>rv s. case rv of Inl _ \<Rightarrow>
                     (tcb_at'
                     (\<lambda>tcb. cdl_intent_op (cdl_tcb_intent tcb) = Some intent_op \<and>
                            cdl_intent_cap (cdl_tcb_intent tcb) = cdl_intent_cap intent \<and>
                            cdl_intent_extras (cdl_tcb_intent tcb) = cdl_intent_extras intent \<and>
                            cdl_intent_error (cdl_tcb_intent tcb) = False)
                            root_tcb_id s \<and>
                     cdl_current_thread s = Some root_tcb_id \<and>
                     cdl_current_domain s = minBound \<and> Pd2 s)
                | Inr rv \<Rightarrow> Q (Inr rv) s" and Q=Q for Q, rotated])
         apply (case_tac r, simp_all)[1]
        apply (simp add: validE_def[symmetric])
        apply (wp handle_pending_interrupts_no_ntf_cap)
         apply (rule handle_event_syscall_allow_error
                       [where cur_thread = root_tcb_id
                          and intent_op = intent_op
                          and intent_cptr = intent_cptr
                          and intent_extra = intent_extra])
                    apply (wp set_cap_wp
                              set_cap_hold delete_cap_simple_wp[where cap = RestartCap])[1]
                   apply (rule decode_invocation_allow_error)
                  apply (rule lookup_extra_caps_exec)
                 apply (rule lookup_cap_and_slot_exec)
                apply (unfold validE_R_def)
                apply (rule hoare_strengthen_postE)
                  apply (rule lookup_cap_and_slot_exec)
                 apply simp
                apply simp
               apply ((wp corrupt_ipc_buffer_sep_inv corrupt_ipc_buffer_active_tcbs
                          mark_tcb_intent_error_hold corrupt_ipc_buffer_hold | simp)+)[4]
           apply (rule hoare_strengthen_postE[OF perform_invocation_hold])
            apply (fastforce simp:sep_state_projection_def sep_any_def sep_map_c_def sep_conj_def)
           apply simp
          apply (wp set_restart_cap_hold)
         apply (clarsimp dest!:error_imp)
         apply (sep_cancel, simp)
        apply (clarsimp split: sum.split_asm)
       apply (rule_tac P = "thread_ptr = root_tcb_id" in hoare_gen_asm)
       apply simp
       apply (wp upd_thread update_thread_wp)+
  apply (clarsimp simp: sep_map_c_conj sep_map_f_conj object_at_def
                        object_project_def sep_state_projection_def
                  split:option.splits cdl_object.split)
  apply (case_tac z)
           apply (clarsimp dest!:arg_cong[where f= object_type],simp add:object_type_def)+
  done

definition
  "cap_of_insert_call c = (case c of (InvokeCNode (InsertCall cap src dest)) \<Rightarrow> cap)"

lemma invoke_cnode_insert_cap':
  "incall = InsertCall cap src_slot dest_slot
  \<Longrightarrow> \<lbrace>\<lambda>s. < dest_slot \<mapsto>c - \<and>* R> s \<and> \<not> is_untyped_cap (cap_of_insert_call (InvokeCNode incall))  \<rbrace>
  invoke_cnode incall
  \<lbrace>\<lambda>rv s. <dest_slot \<mapsto>c cap \<and>* R> s\<rbrace>,\<lbrace>\<lambda>r s. Q\<rbrace>"
  apply (simp add:validE_def)
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:invoke_cnode_def liftE_bindE validE_def[symmetric])
  apply (wpsimp wp: insert_cap_sibling_wp insert_cap_child_wp
                simp: cap_of_insert_call_def)
  done

lemma object_to_sep_state_slot:
  "object_to_sep_state (fst ptr) obj {Slot (snd ptr)} = [(fst ptr, Slot (snd ptr)) \<mapsto>
  (CDL_Cap ((reset_cap_asid \<circ>\<^sub>M object_slots obj) (snd ptr)))]"
  apply (rule ext)
  apply (clarsimp simp:object_to_sep_state_def
    object_project_slot object_slots_object_clean
    split:if_splits)
  done

lemma sep_map_c_asid_reset:
  "reset_cap_asid cap = reset_cap_asid cap'
  \<Longrightarrow> sep_map_c ptr cap = sep_map_c ptr cap'"
  apply (intro ext)
  apply (clarsimp simp:sep_map_c_def split_def)
  apply (rule iffI)
   apply clarsimp
   apply (case_tac "\<not> has_slots obj")
    apply simp
   apply (rule_tac x = "update_slots ((object_slots obj)(snd ptr \<mapsto> cap')) obj"
     in exI)
   apply (simp add:sep_map_general_def object_to_sep_state_slot)
  apply clarsimp
  apply (case_tac "\<not> has_slots obj")
   apply simp
  apply (rule_tac x = "update_slots ((object_slots obj)(snd ptr \<mapsto> cap)) obj"
    in exI)
  apply (simp add:sep_map_general_def object_to_sep_state_slot)
  done

lemma reset_cap_asid_update_cap_data:
  "reset_cap_asid (update_cap_data_det data dcap)
  = update_cap_data_det data (reset_cap_asid dcap)"
  by (case_tac dcap,simp_all add:reset_cap_asid_def badge_update_def
    guard_update_def update_cap_badge_def
    update_cap_data_det_def)

lemmas derived_cap_simps = derived_cap_def[split_simps cdl_cap.split]

lemma reset_cap_asid_derived:
  "reset_cap_asid a = reset_cap_asid b
  \<Longrightarrow> reset_cap_asid (derived_cap a) = reset_cap_asid (derived_cap b)"
  apply (frule reset_cap_asid_id)
  apply (safe, (case_tac b, simp_all add: reset_cap_asid_def derived_cap_simps)+)
  done

lemma reset_cap_asid_update_cap_rights:
  "reset_cap_asid (update_cap_rights rights b) = update_cap_rights rights (reset_cap_asid b)"
  by (case_tac b,simp_all add:update_cap_rights_def reset_cap_asid_def)

lemma use_sep_true_for_sep_map_c:
  "\<lbrakk> < slot \<mapsto>c cap \<and>* (\<lambda>s. True)> s ; < slot \<mapsto>c - \<and>* R> s\<rbrakk>
  \<Longrightarrow> < slot \<mapsto>c cap \<and>* R > s"
  by (clarsimp simp:sep_map_c_conj sep_any_exist)

end
