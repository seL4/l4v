(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDeterministic_AI
imports Deterministic_AI
begin

context Arch begin global_naming RISCV64

named_theorems Deterministic_AI_assms

crunch valid_list[wp, Deterministic_AI_assms]:
  cap_swap_for_delete,set_cap,finalise_cap,arch_get_sanitise_register_info,
  arch_post_modify_registers valid_list
  (wp: crunch_wps simp: unless_def crunch_simps)
declare get_cap_inv[Deterministic_AI_assms]

end

global_interpretation Deterministic_AI_1?: Deterministic_AI_1
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

locale touched_addresses_det_inv = touched_addresses_inv "TYPE(det_ext)"
begin
(*
lemma valid_list_inv [wp]:
  "m \<lbrace>valid_list\<rbrace>"
  apply (simp add: agnostic_preserved ta_agnostic_def)
  done

lemma domain_list_inv [wp]:
  "m \<lbrace>\<lambda>s. P (domain_list s)\<rbrace>"
  apply (rule agnostic_preserved)
  apply (simp add:ta_agnostic_def)
  done

lemma domain_time_inv [wp]:
  "m \<lbrace>\<lambda>s. P (domain_time s)\<rbrace>"
  apply (rule agnostic_preserved)
  apply (simp add:ta_agnostic_def)
  done *)
end

locale touched_addresses_P_det_inv = touched_addresses_det_inv m
  for m::"(det_ext state, 'r) nondet_monad" +
  fixes P :: "det_ext state \<Rightarrow> bool"
  assumes ta_agnostic [simp]: "ta_agnostic P"
begin
lemma m_inv [wp]:
  "m \<lbrace>P\<rbrace>"
  by (rule agnostic_preserved [OF ta_agnostic])
end

sublocale touched_addresses_det_inv \<subseteq> valid_list: touched_addresses_P_det_inv _ valid_list
  by unfold_locales (simp add: agnostic_preserved ta_agnostic_def)

(* locale touched_addresses_invE = touched_addresses_inv state_ext_t m *)
  (* for state_ext_t :: "'state_ext::state_ext itself" *)
  (* and m::"('state_ext::state_ext state, 'ra + 'rb) nondet_monad" *)
(* begin *)

locale touched_addresses_det_invE = touched_addresses_invE "TYPE(det_ext)" m
  + touched_addresses_det_inv m
  for m::"(det_ext state, 'ra + 'rb) nondet_monad"
begin
(*lemma valid_list_inv [wp]:
  "m \<lbrace>valid_list\<rbrace>"
  apply (simp add: agnostic_preserved ta_agnostic_def)
  done *)

(*FIXME: can these be generated with some interesting locale trickery? *)
lemma valid_list_invER[wp]:
  "\<lbrace>valid_list\<rbrace> m \<lbrace>\<lambda>_. valid_list\<rbrace>, -"
  by (clarsimp simp: agnostic_preserved ta_agnostic_def valid_validE_R)

lemma domain_list_invE[wp]:
  "\<lbrace>\<lambda>s. P (domain_list s)\<rbrace> m \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>, \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>"
  by (clarsimp simp: agnostic_preserved ta_agnostic_def valid_validE)

end

interpretation resolve_address_bits_tainv_det:
  touched_addresses_det_inv "resolve_address_bits objref"
  apply unfold_locales
  (* note that here we get this for free. i dont know how to generate this for free though *)
  done

interpretation lookup_extra_caps_tainv_det:
  touched_addresses_det_inv "lookup_extra_caps x y z"
  by unfold_locales

interpretation get_receive_slots_tainv_det:
  touched_addresses_det_inv "get_receive_slots x y"
  by unfold_locales

interpretation decode_invocation_tainv_det:
  touched_addresses_det_inv "decode_invocation x y z xx yy zz"
  apply unfold_locales
  apply (rule decode_inv_tainv)
  done

interpretation lookup_cap_tainv_det:
  touched_addresses_det_invE "lookup_cap x y"
  by unfold_locales

(* does something like this already exist? *)
lemma hoare_post_conj_imp:
  "(\<lbrace>P\<rbrace> m \<lbrace>\<lambda>_. P\<rbrace>, -) \<Longrightarrow>
    \<lbrace>P\<rbrace> m \<lbrace>\<lambda>rv s.
           (\<forall>x. (ZZ1 x \<longrightarrow> P s) \<and>
                (ZZ3 x \<longrightarrow> P s)) \<and>
           P s\<rbrace>, -"
  by (simp add: hoare_post_imp_R)

context Arch begin global_naming RISCV64

crunch valid_list[wp,Deterministic_AI_assms]: arch_invoke_irq_handler valid_list

crunch valid_list[wp]: invoke_untyped valid_list
  (wp: crunch_wps preemption_point_inv' hoare_unless_wp mapME_x_wp'
   simp: mapM_x_def_bak crunch_simps)

crunch valid_list[wp]: invoke_irq_control valid_list

lemma perform_page_table_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_table_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  unfolding perform_page_table_invocation_def
  by (wpsimp wp: mapM_x_wp' simp: perform_pt_inv_map_def perform_pt_inv_unmap_def)

lemma perform_page_invocation_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> perform_page_invocation a \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases a, simp_all add: perform_pg_inv_map_def perform_pg_inv_unmap_def
                                perform_pg_inv_get_addr_def split_def)
    apply (wp mapM_x_wp' mapM_wp' crunch_wps | intro impI conjI allI | wpc
           | simp add: set_message_info_def set_mrs_def split: cap.splits arch_cap.splits)+
  done

crunches perform_invocation
  for valid_list [wp]: valid_list
  (wp: crunch_wps simp: crunch_simps ignore: without_preemption)

crunches decode_invocation
  for valid_list [wp]: valid_list
  (wp: crunch_wps syscall_valid simp: crunch_simps ignore: without_preemption syscall)

crunches handle_invocation
  for valid_list[wp, Deterministic_AI_assms]: valid_list
  (wp: crunch_wps syscall_valid hoare_post_conj_imp simp: crunch_simps
   ignore: without_preemption syscall)

crunch valid_list[wp, Deterministic_AI_assms]: handle_recv, handle_yield, handle_call valid_list
  (wp: crunch_wps simp: crunch_simps)

lemma handle_vm_fault_valid_list[wp, Deterministic_AI_assms]:
  "handle_vm_fault thread fault \<lbrace>valid_list\<rbrace>"
  unfolding handle_vm_fault_def by (cases fault; wpsimp)

lemma handle_interrupt_valid_list[wp, Deterministic_AI_assms]:
  "\<lbrace>valid_list\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_.valid_list\<rbrace>"
  unfolding handle_interrupt_def ackInterrupt_def
  apply (rule hoare_pre)
   by (wp get_cap_wp  do_machine_op_valid_list
       | wpc | simp add: get_irq_slot_def handle_reserved_irq_def arch_mask_irq_signal_def
       | wp (once) hoare_drop_imps)+

crunch valid_list[wp, Deterministic_AI_assms]: handle_send,handle_reply valid_list

crunch valid_list[wp, Deterministic_AI_assms]: handle_hypervisor_fault valid_list

end

global_interpretation Deterministic_AI_2?: Deterministic_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Deterministic_AI_assms)?)
  qed

end
