(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Refinement for handleEvent and syscalls
*)

theory ArchSyscall_AI
imports
  Syscall_AI
begin

context Arch begin arch_global_naming

named_theorems Syscall_AI_assms

declare arch_get_sanitise_register_info_inv[Syscall_AI_assms]
crunch handle_arch_fault_reply, arch_get_sanitise_register_info
 for pred_tcb_at[wp,Syscall_AI_assms]: "\<lambda>s. N (pred_tcb_at proj P t s)"
crunch handle_arch_fault_reply
 for invs[wp,Syscall_AI_assms]: "invs"
crunch handle_arch_fault_reply, arch_get_sanitise_register_info
 for cap_to[wp,Syscall_AI_assms]: "ex_nonz_cap_to c"
crunch handle_arch_fault_reply, arch_get_sanitise_register_info
 for it[wp,Syscall_AI_assms]: "\<lambda>s. P (idle_thread s)"
crunch handle_arch_fault_reply, arch_get_sanitise_register_info
 for caps[wp,Syscall_AI_assms]: "\<lambda>s. P (caps_of_state s)"
crunch handle_arch_fault_reply, make_fault_msg, arch_get_sanitise_register_info
 for cur_thread[wp,Syscall_AI_assms]: "\<lambda>s. P (cur_thread s)"
crunch handle_arch_fault_reply, arch_get_sanitise_register_info
 for valid_objs[wp,Syscall_AI_assms]: "valid_objs"
crunch handle_arch_fault_reply, arch_get_sanitise_register_info
 for valid_mdb[wp,Syscall_AI_assms]: valid_mdb
crunch handle_arch_fault_reply, arch_get_sanitise_register_info
 for cte_wp_at[wp,Syscall_AI_assms]: "\<lambda>s. P (cte_wp_at P' p s)"

crunch invoke_irq_control
  for typ_at[wp, Syscall_AI_assms]: "\<lambda>s. P (typ_at T p s)"

lemma obj_refs_cap_rights_update[simp, Syscall_AI_assms]:
  "obj_refs (cap_rights_update rs cap) = obj_refs cap"
  by (simp add: cap_rights_update_def acap_rights_update_def
         split: cap.split arch_cap.split)

(* FIXME: move to TCB *)
lemma table_cap_ref_mask_cap [Syscall_AI_assms]:
  "table_cap_ref (mask_cap R cap) = table_cap_ref cap"
  by (clarsimp simp add:mask_cap_def table_cap_ref_def acap_rights_update_def
    cap_rights_update_def split:cap.splits arch_cap.splits)

lemma eq_no_cap_to_obj_with_diff_ref [Syscall_AI_assms]:
  "\<lbrakk> cte_wp_at ((=) cap) p s; valid_arch_caps s \<rbrakk>
      \<Longrightarrow> no_cap_to_obj_with_diff_ref cap S s"
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_arch_caps_def)
  apply (frule(1) unique_table_refs_no_cap_asidD)
  apply (clarsimp simp add: no_cap_to_obj_with_diff_ref_def
                            table_cap_ref_mask_cap Ball_def)
  done

lemma hv_invs[wp, Syscall_AI_assms]: "\<lbrace>invs\<rbrace> handle_vm_fault t' flt \<lbrace>\<lambda>r. invs\<rbrace>"
  unfolding handle_vm_fault_def by (cases flt; wpsimp)

crunch getRegister, read_stval
  for inv[wp]: "P"
  (ignore_del: getRegister)

lemma hv_inv_ex [Syscall_AI_assms]:
  "\<lbrace>P\<rbrace> handle_vm_fault t vp \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding handle_vm_fault_def
  by (cases vp; wpsimp wp: dmo_inv getRestartPC_inv det_getRestartPC as_user_inv)

lemma handle_vm_fault_valid_fault[wp, Syscall_AI_assms]:
  "\<lbrace>\<top>\<rbrace> handle_vm_fault thread ft -,\<lbrace>\<lambda>rv s. valid_fault rv\<rbrace>"
  unfolding handle_vm_fault_def
  apply (cases ft, simp_all)
   apply (wp | simp add: valid_fault_def)+
  done

lemma hvmf_st_tcb_at[wp, Syscall_AI_assms]:
  "handle_vm_fault t w \<lbrace>\<lambda>s. N (st_tcb_at P t' s)\<rbrace>"
  unfolding handle_vm_fault_def
  by (cases w; wpsimp)

lemma hvmf_ex_cap[wp, Syscall_AI_assms]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> handle_vm_fault t b \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  unfolding handle_vm_fault_def by (cases b; wpsimp)

lemma hh_invs[wp, Syscall_AI_assms]:
  "\<lbrace>invs and ct_active and st_tcb_at active thread and ex_nonz_cap_to_thread\<rbrace>
     handle_hypervisor_fault thread fault
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (cases fault) wpsimp

crunch make_fault_msg
  for cur_sc[wp, Syscall_AI_assms]: "\<lambda>s. P (cur_sc s)"
  and pred_tcb_at[wp, Syscall_AI_assms]: "pred_tcb_at proj P t"

end

global_interpretation Syscall_AI?: Syscall_AI
proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Syscall_AI_assms)?)
qed

end
