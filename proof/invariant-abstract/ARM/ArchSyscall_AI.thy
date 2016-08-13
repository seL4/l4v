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
Refinement for handleEvent and syscalls
*)

theory ArchSyscall_AI
imports
  "../Syscall_AI"
begin

context Arch begin global_naming ARM

named_theorems Syscall_AI_assms

crunch typ_at[wp, Syscall_AI_assms]: invoke_irq_control "\<lambda>s. P (typ_at T p s)"

lemma obj_refs_cap_rights_update[simp, Syscall_AI_assms]:
  "obj_refs (cap_rights_update rs cap) = obj_refs cap"
  by (simp add: cap_rights_update_def acap_rights_update_def
         split: cap.split arch_cap.split)

(* FIXME: move to TCB *)
lemma table_cap_ref_mask_cap [Syscall_AI_assms]:
  "table_cap_ref (mask_cap R cap) = table_cap_ref cap"
  by (clarsimp simp add:mask_cap_def table_cap_ref_def acap_rights_update_def
    cap_rights_update_def split:cap.splits arch_cap.splits)

lemma diminished_no_cap_to_obj_with_diff_ref [Syscall_AI_assms]:
  "\<lbrakk> cte_wp_at (diminished cap) p s; valid_arch_caps s \<rbrakk>
      \<Longrightarrow> no_cap_to_obj_with_diff_ref cap S s"
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_arch_caps_def)
  apply (frule(1) unique_table_refs_no_cap_asidD)
  apply (clarsimp simp add: no_cap_to_obj_with_diff_ref_def 
    table_cap_ref_mask_cap diminished_def Ball_def)
  done

lemma getDFSR_invs[wp]:
  "valid invs (do_machine_op getDFSR) (\<lambda>_. invs)"
  by (simp add: getDFSR_def do_machine_op_def split_def select_f_returns | wp)+

lemma getFAR_invs[wp]:
  "valid invs (do_machine_op getFAR) (\<lambda>_. invs)"
  by (simp add: getFAR_def do_machine_op_def split_def select_f_returns | wp)+

lemma getIFSR_invs[wp]:
  "valid invs (do_machine_op getIFSR) (\<lambda>_. invs)"
  by (simp add: getIFSR_def do_machine_op_def split_def select_f_returns | wp)+

lemma hv_invs[wp, Syscall_AI_assms]: "\<lbrace>invs\<rbrace> handle_vm_fault t' flt \<lbrace>\<lambda>r. invs\<rbrace>"
  apply (cases flt, simp_all)
  apply (wp|simp)+
  done

lemma hv_inv_ex [Syscall_AI_assms]:
  "\<lbrace>P\<rbrace> handle_vm_fault t vp \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  apply (cases vp, simp_all)
  apply (wp dmo_inv getDFSR_inv getFAR_inv getIFSR_inv getRestartPC_inv 
            det_getRestartPC as_user_inv
         | wpcw | simp)+
  done

lemma handle_vm_fault_valid_fault[wp, Syscall_AI_assms]:
  "\<lbrace>\<top>\<rbrace> handle_vm_fault thread ft -,\<lbrace>\<lambda>rv s. valid_fault rv\<rbrace>"
  apply (cases ft, simp_all)
   apply (wp no_irq_getDFSR no_irq_getIFSR| simp add: valid_fault_def)+
  done

lemma hvmf_active [Syscall_AI_assms]:
  "\<lbrace>st_tcb_at active t\<rbrace> handle_vm_fault t w \<lbrace>\<lambda>rv. st_tcb_at active t\<rbrace>"
  apply (cases w, simp_all)
   apply (wp | simp)+
  done

lemma hvmf_ex_cap[wp, Syscall_AI_assms]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> handle_vm_fault t b \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (cases b, simp_all)
   apply (wp | simp)+
  done

end

global_interpretation Syscall_AI?: Syscall_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Syscall_AI_assms)?)
  qed

end
