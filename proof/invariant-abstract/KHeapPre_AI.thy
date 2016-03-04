(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory KHeapPre_AI
imports "./$L4V_ARCH/Machine_AI"
begin

context Arch begin

unqualify_consts
  empty_table

unqualify_facts
  empty_table_def

end

primrec
  same_caps :: "Structures_A.kernel_object \<Rightarrow> Structures_A.kernel_object \<Rightarrow> bool"
where
  "same_caps val (CNode sz cs)       = (val = CNode sz cs)"
| "same_caps val (TCB tcb)           = (\<exists>tcb'. val = TCB tcb'
                                         \<and> (\<forall>(getF, t) \<in> ran tcb_cap_cases. getF tcb' = getF tcb))"
| "same_caps val (Endpoint ep)       = is_ep val"
| "same_caps val (Notification ntfn) = is_ntfn val"
| "same_caps val (ArchObj ao)        = (\<exists>ao'. val = ArchObj ao')"


lemma same_caps_more_simps[simp]:
 "same_caps (CNode sz cs) val       = (val = CNode sz cs)"
 "same_caps (TCB tcb)     val       = (\<exists>tcb'. val = TCB tcb'
                                         \<and> (\<forall>(getF, t) \<in> ran tcb_cap_cases. getF tcb' = getF tcb))"
 "same_caps (Endpoint ep) val       = is_ep val"
 "same_caps (Notification ntfn) val = is_ntfn val"
 "same_caps (ArchObj ao) val        = (\<exists>ao'. val = ArchObj ao')"
 by (cases val, (fastforce simp: is_obj_defs)+)+

lemma dmo_return [simp]:
  "do_machine_op (return x) = return x"
  by (simp add: do_machine_op_def select_f_def return_def gets_def get_def 
                bind_def modify_def put_def)

fun
  non_arch_obj :: "kernel_object \<Rightarrow> bool" where
  "non_arch_obj (ArchObj _) = False"
  | "non_arch_obj _ = True"

lemma get_object_sp:
  "\<lbrace>P\<rbrace> get_object p \<lbrace>\<lambda>r. P and ko_at r p\<rbrace>"
  apply (simp add: get_object_def)
  apply wp
  apply (auto simp add: obj_at_def)
  done



locale arch_only_obj_pred =
  fixes P :: "kernel_object \<Rightarrow> bool"
  assumes arch_only: "(\<And>ko. \<forall>ako. ko \<noteq> ArchObj ako \<Longrightarrow> \<not> P ko)" 
begin

lemma
  obj_at_aobj_at: 
  "obj_at P = aobj_at (\<lambda>ao. P (ArchObj ao))"
  apply (insert arch_only)
  apply (rule ext)+
  apply (clarsimp simp add: aobj_at_def2 obj_at_def)
  apply safe
  apply (case_tac ko; simp)
  apply (case_tac ko; simp)
  done

lemma
  obj_at_lift:
  assumes obj_at: "\<lbrace>aobj_at (\<lambda>ao. P (ArchObj ao)) p\<rbrace> f \<lbrace>\<lambda>r. aobj_at (\<lambda>ao. P (ArchObj ao)) p\<rbrace>"
  shows "\<lbrace>obj_at P p\<rbrace> f \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  apply (simp add: obj_at_aobj_at)
  apply (rule obj_at)
  done


end

interpretation arch_only_obj_pred "empty_table S" for S
  apply unfold_locales
  by (simp add: empty_table_def)

end