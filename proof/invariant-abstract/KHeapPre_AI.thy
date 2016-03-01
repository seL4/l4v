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




end