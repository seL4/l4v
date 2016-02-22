(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchKHeap_AI
imports "../KHeapPre_AI"
begin

context ARM begin


lemma pspace_in_kernel_window_atyp_lift_strong:
  assumes atyp_inv: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  assumes arch_inv: "\<And>P. \<lbrace>\<lambda>s. P (arm_kernel_vspace (arch_state s))\<rbrace> f \<lbrace>\<lambda>r s. P (arm_kernel_vspace (arch_state s))\<rbrace>"
  shows      "\<lbrace>\<lambda>s. pspace_in_kernel_window s\<rbrace> f \<lbrace>\<lambda>rv s. pspace_in_kernel_window s\<rbrace>"
  apply (simp add: pspace_in_kernel_window_def)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. arm_kernel_vspace (arch_state s)", OF _ arch_inv])
   apply (rule hoare_vcg_all_lift)
   apply (simp add: obj_bits_T)
   apply (simp add: valid_def)
  apply clarsimp
  subgoal for _ x s _ _ ko
  apply (cases "kheap s x")
  apply (frule use_valid[OF _ atyp_inv, where P1= "\<lambda>x. \<not> x" and T1="a_type ko" and p1=x];
          simp add: obj_at_def a_type_def)

   subgoal for ko'
   apply (drule spec[of _ ko'])
   apply (simp add: obj_bits_T)
   apply (frule use_valid[OF _ atyp_inv, where P1= "\<lambda>x. x" and T1="a_type ko'" and p1=x])
   by (simp add: obj_at_def a_type_def)+
 done
 done

lemma pspace_in_kernel_window_atyp_lift:
  assumes atyp_inv: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  assumes arch_inv: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. pspace_in_kernel_window s\<rbrace> f \<lbrace>\<lambda>rv s. pspace_in_kernel_window s\<rbrace>"
  by (rule pspace_in_kernel_window_atyp_lift_strong[OF atyp_inv arch_inv])


lemma cap_refs_in_kernel_window_arch_update[simp]:
  "arm_kernel_vspace (f (arch_state s)) = arm_kernel_vspace (arch_state s)
     \<Longrightarrow> cap_refs_in_kernel_window (arch_state_update f s) = cap_refs_in_kernel_window s"
  by (simp add: cap_refs_in_kernel_window_def not_kernel_window_arch_def)


lemma
  ex_ako_at_def2: 
  "(\<exists>ko. ako_at ko p s \<and> P ko) = (aobj_at P p s)"
  by (simp add: aobj_at_def)

lemma vs_lookup_aobj_at_lift:
  assumes obj_at: "\<And>P P' p. \<lbrace>\<lambda>s. P (aobj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' p s)\<rbrace>"
  assumes arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> f \<lbrace>\<lambda>rv s. P (vs_lookup s)\<rbrace>"
  apply (simp add: vs_lookup_def vs_lookup1_def)
  apply (simp add: ex_ako_at_def2)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch_state])
  apply (rule hoare_lift_Pf[where f="\<lambda>s rs p rs' p'. aobj_at (P' p rs rs' p') p s" for P'])
   apply (rule hoare_vcg_prop)
  apply (clarsimp simp add: valid_def)
  apply (erule_tac P=P in rsubst)
  apply (rule ext)+
  apply (erule use_valid, rule obj_at, simp)
  done

lemma vs_lookup_pages_aobj_at_lift:
  assumes obj_at: "\<And>P P' p. \<lbrace>\<lambda>s. P (aobj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' p s)\<rbrace>"
  assumes arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>rv s. P (vs_lookup_pages s)\<rbrace>"
  apply (simp add: vs_lookup_pages_def vs_lookup_pages1_def)
  apply (simp add: ex_ako_at_def2)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch_state])
  apply (rule hoare_lift_Pf[where f="\<lambda>s rs p rs' p'. aobj_at (P' p rs rs' p') p s" for P'])
   apply (rule hoare_vcg_prop)
  apply (clarsimp simp add: valid_def)
  apply (erule_tac P=P in rsubst)
  apply (rule ext)+
  apply (erule use_valid, rule obj_at, simp)
  done

lemma valid_arch_objs_lift_weak:
  assumes obj_at: "\<And>P P' p. \<lbrace>\<lambda>s. P (aobj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' p s)\<rbrace>"
  assumes arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>valid_arch_objs\<rbrace> f \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (rule valid_arch_objs_lift)
    apply (rule vs_lookup_aobj_at_lift)
     apply (rule obj_at arch_state)+
  done

end
  

end