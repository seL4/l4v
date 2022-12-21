(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchKHeap_AI
imports KHeapPre_AI
begin

(* FIXME AARCH64: if_option is missing all cases for None/Some = if .. *)

declare if_option_Some_eq[simp]

context Arch begin global_naming AARCH64

definition non_vspace_obj :: "kernel_object \<Rightarrow> bool" where
  "non_vspace_obj ko \<equiv> case ko of
     (ArchObj (VCPU _)) \<Rightarrow> True \<comment> \<open>exclude VCPU\<close>
   | (ArchObj _) \<Rightarrow> False
   | _ \<Rightarrow> True"

lemmas non_vspace_obj_simps[simp] =
  non_vspace_obj_def[split_simps kernel_object.split arch_kernel_obj.split]

definition vspace_obj_pred :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> bool" where
  "vspace_obj_pred P \<equiv> \<forall>ko ko'. non_vspace_obj ko \<longrightarrow> non_vspace_obj ko' \<longrightarrow> P ko = P ko'"

(* Not [simp], because we don't always want to break the non_vspace_obj abstraction *)
lemma non_vspace_obj_arch:
  "non_vspace_obj (ArchObj ako) = is_VCPU ako"
  by (cases ako; simp)

(* We could make this the definition of non_vspace_obj_proj, but we wouldn't get nice simp rules *)
lemma non_vspace_obj_proj:
  "non_vspace_obj ko = ((aobj_of |> vspace_obj_of) ko = None)"
  by (cases ko; simp add: in_opt_map_None_eq non_vspace_obj_arch vspace_obj_of_None)

lemma vspace_obj_imp: "non_arch_obj ko \<Longrightarrow> non_vspace_obj ko"
  by (clarsimp simp: non_vspace_obj_def non_arch_obj_def
               split: kernel_object.split arch_kernel_obj.split)

lemma vspace_obj_predE:
  "\<lbrakk>vspace_obj_pred P; non_vspace_obj ko; non_vspace_obj ko'\<rbrakk> \<Longrightarrow> P ko = P ko'"
  unfolding vspace_obj_pred_def
  by blast

lemma vspace_pred_imp: "vspace_obj_pred P \<Longrightarrow> arch_obj_pred P"
  by (clarsimp simp: arch_obj_pred_def elim!: vspace_obj_predE dest!: vspace_obj_imp)+

definition
  "vspace_obj_fun_lift P F c \<equiv> case c of
     ArchObj (VCPU vcpu) \<Rightarrow> F
   | ArchObj ac \<Rightarrow> P ac
   | _ \<Rightarrow> F"

lemmas vspace_obj_fun_lift_simps[simp] =
  vspace_obj_fun_lift_def[split_simps kernel_object.split arch_kernel_obj.split]

lemma vspace_objs_of_Some_obj_at:
  "(vspace_objs_of s p = Some vso) =
   obj_at (\<lambda>ko. \<exists>ao. ko = ArchObj ao \<and> vspace_obj_of ao = Some vso) p s"
  by (auto simp: in_opt_map_eq obj_at_def)

lemma vspace_objs_of_None_obj_at:
  "(vspace_objs_of s p = None) =
   (\<not>obj_at (\<lambda>ko. \<exists>ao. ko = ArchObj ao \<and> \<not>is_VCPU ao) p s)"
  by (auto simp: opt_map_def obj_at_def vspace_obj_of_None split: option.splits)

lemma vspace_obj_pred_vspace_objs:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule rsubst[where P=P])
  apply (rule ext)+
  apply (rename_tac s rv s' p)
  apply (case_tac "vspace_objs_of s p")
   apply (simp add: vspace_objs_of_None_obj_at)
   apply (drule use_valid, rule assms[where P="\<lambda>x. \<not>x"]; assumption?)
    apply (auto simp: vspace_obj_pred_def non_vspace_obj_def vspace_obj_of_def
                split: kernel_object.splits arch_kernel_obj.splits)[1]
   apply (simp flip: vspace_objs_of_None_obj_at)
  apply (simp add: vspace_objs_of_Some_obj_at)
  apply (drule use_valid, rule assms[where P="\<lambda>x. x"]; assumption?)
  subgoal
    by (auto simp: vspace_obj_pred_def non_vspace_obj_def vspace_obj_of_def is_VCPU_def
             split: kernel_object.splits arch_kernel_obj.splits)[1]
  apply (simp flip: vspace_objs_of_Some_obj_at)
  done

lemma vspace_objs_vspace_obj_pred_dom:
  assumes vs: "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  assumes dom: "\<And>P. f \<lbrace>\<lambda>s. P (dom (kheap s))\<rbrace>"
  shows "vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule rsubst[where P=P])
  apply (rename_tac s rv s')
  apply (frule use_valid, rule_tac P="\<lambda>vso. vso = vspace_objs_of s" in vs, rule refl)
  apply (drule fun_cong[where x=p])
  apply (drule use_valid, rule_tac P="(=) (dom (kheap s))" in dom, rule refl)
  apply (drule dom_eq_All)
  apply (case_tac "vspace_objs_of s p"; clarsimp)
   subgoal
     by (auto simp: obj_at_def vspace_obj_pred_def non_vspace_obj_proj in_opt_map_None_eq in_omonad)[1]
  apply (clarsimp simp: in_omonad obj_at_def vspace_obj_of_Some)
  done

lemma dom_typ_at_lift:
  assumes "\<And>P T p. f \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (dom (kheap s))\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule rsubst[where P=P])
  apply (rename_tac s rv s')
  apply (rule subset_antisym; clarsimp; rename_tac p ko)
   apply (drule use_valid, rule_tac P="\<lambda>x. x" and p=p in assms; fastforce simp: obj_at_def)
  apply (case_tac "kheap s p"; simp)
  apply (drule use_valid, rule_tac P="\<lambda>x. \<not>x" and p=p in assms; fastforce simp: obj_at_def)
  done

lemma vspace_objs_vspace_obj_pred:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  assumes "\<And>P T p. f \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  shows "vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  by (rule vspace_objs_vspace_obj_pred_dom, rule assms, rule dom_typ_at_lift, rule assms)

end

locale vspace_only_obj_pred = Arch +
  fixes P :: "kernel_object \<Rightarrow> bool"
  assumes vspace_only: "vspace_obj_pred P"

sublocale vspace_only_obj_pred < arch_only_obj_pred
  using vspace_pred_imp[OF vspace_only] by unfold_locales

context Arch begin global_naming AARCH64

lemma valid_vspace_obj_lift:
  assumes "\<And>T p. T \<noteq> AVCPU \<Longrightarrow> f \<lbrace>typ_at (AArch T) p\<rbrace>"
  shows "f \<lbrace>valid_vspace_obj level obj\<rbrace>"
  by (cases obj; wpsimp wp: assms hoare_vcg_ball_lift valid_pte_lift)

lemma vspace_obj_of_aa_type:
  "vspace_obj_of ako = vspace_obj_of ako' \<Longrightarrow> aa_type ako = aa_type ako'"
  by (cases ako; cases ako'; simp add: vspace_obj_of_def)

lemma valid_vspace_objs_of_typ_at:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  shows "T \<noteq> AVCPU \<Longrightarrow> f \<lbrace>typ_at (AArch T) p\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (rename_tac s rv s')
  apply (drule use_valid, rule_tac P="(=) (vspace_objs_of s)" in assms, rule refl)
  apply (drule fun_cong[where x=p])
  by (auto simp: obj_at_def opt_map_def vspace_obj_of_None is_VCPU_def
           intro!: vspace_obj_of_aa_type split: option.splits)

lemma valid_vspace_objs_lift_vs_lookup:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  shows   "f \<lbrace>valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift valid_vspace_obj_lift assms
                 valid_vspace_objs_of_typ_at)

lemma vspace_obj_pred_a_type[intro, simp]:
  "T \<noteq> AVCPU \<Longrightarrow> vspace_obj_pred (\<lambda>ko. a_type ko = AArch T)"
  by (auto simp add: vspace_obj_pred_def a_type_def
           split: kernel_object.splits arch_kernel_obj.splits)

lemma non_vspace_objs[intro]:
  "non_vspace_obj (Endpoint ep)"
  "non_vspace_obj (CNode sz cnode_contents)"
  "non_vspace_obj (TCB tcb)"
  "non_vspace_obj (Notification notification)"
  "non_vspace_obj (ArchObj (VCPU vcpu))"
  by (auto)

lemma vspace_obj_pred_fun_lift: "vspace_obj_pred (\<lambda>ko. F (vspace_obj_fun_lift P N ko))"
  by (auto simp: vspace_obj_pred_def vspace_obj_fun_lift_def
           split: kernel_object.splits arch_kernel_obj.splits)

lemmas vspace_obj_pred_fun_lift_id[simp]
  = vspace_obj_pred_fun_lift[where F=id, simplified]

lemmas vspace_obj_pred_fun_lift_k[intro]
  = vspace_obj_pred_fun_lift[where F="K R" for R, simplified]

lemmas vspace_obj_pred_fun_lift_el[simp]
  = vspace_obj_pred_fun_lift[where F="\<lambda> S. x \<in> S" for x, simplified]

lemma vspace_obj_pred_const_conjI[intro]:
  "\<lbrakk> vspace_obj_pred P; vspace_obj_pred P' \<rbrakk> \<Longrightarrow> vspace_obj_pred (\<lambda>ko. P ko \<and> P' ko)"
  unfolding vspace_obj_pred_def by blast

lemma vspace_obj_pred_fI:
  "(\<And>x. vspace_obj_pred (P x)) \<Longrightarrow> vspace_obj_pred (\<lambda>ko. f (\<lambda>x. P x ko))"
  unfolding vspace_obj_pred_def
  apply (intro allI impI) \<comment> \<open>clarsimp loops\<close>
  apply (rule arg_cong[where f=f])
  by blast

lemmas [intro!] = vspace_obj_pred_fI[where f=All] vspace_obj_pred_fI[where f=Ex]

lemma kheap_typ_only:
  "(\<forall>p ko. kheap s p = Some ko \<longrightarrow> P p (a_type ko)) = (\<forall>p T. typ_at T p s \<longrightarrow> P p T)"
  by (auto simp: obj_at_def)

lemma pspace_in_kernel_window_atyp_lift_strong:
  assumes "\<And>P p T. f \<lbrace>\<lambda>s. P (typ_at T p s) \<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arm_kernel_vspace (arch_state s))\<rbrace>"
  shows      "\<lbrace>\<lambda>s. pspace_in_kernel_window s\<rbrace> f \<lbrace>\<lambda>rv s. pspace_in_kernel_window s\<rbrace>"
  unfolding pspace_in_kernel_window_def obj_bits_T
  apply (rule hoare_lift_Pf[where f="\<lambda>s. arm_kernel_vspace (arch_state s)"])
   apply (subst kheap_typ_only)+
   apply (wpsimp wp: hoare_vcg_all_lift wp: assms)+
  done

lemma pspace_in_kernel_window_atyp_lift:
  assumes "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. pspace_in_kernel_window s\<rbrace> f \<lbrace>\<lambda>rv s. pspace_in_kernel_window s\<rbrace>"
  by (rule pspace_in_kernel_window_atyp_lift_strong[OF assms])

lemma cap_refs_in_kernel_window_arch_update[simp]:
  "arm_kernel_vspace (f (arch_state s)) = arm_kernel_vspace (arch_state s)
   \<Longrightarrow> cap_refs_in_kernel_window (arch_state_update f s) = cap_refs_in_kernel_window s"
  by (simp add: cap_refs_in_kernel_window_def)

lemma in_user_frame_obj_pred_lift:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  shows "f \<lbrace>in_user_frame p\<rbrace> "
  unfolding in_user_frame_def
  by (wpsimp wp: hoare_vcg_ex_lift assms)

lemma pool_for_asid_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  by (wpsimp simp: pool_for_asid_def wp: assms)

lemma vs_lookup_table_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_table level asid vref s)\<rbrace>"
  apply (simp add: vs_lookup_table_def obind_def split: option.splits)
  apply (wpsimp wp: assms hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift' pool_for_asid_lift
                simp: not_le)
  done

lemma vs_lookup_slot_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_slot level asid vref s)\<rbrace>"
  apply (simp add: vs_lookup_slot_def obind_def split: option.splits)
  apply (wpsimp wp: assms hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift' pool_for_asid_lift
                    vs_lookup_table_lift
                simp: not_le)
  done

lemma vs_lookup_target_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_target level asid vref s)\<rbrace>"
  apply (simp add: vs_lookup_target_def obind_def split: option.splits)
  apply (wpsimp wp: assms hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift' pool_for_asid_lift
                    vs_lookup_slot_lift
                simp: not_le)
  done

lemma vs_lookup_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  apply (rule_tac P=P in hoare_liftP_ext)+
  apply (rename_tac P asid)
  apply (rule_tac P=P in hoare_liftP_ext)
  by (rule vs_lookup_table_lift; rule assms)

lemma vs_lookup_vspace_aobjs_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows " f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  by (rule vs_lookup_lift; rule assms)

lemma aobjs_of_ako_at_Some:
  "(aobjs_of s p = Some ao) = ako_at ao p s"
  by (simp add: obj_at_def in_opt_map_eq)

lemma aobjs_of_ako_at_None:
  "(aobjs_of s p = None) = (\<not> obj_at (\<lambda>obj. \<exists>ao. obj = ArchObj ao) p s)"
  apply (clarsimp simp: obj_at_def opt_map_def split: option.splits)
  apply (rename_tac ao, case_tac ao; simp)
  done

lemma aobjs_of_vspace_eq:
  "\<lbrakk> vspace_objs_of s = vspace_objs_of s'; vcpus_of s = vcpus_of s'\<rbrakk> \<Longrightarrow> aobjs_of s = aobjs_of s'"
  apply (rule ext, rename_tac p)
  apply (drule_tac x=p in fun_cong)+
  apply (case_tac "aobjs_of s' p"; simp)
   apply (auto simp: opt_map_left_None in_opt_map_None_eq vspace_obj_of_None)[1]
  by (auto simp: opt_map_def vspace_obj_of_def is_VCPU_def split: option.splits if_split_asm)

lemma aobjs_of_vspace_cases:
  assumes vspace: "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  assumes vcpus: "\<And>P. f \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  unfolding valid_def
  apply clarsimp
  apply (rename_tac s rv s')
  apply (erule_tac P=P in rsubst)
  apply (frule use_valid, rule_tac P="\<lambda>vso. vso = vspace_objs_of s" in vspace, rule refl)
  apply (frule use_valid, rule_tac P="\<lambda>vcpus. vcpus = vcpus_of s" in vcpus, rule refl)
  apply (drule aobjs_of_vspace_eq; simp)
  done

lemma vspace_objs_of_pts_eq:
  "vspace_objs_of s = vspace_objs_of s' \<Longrightarrow> pts_of s = pts_of s'"
  apply (rule ext, rename_tac p)
  apply (drule_tac x=p in fun_cong)+
  by (auto simp: opt_map_def vspace_obj_of_def is_VCPU_def split: option.splits if_split_asm)

lemma vspace_objs_of_aps_eq:
  "vspace_objs_of s = vspace_objs_of s' \<Longrightarrow> asid_pools_of s = asid_pools_of s'"
  apply (rule ext, rename_tac p)
  apply (drule_tac x=p in fun_cong)+
  by (auto simp: opt_map_def vspace_obj_of_def is_VCPU_def split: option.splits if_split_asm)

lemma vspace_objs_of_pts_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (pts_of s)\<rbrace>"
  unfolding valid_def
  apply clarsimp
  apply (rename_tac s rv s')
  apply (erule_tac P=P in rsubst)
  apply (frule use_valid, rule_tac P="\<lambda>vso. vso = vspace_objs_of s" in assms, rule refl)
  by (drule vspace_objs_of_pts_eq, simp)

lemma vspace_objs_of_aps_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding valid_def
  apply clarsimp
  apply (rename_tac s rv s')
  apply (erule_tac P=P in rsubst)
  apply (frule use_valid, rule_tac P="\<lambda>vso. vso = vspace_objs_of s" in assms, rule refl)
  by (drule vspace_objs_of_aps_eq, simp)

lemma vspace_obj_pred_aobjs:
  assumes vspace: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes vcpus: "\<And>P. f \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  shows "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  by (rule aobjs_of_vspace_cases, rule vspace_obj_pred_vspace_objs, erule vspace, rule vcpus)

lemma vs_lookup_vspace_objs_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  by (intro vs_lookup_lift vspace_objs_of_pts_lift vspace_objs_of_aps_lift assms)

lemma vs_lookup_vspace_obj_at_lift:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  by (intro vs_lookup_vspace_objs_lift vspace_obj_pred_vspace_objs assms)

lemma vs_lookup_pages_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  apply (rule_tac P=P in hoare_liftP_ext)+
  apply (rename_tac P asid)
  apply (rule_tac P=P in hoare_liftP_ext)
  by (rule vs_lookup_target_lift; fact)

lemma vs_lookup_pages_vspace_aobjs_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  by (wpsimp wp: vs_lookup_pages_lift assms)

lemma vs_lookup_pages_vspace_objs_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  by (intro vs_lookup_pages_lift vspace_objs_of_pts_lift vspace_objs_of_aps_lift assms)

lemma vs_lookup_pages_vspace_obj_at_lift:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  by (intro vs_lookup_pages_vspace_objs_lift vspace_obj_pred_vspace_objs assms)

lemma vs_lookup_pages_arch_obj_at_lift:
  assumes "\<And>P P' p. arch_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  by (intro vs_lookup_pages_vspace_obj_at_lift assms vspace_pred_imp)

lemma valid_vspace_objs_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vspace_objs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows   "f \<lbrace>valid_vspace_objs\<rbrace>"
  by (intro valid_vspace_objs_lift_vs_lookup vs_lookup_vspace_objs_lift assms)

lemma valid_vspace_objs_lift_weak:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>valid_vspace_objs\<rbrace>"
  by (intro valid_vspace_objs_lift vspace_obj_pred_vspace_objs assms)

lemma set_pt_pts_of:
  "\<lbrace>\<lambda>s. pts_of s p \<noteq> None \<longrightarrow> P (pts_of s (p \<mapsto> pt)) \<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (pts_of s)\<rbrace>"
  unfolding set_pt_def
  by (wpsimp wp: set_object_wp)
     (auto elim!: rsubst[where P=P] simp: opt_map_def split: option.splits)

lemma pte_ptr_eq:
  "\<lbrakk> table_index pt_t p = table_index pt_t p';
     table_base pt_t p = table_base pt_t p';
     is_aligned p pte_bits; is_aligned p' pte_bits \<rbrakk>
   \<Longrightarrow> p = p'"
  apply (rule word_eqI)
  apply (clarsimp simp: word_size is_aligned_nth)
  apply (case_tac "n < pte_bits", simp)
  apply (drule_tac x="n-pte_bits" in word_eqD)
  apply (drule_tac x="n" in word_eqD)
  apply (simp add: word_size neg_mask_test_bit nth_shiftr not_less)
  apply (case_tac "pt_bits pt_t \<le> n", simp)
  by (fastforce simp: not_le bit_simps)

lemma pt_type_pt_upd[simp]:
  "pt_type (pt_upd pt idx pte) = pt_type pt"
  by (cases pt; simp add: pt_upd_def)

lemma pt_apply_pt_upd_eq[simp]:
  "pt_apply (pt_upd pt idx pte) idx = pte"
  by (cases pt; clarsimp simp: pt_upd_def)

lemma table_index_VSRoot_inj[simp]:
  "\<lbrakk> is_aligned p pte_bits; is_aligned p' pte_bits \<rbrakk> \<Longrightarrow>
   ((ucast (table_index VSRootPT_T p')::vs_index) = ucast (table_index VSRootPT_T p)) =
   (table_index VSRootPT_T p' = table_index VSRootPT_T p)"
  by (rule iffI; word_eqI_solve simp: bit_simps)

lemma table_index_NormalPT_inj[simp]:
  "\<lbrakk> is_aligned p pte_bits; is_aligned p' pte_bits \<rbrakk> \<Longrightarrow>
   ((ucast (table_index NormalPT_T p')::pt_index) = ucast (table_index NormalPT_T p)) =
   (table_index NormalPT_T p' = table_index NormalPT_T p)"
  by (rule iffI; word_eqI_solve simp: bit_simps)

lemma pt_apply_pt_upd_neq:
  "\<lbrakk>p' \<noteq> p; is_aligned p pte_bits; is_aligned p' pte_bits; table_base pt_t p' = table_base pt_t p;
    pt_t = pt_type pt\<rbrakk>
   \<Longrightarrow> pt_apply (pt_upd pt (table_index pt_t p) pte) (table_index pt_t p') =
       pt_apply pt (table_index pt_t p')"
  by (cases pt; fastforce simp: pt_apply_def pt_upd_def dest!: pte_ptr_eq)

lemma ptes_of_pts_of_upd:
  "\<lbrakk> is_aligned p pte_bits; pts_of s (table_base pt_t p) = Some pt; pt_t = pt_type pt \<rbrakk> \<Longrightarrow>
   (\<lambda>pt_t' p'. level_pte_of pt_t' p'
                            (pts_of s (table_base pt_t p \<mapsto> pt_upd pt (table_index pt_t p) pte))) =
   ptes_of s (pt_t, p \<mapsto> pte)"
  apply (rule ext)+
  apply (clarsimp simp: fun_upd2_def)
  apply (intro conjI impI; clarsimp simp:  level_pte_of_def)
     apply (fastforce simp: in_omonad)
    apply (fastforce simp: obind_def split: option.splits)
   apply (fastforce simp: obind_def pt_apply_pt_upd_neq split: option.splits)
  apply (fastforce simp: obind_def split: option.splits)
  done

lemma store_pte_ptes_of_full:
  "\<lbrace>\<lambda>s. ptes_of s pt_t p \<noteq> None \<longrightarrow> P ((ptes_of s) (pt_t, p \<mapsto> pte)) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_ s. P (ptes_of s)\<rbrace>"
  unfolding store_pte_def
  apply (wpsimp wp: set_pt_pts_of simp_del: fun_upd_apply)
  apply (simp add: level_pte_of_pt pt_at_eq ptes_of_pts_of_upd)
  done

lemma store_pte_ptes_of:
  "\<lbrace>\<lambda>s. ptes_of s pt_t p \<noteq> None \<longrightarrow> P (ptes_of s pt_t (p \<mapsto> pte)) \<rbrace>
   store_pte pt_t p pte \<lbrace>\<lambda>_ s. P (ptes_of s pt_t)\<rbrace>"
  by (wpsimp wp: store_pte_ptes_of_full simp: fun_upd2_def simp_del: fun_upd_apply)

definition level_of_slot :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> vm_level"
  where
  "level_of_slot asid vref p s \<equiv>
     GREATEST level. vs_lookup_slot level asid vref s = Some (level, p)"

lemma level_of_slotI:
  "\<lbrakk> vs_lookup_slot level' asid vref s = Some (level', p); level < level'\<rbrakk>
   \<Longrightarrow> vs_lookup_slot (level_of_slot asid vref p s) asid vref s = Some (level_of_slot asid vref p s, p)
       \<and> level < level_of_slot asid vref p s"
  by (auto simp: level_of_slot_def dest: vm_level.GreatestI vm_level.Greatest_le)

lemma pool_for_asid_no_pt:
  "\<lbrakk> pool_for_asid asid s = Some p; pts_of s p = Some pte; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> False"
  unfolding pool_for_asid_def
  by (fastforce dest: pspace_alignedD dest!: valid_asid_tableD
                simp: bit_simps obj_at_def ptes_of_Some in_omonad)

lemma is_aligned_table_base[intro!, simp]:
  "is_aligned (table_base pt p) (table_size pt)"
  by (simp add: pt_bits_def)

lemma ptes_of_other_typ_at:
  "\<lbrakk> ptes_of s pt_t p = Some pte; typ_at T p s; T \<noteq> AArch (APageTable pt_t);
     pspace_aligned s; pspace_distinct s \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: obj_at_def in_omonad level_pte_of_def)
  apply (rename_tac ko pt)
  apply (case_tac "table_base (pt_type pt) p = p", simp)
  apply (frule (1) pspace_alignedD)
  apply (frule (3) pspace_distinctD)
  apply (simp add: is_aligned_no_overflow_mask and_neg_mask_plus_mask_mono pt_bits_def)
  apply (erule notE, rule order.trans[where b=p])
   apply (simp add: word_and_le2)
  apply (simp add: is_aligned_no_overflow_mask)
  done

lemma pool_for_asid_no_pte:
  "\<lbrakk> pool_for_asid asid s = Some p; ptes_of s pt_t p = Some pte; valid_asid_table s;
     pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> False"
  unfolding pool_for_asid_def
  by (fastforce dest: valid_asid_tableD elim: ptes_of_other_typ_at)

lemma vs_lookup_table_no_asid:
  "\<lbrakk> vs_lookup_table asid_pool_level asid vref s = Some (asid_pool_level, p);
     ptes_of s pt_t p = Some pte; valid_asid_table s; pspace_aligned s; pspace_distinct s \<rbrakk>
  \<Longrightarrow> False"
  unfolding vs_lookup_table_def
  by (fastforce dest: pool_for_asid_no_pte simp: in_omonad)

lemma vs_lookup_table_no_asid_pt:
  "\<lbrakk> vs_lookup_table asid_pool_level asid vref s = Some (asid_pool_level, p);
     pts_of s p = Some pte; valid_asid_table s; pspace_aligned s \<rbrakk>
  \<Longrightarrow> False"
  unfolding vs_lookup_table_def
  by (fastforce dest: pool_for_asid_no_pt simp: in_omonad)

lemma vs_lookup_slot_no_asid:
  "\<lbrakk> vs_lookup_slot asid_pool_level asid vref s = Some (asid_pool_level, p);
     ptes_of s pt_t p = Some pte; valid_asid_table s; pspace_aligned s; pspace_distinct s \<rbrakk>
  \<Longrightarrow> False"
  unfolding vs_lookup_slot_def vs_lookup_table_def
  by (fastforce dest: pool_for_asid_no_pte simp: in_omonad)

lemma pts_of_type_unique:
  "\<lbrakk> pts_of s (table_base (pt_type pt) p) = Some pt;
     pts_of s (table_base (pt_type pt') p) = Some pt';
     pspace_distinct s \<rbrakk>
   \<Longrightarrow> pt_type pt = pt_type pt'"
  by (cases "table_base (pt_type pt') p = table_base (pt_type pt) p", simp)
     (fastforce dest: pspace_distinctD
                simp: in_omonad is_aligned_no_overflow_mask and_neg_mask_plus_mask_mono pt_bits_def
                      word_and_le)

lemma pts_of_level_type_unique:
  "\<lbrakk> pts_of s (table_base (level_type level) pte_ptr) = Some pt;
     pts_of s (table_base (level_type level') pte_ptr) = Some pt';
     pt_type pt = level_type level; pt_type pt' = level_type level';
     pspace_distinct s \<rbrakk>
   \<Longrightarrow> level_type level' = level_type level"
  by (metis pts_of_type_unique)

(* If we look up a slot for some level, and we know there is a pte for type pt_t at that slot,
   then it must agree with the level type of the lookup. *)
lemma vs_lookup_slot_level_type:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, p); ptes_of s pt_t p = Some pte;
     vref \<in> user_region; level \<le> max_pt_level;
     valid_asid_table s; pspace_aligned s; pspace_distinct s; valid_vspace_objs s \<rbrakk>
   \<Longrightarrow> level_type level = pt_t"
  by (fastforce simp: ptes_of_Some intro!: pts_of_type_unique dest: valid_vspace_objs_strong_slotD)

(* Removing a page table pte entry at p will cause lookups to stop at higher levels than requested.
   If performing a shallower lookup than the one requested results in p, then any deeper lookup
   in the updated state will return a higher level result along the original path. *)
lemma vs_lookup_non_PageTablePTE:
  "\<lbrakk> ptes_of s pt_t p \<noteq> None; ptes_of s' = ptes_of s (pt_t, p \<mapsto> pte);
     \<not> is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s; asid_table s' = asid_table s;
     vref \<in> user_region;
     valid_asid_table s; pspace_aligned s; pspace_distinct s; valid_vspace_objs s \<rbrakk> \<Longrightarrow>
   vs_lookup_table level asid vref s' =
     (if \<exists>level'. vs_lookup_slot level' asid vref s = Some (level', p) \<and> level < level'
      then vs_lookup_table (level_of_slot asid vref p s) asid vref s
      else vs_lookup_table level asid vref s)"
  apply (induct level rule: vm_level.from_top_full_induct[where y=max_pt_level])
   apply (clarsimp simp: geq_max_pt_level)
   apply (erule disjE; clarsimp)
    apply (rule conjI; clarsimp)
     apply (fastforce dest!: vs_lookup_slot_no_asid)
    apply (simp add: vs_lookup_table_def pool_for_asid_def obind_def split: option.splits)
   apply (simp add: vs_lookup_table_def pool_for_asid_def obind_def split: option.splits)
  apply clarsimp
  apply (rename_tac level old_pte)
  apply (rule conjI; clarsimp)
   apply (drule (1) level_of_slotI, clarsimp)
   apply (prop_tac "level_type (level_of_slot asid vref p s) = pt_t")
    apply (fastforce simp flip: asid_pool_level_neq
                     dest!: vs_lookup_slot_no_asid
                     intro!: vs_lookup_slot_level_type)
   apply (subst vs_lookup_split[where level'="level_of_slot asid vref p s"], simp)
    apply (rule ccontr)
    apply (fastforce dest!: vs_lookup_slot_no_asid simp: not_le)
   apply (clarsimp simp: vs_lookup_slot_def in_obind_eq)
   apply (simp split: if_split_asm)
    apply (fastforce dest!: vs_lookup_table_no_asid)
   apply (subst pt_walk.simps)
   apply (simp add: in_obind_eq fun_upd2_def)
  subgoal for x old_pte
    apply (subst vs_lookup_split[where level'="x+1"])
      apply (simp add: less_imp_le)
     apply (simp add: vm_level.plus_one_leq)
    apply (subst (2) vs_lookup_split[where level'="x+1"])
      apply (simp add: less_imp_le)
     apply (simp add: vm_level.plus_one_leq)
    apply (erule_tac x="x+1" in allE)
    apply (simp add: less_imp_le)
    apply (simp  split: if_split_asm)
     apply (erule_tac x="level'" in allE, simp)
     apply (meson max_pt_level_less_Suc less_imp_le less_trans)
    apply (clarsimp simp: obind_def split: option.splits)
    apply (subst pt_walk.simps)
    apply (subst (2) pt_walk.simps)
    apply (simp add: less_imp_le cong: if_cong)
    apply (subgoal_tac "(ptes_of s (pt_t, p \<mapsto> pte)) (level_type (x + 1)) (pt_slot_offset (x + 1) b vref)
                        = ptes_of s (level_type (x + 1)) (pt_slot_offset (x + 1) b vref)")
     apply (simp add: obind_def split: option.splits)
    apply (clarsimp simp: fun_upd2_def)
    apply (subgoal_tac "vs_lookup_slot (x+1) asid vref s = Some (x+1, p)")
     apply fastforce
    by (clarsimp simp: vs_lookup_slot_def in_obind_eq plus_one_eq_asid_pool)
  done

lemma set_pt_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p' s) \<and> (\<forall>T'. atyps_of s p = Some T' \<longrightarrow> T' = APageTable (pt_type pt)) \<rbrace>
   set_pt p pt \<lbrace>\<lambda>_ s. P (typ_at T p' s)\<rbrace>"
  unfolding set_pt_def
  by (wpsimp wp: set_object_wp simp: in_opt_map_eq obj_at_def)

lemma store_pte_typ_at[wp]:
  "store_pte pt_t p' pte \<lbrace> \<lambda>s. P (typ_at T p s) \<rbrace>"
  unfolding store_pte_def
  by (wpsimp wp: set_pt_typ_at simp: in_omonad pt_upd_def split: pt.split)

crunches store_pte
  for kernel_vspace[wp]: "\<lambda>s. P (arm_kernel_vspace (arch_state s))"
  (wp: hoare_drop_imps)

lemma store_pte_non_PageTablePTE_vs_lookup:
  "\<lbrace>\<lambda>s. (ptes_of s pt_t p \<noteq> None \<longrightarrow>
         P (if \<exists>level'. vs_lookup_slot level' asid vref s = Some (level', p) \<and> level < level'
            then vs_lookup_table (level_of_slot asid vref p s) asid vref s
            else vs_lookup_table level asid vref s))
        \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_asid_table s \<and> valid_vspace_objs s
        \<and> \<not> is_PageTablePTE pte \<and> vref \<in> user_region \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_ s. P (vs_lookup_table level asid vref s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp simp: ptes_of_Some)
  apply (erule rsubst[where P=P])
  apply (subst (3) vs_lookup_non_PageTablePTE[where pte=pte])
          apply (fastforce simp: in_omonad level_pte_of_def)
         apply (simp add: ptes_of_pts_of_upd)
        apply (fastforce simp: opt_map_def split: option.splits)+
  done

lemma store_pte_not_ao:
  "\<lbrace>\<lambda>s. \<forall>pt. aobjs_of s (table_base pt_t p) = Some (PageTable pt) \<longrightarrow>
             P (aobjs_of s (table_base pt_t p \<mapsto> PageTable (pt_upd pt (table_index pt_t p) pte)))\<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_ s. P (aobjs_of s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp simp: in_opt_map_eq)
  apply (fastforce simp: opt_map_def elim!: rsubst[where P=P])
  done

lemma valid_vspace_obj_PT_invalidate:
  "valid_vspace_obj level (PageTable pt) s \<Longrightarrow>
   valid_vspace_obj level (PageTable (pt_upd pt i InvalidPTE)) s"
  by (auto simp: pt_upd_def split: pt.split)

lemma store_pte_InvalidPTE_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs and pspace_aligned and pspace_distinct and valid_asid_table\<rbrace>
   store_pte pt_t p InvalidPTE
   \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_imp_lift hoare_vcg_imp_lift'
                    valid_vspace_obj_lift store_pte_non_PageTablePTE_vs_lookup
                    store_pte_not_ao)
  apply (prop_tac "valid_vspace_objs s", simp add: valid_vspace_objs_def)
  apply (rename_tac s bot_level asid vref)
  apply simp
  apply (rule conjI; clarsimp simp: in_omonad)
   apply (rename_tac level slot pte ao pt)
   apply (drule (1) level_of_slotI)
   apply (case_tac "slot = table_base pt_t p"; clarsimp simp del: valid_vspace_obj.simps)
   apply (fastforce intro!: valid_vspace_obj_PT_invalidate)
  apply (rename_tac level slot pte ao pt)
  apply (clarsimp simp: vs_lookup_slot_def)
  apply (case_tac "slot = table_base pt_t p"; clarsimp simp del: valid_vspace_obj.simps)
  apply (fastforce intro!: valid_vspace_obj_PT_invalidate)
  done

lemma set_object_valid_kernel_mappings:
  "set_object ptr ko \<lbrace>valid_kernel_mappings\<rbrace>"
  unfolding set_object_def
  by (wpsimp simp: valid_kernel_mappings_def split: if_split_asm)

(* interface lemma *)
lemmas set_object_v_ker_map = set_object_valid_kernel_mappings

lemma valid_vs_lookup_lift:
  assumes lookup: "\<And>P. f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. f \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  assumes archvspace: "\<And>P. f \<lbrace>\<lambda>s. P (arm_kernel_vspace (arch_state s))\<rbrace>"
  shows "f \<lbrace>valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply clarsimp
  apply (rule hoare_lift_Pf [where f=vs_lookup_pages])
   apply (rule hoare_lift_Pf [where f="\<lambda>s. (caps_of_state s)"])
    apply (rule hoare_lift_Pf [where f="\<lambda>s. (arm_kernel_vspace (arch_state s))"])
     apply (wpsimp wp: lookup cap archvspace)+
  done

lemma valid_arch_caps_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes pts: "\<And>P. f \<lbrace>\<lambda>s. P (pts_of s)\<rbrace>"
  assumes archvspace: "\<And>P. f \<lbrace>\<lambda>s. P (arm_kernel_vspace (arch_state s))\<rbrace>"
  assumes asidtable: "\<And>P. f \<lbrace>\<lambda>s. P (arm_asid_table (arch_state s))\<rbrace>"
  shows "\<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding valid_arch_caps_def
  apply (wpsimp wp: valid_vs_lookup_lift lookup cap archvspace)
   apply (rule hoare_lift_Pf2[where f="\<lambda>s. (caps_of_state s)"])
    apply (wpsimp wp: cap archvspace asidtable pts)+
  done

context
  fixes f :: "'a::state_ext state \<Rightarrow> ('b \<times> 'a state) set \<times> bool"
  assumes arch: "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
begin

context
  assumes vso_at: "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace>"
begin

private lemma pred_vspace_objs_of_lift: "f \<lbrace> \<lambda>s. P (vspace_objs_of s) \<rbrace>"
  by (intro vso_at vspace_obj_pred_vspace_objs)

private lemma pred_pts_of_lift: "f \<lbrace> \<lambda>s. P (pts_of s) \<rbrace>"
  by (intro vspace_objs_of_pts_lift pred_vspace_objs_of_lift)

lemma valid_global_vspace_mappings_lift:
  "f \<lbrace>valid_global_vspace_mappings\<rbrace>"
  unfolding valid_global_vspace_mappings_def
  by wp

lemma valid_arch_caps_lift_weak:
  assumes cap: "(\<And>P. f \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>)"
  shows "f \<lbrace>valid_arch_caps\<rbrace>"
  by (rule valid_arch_caps_lift)
     (wpsimp wp: vs_lookup_pages_vspace_obj_at_lift[OF vso_at] pred_pts_of_lift arch cap)+

lemma valid_global_objs_lift_weak:
  "\<lbrace>valid_global_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  unfolding valid_global_objs_def by wp

lemma valid_asid_map_lift:
    "\<lbrace>valid_asid_map\<rbrace> f \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  by (wpsimp simp: valid_asid_map_def)

lemma valid_kernel_mappings_lift:
    "\<lbrace>valid_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  unfolding valid_kernel_mappings_def by wp

end

context
  assumes aobj_at: "\<And>P P' pd. arch_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace>"
begin

lemma aobjs_of_lift_aobj_at:
  "f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule_tac P=P in rsubst)
  apply (rule ext, rename_tac s' p)
  apply (case_tac "aobjs_of s p")
   apply (simp add: aobjs_of_ako_at_None)
   apply (drule use_valid)
     prefer 2
     apply assumption
    apply (rule aobj_at)
    apply (clarsimp simp: arch_obj_pred_def non_arch_obj_def)
   apply (simp flip: aobjs_of_ako_at_None)
  apply (simp add: aobjs_of_ako_at_Some)
  apply (drule use_valid)
    prefer 2
    apply assumption
   apply (rule aobj_at)
   apply simp
  apply (simp flip: aobjs_of_ako_at_Some)
  done

lemma valid_arch_state_lift_aobj_at:
  "f \<lbrace>valid_arch_state\<rbrace>"
  unfolding valid_arch_state_def valid_asid_table_def valid_global_arch_objs_def pt_at_eq
  apply (wp_pre, wps arch aobjs_of_lift_aobj_at)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift vmid_inv_ap_lift
                     aobjs_of_lift_aobj_at arch)
  apply simp
  done

end
end

lemma equal_kernel_mappings_lift:
  assumes aobj_at: "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace>"
  assumes [wp]: "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>equal_kernel_mappings\<rbrace>"
  by (wpsimp simp: equal_kernel_mappings_def)

lemma valid_machine_state_lift:
  assumes memory: "\<And>P. \<lbrace>\<lambda>s. P (underlying_memory (machine_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (underlying_memory (machine_state s))\<rbrace>"
  assumes aobj_at: "\<And>P' pd. arch_obj_pred P' \<Longrightarrow> \<lbrace>obj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. obj_at P' pd s\<rbrace>"
  shows "\<lbrace>valid_machine_state\<rbrace> f \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def
  apply (rule hoare_lift_Pf[where f="\<lambda>s. underlying_memory (machine_state s)", OF _ memory])
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_vcg_disj_lift[OF _ hoare_vcg_prop])
  apply (rule in_user_frame_lift)
  apply (wp aobj_at; simp)
  done

lemma ako_at_vspace_objs_of:
  assumes "\<And>ao. f \<lbrace>\<lambda>s. ako_at ao p s\<rbrace>"
  shows "f \<lbrace>\<lambda>s. vspace_objs_of s p = Some ako \<rbrace>"
  unfolding valid_def
  apply (clarsimp simp: in_omonad)
  apply (drule use_valid, rule assms, simp add: obj_at_def)
  apply (simp add: obj_at_def)
  done

(* interface lemma; would otherwise be nicer with projections *)
lemma valid_vso_at_lift:
  assumes "\<And>P p T. f \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace>"
  assumes "\<And>ao. f \<lbrace>\<lambda>s. ako_at ao p s\<rbrace>"
  shows "f \<lbrace>valid_vso_at level p\<rbrace>"
  unfolding valid_vso_at_def
  by (wpsimp wp: hoare_vcg_ex_lift assms valid_vspace_obj_typ ako_at_vspace_objs_of)

lemma valid_vso_at_lift_aobj_at:
  assumes aobj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  shows "f \<lbrace>valid_vso_at level p\<rbrace>"
  unfolding valid_vso_at_def
  by (wpsimp wp: hoare_vcg_ex_lift assms vspace_obj_pred_vspace_objs valid_vspace_obj_lift)

lemma valid_global_vspace_mappings_arch_update[simp]:
  "valid_global_vspace_mappings (f s) = valid_global_vspace_mappings s"
  unfolding valid_global_vspace_mappings_def
  by simp

lemma pte_range_empty[simp]:
  "(pte \<in> pt_range (empty_pt pt_t)) = (pte = InvalidPTE)"
  by (simp add: empty_pt_def)

lemma pt_type_empty[simp]:
  "pt_type (empty_pt pt_t) = pt_t"
  by (cases pt_t; simp add: empty_pt_def)

lemma valid_table_caps_ptD:
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PageTableCap p' pt_t None));
     valid_table_caps s; pt_t = level_type level \<rbrakk> \<Longrightarrow>
   \<exists>pt. pts_of s p' = Some pt \<and> valid_vspace_obj level (PageTable pt) s"
  by (fastforce simp: valid_table_caps_def simp del: split_paired_Ex)

lemma store_pte_pred_tcb_at:
  "store_pte pt_t ptr val \<lbrace>pred_tcb_at proj P t\<rbrace>"
  apply (wpsimp simp: store_pte_def set_pt_def wp: set_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def in_opt_map_eq)
  done

lemma in_user_frame_obj_upd:
  "\<lbrakk>kheap s p = Some ko; a_type k = a_type ko\<rbrakk> \<Longrightarrow>
   in_user_frame x (s\<lparr>kheap := \<lambda>a. if a = p then Some k else kheap s a\<rparr>)
   = in_user_frame x s"
  apply (rule iffI)
  apply (clarsimp simp: in_user_frame_def obj_at_def split: if_split_asm)
   apply (elim disjE)
    apply clarsimp
    apply (intro exI)
    apply (rule conjI,assumption)
    apply (simp add: a_type_def)
   apply (fastforce simp: a_type_def)
  apply (clarsimp simp: in_user_frame_def obj_at_def split: if_split_asm)
  apply (rule_tac x = sz in exI)
  apply (intro conjI impI)
    apply (fastforce simp: a_type_def)+
  done

lemma user_mem_obj_upd_dom:
  "\<lbrakk>kheap s p = Some ko; a_type k = a_type ko\<rbrakk> \<Longrightarrow>
   dom (user_mem (s\<lparr>kheap := \<lambda>a. if a = p then Some k else kheap s a\<rparr>))
   = dom (user_mem s)"
  by (clarsimp simp: user_mem_def in_user_frame_obj_upd dom_def)

lemma in_device_frame_obj_upd:
  "\<lbrakk>kheap s p = Some ko; a_type k = a_type ko\<rbrakk> \<Longrightarrow>
   in_device_frame x (s\<lparr>kheap := \<lambda>a. if a = p then Some k else kheap s a\<rparr>)
   = in_device_frame x s"
  apply (rule iffI)
  apply (clarsimp simp: in_device_frame_def obj_at_def split: if_split_asm)
   apply (elim disjE)
    apply clarsimp
    apply (intro exI)
    apply (rule conjI,assumption)
    apply (simp add: a_type_def)
   apply (fastforce simp: a_type_def)
  apply (clarsimp simp: in_device_frame_def obj_at_def split: if_split_asm)
  apply (rule_tac x = sz in exI)
  apply (intro conjI impI; fastforce simp: a_type_def)
  done

lemma device_mem_obj_upd_dom:
  "\<lbrakk>kheap s p = Some ko; a_type k = a_type ko\<rbrakk> \<Longrightarrow>
   dom (device_mem (s\<lparr>kheap := \<lambda>a. if a = p then Some k else kheap s a\<rparr>))
   = dom (device_mem s)"
  by (clarsimp simp: device_mem_def in_device_frame_obj_upd dom_def)

lemma pspace_respects_region_cong[cong]:
  "\<lbrakk>kheap a  = kheap b; device_state (machine_state a) = device_state (machine_state b)\<rbrakk>
  \<Longrightarrow> pspace_respects_device_region a = pspace_respects_device_region b"
  by (simp add: pspace_respects_device_region_def device_mem_def user_mem_def in_device_frame_def
                in_user_frame_def obj_at_def dom_def)

definition "obj_is_device tp dev \<equiv>
  case tp of Untyped \<Rightarrow> dev
    | _ \<Rightarrow>(case (default_object tp dev 0) of (ArchObj (DataPage dev _)) \<Rightarrow> dev
          | _ \<Rightarrow> False)"

lemma cap_is_device_obj_is_device[simp]:
  "cap_is_device (default_cap tp a sz dev) = obj_is_device tp dev"
  by (simp add: default_cap_def arch_default_cap_def obj_is_device_def
                default_object_def  default_arch_object_def
         split: apiobject_type.splits aobject_type.splits)

crunch device_state_inv: storeWord "\<lambda>ms. P (device_state ms)"
  (ignore_del: storeWord)

(* some hyp_ref invariants *)

lemma state_hyp_refs_of_ep_update: "\<And>s ep val. typ_at AEndpoint ep s \<Longrightarrow>
       state_hyp_refs_of (s\<lparr>kheap := kheap s(ep \<mapsto> Endpoint val)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def hyp_refs_of_def)
  done

lemma state_hyp_refs_of_ntfn_update: "\<And>s ep val. typ_at ANTFN ep s \<Longrightarrow>
       state_hyp_refs_of (s\<lparr>kheap := kheap s(ep \<mapsto> Notification val)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def hyp_refs_of_def)
  done

lemma state_hyp_refs_of_tcb_bound_ntfn_update:
       "kheap s t = Some (TCB tcb) \<Longrightarrow>
          state_hyp_refs_of (s\<lparr>kheap := kheap s(t \<mapsto> TCB (tcb\<lparr>tcb_bound_notification := ntfn\<rparr>))\<rparr>)
            = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_state_update:
       "kheap s t = Some (TCB tcb) \<Longrightarrow>
          state_hyp_refs_of (s\<lparr>kheap := kheap s(t \<mapsto> TCB (tcb\<lparr>tcb_state := ts\<rparr>))\<rparr>)
            = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma valid_vcpu_lift:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  assumes t: "\<And>p. \<lbrace>typ_at ATCB p\<rbrace> f \<lbrace>\<lambda>rv. typ_at ATCB p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_vcpu v s\<rbrace> f \<lbrace>\<lambda>rv s. valid_vcpu v s\<rbrace>"
  apply (cases v)
  apply (simp add: valid_vcpu_def | wp x hoare_vcg_disj_lift)+
  apply (case_tac vcpu_tcb; simp, wp t)
  done

lemma default_arch_object_not_live[simp]: "\<not> live (ArchObj (default_arch_object aty dev us))"
  by (clarsimp simp: default_arch_object_def live_def hyp_live_def arch_live_def default_vcpu_def
               split: aobject_type.splits)

lemma default_tcb_not_live[simp]: "\<not> live (TCB default_tcb)"
  by (clarsimp simp: default_tcb_def default_arch_tcb_def live_def hyp_live_def)

lemma valid_vcpu_same_type:
  "\<lbrakk> valid_vcpu v s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> valid_vcpu v (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  by (cases v; case_tac vcpu_tcb; clarsimp simp: valid_vcpu_def typ_at_same_type)

lemma valid_arch_tcb_same_type:
  "\<lbrakk> valid_arch_tcb t s; valid_obj p k s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> valid_arch_tcb t (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  by (auto simp: valid_arch_tcb_def obj_at_def)


(* interface lemma *)
lemma valid_ioports_lift:
  assumes x: "\<And>P. f \<lbrace>\<lambda>rv. P (caps_of_state s)\<rbrace>"
  assumes y: "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows      "f \<lbrace>valid_ioports\<rbrace>"
  by wpsimp

(* interface lemma *)
lemma valid_arch_mdb_lift:
  assumes c: "\<And>P. f \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  assumes r: "\<And>P. f \<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrace>"
  by (wpsimp simp: valid_arch_mdb_def)

(* interface lemma *)
lemma arch_valid_obj_same_type:
  "\<lbrakk> arch_valid_obj ao s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> arch_valid_obj ao (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  apply (cases ao; simp)
  apply (fastforce simp: valid_vcpu_def obj_at_def split: option.splits)
  done

lemma valid_vspace_obj_same_type:
  "\<lbrakk>valid_vspace_obj l ao s;  kheap s p = Some ko; a_type ko' = a_type ko\<rbrakk>
  \<Longrightarrow> valid_vspace_obj l ao (s\<lparr>kheap := kheap s(p \<mapsto> ko')\<rparr>)"
    apply (rule hoare_to_pure_kheap_upd[OF valid_vspace_obj_typ])
    by (auto simp: obj_at_def)

lemma invs_valid_uses[elim!]:
  "invs s \<Longrightarrow> valid_uses s"
  by (simp add: invs_def valid_state_def valid_arch_state_def)

end
end
