(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchKHeap_AI
imports KHeapPre_AI
begin

context Arch begin arch_global_naming

fun
  non_vspace_obj :: "kernel_object \<Rightarrow> bool"
where
  "non_vspace_obj (ArchObj (VCPU vcpu)) = True"  (* exclude vcpu *)
| "non_vspace_obj (ArchObj _)           = False"
| "non_vspace_obj _                     = True"

lemma valid_vspace_is_vspace_lift:
  assumes P: "\<And>p T. \<lbrace>(K (is_vspace_typ (AArch T))) and (typ_at (AArch T) p)\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows      "\<lbrace>valid_vspace_obj ob\<rbrace> f \<lbrace>\<lambda>rv. valid_vspace_obj ob\<rbrace>"
  apply (cases ob, simp_all add: aa_type_def)
      apply (rule hoare_vcg_const_Ball_lift)
      apply (wp P, simp)
     apply (rule hoare_vcg_all_lift)
     apply (rename_tac "fun" x)
     apply (case_tac "fun x"; simp_all add: data_at_def hoare_vcg_prop)
      apply (rule hoare_vcg_conj_lift hoare_vcg_disj_lift | wp P | simp )+
    apply (rule hoare_vcg_all_lift)
    apply (rename_tac "fun" x)
    apply (case_tac "fun x";simp_all add: data_at_def hoare_vcg_prop)
      apply (rule hoare_vcg_conj_lift hoare_vcg_disj_lift | wp P | simp )+
  done

lemma obj_at_split: "(obj_at (P xo) p s \<and> (Q xo)) = obj_at (\<lambda>ko. P xo ko \<and> Q xo) p s"
  by (auto simp: obj_at_def)

lemma valid_vspace_objs_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  assumes y: "\<And>ako p. is_vspace_typ (AArch (aa_type ako))
                       \<Longrightarrow> \<lbrace>\<lambda>s. \<not> ko_at (ArchObj ako) p s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> ko_at (ArchObj ako) p s\<rbrace>"
  assumes z: "\<And>p T. \<lbrace>(K (is_vspace_typ (AArch T))) and typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  shows      "\<lbrace>valid_vspace_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (simp add: valid_vspace_objs_def)
  apply (rule hoare_vcg_all_lift, wp hoare_convert_imp [OF x]; (rule hoare_vcg_all_lift | assumption))
  apply (case_tac "\<exists>vcpu. ao = VCPU vcpu")
   apply wpsimp
  apply clarsimp
  apply (rule hoare_convert_imp)
   apply (rule y)
   apply (clarsimp simp: aa_type_def split: arch_kernel_obj.split)
  apply (rule valid_vspace_is_vspace_lift [OF z])
  done

lemma vspace_obj_imp: "non_arch_obj ko \<Longrightarrow> non_vspace_obj ko"
  apply (cases ko; clarsimp)
  apply (rename_tac ako)
  apply (case_tac ako, auto simp: non_arch_obj_def)
  done

lemma non_vspace_objs[intro]:
  "non_vspace_obj (Endpoint ep)"
  "non_vspace_obj (CNode sz cnode_contents)"
  "non_vspace_obj (TCB tcb)"
  "non_vspace_obj (Notification notification)"
  "non_vspace_obj (ArchObj (VCPU vcpu))"
  by (auto)

definition vspace_obj_pred :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> bool" where
  "vspace_obj_pred P \<equiv>
    \<forall>ko ko'. non_vspace_obj ko \<longrightarrow> non_vspace_obj ko' \<longrightarrow>
      P ko = P ko'"

lemma vspace_obj_predE:
  "\<lbrakk>vspace_obj_pred P; non_vspace_obj ko; non_vspace_obj ko'\<rbrakk> \<Longrightarrow> P ko = P ko'"
  apply (unfold vspace_obj_pred_def)
  apply (erule allE[where ?x="ko"])
  apply (erule allE[where ?x="ko'"])
  by blast

lemmas vspace_obj_pred_defs = non_vspace_objs vspace_obj_pred_def

lemma vspace_pred_imp: "vspace_obj_pred P \<Longrightarrow> arch_obj_pred P"
  apply (clarsimp simp: arch_obj_pred_def)
  apply (rule vspace_obj_predE)
    apply simp
   apply (rule vspace_obj_imp, assumption)+
  done

lemma vspace_obj_pred_a_type[intro, simp]: "T \<noteq> AVCPU \<Longrightarrow> vspace_obj_pred (\<lambda>ko. a_type ko = AArch T)"
  by (auto simp add: vspace_obj_pred_defs a_type_def
           split: kernel_object.splits arch_kernel_obj.splits)

lemma vspace_obj_pred_fun_lift: "vspace_obj_pred (\<lambda>ko. F (vspace_obj_fun_lift P N ko))"
  by (auto simp: vspace_obj_pred_defs vspace_obj_fun_lift_def
           split: kernel_object.splits arch_kernel_obj.splits)

lemmas vspace_obj_pred_fun_lift_id[simp]
  = vspace_obj_pred_fun_lift[where F=id, simplified]

lemmas vspace_obj_pred_fun_lift_k[intro]
  = vspace_obj_pred_fun_lift[where F="K R" for R, simplified]

lemmas vspace_obj_pred_fun_lift_el[simp]
  = vspace_obj_pred_fun_lift[where F="\<lambda> S. x \<in> S" for x, simplified]

lemma vspace_obj_pred_const_conjI[intro]:
  "vspace_obj_pred P \<Longrightarrow>
    vspace_obj_pred P' \<Longrightarrow>
    vspace_obj_pred (\<lambda>ko. P ko \<and> P' ko)"
  apply (simp only: vspace_obj_pred_def)
  apply blast
  done

lemma vspace_obj_pred_fI:
  "(\<And>x. vspace_obj_pred (P x)) \<Longrightarrow> vspace_obj_pred (\<lambda>ko. f (\<lambda>x :: 'a :: type. P x ko))"
  apply (simp only: vspace_obj_pred_def)
  apply (intro allI impI)
  apply (rule arg_cong[where f=f])
  by blast

declare
  vspace_obj_pred_fI[where f=All, intro]
  vspace_obj_pred_fI[where f=Ex, intro]

end

locale vspace_only_obj_pred = Arch +
  fixes P :: "kernel_object \<Rightarrow> bool"
  assumes vspace_only: "vspace_obj_pred P"

sublocale vspace_only_obj_pred < arch_only_obj_pred
  using vspace_pred_imp[OF vspace_only] by unfold_locales

context Arch begin arch_global_naming

sublocale empty_table: vspace_only_obj_pred "empty_table S" for S
  by unfold_locales (clarsimp simp: vspace_obj_pred_def empty_table_def
                             split: arch_kernel_obj.splits kernel_object.splits)

sublocale vs_refs: vspace_only_obj_pred "\<lambda>ko. x \<in> vs_refs ko"
  by unfold_locales (clarsimp simp: vspace_obj_pred_def vs_refs_def
                             split: arch_kernel_obj.splits kernel_object.splits)

sublocale vs_refs_pages: vspace_only_obj_pred "\<lambda>ko. x \<in> vs_refs_pages ko"
  by unfold_locales (clarsimp simp: vspace_obj_pred_def vs_refs_pages_def
                             split: arch_kernel_obj.split kernel_object.splits)

lemma pspace_in_kernel_window_atyp_lift_strong:
  assumes atyp_inv: "\<And>P p T. \<lbrace> \<lambda>s. P (typ_at T p s) \<rbrace> f \<lbrace> \<lambda>rv s. P (typ_at T p s) \<rbrace>"
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
  by (simp add: cap_refs_in_kernel_window_def)

lemma
  ex_ko_at_def2:
  "(\<exists>ko. ko_at ko p s \<and> P ko) = (obj_at P p s)"
  by (simp add: obj_at_def)

lemma in_user_frame_obj_pred_lift:
 assumes obj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow>
                             \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
 shows "\<lbrace>in_user_frame p\<rbrace> f \<lbrace>\<lambda>_. in_user_frame p\<rbrace>"
 unfolding in_user_frame_def
 apply (wp hoare_vcg_ex_lift obj_at)
 apply (clarsimp simp: vspace_obj_pred_def)
 apply (auto simp: a_type_def aa_type_def split: kernel_object.splits arch_kernel_obj.splits)
 done

lemma vs_lookup_vspace_obj_at_lift:
  assumes obj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow>
                             \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
  assumes arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> f \<lbrace>\<lambda>rv s. P (vs_lookup s)\<rbrace>"
  apply (simp add: vs_lookup_def vs_lookup1_def)
  apply (simp add: ex_ko_at_def2)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch_state])
  apply (rule hoare_lift_Pf[where f="\<lambda>s rs p rs' p'. obj_at (P' p rs rs' p') p s" for P'])
   apply (rule hoare_vcg_prop)
  apply (clarsimp simp add: valid_def)
  apply (erule_tac P=P in rsubst)
  apply (rule ext)+
  apply (erule use_valid, rule obj_at, simp)
  by (auto simp: vs_refs.vspace_only
           intro!: vspace_obj_pred_fI[where f=Ex])

lemma vs_lookup_pages_vspace_obj_at_lift:
  assumes obj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow>
                            \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
  assumes arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>rv s. P (vs_lookup_pages s)\<rbrace>"
  apply (simp add: vs_lookup_pages_def vs_lookup_pages1_def)
  apply (simp add: ex_ko_at_def2)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch_state])
  apply (rule hoare_lift_Pf[where f="\<lambda>s rs p rs' p'. obj_at (P' p rs rs' p') p s" for P'])
   apply (rule hoare_vcg_prop)
  apply (clarsimp simp add: valid_def)
  apply (erule_tac P=P in rsubst)
  apply (rule ext)+
  apply (erule use_valid, rule obj_at, simp)
  by (auto simp: vs_refs_pages.vspace_only
           intro!: vspace_obj_pred_fI[where f=Ex])

lemma valid_vspace_objs_lift_weak:
  assumes obj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow>
                             \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
  assumes arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>valid_vspace_objs\<rbrace> f \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (rule valid_vspace_objs_lift)
    apply (rule vs_lookup_vspace_obj_at_lift)
    apply (rule obj_at arch_state vspace_pred_imp; simp)+
   subgoal
     by (auto simp: aa_type_def vspace_obj_pred_def split: arch_kernel_obj.splits)
  apply (rule hoare_gen_asm_lk)
  apply (rule obj_at)
  subgoal
    by (auto simp: aa_type_def a_type_def vspace_obj_pred_def
              split: arch_kernel_obj.splits kernel_object.splits)
  done

lemma set_object_neg_lookup:
  "\<lbrace>\<lambda>s. \<not> (\<exists>rs. (rs \<rhd> p') s) \<and> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s \<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_ s. \<not> (\<exists>rs. (rs \<rhd> p') s)\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (erule_tac x=rs in allE)
  apply (erule notE)
  apply (erule vs_lookup_stateI)
   apply (clarsimp simp: obj_at_def split: if_split_asm)
  apply simp
  done

lemma set_object_vs_lookup:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko'. vs_refs ko = vs_refs ko') p s \<and> P (vs_lookup s) \<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (erule rsubst [where P=P])
  apply (rule order_antisym)
   apply (rule vs_lookup_sub)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: obj_at_def split: if_split_asm)
  apply simp
  done


lemma set_object_pt_not_vs_lookup_pages:
  "\<lbrace>\<lambda>s. \<not>(ref \<unrhd> p') s
    \<and> ((\<exists>\<unrhd>p) s \<longrightarrow> (\<forall>x. case pte_ref_pages (pt x) of
              Some ptr \<Rightarrow>
                obj_at (\<lambda>ko. vs_refs_pages ko = {}) ptr s \<and>
                ptr \<noteq> p'
            | None \<Rightarrow> True))\<rbrace>
   set_object p (ArchObj (PageTable pt))
   \<lbrace>\<lambda>_ s. \<not>(ref \<unrhd> p') s\<rbrace>"
  apply (wpsimp wp: set_object_wp)
   apply (case_tac "(\<exists>\<unrhd>p) s")
   apply (erule notE)
   apply clarsimp
   apply (subst (asm) vs_lookup_pages_def)
   apply clarsimp
   apply (erule vs_lookup_pagesI)
   apply (erule converse_rtrancl_induct)
    apply simp
   apply (drule vs_lookup_pages1D)
   apply (clarsimp simp: obj_at_def split:if_split_asm)
   apply (case_tac "pa=p")
    apply (clarsimp simp: vs_refs_pages_def graph_of_def)
    apply (rename_tac slot pte)
    apply (erule_tac x=slot in allE)
    apply (drule_tac R="vs_lookup_pages1 s" in rtranclD)
    apply clarsimp
    apply (drule tranclD)
    apply clarsimp
    apply (drule vs_lookup_pages1D)
    apply (clarsimp simp: obj_at_def vs_refs_pages_def)
   apply clarsimp
   apply (erule rtrancl_trans[OF r_into_rtrancl, rotated])
   apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
  apply clarsimp
  apply (erule notE)
  apply (subst (asm) vs_lookup_pages_def)
  apply clarsimp
  apply (rule vs_lookup_pagesI, assumption)
  apply (erule rtrancl_induct)
   apply simp
  apply (drule vs_lookup_pages1D)
  apply (clarsimp simp: obj_at_def split:if_split_asm)
  apply (case_tac "pa=p")
   apply (clarsimp simp: vs_refs_pages_def graph_of_def)
   apply (rename_tac vs slot pte)
   apply (erule_tac x=vs in allE)
   apply (clarsimp simp: vs_lookup_pages_def)
   apply (drule(1) ImageI, erule (1) notE)
  apply clarsimp
  apply (erule rtrancl_trans[OF _ r_into_rtrancl])
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
  done


lemma set_object_vs_lookup_pages:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko'. vs_refs_pages ko = vs_refs_pages ko') p s \<and> P (vs_lookup_pages s) \<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (erule rsubst [where P=P])
  apply (rule order_antisym)
   apply (rule vs_lookup_pages_sub)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply (rule vs_lookup_pages_sub)
   apply (clarsimp simp: obj_at_def split: if_split_asm)
  apply simp
  done


lemma set_object_atyp_at:
  "\<lbrace>\<lambda>s. typ_at (AArch (aa_type ako)) p s \<and> P (typ_at (AArch T) p' s)\<rbrace>
    set_object p (ArchObj ako)
   \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p' s)\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (erule rsubst [where P=P])
  apply (clarsimp simp: obj_at_def a_type_aa_type)
  done

lemma hoare_post_imp_conj_disj: "(\<lbrace> \<lambda>s. R \<rbrace> f \<lbrace> \<lambda>_ s. P \<longrightarrow> Q \<rbrace>) = (\<lbrace> \<lambda>s. R \<rbrace> f \<lbrace> \<lambda>_ s. \<not> P \<or> Q \<rbrace>)"
 by (subst imp_conv_disj, auto)

lemma set_object_vspace_objs:  (* used in set_pd_arch_objs_unmap in ArchAcc_AI *) (* ARMHYP *)
  "\<lbrace>valid_vspace_objs and typ_at (a_type ko) p and
    obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p  and
    (\<lambda>s. case ko of ArchObj ao \<Rightarrow> (\<exists>\<rhd>p)s \<longrightarrow> valid_vspace_obj ao s
            | _ \<Rightarrow> True)\<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (simp add: valid_vspace_objs_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply (subst imp_conv_disj)
  apply (subst imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift set_object_neg_lookup set_object_neg_ko)
  apply (wp valid_vspace_obj_typ2 [where Q="typ_at (a_type ko) p"] set_object_typ_at
         | simp)+
  apply (clarsimp simp: pred_neg_def obj_at_def)
  apply (case_tac ko; auto)
  done

lemma set_object_valid_kernel_mappings:
  "\<lbrace>\<lambda>s. valid_kernel_mappings s\<rbrace>
     set_object ptr ko
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_kernel_mappings_def
                 elim!: ranE split: if_split_asm)
  done

lemma valid_vs_lookup_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>valid_vs_lookup\<rbrace> f \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply (rule hoare_lift_Pf [where f=vs_lookup_pages])
   apply (rule hoare_lift_Pf [where f="\<lambda>s. (caps_of_state s)"])
    apply (wp lookup cap)+
  done


lemma valid_table_caps_lift:
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes obj: "\<And>S p. \<lbrace>obj_at (empty_table S) p\<rbrace> f \<lbrace>\<lambda>rv. obj_at (empty_table S) p\<rbrace>"
  shows "\<lbrace>valid_table_caps\<rbrace> f \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def
   apply (rule hoare_lift_Pf [where f="\<lambda>s. (caps_of_state s)"])
    apply (wp cap hoare_vcg_all_lift hoare_vcg_const_imp_lift obj)+
  done

lemma valid_arch_caps_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes obj: "\<And>S p. \<lbrace>obj_at (empty_table S) p\<rbrace> f \<lbrace>\<lambda>rv. obj_at (empty_table S) p\<rbrace>"
  shows "\<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding valid_arch_caps_def
  apply (rule hoare_pre)
   apply (wp valid_vs_lookup_lift valid_table_caps_lift lookup cap obj)
  apply simp
  done

lemma valid_global_objs_lift':
  assumes obj: "\<And>p. \<lbrace>valid_ao_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_ao_at p\<rbrace>"
  assumes ko: "\<And>ako p. \<lbrace>ko_at (ArchObj ako) p\<rbrace> f \<lbrace>\<lambda>_. ko_at (ArchObj ako) p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_global_objs s \<and> (v \<longrightarrow> P s)\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  by (clarsimp simp: valid_global_objs_def valid_def)

lemmas valid_global_objs_lift
    = valid_global_objs_lift' [where v=False, simplified]

context
  fixes f :: "'a::state_ext state \<Rightarrow> ('b \<times> 'a state) set \<times> bool"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
begin

context
  assumes aobj_at:
    "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow> \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
  notes vspace_obj_fun_lift_expand[simp del]
begin

lemma valid_global_vspace_mappings_lift:
  "\<lbrace>valid_global_vspace_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  by (wpsimp simp: valid_global_vspace_mappings_def)

lemma valid_arch_caps_lift_weak:
  "(\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>) \<Longrightarrow>
      \<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  apply (rule valid_arch_caps_lift[OF _ _ aobj_at])
    apply (rule vs_lookup_pages_vspace_obj_at_lift[OF aobj_at arch], assumption+)
  apply (rule empty_table.vspace_only)
  done

lemma valid_global_objs_lift_weak:
  "\<lbrace>valid_global_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  by (wpsimp simp: valid_global_objs_def)

lemma valid_asid_map_lift:
  "\<lbrace>valid_asid_map\<rbrace> f \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: valid_asid_map_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (simp add: vspace_at_asid_def)
  by (rule vs_lookup_vspace_obj_at_lift[OF aobj_at arch])

lemma valid_kernel_mappings_lift:
  "\<lbrace>valid_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: valid_kernel_mappings_def, wp)
  done

end

(* intended for use inside Arch, as opposed to the interface lemma valid_arch_state_lift_aobj_at,
   since this architecture does not need cap preservation for valid_arch_state *)
lemma valid_arch_state_lift_aobj_at_no_caps:
  assumes aobj_at:
    "\<And>P P' pd. arch_obj_pred P' \<Longrightarrow> \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
  shows "\<lbrace>valid_arch_state\<rbrace> f \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  apply (simp add: valid_arch_state_def valid_asid_table_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (rule hoare_vcg_conj_lift hoare_vcg_ball_lift hoare_vcg_prop | (rule aobj_at, clarsimp))+
   apply (case_tac "arm_current_vcpu x"; simp add: split_def)
   apply wp
   apply (rule aobj_at)
   apply (clarsimp simp: arch_obj_pred_def non_arch_obj_def is_vcpu_def)
  apply wp
  done

(* interface lemma *)
lemma valid_arch_state_lift_aobj_at:
  assumes aobj_at:
    "\<And>P P' pd. arch_obj_pred P' \<Longrightarrow> \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
  assumes caps: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "f \<lbrace>valid_arch_state\<rbrace>"
  by (intro valid_arch_state_lift_aobj_at_no_caps aobj_at)

end

lemma equal_kernel_mappings_lift:
  assumes vsobj_at:
    "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow> \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
  shows "\<lbrace>equal_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: equal_kernel_mappings_def, wp)
  done

lemma valid_machine_state_lift:
  assumes memory: "\<And>P. \<lbrace>\<lambda>s. P (underlying_memory (machine_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (underlying_memory (machine_state s))\<rbrace>"
  assumes aobj_at: "\<And>P' pd. arch_obj_pred P' \<Longrightarrow> \<lbrace>obj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. obj_at P' pd s\<rbrace>"
  shows "\<lbrace>valid_machine_state\<rbrace> f \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def
  apply (rule hoare_lift_Pf[where f="\<lambda>s. underlying_memory (machine_state s)", OF _ memory])
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift[OF _ hoare_vcg_prop]
                 in_user_frame_lift aobj_at)+

lemma valid_vso_at_lift:
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p s)\<rbrace>"
      and y: "\<And>ao. \<lbrace>\<lambda>s. ko_at (ArchObj ao) p s\<rbrace> f \<lbrace>\<lambda>rv s. ko_at (ArchObj ao) p s\<rbrace>"
  shows      "\<lbrace>valid_vso_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_vso_at p\<rbrace>"
  unfolding valid_vso_at_def
  by (wpsimp wp: hoare_vcg_ex_lift y valid_vspace_is_vspace_lift z)+

lemma valid_vso_at_lift_aobj_at:
  assumes aobj_at: "\<And>P' pd. vspace_obj_pred P' \<Longrightarrow> \<lbrace>obj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. obj_at P' pd s\<rbrace>"
  shows      "\<lbrace>valid_vso_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_vso_at p\<rbrace>"
  unfolding valid_vso_at_def
  apply (rule hoare_vcg_ex_lift)
  apply (case_tac "\<exists>vcpu. ao = VCPU vcpu")
   apply (clarsimp simp: aa_type_def)
  apply clarsimp
  apply (rule hoare_vcg_conj_lift aobj_at)+
   apply (case_tac ao; fastforce simp: vspace_obj_pred_def)
  apply (wpsimp wp: valid_vspace_is_vspace_lift)
    apply (case_tac "T = AVCPU", simp)
    apply (wpsimp wp: aobj_at)
   apply wp
  apply assumption
  done

lemmas set_object_v_ker_map
    = set_object_valid_kernel_mappings

lemma set_object_asid_map:
  "\<lbrace>valid_asid_map and
    obj_at (\<lambda>ko'. vs_refs ko' \<subseteq> vs_refs ko) p\<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (wpsimp wp: set_object_wp simp: valid_asid_map_def)
  apply (clarsimp simp: vspace_at_asid_def simp del: fun_upd_apply)
  apply (drule bspec, blast)
  apply clarsimp
  apply (rule vs_lookup_stateI, assumption)
   apply (clarsimp simp: obj_at_def)
   apply blast
  apply simp
  done

lemma set_object_equal_mappings:
  "\<lbrace>\<lambda>s. equal_kernel_mappings s
          \<and> (\<forall>pd. ko = ArchObj (PageDirectory pd)
                \<longrightarrow> (\<forall>x pd'. ko_at (ArchObj (PageDirectory pd')) x s))\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def
             split del: if_split)
  done

lemma valid_table_caps_ptD:
  "\<lbrakk> (caps_of_state s) p = Some (ArchObjectCap (arch_cap.PageTableCap p' None));
     page_table_at p' s; valid_table_caps s \<rbrakk> \<Longrightarrow>
    \<exists>pt. ko_at (ArchObj (PageTable pt)) p' s \<and> valid_vspace_obj (PageTable pt) s"
  apply (clarsimp simp: valid_table_caps_def simp del: split_paired_All)
  apply (erule allE)+
  apply (erule (1) impE)
  apply (clarsimp simp add: is_pt_cap_def cap_asid_def)
  apply (erule impE, rule refl)
  apply (clarsimp simp: obj_at_def empty_table_def)
  done

lemma store_pde_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> store_pde ptr val \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: store_pde_def get_pd_def set_pd_def bind_assoc)
  apply (wpsimp wp: set_object_wp_strong get_object_wp
              simp: a_type_def obj_at_def pred_tcb_at_def
             split: kernel_object.split)
  done

lemma empty_table_lift:
  assumes S: "\<And>P. \<lbrace>\<lambda>s. P (S s)\<rbrace> f \<lbrace>\<lambda>_ s. P (S s)\<rbrace>"
  assumes o: "\<And>P. \<lbrace>obj_at P p and Q\<rbrace> f \<lbrace>\<lambda>_. obj_at P p\<rbrace>"
  shows "\<lbrace>\<lambda>s. obj_at (empty_table (S s)) p s \<and> Q s\<rbrace>
         f \<lbrace>\<lambda>_ s. obj_at (empty_table (S s)) p s\<rbrace>"
  apply (rule hoare_lift_Pf2 [where f="S"])
   apply (wp o S|simp)+
  done

(*
lemma as_user_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> as_user t m \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: as_user_def split_def set_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: a_type_def)
  done

lemma shows
  sts_caps_of_state[wp]:
    "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_thread_state t st \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>" and
  set_bound_caps_of_state[wp]:
    "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_bound_notification t e \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>" and
  as_user_caps_of_state[wp]:
    "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> as_user p f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"

  unfolding set_thread_state_def set_bound_notification_def as_user_def set_object_def
            set_mrs_def
  apply (all \<open>(wp | wpc | simp)+ ; clarsimp, erule rsubst[where P=P], rule cte_wp_caps_of_lift\<close>)
  by (auto simp: cte_wp_at_cases2 tcb_cnode_map_def dest!: get_tcb_SomeD)
*)

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
  apply (intro conjI impI)
    apply (fastforce simp: a_type_def)+
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
    | _ \<Rightarrow>(case default_object tp dev 0 0 of (ArchObj (DataPage dev _)) \<Rightarrow> dev
          | _ \<Rightarrow> False)"

lemma cap_is_device_obj_is_device[simp]:
  "cap_is_device (default_cap tp a sz dev) = obj_is_device tp dev"
  by (simp add: default_cap_def arch_default_cap_def obj_is_device_def
                default_object_def  default_arch_object_def
         split: apiobject_type.splits aobject_type.splits)

crunch storeWord
  for device_state_inv: "\<lambda>ms. P (device_state ms)"
  (ignore_del: storeWord)


(* some hyp_ref invariants *)

lemma state_hyp_refs_of_ep_update: "\<And>s ep val. typ_at AEndpoint ep s \<Longrightarrow>
       state_hyp_refs_of (s\<lparr>kheap := (kheap s)(ep \<mapsto> Endpoint val)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: ARM_HYP.state_hyp_refs_of_def obj_at_def ARM_HYP.hyp_refs_of_def)
  done

lemma state_hyp_refs_of_ntfn_update: "\<And>s ep val. typ_at ANTFN ep s \<Longrightarrow>
       state_hyp_refs_of (s\<lparr>kheap := (kheap s)(ep \<mapsto> Notification val)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: ARM_HYP.state_hyp_refs_of_def obj_at_def ARM_HYP.hyp_refs_of_def)
  done

lemma state_hyp_refs_of_tcb_bound_ntfn_update:
       "kheap s t = Some (TCB tcb) \<Longrightarrow>
          state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_bound_notification := ntfn\<rparr>))\<rparr>)
            = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: ARM_HYP.state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_state_update:
       "kheap s t = Some (TCB tcb) \<Longrightarrow>
          state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_state := ts\<rparr>))\<rparr>)
            = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: ARM_HYP.state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_domain_update:
  "kheap s t = Some (TCB tcb) \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_domain := d\<rparr>))\<rparr>)
     = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_priority_update:
  "kheap s t = Some (TCB tcb) \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_priority := p\<rparr>))\<rparr>)
     = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_time_slice_update:
  "kheap s t = Some (TCB tcb) \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_time_slice := ts\<rparr>))\<rparr>)
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

lemma valid_vcpu_same_type:
  "\<lbrakk> valid_vcpu v s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> valid_vcpu v (s\<lparr>kheap := (kheap s)(p \<mapsto> k)\<rparr>)"
  by (cases v; case_tac vcpu_tcb; clarsimp simp: valid_vcpu_def typ_at_same_type)

lemma arch_valid_obj_same_type:
  "\<lbrakk> arch_valid_obj ao s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> arch_valid_obj ao (s\<lparr>kheap := (kheap s)(p \<mapsto> k)\<rparr>)"
  by (induction ao rule: arch_kernel_obj.induct;
         clarsimp simp: typ_at_same_type valid_vcpu_same_type)


lemma default_arch_object_not_live[simp]: "\<not> live (ArchObj (default_arch_object aty dev us))"
  by (clarsimp simp: default_arch_object_def live_def hyp_live_def arch_live_def default_vcpu_def
               split: aobject_type.splits)

lemma default_tcb_not_live[simp]: "\<not> live (TCB (default_tcb d))"
  by (clarsimp simp: default_tcb_def default_arch_tcb_def live_def hyp_live_def)

lemma valid_arch_tcb_same_type:
  "\<lbrakk> valid_arch_tcb t s; valid_obj p k s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> valid_arch_tcb t (s\<lparr>kheap := (kheap s)(p \<mapsto> k)\<rparr>)"
  by (auto simp: valid_arch_tcb_def obj_at_def)

lemma valid_arch_mdb_lift:
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (caps_of_state s)\<rbrace>"
  assumes r: "\<And>P. \<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> f \<lbrace>\<lambda>r s. P (is_original_cap s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>r s. valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrace>"
  by (clarsimp simp: valid_def valid_arch_mdb_def)

end
end
