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

context Arch begin global_naming ARM


sublocale
  empty_table: vspace_only_obj_pred "empty_table S" for S
  by (unfold_locales, simp add: empty_table_def del: arch_obj_fun_lift_expand)

sublocale
  vs_refs: vspace_only_obj_pred "\<lambda>ko. x \<in> vs_refs ko"
  by (unfold_locales, simp add: vs_refs_def del: vs_refs_arch_def)

sublocale
  vs_refs': arch_only_obj_pred "\<lambda>ko. x \<in> vs_refs ko"
  by (unfold_locales, simp add: vs_refs_def del: vs_refs_arch_def)

sublocale
  vs_refs_pages: vspace_only_obj_pred "\<lambda>ko. x \<in> vs_refs_pages ko"
  by (unfold_locales, simp add: vs_refs_pages_def del: vs_refs_pages_arch_def)

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

lemma vs_lookup_arch_obj_at_lift:
  assumes obj_at: "\<And>P P' p. arch_obj_pred P' \<Longrightarrow>
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
  by (auto simp: vs_refs'.arch_only
           intro!: arch_obj_pred_fI[where f=Ex])
(*
lemma vs_lookup_pages_arch_obj_at_lift:
  assumes obj_at: "\<And>P P' p. arch_obj_pred P' \<Longrightarrow>
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
  by (auto simp: vs_refs_pages.arch_only
           intro!: arch_obj_pred_fI[where f=Ex])
*)
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

(* ARMHYP not needed?
lemma valid_arch_objs_lift_weak:
  assumes obj_at: "\<And>P P' p. arch_obj_pred P' \<Longrightarrow>
                             \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
  assumes arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>valid_arch_objs\<rbrace> f \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>" (* ARMHYP *)
  apply (rule valid_arch_objs_lift)
   apply (rule valid_vspace_objs_lift)
     apply (rule vs_lookup_arch_obj_at_lift)
      apply (rule obj_at arch_state; simp)+
  apply (simp add: obj_at_def)
 done *)

lemma valid_vspace_objs_lift_weak:
  assumes obj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow>
                             \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>"
  assumes arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>valid_vspace_objs\<rbrace> f \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (rule valid_vspace_objs_lift)
    apply (rule vs_lookup_vspace_obj_at_lift)
     apply (rule obj_at arch_state; simp)+
  done

lemma set_object_neg_lookup:
  "\<lbrace>\<lambda>s. \<not> (\<exists>rs. (rs \<rhd> p') s) \<and> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s \<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_ s. \<not> (\<exists>rs. (rs \<rhd> p') s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule_tac x=rs in allE)
  apply (erule notE)
  apply (erule vs_lookup_stateI)
   apply (clarsimp simp: obj_at_def split: split_if_asm)
  apply simp
  done


lemma set_object_vs_lookup:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko'. vs_refs ko = vs_refs ko') p s \<and> P (vs_lookup s) \<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (rule order_antisym)
   apply (rule vs_lookup_sub)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: obj_at_def split: split_if_asm)
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
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def)
   apply (case_tac "(\<exists>\<unrhd>p) s")
   apply (erule notE)
   apply clarsimp
   apply (subst (asm) vs_lookup_pages_def)
   apply clarsimp
   apply (erule vs_lookup_pagesI)
   apply (erule converse_rtrancl_induct)
    apply simp
   apply (drule vs_lookup_pages1D)
   apply (clarsimp simp: obj_at_def split:split_if_asm)
   apply (case_tac "pa=p")
    apply (clarsimp simp: vs_refs_pages_def graph_of_def)
    apply (erule_tac x=ab in allE)
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
  apply (clarsimp simp: obj_at_def split:split_if_asm)
  apply (case_tac "pa=p")
   apply (clarsimp simp: vs_refs_pages_def graph_of_def)
   apply (erule_tac x=rs in allE)
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
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (rule order_antisym)
   apply (rule vs_lookup_pages_sub)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply (rule vs_lookup_pages_sub)
   apply (clarsimp simp: obj_at_def split: split_if_asm)
  apply simp
  done


lemma set_object_atyp_at:
  "\<lbrace>\<lambda>s. typ_at (AArch (aa_type ako)) p s \<and> P (typ_at (AArch T) p' s)\<rbrace>
    set_object p (ArchObj ako)
   \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p' s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (clarsimp simp: obj_at_def a_type_aa_type)
  done

lemma hoare_post_imp_conj_disj: "(\<lbrace> \<lambda>s. R \<rbrace> f \<lbrace> \<lambda>_ s. P \<longrightarrow> Q \<rbrace>) = (\<lbrace> \<lambda>s. R \<rbrace> f \<lbrace> \<lambda>_ s. \<not> P \<or> Q \<rbrace>)"
 by (subst imp_conv_disj, auto)

(*
lemma set_object_arch_objs:  (* used in set_pd_arch_objs_unmap in ArchAcc_AI *) (* ARMHYP *)
  "\<lbrace>valid_arch_objs and typ_at (a_type ko) p and
    obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p  and
    (\<lambda>s. case ko of ArchObj ao \<Rightarrow> (\<exists>\<rhd>p)s \<longrightarrow> valid_arch_obj ao s
            | _ \<Rightarrow> True)\<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: valid_arch_objs_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply (subst imp_conv_disj)
  apply (subst imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift set_object_neg_lookup set_object_neg_ko)
  apply (wp valid_arch_obj_typ2 [where Q="typ_at (a_type ko) p"] set_object_typ_at
         | simp)+
  apply (clarsimp simp: pred_neg_def obj_at_def)
  apply (case_tac ko; auto)
  done *)

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
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp: valid_kernel_mappings_def
                 elim!: ranE split: split_if_asm)
  done

lemma valid_vs_lookup_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>valid_vs_lookup\<rbrace> f \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply (rule hoare_lift_Pf [where f=vs_lookup_pages])
   apply (rule hoare_lift_Pf [where f="\<lambda>s. (caps_of_state s)"])
    apply (wp lookup cap)
  done


lemma valid_table_caps_lift:
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes obj: "\<And>S p. \<lbrace>obj_at (empty_table S) p\<rbrace> f \<lbrace>\<lambda>rv. obj_at (empty_table S) p\<rbrace>"
  shows "\<lbrace>valid_table_caps\<rbrace> f \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def
   apply (rule hoare_lift_Pf [where f="\<lambda>s. (caps_of_state s)"])
    apply (wp cap hoare_vcg_all_lift hoare_vcg_const_imp_lift obj)
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

lemma arch_lifts:
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  assumes aobj_at: "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow>
    \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
  notes arch_obj_fun_lift_expand[simp del]
  shows
  valid_arch_caps_lift_weak:
    "(\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>) \<Longrightarrow>
      \<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>" and
  valid_asid_map_lift:
    "\<lbrace>valid_asid_map\<rbrace> f \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>" and
  valid_kernel_mappings_lift:
    "\<lbrace>valid_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>" and
  valid_arch_state_lift_aobj_at:
    "\<lbrace>valid_arch_state\<rbrace> f \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  apply -

  subgoal
  apply (rule valid_arch_caps_lift[OF _ _ aobj_at])
    apply (rule vs_lookup_pages_vspace_obj_at_lift[OF aobj_at arch], assumption+)
  apply (rule empty_table.vspace_only)
  done

  subgoal
  apply (simp add: valid_asid_map_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (simp add: vspace_at_asid_def)
  by (rule vs_lookup_vspace_obj_at_lift[OF aobj_at arch])

  subgoal
  apply (simp add: valid_kernel_mappings_def, wp)
  done

  subgoal
  apply (simp add: valid_arch_state_def valid_asid_table_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (wp hoare_vcg_conj_lift hoare_vcg_ball_lift | (rule aobj_at, clarsimp))+
   apply (case_tac "arm_current_vcpu x"; simp add: split_def)
   apply (wp, rule aobj_at, simp)
  apply wp
  done

  done

lemma equal_kernel_mappings_lift:
  assumes vsobj_at: "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow>
                               \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
  shows "\<lbrace>equal_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: equal_kernel_mappings_def, wp)
  done

lemma valid_machine_state_lift:
  assumes memory: "\<And>P. \<lbrace>\<lambda>s. P (underlying_memory (machine_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (underlying_memory (machine_state s))\<rbrace>"
  assumes aobj_at: "\<And>P' pd. vspace_obj_pred P' \<Longrightarrow> \<lbrace>obj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. obj_at P' pd s\<rbrace>"
  shows "\<lbrace>valid_machine_state\<rbrace> f \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def
  apply (rule hoare_lift_Pf[where f="\<lambda>s. underlying_memory (machine_state s)", OF _ memory])
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_vcg_disj_lift[OF _ hoare_vcg_prop])
  apply (rule in_user_frame_lift)
  apply (wp aobj_at)
  apply simp
  done

(*
lemma bool_pred_exhaust:
  "(P = (\<lambda>x. x)) \<or> (P = (\<lambda>x. \<not>x)) \<or> (P = (\<lambda>_. True)) \<or> (P = (\<lambda>_. False))"
  apply (cases "P True"; cases "P False")
  apply (rule disjI2, rule disjI2, rule disjI1, rule ext)
  defer
  apply (rule disjI1, rule ext)
  defer
  apply (rule disjI2, rule disjI1, rule ext)
  defer
  apply (rule disjI2, rule disjI2, rule disjI2, rule ext)
  apply (match conclusion in "P x = _" for x \<Rightarrow> \<open>cases x; fastforce\<close>)+
  done
*)
(*
lemma valid_ao_at_lift:
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p s)\<rbrace>"
      and y: "\<And>ao. \<lbrace>\<lambda>s. ko_at (ArchObj ao) p s\<rbrace> f \<lbrace>\<lambda>rv s. ko_at (ArchObj ao) p s\<rbrace>"
  shows      "\<lbrace>valid_ao_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_ao_at p\<rbrace>"
  unfolding valid_ao_at_def
  by (wp hoare_vcg_ex_lift y valid_arch_obj_typ z)

lemma valid_ao_at_lift_aobj_at:
  assumes aobj_at: "\<And>P' pd. arch_obj_pred P' \<Longrightarrow> \<lbrace>obj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. obj_at P' pd s\<rbrace>"
  shows      "\<lbrace>valid_ao_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_ao_at p\<rbrace>"
  unfolding valid_ao_at_def
  by (wp hoare_vcg_ex_lift valid_arch_obj_typ aobj_at | clarsimp)+ *)

lemma valid_vso_at_lift:
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p s)\<rbrace>"
      and y: "\<And>ao. \<lbrace>\<lambda>s. ko_at (ArchObj ao) p s\<rbrace> f \<lbrace>\<lambda>rv s. ko_at (ArchObj ao) p s\<rbrace>"
  shows      "\<lbrace>valid_vso_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_vso_at p\<rbrace>"
  unfolding valid_vso_at_def
  by (wp hoare_vcg_ex_lift y valid_vspace_obj_typ z)

lemma valid_vso_at_lift_aobj_at:
  assumes aobj_at: "\<And>P' pd. vspace_obj_pred P' \<Longrightarrow> \<lbrace>obj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. obj_at P' pd s\<rbrace>"
  shows      "\<lbrace>valid_vso_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_vso_at p\<rbrace>"
  unfolding valid_vso_at_def
  by (wp hoare_vcg_ex_lift valid_vspace_obj_typ aobj_at | clarsimp)+

lemmas set_object_v_ker_map
    = set_object_valid_kernel_mappings

crunch v_ker_map[wp]: set_notification "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_object_asid_map:
  "\<lbrace>valid_asid_map and
    obj_at (\<lambda>ko'. vs_refs ko' \<subseteq> vs_refs ko) p\<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: valid_asid_map_def set_object_def)
  apply wp
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
  apply (simp add: set_object_def, wp)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def
             split del: split_if)
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
  apply (simp add: store_pde_def set_pd_def set_object_def
                   get_pd_def bind_assoc)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply (case_tac x, simp_all)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, simp_all)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply wp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
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
  apply (clarsimp simp: in_user_frame_def obj_at_def split: split_if_asm)
   apply (elim disjE)
    apply clarsimp
    apply (intro exI)
    apply (rule conjI,assumption)
    apply (simp add: a_type_def)
   apply (fastforce simp: a_type_def)
  apply (clarsimp simp: in_user_frame_def obj_at_def split: split_if_asm)
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
  apply (clarsimp simp: in_device_frame_def obj_at_def split: split_if_asm)
   apply (elim disjE)
    apply clarsimp
    apply (intro exI)
    apply (rule conjI,assumption)
    apply (simp add: a_type_def)
   apply (fastforce simp: a_type_def)
  apply (clarsimp simp: in_device_frame_def obj_at_def split: split_if_asm)
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
    | _ \<Rightarrow>(case (default_object tp dev 0) of (ArchObj (DataPage dev _)) \<Rightarrow> dev
          | _ \<Rightarrow> False)"

lemma cap_is_device_obj_is_device[simp]:
  "cap_is_device (default_cap tp a sz dev) = obj_is_device tp dev"
  by (simp add: default_cap_def arch_default_cap_def obj_is_device_def
                default_object_def  default_arch_object_def
         split: apiobject_type.splits aobject_type.splits)

crunch device_state_inv: storeWord "\<lambda>ms. P (device_state ms)"

end
end
