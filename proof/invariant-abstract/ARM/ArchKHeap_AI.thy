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

lemma set_object_neg_lookup:
  "\<lbrace>\<lambda>s. \<not> (\<exists>rs. (rs \<rhd> p') s) \<and> aobj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s \<rbrace> 
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_ s. \<not> (\<exists>rs. (rs \<rhd> p') s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule_tac x=rs in allE)
  apply (erule notE)
  apply (erule vs_lookup_stateI)
   apply (clarsimp simp: aobj_at_def split: split_if_asm)
  apply simp
  done


lemma set_object_vs_lookup:
  "\<lbrace>\<lambda>s. aobj_at (\<lambda>ko'. vs_refs ko = vs_refs ko') p s \<and> P (vs_lookup s) \<rbrace> 
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (rule order_antisym)
   apply (rule vs_lookup_sub)
    apply (clarsimp simp: aobj_at_def)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: aobj_at_def split: split_if_asm)
  apply simp
  done


lemma set_object_pt_not_vs_lookup_pages:
  "\<lbrace>\<lambda>s. \<not>(ref \<unrhd> p') s
    \<and> ((\<exists>\<unrhd>p) s \<longrightarrow> (\<forall>x. case pte_ref_pages (pt x) of
              Some ptr \<Rightarrow> 
                aobj_at (\<lambda>ko. vs_refs_pages ko = {}) ptr s \<and>
                ptr \<noteq> p'
            | None \<Rightarrow> True))\<rbrace>
   set_object p (ArchObj (PageTable pt))
   \<lbrace>\<lambda>_ s. \<not>(ref \<unrhd> p') s\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp: aobj_at_def)
   apply (case_tac "(\<exists>\<unrhd>p) s")
   apply (erule notE)
   apply clarsimp
   apply (subst (asm) vs_lookup_pages_def)
   apply clarsimp
   apply (erule vs_lookup_pagesI)
   apply (erule converse_rtrancl_induct)
    apply simp
   apply (drule vs_lookup_pages1D)
   apply (clarsimp simp: aobj_at_def split:split_if_asm)
   apply (case_tac "pa=p")
    apply (clarsimp simp: vs_refs_pages_def graph_of_def)
    apply (erule_tac x=ab in allE)
    apply (drule_tac R="vs_lookup_pages1 s" in rtranclD)
    apply clarsimp
    apply (drule tranclD)
    apply clarsimp
    apply (drule vs_lookup_pages1D)
    apply (clarsimp simp: aobj_at_def vs_refs_pages_def)
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
  apply (clarsimp simp: aobj_at_def split:split_if_asm)
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
  "\<lbrace>\<lambda>s. aobj_at (\<lambda>ko'. vs_refs_pages ko = vs_refs_pages ko') p s \<and> P (vs_lookup_pages s) \<rbrace> 
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (rule order_antisym)
   apply (rule vs_lookup_pages_sub)
    apply (clarsimp simp: aobj_at_def)
   apply simp
  apply (rule vs_lookup_pages_sub)
   apply (clarsimp simp: aobj_at_def split: split_if_asm)
  apply simp
  done

lemma set_object_neg_ako:
  "\<lbrace>not ako_at ko' p' and K (p = p' \<longrightarrow> ko \<noteq> ko')\<rbrace> 
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_ s. \<not> ako_at ko' p' s\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (simp add: pred_neg_def aobj_at_def)
  done

lemma set_object_neg_ko:
  "\<lbrace>not ko_at ko' p' and K (p = p' \<longrightarrow> ko \<noteq> ko')\<rbrace> 
  set_object p ko 
  \<lbrace>\<lambda>_ s. \<not> ko_at ko' p' s\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (simp add: pred_neg_def obj_at_def)
  done


lemma set_object_typ_at:
  "\<lbrace>\<lambda>s. typ_at (a_type ko) p s \<and> P (typ_at T p' s)\<rbrace> 
  set_object p ko \<lbrace>\<lambda>rv s. P (typ_at T p' s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (clarsimp simp: obj_at_def)
  done

lemma set_object_atyp_at:
  "\<lbrace>\<lambda>s. atyp_at (aa_type ko) p s \<and> P (atyp_at T p' s)\<rbrace> 
  set_object p (ArchObj ko) \<lbrace>\<lambda>rv s. P (atyp_at T p' s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (clarsimp simp: aobj_at_def)
  done


lemma set_object_arch_objs:
  "\<lbrace>valid_arch_objs and atyp_at (aa_type ko) p and 
    aobj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p  and
    (\<lambda>s. (\<exists>\<rhd>p)s \<longrightarrow> valid_arch_obj ko s)\<rbrace>
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: valid_arch_objs_def)
  apply (subst imp_conv_disj)+
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift set_object_neg_lookup set_object_neg_ako 
            valid_arch_obj_typ2 [where Q="atyp_at (aa_type ko) p"] set_object_atyp_at)
  apply (clarsimp simp: pred_neg_def aobj_at_def)
  apply fastforce
  done


lemma set_object_valid_kernel_mappings:
  "\<lbrace>\<lambda>s. valid_kernel_mappings s
           \<and> valid_kernel_mappings_if_pd
                (set (arm_global_pts (arch_state s)))
                    ko\<rbrace>
     set_object ptr ko
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp: valid_kernel_mappings_def
                 elim!: ranE split: split_if_asm)
  apply fastforce
  done

lemma valid_vs_lookup_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>"
  assumes pts: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pts (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pts (arch_state s))\<rbrace>"
  shows "\<lbrace>valid_vs_lookup\<rbrace> f \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply (rule hoare_lift_Pf [where f=vs_lookup_pages])
   apply (rule hoare_lift_Pf [where f=arch_caps_of_state])
    apply (rule hoare_lift_Pf [where f="\<lambda>s. arm_global_pts (arch_state s)"])
     apply (wp lookup cap pts)
  done

lemma valid_table_caps_lift:
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>"
  assumes pts: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pts (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pts (arch_state s))\<rbrace>"
  assumes obj: "\<And>S p. \<lbrace>aobj_at (empty_table S) p\<rbrace> f \<lbrace>\<lambda>rv. aobj_at (empty_table S) p\<rbrace>"
  shows "\<lbrace>valid_table_caps\<rbrace> f \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def
   apply (rule hoare_lift_Pf [where f=arch_caps_of_state])
    apply (rule hoare_lift_Pf [where f="\<lambda>s. arm_global_pts (arch_state s)"])
     apply (wp cap pts hoare_vcg_all_lift hoare_vcg_const_imp_lift obj)
  done


lemma valid_arch_caps_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>"
  assumes pts: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pts (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pts (arch_state s))\<rbrace>"
  assumes obj: "\<And>S p. \<lbrace>aobj_at (empty_table S) p\<rbrace> f \<lbrace>\<lambda>rv. aobj_at (empty_table S) p\<rbrace>"
  shows "\<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding valid_arch_caps_def
  apply (rule hoare_pre)
   apply (wp valid_vs_lookup_lift valid_table_caps_lift lookup cap pts obj)
  apply simp
  done

lemma valid_global_objs_lift':
  assumes pts: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pts (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pts (arch_state s))\<rbrace>"
  assumes pd: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pd (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pd (arch_state s))\<rbrace>"
  assumes obj: "\<And>p. \<lbrace>valid_ao_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_ao_at p\<rbrace>"
  assumes ko: "\<And>ao p. \<lbrace>ako_at ao p\<rbrace> f \<lbrace>\<lambda>_. ako_at ao p\<rbrace>"
  assumes emp: "\<And>pd S. 
       \<lbrace>\<lambda>s. (v \<longrightarrow> pd = arm_global_pd (arch_state s) \<and> S = set (arm_global_pts (arch_state s)) \<and> P s)
            \<and> aobj_at (empty_table S) pd s\<rbrace>
                 f \<lbrace>\<lambda>rv. aobj_at (empty_table S) pd\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_global_objs s \<and> (v \<longrightarrow> P s)\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  unfolding valid_global_objs_def
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f="\<lambda>s. arm_global_pts (arch_state s)", OF pts])
   apply (rule hoare_use_eq [where f="\<lambda>s. arm_global_pd (arch_state s)", OF pd]) 
   apply (wp obj ko emp hoare_vcg_const_Ball_lift hoare_ex_wp)
  apply clarsimp
  done


lemmas valid_global_objs_lift
    = valid_global_objs_lift' [where v=False, simplified]

lemma arch_lifts:
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  assumes aobj_at: "\<And>P P' pd. \<lbrace>\<lambda>s. P (aobj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' pd s)\<rbrace>"
  shows 
  valid_global_pd_mappings_lift: 
    "\<lbrace>valid_global_pd_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_global_pd_mappings\<rbrace>" and
  valid_arch_caps_lift_weak: 
    "(\<And>P. \<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>) \<Longrightarrow> 
      \<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>" and
  valid_global_objs_lift_weak:
    "\<lbrace>valid_global_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>" and
  valid_asid_map_lift:
    "\<lbrace>valid_asid_map\<rbrace> f \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>" and
  valid_kernel_mappings_lift:
    "\<lbrace>valid_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply -
  subgoal 
  apply (simp add: valid_global_pd_mappings_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (rule_tac f="valid_pd_kernel_mappings (arm_kernel_vspace x)" in hoare_lift_Pf)
   apply (rule aobj_at)
  apply (subst valid_pd_kernel_mappings_def valid_pde_kernel_mappings_def)+
  apply (clarsimp simp add: valid_def)
  apply (erule_tac P=P in rsubst)
  apply (rule ext)
  apply (clarsimp intro!: iff_allI split: arch_kernel_obj.splits pde.splits)
  apply (safe; clarsimp)
     apply (erule (1) use_valid[OF _ aobj_at[where P="\<lambda>x. x"]])+
   apply (rule classical, drule (1) use_valid[OF _ aobj_at[where P="\<lambda>x. \<not> x"]], simp)+
   done
  subgoal
  apply (rule valid_arch_caps_lift[OF _ _ arch aobj_at])
   apply (rule vs_lookup_pages_aobj_at_lift[OF aobj_at arch])
  apply assumption
  done
  subgoal
  apply (rule valid_global_objs_lift)
      apply (wp arch)
    apply (simp add: valid_ao_at_def)
    apply (rule hoare_vcg_ex_lift)
    apply (rule hoare_vcg_conj_lift)
     apply (wp aobj_at valid_arch_obj_atyp)
  done
  subgoal
  apply (simp add: valid_asid_map_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (simp add: pd_at_asid_def)
  by (rule vs_lookup_aobj_at_lift[OF aobj_at arch])
  subgoal
  apply (simp add: valid_kernel_mappings_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (simp add: valid_kernel_mappings_if_pd_def ran_def)
  apply (rule hoare_vcg_all_lift)
  apply (case_tac "\<exists>ao. xa = ArchObj ao")
   apply (rule hoare_convert_imp)
    apply clarsimp
    apply (rule hoare_vcg_all_lift)
    subgoal for ao a
    by (rule aobj_at[where P=Not and P'="\<lambda>x. x = ao", simplified aobj_at_def, simplified])
   apply clarsimp
   apply (case_tac ao; simp add: hoare_vcg_prop)
  apply clarsimp
  apply (case_tac xa; simp add: hoare_vcg_prop)
  apply blast
  done
  done

 

lemma equal_kernel_mappings_lift:
  assumes aobj_at: "\<And>P P' pd. \<lbrace>\<lambda>s. P (aobj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' pd s)\<rbrace>"
  shows "\<lbrace>equal_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: equal_kernel_mappings_def)
  apply (rule hoare_vcg_all_lift)+
  apply (rule hoare_convert_imp)
   apply simp
   apply (rule hoare_convert_imp)
    apply (wp aobj_at)
  done


lemma valid_machine_state_lift:
  assumes memory: "\<And>P. \<lbrace>\<lambda>s. P (underlying_memory (machine_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (underlying_memory (machine_state s))\<rbrace>"
  assumes aobj_at: "\<And>P' pd. \<lbrace>aobj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. aobj_at P' pd s\<rbrace>"
  shows "\<lbrace>valid_machine_state\<rbrace> f \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def in_user_frame_def
  apply (rule hoare_lift_Pf[where f="\<lambda>s. underlying_memory (machine_state s)", OF _ memory])
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_vcg_disj_lift[OF _ hoare_vcg_prop])
  apply (rule hoare_vcg_ex_lift)
  subgoal for \<dots> sz
   by (rule aobj_at[where P'="\<lambda>ao. ao = DataPage sz", simplified aobj_at_def, simplified])
  done
  

lemma valid_ao_at_lift:
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
      and y: "\<And>ao. \<lbrace>\<lambda>s. ako_at ao p s\<rbrace> f \<lbrace>\<lambda>rv s. ako_at ao p s\<rbrace>"
  shows      "\<lbrace>valid_ao_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_ao_at p\<rbrace>"
  unfolding valid_ao_at_def
  by (wp hoare_vcg_ex_lift y valid_arch_obj_typ z)


lemmas set_object_v_ker_map
    = set_object_valid_kernel_mappings
            [unfolded valid_kernel_mappings_if_pd_def]


crunch v_ker_map[wp]: set_notification "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_object_asid_map:
  "\<lbrace>valid_asid_map and
    aobj_at (\<lambda>ko'. vs_refs ko' \<subseteq> vs_refs ko) p\<rbrace>
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: valid_asid_map_def set_object_def)
  apply wp
  apply (clarsimp simp: pd_at_asid_def simp del: fun_upd_apply)
  apply (drule bspec, blast)
  apply clarsimp
  apply (rule vs_lookup_stateI, assumption)
   apply (clarsimp simp: aobj_at_def)
   apply blast
  apply simp
  done

lemma set_object_equal_mappings:
  "\<lbrace>\<lambda>s. equal_kernel_mappings s
          \<and> (\<forall>pd. ko = ArchObj (PageDirectory pd)
                \<longrightarrow> (\<forall>x pd'. ako_at (PageDirectory pd') x s
                         \<longrightarrow> (\<forall>w \<in> kernel_mapping_slots. pd w = pd' w)))\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: set_object_def, wp)
  apply (clarsimp simp: equal_kernel_mappings_def aobj_at_def
             split del: split_if)
  apply (simp split: split_if_asm)
  done

lemma valid_global_pd_mappings_pres:
  "\<lbrakk> valid_global_pd_mappings s;
     \<And>pd. ako_at (PageDirectory pd) (arm_global_pd (arch_state s)) s
            \<Longrightarrow> ako_at (PageDirectory pd) (arm_global_pd (arch_state s)) s';
     \<And>pt p. \<lbrakk> ako_at (PageTable pt) p s;
               valid_global_objs s \<Longrightarrow> p \<in> set (arm_global_pts (arch_state s)) \<rbrakk>
            \<Longrightarrow> ako_at (PageTable pt) p s';
     arm_global_pd (arch_state s') = arm_global_pd (arch_state s);
     arm_kernel_vspace (arch_state s') = arm_kernel_vspace (arch_state s) \<rbrakk>
        \<Longrightarrow> valid_global_pd_mappings s'"
  apply atomize
  apply (clarsimp simp: valid_global_pd_mappings_def aobj_at_def)
  apply (clarsimp simp: valid_pd_kernel_mappings_def
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm)
  apply (drule_tac x=x in spec)
  apply (clarsimp simp: valid_pde_kernel_mappings_def aobj_at_def
                        valid_pt_kernel_mappings_def pde_ref_def
                 split: Arch_Structs_A.ARM.pde.split_asm)
  apply (simp split: Structures_A.kernel_object.split_asm
                     arch_kernel_obj.split_asm)
  apply (drule spec, drule spec, drule(1) mp)
  apply (drule mp)
   apply (clarsimp simp: valid_global_objs_def obj_at_def empty_table_def)
   apply (drule_tac x=x in spec)
   apply (simp add: pde_ref_def)[1]
  apply clarsimp
  done

lemma valid_global_pd_mappings_arch_update[simp]:
  "arm_global_pd (f (arch_state s)) = arm_global_pd (arch_state s)
   \<and> arm_kernel_vspace (f (arch_state s)) = arm_kernel_vspace (arch_state s)
     \<Longrightarrow> valid_global_pd_mappings (arch_state_update f s) = valid_global_pd_mappings s"
  by (simp add: valid_global_pd_mappings_def)

lemma set_object_global_pd_mappings:
  "\<lbrace>valid_global_pd_mappings
            and (\<lambda>s. (page_directory_at p s \<or> page_table_at p s)
                       \<longrightarrow> valid_global_objs s \<and> p \<notin> global_refs s)\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv. valid_global_pd_mappings\<rbrace>"
  apply (simp add: set_object_def, wp)
  apply clarsimp
  apply (erule valid_global_pd_mappings_pres)
     apply (clarsimp simp: aobj_at_def a_type_def aa_type_def global_refs_def)+
  done


lemma valid_table_caps_ptD:
  "\<lbrakk> arch_caps_of_state s p = Some (arch_cap.PageTableCap p' None);
     page_table_at p' s; valid_table_caps s \<rbrakk> \<Longrightarrow> 
    \<exists>pt. ako_at (PageTable pt) p' s \<and> valid_arch_obj (PageTable pt) s"
  apply (clarsimp simp: valid_table_caps_def simp del: split_paired_All)
  apply (erule allE)+
  apply (erule (1) impE)  
  apply (clarsimp simp add: is_pt_cap_def cap_asid_def)
  apply (erule impE, rule refl)
  apply (clarsimp simp: aobj_at_def empty_table_def)
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

end
end