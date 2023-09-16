(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAcc_AI
imports SubMonad_AI "Lib.Crunch_Instances_NonDet"
begin

context non_vspace_op
begin

lemma valid_vso_at[wp]:"\<lbrace>valid_vso_at level p\<rbrace> f \<lbrace>\<lambda>_. valid_vso_at level p\<rbrace>"
  by (rule valid_vso_at_lift_aobj_at; wp vsobj_at; simp)

end

context Arch begin global_naming AARCH64

(* Is there a lookup that leads to a page table at (level, p)? *)
locale_abbrev ex_vs_lookup_table ::
  "vm_level \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" ("\<exists>\<rhd> '(_, _')" [0,0] 1000) where
  "ex_vs_lookup_table level p s \<equiv>
     \<exists>asid vref. vs_lookup_table level asid vref s = Some (level, p) \<and> vref \<in> user_region"

bundle unfold_objects =
  obj_at_def[simp]
  in_omonad[simp]
  kernel_object.splits[split]
  arch_kernel_obj.splits[split]
  get_object_wp[wp]

bundle unfold_objects_asm =
  obj_at_def[simp]
  in_omonad[simp]
  kernel_object.split_asm[split]
  arch_kernel_obj.split_asm[split]

lemma invs_valid_asid_table [elim!]:
  "invs s \<Longrightarrow> valid_asid_table s"
  by (simp add: invs_def valid_state_def valid_arch_state_def)

lemma vspace_objs_of_arch_valid_obj:
  "\<lbrakk> vspace_objs_of s p = Some ao; valid_objs s \<rbrakk> \<Longrightarrow> arch_valid_obj ao s"
  by (fastforce simp: valid_obj_arch_valid_obj in_omonad vspace_obj_of_Some)

lemmas pt_upd_simps[simp] = pt_upd_def[split_simps pt.split]

lemma pt_range_upd:
  "pt_range (pt_upd pt i pte) \<subseteq> insert pte (pt_range pt)"
  by (cases pt) auto

lemma ptes_of_wellformed_pte:
  "\<lbrakk> ptes_of s pt_t p = Some pte; valid_objs s \<rbrakk> \<Longrightarrow> wellformed_pte pte"
  apply (clarsimp simp: ptes_of_def in_omonad)
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def)
  done

lemma vs_lookup_table_target:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   vs_lookup_target (level + 1) asid (vref_for_level vref level) s = Some (level + 1, p)"
  apply (simp add: vs_lookup_target_def vs_lookup_slot_def vs_lookup_table_def obind_assoc)
  apply (subgoal_tac "level \<noteq> asid_pool_level"; clarsimp)
  apply (cases "level = max_pt_level", clarsimp simp: max_pt_level_plus_one in_omonad)
  apply (prop_tac "level + 1 \<noteq> asid_pool_level")
   apply (metis max_pt_level_plus_one add.right_cancel)
  apply (clarsimp simp: obind_assoc asid_pool_level_eq)
  apply (subst (asm) pt_walk_split_Some[where level'="level + 1"], simp add: less_imp_le, simp)
  apply (subst (asm) (2) pt_walk.simps)
  apply (clarsimp simp: in_omonad cong: conj_cong)
  apply (rule_tac x="level + 1" in exI)
  apply simp
  apply (subst pt_walk_vref_for_level; simp add: less_imp_le)
  apply (clarsimp simp: is_PageTablePTE_def pptr_from_pte_def split: if_split_asm)
  done

lemma vs_lookup_table_targetD:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> \<exists>p'. vs_lookup_target (level+1) asid vref s = Some (level+1, p')"
  apply (case_tac "level < max_pt_level")
   apply (clarsimp dest!: vs_lookup_table_split_last_Some)
   apply (clarsimp simp: vs_lookup_target_def vs_lookup_slot_def in_omonad pte_ref_def)
   apply (fastforce dest: vm_level_less_plus_1_mono split: pte.splits)
  apply (clarsimp simp: max_pt_level_plus_one vs_lookup_target_def vs_lookup_slot_def in_omonad
                         pte_ref_def pool_for_asid_vs_lookup)
  apply (fastforce dest!: vs_lookup_table_max_pt_level_SomeD)
  done

lemma valid_vs_lookupD:
  "\<lbrakk> vs_lookup_target bot_level asid vref s = Some (level, p) ;
     vref \<in> user_region; valid_vs_lookup s \<rbrakk>
   \<Longrightarrow> asid \<noteq> 0
      \<and> (\<exists>cptr cap. caps_of_state s cptr = Some cap \<and> obj_refs cap = {p}
                    \<and> vs_cap_ref cap = Some (asid, vref_for_level vref level))"
  unfolding valid_vs_lookup_def
  by auto

lemma vs_lookup_table_valid_cap:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); vref \<in> user_region;
     valid_vs_lookup s; valid_asid_pool_caps s \<rbrakk> \<Longrightarrow>
   (\<exists>p' cap. caps_of_state s p' = Some cap \<and> obj_refs cap = {p} \<and>
             vs_cap_ref cap = Some (asid_for_level asid level,
                                    vref_for_level vref (if level=asid_pool_level
                                                         then asid_pool_level else level + 1)))"
  apply (cases "level \<le> max_pt_level")
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region, assumption)
   apply (fastforce simp: asid_for_level_def)
  apply (simp add: not_le)
  apply (clarsimp simp: vs_lookup_table_def pool_for_asid_def valid_asid_pool_caps_def)
  apply (erule allE)+
  apply (erule (1) impE)
  apply clarsimp
  apply (rule exI)+
  apply (rule conjI, assumption)
  apply (simp add: asid_for_level_def vref_for_level_asid_pool user_region_def)
  apply (simp add: asid_high_bits_of_def)
  apply (word_eqI_solve simp: asid_low_bits_def)
  done

lemma invs_valid_asid_pool_caps[elim!]:
  "invs s \<Longrightarrow> valid_asid_pool_caps s"
  by (simp add: invs_def valid_state_def valid_arch_caps_def)

lemma vs_lookup_table_asid_not_0:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); level \<le> max_pt_level;
     vref \<in> user_region; valid_vs_lookup s \<rbrakk>
   \<Longrightarrow> asid \<noteq> 0"
  by (fastforce dest!: vs_lookup_table_targetD valid_vs_lookupD)

lemma vspace_for_asid_from_lookup_target:
  "\<lbrakk> vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level, pt_ptr);
     vref \<in> user_region; valid_vs_lookup s \<rbrakk>
   \<Longrightarrow> vspace_for_asid asid s = Some pt_ptr"
  apply (frule valid_vs_lookupD; clarsimp?)
  apply (clarsimp simp: vs_lookup_target_def in_omonad word_neq_0_conv
                        vs_lookup_slot_def pool_for_asid_vs_lookup asid_pool_level_eq[symmetric]
                        vspace_for_asid_def vspace_for_pool_def entry_for_asid_def
                  split: if_splits)
  done

lemma unique_table_refsD:
  "\<lbrakk> caps_of_state s p = Some cap; caps_of_state s p' = Some cap';
     unique_table_refs s; obj_refs cap' = obj_refs cap \<rbrakk>
   \<Longrightarrow> table_cap_ref cap' = table_cap_ref cap"
  unfolding unique_table_refs_def by blast

lemma table_cap_ref_vs_cap_ref:
  "\<lbrakk> table_cap_ref cap' = table_cap_ref cap; is_pt_cap cap; is_pt_cap cap' \<rbrakk>
   \<Longrightarrow> vs_cap_ref cap' = vs_cap_ref cap"
  apply (clarsimp simp: table_cap_ref_def vs_cap_ref_def arch_cap_fun_lift_def split: cap.splits)
  apply (clarsimp simp: vs_cap_ref_arch_def table_cap_ref_arch_def split: arch_cap.splits)
  done

(* FIXME MOVE, these should be abbreviations *)
lemma is_ko_to_discs:
  "is_ep = is_Endpoint"
  "is_ntfn = is_Notification"
  "is_tcb = is_TCB"
  apply (all \<open>rule ext, simp add: is_ep_def is_ntfn_def is_tcb_def split: kernel_object.splits\<close>)
  done

locale_abbrev cap_pt_type :: "cap \<Rightarrow> pt_type" where
  "cap_pt_type cap \<equiv> acap_pt_type (the_arch_cap cap)"

lemma cap_to_pt_is_pt_cap_and_type:
  "\<lbrakk> obj_refs cap = {p}; caps_of_state s cptr = Some cap; pts_of s p = Some pt;
     valid_caps (caps_of_state s) s \<rbrakk>
   \<Longrightarrow> is_pt_cap cap \<and> cap_pt_type cap = pt_type pt"
  by (drule (1) valid_capsD)
     (auto simp: pts_of_ko_at is_pt_cap_def arch_cap_fun_lift_def arch_cap.disc_eq_case(4)
                 valid_cap_def obj_at_def is_ko_to_discs is_cap_table_def the_arch_cap_def
           split: if_splits arch_cap.split cap.splits option.splits)

lemma unique_vs_lookup_table:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     vs_lookup_table level' asid' vref' s = Some (level', p');
     p' = p; level \<le> max_pt_level; level' \<le> max_pt_level;
     vref \<in> user_region; vref' \<in> user_region;
     unique_table_refs s; valid_vs_lookup s;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     valid_caps (caps_of_state s) s \<rbrakk>
   \<Longrightarrow> asid' = asid \<and>
       vref_for_level vref' (level'+1) = vref_for_level vref (level+1)"
  supply valid_vspace_obj.simps[simp del]
  apply (frule (5) valid_vspace_objs_strongD)
  apply (frule (5) valid_vspace_objs_strongD[where pt_ptr=p'])
  apply (drule (1) vs_lookup_table_target)+
  apply (drule valid_vs_lookupD, erule vref_for_level_user_region, assumption)+
  apply (elim conjE exE)
  apply (rename_tac pt pt' cptr cptr' cap cap')
  apply simp
  apply (subgoal_tac "is_pt_cap cap \<and> is_pt_cap cap'")
   prefer 2
   apply (simp add: cap_to_pt_is_pt_cap_and_type)
  apply (drule (2) unique_table_refsD, simp)
  apply (drule table_cap_ref_vs_cap_ref; simp)
  done

lemma vref_for_level_pt_index_idem:
  assumes "level' \<le> max_pt_level" and "level'' \<le> level'" and "level < max_pt_level"
  shows "vref_for_level
           (vref_for_level vref (level'' + 1) || (pt_index level vref' << pt_bits_left level''))
           (level' + 1)
         = vref_for_level vref (level' + 1)"
proof -
  have dist_zero_right':
    "\<And>w x y. \<lbrakk> (w::('a::len) word) = y; x = 0\<rbrakk> \<Longrightarrow> w || x = y"
    by auto
  show ?thesis using assms
    using ptTranslationBits_NormalPT_T_leq unfolding vref_for_level_def pt_index_def
    apply (subst word_ao_dist)
    apply (rule dist_zero_right')
     apply (subst mask_lower_twice)
      apply (rule pt_bits_left_mono, erule (1) vm_level_le_plus_1_mono, rule refl)
    apply (auto simp: mask_shifl_overlap_zero pt_bits_left_def level_type_less_max_pt_level
                      add_le_mono)
    done
qed

lemma pt_slot_offset_vref_for_level_idem:
  "\<lbrakk> is_aligned p (pt_bits (level_type level)); level' < max_pt_level; level < max_pt_level \<rbrakk>
   \<Longrightarrow> pt_slot_offset level' p
            (vref_for_level vref (level' + 1) || (pt_index level vref << pt_bits_left level'))
       = pt_slot_offset level p vref"
  apply (prop_tac "level_type level' = level_type level", simp add: level_type_less_max_pt_level)
  apply (simp add: pt_slot_offset_or_def)
  done

lemma pt_walk_loop_last_level_ptpte_helper_induct:
  "\<lbrakk> pt_walk level level' p vref ptes = Some (level', p); level < max_pt_level; level > level';
     is_aligned p (pt_bits (level_type level)) \<rbrakk>
   \<Longrightarrow> \<exists>p' vref'. (pt_walk level 0 p vref' ptes = Some (0, p'))
                 \<and> (\<exists>pte level. ptes (level_type level) (pt_slot_offset level p' vref') = Some pte
                                \<and> is_PageTablePTE pte \<and> level < max_pt_level)
                 \<and> vref_for_level vref' (level' + 1) = vref_for_level vref (level' + 1)"
  supply vm_level_less_le_1[simp]
  apply (induct level arbitrary: p level' vref; clarsimp)
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
  apply (rename_tac pte)
  apply (case_tac "level' = 0")
   apply clarsimp
   apply (subst pt_walk.simps)
   apply (clarsimp simp: in_omonad)
   apply (rule_tac x=p in exI)
   apply (clarsimp simp: in_omonad)
   apply (rule_tac x=vref in exI)
   apply (clarsimp simp: in_omonad)
   apply (rule conjI)
    apply force
   apply blast
  (* set up assumption of IH *)
  apply (subgoal_tac
           "pt_walk (level - 1) (level' - 1) (pptr_from_pte pte)
                    (vref_for_level vref (level'+1) || (pt_index level vref << pt_bits_left level'))
                    ptes
            = Some (level' - 1, pptr_from_pte pte)")
   apply (drule meta_spec, drule meta_spec, drule meta_spec, drule (1) meta_mp, drule meta_mp)
    apply (simp add: vm_level.minus_one_leq_less)
   apply (drule meta_mp)
    apply (simp add: vm_level.minus_one_leq_less vm_level.neq_0_conv pt_walk_max_level)
   apply (clarsimp simp: pptr_from_pte_aligned_pt_bits)
   apply (subst pt_walk.simps)
   apply (clarsimp simp: in_omonad)
   apply (rule_tac x=p' in exI)
   apply (rule_tac x=vref' in exI)
   apply (rule conjI)
    (* walk to level 0 *)
    apply (rule_tac x=pte in exI)
    apply clarsimp
    apply (subgoal_tac "pt_slot_offset level p vref' = pt_slot_offset level p vref")
     prefer 2
     apply (rule vref_for_level_pt_slot_offset)
     apply (rule_tac level="level'+1" in  vref_for_level_eq_mono)
      apply (drule_tac level'="level'+1" in  vref_for_level_eq_mono)
       apply (fastforce intro: vref_for_level_pt_index_idem)
      apply (fastforce intro: vref_for_level_pt_index_idem)
     apply (erule vm_level.plus_one_leq)
    apply simp
   apply (rule conjI, blast)
   apply (drule_tac level'="level'+1" in  vref_for_level_eq_mono
          ; fastforce intro: vref_for_level_pt_index_idem)
  (* show assumption used for IH earlier *)
  apply (rule_tac pt_walk_split_Some[where level'="level" and level="level - 1" for level,
                                     THEN iffD2])
    apply (fastforce dest!: vm_level_not_less_zero intro: less_imp_le)
   apply (meson vm_level.leq_minus1_less vm_level.not_less_zero_bit0 le_less less_linear less_trans)
  apply (subgoal_tac
           "pt_walk (level - 1) level' (pptr_from_pte pte)
                    (vref_for_level vref (level' + 1) || (pt_index level vref << pt_bits_left level'))
            = pt_walk (level - 1) level' (pptr_from_pte pte) vref")
   prefer 2
   apply (rule pt_walk_vref_for_level_eq)
    apply (subst vref_for_level_pt_index_idem, simp+)
   apply (meson vm_level.leq_minus1_less vm_level.not_less_zero_bit0 le_less less_linear less_trans)
  apply clarsimp
  apply (subst pt_walk.simps)
  apply clarsimp
  apply (frule vm_level_not_less_zero)
  apply (clarsimp simp: in_omonad)
  apply (rule_tac x=pte in exI)
  apply (clarsimp simp add: pt_slot_offset_vref_for_level_idem level_type_less_max_pt_level)
  done

(* Looking only at PTEs, ensure that all PTEs in a VSRootPT are also a NormalPT. *)
definition pte_types_distinct :: "(pt_type \<Rightarrow> obj_ref \<Rightarrow> pte option) \<Rightarrow> bool" where
  "pte_types_distinct ptes \<equiv>
    \<forall>p vref. is_aligned p (pt_bits (level_type max_pt_level)) \<longrightarrow>
             ptes NormalPT_T p = None \<or> ptes VSRootPT_T (pt_slot_offset max_pt_level p vref) = None"

lemma pspace_distinct_pte_types_distinct:
  "pspace_distinct s \<Longrightarrow> pte_types_distinct (ptes_of s)"
  unfolding pte_types_distinct_def
  apply (rule ccontr, clarsimp dest!: ptes_of_pts_of)
  apply (rename_tac pt pt')
  apply (clarsimp simp: table_base_pt_slot_offset[where level=max_pt_level, simplified])
  apply (drule_tac pt=pt and pt'=pt' and p=p in pts_of_type_unique[rotated -1]; simp)
  done

(* If we start a lookup at max_pt_level and get back to the same page table pointer at a lower
   level, then we would have a pointer that simultaneously is valid under two different level_types.
   This is a contradiction to pspace_distinct, expressed as pte_types_distinct. *)
lemma pt_walk_loop_last_level_ptpte_helper_max_pt_level:
  "\<lbrakk> pt_walk max_pt_level level' p vref ptes = Some (level', p); level' < max_pt_level;
     ptes (level_type level') p = Some pte; pte_types_distinct ptes;
     is_aligned p (pt_bits (level_type max_pt_level)) \<rbrakk>
   \<Longrightarrow> False"
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp add: level_type_less_max_pt_level split: if_split_asm)
  apply (simp add: pte_types_distinct_def)
  apply (erule_tac x=p in allE)
  apply simp
  done

lemma pt_walk_loop_last_level_ptpte_helper:
  "\<lbrakk> pt_walk level level' p vref ptes = Some (level', p); level \<le> max_pt_level; level > level';
     ptes (level_type level') p = Some pte; pte_types_distinct ptes;
     is_aligned p (pt_bits (level_type level)) \<rbrakk>
   \<Longrightarrow> \<exists>p' vref'. (pt_walk level 0 p vref' ptes = Some (0, p'))
                 \<and> (\<exists>pte level. ptes (level_type level) (pt_slot_offset level p' vref') = Some pte
                                \<and> is_PageTablePTE pte \<and> level < max_pt_level)
                 \<and> vref_for_level vref' (level' + 1) = vref_for_level vref (level' + 1)"
  (* If the entire lookup is below max_pt_level, the page tables types stay the same and we
     reason by induction. If the lookup starts at max_pt_level, we reason differently. *)
  apply (cases "level = max_pt_level")
   apply (fastforce dest: pt_walk_loop_last_level_ptpte_helper_max_pt_level)
  apply (prop_tac "level < max_pt_level", simp add: less_le)
  apply (fastforce dest: pt_walk_loop_last_level_ptpte_helper_induct)
  done

(* if you can walk the page tables and get back to a page table you have already visited,
   then you can create a lookup path such that you end up with a PT PTE at the bottom-most level *)
lemma pt_walk_loop_last_level_ptpte:
  "\<lbrakk> pt_walk level level' p vref ptes = Some (level', p); level \<le> max_pt_level; level > level';
     ptes (level_type level') p = Some pte; pte_types_distinct ptes;
     is_aligned p (pt_bits level) \<rbrakk>
   \<Longrightarrow> \<exists>p' vref'. (pt_walk level 0 p vref' ptes = Some (0, p'))
                 \<and> (\<exists>pte. ptes (level_type 0) (pt_slot_offset 0 p' vref') = Some pte \<and> is_PageTablePTE pte)
                 \<and> vref_for_level vref' (level' + 1) = vref_for_level vref (level' + 1)"
  apply (drule pt_walk_loop_last_level_ptpte_helper; simp?)
  apply clarsimp
  apply (rename_tac pte' level'')
  apply (rule_tac x=p' in exI)
  apply (rule_tac x="vref_for_level vref' 1 || (pt_index level'' vref' << pt_bits_left 0)" in exI)
  apply (rule conjI)
   apply (subst pt_walk_vref_for_level_eq; assumption?)
    apply simp
    apply (rule vref_for_level_pt_index_idem[where level''=0 and level'=0, simplified], simp)
   apply simp
  apply (rule conjI)
   apply (rule_tac x=pte' in exI)
   apply (clarsimp simp: level_type_less_max_pt_level)
   apply (subst pt_slot_offset_vref_for_level_idem[where level'=0, simplified]; simp?)
   apply (drule (2) pt_walk_is_aligned)
   apply (clarsimp simp: level_type_less_max_pt_level)
  apply (subst vref_for_level_pt_index_idem[where level''=0, simplified]; simp)
  done

(* If when performing page table walks to two different depths we arrive at the same page table,
   then we can construct a complete walk ending on a PT PTE at the bottom level.
   This is significant, because validity of PTEs requires that only pages are mapped at the
   deepest PT level.
   Note: we are looking up vref in both cases, but as we stop early we observe that only
         vref_for_level bits of vref are used, for the level before we stopped.
   *)
lemma pt_walk_same_for_different_levels:
  "\<lbrakk> pt_walk top_level level' ptptr vref ptes = Some (level', p);
     pt_walk top_level level ptptr vref ptes = Some (level, p);
     level' < level; top_level \<le> max_pt_level;
     ptes (level_type level') p = Some pte; pte_types_distinct ptes;
     is_aligned ptptr (pt_bits top_level) \<rbrakk>
   \<Longrightarrow> \<exists>vref'' ptptr'. pt_walk top_level 0 ptptr vref'' ptes = Some (0, ptptr') \<and>
                      (\<exists>pte. ptes (level_type 0) (pt_slot_offset 0 ptptr' vref'') = Some pte \<and> is_PageTablePTE pte) \<and>
                      vref_for_level vref'' (level' + 1) = vref_for_level vref (level' + 1)"
  apply (subgoal_tac "level \<le> top_level")
   prefer 2
   apply (fastforce simp: pt_walk_max_level)
  apply (subst (asm) pt_walk_split_Some[where level'=level], simp+)
  apply (drule pt_walk_loop_last_level_ptpte; (simp add: pt_walk_is_aligned)?)
  apply clarsimp
  apply (subst pt_walk_split_Some[where level'=level], simp+)
  apply (rule_tac x="vref'" in exI)
  apply (rule_tac x="p'" in exI)
  apply (rule conjI)
   apply (rule_tac x="p" in exI)
   apply simp
   apply (subst pt_walk_vref_for_level_eq; assumption?)
   apply (fastforce elim: vref_for_level_eq_mono  simp: vm_level_le_plus_1_mono)
  apply clarsimp
  done

lemma vs_lookup_table_same_for_different_levels:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     vs_lookup_table level' asid vref' s = Some (level', p);
     vref_for_level vref (level+1) = vref_for_level vref' (level+1);
     vref \<in> user_region; vref' \<in> user_region; level' < level; level \<le> max_pt_level;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> \<exists>vref'' p' pte. vs_lookup_slot 0 asid vref'' s = Some (0, p') \<and> ptes_of s (level_type 0) p' = Some pte \<and>
                      is_PageTablePTE pte \<and>
                      vref_for_level vref'' (level' + 1) = vref_for_level vref' (level' + 1)"
  apply (drule pspace_distinct_pte_types_distinct)
  apply (frule (1) valid_vspace_objs_strongD[where bot_level=level']; simp)
  apply clarsimp
  apply (frule (1) pspace_aligned_pts_ofD)
  apply (drule pts_of_ptes_of; clarsimp)
  apply (subst (asm) vs_lookup_vref_for_level1[where level=level, symmetric], blast)
  apply (subst (asm) vs_lookup_vref_for_level1[where level=level', symmetric], blast)
  apply (clarsimp simp: vs_lookup_table_def in_omonad asid_pool_level_eq)
  apply (prop_tac "level' \<le> max_pt_level", simp)
  apply (simp add: in_omonad pt_walk_vref_for_level1)
  apply (simp add: vs_lookup_slot_def in_omonad vs_lookup_table_def cong: conj_cong)
  apply (drule pt_walk_same_for_different_levels; simp?)
  apply (erule vspace_for_pool_is_aligned; simp)
  by force

lemma no_loop_vs_lookup_table_helper:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     vs_lookup_table level' asid vref' s = Some (level', p);
     vref_for_level vref' (max (level+1) (level'+1)) = vref_for_level vref (max (level+1) (level'+1));
     vref \<in> user_region; vref' \<in> user_region;
     level \<le> max_pt_level; level' \<le> max_pt_level; level' < level;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s; pspace_distinct s \<rbrakk>
    \<Longrightarrow> level' = level"
  apply (drule (1) vs_lookup_table_same_for_different_levels; simp?)
   apply (frule (1) vm_level_less_plus_1_mono)
   apply (simp add: max_absorb1)
  apply (frule (1) vm_level_less_plus_1_mono)
  apply (simp add: max_absorb1)
  apply (clarsimp simp: vs_lookup_slot_def in_omonad, clarsimp split: if_splits)
  apply (rename_tac pt_ptr)
  (* the goal is to derive a contradiction: we have a walk down to the last level;
     if we can show the pte we found is valid, it can't be a PT pte *)
  apply (subgoal_tac "valid_pte 0 pte s")
   apply (blast dest: ptpte_level_0_valid_pte)
  apply (prop_tac "vref'' \<in> user_region")
   apply (frule_tac vref=vref' and level="level'+1" in vref_for_level_user_region)
   apply (rule vref_for_level_user_regionD[where level="level'+1"]; simp?)
   apply (erule vm_level_less_max_pt_level)
  apply (prop_tac "is_aligned pt_ptr (pt_bits (level_type 0))")
   apply (fastforce elim!: vs_lookup_table_is_aligned)
  apply (drule_tac pt_ptr=pt_ptr in valid_vspace_objs_strongD, assumption; simp?)
  apply (fastforce simp: level_pte_of_def in_omonad is_aligned_pt_slot_offset_pte)
  done

lemma no_loop_vs_lookup_table:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     vs_lookup_table level' asid vref' s = Some (level', p);
     vref_for_level vref' (max (level+1) (level'+1)) = vref_for_level vref (max (level+1) (level'+1));
     vref \<in> user_region; vref' \<in> user_region;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s; pspace_distinct s \<rbrakk>
    \<Longrightarrow> level' = level"
  apply (case_tac "level = asid_pool_level"; simp)
   apply (case_tac "level' = asid_pool_level"; simp)
   apply (frule (5) valid_vspace_objs_strongD[where bot_level=level' and level=level'])
   apply (fastforce dest!: vs_lookup_table_no_asid_pt)
  apply (case_tac "level' = asid_pool_level"; simp)
   apply (frule (5) valid_vspace_objs_strongD[where bot_level=level and level=level])
   apply (fastforce dest!: vs_lookup_table_no_asid_pt)
  apply (case_tac "level' = level"; clarsimp)
  (* reduce to two cases with identical proofs, either level' < level or vice-versa *)
  apply (case_tac "level' < level"; (clarsimp dest!: leI dual_order.not_eq_order_implies_strict)?)
   apply (drule no_loop_vs_lookup_table_helper[where level'=level' and level=level])
                 apply assumption+
   apply simp
  apply (drule no_loop_vs_lookup_table_helper[where level'=level and level=level']; assumption?)
   apply (simp add: max.commute)+
  done

(* We can never find the same table/pool object at different levels.
   When combined with unique_vs_lookup_table, shows there exists
   only one path from the ASID table to any asid_pool / page table in the system *)
lemma ex_vs_lookup_level:
  "\<lbrakk> \<exists>\<rhd> (level, p) s;  \<exists>\<rhd> (level', p) s;
     unique_table_refs s; valid_vs_lookup s;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s; pspace_distinct s;
     valid_caps (caps_of_state s) s \<rbrakk>
   \<Longrightarrow> level' = level"
  apply clarsimp
  apply (rename_tac asid' vref vref')
  apply (case_tac "level = asid_pool_level"; simp)
   apply (case_tac "level' = asid_pool_level"; simp)
   apply (frule (5) valid_vspace_objs_strongD[where bot_level=level' and level=level'])
   apply (fastforce dest!: vs_lookup_table_no_asid_pt)
  apply (case_tac "level' = asid_pool_level"; simp)
   apply (frule (5) valid_vspace_objs_strongD[where bot_level=level and level=level])
   apply (fastforce dest!: vs_lookup_table_no_asid_pt)
  apply (frule_tac asid=asid and asid'=asid' in unique_vs_lookup_table, assumption; simp)
  apply (drule_tac level=level and level'=level' and vref'=vref' in no_loop_vs_lookup_table
         ; fastforce dest: vref_for_level_eq_max_mono simp: max.commute)
  done

lemma valid_objs_caps:
  "valid_objs s \<Longrightarrow> valid_caps (caps_of_state s) s"
  apply (clarsimp simp: valid_caps_def)
  apply (erule (1) caps_of_state_valid_cap)
  done

(* invs could be relaxed; lemma so far only needed when invs is present *)
lemma vs_lookup_table_unique_level:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     vs_lookup_table level' asid' vref' s = Some (level', p');
     p' = p;
     level \<le> max_pt_level; level' \<le> max_pt_level; vref \<in> user_region; vref' \<in> user_region;
     invs s\<rbrakk>
  \<Longrightarrow> level' = level \<and> asid' = asid \<and>
      vref_for_level vref' (level+1) = vref_for_level vref (level+1)"
  apply (frule (1) unique_vs_lookup_table[where level'=level']; (clarsimp intro!: valid_objs_caps)?)
  apply (drule (1) no_loop_vs_lookup_table; (clarsimp intro!: valid_objs_caps)?)
  apply (thin_tac "p' = p")
  apply (drule arg_cong[where f="\<lambda>vref. vref_for_level vref (level + 1)"])
  apply (drule arg_cong[where f="\<lambda>vref. vref_for_level vref (level' + 1)"])
  apply (auto simp: max_def split: if_split_asm)
  done

(* invs could be relaxed; lemma so far only needed when invs is present *)
lemma vs_lookup_slot_table_base:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, slot); vref \<in> user_region;
     level \<le> max_pt_level; invs s \<rbrakk> \<Longrightarrow>
   vs_lookup_table level asid vref s = Some (level, table_base level slot)"
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (drule vs_lookup_table_is_aligned; clarsimp)
  done

(* invs could be relaxed; lemma so far only needed when invs is present *)
lemma vs_lookup_slot_table_unfold:
  "\<lbrakk> level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk> \<Longrightarrow>
   vs_lookup_slot level asid vref s = Some (level, pt_slot) =
   (vs_lookup_table level asid vref s = Some (level, table_base level pt_slot) \<and>
    pt_slot = pt_slot_offset level (table_base level pt_slot) vref)"
  apply (rule iffI)
   apply (frule (3) vs_lookup_slot_table_base)
   apply (clarsimp simp: vs_lookup_slot_def in_omonad split: if_split_asm)
  apply (clarsimp simp: vs_lookup_slot_def in_omonad)
  done

lemma pt_slot_offset_vref_for_level:
  "\<lbrakk> vref_for_level vref' (level + 1) = vref_for_level vref (level + 1);
     pt_slot_offset level p vref = pt_slot_offset level p vref';
     is_aligned p (pt_bits level); level \<le> max_pt_level \<rbrakk>
    \<Longrightarrow> vref_for_level vref' level = vref_for_level vref level"
  apply (clarsimp simp: pt_slot_offset_def vref_for_level_def pt_index_def)
  apply (drule shiftl_inj; (rule word_and_le', rule mask_mono, simp add: bit_simps)?)
  apply word_eqI
  apply (case_tac "pt_bits_left level \<le> n"; simp)
  apply (case_tac "pt_bits_left (level + 1) \<le> n", fastforce)
  apply (clarsimp simp: not_le pt_bits_left_plus1)
  apply (thin_tac "All P" for P)
  apply (thin_tac "All P" for P)
  apply (erule_tac x="n - pt_bits_left level" in allE)
  by fastforce

(* invs could be relaxed; lemma so far only needed when invs is present *)
lemma vs_lookup_slot_unique_level:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, p);
     vs_lookup_slot level' asid' vref' s = Some (level', p');
     p' = p;
     level \<le> max_pt_level; level' \<le> max_pt_level; vref \<in> user_region; vref' \<in> user_region;
     invs s\<rbrakk>
  \<Longrightarrow> level' = level \<and> asid' = asid \<and> vref_for_level vref' level = vref_for_level vref level"
  apply (clarsimp simp: vs_lookup_slot_table_unfold)
  apply (frule (1) vs_lookup_table_unique_level[where level'=level']; clarsimp?)
   apply (drule valid_vspace_objs_strongD[rotated]; fastforce?)+
   apply clarsimp
   apply (drule invs_distinct)
   apply (rename_tac pt pt')
   apply (drule_tac pt=pt and pt'=pt' in pts_of_type_unique[rotated -1]; simp)
  apply (drule pt_slot_offset_vref_for_level[where p="table_base (level_type level) p"]; clarsimp)
  done

lemmas get_asid_pool_wp = gets_map_wp'

lemma set_asid_pool_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  including unfold_objects
  by (wpsimp simp: set_asid_pool_def wp: set_object_wp)

lemmas set_asid_pool_typ_ats [wp] = abs_typ_at_lifts [OF set_asid_pool_typ_at]

bundle pagebits =
  pt_bits_def[simp]
  pageBits_def[simp] mask_lower_twice[simp]
  and.assoc[where ?'a = \<open>'a::len word\<close>,symmetric,simp] obj_at_def[simp]
  pte.splits[split]


lemma get_pt_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) p s \<longrightarrow> Q pt s\<rbrace> get_pt p \<lbrace>Q\<rbrace>"
  by (wpsimp simp: obj_at_def in_opt_map_eq)

lemma get_pte_wp:
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (table_base pt_t p) s \<longrightarrow>
             Q (pt_apply pt (table_index pt_t p)) s\<rbrace>
   get_pte pt_t p
   \<lbrace>Q\<rbrace>"
  by (wpsimp simp: ptes_of_Some in_opt_map_eq obj_at_def)

lemma get_pte_inv[wp]:
  "get_pte pt_t p \<lbrace>P\<rbrace>"
  by (wpsimp wp: get_pte_wp)

lemmas store_pte_typ_ats [wp] = abs_typ_at_lifts [OF store_pte_typ_at]

crunch cte_wp_at[wp]: set_irq_state "\<lambda>s. P (cte_wp_at P' p s)"

lemma set_pt_cte_wp_at:
  "set_pt ptr val \<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_pt_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
               simp: cte_wp_at_after_update)

lemma set_asid_pool_cte_wp_at:
  "set_asid_pool ptr val \<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update)

lemma set_pt_pred_tcb_at[wp]:
  "set_pt ptr val \<lbrace> \<lambda>s. Q (pred_tcb_at proj P t s) \<rbrace>"
  unfolding set_pt_def set_object_def
  by (wpsimp wp: get_object_wp simp: pred_tcb_at_def obj_at_def)

lemma set_asid_pool_pred_tcb_atP[wp]:
  "set_asid_pool ptr val \<lbrace>\<lambda>s. P (pred_tcb_at proj Q t s)\<rbrace>"
  unfolding set_asid_pool_def set_object_def
  by (wpsimp wp: get_object_wp simp: pred_tcb_at_def obj_at_def)

lemma table_base_index_eq:
  "is_aligned p pte_bits \<Longrightarrow> table_base pt_t p + (table_index pt_t p << pte_bits) = p"
  apply (subst word_plus_and_or_coroll, word_eqI_solve)
  apply word_eqI
  apply (subgoal_tac "p !! n \<longrightarrow> \<not> pte_bits > n"; fastforce)
  done

lemma more_pt_inner_beauty: (* FIXME AARCH64: rename during Refine *)
  "\<lbrakk> x \<noteq> table_index pt_t p; x \<le> mask (ptTranslationBits pt_t);
     table_base pt_t p + (x << pte_bits) = p \<rbrakk> \<Longrightarrow> False"
  by (metis table_index_plus is_aligned_neg_mask2)

lemmas undefined_validE_R = hoare_FalseE_R[where f=undefined]


lemma arch_derive_cap_valid_cap:
  "\<lbrace>valid_cap (cap.ArchObjectCap arch_cap)\<rbrace>
  arch_derive_cap arch_cap
  \<lbrace>valid_cap\<rbrace>, -"
  apply(simp add: arch_derive_cap_def)
  apply(cases arch_cap, simp_all add: arch_derive_cap_def o_def)
      apply(rule hoare_pre, wpc?, wp+;
            clarsimp simp add: cap_aligned_def valid_cap_def split: option.splits)+
  done


lemma arch_derive_cap_inv:
  "\<lbrace>P\<rbrace> arch_derive_cap arch_cap \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding arch_derive_cap_def by (cases arch_cap; wpsimp)

(* We know it must be a NormalPT_T for PagePTE, because top-level tables cannot have PagePTEs *)
definition
  "valid_mapping_entries m \<equiv> case m of
    (InvalidPTE, _) \<Rightarrow> \<top>
  | (PagePTE _ _ _ _, p) \<Rightarrow> pte_at NormalPT_T p
  | (PageTablePTE _, _) \<Rightarrow> \<bottom>"

definition
  "invalid_pte_at pt_t p \<equiv> \<lambda>s. ptes_of s pt_t p = Some InvalidPTE"

definition
  "valid_slots \<equiv> \<lambda>(pte, p, level) s. wellformed_pte pte \<and>
     (\<forall>level. \<exists>\<rhd>(level, table_base level p) s \<longrightarrow> pte_at level p s \<and> valid_pte level pte s)"

lemma ucast_mask_asid_low_bits [simp]:
  "ucast ((asid::machine_word) && mask asid_low_bits) = (ucast asid :: asid_low_index)"
  by (word_eqI simp: asid_low_bits_def)

lemma ucast_ucast_asid_high_bits [simp]:
  "ucast (ucast (asid_high_bits_of asid)::machine_word) = asid_high_bits_of asid"
  by word_eqI_solve

lemma mask_asid_low_bits_ucast_ucast:
  "((asid::machine_word) && mask asid_low_bits) = ucast (ucast asid :: asid_low_index)"
  by (word_eqI_solve simp: asid_low_bits_def)

lemma set_asid_pool_cur [wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  unfolding set_asid_pool_def by (wpsimp wp: get_object_wp)

lemma set_asid_pool_cur_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  unfolding cur_tcb_def
  by (rule hoare_lift_Pf [where f=cur_thread]; wp)

crunch arch [wp]: set_asid_pool "\<lambda>s. P (arch_state s)"
  (wp: get_object_wp)

lemma set_asid_pool_pts_of [wp]:
  "set_asid_pool p a \<lbrace>\<lambda>s. P (pts_of s)\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_wp)
  apply (erule_tac P=P in subst[rotated])
  apply (rule ext)
  apply (clarsimp simp: opt_map_def obj_at_def split: option.splits)
  done

lemma set_asid_pool_asid_pools_of[wp]:
  "\<lbrace>\<lambda>s. P ((asid_pools_of s) (p \<mapsto> ap))\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_ s. P (asid_pools_of s)\<rbrace>"
  unfolding set_asid_pool_def
  by (wpsimp wp: set_object_wp)
     (fastforce simp: obj_at_def opt_map_def elim!: rsubst[where P=P])

lemma entry_for_pool_None[simp]:
  "entry_for_pool p (asid_of asid_high asid_low) (pools (p \<mapsto> a(asid_low := None))) = None"
  by (simp add: entry_for_pool_def obind_def)

lemma valid_asid_table_inj:
  "\<lbrakk> asid_table s asid = Some p; asid_table s asid' = Some p; valid_asid_table s \<rbrakk> \<Longrightarrow> asid' = asid"
  unfolding valid_asid_table_def
  by clarsimp (drule inj_onD; fastforce)

lemma set_asid_pool_None_vmid[wp]:
  "\<lbrace>\<lambda>s. valid_asid_table s \<and>
        asid_pools_of s p = Some ap \<and>
        (\<exists>asid_high. asid_table s asid_high = Some p \<and>
                     P ((vmid_for_asid s) (asid_of asid_high asid_low := None)))\<rbrace>
   set_asid_pool p (ap(asid_low := None))
   \<lbrace>\<lambda>_ s. P (vmid_for_asid s)\<rbrace>"
  apply (wp_pre, wps, wp)
  apply (clarsimp simp del: fun_upd_apply)
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (clarsimp simp: vmid_for_asid_def obind_def simp del: fun_upd_apply split: option.splits)
  apply (clarsimp simp: opt_map_left_None)
  apply (rule opt_map_apply_left_eq)
  apply (clarsimp simp: entry_for_pool_def obind_def split: option.splits)
  apply (drule (2) valid_asid_table_inj, simp)
  apply (erule notE)
  apply (simp add: asid_bits_of_defs)
  apply (word_eqI_solve simp: asid_high_bits_def asid_low_bits_def)
  done

lemma set_asid_pool_None_vmid_inv:
  "\<lbrace>\<lambda>s. vmid_inv s \<and> valid_asid_table s \<and>
        asid_pools_of s p = Some ap \<and>
        (\<exists>asid_high. asid_table s asid_high = Some p \<and>
                     vmid_for_asid s (asid_of asid_high asid_low) = None) \<rbrace>
   set_asid_pool p (ap(asid_low := None))
   \<lbrace>\<lambda>_. vmid_inv\<rbrace>"
  unfolding vmid_inv_def
  by (rule hoare_lift_Pf2[where f="\<lambda>s. arm_vmid_table (arch_state s)"]; wp)
     (fastforce simp del: fun_upd_apply)

lemma set_asid_pool_vcpus_of[wp]:
  "set_asid_pool p ap \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_asid_pool_def
  by (wpsimp wp: set_object_wp)
     (fastforce simp: dom_def opt_map_def obj_at_def split: option.splits elim!: rsubst[where P=P])

lemma set_asid_pool_dom[wp]:
  "set_asid_pool p ap \<lbrace>\<lambda>s. P (dom (asid_pools_of s))\<rbrace>"
  unfolding set_asid_pool_def
  by (wpsimp wp: set_object_wp)
     (auto simp: dom_def opt_map_def obj_at_def is_ArchObj_def
           split: option.splits elim!: rsubst[where P=P])

lemma set_asid_pool_valid_asid_table[wp]:
  "set_asid_pool p ap \<lbrace>valid_asid_table\<rbrace>"
  unfolding valid_asid_table_def
  using set_asid_pool_asid_pools_of[wp del]
  by (wp_pre, wps, wp, clarsimp)

lemma set_asid_pool_valid_global_tables[wp]:
  "set_asid_pool p ap \<lbrace>valid_global_tables\<rbrace>"
  by (wp_pre, wps, wp, clarsimp)

lemma set_asid_pool_None_valid_arch:
  "\<lbrace>\<lambda>s. valid_arch_state s \<and>
        asid_pools_of s p = Some ap \<and>
        (\<exists>asid_high. asid_table s asid_high = Some p \<and>
                     vmid_for_asid s (asid_of asid_high asid_low) = None) \<rbrace>
   set_asid_pool p (ap (asid_low := None))
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding valid_arch_state_def
  by (wpsimp wp: set_asid_pool_None_vmid_inv valid_global_arch_objs_lift cur_vcpu_typ_lift)

lemma set_asid_pool_valid_objs [wp]:
  "set_asid_pool p ap \<lbrace>valid_objs\<rbrace>"
  unfolding set_asid_pool_def
  by (wpsimp wp: set_object_valid_objs simp: valid_obj_def)

lemma is_aligned_pt:
  "\<lbrakk> pt_at pt_t pt s; pspace_aligned s \<rbrakk> \<Longrightarrow> is_aligned pt (pt_bits pt_t)"
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_alignedD)
  apply (simp add: pt_bits_def pageBits_def)
  done

lemma page_table_pte_atI_nicer:
  "\<lbrakk> pt_at pt_t p s; x \<le> mask (ptTranslationBits pt_t); pspace_aligned s \<rbrakk>
   \<Longrightarrow> pte_at pt_t (p + (x << pte_bits)) s"
  apply (frule (1) is_aligned_pt)
  apply (clarsimp simp: obj_at_def pte_at_def ptes_of_Some in_omonad)
  apply (rule conjI)
   apply (simp add: aligned_add_aligned is_aligned_shiftl_self bit_simps)
  apply (subgoal_tac "p = (p + (x << pte_bits) && ~~ mask (pt_bits pt_t))")
   apply (fastforce simp: bit_simps)
  apply (simp flip: table_base_plus)
  done

lemma page_table_pte_atI:
  "\<lbrakk> pt_at pt_t p s; x < 2^(pt_bits pt_t - pte_bits); pspace_aligned s \<rbrakk>
   \<Longrightarrow> pte_at pt_t (p + (x << pte_bits)) s"
  by (erule page_table_pte_atI_nicer; simp add: le_mask_iff_lt_2n[THEN iffD1] bit_simps)

lemma vs_lookup_table_extend:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, pt);
    pt_walk level bot_level pt vref (ptes_of s) = Some (bot_level, p);
    level \<le> max_pt_level\<rbrakk>
   \<Longrightarrow> vs_lookup_table bot_level asid vref s = Some (bot_level, p)"
  by (rule vs_lookup_split_Some[THEN iffD2] ; fastforce intro!: pt_walk_max_level)

lemma pt_walk_pt_at:
  "\<lbrakk> pt_walk level bot_level pt_ptr vptr (ptes_of s) = Some (level', p);
     vs_lookup_table level asid vptr s = Some (level, pt_ptr); level \<le> max_pt_level;
     vptr \<in> user_region; valid_vspace_objs s; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> pt_at level' p s"
  apply (drule pt_walk_level)
  apply (frule pt_walk_max_level)
  apply (drule vs_lookup_table_extend ; assumption?)
  apply (fastforce dest!: valid_vspace_objs_strongD simp: pt_at_eq)
  done

lemma vs_lookup_table_pt_at:
  "\<lbrakk> vs_lookup_table level asid vptr s = Some (level, pt_ptr); level \<le> max_pt_level;
     vptr \<in> user_region; valid_vspace_objs s; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> pt_at level pt_ptr s"
  apply (subst (asm) vs_lookup_split_max_pt_level_Some, clarsimp+)
  apply (drule (1) pt_walk_pt_at; simp)
  done

lemma pt_lookup_slot_from_level_pte_at:
  "\<lbrakk> pt_lookup_slot_from_level level bot_level pt_ptr vptr (ptes_of s) = Some (level', p);
     vs_lookup_table level asid vptr s = Some (level, pt_ptr); level \<le> max_pt_level;
     vptr \<in> user_region; valid_vspace_objs s; valid_asid_table s; pspace_aligned s \<rbrakk>
  \<Longrightarrow> pte_at level' p s"
  unfolding pt_lookup_slot_from_level_def
  apply (clarsimp simp add: oreturn_def obind_def split: option.splits)
  apply (rename_tac pt_ptr')
  apply (frule pt_walk_pt_at; assumption?)
  apply (frule (1) is_aligned_pt)
  using table_base_pt_slot_offset[where level=level']
  apply (clarsimp simp: pte_at_def is_aligned_pt_slot_offset_pte ptes_of_Some pt_at_eq)
  done

lemma set_pt_distinct [wp]:
  "set_pt p pt \<lbrace>pspace_distinct\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_distinct get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                split: kernel_object.splits arch_kernel_obj.splits)
  done

crunches store_pte
  for arch[wp]: "\<lambda>s. P (arch_state s)"
  and "distinct"[wp]: pspace_distinct

lemma store_pt_asid_pools_of[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (auto simp: obj_at_def opt_map_def elim!: rsubst[where P=P])
  done

lemma store_pte_asid_pools_of[wp]:
  "store_pte pt_t p pte \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding store_pte_def by wpsimp

lemma store_pte_vspace_at_asid:
  "store_pte pt_t p pte \<lbrace>vspace_at_asid asid pt\<rbrace>"
  unfolding vspace_at_asid_def by (wp vspace_for_asid_lift)

lemma ball_pt_range_pt_updI:
  "\<lbrakk> \<forall>pte\<in>pt_range pt. P pte; P pte' \<rbrakk> \<Longrightarrow> \<forall>pte\<in>pt_range (pt_upd pt i pte'). P pte"
  unfolding pt_range_def pt_apply_def pt_upd_def
  by (auto split: pt.splits)

(* To preserve valid_pt_range, we must not insert non-invalid PTEs into invalid mapping slots
   in top-level tables. *)
definition
  "valid_mapping_insert pt_t p pte \<equiv>
    pt_t = VSRootPT_T \<longrightarrow> ucast (table_index VSRootPT_T p) \<in> invalid_mapping_slots \<longrightarrow>
    pte = InvalidPTE"

lemma valid_mapping_insert_NormalPT_T[simp]:
  "valid_mapping_insert NormalPT_T p pte"
  by (simp add: valid_mapping_insert_def)

lemma valid_mapping_insert_InvalidPTE[simp]:
  "valid_mapping_insert pt_t p InvalidPTE"
  by (simp add: valid_mapping_insert_def)

lemma store_pte_valid_objs[wp]:
  "\<lbrace>(\<lambda>s. wellformed_pte pte \<and> valid_mapping_insert pt_t p pte) and valid_objs\<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: store_pte_def set_pt_def bind_assoc)
  apply (wpsimp simp_del: fun_upd_apply)
  apply (erule (1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_pt_range_def pt_upd_def valid_mapping_insert_def split: pt.splits)
  apply (rule ball_pt_range_pt_updI; simp)
  done

lemma set_pt_caps_of_state [wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_pt_def get_object_def bind_assoc set_object_def)
  apply (wpsimp)
  apply (subst caps_of_state_after_update, auto elim: obj_at_weakenE)
  done

lemma store_pte_aligned [wp]:
  "store_pte pt_t pt p \<lbrace>pspace_aligned\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp set_object_aligned get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_asid_pool_aligned [wp]:
  "set_asid_pool p ptr \<lbrace>pspace_aligned\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_aligned|wpc)+
  including unfold_objects
  apply clarsimp
  done

lemma set_asid_pool_distinct [wp]:
  "set_asid_pool p ptr \<lbrace>pspace_distinct\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_distinct|wpc)+
  including unfold_objects
  apply clarsimp
  done


lemma store_pte_valid_pte [wp]:
  "store_pte pt_t p pte \<lbrace>valid_pte level pt\<rbrace>"
  by (wp valid_pte_lift store_pte_typ_at)

lemma global_refs_kheap [simp]:
  "global_refs (kheap_update f s) = global_refs s"
  by (simp add: global_refs_def)


lemma set_pt_valid_objs:
  "\<lbrace>(\<lambda>s. valid_pt_range pt \<and> (\<forall>i. wellformed_pte (pt_apply pt i))) and valid_objs\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  unfolding set_pt_def
  by (wpsimp wp: get_object_wp set_object_valid_objs simp: valid_obj_def obj_at_def pt_range_def)

lemma set_pt_iflive:
  "set_pt p pt \<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp simp: set_pt_def live_def hyp_live_def arch_live_def wp: get_object_wp set_object_iflive)


lemma set_pt_zombies:
  "set_pt p pt \<lbrace>\<lambda>s. zombies_final s\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp wp: get_object_wp)


lemma set_pt_zombies_state_refs:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  unfolding set_pt_def set_object_def including unfold_objects
  apply wpsimp
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: state_refs_of_def split: option.splits)
  done

lemma set_pt_zombies_state_hyp_refs:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_hyp_refs_of_def split: option.splits)
  done

lemma set_pt_cdt:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_pt_def including unfold_objects by wpsimp


lemma set_pt_valid_mdb:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: set_pt_cdt valid_mdb_lift simp: set_pt_def set_object_def)

lemma set_pt_valid_idle:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_idle_lift simp: set_pt_def)

lemma set_pt_ifunsafe:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  including unfold_objects by (wpsimp simp: set_pt_def)

lemma set_pt_reply_caps:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)

lemma set_pt_reply_masters:
  "\<lbrace>valid_reply_masters\<rbrace>  set_pt p pt  \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)

crunches set_pt
  for global_ref[wp]: "\<lambda>s. P (global_refs s)"
  and idle[wp]: "\<lambda>s. P (idle_thread s)"
  and irq[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

lemma set_pt_valid_global:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)

lemma set_pt_vcpus_of[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_pt_def
  by (wp set_object_wp) (auto simp: opt_map_def obj_at_def elim!: rsubst[where P=P])

lemma set_pt_cur:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  apply (simp add: cur_tcb_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  done


lemma set_pt_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_pt p pt \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp get_object_wp set_object_aligned)
  apply (clarsimp simp: a_type_def obj_at_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  done


crunch interrupt_states[wp]: set_pt "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

lemma unique_table_caps_ptD:
  "\<lbrakk> cs p = Some cap; vs_cap_ref cap = None;
     cs p' = Some cap'; is_pt_cap cap; is_pt_cap cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps_2 cs\<rbrakk>
  \<Longrightarrow> p = p'"
  unfolding unique_table_caps_2_def by fastforce

lemma set_pt_table_caps[wp]:
  "\<lbrace>valid_table_caps and (\<lambda>s. valid_caps (caps_of_state s) s) and
    (\<lambda>s. (\<forall>slot pt_t asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap p pt_t asidopt))
                               \<longrightarrow> asidopt = None \<longrightarrow> pt = empty_pt pt_t)) \<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def set_pt_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (rename_tac ref slot)
  apply (subst (asm) caps_of_state_after_update[simplified fun_upd_apply[symmetric]])
   apply (clarsimp simp: obj_at_def)
  apply (drule_tac x=r in spec, erule allE, erule impE, fastforce)
  apply (clarsimp simp: opt_map_def fun_upd_apply split: option.splits)
  done

lemma store_pte_valid_table_caps:
  "\<lbrace> valid_table_caps and (\<lambda>s. valid_caps (caps_of_state s) s) and
     (\<lambda>s. (\<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base pt_t p) pt_t asidopt))
                           \<longrightarrow> asidopt = None \<longrightarrow> pte = InvalidPTE)) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>rv. valid_table_caps\<rbrace>"
  unfolding store_pte_def
  by wpsimp
     (fastforce simp: valid_table_caps_def pts_of_ko_at obj_at_def)

lemma set_object_caps_of_state:
  "\<lbrace>(\<lambda>s. \<not>tcb_at p s \<and> \<not>(\<exists>n. cap_table_at n p s)) and
    K ((\<forall>x y. obj \<noteq> CNode x y) \<and> (\<forall>x. obj \<noteq> TCB x)) and
    (\<lambda>s. P (caps_of_state s))\<rbrace>
   set_object p obj
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong)
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (simp add: caps_of_state_cte_wp_at obj_at_def is_cap_table_def
                   is_tcb_def)
  apply (auto simp: cte_wp_at_cases)
  done

lemma set_pt_aobjs_of:
  "\<lbrace>\<lambda>s. aobjs_of s p \<noteq> None \<longrightarrow> P ((aobjs_of s)(p \<mapsto> PageTable pt)) \<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (aobjs_of s)\<rbrace>"
  unfolding set_pt_def
  supply fun_upd_apply[simp del]
  by (wpsimp wp: set_object_wp)
     (simp add: obj_at_def opt_map_def)

lemma set_pt_asid_pool_caps[wp]:
  "set_pt p pt \<lbrace>valid_asid_pool_caps\<rbrace>"
  unfolding valid_asid_pool_caps_def
  by (rule hoare_lift_Pf[where f=caps_of_state]; wp)

lemma valid_global_refsD2:
  "\<lbrakk> caps_of_state s ptr = Some cap; valid_global_refs s \<rbrakk>
      \<Longrightarrow> global_refs s \<inter> cap_range cap = {}"
  by (cases ptr,
      simp add: valid_global_refs_def valid_refs_def
                cte_wp_at_caps_of_state)


lemma valid_global_refsD:
  "\<lbrakk> valid_global_refs s; cte_wp_at ((=) cap) ptr s;
         r \<in> global_refs s \<rbrakk>
        \<Longrightarrow> r \<notin> cap_range cap"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) valid_global_refsD2)
  apply fastforce
  done


lemma set_pt_global_objs [wp]:
  "\<lbrace>\<top>\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  unfolding valid_global_objs_def by wp


crunch v_ker_map[wp]: set_pt "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)

lemma set_pt_asid_map[wp]:
  "set_pt p pt \<lbrace>valid_asid_map\<rbrace>"
  by (wp valid_asid_map_lift_strong)

crunches store_pte
  for pred_tcb[wp]:  "\<lambda>s. Q (pred_tcb_at proj P t s)"
  and idle[wp]: "\<lambda>s. P (idle_thread s)"

(* not true for set_pt, but true for store_pte: *)
lemma store_pte_only_idle [wp]:
  "store_pte p pt_t pte \<lbrace>only_idle\<rbrace>"
  by (wp only_idle_lift)

lemma pts_of_upd_idem:
  "obj_ref \<noteq> pt_ptr \<Longrightarrow> pts_of (s\<lparr> kheap := (kheap s)(obj_ref := Some ko)\<rparr>) pt_ptr = pts_of s pt_ptr"
  unfolding pt_of_def
  by (clarsimp simp: opt_map_def split: option.splits)

lemma pt_walk_eqI:
  "\<lbrakk> \<forall>level' pt_ptr'.
       level < level'
       \<longrightarrow> pt_walk top_level level' pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts) = Some (level', pt_ptr')
       \<longrightarrow> pts' pt_ptr' = pts pt_ptr';
     is_aligned pt_ptr (pt_bits top_level); top_level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> pt_walk top_level level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts')
      = pt_walk top_level level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts)"
  apply (induct top_level arbitrary: pt_ptr; clarsimp)
  apply (subst pt_walk.simps)
  apply (subst (2) pt_walk.simps)
  apply clarsimp
  apply (rule obind_eqI)
   apply (simp (no_asm) add: level_pte_of_def)
   apply (fastforce simp: obind_def split: option.split)
  apply clarsimp
  apply (rename_tac pte)
  apply (drule_tac x="pptr_from_pte pte" in meta_spec)
  apply (erule meta_impE; (simp add: pptr_from_pte_aligned_pt_bits)?)
  apply clarsimp
  apply (prop_tac "is_aligned pt_ptr (pt_bits (level_type top_level)) \<and> pts' pt_ptr = pts pt_ptr")
   subgoal by simp
  apply (erule_tac x=level' in allE, simp)
  apply (erule_tac x=pt_ptr' in allE)
  apply (erule impE; assumption?)
  apply (subst pt_walk.simps)
  apply (prop_tac "level' < top_level")
   apply (fastforce dest!: pt_walk_max_level simp: le_less_trans)
  apply (fastforce simp: level_pte_of_def in_omonad if_option_eq)
  done

lemma valid_vspace_obj_valid_pte_upd:
  "\<lbrakk> valid_vspace_obj level (PageTable pt) s; valid_pte level pte s \<rbrakk>
   \<Longrightarrow> valid_vspace_obj level (PageTable (pt_upd pt idx pte)) s"
  using pt_range_upd[of pt idx pte]
  by (cases pt) auto

lemma pt_apply_empty[simp]:
  "pt_apply (empty_pt pt_t) idx = InvalidPTE"
  by (simp add: pt_apply_def empty_pt_def)

lemma pte_of_pt_slot_offset_of_empty_pt:
  "\<lbrakk> pts pt_ptr = Some (empty_pt (level_type level)); is_aligned pt_ptr (pt_bits (level_type level)) \<rbrakk>
   \<Longrightarrow> level_pte_of (level_type level) (pt_slot_offset level pt_ptr vref) pts = Some InvalidPTE"
  by (clarsimp simp: level_pte_of_def obind_def is_aligned_pt_slot_offset_pte split: option.split)

lemma pt_walk_non_empty_ptD:
  "\<lbrakk> pt_walk level bot_level pt_ptr vref (\<lambda>pt_t p. level_pte_of pt_t p pts) = Some (level', p);
     pts pt_ptr = Some pt; is_aligned pt_ptr (pt_bits level) \<rbrakk>
   \<Longrightarrow> (pt \<noteq> empty_pt (level_type level) \<or> (level' = level \<and> p = pt_ptr))"
  apply (subst (asm) pt_walk.simps)
  apply (case_tac "bot_level < level")
   apply (clarsimp simp: in_omonad)
   apply (prop_tac "v' = InvalidPTE")
    apply (drule_tac vref=vref and level=level in pte_of_pt_slot_offset_of_empty_pt, clarsimp+)
  done

lemma pt_walk_pt_upd_idem:
  "\<lbrakk> \<forall>level' pt_ptr'.
       level < level'
       \<longrightarrow> pt_walk top_level level' pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts) = Some (level', pt_ptr')
       \<longrightarrow> pt_ptr' \<noteq> obj_ref;
     is_aligned pt_ptr (pt_bits top_level); top_level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> pt_walk top_level level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p (pts(obj_ref := pt)))
      = pt_walk top_level level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts)"
  by (rule pt_walk_eqI; auto)

lemma pt_walk_upd_idem:
  "\<lbrakk> \<forall>level' pt_ptr'.
       level < level'
       \<longrightarrow> pt_walk top_level level' pt_ptr vptr (ptes_of s) = Some (level', pt_ptr')
       \<longrightarrow> pt_ptr' \<noteq> obj_ref;
     is_aligned pt_ptr (pt_bits top_level); top_level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> pt_walk top_level level pt_ptr vptr (ptes_of (s\<lparr>kheap := (kheap s)(obj_ref \<mapsto> ko)\<rparr>))
      = pt_walk top_level level pt_ptr vptr (ptes_of s)"
  by (rule pt_walk_eqI; simp split del: if_split)
     (clarsimp simp: opt_map_def split: option.splits)

lemma pt_walk_pt_None_updD:
  "\<lbrakk> pt_walk top_level level pt_ptr vref (\<lambda>pt_t p. level_pte_of pt_t p ((pts_of s)(p' := None))) =
        Some (level', table_ptr) \<rbrakk>
       \<Longrightarrow> pt_walk top_level level pt_ptr vref (ptes_of s) = Some (level', table_ptr)"
  apply (induct top_level arbitrary: pt_ptr, clarsimp)
  apply (subst pt_walk.simps)
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_splits)
  apply (erule disjE; clarsimp?)
   apply (rule_tac x=v' in exI; clarsimp)
   apply (subst (asm) (3) level_pte_of_def)
   apply (clarsimp simp: in_omonad split: if_splits)
   apply (simp (no_asm) add: ptes_of_def in_monad obind_def)
   apply (clarsimp split: option.splits simp: pts_of_ko_at obj_at_def)
  apply (drule meta_spec)
  apply (fastforce simp: level_pte_of_def in_omonad split: if_splits)
  done

lemma ptes_of_pt_None_updD:
  "\<lbrakk> level_pte_of pt_t p' ((pts_of s)(p := None)) = Some pte \<rbrakk>
   \<Longrightarrow> ptes_of s pt_t p' = Some pte"
  by (clarsimp simp: opt_map_def level_pte_of_def in_omonad if_option split: if_splits)

lemma vs_lookup_table_eqI:
  fixes s :: "'z::state_ext state"
  fixes s' :: "'z::state_ext state"
  shows
  "\<lbrakk> \<forall>level p. bot_level < level
               \<longrightarrow> vs_lookup_table level asid vref s = Some (level, p)
               \<longrightarrow> (if level \<le> max_pt_level
                   then pts_of s' p = pts_of s p
                   else asid_pools_of s' p = asid_pools_of s p);
     asid_table s' (asid_high_bits_of asid) = asid_table s (asid_high_bits_of asid);
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s \<rbrakk>
   \<Longrightarrow> vs_lookup_table bot_level asid vref s' = vs_lookup_table bot_level asid vref s"
  apply (case_tac "bot_level \<le> max_pt_level")
   prefer 2
   apply (clarsimp simp: asid_pool_level_eq[symmetric] vs_lookup_table_def in_omonad
                         pool_for_asid_def)
   apply (rule obind_eqI; fastforce simp: pool_for_asid_def)
  (* pt_walk case: *)
  apply (simp (no_asm) add: vs_lookup_table_def in_omonad)
  apply (rule obind_eqI_full; simp add: pool_for_asid_def)
  apply (rename_tac pool_ptr)
  apply (rule obind_eqI_full; clarsimp)
   apply (erule_tac x=asid_pool_level in allE)
   apply (fastforce simp: pool_for_asid_vs_lookup pool_for_asid_def vspace_for_pool_def obind_def
                          entry_for_pool_def order.not_eq_order_implies_strict
                    split: option.splits)
  apply (rename_tac root)
  apply (rule pt_walk_eqI; clarsimp)
   apply (frule pt_walk_max_level)
   apply (fastforce simp: vs_lookup_table_def in_omonad asid_pool_level_eq pool_for_asid_def)
  apply (rule vspace_for_pool_is_aligned; fastforce simp: pool_for_asid_def)
  done

lemma vs_lookup_table_upd_idem:
  "\<lbrakk> \<forall>level' p'.
       level < level'
       \<longrightarrow> vs_lookup_table  level' asid vref s = Some (level', p')
       \<longrightarrow> p' \<noteq> obj_ref;
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s \<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref (s\<lparr>kheap := (kheap s)(obj_ref \<mapsto> ko)\<rparr>)
      = vs_lookup_table level asid vref s"
  by (rule vs_lookup_table_eqI; simp split del: if_split)
     (clarsimp simp: opt_map_def split: option.splits)

lemma vs_lookup_table_Some_upd_idem:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, obj_ref);
     vref \<in> user_region; pspace_aligned s; pspace_distinct s; valid_vspace_objs s;
     valid_asid_table s \<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref (s\<lparr>kheap := (kheap s)(obj_ref \<mapsto> ko)\<rparr>)
      = vs_lookup_table level asid vref s"
  by (subst vs_lookup_table_upd_idem; simp?)
     (fastforce dest: no_loop_vs_lookup_table)

lemma ex_vs_lookup_upd_idem:
  "\<lbrakk> \<exists>\<rhd> (level, p) s;
     pspace_aligned s; pspace_distinct s; valid_vspace_objs s; valid_asid_table s;
     unique_table_refs s; valid_vs_lookup s; valid_caps (caps_of_state s) s \<rbrakk>
   \<Longrightarrow> \<exists>\<rhd> (level, p) (s\<lparr>kheap := (kheap s)(p \<mapsto> ko)\<rparr>) = \<exists>\<rhd> (level, p) s"
  apply (rule iffI; clarsimp)
  apply (rule_tac x=asid in exI)
  apply (rule_tac x=vref in exI)
  apply (subst vs_lookup_table_Some_upd_idem; fastforce)
  done

lemma pt_lookup_target_translate_address_upd_eq:
  "\<lbrakk> pt_lookup_target 0 pt_ptr vref ptes' = pt_lookup_target 0 pt_ptr vref ptes \<rbrakk>
   \<Longrightarrow> translate_address pt_ptr vref ptes' = translate_address pt_ptr vref ptes"
  unfolding translate_address_def
  by (simp add: obind_def split: option.splits)

lemma pt_lookup_target_slot_from_level_eq:
  "\<lbrakk> pt_lookup_slot_from_level max_pt_level level pt_ptr vref ptes'
     = pt_lookup_slot_from_level max_pt_level level pt_ptr vref ptes;
     \<And>level' slot. pt_lookup_slot_from_level max_pt_level level pt_ptr vref ptes = Some (level', slot)
                   \<Longrightarrow> (ptes' level' |> pte_ref) slot = (ptes level' |> pte_ref) slot \<rbrakk>
   \<Longrightarrow> pt_lookup_target level pt_ptr vref ptes' = pt_lookup_target level pt_ptr vref ptes"
  unfolding pt_lookup_target_def
  by (fastforce simp: obind_def opt_map_def split: option.splits)

lemma pt_walk_Some_finds_pt:
  "\<lbrakk> pt_walk top_level level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts) = Some (level, pt_ptr');
     level < top_level; is_aligned pt_ptr (pt_bits top_level) \<rbrakk>
   \<Longrightarrow> pts pt_ptr \<noteq> None"
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp add: in_omonad split: if_splits)
  apply (fastforce simp: is_PageTablePTE_def level_pte_of_def in_omonad split: if_splits)
  done

lemma pte_of_pt_slot_offset_upd_idem:
  "\<lbrakk> is_aligned pt_ptr (pt_bits pt_t); obj_ref \<noteq> pt_ptr; pt_t = level_type level \<rbrakk>
   \<Longrightarrow> level_pte_of pt_t (pt_slot_offset level pt_ptr vptr) (pts(obj_ref := pt'))
      = level_pte_of pt_t (pt_slot_offset level pt_ptr vptr) pts"
  unfolding level_pte_of_def
  by (rule obind_eqI; clarsimp simp: in_omonad)+

lemma pt_lookup_target_pt_eqI:
  "\<lbrakk> \<forall>level' pt_ptr'.
       pt_walk max_pt_level level' pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts) = Some (level', pt_ptr')
       \<longrightarrow> pts' pt_ptr' = pts pt_ptr';
     is_aligned pt_ptr (pt_bits (level_type max_pt_level)); level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> pt_lookup_target level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts')
      = pt_lookup_target level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts)"
  apply (simp (no_asm) add: pt_lookup_target_def pt_lookup_slot_from_level_def obind_assoc)
  apply (subgoal_tac "pt_walk max_pt_level level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts')
                      = pt_walk max_pt_level level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts)")
   prefer 2
   apply (rule pt_walk_eqI; assumption?)
    apply (intro allI impI)
    apply (erule_tac x=level' in allE)
    apply fastforce
   apply simp
  apply (rule obind_eqI, assumption)
  apply (rule obind_eqI; clarsimp)
  apply (rule obind_eqI; clarsimp)
   apply (rename_tac level'' pt_ptr'')
   apply (drule sym)
   apply (frule pt_walk_level)
   apply (erule_tac x=level'' in allE)
   apply (erule_tac x=pt_ptr'' in allE)
   apply clarsimp
   apply (subst level_pte_of_def)+
   apply (clarsimp simp: obind_def pt_walk_is_aligned split: option.splits)
  apply (rule obind_eqI; clarsimp)
  done

lemma pt_lookup_target_pt_upd_eq:
  "\<lbrakk> \<forall>level' pt_ptr'.
       pt_walk max_pt_level level' pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts) = Some (level', pt_ptr')
       \<longrightarrow> pt_ptr' \<noteq> obj_ref;
     is_aligned pt_ptr (pt_bits max_pt_level); level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> pt_lookup_target level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p (pts(obj_ref := pt')))
      = pt_lookup_target level pt_ptr vptr (\<lambda>pt_t p. level_pte_of pt_t p pts)"
  by (rule pt_lookup_target_pt_eqI; clarsimp)

lemma kheap_pt_upd_simp[simp]:
  "((kheap s)(p \<mapsto> ArchObj (PageTable pt)) |> aobj_of |> pt_of)
   = (kheap s |> aobj_of |> pt_of)(p \<mapsto> pt)"
  unfolding aobj_of_def opt_map_def
  by (auto split: kernel_object.split)

lemma arm_global_vspace_aligned[simp]:
  "\<lbrakk> pspace_aligned s ; valid_global_arch_objs s \<rbrakk>
   \<Longrightarrow> is_aligned (global_pt s) (pt_bits VSRootPT_T)"
  apply (clarsimp simp add: valid_global_arch_objs_def)
  apply (rule is_aligned_pt; assumption?)
  done

lemma global_pt_in_global_refs[simp]:
  "global_pt s \<in> global_refs s"
  unfolding global_refs_def by fastforce

lemma kernel_regionsI:
  "p \<in> kernel_window s \<Longrightarrow> p \<in> kernel_regions s"
  "p \<in> kernel_device_window s \<Longrightarrow> p \<in> kernel_regions s"
  unfolding kernel_regions_def
  by auto

lemma set_pt_valid_global_vspace_mappings[wp]:
  "\<lbrace>\<top>\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_global_vspace_mappings\<rbrace>"
  unfolding valid_global_vspace_mappings_def by wp

lemma store_pte_valid_global_vspace_mappings:
  "\<lbrace>\<top>\<rbrace> store_pte pt_t p pte \<lbrace>\<lambda>_. valid_global_vspace_mappings\<rbrace>"
  unfolding valid_global_vspace_mappings_def by wp

lemma set_pt_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_pt_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_pspace_respects_device_region get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_pt_caps_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_pt_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_cap_refs_respects_device_region get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_pt_valid_ioc[wp]:
  "set_pt p pt \<lbrace>valid_ioc\<rbrace>"
  unfolding set_pt_def
  by (wpsimp wp: set_object_wp_strong)
     (fastforce simp: valid_ioc_def cte_wp_at_cases obj_at_def)

lemma valid_machine_stateE:
  assumes vm: "valid_machine_state s"
  assumes e: "\<lbrakk>in_user_frame p s \<or> underlying_memory (machine_state s) p = 0 \<rbrakk> \<Longrightarrow> E"
  shows E
  using vm by (auto simp: valid_machine_state_def intro: e)

lemma in_user_frame_same_type_upd:
  "\<lbrakk>typ_at type p s; type = a_type obj; in_user_frame q s\<rbrakk>
    \<Longrightarrow> in_user_frame q (s\<lparr>kheap := (kheap s)(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: in_user_frame_def obj_at_def)
  apply (rule_tac x=sz in exI)
  apply (auto simp: a_type_simps)
  done

lemma in_device_frame_same_type_upd:
  "\<lbrakk>typ_at type p s; type = a_type obj ; in_device_frame q s\<rbrakk>
    \<Longrightarrow> in_device_frame q (s\<lparr>kheap := (kheap s)(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: in_device_frame_def obj_at_def)
  apply (rule_tac x=sz in exI)
  apply (auto simp: a_type_simps)
  done

lemma store_word_offs_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> store_word_offs a x w \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)

lemma as_user_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> as_user t m \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)

crunch obj_at[wp]: load_word_offs "\<lambda>s. P (obj_at Q p s)"

lemma load_word_offs_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> load_word_offs a x \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma valid_machine_state_heap_updI:
  "\<lbrakk> valid_machine_state s; typ_at type p s; a_type obj = type \<rbrakk>
   \<Longrightarrow> valid_machine_state (s\<lparr>kheap := (kheap s)(p \<mapsto> obj)\<rparr>)"
  by (fastforce simp: valid_machine_state_def
                intro: in_user_frame_same_type_upd
                elim: valid_machine_stateE)

lemma set_pt_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (erule valid_machine_state_heap_updI)
   apply (fastforce simp: obj_at_def a_type_def
                   split: kernel_object.splits arch_kernel_obj.splits)+
  done

crunch valid_irq_states[wp]: set_pt "valid_irq_states"
  (wp: crunch_wps)


(* FIXME: move to ArchInvariants_A *)
lemma valid_asid_table_ran:
  "valid_asid_table s \<Longrightarrow> \<forall>p\<in>ran (asid_table s). asid_pool_at p s"
  unfolding invs_def valid_state_def valid_arch_state_def valid_asid_table_def
  by (fastforce simp: opt_map_def obj_at_def split: option.splits)

lemmas invs_ran_asid_table = invs_valid_asid_table[THEN valid_asid_table_ran]


lemma set_asid_pool_iflive [wp]:
  "set_asid_pool p ap \<lbrace>if_live_then_nonz_cap\<rbrace>"
  unfolding set_asid_pool_def
  by (wp set_object_iflive)
     (clarsimp simp: obj_at_def live_def hyp_live_def arch_live_def in_omonad)

lemma set_asid_pool_zombies [wp]:
  "set_asid_pool p ap \<lbrace>zombies_final\<rbrace>"
  unfolding set_asid_pool_def
  by (wp set_object_zombies)
     (clarsimp simp: obj_at_def in_omonad)

lemma set_asid_pool_zombies_state_refs [wp]:
  "set_asid_pool p ap \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_refs_of_def split: option.splits)
  done

lemma set_asid_pool_zombies_state_hyp_refs [wp]:
  "set_asid_pool p ap \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_asid_pool_def wp: set_object_wp)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_hyp_refs_of_def in_omonad)
  done

lemma set_asid_pool_cdt [wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by wpsimp

lemma set_asid_pool_caps_of_state [wp]:
  "set_asid_pool p ap \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  unfolding set_asid_pool_def
  by (wpsimp simp: in_omonad wp: set_object_wp)
     (subst cte_wp_caps_of_lift, auto simp: cte_wp_at_cases)

lemma set_asid_pool_valid_mdb [wp]:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_mdb_lift simp: set_asid_pool_def set_object_def)


lemma set_asid_pool_valid_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_idle_lift simp: set_asid_pool_def)


lemma set_asid_pool_ifunsafe [wp]:
  "set_asid_pool p ap \<lbrace>if_unsafe_then_cap\<rbrace>"
  including unfold_objects
  by (wpsimp simp: set_asid_pool_def)


lemma set_asid_pool_reply_caps [wp]:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)


lemma set_asid_pool_reply_masters [wp]:
  "\<lbrace>valid_reply_masters\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)

crunches set_asid_pool
  for global_ref[wp]: "\<lambda>s. P (global_refs s)"
  and idle[wp]: "\<lambda>s. P (idle_thread s)"
  and irq[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and valid_irq_states[wp]: "valid_irq_states"
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

lemma set_asid_pool_valid_global [wp]:
  "set_asid_pool p ap \<lbrace>valid_global_refs\<rbrace>"
  by (wp valid_global_refs_cte_lift)

lemma vs_lookup_table_unreachable_upd_idem:
  "\<lbrakk> \<forall>level. vs_lookup_table level asid vref s \<noteq> Some (level, obj_ref);
     vref \<in> user_region; pspace_aligned s; valid_vspace_objs s; valid_asid_table s \<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref (s\<lparr>kheap := (kheap s)(obj_ref \<mapsto> ko)\<rparr>)
      = vs_lookup_table level asid vref s"
  apply (subst vs_lookup_table_upd_idem; fastforce)
  done

lemma vs_lookup_table_unreachable_upd_idem':
  "\<lbrakk> \<not>(\<exists>level. \<exists>\<rhd> (level, obj_ref) s);
     vref \<in> user_region; pspace_aligned s; valid_vspace_objs s; valid_asid_table s \<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref (s\<lparr>kheap := (kheap s)(obj_ref \<mapsto> ko)\<rparr>)
      = vs_lookup_table level asid vref s"
  by (rule vs_lookup_table_unreachable_upd_idem; fastforce)

lemma vs_lookup_target_unreachable_upd_idem:
  "\<lbrakk> \<forall>level. vs_lookup_table level asid vref s \<noteq> Some (level, obj_ref);
     vref \<in> user_region; pspace_aligned s; valid_vspace_objs s; valid_asid_table s \<rbrakk>
   \<Longrightarrow> vs_lookup_target level asid vref (s\<lparr>kheap := (kheap s)(obj_ref \<mapsto> ko)\<rparr>)
      = vs_lookup_target level asid vref s"
  supply fun_upd_apply[simp del]
  apply (clarsimp simp: vs_lookup_target_def vs_lookup_slot_def obind_assoc)
  apply (rule obind_eqI_full)
   apply (subst vs_lookup_table_upd_idem; fastforce)
  apply (clarsimp split del: if_split)
  apply (rename_tac level' p)
  apply (rule obind_eqI, fastforce)
  apply (clarsimp split del: if_split)
  apply (rule obind_eqI[rotated], fastforce)
  apply (clarsimp split: if_splits)
   (* level' = asid_pool_level *)
   apply (rename_tac pool_ptr)
   apply (drule vs_lookup_level, drule vs_lookup_level)
   apply (clarsimp simp: pool_for_asid_vs_lookup vspace_for_pool_def entry_for_pool_def in_omonad)
   apply (rule obind_eqI[rotated], fastforce)+
   apply (case_tac "pool_ptr = obj_ref"; clarsimp)
    apply (erule_tac x=asid_pool_level in allE)
    apply (fastforce simp: pool_for_asid_vs_lookup)
   apply (fastforce simp: fun_upd_def opt_map_def split: option.splits)
  (* level' \<le> max_pt_level *)
  apply (rule conjI, clarsimp)
  apply (rename_tac pt_ptr level')
   apply (case_tac "pt_ptr = obj_ref")
    apply (fastforce dest: vs_lookup_level)
   apply (rule pte_refs_of_eqI, rule level_ptes_of_eqI)
   apply (prop_tac "is_aligned pt_ptr (pt_bits (level_type level'))")
    apply (erule vs_lookup_table_is_aligned; fastforce)
   apply (clarsimp simp: fun_upd_def opt_map_def split: option.splits)
  done

lemma vs_lookup_target_unreachable_upd_idem':
  "\<lbrakk> \<not>(\<exists>level. \<exists>\<rhd> (level, obj_ref) s);
     vref \<in> user_region; pspace_aligned s; valid_vspace_objs s; valid_asid_table s \<rbrakk>
   \<Longrightarrow> vs_lookup_target level asid vref (s\<lparr>kheap := (kheap s)(obj_ref \<mapsto> ko)\<rparr>)
      = vs_lookup_target level asid vref s"
   by (rule vs_lookup_target_unreachable_upd_idem; fastforce)

lemma vs_lookup_table_fun_upd_deep_idem:
  "\<lbrakk> vs_lookup_table level asid vref (s\<lparr>kheap := (kheap s)(p \<mapsto> ko)\<rparr>) = Some (level, p');
     vs_lookup_table level' asid vref s = Some (level', p);
     level' \<le> level; vref \<in> user_region;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s; pspace_distinct s \<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref s = Some (level, p')"
  apply (case_tac "level=asid_pool_level")
   apply (simp add: pool_for_asid_vs_lookup pool_for_asid_def)
  apply clarsimp
  apply (subst (asm) vs_lookup_table_upd_idem; simp?)
  apply clarsimp
  apply (drule (1) no_loop_vs_lookup_table; simp?)
  done

lemma set_asid_pool_vspace_objs_unmap':
  "\<lbrace>valid_vspace_objs and
    (\<lambda>s. (\<exists>\<rhd> (asid_pool_level, p) s \<longrightarrow> valid_vspace_obj asid_pool_level (ASIDPool ap) s)) and
    (\<lambda>s. \<forall>ap'. asid_pools_of s p = Some ap' \<longrightarrow> graph_of ap \<subseteq> graph_of ap') and
    valid_asid_table and pspace_aligned \<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def set_asid_pool_def
  supply fun_upd_apply[simp del]
  apply (wp set_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac pt_ptr ao)
  apply (subgoal_tac "vs_lookup_table bot_level asid vref s = Some (level, pt_ptr)")
   apply (prop_tac "valid_vspace_objs s", fastforce simp: valid_vspace_objs_def)
   apply (erule_tac x=bot_level in allE)
   apply (erule_tac x=asid in allE)
   apply (erule_tac x=vref in allE)
   apply clarsimp
   apply (case_tac "level = asid_pool_level")
    apply (clarsimp simp: aobjs_of_ako_at_Some obj_at_def fun_upd_apply)
    apply (clarsimp split: if_splits)
     (* pt_ptr = p *)
     apply (drule vs_lookup_level, drule vs_lookup_level)
     apply (fastforce simp: obj_at_def fun_upd_apply in_omonad)
    (* pt_ptr \<noteq> p *)
    apply (clarsimp simp: in_omonad)
    apply (erule (1) valid_vspace_obj_same_type, simp)
   (* level \<le> max_pt_level *)
   apply clarsimp
   apply (drule vs_lookup_level, drule vs_lookup_level)
   apply (drule (5) vs_lookup_table_pt_at)
   apply (case_tac "pt_ptr = p"; simp add: aobjs_of_ako_at_Some)
    apply (clarsimp simp: aobjs_of_ako_at_Some obj_at_def fun_upd_apply fun_upd_def in_omonad)
   apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (clarsimp simp: aobjs_of_ako_at_Some obj_at_def fun_upd_apply in_omonad
                   simp del: valid_vspace_obj.simps)
   apply (erule (1) valid_vspace_obj_same_type, simp)
  apply (case_tac "bot_level = asid_pool_level")
   apply (clarsimp simp: pool_for_asid_vs_lookup pool_for_asid_def)
  apply (clarsimp simp: vs_lookup_table_def in_omonad asid_pool_level_neq[THEN iffD2] pool_for_asid_def)
  apply (drule pt_walk_pt_None_updD)
  apply (rename_tac pool_ptr root)
  apply (clarsimp simp: vspace_for_pool_def in_omonad fun_upd_apply entry_for_pool_def)
  apply (case_tac "pool_ptr = p"; clarsimp simp: asid_pools_of_ko_at obj_at_def)
  by (fastforce elim: graph_of_SomeD)

lemma set_asid_pool_vspace_objs_unmap:
  "\<lbrace>valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p and
    valid_asid_table and pspace_aligned\<rbrace>
  set_asid_pool p (ap (asid_low := None))  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (wp set_asid_pool_vspace_objs_unmap')
  apply (clarsimp simp: in_omonad obj_at_def graph_of_None_update)
  apply (drule valid_vspace_objsD, assumption, assumption, simp add: obj_at_def in_opt_map_eq)
  by (auto simp: obj_at_def ran_def split: if_split_asm)

lemma set_asid_pool_table_caps[wp]:
  "\<lbrace>valid_table_caps\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  apply (simp add: valid_table_caps_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  done

lemma vs_lookup_target_asid_pool_levelI:
  "\<lbrakk> pool_for_asid asid s = Some pool; ako_at (ASIDPool ap) pool s;
     ap (asid_low_bits_of asid) = Some ape; pt_ptr = ap_vspace ape \<rbrakk>
   \<Longrightarrow> vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level, pt_ptr)"
  by (fastforce simp: vs_lookup_target_def obj_at_def pool_for_asid_vs_lookup vspace_for_pool_def
                      entry_for_pool_def vs_lookup_slot_def in_omonad)

lemma vs_lookup_target_pt_levelI:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, pt_ptr);
     pte_refs_of level (pt_slot_offset level pt_ptr vref) s = Some target;
     level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> vs_lookup_target level asid vref s = Some (level, target)"
  by (clarsimp simp: vs_lookup_target_def in_omonad vs_lookup_slot_def asid_pool_level_neq[THEN iffD2])

lemma vs_lookup_target_asid_pool_level_upd_helper:
  "\<lbrakk> graph_of ap \<subseteq> graph_of ap'; kheap s p = Some (ArchObj (ASIDPool ap')); vref \<in> user_region;
     vspace_for_pool pool_ptr asid ((asid_pools_of s)(p \<mapsto> ap)) = Some pt_ptr;
     pool_for_asid asid (s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj (ASIDPool ap))\<rparr>) = Some pool_ptr\<rbrakk>
   \<Longrightarrow> vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level, pt_ptr)"
  apply (clarsimp simp: pool_for_asid_vs_lookup vspace_for_pool_def entry_for_pool_def in_omonad)
  apply (clarsimp split: if_splits)
   apply (rule vs_lookup_target_asid_pool_levelI)
   apply (fastforce simp: pool_for_asid_def obj_at_def dest: graph_of_SomeD)+
  apply (rule vs_lookup_target_asid_pool_levelI
         ; fastforce simp: pool_for_asid_def obj_at_def vs_lookup_target_def in_omonad)
  done

lemma vs_lookup_target_None_upd_helper:
  "\<lbrakk> vs_lookup_table level asid vref (s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj (ASIDPool ap))\<rparr>) =
        Some (level, table_ptr);
     ((\<lambda>pa. level_pte_of (level_type level) pa ((pts_of s)(p := None))) |> pte_ref)
       (pt_slot_offset level table_ptr vref)
       = Some target;
     kheap s p = Some (ArchObj (ASIDPool ap')); graph_of ap \<subseteq> graph_of ap';
     level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> vs_lookup_target level asid vref s = Some (level, target)"
  apply (subst (asm) vs_lookup_split_max_pt_level_Some, assumption)
  apply (clarsimp dest!: vs_lookup_max_pt_levelD)
  apply (clarsimp simp: vs_lookup_target_def in_omonad vs_lookup_slot_def)
  apply (clarsimp simp: asid_pool_level_neq[THEN iffD2])
  apply (rule_tac x="pt_slot_offset level table_ptr vref" in exI)
  apply (rule conjI[rotated], fastforce dest: ptes_of_pt_None_updD)
  apply (rule_tac x=level in exI)
  apply (clarsimp simp: asid_pool_level_neq[THEN iffD2])
  apply (subst vs_lookup_split_max_pt_level_Some, assumption)
  apply (rule_tac x=table_ptr in exI)
  apply simp
  apply (rule_tac x=pt in exI)
  apply (rule conjI)
   apply (rule_tac pool_ptr=pool_ptr in vs_lookup_max_pt_levelI)
    apply (fastforce simp: pool_for_asid_def)
   apply (fastforce simp: vspace_for_pool_def in_omonad entry_for_pool_def
                    dest: graph_of_SomeD pt_walk_pt_None_updD
                    split: if_splits)+
  done

lemma set_asid_pool_vs_lookup_unmap':
  "\<lbrace> valid_vs_lookup and
     obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p \<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  supply fun_upd_apply[simp del]
  apply (simp add: valid_vs_lookup_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac target)
  (* unfold vs_lookup_target on updated state and clean up *)
  apply (subst (asm) (2) vs_lookup_target_def)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac slot_ptr)
  apply (clarsimp simp: vs_lookup_slot_def)
  apply (rename_tac level' table_ptr)
  apply (drule_tac bot_level=bot_level in vs_lookup_level)
  apply (prop_tac "level' = level", fastforce split: if_splits)
  apply clarsimp

  apply (case_tac "level = asid_pool_level")
   apply (clarsimp simp: pool_for_asid_vs_lookup)
   apply (rename_tac root pool_ptr)
   apply (subgoal_tac "vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level, root)"
          , fastforce)
   apply (erule vs_lookup_target_asid_pool_level_upd_helper; simp)
  apply clarsimp
  apply (subgoal_tac "vs_lookup_target level asid vref s = Some (level, target)", fastforce)
  apply (erule vs_lookup_target_None_upd_helper; simp)
  done

lemma set_asid_pool_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and ako_at (ASIDPool ap) p\<rbrace>
   set_asid_pool p (ap (asid_low := None))
   \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  by (wpsimp wp: set_asid_pool_vs_lookup_unmap' simp: obj_at_def graph_of_None_update)

lemma valid_pte_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pte level pte s = valid_pte level pte s'"
  by (case_tac pte, auto simp add: data_at_def)

lemma set_asid_pool_global_objs [wp]:
  "set_asid_pool p ap \<lbrace>valid_global_objs\<rbrace>"
  by (clarsimp simp: valid_global_objs_def) wp

crunch v_ker_map[wp]: set_asid_pool "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)

lemmas set_asid_pool_vspace_objs_unmap_single = set_asid_pool_vspace_objs_unmap

lemma set_asid_pool_only_idle [wp]:
  "set_asid_pool p ap \<lbrace>only_idle\<rbrace>"
  by (wp only_idle_lift set_asid_pool_typ_at)

lemma set_asid_pool_equal_mappings[wp]:
  "\<lbrace>\<top>\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. equal_kernel_mappings\<rbrace>"
  unfolding equal_kernel_mappings_def by wp

lemma translate_address_asid_pool_upd:
  "pts_of s p = None
   \<Longrightarrow> translate_address pt_ptr vref
        (\<lambda>pt_t pa. level_pte_of pt_t pa ((kheap s)(p \<mapsto> ArchObj (ASIDPool ap)) |> aobj_of |> pt_of))
      = translate_address pt_ptr vref (ptes_of s)"
  by simp

lemma ko_atasid_pool_pts_None:
  "ako_at (ASIDPool pool) p s \<Longrightarrow> pts_of s p = None"
  by (clarsimp simp: opt_map_def obj_at_def split: option.splits)

lemma set_asid_pool_valid_global_vspace_mappings[wp]:
  "\<lbrace>\<top>\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_global_vspace_mappings\<rbrace>"
  unfolding valid_global_vspace_mappings_def by wp

lemma set_asid_pool_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  including unfold_objects_asm
  by (clarsimp simp: a_type_def)

lemma set_asid_pool_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_pspace_respects_device_region get_object_wp)
  including unfold_objects_asm
  by (clarsimp simp: a_type_def)


lemma set_asid_pool_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_cap_refs_in_kernel_window)
  including unfold_objects_asm
  by clarsimp

lemma set_asid_pool_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_cap_refs_respects_device_region get_object_wp)
  including unfold_objects_asm
  by clarsimp


lemma set_asid_pool_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_ioc_no_caps get_object_inv)
  including unfold_objects
  by (clarsimp simp: valid_def get_object_def simpler_gets_def assert_def
          return_def fail_def bind_def
          a_type_simps is_tcb is_cap_table)


lemma set_asid_pool_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_asid_pool p S \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (erule valid_machine_state_heap_updI)
  apply (fastforce simp: a_type_def obj_at_def
                  split: kernel_object.splits arch_kernel_obj.splits)+
  done

(* FIXME: example of crunch not being helpful *)
lemma set_asid_pool_valid_asid_pool_caps[wp]:
  "set_asid_pool p ap \<lbrace>valid_asid_pool_caps\<rbrace>"
  unfolding valid_asid_pool_caps_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')

lemma set_asid_pool_None_valid_asid_map[wp]:
  "\<lbrace> valid_asid_map and (\<lambda>s. asid_pools_of s p = Some ap) \<rbrace>
   set_asid_pool p (ap (asid_low := None))
   \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  unfolding valid_asid_map_def entry_for_asid_def
  apply (clarsimp simp: obind_None_eq pool_for_asid_def)
  apply (wp hoare_vcg_disj_lift hoare_vcg_ex_lift get_object_wp)
  apply (fastforce simp: entry_for_pool_def obind_None_eq in_omonad split: if_split_asm)
  done

lemma set_asid_pool_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. asid_pools_of s p = Some ap) and
    (\<lambda>s. \<exists>asid_high. asid_table s asid_high = Some p \<and>
                     vmid_for_asid s (asid_of asid_high asid_low) = None)\<rbrace>
   set_asid_pool p (ap (asid_low := None))
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def
                   valid_arch_caps_def)
  apply (wp valid_irq_node_typ set_asid_pool_typ_at
            set_asid_pool_vspace_objs_unmap
            valid_irq_handlers_lift
            set_asid_pool_vs_lookup_unmap
            set_asid_pool_None_valid_arch)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def in_omonad valid_arch_state_def)
  done

lemmas set_asid_pool_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF set_asid_pool_caps_of_state]


lemma mdb_cte_at_set_asid_pool[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>
   set_asid_pool y pool
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
  done

lemma valid_slots_typ_at:
  assumes x: "\<And>T p. f \<lbrace>typ_at (AArch T) p\<rbrace>"
  assumes y: "\<And>P. f \<lbrace> \<lambda>s. P (vs_lookup s) \<rbrace>"
  shows "\<lbrace>valid_slots m\<rbrace> f \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  unfolding valid_slots_def
  apply (cases m; clarsimp)
  apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift' assms
                    valid_pte_lift pte_at_typ_lift)
  apply fastforce
  done

lemma pool_for_asid_arch_update[simp]:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s) \<Longrightarrow>
  pool_for_asid asid (arch_state_update f s) = pool_for_asid asid s"
  by (simp add: pool_for_asid_def obind_def split: option.splits)

lemma vs_lookup_table_arch_update[simp]:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_table level asid vref (arch_state_update f s) = vs_lookup_table level asid vref s"
  by (simp add: vs_lookup_table_def obind_def split: option.splits)

lemma vs_lookup_arch_update[simp]:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup (arch_state_update f s) = vs_lookup s"
  by (rule ext)+ simp

lemma vs_lookup_slot_arch_update[simp]:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_slot level asid vref (arch_state_update f s) = vs_lookup_slot level asid vref s"
  by (simp add: vs_lookup_slot_def obind_def split: option.splits)

lemma vs_lookup_target_arch_update[simp]:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_target level asid vref (arch_state_update f s) = vs_lookup_target level asid vref  s"
  by (simp add: vs_lookup_target_def obind_def split: option.splits)

lemma vs_lookup_pages_arch_update[simp]:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_pages (arch_state_update f s) = vs_lookup_pages s"
  by (rule ext)+ simp

lemma unique_table_caps_ptE:
  "\<lbrakk> unique_table_caps_2 cs; cs p = Some cap; vs_cap_ref cap = None;
     cs p' = Some cap'; vs_cap_ref cap' = Some v; is_pt_cap cap;
     is_pt_cap cap'; obj_refs cap' = obj_refs cap \<rbrakk>
       \<Longrightarrow> P"
  apply (frule(6) unique_table_caps_ptD[where cs=cs])
  apply simp
  done

lemma set_pt_mappings[wp]:
  "\<lbrace>\<top>\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_kernel_mappings\<rbrace>"
  by (simp add: valid_kernel_mappings_def) wp

lemma set_pt_equal_kernel_mappings:
  "\<lbrace>\<top>\<rbrace> set_pt p pt \<lbrace>\<lambda>_. equal_kernel_mappings\<rbrace>"
  unfolding equal_kernel_mappings_def by wp

lemma store_pte_equal_kernel_mappings_no_kernel_slots:
  "\<lbrace>\<top>\<rbrace> store_pte pt_t p pte \<lbrace>\<lambda>_. equal_kernel_mappings\<rbrace>"
  unfolding equal_kernel_mappings_def by wp

lemma store_pte_state_refs_of[wp]:
  "store_pte pt_t ptr val \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wp get_object_wp set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule ext, clarsimp simp: state_refs_of_def obj_at_def)
  done

lemma store_pte_state_hyp_refs_of[wp]:
  "store_pte pt_t ptr val \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wp get_object_wp set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule ext, clarsimp simp: state_hyp_refs_of_def obj_at_def)
  done

lemma asid_pools_of_pt_None_upd_idem:
  "pt_at pt_t p s \<Longrightarrow> (asid_pools_of s)(p := None) = (asid_pools_of s)"
  by (rule ext)
     (clarsimp simp: opt_map_def obj_at_def )

lemma store_pte_valid_asid_table[wp]:
  "store_pte pt_t p pte \<lbrace>valid_asid_table\<rbrace>"
  unfolding valid_asid_table_def  by (wp_pre, wps, wp, simp)

lemma set_pt_vcpus[wp]:
  "set_pt pt p \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  unfolding set_pt_def
  by (wpsimp wp: set_object_wp)
     (fastforce simp: opt_map_def obj_at_def split: option.splits elim: rsubst[where P=P])

crunches store_pte
  for iflive[wp]: if_live_then_nonz_cap
  and zombies_final[wp]: zombies_final
  and valid_mdb[wp]: valid_mdb
  and valid_ioc[wp]: valid_ioc
  and valid_idle[wp]: valid_idle
  and if_unsafe_then_cap[wp]: if_unsafe_then_cap
  and valid_reply_caps[wp]: valid_reply_caps
  and valid_reply_masters[wp]: valid_reply_masters
  and valid_global_refs[wp]: valid_global_refs
  and valid_irq_handlers[wp]: valid_irq_handlers
  and valid_irq_states[wp]: valid_irq_states
  and valid_machine_state[wp]: valid_machine_state
  and valid_global_objs[wp]: valid_global_objs
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and valid_asid_map[wp]: valid_asid_map
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and cur_tcb[wp]: cur_tcb
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and valid_irq_node[wp]: valid_irq_node
  and vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"
  and cur_vcpu[wp]: cur_vcpu
  and vmid_inv[wp]: vmid_inv
  (wp: set_pt_zombies set_pt_ifunsafe set_pt_reply_caps set_pt_reply_masters
       set_pt_valid_global valid_irq_node_typ valid_irq_handlers_lift set_pt_cur
       vmid_inv_ap_lift cur_vcpu_typ_lift)

lemma store_pte_valid_global_arch_objs[wp]:
  "store_pte pt_t p pte \<lbrace> valid_global_arch_objs \<rbrace>"
  unfolding store_pte_def set_pt_def
  by (wpsimp wp: set_object_wp)
     (clarsimp simp: valid_global_arch_objs_def obj_at_def)

lemma store_pte_unique_table_refs[wp]:
  "store_pte pt_t p pte \<lbrace> unique_table_refs \<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: unique_table_refs_def)
  apply (subst (asm) caps_of_state_after_update[folded fun_upd_def], simp add: obj_at_def)+
  apply blast
  done

lemma store_pte_unique_table_caps[wp]:
  "store_pte pt_t p pte \<lbrace> unique_table_caps \<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: unique_table_caps_def)
  apply (subst (asm) caps_of_state_after_update[folded fun_upd_def], fastforce simp: obj_at_def)+
  apply blast
  done

lemma store_pte_valid_asid_pool_caps[wp]:
  "store_pte pt_t p pte \<lbrace> valid_asid_pool_caps \<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (subst caps_of_state_after_update[folded fun_upd_def], fastforce simp: obj_at_def)+
  apply assumption
  done

lemma ptes_of_pts_of_pt_type:
  "\<lbrakk> ptes_of s pt_t p = Some pte'; pts_of s (table_base pt_t p) = Some pt \<rbrakk> \<Longrightarrow>
   pt_type pt = pt_t"
  by (simp add: level_pte_of_def in_omonad if_option)

lemma store_pte_PagePTE_valid_vspace_objs:
  "\<lbrace> valid_vspace_objs and pspace_aligned and pspace_distinct and valid_asid_table
     and K (pte = PagePTE base_ptr is_small attr rights)
     and (\<lambda>s. \<forall>level. \<exists>\<rhd> (level, table_base pt_t p) s \<longrightarrow> level_type level = pt_t \<longrightarrow>
                      valid_pte level pte s) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def
  supply valid_pte.simps[simp del]
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_imp_lift hoare_vcg_imp_lift' valid_vspace_obj_lift
                    store_pte_non_PageTablePTE_vs_lookup store_pte_not_ao)
  apply (prop_tac "valid_vspace_objs s", simp add: valid_vspace_objs_def)
  apply (rule conjI; clarsimp)
   apply (rename_tac level' slot pte' ao pt)
   apply (drule (1) level_of_slotI)
   apply (case_tac "slot = table_base pt_t p"; clarsimp simp: in_omonad simp del: valid_vspace_obj.simps)
   apply (drule vs_lookup_level)
   apply (clarsimp)
   apply (prop_tac "valid_vspace_obj level' (PageTable pt) s")
    apply fastforce
   apply simp
   apply (rule ball_pt_range_pt_updI, fastforce)
   apply (drule ptes_of_pts_of_pt_type, simp add: in_omonad)
   apply fastforce
  apply (rename_tac level' slot pte' ao pt)
  apply (clarsimp simp: vs_lookup_slot_def)
  apply (case_tac "slot = table_base pt_t p"; clarsimp simp: in_omonad simp del: valid_vspace_obj.simps)
  apply (drule vs_lookup_level)
  apply (clarsimp)
  apply (prop_tac "valid_vspace_obj level' (PageTable pt) s")
   apply fastforce
  apply simp
  apply (rule ball_pt_range_pt_updI, fastforce)
  apply (drule ptes_of_pts_of_pt_type, simp add: in_omonad)
  apply fastforce
  done

lemma pte_ref_apply_upd_Some_id[dest]:
  "pte_ref (pt_apply (pt_upd pt idx InvalidPTE) idx') = Some obj_ref
   \<Longrightarrow> pte_ref (pt_apply pt idx') = Some obj_ref"
  by (auto simp add: pt_apply_def pt_upd_def pte_ref_def split: pt.splits pte.splits if_splits)

lemma isPageTablePTE_apply_upd_InvalidPTED:
  "is_PageTablePTE (pt_apply (pt_upd pt idx' InvalidPTE) idx)
   \<Longrightarrow> is_PageTablePTE (pt_apply pt idx) \<and>
       (pptr_from_pte (pt_apply (pt_upd pt idx' InvalidPTE) idx) = pptr_from_pte (pt_apply pt idx)) \<and>
       idx' \<noteq> idx"
  by (auto simp add: pt_apply_def pt_upd_def split: pt.splits if_splits)


lemma pt_index_table_index_slot_offset_eq:
  "\<lbrakk> pt_index level vref = table_index level p; is_aligned p pte_bits \<rbrakk>
   \<Longrightarrow> pt_slot_offset level (table_base level p) vref = p" for level :: vm_level
  using table_base_index_eq pt_slot_offset_def
  by force

(* If you start with a lookup from asid down to level, and you split off a walk at level', then an
   update at level' does not affect the extended pt_walk from level'-1 down to level. *)
(* FIXME: we should do the same on RISCV64 *)
lemma pt_walk_below_pt_upd_idem:
  "\<lbrakk> vs_lookup_table level' asid vref s = Some (level', table_base (level_type level') p);
     vref \<in> user_region;
     pt_type pt = level_type level';
     pspace_aligned s; pspace_distinct s; valid_vspace_objs s; valid_asid_table s;
     ako_at (PageTable pt) (table_base (level_type level') p) s;
     level' \<le> max_pt_level; level < level';
     is_PageTablePTE (pt_apply (pt_upd pt (table_index (level_type level') p) pte) (pt_index level' vref));
     is_aligned (pt_slot_offset level' (table_base (level_type level') p) vref) pte_bits;
     table_index (level_type level') p \<noteq> pt_index level' vref \<rbrakk>
   \<Longrightarrow>
   pt_walk (level' - 1) level (pptr_from_pte (pt_apply (pt_upd pt (table_index
                                                                     (level_type level') p) pte)
                                                       (pt_index level' vref))) vref
     (\<lambda>pt_t pa. level_pte_of pt_t pa ((pts_of s)(table_base (level_type level') p \<mapsto>
                                               pt_upd pt (table_index (level_type level') p) pte)))
   = pt_walk (level' - 1) level (pptr_from_pte (pt_apply (pt_upd pt (table_index
                                                                       (level_type level') p) pte)
                                                         (pt_index level' vref))) vref (ptes_of s)"
  apply (subst pt_walk_pt_upd_idem; clarsimp?)
   apply (rename_tac level'')
   apply (prop_tac "level'' < level'")
    apply (drule pt_walk_max_level)
    apply (simp add: vm_level.leq_minus1_less)
   apply (prop_tac "pt_walk level' level'' (table_base level' p) vref (ptes_of s) =
                      Some (level'', table_base level' p)")
    apply (subst pt_walk.simps)
    apply clarsimp
    apply (clarsimp simp: in_omonad obj_at_def pt_apply_upd_eq)
    apply (rule_tac x="pt_apply pt (table_index level' (pt_slot_offset level' (table_base level' p) vref))" in exI)
    apply (clarsimp simp: ptes_of_def in_omonad)
   apply (prop_tac "vs_lookup_table level'' asid vref s = Some (level'', table_base level' p)")
    apply (erule (2) vs_lookup_table_extend)
   apply (drule (1) no_loop_vs_lookup_table; simp?)
  apply (clarsimp simp: pptr_from_pte_aligned_pt_bits)
  done

(* Building on the result of pt_walk_below_pt_upd_idem, we can reassemble a vs_lookup_table from
   asid down to level, using a vs_lookup_table down to level', an updated page table at level' and
   a pt_walk from level'-1 down to level, if the update is not on the lookup path at level'. *)
(* FIXME: we should do the same on RISCV64 *)
lemma vs_lookup_table_step_pt_walk_extend:
  "\<lbrakk> vs_lookup_table level' asid vref s = Some (level', table_base level' p);
     pt_type pt = level_type level';
     ako_at (PageTable pt) (table_base level' p) s;
     level < level'; level' \<le> max_pt_level;
     is_PageTablePTE (pt_apply (pt_upd pt (table_index level' p) pte) (pt_index level' vref));
     pt_walk (level' - 1) level (pptr_from_pte (pt_apply (pt_upd pt (table_index level' p) pte)
                                                         (pt_index level' vref))) vref (ptes_of s)
       = Some (level, p');
     is_aligned (pt_slot_offset level' (table_base level' p) vref) pte_bits;
     pt_index level' vref \<noteq> table_index level' p\<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref s = Some (level, p')"
  apply (prop_tac "pt_walk level' level (table_base level' p) vref (ptes_of s) = Some (level, p')")
   apply (subst pt_walk.simps)
   apply (clarsimp simp: in_omonad obj_at_def)
   apply (rule_tac x="pt_apply pt (table_index level' (pt_slot_offset level' (table_base level' p)
                                               vref))" in exI)
   apply (clarsimp simp: ptes_of_def in_omonad pt_apply_upd_eq)
  apply (erule (2) vs_lookup_table_extend)
  done

lemma store_pte_InvalidPTE_valid_vs_lookup:
  "\<lbrace> valid_vs_lookup
     and pspace_aligned and pspace_distinct and valid_vspace_objs
     and valid_asid_table and unique_table_refs
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and K (pte = InvalidPTE) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. valid_vs_lookup \<rbrace>"
  unfolding store_pte_def set_pt_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (simp (no_asm) add: valid_vs_lookup_def)
  apply clarsimp
  apply (subst caps_of_state_after_update[folded fun_upd_def], simp add: obj_at_def)
  apply (rename_tac obj_ref)
  (* interesting case is if table_base p was reachable before the update *)
  apply (case_tac "\<forall>level. vs_lookup_table level asid vref s \<noteq> Some (level, table_base pt_t p)")
   apply (clarsimp simp: valid_vs_lookup_def)
   apply (subst (asm) vs_lookup_target_unreachable_upd_idem; fastforce)
  apply clarsimp
  apply (rename_tac level')

  apply (prop_tac "level' \<le> max_pt_level \<longrightarrow> asid \<noteq> 0")
   apply (fastforce dest: vs_lookup_table_asid_not_0)

  (* unfold vs_lookup_target on updated state and clean up *)
  apply (subst (asm) vs_lookup_target_def)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac slot_ptr)
  apply (clarsimp simp: vs_lookup_slot_def)
  apply (rename_tac level'' table_ptr)
  apply (drule_tac bot_level=bot_level in vs_lookup_level)
  apply (prop_tac "level'' = level", fastforce split: if_splits)
  apply clarsimp
  apply (prop_tac "level' \<le> max_pt_level")
   apply (rule ccontr, clarsimp simp: not_le)
   apply (frule (1) vs_lookup_asid_pool)
   apply (clarsimp simp: asid_pools_of_ko_at)
   apply (fastforce simp: obj_at_def)
  (* the interesting operations all happen when level \<le> max_pt_level; get asid_pool_level out of
     the way first *)
  apply (case_tac "level = asid_pool_level")
   apply clarsimp
   (* FIXME RISCV there is a property hidden in here about vs_lookup_target for asid_pool_level,
      repeating some of the pattern seen in vs_lookup_target_unreachable_upd_idem *)
   apply (clarsimp simp: pool_for_asid_vs_lookup vspace_for_pool_def entry_for_pool_def in_omonad)
   apply (rename_tac pool_ptr ap_entry pool)
   apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (prop_tac "pool_for_asid asid s = Some pool_ptr")
    apply (fastforce simp: pool_for_asid_def)
   apply (prop_tac "vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level,
                                                                         ap_vspace ap_entry)")
    apply (clarsimp simp: vs_lookup_target_def in_omonad)
    apply (rule_tac x=pool_ptr in exI)
    apply (fastforce simp: pool_for_asid_vs_lookup vspace_for_pool_def entry_for_pool_def
                           vs_lookup_slot_def in_omonad)
   apply (fastforce dest: valid_vs_lookupD simp: valid_vs_lookup_def)
  apply clarsimp
  (* now we are looking at page tables only; we can extend or truncate our previous lookup,
     but nowhere in seL4 do we do both in one step
     we also now know asid \<noteq> 0 *)

  (* updating deeper than where we can find table_base p has no effect *)
  apply (case_tac "level' \<le> level")
   apply (drule vs_lookup_level, drule (3) vs_lookup_table_fun_upd_deep_idem; assumption?)
   apply (prop_tac "is_aligned table_ptr (pt_bits (level_type level))")
    apply (fastforce elim!: vs_lookup_table_is_aligned)
   apply (clarsimp simp: in_omonad fun_upd_apply level_pte_of_def split: if_splits)
    (* miss on pte *)
    apply (prop_tac "level' = level")
     apply (drule no_loop_vs_lookup_table; simp?; blast)
    apply clarsimp
    apply (drule vs_lookup_target_pt_levelI; assumption?)
     apply (fastforce simp: in_omonad ptes_of_def obj_at_def)
    apply (fastforce dest!: valid_vs_lookupD)
   (* miss on table_base p *)
    apply (drule_tac level=level in vs_lookup_target_pt_levelI; assumption?)
     apply (fastforce simp: in_omonad ptes_of_def obj_at_def)
    apply (fastforce dest!: valid_vs_lookupD)
  (* we are updating at table_base p, which is within the original lookup path *)
  apply (clarsimp simp: not_le)

  (* split the lookup with state update down to table_base p *)
  apply (drule_tac level=level and level'=level' in vs_lookup_splitD)
    apply simp
   apply (fastforce intro: less_imp_le)
  apply clarsimp
  apply (rename_tac pt_ptr)
  (* update now occurs in pt_walk stage *)
  apply (drule (1) vs_lookup_table_fun_upd_deep_idem; assumption?; simp)
  apply clarsimp
  apply (prop_tac "pt_type pt = level_type level'")
   apply (fastforce simp: in_omonad obj_at_def dest!: valid_vspace_objs_strongD)
  (* handle the actual update, happening on next step of pt_walk *)
  apply (subst (asm) pt_walk.simps, clarsimp simp: in_omonad split: if_splits)
  apply (rename_tac pte')
  apply (erule disjE; clarsimp)
  apply (subst (asm) (2) level_pte_of_def)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pt')
  apply (clarsimp simp: fun_upd_apply if_option)
  apply (case_tac "table_index level' (pt_slot_offset level' (table_base level' p) vref) =
                   table_index level' p"; clarsimp)
  (* staying on old path; we can't hit table_base p again *)
  apply (subst (asm) pt_walk_below_pt_upd_idem; (assumption|simp)?)
  (* pt_walk is now on pts_of s, can stitch it back together into a vs_lookup_table *)
  apply (prop_tac "vs_lookup_table level asid vref s = Some (level, table_ptr)")
   apply (erule vs_lookup_table_step_pt_walk_extend; assumption)
  (* now specifically to vs_lookup_target reconstruction, we get through pte_of ref_of stuff *)
  apply (subst (asm) level_pte_of_def)
  apply (clarsimp simp: in_omonad fun_upd_apply)
  apply (prop_tac "is_aligned table_ptr (pt_bits level)")
   apply (fastforce elim!: vs_lookup_table_is_aligned)
  apply (clarsimp split: if_splits)
   apply (prop_tac "level' = level")
    apply (drule no_loop_vs_lookup_table; simp?; blast)
   apply clarsimp
  apply (drule_tac level=level in vs_lookup_target_pt_levelI; assumption?)
   apply (fastforce simp: in_omonad ptes_of_def obj_at_def)
  apply (drule valid_vs_lookupD; assumption?; clarsimp)
  done

lemma store_pte_non_InvalidPTE_valid_vs_lookup:
  "\<lbrace> valid_vs_lookup
     and pspace_aligned and pspace_distinct and valid_vspace_objs
     and valid_asid_table and unique_table_refs
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and (\<lambda>s. \<forall>level asid vref.
                 vs_lookup_table level asid vref s = Some (level, table_base pt_t p)
                      \<longrightarrow> vref \<in> user_region
                      \<longrightarrow> level_type level = pt_t
                      \<longrightarrow> pt_slot_offset level (table_base pt_t p) vref = p
                      \<longrightarrow> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T))
                         \<and> the (pte_ref pte) \<noteq> table_base pt_t p
                         \<and> (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                     obj_refs cap = {the (pte_ref pte)} \<and>
                                     vs_cap_ref cap = Some (asid, vref_for_level vref level))) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. valid_vs_lookup \<rbrace>"
  unfolding store_pte_def set_pt_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (simp (no_asm) add: valid_vs_lookup_def)
  apply clarsimp
  apply (subst caps_of_state_after_update[folded fun_upd_def], simp add: obj_at_def)
  apply (rename_tac obj_ref)
  (* interesting case is if table_base p was reachable before the update *)
  apply (case_tac "\<forall>level. vs_lookup_table level asid vref s \<noteq> Some (level, table_base pt_t p)")
   apply (clarsimp simp: valid_vs_lookup_def)
   apply (subst (asm) vs_lookup_target_unreachable_upd_idem; fastforce)
  apply clarsimp
  apply (rename_tac level')

  apply (prop_tac "level' \<le> max_pt_level \<longrightarrow> asid \<noteq> 0")
   apply (fastforce dest: vs_lookup_table_asid_not_0)

  (* unfold vs_lookup_target on updated state and clean up *)
  apply (subst (asm) vs_lookup_target_def)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac slot_ptr)
  apply (clarsimp simp: vs_lookup_slot_def)
  apply (rename_tac level'' table_ptr)
  apply (drule_tac bot_level=bot_level in vs_lookup_level)
  apply (prop_tac "level'' = level", fastforce split: if_splits)
  apply clarsimp
  apply (prop_tac "level' \<le> max_pt_level")
   apply (rule ccontr, clarsimp simp: not_le)
   apply (frule (1) vs_lookup_asid_pool)
   apply (clarsimp simp: asid_pools_of_ko_at)
   apply (fastforce simp: obj_at_def)
  (* the interesting operations all happen when level \<le> max_pt_level; get asid_pool_level out of
     the way first *)
  apply (case_tac "level = asid_pool_level")
   apply clarsimp
   (* FIXME RISCV there is a property hidden in here about vs_lookup_target for asid_pool_level,
      repeating some of the pattern seen in vs_lookup_target_unreachable_upd_idem *)
   apply (clarsimp simp: pool_for_asid_vs_lookup vspace_for_pool_def entry_for_pool_def in_omonad)
   apply (rename_tac pool_ptr ap_entry pool)
   apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (prop_tac "pool_for_asid asid s = Some pool_ptr")
    apply (fastforce simp: pool_for_asid_def)
   apply (prop_tac "vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level,
                                                                         ap_vspace ap_entry)")
    apply (clarsimp simp: vs_lookup_target_def in_omonad)
    apply (rule_tac x=pool_ptr in exI)
    apply (fastforce simp: pool_for_asid_vs_lookup vspace_for_pool_def entry_for_pool_def
                           vs_lookup_slot_def in_omonad)
   apply (fastforce dest: valid_vs_lookupD simp: valid_vs_lookup_def)
  apply clarsimp
  (* now we are looking at page tables only; we can extend or truncate our previous lookup,
     but nowhere in seL4 do we do both in one step
     we also now know asid \<noteq> 0 *)

  (* updating deeper than where we can find table_base p has no effect *)
  apply (case_tac "level' \<le> level")
   apply (drule vs_lookup_level, drule (3) vs_lookup_table_fun_upd_deep_idem; assumption?)
   apply (prop_tac "is_aligned table_ptr (pt_bits (level_type level))")
    apply (fastforce elim!: vs_lookup_table_is_aligned)
   apply (clarsimp simp: in_omonad fun_upd_apply level_pte_of_def pt_apply_upd_eq split: if_splits)
     apply (drule sym, drule (1) pt_index_table_index_slot_offset_eq; simp)
    (* miss on pte *)
    apply (prop_tac "level' = level")
     apply (drule no_loop_vs_lookup_table; simp?; blast)
    apply clarsimp
    apply (drule vs_lookup_target_pt_levelI; assumption?)
     apply (fastforce simp: in_omonad ptes_of_def obj_at_def)
    apply (fastforce dest!: valid_vs_lookupD)
   (* miss on table_base p *)
    apply (drule_tac level=level in vs_lookup_target_pt_levelI; assumption?)
     apply (fastforce simp: in_omonad ptes_of_def obj_at_def)
    apply (fastforce dest!: valid_vs_lookupD)
  (* we are updating at table_base p, which is within the original lookup path *)
  apply (clarsimp simp: not_le)

  (* split the lookup with state update down to table_base p *)
  apply (drule_tac level=level and level'=level' in vs_lookup_splitD)
    apply simp
   apply (fastforce intro: less_imp_le)
  apply clarsimp
  apply (rename_tac pt_ptr)
  (* update now occurs in pt_walk stage *)
  apply (drule (1) vs_lookup_table_fun_upd_deep_idem; assumption?; simp)
  (* can now show there's a cap to the (pte_ref pte) at level' *)
  apply ((erule allE)+, erule (1) impE)
  apply clarsimp
  apply (prop_tac "pt_type pt = level_type level'")
   apply (fastforce simp: in_omonad obj_at_def dest!: valid_vspace_objs_strongD)
  (* handle the actual update, happening on next step of pt_walk *)
  apply (subst (asm) pt_walk.simps, clarsimp simp: in_omonad split: if_splits)
  apply (rename_tac pte')
  apply (erule disjE; clarsimp)
  apply (subst (asm) (2) level_pte_of_def)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pt')
  apply (clarsimp simp: fun_upd_apply if_option)
  apply (case_tac "table_index level' (pt_slot_offset level' (table_base level' p) vref) =
                   table_index level' p"; clarsimp)
   (* we could not have arrived at our new empty table through a non-empty table and from
      precondition, we are not creating a loop *)
   apply (drule_tac pt="empty_pt (level' - 1)" in pt_walk_non_empty_ptD;
          (simp add: in_omonad fun_upd_apply pptr_from_pte_aligned_pt_bits)?)
    apply (cases pte; clarsimp simp: pptr_from_pte_def)
    apply (drule (1) pt_index_table_index_slot_offset_eq; simp add: level_type_minus_one)
   apply (clarsimp simp: in_omonad level_pte_of_def)
   apply (frule pptr_from_pte_aligned_pt_bits[rotated], simp)
   apply (cases pte; clarsimp)
   apply (fastforce simp: pptr_from_pte_def in_omonad fun_upd_apply
                    intro!: pt_index_table_index_slot_offset_eq)
  (* staying on old path; we can't hit table_base p again *)
  apply (subst (asm) pt_walk_below_pt_upd_idem; (assumption|simp)?)
  (* pt_walk is now on pts_of s, can stitch it back together into a vs_lookup_table *)
  apply (prop_tac "vs_lookup_table level asid vref s = Some (level, table_ptr)")
   apply (erule vs_lookup_table_step_pt_walk_extend; assumption)
  (* now specifically to vs_lookup_target reconstruction, we get through pte_of ref_of stuff *)
  apply (subst (asm) level_pte_of_def)
  apply (clarsimp simp: in_omonad fun_upd_apply)
  apply (prop_tac "is_aligned table_ptr (pt_bits level)")
   apply (fastforce elim!: vs_lookup_table_is_aligned)
  apply (clarsimp split: if_splits)
   apply (prop_tac "level' = level")
    apply (drule no_loop_vs_lookup_table; simp?; blast)
   apply clarsimp
  apply (drule_tac level=level in vs_lookup_target_pt_levelI; assumption?)
   apply (fastforce simp: in_omonad ptes_of_def obj_at_def)
  apply (drule valid_vs_lookupD; assumption?; clarsimp)
  done

(* NOTE: should be able to derive the (pte_ref pte) \<noteq> table_base p) from
   the (pte_ref pte) being unreachable anywhere in the original state
   (this should come from having an unmapped cap to it) *)
lemma store_pte_PageTablePTE_valid_vspace_objs:
  "\<lbrace> valid_vspace_objs
     and pspace_aligned and pspace_distinct
     and valid_asid_table and unique_table_refs and valid_vs_lookup
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and K (is_PageTablePTE pte)
     and (\<lambda>s. \<forall>level. \<exists>\<rhd> (level, table_base pt_t p) s
                      \<longrightarrow> level_type level = pt_t
                      \<longrightarrow> valid_pte level pte s \<and> pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T)
                         \<and> the (pte_ref pte) \<noteq> table_base pt_t p) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>s. valid_vspace_objs \<rbrace>"
  supply fun_upd_apply[simp del]
  apply (wpsimp simp: store_pte_def set_pt_def wp: set_object_wp)
  apply (subst valid_vspace_objs_def)
  apply (clarsimp split del: if_split)
  apply (rename_tac p' ao)
  (* focus on valid_vspace_obj level ao s  *)
  apply (rule valid_vspace_obj_same_type; simp?)
    defer
    apply (fastforce simp: obj_at_def)
   apply (simp add: obj_at_def)
  apply (drule vs_lookup_level)
  (* if table_base p is unreachable, we are not updating anything relevant *)
  apply (case_tac "\<forall>level. vs_lookup_table level asid vref s \<noteq> Some (level, table_base pt_t p)")
   apply (subst (asm) vs_lookup_table_unreachable_upd_idem; simp?)
   apply (fastforce simp: fun_upd_apply valid_vspace_objs_def split: if_splits)
  (* we are changing the reachable page table at table_base p *)
  supply valid_vspace_obj.simps[simp del]
  apply clarsimp
  apply (rename_tac level')
  apply (prop_tac "level' \<le> max_pt_level")
   (* rephrase as \<noteq> asid_pool_level *)
   apply (case_tac "level' = asid_pool_level"; simp)
   apply (clarsimp simp: pool_for_asid_vs_lookup)
   apply (drule (1) pool_for_asid_validD)
   apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)
  apply (prop_tac "pt_type pt = level_type level'")
   apply (drule (5) valid_vspace_objs_strongD)
   apply (clarsimp simp: in_omonad obj_at_def)
  apply (prop_tac "valid_pte level' pte s", fastforce)
  (* updating deeper than where we can find table_base p has no effect *)
  apply (case_tac "level' \<le> level")
   apply (drule vs_lookup_level, drule (3) vs_lookup_table_fun_upd_deep_idem; assumption?)
   apply (clarsimp simp: fun_upd_apply split: if_splits)
    apply (prop_tac "level' = level", fastforce dest: no_loop_vs_lookup_table)
    apply (rule valid_vspace_obj_valid_pte_upd; simp?)
    apply (clarsimp simp: valid_vspace_objs_def vspace_objs_of_ako_at_Some)
   apply (clarsimp simp: valid_vspace_objs_def vspace_objs_of_ako_at_Some)
  (* we are updating at table_base p, which is within the original lookup path *)
  apply (clarsimp simp: not_le)
  (* split both lookups down to table_base p *)
  apply (drule vs_lookup_level)
  apply (drule_tac level=level in vs_lookup_splitD; simp?)
   apply (fastforce intro: less_imp_le)
  apply clarsimp
  apply (rename_tac pt_ptr)
  (* update now occurs in pt_walk stage *)
  apply (drule (1) vs_lookup_table_fun_upd_deep_idem; assumption?; simp)
  apply (prop_tac "pt_type pt = level_type level'")
   apply (fastforce simp: in_omonad obj_at_def dest!: valid_vspace_objs_strongD)
  apply (prop_tac "valid_pte level' pte s \<and> pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T)
                   \<and> the (pte_ref pte) \<noteq> table_base pt_t p", fastforce)
  (* handle the actual update, happening on next step of pt_walk *)
  apply (subst (asm) pt_walk.simps, clarsimp simp: in_omonad split: if_splits)
  apply (rename_tac pte')
  apply (erule disjE; clarsimp)
  apply (clarsimp simp: fun_upd_apply)
  apply (subst (asm) level_pte_of_def)
  apply (clarsimp simp: in_omonad if_option)
  apply (rename_tac pt')
  apply (clarsimp simp: fun_upd_apply)
  apply (case_tac "table_index level' (pt_slot_offset level' (table_base level' p) vref) =
                   table_index level' p"; clarsimp)
   (* we could not have arrived at our new empty table through a non-empty table and from
      precondition, we are not creating a loop *)
   apply (drule_tac pt="empty_pt (level' - 1)" in pt_walk_non_empty_ptD;
          simp add: in_omonad fun_upd_apply pptr_from_pte_aligned_pt_bits)
    apply (cases pte; clarsimp simp: pptr_from_pte_def)
    apply (drule (1) pt_index_table_index_slot_offset_eq; simp add: level_type_minus_one)
   apply (cases pte; clarsimp simp: pptr_from_pte_def in_omonad valid_vspace_obj.simps)
  (* staying on old path; we can't hit table_base p again *)
  apply (subst (asm) pt_walk_below_pt_upd_idem; (assumption|simp)?)
  (* pt_walk is now on pts_of s, can stitch it back together into a vs_lookup_table *)
  apply (prop_tac "vs_lookup_table level asid vref s = Some (level, p')")
   apply (erule vs_lookup_table_step_pt_walk_extend; assumption)
  (* p' can't equal table_base p since we see it earlier in the lookup *)
  apply (prop_tac "p' \<noteq> table_base pt_t p")
   apply clarsimp
   apply (drule (1) no_loop_vs_lookup_table, simp+)
  (* finally can use valid_vspace_objs *)
  apply (clarsimp simp: valid_vspace_objs_def)
  done

lemma store_pte_valid_vspace_objs:
  "\<lbrace> valid_vspace_objs
     and pspace_aligned and pspace_distinct and valid_asid_table and unique_table_refs and valid_vs_lookup
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and (\<lambda>s. \<forall>level. \<exists>\<rhd> (level, table_base pt_t p) s
                      \<longrightarrow> level_type level = pt_t
                      \<longrightarrow> valid_pte level pte s
                         \<and> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T)
                                                   \<and> the (pte_ref pte) \<noteq> table_base pt_t p)) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. valid_vspace_objs \<rbrace>"
  apply (case_tac pte; clarsimp)
    (* InvalidPTE *)
    apply wpsimp
   (* PagePTE *)
   apply (wpsimp wp: store_pte_PagePTE_valid_vspace_objs)
   apply fastforce
  (* PageTablePTE *)
  apply (wp store_pte_PageTablePTE_valid_vspace_objs, clarsimp)
  done

lemma store_pte_valid_vs_lookup:
  "\<lbrace> valid_vs_lookup
     and pspace_aligned and pspace_distinct
     and valid_vspace_objs and valid_asid_table and unique_table_refs
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and (\<lambda>s. pte \<noteq> InvalidPTE
              \<longrightarrow> (\<forall>level asid vref.
                     vs_lookup_table level asid vref s = Some (level, table_base pt_t p)
                     \<longrightarrow> vref \<in> user_region
                     \<longrightarrow> level_type level = pt_t
                     \<longrightarrow> pt_slot_offset level (table_base pt_t p) vref = p
                     \<longrightarrow> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T))
                         \<and> the (pte_ref pte) \<noteq> table_base pt_t p
                         \<and> (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                     obj_refs cap = {the (pte_ref pte)} \<and>
                                     vs_cap_ref cap = Some (asid, vref_for_level vref level)))) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. valid_vs_lookup \<rbrace>"
  apply (case_tac pte; clarsimp)
    apply (wpsimp wp: store_pte_InvalidPTE_valid_vs_lookup)
   apply (wpsimp wp: store_pte_non_InvalidPTE_valid_vs_lookup)+
  done

lemma store_pte_valid_arch_caps:
  "\<lbrace> valid_arch_caps
     and pspace_aligned and pspace_distinct and valid_vspace_objs and valid_asid_table
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and (\<lambda>s. (\<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base pt_t p) pt_t asidopt))
                              \<longrightarrow> asidopt = None \<longrightarrow> pte = InvalidPTE))
     and (\<lambda>s. pte \<noteq> InvalidPTE
              \<longrightarrow> (\<forall>level asid vref.
                     vs_lookup_table level asid vref s = Some (level, table_base pt_t p)
                     \<longrightarrow> vref \<in> user_region
                     \<longrightarrow> level_type level = pt_t
                     \<longrightarrow> pt_slot_offset level (table_base pt_t p) vref = p
                     \<longrightarrow> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T))
                         \<and> the (pte_ref pte) \<noteq> table_base pt_t p
                         \<and> (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                     obj_refs cap = {the (pte_ref pte)} \<and>
                                     vs_cap_ref cap = Some (asid, vref_for_level vref level)))) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. valid_arch_caps \<rbrace>"
  unfolding valid_arch_caps_def
  by (wpsimp wp: store_pte_valid_vs_lookup store_pte_valid_table_caps)

lemma store_pte_valid_global_tables[wp]:
  "\<lbrace> \<lambda>s. table_base pt_t p \<notin> global_refs s \<and> valid_global_tables s \<rbrace>
   store_pte pt_t p pte
   \<lbrace> \<lambda>_. valid_global_tables \<rbrace>"
  unfolding store_pte_def valid_global_tables_2_def
  by (wpsimp wp: set_pt_pts_of simp: global_refs_def | wps)+

lemma store_pte_invs:
  "\<lbrace> invs
     and (\<lambda>s. table_base pt_t p \<notin> global_refs s)
     and K (wellformed_pte pte \<and> valid_mapping_insert pt_t p pte)
     and (\<lambda>s. \<forall>level. \<exists>\<rhd> (level, table_base pt_t p) s
                      \<longrightarrow> level_type level = pt_t
                      \<longrightarrow> valid_pte level pte s
                         \<and> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T)
                                                   \<and> the (pte_ref pte) \<noteq> table_base pt_t p))
     and (\<lambda>s. (\<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base pt_t p) pt_t asidopt))
                              \<longrightarrow> asidopt = None \<longrightarrow> pte = InvalidPTE))
     and (\<lambda>s. pte \<noteq> InvalidPTE
              \<longrightarrow> (\<forall>level asid vref.
                     vs_lookup_table level asid vref s = Some (level, table_base pt_t p)
                     \<longrightarrow> vref \<in> user_region
                     \<longrightarrow> level_type level = pt_t
                     \<longrightarrow> pt_slot_offset level (table_base pt_t p) vref = p
                     \<longrightarrow> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some (empty_pt NormalPT_T))
                         \<and> the (pte_ref pte) \<noteq> table_base pt_t p
                         \<and> (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                     obj_refs cap = {the (pte_ref pte)} \<and>
                                     vs_cap_ref cap = Some (asid, vref_for_level vref level)))) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. invs \<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_state_def)
  apply (wpsimp wp: store_pte_valid_global_vspace_mappings
                    store_pte_valid_vspace_objs store_pte_valid_arch_caps
                    store_pte_equal_kernel_mappings_no_kernel_slots)
  apply (clarsimp simp: valid_objs_caps valid_arch_caps_def)
  done

lemma store_pte_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base pt_t p) pt_t ref))) and
    (\<lambda>s. (\<exists>asid. vspace_for_asid asid s = Some (table_base pt_t p)) \<longrightarrow>
           ucast (table_index pt_t p) \<notin> invalid_mapping_slots) and
    (\<lambda>s. table_base pt_t p \<notin> global_refs s) and K (pte = InvalidPTE)\<rbrace>
  store_pte pt_t p pte \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp wp: store_pte_invs simp: wellformed_pte_def)


lemma vs_lookup_table_vspace:
  "\<lbrakk> vs_lookup_table level asid vptr s = Some (level, pt_ptr);
     vspace_for_asid asid' s = Some pt_ptr; vptr \<in> user_region; invs s \<rbrakk>
   \<Longrightarrow> asid' = asid \<and> level = max_pt_level"
  apply (cases "level = asid_pool_level"; clarsimp)
   apply (clarsimp simp: vs_lookup_table_def)
   apply (drule pool_for_asid_validD; clarsimp)
   apply (drule vspace_for_asid_valid_pt; clarsimp)
   apply (fastforce simp: in_omonad)
  apply (drule vspace_for_asid_vs_lookup)
  apply (frule_tac level=level and level'=max_pt_level in unique_vs_lookup_table, assumption; clarsimp?)
   apply (fastforce intro: valid_objs_caps)
  apply (drule (1) no_loop_vs_lookup_table; clarsimp?)
  apply (rule vref_for_level_eq_max_mono[symmetric], simp)
  done

lemma pspace_respects_device_region_dmo:
  assumes valid_f: "\<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  shows "do_machine_op f \<lbrace>pspace_respects_device_region\<rbrace>"
  apply (clarsimp simp: do_machine_op_def gets_def select_f_def simpler_modify_def bind_def valid_def
                        get_def return_def)
  apply (drule_tac P1 = "(=) (device_state (machine_state s))" in use_valid[OF _ valid_f])
  apply auto
  done

lemma cap_refs_respects_device_region_dmo:
  assumes valid_f: "\<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  shows "do_machine_op f \<lbrace>cap_refs_respects_device_region\<rbrace>"
  apply (clarsimp simp: do_machine_op_def gets_def select_f_def simpler_modify_def bind_def valid_def
                        get_def return_def)
  apply (drule_tac P1 = "(=) (device_state (machine_state s))" in use_valid[OF _ valid_f])
  apply auto
  done

crunches do_machine_op
  for valid_ioports[wp]: valid_ioports
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and valid_asid_map[wp]: valid_asid_map
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and vspace_at_asid[wp]: "\<lambda>s. P (vspace_at_asid a pt s)"
  and valid_vs_lookup[wp]: "\<lambda>s. P (valid_vs_lookup s)"
  and valid_obj[wp]: "valid_obj t obj"
  (simp: valid_kernel_mappings_def wp: valid_obj_typ)

lemma dmo_invs_lift:
  assumes dev: "\<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  assumes mem: "\<And>P. f \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes irq: "\<And>P. f \<lbrace>\<lambda>ms. P (irq_masks ms)\<rbrace>"
  shows "do_machine_op f \<lbrace>invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def valid_irq_states_def valid_machine_state_def
  by (wpsimp wp: dev hoare_vcg_all_lift hoare_vcg_disj_lift
                 dmo_inv_prop_lift[where g=underlying_memory, OF mem]
                 pspace_respects_device_region_dmo cap_refs_respects_device_region_dmo
      | wps dmo_inv_prop_lift[where g=irq_masks, OF irq])+

lemma dmo_machine_op_lift_invs[wp]:
  "do_machine_op (machine_op_lift f) \<lbrace>invs\<rbrace>"
  by (wp dmo_invs_lift)

lemma as_user_inv:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> as_user t f \<lbrace>\<lambda>x. P\<rbrace>"
proof -
  have P: "\<And>a b input. (a, b) \<in> fst (f input) \<Longrightarrow> b = input"
    by (rule use_valid [OF _ x], assumption, rule refl)
  have Q: "\<And>s ps. ps (kheap s) = kheap s \<Longrightarrow> kheap_update ps s = s"
    by simp
  show ?thesis
    apply (simp add: as_user_def gets_the_def assert_opt_def set_object_def get_object_def split_def)
    apply wp
    apply (clarsimp dest!: P)
    apply (subst Q)
     prefer 2
     apply assumption
    apply (rule ext)
    apply (simp add: get_tcb_def)
    apply (case_tac "kheap s t"; simp)
    apply (case_tac a; simp)
    apply (clarsimp simp: arch_tcb_context_set_def arch_tcb_context_get_def)
    done
qed

crunches getRegister
  for inv[wp]: P
  (simp: getRegister_def)

lemmas user_getreg_inv[wp] = as_user_inv[OF getRegister_inv]

end

end
