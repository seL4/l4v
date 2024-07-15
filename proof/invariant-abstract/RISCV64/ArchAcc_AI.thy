(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Lemmas on arch get/set object etc
*)

theory ArchAcc_AI
imports SubMonad_AI "Lib.Crunch_Instances_NonDet"
begin

context non_vspace_op
begin

lemma valid_vso_at[wp]:"\<lbrace>valid_vso_at level p\<rbrace> f \<lbrace>\<lambda>_. valid_vso_at level p\<rbrace>"
  by (rule valid_vso_at_lift_aobj_at; wp vsobj_at; simp)

end

context Arch begin global_naming RISCV64

(* Is there a lookup that leads to a page table at (level, p)? *)
locale_abbrev ex_vs_lookup_table ::
  "vm_level \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" ("\<exists>\<rhd> '(_, _')" [0,0] 1000) where
  "ex_vs_lookup_table level p s \<equiv>
     \<exists>asid vref. vs_lookup_table level asid vref s = Some (level, p) \<and> vref \<in> user_region"

bundle unfold_objects =
  obj_at_def[simp]
  kernel_object.splits[split]
  arch_kernel_obj.splits[split]
  get_object_wp [wp]

bundle unfold_objects_asm =
  obj_at_def[simp]
  kernel_object.split_asm[split]
  arch_kernel_obj.split_asm[split]

lemma invs_valid_asid_table [elim!]:
  "invs s \<Longrightarrow> valid_asid_table s"
  by (simp add: invs_def valid_state_def valid_arch_state_def)

lemma ptes_of_wellformed_pte:
  "\<lbrakk> ptes_of s p = Some pte; valid_objs s \<rbrakk> \<Longrightarrow> wellformed_pte pte"
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
  apply (subgoal_tac "level + 1 \<noteq> asid_pool_level")
   prefer 2
   apply (metis max_pt_level_plus_one add.right_cancel)
  apply (clarsimp simp: obind_assoc simp del: asid_pool_level_neq)
  apply (subst (asm) pt_walk_split_Some[where level'="level + 1"]; simp add: less_imp_le)
  apply (subst (asm) (2) pt_walk.simps)
  apply (subgoal_tac "level + 1 \<noteq> asid_pool_level")
   prefer 2
   apply (metis max_pt_level_plus_one add.right_cancel)
  apply (clarsimp simp: in_omonad simp del: asid_pool_level_neq cong: conj_cong)
  apply (rule_tac x="level + 1" in exI)
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
                        vspace_for_asid_def
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
  "is_reply = is_Reply"
  apply (all \<open>rule ext, simp add: is_ep_def is_ntfn_def is_tcb_def is_reply_def split: kernel_object.splits\<close>)
  done

lemma cap_to_pt_is_pt_cap:
  "\<lbrakk> obj_refs cap = {p}; caps_of_state s cptr = Some cap; pts_of s p \<noteq> None;
     valid_caps (caps_of_state s) s \<rbrakk>
   \<Longrightarrow> is_pt_cap cap"
  by (drule (1) valid_capsD)
     (auto simp: pts_of_ko_at is_pt_cap_def arch_cap_fun_lift_def arch_cap.disc_eq_case(4)
                 valid_cap_def obj_at_def is_ko_to_discs is_cap_table_def is_sc_obj_def
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
   apply (simp add: cap_to_pt_is_pt_cap)
  apply (drule (2) unique_table_refsD, simp)
  apply (drule table_cap_ref_vs_cap_ref; simp)
  done

lemma vref_for_level_pt_index_idem:
  assumes "level' \<le> max_pt_level" and "level'' \<le> level'"
  shows "vref_for_level
           (vref_for_level vref (level'' + 1) || (pt_index level vref' << pt_bits_left level''))
           (level' + 1)
         = vref_for_level vref (level' + 1)"
proof -
  have dist_zero_right':
    "\<And>w x y. \<lbrakk> (w::('a::len) word) = y; x = 0\<rbrakk> \<Longrightarrow> w || x = y"
    by auto
  show ?thesis using assms
    unfolding vref_for_level_def pt_index_def
    apply (subst word_ao_dist)
    apply (rule dist_zero_right')
    apply (subst mask_lower_twice)
   apply (rule pt_bits_left_mono, erule (1) vm_level_le_plus_1_mono, rule refl)
  apply (simp add: mask_shifl_overlap_zero pt_bits_left_def)
  done
qed

lemma pt_slot_offset_vref_for_level_idem:
  "\<lbrakk> is_aligned p pt_bits; level' \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> pt_slot_offset level' p
            (vref_for_level vref (level' + 1) || (pt_index level vref << pt_bits_left level'))
   = pt_slot_offset level p vref"
  apply (simp add: pt_slot_offset_or_def)
  apply (rule arg_cong[where f="\<lambda>x. p || x"])
  apply (rule arg_cong[where f="\<lambda>x. x << pte_bits"])
  apply (simp add: pt_index_def pt_bits_left_def)
  apply (drule max_pt_level_enum)
  apply word_eqI
  apply (auto simp: bit_simps pt_bits_left_def)
  done

lemma pt_walk_loop_last_level_ptpte_helper:
  "\<lbrakk> pt_walk level level' p vref ptes = Some (level', p); level \<le> max_pt_level; level > level';
     is_aligned p pt_bits \<rbrakk>
   \<Longrightarrow> \<exists>p' vref'. (pt_walk level 0 p vref' ptes = Some (0, p'))
                 \<and> (\<exists>pte level. ptes (pt_slot_offset level p' vref') = Some pte \<and> is_PageTablePTE pte)
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
    apply fastforce
   apply blast
  (* set up assumption of IH *)
  apply (subgoal_tac
           "pt_walk (level - 1) (level' - 1) (pptr_from_pte pte)
                    (vref_for_level vref (level'+1) || (pt_index level vref << pt_bits_left level'))
                    ptes
            = Some (level' - 1, pptr_from_pte pte)")
   apply (drule meta_spec, drule meta_spec, drule meta_spec, drule (1) meta_mp, drule meta_mp)
    using pt_walk_max_level less_linear
    apply fastforce
   apply clarsimp
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
      apply (drule_tac level'="level'+1" in  vref_for_level_eq_mono
             ; fastforce intro: vref_for_level_pt_index_idem)
     apply (erule bit0.plus_one_leq)
    apply simp
   apply (rule conjI, blast)
   apply (drule_tac level'="level'+1" in  vref_for_level_eq_mono
          ; fastforce intro: vref_for_level_pt_index_idem)
  (* show assumption used for IH earlier *)
  apply (rule_tac pt_walk_split_Some[where level'="level" and level="level - 1" for level,
                                     THEN iffD2])
    apply (fastforce dest!: vm_level_not_less_zero intro: less_imp_le)
   apply (meson bit0.leq_minus1_less bit0.not_less_zero_bit0 le_less less_linear less_trans)
  apply (subgoal_tac
           "pt_walk (level - 1) level' (pptr_from_pte pte)
                    (vref_for_level vref (level' + 1) || (pt_index level vref << pt_bits_left level'))
            = pt_walk (level - 1) level' (pptr_from_pte pte) vref")
   prefer 2
   apply (rule pt_walk_vref_for_level_eq)
    apply (subst vref_for_level_pt_index_idem, simp+)
   apply (meson bit0.leq_minus1_less bit0.not_less_zero_bit0 le_less less_linear less_trans)
  apply clarsimp
  apply (subst pt_walk.simps)
  apply clarsimp
  apply (frule vm_level_not_less_zero)
  apply (clarsimp simp: in_omonad)
  apply (rule_tac x=pte in exI)
  apply (clarsimp simp add: pt_slot_offset_vref_for_level_idem)
  done

(* if you can walk the page tables and get back to a page table you have already visited,
   then you can create a lookup path such that you end up with a PT PTE at the bottom-most level *)
lemma pt_walk_loop_last_level_ptpte:
  "\<lbrakk> pt_walk level level' p vref ptes = Some (level', p); level \<le> max_pt_level; level > level';
     is_aligned p pt_bits \<rbrakk>
   \<Longrightarrow> \<exists>p' vref'. (pt_walk level 0 p vref' ptes = Some (0, p'))
                 \<and> (\<exists>pte. ptes (pt_slot_offset 0 p' vref') = Some pte \<and> is_PageTablePTE pte)
                 \<and> vref_for_level vref' (level' + 1) = vref_for_level vref (level' + 1)"
  apply (drule pt_walk_loop_last_level_ptpte_helper; simp)
  apply clarsimp
  apply (rule_tac x=p' in exI)
  apply (rule_tac x="vref_for_level vref' 1 || (pt_index levela vref' << pt_bits_left 0)" in exI)
  apply (rule conjI)
   apply (subst pt_walk_vref_for_level_eq; assumption?)
    apply simp
    apply (rule vref_for_level_pt_index_idem[where level''=0 and level'=0, simplified])
   apply simp
  apply (rule conjI)
   apply (rule_tac x=pte in exI)
   apply clarsimp
   apply (subst pt_slot_offset_vref_for_level_idem[where level'=0, simplified])
    apply (erule (2) pt_walk_is_aligned)
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
     level' < level; top_level \<le> max_pt_level; is_aligned ptptr pt_bits \<rbrakk>
   \<Longrightarrow> \<exists>vref'' ptptr'. pt_walk top_level 0 ptptr vref'' ptes = Some (0, ptptr') \<and>
                      (\<exists>pte. ptes (pt_slot_offset 0 ptptr' vref'') = Some pte \<and> is_PageTablePTE pte) \<and>
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
  apply fastforce
  done

lemma vs_lookup_table_same_for_different_levels:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     vs_lookup_table level' asid vref' s = Some (level', p);
     vref_for_level vref (level+1) = vref_for_level vref' (level+1);
     vref \<in> user_region; level' < level; level \<le> max_pt_level;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> \<exists>vref'' p' pte. vs_lookup_slot 0 asid vref'' s = Some (0, p') \<and> ptes_of s p' = Some pte \<and>
                      is_PageTablePTE pte \<and>
                      vref_for_level vref'' (level' + 1) = vref_for_level vref' (level' + 1)"
  apply (subst (asm) vs_lookup_vref_for_level1[where level=level, symmetric], blast)
  apply (subst (asm) vs_lookup_vref_for_level1[where level=level', symmetric], blast)
  apply (clarsimp simp: vs_lookup_table_def in_omonad asid_pool_level_eq)
  apply (subgoal_tac "level' \<le> max_pt_level")
   prefer 2
   apply simp
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
     unique_table_refs s; valid_vs_lookup s;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     valid_caps (caps_of_state s) s \<rbrakk>
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
   apply (subgoal_tac "vref'' \<in> user_region")
    prefer 2
    apply (frule_tac vref=vref' and level="level'+1" in vref_for_level_user_region)
    apply (rule vref_for_level_user_regionD[where level="level'+1"]; simp?)
    apply (erule vm_level_less_max_pt_level)
   apply (subgoal_tac "is_aligned pt_ptr pt_bits")
    prefer 2
    apply (fastforce elim!: vs_lookup_table_is_aligned)
   apply (drule_tac pt_ptr=pt_ptr in valid_vspace_objs_strongD, assumption; simp?)
   apply (fastforce simp: pte_of_def in_omonad is_aligned_pt_slot_offset_pte)
  done

lemma no_loop_vs_lookup_table:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p);
     vs_lookup_table level' asid vref' s = Some (level', p);
     vref_for_level vref' (max (level+1) (level'+1)) = vref_for_level vref (max (level+1) (level'+1));
     vref \<in> user_region; vref' \<in> user_region;
     unique_table_refs s; valid_vs_lookup s;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     valid_caps (caps_of_state s) s \<rbrakk>
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
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     valid_caps (caps_of_state s) s \<rbrakk>
   \<Longrightarrow> level' = level"
  apply clarsimp
  (* FIXME RISCV no_loop_vs_lookup_table can deal with asid_pool_level, but unique_vs_lookup_table
     can't, else we could get rid of this whole preamble *)
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
   vs_lookup_table level asid vref s = Some (level, table_base slot)"
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (drule vs_lookup_table_is_aligned; clarsimp)
  done

(* invs could be relaxed; lemma so far only needed when invs is present *)
lemma vs_lookup_slot_table_unfold:
  "\<lbrakk> level \<le> max_pt_level; vref \<in> user_region; invs s \<rbrakk> \<Longrightarrow>
   vs_lookup_slot level asid vref s = Some (level, pt_slot) =
   (vs_lookup_table level asid vref s = Some (level, table_base pt_slot) \<and>
    pt_slot = pt_slot_offset level (table_base pt_slot) vref)"
  apply (rule iffI)
   apply (frule (3) vs_lookup_slot_table_base)
   apply (clarsimp simp: vs_lookup_slot_def in_omonad split: if_split_asm)
  apply (clarsimp simp: vs_lookup_slot_def in_omonad)
  done

lemma pt_slot_offset_vref_for_level:
  "\<lbrakk> vref_for_level vref' (level + 1) = vref_for_level vref (level + 1);
     pt_slot_offset level p vref = pt_slot_offset level p vref';
     is_aligned p pt_bits; level \<le> max_pt_level \<rbrakk>
    \<Longrightarrow> vref_for_level vref' level = vref_for_level vref level"
  apply (clarsimp simp: pt_slot_offset_def vref_for_level_def pt_index_def)
  apply (drule shiftl_inj; (clarsimp simp: le_mask_iff, word_eqI, simp add: bit_simps)?)
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
  apply (drule (1) vs_lookup_table_unique_level; clarsimp)
  apply (drule pt_slot_offset_vref_for_level[where p="table_base p"]; clarsimp)
  done

lemma get_asid_pool_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pool. ko_at (ArchObj (ASIDPool pool)) p s \<longrightarrow> Q pool s\<rbrace>
  get_asid_pool p
  \<lbrace>Q\<rbrace>"
  by (wpsimp simp: obj_at_def in_opt_map_eq)


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
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (p && ~~mask pt_bits) s \<longrightarrow>
        Q (pt (ucast (p && mask pt_bits >> pte_bits))) s\<rbrace>
  get_pte p
  \<lbrace>Q\<rbrace>"
  by (wpsimp simp: ptes_of_Some in_opt_map_eq obj_at_def)

lemma get_pte_inv[wp]:
  "\<lbrace>P\<rbrace> get_pte p \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp wp: get_pte_wp)

lemmas store_pte_typ_ats [wp] = abs_typ_at_lifts [OF store_pte_typ_at]

crunch set_irq_state
  for cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"

lemma set_pt_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_pt ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_pt_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
               simp: cte_wp_at_after_update)

lemma set_asid_pool_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_asid_pool ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update)

lemma set_pt_pred_tcb_at[wp]:
  " set_pt ptr val \<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s)\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wpsimp wp: get_object_wp simp: pred_tcb_at_def obj_at_def)
  done


lemma set_asid_pool_pred_tcb_at[wp]:
  "set_asid_pool ptr val \<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wpsimp wp: get_object_wp simp: pred_tcb_at_def obj_at_def)
  done

lemma mask_pt_bits_inner_beauty:
  "is_aligned p pte_bits \<Longrightarrow>
  (p && ~~ mask pt_bits) + (ucast ((ucast (p && mask pt_bits >> pte_bits))::pt_index) << pte_bits) = (p::machine_word)"
  by (rule mask_split_aligned; simp add: bit_simps)

lemma more_pt_inner_beauty:
  fixes x :: pt_index
  fixes p :: machine_word
  assumes x: "x \<noteq> ucast (p && mask pt_bits >> pte_bits)"
  shows "(p && ~~ mask pt_bits) + (ucast x << pte_bits) = p \<Longrightarrow> False"
  by (rule mask_split_aligned_neg[OF _ _ x]; simp add: bit_simps)


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

definition
  "valid_mapping_entries m \<equiv> case m of
    (InvalidPTE, _) \<Rightarrow> \<top>
  | (PagePTE _ _ _, p) \<Rightarrow> pte_at p
  | (PageTablePTE _ _, _) \<Rightarrow> \<bottom>"

definition
  "invalid_pte_at p \<equiv> \<lambda>s. ptes_of s p = Some InvalidPTE"

definition
  "valid_slots \<equiv> \<lambda>(pte, p) s. wellformed_pte pte \<and>
     (\<forall>level. \<exists>\<rhd>(level, p && ~~ mask pt_bits) s \<longrightarrow> pte_at p s \<and> valid_pte level pte s)"


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

lemma set_asid_pool_cur_sc[wp]:
  "set_asid_pool p a \<lbrace>\<lambda>s. P (cur_sc s)\<rbrace>"
  unfolding set_asid_pool_def by (wpsimp wp: set_object_wp)

lemma set_asid_pool_cur_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  unfolding cur_tcb_def
  by (rule hoare_lift_Pf [where f=cur_thread]; wp)

crunch set_asid_pool
  for arch[wp]: "\<lambda>s. P (arch_state s)"
  (wp: get_object_wp)

lemma set_asid_pool_pts_of [wp]:
  "set_asid_pool p a \<lbrace>\<lambda>s. P (pts_of s)\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_wp)
  apply (erule_tac P=P in subst[rotated])
  apply (rule ext)
  apply (clarsimp simp: opt_map_def obj_at_def split: option.splits)
  done

lemma set_asid_pool_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift_arch; wp set_asid_pool_typ_at)

lemma set_asid_pool_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_objs get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def valid_obj_def)


lemma invs_valid_global_arch_objs:
  "invs s \<Longrightarrow> valid_global_arch_objs s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_state_def)

lemma is_aligned_pt:
  "\<lbrakk> pt_at pt s; pspace_aligned s \<rbrakk> \<Longrightarrow> is_aligned pt pt_bits"
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_alignedD)
  apply (simp add: pt_bits_def pageBits_def)
  done

lemma is_aligned_global_pt:
  "\<lbrakk>pt \<in> riscv_global_pts (arch_state s) level; pspace_aligned s; valid_arch_state s\<rbrakk>
   \<Longrightarrow> is_aligned pt pt_bits"
  by (fastforce simp: valid_arch_state_def valid_global_arch_objs_def intro: is_aligned_pt)

lemma page_table_pte_atI:
  "\<lbrakk> pt_at p s; x < 2^(pt_bits - pte_bits); pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at (p + (x << pte_bits)) s"
  apply (clarsimp simp: obj_at_def pte_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def
                 split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self word_bits_conv bit_simps)
  apply (subgoal_tac "p = (p + (x << pte_bits) && ~~ mask pt_bits)")
   subgoal by (auto simp: bit_simps)
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: bit_simps)
  apply (simp del: bit_shiftl_iff bit_shiftl_word_iff)
  apply (subst upper_bits_unset_is_l2p_64[unfolded word_bits_conv])
   apply (simp add: bit_simps)
  apply (rule shiftl_less_t2n)
   apply (simp add: bit_simps)
  apply (simp add: bit_simps)
  done

lemma page_table_pte_at_diffE:
  "\<lbrakk> pt_at p s; q - p = x << pte_bits;
    x < 2^(pt_bits - pte_bits); pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at q s"
  apply (clarsimp simp: diff_eq_eq add.commute)
  apply (erule(2) page_table_pte_atI)
  done

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
   \<Longrightarrow> pt_at p s"
  apply (drule pt_walk_level)
  apply (frule pt_walk_max_level)
  apply (drule vs_lookup_table_extend ; assumption?)
  apply (fastforce dest!: valid_vspace_objs_strongD simp: pt_at_eq)
  done

lemma vs_lookup_table_pt_at:
  "\<lbrakk> vs_lookup_table level asid vptr s = Some (level, pt_ptr); level \<le> max_pt_level;
     vptr \<in> user_region; valid_vspace_objs s; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> pt_at pt_ptr s"
  apply (subst (asm) vs_lookup_split_max_pt_level_Some, clarsimp+)
  apply (drule (1) pt_walk_pt_at; simp)
  done

lemma pt_lookup_slot_from_level_pte_at:
  "\<lbrakk> pt_lookup_slot_from_level level bot_level pt_ptr vptr (ptes_of s) = Some (level', p);
     vs_lookup_table level asid vptr s = Some (level, pt_ptr); level \<le> max_pt_level;
     vptr \<in> user_region; valid_vspace_objs s; valid_asid_table s; pspace_aligned s \<rbrakk>
  \<Longrightarrow> pte_at p s"
  unfolding pt_lookup_slot_from_level_def
  apply (clarsimp simp add: oreturn_def obind_def split: option.splits)
  apply (rename_tac pt_ptr')
  apply (frule pt_walk_pt_at; assumption?)
  apply (fastforce simp: pte_at_def is_aligned_pt_slot_offset_pte is_aligned_pt)
  done

lemma set_pt_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_pt p pt \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_distinct get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                split: kernel_object.splits arch_kernel_obj.splits)
  done

crunch store_pte
  for arch[wp]: "\<lambda>s. P (arch_state s)"
  and "distinct"[wp]: pspace_distinct

lemma store_pt_asid_pools_of[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (auto simp: obj_at_def opt_map_def elim!: rsubst[where P=P])
  done

lemma store_pte_asid_pools_of[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding store_pte_def by wpsimp

lemma store_pte_vspace_at_asid:
  "store_pte p pte \<lbrace>vspace_at_asid asid pt\<rbrace>"
  unfolding vspace_at_asid_def by (wp vspace_for_asid_lift)

(* FIXME MOVE *)
lemma ko_at_kheap:
  "ko_at ko p s \<Longrightarrow> kheap s p = Some ko"
  unfolding obj_at_def by simp

lemma store_pte_valid_objs [wp]:
  "\<lbrace>(\<lambda>s. wellformed_pte pte) and valid_objs\<rbrace> store_pte p pte \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: store_pte_def set_pt_def bind_assoc set_object_def get_object_def)
  apply (wpsimp simp_del: fun_upd_apply)
  apply (clarsimp simp: valid_objs_def dom_def simp del: fun_upd_apply)
  apply (frule ko_at_kheap)
  apply (fastforce intro!: valid_obj_same_type simp: valid_obj_def split: if_split_asm)
  done

lemma set_pt_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_pt_def get_object_def bind_assoc set_object_def)
  apply (wpsimp)
  apply (subst caps_of_state_after_update, auto elim: obj_at_weakenE)
  done

lemma store_pte_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> store_pte pt p \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp set_object_aligned get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_asid_pool_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_aligned|wpc)+
  including unfold_objects
  apply clarsimp
  done

lemma set_asid_pool_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_distinct|wpc)+
  including unfold_objects
  apply clarsimp
  done


lemma store_pte_valid_pte [wp]:
  "\<lbrace>valid_pte level pt\<rbrace> store_pte p pte \<lbrace>\<lambda>_. valid_pte level pt\<rbrace>"
  by (wp valid_pte_lift store_pte_typ_at)

lemma global_refs_kheap [simp]:
  "global_refs (kheap_update f s) = global_refs s"
  by (simp add: global_refs_def)


lemma set_pt_valid_objs:
  "\<lbrace>(\<lambda>s. \<forall>i. wellformed_pte (pt i)) and valid_objs\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp get_object_wp set_object_valid_objs)
  apply (clarsimp simp: valid_obj_def obj_at_def split: kernel_object.splits arch_kernel_obj.splits)
  done


lemma set_pt_iflive:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp simp: set_pt_def live_def hyp_live_def arch_live_def wp: get_object_wp set_object_iflive)


lemma set_pt_zombies:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
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

lemma set_pt_idle_sc_at[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (idle_sc_at t s)\<rbrace>"
  including unfold_objects
  by (wpsimp wp: set_object_wp simp: set_pt_def)

lemma set_pt_valid_idle:
  "set_pt p pt \<lbrace>\<lambda>s. valid_idle s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_idle_lift simp: set_pt_def)

lemma set_pt_ifunsafe:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  including unfold_objects by (wpsimp simp: set_pt_def)

crunch set_pt
  for global_ref[wp]: "\<lambda>s. P (global_refs s)"
  and idle[wp]: "\<lambda>s. P (idle_thread s)"
  and irq[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

lemma set_pt_valid_global:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)

lemma set_pt_cur:
  "set_pt p pt \<lbrace>cur_tcb\<rbrace>"
  including unfold_objects by (wpsimp simp: set_pt_def)

lemma set_pt_aligned [wp]:
  "set_pt p pt \<lbrace>pspace_aligned\<rbrace>"
  including unfold_objects by (wpsimp simp: set_pt_def)

crunch set_pt
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
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
    (\<lambda>s. (\<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap p asidopt))
                         \<longrightarrow> asidopt = None \<longrightarrow> pt = empty_pt)) \<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def set_pt_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (rename_tac ref slot)
  apply (subst (asm) caps_of_state_after_update[simplified fun_upd_apply[symmetric]])
   apply (clarsimp simp: obj_at_def)
  apply (drule_tac x=r in spec, erule impE, fastforce)
  apply (clarsimp simp: opt_map_def fun_upd_apply split: option.splits)
  done

lemma store_pte_valid_table_caps:
  "\<lbrace> valid_table_caps and (\<lambda>s. valid_caps (caps_of_state s) s) and
     (\<lambda>s. (\<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) asidopt))
                          \<longrightarrow> asidopt = None \<longrightarrow> pte = InvalidPTE)) \<rbrace>
   store_pte p pte
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


crunch set_pt
  for v_ker_map[wp]: "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_pt_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: valid_asid_map_def vspace_at_asid_def)
  apply (rule hoare_lift_Pf2 [where f="arch_state"])
   apply wp+
  done

lemma set_pt_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_pt p pt \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)

lemma pts_of_upd_idem:
  "obj_ref \<noteq> pt_ptr \<Longrightarrow> pts_of (s\<lparr> kheap := (kheap s)(obj_ref := Some ko)\<rparr>) pt_ptr = pts_of s pt_ptr"
  unfolding pt_of_def
  by (clarsimp simp: opt_map_def split: option.splits)

lemma pt_walk_eqI:
  "\<lbrakk> \<forall>level' pt_ptr'.
       level < level'
       \<longrightarrow> pt_walk top_level level' pt_ptr vptr (\<lambda>p. pte_of p pts) = Some (level', pt_ptr')
       \<longrightarrow> pts' pt_ptr' = pts pt_ptr';
     is_aligned pt_ptr pt_bits \<rbrakk>
   \<Longrightarrow> pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p pts')
      = pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p pts)"
  apply (induct top_level arbitrary: pt_ptr; clarsimp)
  apply (subst pt_walk.simps)
  apply (subst (2) pt_walk.simps)
  apply clarsimp
  apply (rule obind_eqI)
   apply (simp (no_asm) add: pte_of_def)
   apply (fastforce simp: obind_def split: option.split)
  apply clarsimp
  apply (rename_tac pte)
  apply (drule_tac x="pptr_from_pte pte" in meta_spec)
  apply (erule meta_impE; simp?)
  apply clarsimp
  apply (subgoal_tac "is_aligned pt_ptr pt_bits \<and> pts' pt_ptr = pts pt_ptr")
   prefer 2
   subgoal by simp
  apply (erule_tac x=level' in allE, simp)
  apply (erule_tac x=pt_ptr' in allE)
  apply (erule impE; assumption?)
  apply (subst pt_walk.simps)
  apply (subgoal_tac "level' < top_level")
   prefer 2
   apply (fastforce dest!: pt_walk_max_level simp: le_less_trans)
  apply (fastforce simp: pte_of_def in_omonad)
  done

lemma valid_vspace_obj_valid_pte_upd:
  "\<lbrakk> valid_vspace_obj level (PageTable pt) s; valid_pte level pte s \<rbrakk>
   \<Longrightarrow> valid_vspace_obj level (PageTable (pt(idx := pte))) s"
  by (clarsimp simp: valid_vspace_obj_def split: if_splits)

lemma pte_of_pt_slot_offset_of_empty_pt:
  "\<lbrakk> pts pt_ptr = Some empty_pt; is_aligned pt_ptr pt_bits \<rbrakk>
   \<Longrightarrow> pte_of (pt_slot_offset level pt_ptr vref) pts = Some InvalidPTE"
  by (clarsimp simp: pte_of_def obind_def is_aligned_pt_slot_offset_pte)

lemma pt_walk_non_empty_ptD:
  "\<lbrakk> pt_walk level bot_level pt_ptr vref (\<lambda>pt. pte_of pt pts) = Some (level', p);
     pts pt_ptr = Some pt; is_aligned pt_ptr pt_bits \<rbrakk>
   \<Longrightarrow> (pt \<noteq> empty_pt \<or> (level' = level \<and> p = pt_ptr))"
  apply (subst (asm) pt_walk.simps)
  apply (case_tac "bot_level < level")
   apply (clarsimp simp: in_omonad)
   apply (prop_tac "v' = InvalidPTE")
    apply (drule_tac vref=vref and level=level in pte_of_pt_slot_offset_of_empty_pt, clarsimp+)
  done

lemma pt_walk_pt_upd_idem:
  "\<lbrakk> \<forall>level' pt_ptr'.
       level < level'
       \<longrightarrow> pt_walk top_level level' pt_ptr vptr (\<lambda>p. pte_of p pts) = Some (level', pt_ptr')
       \<longrightarrow> pt_ptr' \<noteq> obj_ref;
     is_aligned pt_ptr pt_bits \<rbrakk>
   \<Longrightarrow> pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p (pts(obj_ref := pt)))
      = pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p pts)"
  by (rule pt_walk_eqI; auto)

lemma pt_walk_upd_idem:
  "\<lbrakk> \<forall>level' pt_ptr'.
       level < level'
       \<longrightarrow> pt_walk top_level level' pt_ptr vptr (ptes_of s) = Some (level', pt_ptr')
       \<longrightarrow> pt_ptr' \<noteq> obj_ref;
     is_aligned pt_ptr pt_bits \<rbrakk>
   \<Longrightarrow> pt_walk top_level level pt_ptr vptr (ptes_of (s\<lparr>kheap := (kheap s)(obj_ref \<mapsto> ko)\<rparr>))
      = pt_walk top_level level pt_ptr vptr (ptes_of s)"
  by (rule pt_walk_eqI; simp split del: if_split)
     (clarsimp simp: opt_map_def split: option.splits)

lemma pt_walk_pt_None_updD:
  "\<lbrakk> pt_walk top_level level pt_ptr vref (\<lambda>pa. pte_of pa ((pts_of s)(p := None))) =
        Some (level', table_ptr) \<rbrakk>
       \<Longrightarrow> pt_walk top_level level pt_ptr vref (ptes_of s) = Some (level', table_ptr)"
  apply (induct top_level arbitrary: pt_ptr, clarsimp)
  apply (subst pt_walk.simps)
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_splits)
  apply (erule disjE; clarsimp?)
   apply (rule_tac x=v' in exI; clarsimp)
   apply (subst (asm) (3) pte_of_def)
   apply (clarsimp simp: in_omonad split: if_splits)
   apply (simp (no_asm) add: ptes_of_def in_monad obind_def)
   apply (clarsimp split: option.splits simp: pts_of_ko_at obj_at_def)
  apply (drule meta_spec)
  apply (fastforce simp: pte_of_def in_omonad split: if_splits)
  done

lemma ptes_of_pt_None_updD:
  "\<lbrakk> pte_of p' ((pts_of s)(p := None)) = Some pte \<rbrakk>
   \<Longrightarrow> ptes_of s p' = Some pte"
  by (clarsimp simp: opt_map_def pte_of_def in_omonad split: option.splits if_splits)

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
  apply (simp (no_asm) add: vs_lookup_table_def in_omonad)
  apply (rule obind_eqI_full; simp add: pool_for_asid_def)
  apply (rename_tac pool_ptr)
  apply (rule obind_eqI_full; clarsimp)
   apply (erule_tac x=asid_pool_level in allE)
   apply (fastforce simp: pool_for_asid_vs_lookup pool_for_asid_def vspace_for_pool_def obind_def
                          order.not_eq_order_implies_strict)
  apply (rename_tac root)
  apply (rule pt_walk_eqI)
   apply clarsimp
   apply (frule pt_walk_max_level)
   apply (fastforce simp add: vs_lookup_table_def in_omonad asid_pool_level_eq pool_for_asid_def)
  apply (rule vspace_for_pool_is_aligned; fastforce simp add: pool_for_asid_def)
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
     vref \<in> user_region; pspace_aligned s; valid_vspace_objs s; valid_asid_table s;
     unique_table_refs s; valid_vs_lookup s; valid_caps (caps_of_state s) s \<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref (s\<lparr>kheap := (kheap s)(obj_ref \<mapsto> ko)\<rparr>)
      = vs_lookup_table level asid vref s"
  by (subst vs_lookup_table_upd_idem; simp?)
     (fastforce dest: no_loop_vs_lookup_table)

lemma ex_vs_lookup_upd_idem:
  "\<lbrakk> \<exists>\<rhd> (level, p) s;
     pspace_aligned s; valid_vspace_objs s; valid_asid_table s; unique_table_refs s;
     valid_vs_lookup s; valid_caps (caps_of_state s) s \<rbrakk>
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
                   \<Longrightarrow> (ptes' |> pte_ref) slot = (ptes |> pte_ref) slot \<rbrakk>
   \<Longrightarrow> pt_lookup_target level pt_ptr vref ptes' = pt_lookup_target level pt_ptr vref ptes"
  unfolding pt_lookup_target_def
  by (fastforce simp: obind_def opt_map_def split: option.splits)

lemma pt_walk_Some_finds_pt:
  "\<lbrakk> pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p pts) = Some (level, pt_ptr');
     level < top_level; is_aligned pt_ptr pt_bits \<rbrakk>
   \<Longrightarrow> pts pt_ptr \<noteq> None"
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp add: in_omonad split: if_splits)
  apply (fastforce simp: is_PageTablePTE_def pte_of_def in_omonad split: if_splits)
  done

lemma pte_of_pt_slot_offset_upd_idem:
  "\<lbrakk> is_aligned pt_ptr pt_bits; obj_ref \<noteq> pt_ptr \<rbrakk>
   \<Longrightarrow> pte_of (pt_slot_offset level pt_ptr vptr) (pts(obj_ref := pt'))
      = pte_of (pt_slot_offset level pt_ptr vptr) pts"
  unfolding pte_of_def
  by (rule obind_eqI; clarsimp simp: in_omonad)+

lemma pt_lookup_target_pt_eqI:
  "\<lbrakk> \<forall>level' pt_ptr'.
       pt_walk max_pt_level level' pt_ptr vptr (\<lambda>p. pte_of p pts) = Some (level', pt_ptr')
       \<longrightarrow> pts' pt_ptr' = pts pt_ptr';
     is_aligned pt_ptr pt_bits; level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> pt_lookup_target level pt_ptr vptr (\<lambda>p. pte_of p pts')
      = pt_lookup_target level pt_ptr vptr (\<lambda>p. pte_of p pts)"
  apply (simp (no_asm) add: pt_lookup_target_def pt_lookup_slot_from_level_def obind_assoc)
  apply (subgoal_tac "pt_walk max_pt_level level pt_ptr vptr (\<lambda>p. pte_of p pts')
                      = pt_walk max_pt_level level pt_ptr vptr (\<lambda>p. pte_of p pts)")
   prefer 2
   apply (rule pt_walk_eqI; assumption?)
   apply (intro allI impI)
   apply (erule_tac x=level' in allE)
   apply fastforce
  apply (rule obind_eqI, assumption)
  apply (rule obind_eqI; clarsimp)
  apply (rule obind_eqI; clarsimp)
   apply (rename_tac level'' pt_ptr'')
   apply (drule sym)
   apply (frule pt_walk_level)
   apply (erule_tac x=level'' in allE)
   apply (erule_tac x=pt_ptr'' in allE)
   apply clarsimp
   apply (subst pte_of_def)+
   apply (clarsimp simp: obind_def pt_walk_is_aligned split: option.splits)
  apply (rule obind_eqI; clarsimp)
  done

lemma pt_lookup_target_pt_upd_eq:
  "\<lbrakk> \<forall>level' pt_ptr'.
       pt_walk max_pt_level level' pt_ptr vptr (\<lambda>p. pte_of p pts) = Some (level', pt_ptr')
       \<longrightarrow> pt_ptr' \<noteq> obj_ref;
     is_aligned pt_ptr pt_bits; level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> pt_lookup_target level pt_ptr vptr (\<lambda>p. pte_of p (pts(obj_ref := pt')))
      = pt_lookup_target level pt_ptr vptr (\<lambda>p. pte_of p pts)"
  by (rule pt_lookup_target_pt_eqI; clarsimp)

lemma kheap_pt_upd_simp[simp]:
  "((kheap s)(p \<mapsto> ArchObj (PageTable pt)) |> aobj_of |> pt_of)
   = (kheap s |> aobj_of |> pt_of)(p \<mapsto> pt)"
  unfolding aobj_of_def opt_map_def
  by (auto split: kernel_object.split)

lemma valid_global_tablesD:
  "\<lbrakk> valid_global_tables s;
     pt_walk max_pt_level bot_level (riscv_global_pt (arch_state s)) vref (ptes_of s)
     = Some (level, pt_ptr) \<rbrakk>
   \<Longrightarrow> vref \<in> kernel_mappings \<longrightarrow> pt_ptr \<in> riscv_global_pts (arch_state s) level"
  unfolding valid_global_tables_def by (simp add: Let_def riscv_global_pt_def)

lemma riscv_global_pt_aligned[simp]:
  "\<lbrakk> pspace_aligned s ; valid_global_arch_objs s \<rbrakk>
   \<Longrightarrow> is_aligned (riscv_global_pt (arch_state s)) pt_bits"
  apply (clarsimp simp add: valid_global_arch_objs_def)
  apply (rule is_aligned_pt; assumption?)
  apply (fastforce simp: riscv_global_pt_def)
  done

lemma riscv_global_pt_in_global_refs[simp]:
  "valid_global_arch_objs s \<Longrightarrow> riscv_global_pt (arch_state s) \<in> global_refs s"
  unfolding riscv_global_pt_def global_refs_def valid_global_arch_objs_def
  by fastforce

lemma kernel_regionsI:
  "p \<in> kernel_elf_window s \<Longrightarrow> p \<in> kernel_regions s"
  "p \<in> kernel_window s \<Longrightarrow> p \<in> kernel_regions s"
  "p \<in> kernel_device_window s \<Longrightarrow> p \<in> kernel_regions s"
  unfolding kernel_regions_def
  by auto

lemma riscv_global_pts_aligned:
  "\<lbrakk> pt_ptr \<in> riscv_global_pts (arch_state s) level; pspace_aligned s; valid_global_arch_objs s \<rbrakk>
   \<Longrightarrow> is_aligned pt_ptr pt_bits"
  unfolding valid_global_arch_objs_def
  by (fastforce dest: pspace_aligned_pts_ofD simp: pt_at_eq)

(* FIXME MOVE, might break proofs elsewhere *)
lemma if_Some_Some[simp]:
  "((if P then Some v else None) = Some v) = P"
  by simp

lemma user_region_canonical_pptr_base:
  "\<lbrakk> p \<notin> user_region; canonical_address p \<rbrakk> \<Longrightarrow> pptr_base \<le> p"
  using canonical_below_pptr_base_canonical_user word_le_not_less
  by (auto simp add: user_region_def not_le)

lemma kernel_regions_pptr_base:
  "\<lbrakk> p \<in> kernel_regions s; valid_uses s \<rbrakk> \<Longrightarrow> pptr_base \<le> p"
  apply (rule user_region_canonical_pptr_base)
   apply (simp add: valid_uses_def window_defs)
   apply (erule_tac x=p in allE)
   apply auto[1]
  apply (simp add: valid_uses_def window_defs)
  apply (erule_tac x=p in allE)
  apply auto[1]
  done

lemma kernel_regions_in_mappings:
  "\<lbrakk> p \<in> kernel_regions s; valid_uses s \<rbrakk> \<Longrightarrow> p \<in> kernel_mappings"
  apply (frule (1) kernel_regions_pptr_base)
  unfolding kernel_regions_def kernel_elf_window_def valid_uses_def kernel_device_window_def
            kernel_mappings_def kernel_window_def
  by (erule_tac x=p in allE) (auto simp: not_le canonical_below_pptr_base_canonical_user)

lemma set_pt_valid_global_vspace_mappings:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_tables s \<and> p \<notin> global_refs s
        \<and> pspace_aligned s \<and> valid_global_arch_objs s \<and> valid_uses s \<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wpsimp wp: set_object_wp)
  unfolding valid_global_vspace_mappings_def Let_def
  apply (safe; clarsimp; drule (1) bspec; thin_tac "Ball _ _")
   (* we don't care about whether we're in kernel window or kernel_elf_window *)
   apply (all \<open>drule kernel_regionsI, erule option_Some_value_independent\<close>)
   apply (distinct_subgoals)
  apply (subst pt_lookup_target_translate_address_upd_eq; assumption?)
  apply (clarsimp simp: translate_address_def in_omonad)
  apply (rename_tac level p')
  apply (subst pt_lookup_target_pt_upd_eq)
     apply clarsimp
     apply (frule valid_global_tablesD)
      apply assumption
     apply (clarsimp simp: kernel_regions_in_mappings)
     apply (clarsimp simp: global_refs_def)
    apply (fastforce dest: riscv_global_pts_aligned)
   apply fastforce
  apply fastforce
  done

lemma store_pte_valid_global_vspace_mappings:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_tables s \<and> table_base p \<notin> global_refs s
        \<and> pspace_aligned s \<and> valid_global_arch_objs s \<and> valid_uses s \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  unfolding store_pte_def
  by (wpsimp wp: set_pt_valid_global_vspace_mappings)

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
  "\<lbrace>valid_ioc\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_valid_ioc_no_caps get_object_wp)
  by (clarsimp simp: a_type_simps obj_at_def is_tcb is_cap_table
              split: kernel_object.splits arch_kernel_obj.splits)



lemma valid_machine_stateE:
  assumes vm: "valid_machine_state s"
  assumes e: "\<lbrakk>in_user_frame p s
    \<or> underlying_memory (machine_state s) p = 0 \<rbrakk> \<Longrightarrow> E "
  shows E
  using vm
  apply (clarsimp simp: valid_machine_state_def)
  apply (drule_tac x = p in spec)
  apply (rule e)
  apply auto
  done

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

lemma store_word_offs_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> store_word_offs a x w \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma store_word_offs_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> store_word_offs a x w \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)


lemma as_user_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> as_user t m \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma as_user_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> as_user t m \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)

crunch load_word_offs
  for obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"

lemma load_word_offs_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> load_word_offs a x \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma valid_machine_state_heap_updI:
assumes vm : "valid_machine_state s"
assumes tyat : "typ_at type p s"
shows
  " a_type obj = type \<Longrightarrow> valid_machine_state (s\<lparr>kheap := (kheap s)(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: valid_machine_state_def)
  subgoal for p
   apply (rule valid_machine_stateE[OF vm,where p = p])
   apply (elim disjE,simp_all)
   apply (drule(1) in_user_frame_same_type_upd[OF tyat])
    apply simp+
   done
  done

lemma set_pt_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (erule valid_machine_state_heap_updI)
   apply (fastforce simp: obj_at_def a_type_def
                   split: kernel_object.splits arch_kernel_obj.splits)+
  done

crunch set_pt
  for valid_irq_states[wp]: "valid_irq_states"
  (wp: crunch_wps)


(* FIXME: move to ArchInvariants_A *)
lemma valid_asid_table_ran:
  "valid_asid_table s \<Longrightarrow> \<forall>p\<in>ran (asid_table s). asid_pool_at p s"
  unfolding invs_def valid_state_def valid_arch_state_def valid_asid_table_def
  by (fastforce simp: opt_map_def obj_at_def split: option.splits)

lemmas invs_ran_asid_table = invs_valid_asid_table[THEN valid_asid_table_ran]


lemma set_asid_pool_iflive [wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_iflive)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def live_def hyp_live_def)
  done


lemma set_asid_pool_zombies [wp]:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_zombies)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done


lemma set_asid_pool_zombies_state_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_refs_of_def split: option.splits)
  done

lemma set_asid_pool_zombies_state_hyp_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_asid_pool_def wp: get_object_wp set_object_wp)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_hyp_refs_of_def split: option.splits)
  done

lemma set_asid_pool_cdt [wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by wpsimp

lemma set_asid_pool_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  unfolding set_asid_pool_def set_object_def including unfold_objects
  apply wpsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ _ y by (cases y, auto simp: cte_wp_at_cases)
  done

lemma set_asid_pool_valid_mdb [wp]:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_mdb_lift simp: set_asid_pool_def set_object_def)


lemma set_asid_pool_valid_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  by (wpsimp simp: set_asid_pool_def set_object_def get_object_def obj_at_def a_type_simps
             wp: valid_idle_lift)


lemma set_asid_pool_ifunsafe [wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  including unfold_objects
  by (wpsimp simp: set_asid_pool_def)


crunch set_asid_pool
 for global_ref[wp]: "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)


crunch set_asid_pool
  for idle[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)


crunch set_asid_pool
  for irq[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

crunch set_asid_pool
  for valid_irq_states[wp]: "valid_irq_states"
  (wp: crunch_wps)

lemma set_asid_pool_valid_global [wp]:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


crunch set_asid_pool
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

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
   apply (clarsimp simp: pool_for_asid_vs_lookup vspace_for_pool_def in_omonad)
   apply (rule obind_eqI[rotated], fastforce)
   apply (case_tac "pool_ptr = obj_ref"; clarsimp)
    apply (erule_tac x=asid_pool_level in allE)
    apply (fastforce simp: pool_for_asid_vs_lookup)
   apply (fastforce simp: fun_upd_def opt_map_def split: option.splits)
  (* level' \<le> max_pt_level *)
  apply (rule conjI, clarsimp)
  apply (rename_tac pt_ptr level')
   apply (case_tac "pt_ptr = obj_ref")
    apply (fastforce dest: vs_lookup_level)
   apply (rule pte_refs_of_eqI, rule ptes_of_eqI)
   apply (prop_tac "is_aligned pt_ptr pt_bits")
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
     level' \<le> level; vref \<in> user_region; unique_table_refs s; valid_vs_lookup s;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s; valid_caps (caps_of_state s) s \<rbrakk>
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
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p and
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
     apply (fastforce simp: aobjs_of_ako_at_Some obj_at_def fun_upd_apply)
    (* pt_ptr \<noteq> p *)
    apply (clarsimp simp: aobjs_of_ako_at_Some obj_at_def fun_upd_apply)
    apply (erule (1) valid_vspace_obj_same_type, simp)
   (* level \<le> max_pt_level *)
   apply clarsimp
   apply (drule vs_lookup_level, drule vs_lookup_level)
   apply (drule (5) vs_lookup_table_pt_at)
   apply (case_tac "pt_ptr = p"; simp add: aobjs_of_ako_at_Some)
    apply (clarsimp simp: aobjs_of_ako_at_Some obj_at_def fun_upd_apply fun_upd_def)
   apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (clarsimp simp: aobjs_of_ako_at_Some obj_at_def fun_upd_apply
                    simp del: valid_vspace_obj.simps)
   apply (erule (1) valid_vspace_obj_same_type, simp)
  apply (case_tac "bot_level = asid_pool_level")
   apply (clarsimp simp: pool_for_asid_vs_lookup pool_for_asid_def)
  apply (clarsimp simp: vs_lookup_table_def in_omonad asid_pool_level_neq[THEN iffD2] pool_for_asid_def)
  apply (drule pt_walk_pt_None_updD)
  apply (rename_tac pool_ptr root)
  apply (clarsimp simp: vspace_for_pool_def in_omonad fun_upd_apply)
  apply (case_tac "pool_ptr = p"; clarsimp simp: asid_pools_of_ko_at obj_at_def)
   apply (fastforce elim: graph_of_SomeD)
  done

lemma set_asid_pool_vspace_objs_unmap:
  "\<lbrace>valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p and
    valid_asid_table and pspace_aligned\<rbrace>
  set_asid_pool p (ap |` S)  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (wp set_asid_pool_vspace_objs_unmap')
  apply (clarsimp simp: obj_at_def graph_of_restrict_map)
  apply (drule valid_vspace_objsD, assumption, assumption, simp add: obj_at_def in_opt_map_eq)
  by (auto simp: obj_at_def dest!: ran_restrictD)

lemma set_asid_pool_table_caps[wp]:
  "\<lbrace>valid_table_caps\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  apply (simp add: valid_table_caps_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  done

lemma vs_lookup_target_asid_pool_levelI:
  "\<lbrakk> pool_for_asid asid s = Some pool; ako_at (ASIDPool ap) pool s;
     ap (asid_low_bits_of asid) = Some pt_ptr \<rbrakk>
   \<Longrightarrow> vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level, pt_ptr)"
  apply (clarsimp simp: vs_lookup_target_def in_omonad)
  apply (clarsimp simp: pool_for_asid_vs_lookup vspace_for_pool_def vs_lookup_slot_def in_omonad)
  apply (rule_tac x=ap in exI)
  apply (fastforce simp: obj_at_def)
  done

lemma vs_lookup_target_pt_levelI:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, pt_ptr);
     pte_refs_of s (pt_slot_offset level pt_ptr vref) = Some target;
     level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> vs_lookup_target level asid vref s = Some (level, target)"
  by (clarsimp simp: vs_lookup_target_def in_omonad vs_lookup_slot_def asid_pool_level_neq[THEN iffD2])

lemma vs_lookup_target_asid_pool_level_upd_helper:
  "\<lbrakk> graph_of ap \<subseteq> graph_of ap'; kheap s p = Some (ArchObj (ASIDPool ap')); vref \<in> user_region;
     vspace_for_pool pool_ptr asid ((asid_pools_of s)(p \<mapsto> ap)) = Some pt_ptr;
     pool_for_asid asid (s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj (ASIDPool ap))\<rparr>) = Some pool_ptr\<rbrakk>
   \<Longrightarrow> vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level, pt_ptr)"
  apply (clarsimp simp: pool_for_asid_vs_lookup vspace_for_pool_def in_omonad)
  apply (clarsimp split: if_splits)
   apply (rule vs_lookup_target_asid_pool_levelI)
   apply (fastforce simp: pool_for_asid_def obj_at_def dest: graph_of_SomeD)+
  apply (rule vs_lookup_target_asid_pool_levelI
         ; fastforce simp: pool_for_asid_def obj_at_def vs_lookup_target_def in_omonad)
  done

lemma vs_lookup_target_None_upd_helper:
  "\<lbrakk> vs_lookup_table level asid vref (s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj (ASIDPool ap))\<rparr>) =
        Some (level, table_ptr);
     ((\<lambda>pa. pte_of pa ((pts_of s)(p := None))) |> pte_ref) (pt_slot_offset level table_ptr vref)
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
   apply (fastforce simp: asid_pools_of_ko_at obj_at_def  vspace_for_pool_def in_omonad
                    dest!: graph_of_SomeD pt_walk_pt_None_updD
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
  "\<lbrace>valid_vs_lookup and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (wp set_asid_pool_vs_lookup_unmap')
  by (clarsimp simp: obj_at_def
                 elim!: subsetD [OF graph_of_restrict_map])

lemma valid_pte_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pte level pte s = valid_pte level pte s'"
  by (case_tac pte, auto simp add: data_at_def)

lemma set_asid_pool_global_objs [wp]:
  "set_asid_pool p ap \<lbrace>valid_global_objs\<rbrace>"
  by (clarsimp simp: valid_global_objs_def) wp

crunch set_asid_pool
  for v_ker_map[wp]: "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)

lemma set_asid_pool_vspace_objs_unmap_single:
  "\<lbrace>valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p and
    valid_asid_table and pspace_aligned\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  using set_asid_pool_vspace_objs_unmap[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

lemma set_asid_pool_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift set_asid_pool_typ_at)

lemma set_asid_pool_equal_mappings[wp]:
  "\<lbrace>equal_kernel_mappings and
    (\<lambda>s. \<forall>p pt. p \<in> ran ap \<longrightarrow> pts_of s p = Some pt \<longrightarrow> has_kernel_mappings pt s)\<rbrace>
    set_asid_pool p ap
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: equal_kernel_mappings_def)
  apply (drule vspace_for_asid_SomeD)
  apply clarsimp
  apply (case_tac "p = pool_ptr")
  apply (clarsimp simp: equal_kernel_mappings_def has_kernel_mappings_def obj_at_def  opt_map_def
                  split: option.splits if_splits)
   apply (subgoal_tac "pt_ptr \<in> ran ap")
    apply fastforce+
  (* p \<noteq> pool_ptr *)
  apply (clarsimp simp: equal_kernel_mappings_def has_kernel_mappings_def obj_at_def  opt_map_def
                  split: option.splits if_splits)
  apply (subgoal_tac "vspace_for_asid asid s = Some pt_ptr")
   apply (fastforce elim: vspace_for_asid_SomeI simp: opt_map_def)+
  done

lemma translate_address_asid_pool_upd:
  "pts_of s p = None
   \<Longrightarrow> translate_address pt_ptr vref
        (\<lambda>pa. pte_of pa ((kheap s)(p \<mapsto> ArchObj (ASIDPool ap)) |> aobj_of |> pt_of))
      = translate_address pt_ptr vref (ptes_of s)"
  by simp

lemma ko_atasid_pool_pts_None:
  "ako_at (ASIDPool pool) p s \<Longrightarrow> pts_of s p = None"
  by (clarsimp simp: opt_map_def obj_at_def split: option.splits)

lemma set_asid_pool_valid_global_vspace_mappings[wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_wp)
  apply (simp only: valid_global_vspace_mappings_def Let_def) (* prevent simp loop *)
  apply (clarsimp simp: translate_address_asid_pool_upd ko_atasid_pool_pts_None)
  done

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
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
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

lemma set_asid_pool_sc_at_pred_n[wp]:
  "set_asid_pool p ap \<lbrace>\<lambda>s. Q (sc_at_pred_n N proj P p' s)\<rbrace>"
  including unfold_objects
  by (wpsimp simp: set_asid_pool_def sc_at_pred_n_def wp: set_object_wp)

lemma set_asid_pool_replies_with_sc[wp]:
  "set_asid_pool p ap \<lbrace>\<lambda>s. P (replies_with_sc s)\<rbrace>"
  by (wp replies_with_sc_lift)

lemma set_asid_pool_replies_blocked[wp]:
  "set_asid_pool p ap \<lbrace>\<lambda>s. P (replies_blocked s)\<rbrace>"
  by (wp replies_blocked_lift)

lemma set_asid_pool_valid_replies[wp]:
  "set_asid_pool p ap \<lbrace>valid_replies\<rbrace>"
  by (wp|wps)+

lemma set_asid_pool_sch_act[wp]:
  "set_asid_pool p ap \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace>"
  including unfold_objects by (wpsimp simp: set_asid_pool_def wp: set_object_wp)

lemma set_asid_pool_fault_tcbs_valid_states_except_set[wp]:
  "set_asid_pool p ap \<lbrace>fault_tcbs_valid_states_except_set T\<rbrace>"
  by (wp fault_tcbs_valid_states_lift)

lemma set_asid_pool_cur_sc_tcb[wp]:
  "set_asid_pool p ap \<lbrace>cur_sc_tcb\<rbrace>"
  unfolding cur_sc_tcb_def by wp_pre (wpsimp|wps)+

lemma set_asid_pool_invs_restrict:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and (\<lambda>s. \<exists>a. asid_table s a = Some p) and
    valid_asid_table and pspace_aligned\<rbrace>
   set_asid_pool p (ap |` S)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def
                   valid_arch_caps_def valid_asid_map_def)
  apply (wp valid_irq_node_typ set_asid_pool_typ_at
            set_asid_pool_vspace_objs_unmap  valid_irq_handlers_lift
            set_asid_pool_vs_lookup_unmap)
  apply (clarsimp simp: equal_kernel_mappings_def)
  apply (rename_tac s pt_ptr hi_bits pt)
  apply (clarsimp dest!: ran_restrictD)
  apply (rename_tac lo_bits)
  (* we can build an asid that resolves to pt_ptr, vref is irrelevant for asid_pool_level *)
  apply (prop_tac "vs_lookup_target asid_pool_level
                      ((ucast hi_bits << asid_low_bits) || ucast lo_bits)
                      0 s = Some (asid_pool_level, pt_ptr)")
   apply (clarsimp simp: vs_lookup_target_def in_omonad)
   apply (rule_tac x=p in exI)
   apply (clarsimp simp: vspace_for_pool_def vs_lookup_slot_def in_omonad obj_at_def
                         pool_for_asid_vs_lookup pool_for_asid_def
                         constructed_asid_high_bits_of constructed_asid_low_bits_of)
  apply (drule vspace_for_asid_from_lookup_target; simp)
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

lemma set_asid_pool_invs_unmap:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and (\<lambda>s. \<exists>a. asid_table s a = Some p) and
    valid_asid_table and pspace_aligned\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. invs\<rbrace>"
  using set_asid_pool_invs_restrict[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

lemma pte_at_typ_at_lift:
  assumes aa_type: "\<And>T p. f \<lbrace>typ_at (AArch T) p\<rbrace>"
  shows "f \<lbrace>pte_at p\<rbrace>"
  unfolding pte_at_def
  by (wpsimp wp: aa_type)

lemma valid_slots_typ_at:
  assumes x: "\<And>T p. f \<lbrace>typ_at (AArch T) p\<rbrace>"
  assumes y: "\<And>P. f \<lbrace> \<lambda>s. P (vs_lookup s) \<rbrace>"
  shows "\<lbrace>valid_slots m\<rbrace> f \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  unfolding valid_slots_def
  apply (cases m; clarsimp)
  apply (wpsimp wp: hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift' assms
                    valid_pte_lift pte_at_typ_at_lift)
  apply fastforce
  done

lemma pool_for_asid_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
  pool_for_asid asid (arch_state_update f s) = pool_for_asid asid s"
  by (simp add: pool_for_asid_def obind_def split: option.splits)

lemma vs_lookup_table_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_table level asid vref (arch_state_update f s) = vs_lookup_table level asid vref s"
  by (simp add: vs_lookup_table_def obind_def split: option.splits)

lemma vs_lookup_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup (arch_state_update f s) = vs_lookup s"
  by (rule ext)+ simp

lemma vs_lookup_slot_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_slot level asid vref (arch_state_update f s) = vs_lookup_slot level asid vref s"
  by (simp add: vs_lookup_slot_def obind_def split: option.splits)

lemma vs_lookup_target_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_target level asid vref (arch_state_update f s) = vs_lookup_target level asid vref  s"
  by (simp add: vs_lookup_target_def obind_def split: option.splits)

lemma vs_lookup_pages_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
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

lemma set_pt_has_kernel_mappings:
  "\<lbrace>\<lambda>s. p \<noteq> riscv_global_pt (arch_state s) \<and> has_kernel_mappings pt s \<rbrace>
   set_pt p pt'
   \<lbrace>\<lambda>_. has_kernel_mappings pt \<rbrace>"
  unfolding has_kernel_mappings_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)
    apply (rule hoare_lift_Pf2[where f="\<lambda>s. riscv_global_pt (arch_state s)"])
     apply (wpsimp wp: set_pt_pts_of)+
  done

lemma set_pt_equal_kernel_mappings:
  "\<lbrace>\<lambda>s. equal_kernel_mappings s
        \<and> ((\<exists>asid. vspace_for_asid asid s = Some p) \<longrightarrow> has_kernel_mappings pt s)
        \<and> p \<noteq> riscv_global_pt (arch_state s) \<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  unfolding equal_kernel_mappings_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' vspace_for_asid_lift set_pt_pts_of
                 set_pt_has_kernel_mappings)

lemma has_kernel_mappings_index_upd_idem:
  "\<lbrakk> has_kernel_mappings pt s; idx \<notin> kernel_mapping_slots \<rbrakk>
   \<Longrightarrow> has_kernel_mappings (pt(idx := pte)) s"
  unfolding has_kernel_mappings_def
  by auto

(* We only affect kernel mapping slots of not-yet-mapped page tables, in particular when copying
   global mappings for a root page table. For preserving validity of mapped tables, we use this
   form. *)
lemma store_pte_equal_kernel_mappings_no_kernel_slots:
  "\<lbrace>\<lambda>s. equal_kernel_mappings s
        \<and> ((\<exists>asid. vspace_for_asid asid s = Some (table_base p))
                   \<longrightarrow> table_index p \<notin> kernel_mapping_slots)
        \<and> table_base p \<noteq> riscv_global_pt (arch_state s) \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  unfolding store_pte_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_pt_equal_kernel_mappings)
  apply (fastforce simp: obj_at_def equal_kernel_mappings_def pts_of_ko_at
                   intro: has_kernel_mappings_index_upd_idem)
  done

lemma store_pte_state_refs_of[wp]:
  "store_pte ptr val \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wp get_object_wp set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule ext, clarsimp simp: state_refs_of_def obj_at_def)
  done

lemma store_pte_state_hyp_refs_of[wp]:
  "store_pte ptr val \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wp get_object_wp set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule ext, clarsimp simp: state_hyp_refs_of_def obj_at_def)
  done

lemma asid_pools_of_pt_None_upd_idem:
  "pt_at p s \<Longrightarrow> (asid_pools_of s)(p := None) = (asid_pools_of s)"
  by (rule ext)
     (clarsimp simp: opt_map_def obj_at_def )

lemma store_pte_valid_asid_table[wp]:
  "\<lbrace> valid_asid_table \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_asid_table \<rbrace>"
  supply fun_upd_apply[simp del]
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp hoare_vcg_imp_lift' hoare_vcg_all_lift)
  apply (subst asid_pools_of_pt_None_upd_idem, auto simp: obj_at_def)
  done

crunch store_pte
  for iflive[wp]: if_live_then_nonz_cap
  and zombies_final[wp]: zombies_final
  and valid_mdb[wp]: valid_mdb
  and valid_ioc[wp]: valid_ioc
  and valid_idle[wp]: valid_idle
  and only_idle[wp]: only_idle
  and if_unsafe_then_cap[wp]: if_unsafe_then_cap
  and valid_global_refs[wp]: valid_global_refs
  and valid_irq_node[wp]: valid_irq_node
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
  and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: set_pt_zombies set_pt_ifunsafe set_object_wp
       set_pt_valid_global valid_irq_node_typ valid_irq_handlers_lift set_pt_cur)

lemma store_pte_valid_global_tables:
  "\<lbrace> valid_global_tables and valid_global_arch_objs and valid_global_vspace_mappings
     and (\<lambda>s. table_base p \<notin> global_refs s) \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_global_tables \<rbrace>"
  unfolding store_pte_def set_pt_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (simp (no_asm) add: valid_global_tables_def Let_def)
  apply (rule conjI)
   apply clarsimp
   apply (subst (asm) pt_walk_pt_upd_idem)
     apply (fastforce simp: global_refs_def dest: valid_global_tablesD[simplified riscv_global_pt_def])
    apply (fastforce dest: valid_global_vspace_mappings_aligned[simplified riscv_global_pt_def])
   apply (fastforce simp: valid_global_tables_def Let_def)
  apply (clarsimp simp: valid_global_tables_def Let_def fun_upd_apply split: if_splits)
  apply (fastforce dest: riscv_global_pt_in_global_refs simp: riscv_global_pt_def global_refs_def)
  done

lemma store_pte_valid_global_arch_objs[wp]:
  "store_pte p pte \<lbrace> valid_global_arch_objs \<rbrace>"
  unfolding store_pte_def set_pt_def
  by (wpsimp wp: set_object_wp)
     (clarsimp simp: valid_global_arch_objs_def obj_at_def)

lemma store_pte_unique_table_refs[wp]:
  "store_pte p pte \<lbrace> unique_table_refs \<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: unique_table_refs_def)
  apply (subst (asm) caps_of_state_after_update[folded fun_upd_def], simp add: obj_at_def)+
  apply blast
  done

lemma store_pte_unique_table_caps[wp]:
  "store_pte p pte \<lbrace> unique_table_caps \<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: unique_table_caps_def)
  apply (subst (asm) caps_of_state_after_update[folded fun_upd_def], fastforce simp: obj_at_def)+
  apply blast
  done

lemma store_pte_valid_asid_pool_caps[wp]:
  "store_pte p pte \<lbrace> valid_asid_pool_caps \<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (subst caps_of_state_after_update[folded fun_upd_def], fastforce simp: obj_at_def)+
  apply assumption
  done

lemma store_pte_PagePTE_valid_vspace_objs:
  "\<lbrace> valid_vspace_objs and pspace_aligned and valid_asid_table
     and K (pte = PagePTE ppn attr rights)
     and (\<lambda>s. \<forall>level. \<exists>\<rhd> (level, table_base p) s \<longrightarrow> valid_pte level pte s)\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def
  supply valid_pte.simps[simp del]
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' valid_vspace_obj_lift
                    store_pte_non_PageTablePTE_vs_lookup)
  apply (rule conjI; clarsimp)
   apply (rename_tac level' slot pte' ao pt)
   apply (drule (1) level_of_slotI)
   apply (case_tac "slot = table_base p"; clarsimp simp del: valid_vspace_obj.simps)
   apply (drule vs_lookup_level)
   apply (clarsimp)
   apply (prop_tac "valid_vspace_obj level' (PageTable pt) s")
    apply fastforce
   apply fastforce
  apply (rename_tac level' slot pte' ao pt)
  apply (clarsimp simp: vs_lookup_slot_def)
  apply (case_tac "slot = table_base p"; clarsimp simp del: valid_vspace_obj.simps)
  apply (drule vs_lookup_level)
  apply (clarsimp)
  apply (prop_tac "valid_vspace_obj level' (PageTable pt) s")
   apply fastforce
  apply fastforce
  done

lemma store_pte_InvalidPTE_valid_vs_lookup:
  "\<lbrace> valid_vs_lookup
     and pspace_aligned and valid_vspace_objs and valid_asid_table and unique_table_refs
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and K (pte = InvalidPTE) \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_vs_lookup \<rbrace>"
  unfolding store_pte_def set_pt_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (simp (no_asm) add: valid_vs_lookup_def)
  apply clarsimp
  apply (subst caps_of_state_after_update[folded fun_upd_def], simp add: obj_at_def)
  apply (rename_tac obj_ref)
  (* interesting case is if table_base p was reachable before the update *)
  apply (case_tac "\<forall>level. vs_lookup_table level asid vref s \<noteq> Some (level, table_base p)")
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
  (* the interesting operations all happen when level \<le> max_pt_level; get asid_pool_level out of
     the way first *)
  apply (prop_tac "level' \<le> max_pt_level")
   apply (rule ccontr, clarsimp simp: not_le)
   apply (frule (1) vs_lookup_asid_pool)
   apply (clarsimp simp: asid_pools_of_ko_at)
   apply (fastforce simp: obj_at_def)
  apply (case_tac "level = asid_pool_level")
   apply clarsimp
   (* FIXME RISCV there is a property hidden in here about vs_lookup_target for asid_pool_level,
      repeating some of the pattern seen in vs_lookup_target_unreachable_upd_idem *)
   apply (clarsimp simp: pool_for_asid_vs_lookup vspace_for_pool_def in_omonad)
   apply (rename_tac pool_ptr pool)
   apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (prop_tac "pool_for_asid asid s = Some pool_ptr")
    apply (fastforce simp: pool_for_asid_def)
   apply (prop_tac "vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level, obj_ref)")
    apply (clarsimp simp: vs_lookup_target_def in_omonad)
    apply (rule_tac x=pool_ptr in exI)
    apply (fastforce simp: pool_for_asid_vs_lookup vspace_for_pool_def vs_lookup_slot_def in_omonad)
   apply (fastforce dest: valid_vs_lookupD simp: valid_vs_lookup_def)
  apply clarsimp
  (* now we are looking at page tables only; we can extend or truncate our previous lookup,
     but nowhere in seL4 do we do both in one step
     we also now know asid \<noteq> 0 *)

  (* updating deeper than where we can find table_base p has no effect *)
  apply (case_tac "level' \<le> level")
   apply (drule vs_lookup_level, drule (3) vs_lookup_table_fun_upd_deep_idem; assumption?)
   apply (prop_tac "is_aligned table_ptr pt_bits")
    apply (fastforce elim!: vs_lookup_table_is_aligned)
   apply (clarsimp simp: in_omonad fun_upd_apply pte_of_def split: if_splits)
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

  (* split both lookups down to table_base p *)
  apply (drule_tac level=level and level'=level' in vs_lookup_splitD)
    apply simp
   apply (fastforce intro: less_imp_le)
  apply clarsimp
  apply (rename_tac pt_ptr)
  (* update now occurs in pt_walk stage *)
  apply (drule (1) vs_lookup_table_fun_upd_deep_idem; assumption?; simp)
  apply clarsimp
  (* handle the actual update, happening on next step of pt_walk *)
  apply (subst (asm) pt_walk.simps, clarsimp simp: in_omonad split: if_splits)
  apply (rename_tac pte')
  apply (erule disjE; clarsimp)
  apply (subst (asm) (2) pte_of_def)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pt')
  apply (clarsimp simp: fun_upd_apply)
  apply (case_tac "table_index (pt_slot_offset level' (table_base p) vref) = table_index p"; clarsimp)
  (* staying on old path; we can't hit table_base p again *)
  (* this transform copied from elsewhere, FIXME RISCV might be useful to extract *)
  apply (subst (asm) pt_walk_pt_upd_idem; simp?)
   apply clarsimp
   apply (rename_tac level'')
   apply (prop_tac "pt_walk level' level'' (table_base p) vref (ptes_of s) = Some (level'', table_base p)")
    apply (subst pt_walk.simps)
    apply clarsimp
    apply (prop_tac "level'' < level'")
     apply (drule pt_walk_max_level)
     apply (simp add: bit0.leq_minus1_less)
    apply (clarsimp simp: in_omonad obj_at_def)
    apply (rule_tac x="(pt (table_index (pt_slot_offset level' (table_base p) vref)))" in exI)
    apply clarsimp
    apply (clarsimp simp: ptes_of_def in_omonad)
   apply (prop_tac "level'' < level'")
    apply (drule pt_walk_max_level)
    apply (simp add: bit0.leq_minus1_less)
   apply (prop_tac "vs_lookup_table level'' asid vref s = Some (level'', table_base p)")
    apply (erule (2) vs_lookup_table_extend)
   apply (drule (1) no_loop_vs_lookup_table; simp?)
  (* pt_walk is now on pts_of s, can stitch it back together into a vs_lookup_table *)
  (* FIXME RISCV again useful transform from elsewhere *)
  apply (prop_tac "pt_walk level' level (table_base p) vref (ptes_of s) = Some (level, table_ptr)")
   apply (subst pt_walk.simps)
   apply clarsimp
   apply (clarsimp simp: in_omonad obj_at_def)
   apply (rule_tac x="(pt (table_index (pt_slot_offset level' (table_base p) vref)))" in exI)
   apply clarsimp
   apply (clarsimp simp: ptes_of_def in_omonad)
  apply (prop_tac "vs_lookup_table level asid vref s = Some (level, table_ptr)")
   apply (erule (2) vs_lookup_table_extend)
  (* now specifically to vs_lookup_target reconstruction, we get through pte_of ref_of stuff *)
  apply (subst (asm) pte_of_def)
  apply (clarsimp simp: in_omonad fun_upd_apply)
  apply (prop_tac "is_aligned table_ptr pt_bits")
   apply (fastforce elim!: vs_lookup_table_is_aligned)
  apply (clarsimp split: if_splits)
   apply (prop_tac "level' = level")
    apply (drule no_loop_vs_lookup_table; simp?; blast)
   apply clarsimp
  apply (drule_tac level=level in vs_lookup_target_pt_levelI; assumption?)
   apply (fastforce simp: in_omonad ptes_of_def obj_at_def)
  apply (drule valid_vs_lookupD; assumption?; clarsimp)
  done

lemma table_index_slot_offset_inj:
  "\<lbrakk> table_index (pt_slot_offset level (table_base p) vref) = table_index p;
     level \<le> max_pt_level; is_aligned p pte_bits \<rbrakk>
   \<Longrightarrow> pt_slot_offset level (table_base p) vref = p"
  apply (simp add: pt_slot_offset_def is_aligned_nth)
  apply (prop_tac "table_base p && (pt_index level vref << pte_bits) = 0")
   apply word_bitwise
   apply (simp add: bit_simps pt_index_def word_size)
  apply (simp add: word_plus_and_or_coroll)
  apply word_bitwise
  apply (drule max_pt_level_enum)
  by (auto simp: pt_bits_left_def pt_index_def word_size bit_simps)

lemma store_pte_non_InvalidPTE_valid_vs_lookup:
  "\<lbrace> valid_vs_lookup
     and pspace_aligned and valid_vspace_objs and valid_asid_table and unique_table_refs
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and (\<lambda>s. \<forall>level asid vref.
                 vs_lookup_table level asid vref s = Some (level, table_base p)
                      \<longrightarrow> vref \<in> user_region
                      \<longrightarrow> pt_slot_offset level (table_base p) vref = p
                      \<longrightarrow> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some empty_pt)
                         \<and> the (pte_ref pte) \<noteq> table_base p
                         \<and> (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                     obj_refs cap = {the (pte_ref pte)} \<and>
                                     vs_cap_ref cap = Some (asid, vref_for_level vref level))) \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_vs_lookup \<rbrace>"
  unfolding store_pte_def set_pt_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (simp (no_asm) add: valid_vs_lookup_def)
  apply clarsimp
  apply (subst caps_of_state_after_update[folded fun_upd_def], simp add: obj_at_def)
  apply (rename_tac obj_ref)
  (* interesting case is if table_base p was reachable before the update *)
  apply (case_tac "\<forall>level. vs_lookup_table level asid vref s \<noteq> Some (level, table_base p)")
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
  (* the interesting operations all happen when level \<le> max_pt_level; get asid_pool_level out of
     the way first *)
  apply (prop_tac "level' \<le> max_pt_level")
   apply (rule ccontr, clarsimp simp: not_le)
   apply (frule (1) vs_lookup_asid_pool)
   apply (clarsimp simp: asid_pools_of_ko_at)
   apply (fastforce simp: obj_at_def)
  apply (case_tac "level = asid_pool_level")
   apply clarsimp
   (* FIXME RISCV there is a property hidden in here about vs_lookup_target for asid_pool_level,
      repeating some of the pattern seen in vs_lookup_target_unreachable_upd_idem *)
   apply (clarsimp simp: pool_for_asid_vs_lookup vspace_for_pool_def in_omonad)
   apply (rename_tac pool_ptr pool)
   apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (prop_tac "pool_for_asid asid s = Some pool_ptr")
    apply (fastforce simp: pool_for_asid_def)
   apply (prop_tac "vs_lookup_target asid_pool_level asid vref s = Some (asid_pool_level, obj_ref)")
    apply (clarsimp simp: vs_lookup_target_def in_omonad)
    apply (rule_tac x=pool_ptr in exI)
    apply (fastforce simp: pool_for_asid_vs_lookup vspace_for_pool_def vs_lookup_slot_def in_omonad)
   apply (fastforce dest: valid_vs_lookupD simp: valid_vs_lookup_def)
  apply clarsimp
  (* now we are looking at page tables only; we can extend or truncate our previous lookup,
     but nowhere in seL4 do we do both in one step
     we also now know asid \<noteq> 0 *)

  (* updating deeper than where we can find table_base p has no effect *)
  apply (case_tac "level' \<le> level")
   apply (drule vs_lookup_level, drule (3) vs_lookup_table_fun_upd_deep_idem; assumption?)
   apply (prop_tac "is_aligned table_ptr pt_bits")
    apply (fastforce elim!: vs_lookup_table_is_aligned)
   apply (clarsimp simp: in_omonad fun_upd_apply pte_of_def split: if_splits)
     apply (drule (2) table_index_slot_offset_inj, simp)
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

  (* split both lookups down to table_base p *)
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
  (* handle the actual update, happening on next step of pt_walk *)
  apply (subst (asm) pt_walk.simps, clarsimp simp: in_omonad split: if_splits)
  apply (rename_tac pte')
  apply (erule disjE; clarsimp)
  apply (subst (asm) (2) pte_of_def)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pt')
  apply (clarsimp simp: fun_upd_apply)
  apply (case_tac "table_index (pt_slot_offset level' (table_base p) vref) = table_index p"; clarsimp)
   prefer 2
   (* staying on old path; we can't hit table_base p again *)
   (* this transform copied from elsewhere, FIXME RISCV might be useful to extract *)
   apply (subst (asm) pt_walk_pt_upd_idem; simp?)
    apply clarsimp
    apply (rename_tac level'')
    apply (prop_tac "pt_walk level' level'' (table_base p) vref (ptes_of s) = Some (level'', table_base p)")
     apply (subst pt_walk.simps)
     apply clarsimp
     apply (prop_tac "level'' < level'")
      apply (drule pt_walk_max_level)
      apply (simp add: bit0.leq_minus1_less)
     apply (clarsimp simp: in_omonad obj_at_def)
     apply (rule_tac x="(pt (table_index (pt_slot_offset level' (table_base p) vref)))" in exI)
     apply clarsimp
     apply (clarsimp simp: ptes_of_def in_omonad)
    apply (prop_tac "level'' < level'")
     apply (drule pt_walk_max_level)
     apply (simp add: bit0.leq_minus1_less)
    apply (prop_tac "vs_lookup_table level'' asid vref s = Some (level'', table_base p)")
     apply (erule (2) vs_lookup_table_extend)
    apply (drule (1) no_loop_vs_lookup_table; simp?)
   (* pt_walk is now on pts_of s, can stitch it back together into a vs_lookup_table *)
   (* FIXME RISCV again useful transform from elsewhere *)
   apply (prop_tac "pt_walk level' level (table_base p) vref (ptes_of s) = Some (level, table_ptr)")
    apply (subst pt_walk.simps)
    apply clarsimp
    apply (clarsimp simp: in_omonad obj_at_def)
    apply (rule_tac x="(pt (table_index (pt_slot_offset level' (table_base p) vref)))" in exI)
    apply clarsimp
    apply (clarsimp simp: ptes_of_def in_omonad)
   apply (prop_tac "vs_lookup_table level asid vref s = Some (level, table_ptr)")
    apply (erule (2) vs_lookup_table_extend)
   (* now specifically to vs_lookup_target reconstruction, we get through pte_of ref_of stuff *)
   apply (subst (asm) pte_of_def)
   apply (clarsimp simp: in_omonad fun_upd_apply)
   apply (prop_tac "is_aligned table_ptr pt_bits")
    apply (fastforce elim!: vs_lookup_table_is_aligned)
   apply (clarsimp split: if_splits)
    apply (prop_tac "level' = level")
     apply (drule no_loop_vs_lookup_table; simp?; blast)
    apply clarsimp
   apply (drule_tac level=level in vs_lookup_target_pt_levelI; assumption?)
    apply (fastforce simp: in_omonad ptes_of_def obj_at_def)
   apply (drule valid_vs_lookupD; assumption?; clarsimp)
  (* we could not have arrived at our new empty table through a non-empty table and from
     precondition, we are not creating a loop *)
  apply (drule_tac pt=empty_pt in pt_walk_non_empty_ptD; simp add: in_omonad fun_upd_apply)
   apply (cases pte; clarsimp simp: pptr_from_pte_def)
   apply (drule (2) table_index_slot_offset_inj, simp)
  apply (clarsimp simp: in_omonad pte_of_def)
  apply (cases pte; clarsimp)
  apply (fastforce simp: pptr_from_pte_def in_omonad fun_upd_apply
                   intro!: table_index_slot_offset_inj)
  done

(* NOTE: should be able to derive the (pte_ref pte) \<noteq> table_base p) from
   the (pte_ref pte) being unreachable anywhere in the original state
   (this should come from having an unmapped cap to it) *)
lemma store_pte_PageTablePTE_valid_vspace_objs:
  "\<lbrace> valid_vspace_objs
     and pspace_aligned and valid_asid_table and unique_table_refs and valid_vs_lookup
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and K (is_PageTablePTE pte)
     and (\<lambda>s. \<forall>level. \<exists>\<rhd> (level, table_base p) s
                      \<longrightarrow> valid_pte level pte s \<and> pts_of s (the (pte_ref pte)) = Some empty_pt
                         \<and> the (pte_ref pte) \<noteq> table_base p) \<rbrace>
   store_pte p pte
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
   apply simp
  apply (drule vs_lookup_level)
  (* if table_base p is unreachable, we are not updating anything relevant *)
  apply (case_tac "\<forall>level. vs_lookup_table level asid vref s \<noteq> Some (level, table_base p)")
   apply (subst (asm) vs_lookup_table_unreachable_upd_idem; simp?)
   apply (fastforce simp: fun_upd_apply valid_vspace_objs_def split: if_splits)
  (* we are changing the reachable page table at table_base p *)
  supply valid_vspace_obj.simps[simp del]
  apply clarsimp
  apply (rename_tac level')
  apply (prop_tac "valid_pte level' pte s", fastforce)
  (* updating deeper than where we can find table_base p has no effect *)
  apply (case_tac "level' \<le> level")
   apply (drule vs_lookup_level, drule (3) vs_lookup_table_fun_upd_deep_idem; assumption?)
   apply (clarsimp simp: fun_upd_apply split: if_splits)
    apply (prop_tac "level' = level", fastforce dest: no_loop_vs_lookup_table)
    apply (rule valid_vspace_obj_valid_pte_upd; simp?)
    apply (clarsimp simp: valid_vspace_objs_def aobjs_of_ako_at_Some)
   apply (clarsimp simp: valid_vspace_objs_def aobjs_of_ako_at_Some)
  (* we are updating at table_base p, which is within the original lookup path *)
  apply (clarsimp simp: not_le)
  (* to use vs_lookup_splitD, need asid_pool_level taken care of *)
  apply (case_tac "level' = asid_pool_level")
   apply (clarsimp simp: pool_for_asid_vs_lookup)
   apply (drule (1) pool_for_asid_validD)
   apply (clarsimp simp: asid_pools_of_ko_at obj_at_def)
  apply clarsimp
  (* split both lookups down to table_base p *)
  apply (drule vs_lookup_level)
  apply (drule_tac level=level in vs_lookup_splitD; simp?)
   apply (fastforce intro: less_imp_le)
  apply clarsimp
  apply (rename_tac pt_ptr)
  (* update now occurs in pt_walk stage *)
  apply (drule (1) vs_lookup_table_fun_upd_deep_idem; assumption?; simp)
  apply (prop_tac "valid_pte level' pte s \<and> pts_of s (the (pte_ref pte)) = Some empty_pt
                   \<and> the (pte_ref pte) \<noteq> table_base p", fastforce)
  (* handle the actual update, happening on next step of pt_walk *)
  apply (subst (asm) pt_walk.simps, clarsimp simp: in_omonad split: if_splits)
  apply (rename_tac pte')
  apply (erule disjE; clarsimp)
  apply (clarsimp simp: fun_upd_apply)
  apply (subst (asm) pte_of_def)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pt')
  apply (clarsimp simp: fun_upd_apply)
  apply (case_tac "table_index (pt_slot_offset level' (table_base p) vref) = table_index p"; clarsimp)
   prefer 2
   (* staying on old path; we can't hit table_base p again *)
   (* this transform copied from elsewhere, FIXME RISCV might be useful to extract *)
   apply (subst (asm) pt_walk_pt_upd_idem; simp?)
    apply clarsimp
    apply (rename_tac level'')
    apply (prop_tac "pt_walk level' level'' (table_base p) vref (ptes_of s) = Some (level'', table_base p)")
     apply (subst pt_walk.simps)
     apply clarsimp
     apply (prop_tac "level'' < level'")
      apply (drule pt_walk_max_level)
      apply (simp add: bit0.leq_minus1_less)
     apply (clarsimp simp: in_omonad obj_at_def)
     apply (rule_tac x="(pt (table_index (pt_slot_offset level' (table_base p) vref)))" in exI)
     apply clarsimp
     apply (clarsimp simp: ptes_of_def in_omonad)
    apply (prop_tac "level'' < level'")
     apply (drule pt_walk_max_level)
     apply (simp add: bit0.leq_minus1_less)
    apply (prop_tac "vs_lookup_table level'' asid vref s = Some (level'', table_base p)")
     apply (erule (2) vs_lookup_table_extend)
    apply (drule (1) no_loop_vs_lookup_table; simp?)
   (* pt_walk is now on pts_of s, can stitch it back together into a vs_lookup_table *)
   (* FIXME RISCV again useful transform from elsewhere *)
   apply (prop_tac "pt_walk level' level (table_base p) vref (ptes_of s) = Some (level, p')")
    apply (subst pt_walk.simps)
    apply clarsimp
    apply (clarsimp simp: in_omonad obj_at_def)
    apply (rule_tac x="(pt (table_index (pt_slot_offset level' (table_base p) vref)))" in exI)
    apply clarsimp
    apply (clarsimp simp: ptes_of_def in_omonad)
   apply (prop_tac "vs_lookup_table level asid vref s = Some (level, p')")
    apply (erule (2) vs_lookup_table_extend)
   (* p' can't equal table_base p since we see it earlier in the lookup *)
   apply (prop_tac "p' \<noteq> table_base p")
    apply clarsimp
    apply (drule (1) no_loop_vs_lookup_table, simp+)
   (* finally can use valid_vspace_objs *)
   apply (clarsimp simp: valid_vspace_objs_def)
  (* we could not have arrived at our new empty table through a non-empty table and from
     precondition, we are not creating a loop *)
  apply (drule_tac pt=empty_pt in pt_walk_non_empty_ptD; simp add: in_omonad fun_upd_apply)
   apply (cases pte; clarsimp simp: pptr_from_pte_def)
  apply clarsimp
  apply (cases pte; clarsimp simp: pptr_from_pte_def in_omonad valid_vspace_obj.simps)
  done

lemma store_pte_valid_vspace_objs:
  "\<lbrace> valid_vspace_objs
     and pspace_aligned and valid_asid_table and unique_table_refs and valid_vs_lookup
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and (\<lambda>s. \<forall>level. \<exists>\<rhd> (level, table_base p) s
                      \<longrightarrow> valid_pte level pte s
                         \<and> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some empty_pt
                                                   \<and> the (pte_ref pte) \<noteq> table_base p)) \<rbrace>
   store_pte p pte
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
     and pspace_aligned and valid_vspace_objs and valid_asid_table and unique_table_refs
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and (\<lambda>s. pte \<noteq> InvalidPTE
              \<longrightarrow> (\<forall>level asid vref.
                     vs_lookup_table level asid vref s = Some (level, table_base p)
                     \<longrightarrow> vref \<in> user_region
                     \<longrightarrow> pt_slot_offset level (table_base p) vref = p
                     \<longrightarrow> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some empty_pt)
                         \<and> the (pte_ref pte) \<noteq> table_base p
                         \<and> (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                     obj_refs cap = {the (pte_ref pte)} \<and>
                                     vs_cap_ref cap = Some (asid, vref_for_level vref level)))) \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_vs_lookup \<rbrace>"
  apply (case_tac pte; clarsimp)
    apply (wpsimp wp: store_pte_InvalidPTE_valid_vs_lookup)
   apply (wpsimp wp: store_pte_non_InvalidPTE_valid_vs_lookup)+
  done

lemma store_pte_valid_arch_caps:
  "\<lbrace> valid_arch_caps
     and pspace_aligned and valid_vspace_objs and valid_asid_table
     and (\<lambda>s. valid_caps (caps_of_state s) s)
     and (\<lambda>s. (\<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) asidopt))
                              \<longrightarrow> asidopt = None \<longrightarrow> pte = InvalidPTE))
     and (\<lambda>s. pte \<noteq> InvalidPTE
              \<longrightarrow> (\<forall>level asid vref.
                     vs_lookup_table level asid vref s = Some (level, table_base p)
                     \<longrightarrow> vref \<in> user_region
                     \<longrightarrow> pt_slot_offset level (table_base p) vref = p
                     \<longrightarrow> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some empty_pt)
                         \<and> the (pte_ref pte) \<noteq> table_base p
                         \<and> (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                     obj_refs cap = {the (pte_ref pte)} \<and>
                                     vs_cap_ref cap = Some (asid, vref_for_level vref level)))) \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_arch_caps \<rbrace>"
  unfolding valid_arch_caps_def
  by (wpsimp wp: store_pte_valid_vs_lookup store_pte_valid_table_caps)

lemma set_pt_sc_at_pred_n[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. Q (sc_at_pred_n N proj P p' s)\<rbrace>"
  including unfold_objects
  by (wpsimp simp: set_pt_def sc_at_pred_n_def wp: set_object_wp)

lemma set_pt_replies_with_sc[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (replies_with_sc s)\<rbrace>"
  by (wp replies_with_sc_lift)

lemma set_pt_replies_blocked[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (replies_blocked s)\<rbrace>"
  by (wp replies_blocked_lift)

lemma set_pt_valid_replies[wp]:
  "set_pt p pt \<lbrace>valid_replies\<rbrace>"
  by (wp|wps)+

lemma set_pt_sch_act[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace>"
  including unfold_objects by (wpsimp simp: set_pt_def wp: set_object_wp)

lemma set_pt_fault_tcbs_valid_states_except_set[wp]:
  "set_pt p pt \<lbrace>fault_tcbs_valid_states_except_set T\<rbrace>"
  by (wp fault_tcbs_valid_states_lift)

lemma set_pt_cur_sc_tcb[wp]:
  "set_pt p pt \<lbrace>cur_sc_tcb\<rbrace>"
  unfolding cur_sc_tcb_def by wp_pre (wpsimp|wps)+

crunch store_pte
  for cur_sc_tcb[wp]: "cur_sc_tcb"
  and fault_tcbs_valid_states_except_set[wp]: "fault_tcbs_valid_states_except_set T"
  and sch_act[wp]: "\<lambda>s. P (scheduler_action s)"
  and sc_at_pred_n[wp]: "\<lambda>s. Q (sc_at_pred_n N proj P p' s)"
  and replies_with_sc[wp]: "\<lambda>s. P (replies_with_sc s)"
  and replies_blocked[wp]: "\<lambda>s. P (replies_blocked s)"
  and valid_replies[wp]: valid_replies

lemma store_pte_invs:
  "\<lbrace> invs
     and (\<lambda>s. table_base p \<notin> global_refs s)
     and K (wellformed_pte pte)
     and (\<lambda>s. \<forall>level. \<exists>\<rhd> (level, table_base p) s
                      \<longrightarrow> valid_pte level pte s
                         \<and> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some empty_pt
                                                   \<and> the (pte_ref pte) \<noteq> table_base p))
     and (\<lambda>s. (\<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) asidopt))
                              \<longrightarrow> asidopt = None \<longrightarrow> pte = InvalidPTE))
     and (\<lambda>s. ((\<exists>asid. vspace_for_asid asid s = Some (table_base p))
                       \<longrightarrow> table_index p \<notin> kernel_mapping_slots))
     and (\<lambda>s. pte \<noteq> InvalidPTE
              \<longrightarrow> (\<forall>level asid vref.
                     vs_lookup_table level asid vref s = Some (level, table_base p)
                     \<longrightarrow> vref \<in> user_region
                     \<longrightarrow> pt_slot_offset level (table_base p) vref = p
                     \<longrightarrow> (is_PageTablePTE pte \<longrightarrow> pts_of s (the (pte_ref pte)) = Some empty_pt)
                         \<and> the (pte_ref pte) \<noteq> table_base p
                         \<and> (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                     obj_refs cap = {the (pte_ref pte)} \<and>
                                     vs_cap_ref cap = Some (asid, vref_for_level vref level)))) \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. invs \<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_state_def)
  apply (wpsimp wp: store_pte_valid_global_vspace_mappings store_pte_valid_global_tables
                    store_pte_valid_vspace_objs store_pte_valid_arch_caps
                    store_pte_equal_kernel_mappings_no_kernel_slots)
  apply (clarsimp simp: valid_objs_caps valid_arch_caps_def)
  done

lemma store_pte_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) ref))) and
    (\<lambda>s. (\<exists>asid. vspace_for_asid asid s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots) and
    (\<lambda>s. table_base p \<notin> global_refs s) and K (pte = InvalidPTE)\<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. invs\<rbrace>"
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
  apply (fastforce intro: valid_objs_caps)
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

lemma machine_op_lift_device_state[wp]:
  "machine_op_lift f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  by (clarsimp simp: machine_op_lift_def Nondet_VCG.valid_def bind_def
                     machine_rest_lift_def gets_def simpler_modify_def get_def return_def
                     select_def ignore_failure_def select_f_def
              split: if_splits)

crunch sfence
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
crunch hwASIDFlush
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
crunch setVSpaceRoot
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"

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

crunch getRegister
  for inv[wp]: P
  (simp: getRegister_def)

lemmas user_getreg_inv[wp] = as_user_inv[OF getRegister_inv]

lemma dmo_read_stval_inv[wp]:
  "do_machine_op read_stval \<lbrace>P\<rbrace>"
  by (rule dmo_inv) (simp add: read_stval_def)

lemma cur_tcb_more_update[iff]:
  "cur_tcb (trans_state f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

end

end
