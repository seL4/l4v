(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchDetype_AI
imports "../Detype_AI"
begin

context Arch begin global_naming ARM

named_theorems Detype_AI_asms

lemma valid_globals_irq_node[Detype_AI_asms]:
    "\<lbrakk> valid_global_refs s; cte_wp_at (op = cap) ptr s \<rbrakk>
          \<Longrightarrow> interrupt_irq_node s irq \<notin> cap_range cap"
    apply (erule(1) valid_global_refsD)
    apply (simp add: global_refs_def)
    done

lemma caps_of_state_ko[Detype_AI_asms]:
  "valid_cap cap s
   \<Longrightarrow> is_untyped_cap cap \<or>
       cap_range cap = {} \<or>
       (\<forall>ptr \<in> cap_range cap. \<exists>ko. kheap s ptr = Some ko)"
  apply (case_tac cap)
    apply (clarsimp split : option.splits
                    simp  : cap_range_def
                            valid_cap_def
                            obj_at_def
                            is_cap_simps)+
  apply (rename_tac arch_cap ptr)
  apply (case_tac arch_cap)
    apply (fastforce split : option.splits
                     simp  : cap_range_def
                             obj_at_def
                             is_cap_simps )+
  done

lemma mapM_x_storeWord[Detype_AI_asms]:
(* FIXME: taken from Retype_C.thy and adapted wrt. the missing intvl syntax. *)
  assumes al: "is_aligned ptr 2"
  shows "mapM_x (\<lambda>x. storeWord (ptr + of_nat x * 4) 0) [0..<n]
  = modify (underlying_memory_update
             (\<lambda>m x. if \<exists>k. x = ptr + of_nat k \<and> k < n * 4 then 0 else m x))"
proof (induct n)
  case 0
  thus ?case
    apply (rule ext)
    apply (simp add: mapM_x_mapM mapM_def sequence_def
      modify_def get_def put_def bind_def return_def)
    done
next
  case (Suc n')

  have funs_eq:
    "\<And>m x. (if \<exists>k. x = ptr + of_nat k \<and> k < 4 + n' * 4 then 0
             else (m x :: word8)) =
           ((\<lambda>xa. if \<exists>k. xa = ptr + of_nat k \<and> k < n' * 4 then 0 else m xa)
           (ptr + of_nat n' * 4 := word_rsplit (0 :: word32) ! 3,
            ptr + of_nat n' * 4 + 1 := word_rsplit (0 :: word32) ! 2,
            ptr + of_nat n' * 4 + 2 := word_rsplit (0 :: word32) ! Suc 0,
            ptr + of_nat n' * 4 + 3 := word_rsplit (0 :: word32) ! 0)) x"
  proof -
    fix m x

    have xin': "\<And>x. (x < 4 + n' * 4) = (x < n' * 4 \<or> x = n' * 4
                     \<or> x = (n' * 4) + 1 \<or> x = (n' * 4) + 2 \<or> x = (n' * 4) + 3)"
      by (safe, simp_all)

    have xin: "(EX k. x = ptr + of_nat k \<and> k < 4 + n' * 4) =
               ((\<exists>k. x = ptr + of_nat k \<and> k < n' * 4) \<or>
                x = ptr + of_nat n' * 4 \<or> x = ptr + of_nat n' * 4 + 1 \<or>
                x = ptr + of_nat n' * 4 + 2 \<or> x = ptr + of_nat n' * 4 + 3)"
      by (simp add: xin' conj_disj_distribL ex_disj_distrib field_simps)

    show "?thesis m x" by (simp add: xin word_rsplit_0 cong: if_cong)
  qed

  from al have "is_aligned (ptr + of_nat n' * 4) 2"
    apply (rule aligned_add_aligned)
    apply (rule is_aligned_mult_triv2 [where n = 2, simplified])
    apply (simp add: word_bits_conv)+
    done

  thus ?case
    apply (simp add: mapM_x_append bind_assoc Suc.hyps mapM_x_singleton)
    apply (simp add: storeWord_def assert_def is_aligned_mask modify_modify
                     comp_def)
    apply (simp only: funs_eq)
    done
qed

lemma empty_fail_freeMemory [Detype_AI_asms]: "empty_fail (freeMemory ptr bits)"
  by (simp add: freeMemory_def mapM_x_mapM ef_storeWord)


lemma region_in_kernel_window_detype[simp]:
  "region_in_kernel_window S (detype S' s)
      = region_in_kernel_window S s"
  by (simp add: region_in_kernel_window_def detype_def)


lemma region_in_kernel_window_machine_state_update[simp]:
  "region_in_kernel_window S (machine_state_update f s) =
   region_in_kernel_window S s"
  by (simp add: region_in_kernel_window_def)


lemma region_in_kernel_window_delete_objects[wp]:
  "\<lbrace>region_in_kernel_window S\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_. region_in_kernel_window S\<rbrace>"
  by (wp | simp add: delete_objects_def do_machine_op_def split_def)+

end

interpretation Detype_AI?: Detype_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact Detype_AI_asms)?)
  qed

context detype_locale_arch begin

named_theorems detype_invs_proofs

lemma valid_cap[detype_invs_proofs]:
    "\<And>cap'. \<lbrakk> s \<turnstile> cap'; obj_reply_refs cap' \<subseteq> (UNIV - untyped_range cap) \<rbrakk>
      \<Longrightarrow> detype (untyped_range cap) s \<turnstile> cap'"
by (clarsimp simp: valid_cap_def valid_untyped_def obj_reply_refs_def
              split: cap.split_asm option.splits arch_cap.split_asm bool.split_asm)

lemma glob_det[detype_invs_proofs]: "\<And>r. global_refs (detype r s) = global_refs s"
    by (simp add: global_refs_def detype_def)

lemma valid_idle_detype[detype_invs_proofs]: "valid_idle (detype (untyped_range cap) s)"
    proof -
    have "valid_idle s" using invs by (simp add: invs_def valid_state_def)
    thus ?thesis using valid_global_refsD [OF globals cap]
    by (fastforce simp add: valid_idle_def state_refs idle cap_range_def
                            global_refs_def)
    qed

lemma valid_vs_lookup: "valid_vs_lookup s"
    using valid_arch_caps by (simp add: valid_arch_caps_def)

lemma valid_arch_state_detype[detype_invs_proofs]:
  "valid_arch_state (detype (untyped_range cap) s)"
  using valid_vs_lookup valid_arch_state ut_mdb valid_global_refsD [OF globals cap] cap
  apply (simp add: valid_arch_state_def valid_asid_table_def
                valid_global_pts_def global_refs_def
                cap_range_def)
  apply (clarsimp simp: ran_def arch_state_det)
  apply (drule vs_lookup_atI)
  apply (drule (1) valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule untyped_mdbD, rule untyped, assumption)
    apply blast
   apply assumption
  apply (drule descendants_range_inD[OF drange])
    apply (simp add:cte_wp_at_caps_of_state)
  apply (simp add:cap_range_def)
  apply blast
  done

lemma global_pts: (* ARCH SPECIFIC STATEMENT*)
  "\<And>p. \<lbrakk> p \<in> set (arm_global_pts (arch_state s)); p \<in> untyped_range cap \<rbrakk>  \<Longrightarrow> False"
  using valid_global_refsD [OF globals cap] by (simp add: cap_range_def global_refs_def)

lemma vs_lookup: (* SIMP *)
  "vs_lookup (detype (untyped_range cap) s) = vs_lookup s"
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (erule vs_lookup_induct)
    apply (simp add: arch_state_det)
    apply (erule vs_lookup_atI)
   apply (erule vs_lookup_step)
   apply (clarsimp simp: vs_lookup1_def)
  apply (erule vs_lookup_induct)
   apply (rule vs_lookup_atI)
   apply (simp add: arch_state_det)
  apply (erule vs_lookup_step)
  apply (clarsimp simp: vs_lookup1_def)
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], rule valid_vs_lookup)
  apply (elim conjE exE)
  apply (insert cap)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule untyped_mdbD, rule untyped, assumption)
    apply blast
   apply (rule ut_mdb)
  apply (drule descendants_range_inD[OF drange])
    apply (simp add:cte_wp_at_caps_of_state)
  apply (simp add:cap_range_def)
  apply blast
  done


lemma vs_lookup_pages: (* SIMP *)
  "vs_lookup_pages (detype (untyped_range cap) s) = vs_lookup_pages s"
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (erule vs_lookup_pages_induct)
    apply (simp add: arch_state_det)
    apply (erule vs_lookup_pages_atI)
   apply (erule vs_lookup_pages_step)
   apply (clarsimp simp: vs_lookup_pages1_def)
  apply (erule vs_lookup_pages_induct)
   apply (rule vs_lookup_pages_atI)
   apply (simp add: arch_state_det)
  apply (erule vs_lookup_pages_step)
  apply (clarsimp simp: vs_lookup_pages1_def)
  apply (drule valid_vs_lookupD, rule valid_vs_lookup)
  apply (elim conjE exE)
  apply (insert cap)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule untyped_mdbD, rule untyped, assumption)
    apply blast
   apply (rule ut_mdb)
  apply (drule descendants_range_inD[OF drange])
    apply (simp add:cte_wp_at_caps_of_state)
  apply (simp add:cap_range_def)
  apply blast
  done

lemma vs_lookup_preserved:
  "\<And>x rf. \<lbrakk> x \<in> untyped_range cap; (rf \<rhd> x) s \<rbrakk> \<Longrightarrow> False"
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI valid_vs_lookup])
  apply (fastforce intro: global_pts no_obj_refs)
  done

lemma vs_lookup_pages_preserved:
  "\<And>x rf. \<lbrakk> x \<in> untyped_range cap; (rf \<unrhd> x) s \<rbrakk> \<Longrightarrow> False"
  apply (drule valid_vs_lookupD[OF _ valid_vs_lookup])
  apply (fastforce intro: global_pts no_obj_refs)
  done

(* FIXME: This is really horrible but I can't get the automated methods
          to "get it". *)
lemma valid_arch_obj:
  "\<And>ao p. \<lbrakk> valid_arch_obj ao s; ko_at (ArchObj ao) p s; (\<exists>\<rhd>p) s \<rbrakk> \<Longrightarrow>
       valid_arch_obj ao (detype (untyped_range cap) s)"
  apply (case_tac ao)
     apply (clarsimp simp: ran_def)
     apply (erule vs_lookup_preserved)
     apply (erule vs_lookup_step)
     apply (erule vs_lookup1I[OF _ _ refl])
     apply (simp add: vs_refs_def)
     apply (rule image_eqI[rotated])
      apply (erule graph_ofI)
     apply fastforce
    apply (rename_tac "fun")
    apply clarsimp
    apply (erule_tac x=x in allE)
    apply (case_tac "fun x", simp_all)[1]
     apply (rename_tac word attr rights)
     apply (drule_tac p'="(ptrFromPAddr word)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
      apply (clarsimp simp: vs_lookup_pages1_def)
      apply (rule exI, erule conjI)
      apply (rule_tac x="VSRef (ucast x) (Some APageTable)" in exI)
      apply (rule conjI[OF refl])
      apply (clarsimp simp: vs_refs_pages_def graph_of_def pte_ref_pages_def)
      apply (rule_tac x="(x, (ptrFromPAddr word))" in image_eqI)
       apply (simp add: split_def)
      apply simp
     apply (force dest!: vs_lookup_pages_preserved)
    apply (rename_tac word attr rights)
    apply (drule_tac p'="(ptrFromPAddr word)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
     apply (clarsimp simp: vs_lookup_pages1_def)
     apply (rule exI, erule conjI)
     apply (rule_tac x="VSRef (ucast x) (Some APageTable)" in exI)
     apply (rule conjI[OF refl])
     apply (clarsimp simp: vs_refs_pages_def graph_of_def pte_ref_pages_def)
     apply (rule_tac x="(x, (ptrFromPAddr word))" in image_eqI)
      apply (simp add: split_def)
     apply simp
    apply (force dest!: vs_lookup_pages_preserved)
   apply (rename_tac "fun")
   apply clarsimp
   apply (case_tac "fun x", simp_all)[1]
     apply (rename_tac word1 attr word2)
     apply (drule bspec, simp)
     apply (clarsimp simp: valid_pde_def)
     apply (drule_tac p'="(ptrFromPAddr word1)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
     apply (clarsimp simp: vs_lookup_pages1_def)
      apply (rule exI, erule conjI)
      apply (rule_tac x="VSRef (ucast x) (Some APageDirectory)" in exI)
      apply (rule conjI[OF refl])
      apply (clarsimp simp: vs_refs_pages_def graph_of_def pde_ref_pages_def)
      apply (rule_tac x="(x, (ptrFromPAddr word1))" in image_eqI)
       apply (simp add: split_def)
      apply (simp add: pde_ref_pages_def)
     apply (force dest!: vs_lookup_pages_preserved)
    apply (rename_tac word1 attr word2 rights)
    apply (drule_tac p'="(ptrFromPAddr word1)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
     apply (clarsimp simp: vs_lookup_pages1_def)
     apply (rule exI, erule conjI)
     apply (rule_tac x="VSRef (ucast x) (Some APageDirectory)" in exI)
     apply (rule conjI[OF refl])
     apply (clarsimp simp: vs_refs_pages_def graph_of_def pde_ref_pages_def)
     apply (rule_tac x="(x, (ptrFromPAddr word1))" in image_eqI)
      apply (simp add: split_def)
     apply (simp add: pde_ref_pages_def)
    apply (force dest!: vs_lookup_pages_preserved)
   apply (rename_tac word attr rights)
   apply (drule_tac p'="(ptrFromPAddr word)" in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI])
    apply (clarsimp simp: vs_lookup_pages1_def)
    apply (rule exI, erule conjI)
    apply (rule_tac x="VSRef (ucast x) (Some APageDirectory)" in exI)
    apply (rule conjI[OF refl])
    apply (clarsimp simp: vs_refs_pages_def graph_of_def pde_ref_pages_def)
    apply (rule_tac x="(x, (ptrFromPAddr word))" in image_eqI)
     apply (simp add: split_def)
    apply (simp add: pde_ref_pages_def)
   apply (force dest!: vs_lookup_pages_preserved)
  apply clarsimp
  done

lemma valid_arch_obj_detype[detype_invs_proofs]: "valid_arch_objs (detype (untyped_range cap) s)"
  proof -
    have "valid_arch_objs s"
    using invs by fastforce
    thus ?thesis
    unfolding valid_arch_objs_def
    apply (simp add: vs_lookup)
    apply (auto intro: valid_arch_obj)
    done
  qed

lemma unique_table_caps:
    "\<And>cps P. unique_table_caps cps
             \<Longrightarrow> unique_table_caps (\<lambda>x. if P x then None else cps x)"
    by (simp add: unique_table_caps_def)

end


sublocale detype_locale < detype_locale_gen_1
 proof goal_cases
  interpret detype_locale_arch ..
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact detype_invs_proofs)?)
  qed


context detype_locale_arch begin

lemma valid_vs_lookup':  (* LOCAL DUP NAME *)
  "valid_vs_lookup s \<Longrightarrow> valid_vs_lookup (detype (untyped_range cap) s)"
  apply (simp add: valid_vs_lookup_def vs_lookup_pages del: split_paired_Ex)
  apply (elim allEI)
  apply (intro disjCI2 impI)
  apply (drule(1) mp)+
  apply (elim conjE)
  apply (erule exEI)
  apply clarsimp
  apply (drule non_null_caps)
   apply clarsimp+
  done

lemma valid_table_caps:
  "valid_table_caps s \<Longrightarrow> valid_table_caps (detype (untyped_range cap) s)"
  apply (simp add: valid_table_caps_def del: imp_disjL)
  apply (elim allEI | rule impI)+
  apply clarsimp
  apply (metis detype_arch_state no_obj_refs) (* METIS USED *)
  done


lemma valid_arch_caps_detype[detype_invs_proofs]: "valid_arch_caps (detype (untyped_range cap) s)"
  using valid_arch_caps  by (simp add: valid_arch_caps_def
                                       unique_table_caps
                                       valid_vs_lookup'
                                       unique_table_refs
                                       valid_table_caps)



lemma pd_at_global_pd: "page_directory_at (arm_global_pd (arch_state s)) s"
  using valid_arch_state by (simp add: valid_arch_state_def)


lemma valid_global_objs_detype[detype_invs_proofs]: "valid_global_objs (detype (untyped_range cap) s)"
  using valid_global_objs valid_global_refsD [OF globals cap]
  apply (simp add: valid_global_objs_def valid_ao_at_def arch_state_det)
  apply (elim conjE, intro conjI)
     apply (simp add: global_refs_def cap_range_def arch_state_det)
    apply (erule exEI)
    apply (insert pd_at_global_pd)[1]
    subgoal by (clarsimp simp: obj_at_def a_type_simps empty_table_def arch_state_det)
   apply (simp add: global_refs_def cap_range_def)
  apply (clarsimp elim!: global_pts)
  done

lemma valid_kernel_mappings_detype[detype_invs_proofs]: "valid_kernel_mappings (detype (untyped_range cap) s)"
  proof -
    have "valid_kernel_mappings s"
      using invs by (simp add: invs_def valid_state_def)
    thus ?thesis by (simp add: valid_kernel_mappings_def detype_def
                  ball_ran_eq)
  qed

lemma valid_asid_map_detype[detype_invs_proofs]: "valid_asid_map (detype (untyped_range cap) s)"
proof -
  have "valid_asid_map s"
  using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
  apply (clarsimp simp: valid_asid_map_def arch_state_det)
  apply (drule bspec)
  apply (blast)
  apply (clarsimp simp: vspace_at_asid_def vs_lookup)
  done
  qed

lemma equal_kernel_mappings_detype[detype_invs_proofs]:
  "equal_kernel_mappings (detype (untyped_range cap) s)"
  proof -
    have "equal_kernel_mappings s"
      using invs by (simp add: invs_def valid_state_def)
    thus ?thesis
      apply (simp add: equal_kernel_mappings_def)
      apply blast
      done
  qed

lemma valid_global_mappings_detype[detype_invs_proofs]:
  "valid_global_vspace_mappings (detype (untyped_range cap) s)"
proof -
  have "valid_global_vspace_mappings s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
  using valid_global_refsD [OF globals cap] valid_global_objs
  apply -
  apply (erule valid_global_vspace_mappings_pres, simp_all)
   apply (simp add: cap_range_def global_refs_def arch_state_det)+
  done
qed

lemma pspace_in_kernel_window_detype[detype_invs_proofs]:
  "pspace_in_kernel_window (detype (untyped_range cap) s)"
proof -
  have "pspace_in_kernel_window s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
    apply (simp add: pspace_in_kernel_window_def arch_state_det)
    apply fastforce
    done
qed

lemma valid_machine_state_detype[detype_invs_proofs]:
    "valid_machine_state (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
  proof -
    have "valid_machine_state s" using invs by (simp add: invs_def valid_state_def)
    thus ?thesis
      apply (clarsimp simp: valid_machine_state_def clear_um_def detype_def)
      apply (drule_tac x=p in spec)
      apply (simp add: in_user_frame_def obj_at_def)
      apply (elim exEI exE conjE, simp)
      apply (frule valid_pspace_aligned[OF valid_pspace])
      apply (drule_tac ptr'=p in mask_in_range)
      apply (case_tac ko, simp_all add: a_type_simps split: split_if_asm)
      apply (rename_tac arch_kernel_obj)
      apply (case_tac arch_kernel_obj, simp_all add: a_type_simps)
      apply clarsimp using untyped cap_is_valid
      apply (case_tac cap, simp_all)
      apply (clarsimp simp add: valid_cap_def cap_aligned_def valid_untyped_def)
      apply (drule_tac x="p && ~~ mask (pageBitsForSize x)" in spec)
      apply (auto simp add: obj_range_def)
    done
  qed
end

sublocale detype_locale < detype_locale_gen_2
 proof goal_cases
  interpret detype_locale_arch ..
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact detype_invs_proofs)?)
  qed

context detype_locale begin
  lemmas invariants = invariants
  lemmas non_filter_detype = non_filter_detype
  lemmas valid_cap = valid_cap
  lemmas non_null_present = non_null_present
end

interpretation Detype_AI_2
  using detype_locale.invariants[simplified detype_locale_def]
        Detype_AI_2.intro
        by blast

context begin interpretation Arch .
lemma delete_objects_invs[wp]:
  "\<lbrace>(\<lambda>s. \<exists>slot. cte_wp_at (op = (cap.UntypedCap ptr bits f)) slot s
    \<and> descendants_range (cap.UntypedCap ptr bits f) slot s) and
    invs and ct_active\<rbrace>
    delete_objects ptr bits \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (simp add: freeMemory_def word_size_def bind_assoc
                   empty_fail_mapM_x ef_storeWord)
   apply (rule hoare_pre)
   apply (rule_tac G="is_aligned ptr bits \<and> 2 \<le> bits \<and> bits \<le> word_bits"
                in hoare_grab_asm)
   apply (simp add:mapM_storeWord_clear_um intvl_range_conv[where 'a=32, folded word_bits_def])
   apply wp
  apply clarsimp
  apply (frule invs_untyped_children)
  apply (frule detype_invariants, clarsimp+)
  apply (drule invs_valid_objs)
  apply (drule (1) cte_wp_valid_cap)
  apply (simp add: valid_cap_def cap_aligned_def)
  done
end

end
