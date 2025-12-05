(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchDetype_AI
imports Detype_AI
begin

context Arch begin arch_global_naming

named_theorems Detype_AI_assms

lemma valid_globals_irq_node[Detype_AI_assms]:
    "\<lbrakk> valid_global_refs s; cte_wp_at ((=) cap) ptr s \<rbrakk>
          \<Longrightarrow> interrupt_irq_node s irq \<notin> cap_range cap"
    apply (erule(1) valid_global_refsD)
    apply (simp add: global_refs_def)
    done

lemma caps_of_state_ko[Detype_AI_assms]:
  "valid_cap cap s
   \<Longrightarrow> is_untyped_cap cap \<or>
       cap_range cap = {} \<or>
       (\<forall>ptr \<in> cap_range cap. \<exists>ko. kheap s ptr = Some ko)"
  apply (case_tac cap)
    apply (clarsimp simp: cap_range_def valid_cap_def obj_at_def is_cap_simps
                   split: option.splits)+
  apply (rename_tac arch_cap ptr)
  apply (case_tac arch_cap)
    apply (fastforce simp: cap_range_def obj_at_def is_cap_simps
                    split: option.splits if_splits)+
  done

lemma mapM_x_storeWord[Detype_AI_assms]:
(* FIXME: taken from Retype_C.thy and adapted wrt. the missing intvl syntax. *)
  assumes al: "is_aligned ptr word_size_bits"
  shows "mapM_x (\<lambda>x. storeWord (ptr + of_nat x * word_size) 0) [0..<n]
  = modify (underlying_memory_update
             (\<lambda>m x. if \<exists>k. x = ptr + of_nat k \<and> k < n * word_size then 0 else m x))"
proof (induct n)
  case 0
  thus ?case
    apply (rule ext)
    apply (simp add: mapM_x_mapM mapM_def sequence_def
                     modify_def get_def put_def bind_def return_def)
    done
next
  case (Suc n')

  have b: "\<And>i. word_rsplit (0 :: machine_word) ! (7 - i) = (0 :: 8 word)"
    apply (simp add: word_rsplit_0 word_bits_def)
    apply (case_tac i; simp; rename_tac i)+
    done

  have k: "\<And>k. (k < word_size + n' * word_size)
                  = (k < n' * word_size \<or> k = n' * word_size
                        \<or> (\<exists>i \<in> {1,2,3,4,5,6,7}. k = n' * word_size + i))"
    by (auto simp: word_size_def)

  have x: "\<And>x. (\<exists>k. x = ptr + of_nat k \<and> k < word_size + n' * word_size)
                  = ((\<exists>k. x = ptr + of_nat k \<and> k < n' * word_size)
                       \<or> (\<exists>i \<in> {0,1,2,3,4,5,6,7}. x = ptr + of_nat n' * word_size + i))"
    unfolding k by (simp add: word_size_def conj_disj_distribL ex_disj_distrib field_simps)

  from al have "is_aligned (ptr + of_nat n' * word_size) word_size_bits"
    apply (rule aligned_add_aligned)
    apply (rule is_aligned_mult_triv2 [of _ word_size_bits, simplified word_size_size_bits_word])
    apply (rule order_refl)
    done

  thus ?case
    apply (simp add: mapM_x_append bind_assoc Suc.hyps mapM_x_singleton)
    apply (simp add: storeWord_def b assert_def is_aligned_mask modify_modify
                     comp_def word_size_bits_def)
    apply (rule arg_cong[where f=modify])
    apply (rule arg_cong[where f=underlying_memory_update])
    apply (rule ext, rule ext, rule sym)
    apply (simp add: x upto0_7_def)
    done
qed

lemma empty_fail_freeMemory [Detype_AI_assms]: "empty_fail (freeMemory ptr bits)"
  by (fastforce simp: freeMemory_def mapM_x_mapM)


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

lemma state_hyp_refs_of_detype:
  "state_hyp_refs_of (detype S s) = (\<lambda>x. if x \<in> S then {} else state_hyp_refs_of s x)"
  by (rule ext, simp add: state_hyp_refs_of_def detype_def)

end

interpretation Detype_AI?: Detype_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact Detype_AI_assms)?)
  qed

context detype_locale_arch begin

named_theorems detype_invs_proofs

lemma state_hyp_refs: "state_hyp_refs_of (detype (untyped_range cap) s) = state_hyp_refs_of s"
  apply (rule ext, clarsimp simp add: state_hyp_refs_of_detype)
  apply (rule sym, rule equals0I, drule state_hyp_refs_of_elemD)
  apply (drule live_okE, rule hyp_refs_of_live, clarsimp)
  apply simp
  done

lemma hyp_refsym : "sym_refs (state_hyp_refs_of s)"
  using invs by (simp add: invs_def valid_state_def valid_pspace_def)

lemma hyp_refs_of: "\<And>obj p. \<lbrakk> ko_at obj p s \<rbrakk> \<Longrightarrow> hyp_refs_of obj \<subseteq> (UNIV - untyped_range cap \<times> UNIV)"
  by (fastforce intro: hyp_refs_of_live dest!: hyp_sym_refs_ko_atD[OF _ hyp_refsym] live_okE)

lemma arch_valid_obj[detype_invs_proofs]:
    "\<And>p ao. \<lbrakk>ko_at (ArchObj ao) p s; arch_valid_obj ao s\<rbrakk>
       \<Longrightarrow> arch_valid_obj ao (detype (untyped_range cap) s)"
  apply (frule hyp_refs_of)
  apply (auto simp: arch_valid_obj_def split: arch_kernel_obj.splits option.splits)
  done

lemma sym_hyp_refs_detype[detype_invs_proofs]:
  "sym_refs (state_hyp_refs_of (detype (untyped_range cap) s))"
  using hyp_refsym by (simp add: state_hyp_refs)

lemma valid_cap[detype_invs_proofs]:
    "\<And>cap'. \<lbrakk> s \<turnstile> cap'; obj_reply_refs cap' \<subseteq> (UNIV - untyped_range cap) \<rbrakk>
      \<Longrightarrow> detype (untyped_range cap) s \<turnstile> cap'"
  by (auto simp: valid_cap_def valid_untyped_def obj_reply_refs_def
          split: cap.split_asm option.splits if_splits
                 arch_cap.split_asm bool.split_asm )

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

lemma hyp_live_strg:
  "hyp_live ko \<Longrightarrow> live ko"
  by (cases ko; simp add: live_def hyp_live_def)

lemma obj_at_hyp_live_strg:
  "obj_at hyp_live p s \<Longrightarrow> obj_at live p s"
  by (erule obj_at_weakenE, rule hyp_live_strg)

lemma tcb_arch_detype[detype_invs_proofs]:
  "\<lbrakk>ko_at (TCB t) p s; valid_arch_tcb (tcb_arch t) s\<rbrakk>
      \<Longrightarrow> valid_arch_tcb (tcb_arch t) (detype (untyped_range cap) s)"
  apply (clarsimp simp: valid_arch_tcb_def)
  done

lemma valid_ioports_detype:
  "valid_ioports s \<Longrightarrow> valid_ioports (detype (untyped_range cap) s)"
  apply (clarsimp simp: valid_ioports_def all_ioports_issued_def ioports_no_overlap_def
                        issued_ioports_def)
  apply (clarsimp simp: detype_def cap_ioports_def ran_def)
  by blast

lemma ioport_control_detype:
  "ioport_control_unique_2 caps \<Longrightarrow>
   ioport_control_unique_2 (\<lambda>p. if fst p \<in> S then None else caps p)"
  by (auto simp: ioport_control_unique_2_def)

lemma valid_arch_state_detype[detype_invs_proofs]:
  "valid_arch_state (detype (untyped_range cap) s)"
  using valid_vs_lookup valid_arch_state ut_mdb valid_global_refsD [OF globals cap] cap
  unfolding valid_arch_state_def
  apply (strengthen valid_ioports_detype,
         simp add: valid_arch_state_def valid_asid_table_def
                   valid_global_pdpts_def valid_global_pds_def valid_global_pts_def
                   global_refs_def cap_range_def ioport_control_detype)
  apply (clarsimp simp: ran_def arch_state_det)
  apply (drule vs_lookup_atI)
  apply (drule (1) valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule untyped_mdbD, rule untyped, assumption)
    apply blast
   apply assumption
  apply (drule descendants_range_inD[OF drange])
    apply (simp add: cte_wp_at_caps_of_state)
  apply (simp add: cap_range_def)
  apply blast
  done

lemma valid_cur_fpu[detype_invs_proofs]:
  "valid_cur_fpu (detype (untyped_range cap) s)"
  using valid_cur_fpu
  by (auto simp: valid_cur_fpu_def is_tcb_cur_fpu_def live_def arch_tcb_live_def arch_state_det elim!: live_okE)

lemma global_pdpts:
  "\<And>p. \<lbrakk> p \<in> set (x64_global_pdpts (arch_state s)); p \<in> untyped_range cap \<rbrakk>  \<Longrightarrow> False"
  using valid_global_refsD [OF globals cap] by (simp add: cap_range_def global_refs_def)

lemma global_pds:
  "\<And>p. \<lbrakk> p \<in> set (x64_global_pds (arch_state s)); p \<in> untyped_range cap \<rbrakk>  \<Longrightarrow> False"
  using valid_global_refsD [OF globals cap] by (simp add: cap_range_def global_refs_def)

lemma global_pts:
  "\<And>p. \<lbrakk> p \<in> set (x64_global_pts (arch_state s)); p \<in> untyped_range cap \<rbrakk>  \<Longrightarrow> False"
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

context begin

private method crush for i =
  (simp add: data_at_def obj_at_def;
   elim disjE exE conjE;
   clarsimp;
   erule vs_lookup_pages_preserved;
   erule vs_lookup_pages_step;
   clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def;
   strengthen image_eqI;
   clarsimp simp: graph_of_def pte_ref_pages_def pde_ref_pages_def
                  pdpte_ref_pages_def pml4e_ref_pages_def;
   rule exI;
   strengthen refl;
   simp;
   rule exI[of _ i];
   fastforce)

lemma valid_vspace_obj:
  "\<And>ao p. \<lbrakk> valid_vspace_obj ao s; ko_at (ArchObj ao) p s; (\<exists>\<rhd>p) s \<rbrakk> \<Longrightarrow>
       valid_vspace_obj ao (detype (untyped_range cap) s)"
  apply (case_tac ao; simp; erule allEI ballEI; clarsimp simp: ran_def;
         drule vs_lookup_pages_vs_lookupI)
  subgoal for p t r ref i by (crush i)
  subgoal for p t i ref by (cases "t i"; crush i)
  subgoal for p t i ref by (cases "t i"; crush i)
  subgoal for p t i ref by (cases "t i"; crush i)
  subgoal for p t i ref by (cases "t i"; crush i)
  done

end

lemma valid_vspace_obj_detype[detype_invs_proofs]: "valid_vspace_objs (detype (untyped_range cap) s)"
  proof -
    have "valid_vspace_objs s"
    using invs by fastforce
    thus ?thesis
    unfolding valid_vspace_objs_def
    apply (simp add: vs_lookup)
    apply (auto intro: valid_vspace_obj)
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
    case 1 show ?case by (unfold_locales; fact detype_invs_proofs)
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
  apply (metis detype_arch_state no_obj_refs)
  done

lemma unique_table_refs:
    "\<And>cps P. unique_table_refs cps
             \<Longrightarrow> unique_table_refs (\<lambda>x. if P x then None else cps x)"
    apply (simp only: unique_table_refs_def option.simps
                      simp_thms
               split: if_split)
    apply blast
    done

lemma valid_arch_caps_detype[detype_invs_proofs]: "valid_arch_caps (detype (untyped_range cap) s)"
  using valid_arch_caps  by (simp add: valid_arch_caps_def
                                       unique_table_caps
                                       valid_vs_lookup'
                                       unique_table_refs
                                       valid_table_caps)



lemma pml4_at_global_pml4: "page_map_l4_at (x64_global_pml4 (arch_state s)) s"
  using valid_arch_state by (simp add: valid_arch_state_def)


lemma valid_global_objs_detype[detype_invs_proofs]:
  "valid_global_objs (detype (untyped_range cap) s)"
  using valid_global_objs valid_global_refsD [OF globals cap]
  apply (simp add: valid_global_objs_def valid_vso_at_def arch_state_det)
  apply (intro conjI; elim conjE exEI;
         clarsimp simp: global_refs_def cap_range_def arch_state_det)
  using pml4_at_global_pml4
  by (clarsimp simp: obj_at_def a_type_simps empty_table_def arch_state_det)

lemma valid_kernel_mappings_detype[detype_invs_proofs]:
  "valid_kernel_mappings (detype (untyped_range cap) s)"
  proof -
    have "valid_kernel_mappings s"
      using invs by (simp add: invs_def valid_state_def)
    thus ?thesis by (simp add: valid_kernel_mappings_def detype_def
                  ball_ran_eq)
  qed

lemma valid_asid_map_detype[detype_invs_proofs]: "valid_asid_map (detype (untyped_range cap) s)"
  by (simp add: valid_asid_map_def)

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

lemma in_user_frame_eq:
  notes [simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                     Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
                     order_class.Icc_eq_Icc
    and [simp] = p2pm1_to_mask
  shows "p \<notin> untyped_range cap \<Longrightarrow>
         in_user_frame p (s \<lparr>kheap := \<lambda>x. if x \<in> untyped_range cap then None else kheap s x\<rparr>)
         = in_user_frame p s"
    using cap_is_valid untyped
    apply (cases cap; simp add: in_user_frame_def valid_untyped_def valid_cap_def obj_at_def)
    apply (rule iffI; erule exEI; elim conjE exE; simp)
    subgoal for dev ptr n f sz ko
      apply (elim allE; erule (1) impE)
      apply (drule valid_pspace_aligned[OF valid_pspace])
      apply (clarsimp simp: obj_range_def)
      apply (erule impE)
       apply (erule not_emptyI[rotated])
       apply (rule mask_in_range[THEN iffD1, simplified])
        apply (simp add: is_aligned_neg_mask)
       apply (simp add: mask_lower_twice)
      apply (cut_tac mask_in_range[THEN iffD1, simplified, OF is_aligned_neg_mask[OF le_refl] refl])
      apply fastforce
      done
    done

lemma in_device_frame_eq:
  notes blah[simp del] =  atLeastAtMost_iff
          atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          order_class.Icc_eq_Icc
     and  p2pm1[simp] = p2pm1_to_mask
  shows "p \<notin> untyped_range cap
       \<Longrightarrow> in_device_frame p (s \<lparr>kheap := \<lambda>x. if x \<in> untyped_range cap then None else kheap s x\<rparr>)
         = in_device_frame p s"
    using cap_is_valid untyped
    unfolding in_device_frame_def
    apply (cases cap; simp add: in_device_frame_def valid_untyped_def valid_cap_def obj_at_def)
    apply (rule iffI; erule exEI; elim conjE exE; simp)
    subgoal for dev ptr n f sz ko
      apply (elim allE; erule (1) impE)
      apply (drule valid_pspace_aligned[OF valid_pspace])
      apply (clarsimp simp: obj_range_def)
      apply (erule impE)
       apply (erule not_emptyI[rotated])
       apply (rule mask_in_range[THEN iffD1, simplified])
        apply (simp add: is_aligned_neg_mask)
       apply (simp add: mask_lower_twice)
      apply (cut_tac mask_in_range[THEN iffD1, simplified, OF is_aligned_neg_mask[OF le_refl] refl])
      apply fastforce
      done
    done

lemma pspace_respects_device_region_detype[detype_invs_proofs]:
  "pspace_respects_device_region (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
  proof -
  have "pspace_respects_device_region s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
    apply (intro pspace_respects_device_regionI)
    using pspace_aligned_detype valid_objs_detype invs
    apply (simp_all add: clear_um.pspace detype_def dom_def clear_um_def
                  split: if_split_asm )
       apply (drule pspace_respects_device_regionD[rotated -1],auto)+
    done
  qed

lemma cap_refs_respects_device_region_detype[detype_invs_proofs]:
  "cap_refs_respects_device_region (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
  proof -
  have "cap_refs_respects_device_region s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
    apply (clarsimp simp: clear_um_def cap_refs_respects_device_region_def
                simp del: split_paired_All split_paired_Ex)
    apply (drule_tac x = "(a,b)" in spec)
    apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_respects_device_region_def detype_def)
    done
  qed

lemma valid_machine_state_detype[detype_invs_proofs]:
    "valid_machine_state (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
  proof -
    have "valid_machine_state s" using invs by (simp add: invs_def valid_state_def)
    thus ?thesis
    using untyped cap_is_valid
    by (clarsimp simp: valid_machine_state_def clear_um_def
      detype_def in_user_frame_eq in_device_frame_eq)
  qed

end

sublocale detype_locale < detype_locale_gen_2
 proof goal_cases
  interpret detype_locale_arch ..
  case 1 show ?case
  by (intro_locales; unfold_locales; (fact detype_invs_proofs)?)
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

(* generic consequence of architecture-specific details *)
lemma (in Arch) delete_objects_invs[wp]:
  "\<lbrace>(\<lambda>s. \<exists>slot. cte_wp_at ((=) (cap.UntypedCap dev ptr bits f)) slot s
    \<and> descendants_range (cap.UntypedCap dev ptr bits f) slot s) and
    invs and ct_active\<rbrace>
    delete_objects ptr bits \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (simp add: freeMemory_def word_size_def bind_assoc)
   apply (rule hoare_pre)
   apply (rule_tac P'="is_aligned ptr bits \<and> word_size_bits \<le> bits \<and> bits \<le> word_bits"
                in hoare_grab_asm)
   apply (simp add: mapM_storeWord_clear_um[unfolded word_size_def]
                    intvl_range_conv[where 'a=machine_word_len, folded word_bits_def])
   apply wp
  apply clarsimp
  apply (frule invs_untyped_children)
  apply (frule detype_invariants, clarsimp+)
  apply (drule invs_valid_objs)
  apply (drule (1) cte_wp_valid_cap)
  apply (simp add: valid_cap_def cap_aligned_def word_size_bits_def untyped_min_bits_def)
  done

requalify_facts Arch.delete_objects_invs
lemmas [wp] = delete_objects_invs

end
