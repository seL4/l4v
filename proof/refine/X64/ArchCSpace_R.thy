(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* CSpace refinement - architecture-specific *)

theory ArchCSpace_R
imports CSpace_R
begin

context Arch begin arch_global_naming

named_theorems CSpace_R_assms

lemmas [CSpace_R_assms] =
  arch_deriveCap_corres arch_deriveCap_inv arch_deriveCap_valid

lemma capAligned_master[CSpace_R_assms]:
  "\<lbrakk>capAligned cap; capMasterCap cap = capMasterCap ncap\<rbrakk> \<Longrightarrow> capAligned ncap"
  apply (case_tac cap)
   apply (clarsimp simp: capAligned_def)+
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability)
   apply (clarsimp simp: capAligned_def)+
  done

lemmas updateMDB_typ_ats[wp] = typ_at_lifts[OF updateMDB_typ_at']
lemmas updateCap_typ_ats[wp] = typ_at_lifts[OF updateCap_typ_at']
lemmas cteInsert_typ_ats[wp] = typ_at_lifts[OF cteInsert_typ_at']

lemma maskedAsFull_derived'[CSpace_R_assms]:
  "\<lbrakk>m src = Some (CTE s_cap s_node); is_derived' m ptr b c\<rbrakk>
   \<Longrightarrow> is_derived' (m(src \<mapsto> CTE (maskedAsFull s_cap cap) s_node)) ptr b c"
  apply (subgoal_tac "m(src \<mapsto> CTE (maskedAsFull s_cap cap) s_node)
     = (modify_map m src (cteCap_update (\<lambda>_. maskedAsFull s_cap cap)))")
   apply simp
   apply (clarsimp simp:maskedAsFull_def is_derived'_def)
   apply (intro conjI impI)
    apply (simp add:modify_map_def del:cteCap_update.simps)
   apply (subst same_master_descendants)
       apply simp
      apply (clarsimp simp:isCap_simps capASID_def )+
   apply (clarsimp simp:modify_map_def)
   done

lemma capMaster_capRange[CSpace_R_assms]:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> capRange c = capRange c'"
  by (simp add: capMasterCap_def arch_capMasterCap_def capRange_def
           split: capability.splits arch_capability.splits)

lemma capMaster_untypedRange[CSpace_R_assms]:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> untypedRange c = untypedRange c'"
  by (simp add: capMasterCap_def capRange_def split: capability.splits arch_capability.splits)

lemma capMaster_capClass[CSpace_R_assms]:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> capClass c = capClass c'"
  by (simp add: capMasterCap_def arch_capMasterCap_def
           split: capability.splits arch_capability.splits)

lemma valid_arch_badges_mdbPrev_update[simp, CSpace_R_assms]:
  "valid_arch_badges cap cap' (mdbPrev_update f node) = valid_arch_badges cap cap' node"
  by (simp add: valid_arch_badges_def)

lemma valid_arch_badges_master_eq:
  "capMasterCap src_cap = capMasterCap cap \<Longrightarrow>
   valid_arch_badges src_cap cap' node = valid_arch_badges cap cap' node"
  by (auto simp: valid_arch_badges_def isCap_simps)

lemmas valid_arch_badges_master[CSpace_R_assms] = valid_arch_badges_master_eq[THEN iffD1]

lemma valid_arch_badges_firstBadged[CSpace_R_assms]:
  "\<lbrakk> valid_arch_badges cap cap' node; mdbFirstBadged node = mdbFirstBadged node' \<rbrakk> \<Longrightarrow>
   valid_arch_badges cap cap' node'"
  by (simp add: valid_arch_badges_def)

lemma badge_derived'_capRange[CSpace_R_assms]:
  "badge_derived' cap src_cap \<Longrightarrow> capRange cap = capRange src_cap"
  apply (clarsimp simp: badge_derived'_def)
  apply (case_tac cap; clarsimp simp: gen_isCap_simps capRange_def)
      apply (rename_tac arch_capability)
      apply (case_tac arch_capability; clarsimp simp: isCap_simps capRange_def)
  done

lemma valid_arch_badges_non_arch[CSpace_R_assms]:
  "\<lbrakk> \<not>isArchObjectCap c; \<not>isArchObjectCap c' \<rbrakk> \<Longrightarrow> valid_arch_badges c c' node"
  by (clarsimp simp add: valid_arch_badges_def isCap_simps)

lemma capMasterCap_valid_arch_badges_isCapRevocable[CSpace_R_assms]:
  "capMasterCap src_cap = capMasterCap cap
   \<Longrightarrow> valid_arch_badges src_cap cap
        (MDB word1 src (Arch.isCapRevocable cap src_cap) (Arch.isCapRevocable cap src_cap))"
  by (clarsimp simp add: valid_arch_badges_def)

lemma setCTE_valid_arch[CSpace_R_assms, wp]:
  "setCTE p c \<lbrace>valid_arch_state'\<rbrace>"
  by (wp valid_arch_state_lift' setCTE_typ_at')

lemma setCTE_global_refs[CSpace_R_assms, wp]:
  "setCTE p c \<lbrace>\<lambda>s. P (global_refs' s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def updateObject_cte global_refs'_def)
  apply (wpsimp+; auto)
  done

crunch cteInsert
  for arch[wp]: "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps simp: cte_wp_at_ctes_of)

crunch cteInsert
  for valid_arch_state'[wp]: valid_arch_state'
  (wp: crunch_wps)

declare cteInsert_valid_arch_state'[CSpace_R_assms]

lemmas cap_ioports'_simps[simp] = cap_ioports'_def[split_simps capability.split arch_capability.split]

definition
  "safe_ioport_insert' newcap oldcap \<equiv> \<lambda>s.  (cap_ioports' newcap = {} \<or>
      (\<forall>cap''\<in>ran (cteCaps_of s).
          cap_ioports' newcap = cap_ioports' cap'' \<or> cap_ioports' newcap \<inter> cap_ioports' cap'' = {})) \<and>
     cap_ioports' newcap - cap_ioports' oldcap \<subseteq> issued_ioports' (ksArchState s)"

lemma not_ioport_cap_cap_ioports'[simp]:
  "\<not>isArchIOPortCap cap \<Longrightarrow> cap_ioports' cap = {}"
  by (clarsimp simp: isCap_simps cap_ioports'_def split: capability.splits arch_capability.splits)

lemma not_ioport_cap_safe_ioport_insert'[simp]:
  "\<not>isArchIOPortCap cap \<Longrightarrow> safe_ioport_insert' cap cap' s"
  by (clarsimp simp: safe_ioport_insert'_def isCap_simps)

end (* Arch *)

context Arch_mdb_move begin

lemma parent_preserved:
  "isMDBParentOf cte' (CTE cap' src_node) =
   isMDBParentOf cte' (CTE src_cap src_node)"
  using parency unfolding weak_derived'_def
  apply (cases cte')
  apply (simp add: isMDBParentOf_CTE sameRegionAs_def2 del: isArchFrameCap_capMasterCap)
  done

lemma children_preserved:
  "isMDBParentOf (CTE cap' src_node) cte' =
   isMDBParentOf (CTE src_cap src_node) cte'"
  using parency unfolding weak_derived'_def
  apply (cases cte')
  apply (simp add: isMDBParentOf_CTE sameRegionAs_def2)
  done

end (* Arch_mdb_move *)

locale Arch_mdb_insert = mdb_insert + Arch
begin

lemma derived_region1[simp]:
  "badge_derived' c' src_cap \<Longrightarrow> sameRegionAs c' cap = sameRegionAs src_cap cap"
  by (clarsimp simp add: badge_derived'_def sameRegionAs_def2)

lemma derived_region2[simp]:
  "badge_derived' c' src_cap \<Longrightarrow> sameRegionAs cap c' = sameRegionAs cap src_cap"
  by (clarsimp simp add: badge_derived'_def sameRegionAs_def2)

lemma derived_mdb_chunked_arch_assms[simp]:
  "badge_derived' c' src_cap \<Longrightarrow> mdb_chunked_arch_assms c' = mdb_chunked_arch_assms src_cap"
  by (clarsimp simp: badge_derived'_def mdb_chunked_arch_assms_def)

lemma chunked_n:
  assumes b: "badge_derived' c' src_cap"
  shows "mdb_chunked n"
  using chunked_m src b
  apply (clarsimp simp: mdb_chunked_def)
  apply (drule n_cap)+
  apply clarsimp
  apply (simp split: if_split_asm)
    apply clarsimp
    apply (erule_tac x=src in allE)
    apply (erule_tac x=p' in allE)
    apply simp
    apply (case_tac "src=p'")
     apply (clarsimp simp: n_trancl_eq)
     apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
     apply (drule (1) trancl_rtrancl_trancl)
     apply simp
    apply (clarsimp simp: n_trancl_eq)
    apply (rule conjI)
     apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq)
     apply (erule_tac x=p'' in allE)
     apply clarsimp
     apply (drule_tac p=p'' in m_cap)
     apply (clarsimp split: if_split_asm)
    apply clarsimp
    apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
    apply (rule conjI)
     apply clarsimp
     apply (erule_tac x=src in allE)
     apply simp
    apply clarsimp
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (drule_tac p=p'' in m_cap)
    apply (clarsimp split: if_split_asm)
   apply (clarsimp simp: n_trancl_eq)
   apply (case_tac "p=src")
    apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
    apply (drule (1) trancl_rtrancl_trancl)
    apply simp
   apply simp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=src in allE)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (drule_tac p=p'' in m_cap)
    apply clarsimp
   apply clarsimp
   apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap)
   apply clarsimp
  apply (clarsimp simp: n_trancl_eq)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (simp add: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (erule sameRegionAsE; simp add: sameRegionAs_def3 isCap_simps)[1]
        apply force
      apply (clarsimp simp: isCap_simps)
     apply (clarsimp simp: isCap_simps)
    apply fastforce
   apply clarsimp
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap)
   apply clarsimp
  apply clarsimp
  apply (simp add: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (erule_tac x=p in allE, simp, erule(1) sameRegionAs_trans)
   apply fastforce
  apply clarsimp
  apply (erule_tac x=p'' in allE)
  apply clarsimp
  apply (drule_tac p=p'' in m_cap)
  apply clarsimp
  done

end (* Arch_mdb_insert *)

context Arch_mdb_insert_sib begin

lemma untyped_inc_n:
  assumes c': "capAligned c'"
  shows "untyped_inc' n"
  using untyped_inc not_untyped[OF c']
  apply (clarsimp simp add: untyped_inc'_def descendants split del: if_split)
  apply (drule n_cap)+
  apply (clarsimp split: if_split_asm)
   apply (simp add: descendants_of'_def untyped_c')
  apply (case_tac "p = dest")
   apply (clarsimp simp: untyped_c')
  apply simp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply simp
  done

end (* Arch_mdb_insert_sib *)

context Arch begin arch_global_naming

(* since these are not used after this theory, drop the Arch assumption directly
   instead of requalifying to improve processing time (unfold_locales for Arch is slow) *)
lemmas [CSpace_R_assms] =
  Arch_mdb_insert.chunked_n[simplified Arch_mdb_insert_def]
  Arch_mdb_insert_sib.untyped_inc_n[simplified Arch_mdb_insert_sib_def]
  Arch_mdb_move.parent_preserved[simplified Arch_mdb_move_def]
  Arch_mdb_move.children_preserved[simplified Arch_mdb_move_def]

crunch cteInsert
  for pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps)

lemmas [CSpace_R_assms] = cteInsert_pspace_in_kernel_mappings'

end

interpretation CSpace_R?: CSpace_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact CSpace_R_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems CSpace_R_2_assms

lemma deriveCap_derived:
  "\<lbrace>\<lambda>s. c'\<noteq> capability.NullCap \<longrightarrow> cte_wp_at' (\<lambda>cte. badge_derived' c' (cteCap cte)
                           \<and> capASID c' = capASID (cteCap cte)
                           \<and> cap_asid_base' c' = cap_asid_base' (cteCap cte)
                           \<and> cap_vptr' c' = cap_vptr' (cteCap cte)) slot s
       \<and> valid_objs' s\<rbrace>
  deriveCap slot c'
  \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow>
          cte_wp_at' (is_derived' (ctes_of s) slot rv \<circ> cteCap) slot s\<rbrace>, -"
  unfolding global.deriveCap_def badge_derived'_def
  apply (cases c'; (solves \<open>(wp ensureNoChildren_wp | simp add: isCap_simps Let_def
        | clarsimp simp: badge_derived'_def vsCapRef_def
        | erule cte_wp_at_weakenE' disjE
        | rule is_derived'_def[THEN meta_eq_to_obj_eq, THEN iffD2])+\<close>)?)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
         simp add: X64_H.deriveCap_def Let_def isCap_simps
              split: if_split,
         safe)
        apply ((wp throwError_validE_R undefined_validE_R
                  | clarsimp simp: isCap_simps capAligned_def cte_wp_at_ctes_of
                  | drule valid_capAligned
                  | drule(1) bits_low_high_eq
                  | simp add: capBadge_def sameObjectAs_def
                              is_derived'_def isCap_simps up_ucast_inj_eq
                              is_aligned_no_overflow badge_derived'_def
                              capAligned_def capASID_def
                  | clarsimp split: option.split_asm)+)
  done

lemma arch_deriveCap_untyped_derived[wp]:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. untyped_derived_eq c' (cteCap cte)) slot s\<rbrace>
     X64_H.deriveCap slot (capCap c')
   \<lbrace>\<lambda>rv s. cte_wp_at' (untyped_derived_eq rv o cteCap) slot s\<rbrace>, -"
  apply (wpsimp simp: X64_H.deriveCap_def Let_def untyped_derived_eq_ArchObjectCap
           split_del: if_split
                  wp: undefined_validE_R)
  apply(clarsimp simp: cte_wp_at_ctes_of isCap_simps untyped_derived_eq_def)
  by (case_tac "capCap c'"; fastforce)

lemma deriveCap_untyped_derived:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. untyped_derived_eq c' (cteCap cte)) slot s\<rbrace>
  deriveCap slot c'
  \<lbrace>\<lambda>rv s. cte_wp_at' (untyped_derived_eq rv o cteCap) slot s\<rbrace>, -"
  apply (simp add: global.deriveCap_def split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply (wp arch_deriveCap_inv | simp add: o_def untyped_derived_eq_ArchObjectCap)+
  apply (clarsimp simp: cte_wp_at_ctes_of gen_isCap_simps untyped_derived_eq_def)
  done

lemma corres_caps_decomposition:
  assumes pspace_corres:
    "corres_underlying {(s, s'). pspace_relation (kheap s) (ksPSpace s')} False True r P P' f g"
  assumes updates:
             "\<And>P. \<lbrace>\<lambda>s. P (new_caps s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_mdb s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_list s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cdt_list (s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_rvk s)\<rbrace> f \<lbrace>\<lambda>rv s. P (is_original_cap s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ctes s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ms s)\<rbrace> f \<lbrace>\<lambda>rv s. P (machine_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ms' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_wuc s)\<rbrace> f \<lbrace>\<lambda>rv s. P (work_units_completed s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_wuc' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksWorkUnitsCompleted s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ct s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ct' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_as s)\<rbrace> f \<lbrace>\<lambda>rv s. P (arch_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_as' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_id s)\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_id' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_irqn s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_irqs s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_states s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_irqs' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ups s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ups_of_heap (kheap s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ups' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (gsUserPages s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cns s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cns_of_heap (kheap s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cns' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (gsCNodes s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_sa' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ksReadyQueues s) (new_tcbSchedNexts_of s) (new_tcbSchedPrevs_of s)
                          (\<lambda>d p. new_inQs d p s)\<rbrace>
                   g \<lbrace>\<lambda>rv s. P (ksReadyQueues s) (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                               (\<lambda>d p. inQ d p |< tcbs_of' s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_di s)\<rbrace> f \<lbrace>\<lambda>rv s. P (domain_index s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dl s)\<rbrace> f \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cd s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dt s)\<rbrace> f \<lbrace>\<lambda>rv s. P (domain_time s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dsi' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksDomScheduleIdx s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ds' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cd' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dt' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksDomainTime s)\<rbrace>"
  assumes updated_relations:
    "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
              \<Longrightarrow> cdt_relation ((\<noteq>) None \<circ> new_caps s) (new_mdb s) (new_ctes s')
                  \<and> cdt_list_relation (new_list s) (new_mdb s) (new_ctes s')
                  \<and> ready_queues_relation_2 (new_ready_queues s) (new_ksReadyQueues s')
                                             (new_tcbSchedNexts_of s') (new_tcbSchedPrevs_of s')
                                             (\<lambda>d p. new_inQs d p s')
                  \<and> sched_act_relation (new_action s) (new_sa' s')
                  \<and> revokable_relation (new_rvk s) (null_filter (new_caps s)) (new_ctes s')
                  \<and> interrupt_state_relation (new_irqn s) (new_irqs s) (new_irqs' s')
                  \<and> (new_as s, new_as' s') \<in> arch_state_relation
                  \<and> new_ct s = new_ct' s'
                  \<and> new_id s = new_id' s'
                  \<and> new_ms s = new_ms' s'
                  \<and> new_di s = new_dsi' s'
                  \<and> new_dl s = new_ds' s'
                  \<and> new_cd s = new_cd' s'
                  \<and> new_dt s = new_dt' s'
                  \<and> new_wuc s = new_wuc' s'
                  \<and> new_ups s = new_ups' s'
                  \<and> new_cns s = new_cns' s'"
  shows "corres r P P' f g"
proof -
  have all_ext: "\<And>f f'. (\<forall>p. f p = f' p) = (f = f')"
    by fastforce
  have mdb_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. cdt_relation ((\<noteq>) None \<circ> new_caps s) (new_mdb s) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. \<exists>m ca. (\<forall>p. ca p = ((\<noteq>) None \<circ> caps_of_state s) p) \<and> m = cdt s
                            \<and> cdt_relation ca m ctes\<rbrace>"
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift updates)
    apply (subst all_ext)
    apply (simp add: o_def)
    done
  note mdb_wp = mdb_wp' [simplified all_ext simp_thms]
  have list_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. cdt_list_relation (new_list s) (new_mdb s) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. \<exists>m t. t = cdt_list s \<and> m = cdt s
                            \<and> cdt_list_relation t m ctes\<rbrace>"
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift updates)
    apply (simp add: o_def)
    done
  note list_wp = list_wp' [simplified all_ext simp_thms]
  have rvk_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. revokable_relation (new_rvk s) (null_filter (new_caps s)) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) ctes\<rbrace>"
    unfolding revokable_relation_def
    apply (simp only: imp_conv_disj)
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_disj_lift updates)
    done
  note rvk_wp = rvk_wp' [simplified all_ext simp_thms]
  have swp_cte_at:
    "\<And>s. swp cte_at s = ((\<noteq>) None \<circ> caps_of_state s)"
    by (rule ext, simp, subst neq_commute, simp add: cte_wp_at_caps_of_state)
  have abs_irq_together':
    "\<And>P. \<lbrace>\<lambda>s. P (new_irqn s) (new_irqs s)\<rbrace> f
             \<lbrace>\<lambda>rv s. \<exists>irn. interrupt_irq_node s = irn \<and> P irn (interrupt_states s)\<rbrace>"
    by (wp hoare_vcg_ex_lift updates, simp)
  note abs_irq_together = abs_irq_together'[simplified]
  show ?thesis
    unfolding state_relation_def swp_cte_at
    apply (rule corres_underlying_decomposition[OF pspace_corres])
     apply (simp add: ghost_relation_of_heap)
     apply (wpsimp wp: hoare_vcg_conj_lift mdb_wp rvk_wp list_wp updates abs_irq_together)+
    apply (frule updated_relations)
      apply fastforce
     apply (fastforce simp: state_relation_def swp_cte_at)
    apply (clarsimp simp: o_def Let_def)
    done
qed

lemma create_reply_master_corres[CSpace_R_2_assms]:
  "\<lbrakk> sl' = cte_map sl ; AllowGrant \<in> rights \<rbrakk> \<Longrightarrow>
   corres dc
      (cte_wp_at ((=) cap.NullCap) sl and valid_pspace and valid_mdb and valid_list)
      (cte_wp_at' (\<lambda>c. cteCap c = NullCap \<and> mdbPrev (cteMDBNode c) = 0) sl'
       and valid_mdb' and valid_pspace')
      (do
         y \<leftarrow> set_original sl True;
         set_cap (cap.ReplyCap thread True rights) sl
       od)
      (setCTE sl' (CTE (capability.ReplyCap thread True True) initMDBNode))"
  apply clarsimp
  apply (rule corres_caps_decomposition)
                                     defer
                                     apply (solves \<open>wpsimp\<close>)+
   apply (intro conjI; (solves \<open>simp add: state_relation_def\<close>)?)
       apply (clarsimp simp: o_def cdt_relation_def cte_wp_at_ctes_of
                  split del: if_split cong: if_cong simp del: id_apply)
       apply (case_tac cte, clarsimp)
       apply (fold fun_upd_def)
       apply (subst descendants_of_Null_update')
            apply fastforce
           apply fastforce
          apply assumption
         apply assumption
        apply (simp add: nullPointer_def)
       apply (subgoal_tac "cte_at (a, b) s")
        prefer 2
        apply (drule not_sym, clarsimp simp: cte_wp_at_caps_of_state
                                      split: if_split_asm)
       apply (simp add: state_relation_def cdt_relation_def)
      apply (clarsimp simp: o_def cdt_list_relation_def cte_wp_at_ctes_of
                 split del: if_split cong: if_cong simp del: id_apply)
      apply (case_tac cte, clarsimp)
      apply (clarsimp simp: state_relation_def cdt_list_relation_def)
      apply (simp split: if_split_asm)
      apply (erule_tac x=a in allE, erule_tac x=b in allE)
      apply clarsimp
      apply(case_tac "next_slot (a, b) (cdt_list s) (cdt s)")
       apply simp
      apply simp
      apply (fastforce simp: valid_mdb'_def valid_mdb_ctes_def valid_nullcaps_def)
     apply (clarsimp simp add: revokable_relation_def cte_wp_at_ctes_of
                    split del: if_split)
     apply simp
     apply (rule conjI)
      apply (clarsimp simp: initMDBNode_def)
     apply clarsimp
     apply (subgoal_tac "null_filter (caps_of_state s) (a, b) \<noteq> None")
      prefer 2
      apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state
                     split: if_split_asm)
     apply (subgoal_tac "cte_at (a,b) s")
      prefer 2
      apply clarsimp
      apply (drule null_filter_caps_of_stateD)
      apply (erule cte_wp_cte_at)
     apply (clarsimp split: if_split_asm cong: conj_cong
                      simp: cte_map_eq_subst revokable_relation_simp
                            cte_wp_at_cte_at valid_pspace_def)
    apply (clarsimp elim!: state_relationE simp: ghost_relation_of_heap o_def)+
  apply (rule corres_guard_imp)
    apply (rule corres_underlying_symb_exec_l [OF set_original_symb_exec_l'])
     apply (rule setCTE_corres)
     apply simp
    apply wp
   apply (clarsimp simp: cte_wp_at_cte_at valid_pspace_def)
  apply (clarsimp simp: valid_pspace'_def cte_wp_at'_def)
  done

lemma cte_map_nat_to_cref:
  "\<lbrakk> n < 2 ^ b; b < word_bits \<rbrakk> \<Longrightarrow>
   cte_map (p, nat_to_cref b n) = p + (of_nat n * 2^cte_level_bits)"
  apply (clarsimp simp: cte_map_def nat_to_cref_def shiftl_t2n
                 dest!: less_is_drop_replicate)
  apply (subst mult_ac)
  apply (rule arg_cong [where f="\<lambda>x. x * 2^cte_level_bits"])
  apply (subst of_drop_to_bl)
  apply (simp add: word_bits_def)
  apply (subst mask_eq_iff_w2p)
   apply (simp add: word_size)
  apply (simp add: word_less_nat_alt word_size word_bits_def)
  apply (rule order_le_less_trans; assumption?)
  apply (subst unat_of_nat)
  apply (rule mod_less_eq_dividend)
  done

lemma setupReplyMaster_global_refs[wp]:
  "\<lbrace>\<lambda>s. valid_global_refs' s \<and> thread \<notin> global_refs' s \<and> tcb_at' thread s
      \<and> ex_nonz_cap_to' thread s \<and> valid_objs' s\<rbrace>
    setupReplyMaster thread
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_conv)
  apply (wp getCTE_wp')
  apply (clarsimp simp: capRange_def cte_wp_at_ctes_of objBits_simps)
  apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (rename_tac "prev_cte")
  apply (case_tac prev_cte, simp)
  apply (frule(1) ctes_of_valid_cap')
  apply (drule(1) valid_global_refsD_with_objSize)+
  apply (clarsimp simp: valid_cap'_def objBits_simps' obj_at'_def
                 split: capability.split_asm)
  done

lemma setupReplyMaster_valid_mdb:
  "slot = t + 2 ^ objBits (undefined :: cte) * tcbReplySlot \<Longrightarrow>
   \<lbrace>valid_mdb' and valid_pspace' and tcb_at' t\<rbrace>
   setupReplyMaster t
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (clarsimp simp: setupReplyMaster_def locateSlot_conv
                        nullMDBNode_def)
  apply (fold initMDBNode_def)
  apply (wp setCTE_valid_mdb getCTE_wp')
  apply clarsimp
  apply (intro conjI)
      apply (case_tac cte)
      apply (fastforce simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def
                            no_mdb_def
                      elim: valid_nullcapsE)
     apply (frule obj_at_aligned')
      apply (simp add: valid_cap'_def capAligned_def
                       objBits_simps' word_bits_def)+
    apply (clarsimp simp: valid_pspace'_def)
   apply (clarsimp simp: caps_no_overlap'_def capRange_def)
  apply (clarsimp simp: fresh_virt_cap_class_def
                 elim!: ranE)
  apply (clarsimp simp add: noReplyCapsFor_def cte_wp_at_ctes_of)
  apply (case_tac x)
  apply (rename_tac capability mdbnode)
  apply (case_tac capability; simp)
   apply (rename_tac arch_capability)
   apply (case_tac arch_capability; simp)
  apply fastforce
  done

crunch setupReplyMaster
  for pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"
  (wp: crunch_wps simp: crunch_simps)

lemma setupReplyMaster_valid_pspace':
  "\<lbrace>valid_pspace' and tcb_at' t\<rbrace>
   setupReplyMaster t
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (wp setupReplyMaster_valid_mdb)
   apply (simp_all add: valid_pspace'_def)
  done

crunch setupReplyMaster
  for valid_arch'[wp]: "valid_arch_state'"
  (wp: crunch_wps simp: crunch_simps)

lemma ex_nonz_tcb_cte_caps':
  "\<lbrakk>ex_nonz_cap_to' t s; tcb_at' t s; valid_objs' s; sl \<in> dom tcb_cte_cases\<rbrakk> \<Longrightarrow>
   ex_cte_cap_to' (t + sl) s"
  apply (clarsimp simp: ex_nonz_cap_to'_def ex_cte_cap_to'_def cte_wp_at_ctes_of)
  apply (subgoal_tac "s \<turnstile>' cteCap cte")
   apply (rule_tac x=cref in exI, rule_tac x=cte in exI)
   apply (clarsimp simp: valid_cap'_def obj_at'_def dom_def X64.typ_at_to_obj_at_arches
                  split: cte.split_asm capability.split_asm)
  apply (case_tac cte)
  apply (clarsimp simp: ctes_of_valid_cap')
  done

lemma ex_nonz_cap_not_global':
  "\<lbrakk>ex_nonz_cap_to' t s; valid_objs' s; valid_global_refs' s\<rbrakk> \<Longrightarrow>
   t \<notin> global_refs' s"
  apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (frule(1) valid_global_refsD')
  apply clarsimp
  apply (drule orthD1, erule (1) subsetD)
  apply (subgoal_tac "s \<turnstile>' cteCap cte")
   apply (clarsimp simp: valid_cap'_def capRange_def capAligned_def
                         is_aligned_no_overflow
                  split: cte.split_asm capability.split_asm)
  apply (case_tac cte)
  apply (clarsimp simp: ctes_of_valid_cap')
  done

lemma setupReplyMaster_invs'[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t\<rbrace>
   setupReplyMaster t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
   apply (wpsimp wp: setupReplyMaster_valid_pspace' sch_act_wf_lift tcb_in_cur_domain'_lift
                     ct_idle_or_in_cur_domain'_lift
                     valid_queues_lift cur_tcb_lift hoare_vcg_disj_lift sym_heap_sched_pointers_lift
                     valid_bitmaps_lift valid_irq_node_lift
          | rule refl)+
  apply (clarsimp simp: ex_nonz_tcb_cte_caps' valid_pspace'_def
                        gen_objBits_simps tcbReplySlot_def
                        ex_nonz_cap_not_global' dom_def)
  done

lemma arch_update_setCTE_mdb[CSpace_R_2_assms]:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and cte_wp_at' ((=) oldcte) p and valid_mdb'\<rbrace>
   setCTE p (cteCap_update (\<lambda>_. cap) oldcte)
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (simp add: valid_mdb'_def)
  apply wp
  apply (clarsimp simp: valid_mdb_ctes_def cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (rule conjI)
   apply (rule valid_dlistI)
    apply (fastforce split: if_split_asm elim: valid_dlistE)
   apply (fastforce split: if_split_asm elim: valid_dlistE)
  apply (rule conjI)
   apply (clarsimp simp: no_0_def)
  apply (rule conjI)
   apply (simp add: mdb_chain_0_def mdb_next_trans_next_pres)
   apply blast
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: valid_badges_def valid_arch_badges_def mdb_next_pres simp del: fun_upd_apply)
   apply (clarsimp simp: is_arch_update'_def)
   apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: isCap_simps)
    prefer 2
    subgoal by fastforce
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p in allE)
   apply simp
   apply (simp add: sameRegionAs_def3)
   apply (rule conjI)
    apply (clarsimp simp: isCap_simps)
   apply (clarsimp simp: isCap_simps)
  apply (rule conjI)
   apply (clarsimp simp: caps_contained'_def simp del: fun_upd_apply)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def)
   apply (frule capMaster_untypedRange)
   apply (frule capMaster_capRange)
   apply (drule sym [where s="capMasterCap cap"])
   apply (frule masterCap.intro)
   apply (clarsimp simp: masterCap.isUntypedCap split: if_split_asm)
      subgoal by fastforce
     subgoal by fastforce
    apply (erule_tac x=pa in allE)
    apply (erule_tac x=p in allE)
    apply fastforce
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p' in allE)
   subgoal by fastforce
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def)
   apply (clarsimp simp: mdb_chunked_def mdb_next_trans_next_pres simp del: fun_upd_apply)
   apply (drule sym [where s="capMasterCap cap"])
   apply (frule masterCap.intro)
   apply (clarsimp split: if_split_asm)
     apply (erule_tac x=p in allE)
     apply (erule_tac x=p' in allE)
     apply (clarsimp simp: masterCap.sameRegionAs)
     apply (simp add: masterCap.sameRegionAs is_chunk_def mdb_next_trans_next_pres
                      mdb_next_rtrans_next_pres mdb_chunked_arch_assms_def)
     subgoal by fastforce
    apply (erule_tac x=pa in allE)
    apply (erule_tac x=p in allE)
    apply (clarsimp simp: masterCap.sameRegionAs)
    apply (simp add: masterCap.sameRegionAs is_chunk_def mdb_next_trans_next_pres
                     mdb_next_rtrans_next_pres)
    subgoal by fastforce
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p' in allE)
   apply clarsimp
   apply (simp add: masterCap.sameRegionAs is_chunk_def mdb_next_trans_next_pres
                    mdb_next_rtrans_next_pres)
   subgoal by fastforce
  apply (rule conjI)
   apply (clarsimp simp: is_arch_update'_def untyped_mdb'_def arch_update_descendants'
                   simp del: fun_upd_apply)
   apply (cases oldcte)
   apply clarsimp
   apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: isCap_simps)
   apply (frule capMaster_isUntyped)
   apply (drule capMaster_capRange)
   apply simp
  apply (rule conjI)
   apply (clarsimp simp: untyped_inc'_def arch_update_descendants'
                   simp del: fun_upd_apply)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def)
   apply (drule capMaster_untypedRange)
   apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: isCap_simps)
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p' in allE)
   apply clarsimp
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: valid_nullcaps_def is_arch_update'_def isCap_simps)
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: ut_revocable'_def is_arch_update'_def isCap_simps)
  apply (rule conjI)
   apply (clarsimp simp: class_links_def simp del: fun_upd_apply)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def mdb_next_pres)
   apply (drule capMaster_capClass)
   apply (clarsimp split: if_split_asm)
   apply fastforce
  apply (rule conjI)
   apply (erule(1) distinct_zombies_sameMasterE)
   apply (clarsimp simp: is_arch_update'_def)
  apply (clarsimp simp: irq_control_def)
  apply (cases oldcte)
  apply (subgoal_tac "cap \<noteq> IRQControlCap")
   prefer 2
   apply (clarsimp simp: is_arch_update'_def isCap_simps)
  apply (rule conjI)
   apply clarsimp
  apply (simp add: reply_masters_rvk_fb_def)
  apply (erule ball_ran_fun_updI)
  apply (clarsimp simp add: is_arch_update'_def isCap_simps)
  done

lemma capMaster_zobj_refs[CSpace_R_2_assms]:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> zobj_refs' c = zobj_refs' c'"
  by (simp add: capMasterCap_def arch_capMasterCap_def
           split: capability.splits arch_capability.splits)

lemma zobj_refs_Master[CSpace_R_2_assms]:
  "zobj_refs' (capMasterCap cap) = zobj_refs' cap"
  by (simp add: capMasterCap_def arch_capMasterCap_def
           split: capability.split arch_capability.split)

lemmas [CSpace_R_2_assms] = setCTE_pspace_in_kernel_mappings'

lemma setUntypedCapAsFull_safe_parent_for'[CSpace_R_2_assms]:
  "\<lbrace>\<lambda>s. safe_parent_for' (ctes_of s) slot a \<and> cte_wp_at' ((=) srcCTE) slot s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) c' slot
   \<lbrace>\<lambda>rv s. safe_parent_for' (ctes_of s) slot a\<rbrace>"
  apply (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def setUntypedCapAsFull_def)
  apply (intro conjI impI)
   apply (wp updateCap_ctes_of_wp)
   apply (subgoal_tac "mdb_inv_preserve (ctes_of s)
     (modify_map (ctes_of s) slot
     (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. max_free_index (capBlockSize c')) (cteCap srcCTE))))")
    apply (frule mdb_inv_preserve.descendants_of[where p = slot])
    apply (clarsimp simp: isCap_simps modify_map_def cte_wp_at_ctes_of simp del: fun_upd_apply)
    apply (clarsimp cong:sameRegionAs_update_untyped)
   apply (rule mdb_inv_preserve_updateCap)
    apply (simp add:cte_wp_at_ctes_of)
   apply simp
  apply wp
  apply simp
  done

lemma maskedAsFull_revokable_safe_parent[CSpace_R_2_assms]:
  "\<lbrakk>is_simple_cap' c'; safe_parent_for' m p c'; m p = Some cte;
    cteCap cte = (maskedAsFull src_cap' a)\<rbrakk>
   \<Longrightarrow> isCapRevocable c' (maskedAsFull src_cap' a) = isCapRevocable c' src_cap'"
  apply (clarsimp simp: Retype_H.isCapRevocable_def X64_H.isCapRevocable_def maskedAsFull_def
                  split: if_splits capability.splits arch_capability.splits)
  apply (auto simp: isCap_simps is_simple_cap'_def)
  done

lemma setUntypedCapAsFull_archMDBAssertions[CSpace_R_2_assms, wp]:
  "setUntypedCapAsFull src_cap cap p \<lbrace>archMDBAssertions\<rbrace>"
  unfolding setUntypedCapAsFull_def archMDBAssertions_def updateCap_def
  apply (wpsimp wp: getCTE_wp')
  apply (rename_tac cte, case_tac cte, rename_tac cte_cap node)
  apply (clarsimp simp: arch_mdb_assert_def cte_wp_at_ctes_of isCap_simps split: if_split_asm)
  done

lemma sameRegion_capRange_sub:
  "sameRegionAs cap cap' \<Longrightarrow> capRange cap' \<subseteq> capRange cap"
  apply (clarsimp simp: sameRegionAs_def2 gen_isCap_Master arch_isCap_Master capRange_Master
                  cong: conj_cong)
  apply (erule disjE, fastforce dest!: capMaster_capRange)
  apply (fastforce simp: isCap_simps capRange_def split: if_split_asm)
  done

lemma safe_parent_for_capRange_capBits[CSpace_R_2_assms]:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some cte \<rbrakk> \<Longrightarrow> capRange cap \<subseteq> capRange (cteCap cte)
    \<and> capBits cap \<le> capBits (cteCap cte)"
  apply (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def)
  apply (erule disjE)
   apply (clarsimp simp: capRange_def)
  by (auto simp: sameRegionAs_def2 isCap_simps capRange_def
                    capMasterCap_def capRange_Master objBits_simps
           split: capability.splits arch_capability.splits)

lemma safe_parent_for_descendants'[CSpace_R_2_assms]:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE pcap n); isUntypedCap pcap \<rbrakk> \<Longrightarrow> descendants_of' p m = {}"
  by (auto simp: safe_parent_for'_def safe_parent_for_arch'_def isCap_simps)

lemma safe_parent_not_ep':
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE src_cap n) \<rbrakk> \<Longrightarrow> \<not>isEndpointCap src_cap"
  by (auto simp: safe_parent_for'_def safe_parent_for_arch'_def isCap_simps)

lemma safe_parent_not_ntfn':
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE src_cap n) \<rbrakk> \<Longrightarrow> \<not>isNotificationCap src_cap"
  by (auto simp: safe_parent_for'_def safe_parent_for_arch'_def isCap_simps)

lemma safe_parent_for_untypedRange[CSpace_R_2_assms]:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some cte \<rbrakk> \<Longrightarrow> untypedRange cap \<subseteq> untypedRange (cteCap cte)"
  apply (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def)
  apply (erule disjE)
   apply (fastforce simp: isCap_simps)
  apply (erule disjE)
   apply (fastforce simp: isCap_simps)
  apply (clarsimp simp: sameRegionAs_def2)
  apply (erule disjE)
   apply (fastforce dest!: capMaster_untypedRange)
  apply (erule disjE)
   apply (clarsimp simp: capRange_Master untypedCapRange)
   apply (cases "isUntypedCap cap")
    apply (fastforce simp: capRange_Master untypedCapRange)
   apply (fastforce dest: notUntypedRange)
  apply (clarsimp simp: gen_isCap_Master isCap_simps)
  done

lemma safe_parent_for_capUntypedRange[CSpace_R_2_assms]:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some cte \<rbrakk> \<Longrightarrow> capRange cap \<subseteq> untypedRange (cteCap cte)"
  apply (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def)
  apply (erule disjE)
   apply (fastforce simp: capRange_def isCap_simps)
  apply (erule disjE)
   apply (fastforce simp: capRange_def isCap_simps)
  apply (clarsimp simp: sameRegionAs_def2)
  apply (erule disjE)
   apply (clarsimp dest!: capMaster_capRange simp: capRange_Master untypedCapRange)
  apply (erule disjE)
   apply (fastforce simp: capRange_Master untypedCapRange)
  apply (clarsimp simp: gen_isCap_Master isCap_simps)
  done

lemma safe_parent_capClass[CSpace_R_2_assms]:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE src_cap n) \<rbrakk> \<Longrightarrow> capClass cap = capClass src_cap"
  by (auto simp: safe_parent_for'_def safe_parent_for_arch'_def isCap_simps sameRegionAs_def2
                 capRange_Master capRange_def capMasterCap_def
           split: capability.splits arch_capability.splits)

(* Generic-only parts of is_simple_cap'. isArchFrameCap appears on all architectures and so is safe. *)
lemma is_simple_cap'_genD[CSpace_R_2_assms]:
  "is_simple_cap' cap \<Longrightarrow>
   cap \<noteq> NullCap \<and> cap \<noteq> IRQControlCap \<and> \<not> isUntypedCap cap \<and> \<not> isReplyCap cap \<and>
   \<not> isEndpointCap cap \<and> \<not> isNotificationCap cap \<and> \<not> isThreadCap cap \<and> \<not> isCNodeCap cap \<and>
   \<not> isZombie cap \<and> \<not> isArchFrameCap cap"
  by (simp add: is_simple_cap'_def)

end (* Arch *)

context Arch_mdb_insert_simple begin

lemma dest_no_parent_n:
  "n \<turnstile> dest \<rightarrow> p = False"
  using src simple safe_parent
  apply clarsimp
  apply (erule subtree.induct)
   prefer 2
   apply simp
  apply (clarsimp simp: parentOf_def mdb_next_unfold n_dest new_dest_def n)
  apply (cases "mdbNext src_node = dest")
   apply (subgoal_tac "m \<turnstile> src \<leadsto> dest")
    apply simp
   apply (subst mdb_next_unfold)
   apply (simp add: src)
  apply (clarsimp simp: isMDBParentOf_CTE)
  apply (clarsimp simp: is_simple_cap'_def Retype_H.isCapRevocable_def X64_H.isCapRevocable_def
                 split: capability.splits arch_capability.splits)
     apply (cases c', auto simp: isCap_simps)[1]
    apply (clarsimp simp add: sameRegionAs_def2)
    apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def isCap_simps)
   apply (cases c', auto simp: isCap_simps)[1]
  apply (clarsimp simp add: sameRegionAs_def2)
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def isCap_simps)
  done

lemma src_node_revokable[simp]:
  "mdbRevocable src_node"
  using safe_parent ut_rev src
  apply (clarsimp simp add: safe_parent_for'_def safe_parent_for_arch'_def)
  apply (erule disjE)
   apply clarsimp
   apply (erule irq_revocable, rule irq_control)
  apply (erule disjE)
   apply (clarsimp simp: isCap_simps)
   apply (erule ioport_revocable, rule arch_mdb_assert)
  apply (clarsimp simp: ut_revocable'_def)
  done

lemma new_child[simp]:
  "isMDBParentOf new_src new_dest"
  using safe_parent ut_rev src
  apply (simp add: new_src_def new_dest_def isMDBParentOf_def)
  apply (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def)
  apply (auto simp: isCap_simps)
  done

lemma ut_capRange_non_empty:
  "isUntypedCap src_cap \<Longrightarrow> capRange c' \<noteq> {}"
  using safe_parent src unfolding safe_parent_for'_def safe_parent_for_arch'_def
  by (clarsimp simp: isCap_simps)

end (* Arch_mdb_insert_simple *)

(* requalify dest_no_parent_n+new_child back into mdb_insert_simple *)
context mdb_insert_simple begin

interpretation Arch_mdb_insert_simple by unfold_locales

lemmas dest_no_parent_n = dest_no_parent_n
lemmas new_child = new_child
lemmas ut_capRange_non_empty = ut_capRange_non_empty

end

context Arch begin arch_global_naming

lemmas [CSpace_R_2_assms] = mdb_insert_simple.dest_no_parent_n mdb_insert_simple.new_child

end

interpretation CSpace_R_2?: CSpace_R_2
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact CSpace_R_2_assms)?)?)
qed

(* transfer facts from partial locales (with extra assumptions) into complete locales
   (since we can now satisfy these assumptions) *)

context mdb_insert_simple begin

sublocale mdb_insert_simple_gen
  by (unfold_locales; rule Arch_mdb_insert_simple.dest_no_parent_n Arch_mdb_insert_simple.new_child)+

end

context mdb_insert_simple' begin

sublocale mdb_insert_simple'_gen
  by (unfold_locales, fact ut_capRange_non_empty)

end

locale Arch_mdb_insert_simple' = mdb_insert_simple' + Arch
begin

lemma src_not_ep[simp]:
  "\<not>isEndpointCap src_cap"
  using safe_parent src by (rule safe_parent_not_ep')

lemma src_not_ntfn[simp]:
  "\<not>isNotificationCap src_cap"
  using safe_parent src by (rule safe_parent_not_ntfn')

lemma valid_nc'[simp]:
  "valid_nullcaps n'"
  unfolding valid_nullcaps_def
  using src dest dest_prev dest_next simple safe_parent
  apply (clarsimp simp: n'_def n_def modify_map_if)
  apply (rule conjI)
   apply (clarsimp simp: is_simple_cap'_def)
  apply clarsimp
  apply (rule conjI)
   apply (fastforce dest!: safe_parent_Null)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) valid_nullcaps_next, rule no_0, rule dlist, rule nullcaps)
   apply simp
  apply clarsimp
  apply (erule nullcapsD', rule nullcaps)
  done

lemma valid_badges'[simp]:
  "valid_badges n'"
  supply sameRegion_src[simp del]
  using simple src dest safe_parent
  apply (clarsimp simp: valid_badges_def)
  apply (simp add: n_direct_eq')
  apply (frule_tac p=p in n'_badge)
  apply (frule_tac p=p' in n'_badge)
  apply (drule n'_cap)+
  apply (rule conjI)
   apply (clarsimp simp: is_simple_cap'_def split: if_split_asm)
   apply (insert valid_badges)[1]
   apply (simp add: valid_badges_def)
   apply blast
  (* valid_arch_badges *)
  apply (clarsimp simp: split: if_split_asm)
    apply (clarsimp simp: Retype_H.isCapRevocable_def isCapRevocable_def safe_parent_for'_def
                          safe_parent_for_arch'_def
                          isCap_simps valid_badges_def valid_arch_badges_def)
   apply (insert valid_badges)[1]
   apply (simp add: valid_badges_def)
   apply (erule_tac x=src in allE)
   apply simp
   apply (erule_tac x=p' in allE)
   apply (clarsimp simp: safe_parent_for'_def isCap_simps valid_arch_badges_def)
  apply (insert valid_badges)[1]
  apply (simp add: valid_badges_def valid_arch_badges_def)
  done

lemma sameRegion_src_c':
  "sameRegionAs cap src_cap \<Longrightarrow> sameRegionAs cap c'"
  using safe_parent simple src capRange_c'
  apply (simp add: safe_parent_for'_def safe_parent_for_arch'_def is_simple_cap'_def)
  apply (erule disjE)
   apply (fastforce simp: sameRegionAs_def2 isCap_simps capRange_def)
  apply (clarsimp simp: sameRegionAs_def2 gen_isCap_Master capRange_Master)
  (* these take too long if combined: *)
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps capRange_def)
  apply (erule disjE; clarsimp simp: isCap_simps)
  done

lemma irq_c'_new_handler:
  assumes irq_src: "isIRQControlCap src_cap"
  assumes handler_dest: "isIRQHandlerCap c'"
  shows "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using safe_parent src assms
  apply (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def isCap_simps)
  apply (fastforce simp: sameRegionAs_def2 isCap_simps)
  done

lemma ioport_c'_new:
  assumes ioport_src: "isIOPortControlCap' src_cap"
  shows "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using safe_parent ioport_src src
  by (clarsimp simp: safe_parent_for'_def safe_parent_for_arch'_def isCap_simps sameRegionAs_def2)

lemma ut_capRange_non_empty:
  "isUntypedCap src_cap \<Longrightarrow> capRange c' \<noteq> {}"
  using safe_parent src unfolding safe_parent_for'_def safe_parent_for_arch'_def
  by (clarsimp simp: isCap_simps)

lemma ut_sameRegion_non_empty:
  "\<lbrakk> isUntypedCap src_cap; sameRegionAs c' cap \<rbrakk> \<Longrightarrow> capRange cap \<noteq> {}"
  using simple safe_parent src
  by (clarsimp simp: is_simple_cap'_def sameRegionAs_def2 gen_isCap_Master)
     (force dest!: capMaster_capRange
            simp: safe_parent_for'_def safe_parent_for_arch'_def isCap_simps capRange_def
                  ut_capRange_non_empty)

lemma ut_c'_new:
  assumes ut_src: "isUntypedCap src_cap"
  shows "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using src simple
  apply clarsimp
  apply (drule untyped_mdbD', rule ut_src, assumption)
     apply (clarsimp simp: is_simple_cap'_def sameRegionAs_def2 gen_isCap_Master capRange_Master)
     apply (fastforce simp: isCap_simps)
    apply (frule sameRegion_capRange_sub)
    apply (drule ut_sameRegion_non_empty [OF ut_src])
    apply (insert utCapRange_c')
    apply blast
   apply (rule untyped_mdb)
  apply (simp add: ut_descendants [OF ut_src])
  done

lemma c'_new:
  "\<lbrakk> m p = Some (CTE cap node) \<rbrakk> \<Longrightarrow> \<not> sameRegionAs c' cap"
  using safe_parent src unfolding safe_parent_for'_def safe_parent_for_arch'_def
  apply (elim exE conjE)
  apply (erule disjE)
   apply (erule irq_c'_new_handler [rotated -1])
    apply (clarsimp simp: isCap_simps)
   apply (clarsimp simp: isCap_simps)
  apply (erule disjE)
   apply (erule ioport_c'_new[rotated])
   apply (clarsimp simp: isCap_simps)
  apply clarsimp
  apply (drule (1) ut_c'_new)
  apply simp
  done

lemma irq_control_src:
  "\<lbrakk> isIRQControlCap src_cap;
     m p = Some (CTE cap node);
     sameRegionAs cap c' \<rbrakk> \<Longrightarrow> p = src"
  using safe_parent src unfolding safe_parent_for'_def safe_parent_for_arch'_def
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: sameRegionAs_def2 gen_isCap_Master)
  apply (erule disjE, fastforce simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps capRange_def)
   apply (drule (1) irq_controlD, rule irq_control)
   apply simp
  apply (clarsimp simp: isCap_simps capRange_def)
  done

lemma ioport_control_src:
  "\<lbrakk> isIOPortControlCap' src_cap;
     m p = Some (CTE cap node);
     sameRegionAs cap c' \<rbrakk> \<Longrightarrow> p = src"
  using safe_parent src unfolding safe_parent_for'_def safe_parent_for_arch'_def
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: sameRegionAs_def2 gen_isCap_Master)
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps capRange_def)
  apply (clarsimp simp: isCap_simps split: if_split_asm)
  apply (drule (1) arch_mdb_assertD, rule arch_mdb_assert)
  apply simp
  done

lemma not_irq_ioport_parentD:
  "\<not> isIRQControlCap src_cap \<Longrightarrow> \<not> isIOPortControlCap' src_cap \<Longrightarrow>
  isUntypedCap src_cap \<and> descendants_of' src m = {} \<and> capRange c' \<noteq> {}"
  using src safe_parent unfolding safe_parent_for'_def safe_parent_for_arch'_def
  by (clarsimp simp: isCap_simps)

lemma ut_src_only_ut_c_parents:
  "\<lbrakk> isUntypedCap src_cap; sameRegionAs cap c'; m p = Some (CTE cap node) \<rbrakk> \<Longrightarrow> isUntypedCap cap"
  using safe_parent src unfolding safe_parent_for'_def safe_parent_for_arch'_def
  apply clarsimp
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply clarsimp
  apply (rule ccontr)
  apply (drule (3) untyped_mdbD')
    apply (frule sameRegion_capRange_sub)
    apply (insert utCapRange_c')[1]
    apply blast
   apply (rule untyped_mdb)
  apply simp
  done

lemma ut_src:
  "\<lbrakk> isUntypedCap src_cap; sameRegionAs cap c'; m p = Some (CTE cap node) \<rbrakk> \<Longrightarrow>
   isUntypedCap cap \<and> untypedRange cap \<inter> untypedRange src_cap \<noteq> {}"
  apply (frule (2) ut_src_only_ut_c_parents)
  apply simp
  apply (frule sameRegion_capRange_sub)
  apply (insert utCapRange_c')[1]
  apply (simp add: untypedCapRange)
  apply (drule ut_capRange_non_empty)
  apply blast
  done

lemma chunked'[simp]:
  "mdb_chunked n'"
  using src dest
  apply (clarsimp simp: mdb_chunked_def)
  apply (drule n'_cap)+
  apply (clarsimp simp: n'_trancl_eq)
  apply (clarsimp split: if_split_asm)
    prefer 3
    apply (frule (4) mdb_chunkedD, rule chunked)
    apply clarsimp
    apply (rule conjI, clarsimp)
     apply (clarsimp simp: is_chunk_def n'_trancl_eq n_rtrancl_eq' n_dest' new_dest_def)
     apply (rule conjI, clarsimp)
      apply (rule conjI, clarsimp)
      apply clarsimp
      apply (erule_tac x=src in allE)
      apply simp
      apply (erule sameRegion_src_c')
     apply clarsimp
     apply (erule_tac x=p'' in allE)
     apply clarsimp
     apply (frule_tac p=p'' in m_cap')
     apply clarsimp
    apply clarsimp
    apply (clarsimp simp: is_chunk_def n'_trancl_eq n_rtrancl_eq' n_dest' new_dest_def)
    apply (rule conjI, clarsimp)
     apply (rule conjI, clarsimp)
     apply clarsimp
     apply (erule_tac x=src in allE)
     apply simp
     apply (erule sameRegion_src_c')
    apply clarsimp
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (frule_tac p=p'' in m_cap')
    apply clarsimp
   apply (case_tac "p' = src")
    apply simp
    apply (clarsimp simp: is_chunk_def)
    apply (simp add: n'_trancl_eq n_rtrancl_eq')
    apply (erule disjE)
     apply (simp add: n_dest' new_dest_def)
    apply clarsimp
    apply (drule (1) trancl_rtrancl_trancl)
    apply simp
   apply clarsimp
   apply (drule c'_new)
   apply (erule (1) notE)
  apply (case_tac "p=src")
   apply clarsimp
   apply (clarsimp simp: is_chunk_def)
   apply (simp add: n'_trancl_eq n_rtrancl_eq')
   apply (erule disjE)
    apply (clarsimp simp: n_dest' new_dest_def)
   apply clarsimp
   apply (drule (1) trancl_rtrancl_trancl)
   apply simp
  apply (case_tac "isIRQControlCap src_cap")
   apply (drule (2) irq_control_src)
   apply simp
  apply (case_tac "isIOPortControlCap' src_cap")
   apply (drule (2) ioport_control_src)
   apply simp
  apply (drule (1) not_irq_ioport_parentD)
  apply clarsimp
  apply (frule (2) ut_src)
  apply clarsimp
  apply (subgoal_tac "src \<in> descendants_of' p m")
   prefer 2
   apply (drule (3) untyped_incD', rule untyped_inc)
   apply clarsimp
   apply fastforce
  apply (frule_tac m=m and p=p and p'=src in mdb_chunkedD, assumption+)
      apply (clarsimp simp: descendants_of'_def)
      apply (drule subtree_parent)
      apply (clarsimp simp: parentOf_def isMDBParentOf_def split: if_split_asm)
     apply simp
    apply (simp add: mdb_chunked_arch_assms_def)
   apply (rule chunked)
  apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (rule conjI)
    prefer 2
    apply clarsimp
    apply (drule (1) trancl_trans, simp)
   apply (clarsimp simp: is_chunk_def)
   apply (simp add: n'_trancl_eq n_rtrancl_eq' split: if_split_asm)
    apply (clarsimp simp: n_dest' new_dest_def)
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap')
   apply clarsimp
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) trancl_trans, simp)
  apply (clarsimp simp: descendants_of'_def)
  apply (drule subtree_mdb_next)
  apply (drule (1) trancl_trans)
  apply simp
  done

lemma notZomb:
  "\<not> isZombie src_cap" "\<not> isZombie c'"
  using sameRegion_src simple
  by (auto simp: isCap_simps sameRegionAs_def3
       simp del: sameRegion_src,
      auto simp: is_simple_cap'_def isCap_simps)

lemma distinct_zombies[simp]:
  "distinct_zombies n'"
  using distinct_zombies_m
  apply (simp add: n'_def distinct_zombies_nonCTE_modify_map)
  apply (simp add: n_def modify_map_apply src dest)
  apply (rule distinct_zombies_sameE[rotated])
         apply (simp add: src)
        apply simp+
  apply (cases "isUntypedCap src_cap")
   apply (erule distinct_zombies_seperateE)
   apply (case_tac "y = src")
    apply (clarsimp simp add: src)
   apply (frule(3) untyped_rangefree)
   apply (simp add: capRange_def)
  apply (rule sameRegionAsE [OF sameRegion_src], simp_all)
     apply (erule distinct_zombies_copyMasterE, rule src)
      apply simp
     apply (simp add: notZomb)
    apply (simp add: notArchPage)
   apply (fastforce simp: isCap_simps elim: distinct_zombies_sameMasterE)+
  done

lemma mdb:
  "valid_mdb_ctes n'"
  by (simp add: valid_mdb_ctes_def no_0_n' chain_n')

end (* Arch_mdb_insert_simple' *)

context Arch begin arch_global_naming

named_theorems CSpace_R_3_assms

(* since mdb_insert_simple' is not used after this theory, drop the Arch assumption directly
   instead of requalifying *)
lemmas [CSpace_R_3_assms] = Arch_mdb_insert_simple'.mdb[simplified Arch_mdb_insert_simple'_def]

lemmas [CSpace_R_3_assms] =
  updateCap_valid_arch_state'
  master_cap_relation
  updateMDB_pspace_in_kernel_mappings'

lemma derived'_not_Null:
  "\<not> is_derived' m p c capability.NullCap"
  "\<not> is_derived' m p capability.NullCap c"
  by (clarsimp simp: is_derived'_def badge_derived'_def)+

lemma cte_refs_maskCapRights[simp]:
  "cte_refs' (maskCapRights rghts cap) = cte_refs' cap"
  by (rule ext, cases cap,
      simp_all add: global.maskCapRights_def isCap_defs Let_def
                    X64_H.maskCapRights_def
         split del: if_split
             split: arch_capability.split)

lemma ghost_relation_wrapper_set_cap_setCTE[CSpace_R_3_assms]:
  "\<lbrakk> ghost_relation_wrapper a c;
     ((), c') \<in> fst (setCTE (cte_map slot) (cteCap_update (\<lambda>_. cap') rv) c);
     ((), a') \<in> fst (set_cap cap slot a)\<rbrakk>
   \<Longrightarrow> ghost_relation_wrapper a' c'"
  apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv data_at_def)
  apply (intro allI conjI)
   apply (frule use_valid[OF _ setCTE_gsUserPages]; simp)
  apply (frule use_valid[OF _ setCTE_gsCNodes]; simp)
  done

end

interpretation CSpace_R_3?: CSpace_R_3
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact CSpace_R_3_assms)?)?)
qed

(* transfer facts from partial locales (with extra assumptions) into complete locales
   (since we can satisfy these assumptions) *)
context mdb_move begin

sublocale mdb_move_gen
  by (unfold_locales; rule Arch_mdb_move.parent_preserved Arch_mdb_move.children_preserved)+

end

context Arch begin arch_global_naming

(* createNewCaps can't deal with top-level page table entries on this architecture;
   required for Retype_R setup *)

definition createNewCaps_arch_ko_pre :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> bool" where
  "createNewCaps_arch_ko_pre P \<equiv>
     \<forall>pml4e pml4e'. P (KOArch (KOPML4E pml4e)) = P (KOArch (KOPML4E pml4e'))"

definition createNewCaps_arch_ko_type_pre :: "kernel_object_type \<Rightarrow> bool" where
  "createNewCaps_arch_ko_type_pre ty \<equiv> ty \<noteq> koType(TYPE(pml4e))"

(* interface lemma, but can't be locale assumption due to free type variable  *)
lemma createNewCaps_arch_ko_type_preD:
  "\<lbrakk> createNewCaps_arch_ko_type_pre (koType(TYPE('a::pspace_storable))) \<rbrakk>
   \<Longrightarrow> createNewCaps_arch_ko_pre (\<lambda>ko. \<exists>obj. projectKO_opt ko = Some (obj::'a) \<and> P obj)"
  unfolding createNewCaps_arch_ko_type_pre_def createNewCaps_arch_ko_pre_def
  by (auto dest!: project_koType[THEN iffD1, OF exI])

end (* Arch *)

arch_requalify_consts
  createNewCaps_arch_ko_pre
  createNewCaps_arch_ko_type_pre

(* requalify interface lemmas which can't be locale assumptions due to free type variable *)
arch_requalify_facts
  createNewCaps_arch_ko_type_preD

end
