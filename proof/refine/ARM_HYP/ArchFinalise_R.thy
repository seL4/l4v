(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalise_R
imports
  Finalise_R
begin

context Arch begin arch_global_naming

named_theorems Finalise_R_assms

lemma isArchSGISignalCap_NullCap[simp]:
  "\<not>isArchSGISignalCap NullCap"
  by (simp add: isCap_simps)

lemma arch_postCapDeletion_ksArchState_lift[Finalise_R_assms]:
  "\<lbrakk>\<And>s as. P (s\<lparr>ksArchState := as\<rparr>) = P s\<rbrakk> \<Longrightarrow> Arch.postCapDeletion ac \<lbrace>P\<rbrace>"
  unfolding postCapDeletion_def
  by wpsimp

lemmas clearUntypedFreeIndex_typ_ats[wp] = typ_at_lifts[OF clearUntypedFreeIndex_typ_at']

crunch setIRQState
  for umm[Finalise_R_assms, wp]: "\<lambda>s. P (underlying_memory (ksMachineState s))"
  (wp: dmo_lift' simp: maskInterrupt_def)

(* better crunch names for Arch.postCapDeletion *)
abbreviation (input)
  "Arch_postCapDeletion \<equiv> Arch.postCapDeletion"

crunch Arch_postCapDeletion
  for valid_global_refs[wp]: valid_global_refs'
  and valid_arch_state'[wp]: valid_arch_state'
  (rule: ARM_HYP_H.postCapDeletion_def)

lemma arch_postCapDeletion_corres[Finalise_R_assms]:
  "acap_relation cap cap' \<Longrightarrow> corres dc \<top> \<top> (arch_post_cap_deletion cap) (ARM_HYP_H.postCapDeletion cap')"
  by (clarsimp simp: arch_post_cap_deletion_def ARM_HYP_H.postCapDeletion_def)

(* better crunch names for Arch.finaliseCap *)
abbreviation (input)
  "Arch_finaliseCap \<equiv> Arch.finaliseCap"

crunch Arch_finaliseCap, prepareThreadDelete
  for typ_at'[Finalise_R_assms, wp]: "\<lambda>s. P (typ_at' T p s)"
  and aligned'[Finalise_R_assms, wp]: "pspace_aligned'"
  and distinct'[Finalise_R_assms, wp]: "pspace_distinct'"
  (wp: crunch_wps getObject_inv loadObject_default_inv
   simp: crunch_simps unless_def o_def
   ignore_del: setObject
   rule: ARM_HYP_H.finaliseCap_def)

crunch prepareThreadDelete, Arch_finaliseCap
  for it'[Finalise_R_assms, wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: hoare_drop_imps mapM_wp
   simp: crunch_simps updateObject_default_def
   rule: ARM_HYP_H.finaliseCap_def)

definition
  arch_final_matters' :: "arch_capability \<Rightarrow> bool" where
 "arch_final_matters' acap \<equiv> case acap of
    PageCap ref rghts sz d mapdata \<Rightarrow> False
  | ASIDControlCap \<Rightarrow> False
  | SGISignalCap _ _ \<Rightarrow> False
  | _ \<Rightarrow> True"

definition arch_cap_has_cleanup' :: "arch_capability \<Rightarrow> bool" where
  "arch_cap_has_cleanup' _ \<equiv> False"

definition
  "post_cap_delete_pre' cap sl cs \<equiv> case cap of
     IRQHandlerCap irq \<Rightarrow> irq \<le> maxIRQ \<and> (\<forall>sl'. sl \<noteq> sl' \<longrightarrow> cs sl' \<noteq> Some cap)
   | _ \<Rightarrow> False"

end (* Arch *)

arch_requalify_consts
  arch_final_matters'
  arch_cap_has_cleanup'

context Arch_mdb_empty begin

lemma valid_badges_n:
  "valid_badges n"
proof -
  from valid_badges
  show ?thesis
    supply if_cong[cong]
    supply to_slot_eq[simp del]
    apply (simp add: valid_badges_def2)
    apply clarsimp
    apply (rule conjI)
     prefer 2
     apply (drule_tac p=p in n_cap)
     apply (frule n_cap)
     apply (drule n_badged)
     apply (clarsimp simp: n_next_eq)
     apply (case_tac "p=slot", simp)
     apply clarsimp
     apply (case_tac "p'=slot", simp add: isCap_simps)
     apply clarsimp
     apply (case_tac "p = mdbPrev s_node")
      apply (clarsimp simp: valid_arch_badges_def)
      apply blast
     apply (fastforce simp: valid_arch_badges_def)
    apply (drule_tac p=p in n_cap)
    apply (frule n_cap)
    apply (drule n_badged)
    apply (clarsimp simp: n_next_eq)
    apply (case_tac "p=slot", simp)
    apply clarsimp
    apply (case_tac "p'=slot", simp)
     apply clarsimp
    apply (case_tac "p = mdbPrev s_node")
     apply clarsimp
     apply (insert slot)[1]
      (* using mdb_chunked to show cap in between is same as on either side *)
     apply (subgoal_tac "capMasterCap s_cap = capMasterCap cap'")
      prefer 2
      apply (thin_tac "\<forall>p. P p" for P)
      apply (drule mdb_chunked2D[OF chunked])
            apply (fastforce simp: mdb_next_unfold)
           apply assumption+
         apply (simp add: sameRegionAs_def3)
         apply (intro disjI1)
         apply (fastforce simp:isCap_simps capMasterCap_def arch_capBadge_def split:capability.splits)
        apply clarsimp
       apply (clarsimp simp: isCap_simps mdb_chunked_arch_assms_def)
      apply clarsimp
      apply (erule sameRegionAsE, auto simp: isCap_simps capMasterCap_def split:capability.splits)[1]
     (* instantiating known valid_badges on both sides to transitively
        give the link we need *)
     apply (frule_tac x="mdbPrev s_node" in spec)
     apply simp
     apply (drule spec, drule spec, drule spec,
            drule(1) mp, drule(1) mp)
     apply simp
     apply (drule_tac x=slot in spec)
     apply (drule_tac x="mdbNext s_node" in spec)
     apply simp
     apply (drule mp, simp(no_asm) add: mdb_next_unfold)
      apply simp
     apply (cases "capBadge s_cap", simp_all)[1]
    apply clarsimp
    apply (case_tac "p' = mdbNext s_node")
     apply clarsimp
     apply (frule vdlist_next_src_unique[where y=slot])
        apply (simp add: mdb_next_unfold slot)
       apply clarsimp
      apply (rule dlist)
     apply clarsimp
    apply clarsimp
    apply fastforce
    done
qed

lemma n_parent_of:
  "\<lbrakk> n \<turnstile> p parentOf p'; p \<noteq> slot; p' \<noteq> slot \<rbrakk> \<Longrightarrow> m \<turnstile> p parentOf p'"
  supply if_cong[cong]
  apply (clarsimp simp: parentOf_def)
  apply (case_tac cte, case_tac cte')
  apply clarsimp
  apply (frule_tac p=p in n_cap)
  apply (frule_tac p=p in n_badged)
  apply (drule_tac p=p in n_revokable)
  apply (clarsimp)
  apply (frule_tac p=p' in n_cap)
  apply (frule_tac p=p' in n_badged)
  apply (drule_tac p=p' in n_revokable)
  apply (clarsimp split: if_split_asm)
  by (auto simp: isMDBParentOf_def isArchMDBParentOf_def2 isCap_simps split: if_split_asm)

lemma m_parent_of:
  "\<lbrakk> m \<turnstile> p parentOf p'; p \<noteq> slot; p' \<noteq> slot; p\<noteq>p'; p'\<noteq>mdbNext s_node \<rbrakk> \<Longrightarrow> n \<turnstile> p parentOf p'"
  supply if_cong[cong]
  apply (clarsimp simp add: parentOf_def)
  apply (case_tac cte, case_tac cte')
  apply clarsimp
  apply (frule_tac p=p in m_cap)
  apply (frule_tac p=p in m_badged)
  apply (drule_tac p=p in m_revokable)
  apply clarsimp
  apply (frule_tac p=p' in m_cap)
  apply (frule_tac p=p' in m_badged)
  apply (drule_tac p=p' in m_revokable)
  apply clarsimp
  by (fastforce simp: isMDBParentOf_def isArchMDBParentOf_def2 isCap_simps
                split: if_split_asm)

lemma m_parent_of_next:
  "\<lbrakk> m \<turnstile> p parentOf mdbNext s_node; m \<turnstile> p parentOf slot; p \<noteq> slot; p\<noteq>mdbNext s_node \<rbrakk>
  \<Longrightarrow> n \<turnstile> p parentOf mdbNext s_node"
  using slot
  apply (clarsimp simp add: parentOf_def)
  apply (case_tac cte'a, case_tac cte)
  apply clarsimp
  apply (frule_tac p=p in m_cap)
  apply (frule_tac p=p in m_badged)
  apply (drule_tac p=p in m_revokable)
  apply (frule_tac p="mdbNext s_node" in m_cap)
  apply (frule_tac p="mdbNext s_node" in m_badged)
  apply (drule_tac p="mdbNext s_node" in m_revokable)
  apply (frule_tac p="slot" in m_cap)
  apply (frule_tac p="slot" in m_badged)
  apply (drule_tac p="slot" in m_revokable)
  by (auto simp: isMDBParentOf_def isArchMDBParentOf_def2 isCap_simps
           split: if_split_asm cong: if_cong)

lemma parency_n:
  assumes "n \<turnstile> p \<rightarrow> p'"
  shows "m \<turnstile> p \<rightarrow> p' \<and> p \<noteq> slot \<and> p' \<noteq> slot"
  using assms
proof induct
  case (direct_parent c')
  moreover
  hence "p \<noteq> slot"
    by (clarsimp simp: n_next_eq)
  moreover
  from direct_parent
  have "c' \<noteq> slot"
    by (clarsimp simp add: n_next_eq split: if_split_asm)
  ultimately
  show ?case
    apply simp
    apply (simp add: n_next_eq split: if_split_asm)
     prefer 2
     apply (erule (1) subtree.direct_parent)
     apply (erule (2) n_parent_of)
    apply clarsimp
    apply (frule n_parent_of, simp, simp)
    apply (prop_tac "\<exists>prev_cap prev_node. m (mdbPrev s_node) = Some (CTE prev_cap prev_node)")
     apply (clarsimp simp: parentOf_def, case_tac cte'a, clarsimp)
    apply clarsimp
    apply (case_tac "isArchSGISignalCap prev_cap")
     prefer 2
     apply (rule subtree.trans_parent[OF _ m_slot_next], simp_all)
     apply (rule subtree.direct_parent)
       apply (erule prev_slot_next)
      apply simp
     apply (clarsimp simp: parentOf_def slot)
     apply (case_tac cte, rename_tac next_cap next_node)
     apply clarsimp
     apply (frule(2) mdb_chunked2D [OF chunked prev_slot_next m_slot_next])
        apply (clarsimp simp: isMDBParentOf_CTE)
       apply simp
      apply (simp add: mdb_chunked_arch_assms_def)
     apply (simp add: slot)
     apply (clarsimp simp add: isMDBParentOf_CTE)
     apply (insert valid_badges)[1]
     apply (simp add: valid_badges_def2)
     apply (drule spec[where x=slot])
     apply (drule spec[where x="mdbNext s_node"])
     apply (simp add: slot m_slot_next)
     apply (insert valid_badges)[1]
     apply (simp add: valid_badges_def2)
     apply (drule spec[where x="mdbPrev s_node"])
     apply (drule spec[where x=slot])
     apply (simp add: slot prev_slot_next)
     apply (case_tac ctea, case_tac cte')
     apply (rename_tac cap'' node'')
     apply (clarsimp simp: isMDBParentOf_CTE)
     apply (frule n_cap, drule n_badged)
     apply (frule n_cap, drule n_badged)
     apply clarsimp
     apply (case_tac cap'', simp_all add: isCap_simps)[1]
      apply (clarsimp simp: sameRegionAs_def3 isCap_simps)
     apply (clarsimp simp: sameRegionAs_def3 isCap_simps)
     apply (rename_tac acap'')
     apply (case_tac acap''; clarsimp simp: sameRegionAs_def3 isCap_simps)
    (* SGISignalCap *)
    apply (clarsimp simp: parentOf_def isCap_simps isMDBParentOf_CTE)
    apply (rename_tac next_node)
    apply (rule subtree.trans_parent[OF _ m_slot_next], simp_all)
     apply (rule subtree.direct_parent)
       apply (erule prev_slot_next)
      apply simp
     prefer 2
     apply (clarsimp simp: parentOf_def slot isMDBParentOf_CTE)
    apply (clarsimp simp: parentOf_def slot isMDBParentOf_CTE isCap_simps)
    apply (cases "mdbFirstBadged s_node", simp)
     apply (case_tac ctea, case_tac cte', clarsimp)
     apply (frule n_cap, drule n_badged)
     apply (frule n_cap, drule n_badged)
     apply clarsimp
     apply (rename_tac prev_node' next_node')
     apply (clarsimp simp: isMDBParentOf_CTE isCap_simps)
    apply simp
    apply (insert valid_badges)[1]
    apply (clarsimp simp: valid_badges_def)
    apply (erule_tac x="slot" in allE)
    apply (erule_tac x="mdbNext s_node" in allE)
    apply (simp add: slot m_p_next isCap_simps valid_arch_badges_def)
    done
next
  case (trans_parent c c')
  moreover
  hence "p \<noteq> slot"
    by (clarsimp simp: n_next_eq)
  moreover
  from trans_parent
  have "c' \<noteq> slot"
    by (clarsimp simp add: n_next_eq split: if_split_asm)
  ultimately
  show ?case
    apply clarsimp
    apply (simp add: n_next_eq split: if_split_asm)
     prefer 2
     apply (erule (2) subtree.trans_parent)
     apply (erule n_parent_of, simp, simp)
    apply clarsimp
    apply (rule subtree.trans_parent)
       apply (rule subtree.trans_parent, assumption)
         apply (rule prev_slot_next)
         apply clarsimp
        apply clarsimp
       apply (frule n_parent_of, simp, simp)
       apply (clarsimp simp: parentOf_def slot)
       apply (case_tac cte'a)
       apply (rename_tac cap node)
       apply (case_tac ctea)
       apply clarsimp
       apply (case_tac "\<not>isArchSGISignalCap cap")
        apply (prop_tac "sameRegionAs cap s_cap")
         apply (insert chunked)[1]
         apply (simp add: mdb_chunked_def)
         apply (erule_tac x="p" in allE)
         apply (erule_tac x="mdbNext s_node" in allE)
         apply simp
         apply (drule isMDBParent_sameRegion)+
         apply clarsimp
         apply (prop_tac "m \<turnstile> p \<leadsto>\<^sup>+ slot")
          apply (rule trancl_trans)
           apply (erule subtree_mdb_next)
          apply (rule r_into_trancl)
          apply (rule prev_slot_next)
          apply clarsimp
         apply (prop_tac "m \<turnstile> p \<leadsto>\<^sup>+ mdbNext s_node")
          apply (erule trancl_trans)
          apply fastforce
         apply (simp add: mdb_chunked_arch_assms_def)
         apply (erule impE)
          apply clarsimp
         apply clarsimp
         apply (thin_tac "s \<longrightarrow> t" for s t)
         apply (simp add: is_chunk_def)
         apply (erule_tac x=slot in allE)
         apply (erule impE, fastforce)
         apply (erule impE, fastforce)
         apply (clarsimp simp: slot)
        apply (clarsimp simp: isMDBParentOf_CTE)
        apply (insert valid_badges, simp add: valid_badges_def2)[1]
        apply (drule spec[where x=slot], drule spec[where x="mdbNext s_node"])
        apply (simp add: slot m_slot_next)
        apply (case_tac cte, case_tac cte')
        apply (rename_tac cap'' node'')
        apply (clarsimp simp: isMDBParentOf_CTE)
        apply (frule n_cap, drule n_badged)
        apply (frule n_cap, drule n_badged)
        apply (clarsimp split: if_split_asm)
         apply (drule subtree_mdb_next)
         apply (drule no_loops_tranclE[OF no_loops])
         apply (erule notE, rule trancl_into_rtrancl)
         apply (rule trancl.intros(2)[OF _ m_slot_next])
         apply (rule trancl.intros(1), rule prev_slot_next)
         apply simp
        apply (case_tac cap'', simp_all add: isCap_simps)[1]
         apply (clarsimp simp: sameRegionAs_def3 isCap_simps)
        apply (clarsimp simp: sameRegionAs_def3 isCap_simps)
        apply (rename_tac acap'')
        apply (case_tac acap''; clarsimp simp: sameRegionAs_def3 isCap_simps)
       (* SGISignalCap *)
       apply (rename_tac next_cap next_node)
       apply (clarsimp simp: isCap_simps)
       apply (case_tac cte, case_tac cte')
       apply (rename_tac cap'' node'')
       apply (clarsimp simp: isMDBParentOf_CTE)
       apply (frule n_cap, drule n_badged)
       apply (frule n_cap, drule n_badged)
       apply (clarsimp simp: isCap_simps)
       apply (insert valid_badges)[1]
       apply (clarsimp simp: valid_badges_def)
       apply (erule_tac x="slot" in allE)
       apply (erule_tac x="mdbNext s_node" in allE)
       apply (simp add: slot m_p_next isCap_simps valid_arch_badges_def)
      apply (rule m_slot_next)
     apply simp
    apply (erule n_parent_of, simp, simp)
    done
qed

end (* Arch_mdb_empty *)

context mdb_empty begin

lemmas gen_arch_assms =
  Arch_mdb_empty.valid_badges_n
  Arch_mdb_empty.parency_n
  Arch_mdb_empty.m_parent_of
  Arch_mdb_empty.m_parent_of_next

(* extract arch-dependent assumptions of mdb_empty_gen proved in Arch_mdb_empty
   (faster than interpreting Arch) *)
lemmas gen_assms = gen_arch_assms[unfolded Arch_mdb_empty_def, OF mdb_empty_axioms]

sublocale mdb_empty_gen
  by (unfold_locales)
     (blast intro!: gen_assms)+

(* re-bind names *)
lemmas vmdb_n = vmdb_n
lemmas descendants = descendants

end (* mdb_empty *)

interpretation Finalise_R?: Finalise_R arch_final_matters' arch_cap_has_cleanup'
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Finalise_R_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems Finalise_R_2_assms

lemma not_Final_removeable[Finalise_R_2_assms]:
  "\<not> isFinal cap sl (cteCaps_of s) \<Longrightarrow> removeable' sl s cap"
  apply (erule not_FinalE)
   apply (clarsimp simp: removeable'_def gen_isCap_simps)
  apply (clarsimp simp: cteCaps_of_def ARM_HYP.sameObjectAs_def2 removeable'_def
                        cte_wp_at_ctes_of)
  apply fastforce
  done

lemma deletedIRQHandler_valid_global_refs[Finalise_R_2_assms, wp]:
  "\<lbrace>valid_global_refs'\<rbrace> deletedIRQHandler irq \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (clarsimp simp: valid_global_refs'_def global_refs'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF deletedIRQHandler_irq_node'])
   apply (rule hoare_use_eq [where f=ksIdleThread, OF deletedIRQHandler_ksIdle])
   apply (rule hoare_use_eq [where f=ksArchState, OF deletedIRQHandler_ksArch])
   apply (rule hoare_use_eq[where f="gsMaxObjectSize"], wp)
   apply (simp add: valid_refs'_cteCaps valid_cap_sizes_cteCaps)
   apply (rule deletedIRQHandler_cteCaps_of)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: valid_refs'_cteCaps valid_cap_sizes_cteCaps ball_ran_eq)
  done

lemma clearUntypedFreeIndex_valid_global_refs[Finalise_R_2_assms, wp]:
  "\<lbrace>valid_global_refs'\<rbrace> clearUntypedFreeIndex irq \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (clarsimp simp: valid_global_refs'_def global_refs'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF clearUntypedFreeIndex_irq_node'])
   apply (rule hoare_use_eq [where f=ksIdleThread, OF clearUntypedFreeIndex_ksIdle])
   apply (rule hoare_use_eq [where f=ksArchState, OF clearUntypedFreeIndex_ksArch])
   apply (rule hoare_use_eq[where f="gsMaxObjectSize"], wp)
   apply (simp add: valid_refs'_cteCaps valid_cap_sizes_cteCaps)
   apply (rule clearUntypedFreeIndex_cteCaps_of)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: valid_refs'_cteCaps valid_cap_sizes_cteCaps ball_ran_eq)
  done

lemma final_matters_Master:
  "final_matters' (capMasterCap cap) = final_matters' cap"
  by (simp add: capMasterCap_def arch_capMasterCap_def split: capability.split arch_capability.split,
      simp add: final_matters'_def arch_final_matters'_def)

lemma final_matters_sameRegion_sameObject:
  "final_matters' cap \<Longrightarrow> sameRegionAs cap cap' = sameObjectAs cap cap'"
  apply (rule iffI)
   apply (erule sameRegionAsE)
      apply (simp add: sameObjectAs_def3)
      apply (clarsimp simp: isCap_simps sameObjectAs_sameRegionAs
                            final_matters'_def arch_final_matters'_def
                      split: capability.splits arch_capability.splits)+
  done

lemma final_matters_sameRegion_sameObject2:
  "\<lbrakk> final_matters' cap'; \<not> isUntypedCap cap; \<not> isIRQHandlerCap cap' \<rbrakk>
   \<Longrightarrow> sameRegionAs cap cap' = sameObjectAs cap cap'"
  apply (rule iffI)
   apply (erule sameRegionAsE)
       apply (simp add: sameObjectAs_def3)
       apply (fastforce simp: isCap_simps final_matters'_def arch_final_matters'_def)
      apply simp
     apply (clarsimp simp: final_matters'_def arch_final_matters'_def isCap_simps)+
  apply (erule sameObjectAs_sameRegionAs)
  done

lemma final_matters_mdb_chunked_arch_assms:
  "final_matters' cap \<Longrightarrow> mdb_chunked_arch_assms cap"
  by (clarsimp simp: mdb_chunked_arch_assms_def isCap_simps
                     final_matters'_def arch_final_matters'_def)

lemma notFinal_prev_or_next[Finalise_R_2_assms]:
  "\<lbrakk> \<not> isFinal cap x (cteCaps_of s); mdb_chunked (ctes_of s);
     valid_dlist (ctes_of s); no_0 (ctes_of s);
     ctes_of s x = Some (CTE cap node); final_matters' cap \<rbrakk>
   \<Longrightarrow> (\<exists>cap' node'. ctes_of s (mdbPrev node) = Some (CTE cap' node') \<and> sameObjectAs cap cap')
      \<or> (\<exists>cap' node'. ctes_of s (mdbNext node) = Some (CTE cap' node') \<and> sameObjectAs cap cap')"
  apply (erule not_FinalE)
   apply (clarsimp simp: isCap_simps final_matters'_def)
  apply (frule final_matters_mdb_chunked_arch_assms)
  apply (clarsimp simp: mdb_chunked_def cte_wp_at_ctes_of cteCaps_of_def
                   del: disjCI)
  apply (erule_tac x=x in allE, erule_tac x=p in allE)
  apply simp
  apply (case_tac z, simp add: sameObjectAs_sameRegionAs)
  apply (elim conjE disjE, simp_all add: is_chunk_def)
   apply (rule disjI2)
   apply (drule tranclD)
   apply (clarsimp simp: mdb_next_unfold)
   apply (drule spec[where x="mdbNext node"])
   apply simp
   apply (drule mp[where P="ctes_of s \<turnstile> x \<leadsto>\<^sup>+ mdbNext node"])
    apply (rule trancl.intros(1), simp add: mdb_next_unfold)
   apply clarsimp
   apply (drule rtranclD)
   apply (erule disjE, clarsimp+)
   apply (drule tranclD)
   apply (clarsimp simp: mdb_next_unfold final_matters_sameRegion_sameObject)
  apply (rule disjI1)
  apply clarsimp
  apply (drule tranclD2)
  apply clarsimp
  apply (frule vdlist_nextD0)
    apply clarsimp
   apply assumption
  apply (clarsimp simp: mdb_prev_def)
  apply (drule rtranclD)
  apply (erule disjE, clarsimp+)
  apply (drule spec, drule(1) mp)
  apply (drule mp, rule trancl_into_rtrancl, erule trancl.intros(1))
  apply clarsimp
  apply (drule iffD1 [OF final_matters_sameRegion_sameObject, rotated])
   apply (subst final_matters_Master[symmetric])
   apply (subst(asm) final_matters_Master[symmetric])
   apply (clarsimp simp: sameObjectAs_def3)
  apply (clarsimp simp: sameObjectAs_def3 simp del: isArchFrameCap_capMasterCap)
  done

lemma sameObjectAs_not_Untyped[Finalise_R_2_assms]:
  "\<lbrakk> global.sameObjectAs cap cap'; \<not> isUntypedCap cap \<rbrakk>
   \<Longrightarrow> \<not> isUntypedCap cap'"
  by (clarsimp simp: gen_isCap_simps sameObjectAs_def3)

lemma sameObjectAs_not_Untyped'[Finalise_R_2_assms]:
  "\<lbrakk> global.sameObjectAs cap cap'; \<not> isUntypedCap cap' \<rbrakk>
   \<Longrightarrow> global.sameObjectAs cap' cap"
  by (clarsimp simp: isCap_simps sameObjectAs_def3)

end (* Arch *)

(* only two arch-specific lemmas in vmdb;
   save processing time by not creating an extra Arch_vmdb locale, directly requalify instead *)

lemma (in vmdb) isFinal_no_subtree:
  "\<lbrakk> m \<turnstile> sl \<rightarrow> p; isFinal cap sl (option_map cteCap o m);
      m sl = Some (CTE cap n); final_matters' cap \<rbrakk> \<Longrightarrow> False"
  apply (erule subtree.induct)
   apply (case_tac "c'=sl", simp)
   apply (clarsimp simp: isFinal_def parentOf_def mdb_next_unfold cteCaps_of_def)
   apply (erule_tac x="mdbNext n" in allE)
   apply simp
   apply (clarsimp simp: ARM_HYP.isMDBParentOf_CTE ARM_HYP.final_matters_sameRegion_sameObject)
   apply (clarsimp simp: gen_isCap_simps ARM_HYP.sameObjectAs_def3)
  apply clarsimp
  done

lemma (in vmdb) isFinal_untypedParent:
  assumes x: "m slot = Some cte" "isFinal (cteCap cte) slot (option_map cteCap o m)"
             "final_matters' (cteCap cte) \<and> \<not> isIRQHandlerCap (cteCap cte)"
  shows
  "m \<turnstile> x \<rightarrow> slot \<Longrightarrow>
  (\<exists>cte'. m x = Some cte' \<and> isUntypedCap (cteCap cte') \<and> RetypeDecls_H.sameRegionAs (cteCap cte') (cteCap cte))"
  apply (cases "x=slot", simp)
  apply (insert x)
  apply (frule subtree_mdb_next)
  apply (drule subtree_parent)
  apply (drule tranclD)
  apply clarsimp
  apply (clarsimp simp: mdb_next_unfold parentOf_def isFinal_def)
  apply (case_tac cte')
  apply (rename_tac c' n')
  apply (cases cte)
  apply (rename_tac c n)
  apply simp
  apply (erule_tac x=x in allE)
  apply clarsimp
  apply (drule isMDBParent_sameRegion)
  apply simp
  apply (frule ARM_HYP.final_matters_mdb_chunked_arch_assms)
  apply (rule classical, simp)
  apply (simp add: ARM_HYP.final_matters_sameRegion_sameObject2
                   sameObjectAs_sym)
  done

context Arch begin arch_global_naming

lemma isFinal_no_descendants:
  "\<lbrakk> isFinal cap sl (cteCaps_of s); ctes_of s sl = Some (CTE cap n);
      valid_mdb' s; final_matters' cap \<rbrakk>
  \<Longrightarrow> descendants_of' sl (ctes_of s) = {}"
  apply (clarsimp simp add: descendants_of'_def cteCaps_of_def)
  apply (erule(3) vmdb.isFinal_no_subtree[rotated])
  apply unfold_locales[1]
  apply (simp add: valid_mdb'_def)
  done

lemmas cancelAllIPC_typs[wp] = typ_at_lifts[OF cancelAllIPC_typ_at']
lemmas cancelAllSignals_typs[wp] = typ_at_lifts[OF cancelAllSignals_typ_at']
lemmas suspend_typs[wp] = typ_at_lifts[OF suspend_typ_at']

lemmas finaliseCap_typ_ats[wp] = typ_at_lifts[OF finaliseCap_typ_at']

crunch flushSpace
  for invs'[wp]: "invs'"
  (ignore: doMachineOp)

lemma invalidateASIDEntry_invs'[wp]:
  "invalidateASIDEntry asid \<lbrace>invs'\<rbrace>"
  apply (simp add: invalidateASIDEntry_def invalidateASID_def
                   invalidateHWASIDEntry_def bind_assoc)
  apply (wp loadHWASID_wp | simp)+
  apply (clarsimp simp: fun_upd_def[symmetric])
  apply (rule conjI)
   apply (clarsimp simp: invs'_def valid_state'_def)
   apply (rule conjI)
    apply (simp add: valid_global_refs'_def
                     global_refs'_def)
   apply (simp add: valid_arch_state'_def ran_def
                    valid_asid_table'_def is_inv_None_upd
                    valid_machine_state'_def
                    comp_upd_simp fun_upd_def[symmetric]
                    inj_on_fun_upd_elsewhere
                    valid_asid_map'_def
                    ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
             cong: option.case_cong)
   subgoal by (auto elim!: subset_inj_on)
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (rule conjI)
   apply (simp add: valid_global_refs'_def global_refs'_def)
  apply (rule conjI)
   apply (simp add: valid_arch_state'_def ran_def
                    valid_asid_table'_def comp_upd_simp
              cong: option.case_cong)
  apply (simp add: valid_machine_state'_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma invs_asid_update_strg':
  "invs' s \<and> tab = armKSASIDTable (ksArchState s) \<longrightarrow>
   invs' (s\<lparr>ksArchState := armKSASIDTable_update
            (\<lambda>_. tab (asid := None)) (ksArchState s)\<rparr>)"
  apply (simp add: invs'_def)
  apply (simp add: valid_state'_def)
  apply (simp add: valid_global_refs'_def global_refs'_def valid_arch_state'_def
                   valid_asid_table'_def valid_machine_state'_def ct_idle_or_in_cur_domain'_def
                   tcb_in_cur_domain'_def
             cong: option.case_cong)
  apply (auto simp add: ran_def split: if_split_asm)
  done

crunch invalidateTLBByASID
  for asidTable[wp]: "\<lambda>s. P (armKSASIDTable (ksArchState s))"

lemma deleteASIDPool_invs[wp]:
  "\<lbrace>invs'\<rbrace> deleteASIDPool asid pool \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: deleteASIDPool_def)
  apply wp
      apply (simp del: fun_upd_apply)
      apply (strengthen invs_asid_update_strg')
      apply (wpsimp wp: mapM_wp' getObject_inv loadObject_default_inv)+
  done

lemma deleteASID_invs'[wp]:
  "deleteASID asid pd \<lbrace>invs'\<rbrace>"
  apply (simp add: deleteASID_def cong: option.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
    apply (rule_tac Q'="\<lambda>rv. valid_obj' (injectKO rv) and invs'"
              in hoare_post_imp)
     apply (rename_tac rv s)
     apply (clarsimp split: if_split_asm del: subsetI)
     apply (simp add: fun_upd_def[symmetric] valid_obj'_def)
     apply (case_tac rv, simp)
     apply (subst inv_f_f, rule inj_onI, simp)+
     apply (rule conjI)
      apply clarsimp
      apply (drule subsetD, blast)
      apply clarsimp
     apply (auto dest!: ran_del_subset)[1]
    apply (wp getObject_valid_obj getObject_inv loadObject_default_inv
             | simp add: objBits_simps pageBits_def)+
  apply clarsimp
  done

lemmas archThreadSet_typ_ats[wp] = typ_at_lifts[OF archThreadSet_typ_at']

lemma archThreadSet_valid_objs'[wp]:
  "\<lbrace>valid_objs' and (\<lambda>s. \<forall>tcb. ko_at' tcb t s \<longrightarrow> valid_arch_tcb' (f (tcbArch tcb)) s)\<rbrace>
   archThreadSet f t \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding archThreadSet_def
  apply (wp setObject_tcb_valid_objs getObject_tcb_wp)
  apply clarsimp
  apply normalise_obj_at'
  apply (drule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (clarsimp simp: valid_obj'_def valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

crunch archThreadSet
  for no_0_obj'[wp]: no_0_obj'

lemma archThreadSet_ctes_of[wp]:
  "archThreadSet f t \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: getObject_tcb_wp)
  apply normalise_obj_at'
  apply (auto simp: tcb_cte_cases_def cteSizeBits_def)
  done

crunch archThreadSet
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (wp: setObject_cd_inv)

lemma archThreadSet_obj_at':
  "(\<And>tcb. P tcb \<Longrightarrow> P (tcb \<lparr> tcbArch:= f (tcbArch tcb)\<rparr>)) \<Longrightarrow> archThreadSet f t \<lbrace>obj_at' P t'\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: getObject_tcb_wp setObject_tcb_strongest)
  apply normalise_obj_at'
  apply auto
  done

lemma archThreadSet_tcbDomain[wp]:
  "archThreadSet f t \<lbrace>obj_at' (\<lambda>tcb. x = tcbDomain tcb) t'\<rbrace>"
  by (wpsimp wp: archThreadSet_obj_at')

lemma archThreadSet_inQ[wp]:
  "archThreadSet f t' \<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace>"
  unfolding obj_at'_real_def archThreadSet_def
  apply (wpsimp wp: setObject_ko_wp_at getObject_tcb_wp
              simp: objBits_simps' archObjSize_def vcpuBits_def pageBits_def
         | simp)+
  apply (auto simp: obj_at'_def ko_wp_at'_def)
  done

crunch archThreadSet
  for ct[wp]: "\<lambda>s. P (ksCurThread s)"
  and sched[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and L1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and L2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  and ksArch[wp]: "\<lambda>s. P (ksArchState s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and pspace_canonical'[wp]: pspace_canonical'
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  (wp: setObject_ct_inv setObject_sa_unchanged setObject_ksDomSchedule_inv)

crunch archThreadSet
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksDomScheduleStart[wp]: "\<lambda>s. P (ksDomScheduleStart s)"
  (simp: setObject_def wp: updateObject_default_inv)

crunch archThreadSet
  for ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  (wp: setObject_ksMachine updateObject_default_inv)

lemma archThreadSet_state_refs_of'[wp]:
  "archThreadSet f t \<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: setObject_tcb_state_refs_of' getObject_tcb_wp)
  apply normalise_obj_at'
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (auto simp: state_refs_of'_def obj_at'_def)
  done

lemma archThreadSet_state_hyp_refs_of'[wp]:
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at' tcb t s \<longrightarrow> P ((state_hyp_refs_of' s)(t := tcb_hyp_refs' (f (tcbArch tcb))))\<rbrace>
  archThreadSet f t \<lbrace>\<lambda>_ s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: setObject_state_hyp_refs_of' getObject_tcb_wp simp: objBits_simps')
  apply normalise_obj_at'
  apply (erule rsubst[where P=P])
  apply auto
  done

crunch archThreadSet
  for ko_at'_pde[wp]: "\<lambda>s. P (ko_at' (pde::pde) p' s)"
  and valid_pde_mappings'[wp]: valid_pde_mappings'

lemma archThreadSet_if_live'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and>
        (\<forall>tcb. ko_at' tcb t s \<longrightarrow> atcbVCPUPtr (f (tcbArch tcb)) \<noteq> None \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
  archThreadSet f t \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: setObject_tcb_iflive' getObject_tcb_wp)
  apply normalise_obj_at'
  apply (clarsimp simp: tcb_cte_cases_def if_live_then_nonz_cap'_def cteSizeBits_def)
  apply (erule_tac x=t in allE)
  apply (erule impE)
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def live'_def hyp_live'_def)
  apply simp
  done

lemma archThreadSet_ifunsafe'[wp]:
  "archThreadSet f t \<lbrace>if_unsafe_then_cap'\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: setObject_tcb_ifunsafe' getObject_tcb_wp)
  apply normalise_obj_at'
  apply (auto simp: tcb_cte_cases_def if_live_then_nonz_cap'_def cteSizeBits_def)
  done

lemma archThreadSet_valid_idle'[wp]:
  "archThreadSet f t \<lbrace>valid_idle'\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: setObject_tcb_idle' getObject_tcb_wp)
  apply (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def idle_tcb'_def)
  done

lemma archThreadSet_ko_wp_at_no_vcpu[wp]:
  "archThreadSet f t \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: getObject_tcb_wp setObject_ko_wp_at simp: objBits_simps' | rule refl)+
  apply normalise_obj_at'
  apply (auto simp: ko_wp_at'_def obj_at'_real_def is_vcpu'_def)
  done

lemma archThreadSet_valid_arch_state'[wp]:
  "archThreadSet f t \<lbrace>valid_arch_state'\<rbrace>"
  unfolding valid_arch_state'_def valid_asid_table'_def option_case_all_conv split_def
  apply (rule hoare_lift_Pf[where f=ksArchState]; wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply (clarsimp simp: pred_conj_def)
  done

lemma archThreadSet_ct_not_inQ[wp]:
  "archThreadSet f t \<lbrace>ct_not_inQ\<rbrace>"
  unfolding ct_not_inQ_def
  apply (rule hoare_lift_Pf[where f=ksCurThread]; wp?)
  apply (wpsimp wp: hoare_vcg_imp_lift simp: o_def)
  done

lemma archThreadSet_obj_at'_pte[wp]:
  "archThreadSet f t \<lbrace>obj_at' (P::pte \<Rightarrow> bool) p\<rbrace>"
  unfolding archThreadSet_def
  by (wpsimp wp: obj_at_setObject2 simp: updateObject_default_def in_monad)

crunch archThreadSet
  for pspace_domain_valid[wp]: pspace_domain_valid

crunch archThreadSet
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"

lemma archThreadSet_untyped_ranges_zero'[wp]:
  "archThreadSet f t \<lbrace>untyped_ranges_zero'\<rbrace>"
  by (rule hoare_lift_Pf[where f=cteCaps_of]; wp cteCaps_of_ctes_of_lift)

lemma archThreadSet_tcb_at'[wp]:
  "\<lbrace>\<top>\<rbrace> archThreadSet f t \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  unfolding archThreadSet_def
  by (wpsimp wp: getObject_tcb_wp simp: obj_at'_def)

lemma archThreadSet_tcbSchedPrevs_of[wp]:
  "archThreadSet f t \<lbrace>\<lambda>s. P (tcbSchedPrevs_of s)\<rbrace>"
  unfolding archThreadSet_def
  apply (wp getObject_tcb_wp)
  apply normalise_obj_at'
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (clarsimp simp: opt_map_def obj_at'_def split: option.splits)
  done

lemma archThreadSet_tcbSchedNexts_of[wp]:
  "archThreadSet f t \<lbrace>\<lambda>s. P (tcbSchedNexts_of s)\<rbrace>"
  unfolding archThreadSet_def
  apply (wp getObject_tcb_wp)
  apply normalise_obj_at'
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (clarsimp simp: opt_map_def obj_at'_def split: option.splits)
  done

lemma archThreadSet_tcbQueued[wp]:
  "archThreadSet f t \<lbrace>\<lambda>s. P (tcbQueued |< tcbs_of' s)\<rbrace>"
  unfolding archThreadSet_def
  apply (wp getObject_tcb_wp)
  apply normalise_obj_at'
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (clarsimp simp: opt_pred_def opt_map_def obj_at'_def split: option.splits)
  done

lemma archThreadSet_valid_sched_pointers[wp]:
  "archThreadSet f t \<lbrace>valid_sched_pointers\<rbrace>"
  by (wp_pre, wps, wp, assumption)

lemma dissoc_invs':
  "\<lbrace>invs' and (\<lambda>s. \<forall>p. (\<exists>a. armHSCurVCPU (ksArchState s) = Some (p, a)) \<longrightarrow> p \<noteq> v) and
    ko_at' vcpu v and K (vcpuTCBPtr vcpu = Some t) and
    obj_at' (\<lambda>tcb. atcbVCPUPtr (tcbArch tcb) = Some v) t\<rbrace>
   do
    archThreadSet (atcbVCPUPtr_update (\<lambda>_. Nothing)) t;
    setObject v $ vcpuTCBPtr_update (\<lambda>_. Nothing) vcpu
   od \<lbrace>\<lambda>_. invs' and tcb_at' t\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_tcb_valid_objs setObject_vcpu_valid_objs'
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    setObject_typ_at' cur_tcb_lift valid_bitmaps_lift valid_dom_schedule'_lift
                    setVCPU_valid_arch' archThreadSet_if_live' sym_heap_sched_pointers_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb valid_arch_tcb'_def
        | clarsimp simp: live'_def hyp_live'_def arch_live'_def)+
  supply fun_upd_apply[simp]
  apply (clarsimp simp: state_hyp_refs_of'_def obj_at'_def tcb_vcpu_refs'_def valid_vcpu'_def
                  split: option.splits if_split_asm)
  apply safe
   apply (rule_tac rfs'="state_hyp_refs_of' s" in delta_sym_refs)
     apply (clarsimp simp: state_hyp_refs_of'_def obj_at'_def tcb_vcpu_refs'_def
                     split: option.splits if_split_asm)+
  done

lemma setVCPU_archThreadSet_None_eq:
  "do
    archThreadSet (atcbVCPUPtr_update (\<lambda>_. Nothing)) t;
    setObject v $ vcpuTCBPtr_update (\<lambda>_. Nothing) vcpu;
    f
   od = do
    do
      archThreadSet (atcbVCPUPtr_update (\<lambda>_. Nothing)) t;
      setObject v $ vcpuTCBPtr_update (\<lambda>_. Nothing) vcpu
    od;
    f
  od" by (simp add: bind_assoc)

lemma vcpuInvalidateActive_inactive[wp]:
  "\<lbrace>\<top>\<rbrace> vcpuInvalidateActive \<lbrace>\<lambda>rv s. \<forall>p. (\<exists>a. armHSCurVCPU (ksArchState s) = Some (p, a)) \<longrightarrow> P p rv s\<rbrace>"
  unfolding vcpuInvalidateActive_def modifyArchState_def by wpsimp

lemma vcpuDisableNone_obj_at'[wp]:
  "vcpuDisable None \<lbrace>\<lambda>s. P (obj_at' P' p s)\<rbrace>"
  unfolding vcpuDisable_def by wpsimp

lemma vcpuInvalidateActive_obj_at'[wp]:
  "vcpuInvalidateActive \<lbrace>\<lambda>s. P (obj_at' P' p s)\<rbrace>"
  unfolding vcpuInvalidateActive_def modifyArchState_def by wpsimp

lemma dissociateVCPUTCB_invs'[wp]:
  "dissociateVCPUTCB vcpu tcb \<lbrace>invs'\<rbrace>"
  unfolding dissociateVCPUTCB_def setVCPU_archThreadSet_None_eq when_assert_eq
  apply (wpsimp wp: dissoc_invs' getVCPU_wp | wpsimp wp: getObject_tcb_wp simp: archThreadGet_def)+
  apply (drule tcb_ko_at')
  apply clarsimp
  apply (rule exI, rule conjI, assumption)
  apply clarsimp
  apply (rule conjI)
   apply normalise_obj_at'
  apply (rule conjI)
   apply normalise_obj_at'
  apply (clarsimp simp: obj_at'_def)
  done

lemma vcpuFinalise_invs'[wp]: "vcpuFinalise vcpu \<lbrace>invs'\<rbrace>"
  unfolding vcpuFinalise_def by wpsimp

lemma arch_finaliseCap_invs[Finalise_R_2_assms, wp]:
  "\<lbrace>invs' and valid_cap' (ArchObjectCap cap)\<rbrace> Arch.finaliseCap cap fin \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding ARM_HYP_H.finaliseCap_def Let_def by wpsimp

lemma setObject_tcb_unlive[wp]:
   "\<lbrace>\<lambda>s. vr \<noteq> t \<and> ko_wp_at' (Not \<circ> live') vr s\<rbrace>
        setObject t (tcbArch_update (\<lambda>_. atcbVCPUPtr_update Map.empty (tcbArch tcb)) tcb)
           \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') vr\<rbrace>"
  apply (rule wp_pre)
  apply (wpsimp wp: setObject_ko_wp_at simp: objBits_simps', simp+)
  apply (clarsimp simp: tcb_at_typ_at' typ_at'_def ko_wp_at'_def )
  done

lemma setVCPU_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> setObject vr (vcpuTCBPtr_update Map.empty vcpu) \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') vr\<rbrace>"
  apply (rule wp_pre)
  apply (wpsimp wp: setObject_ko_wp_at
           simp: objBits_def objBitsKO_def archObjSize_def vcpu_bits_def pageBits_def)
    apply simp+
  apply (clarsimp simp: live'_def hyp_live'_def arch_live'_def ko_wp_at'_def obj_at'_def)
  done

lemma asUser_unlive[wp]:
  "\<lbrace>ko_wp_at' (Not \<circ> live') vr\<rbrace> asUser t f \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> live') vr\<rbrace>"
  unfolding asUser_def
  apply (wpsimp simp: threadSet_def atcbContextSet_def objBits_simps' split_def
                  wp: setObject_ko_wp_at)
  apply (rule refl, simp)
  apply (wpsimp simp: atcbContextGet_def wp: getObject_tcb_wp threadGet_wp)+
  apply (clarsimp simp: tcb_at_typ_at' typ_at'_def ko_wp_at'_def[where p=t])
  apply (case_tac ko; simp)
  apply (rename_tac tcb)
  apply (rule_tac x=tcb in exI)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def live'_def hyp_live'_def)
  done

lemma dissociateVCPUTCB_unlive:
  "\<lbrace> \<top> \<rbrace> dissociateVCPUTCB vcpu tcb \<lbrace> \<lambda>_. ko_wp_at' (Not o live') vcpu \<rbrace>"
  unfolding dissociateVCPUTCB_def setVCPU_archThreadSet_None_eq when_assert_eq
  by (wpsimp wp: getVCPU_wp[where p=vcpu] |
      wpsimp wp: getObject_tcb_wp hoare_vcg_conj_lift hoare_vcg_ex_lift
                 getVCPU_wp[where p=vcpu] setVCPU_unlive[simplified o_def]
                 setObject_tcb_unlive hoare_drop_imp setObject_tcb_strongest
             simp: archThreadGet_def archThreadSet_def)+

lemma vcpuFinalise_unlive[wp]:
  "\<lbrace> \<top> \<rbrace> vcpuFinalise v \<lbrace> \<lambda>_. ko_wp_at' (Not o live') v \<rbrace>"
  apply (wpsimp simp: vcpuFinalise_def wp: dissociateVCPUTCB_unlive getVCPU_wp)
  apply (frule state_hyp_refs_of'_vcpu_absorb)
  apply (auto simp: ko_wp_at'_def)
  apply (rule_tac x="KOArch (KOVCPU ko)" in exI)
  apply (clarsimp simp: live'_def hyp_live'_def arch_live'_def obj_at'_def)
  done

crunch setVMRoot, deleteASIDPool, invalidateTLBByASID, invalidateASIDEntry, vcpuFinalise
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps getObject_inv loadObject_default_inv getASID_wp simp: crunch_simps)

lemma deleteASID_ctes_of[wp]:
  "deleteASID a ptr \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  unfolding deleteASID_def by (wpsimp wp: getASID_wp hoare_drop_imps hoare_vcg_all_lift)

lemma arch_finaliseCap_removeable[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile>' ArchObjectCap cap \<and> invs' s
       \<and> (final_matters' (ArchObjectCap cap)
               \<longrightarrow> (final = isFinal (ArchObjectCap cap) slot (cteCaps_of s))) \<rbrace>
     Arch.finaliseCap cap final
   \<lbrace>\<lambda>rv s. isNullCap (fst rv) \<and> removeable' slot s (ArchObjectCap cap) \<and> isNullCap (snd rv)\<rbrace>"
  unfolding ARM_HYP_H.finaliseCap_def
  including classic_wp_pre
  apply (case_tac cap; clarsimp)
        apply ((wpsimp simp: removeable'_def isCap_simps
                 | rule conjI)+)[5]
   apply (clarsimp simp: isCap_simps, rule conjI)
    apply (wpsimp simp: isCap_simps removeable'_def wp: hoare_disjI2)
   apply (wpsimp simp: not_Final_removeable final_matters'_def arch_final_matters'_def)
  apply (wpsimp simp: isCap_simps removeable'_def)
  done

crunch archThreadSet, vcpuUpdate, dissociateVCPUTCB
  for isFinal: "\<lambda>s. isFinal cap slot (cteCaps_of s)"
  (wp: cteCaps_of_ctes_of_lift)

crunch prepareThreadDelete
  for isFinal: "\<lambda>s. isFinal cap slot (cteCaps_of s)"

lemma archThreadSet_bound_tcb_at'[wp]:
  "archThreadSet f t \<lbrace>bound_tcb_at' P t'\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: setObject_tcb_strongest getObject_tcb_wp simp: pred_tcb_at'_def)
  by (auto simp: obj_at'_def objBits_simps)

lemmas setObject_vcpu_pred_tcb_at'[wp] =
  setObject_vcpu_obj_at'_no_vcpu [of _ "\<lambda>ko. tst (pr (tcb_to_itcb' ko))" for tst pr, folded pred_tcb_at'_def]

crunch dissociateVCPUTCB, vgicUpdateLR, prepareThreadDelete
  for bound_tcb_at'[wp]: "bound_tcb_at' P t"
  (wp: sts_bound_tcb_at' getVCPU_wp crunch_wps hoare_vcg_all_lift hoare_vcg_if_lift3
   ignore: archThreadSet)

lemma dissociateVCPUTCB_cte_wp_at'[wp]:
  "dissociateVCPUTCB v t \<lbrace>cte_wp_at' P p\<rbrace>"
  unfolding cte_wp_at_ctes_of by wp

lemmas dissociateVCPUTCB_typ_ats'[wp] = typ_at_lifts[OF dissociateVCPUTCB_typ_at']

crunch Arch.finaliseCap, prepareThreadDelete
  for irq_node'[Finalise_R_2_assms, wp]: "\<lambda>s. P (irq_node' s)"
  (wp: crunch_wps getObject_inv loadObject_default_inv
       updateObject_default_inv setObject_ksInterrupt
   simp: crunch_simps o_def)

lemmas Arch_finaliseCap_irq_node'[Finalise_R_2_assms] = ArchRetypeDecls_H_ARM_HYP_H_finaliseCap_irq_node'

crunch prepareThreadDelete
  for cte_wp_at'[Finalise_R_2_assms, wp]: "cte_wp_at' P p"
  and valid_cap'[Finalise_R_2_assms, wp]: "valid_cap' cap"

lemma unset_vcpu_hyp_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> archThreadSet (atcbVCPUPtr_update Map.empty) t \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> hyp_live') t\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: setObject_ko_wp_at' getObject_tcb_wp; (simp add: objBits_simps')?)+
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def hyp_live'_def)
  done

 lemma unset_tcb_hyp_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> setObject vr (vcpuTCBPtr_update Map.empty vcpu) \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> hyp_live') vr\<rbrace>"
  apply (wpsimp wp: setObject_ko_wp_at' getObject_tcb_wp
                simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
        | simp)+
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def hyp_live'_def arch_live'_def)
  done

lemma setObject_vcpu_hyp_unlive[wp]:
   "\<lbrace>\<lambda>s. t \<noteq> vr \<and> ko_wp_at' (Not \<circ> hyp_live') t s\<rbrace>
         setObject vr (vcpuTCBPtr_update Map.empty vcpu)
    \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> hyp_live') t\<rbrace>"
  apply (rule wp_pre)
  apply (wpsimp wp: setObject_ko_wp_at
                simp: objBits_def objBitsKO_def archObjSize_def vcpu_bits_def pageBits_def
        | simp)+
  apply (clarsimp simp: tcb_at_typ_at' typ_at'_def ko_wp_at'_def )
  done

lemma asUser_hyp_unlive[wp]:
  "asUser f t \<lbrace>ko_wp_at' (Not \<circ> hyp_live') t'\<rbrace>"
  unfolding asUser_def
  apply (wpsimp wp: threadSet_ko_wp_at2' threadGet_wp)
  apply (clarsimp simp: ko_wp_at'_def obj_at'_def hyp_live'_def atcbContextSet_def)
  done

lemma dissociateVCPUTCB_hyp_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> dissociateVCPUTCB v t \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> hyp_live') t\<rbrace>"
  unfolding dissociateVCPUTCB_def
  by (cases "v = t"; wpsimp wp: unset_tcb_hyp_unlive unset_vcpu_hyp_unlive[simplified comp_def])

lemma prepareThreadDelete_hyp_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> prepareThreadDelete t \<lbrace>\<lambda>_. ko_wp_at' (Not \<circ> hyp_live') t\<rbrace>"
  unfolding prepareThreadDelete_def archThreadGet_def
  apply (wpsimp wp: getObject_tcb_wp hoare_vcg_imp_lift' hoare_vcg_ex_lift)
  apply (auto simp: ko_wp_at'_def obj_at'_def hyp_live'_def)
  done

crunch prepareThreadDelete
  for invs[Finalise_R_2_assms, wp]: "invs'"
  (ignore: doMachineOp simp: crunch_simps)

lemma archThreadSet_tcbSchedPrevNext[wp]:
  "archThreadSet f t' \<lbrace>obj_at' (\<lambda>tcb. P (tcbSchedNext tcb) (tcbSchedPrev tcb)) t\<rbrace>"
  unfolding archThreadSet_def
  apply (wpsimp wp: setObject_tcb_strongest getObject_tcb_wp)
  apply normalise_obj_at'
  apply auto
  done

context notes if_cong[cong] begin

crunch asUser
  for tcbSchedPrevNext[wp]: "obj_at' (\<lambda>tcb. P (tcbSchedNext tcb) (tcbSchedPrev tcb)) t"
  (wp: threadGet_wp)

end

crunch prepareThreadDelete
  for tcbSchedPrevNext[wp]: "obj_at' (\<lambda>tcb. P (tcbSchedNext tcb) (tcbSchedPrev tcb)) t"
  (wp: threadGet_wp getVCPU_wp archThreadGet_wp crunch_wps simp: crunch_simps)

crunch deleteASIDPool
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  (simp: crunch_simps assertE_def
   wp: crunch_wps getObject_inv loadObject_default_inv)

lemma deleteASID_cte_wp_at'[wp]:
  "\<lbrace>cte_wp_at' P p\<rbrace> deleteASID param_a param_b \<lbrace>\<lambda>_. cte_wp_at' P p\<rbrace>"
  apply (simp add: deleteASID_def
              cong: option.case_cong)
  apply (wp setObject_cte_wp_at'[where Q="\<top>"] getObject_inv
            loadObject_default_inv setVMRoot_cte_wp_at'
          | clarsimp simp: updateObject_default_def in_monad cong: if_cong
          | rule equals0I
          | wpc)+
  done

crunch vcpuFinalise
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  (wp: crunch_wps getObject_inv loadObject_default_inv)

lemma arch_finaliseCap_cte_wp_at[Finalise_R_2_assms, wp]:
  "\<lbrace>cte_wp_at' P p\<rbrace> Arch.finaliseCap cap fin \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  unfolding ARM_HYP_H.finaliseCap_def
  by (wpsimp wp: unmapPage_cte_wp_at'|rule conjI)+

lemma finaliseCap_valid_cap[Finalise_R_2_assms, wp]:
  "\<lbrace>\<top>\<rbrace> Arch.finaliseCap cap final \<lbrace>\<lambda>rv. valid_cap' (fst rv)\<rbrace>"
  by (wpsimp simp: ARM_HYP_H.finaliseCap_def split_del: if_split)

lemma finaliseCap_cases[wp]:
  "\<lbrace>\<top>\<rbrace>
   finaliseCap cap final flag
   \<lbrace>\<lambda>rv s. fst rv = NullCap \<and> (snd rv \<noteq> NullCap \<longrightarrow> final \<and> cap_has_cleanup' cap \<and> snd rv = cap)
           \<or> isZombie (fst rv) \<and> final \<and> \<not> flag \<and> snd rv = NullCap
             \<and> capUntypedPtr (fst rv) = capUntypedPtr cap
             \<and> (isThreadCap cap \<or> isCNodeCap cap \<or> isZombie cap)\<rbrace>"
  apply (simp add: finaliseCap_def ARM_HYP_H.finaliseCap_def Let_def
                   getThreadCSpaceRoot
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply ((wp | simp add: gen_isCap_simps split del: if_split
              | wpc
              | simp only: valid_NullCap fst_conv snd_conv)+)[1]
  apply (simp only: simp_thms fst_conv snd_conv option.simps if_cancel
                    o_def)
  apply (intro allI impI conjI TrueI)
  apply (auto simp add: gen_isCap_simps cap_has_cleanup'_def)
  done

lemmas [Finalise_R_2_assms] =
  cancelAllIPC_cte_wp_at' cancelAllSignals_cte_wp_at' unbindMaybeNotification_cte_wp_at'
  prepareThreadDelete_cte_wp_at' unbindNotification_cte_wp_at'
  Arch_postCapDeletion_valid_global_refs Arch_postCapDeletion_valid_arch_state'
  mdb_empty.vmdb_n mdb_empty.descendants not_Final_removeable

end (* Arch *)

interpretation Finalise_R_2?: Finalise_R_2 arch_final_matters' arch_cap_has_cleanup'
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Finalise_R_2_assms)?)?)
qed

(* this is the only arch-specific lemma in delete_one_conc_pre so far;
   save processing time by not creating an extra Arch_delete_one_conc_pre locale
   by directly requalifying instead *)
lemma (in delete_one_conc_pre) finaliseCap_replaceable:
  "\<lbrace>\<lambda>s. invs' s \<and> cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot s
       \<and> (final_matters' cap \<longrightarrow> (final = isFinal cap slot (cteCaps_of s)))
       \<and> weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
     finaliseCap cap final flag
   \<lbrace>\<lambda>rv s. (isNullCap (fst rv) \<and> removeable' slot s cap
                \<and> (snd rv \<noteq> NullCap \<longrightarrow> snd rv = cap \<and> cap_has_cleanup' cap
                                      \<and> isFinal cap slot (cteCaps_of s)))
        \<or>
          (isZombie (fst rv) \<and> snd rv = NullCap
            \<and> isFinal cap slot (cteCaps_of s)
            \<and> capClass cap = capClass (fst rv)
            \<and> capUntypedPtr (fst rv) = capUntypedPtr cap
            \<and> capBits (fst rv) = capBits cap
            \<and> capRange (fst rv) = capRange cap
            \<and> (isThreadCap cap \<or> isCNodeCap cap \<or> isZombie cap)
            \<and> (\<forall>p \<in> threadCapRefs cap. st_tcb_at' ((=) Inactive) p s
                     \<and> obj_at' (Not \<circ> tcbQueued) p s
                     \<and> bound_tcb_at' ((=) None) p s
                     \<and> ko_wp_at' (Not \<circ> hyp_live') p s
                     \<and> obj_at' (\<lambda>tcb. tcbSchedNext tcb = None \<and> tcbSchedPrev tcb = None) p s))\<rbrace>"
  supply [wp] = ARM_HYP.prepareThreadDelete_bound_tcb_at' ARM_HYP.prepareThreadDelete_hyp_unlive
                ARM_HYP.prepareThreadDelete_tcbSchedPrevNext
  apply (simp add: finaliseCap_def Let_def getThreadCSpaceRoot
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp prepares_delete_helper'' [OF cancelAllIPC_unlive]
             prepares_delete_helper'' [OF cancelAllSignals_unlive]
             suspend_isFinal ARM_HYP.prepareThreadDelete_unqueued
             ARM_HYP.prepareThreadDelete_inactive ARM_HYP.prepareThreadDelete_isFinal
             suspend_makes_inactive
             deletingIRQHandler_removeable'
             deletingIRQHandler_final[where slot=slot ]
             unbindMaybeNotification_obj_at'_bound
             getNotification_wp
             suspend_bound_tcb_at'
             unbindNotification_bound_tcb_at'
             suspend_tcbSchedNext_tcbSchedPrev_None
           | simp add: isZombie_Null isThreadCap_threadCapRefs_tcbptr
                       isArchObjectCap_Cap_capCap
           | (rule hoare_strengthen_post[OF ARM_HYP.arch_finaliseCap_removeable[where slot=slot]],
                  clarsimp simp: gen_isCap_simps)
           | wpc)+
  apply clarsimp
  apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp+)
  apply (case_tac "cteCap cte",
         simp_all add: gen_isCap_simps capRange_def cap_has_cleanup'_def
                       final_matters'_def gen_objBits_simps
                       not_Final_removeable finaliseCap_def,
         simp_all add: removeable'_def)
     (* thread *)
     apply (frule capAligned_capUntypedPtr [OF valid_capAligned], simp)
     apply (clarsimp simp: valid_cap'_def)
     apply (drule valid_globals_cte_wpD'[rotated], clarsimp)
     apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
    apply (clarsimp simp: obj_at'_def | rule conjI)+
  done

context Arch begin arch_global_naming

named_theorems Finalise_R_3_assms

lemma finaliseCap_cte_refs:
  "\<lbrace>\<lambda>s. s \<turnstile>' cap\<rbrace>
     finaliseCap cap final flag
   \<lbrace>\<lambda>rv s. fst rv \<noteq> NullCap \<longrightarrow> cte_refs' (fst rv) = cte_refs' cap\<rbrace>"
  apply (simp add: global.finaliseCap_def Let_def getThreadCSpaceRoot finaliseCap_def
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc | simp only: o_def)+
  apply (frule valid_capAligned)
  apply (cases cap, simp_all add: gen_isCap_simps)
   apply (clarsimp simp: tcb_cte_cases_def word_count_from_top gen_objBits_simps)
  apply clarsimp
  apply (rule ext, simp)
  apply (rule image_cong [OF _ refl])
  apply (fastforce simp: mask_def capAligned_def gen_objBits_simps shiftL_nat)
  done

lemma emptySlot_invs'[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> cte_wp_at' (\<lambda>cte. removeable' sl s (cteCap cte)) sl s
            \<and> (\<forall>sl'. info \<noteq> NullCap \<longrightarrow> sl' \<noteq> sl \<longrightarrow> cteCaps_of s sl' \<noteq> Some info)\<rbrace>
     emptySlot sl info
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wp valid_irq_node_lift cur_tcb_lift valid_dom_schedule'_lift)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma cteDeleteOne_invs[Finalise_R_3_assms, wp]:
  "cteDeleteOne ptr \<lbrace>invs'\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def
                   split_def finaliseCapTrue_standin_simple_def)
  apply wp
    apply (rule hoare_strengthen_post)
     apply (rule hoare_vcg_conj_lift[OF finaliseCap_True_invs])
     apply (rule hoare_vcg_conj_lift[OF finaliseCap_replaceable[where slot=ptr]])
     apply (rule hoare_vcg_conj_lift[OF finaliseCap_cte_refs])
     apply (rule finaliseCap_equal_cap[where sl=ptr])
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (erule disjE, solves simp)
    apply (clarsimp dest!: isCapDs simp: capRemovable_def)
    apply (clarsimp simp: removeable'_def fun_eq_iff[where f="cte_refs' cap" for cap]
                     del: disjCI)
    subgoal by (auto dest!: isCapDs simp: pred_tcb_at'_def obj_at'_def live'_def ko_wp_at'_def)
   apply (wp isFinalCapability_inv getCTE_wp' hoare_weak_lift_imp
          | wp (once) isFinal[where x=ptr])+
  apply (fastforce simp: cte_wp_at_ctes_of)
  done

lemma isFinalCapability_corres'[Finalise_R_3_assms]:
  "final_matters' (cteCap cte) \<Longrightarrow>
   corres (=) (invs and cte_wp_at ((=) cap) ptr)
               (invs' and cte_wp_at' ((=) cte) (cte_map ptr))
       (is_final_cap cap) (isFinalCapability cte)"
  apply (rule corres_gets_lift)
      apply (rule isFinalCapability_inv)
     apply (rule isFinal[where x="cte_map ptr"])
    apply clarsimp
    apply (rule conjI, clarsimp)
    apply (rule refl)
   apply (rule no_fail_pre, wp, fastforce)
  apply (simp add: is_final_cap_def)
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def state_relation_def)
  apply (frule (1) pspace_relation_ctes_ofI)
    apply fastforce
   apply fastforce
  apply clarsimp
  apply (rule iffI)
   apply (simp add: is_final_cap'_def2 isFinal_def)
   apply clarsimp
   apply (subgoal_tac "obj_refs cap \<noteq> {} \<or> cap_irqs cap \<noteq> {} \<or> arch_gen_refs cap \<noteq> {}")
    prefer 2
    apply (erule_tac x=a in allE)
    apply (erule_tac x=b in allE)
    apply (clarsimp simp: cte_wp_at_def gen_obj_refs_Int)
   apply (subgoal_tac "ptr = (a,b)")
    prefer 2
    apply (erule_tac x="fst ptr" in allE)
    apply (erule_tac x="snd ptr" in allE)
    apply (clarsimp simp: cte_wp_at_def gen_obj_refs_Int)
   apply clarsimp
   apply (rule context_conjI)
    apply (clarsimp simp: isCap_simps)
    apply (cases cap, auto)[1]
   apply clarsimp
   apply (drule_tac x=p' in pspace_relation_cte_wp_atI, assumption)
    apply fastforce
   apply clarsimp
   apply (erule_tac x=aa in allE)
   apply (erule_tac x=ba in allE)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (clarsimp simp: sameObjectAs_def3 obj_refs_relation_Master cap_irqs_relation_Master
                         arch_gen_refs_relation_Master gen_obj_refs_Int
                   cong: if_cong
                  split: capability.split_asm)
  apply (clarsimp simp: isFinal_def is_final_cap'_def3)
  apply (rule_tac x="fst ptr" in exI)
  apply (rule_tac x="snd ptr" in exI)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_def final_matters'_def arch_final_matters'_def
                         gen_obj_refs_Int
                  split: cap_relation_split_asm arch_cap.split_asm)
  apply clarsimp
  apply (drule_tac p="(a,b)" in cte_wp_at_norm)
  apply clarsimp
  apply (frule_tac slot="(a,b)" in pspace_relation_ctes_ofI, assumption)
    apply fastforce
   apply fastforce
  apply clarsimp
  apply (frule_tac p="(a,b)" in cte_wp_valid_cap, fastforce)
  apply (erule_tac x="cte_map (a,b)" in allE)
  apply simp
  apply (erule impCE, simp, drule cte_map_inj_eq)
        apply (erule cte_wp_at_weakenE, rule TrueI)
       apply (erule cte_wp_at_weakenE, rule TrueI)
      apply fastforce
     apply fastforce
    apply (erule invs_distinct)
   apply simp
  apply (frule_tac p=ptr in cte_wp_valid_cap, fastforce)
  apply (clarsimp simp: cte_wp_at_def gen_obj_refs_Int)
  apply (rule conjI)
   apply (rule classical)
   apply (frule(1) zombies_finalD2[OF _ _ _ invs_zombies],
          simp?, clarsimp, assumption+)
   subgoal by (clarsimp simp: sameObjectAs_def3 isCap_simps valid_cap_def valid_arch_cap_def
                              valid_arch_cap_ref_def obj_at_def is_obj_defs a_type_def
                              final_matters'_def arch_final_matters'_def
                        split: cap.split_asm arch_cap.split_asm option.split_asm if_split_asm,
               simp_all add: is_cap_defs)
  apply (rule classical)
  by (clarsimp simp: cap_irqs_def cap_irq_opt_def sameObjectAs_def3 isCap_simps arch_gen_obj_refs_def
                 split: cap.split_asm)

lemma arch_recycleCap_improve_cases:
  "\<lbrakk>\<not> isPageCap cap; \<not> isPageTableCap cap; \<not> isPageDirectoryCap cap;\<not> isVCPUCap cap;
    \<not> isASIDControlCap cap; \<not>isSGISignalCap cap \<rbrakk> \<Longrightarrow>
   (if isASIDPoolCap cap then v else undefined) = v"
  by (cases cap, simp_all add: isCap_simps)

crunch invalidateTLBByASID
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

crunch dissociateVCPUTCB, unmapPageTable
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getVCPU_wp getObject_inv hoare_vcg_all_lift hoare_vcg_if_lift3
   simp: loadObject_default_def updateObject_default_def)

context notes if_cong[cong] begin

crunch Arch_finaliseCap
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_inv simp: loadObject_default_def updateObject_default_def
   rule: ARM_HYP_H.finaliseCap_def)

end

crunch vcpuFinalise, deletingIRQHandler, finaliseCap
  for sch_act_simple[wp]: sch_act_simple
  (simp: crunch_simps
   rule: sch_act_simple_lift
   wp: getObject_inv loadObject_default_inv crunch_wps)

lemma sym_refs_vcpu_tcb:
  "\<lbrakk> ko_at (ArchObj (VCPU vcpu)) v s; vcpu_tcb vcpu = Some t; sym_refs (state_hyp_refs_of s) \<rbrakk> \<Longrightarrow>
   \<exists>tcb. ko_at (TCB tcb) t s \<and> tcb_vcpu (tcb_arch tcb) = Some v"
  apply (drule (1) hyp_sym_refs_obj_atD)
  apply (clarsimp simp: obj_at_def hyp_refs_of_def)
  apply (rename_tac ko)
  apply (case_tac ko; simp add: tcb_vcpu_refs_def split: option.splits)
  apply (rename_tac koa)
  apply (case_tac koa; simp add: refs_of_a_def vcpu_tcb_refs_def split: option.splits)
  done

lemma vcpuFinalise_corres[corres]:
  "vcpu' = vcpu \<Longrightarrow>
   corres dc (invs and vcpu_at vcpu) no_0_obj' (vcpu_finalise vcpu) (vcpuFinalise vcpu')"
  apply (simp add: vcpuFinalise_def vcpu_finalise_def)
  apply (corres corres: getObject_vcpu_corres
                simp: vcpu_relation_def
                wp: get_vcpu_wp getVCPU_wp
         | corres_cases_both)+
   apply (fastforce simp: obj_at_def in_omonad dest: sym_refs_vcpu_tcb)
  apply (fastforce elim: vcpu_at_cross)
  done

lemma arch_finaliseCap_corres[Finalise_R_3_assms]:
  "\<lbrakk> final_matters' (ArchObjectCap cap') \<Longrightarrow> final = final'; acap_relation cap cap' \<rbrakk>
     \<Longrightarrow> corres (\<lambda>r r'. cap_relation (fst r) (fst r') \<and> cap_relation (snd r) (snd r'))
           (\<lambda>s. invs s \<and> s \<turnstile> cap.ArchObjectCap cap
                       \<and> (final_matters (cap.ArchObjectCap cap)
                            \<longrightarrow> final = is_final_cap' (cap.ArchObjectCap cap) s)
                       \<and> cte_wp_at ((=) (cap.ArchObjectCap cap)) sl s)
           (\<lambda>s. invs' s \<and> s \<turnstile>' ArchObjectCap cap' \<and>
                 (final_matters' (ArchObjectCap cap') \<longrightarrow>
                      final' = isFinal (ArchObjectCap cap') (cte_map sl) (cteCaps_of s)))
           (arch_finalise_cap cap final) (Arch.finaliseCap cap' final')"
  apply (cases cap,
         simp_all add: arch_finalise_cap_def ARM_HYP_H.finaliseCap_def isCap_simps
                       final_matters'_def arch_final_matters'_def case_bool_If liftM_def[symmetric]
                       o_def dc_def[symmetric]
                split: option.split, safe)
     apply (rule corres_guard_imp, rule deleteASIDPool_corres)
      apply (clarsimp simp: valid_cap_def mask_def)
     apply (clarsimp simp: valid_cap'_def)
     apply auto[1]
    apply (rule corres_guard_imp, rule unmapPage_corres)
      apply simp
     apply (clarsimp simp: valid_cap_def valid_unmap_def)
     apply (auto simp: vmsz_aligned_def pbfs_atleast_pageBits mask_def
                 elim: is_aligned_weaken)[2]
   apply (rule corres_guard_imp, rule unmapPageTable_corres)
    apply (auto simp: valid_cap_def valid_cap'_def mask_def
               elim!: is_aligned_weaken)[2]
  apply (rule corres_guard_imp, rule deleteASID_corres)
   apply (auto simp: mask_def valid_cap_def)[2]
  apply corresK
  apply (clarsimp simp: valid_cap_def valid_cap'_def)
  done

lemmas deleteCallerCap_typ_ats[wp] = typ_at_lifts[OF deleteCallerCap_typ_at']

end (* Arch *)

interpretation Finalise_R_3?: Finalise_R_3 arch_final_matters' arch_cap_has_cleanup'
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Finalise_R_3_assms)?)?)
qed

end
