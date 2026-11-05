(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Proof that calling the kernel never leaves threads orphaned: architecture-specific parts.
   More specifically, every active thread must be the current thread,
   or about to be switched to, or be in a scheduling queue. *)

theory ArchOrphanage
imports Orphanage
begin

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for Orphanage locale *)

crunch doMachineOp
  for tcb_in_cur_domain'[wp]: "tcb_in_cur_domain' t"
  (wp: no_orphans_lift tcb_in_cur_domain'_lift)

crunch Arch.switchToThread, Arch.switchToIdleThread
  for ksCurThread[Arch_assms, wp]: "\<lambda>s. P (ksCurThread s)"
  and all_queued_tcb_ptrs[Arch_assms, wp]: "\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)"
  and ksSchedulerAction[Arch_assms, wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and st_tcb_at'[Arch_assms, wp]: "\<lambda>s. P (st_tcb_at' P' p s)"
  (wp: crunch_wps getObject_inv loadObject_default_inv findVSpaceForASID_vs_at_wp
   simp: getThreadVSpaceRoot_def if_distribR
   cong: if_cong)

crunch Arch.switchToIdleThread
  for obj_at'_tcb[Arch_assms, wp]: "\<lambda>s. P (obj_at' (P' :: tcb \<Rightarrow> _) p s)"

crunch Arch.switchToThread
  for no_orphans[Arch_assms, wp]: "no_orphans"
  (wp: no_orphans_lift crunch_wps)

lemma setASID_all_queued_tcb_ptrs[wp]:
  "setObject ptr (ap::asidpool) \<lbrace>\<lambda>s. P (t \<in> all_queued_tcb_ptrs s)\<rbrace>"
  apply (simp add: all_queued_tcb_ptrs_def obj_at'_real_def)
  apply (wpsimp wp: setObject_ko_wp_at simp: objBits_simps)
    apply (simp add: pageBits_def)
   apply simp
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
  done

crunch prepareNextDomain
  for no_orphans[Arch_assms, wp]: no_orphans
  and tcbQueued[Arch_assms, wp]: "\<lambda>s. Q (obj_at' (\<lambda>tcb. P (tcbQueued tcb)) tcb_ptr s)"
  and st_tcb_at'[Arch_assms, wp]: "\<lambda>s. P (st_tcb_at' P' p s)"
  and ct'[Arch_assms, wp]: "\<lambda>s. P (ksCurThread s)"
  (wp:  crunch_wps simp: Let_def)

lemma createNewCaps_no_orphans_arch[Arch_assms]:
  "toAPIType tp = None \<Longrightarrow>
   \<lbrace> (\<lambda>s. no_orphans s
          \<and>  pspace_aligned' s \<and> pspace_distinct' s
          \<and>  pspace_no_overlap' ptr sz s
          \<and>  (tp = APIObjectType CapTableObject \<longrightarrow> us > 0))
     and K (range_cover ptr sz (APIType_capBits tp us) n \<and> 0 < n) \<rbrace>
   Arch_createNewCaps tp ptr n us d
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  supply if_split[split del]
  apply (cases tp; simp)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type; simp)
            apply (wpsimp wp: mapM_x_wp'
                   | clarsimp simp: projectKO_opt_tcb APIType_capBits_def Arch_createNewCaps_def
                   | simp add: objBits_simps mult_2 nat_arith.add1 bit_simps split: if_split)+
  done

crunch Arch.postCapDeletion
  for no_orphans[Arch_assms, wp]: no_orphans

lemma arch_createObject_no_orphans[Arch_assms]:
  "\<lbrace>pspace_no_overlap' ptr sz and pspace_aligned' and pspace_distinct'
    and K (range_cover ptr sz (APIType_capBits tp us) (Suc 0)) and no_orphans\<rbrace>
   Arch.createObject tp ptr us d
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding RISCV64_H.createObject_def
  apply (wpsimp wp: createObjects'_wp_subst createObjects_no_orphans[where sz=sz]
                simp: placeNewObject_def2 placeNewDataObject_def
                      is_active_thread_state_def makeObject_tcb projectKO_opt_tcb
                split_del: if_split)
  apply (clarsimp simp:  APIType_capBits_def objBits_simps bit_simps
                  split: object_type.split_asm if_splits)
  done

lemma deleteObjects_no_orphans[Arch_assms, wp]:
  "\<lbrace> (\<lambda>s. no_orphans s \<and> pspace_distinct' s) and K (is_aligned ptr bits) \<rbrace>
   deleteObjects ptr bits
   \<lbrace> \<lambda>_. no_orphans \<rbrace>"
  apply (rule hoare_gen_asm)
  apply (unfold deleteObjects_def2 doMachineOp_def split_def)
  apply wpsimp
  apply (clarsimp simp: no_orphans_def all_active_tcb_ptrs_def
                        all_queued_tcb_ptrs_def is_active_tcb_ptr_def
                        ksMachineState_ksPSpace_upd_comm
                   cong: if_cong)
  apply (drule_tac x=tcb_ptr in spec)
  apply (clarsimp simp: pred_tcb_at'_def obj_at_delete')
  done

crunch doMachineOp
  for not_pred_tcb_at'[wp]: "\<lambda>s. \<not> (pred_tcb_at' proj P' t) s"

lemma handleReservedIRQ_no_orphans[Arch_assms, wp]:
  "\<lbrace>\<lambda>s. no_orphans s \<and> valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s\<rbrace>
   handleReservedIRQ irq
   \<lbrace>\<lambda>_. no_orphans \<rbrace>"
  unfolding handleReservedIRQ_def
  by wpsimp

crunch maskIrqSignal
  for no_orphans[Arch_assms, wp]: no_orphans

lemma deleteASIDPool_no_orphans [wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<rbrace>
   deleteASIDPool asid pool
   \<lbrace> \<lambda>rv s. no_orphans s \<rbrace>"
  unfolding deleteASIDPool_def
  apply (wp | clarsimp)+
     apply (rule_tac Q'="\<lambda>rv s. no_orphans s" in hoare_post_imp)
      apply (clarsimp simp: no_orphans_def all_queued_tcb_ptrs_def
                            all_active_tcb_ptrs_def is_active_tcb_ptr_def)
     apply (wp mapM_wp_inv getObject_inv loadObject_default_inv | clarsimp)+
  done

lemma storePTE_no_orphans [wp]:
  "storePTE ptr val \<lbrace> no_orphans \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)

lemma archThreadSet_tcbQueued_inv[wp]:
  "archThreadSet f t \<lbrace>\<lambda>s. obj_at' (\<lambda>tcb. P (tcbQueued tcb)) tcb_ptr s\<rbrace>"
  unfolding archThreadSet_def
  by (wp setObject_tcb_strongest getObject_tcb_wp) (fastforce simp: obj_at'_def)

crunch modifyArchState, archThreadSet
  for no_orphans[wp]: "no_orphans"
  (wp: no_orphans_lift crunch_wps)

crunch postSetFlags, prepareSetDomain, handleSpuriousIRQ, unmapPage
  for no_orphans[Arch_assms, wp]: no_orphans

crunch unmapPageTable, prepareThreadDelete
  for no_orphans[Arch_assms, wp]: "no_orphans"
  (wp: lookupPTSlotFromLevel_inv)

lemma setASIDPool_no_orphans [wp]:
  "setObject p (ap :: asidpool) \<lbrace> no_orphans \<rbrace>"
  unfolding no_orphans_disj all_queued_tcb_ptrs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)

crunch deleteASID, Arch.finaliseCap
  for no_orphans[Arch_assms, wp]: "no_orphans"
  (wp: getObject_inv loadObject_default_inv)

lemma no_orphans_arch_finalise_prop_stuff[Arch_assms]:
  "arch_finalise_prop_stuff no_orphans"
  by (simp add: arch_finalise_prop_stuff_def)

crunch performIRQControl, InterruptDecls_H.invokeIRQHandler, performPageTableInvocation,
       performPageInvocation, handleVMFault, copyGlobalMappings
  for no_orphans[Arch_assms, wp]: no_orphans
  (wp: crunch_wps simp: crunch_simps)

lemma handleHypervisorFault_no_orphans[Arch_assms, wp]:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s \<and> no_orphans s\<rbrace>
   handleHypervisorFault w f
   \<lbrace>\<lambda>_. no_orphans\<rbrace>"
  unfolding handleHypervisorFault_def
  by (wpsimp wp: undefined_valid)

crunch performASIDPoolInvocation
  for no_orphans[wp]: no_orphans
  (wp: getObject_inv loadObject_default_inv)

lemma performASIDControlInvocation_no_orphans [wp]:
  notes [simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                     Int_atLeastAtMost  usableUntypedRange.simps
  shows "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_aci' aci s \<and> ct_active' s \<rbrace>
   performASIDControlInvocation aci
   \<lbrace> \<lambda>reply s. no_orphans s \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:valid_aci'_def cte_wp_at_ctes_of
    split:asidcontrol_invocation.splits)
  apply (rename_tac s ptr_base p cref ptr null_cte ut_cte idx)
  proof -
  fix s ptr_base p cref ptr null_cte ut_cte idx
  assume no_orphans: "no_orphans s"
    and  invs'     : "invs' s"
    and  cte       : "ctes_of s p = Some null_cte" "cteCap null_cte = capability.NullCap"
                     "ctes_of s cref = Some ut_cte" "cteCap ut_cte = capability.UntypedCap False ptr_base pageBits idx"
    and  desc      : "descendants_of' cref (ctes_of s) = {}"
    and  misc      : "p \<noteq> cref" "ex_cte_cap_wp_to' (\<lambda>_. True) p s" "sch_act_simple s" "is_aligned ptr asid_low_bits"
                     "asid_wf ptr" "ct_active' s"

  have vc:"s \<turnstile>' UntypedCap False ptr_base pageBits idx"
    using cte misc invs'
    apply -
    apply (case_tac ut_cte)
    apply (rule ctes_of_valid_cap')
     apply simp
    apply fastforce
    done

   hence cover:
    "range_cover ptr_base pageBits pageBits (Suc 0)"
    apply -
    apply (rule range_cover_full)
     apply (simp add:valid_cap'_def capAligned_def)
    apply simp
    done

  have exclude: "cref \<notin> mask_range ptr_base pageBits"
    apply (rule descendants_range_ex_cte'[where cte = "ut_cte"])
        apply (rule empty_descendants_range_in'[OF desc])
       apply (rule if_unsafe_then_capD'[where P = "\<lambda>c. c = ut_cte"])
         apply (clarsimp simp: cte_wp_at_ctes_of cte)
        apply (simp add:invs' invs_unsafe_then_cap')
     apply (simp add:cte invs' add_mask_fold)+
    done

  show "\<lbrace>(=) s\<rbrace>performASIDControlInvocation (asidcontrol_invocation.MakePool ptr_base p cref ptr)
       \<lbrace>\<lambda>reply. no_orphans\<rbrace>"
  apply (clarsimp simp: performASIDControlInvocation_def
                  split: asidcontrol_invocation.splits)
  apply (wp hoare_weak_lift_imp | clarsimp)+
    apply (rule_tac Q'="\<lambda>rv s. no_orphans s" in hoare_post_imp)
     apply (clarsimp simp: no_orphans_def all_active_tcb_ptrs_def
                           is_active_tcb_ptr_def all_queued_tcb_ptrs_def)
    apply (wp | clarsimp simp:placeNewObject_def2)+
     apply (wp createObjects'_wp_subst)+
     apply (wp hoare_weak_lift_imp updateFreeIndex_pspace_no_overlap'[where sz= pageBits] getSlotCap_wp | simp)+
  apply (strengthen invs_pspace_aligned' invs_pspace_distinct' invs_valid_pspace')
  apply (clarsimp simp:conj_comms)
     apply (wp deleteObjects_invs'[where idx = idx and d=False]
       hoare_vcg_ex_lift deleteObjects_cte_wp_at'[where idx = idx and d=False] hoare_vcg_const_imp_lift )
  using invs' misc cte exclude no_orphans cover
  apply (clarsimp simp: is_active_thread_state_def makeObject_tcb valid_aci'_def
                        cte_wp_at_ctes_of invs_pspace_aligned' invs_pspace_distinct'
                        projectKO_opt_tcb isRunning_def isRestart_def conj_comms
                        invs_valid_pspace' vc objBits_simps range_cover.aligned)
  apply (intro conjI)
    apply (rule vc)
   apply (simp add:descendants_range'_def2)
   apply (rule empty_descendants_range_in'[OF desc])
  apply clarsimp
  done
qed

lemma arch_performInvocation_no_orphans[Arch_assms, wp]:
  "\<lbrace> \<lambda>s. no_orphans s \<and> invs' s \<and> valid_arch_inv' i s \<and> ct_active' s \<rbrace>
   Arch.performInvocation i
   \<lbrace> \<lambda>_. no_orphans \<rbrace>"
  unfolding RISCV64_H.performInvocation_def performRISCVMMUInvocation_def
  by (wpsimp simp: valid_arch_inv'_def)

crunch prepareSetDomain
  for cur_tcb'[Arch_assms, wp]: cur_tcb'
  (wp: cur_tcb_lift)

lemmas [Arch_assms] = st_tcb_at'_all_active_tcb_ptrs_lift[OF Arch_switchToThread_st_tcb_at']

lemmas Orphanage_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

interpretation Orphanage?: Orphanage
proof goal_cases
  case 1 show ?case by (intro_locales; (unfold_locales; (fact RISCV64.Orphanage_assms)?)?)
qed

end
