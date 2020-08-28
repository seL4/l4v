(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Finalise_R
imports
  IpcCancel_R
  InterruptAcc_R
  Retype_R
begin
context begin interpretation Arch . (*FIXME: arch_split*)

declare doUnbindNotification_def[simp]

text \<open>Properties about empty_slot/emptySlot\<close>

lemma case_Null_If:
  "(case c of NullCap \<Rightarrow> a | _ \<Rightarrow> b) = (if c = NullCap then a else b)"
  by (case_tac c, simp_all)

crunch aligned'[wp]: emptySlot pspace_aligned' (simp: case_Null_If)
crunch distinct'[wp]: emptySlot pspace_distinct' (simp: case_Null_If)

lemma updateCap_cte_wp_at_cases:
  "\<lbrace>\<lambda>s. (ptr = ptr' \<longrightarrow> cte_wp_at' (P \<circ> cteCap_update (K cap)) ptr' s) \<and> (ptr \<noteq> ptr' \<longrightarrow> cte_wp_at' P ptr' s)\<rbrace>
     updateCap ptr cap
   \<lbrace>\<lambda>rv. cte_wp_at' P ptr'\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (drule updateCap_stuff)
  apply (clarsimp simp: cte_wp_at_ctes_of modify_map_def)
  done

crunches postCapDeletion, updateTrackedFreeIndex
  for cte_wp_at'[wp]: "cte_wp_at' P p"

lemma updateFreeIndex_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_at' p s \<and> P (cte_wp_at' (if p = p' then P'
      o (cteCap_update (capFreeIndex_update (K idx))) else P') p' s)\<rbrace>
    updateFreeIndex p idx
  \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p' s)\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def
        split del: if_split)
  apply (rule hoare_pre)
   apply (wp updateCap_cte_wp_at' getSlotCap_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (cases "p' = p", simp_all)
  apply (case_tac cte, simp)
  done

lemma emptySlot_cte_wp_cap_other:
  "\<lbrace>(\<lambda>s. cte_wp_at' (\<lambda>c. P (cteCap c)) p s) and K (p \<noteq> p')\<rbrace>
  emptySlot p' opt
  \<lbrace>\<lambda>rv s. cte_wp_at' (\<lambda>c. P (cteCap c)) p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: emptySlot_def clearUntypedFreeIndex_def getSlotCap_def)
  apply (rule hoare_pre)
   apply (wp updateMDB_weak_cte_wp_at updateCap_cte_wp_at_cases
             updateFreeIndex_cte_wp_at getCTE_wp' hoare_vcg_all_lift
              | simp add:  | wpc
              | wp (once) hoare_drop_imps)+
  done

lemmas clearUntypedFreeIndex_typ_ats[wp]
    = typ_at_lifts[OF clearUntypedFreeIndex_typ_at']

crunch tcb_at'[wp]: postCapDeletion "tcb_at' t"
crunch ct[wp]: emptySlot "\<lambda>s. P (ksCurThread s)"
crunch cur_tcb'[wp]: clearUntypedFreeIndex "cur_tcb'"
  (wp: cur_tcb_lift)

crunch ksRQ[wp]: emptySlot "\<lambda>s. P (ksReadyQueues s)"
crunch ksRLQ[wp]: emptySlot "\<lambda>s. P (ksReleaseQueue s)"
crunch ksRQL1[wp]: emptySlot "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
crunch ksRQL2[wp]: emptySlot "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
crunch obj_at'[wp]: postCapDeletion "\<lambda>s. Q (obj_at' P p s)"

lemmas postCapDeletion_valid_queues[wp] =
    valid_queues_lift [OF postCapDeletion_obj_at'
                          postCapDeletion_pred_tcb_at'
                          postCapDeletion_ksRQ]

crunch inQ[wp]: clearUntypedFreeIndex "\<lambda>s. P (obj_at' (inQ d p) t s)"
crunch tcbInReleaseQueue[wp]: clearUntypedFreeIndex "\<lambda>s. P (obj_at' (tcbInReleaseQueue) t s)"
crunch tcbDomain[wp]: clearUntypedFreeIndex "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
crunch tcbPriority[wp]: clearUntypedFreeIndex "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t"

lemma emptySlot_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> emptySlot sl opt \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  unfolding emptySlot_def
  by (wp | wpcw | wp valid_queues_lift | simp)+

lemma emptySlot_valid_release_queue [wp]:
  "emptySlot sl opt \<lbrace>Invariants_H.valid_release_queue\<rbrace>"
  unfolding emptySlot_def
  by (wp | wpcw | wp valid_release_queue_lift | simp)+

lemma emptySlot_valid_release_queue' [wp]:
  "emptySlot sl opt \<lbrace>Invariants_H.valid_release_queue'\<rbrace>"
  unfolding emptySlot_def
  by (wp | wpcw | wp valid_release_queue'_lift | simp)+

crunch nosch[wp]: emptySlot "\<lambda>s. P (ksSchedulerAction s)"
crunch ksCurDomain[wp]: emptySlot "\<lambda>s. P (ksCurDomain s)"

lemma emptySlot_sch_act_wf [wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  emptySlot sl opt
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: emptySlot_def case_Null_If)
  apply (wp sch_act_wf_lift tcb_in_cur_domain'_lift | wpcw | simp)+
  done

lemma updateCap_valid_objs' [wp]:
  "\<lbrace>valid_objs' and valid_cap' cap\<rbrace>
  updateCap ptr cap \<lbrace>\<lambda>r. valid_objs'\<rbrace>"
  unfolding updateCap_def
  by (wp setCTE_valid_objs getCTE_wp) (clarsimp dest!: cte_at_cte_wp_atD)

lemma updateFreeIndex_valid_objs' [wp]:
  "\<lbrace>valid_objs'\<rbrace> clearUntypedFreeIndex ptr \<lbrace>\<lambda>r. valid_objs'\<rbrace>"
  apply (simp add: clearUntypedFreeIndex_def getSlotCap_def)
  apply (wp getCTE_wp' | wpc | simp add: updateTrackedFreeIndex_def)+
  done

crunches clearUntypedFreeIndex, updateMDB
  for sc_at'_n[wp]: "sc_at'_n n p"
  (simp: crunch_simps wp: crunch_wps)

crunch valid_objs'[wp]: emptySlot "valid_objs'"

crunch state_refs_of'[wp]: setInterruptState "\<lambda>s. P (state_refs_of' s)"
  (simp: state_refs_of'_pspaceI)
crunch state_refs_of'[wp]: emptySlot "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps)

lemma mdb_chunked2D:
  "\<lbrakk> mdb_chunked m; m \<turnstile> p \<leadsto> p'; m \<turnstile> p' \<leadsto> p'';
     m p = Some (CTE cap nd); m p'' = Some (CTE cap'' nd'');
     sameRegionAs cap cap''; p \<noteq> p'' \<rbrakk>
     \<Longrightarrow> \<exists>cap' nd'. m p' = Some (CTE cap' nd') \<and> sameRegionAs cap cap'"
  apply (subgoal_tac "\<exists>cap' nd'. m p' = Some (CTE cap' nd')")
   apply (clarsimp simp add: mdb_chunked_def)
   apply (drule spec[where x=p])
   apply (drule spec[where x=p''])
   apply clarsimp
   apply (drule mp, erule trancl_into_trancl2)
    apply (erule trancl.intros(1))
   apply (simp add: is_chunk_def)
   apply (drule spec, drule mp, erule trancl.intros(1))
   apply (drule mp, rule trancl_into_rtrancl)
    apply (erule trancl.intros(1))
   apply clarsimp
  apply (clarsimp simp: mdb_next_unfold)
  apply (case_tac z, simp)
  done

lemma nullPointer_eq_0_simp[simp]:
  "(0 = nullPointer) = True"
  by (simp add: nullPointer_def)

lemma no_0_no_0_lhs_trancl [simp]:
  "no_0 m \<Longrightarrow> \<not> m \<turnstile> 0 \<leadsto>\<^sup>+ x"
  by (rule, drule tranclD, clarsimp simp: next_unfold')

lemma no_0_no_0_lhs_rtrancl [simp]:
  "\<lbrakk> no_0 m; x \<noteq> 0 \<rbrakk> \<Longrightarrow> \<not> m \<turnstile> 0 \<leadsto>\<^sup>* x"
  by (clarsimp dest!: rtranclD)

end
locale mdb_empty =
  mdb_ptr?: mdb_ptr m _ _ slot s_cap s_node
    for m slot s_cap s_node +

  fixes n
  defines "n \<equiv>
           modify_map
             (modify_map
               (modify_map
                 (modify_map m (mdbPrev s_node)
                   (cteMDBNode_update (mdbNext_update (%_. (mdbNext s_node)))))
                 (mdbNext s_node)
                 (cteMDBNode_update
                   (\<lambda>mdb. mdbFirstBadged_update (%_. (mdbFirstBadged mdb \<or> mdbFirstBadged s_node))
                           (mdbPrev_update (%_. (mdbPrev s_node)) mdb))))
               slot (cteCap_update (%_. capability.NullCap)))
              slot (cteMDBNode_update (const nullMDBNode))"
begin
interpretation Arch . (*FIXME: arch_split*)

lemmas m_slot_prev = m_p_prev
lemmas m_slot_next = m_p_next
lemmas prev_slot_next = prev_p_next
lemmas next_slot_prev = next_p_prev

lemma n_revokable:
  "n p = Some (CTE cap node) \<Longrightarrow>
  (\<exists>cap' node'. m p = Some (CTE cap' node') \<and>
              (if p = slot
               then \<not> mdbRevocable node
               else mdbRevocable node = mdbRevocable node'))"
  by (auto simp add: n_def modify_map_if nullMDBNode_def split: if_split_asm)

lemma m_revokable:
  "m p = Some (CTE cap node) \<Longrightarrow>
  (\<exists>cap' node'. n p = Some (CTE cap' node') \<and>
              (if p = slot
               then \<not> mdbRevocable node'
               else mdbRevocable node' = mdbRevocable node))"
  apply (clarsimp simp add: n_def modify_map_if nullMDBNode_def split: if_split_asm)
  apply (cases "p=slot", simp)
  apply (cases "p=mdbNext s_node", simp)
   apply (cases "p=mdbPrev s_node", simp)
   apply clarsimp
  apply simp
  apply (cases "p=mdbPrev s_node", simp)
  apply simp
  done

lemma no_0_n:
  "no_0 n"
  using no_0 by (simp add: n_def)

lemma n_next:
  "n p = Some (CTE cap node) \<Longrightarrow>
  (\<exists>cap' node'. m p = Some (CTE cap' node') \<and>
              (if p = slot
               then mdbNext node = 0
               else if p = mdbPrev s_node
               then mdbNext node = mdbNext s_node
               else mdbNext node = mdbNext node'))"
  apply (subgoal_tac "p \<noteq> 0")
   prefer 2
   apply (insert no_0_n)[1]
   apply clarsimp
  apply (cases "p = slot")
   apply (clarsimp simp: n_def modify_map_if initMDBNode_def split: if_split_asm)
  apply (cases "p = mdbPrev s_node")
   apply (auto simp: n_def modify_map_if initMDBNode_def split: if_split_asm)
  done

lemma n_prev:
  "n p = Some (CTE cap node) \<Longrightarrow>
  (\<exists>cap' node'. m p = Some (CTE cap' node') \<and>
              (if p = slot
               then mdbPrev node = 0
               else if p = mdbNext s_node
               then mdbPrev node = mdbPrev s_node
               else mdbPrev node = mdbPrev node'))"
  apply (subgoal_tac "p \<noteq> 0")
   prefer 2
   apply (insert no_0_n)[1]
   apply clarsimp
  apply (cases "p = slot")
   apply (clarsimp simp: n_def modify_map_if initMDBNode_def split: if_split_asm)
  apply (cases "p = mdbNext s_node")
   apply (auto simp: n_def modify_map_if initMDBNode_def split: if_split_asm)
  done

lemma n_cap:
  "n p = Some (CTE cap node) \<Longrightarrow>
  \<exists>cap' node'. m p = Some (CTE cap' node') \<and>
              (if p = slot
               then cap = NullCap
               else cap' = cap)"
  apply (clarsimp simp: n_def modify_map_if initMDBNode_def split: if_split_asm)
   apply (cases node)
   apply auto
  done

lemma m_cap:
  "m p = Some (CTE cap node) \<Longrightarrow>
  \<exists>cap' node'. n p = Some (CTE cap' node') \<and>
              (if p = slot
               then cap' = NullCap
               else cap' = cap)"
  apply (clarsimp simp: n_def modify_map_cases initMDBNode_def)
  apply (cases node)
  apply clarsimp
  apply (cases "p=slot", simp)
  apply clarsimp
  apply (cases "mdbNext s_node = p", simp)
   apply fastforce
  apply simp
  apply (cases "mdbPrev s_node = p", simp)
  apply fastforce
  done

lemma n_badged:
  "n p = Some (CTE cap node) \<Longrightarrow>
  \<exists>cap' node'. m p = Some (CTE cap' node') \<and>
              (if p = slot
               then \<not> mdbFirstBadged node
               else if p = mdbNext s_node
               then mdbFirstBadged node = (mdbFirstBadged node' \<or> mdbFirstBadged s_node)
               else mdbFirstBadged node = mdbFirstBadged node')"
  apply (subgoal_tac "p \<noteq> 0")
   prefer 2
   apply (insert no_0_n)[1]
   apply clarsimp
  apply (cases "p = slot")
   apply (clarsimp simp: n_def modify_map_if initMDBNode_def split: if_split_asm)
  apply (cases "p = mdbNext s_node")
   apply (auto simp: n_def modify_map_if nullMDBNode_def split: if_split_asm)
  done

lemma m_badged:
  "m p = Some (CTE cap node) \<Longrightarrow>
  \<exists>cap' node'. n p = Some (CTE cap' node') \<and>
              (if p = slot
               then \<not> mdbFirstBadged node'
               else if p = mdbNext s_node
               then mdbFirstBadged node' = (mdbFirstBadged node \<or> mdbFirstBadged s_node)
               else mdbFirstBadged node' = mdbFirstBadged node)"
  apply (subgoal_tac "p \<noteq> 0")
   prefer 2
   apply (insert no_0_n)[1]
   apply clarsimp
  apply (cases "p = slot")
   apply (clarsimp simp: n_def modify_map_if nullMDBNode_def split: if_split_asm)
  apply (cases "p = mdbNext s_node")
   apply (clarsimp simp: n_def modify_map_if nullMDBNode_def split: if_split_asm)
  apply clarsimp
  apply (cases "p = mdbPrev s_node")
   apply (auto simp: n_def modify_map_if initMDBNode_def  split: if_split_asm)
  done

lemmas slot = m_p

lemma m_next:
  "m p = Some (CTE cap node) \<Longrightarrow>
  \<exists>cap' node'. n p = Some (CTE cap' node') \<and>
              (if p = slot
               then mdbNext node' = 0
               else if p = mdbPrev s_node
               then mdbNext node' = mdbNext s_node
               else mdbNext node' = mdbNext node)"
  apply (subgoal_tac "p \<noteq> 0")
   prefer 2
   apply clarsimp
  apply (cases "p = slot")
   apply (clarsimp simp: n_def modify_map_if)
  apply (cases "p = mdbPrev s_node")
   apply (simp add: n_def modify_map_if)
  apply simp
  apply (simp add: n_def modify_map_if)
  apply (cases "mdbNext s_node = p")
   apply fastforce
  apply fastforce
  done

lemma m_prev:
  "m p = Some (CTE cap node) \<Longrightarrow>
  \<exists>cap' node'. n p = Some (CTE cap' node') \<and>
              (if p = slot
               then mdbPrev node' = 0
               else if p = mdbNext s_node
               then mdbPrev node' = mdbPrev s_node
               else mdbPrev node' = mdbPrev node)"
  apply (subgoal_tac "p \<noteq> 0")
   prefer 2
   apply clarsimp
  apply (cases "p = slot")
   apply (clarsimp simp: n_def modify_map_if)
  apply (cases "p = mdbPrev s_node")
   apply (simp add: n_def modify_map_if)
  apply simp
  apply (simp add: n_def modify_map_if)
  apply (cases "mdbNext s_node = p")
   apply fastforce
  apply fastforce
  done

lemma n_nextD:
  "n \<turnstile> p \<leadsto> p' \<Longrightarrow>
  if p = slot then p' = 0
  else if p = mdbPrev s_node
  then m \<turnstile> p \<leadsto> slot \<and> p' = mdbNext s_node
  else m \<turnstile> p \<leadsto> p'"
  apply (clarsimp simp: mdb_next_unfold split del: if_split cong: if_cong)
  apply (case_tac z)
  apply (clarsimp split del: if_split)
  apply (drule n_next)
  apply (elim exE conjE)
  apply (simp split: if_split_asm)
  apply (frule dlist_prevD [OF m_slot_prev])
  apply (clarsimp simp: mdb_next_unfold)
  done

lemma n_next_eq:
  "n \<turnstile> p \<leadsto> p' =
  (if p = slot then p' = 0
  else if p = mdbPrev s_node
  then m \<turnstile> p \<leadsto> slot \<and> p' = mdbNext s_node
  else m \<turnstile> p \<leadsto> p')"
  apply (rule iffI)
   apply (erule n_nextD)
  apply (clarsimp simp: mdb_next_unfold split: if_split_asm)
    apply (simp add: n_def modify_map_if slot)
   apply hypsubst_thin
   apply (case_tac z)
   apply simp
   apply (drule m_next)
   apply clarsimp
  apply (case_tac z)
  apply simp
  apply (drule m_next)
  apply clarsimp
  done

lemma n_prev_eq:
  "n \<turnstile> p \<leftarrow> p' =
  (if p' = slot then p = 0
  else if p' = mdbNext s_node
  then m \<turnstile> slot \<leftarrow> p' \<and> p = mdbPrev s_node
  else m \<turnstile> p \<leftarrow> p')"
  apply (rule iffI)
   apply (clarsimp simp: mdb_prev_def split del: if_split cong: if_cong)
   apply (case_tac z)
   apply (clarsimp split del: if_split)
   apply (drule n_prev)
   apply (elim exE conjE)
   apply (simp split: if_split_asm)
   apply (frule dlist_nextD [OF m_slot_next])
   apply (clarsimp simp: mdb_prev_def)
  apply (clarsimp simp: mdb_prev_def split: if_split_asm)
    apply (simp add: n_def modify_map_if slot)
   apply hypsubst_thin
   apply (case_tac z)
   apply clarsimp
   apply (drule m_prev)
   apply clarsimp
  apply (case_tac z)
  apply simp
  apply (drule m_prev)
  apply clarsimp
  done

lemma valid_dlist_n:
  "valid_dlist n" using dlist
  apply (clarsimp simp: valid_dlist_def2 [OF no_0_n])
  apply (simp add: n_next_eq n_prev_eq m_slot_next m_slot_prev cong: if_cong)
  apply (rule conjI, clarsimp)
   apply (rule conjI, clarsimp simp: next_slot_prev prev_slot_next)
   apply (fastforce dest!: dlist_prev_src_unique)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (clarsimp simp: valid_dlist_def2 [OF no_0])
   apply (case_tac "mdbNext s_node = 0")
    apply simp
    apply (subgoal_tac "m \<turnstile> slot \<leadsto> c'")
     prefer 2
     apply fastforce
    apply (clarsimp simp: mdb_next_unfold slot)
   apply (frule next_slot_prev)
   apply (drule (1) dlist_prev_src_unique, simp)
   apply simp
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (fastforce dest: dlist_next_src_unique)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (clarsimp simp: valid_dlist_def2 [OF no_0])
   apply (clarsimp simp: mdb_prev_def slot)
  apply (clarsimp simp: valid_dlist_def2 [OF no_0])
  done

lemma caps_contained_n:
  "caps_contained' n"
  using valid
  apply (clarsimp simp: valid_mdb_ctes_def caps_contained'_def)
  apply (drule n_cap)+
  apply (clarsimp split: if_split_asm)
  apply (erule disjE, clarsimp)
  apply clarsimp
  apply fastforce
  done

lemma chunked:
  "mdb_chunked m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma valid_badges:
  "valid_badges m"
  using valid ..

lemma valid_badges_n:
  "valid_badges n"
proof -
  from valid_badges
  show ?thesis
    apply (simp add: valid_badges_def2)
    apply clarsimp
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
        apply (fastforce simp:isCap_simps capMasterCap_def split:capability.splits)
       apply clarsimp
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

lemma to_slot_eq [simp]:
  "m \<turnstile> p \<leadsto> slot = (p = mdbPrev s_node \<and> p \<noteq> 0)"
  apply (rule iffI)
   apply (frule dlist_nextD0, simp)
   apply (clarsimp simp: mdb_prev_def slot mdb_next_unfold)
  apply (clarsimp intro!: prev_slot_next)
  done

lemma n_parent_of:
  "\<lbrakk> n \<turnstile> p parentOf p'; p \<noteq> slot; p' \<noteq> slot \<rbrakk> \<Longrightarrow> m \<turnstile> p parentOf p'"
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
  apply (clarsimp split: if_split_asm;
         clarsimp simp: isMDBParentOf_def isCap_simps split: if_split_asm cong: if_cong)
  done

lemma m_parent_of:
  "\<lbrakk> m \<turnstile> p parentOf p'; p \<noteq> slot; p' \<noteq> slot; p\<noteq>p'; p'\<noteq>mdbNext s_node \<rbrakk> \<Longrightarrow> n \<turnstile> p parentOf p'"
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
  apply (simp split: if_split_asm;
         clarsimp simp: isMDBParentOf_def isCap_simps split: if_split_asm cong: if_cong)
  done

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
  apply (clarsimp simp: isMDBParentOf_def isCap_simps split: if_split_asm cong: if_cong)
  done

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
    apply (rule subtree.trans_parent[OF _ m_slot_next], simp_all)
    apply (rule subtree.direct_parent)
      apply (erule prev_slot_next)
     apply simp
    apply (clarsimp simp: parentOf_def slot)
    apply (case_tac cte'a)
    apply (case_tac ctea)
    apply clarsimp
    apply (frule(2) mdb_chunked2D [OF chunked prev_slot_next m_slot_next])
      apply (clarsimp simp: isMDBParentOf_CTE)
     apply simp
    apply (simp add: slot)
    apply (clarsimp simp add: isMDBParentOf_CTE)
    apply (insert valid_badges)
    apply (simp add: valid_badges_def2)
    apply (drule spec[where x=slot])
    apply (drule spec[where x="mdbNext s_node"])
    apply (simp add: slot m_slot_next)
    apply (insert valid_badges)
    apply (simp add: valid_badges_def2)
    apply (drule spec[where x="mdbPrev s_node"])
    apply (drule spec[where x=slot])
    apply (simp add: slot prev_slot_next)
    apply (case_tac cte, case_tac cte')
    apply (rename_tac cap'' node'')
    apply (clarsimp simp: isMDBParentOf_CTE)
    apply (frule n_cap, drule n_badged)
    apply (frule n_cap, drule n_badged)
    apply clarsimp
    apply (case_tac cap'', simp_all add: isCap_simps)[1]
     apply (clarsimp simp: sameRegionAs_def3 isCap_simps)
    apply (clarsimp simp: sameRegionAs_def3 isCap_simps)
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
       apply (subgoal_tac "sameRegionAs cap s_cap")
        prefer 2
        apply (insert chunked)[1]
        apply (simp add: mdb_chunked_def)
        apply (erule_tac x="p" in allE)
        apply (erule_tac x="mdbNext s_node" in allE)
        apply simp
        apply (drule isMDBParent_sameRegion)+
        apply clarsimp
        apply (subgoal_tac "m \<turnstile> p \<leadsto>\<^sup>+ slot")
         prefer 2
         apply (rule trancl_trans)
          apply (erule subtree_mdb_next)
         apply (rule r_into_trancl)
         apply (rule prev_slot_next)
         apply clarsimp
        apply (subgoal_tac "m \<turnstile> p \<leadsto>\<^sup>+ mdbNext s_node")
         prefer 2
         apply (erule trancl_trans)
         apply fastforce
        apply simp
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
       apply (insert valid_badges, simp add: valid_badges_def2)
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
      apply (rule m_slot_next)
     apply simp
    apply (erule n_parent_of, simp, simp)
    done
qed

lemma parency_m:
  assumes "m \<turnstile> p \<rightarrow> p'"
  shows "p \<noteq> slot \<longrightarrow> (if p' \<noteq> slot then n \<turnstile> p \<rightarrow> p' else m \<turnstile> p \<rightarrow> mdbNext s_node \<longrightarrow> n \<turnstile> p \<rightarrow> mdbNext s_node)"
using assms
proof induct
  case (direct_parent c)
  thus ?case
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (rule subtree.direct_parent)
       apply (simp add: n_next_eq)
       apply clarsimp
       apply (subgoal_tac "mdbPrev s_node \<noteq> 0")
        prefer 2
        apply (clarsimp simp: mdb_next_unfold)
       apply (drule prev_slot_next)
       apply (clarsimp simp: mdb_next_unfold)
      apply assumption
     apply (erule m_parent_of, simp, simp)
      apply clarsimp
     apply clarsimp
     apply (drule dlist_next_src_unique)
       apply fastforce
      apply clarsimp
     apply simp
    apply clarsimp
    apply (rule subtree.direct_parent)
      apply (simp add: n_next_eq)
     apply (drule subtree_parent)
     apply (clarsimp simp: parentOf_def)
    apply (drule subtree_parent)
    apply (erule (1) m_parent_of_next)
     apply clarsimp
    apply clarsimp
    done
next
  case (trans_parent c c')
  thus ?case
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (cases "c=slot")
      apply simp
      apply (erule impE)
       apply (erule subtree.trans_parent)
         apply fastforce
        apply (clarsimp simp: slot mdb_next_unfold)
       apply (clarsimp simp: slot mdb_next_unfold)
      apply (clarsimp simp: slot mdb_next_unfold)
     apply clarsimp
     apply (erule subtree.trans_parent)
       apply (simp add: n_next_eq)
       apply clarsimp
       apply (subgoal_tac "mdbPrev s_node \<noteq> 0")
        prefer 2
        apply (clarsimp simp: mdb_next_unfold)
       apply (drule prev_slot_next)
       apply (clarsimp simp: mdb_next_unfold)
      apply assumption
     apply (erule m_parent_of, simp, simp)
      apply clarsimp
      apply (drule subtree_mdb_next)
      apply (drule trancl_trans)
       apply (erule r_into_trancl)
      apply simp
     apply clarsimp
     apply (drule dlist_next_src_unique)
       apply fastforce
      apply clarsimp
     apply simp
    apply clarsimp
    apply (erule subtree.trans_parent)
      apply (simp add: n_next_eq)
     apply clarsimp
    apply (rule m_parent_of_next, erule subtree_parent, assumption, assumption)
    apply clarsimp
    done
qed

lemma parency:
  "n \<turnstile> p \<rightarrow> p' = (p \<noteq> slot \<and> p' \<noteq> slot \<and> m \<turnstile> p \<rightarrow> p')"
  by (auto dest!: parency_n parency_m)

lemma descendants:
  "descendants_of' p n =
  (if p = slot then {} else descendants_of' p m - {slot})"
  by (auto simp add: parency descendants_of'_def)

lemma n_tranclD:
  "n \<turnstile> p \<leadsto>\<^sup>+ p' \<Longrightarrow> m \<turnstile> p \<leadsto>\<^sup>+ p' \<and> p' \<noteq> slot"
  apply (erule trancl_induct)
   apply (clarsimp simp add: n_next_eq split: if_split_asm)
     apply (rule mdb_chain_0D)
      apply (rule chain)
     apply (clarsimp simp: slot)
    apply (blast intro: trancl_trans prev_slot_next)
   apply fastforce
  apply (clarsimp simp: n_next_eq split: if_split_asm)
   apply (erule trancl_trans)
   apply (blast intro: trancl_trans prev_slot_next)
  apply (fastforce intro: trancl_trans)
  done

lemma m_tranclD:
  "m \<turnstile> p \<leadsto>\<^sup>+ p' \<Longrightarrow>
  if p = slot then n \<turnstile> mdbNext s_node \<leadsto>\<^sup>* p'
  else if p' = slot then n \<turnstile> p \<leadsto>\<^sup>+ mdbNext s_node
  else n \<turnstile> p \<leadsto>\<^sup>+ p'"
  using no_0_n
  apply -
  apply (erule trancl_induct)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (rule r_into_trancl)
    apply (clarsimp simp: n_next_eq)
   apply clarsimp
   apply (rule conjI)
    apply (insert m_slot_next)[1]
    apply (clarsimp simp: mdb_next_unfold)
   apply clarsimp
   apply (rule r_into_trancl)
   apply (clarsimp simp: n_next_eq)
   apply (rule context_conjI)
    apply (clarsimp simp: mdb_next_unfold)
   apply (drule prev_slot_next)
   apply (clarsimp simp: mdb_next_unfold)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (drule prev_slot_next)
    apply (drule trancl_trans, erule r_into_trancl)
    apply simp
   apply clarsimp
   apply (erule trancl_trans)
   apply (rule r_into_trancl)
   apply (simp add: n_next_eq)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule rtrancl_trans)
   apply (rule r_into_rtrancl)
   apply (simp add: n_next_eq)
   apply (rule conjI)
    apply clarsimp
    apply (rule context_conjI)
     apply (clarsimp simp: mdb_next_unfold)
    apply (drule prev_slot_next)
    apply (clarsimp simp: mdb_next_unfold)
   apply clarsimp
  apply clarsimp
  apply (simp split: if_split_asm)
   apply (clarsimp simp: mdb_next_unfold slot)
  apply (erule trancl_trans)
  apply (rule r_into_trancl)
  apply (clarsimp simp add: n_next_eq)
  apply (rule context_conjI)
   apply (clarsimp simp: mdb_next_unfold)
  apply (drule prev_slot_next)
  apply (clarsimp simp: mdb_next_unfold)
  done

lemma n_trancl_eq:
  "n \<turnstile> p \<leadsto>\<^sup>+ p' = (m \<turnstile> p \<leadsto>\<^sup>+ p' \<and> (p = slot \<longrightarrow> p' = 0) \<and> p' \<noteq> slot)"
  using no_0_n
  apply -
  apply (rule iffI)
   apply (frule n_tranclD)
   apply clarsimp
   apply (drule tranclD)
   apply (clarsimp simp: n_next_eq)
   apply (simp add: rtrancl_eq_or_trancl)
  apply clarsimp
  apply (drule m_tranclD)
  apply (simp split: if_split_asm)
  apply (rule r_into_trancl)
  apply (simp add: n_next_eq)
  done

lemma n_rtrancl_eq:
  "n \<turnstile> p \<leadsto>\<^sup>* p' =
  (m \<turnstile> p \<leadsto>\<^sup>* p' \<and>
   (p = slot \<longrightarrow> p' = 0 \<or> p' = slot) \<and>
   (p' = slot \<longrightarrow> p = slot))"
  by (auto simp: rtrancl_eq_or_trancl n_trancl_eq)

lemma mdb_chain_0_n:
  "mdb_chain_0 n"
  using chain
  apply (clarsimp simp: mdb_chain_0_def)
  apply (drule bspec)
   apply (fastforce simp: n_def modify_map_if split: if_split_asm)
  apply (simp add: n_trancl_eq)
  done

lemma mdb_chunked_n:
  "mdb_chunked n"
  using chunked
  apply (clarsimp simp: mdb_chunked_def)
  apply (drule n_cap)+
  apply (clarsimp split: if_split_asm)
  apply (case_tac "p=slot", clarsimp)
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply (clarsimp simp: is_chunk_def)
  apply (simp add: n_trancl_eq n_rtrancl_eq)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap)
   apply clarsimp
  apply clarsimp
  apply (erule_tac x=p'' in allE)
  apply clarsimp
  apply (drule_tac p=p'' in m_cap)
  apply clarsimp
  done

lemma untyped_mdb_n:
  "untyped_mdb' n"
  using untyped_mdb
  apply (simp add: untyped_mdb'_def descendants_of'_def parency)
  apply clarsimp
  apply (drule n_cap)+
  apply (clarsimp split: if_split_asm)
  apply (case_tac "p=slot", simp)
  apply clarsimp
  done

lemma untyped_inc_n:
  "untyped_inc' n"
  using untyped_inc
  apply (simp add: untyped_inc'_def descendants_of'_def parency)
  apply clarsimp
  apply (drule n_cap)+
  apply (clarsimp split: if_split_asm)
  apply (case_tac "p=slot", simp)
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply simp
  done

lemmas vn_prev [dest!] = valid_nullcaps_prev [OF _ slot no_0 dlist nullcaps]
lemmas vn_next [dest!] = valid_nullcaps_next [OF _ slot no_0 dlist nullcaps]

lemma nullcaps_n: "valid_nullcaps n"
proof -
  from valid have "valid_nullcaps m" ..
  thus ?thesis
    apply (clarsimp simp: valid_nullcaps_def nullMDBNode_def nullPointer_def)
    apply (frule n_cap)
    apply (frule n_next)
    apply (frule n_badged)
    apply (frule n_revokable)
    apply (drule n_prev)
    apply (case_tac n)
    apply (insert slot)
    apply (fastforce split: if_split_asm)
    done
qed

lemma ut_rev_n: "ut_revocable' n"
  apply(insert valid)
  apply(clarsimp simp: ut_revocable'_def)
  apply(frule n_cap)
  apply(drule n_revokable)
  apply(clarsimp simp: isCap_simps split: if_split_asm)
  apply(simp add: valid_mdb_ctes_def ut_revocable'_def)
  done

lemma class_links_n: "class_links n"
  using valid slot
  apply (clarsimp simp: valid_mdb_ctes_def class_links_def)
  apply (case_tac cte, case_tac cte')
  apply (drule n_nextD)
  apply (clarsimp simp: split: if_split_asm)
    apply (simp add: no_0_n)
   apply (drule n_cap)+
   apply clarsimp
   apply (frule spec[where x=slot],
          drule spec[where x="mdbNext s_node"],
          simp, simp add: m_slot_next)
   apply (drule spec[where x="mdbPrev s_node"],
          drule spec[where x=slot], simp)
  apply (drule n_cap)+
  apply clarsimp
  apply (fastforce split: if_split_asm)
  done

lemma distinct_zombies_m: "distinct_zombies m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma distinct_zombies_n[simp]:
  "distinct_zombies n"
  using distinct_zombies_m
  apply (simp add: n_def distinct_zombies_nonCTE_modify_map)
  apply (subst modify_map_apply[where p=slot])
   apply (simp add: modify_map_def slot)
  apply simp
  apply (rule distinct_zombies_sameMasterE)
    apply (simp add: distinct_zombies_nonCTE_modify_map)
   apply (simp add: modify_map_def slot)
  apply simp
  done

lemma irq_control_n [simp]: "irq_control n"
  using slot
  apply (clarsimp simp: irq_control_def)
  apply (frule n_revokable)
  apply (drule n_cap)
  apply (clarsimp split: if_split_asm)
  apply (frule irq_revocable, rule irq_control)
  apply clarsimp
  apply (drule n_cap)
  apply (clarsimp simp: if_split_asm)
  apply (erule (1) irq_controlD, rule irq_control)
  done

lemma vmdb_n: "valid_mdb_ctes n"
  by (simp add: valid_mdb_ctes_def valid_dlist_n
                no_0_n mdb_chain_0_n valid_badges_n
                caps_contained_n mdb_chunked_n
                untyped_mdb_n untyped_inc_n
                nullcaps_n ut_rev_n class_links_n)

end

context begin interpretation Arch .
crunches postCapDeletion, clearUntypedFreeIndex
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"

lemma emptySlot_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace>
  emptySlot sl opt
  \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding emptySlot_def
  apply (simp only: case_Null_If valid_mdb'_def)
  apply (wp updateCap_ctes_of_wp getCTE_wp'
            opt_return_pres_lift | simp add: cte_wp_at_ctes_of)+
  apply (clarsimp)
  apply (case_tac cte)
  apply (rename_tac cap node)
  apply (simp)
  apply (subgoal_tac "mdb_empty (ctes_of s) sl cap node")
   prefer 2
   apply (rule mdb_empty.intro)
   apply (rule mdb_ptr.intro)
    apply (rule vmdb.intro)
    apply (simp add: valid_mdb_ctes_def)
   apply (rule mdb_ptr_axioms.intro)
   apply (simp add: cte_wp_at_ctes_of)
  apply (rule conjI, clarsimp simp: valid_mdb_ctes_def)
  apply (erule mdb_empty.vmdb_n[unfolded const_def])
  done
end

lemma if_live_then_nonz_cap'_def2:
  "if_live_then_nonz_cap' = (\<lambda>s. \<forall>ptr. ko_wp_at' live' ptr s
                               \<longrightarrow> (\<exists>p zr. (option_map zobj_refs' o cteCaps_of s) p = Some zr \<and> ptr \<in> zr))"
  by (fastforce simp: if_live_then_nonz_cap'_def ex_nonz_cap_to'_def
                      cte_wp_at_ctes_of cteCaps_of_def)

lemma updateMDB_ko_wp_at_live[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' live' p' s)\<rbrace>
      updateMDB p m
   \<lbrace>\<lambda>rv s. P (ko_wp_at' live' p' s)\<rbrace>"
  unfolding updateMDB_def Let_def
  apply (rule hoare_pre, wp)
  apply simp
  done

lemma updateCap_ko_wp_at_live[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' live' p' s)\<rbrace>
      updateCap p cap
   \<lbrace>\<lambda>rv s. P (ko_wp_at' live' p' s)\<rbrace>"
  unfolding updateCap_def
  by wp

fun threadCapRefs :: "capability \<Rightarrow> word32 set" where
  "threadCapRefs (ThreadCap r) = {r}"
| "threadCapRefs _             = {}"

definition
  "isFinal cap p m \<equiv>
  \<not>isUntypedCap cap \<and>
  (\<forall>p' c. m p' = Some c \<longrightarrow>
          p \<noteq> p' \<longrightarrow> \<not>isUntypedCap c \<longrightarrow>
          \<not> sameObjectAs cap c)"

lemma not_FinalE:
  "\<lbrakk> \<not> isFinal cap sl cps; isUntypedCap cap \<Longrightarrow> P;
     \<And>p c. \<lbrakk> cps p = Some c; p \<noteq> sl; \<not> isUntypedCap c; sameObjectAs cap c \<rbrakk> \<Longrightarrow> P
    \<rbrakk> \<Longrightarrow> P"
  by (fastforce simp: isFinal_def)

definition
 "removeable' sl \<equiv> \<lambda>s cap.
    (\<exists>p. p \<noteq> sl \<and> cte_wp_at' (\<lambda>cte. capMasterCap (cteCap cte) = capMasterCap cap) p s)
    \<or> ((\<forall>p \<in> cte_refs' cap (irq_node' s). p \<noteq> sl \<longrightarrow> cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) p s)
         \<and> (\<forall>p \<in> zobj_refs' cap. ko_wp_at' (Not \<circ> live') p s)
         \<and> (\<forall>t \<in> threadCapRefs cap. \<forall>p. t \<notin> set (ksReadyQueues s p)))"

lemma not_Final_removeable:
  "\<not> isFinal cap sl (cteCaps_of s)
    \<Longrightarrow> removeable' sl s cap"
  apply (erule not_FinalE)
   apply (clarsimp simp: removeable'_def isCap_simps)
  apply (clarsimp simp: cteCaps_of_def sameObjectAs_def2 removeable'_def
                        cte_wp_at_ctes_of)
  apply fastforce
  done

context begin interpretation Arch .
crunch ko_wp_at'[wp]: postCapDeletion "\<lambda>s. P (ko_wp_at' P' p s)"
crunch cteCaps_of[wp]: postCapDeletion "\<lambda>s. P (cteCaps_of s)"
  (simp: cteCaps_of_def o_def)
end

crunch ko_at_live[wp]: clearUntypedFreeIndex "\<lambda>s. P (ko_wp_at' live' ptr s)"

lemma clearUntypedFreeIndex_cteCaps_of[wp]:
  "\<lbrace>\<lambda>s. P (cteCaps_of s)\<rbrace>
       clearUntypedFreeIndex sl \<lbrace>\<lambda>y s. P (cteCaps_of s)\<rbrace>"
  by (simp add: cteCaps_of_def, wp)

lemma emptySlot_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> cte_wp_at' (\<lambda>cte. removeable' sl s (cteCap cte)) sl s\<rbrace>
     emptySlot sl opt
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: emptySlot_def case_Null_If if_live_then_nonz_cap'_def2
              del: comp_apply)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
             getCTE_wp opt_return_pres_lift
             clearUntypedFreeIndex_ctes_of
             clearUntypedFreeIndex_cteCaps_of
             hoare_vcg_ex_lift
             | wp (once) hoare_vcg_imp_lift
             | simp add: cte_wp_at_ctes_of del: comp_apply)+
  apply (clarsimp simp: modify_map_same imp_conjR[symmetric])
  apply (drule spec, drule(1) mp)
  apply (clarsimp simp: cte_wp_at_ctes_of modify_map_def split: if_split_asm)
  apply (case_tac "p \<noteq> sl")
   apply blast
  apply (simp add: removeable'_def cteCaps_of_def)
  apply (erule disjE)
   apply (clarsimp simp: cte_wp_at_ctes_of modify_map_def
                   dest!: capMaster_same_refs)
   apply fastforce
  apply clarsimp
  apply (drule(1) bspec)
  apply (clarsimp simp: ko_wp_at'_def)
  done

lemma setIRQState_irq_node'[wp]:
  "\<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> setIRQState state irq \<lbrace>\<lambda>_ s. P (irq_node' s)\<rbrace>"
  apply (simp add: setIRQState_def setInterruptState_def getInterruptState_def)
  apply wp
  apply simp
  done

context begin interpretation Arch .
crunch irq_node'[wp]: emptySlot "\<lambda>s. P (irq_node' s)"
end

lemma emptySlot_ifunsafe'[wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap' s \<and> cte_wp_at' (\<lambda>cte. removeable' sl s (cteCap cte)) sl s\<rbrace>
     emptySlot sl opt
   \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: ifunsafe'_def3)
  apply (rule hoare_pre, rule hoare_use_eq_irq_node'[OF emptySlot_irq_node'])
   apply (simp add: emptySlot_def case_Null_If)
   apply (wp opt_return_pres_lift | simp add: o_def)+
   apply (wp getCTE_cteCap_wp clearUntypedFreeIndex_cteCaps_of)+
  apply (clarsimp simp: tree_cte_cteCap_eq[unfolded o_def]
                        modify_map_same
                        modify_map_comp[symmetric]
                 split: option.split_asm if_split_asm
                 dest!: modify_map_K_D)
  apply (clarsimp simp: modify_map_def)
  apply (drule_tac x=cref in spec, clarsimp)
  apply (case_tac "cref' \<noteq> sl")
   apply (rule_tac x=cref' in exI)
   apply (clarsimp simp: modify_map_def)
  apply (simp add: removeable'_def)
  apply (erule disjE)
   apply (clarsimp simp: modify_map_def)
   apply (subst(asm) tree_cte_cteCap_eq[unfolded o_def])
   apply (clarsimp split: option.split_asm dest!: capMaster_same_refs)
   apply fastforce
  apply clarsimp
  apply (drule(1) bspec)
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def)
  done

lemma ctes_of_valid'[elim]:
  "\<lbrakk>ctes_of s p = Some cte; valid_objs' s\<rbrakk> \<Longrightarrow> s \<turnstile>' cteCap cte"
  by (rule ctes_of_valid_cap'')

crunch valid_idle'[wp]: setInterruptState "valid_idle'"
  (simp: valid_idle'_def)

context begin interpretation Arch .
crunch valid_idle'[wp]: emptySlot "valid_idle'"

crunch ksArch[wp]: emptySlot "\<lambda>s. P (ksArchState s)"
crunch ksIdle[wp]: emptySlot "\<lambda>s. P (ksIdleThread s)"
crunch gsMaxObjectSize[wp]: emptySlot "\<lambda>s. P (gsMaxObjectSize s)"
end

lemma emptySlot_cteCaps_of:
  "\<lbrace>\<lambda>s. P (cteCaps_of s(p \<mapsto> NullCap))\<rbrace>
     emptySlot p opt
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: emptySlot_def case_Null_If)
  apply (wp opt_return_pres_lift getCTE_cteCap_wp
            clearUntypedFreeIndex_cteCaps_of)
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of)
  apply (auto elim!: rsubst[where P=P]
               simp: modify_map_def fun_upd_def[symmetric] o_def
                     fun_upd_idem cteCaps_of_def
              split: option.splits)
  done

lemma emptySlot_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs' and cte_at' sl\<rbrace> emptySlot sl opt \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def global_refs'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF emptySlot_irq_node'])
   apply (rule hoare_use_eq [where f=ksArchState, OF emptySlot_ksArch])
   apply (rule hoare_use_eq [where f=ksIdleThread, OF emptySlot_ksIdle])
   apply (rule hoare_use_eq [where f=gsMaxObjectSize], wp)
   apply (simp add: valid_refs'_cteCaps valid_cap_sizes_cteCaps)
   apply (rule emptySlot_cteCaps_of)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule(1) cte_at_valid_cap_sizes_0)
  apply (clarsimp simp: valid_refs'_cteCaps valid_cap_sizes_cteCaps ball_ran_eq)
  done

lemmas doMachineOp_irq_handlers[wp]
    = valid_irq_handlers_lift'' [OF doMachineOp_ctes doMachineOp_ksInterrupt]

lemma deletedIRQHandler_irq_handlers'[wp]:
  "\<lbrace>\<lambda>s. valid_irq_handlers' s \<and> (IRQHandlerCap irq \<notin> ran (cteCaps_of s))\<rbrace>
       deletedIRQHandler irq
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: deletedIRQHandler_def setIRQState_def setInterruptState_def getInterruptState_def)
  apply wp
  apply (clarsimp simp: valid_irq_handlers'_def irq_issued'_def ran_def cteCaps_of_def)
  done

context begin interpretation Arch .

lemma postCapDeletion_irq_handlers'[wp]:
  "\<lbrace>\<lambda>s. valid_irq_handlers' s \<and> (cap \<noteq> NullCap \<longrightarrow> cap \<notin> ran (cteCaps_of s))\<rbrace>
       postCapDeletion cap
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  by (wpsimp simp: Retype_H.postCapDeletion_def ARM_H.postCapDeletion_def)

end

crunch ksInterruptState[wp]: clearUntypedFreeIndex "\<lambda>s. P (ksInterruptState s)"

lemma emptySlot_valid_irq_handlers'[wp]:
  "\<lbrace>\<lambda>s. valid_irq_handlers' s
          \<and> (\<forall>sl'. info \<noteq> NullCap \<longrightarrow> sl' \<noteq> sl \<longrightarrow> cteCaps_of s sl' \<noteq> Some info)\<rbrace>
     emptySlot sl info
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: emptySlot_def case_Null_If)
  apply (wp | wpc)+
        apply (unfold valid_irq_handlers'_def irq_issued'_def)
        apply (wp getCTE_cteCap_wp clearUntypedFreeIndex_cteCaps_of
          | wps clearUntypedFreeIndex_ksInterruptState)+
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of ran_def modify_map_def
                 split: option.split)
  apply auto
  done

declare setIRQState_irq_states' [wp]

context begin interpretation Arch .
crunch irq_states' [wp]: emptySlot valid_irq_states'

crunch no_0_obj' [wp]: emptySlot no_0_obj'
 (wp: crunch_wps)

crunch valid_queues'[wp]: setInterruptState "valid_queues'"
  (simp: valid_queues'_def)

crunch valid_queues'[wp]: emptySlot "valid_queues'"

crunch pde_mappings'[wp]: emptySlot "valid_pde_mappings'"
end

lemma deletedIRQHandler_irqs_masked'[wp]:
  "\<lbrace>irqs_masked'\<rbrace> deletedIRQHandler irq \<lbrace>\<lambda>_. irqs_masked'\<rbrace>"
  apply (simp add: deletedIRQHandler_def setIRQState_def getInterruptState_def setInterruptState_def)
  apply (wp dmo_maskInterrupt)
  apply (simp add: irqs_masked'_def)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma setObject_cte_irq_masked'[wp]:
  "setObject p (v::cte) \<lbrace>irqs_masked'\<rbrace>"
  unfolding setObject_def
  by (wpsimp simp: irqs_masked'_def Ball_def wp: hoare_vcg_all_lift hoare_vcg_imp_lift' updateObject_cte_inv)

crunch irqs_masked'[wp]: emptySlot "irqs_masked'"

lemma setIRQState_umm:
 "\<lbrace>\<lambda>s. P (underlying_memory (ksMachineState s))\<rbrace>
   setIRQState irqState irq
  \<lbrace>\<lambda>_ s. P (underlying_memory (ksMachineState s))\<rbrace>"
  by (simp add: setIRQState_def maskInterrupt_def
                setInterruptState_def getInterruptState_def
      | wp dmo_lift')+

crunch umm[wp]: emptySlot "\<lambda>s. P (underlying_memory (ksMachineState s))"
  (wp: setIRQState_umm)

lemma emptySlot_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> emptySlot slot irq \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  by (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
     (wp hoare_vcg_all_lift hoare_vcg_disj_lift)

crunches emptySlot
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"

lemma deletedIRQHandler_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> deletedIRQHandler irq \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF deletedIRQHandler_nosch])
  apply (rule hoare_weaken_pre)
   apply (wps deletedIRQHandler_ct)
   apply (simp add: deletedIRQHandler_def setIRQState_def)
   apply (wp)
  apply (simp add: comp_def)
  done

crunch ct_not_inQ[wp]: emptySlot "ct_not_inQ"

crunch tcbDomain[wp]: emptySlot "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"

lemma emptySlot_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> emptySlot sl opt \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
apply (wp ct_idle_or_in_cur_domain'_lift2 tcb_in_cur_domain'_lift | simp)+
done

crunch gsUntypedZeroRanges[wp]: postCapDeletion "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps simp: crunch_simps)

lemma untypedZeroRange_modify_map_isUntypedCap:
  "m sl = Some v \<Longrightarrow> \<not> isUntypedCap v \<Longrightarrow> \<not> isUntypedCap (f v)
    \<Longrightarrow> (untypedZeroRange \<circ>\<^sub>m modify_map m sl f) = (untypedZeroRange \<circ>\<^sub>m m)"
  by (simp add: modify_map_def map_comp_def fun_eq_iff untypedZeroRange_def)

lemma emptySlot_untyped_ranges[wp]:
  "\<lbrace>untyped_ranges_zero' and valid_objs' and valid_mdb'\<rbrace>
     emptySlot sl opt \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (simp add: emptySlot_def case_Null_If)
  apply (rule hoare_pre)
   apply (rule hoare_seq_ext)
    apply (rule untyped_ranges_zero_lift)
     apply (wp getCTE_cteCap_wp clearUntypedFreeIndex_cteCaps_of
       | wpc | simp add: clearUntypedFreeIndex_def updateTrackedFreeIndex_def
                         getSlotCap_def
                  split: option.split)+
  apply (clarsimp simp: modify_map_comp[symmetric] modify_map_same)
  apply (case_tac "\<not> isUntypedCap (the (cteCaps_of s sl))")
   apply (case_tac "the (cteCaps_of s sl)",
     simp_all add: untyped_ranges_zero_inv_def
                   untypedZeroRange_modify_map_isUntypedCap isCap_simps)[1]
  apply (clarsimp simp: isCap_simps untypedZeroRange_def modify_map_def)
  apply (strengthen untyped_ranges_zero_fun_upd[mk_strg I E])
  apply simp
  apply (simp add: untypedZeroRange_def isCap_simps)
  done

crunches emptySlot
  for replies_of'[wp]: "\<lambda>s. P (replies_of' s)"

lemma emptySlot_invs'[wp]:
  "\<lbrace>\<lambda>s. invs' s \<and> cte_wp_at' (\<lambda>cte. removeable' sl s (cteCap cte)) sl s
            \<and> (\<forall>sl'. info \<noteq> NullCap \<longrightarrow> sl' \<noteq> sl \<longrightarrow> cteCaps_of s sl' \<noteq> Some info)\<rbrace>
     emptySlot sl info
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp valid_arch_state_lift' valid_irq_node_lift cur_tcb_lift)
  apply (clarsimp simp: cte_wp_at_ctes_of o_def)
  done

lemma deleted_irq_corres:
  "corres dc \<top> \<top>
    (deleted_irq_handler irq)
    (deletedIRQHandler irq)"
  apply (simp add: deleted_irq_handler_def deletedIRQHandler_def)
  apply (rule set_irq_state_corres)
  apply (simp add: irq_state_relation_def)
  done

lemma arch_post_cap_deletion_corres:
  "acap_relation cap cap' \<Longrightarrow> corres dc \<top> \<top> (arch_post_cap_deletion cap) (ARM_H.postCapDeletion cap')"
  by (corressimp simp: arch_post_cap_deletion_def ARM_H.postCapDeletion_def)

lemma post_cap_deletion_corres:
  "cap_relation cap cap' \<Longrightarrow> corres dc \<top> \<top> (post_cap_deletion cap) (postCapDeletion cap')"
  apply (cases cap; clarsimp simp: post_cap_deletion_def Retype_H.postCapDeletion_def)
   apply (corressimp corres: deleted_irq_corres)
  by (corressimp corres: arch_post_cap_deletion_corres)

lemma set_cap_trans_state:
  "((),s') \<in> fst (set_cap c p s) \<Longrightarrow> ((),trans_state f s') \<in> fst (set_cap c p (trans_state f s))"
  apply (cases p)
  apply (clarsimp simp add: set_cap_def in_monad set_object_def get_object_def)
  apply (case_tac y)
  apply (auto simp add: in_monad set_object_def split: if_split_asm)
  done

lemma clearUntypedFreeIndex_corres_noop:
  "corres dc \<top> (cte_at' (cte_map slot))
    (return ()) (clearUntypedFreeIndex (cte_map slot))"
  apply (simp add: clearUntypedFreeIndex_def)
  apply (rule corres_guard_imp)
    apply (rule corres_bind_return2)
    apply (rule corres_symb_exec_r_conj[where P'="cte_at' (cte_map slot)"])
       apply (rule corres_trivial, simp)
      apply (wp getCTE_wp' | wpc
        | simp add: updateTrackedFreeIndex_def getSlotCap_def)+
     apply (clarsimp simp: state_relation_def)
    apply (rule no_fail_pre)
     apply (wp no_fail_getSlotCap getCTE_wp'
       | wpc | simp add: updateTrackedFreeIndex_def getSlotCap_def)+
  done

lemma clearUntypedFreeIndex_valid_pspace'[wp]:
  "\<lbrace>valid_pspace'\<rbrace> clearUntypedFreeIndex slot \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp | simp add: valid_mdb'_def)+
  done

lemma empty_slot_corres:
  "cap_relation info info' \<Longrightarrow> corres dc (einvs and cte_at slot) (invs' and cte_at' (cte_map slot))
             (empty_slot slot info) (emptySlot (cte_map slot) info')"
  unfolding emptySlot_def empty_slot_def
  apply (simp add: case_Null_If)
  apply (rule corres_guard_imp)
    apply (rule corres_split_noop_rhs[OF _ clearUntypedFreeIndex_corres_noop])
     apply (rule_tac R="\<lambda>cap. einvs and cte_wp_at ((=) cap) slot" and
                     R'="\<lambda>cte. valid_pspace' and cte_wp_at' ((=) cte) (cte_map slot)" in
                     corres_split [OF _ get_cap_corres])
       defer
       apply (wp get_cap_wp getCTE_wp')+
     apply (simp add: cte_wp_at_ctes_of)
     apply (wp hoare_vcg_imp_lift clearUntypedFreeIndex_valid_pspace')
    apply fastforce
   apply (fastforce simp: cte_wp_at_ctes_of)
  apply simp
  apply (rule conjI, clarsimp)
   defer
  apply clarsimp
  apply (rule conjI, clarsimp)
  apply clarsimp
  apply (simp only: bind_assoc[symmetric])
  apply (rule corres_split'[where r'=dc, OF _ post_cap_deletion_corres])
    defer
    apply wpsimp+
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp static_imp_wp)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pspace'_def)
   apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def)
   apply (rule conjI, clarsimp)
    apply (erule (2) valid_dlistEp)
    apply simp
   apply clarsimp
   apply (erule (2) valid_dlistEn)
   apply simp
  apply (clarsimp simp: in_monad bind_assoc exec_gets)
  apply (subgoal_tac "mdb_empty_abs a")
   prefer 2
   apply (rule mdb_empty_abs.intro)
   apply (rule vmdb_abs.intro)
   apply fastforce
  apply (frule mdb_empty_abs'.intro)
  apply (simp add: mdb_empty_abs'.empty_slot_ext_det_def2 update_cdt_list_def set_cdt_list_def exec_gets set_cdt_def bind_assoc exec_get exec_put set_original_def modify_def del: fun_upd_apply | subst bind_def, simp, simp add: mdb_empty_abs'.empty_slot_ext_det_def2)+
  apply (simp add: put_def)
  apply (simp add: exec_gets exec_get exec_put del: fun_upd_apply | subst bind_def)+
  apply (clarsimp simp: state_relation_def)
  apply (drule updateMDB_the_lot, fastforce, fastforce, fastforce)
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                         valid_mdb'_def valid_mdb_ctes_def)
  apply (elim conjE)
  apply (drule (4) updateMDB_the_lot, elim conjE)
  apply clarsimp
  apply (drule_tac s'=s''a and c=cap.NullCap in set_cap_not_quite_corres; (simp (no_asm_simp))?)
      subgoal by fastforce
     subgoal by fastforce
    subgoal by fastforce
   apply (erule cte_wp_at_weakenE, rule TrueI)
  apply clarsimp
  apply (drule updateCap_stuff, elim conjE, erule (1) impE)
  apply clarsimp
  apply (drule updateMDB_the_lot, force, assumption+, simp)
  apply (rule bexI)
   prefer 2
   apply (simp only: trans_state_update[symmetric])
   apply (rule set_cap_trans_state)
   apply (rule set_cap_revokable_update)
   apply (erule set_cap_cdt_update)
  apply clarsimp
  apply (thin_tac "ctes_of t = s" for t s)+
  apply (thin_tac "ksMachineState t = p" for t p)+
  apply (thin_tac "ksCurThread t = p" for t p)+
  apply (thin_tac "ksReadyQueues t = p" for t p)+
  apply (thin_tac "ksSchedulerAction t = p" for t p)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac rv')
  apply (rename_tac s_cap s_node)
  apply (subgoal_tac "cte_at slot a")
   prefer 2
   apply (fastforce elim: cte_wp_at_weakenE)
  apply (subgoal_tac "mdb_empty (ctes_of b) (cte_map slot) s_cap s_node")
   prefer 2
   apply (rule mdb_empty.intro)
   apply (rule mdb_ptr.intro)
    apply (rule vmdb.intro)
    subgoal by (simp add: invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def)
   apply (rule mdb_ptr_axioms.intro)
   subgoal by simp
  apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv)

  apply (rule conjI)
   apply (clarsimp simp: data_at_def ghost_relation_typ_at set_cap_a_type_inv)
  apply (rule conjI)
   prefer 2
   apply (rule conjI)
    apply (clarsimp simp: cdt_list_relation_def)
    apply(frule invs_valid_pspace, frule invs_mdb)
    apply(subgoal_tac "no_mloop (cdt a) \<and> finite_depth (cdt a)")
     prefer 2
     subgoal by(simp add: finite_depth valid_mdb_def)
    apply(subgoal_tac "valid_mdb_ctes (ctes_of b)")
     prefer 2
     subgoal by(simp add: mdb_empty_def mdb_ptr_def vmdb_def)
    apply(clarsimp simp: valid_pspace_def)

    apply(case_tac "cdt a slot")
     apply(simp add: next_slot_eq[OF mdb_empty_abs'.next_slot_no_parent])
     apply(case_tac "next_slot (aa, bb) (cdt_list a) (cdt a)")
      subgoal by (simp)
     apply(clarsimp)
     apply(frule(1) mdb_empty.n_next)
     apply(clarsimp)
     apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
     apply(simp split: if_split_asm)
      apply(drule cte_map_inj_eq)
           apply(drule cte_at_next_slot)
             apply(assumption)+
      apply(simp)
     apply(subgoal_tac "(ab, bc) = slot")
      prefer 2
      apply(drule_tac cte="CTE s_cap s_node" in valid_mdbD2')
        subgoal by (clarsimp simp: valid_mdb_ctes_def no_0_def)
       subgoal by (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
      apply(clarsimp)
      apply(rule cte_map_inj_eq)
           apply(assumption)
          apply(drule(3) cte_at_next_slot', assumption)
         apply(assumption)+
     apply(simp)
     apply(drule_tac p="(aa, bb)" in no_parent_not_next_slot)
        apply(assumption)+
     apply(clarsimp)

    apply(simp add: next_slot_eq[OF mdb_empty_abs'.next_slot] split del: if_split)
    apply(case_tac "next_slot (aa, bb) (cdt_list a) (cdt a)")
     subgoal by (simp)
    apply(case_tac "(aa, bb) = slot", simp)
    apply(case_tac "next_slot (aa, bb) (cdt_list a) (cdt a) = Some slot")
     apply(simp)
     apply(case_tac "next_slot ac (cdt_list a) (cdt a)", simp)
     apply(simp)
     apply(frule(1) mdb_empty.n_next)
     apply(clarsimp)
     apply(erule_tac x=aa in allE', erule_tac x=bb in allE)
     apply(erule_tac x=ac in allE, erule_tac x=bd in allE)
     apply(clarsimp split: if_split_asm)
      apply(drule(1) no_self_loop_next)
      apply(simp)
     apply(drule_tac cte="CTE cap' node'" in valid_mdbD1')
       apply(fastforce simp: valid_mdb_ctes_def no_0_def)
      subgoal by (simp add: valid_mdb'_def)
     apply(clarsimp)
    apply(simp)
    apply(frule(1) mdb_empty.n_next)
    apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
    apply(clarsimp split: if_split_asm)
     apply(drule(1) no_self_loop_prev)
     apply(clarsimp)
     apply(drule_tac cte="CTE s_cap s_node" in valid_mdbD2')
       apply(clarsimp simp: valid_mdb_ctes_def no_0_def)
      apply clarify
     apply(clarsimp)
     apply(drule cte_map_inj_eq)
          apply(drule(3) cte_at_next_slot')
          apply(assumption)+
     apply(simp)
    apply(erule disjE)
     apply(drule cte_map_inj_eq)
          apply(drule(3) cte_at_next_slot)
          apply(assumption)+
     apply(simp)
    subgoal by (simp)
   apply (simp add: revokable_relation_def)
   apply (clarsimp simp: in_set_cap_cte_at)
   apply (rule conjI)
    apply clarsimp
    apply (drule(1) mdb_empty.n_revokable)
    subgoal by clarsimp
   apply clarsimp
   apply (drule (1) mdb_empty.n_revokable)
   apply (subgoal_tac "null_filter (caps_of_state a) (aa,bb) \<noteq> None")
    prefer 2
    apply (drule set_cap_caps_of_state_monad)
    subgoal by (force simp: null_filter_def)
   apply clarsimp
   apply (subgoal_tac "cte_at (aa, bb) a")
    prefer 2
    apply (drule null_filter_caps_of_stateD, erule cte_wp_cte_at)
   apply (drule (2) cte_map_inj_ps, fastforce)
   subgoal by simp
  apply (clarsimp simp add: cdt_relation_def)
  apply (subst mdb_empty_abs.descendants, assumption)
  apply (subst mdb_empty.descendants, assumption)
  apply clarsimp
  apply (frule_tac p="(aa, bb)" in in_set_cap_cte_at)
  apply clarsimp
  apply (frule (2) cte_map_inj_ps, fastforce)
  apply simp
  apply (case_tac "slot \<in> descendants_of (aa,bb) (cdt a)")
   apply (subst inj_on_image_set_diff)
      apply (rule inj_on_descendants_cte_map)
         apply fastforce
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    subgoal by simp
   subgoal by simp
  apply simp
  apply (subgoal_tac "cte_map slot \<notin> descendants_of' (cte_map (aa,bb)) (ctes_of b)")
   subgoal by simp
  apply (erule_tac x=aa in allE, erule allE, erule (1) impE)
  apply (drule_tac s="cte_map ` u" for u in sym)
  apply clarsimp
  apply (drule cte_map_inj_eq, assumption)
      apply (erule descendants_of_cte_at, fastforce)
     apply fastforce
    apply fastforce
   apply fastforce
  apply simp
  done



text \<open>Some facts about is_final_cap/isFinalCapability\<close>

lemma isFinalCapability_inv:
  "\<lbrace>P\<rbrace> isFinalCapability cap \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: isFinalCapability_def Let_def
              split del: if_split cong: if_cong)
  apply (rule hoare_pre, wp)
   apply (rule hoare_post_imp [where Q="\<lambda>s. P"], simp)
   apply wp
  apply simp
  done

definition
  final_matters' :: "capability \<Rightarrow> bool"
where
 "final_matters' cap \<equiv> case cap of
    EndpointCap ref bdg s r g gr \<Rightarrow> True
  | NotificationCap ref bdg s r \<Rightarrow> True
  | ThreadCap ref \<Rightarrow> True
  | CNodeCap ref bits gd gs \<Rightarrow> True
  | Zombie ptr zb n \<Rightarrow> True
  | IRQHandlerCap irq \<Rightarrow> True
  | ArchObjectCap acap \<Rightarrow> (case acap of
    PageCap d ref rghts sz mapdata \<Rightarrow> False
  | ASIDControlCap \<Rightarrow> False
  | _ \<Rightarrow> True)
  | _ \<Rightarrow> False"

lemma final_matters_Master:
  "final_matters' (capMasterCap cap) = final_matters' cap"
  by (simp add: capMasterCap_def split: capability.split arch_capability.split,
      simp add: final_matters'_def)

lemma final_matters_sameRegion_sameObject:
  "final_matters' cap \<Longrightarrow> sameRegionAs cap cap' = sameObjectAs cap cap'"
  apply (rule iffI)
   apply (erule sameRegionAsE)
      apply (simp add: sameObjectAs_def3)
      apply (clarsimp simp: isCap_simps sameObjectAs_sameRegionAs final_matters'_def
        split:capability.splits arch_capability.splits)+
  done

lemma final_matters_sameRegion_sameObject2:
  "\<lbrakk> final_matters' cap'; \<not> isUntypedCap cap; \<not> isIRQHandlerCap cap' \<rbrakk>
     \<Longrightarrow> sameRegionAs cap cap' = sameObjectAs cap cap'"
  apply (rule iffI)
   apply (erule sameRegionAsE)
      apply (simp add: sameObjectAs_def3)
      apply (fastforce simp: isCap_simps final_matters'_def)
     apply simp
    apply (clarsimp simp: final_matters'_def isCap_simps)
   apply (clarsimp simp: final_matters'_def isCap_simps)
  apply (erule sameObjectAs_sameRegionAs)
  done

lemma notFinal_prev_or_next:
  "\<lbrakk> \<not> isFinal cap x (cteCaps_of s); mdb_chunked (ctes_of s);
      valid_dlist (ctes_of s); no_0 (ctes_of s);
      ctes_of s x = Some (CTE cap node); final_matters' cap \<rbrakk>
     \<Longrightarrow> (\<exists>cap' node'. ctes_of s (mdbPrev node) = Some (CTE cap' node')
              \<and> sameObjectAs cap cap')
      \<or> (\<exists>cap' node'. ctes_of s (mdbNext node) = Some (CTE cap' node')
              \<and> sameObjectAs cap cap')"
  apply (erule not_FinalE)
   apply (clarsimp simp: isCap_simps final_matters'_def)
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
  apply (clarsimp simp: sameObjectAs_def3)
  done

lemma isFinal:
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> cte_wp_at' ((=) cte) x s
          \<and> final_matters' (cteCap cte)
          \<and> Q (isFinal (cteCap cte) x (cteCaps_of s)) s\<rbrace>
    isFinalCapability cte
   \<lbrace>Q\<rbrace>"
  unfolding isFinalCapability_def
  apply (cases cte)
  apply (rename_tac cap node)
  apply (unfold Let_def)
  apply (simp only: if_False)
  apply (wp getCTE_wp')
  apply (cases "mdbPrev (cteMDBNode cte) = nullPointer")
   apply simp
   apply (clarsimp simp: valid_mdb_ctes_def valid_mdb'_def
                         cte_wp_at_ctes_of)
   apply (rule conjI, clarsimp simp: nullPointer_def)
    apply (erule rsubst[where P="\<lambda>x. Q x s" for s], simp)
    apply (rule classical)
    apply (drule(5) notFinal_prev_or_next)
    apply clarsimp
   apply (clarsimp simp: nullPointer_def)
   apply (erule rsubst[where P="\<lambda>x. Q x s" for s])
   apply (rule sym, rule iffI)
    apply (rule classical)
    apply (drule(5) notFinal_prev_or_next)
    apply clarsimp
   apply clarsimp
   apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def)
   apply (case_tac cte)
   apply clarsimp
   apply (clarsimp simp add: isFinal_def)
   apply (erule_tac x="mdbNext node" in allE)
   apply simp
   apply (erule impE)
    apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def)
    apply (drule (1) mdb_chain_0_no_loops)
    apply simp
   apply (clarsimp simp: sameObjectAs_def3 isCap_simps)
  apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of
                        valid_mdb_ctes_def valid_mdb'_def)
  apply (case_tac cte)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule rsubst[where P="\<lambda>x. Q x s" for s])
   apply clarsimp
   apply (clarsimp simp: isFinal_def cteCaps_of_def)
   apply (erule_tac x="mdbPrev node" in allE)
   apply simp
   apply (erule impE)
    apply clarsimp
    apply (drule (1) mdb_chain_0_no_loops)
    apply (subgoal_tac "ctes_of s (mdbNext node) = Some (CTE cap node)")
     apply clarsimp
    apply (erule (1) valid_dlistEp)
     apply clarsimp
    apply (case_tac cte')
    apply clarsimp
   apply (clarsimp simp add: sameObjectAs_def3 isCap_simps)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule rsubst[where P="\<lambda>x. Q x s" for s], simp)
   apply (rule classical, drule(5) notFinal_prev_or_next)
   apply (clarsimp simp: sameObjectAs_sym nullPointer_def)
  apply (clarsimp simp: nullPointer_def)
  apply (erule rsubst[where P="\<lambda>x. Q x s" for s])
  apply (rule sym, rule iffI)
   apply (rule classical, drule(5) notFinal_prev_or_next)
   apply (clarsimp simp: sameObjectAs_sym)
   apply auto[1]
  apply (clarsimp simp: isFinal_def cteCaps_of_def)
  apply (case_tac cte)
  apply (erule_tac x="mdbNext node" in allE)
  apply simp
  apply (erule impE)
   apply clarsimp
   apply (drule (1) mdb_chain_0_no_loops)
   apply simp
  apply clarsimp
  apply (clarsimp simp: isCap_simps sameObjectAs_def3)
  done
end

lemma (in vmdb) isFinal_no_subtree:
  "\<lbrakk> m \<turnstile> sl \<rightarrow> p; isFinal cap sl (option_map cteCap o m);
      m sl = Some (CTE cap n); final_matters' cap \<rbrakk> \<Longrightarrow> False"
  apply (erule subtree.induct)
   apply (case_tac "c'=sl", simp)
   apply (clarsimp simp: isFinal_def parentOf_def mdb_next_unfold cteCaps_of_def)
   apply (erule_tac x="mdbNext n" in allE)
   apply simp
   apply (clarsimp simp: isMDBParentOf_CTE final_matters_sameRegion_sameObject)
   apply (clarsimp simp: isCap_simps sameObjectAs_def3)
  apply clarsimp
  done

lemma isFinal_no_descendants:
  "\<lbrakk> isFinal cap sl (cteCaps_of s); ctes_of s sl = Some (CTE cap n);
      valid_mdb' s; final_matters' cap \<rbrakk>
  \<Longrightarrow> descendants_of' sl (ctes_of s) = {}"
  apply (clarsimp simp add: descendants_of'_def cteCaps_of_def)
  apply (erule(3) vmdb.isFinal_no_subtree[rotated])
  apply unfold_locales[1]
  apply (simp add: valid_mdb'_def)
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
  apply (rule classical, simp)
  apply (simp add: final_matters_sameRegion_sameObject2
                   sameObjectAs_sym)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma no_fail_isFinalCapability [wp]:
  "no_fail (valid_mdb' and cte_wp_at' ((=) cte) p) (isFinalCapability cte)"
  apply (simp add: isFinalCapability_def)
  apply (clarsimp simp: Let_def split del: if_split)
  apply (rule no_fail_pre, wp getCTE_wp')
  apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def cte_wp_at_ctes_of nullPointer_def)
  apply (rule conjI)
   apply clarsimp
   apply (erule (2) valid_dlistEp)
   apply simp
  apply clarsimp
  apply (rule conjI)
   apply (erule (2) valid_dlistEn)
   apply simp
  apply clarsimp
  apply (rule valid_dlistEn, assumption+)
  apply (erule (2) valid_dlistEp)
  apply simp
  done

lemma corres_gets_lift:
  assumes inv: "\<And>P. \<lbrace>P\<rbrace> g \<lbrace>\<lambda>_. P\<rbrace>"
  assumes res: "\<lbrace>Q'\<rbrace> g \<lbrace>\<lambda>r s. r = g' s\<rbrace>"
  assumes Q: "\<And>s. Q s \<Longrightarrow> Q' s"
  assumes nf: "no_fail Q g"
  shows "corres r P Q f (gets g') \<Longrightarrow> corres r P Q f g"
  apply (clarsimp simp add: corres_underlying_def simpler_gets_def)
  apply (drule (1) bspec)
  apply (rule conjI)
   apply clarsimp
   apply (rule bexI)
    prefer 2
    apply assumption
   apply simp
   apply (frule in_inv_by_hoareD [OF inv])
   apply simp
   apply (drule use_valid, rule res)
    apply (erule Q)
   apply simp
  apply (insert nf)
  apply (clarsimp simp: no_fail_def)
  done

lemma obj_refs_Master:
  "\<lbrakk> cap_relation cap cap'; P cap \<rbrakk>
      \<Longrightarrow> obj_refs cap =
           (if capClass (capMasterCap cap') = PhysicalClass
                  \<and> \<not> isUntypedCap (capMasterCap cap')
            then {capUntypedPtr (capMasterCap cap')} else {})"
  by (clarsimp simp: isCap_simps
              split: cap_relation_split_asm arch_cap.split_asm)

(* FIXME RT: this should maybe replace is_sc_obj_def in is_obj_defs *)
lemma is_sc_obj_def':
  "is_sc_obj n ko = (\<exists>sc. ko = kernel_object.SchedContext sc n \<and> valid_sched_context_size n)"
  unfolding is_sc_obj_def
  apply (case_tac ko; simp)
  by fastforce

lemma final_cap_corres':
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
   apply (clarsimp simp: sameObjectAs_def3 obj_refs_Master cap_irqs_relation_Master
                         arch_gen_refs_relation_Master gen_obj_refs_Int
                   cong: if_cong
                  split: capability.split_asm)
  apply (clarsimp simp: isFinal_def is_final_cap'_def3)
  apply (rule_tac x="fst ptr" in exI)
  apply (rule_tac x="snd ptr" in exI)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_def final_matters'_def
                         gen_obj_refs_Int
                  split: cap_relation_split_asm arch_cap.split_asm)
  apply clarsimp
  apply (drule_tac p="(a,b)" in cte_wp_at_eqD)
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
    apply (clarsimp simp: sameObjectAs_def3 isCap_simps valid_cap_def is_sc_obj_def'
                          obj_at_def is_obj_defs a_type_def final_matters'_def
                simp del: is_sc_obj_def
                   split: cap.split_asm arch_cap.split_asm
                          option.split_asm if_split_asm,
           simp_all add: is_cap_defs)
  apply (rule classical)
  by (clarsimp simp: cap_irqs_def cap_irq_opt_def sameObjectAs_def3 isCap_simps arch_gen_obj_refs_def
                 split: cap.split_asm)

lemma final_cap_corres:
  "corres (\<lambda>rv rv'. final_matters' (cteCap cte) \<longrightarrow> rv = rv')
          (invs and cte_wp_at ((=) cap) ptr)
          (invs' and cte_wp_at' ((=) cte) (cte_map ptr))
       (is_final_cap cap) (isFinalCapability cte)"
  apply (cases "final_matters' (cteCap cte)")
   apply simp
   apply (erule final_cap_corres')
  apply (subst bind_return[symmetric],
         rule corres_symb_exec_r)
     apply (rule corres_no_failI)
      apply wp
     apply (clarsimp simp: in_monad is_final_cap_def simpler_gets_def)
    apply (wp isFinalCapability_inv)+
  apply fastforce
  done

text \<open>Facts about finalise_cap/finaliseCap and
        cap_delete_one/cteDelete in no particular order\<close>


definition
  finaliseCapTrue_standin_simple_def:
  "finaliseCapTrue_standin cap fin \<equiv> finaliseCap cap fin True"

context
notes if_cong [cong]
begin

lemmas finaliseCapTrue_standin_def
    = finaliseCapTrue_standin_simple_def
        [unfolded finaliseCap_def, simplified]

lemmas cteDeleteOne_def'
    = eq_reflection [OF cteDeleteOne_def]
lemmas cteDeleteOne_def
    = cteDeleteOne_def'[folded finaliseCapTrue_standin_simple_def]

crunches cteDeleteOne, suspend, prepareThreadDelete
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps  hoare_vcg_if_lift2 hoare_vcg_all_lift
   simp: crunch_simps unless_def o_def)

end

interpretation cancelAllIPC: typ_at_props' "cancelAllIPC x" by typ_at_props'
interpretation cancelAllSignals: typ_at_props' "cancelAllSignals x" by typ_at_props'
interpretation suspend: typ_at_props' "suspend x" by typ_at_props'

definition
  arch_cap_has_cleanup' :: "arch_capability \<Rightarrow> bool"
where
  "arch_cap_has_cleanup' acap \<equiv> False"

definition
  cap_has_cleanup' :: "capability \<Rightarrow> bool"
where
  "cap_has_cleanup' cap \<equiv> case cap of
     IRQHandlerCap _ \<Rightarrow> True
   | ArchObjectCap acap \<Rightarrow> arch_cap_has_cleanup' acap
   | _ \<Rightarrow> False"

lemmas cap_has_cleanup'_simps[simp] = cap_has_cleanup'_def[split_simps capability.split]

lemma finaliseCap_cases[wp]:
  "\<lbrace>\<top>\<rbrace>
     finaliseCap cap final flag
   \<lbrace>\<lambda>rv s. fst rv = NullCap \<and> (snd rv \<noteq> NullCap \<longrightarrow> final \<and> cap_has_cleanup' cap \<and> snd rv = cap)
     \<or>
       isZombie (fst rv) \<and> final \<and> \<not> flag \<and> snd rv = NullCap
        \<and> capUntypedPtr (fst rv) = capUntypedPtr cap
        \<and> (isThreadCap cap \<or> isCNodeCap cap \<or> isZombie cap)\<rbrace>"
  apply (simp add: finaliseCap_def ARM_H.finaliseCap_def Let_def
                   getThreadCSpaceRoot
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply ((wp | simp add: isCap_simps split del: if_split
              | wpc
              | simp only: valid_NullCap fst_conv snd_conv)+)[1]
  apply (simp only: simp_thms fst_conv snd_conv option.simps if_cancel
                    o_def)
  apply (intro allI impI conjI TrueI)
  apply (auto simp add: isCap_simps cap_has_cleanup'_def)
  done

(* FIXME RT: move to ArchAcc *)
lemma getObject_ap_inv: "\<lbrace>P\<rbrace> getObject p \<lbrace>\<lambda>rv::asidpool. P\<rbrace>"
  apply (rule getObject_inv)
  apply (simp add: loadObject_default_inv)
  done

crunches finaliseCap
  for aligned'[wp]: "pspace_aligned'"
  and distinct'[wp]:"pspace_distinct'"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  (wp: crunch_wps getObject_ap_inv hoare_vcg_all_lift simp: crunch_simps)

lemmas finaliseCap_typ_ats[wp] = typ_at_lifts[OF finaliseCap_typ_at']

lemma ntfn_q_refs_of'_mult:
  "ntfn_q_refs_of' ntfn = (case ntfn of Structures_H.WaitingNtfn q \<Rightarrow> set q | _ \<Rightarrow> {}) \<times> {NTFNSignal}"
  by (cases ntfn, simp_all)

lemma tcb_st_not_Bound:
  "(p, NTFNBound) \<notin> tcb_st_refs_of' ts"
  "(p, TCBBound) \<notin> tcb_st_refs_of' ts"
  by (auto simp: tcb_st_refs_of'_def split: Structures_H.thread_state.split)

lemma get_refs_NTFNSchedContext_not_Bound:
  "(tcb, NTFNBound) \<notin> get_refs NTFNSchedContext (ntfnSc ntfn)"
  by (clarsimp simp: get_refs_def split: option.splits)

lemma tcb_bound_refs'_not_Bound:
  "(y, TCBBound) \<notin> tcb_bound_refs' None sc_ptr yieldto_ptr"
  by (clarsimp simp: tcb_bound_refs'_def get_refs_def split: option.splits)

lemma unbindNotification_invs[wp]:
  "\<lbrace>invs'\<rbrace> unbindNotification tcb \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: unbindNotification_def invs'_def valid_state'_def)
  apply (rule hoare_seq_ext[OF _ gbn_sp'])
  apply (case_tac ntfnPtr, clarsimp, wp, clarsimp)
  apply clarsimp
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
   apply (wp sbn'_valid_pspace'_inv sbn_sch_act' sbn_valid_queues valid_irq_node_lift
             irqs_masked_lift setBoundNotification_ct_not_inQ
             untyped_ranges_zero_lift | clarsimp simp: cteCaps_of_def o_def)+
  apply (rule conjI)
   apply (frule obj_at_valid_objs', clarsimp+)
   apply (simp add: valid_ntfn'_def valid_obj'_def projectKOs
             split: ntfn.splits)
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at' conj_comms)
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs live_ntfn'_def)
  apply (frule obj_at_valid_objs', clarsimp+)
  apply (simp add: valid_ntfn'_def valid_obj'_def projectKOs
            split: ntfn.splits)
  done

lemma ntfn_bound_tcb_at':
  "\<lbrakk>sym_refs (state_refs_of' s); valid_objs' s; ko_at' ntfn ntfnptr s;
    ntfnBoundTCB ntfn = Some tcbptr; P (Some ntfnptr)\<rbrakk>
  \<Longrightarrow> bound_tcb_at' P tcbptr s"
  apply (drule_tac x=ntfnptr in sym_refsD[rotated])
   apply (clarsimp simp: obj_at'_def projectKOs)
   apply (fastforce simp: state_refs_of'_def)
  apply (auto simp: pred_tcb_at'_def obj_at'_def valid_obj'_def valid_ntfn'_def
                    state_refs_of'_def refs_of_rev' projectKOs
          simp del: refs_of_simps
             split: option.splits if_split_asm)
  done


lemma unbindMaybeNotification_invs[wp]:
  "\<lbrace>invs'\<rbrace> unbindMaybeNotification ntfnptr \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: unbindMaybeNotification_def invs'_def valid_state'_def)
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
   apply (wp sbn'_valid_pspace'_inv sbn_sch_act' sbn_valid_queues valid_irq_node_lift
             irqs_masked_lift setBoundNotification_ct_not_inQ
             untyped_ranges_zero_lift
             | wpc | clarsimp simp: cteCaps_of_def)+
  apply (clarsimp simp: o_def)
  sorry (* unbindMaybeNotification_invs *) (*
  apply safe[1]
           defer 3
           defer 7
           apply (fold_subgoals (prefix))[8]
           subgoal premises prems using prems by (auto simp: pred_tcb_at' valid_pspace'_def projectKOs valid_obj'_def valid_ntfn'_def
                             ko_wp_at'_def
                      elim!: obj_atE' valid_objsE' if_live_then_nonz_capE'
                      split: option.splits ntfn.splits)
   apply (rule delta_sym_refs, assumption)
    apply (fold_subgoals (prefix))[2]
    subgoal premises prems using prems by (fastforce simp: symreftype_inverse' ntfn_q_refs_of'_def
                    split: ntfn.splits if_split_asm
                     dest!: ko_at_state_refs_ofD')+
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_split_asm)
   apply (frule ko_at_state_refs_ofD', simp)
  apply (clarsimp split: if_split_asm)
   apply (frule_tac P="(=) (Some ntfnptr)" in ntfn_bound_tcb_at', simp_all add: valid_pspace'_def)[1]
   subgoal by (fastforce simp: ntfn_q_refs_of'_def state_refs_of'_def tcb_ntfn_is_bound'_def
                          tcb_st_refs_of'_def
                   dest!: bound_tcb_at_state_refs_ofD'
                   split: ntfn.splits thread_state.splits)
  apply (frule ko_at_state_refs_ofD', simp)
  done *)

crunches getReplyTCB
  for inv[wp]: P

(* Ugh, required to be able to split out the abstract invs *)
lemma finaliseCap_True_invs[wp]:
  "\<lbrace>invs'\<rbrace> finaliseCap cap final True \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply if_split [split del]
  unfolding finaliseCap_def
  apply (wpsimp wp: irqs_masked_lift simp: Let_def)
  sorry (* finaliseCap_True_invs *)

crunch invs'[wp]: flushSpace "invs'" (ignore: doMachineOp)

lemma ct_not_inQ_ksArchState_update[simp]:
  "ct_not_inQ (s\<lparr>ksArchState := v\<rparr>) = ct_not_inQ s"
  by (simp add: ct_not_inQ_def)

lemma invs_asid_update_strg':
  "invs' s \<and> tab = armKSASIDTable (ksArchState s) \<longrightarrow>
   invs' (s\<lparr>ksArchState := armKSASIDTable_update
            (\<lambda>_. tab (asid := None)) (ksArchState s)\<rparr>)"
  apply (simp add: invs'_def)
  apply (simp add: valid_state'_def)
  apply (simp add: valid_global_refs'_def global_refs'_def valid_arch_state'_def valid_asid_table'_def valid_machine_state'_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  apply (auto simp add: ran_def split: if_split_asm)
  done

lemma invalidateASIDEntry_invs' [wp]:
  "\<lbrace>invs'\<rbrace> invalidateASIDEntry asid \<lbrace>\<lambda>r. invs'\<rbrace>"
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
                    ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
   subgoal by (auto elim!: subset_inj_on)
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (rule conjI)
   apply (simp add: valid_global_refs'_def
                    global_refs'_def)
  apply (rule conjI)
   apply (simp add: valid_arch_state'_def ran_def valid_asid_table'_def
                    fun_upd_def[symmetric] comp_upd_simp)
  apply (simp add: valid_machine_state'_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma deleteASIDPool_invs[wp]:
  "\<lbrace>invs'\<rbrace> deleteASIDPool asid pool \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: deleteASIDPool_def)
  apply wp
    apply (simp del: fun_upd_apply)
    apply (strengthen invs_asid_update_strg')
  apply (wp mapM_wp' getObject_inv loadObject_default_inv
              | simp)+
  done

lemma invalidateASIDEntry_valid_ap' [wp]:
  "\<lbrace>valid_asid_pool' p\<rbrace> invalidateASIDEntry asid \<lbrace>\<lambda>r. valid_asid_pool' p\<rbrace>"
  apply (simp add: invalidateASIDEntry_def invalidateASID_def
                   invalidateHWASIDEntry_def bind_assoc)
  apply (wp loadHWASID_wp | simp)+
  apply (case_tac p)
  apply (clarsimp simp del: fun_upd_apply)
  done

lemmas flushSpace_typ_ats' [wp] = typ_at_lifts [OF flushSpace_typ_at']

lemma deleteASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> deleteASID asid pd \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: deleteASID_def cong: option.case_cong)
  apply (rule hoare_pre)
   apply (wp | wpc)+
      apply (rule_tac Q="\<lambda>rv. valid_obj' (injectKO rv) and invs'"
                in hoare_post_imp)
     apply (clarsimp split: if_split_asm del: subsetI)
     apply (simp add: fun_upd_def[symmetric] valid_obj'_def)
     apply (case_tac r, simp)
     apply (subst inv_f_f, rule inj_onI, simp)+
     apply (rule conjI)
      apply clarsimp
      apply (drule subsetD, blast)
      apply clarsimp
     apply (auto dest!: ran_del_subset)[1]
    apply (wp getObject_valid_obj getObject_inv loadObject_default_inv
             | simp add: objBits_simps archObjSize_def pageBits_def)+
  apply clarsimp
  done

lemma arch_finaliseCap_invs[wp]:
  "\<lbrace>invs' and valid_cap' (ArchObjectCap cap)\<rbrace>
     Arch.finaliseCap cap fin
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding ARM_H.finaliseCap_def
  apply clarsimp
  apply (safe ; wpsimp)
  done

lemma arch_finaliseCap_removeable[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile>' ArchObjectCap cap \<and> invs' s
       \<and> (final \<and> final_matters' (ArchObjectCap cap)
            \<longrightarrow> isFinal (ArchObjectCap cap) slot (cteCaps_of s))\<rbrace>
     Arch.finaliseCap cap final
   \<lbrace>\<lambda>rv s. isNullCap (fst rv) \<and> removeable' slot s (ArchObjectCap cap) \<and> isNullCap (snd rv)\<rbrace>"
  apply (simp add: ARM_H.finaliseCap_def
                   removeable'_def)
  apply (safe ; wpsimp)
  done

lemma isZombie_Null:
  "\<not> isZombie NullCap"
  by (simp add: isCap_simps)

lemma prepares_delete_helper'':
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  shows      "\<lbrace>P and K ((\<forall>x. cte_refs' cap x = {})
                          \<and> zobj_refs' cap = {p}
                          \<and> threadCapRefs cap = {})\<rbrace>
                 f \<lbrace>\<lambda>rv s. removeable' sl s cap\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post [OF x])
  apply (clarsimp simp: removeable'_def)
  done

lemmas ctes_of_cteCaps_of_lift = cteCaps_of_ctes_of_lift

crunches finaliseCapTrue_standin, unbindNotification
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps getObject_inv loadObject_default_inv simp: crunch_simps)

lemma cteDeleteOne_cteCaps_of:
  "\<lbrace>\<lambda>s. (cte_wp_at' (\<lambda>cte. \<exists>final. finaliseCap (cteCap cte) final True \<noteq> fail) p s \<longrightarrow>
          P (cteCaps_of s(p \<mapsto> NullCap)))\<rbrace>
     cteDeleteOne p
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def split_def)
  apply (rule hoare_seq_ext [OF _ getCTE_sp])
  apply (case_tac "\<forall>final. finaliseCap (cteCap cte) final True = fail")
   apply (simp add: finaliseCapTrue_standin_simple_def)
   apply wp
   apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def
                         finaliseCap_def isCap_simps)
   apply (drule_tac x=s in fun_cong)
   apply (simp add: return_def fail_def)
  apply (wp emptySlot_cteCaps_of)
    apply (simp add: cteCaps_of_def)
    apply (wp (once) hoare_drop_imps)
    apply (wp isFinalCapability_inv getCTE_wp')+
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of)
  apply (auto simp: fun_upd_idem fun_upd_def[symmetric] o_def)
  done

lemma cteDeleteOne_isFinal:
  "\<lbrace>\<lambda>s. isFinal cap slot (cteCaps_of s)\<rbrace>
     cteDeleteOne p
   \<lbrace>\<lambda>rv s. isFinal cap slot (cteCaps_of s)\<rbrace>"
  apply (wp cteDeleteOne_cteCaps_of)
  apply (clarsimp simp: isFinal_def sameObjectAs_def2)
  done

lemmas setEndpoint_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF set_ep'.ctes_of]
lemmas setNotification_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF set_ntfn'.ctes_of]
lemmas setSchedContext_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF set_sc'.ctes_of]
lemmas setReply_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF set_reply'.ctes_of]
lemmas setQueue_cteCaps_of[wp] = ctes_of_cteCaps_of_lift [OF setQueue_ctes_of]
lemmas sts_cteCaps_of[wp] = ctes_of_cteCaps_of_lift[OF sts_ctes_of]
lemmas threadSet_cteCaps_of = ctes_of_cteCaps_of_lift [OF threadSet_ctes_of]

(* FIXME RT: I don't understand why this is not crunchable *)
lemma replyRemoveTCB_ctes_of[wp]:
  "replyRemoveTCB t \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace>"
  supply if_split [split del]
  unfolding replyRemoveTCB_def
  by (wpsimp wp: hoare_drop_imp hoare_vcg_if_lift2 hoare_vcg_all_lift)

lemmas replyRemoveTCB_cteCaps_of[wp] = ctes_of_cteCaps_of_lift[OF replyRemoveTCB_ctes_of]

crunches suspend, prepareThreadDelete
  for isFinal: "\<lambda>s. isFinal cap slot (cteCaps_of s)"
  (ignore: threadSet
       wp: threadSet_cteCaps_of crunch_wps
     simp: crunch_simps)

lemma isThreadCap_threadCapRefs_tcbptr:
  "isThreadCap cap \<Longrightarrow> threadCapRefs cap = {capTCBPtr cap}"
  by (clarsimp simp: isCap_simps)

lemma isArchObjectCap_Cap_capCap:
  "isArchObjectCap cap \<Longrightarrow> ArchObjectCap (capCap cap) = cap"
  by (clarsimp simp: isCap_simps)

lemma cteDeleteOne_deletes[wp]:
  "\<lbrace>\<top>\<rbrace> cteDeleteOne p \<lbrace>\<lambda>rv s. cte_wp_at' (\<lambda>c. cteCap c = NullCap) p s\<rbrace>"
  apply (subst tree_cte_cteCap_eq[unfolded o_def])
  apply (wp cteDeleteOne_cteCaps_of)
  apply clarsimp
  done

lemma deletingIRQHandler_removeable':
  "\<lbrace>invs' and (\<lambda>s. isFinal (IRQHandlerCap irq) slot (cteCaps_of s))
          and K (cap = IRQHandlerCap irq)\<rbrace>
     deletingIRQHandler irq
   \<lbrace>\<lambda>rv s. removeable' slot s cap\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: deletingIRQHandler_def getIRQSlot_def locateSlot_conv
                   getInterruptState_def getSlotCap_def)
  apply (simp add: removeable'_def tree_cte_cteCap_eq[unfolded o_def])
  apply (subst tree_cte_cteCap_eq[unfolded o_def])+
  apply (wp hoare_use_eq_irq_node' [OF cteDeleteOne_irq_node' cteDeleteOne_cteCaps_of]
            getCTE_wp')
  apply (clarsimp simp: cte_level_bits_def ucast_nat_def split: option.split_asm)
  done

lemma finaliseCap_cte_refs:
  "\<lbrace>\<lambda>s. s \<turnstile>' cap\<rbrace>
     finaliseCap cap final flag
   \<lbrace>\<lambda>rv s. fst rv \<noteq> NullCap \<longrightarrow> cte_refs' (fst rv) = cte_refs' cap\<rbrace>"
  apply (simp  add: finaliseCap_def Let_def getThreadCSpaceRoot
                    ARM_H.finaliseCap_def
             cong: if_cong split del: if_split)
   apply wpsimp
  apply (frule valid_capAligned)
  apply (cases cap, simp_all add: isCap_simps)
  by (auto simp: capAligned_def objBits_simps shiftL_nat cte_refs'_def tcb_cte_cases_def word_count_from_top objBits_defs)

lemma deletingIRQHandler_final:
  "\<lbrace>\<lambda>s. isFinal cap slot (cteCaps_of s)
             \<and> (\<forall>final. finaliseCap cap final True = fail)\<rbrace>
     deletingIRQHandler irq
   \<lbrace>\<lambda>rv s. isFinal cap slot (cteCaps_of s)\<rbrace>"
  apply (simp add: deletingIRQHandler_def isFinal_def getIRQSlot_def
                   getInterruptState_def locateSlot_conv getSlotCap_def)
  apply (wp cteDeleteOne_cteCaps_of getCTE_wp')
  apply (auto simp: sameObjectAs_def3)
  done

declare suspend_unqueued [wp]

lemma unbindNotification_valid_objs'_helper:
  "valid_tcb' tcb s \<longrightarrow> valid_tcb' (tcbBoundNotification_update (\<lambda>_. None) tcb) s "
  by (clarsimp simp: valid_bound_ntfn'_def valid_tcb'_def tcb_cte_cases_def
                  split: option.splits ntfn.splits)

lemma unbindNotification_valid_objs'_helper':
  "valid_ntfn' tcb s \<longrightarrow> valid_ntfn' (ntfnBoundTCB_update (\<lambda>_. None) tcb) s "
  by (clarsimp simp: valid_bound_tcb'_def valid_ntfn'_def
                  split: option.splits ntfn.splits)

(* FIXME RT: move up, together with locale instance below *)
lemma typ_at'_valid_tcb'_lift:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  assumes Q: "\<And>P n p. \<lbrace>\<lambda>s. P (sc_at'_n n p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (sc_at'_n n p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_tcb' tcb s\<rbrace> f \<lbrace>\<lambda>rv s. valid_tcb' tcb s\<rbrace>"
  including no_pre
  apply (simp add: valid_tcb'_def)
  apply (case_tac "tcbState tcb"; simp add: valid_tcb_state'_def split_def valid_bound_ntfn'_def)
         apply (wp hoare_vcg_const_Ball_lift typ_at_lifts[OF P] Q valid_case_option_post_wp)+
  done

end

locale typ_at_sc_at'_n_props' = typ_at_props' +
  assumes scs: "f \<lbrace>\<lambda>s. Q (sc_at'_n n p s)\<rbrace>"
begin

lemma valid_tcb'[wp]:
  "f \<lbrace>valid_tcb' tcb\<rbrace>"
  by (rule typ_at'_valid_tcb'_lift, rule typ', rule scs)

end

context begin interpretation Arch .

lemma unbindNotification_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace>
     unbindNotification t
   \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: unbindNotification_def)
  apply (rule hoare_pre)
  apply (wp threadSet_valid_objs' gbn_wp' set_ntfn_valid_objs' hoare_vcg_all_lift getNotification_wp
        | wpc | clarsimp simp: setBoundNotification_def unbindNotification_valid_objs'_helper)+
  apply (clarsimp elim!: obj_atE' simp: projectKOs)
  apply (rule valid_objsE', assumption+)
  apply (clarsimp simp: valid_obj'_def unbindNotification_valid_objs'_helper')
  done

lemma unbindMaybeNotification_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace>
     unbindMaybeNotification t
   \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: unbindMaybeNotification_def)
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
  apply (wp threadSet_valid_objs' gbn_wp' set_ntfn_valid_objs' hoare_vcg_all_lift getNotification_wp
        | wpc | clarsimp simp: setBoundNotification_def unbindNotification_valid_objs'_helper)+
  apply (clarsimp elim!: obj_atE' simp: projectKOs)
  apply (rule valid_objsE', assumption+)
  apply (clarsimp simp: valid_obj'_def unbindNotification_valid_objs'_helper')
  done

lemma unbindMaybeNotification_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace> unbindMaybeNotification t
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: unbindMaybeNotification_def)
  apply (rule hoare_pre)
  apply (wp sbn_sch_act' | wpc | simp)+
  done

lemma valid_cong:
  "\<lbrakk> \<And>s. P s = P' s; \<And>s. P' s \<Longrightarrow> f s = f' s;
        \<And>rv s' s. \<lbrakk> (rv, s') \<in> fst (f' s); P' s \<rbrakk> \<Longrightarrow> Q rv s' = Q' rv s' \<rbrakk>
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> = \<lbrace>P'\<rbrace> f' \<lbrace>Q'\<rbrace>"
  by (clarsimp simp add: valid_def, blast)

lemma unbindMaybeNotification_obj_at'_bound:
  "\<lbrace>\<top>\<rbrace>
     unbindMaybeNotification r
   \<lbrace>\<lambda>_ s. obj_at' (\<lambda>ntfn. ntfnBoundTCB ntfn = None) r s\<rbrace>"
  apply (simp add: unbindMaybeNotification_def)
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
   apply (wp obj_at_setObject2
        | wpc
        | simp add: setBoundNotification_def threadSet_def updateObject_default_def in_monad projectKOs)+
  apply (simp add: setNotification_def obj_at'_real_def cong: valid_cong)
   apply (wp setObject_ko_wp_at, (simp add: objBits_simps')+)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  done

crunches unbindNotification, unbindMaybeNotification
  for isFinal[wp]: "\<lambda>s. isFinal cap slot (cteCaps_of s)"
  (wp: sts_bound_tcb_at' threadSet_cteCaps_of crunch_wps getObject_inv loadObject_default_inv
   ignore: threadSet)

crunches cancelSignal, cancelAllIPC
  for bound_tcb_at'[wp]: "bound_tcb_at' P t"
  (wp: sts_bound_tcb_at' crunch_wps getObject_inv loadObject_default_inv)

(* FIXME RT: bound_tcb_at' is an outdated name? *)
lemma threadSet_sc_bound_tcb_at'[wp]:
  "threadSet (tcbSchedContext_update f) t' \<lbrace>bound_tcb_at' P t\<rbrace>"
  by (wpsimp wp: threadSet_pred_tcb_no_state)

crunches replyClear
  for bound_tcb_at'[wp]: "bound_tcb_at' P t"
  (wp: crunch_wps simp: crunch_simps ignore: threadSet)

lemma finaliseCapTrue_standin_bound_tcb_at':
  "\<lbrace>\<lambda>s. bound_tcb_at' P t s \<and> (\<exists>tt r. cap = ReplyCap tt r) \<rbrace>
     finaliseCapTrue_standin cap final
   \<lbrace>\<lambda>_. bound_tcb_at' P t\<rbrace>"
  apply (case_tac cap; simp add: finaliseCapTrue_standin_def isCap_simps)
  by wpsimp

lemma capDeleteOne_bound_tcb_at':
  "\<lbrace>bound_tcb_at' P tptr and cte_wp_at' (isReplyCap \<circ> cteCap) callerCap\<rbrace>
      cteDeleteOne callerCap \<lbrace>\<lambda>rv. bound_tcb_at' P tptr\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def)
  apply (rule hoare_pre)
   apply (wp finaliseCapTrue_standin_bound_tcb_at' hoare_vcg_all_lift
            hoare_vcg_if_lift2 getCTE_cteCap_wp
        | wpc | simp | wp (once) hoare_drop_imp)+
  apply (clarsimp simp:  cteCaps_of_def projectKOs isReplyCap_def cte_wp_at_ctes_of
                 split: option.splits)
  apply (case_tac "cteCap cte", simp_all)
  done

crunches getBlockingObject
  for inv[wp]: P

lemma replyRemoveTCB_bound_tcb_at'[wp]:
  "replyRemoveTCB t \<lbrace>bound_tcb_at' P tptr\<rbrace>"
  unfolding replyRemoveTCB_def
  by (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift threadSet_pred_tcb_no_state)

lemma cancelIPC_bound_tcb_at'[wp]:
  "\<lbrace>bound_tcb_at' P tptr\<rbrace> cancelIPC t \<lbrace>\<lambda>rv. bound_tcb_at' P tptr\<rbrace>"
  unfolding cancelIPC_def
  by (wpsimp wp: sts_bound_tcb_at' hoare_drop_imp hoare_vcg_all_lift threadSet_pred_tcb_no_state
           simp: Let_def)

lemma schedContextCancelYieldTo_bound_tcb_at[wp]:
  "schedContextCancelYieldTo t \<lbrace> bound_tcb_at' P tptr \<rbrace>"
  unfolding schedContextCancelYieldTo_def
  by (wpsimp wp: threadSet_pred_tcb_no_state hoare_vcg_if_lift2 hoare_drop_imp)

crunches suspend, prepareThreadDelete
  for bound_tcb_at'[wp]: "bound_tcb_at' P t"
  (wp: sts_bound_tcb_at' cancelIPC_bound_tcb_at' crunch_wps)

lemma unbindNotification_bound_tcb_at':
  "\<lbrace>\<lambda>_. True\<rbrace> unbindNotification t \<lbrace>\<lambda>rv. bound_tcb_at' ((=) None) t\<rbrace>"
  apply (simp add: unbindNotification_def)
  apply (wp setBoundNotification_bound_tcb gbn_wp' | wpc | simp)+
  done

crunches unbindNotification, unbindMaybeNotification
  for valid_queues[wp]: "Invariants_H.valid_queues"
  (wp: sbn_valid_queues)

crunches unbindNotification, unbindMaybeNotification
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"

lemma unbindNotification_tcb_at'[wp]:
  "\<lbrace>tcb_at' t'\<rbrace> unbindNotification t \<lbrace>\<lambda>rv. tcb_at' t'\<rbrace>"
  apply (simp add: unbindNotification_def)
  apply (wp gbn_wp' | wpc | simp)+
  done

lemma unbindMaybeNotification_tcb_at'[wp]:
  "\<lbrace>tcb_at' t'\<rbrace> unbindMaybeNotification t \<lbrace>\<lambda>rv. tcb_at' t'\<rbrace>"
  apply (simp add: unbindMaybeNotification_def)
  apply (wp gbn_wp' | wpc | simp)+
  done

crunch cte_wp_at'[wp]: prepareThreadDelete "cte_wp_at' P p"
crunch valid_cap'[wp]: prepareThreadDelete "valid_cap' cap"
crunch invs[wp]: prepareThreadDelete "invs'"

end

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
                     \<and> (\<forall>pr. p \<notin> set (ksReadyQueues s pr))))\<rbrace>"
  apply (simp add: finaliseCap_def Let_def getThreadCSpaceRoot
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp prepares_delete_helper'' [OF cancelAllIPC_unlive]
             prepares_delete_helper'' [OF cancelAllSignals_unlive]
             suspend_isFinal prepareThreadDelete_unqueued prepareThreadDelete_nonq
             prepareThreadDelete_inactive prepareThreadDelete_isFinal
             suspend_makes_inactive suspend_nonq
             deletingIRQHandler_removeable'
             deletingIRQHandler_final[where slot=slot ]
             unbindMaybeNotification_obj_at'_bound
             getNotification_wp
             suspend_bound_tcb_at'
             unbindNotification_bound_tcb_at'
           | simp add: isZombie_Null isThreadCap_threadCapRefs_tcbptr
                       isArchObjectCap_Cap_capCap
           | (rule hoare_strengthen_post [OF arch_finaliseCap_removeable[where slot=slot]],
                  clarsimp simp: isCap_simps)
           | wpc)+
  sorry (*
  apply clarsimp
  apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp+)
  apply (case_tac "cteCap cte",
         simp_all add: isCap_simps capRange_def cap_has_cleanup'_def
                       final_matters'_def objBits_simps
                       not_Final_removeable finaliseCap_def,
         simp_all add: removeable'_def)
     (* thread *)
     apply (frule capAligned_capUntypedPtr [OF valid_capAligned], simp)
     apply (clarsimp simp: valid_cap'_def)
     apply (drule valid_globals_cte_wpD'[rotated], clarsimp)
     apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
    apply (clarsimp simp: obj_at'_def | rule conjI)+
  done *)

lemma cteDeleteOne_cte_wp_at_preserved:
  assumes x: "\<And>cap final. P cap \<Longrightarrow> finaliseCap cap final True = fail"
  shows "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s\<rbrace>
           cteDeleteOne ptr
         \<lbrace>\<lambda>rv s. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s\<rbrace>"
  apply (simp add: tree_cte_cteCap_eq[unfolded o_def])
  apply (rule hoare_pre, wp cteDeleteOne_cteCaps_of)
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of x)
  done

crunch ctes_of[wp]: cancelSignal "\<lambda>s. P (ctes_of s)"
  (simp: crunch_simps wp: crunch_wps)

lemma cancelIPC_cteCaps_of:
  "\<lbrace>\<lambda>s. (\<forall>p. cte_wp_at' (\<lambda>cte. \<exists>final. finaliseCap (cteCap cte) final True \<noteq> fail) p s \<longrightarrow>
          P (cteCaps_of s(p \<mapsto> NullCap))) \<and>
     P (cteCaps_of s)\<rbrace>
     cancelIPC t
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cancelIPC_def Let_def capHasProperty_def locateSlot_conv)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_pre)
   apply (wp cteDeleteOne_cteCaps_of getCTE_wp' | wpcw
        | simp add: cte_wp_at_ctes_of
        | wp (once) hoare_drop_imps ctes_of_cteCaps_of_lift)+
          apply (wp hoare_convert_imp hoare_vcg_all_lift
                    threadSet_ctes_of threadSet_cteCaps_of
               | clarsimp)+
  done

lemma cancelIPC_cte_wp_at':
  assumes x: "\<And>cap final. P cap \<Longrightarrow> finaliseCap cap final True = fail"
  shows "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s\<rbrace>
           cancelIPC t
         \<lbrace>\<lambda>rv s. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s\<rbrace>"
  apply (simp add: tree_cte_cteCap_eq[unfolded o_def])
  apply (rule hoare_pre, wp cancelIPC_cteCaps_of)
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of x)
  done

crunch cte_wp_at'[wp]: tcbSchedDequeue "cte_wp_at' P p"

crunches schedContextCancelYieldTo, tcbReleaseRemove
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  (wp: crunch_wps simp: crunch_simps)

lemma suspend_cte_wp_at':
  assumes [simp]: "\<And>cap final. P cap \<Longrightarrow> finaliseCap cap final True = fail"
  shows "suspend t \<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte)) p\<rbrace>"
  unfolding updateRestartPC_def suspend_def
  apply (wpsimp wp: threadSet_cte_wp_at' cancelIPC_cte_wp_at' hoare_vcg_imp_lift
                    cancelIPC_st_tcb_at hoare_disjI2[where Q="\<lambda>_. cte_wp_at' a b" for a b])
  done

context begin interpretation Arch . (*FIXME: arch_split*)

crunch cte_wp_at'[wp]: deleteASIDPool "cte_wp_at' P p"
  (simp: crunch_simps assertE_def
   wp: crunch_wps getObject_inv loadObject_default_inv)

lemma deleteASID_cte_wp_at'[wp]:
  "\<lbrace>cte_wp_at' P p\<rbrace> deleteASID param_a param_b \<lbrace>\<lambda>_. cte_wp_at' P p\<rbrace>"
  apply (simp add: deleteASID_def invalidateHWASIDEntry_def invalidateASID_def
              cong: option.case_cong)
  apply (wp setObject_cte_wp_at'[where Q="\<top>"] getObject_inv
            loadObject_default_inv setVMRoot_cte_wp_at'
          | clarsimp simp: updateObject_default_def in_monad
                           projectKOs
          | rule equals0I
          | wpc)+
  done

crunches unmapPageTable, unmapPage, unbindNotification, finaliseCapTrue_standin
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  (simp: crunch_simps wp: crunch_wps getObject_inv loadObject_default_inv)

lemma arch_finaliseCap_cte_wp_at[wp]:
  "\<lbrace>cte_wp_at' P p\<rbrace> Arch.finaliseCap cap fin \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  apply (simp add: ARM_H.finaliseCap_def)
  apply (safe ; wpsimp wp: unmapPage_cte_wp_at')
  done

lemma deletingIRQHandler_cte_preserved:
  assumes x: "\<And>cap final. P cap \<Longrightarrow> finaliseCap cap final True = fail"
  shows "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte)) p\<rbrace>
           deletingIRQHandler irq
         \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p\<rbrace>"
  apply (simp add: deletingIRQHandler_def getSlotCap_def
                   getIRQSlot_def locateSlot_conv getInterruptState_def)
  apply (wp cteDeleteOne_cte_wp_at_preserved getCTE_wp'
              | simp add: x)+
  done

lemma finaliseCap_equal_cap[wp]:
  "\<lbrace>cte_wp_at' (\<lambda>cte. cteCap cte = cap) sl\<rbrace>
     finaliseCap cap fin flag
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. cteCap cte = cap) sl\<rbrace>"
  apply (simp add: finaliseCap_def Let_def
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp suspend_cte_wp_at' deletingIRQHandler_cte_preserved
        | clarsimp simp: finaliseCap_def | wpc)+
  sorry (*
  apply (case_tac cap)
  apply auto
  done *)

lemma setThreadState_st_tcb_at_simplish':
  "simple' st \<Longrightarrow>
   \<lbrace>st_tcb_at' (P or simple') t\<rbrace>
     setThreadState st t'
   \<lbrace>\<lambda>rv. st_tcb_at' (P or simple') t\<rbrace>"
  apply (wp sts_st_tcb_at'_cases)
  apply clarsimp
  done

lemmas setThreadState_st_tcb_at_simplish
    = setThreadState_st_tcb_at_simplish'[unfolded pred_disj_def]

lemma replyUnlink_st_tcb_at_simplish:
  "replyUnlink r t' \<lbrace>st_tcb_at' (\<lambda>st. P st \<or> simple' st) t\<rbrace>"
  supply if_split [split del]
  unfolding replyUnlink_def
  apply (wpsimp wp: sts_st_tcb' hoare_vcg_if_lift2 hoare_vcg_imp_lift' gts_wp'
              simp: getReplyTCB_def)
  done

crunch st_tcb_at_simplish: cteDeleteOne
            "st_tcb_at' (\<lambda>st. P st \<or> simple' st) t"
  (wp: crunch_wps getObject_inv loadObject_default_inv threadSet_pred_tcb_no_state
   simp: crunch_simps unless_def)

lemma cteDeleteOne_st_tcb_at[wp]:
  assumes x[simp]: "\<And>st. simple' st \<longrightarrow> P st" shows
  "\<lbrace>st_tcb_at' P t\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (subgoal_tac "\<exists>Q. P = (Q or simple')")
   apply (clarsimp simp: pred_disj_def)
   apply (rule cteDeleteOne_st_tcb_at_simplish)
  apply (rule_tac x=P in exI)
  apply (auto)
  done

lemma cteDeleteOne_reply_pred_tcb_at:
  "\<lbrace>\<lambda>s. pred_tcb_at' proj P t s \<and> (\<exists>t' r. cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t' r) slot s)\<rbrace>
    cteDeleteOne slot
   \<lbrace>\<lambda>rv. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def isFinalCapability_def)
  apply (rule hoare_seq_ext [OF _ getCTE_sp])
  apply (rule hoare_assume_pre)
  apply (clarsimp simp: cte_wp_at_ctes_of when_def isCap_simps
                        Let_def finaliseCapTrue_standin_def)
  apply (intro impI conjI, (wp | simp)+)
  sorry


(* FIXME RT: this had cteDeleteOne_sch_act_simple, but does not hold any more *)
crunches unbindNotification
  for sch_act_simple[wp]: sch_act_simple
  (wp: crunch_wps ssa_sch_act_simple sts_sch_act_simple getObject_inv
       loadObject_default_inv
   simp: crunch_simps unless_def
   rule: sch_act_simple_lift)


lemma rescheduleRequired_sch_act_not[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. sch_act_not t\<rbrace>"
  apply (simp add: rescheduleRequired_def setSchedulerAction_def)
  apply (wp hoare_post_taut | simp)+
  done

(* FIXME RT: cancelAllIPC calls possibleSwitchTo
crunch sch_act_not[wp]: cteDeleteOne "sch_act_not t"
  (simp: crunch_simps case_Null_If unless_def
   wp: crunch_wps getObject_inv loadObject_default_inv)
*)

lemma cancelAllIPC_mapM_x_valid_queues:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. \<forall>t\<in>set q. tcb_at' t s)\<rbrace>
   mapM_x (\<lambda>t. do
                 y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                 tcbSchedEnqueue t
               od) q
   \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (rule_tac R="\<lambda>_ s. (\<forall>t\<in>set q. tcb_at' t s) \<and> valid_objs' s"
               in hoare_post_add)
  apply (rule hoare_pre)
  apply (rule mapM_x_wp')
  apply (rule hoare_name_pre_state)
  apply (wp hoare_vcg_const_Ball_lift
            tcbSchedEnqueue_valid_queues tcbSchedEnqueue_not_st
            sts_valid_queues sts_st_tcb_at'_cases setThreadState_not_st
       | simp
       | ((elim conjE)?, drule (1) bspec, clarsimp elim!: obj_at'_weakenE simp: valid_tcb_state'_def))+
  done

lemma cancelAllIPC_mapM_x_weak_sch_act:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   mapM_x (\<lambda>t. do
                 y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                 tcbSchedEnqueue t
               od) q
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (rule mapM_x_wp_inv)
  apply (wp)
  apply (clarsimp)
  done

lemma cancelAllIPC_mapM_x_valid_objs':
  "\<lbrace>valid_objs'\<rbrace>
   mapM_x (\<lambda>t. do
                 y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                 tcbSchedEnqueue t
               od) q
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wp mapM_x_wp' sts_valid_objs')
   apply (clarsimp simp: valid_tcb_state'_def)+
  done

lemma rescheduleRequired_oa_queued':
  "\<lbrace>obj_at' (\<lambda>tcb. Q (tcbDomain tcb) (tcbPriority tcb)) t'\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. Q (tcbDomain tcb) (tcbPriority tcb)) t'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  by (wpsimp wp: tcbSchedEnqueue_not_st isSchedulable_wp)

lemma sts_tcbDomain_obj_at'[wp]:
  "setThreadState t st \<lbrace> obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t' \<rbrace>"
  by (rule setThreadState_oa_queued)

crunches cancelAllIPC, cancelAllSignals, unbindMaybeNotification
  for tcbDomain_obj_at': "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'"
  (wp: crunch_wps)

lemma cancelAllIPC_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>
   cancelAllIPC ep_ptr
   \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: cancelAllIPC_def ep'_Idle_case_helper)
  apply (wp hoare_vcg_conj_lift hoare_vcg_const_Ball_lift
            cancelAllIPC_mapM_x_valid_queues cancelAllIPC_mapM_x_valid_objs' cancelAllIPC_mapM_x_weak_sch_act
            set_ep_valid_objs' getEndpoint_wp)
  apply (clarsimp simp: valid_ep'_def)
  sorry (*
  apply (drule (1) ko_at_valid_objs')
  apply (auto simp: valid_obj'_def valid_ep'_def valid_tcb'_def projectKOs
             split: endpoint.splits
              elim: valid_objs_valid_tcbE')
  done *)


lemma cancelAllSignals_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>
   cancelAllSignals ntfn
   \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (rule hoare_seq_ext_skip, wpsimp)
  apply (rule hoare_seq_ext [OF _ get_ntfn_sp'])
  apply (case_tac "ntfnObj ntfna", simp_all)
    apply (wp, simp)+
    apply (wp hoare_vcg_conj_lift hoare_vcg_const_Ball_lift
              cancelAllIPC_mapM_x_valid_queues cancelAllIPC_mapM_x_valid_objs' cancelAllIPC_mapM_x_weak_sch_act
              set_ntfn_valid_objs'
          | simp)+
  sorry (*
  apply (clarsimp simp: valid_ep'_def)
  apply (drule (1) ko_at_valid_objs')
  apply (auto simp: valid_obj'_def valid_ntfn'_def valid_tcb'_def projectKOs
             split: endpoint.splits
              elim: valid_objs_valid_tcbE')
  done *)

lemma finaliseCapTrue_standin_valid_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>
   finaliseCapTrue_standin cap final
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: finaliseCapTrue_standin_def Let_def)
  apply (safe)
       apply (wp | clarsimp | wpc)+
  sorry


crunches isFinalCapability
  for valid_queues[wp]: "Invariants_H.valid_queues"
  and sch_act[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  and weak_sch_act[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (simp: crunch_simps)

lemma cteDeleteOne_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>
   cteDeleteOne sl
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>" (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: cteDeleteOne_def unless_def split_def)
  apply (wp isFinalCapability_inv getCTE_wp | rule hoare_drop_imps | simp)+
  apply (clarsimp simp: cte_wp_at'_def)
  done

lemma valid_inQ_queues_lift:
  assumes tat: "\<And>d p tcb. \<lbrace>obj_at' (inQ d p) tcb\<rbrace> f \<lbrace>\<lambda>_. obj_at' (inQ d p) tcb\<rbrace>"
  and     prq: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  shows   "\<lbrace>valid_inQ_queues\<rbrace> f \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  proof -
    show ?thesis
      apply (clarsimp simp: valid_def valid_inQ_queues_def)
      apply safe
       apply (rule use_valid [OF _ tat], assumption)
       apply (drule spec, drule spec, erule conjE, erule bspec)
       apply (rule ccontr)
       apply (erule notE[rotated], erule(1) use_valid [OF _ prq])
      apply (erule use_valid [OF _ prq])
      apply simp
      done
  qed

lemma emptySlot_valid_inQ_queues [wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> emptySlot sl opt \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  unfolding emptySlot_def
  by (wp opt_return_pres_lift | wpcw | wp valid_inQ_queues_lift | simp)+

end

context simple_non_tcb_ko'
begin

(* FIXME RT: move to KHeap *)
lemma valid_inQ_queues[wp]:
  "f p v \<lbrace>valid_inQ_queues\<rbrace>"
  by (rule valid_inQ_queues_lift; wp)

end

context begin interpretation Arch .

crunches cancelAllIPC, cancelAllSignals, unbindNotification, unbindMaybeNotification,
         schedContextMaybeUnbindNtfn, isFinalCapability
  for valid_inQ_queues[wp]: "valid_inQ_queues"
  (wp: crunch_wps simp: crunch_simps)

lemma finaliseCapTrue_standin_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace>
   finaliseCapTrue_standin cap final
   \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: finaliseCapTrue_standin_def Let_def)
  apply (safe)
       apply (wp | clarsimp | wpc)+
  sorry

lemma cteDeleteOne_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace>
   cteDeleteOne sl
   \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def)
  apply (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift)
  done

crunches cteDeleteOne
  for ksCurDomain[wp]:  "\<lambda>s. P (ksCurDomain s)"
  and tcbDomain_obj_at'[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'"
  (wp: crunch_wps simp: crunch_simps unless_def)

end

global_interpretation delete_one_conc_pre
  by (unfold_locales, wp)
     (wp cteDeleteOne_tcbDomain_obj_at' cteDeleteOne_typ_at' cteDeleteOne_reply_pred_tcb_at | simp)+

lemma cteDeleteOne_invs[wp]:
  "\<lbrace>invs'\<rbrace> cteDeleteOne ptr \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def
                   split_def finaliseCapTrue_standin_simple_def)
  apply wp
    apply (rule hoare_strengthen_post)
     apply (rule hoare_vcg_conj_lift)
      apply (rule finaliseCap_True_invs)
     apply (rule hoare_vcg_conj_lift)
      apply (rule finaliseCap_replaceable[where slot=ptr])
     apply (rule hoare_vcg_conj_lift)
      apply (rule finaliseCap_cte_refs)
     apply (rule finaliseCap_equal_cap[where sl=ptr])
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (erule disjE)
     apply simp
    apply (clarsimp dest!: isCapDs simp: capRemovable_def)
    apply (clarsimp simp: removeable'_def fun_eq_iff[where f="cte_refs' cap" for cap]
                     del: disjCI)
    apply (rule disjI2)
    apply (rule conjI)
     subgoal by auto
    subgoal sorry (* by (auto dest!: isCapDs simp: pred_tcb_at'_def obj_at'_def projectKOs
                                     ko_wp_at'_def) *)
   apply (wp isFinalCapability_inv getCTE_wp' static_imp_wp
        | wp (once) isFinal[where x=ptr])+
  apply (fastforce simp: cte_wp_at_ctes_of)
  done

global_interpretation delete_one_conc_fr: delete_one_conc
  by unfold_locales wp

declare cteDeleteOne_invs[wp]

lemma deletingIRQHandler_invs' [wp]:
  "\<lbrace>invs'\<rbrace> deletingIRQHandler i \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: deletingIRQHandler_def getSlotCap_def
                   getIRQSlot_def locateSlot_conv getInterruptState_def)
  apply (wp getCTE_wp')
  apply simp
  done

lemma finaliseCap_invs:
  "\<lbrace>invs' and sch_act_simple and valid_cap' cap
         and cte_wp_at' (\<lambda>cte. cteCap cte = cap) sl\<rbrace>
     finaliseCap cap fin flag
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: finaliseCap_def Let_def
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps hoare_vcg_all_lift | simp only: o_def | wpc)+
  sorry (* finaliseCap_invs *) (*
  apply clarsimp
  apply (intro conjI impI)
    apply (clarsimp dest!: isCapDs simp: valid_cap'_def)
   apply (drule invs_valid_global', drule(1) valid_globals_cte_wpD')
   apply (drule valid_capAligned, drule capAligned_capUntypedPtr)
    apply (clarsimp dest!: isCapDs)
   apply (clarsimp dest!: isCapDs)
  apply (clarsimp dest!: isCapDs)
  done *)

lemma finaliseCap_zombie_cap[wp]:
  "\<lbrace>cte_wp_at' (\<lambda>cte. (P and isZombie) (cteCap cte)) sl\<rbrace>
     finaliseCap cap fin flag
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. (P and isZombie) (cteCap cte)) sl\<rbrace>"
  apply (simp add: finaliseCap_def Let_def
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp suspend_cte_wp_at'
             deletingIRQHandler_cte_preserved
                 | clarsimp simp: finaliseCap_def isCap_simps | wpc)+
  sorry (* finaliseCap_zombie_cap *)

lemma finaliseCap_zombie_cap':
  "\<lbrace>cte_wp_at' (\<lambda>cte. (P and isZombie) (cteCap cte)) sl\<rbrace>
     finaliseCap cap fin flag
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteCap cte)) sl\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule finaliseCap_zombie_cap)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma finaliseCap_cte_cap_wp_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to' P sl\<rbrace> finaliseCap cap fin flag \<lbrace>\<lambda>rv. ex_cte_cap_wp_to' P sl\<rbrace>"
  apply (simp add: ex_cte_cap_to'_def)
  apply (rule hoare_pre, rule hoare_use_eq_irq_node' [OF finaliseCap_irq_node'])
   apply (simp add: finaliseCap_def Let_def
              cong: if_cong split del: if_split)
   apply (wp suspend_cte_wp_at'
             deletingIRQHandler_cte_preserved
             hoare_vcg_ex_lift
                 | clarsimp simp: finaliseCap_def isCap_simps
                 | rule conjI
                 | wpc)+
  sorry (* finaliseCap_cte_cap_wp_to *) (*
  apply fastforce
  done *)

crunch valid_cap'[wp]: unbindNotification "valid_cap' cap"

lemma finaliseCap_valid_cap[wp]:
  "\<lbrace>valid_cap' cap\<rbrace> finaliseCap cap final flag \<lbrace>\<lambda>rv. valid_cap' (fst rv)\<rbrace>"
  apply (simp add: finaliseCap_def Let_def
                   getThreadCSpaceRoot
                   ARM_H.finaliseCap_def
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp | simp only: valid_NullCap o_def fst_conv | wpc)+
  sorry (* finaliseCap_valid_cap *) (*
  apply simp
  apply (intro conjI impI)
   apply (clarsimp simp: valid_cap'_def isCap_simps capAligned_def
                         objBits_simps shiftL_nat)+
  done &*)


context begin interpretation Arch . (*FIXME: arch_split*)

crunch nosch[wp]: "Arch.finaliseCap" "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_inv simp: loadObject_default_def updateObject_default_def)

(* FIXME RT: not true any more, calls possibleSwitchTo
crunch sch_act_simple[wp]: finaliseCap sch_act_simple
  (simp: crunch_simps
   rule: sch_act_simple_lift
   wp: getObject_inv loadObject_default_inv crunch_wps) *)

end


lemma interrupt_cap_null_or_ntfn:
  "invs s
    \<Longrightarrow> cte_wp_at (\<lambda>cp. is_ntfn_cap cp \<or> cp = cap.NullCap) (interrupt_irq_node s irq, []) s"
  apply (frule invs_valid_irq_node)
  apply (clarsimp simp: valid_irq_node_def)
  apply (drule_tac x=irq in spec)
  apply (drule cte_at_0)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule caps_of_state_cteD)
  apply (frule if_unsafe_then_capD, clarsimp+)
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (frule cte_refs_obj_refs_elem, erule disjE)
   apply (clarsimp | drule caps_of_state_cteD valid_global_refsD[rotated]
     | rule irq_node_global_refs[where irq=irq])+
   apply (simp add: cap_range_def)
  apply (clarsimp simp: appropriate_cte_cap_def
                 split: cap.split_asm)
  done

lemma (in delete_one) deleting_irq_corres:
  "corres dc (einvs) (invs')
          (deleting_irq_handler irq) (deletingIRQHandler irq)"
  apply (simp add: deleting_irq_handler_def deletingIRQHandler_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_irq_slot_corres])
      apply simp
      apply (rule_tac P'="cte_at' (cte_map slot)" in corres_symb_exec_r_conj)
         apply (rule_tac F="isNotificationCap rv \<or> rv = capability.NullCap"
             and P="cte_wp_at (\<lambda>cp. is_ntfn_cap cp \<or> cp = cap.NullCap) slot
                 and einvs"
             and P'="invs' and cte_wp_at' (\<lambda>cte. cteCap cte = rv)
                 (cte_map slot)" in corres_req)
          apply (clarsimp simp: cte_wp_at_caps_of_state state_relation_def)
          apply (drule caps_of_state_cteD)
          apply (drule(1) pspace_relation_cte_wp_at, clarsimp+)
          apply (auto simp: cte_wp_at_ctes_of is_cap_simps isCap_simps)[1]
         apply simp
         apply (rule corres_guard_imp, rule delete_one_corres[unfolded dc_def])
          apply (auto simp: cte_wp_at_caps_of_state is_cap_simps can_fast_finalise_def)[1]
         apply (clarsimp simp: cte_wp_at_ctes_of)
        apply (wp getCTE_wp' | simp add: getSlotCap_def)+
     apply (wp | simp add: get_irq_slot_def getIRQSlot_def
                           locateSlot_conv getInterruptState_def)+
   apply (clarsimp simp: ex_cte_cap_wp_to_def interrupt_cap_null_or_ntfn)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma arch_finalise_cap_corres:
  "\<lbrakk> final_matters' (ArchObjectCap cap') \<Longrightarrow> final = final'; acap_relation cap cap' \<rbrakk>
     \<Longrightarrow> corres (\<lambda>r r'. cap_relation (fst r) (fst r') \<and> cap_relation (snd r) (snd r'))
           (\<lambda>s. invs s \<and> valid_etcbs s
                       \<and> s \<turnstile> cap.ArchObjectCap cap
                       \<and> (final_matters (cap.ArchObjectCap cap)
                            \<longrightarrow> final = is_final_cap' (cap.ArchObjectCap cap) s)
                       \<and> cte_wp_at ((=) (cap.ArchObjectCap cap)) sl s)
           (\<lambda>s. invs' s \<and> s \<turnstile>' ArchObjectCap cap' \<and>
                 (final_matters' (ArchObjectCap cap') \<longrightarrow>
                      final' = isFinal (ArchObjectCap cap') (cte_map sl) (cteCaps_of s)))
           (arch_finalise_cap cap final) (Arch.finaliseCap cap' final')"
  apply (cases cap;
        clarsimp simp: arch_finalise_cap_def ARM_H.finaliseCap_def
                       final_matters'_def case_bool_If liftM_def[symmetric]
                       isASIDPoolCap_def isPageCap_def isPageDirectoryCap_def
                       isPageTableCap_def
                       o_def dc_def[symmetric]
                split: option.split)
     apply (rule corres_guard_imp, rule delete_asid_pool_corres)
      apply (clarsimp simp: valid_cap_def mask_def)
     apply (clarsimp simp: valid_cap'_def)
     apply auto[1]
    apply (rule corres_guard_imp, rule unmap_page_corres)
      apply simp
     apply (clarsimp simp: valid_cap_def valid_unmap_def)
     apply (auto simp: vmsz_aligned_def pbfs_atleast_pageBits mask_def
                 elim: is_aligned_weaken)[2]
   apply (rule corres_guard_imp, rule unmap_page_table_corres)
    apply (auto simp: valid_cap_def valid_cap'_def mask_def
               elim!: is_aligned_weaken)[2]
  apply (rule corres_guard_imp, rule delete_asid_corres)
   apply (auto simp: mask_def valid_cap_def)[2]
  done

lemma unbind_notification_corres:
  "corres dc
      (invs and tcb_at t)
      (invs' and tcb_at' t)
      (unbind_notification t)
      (unbindNotification t)"
  apply (simp add: unbind_notification_def unbindNotification_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ gbn_corres])
  sorry (* unbind_notification_corres*) (*
      apply (rule corres_option_split)
        apply simp
       apply (rule corres_return_trivial)
      apply (rule corres_split[OF _ get_ntfn_corres])
        apply clarsimp
        apply (rule corres_split[OF _ set_ntfn_corres])
           apply (rule sbn_corres)
          apply (clarsimp simp: ntfn_relation_def split:Structures_A.ntfn.splits)
         apply (wp gbn_wp' gbn_wp)+
   apply (clarsimp elim!: obj_at_valid_objsE
                   dest!: bound_tcb_at_state_refs_ofD invs_valid_objs
                    simp: valid_obj_def is_tcb tcb_ntfn_is_bound_def
                          valid_tcb_def valid_bound_ntfn_def
                   split: option.splits)
  apply (clarsimp dest!: obj_at_valid_objs' bound_tcb_at_state_refs_ofD' invs_valid_objs'
                   simp: projectKOs valid_obj'_def valid_tcb'_def valid_bound_ntfn'_def
                         tcb_ntfn_is_bound'_def
                  split: option.splits)
  done *)

lemma unbind_maybe_notification_corres:
  "corres dc
      (invs and ntfn_at ntfnptr) (invs' and ntfn_at' ntfnptr)
      (unbind_maybe_notification ntfnptr)
      (unbindMaybeNotification ntfnptr)"
  apply (simp add: unbind_maybe_notification_def unbindMaybeNotification_def)
  apply (rule corres_guard_imp)
  sorry (* unbind_maybe_notification_corres *) (*
    apply (rule corres_split[OF _ get_ntfn_corres])
      apply (rule corres_option_split)
        apply (clarsimp simp: ntfn_relation_def split: Structures_A.ntfn.splits)
       apply (rule corres_return_trivial)
      apply simp
      apply (rule corres_split[OF _ set_ntfn_corres])
         apply (rule sbn_corres)
        apply (clarsimp simp: ntfn_relation_def split: Structures_A.ntfn.splits)
       apply (wp get_simple_ko_wp getNotification_wp)+
   apply (clarsimp elim!: obj_at_valid_objsE
                   dest!: bound_tcb_at_state_refs_ofD invs_valid_objs
                    simp: valid_obj_def is_tcb tcb_ntfn_is_bound_def
                          valid_tcb_def valid_bound_ntfn_def valid_ntfn_def
                   split: option.splits)
  apply (clarsimp dest!: obj_at_valid_objs' bound_tcb_at_state_refs_ofD' invs_valid_objs'
                   simp: projectKOs valid_obj'_def valid_tcb'_def valid_bound_ntfn'_def
                         tcb_ntfn_is_bound'_def valid_ntfn'_def
                  split: option.splits)
  done *)

lemma fast_finalise_corres:
  "\<lbrakk> final_matters' cap' \<longrightarrow> final = final'; cap_relation cap cap';
     can_fast_finalise cap \<rbrakk>
   \<Longrightarrow> corres dc
           (\<lambda>s. invs s \<and> valid_sched s \<and> s \<turnstile> cap
                       \<and> cte_wp_at ((=) cap) sl s)
           (\<lambda>s. invs' s \<and> s \<turnstile>' cap')
           (fast_finalise cap final)
           (do
               p \<leftarrow> finaliseCap cap' final' True;
               assert (capRemovable (fst p) (cte_map ptr) \<and> snd p = NullCap)
            od)"
  apply (cases cap, simp_all add: finaliseCap_def isCap_simps
                                  corres_liftM2_simp[unfolded liftM_def]
                                  o_def dc_def[symmetric] when_def
                                  can_fast_finalise_def capRemovable_def
                       split del: if_split cong: if_cong)
   apply (clarsimp simp: final_matters'_def)
   apply (rule corres_guard_imp)
     apply (rule corres_rel_imp)
      apply (rule ep_cancel_corres)
     apply simp
    apply (simp add: valid_cap_def)
   apply (simp add: valid_cap'_def)
  apply (clarsimp simp: final_matters'_def)
  apply (rule corres_guard_imp)
  sorry (* fast_finalise_corres *) (*
    apply (rule corres_split[OF _ unbind_maybe_notification_corres])
         apply (rule ntfn_cancel_corres)
       apply (wp abs_typ_at_lifts unbind_maybe_notification_invs typ_at_lifts hoare_drop_imps getNotification_wp
            | wpc)+
   apply (clarsimp simp: valid_cap_def)
  apply (clarsimp simp: valid_cap'_def projectKOs valid_obj'_def
                 dest!: invs_valid_objs' obj_at_valid_objs' )
  done *)

lemma cap_delete_one_corres:
  "corres dc (einvs and cte_wp_at can_fast_finalise ptr)
        (invs' and cte_at' (cte_map ptr))
        (cap_delete_one ptr) (cteDeleteOne (cte_map ptr))"
  apply (simp add: cap_delete_one_def cteDeleteOne_def'
                   unless_def when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_cap_corres])
      apply (rule_tac F="can_fast_finalise cap" in corres_gen_asm)
      apply (rule corres_if)
        apply fastforce
       apply (rule corres_split [OF _ final_cap_corres[where ptr=ptr]])
         apply (simp add: split_def bind_assoc [THEN sym])
         apply (rule corres_split [OF _ fast_finalise_corres[where sl=ptr]])
              apply (rule empty_slot_corres)
             apply simp+
          apply (wp hoare_drop_imps)+
  sorry (* cap_delete_one_corres *) (*
        apply (wp isFinalCapability_inv | wp (once) isFinal[where x="cte_map ptr"])+
      apply (rule corres_trivial, simp)
     apply (wp get_cap_wp getCTE_wp)+
   apply (clarsimp simp: cte_wp_at_caps_of_state can_fast_finalise_Null
                  elim!: caps_of_state_valid_cap)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply fastforce
  done *)

end
(* FIXME: strengthen locale instead *)

global_interpretation delete_one
  apply unfold_locales
  apply (rule corres_guard_imp)
    apply (rule cap_delete_one_corres)
   apply auto
  done

lemma finalise_cap_corres:
  "\<lbrakk> final_matters' cap' \<Longrightarrow> final = final'; cap_relation cap cap';
          flag \<longrightarrow> can_fast_finalise cap \<rbrakk>
     \<Longrightarrow> corres (\<lambda>x y. cap_relation (fst x) (fst y) \<and> cap_relation (snd x) (snd y))
           (\<lambda>s. einvs s \<and> s \<turnstile> cap \<and> (final_matters cap \<longrightarrow> final = is_final_cap' cap s)
                       \<and> cte_wp_at ((=) cap) sl s)
           (\<lambda>s. invs' s \<and> s \<turnstile>' cap' \<and>
                 (final_matters' cap' \<longrightarrow>
                      final' = isFinal cap' (cte_map sl) (cteCaps_of s)))
           (finalise_cap cap final) (finaliseCap cap' final' flag)"
  apply (cases cap, simp_all add: finaliseCap_def isCap_simps
                                  corres_liftM2_simp[unfolded liftM_def]
                                  o_def dc_def[symmetric] when_def
                                  can_fast_finalise_def
                       split del: if_split cong: if_cong)
        apply (clarsimp simp: final_matters'_def)
        apply (rule corres_guard_imp)
          apply (rule ep_cancel_corres)
         apply (simp add: valid_cap_def)
        apply (simp add: valid_cap'_def)
       apply (clarsimp simp add: final_matters'_def)
       apply (rule corres_guard_imp)
  sorry (* finalise_cap_corres *) (*
         apply (rule corres_split[OF _ unbind_maybe_notification_corres])
           apply (rule ntfn_cancel_corres)
          apply (wp abs_typ_at_lifts unbind_maybe_notification_invs typ_at_lifts hoare_drop_imps hoare_vcg_all_lift | wpc)+
        apply (clarsimp simp: valid_cap_def)
       apply (clarsimp simp: valid_cap'_def)
      apply (fastforce simp: final_matters'_def shiftL_nat zbits_map_def)
     apply (clarsimp simp add: final_matters'_def getThreadCSpaceRoot
                               liftM_def[symmetric] o_def zbits_map_def
                               dc_def[symmetric])
     apply (rule corres_guard_imp)
       apply (rule corres_split[OF _ unbind_notification_corres])
         apply (rule corres_split[OF _ suspend_corres])
            apply (clarsimp simp: liftM_def[symmetric] o_def dc_def[symmetric] zbits_map_def)
          apply (rule prepareThreadDelete_corres)
        apply (wp unbind_notification_invs unbind_notification_simple_sched_action)+
      apply (simp add: valid_cap_def)
     apply (simp add: valid_cap'_def)
    apply (simp add: final_matters'_def liftM_def[symmetric]
                     o_def dc_def[symmetric])
    apply (intro impI, rule corres_guard_imp)
      apply (rule deleting_irq_corres)
     apply simp
    apply simp
   apply (clarsimp simp: final_matters'_def)
   apply (rule_tac F="False" in corres_req)
    apply clarsimp
    apply (frule zombies_finalD, (clarsimp simp: is_cap_simps)+)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply simp
  apply (clarsimp split del: if_split simp: o_def)
  apply (rule corres_guard_imp [OF arch_finalise_cap_corres], (fastforce simp: valid_sched_def)+)
  done *)
context begin interpretation Arch . (*FIXME: arch_split*)
lemma arch_recycleCap_improve_cases:
   "\<lbrakk> \<not> isPageCap cap; \<not> isPageTableCap cap; \<not> isPageDirectoryCap cap;
         \<not> isASIDControlCap cap \<rbrakk> \<Longrightarrow> (if isASIDPoolCap cap then v else undefined) = v"
  by (cases cap, simp_all add: isCap_simps)

crunch queues[wp]: copyGlobalMappings "Invariants_H.valid_queues"
  (wp: crunch_wps ignore: storePDE)

crunch queues'[wp]: copyGlobalMappings "Invariants_H.valid_queues'"
  (wp: crunch_wps ignore: storePDE)

crunch ifunsafe'[wp]: copyGlobalMappings "if_unsafe_then_cap'"
  (wp: crunch_wps ignore: storePDE)

crunch pred_tcb_at'[wp]: copyGlobalMappings "pred_tcb_at' proj P t"
  (wp: crunch_wps ignore: storePDE)

crunch vms'[wp]: copyGlobalMappings "valid_machine_state'"
  (wp: crunch_wps ignore: storePDE)

crunch ct_not_inQ[wp]: copyGlobalMappings "ct_not_inQ"
  (wp: crunch_wps ignore: storePDE)

crunch tcb_in_cur_domain'[wp]: copyGlobalMappings "tcb_in_cur_domain' t"
  (wp: crunch_wps)

crunch ct__in_cur_domain'[wp]: copyGlobalMappings ct_idle_or_in_cur_domain'
  (wp: crunch_wps)

lemma ct_in_current_domain_ArchState_update[simp]:
  "ct_idle_or_in_cur_domain' (s\<lparr>ksArchState := v\<rparr>) = ct_idle_or_in_cur_domain' s"
  by (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma threadSet_ct_idle_or_in_cur_domain':
  "\<lbrace>ct_idle_or_in_cur_domain' and (\<lambda>s. \<forall>tcb. tcbDomain tcb = ksCurDomain s \<longrightarrow> tcbDomain (F tcb) = ksCurDomain s)\<rbrace>
    threadSet F t
   \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  apply (wp hoare_vcg_disj_lift hoare_vcg_imp_lift)
    apply wps
    apply wp
   apply wps
   apply wp
  apply (auto simp: obj_at'_def)
  done

crunch valid_arch_state'[wp]: invalidateTLBByASID "valid_arch_state'"
lemmas invalidateTLBByASID_typ_ats[wp] = typ_at_lifts [OF invalidateTLBByASID_typ_at']

crunch cteCaps_of: invalidateTLBByASID "\<lambda>s. P (cteCaps_of s)"

lemmas final_matters'_simps = final_matters'_def [split_simps capability.split arch_capability.split]

end

context begin interpretation Arch .

lemma cancelAll_ct_not_ksQ_helper:
  "\<lbrace>(\<lambda>s. ksCurThread s \<notin> set (ksReadyQueues s p)) and (\<lambda>s. ksCurThread s \<notin> set q) \<rbrace>
   mapM_x (\<lambda>t. do
                 y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                 tcbSchedEnqueue t
               od) q
   \<lbrace>\<lambda>rv s. ksCurThread s \<notin> set (ksReadyQueues s p)\<rbrace>"
  apply (rule mapM_x_inv_wp2, simp)
  apply (wp)
    apply (wps tcbSchedEnqueue_ct')
    apply (wp tcbSchedEnqueue_ksQ)
   apply (wps setThreadState_ct')
   apply (wp sts_ksQ')
  apply (clarsimp)
  done

lemma cancelAllIPC_ct_not_ksQ:
  "\<lbrace>invs' and ct_in_state' simple' and sch_act_sane
          and (\<lambda>s. ksCurThread s \<notin> set (ksReadyQueues s p))\<rbrace>
   cancelAllIPC epptr
   \<lbrace>\<lambda>rv s. ksCurThread s \<notin> set (ksReadyQueues s p)\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  apply (simp add: cancelAllIPC_def)
  apply (wp, wpc, wp)
        apply (wps rescheduleRequired_ct')
        apply (wp rescheduleRequired_ksQ')
       apply clarsimp
       apply (wp cancelAll_ct_not_ksQ_helper mapM_x_wp_inv)
  oops (* FIXME RT: this lemma is probably not needed since we have ct_queues_cross *) (*
      apply (wp hoare_lift_Pf2 [OF set_ep'.ksReadyQueues set_ep'.ct])+
      apply (wps rescheduleRequired_ct')
      apply (wp rescheduleRequired_ksQ')
     apply clarsimp
     apply (wp cancelAll_ct_not_ksQ_helper mapM_x_wp_inv)
    apply (wp hoare_lift_Pf2 [OF setEndpoint_ksQ setEndpoint_ct'])+
   prefer 2
   apply assumption
  apply (rule_tac Q="\<lambda>ep. ?PRE and ko_at' ep epptr" in hoare_post_imp)
   apply (clarsimp)
   apply (rule conjI)
    apply ((clarsimp simp: invs'_def valid_state'_def
                           sch_act_sane_def
            | drule(1) ct_not_in_epQueue)+)[2]
  apply (wp get_ep_sp')
  done *)

lemma cancelAllSignals_ct_not_ksQ:
  "\<lbrace>invs' and ct_in_state' simple' and sch_act_sane
          and (\<lambda>s. ksCurThread s \<notin> set (ksReadyQueues s p))\<rbrace>
   cancelAllSignals ntfnptr
   \<lbrace>\<lambda>rv s. ksCurThread s \<notin> set (ksReadyQueues s p)\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  apply (simp add: cancelAllSignals_def)
  apply (wp, wpc, wp+)
      apply (wps rescheduleRequired_ct')
      apply (wp rescheduleRequired_ksQ')
     apply clarsimp
     apply (wp cancelAll_ct_not_ksQ_helper mapM_x_wp_inv)
  oops (* FIXME RT: this lemma is probably not needed since we have ct_queues_cross *) (*
    apply (wp hoare_lift_Pf2 [OF set_ntfn'.ksReadyQueues set_ntfn'.ct])
    apply (wps set_ntfn'.ct, wp)
   prefer 2
   apply assumption
  apply (rule_tac Q="\<lambda>ep. ?PRE and ko_at' ep ntfnptr" in hoare_post_imp)
   apply ((clarsimp simp: invs'_def valid_state'_def sch_act_sane_def
          | drule(1) ct_not_in_ntfnQueue)+)[1]
  apply (wp get_ntfn_sp')
  done *)

lemma unbindMaybeNotification_ct_not_ksQ:
 "\<lbrace>invs' and ct_in_state' simple' and sch_act_sane
          and (\<lambda>s. ksCurThread s \<notin> set (ksReadyQueues s p))\<rbrace>
   unbindMaybeNotification t
   \<lbrace>\<lambda>rv s. ksCurThread s \<notin> set (ksReadyQueues s p)\<rbrace>"
  apply (simp add: unbindMaybeNotification_def)
  apply (rule hoare_seq_ext[OF _ get_ntfn_sp'])
  apply (case_tac "ntfnBoundTCB ntfn", simp, wp, simp+)
  apply (rule hoare_pre)
    apply wp
    apply (wps setBoundNotification_ct')
    apply (wp sbn_ksQ)
   apply (wps set_ntfn'.ct, wp)
  apply clarsimp
  done

lemma sbn_ct_in_state'[wp]:
  "\<lbrace>ct_in_state' P\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>_. ct_in_state' P\<rbrace>"
  apply (simp add: ct_in_state'_def)
  apply (rule hoare_pre)
   apply (wps setBoundNotification_ct')
  apply (wp sbn_st_tcb', clarsimp)
  done

lemma set_ntfn_ct_in_state'[wp]:
  "\<lbrace>ct_in_state' P\<rbrace> setNotification a ntfn \<lbrace>\<lambda>_. ct_in_state' P\<rbrace>"
  apply (simp add: ct_in_state'_def)
  apply (wp_pre, wps, wp, clarsimp)
  done

lemma unbindMaybeNotification_ct_in_state'[wp]:
  "\<lbrace>ct_in_state' P\<rbrace> unbindMaybeNotification t \<lbrace>\<lambda>_. ct_in_state' P\<rbrace>"
  apply (simp add: unbindMaybeNotification_def)
  apply (wp | wpc | simp)+
  done

lemma setNotification_sch_act_sane:
  "\<lbrace>sch_act_sane\<rbrace> setNotification a ntfn \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  by (wp sch_act_sane_lift)

crunches unbindNotification, unbindMaybeNotification
  for sch_act_sane[wp]: "sch_act_sane"

lemma ct_queues_cross:
  "cross_rel (\<lambda>s. P (cur_thread s) (ready_queues s d p)) (\<lambda>s. P (ksCurThread s) (ksReadyQueues s (d,p)))"
  by (clarsimp simp: state_relation_def ready_queues_relation_def cross_rel_def)

lemma finaliseCapTrue_standin_ct_not_ksQ:
  "\<lbrace>invs' and ct_in_state' simple' and sch_act_sane
          and (\<lambda>s. ksCurThread s \<notin> set (ksReadyQueues s p))\<rbrace>
   finaliseCapTrue_standin cap final
   \<lbrace>\<lambda>rv s. ksCurThread s \<notin> set (ksReadyQueues s p)\<rbrace>"
(*   apply (simp add: finaliseCapTrue_standin_def Let_def)
  apply (safe)
      apply (wp cancelAllIPC_ct_not_ksQ cancelAllSignals_ct_not_ksQ
                hoare_drop_imps unbindMaybeNotification_ct_not_ksQ
             | wpc
             | clarsimp simp: isNotificationCap_def isReplyCap_def split:capability.splits)+ *)
  oops (* FIXME RT: this lemma is probably not needed since we have ct_queues_cross *)

lemma cteDeleteOne_ct_not_ksQ:
  "\<lbrace>invs' and ct_in_state' simple' and sch_act_sane
          and (\<lambda>s. ksCurThread s \<notin> set (ksReadyQueues s p))\<rbrace>
   cteDeleteOne slot
   \<lbrace>\<lambda>rv s. ksCurThread s \<notin> set (ksReadyQueues s p)\<rbrace>"
(*   apply (simp add: cteDeleteOne_def unless_def split_def)
  apply (rule hoare_seq_ext [OF _ getCTE_sp])
  apply (case_tac "\<forall>final. finaliseCap (cteCap cte) final True = fail")
   apply (simp add: finaliseCapTrue_standin_simple_def)
   apply wp
   apply (clarsimp)
  apply (wp emptySlot_cteCaps_of hoare_lift_Pf2 [OF emptySlot_ksRQ emptySlot_ct])
    apply (simp add: cteCaps_of_def)
    apply (wp (once) hoare_drop_imps)
    apply (wp finaliseCapTrue_standin_ct_not_ksQ isFinalCapability_inv)+
  apply (clarsimp)
  done *)
  oops (* FIXME RT: this lemma is probably not needed since we have ct_queues_cross
                    in fact this is not used at all in Refine (perhaps it is needed in
                    CRefine?) *)

end

end
