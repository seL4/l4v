(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Finalise_R
imports
  ArchIpcCancel_R
  InterruptAcc_R
  ArchRetype_R
begin

arch_requalify_facts
  emptySlot_pred_tcb_at' (* can't be in locale assumptions due to free type variable *)

lemmas [wp] = emptySlot_pred_tcb_at'

lemma nullPointer_eq_0_simp[simp]: (* FIXME: move to nullPointer_0_simp in Retype_R *)
  "(0 = nullPointer) = True"
  by (simp add: nullPointer_def)+

lemma no_0_no_0_lhs_trancl [simp]:
  "no_0 m \<Longrightarrow> \<not> m \<turnstile> 0 \<leadsto>\<^sup>+ x"
  by (rule, drule tranclD, clarsimp simp: next_unfold')

lemma no_0_no_0_lhs_rtrancl [simp]:
  "\<lbrakk> no_0 m; x \<noteq> 0 \<rbrakk> \<Longrightarrow> \<not> m \<turnstile> 0 \<leadsto>\<^sup>* x"
  by (clarsimp dest!: rtranclD)

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
   apply (auto simp: n_def modify_map_if initMDBNode_def split: if_split_asm)
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
  using valid ..

lemma valid_badges:
  "valid_badges m"
  using valid ..

lemma to_slot_eq [simp]:
  "m \<turnstile> p \<leadsto> slot = (p = mdbPrev s_node \<and> p \<noteq> 0)"
  apply (rule iffI)
   apply (frule dlist_nextD0, simp)
   apply (clarsimp simp: mdb_prev_def slot mdb_next_unfold)
  apply (clarsimp intro!: prev_slot_next)
  done

lemma n_mdbNext:
  "\<lbrakk> n (mdbNext s_node) = Some (CTE cap node); mdbPrev s_node \<noteq> 0 \<rbrakk> \<Longrightarrow>
  \<exists>node'. m (mdbNext s_node) = Some (CTE cap node') \<and>
          mdbNext node = mdbNext node' \<and>
          mdbPrev node = mdbPrev s_node \<and>
          mdbRevocable node = mdbRevocable node' \<and>
          (mdbFirstBadged node = mdbFirstBadged node' \<or> mdbFirstBadged s_node)"
  apply (clarsimp simp: n_def modify_map_def)
  apply (case_tac z)
  apply clarsimp
  done

lemma n_mdbPrev:
  "\<lbrakk> n (mdbPrev s_node) = Some (CTE cap node); mdbNext s_node \<noteq> 0 \<rbrakk> \<Longrightarrow>
    \<exists>node'. m (mdbPrev s_node) = Some (CTE cap node') \<and>
          mdbNext node = mdbNext s_node \<and>
          mdbPrev node = mdbPrev node' \<and>
          mdbRevocable node = mdbRevocable node' \<and>
          (mdbFirstBadged node = mdbFirstBadged node')"
  apply (clarsimp simp: n_def modify_map_def)
  apply (case_tac z)
  apply clarsimp
  done

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
  apply(clarsimp simp: gen_isCap_simps split: if_split_asm)
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

lemma reply_masters_rvk_fb_m: "reply_masters_rvk_fb m"
  using valid by auto

lemma reply_masters_rvk_fb_n [simp]: "reply_masters_rvk_fb n"
  using reply_masters_rvk_fb_m
  apply (simp add: reply_masters_rvk_fb_def n_def
                   ball_ran_modify_map_eq
                   modify_map_comp[symmetric])
  apply (subst ball_ran_modify_map_eq)
   apply (frule bspec, rule ranI, rule slot)
   apply (simp add: nullMDBNode_def gen_isCap_simps modify_map_def
                    slot)
  apply (subst ball_ran_modify_map_eq)
   apply (clarsimp simp add: modify_map_def)
   apply fastforce
  apply (simp add: ball_ran_modify_map_eq)
  done

end (* mdb_empty *)

text \<open>Properties about empty_slot/emptySlot\<close>

global_interpretation clearUntypedFreeIndex: gen_typ_at_props' _ "clearUntypedFreeIndex slot"
  by typ_at_props'

lemma case_Null_If:
  "(case c of NullCap \<Rightarrow> a | _ \<Rightarrow> b) = (if c = NullCap then a else b)"
  by (case_tac c, simp_all)

lemma updateCap_cte_wp_at_cases:
  "\<lbrace>\<lambda>s. (ptr = ptr' \<longrightarrow> cte_wp_at' (P \<circ> cteCap_update (K cap)) ptr' s) \<and> (ptr \<noteq> ptr' \<longrightarrow> cte_wp_at' P ptr' s)\<rbrace>
     updateCap ptr cap
   \<lbrace>\<lambda>rv. cte_wp_at' P ptr'\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (drule updateCap_stuff)
  apply (clarsimp simp: cte_wp_at_ctes_of modify_map_def)
  done

lemma updateFreeIndex_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_at' p s
        \<and> P (cte_wp_at' (if p = p' then P' \<circ> (cteCap_update (capFreeIndex_update (K idx))) else P')
                        p' s)\<rbrace>
   updateFreeIndex p idx
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p' s)\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def split del: if_split)
  apply (wpsimp wp: updateCap_cte_wp_at' getSlotCap_wp simp: cte_wp_at_ctes_of)
  apply (cases "p' = p"; simp)
  apply (case_tac cte, simp)
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

crunch setInterruptState
  for state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  (simp: state_refs_of'_pspaceI)
crunch setInterruptState
  for state_hyp_refs_of'[wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  (simp: state_hyp_refs_of'_pspaceI)

definition
  "isFinal cap p m \<equiv>
  \<not>isUntypedCap cap \<and>
  (\<forall>p' c. m p' = Some c \<longrightarrow>
          p \<noteq> p' \<longrightarrow> \<not>isUntypedCap c \<longrightarrow>
          \<not> sameObjectAs cap c)"

locale Finalise_R =
  fixes arch_final_matters' :: "arch_capability \<Rightarrow> bool"
  fixes arch_cap_has_cleanup' :: "arch_capability \<Rightarrow> bool"
  assumes arch_postCapDeletion_ksArchState_lift:
    "\<And>P ac. \<lbrakk>\<And>s as. P (s\<lparr>ksArchState := as\<rparr>) = P s\<rbrakk> \<Longrightarrow> Arch.postCapDeletion ac \<lbrace>P\<rbrace>"
  assumes setIRQState_umm[wp]:
    "\<And>st irq P. setIRQState st irq \<lbrace>\<lambda>s. P (underlying_memory (ksMachineState s))\<rbrace>"
  assumes arch_postCapDeletion_corres:
    "\<And>cap cap'.
     acap_relation cap cap'
     \<Longrightarrow> corres dc \<top> \<top> (arch_post_cap_deletion cap) (Arch.postCapDeletion cap')"
  assumes Arch_finaliseCap_typ_at'[wp]:
    "\<And>acap final P T p. Arch.finaliseCap acap final \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>"
  assumes Arch_finaliseCap_aligned'[wp]:
    "\<And>acap final. Arch.finaliseCap acap final \<lbrace>pspace_aligned'\<rbrace>"
  assumes Arch_finaliseCap_distinct'[wp]:
    "\<And>acap final. Arch.finaliseCap acap final \<lbrace>pspace_distinct'\<rbrace>"
  assumes Arch_finaliseCap_it'[wp]:
    "\<And>acap final P. Arch.finaliseCap acap final \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
  assumes prepareThreadDelete_typ_at'[wp]:
    "\<And>t P T p. Arch.prepareThreadDelete t \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>"
  assumes prepareThreadDelete_aligned'[wp]:
    "\<And>t. Arch.prepareThreadDelete t \<lbrace>pspace_aligned'\<rbrace>"
  assumes prepareThreadDelete_distinct'[wp]:
    "\<And>t. Arch.prepareThreadDelete t \<lbrace>pspace_distinct'\<rbrace>"
  assumes prepareThreadDelete_it'[wp]:
    "\<And>t P. Arch.prepareThreadDelete t \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
begin

definition final_matters' :: "capability \<Rightarrow> bool" where
 "final_matters' cap \<equiv> case cap of
    EndpointCap ref bdg s r g gr \<Rightarrow> True
  | NotificationCap ref bdg s r \<Rightarrow> True
  | ThreadCap ref \<Rightarrow> True
  | CNodeCap ref bits gd gs \<Rightarrow> True
  | Zombie ptr zb n \<Rightarrow> True
  | IRQHandlerCap irq \<Rightarrow> True
  | ArchObjectCap acap \<Rightarrow> arch_final_matters' acap
  | _ \<Rightarrow> False"

crunch Arch.postCapDeletion
  for aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and pspace_canonical'[wp]: pspace_canonical'
  and cte_wp_at'[wp]: "cte_wp_at' P p"
  and obj_at'[wp]: "obj_at' P p"
  and ct[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksRQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksRQL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ksRQL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  and nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and valid_objs'[wp]: "valid_objs'"
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and state_hyp_refs_of'[wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  and ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (rule: arch_postCapDeletion_ksArchState_lift)

crunch emptySlot
  for aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and pspace_canonical'[wp]: pspace_canonical'
  (simp: case_Null_If)

crunch postCapDeletion, updateTrackedFreeIndex
  for cte_wp_at'[wp]: "cte_wp_at' P p"

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

crunch postCapDeletion
  for obj_at'[wp]: "obj_at' P p"

crunch emptySlot
  for ct[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksRQ[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksRQL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ksRQL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  and nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

crunch clearUntypedFreeIndex
  for cur_tcb'[wp]: "cur_tcb'"
  and inQ[wp]: "\<lambda>s. P (obj_at' (inQ d p) t s)"
  and tcbDomain[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  and tcbPriority[wp]: "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t"
  (wp: cur_tcb_lift)

lemma emptySlot_sch_act_wf [wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  emptySlot sl opt
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (simp add: emptySlot_def case_Null_If)
     (wp sch_act_wf_lift tcb_in_cur_domain'_lift | wpcw | simp)+

crunch emptySlot
  for state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps)
crunch emptySlot
  for state_hyp_refs_of'[wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  (wp: crunch_wps)

crunch postCapDeletion, clearUntypedFreeIndex
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"

crunch postCapDeletion
  for ko_wp_at'[wp]: "\<lambda>s. P (ko_wp_at' P' p s)"
  (rule: arch_postCapDeletion_ksArchState_lift)

crunch postCapDeletion
  for cteCaps_of[wp]: "\<lambda>s. P (cteCaps_of s)"
  (simp: cteCaps_of_def o_def)


end (* Finalise_R *)

lemma mdb_chunked2D:
  "\<lbrakk> mdb_chunked m; m \<turnstile> p \<leadsto> p'; m \<turnstile> p' \<leadsto> p'';
     m p = Some (CTE cap nd); m p'' = Some (CTE cap'' nd'');
     sameRegionAs cap cap''; p \<noteq> p''; mdb_chunked_arch_assms cap \<rbrakk>
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

(* assume mdb_empty lemmas which require Arch to prove *)
locale mdb_empty_gen = mdb_empty +
  assumes valid_badges_n:
    "valid_badges n"
  assumes parency_n:
    "\<And>p p'. n \<turnstile> p \<rightarrow> p' \<Longrightarrow> m \<turnstile> p \<rightarrow> p' \<and> p \<noteq> slot \<and> p' \<noteq> slot"
  assumes m_parent_of:
    "\<And>p p'. \<lbrakk> m \<turnstile> p parentOf p'; p \<noteq> slot; p' \<noteq> slot; p\<noteq>p'; p'\<noteq>mdbNext s_node \<rbrakk> \<Longrightarrow> n \<turnstile> p parentOf p'"
  assumes m_parent_of_next:
    "\<And>p. \<lbrakk> m \<turnstile> p parentOf mdbNext s_node; m \<turnstile> p parentOf slot; p \<noteq> slot; p\<noteq>mdbNext s_node \<rbrakk>
         \<Longrightarrow> n \<turnstile> p parentOf mdbNext s_node"
begin

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

lemma vmdb_n: "valid_mdb_ctes n"
  by (simp add: valid_mdb_ctes_def valid_dlist_n
                no_0_n mdb_chain_0_n valid_badges_n
                caps_contained_n mdb_chunked_n
                untyped_mdb_n untyped_inc_n
                nullcaps_n ut_rev_n class_links_n)

end (* mdb_empty_gen *)

locale Arch_mdb_empty = mdb_empty + Arch

lemma if_live_then_nonz_cap'_def2:
  "if_live_then_nonz_cap' =
   (\<lambda>s. \<forall>ptr. ko_wp_at' live' ptr s \<longrightarrow>
              (\<exists>p zr. (option_map zobj_refs' o cteCaps_of s) p = Some zr \<and> ptr \<in> zr))"
  by (fastforce simp: if_live_then_nonz_cap'_def ex_nonz_cap_to'_def cte_wp_at_ctes_of
                      cteCaps_of_def)

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

primrec
  threadCapRefs :: "capability \<Rightarrow> machine_word set"
where
  "threadCapRefs (ThreadCap r)                  = {r}"
| "threadCapRefs (ReplyCap t m x)               = {}"
| "threadCapRefs NullCap                        = {}"
| "threadCapRefs (UntypedCap d r n i)           = {}"
| "threadCapRefs (EndpointCap r badge x y z t)  = {}"
| "threadCapRefs (NotificationCap r badge x y)  = {}"
| "threadCapRefs (CNodeCap r b g gsz)           = {}"
| "threadCapRefs (Zombie r b n)                 = {}"
| "threadCapRefs (ArchObjectCap ac)             = {}"
| "threadCapRefs (IRQHandlerCap irq)            = {}"
| "threadCapRefs (IRQControlCap)                = {}"
| "threadCapRefs (DomainCap)                    = {}"

lemma not_FinalE:
  "\<lbrakk> \<not> isFinal cap sl cps; isUntypedCap cap \<Longrightarrow> P;
     \<And>p c. \<lbrakk> cps p = Some c; p \<noteq> sl; \<not> isUntypedCap c; sameObjectAs cap c \<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (fastforce simp: isFinal_def)

definition
 "removeable' sl \<equiv> \<lambda>s cap.
    (\<exists>p. p \<noteq> sl \<and> cte_wp_at' (\<lambda>cte. capMasterCap (cteCap cte) = capMasterCap cap) p s)
    \<or> ((\<forall>p \<in> cte_refs' cap (irq_node' s). p \<noteq> sl \<longrightarrow> cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) p s)
         \<and> (\<forall>p \<in> zobj_refs' cap. ko_wp_at' (Not \<circ> live') p s))"

crunch clearUntypedFreeIndex
  for ko_at_live[wp]: "\<lambda>s. P (ko_wp_at' live' ptr s)"

lemma setIRQState_irq_node'[wp]:
  "\<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> setIRQState state irq \<lbrace>\<lambda>_ s. P (irq_node' s)\<rbrace>"
  apply (simp add: setIRQState_def setInterruptState_def getInterruptState_def)
  apply wp
  apply simp
  done

lemmas ctes_of_valid'[elim] = ctes_of_valid_cap''[where r=cte for cte]

crunch setInterruptState
  for valid_idle'[wp]: "valid_idle'"
  (simp: valid_idle'_def)

crunch deletedIRQHandler, getSlotCap, clearUntypedFreeIndex, updateMDB, getCTE, updateCap
  for ksArch[wp]: "\<lambda>s. P (ksArchState s)"

context Finalise_R begin

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

crunch emptySlot
  for irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  (rule: arch_postCapDeletion_ksArchState_lift)

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

crunch emptySlot
  for valid_idle'[wp]: "valid_idle'"
  and ksIdle[wp]: "\<lambda>s. P (ksIdleThread s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (rule: arch_postCapDeletion_ksArchState_lift)

lemma emptySlot_cteCaps_of:
  "\<lbrace>\<lambda>s. P ((cteCaps_of s)(p \<mapsto> NullCap))\<rbrace>
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

crunch deletedIRQHandler
  for cteCaps_of[wp]: "\<lambda>s. P (cteCaps_of s)"

definition cap_has_cleanup' :: "capability \<Rightarrow> bool" where
  "cap_has_cleanup' cap \<equiv> case cap of
     IRQHandlerCap _ \<Rightarrow> True
   | ArchObjectCap acap \<Rightarrow> arch_cap_has_cleanup' acap
   | _ \<Rightarrow> False"

lemmas cap_has_cleanup'_simps[simp] = cap_has_cleanup'_def[split_simps capability.split]

end (* Finalise_R *)

locale Finalise_R_2 = Finalise_R +
  assumes Arch_postCapDeletion_valid_global_refs[wp]:
    "\<And>t. Arch.postCapDeletion t \<lbrace>valid_global_refs'\<rbrace>"
  assumes Arch_postCapDeletion_valid_arch_state'[wp]:
    "\<And>t. Arch.postCapDeletion t \<lbrace>valid_arch_state'\<rbrace>"
  assumes clearUntypedFreeIndex_valid_global_refs[wp]:
    "\<And>irq. clearUntypedFreeIndex irq \<lbrace>valid_global_refs'\<rbrace>"
  assumes deletedIRQHandler_valid_global_refs[wp]:
    "\<And>irq. deletedIRQHandler irq \<lbrace>valid_global_refs'\<rbrace>"
  assumes Arch_finaliseCap_irq_node'[wp]:
    "\<And>acap final P. Arch.finaliseCap acap final \<lbrace>\<lambda>s. P (Invariants_H.irq_node' s)\<rbrace>"
  assumes prepareThreadDelete_irq_node'[wp]:
    "\<And>t P. prepareThreadDelete t \<lbrace>\<lambda>s. P (Invariants_H.irq_node' s)\<rbrace>"
  assumes prepareThreadDelete_cte_wp_at'[wp]:
    "\<And>t P p. prepareThreadDelete t \<lbrace>cte_wp_at' P p\<rbrace>"
  assumes arch_finaliseCap_cte_wp_at[wp]:
    "\<And>cap fin P p. Arch.finaliseCap cap fin \<lbrace>cte_wp_at' P p\<rbrace>"
  assumes notFinal_prev_or_next:
    "\<And>cap s x node.
     \<lbrakk> \<not> isFinal cap x (cteCaps_of s); mdb_chunked (ctes_of s); valid_dlist (ctes_of s);
       no_0 (ctes_of s); ctes_of s x = Some (CTE cap node); final_matters' cap \<rbrakk>
     \<Longrightarrow> (\<exists>cap' node'. ctes_of s (mdbPrev node) = Some (CTE cap' node') \<and> sameObjectAs cap cap')
        \<or> (\<exists>cap' node'. ctes_of s (mdbNext node) = Some (CTE cap' node') \<and> sameObjectAs cap cap')"
  assumes sameObjectAs_not_Untyped:
    "\<And>cap cap'. \<lbrakk> global.sameObjectAs cap cap'; \<not> isUntypedCap cap \<rbrakk> \<Longrightarrow> \<not> isUntypedCap cap'"
  assumes sameObjectAs_not_Untyped':
    "\<And>cap cap'.
     \<lbrakk> global.sameObjectAs cap cap'; \<not> isUntypedCap cap' \<rbrakk> \<Longrightarrow> global.sameObjectAs cap' cap"
  assumes arch_finaliseCap_invs[wp]:
    "\<And>cap fin.
     \<lbrace>invs' and valid_cap' (ArchObjectCap cap)\<rbrace> Arch.finaliseCap cap fin \<lbrace>\<lambda>rv. invs'\<rbrace>"
  assumes prepareThreadDelete_invs[wp]:
    "prepareThreadDelete t \<lbrace>invs'\<rbrace>"
  assumes prepareThreadDelete_valid_cap'[wp]:
    "\<And>cap. prepareThreadDelete t \<lbrace>valid_cap' cap\<rbrace>"
  assumes finaliseCap_valid_cap[wp]:
    "\<And>cap final. \<lbrace>\<lambda>_. True\<rbrace> Arch.finaliseCap cap final \<lbrace>\<lambda>rv. valid_cap' (fst rv)\<rbrace>"
  assumes not_Final_removeable:
    "\<And>cap sl s. \<not> isFinal cap sl (cteCaps_of s) \<Longrightarrow> removeable' sl s cap"
  assumes arch_finaliseCap_cases[wp]:
  "\<lbrace>\<top>\<rbrace> Arch.finaliseCap v0 final
   \<lbrace>\<lambda>rv s. fst rv = capability.NullCap \<and>
           (snd rv \<noteq> capability.NullCap
            \<longrightarrow> final \<and> arch_cap_has_cleanup' v0 \<and> snd rv = capability.ArchObjectCap v0)\<rbrace>"
  assumes isFinal_no_descendants:
    "\<And>cap sl s n.
     \<lbrakk> isFinal cap sl (cteCaps_of s); ctes_of s sl = Some (CTE cap n);
       valid_mdb' s; final_matters' cap \<rbrakk>
    \<Longrightarrow> descendants_of' sl (ctes_of s) = {}"
  (* This is the expanded form of mdb_insert.vmdb_n which needs Arch to prove (via mdb_insert_gen).
     The original form contracts this significantly via internal locale variables from mdb_empty. *)
  assumes mdb_empty_vmdb_n:
    "\<And>m slot s_cap s_node.
     mdb_empty m slot s_cap s_node \<Longrightarrow>
     valid_mdb_ctes
      (modify_map
        (modify_map
          (modify_map
            (modify_map m (mdbPrev s_node) (cteMDBNode_update (mdbNext_update (\<lambda>_. mdbNext s_node))))
            (mdbNext s_node)
            (cteMDBNode_update
              (\<lambda>mdb. mdbFirstBadged_update (\<lambda>_. mdbFirstBadged mdb \<or> mdbFirstBadged s_node)
                      (mdbPrev_update (\<lambda>_. mdbPrev s_node) mdb))))
          slot (cteCap_update (\<lambda>_. capability.NullCap)))
        slot (cteMDBNode_update (const nullMDBNode)))"
  assumes mdb_empty_descendants:
    "\<And>m slot s_cap s_node p.
     mdb_empty m slot s_cap s_node \<Longrightarrow>
     descendants_of' p
      (modify_map
        (modify_map
          (modify_map
            (modify_map m (mdbPrev s_node) (cteMDBNode_update (mdbNext_update (\<lambda>_. mdbNext s_node))))
            (mdbNext s_node)
            (cteMDBNode_update
              (\<lambda>mdb. mdbFirstBadged_update (\<lambda>_. mdbFirstBadged mdb \<or> mdbFirstBadged s_node)
                      (mdbPrev_update (\<lambda>_. mdbPrev s_node) mdb))))
          slot (cteCap_update (\<lambda>_. capability.NullCap)))
        slot (cteMDBNode_update (const nullMDBNode))) =
     (if p = slot then {} else descendants_of' p m - {slot})"
begin

crunch global.postCapDeletion
  for valid_global_refs[wp]: "valid_global_refs'"

lemma emptySlot_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs' and cte_at' sl\<rbrace> emptySlot sl opt \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (clarsimp simp: emptySlot_def)
  apply (wpsimp wp: getCTE_wp hoare_drop_imps hoare_vcg_ex_lift simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: valid_global_refs'_def)
  apply (frule(1) cte_at_valid_cap_sizes_0)
  apply (clarsimp simp: valid_refs'_cteCaps valid_cap_sizes_cteCaps ball_ran_eq)
  done

lemma finaliseCap_cases[wp]:
  "\<lbrace>\<top>\<rbrace>
   finaliseCap cap final flag
   \<lbrace>\<lambda>rv s. fst rv = NullCap \<and> (snd rv \<noteq> NullCap \<longrightarrow> final \<and> cap_has_cleanup' cap \<and> snd rv = cap)
           \<or> isZombie (fst rv) \<and> final \<and> \<not> flag \<and> snd rv = NullCap
             \<and> capUntypedPtr (fst rv) = capUntypedPtr cap
             \<and> (isThreadCap cap \<or> isCNodeCap cap \<or> isZombie cap)\<rbrace>"
  apply (simp add: finaliseCap_def Let_def getThreadCSpaceRoot
             cong: if_cong split del: if_split)
  apply (wpsimp simp: gen_isCap_simps valid_NullCap)
  apply (auto simp add: gen_isCap_simps cap_has_cleanup'_def)
  done

end (* Finalise_R_2 *)

lemmas doMachineOp_irq_handlers[wp]
    = valid_irq_handlers_lift'' [OF doMachineOp_ctes doMachineOp_ksInterruptState]

lemma deletedIRQHandler_irq_handlers'[wp]:
  "\<lbrace>\<lambda>s. valid_irq_handlers' s \<and> (IRQHandlerCap irq \<notin> ran (cteCaps_of s))\<rbrace>
       deletedIRQHandler irq
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: deletedIRQHandler_def setIRQState_def setInterruptState_def getInterruptState_def)
  apply wp
  apply (clarsimp simp: valid_irq_handlers'_def irq_issued'_def ran_def cteCaps_of_def)
  done

crunch clearUntypedFreeIndex
  for ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"

lemma deletedIRQHandler_irqs_masked'[wp]:
  "\<lbrace>irqs_masked'\<rbrace> deletedIRQHandler irq \<lbrace>\<lambda>_. irqs_masked'\<rbrace>"
  apply (simp add: deletedIRQHandler_def setIRQState_def getInterruptState_def setInterruptState_def)
  apply (wp dmo_maskInterrupt)
  apply (simp add: irqs_masked'_def)
  done

lemma untypedZeroRange_modify_map_isUntypedCap:
  "m sl = Some v \<Longrightarrow> \<not> isUntypedCap v \<Longrightarrow> \<not> isUntypedCap (f v)
   \<Longrightarrow> (untypedZeroRange \<circ>\<^sub>m modify_map m sl f) = (untypedZeroRange \<circ>\<^sub>m m)"
  by (simp add: modify_map_def map_comp_def fun_eq_iff untypedZeroRange_def)

context Finalise_R begin

lemma postCapDeletion_irq_handlers'[wp]:
  "\<lbrace>\<lambda>s. valid_irq_handlers' s \<and> (cap \<noteq> NullCap \<longrightarrow> cap \<notin> ran (cteCaps_of s))\<rbrace>
   postCapDeletion cap
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  by (wpsimp simp: Retype_H.postCapDeletion_def | rule arch_postCapDeletion_ksArchState_lift)+

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

crunch emptySlot
  for irq_states'[wp]: valid_irq_states'
  and no_0_obj'[wp]: no_0_obj'
  and irqs_masked'[wp]: "irqs_masked'"
  (wp: crunch_wps rule: arch_postCapDeletion_ksArchState_lift)

lemma deletedIRQHandler_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> deletedIRQHandler irq \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF deletedIRQHandler_nosch])
  apply (rule hoare_weaken_pre)
   apply (wps deletedIRQHandler_ct)
   apply (simp add: deletedIRQHandler_def setIRQState_def)
   apply (wp)
  apply (simp add: comp_def)
  done

crunch emptySlot
  for umm[wp]: "\<lambda>s. P (underlying_memory (ksMachineState s))"
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ct_not_inQ[wp]: "ct_not_inQ"
  and tcbDomain[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  (wp: setIRQState_umm rule: arch_postCapDeletion_ksArchState_lift)

lemma emptySlot_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> emptySlot slot irq \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  by (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
     (wp hoare_vcg_all_lift hoare_vcg_disj_lift)

lemma emptySlot_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> emptySlot sl opt \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift2 tcb_in_cur_domain'_lift | simp)+

crunch postCapDeletion
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps simp: crunch_simps rule: arch_postCapDeletion_ksArchState_lift)

lemma emptySlot_untyped_ranges[wp]:
  "\<lbrace>untyped_ranges_zero' and valid_objs' and valid_mdb'\<rbrace>
     emptySlot sl opt \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (simp add: emptySlot_def case_Null_If)
  apply (rule hoare_pre)
   apply (rule bind_wp)
    apply (rule untyped_ranges_zero_lift)
     apply (wp getCTE_cteCap_wp clearUntypedFreeIndex_cteCaps_of
       | wpc | simp add: clearUntypedFreeIndex_def updateTrackedFreeIndex_def
                         getSlotCap_def
                  split: option.split)+
  apply (clarsimp simp: modify_map_comp[symmetric] modify_map_same)
  apply (case_tac "\<not> isUntypedCap (the (cteCaps_of s sl))")
   apply (case_tac "the (cteCaps_of s sl)",
     simp_all add: untyped_ranges_zero_inv_def
                   untypedZeroRange_modify_map_isUntypedCap gen_isCap_simps)[1]
  apply (clarsimp simp: gen_isCap_simps untypedZeroRange_def modify_map_def)
  apply (strengthen untyped_ranges_zero_fun_upd[mk_strg I E])
  apply simp
  apply (simp add: untypedZeroRange_def gen_isCap_simps)
  done

crunch emptySlot
  for valid_bitmaps[wp]: valid_bitmaps
  and tcbQueued_opt_pred[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"
  and valid_sched_pointers[wp]: valid_sched_pointers
  and sched_projs[wp]: "\<lambda>s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)"
  and ksDomScheduleStart[wp]: "\<lambda>s. P (ksDomScheduleStart s)"
  and pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  and valid_objs'[wp]: "valid_objs'"
  (wp: valid_bitmaps_lift rule: arch_postCapDeletion_ksArchState_lift)

end (* Finalise_R *)

context Finalise_R_2 begin

crunch emptySlot
  for valid_arch'[wp]: valid_arch_state'
  (wp: crunch_wps)

lemma emptySlot_mdb[wp]:
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
  apply (erule mdb_empty_vmdb_n[unfolded const_def])
  done

end (* Finalise_R_2 *)

lemma deletedIRQHandler_corres:
  "corres dc \<top> \<top>
    (deleted_irq_handler irq)
    (deletedIRQHandler irq)"
  apply (simp add: deleted_irq_handler_def deletedIRQHandler_def)
  apply (rule setIRQState_corres)
  apply (simp add: irq_state_relation_def)
  done

lemma set_cap_trans_state:
  "((),s') \<in> fst (set_cap c p s) \<Longrightarrow> ((),trans_state f s') \<in> fst (set_cap c p (trans_state f s))"
  apply (cases p)
  apply (clarsimp simp add: set_cap_def in_monad set_object_def get_object_def)
  apply (case_tac y)
      apply (auto simp add: in_monad set_object_def well_formed_cnode_n_def split: if_split_asm)
  done

lemma clearUntypedFreeIndex_noop_corres:
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

context Finalise_R begin

lemma postCapDeletion_corres:
  "cap_relation cap cap' \<Longrightarrow> corres dc \<top> \<top> (post_cap_deletion cap) (postCapDeletion cap')"
  apply (cases cap; clarsimp simp: post_cap_deletion_def Retype_H.postCapDeletion_def)
   apply (corresKsimp corres: deletedIRQHandler_corres)
  by (corresKsimp corres: arch_postCapDeletion_corres)

lemma clearUntypedFreeIndex_valid_pspace'[wp]:
  "\<lbrace>valid_pspace'\<rbrace> clearUntypedFreeIndex slot \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp | simp add: valid_mdb'_def)+
  done

end (* Finalise_R *)

lemma (in Finalise_R_2) emptySlot_corres:
  "cap_relation info info' \<Longrightarrow> corres dc (einvs and cte_at slot) (invs' and cte_at' (cte_map slot))
             (empty_slot slot info) (emptySlot (cte_map slot) info')"
  unfolding emptySlot_def empty_slot_def
  apply (simp add: case_Null_If)
  apply (rule corres_guard_imp)
    apply (rule corres_split_noop_rhs[OF clearUntypedFreeIndex_noop_corres])
     apply (rule_tac R="\<lambda>cap. einvs and cte_wp_at ((=) cap) slot" and
                     R'="\<lambda>cte. valid_pspace' and cte_wp_at' ((=) cte) (cte_map slot)" in
                     corres_split[OF get_cap_corres])
       defer
       apply (wp get_cap_wp getCTE_wp')+
     apply (simp add: cte_wp_at_ctes_of)
     apply (wp hoare_vcg_imp_lift' clearUntypedFreeIndex_valid_pspace')
    apply fastforce
   apply (fastforce simp: cte_wp_at_ctes_of)
  apply simp
  apply (rule conjI, clarsimp)
   defer
  apply clarsimp
  apply (rule conjI, clarsimp)
  apply clarsimp
  apply (simp only: bind_assoc[symmetric])
  apply (rule corres_underlying_split[where r'=dc, OF _ postCapDeletion_corres])
    defer
    apply wpsimp+
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp hoare_weak_lift_imp)
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
  apply (drule updateMDB_the_lot, fastforce simp: pspace_relation_def, fastforce, fastforce)
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def
                         valid_mdb'_def valid_mdb_ctes_def)
  apply (elim conjE)
  apply (drule (4) updateMDB_the_lot, elim conjE)
  apply clarsimp
  apply (drule_tac s'=s''a and c=cap.NullCap in set_cap_not_quite_corres)
                      subgoal by simp
                     subgoal by simp
                    subgoal by simp
                   subgoal by simp
                  subgoal by fastforce
                 subgoal by fastforce
                subgoal by fastforce
               subgoal by fastforce
              subgoal by fastforce
             apply fastforce
            subgoal by fastforce
           subgoal by fastforce
          subgoal by fastforce
         apply (erule cte_wp_at_weakenE, rule TrueI)
        apply assumption
       subgoal by simp
      subgoal by simp
     subgoal by simp
    subgoal by simp
   apply (rule refl)
  apply clarsimp
  apply (drule updateCap_stuff, elim conjE, erule (1) impE)
  apply clarsimp
  apply (drule updateMDB_the_lot, force simp: pspace_relation_def, assumption+, simp)
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
  apply (prop_tac "ghost_relation_wrapper t b")
   apply (erule (1) ghost_relation_wrapper_same_abs_set_cap; rule refl)
  apply (clarsimp simp: set_cap_a_type_inv)
  apply (simp add: pspace_relation_def)
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
  apply (subst mdb_empty_descendants, assumption)
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
   apply (rule hoare_post_imp[where Q'="\<lambda>s. P"], simp)
   apply wp
  apply simp
  done

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

text \<open>Facts about finalise_cap/finaliseCap and
        cap_delete_one/cteDelete in no particular order\<close>

definition
  finaliseCapTrue_standin_simple_def:
  "finaliseCapTrue_standin cap fin \<equiv> finaliseCap cap fin True"

lemmas finaliseCapTrue_standin_def
    = finaliseCapTrue_standin_simple_def[unfolded finaliseCap_def, @\<open>simp cong: if_cong\<close>]

lemmas cteDeleteOne_def' = eq_reflection[OF cteDeleteOne_def]
lemmas cteDeleteOne_def = cteDeleteOne_def'[folded finaliseCapTrue_standin_simple_def]

crunch unbindNotification, finaliseCapTrue_standin
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  (simp: crunch_simps wp: crunch_wps getObject_inv loadObject_default_inv)

crunch cteDeleteOne, suspend
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps getObject_inv loadObject_default_inv
   simp: crunch_simps unless_def o_def
   ignore_del: setObject)

global_interpretation cancelIPC: gen_typ_at_props' _ "cancelIPC tptr" by typ_at_props'
global_interpretation cancelAllIPC: gen_typ_at_props' _ "cancelAllIPC epptr" by typ_at_props'
global_interpretation cancelAllSignals: gen_typ_at_props' _ "cancelAllSignals ntfnPtr" by typ_at_props'
global_interpretation suspend: gen_typ_at_props' _ "suspend target" by typ_at_props'

context Finalise_R begin

crunch finaliseCap
  for aligned'[wp]: pspace_aligned'
  and distinct'[wp]: pspace_distinct'
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps hoare_vcg_all_lift simp: crunch_simps)

sublocale finaliseCap: gen_typ_at_props' _ "finaliseCap cap final x"
  by typ_at_props'

sublocale unbindNotification: gen_typ_at_props' _ "unbindNotification tcb"
  by typ_at_props'

end (* Finalise_R *)

lemma ntfn_q_refs_of'_mult:
  "ntfn_q_refs_of' ntfn = (case ntfn of Structures_H.WaitingNtfn q \<Rightarrow> set q | _ \<Rightarrow> {}) \<times> {NTFNSignal}"
  by (cases ntfn, simp_all)

lemma tcb_st_not_Bound:
  "(p, NTFNBound) \<notin> tcb_st_refs_of' ts"
  "(p, TCBBound) \<notin> tcb_st_refs_of' ts"
  by (auto simp: tcb_st_refs_of'_def split: Structures_H.thread_state.split)

crunch setBoundNotification
  for valid_bitmaps[wp]: valid_bitmaps
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and tcbQueued[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"
  and valid_sched_pointers[wp]: valid_sched_pointers
  (wp: valid_bitmaps_lift)

lemma unbindNotification_invs[wp]:
  "\<lbrace>invs'\<rbrace> unbindNotification tcb \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: unbindNotification_def invs'_def valid_state'_def)
  apply (rule bind_wp[OF _ gbn_sp'])
  apply (case_tac ntfnPtr, clarsimp, wp, clarsimp)
  apply clarsimp
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (wpsimp wp: sbn'_valid_pspace'_inv sbn_sch_act' valid_irq_node_lift valid_dom_schedule'_lift
                    irqs_masked_lift setBoundNotification_ct_not_inQ sym_heap_sched_pointers_lift
                    untyped_ranges_zero_lift
                simp: cteCaps_of_def o_def  doUnbindNotification_def)
  apply (frule obj_at_valid_objs', clarsimp+)
  apply (clarsimp simp: pred_tcb_at' conj_comms)
  apply (frule bound_tcb_ex_cap'', clarsimp+)
  apply (frule(1) sym_refs_bound_tcb_atD')
  apply (frule(1) sym_refs_obj_atD')
  apply (clarsimp simp: refs_of_rev')
  apply normalise_obj_at'
  apply (subst delta_sym_refs, assumption)
    apply (auto split: if_split_asm)[1]
   (* FIXME: weak elimination rule warning for no_0_obj_at' despite supply *)
   supply no_0_obj_at'[rule del] (* avoid weak elim rule warning *)
   apply (auto simp: tcb_st_not_Bound ntfn_q_refs_of'_mult split: if_split_asm)[1]
  apply (frule obj_at_valid_objs', clarsimp+)
  apply (simp add: valid_ntfn'_def valid_obj'_def live'_def
            split: ntfn.splits)
  apply (erule if_live_then_nonz_capE')
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def live'_def)
  done

lemma ntfn_bound_tcb_at':
  "\<lbrakk>sym_refs (state_refs_of' s); valid_objs' s; ko_at' ntfn ntfnptr s;
    ntfnBoundTCB ntfn = Some tcbptr; P (Some ntfnptr)\<rbrakk>
  \<Longrightarrow> bound_tcb_at' P tcbptr s"
  apply (drule_tac x=ntfnptr in sym_refsD[rotated])
   apply (clarsimp simp: obj_at'_def)
   apply (fastforce simp: state_refs_of'_def)
  apply (auto simp: pred_tcb_at'_def obj_at'_def valid_obj'_def valid_ntfn'_def
                    state_refs_of'_def refs_of_rev'
          simp del: refs_of_simps
             split: option.splits if_split_asm)
  done

lemma unbindMaybeNotification_invs[wp]:
  "\<lbrace>invs'\<rbrace> unbindMaybeNotification ntfnptr \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply if_cong[cong]
  apply (simp add: unbindMaybeNotification_def invs'_def valid_state'_def)
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
   apply (wp sbn'_valid_pspace'_inv sbn_sch_act' sym_heap_sched_pointers_lift valid_irq_node_lift
             irqs_masked_lift valid_dom_schedule'_lift setBoundNotification_ct_not_inQ
             untyped_ranges_zero_lift
             | wpc | clarsimp simp: cteCaps_of_def o_def doUnbindNotification_def)+
  apply safe[1]
           defer 3
           defer 7
           apply (fold_subgoals (prefix))[8]
           subgoal premises prems using prems
              by (auto simp: pred_tcb_at' valid_pspace'_def valid_obj'_def valid_ntfn'_def
                             ko_wp_at'_def live'_def
                      elim!: obj_atE' if_live_then_nonz_capE'
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
  done

(* Ugh, required to be able to split out the abstract invs *)
lemma finaliseCap_True_invs[wp]:
  "\<lbrace>invs'\<rbrace> finaliseCap cap final True \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: finaliseCap_def Let_def)
  apply safe
    apply (wp irqs_masked_lift| simp | wpc)+
  done

lemma setObject_tcb_ksInterruptState[wp]:
  "setObject t (v :: tcb) \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wpsimp simp: setObject_def wp: updateObject_default_inv)

lemma setObject_tcb_gsMaxObjectSize[wp]:
  "setObject t (v :: tcb) \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace>"
  by (wpsimp simp: setObject_def wp: updateObject_default_inv)

lemma setObject_tcb_gsUntypedZeroRanges[wp]:
  "setObject ptr (tcb::tcb) \<lbrace>\<lambda>s. P (gsUntypedZeroRanges s)\<rbrace>"
  by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_tcb_tcbs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((tcbs_of' s) (t \<mapsto> tcb))\<rbrace>
   setObject t tcb
   \<lbrace>\<lambda>_ s. P (tcbs_of' s)\<rbrace>"
  unfolding setObject_def
  apply (wpsimp simp: updateObject_default_def)
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (clarsimp simp: opt_map_def split: option.splits)
  done

lemma when_assert_eq:
  "(when P $ haskell_fail xs) = assert (\<not>P)"
  by (simp add: assert_def when_def)

lemma isZombie_Null:
  "\<not> isZombie NullCap"
  by (simp add: gen_isCap_simps)

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

crunch finaliseCapTrue_standin, unbindNotification
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps getObject_inv loadObject_default_inv simp: crunch_simps)

lemma sameObjectAs_Null[simp]:
  "global.sameObjectAs c capability.NullCap = False"
  "global.sameObjectAs capability.NullCap c = False"
  by (clarsimp simp add: sameObjectAs_def split: capability.splits)+

context Finalise_R begin

lemma cteDeleteOne_cteCaps_of:
  "\<lbrace>\<lambda>s. (cte_wp_at' (\<lambda>cte. \<exists>final. finaliseCap (cteCap cte) final True \<noteq> fail) p s \<longrightarrow>
          P ((cteCaps_of s)(p \<mapsto> NullCap)))\<rbrace>
     cteDeleteOne p
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def split_def)
  apply (rule bind_wp [OF _ getCTE_sp])
  apply (case_tac "\<forall>final. finaliseCap (cteCap cte) final True = fail")
   apply (simp add: finaliseCapTrue_standin_simple_def)
   apply wp
   apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def
                         finaliseCap_def gen_isCap_simps)
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
  "cteDeleteOne p \<lbrace>\<lambda>s. isFinal cap slot (cteCaps_of s)\<rbrace>"
  by (wpsimp wp: cteDeleteOne_cteCaps_of simp: isFinal_def)

end (* Finalise_R *)

lemmas setEndpoint_cteCaps_of[wp] = cteCaps_of_ctes_of_lift [OF set_ep_ctes_of]
lemmas setNotification_cteCaps_of[wp] = cteCaps_of_ctes_of_lift [OF set_ntfn_ctes_of]
lemmas threadSet_cteCaps_of = cteCaps_of_ctes_of_lift [OF threadSet_ctes_of]

lemma isThreadCap_threadCapRefs_tcbptr:
  "isThreadCap cap \<Longrightarrow> threadCapRefs cap = {capTCBPtr cap}"
  by (clarsimp simp: gen_isCap_simps)

lemma isArchObjectCap_Cap_capCap:
  "isArchObjectCap cap \<Longrightarrow> ArchObjectCap (capCap cap) = cap"
  by (clarsimp simp: gen_isCap_simps)

context Finalise_R_2 begin

crunch suspend
  for isFinal: "\<lambda>s. isFinal cap slot (cteCaps_of s)"
  (ignore: threadSet
       wp: threadSet_cteCaps_of crunch_wps
     simp: crunch_simps unless_def o_def)

crunch finaliseCap
  for irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  (wp: crunch_wps
   simp: crunch_simps)

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
  apply (clarsimp simp: cteSizeBits_cte_level_bits shiftl_t2n
                  split: option.split_asm)
  done

lemma deletingIRQHandler_final:
  "\<lbrace>\<lambda>s. isFinal cap slot (cteCaps_of s)
             \<and> (\<forall>final. finaliseCap cap final True = fail)\<rbrace>
     deletingIRQHandler irq
   \<lbrace>\<lambda>rv s. isFinal cap slot (cteCaps_of s)\<rbrace>"
  apply (simp add: deletingIRQHandler_def isFinal_def getIRQSlot_def
                   getInterruptState_def locateSlot_conv getSlotCap_def)
  apply (wpsimp wp: cteDeleteOne_cteCaps_of getCTE_wp')
  done

crunch updateRestartPC, cancelIPC
  for valid_sched_pointers[wp]: valid_sched_pointers
  (simp: crunch_simps wp: crunch_wps)

end (* Finalise_R_2 *)

lemma unbindNotification_valid_objs'_helper:
  "valid_tcb' tcb s \<longrightarrow> valid_tcb' (tcbBoundNotification_update (\<lambda>_. None) tcb) s "
  by (clarsimp simp: valid_bound_ntfn'_def valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs
                  split: option.splits ntfn.splits)

lemma unbindNotification_valid_objs'_helper':
  "valid_ntfn' tcb s \<longrightarrow> valid_ntfn' (ntfnBoundTCB_update (\<lambda>_. None) tcb) s "
  by (clarsimp simp: valid_bound_tcb'_def valid_ntfn'_def
                  split: option.splits ntfn.splits)

lemmas setNotification_valid_tcb' = typ_at'_valid_tcb'_lift [OF setNotification_typ_at']

lemma unbindNotification_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace>
     unbindNotification t
   \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: unbindNotification_def)
  apply (rule hoare_pre)
  apply (wpsimp wp: threadSet_valid_objs' gbn_wp' set_ntfn_valid_objs' hoare_vcg_all_lift
                    setNotification_valid_tcb' getNotification_wp
                simp: setBoundNotification_def unbindNotification_valid_objs'_helper
                      doUnbindNotification_def)
  apply (clarsimp elim!: obj_atE')
  apply (rule valid_objsE', assumption+)
  apply (clarsimp simp: valid_obj'_def unbindNotification_valid_objs'_helper')
  done

lemma unbindMaybeNotification_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace>
     unbindMaybeNotification t
   \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: unbindMaybeNotification_def)
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
  apply (wpsimp wp: threadSet_valid_objs' gbn_wp' set_ntfn_valid_objs' hoare_vcg_all_lift
                    setNotification_valid_tcb' getNotification_wp
                simp: setBoundNotification_def unbindNotification_valid_objs'_helper
                      doUnbindNotification_def)+
  apply (clarsimp elim!: obj_atE')
  apply (rule valid_objsE', assumption+)
  apply (clarsimp simp: valid_obj'_def unbindNotification_valid_objs'_helper')
  done

lemma unbindMaybeNotification_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace> unbindMaybeNotification t
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: unbindMaybeNotification_def)
  apply (rule hoare_pre)
  apply (wpsimp wp: sbn_sch_act' simp: doUnbindNotification_def)+
  done

lemma valid_cong:
  "\<lbrakk> \<And>s. P s = P' s; \<And>s. P' s \<Longrightarrow> f s = f' s;
        \<And>rv s' s. \<lbrakk> (rv, s') \<in> fst (f' s); P' s \<rbrakk> \<Longrightarrow> Q rv s' = Q' rv s' \<rbrakk>
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> = \<lbrace>P'\<rbrace> f' \<lbrace>Q'\<rbrace>"
  by (clarsimp simp add: valid_def, blast)

lemma sym_refs_ntfn_bound_eq: "sym_refs (state_refs_of' s)
    \<Longrightarrow> obj_at' (\<lambda>ntfn. ntfnBoundTCB ntfn = Some t) x s
    = bound_tcb_at' (\<lambda>st. st = Some x) t s"
  apply (rule iffI)
   apply (drule (1) sym_refs_obj_atD')
   apply (clarsimp simp: pred_tcb_at'_def obj_at'_def ko_wp_at'_def refs_of_rev')
  apply (drule(1) sym_refs_bound_tcb_atD')
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def refs_of_rev')
  done

lemma unbindMaybeNotification_obj_at'_bound:
  "\<lbrace>\<top>\<rbrace>
   unbindMaybeNotification r
   \<lbrace>\<lambda>_ s. obj_at' (\<lambda>ntfn. ntfnBoundTCB ntfn = None) r s\<rbrace>"
  apply (simp add: unbindMaybeNotification_def)
  apply (rule bind_wp[OF _ get_ntfn_sp'])
  apply (rule hoare_pre)
   apply (wpsimp wp: obj_at_setObject2
                 simp: setBoundNotification_def threadSet_def updateObject_default_def in_monad
                       doUnbindNotification_def)
  apply (simp add: setNotification_def obj_at'_real_def)
   apply (wp setObject_ko_wp_at, (simp add: gen_objBits_simps)+)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
  done

crunch unbindNotification, unbindMaybeNotification
  for isFinal[wp]: "\<lambda>s. isFinal cap slot (cteCaps_of s)"
  (wp: sts_bound_tcb_at' threadSet_cteCaps_of crunch_wps getObject_inv
       loadObject_default_inv
   ignore: threadSet
   simp: setBoundNotification_def)

crunch cancelSignal, cancelAllIPC
  for bound_tcb_at'[wp]: "bound_tcb_at' P t"
  (wp: sts_bound_tcb_at' threadSet_cteCaps_of crunch_wps getObject_inv
       loadObject_default_inv
   ignore: threadSet)

lemma finaliseCapTrue_standin_bound_tcb_at':
  "\<lbrace>\<lambda>s. bound_tcb_at' P t s \<and> (\<exists>tt b r. cap = ReplyCap tt b r) \<rbrace>
     finaliseCapTrue_standin cap final
   \<lbrace>\<lambda>_. bound_tcb_at' P t\<rbrace>"
  apply (case_tac cap, simp_all add:finaliseCapTrue_standin_def)
  apply (clarsimp simp: isNotificationCap_def)
  apply (wp, clarsimp)
  done

lemma capDeleteOne_bound_tcb_at':
  "\<lbrace>bound_tcb_at' P tptr and cte_wp_at' (isReplyCap \<circ> cteCap) callerCap\<rbrace>
      cteDeleteOne callerCap \<lbrace>\<lambda>rv. bound_tcb_at' P tptr\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def)
  apply (rule hoare_pre)
   apply (wp finaliseCapTrue_standin_bound_tcb_at' hoare_vcg_all_lift
            hoare_vcg_if_lift2 getCTE_cteCap_wp emptySlot_pred_tcb_at'
        | wpc | simp | wp (once) hoare_drop_imp)+
  apply (clarsimp simp:  cteCaps_of_def isReplyCap_def cte_wp_at_ctes_of
                 split: option.splits)
  apply (case_tac "cteCap cte", simp_all)
  done

lemma cancelIPC_bound_tcb_at'[wp]:
  "\<lbrace>bound_tcb_at' P tptr\<rbrace> cancelIPC t \<lbrace>\<lambda>rv. bound_tcb_at' P tptr\<rbrace>"
  apply (simp add: cancelIPC_def Let_def)
  apply (rule bind_wp[OF _ gts_sp'])
  apply (case_tac "state", simp_all)
         defer 2
         apply (rule hoare_pre)
          apply ((wp sts_bound_tcb_at' getEndpoint_wp | wpc | simp)+)[8]
  apply (simp add: getThreadReplySlot_def locateSlot_conv liftM_def)
  apply (rule hoare_pre)
   apply (wp capDeleteOne_bound_tcb_at' getCTE_ctes_of)
   apply (rule_tac Q'="\<lambda>_. bound_tcb_at' P tptr" in hoare_post_imp)
   apply (clarsimp simp: capHasProperty_def cte_wp_at_ctes_of)
   apply (wp threadSet_pred_tcb_no_state | simp)+
  done

lemmas asUser_bound_obj_at'[wp] = asUser_pred_tcb_at' [of itcbBoundNotification]

crunch suspend
  for bound_tcb_at'[wp]: "bound_tcb_at' P t"
  (wp: sts_bound_tcb_at' cancelIPC_bound_tcb_at'
   ignore: threadSet)

lemma unbindNotification_bound_tcb_at':
  "\<lbrace>\<lambda>_. True\<rbrace> unbindNotification t \<lbrace>\<lambda>rv. bound_tcb_at' ((=) None) t\<rbrace>"
  unfolding unbindNotification_def
  by (wpsimp wp: setBoundNotification_bound_tcb gbn_wp' simp: doUnbindNotification_def)

crunch unbindNotification, unbindMaybeNotification
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"

lemma unbindNotification_tcb_at'[wp]:
  "\<lbrace>tcb_at' t'\<rbrace> unbindNotification t \<lbrace>\<lambda>rv. tcb_at' t'\<rbrace>"
  unfolding unbindNotification_def
  by (wpsimp wp: setBoundNotification_bound_tcb gbn_wp' simp: doUnbindNotification_def)

lemma unbindMaybeNotification_tcb_at'[wp]:
  "\<lbrace>tcb_at' t'\<rbrace> unbindMaybeNotification t \<lbrace>\<lambda>rv. tcb_at' t'\<rbrace>"
  by (simp add: unbindMaybeNotification_def)
     (wpsimp wp: setBoundNotification_bound_tcb gbn_wp' simp: doUnbindNotification_def)

lemma tcbQueueRemove_tcbSchedNext_tcbSchedPrev_None_obj_at':
  "\<lbrace>\<lambda>s. \<exists>ts. list_queue_relation ts q (tcbSchedNexts_of s) (tcbSchedPrevs_of s)\<rbrace>
   tcbQueueRemove q t
   \<lbrace>\<lambda>_ s. obj_at' (\<lambda>tcb. tcbSchedNext tcb = None \<and> tcbSchedPrev tcb = None) t s\<rbrace>"
  apply (clarsimp simp: tcbQueueRemove_def)
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  by (fastforce dest!: heap_ls_last_None
                 simp: list_queue_relation_def prev_queue_head_def queue_end_valid_def
                       obj_at'_def opt_map_def ps_clear_def gen_objBits_simps
                split: if_splits)

lemma tcbSchedDequeue_tcbSchedNext_tcbSchedPrev_None_obj_at':
  "\<lbrace>valid_sched_pointers\<rbrace>
   tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. obj_at' (\<lambda>tcb. tcbSchedNext tcb = None \<and> tcbSchedPrev tcb = None) t s\<rbrace>"
  unfolding tcbSchedDequeue_def
  by (wpsimp wp: tcbQueueRemove_tcbSchedNext_tcbSchedPrev_None_obj_at' threadGet_wp)
     (fastforce simp: ready_queue_relation_def ksReadyQueues_asrt_def obj_at'_def
                      valid_sched_pointers_def opt_pred_def opt_map_def
               split: option.splits)

lemma setThreadState_tcbSchedNext_tcbSchedPrev_None_obj_at'[wp]:
  "setThreadState ref ts \<lbrace>\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedNext tcb = None \<and> tcbSchedPrev tcb = None) t s\<rbrace>"
  unfolding setThreadState_def
  apply (wpsimp wp: threadSet_wp getTCB_wp)
  apply (fastforce simp: obj_at'_def gen_objBits_simps)
  done

lemma (in Finalise_R_2) suspend_tcbSchedNext_tcbSchedPrev_None:
  "\<lbrace>invs'\<rbrace> suspend t \<lbrace>\<lambda>_ s. obj_at' (\<lambda>tcb. tcbSchedNext tcb = None \<and> tcbSchedPrev tcb = None) t s\<rbrace>"
  unfolding suspend_def
  by (wpsimp wp: hoare_drop_imps tcbSchedDequeue_tcbSchedNext_tcbSchedPrev_None_obj_at')

crunch cancelSignal
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (simp: crunch_simps wp: crunch_wps)

crunch tcbSchedDequeue
  for cte_wp_at'[wp]: "cte_wp_at' P p"
  (wp: crunch_wps)

context Finalise_R begin

lemma cteDeleteOne_cte_wp_at_preserved:
  assumes x: "\<And>cap final. P cap \<Longrightarrow> finaliseCap cap final True = fail"
  shows "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s\<rbrace>
           cteDeleteOne ptr
         \<lbrace>\<lambda>rv s. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s\<rbrace>"
  apply (simp add: tree_cte_cteCap_eq[unfolded o_def])
  apply (rule hoare_pre, wp cteDeleteOne_cteCaps_of)
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of x)
  done

lemma cancelIPC_cteCaps_of:
  "\<lbrace>\<lambda>s. (\<forall>p. cte_wp_at' (\<lambda>cte. \<exists>final. finaliseCap (cteCap cte) final True \<noteq> fail) p s \<longrightarrow>
          P ((cteCaps_of s)(p \<mapsto> NullCap))) \<and>
     P (cteCaps_of s)\<rbrace>
     cancelIPC t
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  supply if_cong[cong]
  apply (simp add: cancelIPC_def Let_def capHasProperty_def
                   getThreadReplySlot_def locateSlot_conv)
  apply (rule hoare_pre)
   apply (wp cteDeleteOne_cteCaps_of getCTE_wp' | wpcw
          | simp add: cte_wp_at_ctes_of
          | wp (once) hoare_drop_imps cteCaps_of_ctes_of_lift)+
          apply (wp hoare_convert_imp hoare_vcg_all_lift
                    threadSet_ctes_of threadSet_cteCaps_of
                 | clarsimp)+
         apply (wp cteDeleteOne_cteCaps_of getCTE_wp' | wpcw | simp
                | wp (once) hoare_drop_imps cteCaps_of_ctes_of_lift)+
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def)
  apply (drule_tac x="mdbNext (cteMDBNode x)" in spec)
  apply clarsimp
  apply (auto simp: o_def map_option_case fun_upd_def[symmetric])
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

lemma suspend_cte_wp_at':
  assumes x: "\<And>cap final. P cap \<Longrightarrow> finaliseCap cap final True = fail"
  shows "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte)) p\<rbrace>
           suspend t
         \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p\<rbrace>"
  apply (simp add: suspend_def updateRestartPC_def cong: if_cong)
  apply (rule hoare_pre)
   apply (wp threadSet_cte_wp_at' cancelIPC_cte_wp_at'
             | simp add: x)+
  done

end (* Finalise_R *)

context Finalise_R_2 begin

lemma deletingIRQHandler_cte_preserved:
  assumes x: "\<And>cap final. P cap \<Longrightarrow> finaliseCap cap final True = fail"
  shows "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte)) p\<rbrace>
           deletingIRQHandler irq
         \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p\<rbrace>"
  apply (simp add: deletingIRQHandler_def getSlotCap_def
                   getIRQSlot_def locateSlot_conv getInterruptState_def)
  apply (wpsimp wp: cteDeleteOne_cte_wp_at_preserved getCTE_wp' simp: x)
  done

lemma finaliseCap_equal_cap[wp]:
  "\<lbrace>cte_wp_at' (\<lambda>cte. cteCap cte = cap) sl\<rbrace>
     finaliseCap cap fin flag
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. cteCap cte = cap) sl\<rbrace>"
  apply (simp add: finaliseCap_def Let_def
             cong: if_cong split del: if_split)
   apply (wpsimp wp: suspend_cte_wp_at' deletingIRQHandler_cte_preserved  simp: finaliseCap_def)
  apply (case_tac cap; auto)
  done

end (* Finalise_R_2 *)

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

crunch cteDeleteOne
  for st_tcb_at_simplish: "st_tcb_at' (\<lambda>st. P st \<or> simple' st) t"
  (wp: crunch_wps getObject_inv loadObject_default_inv threadSet_pred_tcb_no_state
   simp: crunch_simps unless_def ignore: threadSet)

lemma cteDeleteOne_st_tcb_at[wp]:
  assumes x[simp]: "\<And>st. simple' st \<longrightarrow> P st" shows
  "\<lbrace>st_tcb_at' P t\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (subgoal_tac "\<exists>Q. P = (Q or simple')")
   apply (clarsimp simp: pred_disj_def)
   apply (rule cteDeleteOne_st_tcb_at_simplish)
  apply (rule_tac x=P in exI)
  apply auto
  done

lemma cteDeleteOne_reply_pred_tcb_at:
  "\<lbrace>\<lambda>s. pred_tcb_at' proj P t s \<and> (\<exists>t' r. cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t' False r) slot s)\<rbrace>
    cteDeleteOne slot
   \<lbrace>\<lambda>rv. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def isFinalCapability_def)
  apply (rule bind_wp [OF _ getCTE_sp])
  apply (rule hoare_assume_pre)
  apply (clarsimp simp: cte_wp_at_ctes_of when_def gen_isCap_simps
                        Let_def finaliseCapTrue_standin_def)
  apply (intro impI conjI, (wp | simp)+)
  done

global_interpretation setNotification: gen_typ_at_props' _ "setNotification p ko"
  by typ_at_props'

crunch setBoundNotification, setNotification
  for sch_act_simple[wp]: sch_act_simple
  (wp: sch_act_simple_lift)

lemma rescheduleRequired_sch_act_not[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. sch_act_not t\<rbrace>"
  apply (simp add: rescheduleRequired_def setSchedulerAction_def)
  apply (wp hoare_TrueI | simp)+
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
  "\<lbrace>valid_objs' and pspace_aligned' and pspace_distinct'\<rbrace>
   mapM_x (\<lambda>t. do
                 y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                 tcbSchedEnqueue t
               od) q
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp')
  apply (wpsimp wp: sts_valid_objs')
   apply (clarsimp simp: valid_tcb_state'_def)+
  done

lemma cancelAllIPC_mapM_x_tcbDomain_obj_at':
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>
   mapM_x (\<lambda>t. do
                 y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                 tcbSchedEnqueue t
               od) q
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  by (wp mapM_x_wp' | simp)+

lemma rescheduleRequired_oa_queued':
  "rescheduleRequired \<lbrace>obj_at' (\<lambda>tcb. Q (tcbDomain tcb) (tcbPriority tcb)) t\<rbrace>"
  unfolding rescheduleRequired_def tcbSchedEnqueue_def tcbQueuePrepend_def
  by (wpsimp wp: threadGet_wp)

lemma cancelAllIPC_tcbDomain_obj_at':
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>
     cancelAllIPC epptr
   \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  apply (simp add: cancelAllIPC_def)
  apply (wp hoare_vcg_conj_lift hoare_vcg_const_Ball_lift
            rescheduleRequired_oa_queued' cancelAllIPC_mapM_x_tcbDomain_obj_at'
            getEndpoint_wp
       | wpc
       | simp)+
  done

lemma cancelAllSignals_tcbDomain_obj_at':
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>
     cancelAllSignals epptr
   \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
apply (simp add: cancelAllSignals_def)
apply (wp hoare_vcg_conj_lift hoare_vcg_const_Ball_lift
          rescheduleRequired_oa_queued' cancelAllIPC_mapM_x_tcbDomain_obj_at'
          getNotification_wp
     | wpc
     | simp)+
done

lemma unbindMaybeNotification_tcbDomain_obj_at':
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>
     unbindMaybeNotification r
   \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  unfolding unbindMaybeNotification_def
  by (wpsimp wp: getNotification_wp gbn_wp' simp: setBoundNotification_def doUnbindNotification_def)

crunch isFinalCapability
  for sch_act[wp]: "\<lambda>s. sch_act_wf (ksSchedulerAction s) s"
  (simp: crunch_simps)

crunch
  isFinalCapability
  for weak_sch_act[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (simp: crunch_simps)

crunch unbindNotification
  for valid_cap'[wp]: "valid_cap' cap"

lemma no_idle_thread_cap:
  "\<lbrakk> cte_wp_at ((=) (cap.ThreadCap (idle_thread s))) sl s; valid_global_refs s \<rbrakk> \<Longrightarrow> False"
  apply (cases sl)
  apply (clarsimp simp: valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)
  apply ((erule allE)+, erule (1) impE)
  apply (clarsimp simp: cap_range_def)
  done

lemmas getCTE_no_0_obj'_helper
  = getCTE_inv
    hoare_strengthen_post[where Q'="\<lambda>_. no_0_obj'" and P=no_0_obj' and f="getCTE slot" for slot]

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

lemma (in delete_one) deletingIRQHandler_corres:
  "corres dc (einvs) (invs')
          (deleting_irq_handler irq) (deletingIRQHandler irq)"
  apply (simp add: deleting_irq_handler_def deletingIRQHandler_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getIRQSlot_corres])
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
          apply (auto simp: cte_wp_at_ctes_of is_cap_simps gen_isCap_simps)[1]
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

lemma return_NullCap_pair_corres[corres]:
  "corres (\<lambda>r r'. cap_relation (fst r) (fst r') \<and> cap_relation (snd r) (snd r'))
          \<top> \<top>
          (return (cap.NullCap, cap.NullCap)) (return (NullCap, NullCap))"
  by (corres corres: corres_returnTT)

lemma unbindNotification_corres:
  "corres dc
      (invs and tcb_at t)
      invs'
      (unbind_notification t)
      (unbindNotification t)"
  apply (simp add: unbind_notification_def unbindNotification_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getBoundNotification_corres])
      apply (rule corres_option_split)
        apply simp
       apply (rule corres_return_trivial)
      apply (rule corres_split[OF getNotification_corres])
        apply (clarsimp simp: doUnbindNotification_def)
        apply (rule corres_split[OF setNotification_corres])
           apply (clarsimp simp: ntfn_relation_def split:Structures_A.ntfn.splits)
          apply (rule setBoundNotification_corres)
         apply (wp gbn_wp' gbn_wp)+
   apply (clarsimp elim!: obj_at_valid_objsE
                   dest!: bound_tcb_at_state_refs_ofD invs_valid_objs
                    simp: valid_obj_def is_tcb tcb_ntfn_is_bound_def obj_at_def
                          valid_tcb_def valid_bound_ntfn_def invs_psp_aligned invs_distinct
                   split: option.splits)
  apply (clarsimp dest!: obj_at_valid_objs' bound_tcb_at_state_refs_ofD' invs_valid_objs'
                   simp: valid_obj'_def valid_tcb'_def valid_bound_ntfn'_def tcb_ntfn_is_bound'_def
                  split: option.splits)
  done

lemma unbindMaybeNotification_corres:
  "corres dc
      (invs and ntfn_at ntfnptr) (invs' and ntfn_at' ntfnptr)
      (unbind_maybe_notification ntfnptr)
      (unbindMaybeNotification ntfnptr)"
  apply (simp add: unbind_maybe_notification_def unbindMaybeNotification_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getNotification_corres])
      apply (rule corres_option_split)
        apply (clarsimp simp: ntfn_relation_def split: Structures_A.ntfn.splits)
       apply (rule corres_return_trivial)
      apply (simp add: doUnbindNotification_def)
      apply (rule corres_split[OF setNotification_corres])
         apply (clarsimp simp: ntfn_relation_def split: Structures_A.ntfn.splits)
        apply (rule setBoundNotification_corres)
       apply (wp get_simple_ko_wp getNotification_wp)+
   apply (clarsimp elim!: obj_at_valid_objsE
                   dest!: bound_tcb_at_state_refs_ofD invs_valid_objs
                    simp: valid_obj_def is_tcb tcb_ntfn_is_bound_def invs_psp_aligned invs_distinct
                          valid_tcb_def valid_bound_ntfn_def valid_ntfn_def
                   split: option.splits)
  apply (clarsimp dest!: obj_at_valid_objs' bound_tcb_at_state_refs_ofD' invs_valid_objs'
                   simp: valid_obj'_def valid_tcb'_def valid_bound_ntfn'_def
                         tcb_ntfn_is_bound'_def valid_ntfn'_def
                  split: option.splits)
  done

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

lemma cte_wp_at_norm_eq':
  "cte_wp_at' P p s = (\<exists>cte. cte_wp_at' ((=) cte) p s \<and> P cte)"
  by (simp add: cte_wp_at_ctes_of)

lemma isFinal_cte_wp_def:
  "isFinal cap p (cteCaps_of s) =
  (\<not>isUntypedCap cap \<and>
   (\<forall>p'. p \<noteq> p' \<longrightarrow>
         cte_at' p' s \<longrightarrow>
         cte_wp_at' (\<lambda>cte'. \<not> isUntypedCap (cteCap cte') \<longrightarrow>
                            \<not> sameObjectAs cap (cteCap cte')) p' s))"
  apply (simp add: isFinal_def cte_wp_at_ctes_of cteCaps_of_def)
  apply (rule iffI)
   apply clarsimp
   apply (case_tac cte)
   apply fastforce
  apply fastforce
  done

lemma valid_cte_at_neg_typ':
  assumes T: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> cte_at' p' s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> cte_at' p' s\<rbrace>"
  apply (simp add: cte_at_typ')
  apply (rule hoare_vcg_conj_lift [OF T])
  apply (simp only: imp_conv_disj)
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_vcg_disj_lift [OF T])
  apply (rule hoare_vcg_prop)
  done

lemma isFinal_lift:
  assumes x: "\<And>P p. \<lbrace>cte_wp_at' P p\<rbrace> f \<lbrace>\<lambda>_. cte_wp_at' P p\<rbrace>"
  assumes y: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. isFinal (cteCap cte) sl (cteCaps_of s)) sl s\<rbrace>
         f
         \<lbrace>\<lambda>r s. cte_wp_at' (\<lambda>cte. isFinal (cteCap cte) sl (cteCaps_of s)) sl s\<rbrace>"
  apply (subst cte_wp_at_norm_eq')
  apply (subst cte_wp_at_norm_eq' [where P="\<lambda>cte. isFinal (cteCap cte) sl m" for sl m])
  apply (simp only: isFinal_cte_wp_def imp_conv_disj de_Morgan_conj)
  apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift x hoare_vcg_disj_lift
            valid_cte_at_neg_typ' [OF y])
  done

lemma setEndpoint_sch_act_not_ct[wp]:
  "\<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s\<rbrace>
   setEndpoint ptr val \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps, wp, simp)

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
  apply (rule hoare_pre)
   apply (wps setNotification_ksCurThread, wp, clarsimp)
  done

lemma unbindMaybeNotification_ct_in_state'[wp]:
  "\<lbrace>ct_in_state' P\<rbrace> unbindMaybeNotification t \<lbrace>\<lambda>_. ct_in_state' P\<rbrace>"
  unfolding unbindMaybeNotification_def
  by (wpsimp simp: doUnbindNotification_def)

lemma setNotification_sch_act_sane:
  "\<lbrace>sch_act_sane\<rbrace> setNotification a ntfn \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  by (wp sch_act_sane_lift)

lemma unbindMaybeNotification_sch_act_sane[wp]:
  "\<lbrace>sch_act_sane\<rbrace> unbindMaybeNotification t \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  unfolding unbindMaybeNotification_def
  by (wpsimp wp: setNotification_sch_act_sane sbn_sch_act_sane simp: doUnbindNotification_def)

context Finalise_R_2 begin

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
   apply (clarsimp simp: sameObjectAs_not_Untyped)
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
   subgoal by (simp add: verit_implies_simplify(1) sameObjectAs_not_Untyped)
              (simp add: sameObjectAs_not_Untyped') (* simps do not combine *)
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
  apply (clarsimp simp: sameObjectAs_not_Untyped)
  done

crunch cteDeleteOne, unbindNotification
  for sch_act_simple[wp]: sch_act_simple
  (wp: crunch_wps ssa_sch_act_simple sts_sch_act_simple getObject_inv
       loadObject_default_inv
   simp: crunch_simps
   rule: sch_act_simple_lift)

crunch cteDeleteOne
  for sch_act_not[wp]: "sch_act_not t"
  (simp: crunch_simps case_Null_If unless_def
   wp: crunch_wps getObject_inv loadObject_default_inv)

crunch cteDeleteOne
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma cteDeleteOne_tcbDomain_obj_at':
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def split_def)
  apply (wp emptySlot_tcbDomain cancelAllIPC_tcbDomain_obj_at' cancelAllSignals_tcbDomain_obj_at'
          isFinalCapability_inv getCTE_wp
          unbindMaybeNotification_tcbDomain_obj_at'
     | rule hoare_drop_imp
     | simp add: finaliseCapTrue_standin_def Let_def
            split del: if_split
     | wpc)+
  apply (clarsimp simp: cte_wp_at'_def)
  done

lemma fast_finaliseCap_corres:
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
  apply (cases cap, simp_all add: finaliseCap_def gen_isCap_simps
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
    apply (rule corres_split[OF unbindMaybeNotification_corres])
         apply (rule cancelAllSignals_corres)
       apply (wp abs_typ_at_lifts unbind_maybe_notification_invs gen_typ_at_lifts hoare_drop_imps getNotification_wp
            | wpc)+
   apply (clarsimp simp: valid_cap_def)
  apply (clarsimp simp: valid_cap'_def valid_obj'_def
                 dest!: invs_valid_objs' obj_at_valid_objs' )
  done

crunch ThreadDecls_H.suspend, unbindNotification
  for no_0_obj'[wp]: no_0_obj'
  (simp: crunch_simps wp: crunch_wps getCTE_no_0_obj'_helper cong: option.case_cong_weak)

crunch deleteCallerCap
  for idle_thread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps)
crunch deleteCallerCap
  for sch_act_simple: sch_act_simple
  (wp: crunch_wps)
crunch deleteCallerCap
  for sch_act_not[wp]: "sch_act_not t"
  (wp: crunch_wps)
crunch deleteCallerCap
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

sublocale deleteCallerCap: gen_typ_at_props' _ "deleteCallerCap receiver"
  by typ_at_props'

sublocale delete_one_conc_pre
  by (unfold_locales, wp)
     (wp cteDeleteOne_tcbDomain_obj_at' cteDeleteOne_typ_at' cteDeleteOne_reply_pred_tcb_at | simp)+

end (* Finalise_R_2 *)

locale Finalise_R_3 = Finalise_R_2 +
  fixes post_cap_delete_pre' :: "capability \<Rightarrow> paddr \<Rightarrow> (paddr \<Rightarrow> capability option) \<Rightarrow> bool"
  assumes isFinalCapability_corres':
    "\<And>cap ptr cte.
     final_matters' (cteCap cte) \<Longrightarrow>
     corres (=) (invs and cte_wp_at ((=) cap) ptr)
                 (invs' and cte_wp_at' ((=) cte) (cte_map ptr))
         (is_final_cap cap) (isFinalCapability cte)"
  assumes cteDeleteOne_invs[wp]:
    "\<And>ptr. cteDeleteOne ptr \<lbrace>invs'\<rbrace>"
  assumes arch_finaliseCap_corres:
    "\<And>cap cap' final final' sl.
     \<lbrakk>final_matters' (ArchObjectCap cap') \<Longrightarrow> final = final'; acap_relation cap cap'\<rbrakk>
     \<Longrightarrow> corres (\<lambda>r r'. cap_relation (fst r) (fst r') \<and> cap_relation (snd r) (snd r'))
               (\<lambda>s. invs s \<and> s \<turnstile> cap.ArchObjectCap cap
                    \<and> (final_matters (cap.ArchObjectCap cap)
                    \<longrightarrow> final = is_final_cap' (cap.ArchObjectCap cap) s)
                       \<and> cte_wp_at ((=) (cap.ArchObjectCap cap)) sl s)
               (\<lambda>s. invs' s \<and> s \<turnstile>' ArchObjectCap cap' \<and>
                    (final_matters' (ArchObjectCap cap') \<longrightarrow>
                     final' = isFinal (ArchObjectCap cap') (cte_map sl) (cteCaps_of s)))
               (arch_finalise_cap cap final) (Arch.finaliseCap cap' final')"
  assumes emptySlot_invs'[wp]:
    "\<And>sl info.
     \<lbrace>\<lambda>s. invs' s \<and> cte_wp_at' (\<lambda>cte. removeable' sl s (cteCap cte)) sl s
          \<and> (info \<noteq> NullCap \<longrightarrow> post_cap_delete_pre' info sl (cteCaps_of s) )\<rbrace>
     emptySlot sl info
     \<lbrace>\<lambda>rv. invs'\<rbrace>"
  assumes Arch_finaliseCap_sch_act_simple[wp]:
    "\<And>acap b. Arch.finaliseCap acap b \<lbrace>sch_act_simple\<rbrace>"
  assumes prepareThreadDelete_sch_act_simple[wp]:
    "\<And>t. prepareThreadDelete t \<lbrace>sch_act_simple\<rbrace>"
  assumes finaliseCap_cte_refs:
    "\<And>cap final flag.
     \<lbrace>\<lambda>s. s \<turnstile>' cap\<rbrace>
     finaliseCap cap final flag
     \<lbrace>\<lambda>rv s. fst rv \<noteq> NullCap \<longrightarrow> cte_refs' (fst rv) = cte_refs' cap\<rbrace>"
begin

sublocale delete_one_conc_fr: delete_one_conc
  by unfold_locales (wp cteDeleteOne_invs)

crunch finaliseCap
  for sch_act_simple[wp]: sch_act_simple
  (simp: crunch_simps
   rule: sch_act_simple_lift
   wp: crunch_wps)

lemma finaliseCap_valid_cap[wp]:
  "\<lbrace>valid_cap' cap\<rbrace> finaliseCap cap final flag \<lbrace>\<lambda>rv. valid_cap' (fst rv)\<rbrace>"
  apply (simp add: finaliseCap_def Let_def
                   getThreadCSpaceRoot
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp | simp only: valid_NullCap o_def fst_conv | wpc)+
  apply simp
  apply (intro conjI impI)
   apply (clarsimp simp: valid_cap'_def gen_isCap_simps capAligned_def
                         gen_objBits_simps shiftL_nat)+
  done

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
  apply clarsimp
  apply (intro conjI impI)
    apply (clarsimp dest!: isCapDs simp: valid_cap'_def)
   apply (drule invs_valid_global', drule(1) valid_globals_cte_wpD')
   apply (drule valid_capAligned, drule capAligned_capUntypedPtr)
    apply (clarsimp dest!: isCapDs)
   apply (clarsimp dest!: isCapDs)
  apply (clarsimp dest!: isCapDs)
  done

lemma finaliseCap_zombie_cap[wp]:
  "\<lbrace>cte_wp_at' (\<lambda>cte. (P and isZombie) (cteCap cte)) sl\<rbrace>
     finaliseCap cap fin flag
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. (P and isZombie) (cteCap cte)) sl\<rbrace>"
  apply (simp add: finaliseCap_def Let_def
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp suspend_cte_wp_at' deletingIRQHandler_cte_preserved
          | clarsimp simp: finaliseCap_def gen_isCap_simps | wpc)+
  done

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
                 | clarsimp simp: finaliseCap_def gen_isCap_simps
                 | rule conjI
                 | wpc)+
  apply fastforce
  done

lemma isFinalCapability_corres:
  "corres (\<lambda>rv rv'. final_matters' (cteCap cte) \<longrightarrow> rv = rv')
          (invs and cte_wp_at ((=) cap) ptr)
          (invs' and cte_wp_at' ((=) cte) (cte_map ptr))
       (is_final_cap cap) (isFinalCapability cte)"
  apply (cases "final_matters' (cteCap cte)")
   apply simp
   apply (erule isFinalCapability_corres')
  apply (subst bind_return[symmetric],
         rule corres_symb_exec_r)
     apply (rule corres_no_failI)
      apply wp
     apply (clarsimp simp: in_monad is_final_cap_def simpler_gets_def)
    apply (wp isFinalCapability_inv)+
  apply fastforce
  done

lemma cap_delete_one_corres:
  "corres dc (einvs and cte_wp_at can_fast_finalise ptr)
        (invs' and cte_at' (cte_map ptr))
        (cap_delete_one ptr) (cteDeleteOne (cte_map ptr))"
  apply (simp add: cap_delete_one_def cteDeleteOne_def'
                   unless_def when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_cap_corres])
      apply (rule_tac F="can_fast_finalise cap" in corres_gen_asm)
      apply (rule corres_if)
        apply fastforce
       apply (rule corres_split[OF isFinalCapability_corres[where ptr=ptr]])
         apply (simp add: split_def bind_assoc [THEN sym])
         apply (rule corres_split[OF fast_finaliseCap_corres[where sl=ptr]])
              apply simp+
           apply (rule emptySlot_corres, simp)
          apply (repeat 3 \<open>wp hoare_drop_imps\<close>)
       apply (wp isFinalCapability_inv | wp (once) isFinal[where x="cte_map ptr"])+
      apply (rule corres_trivial, simp)
     apply (wp get_cap_wp getCTE_wp)+
   apply (clarsimp simp: cte_wp_at_caps_of_state can_fast_finalise_Null
                  elim!: caps_of_state_valid_cap)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply fastforce
  done

sublocale delete_one
  by (unfold_locales)
     (corres corres: cap_delete_one_corres)

lemma finaliseCap_corres:
  "\<lbrakk> final_matters' cap' \<Longrightarrow> final = final'; cap_relation cap cap';
          flag \<longrightarrow> can_fast_finalise cap \<rbrakk>
     \<Longrightarrow> corres (\<lambda>x y. cap_relation (fst x) (fst y) \<and> cap_relation (snd x) (snd y))
           (\<lambda>s. einvs s \<and> s \<turnstile> cap \<and> (final_matters cap \<longrightarrow> final = is_final_cap' cap s)
                       \<and> cte_wp_at ((=) cap) sl s)
           (\<lambda>s. invs' s \<and> s \<turnstile>' cap' \<and> sch_act_simple s \<and>
                 (final_matters' cap' \<longrightarrow>
                      final' = isFinal cap' (cte_map sl) (cteCaps_of s)))
           (finalise_cap cap final) (finaliseCap cap' final' flag)"
  supply invs_no_0_obj'[simp]
  apply (cases cap, simp_all add: finaliseCap_def gen_isCap_simps
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
         apply (rule corres_split[OF unbindMaybeNotification_corres])
           apply (rule cancelAllSignals_corres)
          apply (wpsimp wp: abs_typ_at_lifts unbind_maybe_notification_invs gen_typ_at_lifts hoare_drop_imps
                            hoare_vcg_all_lift)+
        apply (clarsimp simp: valid_cap_def)
       apply (clarsimp simp: valid_cap'_def)
      apply (fastforce simp: final_matters'_def shiftL_nat zbits_map_def)
     apply (clarsimp simp add: final_matters'_def getThreadCSpaceRoot
                               liftM_def[symmetric] o_def zbits_map_def
                               dc_def[symmetric])
     apply (rename_tac t)
     apply (rule_tac P="\<lambda>s. t \<noteq> idle_thread s" and P'="\<lambda>s. t \<noteq> ksIdleThread s" in corres_add_guard)
      apply clarsimp
      apply (rule context_conjI)
       apply (clarsimp dest!: no_idle_thread_cap)
      apply (clarsimp simp: state_relation_def)
     apply (rule corres_guard_imp)
       apply (rule corres_split[OF unbindNotification_corres])
         apply (rule corres_split[OF suspend_corres])
           apply (clarsimp simp: liftM_def[symmetric] o_def dc_def[symmetric] zbits_map_def)
           apply (rule prepareThreadDelete_corres, simp)
          apply (wp unbind_notification_invs unbind_notification_simple_sched_action
                    delete_one_conc_fr.suspend_objs')+
      apply (clarsimp simp add: valid_cap_def)
     apply (clarsimp simp add: valid_cap'_def)
    apply (simp add: final_matters'_def liftM_def[symmetric]
                     o_def dc_def[symmetric])
    apply (intro impI, rule corres_guard_imp)
      apply (rule deletingIRQHandler_corres)
     apply simp
    apply simp
   apply (clarsimp simp: final_matters'_def)
   apply (rule_tac F="False" in corres_req)
    apply clarsimp
    apply (frule zombies_finalD, (clarsimp simp: is_cap_simps)+)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply simp
  apply (clarsimp split del: if_split simp: o_def)
  apply (rule corres_guard_imp [OF arch_finaliseCap_corres], (fastforce simp: valid_sched_def)+)
  done

end (* Finalise_R_3 *)

end
