(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory IpcCancel_R
imports
  Schedule_R
  "../../lib/SimpStrategy"
begin


crunch aligned'[wp]: epCancelAll pspace_aligned'
  (wp: crunch_wps mapM_x_wp' simp: unless_def)
crunch distinct'[wp]: epCancelAll pspace_distinct'
  (wp: crunch_wps mapM_x_wp' simp: unless_def)

crunch aligned'[wp]: aepCancelAll pspace_aligned'
  (wp: crunch_wps mapM_x_wp')
crunch distinct'[wp]: aepCancelAll pspace_distinct'
  (wp: crunch_wps mapM_x_wp')

lemma asyncIPCCancel_simple[wp]:
  "\<lbrace>\<top>\<rbrace> asyncIPCCancel t aep \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (simp add: asyncIPCCancel_def Let_def)
  apply (wp setThreadState_st_tcb | simp)+
  done

lemma asyncIPCCancel_pred_tcb_at':
  "\<lbrace>pred_tcb_at' proj P t' and K (t \<noteq> t')\<rbrace>
     asyncIPCCancel t aepptr
   \<lbrace>\<lambda>rv. pred_tcb_at' proj P t'\<rbrace>"
  apply (simp add: asyncIPCCancel_def)
  apply (wp sts_pred_tcb_neq' getAsyncEP_wp | wpc | clarsimp)+
  done

crunch pred_tcb_at'[wp]: emptySlot "pred_tcb_at' proj P t"
  (wp: setCTE_pred_tcb_at')

lemma set_ep_pred_tcb_at' [wp]: 
  "\<lbrace> pred_tcb_at' proj P t \<rbrace> 
   setEndpoint ep v 
   \<lbrace> \<lambda>rv. pred_tcb_at' proj P t \<rbrace>"
  apply (simp add: setEndpoint_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
   apply simp
  apply (simp add: updateObject_default_def in_monad projectKOs)
  done

(* valid_queues is too strong *)
definition valid_inQ_queues :: "KernelStateData_H.kernel_state \<Rightarrow> bool" where
  "valid_inQ_queues \<equiv>
     \<lambda>s. \<forall>d p. (\<forall>t\<in>set (ksReadyQueues s (d, p)). obj_at' (inQ d p) t s) \<and> distinct (ksReadyQueues s (d, p))"

defs capHasProperty_def:
  "capHasProperty ptr P \<equiv> cte_wp_at' (\<lambda>c. P (cteCap c)) ptr"

(* Assume various facts about cteDeleteOne, proved in Finalise_R *)
locale delete_one_conc_pre =
  assumes delete_one_st_tcb_at:
    "\<And>P. (\<And>st. simple' st \<longrightarrow> P st) \<Longrightarrow>
     \<lbrace>st_tcb_at' P t\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  assumes delete_one_typ_at:
    "\<And>P. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  assumes delete_one_aligned:
    "\<lbrace>pspace_aligned'\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  assumes delete_one_distinct:
    "\<lbrace>pspace_distinct'\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  assumes delete_one_it:
    "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> cteDeleteOne cap \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  assumes delete_one_queues:
    "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>
     cteDeleteOne sl \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  assumes delete_one_inQ_queues:
    "\<lbrace>valid_inQ_queues\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  assumes delete_one_sch_act_simple:
    "\<lbrace>sch_act_simple\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  assumes delete_one_sch_act_not:
    "\<And>t. \<lbrace>sch_act_not t\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>rv. sch_act_not t\<rbrace>"
  assumes delete_one_reply_st_tcb_at:
    "\<And>P t. \<lbrace>\<lambda>s. st_tcb_at' P t s \<and> (\<exists>t'. cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t' False) slot s)\<rbrace>
      cteDeleteOne slot
     \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  assumes delete_one_ksCurDomain:
    "\<And>P. \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> cteDeleteOne sl \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
  assumes delete_one_tcbDomain_obj_at':
    "\<And>P. \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"

lemma (in delete_one_conc_pre) ipcCancel_simple[wp]:
  "\<lbrace>\<top>\<rbrace> ipcCancel t \<lbrace>\<lambda>rv. st_tcb_at' simple' t\<rbrace>"
  apply (simp add: ipcCancel_def Let_def getThreadReplySlot_def
             cong: Structures_H.thread_state.case_cong list.case_cong)
  apply (rule hoare_seq_ext [OF _ gts_sp'])
  apply (rule hoare_pre)
   apply (wpc
           | wp sts_st_tcb_at'_cases hoare_vcg_conj_lift
                hoare_vcg_const_imp_lift delete_one_st_tcb_at
                threadSet_pred_tcb_no_state
                hoare_strengthen_post [OF asyncIPCCancel_simple]
           | simp
           | rule hoare_drop_imps
           | clarsimp elim!: pred_tcb'_weakenE)+
  apply (auto simp: pred_tcb_at'
             elim!: pred_tcb'_weakenE)
  done

lemma (in delete_one_conc_pre) ipcCancel_st_tcb_at':
  "\<lbrace>st_tcb_at' P t' and K (t \<noteq> t')\<rbrace>
     ipcCancel t
   \<lbrace>\<lambda>rv. st_tcb_at' P t'\<rbrace>"
  apply (simp add: ipcCancel_def Let_def getThreadReplySlot_def locateSlot_def
                   capHasProperty_def isCap_simps)
  apply (wp sts_pred_tcb_neq' hoare_drop_imps delete_one_reply_st_tcb_at
       | wpc | clarsimp)+
          apply (wp getCTE_wp | clarsimp)+
         apply (wp hoare_vcg_ex_lift threadSet_cte_wp_at' hoare_vcg_imp_lift
                   asyncIPCCancel_pred_tcb_at' sts_pred_tcb_neq' getEndpoint_wp gts_wp'
                   threadSet_pred_tcb_no_state
              | wpc | clarsimp)+
  apply (auto simp: cte_wp_at_ctes_of isCap_simps)
  done

crunch typ_at'[wp]: emptySlot "\<lambda>s. P (typ_at' T p s)"

crunch tcb_at'[wp]: asyncIPCCancel "tcb_at' t"
  (wp: crunch_wps simp: crunch_simps)

context delete_one_conc_pre
begin

lemmas delete_one_typ_ats[wp] = typ_at_lifts [OF delete_one_typ_at]

lemma ipcCancel_tcb_at'[wp]:
  "\<lbrace>tcb_at' t\<rbrace> ipcCancel t' \<lbrace>\<lambda>_. tcb_at' t\<rbrace>"
  apply (simp add: ipcCancel_def Let_def getThreadReplySlot_def)
  apply (wp delete_one_typ_ats hoare_drop_imps
       | simp add: o_def if_apply_def2 | wpc | assumption)+
  done

end

declare if_weak_cong [cong]

declare delete_remove1 [simp]

declare delete.simps [simp del]

lemma invs_weak_sch_act_wf[elim!]:
  "invs' s \<Longrightarrow> weak_sch_act_wf (ksSchedulerAction s) s"
  apply (drule invs_sch_act_wf')
  apply (clarsimp simp: weak_sch_act_wf_def)
  done

crunch tcb_at[wp]: set_endpoint "tcb_at t"
crunch tcb_at'[wp]: setEndpoint "tcb_at' t"

lemma blocked_ipc_cancel_corres:
  "\<lbrakk> st = Structures_A.BlockedOnReceive epPtr x \<or> 
     st = Structures_A.BlockedOnSend epPtr p; thread_state_relation st st' \<rbrakk> \<Longrightarrow>
   corres dc (invs and st_tcb_at (op = st) t) (invs' and st_tcb_at' (op = st') t)
           (blocked_ipc_cancel st t)
           (do ep \<leftarrow> getEndpoint epPtr;
               y \<leftarrow> assert (\<not> (case ep of IdleEP \<Rightarrow> True | _ \<Rightarrow> False));
               ep' \<leftarrow>
               if remove1 t (epQueue ep) = [] then return IdleEP
               else 
                 return $ epQueue_update (%_. (remove1 t (epQueue ep))) ep;
               y \<leftarrow> setEndpoint epPtr ep';
               setThreadState Structures_H.thread_state.Inactive t
            od)"  
  apply (simp add: blocked_ipc_cancel_def gbep_ret)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_ep_corres])
      apply (rule_tac F="ep \<noteq> IdleEP" in corres_gen_asm2)
      apply (rule corres_assert_assume[rotated])
       apply (clarsimp split: endpoint.splits)
      apply (rule_tac P="invs and st_tcb_at (op = st) t" and 
                      P'="invs' and st_tcb_at' (op = st') t" in corres_inst)
      apply (case_tac rv)
        apply (simp add: ep_relation_def)
       apply (simp add: get_ep_queue_def ep_relation_def split del: split_if)
       apply (rename_tac list)
       apply (case_tac "remove1 t list")
        apply simp
        apply (rule corres_guard_imp)
          apply (rule corres_split [OF _ set_ep_corres])
             apply (rule sts_corres)
             apply simp
            apply (simp add: ep_relation_def)
           apply (simp add: valid_tcb_state_def pred_conj_def)
           apply (wp weak_sch_act_wf_lift)
         apply (clarsimp simp: st_tcb_at_tcb_at)
         apply (clarsimp simp: st_tcb_at_def obj_at_def)
         apply (erule pspace_valid_objsE)
          apply fastforce
         apply (auto simp: valid_tcb_state_def valid_tcb_def 
                           valid_obj_def obj_at_def)[1]
        apply (clarsimp simp: pred_tcb_at')
        apply (clarsimp simp: pred_tcb_at'_def)
        apply (drule obj_at_ko_at')
        apply clarify
        apply (drule ko_at_valid_objs')
          apply fastforce
         apply (simp add: projectKOs)
        apply (auto simp add: valid_obj'_def valid_tcb'_def 
                              valid_tcb_state'_def)[1]
       apply clarsimp
       apply (rule corres_guard_imp)
         apply (rule corres_split [OF _ set_ep_corres])
            apply (rule sts_corres)
            apply simp
           apply (simp add: ep_relation_def)
          apply (wp)
        apply (clarsimp simp: st_tcb_at_tcb_at)
        apply (clarsimp simp: st_tcb_at_def obj_at_def)
        apply (erule pspace_valid_objsE)
         apply fastforce
        apply (auto simp: valid_tcb_state_def valid_tcb_def 
                          valid_obj_def obj_at_def)[1]
       apply (clarsimp simp: pred_tcb_at')
       apply (clarsimp simp: pred_tcb_at'_def)
       apply (drule obj_at_ko_at')
       apply clarify
       apply (drule ko_at_valid_objs')
         apply fastforce
        apply (simp add: projectKOs)
       apply (auto simp add: valid_obj'_def valid_tcb'_def 
                             valid_tcb_state'_def)[1]
      apply (simp add: get_ep_queue_def ep_relation_def split del: split_if)
      apply (rename_tac list)
      apply (case_tac "remove1 t list")
       apply simp
       apply (rule corres_guard_imp)
         apply (rule corres_split [OF _ set_ep_corres])
            apply (rule sts_corres)
            apply simp
           apply (simp add: ep_relation_def)
          apply (simp add: valid_tcb_state_def pred_conj_def)
          apply (wp weak_sch_act_wf_lift)
        apply (clarsimp simp: st_tcb_at_tcb_at)
        apply (clarsimp simp: st_tcb_at_def obj_at_def)
        apply (erule pspace_valid_objsE)
         apply fastforce
        apply (auto simp: valid_tcb_state_def valid_tcb_def 
                          valid_obj_def obj_at_def)[1]
       apply (clarsimp simp: pred_tcb_at')
       apply (clarsimp simp: pred_tcb_at'_def)
       apply (drule obj_at_ko_at')
       apply clarify
       apply (drule ko_at_valid_objs')
         apply fastforce
        apply (simp add: projectKOs)
       apply (auto simp add: valid_obj'_def valid_tcb'_def 
                             valid_tcb_state'_def)[1]
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (rule corres_split [OF _ set_ep_corres])
           apply (rule sts_corres)
           apply simp
          apply (simp add: ep_relation_def)
         apply (wp)
       apply (clarsimp simp: st_tcb_at_tcb_at)
       apply (clarsimp simp: st_tcb_at_def obj_at_def)
       apply (erule pspace_valid_objsE)
        apply fastforce
       apply (auto simp: valid_tcb_state_def valid_tcb_def 
                         valid_obj_def obj_at_def)[1]
      apply (clarsimp simp: pred_tcb_at')
      apply (clarsimp simp: pred_tcb_at'_def)
      apply (drule obj_at_ko_at')
      apply clarify
      apply (drule ko_at_valid_objs')
        apply fastforce
       apply (simp add: projectKOs)
      apply (auto simp add: valid_obj'_def valid_tcb'_def 
                            valid_tcb_state'_def)[1]
     apply (wp getEndpoint_wp)    
   apply (clarsimp simp: st_tcb_at_def obj_at_def)
   apply (erule pspace_valid_objsE)
    apply fastforce
   apply (auto simp: valid_tcb_state_def valid_tcb_def 
                     valid_obj_def obj_at_def)[1]
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at'_def)
   apply (drule obj_at_ko_at')
   apply clarify
   apply (drule ko_at_valid_objs')
     apply fastforce
    apply (simp add: projectKOs)
   apply (auto simp add: valid_obj'_def valid_tcb'_def 
                         valid_tcb_state'_def)[1]
  apply (fastforce simp: ko_wp_at'_def obj_at'_def projectKOs dest: sym_refs_st_tcb_atD')
  done

lemma ac_corres:
  "corres dc 
          (invs and st_tcb_at (op = (Structures_A.BlockedOnAsyncEvent aep)) t)
          (invs' and st_tcb_at' (op = (BlockedOnAsyncEvent aep)) t) 
          (async_ipc_cancel t aep)
          (asyncIPCCancel t aep)"
  apply (simp add: async_ipc_cancel_def asyncIPCCancel_def Let_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_aep_corres])
      apply (rule_tac F="isWaitingAEP (aepObj aepaa)" in corres_gen_asm2)
      apply (case_tac "aep_obj aepa")
        apply (simp add: aep_relation_def isWaitingAEP_def)
       apply (simp add: isWaitingAEP_def aep_relation_def split del: split_if)
       apply (rename_tac list)
       apply (rule_tac R="remove1 t list = []" in corres_cases)
        apply (simp del: dc_simp)
        apply (rule corres_split [OF _ set_aep_corres])
           apply (rule sts_corres)
           apply simp
          apply (simp add: aep_relation_def)
         apply (wp)
       apply (simp add: list_case_If del: dc_simp)
       apply (rule corres_split [OF _ set_aep_corres])
          apply (rule sts_corres)
          apply simp
         apply (clarsimp simp add: aep_relation_def neq_Nil_conv)
        apply (wp)
      apply (simp add: isWaitingAEP_def aep_relation_def)
     apply (wp getAsyncEP_wp)
   apply (clarsimp simp: conj_comms st_tcb_at_tcb_at)
   apply (clarsimp simp: st_tcb_at_def obj_at_def)
   apply (erule pspace_valid_objsE)
    apply fastforce
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def)
   apply (drule sym, simp add: obj_at_def)
  apply (clarsimp simp: conj_comms pred_tcb_at' cong: conj_cong)
  apply (rule conjI)
   apply (simp add: pred_tcb_at'_def)
   apply (drule obj_at_ko_at')
   apply clarsimp
   apply (frule ko_at_valid_objs')
     apply fastforce
    apply (simp add: projectKOs)
   apply (clarsimp simp: valid_obj'_def valid_tcb'_def valid_tcb_state'_def)
   apply (drule sym, simp)
  apply (clarsimp simp: invs_weak_sch_act_wf)
  apply (drule sym_refs_st_tcb_atD', fastforce)
  apply (fastforce simp: isWaitingAEP_def ko_wp_at'_def obj_at'_def projectKOs
                         aep_bound_refs'_def
                  split: async_endpoint.splits aep.splits option.splits)
  done

lemma cte_map_tcb_2:
  "cte_map (t, tcb_cnode_index 2) = t + 0x20"
  by (simp add: cte_map_def tcb_cnode_index_def to_bl_1)

lemma reply_no_descendants_mdbNext_null:
  assumes descs: "descendants_of (t, tcb_cnode_index 2) (cdt s) = {}"
  and        sr: "(s, s') \<in> state_relation" 
  and      invs: "valid_reply_caps s" "valid_reply_masters s"
                 "valid_objs s" "valid_mdb s" "valid_mdb' s'" "pspace_aligned' s'"
                 "pspace_distinct' s'"
  and       tcb: "st_tcb_at (Not \<circ> halted) t s"
  and       cte: "ctes_of s' (t + 0x20) = Some cte"
  shows          "mdbNext (cteMDBNode cte) = nullPointer"
proof -
  from invs st_tcb_at_reply_cap_valid[OF tcb]
    have "cte_wp_at (op = (cap.ReplyCap t True)) (t, tcb_cnode_index 2) s"
    by (fastforce simp: cte_wp_at_caps_of_state is_cap_simps)
  hence "cteCap cte = capability.ReplyCap t True"
    using invs sr
    by (fastforce simp: cte_wp_at_ctes_of cte cte_map_def tcb_cnode_index_def
                 dest: pspace_relation_cte_wp_at state_relation_pspace_relation)
  hence class_link:
    "\<forall>cte'. ctes_of s' (mdbNext (cteMDBNode cte)) = Some cte' \<longrightarrow>
            capClass (cteCap cte') = ReplyClass t"
    using invs
    apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def)
    apply (drule class_linksD[where m="ctes_of s'", OF cte])
      apply (simp add: mdb_next_unfold cte)
     apply assumption
    apply simp
    done

  from invs tcb descs have "\<forall>ptr m.
      cte_wp_at (op = (cap.ReplyCap t m)) ptr s \<longrightarrow> ptr = (t, tcb_cnode_index 2)"
    apply (intro allI)
    apply (case_tac m)
     apply (clarsimp simp: invs_def valid_state_def valid_reply_masters_def)
    apply (fastforce simp: has_reply_cap_def
                    dest: st_tcb_at_tcb_at reply_master_no_descendants_no_reply)
    done
  hence "\<forall>ptr m mdb.
      ctes_of s' ptr = Some (CTE (capability.ReplyCap t m) mdb) \<longrightarrow> ptr = t + 0x20"
    using sr invs
    apply (intro allI impI)
    apply (drule(2) pspace_relation_cte_wp_atI
                    [OF state_relation_pspace_relation])
    apply (elim exE, case_tac c, simp_all del: split_paired_All)
    apply (elim allE, erule impE, fastforce)
    apply (clarsimp simp: cte_map_def tcb_cnode_index_def)
    done
  hence class_unique:
    "\<forall>ptr cte'. ctes_of s' ptr = Some cte' \<longrightarrow>
                capClass (cteCap cte') = ReplyClass t \<longrightarrow>
                ptr = t + 0x20"
    apply (intro allI impI)
    apply (case_tac cte', rename_tac cap node, case_tac cap, simp_all)
    apply (rename_tac arch_capability)
    apply (case_tac arch_capability, simp_all)
    done

  from invs have no_null: "ctes_of s' nullPointer = None"
    by (clarsimp simp: no_0_def nullPointer_def valid_mdb'_def valid_mdb_ctes_def)

  from invs cte have no_loop: "mdbNext (cteMDBNode cte) \<noteq> t + 0x20"
    by (fastforce simp: mdb_next_rel_def mdb_next_def
                       valid_mdb'_def
                 dest: valid_mdb_no_loops no_loops_direct_simp)

  from invs cte have
    "mdbNext (cteMDBNode cte) \<noteq> nullPointer \<longrightarrow>
     (\<exists>cte'. ctes_of s' (mdbNext (cteMDBNode cte)) = Some cte')"
    by (fastforce simp: valid_mdb'_def valid_mdb_ctes_def nullPointer_def
                 elim: valid_dlistEn)
  hence
    "mdbNext (cteMDBNode cte) \<noteq> nullPointer \<longrightarrow>
     mdbNext (cteMDBNode cte) = t + 0x20"
    using class_link class_unique
    by clarsimp
  thus ?thesis
    by (simp add: no_loop)
qed

lemma reply_descendants_mdbNext_nonnull:
  assumes descs: "descendants_of (t, tcb_cnode_index 2) (cdt s) \<noteq> {}"
  and        sr: "(s, s') \<in> state_relation" 
  and       tcb: "st_tcb_at (Not \<circ> halted) t s"
  and       cte: "ctes_of s' (t + 0x20) = Some cte"
  shows          "mdbNext (cteMDBNode cte) \<noteq> nullPointer"
proof -
  from tcb have "cte_at (t, tcb_cnode_index 2) s"
    by (simp add: st_tcb_at_tcb_at tcb_at_cte_at dom_tcb_cap_cases)
  hence "descendants_of' (t + 0x20) (ctes_of s') \<noteq> {}"
    using sr descs
    by (fastforce simp: state_relation_def cdt_relation_def cte_map_def tcb_cnode_index_def)
  thus ?thesis
    using cte unfolding nullPointer_def
    by (fastforce simp: descendants_of'_def dest: subtree_next_0)
qed

lemma reply_descendants_of_mdbNext:
  "\<lbrakk> (s, s') \<in> state_relation; valid_reply_caps s; valid_reply_masters s;
     valid_objs s; valid_mdb s; valid_mdb' s'; pspace_aligned' s';
     pspace_distinct' s'; st_tcb_at (Not \<circ> halted) t s;
     ctes_of s' (t + 0x20) = Some cte \<rbrakk> \<Longrightarrow> 
   (descendants_of (t, tcb_cnode_index 2) (cdt s) = {}) =
       (mdbNext (cteMDBNode cte) = nullPointer)"
  apply (case_tac "descendants_of (t, tcb_cnode_index 2) (cdt s) = {}")
   apply (simp add: reply_no_descendants_mdbNext_null)
  apply (simp add: reply_descendants_mdbNext_nonnull)
  done

lemma reply_mdbNext_is_descendantD:
  assumes sr: "(s, s') \<in> state_relation"
  and   invs: "invs' s'"
  and    tcb: "tcb_at t s"
  and    cte: "ctes_of s' (t + 0x20) = Some cte"
  and   desc: "descendants_of (t, tcb_cnode_index 2) (cdt s) = {sl}"
  shows       "mdbNext (cteMDBNode cte) = cte_map sl"
proof -
  from tcb have "cte_at (t, tcb_cnode_index 2) s"
    by (simp add: tcb_at_cte_at dom_tcb_cap_cases)
  hence "descendants_of' (t + 0x20) (ctes_of s') = {cte_map sl}"
    using sr desc
    by (fastforce simp: state_relation_def cdt_relation_def cte_map_def tcb_cnode_index_def)
  thus ?thesis
    using cte invs
    apply (clarsimp simp: descendants_of'_def)
    apply (frule singleton_eqD, drule CollectD)
    apply (erule subtree.cases)
     apply (clarsimp simp: mdb_next_rel_def mdb_next_def)
    apply (subgoal_tac "c' = cte_map sl")
     apply (fastforce dest: invs_no_loops no_loops_direct_simp)
    apply fastforce
    done
qed

locale delete_one_conc = delete_one_conc_pre +
  assumes delete_one_invs:
    "\<And>p. \<lbrace>invs'\<rbrace> cteDeleteOne p \<lbrace>\<lambda>rv. invs'\<rbrace>"

locale delete_one = delete_one_conc + delete_one_abs +
  assumes delete_one_corres:
    "corres dc (einvs and cte_wp_at can_fast_finalise ptr)
               (invs' and cte_at' (cte_map ptr))
          (cap_delete_one ptr) (cteDeleteOne (cte_map ptr))"

lemma (in delete_one) reply_ipc_cancel_corres:
  "corres dc (einvs  and st_tcb_at awaiting_reply t)
             (invs' and st_tcb_at' awaiting_reply' t)
      (reply_ipc_cancel t)
      (do y \<leftarrow> threadSet (\<lambda>tcb. tcb \<lparr> tcbFault := None \<rparr>) t;
          slot \<leftarrow> getThreadReplySlot t;
          callerCap \<leftarrow> liftM (mdbNext \<circ> cteMDBNode) (getCTE slot);
          when (callerCap \<noteq> nullPointer) (do
              y \<leftarrow> stateAssert (capHasProperty callerCap (\<lambda>cap. isReplyCap cap
                                                             \<and> \<not> capReplyMaster cap))
                  [];
              cteDeleteOne callerCap
          od)
       od)"
  apply (simp add: reply_ipc_cancel_def getThreadReplySlot_def
                   locateSlot_conv liftM_def cte_level_bits_def
                   tcbReplySlot_def
              del: split_paired_Ex)
  apply (rule_tac Q="\<lambda>_. invs and valid_list and valid_sched and st_tcb_at awaiting_reply t"
              and Q'="\<lambda>_. invs' and st_tcb_at' awaiting_reply' t"
               in corres_split')
     apply (rule corres_guard_imp)
       apply (rule threadset_corresT)
          apply (simp add: tcb_relation_def fault_rel_optionation_def)
         apply (simp add: tcb_cap_cases_def)
        apply (simp add: tcb_cte_cases_def)
       apply (simp add: exst_same_def)
      apply (clarsimp simp: st_tcb_at_tcb_at)
     apply clarsimp
    defer
    apply (wp thread_set_invs_trivial thread_set_no_change_tcb_state
              threadSet_invs_trivial threadSet_pred_tcb_no_state thread_set_not_state_valid_sched
         | fastforce simp: tcb_cap_cases_def inQ_def
         | wp_once sch_act_simple_lift)+
  apply (rule corres_split')
     apply (rule corres_guard_imp)
       apply (rule get_cap_corres [where cslot_ptr="(t, tcb_cnode_index 2)",
                                          simplified cte_map_tcb_2])
      apply (clarsimp dest!: st_tcb_at_tcb_at
                             tcb_at_cte_at [where ref="tcb_cnode_index 2"])
     apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
    defer
    apply (rule hoare_vcg_conj_lift [OF get_cap_inv get_cap_cte_wp_at, simplified])
   apply (rule hoare_vcg_conj_lift [OF getCTE_inv getCTE_cte_wp_at, simplified])
  apply (rename_tac cte)
  apply (rule corres_symb_exec_l [OF _ _ gets_sp])
    apply (rule_tac F="cap = cap.ReplyCap t True \<and>
                       cteCap cte = capability.ReplyCap t True" in corres_req)
     apply (fastforce simp: cte_wp_at_caps_of_state is_cap_simps
                     dest: st_tcb_at_reply_cap_valid)
    apply (rule_tac F="(descs = {}) = (mdbNext (cteMDBNode cte) = nullPointer)"
                 in corres_req)
     apply (fastforce simp: st_tcb_at_tcb_at cte_wp_at_ctes_of st_tcb_def2
                     dest: reply_descendants_of_mdbNext)
    apply (case_tac "descs = {}", simp add: when_def)
    apply (rule_tac F="\<exists>sl. descs = {sl}" in corres_req)
     apply (fastforce intro: st_tcb_at_tcb_at dest: reply_master_one_descendant)
    apply (erule exE, frule singleton_eqD)
    apply (rule_tac F="mdbNext (cteMDBNode cte) = cte_map sl" in corres_req)
     apply (clarsimp dest!: st_tcb_at_tcb_at)
     apply (fastforce simp: cte_wp_at_ctes_of
                    elim!: reply_mdbNext_is_descendantD)
    apply (simp add: when_def getSlotCap_def capHasProperty_def
                del: split_paired_Ex)
    apply (rule corres_guard_imp)
      apply (rule_tac P'="cte_wp_at (op = (cap.ReplyCap t False)) sl"
                   in corres_stateAssert_implied [OF delete_one_corres])
      apply (fastforce dest: pspace_relation_cte_wp_at
                            state_relation_pspace_relation
                      simp: cte_wp_at_ctes_of isCap_simps)
     apply (clarsimp simp: invs_def valid_state_def valid_mdb_def reply_mdb_def
                           reply_masters_mdb_def cte_wp_at_caps_of_state
                           can_fast_finalise_def)
    apply (fastforce simp: valid_mdb'_def valid_mdb_ctes_def
                          cte_wp_at_ctes_of nullPointer_def
                    elim: valid_dlistEn dest: invs_mdb')
   apply (simp add: exs_valid_def gets_def get_def return_def bind_def
               del: split_paired_Ex split_paired_All)
  apply (rule no_fail_pre, wp)
  done

lemma (in delete_one) ipc_cancel_corres:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t)
      (ipc_cancel t) (ipcCancel t)"
  apply (simp add: ipc_cancel_def ipcCancel_def Let_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ gts_corres])
      apply (rule_tac P="einvs and st_tcb_at (op = state) t" and 
                      P'="invs' and st_tcb_at' (op = statea) t" in corres_inst)
      apply (case_tac state, simp_all add: isTS_defs list_case_If)[1]
         apply (rule corres_guard_imp)
           apply (rule blocked_ipc_cancel_corres)
            apply fastforce
           apply fastforce
          apply simp
         apply simp
        apply (clarsimp simp add: isTS_defs list_case_If)
        apply (rule corres_guard_imp)
          apply (rule blocked_ipc_cancel_corres)
           apply fastforce
          apply fastforce
         apply simp
        apply simp
       apply (rule corres_guard_imp)
         apply (rule reply_ipc_cancel_corres)
        apply (clarsimp elim!: st_tcb_weakenE)
       apply (clarsimp elim!: pred_tcb'_weakenE)
      apply (rule corres_guard_imp [OF ac_corres], simp+)
     apply (wp gts_sp[where P="\<top>",simplified])
    apply (rule hoare_strengthen_post)
     apply (rule gts_sp'[where P="\<top>"])
    apply (clarsimp elim!: pred_tcb'_weakenE)
   apply simp
  apply simp
  done

lemma valid_ep_remove:
  "\<lbrakk> remove1 t (epQueue ep) \<noteq> []; valid_ep' ep s; ep \<noteq> IdleEP \<rbrakk> \<Longrightarrow>
  valid_ep' (epQueue_update (\<lambda>a. remove1 t (epQueue ep)) ep) s"
  apply (cases ep)
  apply (auto simp add: valid_ep'_def dest: subsetD [OF set_remove1_subset])
  done

(* Levity: added (20090201 10:50:13) *)
declare cart_singleton_empty [simp]

declare cart_singleton_empty2[simp]

crunch ksQ[wp]: setAsyncEP "\<lambda>s. P (ksReadyQueues s p)"
  (wp: setObject_queues_unchanged_tcb updateObject_default_inv)

lemma sch_act_simple_not_t[simp]: "sch_act_simple s \<Longrightarrow> sch_act_not t s"
  by (clarsimp simp: sch_act_simple_def)

lemma asyncIPCCancel_invs':
  "\<lbrace>invs' and st_tcb_at' (\<lambda>st. st = BlockedOnAsyncEvent aep) t and sch_act_not t\<rbrace>
    asyncIPCCancel t aep \<lbrace>\<lambda>rv. invs'\<rbrace>"
  proof -
    have NIQ: "\<And>s. \<lbrakk> Invariants_H.valid_queues s; st_tcb_at' (Not \<circ> runnable') t s \<rbrakk>
                                         \<Longrightarrow> \<forall>x. t \<notin> set (ksReadyQueues s x)"
      apply (clarsimp simp add: pred_tcb_at'_def Invariants_H.valid_queues_def)
      apply (drule spec | drule(1) bspec | clarsimp simp: obj_at'_def inQ_def)+
      done
    have AEPSN: "\<And>aep aep'.
                    \<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s \<rbrace> setAsyncEP aep aep'
                    \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
      apply (rule hoare_weaken_pre)
       apply (wps setAsyncEP_ksCurThread)
       apply (wp, simp)
      done
    show ?thesis
      apply (simp add: asyncIPCCancel_def invs'_def valid_state'_def Let_def)
      apply (wp valid_irq_node_lift sts_sch_act' irqs_masked_lift
                hoare_vcg_all_lift [OF setAsyncEP_ksQ] sts_valid_queues
                setThreadState_ct_not_inQ AEPSN
                hoare_vcg_all_lift setAsyncEP_ksQ
              | simp add: valid_tcb_state'_def list_case_If split del: split_if)+
      apply (rule hoare_strengthen_post)
       apply (rule get_aep_sp')
      apply (clarsimp simp: pred_tcb_at')
      apply (frule NIQ)
       apply (clarsimp simp: pred_tcb_at'_def obj_at'_def)
      apply (rule conjI)
       apply (clarsimp simp: valid_aep'_def)
       apply (case_tac "aepObj r", simp_all add: isWaitingAEP_def)
       apply (frule ko_at_valid_objs')
         apply (simp add: valid_pspace_valid_objs')
        apply (clarsimp simp: projectKO_opt_aep split: kernel_object.splits)
        apply (simp add: valid_obj'_def valid_aep'_def)
       apply (frule st_tcb_at_state_refs_ofD')
       apply (frule ko_at_state_refs_ofD')
       apply (rule conjI, erule delta_sym_refs)
         apply (clarsimp simp: aep_bound_refs'_def split: split_if_asm)
        apply (clarsimp split: split_if_asm)
          apply (fastforce simp: symreftype_inverse' aep_bound_refs'_def
                                 tcb_bound_refs'_def aep_q_refs_of'_def
                          split: aep.splits)
         apply (fastforce simp: symreftype_inverse' aep_bound_refs'_def
                                tcb_bound_refs'_def)
        apply (fastforce simp: symreftype_inverse' aep_bound_refs'_def
                               tcb_bound_refs'_def aep_q_refs_of'_def remove1_empty
                        split: aep.splits)
       apply (rule conjI, clarsimp elim!: if_live_state_refsE)
       apply (fastforce simp: sym_refs_def dest!: idle'_no_refs)
      apply (case_tac "aepObj r", simp_all)
      apply (frule obj_at_valid_objs', clarsimp)
      apply (clarsimp simp: projectKOs valid_obj'_def valid_aep'_def)
      apply (rule conjI, clarsimp split: option.splits)
      apply (frule st_tcb_at_state_refs_ofD')
      apply (frule ko_at_state_refs_ofD')
      apply (rule conjI)
       apply (erule delta_sym_refs)
        apply (fastforce simp: aep_bound_refs'_def split: split_if_asm)
       apply (clarsimp split: split_if_asm)
        apply (fastforce simp: symreftype_inverse' aep_bound_refs'_def tcb_bound_refs'_def
                               set_eq_subset)
       apply (fastforce simp: symreftype_inverse' aep_bound_refs'_def tcb_bound_refs'_def
                              set_eq_subset)
      apply (rule conjI, clarsimp elim!: if_live_state_refsE)
      apply (rule conjI)
       apply (case_tac "aepBoundTCB r")
        apply (clarsimp elim!: if_live_state_refsE)+
            apply (rule conjI, clarsimp split: option.splits)
      apply (clarsimp dest!: idle'_no_refs)
      done
  qed

lemmas setEndpoint_valid_arch[wp]
    = valid_arch_state_lift' [OF setEndpoint_typ_at' setEndpoint_ksArchState]

(* Levity: added (20090201 10:50:13) *)
declare setEndpoint_ksArch [wp]

lemma setEndpoint_irq_node'[wp]:
  "\<lbrace>\<lambda>s. P (irq_node' s)\<rbrace>
     setEndpoint ep_ptr val
   \<lbrace>\<lambda>_ s. P (irq_node' s)\<rbrace>"
  apply (simp add: setEndpoint_def setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma ep_redux_simps3:
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> RecvEP (y # ys))
        = (set xs \<times> {EPRecv})"
  "ep_q_refs_of' (case xs of [] \<Rightarrow> IdleEP | y # ys \<Rightarrow> SendEP (y # ys))
        = (set xs \<times> {EPSend})"
  by (fastforce split: list.splits
                simp: valid_ep_def valid_aep_def
              intro!: ext)+

lemma setEndpoint_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> setEndpoint ptr val \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (wp valid_pde_mappings_lift')
  apply (simp add: setEndpoint_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp dest!: updateObject_default_result)
  done

(* Levity: added (20090126 19:32:18) *)
declare setEndpoint_ksMachine [wp]

(* Levity: added (20090201 10:50:14) *)
declare setEndpoint_valid_irq_states' [wp]

lemma setEndpoint_vms[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setEndpoint epptr ep' \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  by (simp add: valid_machine_state'_def pointerInUserData_def)
     (wp hoare_vcg_all_lift hoare_vcg_disj_lift)

crunch ksQ[wp]: setEndpoint "\<lambda>s. P (ksReadyQueues s p)"
  (wp: setObject_queues_unchanged_tcb updateObject_default_inv)

crunch sch_act_not[wp]: setEndpoint "sch_act_not t"

crunch ksCurDomain[wp]: setEndpoint "\<lambda>s. P (ksCurDomain s)"
  (wp: setObject_ep_cur_domain ignore: setObject)

lemma setEndpoint_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setEndpoint ptr ep \<lbrace>\<lambda>_ s. P (ksDomSchedule s)\<rbrace>"
apply (simp add: setEndpoint_def setObject_def split_def)
apply (wp updateObject_default_inv | simp)+
done

lemma setEndpoint_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace> ct_idle_or_in_cur_domain' \<rbrace> setEndpoint ptr ep \<lbrace> \<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
  apply (wp hoare_vcg_disj_lift hoare_vcg_imp_lift setObject_ep_ct
       | rule obj_at_setObject2
       | clarsimp simp: updateObject_default_def in_monad setEndpoint_def)+
  done

lemma setEndpoint_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> setEndpoint eeptr ep' \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF setEndpoint_nosch])
  apply (simp add: setEndpoint_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_ep_ct)
   apply (wp obj_at_setObject2)
   apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setEndpoint_ksDomScheduleIdx[wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setEndpoint ptr ep \<lbrace>\<lambda>_ s. P (ksDomScheduleIdx s)\<rbrace>"
apply (simp add: setEndpoint_def setObject_def split_def)
apply (wp updateObject_default_inv | simp)+
done

lemma (in delete_one_conc) ipcCancel_invs[wp]:
  shows "\<lbrace>tcb_at' t and invs'\<rbrace> ipcCancel t \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have P: "\<And>xs v f. (case xs of [] \<Rightarrow> return v | y # ys \<Rightarrow> return (f (y # ys)))
                         = return (case xs of [] \<Rightarrow> v | y # ys \<Rightarrow> f xs)"
    by (clarsimp split: list.split)
  have NIQ: "\<And>s. \<lbrakk> Invariants_H.valid_queues s; st_tcb_at' (Not \<circ> runnable') t s \<rbrakk>
                                       \<Longrightarrow> \<forall>x. t \<notin> set (ksReadyQueues s x)"
    apply (clarsimp simp add: pred_tcb_at'_def Invariants_H.valid_queues_def)
    apply (drule spec | drule(1) bspec | clarsimp simp: obj_at'_def inQ_def)+
    done
  have EPSCHN: "\<And>eeptr ep'. \<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s\<rbrace>
                             setEndpoint eeptr ep'
                             \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
    apply (rule hoare_weaken_pre)
     apply (wps setEndpoint_ct')
     apply (wp, simp)
    done
  have Q:
    "\<And>epptr. \<lbrace>st_tcb_at' (\<lambda>st. (\<exists>x. st = BlockedOnReceive epptr x)
                            \<or> (\<exists>a b c. st = BlockedOnSend epptr a b c)) t
                  and invs'\<rbrace>
      do ep \<leftarrow> getEndpoint epptr;
         y \<leftarrow> assert (\<not> (case ep of IdleEP \<Rightarrow> True | _ \<Rightarrow> False));
         ep' \<leftarrow> case remove1 t (epQueue ep)
                of [] \<Rightarrow> return Structures_H.endpoint.IdleEP
                | x # xs \<Rightarrow> return (epQueue_update (%_. x # xs) ep);
         y \<leftarrow> setEndpoint epptr ep';
         setThreadState Inactive t
      od \<lbrace>\<lambda>rv. invs'\<rbrace>"
    apply (simp add: invs'_def valid_state'_def)
    apply (subst P)
    apply (wp valid_irq_node_lift valid_global_refs_lift' valid_arch_state_lift'
              irqs_masked_lift sts_sch_act'
              hoare_vcg_all_lift [OF setEndpoint_ksQ]
              sts_valid_queues setThreadState_ct_not_inQ EPSCHN
              hoare_vcg_all_lift setAsyncEP_ksQ
              | simp add: valid_tcb_state'_def split del: split_if
              | wpc)+
    apply (rule hoare_strengthen_post [OF get_ep_sp'])
    apply (clarsimp simp: pred_tcb_at' fun_upd_def[symmetric] conj_comms
               split del: split_if cong: if_cong)
    apply (rule conjI, clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def projectKOs)
    apply (frule obj_at_valid_objs', clarsimp)
    apply (clarsimp simp: projectKOs valid_obj'_def)
    apply (rule conjI)
     apply (clarsimp simp: obj_at'_def valid_ep'_def projectKOs 
                    dest!: pred_tcb_at')
    apply (frule NIQ)
     apply (erule pred_tcb'_weakenE, fastforce)
    apply (clarsimp, rule conjI)
     apply (auto simp: pred_tcb_at'_def obj_at'_def)[1]
    apply (rule conjI)
     apply (clarsimp split: Structures_H.endpoint.split_asm list.split
                      simp: valid_ep'_def)
      apply (rename_tac list x xs)
      apply (frule distinct_remove1[where x=t])
      apply (cut_tac xs=list in set_remove1_subset[where x=t])
      apply auto[1]
     apply (rename_tac list x xs)
     apply (frule distinct_remove1[where x=t])
     apply (cut_tac xs=list in set_remove1_subset[where x=t])
     apply auto[1]
    apply (frule(1) sym_refs_ko_atD')
    apply (rule conjI)
     apply (clarsimp elim!: if_live_state_refsE split: Structures_H.endpoint.split_asm)
    apply (drule st_tcb_at_state_refs_ofD')
    apply (clarsimp simp: ep_redux_simps3 valid_ep'_def
                   split: Structures_H.endpoint.split_asm
                    cong: list.case_cong)
     apply (frule_tac x=t in distinct_remove1)
     apply (frule_tac x=t in set_remove1_eq)
     apply (auto elim!: delta_sym_refs
                  simp: symreftype_inverse' tcb_st_refs_of'_def tcb_bound_refs'_def 
                 split: thread_state.splits split_if_asm)
    done
  have R:
    "\<lbrace>invs' and tcb_at' t\<rbrace>
     do y \<leftarrow> threadSet (\<lambda>tcb. tcb \<lparr> tcbFault := None \<rparr>) t;
        slot \<leftarrow> getThreadReplySlot t;
        callerCap \<leftarrow> liftM (mdbNext \<circ> cteMDBNode) (getCTE slot);
        when (callerCap \<noteq> nullPointer) (do
            y \<leftarrow> stateAssert (capHasProperty callerCap (\<lambda>cap. isReplyCap cap
                                                           \<and> \<not> capReplyMaster cap))
                [];
            cteDeleteOne callerCap
        od)
     od 
     \<lbrace>\<lambda>rv. invs'\<rbrace>"
    unfolding getThreadReplySlot_def
    by (wp valid_irq_node_lift delete_one_invs hoare_drop_imps
           threadSet_invs_trivial irqs_masked_lift
      | simp add: o_def if_apply_def2
      | fastforce simp: inQ_def)+
  show ?thesis
    apply (simp add:   ipcCancel_def crunch_simps
               cong:   if_cong list.case_cong)
    apply (rule hoare_seq_ext [OF _ gts_sp'])
    apply (case_tac state,
           simp_all add: isTS_defs)
           apply (safe intro!:  
                                hoare_weaken_pre[OF Q]
                                hoare_weaken_pre[OF R]
                                hoare_weaken_pre[OF return_wp]
                                hoare_weaken_pre[OF asyncIPCCancel_invs']
                       elim!: invs_valid_objs' pred_tcb'_weakenE)
          apply (auto simp: pred_tcb_at'_def obj_at'_def
                      dest: invs_sch_act_wf')
  done
qed

lemma (in delete_one_conc_pre) ipcCancel_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace>
    ipcCancel t
   \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (simp add: ipcCancel_def asyncIPCCancel_def Let_def
             cong: if_cong Structures_H.thread_state.case_cong)
  apply (wp hoare_drop_imps delete_one_sch_act_simple
       | simp add: getThreadReplySlot_def | wpcw
       | rule sch_act_simple_lift
       | (rule_tac Q="\<lambda>rv. sch_act_simple" in hoare_post_imp, simp))+
  done

lemma asyncIPCCancel_st_tcb_at:
  assumes x[simp]: "P Inactive" shows
  "\<lbrace>st_tcb_at' P t\<rbrace>
     asyncIPCCancel t' aep
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: asyncIPCCancel_def Let_def list_case_If)
  apply (wp sts_st_tcb_at'_cases hoare_vcg_const_imp_lift
            hoare_drop_imp[where R="%rv s. P' rv" for P'])
   apply clarsimp+
  done

lemma (in delete_one_conc_pre) ipcCancel_st_tcb_at:
  assumes x[simp]: "\<And>st. simple' st \<longrightarrow> P st" shows
  "\<lbrace>st_tcb_at' P t\<rbrace>
     ipcCancel t'
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: ipcCancel_def Let_def getThreadReplySlot_def
             cong: if_cong Structures_H.thread_state.case_cong)
  apply (rule hoare_seq_ext [OF _ gts_sp'])
  apply (case_tac x, simp_all add: isTS_defs list_case_If
                                   isBlockedOnAsyncEvent_def)
         apply (wp sts_st_tcb_at'_cases delete_one_st_tcb_at
                   threadSet_pred_tcb_no_state
                   asyncIPCCancel_st_tcb_at hoare_drop_imps
                | clarsimp
                )+
  done

lemma weak_sch_act_wf_lift_linear:
  "\<lbrakk> \<And>t. \<lbrace>\<lambda>s. sa s \<noteq> SwitchToThread t\<rbrace> f \<lbrace>\<lambda>rv s. sa s \<noteq> SwitchToThread t\<rbrace>;
     \<And>t. \<lbrace>st_tcb_at' runnable' t\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at' runnable' t\<rbrace>;
     \<And>t. \<lbrace>tcb_in_cur_domain' t\<rbrace> f \<lbrace>\<lambda>rv. tcb_in_cur_domain' t\<rbrace> \<rbrakk>
       \<Longrightarrow> \<lbrace>\<lambda>s. weak_sch_act_wf (sa s) s\<rbrace> f \<lbrace>\<lambda>rv s. weak_sch_act_wf (sa s) s\<rbrace>"
  apply (simp only: weak_sch_act_wf_def imp_conv_disj)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_conj_lift)
  apply simp_all
  done

lemma sts_sch_act_not[wp]:
  "\<lbrace>sch_act_not t\<rbrace> setThreadState st t' \<lbrace>\<lambda>rv. sch_act_not t\<rbrace>"
  apply (simp add: setThreadState_def rescheduleRequired_def)
  apply (wp hoare_drop_imps | simp | wpcw)+
  done

crunch sch_act_not[wp]: asyncIPCCancel, setBoundAEP "sch_act_not t"
  (wp: crunch_wps)

lemma asyncIPCCancel_tcb_at_runnable':
  "t \<noteq> t' \<Longrightarrow>
  \<lbrace>st_tcb_at' runnable' t'\<rbrace> asyncIPCCancel t aepptr \<lbrace>\<lambda>_. st_tcb_at' runnable' t'\<rbrace>"
  (is "_ \<Longrightarrow> \<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: asyncIPCCancel_def)
  apply (wp sts_pred_tcb_neq' | wpc | simp)+
  apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, fastforce)
  apply (wp)
  done

lemma epCancelAll_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> epCancelAll epptr \<lbrace>\<lambda>_. st_tcb_at' runnable' t\<rbrace>"
  apply (clarsimp simp add: epCancelAll_def)
  apply (wp mapM_x_wp [OF _ subset_refl] sts_st_tcb' | wpc | simp)+
  apply (rule_tac Q="\<lambda>_. st_tcb_at' runnable' t" in hoare_post_imp, simp)
  apply (wp)
  done

lemma aepCancelAll_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> aepCancelAll aepptr \<lbrace>\<lambda>_. st_tcb_at' runnable' t\<rbrace>"
  apply (clarsimp simp add: aepCancelAll_def)
  apply (wp mapM_x_wp [OF _ subset_refl] sts_st_tcb' | wpc | simp)+
  apply (rule_tac Q="\<lambda>_. st_tcb_at' runnable' t" in hoare_post_imp, simp)
  apply (wp)
  done

crunch st_tcb_at'[wp]: unbindAsyncEndpoint, bindAsyncEndpoint, unbindMaybeAEP "st_tcb_at' P p"
(wp: threadSet_pred_tcb_no_state ignore: threadSet)

lemma (in delete_one_conc_pre) finaliseCap_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> finaliseCap cap final True \<lbrace>\<lambda>_. st_tcb_at' runnable' t\<rbrace>"
  apply (clarsimp simp add: finaliseCap_def Let_def)
  apply (rule conjI | clarsimp | wp epCancelAll_tcb_at_runnable' getObject_aep_inv
                                    aepCancelAll_tcb_at_runnable'
       | wpc)+
  done

crunch pred_tcb_at'[wp]: isFinalCapability "pred_tcb_at' proj st t"
  (simp: crunch_simps)

lemma (in delete_one_conc_pre) cteDeleteOne_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t\<rbrace> cteDeleteOne callerCap \<lbrace>\<lambda>_. st_tcb_at' runnable' t\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def)
  apply (wp | clarsimp)+
     apply (assumption)
    apply (wp finaliseCap_tcb_at_runnable' | clarsimp)+
  done

crunch pred_tcb_at'[wp]: getThreadReplySlot, getEndpoint "pred_tcb_at' proj st t"

lemma (in delete_one_conc_pre) ipcCancel_tcb_at_runnable':
  "\<lbrace>st_tcb_at' runnable' t'\<rbrace> ipcCancel t \<lbrace>\<lambda>_. st_tcb_at' runnable' t'\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (clarsimp simp: ipcCancel_def Let_def)
  apply (case_tac "t'=t")
   apply (rule_tac B="\<lambda>st. st_tcb_at' runnable' t and K (runnable' st)"
            in hoare_seq_ext)
    apply(case_tac x)
           apply (clarsimp | wp)+
   apply (wpc)
          apply (wp sts_pred_tcb_neq' | simp | wpc)+
          apply (clarsimp)
          apply (rule_tac Q="\<lambda>rv. ?PRE" in hoare_post_imp, fastforce)
          apply (wp cteDeleteOne_tcb_at_runnable'
                    threadSet_pred_tcb_no_state
                    asyncIPCCancel_tcb_at_runnable'
                    sts_pred_tcb_neq'
                 | wpc | simp)+
    apply (rule_tac Q="\<lambda>rv. ?PRE" in hoare_post_imp, fastforce)
    apply (wp)
  apply (rule_tac Q="\<lambda>rv. ?PRE" in hoare_post_imp, fastforce)
  apply (wp)
  done

crunch ksCurDomain[wp]: asyncIPCCancel "\<lambda>s. P (ksCurDomain s)"
  (wp: crunch_wps)

lemma (in delete_one_conc_pre) ipcCancel_ksCurDomain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> ipcCancel t \<lbrace>\<lambda>_ s. P (ksCurDomain s)\<rbrace>"
apply (simp add: ipcCancel_def Let_def)
apply (wp hoare_vcg_conj_lift delete_one_ksCurDomain
     | wpc
     | rule hoare_drop_imps
     | simp add: getThreadReplySlot_def)+
done

(* FIXME move *)
lemma tcbSchedEnqueue_not_st:
  "(\<And>tcb st qd. P (tcb\<lparr>tcbState := st, tcbQueued := qd\<rparr>) \<longleftrightarrow> P tcb)
     \<Longrightarrow> \<lbrace>obj_at' P t'\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. obj_at' P t'\<rbrace>"
apply (simp add: tcbSchedEnqueue_def unless_def)
apply (wp threadGet_wp | simp)+
apply (clarsimp simp: obj_at'_def)
apply (case_tac obja)
apply fastforce
done

(* FIXME move *)
lemma setThreadState_not_st:
  "(\<And>tcb st qd. P (tcb\<lparr>tcbState := st, tcbQueued := qd\<rparr>) \<longleftrightarrow> P tcb)
     \<Longrightarrow> \<lbrace>obj_at' P t'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. obj_at' P t'\<rbrace>"
apply (simp add: setThreadState_def rescheduleRequired_def)
apply (wp hoare_vcg_conj_lift tcbSchedEnqueue_not_st
     | wpc
     | rule hoare_drop_imps
     | simp)+
apply (clarsimp simp: obj_at'_def)
apply (case_tac obj)
apply fastforce
done

lemma setBoundAEP_not_aep:
  "(\<And>tcb aep. P (tcb\<lparr>tcbBoundAEP := aep\<rparr>) \<longleftrightarrow> P tcb)
     \<Longrightarrow> \<lbrace>obj_at' P t'\<rbrace> setBoundAEP aep t \<lbrace>\<lambda>_. obj_at' P t'\<rbrace>"
  apply (simp add: setBoundAEP_def)
  apply (wp hoare_vcg_conj_lift 
     | wpc
     | rule hoare_drop_imps
     | simp)+
  done

(* FIXME move *)
lemma setThreadState_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> setThreadState st t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
apply (simp add: tcb_in_cur_domain'_def)
apply (rule hoare_pre)
apply wps
apply (wp setThreadState_not_st | simp)+
done

lemma setBoundAEP_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> setBoundAEP st t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
  apply (simp add: tcb_in_cur_domain'_def)
  apply (rule hoare_pre)
  apply wps
  apply (wp setBoundAEP_not_aep | simp)+
  done

lemma asyncIPCCancel_tcb_obj_at':
  "(\<And>tcb st qd. P (tcb\<lparr>tcbState := st, tcbQueued := qd\<rparr>) \<longleftrightarrow> P tcb)
     \<Longrightarrow> \<lbrace>obj_at' P t'\<rbrace> asyncIPCCancel t word \<lbrace>\<lambda>_. obj_at' P t'\<rbrace>"
apply (simp add: asyncIPCCancel_def setAsyncEP_def)
apply (wp setThreadState_not_st getAsyncEP_wp | wpc | simp)+
done

lemma (in delete_one_conc_pre) ipcCancel_tcbDomain_obj_at':
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace> ipcCancel t \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
apply (simp add: ipcCancel_def Let_def)
apply (wp hoare_vcg_conj_lift
          setThreadState_not_st delete_one_tcbDomain_obj_at' asyncIPCCancel_tcb_obj_at'
     | wpc
     | rule hoare_drop_imps
     | simp add: getThreadReplySlot_def)+
done

lemma (in delete_one_conc_pre) ipcCancel_tcb_in_cur_domain':
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> ipcCancel t \<lbrace>\<lambda>_. tcb_in_cur_domain' t'\<rbrace>"
apply (simp add: tcb_in_cur_domain'_def)
apply (rule hoare_pre)
apply wps
apply (wp ipcCancel_tcbDomain_obj_at' | simp)+
done

lemma (in delete_one_conc_pre) ipcCancel_sch_act_not:
  "\<lbrace>sch_act_not t'\<rbrace> ipcCancel t \<lbrace>\<lambda>_. sch_act_not t'\<rbrace>"
  apply (simp add: ipcCancel_def Let_def)
  apply (wp hoare_vcg_conj_lift
            delete_one_sch_act_not
       | wpc
       | simp add: getThreadReplySlot_def o_def if_apply_def2
              split del: if_splits
       | rule hoare_drop_imps)+
  done

lemma (in delete_one_conc_pre) ipcCancel_weak_sch_act_wf:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
      ipcCancel t
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (rule weak_sch_act_wf_lift_linear)
  apply (wp ipcCancel_sch_act_not ipcCancel_tcb_in_cur_domain' ipcCancel_tcb_at_runnable')
  done

text {* The suspend operation, significant as called from delete *}

lemma rescheduleRequired_weak_sch_act_wf:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: rescheduleRequired_def setSchedulerAction_def)
  apply (wp hoare_post_taut | simp add: weak_sch_act_wf_def)+
  done

lemma sts_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s
        \<and> (ksSchedulerAction s = SwitchToThread t \<longrightarrow> runnable' st)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp rescheduleRequired_weak_sch_act_wf)
  apply (rule_tac Q="\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s"
           in hoare_post_imp, simp)
  apply (simp add: weak_sch_act_wf_def)
  apply (wp hoare_vcg_all_lift)
   apply (wps threadSet_nosch)
   apply (wp hoare_vcg_const_imp_lift threadSet_pred_tcb_at_state threadSet_tcbDomain_triv | simp)+
  done

lemma sba_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setBoundAEP aep t \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: setBoundAEP_def, wp threadSet_nosch)
  

lemma sba_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
   setBoundAEP aep t
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wp weak_sch_act_wf_lift sba_st_tcb')


lemma set_ep_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
     setEndpoint epptr ep
   \<lbrace>\<lambda>rv s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (wp weak_sch_act_wf_lift)
  done

lemma setObject_aep_sa_unchanged[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
    setObject ptr (aep::async_endpoint)
   \<lbrace>\<lambda>rv s.  P (ksSchedulerAction s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp | simp add: updateObject_default_def)+
  done

lemma setObject_oa_unchanged[wp]:
  "\<lbrace>\<lambda>s. obj_at' (\<lambda>tcb::tcb. P tcb) t s\<rbrace>
    setObject ptr (aep::async_endpoint)
   \<lbrace>\<lambda>rv s.  obj_at' P t s\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_type
                            updateObject_default_def
                            in_monad)
  done

lemma setAsyncEP_weak_sch_act_wf[wp]:
  "\<lbrace>\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>
    setAsyncEP aepptr aep
   \<lbrace>\<lambda>_ s. weak_sch_act_wf (ksSchedulerAction s) s\<rbrace>"
apply (wp hoare_vcg_all_lift hoare_convert_imp
          hoare_vcg_conj_lift
     | simp add: setAsyncEP_def weak_sch_act_wf_def st_tcb_at'_def
                 tcb_in_cur_domain'_def)+
apply (rule hoare_pre)
apply (wps setObject_aep_cur_domain)
apply (wp setObject_aep_obj_at'_tcb | simp)+
done

lemmas ipccancel_weak_sch_act_wfs
    = weak_sch_act_wf_lift[OF _ setCTE_pred_tcb_at']

lemma tcbSchedDequeue_corres':
  "corres dc (is_etcb_at t) (tcb_at' t and valid_inQ_queues) (tcb_sched_action (tcb_sched_dequeue) t) (tcbSchedDequeue t)"
  apply (simp only: tcbSchedDequeue_def tcb_sched_action_def)
  apply (rule corres_symb_exec_r[OF _ _ threadGet_inv, where Q'="\<lambda>rv. tcb_at' t and valid_inQ_queues and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"])
    defer
    apply (wp threadGet_obj_at', simp, simp)
   apply (rule no_fail_pre, wp, simp)
  apply (case_tac queued)
   defer
   apply (simp add: unless_def when_def)
   apply (rule corres_no_failI)
    apply (rule no_fail_pre, wp)
   apply (clarsimp simp: in_monad ethread_get_def get_etcb_def set_tcb_queue_def is_etcb_at_def state_relation_def gets_the_def gets_def get_def return_def bind_def assert_opt_def get_tcb_queue_def modify_def put_def)
   apply (subgoal_tac "t \<notin> set (ready_queues a (tcb_domain y) (tcb_priority y))")
    prefer 2
    apply (force simp: tcb_sched_dequeue_def valid_inQ_queues_def
           ready_queues_relation_def obj_at'_def inQ_def projectKO_eq project_inject)
   apply (simp add: ready_queues_relation_def)
  apply (simp add: unless_def when_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="op =", OF _ ethreadget_corres])
       apply simp
       apply (rule corres_split_eqr[OF _ ethreadget_corres])
          apply (rule corres_split_eqr[OF _ getQueue_corres])
            apply simp
            apply (subst bind_return_unit, rule corres_split[where r'=dc])
               apply (simp add: dc_def[symmetric])
               apply (rule threadSet_corres_noop, simp_all add: tcb_relation_def exst_same_def)[1]
              apply (simp add: tcb_sched_dequeue_def)
              apply (rule setQueue_corres)
             apply (wp | simp add: etcb_relation_def)+
   apply (force simp: etcb_at_def split: option.splits)
  apply simp
  done

lemma setQueue_valid_inQ_queues:
  "\<lbrace>valid_inQ_queues
      and (\<lambda>s. \<forall>t \<in> set ts. obj_at' (inQ d p) t s)
      and K (distinct ts)\<rbrace> 
  setQueue d p ts 
  \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: setQueue_def valid_inQ_queues_def)
  apply wp
  apply clarsimp
  done

lemma threadSet_valid_inQ_queues:
  "\<lbrace>valid_inQ_queues and (\<lambda>s. \<forall>d p. (\<exists>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb)))
                        \<longrightarrow> obj_at' (\<lambda>tcb. (inQ d p tcb) \<and> \<not>(inQ d p (f tcb))) t s
                        \<longrightarrow> t \<notin> set (ksReadyQueues s (d, p)))\<rbrace>
     threadSet f t
   \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  apply (simp add: threadSet_def)
  apply wp
   apply (simp add: valid_inQ_queues_def pred_tcb_at'_def)
   apply (wp setObject_queues_unchanged_tcb
             hoare_Ball_helper
             hoare_vcg_all_lift
             setObject_tcb_strongest)[1]
  apply (wp getObject_tcb_wp)
  apply (clarsimp simp: valid_inQ_queues_def pred_tcb_at'_def)
  apply (clarsimp simp: obj_at'_def projectKOs)
  apply (fastforce)
  done

lemma tcbSchedEnqueue_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def setQueue_after)
  apply (rule hoare_pre)
   apply (rule_tac B="\<lambda>rv. valid_inQ_queues and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
                in hoare_seq_ext)
    apply (rename_tac queued)
    apply (case_tac queued, simp_all add: unless_def when_def)[1]
     apply (wp setQueue_valid_inQ_queues threadSet_valid_inQ_queues threadGet_wp
               hoare_vcg_const_Ball_lift
          | simp add: inQ_def
          | fastforce simp: valid_inQ_queues_def inQ_def obj_at'_def)+
     done

lemma tcbSchedDequeue_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (rule hoare_pre)
   apply (rule_tac B="\<lambda>rv. valid_inQ_queues and obj_at' (\<lambda>obj. tcbQueued obj = rv) t"
                in hoare_seq_ext)
    apply (rename_tac queued)
    apply (case_tac queued, simp_all add: when_def)[1]
     apply (wp threadSet_valid_inQ_queues setQueue_valid_inQ_queues threadGet_wp
          | simp add: setQueue_def
          | fastforce simp: valid_inQ_queues_def inQ_def obj_at'_def)+
  done

lemma rescheduleRequired_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | wpc | simp | clarsimp simp: valid_inQ_queues_def)+
  done

lemma sts_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (wp threadSet_valid_inQ_queues [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def inQ_def)+
  done

lemma updateObject_ep_inv:
  "\<lbrace>P\<rbrace> updateObject (obj::endpoint) ko p q n \<lbrace>\<lambda>rv. P\<rbrace>"
  by simp (rule updateObject_default_inv)

lemma sba_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> setBoundAEP aep t \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  apply (simp add: setBoundAEP_def)
  apply (wp threadSet_valid_inQ_queues [THEN hoare_strengthen_post])
   apply (clarsimp simp: sch_act_simple_def Invariants_H.valid_queues_def inQ_def)+
  done

lemma setEndpoint_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> setEndpoint ptr ep \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  apply (unfold setEndpoint_def)
  apply (rule setObject_ep_pre)
  apply (simp add: valid_inQ_queues_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift setObject_queues_unchanged[OF updateObject_ep_inv])
  apply simp
  done

lemma set_aep_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> setAsyncEP ptr aep \<lbrace>\<lambda>rv. valid_inQ_queues\<rbrace>"
  apply (unfold setAsyncEP_def)
  apply (rule setObject_aep_pre)
  apply (simp add: valid_inQ_queues_def)
  apply (wp hoare_Ball_helper hoare_vcg_all_lift)
    apply (clarsimp simp: updateObject_default_def in_monad)
    apply (wp updateObject_default_inv | simp)+
    done

crunch valid_inQ_queues[wp]: asyncIPCCancel valid_inQ_queues
  (ignore: updateObject setObject simp: updateObject_tcb_inv crunch_simps wp: crunch_wps)

lemma (in delete_one_conc_pre) ipcCancel_valid_inQ_queues[wp]:
  "\<lbrace>valid_inQ_queues\<rbrace> ipcCancel t \<lbrace>\<lambda>_. valid_inQ_queues\<rbrace>"
  apply (simp add: ipcCancel_def Let_def getThreadReplySlot_def)
  apply (wp hoare_drop_imps delete_one_inQ_queues threadSet_valid_inQ_queues | wpc | simp add:if_apply_def2 Fun.comp_def)+
   apply (clarsimp simp: valid_inQ_queues_def inQ_def)+
   done

lemma valid_queues_inQ_queues:
  "Invariants_H.valid_queues s \<Longrightarrow> valid_inQ_queues s"
  apply (force simp: Invariants_H.valid_queues_def valid_inQ_queues_def obj_at'_def)
  done

lemma (in delete_one) suspend_corres:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t)
        (IpcCancel_A.suspend t) (ThreadDecls_H.suspend t)"
  apply (simp add: IpcCancel_A.suspend_def Thread_H.suspend_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor [OF _ ipc_cancel_corres])
      apply (rule corres_split_nor [OF _ sts_corres])
         apply (rule tcbSchedDequeue_corres')
        apply simp
       apply (wp | simp)+
   apply (force simp: valid_sched_def tcb_at_is_etcb_at)
  apply (clarsimp simp add: invs'_def valid_state'_def valid_queues_inQ_queues)
  done

lemma no_refs_simple_strg':
  "st_tcb_at' simple' t s' \<and> P {} \<longrightarrow> st_tcb_at' (\<lambda>st. P (tcb_st_refs_of' st)) t s'"
  by (fastforce elim!: pred_tcb'_weakenE)+

crunch it[wp]: asyncIPCCancel "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps simp: crunch_simps
        ignore: getObject setObject)

lemma (in delete_one_conc_pre) ipcCancel_it[wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>
   ipcCancel t  
   \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  apply (simp add: ipcCancel_def Let_def getThreadReplySlot_def)
  apply (wp hoare_drop_imps delete_one_it | wpc | simp add:if_apply_def2 Fun.comp_def)+
  done

crunch ksQ: threadGet "\<lambda>s. P (ksReadyQueues s p)"

lemma threadGet_ksQ_oa:
  "\<lbrace>\<lambda>s. obj_at' (op = p \<circ> f) t s \<and> P (g p (ksReadyQueues s p) s)\<rbrace>
    threadGet f t
   \<lbrace>\<lambda>rv s. P (g rv (ksReadyQueues s rv) s)\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (wps threadGet_ksQ)
  apply (wp threadGet_const)
  apply (clarsimp elim!:obj_at'_weakenE)
  done

lemma tcbSchedDequeue_notksQ:
  "\<lbrace>\<lambda>s. t' \<notin> set(ksReadyQueues s p)\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. t' \<notin> set(ksReadyQueues s p)\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp)
   apply (rule_tac Q="\<lambda>_ s. t' \<notin> set(ksReadyQueues s p)" in hoare_post_imp)
    apply (wp | clarsimp)+
  done

lemma rescheduleRequired_oa_queued:
  "\<lbrace> (\<lambda>s. P (obj_at' (\<lambda>tcb. Q (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s)) and sch_act_simple\<rbrace>
    rescheduleRequired
   \<lbrace>\<lambda>_ s. P (obj_at' (\<lambda>tcb. Q (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s)\<rbrace>"
  (is "\<lbrace>?OAQ t' p and sch_act_simple\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: rescheduleRequired_def sch_act_simple_def)
  apply (rule_tac B="\<lambda>rv s. (rv = ResumeCurrentThread \<or> rv = ChooseNewThread)
                       \<and> ?OAQ t' p s" in hoare_seq_ext)
   apply (wp | clarsimp)+
   apply (case_tac x)
     apply (wp | clarsimp)+
  done

lemma setThreadState_oa_queued:
  "\<lbrace>\<lambda>s. P' (obj_at' (\<lambda>tcb. P (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s) \<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_ s. P' (obj_at' (\<lambda>tcb. P (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s) \<rbrace>"
  (is "\<lbrace>\<lambda>s. P' (?Q P s)\<rbrace> _ \<lbrace>\<lambda>_ s. P' (?Q P s)\<rbrace>")
  proof (rule P_bool_lift [where P=P'])
    show pos:
      "\<And>R. \<lbrace> ?Q R \<rbrace> setThreadState st t \<lbrace>\<lambda>_. ?Q R \<rbrace>"
      apply (simp add: setThreadState_def)
      apply (wp rescheduleRequired_oa_queued)
      apply (simp add: sch_act_simple_def)
      apply (rule_tac Q="\<lambda>_. ?Q R" in hoare_post_imp, clarsimp)
      apply (wp threadSet_obj_at'_strongish)
      apply (clarsimp)
      done
    show "\<lbrace>\<lambda>s. \<not> ?Q P s\<rbrace> setThreadState st t \<lbrace>\<lambda>_ s. \<not> ?Q P s\<rbrace>"
      by (simp add: not_obj_at' comp_def, wp hoare_convert_imp pos)
  qed

lemma setBoundAEP_oa_queued:
  "\<lbrace>\<lambda>s. P' (obj_at' (\<lambda>tcb. P (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s) \<rbrace>
    setBoundAEP aep t
   \<lbrace>\<lambda>_ s. P' (obj_at' (\<lambda>tcb. P (tcbQueued tcb) (tcbDomain tcb) (tcbPriority tcb)) t' s) \<rbrace>"
  (is "\<lbrace>\<lambda>s. P' (?Q P s)\<rbrace> _ \<lbrace>\<lambda>_ s. P' (?Q P s)\<rbrace>")
  proof (rule P_bool_lift [where P=P'])
    show pos:
      "\<And>R. \<lbrace> ?Q R \<rbrace> setBoundAEP aep t \<lbrace>\<lambda>_. ?Q R \<rbrace>"
      apply (simp add: setBoundAEP_def)
      apply (wp threadSet_obj_at'_strongish)
      apply (clarsimp)
      done
    show "\<lbrace>\<lambda>s. \<not> ?Q P s\<rbrace> setBoundAEP aep t \<lbrace>\<lambda>_ s. \<not> ?Q P s\<rbrace>"
      by (simp add: not_obj_at' comp_def, wp hoare_convert_imp pos)
  qed

lemma tcbSchedDequeue_ksQ_distinct[wp]:
  "\<lbrace>\<lambda>s. distinct (ksReadyQueues s p)\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. distinct (ksReadyQueues s p)\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp)
   apply (rule_tac Q="\<lambda>_ s. distinct (ksReadyQueues s p)" in hoare_post_imp)
    apply (clarsimp | wp)+
  done

lemma sts_valid_queues_partial:
  "\<lbrace>Invariants_H.valid_queues and sch_act_simple\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_ s. \<forall>t' d p.
            (t' \<in> set(ksReadyQueues s (d, p)) \<longrightarrow>
             (obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t' s
              \<and> (t' \<noteq> t \<longrightarrow> st_tcb_at' runnable' t' s)))
            \<and> distinct (ksReadyQueues s (d, p))\<rbrace>"
  (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_ s. \<forall>t' d p. ?OA t' d p s \<and> ?DISTINCT d p s \<rbrace>")
  apply (rule_tac Q="\<lambda>_ s. (\<forall>t' d p. ?OA t' d p s) \<and> (\<forall>d p. ?DISTINCT d p s)"
           in hoare_post_imp)
   apply (clarsimp)
  apply (rule hoare_conjI)
   apply (rule_tac Q="\<lambda>s. \<forall>t' d p.
             ((t'\<in>set(ksReadyQueues s (d, p))
               \<or> \<not> (sch_act_simple s))
                  \<longrightarrow> (obj_at'(\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t' s
                       \<and> st_tcb_at' runnable' t' s))" in hoare_pre_imp)
    apply (fastforce simp: Invariants_H.valid_queues_def pred_tcb_at'_def obj_at'_def inQ_def)
   apply (rule hoare_vcg_all_lift)+
    apply (rule hoare_convert_imp)
     apply (wp sts_ksQ setThreadState_oa_queued hoare_impI sts_pred_tcb_neq'
            | clarsimp)+
  apply (rule_tac Q="\<lambda>s. \<forall>d p. ?DISTINCT d p s \<and> sch_act_simple s" in hoare_pre_imp)
   apply (clarsimp simp: Invariants_H.valid_queues_def)
  apply (wp hoare_vcg_all_lift sts_ksQ)
  apply (clarsimp)
  done

lemma tcbSchedDequeue_t_notksQ:
  "\<lbrace>\<lambda>s. t \<in> set (ksReadyQueues s (d, p)) \<longrightarrow>
           obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t s\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_ s. t \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
  apply (rule_tac Q="(\<lambda>s. t \<notin> set (ksReadyQueues s (d, p)))
                            or obj_at'(\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t"
               in hoare_pre_imp, clarsimp)
  apply (rule hoare_pre_disj)
   apply (wp tcbSchedDequeue_notksQ)[1]
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadGet_wp)
  apply (auto simp: obj_at'_real_def ko_wp_at'_def)
  done

lemma tcbSchedDequeue_valid_queues_partial:
  "\<lbrace>\<lambda>s. \<forall>t' d p. (t' \<in> set (ksReadyQueues s (d, p))
                   \<longrightarrow> obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t' s
                    \<and> (t' \<noteq> t \<longrightarrow> st_tcb_at' runnable' t' s))
                  \<and> distinct (ksReadyQueues s (d, p)) \<and> (maxDomain < d \<or> maxPriority < p \<longrightarrow> ksReadyQueues s (d, p) = [])\<rbrace>
   tcbSchedDequeue t
   \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  proof -
    let ?queued = "(\<lambda>d p tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p)"
    have tcbSchedDequeue_oa_queued:
      "\<And>d p t'. t \<noteq> t' \<Longrightarrow>
           \<lbrace>obj_at' (?queued d p) t'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. obj_at' (?queued d p) t'\<rbrace>"
      by (wp | clarsimp simp: tcbSchedDequeue_def cong: if_cong)+

    show ?thesis
      apply (rule_tac Q="\<lambda>_ s. \<forall>t' d p.
                (t'\<in>set (ksReadyQueues s (d, p))
                    \<longrightarrow> (obj_at' (?queued d p) t' s
                      \<and> st_tcb_at' runnable' t' s))
                 \<and> distinct (ksReadyQueues s (d, p)) \<and> (maxDomain < d \<or> maxPriority < p \<longrightarrow> ksReadyQueues s (d, p) = [])"
          in hoare_post_imp)
       apply (fastforce simp: Invariants_H.valid_queues_def pred_tcb_at'_def obj_at'_def inQ_def)
      apply (wp hoare_vcg_all_lift hoare_vcg_conj_lift)
       apply (case_tac "t'=t")
        apply (clarsimp)
        apply (rule_tac Q="\<lambda>_ s. t \<notin> set (ksReadyQueues s (d, p))" in hoare_post_imp)
         apply (clarsimp)
        apply (rule tcbSchedDequeue_t_notksQ)
       apply (clarsimp)
       apply (wp hoare_convert_imp tcbSchedDequeue_oa_queued tcbSchedDequeue_notksQ
            | clarsimp)+
       apply (simp add: tcbSchedDequeue_def)
       apply (wp threadGet_wp)+
       apply (fastforce simp: obj_at'_real_def ko_wp_at'_def)
       done
   qed

lemma sts_invs_minor'_no_valid_queues:
  "\<lbrace>st_tcb_at' (\<lambda>st'. tcb_st_refs_of' st' = tcb_st_refs_of' st
                   \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow>
                      st' \<noteq> Inactive \<and> \<not> idle' st')) t
      and (\<lambda>s. t = ksIdleThread s \<longrightarrow> idle' st)
      and (\<lambda>s. runnable' st \<and> obj_at' tcbQueued t s \<longrightarrow> st_tcb_at' runnable' t s)
      and sch_act_simple
      and invs'\<rbrace>
    setThreadState st t
   \<lbrace>\<lambda>_ s. (\<forall>t' d p.
            (t' \<in> set(ksReadyQueues s (d, p)) \<longrightarrow>
             (obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t' s
              \<and> (t' \<noteq> t \<longrightarrow> st_tcb_at' runnable' t' s)))
            \<and> distinct (ksReadyQueues s (d, p)) \<and> (maxDomain < d \<or> maxPriority < p \<longrightarrow> ksReadyQueues s (d, p) = [])) \<and>
         valid_pspace' s \<and>
         sch_act_wf (ksSchedulerAction s) s \<and>
         sym_refs (state_refs_of' s) \<and>
         if_live_then_nonz_cap' s \<and>
         if_unsafe_then_cap' s \<and>
         valid_idle' s \<and>
         valid_global_refs' s \<and>
         valid_arch_state' s \<and>
         valid_irq_node' (irq_node' s) s \<and>
         valid_irq_handlers' s \<and>
         valid_irq_states' s \<and>
         valid_machine_state' s \<and>
         irqs_masked' s \<and>
         valid_queues' s \<and>
         ct_not_inQ s \<and>
         ct_idle_or_in_cur_domain' s \<and>
         valid_pde_mappings' s \<and>
         pspace_domain_valid s \<and>
         ksCurDomain s \<le> maxDomain \<and>
         valid_dom_schedule' s \<and>
         cur_tcb' s \<and>
         tcb_at' t s\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (wp sts_valid_queues_partial sts_ksQ
            setThreadState_oa_queued sts_st_tcb_at'_cases
            irqs_masked_lift
            valid_irq_node_lift sts_valid_queues
            setThreadState_ct_not_inQ
            hoare_vcg_conj_lift hoare_vcg_imp_lift hoare_vcg_all_lift)+
  apply clarsimp
  apply (intro conjI)
       apply ((fastforce simp: valid_queues_def inQ_def pred_tcb_at' pred_tcb_at'_def
                        elim!: pred_tcb_at' st_tcb_ex_cap'' obj_at'_weakenE)+)[2]
  apply (clarsimp simp: pred_tcb_at'_def)
     apply (drule obj_at_valid_objs')
      apply (clarsimp simp: valid_pspace'_def)
     apply (clarsimp simp: valid_obj'_def valid_tcb'_def projectKOs)
     apply (fastforce simp: valid_tcb_state'_def
                     split: Structures_H.thread_state.splits)
    apply (clarsimp dest!: st_tcb_at_state_refs_ofD'
                    elim!: rsubst[where P=sym_refs]
                   intro!: ext)
   apply (fastforce simp: valid_queues_def inQ_def pred_tcb_at' pred_tcb_at'_def
                   elim!: pred_tcb_at' st_tcb_ex_cap'' obj_at'_weakenE)+
  done

crunch ct_idle_or_in_cur_domain'[wp]: tcbSchedDequeue ct_idle_or_in_cur_domain'

lemma tcbSchedDequeue_invs'_no_valid_queues:
   "\<lbrace>\<lambda>s. (\<forall>t' d p.
            (t' \<in> set(ksReadyQueues s (d, p)) \<longrightarrow>
             (obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t' s
              \<and> (t' \<noteq> t \<longrightarrow> st_tcb_at' runnable' t' s)))
            \<and> distinct (ksReadyQueues s (d, p)) \<and> (maxDomain < d \<or> maxPriority < p \<longrightarrow> ksReadyQueues s (d, p) = [])) \<and>
         valid_pspace' s \<and>
         sch_act_wf (ksSchedulerAction s) s \<and>
         sym_refs (state_refs_of' s) \<and>
         if_live_then_nonz_cap' s \<and>
         if_unsafe_then_cap' s \<and>
         valid_idle' s \<and>
         valid_global_refs' s \<and>
         valid_arch_state' s \<and>
         valid_irq_node' (irq_node' s) s \<and>
         valid_irq_handlers' s \<and>
         valid_irq_states' s \<and>
         valid_machine_state' s \<and>
         irqs_masked' s \<and>
         valid_queues' s \<and>
         ct_not_inQ s \<and>
         ct_idle_or_in_cur_domain' s \<and>
         valid_pde_mappings' s \<and>
         pspace_domain_valid s \<and>
         ksCurDomain s \<le> maxDomain \<and>
         valid_dom_schedule' s \<and>
         cur_tcb' s \<and>
         tcb_at' t s\<rbrace>
    tcbSchedDequeue t
   \<lbrace>\<lambda>_. invs' \<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (wp tcbSchedDequeue_valid_queues_partial valid_irq_handlers_lift
            valid_irq_node_lift valid_irq_handlers_lift'
            tcbSchedDequeue_irq_states irqs_masked_lift cur_tcb_lift
         | clarsimp simp add: cteCaps_of_def)+
  done

lemmas sts_tcbSchedDequeue_invs' =
  sts_invs_minor'_no_valid_queues
  tcbSchedDequeue_invs'_no_valid_queues

lemma (in delete_one_conc) suspend_invs'[wp]:
  "\<lbrace>invs' and sch_act_simple and tcb_at' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   ThreadDecls_H.suspend t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: suspend_def)
  apply (wp sts_tcbSchedDequeue_invs')
  apply (simp | strengthen no_refs_simple_strg')+
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift
            ipcCancel_simple [simplified] ipcCancel_invs
            ipcCancel_it ipcCancel_tcb_at' ipcCancel_sch_act_simple)
     apply simp+
  done

lemma (in delete_one_conc_pre) suspend_tcb'[wp]:
  "\<lbrace>tcb_at' t'\<rbrace> ThreadDecls_H.suspend t \<lbrace>\<lambda>rv. tcb_at' t'\<rbrace>"
  apply (simp add: suspend_def unless_def)
  apply (wp hoare_drop_imps |clarsimp|rule conjI)+
  done

lemma (in delete_one_conc_pre) suspend_sch_act_simple[wp]:
  "\<lbrace>sch_act_simple\<rbrace>
  ThreadDecls_H.suspend t \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (simp add: suspend_def when_def)
  apply (wp ipcCancel_sch_act_simple | simp add: unless_def
       | rule sch_act_simple_lift)+
  done

lemma (in delete_one_conc) suspend_objs':
  "\<lbrace>invs' and sch_act_simple and tcb_at' t and (\<lambda>s. t \<noteq> ksIdleThread s)\<rbrace>
   suspend t \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (rule_tac Q="\<lambda>_. invs'" in hoare_strengthen_post)
   apply (wp suspend_invs')
  apply fastforce
  done

lemma setQueue_pred_tcb_at'[wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> setQueue d p q \<lbrace>\<lambda>rv. pred_tcb_at' proj P t\<rbrace>"
  unfolding pred_tcb_at'_def
  by (rule setQueue_obj_at)

lemma (in delete_one_conc_pre) suspend_st_tcb_at':
  assumes x[simp]: "\<And>st. simple' st \<longrightarrow> P st" shows
  "\<lbrace>st_tcb_at' P t\<rbrace>
     suspend thread
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  apply (simp add: suspend_def unless_def)
  apply (wp sts_st_tcb_at'_cases threadSet_pred_tcb_no_state
            ipcCancel_st_tcb_at hoare_drop_imps
         | simp)+
  apply clarsimp
  done

lemmas (in delete_one_conc_pre) suspend_makes_simple' =
       suspend_st_tcb_at' [where P=simple', simplified]

lemma valid_queues_rq_distinctD:
  "Invariants_H.valid_queues s \<Longrightarrow> distinct (ksReadyQueues s (d, p))"
  by (clarsimp simp: Invariants_H.valid_queues_def)

lemma valid_queues_not_runnable'_not_ksQ:
  assumes "Invariants_H.valid_queues s" and "st_tcb_at' (Not \<circ> runnable') t s"
  shows   "\<forall>d p. t \<notin> set (ksReadyQueues s (d, p))"
  using assms
  apply -
  apply (clarsimp simp: Invariants_H.valid_queues_def pred_tcb_at'_def)
  apply (erule_tac x=d in allE)
  apply (erule_tac x=p in allE)
  apply (clarsimp)
  apply (drule(1) bspec)
  apply (clarsimp simp: obj_at'_def)
  done

declare valid_queues_not_runnable'_not_ksQ[OF ByAssum, simp]

lemma asyncIPCCancel_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and st_tcb_at' (Not \<circ> runnable') t\<rbrace>
   asyncIPCCancel t ae \<lbrace>\<lambda>_. Invariants_H.valid_queues \<rbrace>"
  apply (simp add: asyncIPCCancel_def)
  apply (wp sts_valid_queues)
     apply (rule_tac Q="\<lambda>_ s. \<forall>p. t \<notin> set (ksReadyQueues s p)" in hoare_post_imp, simp)
     apply (wp hoare_vcg_all_lift)
    apply (wpc)
     apply (wp)
  apply (rule_tac Q="\<lambda>_ s. Invariants_H.valid_queues s \<and> (\<forall>p. t \<notin> set (ksReadyQueues s p))" in hoare_post_imp)
   apply (clarsimp)
  apply (wp)
  apply (clarsimp)
  done

lemma (in delete_one_conc_pre) ipcCancel_queues[wp]:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)\<rbrace>
   ipcCancel t \<lbrace>\<lambda>rv. Invariants_H.valid_queues\<rbrace>"
  apply (simp add: ipcCancel_def Let_def getThreadReplySlot_def
             cong: Structures_H.thread_state.case_cong list.case_cong)
  apply (rule hoare_seq_ext [OF _ gts_sp'])
  apply (rule hoare_pre)
   apply (wpc
           | wp hoare_vcg_conj_lift delete_one_queues threadSet_valid_queues
                threadSet_valid_objs' sts_valid_queues setEndpoint_ksQ
                hoare_vcg_all_lift threadSet_sch_act threadSet_weak_sch_act_wf
           | simp add: o_def if_apply_def2 inQ_def
           | rule hoare_drop_imps
           | clarsimp simp: valid_tcb'_def tcb_cte_cases_def
                     elim!: pred_tcb'_weakenE)+
  apply (safe)
    apply (drule_tac t=t in valid_queues_not_runnable'_not_ksQ)
     apply (erule pred_tcb'_weakenE, simp)
    apply (drule_tac x=xc in spec, simp)
   apply (erule pred_tcb'_weakenE, simp)
  apply (drule_tac t=t in valid_queues_not_runnable'_not_ksQ)
   apply (erule pred_tcb'_weakenE, simp)
  apply (drule_tac x=xe in spec, simp)
  done

(* FIXME: move to Schedule_R *)
lemma tcbSchedDequeue_nonq[wp]:
  "\<lbrace>Invariants_H.valid_queues and tcb_at' t and K (t = t')\<rbrace>
    tcbSchedDequeue t \<lbrace>\<lambda>_ s. \<forall>d p. t' \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: tcbSchedDequeue_def)
  apply (wp threadGet_wp)
  apply (fastforce simp: Invariants_H.valid_queues_def obj_at'_def projectKOs inQ_def)
  done

lemma sts_ksQ_oaQ:
  "\<lbrace>Invariants_H.valid_queues\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. t \<in> set (ksReadyQueues s (d, p)) \<longrightarrow>
           obj_at' (\<lambda>tcb. tcbQueued tcb \<and> tcbDomain tcb = d \<and> tcbPriority tcb = p) t s\<rbrace>"
  (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  proof -
    have RR: "\<lbrace>sch_act_simple and ?POST\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. ?POST\<rbrace>"
      apply (simp add: rescheduleRequired_def)
      apply (wp)
        apply (clarsimp)
       apply (rule_tac
                Q="(\<lambda>s. action = ResumeCurrentThread \<or> action = ChooseNewThread) and ?POST"
                                                               in hoare_pre_imp, assumption)
       apply (case_tac action)
         apply (clarsimp)+
      apply (wp)
      apply (clarsimp simp: sch_act_simple_def)
      done
    show ?thesis
      apply (simp add: setThreadState_def)
      apply (wp RR)
      apply (rule_tac Q="\<lambda>_. ?POST" in hoare_post_imp)
       apply (clarsimp simp add: sch_act_simple_def)
      apply (wp hoare_convert_imp)
      apply (clarsimp simp: Invariants_H.valid_queues_def)
      apply (drule_tac x=d in spec)
      apply (drule_tac x=p in spec)
      apply (fastforce dest: bspec elim!: obj_at'_weakenE simp: inQ_def)
      done
  qed

lemma (in delete_one_conc_pre) suspend_nonq:
  "\<lbrace>Invariants_H.valid_queues and valid_objs' and tcb_at' t
                 and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                 and (\<lambda>s. t \<noteq> ksIdleThread s) and K (t = t')\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv s. \<forall>d p. t' \<notin> set (ksReadyQueues s (d, p))\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: suspend_def unless_def)
  apply (wp hoare_allI tcbSchedDequeue_t_notksQ sts_ksQ_oaQ)
  apply (clarsimp)
  done

lemma suspend_makes_inactive:
  "\<lbrace>K (t = t')\<rbrace> suspend t \<lbrace>\<lambda>rv. st_tcb_at' (op = Inactive) t'\<rbrace>"
  apply (cases "t = t'", simp_all)
  apply (simp add: suspend_def unless_def)
  apply (wp threadSet_pred_tcb_no_state setThreadState_st_tcb | simp)+
  done

(* Levity: added (20090723 09:16:50) *)
declare threadSet_sch_act_sane [wp]

(* Levity: added (20090721 10:56:34) *)
declare sane_update [simp]

(* Levity: added (20090725 09:07:51) *)
declare sts_sch_act_sane [wp]

lemma tcbSchedEnqueue_ksQset_weak:
  "\<lbrace>\<lambda>s. t' \<in> set (ksReadyQueues s p)\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_ s. t' \<in> set (ksReadyQueues s p)\<rbrace>" (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp)
  apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp)
   apply (wp | clarsimp)+
  done

lemma sts_ksQset_weak:
  "\<lbrace>\<lambda>s. t' \<in> set (ksReadyQueues s p)\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. t' \<in> set (ksReadyQueues s p)\<rbrace>" (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: setThreadState_def rescheduleRequired_def)
  apply (wp tcbSchedEnqueue_ksQset_weak | wpc | clarsimp)+
  apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp, clarsimp)
  apply (wp)
  done

lemma tcbSchedEnqueue_sch_act_not_ct[wp]:
  "\<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps tcbSchedEnqueue_ct', wp, simp)

lemma sts_sch_act_not_ct[wp]:
  "\<lbrace>\<lambda>s. sch_act_not (ksCurThread s) s\<rbrace>
   setThreadState st t \<lbrace>\<lambda>_ s. sch_act_not (ksCurThread s) s\<rbrace>"
  by (rule hoare_weaken_pre, wps tcbSchedEnqueue_ct', wp, simp)

text {* Cancelling all IPC in an endpoint or asynchronous endpoint *}

lemma ep_cancel_corres_helper:
  "corres dc ((\<lambda>s. \<forall>t \<in> set list. tcb_at t s) and valid_etcbs)
             ((\<lambda>s. \<forall>t \<in> set list. tcb_at' t s)
                    and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
                    and Invariants_H.valid_queues and valid_queues' and valid_objs')
          (mapM_x (\<lambda>t. do
                        y \<leftarrow> set_thread_state t Structures_A.Restart;
                        tcb_sched_action tcb_sched_enqueue t
                     od) list)
          (mapM_x (\<lambda>t. do
                        y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                        tcbSchedEnqueue t
                     od) list)"
  apply (rule_tac S="{t. (fst t = snd t) \<and> fst t \<in> set list}"
                     in corres_mapM_x)
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (subst bind_return_unit, rule corres_split [OF tcbSchedEnqueue_corres])
          apply simp
          apply (rule corres_guard_imp [OF sts_corres])
            apply simp
           apply (simp add: valid_tcb_state_def)
          apply simp
         apply (wp sts_valid_queues)
       apply (force simp: tcb_at_is_etcb_at)
      apply (fastforce elim: obj_at'_weakenE)
     apply ((wp hoare_vcg_const_Ball_lift | simp)+)[1]
    apply (rule hoare_pre)
    apply (wp hoare_vcg_const_Ball_lift
              weak_sch_act_wf_lift_linear sts_st_tcb' setThreadState_not_st
              sts_valid_queues tcbSchedEnqueue_not_st
         | simp)+
    apply (auto elim: obj_at'_weakenE simp: valid_tcb_state'_def)
  done

lemma ep_cancel_corres:
  "corres dc (invs and valid_sched and ep_at ep) (invs' and ep_at' ep)
             (ep_cancel_all ep) (epCancelAll ep)"
proof -
  have P:
    "\<And>list.
     corres dc (\<lambda>s. (\<forall>t \<in> set list. tcb_at t s) \<and> valid_pspace s \<and> ep_at ep s
                        \<and> valid_etcbs s \<and> weak_valid_sched_action s)
               (\<lambda>s. (\<forall>t \<in> set list. tcb_at' t s) \<and> valid_pspace' s
                         \<and> ep_at' ep s \<and> weak_sch_act_wf (ksSchedulerAction s) s
                         \<and> Invariants_H.valid_queues s \<and> valid_queues' s \<and> valid_objs' s)
               (do x \<leftarrow> set_endpoint ep Structures_A.IdleEP;
                   x \<leftarrow> mapM_x (\<lambda>t. do
                        y \<leftarrow> set_thread_state t Structures_A.Restart;
                        tcb_sched_action tcb_sched_enqueue t
                     od) list;
                   reschedule_required
               od)
               (do x \<leftarrow> setEndpoint ep IdleEP;
                   x \<leftarrow> mapM_x (\<lambda>t. do
                        y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                        tcbSchedEnqueue t
                     od) list;
                   rescheduleRequired
                od)"
    apply (rule corres_split')
       apply (rule corres_guard_imp [OF set_ep_corres])
         apply (simp add: ep_relation_def)+
      apply (rule corres_split [OF rescheduleRequired_corres])
        apply (rule ep_cancel_corres_helper)
       apply (rule mapM_x_wp')
       apply (wp weak_sch_act_wf_lift_linear set_thread_state_runnable_weak_valid_sched_action | simp)+
      apply (rule_tac R="\<lambda>_ s. \<forall>x\<in>set list. tcb_at' x s \<and> valid_objs' s"
                   in hoare_post_add)
      apply (rule mapM_x_wp')
      apply (rule hoare_name_pre_state)
      apply ((wp hoare_vcg_const_Ball_lift mapM_x_wp'
                sts_valid_queues setThreadState_not_st sts_st_tcb' tcbSchedEnqueue_not_st
           | clarsimp
           | fastforce elim: obj_at'_weakenE simp: valid_tcb_state'_def)+)[2]
      apply (rule hoare_name_pre_state)
      apply (wp hoare_vcg_const_Ball_lift set_ep_valid_objs'
          | (clarsimp simp: valid_ep'_def)
          | (drule (1) bspec, clarsimp simp: valid_pspace'_def valid_tcb'_def valid_ep'_def elim!: valid_objs_valid_tcbE))+
      done

  show ?thesis
    apply (simp add: ep_cancel_all_def epCancelAll_def)
    apply (rule corres_split' [OF _ _ get_endpoint_sp get_ep_sp'])
     apply (rule corres_guard_imp [OF get_ep_corres], simp+)
    apply (case_tac epa, simp_all add: ep_relation_def
                                       get_ep_queue_def)
     apply (rule corres_guard_imp [OF P]
             | clarsimp simp: valid_obj_def valid_ep_def
                              valid_obj'_def valid_ep'_def
                              invs_valid_pspace projectKOs
                              valid_sched_def valid_sched_action_def
             | erule obj_at_valid_objsE
             | drule ko_at_valid_objs'
             | rule conjI | clarsimp simp: invs'_def valid_state'_def)+
    done
qed

(* FIXME move *)
lemma set_aep_tcb_obj_at' [wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace>
     setAsyncEP aep v
   \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
apply (clarsimp simp: setAsyncEP_def, wp)
done

lemma aep_cancel_corres:
  "corres dc (invs and valid_sched and aep_at aep) (invs' and aep_at' aep)
             (aep_cancel_all aep) (aepCancelAll aep)"
  apply (simp add: aep_cancel_all_def aepCancelAll_def)
  apply (rule corres_split' [OF _ _ get_aep_sp get_aep_sp'])
   apply (rule corres_guard_imp [OF get_aep_corres])
    apply simp+
  apply (case_tac "aep_obj aepa", simp_all add: aep_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ set_aep_corres])
       apply (rule corres_split [OF rescheduleRequired_corres])
         apply (rule ep_cancel_corres_helper)
        apply (wp mapM_x_wp'[where 'b="det_ext state"]
                  weak_sch_act_wf_lift_linear setThreadState_not_st
                  set_thread_state_runnable_weak_valid_sched_action
             | simp)+
       apply (rename_tac list)
       apply (rule_tac R="\<lambda>_ s. (\<forall>x\<in>set list. tcb_at' x s) \<and> valid_objs' s"
                    in hoare_post_add)
       apply (rule mapM_x_wp')
       apply (rule hoare_name_pre_state)
       apply (wp hoare_vcg_const_Ball_lift
                 sts_st_tcb' sts_valid_queues setThreadState_not_st
                 tcbSchedEnqueue_not_st
            | (clarsimp simp: valid_tcb_state'_def)
            | fastforce elim: obj_at'_weakenE)+
      apply (simp add: aep_relation_def)
     apply (wp hoare_vcg_const_Ball_lift set_aep_aligned' set_aep_valid_objs'
               weak_sch_act_wf_lift_linear
          | simp)+
   apply (clarsimp simp: invs'_def valid_state'_def invs_valid_pspace valid_obj_def valid_aep_def invs_weak_sch_act_wf valid_aep'_def valid_pspace'_def
              valid_sched_def valid_sched_action_def valid_obj'_def projectKOs | erule obj_at_valid_objsE | drule ko_at_valid_objs')+
  done

lemma ep'_Idle_case_helper:
  "(case ep of IdleEP \<Rightarrow> a | _ \<Rightarrow> b) = (if (ep = IdleEP) then a else b)"
  by (cases ep, simp_all)

lemma rescheduleRequired_notresume:
  "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread\<rbrace>
    rescheduleRequired \<lbrace>\<lambda>_ s. ksSchedulerAction s = ChooseNewThread\<rbrace>"
  proof -
    have ssa: "\<lbrace>\<top>\<rbrace> setSchedulerAction ChooseNewThread
               \<lbrace>\<lambda>_ s. ksSchedulerAction s = ChooseNewThread\<rbrace>"
      by (simp add: setSchedulerAction_def | wp)+
    show ?thesis
      by (simp add: rescheduleRequired_def, wp ssa)
  qed

lemma setThreadState_ResumeCurrentThread_imp_notct[wp]:
  "\<lbrace>\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t'\<rbrace>"
  (is "\<lbrace>?PRE\<rbrace> _ \<lbrace>_\<rbrace>")
proof -
  have nrct:
    "\<lbrace>\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread\<rbrace>
     rescheduleRequired
     \<lbrace>\<lambda>_ s. ksSchedulerAction s \<noteq> ResumeCurrentThread\<rbrace>"
    by (rule hoare_strengthen_post [OF rescheduleRequired_notresume], simp)
  show ?thesis
  apply (simp add: setThreadState_def)
  apply (wp hoare_vcg_imp_lift [OF nrct])
  apply (rule_tac Q="\<lambda>_. ?PRE" in hoare_post_imp)
   apply (clarsimp)
  apply (rule hoare_convert_imp [OF threadSet_no_sa threadSet_ksCurThread])
  done
qed

lemma cancel_all_invs'_helper:
  "\<lbrace>all_invs_but_sym_refs_ct_not_inQ' and (\<lambda>s. \<forall>x \<in> set q. tcb_at' x s)
         and (\<lambda>s. sym_refs (\<lambda>x. if x \<in> set q then {r \<in> state_refs_of' s x. snd r = TCBBound}
                                else state_refs_of' s x)
                \<and>  (\<forall>x \<in> set q. ex_nonz_cap_to' x s))\<rbrace>
     mapM_x (\<lambda>t. do
                   y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                   tcbSchedEnqueue t
                 od) q
   \<lbrace>\<lambda>rv. all_invs_but_ct_not_inQ'\<rbrace>"
  apply (rule mapM_x_inv_wp2)
   apply clarsimp
  apply (rule hoare_pre)
   apply (wp valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
             hoare_vcg_const_Ball_lift
             sts_valid_queues sts_st_tcb' setThreadState_not_st
        | simp)+
  apply (unfold fun_upd_apply Invariants_H.tcb_st_refs_of'_simps)
  apply clarsimp
  apply (intro conjI)
  apply (clarsimp simp: valid_tcb_state'_def global'_no_ex_cap
                 elim!: rsubst[where P=sym_refs]
                 dest!: suffixeq_set_subset
                intro!: ext
       | (drule (1) bspec, clarsimp simp: valid_pspace'_def valid_tcb'_def elim!: valid_objs_valid_tcbE))+
  done

lemma ep_q_refs_max:
  "\<lbrakk> ko_at' r p s; sym_refs (state_refs_of' s); r \<noteq> IdleEP \<rbrakk>
      \<Longrightarrow> (state_refs_of' s p \<subseteq> (set (epQueue r) \<times> {EPSend, EPRecv}))
       \<and> (\<forall>x\<in>set (epQueue r). \<exists>aepptr. state_refs_of' s x \<subseteq>
                                  {(p, TCBBlockedSend), (p, TCBBlockedRecv), (aepptr, TCBBound)})"
  apply (frule(1) sym_refs_ko_atD')
  apply (drule ko_at_state_refs_ofD')
  apply (case_tac r)
    apply (clarsimp simp: st_tcb_at_refs_of_rev' tcb_bound_refs'_def
             | rule conjI | drule(1) bspec | drule st_tcb_at_state_refs_ofD'
             | case_tac aepptr)+
  done

crunch ct' [wp]: setEndpoint "\<lambda>s. P (ksCurThread s)"
  (wp: setObject_ep_ct ignore: setObject)

crunch ct' [wp]: setAsyncEP "\<lambda>s. P (ksCurThread s)"
  (wp: setObject_aep_ct ignore: setObject)

lemma tcbSchedEnqueue_cur_tcb'[wp]:
  "\<lbrace>cur_tcb'\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. cur_tcb'\<rbrace>"
  by (simp add: tcbSchedEnqueue_def unless_def)
     (wp threadSet_cur setQueue_cur | simp)+

lemma rescheduleRequired_invs'[wp]:
  "\<lbrace>invs'\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp ssa_invs' | simp add: invs'_update_cnt | wpc)+
  apply (clarsimp simp: invs'_def valid_state'_def)
  done

lemma ss_sch_act_sane_weak:
  "sa = ResumeCurrentThread \<or> sa = ChooseNewThread \<Longrightarrow> 
  \<lbrace>\<top>\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>rv. sch_act_sane\<rbrace>"
  apply (simp add: setSchedulerAction_def)
  apply wp
  apply (auto simp: sch_act_sane_def)
  done

lemma invs_rct_ct_activatable':
  "\<lbrakk> invs' s; ksSchedulerAction s = ResumeCurrentThread \<rbrakk>
   \<Longrightarrow> st_tcb_at' activatable' (ksCurThread s) s"
  by (simp add: invs'_def valid_state'_def ct_in_state'_def)

lemma not_in_epQueue:
  assumes ko_at:  "ko_at' r ep_ptr s" and
          srefs:  "sym_refs (state_refs_of' s)" and
          nidle:  "r \<noteq> IdleEP" and
          st_act: "st_tcb_at' simple' t s"
  shows   "t \<notin> set (epQueue r)"
  proof
    assume t_epQ: "t \<in> set (epQueue r)"

    with ko_at nidle
    have "(t, EPRecv) \<in> state_refs_of' s ep_ptr
          \<or> (t, EPSend) \<in> state_refs_of' s ep_ptr"
      by - (drule ko_at_state_refs_ofD', case_tac r, (clarsimp)+)

    with ko_at srefs
    have "(ep_ptr, TCBBlockedRecv) \<in> state_refs_of' s t
           \<or> (ep_ptr, TCBBlockedSend) \<in> state_refs_of' s t"
      apply -
      apply (frule(1) sym_refs_ko_atD')
      apply (drule ko_at_state_refs_ofD')
      apply (case_tac r)
        apply (clarsimp simp: st_tcb_at_refs_of_rev'
               | drule(1) bspec | drule st_tcb_at_state_refs_ofD')+
      done

    with ko_at have "st_tcb_at' (Not \<circ> simple') t s"
      apply -
      apply (erule disjE)
       apply (drule state_refs_of'_elemD)
       apply (simp add: st_tcb_at_refs_of_rev')
       apply (erule pred_tcb'_weakenE)
       apply (clarsimp)
      apply (drule state_refs_of'_elemD)
      apply (simp add: st_tcb_at_refs_of_rev')
      apply (erule pred_tcb'_weakenE)
      apply (clarsimp)
      done

    with st_act show False
      by (rule pred_tcb'_neq_contra) simp
  qed

lemma ct_not_in_epQueue:
  assumes "ko_at' r ep_ptr s" and
          "sym_refs (state_refs_of' s)" and
          "r \<noteq> IdleEP" and
          "ct_in_state' simple' s"
  shows   "ksCurThread s \<notin> set (epQueue r)"
  using assms unfolding ct_in_state'_def
  by (rule not_in_epQueue)

lemma not_in_aepQueue:
  assumes ko_at:  "ko_at' r aep_ptr s" and
          srefs:  "sym_refs (state_refs_of' s)" and
          nidle:  "aepObj r \<noteq> IdleAEP \<and> (\<forall>b m. aepObj r \<noteq> ActiveAEP b)" and
          st_act: "st_tcb_at' simple' t s"
  shows   "t \<notin> set (aepQueue (aepObj r))"
  proof
    assume t_epQ: "t \<in> set (aepQueue (aepObj r))"

    with ko_at nidle
    have "(t, AEPAsync) \<in> state_refs_of' s aep_ptr"
      by - (drule ko_at_state_refs_ofD', case_tac "aepObj r", (clarsimp)+)
    with ko_at srefs
    have "(aep_ptr, TCBAsync) \<in> state_refs_of' s t"
      apply -
      apply (frule(1) sym_refs_ko_atD')
      apply (drule ko_at_state_refs_ofD')
      apply (case_tac "aepObj r")
        apply (clarsimp simp: st_tcb_at_refs_of_rev' aep_bound_refs'_def
             | drule st_tcb_at_state_refs_ofD')+
      apply (drule_tac x="(t, AEPAsync)" in bspec, clarsimp)
      apply (clarsimp simp: st_tcb_at_refs_of_rev' dest!: st_tcb_at_state_refs_ofD')
      done

    with ko_at have "st_tcb_at' (Not \<circ> simple') t s"
      apply -
      apply (drule state_refs_of'_elemD)
      apply (simp add: st_tcb_at_refs_of_rev')
      apply (erule pred_tcb'_weakenE)
      apply (clarsimp)
      done

    with st_act show False
      by (rule pred_tcb'_neq_contra) simp
  qed

lemma ct_not_in_aepQueue:
  assumes ko_at:  "ko_at' r aep_ptr s" and
          srefs:  "sym_refs (state_refs_of' s)" and
          nidle:  "aepObj r \<noteq> IdleAEP \<and> (\<forall>b m. aepObj r \<noteq> ActiveAEP b)" and
          st_act: "ct_in_state' simple' s"
  shows   "ksCurThread s \<notin> set (aepQueue (aepObj r))"
  using assms unfolding ct_in_state'_def
  by (rule not_in_aepQueue)

crunch valid_pspace'[wp]: rescheduleRequired "valid_pspace'"
crunch valid_global_refs'[wp]: rescheduleRequired "valid_global_refs'"
crunch valid_machine_state'[wp]: rescheduleRequired "valid_machine_state'"

lemma sch_act_wf_weak:
  "sch_act_wf sa s \<Longrightarrow> weak_sch_act_wf sa s"
  by (case_tac sa, (simp add: weak_sch_act_wf_def)+)

lemma rescheduleRequired_all_invs_but_ct_not_inQ:
  "\<lbrace>all_invs_but_ct_not_inQ'\<rbrace> rescheduleRequired \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
  apply (wp_trace rescheduleRequired_ct_not_inQ
            valid_irq_node_lift valid_irq_handlers_lift''
            irqs_masked_lift cur_tcb_lift)
                   apply (auto simp: sch_act_wf_weak)
  done

lemma epCancelAll_invs'[wp]:
  "\<lbrace>invs'\<rbrace> epCancelAll ep_ptr \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: epCancelAll_def ep'_Idle_case_helper cong del: if_cong)
  apply (wp rescheduleRequired_all_invs_but_ct_not_inQ
            cancel_all_invs'_helper hoare_vcg_const_Ball_lift
            valid_global_refs_lift' valid_arch_state_lift'
            valid_irq_node_lift ssa_invs' sts_sch_act'
            irqs_masked_lift
         | simp only: sch_act_wf.simps forM_x_def | simp)+
  apply (rule hoare_strengthen_post [OF get_ep_sp'])
  apply (clarsimp simp: invs'_def valid_state'_def valid_ep'_def)
  apply (frule obj_at_valid_objs', fastforce)
  apply (clarsimp simp: projectKOs valid_obj'_def)
  apply (rule conjI)
   apply (case_tac r, simp_all add: valid_ep'_def)[1]
  apply (rule conjI[rotated])
   apply (drule(1) sym_refs_ko_atD')
   apply (case_tac r, simp_all add: st_tcb_at_refs_of_rev')[1]
    apply (clarsimp elim!: if_live_state_refsE
           | drule(1) bspec | drule st_tcb_at_state_refs_ofD')+
  apply (drule(2) ep_q_refs_max)
  apply (erule delta_sym_refs)
   apply (clarsimp dest!: symreftype_inverse' split: split_if_asm | drule(1) bspec subsetD)+
  done

lemma aepCancelAll_invs'[wp]:
  "\<lbrace>invs'\<rbrace> aepCancelAll aep \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: aepCancelAll_def)
  apply (rule hoare_seq_ext [OF _ get_aep_sp'])
  apply (case_tac "aepObj aepa", simp_all)
    apply (wp, simp)
   apply (wp, simp)
  apply (rule hoare_pre)
   apply (wp rescheduleRequired_all_invs_but_ct_not_inQ
             cancel_all_invs'_helper hoare_vcg_const_Ball_lift
             valid_irq_node_lift ssa_invs' irqs_masked_lift
          | simp only: sch_act_wf.simps)+
  apply (clarsimp simp: invs'_def valid_state'_def valid_aep'_def)
  apply (frule obj_at_valid_objs', clarsimp)
  apply (clarsimp simp: projectKOs valid_obj'_def valid_aep'_def)
  apply (drule(1) sym_refs_ko_atD')
  apply (rule conjI, clarsimp elim!: if_live_state_refsE)
  apply (rule conjI[rotated])
   apply (clarsimp elim!: if_live_state_refsE)
   apply (drule_tac x="(x, AEPAsync)" in bspec)
    apply (clarsimp simp: st_tcb_at_refs_of_rev')+
   apply (drule st_tcb_at_state_refs_ofD')
   apply clarsimp
  apply (erule delta_sym_refs)
   apply (clarsimp split: split_if_asm)
  apply (clarsimp split: split_if_asm)
   apply (fastforce simp: symreftype_inverse' aep_bound_refs'_def)
  apply (drule_tac x="(x, AEPAsync)" in bspec)
   apply (clarsimp simp: st_tcb_at_refs_of_rev')+
  apply (drule st_tcb_at_state_refs_ofD')
  apply (fastforce simp: symreftype_inverse' aep_bound_refs'_def tcb_bound_refs'_def)
  done

crunch valid_objs'[wp]: tcbSchedEnqueue valid_objs'
  (simp: unless_def valid_tcb'_def tcb_cte_cases_def)

lemma epCancelAll_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> epCancelAll ep \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: epCancelAll_def ep'_Idle_case_helper  cong del: if_cong)
  apply (rule hoare_seq_ext [OF _ get_ep_sp'])
  apply (rule hoare_pre)
   apply (wp set_ep_valid_objs' setSchedulerAction_valid_objs')
    apply (rule_tac Q="\<lambda>rv s. valid_objs' s \<and> (\<forall>x\<in>set (epQueue ep). tcb_at' x s)"
                    in hoare_post_imp)
     apply simp
    apply (simp add: Ball_def)
    apply (wp mapM_x_wp' sts_valid_objs'
              hoare_vcg_all_lift hoare_vcg_const_imp_lift)+
     apply simp
    apply (simp add: valid_tcb_state'_def)
   apply (wp set_ep_valid_objs' hoare_vcg_all_lift hoare_vcg_const_imp_lift)
  apply (clarsimp)
  apply (frule(1) ko_at_valid_objs')
   apply (simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def)
  apply (case_tac epa, simp_all)
  done

lemma aepCancelAll_valid_objs'[wp]:
  "\<lbrace>valid_objs'\<rbrace> aepCancelAll aep \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (simp add: aepCancelAll_def)
  apply (rule hoare_seq_ext [OF _ get_aep_sp'])
  apply (case_tac "aepObj aepa", simp_all)
    apply (wp, simp)
   apply (wp, simp)
  apply (rename_tac list)
  apply (rule_tac Q="\<lambda>rv s. valid_objs' s \<and> (\<forall>x\<in>set list. tcb_at' x s)"
                  in hoare_post_imp)
   apply (simp add: valid_aep'_def)
  apply (simp add: Ball_def)
  apply (wp setSchedulerAction_valid_objs' mapM_x_wp'
            sts_valid_objs' hoare_vcg_all_lift hoare_vcg_const_imp_lift
       | simp)+
   apply (simp add: valid_tcb_state'_def)
  apply (rule hoare_pre,
         wp set_aep_valid_objs' hoare_vcg_all_lift hoare_vcg_const_imp_lift)
  apply clarsimp
  apply (frule(1) ko_at_valid_objs')
   apply (simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def valid_aep'_def)
  done

lemma epCancelAll_st_tcb_at:
  assumes x[simp]: "P Restart" shows
  "\<lbrace>st_tcb_at' P t\<rbrace> epCancelAll epptr \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  unfolding epCancelAll_def
  by (wp ep'_cases_weak_wp mapM_x_wp' sts_st_tcb_at'_cases | clarsimp)+

lemmas epCancelAll_makes_simple[wp] =
       epCancelAll_st_tcb_at [where P=simple', simplified]

lemma aepCancelAll_st_tcb_at:
  assumes x[simp]: "P Restart" shows
  "\<lbrace>st_tcb_at' P t\<rbrace> aepCancelAll epptr \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>"
  unfolding aepCancelAll_def
  by (wp aep'_cases_weak_wp mapM_x_wp' sts_st_tcb_at'_cases | clarsimp)+

lemmas aepCancelAll_makes_simple[wp] =
       aepCancelAll_st_tcb_at [where P=simple', simplified]

lemma threadSet_not_tcb[wp]:
  "\<lbrace>ko_wp_at' (\<lambda>x. P x \<and> (projectKO_opt x = (None :: tcb option))) p\<rbrace>
     threadSet f t
   \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>x. P x \<and> (projectKO_opt x = (None :: tcb option))) p\<rbrace>"
  by (clarsimp simp: threadSet_def valid_def getObject_def
                     setObject_def in_monad loadObject_default_def
                     ko_wp_at'_def projectKOs split_def in_magnitude_check
                     objBits_simps updateObject_default_def
                     ps_clear_upd' projectKO_opt_tcb)

lemma ko_wp_at_q[simp]:
  "ko_wp_at' P p (ksReadyQueues_update f s) = ko_wp_at' P p s"
  by (simp add: ko_wp_at'_def ps_clear_def)

lemma setThreadState_not_tcb[wp]:
  "\<lbrace>ko_wp_at' (\<lambda>x. P x \<and> (projectKO_opt x = (None :: tcb option))) p\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>x. P x \<and> (projectKO_opt x = (None :: tcb option))) p\<rbrace>"
  apply (simp add: setThreadState_def setQueue_def
                   rescheduleRequired_def tcbSchedEnqueue_def
                   unless_def
             cong: scheduler_action.case_cong  cong del: if_cong
            | wp | wpcw)+
  done

lemma tcbSchedEnqueue_unlive:
  "\<lbrace>ko_wp_at' (\<lambda>x. \<not> live' x \<and> (projectKO_opt x = (None :: tcb option))) p
    and tcb_at' t\<rbrace>
    tcbSchedEnqueue t
   \<lbrace>\<lambda>_. ko_wp_at' (\<lambda>x. \<not> live' x \<and> (projectKO_opt x = (None :: tcb option))) p\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def)
  apply (wp | simp add: setQueue_def)+
  done

lemma cancelAll_unlive_helper:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set xs. tcb_at' x s) \<and>
     ko_wp_at' (\<lambda>x. \<not> live' x \<and> (projectKO_opt x = (None :: tcb option))) p s\<rbrace>
     mapM_x (\<lambda>t. do
                   y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                   tcbSchedEnqueue t
                 od) xs
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp')
   apply (rule hoare_pre)
    apply (wp tcbSchedEnqueue_unlive hoare_vcg_const_Ball_lift)
   apply clarsimp
  apply (clarsimp elim!: ko_wp_at'_weakenE)
  done

lemma setObject_ko_wp_at':
  fixes v :: "'a :: pspace_storable"
  assumes x: "\<And>v :: 'a. updateObject v = updateObject_default v"
  assumes n: "\<And>v :: 'a. objBits v = n"
  assumes v: "(1 :: word32) < 2 ^ n"
  shows
  "\<lbrace>\<lambda>s. P (injectKO v)\<rbrace> setObject p v \<lbrace>\<lambda>rv. ko_wp_at' P p\<rbrace>"
  by (clarsimp simp: setObject_def valid_def in_monad
                     ko_wp_at'_def x split_def n
                     updateObject_default_def
                     objBits_def[symmetric] ps_clear_upd'
                     in_magnitude_check v projectKOs)

lemma rescheduleRequired_unlive:
  "\<lbrace>\<lambda>s. ko_wp_at' (Not \<circ> live') p s \<and> ksSchedulerAction s \<noteq> SwitchToThread p\<rbrace>
      rescheduleRequired
   \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') p\<rbrace>"
  apply (simp add: rescheduleRequired_def)
  apply (wp | simp | wpc)+
   apply (simp add: tcbSchedEnqueue_def unless_def
                    threadSet_def setQueue_def threadGet_def)
   apply (wp setObject_ko_wp_at getObject_tcb_wp
            | simp add: objBits_simps split del: split_if)+
  apply (clarsimp simp: o_def)
  apply (drule obj_at_ko_at')
  apply clarsimp
  done

lemmas setEndpoint_ko_wp_at'
    = setObject_ko_wp_at'[where 'a=endpoint, folded setEndpoint_def, simplified]

lemma epCancelAll_unlive:
  "\<lbrace>valid_objs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s)\<rbrace>
      epCancelAll ep \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') ep\<rbrace>"
  apply (simp add: epCancelAll_def ep'_Idle_case_helper)
  apply (rule hoare_seq_ext [OF _ get_ep_sp'])
  apply (rule hoare_pre)
   apply (wp_trace cancelAll_unlive_helper setEndpoint_ko_wp_at'
             hoare_vcg_const_Ball_lift rescheduleRequired_unlive
             mapM_x_wp'
        | simp add: objBits_simps)+
  apply (clarsimp simp: projectKO_opt_tcb)
  apply (frule(1) obj_at_valid_objs')
  apply (intro conjI impI)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def projectKOs
                        obj_at'_def pred_tcb_at'_def ko_wp_at'_def
                 split: endpoint.split_asm)+
  done

lemma aepCancelAll_unlive:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> sch_act_wf (ksSchedulerAction s) s
      \<and> obj_at' (\<lambda>ko. aepBoundTCB ko = None) aepptr s\<rbrace>
      aepCancelAll aepptr \<lbrace>\<lambda>rv. ko_wp_at' (Not \<circ> live') aepptr\<rbrace>"
  apply (simp add: aepCancelAll_def)
  apply (rule hoare_seq_ext [OF _ get_aep_sp'])
  apply (case_tac "aepObj aep", simp_all add: setAsyncEP_def)
    apply wp
    apply (fastforce simp: obj_at'_real_def projectKOs
                     dest: obj_at_conj'
                     elim: ko_wp_at'_weakenE)
   apply wp
   apply (fastforce simp: obj_at'_real_def projectKOs
                    dest: obj_at_conj'
                    elim: ko_wp_at'_weakenE)
  apply (wp rescheduleRequired_unlive)
   apply (wp cancelAll_unlive_helper)
   apply (wp mapM_x_wp' setObject_ko_wp_at' hoare_vcg_const_Ball_lift,
          simp_all add: objBits_simps, simp_all)
    apply (fold setAsyncEP_def, wp)
    apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
   apply (simp add: projectKOs projectKO_opt_tcb)
  apply (fastforce simp: ko_wp_at'_def valid_obj'_def valid_aep'_def
                        obj_at'_def projectKOs 
                  elim: valid_objsE')+
  done

crunch ep_at'[wp]: tcbSchedEnqueue "ep_at' epptr"
  (simp: unless_def)

declare if_cong[cong]

lemma insert_eqD:
  "A = insert a B \<Longrightarrow> a \<in> A"
  by blast

lemma epCancelBadgedSends_filterM_helper':
  notes if_cong[cong del]
  shows
  "\<forall>ys.
   \<lbrace>\<lambda>s. all_invs_but_sym_refs_ct_not_inQ' s
           \<and> ex_nonz_cap_to' epptr s \<and> ep_at' epptr s
           \<and> sym_refs ((state_refs_of' s) (epptr := set (xs @ ys) \<times> {EPSend}))
           \<and> (\<forall>y \<in> set (xs @ ys). state_refs_of' s y = {(epptr, TCBBlockedSend)} 
                                       \<union> {r \<in> state_refs_of' s y. snd r = TCBBound})
           \<and> distinct (xs @ ys)\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> getThreadState t;
                      if blockingIPCBadge st = badge then
                        do y \<leftarrow> setThreadState Structures_H.thread_state.Restart t;
                           y \<leftarrow> tcbSchedEnqueue t;
                           return False
                        od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv s. all_invs_but_sym_refs_ct_not_inQ' s
           \<and> ex_nonz_cap_to' epptr s \<and> ep_at' epptr s
           \<and> sym_refs ((state_refs_of' s) (epptr := (set rv \<union> set ys) \<times> {EPSend}))
           \<and> (\<forall>y \<in> set ys. state_refs_of' s y = {(epptr, TCBBlockedSend)} 
                                   \<union> {r \<in> state_refs_of' s y. snd r = TCBBound})
           \<and> distinct rv \<and> distinct (xs @ ys) \<and> set rv \<subseteq> set xs \<and> (\<forall>x \<in> set xs. tcb_at' x s)\<rbrace>"
  apply (rule_tac xs=xs in rev_induct)
   apply clarsimp
   apply wp
   apply clarsimp
  apply (clarsimp simp: filterM_append bind_assoc simp del: set_append distinct_append)
  apply (drule spec, erule hoare_seq_ext[rotated])
  apply (rule hoare_seq_ext [OF _ gts_inv'])
  apply (rule hoare_pre)
   apply (wp valid_irq_node_lift hoare_vcg_const_Ball_lift sts_sch_act'
             sch_act_wf_lift valid_irq_handlers_lift'' cur_tcb_lift irqs_masked_lift
             sts_st_tcb' sts_valid_queues setThreadState_not_st
             tcbSchedEnqueue_not_st
        | clarsimp)+
  apply (frule insert_eqD, frule state_refs_of'_elemD)
  apply (clarsimp simp: valid_tcb_state'_def st_tcb_at_refs_of_rev')
  apply (frule pred_tcb_at')
  apply (rule conjI[rotated], blast)
  apply clarsimp
  apply (intro conjI)
      apply (clarsimp simp: valid_pspace'_def valid_tcb'_def elim!: valid_objs_valid_tcbE dest!: st_tcb_ex_cap'')
     apply (fastforce dest!: st_tcb_ex_cap'')
    apply (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def)
   apply (erule delta_sym_refs)
    apply (fastforce elim!: obj_atE' 
                      simp: state_refs_of'_def projectKOs tcb_bound_refs'_def 
                            subsetD symreftype_inverse'
                     split: split_if_asm)+
  done

lemmas epCancelBadgedSends_filterM_helper
    = spec [where x=Nil, OF epCancelBadgedSends_filterM_helper', simplified]

lemma epCancelBadgedSends_invs[wp]:
  notes if_cong[cong del]
  shows
  "\<lbrace>invs'\<rbrace> epCancelBadgedSends epptr badge \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: epCancelBadgedSends_def)
  apply (rule hoare_seq_ext [OF _ get_ep_sp'])
  apply (case_tac ep, simp_all)
    apply ((wp | simp)+)[2]
  apply (subst bind_assoc [where g="\<lambda>_. rescheduleRequired",
                           symmetric])+
  apply (rule hoare_seq_ext
                [OF rescheduleRequired_all_invs_but_ct_not_inQ])
  apply (simp add: list_case_return cong: list.case_cong)
  apply (rule hoare_pre, wp valid_irq_node_lift irqs_masked_lift)
    apply simp
    apply (rule hoare_strengthen_post,
           rule epCancelBadgedSends_filterM_helper[where epptr=epptr])
    apply (clarsimp simp: ep_redux_simps3 fun_upd_def[symmetric])
    apply (clarsimp simp add: valid_ep'_def split: list.split)
    apply blast
   apply (wp valid_irq_node_lift irqs_masked_lift | wp_once sch_act_sane_lift)+
  apply (clarsimp simp: invs'_def valid_state'_def
                        valid_ep'_def fun_upd_def[symmetric]
                        obj_at'_weakenE[OF _ TrueI])
  apply (frule obj_at_valid_objs', clarsimp)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def projectKOs)
  apply (frule if_live_then_nonz_capD', simp add: obj_at'_real_def)
   apply (clarsimp simp: projectKOs)
  apply (frule(1) sym_refs_ko_atD')
  apply (clarsimp simp add: fun_upd_idem
                            st_tcb_at_refs_of_rev')
  apply (drule (1) bspec, drule st_tcb_at_state_refs_ofD', clarsimp)
  apply (fastforce simp: set_eq_subset tcb_bound_refs'_def)
  done

crunch state_refs_of[wp]: tcb_sched_action "\<lambda>s. P (state_refs_of s)"


lemma ep_cancel_badged_sends_corres:
  "corres dc (invs and valid_sched and ep_at epptr) (invs' and ep_at' epptr)
         (ep_cancel_badged_sends epptr bdg) (epCancelBadgedSends epptr bdg)"
  apply (simp add: ep_cancel_badged_sends_def epCancelBadgedSends_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ get_ep_corres get_endpoint_sp get_ep_sp',
                                 where Q="invs and valid_sched" and Q'=invs'])
    apply simp_all
  apply (case_tac ep, simp_all add: ep_relation_def)
  apply (simp add: filterM_mapM list_case_return cong: list.case_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor [OF _ set_ep_corres])
       apply (rule corres_split_eqr[OF _ _ _ hoare_post_add[where R="\<lambda>_. valid_objs'"]])
          apply (rule corres_split [OF rescheduleRequired_corres])
            apply (rule set_ep_corres)
            apply (simp split: list.split add: ep_relation_def)
           apply (wp weak_sch_act_wf_lift_linear)
         apply (rule_tac S="op ="
                     and Q="\<lambda>xs s. (\<forall>x \<in> set xs. (epptr, TCBBlockedSend) \<in> state_refs_of s x) \<and> distinct xs \<and> valid_etcbs s"
                    and Q'="\<lambda>xs s. (\<forall>x \<in> set xs. tcb_at' x s) \<and> weak_sch_act_wf (ksSchedulerAction s) s \<and> Invariants_H.valid_queues s \<and> valid_queues' s \<and> valid_objs' s"
                     in corres_mapM_list_all2[where r'="op ="],
                simp_all add: list_all2_refl)[1]
           apply (clarsimp simp: liftM_def[symmetric] o_def)
           apply (rule corres_guard_imp)
             apply (rule corres_split [OF _ gts_corres])
               apply (rule_tac F="\<exists>pl. st = Structures_A.BlockedOnSend epptr pl"
                            in corres_gen_asm)
               apply (clarsimp simp: o_def dc_def[symmetric] liftM_def)
               apply (rule corres_split [OF _ sts_corres])
                  apply (rule corres_split[OF _ tcbSchedEnqueue_corres])
                    apply (rule corres_trivial)
                    apply simp
                   apply wp
                 apply simp
                apply (wp sts_valid_queues gts_st_tcb_at)
            apply (clarsimp simp: valid_tcb_state_def tcb_at_def st_tcb_def2
                                  st_tcb_at_refs_of_rev
                           dest!: state_refs_of_elemD elim!: tcb_at_is_etcb_at[rotated])
            apply (simp add: is_tcb_def)
           apply simp
          apply (wp hoare_vcg_const_Ball_lift gts_wp | clarsimp)+
            apply (wp gts_st_tcb_at hoare_vcg_const_Ball_lift hoare_vcg_imp_lift
                      weak_sch_act_wf_lift_linear mapM_wp'
                      sts_st_tcb' sts_valid_queues setThreadState_valid_objs'
                      set_thread_state_runnable_weak_valid_sched_action
                      | clarsimp simp: valid_tcb_state'_def)+
      apply (simp add: ep_relation_def)
     apply (wp hoare_vcg_const_Ball_lift weak_sch_act_wf_lift_linear set_ep_valid_objs'
                | simp)+
   apply (clarsimp simp: conj_comms)
   apply (frule sym_refs_ko_atD, clarsimp+)
   apply (rule obj_at_valid_objsE, assumption+, clarsimp+)
   apply (clarsimp simp: valid_obj_def valid_ep_def valid_sched_def valid_sched_action_def)
   apply (rule conjI, erule obj_at_weakenE, clarsimp simp: is_ep)
   apply (clarsimp simp: st_tcb_at_refs_of_rev)
   apply (drule(1) bspec, drule st_tcb_at_state_refs_ofD, clarsimp)
   apply (simp add: set_eq_subset)
  apply (clarsimp simp: obj_at'_weakenE[OF _ TrueI])
  apply (drule ko_at_valid_objs', clarsimp)
   apply (simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def invs_weak_sch_act_wf
                        invs'_def valid_state'_def)
  done

lemma suspend_unqueued:
  "\<lbrace>\<top>\<rbrace> suspend t \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: suspend_def unless_def tcbSchedDequeue_def)
  apply wp
    apply (simp add: threadGet_def)
    apply (wp getObject_tcb_wp)
   apply (rule hoare_strengthen_post, rule hoare_post_taut)
   apply (fastforce simp: obj_at'_def projectKOs)
  apply (rule hoare_post_taut)
  done

end
