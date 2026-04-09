(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory HeapStateRelation
imports ArchHeapStateRelation
begin

arch_requalify_consts
  aobjs_relation
  heap_ghost_relation_wrapper_2

\<comment> \<open>An alternative approach to @{const state_relation} using heap projections\<close>

abbreviation tcbs_relation :: "'z state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "tcbs_relation s s' \<equiv> map_relation (tcbs_of s) (tcbs_of' s') tcb_relation"

definition cnode_to_cte_ptrs :: "obj_ref \<Rightarrow> cnode_contents \<Rightarrow> machine_word set" where
  "cnode_to_cte_ptrs p cnode = { cte_map (p, y) | y. y \<in> dom cnode }"

definition caps_relation_2 ::
  "(obj_ref \<rightharpoonup> nat) \<Rightarrow> (obj_ref \<rightharpoonup> cnode_contents) \<Rightarrow> (obj_ref \<rightharpoonup> cte) \<Rightarrow> bool"
  where
  "caps_relation_2 cnode_sizes cnodes ctes \<equiv>
    (\<Union>p\<in>dom cnodes. cnode_to_cte_ptrs p (the (cnodes p))) = dom ctes
    \<and> (\<forall>p\<in>dom cnodes. \<forall>cnode sz.
         cnodes p = Some cnode \<and> cnode_sizes p = Some sz
         \<longrightarrow> (well_formed_cnode_n sz cnode
              \<and> (\<forall>y \<in> dom cnode. \<forall>cap cte.
                   cnode y = Some cap \<and> ctes (cte_map (p, y)) = Some cte
                   \<longrightarrow> cap_relation cap (cteCap cte))))"

abbreviation caps_relation :: "'z state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "caps_relation s s' \<equiv> caps_relation_2 (cnode_sizes_of s) (cnode_contents_of s) (ctes_of' s')"

lemmas caps_relation_def = caps_relation_2_def

abbreviation ntfns_relation :: "'z state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ntfns_relation s s' \<equiv> map_relation (ntfns_of s) (ntfns_of' s') ntfn_relation"

abbreviation eps_relation :: "'z state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "eps_relation s s' \<equiv> map_relation (eps_of s) (eps_of' s') ep_relation"

definition scs_relation_2 ::
  "(obj_ref \<rightharpoonup> Structures_A.sched_context) \<Rightarrow> (obj_ref \<rightharpoonup> nat) \<Rightarrow> (obj_ref \<rightharpoonup> sched_context) \<Rightarrow> bool"
  where
  "scs_relation_2 scs sc_sizes scs' \<equiv>
     dom scs = dom scs'
     \<and> (\<forall>p sc n sc'. scs p = Some sc \<and> sc_sizes p = Some n \<and> scs' p = Some sc'
                     \<longrightarrow> valid_sched_context_size n \<and> sc_relation sc n sc')"

abbreviation scs_relation :: "'z state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "scs_relation s s' \<equiv> scs_relation_2 (scs_of s) (sc_sizes_of s) (scs_of' s')"

lemmas scs_relation_def = scs_relation_2_def

abbreviation replies_relation :: "'z state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "replies_relation s s' \<equiv> map_relation (replies_of s) (replies_of' s') reply_relation"

text \<open>
  The conjunct below involving @{const KOKernelData} is required in order to make the following
  definition fully equivalent to @{const pspace_relation}: the conjunct in @{const pspace_relation}
  involving @{const pspace_dom} will entail that there are no @{const KOKernelData} objects in the
  concrete heap.\<close>
definition heap_pspace_relation :: "'z::state_ext state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "heap_pspace_relation s s' \<equiv>
     tcbs_relation s s'
     \<and> caps_relation s s'
     \<and> scs_relation s s'
     \<and> eps_relation s s'
     \<and> ntfns_relation s s'
     \<and> replies_relation s s'
     \<and> (\<forall>p. ksPSpace s' p \<noteq> Some KOKernelData)
     \<and> aobjs_relation s s'"

lemma heap_pspace_relation_tcbs_relation[elim!]:
  "heap_pspace_relation s s' \<Longrightarrow> tcbs_relation s s'"
  by (simp add: heap_pspace_relation_def)

lemma heap_pspace_relation_caps_relation[elim!]:
  "heap_pspace_relation s s' \<Longrightarrow> caps_relation s s'"
  by (simp add: heap_pspace_relation_def)

lemma heap_pspace_relation_scs_relation[elim!]:
  "heap_pspace_relation s s' \<Longrightarrow> scs_relation s s'"
  by (simp add: heap_pspace_relation_def)

lemma heap_pspace_relation_eps_relation[elim!]:
  "heap_pspace_relation s s' \<Longrightarrow> eps_relation s s'"
  by (simp add: heap_pspace_relation_def)

lemma heap_pspace_relation_ntfns_relation[elim!]:
  "heap_pspace_relation s s' \<Longrightarrow> ntfns_relation s s'"
  by (simp add: heap_pspace_relation_def)

lemma heap_pspace_relation_replies_relation[elim!]:
  "heap_pspace_relation s s' \<Longrightarrow> replies_relation s s'"
  by (simp add: heap_pspace_relation_def)

lemma heap_pspace_relation_KOKernelData[elim!]:
  "heap_pspace_relation s s' \<Longrightarrow> (\<forall>p. ksPSpace s' p \<noteq> Some KOKernelData)"
  by (simp add: heap_pspace_relation_def)

lemma heap_pspace_relation_aobjs_relation[elim!]:
  "heap_pspace_relation s s' \<Longrightarrow> aobjs_relation s s'"
  by (simp add: heap_pspace_relation_def)

abbreviation heap_ghost_relation_wrapper :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "heap_ghost_relation_wrapper s s' \<equiv>
     heap_ghost_relation_wrapper_2
       (aobjs_of s) (cnode_sizes_of s) (cnode_contents_of s) (gsUserPages s') (gsCNodes s')
       (ksArchState s')"

lemma tcbs_relation_lift_rcorres[rcorres_lift]:
  assumes det: "\<And>s'. det_wp (\<lambda>s. Q s s') f"
  assumes abs: "\<And>P s'. \<lbrace>\<lambda>s. P (tcbs_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (tcbs_of s)\<rbrace>"
  assumes conc:
    "\<And>P s. \<lbrace>\<lambda>s'. P (dom (tcbs_of' s')) \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (dom (tcbs_of' s'))\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbIPCBuffers_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbIPCBuffers_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbArches_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbArches_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbStates_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbStates_of' s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbFaults_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbFaults_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbCTables_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbCTables_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbVTables_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbVTables_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbFaultHandlers_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbFaultHandlers_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbTimeoutHandlers_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbTimeoutHandlers_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbIPCBufferFrames_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbIPCBufferFrames_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbBoundNotifications_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbBoundNotifications_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbSchedContexts_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbSchedContexts_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbYieldTos_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbYieldTos_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbMCPs_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbMCPs_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbPriorities_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbPriorities_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbDomains_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbDomains_of s')\<rbrace>"
    "\<And>P s. \<lbrace>\<lambda>s'. P (tcbFlags_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbFlags_of s')\<rbrace>"
  shows "rcorres (\<lambda>s s'. tcbs_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. tcbs_relation)"
  apply (rule rcorres_from_valid_det)
   apply (fastforce intro: det_wp_pre det)
  apply (rename_tac s t)
  apply (rule_tac P'1="\<lambda>_. tcbs_of t = tcbs_of s" in hoare_pre_add[THEN iffD2])
   apply (fastforce dest: use_valid[OF _ abs])
  apply (insert conc)
  unfolding map_relation_def
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule hoare_weaken_pre)
    apply fast
   apply force
  apply (clarsimp simp: tcb_relation_def)
  apply (rule hoare_allI, rename_tac p)
  apply (rule hoare_allI, rename_tac tcb)
  apply (simp add: imp_conjL)
  apply (rule hoare_impI)
  apply (simp add: all_conj_distrib imp_conjR)
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. (tcbs_of' s' ||> tcbIPCBuffer) p = Some (tcb_ipc_buffer tcb)"
                in hoare_post_imp)
    apply (clarsimp simp: opt_map_def)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI)
    apply (clarsimp simp: opt_pred_def opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. ((\<lambda>atcb. arch_tcb_relation (tcb_arch tcb) atcb)
                               |< (tcbs_of' s' ||> tcbArch)) p"
                in hoare_post_imp)
    apply (clarsimp simp: opt_pred_def opt_map_def)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_pred_def opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. ((\<lambda>ts. thread_state_relation (tcb_state tcb) ts)
                               |< (tcbs_of' s' ||> tcbState)) p"
                in hoare_post_imp)
    apply (clarsimp simp: opt_pred_def opt_map_def)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_pred_def opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. fault_rel_optionation
                                ((tcbs_of t |> tcb_fault) p) ((tcbs_of' s' |> tcbFault) p)"
                in hoare_post_imp)
   apply (clarsimp simp: opt_map_red)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_pred_def opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. opt_ord_rel cap_relation
                                ((tcbs_of t ||> tcb_ctable) p)
                                ((tcbs_of' s' ||> tcbCTable ||> cteCap) p)"
                in hoare_post_imp)
   apply (clarsimp simp: opt_map_red)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_pred_def opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. opt_ord_rel cap_relation
                                ((tcbs_of t ||> tcb_vtable) p)
                                ((tcbs_of' s' ||> tcbVTable ||> cteCap) p)"
                in hoare_post_imp)
   apply (clarsimp simp: opt_map_red)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_pred_def opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. opt_ord_rel cap_relation
                                ((tcbs_of t ||> tcb_fault_handler) p)
                                ((tcbs_of' s' ||> tcbFaultHandler ||> cteCap) p)"
                in hoare_post_imp)
   apply (clarsimp simp: opt_map_red)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_pred_def opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. opt_ord_rel cap_relation
                                ((tcbs_of t ||> tcb_timeout_handler) p)
                                ((tcbs_of' s' ||> tcbTimeoutHandler ||> cteCap) p)"
                in hoare_post_imp)
   apply (clarsimp simp: opt_map_red)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_pred_def opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. opt_ord_rel cap_relation
                                ((tcbs_of t ||> tcb_ipcframe) p)
                                ((tcbs_of' s' ||> tcbIPCBufferFrame ||> cteCap) p)"
                in hoare_post_imp)
   apply (clarsimp simp: opt_map_red)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_pred_def opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. (tcbs_of' s' |> tcbBoundNotification) p = tcb_bound_notification tcb"
                in hoare_post_imp)
    apply (clarsimp simp: opt_map_def)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. (tcbs_of' s' |> tcbSchedContext) p = tcb_sched_context tcb"
                in hoare_post_imp)
    apply (clarsimp simp: opt_map_def)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. (tcbs_of' s' |> tcbYieldTo) p = tcb_yield_to tcb"
                in hoare_post_imp)
    apply (clarsimp simp: opt_map_def)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. (tcbs_of' s' ||> tcbMCP) p = Some (tcb_mcpriority tcb)"
                in hoare_post_imp)
    apply (clarsimp simp: opt_map_def)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. (tcbs_of' s' ||> tcbPriority) p = Some (tcb_priority tcb)"
                in hoare_post_imp)
    apply (clarsimp simp: opt_map_def)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_map_red)
   apply fastforce
  apply (rule hoare_vcg_conj_lift_pre_fix)
   apply (rule_tac Q'="\<lambda>_ s'. (tcbs_of' s' ||> tcbDomain) p = Some (tcb_domain tcb)"
                in hoare_post_imp)
    apply (clarsimp simp: opt_map_def)
   apply (rule hoare_weaken_pre, assumption)
   apply (rule conjI)
    apply clarsimp
    apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_map_red)
   apply fastforce
  apply (rule_tac Q'="\<lambda>_ s'. ((\<lambda>flg. word_to_tcb_flags flg = (tcb_flags tcb))
                              |< (tcbs_of' s' ||> tcbFlags)) p"
               in hoare_post_imp)
   apply (clarsimp simp: opt_pred_def opt_map_def)
  apply (rule hoare_weaken_pre, assumption)
  apply (rule conjI)
   apply clarsimp
   apply (frule_tac m="tcbs_of s" in domI, clarsimp simp: opt_pred_def opt_map_red)
  apply fastforce
  done

lemma scs_relation_lift_rcorres_weak[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (scs_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (scs_of s)\<rbrace>;
    \<And>P s'. \<lbrace>\<lambda>s. P (sc_sizes_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (sc_sizes_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (scs_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (scs_of' s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. scs_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. scs_relation)"
  apply (rule rcorres_lift_conc[where p=scs_of'])
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply fastforce
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=scs_of])
     apply (rule hoare_lift_Pf2_pre_conj[where f=sc_sizes_of])
      apply wpsimp
     apply fastforce
    apply fastforce
   apply fastforce
  apply wpsimp
  done

lemma eps_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (eps_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (eps_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (eps_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s. P (eps_of' s)\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. eps_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. eps_relation)"
  apply (rule rcorres_lift_conc[where p=eps_of'])
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
     by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma ntfns_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (ntfns_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (ntfns_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ntfns_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ntfns_of' s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. ntfns_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. ntfns_relation)"
  apply (rule rcorres_lift_conc[where p=ntfns_of'])
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
     by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma replies_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (replies_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (replies_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (replies_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s. P (replies_of' s)\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. replies_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. replies_relation)"
  apply (rule rcorres_lift_conc[where p=replies_of'])
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
     by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma caps_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (cnode_contents_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cnode_contents_of s)\<rbrace>;
    \<And>P s'. \<lbrace>\<lambda>s. P (cnode_sizes_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cnode_sizes_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ctes_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ctes_of' s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. caps_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. caps_relation)"
  apply (rule rcorres_lift_conc[where p=ctes_of'])
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply fastforce
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=cnode_contents_of])
     by (fastforce intro: hoare_weaken_pre)+

lemma kernel_data_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. det_wp (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s. \<lbrace>\<lambda>s'. P (kernelData_at s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (kernelData_at s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. \<forall>p. ksPSpace s' p \<noteq> Some KOKernelData \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. \<forall>p. ksPSpace s' p \<noteq> Some KOKernelData)"
  apply (rule rcorres_allI_fwd)
   apply (fastforce intro: det_wp_pre)
  apply (rule rcorres_weaken_pre)
   apply (rule_tac R="\<lambda>_ x _. x" in rcorres_lift_conc[where Q="\<lambda>s s'. Q s s'"])
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: det_wp_no_fail no_fail_pre)+

lemma sc_replies_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (sc_replies_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (sc_replies_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (scReplies_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (scReplies_of s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (replyPrevs_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (replyPrevs_of s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. sc_replies_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. sc_replies_relation)"
  apply (rule rcorres_lift_abs[where p=sc_replies_of])
   apply (rule rcorres_lift_conc)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply force
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=scReplies_of])
     by (fastforce intro: hoare_weaken_pre)+

lemma ready_queues_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (ready_queues s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (ready_queues s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksReadyQueues s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksReadyQueues s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (tcbSchedNexts_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbSchedNexts_of s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (tcbSchedPrevs_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbSchedPrevs_of s')\<rbrace>;
    \<And>P d p s. \<lbrace>\<lambda>s'. P (inQ d p |< tcbs_of' s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (inQ d p |< tcbs_of' s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. ready_queues_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. ready_queues_relation)"
  apply (rule rcorres_lift_abs[where p=ready_queues])
   apply (rule rcorres_lift_conc)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply force
   apply (rule hoare_weaken_pre)
   apply (rule hoare_lift_Pf2_pre_conj[where f=ksReadyQueues])
    apply (rule hoare_lift_Pf2_pre_conj[where f=tcbSchedNexts_of])
     apply (rule hoare_lift_Pf2_pre_conj[where f=tcbSchedPrevs_of])
      apply (rule inQ_lift)
      apply (rename_tac d p)
      apply (rule_tac f="\<lambda>s'. inQ d p |< tcbs_of' s'" in hoare_lift_Pf2_pre_conj)
        apply wpsimp
       by (fastforce intro: hoare_weaken_pre)+

lemma release_queue_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (release_queue s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (release_queue s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksReleaseQueue s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksReleaseQueue s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (tcbSchedNexts_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbSchedNexts_of s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (tcbSchedPrevs_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbSchedPrevs_of s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (tcbInReleaseQueue |< tcbs_of' s') \<and> Q s s'\<rbrace>
           f'  \<lbrace>\<lambda>_ s'. P (tcbInReleaseQueue |< tcbs_of' s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. release_queue_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. release_queue_relation)"
  apply (rule rcorres_lift_abs[where p=release_queue])
   apply (rule rcorres_lift_conc)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply force
   apply (rule hoare_weaken_pre)
   apply (rule hoare_lift_Pf2_pre_conj[where f=ksReleaseQueue])
     apply (rule hoare_lift_Pf2_pre_conj[where f=tcbSchedNexts_of])
      apply (rule hoare_lift_Pf2_pre_conj[where f=tcbSchedPrevs_of])
       by (fastforce intro: hoare_weaken_pre)+

lemma ep_queues_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (ep_queues_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (ep_queues_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (epQueues_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (epQueues_of s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (tcbSchedNexts_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbSchedNexts_of s')\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (tcbSchedPrevs_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (tcbSchedPrevs_of s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. ep_queues_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. ep_queues_relation)"
  apply (rule rcorres_lift_abs[where p=ep_queues_of])
   apply (rule rcorres_lift_conc)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply force
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=epQueues_of])
     apply (rule hoare_lift_Pf2_pre_conj[where f=tcbSchedNexts_of])
      by (fastforce intro: hoare_weaken_pre)+

lemma ntfn_queues_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (ntfn_queues_of s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (ntfn_queues_of s) \<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ntfnQueues_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s. P (ntfnQueues_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (tcbSchedNexts_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s. P (tcbSchedNexts_of s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (tcbSchedPrevs_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s. P (tcbSchedPrevs_of s)\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres (\<lambda>s s'. ntfn_queues_relation s s' \<and> Q s s') f  f' (\<lambda>_ _. ntfn_queues_relation)"
  apply (rule rcorres_lift_abs[where p=ntfn_queues_of])
    apply (rule rcorres_lift_conc)
     apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply force
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=ntfnQueues_of])
     apply (rule hoare_lift_Pf2_pre_conj[where f=tcbSchedNexts_of])
      by (fastforce intro: hoare_weaken_pre)+

lemma sched_act_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (scheduler_action s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksSchedulerAction s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksSchedulerAction s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. sched_act_relation (scheduler_action s) (ksSchedulerAction s') \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. sched_act_relation (scheduler_action s) (ksSchedulerAction s'))"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: hoare_weaken_pre no_fail_pre)+

lemma swp_cte_at_lift:
  "(\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>)
   \<Longrightarrow> (\<And>P. \<lbrace>\<lambda>s. P (swp cte_at s) \<and> Q s\<rbrace> f \<lbrace>\<lambda>_ s. P (swp cte_at s)\<rbrace>)"
  apply (simp add: swp_def cte_wp_at_caps_of_state)
  apply (rule hoare_lift_Pf2_pre_conj[where f="\<lambda>s y. \<exists>cap. caps_of_state s y = Some cap"])
   apply wpsimp
  apply fastforce
  done

lemma cdt_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (caps_of_state s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>;
    \<And>P s'. \<lbrace>\<lambda>s. P (cdt s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ctes_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ctes_of s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. cdt_relation (swp cte_at s) (cdt s) (ctes_of s') \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. cdt_relation (swp cte_at s) (cdt s) (ctes_of s'))"
  apply (rule rcorres_lift_conc[where p=ctes_of])
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply force
    apply fastforce
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=cdt])
     apply (rule hoare_lift_Pf2_pre_conj[where f="swp cte_at"])
      apply (fastforce intro: hoare_weaken_pre)
     apply (rule hoare_weaken_pre)
      apply (rule swp_cte_at_lift)
      by (fastforce intro: hoare_weaken_pre)+

lemma cdt_list_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (cdt_list s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cdt_list s)\<rbrace>;
    \<And>P s'. \<lbrace>\<lambda>s. P (cdt s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ctes_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ctes_of s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'.  cdt_list_relation (cdt_list s) (cdt s) (ctes_of s') \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. cdt_list_relation (cdt_list s) (cdt s) (ctes_of s'))"
  apply (rule rcorres_lift_conc[where p=ctes_of])
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply fastforce
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=cdt_list])
     by (fastforce intro: hoare_weaken_pre)+

lemma revokable_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (is_original_cap s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (is_original_cap s)\<rbrace>;
    \<And>P s'. \<lbrace>\<lambda>s. P (caps_of_state s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ctes_of s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ctes_of s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. revokable_relation
                   (is_original_cap s) (null_filter (caps_of_state s)) (ctes_of s')
                 \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. revokable_relation
                       (is_original_cap s) (null_filter (caps_of_state s)) (ctes_of s'))"
  apply (rule rcorres_lift_conc[where p=ctes_of])
   apply (rule rcorres_lift_abs)
     apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply fastforce
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=is_original_cap])
     by (fastforce intro: hoare_weaken_pre)+

lemma arch_state_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (arch_state s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksArchState s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksArchState s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. (arch_state s, ksArchState s') \<in> arch_state_relation \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. (arch_state s, ksArchState s') \<in> arch_state_relation)"
  apply (rule rcorres_lift_conc[where p=ksArchState])
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma interrupt_state_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (interrupt_irq_node s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>;
    \<And>P s'. \<lbrace>\<lambda>s. P (interrupt_states s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksInterruptState s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksInterruptState s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. interrupt_state_relation
                   (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s')
                 \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. interrupt_state_relation
                       (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s'))"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre)
     apply fastforce
    apply fastforce
   apply (rule hoare_weaken_pre)
    apply (rule hoare_lift_Pf2_pre_conj[where f=interrupt_irq_node])
     by (fastforce intro: hoare_weaken_pre)+

lemma cur_thread_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (cur_thread s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksCurThread s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksCurThread s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. cur_thread s = ksCurThread s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. cur_thread s = ksCurThread s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma idle_thread_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (idle_thread s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksIdleThread s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksIdleThread s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. idle_thread s = ksIdleThread s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. idle_thread s = ksIdleThread s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma idle_sc_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksIdleSC s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksIdleSC s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. idle_sc_ptr = ksIdleSC s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. idle_sc_ptr = ksIdleSC s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      apply (fastforce intro: no_fail_pre hoare_weaken_pre)
     apply (fastforce intro: no_fail_pre hoare_weaken_pre)
    apply (fastforce intro: no_fail_pre hoare_weaken_pre)
   apply wpsimp
  apply (fastforce intro: no_fail_pre hoare_weaken_pre)
  done

lemma machine_state_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (machine_state s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (machine_state s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksMachineState s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksMachineState s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. machine_state s = ksMachineState s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. machine_state s = ksMachineState s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma work_units_completed_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (work_units_completed s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (work_units_completed s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksWorkUnitsCompleted s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksWorkUnitsCompleted s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. work_units_completed s = ksWorkUnitsCompleted s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. work_units_completed s = ksWorkUnitsCompleted s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma domain_index_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (domain_index s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (domain_index s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksDomScheduleIdx s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksDomScheduleIdx s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. domain_index s = ksDomScheduleIdx s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. domain_index s = ksDomScheduleIdx s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma domain_list_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (domain_list s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (domain_list s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksDomSchedule s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksDomSchedule s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. domain_list s = ksDomSchedule s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. domain_list s = ksDomSchedule s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma cur_domain_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (cur_domain s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksCurDomain s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksCurDomain s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. cur_domain s = ksCurDomain s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. cur_domain s = ksCurDomain s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma domain_time_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (domain_time s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (domain_time s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksDomainTime s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksDomainTime s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. domain_time s = ksDomainTime s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. domain_time s = ksDomainTime s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma consumed_time_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (consumed_time s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (consumed_time s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksConsumedTime s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksConsumedTime s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. consumed_time s = ksConsumedTime s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. consumed_time s = ksConsumedTime s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma cur_time_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (cur_time s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_time s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksCurTime s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksCurTime s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. cur_time s = ksCurTime s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. cur_time s = ksCurTime s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma cur_sc_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (cur_sc s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_sc s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksCurSc s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksCurSc s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. cur_sc s = ksCurSc s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. cur_sc s = ksCurSc s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

lemma reprogram_timer_relation_lift_rcorres[rcorres_lift]:
  "\<lbrakk>\<And>s'. no_fail (\<lambda>s. Q s s') f; empty_fail f;
    \<And>P s'. \<lbrace>\<lambda>s. P (reprogram_timer s) \<and> Q s s'\<rbrace> f \<lbrace>\<lambda>_ s. P (reprogram_timer s)\<rbrace>;
    \<And>P s. \<lbrace>\<lambda>s'. P (ksReprogramTimer s') \<and> Q s s'\<rbrace> f' \<lbrace>\<lambda>_ s'. P (ksReprogramTimer s')\<rbrace>\<rbrakk>
   \<Longrightarrow> rcorres
         (\<lambda>s s'. reprogram_timer s = ksReprogramTimer s' \<and> Q s s')
         f  f'
         (\<lambda>_ _ s s'. reprogram_timer s = ksReprogramTimer s')"
  apply (rule rcorres_lift_conc)
   apply (rule rcorres_lift_abs)
    apply (rule rcorres_prop_fwd)
      by (fastforce intro: no_fail_pre hoare_weaken_pre)+

locale HeapStateRelation_R =
  assumes pspace_relation_heap_pspace_relation:
    "\<And>(s :: det_state) s'. pspace_relation (kheap s) (ksPSpace s') \<longleftrightarrow> heap_pspace_relation s s'"
  assumes ghost_relation_heap_ghost_relation:
    "\<And>(s :: det_state) s'. ghost_relation_wrapper s s' \<longleftrightarrow> heap_ghost_relation_wrapper s s'"

end
