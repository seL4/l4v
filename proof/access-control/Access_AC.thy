(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Access_AC
imports Access
begin

section\<open>Generic AC proofs\<close>

lemma aag_wellformed_Control:
  "\<lbrakk> (x, Control, y) \<in> aag; policy_wellformed aag mirqs irqs x \<rbrakk> \<Longrightarrow> x = y"
  unfolding policy_wellformed_def by metis

lemma aag_wellformed_refl:
  "\<lbrakk> policy_wellformed aag mirqs irqs x \<rbrakk> \<Longrightarrow> (x, a, x) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_grant_Control_to_recv:
  "\<lbrakk> (s, Grant, ep) \<in> aag; (r, Receive, ep) \<in> aag; policy_wellformed aag mirqs irqs l \<rbrakk>
     \<Longrightarrow> (s, Control, r) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_grant_Control_to_send:
  "\<lbrakk> (s, Grant, ep) \<in> aag; (r, Receive, ep) \<in> aag; policy_wellformed aag mirqs irqs l \<rbrakk>
     \<Longrightarrow> (r, Control, s) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_reply:
  "\<lbrakk> (s, Call, ep) \<in> aag; (r, Receive, ep) \<in> aag; policy_wellformed aag mirqs irqs l \<rbrakk>
     \<Longrightarrow> (r, Reply, s) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_delete_derived':
  "\<lbrakk> (s, Call, ep) \<in> aag; (r, Receive, ep) \<in> aag; policy_wellformed aag mirqs irqs l \<rbrakk>
     \<Longrightarrow> (s, DeleteDerived, r) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_delete_derived:
  "\<lbrakk> (s, Reply, r) \<in> aag; policy_wellformed aag mirqs irqs l \<rbrakk>
     \<Longrightarrow> (r, DeleteDerived, s) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_delete_derived_trans:
  "\<lbrakk> (l1, DeleteDerived, l2) \<in> aag; (l2, DeleteDerived, l3) \<in> aag;
     policy_wellformed aag mirqs irqs l\<rbrakk>
     \<Longrightarrow> (l1, DeleteDerived, l3) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_call_to_syncsend:
  "\<lbrakk> (s, Call, ep) \<in> aag; policy_wellformed aag mirqs irqs l \<rbrakk>
     \<Longrightarrow> (s, SyncSend, ep) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_grant_Control_to_send_by_reply:
  "\<lbrakk> (s, Call, ep) \<in> aag; (r, Receive, ep) \<in> aag;
     (r, Grant, ep) \<in> aag; policy_wellformed aag mirqs irqs l \<rbrakk>
     \<Longrightarrow> (r, Control, s) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma aag_wellformed_grant_Control_to_recv_by_reply:
  "\<lbrakk> (s, Call, ep) \<in> aag; (r, Receive, ep) \<in> aag;
     (r, Grant, ep) \<in> aag; policy_wellformed aag mirqs irqs l \<rbrakk>
     \<Longrightarrow> (s, Control, r) \<in> aag"
  unfolding policy_wellformed_def by blast

lemma auth_graph_map_mem:
  "(x, auth, y) \<in> auth_graph_map f S = (\<exists>x' y'. x = f x' \<and> y = f y' \<and> (x', auth, y') \<in> S)"
  by (simp add: auth_graph_map_def)

lemmas auth_graph_map_memD = auth_graph_map_mem[THEN iffD1]

lemma auth_graph_map_memE:
  assumes hyp: "(x, auth, y) \<in> auth_graph_map f S"
  obtains x' and y' where "x = f x'" and "y = f y'" and "(x', auth, y') \<in> S"
  using hyp[THEN auth_graph_map_mem[THEN iffD1]] by fastforce

lemma auth_graph_map_memI:
  "\<lbrakk> (x', auth, y') \<in> S; x = f x'; y = f y' \<rbrakk>
     \<Longrightarrow> (x, auth, y) \<in> auth_graph_map f S"
  by (fastforce simp add: auth_graph_map_mem)

lemma auth_graph_map_mono:
  "S \<subseteq> S' \<Longrightarrow> auth_graph_map G S \<subseteq> auth_graph_map G S'"
  unfolding auth_graph_map_def by auto

lemma is_transferable_capE:
  assumes hyp:"is_transferable_cap cap"
  obtains "cap = NullCap" | t R where "cap = ReplyCap t False R"
  by (rule is_transferable.cases[OF hyp]) auto

lemma is_transferable_None[simp]: "is_transferable None"
  using is_transferable.simps by simp
lemma is_transferable_Null[simp]: "is_transferable_cap NullCap"
  using is_transferable.simps by simp
lemma is_transferable_Reply[simp]: "is_transferable_cap (ReplyCap t False R)"
  using is_transferable.simps by simp

lemma is_transferable_NoneE:
  assumes hyp: "is_transferable opt_cap"
  obtains "opt_cap = None" | cap where "opt_cap = Some cap" and "is_transferable_cap cap"
  by (rule is_transferable.cases[OF hyp];simp)

lemma is_transferable_Untyped[simp]: "\<not> is_transferable (Some (UntypedCap dev ptr sz freeIndex))"
  by (blast elim: is_transferable.cases)
lemma is_transferable_IRQ[simp]: "\<not> is_transferable_cap IRQControlCap"
  by (blast elim: is_transferable.cases)
lemma is_transferable_Zombie[simp]: "\<not> is_transferable (Some (Zombie ptr sz n))"
  by (blast elim: is_transferable.cases)
lemma is_transferable_Ntfn[simp]: "\<not> is_transferable (Some (NotificationCap ntfn badge R))"
  by (blast elim: is_transferable.cases)
lemma is_transferable_Endpoint[simp]: "\<not> is_transferable (Some (EndpointCap ntfn badge R))"
  by (blast elim: is_transferable.cases)

(* FIXME MOVE *)
lemmas descendants_incD = descendants_inc_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

(* FIXME MOVE *)
lemmas all_childrenI = all_children_def[THEN meta_eq_to_obj_eq, THEN iffD2, rule_format]
lemmas all_childrenD = all_children_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

(* FIXME MOVE *)
lemma valid_mdb_descendants_inc[elim!]:
  "valid_mdb s \<Longrightarrow> descendants_inc (cdt s) (caps_of_state s)"
  by (simp add:valid_mdb_def)

(* FIXME MOVE *)
lemma valid_mdb_mdb_cte_at [elim!]:
  "valid_mdb s \<Longrightarrow> mdb_cte_at (swp (cte_wp_at ((\<noteq>) NullCap)) s) (cdt s)"
  by (simp add:valid_mdb_def)

(* FIXME MOVE *)
lemma descendants_inc_cap_classD:
  "\<lbrakk> descendants_inc m caps; p \<in> descendants_of p' m; caps p = Some cap ; caps p' = Some cap' \<rbrakk>
     \<Longrightarrow> cap_class cap = cap_class cap'"
  by (fastforce dest:descendants_incD)


locale Access_AC_1 =
  fixes aag :: "'a PAS"
  and user_monad_t :: "'b user_monad"
  assumes acap_class_reply:
    "acap_class acap \<noteq> ReplyClass t"
  and arch_troa_tro_alt[elim!]:
    "arch_integrity_obj_atomic aag subjects l ko ko'
     \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko'"
  and arch_tro_alt_trans_spec:
    "\<lbrakk> arch_integrity_obj_alt aag subjects l ko ko';
       arch_integrity_obj_alt aag subjects l ko' ko'' \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko''"
  and clas_caps_of_state:
    "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk>
       \<Longrightarrow> cap_links_asid_slot aag (pasObjectAbs aag (fst slot)) cap"
begin

lemma cap_class_reply:
  "(cap_class cap = ReplyClass t) = (\<exists>r m. cap = ReplyCap t m r)"
  by (cases cap; simp add: acap_class_reply)

lemma reply_cap_no_children:
  "\<lbrakk> valid_mdb s; caps_of_state s p = Some (ReplyCap t False r) \<rbrakk> \<Longrightarrow> cdt s p' \<noteq> Some p"
  apply (clarsimp simp: valid_mdb_def)
  apply (frule descendants_incD[where p=p' and p'=p])
   apply (rule child_descendant)
   apply (fastforce)
  apply clarsimp
  apply (subgoal_tac "caps_of_state s p' \<noteq> None")
   apply (clarsimp simp: cap_class_reply)
   apply (simp only: reply_mdb_def reply_caps_mdb_def reply_masters_mdb_def)
   apply (elim conjE allE[where x=p'])
   apply simp
  apply (drule(1) mdb_cte_atD)
  apply (fastforce simp add: cte_wp_at_def caps_of_state_def)
  done

lemma is_transferable_all_children:
  "valid_mdb s \<Longrightarrow> all_children (\<lambda>slot . is_transferable (caps_of_state s slot)) (cdt s)"
  apply (rule all_childrenI)
  apply (erule is_transferable.cases)
    apply (fastforce dest: mdb_cte_atD valid_mdb_mdb_cte_at
                     simp: mdb_cte_at_def cte_wp_at_def caps_of_state_def)
   apply (fastforce dest: mdb_cte_atD valid_mdb_mdb_cte_at
                    simp: mdb_cte_at_def cte_wp_at_def caps_of_state_def)
  apply (blast dest: reply_cap_no_children)
  done

end


lemmas state_objs_to_policy_mem = eqset_imp_iff[OF state_objs_to_policy_def]

lemmas state_objs_to_policy_intros
    = state_bits_to_policy.intros[THEN state_objs_to_policy_mem[THEN iffD2]]

(* FIXME: brittle when adding rules to or removing rules from state_bits_to_policy *)
lemmas sta_caps = state_objs_to_policy_intros(1)
  and sta_untyped = state_objs_to_policy_intros(2)
  and sta_ts = state_objs_to_policy_intros(3)
  and sta_bas = state_objs_to_policy_intros(4)
  and sta_cdt = state_objs_to_policy_intros(5)
  and sta_cdt_transferable = state_objs_to_policy_intros(6)
  and sta_vref = state_objs_to_policy_intros(7)

lemmas state_objs_to_policy_cases
    = state_bits_to_policy.cases[OF state_objs_to_policy_mem[THEN iffD1]]

lemma tcb_states_of_state_preserved:
  "\<lbrakk> get_tcb False thread s = Some tcb; tcb_state tcb' = tcb_state tcb \<rbrakk>
     \<Longrightarrow> tcb_states_of_state (s\<lparr>kheap := kheap s(thread \<mapsto> TCB tcb')\<rparr>) = tcb_states_of_state s"
  by (auto split: option.splits simp: tcb_states_of_state_def get_tcb_def obind_def ta_filter_def)

lemma thread_st_auth_preserved:
  "\<lbrakk> get_tcb False thread s = Some tcb; tcb_state tcb' = tcb_state tcb \<rbrakk>
     \<Longrightarrow> thread_st_auth (s\<lparr>kheap := kheap s(thread \<mapsto> TCB tcb')\<rparr>) = thread_st_auth s"
  by (simp add: tcb_states_of_state_preserved thread_st_auth_def)

lemma thread_bound_ntfns_preserved:
  "\<lbrakk> get_tcb False thread s = Some tcb; tcb_bound_notification tcb' = tcb_bound_notification tcb \<rbrakk>
     \<Longrightarrow> thread_bound_ntfns (s\<lparr>kheap := kheap s(thread \<mapsto> TCB tcb')\<rparr>) = thread_bound_ntfns s"
  by (auto simp: thread_bound_ntfns_def get_tcb_def obind_def ta_filter_def split: option.splits)

lemma is_transferable_null_filter[simp]:
  "is_transferable (null_filter caps ptr) = is_transferable (caps ptr)"
  by (auto simp: is_transferable.simps null_filter_def)

lemma tcb_domain_map_wellformed_mono:
  "\<lbrakk> domains_of_state s' \<subseteq> domains_of_state s; tcb_domain_map_wellformed pas s \<rbrakk>
     \<Longrightarrow> tcb_domain_map_wellformed pas s'"
  by (auto simp: tcb_domain_map_wellformed_aux_def get_etcb_def)

lemma pas_refined_mem:
  "\<lbrakk> (x, auth, y) \<in> state_objs_to_policy s; pas_refined aag s \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag auth x y"
  by (auto simp: pas_refined_def intro: auth_graph_map_memI)

lemma pas_refined_wellformed[elim!]:
  "pas_refined aag s \<Longrightarrow> pas_wellformed aag"
  unfolding pas_refined_def by simp

lemmas pas_refined_Control
    = aag_wellformed_Control[OF _ pas_refined_wellformed]
  and pas_refined_refl = aag_wellformed_refl [OF pas_refined_wellformed]

lemma caps_of_state_pasObjectAbs_eq:
  "\<lbrakk> caps_of_state s p = Some cap; Control \<in> cap_auth_conferred cap;
     is_subject aag (fst p); pas_refined aag s; x \<in> obj_refs_ac cap \<rbrakk>
     \<Longrightarrow> is_subject aag x"
  apply (frule sta_caps, simp+)
  apply (drule pas_refined_mem, simp+)
  apply (drule pas_refined_Control, simp+)
  done

lemma pas_refined_state_objs_to_policy_subset:
  "\<lbrakk> pas_refined aag s;
     state_objs_to_policy s' \<subseteq> state_objs_to_policy s;
     state_asids_to_policy aag s' \<subseteq> state_asids_to_policy aag s;
     state_irqs_to_policy aag s' \<subseteq> state_irqs_to_policy aag s;
     domains_of_state s' \<subseteq> domains_of_state s;
     interrupt_irq_node s' = interrupt_irq_node s \<rbrakk>
     \<Longrightarrow> pas_refined aag s'"
  by (simp add: pas_refined_def)
     (blast dest: tcb_domain_map_wellformed_mono auth_graph_map_mono[where G="pasObjectAbs aag"])

lemma aag_wellformed_all_auth_is_owns':
  "\<lbrakk> Control \<in> S; pas_wellformed aag \<rbrakk>
     \<Longrightarrow> (\<forall>auth \<in> S. aag_has_auth_to aag auth x) = (is_subject aag x)"
  by (fastforce simp: aag_wellformed_refl dest: aag_wellformed_Control)

lemmas aag_wellformed_all_auth_is_owns
   = aag_wellformed_all_auth_is_owns'[where S=UNIV, simplified]
     aag_wellformed_all_auth_is_owns'[where S="{Control}", simplified]

lemmas aag_wellformed_control_is_owns
   = aag_wellformed_all_auth_is_owns'[where S="{Control}", simplified]

lemmas pas_refined_all_auth_is_owns = aag_wellformed_all_auth_is_owns[OF pas_refined_wellformed]

lemma pas_refined_sita_mem:
  "\<lbrakk> (x, auth, y) \<in> state_irqs_to_policy aag s; pas_refined aag s \<rbrakk>
     \<Longrightarrow> (x, auth, y) \<in> pasPolicy aag"
  by (auto simp: pas_refined_def)

lemma receive_blocked_on_can_receive_ipc[elim!,simp]:
  "receive_blocked_on ref ts \<Longrightarrow> can_receive_ipc ts"
  by (cases ts; simp)

lemma receive_blocked_on_can_receive_ipc'[elim!,simp]:
  "case_option False (receive_blocked_on ref) tsopt \<Longrightarrow> case_option False can_receive_ipc tsopt"
  by (cases tsopt;simp)

lemma tcb_bound_notification_reset_integrity_refl[simp]:
  "tcb_bound_notification_reset_integrity ntfn ntfn subjects aag"
  by (simp add: tcb_bound_notification_reset_integrity_def)

lemma allowed_call_blocked_call_blocked[elim!]:
  "allowed_call_blocked ep tst \<Longrightarrow> call_blocked ep tst"
  unfolding allowed_call_blocked_def call_blocked_def by fastforce

lemmas reply_cap_deletion_integrityI1 =
       reply_cap_deletion_integrity_def[THEN meta_eq_to_obj_eq,THEN iffD2,OF disjI1]
lemmas reply_cap_deletion_integrityI2 =
       reply_cap_deletion_integrity_def[THEN meta_eq_to_obj_eq,THEN iffD2, OF disjI2, OF exI,
                                        OF exI, OF conjI [OF _ conjI], rule_format]
lemmas reply_cap_deletion_integrity_intros =
       reply_cap_deletion_integrityI1 reply_cap_deletion_integrityI2

lemma reply_cap_deletion_integrityE:
  assumes hyp: "reply_cap_deletion_integrity subjects aag cap cap'"
  obtains "cap = cap'" | caller R where "cap = ReplyCap caller False R"
  and "cap' = NullCap" and "pasObjectAbs aag caller \<in> subjects"
  using hyp reply_cap_deletion_integrity_def by blast

lemma reply_cap_deletion_integrity_refl[simp]:
  "reply_cap_deletion_integrity subjects aag cap cap"
  by (rule reply_cap_deletion_integrityI1) simp

lemmas cnode_integrityI = cnode_integrity_def[THEN meta_eq_to_obj_eq,THEN iffD2,rule_format]
lemmas cnode_integrityD = cnode_integrity_def[THEN meta_eq_to_obj_eq,THEN iffD1,rule_format]
lemma cnode_integrityE:
  assumes hyp:"cnode_integrity subjects aag content content'"
  obtains "content l = content' l" | cap cap' where "content l = Some cap"
  and "content' l = Some cap'" and "reply_cap_deletion_integrity subjects aag cap cap'"
  using hyp cnode_integrityD by blast

subsubsection \<open>Introduction rules for object integrity\<close>

lemma troa_tro:
  "integrity_obj_atomic aag activate subjects l ko ko'
    \<Longrightarrow> integrity_obj aag activate subjects l ko ko'"
  unfolding integrity_obj_def by (rule r_into_rtranclp)

lemmas tro_lrefl = troa_lrefl[THEN troa_tro]
lemma tro_orefl:
  "ko = ko' \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
  unfolding integrity_obj_def by simp
lemmas tro_ntfn = troa_ntfn[THEN troa_tro]
lemmas tro_ep = troa_ep[THEN troa_tro]
lemmas tro_ep_unblock = troa_ep_unblock[THEN troa_tro]
lemmas tro_tcb_send = troa_tcb_send[THEN troa_tro]
lemmas tro_tcb_call = troa_tcb_call[THEN troa_tro]
lemmas tro_tcb_reply = troa_tcb_reply[THEN troa_tro]
lemmas tro_tcb_receive = troa_tcb_receive[THEN troa_tro]
lemmas tro_tcb_restart = troa_tcb_restart[THEN troa_tro]
lemmas tro_tcb_unbind = troa_tcb_unbind[THEN troa_tro]
lemmas tro_tcb_empty_ctable = troa_tcb_empty_ctable[THEN troa_tro]
lemmas tro_tcb_empty_caller = troa_tcb_empty_caller[THEN troa_tro]
lemmas tro_tcb_activate = troa_tcb_activate[THEN troa_tro]
lemmas tro_arch = troa_arch[THEN troa_tro]
lemmas tro_cnode = troa_cnode[THEN troa_tro]

lemmas tro_intros = tro_lrefl tro_orefl tro_ntfn tro_ep tro_ep_unblock tro_tcb_send tro_tcb_call
           tro_tcb_reply tro_tcb_receive tro_tcb_restart tro_tcb_unbind tro_tcb_empty_ctable
           tro_tcb_empty_caller tro_tcb_activate tro_arch tro_cnode

lemma tro_tcb_unbind':
  "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
     tcb' = tcb\<lparr>tcb_bound_notification := ntfn'\<rparr>;
     tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag \<rbrakk>
     \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
  apply (clarsimp simp:tcb_bound_notification_reset_integrity_def)
  apply (elim disjE)
   apply (rule tro_orefl;fastforce)
  apply (rule tro_tcb_unbind;fastforce)
  done

lemmas rtranclp_transp[intro!] = transp_rtranclp

lemma tro_transp[intro!]:
  "transp (integrity_obj aag activate es subjects)"
  unfolding integrity_obj_def by simp

lemmas tro_trans_spec = tro_transp[THEN transpD]

lemma tro_tcb_generic':
  "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
     tcb' = tcb \<lparr>tcb_bound_notification := ntfn', tcb_caller := cap', tcb_ctable := ccap'\<rparr>;
     tcb_bound_notification_reset_integrity (tcb_bound_notification tcb) ntfn' subjects aag;
     reply_cap_deletion_integrity subjects aag (tcb_caller tcb) cap';
     reply_cap_deletion_integrity subjects aag (tcb_ctable tcb) ccap' \<rbrakk>
     \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
  apply clarsimp
  apply (rule tro_trans_spec)
   apply (rule tro_tcb_empty_caller[OF refl refl refl];simp)
  apply (rule tro_trans_spec)
   apply (rule tro_tcb_empty_ctable[OF refl refl refl];simp)
  apply (rule tro_trans_spec)
   apply (rule tro_tcb_unbind'[OF refl refl refl];simp)
  apply (fastforce intro!: tro_orefl tcb.equality)
  done

lemma tro_tcb_reply':
  "\<lbrakk> ko = Some (TCB tcb); ko' = Some (TCB tcb');
     tcb' = tcb \<lparr>tcb_arch := arch_tcb_context_set ctxt' (tcb_arch tcb),
                 tcb_state := new_st, tcb_fault := None\<rparr>;
     new_st = Running \<or> (tcb_fault tcb \<noteq> None \<and> (new_st = Restart \<or> new_st = Inactive));
     direct_reply subjects aag l' tcb \<rbrakk>
     \<Longrightarrow> integrity_obj aag activate subjects l' ko ko'"
  apply (clarsimp simp:direct_reply_def simp del:not_None_eq)
  apply (erule disjE, (rule tro_tcb_reply[OF refl refl], force; force)) (* Warning: schematics *)
  apply (clarsimp simp del:not_None_eq)
  apply (rule tro_trans_spec)
   apply (frule allowed_call_blocked_def[THEN meta_eq_to_obj_eq,THEN iffD1],clarsimp)
   apply (rule tro_tcb_receive[OF refl refl refl, where new_st=BlockedOnReply];force)
  apply (rule tro_trans_spec)
   apply (rule tro_tcb_reply[OF refl refl refl, where new_st=new_st];force)
  by (fastforce intro!: tro_orefl tcb.equality)


context Access_AC_1 begin

lemma troa_tro_alt[elim!]:
  "integrity_obj_atomic aag activate subjects l ko ko'
   \<Longrightarrow> integrity_obj_alt aag activate subjects l ko ko'"
  apply (erule integrity_obj_atomic.cases)

  text \<open>Single out TCB cases for special handling. We manually simplify
        the TCB updates in the tro_alt rules using @{thm tcb.equality}.\<close>
    (* somewhat slow 10s *)
                apply (find_goal \<open>match premises in "ko = Some (TCB _)" \<Rightarrow> succeed\<close>,
                       ((erule(1) integrity_obj_alt.intros[OF tro_tagI],
                         (intro exI tcb.equality; solves \<open>simp\<close>));
                        fastforce simp: reply_cap_deletion_integrity_def direct_reply_def
                                        tcb_bound_notification_reset_integrity_def))+

       text \<open>Remaining cases.\<close>
       apply (fastforce intro: integrity_obj_alt.intros[OF tro_tagI])+

  done

end


lemma integrity_ready_queues_refl[simp]: "integrity_ready_queues aag subjects ptr s s"
  unfolding integrity_ready_queues_def by simp

(* FIXME MOVE *)
lemma caps_of_state_tcb':
  "\<lbrakk> get_tcb False p s = Some tcb; option_map fst (tcb_cap_cases idx) = Some getF \<rbrakk>
     \<Longrightarrow> caps_of_state s (p, idx) = Some (getF tcb)"
  apply (drule get_tcb_SomeD)
  apply clarsimp
  apply (drule (1) cte_wp_at_tcbI [where t = "(p, idx)" and P = "(=) (getF tcb)", simplified])
  apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

(* FIXME MOVE *)
lemma caps_of_state_tcb_cap_cases:
  "\<lbrakk> get_tcb False p s = Some tcb; idx \<in> dom tcb_cap_cases \<rbrakk>
     \<Longrightarrow> caps_of_state s (p, idx) = Some ((the (option_map fst (tcb_cap_cases idx))) tcb)"
  apply (clarsimp simp: dom_def)
  apply (erule caps_of_state_tcb')
  apply simp
  done

lemmas integrity_obj_simps [simp] =
  tro_orefl[OF refl]
  tro_lrefl[OF singletonI]
  trm_orefl[OF refl]
  trd_orefl[OF refl]
  tre_lrefl[OF singletonI]
  tre_orefl[OF refl]

lemma cdt_change_allowedI:
  "\<lbrakk> m \<Turnstile> pptr \<rightarrow>* ptr; cdt_direct_change_allowed aag subjects tcbsts pptr \<rbrakk>
     \<Longrightarrow> cdt_change_allowed aag subjects m tcbsts ptr"
  by (fastforce simp: cdt_change_allowed_def simp del: split_paired_Ex)

lemma cdt_change_allowedE:
  assumes "cdt_change_allowed aag subjects m tcbsts ptr"
  obtains pptr where "m \<Turnstile> pptr \<rightarrow>* ptr" "cdt_direct_change_allowed aag subjects tcbsts pptr"
  using assms by (fastforce simp: cdt_change_allowed_def simp del: split_paired_Ex)

lemma cdca_ccaI:
  "\<lbrakk> cdt_direct_change_allowed aag subjects tcbsts ptr \<rbrakk>
     \<Longrightarrow> cdt_change_allowed aag subjects m tcbsts ptr"
  by (fastforce simp: cdt_change_allowed_def simp del: split_paired_Ex)

lemmas cca_owned = cdt_change_allowedI[OF _ cdca_owned]
lemmas cca_reply' = cdt_change_allowedI[OF _ cdca_owned]
lemmas cca_direct[intro] = cdca_ccaI[OF cdca_owned]
lemmas cca_reply = cdca_ccaI[OF cdca_reply]

lemma cca_direct_single[intro]:
  "is_subject aag (fst ptr) \<Longrightarrow> cdt_change_allowed aag {pasSubject aag} m kh ptr"
  by (rule cca_direct) blast

lemma integrity_cdtE:
  assumes hyp:"integrity_cdt aag subjects m tcbsts ptr v v'"
  obtains "v = v'" | "cdt_change_allowed aag subjects m tcbsts ptr"
  using hyp integrity_cdt_def by blast

lemma integrity_cdt_refl[simp]: "integrity_cdt aag subjects m kh ptr v v"
  by (simp add: integrity_cdt_def)

lemma integrity_cdt_change_allowed[simp,intro]:
  "cdt_change_allowed aag subjects m kh ptr \<Longrightarrow> integrity_cdt aag subjects m kh ptr v v'"
  by (simp add: integrity_cdt_def)

lemmas integrity_cdt_intros = integrity_cdt_refl integrity_cdt_change_allowed

lemmas integrity_cdt_direct = cca_direct[THEN  integrity_cdt_change_allowed]

lemma integrity_cdt_list_refl[simp]: "integrity_cdt_list aag subjects m kh ptr v v"
  by (simp add: integrity_cdt_list_def)

lemma integrity_cdt_list_filt:
  "filtered_eq (cdt_change_allowed aag subjects m kh) l l'
   \<Longrightarrow> integrity_cdt_list aag subjects m kh ptr l l'"
  by (simp add: integrity_cdt_list_def)

lemma integrity_cdt_list_change_allowed:
  "cdt_change_allowed aag subjects m kh ptr \<Longrightarrow> integrity_cdt_list aag subjects m kh ptr l l'"
  by (simp add: integrity_cdt_list_def)

lemmas integrity_cdt_list_intros = integrity_cdt_list_filt integrity_cdt_list_change_allowed

lemma integrity_cdt_listE:
  assumes hyp:"integrity_cdt_list aag subjects m kh ptr l l'"
  obtains "filtered_eq (cdt_change_allowed aag subjects m kh) l l'" |
          "cdt_change_allowed aag subjects m kh ptr"
  using hyp integrity_cdt_list_def by blast

lemma integrity_interrupts_refl[simp]: "integrity_interrupts aag subjects ptr v v"
  by (simp add: integrity_interrupts_def)

section \<open>Integrity transitivity\<close>

subsection \<open>Object integrity transitivity\<close>

lemma tcb_bound_notification_reset_integrity_trans[elim]:
  "\<lbrakk> tcb_bound_notification_reset_integrity ntfn ntfn' subjects aag;
     tcb_bound_notification_reset_integrity ntfn' ntfn'' subjects aag \<rbrakk>
     \<Longrightarrow> tcb_bound_notification_reset_integrity ntfn ntfn'' subjects aag"
  by (auto simp: tcb_bound_notification_reset_integrity_def)

lemma reply_cap_deletion_integrity_trans[elim]:
  "\<lbrakk> reply_cap_deletion_integrity subjects aag cap cap';
     reply_cap_deletion_integrity subjects aag cap' cap'' \<rbrakk>
     \<Longrightarrow> reply_cap_deletion_integrity subjects aag cap cap''"
  by (auto simp: reply_cap_deletion_integrity_def)


lemma cnode_integrity_trans[elim]:
  "\<lbrakk> cnode_integrity subjects aag cont cont';
     cnode_integrity subjects aag cont' cont'' \<rbrakk>
     \<Longrightarrow> cnode_integrity subjects aag cont cont''"
   unfolding cnode_integrity_def
   apply (intro allI)
   apply (drule_tac x=l in spec)+
   by fastforce

lemma tcb_bound_notification_reset_eq_or_none:
  "tcb_bound_notification_reset_integrity ntfn ntfn' subjects aag \<Longrightarrow> ntfn = ntfn' \<or> ntfn' = None"
  by (auto simp: tcb_bound_notification_reset_integrity_def)


context Access_AC_1 begin

lemma tro_alt_trans_spec: (* this takes a long time to process *)
  "\<lbrakk> integrity_obj_alt aag activate es subjects ko ko';
     integrity_obj_alt aag activate es subjects ko' ko'' \<rbrakk>
     \<Longrightarrow> integrity_obj_alt aag activate es subjects ko ko''"
  (* We need to consider nearly 200 cases, one for each possible pair
     of integrity steps. We use the tro_tags to select subsets of goals
     that can be solved by the same method. *)

  (* Expand the first integrity step *)
  apply (erule integrity_obj_alt.cases[where ko=ko and ko'=ko'])

  (* LRefl and ORefl trivially collapse into the second integrity step *)
  apply (find_goal \<open>match premises in "tro_tag LRefl" \<Rightarrow> -\<close>)
  subgoal by (rule tro_alt_lrefl, simp)

  apply (find_goal \<open>match premises in "tro_tag ORefl" \<Rightarrow> -\<close>)
  subgoal by simp

  (* Now re-tag the first step with tro_tag' *)
  apply (all \<open>simp only:tro_tag_to_prime\<close>)
  (* Expand the second integrity step, which will be tagged with tro_tag *)
  apply (all \<open>erule integrity_obj_alt.cases\<close>)

  (* There are some special cases that would be too slow or unsolvable by the bulk tactics.
     We move them up here and solve manually *)
  apply (find_goal \<open>match premises in "tro_tag' TCBReply" and "tro_tag TCBActivate" \<Rightarrow> -\<close>)
  apply (clarsimp, rule tro_alt_tcb_reply[OF tro_tagI refl refl],
         (rule exI; rule tcb.equality; simp); fastforce)

  apply (find_goal \<open>match premises in "tro_tag' TCBReceive" and "tro_tag TCBReply" \<Rightarrow> -\<close>)
  apply (clarsimp, rule tro_alt_tcb_reply[OF tro_tagI refl refl],
         (rule exI; rule tcb.equality; simp);
          fastforce simp: direct_reply_def allowed_call_blocked_def)

  apply (find_goal \<open>match premises in "tro_tag TCBGeneric" and "tro_tag' TCBRestart" \<Rightarrow> -\<close>)
  subgoal
    apply (erule integrity_obj_alt.intros[simplified tro_tag_to_prime])
            apply (simp | rule tcb.equality | fastforce)+
    done

  apply (find_goal \<open>match premises in "tro_tag TCBActivate" and "tro_tag' TCBRestart" \<Rightarrow> -\<close>)
  apply (rule tro_alt_tcb_restart[OF tro_tagI], (fastforce simp: tcb.splits fun_upd_def)+)[1]

  apply (find_goal \<open>match premises in "tro_tag REp" and "tro_tag' REp" \<Rightarrow> -\<close>)
  subgoal by (erule integrity_obj_alt.intros, (rule refl | assumption)+)

  (* Select groups of subgoals by tag, then solve with the given methods *)
  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag LRefl"]\<close>
             | time_methods \<open>fastforce intro: tro_alt_lrefl\<close>\<close>)

  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag ORefl"]\<close>
             | time_methods \<open>solves \<open>
                   drule sym[where t="ko''"];
                   erule integrity_obj_alt.intros[simplified tro_tag_to_prime];
                   solves \<open>simp\<close>\<close>\<close>\<close>)

  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag RNtfn"] thin_rl[of "tro_tag' RNtfn"]\<close>
             | time_methods \<open>fastforce intro: tro_alt_ntfn\<close>\<close>)

  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag REp"]
                    | erule thin_rl[of "tro_tag' REp"]
                    | erule thin_rl[of "tro_tag RArch"]
                    | erule thin_rl[of "tro_tag' RArch"]
                    | erule thin_rl[of "tro_tag EpUnblock"]
                    | erule thin_rl[of "tro_tag' EpUnblock"]
                    | erule thin_rl[of "tro_tag RCNode"]
                    | erule thin_rl[of "tro_tag' RCNode"]\<close>
             | time_methods \<open>fastforce intro: integrity_obj_alt.intros
                                        simp: arch_tro_alt_trans_spec\<close>\<close>)

  (* TCB-TCB steps, somewhat slow *)
  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag TCBGeneric"]\<close>
             | time_methods \<open>solves \<open>
                    erule integrity_obj_alt.intros[simplified tro_tag_to_prime],
                    (assumption | rule refl
                    | ((erule exE)+)?, (rule exI)?, force intro: tcb.equality)+\<close>\<close>\<close>)

  apply (all \<open>fails \<open>erule thin_rl[of "tro_tag' TCBGeneric"]\<close>
             | time_methods \<open>solves \<open>
                    erule integrity_obj_alt.intros,
                    (assumption | rule refl
                    | (elim exE)?, (intro exI)?, fastforce intro: tcb.equality
                    | fastforce simp: indirect_send_def direct_send_def direct_call_def direct_reply_def
                                dest: tcb_bound_notification_reset_eq_or_none)+\<close>\<close>\<close>)

  apply (time_methods \<open>
           succeeds \<open>match premises in T: "tro_tag _" and T': "tro_tag' _" \<Rightarrow>
                                       \<open>print_fact T, print_fact T'\<close>\<close>,
           fastforce intro: integrity_obj_alt.intros tcb.equality
                     simp: indirect_send_def direct_send_def direct_call_def direct_reply_def
                           call_blocked_def allowed_call_blocked_def\<close>)+

  done

lemma tro_alt_transp[intro!]:
  "transp (integrity_obj_alt (aag :: 'a PAS) activate es subjects)"
  by (rule transpI) (rule tro_alt_trans_spec)

lemma tro_alt_reflp[intro!]:
  "reflp (integrity_obj_alt aag activate es subjects)"
  by (rule reflpI) (rule tro_alt_orefl; blast)

lemma tro_tro_alt[elim!]:
  "integrity_obj aag activate es subjects ko ko'
  \<Longrightarrow> integrity_obj_alt aag activate es subjects ko ko'"
  unfolding integrity_obj_def
  by (subst rtranclp_id[symmetric]; fastforce elim: rtranclp_mono[THEN predicate2D,rotated])

lemmas integrity_objE = tro_tro_alt[THEN integrity_obj_alt.cases
                                          [simplified tro_tag_def True_implies_equals]]

end


lemma tro_trans:
  "\<lbrakk> integrity_obj_state aag activate es s s'; integrity_obj_state aag activate es s' s'' \<rbrakk>
     \<Longrightarrow> integrity_obj_state aag activate es s s''"
  unfolding integrity_obj_def
  apply clarsimp
  apply (drule_tac x = x in spec)+
  by force

lemma tre_trans:
  "\<lbrakk> (\<forall>x. integrity_eobj aag es (pasObjectAbs aag x) (ekh x) (ekh' x));
     (\<forall>x. integrity_eobj aag es (pasObjectAbs aag x) (ekh' x) (ekh'' x)) \<rbrakk>
     \<Longrightarrow> (\<forall>x. integrity_eobj aag es (pasObjectAbs aag x) (ekh x) (ekh'' x))"
  by (fastforce elim!: integrity_eobj.cases intro: integrity_eobj.intros)


subsection \<open>Integrity transitivity\<close>

lemma tcb_caller_slot_empty_on_recieve:
  "\<lbrakk> valid_mdb s; valid_objs s; kheap s tcb_ptr = Some (TCB tcb); ep_recv_blocked ep (tcb_state tcb) \<rbrakk>
     \<Longrightarrow> tcb_caller tcb = NullCap \<and> cdt s (tcb_ptr,(tcb_cnode_index 3)) = None \<and>
         descendants_of (tcb_ptr,(tcb_cnode_index 3)) (cdt s) = {}"
  apply (simp only:valid_objs_def)
  apply (drule bspec,fastforce)
  apply (simp add:valid_obj_def)
  apply (simp only:valid_tcb_def)
  apply (drule conjunct1)
  apply (drule_tac x="the (tcb_cap_cases (tcb_cnode_index 3))" in  bspec)
   apply (fastforce simp:tcb_cap_cases_def)
  apply (simp add:tcb_cap_cases_def split: thread_state.splits)
  apply (subgoal_tac "caps_of_state s (tcb_ptr, tcb_cnode_index 3) = Some NullCap")
   apply (simp only: valid_mdb_def2, drule conjunct1)
   apply (intro conjI)
    apply (simp add: mdb_cte_at_def)
    apply (rule classical)
    apply fastforce
   apply (rule mdb_cte_at_no_descendants, fastforce+)[1]
  apply (fastforce simp add: tcb_cnode_map_def caps_of_state_tcb_index_trans[OF get_tcb_rev])
  done

(* FIXME MOVE next to tcb_states_of_state definition *)
lemma tcb_states_of_state_kheap:
   "\<lbrakk> kheap s slot = Some (TCB tcb)\<rbrakk>
      \<Longrightarrow> tcb_states_of_state s slot = Some (tcb_state tcb)"
  by (simp add:tcb_states_of_state_def get_tcb_def split: option.splits kernel_object.splits)

lemma tcb_states_of_state_kheapI:
   "\<lbrakk> kheap s slot = Some (TCB tcb); tcb_state tcb = tcbst \<rbrakk>
      \<Longrightarrow> tcb_states_of_state s slot = Some tcbst"
  by (simp add: tcb_states_of_state_def get_tcb_def split: option.splits kernel_object.splits)

lemma tcb_states_of_state_kheapD:
  "tcb_states_of_state s slot = Some tcbst \<Longrightarrow>
   \<exists>tcb. kheap s slot = Some (TCB tcb) \<and> tcb_state tcb = tcbst"
  by (simp add:tcb_states_of_state_def get_tcb_def split: option.splits kernel_object.splits)

lemma tcb_states_of_state_kheapE:
  assumes "tcb_states_of_state s slot = Some tcbst"
  obtains tcb where "kheap s slot = Some (TCB tcb)" "tcb_state tcb = tcbst"
  using assms tcb_states_of_state_kheapD by blast

lemma cdt_change_allowed_to_child:
  "\<lbrakk> cdt_change_allowed aag subjects m tcbsts pptr; m ptr = Some pptr \<rbrakk>
     \<Longrightarrow> cdt_change_allowed aag subjects m tcbsts ptr"
  apply (elim cdt_change_allowedE)
  apply (erule cdt_change_allowedI[rotated])
  by (fastforce intro: rtrancl_into_rtrancl simp: cdt_parent_of_def)

lemma trinterrupts_trans:
  "\<lbrakk> (\<forall>x. integrity_interrupts aag subjects x (interrupt_irq_node s x, interrupt_states s x)
                                              (interrupt_irq_node s' x, interrupt_states s' x));
     (\<forall>x. integrity_interrupts aag subjects x (interrupt_irq_node s' x, interrupt_states s' x)
                                              (interrupt_irq_node s'' x, interrupt_states s'' x)) \<rbrakk>
     \<Longrightarrow> (\<forall>x. integrity_interrupts aag subjects x (interrupt_irq_node s x, interrupt_states s x)
                                                  (interrupt_irq_node s'' x, interrupt_states s'' x))"
  apply (simp add: integrity_interrupts_def del: split_paired_All)
  apply metis
  done

lemma trrqs_trans:
  "\<lbrakk> (\<forall>d p. integrity_ready_queues aag subjects (pasDomainAbs aag d)
                                  (ready_queues s d p) (ready_queues s' d p));
     (\<forall>d p. integrity_ready_queues aag subjects (pasDomainAbs aag d)
                                   (ready_queues s' d p) (ready_queues s'' d p)) \<rbrakk>
     \<Longrightarrow> (\<forall>d p. integrity_ready_queues aag subjects (pasDomainAbs aag d)
                                       (ready_queues s d p) (ready_queues s'' d p))"
  apply (clarsimp simp: integrity_ready_queues_def)
  apply (metis append_assoc)
  done


context Access_AC_1 begin

lemma cdt_direct_change_allowed_backward:
  "\<lbrakk> integrity_obj_state aag activate subjects s s';
     cdt_direct_change_allowed aag subjects (tcb_states_of_state s') ptr \<rbrakk>
     \<Longrightarrow> cdt_direct_change_allowed aag subjects (tcb_states_of_state s) ptr"
  apply (erule cdt_direct_change_allowed.cases)
   subgoal by (rule cdca_owned)
  apply (erule tcb_states_of_state_kheapE)
  by (drule spec,
      erule integrity_objE, erule cdca_owned;
      (elim exE)?;
      simp;
      rule cdca_reply[rotated], assumption, assumption,
      fastforce elim:tcb_states_of_state_kheapI simp:direct_call_def)

lemma cdt_change_allowed_backward:
  "\<lbrakk> integrity_obj_state aag activate subjects s s';
     integrity_cdt_state aag subjects s s';
     cdt_change_allowed aag subjects (cdt s') (tcb_states_of_state s') ptr \<rbrakk>
     \<Longrightarrow> cdt_change_allowed aag subjects (cdt s) (tcb_states_of_state s) ptr"
  apply (elim cdt_change_allowedE)
  apply (drule(1) cdt_direct_change_allowed_backward)
  apply (erule rtrancl_induct)
   subgoal by (rule cdca_ccaI)
  apply (rename_tac pptr0 ptr)
  apply (frule_tac x=ptr in spec)
  apply (elim integrity_cdtE; simp; elim conjE)
  apply (erule cdt_change_allowed_to_child)
  by (simp add: cdt_parent_of_def)

lemma trcdt_trans:
  "\<lbrakk> integrity_cdt_state aag subjects s s' ;
     integrity_obj_state aag activate subjects s s' ;
     integrity_cdt_state aag subjects s' s'' \<rbrakk>
     \<Longrightarrow> integrity_cdt_state aag subjects s s''"
  apply (intro allI)
  apply (frule_tac x=x in spec)
  apply (frule_tac x=x in spec[where P = "\<lambda>x. integrity_cdt _ _ (cdt s') _ x (_ x) (_ x)"])
  apply (erule integrity_cdtE)+
    apply simp
  by (blast dest: cdt_change_allowed_backward)+

lemma trcdtlist_trans:
  "\<lbrakk> integrity_cdt_list_state aag subjects s s' ;
     integrity_obj_state aag activate subjects s s' ;
     integrity_cdt_state aag subjects s s' ;
     integrity_cdt_list_state aag subjects s' s'' \<rbrakk>
     \<Longrightarrow> integrity_cdt_list_state aag subjects s s''"
  apply (intro allI)
  apply (drule_tac x=x in spec [where P="\<lambda>ptr. integrity_cdt_list _ _ _ _ ptr (_ ptr) (_ ptr)"] )+
  apply (erule integrity_cdt_listE)+
    apply (rule integrity_cdt_list_filt)
    apply (simp del: split_paired_All split_paired_Ex)
    apply (erule weaken_filter_eq')
  by (blast intro: integrity_cdt_list_intros dest: cdt_change_allowed_backward)+

(* FIXME RENAME *)
lemma tsos_tro:
  "\<lbrakk> integrity_obj_state aag activate subjects s s'; tcb_states_of_state s' p = Some a;
     receive_blocked_on ep a; pasObjectAbs aag p \<notin> subjects \<rbrakk>
     \<Longrightarrow> tcb_states_of_state s p = Some a"
  apply (drule_tac x = p in spec)
  apply (erule integrity_objE, simp_all add: tcb_states_of_state_def get_tcb_def)
  by fastforce+

lemma can_receive_ipc_backward:
  "\<lbrakk> integrity_obj_state aag activate subjects s s'; tcb_states_of_state s' p = Some a;
     can_receive_ipc a; pasObjectAbs aag p \<notin> subjects \<rbrakk>
     \<Longrightarrow> case tcb_states_of_state s p of None \<Rightarrow> False | Some x \<Rightarrow> can_receive_ipc x"
  apply (drule_tac x = p in spec)
  apply (erule integrity_objE;
         (fastforce simp: tcb_states_of_state_def get_tcb_def
                         call_blocked_def allowed_call_blocked_def
                   split: option.splits kernel_object.splits
         | cases a \<comment> \<open>only split when needed\<close>)+)
  done

lemma tsos_tro_running:
  "\<lbrakk> \<forall>x. integrity_obj aag activate subjects (pasObjectAbs aag x) (kheap s x) (kheap s' x);
     tcb_states_of_state s p = Some Running; pasObjectAbs aag p \<notin> subjects \<rbrakk>
     \<Longrightarrow> tcb_states_of_state s' p = Some Running"
  by (drule_tac x=p in spec, erule integrity_objE,
      simp_all add: tcb_states_of_state_def get_tcb_def indirect_send_def direct_send_def
                    direct_call_def direct_reply_def call_blocked_def allowed_call_blocked_def)

end


locale Access_AC_2 = Access_AC_1 +
  assumes auth_ipc_buffers_tro:
    "\<And>x. \<lbrakk> integrity_obj_state aag activate subjects s s';
            x \<in> auth_ipc_buffers s' p; pasObjectAbs aag p \<notin> subjects \<rbrakk>
            \<Longrightarrow> x \<in> auth_ipc_buffers s p "
  and integrity_asids_refl[simp]:
    "\<And>x. integrity_asids aag subjects x a (s :: det_ext state) s"
  and trasids_trans:
    "\<lbrakk> (\<forall>x a. integrity_asids aag subjects x a s (s' :: det_ext state));
       (\<forall>x a. integrity_asids aag subjects x a s' (s'' :: det_ext state))\<rbrakk>
       \<Longrightarrow> (\<forall>x a. integrity_asids aag subjects x a s s'')"
  and integrity_asids_update_autarch:
    "\<lbrakk> \<forall>x a. integrity_asids aag {pasSubject aag} x a s s'; is_subject aag ptr \<rbrakk>
       \<Longrightarrow> \<forall>x a. integrity_asids aag {pasSubject aag} x a s (s'\<lparr>kheap := kheap s'(ptr \<mapsto> obj)\<rparr>)"
begin

section \<open>Generic AC stuff\<close>

subsection \<open>Basic integrity lemmas\<close>

lemma integrity_trans:
  assumes t1: "integrity_subjects subjects aag activate X s s'"
  and     t2: "integrity_subjects subjects aag activate X s' s''"
  shows  "integrity_subjects subjects aag activate X s s''"
proof -
  from t1 have tro1: "integrity_obj_state aag activate subjects s s'"
    unfolding integrity_subjects_def by simp
  from t2 have tro2: "integrity_obj_state aag activate subjects s' s''"
    unfolding integrity_subjects_def by simp

  have intm: "\<forall>x. integrity_mem aag subjects x
                  (tcb_states_of_state s) (tcb_states_of_state s'') (auth_ipc_buffers s) X
                  (underlying_memory (machine_state s) x)
                  (underlying_memory (machine_state s'') x)" (is "\<forall>x. ?P x s s''")
  proof
    fix x
    from t1 t2 have m1: "?P x s s'" and m2: "?P x s' s''" unfolding integrity_subjects_def by auto

    from m1 show "?P x s s''"
    proof cases
      case trm_lrefl thus ?thesis by (rule integrity_mem.intros)
    next
      case trm_globals thus ?thesis by (rule integrity_mem.intros)
    next
      case trm_orefl
      from m2 show ?thesis
      proof cases
        case (trm_ipc p')

        show ?thesis
        proof (rule integrity_mem.trm_ipc)
          from trm_ipc show "case_option False can_receive_ipc (tcb_states_of_state s p')"
            by (fastforce split: option.splits dest: can_receive_ipc_backward [OF tro1])

          from trm_ipc show "x \<in> auth_ipc_buffers s p'"
            by (fastforce split: option.splits intro: auth_ipc_buffers_tro [OF tro1])
        qed (simp_all add: trm_ipc)
      qed (auto simp add: trm_orefl intro: integrity_mem.intros)
    next
      case trm_write thus ?thesis by (rule integrity_mem.intros)
    next
      case (trm_ipc p')
      note trm_ipc1 = trm_ipc

      from m2 show ?thesis
      proof cases
        case trm_orefl
        thus ?thesis using trm_ipc1
          by (auto intro!: integrity_mem.trm_ipc simp add: restrict_map_Some_iff elim!: tsos_tro_running [OF tro2, rotated])
      next
        case (trm_ipc p'')
        show ?thesis
        proof (cases "p' = p''")
          case True thus ?thesis using trm_ipc trm_ipc1 by (simp add: restrict_map_Some_iff)
        next
          (* 2 tcbs sharing same IPC buffer, we can appeal to either t1 or t2 *)
          case False
          thus ?thesis using trm_ipc1
            by (auto intro!: integrity_mem.trm_ipc simp add: restrict_map_Some_iff elim!: tsos_tro_running [OF tro2, rotated])
        qed
      qed (auto simp add: trm_ipc intro: integrity_mem.intros)
    qed
  qed

  moreover have "\<forall>x. integrity_device aag subjects x
                  (tcb_states_of_state s) (tcb_states_of_state s'')
                  (device_state (machine_state s) x)
                  (device_state (machine_state s'') x)" (is "\<forall>x. ?P x s s''")
  proof
    fix x
    from t1 t2 have m1: "?P x s s'" and m2: "?P x s' s''" unfolding integrity_subjects_def by auto

    from m1 show "?P x s s''"
    proof cases
      case trd_lrefl thus ?thesis by (rule integrity_device.intros)
    next
      case torel1: trd_orefl
      from m2 show ?thesis
      proof cases
        case (trd_lrefl) thus ?thesis by (rule integrity_device.trd_lrefl)
      next
        case trd_orefl thus ?thesis
          by (simp add: torel1)
      next
        case trd_write thus ?thesis by (rule integrity_device.trd_write)
      qed
    next
      case trd_write thus ?thesis by (rule integrity_device.intros)
    qed
  qed
  thus ?thesis using tro_trans[OF tro1 tro2] t1 t2 intm
    apply (clarsimp simp add: integrity_subjects_def simp del:  split_paired_All)
    apply (frule(2) trcdt_trans)
    apply (frule(3) trcdtlist_trans)
    apply (frule(1) trinterrupts_trans[simplified])
    apply (frule(1) trasids_trans[simplified])
    apply (frule(1) tre_trans[simplified])
    apply (frule(1) trrqs_trans[simplified])
    by blast
qed

lemma integrity_refl [simp]:
  "integrity_subjects S aag activate X s s"
  unfolding integrity_subjects_def
  by simp

lemma integrity_update_autarch:
  "\<lbrakk> integrity aag X st s; is_subject aag ptr \<rbrakk>
     \<Longrightarrow> integrity aag X st (s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr>)"
  unfolding integrity_subjects_def
  apply (intro conjI,simp_all)
    apply clarsimp
    apply (drule_tac x = x in spec, erule integrity_mem.cases)
        apply ((auto intro: integrity_mem.intros)+)[4]
    apply (erule trm_ipc, simp_all)
    apply (clarsimp simp: restrict_map_Some_iff tcb_states_of_state_def get_tcb_def
      obind_def ta_filter_def)
   apply clarsimp
   apply (drule_tac x = x in spec, erule integrity_device.cases)
     apply (erule integrity_device.trd_lrefl)
    apply (erule integrity_device.trd_orefl)
   apply (erule integrity_device.trd_write)
  apply (clarsimp simp: integrity_asids_update_autarch)
  done

lemma integrity_update_ta_autarch:
  "\<lbrakk> integrity aag X st s; is_subject aag ptr \<rbrakk>
     \<Longrightarrow> integrity aag X st (ms_ta_obj_update ptr obj (s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr>))"
  unfolding integrity_subjects_def
  apply (intro conjI,simp_all)
    apply clarsimp
    apply (drule_tac x = x in spec, erule integrity_mem.cases)
        apply ((auto intro: integrity_mem.intros)+)[4]
    apply (erule trm_ipc, simp_all)
    apply (clarsimp simp: restrict_map_Some_iff tcb_states_of_state_def get_tcb_def
      obind_def ta_filter_def)
   apply clarsimp
   apply (drule_tac x = x in spec, erule integrity_device.cases)
     apply (erule integrity_device.trd_lrefl)
    apply (erule integrity_device.trd_orefl)
   apply (erule integrity_device.trd_write)
  apply (clarsimp simp: integrity_asids_update_autarch)
  done

lemma set_object_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag ptr)\<rbrace>
   set_object True ptr obj
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (rule integrity_update_ta_autarch, simp_all)
  done

end

context pspace_update_eq begin

lemma thread_st_auth[iff]: "thread_st_auth (f s) = thread_st_auth s"
  by (simp add: thread_st_auth_def pspace get_tcb_def swp_def tcb_states_of_state_def
    obind_def ta_filter_def)

lemma thread_bound_ntfns[iff]: "thread_bound_ntfns (f s) = thread_bound_ntfns s"
  by (simp add: thread_bound_ntfns_def pspace get_tcb_def swp_def obind_def ta_filter_def
    split: option.splits)

lemma integrity_update_eq[iff]:
  "tcb_states_of_state (f s) = tcb_states_of_state s"
  by (simp add: pspace tcb_states_of_state_def get_tcb_def obind_def ta_filter_def)

end

context Access_AC_2 begin

(* TA-agnosticism of integrity and pas_refined.
   This appears to be the earliest place we can prove these. -robs *)
lemma integrity_ta_agnostic: "ta_agnostic (integrity aag X st)"
  by (clarsimp simp:ta_agnostic_def integrity_subjects_def integrity_obj_def integrity_mem.simps)

(* Following the conventions of `pas_refined_irq_state_independent` (ArchAccess_AC). -robs *)
lemma integrity_ms_ta_independent[intro!, simp]:
  "integrity aag X st (ms_ta_update taf s) = integrity aag X st s"
  using integrity_ta_agnostic
  by (simp add: ta_agnostic_def)

(* Alternative version that deals with kheap updates. -robs *)
lemma integrity_ms_ta_independent'[intro!, simp]:
  "integrity aag X st ((ms_ta_update taf s \<lparr>kheap := something\<rparr>)) =
   integrity aag X st (s \<lparr>kheap := something\<rparr>)"
  by (clarsimp simp:ta_agnostic_def integrity_subjects_def integrity_obj_def integrity_mem.simps
    Arch.integrity_asids_def tcb_states_of_state_def get_tcb_def obind_def ta_filter_def)

lemma pas_refined_ta_agnostic: "ta_agnostic (pas_refined aag)"
  by (clarsimp simp:ta_agnostic_def pas_refined_def auth_graph_map_def state_objs_to_policy_def)

lemma pas_refined_ms_ta_independent[intro!, simp]:
  "pas_refined aag (ms_ta_update taf s) = pas_refined aag s"
  using pas_refined_ta_agnostic
  by (simp add: ta_agnostic_def)

(* FIXME: Should these helpers for valid_caps be moved to AInvs? -robs *)
lemma valid_caps_ta_agnostic: "ta_agnostic (valid_caps cs)"
  by (clarsimp simp:ta_agnostic_def valid_caps_def)

lemma valid_caps_ms_ta_independent[intro!, simp]:
  "valid_caps cs (ms_ta_update taf s) = valid_caps cs s"
  using valid_caps_ta_agnostic
  by (metis ta_agnostic_def)

lemma eintegrity_sa_update[simp]:
  "integrity aag X st (scheduler_action_update f s) = integrity aag X st s"
  by (simp add: integrity_subjects_def)

lemma trans_state_back[simp]:
  "trans_state (\<lambda>_. exst s) s = s"
  by simp

declare wrap_ext_op_det_ext_ext_def[simp]

crunch integrity[wp]: set_thread_state_ext "integrity aag X st"
  (wp: touch_objects_wp)

(* FIXME: Crunch does not discover the right precondition (presumably it used to); Ryan B (@ryybrr)
   noticed the same for `set_cap_integrity_autarch` (CNode_AC) when he did the arch-split. -robs *)
lemma set_thread_state_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag ptr)\<rbrace>
   set_thread_state ptr ts
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp:set_thread_state_def wp:set_object_integrity_autarch touch_object_wp')

crunch integrity_autarch: set_thread_state "integrity aag X st"

lemmas integrity_def = integrity_subjects_def

subsection \<open>Out of subject cap manipulation\<close>

(* FIXME MOVE *)
lemma all_children_descendants_of:
  "\<lbrakk> all_children P m; p \<in> descendants_of q m; P q \<rbrakk> \<Longrightarrow> P p"
  apply (simp add: descendants_of_def)
  apply (erule trancl_induct[where P=P])
   apply (unfold cdt_parent_of_def)
   apply (erule(2) all_childrenD)+
  done

lemmas all_children_parent_of_trancl =
  all_children_descendants_of[simplified descendants_of_def,simplified]

lemma all_children_parent_of_rtrancl:
  "\<lbrakk> all_children P m; m \<Turnstile> q \<rightarrow>* p; P q \<rbrakk> \<Longrightarrow> P p"
  by (drule rtranclD, elim conjE disjE; blast dest: all_children_parent_of_trancl)

lemma pas_refined_all_children':
  "\<lbrakk> valid_mdb s; pas_refined aag s; m = (cdt s) \<rbrakk>
     \<Longrightarrow> all_children (\<lambda>x. is_subject aag (fst x) \<or> is_transferable (caps_of_state s x)) m"
  apply (rule all_childrenI)
  apply (erule disjE)
   apply (simp add: pas_refined_def,elim conjE)
   apply (rule disjCI)
   apply (subgoal_tac "abs_has_auth_to aag Control (fst p) (fst c)")
    apply (fastforce elim: aag_wellformed_control_is_owns[THEN iffD1])
   apply (simp add: state_objs_to_policy_def auth_graph_map_def)
   apply (erule set_mp)
   apply (frule(1) sbta_cdt)
   apply force
  apply (rule disjI2)
  by (rule is_transferable_all_children[THEN all_childrenD]; solves \<open>simp\<close>)

lemmas pas_refined_all_children = pas_refined_all_children'[OF _ _ refl]

(* FIXME MOVE just after cte_wp_at_cases2 *)
lemma caps_of_state_def':
  "caps_of_state s slot =
   (case kheap s (fst slot) of
      Some (TCB tcb) \<Rightarrow> tcb_cnode_map tcb (snd slot)
    | Some (CNode sz content) \<Rightarrow> (if well_formed_cnode_n sz content then content (snd slot) else None)
    | _ \<Rightarrow> None)"
  by (fastforce simp: caps_of_state_cte_wp_at cte_wp_at_cases2
               split: option.splits kernel_object.splits)

lemma caps_of_state_cnode:
  "\<lbrakk> kheap s pos = Some (CNode sz content); well_formed_cnode_n sz content\<rbrakk>
     \<Longrightarrow> caps_of_state s (pos,addr) = content addr"
  by (simp add:caps_of_state_def')

lemma caps_of_state_tcb:
  "kheap s pos = Some (TCB tcb) \<Longrightarrow> caps_of_state s (pos,addr) = tcb_cnode_map tcb addr"
  by (simp add:caps_of_state_def')

end


(* FIXME MOVE next to tcb_cnode_cases_simps *)
lemma tcb_cnode_map_simps[simp]:
  "tcb_cnode_map tcb (tcb_cnode_index 0) = Some (tcb_ctable tcb)"
  "tcb_cnode_map tcb (tcb_cnode_index (Suc 0)) = Some (tcb_vtable tcb)"
  "tcb_cnode_map tcb (tcb_cnode_index 2) = Some (tcb_reply tcb)"
  "tcb_cnode_map tcb (tcb_cnode_index 3) = Some (tcb_caller tcb)"
  "tcb_cnode_map tcb (tcb_cnode_index 4) = Some (tcb_ipcframe tcb)"
  by (simp_all add: tcb_cnode_map_def)

(* FIXME MOVE *)
lemma valid_mdb_reply_mdb[elim!]:
  "valid_mdb s \<Longrightarrow> reply_mdb (cdt s) (caps_of_state s)"
  by (simp add:valid_mdb_def)

(* FIXME MOVE *)
lemma invs_reply_mdb[elim!]:
  "invs s \<Longrightarrow> reply_mdb (cdt s) (caps_of_state s)"
  by (simp add:invs_def valid_state_def valid_mdb_def)

lemma parent_of_rtrancl_no_descendant:
  "\<lbrakk> m \<Turnstile> pptr \<rightarrow>* ptr; descendants_of pptr m = {} \<rbrakk> \<Longrightarrow> pptr = ptr"
  by (fastforce simp add:rtrancl_eq_or_trancl descendants_of_def)

(* FIXME MOVE *)
lemma tcb_atD:
  "tcb_at ptr s \<Longrightarrow> \<exists>tcb. kheap s ptr = Some (TCB tcb)"
  by (cases "the (kheap s ptr)";fastforce simp:obj_at_def is_tcb_def)

(* FIXME MOVE *)
lemma tcb_atE:
  assumes hyp: "tcb_at ptr s"
  obtains tcb where "kheap s ptr = Some (TCB tcb)"
  using hyp[THEN tcb_atD] by blast

(*FIXME MOVE *)
lemma tcb_atI:
  "kheap s ptr = Some (TCB tcb) \<Longrightarrow> tcb_at ptr s"
  by (simp add:obj_at_def is_tcb_def)


context Access_AC_2 begin

lemma descendant_of_caller_slot:
  "\<lbrakk> valid_mdb s; valid_objs s; tcb_at t s \<rbrakk> \<Longrightarrow> descendants_of (t, tcb_cnode_index 3) (cdt s) = {}"
  apply (frule(1) tcb_caller_cap)
  apply (clarsimp simp add:cte_wp_at_caps_of_state is_cap_simps; elim disjE ;clarsimp)
  subgoal by (intro allI no_children_empty_desc[THEN iffD1] reply_cap_no_children)
  apply (drule valid_mdb_mdb_cte_at)
  apply (erule mdb_cte_at_no_descendants)
  apply (simp add:cte_wp_at_caps_of_state)
  done

lemma cca_to_transferable_or_subject:
  "\<lbrakk> valid_objs s; valid_mdb s; pas_refined aag s; cdt_change_allowed' aag ptr s \<rbrakk>
     \<Longrightarrow> is_subject aag (fst ptr) \<or> is_transferable (caps_of_state s ptr)"
  apply (elim cdt_change_allowedE cdt_direct_change_allowed.cases)
   apply (rule all_children_parent_of_rtrancl[OF pas_refined_all_children]; blast)
  apply (simp add:rtrancl_eq_or_trancl,elim disjE conjE)
   apply (simp add:direct_call_def, elim conjE)
   apply (drule tcb_states_of_state_kheapD, elim exE conjE)
   apply (frule(2) tcb_caller_slot_empty_on_recieve ,simp)
   apply (cases ptr,simp)
   apply (simp add:caps_of_state_tcb)
  apply (elim tcb_states_of_state_kheapE)
  apply (drule(2) descendant_of_caller_slot[OF _ _ tcb_atI])
  by (force simp add: descendants_of_def simp del:split_paired_All)

lemma is_transferable_weak_derived:
  "weak_derived cap cap' \<Longrightarrow> is_transferable_cap cap = is_transferable_cap cap'"
  unfolding is_transferable.simps weak_derived_def copy_of_def same_object_as_def
  by (fastforce simp: is_cap_simps split: cap.splits)

lemma aag_cdt_link_Control:
  "\<lbrakk> cdt s x = Some y; \<not> is_transferable(caps_of_state s x); pas_refined aag s \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag Control (fst y) (fst x)"
  by (fastforce elim: pas_refined_mem[rotated] sta_cdt)

lemma aag_cdt_link_DeleteDerived:
  "\<lbrakk> cdt s x = Some y; pas_refined aag s \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag  DeleteDerived (fst y) (fst x)"
  by (fastforce elim: pas_refined_mem[rotated] sta_cdt_transferable)

lemma tcb_states_of_state_to_auth:
  "\<lbrakk> tcb_states_of_state s thread = Some tcbst; pas_refined aag s \<rbrakk>
     \<Longrightarrow> \<forall>(obj,auth) \<in> tcb_st_to_auth tcbst. abs_has_auth_to aag auth thread obj"
   apply clarsimp
   apply (erule pas_refined_mem[rotated])
   apply (rule sta_ts)
   apply (simp add:thread_st_auth_def)
   done

lemma tcb_states_of_state_to_auth':
  "\<lbrakk> tcb_states_of_state s thread = Some tcbst;
     pas_refined aag s; (obj,auth) \<in> tcb_st_to_auth tcbst \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag auth thread obj"
   using tcb_states_of_state_to_auth by blast

lemma ep_recv_blocked_def:
  "ep_recv_blocked ep st \<longleftrightarrow> (\<exists>pl. st = BlockedOnReceive ep pl)"
  by (simp split: thread_state.split)

lemma cdt_change_allowed_delete_derived:
  "\<lbrakk> valid_objs s; valid_mdb s; pas_refined aag s; cdt_change_allowed' aag slot s \<rbrakk>
     \<Longrightarrow> aag_has_auth_to aag DeleteDerived (fst slot)"
  apply (elim cdt_change_allowedE cdt_direct_change_allowed.cases)
   apply (erule rtrancl_induct)
    apply (solves\<open>simp add: pas_refined_refl\<close>)
   apply (fastforce simp: cdt_parent_of_def
                    dest: aag_cdt_link_DeleteDerived
                   intro: aag_wellformed_delete_derived_trans)
  apply (clarsimp simp: direct_call_def ep_recv_blocked_def)
  apply (frule(1)tcb_states_of_state_to_auth)
  apply (elim tcb_states_of_state_kheapE)
  apply (frule(2) descendant_of_caller_slot[OF _ _ tcb_atI])
  apply (frule(1) parent_of_rtrancl_no_descendant)
  apply clarsimp
  by (rule aag_wellformed_delete_derived'[OF _ _ pas_refined_wellformed])

end


lemma owns_thread_owns_cspace:
  "\<lbrakk> is_subject aag thread; pas_refined aag s; get_tcb False thread s = Some tcb;
     is_cnode_cap (tcb_ctable tcb); x \<in> obj_refs_ac (tcb_ctable tcb) \<rbrakk>
     \<Longrightarrow> is_subject aag x"
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp:ta_filter_def)
  apply (drule cte_wp_at_tcbI[where t="(thread, tcb_cnode_index 0)"
                                and P="\<lambda>cap. cap = tcb_ctable tcb", simplified])
  apply (auto simp: cte_wp_at_caps_of_state is_cap_simps cap_auth_conferred_def
              elim: caps_of_state_pasObjectAbs_eq[where p = "(thread, tcb_cnode_index 0)"])
  done

lemma is_subject_into_is_subject_asid:
  "\<lbrakk> cap_links_asid_slot aag (pasObjectAbs aag p) cap;
     is_subject aag p; pas_refined aag s; asid \<in> cap_asid' cap \<rbrakk>
     \<Longrightarrow> is_subject_asid aag asid"
  apply (clarsimp simp add: cap_links_asid_slot_def label_owns_asid_slot_def)
  apply (drule (1) bspec)
  apply (drule (1) pas_refined_Control)
  apply simp
  done

lemma clas_no_asid:
  "cap_asid' cap = {} \<Longrightarrow> cap_links_asid_slot aag l cap"
  unfolding cap_links_asid_slot_def by simp

lemma cli_no_irqs:
  "cap_irqs_controlled cap = {} \<Longrightarrow> cap_links_irq aag l cap"
  unfolding cap_links_irq_def by simp

lemma as_user_tcb_states[wp]:
  "as_user t f \<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace>"
  apply (simp add: as_user_def)
  apply (wpsimp wp: set_object_wp touch_object_wp')
  apply (clarsimp simp: thread_st_auth_def get_tcb_def tcb_states_of_state_def obind_def ta_filter_def
                 elim!: rsubst[where P=P, OF _ ext] split: option.split)
  done

lemma as_user_thread_state[wp]:
  "as_user t f \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (simp add: thread_st_auth_def)
  apply wp
  done

lemma as_user_thread_bound_ntfn[wp]:
  "as_user t f \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: as_user_def set_object_def split_def thread_bound_ntfns_def)
  apply (wp get_object_wp touch_object_wp')
  apply (clarsimp simp: thread_st_auth_def get_tcb_def ta_filter_def obind_def
                 elim!: rsubst[where P=P, OF _ ext] split: option.split)
  done

lemma tcb_domain_map_wellformed_lift:
  assumes 1: "\<And>P. f \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>"
  shows "f \<lbrace>tcb_domain_map_wellformed aag\<rbrace>"
  by (rule 1)


(* **************************************** *)

subsection\<open>Random lemmas that belong elsewhere.\<close>

(* FIXME: move *)
lemma bang_0_in_set:
  "xs \<noteq> [] \<Longrightarrow> xs ! 0 \<in> set xs"
  by (fastforce simp: in_set_conv_nth)

(* FIXME: move *)
lemma update_one_strg:
  "(b \<longrightarrow> P c v) \<and> (\<not> b \<longrightarrow> (\<forall>v'. f c' = Some v' \<longrightarrow> P c v'))
   \<longrightarrow> ((f(c := if b then Some v else f c')) x = Some y \<and> f x \<noteq> Some y \<longrightarrow> P x y)"
  by auto

(* FIXME: move *)
lemma hoare_gen_asm2:
  assumes a: "P \<Longrightarrow> \<lbrace>\<top>\<rbrace> f \<lbrace>Q\<rbrace>"
  shows "\<lbrace>K P\<rbrace> f \<lbrace>Q\<rbrace>"
  using a by (fastforce simp: valid_def)

(* FIXME: move *)
lemma hoare_vcg_all_liftE:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>, \<lbrace>Q' x\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>, \<lbrace>\<lambda>rv s. \<forall>x. Q' x rv s\<rbrace>"
  unfolding validE_def
  apply (rule hoare_post_imp [where Q = "\<lambda>v s. \<forall>x. case v of Inl e \<Rightarrow> Q' x e s | Inr r \<Rightarrow> Q x r s"])
   apply (clarsimp split: sum.splits)
  apply (erule hoare_vcg_all_lift)
  done

(* FIXME: move *)
lemma hoare_use_ex_R:
  "(\<And>x. \<lbrace>P x and Q \<rbrace> f \<lbrace>R\<rbrace>, -) \<Longrightarrow> \<lbrace>\<lambda>s. (\<exists>x. P x s) \<and> Q s \<rbrace> f \<lbrace>R\<rbrace>, -"
  unfolding validE_R_def validE_def valid_def by fastforce

(* FIXME: move *)
lemma mapM_x_and_const_wp:
  assumes f: "\<And>v. \<lbrace>P and K (Q v)\<rbrace> f v \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "\<lbrace>P and K (\<forall>v \<in> set vs. Q v)\<rbrace> mapM_x f vs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct vs)
   apply (simp add: mapM_x_Nil)
  apply (simp add: mapM_x_Cons)
  apply (wp f | assumption | simp)+
  done

(* stronger *)
(* FIXME: MOVE *)
lemma ep_queued_st_tcb_at':
  "\<And>P. \<lbrakk> ko_at (Endpoint ep) ptr s; (t, rt) \<in> ep_q_refs_of ep;
         valid_objs s; sym_refs (state_refs_of s);
         \<And>pl pl'. P (BlockedOnSend ptr pl) \<and> P (BlockedOnReceive ptr pl') \<rbrakk>
         \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac ep, simp_all)
  apply (frule(1) sym_refs_ko_atD, clarsimp, erule (1) my_BallE,
         clarsimp simp: st_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done

(* Sometimes we only care about one of the queues. *)
(* FIXME: move *)
lemma ep_rcv_queued_st_tcb_at:
  "\<And>P. \<lbrakk> ko_at (Endpoint ep) epptr s; (t, EPRecv) \<in> ep_q_refs_of ep;
         valid_objs s; sym_refs (state_refs_of s);
         \<And>pl. P (BlockedOnReceive epptr pl); kheap s' t = kheap s t\<rbrakk>
         \<Longrightarrow> st_tcb_at P t s'"
  apply (case_tac ep, simp_all)
  apply (subgoal_tac "st_tcb_at P t s")
   apply (simp add: st_tcb_at_def obj_at_def)
  apply (frule(1) sym_refs_ko_atD, clarsimp, erule (1) my_BallE,
         clarsimp simp: st_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done

(* FIXME: move. *)
lemma ntfn_queued_st_tcb_at':
  "\<And>P. \<lbrakk> ko_at (Notification ntfn) ntfnptr s; (t, rt) \<in> ntfn_q_refs_of (ntfn_obj ntfn);
         valid_objs s; sym_refs (state_refs_of s); P (BlockedOnNotification ntfnptr) \<rbrakk>
         \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac "ntfn_obj ntfn", simp_all)
  apply (frule(1) sym_refs_ko_atD)
  apply (clarsimp)
  apply (erule_tac y="(t, NTFNSignal)" in my_BallE, clarsimp)
  apply (clarsimp simp: pred_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done

(* FIXME: move *)
lemma case_prod_wp:
  "(\<And>a b. x = (a, b) \<Longrightarrow> \<lbrace>P a b\<rbrace> f a b \<lbrace>Q\<rbrace>)
   \<Longrightarrow> \<lbrace>P (fst x) (snd x)\<rbrace> case_prod f x \<lbrace>Q\<rbrace>"
  by (cases x, simp)

(* FIXME: move *)
lemma case_sum_wp:
  "\<lbrakk> (\<And>a. x = Inl a \<Longrightarrow> \<lbrace>P a\<rbrace> f a \<lbrace>Q\<rbrace>); (\<And>a. x = Inr a \<Longrightarrow> \<lbrace>P' a\<rbrace> g a \<lbrace>Q\<rbrace>) \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. (\<forall>a. x = Inl a \<longrightarrow> P a s) \<and> (\<forall>a. x = Inr a \<longrightarrow> P' a s)\<rbrace> case_sum f g x \<lbrace>Q\<rbrace>"
  by (cases x, simp_all)

lemma st_tcb_at_to_thread_st_auth:
  "st_tcb_at P t s \<Longrightarrow> \<exists>st. P st \<and> thread_st_auth s t = tcb_st_to_auth st"
  by (fastforce simp: st_tcb_def2 thread_st_auth_def tcb_states_of_state_def)

lemma aag_Control_into_owns:
  "\<lbrakk> aag_has_auth_to aag Control p; pas_refined aag s \<rbrakk> \<Longrightarrow> is_subject aag p"
  apply (drule (1) pas_refined_Control)
  apply simp
  done

lemma aag_has_Control_iff_owns:
  "pas_refined aag s \<Longrightarrow> (aag_has_auth_to aag Control x) = (is_subject aag x)"
  apply (rule iffI)
  apply (erule (1) aag_Control_into_owns)
  apply (simp add: pas_refined_refl)
  done

lemma aag_Control_owns_strg:
  "pas_wellformed aag \<and> is_subject aag v \<longrightarrow> aag_has_auth_to aag Control v"
  by (clarsimp simp: aag_wellformed_refl)

(* **************************************** *)

subsection \<open>Policy entailments\<close>

lemma owns_ep_owns_receivers:
  "\<lbrakk> \<forall>auth. aag_has_auth_to aag auth epptr; pas_refined aag s; invs s;
     ko_at (Endpoint ep) epptr s; (t, EPRecv) \<in> ep_q_refs_of ep \<rbrakk>
     \<Longrightarrow> is_subject aag t"
  apply (drule (1) ep_rcv_queued_st_tcb_at[where P = "receive_blocked_on epptr"])
      apply clarsimp
     apply clarsimp
    apply clarsimp
   apply (rule refl)
  apply (drule st_tcb_at_to_thread_st_auth)
  apply (clarsimp simp: receive_blocked_on_def2)
  apply (drule spec[where x = Grant])
  apply (frule aag_wellformed_grant_Control_to_recv[OF _ _ pas_refined_wellformed])
    apply (rule pas_refined_mem[OF sta_ts])
     apply (case_tac st; fastforce)
    apply assumption+
  apply (erule (1) aag_Control_into_owns)
  done

(* MOVE *)
lemma cli_caps_of_state:
  "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk>
     \<Longrightarrow> cap_links_irq aag (pasObjectAbs aag (fst slot)) cap"
  apply (clarsimp simp add: cap_links_irq_def pas_refined_def)
  apply (blast dest: state_irqs_to_policy_aux.intros)
  done


context Access_AC_2 begin

(* MOVE *)
lemma cap_auth_caps_of_state:
  "\<lbrakk> caps_of_state s p = Some cap; pas_refined aag s \<rbrakk>
     \<Longrightarrow> aag_cap_auth aag (pasObjectAbs aag (fst p)) cap"
  unfolding aag_cap_auth_def
  apply (intro conjI)
    apply clarsimp
    apply (drule (2) sta_caps)
    apply (drule_tac f="pasObjectAbs aag" in auth_graph_map_memI[OF _ refl refl])
    apply (fastforce simp: pas_refined_def)
   apply clarsimp
   apply (drule (2) sta_untyped [THEN pas_refined_mem] )
   apply simp
  apply (drule (1) clas_caps_of_state)
  apply simp
  apply (drule (1) cli_caps_of_state)
  apply simp
  done

lemma cap_cur_auth_caps_of_state:
  "\<lbrakk> caps_of_state s p = Some cap; pas_refined aag s; is_subject aag (fst p) \<rbrakk>
     \<Longrightarrow> pas_cap_cur_auth aag cap"
  by (metis cap_auth_caps_of_state)

end


subsection \<open>Integrity monotony over subjects\<close>


lemma tcb_bound_notification_reset_integrity_mono:
  "\<lbrakk> tcb_bound_notification_reset_integrity ntfn ntfn' S aag; S \<subseteq> T\<rbrakk>
     \<Longrightarrow> tcb_bound_notification_reset_integrity ntfn ntfn' T aag"
  unfolding tcb_bound_notification_reset_integrity_def by blast

lemma reply_cap_deletion_integrity_mono:
  "\<lbrakk> reply_cap_deletion_integrity S aag cap cap'; S \<subseteq> T \<rbrakk>
     \<Longrightarrow> reply_cap_deletion_integrity T aag cap cap'"
  by (blast intro: reply_cap_deletion_integrity_intros elim: reply_cap_deletion_integrityE)

lemma cnode_integrity_mono:
  "\<lbrakk> cnode_integrity S aag cont cont'; S \<subseteq> T\<rbrakk> \<Longrightarrow> cnode_integrity T aag cont cont'"
  by (blast intro!: cnode_integrityI elim: cnode_integrityE dest: reply_cap_deletion_integrity_mono)

lemmas new_range_subset' = aligned_range_offset_subset
lemmas ptr_range_subset = new_range_subset' [folded ptr_range_def]

lemma cdt_change_allowed_mono:
  "\<lbrakk> cdt_change_allowed aag S (cdt s) (tcb_states_of_state s) ptr; S \<subseteq> T \<rbrakk>
     \<Longrightarrow> cdt_change_allowed aag T (cdt s) (tcb_states_of_state s) ptr"
  unfolding cdt_change_allowed_def cdt_direct_change_allowed.simps direct_call_def by blast

lemmas rtranclp_monoE = rtranclp_mono[THEN predicate2D,rotated,OF _ predicate2I]


locale Access_AC_3 = Access_AC_2 +
  assumes arch_integrity_obj_atomic_mono:
    "\<lbrakk> arch_integrity_obj_atomic aag S l ao ao'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
       \<Longrightarrow> arch_integrity_obj_atomic aag T l ao ao'"
  and integrity_asids_mono:
    "\<And>x. \<lbrakk> integrity_asids aag S x a s s'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
            \<Longrightarrow> integrity_asids aag T x a s (s' :: det_ext state)"
  and auth_ipc_buffers_member:
    "\<And>x. \<lbrakk> x \<in> auth_ipc_buffers s p; valid_objs s \<rbrakk>
            \<Longrightarrow> \<exists>tcb acap. get_tcb False p s = Some tcb
                         \<and> tcb_ipcframe tcb = (ArchObjectCap acap)
                         \<and> caps_of_state s (p, tcb_cnode_index 4) = Some (ArchObjectCap acap)
                         \<and> Write \<in> arch_cap_auth_conferred acap
                         \<and> x \<in> aobj_ref' acap"
begin

lemma trm_ipc':
  "\<lbrakk> pas_refined aag s; valid_objs s; case_option False can_receive_ipc (tcb_states_of_state s p');
     (tcb_states_of_state s' p') = Some Structures_A.Running; p \<in> auth_ipc_buffers s p' \<rbrakk>
     \<Longrightarrow> integrity_mem aag subjects p (tcb_states_of_state s) (tcb_states_of_state s')
                      (auth_ipc_buffers s) X
                      (underlying_memory (machine_state s) p)
                      (underlying_memory (machine_state s') p)"
  apply (cases "pasObjectAbs aag p' \<in> subjects")
   apply (rule trm_write)
   apply (clarsimp simp: )
   apply (frule pas_refined_mem[rotated])
    prefer 3
    apply (rule trm_ipc; fastforce)
   prefer 2
   apply (rule bexI)
    apply assumption
   apply assumption
  apply (drule (1) auth_ipc_buffers_member)
  apply clarsimp
  apply (drule (1) sta_caps[where cap="ArchObjectCap acap" for acap, simplified])
   apply (auto simp: cap_auth_conferred_def)
  done

lemma integrity_mono:
  "\<lbrakk> integrity_subjects S aag activate X s s'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> integrity_subjects T aag activate X s s'"
  apply (clarsimp simp: integrity_subjects_def simp del: split_paired_All)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec)+
   apply (simp only: integrity_obj_def)
   apply (erule rtranclp_monoE)
   apply (erule integrity_obj_atomic.cases[OF _ integrity_obj_atomic.intros];
          auto simp: indirect_send_def direct_send_def direct_call_def direct_reply_def
               elim: reply_cap_deletion_integrity_mono cnode_integrity_mono
                     arch_integrity_obj_atomic_mono)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec)+
   apply (erule integrity_eobj.cases; auto intro: integrity_eobj.intros)
  apply (rule conjI)
   apply (intro allI)
   apply (drule_tac x=x in spec)+
   apply (erule integrity_cdtE; auto elim: cdt_change_allowed_mono)
  apply (rule conjI)
   apply (intro allI)
   apply (drule_tac x=x in spec)+
   apply (erule integrity_cdt_listE;
          auto elim!: weaken_filter_eq' intro: integrity_cdt_list_intros
               elim: cdt_change_allowed_mono)
  apply (rule conjI)
   apply (fastforce simp: integrity_interrupts_def)
  apply (rule conjI)
   apply (clarsimp simp: integrity_ready_queues_def)
   apply blast
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec, erule integrity_mem.cases;
          blast intro: integrity_mem.intros trm_ipc')
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec, erule integrity_device.cases;
          blast intro: integrity_device.intros)
  apply (fastforce elim: integrity_asids_mono)
  done


subsection\<open>Access control do not care about machine_state\<close>

lemma state_objs_to_policy_irq_state_independent[intro!, simp]:
  "state_objs_to_policy (s\<lparr>machine_state :=
                           machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>) =
   state_objs_to_policy s"
  by (simp add: state_objs_to_policy_def)

lemma tcb_domain_map_wellformed_independent[intro!, simp]:
  "tcb_domain_map_wellformed aag (s\<lparr>machine_state :=
                                    machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>) =
   tcb_domain_map_wellformed aag s"
  by (simp add: tcb_domain_map_wellformed_aux_def get_etcb_def)

subsection\<open>Transitivity of integrity lemmas and tactics\<close>

lemma integrity_trans_start:
  "(\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. integrity aag X s\<rbrace>)
   \<Longrightarrow> \<lbrace>integrity aag X st and P\<rbrace> f \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding spec_valid_def valid_def using integrity_trans by simp blast

method integrity_trans_start =
  ((simp only: and_assoc[symmetric])?, rule integrity_trans_start[rotated])

(* Q should be explicitly supplied, if not, use wp_integrity_clean' *)
lemma wp_integrity_clean:
  "\<lbrakk> \<And>s. Q s \<Longrightarrow> integrity aag X s (g s); \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. integrity aag X st and Q\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. integrity aag X st (g s)\<rbrace> "
   by (rule hoare_post_imp[of "\<lambda>_. integrity aag X st and Q"])
      (fastforce elim: integrity_trans)

lemmas wp_integrity_clean'= wp_integrity_clean[of \<top>, simplified]

end

end
