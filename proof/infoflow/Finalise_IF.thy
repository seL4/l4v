(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Finalise_IF
imports ArchArch_IF ArchIRQMasks_IF
begin

locale Finalise_IF_1 =
  fixes aag :: "'a subject_label PAS"
  assumes dmo_maskInterrupt_reads_respects:
    "reads_respects aag l \<top> (do_machine_op (maskInterrupt m irq))"
  and arch_post_cap_deletion_read_respects[wp]:
    "reads_respects aag l \<top> (arch_post_cap_deletion acap)"
  and equiv_asid_sa_update[simp]:
    "\<And>f. equiv_asid asid (scheduler_action_update f s) s' = equiv_asid asid s s'"
    "\<And>f. equiv_asid asid s (scheduler_action_update f s') = equiv_asid asid s s'"
  and equiv_asid_ready_queues_update[simp]:
    "\<And>f. equiv_asid asid (ready_queues_update f s) s' = equiv_asid asid s s'"
    "\<And>f. equiv_asid asid s (ready_queues_update f s') = equiv_asid asid s s'"
  and set_thread_state_reads_respects:
    "pas_domains_distinct aag
     \<Longrightarrow> reads_respects aag l (\<lambda>s. is_subject aag (cur_thread s)) (set_thread_state ref ts)"
  and set_bound_notification_globals_equiv:
    "\<lbrace>globals_equiv s and valid_arch_state\<rbrace> set_bound_notification ref nopt \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  and set_thread_state_runnable_reads_respects:
    "\<lbrakk> pas_domains_distinct aag; runnable ts \<rbrakk> \<Longrightarrow> reads_respects aag l \<top> (set_thread_state ref ts)"
  and set_bound_notification_none_reads_respects:
    "pas_domains_distinct aag \<Longrightarrow> reads_respects aag l \<top> (set_bound_notification ref None)"
  and thread_set_reads_respects:
    "pas_domains_distinct aag \<Longrightarrow> reads_respects aag l \<top> (thread_set x y)"
  and set_tcb_queue_reads_respects[wp]:
    "reads_respects aag l \<top> (set_tcb_queue d prio queue)"
  and set_notification_equiv_but_for_labels:
    "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag ntfnptr \<in> L)\<rbrace>
     set_notification ntfnptr ntfn
     \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  and prepare_thread_delete_reads_respects_f:
    "reads_respects_f aag l \<top> (prepare_thread_delete t)"
  and arch_finalise_cap_reads_respects:
    "reads_respects aag l (pas_refined aag and invs and cte_wp_at ((=) (ArchObjectCap cap)) slot
                                           and K (pas_cap_cur_auth aag (ArchObjectCap cap)))
                          (arch_finalise_cap cap is_final)"
  and arch_finalise_cap_makes_halted:
    "\<lbrace>invs and valid_cap (ArchObjectCap acap)
           and (\<lambda>s. ex = is_final_cap' (ArchObjectCap acap) s)
           and cte_wp_at ((=) (ArchObjectCap acap)) slot\<rbrace>
     arch_finalise_cap acap ex
     \<lbrace>\<lambda>rv s :: det_state. \<forall>t \<in> obj_refs_ac (fst rv). halted_if_tcb t s\<rbrace>"
  and set_notification_globals_equiv:
    "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
     set_notification ntfnptr ntfn
     \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  and arch_post_cap_deletion_globals_equiv[wp]:
    "arch_post_cap_deletion acap \<lbrace>globals_equiv st\<rbrace>"
  and set_irq_state_globals_equiv:
    "set_irq_state state irq \<lbrace>globals_equiv st\<rbrace>"
  and arch_finalise_cap_globals_equiv:
    "\<lbrace>globals_equiv st and invs and valid_arch_cap acap\<rbrace>
     arch_finalise_cap acap ex
     \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  and prepare_thread_delete_globals_equiv[wp]:
    "prepare_thread_delete t \<lbrace>globals_equiv st\<rbrace>"
begin

lemma set_irq_state_reads_respects:
  "reads_respects aag l \<top> (set_irq_state state irq)"
  unfolding set_irq_state_def fun_app_def
  apply (wp dmo_maskInterrupt_reads_respects)
    apply (subst equiv_valid_def2)
    apply (rule_tac P="\<top>" and P'="\<top>" in modify_ev2)
    apply (fastforce elim: affects_equivE reads_equivE equiv_forE intro: equiv_forI
                   intro!: reads_equiv_interrupt_states_update affects_equiv_interrupt_states_update)
   apply wpsimp+
  done

lemma deleted_irq_handler_reads_respects:
  "reads_respects aag l \<top> (deleted_irq_handler irq)"
  unfolding deleted_irq_handler_def
  by (rule set_irq_state_reads_respects)

lemma empty_slot_reads_respects:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "reads_respects aag l (K (aag_can_read aag (fst slot))) (empty_slot slot free_irq)"
  unfolding empty_slot_def post_cap_deletion_def fun_app_def
  apply (simp add: bind_assoc[symmetric] cong: if_cong)
  apply (fold update_cdt_def)
  apply (simp add: bind_assoc empty_slot_ext_def cong: if_cong)
  apply (rule gen_asm_ev)
  apply (wp deleted_irq_handler_reads_respects set_cap_reads_respects set_original_reads_respects
            update_cdt_list_reads_respects update_cdt_reads_respects get_cap_wp get_cap_rev
         | wpsimp
         | frule aag_can_read_self, fastforce simp: equiv_for_def split: option.splits)+
  by (fastforce simp: reads_equiv_def2 equiv_for_def
                elim: states_equiv_forE_cdt
                dest: aag_can_read_self
               split: option.splits)

lemma scheduler_action_states_equiv[simp]:
  "states_equiv_for P Q R S st (scheduler_action_update f s) = states_equiv_for P Q R S st s"
  by (simp add: states_equiv_for_def equiv_for_def equiv_asids_def)

crunch states_equiv[wp]: set_thread_state_ext "states_equiv_for P Q R S st"
  (ignore_del: set_thread_state_ext)

end


lemma requiv_get_tcb_eq':
  "\<lbrakk> reads_equiv aag s t; aag_can_read aag thread \<rbrakk>
     \<Longrightarrow> get_tcb thread s = get_tcb thread t"
  by (auto simp: reads_equiv_def2 get_tcb_def
           elim: states_equiv_forE_kheap
          dest!: aag_can_read_self)

lemma set_scheduler_action_reads_respects[wp]:
  "reads_respects aag l \<top> (set_scheduler_action action)"
  by (simp add: set_scheduler_action_def equiv_valid_def2 equiv_valid_2_def modify_def bind_def put_def
                get_def reads_equiv_scheduler_action_update affects_equiv_scheduler_action_update)

lemma set_thread_state_ext_reads_respects:
  "reads_respects aag l (\<lambda>s. is_subject aag (cur_thread s)) (set_thread_state_ext ref)"
  apply (case_tac "is_subject aag ref")
   apply (simp add: set_thread_state_ext_def when_def get_thread_state_def | wp thread_get_rev)+
   apply (simp add: reads_equiv_def)
  apply (simp add: set_thread_state_ext_def when_def)
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_rv_bind[where W="\<top>\<top>"])
    apply (clarsimp simp: equiv_valid_2_def get_thread_state_def thread_get_def gets_the_def
                          return_def bind_def assert_opt_def gets_def get_tcb_def fail_def get_def
                   split: option.splits)
   apply clarsimp
   apply (rule equiv_valid_2_bind[where R'="(=)" and Q="\<lambda>rv _. rv \<noteq> ref" and Q'="\<lambda>rv _. rv \<noteq> ref"])
      apply (rule gen_asm_ev2)
      apply (simp add: equiv_valid_def2[symmetric] | wp)+
      apply (clarsimp simp: reads_equiv_def)
     apply (subst equiv_valid_def2[symmetric])
     apply wp+
  apply force
  done

lemma set_thread_state_ext_owned_reads_respects:
  "reads_respects aag l (\<lambda>s. aag_can_read aag ref) (set_thread_state_ext ref)"
  apply (simp add: set_thread_state_ext_def when_def get_thread_state_def | wp thread_get_rev)+
  apply (simp add: reads_equiv_def)
  done

lemma set_thread_state_owned_reads_respects:
  "reads_respects aag l (\<lambda>s. aag_can_read aag ref) (set_thread_state ref ts)"
  apply (simp add: set_thread_state_def)
  apply (wp set_object_reads_respects gets_the_ev set_thread_state_ext_owned_reads_respects)
  by (fastforce intro: kheap_get_tcb_eq elim: reads_equivE equiv_forD)

lemma set_bound_notification_owned_reads_respects:
  "reads_respects aag l (\<lambda>s. is_subject aag ref) (set_bound_notification ref ntfn)"
  apply (simp add: set_bound_notification_def)
  apply (wp set_object_reads_respects gets_the_ev)
  apply (force elim: reads_equivE equiv_forE)
  done

lemma get_thread_state_runnable[wp]:
   "\<lbrace>st_tcb_at runnable ref\<rbrace> get_thread_state ref \<lbrace>\<lambda>rv _. runnable rv\<rbrace>"
  by (wpsimp wp: gts_st_tcb_at)

lemma set_thread_state_ext_runnable_reads_respects:
  "reads_respects aag l (st_tcb_at runnable ref) (set_thread_state_ext ref)"
  apply (simp add: set_thread_state_ext_def when_def)
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_rv_bind[where W="\<top>\<top>" and Q="\<lambda>rv _. runnable rv"])
    apply (clarsimp simp: equiv_valid_2_def get_thread_state_def thread_get_def gets_the_def
                          return_def bind_def assert_opt_def gets_def get_tcb_def fail_def get_def
                   split: option.splits)
   apply (rule gen_asm_ev2)
   apply (clarsimp simp: equiv_valid_def2[symmetric] | wp)+
   apply (simp add: reads_equiv_def)
  apply wp
  done

lemma set_simple_ko_reads_respects:
  "reads_respects aag l \<top> (set_simple_ko f ptr ep)"
  unfolding set_simple_ko_def
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp)
     apply (rule get_object_revrv)
    apply (simp, simp)
   apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
      apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
         apply (subst equiv_valid_def2[symmetric])
         apply (rule set_object_reads_respects)
        apply (rule assert_ev2)
        apply (simp)
       apply (rule assert_inv)+
     apply (rule assert_ev2)
     apply (simp)
    apply (rule assert_inv)+
  apply (simp)
  apply (wp get_object_inv)
  done

lemma get_ep_queue_reads_respects:
  "reads_respects aag l \<top> (get_ep_queue ep)"
  unfolding get_ep_queue_def
  apply (rule equiv_valid_guard_imp)
   apply (wp | wpc)+
  apply (simp)
  done

lemma get_object_reads_respects:
  "reads_respects aag l (K (aag_can_read aag ptr \<or> (aag_can_affect aag l ptr))) (get_object ptr)"
  apply (unfold get_object_def fun_app_def)
  apply (subst gets_apply)
  apply (wp gets_apply_ev | wp (once) hoare_drop_imps)+
  apply (fastforce elim: reads_equivE affects_equivE equiv_forE)
  done

lemma get_simple_ko_reads_respects:
  "reads_respects aag l (K (aag_can_read aag ptr \<or> aag_can_affect aag l ptr))
    (get_simple_ko f ptr)"
  unfolding get_simple_ko_def
  by (wp get_object_reads_respects | wpc | simp)+

lemma get_epq_SendEP_ret:
  "\<lbrace>\<lambda>s. \<forall>x\<in>set list. P x\<rbrace> get_ep_queue (SendEP list) \<lbrace>\<lambda>rv s. \<forall>x\<in>set rv. P x\<rbrace>"
  by (wpsimp simp: get_ep_queue_def)

lemma get_epq_RecvEP_ret:
  "\<lbrace>\<lambda>s. \<forall>x\<in>set list. P x\<rbrace> get_ep_queue (RecvEP list) \<lbrace>\<lambda>rv s. \<forall>x\<in>set rv. P x\<rbrace>"
  by (wpsimp simp: get_ep_queue_def)


fun ep_queue_invisible where
  "ep_queue_invisible aag l (SendEP list) = labels_are_invisible aag l ((pasObjectAbs aag) ` (set list))"
| "ep_queue_invisible aag l (RecvEP list) = labels_are_invisible aag l ((pasObjectAbs aag) ` (set list))"
| "ep_queue_invisible aag l IdleEP = True"


lemma obj_eq_st_tcb_at:
  "\<lbrakk> kheap s x = kheap s' x; st_tcb_at P x s' \<rbrakk>
    \<Longrightarrow> st_tcb_at P x s"
  by (clarsimp simp: st_tcb_at_def obj_at_def)

lemma send_blocked_on_tcb_st_to_auth:
  "send_blocked_on epptr ts \<Longrightarrow> (epptr, SyncSend) \<in> tcb_st_to_auth ts"
  by (case_tac ts, simp_all)

lemma receive_blocked_on_tcb_st_to_auth:
  "receive_blocked_on epptr ts \<Longrightarrow> (epptr, Receive) \<in> tcb_st_to_auth ts"
  by (case_tac ts, simp_all)

lemma not_ep_queue_invisible:
  "\<lbrakk> \<not> ep_queue_invisible aag l eplist; eplist = SendEP list \<or> eplist = RecvEP list \<rbrakk>
     \<Longrightarrow> \<exists>t \<in> set list. aag_can_read aag t \<or> aag_can_affect aag l t"
  by (auto simp: labels_are_invisible_def)

lemma ep_queued_st_tcb_at'':
  "\<And>P. \<lbrakk> ko_at (Endpoint ep) ptr s; (t, rt) \<in> ep_q_refs_of ep;
          valid_objs s; sym_refs (state_refs_of s);
          \<And>pl pl'. (rt = EPSend \<and> P (BlockedOnSend ptr pl)) \<or>
                    (rt = EPRecv \<and> P (BlockedOnReceive ptr pl')) \<rbrakk>
          \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac ep, simp_all)
  apply (frule (1) sym_refs_ko_atD, fastforce simp: st_tcb_at_def obj_at_def refs_of_rev)+
  done

lemma ep_queues_are_invisible_or_eps_are_equal':
  "\<lbrakk> (pasSubject aag, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag;
     ko_at (Endpoint ep) epptr s; ko_at (Endpoint ep') epptr s';
     reads_equiv aag s s'; affects_equiv aag l s s';
     valid_objs s; sym_refs (state_refs_of s); valid_objs s';
     sym_refs (state_refs_of s'); pas_refined aag s; pas_refined aag s' \<rbrakk>
     \<Longrightarrow> (\<not> ep_queue_invisible aag l ep) \<longrightarrow> ep = ep'"
  apply (rule impI)
  apply (case_tac "\<exists>list. ep = SendEP list \<or> ep = RecvEP list")
   apply (erule exE)
   apply (drule (1) not_ep_queue_invisible)
   apply clarsimp
   apply (erule disjE)
    apply (erule disjE)
     apply (drule_tac auth="SyncSend" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
         apply blast
        apply (erule pas_refined_mem[rotated])
        apply (rule sta_ts)
        apply (drule_tac P="send_blocked_on epptr" and s=s and t=t in ep_queued_st_tcb_at'')
            apply (simp)+
        apply (simp add: thread_st_auth_def split: option.splits)
        apply (clarsimp simp: tcb_states_of_state_def st_tcb_def2 send_blocked_on_tcb_st_to_auth)
       apply blast
      apply assumption
     apply (fastforce dest: reads_affects_equiv_kheap_eq simp: obj_at_def)
    apply (drule_tac auth="SyncSend" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
        apply blast
       apply (erule pas_refined_mem[rotated])
       apply (rule sta_ts)
       apply (drule_tac P="send_blocked_on epptr" and s=s and t=t in ep_queued_st_tcb_at'')
           apply (simp)+
       apply (simp add: thread_st_auth_def split: option.splits)
       apply (clarsimp simp: tcb_states_of_state_def st_tcb_def2 send_blocked_on_tcb_st_to_auth)
      apply blast
     apply (erule conjE, assumption)
    apply (drule_tac x=epptr in reads_affects_equiv_kheap_eq, simp+)
    apply (fastforce simp: obj_at_def)
   apply (erule disjE)
    apply (drule_tac auth="Receive" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
        apply blast
       apply (erule pas_refined_mem[rotated])
       apply (rule sta_ts)
       apply (drule_tac P="receive_blocked_on epptr" and s=s and t=t in ep_queued_st_tcb_at'')
           apply (simp)+
       apply (simp add: thread_st_auth_def split: option.splits)
       apply (clarsimp simp: tcb_states_of_state_def st_tcb_def2 receive_blocked_on_tcb_st_to_auth)
      apply blast
     apply assumption
    apply (fastforce dest: reads_affects_equiv_kheap_eq simp: obj_at_def)
   apply (drule_tac auth="Receive" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
       apply blast
      apply (erule pas_refined_mem[rotated])
      apply (rule sta_ts)
      apply (drule_tac P="receive_blocked_on epptr" and s=s and t=t in ep_queued_st_tcb_at'')
          apply (simp)+
      apply (simp add: thread_st_auth_def split: option.splits)
      apply (clarsimp simp: tcb_states_of_state_def st_tcb_def2 receive_blocked_on_tcb_st_to_auth)
     apply blast
    apply (erule conjE, assumption)
   apply (drule_tac x=epptr in reads_affects_equiv_kheap_eq, simp+)
   apply (fastforce simp: obj_at_def)
  apply (case_tac ep, auto)
  done

lemma ep_queues_are_invisible_or_eps_are_equal:
  "\<lbrakk> (pasSubject aag, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag;
     ko_at (Endpoint ep) epptr s; ko_at (Endpoint ep') epptr s';
     reads_equiv aag s s'; affects_equiv aag l s s';
     valid_objs s; sym_refs (state_refs_of s); valid_objs s';
     sym_refs (state_refs_of s'); pas_refined aag s; pas_refined aag s' \<rbrakk>
     \<Longrightarrow> (\<not> ep_queue_invisible aag l ep \<or> \<not> ep_queue_invisible aag l ep') \<longrightarrow> ep = ep'"
  apply (rule impI)
  apply (erule disjE)
   apply (blast intro!: ep_queues_are_invisible_or_eps_are_equal'[rule_format])
  apply (rule sym)
  apply (erule ep_queues_are_invisible_or_eps_are_equal'[rule_format])
  by (assumption | erule reads_equiv_sym | erule affects_equiv_sym)+

lemma get_simple_ko_revrv:
  "inj C \<Longrightarrow> reads_equiv_valid_rv_inv R aag (\<lambda>obj obj'. \<exists>s t. reads_equiv aag s t
                                                            \<and> R s t \<and> P s \<and> P t
                                                            \<and> ko_at (C obj) ptr s
                                                            \<and> ko_at (C obj') ptr t)
                                      P (get_simple_ko C ptr)"
  apply (simp add: get_simple_ko_def)
  apply (rule_tac Q="\<lambda> rv. ko_at rv ptr and P" in equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
     apply wpsimp+
   apply (clarsimp simp add: assert_def fail_ev2_l fail_ev2_r
                   simp del: imp_disjL split: option.split)
   apply (rule return_ev2)
   apply (auto simp: proj_inj)[1]
  apply (rule hoare_strengthen_post[OF get_object_sp])
  apply simp
  done

lemma get_endpoint_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
     (\<lambda>ep ep'. (\<not> ep_queue_invisible aag l ep \<or> \<not> ep_queue_invisible aag l ep') \<longrightarrow> ep = ep')
     (pas_refined aag and valid_objs and sym_refs \<circ> state_refs_of
                      and K ((pasSubject aag, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag))
     (get_endpoint epptr)"
  apply (rule equiv_valid_2_rvrel_imp, rule get_simple_ko_revrv)
   apply (simp add: inj_Endpoint)
  apply (auto elim: ep_queues_are_invisible_or_eps_are_equal[rule_format])
  done

lemma gen_asm_ev2_r:
  "(P' \<Longrightarrow> equiv_valid_2 I A B R P \<top> f f') \<Longrightarrow> equiv_valid_2 I A B R P (\<lambda>s. P') f f'"
  by (rule gen_asm_ev2_r')

lemma gen_asm_ev2_l:
  "(P \<Longrightarrow> equiv_valid_2 I A B R \<top> P' f f') \<Longrightarrow> equiv_valid_2 I A B R (\<lambda>s. P) P' f f'"
  by (rule gen_asm_ev2_l')

lemma bind_return_unit2:
  "f = return () >>= (\<lambda>_. f)"
  by simp

lemma mapM_x_ev2_invisible:
  assumes domains_distinct:
    "pas_domains_distinct aag"
  assumes mam:
    "\<And>ptr. modifies_at_most aag (L ptr) \<top> ((f :: obj_ref \<Rightarrow> (unit, det_ext) s_monad) ptr)"
  assumes mam':
    "\<And>ptr. modifies_at_most aag (L' ptr) \<top> ((f' :: obj_ref \<Rightarrow> (unit, det_ext) s_monad) ptr)"
  shows
    "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) (=)
                   (K (\<forall>x. x \<in> set list' \<longrightarrow> (labels_are_invisible aag l (L' x))))
                   (K (\<forall>x. x \<in> set list \<longrightarrow> (labels_are_invisible aag l (L x))))
                   (mapM_x f' list') (mapM_x f list)"
  apply (induct list)
   apply (induct_tac list')
    apply (simp add: mapM_x_Nil)
    apply (blast intro: return_ev2)
   apply (simp add: mapM_x_Cons mapM_x_Nil)
   apply (subst bind_return_unit[where f="return ()"])
   apply (rule_tac R'="(=)" and P="\<lambda>s. labels_are_invisible aag l (L' a)" in equiv_valid_2_bind_pre)
        apply simp
       apply (rule gen_asm_ev2_l)
       apply (rule equiv_valid_2_guard_imp[OF ev2_invisible[OF domains_distinct]], assumption+)
           apply (rule mam')
          apply (rule_tac P="\<top>" in modifies_at_mostI)
          apply (wp | simp)+
  apply (simp add: mapM_x_Cons)
  apply (subst bind_return_unit2)
  apply (rule_tac R'="(=)" and P'="\<lambda>s. labels_are_invisible aag l (L a)" in equiv_valid_2_bind_pre)
       apply simp
      apply (rule gen_asm_ev2_r)
      apply (rule equiv_valid_2_guard_imp[OF ev2_invisible[OF domains_distinct]], assumption+)
          apply (rule_tac P="\<top>" in modifies_at_mostI)
          apply (wp | simp)+
         apply (rule mam)
        apply (wp | simp)+
  done

lemma ev2_inv:
  assumes inv: "\<And>P. f \<lbrace>P\<rbrace>"
  assumes inv': "\<And>P. g \<lbrace>P\<rbrace>"
  shows "equiv_valid_2 I A A \<top>\<top> \<top> \<top> f g"
  apply (clarsimp simp: equiv_valid_2_def)
  apply (drule state_unchanged[OF inv])
  apply (drule state_unchanged[OF inv'])
  by simp

lemma mapM_x_ev2_r_invisible:
  assumes domains_distinct:
    "pas_domains_distinct aag"
  assumes mam:
    "\<And>ptr. modifies_at_most aag (L ptr) \<top> ((f :: obj_ref \<Rightarrow> (unit, det_ext) s_monad) ptr)"
  assumes inv:
    "\<And>P. g \<lbrace>P\<rbrace>"
  shows
    "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) (=) \<top>
                   (K (\<forall>x. x \<in> set list \<longrightarrow>  labels_are_invisible aag l (L x))) g (mapM_x f list)"
  apply (induct list)
   apply (simp add: mapM_x_Nil)
   apply (rule ev2_inv[OF inv])
   apply wp
  apply (simp add: mapM_x_Cons)
  apply (subst bind_return_unit2)
  apply (rule_tac R'="(=)" and P'="\<lambda> s. labels_are_invisible aag l (L a)" in equiv_valid_2_bind_pre)
       apply simp
      apply (rule gen_asm_ev2_r)
      apply (rule equiv_valid_2_guard_imp[OF ev2_invisible[OF domains_distinct]], assumption+)
          apply (rule_tac P="\<top>" in modifies_at_mostI)
          apply (wp | simp)+
         apply (rule mam)
        apply (wp | simp)+
  done

(* MOVE *)
lemma ev2_sym:
  assumes symI: "\<And>x y. I x y \<Longrightarrow> I y x"
  assumes symA: "\<And>x y. A x y \<Longrightarrow> A y x"
  assumes symB: "\<And>x y. B x y \<Longrightarrow> B y x"
  assumes symR: "\<And>x y. R x y \<Longrightarrow> R y x"
  shows "equiv_valid_2 I A B R P' P f' f \<Longrightarrow>
         equiv_valid_2 I A B R P P' f f'"
  apply (clarsimp simp: equiv_valid_2_def)
  apply (blast intro: symA symB symI symR)
  done

lemma mapM_x_ev2_l_invisible:
  assumes domains_distinct:
    "pas_domains_distinct aag"
  assumes mam:
    "\<And>ptr. modifies_at_most aag (L ptr) \<top> ((f :: obj_ref \<Rightarrow> (unit, det_ext) s_monad) ptr)"
  assumes inv:
    "\<And>P. g \<lbrace>P\<rbrace>"
  shows
    "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) (=)
                   (K (\<forall>x. x \<in> set list \<longrightarrow> labels_are_invisible aag l (L x))) \<top> (mapM_x f list) g"
  apply (rule ev2_sym[OF reads_equiv_sym affects_equiv_sym affects_equiv_sym])
      apply (simp_all)[4]
  apply (rule mapM_x_ev2_r_invisible[OF domains_distinct mam inv])
  done

lemma not_label_is_invisible:
  "(\<not> labels_are_invisible aag l {(pasObjectAbs aag x)}) =
   (aag_can_read aag x \<or> aag_can_affect aag l x)"
  by (simp add: labels_are_invisible_def)

lemma label_is_invisible:
  "(labels_are_invisible aag l {(pasObjectAbs aag x)}) =
   (\<not> (aag_can_read aag x \<or> aag_can_affect aag l x))"
  by (simp add: labels_are_invisible_def)

lemma op_eq_unit_taut: "(=) = (\<lambda> (_:: unit) _. True)"
  by (rule ext | simp)+

lemma ev2_symmetric:
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) (=) P P f f'
   \<Longrightarrow> equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) (=) P P f' f"
  apply (clarsimp simp add: equiv_valid_2_def)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=s in spec)
  apply (fastforce elim: affects_equiv_sym reads_equiv_sym)
  done

lemma reads_respects_ethread_get:
  "reads_respects aag l (\<lambda>_. is_subject aag thread) (ethread_get f thread)"
  apply (simp add: ethread_get_def)
  apply wp
  apply (drule aag_can_read_self)
  apply (fastforce simp: reads_equiv_def2 get_etcb_def equiv_for_def states_equiv_for_def)
  done

lemma aag_can_read_self'[simp]:
  "aag_can_read_label aag (pasSubject aag)"
  by fastforce

lemma gets_apply_ready_queues_reads_respects:
  "reads_respects aag l (\<lambda>_. pasSubject aag \<in> pasDomainAbs aag d) (gets_apply ready_queues d)"
  apply (rule gets_apply_ev')
  apply (force elim: reads_equivE simp: equiv_for_def)
  done

(* FIXME: move *)
lemma equiv_valid_rv_trivial':
  assumes inv: "\<And>P. f \<lbrace>P\<rbrace>"
  shows "equiv_valid_rv_inv I A \<top>\<top> Q f"
  by (auto simp: equiv_valid_2_def dest: state_unchanged[OF inv])

lemma gets_cur_domain_ev:
  "reads_equiv_valid_inv A aag \<top> (gets cur_domain)"
  apply (rule equiv_valid_guard_imp)
   apply wp
  apply (simp add: reads_equiv_def)
  done

crunch sched_act[wp]: set_simple_ko "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps)



context Finalise_IF_1 begin

lemma set_tcb_queue_modifies_at_most:
  "modifies_at_most aag L (\<lambda>s. pasDomainAbs aag d \<inter> L \<noteq> {}) (set_tcb_queue d prio queue)"
  apply (rule modifies_at_mostI)
  apply (simp add: set_tcb_queue_def modify_def, wp)
  apply (force simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def equiv_asids_def)
  done

lemma tcb_sched_action_reads_respects:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects aag l (pas_refined aag) (tcb_sched_action action t)"
  apply (simp add: tcb_sched_action_def get_tcb_queue_def)
  apply (subst gets_apply)
  apply (case_tac "aag_can_read aag t \<or> aag_can_affect aag l t")
   apply (simp add: ethread_get_def)
   apply wp
         apply (rule_tac Q="\<lambda>s. pasObjectAbs aag t \<in> pasDomainAbs aag (tcb_domain rv)"
                      in equiv_valid_guard_imp)
          apply (wp gets_apply_ev')
          apply (fastforce simp: reads_equiv_def affects_equiv_def equiv_for_def states_equiv_for_def)
         apply (wp | simp)+
   apply (intro conjI impI allI
          | fastforce simp: get_etcb_def elim: reads_equivE affects_equivE equiv_forE)+
   apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def split: option.splits)
   apply (erule_tac x="(t, tcb_domain y)" in ballE, force)
   apply (force intro: domtcbs simp: get_etcb_def)
  apply (simp add: equiv_valid_def2 ethread_get_def)
  apply (rule equiv_valid_rv_bind)
    apply (wp equiv_valid_rv_trivial', simp)
   apply (rule equiv_valid_2_bind)
      prefer 2
      apply (wp equiv_valid_rv_trivial, simp)
     apply (rule equiv_valid_2_bind)
        apply (rule_tac P=\<top> and P'=\<top> and L="{pasObjectAbs aag t}" and L'="{pasObjectAbs aag t}"
                     in ev2_invisible[OF domains_distinct])
            apply (blast | simp add: labels_are_invisible_def)+
          apply (rule set_tcb_queue_modifies_at_most)
         apply (rule set_tcb_queue_modifies_at_most)
        apply (simp | wp)+
       apply (clarsimp simp: equiv_valid_2_def gets_apply_def get_def
                             bind_def return_def labels_are_invisible_def)
      apply wpsimp+
  apply (force intro: domtcbs simp: get_etcb_def pas_refined_def tcb_domain_map_wellformed_aux_def)
  done

lemma reschedule_required_reads_respects[wp]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (pas_refined aag) reschedule_required"
  apply (simp add: reschedule_required_def | wp tcb_sched_action_reads_respects | wpc)+
  apply (simp add: reads_equiv_def)
  done

lemma possible_switch_to_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (pas_refined aag and pas_cur_domain aag
                                               and (\<lambda>s. is_subject aag (cur_thread s)))
                              (possible_switch_to tptr)"
  apply (simp add: possible_switch_to_def ethread_get_def)
  apply (case_tac "aag_can_read aag tptr \<or> aag_can_affect aag l tptr")
   apply (wp static_imp_wp tcb_sched_action_reads_respects | wpc | simp)+
   apply (clarsimp simp: get_etcb_def)
   apply ((intro conjI impI allI
          | elim aag_can_read_self reads_equivE affects_equivE equiv_forE conjE disjE
          | force)+)[1]
  apply clarsimp
  apply (wp (once), rename_tac cur_dom)
     apply (simp add: equiv_valid_def2)
     apply (rule_tac W="\<top>\<top>" and Q="\<lambda>tcb. pas_refined aag and K (tcb_domain tcb \<noteq> cur_dom)"
                  in equiv_valid_rv_bind)
       prefer 3
       apply wp
      apply (monad_eq simp: get_etcb_def equiv_valid_2_def)
     apply (rule gen_asm_ev2')
     apply (simp add: equiv_valid_def2[symmetric])
     apply (wp tcb_sched_action_reads_respects)
     apply (simp add: reads_equiv_def)
    apply (wp gets_cur_domain_ev)+
  apply (clarsimp simp: get_etcb_def pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (frule_tac x="(tptr, tcb_domain y)" in bspec, force intro: domtcbs)
  apply (erule notE)
  apply (fastforce dest: domains_distinct[THEN pas_domains_distinct_inj])
  done

lemma cancel_all_ipc_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs
                                               and valid_arch_state and K (aag_can_read aag epptr))
                        (cancel_all_ipc epptr)"
  unfolding cancel_all_ipc_def fun_app_def
  by (wp mapM_x_ev'' tcb_sched_action_reads_respects set_thread_state_runnable_reads_respects
         set_thread_state_pas_refined hoare_vcg_ball_lift
         set_thread_state_runnable_valid_sched_action
         set_simple_ko_reads_respects get_ep_queue_reads_respects get_epq_SendEP_ret
         get_epq_RecvEP_ret get_simple_ko_reads_respects get_simple_ko_wp
      | wpc
      | clarsimp simp: ball_conj_distrib
      | rule subset_refl
      | wp (once) hoare_drop_imps
      | assumption
      | rule hoare_strengthen_post[where Q="\<lambda>_. pas_refined aag and pspace_aligned
                                                                and valid_vspace_objs
                                                                and valid_arch_state", OF mapM_x_wp])+

end


fun ntfn_queue_invisible where
  "ntfn_queue_invisible aag l (WaitingNtfn list) = labels_are_invisible aag l ((pasObjectAbs aag) ` (set list))"
| "ntfn_queue_invisible aag l _ = True"


lemma not_ntfn_queue_invisible:
  "\<lbrakk> \<not> ntfn_queue_invisible aag l eplist; eplist = WaitingNtfn list \<rbrakk>
     \<Longrightarrow> (\<exists>t \<in> set list. aag_can_read aag t \<or> aag_can_affect aag l t)"
  by (auto simp: labels_are_invisible_def)

lemma ntfn_queues_are_invisible_or_ntfns_are_equal':
  "\<lbrakk> (pasSubject aag, Reset, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag;
     ko_at (Notification ntfn) ntfnptr s; ko_at (Notification ntfn') ntfnptr s';
     reads_equiv aag s s'; affects_equiv aag l s s';
     valid_objs s; sym_refs (state_refs_of s); valid_objs s';
     sym_refs (state_refs_of s'); pas_refined aag s; pas_refined aag s' \<rbrakk>
     \<Longrightarrow> \<not> ntfn_queue_invisible aag l (ntfn_obj ntfn) \<longrightarrow> ntfn_obj ntfn = ntfn_obj ntfn'"
  apply (rule impI)
  apply (case_tac "\<exists>list. ntfn_obj ntfn = WaitingNtfn list")
   apply (erule exE)
   apply (drule (1) not_ntfn_queue_invisible)
   apply clarsimp
   apply (erule disjE)
    apply (drule_tac auth="Receive" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
        apply blast
       apply (erule pas_refined_mem[rotated])
       apply (rule sta_ts)
       apply (drule_tac P="receive_blocked_on ntfnptr" and s=s and t=t in ntfn_queued_st_tcb_at')
           apply (simp)+
       apply (simp add: thread_st_auth_def split: option.splits)
       apply (clarsimp simp: tcb_states_of_state_def st_tcb_def2 receive_blocked_on_tcb_st_to_auth)
      apply blast
     apply assumption
    apply (fastforce dest: reads_affects_equiv_kheap_eq simp: obj_at_def)
   apply (drule_tac auth="Receive" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
       apply blast
      apply (erule pas_refined_mem[rotated])
      apply (rule sta_ts)
      apply (drule_tac P="receive_blocked_on ntfnptr" and s=s and t=t in ntfn_queued_st_tcb_at')
          apply (simp)+
      apply (simp add: thread_st_auth_def split: option.splits)
      apply (clarsimp simp: tcb_states_of_state_def st_tcb_def2 receive_blocked_on_tcb_st_to_auth)
     apply blast
    apply (erule conjE, assumption)
   apply (drule_tac x=ntfnptr in reads_affects_equiv_kheap_eq, simp+)
   apply (fastforce simp: obj_at_def)
  apply (case_tac "ntfn_obj ntfn", auto)
  done

lemma get_bound_notification_reads_respects':
  "reads_respects aag l (K(is_subject aag thread)) (get_bound_notification thread)"
  unfolding get_bound_notification_def thread_get_def
  apply (wp | simp)+
  apply clarify
  apply (rule requiv_get_tcb_eq)
   apply simp+
  done

lemma thread_get_reads_respects:
  "reads_respects aag l (K (aag_can_read aag thread \<or> aag_can_affect aag l thread))
                  (thread_get f thread)"
  unfolding thread_get_def fun_app_def
  apply (wp gets_the_ev)
  apply (auto intro: reads_affects_equiv_get_tcb_eq)
  done

lemma get_bound_notification_reads_respects:
  "reads_respects aag l (\<lambda> s. aag_can_read aag thread \<or> aag_can_affect aag l thread)
                  (get_bound_notification thread)"
  unfolding get_bound_notification_def
  apply (rule equiv_valid_guard_imp)
   apply (wp thread_get_reads_respects | simp)+
  done

lemma bound_tcb_at_implies_read:
  "\<lbrakk> pas_refined aag s; is_subject aag t; bound_tcb_at ((=) (Some x)) t s \<rbrakk>
     \<Longrightarrow> aag_can_read_label aag (pasObjectAbs aag x)"
  apply (frule bound_tcb_at_implies_receive, simp)
  apply clarsimp
  apply (frule_tac l="pasSubject aag" and auth=Receive in reads_ep, simp)
  apply (auto simp: aag_can_read_read)
  done

lemma bound_tcb_at_eq:
  "\<lbrakk> sym_refs (state_refs_of s); valid_objs s; kheap s ntfnptr = Some (Notification ntfn);
     ntfn_bound_tcb ntfn = Some tcbptr; bound_tcb_at ((=) (Some ntfnptr')) tcbptr s \<rbrakk>
     \<Longrightarrow> ntfnptr = ntfnptr'"
  apply (drule_tac x=ntfnptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def)
  apply (auto simp: pred_tcb_at_def obj_at_def valid_obj_def valid_ntfn_def
                    is_tcb state_refs_of_def refs_of_rev
          simp del: refs_of_simps)
  done

lemma unbind_notification_is_subj_reads_respects:
  "reads_respects aag l (pas_refined aag and invs and K (is_subject aag t))
                  (unbind_notification t)"
  apply (clarsimp simp: unbind_notification_def)
  apply (wp set_bound_notification_owned_reads_respects set_simple_ko_reads_respects
            get_simple_ko_reads_respects get_bound_notification_reads_respects
            gbn_wp[unfolded get_bound_notification_def, simplified]
         | wpc
         | simp add: get_bound_notification_def)+
  apply (clarsimp)
  apply (rule bound_tcb_at_implies_read, auto)
  done


context Finalise_IF_1 begin

lemma cancel_all_signals_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects aag l (pas_refined aag and pspace_aligned and valid_vspace_objs
                                           and valid_arch_state and K (aag_can_read aag ntfnptr))
                   (cancel_all_signals ntfnptr)"
  unfolding cancel_all_signals_def
  by (wp mapM_x_ev'' tcb_sched_action_reads_respects set_thread_state_runnable_reads_respects
         set_thread_state_pas_refined hoare_vcg_ball_lift
         set_thread_state_runnable_valid_sched_action
         set_simple_ko_reads_respects get_epq_SendEP_ret get_epq_RecvEP_ret
         get_simple_ko_reads_respects get_simple_ko_wp
      | wpc
      | clarsimp simp: ball_conj_distrib
      | rule subset_refl
      | wp (once) hoare_drop_imps
      | simp
      | rule hoare_strengthen_post[where Q="\<lambda>_. pas_refined aag and pspace_aligned
                                                                and valid_vspace_objs
                                                                and valid_arch_state", OF mapM_x_wp])+

lemma unbind_maybe_notification_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects aag l (pas_refined aag and invs and K (aag_can_read aag ntfnptr))
                  (unbind_maybe_notification ntfnptr)"
  unfolding unbind_maybe_notification_def
  by (wp set_bound_notification_none_reads_respects
         set_simple_ko_reads_respects get_simple_ko_reads_respects
      | wpc | simp)+

(* aag_can_read is transitive on endpoints but intransitive on notifications *)
lemma fast_finalise_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects aag l (pas_refined aag and invs and
                           K (fin \<longrightarrow> (case cap of EndpointCap r badge rights \<Rightarrow> aag_can_read aag r
                                             | NotificationCap r badge rights \<Rightarrow> is_subject aag r
                                             | _ \<Rightarrow> True)))
                    (fast_finalise cap fin)"
  apply (case_tac cap, simp_all)
  by (wp equiv_valid_guard_imp[OF cancel_all_ipc_reads_respects]
         equiv_valid_guard_imp[OF cancel_all_signals_reads_respects]
         unbind_notification_is_subj_reads_respects
         unbind_maybe_notification_reads_respects
         get_simple_ko_reads_respects get_simple_ko_wp
      | simp add: when_def
      | wpc
      | intro conjI impI
      | fastforce simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)+

lemma cap_delete_one_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_f aag l (silc_inv aag st and invs and pas_refined aag
                                                 and K (is_subject aag (fst slot)))
                          (cap_delete_one slot)"
  unfolding cap_delete_one_def fun_app_def
  apply (unfold unless_def when_def)
  apply (rule equiv_valid_guard_imp)
   apply (wp is_final_cap_reads_respects
            reads_respects_f[OF empty_slot_reads_respects, where st=st]
            reads_respects_f[OF fast_finalise_reads_respects, where st=st]
            empty_slot_silc_inv
        | simp | elim conjE)+
      apply (rule_tac Q="\<lambda>rva s. rva = is_final_cap' rv s \<and>
                                 cte_wp_at ((=) rv) slot s \<and>
                                 silc_inv aag st s \<and>
                                 is_subject aag (fst slot) \<and>
                                 pasObjectAbs aag (fst slot) \<noteq> SilcLabel"
                   in hoare_strengthen_post)
       apply wp
      apply (rule conjI)
       apply clarsimp
       apply (drule silc_inv)
       apply (erule_tac x=rv in allE, erule_tac x=slot in allE)
       apply simp
       apply (drule(1) intra_label_capD)
       apply (clarsimp simp: cap_points_to_label_def split: cap.splits)
      apply force
     apply (wp reads_respects_f[OF get_cap_rev] get_cap_auth_wp | simp | elim conjE)+
  by (fastforce simp: cte_wp_at_caps_of_state silc_inv_def)

lemma cap_delete_one_reads_respects_f_transferable:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_f aag l
     (silc_inv aag st and invs and pas_refined aag
                      and K (aag_can_read_not_silc aag (fst slot)) and is_transferable_in slot)
     (cap_delete_one slot)"
  unfolding cap_delete_one_def fun_app_def
  apply (unfold unless_def when_def)
  apply (rule equiv_valid_guard_imp)
   apply (wp is_final_cap_reads_respects empty_slot_silc_inv
             reads_respects_f[OF empty_slot_reads_respects, where st=st]
             reads_respects_f[OF fast_finalise_reads_respects, where st=st]
          | simp | elim conjE)+
      apply (rule_tac Q="\<lambda>rva s. rva = is_final_cap' rv s \<and>
                                 cte_wp_at ((=) rv) slot s \<and>
                                 silc_inv aag st s \<and>
                                 is_transferable_in slot s \<and>
                                 aag_can_read_not_silc aag (fst slot)"
                   in hoare_strengthen_post)
       apply wp
      apply (rule conjI)
       apply clarsimp
       apply (drule silc_inv)
       apply (erule_tac x=rv in allE, erule_tac x=slot in allE)
       apply simp
       apply (drule(1) intra_label_capD)
       apply (clarsimp simp: cap_points_to_label_def' cte_wp_at_caps_of_state split: cap.splits)
      apply (force elim: is_transferable_capE)
     apply (wp reads_respects_f[OF get_cap_rev] get_cap_wp | simp | elim conjE)+
  by (fastforce simp: cte_wp_at_caps_of_state silc_inv_def)

end


lemma get_blocking_object_reads_respects:
  "reads_respects aag l \<top> (get_blocking_object state)"
  unfolding get_blocking_object_def
  apply (rule equiv_valid_guard_imp)
   apply (wp | wpc | simp)+
  done


fun tcb_st_to_auth' where
  "tcb_st_to_auth' (BlockedOnSend x pl) = SyncSend"
| "tcb_st_to_auth' (BlockedOnReceive x pl) = Receive"
| "tcb_st_to_auth' (BlockedOnNotification x) = Receive"


lemma owns_thread_blocked_reads_endpoint:
  "\<lbrakk> pas_refined aag s; invs s; st_tcb_at (\<lambda> y. y = state) tptr s; is_subject aag tptr;
     state = BlockedOnReceive x pl \<or> state = BlockedOnSend x xb \<or> state = BlockedOnNotification x \<rbrakk>
     \<Longrightarrow> aag_can_read aag x"
  apply (rule_tac auth="tcb_st_to_auth' state" in reads_ep)
   apply (drule sym, simp, rule pas_refined_mem)
    apply (rule_tac s=s in sta_ts)
    apply (clarsimp simp: thread_st_auth_def tcb_states_of_state_def
                          st_tcb_at_def get_tcb_def obj_at_def)
    apply fastforce
   apply assumption
  apply fastforce
  done

lemma st_tcb_at_sym:
  "st_tcb_at ((=) x) t s = st_tcb_at (\<lambda> y. y = x) t s"
  by (auto simp: st_tcb_at_def obj_at_def)

lemma blocked_cancel_ipc_reads_respects:
  "reads_respects aag l (pas_refined aag and invs and st_tcb_at ((=) state) tptr
                                                  and K (is_subject aag tptr))
                  (blocked_cancel_ipc state tptr)"
  unfolding blocked_cancel_ipc_def
  apply (wp set_thread_state_owned_reads_respects set_simple_ko_reads_respects
            get_ep_queue_reads_respects get_simple_ko_reads_respects get_blocking_object_reads_respects
         | simp add: get_blocking_object_def | wpc)+
  apply (fastforce intro: aag_can_read_self owns_thread_blocked_reads_endpoint simp: st_tcb_at_sym)
  done

lemma select_singleton_ev:
  "equiv_valid_inv I B (K (\<exists>a. A = {a})) (select A)"
  by (fastforce simp: equiv_valid_def2 equiv_valid_2_def select_def)

lemma thread_set_fault_pas_refined':
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state\<rbrace>
   thread_set (tcb_fault_update fault) thread
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  by (wp thread_set_pas_refined | simp)+

(* FIXME MERGE names *)
lemmas thread_set_fault_empty_invs = thread_set_tcb_fault_reset_invs

lemma get_thread_state_rev:
  "reads_equiv_valid_inv A aag (K (aag_can_read aag ref)) (get_thread_state ref)"
  unfolding get_thread_state_def
  by (rule thread_get_rev)

lemma get_irq_slot_reads_respects:
  "reads_respects aag l (K (is_subject_irq aag irq)) (get_irq_slot irq)"
  unfolding get_irq_slot_def
  apply (rule equiv_valid_guard_imp)
   apply (rule gets_ev)
  apply (simp add: reads_equiv_def states_equiv_for_def equiv_for_def affects_equiv_def)
  apply (drule aag_can_read_irq_self)
  apply (simp)
  done

lemma thread_set_tcb_at:
  "\<lbrace>\<lambda>s. Q s\<rbrace> thread_set x ptr \<lbrace>\<lambda>_ s. P s\<rbrace>
   \<Longrightarrow> \<lbrace>\<lambda>s. tcb_at ptr s \<longrightarrow> Q s\<rbrace> thread_set x ptr \<lbrace>\<lambda>_ s. P s\<rbrace>"
  apply (rule use_spec(1))
  apply (case_tac "tcb_at ptr s")
   apply (clarsimp simp add: spec_valid_def valid_def)
  apply (simp add: spec_valid_def thread_set_def set_object_def[abs_def])
  apply (wp get_object_wp)
  apply (force simp: get_tcb_def obj_at_def is_tcb_def
              split: option.splits Structures_A.kernel_object.splits)
  done

(* FIXME: Why was the [wp] attribute on this lemma clobbered by interpretation of the Arch locale? *)
lemmas [wp] = thread_set_fault_valid_global_refs

lemma cancel_signal_owned_reads_respects:
  "reads_respects aag l
     (K (is_subject aag threadptr \<and> (aag_can_read aag ntfnptr \<or> aag_can_affect aag l ntfnptr)))
     (cancel_signal threadptr ntfnptr)"
  unfolding cancel_signal_def
  by (wp set_thread_state_owned_reads_respects set_simple_ko_reads_respects
         get_simple_ko_reads_respects hoare_drop_imps
      | wpc | simp)+

lemma as_user_get_register_reads_respects:
  "reads_respects aag l (K (is_subject aag thread)) (as_user thread (getRegister reg))"
  by (fastforce simp: equiv_valid_guard_imp[OF as_user_reads_respects] det_getRegister)

lemma update_restart_pc_reads_respects[wp]:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects aag l (silc_inv aag s and K (is_subject aag thread))
                        (update_restart_pc thread)"
  unfolding update_restart_pc_def
  apply (subst as_user_bind)
  apply (wpsimp wp: as_user_set_register_reads_respects' as_user_get_register_reads_respects)
  done


context Finalise_IF_1 begin

lemma reply_cancel_ipc_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_f aag l (silc_inv aag st and pas_refined aag and invs
                                                 and tcb_at tptr and K (is_subject aag tptr))
                          (reply_cancel_ipc tptr)"
  unfolding reply_cancel_ipc_def
  apply (rule gen_asm_ev)
  apply (wp cap_delete_one_reads_respects_f_transferable[where st=st]
            select_singleton_ev select_inv select_wp assert_wp
            reads_respects_f[OF get_cap_rev, where st=st]
            reads_respects_f[OF thread_set_reads_respects, where st=st]
            reads_respects_f[OF gets_descendants_of_revrv[folded equiv_valid_def2]]
         | simp add: when_def split del: if_split | elim conjE)+
   apply (rule_tac Q="\<lambda> rv s. silc_inv aag st s \<and> invs s \<and> pas_refined aag s
                                                \<and> tcb_at tptr s \<and> is_subject aag tptr"
                in hoare_strengthen_post)
    apply (wp thread_set_tcb_fault_update_silc_inv hoare_vcg_imp_lift hoare_vcg_ball_lift
              thread_set_fault_empty_invs thread_set_fault_pas_refined'
           | wps | simp)+
   apply clarsimp apply (rule conjI,rule TrueI)
   apply clarsimp
   apply (frule(1) reply_cap_descends_from_master0)
   apply (frule all_children_subjectReads[THEN all_children_descendants_of],force,force)
   apply (fastforce simp: cte_wp_at_caps_of_state
                    elim: silc_inv_no_transferable'[where slot = "(a,b)" for a b,simplified])
  by fastforce

lemma cancel_ipc_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_f aag l (silc_inv aag st and pas_refined aag and invs and tcb_at t and
                          (K (is_subject aag t))) (cancel_ipc t)"
  unfolding cancel_ipc_def
  apply (wp reads_respects_f[OF blocked_cancel_ipc_reads_respects, where st=st and Q="\<top>"]
            reply_cancel_ipc_reads_respects_f[where st=st]
            reads_respects_f[OF cancel_signal_owned_reads_respects, where st=st and Q="\<top>"]
            reads_respects_f[OF get_thread_state_rev, where st=st and Q="\<top>"] gts_wp
         | wpc | simp add: blocked_cancel_ipc_def | erule conjE)+
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  apply (rule owns_thread_blocked_reads_endpoint)
      apply (simp add: st_tcb_at_def obj_at_def | blast)+
  done

lemma suspend_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_f aag l (silc_inv aag st and pas_refined aag and invs and tcb_at thread
                                                 and K (is_subject aag thread))
                          (suspend thread)"
  unfolding suspend_def
  apply (wp reads_respects_f[OF set_thread_state_owned_reads_respects, where st=st and Q="\<top>"]
            reads_respects_f[OF tcb_sched_action_reads_respects, where st=st and Q=\<top>]
            reads_respects_f[OF get_thread_state_rev, where st=st and Q="\<top>"]
            reads_respects_f[OF update_restart_pc_reads_respects, where st=st and Q="\<top>"]
            gts_wp set_thread_state_pas_refined | simp)+
    apply (wp cancel_ipc_reads_respects_f[where st=st] cancel_ipc_silc_inv)+
   apply clarsimp
   apply (wp hoare_allI hoare_drop_imps)
    apply clarsimp
    apply (wp cancel_ipc_silc_inv)+
  apply auto
  done

lemma deleting_irq_handler_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows "reads_respects_f aag l (silc_inv aag st and invs and pas_refined aag
                                                 and K (is_subject_irq aag irq))
                          (deleting_irq_handler irq)"
  unfolding deleting_irq_handler_def
  by (wp cap_delete_one_reads_respects_f reads_respects_f[OF get_irq_slot_reads_respects]
      | simp | blast)+

lemma finalise_cap_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
    "reads_respects_f aag l
       (silc_inv aag st and pas_refined aag and invs and cte_wp_at ((=) cap) slot
                        and K (pas_cap_cur_auth aag cap)
                        and K (final \<longrightarrow> (case cap of EndpointCap r badge rights \<Rightarrow> is_subject aag r
                                                | NotificationCap r badge rights \<Rightarrow> is_subject aag r
                                                | _ \<Rightarrow> True)))
       (finalise_cap cap final)"
  apply (case_tac cap, simp_all split del: if_split)
             apply ((wp cancel_all_ipc_reads_respects cancel_all_signals_reads_respects
                        prepare_thread_delete_reads_respects_f
                        suspend_reads_respects_f[where st=st] deleting_irq_handler_reads_respects
                        unbind_notification_is_subj_reads_respects
                        unbind_maybe_notification_reads_respects
                        unbind_notification_invs unbind_maybe_notification_invs
                     | simp add: when_def invs_valid_objs invs_sym_refs aag_cap_auth_def
                                 cap_auth_conferred_def cap_rights_to_auth_def cap_links_irq_def
                                 aag_has_Control_iff_owns cte_wp_at_caps_of_state
                            split del: if_split
                     | rule aag_Control_into_owns_irq
                     | clarsimp split del: if_split
                     | rule conjI
                     | wp (once) reads_respects_f[where st=st]
                     | blast
                     | clarsimp
                     | force dest: caps_of_state_valid simp: valid_cap_def)+)[11]
  apply (rule equiv_valid_guard_imp)
  by (wp arch_finalise_cap_reads_respects reads_respects_f[where st=st] arch_finalise_cap_silc_inv
      | simp | elim conjE)+

end


lemma cap_swap_for_delete_reads_respects:
  "reads_respects aag l (K (is_subject aag (fst slot1) \<and> is_subject aag (fst slot2)))
                 (cap_swap_for_delete slot1 slot2)"
  unfolding cap_swap_for_delete_def
  apply (simp add: when_def)
  apply (rule conjI, rule impI)
   apply (rule equiv_valid_guard_imp)
    apply (wp cap_swap_reads_respects get_cap_rev)
   apply (simp)
  apply (rule impI, wp)
  done

lemma owns_cnode_owns_obj_ref_of_child_cnodes_threads_and_zombies:
  "\<lbrakk> pas_refined aag s; is_subject aag (fst slot); cte_wp_at ((=) cap) slot s;
     is_cnode_cap cap \<or> is_thread_cap cap \<or> is_zombie cap \<rbrakk>
     \<Longrightarrow> is_subject aag (obj_ref_of cap)"
  apply (frule (1) cap_cur_auth_caps_of_state[rotated])
   apply (simp add: cte_wp_at_caps_of_state)
  apply (clarsimp simp: aag_cap_auth_def)
  apply (case_tac cap, simp_all add: is_zombie_def)
    apply (drule_tac x=Control in bspec)
     apply (clarsimp simp: cap_auth_conferred_def)
    apply (erule (1) aag_Control_into_owns)
   apply (drule_tac x=Control in bspec)
    apply (clarsimp simp: cap_auth_conferred_def)
   apply (erule (1) aag_Control_into_owns)
  apply (drule_tac x=Control in bspec)
   apply (clarsimp simp: cap_auth_conferred_def)
  apply (erule (1) aag_Control_into_owns)
  done

lemmas only_timer_irq_inv_irq_state_independent_A[intro!] =
  irq_state_independent_A_only_timer_irq_inv

lemma rec_del_only_timer_irq:
  "\<lbrace>only_timer_irq_inv irq (st :: det_state)\<rbrace>
   rec_del call
   \<lbrace>\<lambda>_. only_timer_irq irq\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (rule hoare_pre, rule only_timer_irq_pres)
    apply (rule hoare_pre, wp rec_del_irq_masks)
    apply (wp rec_del_domain_sep_inv | force | rule hoare_pre, wp (once) rec_del_domain_sep_inv)+
  done

lemma rec_del_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st :: det_state)\<rbrace>
   rec_del call
   \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (rule hoare_wp_simps)
  apply (rule hoare_conjI)
   apply (wp rec_del_domain_sep_inv rec_del_only_timer_irq | force simp: only_timer_irq_inv_def)+
  done

lemma set_cap_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st :: det_state) and K (domain_sep_inv_cap False cap)\<rbrace>
   set_cap cap slot
   \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres set_cap_domain_sep_inv | force)+
  done

lemma finalise_cap_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st :: det_state)\<rbrace>
   finalise_cap cap final
   \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres | force)+
  done


context Finalise_IF_1 begin

lemma rec_del_spec_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
        drop_spec_ev[wp_split del] rec_del.simps[simp del]
  shows
  "spec_reads_respects_f s aag l
     (silc_inv aag st and only_timer_irq_inv irq st' and einvs and simple_sched_action
                      and pas_refined aag and valid_rec_del_call call and emptyable (slot_rdcall call)
                      and (\<lambda>s. \<not> exposed_rdcall call
                               \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall call) s)
                      and K (case call of CTEDeleteCall slot exposed \<Rightarrow> is_subject aag (fst slot)
                               | FinaliseSlotCall slot exposed \<Rightarrow> is_subject aag (fst slot)
                               | ReduceZombieCall cap slot exposed \<Rightarrow> is_subject aag (fst slot) \<and>
                                                                      is_subject aag (obj_ref_of cap)))
     (rec_del call)"
proof (induct s rule: rec_del.induct, simp_all only: rec_del_fails drop_spec_ev[OF fail_ev_pre])
  case (1 slot exposed s) show ?case
    apply (rule spec_equiv_valid_guard_imp)
     apply (simp add: rec_del.simps split_def when_def)
     apply (wp drop_spec_ev[OF returnOk_ev_pre] drop_spec_ev[OF liftE_ev] hoareE_TrueI
               reads_respects_f[OF empty_slot_reads_respects, where st=st] empty_slot_silc_inv)
      apply (rule "1.hyps")
     apply (rule_tac Q'="\<lambda>r s. silc_inv aag st s \<and> is_subject aag (fst slot)" in hoare_post_imp_R)
      apply (wp validE_validE_R'[OF rec_del_silc_inv_not_transferable] | fastforce simp: silc_inv_def)+
    done
next
  case (2 slot exposed s) show ?case
    apply (simp add: rec_del.simps)
    apply (rule spec_equiv_valid_guard_imp)
     apply (wp drop_spec_ev[OF returnOk_ev] drop_spec_ev[OF liftE_ev]
               set_cap_reads_respects_f "2.hyps" preemption_point_inv'
               drop_spec_ev[OF preemption_point_reads_respects_f[where st=st and st'=st']]
               validE_validE_R'[OF rec_del_silc_inv_not_transferable] rec_del_invs
               rec_del_respects(2) rec_del_only_timer_irq_inv
            | simp add: split_def split del: if_split | (rule irq_state_independent_A_conjI, simp)+)+
             apply (rule_tac
                    Q'="\<lambda>rv s. emptyable (slot_rdcall (ReduceZombieCall (fst rvb) slot exposed)) s \<and>
                               (\<not> exposed \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s) \<and>
                               is_subject aag (fst slot)" in hoare_post_imp_R)
              apply (wp rec_del_emptyable reduce_zombie_cap_to)
             apply simp
            apply (wp drop_spec_ev[OF liftE_ev] set_cap_reads_respects_f[where st=st]
                      set_cap_silc_inv[where st=st] | simp)+
           apply (wp replace_cap_invs set_cap_cte_wp_at set_cap_sets final_cap_same_objrefs
                     set_cap_cte_cap_wp_to  hoare_vcg_const_Ball_lift static_imp_wp
                     drop_spec_ev[OF liftE_ev] finalise_cap_reads_respects set_cap_silc_inv
                     set_cap_only_timer_irq_inv set_cap_pas_refined_not_transferable
                  | simp add: cte_wp_at_eq_simp
                  | erule finalise_cap_not_reply_master[simplified Inr_in_liftE_simp])+
         apply (rule hoare_strengthen_post)
          apply (rule_tac
                 Q="\<lambda>fin s. silc_inv aag st s \<and> only_timer_irq_inv irq st' s
                         \<and> (\<not> cap_points_to_label aag (fst fin) (pasObjectAbs aag (fst slot))
                            \<longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps (fst fin) s \<and>
                                         pasObjectAbs aag (fst lslot) = SilcLabel))
                         \<and> einvs s \<and> replaceable s slot (fst fin) rv
                         \<and> cte_wp_at ((=) rv) slot s \<and> s \<turnstile> (fst fin)
                         \<and> ex_cte_cap_wp_to (appropriate_cte_cap rv) slot s
                         \<and> (\<forall>t\<in>obj_refs_ac (fst fin). halted_if_tcb t s)
                         \<and> pas_refined aag s
                         \<and> emptyable slot s
                         \<and> simple_sched_action s
                         \<and> pas_cap_cur_auth aag (fst fin)
                         \<and> is_subject aag (fst slot)
                         \<and> (case (fst fin) of Zombie _ _ _ \<Rightarrow> is_subject aag (obj_ref_of (fst fin))
                                                       | _ \<Rightarrow> True)
                         \<and> (is_zombie (fst fin) \<or> fst fin = NullCap)
                         \<and> (is_zombie (fst fin) \<or> fst fin = NullCap)" in hoare_vcg_conj_lift)
           apply (wp finalise_cap_replaceable Finalise_AC_1.finalise_cap_makes_halted
                     finalise_cap_invs finalise_cap_auth' finalise_cap_ret_is_subject finalise_cap_ret'
                     finalise_cap_silc_inv finalise_cap_ret_is_silc finalise_cap_only_timer_irq_inv)[1]
          apply (rule finalise_cap_cases[where slot=slot])
         apply (clarsimp simp: cte_wp_at_caps_of_state)
         apply (erule disjE)
          apply (clarsimp simp: cap_irq_opt_def cte_wp_at_def is_zombie_def gen_obj_refs_eq
                         split: cap.split_asm if_split_asm
                         elim!: ranE dest!: caps_of_state_cteD)
          apply (clarsimp cong: conj_cong simp: conj_comms)
          apply (rename_tac word option nat)
          apply (drule_tac s="{word}" in sym)
          apply (clarsimp simp: invs_psp_aligned invs_arch_state invs_vspace_objs)
          apply (rule conjI, fastforce)
          apply (clarsimp, rule conjI)
           apply (erule replaceable_zombie_not_transferable)(* WHY *)
          apply (rule conjI)
           apply (fastforce simp: silc_inv_def)
          apply (rule conjI)
           apply (fastforce simp: domain_sep_inv_def domain_sep_inv_cap_def only_timer_irq_inv_def)
          apply (rule conjI[rotated], force)
          apply (clarsimp simp: ex_cte_cap_wp_to_def)+
          apply (rule_tac x="a" in exI, rule_tac x="b" in exI)
          apply (clarsimp simp: cte_wp_at_def appropriate_cte_cap_def)
          apply (drule_tac x="cap" in fun_cong)
          apply (clarsimp simp: appropriate_cte_cap_def split: cap.splits)
         apply (clarsimp cong: conj_cong simp: conj_comms)
        apply (wp drop_spec_ev[OF liftE_ev] is_final_cap_reads_respects | simp)+
       apply (rule_tac Q="\<lambda>rva s. rva = is_final_cap' rv s \<and> cte_wp_at ((=) rv) slot s \<and>
                                  only_timer_irq_inv irq st' s \<and> silc_inv aag st s \<and>
                                  pas_refined aag s \<and> pas_cap_cur_auth aag rv \<and>
                                  invs s \<and> valid_list s \<and> valid_sched s \<and> simple_sched_action s \<and>
                                  s \<turnstile> rv \<and> is_subject aag (fst slot) \<and> emptyable slot s \<and>
                                  ex_cte_cap_wp_to (appropriate_cte_cap rv) slot s"
                    in hoare_strengthen_post)
        apply (wp is_final_cap_is_final | simp)+
       apply clarsimp
       apply (rule conjI)
        apply clarsimp
        apply (frule silc_inv)
        apply (erule_tac x=rv in allE, erule_tac x=slot in allE)
        apply simp
        apply (erule disjE)
         apply (drule(1) intra_label_capD)
         apply (clarsimp simp: cap_points_to_label_def split: cap.splits)
        apply (simp add: silc_inv_def)
       apply (force simp: owns_cnode_owns_obj_ref_of_child_cnodes_threads_and_zombies)
      apply (wp drop_spec_ev reads_respects_f[OF get_cap_rev, where st=st and Q="\<top>"] get_cap_wp
             | simp)+
    apply (clarsimp cong: conj_cong simp: invs_valid_objs invs_arch_state invs_psp_aligned)
    apply (intro conjI impI | clarsimp | assumption | fastforce dest: silc_inv_not_subject)+
      apply (erule (1) cap_cur_auth_caps_of_state[rotated])
      apply (simp add: cte_wp_at_caps_of_state)
     apply (fastforce dest: cte_wp_at_valid_objs_valid_cap simp: invs_valid_objs)
    apply (drule if_unsafe_then_capD)
      apply (simp add: invs_ifunsafe)
     apply simp
    apply (clarsimp simp: ex_cte_cap_wp_to_def)
    done
next
  case (3 ptr bits n slot s) show ?case
    apply (simp add: rec_del.simps)
    apply (rule spec_equiv_valid_guard_imp)
     apply (wp drop_spec_ev[OF liftE_ev] drop_spec_ev[OF returnOk_ev]
              reads_respects_f[OF cap_swap_for_delete_reads_respects] cap_swap_for_delete_silc_inv
              drop_spec_ev[OF assertE_ev])+
    apply (fastforce simp: silc_inv_def)
    done
next
  case (4 ptr bits n slot s) show ?case
    apply (simp add: rec_del.simps)
    apply (rule spec_equiv_valid_guard_imp)
     apply (wp drop_spec_ev[OF returnOk_ev] drop_spec_ev[OF liftE_ev] set_cap_reads_respects_f
               drop_spec_ev[OF assertE_ev] get_cap_wp "4.hyps"
               reads_respects_f[OF get_cap_rev, where st=st and Q="\<top>"]
               validE_validE_R'[OF rec_del_silc_inv_not_transferable]
            | simp add: in_monad)+
     apply (rule_tac Q'="\<lambda> _. silc_inv aag st and
                            K (pasObjectAbs aag (fst slot) \<noteq> SilcLabel \<and> is_subject aag (fst slot))"
                  in hoare_post_imp_R)
      prefer 2
      apply (clarsimp)
      apply (rule conjI, assumption)
      apply (rule impI)
      apply (drule silc_invD)
        apply assumption
       apply (simp add: intra_label_cap_def)
       apply (rule exI)
       apply (rule conjI)
        apply assumption
       apply (fastforce simp: cap_points_to_label_def)
      apply (clarsimp simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
     apply (wp validE_validE_R'[OF rec_del_silc_inv_not_transferable] | simp)+
    apply (clarsimp simp: zombie_is_cap_toE cte_wp_at_caps_of_state zombie_ptr_emptyable silc_inv_def)
    done
qed

lemmas rec_del_reads_respects_f = use_spec_ev[OF rec_del_spec_reads_respects_f]

end


(* FIXME MOVE in lib *)
lemma ev_pre_cont:
  "equiv_valid I A B \<bottom> f"
  by (simp add: equiv_valid_def2 equiv_valid_2_def)

lemma finalise_cap_transferable_ev:
  "equiv_valid_inv I A (K(is_transferable_cap cap)) (finalise_cap cap final)"
  by (rule gen_asm_ev) (erule is_transferable_capE; wpsimp wp: return_ev)

lemma rec_del_Finalise_transferable_read_respects_f:
  "reads_respects_f aag l
     (silc_inv aag st and is_transferable_in slot and K(aag_can_read_not_silc aag (fst slot)))
     (rec_del (FinaliseSlotCall slot exposed))"
  apply (subst rec_del.simps[abs_def])
  apply (wp | wpc | simp)+
           apply ((wp ev_pre_cont hoare_pre_cont)+)[3]
        apply simp
        apply (wp liftE_ev finalise_cap_transferable_ev | simp)+
       apply (rule hoare_post_imp[OF _ finalise_cap_transferable[where P=\<top>]], fastforce)
      apply (wpsimp wp: is_final_cap_reads_respects hoare_drop_imp get_cap_wp
                        reads_respects_f[OF get_cap_rev, where st=st and Q="\<top>"])+
  by (fastforce simp: cte_wp_at_caps_of_state)

lemma rec_del_Finalise_transferableE_R:
  "\<lbrace>(\<lambda>s. is_transferable (caps_of_state s slot)) and P\<rbrace>
   rec_del (FinaliseSlotCall slot exposed)
   \<lbrace>\<lambda>_. P\<rbrace>, -"
  apply (rule hoare_pre)
   apply (simp add: validE_R_def)
   apply (rule hoare_post_impErr)
     apply (rule rec_del_Finalise_transferable)
  by force+


context Finalise_IF_1 begin

lemma rec_del_CTEDeleteCall_reads_respects_f:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_f aag l
     (silc_inv aag st and only_timer_irq_inv irq st' and einvs and simple_sched_action
                      and pas_refined aag and emptyable slot and cdt_change_allowed' aag slot
                      and (\<lambda>s. \<not> exposed \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s))
     (rec_del (CTEDeleteCall slot exposed))"
  apply (cases "is_subject aag (fst slot)")
   apply (rule equiv_valid_guard_imp)
   apply (wp rec_del_reads_respects_f)
   apply fastforce
  apply (subst rec_del.simps[abs_def])
  apply (wp when_ev reads_respects_f[OF empty_slot_reads_respects] empty_slot_silc_inv
            rec_del_Finalise_transferable_read_respects_f hoare_vcg_all_lift_R hoare_drop_impE_R
            rec_del_Finalise_transferableE_R
         | wpc | simp)+
  apply clarsimp
  apply (frule(3) cca_can_read[OF invs_mdb invs_valid_objs])
  apply (frule(2) cdt_change_allowed_not_silc[rotated 2], force, force)
  apply (frule(1) cca_to_transferable_or_subject[rotated 2], force, force)
  apply force
  done

lemma cap_delete_reads_respects:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "reads_respects_f aag l (silc_inv aag st and only_timer_irq_inv irq st' and einvs
                                           and simple_sched_action and pas_refined aag
                                           and emptyable slot and K (is_subject aag (fst slot)))
                    (cap_delete slot)"
  unfolding cap_delete_def
  by (wp rec_del_spec_reads_respects_f | rule use_spec_ev | simp | elim conjE | force)+

end


lemma globals_equiv_interrupt_states_update:
  "globals_equiv st (s\<lparr>interrupt_states := x\<rparr>) = globals_equiv st s"
  by (auto simp: globals_equiv_def idle_equiv_def)

lemma cancel_all_ipc_globals_equiv':
  "cancel_all_ipc epptr \<lbrace>globals_equiv st and valid_arch_state\<rbrace>"
  unfolding cancel_all_ipc_def
  by (wp mapM_x_wp[OF _ subset_refl] set_thread_state_globals_equiv
         set_simple_ko_globals_equiv hoare_vcg_all_lift get_object_inv dxo_wp_weak
      | wpc | simp | wp (once) hoare_drop_imps)+

lemma cancel_all_ipc_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   cancel_all_ipc epptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  by (fastforce intro: hoare_strengthen_post[OF cancel_all_ipc_globals_equiv'])

crunch valid_global_objs: fast_finalise "valid_global_objs"
  (wp: crunch_wps dxo_wp_weak ignore: reschedule_required)

lemma cancel_all_signals_globals_equiv':
  "cancel_all_signals epptr \<lbrace>globals_equiv st and valid_arch_state\<rbrace>"
  unfolding cancel_all_signals_def
  by (wp mapM_x_wp[OF _ subset_refl] set_thread_state_globals_equiv
         set_simple_ko_globals_equiv hoare_vcg_all_lift get_object_inv dxo_wp_weak
      | wpc | simp | wp (once) hoare_drop_imps)+

lemma cancel_all_signals_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   cancel_all_signals epptr
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  by (fastforce intro: hoare_strengthen_post[OF cancel_all_signals_globals_equiv'])


context Finalise_IF_1 begin

lemma unbind_notification_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   unbind_notification t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding unbind_notification_def
  by (wpsimp wp: gbn_wp set_bound_notification_globals_equiv set_notification_globals_equiv)

lemma unbind_maybe_notification_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   unbind_maybe_notification a
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding unbind_maybe_notification_def
  by (wpsimp wp: gbn_wp set_bound_notification_globals_equiv
                 set_notification_globals_equiv get_simple_ko_wp)

lemma fast_finalise_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace>
   fast_finalise cap final
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (cases cap)
  by (wpsimp wp: cancel_all_ipc_globals_equiv cancel_all_signals_globals_equiv
                    unbind_maybe_notification_globals_equiv
              simp: when_def split_del: if_split)+

crunch globals_equiv[wp]: deleted_irq_handler "globals_equiv st"

lemma empty_slot_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state\<rbrace> empty_slot s b \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding empty_slot_def post_cap_deletion_def
  by (wpsimp wp: set_cap_globals_equiv'' set_original_globals_equiv hoare_vcg_if_lift2
                 set_cdt_globals_equiv dxo_wp_weak hoare_drop_imps hoare_vcg_all_lift)

crunch globals_equiv: cap_delete_one "globals_equiv st"
  (wp: set_cap_globals_equiv'' hoare_drop_imps simp: crunch_simps unless_def)

(*FIXME: Lots of this stuff should be in arch *)
crunch globals_equiv[wp]: deleting_irq_handler "globals_equiv st"

crunch globals_equiv[wp]: cancel_ipc "globals_equiv st"
  (wp: mapM_x_wp select_inv hoare_drop_imps hoare_vcg_if_lift2 simp: unless_def)

lemma suspend_globals_equiv[ wp]:
  "\<lbrace>globals_equiv st and (\<lambda>s. t \<noteq> idle_thread s) and valid_arch_state\<rbrace>
   suspend t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding suspend_def update_restart_pc_def
  apply (wp tcb_sched_action_extended.globals_equiv dxo_wp_weak)
       apply simp
      apply (wp set_thread_state_globals_equiv)
     apply wp+
    apply clarsimp
    apply (rule hoare_vcg_conj_lift)
     prefer 2
     apply (rule hoare_drop_imps)
     apply wp+
    apply (rule hoare_drop_imps)
    apply wp+
  apply auto
  done

crunches unbind_notification
  for valid_arch_state[wp]: valid_arch_state

lemma finalise_cap_globals_equiv:
  "\<lbrace>globals_equiv st and invs and valid_cap cap
                     and (\<lambda>s. \<forall>p. cap = ThreadCap p \<longrightarrow> p \<noteq> idle_thread s)\<rbrace>
   finalise_cap cap b
   \<lbrace>\<lambda> _. globals_equiv st\<rbrace>"
  apply (induct cap; simp)
  by (wp cancel_all_ipc_globals_equiv cancel_all_ipc_valid_global_objs
         cancel_all_signals_globals_equiv cancel_all_signals_valid_global_objs
         arch_finalise_cap_globals_equiv unbind_maybe_notification_globals_equiv
         unbind_notification_globals_equiv liftM_wp when_def
      | clarsimp simp: valid_cap_def | intro impI conjI)+

end

end
