(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Finalise_IF
imports Arch_IF IRQMasks_IF
begin

context begin interpretation Arch . (*FIXME: arch_split*)

crunch_ignore (add: tcb_sched_action)

crunch cur_thread[wp]: finalise_cap "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps select_wp modify_wp dxo_wp_weak
   simp: crunch_simps)

lemma dmo_maskInterrupt_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (maskInterrupt m irq))"
  unfolding maskInterrupt_def
  apply(rule use_spec_ev)
  apply(rule do_machine_op_spec_reads_respects)
   apply(simp add: equiv_valid_def2)
   apply(rule modify_ev2)
   apply(fastforce simp: equiv_for_def)
  apply (wp modify_wp | simp)+
  done

lemma set_irq_state_reads_respects:
  "reads_respects aag l \<top> (set_irq_state state irq)"
  unfolding set_irq_state_def fun_app_def
  apply(wp dmo_maskInterrupt_reads_respects)
    apply(subst equiv_valid_def2)
    apply(rule_tac P="\<top>" and P'="\<top>" in modify_ev2)
    apply clarsimp
    apply(rule conjI)
     apply(fastforce intro!: reads_equiv_interrupt_states_update elim: reads_equivE intro: equiv_forI elim: equiv_forE)
    apply(fastforce intro!: affects_equiv_interrupt_states_update elim: affects_equivE intro: equiv_forI elim: equiv_forE)
   apply(wp)
  apply(fastforce)
  done


lemma deleted_irq_handler_reads_respects:
  "reads_respects aag l \<top> (deleted_irq_handler irq)"
  unfolding deleted_irq_handler_def
  apply(rule set_irq_state_reads_respects)
  done

lemma empty_slot_reads_respects:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "reads_respects aag l (K (is_subject aag (fst slot))) (empty_slot slot free_irq)"
  unfolding empty_slot_def fun_app_def
  apply (simp add: bind_assoc[symmetric] cong: if_cong)
  apply (fold update_cdt_def)
  apply (simp add: bind_assoc empty_slot_ext_def cong: if_cong)
  apply(rule gen_asm_ev)
  apply (wp deleted_irq_handler_reads_respects set_cap_reads_respects set_original_reads_respects update_cdt_list_reads_respects | wpc | simp | (frule aag_can_read_self,fastforce simp: equiv_for_def split: option.splits))+
        apply (wp update_cdt_reads_respects get_cap_wp get_cap_rev)+
  apply(intro impI allI conjI)
        apply(fastforce simp: reads_equiv_def2 equiv_for_def elim: states_equiv_forE_cdt dest: aag_can_read_self split: option.splits)+ done

lemma requiv_get_tcb_eq':
  "\<lbrakk>reads_equiv aag s t; aag_can_read aag thread\<rbrakk> \<Longrightarrow>
    get_tcb thread s = get_tcb thread t"
  apply(auto simp: reads_equiv_def2 elim: states_equiv_forE_kheap dest!: aag_can_read_self simp: get_tcb_def split: option.split kernel_object.split)
  done

lemma requiv_the_get_tcb_eq':
  "\<lbrakk>reads_equiv aag s t; aag_can_read aag thread\<rbrakk> \<Longrightarrow>
    the (get_tcb thread s) = the (get_tcb thread t)"
  apply(subgoal_tac "get_tcb thread s = get_tcb thread t")
   apply(simp)
  apply(fastforce intro: requiv_get_tcb_eq')
  done



(* FIXME: move *)




lemma set_object_modifies_at_most:
  "modifies_at_most aag {pasObjectAbs aag ptr} (\<lambda> s. \<not> asid_pool_at ptr s \<and> (\<forall> asid_pool. obj \<noteq> ArchObj (ASIDPool asid_pool))) (set_object ptr obj)"
  apply(rule modifies_at_mostI)
  apply(wp set_object_equiv_but_for_labels)
  apply clarsimp
  done




(*Not currently considered*)
lemma scheduler_action_states_equiv[simp]: "states_equiv_for P Q R S st (scheduler_action_update f s) = states_equiv_for P Q R S st s"
  apply (simp add: states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)
  done

crunch states_equiv[wp]: set_thread_state_ext "states_equiv_for P Q R S st"

lemma set_scheduler_action_reads_respects[wp]:
  "reads_respects aag l \<top> (set_scheduler_action action)"
  by (simp add: set_scheduler_action_def modify_def put_def get_def bind_def equiv_valid_def2 equiv_valid_2_def reads_equiv_scheduler_action_update affects_equiv_scheduler_action_update)

lemma set_thread_state_ext_reads_respects:
  "reads_respects aag l (\<lambda>s. is_subject aag (cur_thread s)) (set_thread_state_ext ref)"
  apply (case_tac "is_subject aag ref")
   apply (simp add: set_thread_state_ext_def when_def get_thread_state_def | wp thread_get_rev)+
   apply (simp add: reads_equiv_def)
  apply (simp add: set_thread_state_ext_def when_def)
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_rv_bind[where W="\<top>\<top>"])
    apply (clarsimp simp: equiv_valid_2_def get_thread_state_def thread_get_def gets_the_def return_def bind_def assert_opt_def gets_def get_tcb_def fail_def get_def split: option.splits kernel_object.splits)
   apply clarsimp
   apply (rule equiv_valid_2_bind[where R'="op =" and Q="\<lambda>rv _. rv \<noteq> ref" and Q'="\<lambda>rv _. rv \<noteq> ref"])
      apply (rule gen_asm_ev2)
      apply (simp add: equiv_valid_def2[symmetric] | wp)+
      apply (clarsimp simp: reads_equiv_def)
     apply (subst equiv_valid_def2[symmetric])
     apply wp+
  apply force
  done

lemma set_thread_state_reads_respects:
  "reads_respects aag l (\<lambda>s. is_subject aag (cur_thread s)) (set_thread_state ref ts)"
  unfolding set_thread_state_def fun_app_def
  apply (simp add: bind_assoc[symmetric]) (*Remove the currently not considered extended op*)
  apply (rule pre_ev)
   apply (rule_tac P'=\<top> in bind_ev)
     apply (rule set_thread_state_ext_reads_respects)
    apply(case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
     apply(wp set_object_reads_respects gets_the_ev)
     apply(fastforce simp: get_tcb_def split: option.splits elim: reads_equivE affects_equivE equiv_forE)
    apply(simp add: equiv_valid_def2)
    apply(rule equiv_valid_rv_bind)
      apply(rule equiv_valid_rv_trivial)
      apply (wp | simp)+
     apply(rule_tac P="\<top>" and P'="\<top>" and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}" in ev2_invisible)
         apply (blast | simp add: labels_are_invisible_def)+
       apply(rule set_object_modifies_at_most)
      apply(rule set_object_modifies_at_most)
     apply(simp | wp)+
    apply(blast dest: get_tcb_not_asid_pool_at)
   apply (subst thread_set_def[symmetric, simplified fun_app_def])
   apply (wp | simp)+
   done

lemma set_bound_notification_reads_respects:
  "reads_respects aag l (\<lambda>s. is_subject aag (cur_thread s)) (set_bound_notification ref ntfn)"
  unfolding set_bound_notification_def fun_app_def
  apply (rule pre_ev(5)[where Q=\<top>])
   apply(case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
    apply(wp set_object_reads_respects gets_the_ev)[1]
    apply (fastforce simp: get_tcb_def split: option.splits elim: reads_equivE affects_equivE equiv_forE)
   apply (simp add: equiv_valid_def2)
   apply(rule equiv_valid_rv_bind)
     apply(rule equiv_valid_rv_trivial)
     apply (wp | simp)+
    apply(rule_tac P="\<top>" and P'="\<top>" and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}" in ev2_invisible)
        apply (blast | simp add: labels_are_invisible_def)+
      apply(rule set_object_modifies_at_most)
     apply(rule set_object_modifies_at_most)
    apply(simp | wp)+
   apply(blast dest: get_tcb_not_asid_pool_at)
  apply simp
  done

lemma set_thread_state_ext_owned_reads_respects:
  "reads_respects aag l (\<lambda>s. is_subject aag ref) (set_thread_state_ext ref)"
  apply (simp add: set_thread_state_ext_def when_def get_thread_state_def | wp thread_get_rev)+
  apply (simp add: reads_equiv_def)
  done

lemma set_thread_state_owned_reads_respects:
  "reads_respects aag l (\<lambda>s. is_subject aag ref) (set_thread_state ref ts)"
  apply (simp add: set_thread_state_def fun_app_def)
  apply (wp set_object_reads_respects gets_the_ev set_thread_state_ext_owned_reads_respects)
  apply (force elim: reads_equivE equiv_forE)
  done

lemma set_bound_notification_owned_reads_respects:
  "reads_respects aag l (\<lambda>s. is_subject aag ref) (set_bound_notification ref ntfn)"
  apply (simp add:set_bound_notification_def fun_app_def)
  apply (wp set_object_reads_respects gets_the_ev)
  apply (force elim: reads_equivE equiv_forE)
  done

lemma get_thread_state_runnable[wp]: "\<lbrace>st_tcb_at runnable ref\<rbrace> get_thread_state ref \<lbrace>\<lambda>rv _. runnable rv\<rbrace>"
  apply (simp add: get_thread_state_def thread_get_def)
  apply wp
  apply (clarsimp simp: st_tcb_at_def obj_at_def get_tcb_def)
  done

lemma set_thread_state_ext_runnable_reads_respects:
  "reads_respects aag l (st_tcb_at runnable ref) (set_thread_state_ext ref)"
  apply (simp add: set_thread_state_ext_def when_def)
  apply (simp add: equiv_valid_def2)
  apply (rule equiv_valid_rv_bind[where W="\<top>\<top>" and Q="\<lambda>rv _. runnable rv"])
    apply (clarsimp simp: equiv_valid_2_def get_thread_state_def thread_get_def gets_the_def return_def bind_def assert_opt_def gets_def get_tcb_def fail_def get_def split: option.splits kernel_object.splits)
   apply (rule gen_asm_ev2)
   apply (clarsimp simp: equiv_valid_def2[symmetric] | wp)+
   apply (simp add: reads_equiv_def)
  apply wp
  done

lemma set_thread_state_runnable_reads_respects:
  "runnable ts \<Longrightarrow> reads_respects aag l \<top> (set_thread_state ref ts)"
  unfolding set_thread_state_def fun_app_def
  apply (simp add: bind_assoc[symmetric]) (*Remove the currently not considered extended op*)
  apply (rule pre_ev)
   apply (rule_tac P'=\<top> in bind_ev)
     apply (rule set_thread_state_ext_runnable_reads_respects)
    apply(case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
     apply(wp set_object_reads_respects gets_the_ev)
     apply(fastforce simp: get_tcb_def split: option.splits elim: reads_equivE affects_equivE equiv_forE)
    apply(simp add: equiv_valid_def2)
    apply(rule equiv_valid_rv_bind)
      apply(rule equiv_valid_rv_trivial)
      apply (wp | simp)+
     apply(rule_tac P="\<top>" and P'="\<top>" and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}" in ev2_invisible)
         apply (blast | simp add: labels_are_invisible_def)+
       apply(rule set_object_modifies_at_most)
      apply(rule set_object_modifies_at_most)
     apply(simp | wp)+
    apply(blast dest: get_tcb_not_asid_pool_at)
   apply (subst thread_set_def[symmetric, simplified fun_app_def])
   apply (wp thread_set_st_tcb_at | simp)+
   done

lemma set_bound_notification_none_reads_respects:
  "reads_respects aag l \<top> (set_bound_notification ref None)"
  unfolding set_bound_notification_def fun_app_def
  apply (rule pre_ev(5)[where Q=\<top>])
   apply(case_tac "aag_can_read aag ref \<or> aag_can_affect aag l ref")
    apply(wp set_object_reads_respects gets_the_ev)[1]
    apply (fastforce simp: get_tcb_def split: option.splits elim: reads_equivE affects_equivE equiv_forE)
   apply (simp add: equiv_valid_def2)
   apply(rule equiv_valid_rv_bind)
     apply(rule equiv_valid_rv_trivial)
     apply (wp | simp)+
    apply(rule_tac P="\<top>" and P'="\<top>" and L="{pasObjectAbs aag ref}" and L'="{pasObjectAbs aag ref}" in ev2_invisible)
        apply (blast | simp add: labels_are_invisible_def)+
      apply(rule set_object_modifies_at_most)
     apply(rule set_object_modifies_at_most)
    apply(simp | wp)+
   apply(blast dest: get_tcb_not_asid_pool_at)
  apply simp
  done

lemma get_object_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> (get_object ptr)"
  apply(rule equiv_valid_rv_trivial)
  apply wp
  done

lemma set_endpoint_reads_respects:
  "reads_respects aag l \<top> (set_endpoint ptr ep)"
  unfolding set_endpoint_def
  apply(simp add: equiv_valid_def2)
  apply(rule equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp)
     apply(rule get_object_revrv)
    apply(simp, simp)
   apply(rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
      apply(subst equiv_valid_def2[symmetric])
      apply(rule set_object_reads_respects)
     apply(rule assert_ev2)
     apply(simp)
    apply(rule assert_wp)+
  apply(simp)
  apply(rule get_object_inv)
  done

lemma get_ep_queue_reads_respects:
  "reads_respects aag l \<top> (get_ep_queue ep)"
  unfolding get_ep_queue_def
  apply(rule equiv_valid_guard_imp)
   apply(wp | wpc)+
  apply(simp)
  done

lemma get_object_reads_respects:
  "reads_respects aag l (K (aag_can_read aag ptr \<or> (aag_can_affect aag l ptr))) (get_object ptr)"
  apply (unfold get_object_def fun_app_def)
  apply (subst gets_apply)
  apply (wp gets_apply_ev | wp_once hoare_drop_imps)+
  apply (fastforce elim: reads_equivE affects_equivE equiv_forE)
  done

lemma get_endpoint_reads_respects:
  "reads_respects aag l (K (aag_can_read aag ptr \<or> aag_can_affect aag l ptr)) (get_endpoint ptr)"
  unfolding get_endpoint_def
  apply(wp get_object_reads_respects | wpc | simp)+
  done

lemma get_epq_SendEP_ret:
  "\<lbrace>\<lambda>s. \<forall>x\<in>set list. P x\<rbrace> get_ep_queue (SendEP list) \<lbrace>\<lambda>rv s. \<forall>x\<in>set rv. P x\<rbrace>"
  apply(simp add: get_ep_queue_def)
  apply(wp)
  done

lemma get_epq_RecvEP_ret:
  "\<lbrace>\<lambda>s. \<forall>x\<in>set list. P x\<rbrace> get_ep_queue (RecvEP list) \<lbrace>\<lambda>rv s. \<forall>x\<in>set rv. P x\<rbrace>"
  apply(simp add: get_ep_queue_def)
  apply(wp)
  done

fun ep_queue_invisible where
  "ep_queue_invisible aag l (SendEP list) = labels_are_invisible aag l ((pasObjectAbs aag) ` (set list))" |
  "ep_queue_invisible aag l (RecvEP list) = labels_are_invisible aag l ((pasObjectAbs aag) ` (set list))" |
  "ep_queue_invisible aag l IdleEP = True"

(*
(* unneeded now? *)
lemma aag_can_affect_ep_queued:
  "\<lbrakk>(pasSubject aag, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag;
    ko_at (Endpoint (SendEP list)) epptr s \<or> ko_at (Endpoint (RecvEP list)) epptr s;
    t \<in> set list; pas_refined aag s; valid_objs s; sym_refs (state_refs_of s)\<rbrakk> \<Longrightarrow>
  aag_can_affect aag (pasObjectAbs aag t) t"
  apply(erule disjE)
   apply(drule_tac P="send_blocked_on epptr" in ep_queued_st_tcb_at'')
       apply(fastforce)
      apply assumption
     apply assumption
    apply simp
   apply(rule conjI)
    apply(erule_tac auth=SyncSend and l'="pasObjectAbs aag t" in affects_reset)
      apply(erule pas_refined_mem[rotated])
      apply(rule sta_ts)
      apply(clarsimp simp: thread_states_def split: option.split simp: tcb_states_of_state_def st_tcb_def2)
      apply(case_tac "tcb_state tcb", simp_all)
  apply(drule_tac P="receive_blocked_on epptr" in ep_queued_st_tcb_at'')
      apply(fastforce)
     apply assumption
    apply assumption
   apply simp
  apply(erule_tac auth=Receive and l'="pasObjectAbs aag t" in affects_reset)
   apply(erule pas_refined_mem[rotated])
   apply(rule sta_ts)
   apply(clarsimp simp: thread_states_def split: option.split simp: tcb_states_of_state_def st_tcb_def2)
   apply(case_tac "tcb_state tcb", simp_all)
  done
*)

lemma obj_eq_st_tcb_at:
  "\<lbrakk>kheap s x = kheap s' x; st_tcb_at P x s'\<rbrakk> \<Longrightarrow>
  st_tcb_at P x s"
  apply(clarsimp simp: st_tcb_at_def obj_at_def)
  done


lemma send_blocked_on_tcb_st_to_auth:
  "send_blocked_on epptr ts
   \<Longrightarrow> (epptr, SyncSend) \<in> tcb_st_to_auth ts"
  apply(case_tac ts, simp_all)
  done

lemma receive_blocked_on_tcb_st_to_auth:
  "receive_blocked_on epptr ts
   \<Longrightarrow> (epptr, Receive) \<in> tcb_st_to_auth ts"
  apply(case_tac ts, simp_all)
  done


lemma not_ep_queue_invisible:
  "\<lbrakk>\<not> ep_queue_invisible aag l eplist; eplist = SendEP list \<or> eplist = RecvEP list\<rbrakk>  \<Longrightarrow>
  (\<exists> t \<in> set list. aag_can_read aag t \<or> aag_can_affect aag l t)"
  apply(auto simp: labels_are_invisible_def)
  done


lemma ep_queues_are_invisible_or_eps_are_equal':
  "\<lbrakk>(pasSubject aag, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag;
    ko_at (Endpoint ep) epptr s;
    ko_at (Endpoint ep') epptr s';
    reads_equiv aag s s'; affects_equiv aag l s s';
    valid_objs s; sym_refs (state_refs_of s); valid_objs s';
    sym_refs (state_refs_of s'); pas_refined aag s; pas_refined aag s'\<rbrakk> \<Longrightarrow>
  (\<not> ep_queue_invisible aag l ep) \<longrightarrow> ep = ep'"
  apply(rule impI)
  apply(case_tac "\<exists> list. ep = SendEP list \<or> ep = RecvEP list")
   apply(erule exE)
   apply(drule (1) not_ep_queue_invisible)
   apply clarsimp
   apply(erule disjE)
    apply(erule disjE)
     apply(drule_tac auth="SyncSend" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
         apply blast
        apply(erule pas_refined_mem[rotated])
        apply(rule sta_ts)
        apply(drule_tac P="send_blocked_on epptr" and s=s and t=t in ep_queued_st_tcb_at'')
            apply(simp)+
        apply(simp add: thread_states_def split: option.splits)
        apply(clarsimp simp: tcb_states_of_state_def st_tcb_def2 send_blocked_on_tcb_st_to_auth)
       apply blast
      apply assumption
     apply(fastforce dest: reads_affects_equiv_kheap_eq simp: obj_at_def)
    apply(drule_tac auth="SyncSend" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
        apply blast
       apply(erule pas_refined_mem[rotated])
       apply(rule sta_ts)
       apply(drule_tac P="send_blocked_on epptr" and s=s and t=t in ep_queued_st_tcb_at'')
           apply(simp)+
       apply(simp add: thread_states_def split: option.splits)
       apply(clarsimp simp: tcb_states_of_state_def st_tcb_def2 send_blocked_on_tcb_st_to_auth)
      apply blast
     apply(erule conjE, assumption)
    apply(drule_tac x=epptr in reads_affects_equiv_kheap_eq, simp+)
    apply(fastforce simp: obj_at_def)
   apply(erule disjE)
    apply(drule_tac auth="Receive" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
        apply blast
       apply(erule pas_refined_mem[rotated])
       apply(rule sta_ts)
       apply(drule_tac P="receive_blocked_on epptr" and s=s and t=t in ep_queued_st_tcb_at'')
           apply(simp)+
       apply(simp add: thread_states_def split: option.splits)
       apply(clarsimp simp: tcb_states_of_state_def st_tcb_def2 receive_blocked_on_tcb_st_to_auth)
      apply blast
     apply assumption
    apply(fastforce dest: reads_affects_equiv_kheap_eq simp: obj_at_def)
   apply(drule_tac auth="Receive" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
       apply blast
      apply(erule pas_refined_mem[rotated])
      apply(rule sta_ts)
      apply(drule_tac P="receive_blocked_on epptr" and s=s and t=t in ep_queued_st_tcb_at'')
          apply(simp)+
      apply(simp add: thread_states_def split: option.splits)
      apply(clarsimp simp: tcb_states_of_state_def st_tcb_def2 receive_blocked_on_tcb_st_to_auth)
     apply blast
    apply(erule conjE, assumption)
   apply(drule_tac x=epptr in reads_affects_equiv_kheap_eq, simp+)
   apply(fastforce simp: obj_at_def)
  apply(case_tac ep, auto)
  done


lemma ep_queues_are_invisible_or_eps_are_equal:
  "\<lbrakk>(pasSubject aag, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag;
    ko_at (Endpoint ep) epptr s;
    ko_at (Endpoint ep') epptr s';
    reads_equiv aag s s'; affects_equiv aag l s s';
    valid_objs s; sym_refs (state_refs_of s); valid_objs s';
    sym_refs (state_refs_of s'); pas_refined aag s; pas_refined aag s'\<rbrakk> \<Longrightarrow>
  (\<not> ep_queue_invisible aag l ep \<or> \<not> ep_queue_invisible aag l ep') \<longrightarrow> ep = ep'"
  apply(rule impI)
  apply(erule disjE)
   apply(blast intro!: ep_queues_are_invisible_or_eps_are_equal'[rule_format])
  apply(rule sym)
  apply(erule ep_queues_are_invisible_or_eps_are_equal'[rule_format])
            apply (assumption | erule reads_equiv_sym | erule affects_equiv_sym)+
  done

lemma get_endpoint_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
        (\<lambda>ep ep'. (\<not> ep_queue_invisible aag l ep \<or> \<not> ep_queue_invisible aag l ep') \<longrightarrow> ep = ep')
        (pas_refined aag and valid_objs and sym_refs \<circ> state_refs_of and
         K ((pasSubject aag, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag))
        (get_endpoint epptr)"
  unfolding get_endpoint_def
  apply(rule_tac Q="\<lambda> rv. ko_at rv epptr and pas_refined aag and valid_objs and sym_refs \<circ> state_refs_of and (K ((pasSubject aag, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag))" in equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp[OF equiv_valid_rv_trivial])
     apply wp+
   apply(case_tac "\<exists> ep. rv = Endpoint ep")
    apply(case_tac "\<exists> ep. rv' = Endpoint ep")
     apply (clarsimp split: kernel_object.splits)
     apply (rule return_ev2)
     apply (rule ep_queues_are_invisible_or_eps_are_equal[simplified])
                apply fastforce+
    apply(clarsimp split: kernel_object.splits simp: fail_ev2_l fail_ev2_r)
   apply(clarsimp split: kernel_object.splits simp: fail_ev2_l fail_ev2_r)
  apply (rule hoare_strengthen_post[OF get_object_sp])
  by simp

lemma gen_asm_ev2_r:
  "\<lbrakk>P' \<Longrightarrow> equiv_valid_2 I A B R P \<top> f f'\<rbrakk> \<Longrightarrow>
   equiv_valid_2 I A B R P (\<lambda>s. P') f f'"
  by (rule gen_asm_ev2_r')

lemma gen_asm_ev2_l:
  "\<lbrakk>P \<Longrightarrow> equiv_valid_2 I A B R \<top> P' f f'\<rbrakk> \<Longrightarrow>
   equiv_valid_2 I A B R (\<lambda>s. P) P' f f'"
  by (rule gen_asm_ev2_l')

lemma bind_return_unit2:
  "f = return () >>= (\<lambda>_. f)"
  by simp

lemma mapM_x_ev2_invisible:
  assumes
    mam: "\<And> ptr. modifies_at_most aag (L ptr) \<top> ((f::word32 \<Rightarrow> (unit,det_ext) s_monad) ptr)"
  assumes
    mam': "\<And> ptr. modifies_at_most aag (L' ptr) \<top> ((f'::word32 \<Rightarrow> (unit,det_ext) s_monad) ptr)"
  shows
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
   op =
   (K (\<forall>x. x \<in> set list' \<longrightarrow> (labels_are_invisible aag l (L' x))))
   (K (\<forall>x. x \<in> set list \<longrightarrow>  (labels_are_invisible aag l (L x))))
   (mapM_x f' list') (mapM_x f list)"
  apply(induct list)
   apply(induct_tac list')
    apply (simp add: mapM_x_Nil)
    apply (blast intro: return_ev2)
   apply (simp add: mapM_x_Cons mapM_x_Nil)
   apply (subst bind_return_unit[where f="return ()"])
   apply (rule_tac R'="op =" and P="\<lambda> s. labels_are_invisible aag l (L' a)" in equiv_valid_2_bind_pre)
        apply simp
       apply(rule gen_asm_ev2_l)
       apply(rule equiv_valid_2_guard_imp[OF ev2_invisible], assumption+)
           apply(rule mam')
          apply(rule_tac P="\<top>" in modifies_at_mostI)
          apply(wp | simp)+
  apply (simp add: mapM_x_Cons)
  apply (subst bind_return_unit2)
  apply (rule_tac R'="op =" and P'="\<lambda> s. labels_are_invisible aag l (L a)" in equiv_valid_2_bind_pre)
       apply simp
       apply(rule gen_asm_ev2_r)
       apply(rule equiv_valid_2_guard_imp[OF ev2_invisible], assumption+)
          apply(rule_tac P="\<top>" in modifies_at_mostI)
          apply(wp | simp)+
         apply(rule mam)
        apply(wp | simp)+
  done

lemma ev2_inv:
  assumes
    inv: "\<And> P. invariant f P"
  assumes
    inv': "\<And> P. invariant g P"
  shows
  "equiv_valid_2 I A A \<top>\<top> \<top> \<top> f g"
  apply(clarsimp simp: equiv_valid_2_def)
  apply(drule state_unchanged[OF inv])
  apply(drule state_unchanged[OF inv'])
  by simp

lemma mapM_x_ev2_r_invisible:
  assumes
    mam: "\<And> ptr. modifies_at_most aag (L ptr) \<top> ((f::word32 \<Rightarrow> (unit,det_ext) s_monad) ptr)"
  assumes
    inv: "\<And> P. invariant g P"
  shows
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
   op = \<top>
   (K (\<forall>x. x \<in> set list \<longrightarrow>  labels_are_invisible aag l (L x)))
   g (mapM_x f list)"
  apply(induct list)
   apply(simp add: mapM_x_Nil)
   apply(rule ev2_inv[OF inv])
   apply wp
   apply (simp add: mapM_x_Cons)
  apply (subst bind_return_unit2)
  apply (rule_tac R'="op =" and P'="\<lambda> s. labels_are_invisible aag l (L a)" in equiv_valid_2_bind_pre)
       apply simp
      apply(rule gen_asm_ev2_r)
      apply(rule equiv_valid_2_guard_imp[OF ev2_invisible], assumption+)
          apply(rule_tac P="\<top>" in modifies_at_mostI)
          apply(wp | simp)+
         apply(rule mam)
        apply(wp | simp)+
  done

(* MOVE *)
lemma ev2_sym:
  assumes
   symI: "\<And> x y. I x y \<Longrightarrow> I y x"
  assumes
   symA: "\<And> x y. A x y \<Longrightarrow> A y x"
  assumes
   symB: "\<And> x y. B x y \<Longrightarrow> B y x"
  assumes
   symR: "\<And> x y. R x y \<Longrightarrow> R y x"
  shows
  "equiv_valid_2 I A B R P' P f' f \<Longrightarrow>
   equiv_valid_2 I A B R P P' f f'"
  apply(clarsimp simp: equiv_valid_2_def)
  apply(blast intro: symA symB symI symR)
  done

lemma mapM_x_ev2_l_invisible:
  assumes
    mam: "\<And> ptr. modifies_at_most aag (L ptr) \<top> ((f::word32 \<Rightarrow> (unit,det_ext) s_monad) ptr)"
  assumes
    inv: "\<And> P. invariant g P"
  shows
  "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
   op =
   (K (\<forall>x. x \<in> set list \<longrightarrow> labels_are_invisible aag l (L x)))
   \<top>
   (mapM_x f list) g"
  apply(rule ev2_sym[OF reads_equiv_sym affects_equiv_sym affects_equiv_sym])
      apply(simp_all)[4]
  apply(rule mapM_x_ev2_r_invisible[OF mam inv])
  done


lemma set_endpoint_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag epptr \<in> L)\<rbrace>
   set_endpoint epptr ep
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_endpoint_def
  apply (wp set_object_equiv_but_for_labels get_object_wp)
  apply (clarsimp simp: asid_pool_at_kheap split: kernel_object.splits simp: obj_at_def)
  done


lemma not_label_is_invisible:
  "(\<not> labels_are_invisible aag l {(pasObjectAbs aag x)}) =
    (aag_can_read aag x \<or> aag_can_affect aag l x)"
  apply(simp add: labels_are_invisible_def)
  done

lemma label_is_invisible:
  "(labels_are_invisible aag l {(pasObjectAbs aag x)}) =
   (\<not> (aag_can_read aag x \<or> aag_can_affect aag l x))"
  apply(simp add: labels_are_invisible_def)
  done

lemma op_eq_unit_taut: "(op =) = (\<lambda> (_:: unit) _. True)"
  apply (rule ext | simp)+
  done

lemma ev2_symmetric: "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) op = P P f f' \<Longrightarrow> equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) op = P P f' f"
  apply (clarsimp simp add: equiv_valid_2_def)
  apply (drule_tac x=t in spec)
  apply (drule_tac x=s in spec)
  apply (fastforce elim: affects_equiv_sym reads_equiv_sym)
  done

lemma reads_respects_ethread_get: "reads_respects aag l (\<lambda>_. is_subject aag thread) (ethread_get f thread)"
  apply (simp add: ethread_get_def)
  apply wp
  apply (drule aag_can_read_self)
  apply (fastforce simp add: reads_equiv_def2 get_etcb_def
                             equiv_for_def states_equiv_for_def)
  done

lemma set_tcb_queue_reads_respects[wp]:
  "reads_respects aag l (\<lambda>_. True) (set_tcb_queue d prio queue)"
  unfolding equiv_valid_def2 equiv_valid_2_def
  apply (clarsimp simp: set_tcb_queue_def bind_def modify_def put_def get_def)
  apply (rule conjI | rule affects_equiv_ready_queues_update reads_equiv_ready_queues_update, assumption | fastforce elim: affects_equivE reads_equivE simp: equiv_for_def)+
  done

lemma aag_can_read_self'[simp]:
  "aag_can_read_label aag (pasSubject aag)"
  by (fastforce intro: reads_lrefl)

lemma gets_apply_ready_queues_reads_respects:
  "reads_respects aag l (\<lambda>_. pasDomainAbs aag d = pasSubject aag) (gets_apply ready_queues d)"
  apply (rule gets_apply_ev')
  apply (fastforce elim: reads_equivE simp: equiv_for_def)
  done

(*
lemma set_tcb_queue_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasDomainAbs aag d \<in> L)\<rbrace>
   set_tcb_queue d prio queue
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  apply (simp add: set_tcb_queue_def modify_def)
  apply wp
  apply (force simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)
  done
*)

lemma set_tcb_queue_modifies_at_most:
  "modifies_at_most aag L (\<lambda>s. L = {pasDomainAbs aag d}) (set_tcb_queue d prio queue)"
  apply (rule modifies_at_mostI)
  apply (simp add: set_tcb_queue_def modify_def, wp)
  apply (force simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)
  done

(*
lemma set_tcb_queue_modifies_at_most:
  "modifies_at_most aag {pasObjectAbs aag thread} (\<lambda>s. True) (set_tcb_queue d prio queue)"
  apply (rule modifies_at_mostI)
  apply (simp add: set_tcb_queue_def modify_def, wp)
  apply (force simp: equiv_but_for_labels_def states_equiv_for_def equiv_for_def equiv_asids_def equiv_asid_def)
  done
*)

(* FIXME: move *)
lemma equiv_valid_rv_trivial':
  assumes inv: "\<And> P. \<lbrace> P \<rbrace> f \<lbrace> \<lambda>_. P \<rbrace>"
  shows "equiv_valid_rv_inv I A \<top>\<top> Q f"
  by(auto simp: equiv_valid_2_def dest: state_unchanged[OF inv])

lemma tcb_sched_action_reads_respects:
  "reads_respects aag l (pas_refined aag) (tcb_sched_action action thread)"
  apply (simp add: tcb_sched_action_def get_tcb_queue_def)
  apply (subst gets_apply)
  apply (case_tac "aag_can_read aag thread \<or> aag_can_affect aag l thread")
   apply (simp add: ethread_get_def)
   apply wp
         apply (rule_tac Q="\<lambda>s. pasObjectAbs aag thread = pasDomainAbs aag (tcb_domain rv)" in equiv_valid_guard_imp)
          apply (wp gets_apply_ev')
          apply (fastforce elim: reads_equivE affects_equivE equiv_forE)
         apply (wp | simp)+
   apply (intro conjI impI allI
         | fastforce simp: get_etcb_def elim: reads_equivE affects_equivE equiv_forE)+
   apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def split: option.splits)
   apply (erule_tac x="(thread, tcb_domain y)" in ballE, force)
   apply (force intro: domtcbs simp: get_etcb_def)

  apply (simp add: equiv_valid_def2 ethread_get_def)
  apply (rule equiv_valid_rv_bind)
    apply (wp equiv_valid_rv_trivial', simp)
   apply (rule equiv_valid_2_bind)
      prefer 2
      apply (wp equiv_valid_rv_trivial, simp)
     apply (rule equiv_valid_2_bind)
        apply (rule_tac P="\<top>" and P'="\<top>" and L="{pasObjectAbs aag thread}" and L'="{pasObjectAbs aag thread}" in ev2_invisible)
            apply (blast | simp add: labels_are_invisible_def)+
          apply (rule set_tcb_queue_modifies_at_most)
         apply (rule set_tcb_queue_modifies_at_most)
        apply (simp | wp)+
       apply (clarsimp simp: equiv_valid_2_def gets_apply_def get_def bind_def return_def labels_are_invisible_def)
      apply wp+
  apply clarsimp
  apply (rule conjI, force)
  apply (clarsimp simp: pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (erule_tac x="(thread, tcb_domain y)" in ballE)
   apply force
  apply (force intro: domtcbs simp: get_etcb_def)
  done

lemma reschedule_required_reads_respects[wp]:
  "reads_respects aag l (pas_refined aag) reschedule_required"
  apply (simp add: reschedule_required_def | wp tcb_sched_action_reads_respects | wpc)+
  apply (simp add: reads_equiv_def)
  done

lemma possible_switch_to_reads_respects:
  "reads_respects aag l (pas_refined aag and pas_cur_domain aag and (\<lambda>s. is_subject aag (cur_thread s))) (possible_switch_to tptr on_same_prio)"
  apply (simp add: possible_switch_to_def ethread_get_def)
  apply (case_tac "aag_can_read aag tptr \<or> aag_can_affect aag l tptr")
   apply ((wp static_imp_wp tcb_sched_action_reads_respects | wpc | simp add: fun_app_def)+)[1]
   apply (clarsimp simp: get_etcb_def)
   apply ((intro conjI impI allI | elim aag_can_read_self reads_equivE affects_equivE equiv_forE conjE disjE | force)+)[1]
  apply clarsimp
  apply wp_once
     apply wp_once
       apply wp_once
         apply (simp add: equiv_valid_def2)
         apply (rule_tac W="\<top>\<top>" and Q="\<lambda>tcb. pas_refined aag and K (tcb_domain tcb \<noteq> rva)" in equiv_valid_rv_bind)
           prefer 3
           apply wp
          apply (clarsimp simp: gets_the_def get_etcb_def equiv_valid_2_def gets_def bind_def assert_opt_def get_def fail_def return_def split: option.splits)
         apply (rule gen_asm_ev2')
         apply simp
         apply (rule equiv_valid_rv_bind[where W="\<top>\<top>" and Q="\<lambda>rv. pas_refined aag"])
           apply (clarsimp simp: gets_the_def get_etcb_def equiv_valid_2_def gets_def bind_def assert_opt_def get_def fail_def return_def split: option.splits)
          apply (simp add: equiv_valid_def2[symmetric])
          apply (wp tcb_sched_action_reads_respects)
          apply (simp add: reads_equiv_def)
         apply (wp | simp)+
  apply (clarsimp)
  apply (rule conjI, force simp: get_etcb_def elim: equiv_forE reads_equivE aag_can_read_self)+
  apply (clarsimp simp: get_etcb_def pas_refined_def tcb_domain_map_wellformed_aux_def)
  apply (frule_tac x="(tptr, tcb_domain ya)" in bspec, force intro: domtcbs)
  apply (erule notE, rule aag_can_read_self)
  apply simp
  done

lemma switch_if_required_to_reads_respects:
  "reads_respects aag l (pas_refined aag and pas_cur_domain aag and (\<lambda>s. is_subject aag (cur_thread s))) (switch_if_required_to a)"
  apply (simp add: switch_if_required_to_def possible_switch_to_reads_respects)
  done

lemma attempt_switch_to_reads_respects:
  "reads_respects aag l (pas_refined aag and pas_cur_domain aag and (\<lambda>s. is_subject aag (cur_thread s))) (attempt_switch_to a)"
  apply (simp add: attempt_switch_to_def possible_switch_to_reads_respects)
  done

crunch sched_act[wp]: set_endpoint "\<lambda>s. P (scheduler_action s)"
  (wp: crunch_wps)

lemma set_endpoint_valid_sched_action[wp]:
  "\<lbrace>valid_sched_action\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>_. valid_sched_action\<rbrace>"
  by (wp valid_sched_action_lift)


lemma cancel_all_ipc_reads_respects:
  "reads_respects aag l (pas_refined aag and K (is_subject aag epptr)) (cancel_all_ipc epptr)"
  unfolding cancel_all_ipc_def fun_app_def
  apply (wp mapM_x_ev'' tcb_sched_action_reads_respects set_thread_state_runnable_reads_respects set_thread_state_pas_refined hoare_vcg_ball_lift mapM_x_wp set_thread_state_runnable_valid_sched_action set_endpoint_reads_respects get_ep_queue_reads_respects get_epq_SendEP_ret get_epq_RecvEP_ret get_endpoint_reads_respects get_endpoint_wp | wpc | clarsimp simp: ball_conj_distrib | rule subset_refl | wp_once hoare_drop_imps | assumption)+
  done
(*
lemma cancel_all_ipc_reads_respects:
  "reads_respects aag l (pas_refined aag and pas_cur_domain aag and valid_sched and valid_objs and (sym_refs \<circ> state_refs_of) and K ((pasSubject aag, Reset, pasObjectAbs aag epptr) \<in> pasPolicy aag)) (cancel_all_ipc epptr)"
  apply(subst (asm) label_is_invisible[symmetric])
  apply(clarsimp simp: equiv_valid_def2 simp del: K_def)
  apply(rule_tac W="\<lambda> ep ep'. (\<not> ep_queue_invisible aag l ep \<or> \<not> ep_queue_invisible aag l ep') \<longrightarrow> ep = ep'" and Q="\<lambda> rv s. pas_refined aag s" in equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp, rule get_endpoint_revrv, simp)
   apply(case_tac "rv = rv'")
    apply(clarsimp)
    apply(fold equiv_valid_def2)
    apply(rule equiv_valid_guard_imp)
     apply((wp mapM_x_ev'' set_thread_state_runnable_reads_respects set_endpoint_reads_respects get_ep_queue_reads_respects get_epq_SendEP_ret get_epq_RecvEP_ret get_endpoint_reads_respects get_endpoint_wp reschedule_required_reads_respects tcb_sched_action_reads_respects set_thread_state_pas_refined mapM_x_wp | wpc | simp | rule subset_refl | wp_once hoare_drop_imps)+)[2]
   apply clarsimp+
   apply(clarsimp  split: endpoint.splits)
   apply(intro allI impI conjI)
           apply(fastforce intro: return_ev2)
          apply(clarsimp)
          apply(subst bind_return_unit)
          apply(rule_tac Q="\<top>\<top>" and Q'="\<lambda> rv s. rv = list" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
               apply(rule gen_asm_ev2_r)
               apply(subst bind_return_unit)
               apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
                    apply (subst bind_return_unit)
                    apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top>  and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
                         apply (simp add: op_eq_unit_taut)
                         apply (rule equiv_valid_2_unobservable)
                            apply wp
                        apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_r_invisible])
                           apply(rule modifies_at_mostI)
                           apply(wp set_thread_state_equiv_but_for  | simp add: labels_are_invisible_def)+
                   apply(rule_tac L="{pasObjectAbs aag epptr}" and L'="{pasObjectAbs aag epptr}" in ev2_invisible)
                       apply (simp add: labels_are_invisible_def)+
                     apply(rule_tac P="\<top>" in modifies_at_mostI | wp set_endpoint_equiv_but_for_labels | simp)+
              apply(rule ev2_inv | wp | simp add: get_ep_queue_def)+
         apply(clarsimp)
         apply(subst bind_return_unit)
         apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
              apply(subst bind_return_unit)
              apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="op =" in equiv_valid_2_bind_pre)
                   apply (simp add: op_eq_unit_taut)
                   apply (rule equiv_valid_2_unobservable)
                      apply wp
                  apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_r_invisible])
                     apply(rule modifies_at_mostI)
                     apply(wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
             apply(rule_tac L="{pasObjectAbs aag epptr}" and L'="{pasObjectAbs aag epptr}" in ev2_invisible)
                 apply (simp add: labels_are_invisible_def)+
               apply(rule_tac P="\<top>" in modifies_at_mostI | wp set_endpoint_equiv_but_for_labels | simp)+
        apply clarsimp
        apply(subst bind_return_unit[where f="return ()"])
        apply(rule_tac Q="\<lambda> rv s. rv = list" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
             apply(rule gen_asm_ev2_l)
             apply(subst bind_return_unit[where f="return ()"])
             apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
                  apply(subst bind_return_unit[where f="return ()"])
                  apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="op =" in equiv_valid_2_bind_pre)
                       apply (simp add: op_eq_unit_taut)
                       apply (rule equiv_valid_2_unobservable)
                          apply wp
                      apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_l_invisible])
                         apply(rule modifies_at_mostI)
                         apply(wp set_thread_state_equiv_but_for set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
                 apply(rule_tac L="{pasObjectAbs aag epptr}" and L'="{pasObjectAbs aag epptr}" in ev2_invisible)
                     apply (simp add: labels_are_invisible_def)+
                   apply(rule_tac P="\<top>" in modifies_at_mostI | wp set_endpoint_equiv_but_for_labels | simp | wp_once hoare_drop_imps)+
            apply(rule ev2_inv | wp | simp add: get_ep_queue_def)+
       apply(clarsimp)
       apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
            apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
                 apply (simp add: op_eq_unit_taut)
                 apply (rule equiv_valid_2_unobservable)
                    apply wp
                apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_invisible])
                   apply(rule modifies_at_mostI |
                         wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
           apply(rule_tac L="{pasObjectAbs aag epptr}" and L'="{pasObjectAbs aag epptr}" in ev2_invisible)
               apply (simp add: labels_are_invisible_def)+
             apply(rule_tac P="\<top>" in modifies_at_mostI | simp | wp set_endpoint_equiv_but_for_labels | wp_once hoare_drop_imps)+
      apply clarsimp
      apply(rule_tac Q="\<lambda> rv s. rv = list" and Q'="\<lambda> rv s. rv = lista" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
           apply(rule gen_asm_ev2_l)
           apply(rule gen_asm_ev2_r)
           apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
                apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
                     apply (simp add: equiv_valid_def2[symmetric])
                     apply (rule reads_respects_unobservable_unit_return)
                      apply wp
                    apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_invisible])
                       apply(rule modifies_at_mostI |
                             wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
               apply(rule_tac L="{pasObjectAbs aag epptr}" and L'="{pasObjectAbs aag epptr}" in ev2_invisible)
                   apply (simp add: labels_are_invisible_def)+
                 apply(rule_tac P="\<top>" in modifies_at_mostI | wp set_endpoint_equiv_but_for_labels | simp | wp_once hoare_drop_imps)+
          apply(rule ev2_inv | wp | simp add: get_ep_queue_def)+
     apply(clarsimp)
     apply(subst bind_return_unit[where f="return ()"])
     apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
          apply(subst bind_return_unit[where f="return ()"])
          apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
               apply (simp add: op_eq_unit_taut)
               apply (rule equiv_valid_2_unobservable)
                  apply (wp)
              apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_l_invisible])
                 apply(rule modifies_at_mostI)
                 apply(wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
         apply(rule_tac L="{pasObjectAbs aag epptr}" and L'="{pasObjectAbs aag epptr}" in ev2_invisible)
             apply (simp add: labels_are_invisible_def)+
           apply(rule_tac P="\<top>" in modifies_at_mostI | wp set_endpoint_equiv_but_for_labels | simp | wp_once hoare_drop_imps)+
    apply clarsimp
    apply(rule_tac Q="\<lambda> rv s. rv = list" and Q'="\<lambda> rv s. rv = lista" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
         apply(rule gen_asm_ev2_l)
         apply(rule gen_asm_ev2_r)
         apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
              apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
                   apply (simp add: op_eq_unit_taut)
                   apply (rule equiv_valid_2_unobservable)
                      apply wp
                  apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_invisible])
                     apply(rule modifies_at_mostI |
                           wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
             apply(rule_tac L="{pasObjectAbs aag epptr}" and L'="{pasObjectAbs aag epptr}" in ev2_invisible)
                 apply (simp add: labels_are_invisible_def)+
               apply(rule_tac P="\<top>" in modifies_at_mostI | wp set_endpoint_equiv_but_for_labels | simp | wp_once hoare_drop_imps)+
        apply(rule ev2_inv | wp | simp add: get_ep_queue_def)+
   apply(clarsimp)
   apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
        apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
             apply (simp add: op_eq_unit_taut)
             apply (rule equiv_valid_2_unobservable)
                apply wp
            apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_invisible])
               apply(rule modifies_at_mostI |
                     wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
       apply(rule_tac L="{pasObjectAbs aag epptr}" and L'="{pasObjectAbs aag epptr}" in ev2_invisible)
           apply (simp add: labels_are_invisible_def)+
         apply(rule_tac P="\<top>" in modifies_at_mostI | simp | wp set_endpoint_equiv_but_for_labels | wp_once hoare_drop_imps)+
  done
*)

lemma set_notification_reads_respects:
  "reads_respects aag l \<top> (set_notification ptr ntfn)"
  unfolding set_notification_def
  apply(simp add: equiv_valid_def2)
  apply(rule equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp)
     apply(rule get_object_revrv)
    apply(simp, simp)
   apply(rule equiv_valid_2_bind)
      apply(subst equiv_valid_def2[symmetric])
      apply(rule set_object_reads_respects)
     apply(rule assert_ev2)
     apply(simp)
    apply(rule assert_wp)+
  apply(simp)
  apply (rule get_object_inv)
  done

lemma get_notification_reads_respects:
  "reads_respects aag l (K (aag_can_read aag ptr \<or> aag_can_affect aag l ptr)) (get_notification ptr)"
  unfolding get_notification_def
  apply(wp get_object_reads_respects hoare_vcg_all_lift | wpc | simp)+
  done


fun ntfn_queue_invisible where
  "ntfn_queue_invisible aag l (WaitingNtfn list) = labels_are_invisible aag l ((pasObjectAbs aag) ` (set list))" |
  "ntfn_queue_invisible aag l _ = True"


lemma not_ntfn_queue_invisible:
  "\<lbrakk>\<not> ntfn_queue_invisible aag l eplist; eplist = WaitingNtfn list\<rbrakk>  \<Longrightarrow>
  (\<exists> t \<in> set list. aag_can_read aag t \<or> aag_can_affect aag l t)"
  apply(auto simp: labels_are_invisible_def)
  done

lemma ntfn_queues_are_invisible_or_ntfns_are_equal':
  "\<lbrakk>(pasSubject aag, Reset, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag;
    ko_at (Notification ntfn) ntfnptr s;
    ko_at (Notification ntfn') ntfnptr s';
    reads_equiv aag s s'; affects_equiv aag l s s';
    valid_objs s; sym_refs (state_refs_of s); valid_objs s';
    sym_refs (state_refs_of s'); pas_refined aag s; pas_refined aag s'\<rbrakk> \<Longrightarrow>
  \<not> ntfn_queue_invisible aag l (ntfn_obj ntfn) \<longrightarrow> ntfn_obj ntfn = ntfn_obj ntfn'"
  apply(rule impI)
  apply(case_tac "\<exists> list. ntfn_obj ntfn = WaitingNtfn list")
   apply(erule exE)
   apply(drule (1) not_ntfn_queue_invisible)
   apply clarsimp
   apply(erule disjE)
    apply(drule_tac auth="Receive" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
        apply blast
       apply(erule pas_refined_mem[rotated])
       apply(rule sta_ts)
       apply(drule_tac P="receive_blocked_on ntfnptr" and s=s and t=t in ntfn_queued_st_tcb_at')
           apply(simp)+
       apply(simp add: thread_states_def split: option.splits)
       apply(clarsimp simp: tcb_states_of_state_def st_tcb_def2 receive_blocked_on_tcb_st_to_auth)
      apply blast
     apply assumption
    apply(fastforce dest: reads_affects_equiv_kheap_eq simp: obj_at_def)
   apply(drule_tac auth="Receive" and t="pasObjectAbs aag t" in reads_read_queued_thread_read_ep)
       apply blast
      apply(erule pas_refined_mem[rotated])
      apply(rule sta_ts)
      apply(drule_tac P="receive_blocked_on ntfnptr" and s=s and t=t in ntfn_queued_st_tcb_at')
          apply(simp)+
      apply(simp add: thread_states_def split: option.splits)
      apply(clarsimp simp: tcb_states_of_state_def st_tcb_def2 receive_blocked_on_tcb_st_to_auth)
     apply blast
    apply(erule conjE, assumption)
   apply(drule_tac x=ntfnptr in reads_affects_equiv_kheap_eq, simp+)
   apply(fastforce simp: obj_at_def)
  apply(case_tac "ntfn_obj ntfn", auto)
  done

lemma set_notification_equiv_but_for_labels:
  "\<lbrace>equiv_but_for_labels aag L st and K (pasObjectAbs aag ntfnptr \<in> L)\<rbrace>
   set_notification ntfnptr ntfn
   \<lbrace>\<lambda>_. equiv_but_for_labels aag L st\<rbrace>"
  unfolding set_notification_def
  apply (wp set_object_equiv_but_for_labels get_object_wp)
  apply (clarsimp simp: asid_pool_at_kheap split: kernel_object.splits simp: obj_at_def)
  done

lemma cancel_all_signals_reads_respects:
  "reads_respects aag l (pas_refined aag and K (is_subject aag ntfnptr)) (cancel_all_signals ntfnptr)"
  unfolding cancel_all_signals_def
  apply ((wp mapM_x_ev'' tcb_sched_action_reads_respects set_thread_state_runnable_reads_respects set_thread_state_pas_refined hoare_vcg_ball_lift mapM_x_wp set_thread_state_runnable_valid_sched_action set_notification_reads_respects get_ep_queue_reads_respects get_epq_SendEP_ret get_epq_RecvEP_ret get_notification_reads_respects get_endpoint_wp set_notification_pas_refined hoare_vcg_all_lift | wpc | clarsimp simp: ball_conj_distrib | rule subset_refl | wp_once hoare_drop_imps | simp)+)[1]
  done
(*
  apply (wp hoare_vcg_all_lift)
  apply(case_tac "aag_can_read aag ntfnptr \<or> aag_can_affect aag l ntfnptr")
   apply((wp mapM_x_ev' set_thread_state_reads_respects set_notification_reads_respects
             get_notification_reads_respects hoare_vcg_all_lift

         | wpc | simp)+)[1]
    apply (wp hoare_drop_imps)
   apply simp
   apply force
  apply(clarsimp simp: equiv_valid_def2 simp del: K_def)
  apply(rule_tac W="\<lambda> ntfn ntfn'. (\<not> ntfn_queue_invisible aag l ntfn \<or> \<not> ntfn_queue_invisible aag l ntfn') \<longrightarrow> ntfn = ntfn'" and Q="\<top>\<top>" in equiv_valid_rv_bind)
    apply(rule get_notification_revrv)
   apply(case_tac "rv = rv'")
    apply(clarsimp)
    apply(fold equiv_valid_def2)
    apply(rule equiv_valid_guard_imp)
     apply((wp mapM_x_ev' set_thread_state_reads_respects set_notification_reads_respects
               get_notification_reads_respects hoare_vcg_all_lift
           | wpc | simp)+)[1]
    apply clarsimp+
    apply force
   apply(clarsimp  split: notification.splits)
   apply(intro allI impI conjI)
           apply(fastforce intro: return_ev2)
          apply(subst bind_return_unit[where f="return ()"])
          apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
               apply(subst bind_return_unit[where f="return ()"])
               apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
                    apply (simp add: op_eq_unit_taut)
                    apply (rule equiv_valid_2_unobservable)
                       apply wp
                   apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_r_invisible])
                      apply(rule modifies_at_mostI |
                            wp set_thread_state_equiv_but_for  | simp add: labels_are_invisible_def)+
              apply(rule ev2_invisible_ntfn)
                  apply (simp add: labels_are_invisible_def)+
                apply(rule_tac P="\<top>" in modifies_at_mostI | wp set_notification_equiv_but_for_labels | simp  | wp_once hoare_drop_imps)+
         apply(fastforce intro: return_ev2)
        apply(subst bind_return_unit[where f="return ()"])
        apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
             apply(subst bind_return_unit[where f="return ()"])
             apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
                  apply (simp add: op_eq_unit_taut)
                  apply (rule equiv_valid_2_unobservable)
                     apply wp
                 apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_l_invisible])
                    apply(rule modifies_at_mostI |
                          wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
            apply(rule ev2_invisible_ntfn)
                apply (simp add: labels_are_invisible_def)+
              apply((rule_tac P="\<top>" in modifies_at_mostI | wp set_notification_equiv_but_for_labels | simp | wp_once hoare_drop_imps)+)[7]
       apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
            apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
                 apply (simp add: op_eq_unit_taut)
                 apply (rule equiv_valid_2_unobservable)
                    apply wp
                apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_invisible])
                   apply(rule modifies_at_mostI |
                         wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
           apply(rule ev2_invisible_ntfn)
               apply (simp add: labels_are_invisible_def)+
             apply((rule_tac P="\<top>" in modifies_at_mostI | wp set_notification_equiv_but_for_labels | simp | wp_once hoare_drop_imps)+)[7]
      apply(subst bind_return_unit[where f="return ()"])
      apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
           apply(subst bind_return_unit[where f="return ()"])
           apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
                apply (simp add: op_eq_unit_taut)
                apply (rule equiv_valid_2_unobservable)
                   apply wp
               apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_l_invisible])
                  apply(rule modifies_at_mostI |
                        wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
          apply(rule ev2_invisible_ntfn)
              apply (simp add: labels_are_invisible_def)+
            apply((rule_tac P="\<top>" in modifies_at_mostI | wp set_notification_equiv_but_for_labels | simp | wp_once hoare_drop_imps)+)[7]
     apply(fastforce intro: return_ev2)
    apply(subst bind_return_unit[where f="return ()"])
    apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and R'="\<top>\<top>" in equiv_valid_2_bind_pre)
         apply(subst bind_return_unit[where f="return ()"])
         apply(rule_tac Q="\<top>\<top>" and Q'="\<top>\<top>" and P=\<top> and P'=\<top> and R'="op =" in equiv_valid_2_bind_pre)
              apply (simp add: op_eq_unit_taut)
              apply (rule equiv_valid_2_unobservable)
                 apply wp
             apply(rule equiv_valid_2_guard_imp[OF mapM_x_ev2_r_invisible])
                apply(rule modifies_at_mostI |
                      wp set_thread_state_equiv_but_for | simp add: labels_are_invisible_def)+
        apply(rule ev2_invisible_ntfn)
            apply (simp add: labels_are_invisible_def)+
          apply((rule_tac P="\<top>" in modifies_at_mostI | wp set_notification_equiv_but_for_labels | simp  | wp_once hoare_drop_imps)+)[7]
   apply(fastforce intro: return_ev2)
  apply wp
  done
*)

lemma get_bound_notification_reads_respects':
  "reads_respects aag l (K(is_subject aag thread)) (get_bound_notification thread)"
  unfolding get_bound_notification_def thread_get_def
  apply (wp | simp)+
  apply clarify
  apply (rule requiv_get_tcb_eq)
  apply simp+
  done

lemma reads_affects_equiv_get_tcb_eq:
  "\<lbrakk>aag_can_read aag thread \<or> aag_can_affect aag l thread;
    reads_equiv aag s t; affects_equiv aag l s t\<rbrakk> \<Longrightarrow>
   get_tcb thread s = get_tcb thread t"
  apply (fastforce simp: get_tcb_def split: kernel_object.splits option.splits simp: reads_affects_equiv_kheap_eq)
  done

lemma thread_get_reads_respects:
  "reads_respects aag l (K (aag_can_read aag thread \<or> aag_can_affect aag l thread)) (thread_get f thread)"
  unfolding thread_get_def fun_app_def
  apply (wp gets_the_ev)
  apply (auto intro: reads_affects_equiv_get_tcb_eq)
  done

lemma get_bound_notification_reads_respects:
  "reads_respects aag l (\<lambda> s. aag_can_read aag thread \<or> aag_can_affect aag l thread) (get_bound_notification thread)"
  unfolding get_bound_notification_def
  apply(rule equiv_valid_guard_imp)
   apply(wp thread_get_reads_respects | simp)+
  done


lemma bound_tcb_at_implies_read:
  "\<lbrakk>pas_refined aag s; is_subject aag t; bound_tcb_at (op = (Some x)) t s\<rbrakk>
     \<Longrightarrow> aag_can_read_label aag (pasObjectAbs aag x)"
  apply (frule bound_tcb_at_implies_receive, simp)
  apply clarsimp
apply (frule_tac l="pasSubject aag" and auth=Receive in reads_ep, simp)
apply (auto simp: aag_can_read_read)
  done

lemma bound_tcb_at_eq:
  "\<lbrakk>sym_refs (state_refs_of s); valid_objs s; kheap s ntfnptr = Some (Notification ntfn);
    ntfn_bound_tcb ntfn = Some tcbptr; bound_tcb_at (op = (Some ntfnptr')) tcbptr s\<rbrakk>
    \<Longrightarrow> ntfnptr = ntfnptr'"
    apply (drule_tac x=ntfnptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def)
  apply (auto simp: pred_tcb_at_def obj_at_def valid_obj_def valid_ntfn_def is_tcb
                    state_refs_of_def refs_of_rev
          simp del: refs_of_simps
             elim!: valid_objsE)
  done

lemma unbind_maybe_notification_reads_respects:
  "reads_respects aag l 
     (pas_refined aag and invs and K (is_subject aag ntfnptr))
     (unbind_maybe_notification ntfnptr)"
  apply (clarsimp simp: unbind_maybe_notification_def)
apply wp
  apply (case_tac "ntfn_bound_tcb rv")
   apply (clarsimp, wp)[1] 
  -- "interesting case, ntfn is bound"
  apply (clarsimp)
   apply ((wp set_bound_notification_none_reads_respects set_notification_reads_respects 
              get_notification_reads_respects
          | wpc
          | simp)+)
  done

lemma unbind_notification_is_subj_reads_respects:
  "reads_respects aag l (pas_refined aag and invs and K (is_subject aag t))
       (unbind_notification t)"
  apply (clarsimp simp: unbind_notification_def)
  apply (wp set_bound_notification_owned_reads_respects set_notification_reads_respects 
            get_notification_reads_respects get_bound_notification_reads_respects
            gbn_wp[unfolded get_bound_notification_def, simplified]
       | wpc 
       | simp add: get_bound_notification_def)+
  apply (clarsimp)
  apply (rule bound_tcb_at_implies_read, auto)
  done

lemma fast_finalise_reads_respects:
  "reads_respects aag l (pas_refined aag and invs and K (pas_cap_cur_auth aag cap) and
    K (fin \<longrightarrow> (case cap of EndpointCap r badge rights \<Rightarrow> is_subject aag r |
                           NotificationCap r badge rights \<Rightarrow> is_subject aag r |
                            _ \<Rightarrow> True)))
  (fast_finalise cap fin)"
  apply(case_tac cap, simp_all)
  apply(wp equiv_valid_guard_imp[OF cancel_all_ipc_reads_respects]
           equiv_valid_guard_imp[OF cancel_all_signals_reads_respects]
           unbind_notification_is_subj_reads_respects
           unbind_maybe_notification_reads_respects
           get_notification_reads_respects get_ntfn_wp
      | simp add: when_def 
      | wpc
      | intro conjI impI
      | fastforce simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)+
  done

lemma cap_delete_one_reads_respects_f:
  "reads_respects_f aag l (silc_inv aag st and invs and pas_refined aag and K (is_subject aag (fst slot))) (cap_delete_one slot)"
  unfolding cap_delete_one_def fun_app_def
  apply(unfold unless_def when_def)
  apply(rule equiv_valid_guard_imp)
   apply(wp is_final_cap_reads_respects
            reads_respects_f[OF empty_slot_reads_respects, where st=st and aag=aag]
            reads_respects_f[OF fast_finalise_reads_respects, where st=st and aag=aag]
            empty_slot_silc_inv
        | simp | elim conjE)+
      apply (rule_tac Q="\<lambda>rva s.
             rva = is_final_cap' rv s \<and>
             cte_wp_at (op = rv) slot s \<and>
             silc_inv aag st s \<and>
             is_subject aag (fst slot) \<and> pasObjectAbs aag (fst slot) \<noteq> SilcLabel" in hoare_strengthen_post)
       apply wp
      apply (rule conjI)
       apply clarsimp
       apply (drule silc_inv)
       apply (erule_tac x=rv in allE, erule_tac x=slot in allE)
       apply simp
       apply (drule(1) intra_label_capD)
       apply (clarsimp simp: cap_points_to_label_def split: cap.splits)
      apply force
     apply(wp reads_respects_f[OF get_cap_rev, where st=st and aag=aag]
              get_cap_auth_wp[where aag=aag]
        | simp | elim conjE)+
  apply (auto simp: cte_wp_at_caps_of_state silc_inv_def)
  done

lemma get_blocking_object_reads_respects:
  "reads_respects aag l \<top>  (get_blocking_object state)"
  unfolding get_blocking_object_def
  apply(rule equiv_valid_guard_imp)
   apply(wp | wpc | simp)+
   done

fun tcb_st_to_auth' where
  "tcb_st_to_auth' (BlockedOnSend x xa) = SyncSend" |
  "tcb_st_to_auth' (BlockedOnReceive x) = Receive" |
  "tcb_st_to_auth' (BlockedOnNotification x) = Receive"




lemma owns_thread_blocked_reads_endpoint:
  "\<lbrakk>pas_refined aag s; invs s;
        st_tcb_at (\<lambda> y. y = state) tptr s;
        is_subject aag tptr;
        state = (BlockedOnReceive x) \<or> state = (BlockedOnSend x xb) \<or> state = BlockedOnNotification x\<rbrakk> \<Longrightarrow> aag_can_read aag x"
  apply(rule_tac auth="tcb_st_to_auth' state" in reads_ep)
   apply(drule sym, simp, rule pas_refined_mem)
    apply(rule_tac s=s in sta_ts)
    apply(clarsimp simp: thread_states_def split: option.splits simp: tcb_states_of_state_def st_tcb_at_def get_tcb_def obj_at_def)
    apply fastforce
   apply assumption
  apply(fastforce)
  done


lemma st_tcb_at_sym:
  "st_tcb_at (op = x) t s = st_tcb_at (\<lambda> y. y = x) t s"
  apply(auto simp: st_tcb_at_def obj_at_def)
  done

lemma blocked_cancel_ipc_reads_respects:
  "reads_respects aag l (pas_refined aag and invs and st_tcb_at (op = state) tptr and (\<lambda>_. (is_subject aag tptr)))
    (blocked_cancel_ipc state tptr)"
  unfolding blocked_cancel_ipc_def
  apply(wp set_thread_state_owned_reads_respects set_endpoint_reads_respects get_ep_queue_reads_respects get_endpoint_reads_respects get_blocking_object_reads_respects | simp add: get_blocking_object_def | wpc)+
  apply(fastforce intro: aag_can_read_self owns_thread_blocked_reads_endpoint simp: st_tcb_at_sym)
  done


  


lemma select_singleton_ev:
  "equiv_valid_inv I B (K (\<exists>a. A = {a})) (select A)"
  apply(fastforce simp: equiv_valid_def2 equiv_valid_2_def select_def)
  done


lemma thread_set_fault_pas_refined':
  "\<lbrace>pas_refined aag\<rbrace>
     thread_set (tcb_fault_update fault) thread
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply(wp thread_set_pas_refined_triv | simp)+
  done

lemma thread_set_fault_empty_invs:
  "\<lbrace>invs\<rbrace> thread_set (tcb_fault_update Map.empty) thread \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply(wp itr_wps(27) | simp)+
  done

lemma thread_set_reads_respects:
  "reads_respects aag l \<top> (thread_set x y)"
  unfolding thread_set_def fun_app_def
  apply(case_tac "aag_can_read aag y \<or> aag_can_affect aag l y")
   apply(wp set_object_reads_respects)
   apply(clarsimp, rule reads_affects_equiv_get_tcb_eq, simp+)[1]
  apply(simp add: equiv_valid_def2)
  apply(rule equiv_valid_rv_guard_imp)
   apply(rule_tac L="{pasObjectAbs aag y}" and L'="{pasObjectAbs aag y}" in ev2_invisible)
       apply (assumption | simp add: labels_are_invisible_def)+
     apply(rule modifies_at_mostI[where P="\<top>"] | wp set_object_equiv_but_for_labels | simp | (clarify, drule get_tcb_not_asid_pool_at))+
  done

lemma get_thread_state_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ref)) (get_thread_state ref)"
  unfolding get_thread_state_def
  by (rule thread_get_rev)

lemma get_irq_slot_reads_respects:
  "reads_respects aag l (K (is_subject_irq aag irq)) (get_irq_slot irq)"
  unfolding get_irq_slot_def
  apply(rule equiv_valid_guard_imp)
  apply(rule gets_ev)
  apply(simp add: reads_equiv_def states_equiv_for_def equiv_for_def
       affects_equiv_def)
   apply(drule aag_can_read_irq_self)
   apply(simp)
   done

lemma thread_set_tcb_at:
  "\<lbrace>\<lambda>s. Q s\<rbrace> thread_set x ptr \<lbrace>\<lambda>_ s. P s\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. tcb_at ptr s \<longrightarrow> Q s\<rbrace> thread_set x ptr \<lbrace>\<lambda>_ s. P s\<rbrace>"
  apply (rule use_spec(1))
  apply (case_tac "tcb_at ptr s")
  apply (clarsimp simp add: spec_valid_def valid_def)
  apply (simp add: spec_valid_def thread_set_def set_object_def[abs_def])
  apply wp
  apply clarsimp
  apply (clarsimp simp: get_tcb_def obj_at_def is_tcb_def split: option.splits Structures_A.kernel_object.splits)
  done

(* FIXME: Why was the [wp] attribute on this lemma clobbered by interpretation of the Arch locale? *)
lemmas [wp] = thread_set_fault_valid_global_refs

lemma reply_cancel_ipc_reads_respects_f:
  notes gets_ev[wp del]
  shows
  "reads_respects_f aag l (silc_inv aag st and pas_refined aag and invs and K (is_subject aag tptr)) (reply_cancel_ipc tptr)"
  apply (rule gen_asm_ev)
  unfolding reply_cancel_ipc_def
  apply (wp cap_delete_one_reads_respects_f[where st=st and aag=aag] select_singleton_ev select_inv select_wp
            reads_respects_f[OF get_cap_rev, where st=st and aag=aag] assert_wp
            reads_respects_f[OF thread_set_reads_respects, where st=st and aag=aag ]
            reads_respects_f[OF gets_descendants_of_revrv[folded equiv_valid_def2]]
        | simp add: when_def split del: if_split | elim conjE)+
   apply(rule_tac Q="\<lambda> rv s. silc_inv aag st s \<and> invs s \<and> pas_refined aag s \<and> is_subject aag tptr \<and>
                   (\<forall>x\<in>descendants_of (tptr, tcb_cnode_index 2) (cdt s).
                       is_subject aag (fst x))" in hoare_strengthen_post)
    apply(wp thread_set_tcb_fault_update_silc_inv hoare_vcg_imp_lift hoare_vcg_ball_lift
      thread_set_fault_empty_invs thread_set_fault_pas_refined' | wps | simp)+
  apply(fastforce dest: descendants_of_owned)
  done

lemma cancel_signal_reads_respects:
  "reads_respects aag l ((\<lambda>s. is_subject aag (cur_thread s)) and K (aag_can_read_label aag (pasObjectAbs aag ntfnptr) \<or>
        aag_can_affect aag l ntfnptr)) (cancel_signal threadptr ntfnptr)"
  unfolding cancel_signal_def
  apply(wp set_thread_state_reads_respects set_notification_reads_respects get_notification_reads_respects hoare_drop_imps | wpc | simp)+
  done

lemma cancel_signal_owned_reads_respects:
  "reads_respects aag l (K (is_subject aag threadptr) and K (aag_can_read_label aag (pasObjectAbs aag ntfnptr) \<or>
        aag_can_affect aag l ntfnptr)) (cancel_signal threadptr ntfnptr)"
  unfolding cancel_signal_def
  apply(wp set_thread_state_owned_reads_respects set_notification_reads_respects get_notification_reads_respects hoare_drop_imps | wpc | simp)+
  done

lemma cancel_ipc_reads_respects_f:
  "reads_respects_f aag l (silc_inv aag st and pas_refined aag and invs and
   (K (is_subject aag t)))
    (cancel_ipc t)"
  unfolding cancel_ipc_def
  apply(wp reads_respects_f[OF blocked_cancel_ipc_reads_respects, where st=st and Q="\<top>"]
           reply_cancel_ipc_reads_respects_f[where st=st]
           reads_respects_f[OF cancel_signal_owned_reads_respects, where st=st and Q="\<top>"]
           reads_respects_f[OF get_thread_state_rev, where st=st and Q="\<top>"] gts_wp
       | wpc | simp add: blocked_cancel_ipc_def | erule conjE)+
  apply(clarsimp simp: st_tcb_at_def obj_at_def)
  apply(rule owns_thread_blocked_reads_endpoint)
       apply (simp add: st_tcb_at_def obj_at_def | blast)+
  done


lemma suspend_reads_respects_f:
  "reads_respects_f aag l (silc_inv aag st and pas_refined aag and invs and
  (K (is_subject aag thread))) (suspend thread)"
  unfolding suspend_def
  apply(wp reads_respects_f[OF set_thread_state_owned_reads_respects, where st=st and Q="\<top>"] reads_respects_f[OF tcb_sched_action_reads_respects, where st=st and Q=\<top>] set_thread_state_pas_refined| simp)+
    apply(wp cancel_ipc_reads_respects_f[where st=st] cancel_ipc_silc_inv)+
  apply(simp)
  done

lemma prepare_thread_delete_reads_respects_f:
  "reads_respects_f aag l \<top> (prepare_thread_delete thread)"
  unfolding prepare_thread_delete_def
  by wp

lemma arch_finalise_cap_reads_respects:
  "reads_respects aag l (pas_refined aag and invs and
    cte_wp_at (op = (ArchObjectCap cap)) slot and
    K(pas_cap_cur_auth aag (ArchObjectCap cap))) (arch_finalise_cap cap is_final)"
  apply (rule gen_asm_ev)
  unfolding arch_finalise_cap_def
  apply (case_tac cap)
  apply simp
  apply (simp split: bool.splits)
  apply (intro impI conjI)
  apply (
         wp delete_asid_pool_reads_respects
            unmap_page_reads_respects
            unmap_page_table_reads_respects
            delete_asid_reads_respects

    | simp add: invs_psp_aligned invs_arch_objs invs_valid_objs valid_cap_def
    split: option.splits bool.splits | intro impI conjI allI |
    elim conjE |
    (rule aag_cap_auth_subject,assumption,assumption) |
    (drule cte_wp_valid_cap)
    )+
done

lemma deleting_irq_handler_reads_respects:
  "reads_respects_f aag l (silc_inv aag st and invs and pas_refined aag and K (is_subject_irq aag irq)) (deleting_irq_handler irq)"
  unfolding deleting_irq_handler_def
  apply(wp cap_delete_one_reads_respects_f
           reads_respects_f[OF get_irq_slot_reads_respects]
      | simp | blast)+
  done

lemma finalise_cap_reads_respects:
  "reads_respects_f aag l (silc_inv aag st and pas_refined aag and invs and cte_wp_at (op = cap) slot and K (pas_cap_cur_auth aag cap)
    and K (final \<longrightarrow> (case cap of EndpointCap r badge rights \<Rightarrow> is_subject aag r |
                           NotificationCap r badge rights \<Rightarrow> is_subject aag r |
                            _ \<Rightarrow> True))) (finalise_cap cap final)"
  apply(case_tac cap, simp_all split del: if_split)
            apply ((wp cancel_all_ipc_reads_respects cancel_all_signals_reads_respects
                      prepare_thread_delete_reads_respects_f
                      suspend_reads_respects_f[where st=st] deleting_irq_handler_reads_respects
                      unbind_notification_is_subj_reads_respects
                      unbind_maybe_notification_reads_respects
                      unbind_notification_invs unbind_maybe_notification_invs
                  | simp add: when_def split del: if_split
                         add: invs_valid_objs invs_sym_refs aag_cap_auth_def
                              cap_auth_conferred_def cap_rights_to_auth_def
                              cap_links_irq_def aag_has_auth_to_Control_eq_owns
                  | rule aag_Control_into_owns_irq
                  | clarsimp split del: if_split
                  | rule conjI
                  | wp_once reads_respects_f[where st=st] 
                  | blast
                  | clarsimp)+)[11]
  apply (rule equiv_valid_guard_imp)
  by ((wp arch_finalise_cap_reads_respects reads_respects_f[where st=st] arch_finalise_cap_silc_inv | simp | elim conjE)+)[2]


lemma cap_swap_for_delete_reads_respects:
  "reads_respects aag l (K (is_subject aag (fst slot1) \<and> is_subject aag (fst slot2))) (cap_swap_for_delete slot1 slot2)"
  unfolding cap_swap_for_delete_def
  apply(simp add: when_def)
  apply(rule conjI, rule impI)
   apply(rule equiv_valid_guard_imp)
    apply(wp cap_swap_reads_respects get_cap_rev)
   apply(simp)
  apply(rule impI, wp)
  done



lemma rec_del_pas_refined'':
  "\<lbrace>pas_refined aag and K (case call of
  CTEDeleteCall slot exposed \<Rightarrow> is_subject aag (fst slot) |
  FinaliseSlotCall slot exposed \<Rightarrow> is_subject aag (fst slot) |
  ReduceZombieCall cap slot exposed \<Rightarrow> is_subject aag (fst slot) \<and>
  is_subject aag (obj_ref_of cap))\<rbrace>
    rec_del call \<lbrace>K (pas_refined aag)\<rbrace>"
  apply(rule validE_cases_valid)
  apply(rule_tac E="K (pas_refined aag)" in hoare_post_impErr)
    apply(rule rec_del_pas_refined')
   apply(simp)+
   done




lemma owns_cnode_owns_obj_ref_of_child_cnodes_threads_and_zombies:
  "\<lbrakk>pas_refined aag s; is_subject aag (fst slot);
        cte_wp_at (op = cap) slot s; is_cnode_cap cap \<or> is_thread_cap cap \<or> is_zombie cap\<rbrakk>
       \<Longrightarrow> is_subject aag (obj_ref_of cap)"
  apply(frule (1) cap_cur_auth_caps_of_state[rotated])
  apply(simp add: cte_wp_at_caps_of_state)
  apply(clarsimp simp: aag_cap_auth_def)
  apply(case_tac cap, simp_all add: is_zombie_def)
    apply(drule_tac x=Control in bspec)
     apply (clarsimp simp: cap_auth_conferred_def)
    apply(erule (1) aag_Control_into_owns)
   apply(drule_tac x=Control in bspec)
    apply (clarsimp simp: cap_auth_conferred_def)
   apply(erule (1) aag_Control_into_owns)
  apply(drule_tac x=Control in bspec)
   apply (clarsimp simp: cap_auth_conferred_def)
  apply(erule (1) aag_Control_into_owns)
  done


lemma only_timer_irq_inv_irq_state_independent_A[simp, intro!]:
  "irq_state_independent_A (only_timer_irq_inv irq st)"
  apply (clarsimp simp: irq_state_independent_A_def only_timer_irq_inv_def only_timer_irq_def irq_is_recurring_def is_irq_at_def)
  done

lemma only_timer_irq_inv_wuc_update[simp]:
  "only_timer_irq_inv irq st (work_units_completed_update f s) = only_timer_irq_inv irq st s"
  by (clarsimp simp: only_timer_irq_inv_def only_timer_irq_def irq_is_recurring_def is_irq_at_def)

lemma rec_del_only_timer_irq:
  "\<lbrace>only_timer_irq_inv irq (st::det_ext state)\<rbrace> rec_del call \<lbrace>\<lambda>_. only_timer_irq irq\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (rule hoare_pre, rule only_timer_irq_pres)
    apply (rule hoare_pre, wp rec_del_irq_masks)
    apply (wp rec_del_domain_sep_inv | force)+
    done

lemma rec_del_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st::det_ext state)\<rbrace> rec_del call \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (rule hoare_wp_simps)
  apply (rule hoare_conjI)
   apply (wp rec_del_domain_sep_inv rec_del_only_timer_irq | force simp: only_timer_irq_inv_def)+
   done

lemma set_cap_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st::det_ext state) and K (domain_sep_inv_cap False cap)\<rbrace>
   set_cap cap slot \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres set_cap_domain_sep_inv | force)+
  done

lemma finalise_cap_only_timer_irq_inv:
  "\<lbrace>only_timer_irq_inv irq (st::det_ext state)\<rbrace>
   finalise_cap cap final \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply (simp add: only_timer_irq_inv_def)
  apply (wp only_timer_irq_pres | force)+
  done

lemma rec_del_spec_reads_respects_f:
  notes drop_spec_valid[wp_split del] drop_spec_validE[wp_split del]
        drop_spec_ev[wp_split del] rec_del.simps[simp del]
  shows
  "spec_reads_respects_f s aag l (silc_inv aag st and only_timer_irq_inv irq st' and einvs and simple_sched_action and pas_refined aag and
   valid_rec_del_call call and
   emptyable (slot_rdcall call) and
   (\<lambda>s. \<not> exposed_rdcall call \<longrightarrow>
        ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall call) s) and
    K (case call of
     CTEDeleteCall slot exposed \<Rightarrow> is_subject aag (fst slot) |
     FinaliseSlotCall slot exposed \<Rightarrow> is_subject aag (fst slot) |
     ReduceZombieCall cap slot exposed \<Rightarrow> is_subject aag (fst slot) \<and>
                                          is_subject aag (obj_ref_of cap)))
 (rec_del call)"
proof (induct s rule: rec_del.induct, simp_all only: rec_del_fails drop_spec_ev[OF fail_ev_pre])
  case (1 slot exposed s) show ?case
    apply(rule spec_equiv_valid_guard_imp)
     apply(simp add: rec_del.simps split_def when_def)
     apply(wp drop_spec_ev[OF returnOk_ev_pre] drop_spec_ev[OF liftE_ev] hoareE_TrueI
              reads_respects_f[OF empty_slot_reads_respects, where st=st] empty_slot_silc_inv)
      apply(rule "1.hyps")
     apply(rule_tac Q'="\<lambda>r s. silc_inv aag st s \<and> is_subject aag (fst slot)" in hoare_post_imp_R)
      apply((wp validE_validE_R'[OF rec_del_silc_inv] | fastforce simp: silc_inv_def)+)[2]
    apply simp
    done
next
  case (2 slot exposed s) show ?case
    apply(simp add: rec_del.simps)
    apply(rule spec_equiv_valid_guard_imp)
     apply(wp drop_spec_ev[OF returnOk_ev] drop_spec_ev[OF liftE_ev]
              set_cap_reads_respects_f "2.hyps" preemption_point_inv'
              drop_spec_ev[OF preemption_point_reads_respects_f[where st=st and st'=st']]
              validE_validE_R'[OF rec_del_silc_inv] rec_del_invs rec_del_respects(2)
              rec_del_only_timer_irq_inv
          | simp add: split_def split del: if_split | (rule irq_state_independent_A_conjI, simp)+)+
             apply(rule_tac Q'="\<lambda>rv s. emptyable (slot_rdcall (ReduceZombieCall (fst rvb) slot exposed)) s \<and> (\<not> exposed \<longrightarrow>
                   ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s) \<and>
                  is_subject aag (fst slot)" in hoare_post_imp_R)
              apply(wp rec_del_emptyable reduce_zombie_cap_to)
             apply simp
            apply(wp drop_spec_ev[OF liftE_ev] set_cap_reads_respects_f[where st=st] set_cap_silc_inv[where st=st] | simp)+
           apply(wp replace_cap_invs set_cap_cte_wp_at   set_cap_sets final_cap_same_objrefs
                    set_cap_cte_cap_wp_to  hoare_vcg_const_Ball_lift static_imp_wp
                    drop_spec_ev[OF liftE_ev] finalise_cap_reads_respects set_cap_silc_inv
                    set_cap_only_timer_irq_inv
                | simp add: cte_wp_at_eq_simp
                | erule finalise_cap_not_reply_master[simplified Inr_in_liftE_simp])+
         apply(rule hoare_strengthen_post)
          apply (rule_tac Q="\<lambda>fin s. silc_inv aag st s
                                 \<and> only_timer_irq_inv irq st' s
                                 \<and>
                       (\<not> cap_points_to_label aag (fst fin) (pasObjectAbs aag (fst slot)) \<longrightarrow>
                          (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps (fst fin) s \<and>
                                     pasObjectAbs aag (fst lslot) = SilcLabel))
                                 \<and> einvs s \<and> replaceable s slot (fst fin) rv
                                 \<and> cte_wp_at (op = rv) slot s \<and> s \<turnstile> (fst fin)
                                 \<and> ex_cte_cap_wp_to (appropriate_cte_cap rv) slot s
                                 \<and> (\<forall>t\<in>obj_refs (fst fin). halted_if_tcb t s)
                                 \<and> pas_refined aag s
                                 \<and> emptyable slot s
                                 \<and> simple_sched_action s
                                 \<and> pas_cap_cur_auth aag (fst fin)
                                 \<and> is_subject aag (fst slot) \<and>
(case (fst fin) of Zombie ptr bits n \<Rightarrow> is_subject aag (obj_ref_of (fst fin)) | _ \<Rightarrow> True) \<and> (is_zombie (fst fin) \<or> fst fin = NullCap) \<and>
                                   (is_zombie (fst fin) \<or> fst fin = NullCap)" in hoare_vcg_conj_lift)
           apply(wp finalise_cap_invs finalise_cap_replaceable finalise_cap_makes_halted finalise_cap_auth' finalise_cap_ret_is_subject finalise_cap_ret' finalise_cap_silc_inv finalise_cap_ret_is_silc finalise_cap_only_timer_irq_inv)[1]
          apply(rule finalise_cap_cases[where slot=slot])
         apply (clarsimp simp: cte_wp_at_caps_of_state)
         apply (erule disjE)
          apply (clarsimp simp: cap_irq_opt_def cte_wp_at_def is_zombie_def
                         split: cap.split_asm if_split_asm
                         elim!: ranE dest!: caps_of_state_cteD)
          apply(clarsimp cong: conj_cong simp: conj_comms)
          apply(rename_tac word option nat)
          apply(drule_tac s="{word}" in sym)
          apply clarsimp
          apply(rule conjI, fastforce)
          apply(clarsimp, rule conjI)
           apply(fastforce simp: silc_inv_def)
          apply(rule conjI)
           apply(fastforce simp: domain_sep_inv_def domain_sep_inv_cap_def
                                                      only_timer_irq_inv_def)
          
          apply(rule conjI[rotated], force)
          apply(clarsimp simp: ex_cte_cap_wp_to_def)+
          apply(rule_tac x="a" in exI, rule_tac x="b" in exI)
          apply(clarsimp simp: cte_wp_at_def appropriate_cte_cap_def)
          apply(drule_tac x="cap" in fun_cong)
          apply(clarsimp simp: appropriate_cte_cap_def split: cap.splits)
         apply(clarsimp cong: conj_cong simp: conj_comms)
        apply(wp drop_spec_ev[OF liftE_ev] is_final_cap_reads_respects | simp)+


       apply(rule_tac Q="\<lambda> rva s. rva = is_final_cap' rv s \<and> cte_wp_at (op = rv) slot s \<and>
                            only_timer_irq_inv irq st' s \<and>
                            silc_inv aag st s \<and>
                            pas_refined aag s \<and>
                            pas_cap_cur_auth aag rv \<and>
                            invs s \<and> valid_list s \<and> valid_sched s \<and> simple_sched_action s \<and>
                            s \<turnstile> rv \<and>
                            is_subject aag (fst slot) \<and>
                            emptyable slot s \<and>
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
      apply(wp drop_spec_ev[OF liftE_ev] reads_respects_f[OF get_cap_rev, where st=st and Q="\<top>"] get_cap_wp | simp)+
    apply(clarsimp cong: conj_cong simp:invs_valid_objs invs_arch_state invs_psp_aligned)
    apply(intro conjI impI | clarsimp | assumption)+
      apply(erule (1) cap_cur_auth_caps_of_state[rotated])
      apply(simp add: cte_wp_at_caps_of_state)
     apply(fastforce dest: cte_wp_at_valid_objs_valid_cap simp: invs_valid_objs)
    apply(drule if_unsafe_then_capD)
      apply(simp add: invs_ifunsafe)
     apply simp
    apply(clarsimp simp: ex_cte_cap_wp_to_def)
   done
next
  case (3 ptr bits n slot s) show ?case
    apply(simp add: rec_del.simps)
    apply(rule spec_equiv_valid_guard_imp)
     apply(wp drop_spec_ev[OF liftE_ev] drop_spec_ev[OF returnOk_ev] reads_respects_f[OF cap_swap_for_delete_reads_respects] cap_swap_for_delete_silc_inv drop_spec_ev[OF assertE_ev])+
    apply(fastforce simp: silc_inv_def)
    done
next
  case (4 ptr bits n slot s) show ?case
    apply(simp add: rec_del.simps)
    apply(rule spec_equiv_valid_guard_imp)
     apply(wp drop_spec_ev[OF returnOk_ev] drop_spec_ev[OF liftE_ev] set_cap_reads_respects_f drop_spec_ev[OF assertE_ev] get_cap_wp "4.hyps" reads_respects_f[OF get_cap_rev, where st=st and Q="\<top>"] validE_validE_R'[OF rec_del_silc_inv] | simp add: in_monad)+
    apply (rule_tac Q'="\<lambda> _. silc_inv aag st and
                    K (pasObjectAbs aag (fst slot) \<noteq> SilcLabel \<and> is_subject aag (fst slot))" in hoare_post_imp_R)
     prefer 2
     apply (clarsimp)
     apply(rule conjI, assumption)
     apply(rule impI)
     apply (drule silc_invD)
       apply assumption
      apply(simp add: intra_label_cap_def)
      apply(rule exI)
      apply(rule conjI)
       apply assumption
      apply(fastforce simp: cap_points_to_label_def)
     apply(clarsimp simp: slots_holding_overlapping_caps_def2 ctes_wp_at_def)
    apply(wp validE_validE_R'[OF rec_del_silc_inv] | simp)+
    apply (clarsimp simp add: zombie_is_cap_toE)
    apply (clarsimp simp: cte_wp_at_caps_of_state zombie_ptr_emptyable silc_inv_def)
   done
qed

lemmas rec_del_reads_respects_f = use_spec_ev[OF rec_del_spec_reads_respects_f]

lemma cap_delete_reads_respects:
  "reads_respects_f aag l (silc_inv aag st and only_timer_irq_inv irq st' and einvs and simple_sched_action and pas_refined aag and emptyable slot and K (is_subject aag (fst slot)))
    (cap_delete slot)"
  unfolding cap_delete_def
  apply(wp rec_del_spec_reads_respects_f | rule use_spec_ev | simp | elim conjE | force)+
  done



(*NOTE: Required to dance around the issue of the base potentially
        being zero and thus we can't conclude it is in the current subject.*)
lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq':
  "\<lbrakk>pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap ptr base)); reads_equiv aag s t; pas_refined aag x\<rbrakk>
   \<Longrightarrow>
   arm_asid_table (arch_state s) (asid_high_bits_of base) =
   arm_asid_table (arch_state t) (asid_high_bits_of base)"
  apply (subgoal_tac "asid_high_bits_of 0 = asid_high_bits_of 1")
   apply(case_tac "base = 0")
    apply(subgoal_tac "is_subject_asid aag 1")
     apply ((auto intro: requiv_arm_asid_table_asid_high_bits_of_asid_eq
                       aag_cap_auth_ASIDPoolCap_asid) |
            (auto simp: asid_high_bits_of_def asid_low_bits_def))+
  done

lemma pt_cap_aligned:
  "\<lbrakk>caps_of_state s p = Some (ArchObjectCap (PageTableCap word x));
    valid_caps (caps_of_state s) s\<rbrakk>
   \<Longrightarrow> is_aligned word pt_bits"
  by (auto simp: obj_ref_of_def pt_bits_def pageBits_def
          dest!: cap_aligned_valid[OF valid_capsD, unfolded cap_aligned_def,
                                    THEN conjunct1])

section "globals_equiv"

lemma maskInterrupt_no_mem:
  "invariant (maskInterrupt a b) (\<lambda>ms. P (underlying_memory ms))"
  apply(unfold maskInterrupt_def)
  apply(wp modify_wp)
  by simp

lemma maskInterrupt_no_exclusive:
  "invariant (maskInterrupt a b) (\<lambda>ms. P (exclusive_state ms))"
  apply(unfold maskInterrupt_def)
  apply(wp modify_wp)
  by simp

lemma globals_equiv_interrupt_states_update:
  "globals_equiv st (s\<lparr> interrupt_states := x \<rparr>) = globals_equiv st s"
  by(auto simp: globals_equiv_def idle_equiv_def)

lemma set_irq_state_valid_global_objs:
  "invariant (set_irq_state state irq) (valid_global_objs)"
  apply(simp add: set_irq_state_def)
  apply(wp modify_wp)
  apply(fastforce simp: valid_global_objs_def)
  done

crunch device_state_invs[wp]: maskInterrupt "\<lambda> ms. P (device_state ms)"

lemma set_irq_state_globals_equiv:
  "invariant (set_irq_state state irq) (globals_equiv st)"
  apply(simp add: set_irq_state_def)
  apply(wp dmo_no_mem_globals_equiv maskInterrupt_no_mem maskInterrupt_no_exclusive modify_wp)
  apply(simp add: globals_equiv_interrupt_states_update)
  done

lemma cancel_all_ipc_globals_equiv':
  "\<lbrace> globals_equiv st and valid_ko_at_arm \<rbrace>
   cancel_all_ipc epptr
   \<lbrace> \<lambda>_. globals_equiv st and valid_ko_at_arm \<rbrace>"
  unfolding cancel_all_ipc_def
  apply(wp mapM_x_wp[OF _ subset_refl] set_thread_state_globals_equiv
           set_endpoint_globals_equiv hoare_vcg_all_lift get_object_inv
           dxo_wp_weak | wpc | simp
        | wp_once hoare_drop_imps)+
  done

lemma cancel_all_ipc_globals_equiv:
  "\<lbrace> globals_equiv st and valid_ko_at_arm \<rbrace>
   cancel_all_ipc epptr
   \<lbrace> \<lambda>_. globals_equiv st \<rbrace>"
  apply(rule hoare_strengthen_post[OF cancel_all_ipc_globals_equiv'])
  by simp

lemma set_notification_globals_equiv:
  "\<lbrace> globals_equiv st and valid_ko_at_arm \<rbrace>
  set_notification ptr ntfn
   \<lbrace> \<lambda>_. globals_equiv st \<rbrace>"
  unfolding set_notification_def
  apply(wp set_object_globals_equiv get_object_wp | simp)+
  apply(fastforce simp: valid_ko_at_arm_def obj_at_def)+
  done

lemma set_notification_valid_ko_at_arm:
  "\<lbrace> valid_ko_at_arm \<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding set_notification_def
  apply (wp get_object_wp)
  apply(fastforce simp: valid_ko_at_arm_def get_tcb_ko_at obj_at_def)
done

lemma cancel_all_signals_globals_equiv':
  "\<lbrace> globals_equiv st and valid_ko_at_arm \<rbrace>
   cancel_all_signals epptr
   \<lbrace> \<lambda>_. globals_equiv st and valid_ko_at_arm \<rbrace>"
  unfolding cancel_all_signals_def
  apply(wp mapM_x_wp[OF _ subset_refl] set_thread_state_globals_equiv
           set_notification_valid_ko_at_arm dxo_wp_weak
           set_notification_globals_equiv hoare_vcg_all_lift | wpc | simp
        | wp_once hoare_drop_imps)+
  done

lemma cancel_all_signals_globals_equiv:
  "\<lbrace> globals_equiv st and valid_ko_at_arm \<rbrace>
   cancel_all_signals epptr
   \<lbrace> \<lambda>_. globals_equiv st \<rbrace>"
  apply(rule hoare_strengthen_post[OF cancel_all_signals_globals_equiv'])
  by simp

lemma unbind_notification_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm \<rbrace>
   unbind_notification t
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding unbind_notification_def
  by (wp gbn_wp set_bound_notification_globals_equiv set_notification_valid_ko_at_arm 
            set_notification_globals_equiv 
          | wpc 
          | simp)+

lemma unbind_notification_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm \<rbrace>
   unbind_notification t
   \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding unbind_notification_def
  by (wp gbn_wp set_bound_notification_valid_ko_at_arm set_notification_valid_ko_at_arm 
             
          | wpc 
          | simp)+

lemma unbind_maybe_notification_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm \<rbrace>
   unbind_maybe_notification a
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding unbind_maybe_notification_def
  by (wp gbn_wp set_bound_notification_globals_equiv set_notification_valid_ko_at_arm 
            set_notification_globals_equiv get_ntfn_wp 
          | wpc 
          | simp)+

lemma unbind_maybe_notification_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm \<rbrace>
   unbind_maybe_notification a
   \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding unbind_maybe_notification_def
  by (wp gbn_wp set_bound_notification_valid_ko_at_arm set_notification_valid_ko_at_arm 
         get_ntfn_wp
          | wpc 
          | simp)+

crunch valid_global_objs: fast_finalise "valid_global_objs"
  (wp: crunch_wps dxo_wp_weak ignore: reschedule_required)

lemma fast_finalise_globals_equiv:
  "\<lbrace> globals_equiv st and valid_ko_at_arm \<rbrace>
   fast_finalise cap final
   \<lbrace> \<lambda>_. globals_equiv st \<rbrace>"
  apply(case_tac cap)
  apply(clarsimp simp: when_def | wp cancel_all_ipc_globals_equiv cancel_all_signals_globals_equiv unbind_maybe_notification_globals_equiv | rule conjI)+
  done

lemma tcb_sched_action_enqueue_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> tcb_sched_action tcb_sched_enqueue word \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (simp add: etcb_at_def)
  done

lemma tcb_sched_action_dequeue_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> tcb_sched_action tcb_sched_dequeue word \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  apply (simp add: tcb_sched_action_def)
  apply wp
  apply (simp add: etcb_at_def)
 done

crunch valid_ko_at_arm[wp]: fast_finalise "valid_ko_at_arm" (wp: mapM_x_wp' dxo_wp_weak ignore: reschedule_required)
crunch valid_ko_at_arm[wp]: set_original "valid_ko_at_arm" (simp: valid_ko_at_arm_def)
crunch valid_ko_at_arm[wp]: set_cdt "valid_ko_at_arm" (simp: valid_ko_at_arm_def)

crunch valid_ko_at_arm[wp]: cap_insert "valid_ko_at_arm" (wp: hoare_drop_imps dxo_wp_weak simp: crunch_simps ignore: cap_insert_ext)

crunch valid_ko_at_arm[wp]: set_message_info "valid_ko_at_arm"
crunch valid_ko_at_arm[wp]: set_extra_badge "valid_ko_at_arm"
crunch valid_ko_at_arm[wp]: copy_mrs "valid_ko_at_arm" (wp: mapM_wp')

crunch valid_ko_at_arm[wp]: set_mrs "valid_ko_at_arm" (wp: mapM_x_wp' simp: zipWithM_x_mapM_x simp: arm_global_pd_not_tcb)

crunch globals_equiv[wp]: deleted_irq_handler "globals_equiv st"

lemma transfer_caps_valid_ko_at_arm[wp]:
  "\<lbrace> valid_ko_at_arm \<rbrace> transfer_caps a b c d e \<lbrace>\<lambda>_. valid_ko_at_arm\<rbrace>"
  unfolding transfer_caps_def
  by (wpsimp wp: transfer_caps_loop_pres cap_insert_valid_ko_at_arm)

lemma empty_slot_globals_equiv:
  "\<lbrace>globals_equiv st and valid_ko_at_arm\<rbrace> empty_slot s b\<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding empty_slot_def
  by (wpsimp wp: set_cap_globals_equiv'' set_original_globals_equiv hoare_vcg_if_lift2
                 set_cdt_globals_equiv dxo_wp_weak hoare_drop_imps hoare_vcg_all_lift)

crunch globals_equiv: cap_delete_one "globals_equiv st"
  (wp: set_cap_globals_equiv'' hoare_drop_imps simp: crunch_simps unless_def)

crunch valid_ko_at_arm[wp]: thread_set "valid_ko_at_arm" (simp: arm_global_pd_not_tcb)

lemma set_asid_pool_valid_ko_at_arm[wp]:
  "\<lbrace>valid_ko_at_arm\<rbrace> set_asid_pool a b\<lbrace>\<lambda>_.valid_ko_at_arm\<rbrace>"
  unfolding set_asid_pool_def
  apply (wp get_object_wp | wpc)+
  apply(fastforce simp: valid_ko_at_arm_def get_tcb_ko_at obj_at_def)
done

crunch valid_ko_at_arm[wp]: finalise_cap "valid_ko_at_arm"
  (wp: hoare_vcg_if_lift2 hoare_drop_imps select_wp modify_wp mapM_wp' dxo_wp_weak
   simp: unless_def crunch_simps
   ignore: empty_slot_ext)

lemma delete_asid_globals_equiv:
  "\<lbrace>globals_equiv st and valid_arch_state \<rbrace>
    delete_asid asid pd
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding delete_asid_def
  apply (wp set_vm_root_globals_equiv set_asid_pool_globals_equiv invalidate_asid_entry_globals_equiv
     flush_space_globals_equiv invalidate_asid_entry_valid_ko_at_arm
    | wpc | simp add: valid_arch_state_ko_at_arm)+
done

lemma pagebitsforsize_ge_2[simp] :
  "2 \<le> pageBitsForSize vmpage_size"
  apply (induct vmpage_size)
  apply simp+
done

lemma arch_finalise_cap_globals_equiv:
  "\<lbrace>globals_equiv st and valid_global_objs and valid_arch_state and pspace_aligned and valid_arch_objs and valid_global_refs and valid_vs_lookup\<rbrace>
     arch_finalise_cap cap b
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (induct cap)
  apply (simp_all add:arch_finalise_cap_def)
  apply (wp delete_asid_pool_globals_equiv case_option_wp unmap_page_globals_equiv
            unmap_page_table_globals_equiv delete_asid_globals_equiv |
         wpc | clarsimp split: bool.splits option.splits | intro impI conjI)+
done


lemma arch_finalise_cap_globals_equiv' : "\<lbrace>globals_equiv st and invs\<rbrace>
  arch_finalise_cap cap b \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (rule arch_finalise_cap_globals_equiv)
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_caps_def)
done


lemma mapM_x_swp_store_kernel_base_globals_equiv:
  "\<lbrace>invs and globals_equiv st and cte_wp_at (op = (ArchObjectCap (PageDirectoryCap word option)))
         slot\<rbrace>
  mapM_x (swp store_pde InvalidPDE)
        (map ((\<lambda>x. x + word) \<circ> swp op << 2)
          [0.e.(kernel_base >> 20) - 1])
       \<lbrace>\<lambda>y s. globals_equiv st s \<and>
              invs s\<rbrace>"
  apply (rule hoare_pre)
  apply (wp mapM_x_swp_store_pde_invs_unmap mapM_x_swp_store_pde_globals_equiv)
  apply clarsimp
  apply (frule invs_valid_objs)
  apply (frule invs_valid_global_refs)
  apply (intro impI conjI allI)
  apply (simp add: cte_wp_at_page_directory_not_in_globals
                   cte_wp_at_page_directory_not_in_kernel_mappings
                   not_in_global_not_arm
                   pde_ref_def)+
done

end

end
