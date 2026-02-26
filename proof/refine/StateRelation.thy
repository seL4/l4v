(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   The refinement relation between abstract and concrete states
*)

theory StateRelation
imports ArchStateRelation
begin

arch_requalify_consts
  arch_fault_map
  vmrights_map
  acap_relation
  arch_tcb_relation
  aobj_relation_cuts
  is_other_obj_relation_type
  ghost_relation_wrapper_2
  arch_state_relation

definition cte_map :: "cslot_ptr \<Rightarrow> machine_word" where
  "cte_map \<equiv> \<lambda>(oref, cref). oref + (of_bl cref << cte_level_bits)"

(* FIXME arch-split: same derivation on all arches *)
lemmas (in Arch) cte_map_def' = cte_map_def[simplified cte_level_bits_def shiftl_t2n mult_ac, simplified]

definition lookup_failure_map :: "ExceptionTypes_A.lookup_failure \<Rightarrow> Fault_H.lookup_failure" where
  "lookup_failure_map \<equiv> \<lambda>lf. case lf of
     ExceptionTypes_A.InvalidRoot         \<Rightarrow> Fault_H.InvalidRoot
   | ExceptionTypes_A.MissingCapability n \<Rightarrow> Fault_H.MissingCapability n
   | ExceptionTypes_A.DepthMismatch n m   \<Rightarrow> Fault_H.DepthMismatch n m
   | ExceptionTypes_A.GuardMismatch n g   \<Rightarrow> Fault_H.GuardMismatch n (of_bl g) (length g)"

primrec fault_map :: "ExceptionTypes_A.fault \<Rightarrow> Fault_H.fault" where
  "fault_map (ExceptionTypes_A.CapFault ref bool failure) =
     Fault_H.CapFault ref bool (lookup_failure_map failure)"
| "fault_map (ExceptionTypes_A.ArchFault arch_fault) =
     Fault_H.ArchFault (arch_fault_map arch_fault)"
| "fault_map (ExceptionTypes_A.UnknownSyscallException n) =
     Fault_H.UnknownSyscallException n"
| "fault_map (ExceptionTypes_A.UserException x y) =
     Fault_H.UserException x y"

definition zbits_map :: "nat option \<Rightarrow> zombie_type" where
  "zbits_map N \<equiv> case N of Some n \<Rightarrow> ZombieCNode n | None \<Rightarrow> ZombieTCB"

primrec cap_relation :: "cap \<Rightarrow> capability \<Rightarrow> bool" where
  "cap_relation Structures_A.NullCap c =
     (c = Structures_H.NullCap)"
| "cap_relation Structures_A.DomainCap c =
     (c = Structures_H.DomainCap)"
| "cap_relation (Structures_A.UntypedCap dev ref n f) c =
     (c = Structures_H.UntypedCap dev ref n f)"
| "cap_relation (Structures_A.EndpointCap ref b r) c =
     (c = Structures_H.EndpointCap ref b (AllowSend \<in> r) (AllowRecv \<in> r) (AllowGrant \<in> r)
                                         (AllowGrantReply \<in> r))"
| "cap_relation (Structures_A.NotificationCap ref b r) c =
     (c = Structures_H.NotificationCap ref b (AllowSend \<in> r) (AllowRecv \<in> r))"
| "cap_relation (Structures_A.CNodeCap ref n L) c =
     (c = Structures_H.CNodeCap ref n (of_bl L) (length L))"
| "cap_relation (Structures_A.ThreadCap ref) c =
     (c = Structures_H.ThreadCap ref)"
| "cap_relation (Structures_A.ReplyCap ref master r) c =
     (c = Structures_H.ReplyCap ref master (AllowGrant \<in> r))"
| "cap_relation (Structures_A.IRQControlCap) c =
     (c = Structures_H.IRQControlCap)"
| "cap_relation (Structures_A.IRQHandlerCap irq) c =
     (c = Structures_H.IRQHandlerCap irq)"
| "cap_relation (Structures_A.ArchObjectCap a) c =
     (\<exists>a'. acap_relation a a' \<and> c = Structures_H.ArchObjectCap a')"
| "cap_relation (Structures_A.Zombie p b n) c =
     (c = Structures_H.Zombie p (zbits_map b) n)"

definition cte_relation :: "cap_ref \<Rightarrow> obj_relation_cut" where
  "cte_relation y \<equiv> \<lambda>ko ko'. \<exists>sz cs cte cap. ko = CNode sz cs \<and> ko' = KOCTE cte
                                              \<and> cs y = Some cap \<and> cap_relation cap (cteCap cte)"

definition ntfn_relation :: "Structures_A.notification \<Rightarrow> Structures_H.notification \<Rightarrow> bool" where
  "ntfn_relation \<equiv> \<lambda>ntfn ntfn'.
     (case ntfn_obj ntfn of
        Structures_A.IdleNtfn      \<Rightarrow> ntfnObj ntfn' = Structures_H.IdleNtfn
      | Structures_A.WaitingNtfn q \<Rightarrow> ntfnObj ntfn' = Structures_H.WaitingNtfn q
      | Structures_A.ActiveNtfn b  \<Rightarrow> ntfnObj ntfn' = Structures_H.ActiveNtfn b)
     \<and> ntfn_bound_tcb ntfn = ntfnBoundTCB ntfn'"

definition ep_relation :: "Structures_A.endpoint \<Rightarrow> Structures_H.endpoint \<Rightarrow> bool" where
 "ep_relation \<equiv> \<lambda>ep ep'. case ep of
    Structures_A.IdleEP   \<Rightarrow> ep' = Structures_H.IdleEP
  | Structures_A.RecvEP q \<Rightarrow> ep' = Structures_H.RecvEP q
  | Structures_A.SendEP q \<Rightarrow> ep' = Structures_H.SendEP q"

definition fault_rel_optionation :: "ExceptionTypes_A.fault option \<Rightarrow> Fault_H.fault option \<Rightarrow> bool"
  where
  "fault_rel_optionation \<equiv> \<lambda>f f'. f' = map_option fault_map f"

primrec thread_state_relation :: "Structures_A.thread_state \<Rightarrow> Structures_H.thread_state \<Rightarrow> bool"
  where
  "thread_state_relation (Structures_A.Running) ts'
     = (ts' = Structures_H.Running)"
| "thread_state_relation (Structures_A.Restart) ts'
     = (ts' = Structures_H.Restart)"
| "thread_state_relation (Structures_A.Inactive) ts'
     = (ts' = Structures_H.Inactive)"
| "thread_state_relation (Structures_A.IdleThreadState) ts'
     = (ts' = Structures_H.IdleThreadState)"
| "thread_state_relation (Structures_A.BlockedOnReply) ts'
     = (ts' = Structures_H.BlockedOnReply)"
| "thread_state_relation (Structures_A.BlockedOnReceive oref sp) ts'
     = (ts' = Structures_H.BlockedOnReceive oref (receiver_can_grant sp))"
| "thread_state_relation (Structures_A.BlockedOnSend oref sp) ts'
     = (ts' = Structures_H.BlockedOnSend oref (sender_badge sp)
                         (sender_can_grant sp) (sender_can_grant_reply sp) (sender_is_call sp))"
| "thread_state_relation (Structures_A.BlockedOnNotification oref) ts'
     = (ts' = Structures_H.BlockedOnNotification oref)"

definition tcb_relation :: "Structures_A.tcb \<Rightarrow> Structures_H.tcb \<Rightarrow> bool" where
  "tcb_relation \<equiv> \<lambda>tcb tcb'.
     tcb_fault_handler tcb = to_bl (tcbFaultHandler tcb')
   \<and> tcb_ipc_buffer tcb = tcbIPCBuffer tcb'
   \<and> arch_tcb_relation (tcb_arch tcb) (tcbArch tcb')
   \<and> thread_state_relation (tcb_state tcb) (tcbState tcb')
   \<and> fault_rel_optionation (tcb_fault tcb) (tcbFault tcb')
   \<and> cap_relation (tcb_ctable tcb) (cteCap (tcbCTable tcb'))
   \<and> cap_relation (tcb_vtable tcb) (cteCap (tcbVTable tcb'))
   \<and> cap_relation (tcb_reply tcb) (cteCap (tcbReply tcb'))
   \<and> cap_relation (tcb_caller tcb) (cteCap (tcbCaller tcb'))
   \<and> cap_relation (tcb_ipcframe tcb) (cteCap (tcbIPCBufferFrame tcb'))
   \<and> tcb_bound_notification tcb = tcbBoundNotification tcb'
   \<and> tcb_mcpriority tcb = tcbMCP tcb'
   \<and> tcb_priority tcb = tcbPriority tcb'
   \<and> tcb_time_slice tcb = tcbTimeSlice tcb'
   \<and> tcb_domain tcb = tcbDomain tcb'
   \<and> tcb_flags tcb = word_to_tcb_flags (tcbFlags tcb')"

\<comment> \<open>
  A pair of objects @{term "(obj, obj')"} should satisfy the following relation when, under further
  mild assumptions, a @{term corres_underlying} lemma for @{term "set_object obj"}
  and @{term "setObject obj'"} can be stated: see setObject_other_corres in KHeap_R.

  TCBs do not satisfy this relation because the tcbSchedPrev and tcbSchedNext fields of a TCB are
  used to model the ready queues, and so an update to such a field would correspond to an update
  to a ready queue (see ready_queues_relation below).\<close>
definition
  other_obj_relation :: "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "other_obj_relation obj obj' \<equiv>
   case (obj, obj') of
      (Endpoint ep, KOEndpoint ep') \<Rightarrow> ep_relation ep ep'
    | (Notification ntfn, KONotification ntfn') \<Rightarrow> ntfn_relation ntfn ntfn'
    | _ \<Rightarrow> False"

definition tcb_relation_cut :: "Structures_A.kernel_object \<Rightarrow> kernel_object \<Rightarrow> bool" where
  "tcb_relation_cut obj obj' \<equiv>
   case (obj, obj') of
       (TCB t, KOTCB t') \<Rightarrow> tcb_relation t t'
     | _ \<Rightarrow> False"

primrec obj_relation_cuts :: "Structures_A.kernel_object \<Rightarrow> machine_word \<Rightarrow> obj_relation_cuts" where
  "obj_relation_cuts (CNode sz cs) x =
     (if well_formed_cnode_n sz cs
      then {(cte_map (x, y), cte_relation y) | y. y \<in> dom cs}
      else {(x, \<bottom>\<bottom>)})"
| "obj_relation_cuts (TCB tcb) x = {(x, tcb_relation_cut)}"
| "obj_relation_cuts (Endpoint ep) x = {(x, other_obj_relation)}"
| "obj_relation_cuts (Notification ntfn) x = {(x, other_obj_relation)}"
| "obj_relation_cuts (ArchObj ao) x = aobj_relation_cuts ao x"

lemma other_obj_relation_not_aobj:
  "other_obj_relation ko ko' \<Longrightarrow> \<not> is_ArchObj ko"
  unfolding other_obj_relation_def is_ArchObj_def
  by clarsimp

definition pspace_dom :: "Structures_A.kheap \<Rightarrow> machine_word set" where
  "pspace_dom ps \<equiv> \<Union>x\<in>dom ps. fst ` (obj_relation_cuts (the (ps x)) x)"

definition pspace_relation ::
  "Structures_A.kheap \<Rightarrow> (machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> bool" where
  "pspace_relation ab con \<equiv>
     (pspace_dom ab = dom con) \<and>
     (\<forall>x \<in> dom ab. \<forall>(y, P) \<in> obj_relation_cuts (the (ab x)) x. P (the (ab x)) (the (con y)))"

primrec sched_act_relation :: "Structures_A.scheduler_action \<Rightarrow> scheduler_action \<Rightarrow> bool"
  where
  "sched_act_relation resume_cur_thread a' = (a' = ResumeCurrentThread)" |
  "sched_act_relation choose_new_thread a' = (a' = ChooseNewThread)" |
  "sched_act_relation (switch_thread x) a' = (a' = SwitchToThread x)"

definition queue_end_valid :: "obj_ref list \<Rightarrow> tcb_queue \<Rightarrow> bool" where
  "queue_end_valid ts q \<equiv>
     (ts = [] \<longrightarrow> tcbQueueEnd q = None) \<and> (ts \<noteq> [] \<longrightarrow> tcbQueueEnd q = Some (last ts))"

definition prev_queue_head :: "tcb_queue \<Rightarrow> (obj_ref \<rightharpoonup> 'a) \<Rightarrow> bool" where
  "prev_queue_head q prevs \<equiv> \<forall>head. tcbQueueHead q = Some head \<longrightarrow> prevs head = None"

lemma prev_queue_head_heap_upd:
  "\<lbrakk>prev_queue_head q prevs; Some r \<noteq> tcbQueueHead q\<rbrakk> \<Longrightarrow> prev_queue_head q (prevs(r := x))"
  by (clarsimp simp: prev_queue_head_def)

definition list_queue_relation ::
  "obj_ref list \<Rightarrow> tcb_queue \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> bool"
  where
  "list_queue_relation ts q nexts prevs \<equiv>
     heap_ls nexts (tcbQueueHead q) ts \<and> queue_end_valid ts q \<and> prev_queue_head q prevs"

lemma list_queue_relation_nil:
  "list_queue_relation ts q nexts prevs \<Longrightarrow> ts = [] \<longleftrightarrow> tcbQueueEmpty q"
  by (fastforce dest: heap_path_head simp: tcbQueueEmpty_def list_queue_relation_def)

definition ready_queue_relation ::
  "Structures_A.domain \<Rightarrow> Structures_A.priority
   \<Rightarrow> Structures_A.ready_queue \<Rightarrow> ready_queue
   \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref)
   \<Rightarrow> (obj_ref \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "ready_queue_relation d p q q' nexts prevs flag \<equiv>
     list_queue_relation q q' nexts prevs
     \<and> (\<forall>t. flag t \<longleftrightarrow> t \<in> set q)
     \<and> (d > maxDomain \<or> p > maxPriority \<longrightarrow> tcbQueueEmpty q')"

definition ready_queues_relation_2 ::
  "(Structures_A.domain \<Rightarrow> Structures_A.priority \<Rightarrow> Structures_A.ready_queue)
   \<Rightarrow> (domain \<times> priority \<Rightarrow> ready_queue)
   \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref)
   \<Rightarrow> (domain \<Rightarrow> priority \<Rightarrow> obj_ref \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "ready_queues_relation_2 qs qs' nexts prevs inQs \<equiv>
     \<forall>d p. let q = qs d p; q' = qs' (d, p); flag = inQs d p in
           ready_queue_relation d p q q' nexts prevs flag"

abbreviation ready_queues_relation :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ready_queues_relation s s' \<equiv>
     ready_queues_relation_2
      (ready_queues s) (ksReadyQueues s') (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
      (\<lambda>d p. inQ d p |< tcbs_of' s')"

lemmas ready_queues_relation_def = ready_queues_relation_2_def

definition cdt_relation :: "(cslot_ptr \<Rightarrow> bool) \<Rightarrow> cdt \<Rightarrow> cte_heap \<Rightarrow> bool" where
  "cdt_relation \<equiv> \<lambda>cte_at m m'.
     \<forall>c. cte_at c \<longrightarrow> cte_map ` descendants_of c m = descendants_of' (cte_map c) m'"

definition cdt_list_relation :: "cdt_list \<Rightarrow> cdt \<Rightarrow> cte_heap \<Rightarrow> bool" where
 "cdt_list_relation \<equiv> \<lambda>t m m'.
    \<forall>c cap node. m' (cte_map c) = Some (CTE cap node)
        \<longrightarrow> (case next_slot c t m of None \<Rightarrow> True
                                   | Some next \<Rightarrow> mdbNext node = cte_map next)"

definition revokable_relation ::
  "(cslot_ptr \<Rightarrow> bool) \<Rightarrow> (cslot_ptr \<Rightarrow> cap option) \<Rightarrow> cte_heap \<Rightarrow> bool" where
  "revokable_relation revo cs m' \<equiv>
     \<forall>c cap node. cs c \<noteq> None \<longrightarrow>
                    m' (cte_map c) = Some (CTE cap node) \<longrightarrow>
                    revo c = mdbRevocable node"

definition irq_state_relation :: "irq_state \<Rightarrow> irqstate \<Rightarrow> bool" where
  "irq_state_relation irq irq' \<equiv> case (irq, irq') of
     (irq_state.IRQInactive, irqstate.IRQInactive) \<Rightarrow> True
   | (irq_state.IRQSignal, irqstate.IRQSignal) \<Rightarrow> True
   | (irq_state.IRQTimer, irqstate.IRQTimer) \<Rightarrow> True
   | (irq_state.IRQReserved, irqstate.IRQReserved) \<Rightarrow> True
   | _ \<Rightarrow> False"

definition interrupt_state_relation ::
  "(irq \<Rightarrow> obj_ref) \<Rightarrow> (irq \<Rightarrow> irq_state) \<Rightarrow> interrupt_state \<Rightarrow> bool" where
  "interrupt_state_relation node_map irqs is \<equiv>
     (\<exists>node irqs'. is = InterruptState node irqs'
                    \<and> (\<forall>irq. node_map irq = node + (ucast irq << cte_level_bits))
                    \<and> (\<forall>irq. irq_state_relation (irqs irq) (irqs' irq)))"

definition rights_mask_map :: "rights set \<Rightarrow> Types_H.cap_rights" where
  "rights_mask_map \<equiv>
     \<lambda>rs. CapRights (AllowWrite \<in> rs) (AllowRead \<in> rs) (AllowGrant \<in> rs) (AllowGrantReply \<in> rs)"

text \<open>
  Relations on other data types that aren't stored but used as intermediate values
  in the specs.
\<close>
primrec message_info_map :: "Structures_A.message_info \<Rightarrow> Types_H.message_info" where
  "message_info_map (Structures_A.MI a b c d) = (Types_H.MI a b c d)"

lemma mi_map_label[simp]: "msgLabel (message_info_map mi) = mi_label mi"
  by (cases mi, simp)

primrec syscall_error_map :: "ExceptionTypes_A.syscall_error \<Rightarrow> Fault_H.syscall_error" where
  "syscall_error_map (ExceptionTypes_A.InvalidArgument n)   = Fault_H.InvalidArgument n"
| "syscall_error_map (ExceptionTypes_A.InvalidCapability n) = (Fault_H.InvalidCapability n)"
| "syscall_error_map ExceptionTypes_A.IllegalOperation      = Fault_H.IllegalOperation"
| "syscall_error_map (ExceptionTypes_A.RangeError n m)      = Fault_H.RangeError n m"
| "syscall_error_map ExceptionTypes_A.AlignmentError        = Fault_H.AlignmentError"
| "syscall_error_map (ExceptionTypes_A.FailedLookup b lf)   = Fault_H.FailedLookup b (lookup_failure_map lf)"
| "syscall_error_map ExceptionTypes_A.TruncatedMessage      = Fault_H.TruncatedMessage"
| "syscall_error_map ExceptionTypes_A.DeleteFirst           = Fault_H.DeleteFirst"
| "syscall_error_map ExceptionTypes_A.RevokeFirst           = Fault_H.RevokeFirst"
| "syscall_error_map (ExceptionTypes_A.NotEnoughMemory n)   = Fault_H.syscall_error.NotEnoughMemory n"

(* provided so that ghost_relation can be used within the generic definition of state_relation, by
   passing in the union of fields needed by ghost_relation on all architectures and hiding any
   specific arch fields needed *)
abbreviation ghost_relation_wrapper :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ghost_relation_wrapper s s' \<equiv>
     ghost_relation_wrapper_2 (kheap s) (gsUserPages s') (gsCNodes s') (ksArchState s')"

abbreviation domain_list_map ::
  "(domain \<times> Structures_A.domain_duration) list \<Rightarrow> domain_schedule_item list" where
  "domain_list_map \<equiv> map (\<lambda>(domain, duration). (domain, ucast duration))"

definition state_relation :: "(det_state \<times> kernel_state) set" where
  "state_relation \<equiv> {(s, s').
         pspace_relation (kheap s) (ksPSpace s')
       \<and> sched_act_relation (scheduler_action s) (ksSchedulerAction s')
       \<and> ready_queues_relation s s'
       \<and> ghost_relation_wrapper s s'
       \<and> cdt_relation (swp cte_at s) (cdt s) (ctes_of s')
       \<and> cdt_list_relation (cdt_list s) (cdt s) (ctes_of s')
       \<and> revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) (ctes_of s')
       \<and> (arch_state s, ksArchState s') \<in> arch_state_relation
       \<and> interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s')
       \<and> (cur_thread s = ksCurThread s')
       \<and> (idle_thread s = ksIdleThread s')
       \<and> (machine_state s = ksMachineState s')
       \<and> (work_units_completed s = ksWorkUnitsCompleted s')
       \<and> (domain_index s = ksDomScheduleIdx s')
       \<and> (domain_list_map (domain_list s) = ksDomSchedule s')
       \<and> (domain_start_index s = ksDomScheduleStart s')
       \<and> (cur_domain s = ksCurDomain s')
       \<and> (domain_time s = ksDomainTime s')}"

text \<open>Rules for using states in the relation.\<close>

lemma curthread_relation:
  "(a, b) \<in> state_relation \<Longrightarrow> ksCurThread b = cur_thread a"
  by (simp add: state_relation_def)

lemma curdomain_relation[elim!]:
  "(s, s') \<in> state_relation \<Longrightarrow> cur_domain s = ksCurDomain s'"
  by (clarsimp simp: state_relation_def)

lemma state_relation_pspace_relation[elim!]:
  "(s,s') \<in> state_relation \<Longrightarrow> pspace_relation (kheap s) (ksPSpace s')"
  by (simp add: state_relation_def)

lemma state_relation_sched_act_relation[elim!]:
  "(s,s') \<in> state_relation \<Longrightarrow> sched_act_relation (scheduler_action s) (ksSchedulerAction s')"
  by (clarsimp simp: state_relation_def)

lemma state_relation_ready_queues_relation[elim!]:
  "(s, s') \<in> state_relation \<Longrightarrow> ready_queues_relation s s'"
  by (simp add: state_relation_def)

lemma state_relation_idle_thread[elim!]:
  "(s, s') \<in> state_relation \<Longrightarrow> idle_thread s = ksIdleThread s'"
  by (clarsimp simp: state_relation_def)

lemma state_relationD:
  "(s, s') \<in> state_relation \<Longrightarrow>
   pspace_relation (kheap s) (ksPSpace s') \<and>
   sched_act_relation (scheduler_action s) (ksSchedulerAction s') \<and>
   ready_queues_relation s s' \<and>
   ghost_relation_wrapper s s' \<and>
   cdt_relation (swp cte_at s) (cdt s) (ctes_of s') \<and>
   cdt_list_relation (cdt_list s) (cdt s) (ctes_of s') \<and>
   revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) (ctes_of s') \<and>
   (arch_state s, ksArchState s') \<in> arch_state_relation \<and>
   interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s') \<and>
   cur_thread s = ksCurThread s' \<and>
   idle_thread s = ksIdleThread s' \<and>
   machine_state s = ksMachineState s' \<and>
   work_units_completed s = ksWorkUnitsCompleted s' \<and>
   domain_index s = ksDomScheduleIdx s' \<and>
   domain_list_map (domain_list s) = ksDomSchedule s' \<and>
   domain_start_index s = ksDomScheduleStart s' \<and>
   cur_domain s = ksCurDomain s' \<and>
   domain_time s = ksDomainTime s'"
  unfolding state_relation_def by simp

lemma state_relationE [elim?]:
  assumes sr:  "(s, s') \<in> state_relation"
  and rl: "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
             sched_act_relation (scheduler_action s) (ksSchedulerAction s');
             ready_queues_relation s s';
             ghost_relation_wrapper s s';
             cdt_relation (swp cte_at s) (cdt s) (ctes_of s') \<and>
             revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) (ctes_of s');
             cdt_list_relation (cdt_list s) (cdt s) (ctes_of s');
             (arch_state s, ksArchState s') \<in> arch_state_relation;
             interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s');
             cur_thread s = ksCurThread s';
             idle_thread s = ksIdleThread s';
             machine_state s = ksMachineState s';
             work_units_completed s = ksWorkUnitsCompleted s';
             domain_index s = ksDomScheduleIdx s';
             domain_list_map (domain_list s) = ksDomSchedule s';
             domain_start_index s = ksDomScheduleStart s';
             cur_domain s = ksCurDomain s';
             domain_time s = ksDomainTime s' \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using sr by (blast intro!: rl dest: state_relationD)

lemmas gen_isCap_defs =
  isZombie_def isArchObjectCap_def
  isThreadCap_def isCNodeCap_def isNotificationCap_def
  isEndpointCap_def isUntypedCap_def isNullCap_def
  isIRQHandlerCap_def isIRQControlCap_def isReplyCap_def
  isDomainCap_def

lemma isCNodeCap_cap_map[simp]:
  "cap_relation c c' \<Longrightarrow> isCNodeCap c' = is_cnode_cap c"
  by (cases c) (auto simp: gen_isCap_defs split: sum.splits)

lemma sts_rel_idle :
  "thread_state_relation st IdleThreadState = (st = Structures_A.IdleThreadState)"
  by (cases st, auto)

lemma pspace_relation_absD:
  "\<lbrakk> ab x = Some y; pspace_relation ab con \<rbrakk>
      \<Longrightarrow> \<forall>(x', P) \<in> obj_relation_cuts y x. \<exists>z. con x' = Some z \<and> P y z"
  apply (clarsimp simp: pspace_relation_def)
  apply (drule bspec, erule domI)
  apply simp
  apply (drule(1) bspec)
  apply (subgoal_tac "a \<in> pspace_dom ab", clarsimp)
  apply (simp (no_asm) add: pspace_dom_def)
  apply (fastforce simp: image_def intro: rev_bexI)
  done

lemma in_related_pspace_dom:
  "\<lbrakk> s' x = Some y; pspace_relation s s' \<rbrakk> \<Longrightarrow> x \<in> pspace_dom s"
  by (clarsimp simp add: pspace_relation_def)

lemma pspace_dom_revE:
  "\<lbrakk> x \<in> pspace_dom ps; \<And>ko y P. \<lbrakk> ps y = Some ko; (x, P) \<in> obj_relation_cuts ko y \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (clarsimp simp add: pspace_dom_def)

lemma pspace_dom_relatedE:
  "\<lbrakk> s' x = Some ko'; pspace_relation s s';
     \<And>y ko P. \<lbrakk> s y = Some ko; (x, P) \<in> obj_relation_cuts ko y; P ko ko' \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  apply (rule pspace_dom_revE [OF in_related_pspace_dom]; assumption?)
  apply (fastforce dest: pspace_relation_absD)
  done

(* used for generating architecture-specific cap_relation split lemmas *)
lemma eq_trans_helper:
  "\<lbrakk> x = y; P y = Q \<rbrakk> \<Longrightarrow> P x = Q"
  by simp

text \<open>Architecture-specific requirements\<close>

locale StateRelation_R =
  assumes is_other_obj_relation_type_gen[simp]:
    "\<And>n. \<not> is_other_obj_relation_type (ACapTable n)"
    "\<not> is_other_obj_relation_type ATCB"
    "is_other_obj_relation_type AEndpoint"
    "is_other_obj_relation_type ANTFN"
    "\<And>n. \<not> is_other_obj_relation_type (AGarbage n)"
  assumes msgLabelBits_msg_label_bits:
    "msgLabelBits = msg_label_bits"
  assumes msgInfoRegister_msg_info_register:
    "msgInfoRegister = msg_info_register"
  assumes obj_relation_cuts_trivial:
    "\<And>ptr ty. ptr \<in> fst ` obj_relation_cuts ty ptr"

end
