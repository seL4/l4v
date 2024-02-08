(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   The refinement relation between abstract and concrete states
*)

theory StateRelation
imports InvariantUpdates_H
begin

context begin interpretation Arch .

definition cte_map :: "cslot_ptr \<Rightarrow> machine_word" where
  "cte_map \<equiv> \<lambda>(oref, cref). oref + (of_bl cref << cte_level_bits)"

lemmas cte_map_def' = cte_map_def[simplified cte_level_bits_def shiftl_t2n mult_ac, simplified]

definition lookup_failure_map :: "ExceptionTypes_A.lookup_failure \<Rightarrow> Fault_H.lookup_failure" where
  "lookup_failure_map \<equiv> \<lambda>lf. case lf of
     ExceptionTypes_A.InvalidRoot         \<Rightarrow> Fault_H.InvalidRoot
   | ExceptionTypes_A.MissingCapability n \<Rightarrow> Fault_H.MissingCapability n
   | ExceptionTypes_A.DepthMismatch n m   \<Rightarrow> Fault_H.DepthMismatch n m
   | ExceptionTypes_A.GuardMismatch n g   \<Rightarrow> Fault_H.GuardMismatch n (of_bl g) (length g)"

primrec arch_fault_map :: "Machine_A.RISCV64_A.arch_fault \<Rightarrow> arch_fault" where
  "arch_fault_map (Machine_A.RISCV64_A.VMFault ptr msg) = VMFault ptr msg"

primrec fault_map :: "ExceptionTypes_A.fault \<Rightarrow> Fault_H.fault" where
  "fault_map (ExceptionTypes_A.CapFault ref bool failure) =
     Fault_H.CapFault ref bool (lookup_failure_map failure)"
| "fault_map (ExceptionTypes_A.ArchFault arch_fault) =
     Fault_H.ArchFault (arch_fault_map arch_fault)"
| "fault_map (ExceptionTypes_A.UnknownSyscallException n) =
     Fault_H.UnknownSyscallException n"
| "fault_map (ExceptionTypes_A.UserException x y) =
     Fault_H.UserException x y"
| "fault_map (ExceptionTypes_A.Timeout d) =
     Fault_H.Timeout d"

type_synonym obj_relation_cut = "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
type_synonym obj_relation_cuts = "(machine_word \<times> obj_relation_cut) set"

definition vmrights_map :: "rights set \<Rightarrow> vmrights" where
  "vmrights_map S \<equiv> if AllowRead \<in> S
                     then (if AllowWrite \<in> S then VMReadWrite else VMReadOnly)
                     else VMKernelOnly"

definition zbits_map :: "nat option \<Rightarrow> zombie_type" where
  "zbits_map N \<equiv> case N of Some n \<Rightarrow> ZombieCNode n | None \<Rightarrow> ZombieTCB"

definition mdata_map ::
  "(Machine_A.RISCV64_A.asid \<times> vspace_ref) option \<Rightarrow> (asid \<times> vspace_ref) option" where
  "mdata_map = map_option (\<lambda>(asid, ref). (ucast asid, ref))"

primrec acap_relation :: "arch_cap \<Rightarrow> arch_capability \<Rightarrow> bool" where
  "acap_relation (arch_cap.ASIDPoolCap p asid) c =
     (c = ASIDPoolCap p (ucast asid))"
| "acap_relation (arch_cap.ASIDControlCap) c =
     (c = ASIDControlCap)"
| "acap_relation (arch_cap.FrameCap p rghts sz dev data) c =
     (c = FrameCap p (vmrights_map rghts) sz dev (mdata_map data))"
| "acap_relation (arch_cap.PageTableCap p data) c =
     (c = PageTableCap p (mdata_map data))"

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
| "cap_relation (Structures_A.ReplyCap ref r) c           = (c =
           Structures_H.ReplyCap ref (AllowGrant \<in> r))"
| "cap_relation (Structures_A.SchedContextCap ref n) c    = (c =
           Structures_H.SchedContextCap ref (min_sched_context_bits + n))"
| "cap_relation (Structures_A.SchedControlCap) c          = (c =
           Structures_H.SchedControlCap)"
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

definition asid_pool_relation :: "(asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> asidpool \<Rightarrow> bool" where
  "asid_pool_relation \<equiv> \<lambda>p p'. p = inv ASIDPool p' o ucast"

definition ntfn_relation :: "Structures_A.notification \<Rightarrow> Structures_H.notification \<Rightarrow> bool" where
  "ntfn_relation \<equiv> \<lambda>ntfn ntfn'.
     (case ntfn_obj ntfn of
        Structures_A.IdleNtfn      \<Rightarrow> ntfnObj ntfn' = Structures_H.IdleNtfn
      | Structures_A.WaitingNtfn q \<Rightarrow> ntfnObj ntfn' = Structures_H.WaitingNtfn q
      | Structures_A.ActiveNtfn b  \<Rightarrow> ntfnObj ntfn' = Structures_H.ActiveNtfn b)
                                      \<and> ntfn_bound_tcb ntfn = ntfnBoundTCB ntfn'
                                      \<and> ntfn_sc ntfn = ntfnSc ntfn'"

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
| "thread_state_relation (Structures_A.BlockedOnReply r) ts'
     = (ts' = Structures_H.BlockedOnReply (Some r))"
| "thread_state_relation (Structures_A.BlockedOnReceive oref reply sp) ts'
     = (ts' = Structures_H.BlockedOnReceive oref (receiver_can_grant sp) reply)"
| "thread_state_relation (Structures_A.BlockedOnSend oref sp) ts'
     = (ts' = Structures_H.BlockedOnSend oref (sender_badge sp)
                         (sender_can_grant sp) (sender_can_grant_reply sp) (sender_is_call sp))"
| "thread_state_relation (Structures_A.BlockedOnNotification oref) ts'
     = (ts' = Structures_H.BlockedOnNotification oref)"

definition arch_tcb_relation :: "Structures_A.arch_tcb \<Rightarrow> Structures_H.arch_tcb \<Rightarrow> bool" where
  "arch_tcb_relation \<equiv> \<lambda>atcb atcb'. tcb_context atcb = atcbContext atcb'"

definition tcb_relation :: "Structures_A.tcb \<Rightarrow> Structures_H.tcb \<Rightarrow> bool" where
  "tcb_relation \<equiv> \<lambda>tcb tcb'.
     tcb_ipc_buffer tcb = tcbIPCBuffer tcb'
  \<and> arch_tcb_relation (tcb_arch tcb) (tcbArch tcb')
  \<and> thread_state_relation (tcb_state tcb) (tcbState tcb')
  \<and> fault_rel_optionation (tcb_fault tcb) (tcbFault tcb')
  \<and> cap_relation (tcb_ctable tcb) (cteCap (tcbCTable tcb'))
  \<and> cap_relation (tcb_vtable tcb) (cteCap (tcbVTable tcb'))
  \<and> cap_relation (tcb_fault_handler tcb) (cteCap (tcbFaultHandler tcb'))
  \<and> cap_relation (tcb_timeout_handler tcb) (cteCap (tcbTimeoutHandler tcb'))
  \<and> cap_relation (tcb_ipcframe tcb) (cteCap (tcbIPCBufferFrame tcb'))
  \<and> tcb_bound_notification tcb = tcbBoundNotification tcb'
  \<and> tcb_sched_context tcb = tcbSchedContext tcb'
  \<and> tcb_yield_to tcb = tcbYieldTo tcb'
  \<and> tcb_mcpriority tcb = tcbMCP tcb'
  \<and> tcb_priority tcb = tcbPriority tcb'
  \<and> tcb_domain tcb = tcbDomain tcb'"

lemma sc_sporadic_flag_eq_schedContextSporadicFlag[simp]:
  "sc_sporadic_flag = schedContextSporadicFlag"
  by (simp add: sc_sporadic_flag_def schedContextSporadicFlag_def)

lemma minRefills_eq_MIN_REFILLS[simp]:
  "minRefills = MIN_REFILLS"
  by (clarsimp simp: minRefills_def MIN_REFILLS_def)

definition refill_map :: "Structures_H.refill \<Rightarrow> Structures_A.refill" where
  "refill_map refill \<equiv> \<lparr> r_time = rTime refill, r_amount = rAmount refill\<rparr>"


(* Assumes count \<le> mx; start \<le> mx; mx \<le> length xs
   Produces count elements from start, wrapping around to the beginning of the list at mx *)
definition wrap_slice :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "wrap_slice start count mx xs \<equiv> if start + count \<le> mx
                                   then take count (drop start xs)
                                   else take (mx - start) (drop start xs) @ take (start + count - mx) xs"

(* Sanity check: *)
lemma "wrap_slice 1 3 4 [1::nat,2,3,4,5,6] = [2,3,4]" by eval
lemma "wrap_slice 3 3 4 [1::nat,2,3,4,5,6] = [4,1,2]" by eval

lemma length_wrap_slice[simp]:
  "\<lbrakk> count \<le> mx; start \<le> mx; mx \<le> length xs \<rbrakk> \<Longrightarrow> length (wrap_slice start count mx xs) = count"
  by (simp add: wrap_slice_def)

lemma wrap_slice_empty[simp]:
  "start \<le> mx \<Longrightarrow> wrap_slice start 0 mx xs = []"
  by (clarsimp simp: wrap_slice_def)

lemma hd_wrap_slice:
  "\<lbrakk>0 < count; mx \<le> length list; start < mx\<rbrakk> \<Longrightarrow> hd (wrap_slice start count mx list) = list ! start"
  by (auto simp: wrap_slice_def hd_drop_conv_nth)

definition refills_map :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> refill list \<Rightarrow>  Structures_A.refill list" where
  "refills_map start count mx \<equiv> map refill_map \<circ> wrap_slice (min start mx) (min count mx) mx"

(* This leaves those Haskell refills unconstrained that are not in the abstract sc_refills list.
   This is intentional: for instance, refillPopHead will leave "garbage" behind in memory which
   is not captured on the abstract side, and we can't demand that the Haskell side has empty
   refills there. This should be fine, from concrete to abstract we still have a function. *)
definition sc_relation ::
  "Structures_A.sched_context \<Rightarrow> nat \<Rightarrow> Structures_H.sched_context \<Rightarrow> bool"
  where
  "sc_relation \<equiv> \<lambda>sc n sc'.
     sc_period sc = scPeriod sc' \<and>
     sc_consumed sc = scConsumed sc' \<and>
     sc_tcb sc = scTCB sc' \<and>
     sc_ntfn sc = scNtfn sc' \<and>
     sc_refills sc = refills_map (scRefillHead sc') (refillSize sc')
                                 (scRefillMax sc') (scRefills sc') \<and>
     n = scSize sc' \<and>
     sc_refill_max sc = scRefillMax sc' \<and>
     sc_badge sc = scBadge sc' \<and>
     sc_sporadic sc = scSporadic sc' \<and>
     sc_yield_from sc = scYieldFrom sc'"

(* projection rewrite *)

definition is_active_sc' where
  "is_active_sc' p s' \<equiv> ((\<lambda>sc'. 0 < scRefillMax sc') |< scs_of' s') p"

lemma active_sc_at'_imp_is_active_sc':
  "active_sc_at' scp s \<Longrightarrow> is_active_sc' scp s"
  by (clarsimp simp: active_sc_at'_def is_active_sc'_def obj_at'_def opt_map_def projectKO_eq
                     opt_pred_def)

lemma active_sc_at'_rewrite:
  "active_sc_at' scp s = (is_active_sc' scp s \<and> sc_at' scp s)"
  by (fastforce simp: active_sc_at'_def is_active_sc'_def obj_at'_def opt_map_def projectKO_eq
                      opt_pred_def)

(* valid_refills' *)

(* Most sched contexts should satisfy these conditions. These are the conditions we need for
   the refill list circular buffer to make sense. In other words, these are the constraints
   we expect for wrap_slice to give what we want. *)

abbreviation sc_valid_refills' :: "sched_context \<Rightarrow> bool" where
  "sc_valid_refills' sc \<equiv>
     scRefillMax sc \<le> length (scRefills sc)
     \<and> scRefillHead sc < scRefillMax sc \<and> scRefillTail sc < scRefillMax sc
     \<and> refillSize sc \<le> scRefillMax sc"

lemma refillNext_less_length_scRefills:
  "\<lbrakk>sc_valid_refills' sc; idx < scRefillMax sc\<rbrakk> \<Longrightarrow> refillNext sc idx < length (scRefills sc)"
  by (fastforce simp: refillNext_def split: if_splits)

definition valid_refills' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_refills' sc_ptr s' \<equiv> (sc_valid_refills' |< scs_of' s') sc_ptr"

lemma valid_refills'_nonzero_scRefillCount:
  "valid_refills' scp s' \<Longrightarrow> ((\<lambda>sc. 0 < refillSize sc) |< scs_of' s') scp"
  by (clarsimp simp: valid_refills'_def opt_pred_def refillSize_def split: option.splits)

lemma valid_objs'_valid_refills':
  "\<lbrakk>valid_objs' s'; sc_at' scp s'; is_active_sc' scp s'\<rbrakk> \<Longrightarrow> valid_refills' scp s'"
  apply (clarsimp simp: obj_at'_def projectKO_eq projectKO_opt_sc
                 split: option.split_asm)
  apply (case_tac ko; clarsimp)
  apply (erule (1) valid_objsE')
  by (clarsimp simp: valid_refills'_def valid_obj'_def valid_sched_context'_def opt_pred_def
                     is_active_sc'_def opt_map_red projectKO_opt_sc)

lemma
  valid_refills'_ksSchedulerAction_update[simp]:
  "valid_refills' scp (ksSchedulerAction_update g s) = valid_refills' scp s" and
  valid_refills'_ksReadyQueues_update[simp]:
  "valid_refills' scp (ksReadyQueues_update f s) = valid_refills' scp s" and
  valid_refills'_ksReadyQueuesL1Bitmap_update[simp]:
  "valid_refills' scp (ksReadyQueuesL1Bitmap_update f' s) = valid_refills' scp s" and
  valid_refills'_ksReadyQueuesL2Bitmap_update[simp]:
  "valid_refills' scp (ksReadyQueuesL2Bitmap_update f'' s) = valid_refills' scp s"
  by (clarsimp simp: valid_refills'_def)+

lemma maxReleaseTime_equiv:
  "maxReleaseTime = MAX_RELEASE_TIME"
  apply (clarsimp simp: maxReleaseTime_def MAX_RELEASE_TIME_def maxBound_max_word maxPeriodUs_def
                        usToTicks_def MAX_PERIOD_def)
  done

definition reply_relation :: "Structures_A.reply \<Rightarrow> Structures_H.reply \<Rightarrow> bool" where
  "reply_relation \<equiv> \<lambda>reply reply'.
     reply_sc reply = replySC reply' \<and> reply_tcb reply = replyTCB reply'"

\<comment> \<open>
  A pair of objects @{term "(obj, obj')"} should satisfy the following relation when, under further
  mild assumptions, a @{term corres_underlying} lemma for @{term "set_object obj"}
  and @{term "setObject obj'"} can be stated: see setObject_other_corres in KHeap_R.

  Scheduling context objects and reply objects do not satisfy this relation because of the
  reply stack (see sc_replies_relation below). TCBs do not satisfy this relation because the
  tcbSchedPrev and tcbSchedNext fields of a TCB are used to model the ready queues and the release
  queue, and so an update to such a field would correspond to an update to a ready queue or the
  release queue (see ready_queues_relation and release_queue_relation below).\<close>
definition
  other_obj_relation :: "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "other_obj_relation obj obj' \<equiv>
   (case (obj, obj') of
      (Endpoint ep, KOEndpoint ep') \<Rightarrow> ep_relation ep ep'
    | (Notification ntfn, KONotification ntfn') \<Rightarrow> ntfn_relation ntfn ntfn'
    | (ArchObj (RISCV64_A.ASIDPool ap), KOArch (KOASIDPool ap')) \<Rightarrow> asid_pool_relation ap ap'
    | _ \<Rightarrow> False)"

primrec pte_relation' :: "RISCV64_A.pte \<Rightarrow> RISCV64_H.pte \<Rightarrow> bool" where
  "pte_relation' RISCV64_A.InvalidPTE x =
     (x = RISCV64_H.InvalidPTE)"
| "pte_relation' (RISCV64_A.PageTablePTE ppn atts) x =
     (x = RISCV64_H.PageTablePTE (ucast ppn) (Global \<in> atts) \<and> Execute \<notin> atts \<and> User \<notin> atts)"
| "pte_relation' (RISCV64_A.PagePTE ppn atts rghts) x =
     (x = RISCV64_H.PagePTE (ucast ppn) (Global \<in> atts) (User \<in> atts) (Execute \<in> atts)
                            (vmrights_map rghts))"

definition pte_relation :: "pt_index \<Rightarrow> Structures_A.kernel_object \<Rightarrow> kernel_object \<Rightarrow> bool" where
 "pte_relation y \<equiv> \<lambda>ko ko'. \<exists>pt pte. ko = ArchObj (PageTable pt) \<and> ko' = KOArch (KOPTE pte)
                                      \<and> pte_relation' (pt y) pte"

primrec aobj_relation_cuts :: "RISCV64_A.arch_kernel_obj \<Rightarrow> machine_word \<Rightarrow> obj_relation_cuts" where
  "aobj_relation_cuts (DataPage dev sz) x =
     { (x + (n << pageBits), \<lambda>_ obj. obj = (if dev then KOUserDataDevice else KOUserData))
       | n. n < 2 ^ (pageBitsForSize sz - pageBits) }"
| "aobj_relation_cuts (RISCV64_A.ASIDPool pool) x =
     {(x, other_obj_relation)}"
| "aobj_relation_cuts (PageTable pt) x =
     (\<lambda>y. (x + (ucast y << pteBits), pte_relation y)) ` UNIV"

abbreviation sc_relation_cut :: "Structures_A.kernel_object \<Rightarrow> kernel_object \<Rightarrow> bool" where
  "sc_relation_cut obj obj' \<equiv>
  case (obj, obj') of
        (Structures_A.SchedContext sc n, KOSchedContext sc') \<Rightarrow> sc_relation sc n sc'
      | _ \<Rightarrow> False"

abbreviation reply_relation_cut :: "Structures_A.kernel_object \<Rightarrow> kernel_object \<Rightarrow> bool" where
  "reply_relation_cut obj obj' \<equiv>
  (case (obj, obj') of
        (Structures_A.Reply r, KOReply r') \<Rightarrow> reply_relation r r'
      | _ \<Rightarrow> False)"

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
| "obj_relation_cuts (Structures_A.SchedContext sc n) x =
     (if valid_sched_context_size n then {(x, sc_relation_cut)} else {(x, \<bottom>\<bottom>)})"
| "obj_relation_cuts (Structures_A.Reply _) x = {(x, reply_relation_cut)}"
| "obj_relation_cuts (ArchObj ao) x = aobj_relation_cuts ao x"

lemma obj_relation_cuts_def2:
  "obj_relation_cuts ko x =
   (case ko of CNode sz cs \<Rightarrow> if well_formed_cnode_n sz cs
                              then {(cte_map (x, y), cte_relation y) | y. y \<in> dom cs}
                              else {(x, \<bottom>\<bottom>)}
             | Structures_A.SchedContext sc n \<Rightarrow>
                 if valid_sched_context_size n then {(x, sc_relation_cut)} else {(x, \<bottom>\<bottom>)}
             | Structures_A.Reply reply \<Rightarrow> {(x, reply_relation_cut)}
             | TCB tcb \<Rightarrow> {(x, tcb_relation_cut)}
             | ArchObj (PageTable pt) \<Rightarrow> (\<lambda>y. (x + (ucast y << pteBits), pte_relation y)) ` UNIV
             | ArchObj (DataPage dev sz) \<Rightarrow>
                 {(x + (n << pageBits),  \<lambda>_ obj. obj =(if dev then KOUserDataDevice else KOUserData))
                  | n . n < 2 ^ (pageBitsForSize sz - pageBits) }
             | _ \<Rightarrow> {(x, other_obj_relation)})"
  by (simp split: Structures_A.kernel_object.split
                  RISCV64_A.arch_kernel_obj.split)

lemma obj_relation_cuts_def3:
  "obj_relation_cuts ko x =
   (case a_type ko of
      ACapTable n \<Rightarrow> {(cte_map (x, y), cte_relation y) | y. length y = n}
    | ASchedContext n \<Rightarrow>
        if valid_sched_context_size n then {(x, sc_relation_cut)} else {(x, \<bottom>\<bottom>)}
    | AReply \<Rightarrow> {(x, reply_relation_cut)}
    | ATCB \<Rightarrow> {(x, tcb_relation_cut)}
    | AArch APageTable \<Rightarrow> (\<lambda>y. (x + (ucast y << pteBits), pte_relation y)) ` UNIV
    | AArch (AUserData sz) \<Rightarrow> {(x + (n << pageBits), \<lambda>_ obj. obj = KOUserData)
                               | n . n < 2 ^ (pageBitsForSize sz - pageBits) }
    | AArch (ADeviceData sz) \<Rightarrow> {(x + (n << pageBits), \<lambda>_ obj. obj = KOUserDataDevice )
                                 | n . n < 2 ^ (pageBitsForSize sz - pageBits) }
    | AGarbage _ \<Rightarrow> {(x, \<bottom>\<bottom>)}
    | _ \<Rightarrow> {(x, other_obj_relation)})"
  by (simp add: obj_relation_cuts_def2 a_type_def well_formed_cnode_n_def length_set_helper
           split: Structures_A.kernel_object.split RISCV64_A.arch_kernel_obj.split)

definition is_other_obj_relation_type :: "a_type \<Rightarrow> bool" where
 "is_other_obj_relation_type tp \<equiv>
    case tp of
      ACapTable n \<Rightarrow> False
    | ASchedContext n \<Rightarrow> False
    | AReply \<Rightarrow> False
    | ATCB \<Rightarrow> False
    | AArch APageTable \<Rightarrow> False
    | AArch (AUserData _) \<Rightarrow> False
    | AArch (ADeviceData _) \<Rightarrow> False
    | AGarbage _ \<Rightarrow> False
    | _ \<Rightarrow> True"

lemma is_other_obj_relation_type_CapTable:
  "\<not> is_other_obj_relation_type (ACapTable n)"
  by (simp add: is_other_obj_relation_type_def)

lemma is_other_obj_relation_type_SchedContext:
  "\<not> is_other_obj_relation_type (ASchedContext n)"
  by (simp add: is_other_obj_relation_type_def)

lemma is_other_obj_relation_type_Reply:
  "\<not> is_other_obj_relation_type AReply"
  by (simp add: is_other_obj_relation_type_def)

lemma is_other_obj_relation_type_TCB:
  "\<not> is_other_obj_relation_type ATCB"
  by (simp add: is_other_obj_relation_type_def)

lemma is_other_obj_relation_type_UserData:
  "\<not> is_other_obj_relation_type (AArch (AUserData sz))"
  unfolding is_other_obj_relation_type_def by simp

lemma is_other_obj_relation_type_DeviceData:
  "\<not> is_other_obj_relation_type (AArch (ADeviceData sz))"
  unfolding is_other_obj_relation_type_def by simp

lemma is_other_obj_relation_type:
  "is_other_obj_relation_type (a_type ko) \<Longrightarrow> obj_relation_cuts ko x = {(x, other_obj_relation)}"
  by (simp add: obj_relation_cuts_def3 is_other_obj_relation_type_def
           split: a_type.splits aa_type.splits)

definition pspace_dom :: "Structures_A.kheap \<Rightarrow> machine_word set" where
  "pspace_dom ps \<equiv> \<Union>x\<in>dom ps. fst ` (obj_relation_cuts (the (ps x)) x)"

definition pspace_relation ::
  "Structures_A.kheap \<Rightarrow> (machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> bool" where
  "pspace_relation ab con \<equiv>
     (pspace_dom ab = dom con) \<and>
     (\<forall>x \<in> dom ab. \<forall>(y, P) \<in> obj_relation_cuts (the (ab x)) x. P (the (ab x)) (the (con y)))"

definition sc_replies_relation_2 ::
  "(obj_ref \<rightharpoonup> obj_ref list) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> bool"
  where
  "sc_replies_relation_2 sc_repls scRepl replPrevs \<equiv>
     \<forall>p replies. sc_repls p = Some replies \<longrightarrow> heap_ls replPrevs (scRepl p) replies"

abbreviation sc_replies_relation :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "sc_replies_relation s s' \<equiv>
    sc_replies_relation_2 (sc_replies_of s) (scReplies_of s') (replyPrevs_of s')"

lemmas sc_replies_relation_def = sc_replies_relation_2_def

abbreviation sc_replies_relation_obj ::
  "Structures_A.kernel_object \<Rightarrow> kernel_object \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> bool"
  where
  "sc_replies_relation_obj obj obj' nexts \<equiv>
   case (obj, obj') of
     (Structures_A.SchedContext sc _, KOSchedContext sc') \<Rightarrow>
       heap_ls nexts (scReply sc') (sc_replies sc)"

primrec sched_act_relation :: "Structures_A.scheduler_action \<Rightarrow> scheduler_action \<Rightarrow> bool" where
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

definition release_queue_relation_2 ::
  "obj_ref list \<Rightarrow> tcb_queue \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<Rightarrow> bool)
   \<Rightarrow> bool"
  where
  "release_queue_relation_2 ls q nexts prevs flags \<equiv>
     list_queue_relation ls q nexts prevs
     \<and> (\<forall>t. flags t \<longleftrightarrow> t \<in> set ls)"

abbreviation release_queue_relation :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "release_queue_relation s s' \<equiv>
     release_queue_relation_2
      (release_queue s) (ksReleaseQueue s') (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
      (tcbInReleaseQueue |< tcbs_of' s')"

lemmas release_queue_relation_def = release_queue_relation_2_def

definition ghost_relation ::
  "Structures_A.kheap \<Rightarrow> (machine_word \<rightharpoonup> vmpage_size) \<Rightarrow> (machine_word \<rightharpoonup> nat) \<Rightarrow> bool" where
  "ghost_relation h ups cns \<equiv>
     (\<forall>a sz. (\<exists>dev. h a = Some (ArchObj (DataPage dev sz))) \<longleftrightarrow> ups a = Some sz) \<and>
     (\<forall>a n. (\<exists>cs. h a = Some (CNode n cs) \<and> well_formed_cnode_n n cs) \<longleftrightarrow> cns a = Some n)"

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
   | _ \<Rightarrow> False"

definition interrupt_state_relation ::
  "(irq \<Rightarrow> obj_ref) \<Rightarrow> (irq \<Rightarrow> irq_state) \<Rightarrow> interrupt_state \<Rightarrow> bool" where
  "interrupt_state_relation node_map irqs is \<equiv>
     (\<exists>node irqs'. is = InterruptState node irqs'
                    \<and> (\<forall>irq. node_map irq = node + (ucast irq << cte_level_bits))
                    \<and> (\<forall>irq. irq_state_relation (irqs irq) (irqs' irq)))"

definition arch_state_relation :: "(arch_state \<times> RISCV64_H.kernel_state) set" where
  "arch_state_relation \<equiv> {(s, s') .
         riscv_asid_table s = riscvKSASIDTable s' o ucast
         \<and> riscv_global_pts s = (\<lambda>l. set (riscvKSGlobalPTs s' (size l)))
         \<and> riscv_kernel_vspace s = riscvKSKernelVSpace s'}"

definition rights_mask_map :: "rights set \<Rightarrow> Types_H.cap_rights" where
  "rights_mask_map \<equiv>
     \<lambda>rs. CapRights (AllowWrite \<in> rs) (AllowRead \<in> rs) (AllowGrant \<in> rs) (AllowGrantReply \<in> rs)"

lemma obj_relation_cutsE:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; P ko ko';
     \<And>sz cs z cap cte. \<lbrakk> ko = CNode sz cs; well_formed_cnode_n sz cs; y = cte_map (x, z);
                         ko' = KOCTE cte; cs z = Some cap; cap_relation cap (cteCap cte) \<rbrakk>
              \<Longrightarrow> R;
     \<And>sc n sc'. \<lbrakk> y = x; ko = Structures_A.SchedContext sc n; valid_sched_context_size n;
                      ko' = KOSchedContext sc'; sc_relation sc n sc' \<rbrakk>
              \<Longrightarrow> R;
     \<And>reply reply'. \<lbrakk> y = x; ko = Structures_A.Reply reply;
                      ko' = KOReply reply'; reply_relation reply reply' \<rbrakk>
              \<Longrightarrow> R;
     \<And>tcb tcb'. \<lbrakk> y = x; ko = TCB tcb; ko' = KOTCB tcb'; tcb_relation tcb tcb' \<rbrakk>
              \<Longrightarrow> R;
     \<And>pt (z :: pt_index) pte'. \<lbrakk> ko = ArchObj (PageTable pt); y = x + (ucast z << pteBits);
                                 ko' = KOArch (KOPTE pte'); pte_relation' (pt z) pte' \<rbrakk>
              \<Longrightarrow> R;
     \<And>sz dev n. \<lbrakk> ko = ArchObj (DataPage dev sz);
                  ko' = (if dev then KOUserDataDevice else KOUserData);
                  y = x + (n << pageBits); n < 2 ^ (pageBitsForSize sz - pageBits) \<rbrakk> \<Longrightarrow> R;
            \<lbrakk> y = x; other_obj_relation ko ko'; is_other_obj_relation_type (a_type ko) \<rbrakk> \<Longrightarrow> R
    \<rbrakk> \<Longrightarrow> R"
  apply (simp add: obj_relation_cuts_def2 is_other_obj_relation_type_def
                   a_type_def tcb_relation_cut_def
            split: Structures_A.kernel_object.split_asm if_split_asm
                   RISCV64_A.arch_kernel_obj.split_asm)
  by (clarsimp split: if_splits kernel_object.split_asm,
      clarsimp simp: cte_relation_def pte_relation_def
                     reply_relation_def sc_relation_def)+

lemma eq_trans_helper:
  "\<lbrakk> x = y; P y = Q \<rbrakk> \<Longrightarrow> P x = Q"
  by simp

lemma cap_relation_case':
  "cap_relation cap cap' = (case cap of
                              cap.ArchObjectCap arch_cap.ASIDControlCap \<Rightarrow> cap_relation cap cap'
                            | _ \<Rightarrow> cap_relation cap cap')"
  by (simp split: cap.split arch_cap.split)

schematic_goal cap_relation_case:
  "cap_relation cap cap' = ?P"
  apply (subst cap_relation_case')
  apply (clarsimp cong: cap.case_cong arch_cap.case_cong)
  apply (rule refl)
  done

lemmas cap_relation_split =
  eq_trans_helper [where P=P, OF cap_relation_case cap.split[where P=P]] for P
lemmas cap_relation_split_asm =
  eq_trans_helper [where P=P, OF cap_relation_case cap.split_asm[where P=P]] for P

text \<open> Relations on other data types that aren't stored but used as intermediate values
       in the specs. \<close>
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

definition APIType_map :: "Structures_A.apiobject_type \<Rightarrow> RISCV64_H.object_type" where
  "APIType_map ty \<equiv>
     case ty of
       Structures_A.Untyped \<Rightarrow> APIObjectType ArchTypes_H.Untyped
     | Structures_A.TCBObject \<Rightarrow> APIObjectType ArchTypes_H.TCBObject
     | Structures_A.EndpointObject \<Rightarrow> APIObjectType ArchTypes_H.EndpointObject
     | Structures_A.NotificationObject \<Rightarrow> APIObjectType ArchTypes_H.NotificationObject
     | Structures_A.CapTableObject \<Rightarrow> APIObjectType ArchTypes_H.CapTableObject
     | ArchObject ao \<Rightarrow> (case ao of
                           SmallPageObj \<Rightarrow> SmallPageObject
                         | LargePageObj \<Rightarrow> LargePageObject
                         | HugePageObj  \<Rightarrow> HugePageObject
                         | PageTableObj \<Rightarrow> PageTableObject)"

definition state_relation :: "(det_state \<times> kernel_state) set" where
  "state_relation \<equiv> {(s, s').
         pspace_relation (kheap s) (ksPSpace s')
       \<and> sc_replies_relation s s'
       \<and> sched_act_relation (scheduler_action s) (ksSchedulerAction s')
       \<and> ready_queues_relation s s'
       \<and> release_queue_relation s s'
       \<and> ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')
       \<and> cdt_relation (swp cte_at s) (cdt s) (ctes_of s')
       \<and> cdt_list_relation (cdt_list s) (cdt s) (ctes_of s')
       \<and> revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) (ctes_of s')
       \<and> (arch_state s, ksArchState s') \<in> arch_state_relation
       \<and> interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s')
       \<and> (cur_thread s = ksCurThread s')
       \<and> (idle_thread s = ksIdleThread s')
       \<and> (idle_sc_ptr = ksIdleSC s')
       \<and> (machine_state s = ksMachineState s')
       \<and> (work_units_completed s = ksWorkUnitsCompleted s')
       \<and> (domain_index s = ksDomScheduleIdx s')
       \<and> (domain_list s = ksDomSchedule s')
       \<and> (cur_domain s = ksCurDomain s')
       \<and> (domain_time s = ksDomainTime s')
       \<and> (consumed_time s = ksConsumedTime s')
       \<and> (cur_time s = ksCurTime s')
       \<and> (cur_sc s = ksCurSc s')
       \<and> (reprogram_timer s = ksReprogramTimer s')}"


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
  by (simp add: state_relation_def)

lemma state_relation_ready_queues_relation[elim!]:
  "(s, s') \<in> state_relation \<Longrightarrow> ready_queues_relation s s'"
  by (simp add: state_relation_def)

lemma state_relation_release_queue_relation[elim!]:
  "(s,s') \<in> state_relation \<Longrightarrow> release_queue_relation s s'"
  by (clarsimp simp: state_relation_def)

lemma state_relation_sc_replies_relation:
  "(s,s') \<in> state_relation \<Longrightarrow> sc_replies_relation s s'"
  using state_relation_def by blast

lemma state_relation_idle_thread[elim!]:
  "(s, s') \<in> state_relation \<Longrightarrow> idle_thread s = ksIdleThread s'"
  by (clarsimp simp: state_relation_def)

lemma state_relationD:
  assumes sr:  "(s, s') \<in> state_relation"
  shows "pspace_relation (kheap s) (ksPSpace s') \<and>
  sc_replies_relation s s' \<and>
  sched_act_relation (scheduler_action s) (ksSchedulerAction s') \<and>
  ready_queues_relation s s' \<and>
  release_queue_relation s s' \<and>
  ghost_relation (kheap s) (gsUserPages s') (gsCNodes s') \<and>
  cdt_relation (swp cte_at s) (cdt s) (ctes_of s') \<and>
  cdt_list_relation (cdt_list s) (cdt s) (ctes_of s') \<and>
  revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) (ctes_of s') \<and>
  (arch_state s, ksArchState s') \<in> arch_state_relation \<and>
  interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s') \<and>
  cur_thread s = ksCurThread s' \<and>
  idle_thread s = ksIdleThread s' \<and>
  idle_sc_ptr = ksIdleSC s' \<and>
  machine_state s = ksMachineState s' \<and>
  work_units_completed s = ksWorkUnitsCompleted s' \<and>
  domain_index s = ksDomScheduleIdx s' \<and>
  domain_list s = ksDomSchedule s' \<and>
  cur_domain s = ksCurDomain s' \<and>
  domain_time s = ksDomainTime s' \<and>
  consumed_time s = ksConsumedTime s' \<and>
  cur_time s = ksCurTime s' \<and>
  cur_sc s = ksCurSc s' \<and>
  reprogram_timer s = ksReprogramTimer s'"
  using sr unfolding state_relation_def by simp

lemma state_relationE [elim?]:
  assumes sr:  "(s, s') \<in> state_relation"
  and rl: "\<lbrakk>pspace_relation (kheap s) (ksPSpace s');
            sc_replies_relation s s';
            sched_act_relation (scheduler_action s) (ksSchedulerAction s');
            ready_queues_relation s s';
            release_queue_relation s s';
            ghost_relation (kheap s) (gsUserPages s') (gsCNodes s');
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
            domain_list s = ksDomSchedule s';
            cur_domain s = ksCurDomain s';
            domain_time s = ksDomainTime s';
            consumed_time s = ksConsumedTime s';
            cur_time s = ksCurTime s';
            cur_sc s = ksCurSc s';
            reprogram_timer s = ksReprogramTimer s' \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using sr by (blast intro!: rl dest: state_relationD)

lemmas isCap_defs =
  isZombie_def isArchObjectCap_def
  isThreadCap_def isCNodeCap_def isNotificationCap_def
  isEndpointCap_def isUntypedCap_def isNullCap_def
  isIRQHandlerCap_def isIRQControlCap_def isReplyCap_def
  isSchedContextCap_def isSchedControlCap_def
  isFrameCap_def isPageTableCap_def
  isASIDControlCap_def isASIDPoolCap_def
  isDomainCap_def isArchFrameCap_def

lemma isCNodeCap_cap_map[simp]:
  "cap_relation c c' \<Longrightarrow> isCNodeCap c' = is_cnode_cap c"
  by (cases c) (auto simp: isCap_defs split: sum.splits)

lemma cap_rel_valid_fh:
  "cap_relation a b \<Longrightarrow> valid_fault_handler a = isValidFaultHandler b"
  apply (case_tac a ; case_tac b; simp add: valid_fault_handler_def isValidFaultHandler_def)
  apply (rule iffI; clarsimp simp: has_handler_rights_def split: bool.split_asm)
  done

lemma sts_rel_idle :
  "thread_state_relation st IdleThreadState = (st = Structures_A.IdleThreadState)"
  by (cases st, auto)

lemma sts_rel_runnable :
  "\<lbrakk>thread_state_relation st st'; runnable st\<rbrakk> \<Longrightarrow> runnable' st'"
  by (cases st, auto)

lemma sts_rel_activatable:
  "\<lbrakk>thread_state_relation st st'; activatable st\<rbrakk> \<Longrightarrow> activatable' st'"
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

lemma pspace_relation_None:
  "\<lbrakk>pspace_relation p p'; p' ptr = None \<rbrakk> \<Longrightarrow> p ptr = None"
  apply (rule not_Some_eq[THEN iffD1, OF allI, OF notI])
  apply (drule(1) pspace_relation_absD)
   apply (case_tac y; clarsimp simp: cte_map_def of_bl_def well_formed_cnode_n_def split: if_splits)
   subgoal for n
    apply (drule spec[of _ ptr])
    apply (drule spec)
    apply clarsimp
    apply (drule spec[of _ "replicate n False"])
    apply (drule mp[OF _ refl])
     apply (drule mp)
    subgoal premises by (induct n; simp)
    apply clarsimp
    done
  subgoal for x
     apply (cases x; clarsimp)
   apply ((drule spec[of _ 0], fastforce)+)[2]
   apply (drule spec[of _ ptr])
   apply (drule spec)
   apply clarsimp
   apply (drule mp[OF _ refl])
   apply (drule spec[of _ 0])
   subgoal for _ sz by (cases sz; simp add: ptTranslationBits_def)
   done
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

lemma ghost_relation_typ_at:
  "ghost_relation (kheap s) ups cns \<equiv>
     (\<forall>a sz. data_at sz a s = (ups a = Some sz)) \<and>
     (\<forall>a n. typ_at (ACapTable n) a s = (cns a = Some n))"
  apply (rule eq_reflection)
  apply (clarsimp simp: ghost_relation_def typ_at_eq_kheap_obj data_at_def)
  apply (intro conjI impI iffI allI; force)
  done

(* more replyNext/replyPrev related lemmas *)

lemma sc_replies_relation_replyNext_None:
  "\<lbrakk>sc_replies_relation s s'; reply_at rp s; replies_of' s' rp \<noteq> None;
    \<forall>p'. replyPrevs_of s' p' \<noteq> Some rp; \<forall>p'. scReplies_of s' p' \<noteq> Some rp\<rbrakk>
     \<Longrightarrow> sc_replies_relation s (s'\<lparr>ksPSpace := (ksPSpace s')(rp \<mapsto> KOReply r)\<rparr>)"
  apply (clarsimp simp: sc_replies_relation_def)
  apply (rename_tac scp replies)
  apply (drule_tac x=scp and y=replies in spec2)
  apply simp
  apply (clarsimp simp: projectKO_opts_defs obj_at'_def opt_map_red obj_at_def is_reply vs_all_heap_simps)
  apply (rename_tac ko scp sc reply n)
  apply (case_tac ko; clarsimp)
  apply (intro conjI; clarsimp)
  apply (rename_tac sc reply n)
  apply (rule heap_path_heap_upd_not_in, simp)
  apply clarsimp
  apply (frule split_list)
  apply (elim exE)
  apply (simp only:)
  apply (case_tac ys; simp only:)
   apply (clarsimp simp: opt_map_red)
  apply (prop_tac "\<exists>ls x. a # list = ls @ [x]")
   using append_butlast_last_id apply fastforce
  apply (elim exE conjE, simp only:)
  apply (prop_tac "(ls @ [x]) @ rp # zs = ls @ x # rp # zs", simp)
  apply (simp only:)
  apply (frule_tac z=x in heap_path_non_nil_lookup_next)
  apply (clarsimp simp: opt_map_red)
  done

lemma sc_replies_relation_scReplies_of:
  "\<lbrakk>sc_replies_relation s s'; sc_at sc_ptr s; bound (scs_of' s' sc_ptr)\<rbrakk>
   \<Longrightarrow> (sc_replies_of s |> hd_opt) sc_ptr = scReplies_of s' sc_ptr"
  by (fastforce simp: sc_replies_relation_def sc_replies_of_scs_def scs_of_kh_def map_project_def
                      hd_opt_def obj_at_def is_sc_obj_def opt_map_def
               split: option.splits Structures_A.kernel_object.splits list.splits)

lemma sc_replies_prevs_walk:
  "\<lbrakk> sc_replies_relation s s';
     ksPSpace s' p = Some (KOSchedContext sc'); kheap s p = Some (kernel_object.SchedContext sc n) \<rbrakk>
   \<Longrightarrow> heap_walk (replyPrevs_of s') (scReply sc') [] = sc_replies sc"
  unfolding sc_replies_relation_def
  apply (erule_tac x=p in allE)
  apply (erule_tac x="sc_replies sc" in allE)
  apply (clarsimp simp: sc_replies.all_simps)
  apply (rule heap_ls_is_walk)
  apply (subgoal_tac "scReplies_of s' p = scReply sc'", simp)
  apply (clarsimp simp: opt_map_def projectKO_opt_sc)
  done

lemma sc_replies_relation_prevs_list:
  "\<lbrakk> sc_replies_relation s s';
     kheap s x = Some (kernel_object.SchedContext sc n);
     ksPSpace s' x = Some (KOSchedContext sc')\<rbrakk>
    \<Longrightarrow> heap_ls (replyPrevs_of s') (scReply sc') (sc_replies sc)"
  apply (clarsimp simp: sc_replies_relation_def sc_replies_of_scs_def scs_of_kh_def map_project_def)
  apply (drule_tac x=x and y="sc_replies sc" in spec2)
  apply (clarsimp simp: opt_map_def projectKO_opt_sc split: option.splits)
  done

lemma list_refs_of_replies'_reftype[simp]:
  "(p, reftype) \<in> list_refs_of_replies' s' p' \<Longrightarrow> reftype \<in> {ReplyPrev, ReplyNext}"
  by (clarsimp simp: list_refs_of_replies'_def list_refs_of_reply'_def get_refs_def2 opt_map_def
              split: option.split_asm)

lemma replyNext_replyNexts_of_opt_map:
  "\<lbrakk>ksPSpace s' p = Some (KOReply reply); replyNext reply = Some (Next p')\<rbrakk>
    \<Longrightarrow> (replyNexts_of s' |> f s') p = f s' p'"
  by (clarsimp simp: opt_map_red projectKO_opt_reply split: option.split)

lemma replyPrevs_of_refs:
  "replyPrevs_of s' p = Some p' \<longleftrightarrow> (p', ReplyPrev) \<in> list_refs_of_replies' s' p"
  by (fastforce simp: map_set_def list_refs_of_reply'_def opt_map_def get_refs_def
               split: option.splits)

lemma replyNexts_of_refs:
  "replyNexts_of s' p = Some p' \<longleftrightarrow> (p', ReplyNext) \<in> list_refs_of_replies' s' p"
  by (fastforce simp: map_set_def list_refs_of_reply'_def opt_map_def get_refs_def
               split: option.splits)

lemma sym_replies_prev_then_next_id_p:
  "\<lbrakk>sym_refs (list_refs_of_replies' s'); replyPrevs_of s' p = Some p'\<rbrakk>
   \<Longrightarrow> (replyPrevs_of s' |> replyNexts_of s') p = Some p"
  apply (clarsimp simp: replyPrevs_of_refs replyNexts_of_refs opt_map_red)
  by (drule (1) sym_refsD[rotated], simp)

lemma sym_replies_next_then_prev_id_p:
  "\<lbrakk>sym_refs (list_refs_of_replies' s'); replyNexts_of s' p = Some p'\<rbrakk>
   \<Longrightarrow> (replyNexts_of s' |> replyPrevs_of s') p = Some p"
  supply opt_map_red[simp]
  apply (clarsimp simp: replyPrevs_of_refs replyNexts_of_refs)
  by (drule (1) sym_refsD[rotated], simp)

(* Some results related to the size of scheduling contexts *)

lemma sc_const_eq:
  "refillSizeBytes = (refill_size_bytes::nat)"
  "schedContextStructSize = sizeof_sched_context_t"
  "minSchedContextBits = min_sched_context_bits"
  by (auto simp: refillSizeBytes_def refill_size_bytes_def minSchedContextBits_def
                 wordSize_def wordBits_def' word_size_def
                 sizeof_sched_context_t_def min_sched_context_bits_def schedContextStructSize_def)

lemma max_num_refills_eq_refillAbsoluteMax':
  "max_num_refills = refillAbsoluteMax'"
  by (rule ext)
     (simp add: max_num_refills_def refillAbsoluteMax'_def shiftL_nat sc_const_eq)

lemma maxUntyped_eq:
  "untyped_max_bits = maxUntypedSizeBits"
  by (simp add: untyped_max_bits_def maxUntypedSizeBits_def)

lemmas sc_const_conc = sc_const_eq[symmetric] max_num_refills_eq_refillAbsoluteMax' maxUntyped_eq

lemma refillAbsoluteMax'_mono:
  fixes x y
  assumes "minSchedContextBits \<le> x"
    and "x \<le> y"
  shows "refillAbsoluteMax' x \<le> refillAbsoluteMax' y"
proof -
  show ?thesis
    unfolding refillAbsoluteMax'_def
    using assms
    by (simp add: diff_le_mono div_le_mono shiftL_nat)
qed

lemmas scBits_simps = refillAbsoluteMax_def sc_size_bounds_def sc_const_conc

lemma minSchedContextBits_check:
  "minSchedContextBits = (LEAST n. schedContextStructSize + MIN_REFILLS * refillSizeBytes \<le> 2 ^ n)"
proof -
  note simps = minSchedContextBits_def sc_const_eq(2) sizeof_sched_context_t_def word_size_def
               MIN_REFILLS_def refillSizeBytes_def
  show ?thesis
    apply (rule sym)
    apply (rule Least_equality)
     apply (clarsimp simp: simps)
    apply (rename_tac n)
    apply (rule ccontr)
    apply (simp add: not_le)
    apply (prop_tac "2 ^ n \<le> 2 ^ (minSchedContextBits - 1)")
     apply (fastforce intro: power_increasing_iff[THEN iffD2])
    using less_le_trans
    by (fastforce simp: simps)
qed

lemma minSchedContextBits_rel:
  "schedContextStructSize + MIN_REFILLS * refillSizeBytes \<le> 2 ^ minSchedContextBits"
  apply (simp add: minSchedContextBits_check)
  by (meson self_le_ge2_pow order_refl wellorder_Least_lemma(1))

lemma refillAbsoluteMax'_greatest:
  assumes "schedContextStructSize \<le> 2 ^ n"
  shows "refillAbsoluteMax' n = (GREATEST r. schedContextStructSize + r * refillSizeBytes \<le> 2 ^ n)"
  apply (simp flip: max_num_refills_eq_refillAbsoluteMax'
               add: max_num_refills_def scBits_simps(4) scBits_simps(3))
  apply (rule sym)
  apply (rule Greatest_equality)
   apply (metis assms le_diff_conv2 le_imp_diff_is_add div_mult_le le_add1 diff_add_inverse)
  apply (rename_tac r)
  apply (prop_tac "r * refillSizeBytes \<le> 2 ^ n - schedContextStructSize")
   apply linarith
  apply (drule_tac k=refillSizeBytes in div_le_mono)
  by (simp add: refillSizeBytes_def)

lemma refillAbsoluteMax'_leq:
  "schedContextStructSize \<le> 2 ^ n \<Longrightarrow>
   schedContextStructSize + refillAbsoluteMax' n * refillSizeBytes \<le> 2 ^ n"
  apply (frule refillAbsoluteMax'_greatest)
   apply (simp add: refillSizeBytes_def)
  apply (rule_tac b="2 ^ n" in GreatestI_ex_nat)
   apply presburger
  by fastforce

lemma schedContextStructSize_minSchedContextBits:
  "schedContextStructSize \<le> 2 ^ minSchedContextBits"
  apply (insert minSchedContextBits_check)
  by (metis LeastI_ex add_leD1 le_refl self_le_ge2_pow)

lemma MIN_REFILLS_refillAbsoluteMax'[simp]:
  "minSchedContextBits \<le> us \<Longrightarrow> MIN_REFILLS \<le> refillAbsoluteMax' us"
  apply (insert minSchedContextBits_rel)
  apply (frule_tac b1=2 in power_increasing_iff[THEN iffD2, rotated])
   apply fastforce
  apply (subst refillAbsoluteMax'_greatest)
   apply (insert schedContextStructSize_minSchedContextBits)
   apply (fastforce elim!: order_trans)
  apply (rule_tac b="2 ^ us" in Greatest_le_nat)
   apply (fastforce intro: order_trans)
  apply (clarsimp simp: refillSizeBytes_def)
  done

lemma length_scRefills_bounded:
  "\<lbrakk>valid_sched_context' sc s; valid_sched_context_size' sc\<rbrakk>
   \<Longrightarrow> refillSizeBytes * length (scRefills sc) < 2 ^ word_bits"
  apply (clarsimp simp: valid_sched_context_size'_def sc_size_bounds_def objBits_simps
                        valid_sched_context'_def)
  apply (insert schedContextStructSize_minSchedContextBits)
  apply (prop_tac "schedContextStructSize \<le> 2 ^ (minSchedContextBits + scSize sc)")
   apply (fastforce intro: order_trans)
  apply (frule_tac n="minSchedContextBits + scSize sc" in refillAbsoluteMax'_leq)
  apply (rule_tac y="2 ^ (minSchedContextBits + scSize sc)" in le_less_trans)
   apply (clarsimp simp: refillSizeBytes_def)
  apply simp
  apply (clarsimp simp add: word_bits_def untypedBits_defs)
  done

lemma scBits_pos_power2:
  assumes "minSchedContextBits + scSize sc < word_bits"
  shows "(1::machine_word) < (2::machine_word) ^ (minSchedContextBits + scSize sc)"
  apply (insert assms)
  apply (subst word_less_nat_alt)
  apply (clarsimp simp: minSchedContextBits_def)
  by (auto simp: pow_mono_leq_imp_lt)

lemma objBits_pos_power2[simp]:
  assumes "objBits v < word_bits"
  shows "(1::machine_word) < (2::machine_word) ^ objBits v"
  unfolding objBits_simps'
  apply (insert assms)
  apply (case_tac "injectKO v"; simp)
  by (simp add: pageBits_def pteBits_def objBits_simps scBits_pos_power2
         split: arch_kernel_object.split)+

lemma objBitsKO_no_overflow[simp, intro!]:
  "objBitsKO ko < word_bits \<Longrightarrow> (1::machine_word) < (2::machine_word)^(objBitsKO ko)"
  by (cases ko; simp add: objBits_simps' pageBits_def pteBits_def scBits_pos_power2
                   split: arch_kernel_object.splits)

(* for handling refill buffer *)

abbreviation replaceAt where
  "replaceAt i xs new \<equiv> updateAt i xs (\<lambda>_. new)"

lemmas replaceAt_def = updateAt_def

lemma length_updateAt[simp]:
  "length (updateAt i xs f) = length xs"
  apply (clarsimp simp: updateAt_def)
  by (case_tac xs; simp)

lemma wrap_slice_index:
  "\<lbrakk>count \<le> mx; start < mx; mx \<le> length xs; index < count\<rbrakk>
   \<Longrightarrow> (wrap_slice start count mx xs) ! index
       = (if start + index < mx
             then (xs ! (start + index))
             else (xs ! (start + index - mx)))"
  apply (clarsimp split: if_splits)
  apply (intro conjI)
   apply (clarsimp simp: wrap_slice_def)
   apply (prop_tac "index < mx - start", linarith)
   apply (prop_tac "(take (mx - start) (drop start xs) @ take (start + count - mx) xs) ! index
                    = (take (mx - start) (drop start xs)) ! index")
    apply (simp add: nth_append)
   apply fastforce
  apply (clarsimp simp: wrap_slice_def)
  apply (cases "index < mx - start")
   apply linarith
  apply (drule not_less[THEN iffD1])+
  apply (prop_tac "(take (mx - start) (drop start xs) @ take (start + count - mx) xs) ! index
                   = (take (start + count - mx) xs) ! (index - (mx - start))")
   apply (prop_tac "mx - start \<le> index", linarith)
   apply (simp add: nth_append)
  using less_imp_le_nat nat_le_iff_add apply auto
  done

lemma wrap_slice_append:
  "\<lbrakk>Suc count \<le> mx; start < mx; mx \<le> length xs\<rbrakk>
   \<Longrightarrow> wrap_slice start (Suc count) mx xs
       = wrap_slice start count mx xs @ [if (start + count < mx)
                                            then (xs ! (start + count))
                                            else (xs ! (start + count - mx))]"
  apply (rule nth_equalityI)
   apply simp
  apply (rename_tac i)
  apply (case_tac "i < count")
   apply (prop_tac "(wrap_slice start count mx xs
                     @ [if start + count < mx
                           then xs ! (start + count)
                           else xs ! (start + count - mx)]) ! i
                    = (wrap_slice start count mx xs) ! i")
    apply (metis length_wrap_slice Suc_leD less_imp_le_nat nth_append)
   apply (simp add: wrap_slice_index)
  apply (prop_tac "(wrap_slice start count mx xs
                    @ [if start + count < mx
                          then xs ! (start + count)
                          else xs ! (start + count - mx)]) ! i
                   = (if start + count < mx
                         then xs ! (start + count)
                         else xs ! (start + count - mx))")
   apply (clarsimp simp: nth_append)
  apply (simp add: wrap_slice_index)
  apply (prop_tac "i = count", linarith)
  apply simp
  done

lemma updateAt_index:
  "\<lbrakk>xs \<noteq> []; i < length xs; j < length xs\<rbrakk>
   \<Longrightarrow> (updateAt i xs f) ! j = (if i = j then f (xs ! i) else (xs ! j))"
  by (fastforce simp: updateAt_def null_def nth_append)

lemma wrap_slice_updateAt_eq:
  "\<lbrakk>if start + count \<le> mx
       then (i < start \<or> start + count \<le> i)
       else (start + count - mx \<le> i \<and> i < start);
    count \<le> mx; start < mx; mx \<le> length xs; xs \<noteq> []; i < mx\<rbrakk>
   \<Longrightarrow> wrap_slice start count mx xs = wrap_slice start count mx (updateAt i xs new)"
  apply (rule nth_equalityI)
   apply clarsimp
  by (subst wrap_slice_index; clarsimp simp: updateAt_index split: if_split_asm)+

lemma take_updateAt_eq[simp]:
  "n \<le> i \<Longrightarrow> take n (updateAt i ls f) = take n ls"
  by (clarsimp simp: updateAt_def)

lemma refills_tl_equal:
  "\<lbrakk>sc_relation sc n sc'; sc_valid_refills' sc'\<rbrakk>
   \<Longrightarrow> refill_tl sc = refill_map (refillTl sc')"
  apply (clarsimp simp: sc_relation_def refillTl_def refills_map_def)
  apply (subst last_conv_nth)
  apply (metis refillSize_def add_is_0 length_wrap_slice less_or_eq_imp_le list.map_disc_iff
               list.size(3) zero_neq_one)
  apply (subst nth_map)
   apply (clarsimp simp: refillSize_def)
  apply (fastforce simp: wrap_slice_index refillSize_def)
  done

(* wrap_slice *)
lemma wrap_slice_start_0:
  "\<lbrakk>0 < count; mx \<le> length ls; count \<le> mx\<rbrakk> \<Longrightarrow> wrap_slice 0 count mx ls = take count ls"
  by (clarsimp simp: wrap_slice_def)

lemma butlast_wrap_slice:
  "\<lbrakk>0 < count; start < mx; count \<le> mx; mx \<le> length list\<rbrakk> \<Longrightarrow>
   butlast (wrap_slice start count mx list) =  wrap_slice start (count -1) mx list"
  by (case_tac "start + count - 1 < mx"; clarsimp simp: wrap_slice_def butlast_conv_take add_ac)

lemma last_wrap_slice:
  "\<lbrakk>0 < count; start < mx; count \<le> mx; mx \<le> length list\<rbrakk>
   \<Longrightarrow> last (wrap_slice start count mx list)
           = list ! (if start + count - 1 < mx then start + count - 1 else start + count - mx -1)"
  by (fastforce simp: wrap_slice_def last_take last_append not_le)

lemma tl_wrap_slice:
  "\<lbrakk>0 < count; mx \<le> length list; start < mx\<rbrakk> \<Longrightarrow>
   tl (wrap_slice start count mx list) = wrap_slice (start + 1) (count - 1) mx list"
  by (fastforce simp: wrap_slice_def tl_take tl_drop drop_Suc)

lemma wrap_slice_max[simp]:
  "wrap_slice start count start list = take count list"
  by (clarsimp simp: wrap_slice_def)

lemma length_refills_map[simp]:
  "\<lbrakk> mx \<le> length list; count \<le> mx \<rbrakk> \<Longrightarrow> length (refills_map start count mx list) = count"
  by (clarsimp simp: refills_map_def)

lemma sc_valid_refills_refillSize:
  "\<lbrakk>sc_valid_refills sc; sc_relation sc n sc'\<rbrakk> \<Longrightarrow> 0 < refillSize sc'"
  by (clarsimp simp: valid_sched_context_def sc_relation_def refillSize_def)

lemma sc_refills_neq_zero_cross:
  "\<lbrakk>sc_relation sc n sc'; sc_refills sc \<noteq> []\<rbrakk>
   \<Longrightarrow> refills_map (scRefillHead sc') (refillSize sc') (scRefillMax sc') (scRefills sc') \<noteq> []"
  by (clarsimp simp: sc_relation_def)

lemma refills_map_non_empty_pos_count:
  "refills_map start count mx list \<noteq> [] \<Longrightarrow> 0 < count \<and> 0 < mx"
  apply (clarsimp simp: refills_map_def refill_map_def wrap_slice_def split: if_split_asm)
  by linarith

lemma hd_refills_map:
  "\<lbrakk>refills_map start count mx list \<noteq> []; mx \<le> length list; start < mx\<rbrakk>
   \<Longrightarrow> hd (refills_map start count mx list) = refill_map (list ! start)"
  apply (frule refills_map_non_empty_pos_count)
  apply (clarsimp simp: refills_map_def)
  by (simp add: hd_map hd_wrap_slice)

lemma refill_hd_relation:
  "sc_relation sc n sc' \<Longrightarrow> sc_valid_refills' sc' \<Longrightarrow> refill_hd sc = refill_map (refillHd sc')"
  apply (clarsimp simp: sc_relation_def refillHd_def refills_map_def valid_sched_context'_def)
  apply (subst hd_map, clarsimp simp: wrap_slice_def refillSize_def)
  apply (rule arg_cong[where f=refill_map])
  apply (fastforce simp: refillSize_def intro: hd_wrap_slice)
  done

lemma refill_hd_relation2:
  "\<lbrakk>sc_relation sc n sc'; sc_refills sc \<noteq> []; valid_sched_context' sc' s'\<rbrakk>
   \<Longrightarrow> rAmount (refillHd sc') = r_amount (refill_hd sc)
       \<and> rTime (refillHd sc') = r_time (refill_hd sc)"
  apply (frule refill_hd_relation)
   apply (frule (1) sc_refills_neq_zero_cross[THEN refills_map_non_empty_pos_count])
   apply (simp add: valid_sched_context'_def)
  apply (clarsimp simp: refill_map_def)
  done

lemma refill_ready_relation:
  "\<lbrakk>sc_relation sc n sc'; sc_valid_refills' sc'\<rbrakk>
   \<Longrightarrow> refill_ready time (refill_hd sc) = (rTime (refillHd sc') \<le> time)"
  apply (frule (1) refill_hd_relation)
  by (clarsimp simp: refill_ready_def kernelWCETTicks_def refill_map_def)

lemma refill_capacity_relation:
  "\<lbrakk>sc_relation sc n sc'; sc_valid_refills' sc'\<rbrakk> \<Longrightarrow>
   refill_capacity usage (refill_hd sc) = refillCapacity usage (refillHd sc')"
  apply (frule (1) refill_hd_relation)
  by (clarsimp simp: refillCapacity_def refill_capacity_def refillHd_def refill_map_def)

lemma refill_sufficient_relation:
  "\<lbrakk>sc_relation sc n sc'; sc_valid_refills' sc'\<rbrakk> \<Longrightarrow>
   refill_sufficient usage (refill_hd sc) = refillSufficient usage (refillHd sc')"
  apply (frule (1) refill_capacity_relation[where usage=usage])
  by (clarsimp simp: refillSufficient_def refill_sufficient_def minBudget_def MIN_BUDGET_def
                     kernelWCETTicks_def)

end
end