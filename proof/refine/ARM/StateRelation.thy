(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   The refinement relation between abstract and concrete states
*)

theory StateRelation
imports Invariants_H
begin

context begin interpretation Arch . (*FIXME: arch_split*)
definition
  cte_map :: "cslot_ptr \<Rightarrow> word32"
where
 "cte_map \<equiv> \<lambda>(oref, cref). oref + (of_bl cref * 2 ^ cte_level_bits)"

lemmas cte_map_def' = cte_map_def[simplified cte_level_bits_def, simplified]

definition
  lookup_failure_map :: "ExceptionTypes_A.lookup_failure \<Rightarrow> Fault_H.lookup_failure"
where
 "lookup_failure_map \<equiv> \<lambda>lf. case lf of
    ExceptionTypes_A.InvalidRoot            \<Rightarrow> Fault_H.InvalidRoot
  | ExceptionTypes_A.MissingCapability n    \<Rightarrow> Fault_H.MissingCapability n
  | ExceptionTypes_A.DepthMismatch n m      \<Rightarrow> Fault_H.DepthMismatch n m
  | ExceptionTypes_A.GuardMismatch n g      \<Rightarrow> Fault_H.GuardMismatch n (of_bl g) (length g)"

primrec
  arch_fault_map :: "Machine_A.ARM_A.arch_fault \<Rightarrow> ArchFault_H.ARM_H.arch_fault"
where
 "arch_fault_map (Machine_A.ARM_A.VMFault ptr msg) = ArchFault_H.ARM_H.VMFault ptr msg"

primrec
  fault_map :: "ExceptionTypes_A.fault \<Rightarrow> Fault_H.fault"
where
  "fault_map (ExceptionTypes_A.CapFault ref bool failure) =
   Fault_H.CapFault ref bool (lookup_failure_map failure)"
| "fault_map (ExceptionTypes_A.ArchFault  arch_fault) =
   Fault_H.ArchFault  (arch_fault_map arch_fault)"
| "fault_map (ExceptionTypes_A.UnknownSyscallException n) =
   Fault_H.UnknownSyscallException n"
| "fault_map (ExceptionTypes_A.UserException x y) =
   Fault_H.UserException x y"
| "fault_map (ExceptionTypes_A.Timeout d) =
   Fault_H.Timeout d"


text \<open>
  A pspace and a tree are related if every object in the pspace
  corresponds to an object in the tree. Some abstract objects
  like CapTables correspond to multiple concrete ones, thus we
  have to make cuts.
\<close>

type_synonym obj_relation_cut = "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
type_synonym obj_relation_cuts = "(word32 \<times> obj_relation_cut) set"

definition
  vmrights_map :: "rights set \<Rightarrow> vmrights"
where
 "vmrights_map S \<equiv> if AllowRead \<in> S
                   then (if AllowWrite \<in> S then VMReadWrite else VMReadOnly)
                   else VMKernelOnly"

definition
  zbits_map :: "nat option \<Rightarrow> zombie_type"
where
 "zbits_map N \<equiv> case N of Some n \<Rightarrow> ZombieCNode n
                        | None \<Rightarrow> ZombieTCB"

primrec
  acap_relation :: "arch_cap \<Rightarrow> arch_capability \<Rightarrow> bool"
where
  "acap_relation (arch_cap.ASIDPoolCap x y) c             = (c =
        arch_capability.ASIDPoolCap x y)"
| "acap_relation (arch_cap.ASIDControlCap) c              = (c =
        arch_capability.ASIDControlCap)"
| "acap_relation (arch_cap.PageCap dev word rghts sz data) c  = (c =
        arch_capability.PageCap dev word (vmrights_map rghts) sz data)"
| "acap_relation (arch_cap.PageTableCap word data) c      = (c =
        arch_capability.PageTableCap word data)"
| "acap_relation (arch_cap.PageDirectoryCap word data) c  = (c =
        arch_capability.PageDirectoryCap word data)"

primrec
  cap_relation :: "cap \<Rightarrow> capability \<Rightarrow> bool"
where
  "cap_relation Structures_A.NullCap c                    = (c =
           Structures_H.NullCap)"
| "cap_relation Structures_A.DomainCap c                  = (c =
           Structures_H.DomainCap)"
| "cap_relation (Structures_A.UntypedCap dev ref n f) c   = (c =
           Structures_H.UntypedCap dev ref n f)"
| "cap_relation (Structures_A.EndpointCap ref b r) c      = (c =
           Structures_H.EndpointCap ref b (AllowSend \<in> r)
             (AllowRecv \<in> r) (AllowGrant \<in> r) (AllowGrantReply \<in> r))"
| "cap_relation (Structures_A.NotificationCap ref b r) c  = (c =
           Structures_H.NotificationCap ref b (AllowSend \<in> r) (AllowRecv \<in> r))"
| "cap_relation (Structures_A.CNodeCap ref n L) c         = (c =
           Structures_H.CNodeCap ref n (of_bl L) (length L))"
| "cap_relation (Structures_A.ThreadCap ref) c            = (c =
           Structures_H.ThreadCap ref)"
| "cap_relation (Structures_A.ReplyCap ref r) c           = (c =
           Structures_H.ReplyCap ref (AllowGrant \<in> r))"
| "cap_relation (Structures_A.SchedContextCap ref n) c    = (c =
           Structures_H.SchedContextCap ref (min_sched_context_bits + n))"
| "cap_relation (Structures_A.SchedControlCap) c          = (c =
           Structures_H.SchedControlCap)"
| "cap_relation (Structures_A.IRQControlCap) c            = (c =
           Structures_H.IRQControlCap)"
| "cap_relation (Structures_A.IRQHandlerCap irq) c        = (c =
           Structures_H.IRQHandlerCap irq)"
| "cap_relation (Structures_A.ArchObjectCap a) c          = (\<exists>a'.
           acap_relation a a' \<and> c = Structures_H.ArchObjectCap a')"
| "cap_relation (Structures_A.Zombie p b n) c             = (c =
           Structures_H.Zombie p (zbits_map b) n)"


definition
  cte_relation :: "cap_ref \<Rightarrow> obj_relation_cut"
where
 "cte_relation y \<equiv> \<lambda>ko ko'. \<exists>sz cs cte cap. ko = CNode sz cs \<and> ko' = KOCTE cte
                               \<and> cs y = Some cap \<and> cap_relation cap (cteCap cte)"

definition
  asid_pool_relation :: "(10 word \<rightharpoonup> word32) \<Rightarrow> asidpool \<Rightarrow> bool"
where
  "asid_pool_relation \<equiv> \<lambda>p p'. p = inv ASIDPool p' o ucast"

definition
  ntfn_relation :: "Structures_A.notification \<Rightarrow> Structures_H.notification \<Rightarrow> bool"
where
 "ntfn_relation \<equiv> \<lambda>ntfn ntfn'.
    (case ntfn_obj ntfn of
      Structures_A.IdleNtfn       \<Rightarrow> ntfnObj ntfn' = Structures_H.IdleNtfn
    | Structures_A.WaitingNtfn q  \<Rightarrow> ntfnObj ntfn' = Structures_H.WaitingNtfn q
    | Structures_A.ActiveNtfn b \<Rightarrow> ntfnObj ntfn' = Structures_H.ActiveNtfn b)
  \<and> ntfn_bound_tcb ntfn = ntfnBoundTCB ntfn' \<and> ntfn_sc ntfn = ntfnSc ntfn'"

definition
  ep_relation :: "Structures_A.endpoint \<Rightarrow> Structures_H.endpoint \<Rightarrow> bool"
where
 "ep_relation \<equiv> \<lambda>ep ep'. case ep of
    Structures_A.IdleEP   \<Rightarrow> ep' = Structures_H.IdleEP
  | Structures_A.RecvEP q \<Rightarrow> ep' = Structures_H.RecvEP q
  | Structures_A.SendEP q \<Rightarrow> ep' = Structures_H.SendEP q"

definition
  fault_rel_optionation :: "ExceptionTypes_A.fault option \<Rightarrow> Fault_H.fault option \<Rightarrow> bool"
where
 "fault_rel_optionation \<equiv> \<lambda>f f'. f' = option_map fault_map f"

primrec
  thread_state_relation :: "Structures_A.thread_state \<Rightarrow> Structures_H.thread_state \<Rightarrow> bool"
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

definition
  arch_tcb_relation :: "Structures_A.arch_tcb \<Rightarrow> Structures_H.arch_tcb \<Rightarrow> bool"
where
 "arch_tcb_relation \<equiv> \<lambda>atcb atcb'.
   tcb_context atcb = atcbContext atcb'"

definition
  tcb_relation :: "Structures_A.tcb \<Rightarrow> Structures_H.tcb \<Rightarrow> bool"
where
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

definition refills_map :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> refill list \<Rightarrow>  Structures_A.refill list" where
  "refills_map start count mx \<equiv> map refill_map \<circ> wrap_slice (min start mx) (min count mx) mx"

(* This leaves those Haskell refills unconstrained that are not in the abstract sc_refills list.
   This is intentional: for instance, refillPopHead will leave "garbage" behind in memory which
   is not captured on the abstract side, and we can't demand that the Haskell side has empty
   refills there. This should be fine, from concrete to abstract we still have a function.
 *)
definition sc_relation ::
  "Structures_A.sched_context \<Rightarrow> nat \<Rightarrow> Structures_H.sched_context \<Rightarrow> bool" where
  "sc_relation \<equiv> \<lambda>sc n sc'.
     sc_period sc = scPeriod sc' \<and>
     sc_budget sc = scBudget sc' \<and>
     sc_consumed sc = scConsumed sc' \<and>
     sc_tcb sc = scTCB sc' \<and>
     sc_ntfn sc = scNtfn sc' \<and>
     sc_refills sc = refills_map (scRefillHead sc') (scRefillCount sc')
                                 (scRefillMax sc') (scRefills sc') \<and>
     \<comment> \<open>Relates the abstract @{term n} with the concrete refill list length\<close>
     length (scRefills sc') = max_num_refills (min_sched_context_bits + n) \<and>
     sc_refill_max sc = scRefillMax sc' \<and>
     sc_badge sc = scBadge sc' \<and>
     sc_yield_from sc = scYieldFrom sc'"

definition reply_relation :: "Structures_A.reply \<Rightarrow> Structures_H.reply \<Rightarrow> bool" where
  "reply_relation \<equiv> \<lambda>reply reply'.
     reply_sc reply = replySc reply' \<and> reply_tcb reply = replyTCB reply'"

definition
  other_obj_relation :: "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "other_obj_relation obj obj' \<equiv>
  (case (obj, obj') of
        (TCB tcb, KOTCB tcb') \<Rightarrow> tcb_relation tcb tcb'
      | (Endpoint ep, KOEndpoint ep') \<Rightarrow> ep_relation ep ep'
      | (Notification ntfn, KONotification ntfn') \<Rightarrow> ntfn_relation ntfn ntfn'
      | (ArchObj (ARM_A.ASIDPool pool), KOArch (KOASIDPool pool'))
             \<Rightarrow> asid_pool_relation pool pool'
      | _ \<Rightarrow> False)"

primrec
   pde_relation' :: "ARM_A.pde \<Rightarrow> ARM_H.pde \<Rightarrow> bool"
where
  "pde_relation'  ARM_A.InvalidPDE x = (x = ARM_H.InvalidPDE)"
| "pde_relation' (ARM_A.PageTablePDE ptr atts domain) x
      = (x = ARM_H.PageTablePDE ptr (ParityEnabled \<in> atts) domain)"
| "pde_relation' (ARM_A.SectionPDE ptr atts domain rghts) x
      = (x = ARM_H.SectionPDE ptr (ParityEnabled \<in> atts) domain
               (PageCacheable \<in> atts) (Global \<in> atts) (XNever \<in> atts) (vmrights_map rghts))"
| "pde_relation' (ARM_A.SuperSectionPDE ptr atts rghts) x
      = (x = ARM_H.SuperSectionPDE ptr (ParityEnabled \<in> atts)
               (PageCacheable \<in> atts) (Global \<in> atts) (XNever \<in> atts) (vmrights_map rghts))"


primrec
   pte_relation' :: "ARM_A.pte \<Rightarrow> ARM_H.pte \<Rightarrow> bool"
where
  "pte_relation'  ARM_A.InvalidPTE x = (x = ARM_H.InvalidPTE)"
| "pte_relation' (ARM_A.LargePagePTE ptr atts rghts) x
      = (x = ARM_H.LargePagePTE ptr (PageCacheable \<in> atts) (Global \<in> atts)
                                         (XNever \<in> atts) (vmrights_map rghts))"
| "pte_relation' (ARM_A.SmallPagePTE ptr atts rghts) x
      = (x = ARM_H.SmallPagePTE ptr (PageCacheable \<in> atts) (Global \<in> atts)
                                         (XNever \<in> atts) (vmrights_map rghts))"


definition
  pde_align' :: "ARM_H.pde \<Rightarrow> nat"
where
 "pde_align' pde \<equiv>
  case pde of ARM_H.pde.SuperSectionPDE _ _ _ _ _ _ \<Rightarrow> 4 | _ \<Rightarrow> 0"

lemmas pde_align_simps[simp] =
  pde_align'_def[split_simps ARM_A.pde.split]

definition
  pte_align' :: "ARM_H.pte \<Rightarrow> nat"
where
 "pte_align' pte \<equiv> case pte of ARM_H.pte.LargePagePTE _ _ _ _ _ \<Rightarrow> 4 | _ \<Rightarrow> 0"

lemmas pte_align_simps[simp] =
  pte_align'_def[split_simps ARM_A.pte.split]

definition
  "pde_relation_aligned y pde pde' \<equiv>
   if is_aligned y (pde_align' pde') then pde_relation' pde pde'
   else pde = ARM_A.InvalidPDE"

definition
  "pte_relation_aligned y pte pte' \<equiv>
   if is_aligned y (pte_align' pte') then pte_relation' pte pte'
   else pte = ARM_A.InvalidPTE"

definition
 "pte_relation y \<equiv> \<lambda>ko ko'. \<exists>pt pte. ko = ArchObj (PageTable pt) \<and> ko' = KOArch (KOPTE pte)
                              \<and> pte_relation_aligned y (pt y) pte"

definition
 "pde_relation y \<equiv> \<lambda>ko ko'. \<exists>pd pde. ko = ArchObj (PageDirectory pd) \<and> ko' = KOArch (KOPDE pde)
                              \<and> pde_relation_aligned y (pd y) pde"

primrec
 aobj_relation_cuts :: "ARM_A.arch_kernel_obj \<Rightarrow> word32 \<Rightarrow> obj_relation_cuts"
where
  "aobj_relation_cuts (DataPage dev sz) x =
      {(x + n * 2 ^ pageBits, \<lambda>_ obj. obj = (if dev then KOUserDataDevice else KOUserData) ) | n . n < 2 ^ (pageBitsForSize sz - pageBits) }"
| "aobj_relation_cuts (ARM_A.ASIDPool pool) x =
     {(x, other_obj_relation)}"
| "aobj_relation_cuts (PageTable pt) x =
     (\<lambda>y. (x + (ucast y << 2), pte_relation y)) ` UNIV"
| "aobj_relation_cuts (PageDirectory pd) x =
     (\<lambda>y. (x + (ucast y << 2), pde_relation y)) ` UNIV"

abbreviation
  sc_relation_cut :: "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "sc_relation_cut obj obj' \<equiv>
  (case (obj, obj') of
        (Structures_A.SchedContext sc n, KOSchedContext sc') \<Rightarrow> sc_relation sc n sc'
      | _ \<Rightarrow> False)"

abbreviation
  reply_relation_cut :: "Structures_A.kernel_object \<Rightarrow> Structures_H.kernel_object \<Rightarrow> bool"
where
  "reply_relation_cut obj obj' \<equiv>
  (case (obj, obj') of
        (Structures_A.Reply r, KOReply r') \<Rightarrow> reply_relation r r'
      | _ \<Rightarrow> False)"

primrec
  obj_relation_cuts :: "Structures_A.kernel_object \<Rightarrow> word32 \<Rightarrow> obj_relation_cuts"
where
  "obj_relation_cuts (CNode sz cs) x =
     (if well_formed_cnode_n sz cs
      then {(cte_map (x, y), cte_relation y) | y. y \<in> dom cs}
      else {(x, \<bottom>\<bottom>)})"
| "obj_relation_cuts (TCB tcb) x = {(x, other_obj_relation)}"
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
             | ArchObj (PageTable pt) \<Rightarrow> (\<lambda>y. (x + (ucast y << 2), pte_relation y))
                                           ` (UNIV :: word8 set)
             | ArchObj (PageDirectory pd) \<Rightarrow> (\<lambda>y. (x + (ucast y << 2), pde_relation y))
                                           ` (UNIV :: 12 word set)
             | ArchObj (DataPage dev sz)      \<Rightarrow>
                 {(x + n * 2 ^ pageBits,  \<lambda>_ obj. obj =(if dev then KOUserDataDevice else KOUserData)) | n . n < 2 ^ (pageBitsForSize sz - pageBits) }
             | _ \<Rightarrow> {(x, other_obj_relation)})"
  by (simp split: Structures_A.kernel_object.split
                  ARM_A.arch_kernel_obj.split)

lemma obj_relation_cuts_def3:
  "obj_relation_cuts ko x =
  (case a_type ko of
     ACapTable n \<Rightarrow> {(cte_map (x, y), cte_relation y) | y. length y = n}
   | ASchedContext n \<Rightarrow>
       if valid_sched_context_size n then {(x, sc_relation_cut)} else {(x, \<bottom>\<bottom>)}
   | AReply \<Rightarrow> {(x, reply_relation_cut)}
   | AArch APageTable \<Rightarrow> (\<lambda>y. (x + (ucast y << 2), pte_relation y))
                            ` (UNIV :: word8 set)
   | AArch APageDirectory \<Rightarrow> (\<lambda>y. (x + (ucast y << 2), pde_relation y))
                            ` (UNIV :: 12 word set)
   | AArch (AUserData sz)  \<Rightarrow> {(x + n * 2 ^ pageBits, \<lambda>_ obj. obj = KOUserData) | n . n < 2 ^ (pageBitsForSize sz - pageBits) }
   | AArch (ADeviceData sz)  \<Rightarrow> {(x + n * 2 ^ pageBits, \<lambda>_ obj. obj = KOUserDataDevice ) | n . n < 2 ^ (pageBitsForSize sz - pageBits) }
   | AGarbage _ \<Rightarrow> {(x, \<bottom>\<bottom>)}
   | _ \<Rightarrow> {(x, other_obj_relation)})"
  apply (simp add: obj_relation_cuts_def2 a_type_def
            split: Structures_A.kernel_object.split
                  ARM_A.arch_kernel_obj.split)
  apply (clarsimp simp: well_formed_cnode_n_def length_set_helper)
  done

definition
 "is_other_obj_relation_type tp \<equiv>
  case tp of
     ACapTable n \<Rightarrow> False
   | ASchedContext n \<Rightarrow> False
   | AReply \<Rightarrow> False
   | AArch APageTable \<Rightarrow> False
   | AArch APageDirectory \<Rightarrow> False
   | AArch (AUserData _)   \<Rightarrow> False
   | AArch (ADeviceData _)   \<Rightarrow> False
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

lemma is_other_obj_relation_type_UserData:
  "\<not> is_other_obj_relation_type (AArch (AUserData sz))"
  unfolding is_other_obj_relation_type_def by simp

lemma is_other_obj_relation_type_DeviceData:
  "\<not> is_other_obj_relation_type (AArch (ADeviceData sz))"
  unfolding is_other_obj_relation_type_def by simp

lemma is_other_obj_relation_type:
  "is_other_obj_relation_type (a_type ko) \<Longrightarrow>
   obj_relation_cuts ko x = {(x, other_obj_relation)}"
  by (simp add: obj_relation_cuts_def3 is_other_obj_relation_type_def
         split: a_type.splits aa_type.splits)

definition
  pspace_dom :: "Structures_A.kheap \<Rightarrow> word32 set"
where
  "pspace_dom ps \<equiv> \<Union>x\<in>dom ps. fst ` (obj_relation_cuts (the (ps x)) x)"

definition
  pspace_relation :: "Structures_A.kheap \<Rightarrow> (word32 \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> bool"
where
 "pspace_relation ab con \<equiv>
  (pspace_dom ab = dom con) \<and>
  (\<forall>x \<in> dom ab. \<forall>(y, P) \<in> obj_relation_cuts (the (ab x)) x.
       P (the (ab x)) (the (con y)))"

definition
  sc_replies_relation_2 ::
  "(obj_ref \<rightharpoonup> obj_ref list) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> bool" where
  "sc_replies_relation_2 sc_repls scRepl replPrevs \<equiv>
     \<forall>p replies. sc_repls p = Some replies \<longrightarrow> heap_ls replPrevs (scRepl p) replies"

abbreviation sc_replies_relation :: "det_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "sc_replies_relation s s' \<equiv>
    sc_replies_relation_2 (sc_replies_of s) (scReplies_of s') (replyPrevs_of s')"

lemmas sc_replies_relation_def = sc_replies_relation_2_def

abbreviation (input) sc_replies_relation_obj ::
  "Structures_A.sched_context \<Rightarrow> sched_context \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> bool" where
  "sc_replies_relation_obj sc sc' nexts \<equiv>
       heap_ls nexts (scReply sc') (sc_replies sc)"

primrec
  sched_act_relation :: "Structures_A.scheduler_action \<Rightarrow> Structures_H.scheduler_action \<Rightarrow> bool"
where
  "sched_act_relation resume_cur_thread a' = (a' = ResumeCurrentThread)" |
  "sched_act_relation choose_new_thread a' = (a' = ChooseNewThread)" |
  "sched_act_relation (switch_thread x) a' = (a' = SwitchToThread x)"

definition
  ready_queues_relation :: "(Structures_A.domain \<Rightarrow> Structures_A.priority \<Rightarrow> Structures_A.ready_queue)
                         \<Rightarrow> (domain \<times> priority \<Rightarrow> KernelStateData_H.ready_queue) \<Rightarrow> bool"
where
  "ready_queues_relation qs qs' \<equiv> \<forall>d p. (qs d p = qs' (d, p))"

definition
  release_queue_relation :: "Structures_A.release_queue \<Rightarrow> KernelStateData_H.release_queue \<Rightarrow> bool"
where
  "release_queue_relation qs qs' \<equiv> (qs = qs')"

definition
  ghost_relation :: "Structures_A.kheap \<Rightarrow> (word32 \<rightharpoonup> vmpage_size) \<Rightarrow> (word32 \<rightharpoonup> nat) \<Rightarrow> bool"
where
  "ghost_relation h ups cns \<equiv>
   (\<forall>a sz. (\<exists>dev. h a = Some (ArchObj (DataPage dev sz))) \<longleftrightarrow> ups a = Some sz) \<and>
   (\<forall>a n. (\<exists>cs. h a = Some (CNode n cs) \<and> well_formed_cnode_n n cs) \<longleftrightarrow>
          cns a = Some n)"

definition
  cdt_relation :: "(cslot_ptr \<Rightarrow> bool) \<Rightarrow> cdt \<Rightarrow> cte_heap \<Rightarrow> bool"
where
  "cdt_relation \<equiv> \<lambda>cte_at m m'.
  \<forall>c. cte_at c \<longrightarrow> cte_map ` descendants_of c m = descendants_of' (cte_map c) m'"

definition
  cdt_list_relation :: "cdt_list \<Rightarrow> cdt \<Rightarrow> cte_heap \<Rightarrow> bool"
where
 "cdt_list_relation \<equiv> \<lambda>t m m'.
    \<forall>c cap node. m' (cte_map c) = Some (CTE cap node)
        \<longrightarrow> (case next_slot c t m of None \<Rightarrow> True
            | Some next \<Rightarrow> mdbNext node = cte_map next)"

definition
  revokable_relation :: "(cslot_ptr \<Rightarrow> bool) \<Rightarrow> (cslot_ptr \<Rightarrow> cap option) \<Rightarrow> cte_heap \<Rightarrow> bool"
where
  "revokable_relation revo cs m' \<equiv>
  \<forall>c cap node. cs c \<noteq> None \<longrightarrow>
               m' (cte_map c) = Some (CTE cap node) \<longrightarrow>
               revo c = mdbRevocable node"

definition
  irq_state_relation :: "irq_state \<Rightarrow> irqstate \<Rightarrow> bool"
where
  "irq_state_relation irq irq' \<equiv> case (irq, irq') of
     (irq_state.IRQInactive, irqstate.IRQInactive) \<Rightarrow> True
   | (irq_state.IRQSignal, irqstate.IRQSignal) \<Rightarrow> True
   | (irq_state.IRQTimer, irqstate.IRQTimer) \<Rightarrow> True
   | _ \<Rightarrow> False"

definition
  interrupt_state_relation :: "(irq \<Rightarrow> obj_ref) \<Rightarrow> (irq \<Rightarrow> irq_state) \<Rightarrow> interrupt_state \<Rightarrow> bool"
where
  "interrupt_state_relation node_map irqs is \<equiv>
    (\<exists>node irqs'. is = InterruptState node irqs'
              \<and> (\<forall>irq. node_map irq = node + (ucast irq << cte_level_bits))
              \<and> (\<forall>irq. irq_state_relation (irqs irq) (irqs' irq)))"

definition
  arch_state_relation :: "(arch_state \<times> ARM_H.kernel_state) set"
where
  "arch_state_relation \<equiv> {(s, s') .
         arm_asid_table s = armKSASIDTable s' o ucast
       \<and> arm_global_pd s = armKSGlobalPD s'
       \<and> arm_hwasid_table s = armKSHWASIDTable s'
       \<and> arm_global_pts s = armKSGlobalPTs s'
       \<and> arm_next_asid s = armKSNextASID s'
       \<and> arm_asid_map s = armKSASIDMap s'
       \<and> arm_kernel_vspace s = armKSKernelVSpace s'}"


definition
  rights_mask_map :: "rights set \<Rightarrow> Types_H.cap_rights"
where
 "rights_mask_map \<equiv> \<lambda>rs. CapRights (AllowWrite \<in> rs) (AllowRead \<in> rs) (AllowGrant \<in> rs)
                                   (AllowGrantReply \<in> rs)"


lemma length_wrap_slice[simp]:
  "\<lbrakk> count \<le> mx; start \<le> mx; mx \<le> length xs \<rbrakk> \<Longrightarrow> length (wrap_slice start count mx xs) = count"
  by (simp add: wrap_slice_def)

lemma wrap_slice_empty[simp]:
  "start \<le> mx \<Longrightarrow> wrap_slice start 0 mx xs = []"
  by (clarsimp simp: wrap_slice_def)

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
     \<And>pt (z :: word8) pte'. \<lbrakk> ko = ArchObj (PageTable pt); y = x + (ucast z << 2);
                              ko' = KOArch (KOPTE pte'); pte_relation_aligned z (pt z) pte' \<rbrakk>
              \<Longrightarrow> R;
     \<And>pd (z :: 12 word) pde'. \<lbrakk> ko = ArchObj (PageDirectory pd); y = x + (ucast z << 2);
                              ko' = KOArch (KOPDE pde'); pde_relation_aligned z (pd z) pde' \<rbrakk>
              \<Longrightarrow> R;
     \<And>sz dev n. \<lbrakk> ko = ArchObj (DataPage dev sz); ko' = (if dev then KOUserDataDevice else KOUserData);
              y = x + n * 2 ^ pageBits; n < 2 ^ (pageBitsForSize sz - pageBits) \<rbrakk> \<Longrightarrow> R;
            \<lbrakk> y = x; other_obj_relation ko ko'; is_other_obj_relation_type (a_type ko) \<rbrakk> \<Longrightarrow> R
    \<rbrakk> \<Longrightarrow> R"
  apply (simp add: obj_relation_cuts_def2 is_other_obj_relation_type_def
                   a_type_def
            split: Structures_A.kernel_object.split_asm if_split_asm
                   ARM_A.arch_kernel_obj.split_asm)
  by (clarsimp split: if_splits kernel_object.split_asm,
      clarsimp simp: cte_relation_def pte_relation_def pde_relation_def
                     reply_relation_def sc_relation_def)+

lemma eq_trans_helper:
  "\<lbrakk> x = y; P y = Q \<rbrakk> \<Longrightarrow> P x = Q"
  by simp

lemma cap_relation_case':
  "cap_relation cap cap'
     = (case cap of cap.ArchObjectCap arch_cap.ASIDControlCap \<Rightarrow> cap_relation cap cap'
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



text \<open>Relations on other data types that aren't stored but
        used as intermediate values in the specs.\<close>

primrec
  message_info_map :: "Structures_A.message_info \<Rightarrow> Types_H.message_info"
where
 "message_info_map (Structures_A.MI a b c d) = (Types_H.MI a b c d)"

lemma mi_map_label[simp]: "msgLabel (message_info_map mi) = mi_label mi"
  by (cases mi, simp)

primrec
  syscall_error_map :: "ExceptionTypes_A.syscall_error \<Rightarrow> Fault_H.syscall_error"
where
  "syscall_error_map (ExceptionTypes_A.InvalidArgument n)     = Fault_H.InvalidArgument n"
| "syscall_error_map (ExceptionTypes_A.InvalidCapability n)   = (Fault_H.InvalidCapability n)"
| "syscall_error_map ExceptionTypes_A.IllegalOperation        = Fault_H.IllegalOperation"
| "syscall_error_map (ExceptionTypes_A.RangeError n m)        = Fault_H.RangeError n m"
| "syscall_error_map ExceptionTypes_A.AlignmentError          = Fault_H.AlignmentError"
| "syscall_error_map (ExceptionTypes_A.FailedLookup b lf)     = Fault_H.FailedLookup b (lookup_failure_map lf)"
| "syscall_error_map ExceptionTypes_A.TruncatedMessage        = Fault_H.TruncatedMessage"
| "syscall_error_map ExceptionTypes_A.DeleteFirst             = Fault_H.DeleteFirst"
| "syscall_error_map ExceptionTypes_A.RevokeFirst             = Fault_H.RevokeFirst"
| "syscall_error_map (ExceptionTypes_A.NotEnoughMemory n)       = Fault_H.syscall_error.NotEnoughMemory n"

definition
  APIType_map :: "Structures_A.apiobject_type \<Rightarrow> ARM_H.object_type"
where
  "APIType_map ty \<equiv> case ty of
                    Structures_A.Untyped \<Rightarrow> APIObjectType ArchTypes_H.Untyped
                  | Structures_A.TCBObject \<Rightarrow> APIObjectType ArchTypes_H.TCBObject
                  | Structures_A.EndpointObject \<Rightarrow> APIObjectType ArchTypes_H.EndpointObject
                  | Structures_A.NotificationObject \<Rightarrow> APIObjectType ArchTypes_H.NotificationObject
                  | Structures_A.CapTableObject \<Rightarrow> APIObjectType ArchTypes_H.CapTableObject
                  | ArchObject ao \<Rightarrow> (case ao of
         SmallPageObj     \<Rightarrow> SmallPageObject
       | LargePageObj     \<Rightarrow> LargePageObject
       | SectionObj       \<Rightarrow> SectionObject
       | SuperSectionObj  \<Rightarrow> SuperSectionObject
       | PageTableObj     \<Rightarrow> PageTableObject
       | PageDirectoryObj \<Rightarrow> PageDirectoryObject)"

definition
  state_relation :: "(det_state \<times> kernel_state) set"
where
 "state_relation \<equiv> {(s, s').
         pspace_relation (kheap s) (ksPSpace s')
       \<and> sc_replies_relation s s'
       \<and> sched_act_relation (scheduler_action s) (ksSchedulerAction s')
       \<and> ready_queues_relation (ready_queues s) (ksReadyQueues s')
       \<and> release_queue_relation (release_queue s) (ksReleaseQueue s')
       \<and> ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')
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

lemma curdomain_relation:
  "(s, s') \<in> state_relation \<Longrightarrow> cur_domain s = ksCurDomain s'"
  by (clarsimp simp: state_relation_def)

lemma state_relation_pspace_relation[elim!]:
  "(s,s') \<in> state_relation \<Longrightarrow> pspace_relation (kheap s) (ksPSpace s')"
  by (simp add: state_relation_def)

lemma state_relation_ready_queues_relation[elim!]:
  "(s, s') \<in> state_relation \<Longrightarrow> ready_queues_relation (ready_queues s) (ksReadyQueues s')"
  by (simp add: state_relation_def)

lemma state_relation_release_queue_relation:
  "(s,s') \<in> state_relation \<Longrightarrow> release_queue_relation (release_queue s) (ksReleaseQueue s')"
  by (clarsimp simp: state_relation_def)

lemma state_relation_sc_replies_relation:
  "(s,s') \<in> state_relation \<Longrightarrow> sc_replies_relation s s'"
  using state_relation_def by blast

lemma state_relation_sched_act_relation[elim!]:
  "(s,s') \<in> state_relation \<Longrightarrow> sched_act_relation (scheduler_action s) (ksSchedulerAction s')"
  by (clarsimp simp: state_relation_def)

lemma state_relationD:
  assumes sr:  "(s, s') \<in> state_relation"
  shows "pspace_relation (kheap s) (ksPSpace s') \<and>
  sc_replies_relation s s' \<and>
  sched_act_relation (scheduler_action s) (ksSchedulerAction s') \<and>
  ready_queues_relation (ready_queues s) (ksReadyQueues s') \<and>
  release_queue_relation (release_queue s) (ksReleaseQueue s') \<and>
  ghost_relation (kheap s) (gsUserPages s') (gsCNodes s') \<and>
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
  ready_queues_relation (ready_queues s) (ksReadyQueues s');
  release_queue_relation (release_queue s) (ksReleaseQueue s');
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

text \<open>This isn't defined for arch objects\<close>

lemmas isCap_defs =
  isZombie_def isArchObjectCap_def
  isThreadCap_def isCNodeCap_def isNotificationCap_def
  isEndpointCap_def isUntypedCap_def isNullCap_def
  isIRQHandlerCap_def isIRQControlCap_def isReplyCap_def
  isSchedContextCap_def isSchedControlCap_def
  isPageCap_def isPageTableCap_def isPageDirectoryCap_def
  isASIDControlCap_def isASIDPoolCap_def isArchPageCap_def
  isDomainCap_def

lemma isCNodeCap_cap_map [simp]:
  "cap_relation c c' \<Longrightarrow> isCNodeCap c' = is_cnode_cap c"
  apply (cases c, simp_all add: isCap_defs split: sum.splits)
   apply clarsimp+
  done

lemma cap_rel_valid_fh:
  "cap_relation a b \<Longrightarrow> valid_fault_handler a = isValidFaultHandler b"
  apply (case_tac a
         ; case_tac b
         ; simp add: valid_fault_handler_def isValidFaultHandler_def)
  apply (rule iffI
         ; clarsimp simp: has_handler_rights_def split: bool.split_asm)
  done

lemma sts_rel_idle :
  "thread_state_relation st IdleThreadState = (st = Structures_A.IdleThreadState)"
  by (cases st, auto)

lemma sts_rel_runnable :
  "\<lbrakk>thread_state_relation st st'; runnable st\<rbrakk> \<Longrightarrow> runnable' st'"
  by (cases st, auto)

lemma pspace_relation_absD:
  "\<lbrakk> ab x = Some y; pspace_relation ab con \<rbrakk>
      \<Longrightarrow> \<forall>(x', P) \<in> obj_relation_cuts y x. \<exists>z. con x' = Some z \<and> P y z"
  apply (clarsimp simp add: pspace_relation_def)
  apply (drule bspec, erule domI)
  apply simp
  apply (drule(1) bspec)
  apply (subgoal_tac "a \<in> pspace_dom ab")
   apply clarsimp
  apply (simp(no_asm) add: pspace_dom_def)
  apply (rule rev_bexI, erule domI)
  apply (simp add: image_def rev_bexI)
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
   subgoal for _ sz by (cases sz; simp add: pageBits_def)
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
     \<And>y ko P. \<lbrakk> s y = Some ko; (x, P) \<in> obj_relation_cuts ko y; P ko ko' \<rbrakk> \<Longrightarrow> R
        \<rbrakk> \<Longrightarrow> R"
  apply (rule pspace_dom_revE [OF in_related_pspace_dom],
         assumption+)
  apply (frule(1) pspace_relation_absD)
  apply fastforce
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

lemma sc_replies_relation_scReply:
  "\<lbrakk> sc_replies_relation s s';
     kheap s x = Some (kernel_object.SchedContext sc n);
     ksPSpace s' x = Some (KOSchedContext sc')\<rbrakk>
    \<Longrightarrow> hd_opt (sc_replies sc) = scReply sc'"
  apply (clarsimp simp: sc_replies_relation_def sc_replies_of_scs_def scs_of_kh_def map_project_def)
  apply (drule_tac x=x and y="sc_replies sc" in spec2)
  apply (clarsimp simp: sc_of_def opt_map_def)
  apply (case_tac "sc_replies sc"; clarsimp simp: projectKO_opt_sc)
  done

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
  apply (clarsimp simp: sc_of_def opt_map_def projectKO_opt_sc split: option.splits)
  done

lemma list_refs_of_replies'_reftype[simp]:
  "(p, reftype) \<in> list_refs_of_replies' s' p' \<Longrightarrow> reftype \<in> {ReplyPrev, ReplyNext}"
  by (clarsimp simp: list_refs_of_replies'_def list_refs_of_reply'_def get_refs_def2
              split: option.split_asm)

lemma replyNext_replyNexts_of_opt_map:
  "\<lbrakk>ksPSpace s' p = Some (KOReply reply); replyNext reply = Some (Next p')\<rbrakk>
    \<Longrightarrow> (replyNexts_of s' |> f s') p = f s' p'"
  by (clarsimp simp: opt_map_left_Some projectKO_opt_reply split: option.split)

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
  apply (clarsimp simp: replyPrevs_of_refs replyNexts_of_refs opt_map_left_Some)
  by (drule (1) sym_refsD[rotated], simp)

lemma sym_replies_next_then_prev_id_p:
  "\<lbrakk>sym_refs (list_refs_of_replies' s'); replyNexts_of s' p = Some p'\<rbrakk>
   \<Longrightarrow> (replyNexts_of s' |> replyPrevs_of s') p = Some p"
  supply opt_map_left_Some[simp]
  apply (clarsimp simp: replyPrevs_of_refs replyNexts_of_refs)
  by (drule (1) sym_refsD[rotated], simp)

(* proofs on scBitsFromRefillLength properties *)

lemma sc_const_eq:
  "refillSizeBytes = (refill_size_bytes::nat)"
  "schedContextStructSize = sizeof_sched_context_t"
  "minSchedContextBits = min_sched_context_bits"
  by (auto simp: refillSizeBytes_def refill_size_bytes_def minSchedContextBits_def
                 sizeof_sched_context_t_def min_sched_context_bits_def schedContextStructSize_def)

lemma max_num_refills_eq_refillAbsoluteMax':
  "max_num_refills = refillAbsoluteMax'"
  by (rule ext)
     (simp add: max_num_refills_def refillAbsoluteMax'_def shiftL_nat sc_const_eq)

lemma maxUntyped_eq:
  "untyped_max_bits = maxUntypedSizeBits"
  by (simp add: untyped_max_bits_def maxUntypedSizeBits_def)

lemmas sc_const_conc = sc_const_eq[symmetric] max_num_refills_eq_refillAbsoluteMax' maxUntyped_eq

lemma scRefills_length:
  "sc_relation sc n sc' \<Longrightarrow> length (scRefills sc') = max_num_refills (min_sched_context_bits + n)"
  by (simp add: sc_relation_def)

lemma scBits_core_ub:
  assumes cond: "sizeof_sched_context_t + refill_size_bytes < (2::nat) ^ (min_size - 1)"
  assumes min: "min_size \<le> us"
  shows "nat \<lceil>log 2
          (of_nat
            (((2::nat) ^ us - sizeof_sched_context_t) div
             refill_size_bytes *
             refill_size_bytes +
             sizeof_sched_context_t))\<rceil> \<le> us" (is "nat \<lceil>log 2 (of_nat ?F)\<rceil> \<le> _")
  apply (clarsimp simp del: of_nat_add of_nat_mult)
proof -
  have pos: "(0::real) < (2::nat) ^ us" using assms by simp
  have s0: "sizeof_sched_context_t \<le> (2::nat) ^ us"
    using le_trans[OF _  power_increasing[OF min]] cond
    by (metis HOL_Lemmas.nat_power_minus_less add_lessD1 arith_special(3) le_simps(1) nat_le_iff_add)
  have P1: "?F \<le> (2::nat) ^us"
  proof -
    have h1: "?F \<le> ((2::nat) ^ us
                         - sizeof_sched_context_t) + sizeof_sched_context_t" by simp
    thus ?thesis using s0 by linarith
  qed
  have P2: "(0::real) < ?F" by (simp add: refill_size_bytes_def sizeof_sched_context_t_def)
  thus "log 2 (of_nat ?F) \<le> of_nat us"
    using log_le_cancel_iff[where a="2::real", OF _ P2 pos, THEN iffD2] P1
    using log2_of_power_le by force
qed

lemma scBits_core_lb:
  assumes cond: "sizeof_sched_context_t + refill_size_bytes < (2::nat) ^ (min_size - 1)"
  assumes min: "min_size \<le> us"
  shows "us - 1 < nat \<lceil>log 2
          (of_nat
            (((2::nat) ^ us - sizeof_sched_context_t) div
             refill_size_bytes *
             refill_size_bytes +
             sizeof_sched_context_t))\<rceil>" (is "us - 1 < nat \<lceil>log 2 (of_nat ?F)\<rceil>")
proof -
   have s0: "sizeof_sched_context_t + refill_size_bytes < (2::nat) ^ (us - 1)"
    apply (rule less_le_trans[where y="(2::nat)^(min_size - 1)", OF cond])
     apply (clarsimp simp: sizeof_sched_context_t_def refill_size_bytes_def)
    using min by linarith
  have min_pos: "0 < min_size"
    using cond refill_size_bytes_def
    by (metis add_lessD1 diff_0_eq_0 gr0I less_one plus_nat.add_0 power.simps(1) power_zero_numeral)
  have step: "(2::nat)^(us - 1) < 2^us - (sizeof_sched_context_t + refill_size_bytes)"
  proof -
    have us_diff: "(2::nat)^(us - 1) = 2^us - 2^(us - 1)"
    proof -
      have power2_diff': "\<And>n::nat.(2::nat)^(n + 1) - 2^n = 2^n" by simp
      then have power2_diff: "\<And>n::nat. 0 < n \<Longrightarrow> (2::nat)^(n - 1) = 2^n - 2^(n - 1)"
        using Suc_pred' by (metis Suc_eq_plus1)
      thus ?thesis using min_pos min
        by auto
    qed
    thus ?thesis
      using diff_less_mono2[where l="2^us"] us_diff Lib.nat_power_minus_less s0
      by linarith
  qed
  have P1: "(2::nat)^us - refill_size_bytes < ?F"
  proof -
    have s01: "refill_size_bytes < (2::nat) ^ us" using step by linarith
    have s02: "sizeof_sched_context_t < (2::nat) ^ us" using step by linarith
    have h1: "?F = (2::nat)^us - ((2^us - sizeof_sched_context_t) mod refill_size_bytes)"
    proof -
      have p1: "((2^us - sizeof_sched_context_t) div refill_size_bytes * refill_size_bytes)
                  = (2::nat)^us - sizeof_sched_context_t
                      - ((2^us - sizeof_sched_context_t) mod refill_size_bytes)"
        by (simp add: minus_mod_eq_div_mult)
      thus ?thesis
      proof -
        have "sizeof_sched_context_t \<le> (2::nat) ^ us
                                          - (2 ^ us - sizeof_sched_context_t) mod
                                                                            refill_size_bytes"
        proof -
          have s0n: "sizeof_sched_context_t + refill_size_bytes < (2::nat) ^ us" using s0
            using HOL_Lemmas.nat_power_minus_less by blast
          have " sizeof_sched_context_t <  (2::nat) ^ us - refill_size_bytes" using s0n
            using less_diff_conv by blast
          then have "sizeof_sched_context_t
                        < (2::nat) ^ us - (2 ^ us - sizeof_sched_context_t) mod refill_size_bytes"
            apply -
            apply (drule less_le_trans[where z=" 2 ^ us -
                 ((2::nat) ^ us - sizeof_sched_context_t) mod refill_size_bytes"])
             apply (simp add: refill_size_bytes_def) by blast
          thus ?thesis using le_simps(1) by blast
        qed
        then have " (2::nat) ^ us - (2 ^ us - sizeof_sched_context_t) mod refill_size_bytes
                         - sizeof_sched_context_t + sizeof_sched_context_t
                     = 2 ^ us - (2 ^ us - sizeof_sched_context_t) mod refill_size_bytes "
          using le_add_diff_inverse2[where b=sizeof_sched_context_t] by blast
        thus ?thesis
          using diff_right_commute[where c=sizeof_sched_context_t]
          by (simp add: p1)
      qed
    qed
    thus ?thesis
      using diff_less_mono2[OF mod_less_divisor] s01
      by (simp add: refill_size_bytes_def)
  qed
  then have "2 ^ (us - 1) < ?F" using step P1 by linarith
  thus ?thesis
    using less_log2_of_power real_nat_ceiling_ge less_le_trans of_nat_less_iff
    by metis
qed


lemma scBits_core_identity:
  assumes cond: "sizeof_sched_context_t + refill_size_bytes < (2::nat) ^ (min_size - 1)"
  assumes min: "min_size \<le> us"
  shows "nat \<lceil>log 2 ((((2::nat) ^ us - sizeof_sched_context_t) div refill_size_bytes
                         * refill_size_bytes + sizeof_sched_context_t))\<rceil>
          = us"
proof -
  have min_pos: "0 < min_size"
    using cond refill_size_bytes_def
    by (metis add_lessD1 diff_0_eq_0 gr0I less_one plus_nat.add_0 power.simps(1) power_zero_numeral)
  then have pos: "0 < us" using assms by linarith
  thus ?thesis
    using scBits_core_lb[OF assms] scBits_core_ub[OF assms] by linarith
qed

lemma min_sched_context_bits_cond:
  "sizeof_sched_context_t + refill_size_bytes < (2::nat) ^ (min_sched_context_bits - 1)"
   by (clarsimp simp: sizeof_sched_context_t_def refill_size_bytes_def min_sched_context_bits_def)

lemma minSchedContextBits_cond:
  "sizeof_sched_context_t + refill_size_bytes < (2::nat) ^ (minSchedContextBits - 1)"
   by (clarsimp simp: sizeof_sched_context_t_def refill_size_bytes_def minSchedContextBits_def)

lemma scBits_inverse_us:
  notes sc_const_eq[simp]
  assumes "minSchedContextBits \<le> us"
  shows "scBitsFromRefillLength' (refillAbsoluteMax' us) = us"
  unfolding scBitsFromRefillLength'_def refillAbsoluteMax'_def
  apply (clarsimp simp del: of_nat_add of_nat_mult simp: shiftL_nat)
  using scBits_core_identity[of minSchedContextBits, OF minSchedContextBits_cond assms]
  by simp

lemma scBits_inverse_sc_relation:
  notes sc_const_eq[simp]
  assumes "sc_relation sc n sc'"
  shows "scBitsFromRefillLength sc' = minSchedContextBits + n"
  unfolding scBitsFromRefillLength'_def
  apply (clarsimp simp del: of_nat_add of_nat_mult simp: scRefills_length[OF assms] max_num_refills_def)
  using scBits_core_identity[of min_sched_context_bits, OF min_sched_context_bits_cond]
  by simp

lemma minRefillLength_ARM: "minRefillLength = 12"
  by (auto simp: minRefillLength_def minSchedContextBits_def refillAbsoluteMax'_def
                 schedContextStructSize_def refillSizeBytes_def shiftL_nat)

lemma minRefillLength_minSchedContextBits[simp]:
  "scBitsFromRefillLength' minRefillLength = minSchedContextBits"
  by (clarsimp simp: minRefillLength_def scBits_inverse_us)

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

lemma refillAbsoluteMax'_lb:
  "minSchedContextBits \<le> us \<Longrightarrow> minRefillLength \<le> refillAbsoluteMax' us"
  apply (simp add: minRefillLength_def)
  using refillAbsoluteMax'_mono by blast

lemma MIN_REFILLS_le_minRefillLength:
  "MIN_REFILLS \<le> minRefillLength"
  by (clarsimp simp: MIN_REFILLS_def minRefillLength_ARM)

lemmas scBits_simps = scBits_inverse_us refillAbsoluteMax_def sc_size_bounds_def sc_const_conc

(* leaving this sorried for now, still tweaking what to assume and how *)
lemma scBits_max:
(*  assumes "valid_sched_context_size' sc'"*)
  shows "scBitsFromRefillLength' us < LENGTH(machine_word_len)"
  unfolding scBitsFromRefillLength'_def
(*  using assms
  by (clarsimp simp: valid_sched_context_size'_def maxUntypedSizeBits_def)*) sorry

lemma scBits_pos':
  "0 < scBitsFromRefillLength' us"
proof -
  note sc_const_eq[simp]
  have "log 2 (of_nat sizeof_sched_context_t)
           \<le> log 2 (of_nat (us * refill_size_bytes + sizeof_sched_context_t))"
    apply (simp only: sc_const_eq(2)[symmetric, simplified schedContextStructSize_def, simplified])
    by (simp only: log_le_cancel_iff[where a="2::real", THEN iffD2])
  moreover have "0 < log 2 (of_nat sizeof_sched_context_t)"
    by (simp add: sc_const_eq(2)[symmetric, simplified schedContextStructSize_def, simplified])
  ultimately show ?thesis
    by (clarsimp simp: scBitsFromRefillLength'_def max_num_refills_def)
qed

lemma scBits_pos:
(*  assumes "valid_sched_context_size' sc'"*)
  shows "(0::machine_word) < of_nat (scBitsFromRefillLength' us)"
  using scBits_pos' scBits_max unat_ucast_less_no_overflow_simp
  by (metis less_or_eq_imp_le pow_mono_leq_imp_lt unat_0)

lemma scBits_pos_power2:
(*  assumes "valid_sched_context_size' sc'"*)
  shows "(1::machine_word) < (2::machine_word) ^ scBitsFromRefillLength' us"
  using one_less_power rel_simps(49) semiring_norm(76) scBits_pos' scBits_max
  by (metis Num.of_nat_simps(2) unat_2tp_if word_of_nat_less)

lemma sc_objBits_pos_power2:
(*  assumes "valid_sched_context_size' sc'"*)
  shows "(1::machine_word) < (2::machine_word) ^ objBits v"
  unfolding objBits_simps'
  apply (case_tac "injectKO v"; simp)
  by (simp add: pageBits_def archObjSize_def pteBits_def pdeBits_def scBits_pos_power2
         split: arch_kernel_object.split)+

(* possible alternative

definition scBitsFromRefillLength2 :: "sched_context => nat"
where
  "scBitsFromRefillLength2 sc \<equiv>
      (word_log2::machine_word \<Rightarrow> _) (of_nat ((length (scRefills sc)) * refillSizeBytes + schedContextStructSize))"

lemma word_clz_le:
  "0 < unat p \<Longrightarrow> unat (p::'a::len word) \<le> unat (q::'a::len word) \<Longrightarrow> word_clz q \<le> word_clz p"
  apply (clarsimp simp: word_clz_def word_size)
 oops

lemma word_log2_mono_le:
  "\<lbrakk>0 < unat p; 0 < unat q; unat (p::machine_word) \<le> unat (q::machine_word)\<rbrakk>
         \<Longrightarrow> word_log2 p \<le> word_log2 q"
  unfolding word_log2_def
  apply (case_tac "size p = size q"; simp)
   apply (simp add: word_clz_le diff_le_mono2)
  by (simp add: word_size_bl)

lemma word_log2_power2:
  "\<And>x. x < LENGTH('a) \<Longrightarrow> (word_log2::'a::len word \<Rightarrow> _) (2 ^ x) = x"
  unfolding word_log2_def word_clz_def
  apply (simp add: to_bl_2p)
  apply (prop_tac "replicate (LENGTH('a) - Suc x) False @
                   True # replicate x False = (replicate (LENGTH('a) - Suc x) False @
                   [True]) @ replicate x False") apply simp
  apply (simp only:)
  apply (subst takeWhile_append1[where x=True])
    apply simp+
  apply (subst takeWhile_append2)
  by (simp add: word_size)+
*)

end
end
