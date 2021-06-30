(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>Abstract datatype for the executable specification\<close>

theory ADT_H
imports
  "AInvs.ADT_AI"
  Syscall_R
begin

(* FIXME: many of the naming conventions in this file are wrong. Definitions should start with
          lower case letters, and should be under_score, not camelCase. Some, possibly many of
          the functions here can benefit from projections that have been developed since this
          was originally written *)

text \<open>
  The general refinement calculus (see theory Simulation) requires
  the definition of a so-called ``abstract datatype'' for each refinement layer.
  This theory defines this datatype for the executable specification.
  It is based on the abstract specification because we chose
  to base the refinement's observable state on the abstract state.
\<close>

consts
  initEntry :: word32
  initFrames :: "word32 list"
  initOffset :: word32
  initKernelFrames :: "word32 list"
  initBootFrames :: "word32 list"
  initDataStart :: word32

context begin interpretation Arch . (*FIXME: arch_split*)

text \<open>
  The construction of the abstract data type
  for the executable specification largely follows
  the one for the abstract specification.
\<close>
definition
  Init_H :: "kernel_state global_state set"
  where
  "Init_H \<equiv>
   ({empty_context} \<times> snd `
      fst (initKernel (VPtr initEntry) (PPtr initOffset) (map PPtr initFrames)
                      (map PPtr initKernelFrames) initBootFrames
                      (newKernelState initDataStart))) \<times>
    {UserMode} \<times> {None}"

definition
  "user_mem' s \<equiv> \<lambda>p.
  if (pointerInUserData p s)
  then Some (underlying_memory (ksMachineState s) p)
  else None"

definition
  "device_mem' s \<equiv> \<lambda>p.
  if (pointerInDeviceData p s)
  then Some p
  else None"


definition
  vm_rights_of :: "vmrights \<Rightarrow> rights set"
  where
  "vm_rights_of x \<equiv> case x of VMKernelOnly \<Rightarrow> vm_kernel_only
                    | VMReadOnly \<Rightarrow> vm_read_only
                    | VMReadWrite \<Rightarrow> vm_read_write"

lemma vm_rights_of_vmrights_map_id[simp]:
  "rs \<in> valid_vm_rights \<Longrightarrow> vm_rights_of (vmrights_map rs)= rs"
  by (auto simp: vm_rights_of_def vmrights_map_def valid_vm_rights_def
                 vm_read_write_def vm_read_only_def vm_kernel_only_def)

definition
  absPageTable :: "(word32 \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> obj_ref \<Rightarrow>
                  word8 \<Rightarrow> ARM_A.pte"
  where
  "absPageTable h a \<equiv> %offs.
   case (h (a + (ucast offs << 2))) of
     Some (KOArch (KOPTE (ARM_H.InvalidPTE))) \<Rightarrow> ARM_A.InvalidPTE
   | Some (KOArch (KOPTE (ARM_H.LargePagePTE p c g xn rights))) \<Rightarrow>
       if is_aligned offs 4 then
         ARM_A.LargePagePTE p
           {x. c & x=PageCacheable | g & x=Global | xn & x=XNever}
           (vm_rights_of rights)
       else ARM_A.InvalidPTE
   | Some (KOArch (KOPTE (ARM_H.SmallPagePTE p c g xn rights))) \<Rightarrow>
       ARM_A.SmallPagePTE p {x. c & x=PageCacheable |
                                        g & x=Global |
                                        xn & x=XNever} (vm_rights_of rights)"

definition
  absPageDirectory :: "(word32 \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> obj_ref \<Rightarrow>
                      12 word \<Rightarrow>  ARM_A.pde"
  where
  "absPageDirectory h a \<equiv> %offs.
   case (h (a + (ucast offs << 2))) of
     Some (KOArch (KOPDE (ARM_H.InvalidPDE))) \<Rightarrow> ARM_A.InvalidPDE
   | Some (KOArch (KOPDE (ARM_H.PageTablePDE p e mw))) \<Rightarrow>
       ARM_A.PageTablePDE p {x. e & x=ParityEnabled} mw
   | Some (KOArch (KOPDE (ARM_H.SectionPDE p e mw c g xn rights))) \<Rightarrow>
       ARM_A.SectionPDE p {x. e & x=ParityEnabled |
                                      c & x=PageCacheable |
                                      g & x=Global |
                                      xn & x=XNever} mw (vm_rights_of rights)
   | Some (KOArch (KOPDE (ARM_H.SuperSectionPDE p e c g xn rights))) \<Rightarrow>
       if is_aligned offs 4 then
         ARM_A.SuperSectionPDE p
           {x. e & x=ParityEnabled | c & x=PageCacheable
             | g & x=Global | xn & x=XNever}
           (vm_rights_of rights)
       else ARM_A.InvalidPDE"

(* Can't pull the whole heap off at once, start with arch specific stuff.*)
definition
  absHeapArch :: "(word32 \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> word32
                 \<Rightarrow> arch_kernel_object \<rightharpoonup> arch_kernel_obj"
  where
  "absHeapArch h a \<equiv> %ako.
   (case ako of
     KOASIDPool (ARM_H.ASIDPool ap) \<Rightarrow>
       Some (ARM_A.ASIDPool (\<lambda>w. ap (ucast w)))
   | KOPTE _ \<Rightarrow>
       if is_aligned a pt_bits then Some (PageTable (absPageTable h a))
       else None
   | KOPDE _ \<Rightarrow>
       if is_aligned a pd_bits then Some (PageDirectory (absPageDirectory h a))
       else None)"

lemma
  assumes ptes:
    "\<forall>x. (\<exists>pte. ksPSpace \<sigma> x = Some (KOArch (KOPTE pte))) \<longrightarrow>
         is_aligned x pt_bits \<longrightarrow>
         (\<forall>y::word8. \<exists>pte'. ksPSpace \<sigma> (x + (ucast y << 2)) =
                           Some (KOArch (KOPTE pte')))"
  and pte_rights:
    "\<forall>x. case ksPSpace \<sigma> x of
           Some (KOArch (KOPTE (ARM_H.LargePagePTE _ _ _ _ r))) \<Rightarrow>
             r \<noteq> VMNoAccess"
    "\<forall>x. case ksPSpace \<sigma> x of
           Some (KOArch (KOPTE (ARM_H.SmallPagePTE _ _ _ _ r))) \<Rightarrow>
             r \<noteq> VMNoAccess"

  assumes pdes:
    "\<forall>x. (\<exists>pde. ksPSpace \<sigma> x = Some (KOArch (KOPDE pde))) \<longrightarrow>
         is_aligned x pd_bits \<longrightarrow>
         (\<forall>y::12 word. \<exists>pde'. ksPSpace \<sigma> (x + (ucast y << 2)) =
                             Some (KOArch (KOPDE pde')))"
  and pde_rights:
    "\<forall>x. case ksPSpace \<sigma> x of
           Some (KOArch (KOPDE (ARM_H.SectionPDE _ _ _ _ _ _ r))) \<Rightarrow>
             r \<noteq> VMNoAccess"
    "\<forall>x. case ksPSpace \<sigma> x of
           Some (KOArch (KOPDE (ARM_H.SuperSectionPDE _ _ _ _ _ r))) \<Rightarrow>
             r \<noteq> VMNoAccess"

  assumes fst_pte:
    "\<forall>x. (\<exists>pte. ksPSpace \<sigma> x = Some (KOArch (KOPTE pte))) \<longrightarrow>
          (\<exists>pte'. ksPSpace \<sigma> (x && ~~ mask pt_bits) =
                  Some (KOArch (KOPTE pte')))"
  assumes fst_pde:
    "\<forall>x. (\<exists>pde. ksPSpace \<sigma> x = Some (KOArch (KOPDE pde))) \<longrightarrow>
          (\<exists>pde'. ksPSpace \<sigma> (x && ~~ mask pd_bits) =
                  Some (KOArch (KOPDE pde')))"
  assumes pspace_aligned': "pspace_aligned' \<sigma>"

  shows
    "pspace_relation
     (%x. case ksPSpace \<sigma> x of
            Some (KOArch ako) \<Rightarrow>
              map_option ArchObj (absHeapArch (ksPSpace \<sigma>) x ako)
          | _ \<Rightarrow> None)
     (%x. case ksPSpace \<sigma> x of Some (KOArch _) \<Rightarrow> ksPSpace \<sigma> x | _ \<Rightarrow> None)"
  supply image_cong_simp [cong del]
  apply (clarsimp simp add: pspace_relation_def dom_def)
  apply (rule conjI)
   apply (clarsimp simp add: pspace_dom_def dom_def UNION_eq)
   apply (rule Collect_cong)
   apply (rule iffI)
    apply (erule exE)
    apply (case_tac "ksPSpace \<sigma> x", simp+)
    apply (clarsimp split: option.splits Structures_H.kernel_object.splits)
    apply (rename_tac arch_kernel_object aa b z)
    apply (simp add: absHeapArch_def)
    apply (case_tac arch_kernel_object)
      apply (clarsimp split: asidpool.splits)
     apply (clarsimp split: if_split_asm)
     using  ptes
     apply (erule_tac x=x in allE)
     apply simp
     apply (erule_tac x=y in allE)
     apply clarsimp
    apply (clarsimp split: if_split_asm)
    using pdes
    apply (erule_tac x=x in allE)
    apply simp
    apply (erule_tac x=y in allE)
    apply clarsimp
   apply (clarsimp split: option.splits Structures_H.kernel_object.splits)
   apply (clarsimp simp add: absHeapArch_def)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object)
     apply (rule_tac x=y in exI)
     apply (clarsimp split: asidpool.splits)
    using fst_pte
    apply (erule_tac x=y in allE)
    apply (clarsimp split: if_split_asm)
    apply (rule_tac x="(y && ~~ mask pt_bits)" in exI, simp)
    apply (simp add: range_composition[symmetric])
    apply (rule_tac x="ucast (y >> 2)" in range_eqI)
    apply (simp add: pt_bits_def pageBits_def)
    apply (simp add: word_size ucast_ucast_mask and_mask_shiftl_comm)
    using pspace_aligned'
    apply (simp add: pspace_aligned'_def dom_def)
    apply (erule_tac x=y in allE)
    apply (simp add: objBitsKO_def archObjSize_def pteBits_def
                     and_not_mask[symmetric] AND_NOT_mask_plus_AND_mask_eq)
   using fst_pde
   apply (erule_tac x=y in allE)
   apply clarsimp
   apply (rule_tac x="(y && ~~ mask pd_bits)" in exI, simp)
   apply (simp add: range_composition[symmetric])
   apply (rule_tac x="ucast (y >> 2)" in range_eqI)
   apply (simp add: pd_bits_def pageBits_def)
   apply (simp add: word_size ucast_ucast_mask and_mask_shiftl_comm)
   using pspace_aligned'
   apply (simp add: pspace_aligned'_def dom_def)
   apply (erule_tac x=y in allE)
   apply (simp add: objBitsKO_def archObjSize_def pdeBits_def
                    and_not_mask[symmetric] AND_NOT_mask_plus_AND_mask_eq)
  apply (simp split: option.splits Structures_H.kernel_object.splits)
  apply (intro allI)
  apply (intro impI)
  apply (elim exE)
  apply (clarsimp split: option.splits Structures_H.kernel_object.splits)
  apply (simp add: absHeapArch_def)
  apply (rename_tac arch_kernel_object z a b)
  apply (case_tac arch_kernel_object)
    apply (clarsimp split: asidpool.splits)
    apply (simp add: other_obj_relation_def asid_pool_relation_def o_def inv_def)
   apply simp
   apply (clarsimp simp: pte_relation_def pte_relation_aligned_def
                  split: if_split_asm)
   using ptes
   apply (erule_tac x=x in allE)
   apply simp
   apply (erule_tac x=y in allE)
   apply clarsimp
   apply (rule_tac x=pte' in exI)
   apply (simp add: absPageTable_def  split: option.splits ARM_H.pte.splits)
   apply (clarsimp simp add:  vmrights_map_def vm_rights_of_def
              vm_kernel_only_def vm_read_only_def vm_read_write_def
            split: vmrights.splits)
   using pte_rights
   apply -[1]
   apply (erule_tac x="x + (ucast y << 2)" in allE)+
   subgoal by fastforce
  apply (clarsimp split: if_split_asm)
  using pdes
  apply (erule_tac x=x in allE)
  apply simp
  apply (erule_tac x=y in allE)
  apply clarsimp
  apply (simp add: pde_relation_def pde_relation_aligned_def)
  apply (simp add: absPageDirectory_def
              split: option.splits ARM_H.pde.splits)
  apply (clarsimp simp add:  vmrights_map_def vm_rights_of_def
             vm_kernel_only_def vm_read_only_def vm_read_write_def
           split: vmrights.splits)
  using pde_rights
  apply -[1]
  apply (erule_tac x="x + (ucast y << 2)" in allE)+
  apply fastforce
  done

definition
  "EndpointMap ep \<equiv> case ep of
                     Structures_H.IdleEP \<Rightarrow> Structures_A.IdleEP
                   | Structures_H.SendEP q \<Rightarrow> Structures_A.SendEP q
                   | Structures_H.RecvEP q \<Rightarrow> Structures_A.RecvEP q"

definition
  "NtfnMap ntfn \<equiv>
      \<lparr> ntfn_obj = case ntfnObj ntfn of
                       Structures_H.IdleNtfn \<Rightarrow> Structures_A.IdleNtfn
                     | Structures_H.WaitingNtfn q \<Rightarrow> Structures_A.WaitingNtfn q
                     | Structures_H.ActiveNtfn b \<Rightarrow> Structures_A.ActiveNtfn b
      , ntfn_bound_tcb = ntfnBoundTCB ntfn
      , ntfn_sc = ntfnSc ntfn \<rparr>"

fun
  CapabilityMap :: "capability \<Rightarrow> cap"
 where
  "CapabilityMap capability.NullCap = cap.NullCap"
| "CapabilityMap (capability.UntypedCap d ref n idx) = cap.UntypedCap d ref n idx"
| "CapabilityMap (capability.EndpointCap ref b sr rr gr grr) =
   cap.EndpointCap ref b {x. sr \<and> x = AllowSend \<or> rr \<and> x = AllowRecv \<or>
                             gr \<and> x = AllowGrant \<or> grr \<and> x = AllowGrantReply}"
| "CapabilityMap (capability.NotificationCap ref b sr rr) =
   cap.NotificationCap ref b {x. sr \<and> x = AllowSend \<or> rr \<and> x = AllowRecv}"
| "CapabilityMap (capability.CNodeCap ref n L l) =
   cap.CNodeCap ref n (bin_to_bl l (uint L))"
| "CapabilityMap (capability.ThreadCap ref) = cap.ThreadCap ref"
| "CapabilityMap capability.DomainCap = cap.DomainCap"
| "CapabilityMap (capability.ReplyCap ref gr) =
   cap.ReplyCap ref {x. gr \<and> x = AllowGrant \<or> x = AllowWrite}"
| "CapabilityMap (SchedContextCap sc n) = cap.SchedContextCap sc (n - min_sched_context_bits)"
| "CapabilityMap SchedControlCap = cap.SchedControlCap"
| "CapabilityMap capability.IRQControlCap = cap.IRQControlCap"
| "CapabilityMap (capability.IRQHandlerCap irq) = cap.IRQHandlerCap irq"
| "CapabilityMap (capability.Zombie p b n) =
   cap.Zombie p (case b of ZombieTCB \<Rightarrow> None | ZombieCNode n \<Rightarrow> Some n) n"
| "CapabilityMap (capability.ArchObjectCap (arch_capability.ASIDPoolCap x y)) =
   cap.ArchObjectCap (arch_cap.ASIDPoolCap x y)"
| "CapabilityMap (capability.ArchObjectCap (arch_capability.ASIDControlCap)) =
   cap.ArchObjectCap (arch_cap.ASIDControlCap)"
| "CapabilityMap (capability.ArchObjectCap
                    (arch_capability.PageCap d word rghts sz data)) =
   cap.ArchObjectCap (arch_cap.PageCap d word (vm_rights_of rghts) sz data)"
| "CapabilityMap (capability.ArchObjectCap
                    (arch_capability.PageTableCap word data)) =
  cap.ArchObjectCap (arch_cap.PageTableCap word data)"
| "CapabilityMap (capability.ArchObjectCap
                    (arch_capability.PageDirectoryCap word data)) =
  cap.ArchObjectCap (arch_cap.PageDirectoryCap word data)"

(* FIXME: wellformed_cap_simps has lots of duplicates. *)
lemma cap_relation_imp_CapabilityMap:
  "\<lbrakk>wellformed_cap c; cap_relation c c'\<rbrakk> \<Longrightarrow> CapabilityMap c' = c"
  apply (case_tac c; simp add: wellformed_cap_simps)
       apply (rule set_eqI, clarsimp)
       apply (case_tac "x", simp_all)
      apply (rule set_eqI, clarsimp)
      apply (case_tac "x", simp_all add: word_bits_def)
     apply clarsimp
     apply (simp add: set_eq_iff, rule allI)
     apply (case_tac x; clarsimp)
    apply (simp add: uint_of_bl_is_bl_to_bin bl_bin_bl[simplified])
   apply (simp add: zbits_map_def split: option.splits)
  apply (rename_tac arch_cap)
  apply clarsimp
  apply (case_tac arch_cap, simp_all add: wellformed_cap_simps)
  done

primrec
  ThStateMap :: "Structures_H.thread_state \<Rightarrow> Structures_A.thread_state"
where
  "ThStateMap Structures_H.thread_state.Running =
              Structures_A.thread_state.Running"
| "ThStateMap Structures_H.thread_state.Restart =
              Structures_A.thread_state.Restart"
| "ThStateMap Structures_H.thread_state.Inactive =
              Structures_A.thread_state.Inactive"
| "ThStateMap Structures_H.thread_state.IdleThreadState =
              Structures_A.thread_state.IdleThreadState"
| "ThStateMap (Structures_H.thread_state.BlockedOnReply r) =
              Structures_A.thread_state.BlockedOnReply (the r)"
| "ThStateMap (Structures_H.thread_state.BlockedOnReceive oref grant r) =
              Structures_A.thread_state.BlockedOnReceive oref r \<lparr> receiver_can_grant = grant \<rparr>"
| "ThStateMap (Structures_H.thread_state.BlockedOnSend oref badge grant grant_reply call) =
              Structures_A.thread_state.BlockedOnSend oref
                \<lparr> sender_badge = badge,
                  sender_can_grant = grant,
                  sender_can_grant_reply = grant_reply,
                  sender_is_call = call \<rparr>"
| "ThStateMap (Structures_H.thread_state.BlockedOnNotification oref) =
              Structures_A.thread_state.BlockedOnNotification oref"

lemma thread_state_relation_imp_ThStateMap:
  "thread_state_relation ts ts' \<Longrightarrow> ThStateMap ts' = ts"
by (cases ts) simp_all

definition
  "LookupFailureMap \<equiv> \<lambda>lf. case lf of
     Fault_H.lookup_failure.InvalidRoot \<Rightarrow>
         ExceptionTypes_A.lookup_failure.InvalidRoot
     | Fault_H.lookup_failure.MissingCapability n \<Rightarrow>
         ExceptionTypes_A.lookup_failure.MissingCapability n
     | Fault_H.lookup_failure.DepthMismatch n m \<Rightarrow>
         ExceptionTypes_A.lookup_failure.DepthMismatch n m
     | Fault_H.lookup_failure.GuardMismatch n g l \<Rightarrow>
         ExceptionTypes_A.lookup_failure.GuardMismatch n (bin_to_bl l (uint g))"

lemma LookupFailureMap_lookup_failure_map:
  "(\<forall>n g. lf = ExceptionTypes_A.GuardMismatch n g \<longrightarrow> length g \<le> 32)
   \<Longrightarrow> LookupFailureMap (lookup_failure_map lf) = lf"
  by (clarsimp simp add: LookupFailureMap_def lookup_failure_map_def
                         uint_of_bl_is_bl_to_bin
               simp del: bin_to_bl_def
               split: ExceptionTypes_A.lookup_failure.splits)

primrec
  ArchFaultMap :: "Fault_H.arch_fault \<Rightarrow> ExceptionTypes_A.arch_fault"
where
  "ArchFaultMap (ArchFault_H.ARM_H.arch_fault.VMFault p m) = Machine_A.ARM_A.arch_fault.VMFault p m"


primrec
  FaultMap :: "Fault_H.fault \<Rightarrow> ExceptionTypes_A.fault"
where
  "FaultMap (Fault_H.fault.CapFault ref b failure) =
     ExceptionTypes_A.fault.CapFault ref b (LookupFailureMap failure)"
| "FaultMap (Fault_H.fault.Timeout b) =
     ExceptionTypes_A.fault.Timeout b"
| "FaultMap (Fault_H.fault.ArchFault fault) =
     ExceptionTypes_A.fault.ArchFault (ArchFaultMap fault)"
| "FaultMap (Fault_H.fault.UnknownSyscallException n) =
     ExceptionTypes_A.fault.UnknownSyscallException n"
| "FaultMap (Fault_H.fault.UserException x y) =
     ExceptionTypes_A.fault.UserException x y"

lemma ArchFaultMap_arch_fault_map: "ArchFaultMap (arch_fault_map f) = f"
  by (cases f, simp add: ArchFaultMap_def arch_fault_map_def)

lemma FaultMap_fault_map[simp]:
  "valid_fault ft \<Longrightarrow> FaultMap (fault_map ft) = ft"
  apply (case_tac ft; simp)
   apply (simp add: valid_fault_def LookupFailureMap_lookup_failure_map word_bits_def)
  apply (rule ArchFaultMap_arch_fault_map)
  done

definition
  "ArchTcbMap atcb \<equiv>
    \<lparr> tcb_context =  atcbContext atcb \<rparr>"

lemma arch_tcb_relation_imp_ArchTcnMap:
  "\<lbrakk> arch_tcb_relation atcb atcb'\<rbrakk> \<Longrightarrow> ArchTcbMap atcb' = atcb"
  by (clarsimp simp: arch_tcb_relation_def ArchTcbMap_def)

definition
  "TcbMap tcb \<equiv>
     \<lparr>tcb_ctable = CapabilityMap (cteCap (tcbCTable tcb)),
      tcb_vtable = CapabilityMap (cteCap (tcbVTable tcb)),
      tcb_ipcframe = CapabilityMap (cteCap (tcbIPCBufferFrame tcb)),
      tcb_fault_handler = CapabilityMap (cteCap (tcbFaultHandler tcb)),
      tcb_timeout_handler = CapabilityMap (cteCap (tcbTimeoutHandler tcb)),
      tcb_state = ThStateMap (tcbState tcb),
      tcb_ipc_buffer = tcbIPCBuffer tcb,
      tcb_fault = map_option FaultMap (tcbFault tcb),
      tcb_bound_notification = tcbBoundNotification tcb,
      tcb_mcpriority = tcbMCP tcb,
      tcb_sched_context = tcbSchedContext tcb,
      tcb_yield_to = tcbYieldTo tcb,
      tcb_priority = tcbPriority tcb,
      tcb_domain = tcbDomain tcb,
      tcb_arch = ArchTcbMap (tcbArch tcb)\<rparr>"

definition absCNode :: "nat \<Rightarrow> (obj_ref \<rightharpoonup> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> Structures_A.kernel_object"
  where
  "absCNode sz h a \<equiv> CNode sz (\<lambda>bl. if length bl = sz
                                     then Some (CapabilityMap
                                                  (case (h (a + of_bl bl * 2^cteSizeBits)) of
                                                     Some (KOCTE cte) \<Rightarrow> cteCap cte))
                                     else None)"

definition scMap :: "(obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> sched_context \<Rightarrow> Structures_A.sched_context" where
  "scMap replyPrevs sc = \<lparr>
     sc_period     = scPeriod sc,
     sc_budget     = scBudget sc,
     sc_consumed   = scConsumed sc,
     sc_tcb        = scTCB sc,
     sc_ntfn       = scNtfn sc,
     sc_refills    = refills_map (scRefillHead sc) (scRefillCount sc) (scRefillMax sc) (scRefills sc),
     sc_refill_max = scRefillMax sc,
     sc_badge      = scBadge sc,
     sc_yield_from = scYieldFrom sc,
     sc_replies    = heap_walk replyPrevs (scReply sc) [],
     sc_sporadic   = scSporadic sc
   \<rparr>"

definition
  "mapScSize sc \<equiv> scBitsFromRefillLength' (length (scRefills sc)) - minSchedContextBits"

definition replyMap :: "reply \<Rightarrow>  Structures_A.reply" where
  "replyMap r = \<lparr> reply_tcb = replyTCB r, reply_sc = replySC r \<rparr>"

definition
  absHeap :: "(word32 \<rightharpoonup> vmpage_size) \<Rightarrow> (word32 \<rightharpoonup> nat) \<Rightarrow>
              (word32 \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> Structures_A.kheap"
  where
  "absHeap ups cns h \<equiv> \<lambda>x.
     case h x of
       Some (KOEndpoint ep) \<Rightarrow> Some (Endpoint (EndpointMap ep))
     | Some (KONotification ntfn) \<Rightarrow> Some (Notification (NtfnMap ntfn))
     | Some KOKernelData \<Rightarrow> undefined \<comment> \<open>forbidden by pspace_relation\<close>
     | Some KOUserData \<Rightarrow> map_option (ArchObj \<circ> DataPage False) (ups x)
     | Some KOUserDataDevice \<Rightarrow> map_option (ArchObj \<circ> DataPage True) (ups x)
     | Some (KOTCB tcb) \<Rightarrow> Some (TCB (TcbMap tcb))
     | Some (KOCTE cte) \<Rightarrow> map_option (%sz. absCNode sz h x) (cns x)
     | Some (KOReply reply) \<Rightarrow> Some (Structures_A.Reply (replyMap reply))
     | Some (KOSchedContext sc) \<Rightarrow> Some (Structures_A.SchedContext
                                           (scMap (h |> reply_of' |> replyPrev) sc) (mapScSize sc))
     | Some (KOArch ako) \<Rightarrow> map_option ArchObj (absHeapArch h x ako)
     | None \<Rightarrow> None"

lemma unaligned_page_offsets_helper:
  "\<lbrakk>is_aligned y (pageBitsForSize vmpage_size); n\<noteq>0;
    n < 2 ^ (pageBitsForSize vmpage_size - pageBits)\<rbrakk>
   \<Longrightarrow> \<not> is_aligned (y + n * 2 ^ pageBits :: word32) (pageBitsForSize vmpage_size)"
  apply (simp (no_asm_simp) add: is_aligned_mask)
  apply (simp add: mask_add_aligned)
  apply (cut_tac mask_eq_iff_w2p [of "pageBitsForSize vmpage_size" "n * 2 ^ pageBits"])
   prefer 2
   apply (case_tac vmpage_size, simp_all add: pageBits_def word_size)
  apply (cut_tac word_power_nonzero_32[of n pageBits];
         simp add: word_bits_conv pageBits_def)
   prefer 2
   apply (case_tac vmpage_size, simp_all add: pageBits_def word_size)
     apply (frule less_trans[of n _ "0x100000"], simp+)+
  apply clarsimp
  apply (case_tac vmpage_size, simp_all add: pageBits_def)
    apply (frule_tac i=n and k="0x1000" in word_mult_less_mono1, simp+)+
  done

lemma pspace_aligned_distinct_None:
  (* NOTE: life would be easier if pspace_aligned and pspace_distinct were defined on PSpace instead of the whole kernel state. *)
assumes pspace_aligned:
  "\<forall>x\<in>dom ha. is_aligned (x :: word32) (obj_bits (the (ha x)))"
assumes pspace_distinct:
  "\<forall>x y ko ko'.
   ha x = Some ko \<and> ha y = Some ko' \<and> x \<noteq> y \<longrightarrow>
   {x..x + (2 ^ obj_bits ko - 1)} \<inter> {y..y + (2 ^ obj_bits ko' - 1)} = {}"
shows
  "\<lbrakk>ha x = Some ko; y \<in> {0<..<2^(obj_bits ko)}\<rbrakk> \<Longrightarrow> ha (x+y) = None"
  using pspace_aligned[simplified dom_def, simplified]
  apply (erule_tac x=x in allE)
  apply (rule ccontr)
  apply clarsimp
  apply (rename_tac ko')
  using pspace_distinct pspace_aligned[simplified dom_def, simplified]
  apply (erule_tac x=x in allE)
  apply (erule_tac x="x+y" in allE)+
  apply (clarsimp simp add: word_gt_0)
  apply (clarsimp simp add: ucast_of_nat_small is_aligned_mask mask_2pm1[symmetric])
  apply (frule (1) is_aligned_AND_less_0)
  apply (clarsimp simp add: word_plus_and_or_coroll le_word_or2)
  apply (simp add: word_bool_alg.disj_assoc le_word_or2)
  apply (simp add: word_plus_and_or_coroll[symmetric])
  apply (subgoal_tac "x + y \<le> x + mask (obj_bits ko)", simp)
  apply (rule word_add_le_mono2)
   apply (simp add: mask_def plus_one_helper)
  apply (thin_tac "~ P" for P)+
  apply (thin_tac "(x::'a::len word) < y" for x y)+
  apply (thin_tac "x = Some y" for x y)+
  apply (thin_tac "x && mask (obj_bits ko') = 0" for x)
  apply (thin_tac "x && y = 0")
  apply (clarsimp simp add: dvd_def word_bits_len_of word_bits_conv
                            and_mask_dvd_nat[symmetric])
  apply (cut_tac x=x in unat_lt2p)
  apply (cut_tac x="mask (obj_bits ko)::word32" in unat_lt2p)
  apply (simp add: mult.commute
                   add.commute[of "unat (mask (obj_bits ko))"])
  apply (case_tac "k=0", simp+)
  apply (subgoal_tac "obj_bits ko\<le>32")
   prefer 2
   apply (rule ccontr)
   apply (simp add: not_le)
   apply (frule_tac a="2::nat" and n=32 in power_strict_increasing, simp+)
   apply (case_tac "k=1", simp)
   apply (cut_tac m=k and n="2 ^ obj_bits ko" in n_less_n_mult_m,
          (simp(no_asm_simp))+)
   apply (simp only: mult.commute)
  apply (thin_tac "x = y" for x y)+
  apply (clarsimp simp add: le_less)
  apply (erule disjE)
   prefer 2
   apply (simp add: mask_def)
  apply (subgoal_tac "obj_bits ko <= (31::nat)", simp_all)
  apply (simp add: mask_def unat_minus_one word_bits_conv)
  apply (cut_tac w=k and c="2 ^ obj_bits ko" and b="2^(32-obj_bits ko)"
              in less_le_mult_nat)
   apply (simp_all add: power_add[symmetric])
  apply (rule ccontr)
  apply (simp add: not_less)
  apply (simp add: le_less[of "2 ^ (32 - obj_bits ko)"])
  apply (erule disjE)
   prefer 2
   apply (clarsimp simp add: power_add[symmetric])
  apply clarsimp
  apply (drule mult_less_mono1[of "2 ^ (32 - obj_bits ko)" _ "2 ^ obj_bits ko"])
   apply (simp add: power_add[symmetric])+
  done

lemma pspace_aligned_distinct_None':
  assumes pspace_aligned: "pspace_aligned s"
  assumes pspace_distinct: "pspace_distinct s"
  shows
  "\<lbrakk>kheap s x = Some ko; y \<in> {0<..<2^(obj_bits ko)}\<rbrakk> \<Longrightarrow> kheap s (x+y) = None"
  apply (rule pspace_aligned_distinct_None)
     apply (rule pspace_aligned[simplified pspace_aligned_def])
    apply (rule pspace_distinct[simplified pspace_distinct_def])
   apply assumption+
  done

context
begin

private method ako =
  find_goal \<open>match premises in "kheap s p = Some (ArchObj ako)" for s p ako \<Rightarrow> succeed\<close>,
  (rename_tac ako, case_tac ako;
   clarsimp simp: other_obj_relation_def pte_relation_def pde_relation_def split: if_split_asm)

private method ko =
  case_tac ko; clarsimp simp: other_obj_relation_def cte_relation_def split: if_split_asm


lemma absHeap_correct:
  assumes pspace_aligned:  "pspace_aligned s"
  assumes pspace_distinct: "pspace_distinct s"
  assumes valid_objs:      "valid_objs s"
  assumes pspace_relation: "pspace_relation (kheap s) (ksPSpace s')"
  assumes ghost_relation:  "ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')"
  assumes replies:         "sc_replies_relation s s'"
shows
  "absHeap (gsUserPages s') (gsCNodes s') (ksPSpace s') = kheap s"
proof -
  note relatedE = pspace_dom_relatedE[OF _ pspace_relation]
  from ghost_relation
  have gsUserPages:
    "\<And>a sz. (\<exists>dev. kheap s a = Some (ArchObj (DataPage dev sz))) \<longleftrightarrow>
             gsUserPages s' a = Some sz"
   and gsCNodes:
    "\<And>a n. (\<exists>cs. kheap s a = Some (CNode n cs) \<and> well_formed_cnode_n n cs) \<longleftrightarrow>
            gsCNodes s' a = Some n"
    by (fastforce simp add: ghost_relation_def)+

  show "?thesis"
    supply image_cong_simp [cong del]
    apply (rule ext)
    apply (simp add: absHeap_def split: option.splits)
    apply (rule conjI)
     using pspace_relation
     apply (clarsimp simp: pspace_relation_def pspace_dom_def UNION_eq dom_def Collect_eq)
     apply (erule_tac x=x in allE)
     apply clarsimp
     apply (case_tac "kheap s x", simp)
     apply (rename_tac ko)
     apply (erule_tac x=x in allE, clarsimp)
     apply (erule_tac x=x in allE, simp add: Ball_def)
     apply (erule_tac x=x in allE, clarsimp)

     apply (case_tac ko; simp add: other_obj_relation_def split: if_split_asm kernel_object.splits)
      apply (rename_tac sz cs)
      apply (clarsimp simp: image_def cte_map_def well_formed_cnode_n_def Collect_eq dom_def)
      apply (erule_tac x="replicate sz False" in allE)+
      apply simp
     apply (rename_tac arch_kernel_obj)
     apply (case_tac arch_kernel_obj; simp add: image_def)
       apply (erule_tac x=0 in allE, simp)
      apply (erule_tac x=0 in allE, simp)
     apply clarsimp
     apply (erule_tac x=0 in allE, simp add: pageBits_def)
     apply (rename_tac vmpage_size)
     apply (case_tac vmpage_size; simp)

    apply (clarsimp split: kernel_object.splits)
    apply (intro conjI impI allI)
             apply (erule relatedE, ko, ako)
             apply (clarsimp simp: ep_relation_def EndpointMap_def
                             split: Structures_A.endpoint.splits)
            apply (erule relatedE, ko, ako)
            apply (clarsimp simp: ntfn_relation_def NtfnMap_def
                            split: Structures_A.ntfn.splits)
           apply (erule relatedE, ko, ako)
          apply (erule relatedE, ko, ako)
          apply (rename_tac vmpage_size n)
          apply (cut_tac a=y and sz=vmpage_size in gsUserPages, clarsimp split: if_split_asm)
          apply (case_tac "n=0", simp)
          apply (case_tac "kheap s (y + n * 2 ^ pageBits)")
           apply (rule ccontr)
           apply (clarsimp dest!: gsUserPages[symmetric, THEN iffD1] )
          using pspace_aligned
          apply (simp add: pspace_aligned_def dom_def)
          apply (erule_tac x=y in allE)
          apply (case_tac "n=0",(simp split: if_split_asm)+)
          apply (frule (2) unaligned_page_offsets_helper)
          apply (frule_tac y="n*2^pageBits" in pspace_aligned_distinct_None'
                                            [OF pspace_aligned pspace_distinct])
           apply simp
           apply (rule conjI, clarsimp simp add: word_gt_0)
           apply (simp add: is_aligned_mask)
           apply (clarsimp simp add: pageBits_def mask_def)
           apply (case_tac vmpage_size; frule_tac i=n and k="0x1000" in word_mult_less_mono1; simp)
          apply simp

         apply (erule relatedE, ko, ako)
         apply (rename_tac vmpage_size n)
         apply (cut_tac a=y and sz=vmpage_size in gsUserPages, clarsimp split: if_split_asm)
         apply (case_tac "n=0", simp)
         apply (case_tac "kheap s (y + n * 2 ^ pageBits)")
          apply (rule ccontr)
          apply (clarsimp dest!: gsUserPages[symmetric, THEN iffD1])
         using pspace_aligned
         apply (simp add: pspace_aligned_def dom_def)
         apply (erule_tac x=y in allE)
         apply (case_tac "n=0"; simp)
         apply (frule (2) unaligned_page_offsets_helper)
         apply (frule_tac y="n*2^pageBits" in pspace_aligned_distinct_None'
                                           [OF pspace_aligned pspace_distinct])
          apply simp
          apply (rule conjI, clarsimp simp add: word_gt_0)
          apply (simp add: is_aligned_mask)
          apply (clarsimp simp add: pageBits_def mask_def)
          apply (case_tac vmpage_size; frule_tac i=n and k="0x1000" in word_mult_less_mono1; simp)
         apply simp

        apply (erule relatedE, ko, ako)
        apply (clarsimp simp: TcbMap_def tcb_relation_def valid_obj_def)
        apply (rename_tac tcb y tcb')
        apply (case_tac tcb, case_tac tcb')
        apply (simp add: thread_state_relation_imp_ThStateMap)
        apply (subgoal_tac "map_option FaultMap (tcbFault tcb) = tcb_fault")
         prefer 2
         apply (simp add: fault_rel_optionation_def)
         using valid_objs[simplified valid_objs_def dom_def fun_app_def, simplified]
         apply (erule_tac x=y in allE)
         apply (clarsimp simp: valid_obj_def valid_tcb_def split: option.splits)
        using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
        apply (erule_tac x=y in allE)
        apply (clarsimp simp: cap_relation_imp_CapabilityMap valid_obj_def valid_tcb_def
                              ran_tcb_cap_cases valid_cap_def2 arch_tcb_relation_imp_ArchTcnMap)

       apply (erule relatedE, ko, ako)
       apply (simp add: absCNode_def cte_map_def)
       apply (cut_tac a=y and n=sz in gsCNodes, clarsimp)
       using pspace_aligned[simplified pspace_aligned_def]
       apply (drule_tac x=y in bspec, clarsimp)
       apply clarsimp
       apply (case_tac "(of_bl ya::word32) * 2^cte_level_bits = 0", simp)
        apply (rule ext)
        apply simp
        apply (rule conjI)
         prefer 2
         using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
         apply (erule_tac x=y in allE)
         apply (clarsimp simp: valid_obj_def valid_cs_def valid_cs_size_def
                               well_formed_cnode_n_def dom_def Collect_eq)
         apply (frule_tac x=ya in spec, simp)
         apply (erule_tac x=bl in allE)
         apply clarsimp
        apply (frule pspace_relation_absD[OF _ pspace_relation])
        apply (simp add: cte_map_def)
        apply (drule_tac x="y + of_bl bl * 2^cte_level_bits" in spec)
        apply clarsimp
        apply (erule_tac x="cte_relation bl" in allE)
        apply (erule impE)
         apply (fastforce simp add: well_formed_cnode_n_def)
        apply clarsimp
        apply (clarsimp simp add: cte_relation_def)
        apply (rule cap_relation_imp_CapabilityMap)
         using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
         apply (erule_tac x=y in allE)
         apply (clarsimp simp: valid_obj_def valid_cs_def valid_cap_def2 ran_def)
         apply (fastforce simp: cte_level_bits_def cteSizeBits_def)+
       apply (subgoal_tac "kheap s (y + of_bl ya * 2^cte_level_bits) = None")
        prefer 2
        using valid_objs[simplified valid_objs_def Ball_def dom_def fun_app_def]
        apply (erule_tac x=y in allE)
        apply (clarsimp simp add: valid_obj_def valid_cs_def valid_cs_size_def)
        apply (rule pspace_aligned_distinct_None'[OF
                    pspace_aligned pspace_distinct], assumption)
        apply (clarsimp simp: word_neq_0_conv power_add cte_index_repair)
        apply (simp add: well_formed_cnode_n_def dom_def Collect_eq)
        apply (erule_tac x=ya in allE)+
        apply (rule word_mult_less_mono1)
          apply (subgoal_tac "sz = length ya")
           apply simp
           apply (rule of_bl_length, (simp add: word_bits_def)+)[1]
          apply fastforce
         apply (simp add: cte_level_bits_def)
        apply (simp add: word_bits_conv cte_level_bits_def)
        apply (drule_tac a="2::nat" in power_strict_increasing, simp+)
       apply (rule ccontr, clarsimp)
       apply (cut_tac a="y + of_bl ya * 2^cte_level_bits" and n=yc in gsCNodes)
       apply clarsimp

      (* mapping architecture-specific objects *)
      apply clarsimp
      apply (rename_tac x arch_kernel_object)
      apply (erule relatedE, ko)
      apply (rename_tac y P arch_kernel_obj)
      apply (case_tac arch_kernel_object; simp add: absHeapArch_def split: asidpool.splits)

        apply clarsimp
        apply (case_tac arch_kernel_obj)
           apply (simp add: other_obj_relation_def asid_pool_relation_def inv_def o_def)
          apply (clarsimp simp add:  pte_relation_def)
         apply (clarsimp simp add:  pde_relation_def)
        apply (clarsimp split: if_split_asm)+

       apply (case_tac arch_kernel_obj)
          apply (simp add: other_obj_relation_def asid_pool_relation_def inv_def o_def)
         using pspace_aligned[simplified pspace_aligned_def Ball_def dom_def]
         apply (erule_tac x=y in allE)
         apply (clarsimp simp add: pte_relation_def absPageTable_def pt_bits_def pageBits_def)
         apply (rule conjI)
          prefer 2
          apply clarsimp
          apply (rule sym)
          apply (rule pspace_aligned_distinct_None'[OF pspace_aligned pspace_distinct]; simp)
          apply (cut_tac x=ya and n="2^10" in
                 ucast_less_shiftl_helper[where 'a=32,simplified word_bits_conv]; simp)
          apply (clarsimp simp add: word_gt_0)
         apply clarsimp
         apply (subgoal_tac "ucast ya << 2 = 0")
          prefer 2
          apply (rule ccontr)
          apply (frule_tac x=y in unaligned_helper, assumption)
           apply (rule ucast_less_shiftl_helper; simp)
          apply simp
         apply simp
         apply (rule ext)
         apply (frule pspace_relation_absD[OF _ pspace_relation])
         apply simp
         apply (erule_tac x=offs in allE)
         apply (clarsimp simp add: pte_relation_def)
         using valid_objs[simplified valid_objs_def fun_app_def dom_def, simplified]
         apply (erule_tac x=y in allE)
         apply (clarsimp simp add: valid_obj_def wellformed_pte_def)
         apply (erule_tac x=offs in allE)
         apply (rename_tac pte')
         apply (case_tac pte', simp_all add: pte_relation_aligned_def)[1]
          apply (clarsimp split: ARM_A.pte.splits)
          apply (rule set_eqI, clarsimp)
          apply (case_tac x; simp)
         apply (clarsimp split: ARM_A.pte.splits)
         apply (rule set_eqI, clarsimp)
         apply (case_tac x; simp)
        apply (clarsimp simp add: pde_relation_def)
       apply (clarsimp split: if_split_asm)

      apply (case_tac arch_kernel_obj)
         apply (simp add: other_obj_relation_def asid_pool_relation_def inv_def o_def)
        apply (clarsimp simp add:  pte_relation_def)
       using pspace_aligned
       apply (simp add: pspace_aligned_def dom_def)
       apply (erule_tac x=y in allE)
       apply (clarsimp simp add: pde_relation_def absPageDirectory_def pd_bits_def pageBits_def)
       apply (rule conjI)
        prefer 2
        apply clarsimp
        apply (rule sym)
        apply (rule pspace_aligned_distinct_None' [OF pspace_aligned pspace_distinct]; simp)
        apply (cut_tac x=ya and n="2^14" in
               ucast_less_shiftl_helper[where 'a=32, simplified word_bits_conv]; simp)
        apply (clarsimp simp add: word_gt_0)
       apply clarsimp
       apply (subgoal_tac "ucast ya << 2 = 0")
        prefer 2
        apply (rule ccontr)
        apply (frule_tac x=y in unaligned_helper, assumption)
         apply (rule ucast_less_shiftl_helper; simp)
        apply simp
       apply simp
       apply (rule ext)
       apply (frule pspace_relation_absD[OF _ pspace_relation])
       apply simp
       apply (erule_tac x=offs in allE)
       apply (clarsimp simp add: pde_relation_def)

       using valid_objs[simplified valid_objs_def fun_app_def dom_def,simplified]
       apply (erule_tac x=y in allE)
       apply (clarsimp simp add: valid_obj_def wellformed_pde_def)
       apply (erule_tac x=offs in allE)
       apply (rename_tac pde')
       apply (case_tac pde'; simp add: pde_relation_aligned_def)
          apply (clarsimp split: ARM_A.pde.splits)+
         apply (fastforce simp add: subset_eq)
        apply (clarsimp split: ARM_A.pde.splits)
        apply (rule set_eqI, clarsimp)
        apply (case_tac x; simp)
       apply (clarsimp split: ARM_A.pde.splits)
       apply (rule set_eqI, clarsimp)
       apply (case_tac x; simp)
      apply (clarsimp simp add: pde_relation_def split: if_split_asm)

     apply (rule relatedE, assumption, ko, ako)
     apply (frule scBits_inverse_sc_relation)
     apply (clarsimp simp: sc_relation_def scMap_def mapScSize_def sc_replies_prevs_walk[OF replies])

    apply (erule relatedE, ko, ako)
    apply (clarsimp simp: reply_relation_def replyMap_def)
    done
qed

end

text \<open>The following function can be used to reverse cte_map.\<close>
definition
  "cteMap cns \<equiv> \<lambda>p.
   let P = (%(a,bl). cte_map (a,bl) = p \<and> cns a = Some (length bl))
   in if \<exists>x. P x then (SOME x. P x)
      else (p && ~~ mask tcbBlockSizeBits, bin_to_bl 3 (uint (p >> cte_level_bits)))"

lemma tcb_cap_cases_length:
  "tcb_cap_cases b = Some x \<Longrightarrow> length b = 3"
by (simp add: tcb_cap_cases_def tcb_cnode_index_def split: if_split_asm)

lemma of_bl_mult_and_not_mask_eq:
  "\<lbrakk>is_aligned (a :: word32) n; length b + m \<le> n\<rbrakk>
   \<Longrightarrow> a + of_bl b * (2^m) && ~~ mask n = a"
  apply (simp add: shiftl_t2n[simplified mult.commute, symmetric])
  apply (simp add: mask_out_add_aligned[where q="of_bl b << m", symmetric])
  apply (case_tac "n<32")
   prefer 2
   apply (simp add: not_less power_overflow mask_def)
  apply (simp add: mask_eq_x_eq_0[symmetric])
  apply (rule less_mask_eq)
  apply (rule shiftl_less_t2n, simp_all)
  apply (cut_tac 'a=32 and xs=b in of_bl_length, simp)
  apply (drule nat_move_sub_le)
  apply (drule two_power_increasing[where 'a=32], simp)
  apply (drule (2) less_le_trans)
done

lemma bin_to_bl_of_bl_eq:
  "\<lbrakk>is_aligned (a::'a::len word) n; length b + c \<le> n; length b + c < LENGTH('a)\<rbrakk>
  \<Longrightarrow> bin_to_bl (length b) (uint ((a + of_bl b * 2^c) >> c)) = b"
  apply (subst word_plus_and_or_coroll)
   apply (erule is_aligned_get_word_bits)
    apply (rule is_aligned_AND_less_0)
     apply (simp add: is_aligned_mask)
    apply (rule order_less_le_trans)
     apply (rule of_bl_length2)
     apply (simp add: word_bits_conv cte_level_bits_def)
    apply (simp add: two_power_increasing)
   apply simp
  apply (rule nth_equalityI)
   apply (simp only: len_bin_to_bl)
  apply (clarsimp simp only: len_bin_to_bl nth_bin_to_bl
                             word_test_bit_def[symmetric])
  apply (simp add: nth_shiftr nth_shiftl
                   shiftl_t2n[where n=c, simplified mult.commute,
                              simplified, symmetric])
  apply (simp add: is_aligned_nth[THEN iffD1, rule_format]
                   test_bit_of_bl nth_rev)
  apply (case_tac "b ! i", simp_all)
  apply arith
  done

lemma TCB_implies_KOTCB:
  "\<lbrakk>pspace_relation (kheap s) (ksPSpace s'); kheap s a = Some (TCB tcb)\<rbrakk>
   \<Longrightarrow> \<exists>tcb'. ksPSpace s' a = Some (KOTCB tcb') \<and> tcb_relation tcb tcb'"
  apply (clarsimp simp add: pspace_relation_def pspace_dom_def
                            dom_def UNION_eq Collect_eq)
  apply (erule_tac x=a in allE)+
  apply (clarsimp simp add: other_obj_relation_def
                  split: Structures_H.kernel_object.splits)
  apply (drule iffD1)
   apply (fastforce simp add: dom_def image_def)
  apply clarsimp
  done

lemma cte_at_CNodeI:
  "\<lbrakk>kheap s a = Some (CNode (length b) cs); well_formed_cnode_n (length b) cs\<rbrakk>
   \<Longrightarrow> cte_at (a,b) s"
  apply (subgoal_tac "\<exists>y. cs b = Some y")
   apply clarsimp
   apply (rule_tac cte=y in cte_wp_at_cteI[of s _ "length b" cs]; simp)
  apply (simp add: well_formed_cnode_n_def dom_def Collect_eq)
  done

lemma cteMap_correct:
  assumes rel:              "(s,s') \<in> state_relation"
  assumes valid_objs:       "valid_objs s"
  assumes pspace_aligned:   "pspace_aligned s"
  assumes pspace_distinct:  "pspace_distinct s"
  assumes pspace_aligned':  "pspace_aligned' s'"
  assumes pspace_distinct': "pspace_distinct' s'"
  shows "p \<in> dom (caps_of_state s) \<longrightarrow> cteMap (gsCNodes s') (cte_map p) = p"
proof -
  from rel have gsCNodes:
    "\<forall>a n. (\<exists>cs. kheap s a = Some (CNode n cs) \<and> well_formed_cnode_n n cs) \<longleftrightarrow>
           gsCNodes s' a = Some n"
    by (simp add: state_relation_def ghost_relation_def)
  show ?thesis
  apply (simp add: dom_def cteMap_def  split: if_split_asm)
  apply (clarsimp simp: caps_of_state_cte_wp_at split: if_split_asm)
  apply (drule cte_wp_cte_at)
  apply (intro conjI impI)
   apply (rule some_equality)
    apply (clarsimp simp add: split_def)
    apply (frule gsCNodes[rule_format,THEN iffD2])
    apply clarsimp
    apply (frule (1) cte_at_CNodeI)
    apply (frule (2) cte_map_inj_eq[OF _ _ _ valid_objs pspace_aligned pspace_distinct])
    apply clarsimp
   apply (clarsimp simp add: split_def)
   apply (frule gsCNodes[rule_format,THEN iffD2])
   apply clarsimp
   apply (frule (1) cte_at_CNodeI)
   apply (frule (2) cte_map_inj_eq[OF _ _ _ valid_objs pspace_aligned pspace_distinct])
   apply clarsimp
  apply (case_tac p)
  apply (clarsimp simp add: cte_wp_at_cases)
  apply (erule disjE)
   apply clarsimp
   apply (drule_tac x=a in spec, drule_tac x=b in spec, simp)
   apply (cut_tac a=a and n=sz in gsCNodes[rule_format])
   apply clarsimp
   apply (simp add: well_formed_cnode_n_def dom_def Collect_eq)
   apply (erule_tac x=b in allE)
   apply simp
  apply (thin_tac "ALL x. P x" for P)
  apply clarsimp
  apply (frule TCB_implies_KOTCB[OF state_relation_pspace_relation[OF rel]])
  apply clarsimp
  using pspace_aligned'[simplified pspace_aligned'_def]
  apply (drule_tac x=a in bspec, simp add: dom_def)
  apply (simp add: objBitsKO_def cte_map_def)
  apply (rule conjI[rotated])
   apply (drule tcb_cap_cases_length)
   apply (frule_tac b=b and c=cte_level_bits in bin_to_bl_of_bl_eq)
     apply (fastforce simp: cte_level_bits_def objBits_defs)+
  apply (case_tac "b = [False, False, False]")
   apply (simp)
  apply (frule_tac b=b and c=cte_level_bits in bin_to_bl_of_bl_eq)
    apply (fastforce simp: tcb_cap_cases_length cte_level_bits_def objBits_defs)+
  apply (subgoal_tac "ksPSpace s' (cte_map (a, b)) = None")
   prefer 2
   apply (rule ccontr)
   apply clarsimp
   using pspace_distinct'[simplified pspace_distinct'_def]
   apply (drule_tac x=a in bspec, simp add: dom_def)
   apply (simp add: ps_clear_def dom_def mask_2pm1[symmetric] x_power_minus_1)
   apply (simp add: objBitsKO_def)
   apply (drule_tac a="cte_map (a, b)" in equals0D)
   apply (clarsimp simp add: cte_map_def)
   apply (drule tcb_cap_cases_length)
   apply (erule impE)
    apply (rule word_plus_mono_right)
     apply (cut_tac 'a=machine_word_len and xs=b in of_bl_length, fastforce simp: word_bits_conv)
     apply (drule_tac k="2^cte_level_bits" in word_mult_less_mono1)
       apply (fastforce simp: cte_level_bits_def objBits_defs)+
     apply (simp add: mask_def)
     apply (rule ccontr)
     apply (simp add: not_le)
     apply (drule (1) less_trans, fastforce simp: cte_level_bits_def objBits_defs)
    apply (drule is_aligned_no_overflow'[simplified mask_2pm1[symmetric]])
    apply (simp add: word_bits_conv)
   apply simp
   apply (erule impE)
    apply (drule is_aligned_no_overflow'[simplified mask_2pm1[symmetric]])
    apply (cut_tac 'a=machine_word_len and xs=b in of_bl_length, simp add: word_bits_conv)
    apply (drule_tac k="2^cte_level_bits" in word_mult_less_mono1)
      apply (fastforce simp: cte_level_bits_def objBits_defs)+
    apply (erule word_random)
    apply (rule order.strict_implies_order)
    apply (erule less_trans)
    apply (fastforce simp: cte_level_bits_def objBits_defs mask_def)
   apply (simp add: mult.commute[of _ "2^cte_level_bits"]
                    shiftl_t2n[of _ cte_level_bits, simplified, symmetric])
   apply word_bitwise
   apply simp
   apply (case_tac b, simp)
   apply (rename_tac b, case_tac b, simp)
   apply (rename_tac b, case_tac b, simp)
   apply (clarsimp simp add: test_bit_of_bl eval_nat_numeral cte_level_bits_def)
  apply (simp add: cte_map_def split: option.splits)
  apply (drule tcb_cap_cases_length)
  apply (rule of_bl_mult_and_not_mask_eq[where m=cte_level_bits, simplified])
   apply (fastforce simp: cte_level_bits_def objBits_defs)+
  done
qed

definition (* NOTE: cnp maps addresses to CNode, offset pairs *)
  "absIsOriginalCap cnp h \<equiv>
   %(oref,cref).
   cnp (cte_map (oref, cref)) = (oref, cref) \<and>
   cte_map (oref,cref) : dom (map_to_ctes h) \<and>
   (\<exists>cte. map_to_ctes h (cte_map (oref,cref)) = Some cte \<and>
          (cteCap cte \<noteq> capability.NullCap) \<and> mdbRevocable (cteMDBNode cte))"

lemma absIsOriginalCap_correct:
assumes valid_ioc: "valid_ioc s"
assumes valid_objs: "valid_objs s"
assumes rel: "(s,s') \<in> state_relation"
assumes pspace_aligned: "pspace_aligned s"
assumes pspace_distinct: "pspace_distinct s"
assumes pspace_aligned': "pspace_aligned' s'"
assumes pspace_distinct': "pspace_distinct' s'"
shows
  "absIsOriginalCap (cteMap (gsCNodes s')) (ksPSpace s') = is_original_cap s"
proof -
  from valid_ioc
  have no_cap_not_orig:
    "\<forall>p. caps_of_state s p = None \<longrightarrow> is_original_cap s p = False"
  and null_cap_not_orig:
    "\<forall>p. caps_of_state s p = Some cap.NullCap \<longrightarrow> is_original_cap s p = False"
    by (fastforce simp: valid_ioc_def2 null_filter_def)+

  have cnp:
  "\<forall>a b. caps_of_state s (a, b) \<noteq> None \<longrightarrow>
         (cteMap (gsCNodes s')) (cte_map (a, b)) = (a, b)"
    using cteMap_correct[OF rel valid_objs pspace_aligned pspace_distinct
                            pspace_aligned' pspace_distinct']
    by (clarsimp simp: dom_def)

  show ?thesis
    apply (subgoal_tac "revokable_relation (is_original_cap s)
                          (null_filter (caps_of_state s)) (ctes_of s') \<and>
                        pspace_relation (kheap s) (ksPSpace s')")
     prefer 2
     using rel
     apply (clarsimp simp add: state_relation_def)
    apply (rule ext)
    apply (clarsimp simp add: revokable_relation_def
                              null_filter_def absIsOriginalCap_def
                       split: if_split_asm)
    apply (erule_tac x=a in allE)
    apply (erule_tac x=b in allE)
    apply (case_tac "caps_of_state s (a, b)")
     apply (clarsimp simp: no_cap_not_orig)
     apply (frule (1) pspace_relation_cte_wp_atI[OF _ _ valid_objs])
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (subgoal_tac "(a,b) = (aa,ba)", simp)
     apply (cut_tac a=aa and b=ba in cnp[rule_format], simp)
     apply (simp add: cte_map_def)
    apply simp
    apply (case_tac "aa = cap.NullCap")
     apply (clarsimp simp add: null_cap_not_orig)
     apply (frule (1) pspace_relation_ctes_ofI
              [OF _ caps_of_state_cteD pspace_aligned' pspace_distinct'])
     apply clarsimp
    apply (frule (1) pspace_relation_ctes_ofI
             [OF _ caps_of_state_cteD pspace_aligned' pspace_distinct'])
    apply (clarsimp simp add: dom_def)
    apply (cut_tac a=a and b=b in cnp[rule_format], simp+)
    apply (case_tac cte, clarsimp)
    apply (case_tac aa, simp_all)
    apply (rename_tac arch_cap)
    apply (case_tac arch_cap, simp_all)
    done
qed

text \<open>
  In the executable specification,
  a linked list connects all children of a certain node.
  More specifically, the predicate @{term "subtree h c c'"} holds iff
  the map @{term h} from addresses to CTEs contains capabilities
  at the addresses @{term c} and @{term c'} and
  the latter is a child of the former.

  In the abstract specification, the capability-derivation tree @{term "cdt s"}
  maps the address of each capability to the address of its immediate parent.

  The definition below takes a binary predicate @{term ds} as parameter,
  which represents a childhood relation like @{term "subtree h"},
  and converts this into an optional function to the immediate parent
  in the same format as @{term "cdt s"}.
\<close>
definition
  "parent_of' ds \<equiv> %x.
   if \<forall>p. \<not> ds p x then None
   else Some (THE p. ds p x \<and> (\<forall>q. ds p q \<and> ds q x \<longrightarrow> p = q))"

definition
  "absCDT cnp h \<equiv>
   \<lambda>(oref,cref).
   if cnp (cte_map (oref, cref)) = (oref, cref)
     then map_option cnp (parent_of' (subtree h) (cte_map (oref, cref)))
   else None"

lemma valid_mdb_mdb_cte_at:
  "valid_mdb s
   \<Longrightarrow> mdb_cte_at (\<lambda>p. \<exists>c. caps_of_state s p = Some c \<and> cap.NullCap \<noteq> c)
      (cdt s)"
  by (simp add: valid_mdb_def2)

lemma ctes_of_cte_wp_atD:
  "ctes_of s p = Some cte \<Longrightarrow> cte_wp_at' ((=) cte) p s"
by (simp add: KHeap_R.cte_wp_at_ctes_of)


lemma absCDT_correct':
assumes pspace_aligned: "pspace_aligned s"
assumes pspace_distinct: "pspace_distinct s"
assumes pspace_aligned': "pspace_aligned' s'"
assumes pspace_distinct': "pspace_distinct' s'"
assumes valid_objs: "valid_objs s"
assumes valid_mdb:  "valid_mdb s"
assumes rel:  "(s,s') \<in> state_relation"
shows
  "absCDT (cteMap (gsCNodes s')) (ctes_of s') = cdt s" (is ?P)
  "(case (cdt s x) of None \<Rightarrow> caps_of_state s x \<noteq> None \<longrightarrow> (\<forall>q. \<not>(ctes_of s' \<turnstile> q \<rightarrow> cte_map x)) |
             Some p \<Rightarrow>
             ctes_of s' \<turnstile> cte_map p \<rightarrow> cte_map x \<and>
                   (\<forall>q. ctes_of s' \<turnstile> cte_map p \<rightarrow> q \<and>
                        ctes_of s' \<turnstile> q \<rightarrow> cte_map x \<longrightarrow>
                        cte_map p = q))" (is ?Q)
proof -

  have cnp:
  "\<forall>a b. caps_of_state s (a, b) \<noteq> None \<longrightarrow>
         (cteMap (gsCNodes s')) (cte_map (a, b)) = (a, b)"
    using cteMap_correct[OF rel valid_objs pspace_aligned pspace_distinct
                            pspace_aligned' pspace_distinct']
    by (clarsimp simp: dom_def)

  from rel
  have descs_eq:
    "\<forall>a b. cte_wp_at (\<lambda>_. True) (a, b) s \<longrightarrow>
           {y. \<exists>x\<in>descendants_of (a, b) (cdt s). y = cte_map x} =
               descendants_of' (cte_map (a, b)) (ctes_of s')"
    apply (clarsimp simp add: state_relation_def)
    apply (clarsimp simp add: swp_def cdt_relation_def image_def)
    done

  from rel
  have pspace_relation: "pspace_relation (kheap s) (ksPSpace s')"
    by (clarsimp simp add: state_relation_def)

  note cdt_has_caps = mdb_cte_atD[OF _ valid_mdb_mdb_cte_at[OF valid_mdb]]
  note descendants_of_simps =
    descendants_of_def cdt_parent_rel_def is_cdt_parent_def

  have descendants_implies:
    "\<And>p p'. p' \<in> descendants_of p (cdt s) \<Longrightarrow>
            \<exists>cap cap'. caps_of_state s p = Some cap \<and>
                       caps_of_state s p' = Some cap'"
    apply (clarsimp simp: descendants_of_simps)
    apply (frule tranclD2, drule tranclD)
    apply (auto dest: cdt_has_caps)
    done

  let ?cnp = "cteMap (gsCNodes s')"
  have subtree_implies:
  "\<And>p p'. subtree (ctes_of s') p p' \<Longrightarrow>
           \<exists>cap cap'. ?cnp p' \<in> descendants_of (?cnp p) (cdt s) \<and>
                      caps_of_state s (?cnp p) = Some cap \<and>
                      caps_of_state s (?cnp p') = Some cap' \<and>
           (\<exists>cte cte'. ctes_of s' p = Some cte \<and> ctes_of s' p' = Some cte')"
    apply (subgoal_tac "(ctes_of s') \<turnstile> p parentOf p'")
     prefer 2
     apply (erule subtree.cases, simp+)
    apply (clarsimp simp add: parentOf_def)
    apply (frule_tac x=p in
      pspace_relation_cte_wp_atI[OF pspace_relation _ valid_objs])
    apply clarsimp
    apply (frule descs_eq[rule_format, OF cte_wp_at_weakenE], simp)
    apply (simp add: descendants_of'_def Collect_eq)
    apply (drule spec, drule(1) iffD2)
    apply (clarsimp simp: cnp cte_wp_at_caps_of_state)
    apply (frule descendants_implies)
    apply (clarsimp simp: cnp)
    done
  have is_parent:
  "\<And>a b p cap cap' a' b' c.
       \<lbrakk>cdt s (a, b) = Some (a', b')\<rbrakk>
       \<Longrightarrow> ctes_of s' \<turnstile> cte_map (a', b') \<rightarrow> cte_map (a, b) \<and>
          (\<forall>q. ctes_of s' \<turnstile> cte_map (a', b') \<rightarrow> q \<and>
               ctes_of s' \<turnstile> q \<rightarrow> cte_map (a, b) \<longrightarrow>
               cte_map (a', b') = q)"
    apply (frule cdt_has_caps)
    using descs_eq pspace_relation
    apply (frule_tac x=a' in spec, erule_tac x=b' in allE)
     apply (simp add: cte_wp_at_caps_of_state Collect_eq descendants_of_simps
                      descendants_of'_def)
     apply (rule conjI)
      apply fastforce
     apply clarsimp
     apply (drule subtree_implies)+
     apply (clarsimp simp: cnp)
     using valid_mdb
     apply (clarsimp simp: cnp descendants_of_simps valid_mdb_def no_mloop_def)
     apply (drule_tac x="?cnp q" and y="(a, b)" in tranclD2)
     apply clarsimp
     apply (fastforce intro: trancl_rtrancl_trancl)
     done


  show ?P
    apply (rule ext)
    using descs_eq pspace_relation
    apply (simp add: absCDT_def)
    apply (rule conjI[rotated])
     apply clarsimp
     apply (rule sym, rule ccontr, clarsimp)
     apply (frule cdt_has_caps)
     using cnp
     apply fastforce
    apply clarsimp

    apply (clarsimp simp: parent_of'_def)
    apply (rule conjI)
     apply clarsimp
     apply (rule sym, rule ccontr, clarsimp)
     apply (simp add: descendants_of_simps descendants_of'_def)
     apply (rename_tac a' b')
     apply (erule_tac x=a' in allE, erule_tac x=b' in allE)
     apply (erule_tac x="cte_map (a', b')" in allE, erule notE)
     apply (frule cdt_has_caps)
     apply (clarsimp simp: cte_wp_at_caps_of_state Collect_eq)
     apply fastforce
    apply clarsimp
    apply (drule subtree_implies)
    apply clarsimp
    apply (case_tac "cdt s (a, b)")
     apply (simp add: descendants_of_simps descendants_of'_def)
     apply (drule tranclD2)
     apply clarsimp
    apply clarsimp
    apply (rename_tac a' b')
    apply (frule cdt_has_caps)
    apply clarsimp
    apply (rule trans[rotated])
     apply (rule cnp[rule_format], simp)
    apply (rule arg_cong[where f="?cnp"])
    apply (rule the_equality)
    apply (rule is_parent,assumption)
    apply clarsimp
    apply (rule ccontr)
    apply (drule_tac x="cte_map (a', b')" in spec, drule mp)
     apply simp_all
    apply (drule subtree_implies)
    apply clarsimp
    apply (drule_tac p=pa in ctes_of_cte_wp_atD)
    apply (drule pspace_relation_cte_wp_atI'[OF pspace_relation _ valid_objs])
    apply (clarsimp simp add: cte_wp_at_caps_of_state cnp)
    apply (thin_tac "(a, b) \<in> descendants_of (?cnp p) (cdt s)",
           thin_tac "caps_of_state s (?cnp p) = Some cap")
    apply (unfold descendants_of'_def)
    apply (erule_tac x=a' in allE)
    apply (erule_tac x=b' in allE)
    apply (simp add: Collect_eq)
    apply (erule_tac x="cte_map (a, b)" in allE)
    apply (drule iffD1)
     apply (rule_tac x="(a, b)" in bexI, simp)
     apply (clarsimp simp: cnp descendants_of_simps)
     apply (rule trancl.intros(1))
     apply simp_all
    apply (rule descs_eq[simplified descendants_of'_def Collect_eq,
                         rule_format, THEN iffD1])
     apply (clarsimp simp add: cte_wp_at_caps_of_state)
    apply (rule_tac x="(a', b')" in bexI, simp)
    apply (clarsimp simp: descendants_of_simps)
    apply (drule_tac x="(aa,ba)" and y="(a, b)" in tranclD2)
    apply clarsimp
    apply (drule rtranclD, erule disjE, simp_all)[1]
     done
  thus ?Q
    apply (case_tac x)
    apply (case_tac "cdt s (a, b)")
     apply (drule sym)
     apply (simp add: mdb_cte_at_def)
     apply (simp add: absCDT_def split_def)
     apply (simp add: parent_of'_def split: if_split_asm)
     apply (intro impI)
     apply (frule_tac a=a and b=b in cnp[simplified,rule_format])
     apply simp
    apply simp
    apply (clarsimp simp: is_parent)
    done
qed

lemmas absCDT_correct = absCDT_correct'(1)
lemmas cdt_simple_rel =  absCDT_correct'(2)


(* Produce a cdt_list from a cdt by sorting the children
   sets by reachability via mdbNext. We then demonstrate
   that a list satisfying the state relation must
   already be sorted in the same way and therefore is
   equivalent. *)

definition sort_cdt_list where
"sort_cdt_list cd m = (\<lambda>p. (THE xs. set xs = {c. cd c = Some p} \<and> partial_sort.psorted (\<lambda>x y. m \<turnstile> cte_map x \<leadsto>\<^sup>* cte_map y) xs \<and> distinct xs))"

end

locale partial_sort_cdt = partial_sort "\<lambda> x y.  m' \<turnstile> cte_map x \<leadsto>\<^sup>* cte_map y"
                                       "\<lambda> x y. cte_at x (s::det_state) \<and> cte_at y s \<and> (\<exists>p. m' \<turnstile> p \<rightarrow> cte_map x \<and> m' \<turnstile> p \<rightarrow> cte_map y)" for m' s +
  fixes s'::"kernel_state"
  fixes m t
  defines "m \<equiv> (cdt s)"
  defines "t \<equiv> (cdt_list s)"
  assumes m'_def : "m' = (ctes_of s')"
  assumes rel:"(s,s') \<in> state_relation"
  assumes valid_mdb: "valid_mdb s"
  assumes assms' : "pspace_aligned s" "pspace_distinct s" "pspace_aligned' s'"
                   "pspace_distinct' s'" "valid_objs s" "valid_mdb s" "valid_list s"

begin

interpretation Arch . (*FIXME: arch_split*)

lemma valid_list_2 : "valid_list_2 t m"
    apply (insert assms')
    apply (simp add: t_def m_def)
    done

lemma has_next_not_child_is_descendant:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "next_not_child slot t m = Some slot2 \<Longrightarrow> (\<exists>p. slot \<in> descendants_of p m)"
  apply (drule next_not_childD)
  apply (simp add: m_def finite_depth assms')+
   using assms'
   apply (simp add: valid_mdb_def)
  apply (elim disjE)
   apply (drule next_sib_same_parent[OF valid_list_2])
   apply (elim exE)
   apply (rule_tac x=p in exI)
   apply (rule child_descendant)
   apply simp
  apply (elim conjE exE)
  apply force
  done


lemma has_next_slot_is_descendant :
    notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
    "next_slot slot t m = Some slot2 \<Longrightarrow> m slot2 = Some slot \<or> (\<exists>p. slot \<in> descendants_of p m)"
    apply (insert valid_list_2)
    apply (simp add: next_slot_def next_child_def split: if_split_asm)
     apply (case_tac "t slot",simp+)
     apply (simp add: valid_list_2_def)
     apply (rule disjI1)
     apply force
    apply (rule disjI2)
    apply (erule has_next_not_child_is_descendant)
    done

lemma descendant_has_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
    shows
  "slot \<in> descendants_of p m \<Longrightarrow> \<exists>q. m slot = Some q"
  apply (simp add: descendants_of_def)
  apply (drule tranclD2)
  apply (simp add: cdt_parent_of_def)
  apply force
  done



lemma next_slot_cte_at:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "next_slot slot t m = Some slot2 \<Longrightarrow> cte_at slot s"
   apply (cut_tac valid_mdb_mdb_cte_at)
   prefer 2
   apply (cut_tac assms')
   apply simp
  apply (fold m_def)
  apply (simp add: mdb_cte_at_def)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule has_next_slot_is_descendant)
  apply (elim disjE)
   apply force
  apply (elim exE)
  apply (drule descendant_has_parent)
  apply force
  done

lemma cte_at_has_cap: "cte_at slot s \<Longrightarrow> \<exists>c. cte_wp_at ((=) c) slot s"
  apply (drule cte_at_get_cap_wp)
  apply force
  done


  lemma next_slot_mdb_next:
  notes split_paired_All[simp del]
  shows
 "next_slot slot t m = Some slot2 \<Longrightarrow> m' \<turnstile> (cte_map slot) \<leadsto> (cte_map slot2)"
    apply (frule cte_at_has_cap[OF next_slot_cte_at])
    apply (elim exE)
    apply (cut_tac s=s and s'=s' in pspace_relation_ctes_ofI)
        apply (fold m'_def)
        using rel
        apply (simp add: state_relation_def)
       apply simp
      using assms'
      apply simp
     using assms'
     apply simp
    apply (subgoal_tac "cdt_list_relation t m m'")
     apply (simp add: cdt_list_relation_def)
     apply (elim exE)
     apply (case_tac cte)
     apply (simp add: mdb_next_rel_def mdb_next_def)
     apply force
    using rel
    apply (simp add: state_relation_def m_def t_def m'_def)
    done


  lemma next_sib_2_reachable: "next_sib_2 slot p s = Some slot2  \<Longrightarrow> m' \<turnstile> (cte_map slot) \<leadsto>\<^sup>* (cte_map slot2)"
    apply (induct slot rule: next_sib_2_pinduct[where s=s and p=p])
    apply (cut_tac slot=slot and s=s and p=p in next_sib_2.psimps[OF next_sib_2_termination], (simp add: assms')+)
    apply (fold m_def t_def)
      apply (simp split: if_split_asm)
      apply (case_tac "next_slot slot t m")
       apply simp
      apply (simp split: if_split_asm)
       apply (rule r_into_rtrancl)
       apply (erule next_slot_mdb_next)
      apply (drule_tac x="a" in meta_spec)
      apply simp
      apply (rule trans)
       apply (rule r_into_rtrancl)
       apply (rule next_slot_mdb_next)
       apply (simp add: assms' valid_list_2)+
    done


lemma next_sib_reachable: "next_sib slot t m = Some slot2 \<Longrightarrow> m slot = Some p \<Longrightarrow>
                             m' \<turnstile> (cte_map slot) \<leadsto>\<^sup>* (cte_map slot2)"
    apply (rule next_sib_2_reachable)
    apply (insert assms')
    apply (simp add: t_def m_def)
    apply (subst next_sib_def2,simp+)
    done

lemma after_in_list_next_reachable:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "after_in_list (t p) slot = Some slot2 \<Longrightarrow> m' \<turnstile> (cte_map slot) \<leadsto>\<^sup>* (cte_map slot2)"
    apply (subgoal_tac "m slot = Some p")
   apply (rule next_sib_reachable)
    apply (simp add: next_sib_def)+
  apply (drule after_in_list_in_list')
  apply (insert valid_list_2)
  apply (simp add: valid_list_2_def)
    done

lemma sorted_lists:
   "psorted (t p)"
    apply (rule after_order_sorted)
     apply (rule after_in_list_next_reachable)
     apply simp
    apply (insert assms')
    apply (simp add: valid_list_def t_def del: split_paired_All)
    done

lemma finite_children:
notes split_paired_All[simp del]
shows
"finite {c. m c = Some p}"
  apply (insert assms')
  apply(subgoal_tac "{x. x \<in> descendants_of p (cdt s)} \<subseteq> {x. cte_wp_at (\<lambda>_. True) x s}")
   prefer 2
   apply(fastforce simp: descendants_of_cte_at)
  apply(drule finite_subset)
   apply(simp add: cte_wp_at_set_finite)
  apply(subgoal_tac "{c. m c = Some p} \<subseteq> {c. c \<in> descendants_of p (cdt s)}")
   apply (drule finite_subset)
    apply simp
   apply simp
  apply clarsimp
  apply (simp add: m_def child_descendant)
  done


lemma ex1_sorted_cdt: "\<exists>!xs. set xs = {c. m c = Some p} \<and>
           psorted xs \<and>
           distinct xs"
  apply (rule psorted_set[OF finite_children])
  apply (simp add: R_set_def)
  apply (intro impI conjI allI)
    apply (simp add: has_parent_cte_at[OF valid_mdb] m_def)
   apply (simp add: has_parent_cte_at[OF valid_mdb] m_def)

  apply (cut_tac s=s and s'=s' and x="(a,b)" in cdt_simple_rel, simp_all add: assms' rel)
  apply (simp add: m_def)
  apply (cut_tac s=s and s'=s' and x="(aa,ba)" in cdt_simple_rel, simp_all add: assms' rel)
  apply (rule_tac x="cte_map p" in exI)
  apply (simp add: m'_def)
  done

lemma sort_cdt_list_correct:
  "sort_cdt_list m m' = t"
  apply (rule ext)
  apply (simp add: sort_cdt_list_def)
  apply (rule the1_equality)
   apply (rule ex1_sorted_cdt)
  apply (simp add: sorted_lists)
  apply (insert assms')
  apply (simp add: valid_list_def t_def m_def del: split_paired_All)
  done

end

context begin interpretation Arch . (*FIXME: arch_split*)

definition absCDTList where
"absCDTList cnp h \<equiv> sort_cdt_list (absCDT cnp h) h"

lemma no_loops_sym_eq: "no_loops m \<Longrightarrow> m \<turnstile> a \<leadsto>\<^sup>* b \<Longrightarrow> m \<turnstile> b \<leadsto>\<^sup>* a \<Longrightarrow> a = b"
  apply (rule ccontr)
  apply (subgoal_tac "m \<turnstile> a \<leadsto>\<^sup>+ a")
   apply (simp add: no_loops_def)
  apply (simp add: rtrancl_eq_or_trancl)
  done

lemma mdb_next_single_valued: "single_valued (mdb_next_rel m)"
  apply (simp add: single_valued_def mdb_next_rel_def)
  done

lemma substring_next: "m \<turnstile> a \<leadsto>\<^sup>* b \<Longrightarrow> m \<turnstile> a \<leadsto>\<^sup>* c \<Longrightarrow> m \<turnstile> b \<leadsto>\<^sup>* c \<or> m \<turnstile> c \<leadsto>\<^sup>* b"
  apply (rule single_valued_confluent)
  apply (rule mdb_next_single_valued)
  apply simp+
  done

lemma ancestor_comparable: "\<lbrakk>m \<turnstile> a \<rightarrow> x; m \<turnstile> a \<rightarrow> y\<rbrakk> \<Longrightarrow> m \<turnstile> x \<leadsto>\<^sup>* y \<or> m \<turnstile> y \<leadsto>\<^sup>* x"
  apply (rule substring_next)
  apply (erule subtree_mdb_next[THEN trancl_into_rtrancl])+
  done

lemma valid_mdb'_no_loops: "valid_mdb' s \<Longrightarrow> no_loops (ctes_of s)"
  apply (rule mdb_chain_0_no_loops)
  apply (simp add: valid_mdb'_def valid_mdb_ctes_def)+
  done


lemma absCDTList_correct:
notes split_paired_All[simp del] split_paired_Ex[simp del]
assumes valid_mdb:  "valid_mdb s"
assumes valid_mdb': "valid_mdb' s'"
assumes valid_list: "valid_list s"
assumes valid_objs: "valid_objs s"
assumes pspace_aligned: "pspace_aligned s"
assumes pspace_aligned': "pspace_aligned' s'"
assumes pspace_distinct: "pspace_distinct s"
assumes pspace_distinct': "pspace_distinct' s'"
assumes rel:  "(s,s') \<in> state_relation"
shows
  "absCDTList (cteMap (gsCNodes s')) (ctes_of s') = cdt_list s"
  apply (simp add: absCDTList_def)
  apply (subst absCDT_correct[where s=s])
         apply (simp add: assms)+
  apply (rule partial_sort_cdt.sort_cdt_list_correct[where s'=s'])
  apply (simp add: partial_sort_cdt_def)
  apply (rule context_conjI')
   apply unfold_locales
             apply (simp add: assms)+
    apply (simp add: partial_sort_cdt_axioms_def)
    apply (elim conjE exE)
    apply (rule ancestor_comparable,assumption+)
   apply (elim conjE)
   apply (rule cte_map_inj_eq)
        apply (rule no_loops_sym_eq[where m="ctes_of s'"])
          apply (rule valid_mdb'_no_loops[OF valid_mdb'])
         apply (simp add: assms)+
  done

definition
  "absInterruptIRQNode is' \<equiv> \<lambda>irq.
   case is' of InterruptState node irqs' \<Rightarrow>
   node + (ucast irq << cte_level_bits)"

definition
  "irq_state_map s \<equiv> case s of
     irq_state.IRQInactive \<Rightarrow> irqstate.IRQInactive
   | irq_state.IRQSignal \<Rightarrow> irqstate.IRQSignal
   | irq_state.IRQTimer \<Rightarrow> irqstate.IRQTimer
   | irq_state.IRQReserved \<Rightarrow> irqstate.IRQReserved"

definition
  "IRQStateMap s \<equiv> case s of
     irqstate.IRQInactive \<Rightarrow> irq_state.IRQInactive
   | irqstate.IRQSignal \<Rightarrow> irq_state.IRQSignal
   | irqstate.IRQTimer \<Rightarrow> irq_state.IRQTimer
   | irqstate.IRQReserved \<Rightarrow> irq_state.IRQReserved"

definition
  "absInterruptStates is' \<equiv>
   case is' of InterruptState node m \<Rightarrow>
 IRQStateMap \<circ> m"

lemma absInterruptIRQNode_correct:
  "interrupt_state_relation (interrupt_irq_node s) (interrupt_states s)
      (ksInterruptState s') \<Longrightarrow>
   absInterruptIRQNode (ksInterruptState s') = interrupt_irq_node s"
   by (rule ext) (clarsimp simp add: absInterruptIRQNode_def
                                     interrupt_state_relation_def)

lemma absInterruptStates_correct:
  "interrupt_state_relation (interrupt_irq_node s) (interrupt_states s)
      (ksInterruptState s') \<Longrightarrow>
   absInterruptStates (ksInterruptState s') = interrupt_states s"
apply (rule ext)
apply (clarsimp simp add: absInterruptStates_def IRQStateMap_def
         interrupt_state_relation_def irq_state_relation_def)
apply (erule_tac x=x in allE)+
apply (clarsimp split: irq_state.splits irqstate.splits)
done

definition
  "absArchState s' \<equiv>
   case s' of ARMKernelState asid_tbl hwat anext am gpd gpts kvspace \<Rightarrow>
     \<lparr>arm_asid_table = asid_tbl \<circ> ucast,
      arm_hwasid_table = hwat, arm_next_asid = anext,
      arm_asid_map = am, arm_global_pd = gpd, arm_global_pts = gpts,
      arm_kernel_vspace = kvspace\<rparr>"

lemma absArchState_correct:
assumes rel:
  "(s,s') \<in> state_relation"
shows
  "absArchState (ksArchState s') = arch_state s"
apply (subgoal_tac "(arch_state s, ksArchState s') \<in> arch_state_relation")
 prefer 2
 using rel
 apply (simp add: state_relation_def)
apply (clarsimp simp add: arch_state_relation_def)
by (clarsimp simp add: absArchState_def
             split: ARM_H.kernel_state.splits)

definition absSchedulerAction where
  "absSchedulerAction action \<equiv>
    case action of ResumeCurrentThread \<Rightarrow> resume_cur_thread
                 | SwitchToThread t \<Rightarrow> switch_thread t
                 | ChooseNewThread \<Rightarrow> choose_new_thread"

lemma absSchedulerAction_correct:
  assumes act_rel: "sched_act_relation action action'"
  shows " absSchedulerAction action' = action"
  using act_rel
  by (cases action, simp_all add: absSchedulerAction_def)

definition
  "absExst s \<equiv>
     \<lparr>work_units_completed_internal = ksWorkUnitsCompleted s,
      cdt_list_internal = absCDTList (cteMap (gsCNodes s)) (ctes_of s)\<rparr>"

lemma absExst_correct:
  assumes invs: "einvs s" and invs': "invs' s'"
  assumes rel: "(s, s') \<in> state_relation"
  shows "absExst s' = exst s"
  apply (rule det_ext.equality)
      using rel invs invs'
      apply (simp_all add: absExst_def absSchedulerAction_correct
                           absCDTList_correct[THEN fun_cong] state_relation_def invs_def valid_state_def
                           ready_queues_relation_def invs'_def valid_state'_def
                           valid_pspace_def valid_sched_def valid_pspace'_def curry_def fun_eq_iff)
  done


definition
  "absKState s \<equiv>
   \<lparr>kheap = absHeap (gsUserPages s) (gsCNodes s) (ksPSpace s),
    cdt = absCDT (cteMap (gsCNodes s)) (ctes_of s),
    is_original_cap = absIsOriginalCap (cteMap (gsCNodes s)) (ksPSpace s),
    cur_thread = ksCurThread s, idle_thread = ksIdleThread s,
    consumed_time = ksConsumedTime s,
    cur_time = ksCurTime s,
    cur_sc = ksCurSc s,
    reprogram_timer = ksReprogramTimer s,
    scheduler_action = absSchedulerAction (ksSchedulerAction s),
    domain_list = ksDomSchedule s,
    domain_index = ksDomScheduleIdx s,
    cur_domain = ksCurDomain s,
    domain_time = ksDomainTime s,
    ready_queues = curry (ksReadyQueues s),
    release_queue = ksReleaseQueue s,
    machine_state = observable_memory (ksMachineState s) (user_mem' s),
    interrupt_irq_node = absInterruptIRQNode (ksInterruptState s),
    interrupt_states = absInterruptStates (ksInterruptState s),
    arch_state = absArchState (ksArchState s),
    exst = absExst s\<rparr>"

(* TODO: move *)
lemma invs_valid_ioc[elim!]: "invs s \<Longrightarrow> valid_ioc s"
  by (clarsimp simp add: invs_def valid_state_def)



definition
  checkActiveIRQ :: "(kernel_state, bool) nondet_monad"
  where
  "checkActiveIRQ \<equiv>
   do irq \<leftarrow> doMachineOp (getActiveIRQ False);
      return (irq \<noteq> None)
   od"

definition
  check_active_irq_H :: "((user_context \<times> kernel_state) \<times> bool \<times> (user_context \<times> kernel_state)) set"
  where
  "check_active_irq_H \<equiv> {((tc, s), irq, (tc, s')). (irq, s') \<in> fst (checkActiveIRQ s)}"

definition
  doUserOp :: "user_transition \<Rightarrow> user_context \<Rightarrow>
               (kernel_state, event option \<times> user_context) nondet_monad"
  where
  "doUserOp uop tc \<equiv>
   do t \<leftarrow> getCurThread;
      trans \<leftarrow> gets (ptable_lift t \<circ> absKState);
      perms \<leftarrow> gets (ptable_rights t \<circ> absKState);

      um \<leftarrow> gets (\<lambda>s. user_mem' s \<circ> ptrFromPAddr);
      dm \<leftarrow> gets (\<lambda>s. device_mem' s \<circ> ptrFromPAddr);

      ds \<leftarrow> gets (device_state \<circ> ksMachineState);
      assert (dom (um \<circ> addrFromPPtr) \<subseteq> - dom ds);
      assert (dom (dm \<circ> addrFromPPtr) \<subseteq> dom ds);

      (e, tc',um',ds') \<leftarrow> select (fst (uop t (restrict_map trans {pa. perms pa \<noteq> {}}) perms
                   (tc, restrict_map um
                        {pa. \<exists>va. trans va = Some pa \<and> AllowRead \<in> perms va}
                       ,(ds \<circ> ptrFromPAddr) |`  {pa. \<exists>va. trans va = Some pa \<and> AllowRead \<in> perms va} )
                       ));
      doMachineOp (user_memory_update
                       ((um' |` {pa. \<exists>va. trans va = Some pa \<and> AllowWrite \<in> perms va}
                      \<circ> addrFromPPtr) |` (- dom ds)));
      doMachineOp (device_memory_update
                       ((ds' |` {pa. \<exists>va. trans va = Some pa \<and> AllowWrite \<in> perms va}
                      \<circ> addrFromPPtr )|` (dom ds)));
      return (e, tc')
   od"

definition
  do_user_op_H
    :: "user_transition \<Rightarrow>
        ((user_context \<times> kernel_state) \<times> (event option \<times> user_context \<times> kernel_state)) set"
  where
  "do_user_op_H uop \<equiv> monad_to_transition (doUserOp uop)"

definition
  "kernelEntry e tc \<equiv> do
    t \<leftarrow> getCurThread;
    threadSet (\<lambda>tcb. tcb \<lparr> tcbArch := atcbContextSet tc (tcbArch tcb) \<rparr>) t;
    callKernel e;
    t' \<leftarrow> getCurThread;
    threadGet (atcbContextGet o tcbArch) t'
  od"

definition
  kernel_call_H
    :: "event \<Rightarrow> ((user_context \<times> kernel_state) \<times> mode \<times>
                  (user_context \<times> kernel_state)) set"
  where
  "kernel_call_H e \<equiv>
      {(s, m, s'). s' \<in> fst (split (kernelEntry e) s) \<and>
                   m = (if ct_running' (snd s') then UserMode else IdleMode)}"

definition
  ADT_H :: "user_transition \<Rightarrow>
            (kernel_state global_state, det_ext observable, unit) data_type"

  where
  "ADT_H uop \<equiv>
   \<lparr>Init = \<lambda>s. Init_H,
    Fin = \<lambda>((tc,s),m,e). ((tc, absKState s),m,e),
    Step = (\<lambda>u. global_automaton check_active_irq_H (do_user_op_H uop) kernel_call_H)\<rparr>"

end

end
