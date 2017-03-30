(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* Wellformedness of caps, kernel objects, states on the C level
*)

theory Wellformed_C
imports
  "../../../lib/CTranslationNICTA"
  CLevityCatch
  "../../../spec/cspec/Substitute"
begin

context begin interpretation Arch . (*FIXME: arch_split*)

abbreviation
  cte_Ptr :: "word32 \<Rightarrow> cte_C ptr" where "cte_Ptr == Ptr"
abbreviation
  mdb_Ptr :: "word32 \<Rightarrow> mdb_node_C ptr" where "mdb_Ptr == Ptr"
abbreviation
  cap_Ptr :: "word32 \<Rightarrow> cap_C ptr" where "cap_Ptr == Ptr"
abbreviation
  tcb_Ptr :: "word32 \<Rightarrow> tcb_C ptr" where "tcb_Ptr == Ptr"
abbreviation
  ep_Ptr :: "word32 \<Rightarrow> endpoint_C ptr" where "ep_Ptr == Ptr"
abbreviation
  ntfn_Ptr :: "word32 \<Rightarrow> notification_C ptr" where "ntfn_Ptr == Ptr"
abbreviation
  ap_Ptr :: "word32 \<Rightarrow> asid_pool_C ptr" where "ap_Ptr == Ptr"
abbreviation
  pte_Ptr :: "word32 \<Rightarrow> pte_C ptr" where "pte_Ptr == Ptr"
abbreviation
  pde_Ptr :: "word32 \<Rightarrow> pde_C ptr" where "pde_Ptr == Ptr"

lemma halt_spec:
  "Gamma \<turnstile> {} Call halt_'proc {}"
  apply (rule hoare_complete)
  apply (simp add: HoarePartialDef.valid_def)
  done

definition
  isUntypedCap_C :: "cap_CL \<Rightarrow> bool" where
  "isUntypedCap_C c \<equiv>
   case c of
   Cap_untyped_cap q \<Rightarrow> True
   | _ \<Rightarrow> False"

definition
  isNullCap_C :: "cap_CL \<Rightarrow> bool" where
  "isNullCap_C c \<equiv>
  case c of
   Cap_null_cap \<Rightarrow> True
   | _ \<Rightarrow> False"

definition
  isEndpointCap_C :: "cap_CL \<Rightarrow> bool" where
 "isEndpointCap_C v \<equiv> case v of
  Cap_endpoint_cap ec \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  isCNodeCap_C :: "cap_CL \<Rightarrow> bool" where
  "isCNodeCap_C c \<equiv> case c of
   Cap_cnode_cap a \<Rightarrow> True
   | _ \<Rightarrow> False"


definition
  isThreadCap_C :: "cap_CL \<Rightarrow> bool" where
  "isThreadCap_C c \<equiv> case c of
   Cap_thread_cap a \<Rightarrow> True
   | _ \<Rightarrow> False"

definition
  isIRQControlCap_C :: "cap_CL \<Rightarrow> bool" where
  "isIRQControlCap_C c \<equiv> case c of
   Cap_irq_control_cap \<Rightarrow> True
   | _ \<Rightarrow> False"

definition
  isIRQHandlerCap_C :: "cap_CL \<Rightarrow> bool" where
  "isIRQHandlerCap_C c \<equiv> case c of
   Cap_irq_handler_cap a \<Rightarrow> True
   | _ \<Rightarrow> False"

definition
  isNotificationCap_C :: "cap_CL \<Rightarrow> bool" where
 "isNotificationCap_C v \<equiv> case v of
  Cap_notification_cap aec \<Rightarrow> True
  | _ \<Rightarrow> False"

definition
  ep_at_C' :: "word32 \<Rightarrow> heap_raw_state \<Rightarrow> bool"
where
  "ep_at_C' p h \<equiv> Ptr p \<in> dom (clift h :: endpoint_C typ_heap)" -- "endpoint_lift is total"

definition
  ntfn_at_C' :: "word32 \<Rightarrow> heap_raw_state \<Rightarrow> bool"
  where -- "notification_lift is total"
  "ntfn_at_C' p h \<equiv> Ptr p \<in> dom (clift h :: notification_C typ_heap)"

definition
  tcb_at_C' :: "word32 \<Rightarrow> heap_raw_state \<Rightarrow> bool"
  where
  "tcb_at_C' p h \<equiv> Ptr p \<in> dom (clift h :: tcb_C typ_heap)"

definition
  cte_at_C' :: "word32 \<Rightarrow> heap_raw_state \<Rightarrow> bool"
  where
  "cte_at_C' p h \<equiv> Ptr p \<in> dom (clift h :: cte_C typ_heap)"

definition
  ctcb_offset :: word32
  where
  "ctcb_offset \<equiv> 2 ^ 8"

definition
  ctcb_ptr_to_tcb_ptr :: "tcb_C ptr \<Rightarrow> word32"
  where
  "ctcb_ptr_to_tcb_ptr p \<equiv> ptr_val p - ctcb_offset"

definition
  tcb_ptr_to_ctcb_ptr :: "word32 \<Rightarrow> tcb_C ptr"
  where
  "tcb_ptr_to_ctcb_ptr p \<equiv> Ptr (p + ctcb_offset)"

primrec
  tcb_queue_relation :: "(tcb_C \<Rightarrow> tcb_C ptr) \<Rightarrow> (tcb_C \<Rightarrow> tcb_C ptr) \<Rightarrow>
                         (tcb_C ptr \<Rightarrow> tcb_C option) \<Rightarrow> word32 list \<Rightarrow>
                         tcb_C ptr \<Rightarrow> tcb_C ptr \<Rightarrow> bool"
where
  "tcb_queue_relation getNext getPrev hp [] qprev qhead = (qhead = NULL)"
| "tcb_queue_relation getNext getPrev hp (x#xs) qprev qhead =
     (qhead = tcb_ptr_to_ctcb_ptr x \<and>
      (\<exists>tcb. (hp qhead = Some tcb \<and> getPrev tcb = qprev \<and> tcb_queue_relation getNext getPrev hp xs qhead (getNext tcb))))"

abbreviation
  "ep_queue_relation \<equiv> tcb_queue_relation tcbEPNext_C tcbEPPrev_C"

abbreviation
  "sched_queue_relation \<equiv> tcb_queue_relation tcbSchedNext_C tcbSchedPrev_C"


definition
wordSizeCase :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"wordSizeCase a b \<equiv> (if bitSize (undefined::word32) = 32
        then  a
        else if bitSize (undefined::word32) = 64
        then  b
        else  error []
        )"


primrec
  capBits_C :: "cap_CL \<Rightarrow> nat"
where
  "capBits_C Cap_null_cap = 0"
| "capBits_C (Cap_untyped_cap uc) = unat (capBlockSize_CL uc)" 
| "capBits_C (Cap_endpoint_cap ec) = wordSizeCase 4 5"
| "capBits_C (Cap_notification_cap aec) = wordSizeCase 4 5"
| "capBits_C (Cap_cnode_cap cnc) =  wordSizeCase 4 5"
| "capBits_C (Cap_thread_cap tc) = 10"
| "capBits_C (Cap_zombie_cap zc) =  (wordSizeCase 4 5)" 


definition
capUntypedPtr_C :: "cap_CL \<Rightarrow> word32" where
  "capUntypedPtr_C cap \<equiv> case cap of
 (Cap_untyped_cap uc) \<Rightarrow> (capBlockSize_CL uc)
 |  Cap_endpoint_cap ep \<Rightarrow> (capEPPtr_CL ep)
 |  Cap_notification_cap ntfn \<Rightarrow> (capNtfnPtr_CL ntfn)
 |  Cap_cnode_cap ccap \<Rightarrow> (capCNodePtr_CL ccap)
 |  Cap_reply_cap rc \<Rightarrow>  (cap_reply_cap_CL.capTCBPtr_CL rc)
 |  Cap_thread_cap tc \<Rightarrow>  (cap_thread_cap_CL.capTCBPtr_CL tc)
 |  Cap_small_frame_cap sfc \<Rightarrow>  (cap_small_frame_cap_CL.capFBasePtr_CL sfc)
 |  Cap_frame_cap fc \<Rightarrow>  (cap_frame_cap_CL.capFBasePtr_CL fc)
 |  Cap_page_table_cap ptc \<Rightarrow>  (capPTBasePtr_CL ptc)
 |  Cap_page_directory_cap pdc \<Rightarrow>  (capPDBasePtr_CL pdc)
 | _ \<Rightarrow> error []"

definition ZombieTCB_C_def:
"ZombieTCB_C \<equiv> bit 5"

definition
  isZombieTCB_C :: "word32 \<Rightarrow> bool" where
 "isZombieTCB_C v \<equiv> v = ZombieTCB_C"

definition
vmrights_to_H :: "word32 \<Rightarrow> vmrights" where
"vmrights_to_H c \<equiv>
  if c = scast Kernel_C.VMNoAccess then VMNoAccess
  else if c = scast Kernel_C.VMKernelOnly then VMKernelOnly
  else if c = scast Kernel_C.VMReadOnly then VMReadOnly
  else VMReadWrite"

(* Force clarity over name collisions *)
abbreviation
  ARMSmallPage :: "vmpage_size" where
 "ARMSmallPage == ARM.ARMSmallPage"
abbreviation
  ARMLargePage :: "vmpage_size" where
 "ARMLargePage == ARM.ARMLargePage"
abbreviation
  ARMSection :: "vmpage_size" where
 "ARMSection == ARM.ARMSection"
abbreviation
  ARMSuperSection :: "vmpage_size" where
 "ARMSuperSection == ARM.ARMSuperSection"

-- "ARMSmallFrame is treated in a separate cap in C,
    so needs special treatment in ccap_relation"
definition
framesize_to_H:: "word32 \<Rightarrow> vmpage_size" where
"framesize_to_H c \<equiv>
  if c = scast Kernel_C.ARMLargePage then ARMLargePage
  else if c = scast Kernel_C.ARMSection then ARMSection
  else ARMSuperSection"

-- "Use this for results of generic_frame_cap_get_capFSize"
definition
gen_framesize_to_H:: "word32 \<Rightarrow> vmpage_size" where
"gen_framesize_to_H c \<equiv>
  if c = scast Kernel_C.ARMSmallPage then ARMSmallPage
  else if c = scast Kernel_C.ARMLargePage then ARMLargePage
  else if c = scast Kernel_C.ARMSection then ARMSection
  else ARMSuperSection"

end

record cte_CL =
  cap_CL :: cap_CL
  cteMDBNode_CL :: mdb_node_CL

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  cte_lift :: "cte_C \<rightharpoonup> cte_CL"
  where
  "cte_lift c \<equiv> case cap_lift (cte_C.cap_C c) of
                     None \<Rightarrow> None
                   | Some cap \<Rightarrow> Some \<lparr> cap_CL = cap,
                                       cteMDBNode_CL = mdb_node_lift (cteMDBNode_C c) \<rparr>"

lemma to_bool_false [simp]: "\<not> to_bool false"
  by (simp add: to_bool_def false_def)

(* this is slightly weird, but the bitfield generator
   masks everything with the expected bit length.
   So we do that here too. *)
definition
  to_bool_bf :: "'a::len word \<Rightarrow> bool" where
  "to_bool_bf w \<equiv> (w && mask 1) = 1"

lemma to_bool_bf_mask1 [simp]:
  "to_bool_bf (mask (Suc 0))"
  by (simp add: mask_def to_bool_bf_def)

lemma to_bool_bf_0 [simp]: "\<not>to_bool_bf 0"
  by (simp add: to_bool_bf_def)

lemma to_bool_bf_1 [simp]: "to_bool_bf 1"
  by (simp add: to_bool_bf_def mask_def)

lemma to_bool_bf_false [simp]:
  "\<not>to_bool_bf false"
  by (simp add: false_def)

lemma to_bool_bf_true [simp]:
  "to_bool_bf true"
  by (simp add: true_def)

lemma to_bool_to_bool_bf:
  "w = false \<or> w = true \<Longrightarrow> to_bool_bf w = to_bool w"
  by (auto simp: false_def true_def to_bool_def to_bool_bf_def mask_def)

lemma to_bool_bf_mask_1 [simp]:
  "to_bool_bf (w && mask (Suc 0)) = to_bool_bf w"
  by (simp add: to_bool_bf_def)

lemma to_bool_bf_and [simp]:
  "to_bool_bf (a && b) = (to_bool_bf a \<and> to_bool_bf (b::word32))"
  apply (clarsimp simp: to_bool_bf_def)
  apply (rule iffI)
   apply (subst (asm) bang_eq)
   apply (simp add: word_size)
   apply (rule conjI)
    apply (rule word_eqI)
    apply (auto simp add: word_size)[1]
   apply (rule word_eqI)
   apply (auto simp add: word_size)[1]
  apply clarsimp
  apply (rule word_eqI)
  apply (subst (asm) bang_eq)+
  apply (auto simp add: word_size)[1]
  done

lemma to_bool_bf_to_bool_mask:
  "w && mask (Suc 0) = w \<Longrightarrow> to_bool_bf w = to_bool (w::word32)"
  apply (auto simp add: to_bool_bf_def to_bool_def mask_eq_iff_w2p word_size)
  apply (auto simp add: mask_def dest: word_less_cases)
  done

definition
  mdb_node_to_H :: "mdb_node_CL \<Rightarrow> mdbnode"
  where
  "mdb_node_to_H n \<equiv> MDB (mdbNext_CL n)
                         (mdbPrev_CL n)
                         (to_bool (mdbRevocable_CL n))
                         (to_bool (mdbFirstBadged_CL n))"


definition
cap_to_H :: "cap_CL \<Rightarrow> capability"
where
"cap_to_H c \<equiv>  case c of
 Cap_null_cap \<Rightarrow> NullCap
 | Cap_zombie_cap zc \<Rightarrow>  (if isZombieTCB_C(capZombieType_CL zc)
                         then
                               (Zombie ((capZombieID_CL zc) && ~~(mask(5)))
                                       (ZombieTCB)
                                       (unat ((capZombieID_CL zc) && mask(5))))
                         else let radix = unat (capZombieType_CL zc) in
                               (Zombie ((capZombieID_CL zc) && ~~(mask (radix+1)))
                                       (ZombieCNode radix)
                                       (unat ((capZombieID_CL zc) && mask(radix+1)))))
 | Cap_cnode_cap ccap \<Rightarrow>
    CNodeCap (capCNodePtr_CL ccap) (unat (capCNodeRadix_CL ccap))
             (capCNodeGuard_CL ccap)
             (unat (capCNodeGuardSize_CL ccap))
 | Cap_untyped_cap uc \<Rightarrow> UntypedCap (to_bool(capIsDevice_CL uc)) (capPtr_CL uc) (unat (capBlockSize_CL uc)) (unat (capFreeIndex_CL uc << 4))
 | Cap_endpoint_cap ec \<Rightarrow>
    EndpointCap (capEPPtr_CL ec) (capEPBadge_CL ec) (to_bool(capCanSend_CL ec)) (to_bool(capCanReceive_CL ec))
                (to_bool(capCanGrant_CL ec))
 | Cap_notification_cap ntfn \<Rightarrow>
    NotificationCap (capNtfnPtr_CL ntfn)(capNtfnBadge_CL ntfn)(to_bool(capNtfnCanSend_CL ntfn))
                     (to_bool(capNtfnCanReceive_CL ntfn))
 | Cap_reply_cap rc \<Rightarrow> ReplyCap (ctcb_ptr_to_tcb_ptr (Ptr (cap_reply_cap_CL.capTCBPtr_CL rc))) (to_bool (capReplyMaster_CL rc))
 | Cap_thread_cap tc \<Rightarrow>  ThreadCap(ctcb_ptr_to_tcb_ptr (Ptr (cap_thread_cap_CL.capTCBPtr_CL tc)))
 | Cap_irq_handler_cap ihc \<Rightarrow> IRQHandlerCap (ucast(capIRQ_CL ihc))
 | Cap_irq_control_cap \<Rightarrow> IRQControlCap
 | Cap_asid_control_cap \<Rightarrow> ArchObjectCap ASIDControlCap
 | Cap_asid_pool_cap apc \<Rightarrow> ArchObjectCap (ASIDPoolCap (capASIDPool_CL apc) (capASIDBase_CL apc))
 | Cap_small_frame_cap sfc \<Rightarrow> ArchObjectCap (PageCap (to_bool(cap_small_frame_cap_CL.capFIsDevice_CL sfc)) (cap_small_frame_cap_CL.capFBasePtr_CL sfc)
                                            (vmrights_to_H(cap_small_frame_cap_CL.capFVMRights_CL sfc)) (ARMSmallPage)
                                            (if cap_small_frame_cap_CL.capFMappedASIDHigh_CL sfc = 0
                                                \<and> cap_small_frame_cap_CL.capFMappedASIDLow_CL sfc = 0
                                             then None else
                                             Some( (((cap_small_frame_cap_CL.capFMappedASIDHigh_CL sfc)<<asidLowBits) +
                                             (cap_small_frame_cap_CL.capFMappedASIDLow_CL sfc)) ,
                                             cap_small_frame_cap_CL.capFMappedAddress_CL sfc)))
 | Cap_frame_cap fc \<Rightarrow> ArchObjectCap (PageCap (to_bool(capFIsDevice_CL fc)) (capFBasePtr_CL fc)
                                            (vmrights_to_H(capFVMRights_CL fc)) (framesize_to_H(capFSize_CL fc))
                                            (if capFMappedASIDHigh_CL fc = 0
                                               \<and> capFMappedASIDLow_CL fc = 0
                                             then None else
                                             Some( (((capFMappedASIDHigh_CL fc)<<asidLowBits) +
                                             (capFMappedASIDLow_CL fc)),capFMappedAddress_CL fc)))
 | Cap_page_table_cap ptc \<Rightarrow> ArchObjectCap (PageTableCap (capPTBasePtr_CL ptc)
                                          (if to_bool (capPTIsMapped_CL ptc)
                                           then Some( ((capPTMappedASID_CL ptc)),(capPTMappedAddress_CL ptc))
                                           else None))
 | Cap_page_directory_cap pdf \<Rightarrow> ArchObjectCap (PageDirectoryCap (capPDBasePtr_CL pdf)
                                          (if to_bool (capPDIsMapped_CL pdf)
                                           then Some (capPDMappedASID_CL pdf)
                                           else None))
 | Cap_domain_cap \<Rightarrow> DomainCap"

lemmas cap_to_H_simps = cap_to_H_def[split_simps cap_CL.split]

definition
  cte_to_H :: "cte_CL \<Rightarrow> cte"
  where
  "cte_to_H cte \<equiv> CTE (cap_to_H (cap_CL cte)) (mdb_node_to_H (cteMDBNode_CL cte))"



definition
cl_valid_cap :: "cap_CL \<Rightarrow> bool"
where
"cl_valid_cap c \<equiv>
   case c of
     Cap_frame_cap fc \<Rightarrow> ((capFSize_CL fc) \<noteq>  scast Kernel_C.ARMSmallPage)
     | Cap_irq_handler_cap fc \<Rightarrow> ((capIRQ_CL fc) && mask 10 = capIRQ_CL fc)
     | x \<Rightarrow> True"

definition
c_valid_cap :: "cap_C \<Rightarrow> bool"
where
"c_valid_cap c \<equiv> case_option True cl_valid_cap (cap_lift c)"


definition
cl_valid_cte :: "cte_CL \<Rightarrow> bool"
where
"cl_valid_cte c \<equiv>  cl_valid_cap (cap_CL c)"


definition
c_valid_cte :: "cte_C \<Rightarrow> bool"
where
"c_valid_cte c \<equiv>  c_valid_cap (cte_C.cap_C c)"

lemma  c_valid_cap_simps [simp]:
  "cap_get_tag c = scast cap_small_frame_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_thread_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_notification_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_endpoint_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_cnode_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_page_directory_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_asid_control_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_irq_control_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_page_table_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_asid_pool_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_untyped_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_zombie_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_reply_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_null_cap \<Longrightarrow> c_valid_cap c"
  unfolding c_valid_cap_def  cap_lift_def cap_tag_defs
  by (simp add: cl_valid_cap_def)+

lemma ptr_val_tcb_ptr_mask2:
  "is_aligned thread 9
      \<Longrightarrow> ptr_val (tcb_ptr_to_ctcb_ptr thread) && (~~ mask 9)
                  = thread"
  apply (clarsimp simp: tcb_ptr_to_ctcb_ptr_def projectKOs)
  apply (simp add: is_aligned_add_helper ctcb_offset_def objBits_simps)
  done

lemma maxDom_to_H:
  "ucast maxDom = maxDomain"
  by (simp add: maxDomain_def maxDom_def numDomains_def)

lemma maxPrio_to_H:
  "ucast seL4_MaxPrio = maxPriority"
  by (simp add: maxPriority_def seL4_MaxPrio_def numPriorities_def)

abbreviation(input)
  NotificationObject :: sword32
where
  "NotificationObject == seL4_NotificationObject"

abbreviation(input)
  CapTableObject :: sword32
where
  "CapTableObject == seL4_CapTableObject"

abbreviation(input)
  EndpointObject :: sword32
where
  "EndpointObject == seL4_EndpointObject"

abbreviation(input)
  LargePageObject :: sword32
where
  "LargePageObject == seL4_ARM_LargePageObject"

abbreviation(input)
  PageDirectoryObject :: sword32
where
  "PageDirectoryObject == seL4_ARM_PageDirectoryObject"

abbreviation(input)
  PageTableObject :: sword32
where
  "PageTableObject == seL4_ARM_PageTableObject"

abbreviation(input)
  SectionObject :: sword32
where
  "SectionObject == seL4_ARM_SectionObject"

abbreviation(input)
  SmallPageObject :: sword32
where
  "SmallPageObject == seL4_ARM_SmallPageObject"

abbreviation(input)
  SuperSectionObject :: sword32
where
  "SuperSectionObject == seL4_ARM_SuperSectionObject"

abbreviation(input)
  TCBObject :: sword32
where
  "TCBObject == seL4_TCBObject"

abbreviation(input)
  UntypedObject :: sword32
where
  "UntypedObject == seL4_UntypedObject"

abbreviation(input)
  maxPrio :: sword32
where
  "maxPrio == seL4_MaxPrio"

abbreviation(input)
  minPrio :: sword32
where
  "minPrio == seL4_MinPrio"

abbreviation(input)
  nAPIObjects :: sword32
where
  "nAPIObjects == seL4_NonArchObjectTypeCount"

abbreviation(input)
  nObjects :: sword32
where
  "nObjects == seL4_ObjectTypeCount"

abbreviation(input)
  prioInvalid :: sword32
where
  "prioInvalid == seL4_InvalidPrio"

end

end
