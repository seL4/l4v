(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Wellformedness of caps, kernel objects, states on the C level
*)

theory Wellformed_C
imports
  "CLib.CTranslationNICTA"
  CLevityCatch
  "CSpec.Substitute"
begin

context begin interpretation Arch . (*FIXME: arch-split*)

abbreviation
  cte_Ptr :: "word64 \<Rightarrow> cte_C ptr" where "cte_Ptr == Ptr"
abbreviation
  mdb_Ptr :: "word64 \<Rightarrow> mdb_node_C ptr" where "mdb_Ptr == Ptr"
abbreviation
  cap_Ptr :: "word64 \<Rightarrow> cap_C ptr" where "cap_Ptr == Ptr"
abbreviation
  tcb_Ptr :: "word64 \<Rightarrow> tcb_C ptr" where "tcb_Ptr == Ptr"
abbreviation
  atcb_Ptr :: "word64 \<Rightarrow> arch_tcb_C ptr" where "atcb_Ptr == Ptr"
abbreviation
  ep_Ptr :: "word64 \<Rightarrow> endpoint_C ptr" where "ep_Ptr == Ptr"
abbreviation
  ntfn_Ptr :: "word64 \<Rightarrow> notification_C ptr" where "ntfn_Ptr == Ptr"
abbreviation
  ap_Ptr :: "word64 \<Rightarrow> asid_pool_C ptr" where "ap_Ptr == Ptr"
abbreviation
  pte_Ptr :: "word64 \<Rightarrow> pte_C ptr" where "pte_Ptr == Ptr"
abbreviation
  pde_Ptr :: "word64 \<Rightarrow> pde_C ptr" where "pde_Ptr == Ptr"
abbreviation
  pdpte_Ptr :: "word64 \<Rightarrow> pdpte_C ptr" where "pdpte_Ptr == Ptr"
abbreviation
  pml4e_Ptr :: "word64 \<Rightarrow> pml4e_C ptr" where "pml4e_Ptr == Ptr"
abbreviation
  pml4_Ptr :: "machine_word \<Rightarrow> (pml4e_C[512]) ptr" where "pml4_Ptr == Ptr"
abbreviation
  pdpt_Ptr :: "machine_word \<Rightarrow> (pdpte_C[512]) ptr" where "pdpt_Ptr == Ptr"
abbreviation
  pd_Ptr :: "machine_word \<Rightarrow> (pde_C[512]) ptr" where "pd_Ptr == Ptr"
abbreviation
  pt_Ptr :: "machine_word \<Rightarrow> (pte_C[512]) ptr" where "pt_Ptr == Ptr"

(* 1024 = number of entries in ioport table
        = 2^16 (total number of ioports) / word_bits *)
type_synonym ioport_table_C = "machine_word[1024]"

type_synonym tcb_cnode_array = "cte_C[5]"
type_synonym fpu_bytes_array = "word8[fpu_bytes]"
type_synonym registers_array = "machine_word[24]"

abbreviation "user_context_Ptr \<equiv> Ptr :: addr \<Rightarrow> user_context_C ptr"
abbreviation "machine_word_Ptr \<equiv> Ptr :: addr \<Rightarrow> machine_word ptr"
abbreviation "tcb_cnode_Ptr \<equiv> Ptr :: addr \<Rightarrow> tcb_cnode_array ptr"
abbreviation "fpu_state_Ptr \<equiv> Ptr :: addr \<Rightarrow> user_fpu_state_C ptr"
abbreviation "fpu_bytes_Ptr \<equiv> Ptr :: addr \<Rightarrow> fpu_bytes_array ptr"
abbreviation "registers_Ptr \<equiv> Ptr :: addr \<Rightarrow> registers_array ptr"
abbreviation "ioport_table_Ptr \<equiv> Ptr :: addr \<Rightarrow> ioport_table_C ptr"

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
  ep_at_C' :: "word64 \<Rightarrow> heap_raw_state \<Rightarrow> bool"
where
  "ep_at_C' p h \<equiv> Ptr p \<in> dom (clift h :: endpoint_C typ_heap)" \<comment> \<open>endpoint_lift is total\<close>

definition
  ntfn_at_C' :: "word64 \<Rightarrow> heap_raw_state \<Rightarrow> bool"
  where \<comment> \<open>notification_lift is total\<close>
  "ntfn_at_C' p h \<equiv> Ptr p \<in> dom (clift h :: notification_C typ_heap)"

definition
  tcb_at_C' :: "word64 \<Rightarrow> heap_raw_state \<Rightarrow> bool"
  where
  "tcb_at_C' p h \<equiv> Ptr p \<in> dom (clift h :: tcb_C typ_heap)"

definition
  cte_at_C' :: "word64 \<Rightarrow> heap_raw_state \<Rightarrow> bool"
  where
  "cte_at_C' p h \<equiv> Ptr p \<in> dom (clift h :: cte_C typ_heap)"

definition
  ctcb_ptr_to_tcb_ptr :: "tcb_C ptr \<Rightarrow> word64"
  where
  "ctcb_ptr_to_tcb_ptr p \<equiv> ptr_val p - ctcb_offset"

definition
  tcb_ptr_to_ctcb_ptr :: "word64 \<Rightarrow> tcb_C ptr"
  where
  "tcb_ptr_to_ctcb_ptr p \<equiv> Ptr (p + ctcb_offset)"

primrec
  tcb_queue_relation :: "(tcb_C \<Rightarrow> tcb_C ptr) \<Rightarrow> (tcb_C \<Rightarrow> tcb_C ptr) \<Rightarrow>
                         (tcb_C ptr \<Rightarrow> tcb_C option) \<Rightarrow> word64 list \<Rightarrow>
                         tcb_C ptr \<Rightarrow> tcb_C ptr \<Rightarrow> bool"
where
  "tcb_queue_relation getNext getPrev hp [] qprev qhead = (qhead = NULL)"
| "tcb_queue_relation getNext getPrev hp (x#xs) qprev qhead =
     (qhead = tcb_ptr_to_ctcb_ptr x \<and>
      (\<exists>tcb. (hp qhead = Some tcb \<and> getPrev tcb = qprev \<and> tcb_queue_relation getNext getPrev hp xs qhead (getNext tcb))))"

abbreviation
  "ep_queue_relation \<equiv> tcb_queue_relation tcbEPNext_C tcbEPPrev_C"

definition
wordSizeCase :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"wordSizeCase a b \<equiv> (if bitSize (undefined::machine_word) = 32
        then  a
        else if bitSize (undefined::machine_word) = 64
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
capUntypedPtr_C :: "cap_CL \<Rightarrow> word64" where
  "capUntypedPtr_C cap \<equiv> case cap of
 (Cap_untyped_cap uc) \<Rightarrow> (capBlockSize_CL uc)
 |  Cap_endpoint_cap ep \<Rightarrow> (capEPPtr_CL ep)
 |  Cap_notification_cap ntfn \<Rightarrow> (capNtfnPtr_CL ntfn)
 |  Cap_cnode_cap ccap \<Rightarrow> (capCNodePtr_CL ccap)
 |  Cap_reply_cap rc \<Rightarrow>  (cap_reply_cap_CL.capTCBPtr_CL rc)
 |  Cap_thread_cap tc \<Rightarrow>  (cap_thread_cap_CL.capTCBPtr_CL tc)
 |  Cap_frame_cap fc \<Rightarrow>  (cap_frame_cap_CL.capFBasePtr_CL fc)
 |  Cap_page_table_cap ptc \<Rightarrow>  (cap_page_table_cap_CL.capPTBasePtr_CL ptc)
 |  Cap_page_directory_cap pdc \<Rightarrow>  (cap_page_directory_cap_CL.capPDBasePtr_CL pdc)
 |  Cap_pdpt_cap pdptc \<Rightarrow> (cap_pdpt_cap_CL.capPDPTBasePtr_CL pdptc)
 |  Cap_pml4_cap pml4c \<Rightarrow> (cap_pml4_cap_CL.capPML4BasePtr_CL pml4c)
 | _ \<Rightarrow> error []"

definition ZombieTCB_C_def:
"ZombieTCB_C \<equiv> bit 6" (*wordRadix*)

definition
  isZombieTCB_C :: "word64 \<Rightarrow> bool" where
 "isZombieTCB_C v \<equiv> v = ZombieTCB_C"

definition
vmrights_to_H :: "word64 \<Rightarrow> vmrights" where
"vmrights_to_H c \<equiv>
  if c = scast Kernel_C.VMReadWrite then VMReadWrite
  else if c = scast Kernel_C.VMReadOnly then VMReadOnly
  else VMKernelOnly"

(* Force clarity over name collisions *)
abbreviation
  X64SmallPage :: "vmpage_size" where
 "X64SmallPage == X64.X64SmallPage"
abbreviation
  X64LargePage :: "vmpage_size" where
 "X64LargePage == X64.X64LargePage"
abbreviation
  X64HugePage :: "vmpage_size" where
 "X64HugePage == X64.X64HugePage"

definition
  framesize_to_H :: "machine_word \<Rightarrow> vmpage_size"
where
  "framesize_to_H c \<equiv>
    if c = scast Kernel_C.X86_SmallPage then X64SmallPage
    else if c = scast Kernel_C.X86_LargePage then X64LargePage
    else X64HugePage"

definition
  framesize_from_H :: "vmpage_size \<Rightarrow> machine_word"
where
  "framesize_from_H sz \<equiv>
    case sz of
         X64SmallPage \<Rightarrow> scast Kernel_C.X86_SmallPage
       | X64LargePage \<Rightarrow> scast Kernel_C.X86_LargePage
       | X64HugePage \<Rightarrow> scast Kernel_C.X64_HugePage"

lemma framesize_from_to_H:
  "framesize_to_H (framesize_from_H sz) = sz"
  by (simp add: framesize_to_H_def framesize_from_H_def
                Kernel_C.X86_SmallPage_def Kernel_C.X86_LargePage_def
                Kernel_C.X64_HugePage_def
           split: if_split vmpage_size.splits)

lemma framesize_from_H_eq:
  "(framesize_from_H sz = framesize_from_H sz') = (sz = sz')"
  by (cases sz; cases sz';
      simp add: framesize_from_H_def X86_SmallPage_def X86_LargePage_def X64_HugePage_def)

definition
  maptype_to_H :: "machine_word \<Rightarrow> vmmap_type"
where
  "maptype_to_H c \<equiv>
    if c = scast Kernel_C.X86_MappingNone then VMNoMap
    else VMVSpaceMap"

end

record cte_CL =
  cap_CL :: cap_CL
  cteMDBNode_CL :: mdb_node_CL

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  cte_lift :: "cte_C \<rightharpoonup> cte_CL"
  where
  "cte_lift c \<equiv> case cap_lift (cte_C.cap_C c) of
                     None \<Rightarrow> None
                   | Some cap \<Rightarrow> Some \<lparr> cap_CL = cap,
                                       cteMDBNode_CL = mdb_node_lift (cteMDBNode_C c) \<rparr>"

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
                (to_bool(capCanGrant_CL ec)) (to_bool(capCanGrantReply_CL ec))
 | Cap_notification_cap ntfn \<Rightarrow>
    NotificationCap (capNtfnPtr_CL ntfn)(capNtfnBadge_CL ntfn)(to_bool(capNtfnCanSend_CL ntfn))
                     (to_bool(capNtfnCanReceive_CL ntfn))
 | Cap_reply_cap rc \<Rightarrow> ReplyCap (ctcb_ptr_to_tcb_ptr (Ptr (cap_reply_cap_CL.capTCBPtr_CL rc)))
                               (to_bool (capReplyMaster_CL rc)) (to_bool (capReplyCanGrant_CL rc))
 | Cap_thread_cap tc \<Rightarrow>  ThreadCap(ctcb_ptr_to_tcb_ptr (Ptr (cap_thread_cap_CL.capTCBPtr_CL tc)))
 | Cap_irq_handler_cap ihc \<Rightarrow> IRQHandlerCap (ucast(capIRQ_CL ihc))
 | Cap_irq_control_cap \<Rightarrow> IRQControlCap
 | Cap_asid_control_cap \<Rightarrow> ArchObjectCap ASIDControlCap
 | Cap_asid_pool_cap apc \<Rightarrow> ArchObjectCap (ASIDPoolCap (capASIDPool_CL apc) (capASIDBase_CL apc))
 | Cap_frame_cap fc \<Rightarrow> ArchObjectCap (PageCap (capFBasePtr_CL fc)
                                            (vmrights_to_H(capFVMRights_CL fc))
                                            (maptype_to_H(capFMapType_CL fc)) (framesize_to_H(capFSize_CL fc))
                                            (to_bool(capFIsDevice_CL fc))
                                            (if capFMappedASID_CL fc = 0
                                             then None else
                                             Some(capFMappedASID_CL fc, capFMappedAddress_CL fc)))
 | Cap_page_table_cap ptc \<Rightarrow> ArchObjectCap (PageTableCap (cap_page_table_cap_CL.capPTBasePtr_CL ptc)
                                          (if to_bool (cap_page_table_cap_CL.capPTIsMapped_CL ptc)
                                           then Some( ((cap_page_table_cap_CL.capPTMappedASID_CL ptc)),(cap_page_table_cap_CL.capPTMappedAddress_CL ptc))
                                           else None))
 | Cap_page_directory_cap pdf \<Rightarrow> ArchObjectCap (PageDirectoryCap (cap_page_directory_cap_CL.capPDBasePtr_CL pdf)
                                          (if to_bool (cap_page_directory_cap_CL.capPDIsMapped_CL pdf)
                                           then Some (cap_page_directory_cap_CL.capPDMappedASID_CL pdf, cap_page_directory_cap_CL.capPDMappedAddress_CL pdf)
                                           else None))
 | Cap_pdpt_cap pdf \<Rightarrow> ArchObjectCap (PDPointerTableCap (cap_pdpt_cap_CL.capPDPTBasePtr_CL pdf)
                                          (if to_bool (cap_pdpt_cap_CL.capPDPTIsMapped_CL pdf)
                                           then Some (cap_pdpt_cap_CL.capPDPTMappedASID_CL pdf, cap_pdpt_cap_CL.capPDPTMappedAddress_CL pdf)
                                           else None))
 | Cap_pml4_cap pdf \<Rightarrow> ArchObjectCap (PML4Cap (cap_pml4_cap_CL.capPML4BasePtr_CL pdf)
                                          (if to_bool (cap_pml4_cap_CL.capPML4IsMapped_CL pdf)
                                           then Some (cap_pml4_cap_CL.capPML4MappedASID_CL pdf)
                                           else None))
 | Cap_domain_cap \<Rightarrow> DomainCap
 | Cap_io_port_control_cap \<Rightarrow> ArchObjectCap IOPortControlCap
 | Cap_io_port_cap ioc \<Rightarrow> ArchObjectCap (IOPortCap (ucast(capIOPortFirstPort_CL ioc)) (ucast(capIOPortLastPort_CL ioc)))"

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
     Cap_irq_handler_cap fc \<Rightarrow> ((capIRQ_CL fc) && mask 8 = capIRQ_CL fc)
   | Cap_frame_cap fc \<Rightarrow> capFSize_CL fc < 3 \<and> capFMapType_CL fc < 2 \<and> capFVMRights_CL fc < 4 \<and> capFVMRights_CL fc \<noteq> 0
   | Cap_pml4_cap pc \<Rightarrow> to_bool (capPML4IsMapped_CL pc) = (capPML4MappedASID_CL pc \<noteq> ucast asidInvalid)
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

(* all uninteresting cases can be deduced from the cap tag *)
lemma  c_valid_cap_simps [simp]:
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
  "cap_get_tag c = scast cap_pdpt_cap \<Longrightarrow> c_valid_cap c"
  "cap_get_tag c = scast cap_io_port_cap \<Longrightarrow> c_valid_cap c"
  unfolding c_valid_cap_def  cap_lift_def cap_tag_defs
  by (simp add: cl_valid_cap_def)+

lemma ptr_val_tcb_ptr_mask2:
  "is_aligned thread tcbBlockSizeBits
      \<Longrightarrow> ptr_val (tcb_ptr_to_ctcb_ptr thread) && (~~ mask tcbBlockSizeBits)
                  = thread"
  apply (clarsimp simp: tcb_ptr_to_ctcb_ptr_def projectKOs)
  apply (simp add: is_aligned_add_helper ctcb_offset_defs objBits_simps')
  done


section \<open>Domains\<close>

text \<open>
  seL4's build system allows configuration of the number of domains. This means the proofs have to
  work for any number of domains provided it fits into the hard limit of a 8-bit word.

  In the C code, we have the enumerated constant numDomains, one greater than maxDom. In the
  abstract specs, we have the corresponding Platform_Config.numDomains and maxDomain.

  To keep the proofs as general as possible, we avoid unfolding definitions of:
  maxDom, maxDomain, numDomains except in this theory where we need to establish basic properties.

  Unfortunately, array bounds checks coming from the C code use numerical values, meaning we might
  get 0x10 instead of the number of domains, or 0x1000 for numDomains * numPriorities. To solve
  these, the "explicit" lemmas expose direct numbers. They are more risky to deploy, as one could
  prove that 0x5 is less than the number of domains when that's the case, and then the proof will
  break upon reconfiguration.
\<close>

text \<open>The @{text num_domains} enumerated type and constant represent the number of domains.\<close>

value_type num_domains = "numDomains"

context includes no_less_1_simps begin

(* The proofs expect the minimum priority and minimum domain to be zero.
   Note that minDom is unused in the C code. *)
lemma min_prio_dom_sanity:
  "seL4_MinPrio = 0"
  "Kernel_C.minDom = 0"
  by (auto simp: seL4_MinPrio_def minDom_def)

lemma less_numDomains_is_domain[simplified word_size, simplified]:
  "x < numDomains \<Longrightarrow> x < 2 ^ size (y::domain)"
  unfolding Kernel_Config.numDomains_def
  by (simp add: word_size)

lemma sint_numDomains_to_H:
  "sint Kernel_C.numDomains = int Kernel_Config.numDomains"
  by (clarsimp simp: Kernel_C.numDomains_def Kernel_Config.numDomains_def)

lemma unat_numDomains_to_H:
  "unat Kernel_C.numDomains = Kernel_Config.numDomains"
  by (clarsimp simp: Kernel_C.numDomains_def Kernel_Config.numDomains_def)

lemma maxDom_to_H:
  "ucast maxDom = maxDomain"
  by (simp add: maxDomain_def Kernel_C.maxDom_def Kernel_Config.numDomains_def)

lemma maxDom_sgt_0_maxDomain:
  "0 <s maxDom \<longleftrightarrow> 0 < maxDomain"
  unfolding Kernel_C.maxDom_def maxDomain_def Kernel_Config.numDomains_def
  by clarsimp

lemma num_domains_calculation:
  "num_domains = numDomains"
  unfolding num_domains_val by eval

private lemma num_domains_card_explicit:
  "num_domains = CARD(num_domains)"
  by (simp add: num_domains_val)

lemmas num_domains_index_updates =
  index_update[where 'b=num_domains, folded num_domains_card_explicit num_domains_val,
               simplified num_domains_calculation]
  index_update2[where 'b=num_domains, folded num_domains_card_explicit num_domains_val,
                simplified num_domains_calculation]

(* C ArrayGuards will throw these at us and there is no way to avoid a proof of being less than a
   specific number expressed as a word, so we must introduce these. However, being explicit means
   lack of discipline can lead to a violation. *)
lemma numDomains_less_numeric_explicit[simplified num_domains_val One_nat_def]:
  "x < Kernel_Config.numDomains \<Longrightarrow> x < num_domains"
  by (simp add: num_domains_calculation)

lemma numDomains_less_unat_ucast_explicit[simplified num_domains_val]:
  "unat x < Kernel_Config.numDomains \<Longrightarrow> (ucast (x::domain) :: machine_word) < of_nat num_domains"
  apply (rule word_less_nat_alt[THEN iffD2])
  apply transfer
  apply simp
  apply (drule numDomains_less_numeric_explicit, simp add: num_domains_val)
  done

lemmas maxDomain_le_unat_ucast_explicit =
  numDomains_less_unat_ucast_explicit[simplified le_maxDomain_eq_less_numDomains(2)[symmetric],
                                      simplified]

lemma unat_scast_domScheduleLength:
  "unat (scast domScheduleLength :: machine_word) = unat domScheduleLength"
  by (simp add: domScheduleLength_def)

lemma domScheduleLength_le_unat:
  "(scast domScheduleLength \<le> n) = (unat domScheduleLength \<le> unat n)" for n::machine_word
  by (simp add: word_le_nat_alt unat_scast_domScheduleLength)

lemma less_domScheduleLength_plus_1:
  "unat n < unat domScheduleLength \<Longrightarrow> unat (n + 1) = Suc (unat n)" for n::machine_word
  by (simp add: domScheduleLength_def unat_add_lem')

end (* numDomain abstraction definitions and lemmas *)


text \<open>Priorities - not expected to be configurable\<close>

lemma maxPrio_to_H:
  "ucast seL4_MaxPrio = maxPriority"
  by (simp add: maxPriority_def seL4_MaxPrio_def numPriorities_def)


text \<open>TCB scheduling queues\<close>

(* establish and sanity-check relationship between the calculation of the number of TCB queues and
   the size of the array in C *)
value_type num_tcb_queues = "numDomains * numPriorities"

lemma num_tcb_queues_calculation:
  "num_tcb_queues = numDomains * numPriorities"
  unfolding num_tcb_queues_val by eval


text \<open>maxIRQ interface\<close>

declare Kernel_C.maxIRQ_def[code]

(* FIXME: would be more uniform to have a maxIRQ in Kernel_Config for X64 as well *)
value_type irq_array_size = "Suc (unat Kernel_C.maxIRQ)"


text \<open>TCBFlags interface\<close>

lemma scast_seL4_TCBFlag_simps[simp]:
  "scast seL4_TCBFlag_NoFlag = 0"
  "scast seL4_TCBFlag_fpuDisabled = tcbFlagToWord FpuDisabled"
  by (clarsimp simp: seL4_TCBFlag_fpuDisabled_def seL4_TCBFlag_NoFlag_def tcbFlagToWord_def)+

(* config_HAVE_FPU has to be unfolded here to match the implicit enum value from the preprocessor. *)
lemma scast_seL4_TCBFlag_MASK_tcbFlagMask[simp]:
  "scast seL4_TCBFlag_MASK = tcbFlagMask"
  by (clarsimp simp: seL4_TCBFlag_MASK_def tcbFlagMask_def Kernel_Config.config_HAVE_FPU_def tcbFlagToWord_def)

(* end of Kernel_Config interface section *)


(* Input abbreviations for API object types *)
(* disambiguates names *)

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
  "LargePageObject == seL4_X86_LargePageObject"

abbreviation(input)
  PageDirectoryObject :: sword32
where
  "PageDirectoryObject == seL4_X86_PageDirectoryObject"

abbreviation(input)
  PageTableObject :: sword32
where
  "PageTableObject == seL4_X86_PageTableObject"

abbreviation(input)
  HugePageObject :: sword32
where
  "HugePageObject == seL4_X64_HugePageObject"

abbreviation(input)
  SmallPageObject :: sword32
where
  "SmallPageObject == seL4_X86_4K"

abbreviation(input)
  PDPTObject :: sword32
where
  "PDPTObject == seL4_X86_PDPTObject"

abbreviation(input)
  PML4Object :: sword32
where
  "PML4Object == seL4_X64_PML4Object"

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

(* The magic 4 comes out of the bitfield generator -- this applies to all versions of the kernel. *)
lemma
  shows ThreadState_Restart_mask[simp]:
  "(scast ThreadState_Restart :: machine_word) && mask 4 = scast ThreadState_Restart"
  and ThreadState_Inactive_mask[simp]:
  "(scast ThreadState_Inactive :: machine_word) && mask 4 = scast ThreadState_Inactive"
  and ThreadState_Running_mask[simp]:
  "(scast ThreadState_Running :: machine_word) && mask 4 = scast ThreadState_Running"
  and ThreadState_BlockedOnReceive_mask[simp]:
  "(scast ThreadState_BlockedOnReceive :: machine_word) && mask 4
   = scast ThreadState_BlockedOnReceive"
  and ThreadState_BlockedOnSend_mask[simp]:
  "(scast ThreadState_BlockedOnSend :: machine_word) && mask 4 = scast ThreadState_BlockedOnSend"
  and ThreadState_BlockedOnReply_mask[simp]:
  "(scast ThreadState_BlockedOnReply :: machine_word) && mask 4 = scast ThreadState_BlockedOnReply"
  and ThreadState_BlockedOnNotification_mask[simp]:
  "(scast ThreadState_BlockedOnNotification :: machine_word) && mask 4
   = scast ThreadState_BlockedOnNotification"
  and ThreadState_IdleThreadState_mask[simp]:
  "(scast ThreadState_IdleThreadState :: machine_word) && mask 4 = scast ThreadState_IdleThreadState"
  by (simp add: ThreadState_defs mask_def)+

end

end
