(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory StateRelation_C
imports Wellformed_C
begin

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  "lifth p s \<equiv> the (clift (t_hrs_' s) p)"

definition
  "array_relation r n a c \<equiv> \<forall>i \<le> n. r (a i) (index c (unat i))"

definition option_to_ctcb_ptr :: "machine_word option \<Rightarrow> tcb_C ptr" where
  "option_to_ctcb_ptr x \<equiv> case x of None \<Rightarrow> NULL | Some t \<Rightarrow> tcb_ptr_to_ctcb_ptr t"


definition
  byte_to_word_heap :: "(machine_word \<Rightarrow> word8) \<Rightarrow> (machine_word \<Rightarrow> 9 word \<Rightarrow> machine_word)"
  where
  "byte_to_word_heap m base off \<equiv> let (ptr :: machine_word) = base + (ucast off * 8) in
                                       word_rcat [m (ptr + 7), m (ptr + 6), m (ptr + 5), m (ptr + 4),
                                                  m (ptr + 3), m (ptr + 2), m (ptr + 1), m ptr]"

definition
  heap_to_user_data :: "(machine_word \<Rightarrow> kernel_object option) \<Rightarrow> (machine_word \<Rightarrow> word8) \<Rightarrow> (machine_word \<Rightarrow> (9 word \<Rightarrow> machine_word) option)"
  where
  "heap_to_user_data hp bhp \<equiv> \<lambda>p. let (uhp :: machine_word \<Rightarrow> user_data option) = (projectKO_opt \<circ>\<^sub>m hp) in
                                      option_map (\<lambda>_. byte_to_word_heap bhp p) (uhp p)"

definition
  heap_to_device_data :: "(machine_word \<Rightarrow> kernel_object option) \<Rightarrow> (machine_word \<Rightarrow> word8) \<Rightarrow> (machine_word \<Rightarrow> (9 word \<Rightarrow> machine_word) option)"
  where
  "heap_to_device_data hp bhp \<equiv> \<lambda>p. let (uhp :: machine_word \<Rightarrow> user_data_device option) = (projectKO_opt \<circ>\<^sub>m hp) in
                                      option_map (\<lambda>_. byte_to_word_heap bhp p) (uhp p)"


definition
  cmap_relation :: "(machine_word \<rightharpoonup> 'a) \<Rightarrow> 'b typ_heap \<Rightarrow> (machine_word \<Rightarrow> 'b ptr) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "cmap_relation as cs addr_fun rel \<equiv>
          (addr_fun ` (dom as) = dom cs) \<and>
          (\<forall>x \<in> dom as. rel (the (as x)) (the (cs (addr_fun x))))"

definition
  carray_map_relation :: "nat \<Rightarrow> (machine_word \<rightharpoonup> ('a :: pre_storable))
    \<Rightarrow> ('b ptr \<Rightarrow> bool) \<Rightarrow> (machine_word \<Rightarrow> 'b ptr) \<Rightarrow> bool"
where
  "carray_map_relation bits as cs addr_fun \<equiv>
    (\<forall>p. (is_aligned p bits \<and> (\<forall>p'. p' && ~~ mask bits = p \<and> is_aligned p' (objBits (the (as p')))
        \<longrightarrow> p' \<in> dom as)) \<longleftrightarrow> cs (addr_fun p))"

definition
  cvariable_array_map_relation :: "(machine_word \<rightharpoonup> 'a) \<Rightarrow> ('a \<Rightarrow> nat)
    \<Rightarrow> (machine_word \<Rightarrow> ('c :: c_type) ptr) \<Rightarrow> heap_typ_desc \<Rightarrow> bool"
where
  "cvariable_array_map_relation amap szs ptrfun htd
    \<equiv> \<forall>p v. amap p = Some v \<longrightarrow> h_t_array_valid htd (ptrfun p) (szs v)"

end

text \<open>
  Conceptually, the constant armKSKernelVSpace_C resembles ghost state.
  The constant specifies the use of certain address ranges, or ``windows''.
  It is the very nature of these ranges is that they remain fixed
  after initialization.
  Hence, it is not necessary to carry this value around
  as part of the actual state.
  Rather, we simply fix it in a locale for the state relation.

  Note that this locale does not build on @{text kernel}
  but @{text substitute_pre}.
  Hence, we can later base definitions for the ADT on it,
  which can subsequently be instantiated for
  @{text kernel_all_global_addresses} as well as @{text kernel_all_substitute}.
\<close>
locale state_rel = Arch + substitute_pre + (*FIXME: arch_split*)
  fixes armKSKernelVSpace_C :: "machine_word \<Rightarrow> arm_vspace_region_use"

locale kernel = kernel_all_substitute + state_rel

context state_rel
begin

(* FIXME AARCH64 change/expand the comment in C for armKSGlobalUserVSpace to include that it's
"the default page table for when the user does not have a page table" rather than the currently
confusing
"the temporary userspace page table in kernel.
It is required before running user thread to avoid speculative page table walking with the
wrong page table." *)

abbreviation armKSGlobalUserVSpace_Ptr :: vs_ptr where
  "armKSGlobalUserVSpace_Ptr \<equiv> vs_Ptr (symbol_table ''armKSGlobalUserVSpace'')"

(* relates fixed addresses *)
definition carch_globals :: "Arch.kernel_state \<Rightarrow> bool" where
  "carch_globals s \<equiv> armKSGlobalUserVSpace s = ptr_val armKSGlobalUserVSpace_Ptr"

lemma carch_globals_armKSGlobalUserVSpace:
  "carch_globals s \<Longrightarrow> armKSGlobalUserVSpace s = symbol_table ''armKSGlobalUserVSpace''"
  by (simp add: carch_globals_def armKSGlobalUserVSpace_def)

definition cur_vcpu_relation ::
  "(machine_word \<times> bool) option \<Rightarrow> vcpu_C ptr \<Rightarrow> machine_word \<Rightarrow> bool" where
  "cur_vcpu_relation akscurvcpu cvcpu cactive \<equiv>
    case akscurvcpu of
      Some acurvcpu \<Rightarrow> cvcpu = Ptr (fst acurvcpu) \<and> cvcpu \<noteq> NULL \<and> cactive = from_bool (snd acurvcpu)
    | None \<Rightarrow> cvcpu = NULL \<and> cactive = 0"

(* FIXME AARCH64: the naming in C is confusing (do we want to change it to talk about VMIDs instead
   of HW ASIDs?:
   armKSNextVMID in Haskell is armKSNextASID in C (note this is a hw_asid_t, so should have "HW" in it
     at least)
   armKSVMIDTable in Haskell is  armKSHWASIDTable in C *)

definition carch_state_relation :: "Arch.kernel_state \<Rightarrow> globals \<Rightarrow> bool" where
  "carch_state_relation astate cstate \<equiv>
    armKSKernelVSpace astate = armKSKernelVSpace_C \<and>
    array_relation ((=) \<circ> option_to_ptr) (mask asid_high_bits) (armKSASIDTable astate) (armKSASIDTable_' cstate) \<and>
    armKSNextVMID astate = armKSNextASID_' cstate \<and>
    array_relation ((=) \<circ> option_to_0) (mask vmid_bits)
      (armKSVMIDTable astate) (armKSHWASIDTable_' cstate) \<and>
    carch_globals astate \<and>
    gic_vcpu_num_list_regs_' cstate = of_nat (armKSGICVCPUNumListRegs astate) \<and>
    cur_vcpu_relation (armHSCurVCPU astate) (armHSCurVCPU_' cstate) (armHSVCPUActive_' cstate)"

end

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  cmachine_state_relation :: "machine_state \<Rightarrow> globals \<Rightarrow> bool"
where
  "cmachine_state_relation s s' \<equiv>
  irq_masks s = irq_masks (phantom_machine_state_' s') \<and>
  irq_state s = irq_state (phantom_machine_state_' s') \<and>
  device_state s = device_state (phantom_machine_state_' s') \<and>
  \<comment> \<open>exclusive_state s = exclusive_state (phantom_machine_state_' s') \<and>\<close> \<comment> \<open>FIXME: this is needed for infoflow so we'll leave it commented\<close>
  machine_state_rest s = machine_state_rest (phantom_machine_state_' s')"


definition
  "globals_list_id_fudge = id"

type_synonym ('a, 'b) ltyp_heap = "'a ptr \<rightharpoonup> 'b"

abbreviation
  map_to_tcbs :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> tcb"
  where
  "map_to_tcbs hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

abbreviation
  map_to_eps :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> endpoint"
  where
  "map_to_eps hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

abbreviation
  map_to_ntfns :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> notification"
  where
  "map_to_ntfns hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

abbreviation
  map_to_ptes :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> pte"
  where
  "map_to_ptes hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

abbreviation
  map_to_asidpools :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> asidpool"
  where
  "map_to_asidpools hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

abbreviation
  map_to_user_data :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> user_data"
  where
  "map_to_user_data hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

abbreviation
  map_to_user_data_device :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> user_data_device"
  where
  "map_to_user_data_device hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

abbreviation
  map_to_vcpus :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> vcpu"
  where
  "map_to_vcpus hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"


definition
  cmdbnode_relation :: "Structures_H.mdbnode \<Rightarrow> mdb_node_C \<Rightarrow> bool"
where
  "cmdbnode_relation amdb cmdb \<equiv> amdb = mdb_node_to_H (mdb_node_lift cmdb)"

definition
  ccte_relation :: "Structures_H.cte \<Rightarrow> cte_C \<Rightarrow> bool"
where
  "ccte_relation acte ccte \<equiv> Some acte = option_map cte_to_H (cte_lift ccte)
                             \<and> c_valid_cte ccte"

lemma ccte_relation_c_valid_cte: "ccte_relation  c c' \<Longrightarrow> c_valid_cte c'"
  by (simp add: ccte_relation_def)


definition
  tcb_queue_relation' :: "(tcb_C \<Rightarrow> tcb_C ptr) \<Rightarrow> (tcb_C \<Rightarrow> tcb_C ptr) \<Rightarrow> (tcb_C ptr \<Rightarrow> tcb_C option) \<Rightarrow> machine_word list \<Rightarrow> tcb_C ptr \<Rightarrow> tcb_C ptr \<Rightarrow> bool"
  where
  "tcb_queue_relation' getNext getPrev hp queue qhead end \<equiv>
  (end = (if queue = [] then NULL else (tcb_ptr_to_ctcb_ptr (last queue))))
  \<and> tcb_queue_relation getNext getPrev hp queue NULL qhead"

fun register_from_H :: "register \<Rightarrow> register_idx" where
  "register_from_H AARCH64.X0          = scast Kernel_C.X0"
| "register_from_H AARCH64.X1          = scast Kernel_C.X1"
| "register_from_H AARCH64.X2          = scast Kernel_C.X2"
| "register_from_H AARCH64.X3          = scast Kernel_C.X3"
| "register_from_H AARCH64.X4          = scast Kernel_C.X4"
| "register_from_H AARCH64.X5          = scast Kernel_C.X5"
| "register_from_H AARCH64.X6          = scast Kernel_C.X6"
| "register_from_H AARCH64.X7          = scast Kernel_C.X7"
| "register_from_H AARCH64.X8          = scast Kernel_C.X8"
| "register_from_H AARCH64.X9          = scast Kernel_C.X9"
| "register_from_H AARCH64.X10         = scast Kernel_C.X10"
| "register_from_H AARCH64.X11         = scast Kernel_C.X11"
| "register_from_H AARCH64.X12         = scast Kernel_C.X12"
| "register_from_H AARCH64.X13         = scast Kernel_C.X13"
| "register_from_H AARCH64.X14         = scast Kernel_C.X14"
| "register_from_H AARCH64.X15         = scast Kernel_C.X15"
| "register_from_H AARCH64.X16         = scast Kernel_C.X16"
| "register_from_H AARCH64.X17         = scast Kernel_C.X17"
| "register_from_H AARCH64.X18         = scast Kernel_C.X18"
| "register_from_H AARCH64.X19         = scast Kernel_C.X19"
| "register_from_H AARCH64.X20         = scast Kernel_C.X20"
| "register_from_H AARCH64.X21         = scast Kernel_C.X21"
| "register_from_H AARCH64.X22         = scast Kernel_C.X22"
| "register_from_H AARCH64.X23         = scast Kernel_C.X23"
| "register_from_H AARCH64.X24         = scast Kernel_C.X24"
| "register_from_H AARCH64.X25         = scast Kernel_C.X25"
| "register_from_H AARCH64.X26         = scast Kernel_C.X26"
| "register_from_H AARCH64.X27         = scast Kernel_C.X27"
| "register_from_H AARCH64.X28         = scast Kernel_C.X28"
| "register_from_H AARCH64.X29         = scast Kernel_C.X29"
| "register_from_H AARCH64.X30         = scast Kernel_C.X30"
| "register_from_H AARCH64.SP_EL0      = scast Kernel_C.SP_EL0"
| "register_from_H AARCH64.NextIP      = scast Kernel_C.NextIP"
| "register_from_H AARCH64.SPSR_EL1    = scast Kernel_C.SPSR_EL1"
| "register_from_H AARCH64.FaultIP     = scast Kernel_C.FaultIP"
| "register_from_H AARCH64.TPIDR_EL0   = scast Kernel_C.TPIDR_EL0"
| "register_from_H AARCH64.TPIDRRO_EL0 = scast Kernel_C.TPIDRRO_EL0"

lemma ELR_EL1_is_NextIP[simp]:
  "Kernel_C.ELR_EL1 = Kernel_C.NextIP"
  by (simp add: C_register_defs)

definition
  cregs_relation :: "(MachineTypes.register \<Rightarrow> machine_word) \<Rightarrow> machine_word[registers_count] \<Rightarrow> bool"
where
  "cregs_relation Hregs Cregs \<equiv>  \<forall>r. Hregs r = Cregs.[unat (register_from_H r)]"

definition fpu_relation :: "fpu_state \<Rightarrow> user_fpu_state_C \<Rightarrow> bool" where
  "fpu_relation fpu_H fpu_C \<equiv>
     (\<forall>r < CARD(fpu_regs). (fpuRegs fpu_H) (of_nat r) = (vregs_C fpu_C).[r])
     \<and> fpuSr fpu_H = fpsr_C fpu_C
     \<and> fpuCr fpu_H = fpcr_C fpu_C"

definition
  ccontext_relation :: "user_context \<Rightarrow> user_context_C \<Rightarrow> bool"
where
  "ccontext_relation uc_H uc_C \<equiv> cregs_relation (user_regs uc_H) (registers_C uc_C) \<and>
                                 fpu_relation (fpu_state uc_H) (fpuState_C uc_C)"

primrec
  cthread_state_relation_lifted :: "Structures_H.thread_state \<Rightarrow>
   (thread_state_CL \<times> seL4_Fault_CL option) \<Rightarrow> bool"
where
  "cthread_state_relation_lifted (Structures_H.Running) ts'
     = (tsType_CL (fst ts') = scast ThreadState_Running)"
| "cthread_state_relation_lifted (Structures_H.Restart) ts'
     = (tsType_CL (fst ts') = scast ThreadState_Restart)"
| "cthread_state_relation_lifted (Structures_H.Inactive) ts'
     = (tsType_CL (fst ts') = scast ThreadState_Inactive)"
| "cthread_state_relation_lifted (Structures_H.IdleThreadState) ts'
     = (tsType_CL (fst ts') = scast ThreadState_IdleThreadState)"
| "cthread_state_relation_lifted (Structures_H.BlockedOnReply) ts'
     = (tsType_CL (fst ts') = scast ThreadState_BlockedOnReply)"
| "cthread_state_relation_lifted (Structures_H.BlockedOnReceive oref cg) ts'
     = (tsType_CL (fst ts') = scast ThreadState_BlockedOnReceive
        \<and> oref = blockingObject_CL (fst ts')
        \<and> cg = to_bool (blockingIPCCanGrant_CL (fst ts')))"
| "cthread_state_relation_lifted (Structures_H.BlockedOnSend oref badge cg cgr isc) ts'
     = (tsType_CL (fst ts') = scast ThreadState_BlockedOnSend
        \<and> oref = blockingObject_CL (fst ts')
        \<and> badge = blockingIPCBadge_CL (fst ts')
        \<and> cg    = to_bool (blockingIPCCanGrant_CL (fst ts'))
        \<and> cgr   = to_bool (blockingIPCCanGrantReply_CL (fst ts'))
        \<and> isc   = to_bool (blockingIPCIsCall_CL (fst ts')))"
| "cthread_state_relation_lifted (Structures_H.BlockedOnNotification oref) ts'
     = (tsType_CL (fst ts') = scast ThreadState_BlockedOnNotification
        \<and> oref = blockingObject_CL (fst ts'))"


definition
  cthread_state_relation :: "Structures_H.thread_state \<Rightarrow>
  (thread_state_C \<times> seL4_Fault_C) \<Rightarrow> bool"
where
  "cthread_state_relation \<equiv> \<lambda>a (cs, cf).
  cthread_state_relation_lifted a (thread_state_lift cs, seL4_Fault_lift cf)"

definition "is_cap_fault cf \<equiv>
  (case cf of (SeL4_Fault_CapFault _) \<Rightarrow> True
  | _ \<Rightarrow> False)"

lemma is_cap_fault_simp: "is_cap_fault cf = (\<exists> x. cf=SeL4_Fault_CapFault x)"
  by (simp add: is_cap_fault_def split:seL4_Fault_CL.splits)


definition
  message_info_to_H :: "seL4_MessageInfo_C \<Rightarrow> Types_H.message_info"
  where
  "message_info_to_H mi \<equiv> Types_H.message_info.MI (length_CL (seL4_MessageInfo_lift mi))
                                                  (extraCaps_CL (seL4_MessageInfo_lift mi))
                                                  (capsUnwrapped_CL (seL4_MessageInfo_lift mi))
                                                  (label_CL (seL4_MessageInfo_lift mi))"


fun
  lookup_fault_to_H :: "lookup_fault_CL \<Rightarrow> lookup_failure"
  where
  "lookup_fault_to_H Lookup_fault_invalid_root = InvalidRoot"
  | "lookup_fault_to_H (Lookup_fault_guard_mismatch lf) =
                      (GuardMismatch (unat (bitsLeft_CL lf)) (guardFound_CL lf) (unat (bitsFound_CL lf)))"
  | "lookup_fault_to_H (Lookup_fault_depth_mismatch lf) =
                      (DepthMismatch (unat (lookup_fault_depth_mismatch_CL.bitsLeft_CL lf))
                                     (unat (lookup_fault_depth_mismatch_CL.bitsFound_CL lf)))"
  | "lookup_fault_to_H (Lookup_fault_missing_capability lf) =
                        (MissingCapability (unat (lookup_fault_missing_capability_CL.bitsLeft_CL lf)))"

fun
  fault_to_H :: "seL4_Fault_CL \<Rightarrow> lookup_fault_CL \<Rightarrow> fault option"
where
  "fault_to_H SeL4_Fault_NullFault lf = None"
  | "fault_to_H (SeL4_Fault_CapFault cf) lf
           = Some (CapFault (seL4_Fault_CapFault_CL.address_CL cf) (to_bool (inReceivePhase_CL cf)) (lookup_fault_to_H lf))"
  | "fault_to_H (SeL4_Fault_VMFault vf) lf
           = Some (ArchFault (VMFault (seL4_Fault_VMFault_CL.address_CL vf) [instructionFault_CL vf, FSR_CL vf]))"
  | "fault_to_H (SeL4_Fault_UnknownSyscall us) lf
           = Some (UnknownSyscallException (syscallNumber_CL us))"
  | "fault_to_H (SeL4_Fault_UserException ue) lf
          = Some (UserException (number_CL ue) (code_CL ue))"
  | "fault_to_H (SeL4_Fault_VCPUFault vf) lf
          = Some (ArchFault (VCPUFault (seL4_Fault_VCPUFault_CL.hsr_CL vf)))"
  | "fault_to_H (SeL4_Fault_VGICMaintenance vf) lf
          = Some (ArchFault (VGICMaintenance (if seL4_Fault_VGICMaintenance_CL.idxValid_CL vf = 1
                                              then Some (seL4_Fault_VGICMaintenance_CL.idx_CL vf)
                                              else None)))"
  | "fault_to_H (SeL4_Fault_VPPIEvent irq) lf
          = Some (ArchFault (VPPIEvent (ucast (seL4_Fault_VPPIEvent_CL.irq_w_CL irq))))"

definition
  cfault_rel :: "Fault_H.fault option \<Rightarrow> seL4_Fault_CL option \<Rightarrow> lookup_fault_CL option \<Rightarrow> bool"
where
  "cfault_rel af cf lf \<equiv> \<exists>cf'. cf = Some cf' \<and>
         (if (is_cap_fault cf') then (\<exists>lf'. lf = Some lf' \<and> fault_to_H cf' lf' = af)
           else (fault_to_H cf' undefined = af))"

definition
  carch_tcb_relation :: "Structures_H.arch_tcb \<Rightarrow> arch_tcb_C \<Rightarrow> bool"
where
  "carch_tcb_relation aarch_tcb carch_tcb \<equiv>
     ccontext_relation (atcbContextGet aarch_tcb) (tcbContext_C carch_tcb)
     \<and> option_to_ptr (atcbVCPUPtr aarch_tcb) = tcbVCPU_C carch_tcb"

definition
  ctcb_relation :: "Structures_H.tcb \<Rightarrow> tcb_C \<Rightarrow> bool"
where
  "ctcb_relation atcb ctcb \<equiv>
       tcbFaultHandler atcb = tcbFaultHandler_C ctcb
     \<and> cthread_state_relation (tcbState atcb) (tcbState_C ctcb, tcbFault_C ctcb)
     \<and> tcbIPCBuffer atcb    = tcbIPCBuffer_C ctcb
     \<and> carch_tcb_relation (tcbArch atcb) (tcbArch_C ctcb)
     \<and> tcbQueued atcb       = to_bool (tcbQueued_CL (thread_state_lift (tcbState_C ctcb)))
     \<and> ucast (tcbDomain atcb) = tcbDomain_C ctcb
     \<and> ucast (tcbPriority atcb) = tcbPriority_C ctcb
     \<and> ucast (tcbMCP atcb) = tcbMCP_C ctcb
     \<and> tcbTimeSlice atcb    = unat (tcbTimeSlice_C ctcb)
     \<and> cfault_rel (tcbFault atcb) (seL4_Fault_lift (tcbFault_C ctcb))
                  (lookup_fault_lift (tcbLookupFailure_C ctcb))
     \<and> option_to_ptr (tcbBoundNotification atcb) = tcbBoundNotification_C ctcb
     \<and> option_to_ctcb_ptr (tcbSchedPrev atcb) = tcbSchedPrev_C ctcb
     \<and> option_to_ctcb_ptr (tcbSchedNext atcb) = tcbSchedNext_C ctcb"

abbreviation
  "ep_queue_relation' \<equiv> tcb_queue_relation' tcbEPNext_C tcbEPPrev_C"

definition
  cendpoint_relation :: "tcb_C typ_heap \<Rightarrow> Structures_H.endpoint \<Rightarrow> endpoint_C \<Rightarrow> bool"
where
  "cendpoint_relation h ntfn cep \<equiv>
     let cstate = endpoint_CL.state_CL (endpoint_lift cep);
         chead  = (Ptr o epQueue_head_CL o endpoint_lift) cep;
         cend   = (Ptr o epQueue_tail_CL o endpoint_lift) cep in
       case ntfn of
         IdleEP \<Rightarrow> cstate = scast EPState_Idle \<and> ep_queue_relation' h [] chead cend
       | SendEP q \<Rightarrow> cstate = scast EPState_Send \<and> ep_queue_relation' h q chead cend
       | RecvEP q \<Rightarrow> cstate = scast EPState_Recv \<and> ep_queue_relation' h q chead cend"

definition
  cnotification_relation :: "tcb_C typ_heap \<Rightarrow> Structures_H.notification \<Rightarrow>
                              notification_C \<Rightarrow> bool"
where
  "cnotification_relation h antfn cntfn \<equiv>
     let cntfn'  = notification_lift cntfn;
         cstate = notification_CL.state_CL cntfn';
         chead  = (Ptr o ntfnQueue_head_CL) cntfn';
         cend   = (Ptr o ntfnQueue_tail_CL) cntfn';
         cbound = ((Ptr o ntfnBoundTCB_CL) cntfn' :: tcb_C ptr)
     in
       (case ntfnObj antfn of
         IdleNtfn \<Rightarrow> cstate = scast NtfnState_Idle \<and> ep_queue_relation' h [] chead cend
       | WaitingNtfn q \<Rightarrow> cstate = scast NtfnState_Waiting \<and> ep_queue_relation' h q chead cend
       | ActiveNtfn msgid \<Rightarrow> cstate = scast NtfnState_Active \<and>
                           msgid = ntfnMsgIdentifier_CL cntfn' \<and>
                           ep_queue_relation' h [] chead cend)
       \<and> option_to_ctcb_ptr (ntfnBoundTCB antfn) = cbound"

lemmas pte_tag_defs =
  pte_pte_table_def
  pte_pte_page_def
  pte_pte_4k_page_def
  pte_pte_invalid_def

definition ap_from_vm_rights :: "vmrights \<Rightarrow> machine_word" where
  "ap_from_vm_rights R \<equiv> case R of
     VMKernelOnly \<Rightarrow> 0
   | VMReadWrite \<Rightarrow> 3
   | VMReadOnly \<Rightarrow> 1" \<comment> \<open>note: hyp vs non-hyp swap VMReadWrite and VMReadOnly AP values\<close>

(* Invalid PTEs map to invalid PTEs (sanity check) *)
lemma pte_0:
  "index (pte_C.words_C cpte) 0 = 0 \<Longrightarrow>
   pte_lift cpte = Some (Pte_pte_invalid)"
  by (simp add: pte_lift_def pte_get_tag_def pte_tag_defs)

(* with hypervisor support enabled, use stage-2 translation format for PTE *)
(* see makeUserPage in C *)
definition cpte_relation :: "pte \<Rightarrow> pte_C \<Rightarrow> bool" where
  "cpte_relation pte cpte \<equiv>
    (let cpte' = pte_lift cpte in
    case pte of
      InvalidPTE \<Rightarrow>
        cpte' = Some Pte_pte_invalid
    | PageTablePTE ppn \<Rightarrow>
        cpte' = Some (Pte_pte_table \<lparr> pt_base_address_CL = ppn << pageBits \<rparr>)
    | PagePTE baseaddr small global xn device vmrights \<Rightarrow>
        \<comment> \<open>Other than their type tag, the fields of page PTEs are identical\<close>
        if small
        then cpte' = Some (Pte_pte_4k_page
                             \<lparr> pte_pte_4k_page_CL.UXN_CL = of_bool xn,
                               page_base_address_CL = baseaddr,
                               nG_CL = from_bool global, \<comment> \<open>flipped in hyp mode\<close>
                               AF_CL = 1,
                               SH_CL = 0,
                               AP_CL = ap_from_vm_rights vmrights,
                               AttrIndx_CL = attridx_from_vmattributes (VMAttributes xn (\<not>device))
                                 \<comment> \<open>device means non-cacheable\<close>
                             \<rparr>)
        else cpte' = Some (Pte_pte_page
                             \<lparr> pte_pte_page_CL.UXN_CL = of_bool xn,
                               page_base_address_CL = baseaddr,
                               nG_CL = from_bool global, \<comment> \<open>flipped in hyp mode\<close>
                               AF_CL = 1,
                               SH_CL = 0,
                               AP_CL = ap_from_vm_rights vmrights,
                               AttrIndx_CL = attridx_from_vmattributes (VMAttributes xn (\<not>device))
                                 \<comment> \<open>device means non-cacheable\<close>
                             \<rparr>))"

(* note: asid_map_C is a historical name, on AARCH64 it refers to a single ASID pool entry *)
definition casid_map_relation :: "asidpool_entry option \<Rightarrow> asid_map_C \<Rightarrow> bool" where
  "casid_map_relation ap_entry_opt c_asid_map \<equiv>
    case asid_map_lift c_asid_map of
      None \<Rightarrow> False \<comment> \<open>bad tag, should never happen\<close>
    | Some Asid_map_asid_map_none \<Rightarrow> ap_entry_opt = None
    | Some (Asid_map_asid_map_vspace vsroot) \<Rightarrow>
        ap_entry_opt = Some (ASIDPoolVSpace (if to_bool (stored_vmid_valid_CL vsroot)
                                             then Some (ucast (stored_hw_vmid_CL vsroot)) else None)
                                            (vspace_root_CL vsroot))"

definition casid_pool_relation :: "asidpool \<Rightarrow> asid_pool_C \<Rightarrow> bool" where
  "casid_pool_relation asid_pool casid_pool \<equiv>
    case asid_pool of ASIDPool pool \<Rightarrow>
    case casid_pool of asid_pool_C.asid_pool_C cpool \<Rightarrow>
      array_relation casid_map_relation (mask asid_low_bits) pool cpool
      \<and> dom pool \<subseteq> {0 .. mask asid_low_bits}"

definition cvcpu_regs_relation :: "vcpu \<Rightarrow> vcpu_C \<Rightarrow> bool" where
  "cvcpu_regs_relation vcpu cvcpu \<equiv>
    \<forall>r. regs_C cvcpu.[fromEnum r] = vcpuRegs vcpu r"

definition cvcpu_vppi_masked_relation :: "vcpu \<Rightarrow> vcpu_C \<Rightarrow> bool" where
  "cvcpu_vppi_masked_relation vcpu cvcpu \<equiv>
     \<forall>vppi. (vppi_masked_C cvcpu).[fromEnum vppi]
            = from_bool (vcpuVPPIMasked vcpu vppi)"

definition virq_to_H :: "virq_C \<Rightarrow> virq" where
  "virq_to_H virq = (virq_C.words_C virq).[0]"

definition cvgic_relation :: "gicvcpuinterface \<Rightarrow> gicVCpuIface_C \<Rightarrow> bool" where
  "cvgic_relation vgic cvgic \<equiv>
       gicVCpuIface_C.hcr_C cvgic = vgicHCR vgic
     \<and> gicVCpuIface_C.vmcr_C cvgic = vgicVMCR vgic
     \<and> gicVCpuIface_C.apr_C cvgic = vgicAPR vgic
     \<and> (\<forall>i\<le>63. vgicLR vgic i = virq_to_H ((gicVCpuIface_C.lr_C cvgic).[i]))
     \<and> (\<forall>i\<ge>64. vgicLR vgic i = 0)"

definition cvcpu_relation :: "vcpu \<Rightarrow> vcpu_C \<Rightarrow> bool" where
  "cvcpu_relation vcpu cvcpu \<equiv>
     vcpuTCB_C cvcpu = option_to_ctcb_ptr (vcpuTCBPtr vcpu)
     \<and> cvcpu_regs_relation vcpu cvcpu
     \<and> cvgic_relation (vcpuVGIC vcpu) (vgic_C cvcpu)
     \<and> cvcpu_vppi_masked_relation vcpu cvcpu
     \<and> last_pcount_C (virtTimer_C cvcpu) = vtimerLastPCount (vcpuVTimer vcpu)"

definition
  cuser_user_data_relation :: "(9 word \<Rightarrow> machine_word) \<Rightarrow> user_data_C \<Rightarrow> bool"
where
  "cuser_user_data_relation f ud \<equiv> \<forall>off. f off = index (user_data_C.words_C ud) (unat off)"

definition
  cuser_user_data_device_relation :: "(9 word \<Rightarrow> machine_word) \<Rightarrow> user_data_device_C \<Rightarrow> bool"
where
  "cuser_user_data_device_relation f ud \<equiv> True"

abbreviation
  "cpspace_cte_relation ah ch \<equiv> cmap_relation (map_to_ctes ah) (clift ch) Ptr ccte_relation"

abbreviation
  "cpspace_tcb_relation ah ch \<equiv> cmap_relation (map_to_tcbs ah) (clift ch) tcb_ptr_to_ctcb_ptr ctcb_relation"

abbreviation
  "cpspace_ep_relation ah ch \<equiv> cmap_relation (map_to_eps ah) (clift ch) Ptr (cendpoint_relation (clift ch))"

abbreviation
  "cpspace_ntfn_relation ah ch \<equiv> cmap_relation (map_to_ntfns ah) (clift ch) Ptr (cnotification_relation (clift ch))"

abbreviation
  "cpspace_pte_relation ah ch \<equiv> cmap_relation (map_to_ptes ah) (clift ch) Ptr cpte_relation"

abbreviation
  "cpspace_asidpool_relation ah ch \<equiv> cmap_relation (map_to_asidpools ah) (clift ch) Ptr casid_pool_relation"

abbreviation
  "cpspace_vcpu_relation ah ch \<equiv> cmap_relation (map_to_vcpus ah) (clift ch) Ptr cvcpu_relation"

abbreviation
  "cpspace_user_data_relation ah bh ch \<equiv> cmap_relation (heap_to_user_data ah bh) (clift ch) Ptr cuser_user_data_relation"

abbreviation
  "cpspace_device_data_relation ah bh ch \<equiv> cmap_relation (heap_to_device_data ah bh) (clift ch) Ptr cuser_user_data_device_relation"

definition
  cpspace_relation :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> (machine_word \<Rightarrow> word8) \<Rightarrow> heap_raw_state \<Rightarrow> bool"
where
  "cpspace_relation ah bh ch \<equiv>
    cpspace_cte_relation ah ch \<and> cpspace_tcb_relation ah ch \<and> cpspace_ep_relation ah ch \<and> cpspace_ntfn_relation ah ch \<and>
    cpspace_pte_relation ah ch \<and> cpspace_asidpool_relation ah ch \<and>
    cpspace_user_data_relation ah bh ch \<and> cpspace_device_data_relation ah bh ch \<and>
    cpspace_vcpu_relation ah ch"

(*
  We sometimes want to treat page tables as arrays, e.g. in Retype. Also, pointer addition
  as in lookupPTSlot creates array_assertion guards in the C parser, which require an array type
  tag in the heap, so we can't escape the array in Retype by creating single PTEs instead.

  It is Ok to represent the same area of memory as a set of independent PTEs and as an array at
  the same time. See thms h_t_array_valid and h_t_array_valid_field that show both types being
  valid at the same time -- this means cpspace_pte_relation does not create a contradiction with
  the below.

  It is *not* Ok to represent the same (overlapping) area of memory as arrays of different
  lengths (VSRootPT/NormalPT), because the array type tag contains the length, leading to a
  contradiction. This means we can't use carray_map_relation for both types.

  We can use ghost state to say which arrays should have which type to avoid overlaps. The
  CNode cte_array_relation relation already provides a mechanism for that (as opposed to
  cpspace_cte_relation which handles single ctes).

*)
abbreviation pt_array_relation :: "kernel_state \<Rightarrow> globals \<Rightarrow> bool" where
  "pt_array_relation astate cstate \<equiv>
     cvariable_array_map_relation (gsPTTypes (ksArchState astate))
                                  (\<lambda>pt_t. 2 ^ ptTranslationBits pt_t)
                                  pte_Ptr
                                  (hrs_htd (t_hrs_' cstate))"

abbreviation
  "sched_queue_relation' \<equiv> tcb_queue_relation' tcbSchedNext_C tcbSchedPrev_C"

abbreviation
  end_C :: "tcb_queue_C \<Rightarrow> tcb_C ptr"
where
 "end_C == tcb_queue_C.end_C"

definition
  cready_queues_index_to_C :: "domain \<Rightarrow> priority \<Rightarrow> nat"
where
  "cready_queues_index_to_C qdom prio \<equiv> (unat qdom) * numPriorities + (unat prio)"

definition ctcb_queue_relation :: "tcb_queue \<Rightarrow> tcb_queue_C \<Rightarrow> bool" where
   "ctcb_queue_relation aqueue cqueue \<equiv>
      head_C cqueue = option_to_ctcb_ptr (tcbQueueHead aqueue)
      \<and> end_C cqueue = option_to_ctcb_ptr (tcbQueueEnd aqueue)"

definition cready_queues_relation ::
  "(domain \<times> priority \<Rightarrow> ready_queue) \<Rightarrow> (tcb_queue_C[num_tcb_queues]) \<Rightarrow>  bool"
  where
  "cready_queues_relation aqueues cqueues \<equiv>
     \<forall>d p. d \<le> maxDomain \<and> p \<le> maxPriority
           \<longrightarrow> ctcb_queue_relation (aqueues (d, p)) (index cqueues (cready_queues_index_to_C d p))"

abbreviation
  "cte_array_relation astate cstate
    \<equiv> cvariable_array_map_relation (gsCNodes astate) (\<lambda>n. 2 ^ n)
        cte_Ptr (hrs_htd (t_hrs_' cstate))"

(* There are 5 elements in the TCB CTE *)
abbreviation
  "tcb_cte_array_relation astate cstate
    \<equiv> cvariable_array_map_relation (map_to_tcbs (ksPSpace astate))
        (\<lambda>x. 5) cte_Ptr (hrs_htd (t_hrs_' cstate))"

fun
  irqstate_to_C :: "irqstate \<Rightarrow> machine_word"
  where
  "irqstate_to_C IRQInactive = scast Kernel_C.IRQInactive"
  | "irqstate_to_C IRQSignal = scast Kernel_C.IRQSignal"
  | "irqstate_to_C IRQTimer = scast Kernel_C.IRQTimer"
  | "irqstate_to_C irqstate.IRQReserved = scast Kernel_C.IRQReserved"

definition
  cinterrupt_relation :: "interrupt_state \<Rightarrow> 'a ptr \<Rightarrow> (machine_word[irq_array_size]) \<Rightarrow> bool"
where
  "cinterrupt_relation airqs cnode cirqs \<equiv>
     cnode = Ptr (intStateIRQNode airqs) \<and>
     (\<forall>irq \<le> (ucast Kernel_C.maxIRQ).
       irqstate_to_C (intStateIRQTable airqs irq) = index cirqs (unat irq))"

definition
  cscheduler_action_relation :: "Structures_H.scheduler_action \<Rightarrow> tcb_C ptr \<Rightarrow> bool"
where
  "cscheduler_action_relation a p \<equiv> case a of
     ResumeCurrentThread \<Rightarrow> p = NULL
   | ChooseNewThread \<Rightarrow> p = Ptr 1
   | SwitchToThread p' \<Rightarrow> p = tcb_ptr_to_ctcb_ptr p'"

definition
  dom_schedule_entry_relation :: "8 word \<times> machine_word \<Rightarrow> dschedule_C \<Rightarrow> bool"
where
  "dom_schedule_entry_relation adomSched cdomSched \<equiv>
     ucast (fst adomSched) = dschedule_C.domain_C cdomSched \<and>
     (snd adomSched) = dschedule_C.length_C cdomSched"

definition
  cdom_schedule_relation :: "(8 word \<times> machine_word) list \<Rightarrow> (dschedule_C['b :: finite]) \<Rightarrow> bool"
where
  "cdom_schedule_relation adomSched cdomSched \<equiv>
     length adomSched = card (UNIV :: 'b set) \<and>
     (\<forall>n \<le> length adomSched. dom_schedule_entry_relation (adomSched ! n) (index cdomSched n))"

definition
  ghost_size_rel :: "cghost_state \<Rightarrow> nat \<Rightarrow> bool"
where
  "ghost_size_rel gs maxSize = ((gs_get_assn cap_get_capSizeBits_'proc gs = 0
            \<and> maxSize = card (UNIV :: machine_word set))
    \<or> (maxSize > 0 \<and> maxSize = unat (gs_get_assn cap_get_capSizeBits_'proc gs)))"

definition
  cbitmap_L1_relation :: "machine_word['dom::finite] \<Rightarrow> (domain \<Rightarrow> machine_word) \<Rightarrow> bool"
where
  "cbitmap_L1_relation cbitmap1 abitmap1 \<equiv>
    \<forall>d. (d \<le> maxDomain \<longrightarrow> cbitmap1.[unat d] = abitmap1 d) \<and>
        (\<not> d \<le> maxDomain \<longrightarrow> abitmap1 d = 0)"

definition
  cbitmap_L2_relation :: "machine_word['i::finite]['dom::finite]
                          \<Rightarrow> ((domain \<times> nat) \<Rightarrow> machine_word) \<Rightarrow> bool"
where
  "cbitmap_L2_relation cbitmap2 abitmap2 \<equiv>
    \<forall>d i. ((d \<le> maxDomain \<and> i < l2BitmapSize)
            \<longrightarrow> cbitmap2.[unat d].[i] = abitmap2 (d, i)) \<and>
           ((\<not> (d \<le> maxDomain \<and> i < l2BitmapSize))
            \<longrightarrow>  abitmap2 (d, i) = 0)"

end (* interpretation Arch . (*FIXME: arch_split*) *)

definition
   region_is_bytes' :: "machine_word \<Rightarrow> nat \<Rightarrow> heap_typ_desc \<Rightarrow> bool"
where
  "region_is_bytes' ptr sz htd \<equiv> \<forall>z\<in>{ptr ..+ sz}. \<forall> td. td \<noteq> typ_uinfo_t TYPE (word8) \<longrightarrow>
    (\<forall>n b. snd (htd z) n \<noteq> Some (td, b))"

abbreviation
  region_is_bytes :: "machine_word \<Rightarrow> nat \<Rightarrow> globals myvars \<Rightarrow> bool"
where
  "region_is_bytes ptr sz s \<equiv> region_is_bytes' ptr sz (hrs_htd (t_hrs_' (globals s)))"

abbreviation(input)
  "heap_list_is_zero hp ptr n \<equiv> heap_list hp n ptr = replicate n 0"

abbreviation
  "region_is_zero_bytes ptr n x \<equiv> region_is_bytes ptr n x
      \<and> heap_list_is_zero (hrs_mem (t_hrs_' (globals x))) ptr n"

definition
  region_actually_is_bytes' :: "addr \<Rightarrow> nat \<Rightarrow> heap_typ_desc \<Rightarrow> bool"
where
  "region_actually_is_bytes' ptr len htd
    = (\<forall>x \<in> {ptr ..+ len}. htd x
        = (True, [0 \<mapsto> (typ_uinfo_t TYPE(8 word), True)]))"

abbreviation
  "region_actually_is_bytes ptr len s
    \<equiv> region_actually_is_bytes' ptr len (hrs_htd (t_hrs_' (globals s)))"

lemmas region_actually_is_bytes_def = region_actually_is_bytes'_def

abbreviation
  "region_actually_is_zero_bytes ptr len s
    \<equiv> region_actually_is_bytes ptr len s
        \<and> heap_list_is_zero (hrs_mem (t_hrs_' (globals s))) ptr len"

definition
  zero_ranges_are_zero
where
  "zero_ranges_are_zero rs hrs
    = (\<forall>(start, end) \<in> rs. region_actually_is_bytes' start (unat ((end + 1) - start)) (hrs_htd hrs)
        \<and> heap_list_is_zero (hrs_mem hrs) start (unat ((end + 1) - start)))"

context state_rel begin

value_type intState_array_size = "2^irqBits :: nat"

\<comment> \<open>The IRQ node is a global array of CTEs.\<close>
abbreviation intStateIRQNode_array_Ptr :: "(cte_C[intState_array_size]) ptr" where
  "intStateIRQNode_array_Ptr \<equiv> Ptr (symbol_table ''intStateIRQNode'')"

\<comment> \<open>But for compatibility with older proofs (written when the IRQ Node was a global pointer
    initialised during boot), it is sometimes convenient to treat the IRQ node pointer as
    a pointer to a CTE.\<close>
abbreviation intStateIRQNode_Ptr :: "cte_C ptr" where
  "intStateIRQNode_Ptr \<equiv> Ptr (symbol_table ''intStateIRQNode'')"

definition
  cstate_relation :: "KernelStateData_H.kernel_state \<Rightarrow> globals \<Rightarrow> bool"
where
  cstate_relation_def:
  "cstate_relation astate cstate \<equiv>
     let cheap = t_hrs_' cstate in
       cpspace_relation (ksPSpace astate) (underlying_memory (ksMachineState astate)) cheap \<and>
       cready_queues_relation (ksReadyQueues astate) (ksReadyQueues_' cstate) \<and>
       zero_ranges_are_zero (gsUntypedZeroRanges astate) cheap \<and>
       cbitmap_L1_relation (ksReadyQueuesL1Bitmap_' cstate) (ksReadyQueuesL1Bitmap astate) \<and>
       cbitmap_L2_relation (ksReadyQueuesL2Bitmap_' cstate) (ksReadyQueuesL2Bitmap astate) \<and>
       ksCurThread_' cstate = (tcb_ptr_to_ctcb_ptr (ksCurThread astate)) \<and>
       ksIdleThread_' cstate = (tcb_ptr_to_ctcb_ptr (ksIdleThread astate)) \<and>
       cinterrupt_relation (ksInterruptState astate) intStateIRQNode_array_Ptr (intStateIRQTable_' cstate) \<and>
       cscheduler_action_relation (ksSchedulerAction astate)
                                 (ksSchedulerAction_' cstate) \<and>
       carch_state_relation (ksArchState astate) cstate \<and>
       cmachine_state_relation (ksMachineState astate) cstate \<and>
       cte_array_relation astate cstate \<and>
       tcb_cte_array_relation astate cstate \<and>
       pt_array_relation astate cstate \<and>
       apsnd fst (ghost'state_' cstate) = (gsUserPages astate, gsCNodes astate) \<and>
       fst (snd (snd (ghost'state_' cstate))) = gsPTTypes (ksArchState astate) \<and>
       ghost_size_rel (ghost'state_' cstate) (gsMaxObjectSize astate) \<and>
       ksWorkUnitsCompleted_' cstate = ksWorkUnitsCompleted astate \<and>
       h_t_valid (hrs_htd (t_hrs_' cstate)) c_guard intStateIRQNode_array_Ptr \<and>
       ptr_span intStateIRQNode_array_Ptr \<subseteq> kernel_data_refs \<and>
       h_t_valid (hrs_htd (t_hrs_' cstate)) c_guard armKSGlobalUserVSpace_Ptr  \<and>
       ptr_span armKSGlobalUserVSpace_Ptr \<subseteq> kernel_data_refs \<and>
       htd_safe domain (hrs_htd (t_hrs_' cstate)) \<and>
       -domain \<subseteq> kernel_data_refs \<and>
       globals_list_distinct (- kernel_data_refs) symbol_table globals_list \<and>
       cdom_schedule_relation (ksDomSchedule astate)
                              Kernel_C.kernel_all_global_addresses.ksDomSchedule \<and>
       ksDomScheduleIdx_' cstate = of_nat (ksDomScheduleIdx astate) \<and>
       ksCurDomain_' cstate = ucast (ksCurDomain astate) \<and>
       ksDomainTime_' cstate = ksDomainTime astate"

end

definition
  ccap_relation :: "capability \<Rightarrow> cap_C \<Rightarrow> bool"
where
  "ccap_relation acap ccap \<equiv> (Some acap = option_map cap_to_H (cap_lift ccap))
                             \<and> (c_valid_cap ccap)"

lemma ccap_relation_c_valid_cap: "ccap_relation  c c' \<Longrightarrow> c_valid_cap c'"
  by (simp add: ccap_relation_def)

context begin interpretation Arch .
fun
  arch_fault_to_fault_tag :: "arch_fault \<Rightarrow> machine_word"
  where
  "arch_fault_to_fault_tag (VMFault a b) = scast seL4_Fault_VMFault"
| "arch_fault_to_fault_tag (VCPUFault a) = scast seL4_Fault_VCPUFault"
| "arch_fault_to_fault_tag (VGICMaintenance a) = scast seL4_Fault_VGICMaintenance"
| "arch_fault_to_fault_tag (VPPIEvent a) = scast seL4_Fault_VPPIEvent"
end

fun
  fault_to_fault_tag :: "fault \<Rightarrow> machine_word"
where
  "  fault_to_fault_tag (CapFault a b c) = scast seL4_Fault_CapFault"
  | "fault_to_fault_tag (ArchFault f)    = arch_fault_to_fault_tag f"
  | "fault_to_fault_tag (UnknownSyscallException a) = scast seL4_Fault_UnknownSyscall"
  | "fault_to_fault_tag (UserException a b) = scast seL4_Fault_UserException"

lemmas seL4_Faults = seL4_Fault_UserException_def
                     seL4_Fault_UnknownSyscall_def
                     seL4_Fault_CapFault_def

lemmas seL4_Arch_Faults = seL4_Fault_VMFault_def
                          seL4_Fault_VCPUFault_def
                          seL4_Fault_VGICMaintenance_def
                          seL4_Fault_VPPIEvent_def

(* Return relations *)

record errtype =
  errfault :: "seL4_Fault_CL option"
  errlookup_fault :: "lookup_fault_CL option"
  errsyscall :: syscall_error_C

primrec
  lookup_failure_rel :: "lookup_failure \<Rightarrow> machine_word \<Rightarrow> errtype \<Rightarrow> bool"
where
  "lookup_failure_rel InvalidRoot fl es = (fl = scast EXCEPTION_LOOKUP_FAULT \<and> errlookup_fault es = Some Lookup_fault_invalid_root)"
| "lookup_failure_rel (GuardMismatch bl gf sz) fl es = (fl = scast EXCEPTION_LOOKUP_FAULT \<and>
    (\<exists>lf. errlookup_fault es = Some (Lookup_fault_guard_mismatch lf) \<and>
          guardFound_CL lf = gf \<and> unat (bitsLeft_CL lf) = bl \<and> unat (bitsFound_CL lf) = sz))"
| "lookup_failure_rel (DepthMismatch bl bf) fl es = (fl = scast EXCEPTION_LOOKUP_FAULT \<and>
    (\<exists>lf. errlookup_fault es = Some (Lookup_fault_depth_mismatch lf) \<and>
          unat (lookup_fault_depth_mismatch_CL.bitsLeft_CL lf) = bl
        \<and> unat (lookup_fault_depth_mismatch_CL.bitsFound_CL lf) = bf))"
| "lookup_failure_rel (MissingCapability bl) fl es = (fl = scast EXCEPTION_LOOKUP_FAULT \<and>
    (\<exists>lf. errlookup_fault es = Some (Lookup_fault_missing_capability lf) \<and>
          unat (lookup_fault_missing_capability_CL.bitsLeft_CL lf) = bl))"


definition
  syscall_error_to_H :: "syscall_error_C \<Rightarrow> lookup_fault_CL option \<Rightarrow> syscall_error option"
where
 "syscall_error_to_H se lf \<equiv>
    if syscall_error_C.type_C se = scast seL4_InvalidArgument
         then Some (InvalidArgument (unat (invalidArgumentNumber_C se)))
    else if syscall_error_C.type_C se = scast seL4_InvalidCapability
         then Some (InvalidCapability (unat (invalidCapNumber_C se)))
    else if syscall_error_C.type_C se = scast seL4_IllegalOperation then Some IllegalOperation
    else if syscall_error_C.type_C se = scast seL4_RangeError
         then Some (RangeError (rangeErrorMin_C se) (rangeErrorMax_C se))
    else if syscall_error_C.type_C se = scast seL4_AlignmentError then Some AlignmentError
    else if syscall_error_C.type_C se = scast seL4_FailedLookup
         then option_map (FailedLookup (to_bool (failedLookupWasSource_C se))
                           o lookup_fault_to_H) lf
    else if syscall_error_C.type_C se = scast seL4_TruncatedMessage then Some TruncatedMessage
    else if syscall_error_C.type_C se = scast seL4_DeleteFirst then Some DeleteFirst
    else if syscall_error_C.type_C se = scast seL4_RevokeFirst then Some RevokeFirst
    else if syscall_error_C.type_C se = scast seL4_NotEnoughMemory then Some (NotEnoughMemory (memoryLeft_C se))
    else None"

lemmas syscall_error_type_defs
    = seL4_AlignmentError_def seL4_DeleteFirst_def seL4_FailedLookup_def
      seL4_IllegalOperation_def seL4_InvalidArgument_def seL4_InvalidCapability_def
      seL4_NotEnoughMemory_def seL4_RangeError_def seL4_RevokeFirst_def
      seL4_TruncatedMessage_def

lemma
  syscall_error_to_H_cases:
 "syscall_error_C.type_C se = scast seL4_InvalidArgument
     \<Longrightarrow> syscall_error_to_H se lf = Some (InvalidArgument (unat (invalidArgumentNumber_C se)))"
 "syscall_error_C.type_C se = scast seL4_InvalidCapability
     \<Longrightarrow> syscall_error_to_H se lf =  Some (InvalidCapability (unat (invalidCapNumber_C se)))"
 "syscall_error_C.type_C se = scast seL4_IllegalOperation
     \<Longrightarrow> syscall_error_to_H se lf = Some IllegalOperation"
 "syscall_error_C.type_C se = scast seL4_RangeError
     \<Longrightarrow> syscall_error_to_H se lf = Some (RangeError (rangeErrorMin_C se) (rangeErrorMax_C se))"
 "syscall_error_C.type_C se = scast seL4_AlignmentError
     \<Longrightarrow> syscall_error_to_H se lf = Some AlignmentError"
 "syscall_error_C.type_C se = scast seL4_FailedLookup
     \<Longrightarrow> syscall_error_to_H se lf =  option_map (FailedLookup (to_bool (failedLookupWasSource_C se))
                           o lookup_fault_to_H) lf"
 "syscall_error_C.type_C se = scast seL4_TruncatedMessage
     \<Longrightarrow> syscall_error_to_H se lf = Some TruncatedMessage"
 "syscall_error_C.type_C se = scast seL4_DeleteFirst
     \<Longrightarrow> syscall_error_to_H se lf = Some DeleteFirst"
 "syscall_error_C.type_C se = scast seL4_RevokeFirst
     \<Longrightarrow> syscall_error_to_H se lf = Some RevokeFirst"
 "syscall_error_C.type_C se = scast seL4_NotEnoughMemory
     \<Longrightarrow> syscall_error_to_H se lf = Some (NotEnoughMemory (memoryLeft_C se))"
  by (simp add: syscall_error_to_H_def syscall_error_type_defs)+

definition
  syscall_error_rel :: "syscall_error \<Rightarrow> machine_word \<Rightarrow> errtype \<Rightarrow> bool" where
 "syscall_error_rel se fl es \<equiv> fl = scast EXCEPTION_SYSCALL_ERROR
                                 \<and> syscall_error_to_H (errsyscall es) (errlookup_fault es)
                                       = Some se"

(* cap rights *)
definition
  "cap_rights_to_H rs \<equiv> CapRights (to_bool (capAllowWrite_CL rs))
                                  (to_bool (capAllowRead_CL rs))
                                  (to_bool (capAllowGrant_CL rs))
                                  (to_bool (capAllowGrantReply_CL rs))"

definition
  "ccap_rights_relation cr cr' \<equiv> cr = cap_rights_to_H (seL4_CapRights_lift cr')"

definition
  syscall_from_H :: "syscall \<Rightarrow> machine_word"
where
  "syscall_from_H c \<equiv> case c of
    SysSend \<Rightarrow> scast Kernel_C.SysSend
  | SysNBSend \<Rightarrow> scast Kernel_C.SysNBSend
  | SysCall \<Rightarrow> scast Kernel_C.SysCall
  | SysRecv \<Rightarrow> scast Kernel_C.SysRecv
  | SysReply \<Rightarrow> scast Kernel_C.SysReply
  | SysReplyRecv \<Rightarrow> scast Kernel_C.SysReplyRecv
  | SysNBRecv \<Rightarrow> scast Kernel_C.SysNBRecv
  | SysYield \<Rightarrow> scast Kernel_C.SysYield"

context kernel
begin

lemma syscall_error_to_H_cases_rev:
  "\<And>n. syscall_error_to_H e lf = Some (InvalidArgument n) \<Longrightarrow>
        syscall_error_C.type_C e = scast seL4_InvalidArgument"
  "\<And>n. syscall_error_to_H e lf = Some (InvalidCapability n) \<Longrightarrow>
        syscall_error_C.type_C e = scast seL4_InvalidCapability"
  "syscall_error_to_H e lf = Some IllegalOperation \<Longrightarrow>
        syscall_error_C.type_C e = scast seL4_IllegalOperation"
  "\<And>w1 w2. syscall_error_to_H e lf = Some (RangeError w1 w2) \<Longrightarrow>
        syscall_error_C.type_C e = scast seL4_RangeError"
  "syscall_error_to_H e lf = Some AlignmentError \<Longrightarrow>
        syscall_error_C.type_C e = scast seL4_AlignmentError"
  "\<And>b lf'. syscall_error_to_H e lf = Some (FailedLookup b lf') \<Longrightarrow>
        syscall_error_C.type_C e = scast seL4_FailedLookup"
  "syscall_error_to_H e lf = Some TruncatedMessage \<Longrightarrow>
        syscall_error_C.type_C e = scast seL4_TruncatedMessage"
  "syscall_error_to_H e lf = Some DeleteFirst \<Longrightarrow>
        syscall_error_C.type_C e = scast seL4_DeleteFirst"
  "syscall_error_to_H e lf = Some RevokeFirst \<Longrightarrow>
        syscall_error_C.type_C e = scast seL4_RevokeFirst"
  by (clarsimp simp: syscall_error_to_H_def syscall_error_type_defs
              split: if_split_asm)+

lemma cmap_relation_cs_atD:
  "\<lbrakk> cmap_relation as cs addr_fun rel; cs (addr_fun x) = Some y; inj addr_fun \<rbrakk> \<Longrightarrow>
  \<exists>ko. as x = Some ko \<and> rel ko y"
  apply (clarsimp simp: cmap_relation_def)
  apply (subgoal_tac "x \<in> dom as")
   apply (drule (1) bspec)
   apply (clarsimp simp: dom_def)
  apply (subgoal_tac "addr_fun x \<in> addr_fun ` dom as")
   prefer 2
   apply fastforce
  apply (erule imageE)
  apply (drule (1) injD)
  apply simp
  done

definition
  rf_sr :: "(KernelStateData_H.kernel_state \<times> cstate) set"
  where
  "rf_sr \<equiv> {(s, s'). cstate_relation s (globals s')}"

end

end
