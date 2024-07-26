(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory StateRelation_C
imports Wellformed_C
begin

context begin interpretation Arch . (*FIXME: arch-split*)

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
  Conceptually, the constant x64KSKernelVSpace_C resembles ghost state.
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
locale state_rel = Arch + substitute_pre + (*FIXME: arch-split*)
  fixes x64KSKernelVSpace_C :: "machine_word \<Rightarrow> x64vspace_region_use"

locale kernel = kernel_all_substitute + state_rel

context state_rel
begin

abbreviation x64KSSKIMPML4_Ptr :: "(pml4e_C[512]) ptr" where
  "x64KSSKIMPML4_Ptr \<equiv> pml4_Ptr (symbol_table ''x64KSSKIMPML4'')"

abbreviation x64KSSKIMPDPT_Ptr :: "(pdpte_C[512]) ptr" where
  "x64KSSKIMPDPT_Ptr \<equiv> pdpt_Ptr (symbol_table ''x64KSSKIMPDPT'')"

abbreviation x64KSSKIMPD_Ptr :: "(pde_C[512]) ptr" where
  "x64KSSKIMPD_Ptr \<equiv> pd_Ptr (symbol_table ''x64KSSKIMPD'')"

(* relates fixed adresses *)
definition
  "carch_globals s \<equiv> (x64KSSKIMPML4 s = ptr_val x64KSSKIMPML4_Ptr)
                   \<and> (x64KSSKIMPDPTs s = [ptr_val x64KSSKIMPDPT_Ptr])
                   \<and> (x64KSSKIMPDs s = [ptr_val x64KSSKIMPD_Ptr])
                   \<and> (x64KSSKIMPTs s = [])"

(* FIXME x64: DON'T DELETE!
    keep this for a rainy day, if we find out that leaving the asid map out of the state relation
    is no longer possible
    This recreates the asid map from the asid table *)
definition
  asid_map_trace
where
  "asid_map_trace s \<equiv> \<lambda>asid. case (x64KSASIDTable (ksArchState s)) (asidHighBitsOf asid) of None \<Rightarrow> None |
       Some asidpoolptr \<Rightarrow> case (ksPSpace s) asidpoolptr of None \<Rightarrow> None |
          Some (KOArch (KOASIDPool (ASIDPool pool))) \<Rightarrow> pool (asid && mask asidLowBits)"

(* The C kernel stores and performs operations on the current CR3 as a word.
   This means that we need to reason about bits which the bitfield generator ignores.
   We therefore encode an invariant about those extra bits here. *)
definition
  ccr3_relation :: "X64_H.cr3 \<Rightarrow> machine_word \<Rightarrow> bool"
where
  "ccr3_relation hcr3 ccr3 \<equiv>
     case hcr3 of
       CR3 addr pcid \<Rightarrow> addr = ccr3 && (mask 39 << 12)
                         \<and> pcid = ccr3 && mask 12
                         \<and> 1 << 63 = ccr3 && (~~ mask 51)"

fun
  x86_irq_state_to_H :: "x86_irq_state_CL \<Rightarrow> x64irqstate"
where
  "x86_irq_state_to_H X86_irq_state_irq_free = X64IRQFree"
| "x86_irq_state_to_H X86_irq_state_irq_reserved = X64IRQReserved"
| "x86_irq_state_to_H (X86_irq_state_irq_ioapic irq_ioapic) =
     X64IRQIOAPIC
       (ucast (id_CL irq_ioapic))
       (ucast (pin_CL irq_ioapic))
       (ucast (level_CL irq_ioapic))
       (ucast (polarity_low_CL irq_ioapic))
       (to_bool (masked_CL irq_ioapic))"
| "x86_irq_state_to_H (X86_irq_state_irq_msi irq_msi) =
     X64IRQMSI
       (ucast (bus_CL irq_msi))
       (ucast (dev_CL irq_msi))
       (ucast (func_CL irq_msi))
       (ucast (handle_CL irq_msi))"

definition
  x64_irq_state_relation :: "x64irqstate \<Rightarrow> x86_irq_state_C \<Rightarrow> bool"
where
  "x64_irq_state_relation s s' \<equiv>
     case x86_irq_state_lift s' of
       None \<Rightarrow> False \<comment> \<open>should never happen\<close>
     | Some x \<Rightarrow> s = x86_irq_state_to_H x"

(* This is required for type collision shenanigans, 1024 matches above *)
lemma ntbs_1024[simp]:
  "nat_to_bin_string 1024 = ''000000000010''"
  by (simp add: nat_to_bin_string_simps)

definition
  cioport_bitmap_to_H :: "ioport_table_C \<Rightarrow> (ioport \<Rightarrow> bool)"
where
  "cioport_bitmap_to_H ctable \<equiv>
    \<lambda>port. ctable.[unat (port >> wordRadix)] !! unat (port && mask wordRadix)"

definition
  global_ioport_bitmap_relation :: "(ioport_table_C ptr \<Rightarrow> ioport_table_C option) \<Rightarrow>
                                      (ioport \<Rightarrow> bool) \<Rightarrow> bool"
where
  "global_ioport_bitmap_relation ctable_heap htable \<equiv>
    \<exists>ctable. ctable_heap (Ptr (symbol_table ''x86KSAllocatedIOPorts'')) = Some ctable
           \<and> cioport_bitmap_to_H ctable = htable
           \<and> ptr_span (ioport_table_Ptr (symbol_table ''x86KSAllocatedIOPorts'')) \<subseteq> kernel_data_refs"

definition
  fpu_null_state_relation :: "heap_raw_state \<Rightarrow> bool"
where
  "fpu_null_state_relation hrs \<equiv>
    clift hrs (Ptr (symbol_table ''x86KSnullFpuState''))
      = Some (user_fpu_state_C (ARRAY i. FPUNullState (finite_index i))) \<and>
    ptr_span (fpu_state_Ptr (symbol_table ''x86KSnullFpuState'')) \<subseteq> kernel_data_refs"

definition
  carch_state_relation :: "Arch.kernel_state \<Rightarrow> globals \<Rightarrow> bool"
where
  "carch_state_relation astate cstate \<equiv>
    x64KSKernelVSpace astate = x64KSKernelVSpace_C \<and>
    array_relation ((=) \<circ> option_to_ptr) (2^asid_high_bits - 1) (x64KSASIDTable astate) (x86KSASIDTable_' cstate) \<and>
    ccr3_relation (x64KSCurrentUserCR3 astate) (x64KSCurrentUserCR3_' cstate) \<and>
    global_ioport_bitmap_relation (clift (t_hrs_' cstate)) (x64KSAllocatedIOPorts astate) \<and>
    fpu_null_state_relation (t_hrs_' cstate) \<and>
    x64KSNumIOAPICs astate = UCAST (32 \<rightarrow> 64) (num_ioapics_' cstate) \<and>
    array_relation (=) (of_nat Kernel_Config.maxNumIOAPIC) (x64KSIOAPICnIRQs astate) (ioapic_nirqs_' cstate) \<and>
    array_relation x64_irq_state_relation maxIRQ (x64KSIRQState astate) (x86KSIRQState_' cstate) \<and>
    carch_globals astate"

end

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  cmachine_state_relation :: "machine_state \<Rightarrow> globals \<Rightarrow> bool"
where
  "cmachine_state_relation s s' \<equiv>
  irq_masks s = irq_masks (phantom_machine_state_' s') \<and>
  irq_state s = irq_state (phantom_machine_state_' s') \<and>
  device_state s = device_state (phantom_machine_state_' s') \<and>
  \<comment> \<open>exclusive_state s = exclusive_state (phantom_machine_state_' s') \<and>\<close> \<comment> \<open>FIXME x64:this is needed for infoflow so we'll leave it commented\<close>
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
  map_to_pml4es :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> pml4e"
  where
  "map_to_pml4es hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

abbreviation
  map_to_pdptes :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> pdpte"
  where
  "map_to_pdptes hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

abbreviation
  map_to_pdes :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> machine_word \<rightharpoonup> pde"
  where
  "map_to_pdes hp \<equiv> projectKO_opt \<circ>\<^sub>m hp"

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

fun
  register_from_H :: "register \<Rightarrow> 32 word"
  where
    "register_from_H X64.RAX = scast Kernel_C.RAX"
  | "register_from_H X64.RBX = scast Kernel_C.RBX"
  | "register_from_H X64.RCX = scast Kernel_C.RCX"
  | "register_from_H X64.RDX = scast Kernel_C.RDX"
  | "register_from_H X64.RSI = scast Kernel_C.RSI"
  | "register_from_H X64.RDI = scast Kernel_C.RDI"
  | "register_from_H X64.RBP = scast Kernel_C.RBP"
  | "register_from_H X64.RSP = scast Kernel_C.RSP"
  | "register_from_H X64.R8 = scast Kernel_C.R8"
  | "register_from_H X64.R9 = scast Kernel_C.R9"
  | "register_from_H X64.R10 = scast Kernel_C.R10"
  | "register_from_H X64.R11 = scast Kernel_C.R11"
  | "register_from_H X64.R12 = scast Kernel_C.R12"
  | "register_from_H X64.R13 = scast Kernel_C.R13"
  | "register_from_H X64.R14 = scast Kernel_C.R14"
  | "register_from_H X64.R15 = scast Kernel_C.R15"
  | "register_from_H X64.FLAGS = scast Kernel_C.FLAGS"
  | "register_from_H X64.NextIP = scast Kernel_C.NextIP"
  | "register_from_H X64.FaultIP = scast Kernel_C.FaultIP"
  | "register_from_H X64.CS = scast Kernel_C.CS"
  | "register_from_H X64.SS = scast Kernel_C.SS"
  | "register_from_H X64.ErrorRegister = scast Kernel_C.Error"
  | "register_from_H X64.FS_BASE = scast Kernel_C.FS_BASE"
  | "register_from_H X64.GS_BASE = scast Kernel_C.GS_BASE"

definition
  cregs_relation :: "(MachineTypes.register \<Rightarrow> machine_word) \<Rightarrow> machine_word[24] \<Rightarrow> bool"
where
  "cregs_relation Hregs Cregs \<equiv>  \<forall>r. Hregs r = Cregs.[unat (register_from_H r)]"

definition
  fpu_relation :: "fpu_state \<Rightarrow> user_fpu_state_C \<Rightarrow> bool"
where
  "fpu_relation fpu_H fpu_C \<equiv> \<forall>r < CARD(fpu_bytes). fpu_H (finite_index r) = (state_C fpu_C).[r]"

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
      ccontext_relation (atcbContextGet aarch_tcb) (tcbContext_C carch_tcb)"

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

definition
  "superuser_from_vm_rights R \<equiv> case R of
    VMKernelOnly \<Rightarrow> 0
  | _ \<Rightarrow> 1"

definition
  "writable_from_vm_rights R \<equiv> case R of
    VMReadOnly \<Rightarrow> 0
  | _ \<Rightarrow> 1"

definition
  cpml4e_relation :: "pml4e \<Rightarrow> pml4e_C \<Rightarrow> bool"
where
  "cpml4e_relation pml4e cpml4e \<equiv>
  (let cpml4e' = pml4e_lift cpml4e in
  case pml4e of
    InvalidPML4E \<Rightarrow>
      (cpml4e' = \<lparr> pml4e_CL.xd_CL = 0,
       pml4e_CL.pdpt_base_address_CL = 0,
       pml4e_CL.accessed_CL = 0,
       pml4e_CL.cache_disabled_CL = 0,
       pml4e_CL.write_through_CL = 0,
       pml4e_CL.super_user_CL = 0,
       pml4e_CL.read_write_CL = 0,
       pml4e_CL.present_CL = 0\<rparr>)
  | PDPointerTablePML4E tab acc cd wt xd rights \<Rightarrow>
      (cpml4e' = \<lparr> pml4e_CL.xd_CL = of_bool xd,
       pml4e_CL.pdpt_base_address_CL = tab,
       pml4e_CL.accessed_CL = of_bool acc,
       pml4e_CL.cache_disabled_CL = of_bool cd,
       pml4e_CL.write_through_CL = of_bool wt,
       pml4e_CL.super_user_CL = superuser_from_vm_rights rights,
       pml4e_CL.read_write_CL = writable_from_vm_rights rights,
       pml4e_CL.present_CL = 1 \<rparr>)
  )"

definition
  cpdpte_relation :: "pdpte \<Rightarrow> pdpte_C \<Rightarrow> bool"
where
  "cpdpte_relation pdpte cpdpte \<equiv>
  (let cpdpte' = pdpte_lift cpdpte in
  case pdpte of
    InvalidPDPTE \<Rightarrow>
      (cpdpte' = Some (Pdpte_pdpte_pd \<lparr> pdpte_pdpte_pd_CL.xd_CL = 0,
       pdpte_pdpte_pd_CL.pd_base_address_CL = 0,
       pdpte_pdpte_pd_CL.accessed_CL = 0,
       pdpte_pdpte_pd_CL.cache_disabled_CL = 0,
       pdpte_pdpte_pd_CL.write_through_CL = 0,
       pdpte_pdpte_pd_CL.super_user_CL = 0,
       pdpte_pdpte_pd_CL.read_write_CL = 0,
       pdpte_pdpte_pd_CL.present_CL = 0\<rparr>))
  | PageDirectoryPDPTE tab acc cd wt xd rights \<Rightarrow>
      (cpdpte' = Some (Pdpte_pdpte_pd \<lparr> pdpte_pdpte_pd_CL.xd_CL = of_bool xd,
       pdpte_pdpte_pd_CL.pd_base_address_CL = tab,
       pdpte_pdpte_pd_CL.accessed_CL = of_bool acc,
       pdpte_pdpte_pd_CL.cache_disabled_CL = of_bool cd,
       pdpte_pdpte_pd_CL.write_through_CL = of_bool wt,
       pdpte_pdpte_pd_CL.super_user_CL = superuser_from_vm_rights rights,
       pdpte_pdpte_pd_CL.read_write_CL = writable_from_vm_rights rights,
       pdpte_pdpte_pd_CL.present_CL = 1 \<rparr>))
  | HugePagePDPTE frame glob pat dirty acc cd wt xd rights \<Rightarrow>
      (cpdpte' = Some (Pdpte_pdpte_1g \<lparr> pdpte_pdpte_1g_CL.xd_CL = of_bool xd,
       pdpte_pdpte_1g_CL.page_base_address_CL = frame,
       pdpte_pdpte_1g_CL.pat_CL = of_bool pat,
       pdpte_pdpte_1g_CL.global_CL = of_bool glob,
       pdpte_pdpte_1g_CL.dirty_CL = of_bool dirty,
       pdpte_pdpte_1g_CL.accessed_CL = of_bool acc,
       pdpte_pdpte_1g_CL.cache_disabled_CL = of_bool cd,
       pdpte_pdpte_1g_CL.write_through_CL = of_bool wt,
       pdpte_pdpte_1g_CL.super_user_CL = superuser_from_vm_rights rights,
       pdpte_pdpte_1g_CL.read_write_CL = writable_from_vm_rights rights,
       pdpte_pdpte_1g_CL.present_CL = 1 \<rparr>))
  )"

definition
  cpde_relation :: "pde \<Rightarrow> pde_C \<Rightarrow> bool"
where
  "cpde_relation pde cpde \<equiv>
  (let cpde' = pde_lift cpde in
  case pde of
    InvalidPDE \<Rightarrow>
      (cpde' =  Some (Pde_pde_pt \<lparr> pde_pde_pt_CL.xd_CL = 0,
       pde_pde_pt_CL.pt_base_address_CL = 0,
       pde_pde_pt_CL.accessed_CL = 0,
       pde_pde_pt_CL.cache_disabled_CL = 0,
       pde_pde_pt_CL.write_through_CL = 0,
       pde_pde_pt_CL.super_user_CL = 0,
       pde_pde_pt_CL.read_write_CL = 0,
       pde_pde_pt_CL.present_CL = 0\<rparr>))
  | PageTablePDE tab acc cd wt xd rights \<Rightarrow>
      (cpde' =  Some (Pde_pde_pt \<lparr> pde_pde_pt_CL.xd_CL = of_bool xd,
       pde_pde_pt_CL.pt_base_address_CL = tab,
       pde_pde_pt_CL.accessed_CL = of_bool acc,
       pde_pde_pt_CL.cache_disabled_CL = of_bool cd,
       pde_pde_pt_CL.write_through_CL = of_bool wt,
       pde_pde_pt_CL.super_user_CL = superuser_from_vm_rights rights,
       pde_pde_pt_CL.read_write_CL = writable_from_vm_rights rights,
       pde_pde_pt_CL.present_CL = 1 \<rparr>))
  | LargePagePDE frame glob pat dirty acc cd wt xd rights \<Rightarrow>
      (cpde' = Some (Pde_pde_large \<lparr> pde_pde_large_CL.xd_CL = of_bool xd,
       pde_pde_large_CL.page_base_address_CL = frame,
       pde_pde_large_CL.pat_CL = of_bool pat,
       pde_pde_large_CL.global_CL = of_bool glob,
       pde_pde_large_CL.dirty_CL = of_bool dirty,
       pde_pde_large_CL.accessed_CL = of_bool acc,
       pde_pde_large_CL.cache_disabled_CL = of_bool cd,
       pde_pde_large_CL.write_through_CL = of_bool wt,
       pde_pde_large_CL.super_user_CL = superuser_from_vm_rights rights,
       pde_pde_large_CL.read_write_CL = writable_from_vm_rights rights,
       pde_pde_large_CL.present_CL = 1 \<rparr>))
  )"

definition
  cpte_relation :: "pte \<Rightarrow> pte_C \<Rightarrow> bool"
where
  "cpte_relation pte cpte \<equiv>
  (let cpte' = pte_lift cpte in
  case pte of
    InvalidPTE \<Rightarrow>
      (cpte' =  \<lparr> pte_CL.xd_CL = 0,
       pte_CL.page_base_address_CL = 0,
       pte_CL.global_CL = 0,
       pte_CL.pat_CL = 0,
       pte_CL.dirty_CL = 0,
       pte_CL.accessed_CL = 0,
       pte_CL.cache_disabled_CL = 0,
       pte_CL.write_through_CL = 0,
       pte_CL.super_user_CL = 0,
       pte_CL.read_write_CL = 0,
       pte_CL.present_CL = 0\<rparr>)
  | SmallPagePTE frame global pat dirty acc cd wt xd rights \<Rightarrow>
    cpte' =  \<lparr> pte_CL.xd_CL = of_bool xd,
       pte_CL.page_base_address_CL = frame,
       pte_CL.global_CL = of_bool global,
       pte_CL.pat_CL = of_bool pat,
       pte_CL.dirty_CL = of_bool dirty,
       pte_CL.accessed_CL = of_bool acc,
       pte_CL.cache_disabled_CL = of_bool cd,
       pte_CL.write_through_CL = of_bool wt,
       pte_CL.super_user_CL = superuser_from_vm_rights rights,
       pte_CL.read_write_CL = writable_from_vm_rights rights,
       pte_CL.present_CL = 1 \<rparr>
  )"

(* Invalid PTEs map to invalid PTEs (sanity check?) *)
lemma pte_0:
  "index (pte_C.words_C cpte) 0 = 0 \<Longrightarrow>
   pte_lift cpte = \<lparr> pte_CL.xd_CL = 0,
       pte_CL.page_base_address_CL = 0,
       pte_CL.global_CL = 0,
       pte_CL.pat_CL = 0,
       pte_CL.dirty_CL = 0,
       pte_CL.accessed_CL = 0,
       pte_CL.cache_disabled_CL = 0,
       pte_CL.write_through_CL = 0,
       pte_CL.super_user_CL = 0,
       pte_CL.read_write_CL = 0,
       pte_CL.present_CL = 0\<rparr>"
  by (simp add: pte_lift_def)

lemma pde_0:
  "index (pde_C.words_C cpde) 0 = 0 \<Longrightarrow>
   pde_lift cpde = Some (Pde_pde_pt \<lparr> pde_pde_pt_CL.xd_CL = 0,
       pde_pde_pt_CL.pt_base_address_CL = 0,
       pde_pde_pt_CL.accessed_CL = 0,
       pde_pde_pt_CL.cache_disabled_CL = 0,
       pde_pde_pt_CL.write_through_CL = 0,
       pde_pde_pt_CL.super_user_CL = 0,
       pde_pde_pt_CL.read_write_CL = 0,
       pde_pde_pt_CL.present_CL = 0\<rparr>)"
  by (simp add: pde_lift_def pde_get_tag_def pde_pde_pt_def)

lemma pdpte_0:
  "index (pdpte_C.words_C cpdpte) 0 = 0 \<Longrightarrow>
   pdpte_lift cpdpte = Some (Pdpte_pdpte_pd \<lparr> pdpte_pdpte_pd_CL.xd_CL = 0,
       pdpte_pdpte_pd_CL.pd_base_address_CL = 0,
       pdpte_pdpte_pd_CL.accessed_CL = 0,
       pdpte_pdpte_pd_CL.cache_disabled_CL = 0,
       pdpte_pdpte_pd_CL.write_through_CL = 0,
       pdpte_pdpte_pd_CL.super_user_CL = 0,
       pdpte_pdpte_pd_CL.read_write_CL = 0,
       pdpte_pdpte_pd_CL.present_CL = 0\<rparr>)"
  by (simp add: pdpte_lift_def pdpte_get_tag_def pdpte_pdpte_pd_def pdpte_pdpte_1g_def)

lemma pml4e_0:
  "index (pml4e_C.words_C cpml4e) 0 = 0 \<Longrightarrow>
   pml4e_lift cpml4e =  \<lparr> pml4e_CL.xd_CL = 0,
       pml4e_CL.pdpt_base_address_CL = 0,
       pml4e_CL.accessed_CL = 0,
       pml4e_CL.cache_disabled_CL = 0,
       pml4e_CL.write_through_CL = 0,
       pml4e_CL.super_user_CL = 0,
       pml4e_CL.read_write_CL = 0,
       pml4e_CL.present_CL = 0\<rparr>"
  by (simp add: pml4e_lift_def)

definition
  option_to_asid_map_CL :: "machine_word option \<Rightarrow> asid_map_CL"
where
  "option_to_asid_map_CL opt \<equiv> case opt of None \<Rightarrow> Asid_map_asid_map_none
                                | Some vspace \<Rightarrow> Asid_map_asid_map_vspace \<lparr> vspace_root_CL = vspace\<rparr>"

definition
  asid_map_relation :: "machine_word option \<Rightarrow> asid_map_C \<Rightarrow> bool"
where
  "asid_map_relation pml4ptr casid_map \<equiv>
    case (asid_map_lift casid_map) of
        None \<Rightarrow> False \<comment> \<open>should never happen\<close>
      | Some Asid_map_asid_map_none \<Rightarrow> pml4ptr = None
      | Some (Asid_map_asid_map_vspace vspace_root) \<Rightarrow> pml4ptr = Some (vspace_root_CL vspace_root)"


definition
  casid_pool_relation :: "asidpool \<Rightarrow> asid_pool_C \<Rightarrow> bool"
where
  "casid_pool_relation asid_pool casid_pool \<equiv>
  case asid_pool of ASIDPool pool \<Rightarrow>
  case casid_pool of asid_pool_C.asid_pool_C cpool \<Rightarrow>
  array_relation asid_map_relation (2^asid_low_bits - 1) pool cpool"


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
  "cpspace_pml4e_relation ah ch \<equiv> cmap_relation (map_to_pml4es ah) (clift ch) Ptr cpml4e_relation"

abbreviation
  "cpspace_pdpte_relation ah ch \<equiv> cmap_relation (map_to_pdptes ah) (clift ch) Ptr cpdpte_relation"

abbreviation
  "cpspace_pde_relation ah ch \<equiv> cmap_relation (map_to_pdes ah) (clift ch) Ptr cpde_relation"

abbreviation
  "cpspace_pte_relation ah ch \<equiv> cmap_relation (map_to_ptes ah) (clift ch) Ptr cpte_relation"

abbreviation
  "cpspace_asidpool_relation ah ch \<equiv> cmap_relation (map_to_asidpools ah) (clift ch) Ptr casid_pool_relation"

abbreviation
  "cpspace_user_data_relation ah bh ch \<equiv> cmap_relation (heap_to_user_data ah bh) (clift ch) Ptr cuser_user_data_relation"

abbreviation
  "cpspace_device_data_relation ah bh ch \<equiv> cmap_relation (heap_to_device_data ah bh) (clift ch) Ptr cuser_user_data_device_relation"

abbreviation
  "cpspace_pdpte_array_relation ah ch \<equiv> carray_map_relation pdptBits (map_to_pdptes ah) (h_t_valid (hrs_htd ch) c_guard) pdpt_Ptr"

abbreviation
  "cpspace_pml4e_array_relation ah ch \<equiv> carray_map_relation pml4Bits (map_to_pml4es ah) (h_t_valid (hrs_htd ch) c_guard) pml4_Ptr"

abbreviation
  "cpspace_pde_array_relation ah ch \<equiv> carray_map_relation pdBits (map_to_pdes ah) (h_t_valid (hrs_htd ch) c_guard) pd_Ptr"

abbreviation
  "cpspace_pte_array_relation ah ch \<equiv> carray_map_relation ptBits (map_to_ptes ah) (h_t_valid (hrs_htd ch) c_guard) pt_Ptr"


definition
  cpspace_relation :: "(machine_word \<rightharpoonup> Structures_H.kernel_object) \<Rightarrow> (machine_word \<Rightarrow> word8) \<Rightarrow> heap_raw_state \<Rightarrow> bool"
where
  "cpspace_relation ah bh ch \<equiv>
  cpspace_cte_relation ah ch \<and> cpspace_tcb_relation ah ch \<and> cpspace_ep_relation ah ch \<and> cpspace_ntfn_relation ah ch \<and>
  cpspace_pde_relation ah ch \<and> cpspace_pte_relation ah ch \<and> cpspace_pdpte_relation ah ch \<and>
  cpspace_pml4e_relation ah ch \<and> cpspace_asidpool_relation ah ch \<and>
  cpspace_user_data_relation ah bh ch \<and> cpspace_device_data_relation ah bh ch \<and>
  cpspace_pdpte_array_relation ah ch \<and> cpspace_pml4e_array_relation ah ch \<and>
  cpspace_pde_array_relation ah ch \<and> cpspace_pte_array_relation ah ch"

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

end (* interpretation Arch . (*FIXME: arch-split*) *)

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

value_type intState_array_size = "2^LENGTH(irq_len) :: nat"

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
       apsnd fst (ghost'state_' cstate) = (gsUserPages astate, gsCNodes astate) \<and>
       ghost_size_rel (ghost'state_' cstate) (gsMaxObjectSize astate) \<and>
       ksWorkUnitsCompleted_' cstate = ksWorkUnitsCompleted astate \<and>
       h_t_valid (hrs_htd (t_hrs_' cstate)) c_guard intStateIRQNode_array_Ptr \<and>
       ptr_span intStateIRQNode_array_Ptr \<subseteq> kernel_data_refs \<and>
       h_t_valid (hrs_htd (t_hrs_' cstate)) c_guard x64KSSKIMPML4_Ptr \<and>
       ptr_span x64KSSKIMPML4_Ptr \<subseteq> kernel_data_refs \<and>
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

lemma (in kernel) syscall_error_to_H_cases_rev:
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

lemma (in kernel) cmap_relation_cs_atD:
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

definition (in kernel)
  rf_sr :: "(KernelStateData_H.kernel_state \<times> cstate) set"
  where
  "rf_sr \<equiv> {(s, s'). cstate_relation s (globals s')}"

end
