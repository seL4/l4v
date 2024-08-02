(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Higher level functions for manipulating virtual address spaces
*)

chapter "ARM VSpace Functions"

theory ArchVSpace_A
imports
  Retype_A
  ArchTcb_A
begin

context Arch begin global_naming ARM_HYP_A

text \<open>Save the set of entries that would be inserted into a page table or
page directory to map various different sizes of frame at a given virtual
address.\<close>

definition largePagePTE_offsets :: "obj_ref list"
  where
  "largePagePTE_offsets \<equiv>
    let pts = of_nat pte_bits
    in [0, 2 ^ pts  .e.  (15 << pte_bits)]"

definition superSectionPDE_offsets :: "obj_ref list"
  where
  "superSectionPDE_offsets \<equiv>
    let pts = of_nat pde_bits
    in [0, 2 ^ pts  .e.  (15 << pde_bits)]"

fun create_mapping_entries ::
  "paddr \<Rightarrow> vspace_ref \<Rightarrow> vmpage_size \<Rightarrow> vm_rights \<Rightarrow> vm_attributes \<Rightarrow> word32 \<Rightarrow>
  ((pte * word32 list) + (pde * word32 list),'z::state_ext) se_monad"
where
  "create_mapping_entries base vptr ARMSmallPage vm_rights attrib pd =
  doE
    p \<leftarrow> lookup_error_on_failure False $ lookup_pt_slot pd vptr;
    returnOk $ Inl (SmallPagePTE base attrib vm_rights, [p])
  odE"

| "create_mapping_entries base vptr ARMLargePage vm_rights attrib pd =
  doE
    p \<leftarrow> lookup_error_on_failure False $ lookup_pt_slot pd vptr;
    returnOk $ Inl (LargePagePTE base attrib vm_rights, map (\<lambda>x. x + p) largePagePTE_offsets)
  odE"

| "create_mapping_entries base vptr ARMSection vm_rights attrib pd =
  doE
    p \<leftarrow> returnOk (lookup_pd_slot pd vptr);
    returnOk $ Inr (SectionPDE base attrib vm_rights, [p])
  odE"

| "create_mapping_entries base vptr ARMSuperSection vm_rights attrib pd =
  doE
    p \<leftarrow> returnOk (lookup_pd_slot pd vptr);
    returnOk $ Inr (SuperSectionPDE base attrib vm_rights, map (\<lambda>x. x + p) superSectionPDE_offsets)
  odE"

definition get_master_pde :: "word32 \<Rightarrow> (pde,'z::state_ext)s_monad"
  where "get_master_pde ptr \<equiv> do
    pde \<leftarrow> (get_pde (ptr && ~~ mask 7));
    (case pde of SuperSectionPDE _ _ _ \<Rightarrow> return pde
    | _ \<Rightarrow> get_pde ptr)
  od"

definition get_master_pte :: "word32 \<Rightarrow> (pte, 'z::state_ext)s_monad"
  where "get_master_pte ptr \<equiv> do
    pte \<leftarrow> (get_pte (ptr && ~~ mask 7));
    (case pte of LargePagePTE _ _ _ \<Rightarrow> return pte
    | _ \<Rightarrow> get_pte ptr)
  od"

text \<open>Placing an entry which maps a frame within the set of entries that map a
larger frame is unsafe. This function checks that given entries replace either
invalid entries or entries of the same granularity.\<close>
fun ensure_safe_mapping ::
  "(pte * word32 list) + (pde * word32 list) \<Rightarrow> (unit,'z::state_ext) se_monad"
where
"ensure_safe_mapping (Inl (InvalidPTE, _)) = returnOk ()"
|
"ensure_safe_mapping (Inl (SmallPagePTE _ _ _, pt_slots)) =
    mapME_x (\<lambda>slot. (doE
        pte \<leftarrow> liftE $ get_master_pte slot;
        (case pte of
              InvalidPTE \<Rightarrow> returnOk ()
            | SmallPagePTE _ _ _ \<Rightarrow> returnOk ()
            | _ \<Rightarrow> throwError DeleteFirst)
    odE)) pt_slots"
|
"ensure_safe_mapping (Inl (LargePagePTE _ _ _, pt_slots)) =
    mapME_x (\<lambda> slot. (doE
        pte \<leftarrow> liftE $ get_master_pte slot;
        (case pte of
              InvalidPTE \<Rightarrow> returnOk ()
            | LargePagePTE _ _ _ \<Rightarrow> returnOk ()
            | _ \<Rightarrow> throwError DeleteFirst
            )
    odE)) pt_slots"
|
"ensure_safe_mapping (Inr (InvalidPDE, _)) = returnOk ()"
|
"ensure_safe_mapping (Inr (PageTablePDE _, _)) = fail"
|
"ensure_safe_mapping (Inr (SectionPDE _ _ _, pd_slots)) =
    mapME_x (\<lambda> slot. (doE
        pde \<leftarrow> liftE $ get_master_pde slot;
        (case pde of
              InvalidPDE \<Rightarrow> returnOk ()
            | SectionPDE _ _ _ \<Rightarrow> returnOk ()
            | _ \<Rightarrow> throwError DeleteFirst
            )
    odE)) pd_slots"
|
"ensure_safe_mapping (Inr (SuperSectionPDE _ _ _, pd_slots)) =
    mapME_x (\<lambda> slot. (doE
        pde \<leftarrow> liftE $ get_master_pde slot;
        (case pde of
              InvalidPDE \<Rightarrow> returnOk ()
            | SuperSectionPDE _ _ _ \<Rightarrow> returnOk ()
            | _ \<Rightarrow> throwError DeleteFirst
            )
    odE)) pd_slots"

text \<open>Look up a thread's IPC buffer and check that the thread has the right
authority to read or (in the receiver case) write to it.\<close>
definition
lookup_ipc_buffer :: "bool \<Rightarrow> word32 \<Rightarrow> (word32 option,'z::state_ext) s_monad" where
"lookup_ipc_buffer is_receiver thread \<equiv> do
    buffer_ptr \<leftarrow> thread_get tcb_ipc_buffer thread;
    buffer_frame_slot \<leftarrow> return (thread, tcb_cnode_index 4);
    buffer_cap \<leftarrow> get_cap buffer_frame_slot;
    (case buffer_cap of
      ArchObjectCap (PageCap _ p R vms _) \<Rightarrow>
        if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
        then return $ Some $ p + (buffer_ptr && mask (pageBitsForSize vms))
        else return None
    | _ \<Rightarrow> return None)
od"

text \<open>Locate the page directory associated with a given virtual ASID.\<close>
definition
find_pd_for_asid :: "asid \<Rightarrow> (word32,'z::state_ext) lf_monad" where
"find_pd_for_asid asid \<equiv> doE
    assertE (asid > 0);
    asid_table \<leftarrow> liftE $ gets (arm_asid_table \<circ> arch_state);
    pool_ptr \<leftarrow> returnOk (asid_table (asid_high_bits_of asid));
    pool \<leftarrow> (case pool_ptr of
               Some ptr \<Rightarrow> liftE $ get_asid_pool ptr
             | None \<Rightarrow> throwError InvalidRoot);
    pd \<leftarrow> returnOk (pool (ucast asid));
    (case pd of
          Some ptr \<Rightarrow> returnOk ptr
        | None \<Rightarrow> throwError InvalidRoot)
odE"

text \<open>Locate the page directory and check that this process succeeds and
returns a pointer to a real page directory.\<close>
definition
find_pd_for_asid_assert :: "asid \<Rightarrow> (word32,'z::state_ext) s_monad" where
"find_pd_for_asid_assert asid \<equiv> do
   pd \<leftarrow> find_pd_for_asid asid <catch> K fail;
   get_pde pd;
   return pd
 od"

text \<open>Format a VM fault message to be passed to a thread's supervisor after
it encounters a page fault.\<close>
fun
handle_vm_fault :: "word32 \<Rightarrow> vmfault_type \<Rightarrow> (unit,'z::state_ext) f_monad"
where
"handle_vm_fault thread ARMDataAbort = doE
    addr \<leftarrow> liftE $ do_machine_op getHDFAR;
    uaddr \<leftarrow> liftE $ do_machine_op (addressTranslateS1 addr);
    fault \<leftarrow> liftE $ do_machine_op getHSR;
    let faddr = (uaddr && complement (mask pageBits)) || (addr && mask pageBits)
    in
    throwError $ ArchFault $ VMFault faddr [0, fault && 0x3ffffff]
odE"
|
"handle_vm_fault thread ARMPrefetchAbort = doE
    pc \<leftarrow> liftE $ as_user thread $ getRestartPC;
    upc \<leftarrow> liftE $ do_machine_op (addressTranslateS1 pc);
    fault \<leftarrow> liftE $ do_machine_op getHSR;
    let faddr = (upc && complement (mask pageBits)) || (pc && mask pageBits)
    in
    throwError $ ArchFault $ VMFault faddr [1, fault && 0x3ffffff]
odE"

text \<open>Load the optional hardware ASID currently associated with this virtual
ASID.\<close>
definition
load_hw_asid :: "asid \<Rightarrow> (hardware_asid option,'z::state_ext) s_monad" where
"load_hw_asid asid \<equiv> do
    asid_map \<leftarrow> gets (arm_asid_map \<circ> arch_state);
    return $ option_map fst $ asid_map asid
od"

text \<open>Associate a hardware ASID with a virtual ASID.\<close>
definition
store_hw_asid :: "asid \<Rightarrow> hardware_asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"store_hw_asid asid hw_asid \<equiv> do
    pd \<leftarrow> find_pd_for_asid_assert asid;
    asid_map \<leftarrow> gets (arm_asid_map \<circ> arch_state);
    asid_map' \<leftarrow> return (asid_map (asid \<mapsto> (hw_asid, pd)));
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_asid_map := asid_map' \<rparr>\<rparr>);
    hw_asid_map \<leftarrow> gets (arm_hwasid_table \<circ> arch_state);
    hw_asid_map' \<leftarrow> return (hw_asid_map (hw_asid \<mapsto> asid));
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_hwasid_table := hw_asid_map' \<rparr>\<rparr>)
od"

text \<open>Clear all TLB mappings associated with this virtual ASID.\<close>
definition
invalidate_tlb_by_asid :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"invalidate_tlb_by_asid asid \<equiv> do
    maybe_hw_asid \<leftarrow> load_hw_asid asid;
    (case maybe_hw_asid of
          None \<Rightarrow> return ()
        | Some hw_asid \<Rightarrow> do_machine_op $ invalidateLocalTLB_ASID hw_asid)
od"

text \<open>Flush all cache and TLB entries associated with this virtual ASID.\<close>
definition
flush_space :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"flush_space asid \<equiv> do
    maybe_hw_asid \<leftarrow> load_hw_asid asid;
    do_machine_op cleanCaches_PoU;
    (case maybe_hw_asid of
          None \<Rightarrow> return ()
        | Some hw_asid \<Rightarrow> do_machine_op $ invalidateLocalTLB_ASID hw_asid)
od"

text \<open>Remove any mapping from this virtual ASID to a hardware ASID.\<close>
definition
invalidate_asid :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"invalidate_asid asid \<equiv> do
    asid_map \<leftarrow> gets (arm_asid_map \<circ> arch_state);
    asid_map' \<leftarrow> return (asid_map (asid:= None));
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_asid_map := asid_map' \<rparr>\<rparr>)
od"

text \<open>Remove any mapping from this hardware ASID to a virtual ASID.\<close>
definition
invalidate_hw_asid_entry :: "hardware_asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"invalidate_hw_asid_entry hw_asid \<equiv> do
  hw_asid_map \<leftarrow> gets (arm_hwasid_table \<circ> arch_state);
  hw_asid_map' \<leftarrow> return (hw_asid_map (hw_asid:= None));
  modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_hwasid_table := hw_asid_map' \<rparr>\<rparr>)
od"

text \<open>Remove virtual to physical mappings in either direction involving this
virtual ASID.\<close>
definition
invalidate_asid_entry :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
"invalidate_asid_entry asid \<equiv> do
  maybe_hw_asid \<leftarrow> load_hw_asid asid;
  when (maybe_hw_asid \<noteq> None) $ invalidate_hw_asid_entry (the maybe_hw_asid);
  invalidate_asid asid
od"

text \<open>Locate a hardware ASID that is not in use, if necessary by reclaiming
one from another virtual ASID in a round-robin manner.\<close>
definition
find_free_hw_asid :: "(hardware_asid,'z::state_ext) s_monad" where
"find_free_hw_asid \<equiv> do
    hw_asid_table \<leftarrow> gets (arm_hwasid_table \<circ> arch_state);
    next_asid \<leftarrow> gets (arm_next_asid \<circ> arch_state);
    maybe_asid \<leftarrow> return (find (\<lambda>a. hw_asid_table a = None)
                    (take (length [minBound :: hardware_asid .e. maxBound])
                        ([next_asid .e. maxBound] @ [minBound .e. next_asid])));
    (case maybe_asid of
       Some hw_asid \<Rightarrow> return hw_asid
     | None \<Rightarrow>  do
            invalidate_asid $ the $ hw_asid_table next_asid;
            do_machine_op $ invalidateLocalTLB_ASID next_asid;
            invalidate_hw_asid_entry next_asid;
            new_next_asid \<leftarrow> return (next_asid + 1);
            modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_next_asid := new_next_asid \<rparr>\<rparr>);
            return next_asid
       od)
od"

text \<open>Get the hardware ASID associated with a virtual ASID, assigning one if
none is already assigned.\<close>
definition
get_hw_asid :: "asid \<Rightarrow> (hardware_asid,'z::state_ext) s_monad" where
"get_hw_asid asid \<equiv> do
  maybe_hw_asid \<leftarrow> load_hw_asid asid;
  (case maybe_hw_asid of
    Some hw_asid \<Rightarrow> return hw_asid
  | None \<Rightarrow>  do
      new_hw_asid \<leftarrow> find_free_hw_asid;
      store_hw_asid asid new_hw_asid;
      return new_hw_asid
  od)
od"


abbreviation
  "arm_context_switch_hwasid pd hwasid \<equiv> writeContextIDAndPD hwasid (addrFromPPtr pd)"

definition
  arm_context_switch :: "word32 \<Rightarrow> asid \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "arm_context_switch pd asid \<equiv> do
    hwasid \<leftarrow> get_hw_asid asid;
    do_machine_op $ arm_context_switch_hwasid pd hwasid
   od"

text \<open>Manipulation of VCPU-related state and registers\<close>

definition
  vcpu_update :: "obj_ref \<Rightarrow> (vcpu \<Rightarrow> vcpu) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_update vr f \<equiv> do
    vcpu \<leftarrow> get_vcpu vr;
    set_vcpu vr (f vcpu)
  od"

definition
  vgic_update :: "obj_ref \<Rightarrow> (gic_vcpu_interface \<Rightarrow> gic_vcpu_interface) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vgic_update vr f \<equiv> vcpu_update vr (\<lambda>vcpu. vcpu \<lparr> vcpu_vgic := f (vcpu_vgic vcpu) \<rparr> )"

definition
  vgic_update_lr :: "obj_ref \<Rightarrow> nat \<Rightarrow> virq \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vgic_update_lr vr irq_idx virq \<equiv>
    vgic_update vr (\<lambda>vgic. vgic \<lparr> vgic_lr := (vgic_lr vgic)(irq_idx := virq) \<rparr>)"

definition
  vcpu_save_reg :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_save_reg vr reg \<equiv> do
    rval \<leftarrow> do_machine_op (readVCPUHardwareReg reg);
    vcpu_update vr (\<lambda>vcpu. vcpu \<lparr> vcpu_regs := (vcpu_regs vcpu)(reg := rval) \<rparr> )
  od"

definition
  vcpu_save_reg_range :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> vcpureg \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_save_reg_range vr from to \<equiv> mapM_x (\<lambda>reg. vcpu_save_reg vr reg) [from .e. to]"

definition
  vcpu_restore_reg :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_restore_reg vr reg \<equiv> do
    vcpu \<leftarrow> get_vcpu vr;
    do_machine_op (writeVCPUHardwareReg reg (vcpu_regs vcpu reg))
  od"

definition
  vcpu_restore_reg_range :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> vcpureg \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_restore_reg_range vr from to \<equiv> mapM_x (\<lambda>reg. vcpu_restore_reg vr reg) [from .e. to]"

definition
  vcpu_read_reg :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> (machine_word, 'z::state_ext) s_monad"
where
  "vcpu_read_reg vr reg \<equiv> do
    vcpu \<leftarrow> get_vcpu vr;
    return (vcpu_regs vcpu reg)
  od"

definition
  vcpu_write_reg :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_write_reg vr reg val \<equiv>
    vcpu_update vr (\<lambda>vcpu. vcpu \<lparr> vcpu_regs := (vcpu_regs vcpu)(reg := val) \<rparr> )"

definition save_virt_timer :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "save_virt_timer vcpu_ptr \<equiv> do
     vcpu_save_reg vcpu_ptr VCPURegCNTV_CTL;
     do_machine_op $ writeVCPUHardwareReg VCPURegCNTV_CTL 0;
     cval \<leftarrow> do_machine_op get_cntv_cval_64;
     cntvoff \<leftarrow> do_machine_op get_cntv_off_64;
     vcpu_write_reg vcpu_ptr VCPURegCNTV_CVALhigh (ucast (cval >> 32));
     vcpu_write_reg vcpu_ptr VCPURegCNTV_CVALlow (ucast cval);
     vcpu_write_reg vcpu_ptr VCPURegCNTVOFFhigh (ucast (cntvoff >> 32));
     vcpu_write_reg vcpu_ptr VCPURegCNTVOFFlow (ucast cntvoff);
     cntpct \<leftarrow> do_machine_op read_cntpct;
     vcpu_update vcpu_ptr (\<lambda>vcpu. vcpu\<lparr>vcpu_vtimer := VirtTimer cntpct \<rparr>)
   od"

definition irq_vppi_event_index :: "irq \<rightharpoonup> vppievent_irq" where
  "irq_vppi_event_index irq \<equiv>
     if irq = irqVTimerEvent
     then Some VPPIEventIRQ_VTimer
     else None"

definition restore_virt_timer :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "restore_virt_timer vcpu_ptr \<equiv> do
     cval_high \<leftarrow> vcpu_read_reg vcpu_ptr VCPURegCNTV_CVALhigh;
     cval_low \<leftarrow> vcpu_read_reg vcpu_ptr VCPURegCNTV_CVALlow;
     (cval :: 64 word) \<leftarrow> return $ ((ucast cval_high) << 32) || ucast cval_low;
     do_machine_op $ set_cntv_cval_64 cval;
     current_cntpct \<leftarrow> do_machine_op read_cntpct;
     vcpu \<leftarrow> get_vcpu vcpu_ptr;
     last_pcount \<leftarrow> return $ vtimerLastPCount $ vcpu_vtimer vcpu;
     delta \<leftarrow> return $ current_cntpct - last_pcount;
     offs_high \<leftarrow> vcpu_read_reg vcpu_ptr VCPURegCNTVOFFhigh;
     offs_low \<leftarrow> vcpu_read_reg vcpu_ptr VCPURegCNTVOFFlow;
     (offset :: 64 word) \<leftarrow> return $ (((ucast offs_high) << 32) || ucast offs_low) + delta;
     vcpu_write_reg vcpu_ptr VCPURegCNTVOFFhigh (ucast (offset >> 32));
     vcpu_write_reg vcpu_ptr VCPURegCNTVOFFlow (ucast offset);
     do_machine_op $ set_cntv_off_64 offset;
     masked \<leftarrow> return $ (vcpu_vppi_masked vcpu (the $ irq_vppi_event_index irqVTimerEvent));
     \<comment> \<open>we do not know here that irqVTimerEvent is IRQReserved, therefore not IRQInactive,
        so the only way to prove we don't unmask an inactive interrupt is to check\<close>
     safe_to_unmask \<leftarrow> is_irq_active irqVTimerEvent;
     when safe_to_unmask $ do_machine_op $ maskInterrupt masked irqVTimerEvent;
     vcpu_restore_reg vcpu_ptr VCPURegCNTV_CTL
   od"

text \<open>Turn VPCU mode off on the hardware level.\<close>
definition
  vcpu_disable :: "obj_ref option \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_disable vo \<equiv> do
    do_machine_op dsb;
    (case vo of
      Some vr \<Rightarrow> do
        hcr \<leftarrow> do_machine_op get_gic_vcpu_ctrl_hcr;
        vgic_update vr (\<lambda>vgic. vgic\<lparr> vgic_hcr := hcr \<rparr>);
        vcpu_save_reg vr VCPURegSCTLR;
        do_machine_op isb
      od
    | _ \<Rightarrow> return ());
    do_machine_op $ do
        set_gic_vcpu_ctrl_hcr 0; \<comment> \<open>turn VGIC off\<close>
        isb;
        setSCTLR sctlrDefault; \<comment> \<open>turn SI MMU off\<close>
        setHCR hcrNative;
        isb
      od;
    case vo of
      Some vr \<Rightarrow> do
          save_virt_timer vr;
          do_machine_op $ maskInterrupt True irqVTimerEvent
        od
      | _ \<Rightarrow> return ()
    od"

text \<open>Turn VCPU mode on, on the hardware level.\<close>
definition
  vcpu_enable :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_enable vr \<equiv> do
     vcpu_restore_reg vr VCPURegSCTLR;
     vcpu \<leftarrow> get_vcpu vr;
     do_machine_op $ do
        setHCR hcrVCPU;
        isb;
        set_gic_vcpu_ctrl_hcr (vgic_hcr $ vcpu_vgic vcpu)
     od;
     restore_virt_timer vr
   od"

text \<open>
  Prepare the current VCPU for removal.
\<close>
definition
  vcpu_invalidate_active :: "(unit,'z::state_ext) s_monad"
where
  "vcpu_invalidate_active \<equiv> do
    cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
    case cur_v of
      Some (vr, True) \<Rightarrow> vcpu_disable None
    | _ \<Rightarrow> return ();
    modify (\<lambda>s. s\<lparr> arch_state := (arch_state s)\<lparr> arm_current_vcpu := None \<rparr>\<rparr>)
  od"

text \<open>VCPU objects can be associated with and dissociated from TCBs.\<close>
(* ARMHYP: maybe these vcpu related definitions can go into a separate file? *)

text \<open>Removing the connection between a TCB and VCPU:\<close>
definition dissociate_vcpu_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where "dissociate_vcpu_tcb vr t \<equiv> do
  t_vcpu \<leftarrow> arch_thread_get tcb_vcpu t;
  v \<leftarrow> get_vcpu vr;
  assert (t_vcpu = Some vr \<and> vcpu_tcb v = Some t); \<comment> \<open>make sure they were associated\<close>
  cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
  when (\<exists>a. cur_v = Some (vr,a)) vcpu_invalidate_active;
  arch_thread_set (\<lambda>x. x \<lparr> tcb_vcpu := None \<rparr>) t;
  set_vcpu vr (v\<lparr> vcpu_tcb := None \<rparr>);
  as_user t $ do
    cpsr \<leftarrow> getRegister CPSR;
    setRegister CPSR $ sanitise_register False CPSR cpsr
  od
od"

text \<open>Register + context save for VCPUs\<close>

definition
  vcpu_save :: "(obj_ref \<times> bool) option \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_save vb \<equiv>
     case vb
     of Some (vr, active) \<Rightarrow> do
          do_machine_op dsb;

          when active $ do
            vcpu_save_reg vr VCPURegSCTLR;
            hcr \<leftarrow> do_machine_op get_gic_vcpu_ctrl_hcr;
            vgic_update vr (\<lambda>vgic. vgic\<lparr> vgic_hcr := hcr \<rparr>);
            save_virt_timer vr
          od;

          vmcr \<leftarrow> do_machine_op get_gic_vcpu_ctrl_vmcr;
          vgic_update vr (\<lambda>vgic. vgic \<lparr>vgic_vmcr := vmcr\<rparr>);

          apr \<leftarrow> do_machine_op get_gic_vcpu_ctrl_apr;
          vgic_update vr (\<lambda>vgic. vgic \<lparr>vgic_apr := apr\<rparr>);

          num_list_regs \<leftarrow> gets (arm_gicvcpu_numlistregs \<circ> arch_state);
          gicIndices \<leftarrow> return [0..<num_list_regs];

          mapM (\<lambda>vreg. do
                    val \<leftarrow> do_machine_op $ get_gic_vcpu_ctrl_lr (of_nat vreg);
                    vgic_update_lr vr vreg val
                  od)
            gicIndices;

          vcpu_save_reg_range vr VCPURegACTLR VCPURegSPSRfiq;
          do_machine_op isb
       od
     | _ \<Rightarrow> fail"

text \<open>Register + context restore for VCPUs\<close>
definition
  vcpu_restore :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_restore vr \<equiv> do
     do_machine_op $ set_gic_vcpu_ctrl_hcr 0;  \<comment> \<open>turn off VGIC\<close>
     do_machine_op $ isb;
     vcpu \<leftarrow> get_vcpu vr;  \<comment> \<open>restore GIC VCPU control state\<close>
     vgic \<leftarrow> return (vcpu_vgic vcpu);
     num_list_regs \<leftarrow> gets (arm_gicvcpu_numlistregs \<circ> arch_state);
     gicIndices \<leftarrow> return [0..<num_list_regs];
     do_machine_op $ do
         set_gic_vcpu_ctrl_vmcr (vgic_vmcr vgic);
         set_gic_vcpu_ctrl_apr (vgic_apr vgic);
         mapM (\<lambda>p. set_gic_vcpu_ctrl_lr (of_nat (fst p)) (snd p))
              (map (\<lambda>i. (i, (vgic_lr vgic) i)) gicIndices)
     od;
    \<comment> \<open>restore banked VCPU registers except SCTLR (that's in VCPUEnable)\<close>
     vcpu_restore_reg_range vr VCPURegACTLR VCPURegSPSRfiq;
     vcpu_enable vr
  od"


text \<open>
  Make a new VCPU the active/current VCPU. If passed None, will mark the current VCPU as
  not active, and disable VCPU mode, but leave the rest intact caching for the case where
  we switch back to the same VCPU soon.
\<close>
definition vcpu_switch :: "obj_ref option \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_switch v \<equiv> case v of
   None \<Rightarrow> do
     cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
     (case cur_v of
        None \<Rightarrow> return () \<comment> \<open>both null, current cannot be active\<close>
      | Some (vr, active) \<Rightarrow> do \<comment> \<open>switch to thread without vcpu\<close>
          when active $ do  \<comment> \<open> save state if not saved already\<close>
            vcpu_disable (Some vr);
            modify (\<lambda>s. s\<lparr> arch_state := (arch_state s)\<lparr> arm_current_vcpu := Some (vr, False) \<rparr>\<rparr>)
          od;
          return ()
        od)
     od
 | Some new \<Rightarrow> do
     cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
     (case cur_v of
        None \<Rightarrow> do \<comment> \<open>switch to the new vcpu with no current one\<close>
          vcpu_restore new;
          modify (\<lambda>s. s\<lparr> arch_state := (arch_state s)\<lparr> arm_current_vcpu := Some (new, True) \<rparr>\<rparr>)
        od
      | Some (vr, active) \<Rightarrow> \<comment> \<open>switch from an existing vcpu\<close>
          (if vr \<noteq> new
          then do \<comment> \<open>different vcpu\<close>
            vcpu_save cur_v;
            vcpu_restore new;
            modify (\<lambda>s. s\<lparr> arch_state := (arch_state s)\<lparr> arm_current_vcpu := Some (new, True) \<rparr>\<rparr>)
          od
          else \<comment> \<open>same vcpu\<close>
            when (\<not> active) $ do
              do_machine_op isb;
              vcpu_enable new;
              modify (\<lambda>s. s\<lparr> arch_state := (arch_state s)\<lparr> arm_current_vcpu := Some (new, True) \<rparr>\<rparr>)
            od))
   od"

text \<open>Associating a TCB and VCPU, removing any potentially existing associations:\<close>
definition associate_vcpu_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "associate_vcpu_tcb vr t \<equiv> do
    t_vcpu \<leftarrow> arch_thread_get tcb_vcpu t;
    case t_vcpu of Some p \<Rightarrow> dissociate_vcpu_tcb p t
                 | _ \<Rightarrow> return ();
    v \<leftarrow> get_vcpu vr;
    case vcpu_tcb v of Some p \<Rightarrow> dissociate_vcpu_tcb vr p
                     | _ \<Rightarrow> return ();
    arch_thread_set (\<lambda>x. x \<lparr> tcb_vcpu := Some vr \<rparr>) t;
    set_vcpu vr (v\<lparr> vcpu_tcb := Some t \<rparr>);
    ct \<leftarrow> gets cur_thread;
    when (t = ct) $ vcpu_switch (Some vr)
  od"

text \<open>
  Prepare a given VCPU for removal: dissociate it, and clean up current VCPU state
  if necessary.
\<close>
definition vcpu_finalise :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_finalise vr \<equiv> do
    v \<leftarrow> get_vcpu vr;
    case vcpu_tcb v of
      Some t \<Rightarrow> dissociate_vcpu_tcb vr t
    | None \<Rightarrow> return ()
   od"

(* end of vcpu related definitions *)

text \<open>Switch into the address space of a given thread or the global address
space if none is correctly configured.\<close>
definition
  set_vm_root :: "word32 \<Rightarrow> (unit,'z::state_ext) s_monad" where
"set_vm_root tcb \<equiv> do
    thread_root_slot \<leftarrow> return (tcb, tcb_cnode_index 1);
    thread_root \<leftarrow> get_cap thread_root_slot;
    (case thread_root of
       ArchObjectCap (PageDirectoryCap pd (Some asid)) \<Rightarrow> doE
           pd' \<leftarrow> find_pd_for_asid asid;
           whenE (pd \<noteq> pd') $ throwError InvalidRoot;
           liftE $ arm_context_switch pd asid
       odE
     | _ \<Rightarrow> throwError InvalidRoot) <catch>
    (\<lambda>_. do
       global_us_pd \<leftarrow> gets (arm_us_global_pd o arch_state);
       do_machine_op $ set_current_pd $ addrFromKPPtr global_us_pd
    od)
od"

text \<open>Before deleting an ASID pool object we must deactivate all page
directories that are installed in it.\<close>
definition
delete_asid_pool :: "asid \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) s_monad" where
"delete_asid_pool base ptr \<equiv> do
  assert (base && mask asid_low_bits = 0);
  asid_table \<leftarrow> gets (arm_asid_table \<circ> arch_state);
  when (asid_table (asid_high_bits_of base) = Some ptr) $ do
    pool \<leftarrow> get_asid_pool ptr;
    mapM (\<lambda>offset. (when (pool (ucast offset) \<noteq> None) $ do
                          flush_space $ base + offset;
                          invalidate_asid_entry $ base + offset
                    od)) [0  .e.  (1 << asid_low_bits) - 1];
    asid_table' \<leftarrow> return (asid_table (asid_high_bits_of base:= None));
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_asid_table := asid_table' \<rparr>\<rparr>);
    tcb \<leftarrow> gets cur_thread;
    set_vm_root tcb
  od
od"

text \<open>When deleting a page directory from an ASID pool we must deactivate
it.\<close>
definition
delete_asid :: "asid \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) s_monad" where
"delete_asid asid pd \<equiv> do
  asid_table \<leftarrow> gets (arm_asid_table \<circ> arch_state);
  (case asid_table (asid_high_bits_of asid) of
    None \<Rightarrow> return ()
  | Some pool_ptr \<Rightarrow>  do
     pool \<leftarrow> get_asid_pool pool_ptr;
     when (pool (ucast asid) = Some pd) $ do
                flush_space asid;
                invalidate_asid_entry asid;
                pool' \<leftarrow> return (pool (ucast asid := None));
                set_asid_pool pool_ptr pool';
                tcb \<leftarrow> gets cur_thread;
                set_vm_root tcb
            od
    od)
od"


text \<open>Switch to a particular address space in order to perform a flush
operation.\<close>
definition
set_vm_root_for_flush :: "word32 \<Rightarrow> asid \<Rightarrow> (bool,'z::state_ext) s_monad" where
"set_vm_root_for_flush pd asid \<equiv> do
    tcb \<leftarrow> gets cur_thread;
    thread_root_slot \<leftarrow> return (tcb, tcb_cnode_index 1);
    thread_root \<leftarrow> get_cap thread_root_slot;
    not_is_pd \<leftarrow> (case thread_root of
                    ArchObjectCap (PageDirectoryCap cur_pd (Some _)) \<Rightarrow> return (cur_pd \<noteq> pd)
                  | _ \<Rightarrow> return True);
    (if not_is_pd then do
        arm_context_switch pd asid;
        return True
    od
    else return False)
od"

definition
do_flush :: "flush_type \<Rightarrow> vspace_ref \<Rightarrow> vspace_ref \<Rightarrow> paddr \<Rightarrow> unit machine_monad" where
"do_flush flush_type vstart vend pstart \<equiv>
    let vstart' = ptrFromPAddr pstart;
        vend'  = vstart' + (vend - vstart)
    in
    (case flush_type of
       Clean \<Rightarrow> cleanCacheRange_RAM vstart' vend' pstart
     | Invalidate \<Rightarrow> invalidateCacheRange_RAM vstart' vend' pstart
     | CleanInvalidate \<Rightarrow> cleanInvalidateCacheRange_RAM vstart' vend' pstart
     | Unify \<Rightarrow> do
         cleanCacheRange_PoU vstart' vend' pstart;
         dsb;
         invalidateCacheRange_I vstart' vend' pstart;
         branchFlushRange vstart' vend' pstart;
         isb
     od)"

text \<open>Flush mappings associated with a page table.\<close>
definition
flush_table :: "word32 \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) s_monad" where
"flush_table pd asid vptr pt \<equiv> do
    assert (vptr && mask (pageBitsForSize ARMSection) = 0);
    root_switched \<leftarrow> set_vm_root_for_flush pd asid;
    maybe_hw_asid \<leftarrow> load_hw_asid asid;
    when (maybe_hw_asid \<noteq> None) $ do
      hw_asid \<leftarrow> return (the maybe_hw_asid);
      do_machine_op $ invalidateLocalTLB_ASID hw_asid;
      when root_switched $ do
        tcb \<leftarrow> gets cur_thread;
        set_vm_root tcb
      od
    od
od"

text \<open>Flush mappings associated with a given page.\<close>
definition
flush_page :: "vmpage_size \<Rightarrow> word32 \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"flush_page page_size pd asid vptr\<equiv> do
    assert (vptr && mask pageBits = 0);
    root_switched \<leftarrow> set_vm_root_for_flush pd asid;
    maybe_hw_asid \<leftarrow> load_hw_asid asid;
    when (maybe_hw_asid \<noteq> None) $ do
      hw_asid \<leftarrow> return (the maybe_hw_asid);
      do_machine_op $ invalidateLocalTLB_VAASID (vptr || ucast hw_asid);
      when root_switched $ do
          tcb \<leftarrow> gets cur_thread;
          set_vm_root tcb
      od
   od
od"

text \<open>Return the optional page directory a page table is mapped in.\<close>
definition
page_table_mapped :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad" where
"page_table_mapped asid vaddr pt \<equiv> doE
    pd \<leftarrow> find_pd_for_asid asid;
    pd_slot \<leftarrow> returnOk $ lookup_pd_slot pd vaddr;
    pde \<leftarrow> liftE $ get_pde pd_slot;
    case pde of
      PageTablePDE addr \<Rightarrow> returnOk $
             if addrFromPPtr pt = addr then Some pd else None
    | _ \<Rightarrow> returnOk None
odE <catch> (K $ return None)"

text \<open>Unmap a page table from its page directory.\<close>
definition
unmap_page_table :: "asid \<Rightarrow> vspace_ref \<Rightarrow> word32 \<Rightarrow> (unit,'z::state_ext) s_monad" where
"unmap_page_table asid vaddr pt \<equiv> do
    pdOpt \<leftarrow> page_table_mapped asid vaddr pt;
    case pdOpt of
      None \<Rightarrow> return ()
    | Some pd \<Rightarrow> do
        pd_slot \<leftarrow> return $ lookup_pd_slot pd vaddr;
        store_pde pd_slot InvalidPDE;
        do_machine_op $ cleanByVA_PoU pd_slot (addrFromPPtr pd_slot);
        flush_table pd asid vaddr pt
    od
od"

text \<open>Check that a given frame is mapped by a given mapping entry.\<close>
definition
check_mapping_pptr :: "obj_ref \<Rightarrow> vmpage_size \<Rightarrow> (obj_ref + obj_ref) \<Rightarrow> (bool,'z::state_ext) s_monad" where
"check_mapping_pptr pptr pgsz tablePtr \<equiv> case tablePtr of
   Inl ptePtr \<Rightarrow> do
     pte \<leftarrow> get_pte ptePtr;
     return $ case pte of
       SmallPagePTE x _ _ \<Rightarrow> x = addrFromPPtr pptr \<and> pgsz = ARMSmallPage
     | LargePagePTE x _ _ \<Rightarrow> x = addrFromPPtr pptr \<and> pgsz = ARMLargePage
     | _ \<Rightarrow> False
   od
 | Inr pdePtr \<Rightarrow> do
     pde \<leftarrow> get_pde pdePtr;
     return $ case pde of
       SectionPDE x _ _ \<Rightarrow> x = addrFromPPtr pptr \<and> pgsz = ARMSection
     | SuperSectionPDE x _ _ \<Rightarrow> x = addrFromPPtr pptr \<and> pgsz = ARMSuperSection
     | _ \<Rightarrow> False
   od"


definition
  "last_byte_pte x \<equiv> x + ((1 << pte_bits) - 1)"

definition
  "last_byte_pde x \<equiv> x + ((1 << pde_bits) - 1)"

text \<open>Unmap a mapped page if the given mapping details are still current.\<close>
definition
unmap_page :: "vmpage_size \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"unmap_page pgsz asid vptr pptr \<equiv> doE
    pd \<leftarrow> find_pd_for_asid asid;
    (case pgsz of
          ARMSmallPage \<Rightarrow> doE
            p \<leftarrow> lookup_pt_slot pd vptr;
            throw_on_false undefined $
                check_mapping_pptr pptr pgsz (Inl p);
            liftE $ do
                store_pte p InvalidPTE;
                do_machine_op $ cleanByVA_PoU p (addrFromPPtr p)
            od
          odE
        | ARMLargePage \<Rightarrow> doE
            p \<leftarrow> lookup_pt_slot pd vptr;
            throw_on_false undefined $
                check_mapping_pptr pptr pgsz (Inl p);
            liftE $ do
                assert $ p && mask 7 = 0;
                slots \<leftarrow> return (map (\<lambda>x. x + p) largePagePTE_offsets);
                mapM (swp store_pte InvalidPTE) slots;
                do_machine_op $ cleanCacheRange_PoU (hd slots) (last_byte_pte (last slots))
                                                    (addrFromPPtr (hd slots))
            od
          odE
        | ARMSection \<Rightarrow> doE
            p \<leftarrow> returnOk (lookup_pd_slot pd vptr);
            throw_on_false undefined $
                check_mapping_pptr pptr pgsz (Inr p);
            liftE $ do
                store_pde p InvalidPDE;
                do_machine_op $ cleanByVA_PoU p (addrFromPPtr p)
            od
          odE
        | ARMSuperSection \<Rightarrow> doE
            p \<leftarrow> returnOk (lookup_pd_slot pd vptr);
            throw_on_false undefined $
                check_mapping_pptr pptr pgsz (Inr p);
            liftE $ do
                assert $ p && mask 7 = 0;
                slots \<leftarrow> return (map (\<lambda>x. x + p) superSectionPDE_offsets);
                mapM (swp store_pde InvalidPDE) slots;
                do_machine_op $ cleanCacheRange_PoU (hd slots) (last_byte_pde (last slots))
                                                    (addrFromPPtr (hd slots))
            od
          odE);
    liftE $ flush_page pgsz pd asid vptr
odE <catch> (K $ return ())"


text \<open>PageDirectory and PageTable capabilities cannot be copied until they
have a virtual ASID and location assigned. This is because page directories
cannot have multiple current virtual ASIDs and page tables cannot be shared
between address spaces or virtual locations.\<close>
definition
  arch_derive_cap :: "arch_cap \<Rightarrow> (cap,'z::state_ext) se_monad"
where
  "arch_derive_cap c \<equiv> case c of
     PageTableCap _ (Some x) \<Rightarrow> returnOk (ArchObjectCap c)
   | PageTableCap _ None \<Rightarrow> throwError IllegalOperation
   | PageDirectoryCap _ (Some x) \<Rightarrow> returnOk (ArchObjectCap c)
   | PageDirectoryCap _ None \<Rightarrow> throwError IllegalOperation
   | PageCap dev r R pgs x \<Rightarrow> returnOk (ArchObjectCap (PageCap dev r R pgs None))
   | ASIDControlCap \<Rightarrow> returnOk (ArchObjectCap c)
   | ASIDPoolCap _ _ \<Rightarrow> returnOk (ArchObjectCap c)
   | VCPUCap _ \<Rightarrow> returnOk (ArchObjectCap c)"

text \<open>No user-modifiable data is stored in ARM-specific capabilities.\<close>
definition
  arch_update_cap_data :: "bool \<Rightarrow> data \<Rightarrow> arch_cap \<Rightarrow> cap"
where
  "arch_update_cap_data preserve data c \<equiv> ArchObjectCap c"


text \<open>Actions that must be taken on finalisation of AR\_MHYP-specific
capabilities.\<close>
definition
  arch_finalise_cap :: "arch_cap \<Rightarrow> bool \<Rightarrow> (cap \<times> cap,'z::state_ext) s_monad"
where
  "arch_finalise_cap c x \<equiv> case (c, x) of
    (ASIDPoolCap ptr b, True) \<Rightarrow>  do
    delete_asid_pool b ptr;
    return (NullCap, NullCap)
    od
  | (PageDirectoryCap ptr (Some a), True) \<Rightarrow> do
    delete_asid a ptr;
    return (NullCap, NullCap)
  od
  | (PageTableCap ptr (Some (a, v)), True) \<Rightarrow> do
    unmap_page_table a v ptr;
    return (NullCap, NullCap)
  od
  | (PageCap _ ptr _ s (Some (a, v)), _) \<Rightarrow> do
     unmap_page s a v ptr;
     return (NullCap, NullCap)
  od
  | (VCPUCap vcpu_ref, True) \<Rightarrow> do
     vcpu_finalise vcpu_ref;
     return (NullCap, NullCap)
  od
  | _ \<Rightarrow> return (NullCap, NullCap)"

definition
  prepare_thread_delete :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "prepare_thread_delete p \<equiv> do
   t_vcpu \<leftarrow> arch_thread_get tcb_vcpu p;
   case t_vcpu of
   Some v \<Rightarrow> dissociate_vcpu_tcb v p
 | None \<Rightarrow> return ()
 od"


text \<open>A thread's virtual address space capability must be to a page directory
to be valid on the ARM architecture.\<close>
definition
  is_valid_vtable_root :: "cap \<Rightarrow> bool" where
  "is_valid_vtable_root c \<equiv> \<exists>r a. c = ArchObjectCap (PageDirectoryCap r (Some a))"

definition
check_valid_ipc_buffer :: "vspace_ref \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) se_monad" where
"check_valid_ipc_buffer vptr c \<equiv> case c of
  (ArchObjectCap (PageCap False _ _ _ _)) \<Rightarrow> doE
    whenE (\<not> is_aligned vptr msg_align_bits) $ throwError AlignmentError;
    returnOk ()
  odE
| _ \<Rightarrow> throwError IllegalOperation"

text \<open>Decode a user argument word describing the kind of VM attributes a
mapping is to have.\<close>
definition
attribs_from_word :: "word32 \<Rightarrow> vm_attributes" where
"attribs_from_word w \<equiv>
  let V = (if w !!0 then {PageCacheable} else {})
  in if w!!2 then insert XNever V else V"

text \<open>Update the mapping data saved in a page or page table capability.\<close>
definition
  update_map_data :: "arch_cap \<Rightarrow> (word32 \<times> word32) option \<Rightarrow> arch_cap" where
  "update_map_data cap m \<equiv> case cap of PageCap dev p R sz _ \<Rightarrow> PageCap dev p R sz m
                                     | PageTableCap p _ \<Rightarrow> PageTableCap p m"

text \<open>Get information about the frame of a given virtual address\<close>
definition
  resolve_vaddr :: "word32 \<Rightarrow> vspace_ref \<Rightarrow> ((vmpage_size \<times> obj_ref) option, 'z::state_ext) s_monad"
where
  "resolve_vaddr pd vaddr \<equiv> do
     pd_slot \<leftarrow> return $ lookup_pd_slot pd vaddr;
     pde \<leftarrow> get_master_pde pd_slot;
     case pde of
         SectionPDE f _ _ \<Rightarrow> return $ Some (ARMSection, f)
       | SuperSectionPDE f _ _ \<Rightarrow> return $ Some (ARMSuperSection, f)
       | PageTablePDE t \<Rightarrow> (do
           pt \<leftarrow> return $ ptrFromPAddr t;
           pte_slot \<leftarrow> return $ lookup_pt_slot_no_fail pt vaddr;
           pte \<leftarrow> get_master_pte pte_slot;
           case pte of
               LargePagePTE f _ _ \<Rightarrow> return $ Some (ARMLargePage, f)
             | SmallPagePTE f _ _ \<Rightarrow> return $ Some (ARMSmallPage, f)
             | _ \<Rightarrow> return None
         od)
       | _ \<Rightarrow> return None
   od"

text \<open>
  A pointer is inside a user frame if its top bits point to a @{text DataPage}.
\<close>
definition
  in_user_frame :: "word32 \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "in_user_frame p s \<equiv>
   \<exists>sz. kheap s (p && ~~ mask (pageBitsForSize sz)) =
        Some (ArchObj (DataPage False sz))"

text \<open>Make numeric value of @{const msg_align_bits} visible.\<close>
lemmas msg_align_bits = msg_align_bits'[unfolded word_size_bits_def, simplified]

end

end
