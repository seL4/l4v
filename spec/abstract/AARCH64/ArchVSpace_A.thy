(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* FIXME AARCH64: validated modulo VCPU operations and style update *)

chapter "AARCH64 VSpace Functions"

theory ArchVSpace_A
imports
  Retype_A
  ArchTcb_A
begin

context Arch begin global_naming AARCH64_A

text \<open>
  Look up a thread's IPC buffer and check that the thread has the authority to read or (in the
  receiver case) write to it.
\<close>
definition lookup_ipc_buffer :: "bool \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
  where
  "lookup_ipc_buffer is_receiver thread \<equiv> do
     buffer_ptr \<leftarrow> thread_get tcb_ipc_buffer thread;
     buffer_frame_slot \<leftarrow> return (thread, tcb_cnode_index 4);
     buffer_cap \<leftarrow> get_cap buffer_frame_slot;
     case buffer_cap of
       ArchObjectCap (FrameCap p R vms False _) \<Rightarrow>
         if vm_read_write \<subseteq> R \<or> vm_read_only \<subseteq> R \<and> \<not>is_receiver
         then return $ Some $ p + (buffer_ptr && mask (pageBitsForSize vms))
         else return None
     | _ \<Rightarrow> return None
   od"

definition pool_for_asid :: "asid \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref option" where
  "pool_for_asid asid \<equiv> \<lambda>s. asid_table s (asid_high_bits_of asid)"

definition entry_for_pool :: "obj_ref \<Rightarrow> asid \<Rightarrow> (obj_ref \<rightharpoonup> asid_pool) \<Rightarrow> asid_pool_entry option"
  where
  "entry_for_pool pool_ptr asid \<equiv> do {
     pool \<leftarrow> oapply pool_ptr;
     K $ pool (asid_low_bits_of asid)
   }"

definition vspace_for_pool :: "obj_ref \<Rightarrow> asid \<Rightarrow> (obj_ref \<rightharpoonup> asid_pool) \<Rightarrow> obj_ref option" where
  "vspace_for_pool pool_ptr asid \<equiv> do {
     entry \<leftarrow> entry_for_pool pool_ptr asid;
     oreturn $ ap_vspace entry
   }"

(* this is what asid_map encodes in ARM/ARM_HYP; getASIDPoolEntry in Haskell *)
definition entry_for_asid :: "asid \<Rightarrow> 'z::state_ext state \<Rightarrow> asid_pool_entry option" where
  "entry_for_asid asid = do {
     oassert (0 < asid);
     pool_ptr \<leftarrow> pool_for_asid asid;
     entry_for_pool pool_ptr asid \<circ> asid_pools_of
   }"

(* update an entry in the asid map *)
definition update_asid_pool_entry ::
  "(asid_pool_entry \<rightharpoonup> asid_pool_entry) \<Rightarrow> asid \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "update_asid_pool_entry f asid \<equiv> do
     pool_ptr \<leftarrow> gets_the $ pool_for_asid asid;
     pool \<leftarrow> get_asid_pool pool_ptr;
     idx \<leftarrow> return $ asid_low_bits_of asid;
     entry \<leftarrow> assert_opt $ pool idx;
     set_asid_pool pool_ptr (pool (idx := f entry))
   od"

definition vspace_for_asid :: "asid \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref option" where
  "vspace_for_asid asid = do {
     entry \<leftarrow> entry_for_asid asid;
     oreturn $ ap_vspace entry
   }"

text \<open>Locate the top-level page table associated with a given virtual ASID.\<close>
definition find_vspace_for_asid :: "asid \<Rightarrow> (obj_ref,'z::state_ext) lf_monad" where
  "find_vspace_for_asid asid \<equiv> doE
     vspace_opt \<leftarrow> liftE $ gets $ vspace_for_asid asid;
     throw_opt InvalidRoot vspace_opt
   odE"

definition load_vmid :: "asid \<Rightarrow> (vmid option, 'z::state_ext) s_monad" where
  "load_vmid asid \<equiv> do
     entry \<leftarrow> gets_the $ entry_for_asid asid;
     return $ ap_vmid entry
   od"

text \<open>Associate a VMID with an ASID.\<close>
definition store_vmid :: "asid \<Rightarrow> vmid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_vmid asid hw_asid \<equiv> do
     update_asid_pool_entry (\<lambda>entry. Some $ ASIDPoolVSpace (Some hw_asid) (ap_vspace entry)) asid;
     vmid_table \<leftarrow> gets (arm_vmid_table \<circ> arch_state);
     vmid_table' \<leftarrow> return $ vmid_table (hw_asid \<mapsto> asid);
     modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_vmid_table := vmid_table' \<rparr>\<rparr>)
   od"

text \<open>Clear all TLB mappings associated with this ASID.\<close>
definition invalidate_tlb_by_asid :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_tlb_by_asid asid \<equiv> do
     maybe_vmid \<leftarrow> load_vmid asid;
     case maybe_vmid of
       None \<Rightarrow> return ()
     | Some vmid \<Rightarrow> do_machine_op $ invalidateTranslationASID (ucast vmid)
   od"

text \<open>Clear all TLB mappings associated with this ASID and virtual address.\<close>
definition invalidate_tlb_by_asid_va :: "asid \<Rightarrow> vspace_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_tlb_by_asid_va asid vaddr \<equiv> do
     maybe_vmid \<leftarrow> load_vmid asid;
     case maybe_vmid of
       None \<Rightarrow> return ()
     | Some vmid \<Rightarrow>
         do_machine_op $
           invalidateTranslationSingle $ (ucast vmid << word_bits-asid_bits) || (vaddr >> pageBits)
   od"

text \<open>Remove any mapping from this virtual ASID to a VMID.\<close>
definition invalidate_asid :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_asid asid \<equiv>
     update_asid_pool_entry (\<lambda>entry. Some $ ASIDPoolVSpace None (ap_vspace entry)) asid"

text \<open>Remove any mapping from this VMID to an ASID.\<close>
definition invalidate_vmid_entry :: "vmid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_vmid_entry vmid \<equiv> do
     vmid_table \<leftarrow> gets (arm_vmid_table \<circ> arch_state);
     vmid_table' \<leftarrow> return (vmid_table (vmid := None));
     modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_vmid_table := vmid_table' \<rparr>\<rparr>)
  od"

text \<open>Remove mappings in either direction involving this ASID.\<close>
definition invalidate_asid_entry :: "asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invalidate_asid_entry asid \<equiv> do
     maybe_hw_asid \<leftarrow> load_vmid asid;
     when (maybe_hw_asid \<noteq> None) $ invalidate_vmid_entry (the maybe_hw_asid);
     invalidate_asid asid
  od"

text \<open>Locate a VMID that is not in use, if necessary by reclaiming one already assigned to an ASID.\<close>
definition find_free_vmid :: "(vmid,'z::state_ext) s_monad" where
  "find_free_vmid \<equiv> do
     vmid_table \<leftarrow> gets (arm_vmid_table \<circ> arch_state);
     next_vmid \<leftarrow> gets (arm_next_vmid \<circ> arch_state);
     maybe_vmid \<leftarrow> return $ find (\<lambda>a. vmid_table a = None)
                                 (take (length [minBound :: vmid .e. maxBound])
                                       ([next_vmid .e. maxBound] @ [minBound .e. next_vmid]));
     case maybe_vmid of
       Some vmid \<Rightarrow> return vmid
     | None \<Rightarrow> do
         invalidate_asid $ the $ vmid_table next_vmid;
         do_machine_op $ invalidateTranslationASID (ucast next_vmid);
         invalidate_vmid_entry next_vmid;
         modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_next_vmid := next_vmid + 1 \<rparr>\<rparr>);
         return next_vmid
       od
   od"

text \<open>Get the VMID associated with an ASID, assigning one if none is already assigned.\<close>
definition get_vmid :: "asid \<Rightarrow> (vmid, 'z::state_ext) s_monad" where
  "get_vmid asid \<equiv> do
     maybe_vmid \<leftarrow> load_vmid asid;
     case maybe_vmid of
       Some vmid \<Rightarrow> return vmid
     | None \<Rightarrow>  do
         new_hw_asid \<leftarrow> find_free_vmid;
         store_vmid asid new_hw_asid;
         return new_hw_asid
       od
   od"

text \<open>
  Format a VM fault message to be passed to a thread's supervisor after it encounters a page fault.
\<close>
definition handle_vm_fault :: "obj_ref \<Rightarrow> vmfault_type \<Rightarrow> (unit, 'z::state_ext) f_monad" where
  "handle_vm_fault thread fault \<equiv> case fault of
     ARMDataAbort \<Rightarrow> doE
       \<comment> \<open>FIXME AARCH64: needs VCPU adjustment (currently copy/paste from ARM)\<close>
       addr \<leftarrow> liftE $ do_machine_op getFAR;
       fault \<leftarrow> liftE $ do_machine_op getDFSR;
       throwError $ ArchFault $ VMFault addr [0, fault && mask 14]
     odE
   | ARMPrefetchAbort \<Rightarrow> doE
       \<comment> \<open>FIXME AARCH64: needs VCPU adjustment (currently copy/paste from ARM)\<close>
       pc \<leftarrow> liftE $ as_user thread $ getRestartPC;
       fault \<leftarrow> liftE $ do_machine_op getIFSR;
       throwError $ ArchFault $ VMFault pc [1, fault && mask 14]
     odE"


text \<open>Switch to given address space, using VMID associated with provided ASID.\<close>
definition arm_context_switch :: "obj_ref \<Rightarrow> asid \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arm_context_switch vspace asid = do
     vmid <- get_vmid asid;
     do_machine_op $ setVSpaceRoot (addrFromPPtr vspace) (ucast vmid)
   od"


section \<open>Manipulation of VCPU-related state and registers\<close>

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
  vgic_update_lr :: "obj_ref \<Rightarrow> nat \<Rightarrow> AARCH64_A.virq \<Rightarrow> (unit,'z::state_ext) s_monad"
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
     vcpu_save_reg vcpu_ptr VCPURegCNTV_CVAL;
     vcpu_save_reg vcpu_ptr VCPURegCNTVOFF;
     vcpu_save_reg vcpu_ptr VCPURegCNTKCTL_EL1;
     do_machine_op check_export_arch_timer;
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
     vcpu_restore_reg vcpu_ptr VCPURegCNTV_CVAL;
     vcpu_restore_reg vcpu_ptr VCPURegCNTKCTL_EL1;
     current_cntpct \<leftarrow> do_machine_op read_cntpct;
     vcpu \<leftarrow> get_vcpu vcpu_ptr;
     last_pcount \<leftarrow> return $ vtimerLastPCount $ vcpu_vtimer vcpu;
     delta \<leftarrow> return $ current_cntpct - last_pcount;
     cntvoff \<leftarrow> vcpu_read_reg vcpu_ptr VCPURegCNTVOFF;
     offset \<leftarrow> return $ cntvoff + ucast delta;
     vcpu_write_reg vcpu_ptr VCPURegCNTVOFF offset;
     vcpu_restore_reg vcpu_ptr VCPURegCNTVOFF;
     masked \<leftarrow> return $ (vcpu_vppi_masked vcpu (the $ irq_vppi_event_index irqVTimerEvent));
     \<comment> \<open>we do not know here that irqVTimerEvent is IRQReserved, therefore not IRQInactive,
        so the only way to prove we don't unmask an inactive interrupt is to check\<close>
     safe_to_unmask \<leftarrow> is_irq_active irqVTimerEvent;
     when safe_to_unmask $ do_machine_op $ maskInterrupt masked irqVTimerEvent;
     vcpu_restore_reg vcpu_ptr VCPURegCNTV_CTL
   od"

text \<open>Turn VPCU mode off on the hardware level.\<close>
definition vcpu_disable :: "obj_ref option \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vcpu_disable vo \<equiv> do
    do_machine_op dsb;
    (case vo of
      Some vr \<Rightarrow> do
        hcr \<leftarrow> do_machine_op get_gic_vcpu_ctrl_hcr;
        vgic_update vr (\<lambda>vgic. vgic\<lparr> vgic_hcr := hcr \<rparr>);
        vcpu_save_reg vr VCPURegSCTLR;
        vcpu_save_reg vr VCPURegACTLR; \<comment> \<open>since FPU enabled\<close>
        do_machine_op isb
      od
    | _ \<Rightarrow> return ());
    do_machine_op $ do
        set_gic_vcpu_ctrl_hcr 0; \<comment> \<open>turn VGIC off\<close>
        isb;
        setSCTLR sctlrDefault; \<comment> \<open>turn S1 MMU off\<close>
        isb;
        setHCR hcrNative;
        isb;
        \<comment> \<open>allow FPU instructions in EL0 and EL1 for native threads\<close>
        enableFpuEL01
      od;
    case vo of
      Some vr \<Rightarrow> do
          save_virt_timer vr;
          do_machine_op $ maskInterrupt True irqVTimerEvent
        od
      | _ \<Rightarrow> return ()
    od"

text \<open>Turn VCPU mode on, on the hardware level.\<close>
definition vcpu_enable :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vcpu_enable vr \<equiv> do
     vcpu_restore_reg vr VCPURegSCTLR;
     vcpu \<leftarrow> get_vcpu vr;
     do_machine_op $ do
        setHCR hcrVCPU;
        isb;
        set_gic_vcpu_ctrl_hcr (vgic_hcr $ vcpu_vgic vcpu)
     od;
     vcpu_restore_reg vr VCPURegCPACR; \<comment> \<open>FPU\<close>
     restore_virt_timer vr
   od"

text \<open>Prepare the current VCPU for removal.\<close>
definition vcpu_invalidate_active :: "(unit,'z::state_ext) s_monad" where
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
definition dissociate_vcpu_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "dissociate_vcpu_tcb vr t \<equiv> do
     t_vcpu \<leftarrow> arch_thread_get tcb_vcpu t;
     v \<leftarrow> get_vcpu vr;
     assert (t_vcpu = Some vr \<and> vcpu_tcb v = Some t); \<comment> \<open>make sure they were associated\<close>
     cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
     when (\<exists>a. cur_v = Some (vr,a)) vcpu_invalidate_active;
     arch_thread_set (\<lambda>x. x \<lparr> tcb_vcpu := None \<rparr>) t;
     set_vcpu vr (v\<lparr> vcpu_tcb := None \<rparr>);
     as_user t $ do
       sr \<leftarrow> getRegister SPSR_EL1;
       setRegister SPSR_EL1 $ sanitise_register False SPSR_EL1 sr
     od
   od"

text \<open>Associating a TCB and VCPU, removing any potentially existing associations:\<close>
definition associate_vcpu_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "associate_vcpu_tcb vr t \<equiv> do
     t_vcpu \<leftarrow> arch_thread_get tcb_vcpu t;
     case t_vcpu of
       Some p \<Rightarrow> dissociate_vcpu_tcb p t
     | _ \<Rightarrow> return ();
     v \<leftarrow> get_vcpu vr;
     case vcpu_tcb v of
       Some p \<Rightarrow> dissociate_vcpu_tcb vr p
     | _ \<Rightarrow> return ();
     arch_thread_set (\<lambda>x. x \<lparr> tcb_vcpu := Some vr \<rparr>) t;
     set_vcpu vr (v\<lparr> vcpu_tcb := Some t \<rparr>)
  od"

text \<open>Register + context save for VCPUs\<close>

definition
  vcpu_save :: "(obj_ref \<times> bool) option \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vcpu_save vb \<equiv>
     case vb
     of Some (vr, active) \<Rightarrow> do
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

          \<comment> \<open>armvVCPUSave\<close>
          vcpu_save_reg_range vr VCPURegTTBR0 VCPURegSPSR_EL1;
          do_machine_op isb
       od
     | _ \<Rightarrow> fail"

text \<open>Register + context restore for VCPUs\<close>
definition vcpu_restore :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
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
     vcpu_restore_reg_range vr VCPURegTTBR0 VCPURegSPSR_EL1;
     vcpu_enable vr
  od"

text \<open> Make a new VCPU the active/current VCPU. If passed None, will mark the current VCPU as
  not active, and disable VCPU mode, but leave the rest intact caching for the case where
  we switch back to the same VCPU soon.\<close>
definition vcpu_switch :: "obj_ref option \<Rightarrow> (unit,'z::state_ext) s_monad" where
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

text \<open>Prepare a given VCPU for removal: dissociate it, and clean up current VCPU state
  if necessary.\<close>
definition vcpu_finalise :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vcpu_finalise vr \<equiv> do
    v \<leftarrow> get_vcpu vr;
    case vcpu_tcb v of
      Some t \<Rightarrow> dissociate_vcpu_tcb vr t
    | None \<Rightarrow> return ()
   od"

(* end of vcpu related definitions *)


text \<open>Switch to global user address space, using VMID 0.\<close>
definition set_global_user_vspace :: "(unit,'z::state_ext) s_monad" where
  "set_global_user_vspace = do
     global <- gets (arm_us_global_vspace \<circ> arch_state);
     do_machine_op $ setVSpaceRoot (addrFromKPPtr global) 0
   od"

text \<open>
  Switch into the address space of a given thread or the global address space if none is correctly
  configured.
\<close>
definition set_vm_root :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_vm_root tcb \<equiv> do
     thread_root_slot \<leftarrow> return (tcb, tcb_cnode_index 1);
     thread_root \<leftarrow> get_cap thread_root_slot;
     (case thread_root of
        ArchObjectCap (PageTableCap pt True (Some (asid, _))) \<Rightarrow> doE
          pt' \<leftarrow> find_vspace_for_asid asid;
          whenE (pt \<noteq> pt') $ throwError InvalidRoot;
          liftE $ arm_context_switch pt asid
        odE
      | _ \<Rightarrow> throwError InvalidRoot) <catch> (\<lambda>_. set_global_user_vspace)
  od"


definition delete_asid_pool :: "asid \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "delete_asid_pool base ptr \<equiv> do
     assert (asid_low_bits_of base = 0);
     asid_table \<leftarrow> gets asid_table;
     when (asid_table (asid_high_bits_of base) = Some ptr) $ do
       pool \<leftarrow> get_asid_pool ptr;
       mapM (\<lambda>offset. when (pool (ucast offset) \<noteq> None) $ do
                            invalidate_tlb_by_asid $ base + offset;
                            invalidate_asid_entry $ base + offset
                      od) [0  .e.  mask asid_low_bits];
       asid_table' \<leftarrow> return $ asid_table (asid_high_bits_of base:= None);
       modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> arm_asid_table := asid_table' \<rparr>\<rparr>);
       tcb \<leftarrow> gets cur_thread;
       set_vm_root tcb
     od
   od"


definition delete_asid :: "asid \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "delete_asid asid pt \<equiv> do
     pool_ptr_op \<leftarrow> gets (pool_for_asid asid);
     case pool_ptr_op of
       None \<Rightarrow> return ()
     | Some pool_ptr \<Rightarrow> do
         pool \<leftarrow> get_asid_pool pool_ptr;
         when (\<exists>vmid. pool (asid_low_bits_of asid) = Some (ASIDPoolVSpace vmid pt)) $ do
           invalidate_tlb_by_asid asid;
           invalidate_asid_entry asid;
           pool' \<leftarrow> return $ pool (asid_low_bits_of asid := None);
           set_asid_pool pool_ptr pool';
           tcb \<leftarrow> gets cur_thread;
           set_vm_root tcb
         od
       od
   od"


definition unmap_page_table :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "unmap_page_table asid vaddr pt \<equiv> doE
     top_level_pt \<leftarrow> find_vspace_for_asid asid;
     pt_slot \<leftarrow> pt_lookup_from_level max_pt_level top_level_pt vaddr pt;
     liftE $ store_pte pt_slot InvalidPTE;
     liftE $ do_machine_op $ cleanByVA_PoU pt_slot (addrFromPPtr pt_slot);
     liftE $ invalidate_tlb_by_asid asid
   odE <catch> (K $ return ())"

text \<open>
  Look up an @{text "asid+vspace_ref"} down to the provided level in the page table.
  For level @{term bot_level}, return a pointer to a table at the returned level.
  The level can be higher than @{term bot_level} if the lookup terminates early because
  it hit a page or an invalid entry.
\<close>
definition vs_lookup_table :: "vm_level \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> (vm_level \<times> obj_ref) option"
  where
  "vs_lookup_table bot_level asid vptr \<equiv> do {
     pool_ptr \<leftarrow> pool_for_asid asid;
     if bot_level = asid_pool_level
     then oreturn (asid_pool_level, pool_ptr)
     else do {
       top_level_pt \<leftarrow> vspace_for_pool pool_ptr asid \<circ> asid_pools_of;
       pt_walk max_pt_level bot_level top_level_pt vptr \<circ> ptes_of
     }
   }"

text \<open>
  Same as @{const vs_lookup_table}, but return a pointer to a slot in a table at the returned level.
  For @{prop "bot_level = asid_pool_level"}, still return the pointer to the ASID pool (not a slot
  inside it, since there are no slot functions for ASID pools).
\<close>
definition vs_lookup_slot :: "vm_level \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> (vm_level \<times> obj_ref) option"
  where
  "vs_lookup_slot bot_level asid vref \<equiv> do {
     (level', table) \<leftarrow> vs_lookup_table bot_level asid vref;
     if level' = asid_pool_level then
       oreturn (level', table)
     else
       oreturn (level', pt_slot_offset level' table vref)
   }"

text \<open>Unmap a mapped page if the given mapping details are still current.\<close>
definition unmap_page :: "vmpage_size \<Rightarrow> asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "unmap_page pgsz asid vptr pptr \<equiv> doE
     top_level_pt \<leftarrow> find_vspace_for_asid asid;
     (lev, slot) \<leftarrow> liftE $ gets_the $ pt_lookup_slot top_level_pt vptr \<circ> ptes_of;
     unlessE (pt_bits_left lev = pageBitsForSize pgsz) $ throwError InvalidRoot;
     pte \<leftarrow> liftE $ get_pte slot;
     unlessE (is_PagePTE pte \<and> pptr_from_pte pte = pptr) $ throwError InvalidRoot;
     liftE $ store_pte slot InvalidPTE;
     liftE $ do_machine_op $ cleanByVA_PoU slot (addrFromPPtr slot);
     liftE $ invalidate_tlb_by_asid_va asid vptr
   odE <catch> (K $ return ())"

text \<open>
  Page table structure capabilities cannot be copied until they have an ASID and location
  assigned. This is because they cannot have multiple current ASIDs and cannot be shared between
  address spaces or virtual locations.
\<close>
definition arch_derive_cap :: "arch_cap \<Rightarrow> (cap,'z::state_ext) se_monad"
  where
  "arch_derive_cap c \<equiv>
     case c of
       PageTableCap _ _ (Some x) \<Rightarrow> returnOk (ArchObjectCap c)
     | PageTableCap _ _ None \<Rightarrow> throwError IllegalOperation
     | FrameCap r R sz dev mp \<Rightarrow> returnOk $ ArchObjectCap (FrameCap r R sz dev None)
     | ASIDControlCap \<Rightarrow> returnOk (ArchObjectCap c)
     | ASIDPoolCap _ _ \<Rightarrow> returnOk (ArchObjectCap c)
     | VCPUCap _ \<Rightarrow> returnOk (ArchObjectCap c)"

text \<open>No user-modifiable data is stored in AARCH64-specific capabilities.\<close>
definition arch_update_cap_data :: "bool \<Rightarrow> data \<Rightarrow> arch_cap \<Rightarrow> cap"
  where
  "arch_update_cap_data preserve data c \<equiv> ArchObjectCap c"


text \<open>Actions that must be taken on finalisation of AARCH64-specific capabilities.\<close>
definition arch_finalise_cap :: "arch_cap \<Rightarrow> bool \<Rightarrow> (cap \<times> cap,'z::state_ext) s_monad"
  where
  "arch_finalise_cap c x \<equiv> case (c, x) of
     (ASIDPoolCap ptr b, True) \<Rightarrow>  do
       delete_asid_pool b ptr;
       return (NullCap, NullCap)
     od
   | (PageTableCap ptr is_top (Some (a, v)), True) \<Rightarrow> do
       doE
         vroot \<leftarrow> find_vspace_for_asid a;
         if vroot = ptr then liftE $ delete_asid a ptr else throwError InvalidRoot
       odE <catch>
       (\<lambda>_. unmap_page_table a v ptr);
       return (NullCap, NullCap)
     od
   | (FrameCap ptr _ sz _ (Some (a, v)), _) \<Rightarrow> do
       unmap_page sz a v ptr;
       return (NullCap, NullCap)
     od
   | (VCPUCap vcpu_ref, True) \<Rightarrow> do
      vcpu_finalise vcpu_ref;
      return (NullCap, NullCap)
   od
   | _ \<Rightarrow> return (NullCap, NullCap)"


text \<open>
  A thread's virtual address space capability must be to a mapped page table to be valid on
  the AARCH64 architecture.
\<close>
definition is_valid_vtable_root :: "cap \<Rightarrow> bool"
  where
  "is_valid_vtable_root c \<equiv>
     case c of ArchObjectCap (PageTableCap _ True (Some _)) \<Rightarrow> True | _ \<Rightarrow> False"

text \<open>Make numeric value of @{const msg_align_bits} visible.\<close>
lemmas msg_align_bits = msg_align_bits'[unfolded word_size_bits_def, simplified]

definition check_valid_ipc_buffer :: "vspace_ref \<Rightarrow> cap \<Rightarrow> (unit,'z::state_ext) se_monad"
  where
  "check_valid_ipc_buffer vptr c \<equiv>
     case c of
       ArchObjectCap (FrameCap _ _ _ False _) \<Rightarrow>
         whenE (\<not> is_aligned vptr msg_align_bits) $ throwError AlignmentError
     | _ \<Rightarrow> throwError IllegalOperation"

text \<open>A pointer is inside a user frame if its top bits point to a @{const DataPage}.\<close>
definition in_user_frame :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  where
  "in_user_frame p s \<equiv>
     \<exists>sz. kheap s (p && ~~ mask (pageBitsForSize sz)) = Some (ArchObj (DataPage False sz))"

definition fpu_thread_delete :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "fpu_thread_delete thread_ptr \<equiv> do_machine_op (fpuThreadDeleteOp thread_ptr)"

definition prepare_thread_delete :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "prepare_thread_delete thread_ptr \<equiv> do
     fpu_thread_delete thread_ptr;
     t_vcpu \<leftarrow> arch_thread_get tcb_vcpu thread_ptr;
     case t_vcpu of
       Some v \<Rightarrow> dissociate_vcpu_tcb v thread_ptr
     | None \<Rightarrow> return ()
   od"

end
end
