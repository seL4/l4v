(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "AARCH64 VCPU Accessor Functions"

theory VCPUAcc_A
imports
  ArchVSpaceAcc_A
  ArchTcb_A
begin

context Arch begin global_naming AARCH64_A

section \<open>Accessors\<close>

locale_abbrev vcpus_of :: "'z::state_ext state \<Rightarrow> obj_ref \<rightharpoonup> vcpu" where
  "vcpus_of \<equiv> \<lambda>s. aobjs_of s |> vcpu_of"

definition get_vcpu :: "obj_ref \<Rightarrow> (vcpu,'z::state_ext) s_monad" where
  "get_vcpu \<equiv> gets_map vcpus_of"

definition set_vcpu :: "obj_ref \<Rightarrow> vcpu \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_vcpu ptr vcpu \<equiv> set_object ptr (ArchObj (VCPU vcpu))"


section \<open>Manipulation of VCPU-related state and registers\<close>

definition vcpu_update :: "obj_ref \<Rightarrow> (vcpu \<Rightarrow> vcpu) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vcpu_update vr f \<equiv> do
    vcpu \<leftarrow> get_vcpu vr;
    set_vcpu vr (f vcpu)
  od"

definition vgic_update ::
  "obj_ref \<Rightarrow> (gic_vcpu_interface \<Rightarrow> gic_vcpu_interface) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vgic_update vr f \<equiv> vcpu_update vr (\<lambda>vcpu. vcpu \<lparr> vcpu_vgic := f (vcpu_vgic vcpu) \<rparr> )"

definition vgic_update_lr :: "obj_ref \<Rightarrow> nat \<Rightarrow> AARCH64_A.virq \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vgic_update_lr vr irq_idx virq \<equiv>
    vgic_update vr (\<lambda>vgic. vgic \<lparr> vgic_lr := (vgic_lr vgic)(irq_idx := virq) \<rparr>)"

definition vcpu_save_reg :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vcpu_save_reg vr reg \<equiv> do
    rval \<leftarrow> do_machine_op (readVCPUHardwareReg reg);
    vcpu_update vr (\<lambda>vcpu. vcpu \<lparr> vcpu_regs := (vcpu_regs vcpu)(reg := rval) \<rparr> )
  od"

definition vcpu_save_reg_range :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> vcpureg \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vcpu_save_reg_range vr from to \<equiv> mapM_x (\<lambda>reg. vcpu_save_reg vr reg) [from .e. to]"

definition vcpu_restore_reg :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vcpu_restore_reg vr reg \<equiv> do
    vcpu \<leftarrow> get_vcpu vr;
    do_machine_op (writeVCPUHardwareReg reg (vcpu_regs vcpu reg))
  od"

definition vcpu_restore_reg_range :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> vcpureg \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "vcpu_restore_reg_range vr from to \<equiv> mapM_x (\<lambda>reg. vcpu_restore_reg vr reg) [from .e. to]"

definition vcpu_read_reg :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> (machine_word, 'z::state_ext) s_monad" where
  "vcpu_read_reg vr reg \<equiv> do
    vcpu \<leftarrow> get_vcpu vr;
    return (vcpu_regs vcpu reg)
  od"

definition vcpu_write_reg :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
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
    case vo of
      Some vr \<Rightarrow> do
        hcr \<leftarrow> do_machine_op get_gic_vcpu_ctrl_hcr;
        vgic_update vr (\<lambda>vgic. vgic\<lparr> vgic_hcr := hcr \<rparr>);
        vcpu_save_reg vr VCPURegSCTLR;
        vcpu_save_reg vr VCPURegCPACR; \<comment> \<open>since FPU enabled\<close>
        do_machine_op isb
      od
    | _ \<Rightarrow> return ();
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

text \<open>Register + context save for VCPUs\<close>
definition vcpu_save :: "(obj_ref \<times> bool) option \<Rightarrow> (unit,'z::state_ext) s_monad" where
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

          \<comment> \<open>armvVCPUSave\<close>
          vcpu_save_reg_range vr VCPURegTTBR0 VCPURegSPSR_EL1
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

text \<open>
  Make a new VCPU the active/current VCPU. If passed None, will mark the current VCPU as
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


text \<open>VCPU objects can be associated with and dissociated from TCBs.\<close>

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
  "associate_vcpu_tcb vcpu_ptr t \<equiv> do
     t_vcpu \<leftarrow> arch_thread_get tcb_vcpu t;
     case t_vcpu of
       Some p \<Rightarrow> dissociate_vcpu_tcb p t
     | _ \<Rightarrow> return ();
     v \<leftarrow> get_vcpu vcpu_ptr;
     case vcpu_tcb v of
       Some p \<Rightarrow> dissociate_vcpu_tcb vcpu_ptr p
     | _ \<Rightarrow> return ();
     arch_thread_set (\<lambda>x. x \<lparr> tcb_vcpu := Some vcpu_ptr \<rparr>) t;
     set_vcpu vcpu_ptr (v\<lparr> vcpu_tcb := Some t \<rparr>);
     ct \<leftarrow> gets cur_thread;
     when (t = ct) $ vcpu_switch (Some vcpu_ptr)
  od"

text \<open>
  Prepare a given VCPU for removal: dissociate it, and clean up current VCPU state
  if necessary.\<close>
definition vcpu_finalise :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vcpu_finalise vr \<equiv> do
    v \<leftarrow> get_vcpu vr;
    case vcpu_tcb v of
      Some t \<Rightarrow> dissociate_vcpu_tcb vr t
    | None \<Rightarrow> return ()
   od"

end
end
