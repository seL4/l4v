(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Arch-specific Interrupts"

theory ArchInterrupt_A
imports Ipc_A
begin

context Arch begin arch_global_naming (A)

definition virqSetEOIIRQEN :: "virq \<Rightarrow> machine_word \<Rightarrow> virq" where
  "virqSetEOIIRQEN virq v \<equiv>
     if virq_type virq = 3
     then virq
     else (virq && ~~(1 << eoiirqen_shift)) || ((v << eoiirqen_shift) && (1 << eoiirqen_shift))"

definition vgic_maintenance :: "(unit,'z::state_ext) s_monad" where
  "vgic_maintenance = do
     cur_vcpu \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
     case cur_vcpu
       of Some (vcpu_ptr, True) \<Rightarrow> do
            eisr0 \<leftarrow> do_machine_op $ get_gic_vcpu_ctrl_eisr0;
            eisr1 \<leftarrow> do_machine_op $ get_gic_vcpu_ctrl_eisr1;
            flags \<leftarrow> do_machine_op $ get_gic_vcpu_ctrl_misr;
            vgic_misr_eoi \<leftarrow> return $ vgicHCREN;
            irq_idx \<leftarrow> return (if eisr0 \<noteq> 0 then word_ctz eisr0 else word_ctz eisr1 + 32);
            gic_vcpu_num_list_regs \<leftarrow> gets (arm_gicvcpu_numlistregs o arch_state);
            fault \<leftarrow> if flags && vgic_misr_eoi \<noteq> 0
                    then
                      if eisr0 = 0 \<and> eisr1 = 0 \<or> irq_idx \<ge> gic_vcpu_num_list_regs
                      then return $ VGICMaintenance None
                      else do
                        virq <- do_machine_op $ get_gic_vcpu_ctrl_lr (of_nat irq_idx);
                        virqen <- return $ virqSetEOIIRQEN virq 0;
                        do_machine_op $ set_gic_vcpu_ctrl_lr (of_nat irq_idx) virqen;
                        vgic_update_lr vcpu_ptr irq_idx virqen;
                        return $ VGICMaintenance $ Some $ of_nat irq_idx
                      od
                    else return $ VGICMaintenance None;

            ct \<leftarrow> gets cur_thread;
            st \<leftarrow> get_thread_state ct;
            \<comment> \<open>until a proof links active current vcpu to runnable current thread, we need this
               check: @{term handle_fault} needs a runnable current thread\<close>
            when (runnable st) $ handle_fault ct $ ArchFault fault
          od
        | _ \<Rightarrow> return ()
   od"

definition vppi_event :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "vppi_event irq = do
     cur_vcpu \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
     case cur_vcpu
       of Some (vcpu_ptr, True) \<Rightarrow> do
            do_machine_op $ maskInterrupt True irq;
            vppi \<leftarrow> return $ the $ irq_vppi_event_index irq;
            vcpu_update vcpu_ptr
                        (\<lambda>vcpu. vcpu\<lparr> vcpu_vppi_masked := (vcpu_vppi_masked vcpu)(vppi := True) \<rparr>);
            ct \<leftarrow> gets cur_thread;
            st \<leftarrow> get_thread_state ct;
            \<comment> \<open>until a proof links active current vcpu to runnable current thread, we need this
               check: @{term handle_fault} needs a runnable current thread\<close>
            when (runnable st) $ handle_fault ct $ ArchFault $ VPPIEvent irq
          od
        | _ \<Rightarrow> return ()
   od"

definition handle_reserved_irq :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "handle_reserved_irq irq \<equiv> do
     when (irq = irqVGICMaintenance) vgic_maintenance;
     when (irq_vppi_event_index irq \<noteq> None) $ vppi_event irq
   od"

fun arch_invoke_irq_handler :: "irq_handler_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arch_invoke_irq_handler (ACKIrq irq) =
     do_machine_op (if Kernel_Config.config_ARM_GIC_V3
                    then deactivateInterrupt irq
                    else maskInterrupt False irq)"
| "arch_invoke_irq_handler _ = return ()"

definition arch_mask_irq_signal :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "arch_mask_irq_signal irq \<equiv>
     when (\<not>Kernel_Config.config_ARM_GIC_V3) (do_machine_op $ maskInterrupt True irq)"

end

end
