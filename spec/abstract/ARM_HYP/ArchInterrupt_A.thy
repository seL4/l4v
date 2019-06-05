(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
Formalisation of interrupt handling.
*)

chapter "Arch-specific Interrupts"

theory ArchInterrupt_A
imports "../Ipc_A"
begin

context Arch begin global_naming ARM_A

text \<open>VGIC Maintenance\<close>

definition
  virqSetEOIIRQEN :: "virq \<Rightarrow> 32 word \<Rightarrow> virq"
where
  "virqSetEOIIRQEN virq v =
    (if ((virq >> 28) && 3 = 3)
    then virq
    else (virq && ~~0x80000) || ((v << 19) && 0x80000))"

definition
  vgic_maintenance :: "(unit,'z::state_ext) s_monad"
where
  "vgic_maintenance = do
     ct \<leftarrow> gets cur_thread;
     st \<leftarrow> thread_get tcb_state ct;
     when (runnable st) $ do
       eisr0 \<leftarrow> do_machine_op $ get_gic_vcpu_ctrl_eisr0;
       eisr1 \<leftarrow> do_machine_op $ get_gic_vcpu_ctrl_eisr1;
       flags \<leftarrow> do_machine_op $ get_gic_vcpu_ctrl_misr;
       vgic_misr_eoi \<leftarrow> return $ 1;
       irq_idx \<leftarrow> return (if eisr0 \<noteq> 0 then word_ctz eisr0 else word_ctz eisr1 + 32);
       gic_vcpu_num_list_regs \<leftarrow> gets (arm_gicvcpu_numlistregs o arch_state);

       fault \<leftarrow>
           if flags && vgic_misr_eoi \<noteq> 0
           then
                if eisr0 = 0 \<and> eisr1 = 0 \<or>
                   irq_idx \<ge> gic_vcpu_num_list_regs
                   then return $ VGICMaintenance None
                   else do
                     virq <- do_machine_op $ get_gic_vcpu_ctrl_lr (of_nat irq_idx);
                     virqen <- return $ virqSetEOIIRQEN virq 0;
                     do_machine_op $ set_gic_vcpu_ctrl_lr (of_nat irq_idx) virqen;
                     cur_vcpu \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
                     case cur_vcpu of
                         Some (vr, True) \<Rightarrow> vgic_update_lr vr irq_idx virqen
                       | _ \<Rightarrow> return ();
                     return $ VGICMaintenance $ Some $ of_nat irq_idx
                   od
           else return $ VGICMaintenance None;
       ct \<leftarrow> gets cur_thread;
       handle_fault ct $ ArchFault fault
     od
   od"

definition
  handle_reserved_irq :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "handle_reserved_irq irq \<equiv> if irq = irqVGICMaintenance then vgic_maintenance else return ()"

end


end
