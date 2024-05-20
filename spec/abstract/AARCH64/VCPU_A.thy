(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>VCPU\<close>

theory VCPU_A
imports
  TcbAcc_A
  InvocationLabels_A
begin

text \<open>This is used by some decode functions. VCPU decode functions are the first that need to bounds
  check IRQs from the user.\<close>
definition arch_check_irq :: "data \<Rightarrow> (unit,'z::state_ext) se_monad" where
  "arch_check_irq irq \<equiv> whenE (irq > maxIRQ \<or> irq < ucast minIRQ)
                          $ throwError (RangeError (ucast minIRQ) maxIRQ)"

context Arch begin global_naming AARCH64_A

section "VCPU"

subsection "VCPU: Set TCB"

definition decode_vcpu_set_tcb ::
  "arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
  where
  "decode_vcpu_set_tcb cap extras \<equiv> case (cap, extras) of
     (VCPUCap v, fs#_) \<Rightarrow> (case fs of
           (ThreadCap t, _) \<Rightarrow> returnOk $ InvokeVCPU $ VCPUSetTCB v t
         | _ \<Rightarrow> throwError IllegalOperation)
   | (VCPUCap v, _) \<Rightarrow> throwError TruncatedMessage
   | _ \<Rightarrow> throwError IllegalOperation"

text \<open>VCPU objects can be associated with and dissociated from TCBs.
  It is not possible to dissociate a VCPU and a TCB by using setTCB.
  Final outcome has to be an associated TCB and VCPU.
  The only way to get lasting dissociation is to delete the TCB or the VCPU. See ArchVSpace\_A.\<close>


subsection "VCPU: Read/Write Registers"

definition read_vcpu_register :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> (machine_word,'z::state_ext) s_monad" where
  "read_vcpu_register vcpu_ptr reg \<equiv> do
     cur_vcpu \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
     (on_cur_vcpu, active) \<leftarrow> return (case cur_vcpu of
         Some (vcpu_ptr', a) \<Rightarrow> (vcpu_ptr' = vcpu_ptr, a)
       | _ \<Rightarrow> (False, False));

     if on_cur_vcpu
       then if vcpuRegSavedWhenDisabled reg \<and> \<not>active
              then vcpu_read_reg vcpu_ptr reg
              else do_machine_op $ readVCPUHardwareReg reg
       else vcpu_read_reg vcpu_ptr reg
  od"

definition
  write_vcpu_register :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "write_vcpu_register vcpu_ptr reg val \<equiv>
  do
     cur_vcpu \<leftarrow> gets (arm_current_vcpu o arch_state);
     (on_cur_vcpu, active) \<leftarrow> return (case cur_vcpu of
         Some (cv, a) \<Rightarrow> (cv = vcpu_ptr, a)
       | _ \<Rightarrow> (False, False));

     if on_cur_vcpu
       then if vcpuRegSavedWhenDisabled reg \<and> \<not>active
         then vcpu_write_reg vcpu_ptr reg val
         else do_machine_op $ writeVCPUHardwareReg reg val
       else vcpu_write_reg vcpu_ptr reg val
  od"

definition decode_vcpu_read_register ::
  "machine_word list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
  where
  "decode_vcpu_read_register args cap \<equiv> case (args, cap) of
      (reg#_, VCPUCap p) \<Rightarrow> if fromEnum (maxBound::vcpureg) < unat reg
                           then throwError (InvalidArgument 1)
                           else returnOk $ InvokeVCPU $ VCPUReadRegister p $ toEnum (unat reg)
    | (_, _) \<Rightarrow> throwError TruncatedMessage"

definition decode_vcpu_write_register :: "machine_word list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
  where
  "decode_vcpu_write_register args cap \<equiv> case (args, cap) of
    (reg#val#_, VCPUCap p) \<Rightarrow> if fromEnum (maxBound::vcpureg) < unat reg
                              then throwError (InvalidArgument 1)
                              else returnOk $ InvokeVCPU $ VCPUWriteRegister p (toEnum (unat reg)) val
  | (_, _) \<Rightarrow> throwError TruncatedMessage"

definition invoke_vcpu_read_register :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> (data list, 'z::state_ext) s_monad"
  where
  "invoke_vcpu_read_register v reg \<equiv> do
     val \<leftarrow> read_vcpu_register v reg;
     return [val]
   od"

definition
  invoke_vcpu_write_register :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "invoke_vcpu_write_register v reg val \<equiv>  write_vcpu_register v reg val"

text \<open>VCPU : inject IRQ\<close>

(* This following function does not correspond to exactly what the C does, but
   it is the value that is stored inside of lr in the vgic  *)
definition make_virq :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> virq" where
  "make_virq grp prio irq \<equiv>
    let
      groupShift = 30;
      prioShift = 23;
      irqPending = 1 << 28;
      eoiirqen = 1 << 19
    in ((grp && 1) << groupShift) || ((prio && 0x1F) << prioShift) || (irq && 0x3FF)
       || irqPending || eoiirqen"

definition virq_type :: "virq \<Rightarrow> nat" where
  "virq_type virq \<equiv> unat ((virq >> 28) && 3)"

definition is_virq_active :: "virq \<Rightarrow> bool" where
  "is_virq_active virq \<equiv> virq_type virq = 2"

definition decode_vcpu_inject_irq ::
  "obj_ref list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
  where
  "decode_vcpu_inject_irq ptrs cap \<equiv> case (ptrs, cap) of
  (mr0 # _, VCPUCap p) \<Rightarrow> doE
     vid \<leftarrow> returnOk (mr0 && 0xFFFF);
     priority \<leftarrow> returnOk ((mr0 >> 16) && 0xFF);
     group \<leftarrow> returnOk ((mr0 >> 24) && 0xFF);
     index \<leftarrow> returnOk ((mr0 >> 32) && 0xFF);
     range_check vid 0 ((1 << 10) - 1);
     range_check priority 0 31;
     range_check group 0 1;
     num_list_regs \<leftarrow> liftE $ gets (arm_gicvcpu_numlistregs \<circ> arch_state);
     whenE (index \<ge> of_nat num_list_regs) $
        (throwError $ RangeError 0 (of_nat num_list_regs - 1));

     vcpu \<leftarrow> liftE $ get_vcpu p;
     vcpuLR \<leftarrow> returnOk (vgic_lr $ vcpu_vgic $ vcpu);

     whenE (is_virq_active (vcpuLR (unat index))) $ throwError DeleteFirst;

     virq \<leftarrow> returnOk (make_virq group priority vid);
     returnOk $ InvokeVCPU $ VCPUInjectIRQ p (unat index) virq
  odE
| _ \<Rightarrow> throwError TruncatedMessage"

definition invoke_vcpu_inject_irq :: "obj_ref \<Rightarrow> nat \<Rightarrow> virq \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invoke_vcpu_inject_irq vr index virq \<equiv> do
    cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
    if (cur_v \<noteq> None \<and> fst (the cur_v) = vr)
    then do_machine_op $ set_gic_vcpu_ctrl_lr (of_nat index) virq
    else vgic_update_lr vr index virq
   od"

text \<open>VCPU : acknowledge VPPI\<close>

definition decode_vcpu_ack_vppi ::
  "obj_ref list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
  where
  "decode_vcpu_ack_vppi mrs cap \<equiv>
     case (mrs, cap)
       of (mr0 # _, VCPUCap vcpu_ptr) \<Rightarrow> doE
           arch_check_irq mr0;
           (case irq_vppi_event_index (ucast mr0)
            of None \<Rightarrow> throwError $ InvalidArgument 0
             | Some vppi \<Rightarrow> returnOk $ InvokeVCPU $ VCPUAckVPPI vcpu_ptr vppi)
         odE
       | _ \<Rightarrow> throwError TruncatedMessage"

definition invoke_vcpu_ack_vppi :: "obj_ref \<Rightarrow> vppievent_irq \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "invoke_vcpu_ack_vppi vcpu_ptr vppi =
     vcpu_update vcpu_ptr
                 (\<lambda>vcpu. vcpu\<lparr> vcpu_vppi_masked := (vcpu_vppi_masked vcpu)(vppi := False) \<rparr>)"

text \<open>VCPU perform and decode main functions\<close>

definition
  perform_vcpu_invocation :: "vcpu_invocation \<Rightarrow> (data list,'z::state_ext) s_monad" where
  "perform_vcpu_invocation iv \<equiv> case iv of
     VCPUSetTCB vcpu tcb \<Rightarrow> do associate_vcpu_tcb vcpu tcb; return [] od
   | VCPUReadRegister vcpu reg \<Rightarrow> invoke_vcpu_read_register vcpu reg
   | VCPUWriteRegister vcpu reg val \<Rightarrow> do invoke_vcpu_write_register vcpu reg val; return [] od
   | VCPUInjectIRQ vcpu index vir \<Rightarrow> do invoke_vcpu_inject_irq vcpu index vir; return [] od
   | VCPUAckVPPI vcpu vppi \<Rightarrow> do invoke_vcpu_ack_vppi vcpu vppi; return [] od"

definition decode_vcpu_invocation ::
  "machine_word \<Rightarrow> machine_word list \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
   (arch_invocation,'z::state_ext) se_monad"
  where
  "decode_vcpu_invocation label args cap extras \<equiv> case cap of
  VCPUCap _ \<Rightarrow> (case invocation_type label of
      ArchInvocationLabel ARMVCPUSetTCB \<Rightarrow> decode_vcpu_set_tcb cap extras
    | ArchInvocationLabel ARMVCPUReadReg \<Rightarrow> decode_vcpu_read_register args cap
    | ArchInvocationLabel ARMVCPUWriteReg \<Rightarrow> decode_vcpu_write_register args cap
    | ArchInvocationLabel ARMVCPUInjectIRQ \<Rightarrow> decode_vcpu_inject_irq args cap
    | ArchInvocationLabel ARMVCPUAckVPPI \<Rightarrow> decode_vcpu_ack_vppi args cap
    |  _ \<Rightarrow> throwError IllegalOperation)
  | _ \<Rightarrow> throwError IllegalOperation"

end

end
