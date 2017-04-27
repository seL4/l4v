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
Functions to access kernel memory.
*)

chapter {* VCPU *}

theory VCPU_A
imports
  "../Structures_A"
  "../TcbAcc_A"
  "../InvocationLabels_A"
begin


text {*
  Some parts of some registers cannot be written by the user.
  Bits set in the mask will be preserved (used in vcpu\_write\_register).
*}
consts
  register_mask :: "machine_word option" (* no need for option? *)


context Arch begin global_naming ARM_A

section "VCPU"

subsection "VCPU: Set TCB"

definition decode_vcpu_set_tcb :: "arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where "decode_vcpu_set_tcb cap extras \<equiv> case (cap, extras) of
  (VCPUCap v, fs#_) \<Rightarrow> (case fs of
        (ThreadCap t, _) \<Rightarrow> returnOk $ InvokeVCPU $ VCPUSetTCB v t (* FIXME ARMHYP C code calls deriveCap here before checking the cap type, discuss with kernel team *)
      | _ \<Rightarrow> throwError IllegalOperation)
 |(VCPUCap v, _) \<Rightarrow> throwError TruncatedMessage
 | _ \<Rightarrow> throwError IllegalOperation"

text {* VCPU objects can be associated with and dissociated from TCBs. *}
text {*It is not possible to dissociate a VCPU and a TCB by using SetTCB.
Final outcome has to be an associated TCB and VCPU.
The only way to get lasting dissociation is to delete the TCB or the VCPU. See ArchVSpace\_A. *}


subsection "VCPU: Read/Write Registers"

definition
  read_vcpu_register :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> (machine_word,'z::state_ext) s_monad"
where
  "read_vcpu_register vcpu_ptr reg \<equiv>
  do
     cur_vcpu \<leftarrow> gets (arm_current_vcpu o arch_state);
     (on_cur_vcpu, active) \<leftarrow> return (case cur_vcpu of
          Some (vcpu_ptr', a) \<Rightarrow> (vcpu_ptr' = vcpu_ptr, a)
       |  _ \<Rightarrow> (False, False));

     if on_cur_vcpu
         then case reg of
                  VCPURegSCTLR \<Rightarrow> if active then do_machine_op getSCTLR
                                            else do
                                                vcpu \<leftarrow> get_vcpu vcpu_ptr;
                                                return $ vcpu_regs vcpu reg
                                            od
                | VCPURegLRsvc \<Rightarrow> do_machine_op get_lr_svc
                | VCPURegSPsvc \<Rightarrow> do_machine_op get_sp_svc
                | VCPURegLRabt \<Rightarrow> do_machine_op get_lr_abt
                | VCPURegSPabt \<Rightarrow> do_machine_op get_sp_abt
                | VCPURegLRund \<Rightarrow> do_machine_op get_lr_und
                | VCPURegSPund \<Rightarrow> do_machine_op get_sp_und
                | VCPURegLRirq \<Rightarrow> do_machine_op get_lr_irq
                | VCPURegSPirq \<Rightarrow> do_machine_op get_sp_irq
                | VCPURegLRfiq \<Rightarrow> do_machine_op get_lr_fiq
                | VCPURegSPfiq \<Rightarrow> do_machine_op get_sp_fiq
                | VCPURegR8fiq \<Rightarrow> do_machine_op get_r8_fiq
                | VCPURegR9fiq \<Rightarrow> do_machine_op get_r9_fiq
                | VCPURegR10fiq \<Rightarrow> do_machine_op get_r10_fiq
                | VCPURegR11fiq \<Rightarrow> do_machine_op get_r11_fiq
                | VCPURegR12fiq \<Rightarrow> do_machine_op get_r12_fiq
         else do
             vcpu \<leftarrow> get_vcpu vcpu_ptr;
             return $ vcpu_regs vcpu reg
         od
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
         then case reg of
                  VCPURegSCTLR \<Rightarrow> if active then do_machine_op $ setSCTLR val
                                            else do
                                                vcpu \<leftarrow> get_vcpu vcpu_ptr;
                                                set_vcpu vcpu_ptr $ vcpu \<lparr> vcpu_regs := (vcpu_regs vcpu) (reg := val) \<rparr>
                                            od
                | VCPURegLRsvc \<Rightarrow> do_machine_op $ set_lr_svc val
                | VCPURegSPsvc \<Rightarrow> do_machine_op $ set_sp_svc val
                | VCPURegLRabt \<Rightarrow> do_machine_op $ set_lr_abt val
                | VCPURegSPabt \<Rightarrow> do_machine_op $ set_sp_abt val
                | VCPURegLRund \<Rightarrow> do_machine_op $ set_lr_und val
                | VCPURegSPund \<Rightarrow> do_machine_op $ set_sp_und val
                | VCPURegLRirq \<Rightarrow> do_machine_op $ set_lr_irq val
                | VCPURegSPirq \<Rightarrow> do_machine_op $ set_sp_irq val
                | VCPURegLRfiq \<Rightarrow> do_machine_op $ set_lr_fiq val
                | VCPURegSPfiq \<Rightarrow> do_machine_op $ set_sp_fiq val
                | VCPURegR8fiq \<Rightarrow> do_machine_op $ set_r8_fiq val
                | VCPURegR9fiq \<Rightarrow> do_machine_op $ set_r9_fiq val
                | VCPURegR10fiq \<Rightarrow> do_machine_op $ set_r10_fiq val
                | VCPURegR11fiq \<Rightarrow> do_machine_op $ set_r11_fiq val
                | VCPURegR12fiq \<Rightarrow> do_machine_op $ set_r12_fiq val
         else do
             vcpu \<leftarrow> get_vcpu vcpu_ptr;
             set_vcpu vcpu_ptr $ vcpu \<lparr> vcpu_regs := (vcpu_regs vcpu) (reg := val) \<rparr>
         od
  od"

definition decode_vcpu_read_register :: "machine_word list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
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
where "invoke_vcpu_read_register v reg \<equiv> do
   val \<leftarrow> read_vcpu_register v reg;
   return [val]
od"

definition
  invoke_vcpu_write_register :: "obj_ref \<Rightarrow> vcpureg \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "invoke_vcpu_write_register v reg val \<equiv>  write_vcpu_register v reg val"

text {* VCPU : inject IRQ *}

(* ARMHYP FIXME see comment in VCPU_H *)
definition make_virq :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> virq" where
  "make_virq grp prio irq \<equiv>
  let
    groupShift = 30;
    prioShift = 23;
    irqPending = 1 << 28;
    eoiirqen = 1 << 19
  in ((grp && 1) << groupShift) || ((prio && 0x1F) << prioShift) || (irq && 0x3FF) || irqPending || eoiirqen"


definition decode_vcpu_inject_irq :: "obj_ref list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_vcpu_inject_irq ptrs cap \<equiv> case (ptrs, cap) of
  (mr0 # mr1 # _, VCPUCap p) \<Rightarrow> doE
     vid \<leftarrow> returnOk (mr0 && 0xFFFF);
     priority \<leftarrow> returnOk ((mr0 >> 16) && 0xFF);
     group \<leftarrow> returnOk ((mr0 >> 24) && 0xFF);
     index \<leftarrow> returnOk (mr1 && 0xFF);
     range_check vid 0 ((1 << 10) - 1);
     range_check priority 0 31;
     range_check group 0 1;
     num_list_regs \<leftarrow> liftE $ gets (arm_gicvcpu_numlistregs \<circ> arch_state);
     whenE (index \<ge> of_nat num_list_regs) $
        (throwError $ RangeError 0 (of_nat num_list_regs - 1));

     vcpu \<leftarrow> liftE $ get_vcpu p;
     vcpuLR \<leftarrow> returnOk (vgic_lr $ vcpu_vgic $ vcpu);

     whenE (vcpuLR (unat index) && vgic_irq_mask = vgic_irq_active) $ throwError DeleteFirst;

     virq \<leftarrow> returnOk (make_virq group priority vid);
     returnOk $ InvokeVCPU $ VCPUInjectIRQ p (unat index) virq
  odE
| _ \<Rightarrow> throwError TruncatedMessage"

definition invoke_vcpu_inject_irq :: "obj_ref \<Rightarrow> nat \<Rightarrow> virq \<Rightarrow> (unit,'z::state_ext) s_monad"
where "invoke_vcpu_inject_irq vr index virq \<equiv> do
   cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
   if (cur_v \<noteq> None \<and> fst (the cur_v) = vr)
   then do_machine_op $ set_gic_vcpu_ctrl_lr (of_nat index) virq
   else do
           vcpu \<leftarrow> get_vcpu vr;
           vcpuLR \<leftarrow> return $ (vgic_lr $ vcpu_vgic vcpu) (index := virq);
           set_vcpu vr $ vcpu \<lparr> vcpu_vgic := (vcpu_vgic vcpu) \<lparr> vgic_lr := vcpuLR \<rparr>\<rparr>
           od
   od"

text {* VCPU perform and decode main functions *}


definition
perform_vcpu_invocation :: "vcpu_invocation \<Rightarrow> (data list,'z::state_ext) s_monad" where
"perform_vcpu_invocation iv \<equiv> case iv of
    VCPUSetTCB vcpu tcb \<Rightarrow> do associate_vcpu_tcb vcpu tcb; return [] od
  | VCPUReadRegister vcpu reg \<Rightarrow> invoke_vcpu_read_register vcpu reg
  | VCPUWriteRegister vcpu reg val \<Rightarrow> do invoke_vcpu_write_register vcpu reg val; return [] od
  | VCPUInjectIRQ vcpu index vir \<Rightarrow> do invoke_vcpu_inject_irq vcpu index vir; return [] od"


definition decode_vcpu_invocation ::
"machine_word \<Rightarrow> machine_word list \<Rightarrow> arch_cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
"decode_vcpu_invocation label args cap extras \<equiv> case cap of
VCPUCap _ \<Rightarrow> (case invocation_type label of
    ArchInvocationLabel ARMVCPUSetTCB \<Rightarrow> decode_vcpu_set_tcb cap extras
  | ArchInvocationLabel ARMVCPUReadReg \<Rightarrow> decode_vcpu_read_register args cap
  | ArchInvocationLabel ARMVCPUWriteReg \<Rightarrow> decode_vcpu_write_register args cap
  | ArchInvocationLabel ARMVCPUInjectIRQ \<Rightarrow> decode_vcpu_inject_irq args cap (* ARMHYP *)
  |  _ \<Rightarrow> throwError IllegalOperation)
| _ \<Rightarrow> throwError IllegalOperation"

end

end