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
  read_vcpu_register :: "obj_ref \<Rightarrow> (machine_word,'z::state_ext) s_monad"
where
  "read_vcpu_register vcpu \<equiv>
  do
    v \<leftarrow> get_vcpu vcpu;
    return $ vcpu_sctlr v
  od"

definition
  write_vcpu_register :: "obj_ref \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "write_vcpu_register vcpu val \<equiv>
  do
    v \<leftarrow> get_vcpu vcpu;
    val' \<leftarrow> return (case register_mask of
              None \<Rightarrow> val
            | Some m \<Rightarrow> (vcpu_sctlr v) && m || val && ~~m);
    set_vcpu vcpu (v\<lparr> vcpu_sctlr := val' \<rparr> )
  od"

text {*Currently, there is only one VCPU register available for reading/writing by the user: cpx.sctlr. *}

definition decode_vcpu_read_register :: "obj_ref list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_vcpu_read_register ptrs cap \<equiv> case (ptrs, cap) of
      (_, VCPUCap p) \<Rightarrow> returnOk $ InvokeVCPU $ VCPUReadRegister p
    | (_, _) \<Rightarrow> throwError TruncatedMessage"

definition decode_vcpu_write_register :: "obj_ref list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_vcpu_write_register ptrs cap \<equiv> case (ptrs, cap) of
    (val # _, VCPUCap p) \<Rightarrow> returnOk $ InvokeVCPU $ VCPUWriteRegister p val
  | (_, _) \<Rightarrow> throwError TruncatedMessage"

definition invoke_vcpu_read_register :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where "invoke_vcpu_read_register v \<equiv> do
   ct \<leftarrow> gets cur_thread;
   cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
   (case cur_v of
      Some (vr, _) \<Rightarrow> vcpu_clean_invalidate_active
    | None \<Rightarrow> return ());
   val \<leftarrow> read_vcpu_register v;
   as_user ct $ set_register (hd msg_registers) $ val;
   let msg = MI 1 0 0 0 (* FIXME ARMHYP: is this correct? *)
   in do set_message_info ct msg;
         set_thread_state ct Running od
od"

definition invoke_vcpu_write_register :: "obj_ref \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
where "invoke_vcpu_write_register v val \<equiv> do
   cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
   (case cur_v of
      Some (vr, _) \<Rightarrow> vcpu_clean_invalidate_active
    | None \<Rightarrow> return ());
   write_vcpu_register v val;
   ct \<leftarrow> gets cur_thread;
   set_thread_state ct Restart
   od"

text {* VCPU : inject IRQ *}

(* ARMHYP FIXME see comment in VCPU_H *)
definition make_virq :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> virq" where
  "make_virq grp prio irq \<equiv>
  let
    groupShift = 30;
    prioShift = 23;
    irqPending = 1 << (28 - 1);
    eoiirqen = 1 << (19 - 1)
  in (grp << groupShift) || (prio << prioShift) || irq || irqPending || eoiirqen"


definition decode_vcpu_inject_irq :: "obj_ref list \<Rightarrow> arch_cap \<Rightarrow> (arch_invocation,'z::state_ext) se_monad"
where
  "decode_vcpu_inject_irq ptrs cap \<equiv> case (ptrs, cap) of
  (mr0 # mr1 # _, VCPUCap p) \<Rightarrow> doE
     vid \<leftarrow> returnOk (mr0 && 0xFFFF);
     priority \<leftarrow> returnOk ((mr0 >> 16) && 0xFF);
     group \<leftarrow> returnOk ((mr0 >> 24) && 0xFF);
     index \<leftarrow> returnOk (mr1 && 0xFF);
     range_check vid 0 (1 << 10 - 1);
     range_check priority 0 31;
     range_check group 0 1;
     num_list_regs \<leftarrow> liftE $ gets (arm_gicvcpu_numlistregs \<circ> arch_state);
     range_check index 0 (of_nat num_list_regs);
     vcpu \<leftarrow> liftE $ get_vcpu p;
     vcpuLR \<leftarrow> returnOk (vgicLR $ vcpu_VGIC $ vcpu);

     whenE (the (vcpuLR (unat index)) && vgic_irq_mask = vgic_irq_active) $ throwError DeleteFirst;

     virq \<leftarrow> returnOk (make_virq group priority vid);
     returnOk $ InvokeVCPU $ VCPUInjectIRQ p (unat index) virq
  odE
| _ \<Rightarrow> throwError TruncatedMessage"

definition invoke_vcpu_inject_irq :: "obj_ref \<Rightarrow> nat \<Rightarrow> virq \<Rightarrow> (unit,'z::state_ext) s_monad"
where "invoke_vcpu_inject_irq vr index virq \<equiv> do
   cur_v \<leftarrow> gets (arm_current_vcpu \<circ> arch_state);
   (case cur_v of
      Some (vr, _) \<Rightarrow> do_machine_op $ set_gic_vcpu_ctrl_lr index virq
    | None \<Rightarrow> do
           vcpu \<leftarrow> get_vcpu vr;
           vcpuLR \<leftarrow> return (fun_upd (vgicLR $ vcpu_VGIC $ vcpu) index (Some virq));
           set_vcpu vr $ vcpu \<lparr> vcpu_VGIC := (vcpu_VGIC vcpu) \<lparr> vgicLR := vcpuLR \<rparr>\<rparr>
           od);
   ct \<leftarrow> gets cur_thread;
   set_thread_state ct Restart
   od"

text {* VCPU perform and decode main functions *}


definition
perform_vcpu_invocation :: "vcpu_invocation \<Rightarrow> (unit,'z::state_ext) s_monad" where
"perform_vcpu_invocation iv \<equiv> case iv of
    VCPUSetTCB vcpu tcb \<Rightarrow> associate_vcpu_tcb tcb vcpu
  | VCPUReadRegister vcpu \<Rightarrow> invoke_vcpu_read_register vcpu
  | VCPUWriteRegister vcpu val \<Rightarrow> invoke_vcpu_write_register vcpu val
  | VCPUInjectIRQ vcpu _ _ \<Rightarrow> fail" (* FIXME ARMHYP: TODO *)


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