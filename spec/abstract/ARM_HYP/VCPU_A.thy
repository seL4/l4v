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
imports "../Structures_A" ArchTcbAcc_A
begin


text {*
  Some parts of some registers cannot be written by the user.
  Bits set in the mask will be preserved (used in vcpu_write_register).
*}
consts
  register_mask :: "hyper_reg \<Rightarrow> machine_word option"

context Arch begin global_naming ARM_A

section "VCPU"

text {* VCPU objects can be associated with and dissociated from TCBs. *}
definition
  vcpu_read_register :: "obj_ref \<Rightarrow> hyper_reg \<Rightarrow> (machine_word,'z::state_ext) s_monad"
where
  "vcpu_read_register vcpu reg \<equiv> do
    (_,regs) \<leftarrow> get_vcpu vcpu;
    return $ regs reg
  od"

definition
  vcpu_write_register :: "obj_ref \<Rightarrow> hyper_reg \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "vcpu_write_register vcpu reg val \<equiv>  do
    (tcb_opt,regs) \<leftarrow> get_vcpu vcpu;
    val' \<leftarrow> return (case register_mask reg of
              None \<Rightarrow> val
            | Some m \<Rightarrow> regs reg && m || val && ~~m);
    set_vcpu vcpu (tcb_opt,regs(reg := val'))
  od"

definition
perform_vcpu_invocation :: "vcpu_invocation \<Rightarrow> (machine_word list,'z::state_ext) s_monad" where
"perform_vcpu_invocation iv \<equiv> case iv of
    VCPUSetTCB vcpu tcb \<Rightarrow> do associate vcpu tcb; return [] od
  | VCPUInjectIRQ vcpu index group prio irq \<Rightarrow> do
      vgic_lr \<leftarrow> return $ ((ucast group :: machine_word) << 30) || (ucast prio << 23) || ucast irq
        || (1 << 28)(*FIXME VGIC_IRQ_PENDING*) || (1 << 19)(*FIXME VGIC_LR_EOIIRQEN*);
      (* FIXME ARMHYP: vcpu->vgic.lr[index] = vgic_lr *)
      tcb \<leftarrow> gets cur_thread;
      set_thread_state tcb Restart;
      return []
    od
  | VCPUReadRegister vcpu reg \<Rightarrow> do val \<leftarrow> vcpu_read_register vcpu reg; return [val] od
  | VCPUWriteRegister vcpu reg val \<Rightarrow> do vcpu_write_register vcpu reg val; return [] od"

end

end