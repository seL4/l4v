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
The only way to get lasting dissociation is to delete the TCB or the VCPU. *}

definition dissociate_vcpu_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where "dissociate_vcpu_tcb t v \<equiv> do
  t_vcpu \<leftarrow> arch_thread_get tcb_vcpu t;
  (v_tcb, reg) \<leftarrow> get_vcpu v;
  when (t_vcpu \<noteq> Some v \<or> v_tcb \<noteq> Some t) $ fail; (* TCB and VCPU not associated *)
  set_vcpu v (None, reg);
  arch_thread_set (\<lambda>x. x \<lparr> tcb_vcpu := None \<rparr>) t
od"


definition associate_vcpu_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where "associate_vcpu_tcb t v \<equiv> do
  t_vcpu \<leftarrow> arch_thread_get tcb_vcpu t;
  case t_vcpu of
    Some p \<Rightarrow> dissociate_vcpu_tcb t p
  | _ \<Rightarrow> return ();
  (v_tcb, reg) \<leftarrow> get_vcpu v;
  case v_tcb of
    Some p \<Rightarrow> dissociate_vcpu_tcb p v
  | _ \<Rightarrow> return ();
  arch_thread_set (\<lambda>x. x \<lparr> tcb_vcpu := Some v \<rparr>) t;
  set_vcpu v (Some t, reg)
  od"


subsection "VCPU: Read/Write Registers"

definition
  read_vcpu_register :: "obj_ref \<Rightarrow> (machine_word,'z::state_ext) s_monad"
where
  "read_vcpu_register vcpu \<equiv>
  do
    (_,val) \<leftarrow> get_vcpu vcpu;
    return $ val
  od"

definition
  write_vcpu_register :: "obj_ref \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "write_vcpu_register vcpu val \<equiv>
  do
    (tcb_opt,oldval) \<leftarrow> get_vcpu vcpu;
    val' \<leftarrow> return (case register_mask of
              None \<Rightarrow> val
            | Some m \<Rightarrow> oldval && m || val && ~~m);
    set_vcpu vcpu (tcb_opt,val')
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
   val \<leftarrow> read_vcpu_register v;
   as_user ct $ set_register (hd msg_registers) $ val;
   let msg = MI 1 0 0 0 (* FIXME ARMHYP: is this correct? *)
   in do set_message_info ct msg;
         set_thread_state ct Running od
od"

definition invoke_vcpu_write_register :: "obj_ref \<Rightarrow> machine_word \<Rightarrow> (unit,'z::state_ext) s_monad"
where "invoke_vcpu_write_register v val \<equiv> write_vcpu_register v val"

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
  | ArchInvocationLabel ARMVCPUInjectIRQ \<Rightarrow> fail (* FIXME ARMHYP TODO *)
  | ArchInvocationLabel ARMVCPUReadReg \<Rightarrow> decode_vcpu_read_register args cap
  | ArchInvocationLabel ARMVCPUWriteReg \<Rightarrow> decode_vcpu_write_register args cap
  |  _ \<Rightarrow> throwError IllegalOperation)
| _ \<Rightarrow> throwError IllegalOperation"

end

end