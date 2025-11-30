(*
 * Copyright 2024, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "AARCH64 FPU Functions"

theory FPU_A
imports
  KHeap_A
begin

context Arch begin arch_global_naming (A)

definition save_fpu_state :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "save_fpu_state t \<equiv> do
     fpu_state \<leftarrow> do_machine_op readFpuState;
     as_user t (setFPUState fpu_state)
   od"

definition load_fpu_state :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "load_fpu_state t \<equiv> do
     fpu_state \<leftarrow> as_user t getFPUState;
     do_machine_op (writeFpuState fpu_state)
   od"

definition set_arm_current_fpu_owner :: "obj_ref option \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_arm_current_fpu_owner new_owner \<equiv> do
     cur_fpu_owner \<leftarrow> gets (arm_current_fpu_owner \<circ> arch_state);
     maybeM (arch_thread_set (tcb_cur_fpu_update \<bottom>)) cur_fpu_owner;
     modify (\<lambda>s. s \<lparr>arch_state := arch_state s\<lparr>arm_current_fpu_owner := new_owner\<rparr>\<rparr>);
     maybeM (arch_thread_set (tcb_cur_fpu_update \<top>)) new_owner
   od"

\<comment> \<open>FIXME FPU: maybe use an if instead of the case (depends on if wpc or if\_split is easier)\<close>
definition switch_local_fpu_owner :: "obj_ref option \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "switch_local_fpu_owner new_owner \<equiv> do
     cur_fpu_owner \<leftarrow> gets (arm_current_fpu_owner \<circ> arch_state);
     do_machine_op enableFpu;
     maybeM save_fpu_state cur_fpu_owner;
     case new_owner of
       None \<Rightarrow> do_machine_op disableFpu
       | Some tcb_ptr \<Rightarrow> load_fpu_state tcb_ptr;
     set_arm_current_fpu_owner new_owner
   od"

definition fpu_release :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "fpu_release thread_ptr \<equiv> do
     cur_fpu_owner \<leftarrow> gets (arm_current_fpu_owner \<circ> arch_state);
     when (cur_fpu_owner = Some thread_ptr) $ switch_local_fpu_owner None
   od"

definition lazy_fpu_restore :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "lazy_fpu_restore thread_ptr \<equiv> do
     flags \<leftarrow> thread_get tcb_flags thread_ptr;
     if FpuDisabled \<in> flags
     then do_machine_op disableFpu
     else do
       cur_fpu_owner \<leftarrow> gets (arm_current_fpu_owner \<circ> arch_state);
       if cur_fpu_owner = Some thread_ptr
       then do_machine_op enableFpu
       else switch_local_fpu_owner (Some thread_ptr)
     od
   od"

end

end