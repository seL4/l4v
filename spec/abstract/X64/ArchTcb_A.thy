(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Arch-specific functions for the abstract model of CSpace.
*)

chapter "Architecture-specific TCB functions"

theory ArchTcb_A
imports FPU_A
begin

context Arch begin arch_global_naming (A)

definition
  sanitise_or_flags :: machine_word
where
  "sanitise_or_flags \<equiv> bit 1 || bit 9"

definition
  sanitise_and_flags :: machine_word
where
  "sanitise_and_flags \<equiv> mask 12 && ~~ bit 8 && ~~ bit 3 && ~~ bit 5"

definition
  sanitise_register :: "bool \<Rightarrow> register \<Rightarrow> machine_word \<Rightarrow> machine_word"
where
  "sanitise_register t r v \<equiv>
    let val = (if r = FaultIP \<or> r = NextIP \<or> r = FS_BASE \<or> r = GS_BASE
               then if v > 0x00007fffffffffff \<and> v < 0xffff800000000000 then 0 else v
               else v)
    in
      if r = FLAGS then (val || sanitise_or_flags) && sanitise_and_flags else val"

definition
  arch_get_sanitise_register_info :: "obj_ref \<Rightarrow> (bool, 'a::state_ext) s_monad"
where
  "arch_get_sanitise_register_info t \<equiv> return False"

definition
  arch_post_modify_registers :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'a::state_ext) s_monad"
where
  "arch_post_modify_registers cur t \<equiv> when (t \<noteq> cur) $ as_user t $ setRegister ErrorRegister 0"

\<comment> \<open>The corresponding C code is not arch dependent and so is inline as part of invokeSetFlags\<close>
definition arch_post_set_flags :: "obj_ref \<Rightarrow> tcb_flags \<Rightarrow> (unit, 'a::state_ext) s_monad" where
  "arch_post_set_flags t flags \<equiv> do
     cur \<leftarrow> gets cur_thread;
     if FpuDisabled \<in> flags
     then fpu_release t
     else when (t = cur) (lazy_fpu_restore t)
   od"

(* As opposed to hyp-enabled architectures, we can keep this here as it does not cause circular
   function dependency. *)
definition arch_prepare_set_domain :: "obj_ref \<Rightarrow> domain \<Rightarrow> (unit, 'a::state_ext) s_monad" where
  "arch_prepare_set_domain t new_dom \<equiv> do
     cur_domain \<leftarrow> gets cur_domain;
     when (cur_domain \<noteq> new_dom) $ fpu_release t
   od"

end
end
