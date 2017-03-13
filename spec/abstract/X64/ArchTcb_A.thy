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
Arch-specific functions for the abstract model of CSpace.
*)

chapter "Architecture-specific TCB functions"

theory ArchTcb_A
imports "../KHeap_A"
begin

context Arch begin global_naming X64_A

definition
  arch_tcb_set_ipc_buffer :: "machine_word \<Rightarrow> vspace_ref \<Rightarrow> (unit, 'a::state_ext) s_monad"
where
  "arch_tcb_set_ipc_buffer target ptr \<equiv> return ()"

definition
  sanitise_or_flags :: machine_word
where
  "sanitise_or_flags \<equiv> bit 1 || bit 9"

definition
  sanitise_and_flags :: machine_word
where
  "sanitise_and_flags \<equiv> mask 12 && ~~ bit 8 && ~~ bit 3 && ~~ bit 5"

(* FIXME x64: this is disgusting *)
definition
  sanitise_register :: "tcb \<Rightarrow> register \<Rightarrow> machine_word \<Rightarrow> machine_word"
where
  "sanitise_register t r v \<equiv>
    let val = (if (r = FaultIP \<or> r = NextIP) then
                if (v > 0x00007fffffffffff \<and> v < 0xffff800000000000) then 0 else v
              else v);
        val' = (if (r = TLS_BASE) then if (val > user_vtop) then user_vtop else val else val )
    in
      if r = FLAGS then (val' || sanitise_or_flags) && sanitise_and_flags else val'"


end
end
