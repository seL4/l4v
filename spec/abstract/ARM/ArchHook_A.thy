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
Top-level system call interface.
*)

chapter "Arch-specific definitions of kernel entry/exit hooks"

theory ArchHook_A
imports
  "../Schedule_A"
begin

context Arch begin global_naming ARM_A

text {* Kernel entry/exit hooks *}

definition c_entry_hook :: "(unit,'z::state_ext_sched) s_monad"
where "c_entry_hook \<equiv> return ()"

definition c_exit_hook :: "(unit,'z::state_ext_sched) s_monad"
where "c_exit_hook \<equiv> return ()"

end

end
