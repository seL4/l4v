(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Arch Functions for cancelling IPC.
*)

chapter \<open>Arch IPC Cancelling\<close>

theory ArchIpcCancel_A
imports CSpaceAcc_A
begin

context Arch begin arch_global_naming (A)

definition
  set_ioport_mask :: "io_port \<Rightarrow> io_port \<Rightarrow> bool \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_ioport_mask f l val \<equiv> do
    allocated_ports \<leftarrow> gets (x64_allocated_io_ports \<circ> arch_state);
    ap' \<leftarrow> return (\<lambda>p. if p \<ge> f \<and> p \<le> l then val else allocated_ports p);
    modify (\<lambda>s. s \<lparr> arch_state := (arch_state s) \<lparr> x64_allocated_io_ports := ap' \<rparr>\<rparr>)
  od"

definition
  free_ioport_range :: "io_port \<Rightarrow> io_port \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "free_ioport_range f l \<equiv> set_ioport_mask f l False"

text \<open>Actions to be taken after a cap is deleted\<close>
definition
  arch_post_cap_deletion :: "arch_cap \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "arch_post_cap_deletion ac \<equiv> case ac of
       IOPortCap f l \<Rightarrow> free_ioport_range f l
     | _ \<Rightarrow> return ()"

text \<open>Arch specific generic object references not covered by generic references\<close>
datatype arch_gen_obj_ref = IOPortRef io_port

definition
  arch_gen_obj_refs :: "arch_cap \<Rightarrow> arch_gen_obj_ref set"
where
  "arch_gen_obj_refs ac \<equiv> case ac of
      IOPortCap f l \<Rightarrow> IOPortRef ` {f}
    | _ \<Rightarrow> {}"

definition
  arch_cap_cleanup_opt :: "arch_cap \<Rightarrow> cap"
where
  "arch_cap_cleanup_opt ac \<equiv> case ac of IOPortCap f l \<Rightarrow> ArchObjectCap (IOPortCap f l) | _ \<Rightarrow> NullCap"

end
end
