(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Specification of Inter-Process Communication.
*)

chapter "IPC"

theory Ipc_SA
imports "ASpec.Syscall_A"
begin


section \<open>Asynchronous Message Transfers\<close>

text \<open>

  \texttt{handle_fault} in \texttt{sep-abstract} always sets the thread state to
  \texttt{Inactive}. This is the same behaviour as \texttt{handle_double_fault} in the abstract
  specification.

  The two \texttt{handle_fault}s have the same behaviour under restricted capabilities because in
  the abstract specification \texttt{handle_fault} will call \texttt{handle_double_fault} in all
  cases except when the thread has an \texttt{EndpointCap}. Since \texttt{EndpointCap} is not part
  of the restricted capabilities their behaviour is the same. This means, the system assumes
  fully static virtual memory and no dynamic paging of any kind.
  Faulting threads will be disabled by the kernel.
\<close>

definition
  handle_fault :: "obj_ref \<Rightarrow> fault \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "handle_fault tptr ex \<equiv> set_thread_state tptr Inactive"

end
