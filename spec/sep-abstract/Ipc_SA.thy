(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
Specification of Inter-Process Communication.
*)

chapter "IPC"

theory Ipc_SA
imports "../abstract/Syscall_A"
begin


section {* Asynchronous Message Transfers *}

text {*

  \texttt{handle_fault} in \texttt{sep-abstract} always sets the thread state to
  \texttt{Inactive}. This is the same behaviour as \texttt{handle_double_fault} in the abstract
  specification.

  The two \texttt{handle_fault}s have the same behaviour under restricted capabilities because in
  the abstract specification \texttt{handle_fault} will call \texttt{handle_double_fault} in all
  cases except when the thread has an \texttt{EndpointCap}. Since \texttt{EndpointCap} is not part
  of the restricted capabilities their behaviour is the same. This means, the system assumes
  fully static virtual memory and no dynamic paging of any kind. 
  Faulting threads will be disabled by the kernel.
*}

definition
  handle_fault :: "obj_ref \<Rightarrow> fault \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "handle_fault tptr ex \<equiv> set_thread_state tptr Inactive"

end
