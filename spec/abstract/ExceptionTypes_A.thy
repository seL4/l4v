(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Types of exceptions in the abstract model.
*)

chapter "Error and Fault Messages"

theory ExceptionTypes_A
imports MiscMachine_A
begin

arch_requalify_types (A) arch_fault

text \<open>
  There are two types of exceptions that can occur in the kernel:
  faults and errors. Faults are reported to the user's fault handler.
  Errors are reported to the user directly.

  Capability lookup failures can be be either fault or error,
  depending on context.
\<close>

datatype lookup_failure
     = InvalidRoot
     | MissingCapability nat
     | DepthMismatch nat nat
     | GuardMismatch nat "bool list"

datatype fault
         = CapFault obj_ref bool lookup_failure
         | UnknownSyscallException data
         | UserException data data
         | Timeout data
         | ArchFault arch_fault

datatype syscall_error
         = InvalidArgument nat
         | InvalidCapability nat
         | IllegalOperation
         | RangeError data data
         | AlignmentError
         | FailedLookup bool lookup_failure
         | TruncatedMessage
         | DeleteFirst
         | RevokeFirst
         | NotEnoughMemory data

text \<open>Create a message from a system-call failure to be returned to the
thread attempting the operation that failed.\<close>
primrec
  msg_from_lookup_failure :: "lookup_failure \<Rightarrow> data list"
where
  "msg_from_lookup_failure InvalidRoot           = [1]"
| "msg_from_lookup_failure (MissingCapability n) = [2, of_nat n]"
| "msg_from_lookup_failure (DepthMismatch n m)   = [3, of_nat n, of_nat m]"
| "msg_from_lookup_failure (GuardMismatch n g)   = [4, of_nat n, of_bl g, of_nat (size g)]"

primrec
  msg_from_syscall_error :: "syscall_error \<Rightarrow> (data \<times> data list)"
where
  "msg_from_syscall_error (InvalidArgument n)    = (1, [of_nat n])"
| "msg_from_syscall_error (InvalidCapability n)  = (2, [of_nat n])"
| "msg_from_syscall_error IllegalOperation       = (3, [])"
| "msg_from_syscall_error (RangeError minv maxv) = (4, [minv, maxv])"
| "msg_from_syscall_error AlignmentError         = (5, [])"
| "msg_from_syscall_error (FailedLookup s lf)    = (6, [if s then 1 else 0]@(msg_from_lookup_failure lf))"
| "msg_from_syscall_error TruncatedMessage       = (7, [])"
| "msg_from_syscall_error DeleteFirst            = (8, [])"
| "msg_from_syscall_error RevokeFirst            = (9, [])"
| "msg_from_syscall_error (NotEnoughMemory n)    = (10, [n])"

end
