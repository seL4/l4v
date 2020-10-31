(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Kernel Events"

theory Event_H
imports MachineExports
begin

text \<open>
  \label{sec:Event_H}

  These are the user-level and machine generated events the kernel reacts to.
\<close>

#INCLUDE_HASKELL SEL4/API/Syscall.lhs ONLY Event Syscall

end
