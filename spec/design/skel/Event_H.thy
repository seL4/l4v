(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Kernel Events"

theory Event_H
imports "../machine/MachineExports"
begin

text {*
  \label{sec:Event_H}
 
  These are the user-level and machine generated events the kernel reacts to.
*}

#INCLUDE_HASKELL SEL4/API/Syscall.lhs ONLY Event Syscall

end
