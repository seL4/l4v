(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchCrunchSetup_AI
imports
  "../../../spec/abstract/Syscall_A"
  "../../../lib/Crunch"
begin
context Arch begin global_naming X64


crunch_ignore (add: debugPrint clearMemory invalidateTLB initL2Cache)

end

end