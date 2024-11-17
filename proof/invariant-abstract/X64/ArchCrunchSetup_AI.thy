(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchCrunchSetup_AI
imports
  "ASpec.Syscall_A"
  "Lib.Crunch_Instances_NonDet"
begin
context Arch begin arch_global_naming


crunch_ignore (add: debugPrint clearMemory invalidateTLB initL2Cache)

end

end
