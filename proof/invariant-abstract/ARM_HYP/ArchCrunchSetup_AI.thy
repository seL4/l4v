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


crunch_ignore (add: debugPrint invalidateLocalTLB_ASID invalidateLocalTLB_VAASID cleanByVA
  cleanByVA_PoU invalidateByVA invalidateByVA_I invalidate_I_PoU
  cleanInvalByVA branchFlush clean_D_PoU cleanInvalidate_D_PoC cleanInvalidateL2Range
  invalidateL2Range cleanL2Range flushBTAC writeContextID isb dsb dmb
  setHardwareASID setCurrentPDPL2 clearMemory)

end

end
