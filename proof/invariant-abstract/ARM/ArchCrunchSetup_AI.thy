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
context Arch begin global_naming ARM


crunch_ignore (add: debugPrint invalidateTLB_ASID invalidateTLB_VAASID cleanByVA
  cleanByVA_PoU invalidateByVA invalidateByVA_I invalidate_I_PoU
  cleanInvalByVA branchFlush clean_D_PoU cleanInvalidate_D_PoC cleanInvalidateL2Range
  invalidateL2Range cleanL2Range flushBTAC writeContextID isb dsb dmb
  setHardwareASID setCurrentPD clearMemory)

end

end