(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

header "Initialisation"

theory KernelInit_H
imports
  KI_Decls_H
  ArchRetype_H
  Retype_H
  Config_H
begin

#INCLUDE_HASKELL SEL4/Kernel/Init.lhs bodies_only NOT funArray newKernelState distinct rangesBy InitData doKernelOp runInit

definition
  newKernelState :: "machine_word \<Rightarrow> kernel_state"
where
"newKernelState arg \<equiv> \<lparr>
        ksPSpace= newPSpace,
        gsUserPages= (\<lambda>x. None),
        gsCNodes= (\<lambda>x. None),
        ksDomScheduleIdx = 0,
        ksDomSchedule = [(0, 15), (2, 42), (1, 73)],
        ksCurDomain = 0,
        ksDomainTime = 15,
        ksReadyQueues= const [],
        ksCurThread= error [],
        ksIdleThread= error [],
        ksSchedulerAction= ResumeCurrentThread,
        ksInterruptState= error [],
        ksWorkUnitsCompleted= 0,
        ksArchState= fst (ArchStateData_H.newKernelState arg),
        ksMachineState= init_machine_state
	\<rparr>"

end
