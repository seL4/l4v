(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "SchedContexts"

theory SchedContext_H

imports
  SchedContextDecls_H
  TCBDecls_H
  ThreadDecls_H
  NotificationDecls_H
  Reply_H
  VSpace_H

begin

context begin interpretation Arch .
requalify_consts
  kernelWCETTicks
  kernelWCETUs
  ticksToUs
  maxTicksToUs
  getCurrentTime
  maxPeriodUs
end

#INCLUDE_HASKELL SEL4/Object/SchedContext.lhs bodies_only NOT preemptionPoint workUnitsLimit

defs preemptionPoint_def:
"preemptionPoint\<equiv> (doE
    liftE $ modifyWorkUnits (\<lambda>op. op + 1);
    workUnits \<leftarrow> liftE $ getWorkUnits;
    whenE (workUnitsLimit \<le> workUnits) $ (doE
      liftE $ setWorkUnits 0;
      preempt \<leftarrow> liftE $ doMachineOp (getActiveIRQ True);
      (case preempt of
            Some irq \<Rightarrow>   throwError ()
          | None \<Rightarrow>   (doE
             csc \<leftarrow> liftE $ getCurSc;
             active \<leftarrow> liftE $ scActive csc;
             consumed \<leftarrow> liftE $ getConsumedTime;
             sufficient \<leftarrow> liftE $ refillSufficient csc consumed;
             domExp \<leftarrow> liftE $isCurDomainExpired;
             if (Not (active \<and> sufficient) \<or> domExp)
                  then throwError ()
                  else returnOk ()
          odE)
          )
    odE)
odE)"

end
