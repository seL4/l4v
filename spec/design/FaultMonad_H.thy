(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file FaultMonad_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "The Fault Monad"

theory FaultMonad_H
imports KernelStateData_H Fault_H
begin

context begin interpretation Arch .
requalify_consts
  getActiveIRQ
end

type_synonym ('f, 'a) kernel_f = "('f + 'a) kernel"

translations
  (type) "('f,'a) kernel_f" <= (type) "('f + 'a) kernel"

subsubsection "Error Handling"

definition
  withoutFailure :: "'a kernel \<Rightarrow> ('f, 'a) kernel_f"
where
  withoutFailure_def[simp]:
  "withoutFailure \<equiv> liftE"

definition
  throw :: "'f \<Rightarrow> ('f, 'a) kernel_f"
where
  throw_def[simp]:
  "throw \<equiv> throwError"

definition
  catchFailure :: "('f, 'a) kernel_f \<Rightarrow> ('f \<Rightarrow> 'a kernel) \<Rightarrow> 'a kernel"
where
  catchFailure_def[simp]:
 "catchFailure \<equiv> catch"

definition
  rethrowFailure :: "('f1 \<Rightarrow> 'f2) \<Rightarrow> ('f1, 'a) kernel_f \<Rightarrow> ('f2, 'a) kernel_f"
where
 "rethrowFailure f m \<equiv> m <handle2> (throwError \<circ> f)"

definition
  ignoreFailure :: "( 'f , unit ) kernel_f \<Rightarrow> unit kernel"
where
  "ignoreFailure x \<equiv> (catchFailure x (const (return ())))"


definition
capFaultOnFailure :: "cptr \<Rightarrow> bool \<Rightarrow> ( lookup_failure , 'a ) kernel_f \<Rightarrow> ( fault , 'a ) kernel_f"
where
"capFaultOnFailure cptr rp \<equiv> rethrowFailure $ CapFault cptr rp"

definition
lookupErrorOnFailure :: "bool \<Rightarrow> ( lookup_failure , 'a ) kernel_f \<Rightarrow> ( syscall_error , 'a ) kernel_f"
where
"lookupErrorOnFailure isSource \<equiv> rethrowFailure $ FailedLookup isSource"

definition
constOnFailure :: "'a \<Rightarrow> ( 'f , 'a ) kernel_f \<Rightarrow> 'a kernel"
where
"constOnFailure x m\<equiv> m `~catchFailure~` (const $ return x)"

definition
unifyFailure :: "( 'f , 'a ) kernel_f \<Rightarrow> ( unit , 'a ) kernel_f"
where
"unifyFailure\<equiv> rethrowFailure $ const ()"

definition
rangeCheck :: "('a :: integral) \<Rightarrow> ('b :: integral) \<Rightarrow> 'b \<Rightarrow> ( syscall_error , unit ) kernel_f"
where
"rangeCheck value minV maxV \<equiv>
    unlessE (value \<ge> fromIntegral minV \<and> value \<le> fromIntegral maxV) $
        throw $ RangeError (fromIntegral minV) (fromIntegral maxV)"


definition
  nullCapOnFailure :: "('f, capability) kernel_f \<Rightarrow> capability kernel"
where
 "nullCapOnFailure m \<equiv> m <catch> (\<lambda>x. return NullCap)"

definition
  emptyOnFailure :: "('f, 'a list) kernel_f \<Rightarrow> 'a list kernel"
where
 "emptyOnFailure m \<equiv> m <catch> (\<lambda>x. return [])"

definition
  nothingOnFailure :: "('f, 'a option) kernel_f \<Rightarrow> 'a option kernel"
where
 "nothingOnFailure m \<equiv> m <catch> (\<lambda>x. return Nothing)"

subsection "Preemption"

type_synonym 'a kernel_p = "(irq + 'a) kernel"

translations
  (type) "'a kernel_p" <= (type) "(irq + 'a) kernel"

definition
  withoutPreemption :: "'a kernel \<Rightarrow> 'a kernel_p"
where
  withoutPreemption_def[simp]:
 "withoutPreemption \<equiv> liftE"

definition
  workUnitsLimit :: machine_word
where
  "workUnitsLimit \<equiv> 0x64"

definition
  preemptionPoint :: "unit kernel_p"
where
  "preemptionPoint \<equiv> doE
     liftE $ modifyWorkUnits (\<lambda>u. u + 1);
     workUnits <- liftE $ getWorkUnits;
     whenE (workUnitsLimit <= workUnits) $ doE
       liftE $ setWorkUnits 0;
       preempt <- liftE $ doMachineOp getActiveIRQ;
       case preempt of
           Some irq => throwError irq
           | None => returnOk ()
     odE
   odE"


end
