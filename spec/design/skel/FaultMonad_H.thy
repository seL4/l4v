(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "The Fault Monad"

theory FaultMonad_H
imports
  KernelStateData_H
  Fault_H
begin

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


#INCLUDE_HASKELL_PREPARSE SEL4/API/Failures.lhs
#INCLUDE_HASKELL SEL4/Model/Failures.lhs NOT KernelF withoutFailure catchFailure throw rethrowFailure nullCapOnFailure nothingOnFailure ignoreFailure emptyOnFailure

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

type_synonym 'a kernel_p = "(unit + 'a) kernel"

translations
  (type) "'a kernel_p" <= (type) "(unit + 'a) kernel"

definition
  withoutPreemption :: "'a kernel \<Rightarrow> 'a kernel_p"
where
  withoutPreemption_def[simp]:
 "withoutPreemption \<equiv> liftE"

end
