(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * The basic monads used in capDL
 *)

theory Monads_D
imports
  Types_D
  "Monads.NonDetMonadVCG"
begin

(* Kernel state monad *)
type_synonym 'a k_monad = "(cdl_state, 'a) nondet_monad"

datatype cdl_except_error = ExceptError
datatype cdl_preempt_error = PreemptError
datatype cdl_fault_error = FaultError

(* Exception monad, no further exception information *)
type_synonym 'a except_monad = "(cdl_state, cdl_except_error + 'a) nondet_monad"

(* Exception monad, no further exception information *)
type_synonym 'a preempt_monad = "(cdl_state, cdl_preempt_error + 'a) nondet_monad"

(* Exception monad, no further exception information *)
type_synonym 'a fault_monad =  "(cdl_state, cdl_fault_error + 'a) nondet_monad"

abbreviation
  throw :: "(cdl_state, 'a + 'b) nondet_monad" where
  "throw == throwError undefined"

text \<open>Allow preemption at this point.\<close>
definition
  preemption_point :: "unit preempt_monad" where
 "preemption_point \<equiv> throw \<sqinter> returnOk ()"

(*
 * Convert an exception monad with aribtrary type into a
 * new exception monad with unit type.
 *)
definition
  unify_failure :: "('f + 'a) k_monad \<Rightarrow> (unit + 'a) k_monad" where
 "unify_failure m \<equiv> handleE' m (\<lambda>x. throwError ())"

text \<open>
  Convert a fault monad into an exception monad.
\<close>
definition
  fault_to_except :: "'a fault_monad \<Rightarrow> 'a except_monad"
where
  "fault_to_except m \<equiv> handleE' m (\<lambda>x. throw)"

(*
 * Non-deterministically select an item from the given set.
 * If the set if empty, return 'None'.
 *)
definition
  option_select :: "'a set \<Rightarrow> ('s, 'a option) nondet_monad"
where
  "option_select S \<equiv>
    if S = {} then
      return None
    else
      select S >>= (\<lambda>a. return (Some a))"

(* Return the given object, throwing an error if it is 'None'. *)
definition
  throw_on_none :: "'a option \<Rightarrow> ('e + 'a) k_monad"
where
  "throw_on_none x \<equiv>
    case x of
        None \<Rightarrow> throw
      | Some y \<Rightarrow> returnOk y"


end
