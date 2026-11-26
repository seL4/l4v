(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* The basic monads used in capDL *)

theory Monads_D
  imports
    Types_D
    Monads.Nondet_In_Monad
    Monads.Nondet_VCG
begin

(* Kernel state monad *)
type_synonym 'a k_monad = "(cdl_state, 'a) nondet_monad"

datatype cdl_except_error = ExceptError
datatype cdl_preempt_error = PreemptError
datatype cdl_fault_error = FaultError

(* Exception monad, no further exception information *)
type_synonym 'a except_monad = "(cdl_state, cdl_except_error + 'a) nondet_monad"

(* Preemption monad *)
type_synonym 'a preempt_monad = "(cdl_state, cdl_preempt_error + 'a) nondet_monad"

(* Fault monad, no further fault information *)
type_synonym 'a fault_monad =  "(cdl_state, cdl_fault_error + 'a) nondet_monad"

abbreviation throw :: "(cdl_state, 'a + 'b) nondet_monad" where
  "throw == throwError undefined"

(* Convert a fault monad into an exception monad. *)
definition fault_to_except :: "'a fault_monad \<Rightarrow> 'a except_monad" where
  "fault_to_except m \<equiv> handleE' m (\<lambda>x. throw)"

(* Return the given object, throwing an error if it is 'None'. *)
definition throw_on_none :: "'a option \<Rightarrow> ('e + 'a) k_monad" where
  "throw_on_none x \<equiv> case x of None \<Rightarrow> throw | Some y \<Rightarrow> returnOk y"

end
