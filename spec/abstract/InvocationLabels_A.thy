(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 Generic functions for invocation labels
*)

chapter "Kernel Object Invocations"

theory InvocationLabels_A
imports
  MiscMachine_A
  "ExecSpec.ArchLabelFuns_H"
begin

definition
  invocation_type :: "data \<Rightarrow> invocation_label"
where
 "invocation_type x \<equiv> if \<exists>(v :: invocation_label). fromEnum v = data_to_nat x
                      then toEnum (data_to_nat x) else GenInvocationLabel InvalidInvocation"

definition
  gen_invocation_type :: "data \<Rightarrow> gen_invocation_labels"
where
 "gen_invocation_type x \<equiv>
   case invocation_type x of
     GenInvocationLabel l \<Rightarrow> l
   | ArchInvocationLabel _ \<Rightarrow> InvalidInvocation"

end
