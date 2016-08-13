(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
 Generic functions for invocation labels
*)

chapter "Kernel Object Invocations"

theory InvocationLabels_A
imports
  MiscMachine_A
  "../design/$L4V_ARCH/ArchLabelFuns_H"
begin

definition
  invocation_type :: "data \<Rightarrow> invocation_label"
where
 "invocation_type x \<equiv> if \<exists>(v :: invocation_label). fromEnum v = data_to_nat x
                      then toEnum (data_to_nat x) else InvalidInvocation"

end
