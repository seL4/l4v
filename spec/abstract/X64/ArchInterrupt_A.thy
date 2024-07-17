(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Formalisation of interrupt handling.
*)

chapter "Arch-specific Interrupts"

theory ArchInterrupt_A
imports Ipc_A
begin

context Arch begin global_naming X64_A

definition handle_reserved_irq :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
  where "handle_reserved_irq irq = return ()"

fun arch_invoke_irq_handler :: "irq_handler_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "arch_invoke_irq_handler (ACKIrq irq) = (do_machine_op $ maskInterrupt False irq)"
| "arch_invoke_irq_handler _ = return ()"

definition arch_mask_irq_signal :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "arch_mask_irq_signal irq \<equiv> do_machine_op $ maskInterrupt True irq"

end

context begin interpretation Arch .

(* On Arm architectures, maxIRQ is defined in Kernel_Config. On X64 it is defined manually. *)
requalify_consts
  maxIRQ

end

end
