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

context Arch begin arch_global_naming (A)

definition handle_reserved_irq :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
  where "handle_reserved_irq irq = return ()"

fun arch_invoke_irq_handler :: "irq_handler_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "arch_invoke_irq_handler (ACKIrq irq) = (do_machine_op $ maskInterrupt False irq)"
| "arch_invoke_irq_handler _ = return ()"

definition arch_mask_irq_signal :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "arch_mask_irq_signal irq \<equiv> do_machine_op $ maskInterrupt True irq"

definition handle_spurious_irq :: "(unit,'z::state_ext) s_monad"
  where
  "handle_spurious_irq \<equiv> return ()"

end

(* On Arm architectures, maxIRQ is defined in Kernel_Config. On X64 it is defined manually. *)
arch_requalify_consts
  maxIRQ

end
