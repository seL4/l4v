(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Arch-specific Interrupts"

theory ArchInterrupt_A
imports Ipc_A
begin

context Arch begin global_naming RISCV64_A

definition handle_reserved_irq :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "handle_reserved_irq irq = return ()"

fun arch_invoke_irq_handler :: "irq_handler_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "arch_invoke_irq_handler (ACKIrq irq) = (do_machine_op $ plic_complete_claim irq)"
| "arch_invoke_irq_handler _ = return ()"

definition arch_mask_irq_signal :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "arch_mask_irq_signal irq \<equiv> return ()"

end

context begin interpretation Arch .

(* On Arm architectures, maxIRQ is defined in Kernel_Config. On RISCV64 it is defined manually. *)
requalify_consts
  maxIRQ

end

end
