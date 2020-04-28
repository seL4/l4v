(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Arch-specific Interrupts"

theory ArchInterrupt_A
imports "../Ipc_A"
begin

context begin interpretation Arch .

definition handle_reserved_irq :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "handle_reserved_irq irq = return ()"

fun arch_invoke_irq_handler :: "irq_handler_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "arch_invoke_irq_handler (ACKIrq irq) = (do_machine_op $ plic_complete_claim irq)"
| "arch_invoke_irq_handler _ = return ()"

end

end
