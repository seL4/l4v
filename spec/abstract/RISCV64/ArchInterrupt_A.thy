(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Arch-specific Interrupts"

theory ArchInterrupt_A
imports "../Ipc_A"
begin

definition handle_reserved_irq :: "irq \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "handle_reserved_irq irq = return ()"

end