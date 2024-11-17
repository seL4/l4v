(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Hypervisor code.
*)

theory Hypervisor_H
imports
  CNode_H
  ArchHypervisor_H
  KernelInitMonad_H
begin

arch_requalify_consts (H)
  handleHypervisorFault

end
