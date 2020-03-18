(*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Toplevel Refinement Statement"

theory Refine_C
imports
  Include_C (* FIXME RISCV: replace with below *)

  (* FIXME RISCV:
  Init_C

  (* FIXME: Fastpath_C left out, imports lifted here: *)
  SyscallArgs_C
  Delete_C
  Syscall_C
  *)

  "Refine.RAB_FN"
  "CLib.MonadicRewrite_C"

  "../lib/CToCRefine"
begin

(* FIXME RISCV: fill in *)

end
