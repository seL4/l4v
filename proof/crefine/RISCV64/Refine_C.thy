(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
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
