(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory TestSEL4
imports
  "AutoCorres.AutoCorres"
  "CSpec.KernelInc_C"
begin

(*
 * Test to see if we can parse all of seL4.
 *)
autocorres [skip_heap_abs, ts_rules = nondet] "../c/build/$L4V_ARCH/kernel_all.c_pp"

end
