(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory TestSEL4
imports
  AutoCorres
  "../../spec/cspec/KernelInc_C"
begin

(*
 * Test to see if we can parse all of seL4.
 *)
autocorres [skip_heap_abs, ts_rules = nondet] "c/kernel_all.c_pp"

end
