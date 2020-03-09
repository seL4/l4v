(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Simple test for skip_heap_abs.
 *)
theory skip_heap_abs imports "AutoCorres.AutoCorres" begin

external_file "skip_heap_abs.c"
install_C_file "skip_heap_abs.c"
autocorres [skip_heap_abs] "skip_heap_abs.c"

(* There should be no heap lift phase. *)
ML \<open>
val fn_infos = the (Symtab.lookup (AutoCorresFunctionInfo.get @{theory}) "skip_heap_abs.c");
assert (is_none (FunctionInfo.Phasetab.lookup fn_infos FunctionInfo.HL)) "skip_heap_abs failed";
\<close>

end
