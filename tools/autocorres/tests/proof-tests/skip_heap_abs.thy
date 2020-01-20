(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
