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
theory skip_heap_abs imports "../../AutoCorres" begin

install_C_file "skip_heap_abs.c"
autocorres [skip_heap_abs] "skip_heap_abs.c"

(* There should be no heap lift theorem. *)
ML {*
assert (is_none (AutoCorresData.get_thm @{theory} "skip_heap_abs.c" "HL" "f")) "skip_heap_abs failed"
*}

end
