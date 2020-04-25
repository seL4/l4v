(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Tests for handling of names and free variables.
 *)
theory dirty_frees imports "AutoCorres.AutoCorres" begin

external_file "dirty_frees.c"
install_C_file "dirty_frees.c"

autocorres [scope = f1 f2, function_name_suffix = ""] "dirty_frees.c"

autocorres [scope = symbol_table] "dirty_frees.c"

locale measure_fix = dirty_frees +
  fixes rec_measure' :: unit
autocorres [scope = foo, c_locale = measure_fix] "dirty_frees.c"

locale name_fix = dirty_frees +
  fixes locale_fixed_asdf :: nat
autocorres [scope = locale_fixed, function_name_suffix="_asdf", c_locale = name_fix] "dirty_frees.c"

(* This one is expected to fail, but it should be detected earlier and reported better *)
locale name_taken = dirty_frees begin
  definition "foo' = ()"
end
autocorres [scope = foo, c_locale = name_taken] "dirty_frees.c"

end
