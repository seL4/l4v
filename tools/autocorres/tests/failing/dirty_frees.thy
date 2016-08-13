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
 * Tests for handling of names and free variables.
 *)
theory dirty_frees imports "../../AutoCorres" begin

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
