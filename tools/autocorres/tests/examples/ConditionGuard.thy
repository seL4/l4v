(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* See comment in condition_guard.c *)
theory ConditionGuard imports "../../AutoCorres" begin

install_C_file "condition_guard.c"
autocorres "condition_guard.c"

context condition_guard begin

thm f1_body_def f1'_def
thm f2_body_def f2'_def
thm fancy_body_def fancy'_def
thm loop_body_def loop'_def
thm arith_body_def arith'_def

end

end