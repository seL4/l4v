(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* See comment in condition_guard.c *)
theory ConditionGuard
imports "AutoCorres.AutoCorres"
begin

external_file "condition_guard.c"
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
