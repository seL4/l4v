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
 * AutoCorres has experimental support for incremental translation.
 * To use it, simply run the autocorres command with the "scope" option
 * to select different functions for each run.
 *)
theory Incremental imports
  "../../AutoCorres"
begin

install_C_file "type_strengthen.c"

(* Translate only opt_j *)
autocorres [
  scope_depth = 0,
  scope = opt_j
  ] "type_strengthen.c"

thm type_strengthen.opt_j'_def

(* Translate st_i, which calls opt_j. Calls to opt_j are translated correctly. *)
autocorres [
  ts_rules = nondet,
  no_heap_abs = st_i,
  scope_depth = 0,
  scope = st_i
  ] "type_strengthen.c"

thm type_strengthen.st_i'.simps

(* st_h calls st_g, which we did not select.
 * So this translates st_g by generating a wrapper for its SIMPL code. *)
autocorres [
  ts_rules = nondet,
  no_signed_word_abs = st_h,
  scope_depth = 0,
  scope = st_h
  ] "type_strengthen.c"

thm type_strengthen.st_h'_def
    type_strengthen.st_g'_def

(* Translate the remaining functions. *)
autocorres [
  ts_rules = pure option nondet,
  ts_force option = pure_f,
  scope_depth = 0,
  scope = pure_f pure_f2 pure_g pure_h pure_i pure_j pure_k pure_div_roundup
          gets_f gets_g opt_f opt_g opt_h (* opt_j *) opt_i opt_none opt_l opt_a opt_a2 hax
          st_f (* st_g st_h st_i *) exc_f
  ] "type_strengthen.c"

context type_strengthen begin
(* All function defs. *)
thm pure_f'_def pure_f2'_def
thm pure_g'_def pure_h'_def
    pure_i'_def pure_j'_def pure_k'_def pure_div_roundup'_def
thm gets_f'_def gets_g'_def
thm opt_f'_def opt_g'_def opt_h'.simps opt_i'_def
    opt_j'_def opt_a'.simps opt_a2'_def
thm opt_l'_def
thm st_f'_def st_g'_def st_h'_def st_i'.simps hax'_def
thm exc_f'_def
end

end