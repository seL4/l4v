(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature TERM_EXTRAS =
sig
  val abs_all : int -> term -> term
  val dest_arg : term -> term
  val strip_all : term -> (string * typ) list * term
  val drop_binders: int -> typ -> typ
end

structure TermExtras: TERM_EXTRAS =
struct

\<comment>\<open>
  `abs_all n t` wraps the first `n` lambda abstractions in `t` with interleaved
  @{term Pure.all} constructors. For example, `abs_all 2 @{term "\<lambda>a b c. P"}` becomes
  "\<And>a b. \<lambda>c. P". The resulting term is usually not well-typed.
\<close>
fun abs_all 0 t = t
  | abs_all n (Abs (v, typ, body)) =
      if n < 0 then error "Number of lambdas to wrap should be positive." else
      Const (@{const_name Pure.all}, dummyT)
        $ Abs (v, typ, abs_all (n - 1) body)
  | abs_all n _ = error ("Expected at least " ^ Int.toString n ^ " more lambdas.")

\<comment> \<open>
  Term version of @{ML "Thm.dest_arg"}.
\<close>
val dest_arg = Term.dest_comb #> snd

\<comment> \<open>
  Cousin of @{ML "Term.strip_abs"}.
\<close>
fun strip_all t = (Term.strip_all_vars t, Term.strip_all_body t)

\<comment> \<open>
  Drops the first n binders of a type.
\<close>
fun drop_binders 0 T = T
| drop_binders n (Type ("fun", [_, T])) = drop_binders (n-1) T
| drop_binders _ T = T;

end