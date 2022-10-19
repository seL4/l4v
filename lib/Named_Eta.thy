(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Manipulation of eta-contractable terms taking into account their bound name. *)

theory Named_Eta
imports Main
begin

(* Eta-contraction applied only to lambda terms where the abstracted variable has a specific name.
   Primary use-case is getting rid of such terms where the name is an empty string. Such situations
   may arise during unification, especially involving schematics that depend on constants.

   Ordinarily this would not be an issue, but it inhibits preservation of bound names during further
   unification, which is especially relevant during symbolic execution.

   For example, when we have some kind of \<open>P (do my_name <- f; g my_name)\<close> and apply a rule that
   includes \<open>\<And>rv. P (g rv) \<Longrightarrow> P (g >>= (\<lambda>rv. g rv))\<close>, we want to get \<open>P (g my_name)\<close> and *not*
   \<open>P (g rv)\<close>!

   This ability of unification to preserve names will not work if the goal internally looks like:
   \<open>P (\<lambda>a. (do my_name <- (\<lambda>a. f a); (\<lambda>a. (g my_name) a) a)\<close> (where "a" is the output for "")
   because to unify with these extra bound variables, you'd first need to eta-contract, which will
   take out the my_name binding as well. *)

ML \<open>
structure Named_Eta = struct

(* copied from Pure/envir.ML *)
fun decr lev (Bound i) = if i >= lev then Bound (i - 1) else raise Same.SAME
  | decr lev (Abs (a, T, body)) = Abs (a, T, decr (lev + 1) body)
  | decr lev (t $ u) = (decr lev t $ decrh lev u handle Same.SAME => t $ decr lev u)
  | decr _ _ = raise Same.SAME
and decrh lev t = (decr lev t handle Same.SAME => t);

(* copied from Pure/envir.ML and modified to only target a specific bound variable name (i.e. "") *)
fun named_eta name (Abs (a, T, body)) =
    if a = name then
      (case named_eta name body of
          body' as (f $ Bound 0) =>
            if Term.is_dependent f then Abs (a, T, body')
            else decrh 0 f
       | body' => Abs (a, T, body')) handle Same.SAME =>
          (case body of
            f $ Bound 0 =>
              if Term.is_dependent f then raise Same.SAME
              else decrh 0 f
          | _ => raise Same.SAME)
     else Abs (a, T, named_eta name body)
  | named_eta name (t $ u) =
      (named_eta name t $ Same.commit (named_eta name) u handle Same.SAME => t $ named_eta name u)
  | named_eta _ _ = raise Same.SAME;

fun named_eta_contract name t = Same.commit (named_eta name) t

(* To make a conversion out of this partial eta contraction function, we observe that a
   partially eta-contracted term is eta-equivalent with the original term. This means: if
   we fully eta contract the partially contracted term and fully eta contract the original
   term, we must get the same normal form. That in turn means we have "partial == norm" and
   "full == norm", so with transitivity and symmetry, we get "full == partial", which is
   the theorem we want out of a conversion. *)
fun named_eta_conv name ctxt ct =
  let val eta_full_eq = Thm.eta_conversion ct
      val eta_partial_ct = Thm.cterm_of ctxt (named_eta_contract name (Thm.term_of ct))
      val eta_partial_eq = Thm.eta_conversion eta_partial_ct
  in
    Thm.transitive eta_full_eq (Thm.symmetric eta_partial_eq)
  end

end;

(* Apply as a tactic *)
fun named_eta_tac name ctxt = CONVERSION (Named_Eta.named_eta_conv name ctxt) 1
val no_name_eta_tac = named_eta_tac ""
\<close>

method_setup no_name_eta = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD (no_name_eta_tac ctxt))\<close>
  "Perform eta-contraction only on bound variables that do not have a name."

method_setup named_eta = \<open>Scan.lift Parse.name >> (fn v => fn ctxt => SIMPLE_METHOD (named_eta_tac v ctxt))\<close>
  "Perform eta-contraction only on bound variables with a specific name."

end
