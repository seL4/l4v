(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(* Collects general lemmas in the capDL refinement proof. 
   Those should eventually be moved to Lib.

   Also defines a single entry point for all drefine theories 
   in which global simpset and notation changes can be made.
*)

theory Lemmas_D
imports
  Include_D
  MoreHOL
  MoreCorres
  "../../spec/design/InvocationLabels_H"
  "../../lib/MonadicRewrite"
  "../refine/EmptyFail"
begin

no_notation bind_drop (infixl ">>" 60)

(* FIXME: move *)
lemma alternative_com:
  "(f \<sqinter> g) = (g \<sqinter> f)"
  apply (rule ext)
  apply (auto simp: alternative_def)
  done

end
