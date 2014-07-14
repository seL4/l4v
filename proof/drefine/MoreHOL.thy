(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory MoreHOL
imports "~~/src/HOL/Main"
begin

(*
 * Simplification of a common pattern that comes out of
 * expansions of "corres_underlying".
 *)
lemma tuple_relation_to_function [simp]: "((a, b) \<in> {(s, s'). f s' = s}) = (a = f b)"
  by auto

end
