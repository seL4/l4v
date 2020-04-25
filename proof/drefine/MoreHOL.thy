(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory MoreHOL
imports Main
begin

(*
 * Simplification of a common pattern that comes out of
 * expansions of "corres_underlying".
 *)
lemma tuple_relation_to_function [simp]: "((a, b) \<in> {(s, s'). f s' = s}) = (a = f b)"
  by auto

end
