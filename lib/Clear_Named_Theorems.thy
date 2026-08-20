(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Clearing an existing named_theorems within the current context, allowing the same named_theorems
   to be re-used multiple times as an accumulator. *)

theory Clear_Named_Theorems
imports Main
keywords "clear_named_theorems" :: thy_decl
begin

ML \<open>
local

(* We need to lift from a Context.generic transformer to a local_theory transformer.
   Context.proof_map looks like it should do this, but using it with Named_Theorems.clear does not
   have any effect. It is unclear why that's the case.
   Going via Local_Theory.declaration does work, even if we have to give it a "morphism" that
   doesn't actually contain a morphism. *)
fun local_declare f =
  Local_Theory.declaration {syntax = false, pervasive = false, pos = \<^here>} (K f);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>clear_named_theorems\<close>
    "clear named collection of theorems"
    (Parse.name_position >>
      (fn (b,pos) => fn ctxt =>
       local_declare (Named_Theorems.clear (Named_Theorems.check ctxt (b, pos))) ctxt));

in end\<close>

end
