(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Attribute that applies a list of attributes only if an environment variable is non-empty.
   Example:

     context
       notes [[if_env SORRY_MODIFIES_PROOFS [quick_and_dirty, sorry_modifies_proofs]]]
     begin
       ...
     end

   See tests/If_Env_Test.thy for more examples. *)

theory If_Env
imports Main
begin

attribute_setup if_env = \<open>
  Scan.lift Parse.embedded -- Attrib.attribs >> (fn (var, srcs) => fn (context, th) =>
    if can getenv_strict var then
      let
        val atts = map (Attrib.attribute (Context.proof_of context)) srcs
        val (th', context') = fold (uncurry o Thm.apply_attribute) atts (th, context)
      in (SOME context', SOME th') end
    else (NONE, NONE))
\<close> "apply attributes only if environment variable is non-empty"

end
