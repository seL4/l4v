(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Repeat_Attribute
imports Main
begin

ML \<open>
local

val attribute_generic = Context.cases Attrib.attribute_global Attrib.attribute

fun apply_attributes attrs thm ctxt =
  let
    val (thm', ctxt') = fold (uncurry o Thm.apply_attribute) attrs (thm, ctxt)
  in if Thm.eq_thm (thm, thm')
     then (SOME ctxt', SOME thm)
     else
       \<^try>\<open>apply_attributes attrs thm' ctxt' catch _ => (SOME ctxt', SOME thm')\<close>
  end

fun repeat_attribute_cmd attr_srcs (ctxt, thm) =
  let val attrs = map (attribute_generic ctxt) attr_srcs
  in apply_attributes attrs thm ctxt end

in

val _ = Theory.setup
  (Attrib.setup @{binding REPEAT}
    (Attrib.attribs >> repeat_attribute_cmd)
    "higher order attribute combinator to repeatedly apply other attributes one or more times")

end
\<close>

text \<open>

  The @{attribute REPEAT} attribute is an attribute combinator that repeatedly applies
  other attributes one or more times. It will stop applying the attributes once they can
  either no longer be applied, or if applying them would not change the theorem being
  modified.

  Usage:
    thm foo[REPEAT [<attributes>]]

\<close>

section \<open>Examples\<close>

experiment begin
  lemma test1: "True \<Longrightarrow> True" .
  lemma test2: "True \<Longrightarrow> True \<Longrightarrow> True" .
  lemmas tests = test1 test2
  text \<open>
    `tests[OF TrueI]` would only discharge one of the assumptions of @{thm test2}, but
    @{attribute REPEAT} handles both cases.
  \<close>
  thm tests[REPEAT [OF TrueI]]

  text \<open>
    @{attribute REPEAT} succesfully terminates when applying an attribute that could loop,
    such as @{attribute simplified} and @{attribute simp}. Importantly, it still updates
    the context if necessary, in this case by adding P to the simp set.
  \<close>
  lemma
    assumes P[REPEAT [simplified], REPEAT [simp]]: "P \<or> False"
    shows P
    by simp

end

end
