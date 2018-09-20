(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Try_Attribute
imports Main
begin

ML \<open>
local

val parse_warn = Scan.lift (Scan.optional (Args.parens (Parse.reserved "warn") >> K true) false)

val attribute_generic = Context.cases Attrib.attribute_global Attrib.attribute

fun try_attribute_cmd (warn, attr_srcs) (ctxt, thm) =
  let
    val attrs = map (attribute_generic ctxt) attr_srcs
    val (th', context') =
      fold (uncurry o Thm.apply_attribute) attrs (thm, ctxt)
      handle e =>
        (if Exn.is_interrupt e then Exn.reraise e
         else if warn then warning ("TRY: ignoring exception: " ^ (@{make_string} e))
         else ();
        (thm, ctxt))
  in (SOME context', SOME th') end

in

val _ = Theory.setup
  (Attrib.setup @{binding TRY}
    (parse_warn -- Attrib.attribs >> try_attribute_cmd)
    "higher order attribute combinator to try other attributes, ignoring failure")

end
\<close>

text \<open>
  The @{attribute TRY} attribute is an attribute combinator that applies other
  attributes, ignoring any failures by returning the original state. Note that since attributes
  are applied separately to each theorem in a theorem list, @{attribute TRY} will leave
  failing theorems unchanged while modifying the rest.

  Accepts a "warn" flag to print any errors encountered.

  Usage:
    thm foo[TRY [<attributes>]]

    thm foo[TRY (warn) [<attributes>]]
\<close>

section \<open>Examples\<close>

experiment begin
  lemma eq1: "(1 :: nat) = 1 + 0" by simp
  lemma eq2: "(2 :: nat) = 1 + 1" by simp

  lemmas eqs = eq1 TrueI eq2

  text \<open>
    `eqs[symmetric]` would fail because there are no unifiers with @{term True}, but
    @{attribute TRY} ignores that.
  \<close>
  lemma
    "1 + 0 = (1 :: nat)"
    "True"
    "1 + 1 = (2 :: nat)"
    by (rule eqs[TRY [symmetric]])+

  text \<open>
    You can chain calls to @{attribute TRY} at the top level, to apply different attributes to
    different theorems.
  \<close>
  lemma ineq: "(1 :: nat) < 2" by simp
  lemmas ineqs = eq1 ineq
  lemma
    "1 + 0 = (1 :: nat)"
    "(1 :: nat) \<le> 2"
    by (rule ineqs[TRY [symmetric], TRY [THEN order.strict_implies_order]])+

  text \<open>
    You can chain calls to @{attribute TRY} within each other, to chain more attributes onto
    particular theorems.
  \<close>
  lemmas more_eqs = eq1 eq2
  lemma
    "1 = (1 :: nat)"
    "1 + 1 = (2 :: nat)"
    by (rule more_eqs[TRY [symmetric, TRY [simplified add_0_right]]])+

  text \<open>
    The 'warn' flag will print out any exceptions encountered. Since @{attribute symmetric}
    doesn't apply to @{term True} or @{term "(1 :: nat) < 2"}, this will log two errors.
  \<close>
  lemmas yet_another_group = eq1 TrueI eq2 ineq
  thm yet_another_group[TRY (warn) [symmetric]]

  text \<open>@{attribute TRY} should handle pretty much anything it might encounter.\<close>
  thm eq1[TRY (warn) [where x=5]]
  thm eq1[TRY (warn) [OF refl]]
end

end