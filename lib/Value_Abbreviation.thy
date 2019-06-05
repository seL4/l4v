(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Value_Abbreviation

imports Main

keywords "value_abbreviation" :: thy_decl

begin

text \<open>Computing values and saving as abbreviations.

Useful in program verification to handle some configuration constant
(e.g. n = 4) which may change. This mechanism can be used to give
names (abbreviations) to other related constants (e.g. 2 ^ n, 2 ^ n - 1,
[1 .. n], rev [1 .. n]) which may appear repeatedly.
\<close>

ML \<open>
structure Value_Abbreviation = struct
fun value_and_abbreviation mode name expr int ctxt = let
    val decl = (name, NONE, Mixfix.NoSyn)
    val expr = Syntax.read_term ctxt expr
    val eval_expr =Value_Command.value ctxt expr
    val lhs = Free (Binding.name_of name, fastype_of expr)
    val eq = Logic.mk_equals (lhs, eval_expr)
    val ctxt = Specification.abbreviation mode (SOME decl) [] eq int ctxt
    val pretty_eq = Syntax.pretty_term ctxt eq
  in Pretty.writeln pretty_eq; ctxt end

val _ =
  Outer_Syntax.local_theory' @{command_keyword value_abbreviation}
    "setup abbreviation for evaluated value"
    (Parse.syntax_mode -- Parse.binding -- Parse.term
      >> (fn ((mode, name), expr) => value_and_abbreviation mode name expr));

end
\<close>

text \<open>Testing it out.
Unfortunately locale/experiment/notepad all won't work here because
the code equation setup is all global.
\<close>

definition
  "value_abbreviation_test_config_constant_1 = (24 :: nat)"

definition
  "value_abbreviation_test_config_constant_2 = (5 :: nat)"

value_abbreviation (input)
  value_abbreviation_test_important_magic_number
    "((2 :: int) ^ value_abbreviation_test_config_constant_1)
     - (2 ^ value_abbreviation_test_config_constant_2)"

value_abbreviation (input)
  value_abbreviation_test_range_of_options
    "rev [int value_abbreviation_test_config_constant_2
          .. int value_abbreviation_test_config_constant_1]"

end
