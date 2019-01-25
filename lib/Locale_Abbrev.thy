(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Locale_Abbrev
  imports Main
  keywords "revert_abbrev" :: thy_decl and "locale_abbrev" :: thy_decl
begin

(*
  "Normal" abbreviations in locales provide input syntax only, i.e. they are not contracted on
  pretty printing. Presumably this is because a) this would not work with fixed variables on locale
  export and b) one cannot make a global decision whether everything is to be abbreviated only
  inside the locale or inside and outside, and so the safe option is to provide input only.

  This theory provides two commands:
    - revert_abbrev (print-mode) name (:: lthy \<Rightarrow> lthy)
        causes an already defined abbreviation \<open>name\<close> to always be contracted on pretty printing
        for the specified optional print mode. This only works when the abbreviation does not
        mention any fixed variables of the locale.

    - locale_abbrev spec (:: lthy \<Rightarrow> lthy)
        is an alias for the standard abbreviation command, followed by revert_abbrev.
        This is the command to use for abbreviations that should be contracted inside locales.
        Contrary to standard abbreviations, this command cannot mention fixed variables of the
        locale.
*)

ML \<open>
local

fun revert_abbrev (mode,name) lthy =
  let
    val the_const = (fst o dest_Const) oo Proof_Context.read_const {proper = true, strict = false};
  in
    Local_Theory.raw_theory (Sign.revert_abbrev (fst mode) (the_const lthy name)) lthy
  end

fun name_of spec lthy = Local_Defs.abs_def (Syntax.read_term lthy spec) |> #1 |> #1

in

val _ =
  Outer_Syntax.local_theory @{command_keyword revert_abbrev}
    "make an abbreviation available for output"
    (Parse.syntax_mode -- Parse.const >> revert_abbrev)

val _ =
  Outer_Syntax.local_theory' @{command_keyword locale_abbrev}
    "constant abbreviation that provides also provides printing in locales"
    (Parse.syntax_mode -- Scan.option Parse_Spec.constdecl -- Parse.prop -- Parse.for_fixes
      >> (fn (((mode, decl), spec), params) => fn restricted => fn lthy =>
           lthy
           |> Local_Theory.open_target |> snd
           |> Specification.abbreviation_cmd mode decl params spec restricted
           |> Local_Theory.close_target (* commit new abbrev. name *)
           |> revert_abbrev (mode, name_of spec lthy)));

end
\<close>

end