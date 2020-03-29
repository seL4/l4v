(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Locale_Abbrev_Test
 imports Lib.Locale_Abbrev
begin

section \<open>Examples for @{command locale_abbrev}/@{command revert_abbrev}\<close>

locale blah =
  assumes X
  fixes y
begin

definition "foo \<equiv> True"

locale_abbrev "test \<equiv> foo"
abbreviation "test2 \<equiv> y"
abbreviation "test3 \<equiv> False"
revert_abbrev test3
abbreviation "test4 \<equiv> True"

term test   (* shows test, contracted, no fixed variable *)
term test2  (* shows test2, contracted, fixed variable, not exportable *)
term test3  (* shows test3, contracted, no fixed variable *)
term test4  (* shows True, not contracted, no fixed variable *)

end

term test           (* free variable, proper name is qualified *)
term blah.test      (* shows "blah.test", contracted *)
term "blah.test2 y" (* shows "y", not contracted, needs fixed variable as parameter *)
term blah.test3     (* shows "blah.test3", contracted *)
term blah.test4     (* shows "True", not contracted *)


locale blah2 = blah +
  assumes Z
begin

(* unchanged from above on re-entering the context *)

term test   (* shows test, contracted, no fixed variable *)
term test2  (* shows test2, contracted, fixed variable, not exportable *)
term test3  (* shows test3, contracted, no fixed variable *)
term test4  (* shows True, not contracted, no fixed variable *)

end

(* Can be used outside locales, but there is not really any point, because the
   abbreviation command already provides everything *)
locale_abbrev "test6 \<equiv> False"
abbreviation "test5 \<equiv> False"

(* revert_abbrev does not change anything outside locales, since the reverse abbreviation
   is already present *)
revert_abbrev test5
revert_abbrev test6

end