(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver1241
imports "CParser.CTranslation"
begin

external_file "jiraver1241.c"
install_C_file "jiraver1241.c"

ML \<open>
val mungedb =
    CalculateState.get_csenv @{theory} "jiraver1241.c"
    |> the
    |> ProgramAnalysis.get_mungedb
    |> ProgramAnalysis.render_mungedb;

assert
  (mungedb = [
    (* Functions are global variables with guaranteed-unique names,
       so no aliasing is required. *)
    "C variable 'a' declared globally -> Isabelle state field 'a' with no abbreviation",
    "C variable 'b' declared globally -> Isabelle state field 'b' with no abbreviation",
    "C variable 'c' declared globally -> Isabelle state field 'c' with no abbreviation",

    (* `a` comes before `b` in the source file, so the overloaded
       declaration `local` gets both a short name and a long name:
       Isabelle sees `local___int` as well as an abbreviation `local`
       which abbreviates `local__int`. *)
    "C variable 'local' declared in function 'a' -> Isabelle state field 'local___int' with abbreviation 'local'",

    (* `b` comes after `a` in the source file, so the overloaded
       declaration `local` doesn't get a short name in Isabelle:
       Isabelle only sees `local__long`. *)
    "C variable 'local' declared in function 'b' -> Isabelle state field 'local___long' with no abbreviation",

    (* `c` comes after `a`, but the overloaded declaration `local`
       is compatible with the declaration for `a::local` because of
       the shared type, so again Isabelle sees the short and long name. *)
    "C variable 'local' declared in function 'c' -> Isabelle state field 'local___int' with abbreviation 'local'"
  ])

  "Incorrect mungeDB output";
\<close>

end