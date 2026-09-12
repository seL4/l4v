(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory array_size_errors
imports "CParser.CTranslation"
begin

text \<open>Negative tests for array size errors.\<close>

external_file "errors/zero_length_array.c"
external_file "errors/empty_initializer.c"
external_file "errors/unsized_local_array.c"
external_file "errors/nonconst_array_init.c"

ML \<open>
fun expect_error file expected thy =
  case Exn.capture (IsarInstall.interactive_install file) thy of
    Exn.Res _ => error ("expected " ^ file ^ " to be rejected")
  | Exn.Exn (ERROR msg) =>
      if String.isSubstring expected msg
      then (writeln (file ^ " Ok"); thy)
      else error ("Unexpected error message for " ^ file ^ ":\n" ^ msg)
  | Exn.Exn exn => Exn.reraise exn
\<close>

ML \<open>
  val _ =
    @{theory}
    |> expect_error "errors/zero_length_array.c"
                    "Array has non-positive size 0; zero-length arrays are not supported"
    |> expect_error "errors/empty_initializer.c"
                    "Empty initializer lists are not supported"
    |> expect_error "errors/unsized_local_array.c"
                    "Array a in function f must have a size or an initializer"
    |> expect_error "errors/nonconst_array_init.c"
                    "Array a initialized with non-constant expression"
\<close>

end
