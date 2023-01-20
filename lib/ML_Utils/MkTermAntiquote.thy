(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

text \<open>
  mk_term: ML antiquotation for building and splicing terms.

  See MkTermAntiquote_Tests for examples and tests.
\<close>
theory MkTermAntiquote
imports
  Pure
begin

(* Simple wrapper theory for historical reasons. *)
ML_file "mkterm_antiquote.ML"

end