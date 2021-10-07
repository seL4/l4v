(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Basic tests for the Insulin desugar tool. *)

theory Insulin_Test
imports
  Lib.Insulin
  Main
begin

ML \<open>
(*
 * To be considered successful, desugaring should do two things:
 *   - remove the unwanted syntax strings
 *   - return an equivalent term
 * The following code just checks those two conditions.
 *)

fun test_desugar ctxt (term, bad_strings) = let
  val text = (* function being tested *)
             Insulin.desugar_term ctxt term bad_strings
             (* strip markup from result *)
             |> YXML.parse_body
             |> XML.content_of
  val remaining_bads = filter (fn bs => String.isSubstring bs text) bad_strings
  val _ = if null remaining_bads then () else
          raise TERM ("failed to desugar these strings: [" ^ commas bad_strings ^ "]\n" ^
                      "output: " ^ text, [term])
  val term' = Syntax.read_term ctxt text
  val _ = if term = term' then () else
          raise TERM ("desugared term not equal to original",
                      [term, term'])
  in () end
\<close>

ML \<open>
(* The test cases. *)
[ (@{term "A \<and> B"}, ["\<and>"])
, (@{term "a + 0 = a * 1"}, ["+", "0", "1"])
, (@{term "(f(x := y)) z = (if z = x then y else f z)"}, [":="])
, (@{term "(f(x := y)) z = (if z = x then y else f z)"}, ["="])
] |> app (test_desugar @{context})
\<close>

end
