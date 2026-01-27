(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory no_modifies_test
imports "CParser.CTranslation"
begin

(* Test that the "no_modifies" argument does not produce modifies proofs *)

external_file "modifies_assumptions.c"
install_C_file no_modifies "modifies_assumptions.c"

context modifies_assumptions
begin

thm f_body_def

(* Would produce a name clash error if f_modifies existed: *)
lemma f_modifies: "True" by simp

end

end
