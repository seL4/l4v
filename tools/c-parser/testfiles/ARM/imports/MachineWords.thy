(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory MachineWords
imports "CParser.CTranslation"
begin

type_synonym machine_word_len = "32"

type_synonym machine_word = "machine_word_len word"

abbreviation "machine_word_bytes \<equiv> 4 :: nat"

lemma of_nat_machine_word_bytes[simp]: "of_nat machine_word_bytes = 4"
  by simp

end
