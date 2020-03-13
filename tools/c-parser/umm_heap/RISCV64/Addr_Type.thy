(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* License: BSD, terms see file ./LICENSE *)

theory Addr_Type
imports "HOL-Word.Word"
begin

type_synonym addr_bitsize = "64"
type_synonym addr = "addr_bitsize word"
definition addr_bitsize :: nat where "addr_bitsize \<equiv> 64"
definition addr_align :: nat where "addr_align \<equiv> 3"
declare addr_align_def[simp]

definition addr_card :: nat where
  "addr_card \<equiv> card (UNIV::addr set)"



declare addr_bitsize_def[simp]

lemma addr_card:
  "addr_card = 2^addr_bitsize"
  by (simp add: addr_card_def card_word)

lemma len_of_addr_card:
  "2 ^ len_of TYPE(addr_bitsize) = addr_card"
  by (simp add: addr_card)

lemma of_nat_addr_card [simp]:
  "of_nat addr_card = (0::addr)"
  by (simp add: addr_card)

end
