(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* License: BSD, terms see file ./LICENSE *)

theory Vanilla32_typinfo
imports "~~/src/HOL/Word/Word"
begin

type_synonym addr = "32 word"

definition addr_card :: nat where
  "addr_card \<equiv> card (UNIV::addr set)"

lemma addr_card:
  "addr_card = 2^32"
  by (simp add: addr_card_def card_word)

lemma len_of_addr_card:
  "2 ^ len_of TYPE(32) = addr_card"
  by (simp add: addr_card)

lemma of_nat_addr_card [simp]:
  "of_nat addr_card = (0::addr)"
  by (simp add: addr_card)

end
