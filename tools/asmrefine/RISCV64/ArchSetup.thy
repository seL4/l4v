(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ArchSetup
imports
  "CLib.CTranslationNICTA"
begin

abbreviation (input)
  "(arch_load_machine_word
      (load_word32 :: word32 mem_read)
      (load_word64 :: word64 mem_read)
      :: machine_word mem_read)
    \<equiv> load_word64"

abbreviation (input)
  "(arch_store_machine_word
      (store_word32 :: word32 mem_upd)
      (store_word64 :: word64 mem_upd)
      :: machine_word mem_upd)
    \<equiv> store_word64"

abbreviation (input)
  "(arch_machine_word_constructor
      (from_word32 :: word32 \<Rightarrow> 'a)
      (from_word64 :: word64 \<Rightarrow> 'a)
      :: machine_word \<Rightarrow> 'a)
    \<equiv> from_word64"

end
