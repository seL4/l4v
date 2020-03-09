(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Word_Lemmas_64_Internal
imports Word_Lemmas_64
begin

lemmas unat_add_simple = iffD1[OF unat_add_lem[where 'a = 64, folded word_bits_def]]

end