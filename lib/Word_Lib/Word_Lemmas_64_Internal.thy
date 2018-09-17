(*
 * Copyright 2018, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Word_Lemmas_64_Internal
imports Word_Lemmas_64
begin

lemmas unat_add_simple = iffD1[OF unat_add_lem[where 'a = 64, folded word_bits_def]]

end