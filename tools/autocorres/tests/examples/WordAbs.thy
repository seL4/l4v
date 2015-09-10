(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WordAbs
imports "../../AutoCorres"
begin

install_C_file "word_abs.c"
autocorres [unsigned_word_abs = f] "word_abs.c"

thm word_abs.f'_def

end