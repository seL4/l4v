(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory struct2
imports "../../AutoCorres"
begin

install_C_file "struct2.c"

autocorres [keep_going] "struct2.c"

end
