(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory struct3
imports "struct"
begin

(* In a separate thy file to install_C_file to catch errors in type name generation *)

autocorres "struct.c"

end
