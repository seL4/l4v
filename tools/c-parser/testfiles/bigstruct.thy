(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory bigstruct
imports "../CTranslation"
begin

(* to prove a case rule with up to 25 fields *)
declare [[blast_depth_limit = 25]]

install_C_file "bigstruct.c"

end
