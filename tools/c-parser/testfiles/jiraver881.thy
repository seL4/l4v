(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory jiraver881

imports "../CTranslation"

begin

install_C_file "jiraver881.c"

context jiraver881 begin

(* note that x is assigned directly from f(),
   but that compound lvars and y (different notional type) are
   assigned via explicit statements. *)
thm g_body_def

end

end
