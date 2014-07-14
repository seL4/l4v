(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory dc_embbug
imports "../CTranslation"
begin

install_C_file "dc_embbug.c"

thm dc_embbug_global_addresses.f_body_def
thm dc_embbug_global_addresses.h_body_def


end
