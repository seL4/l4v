(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory parse_addr
imports "../CTranslation"
begin

install_C_file "parse_addr.c"

context parse_addr_global_addresses
begin
thm f_body_def
thm f2_body_def
thm g_body_def
thm h_body_def
term c_'
end

end
