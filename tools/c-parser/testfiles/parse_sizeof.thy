(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory parse_sizeof
imports "../CTranslation"
begin

install_C_file "parse_sizeof.c"

print_locale parse_sizeof_global_addresses
context parse_sizeof_global_addresses
begin
thm f_body_def
(* notice how repulsive the above is *)
thm g_body_def
end

end
