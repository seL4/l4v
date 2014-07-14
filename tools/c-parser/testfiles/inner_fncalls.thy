(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory inner_fncalls
imports "../CTranslation"
begin

install_C_file "inner_fncalls.c"

print_locale inner_fncalls_global_addresses

context inner_fncalls_global_addresses
begin
thm f_body_def
thm e_body_def
thm f2_body_def
thm g_body_def
thm function_body_def
thm function2_body_def
end

end
