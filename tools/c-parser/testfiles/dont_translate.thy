(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory dont_translate
imports "../CTranslation"
begin

install_C_file "dont_translate.c"

context dont_translate
begin

thm f_modifies
thm not_scary_modifies
thm scary_modifies
thm somewhat_scary_modifies

end

end
