(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory dont_translate
imports "CParser.CTranslation"
begin

external_file "dont_translate.c"
install_C_file "dont_translate.c"

context dont_translate
begin

thm f_modifies
thm not_scary_modifies
thm scary_modifies
thm somewhat_scary_modifies

end

end
