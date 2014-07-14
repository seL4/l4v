(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory mutrec_modifies
imports "../CTranslation"
begin

install_C_file "mutrec_modifies.c"

context mutrec_modifies
begin

thm f_modifies
thm g_modifies
thm atop_modifies
thm h_modifies
thm fact_modifies

thm rec1_modifies
thm rec2_modifies
thm rec3_modifies
thm rec4_modifies

end

end
