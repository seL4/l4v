(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory mutrec_modifies
imports "CParser.CTranslation"
begin

external_file "mutrec_modifies.c"
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
