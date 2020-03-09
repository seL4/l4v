(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory dc_embbug
imports "CParser.CTranslation"
begin

external_file "dc_embbug.c"
install_C_file "dc_embbug.c"

thm dc_embbug_global_addresses.f_body_def
thm dc_embbug_global_addresses.h_body_def


end
