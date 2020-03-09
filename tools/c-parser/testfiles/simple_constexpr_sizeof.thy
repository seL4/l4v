(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory simple_constexpr_sizeof
imports "CParser.CTranslation"
begin

external_file "simple_constexpr_sizeof.c"
install_C_file "simple_constexpr_sizeof.c"

thm simple_constexpr_sizeof_global_addresses.f_body_def


end
