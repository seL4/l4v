(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory multidim_arrays
imports "CParser.CTranslation"
begin

external_file "multidim_arrays.c"
install_C_file "multidim_arrays.c"

context multidim_arrays
begin

thm h1_body_def
thm h2_body_def


end

end
