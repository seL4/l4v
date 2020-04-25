(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory struct
imports "AutoCorres.AutoCorres"
begin

external_file "struct.c"
install_C_file "struct.c"

end
