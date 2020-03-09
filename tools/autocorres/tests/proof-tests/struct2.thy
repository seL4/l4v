(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory struct2
imports "AutoCorres.AutoCorres"
begin

external_file "struct2.c"
install_C_file "struct2.c"

autocorres [keep_going] "struct2.c"

end
