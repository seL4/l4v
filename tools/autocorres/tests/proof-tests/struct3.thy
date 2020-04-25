(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory struct3
imports "struct"
begin

(* In a separate thy file to install_C_file to catch errors in type name generation *)

autocorres "struct.c"

end
