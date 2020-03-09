(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Test handling of C idents that are unusual or at risk of conflicting with other names.
 *)
theory badnames imports "AutoCorres.AutoCorres" begin

external_file "badnames.c"

declare [[allow_underscore_idents]]
install_C_file "badnames.c"
autocorres "badnames.c"

end
