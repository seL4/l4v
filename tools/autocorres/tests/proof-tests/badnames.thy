(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
