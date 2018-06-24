(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
