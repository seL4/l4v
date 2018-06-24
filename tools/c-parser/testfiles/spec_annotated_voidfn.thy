(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory spec_annotated_voidfn
imports "CParser.CTranslation"
begin

external_file "spec_annotated_voidfn.c"
install_C_file "spec_annotated_voidfn.c"

thm spec_annotated_voidfn_global_addresses.f_impl
print_locale f_spec
thm f_spec_def

end
