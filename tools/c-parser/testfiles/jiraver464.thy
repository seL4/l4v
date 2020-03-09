(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver464
  imports "CParser.CTranslation"
begin

(* declare [[calculate_modifies_proofs=false]] *)

external_file "jiraver464.c"
install_C_file "jiraver464.c"

print_locale f_spec
context f_spec
begin
  thm f_spec_def
end

context jiraver464
begin
  thm f_body_def
  thm f_modifies

thm clz_body_def
thm clz_modifies

thm clz_body_def
thm halt_body_def

end

end
