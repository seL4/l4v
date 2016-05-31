(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver464
  imports "../CTranslation"
begin

(* declare [[calculate_modifies_proofs=false]] *)
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
