(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory populate_globals
imports "CParser.CTranslation"
begin

external_file "globsall_addressed.c"

declare [[globals_all_addressed=true,populate_globals=true]]
install_C_file "globsall_addressed.c"

context globsall_addressed
begin
  thm f_body_def

  term wannabe_constant
  thm wannabe_constant_def

  term glob1_'
end

end
