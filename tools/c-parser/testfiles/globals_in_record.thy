(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory globals_in_record
imports
  "CParser.CTranslation"
begin

external_file "globals_in_record.c"
install_C_file "globals_in_record.c"

context globals_in_record begin

thm globals.equality

find_theorems "zuzu_'"
thm globals.zuzu_'_def

find_theorems "zozo"

find_theorems "zyzy"
thm zyzy_def

end

end
