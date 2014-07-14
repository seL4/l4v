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
  "../CTranslation"
begin

install_C_file "globals_in_record.c"

context globals_in_record begin

thm globals.equality
thm adglobs_struct_idupdates adglobs_struct_tag_def

find_theorems "zuzu_'"
thm globals.zuzu_'_def

find_theorems "zozo"
thm adglobs_struct.zozo.zozo_def

find_theorems "zyzy"
thm zyzy_def

end

end
