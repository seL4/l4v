(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory jiraver808
  imports "../CTranslation"
begin

 install_C_file "jiraver808.c"

context jiraver808
begin
thm bar_body_def
end

end
