(*
 * Copyright 2016, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory asm_stmt

imports "../../CTranslation"

begin

declare [[populate_globals=true]]

typedecl machine_state
typedecl cghost_state

install_C_file "asm_stmt.c"
  [machinety=machine_state, ghostty=cghost_state]

context asm_stmt begin

thm f_body_def
thm f_modifies
thm combine_body_def
thm combine_modifies

end

end
