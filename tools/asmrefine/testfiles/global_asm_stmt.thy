(*
 * Copyright 2016, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory global_asm_stmt

imports
  "../../c-parser/CTranslation" "../GlobalsSwap"
begin

declare [[populate_globals=true]]

typedecl machine_state
typedecl cghost_state

install_C_file "global_asm_stmt.c"
  [machinety=machine_state, ghostty=cghost_state]

setup {* DefineGlobalsList.define_globals_list_i
  "global_asm_stmt.c" @{typ globals} *}

locale g_asm_target
  = global_asm_stmt_global_addresses
begin

abbreviation
 "globals_list \<equiv> global_asm_stmt_global_addresses.global_data_list"
lemmas global_data_defs = global_asm_stmt_global_addresses.global_data_defs

end

end
