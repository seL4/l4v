(*
 * Copyright 2016, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory inf_loop

imports
  "../../c-parser/CTranslation" "../GlobalsSwap"
begin

declare [[populate_globals=true]]

typedecl machine_state
typedecl cghost_state

install_C_file "inf_loop.c"
  [machinety=machine_state, ghostty=cghost_state]

setup {* DefineGlobalsList.define_globals_list_i
  "inf_loop.c" @{typ globals} *}

locale target
  = inf_loop_global_addresses
begin

abbreviation
 "globals_list \<equiv> inf_loop_global_addresses.global_data_list"
lemmas global_data_defs = inf_loop_global_addresses.global_data_defs

end

end
