(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory inf_loop
imports "CParser.CTranslation" "AsmRefine.GlobalsSwap"
begin

declare [[populate_globals=true]]

typedecl machine_state
typedecl cghost_state

external_file "inf_loop.c"
install_C_file "inf_loop.c"
  [machinety=machine_state, ghostty=cghost_state]

setup \<open>DefineGlobalsList.define_globals_list_i
  "inf_loop.c" @{typ globals}\<close>

locale target
  = inf_loop_global_addresses
begin

abbreviation
 "globals_list \<equiv> inf_loop_global_addresses.global_data_list"
lemmas global_data_defs = inf_loop_global_addresses.global_data_defs

end

end
