(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory global_array_swap
imports "CParser.CTranslation" "AsmRefine.GlobalsSwap"
begin

declare [[populate_globals=true]]

typedecl machine_state
typedecl cghost_state

external_file "global_array_swap.c"
install_C_file "global_array_swap.c"
  [machinety=machine_state, ghostty=cghost_state]

setup \<open>DefineGlobalsList.define_globals_list_i
  "global_array_swap.c" @{typ globals}\<close>

locale target
  = global_array_swap_global_addresses
begin

abbreviation
 "globals_list \<equiv> global_array_swap_global_addresses.global_data_list"
lemmas global_data_defs = global_array_swap_global_addresses.global_data_defs

end

end
