(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Structures_D
imports
  Arch_Structs_D
begin

arch_requalify_consts (D)
  slot_bits_cdl
  endpoint_bits_cdl
  tcb_bits_cdl
  ntfn_bits_cdl
  pageBits_cdl

end