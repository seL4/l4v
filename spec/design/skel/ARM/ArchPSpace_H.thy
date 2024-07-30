(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch-specific ghost update functions for physical memory *)

theory ArchPSpace_H
imports
  ObjectInstances_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Model/PSpace/ARM.hs

end (* context Arch *)

end
