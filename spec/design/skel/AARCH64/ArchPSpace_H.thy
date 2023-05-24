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

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL SEL4/Model/PSpace/AARCH64.hs

end (* context Arch *)

end
