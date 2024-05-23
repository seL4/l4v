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

#INCLUDE_HASKELL SEL4/Model/PSpace/AARCH64.hs decls_only ONLY pTablePartialOverlap
#INCLUDE_HASKELL SEL4/Model/PSpace/AARCH64.hs NOT pTablePartialOverlap

end (* context Arch *)

end
