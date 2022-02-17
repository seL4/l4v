(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory ArchTCB_H
imports TCBDecls_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL SEL4/Object/TCB/AARCH64.hs RegisterSet= CONTEXT AARCH64_H

#INCLUDE_HASKELL SEL4/Object/TCB.lhs Arch= ONLY archThreadGet archThreadSet

end
end
