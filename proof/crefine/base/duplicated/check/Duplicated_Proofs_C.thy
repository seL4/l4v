(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* This theory is loaded with skip_proofs on in CBaseRefine.

   This version in check/ imports nothing outside the base image, which means all
   theories that are imported in Include_C are fully checked. *)

theory Duplicated_Proofs_C
imports
  "CSpec.KernelInc_C"
begin

end
