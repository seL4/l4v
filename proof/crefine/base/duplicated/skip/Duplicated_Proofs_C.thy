(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* This theory is loaded with skip_proofs on in CBaseRefine.

   Everything imported in this version of the theory in skip/ is processed without
   checking proofs and will not be re-loaded in Include_C. This is safe for development,
   because all of these theories are already checked in other sessions. *)

theory Duplicated_Proofs_C
imports
  "Refine.ArchRefine"
  "AutoCorres.AutoCorres"
  "CLib.Corres_UL_C"
begin

end
