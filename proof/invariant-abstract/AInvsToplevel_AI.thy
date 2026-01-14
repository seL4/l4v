(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* This theory serves as a top-level theory for testing AInvs and as a
   convenient file to import when we want to include all of AInvs.
   It should import everything that we want tested as part of building the
   AInvs image. *)

theory AInvsToplevel_AI
imports
  AInvs
  ArchAInvsToplevel_AI
  KernelInit_AI
begin

(* Remove this rule from [wp] here because it is not safe for proofs that
   involve extended state. It is also removed in Deterministic_AI but may have
   been added back in during the theory merge with KernelInit_AI. *)
declare dxo_wp_weak[wp del]

end