(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AInvsToplevel_AI
imports
  ArchAInvsToplevel_AI
  KernelInit_AI
begin

(* Remove this rule from [wp] here because it is not safe for proofs that involve extended state. It
   is also removed in Deterministic_AI but may have been added back in during a theory merge. *)
declare dxo_wp_weak[wp del]

end