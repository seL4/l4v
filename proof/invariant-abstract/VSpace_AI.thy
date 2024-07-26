(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Architecture-independent VSpace invariant proofs
*)

theory VSpace_AI
imports ArchVSpace_AI
begin

arch_requalify_facts
  do_machine_op_valid_kernel_mappings
  ackInterrupt_device_state_inv
  pspace_respects_device_region_dmo
  cap_refs_respects_device_region_dmo

lemmas device_region_dmos = pspace_respects_device_region_dmo

end
