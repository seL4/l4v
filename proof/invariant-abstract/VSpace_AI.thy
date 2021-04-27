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
context begin interpretation Arch .

requalify_facts
   pspace_respects_device_region_dmo
   cap_refs_respects_device_region_dmo
   ackInterrupt_device_state_inv

end

lemmas device_region_dmos = pspace_respects_device_region_dmo

end
