(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Architecture-independent VSpace invariant proofs
*)

theory VSpace_AI
imports "./$L4V_ARCH/ArchVSpace_AI"
begin
context begin interpretation Arch .

requalify_facts
   pspace_respects_device_region_dmo
   cap_refs_respects_device_region_dmo

end

lemmas device_region_dmos = pspace_respects_device_region_dmo

end
