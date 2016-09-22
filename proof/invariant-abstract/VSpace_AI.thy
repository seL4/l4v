(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
(* Nothing to see here. *)
end

lemmas device_region_dmos = pspace_respects_device_region_dmo

end
