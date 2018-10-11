(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchBCorres_AI
imports
  "../BCorres_AI"
begin

context Arch begin global_naming ARM

crunch (bcorres)bcorres[wp]: arch_finalise_cap truncate_state
  (simp: swp_def)

crunch (bcorres)bcorres[wp]: prepare_thread_delete truncate_state
  (simp: swp_def)

end

requalify_facts ARM.arch_finalise_cap_bcorres ARM.prepare_thread_delete_bcorres

declare arch_finalise_cap_bcorres[wp] prepare_thread_delete_bcorres[wp]

end
