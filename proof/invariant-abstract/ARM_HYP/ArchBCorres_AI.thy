(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBCorres_AI
imports
  BCorres_AI
begin

context Arch begin global_naming ARM_HYP

crunch arch_finalise_cap
  for (bcorres) bcorres[wp]: truncate_state
  (simp: swp_def)

crunch prepare_thread_delete
  for (bcorres) bcorres[wp]: truncate_state
  (simp: swp_def)

end

requalify_facts ARM_HYP.arch_finalise_cap_bcorres ARM_HYP.prepare_thread_delete_bcorres

declare arch_finalise_cap_bcorres[wp] prepare_thread_delete_bcorres[wp]

end
