(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Toplevel Refinement Statement"

theory Init_C
imports ADT_C
begin

text \<open>Currently, we assume correctness of the init code.\<close>

context kernel_m begin

lemma init_refinement_C:
  "Init_C s \<subseteq> lift_state_relation rf_sr `` Init_H"
  by (fact init_refinement_C_axiom)

end

end
