(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Toplevel Refinement Statement"

theory Init_C
imports ADT_C
begin

text {*
  Currently, we assume correctness of the init code.
*}

axiomatization where init_refinement_C:
  "Init_C s \<subseteq> lift_state_relation rf_sr `` Init_H"

end
