(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Corres
imports StateRelation "CorresK.CorresK_Lemmas"
begin

text \<open>Instantiating the corres framework to this particular state relation.\<close>
abbreviation
 "corres \<equiv> corres_underlying state_relation False True"

abbreviation
 "cross_rel \<equiv> cross_rel_ul state_relation"

lemmas cross_rel_def = cross_rel_ul_def

abbreviation
 "corresK \<equiv> corres_underlyingK state_relation False True"

abbreviation
  "ex_abs \<equiv> ex_abs_underlying state_relation"

lemmas ex_abs_def = ex_abs_underlying_def

abbreviation "sr_inv P P' f \<equiv> sr_inv_ul state_relation P P' f"

lemmas sr_inv_def = sr_inv_ul_def

lemmas sr_inv_imp = sr_inv_ul_imp[of state_relation]

lemmas sr_inv_bind = sr_inv_ul_bind[where sr=state_relation]

end
