(*
 * Copyright 2014, General Dynamics C4 Systems
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
 "corresK \<equiv> corres_underlyingK state_relation False True"

abbreviation
  "ex_abs \<equiv> ex_abs_underlying state_relation"

lemmas ex_abs_def = ex_abs_underlying_def[where sr=state_relation and P=G,abs_def] for G

end
