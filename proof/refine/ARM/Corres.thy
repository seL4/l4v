(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Corres
imports StateRelation "CorresK.CorresK_Lemmas"
begin

text {* Instantiating the corres framework to this particular state relation. *}
abbreviation
 "corres \<equiv> corres_underlying state_relation False True"

abbreviation
 "corresK \<equiv> corres_underlyingK state_relation False True"

abbreviation
  "ex_abs \<equiv> ex_abs_underlying state_relation"

end
