(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.

 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.

 * @TAG(DATA61_BSD)
 *)

theory GenericTag
imports
  HOL.HOL
begin

text \<open>
  Generic annotation constant.

  @{typ 'ns} is a namespace parameter and should be a different
  type or constant for each distinct use of this constant.

  @{typ 'tag} is an arbitrary annotation associated with the actual
  value @{term x}.
\<close>
definition generic_tag :: "'ns \<Rightarrow> 'tag \<Rightarrow> 'a \<Rightarrow> 'a"
  where remove_generic_tag[code del]: "generic_tag _ _ x \<equiv> x"

text \<open>Often the tagged value is a proposition to be proved.\<close>
lemma generic_tagP_I:
  "P \<Longrightarrow> generic_tag ns tag P"
  by (simp add: remove_generic_tag)

lemma generic_tag_True:
  "generic_tag ns tag True"
  by (simp add: remove_generic_tag)

text \<open>We often want to avoid rewriting under annotations.\<close>
lemma generic_tag_cong:
  "x = x' \<Longrightarrow> generic_tag ns tag x = generic_tag ns tag x'"
  by simp

end