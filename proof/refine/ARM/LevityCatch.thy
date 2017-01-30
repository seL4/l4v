(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory LevityCatch
imports
  Include
  "../../../lib/LemmaBucket"
begin

(* Try again, clagged from Include *)
no_notation bind_drop (infixl ">>" 60)

lemma no_fail_getCurThread:
  "no_fail \<top> getCurThread"
  by (clarsimp simp: getCurThread_def no_fail_def gets_def
                     bind_def return_def get_def)

lemma no_fail_getSchedulerAction:
  "no_fail \<top> getSchedulerAction"
  by (auto simp: getSchedulerAction_def)

lemma projectKO_def2:
  "projectKO x = assert_opt (projectKO_opt x)"
  by (simp add: assert_opt_def projectKO_def)

lemma magnitudeCheck_assert:
  "magnitudeCheck x y n = assert (case y of None \<Rightarrow> True | Some z \<Rightarrow> 1 << n \<le> z - x)"
  apply (simp add: magnitudeCheck_def assert_def when_def
            split: option.split)
  apply fastforce
  done
context begin interpretation Arch . (*FIXME: arch_split*)
lemmas makeObject_simps =
  makeObject_endpoint makeObject_notification makeObject_cte
  makeObject_tcb makeObject_user_data makeObject_pde makeObject_pte 
  makeObject_asidpool
end
definition
  "diminished' cap cap' \<equiv> \<exists>R. cap = maskCapRights R cap'"

lemma projectKO_inv : "\<lbrace>P\<rbrace> projectKO ko \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: projectKO_def fail_def valid_def return_def 
           split: option.splits)

(****** From GeneralLib *******)

lemma alignCheck_assert:
  "alignCheck ptr n = assert (is_aligned ptr n)"
  by (simp add: is_aligned_mask alignCheck_def assert_def
                alignError_def unless_def when_def)

lemma magnitudeCheck_inv:   "\<lbrace>P\<rbrace> magnitudeCheck x y n \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (clarsimp simp add: magnitudeCheck_def split: option.splits)
  apply (wp hoare_when_wp)
  apply simp
  done

lemma alignCheck_inv:
  "\<lbrace>P\<rbrace> alignCheck x n \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: alignCheck_def unless_def alignError_def)
  apply (wp hoare_when_wp)
  apply simp
  done

lemma updateObject_default_inv:
  "\<lbrace>P\<rbrace> updateObject_default obj ko x y n \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding updateObject_default_def
  by (simp, wp magnitudeCheck_inv alignCheck_inv projectKO_inv, simp)
context begin interpretation Arch . (*FIXME: arch_split*)
lemma to_from_apiType [simp]: "toAPIType (fromAPIType x) = Some x"
  by (cases x) (auto simp add: fromAPIType_def ARM_H.fromAPIType_def 
    toAPIType_def ARM_H.toAPIType_def)
end
end
