(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Lemmas about the no_fail predicate. *)

theory No_Fail
  imports NonDetMonadVCG
begin

lemma no_fail_assume_pre:
  "(\<And>s. P s \<Longrightarrow> no_fail P f) \<Longrightarrow> no_fail P f"
  by (simp add: no_fail_def)

lemma no_fail_liftM_eq [simp]:
  "no_fail P (liftM f m) = no_fail P m"
  by (auto simp: liftM_def no_fail_def bind_def return_def)

lemma no_fail_select_f [wp]:
  "no_fail (\<lambda>s. \<not>snd S) (select_f S)"
  by (simp add: select_f_def no_fail_def)

lemma no_fail_liftM [wp]:
  "no_fail P m \<Longrightarrow> no_fail P (liftM f m)"
  by (simp)

lemma no_fail_pre_and:
  "no_fail P f \<Longrightarrow> no_fail (P and Q) f"
  by (erule no_fail_pre) simp

lemma no_fail_spec:
  "\<lbrakk> \<And>s. no_fail (((=) s) and P) f \<rbrakk> \<Longrightarrow> no_fail P f"
  by (simp add: no_fail_def)

lemma no_fail_assertE [wp]:
  "no_fail (\<lambda>_. P) (assertE P)"
  by (simp add: assertE_def split: if_split)

lemma no_fail_spec_pre:
  "\<lbrakk> no_fail (((=) s) and P') f; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> no_fail (((=) s) and P) f"
  by (erule no_fail_pre, simp)

lemma no_fail_whenE [wp]:
  "\<lbrakk> G \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s. G \<longrightarrow> P s) (whenE G f)"
  by (simp add: whenE_def split: if_split)

lemma no_fail_unlessE [wp]:
  "\<lbrakk> \<not> G \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s. \<not> G \<longrightarrow> P s) (unlessE G f)"
  by (simp add: unlessE_def split: if_split)

lemma no_fail_throwError [wp]:
  "no_fail \<top> (throwError e)"
  by (simp add: throwError_def)

lemma no_fail_liftE [wp]:
  "no_fail P f \<Longrightarrow> no_fail P (liftE f)"
  unfolding liftE_def by wpsimp

lemma no_fail_gets_the [wp]:
  "no_fail (\<lambda>s. f s \<noteq> None) (gets_the f)"
  apply (simp add: gets_the_def)
  apply (rule no_fail_pre, wp)
  apply simp
  done

lemma assert_opt_If:
  "assert_opt v = If (v = None) fail (return (the v))"
  by (simp_all add: assert_opt_def split: option.split)

lemma if_to_top_of_bind:
  "(bind (If P x y) z) = If P (bind x z) (bind y z)"
  by (simp split: if_split)

lemma if_to_top_of_bindE:
  "(bindE (If P x y) z) = If P (bindE x z) (bindE y z)"
  by (simp split: if_split)

lemma alternative_bind:
  "((a \<sqinter> b) >>= c) = ((a >>= c) \<sqinter> (b >>= c))"
  apply (rule ext, simp add: alternative_def bind_def split_def)
  apply blast
  done

lemma alternative_refl:
  "(a \<sqinter> a) = a"
  by (rule ext, simp add: alternative_def)

lemma alternative_com:
  "(f \<sqinter> g) = (g \<sqinter> f)"
  apply (rule ext)
  apply (auto simp: alternative_def)
  done

lemma liftE_alternative:
  "liftE (a \<sqinter> b) = (liftE a \<sqinter> liftE b)"
  by (simp add: liftE_def alternative_bind)

lemma no_fail_bindE [wp]:
  "\<lbrakk> no_fail P f; \<And>rv. no_fail (R rv) (g rv); \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,- \<rbrakk>
     \<Longrightarrow> no_fail (P and Q) (f >>=E g)"
  apply (simp add: bindE_def)
  apply (erule no_fail_bind)
   apply (simp add: lift_def)
   apply wpc
    apply (simp add: throwError_def)
    apply wp
   apply assumption
  apply (simp add: validE_R_def validE_def)
  apply (erule hoare_strengthen_post)
  apply clarsimp
  done

lemma no_fail_False [simp]:
  "no_fail (\<lambda>_. False) X"
  by (clarsimp simp: no_fail_def)

end
