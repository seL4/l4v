(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory EmptyFailLib
imports
  "Monad_WP/NonDetMonad"
  HaskellLib_H
begin

(* Collect generic empty_fail lemmas here. naming convention is emtpy_fail_NAME.
   Unless there is a good reason, they should all be [intro!, simp] *)

lemma empty_fail_when [simp, intro!]:
  "(P \<Longrightarrow> empty_fail x) \<Longrightarrow> empty_fail (when P x)"
  unfolding when_def by simp

lemma empty_fail_bindD1:
  "empty_fail (a >>= b) \<Longrightarrow> empty_fail a"
  unfolding empty_fail_def bind_def
  apply (clarsimp simp: split_def image_image)
  apply (drule_tac x = s in spec)
  apply simp
  done

lemma empty_fail_liftM [simp, intro!]:
  "empty_fail (liftM f m) = empty_fail m"
  unfolding liftM_def
  apply (rule iffI)
   apply (erule empty_fail_bindD1)
  apply (erule empty_fail_bind)
  apply simp
  done

lemma empty_fail_assert [simp, intro!]:
  "empty_fail (assert P)"
  unfolding empty_fail_def assert_def
  by (simp add: return_def fail_def)

lemma empty_fail_unless [intro!, simp]:
  "empty_fail f \<Longrightarrow> empty_fail (unless P f)"
  by (simp add: unless_def)

lemma empty_fail_stateAssert [intro!, simp]:
  "empty_fail (stateAssert P l)"
  by (simp add: stateAssert_def empty_fail_def get_def assert_def
                return_def fail_def bind_def)

end
