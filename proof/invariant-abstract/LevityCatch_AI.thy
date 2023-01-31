(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory LevityCatch_AI
imports
  ArchLevityCatch_AI
begin

context begin interpretation Arch .

requalify_consts
  ptrFromPAddr addrFromPPtr
requalify_facts
  ptrFormPAddr_addFromPPtr
  aobj_ref_arch_cap

end

(*FIXME: Move or remove *)

method spec for x :: "_ :: type" = (erule allE[of _ x])
method bspec for x :: "_ :: type" = (erule ballE[of _ _ x])
method prove for x :: "prop" = (rule revcut_rl[of "PROP x"])

lemmas aobj_ref_arch_cap_simps[simp] = aobj_ref_arch_cap

lemma detype_arch_state :
  "arch_state (detype S s) = arch_state s"
  by (simp add: detype_def)

lemma obj_ref_elemD:
  "r \<in> obj_refs cap \<Longrightarrow> obj_refs cap = {r}"
  by (cases cap, simp_all)

lemma const_on_failure_wp :
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>rv. Q n\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> const_on_failure n m \<lbrace>Q\<rbrace>"
  apply (simp add: const_on_failure_def)
  apply wp
  done

lemma get_cap_id:
  "(v, s') \<in> fst (get_cap ta_f p s) \<Longrightarrow> (s' = s)"
  by (clarsimp simp: get_cap_def get_object_def in_monad
                     split_def
              split: Structures_A.kernel_object.splits)


lemmas cap_irq_opt_simps[simp] =
  cap_irq_opt_def [split_simps cap.split sum.split]

lemmas cap_irqs_simps[simp] =
    cap_irqs_def [unfolded cap_irq_opt_def, split_simps cap.split sum.split, simplified option.simps]


lemma all_eq_trans: "\<lbrakk> \<forall>x. P x = Q x; \<forall>x. Q x = R x \<rbrakk> \<Longrightarrow> \<forall>x. P x = R x"
  by simp


declare liftE_wp[wp]
declare case_sum_True[simp]
declare select_singleton[simp]

crunch_ignore (add: cap_swap_ext
              cap_move_ext cap_insert_ext empty_slot_ext create_cap_ext
              do_extended_op)

lemma select_ext_weak_wp[wp]: "\<lbrace>\<lambda>s. \<forall>x\<in>S. Q x s\<rbrace> select_ext a S \<lbrace>Q\<rbrace>"
  apply (simp add: select_ext_def)
  apply (wp select_wp)
  apply simp
  done

lemma select_ext_wp[wp]:"\<lbrace>\<lambda>s. a s \<in> S \<longrightarrow> Q (a s) s\<rbrace> select_ext a S \<lbrace>Q\<rbrace>"
  apply (simp add: select_ext_def unwrap_ext_det_ext_ext_def)
  apply (wp select_wp)
  apply (simp add: unwrap_ext_det_ext_ext_def select_switch_det_ext_ext_def)
  done

(* FIXME: move *)
lemmas mapM_UNIV_wp = mapM_wp[where S="UNIV", simplified]

lemmas word_simps =
  word_size word_ops_nth_size nth_ucast nth_shiftr nth_shiftl

lemma mask_split_aligned:
  assumes len: "m \<le> a + len_of TYPE('a)"
  assumes align: "is_aligned p a"
  shows "(p && ~~ mask m) + (ucast ((ucast (p && mask m >> a))::'a::len word) << a) = p"
  apply (insert align[simplified is_aligned_nth])
  apply (subst word_plus_and_or_coroll; rule word_eqI; clarsimp simp: word_simps)
  apply (rule iffI)
   apply (erule disjE; clarsimp)
  apply (case_tac "n < m"; case_tac "n < a")
  using len by auto

lemma mask_split_aligned_neg:
  fixes x :: "'a::len word"
  fixes p :: "'b::len word"
  assumes len: "a + len_of TYPE('a) \<le> len_of TYPE('b)"
               "m = a + len_of TYPE('a)"
  assumes x: "x \<noteq> ucast (p && mask m >> a)"
  shows "(p && ~~ mask m) + (ucast x << a) = p \<Longrightarrow> False"
  apply (subst (asm) word_plus_and_or_coroll)
   apply (clarsimp simp: word_simps bang_eq)
   apply (metis bit_imp_le_length diff_add_inverse le_add1 len(2) less_diff_iff)
  apply (insert x)
  apply (erule notE)
  apply word_eqI
  subgoal for n
    using len
    apply (clarsimp)
    apply (spec "n + a")
    by (clarsimp simp: add.commute)
  done

lemma mask_alignment_ugliness:
  "\<lbrakk> x \<noteq> x + z && ~~ mask m;
     is_aligned (x + z && ~~ mask m) m;
     is_aligned x m;
     \<forall>n \<ge> m. \<not>z !! n\<rbrakk>
  \<Longrightarrow> False"
  apply (erule notE)
  apply (subst word_plus_and_or_coroll; word_eqI)
   apply (meson linorder_not_le)
  by (auto simp: le_def)

end
