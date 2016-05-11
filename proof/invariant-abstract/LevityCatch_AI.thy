(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory LevityCatch_AI
imports
  "./$L4V_ARCH/ArchLevityCatch_AI"
begin

lemma detype_arch_state :
  "arch_state (detype S s) = arch_state s"
  by (simp add: detype_def)

lemma obj_ref_elemD:
  "r \<in> obj_refs cap \<Longrightarrow> obj_refs cap = {r}"
  by (cases cap, simp_all)


definition
  "diminished cap cap' \<equiv> \<exists>R. cap = mask_cap R cap'"



lemma const_on_failure_wp : 
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>rv. Q n\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> const_on_failure n m \<lbrace>Q\<rbrace>"
  apply (simp add: const_on_failure_def)
  apply wp
  apply simp
  done

lemma get_cap_id:
  "(v, s') \<in> fst (get_cap p s) \<Longrightarrow> (s' = s)"
  by (clarsimp simp: get_cap_def get_object_def in_monad 
                     split_def
              split: Structures_A.kernel_object.splits)


lemmas cap_irq_opt_simps[simp] = 
  cap_irq_opt_def [split_simps cap.split sum.split]

lemmas cap_irqs_simps[simp] =
    cap_irqs_def [unfolded cap_irq_opt_def, split_simps cap.split sum.split, simplified option.simps]

(* FIXME: move *)
lemma mask_lower_twice:
  "n \<le> m \<Longrightarrow> (x && ~~ mask n) && ~~ mask m = x && ~~ mask m"
  apply (rule word_eqI)
  apply (simp add: word_size word_ops_nth_size)
  apply safe
  apply simp
  done

(* FIXME: move *)
lemma mask_lower_twice2:
  "(a && ~~ mask n) && ~~ mask m = a && ~~ mask (max n m)"
  by (rule word_eqI, simp add: neg_mask_bang conj_comms)

lemma all_eq_trans: "\<lbrakk> \<forall>x. P x = Q x; \<forall>x. Q x = R x \<rbrakk> \<Longrightarrow> \<forall>x. P x = R x"
  by simp

(* FIXME: move *)
lemma ucast_and_neg_mask:
  "ucast (x && ~~ mask n) = ucast x && ~~ mask n"
  apply (rule word_eqI)
  apply (simp add: word_size neg_mask_bang nth_ucast)
  apply (auto simp add: test_bit_bl word_size)
  done

(* FIXME: move *)
lemma ucast_and_mask:
  "ucast (x && mask n) = ucast x && mask n"
  apply (rule word_eqI)
  apply (simp add: nth_ucast)
  apply (auto simp add: test_bit_bl word_size)
  done

lemma mask_out_8_le_kernel_base:
  "(x && ~~ mask 8 \<ge> kernel_base >> 20) = (x \<ge> kernel_base >> 20)"
  apply (rule iffI)
   apply (erule order_trans, rule word_and_le2)
  apply (drule_tac n=8 in neg_mask_mono_le)
  apply (simp add: kernel_base_def mask_def)
  done

lemma mask_out_8_less_kernel_base:
  "(x && ~~ mask 8 < kernel_base >> 20) = (x < kernel_base >> 20)"
  using mask_out_8_le_kernel_base[where x=x]
  by (simp add: linorder_not_less[symmetric])

(* FIXME: move *)
lemma ucast_mask_drop:
  "len_of TYPE('a :: len) \<le> n \<Longrightarrow> (ucast (x && mask n) :: 'a word) = ucast x"
  apply (rule word_eqI)
  apply (simp add: nth_ucast word_size)
  apply safe
  apply (simp add: test_bit_bl word_size)
  done

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

end
