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
  Include_AI
  "../../lib/LemmaBucket"
  "../../lib/SplitRule"
begin

lemma detype_arch_state :
  "arch_state (detype S s) = arch_state s"
  by (simp add: detype_def)

lemma obj_ref_elemD:
  "r \<in> obj_refs cap \<Longrightarrow> obj_refs cap = {r}"
  by (cases cap, simp_all)

lemma asid_high_bits_of_shift :
  "asid_high_bits_of (ucast x << asid_low_bits) = x"
  apply (simp add: asid_high_bits_of_def)
  apply (rule word_eqI)
  apply (simp add: word_size nth_ucast nth_shiftr nth_shiftl asid_low_bits_def)
  done

lemma  ptrFormPAddr_addFromPPtr :
  "Platform.ptrFromPAddr (Platform.addrFromPPtr x) = x"
  by (simp add: Platform.ptrFromPAddr_def Platform.addrFromPPtr_def)

definition
  "cap_asid_base cap \<equiv> case cap of 
    cap.ArchObjectCap (arch_cap.ASIDPoolCap _ asid) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

lemmas cap_asid_base_simps [simp] = 
  cap_asid_base_def [split_simps cap.split arch_cap.split]

definition
  "diminished cap cap' \<equiv> \<exists>R. cap = mask_cap R cap'"


(****** From GeneralLib *******)

lemma asid_high_bits_of_add_ucast:
  "is_aligned w asid_low_bits \<Longrightarrow> 
  asid_high_bits_of (ucast (x::9 word) + w) = asid_high_bits_of w"
  apply (rule word_eqI)
  apply (simp add: word_size asid_high_bits_of_def nth_ucast nth_shiftr is_aligned_nth)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI) 
   apply (clarsimp simp: nth_ucast)
   apply (drule test_bit_size)
   apply (simp add: word_size asid_low_bits_def)
  apply (auto dest: test_bit_size simp: word_size asid_low_bits_def nth_ucast)
  done

lemma asid_high_bits_of_add:
  "\<lbrakk>is_aligned w asid_low_bits; x \<le> 2 ^ asid_low_bits - 1\<rbrakk>
   \<Longrightarrow> asid_high_bits_of (w + x) = asid_high_bits_of w"
  apply (rule word_eqI)
  apply (simp add: word_size asid_high_bits_of_def nth_ucast nth_shiftr
                   is_aligned_nth)
  apply (drule le2p_bits_unset, simp add: asid_low_bits_def word_bits_def)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size)
   apply (case_tac "na < asid_low_bits")
    apply (simp add: asid_low_bits_def linorder_not_less word_bits_def)
  apply (auto dest: test_bit_size
              simp: asid_low_bits_def nth_ucast)
  done

lemma const_on_failure_wp : 
  "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>rv. Q n\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> const_on_failure n m \<lbrace>Q\<rbrace>"
  apply (simp add: const_on_failure_def)
  apply wp
  apply simp
  done

lemma preemption_point_success [simp,intro]:
  "((Inr (), s') \<in> fst (preemption_point s)) \<Longrightarrow> 
  \<exists>f es. s' = s \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr>, exst := es \<rparr>"
  apply (auto simp: in_monad preemption_point_def do_machine_op_def 
                    select_f_def select_def getActiveIRQ_def alternative_def
                    do_extended_op_def OR_choiceE_def mk_ef_def
             split: option.splits if_splits
             intro: exI[where x=id])
      apply (rule_tac x=Suc in exI, rule_tac x="exst bb" in exI, force)+
    apply (rule_tac x=id in exI, rule_tac x="exst b" in exI, force)+
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

lemma pageBits_less_word_bits [simp]:
  "pageBits < word_bits" by (simp add: pageBits_def word_bits_conv)

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
