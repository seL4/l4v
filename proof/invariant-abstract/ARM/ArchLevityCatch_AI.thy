(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchLevityCatch_AI
imports
  "../BCorres_AI"
  "../../../lib/LemmaBucket"
  "../../../lib/SplitRule"
begin

context Arch begin global_naming ARM

lemma asid_high_bits_of_shift :
  "asid_high_bits_of (ucast x << asid_low_bits) = x"
  apply (simp add: asid_high_bits_of_def)
  apply (rule word_eqI)
  apply (simp add: word_size nth_ucast nth_shiftr nth_shiftl asid_low_bits_def)
  done

lemma  ptrFormPAddr_addFromPPtr :
  "ptrFromPAddr (Platform.ARM.addrFromPPtr x) = x"
  by (simp add: ptrFromPAddr_def Platform.ARM.addrFromPPtr_def)

(****** From GeneralLib *******)

lemma asid_high_bits_of_add_ucast:
  "is_aligned w asid_low_bits \<Longrightarrow> 
  asid_high_bits_of (ucast (x::10 word) + w) = asid_high_bits_of w"
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
  apply (drule le2p_bits_unset_32, simp add: asid_low_bits_def)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size)
   apply (case_tac "na < asid_low_bits")
    apply (simp add: asid_low_bits_def linorder_not_less word_bits_def)
  apply (auto dest: test_bit_size
              simp: asid_low_bits_def word_bits_def nth_ucast)
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

lemma pageBits_less_word_bits [simp]:
  "pageBits < word_bits" by (simp add: pageBits_def word_bits_conv)

end
end