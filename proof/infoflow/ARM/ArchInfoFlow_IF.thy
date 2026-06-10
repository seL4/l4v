(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInfoFlow_IF
imports InfoFlow_IF
begin

context Arch begin global_naming ARM

named_theorems InfoFlow_IF_assms

lemma asid_pool_at_kheap:
  "asid_pool_at ptr s = (\<exists>asid_pool. kheap s ptr = Some (ArchObj (ASIDPool asid_pool)))"
  by (simp add: atyp_at_eq_kheap_obj)

lemma equiv_asid:
  "equiv_asid asid s s' = equiv_asid' asid (arm_asid_table (arch_state s) (asid_high_bits_of asid))
                                           (arm_asid_table (arch_state s') (asid_high_bits_of asid))
                                           (kheap s) (kheap s')"
  by (auto simp: equiv_asid_def equiv_asid'_def asid_pool_at_kheap split: option.splits )

lemma equiv_asids_refl[InfoFlow_IF_assms]:
  "equiv_asids R s s"
  by (auto simp: equiv_asids_def equiv_asid_def)

lemma equiv_asids_sym[InfoFlow_IF_assms]:
  "equiv_asids R s t \<Longrightarrow> equiv_asids R t s"
  by (auto simp: equiv_asids_def equiv_asid_def)

lemma equiv_asids_trans[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_asids R s t; equiv_asids R t u \<rbrakk> \<Longrightarrow> equiv_asids R s u"
  by (fastforce simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap)

lemma equiv_asids_non_asid_pool_kheap_update[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_asids R s s'; non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh' \<rbrakk>
     \<Longrightarrow> equiv_asids R (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  apply (clarsimp simp: equiv_asids_def equiv_asid non_asid_pool_kheap_update_def)
  apply (fastforce simp: equiv_asid'_def split: option.splits)
  done

lemma equiv_asids_identical_kheap_updates[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_asids R s s'; identical_kheap_updates s s' kh kh' \<rbrakk>
     \<Longrightarrow> equiv_asids R (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  apply (clarsimp simp: equiv_asids_def equiv_asid_def identical_kheap_updates_def asid_pool_at_kheap)
  apply (case_tac "kh pool_ptr = kh' pool_ptr"; fastforce)
  done

lemma equiv_asids_trivial[InfoFlow_IF_assms]:
  "(\<And>x. P x \<Longrightarrow> False) \<Longrightarrow> equiv_asids P x y"
  by (auto simp: equiv_asids_def)

lemma equiv_asids_triv':
  "\<lbrakk> equiv_asids R s s'; kheap t = kheap s; kheap t' = kheap s';
     arm_asid_table (arch_state t) = arm_asid_table (arch_state s);
     arm_asid_table (arch_state t') = arm_asid_table (arch_state s') \<rbrakk>
     \<Longrightarrow> equiv_asids R t t'"
  by (fastforce simp: equiv_asids_def equiv_asid equiv_asid'_def)

lemma equiv_asids_triv[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_asids R s s'; kheap t = kheap s; kheap t' = kheap s';
     arch_state t = arch_state s; arch_state t' = arch_state s' \<rbrakk>
     \<Longrightarrow> equiv_asids R t t'"
  by (fastforce simp: equiv_asids_triv')

lemma globals_equiv_refl[InfoFlow_IF_assms]:
  "globals_equiv s s"
  by (simp add: globals_equiv_def idle_equiv_refl)

lemma globals_equiv_sym[InfoFlow_IF_assms]:
  "globals_equiv s t \<Longrightarrow> globals_equiv t s"
  by (auto simp: globals_equiv_def idle_equiv_def)

lemma globals_equiv_trans[InfoFlow_IF_assms]:
  "\<lbrakk> globals_equiv s t; globals_equiv t u \<rbrakk> \<Longrightarrow> globals_equiv s u"
  unfolding globals_equiv_def arch_globals_equiv_def
  by clarsimp (metis idle_equiv_trans idle_equiv_def)

lemma equiv_asids_guard_imp[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_asids R s s'; \<And>x. Q x \<Longrightarrow> R x \<rbrakk> \<Longrightarrow> equiv_asids Q s s'"
  by (auto simp: equiv_asids_def)


definition identical_hyp_state_updates :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> bool" where
  "identical_hyp_state_updates _ _ _ _ _ \<equiv> True"

definition identical_fpu_state_updates :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> bool" where
  "identical_fpu_state_updates _ _ _ _ _ \<equiv> True"

definition no_hyp :: "'m machine_monad \<Rightarrow> bool" where
  "no_hyp f \<equiv> True"

definition no_fpu :: "'m machine_monad \<Rightarrow> bool" where
  "no_fpu f \<equiv> True"

lemma equiv_hyp_dummy[intro!,simp]:
  "equiv_hyp P s s'"
  by (simp add: equiv_hyp_def)

lemma equiv_fpu_dummy[intro!,simp]:
  "equiv_fpu P s s'"
  by (simp add: equiv_fpu_def)

lemma identical_hyp_states_updates_dummy[intro!,simp]:
  "identical_hyp_state_updates P s s' ms ms'"
  by (simp add: identical_hyp_state_updates_def)

lemma identical_fpu_states_updates_dummy[intro!,simp]:
  "identical_fpu_state_updates P s s' ms ms'"
  by (simp add: identical_fpu_state_updates_def)

lemma no_hyp_dummy[intro!,simp]:
  "no_hyp f"
  by (simp add: no_hyp_def)

lemma no_fpu_dummy[intro!,simp]:
  "no_fpu f"
  by (simp add: no_fpu_def)

lemmas equiv_arch_dummy =
  equiv_hyp_dummy
  equiv_fpu_dummy
  identical_hyp_states_updates_dummy
  identical_fpu_states_updates_dummy
  no_hyp_dummy
  no_fpu_dummy

end

arch_requalify_consts
  identical_hyp_state_updates
  identical_fpu_state_updates
  no_hyp
  no_fpu


global_interpretation InfoFlow_IF_1?: InfoFlow_IF_1 identical_hyp_state_updates identical_fpu_state_updates
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact InfoFlow_IF_assms | solves \<open>rule equiv_arch_dummy\<close>)?)
qed


context Arch begin arch_global_naming

lemma dmo_loadWord_rev[InfoFlow_IF_assms]:
  "reads_equiv_valid_inv A aag (K (for_each_byte_of_word (aag_can_read aag) p))
                               (do_machine_op (loadWord p))"
  apply (rule gen_asm_ev)
  apply (rule use_spec_ev)
  apply (rule spec_equiv_valid_hoist_guard)
  apply (rule do_machine_op_spec_rev)
   apply (simp add: loadWord_def equiv_valid_def2 spec_equiv_valid_def)
   apply (rule_tac R'="\<lambda>rv rv'. for_each_byte_of_word (\<lambda>y. rv y = rv' y) p" and Q="\<top>\<top>" and Q'="\<top>\<top>"
               and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
        apply (rule_tac R'="(=)" and Q="\<lambda>r s. p && mask 2 = 0" and Q'="\<lambda>r s. p && mask 2 = 0"
                    and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
             apply (rule return_ev2)
             apply (rule_tac f="word_rcat" in arg_cong)
             apply (fastforce intro: is_aligned_no_wrap' word_plus_mono_right
                               simp: is_aligned_mask for_each_byte_of_word_def word_size_def) (* slow *)
            apply (rule assert_ev2[OF refl])
           apply (rule assert_wp)+
         apply simp+
       apply (clarsimp simp: equiv_valid_2_def in_monad for_each_byte_of_word_def)
       apply (erule equiv_forD)
       apply fastforce
      apply (wp wp_post_taut loadWord_inv | simp)+
  done

lemma do_machine_op_reads_respects'[InfoFlow_IF_assms]:
  assumes equiv_dmo:
   "equiv_valid_inv (equiv_machine_state (aag_can_read aag) and equiv_irq_state)
                    (equiv_machine_state (aag_can_affect aag l)) Q f"
  assumes guard:
    "\<And>s. P s \<Longrightarrow> Q (machine_state s)"
  and no_hyp: "no_hyp f"
  and no_fpu: "no_fpu f"
  shows
  "reads_respects aag l P (do_machine_op f)"
  apply (rule use_spec_ev)
  unfolding do_machine_op_def spec_equiv_valid_def
  apply (rule equiv_valid_2_guard_imp)
   apply (rule_tac  R'="\<lambda> rv rv'. equiv_machine_state (aag_can_read aag or aag_can_affect aag l) rv rv' \<and> equiv_irq_state rv rv'" and Q="\<lambda> r s. st = s \<and> Q r" and Q'="\<lambda> r s. Q r" and P="(=) st" and P'="\<top>" in equiv_valid_2_bind)
       apply (rule gen_asm_ev2_l[simplified K_def pred_conj_def])
       apply (rule gen_asm_ev2_r')
       apply (rule_tac R'="\<lambda> (r, ms') (r', ms'').  r = r' \<and> equiv_machine_state (aag_can_read aag)  ms' ms'' \<and> equiv_machine_state (aag_can_affect aag l) ms' ms'' \<and> equiv_irq_state ms' ms''" and Q="\<lambda> r s. st = s" and Q'="\<top>\<top>" and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
            apply (clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
            apply (fastforce intro: reads_equiv_machine_state_update affects_equiv_machine_state_update)
            apply (insert equiv_dmo)[1]
           apply (clarsimp simp: select_f_def equiv_valid_2_def equiv_valid_def2 equiv_for_or simp: split_def split: prod.splits simp: equiv_for_def)[1]
           apply (drule_tac x=rv in spec, drule_tac x=rv' in spec)
           apply (fastforce)
          apply (rule select_f_inv)
         apply (rule wp_post_taut)
        apply simp+
      apply (clarsimp simp: equiv_valid_2_def in_monad)
      apply (fastforce elim: reads_equivE affects_equivE equiv_forE intro: equiv_forI)
     apply (wp | simp add: guard)+
  done

end


global_interpretation InfoFlow_IF_1?: InfoFlow_IF_2 identical_hyp_state_updates identical_fpu_state_updates no_hyp no_fpu
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact InfoFlow_IF_assms | solves \<open>rule equiv_arch_dummy\<close>)?)
qed

end
