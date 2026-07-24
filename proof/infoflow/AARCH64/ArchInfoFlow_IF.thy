(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInfoFlow_IF
imports InfoFlow_IF
begin

context Arch begin arch_global_naming

named_theorems InfoFlow_IF_assms

definition identical_hyp_state_updates ::
  "(obj_ref \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> bool" where
  "identical_hyp_state_updates P s s' ms ms' \<equiv>
     identical_updates_for P (hw_vcpu_of s) (hw_vcpu_of s')
                             (hw_vcpu_of (s\<lparr>machine_state := ms\<rparr>))
                             (hw_vcpu_of (s'\<lparr>machine_state := ms'\<rparr>))"

definition identical_fpu_state_updates ::
  "(obj_ref \<Rightarrow> bool) \<Rightarrow> det_state \<Rightarrow> det_state \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> bool" where
  "identical_fpu_state_updates P s s' ms ms' \<equiv>
     identical_updates_for P (hw_fpu_of s) (hw_fpu_of s')
                             (hw_fpu_of (s\<lparr>machine_state := ms\<rparr>))
                             (hw_fpu_of (s'\<lparr>machine_state := ms'\<rparr>))"

lemma asid_pool_at_kheap:
  "asid_pool_at ptr s = (\<exists>asid_pool. kheap s ptr = Some (ArchObj (ASIDPool asid_pool)))"
  by (simp add: atyp_at_eq_kheap_obj)

lemma equiv_asid:
  "equiv_asid asid s s' = equiv_asid' asid (arm_asid_table (arch_state s) (asid_high_bits_of asid))
                                           (arm_asid_table (arch_state s') (asid_high_bits_of asid))
                                           (kheap s) (kheap s')"
  by (auto simp: equiv_asid_def equiv_asid'_def asid_pool_at_kheap opt_map_def split: option.splits)

lemma equiv_asids_refl[InfoFlow_IF_assms]:
  "equiv_asids R s s"
  by (auto simp: equiv_asids_def equiv_asid_def)

lemma equiv_asids_sym[InfoFlow_IF_assms]:
  "equiv_asids R s t \<Longrightarrow> equiv_asids R t s"
  by (auto simp: equiv_asids_def equiv_asid_def)

lemma equiv_asids_trans[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_asids R s t; equiv_asids R t u \<rbrakk> \<Longrightarrow> equiv_asids R s u"
  by (fastforce simp: equiv_asids_def equiv_asid_def asid_pool_at_kheap asid_pools_of_ko_at obj_at_def)

lemma equiv_asids_guard_imp[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_asids R s s'; \<And>x. Q x \<Longrightarrow> R x \<rbrakk> \<Longrightarrow> equiv_asids Q s s'"
  by (auto simp: equiv_asids_def)

lemma equiv_asids_non_asid_pool_kheap_update[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_asids R s s'; non_asid_pool_kheap_update s kh; non_asid_pool_kheap_update s' kh' \<rbrakk>
     \<Longrightarrow> equiv_asids R (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  apply (clarsimp simp: equiv_asids_def equiv_asid non_asid_pool_kheap_update_def)
  apply (fastforce simp: equiv_asid'_def split: option.splits)
  done

lemma equiv_asids_identical_kheap_updates[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_asids R s s'; identical_kheap_updates s s' kh kh' \<rbrakk>
     \<Longrightarrow> equiv_asids R (s\<lparr>kheap := kh\<rparr>) (s'\<lparr>kheap := kh'\<rparr>)"
  apply (clarsimp simp: equiv_asids_def equiv_asid_def opt_map_def
                        asid_pool_at_kheap identical_kheap_updates_def)
  apply (case_tac "kh pool_ptr = kh' pool_ptr"; fastforce)
  done

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

lemma equiv_hyp_refl[InfoFlow_IF_assms]:
  "equiv_hyp P s s"
  by (auto simp: equiv_hyp_def equiv_for_def)

lemma equiv_hyp_sym[InfoFlow_IF_assms]:
  "equiv_hyp P s t \<Longrightarrow> equiv_hyp P t s"
  by (auto simp: equiv_hyp_def equiv_for_def)

lemma equiv_hyp_trans[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_hyp P s t; equiv_hyp P t u \<rbrakk> \<Longrightarrow> equiv_hyp P s u"
  by (fastforce simp: equiv_hyp_def equiv_for_def)

lemma equiv_hyp_guard_imp[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_hyp P s s'; \<And>x. Q x \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> equiv_hyp Q s s'"
  by (fastforce simp: equiv_hyp_def equiv_for_def)

lemma equiv_hyp_triv':
  "\<lbrakk> equiv_hyp P s s';
     arm_current_vcpu (arch_state t) = arm_current_vcpu (arch_state s);
     arm_current_vcpu (arch_state t') = arm_current_vcpu (arch_state s');
     vcpu_state (machine_state t) = vcpu_state (machine_state s);
     vcpu_state (machine_state t') = vcpu_state (machine_state s');
     arm_gicvcpu_numlistregs (arch_state t) = arm_gicvcpu_numlistregs (arch_state s);
     arm_gicvcpu_numlistregs (arch_state t') = arm_gicvcpu_numlistregs (arch_state s') \<rbrakk>
     \<Longrightarrow> equiv_hyp P t t'"
  by (fastforce simp: equiv_hyp_def equiv_for_def)

lemma equiv_hyp_triv[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_hyp P s s'; arch_state t = arch_state s; arch_state t' = arch_state s';
     machine_state t = machine_state s; machine_state t' = machine_state s' \<rbrakk>
     \<Longrightarrow> equiv_hyp P t t'"
  by (fastforce simp: equiv_hyp_triv')

lemma equiv_hyp_machine_state_update[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_hyp P s s'; identical_hyp_state_updates P s s' ms ms' \<rbrakk>
     \<Longrightarrow> equiv_hyp P (s\<lparr>machine_state := ms\<rparr>) (s'\<lparr>machine_state := ms'\<rparr>)"
  by (fastforce simp: equiv_hyp_def equiv_for_def identical_hyp_state_updates_def identical_updates_def)

lemma equiv_fpu_refl[InfoFlow_IF_assms]:
  "equiv_fpu P s s"
  by (auto simp: equiv_fpu_def equiv_for_def)

lemma equiv_fpu_sym[InfoFlow_IF_assms]:
  "equiv_fpu P s t \<Longrightarrow> equiv_fpu P t s"
  by (auto simp: equiv_fpu_def equiv_for_def)

lemma equiv_fpu_trans[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_fpu P s t; equiv_fpu P t u \<rbrakk> \<Longrightarrow> equiv_fpu P s u"
  by (fastforce simp: equiv_fpu_def equiv_for_def)

lemma equiv_fpu_guard_imp[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_fpu P s s'; \<And>x. Q x \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> equiv_fpu Q s s'"
  by (auto simp: equiv_fpu_def equiv_for_def)

lemma equiv_fpu_triv':
  "\<lbrakk> equiv_fpu P s s'; current_fpu t = current_fpu s; current_fpu t' = current_fpu s';
     fpu_state (machine_state t) = fpu_state (machine_state s);
     fpu_state (machine_state t') = fpu_state (machine_state s') \<rbrakk>
     \<Longrightarrow> equiv_fpu P t t'"
  by (auto simp: equiv_fpu_def equiv_for_def get_tcb_def hw_fpu_def)

lemma equiv_fpu_triv[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_fpu P s s'; arch_state t = arch_state s; arch_state t' = arch_state s';
     machine_state t = machine_state s; machine_state t' = machine_state s' \<rbrakk>
     \<Longrightarrow> equiv_fpu P t t'"
  by (fastforce simp: equiv_fpu_triv')

lemma equiv_fpu_machine_state_update[InfoFlow_IF_assms]:
  "\<lbrakk> equiv_fpu P s s'; identical_fpu_state_updates P s s' ms ms' \<rbrakk>
     \<Longrightarrow> equiv_fpu P (s\<lparr>machine_state := ms\<rparr>) (s'\<lparr>machine_state := ms'\<rparr>)"
  by (fastforce simp: equiv_fpu_def equiv_for_def hw_fpu_def
                      identical_fpu_state_updates_def identical_updates_def
               split: if_splits)

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

lemma equiv_hypI[InfoFlow_IF_assms]:
  assumes "\<And>x. P x \<Longrightarrow> equiv_hyp ((=) x) s t"
  shows "equiv_hyp P s t"
  using assms by (fastforce simp: equiv_hyp_def equiv_for_def)

lemma equiv_fpuI[InfoFlow_IF_assms]:
  assumes "\<And>x. P x \<Longrightarrow> equiv_fpu ((=) x) s t"
  shows "equiv_fpu P s t"
  using assms by (fastforce simp: equiv_fpu_def equiv_for_def)

end

arch_requalify_consts
  identical_hyp_state_updates
  identical_fpu_state_updates


global_interpretation InfoFlow_IF_1?: InfoFlow_IF_1 identical_hyp_state_updates identical_fpu_state_updates
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact InfoFlow_IF_assms)?)
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
        apply (rule_tac R'="(=)" and Q="\<lambda>r s. p && mask 3 = 0" and Q'="\<lambda>r s. p && mask 3 = 0"
                    and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
             apply (rule return_ev2)
             apply (rule_tac f="word_rcat" in arg_cong)
             apply (clarsimp simp: upto.simps)
             apply (fastforce intro: is_aligned_no_wrap' word_plus_mono_right
                               simp: is_aligned_mask for_each_byte_of_word_def word_size_def)
            apply (rule assert_ev2[OF refl])
           apply (rule assert_wp)+
         apply simp+
       apply (clarsimp simp: equiv_valid_2_def in_monad for_each_byte_of_word_def)
       apply (erule equiv_forD)
       apply fastforce
      apply (wp wp_post_taut loadWord_inv | simp)+
  done

definition cur_vcpu_for_2 :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> (obj_ref \<times> bool) option \<rightharpoonup> bool" where
  "cur_vcpu_for_2 P cv \<equiv> case cv of
     None \<Rightarrow> None
   | Some (ptr,b) \<Rightarrow> if P ptr then Some b else None"

locale_abbrev cur_vcpu_for :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> 's state \<rightharpoonup> bool" where
  "cur_vcpu_for P s \<equiv> cur_vcpu_for_2 P (current_vcpu s)"

lemmas cur_vcpu_for_def = cur_vcpu_for_2_def

lemma hw_vcpu_None[simp]:
  "hw_vcpu n None vst = None"
  by (simp add: hw_vcpu_def)

definition equiv_hyp_state :: "nat \<Rightarrow> bool option \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> bool" where
  "equiv_hyp_state n cv ms ms' \<equiv> hw_vcpu n cv (vcpu_state ms) = hw_vcpu n cv (vcpu_state ms')"

definition equiv_fpu_state :: "bool \<Rightarrow> machine_state \<Rightarrow> machine_state \<Rightarrow> bool" where
  "equiv_fpu_state cf ms ms' \<equiv> hw_fpu cf (fpu_state ms) = hw_fpu cf (fpu_state ms')"

definition no_hyp :: "'a machine_monad \<Rightarrow> bool" where
  "no_hyp f \<equiv> \<forall>P. \<lbrace>\<lambda>s. P (vcpu_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vcpu_state s)\<rbrace>"

definition no_fpu :: "'a machine_monad \<Rightarrow> bool" where
  "no_fpu f \<equiv> \<forall>P. \<lbrace>\<lambda>s. P (fpu_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (fpu_state s)\<rbrace>"

lemma equiv_hyp_state_identical_hyp_state_updates:
  "\<lbrakk> equiv_hyp_state (numlistregs s) (cur_vcpu_for P s) ms ms'; equiv_hyp P s t \<rbrakk>
     \<Longrightarrow> identical_hyp_state_updates P s t ms ms'"
  apply (clarsimp simp: equiv_hyp_state_def equiv_for_def identical_hyp_state_updates_def equiv_hyp_def)
  apply (erule_tac x=x in allE)+
  apply (drule mp, fastforce)
  apply (clarsimp simp: cur_vcpu_for_def cur_vcpu_of_def identical_updates_rv_def
                 split: option.splits if_splits)
  done

lemma cur_vcpu_for_None:
  "cur_vcpu_for_2 P None = None"
  by (clarsimp simp: cur_vcpu_for_def)

lemma cur_vcpu_for_Some:
  "cur_vcpu_for_2 P (Some (a,b)) = (if P a then Some b else None)"
  by (clarsimp simp: cur_vcpu_for_def)

lemma cur_vcpu_for_equiv:
  "\<lbrakk> reads_equiv aag st s; affects_equiv aag l st s \<rbrakk>
     \<Longrightarrow> cur_vcpu_for (aag_can_read aag or aag_can_affect aag l) st = cur_vcpu_for (aag_can_read aag or aag_can_affect aag l) s"
  apply (prop_tac "equiv_for (aag_can_read aag or aag_can_affect aag l) cur_vcpu_of st s")
   apply (simp add: equiv_hyp_def equiv_for_or reads_equiv_def2 affects_equiv_def2 states_equiv_for_def)
  apply (case_tac "current_vcpu st"; case_tac "current_vcpu s"; clarsimp)
    apply (clarsimp simp: cur_vcpu_for_None)
    apply (case_tac "(aag_can_read aag or aag_can_affect aag l) a")
     prefer 2
     apply (clarsimp simp: cur_vcpu_for_Some)
    apply (erule equiv_forE)
    apply (erule_tac x=a in meta_allE)
    apply (drule (1) meta_mp)
    apply (clarsimp simp: cur_vcpu_of_def)
   apply (clarsimp simp: cur_vcpu_for_None)
   apply (case_tac "(aag_can_read aag or aag_can_affect aag l) a")
    prefer 2
    apply (clarsimp simp: cur_vcpu_for_Some)
   apply (erule equiv_forE)
   apply (erule_tac x=a in meta_allE)
   apply (drule (1) meta_mp)
   apply (clarsimp simp: cur_vcpu_of_def)
  apply (case_tac "(aag_can_read aag or aag_can_affect aag l) a"; case_tac "(aag_can_read aag or aag_can_affect aag l) aa")
     apply (erule equiv_forE)
     apply (erule_tac x=a in meta_allE)
     apply (drule (1) meta_mp)
     apply (clarsimp simp: cur_vcpu_of_def split: if_splits)
    apply (erule equiv_forE)
    apply (erule_tac x=a in meta_allE)
    apply (drule (1) meta_mp)
    apply (clarsimp simp: cur_vcpu_of_def split: if_splits)
   apply (erule equiv_forE)
   apply (erule_tac x=aa in meta_allE)
   apply (drule (1) meta_mp)
   apply (clarsimp simp: cur_vcpu_of_def split: if_splits)
  apply (clarsimp simp: cur_vcpu_for_Some)
  done

lemma aequiv_get_tcb_eq'[intro]:
  "\<lbrakk> affects_equiv aag l s t; aag_can_affect aag l thread \<rbrakk>
     \<Longrightarrow> get_tcb thread s = get_tcb thread t"
  by (auto simp: affects_equiv_def2 get_tcb_def elim: states_equiv_forE_kheap)

definition cur_fpu_for :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> 's state \<Rightarrow> bool" where
  "cur_fpu_for P s \<equiv> \<exists>ptr. P ptr \<and> is_arch_cur_fpu ptr s"

lemma equiv_fpu_cur_fpu_for:
  "equiv_fpu P st s \<Longrightarrow> cur_fpu_for P st = cur_fpu_for P s"
  apply (clarsimp simp: equiv_fpu_def equiv_for_def cur_fpu_for_def)
  apply (rule iffI; erule ex_forward; erule_tac x=ptr in allE; clarsimp simp: hw_fpu_def split: if_splits)
  done

lemma cur_fpu_for_equiv:
  "\<lbrakk> reads_equiv aag st s; affects_equiv aag l st s \<rbrakk>
     \<Longrightarrow> cur_fpu_for (aag_can_read aag or aag_can_affect aag l) st =
         cur_fpu_for (aag_can_read aag or aag_can_affect aag l) s"
  apply (prop_tac "equiv_fpu (aag_can_read aag or aag_can_affect aag l) st s")
   apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_fpu_def equiv_for_def)
  apply (simp add: equiv_fpu_cur_fpu_for)
  done

lemma equiv_fpu_state_identical_fpu_state_updates:
  "\<lbrakk> equiv_fpu_state (cur_fpu_for P s) ms ms'; equiv_fpu P s t \<rbrakk>
     \<Longrightarrow> identical_fpu_state_updates P s t ms ms'"
  unfolding identical_fpu_state_updates_def
  apply (clarsimp simp: identical_fpu_state_updates_def identical_updates_def)
  apply (clarsimp simp: equiv_fpu_state_def equiv_for_def equiv_fpu_def)
  apply (erule_tac x=x in allE, clarsimp)
  apply (auto simp: cur_fpu_for_def hw_fpu_def get_tcb_def identical_updates_rv_def split: if_splits option.splits kernel_object.splits)
  done

definition numlistregs_for :: "(obj_ref \<Rightarrow> bool) \<Rightarrow> 's state \<Rightarrow> nat" where
  "numlistregs_for P s \<equiv> if \<exists>p. P p then numlistregs s else undefined"

lemma numlistregs_for_equiv:
  "\<lbrakk> reads_equiv aag st s; affects_equiv aag l st s \<rbrakk>
     \<Longrightarrow> numlistregs_for (aag_can_read aag or aag_can_affect aag l) st = numlistregs_for (aag_can_read aag or aag_can_affect aag l) s"
  by (auto simp: reads_equiv_def2 affects_equiv_def2 states_equiv_for_def equiv_hyp_def equiv_for_def numlistregs_for_def)

lemma equiv_hyp_state_sym:
  "equiv_hyp_state n cv ms' ms \<Longrightarrow> equiv_hyp_state n cv ms ms'"
  by (simp add: equiv_hyp_state_def)

lemma equiv_fpu_state_sym:
  "equiv_fpu_state cf ms' ms \<Longrightarrow> equiv_fpu_state cf ms ms'"
  by (simp add: equiv_fpu_state_def)

lemma spec_equiv_valid_add_inv:
  assumes "spec_equiv_valid st I A B (P and I st) f"
  and "\<And>s. I s s"
  shows "spec_equiv_valid st I A B P f"
  using assms by (fastforce simp: spec_equiv_valid_def equiv_valid_2_def)

lemma spec_equiv_valid_add_A:
  assumes "spec_equiv_valid st I A B (P and A st) f"
  and "\<And>s. A s s"
  shows "spec_equiv_valid st I A B P f"
  using assms by (fastforce simp: spec_equiv_valid_def equiv_valid_2_def)

lemma do_machine_op_reads_respects'':
  assumes equiv_dmo:
   "\<And>n cv cf. equiv_valid_inv (equiv_irq_state and equiv_machine_state (aag_can_read aag)
                                                and equiv_hyp_state n cv and equiv_fpu_state cf)
                               (equiv_machine_state (aag_can_affect aag l)) (Q n cv cf) f"
  assumes guard:
    "\<And>s. P s \<Longrightarrow> Q (numlistregs_for (aag_can_read aag or aag_can_affect aag l) s)
                    (cur_vcpu_for (aag_can_read aag or aag_can_affect aag l) s)
                    (cur_fpu_for (aag_can_read aag or aag_can_affect aag l) s)
                    (machine_state s)"
    (is "\<And>s. P s \<Longrightarrow> Q (?nlf s) (?cvf s) (?cff s) (machine_state s)")
  shows
    "reads_respects aag l P (do_machine_op f)"
  apply (rule use_spec_ev)
  apply (rule spec_equiv_valid_add_inv)
   prefer 2
   apply (simp add: reads_equiv_refl)
  apply (rule spec_equiv_valid_add_A)
   prefer 2
   apply (simp add: affects_equiv_refl)
  apply (unfold do_machine_op_def spec_equiv_valid_def)
  supply equiv_for_disj[simp]
  apply (rule equiv_valid_2_guard_imp)
    apply (rule_tac R'="\<lambda>rv rv'. equiv_machine_state (aag_can_read_or_affect aag l) rv rv' \<and>
                                 equiv_irq_state rv rv' \<and>
                                 equiv_hyp_state (?nlf st) (?cvf st) rv rv' \<and>
                                 equiv_fpu_state (?cff st) rv rv'"
                and Q="\<lambda>r s. st = s \<and> Q (?nlf st) (?cvf st) (?cff st) r"
                and Q'="\<lambda>r s. Q (?nlf st) (?cvf st)
                                (?cff st) r"
                and P="(=) st" and P'="\<top>" in equiv_valid_2_bind)
       apply (rule gen_asm_ev2_l[simplified K_def pred_conj_def])
       apply (rule gen_asm_ev2_r')
       apply (rule_tac R'="\<lambda>(r, ms') (r', ms''). r = r'
                                               \<and> equiv_machine_state (aag_can_read_or_affect aag l) ms' ms''
                                               \<and> equiv_irq_state ms' ms''
                                               \<and> equiv_hyp_state (?nlf st) (?cvf st) ms' ms''
                                               \<and> equiv_fpu_state (?cff st) ms' ms''"
                   and Q="\<lambda>r s. s = st"
                   and Q'="\<top>\<top>"
                   and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
            apply (clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
            apply (rule conjI)
             apply (rule reads_equiv_machine_state_update; clarsimp?)
              apply (rule equiv_hyp_state_identical_hyp_state_updates)
               apply (clarsimp simp: equiv_hyp_state_def cur_vcpu_for_def numlistregs_for_def
                              split: option.splits if_splits)
              apply (erule reads_equivE, clarsimp simp: equiv_hyp_def)
             apply (rule equiv_fpu_state_identical_fpu_state_updates)
              apply (fastforce simp: equiv_fpu_state_def cur_fpu_for_def hw_fpu_def
                              split: option.splits if_splits)
             apply (erule reads_equivE, clarsimp simp: equiv_fpu_def)
            apply (rule affects_equiv_machine_state_update; clarsimp?)
             apply (rule equiv_hyp_state_identical_hyp_state_updates)
              apply (clarsimp simp: equiv_hyp_state_def cur_vcpu_for_def numlistregs_for_def
                             split: option.splits if_splits)
             apply (erule affects_equivE, clarsimp simp: equiv_hyp_def)
            apply (rule equiv_fpu_state_identical_fpu_state_updates)
             apply (fastforce simp: equiv_fpu_state_def cur_fpu_for_def hw_fpu_def
                             split: option.splits if_splits)
            apply (erule affects_equivE, clarsimp simp: equiv_fpu_def)
           apply (insert equiv_dmo)[1]
           apply (clarsimp simp: select_f_def equiv_valid_2_def equiv_valid_def2 equiv_for_or
                           simp: split_def split: prod.splits simp: equiv_for_def)[1]
           apply (erule_tac x="?nlf st" in meta_allE)
           apply (erule_tac x="?cvf st" in meta_allE)
           apply (erule_tac x="?cff st" in meta_allE)
           apply (drule_tac x=rv in spec, drule_tac x=rv' in spec)
           apply clarsimp
           apply (drule (1) bspec)+
           apply clarsimp
          apply wp
         apply wp
        apply clarsimp
       apply clarsimp
      apply (clarsimp simp: equiv_valid_2_def in_monad)
      apply (intro conjI)
            apply (fastforce elim: reads_equivE affects_equivE equiv_forE intro: equiv_forI)
           apply (fastforce elim: reads_equivE affects_equivE equiv_forE intro: equiv_forI)
          apply (fastforce elim: reads_equivE affects_equivE equiv_forE intro: equiv_forI)
         apply (fastforce elim: reads_equivE affects_equivE equiv_forE intro: equiv_forI)
        apply (fastforce elim: reads_equivE affects_equivE equiv_forE intro: equiv_forI)
       apply (frule (1) cur_vcpu_for_equiv)
       apply (clarsimp simp: equiv_hyp_state_def)
       apply (prop_tac "equiv_for (aag_can_read aag or aag_can_affect aag l) (K \<circ> numlistregs) st t")
        apply (simp add: equiv_hyp_def equiv_for_or reads_equiv_def2 affects_equiv_def2 states_equiv_for_def)
       apply (prop_tac "equiv_for (aag_can_read aag or aag_can_affect aag l) hw_vcpu_of st t")
        apply (simp add: equiv_hyp_def equiv_for_or reads_equiv_def2 affects_equiv_def2 states_equiv_for_def)
       apply (case_tac "cur_vcpu_for (aag_can_read aag or aag_can_affect aag l) t"; clarsimp)
       apply (clarsimp simp: cur_vcpu_for_def split: option.splits if_splits)
       apply (erule equiv_forE)+
       apply (erule_tac x=aa in meta_allE, clarsimp)+
       apply (clarsimp simp: cur_vcpu_of_def hw_vcpu_def numlistregs_for_def split: if_splits)
      apply (frule (1) cur_fpu_for_equiv)
      apply (clarsimp simp: equiv_fpu_state_def)
      apply (prop_tac "equiv_for ((aag_can_read aag or aag_can_affect aag l)) hw_fpu_of st t")
       apply (simp add: equiv_fpu_def equiv_for_or reads_equiv_def2 affects_equiv_def2 states_equiv_for_def)
      apply (fastforce simp: equiv_for_def hw_fpu_def cur_fpu_for_def split: if_splits)
     apply (wp | simp add: guard)+
  using guard cur_fpu_for_equiv cur_vcpu_for_equiv numlistregs_for_equiv apply fastforce
  done

lemma do_machine_op_reads_respects'[InfoFlow_IF_assms]:
  assumes equiv_dmo:
    "equiv_valid_inv (equiv_machine_state (aag_can_read aag) and equiv_irq_state)
                    (equiv_machine_state (aag_can_affect aag l)) Q f"
  assumes guard: "\<And>s. P s \<Longrightarrow> Q (machine_state s)"
  assumes no_hyp: "no_hyp f"
  assumes no_fpu: "no_fpu f"
  shows "reads_respects aag l P (do_machine_op f)"
  apply (rule do_machine_op_reads_respects''[where Q="\<lambda>_ _ _. Q"])
   apply (insert equiv_dmo no_hyp no_fpu)
   apply (clarsimp simp: equiv_valid_2_def equiv_valid_def2 equiv_for_or no_hyp_def no_fpu_def
                         equiv_for_def split_def)
   apply (rename_tac rv st rv' st')
   apply (drule_tac x=s in spec, drule_tac x=t in spec)
   apply clarsimp
   apply (drule (1) bspec)+
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: equiv_hyp_state_def)
    apply (erule use_valid, erule spec)+
    apply clarsimp
   apply (clarsimp simp: equiv_fpu_state_def)
   apply (erule use_valid, erule spec)+
   apply clarsimp
  apply (simp add: guard)
  done

lemma equiv_hyp_state_upds[simp]:
  "\<And>f. equiv_hyp_state n cv ms (underlying_memory_update f ms') = equiv_hyp_state n cv ms ms'"
  "\<And>f. equiv_hyp_state n cv (underlying_memory_update f ms) ms' = equiv_hyp_state n cv ms ms'"
  "\<And>f. equiv_hyp_state n cv ms (device_state_update f ms') = equiv_hyp_state n cv ms ms'"
  "\<And>f. equiv_hyp_state n cv (device_state_update f ms) ms' = equiv_hyp_state n cv ms ms'"
  "\<And>f. equiv_hyp_state n cv ms (machine_state_rest_update f ms') = equiv_hyp_state n cv ms ms'"
  "\<And>f. equiv_hyp_state n cv (machine_state_rest_update f ms) ms' = equiv_hyp_state n cv ms ms'"
  by (auto simp: equiv_hyp_state_def)

lemma equiv_fpu_state_upds[simp]:
  "\<And>f. equiv_fpu_state cf ms (underlying_memory_update f ms') = equiv_fpu_state cf ms ms'"
  "\<And>f. equiv_fpu_state cf (underlying_memory_update f ms) ms' = equiv_fpu_state cf ms ms'"
  "\<And>f. equiv_fpu_state cf ms (device_state_update f ms') = equiv_fpu_state cf ms ms'"
  "\<And>f. equiv_fpu_state cf (device_state_update f ms) ms' = equiv_fpu_state cf ms ms'"
  "\<And>f. equiv_fpu_state cf ms (machine_state_rest_update f ms') = equiv_fpu_state cf ms ms'"
  "\<And>f. equiv_fpu_state cf (machine_state_rest_update f ms) ms' = equiv_fpu_state cf ms ms'"
  by (auto simp: equiv_fpu_state_def)

lemma no_hyp_bind:
  "\<lbrakk> no_hyp f; \<And>rv. no_hyp (g rv) \<rbrakk> \<Longrightarrow> no_hyp (f >>= g)"
  unfolding no_hyp_def
  by (wpsimp, blast+)

lemma no_fpu_bind:
  "\<lbrakk> no_fpu f; \<And>rv. no_fpu (g rv) \<rbrakk> \<Longrightarrow> no_fpu (f >>= g)"
  unfolding no_fpu_def
  by (wpsimp, blast+)

lemma equiv_hyp_state_lift[wp]:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vcpu_state s)\<rbrace>"
  shows "f \<lbrace>equiv_hyp_state n cv st\<rbrace>"
  unfolding equiv_hyp_state_def
  by (wp assms)

lemma equiv_fpu_state_lift[wp]:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (fpu_state s)\<rbrace>"
  shows "f \<lbrace>equiv_fpu_state cf st\<rbrace>"
  unfolding equiv_fpu_state_def
  by (wp assms)

lemma no_hyp_lift[wp]:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vcpu_state s)\<rbrace>"
  shows "no_hyp f"
  using assms by (simp add: no_hyp_def)

lemma no_fpu_lift[wp]:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (fpu_state s)\<rbrace>"
  shows "no_fpu f"
  using assms by (simp add: no_fpu_def)

end

arch_requalify_consts
  no_hyp no_fpu


global_interpretation InfoFlow_IF_2?: InfoFlow_IF_2 identical_hyp_state_updates identical_fpu_state_updates no_hyp no_fpu
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact InfoFlow_IF_assms)?)
qed

end
