(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_IF
imports ArchRetype_IF
begin

abbreviation irq_state_of_state :: "det_state \<Rightarrow> nat" where
  "irq_state_of_state s \<equiv> irq_state (machine_state s)"


crunches cap_insert, cap_swap_for_delete
  for irq_state_of_state[wp]: "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps)

lemma do_extended_op_irq_state_of_state[wp]:
  "do_extended_op f \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  by (wpsimp wp: dxo_wp_weak)

lemma no_irq_underlying_memory_update[simp]:
  "no_irq (modify (underlying_memory_update f))"
  by (wpsimp simp: no_irq_def)

lemma detype_irq_state_of_state[simp]:
  "irq_state_of_state (detype S s) = irq_state_of_state s"
  by (simp add: detype_def)

lemma gets_applyE:
  "liftE (gets f) >>=E (\<lambda>f. g (f x)) = liftE (gets_apply f x) >>=E g"
  apply (simp add: liftE_bindE)
  apply (rule gets_apply)
  done

lemma aag_can_read_own_asids:
  "is_subject_asid aag asid \<Longrightarrow> aag_can_read_asid aag asid"
  by simp

(* for things that only modify parts of the state not in the state relations,
   we don't care what they read since these reads are unobservable anyway;
   however, we cannot assert anything about their return-values *)
lemma equiv_valid_2_unobservable:
  assumes f:
    "\<And>P Q R S st. \<lbrace>states_equiv_for P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes f':
    "\<And>P Q R S st. \<lbrace>states_equiv_for P Q R S st\<rbrace> f' \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes g:
    "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes g':
    "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f' \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes h:
    "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes h':
    "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f' \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes j:
    "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes j':
    "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f' \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes k:
    "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s)\<rbrace> f \<lbrace>\<lambda>rv s. P (work_units_completed s)\<rbrace>"
  assumes k':
    "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s)\<rbrace> f' \<lbrace>\<lambda>rv s. P (work_units_completed s)\<rbrace>"
  assumes l:
    "\<And>P. \<lbrace>\<lambda>s. P (irq_state (machine_state s))\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_state (machine_state s))\<rbrace>"
  assumes l':
    "\<And>P. \<lbrace>\<lambda>s. P (irq_state (machine_state s))\<rbrace> f' \<lbrace>\<lambda>rv s. P (irq_state (machine_state s))\<rbrace>"
  shows
    "equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) \<top>\<top> \<top> \<top> f f'"
  apply (clarsimp simp: equiv_valid_2_def)
  apply (frule use_valid[OF _ f])
   apply (rule states_equiv_for_refl)
  apply (frule use_valid[OF _ f'])
   apply (rule states_equiv_for_refl)
  apply (frule use_valid[OF _ f])
   apply (rule states_equiv_for_refl)
  apply (frule use_valid[OF _ f'])
   apply (rule states_equiv_for_refl)
  apply (frule use_valid)
    apply (rule_tac P="(=) (cur_thread s)" in g)
   apply (rule refl)
  apply (frule_tac f=f' in use_valid)
    apply (rule_tac P="(=) (cur_thread t)" in g')
   apply (rule refl)
  apply (frule use_valid)
    apply (rule_tac P="(=) (cur_domain s)" in h)
   apply (rule refl)
  apply (frule_tac f=f' in use_valid)
    apply (rule_tac P="(=) (cur_domain t)" in h')
   apply (rule refl)
  apply (frule use_valid)
    apply (rule_tac P="(=) (scheduler_action s)" in j)
   apply (rule refl)
  apply (frule_tac f=f' in use_valid)
    apply (rule_tac P="(=) (scheduler_action t)" in j')
   apply (rule refl)
  apply (frule use_valid)
    apply (rule_tac P="(=) (work_units_completed s)" in k)
   apply (rule refl)
  apply (frule_tac f=f' in use_valid)
    apply (rule_tac P="(=) (work_units_completed t)" in k')
   apply (rule refl)
  apply (frule use_valid)
    apply (rule_tac P="(=) (irq_state (machine_state s))" in l)
   apply (rule refl)
  apply (frule_tac f=f' in use_valid)
    apply (rule_tac P="(=) (irq_state (machine_state t))" in l')
   apply (rule refl)
  apply (clarsimp simp: reads_equiv_def2 affects_equiv_def2)
  apply (auto intro: states_equiv_for_sym states_equiv_for_trans)
  done

lemma reads_respects_unobservable_unit_return:
  assumes f:
    "\<And>P Q R S st. \<lbrace>states_equiv_for P Q R S st\<rbrace> f \<lbrace>\<lambda>_. states_equiv_for P Q R S st\<rbrace>"
  assumes g:
    "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes h:
    "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes j:
    "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes k:
    "\<And>P. \<lbrace>\<lambda>s. P (work_units_completed s)\<rbrace> f \<lbrace>\<lambda>rv s. P (work_units_completed s)\<rbrace>"
  assumes l:
    "\<And>P. \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_state_of_state s)\<rbrace>"
  shows
    "reads_respects aag l \<top> (f::(unit,det_ext) s_monad)"
  apply (subgoal_tac "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> f")
   apply (clarsimp simp: equiv_valid_2_def equiv_valid_def2)
  apply (rule equiv_valid_2_unobservable[OF f f g g h h j j k k l l])
  done

lemma dmo_mol_irq_state_of_state[wp]:
  "do_machine_op (machine_op_lift m) \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  by (wpsimp wp: dmo_wp)

lemma throw_on_false_reads_respects:
  "reads_respects aag l P f
   \<Longrightarrow> reads_respects aag l P (throw_on_false ex f)"
  unfolding throw_on_false_def fun_app_def unlessE_def by wpsimp

lemma dmo_mol_2_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (machine_op_lift mop >>= (\<lambda> y. machine_op_lift mop')))"
  apply (rule use_spec_ev)
  apply (rule do_machine_op_spec_reads_respects)
  by (wpsimp wp: machine_op_lift_ev)+

lemma tl_subseteq:
  "set (tl xs) \<subseteq> set xs"
  by (induct xs, auto)


abbreviation(input) aag_can_read_label where
  "aag_can_read_label aag l \<equiv> l \<in> subjectReads (pasPolicy aag) (pasSubject aag)"

definition labels_are_invisible where
  "labels_are_invisible aag l L \<equiv>
     (\<forall>d \<in> L. \<not> aag_can_read_label aag d) \<and>
     (aag_can_affect_label aag l \<longrightarrow> (\<forall>d \<in> L. d \<notin> subjectReads (pasPolicy aag) l))"


lemma equiv_but_for_reads_equiv:
  "\<lbrakk> pas_domains_distinct aag; labels_are_invisible aag l L; equiv_but_for_labels aag L s s' \<rbrakk>
     \<Longrightarrow> reads_equiv aag s s'"
  apply (simp add: reads_equiv_def2)
  apply (rule conjI)
   apply (clarsimp simp: labels_are_invisible_def equiv_but_for_labels_def)
   apply (rule states_equiv_forI)
            apply (fastforce intro: equiv_forI elim: states_equiv_forE equiv_forD)+
       apply (auto intro!: equiv_forI elim!: states_equiv_forE elim!: equiv_forD simp: o_def)[1]
      apply (fastforce intro: equiv_forI elim: states_equiv_forE equiv_forD)+
    apply (fastforce simp: equiv_asids_def elim: states_equiv_forE elim: equiv_forD)
   apply (clarsimp simp: equiv_for_def states_equiv_for_def disjoint_iff_not_equal)
   apply (metis pas_domains_distinct_inj)
  apply (fastforce simp: equiv_but_for_labels_def)
  done

lemma equiv_but_for_affects_equiv:
  "\<lbrakk> pas_domains_distinct aag; labels_are_invisible aag l L; equiv_but_for_labels aag L s s' \<rbrakk>
     \<Longrightarrow> affects_equiv aag l s s'"
  apply (subst affects_equiv_def2)
  apply (clarsimp simp: labels_are_invisible_def equiv_but_for_labels_def aag_can_affect_label_def)
  apply (rule states_equiv_forI)
           apply (fastforce intro!: equiv_forI elim!: states_equiv_forE equiv_forD)+
   apply (fastforce simp: equiv_asids_def elim!: states_equiv_forE elim!: equiv_forD)
  apply (clarsimp simp: equiv_for_def states_equiv_for_def disjoint_iff_not_equal)
  apply (metis pas_domains_distinct_inj)
  done

(* consider rewriting the return-value assumption using equiv_valid_rv_inv *)
lemma ev2_invisible:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "\<lbrakk> labels_are_invisible aag l L; labels_are_invisible aag l L';
     modifies_at_most aag L Q f; modifies_at_most aag L' Q' g;
     \<forall>s t. P s \<and> P' t \<longrightarrow> (\<forall>(rva,s') \<in> fst (f s). \<forall>(rvb,t') \<in> fst (g t). W rva rvb) \<rbrakk>
     \<Longrightarrow> equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
                        W (P and Q) (P' and Q') f g"
  apply (clarsimp simp: equiv_valid_2_def)
  apply (rule conjI)
   apply blast
  apply (drule_tac s=s in modifies_at_mostD, assumption+)
  apply (drule_tac s=t in modifies_at_mostD, assumption+)
  apply (frule (1) equiv_but_for_reads_equiv[OF domains_distinct])
  apply (frule_tac s=t in equiv_but_for_reads_equiv[OF domains_distinct], assumption)
  apply (drule (1) equiv_but_for_affects_equiv[OF domains_distinct])
  apply (drule_tac s=t in equiv_but_for_affects_equiv[OF domains_distinct], assumption)
  apply (blast intro: reads_equiv_trans reads_equiv_sym affects_equiv_trans affects_equiv_sym)
  done

lemma ev_invisible:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
    "\<lbrakk> labels_are_invisible aag l L; modifies_at_most aag L Q f;
       \<forall>s t. P s \<and> P t \<longrightarrow> (\<forall>(rva, s') \<in> fst (f s). \<forall>(rvb, t') \<in> fst(f t). W rva rvb) \<rbrakk>
       \<Longrightarrow> equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
                         W (P and Q) (P and Q) f f"
  by (rule ev2_invisible[OF domains_distinct]; simp)

lemma modify_det:
  "det (modify f)"
  by (clarsimp simp: det_def modify_def get_def put_def bind_def)

lemma dummy_kheap_update:
  "st = st\<lparr>kheap := kheap st\<rparr>"
  by simp

lemma reads_affects_equiv_kheap_eq:
  "\<lbrakk> reads_equiv aag s s'; affects_equiv aag l s s'; aag_can_affect aag l x \<or> aag_can_read aag x \<rbrakk>
     \<Longrightarrow> kheap s x = kheap s' x"
  by (fastforce elim: affects_equivE reads_equivE equiv_forE)

lemma reads_affects_equiv_get_tcb_eq:
  "\<lbrakk> aag_can_read aag t \<or> aag_can_affect aag l t; reads_equiv aag s s'; affects_equiv aag l s s' \<rbrakk>
     \<Longrightarrow> get_tcb t s = get_tcb t s'"
  by (fastforce simp: get_tcb_def reads_affects_equiv_kheap_eq)

lemma equiv_valid_get_assert:
  "equiv_valid_inv I A P f
   \<Longrightarrow> equiv_valid_inv I A P (get >>= (\<lambda> s. assert (g s) >>= (\<lambda> y. f)))"
  apply (subst equiv_valid_def2)
  apply (rule_tac W="\<top>\<top>" in equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp)
     apply (rule equiv_valid_rv_trivial)
     apply wpsimp+
   apply (rule_tac R'="\<top>\<top>" in equiv_valid_2_bind)
      apply (simp add: equiv_valid_def2)
     apply (rule assert_ev2)
     apply (wp | simp)+
  done

lemma my_bind_rewrite_lemma:
  "(f >>= g) =  (f >>= (\<lambda> r. (g r) >>= (\<lambda> x. return ())))"
  by simp

lemma delete_objects_reads_respects:
  "reads_respects aag l (\<lambda>_. True) (delete_objects p b)"
  apply (simp add: delete_objects_def)
  apply (wp detype_reads_respects dmo_freeMemory_reads_respects)
  done

lemma another_hacky_rewrite:
  "do a; (do x \<leftarrow> f; g x od); h; j od = do a; (f >>= g >>= (\<lambda>_. h)); j od"
  by (simp add: bind_assoc[symmetric])


definition states_equal_except_kheap_asid :: "det_state \<Rightarrow> det_state \<Rightarrow> bool" where
  "states_equal_except_kheap_asid s s' \<equiv>
     equiv_machine_state \<top> (machine_state s) (machine_state s') \<and>
     equiv_for \<top> cdt s s' \<and>
     equiv_for \<top> cdt_list s s' \<and>
     equiv_for \<top> ekheap s s' \<and>
     equiv_for \<top> ready_queues s s' \<and>
     equiv_for \<top> is_original_cap s s' \<and>
     equiv_for \<top> interrupt_states s s' \<and>
     equiv_for \<top> interrupt_irq_node s s' \<and>
     cur_thread s = cur_thread s' \<and>
     cur_domain s = cur_domain s' \<and>
     scheduler_action s = scheduler_action s' \<and>
     work_units_completed s = work_units_completed s' \<and>
     irq_state_of_state s = irq_state_of_state s'"


lemma idle_equiv_arch_state_update[simp]: "idle_equiv st (s\<lparr>arch_state := x\<rparr>) = idle_equiv st s"
  by (simp add: idle_equiv_def)

(* FIXME: This should either be straightforward or moved somewhere else *)
lemma case_junk:
  "(case rv of Inl e \<Rightarrow> True | Inr r \<Rightarrow> P r) \<longrightarrow> (case rv of Inl e \<Rightarrow> True | Inr r \<Rightarrow> R r) =
   (case rv of Inl e \<Rightarrow> True | Inr r \<Rightarrow> P r \<longrightarrow> R r)"
  by (case_tac rv; simp)

(* FIXME: Same here *)
lemma hoare_add_postE:
  "\<lbrakk> \<lbrace>Q\<rbrace> f \<lbrace>P\<rbrace>, - ; \<lbrace>Q\<rbrace> f \<lbrace>\<lambda>rv s. (P rv s) \<longrightarrow> (R rv s)\<rbrace>, - \<rbrakk>
     \<Longrightarrow> \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,-"
  unfolding validE_R_def validE_def
  apply (erule hoare_add_post)
   apply simp
  apply (erule hoare_post_imp[rotated])
  apply (simp add: case_junk)
  done

lemma store_word_offs_globals_equiv:
  "store_word_offs ptr offs v \<lbrace>globals_equiv s\<rbrace>"
  unfolding store_word_offs_def fun_app_def
  apply (wp do_machine_op_globals_equiv)
     apply clarsimp
     apply (erule use_valid[OF _ storeWord_globals_equiv])
     apply (wp | simp | force)+
  done

lemma restrict_eq_asn_none: "f(N := None) = f |` {s. s \<noteq> N}" by auto

crunches cap_swap_for_delete
  for valid_vspace_objs[wp]: valid_vspace_objs
  and valid_global_refs[wp]: valid_global_refs
  (simp: crunch_simps)

lemma thread_set_fault_valid_global_refs[wp]:
  "thread_set (tcb_fault_update A) thread \<lbrace>valid_global_refs\<rbrace>"
  apply (wp thread_set_global_refs_triv thread_set_refs_trivial thread_set_obj_at_impossible | simp)+
  apply (rule ball_tcb_cap_casesI, simp+)
  done

lemma cap_swap_for_delete_valid_arch_caps[wp]:
  "cap_swap_for_delete a b \<lbrace>valid_arch_caps\<rbrace>"
  unfolding cap_swap_for_delete_def
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_weakenE)
  done

(* this to go in InfloFlowBase? *)
lemma get_object_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag \<top>\<top> \<top> (get_object ptr)"
  unfolding get_object_def
  apply (rule equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp)
     apply (rule gets_kheap_revrv')
    apply (simp, simp)
   apply (rule equiv_valid_2_bind)
      apply (rule return_ev2)
      apply (simp)
     apply (rule assert_ev2)
     apply (simp)
    apply (wpsimp)+
  done

lemma get_object_revrv':
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag
   (\<lambda>rv rv'. aag_can_read aag ptr \<longrightarrow> rv = rv')
   \<top> (get_object ptr)"
  unfolding get_object_def
  apply (rule equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp)
     apply (rule gets_kheap_revrv)
    apply (simp, simp)
   apply (rule equiv_valid_2_bind)
      apply (rule return_ev2)
      apply (simp)
     apply (rule assert_ev2)
     apply (simp add: equiv_for_def)
    apply (wpsimp)+
  done

crunch irq_state_of_state[wp]: cancel_badged_sends "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps simp: filterM_mapM)


locale Arch_IF_1 =
  fixes aag :: "'a PAS"
  assumes arch_post_cap_deletion_valid_global_refs:
    "arch_post_cap_deletion acap \<lbrace>\<lambda>s :: det_state. valid_global_refs s\<rbrace>"
  and arch_post_cap_deletion_irq_state_of_state[wp]:
    "arch_post_cap_deletion acap \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  and store_word_offs_irq_state_of_state[wp]:
    "store_word_offs ptr offs v \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  and set_irq_state_irq_state_of_state[wp]:
    "set_irq_state state irq \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  and handle_arch_fault_reply_irq_state_of_state[wp]:
    "handle_arch_fault_reply vmf thread x y \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  and arch_switch_to_idle_thread_irq_state_of_state[wp]:
    "arch_switch_to_idle_thread \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  and arch_switch_to_thread_irq_state_of_state[wp]:
    "arch_switch_to_thread t \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  and arch_invoke_irq_handler_irq_state_of_state[wp]:
    "arch_invoke_irq_handler hi \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  and arch_finalise_cap_irq_state_of_state[wp]:
    "arch_finalise_cap acap b \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  and prepare_thread_delete_irq_state_of_state[wp]:
    "prepare_thread_delete t \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  and equiv_asid_machine_state_update[simp]:
    "\<And>f. equiv_asid asid (machine_state_update f s) s' = equiv_asid asid s s'"
    "\<And>f. equiv_asid asid s (machine_state_update f s') = equiv_asid asid s s'"
  and as_user_set_register_reads_respects':
    "pas_domains_distinct aag \<Longrightarrow> reads_respects aag l \<top> (as_user t (setRegister r v))"
  and store_word_offs_reads_respects:
    "reads_respects aag l \<top> (store_word_offs ptr offs v)"
  and set_endpoint_globals_equiv:
    "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
     set_endpoint ptr ep
     \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  and set_cap_globals_equiv'':
    "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
     set_cap cap p
     \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  and set_thread_state_globals_equiv:
    "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
     set_thread_state ref ts
     \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  and as_user_globals_equiv:
    "\<And>f :: unit user_monad.
     \<lbrace>globals_equiv s and valid_arch_state and (\<lambda>s. tptr \<noteq> idle_thread s)\<rbrace>
     as_user tptr f
     \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
begin

crunch valid_global_refs[wp]: empty_slot "\<lambda>s :: det_state. valid_global_refs s"
  (simp: cap_range_def)

crunches set_extra_badge, set_mrs, reply_from_kernel, invoke_domain
  for irq_state_of_state[wp]: "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma transfer_caps_loop_irq_state[wp]:
  "transfer_caps_loop a b c d e f \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunch irq_state_of_state[wp]: handle_recv, handle_reply "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: crunch_simps)

crunch irq_state_of_state[wp]: invoke_irq_handler "\<lambda>s. P (irq_state_of_state s)"

crunch irq_state_of_state[wp]: schedule "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp modify_wp crunch_wps whenE_wp
   simp: machine_op_lift_def machine_rest_lift_def crunch_simps)

crunch irq_state_of_state[wp]: finalise_cap "\<lambda>s. P (irq_state_of_state s)"
  (wp: select_wp modify_wp crunch_wps dmo_wp simp: crunch_simps)

crunch irq_state_of_state[wp]: send_signal, restart "\<lambda>s. P (irq_state_of_state s)"

lemma mol_states_equiv_for:
  "machine_op_lift mop \<lbrace>\<lambda>ms. states_equiv_for P Q R S st (s\<lparr>machine_state := ms\<rparr>)\<rbrace>"
  unfolding machine_op_lift_def
  apply (simp add: machine_rest_lift_def split_def)
  apply (wp modify_wp)
  apply (clarsimp simp: states_equiv_for_def equiv_asids_def)
  apply (fastforce elim!: equiv_forE intro!: equiv_forI)
  done

lemma do_machine_op_mol_states_equiv_for:
  "do_machine_op (machine_op_lift f) \<lbrace>states_equiv_for P Q R S st\<rbrace>"
  apply (simp add: do_machine_op_def)
  apply (wp modify_wp | simp add: split_def)+
  apply (clarify)
  apply (erule use_valid)
   apply simp
   apply (rule mol_states_equiv_for)
  by simp

lemma set_message_info_reads_respects:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows "reads_respects aag l \<top> (set_message_info thread info)"
  unfolding set_message_info_def fun_app_def
  by (rule as_user_set_register_reads_respects'[OF domains_distinct])

lemma set_mrs_reads_respects:
  "reads_respects aag l (K (aag_can_read aag t \<or> aag_can_affect aag l t)) (set_mrs t buf msgs)"
  apply (simp add: set_mrs_def cong: option.case_cong_weak)
  apply (wp mapM_x_ev' store_word_offs_reads_respects set_object_reads_respects
         | wpc | simp add: split_def split del: if_split add: zipWithM_x_mapM_x)+
  apply (auto intro: reads_affects_equiv_get_tcb_eq)
  done

lemma cap_insert_globals_equiv'':
  "\<lbrace>globals_equiv s and valid_global_objs and valid_arch_state\<rbrace>
   cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding cap_insert_def
  by (wpsimp wp: set_original_globals_equiv update_cdt_globals_equiv
                 set_cap_globals_equiv'' dxo_wp_weak hoare_drop_imps)

lemma set_message_info_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state and (\<lambda>s. thread \<noteq> idle_thread s)\<rbrace>
   set_message_info thread info
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_message_info_def by (wp as_user_globals_equiv)

lemma cancel_badged_sends_globals_equiv:
  "\<lbrace>globals_equiv s and valid_arch_state\<rbrace>
   cancel_badged_sends epptr badge
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace> "
  unfolding cancel_badged_sends_def
  by (wpsimp wp: set_endpoint_globals_equiv set_thread_state_globals_equiv
                 filterM_preserved dxo_wp_weak hoare_drop_imps)

end

end
