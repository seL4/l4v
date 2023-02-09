(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CNode_IF
imports ArchFinalCaps
begin

lemma cap_fault_on_failure_rev:
  "reads_equiv_valid_inv A aag P m
   \<Longrightarrow> reads_equiv_valid_inv A aag P (cap_fault_on_failure cptr rp m)"
  unfolding cap_fault_on_failure_def handleE'_def
  by (wp | wpc | simp add: o_def)+

lemma cap_fault_on_failure_rev_g:
  "reads_respects_g aag l P m \<Longrightarrow> reads_respects_g aag l P (cap_fault_on_failure cptr rp m)"
  unfolding cap_fault_on_failure_def handleE'_def
  by (wp | wpc | simp add: o_def)+

definition gets_apply where
  "gets_apply f x \<equiv>
     do s \<leftarrow> get;
        return ((f s) x)
     od"

lemma gets_apply_ev:
  "equiv_valid I A A (K (\<forall>s t. I s t \<and> A s t \<longrightarrow> (f s) x = (f t) x)) (gets_apply f x)"
  apply (simp add: gets_apply_def get_def bind_def return_def)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  done

lemma gets_apply:
  "gets f >>= (\<lambda>f. g (f x)) = gets_apply f x >>= g"
  by (simp add: gets_apply_def gets_def)

lemma get_object_rev:
  "reads_equiv_valid_inv A aag (\<lambda>s. aag_can_read aag oref) (get_object oref)"
  apply (unfold get_object_def fun_app_def)
  apply (subst gets_apply)
  apply (wp gets_apply_ev | wp (once) hoare_drop_imps)+
  apply (fastforce elim: reads_equivE equiv_forE)
  done

lemma get_cap_rev:
  "reads_equiv_valid_inv A aag (K (aag_can_read aag (fst slot))) (get_cap slot)"
  unfolding get_cap_def
  by (wp get_object_rev | wpc | simp add: split_def)+

declare if_weak_cong[cong]

lemma resolve_address_bits_spec_rev:
  "reads_spec_equiv_valid_inv s A aag
     (pas_refined aag and K (is_cnode_cap (fst ref) \<longrightarrow> is_subject aag (obj_ref_of (fst ref))))
     (resolve_address_bits ref)"
proof(unfold resolve_address_bits_def, induct ref arbitrary: s rule: resolve_address_bits'.induct)
  case (1 z cap' cref' s') show ?case
    apply (subst resolve_address_bits'.simps)
    apply (cases cap')
               apply (simp_all add: drop_spec_ev throwError_ev_pre
                              cong: if_cong
                         split del: if_split)
    apply (wp "1.hyps")
                   apply (assumption | simp add: in_monad | rule conjI)+
           apply (wp get_cap_rev get_cap_wp whenE_throwError_wp)+
    apply (auto simp: cte_wp_at_caps_of_state is_cap_simps cap_auth_conferred_def
                dest: caps_of_state_pasObjectAbs_eq)
    done
qed

lemma resolve_address_bits_rev:
  "reads_equiv_valid_inv A aag
     (pas_refined aag and K (is_cnode_cap (fst ref) \<longrightarrow> is_subject aag (obj_ref_of (fst ref))))
     (resolve_address_bits ref)"
  by (rule use_spec_ev[OF resolve_address_bits_spec_rev])

lemma lookup_slot_for_thread_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and K (is_subject aag thread))
                         (lookup_slot_for_thread thread cptr)"
  unfolding lookup_slot_for_thread_def fun_app_def
  apply (rule gen_asm_ev)
  apply (wp resolve_address_bits_rev gets_the_ev | simp)+
  apply (rule conjI)
   apply blast
  apply (clarsimp simp: tcb.splits)
  apply (erule (2) owns_thread_owns_cspace)
   defer
   apply (case_tac tcb_ctablea, simp_all)
  done

lemma lookup_cap_and_slot_rev[wp]:
  "reads_equiv_valid_inv A aag (pas_refined aag and K (is_subject aag thread))
                         (lookup_cap_and_slot thread cptr)"
  unfolding lookup_cap_and_slot_def
  by (wp lookup_slot_for_thread_rev lookup_slot_for_thread_authorised get_cap_rev
      | simp add: split_def
      | strengthen aag_can_read_self)+

lemmas lookup_cap_and_slot_reads_respects_g =
  reads_respects_g_from_inv[OF lookup_cap_and_slot_rev lookup_cap_and_slot_inv]

lemma set_cap_reads_respects:
  "reads_respects aag l (K (aag_can_read aag (fst slot))) (set_cap cap slot)"
  by (wpsimp wp: set_object_reads_respects get_object_rev hoare_vcg_all_lift
           simp: set_cap_def split_def)

lemma set_original_reads_respects:
  "reads_respects aag l \<top> (set_original slot v)"
  unfolding set_original_def
  apply (unfold equiv_valid_def2)
  apply (rule_tac Q="\<top>\<top>" in equiv_valid_rv_bind)
    apply (rule gets_is_original_cap_revrv)
   apply (rule modify_ev2)
   apply (clarsimp simp: equiv_for_or or_comp_dist)
   apply (safe)
    apply (erule reads_equiv_is_original_cap_update)
    apply (erule equiv_for_id_update)
   apply (erule affects_equiv_is_original_cap_update)
   apply (erule equiv_for_id_update)
  apply wp
  done

lemma set_cdt_reads_respects:
  "reads_respects aag l \<top> (set_cdt c)"
  unfolding set_cdt_def
  apply (unfold equiv_valid_def2)
  apply (rule get_bind_ev2)
  apply (unfold fun_app_def, rule put_ev2)
  apply (fastforce intro: reads_equiv_cdt_update affects_equiv_cdt_update equiv_for_refl)
  done

lemma set_cdt_ev2:
  "equiv_for (((aag_can_read aag) or (aag_can_affect aag l)) \<circ> fst) id c c'
   \<Longrightarrow> equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
                     (=) \<top> \<top> (set_cdt c) (set_cdt c')"
  unfolding set_cdt_def
  apply (rule get_bind_ev2)
  apply (unfold fun_app_def, rule put_ev2)
  apply (fastforce simp: equiv_for_or or_comp_dist reads_equiv_cdt_update affects_equiv_cdt_update)
  done

lemma set_cdt_list_ev2:
  "equiv_for (((aag_can_read aag) or (aag_can_affect aag l)) \<circ> fst) id c c'
   \<Longrightarrow> equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l)
                     (=) \<top> \<top> (set_cdt_list c) (set_cdt_list c')"
  unfolding set_cdt_list_def
  apply (rule get_bind_ev2)
  apply (unfold fun_app_def, rule put_ev2)
  apply (fastforce simp: equiv_for_or or_comp_dist reads_equiv_cdt_list_update affects_equiv_cdt_list_update)
  done

lemma kheap_get_tcb_eq: "kheap s ref = kheap t ref \<Longrightarrow> get_tcb ref s = get_tcb ref t"
  by (simp add: get_tcb_def)

lemma thread_get_rev:
  "reads_equiv_valid_inv A aag (K (aag_can_read aag thread)) (thread_get f thread)"
  unfolding thread_get_def fun_app_def
  by (wp gets_the_ev) (fastforce intro: kheap_get_tcb_eq elim: reads_equivE equiv_forD)

lemma update_cdt_reads_respects:
  "reads_respects aag l (K (\<forall>rv rv'.
      equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id rv rv' \<longrightarrow>
      equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) f rv rv'))
     (update_cdt f)"
  unfolding update_cdt_def
  apply (rule gen_asm_ev)
  apply (unfold equiv_valid_def2)
  apply (rule equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp[OF gets_cdt_revrv])
    apply (rule TrueI)
   apply (rule set_cdt_ev2)
   apply (simp add: equiv_for_comp[symmetric])
  apply wp
  done

lemma update_cdt_list_reads_respects:
  "reads_respects aag l (K  (\<forall>rv rv'.
      equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id rv rv' \<longrightarrow>
      equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) f rv rv'))
     (update_cdt_list f)"
  unfolding update_cdt_list_def
  apply (rule gen_asm_ev)
  apply (unfold equiv_valid_def2)
  apply (rule equiv_valid_rv_bind)
    apply (rule equiv_valid_rv_guard_imp[OF gets_cdt_list_revrv])
    apply (rule TrueI)
   apply (rule set_cdt_list_ev2)
   apply (simp add: equiv_for_comp[symmetric])
  apply wp
  done

lemma gen_asm_ev2':
  assumes "Q \<Longrightarrow> Q' \<Longrightarrow> equiv_valid_2 I A B R P P' f f'"
  shows "equiv_valid_2 I A B R (P and K Q) (P' and K Q') f f'"
  using assms by (fastforce simp: equiv_valid_def2 equiv_valid_2_def)

lemmas gen_asm_ev2 = gen_asm_ev2'[where P=\<top> and P'=\<top>, simplified]

lemma set_untyped_cap_as_full_reads_respects:
  "reads_respects aag l (K (aag_can_read aag (fst src_slot)))
     (set_untyped_cap_as_full src_cap new_cap src_slot)"
  unfolding set_untyped_cap_as_full_def
  apply (wp set_cap_reads_respects)
  apply auto
  done

lemma gets_apply_wp[wp]:
  "\<lbrace>\<lambda>s. P (f s x) s\<rbrace> gets_apply f x \<lbrace>P\<rbrace>"
  by (wpsimp simp: gets_apply_def)

lemma cap_insert_reads_respects:
  notes split_paired_All[simp del]
  shows
  "reads_respects aag l (K (aag_can_read aag (fst src_slot) \<and> aag_can_read aag (fst dest_slot)))
                  (cap_insert new_cap src_slot dest_slot)"
  unfolding cap_insert_def
  apply (rule gen_asm_ev)
  apply (subst gets_apply)
  apply (simp only: cap_insert_ext_extended.dxo_eq)
  apply (simp only: cap_insert_ext_def)
  apply (wp set_original_reads_respects update_cdt_reads_respects set_cap_reads_respects
            gets_apply_ev update_cdt_list_reads_respects set_untyped_cap_as_full_reads_respects
            get_cap_wp get_cap_rev
         | simp split del: if_split
         | clarsimp simp: equiv_for_def split: option.splits)+
  by (fastforce simp: reads_equiv_def2 equiv_for_def
                elim: states_equiv_forE_is_original_cap states_equiv_forE_cdt
                dest: aag_can_read_self
               split: option.splits)

lemma cap_move_reads_respects:
  notes split_paired_All[simp del]
  shows
  "reads_respects aag l (K (is_subject aag (fst src_slot) \<and> is_subject aag (fst dest_slot)))
                  (cap_move new_cap src_slot dest_slot)"
  unfolding cap_move_def
  apply (subst gets_apply)
  apply (simp add: bind_assoc[symmetric])
  apply (fold update_cdt_def)
  apply (simp add: bind_assoc cap_move_ext_def)
  apply (rule gen_asm_ev)
  apply (elim conjE)
  apply (wp set_original_reads_respects gets_apply_ev update_cdt_reads_respects
            set_cap_reads_respects update_cdt_list_reads_respects
         | simp split del: if_split | fastforce simp: equiv_for_def split: option.splits)+
  apply (intro impI conjI allI)
  apply (fastforce simp: reads_equiv_def2 equiv_for_def
                   elim: states_equiv_forE_is_original_cap states_equiv_forE_cdt
                   dest: aag_can_read_self
                  split: option.splits)+
  done

lemma get_idemp:
  "do s1 \<leftarrow> get; s2 \<leftarrow> get; f s1 s2 od =
   do s1 \<leftarrow> get; f s1 s1 od"
  by (simp add: get_def bind_def)

lemma gets_apply2:
  "gets f >>= (\<lambda> f. g (f x) (f y)) =
   gets_apply f x >>= (\<lambda> x. gets_apply f y >>= (\<lambda> y. g x y))"
  by (simp add: gets_def gets_apply_def get_idemp)

lemma cap_swap_reads_respects:
  notes split_paired_All[simp del]
  shows "reads_respects aag l (K (is_subject aag (fst slot1) \<and> is_subject aag (fst slot2)))
                        (cap_swap cap1 slot1 cap2 slot2)"
  unfolding cap_swap_def
  apply (subst gets_apply2)
  apply (simp add: bind_assoc[symmetric])
  apply (fold update_cdt_def)
  apply (simp add: bind_assoc cap_swap_ext_def)
  apply (rule gen_asm_ev)
  apply (wp set_original_reads_respects update_cdt_reads_respects gets_apply_ev
            set_cap_reads_respects update_cdt_list_reads_respects
         | simp split del: if_split | fastforce simp: equiv_for_def split: option.splits)+
  apply (intro impI conjI allI)
      apply ((fastforce simp: reads_equiv_def2 equiv_for_def
                        elim: states_equiv_forE_is_original_cap states_equiv_forE_cdt
                        dest: aag_can_read_self
                       split: option.splits)+)[2]
    apply (frule_tac x = slot1 in equiv_forD, elim conjE,drule aag_can_read_self,simp)
    apply (frule_tac x = slot2 in equiv_forD, elim conjE)
     apply (drule aag_can_read_self)+
     apply clarsimp
    apply clarsimp
    apply (erule equiv_forE)
    apply (fastforce intro: equiv_forI)
   apply (fastforce simp: equiv_for_def dest: aag_can_read_self
                    elim: reads_equivE equiv_forE[where f="is_original_cap"] split: option.splits)+
  done

lemma tcb_at_def2: "tcb_at ptr s = (\<exists>tcb. kheap s ptr = Some (TCB tcb))"
  by (clarsimp simp: tcb_at_def get_tcb_def split: kernel_object.splits option.splits)

lemma set_cdt_globals_equiv:
  "set_cdt c \<lbrace>globals_equiv s\<rbrace>"
  unfolding set_cdt_def
  by (wpsimp simp: globals_equiv_def idle_equiv_def)

lemma update_cdt_globals_equiv:
  "update_cdt f \<lbrace>globals_equiv s\<rbrace>"
  unfolding update_cdt_def
  by (wp set_cdt_globals_equiv)

declare set_original_wp[wp del]

lemma set_original_globals_equiv:
  "set_original slot v \<lbrace>globals_equiv s\<rbrace>"
  unfolding set_original_def
  by (wpsimp simp: globals_equiv_def idle_equiv_def)

lemma globals_equiv_exst_update[simp]:
  "globals_equiv st (trans_state f s) =
   globals_equiv st s"
  by (simp add: globals_equiv_def idle_equiv_def)

lemma (in is_extended') globals_equiv: "I (globals_equiv st)" by (rule lift_inv,simp)

lemma domain_sep_inv_refl:
  "domain_sep_inv irqs st s \<Longrightarrow> domain_sep_inv irqs s s"
  by (fastforce simp: domain_sep_inv_def)


locale CNode_IF_1 =
  fixes state_ext_t :: "'s :: state_ext itself"
  and irq_at :: "nat \<Rightarrow> (irq \<Rightarrow> bool) \<Rightarrow> irq option"
  assumes set_cap_globals_equiv:
    "\<lbrace>globals_equiv s and valid_global_objs and valid_arch_state\<rbrace>
     set_cap cap p
     \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  and dmo_getActiveIRQ_wp:
    "\<lbrace>\<lambda>s. P (irq_at (irq_state (machine_state s) + 1) (irq_masks (machine_state s)))
            (s\<lparr>machine_state := machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>\<rparr>)\<rbrace>
     do_machine_op (getActiveIRQ in_kernel)
     \<lbrace>\<lambda>rv s :: 's state. P rv s\<rbrace>"
  and arch_globals_equiv_irq_state_update[simp]:
    "arch_globals_equiv ct it kh kh' as as' ms (irq_state_update f ms') =
     arch_globals_equiv ct it kh kh' as as' ms ms'"
    "arch_globals_equiv ct it kh kh' as as' (irq_state_update f ms) ms' =
     arch_globals_equiv ct it kh kh' as as' ms ms'"
begin

crunch globals_equiv[wp]: set_untyped_cap_as_full "globals_equiv st"

lemma cap_insert_globals_equiv:
  "\<lbrace>globals_equiv s and valid_global_objs and valid_arch_state\<rbrace>
   cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding cap_insert_def fun_app_def
  by (wpsimp wp: update_cdt_globals_equiv set_original_globals_equiv
                 set_cap_globals_equiv hoare_drop_imps dxo_wp_weak)

lemma cap_move_globals_equiv:
  "\<lbrace>globals_equiv s and valid_global_objs and valid_arch_state\<rbrace>
   cap_move new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding cap_move_def fun_app_def
  by (wpsimp wp: set_original_globals_equiv set_cdt_globals_equiv set_cap_globals_equiv dxo_wp_weak)

lemma cap_swap_globals_equiv:
  "\<lbrace>globals_equiv s and valid_global_objs and valid_arch_state\<rbrace>
   cap_swap cap1 slot1 cap2 slot2
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding cap_swap_def
  by (wpsimp wp: set_original_globals_equiv set_cdt_globals_equiv set_cap_globals_equiv dxo_wp_weak)

definition is_irq_at :: "('z::state_ext) state \<Rightarrow> irq \<Rightarrow> nat \<Rightarrow> bool" where
  "is_irq_at s \<equiv> \<lambda>irq pos. irq_at pos (irq_masks (machine_state s)) = Some irq"

text \<open>
  We require that interrupts recur in order to ensure that no individual
  big step ever diverges.
\<close>
definition irq_is_recurring :: "irq \<Rightarrow> ('z::state_ext) state \<Rightarrow> bool" where
  "irq_is_recurring irq s \<equiv> \<forall>n. (\<exists>m. is_irq_at s irq (n+m))"

text \<open>
  There is only one interrupt turned on, namely @{term irq}, and it is
  a timer interrupt.
\<close>
definition only_timer_irq :: "irq \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "only_timer_irq irq s \<equiv> (\<forall>x. interrupt_states s x = IRQTimer \<longrightarrow> x = irq) \<and> irq_is_recurring irq s"

end


locale CNode_IF_2 = CNode_IF_1 state_ext_t
  for state_ext_t :: "'s :: state_ext itself"
  and f :: "('s state, 'a) nondet_monad" +
  assumes is_irq_at_triv:
    "(\<And>P. \<lbrace>(\<lambda>s. P (irq_masks (machine_state s))) and Q\<rbrace>
           f
           \<lbrace>\<lambda>rv s. P (irq_masks (machine_state s))\<rbrace>)
     \<Longrightarrow> \<lbrace>(\<lambda>s. P (is_irq_at s)) and Q\<rbrace>
         f
         \<lbrace>\<lambda>rv s. P (is_irq_at s)\<rbrace>"
  and is_irq_at_not_masked:
    "is_irq_at (s :: det_state) irq pos \<Longrightarrow> \<not> irq_masks (machine_state s) irq"
begin

lemma irq_is_recurring_triv:
  assumes a: "\<And>P. \<lbrace>(\<lambda>s. P (irq_masks (machine_state s))) and Q\<rbrace>
                   (f :: ('s state, 'a) nondet_monad)
                   \<lbrace>\<lambda>rv s. P (irq_masks (machine_state s))\<rbrace>"
  shows "\<lbrace>irq_is_recurring irq and Q\<rbrace> f \<lbrace>\<lambda>_. irq_is_recurring irq\<rbrace>"
  apply (clarsimp simp: irq_is_recurring_def valid_def)
  apply (rule use_valid[OF _ is_irq_at_triv[OF a]])
   apply assumption
  apply simp
  done

lemma domain_sep_inv_to_interrupt_states_pres:
  assumes a: "\<And>st. \<lbrace>domain_sep_inv False (st :: 's state) and P\<rbrace> f \<lbrace>\<lambda>_. domain_sep_inv False st\<rbrace>"
  shows "\<lbrace>(\<lambda>s. Q (interrupt_states s)) and P and domain_sep_inv False st\<rbrace>
         f
         \<lbrace>\<lambda>_ s. Q (interrupt_states s)\<rbrace>"
  apply (clarsimp simp: valid_def)
   apply (erule use_valid)
   apply (rule hoare_strengthen_post)
    apply (rule_tac st3=s in a)
   apply (fastforce simp: domain_sep_inv_def)
  apply (simp add: domain_sep_inv_refl)
  done

lemma only_timer_irq_pres:
  assumes a: "\<And>P. \<lbrace>(\<lambda>s. P (irq_masks (machine_state s))) and Q\<rbrace>
                   f
                   \<lbrace>\<lambda>rv s. P (irq_masks (machine_state s))\<rbrace>"
  assumes b:
    "\<And>st :: 's state. \<lbrace>domain_sep_inv False st and P\<rbrace> f \<lbrace>\<lambda>_. domain_sep_inv False st\<rbrace>"
  shows
    "\<lbrace>only_timer_irq irq and Q and P and (\<lambda>s. domain_sep_inv False (st :: 's state) s)\<rbrace>
     f
     \<lbrace>\<lambda>_. only_timer_irq irq\<rbrace>"
  apply (clarsimp simp: only_timer_irq_def valid_def)
  apply (rule conjI)
   apply (clarsimp)
   apply (drule spec)
   apply (erule mp)
   apply (erule contrapos_pp, erule use_valid, rule domain_sep_inv_to_interrupt_states_pres, rule b, fastforce)
  apply (erule use_valid[OF _ irq_is_recurring_triv[OF a]])
  by simp

definition only_timer_irq_inv :: "irq \<Rightarrow> 'z :: state_ext state \<Rightarrow> 'z state \<Rightarrow> bool" where
  "only_timer_irq_inv irq st \<equiv> domain_sep_inv False st and only_timer_irq irq"

lemma only_timer_irq_inv_pres:
  assumes a:
    "\<And>P. \<lbrace>(\<lambda>s. P (irq_masks (machine_state s))) and Q\<rbrace>
          f
          \<lbrace>\<lambda>rv s. P (irq_masks (machine_state s))\<rbrace>"
  assumes b: "\<And>st :: 's state. \<lbrace>domain_sep_inv False st and P\<rbrace> f \<lbrace>\<lambda>_. domain_sep_inv False st\<rbrace>"
  shows "\<lbrace>only_timer_irq_inv irq (st :: 's state) and Q and P\<rbrace> f \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply (clarsimp simp: only_timer_irq_inv_def valid_def)
  apply (rule conjI)
   apply (erule use_valid[OF _ b], simp)
  apply (erule use_valid[OF _ only_timer_irq_pres[OF a b]])
  apply simp
  done

lemma only_timer_irq_inv_domain_sep_inv[intro]:
  "only_timer_irq_inv irq st s \<Longrightarrow> domain_sep_inv False st s"
  by (simp add: only_timer_irq_inv_def)

lemma irq_is_recurring_not_masked:
  "irq_is_recurring irq (s :: det_state) \<Longrightarrow> \<not> irq_masks (machine_state s) irq"
  apply (clarsimp simp: irq_is_recurring_def)
  apply (blast dest: is_irq_at_not_masked)
  done

lemma only_timer_irq_inv_determines_irq_masks:
  "\<lbrakk>invs (s :: det_state); only_timer_irq_inv irq st s\<rbrakk> \<Longrightarrow>
   \<not> irq_masks (machine_state s) irq \<and>
   (\<forall>x. x \<noteq> irq \<longrightarrow> irq_masks (machine_state s) x)"
  apply (rule conjI)
   apply (clarsimp simp: only_timer_irq_inv_def only_timer_irq_def)
   apply (blast dest: irq_is_recurring_not_masked)
  apply (clarsimp simp: only_timer_irq_inv_def domain_sep_inv_def only_timer_irq_def)
  apply (case_tac "interrupt_states s x")
    apply (fastforce simp: invs_def valid_state_def valid_irq_states_def valid_irq_masks_def)
   apply fastforce+
  done

lemma dmo_getActiveIRQ_globals_equiv:
  "\<lbrace>globals_equiv st\<rbrace> do_machine_op (getActiveIRQ in_kernel) \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (wp dmo_getActiveIRQ_wp)
  apply (auto simp: globals_equiv_def idle_equiv_def)
  done

crunches reset_work_units, work_units_limit_reached, update_work_units
  for only_timer_irq_inv[wp]: "only_timer_irq_inv irq st"
  (simp: only_timer_irq_inv_def only_timer_irq_def irq_is_recurring_def is_irq_at_def)

end


lemma gets_irq_masks_equiv_valid:
  "equiv_valid_inv I A (\<lambda>s. \<not> (irq_masks s) irq \<and> (\<forall>x. x \<noteq> irq \<longrightarrow> (irq_masks s) x)) (gets irq_masks)"
  by (fastforce simp: equiv_valid_def2 equiv_valid_2_def in_monad)

lemma irq_state_increment_reads_respects_memory:
  "equiv_valid_inv (equiv_machine_state P and equiv_irq_state)
                   (equiv_for (\<lambda>x. aag_can_affect_label aag l \<and>
                                   pasObjectAbs aag x \<in> subjectReads (pasPolicy aag) l)
                              underlying_memory)
                   \<top> (modify (\<lambda>s. s\<lparr>irq_state := Suc (irq_state s)\<rparr>))"
  apply (simp add: equiv_valid_def2)
  apply (rule modify_ev2)
  apply (fastforce intro: equiv_forI elim: equiv_forE)
  done

lemma irq_state_increment_reads_respects_device:
  "equiv_valid_inv (equiv_machine_state P and equiv_irq_state)
                   (equiv_for (\<lambda>x. aag_can_affect_label aag l \<and>
                                   pasObjectAbs aag x \<in> subjectReads (pasPolicy aag) l)
                              device_state)
                   \<top> (modify (\<lambda>s. s\<lparr>irq_state := Suc (irq_state s)\<rparr>))"
  apply (simp add: equiv_valid_def2)
  apply (rule modify_ev2)
  apply (fastforce intro: equiv_forI elim: equiv_forE)
  done

lemma use_equiv_valid_inv:
  "\<lbrakk> x \<in> fst (f st); y \<in> fst (f s); g s; g st; I s st; P s st; equiv_valid_inv I P g f \<rbrakk>
     \<Longrightarrow> fst x = fst y \<and> P (snd y) (snd x) \<and> I (snd y) (snd x)"
  apply (clarsimp simp add: equiv_valid_def spec_equiv_valid_def equiv_valid_2_def)
  apply (drule spec)+
  apply (erule impE)
   apply fastforce
  apply (drule(1) bspec | clarsimp)+
  done

lemma equiv_valid_inv_conj_lift:
  assumes P: "equiv_valid_inv I (\<lambda>s s'. P s s') g f"
      and P': "equiv_valid_inv I (\<lambda>s s'. P' s s') g f"
  shows "equiv_valid_inv I (\<lambda>s s'. P s s' \<and> P' s s') g f"
  apply (clarsimp simp add: equiv_valid_def spec_equiv_valid_def equiv_valid_2_def)
  apply (frule_tac st = t and s = st in use_equiv_valid_inv[OF _ _ _ _ _ _ P])
       apply fastforce+
  apply (frule_tac st = t and s = st in use_equiv_valid_inv[OF _ _ _ _ _ _ P'])
       apply fastforce+
  done

lemma reset_work_units_reads_respects[wp]:
  "reads_respects aag l \<top> reset_work_units"
  apply (simp add: reset_work_units_def equiv_valid_def2)
  apply (rule modify_ev2)
  apply (force intro: reads_equiv_work_units_completed_update affects_equiv_work_units_completed_update)
  done

lemma update_work_units_reads_respects[wp]:
  "reads_respects aag l \<top> update_work_units"
  apply (simp add: update_work_units_def equiv_valid_def2)
  apply (rule modify_ev2)
  apply (force intro: reads_equiv_work_units_completed_update' affects_equiv_work_units_completed_update')
  done

lemma work_units_limit_reached_reads_respects[wp]:
  "reads_respects aag l \<top> work_units_limit_reached"
  apply (simp add: work_units_limit_reached_def, wp)
  apply force
  done

crunch invs[wp]: work_units_limit_reached invs

lemma preemption_point_def2:
  "(preemption_point :: (unit,det_ext) p_monad) =
   doE liftE update_work_units;
       rv \<leftarrow> liftE work_units_limit_reached;
       if rv then doE liftE reset_work_units;
                      liftE (do_machine_op (getActiveIRQ True)) >>=E
                      case_option (returnOk ()) (K (throwError $ ()))
                  odE
       else returnOk()
   odE"
  apply (rule ext)
  apply (simp add: preemption_point_def OR_choiceE_def wrap_ext_bool_det_ext_ext_def
                   ef_mk_ef work_units_limit_reached_def select_f_def)
  apply (clarsimp simp: work_units_limit_reached_def gets_def liftE_def select_f_def get_def
                        lift_def return_def bind_def bindE_def split_def image_def
                 split: option.splits sum.splits)
  done

lemma all_children_descendants_equal:
  "\<lbrakk> equiv_for P id s t; all_children P s; all_children P t; P slot \<rbrakk>
     \<Longrightarrow> descendants_of slot s = descendants_of slot t"
  apply (clarsimp | rule equalityI)+
   apply (frule_tac p="(a, b)" and q="slot" and m=s in all_children_descendants_of)
     apply (simp)+
   apply (simp add: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)
   apply (rule_tac r'="{(p, c). s c = Some p}" and Q="P" in trancl_subset_equivalence)
     apply (clarsimp)+
    apply (frule_tac p="(aa, ba)" and q="slot" in all_children_descendants_of)
      apply (fastforce simp: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)+
   apply (fastforce simp: equiv_for_def)
  apply (clarsimp)
  apply (frule_tac p="(a, b)" and q="slot" and m=t in all_children_descendants_of)
    apply (simp)+
  apply (simp add: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)
  apply (rule_tac r'="{(p, c). t c = Some p}" and Q="P" in trancl_subset_equivalence)
    apply (clarsimp)+
   apply (frule_tac p="(aa, ba)" and q="slot" and m=t in all_children_descendants_of)
     apply (fastforce simp: equiv_for_def descendants_of_def cdt_parent_rel_def is_cdt_parent_def)+
  done

lemma cca_can_read:
  "\<lbrakk> valid_mdb s; valid_objs s; cdt_change_allowed' aag slot s; pas_refined aag s \<rbrakk>
     \<Longrightarrow> aag_can_read aag (fst slot)"
  apply (frule(3) cdt_change_allowed_delete_derived)
  by (rule read_delder_thread_read_thread_rev[OF reads_lrefl])

lemma all_children_subjectReads:
  "pas_refined aag s \<Longrightarrow> all_children (aag_can_read aag \<circ> fst) (cdt s)"
  apply (rule all_childrenI)
  apply simp
  apply (erule read_delder_thread_read_thread_rev)
  by (rule aag_cdt_link_DeleteDerived)

lemma descendants_of_eq:
  "\<lbrakk> reads_equiv aag s t; affects_equiv aag l s t;
     pas_refined aag s; pas_refined aag t; is_subject aag (fst slot) \<rbrakk>
   \<Longrightarrow> descendants_of slot (cdt s) = descendants_of slot (cdt t)"
  apply (rule all_children_descendants_equal[OF _ all_children_subjectReads all_children_subjectReads])
     apply (elim reads_equivE)
     apply (solves\<open>simp add: equiv_for_apply\<close>)
  by force+

lemma gets_descendants_of_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag (=)
                            (pas_refined aag and K (is_subject aag (fst slot)))
                            (gets (descendants_of slot \<circ> cdt))"
  apply (rule gets_evrv'')
  apply clarsimp
  by (rule descendants_of_eq)

lemma silc_dom_equiv_trans[elim]:
  "\<lbrakk> silc_dom_equiv aag s t; silc_dom_equiv aag t u \<rbrakk>
     \<Longrightarrow> silc_dom_equiv aag s u"
  by (auto simp: silc_dom_equiv_def elim: equiv_for_trans)

lemma silc_dom_equiv_sym[elim]:
  "silc_dom_equiv aag s t \<Longrightarrow> silc_dom_equiv aag t s"
  by (auto simp: silc_dom_equiv_def elim: equiv_for_sym)

lemma reads_respects_f:
  "\<lbrakk> reads_respects aag l P f; \<lbrace>silc_inv aag st and Q\<rbrace> f \<lbrace>\<lambda>_. silc_inv aag st\<rbrace> \<rbrakk>
     \<Longrightarrow> reads_respects_f aag l (silc_inv aag st and P and Q) f"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def reads_equiv_f_def)
  apply (rule conjI, fastforce)
  apply (rule conjI, fastforce)
  apply (subst conj_commute, rule conjI, fastforce)
  apply (rule silc_dom_equiv_trans)
   apply (rule silc_dom_equiv_sym)
   apply (rule silc_inv_silc_dom_equiv)
   apply (erule (1) use_valid, simp)
  apply (rule silc_inv_silc_dom_equiv)
  apply (erule (1) use_valid, simp)
  done


locale CNode_IF_3 = CNode_IF_2 +
  fixes aag :: "'a subject_label PAS"
  assumes dmo_getActiveIRQ_reads_respects:
    "reads_respects aag l (invs and only_timer_irq_inv irq st) (do_machine_op (getActiveIRQ in_kernel))"
begin

lemma dmo_getActiveIRQ_reads_respects_g :
  "reads_respects_g aag l (invs and only_timer_irq_inv irq st) (do_machine_op (getActiveIRQ in_kernel))"
  apply (rule equiv_valid_guard_imp[OF reads_respects_g])
    apply (rule dmo_getActiveIRQ_reads_respects)
   apply (rule doesnt_touch_globalsI)
   apply (wp dmo_getActiveIRQ_globals_equiv | blast)+
  done

lemma preemption_point_reads_respects:
  "reads_respects aag l (invs and only_timer_irq_inv irq st) preemption_point"
  apply (simp add: preemption_point_def2)
  apply (wp | wpc | simp add: comp_def)+
           apply ((wp dmo_getActiveIRQ_reads_respects hoare_TrueI | simp
                   | wp (once) hoare_drop_imps)+)[8]
   apply wp
  apply force
  done

lemma preemption_point_reads_respects_f:
  "reads_respects_f aag l (invs and only_timer_irq_inv irq st' and silc_inv aag st) preemption_point"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_f)
    apply (rule preemption_point_reads_respects)
   apply (wp, force+)
  done

end


abbreviation
  reads_spec_equiv_valid_f ::
    "det_state \<Rightarrow> (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow> (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow>
    'a subject_label PAS \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state, 'b) nondet_monad \<Rightarrow> bool" where
  "reads_spec_equiv_valid_f s A B aag P f \<equiv> spec_equiv_valid s (reads_equiv_f aag) A B P f"

abbreviation reads_spec_equiv_valid_f_inv
where
  "reads_spec_equiv_valid_f_inv s A aag P f \<equiv> reads_spec_equiv_valid_f s A A aag P f"

abbreviation
  spec_reads_respects_f :: "det_state \<Rightarrow> 'a subject_label PAS \<Rightarrow> 'a subject_label \<Rightarrow>
                            (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool" where
  "spec_reads_respects_f s aag l P f \<equiv> reads_spec_equiv_valid_f_inv s (affects_equiv aag l) aag P f"

definition reads_equiv_f_g where
  "reads_equiv_f_g aag s s' \<equiv> reads_equiv aag s s' \<and> globals_equiv s s' \<and> silc_dom_equiv aag s s'"

abbreviation reads_respects_f_g :: "'a subject_label PAS \<Rightarrow> 'a subject_label \<Rightarrow>
                                    (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool" where
"reads_respects_f_g aag l P f \<equiv>
   equiv_valid_inv (reads_equiv_f_g aag) (affects_equiv aag l) P f"

lemma reads_equiv_f_g_conj:
  "reads_equiv_f_g aag s s' \<equiv> reads_equiv_f aag s s' \<and> reads_equiv_g aag s s'"
  by (simp add: reads_equiv_f_g_def reads_equiv_f_def reads_equiv_g_def conj_comms)

lemma reads_respects_f_g:
  "\<lbrakk> reads_respects_f aag l P f; doesnt_touch_globals Q f \<rbrakk>
     \<Longrightarrow> reads_respects_f_g aag l (P and Q) f"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (subst (asm) reads_equiv_f_g_conj, erule conjE)
  apply (subst reads_equiv_f_g_conj)
  apply (drule reads_equiv_gD)
  apply clarsimp
  apply (subgoal_tac "reads_equiv_g aag b ba", blast)
  apply (subgoal_tac "globals_equiv b ba", fastforce intro: reads_equiv_gI simp: reads_equiv_f_def)
  apply (rule globals_equiv_trans)
   apply (rule globals_equiv_sym)
   apply (fastforce intro: globals_equivI)
  apply (rule globals_equiv_trans)
   apply (assumption)
  apply (fastforce intro: globals_equivI)
  done

lemma reads_equiv_valid_rv_inv_f:
  assumes a: "reads_equiv_valid_rv_inv A aag R P f"
  assumes b: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "equiv_valid_rv_inv (reads_equiv_f aag) A R P f"
  apply (clarsimp simp: equiv_valid_2_def reads_equiv_f_def)
  apply (insert a, clarsimp simp: equiv_valid_2_def)
  apply (drule_tac x=s in spec, drule_tac x=t in spec, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (drule state_unchanged[OF b])+
  by simp

lemma set_cap_silc_inv':
  "\<lbrace>silc_inv aag st and (\<lambda>s. \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst slot))
                             \<longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps cap s \<and>
                                          pasObjectAbs aag (fst lslot) = SilcLabel))
                    and K (pasObjectAbs aag (fst slot) \<noteq> SilcLabel)\<rbrace>
   set_cap cap slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply (rule hoare_pre)
   apply (rule set_cap_silc_inv)
  by blast

lemma set_cap_reads_respects_f:
  "reads_respects_f aag l
     (silc_inv aag st and (\<lambda>s. \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst slot))
                               \<longrightarrow> (\<exists>lslot. lslot \<in> slots_holding_overlapping_caps cap s \<and>
                                            pasObjectAbs aag (fst lslot) = SilcLabel))
                      and K (is_subject aag (fst slot))) (set_cap cap slot)"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_f[OF set_cap_reads_respects])
   apply (wp set_cap_silc_inv')
   apply (auto simp: silc_inv_def)
  done

lemma select_ext_ev:
  "(\<And>s t. I s t \<Longrightarrow> A s t \<Longrightarrow> a s \<in> S \<Longrightarrow> a t \<in> S \<Longrightarrow> a s = a t)
   \<Longrightarrow> equiv_valid_inv I A (\<top> :: det_state \<Rightarrow> bool) (select_ext a S)"
  apply (clarsimp simp: select_ext_def gets_def get_def assert_def return_def bind_def)
  apply (simp add: equiv_valid_def2 equiv_valid_2_def return_def fail_def)
  done

end
