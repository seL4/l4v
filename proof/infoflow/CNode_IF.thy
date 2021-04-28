(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CNode_IF
imports FinalCaps
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma cap_fault_on_failure_rev:
  "reads_equiv_valid_inv A aag P m \<Longrightarrow> reads_equiv_valid_inv A aag P (cap_fault_on_failure cptr rp m)"
  unfolding cap_fault_on_failure_def handleE'_def
  apply(wp | wpc | simp add: o_def)+
  done

lemma cap_fault_on_failure_rev_g:
  "reads_respects_g aag l P m \<Longrightarrow> reads_respects_g aag l P (cap_fault_on_failure cptr rp m)"
  unfolding cap_fault_on_failure_def handleE'_def
  apply (wp | wpc | simp add: o_def)+
done

definition gets_apply where
  "gets_apply f x \<equiv>
  do
   s \<leftarrow> get;
   return ((f s) x)
  od"

lemma gets_apply_ev:
  "equiv_valid I A A (K (\<forall> s t. I s t \<and> A s t \<longrightarrow> (f s) x = (f t) x)) (gets_apply f x)"
  apply(simp add: gets_apply_def get_def bind_def return_def)
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  done

lemma gets_apply:
  "gets f >>= (\<lambda> f. g (f x)) = gets_apply f x >>= g"
  apply(simp add: gets_apply_def gets_def)
  done

lemma get_object_rev:
  "reads_equiv_valid_inv A aag (\<lambda> s. aag_can_read aag oref) (get_object oref)"
  apply (unfold get_object_def fun_app_def)
  apply (subst gets_apply)
  apply (wp gets_apply_ev | wp (once) hoare_drop_imps)+
  apply (fastforce elim: reads_equivE equiv_forE)
  done

lemma get_cap_rev:
  "reads_equiv_valid_inv A aag (K (aag_can_read aag (fst slot))) (get_cap slot)"
  unfolding get_cap_def
  apply(wp get_object_rev | wpc | simp add: split_def)+
  done

declare if_weak_cong[cong]

lemma resolve_address_bits_spec_rev:
  "reads_spec_equiv_valid_inv s A aag (pas_refined aag and K (is_cnode_cap (fst ref) \<longrightarrow> is_subject aag (obj_ref_of (fst ref)))) (resolve_address_bits ref)"
unfolding resolve_address_bits_def
proof(induct ref arbitrary: s rule: resolve_address_bits'.induct)
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
  "reads_equiv_valid_inv A aag (pas_refined aag
                                and K (is_cnode_cap (fst ref)
                                       \<longrightarrow> is_subject aag (obj_ref_of (fst ref))))
                (resolve_address_bits ref)"
  by (rule use_spec_ev[OF resolve_address_bits_spec_rev])

lemma lookup_slot_for_thread_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and K (is_subject aag thread))
                         (lookup_slot_for_thread thread cptr)"
  unfolding lookup_slot_for_thread_def fun_app_def
  apply (rule gen_asm_ev)
  apply (wp resolve_address_bits_rev gets_the_ev
       | simp)+
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
  apply (wp lookup_slot_for_thread_rev lookup_slot_for_thread_authorised get_cap_rev
        | simp add: split_def
        | strengthen aag_can_read_self)+
  done


lemmas lookup_cap_and_slot_reads_respects_g =
                  reads_respects_g_from_inv[OF lookup_cap_and_slot_rev lookup_cap_and_slot_inv]

lemma set_cap_reads_respects:
  "reads_respects aag l (K (aag_can_read aag (fst slot))) (set_cap cap slot)"
  apply(simp add: set_cap_def split_def)
  apply(wp set_object_reads_respects get_object_rev hoare_vcg_all_lift
       | wpc
       | simp )+
  done


lemma set_original_reads_respects:
  "reads_respects aag l \<top> (set_original slot v)"
  unfolding set_original_def
  apply(unfold equiv_valid_def2)
  apply(rule_tac Q="\<top>\<top>" in equiv_valid_rv_bind)
    apply(rule gets_is_original_cap_revrv)
   apply(rule modify_ev2)
   apply(clarsimp simp: equiv_for_or or_comp_dist)
   apply(safe)
    apply(erule reads_equiv_is_original_cap_update)
    apply(erule equiv_for_id_update)
   apply(erule affects_equiv_is_original_cap_update)
   apply(erule equiv_for_id_update)
  apply wp
  done


lemma set_cdt_reads_respects:
  "reads_respects aag l \<top> (set_cdt c)"
  unfolding set_cdt_def
  apply(unfold equiv_valid_def2)
  apply(rule get_bind_ev2)
  apply(unfold fun_app_def, rule put_ev2)
  apply(fastforce intro: reads_equiv_cdt_update affects_equiv_cdt_update equiv_for_refl)
  done

lemma set_cdt_ev2:
  "equiv_for (((aag_can_read aag) or (aag_can_affect aag l)) \<circ> fst) id c c' \<Longrightarrow>
   equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) (=) \<top> \<top> (set_cdt c) (set_cdt c')"
  unfolding set_cdt_def
  apply(rule get_bind_ev2)
  apply(unfold fun_app_def, rule put_ev2)
  apply(fastforce simp: equiv_for_or or_comp_dist reads_equiv_cdt_update affects_equiv_cdt_update)
  done

lemma set_cdt_list_ev2:
  "equiv_for (((aag_can_read aag) or (aag_can_affect aag l)) \<circ> fst) id c c' \<Longrightarrow>
   equiv_valid_2 (reads_equiv aag) (affects_equiv aag l) (affects_equiv aag l) (=) \<top> \<top> (set_cdt_list c) (set_cdt_list c')"
  unfolding set_cdt_list_def
  apply(rule get_bind_ev2)
  apply(unfold fun_app_def, rule put_ev2)
  apply(fastforce simp: equiv_for_or or_comp_dist reads_equiv_cdt_list_update affects_equiv_cdt_list_update)
  done

lemma kheap_get_tcb_eq: "kheap s ref = kheap t ref \<Longrightarrow> get_tcb ref s = get_tcb ref t"
  by (simp add: get_tcb_def)

lemma thread_get_rev:
  "reads_equiv_valid_inv A aag (K (aag_can_read aag thread)) (thread_get f thread)"
  unfolding thread_get_def fun_app_def
  by (wp gets_the_ev) (fastforce intro: kheap_get_tcb_eq elim: reads_equivE equiv_forD)

lemma update_cdt_reads_respects:
  "reads_respects aag l (K  (\<forall> rv rv'.
       equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id rv rv' \<longrightarrow>
       equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) f rv rv'))
      (update_cdt f)"
  unfolding update_cdt_def
  apply(rule gen_asm_ev)
  apply(unfold equiv_valid_def2)
  apply(rule equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp[OF gets_cdt_revrv])
    apply(rule TrueI)
   apply(rule set_cdt_ev2)
   apply(simp add: equiv_for_comp[symmetric])
  apply wp
  done

lemma update_cdt_list_reads_respects:
  "reads_respects aag l (K  (\<forall> rv rv'.
       equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) id rv rv' \<longrightarrow>
       equiv_for ((aag_can_read aag or aag_can_affect aag l) \<circ> fst) f rv rv'))
      (update_cdt_list f)"
  unfolding update_cdt_list_def
  apply(rule gen_asm_ev)
  apply(unfold equiv_valid_def2)
  apply(rule equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp[OF gets_cdt_list_revrv])
    apply(rule TrueI)
   apply(rule set_cdt_list_ev2)
   apply(simp add: equiv_for_comp[symmetric])
  apply wp
  done

lemma gen_asm_ev2':
  assumes "Q \<Longrightarrow> Q' \<Longrightarrow> equiv_valid_2 I A B R P P' f f'"
  shows "equiv_valid_2 I A B R (P and K Q) (P' and K Q') f f'"
  using assms by (fastforce simp: equiv_valid_def2 equiv_valid_2_def)

lemmas gen_asm_ev2 = gen_asm_ev2'[where P=\<top> and P'=\<top>, simplified]

lemma hoare_vcg_post_lift:
  "\<lbrakk>P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> \<lbrace> \<lambda> s. P \<rbrace> f \<lbrace> \<lambda> rv s. Q \<rbrace>"
  by(simp add: valid_def)

lemmas hoare_vcg_post_lift' = hoare_vcg_post_lift[where P="True", simplified]

lemma set_untyped_cap_as_full_reads_respects:
  "reads_respects aag l (K (aag_can_read aag (fst src_slot)))
        (set_untyped_cap_as_full src_cap new_cap src_slot)"
  unfolding set_untyped_cap_as_full_def
  apply (wp set_cap_reads_respects)
  apply auto
  done



lemma gets_apply_wp[wp]:
  "\<lbrace>\<lambda>s. P (f s x) s\<rbrace> gets_apply f x \<lbrace>P\<rbrace>"
  apply (simp add: gets_apply_def)
  apply wp
  done


lemma morestuff: "\<lbrakk>is_subject aag (fst src_slot);
        reads_equiv aag sa t\<rbrakk>
       \<Longrightarrow> is_original_cap sa src_slot = is_original_cap t src_slot"
  apply (clarsimp simp: reads_equiv_def2)
  apply (erule states_equiv_forE_is_original_cap)
  apply (drule_tac x="src_slot" in meta_spec)
  apply (frule aag_can_read_self)
  apply simp
  done


lemma cap_insert_reads_respects:
  notes split_paired_All[simp del]
  shows
  "reads_respects aag l (K (aag_can_read aag (fst src_slot) \<and> aag_can_read aag (fst dest_slot)))
                  (cap_insert new_cap src_slot dest_slot)"
  unfolding cap_insert_def
  apply(rule gen_asm_ev)
  apply(subst gets_apply)
  apply (simp only: cap_insert_ext_extended.dxo_eq)
  apply (simp only: cap_insert_ext_def)
  apply(wp set_original_reads_respects update_cdt_reads_respects set_cap_reads_respects
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
  apply(wp set_original_reads_respects gets_apply_ev update_cdt_reads_respects
           set_cap_reads_respects update_cdt_list_reads_respects
       | simp split del: if_split | fastforce simp: equiv_for_def split: option.splits)+
  apply (intro impI conjI allI)
  apply(fastforce simp: reads_equiv_def2 equiv_for_def
                  elim: states_equiv_forE_is_original_cap states_equiv_forE_cdt
                  dest: aag_can_read_self
                 split: option.splits)+
  done

lemma get_idemp:
  "do s1 \<leftarrow> get; s2 \<leftarrow> get; f s1 s2 od =
   do s1 \<leftarrow> get; f s1 s1 od"
  apply(simp add: get_def bind_def)
  done

lemma gets_apply2:
  "gets f >>= (\<lambda> f. g (f x) (f y)) =
   gets_apply f x >>= (\<lambda> x. gets_apply f y >>= (\<lambda> y. g x y))"
  apply(simp add: gets_def gets_apply_def get_idemp)
  done

lemma cap_swap_reads_respects:
  notes split_paired_All[simp del]
  shows
  "reads_respects aag l (K (is_subject aag (fst slot1) \<and> is_subject aag (fst slot2))) (cap_swap cap1 slot1 cap2 slot2)"
  unfolding cap_swap_def
  apply (subst gets_apply2)
  apply (simp add: bind_assoc[symmetric])
  apply (fold update_cdt_def)
  apply (simp add: bind_assoc cap_swap_ext_def)
  apply (rule gen_asm_ev)
  apply(wp set_original_reads_respects update_cdt_reads_respects gets_apply_ev set_cap_reads_respects update_cdt_list_reads_respects | simp split del: if_split | fastforce simp: equiv_for_def split: option.splits)+
  apply (intro impI conjI allI)
      apply((fastforce simp: reads_equiv_def2 equiv_for_def elim: states_equiv_forE_is_original_cap states_equiv_forE_cdt dest: aag_can_read_self split: option.splits)+)[2]
    apply (frule_tac x = slot1 in equiv_forD,elim conjE,drule aag_can_read_self,simp)
    apply (frule_tac x = slot2 in equiv_forD,elim conjE)
     apply (drule aag_can_read_self)+
     apply clarsimp
    apply clarsimp
    apply(erule equiv_forE)
    apply(fastforce intro: equiv_forI)
   apply(fastforce simp: equiv_for_def dest: aag_can_read_self elim: reads_equivE equiv_forE[where f="is_original_cap"] split: option.splits)+
  done

lemma tcb_at_def2: "tcb_at ptr s = (\<exists>tcb. kheap s ptr = Some (TCB tcb))"
  apply (clarsimp simp: tcb_at_def get_tcb_def split: kernel_object.splits option.splits)
  done

lemma set_object_globals_equiv:
  "\<lbrace> globals_equiv s and (\<lambda> s. ptr \<noteq> arm_global_pd (arch_state s))
    and (\<lambda>t. ptr = idle_thread t \<longrightarrow>
                (\<forall>tcb. kheap t (idle_thread t) = Some (TCB tcb) \<longrightarrow> (\<exists>tcb'. obj = (TCB tcb')
             \<and> arch_tcb_context_get (tcb_arch tcb) = arch_tcb_context_get (tcb_arch tcb')))
             \<and> (\<forall>tcb'. obj = (TCB tcb') \<longrightarrow> tcb_at (idle_thread t) t)) \<rbrace>
   set_object ptr obj
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (case_tac "ptr = idle_thread sa")
   apply (clarsimp simp: globals_equiv_def idle_equiv_def tcb_at_def2)
   apply (intro impI conjI allI notI iffI | clarsimp)+
  apply (clarsimp simp: globals_equiv_def idle_equiv_def tcb_at_def2)
  done

lemma set_object_globals_equiv'':
  "\<lbrace> globals_equiv s and (\<lambda> s. ptr \<noteq> arm_global_pd (arch_state s)) and (\<lambda>t. ptr \<noteq> idle_thread t)\<rbrace>
   set_object ptr obj
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  apply (wp set_object_globals_equiv)
  apply simp
  done

lemma set_cap_globals_equiv':
  "\<lbrace>globals_equiv s and (\<lambda> s. fst p \<noteq> arm_global_pd (arch_state s))\<rbrace>
   set_cap cap p \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_cap_def
  apply(simp only: split_def)
  apply(wp set_object_globals_equiv hoare_vcg_all_lift get_object_wp | wpc | simp)+
   apply (fastforce simp: obj_at_def is_tcb_def)+
  done


lemma set_cap_globals_equiv:
  "\<lbrace>globals_equiv s and valid_global_objs\<rbrace>
   set_cap cap p \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_cap_def
  apply(simp only: split_def)
  apply(wp set_object_globals_equiv hoare_vcg_all_lift get_object_wp | wpc | simp)+
   apply(fastforce simp: valid_global_objs_def valid_vso_at_def obj_at_def is_tcb_def)+
  done


lemma set_cdt_globals_equiv:
  "\<lbrace>globals_equiv s\<rbrace> set_cdt c \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_cdt_def
  apply(wp)
  apply(fastforce simp: globals_equiv_def idle_equiv_def)
  done

lemma update_cdt_globals_equiv:
  "\<lbrace>globals_equiv s\<rbrace> update_cdt f \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding update_cdt_def
  apply(wp set_cdt_globals_equiv)
  done

declare set_original_wp [wp del]
lemma set_original_globals_equiv:
  "\<lbrace>globals_equiv s\<rbrace> set_original slot v \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding set_original_def
  apply(wp)
  apply(fastforce simp: globals_equiv_def idle_equiv_def)
  done

crunch globals_equiv[wp]: set_untyped_cap_as_full "globals_equiv st"

lemma globals_equiv_exst_update[simp]:
  "globals_equiv st (trans_state f s) =
   globals_equiv st s"
  by (simp add: globals_equiv_def idle_equiv_def)

end

lemma (in is_extended') globals_equiv: "I (globals_equiv st)" by (rule lift_inv,simp)

context begin interpretation Arch . (*FIXME: arch_split*)

lemma cap_insert_globals_equiv:
  "\<lbrace>globals_equiv s and valid_global_objs\<rbrace>
   cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding cap_insert_def fun_app_def
  apply(wp update_cdt_globals_equiv set_original_globals_equiv set_cap_globals_equiv hoare_drop_imps dxo_wp_weak| simp)+
  done

lemma cap_move_globals_equiv:
  "\<lbrace>globals_equiv s and valid_global_objs\<rbrace>
    cap_move new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding cap_move_def fun_app_def
  apply(wp set_original_globals_equiv set_cdt_globals_equiv set_cap_globals_equiv
           dxo_wp_weak | simp)+
  done

lemma cap_swap_globals_equiv:
  "\<lbrace>globals_equiv s and valid_global_objs\<rbrace>
   cap_swap cap1 slot1 cap2 slot2
   \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  unfolding cap_swap_def
  apply(wp set_original_globals_equiv set_cdt_globals_equiv set_cap_globals_equiv
           dxo_wp_weak|simp)+
  done

lemma aag_cap_auth_ASIDPoolCap:
  "pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap r asid)) \<Longrightarrow>
   pas_refined aag s \<Longrightarrow> is_subject aag r"
unfolding aag_cap_auth_def
  apply (simp add: cli_no_irqs clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                   pas_refined_all_auth_is_owns is_page_cap_def)
  done

lemma aag_cap_auth_PageDirectory:
  "pas_cap_cur_auth aag (ArchObjectCap (PageDirectoryCap word (Some a))) \<Longrightarrow>
    pas_refined aag s \<Longrightarrow> is_subject aag word"
  unfolding aag_cap_auth_def
  apply (simp add: cli_no_irqs clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                   pas_refined_all_auth_is_owns is_page_cap_def)
  done

lemma aag_cap_auth_ASIDPoolCap_asid:
  "pas_cap_cur_auth aag (ArchObjectCap (ASIDPoolCap r asid)) \<Longrightarrow>
  asid' \<noteq> 0 \<Longrightarrow> asid_high_bits_of asid' = asid_high_bits_of asid \<Longrightarrow>
  pas_refined aag s \<Longrightarrow>
  is_subject_asid aag asid'"
  apply (frule (1) aag_cap_auth_ASIDPoolCap)
  unfolding aag_cap_auth_def
  apply (rule is_subject_into_is_subject_asid)
  apply auto
  done

lemma aag_cap_auth_PageCap_asid:
  "pas_cap_cur_auth aag (ArchObjectCap (PageCap dev word fun vmpage_size (Some (a, b))))
  \<Longrightarrow> pas_refined aag s
  \<Longrightarrow> is_subject_asid aag a"
  apply (auto simp add: aag_cap_auth_def cap_auth_conferred_def
                        cap_links_asid_slot_def label_owns_asid_slot_def
                 intro: pas_refined_Control_into_is_subject_asid)
  done

lemma aag_cap_auth_PageTableCap:
  "pas_cap_cur_auth aag (ArchObjectCap (PageTableCap word option)) \<Longrightarrow>
   pas_refined aag s \<Longrightarrow> is_subject aag word"
  unfolding aag_cap_auth_def
  apply (simp add: cli_no_irqs clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def
                   pas_refined_all_auth_is_owns is_page_cap_def)
  done

lemma aag_cap_auth_PageTableCap_asid: "pas_cap_cur_auth aag (ArchObjectCap (PageTableCap word (Some (a, b)))) \<Longrightarrow> pas_refined aag s \<Longrightarrow> is_subject_asid aag a"
  apply (auto simp add: aag_cap_auth_def cap_auth_conferred_def
                   cap_links_asid_slot_def label_owns_asid_slot_def
                   intro: pas_refined_Control_into_is_subject_asid)
  done

lemma aag_cap_auth_PageDirectoryCap:"pas_cap_cur_auth aag (ArchObjectCap (PageDirectoryCap word option)) \<Longrightarrow> pas_refined aag s \<Longrightarrow>
  is_subject aag word"
  unfolding aag_cap_auth_def
  apply (simp add: cli_no_irqs clas_no_asid cap_auth_conferred_def arch_cap_auth_conferred_def   pas_refined_all_auth_is_owns is_page_cap_def)
  done


lemma aag_cap_auth_PageDirectoryCap_asid:"pas_cap_cur_auth aag (ArchObjectCap (PageDirectoryCap word (Some a))) \<Longrightarrow> pas_refined aag s \<Longrightarrow>
  is_subject_asid aag a"
  unfolding aag_cap_auth_def
  apply (auto simp add: aag_cap_auth_def cap_auth_conferred_def
                   cap_links_asid_slot_def label_owns_asid_slot_def
                   intro: pas_refined_Control_into_is_subject_asid)
done


lemma aag_cap_auth_recycle_EndpointCap:"pas_cap_cur_auth aag (EndpointCap word1 word2 f) \<Longrightarrow>
  pas_refined aag s \<Longrightarrow>
  has_cancel_send_rights (EndpointCap word1 word2 f) \<Longrightarrow>
  is_subject aag word1"
  unfolding aag_cap_auth_def
  apply (simp add: cli_no_irqs clas_no_asid cap_auth_conferred_def
                   pas_refined_all_auth_is_owns is_page_cap_def
                   has_cancel_send_rights_def cap_rights_to_auth_def
                   all_rights_def)
  done

lemma aag_cap_auth_Zombie:"pas_cap_cur_auth aag (Zombie word x y) \<Longrightarrow>
  pas_refined aag s \<Longrightarrow>
 is_subject aag word"
  unfolding aag_cap_auth_def
  apply (simp add: cli_no_irqs clas_no_asid cap_auth_conferred_def
        pas_refined_all_auth_is_owns is_page_cap_def cap_rights_to_auth_def)
  done

lemmas aag_cap_auth_subject = aag_cap_auth_PageTableCap
                              aag_cap_auth_PageDirectory
                              aag_cap_auth_ASIDPoolCap
                              aag_cap_auth_ASIDPoolCap_asid
                              aag_cap_auth_PageCap_asid
                              aag_cap_auth_PageTableCap_asid
                              aag_cap_auth_PageDirectoryCap
                              aag_cap_auth_PageDirectoryCap_asid
                              aag_cap_auth_Zombie
                              aag_cap_auth_recycle_EndpointCap

(*Pushed up from Arch_IF*)
definition valid_ko_at_arm :: "'a::state_ext state \<Rightarrow> bool" where
  "valid_ko_at_arm \<equiv>
    \<lambda>s. \<exists>pd. ko_at (ArchObj (PageDirectory pd)) (arm_global_pd (arch_state s)) s"

lemma valid_arch_state_ko_at_arm:
  "valid_arch_state s \<Longrightarrow> valid_ko_at_arm s"
  apply(fastforce simp: valid_arch_state_def valid_ko_at_arm_def obj_at_def dest: a_type_pdD)
  done

lemma invs_valid_ko_at_arm:
  "invs s \<Longrightarrow> valid_ko_at_arm s" by (simp add: invs_def valid_state_def valid_arch_state_ko_at_arm)

lemmas invs_imps = invs_valid_vs_lookup invs_sym_refs invs_psp_aligned invs_distinct invs_valid_ko_at_arm invs_valid_global_objs invs_arch_state invs_valid_objs invs_valid_global_refs tcb_at_invs invs_cur invs_kernel_mappings

lemma cte_wp_at_page_cap_aligned :
  "\<lbrakk>cte_wp_at
           ((=) (ArchObjectCap (PageCap dev word fun vmpage_size option))) slot s ; valid_objs s \<rbrakk>\<Longrightarrow>
  is_aligned word (pageBitsForSize vmpage_size)"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (case_tac slot)
  apply simp
  apply (frule caps_of_state_valid_cap)
   apply simp
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def)
done

lemma cte_wp_at_pt_exists_cap:
  "valid_objs s \<Longrightarrow> cte_wp_at ((=) (ArchObjectCap (PageTableCap word option))) slot s \<Longrightarrow>
    x \<in> set [word , word + 4 .e. word + 2 ^ pt_bits - 1]
    \<Longrightarrow>\<exists>a b cap.
               caps_of_state s (a, b) = Some cap \<and>
               x && ~~ mask pt_bits \<in> Structures_A.obj_refs cap \<and> is_pt_cap cap"
  apply (case_tac slot)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (subgoal_tac "is_aligned word pt_bits")
   apply (frule (1) word_aligned_pt_slots)
   apply (simp add:pageBits_def cte_wp_at_caps_of_state is_pt_cap_def)
  apply (frule (1) cte_wp_valid_cap)
  apply (simp add: valid_cap_def cap_aligned_def pt_bits_def pageBits_def)
done


lemma pd_bits_store_pde_helper:
  "xa \<le> (kernel_base >> 20) - 1 \<Longrightarrow>
    is_aligned word pd_bits \<Longrightarrow>
   ((xa << 2) + word && ~~ mask pd_bits) = word"
  apply (clarsimp simp: field_simps)
  apply (subst is_aligned_add_helper)
    apply simp
   apply (rule shiftl_less_t2n)
    apply (erule order_le_less_trans)
    apply (simp add: kernel_base_def  pd_bits_def pageBits_def)+
done


lemma cte_wp_at_page_directory_not_in_globals:
  "\<lbrakk>cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap word optiona)))
           slot s; x \<le> (kernel_base >> 20) - 1; valid_objs s; valid_global_refs s\<rbrakk> \<Longrightarrow>
    (x << 2) + word && ~~ mask pd_bits \<notin> global_refs s
            "
  apply (frule (1) cte_wp_at_valid_objs_valid_cap)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule (1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def)
  apply (subgoal_tac "is_aligned word pd_bits")
  apply (rule pd_shifting_global_refs)
  apply (simp add: pd_bits_def pageBits_def)+
done


lemma not_in_global_not_arm:
  "A \<notin> global_refs s \<Longrightarrow> A \<noteq> arm_global_pd (arch_state s)" by (simp add: global_refs_def)


lemma cte_wp_at_page_cap_bits :
  "\<lbrakk>cte_wp_at ((=) (ArchObjectCap (PageTableCap word option))) slot
           s; valid_objs s\<rbrakk> \<Longrightarrow>
    cte_wp_at
                   (\<lambda>c. (\<lambda>x. x && ~~ mask pt_bits) `
                        set [word , word + 4 .e. word + 2 ^ pt_bits - 1]
                        \<subseteq> Structures_A.obj_refs c \<and>
                        is_pt_cap c)
                   slot s"
  apply (frule (1) cte_wp_at_valid_objs_valid_cap)
  apply (clarsimp simp: valid_cap_def cap_aligned_def)
  apply (erule cte_wp_at_weakenE)
  apply (unfold is_pt_cap_def)
  apply (subgoal_tac "is_aligned word pt_bits")
  prefer 2
  apply (simp add: pt_bits_def pageBits_def)
  apply (auto simp: word_aligned_pt_slots)
done

lemma mapM_x_swp_store_pte_invs' :
  "\<lbrace>invs
     and
     (\<lambda>s. cte_wp_at ((=) (ArchObjectCap (PageTableCap word option))) slot
           s)\<rbrace>
    mapM_x (swp store_pte InvalidPTE) [word , word + 4 .e. word + 2 ^ pt_bits - 1] \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_pre)
  apply (rule mapM_x_swp_store_pte_invs)
  apply clarsimp
  apply (case_tac slot)
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (auto simp: cte_wp_at_page_cap_bits invs_def valid_state_def valid_pspace_def)
done

lemma cte_wp_at_page_directory_not_in_kernel_mappings:
  "\<lbrakk>cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap word optiona)))
           slot s; x \<le> (kernel_base >> 20) - 1; valid_objs s; valid_global_refs s\<rbrakk> \<Longrightarrow>
  ucast ((x << 2) + word && mask pd_bits >> 2) \<notin> kernel_mapping_slots"
  apply (frule (1) cte_wp_at_valid_objs_valid_cap)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (drule (1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def)
  apply (subgoal_tac "is_aligned word pd_bits")
  apply (rule pd_shifting_kernel_mapping_slots)
  apply (simp add: pd_bits_def pageBits_def)+
done

lemma preemption_point_def2:
  "(preemption_point :: (unit,det_ext) p_monad)
     = doE liftE update_work_units;
           rv \<leftarrow> liftE work_units_limit_reached;
           if rv then doE
             liftE reset_work_units;
             liftE (do_machine_op (getActiveIRQ True)) >>=E
             case_option (returnOk ()) (K (throwError $ ()))
           odE else returnOk()
       odE"
  apply (rule ext)
  apply (simp add: preemption_point_def OR_choiceE_def wrap_ext_bool_det_ext_ext_def ef_mk_ef work_units_limit_reached_empty_fail)
  apply (simp add: select_f_def)
  apply (clarsimp simp: work_units_limit_reached_def gets_def liftE_def select_f_def get_def lift_def return_def bind_def bindE_def split_def image_def split: option.splits sum.splits)
  done


(* moved from ADT_IF *)
definition irq_at :: "nat \<Rightarrow> (10 word \<Rightarrow> bool) \<Rightarrow> irq option" where
  "irq_at pos masks \<equiv>
  let i = irq_oracle pos in
  (if i = 0x3FF \<or> masks i then None else Some i)"

definition is_irq_at :: "('z::state_ext) state \<Rightarrow> irq \<Rightarrow> nat \<Rightarrow> bool" where
  "is_irq_at s \<equiv> \<lambda> irq pos. irq_at pos (irq_masks (machine_state s)) = Some irq"

text \<open>
  We require that interrupts recur in order to ensure that no individual
  big step ever diverges.
\<close>
definition irq_is_recurring :: "irq \<Rightarrow> ('z::state_ext) state \<Rightarrow> bool" where
  "irq_is_recurring irq s \<equiv> \<forall>n. (\<exists>m. is_irq_at s irq (n+m))"


lemma dmo_getActiveIRQ_wp:
  "\<lbrace>\<lambda>s. P (irq_at (irq_state (machine_state s) + 1) (irq_masks (machine_state s))) (s\<lparr>machine_state := (machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>)\<rparr>)\<rbrace> do_machine_op (getActiveIRQ in_kernel) \<lbrace>P\<rbrace>"
  apply(simp add: do_machine_op_def getActiveIRQ_def non_kernel_IRQs_def)
  apply(wp modify_wp | wpc)+
  apply clarsimp
  apply(erule use_valid)
   apply (wp modify_wp)
  apply(auto simp: irq_at_def Let_def split: if_splits)
  done

lemma only_timer_irqs:
  "\<lbrakk>domain_sep_inv False st s; valid_irq_states s; is_irq_at s irq n\<rbrakk> \<Longrightarrow>
  interrupt_states s irq = IRQTimer"
  apply(clarsimp simp: is_irq_at_def irq_at_def Let_def split: if_split_asm)
  apply(case_tac "interrupt_states s (irq_oracle n)")
     apply(blast elim: valid_irq_statesE)
    apply(fastforce simp: domain_sep_inv_def)
   apply assumption
  apply(fastforce simp: domain_sep_inv_def)
  done

lemma dmo_getActiveIRQ_only_timer:
  "\<lbrace>domain_sep_inv False st and valid_irq_states\<rbrace>
   do_machine_op (getActiveIRQ in_kernel)
   \<lbrace>\<lambda>rv s. (\<forall>x. rv = Some x \<longrightarrow> interrupt_states s x = IRQTimer)\<rbrace>"
  apply(wp dmo_getActiveIRQ_wp)
  apply clarsimp
  apply(erule (1) only_timer_irqs)
  apply(simp add: is_irq_at_def)
  done

text \<open>
  There is only one interrupt turned on, namely @{term irq}, and it is
  a timer interrupt.
\<close>
definition only_timer_irq :: "10 word \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "only_timer_irq irq s \<equiv> (\<forall>x. interrupt_states s x = IRQTimer \<longrightarrow> x = irq) \<and> irq_is_recurring irq s"

lemma is_irq_at_triv:
  assumes a:
  "\<And>P. \<lbrace>(\<lambda>s. P (irq_masks (machine_state s))) and Q\<rbrace>
        f
       \<lbrace>\<lambda>rv s. P (irq_masks (machine_state s)) \<rbrace>"
  shows
  "\<lbrace> (\<lambda>s. P (is_irq_at s)) and Q \<rbrace> f \<lbrace> \<lambda>rv s. P (is_irq_at s) \<rbrace>"
  apply(clarsimp simp: valid_def is_irq_at_def irq_at_def Let_def)
  apply(erule use_valid[OF _ a])
  apply simp
  done

lemma irq_is_recurring_triv:
  assumes a:
  "\<And>P. \<lbrace>(\<lambda>s. P (irq_masks (machine_state s))) and Q\<rbrace>
        f
       \<lbrace>\<lambda>rv s. P (irq_masks (machine_state s))\<rbrace>"
  shows
  "\<lbrace>irq_is_recurring irq and Q\<rbrace> f \<lbrace>\<lambda>_. irq_is_recurring irq\<rbrace>"
  apply(clarsimp simp: irq_is_recurring_def valid_def)
  apply(rule use_valid[OF _ is_irq_at_triv[OF a]])
   apply assumption
  apply simp
  done

lemma domain_sep_inv_refl:
  "domain_sep_inv irqs st s \<Longrightarrow> domain_sep_inv irqs s s"
  apply(fastforce simp: domain_sep_inv_def)
  done

lemma domain_sep_inv_to_interrupt_states_pres:
  assumes a: "\<And> st. \<lbrace>domain_sep_inv False (st::'z::state_ext state) and P\<rbrace> f \<lbrace>\<lambda>_. domain_sep_inv False st\<rbrace>"
  shows "\<lbrace>(\<lambda>s. Q (interrupt_states (s::'z::state_ext state))) and P and domain_sep_inv False st\<rbrace> f \<lbrace>\<lambda>_ s. Q (interrupt_states s)\<rbrace>"
  apply(clarsimp simp: valid_def)
   apply(erule use_valid)
   apply(rule hoare_strengthen_post)
    apply(rule_tac st=s in a)
   apply(fastforce simp: domain_sep_inv_def)
  apply(simp add: domain_sep_inv_refl)
  done

lemma only_timer_irq_pres:
  assumes a:
  "\<And>P. \<lbrace>(\<lambda>s. P (irq_masks (machine_state s))) and Q\<rbrace>
        f
       \<lbrace>\<lambda>rv s. P (irq_masks (machine_state s)) \<rbrace>"
  assumes b:
  "\<And> st::'z::state_ext state. \<lbrace>domain_sep_inv False st and P\<rbrace> f \<lbrace>\<lambda>_. domain_sep_inv False st\<rbrace>"
  shows
  "\<lbrace>only_timer_irq irq and Q and P and (\<lambda>s. domain_sep_inv False (st::'z::state_ext state) (s::'z::state_ext state))\<rbrace> f \<lbrace>\<lambda>_. only_timer_irq irq\<rbrace>"
  apply(clarsimp simp: only_timer_irq_def valid_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(drule spec)
   apply(erule mp)
   apply(erule contrapos_pp, erule use_valid, rule domain_sep_inv_to_interrupt_states_pres, rule b, fastforce)
  apply(erule use_valid[OF _ irq_is_recurring_triv[OF a]])
  by simp

definition only_timer_irq_inv :: "10 word \<Rightarrow> 'a::state_ext state \<Rightarrow> 'a state \<Rightarrow> bool" where
  "only_timer_irq_inv irq st \<equiv> domain_sep_inv False st and only_timer_irq irq"

lemma only_timer_irq_inv_pres:
  assumes a:
  "\<And>P. \<lbrace>(\<lambda>s. P (irq_masks (machine_state s))) and Q\<rbrace>
        f
       \<lbrace>\<lambda>rv s. P (irq_masks (machine_state s)) \<rbrace>"
  assumes b: "\<And>st::'z::state_ext state. \<lbrace>domain_sep_inv False st and P\<rbrace> f \<lbrace>\<lambda>_. domain_sep_inv False st\<rbrace>"
  shows "\<lbrace>only_timer_irq_inv irq (st::'z::state_ext state) and Q and P\<rbrace> f \<lbrace>\<lambda>_. only_timer_irq_inv irq st\<rbrace>"
  apply(clarsimp simp: only_timer_irq_inv_def valid_def)
  apply(rule conjI)
   apply(erule use_valid[OF _ b], simp)
  apply(erule use_valid[OF _ only_timer_irq_pres[OF a b]])
  apply simp
  done

lemma only_timer_irq_inv_domain_sep_inv[intro]:
  "only_timer_irq_inv irq st s \<Longrightarrow> domain_sep_inv False st s"
  apply(simp add: only_timer_irq_inv_def)
  done

(* FIXME: repalce Infoflow.do_machine_op_spec_reads_respects' with this *)
lemma do_machine_op_spec_reads_respects':
  assumes equiv_dmo:
   "equiv_valid_inv (equiv_machine_state (aag_can_read aag) And equiv_irq_state)  (equiv_machine_state (aag_can_affect aag l)) Q f"
  assumes guard:
    "\<And> s. P s \<Longrightarrow> Q (machine_state s)"
  shows
  "spec_reads_respects st aag l P (do_machine_op f)"
  unfolding do_machine_op_def spec_equiv_valid_def
  apply(rule equiv_valid_2_guard_imp)
   apply(rule_tac  R'="\<lambda> rv rv'. equiv_machine_state (aag_can_read aag or aag_can_affect aag l) rv rv' \<and> equiv_irq_state rv rv'" and Q="\<lambda> r s. st = s \<and> Q r" and Q'="\<lambda> r s. Q r" and P="(=) st" and P'="\<top>" in equiv_valid_2_bind)
       apply(rule gen_asm_ev2_l[simplified K_def pred_conj_def])
       apply(rule gen_asm_ev2_r')
       apply(rule_tac R'="\<lambda> (r, ms') (r', ms'').  r = r' \<and> equiv_machine_state (aag_can_read aag)  ms' ms'' \<and> equiv_machine_state (aag_can_affect aag l) ms' ms'' \<and> equiv_irq_state ms' ms''" and Q="\<lambda> r s. st = s" and Q'="\<top>\<top>" and P="\<top>" and P'="\<top>" in equiv_valid_2_bind_pre)
            apply(clarsimp simp: modify_def get_def put_def bind_def return_def equiv_valid_2_def)
            apply(fastforce intro: reads_equiv_machine_state_update affects_equiv_machine_state_update)
            apply(insert equiv_dmo)[1]
           apply(clarsimp simp: select_f_def equiv_valid_2_def equiv_valid_def2 equiv_for_or simp: split_def split: prod.splits simp: equiv_for_def)[1]
           apply(drule_tac x=rv in spec, drule_tac x=rv' in spec)
           apply(fastforce)
          apply(rule select_f_inv)
         apply(rule wp_post_taut)
        apply simp+
      apply(clarsimp simp: equiv_valid_2_def in_monad)
      apply(fastforce elim: reads_equivE affects_equivE equiv_forE intro: equiv_forI)
     apply(wp | simp add: guard)+
  done

lemma is_irq_at_not_masked:
  "is_irq_at s irq pos \<Longrightarrow> \<not> irq_masks (machine_state s) irq"
  apply(clarsimp simp: is_irq_at_def irq_at_def split: option.splits simp: Let_def split: if_splits)
  done


lemma irq_is_recurring_not_masked:
  "irq_is_recurring irq s \<Longrightarrow> \<not> irq_masks (machine_state s) irq"
  apply(clarsimp simp: irq_is_recurring_def)
  apply(blast dest: is_irq_at_not_masked)
  done

lemma only_timer_irq_inv_determines_irq_masks:
  "\<lbrakk>invs s; only_timer_irq_inv irq st s\<rbrakk> \<Longrightarrow>
   \<not> irq_masks (machine_state s) irq \<and>
   (\<forall>x. x \<noteq> irq \<longrightarrow> irq_masks (machine_state s) x)"
  apply(rule conjI)
   apply(clarsimp simp: only_timer_irq_inv_def only_timer_irq_def)
   apply(blast dest: irq_is_recurring_not_masked)
  apply(clarsimp simp: only_timer_irq_inv_def domain_sep_inv_def only_timer_irq_def)
  apply(case_tac "interrupt_states s x")
    apply(fastforce simp: invs_def valid_state_def valid_irq_states_def valid_irq_masks_def)
   apply fastforce+
  done

lemma gets_irq_masks_equiv_valid:
  "equiv_valid_inv I A (\<lambda>s. \<not> (irq_masks s) irq \<and> (\<forall>x. x \<noteq> irq \<longrightarrow> (irq_masks s) x)) (gets irq_masks)"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad)
  apply(auto)
  done

lemma irq_state_increment_reads_respects_memory:
  "equiv_valid_inv
          (equiv_machine_state (\<lambda>x. aag_can_read_label aag (pasObjectAbs aag x))
            And
           equiv_irq_state)
          (equiv_for
            (\<lambda>x. aag_can_affect_label aag l \<and>
                 pasObjectAbs aag x \<in> subjectReads (pasPolicy aag) l)
            underlying_memory)  \<top> (modify (\<lambda>s. s\<lparr>irq_state := Suc (irq_state s)\<rparr>))"
  apply(simp add: equiv_valid_def2)
  apply(rule modify_ev2)
  apply(fastforce intro: equiv_forI elim: equiv_forE)
  done

lemma irq_state_increment_reads_respects_device:
  "equiv_valid_inv
          (equiv_machine_state (\<lambda>x. aag_can_read_label aag (pasObjectAbs aag x))
            And
           equiv_irq_state)
          (equiv_for
            (\<lambda>x. aag_can_affect_label aag l \<and>
                 pasObjectAbs aag x \<in> subjectReads (pasPolicy aag) l)
            device_state)  \<top> (modify (\<lambda>s. s\<lparr>irq_state := Suc (irq_state s)\<rparr>))"
  apply(simp add: equiv_valid_def2)
  apply(rule modify_ev2)
  apply(fastforce intro: equiv_forI elim: equiv_forE)
  done

lemma use_equiv_valid_inv:
  "\<lbrakk>x\<in>fst (f st); y\<in> fst (f s); g s; g st;I s st;P s st; equiv_valid_inv I P g f \<rbrakk>
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

lemma dmo_getActiveIRQ_reads_respects:
  notes gets_ev[wp del]
  shows
  "reads_respects aag l (invs and only_timer_irq_inv irq st) (do_machine_op (getActiveIRQ in_kernel))"
  apply(rule use_spec_ev)
  apply(rule do_machine_op_spec_reads_respects')
   apply(simp add: getActiveIRQ_def)
   apply (wp irq_state_increment_reads_respects_memory irq_state_increment_reads_respects_device
             gets_ev[where f="irq_oracle \<circ> irq_state"] equiv_valid_inv_conj_lift
             gets_irq_masks_equiv_valid modify_wp
         | simp add: no_irq_def)+
  apply(rule only_timer_irq_inv_determines_irq_masks, blast+)
  done

lemma dmo_getActiveIRQ_globals_equiv:
  "\<lbrace>globals_equiv st\<rbrace> do_machine_op (getActiveIRQ in_kernel) \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (wp dmo_getActiveIRQ_wp)
  apply(auto simp: globals_equiv_def idle_equiv_def)
  done

lemma dmo_getActiveIRQ_reads_respects_g :
  "reads_respects_g aag l (invs and only_timer_irq_inv irq st) (do_machine_op (getActiveIRQ in_kernel))"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule dmo_getActiveIRQ_reads_respects)
   apply(rule doesnt_touch_globalsI)
   apply(wp dmo_getActiveIRQ_globals_equiv | blast)+
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

crunches reset_work_units, work_units_limit_reached, update_work_units
     for only_timer_irq_inv[wp]: "only_timer_irq_inv irq st"
  (simp: only_timer_irq_inv_def only_timer_irq_def irq_is_recurring_def is_irq_at_def)

crunch invs[wp]: work_units_limit_reached invs

lemma preemption_point_reads_respects:
  "reads_respects aag l (invs and only_timer_irq_inv irq st) preemption_point"
  apply (simp add: preemption_point_def2)
  apply (wp | wpc | simp add: comp_def)+
            apply ((wp dmo_getActiveIRQ_reads_respects hoare_TrueI | simp
                  | wp (once) hoare_drop_imps)+)[8]
   apply wp
  apply force
  done

lemma all_children_descendants_equal:
  "\<lbrakk>equiv_for P id s t; all_children P s; all_children P t; P slot\<rbrakk>
   \<Longrightarrow> descendants_of slot s = descendants_of slot t"
  apply(clarsimp | rule equalityI)+
   apply(frule_tac p="(a, b)" and q="slot" and m=s in all_children_descendants_of)
     apply(simp)+
   apply(simp add: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)
   apply(rule_tac r'="{(p, c). s c = Some p}" and Q="P" in trancl_subset_equivalence)
     apply(clarsimp)+
    apply(frule_tac p="(aa, ba)" and q="slot" in all_children_descendants_of)
      apply(fastforce simp: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)+
   apply(fastforce simp: equiv_for_def)
  apply(clarsimp)
  apply(frule_tac p="(a, b)" and q="slot" and m=t in all_children_descendants_of)
    apply(simp)+
  apply(simp add: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)
  apply(rule_tac r'="{(p, c). t c = Some p}" and Q="P" in trancl_subset_equivalence)
    apply(clarsimp)+
   apply(frule_tac p="(aa, ba)" and q="slot" and m=t in all_children_descendants_of)
     apply(fastforce simp: equiv_for_def descendants_of_def cdt_parent_rel_def is_cdt_parent_def)+
  done

lemma cca_can_read:
  "\<lbrakk>valid_mdb s; valid_objs s; cdt_change_allowed' aag slot s; pas_refined aag s\<rbrakk>
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
  "\<lbrakk>reads_equiv aag s t; affects_equiv aag l s t; pas_refined aag s;
    pas_refined aag t; is_subject aag (fst slot)\<rbrakk>
   \<Longrightarrow> descendants_of slot (cdt s) = descendants_of slot (cdt t)"
  apply (rule all_children_descendants_equal[OF _ all_children_subjectReads all_children_subjectReads])
     apply (elim reads_equivE)
     apply (solves\<open>simp add: equiv_for_apply\<close>)
  by force+

lemma gets_descendants_of_revrv:
  "reads_equiv_valid_rv_inv (affects_equiv aag l) aag (=)
                            (pas_refined aag and K (is_subject aag (fst slot)))
                            (gets (descendants_of slot \<circ> cdt))"
  apply(rule gets_evrv'')
  apply clarsimp
  by (rule descendants_of_eq)

lemma silc_dom_equiv_trans:
  "\<lbrakk>silc_dom_equiv aag s t; silc_dom_equiv aag t u\<rbrakk> \<Longrightarrow> silc_dom_equiv aag s u"
  by (auto simp: silc_dom_equiv_def elim: equiv_for_trans)

lemma silc_dom_equiv_sym:
  "\<lbrakk>silc_dom_equiv aag s t\<rbrakk> \<Longrightarrow> silc_dom_equiv aag t s"
  by (auto simp: silc_dom_equiv_def elim: equiv_for_sym)

lemma reads_respects_f:
  "\<lbrakk>reads_respects aag l P f; \<lbrace>silc_inv aag st and Q\<rbrace> f \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>\<rbrakk> \<Longrightarrow>
   reads_respects_f aag l (silc_inv aag st and P and Q) f"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def reads_equiv_f_def)
  apply(rule conjI, fastforce)
  apply(rule conjI, fastforce)
  apply(subst conj_commute, rule conjI, fastforce)
  apply(rule silc_dom_equiv_trans)
   apply(rule silc_dom_equiv_sym)
   apply(rule silc_inv_silc_dom_equiv)
   apply(erule (1) use_valid, simp)
  apply(rule silc_inv_silc_dom_equiv)
  apply(erule (1) use_valid, simp)
  done

lemma preemption_point_reads_respects_f:
  "reads_respects_f aag l (invs and only_timer_irq_inv irq st' and silc_inv aag st) preemption_point"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_f)
    apply (rule preemption_point_reads_respects)
   apply (wp, force+)
  done

abbreviation
  reads_spec_equiv_valid_f :: "det_state \<Rightarrow> (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow> (det_state \<Rightarrow> det_state \<Rightarrow> bool) \<Rightarrow> 'a subject_label PAS \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool"
where
  "reads_spec_equiv_valid_f s A B aag P f \<equiv> spec_equiv_valid s (reads_equiv_f aag) A B P f"

abbreviation reads_spec_equiv_valid_f_inv
where
  "reads_spec_equiv_valid_f_inv s A aag P f \<equiv> reads_spec_equiv_valid_f s A A aag P f"

abbreviation
  spec_reads_respects_f :: "det_state \<Rightarrow> 'a subject_label PAS \<Rightarrow> 'a subject_label \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool"
where
  "spec_reads_respects_f s aag l P f \<equiv> reads_spec_equiv_valid_f_inv s (affects_equiv aag l) aag P f"

definition reads_equiv_f_g where
  "reads_equiv_f_g aag s s' \<equiv> reads_equiv aag s s' \<and> globals_equiv s s' \<and> silc_dom_equiv aag s s'"

abbreviation reads_respects_f_g :: "'a subject_label PAS \<Rightarrow> 'a subject_label \<Rightarrow> (det_state \<Rightarrow> bool) \<Rightarrow> (det_state,'b) nondet_monad \<Rightarrow> bool"
where
"reads_respects_f_g aag l P f \<equiv>
   equiv_valid_inv (reads_equiv_f_g aag) (affects_equiv aag l) P f"

lemma reads_equiv_f_g_conj:
  "reads_equiv_f_g aag s s' \<equiv> reads_equiv_f aag s s' \<and> reads_equiv_g aag s s'"
  apply(simp add: reads_equiv_f_g_def reads_equiv_f_def reads_equiv_g_def conj_comms)
  done

lemma reads_respects_f_g:
  "\<lbrakk>reads_respects_f aag l P f; doesnt_touch_globals Q f\<rbrakk> \<Longrightarrow>
   reads_respects_f_g aag l (P and Q) f"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply(subst (asm) reads_equiv_f_g_conj, erule conjE)
  apply(subst reads_equiv_f_g_conj)
  apply(drule reads_equiv_gD)
  apply clarsimp
  apply(subgoal_tac "reads_equiv_g aag b ba", blast)
  apply(subgoal_tac "globals_equiv b ba", fastforce intro: reads_equiv_gI simp: reads_equiv_f_def)
  apply(rule globals_equiv_trans)
   apply(rule globals_equiv_sym)
   apply(fastforce intro: globals_equivI)
  apply(rule globals_equiv_trans)
   apply(assumption)
  apply(fastforce intro: globals_equivI)
  done

lemma reads_equiv_valid_rv_inv_f:
  assumes a: "reads_equiv_valid_rv_inv A aag R P f"
  assumes b: "\<And> P. \<lbrace> P \<rbrace> f \<lbrace>\<lambda>_. P \<rbrace>"
  shows "equiv_valid_rv_inv (reads_equiv_f aag) A R P f"
  apply(clarsimp simp: equiv_valid_2_def reads_equiv_f_def)
  apply(insert a, clarsimp simp: equiv_valid_2_def)
  apply(drule_tac x=s in spec, drule_tac x=t in spec, clarsimp)
  apply(drule (1) bspec, clarsimp)
  apply(drule (1) bspec, clarsimp)
  apply(drule state_unchanged[OF b])+
  by simp


lemma set_cap_silc_inv':
  "\<lbrace>silc_inv aag st and (((\<lambda>s. \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst slot)) \<longrightarrow>
              (\<exists>lslot.
                  lslot \<in> slots_holding_overlapping_caps cap s \<and>
                  pasObjectAbs aag (fst lslot) = SilcLabel)) and
         K (pasObjectAbs aag (fst slot) \<noteq> SilcLabel)))\<rbrace> set_cap cap slot
   \<lbrace>\<lambda>_. silc_inv aag st\<rbrace>"
  apply(rule hoare_pre)
   apply(rule set_cap_silc_inv)
  by blast

lemma set_cap_reads_respects_f:
  "reads_respects_f aag l (silc_inv aag st and
         (\<lambda>s. \<not> cap_points_to_label aag cap (pasObjectAbs aag (fst slot)) \<longrightarrow>
               (\<exists>lslot.
                   lslot \<in> slots_holding_overlapping_caps cap s \<and>
                   pasObjectAbs aag (fst lslot) = SilcLabel)) and
         K (is_subject aag (fst slot))) (set_cap cap slot)"
  apply(rule equiv_valid_guard_imp)
   apply(rule reads_respects_f[OF set_cap_reads_respects, OF set_cap_silc_inv'])
  apply(auto simp: silc_inv_def)
  done

lemma select_ext_ev:
  "(\<And>s t. I s t \<Longrightarrow> A s t \<Longrightarrow> a s \<in> S \<Longrightarrow> a t \<in> S \<Longrightarrow> a s = a t) \<Longrightarrow> equiv_valid_inv I A (\<top> :: det_ext state \<Rightarrow> bool) (select_ext a S)"
  apply (clarsimp simp: select_ext_def gets_def get_def assert_def return_def bind_def)
  apply (simp add: equiv_valid_def2 equiv_valid_2_def return_def fail_def)
  done

end

end
