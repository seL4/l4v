(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Schedule_AI
imports VSpace_AI
begin

locale Schedule_AI begin

extend_locale 
  fixes Schedule_AI_dummy_const :: nat
  assumes Schedule_AI_trivial_asm: "Schedule_AI_dummy_const > 0"

end

context begin interpretation Arch .
(* FIXME arch_split: some of these could be moved to generic theories
   so they don't need to be unqualified. *)
requalify_facts 
  no_irq
  no_irq_storeWord
  ef_storeWord
  mapM_UNIV_wp

end

lemma findM_inv'':
  assumes p: "suffixeq xs xs'"
  assumes x: "\<And>x xs. suffixeq (x # xs) xs' \<Longrightarrow> \<lbrace>P (x # xs)\<rbrace> m x \<lbrace>\<lambda>rv s. (rv \<longrightarrow> Q s) \<and> (\<not> rv \<longrightarrow> P xs s)\<rbrace>"
  assumes y: "\<And>s. P [] s \<Longrightarrow> Q s"
  shows      "\<lbrace>P xs\<rbrace> findM m xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  using p
  apply (induct xs)
   apply simp
   apply wp
   apply (erule y)
  apply (frule suffixeq_ConsD)
  apply simp
  apply wp
   apply assumption
  apply (erule x)
  done

lemmas findM_inv' = findM_inv''[OF suffixeq_refl]

lemma findM_inv:
  assumes x: "\<And>x xs. \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> findM m xs \<lbrace>\<lambda>rv. P\<rbrace>"
  by (rule findM_inv', simp_all add: x)


lemma allActiveTCBs_gets:
  "allActiveTCBs = gets (\<lambda>state. {x. getActiveTCB x state \<noteq> None})"
  by (simp add: allActiveTCBs_def gets_def)


lemma postfix_tails:
  "\<lbrakk> suffixeq (xs # ys) (tails zs) \<rbrakk>
     \<Longrightarrow> suffixeq xs zs \<and> (xs # ys) = tails xs"
  apply (induct zs arbitrary: xs ys)
   apply (clarsimp elim!: suffixeqE)
   apply (case_tac zs, simp_all)[1]
  apply (clarsimp elim!: suffixeqE)
  apply (case_tac zsa, simp_all)
   apply clarsimp
  apply clarsimp
  apply (erule meta_allE, erule meta_allE, drule meta_mp,
         rule suffixeq_appendI[OF suffixeq_refl])
  apply clarsimp
  apply (erule suffixeq_ConsI)
  done


lemma valid_irq_states_cur_thread_update[simp]:
  "valid_irq_states (cur_thread_update f s) = valid_irq_states s"
  by(simp add: valid_irq_states_def)

lemma sct_invs:
  "\<lbrace>invs and tcb_at t\<rbrace> modify (cur_thread_update (%_. t)) \<lbrace>\<lambda>rv. invs\<rbrace>"
  by wp (clarsimp simp add: invs_def cur_tcb_def valid_state_def valid_idle_def
                            valid_irq_node_def valid_machine_state_def)

lemma storeWord_valid_irq_states:
  "\<lbrace>\<lambda>m. valid_irq_states (s\<lparr>machine_state := m\<rparr>)\<rbrace> storeWord x y
   \<lbrace>\<lambda>a b. valid_irq_states (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  apply (simp add: valid_irq_states_def | wp no_irq | simp add: no_irq_storeWord)+
  done

lemma dmo_storeWord_valid_irq_states[wp]:
  "\<lbrace>valid_irq_states\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>_. valid_irq_states\<rbrace>"
  apply(simp add: do_machine_op_def |  wp | wpc)+
  apply clarsimp
  apply(erule use_valid[OF _ storeWord_valid_irq_states])
  by simp

context begin interpretation Arch . (*FIXME: arch_split*)
lemma dmo_mapM_storeWord_0_invs[wp]:
  "valid invs (do_machine_op (mapM (\<lambda>p. storeWord p 0) S)) (\<lambda>_. invs)"
  apply (simp add: dom_mapM ef_storeWord)
  apply (rule mapM_UNIV_wp)
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def cur_tcb_def
                        valid_machine_state_def)
  apply (rule conjI)
   apply(erule use_valid[OF _ storeWord_valid_irq_states], simp)
  apply (erule use_valid)
   apply (simp add: storeWord_def word_rsplit_0)
   apply wp
  apply simp
  done
end

lemma dmo_kheap_arch_state[wp]:
  "\<lbrace>\<lambda>s. P (kheap s) (arch_state s)\<rbrace>
   do_machine_op a
   \<lbrace>\<lambda>_ s. P (kheap s) (arch_state s)\<rbrace>"
  by (clarsimp simp: do_machine_op_def simpler_gets_def select_f_def
          simpler_modify_def return_def bind_def valid_def)

context Arch begin global_naming ARM (*FIXME: arch_split*)
lemma set_vm_root_kheap_arch_state[wp]:
  "\<lbrace>\<lambda>s. P (kheap s) (arm_globals_frame (arch_state s))\<rbrace> set_vm_root a
   \<lbrace>\<lambda>_ s. P (kheap s) (arm_globals_frame (arch_state s))\<rbrace>" (is "valid ?P _ _")
  apply (simp add: set_vm_root_def arm_context_switch_def)
  apply (wp | wpcw | simp add: arm_context_switch_def get_hw_asid_def
           store_hw_asid_def find_pd_for_asid_assert_def find_free_hw_asid_def
           invalidate_hw_asid_entry_def invalidate_asid_def load_hw_asid_def)+
     apply (simp add: whenE_def, intro conjI impI)
      apply (wp, simp add: returnOk_def validE_E_def validE_def)+
    apply (simp add: whenE_def, intro conjI[rotated] impI)
     apply (wp | simp add: returnOk_def validE_E_def validE_def)+
    apply (wp | simp add: throwError_def validE_R_def validE_def)+
done
end

context Arch begin global_naming ARM (*FIXME: arch_split*)
lemma clearExMonitor_invs [wp]:
  "\<lbrace>invs\<rbrace> do_machine_op clearExMonitor \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply (clarsimp simp: clearExMonitor_def machine_op_lift_def
                        machine_rest_lift_def in_monad select_f_def)
  done
end

context begin interpretation Arch . (*FIXME: arch_split*)
lemma arch_stt_invs [wp]:
  "\<lbrace>invs\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply wp
  apply (simp add: in_user_frame_def obj_at_def)
  apply (wp hoare_vcg_ex_lift)
  apply (rule_tac x=ARMSmallPage in exI)
  apply (clarsimp simp add: invs_def valid_state_def valid_arch_state_def
           valid_pspace_def pspace_aligned_def obj_at_def dom_def)
  apply (drule spec, erule impE, fastforce)
  apply (clarsimp simp: is_aligned_neg_mask_eq a_type_simps)
  done
end

lemmas do_machine_op_tcb[wp] =
  do_machine_op_obj_at[where P=id and Q=is_tcb, simplified]

context begin interpretation Arch . (*FIXME: arch_split*)
lemma arch_stt_tcb [wp]:
  "\<lbrace>tcb_at t'\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. tcb_at t'\<rbrace>"
  apply (simp add: arch_switch_to_thread_def) 
  apply (wp)
  done
end

lemma stt_tcb [wp]:
  "\<lbrace>tcb_at t\<rbrace> switch_to_thread t \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  apply (simp add: switch_to_thread_def) 
  apply (wp | simp)+ 
 done

(* FIXME - Move Invariants_AI *)
lemma invs_exst [iff]:
  "invs (trans_state f s) = invs s"
  by (simp add: invs_def valid_state_def)

lemma stt_invs [wp]:
  "\<lbrace>invs\<rbrace> switch_to_thread t' \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply wp
     apply (simp add: trans_state_update[symmetric] del: trans_state_update)
    apply (rule_tac Q="\<lambda>_. invs and tcb_at t'" in hoare_strengthen_post, wp)
    apply (clarsimp simp: invs_def valid_state_def valid_idle_def
                          valid_irq_node_def valid_machine_state_def)
    apply (fastforce simp: cur_tcb_def obj_at_def
                     elim: valid_pspace_eqI ifunsafe_pspaceI)
   apply wp
  apply clarsimp
  apply (simp add: is_tcb_def)
  done

abbreviation
  "activatable \<equiv> \<lambda>st. runnable st \<or> idle st"

context begin interpretation Arch . (*FIXME: arch_split*)
lemma arch_stt_runnable:
  "\<lbrace>st_tcb_at runnable t\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>r . st_tcb_at runnable t\<rbrace>"
  apply (simp add: arch_switch_to_thread_def)
  apply wp
  done
end

lemma stt_activatable:
  "\<lbrace>st_tcb_at runnable t\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wp | simp add: ct_in_state_def)+
    apply (rule hoare_post_imp [OF _ arch_stt_runnable])
    apply (clarsimp elim!: pred_tcb_weakenE)
   apply (rule assert_inv)
  apply wp
  done


lemma invs_upd_cur_valid:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. invs\<rbrace>; \<lbrace>Q\<rbrace> f \<lbrace>\<lambda>rv. tcb_at thread\<rbrace>\<rbrakk>
    \<Longrightarrow> \<lbrace>P and Q\<rbrace> f \<lbrace>\<lambda>rv s. invs (s\<lparr>cur_thread := thread\<rparr>)\<rbrace>"
  by (fastforce simp: valid_def invs_def valid_state_def cur_tcb_def valid_machine_state_def)

context begin interpretation Arch . (*FIXME: arch_split*)
lemma stit_invs [wp]:
  "\<lbrace>invs\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply wp
    apply (rule invs_upd_cur_valid)
     apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_idle_def pred_tcb_at_tcb_at)
  apply (clarsimp simp: in_user_frame_def valid_arch_state_def)
  apply (rule_tac x=ARMSmallPage in exI)
  apply (clarsimp simp: obj_at_def)
  apply (drule_tac addr="arm_globals_frame (arch_state s)" in valid_pspace_aligned, simp)
  apply (drule is_aligned_neg_mask_eq, simp add: a_type_def)
  done
end

(* FIXME move *)
lemma pred_tcb_weaken_strongerE:
  "\<lbrakk> pred_tcb_at proj P t s; \<And>tcb . P (proj tcb) \<Longrightarrow> P' (proj' tcb) \<rbrakk> \<Longrightarrow> pred_tcb_at proj' P' t s"
  by (auto simp: pred_tcb_at_def elim: obj_at_weakenE)

context begin interpretation Arch . (* FIXME: arch_split*)
lemma stit_activatable:
  "\<lbrace>invs\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . ct_in_state activatable\<rbrace>"
  apply (simp add: switch_to_idle_thread_def arch_switch_to_idle_thread_def)
  apply (wp | simp add: ct_in_state_def)+
  apply (clarsimp simp: invs_def valid_state_def cur_tcb_def valid_idle_def
                 elim!: pred_tcb_weaken_strongerE)
  done
end

lemma OR_choice_weak_wp:
  "\<lbrace>P\<rbrace> f \<sqinter> g \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> OR_choice b f g \<lbrace>Q\<rbrace>"
  apply (fastforce simp add: OR_choice_def alternative_def valid_def bind_def
                    select_f_def gets_def return_def get_def
          split: option.splits split_if_asm)
  done

lemma schedule_invs[wp]: "\<lbrace>invs\<rbrace> (Schedule_A.schedule :: (unit,unit) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: Schedule_A.schedule_def allActiveTCBs_def)
  apply (wp OR_choice_weak_wp alternative_wp dmo_invs thread_get_inv
            do_machine_op_tcb select_ext_weak_wp select_wp when_def
          | clarsimp simp: getActiveTCB_def get_tcb_def)+
  done

(* FIXME - move *)
lemma get_tcb_exst_update:
  "get_tcb p (trans_state f s) = get_tcb p s"
  by (simp add: get_tcb_def)

lemma ct_in_state_trans_update[simp]: "ct_in_state st (trans_state f s) = ct_in_state st s"
  apply (simp add: ct_in_state_def)
  done

lemma schedule_ct_activateable[wp]:
  "\<lbrace>invs\<rbrace> (Schedule_A.schedule :: (unit,unit) s_monad) \<lbrace>\<lambda>rv. ct_in_state activatable\<rbrace>"
  proof -
  have P: "\<And>t s. ct_in_state activatable (cur_thread_update (\<lambda>_. t) s) = st_tcb_at activatable t s"
    by (fastforce simp: ct_in_state_def pred_tcb_at_def intro: obj_at_pspaceI)
  show ?thesis
    apply (simp add: Schedule_A.schedule_def allActiveTCBs_def)
    apply (wp alternative_wp
              select_ext_weak_wp select_wp stt_activatable stit_activatable
               | simp add: P)+
    apply (clarsimp simp: getActiveTCB_def ct_in_state_def)
    apply (rule conjI)
     apply clarsimp
     apply (case_tac "get_tcb (cur_thread s) s", simp_all add: ct_in_state_def)
     apply (drule get_tcb_SomeD)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def split: split_if_asm)
    apply (case_tac "get_tcb x s", simp_all)
    apply (drule get_tcb_SomeD)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def split: split_if_asm)
    done
qed

end
