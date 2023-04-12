(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_AI
imports VSpace_AI
begin

abbreviation
  "activatable \<equiv> \<lambda>st. runnable st \<or> idle st"


locale Schedule_AI =
    fixes state_ext :: "('a::state_ext) itself"
    assumes dmo_mapM_storeWord_0_invs[wp]:
      "\<And>S. valid invs (do_machine_op (mapM (\<lambda>p. storeWord p 0) S)) (\<lambda>_. (invs :: 'a state \<Rightarrow> bool))"
    assumes arch_stt_invs [wp]:
      "\<And>t'. \<lbrace>invs\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. (invs :: 'a state \<Rightarrow> bool)\<rbrace>"
    assumes arch_stt_tcb [wp]:
      "\<And>t'. \<lbrace>tcb_at t'\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. (tcb_at t' :: 'a state \<Rightarrow> bool)\<rbrace>"
    assumes arch_stt_runnable:
      "\<And>t. \<lbrace>st_tcb_at runnable t\<rbrace> arch_switch_to_thread t \<lbrace>\<lambda>r . (st_tcb_at runnable t :: 'a state \<Rightarrow> bool)\<rbrace>"
    assumes stit_invs [wp]:
      "\<lbrace>invs\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv. (invs :: 'a state \<Rightarrow> bool)\<rbrace>"
    assumes stit_activatable:
      "\<lbrace>invs\<rbrace> switch_to_idle_thread \<lbrace>\<lambda>rv . (ct_in_state activatable :: 'a state \<Rightarrow> bool)\<rbrace>"

context begin interpretation Arch .
(* FIXME arch_split: some of these could be moved to generic theories
   so they don't need to be unqualified. *)
requalify_facts
  no_irq
  no_irq_storeWord
end

crunch inv[wp]: schedule_switch_thread_fastfail P

lemma findM_inv'':
  assumes p: "suffix xs xs'"
  assumes x: "\<And>x xs. suffix (x # xs) xs' \<Longrightarrow> \<lbrace>P (x # xs)\<rbrace> m x \<lbrace>\<lambda>rv s. (rv \<longrightarrow> Q s) \<and> (\<not> rv \<longrightarrow> P xs s)\<rbrace>"
  assumes y: "\<And>s. P [] s \<Longrightarrow> Q s"
  shows      "\<lbrace>P xs\<rbrace> findM m xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  using p
  apply (induct xs)
   apply simp
   apply wp
   apply (erule y)
  apply (frule suffix_ConsD)
  apply simp
  apply wp
   apply (erule x)
  apply simp
  done

lemmas findM_inv' = findM_inv''[OF suffix_order.refl]

lemma findM_inv:
  assumes x: "\<And>x. \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> findM m xs \<lbrace>\<lambda>rv. P\<rbrace>"
  by (rule findM_inv', simp_all add: x)


lemma allActiveTCBs_gets:
  "allActiveTCBs = gets (\<lambda>state. {x. getActiveTCB x state \<noteq> None})"
  by (simp add: allActiveTCBs_def gets_def)


lemma postfix_tails:
  "\<lbrakk> suffix (xs # ys) (tails zs) \<rbrakk>
     \<Longrightarrow> suffix xs zs \<and> (xs # ys) = tails xs"
  apply (induct zs arbitrary: xs ys)
   apply (clarsimp elim!: suffixE)
   apply (case_tac zs, simp_all)[1]
  apply (clarsimp elim!: suffixE)
  apply (case_tac zsa, simp_all)
   apply clarsimp
  apply clarsimp
  apply (erule meta_allE, erule meta_allE, drule meta_mp,
         rule suffix_appendI[OF suffix_order.refl])
  apply clarsimp
  apply (erule suffix_ConsI)
  done


lemma valid_irq_states_cur_thread_update[simp]:
  "valid_irq_states (cur_thread_update f s) = valid_irq_states s"
  by(simp add: valid_irq_states_def)

lemma sct_invs:
  "\<lbrace>invs and tcb_at t\<rbrace> modify (cur_thread_update (%_. t)) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply wp
  apply (clarsimp simp add: invs_def cur_tcb_def valid_state_def valid_idle_def
                            valid_irq_node_def valid_machine_state_def)
  sorry (* -scottb *)

lemma storeWord_valid_irq_states:
  "\<lbrace>\<lambda>m. valid_irq_states (s\<lparr>machine_state := m\<rparr>)\<rbrace> storeWord x y
   \<lbrace>\<lambda>a b. valid_irq_states (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  apply (simp add: valid_irq_states_def | wp no_irq | simp add: no_irq_storeWord)+
  done

lemma dmo_storeWord_valid_irq_states[wp]:
  "\<lbrace>valid_irq_states\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>_. valid_irq_states\<rbrace>"
  apply (simp add: do_machine_op_def |  wp | wpc)+
  apply clarsimp
  apply(erule use_valid[OF _ storeWord_valid_irq_states])
  by simp

lemma dmo_kheap_arch_state[wp]:
  "\<lbrace>\<lambda>s. P (kheap s) (arch_state s)\<rbrace>
   do_machine_op a
   \<lbrace>\<lambda>_ s. P (kheap s) (arch_state s)\<rbrace>"
  by (clarsimp simp: do_machine_op_def simpler_gets_def select_f_def
          simpler_modify_def return_def bind_def valid_def)

lemmas do_machine_op_tcb[wp] =
  do_machine_op_obj_at[where P=id and Q=is_tcb, simplified]

lemma (in Schedule_AI) stt_tcb [wp]:
  "\<lbrace>tcb_at t\<rbrace> switch_to_thread t \<lbrace>\<lambda>_. (tcb_at t :: 'a state \<Rightarrow> bool)\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wp touch_object_wp' | simp)+
  done

lemma (in Schedule_AI) stt_invs [wp]:
  "\<lbrace>invs :: 'a state \<Rightarrow> bool\<rbrace> switch_to_thread t' \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply wp
     apply (simp add: trans_state_update[symmetric] del: trans_state_update)
    apply (rule_tac Q="\<lambda>_. invs and tcb_at t'" in hoare_strengthen_post, wp)
    apply (clarsimp simp: invs_def valid_state_def valid_idle_def
                          valid_irq_node_def valid_machine_state_def)
    apply (fastforce simp: cur_tcb_def obj_at_def
                     elim: valid_pspace_eqI ifunsafe_pspaceI)
   apply (wp touch_object_wp')+
  apply clarsimp
  sorry (* broken by touched-addrs -scottb
  apply (simp add: is_tcb_def)
  done *)

lemma (in Schedule_AI) stt_activatable:
  "\<lbrace>st_tcb_at runnable t\<rbrace> switch_to_thread t \<lbrace>\<lambda>rv . (ct_in_state activatable :: 'a state \<Rightarrow> bool) \<rbrace>"
  apply (simp add: switch_to_thread_def)
  apply (wp | simp add: ct_in_state_def)+
     apply (rule hoare_post_imp [OF _ arch_stt_runnable])
     apply (clarsimp elim!: pred_tcb_weakenE)
    apply (rule assert_inv)
   apply (wp touch_object_wp')
  sorry (* broken by touched-addrs -scottb
  apply assumption
  done *)


lemma invs_upd_cur_valid:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. invs\<rbrace>; \<lbrace>Q\<rbrace> f \<lbrace>\<lambda>rv. tcb_at thread\<rbrace>\<rbrakk>
    \<Longrightarrow> \<lbrace>P and Q\<rbrace> f \<lbrace>\<lambda>rv s. invs (s\<lparr>cur_thread := thread\<rparr>)\<rbrace>"
  by (fastforce simp: valid_def invs_def valid_state_def cur_tcb_def valid_machine_state_def)


(* FIXME move *)
lemma pred_tcb_weaken_strongerE:
  "\<lbrakk> pred_tcb_at proj P t s; \<And>tcb . P (proj tcb) \<Longrightarrow> P' (proj' tcb) \<rbrakk> \<Longrightarrow> pred_tcb_at proj' P' t s"
  by (auto simp: pred_tcb_at_def elim: obj_at_weakenE)

lemma OR_choice_weak_wp:
  "\<lbrace>P\<rbrace> f \<sqinter> g \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> OR_choice b f g \<lbrace>Q\<rbrace>"
  apply (fastforce simp add: OR_choice_def alternative_def valid_def bind_def
                    select_f_def gets_def return_def get_def
          split: option.splits if_split_asm)
  done

locale Schedule_AI_U = Schedule_AI "TYPE(unit)"

lemma (in Schedule_AI_U) schedule_invs[wp]:
  "\<lbrace>invs\<rbrace> (Schedule_A.schedule :: (unit,unit) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: Schedule_A.schedule_def allActiveTCBs_def)
  apply (wp OR_choice_weak_wp alternative_wp dmo_invs thread_get_inv
            do_machine_op_tcb select_ext_weak_wp select_wp when_def
            touch_objects_wp
          | clarsimp simp: getActiveTCB_def get_tcb_def)+
  done

(* FIXME - move *)
lemma get_tcb_exst_update:
  "get_tcb False p (trans_state f s) = get_tcb False p s"
  by (simp add: get_tcb_def)

lemma ct_in_state_trans_update[simp]: "ct_in_state st (trans_state f s) = ct_in_state st s"
  apply (simp add: ct_in_state_def)
  done

lemma (in Schedule_AI_U) schedule_ct_activateable[wp]:
  "\<lbrace>invs\<rbrace> (Schedule_A.schedule :: (unit,unit) s_monad) \<lbrace>\<lambda>rv. ct_in_state activatable \<rbrace>"
  proof -
  have P: "\<And>t s. ct_in_state activatable (cur_thread_update (\<lambda>_. t) s) = st_tcb_at activatable t s"
    by (fastforce simp: ct_in_state_def pred_tcb_at_def intro: obj_at_pspaceI)
  have Q: "\<And>s. invs s \<longrightarrow> idle_thread s = cur_thread s \<longrightarrow> ct_in_state activatable s"
    apply (clarsimp simp: ct_in_state_def dest!: invs_valid_idle)
    apply (clarsimp simp: valid_idle_def pred_tcb_def2)
    done
  show ?thesis
    apply (simp add: Schedule_A.schedule_def allActiveTCBs_def)
    apply (wp alternative_wp
              select_ext_weak_wp select_wp stt_activatable stit_activatable
              touch_objects_wp
               | simp add: P Q)+
    apply (clarsimp simp: getActiveTCB_def ct_in_state_def)
    apply (rule conjI)
     apply clarsimp
     apply (case_tac "get_tcb False (cur_thread s) s", simp_all add: ct_in_state_def)
     apply (drule get_tcb_SomeD)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def split: if_split_asm)
    apply (case_tac "get_tcb False x s", simp_all)
    apply (drule get_tcb_SomeD)
    apply (clarsimp simp: pred_tcb_at_def obj_at_def split: if_split_asm)
    done
qed

end
