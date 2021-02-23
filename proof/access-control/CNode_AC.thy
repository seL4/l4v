(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CNode_AC
imports ArchAccess_AC
begin

context begin interpretation Arch . (*FIXME: arch_split*)

declare arch_post_modify_registers_def[simp]
declare arch_post_cap_deletion_def[simp]
declare arch_cap_cleanup_opt_def[simp]
declare arch_mask_irq_signal_def[simp]
declare arch_integrity_subjects_def[simp]

(* FIXME: arch-split *)
lemmas post_cap_deletion_simps[simp] = post_cap_deletion_def[simplified arch_post_cap_deletion_def]
                                       cap_cleanup_opt_def[simplified arch_cap_cleanup_opt_def]

(* FIXME: Move. *)
lemma tcb_domain_map_wellformed_ekheap[intro!, simp]:
  "ekheap (P s) = ekheap s \<Longrightarrow> tcb_domain_map_wellformed aag (P s) = tcb_domain_map_wellformed aag s"
by (simp add: tcb_domain_map_wellformed_aux_def get_etcb_def)


section\<open>CNode-specific AC.\<close>

lemma set_original_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst slot))\<rbrace>
      set_original slot orig \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: set_original_def)
  apply wp
  apply (simp add: integrity_def)
  apply (clarsimp intro!: integrity_cdt_direct)
  done

lemma set_original_integrity:
  "\<lbrace>integrity aag X st and cdt_change_allowed' aag slot\<rbrace>
      set_original slot orig
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  by integrity_trans_start (wpsimp simp: set_original_def integrity_def)


lemma update_cdt_fun_upd_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst slot))\<rbrace>
      update_cdt (\<lambda>cdt. cdt (slot := v cdt)) \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: update_cdt_def set_cdt_def)
  apply wp
  apply (simp add: integrity_def)
  apply (clarsimp intro!: integrity_cdt_direct)
  done

(* FIXME: for some reason crunch does not discover the right precondition *)
lemma set_cap_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst slot))\<rbrace> set_cap cap slot \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding set_cap_def
  apply (rule hoare_pre)
   apply (wp set_object_integrity_autarch get_object_wp | wpc)+
  apply clarsimp
  done

lemma integrity_cdt_list_as_list_integ:
  "cdt_list_integrity_state aag st s =
       (list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st s)"
  apply (rule iffI)
  apply (fastforce elim!: integrity_cdt_listE  intro: list_integI)
  apply (fastforce elim!:list_integE  intro: integrity_cdt_list_intros)
  done

end

context is_extended begin

interpretation Arch . (*FIXME: arch_split*)

lemma list_integ_lift:
  assumes li:
   "\<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
       f
    \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag}  (cdt st) (tcb_states_of_state st)) st\<rbrace>"
  assumes ekh: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  assumes rq: "\<And>P. \<lbrace> \<lambda>s. P (ready_queues s) \<rbrace> f \<lbrace> \<lambda>rv s. P (ready_queues s) \<rbrace>"
  shows "\<lbrace>integrity aag X st and Q\<rbrace> f \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_pre)
   apply (unfold integrity_def[abs_def])
   apply (simp only: integrity_cdt_list_as_list_integ)
   apply (rule hoare_lift_Pf2[where f="ekheap"])
    apply (simp add: tcb_states_of_state_def get_tcb_def)
    apply (wp li[simplified tcb_states_of_state_def get_tcb_def] ekh rq)+
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (simp add: tcb_states_of_state_def get_tcb_def)
  done

end

context begin interpretation Arch . (*FIXME: arch_split*)

crunch ekheap[wp]: cap_swap_ext,cap_move_ext,empty_slot_ext "\<lambda>s. P (ekheap s)"

crunch ready_queues[wp]: cap_swap_ext,cap_move_ext,empty_slot_ext "\<lambda>s. P (ready_queues s)"

crunch integrity_autarch: set_untyped_cap_as_full "integrity aag X st"
  (simp: crunch_simps wp: crunch_wps update_cdt_fun_upd_integrity_autarch
         cap_insert_ext_extended.list_integ_lift cap_insert_list_integrity
   ignore:update_cdt)

lemma cap_insert_integrity_autarch:
  "\<lbrace>integrity aag X st and
     K (is_subject aag (fst src_slot) \<and> is_subject aag (fst dest_slot))\<rbrace>
   cap_insert cap src_slot dest_slot
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add:cap_insert_def)
  apply (wp set_original_integrity_autarch cap_insert_ext_extended.list_integ_lift
            cap_insert_list_integrity update_cdt_fun_upd_integrity_autarch gets_inv
            set_cap_integrity_autarch set_untyped_cap_as_full_integrity_autarch assert_inv)
  apply fastforce
  done

text\<open>

Establish that the pointers this syscall will change are labelled with
the current agent's label.

NOTE: @{term "(\<subseteq>)"} is used consciously here to block the simplifier
rewriting (the equivalent equalities) in the wp proofs.

\<close>

definition
  authorised_cnode_inv :: "'a PAS \<Rightarrow> Invocations_A.cnode_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "authorised_cnode_inv aag ci \<equiv> K (case ci of
    InsertCall cap ptr ptr' \<Rightarrow> pasObjectAbs aag ` {fst ptr, fst ptr'} \<subseteq> {pasSubject aag}
  | MoveCall cap ptr ptr' \<Rightarrow> pasObjectAbs aag ` {fst ptr, fst ptr'} \<subseteq> {pasSubject aag}
  | RotateCall s_cap p_cap src pivot dest \<Rightarrow>
                           pasObjectAbs aag ` {fst src, fst pivot, fst dest} \<subseteq> {pasSubject aag}
  | SaveCall ptr \<Rightarrow> is_subject aag (fst ptr)
  | DeleteCall ptr \<Rightarrow> is_subject aag (fst ptr)
  | CancelBadgedSendsCall cap \<Rightarrow> pas_cap_cur_auth aag cap
  | RevokeCall ptr \<Rightarrow> is_subject aag (fst ptr))"

lemma resolve_address_bits_authorised_aux:
  "s \<turnstile> \<lbrace>pas_refined aag and K (is_cnode_cap (fst (cap, cref))
                               \<longrightarrow> (\<forall>x \<in> obj_refs (fst (cap, cref)). is_subject aag x))\<rbrace>
         resolve_address_bits (cap, cref)
       \<lbrace>\<lambda>rv s. is_subject aag (fst (fst rv))\<rbrace>, \<lbrace>\<lambda>rv. \<top>\<rbrace>"
unfolding resolve_address_bits_def
proof (induct arbitrary: s rule: resolve_address_bits'.induct)
  case (1 z cap' cref' s')
  have P: "\<And>s f P Q. s \<turnstile> \<lbrace>P\<rbrace> throwError f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s. True\<rbrace>"
    by wp+
  show ?case
    apply (subst resolve_address_bits'.simps)
    apply (cases cap', simp_all add: P split del: if_split)
    apply (rule hoare_pre_spec_validE)
     apply (wp "1.hyps", (assumption | simp add: in_monad | rule conjI)+)
          apply (wp get_cap_wp)+
    apply (auto simp: cte_wp_at_caps_of_state is_cap_simps cap_auth_conferred_def
                dest: caps_of_state_pasObjectAbs_eq)
    done
qed

lemma resolve_address_bits_authorised[wp]:
  "\<lbrace>pas_refined aag and K (is_cnode_cap cap \<longrightarrow> (\<forall>x \<in> obj_refs cap. is_subject aag x))\<rbrace>
    resolve_address_bits (cap, cref)
   \<lbrace>\<lambda>rv s. is_subject aag (fst (fst rv))\<rbrace>, -"
  apply (unfold validE_R_def)
  apply (rule hoare_pre)
  apply (rule use_spec(2)[OF resolve_address_bits_authorised_aux])
  apply simp
  done

lemma lookup_slot_for_cnode_op_authorised[wp]:
  "\<lbrace>pas_refined aag and K (is_cnode_cap croot \<longrightarrow> (\<forall>x \<in> obj_refs croot. is_subject aag x))\<rbrace>
    lookup_slot_for_cnode_op is_source croot ptr depth
   \<lbrace>\<lambda>rv s. is_subject aag (fst rv)\<rbrace>, -"
  apply (simp add: lookup_slot_for_cnode_op_def split del: if_split)
  apply (rule hoare_pre)
  apply (wp whenE_throwError_wp hoare_drop_imps
            resolve_address_bits_authorised[THEN hoare_post_imp_R[where Q'="\<lambda>x s. is_subject aag (fst (fst x))"]]
       | wpc
       | simp add: split_def authorised_cnode_inv_def split del: if_split
              del: split_paired_All | clarsimp)+
  done

(* MOVE *)
lemma is_cnode_into_is_subject:
  "\<lbrakk> pas_cap_cur_auth aag cap; pas_refined aag s \<rbrakk> \<Longrightarrow> is_cnode_cap cap \<longrightarrow> (\<forall>x\<in>obj_refs cap. is_subject aag x)"
  by (clarsimp simp: is_cap_simps cap_auth_conferred_def
                     pas_refined_all_auth_is_owns aag_cap_auth_def)

lemma get_cap_prop_imp:
  "\<lbrace>cte_wp_at (\<lambda>cap. P cap \<longrightarrow> Q cap) slot\<rbrace>
       get_cap slot \<lbrace>\<lambda>rv s. P rv \<longrightarrow> cte_wp_at Q slot s\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma get_cap_prop_imp2:
  "\<lbrace>cte_wp_at (\<lambda>cap. P cap) slot\<rbrace> get_cap slot \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (rule hoare_pre)
   apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma get_cap_cur_auth:
  "\<lbrace>pas_refined aag and cte_wp_at (\<lambda>_. True) slot and K (is_subject aag (fst slot))\<rbrace> get_cap slot \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag rv\<rbrace>"
  apply (rule hoare_pre)
   apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state cap_cur_auth_caps_of_state)
  done

lemma decode_cnode_inv_authorised:
  "\<lbrace>pas_refined aag and invs and valid_cap cap and K (\<forall>c \<in> {cap} \<union> set excaps. pas_cap_cur_auth aag c)\<rbrace>
     decode_cnode_invocation label args cap excaps
   \<lbrace>\<lambda>rv s. authorised_cnode_inv aag rv s\<rbrace>,-"
  apply (simp add: authorised_cnode_inv_def decode_cnode_invocation_def split_def whenE_def unlessE_def set_eq_iff
                 cong: if_cong Invocations_A.cnode_invocation.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
              lsfco_cte_at
        | simp only: simp_thms if_simps fst_conv snd_conv Invocations_A.cnode_invocation.simps K_def
        | wpc
        | wp (once) get_cap_cur_auth)+
  apply clarsimp
  apply (frule is_cnode_into_is_subject [rotated], fastforce)
  apply simp
  apply (subgoal_tac "\<forall>n. n < length excaps \<longrightarrow> (is_cnode_cap (excaps ! n) \<longrightarrow> (\<forall>x\<in>obj_refs (excaps ! n). is_subject aag x))")
   apply (frule spec [where x = 0])
   apply (drule spec [where x = 1])
   apply (clarsimp simp: invs_valid_objs)
   apply (drule (1) mp [OF _ length_ineq_not_Nil(1)], erule (1) bspec) (* yuck *)
  apply (rule allI, rule impI)
  apply (rule is_cnode_into_is_subject)
   apply fastforce
  apply assumption
  done

lemma set_cap_state_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> set_cap cap ptr \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def)
  apply (wp get_object_wp | wpc)+
  apply (auto simp: obj_at_def state_vrefs_def
             elim!: rsubst[where P=P, OF _ ext]
             split: if_split_asm simp: vs_refs_no_global_pts_def)
  done

lemma set_cap_thread_states[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> set_cap cap ptr \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: obj_at_def | rule conjI
           | erule rsubst[where P=P, OF _ ext]
           | clarsimp simp: thread_states_def get_tcb_def tcb_states_of_state_def)+
  done

lemma set_cap_tcb_states_of_state[wp]:
  "\<lbrace> \<lambda>s. P (tcb_states_of_state s) \<rbrace> set_cap cap ptr \<lbrace> \<lambda>rv s. P (tcb_states_of_state s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: obj_at_def get_tcb_def tcb_states_of_state_def | rule conjI
           | erule rsubst[where P=P, OF _ ext])+
  done

lemma set_cap_thread_bound_ntfns[wp]:
  "\<lbrace> \<lambda>s. P (thread_bound_ntfns s) \<rbrace> set_cap cap ptr \<lbrace> \<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: obj_at_def get_tcb_def thread_bound_ntfns_def | rule conjI
           | erule rsubst[where P=P, OF _ ext])+
  done

lemma sita_caps_update:
  "\<lbrakk> pas_wellformed aag;
    state_irqs_to_policy_aux aag caps \<subseteq> pasPolicy aag;
    cap_links_irq aag (pasObjectAbs aag (fst ptr)) cap \<rbrakk> \<Longrightarrow>
    state_irqs_to_policy_aux aag (caps(ptr \<mapsto> cap))  \<subseteq> pasPolicy aag"
  apply clarsimp
  apply (erule state_irqs_to_policy_aux.cases)
  apply (fastforce intro: state_irqs_to_policy_aux.intros simp: cap_links_irq_def split: if_split_asm)+
  done

lemma sita_caps_update2:
  "\<lbrakk> pas_wellformed aag;
    state_irqs_to_policy_aux aag caps \<subseteq> pasPolicy aag;
    cap_links_irq aag (pasObjectAbs aag (fst ptr')) cap';
    cap_links_irq aag (pasObjectAbs aag (fst ptr)) cap \<rbrakk> \<Longrightarrow>
    state_irqs_to_policy_aux aag (caps(ptr \<mapsto> cap, ptr' \<mapsto> cap'))  \<subseteq> pasPolicy aag"
  apply clarsimp
  apply (erule state_irqs_to_policy_aux.cases)
  apply (fastforce intro: state_irqs_to_policy_aux.intros simp: cap_links_irq_def split: if_split_asm)+
  done

lemma sata_update:
  "\<lbrakk> pas_wellformed aag;
     state_asids_to_policy_aux aag (caps_of_state s) asid_tab vrefs \<subseteq> pasPolicy aag;
     cap_links_asid_slot aag (pasObjectAbs aag (fst ptr)) cap \<rbrakk> \<Longrightarrow>
     state_asids_to_policy_aux aag ((caps_of_state s) (ptr \<mapsto> cap)) asid_tab vrefs \<subseteq> pasPolicy aag"
  apply clarsimp
  apply (erule state_asids_to_policy_aux.cases)
  apply (fastforce intro: state_asids_to_policy_aux.intros simp: cap_links_asid_slot_def label_owns_asid_slot_def split: if_split_asm)+
  done

lemma sata_update2:
  "\<lbrakk> pas_wellformed aag;
     state_asids_to_policy_aux aag (caps_of_state s) asid_tab vrefs \<subseteq> pasPolicy aag;
     cap_links_asid_slot aag (pasObjectAbs aag (fst ptr)) cap ;
     cap_links_asid_slot aag (pasObjectAbs aag (fst ptr')) cap' \<rbrakk> \<Longrightarrow>
     state_asids_to_policy_aux aag ((caps_of_state s) (ptr \<mapsto> cap,ptr' \<mapsto> cap')) asid_tab vrefs \<subseteq> pasPolicy aag"
  apply clarsimp
  apply (erule state_asids_to_policy_aux.cases)
  apply (fastforce intro: state_asids_to_policy_aux.intros simp: cap_links_asid_slot_def label_owns_asid_slot_def split: if_split_asm)+
  done

lemma cli_caps_of_state:
  "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk> \<Longrightarrow> cap_links_irq aag (pasObjectAbs aag (fst slot)) cap"
apply (clarsimp simp add: cap_links_irq_def pas_refined_def)
apply (blast dest: state_irqs_to_policy_aux.intros)
done

lemma set_object_caps_of_state:
  "\<lbrace>(\<lambda>s. \<not>(tcb_at p s) \<and> \<not>(\<exists>n. cap_table_at n p s)) and
    K ((\<forall>x y. obj \<noteq> CNode x y) \<and> (\<forall>x. obj \<noteq> TCB x)) and
    (\<lambda>s. P (caps_of_state s))\<rbrace>
   set_object p obj
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (simp add: caps_of_state_cte_wp_at obj_at_def is_cap_table_def
                   is_tcb_def)
  apply (auto simp: cte_wp_at_cases)
  done

lemma set_object_domains_of_state[wp]:
  "\<lbrace> \<lambda>s. P (domains_of_state s) \<rbrace> set_object a b \<lbrace> \<lambda>_ s. P (domains_of_state s) \<rbrace>"
  by (wpsimp wp: set_object_wp)

lemma set_cap_pas_refined:
  "\<lbrace>pas_refined aag and (\<lambda>s. (is_transferable_in ptr s \<and> (\<not> Option.is_none (cdt s ptr)))
          \<longrightarrow> is_transferable_cap cap
            \<or> (pasObjectAbs aag (fst $ the $ cdt s ptr), Control, pasObjectAbs aag (fst ptr))
                                                                                    \<in> pasPolicy aag)
         and K (aag_cap_auth aag (pasObjectAbs aag (fst ptr)) cap)\<rbrace>
      set_cap cap ptr
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def aag_cap_auth_def)
  apply (rule hoare_pre)
   apply (wp set_cap_caps_of_state| wps)+
  apply clarsimp
  apply (intro conjI)  \<comment> \<open>auth_graph_map\<close>
   apply (clarsimp dest!: auth_graph_map_memD)
   apply (erule state_bits_to_policy.cases;
          solves\<open>auto simp: cap_links_asid_slot_def label_owns_asid_slot_def
                     intro: auth_graph_map_memI state_bits_to_policy.intros
                     split: if_split_asm\<close>)
  apply (erule (2) sata_update[unfolded fun_upd_def])
  apply (erule (2) sita_caps_update[unfolded fun_upd_def])
  done

lemma set_cap_pas_refined_not_transferable:
  "\<lbrace>pas_refined aag and cte_wp_at (\<lambda>c. \<not>is_transferable (Some c)) ptr
       and K (aag_cap_auth aag (pasObjectAbs aag (fst ptr)) cap)\<rbrace>
      set_cap cap ptr
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_pre)
  apply (rule set_cap_pas_refined)
  by (fastforce simp: cte_wp_at_caps_of_state)



(* FIXME MOVE *)
lemma parent_ofI[intro!]: "m x = Some src \<Longrightarrow> m \<Turnstile> src \<leadsto> x"
  by (simp add: cdt_parent_rel_def is_cdt_parent_def)

declare set_original_wp[wp del]

lemma cap_move_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and  K (is_subject aag (fst dest) \<and> is_subject aag (fst src))\<rbrace>
       cap_move cap src dest \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm) apply (elim conjE)
  apply (simp add: cap_move_def)
  apply (rule hoare_pre)
   apply (wp add: get_cap_wp set_cap_integrity_autarch set_original_integrity_autarch
             cap_move_ext.list_integ_lift[where Q="\<top>"] cap_move_list_integrity
             | simp add: set_cdt_def split del: if_split | blast)+
    apply (rule wp_integrity_clean')
     apply (simp add: integrity_def del:split_paired_All)
     apply (simp add:integrity_cdt_def) apply (blast intro: cca_owned)
    apply (wp set_cap_integrity_autarch| simp)+
  done

lemma integrity_cdt_fun_upd:
  "\<lbrakk> integrity aag X st (cdt_update f s); is_subject aag (fst slot) \<rbrakk>
       \<Longrightarrow> integrity aag X st (cdt_update (\<lambda>cdt. (f cdt) (slot := v cdt)) s)"
  apply (simp add: integrity_def integrity_cdt_def del:split_paired_All)
  oops

lemma cap_swap_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and
               K (is_subject aag (fst slot) \<and> is_subject aag (fst slot'))\<rbrace>
       cap_swap cap slot cap' slot' \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cap_swap_def)
  apply (wp get_cap_wp set_cap_integrity_autarch
            cap_swap_ext_extended.list_integ_lift[where Q="\<top>"] cap_swap_list_integrity
            set_original_integrity_autarch[unfolded pred_conj_def K_def]
         | simp add: set_cdt_def split del: if_split | blast)+
    apply (rule wp_integrity_clean')
     (* 5s clarsimp *)
     apply (clarsimp simp add: integrity_def)
     apply (blast intro: cca_owned)
    apply (wp set_cap_integrity_autarch set_cap_pas_refined
           | simp | simp_all)+
  done

lemma cap_swap_for_delete_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag
            and K (is_subject aag (fst slot) \<and> is_subject aag (fst slot'))\<rbrace>
      cap_swap_for_delete slot slot'
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp | simp)+
  done

lemma dmo_no_mem_respects:
  assumes p: "\<And>P. \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace> mop \<lbrace>\<lambda>_ ms. P (underlying_memory ms)\<rbrace>"
  assumes q: "\<And>P. \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> mop \<lbrace>\<lambda>_ ms. P (device_state ms)\<rbrace>"
  shows "\<lbrace>integrity aag X st\<rbrace> do_machine_op mop \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding do_machine_op_def
  apply (rule hoare_pre)
  apply (simp add: split_def)
  apply (wp )
  apply (clarsimp simp: integrity_def)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x = x in spec)+
   apply (erule (1) use_valid [OF _ p])
  apply clarsimp
  apply (drule_tac x = x in spec)+
  apply (erule (1) use_valid [OF _ q])
  done

(* FIXME: MOVE *)
(* Only works after a hoare_pre! *)
lemma dmo_wp:
  assumes mopv: "\<And>s. \<lbrace>P s\<rbrace> mop \<lbrace>\<lambda>a b. R a (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P s (machine_state s)\<rbrace> do_machine_op mop \<lbrace>R\<rbrace>"
  unfolding do_machine_op_def
  apply (simp add: split_def)
  apply (wp)
  apply clarsimp
  apply (erule use_valid [OF _ mopv])
  apply simp
  done

lemma set_irq_state_respects[wp]:
  "\<lbrace> integrity aag X st and K (is_subject_irq aag irq) \<rbrace>
   set_irq_state irqst irq
   \<lbrace> \<lambda>_. integrity aag X st \<rbrace>"
  unfolding set_irq_state_def
  apply (wp dmo_no_mem_respects | simp add: maskInterrupt_def)+
  apply (clarsimp simp: integrity_subjects_def integrity_interrupts_def)
  done

crunch respects[wp]: deleted_irq_handler "integrity aag X st"

lemmas cases_simp_options
    = cases_simp_option cases_simp_option[where 'a="'b \<times> 'c", simplified]

(* FIXME MOVE *)
lemma cdt_change_allowed_all_children:
 "all_children (cdt_change_allowed aag subject (cdt s) (tcb_states_of_state s)) (cdt s)"
  by (rule all_childrenI) (erule cdt_change_allowed_to_child)


abbreviation cleanup_info_wf :: "cap \<Rightarrow> 'a PAS \<Rightarrow> bool"
where
  "cleanup_info_wf c aag \<equiv> c \<noteq> NullCap \<longrightarrow> (\<exists>irq. c = (IRQHandlerCap irq) \<and> is_subject_irq aag irq)"

(* FIXME: MOVE *)
named_theorems wp_transferable
named_theorems wp_not_transferable

lemma empty_slot_integrity_spec:
  notes split_paired_All[simp del]
  shows
  "s \<turnstile> \<lbrace>valid_list and valid_mdb and valid_objs and pas_refined aag and
            K (is_subject aag (fst slot) \<and> cleanup_info_wf cleanup_info aag)\<rbrace>
          empty_slot slot cleanup_info
       \<lbrace>\<lambda>rv. integrity aag X s\<rbrace>"
   apply (simp add: spec_valid_def)
  apply (simp add: empty_slot_def)
  apply (wp add:get_cap_wp set_cap_integrity_autarch set_original_integrity_autarch
            hoare_vcg_all_lift static_imp_wp
            empty_slot_extended.list_integ_lift empty_slot_list_integrity[where m="cdt s"] |
         simp add: set_cdt_def |
         wpc)+
  apply (safe; \<comment> \<open>for speedup\<close>
         clarsimp simp add: integrity_def,
         blast intro: cca_owned cdt_change_allowed_all_children)
  done

lemma empty_slot_integrity[wp,wp_not_transferable]:
  "\<lbrace>integrity aag X st and valid_list and valid_objs and valid_mdb and pas_refined aag and
    K (is_subject aag (fst slot) \<and> cleanup_info_wf c aag)\<rbrace>
       empty_slot slot c \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (integrity_trans_start)
  apply (rule hoare_pre)
  apply (wp empty_slot_integrity_spec[simplified spec_valid_def])
  by force

(* FIXME MOVE next to obj_atE *)
lemma ko_atD:
  "ko_at obj pos s \<Longrightarrow> kheap s pos = Some obj"
  by (blast elim: obj_atE)


lemma reply_cap_mdbE:
  assumes hyp:"reply_caps_mdb m cs"
  assumes side_hyp: "cs slot = Some (ReplyCap t False R)"
  obtains ptr R' where "m slot = Some ptr" and "cs ptr = Some (ReplyCap t True R')"
  using side_hyp hyp by (fastforce simp:reply_caps_mdb_def)

lemma reply_masters_mdbD1:
 "\<lbrakk>reply_masters_mdb m cs ; cs slot = Some (ReplyCap t True R)\<rbrakk> \<Longrightarrow> m slot = None"
  by (fastforce simp:reply_masters_mdb_def simp del:split_paired_All)

lemma reply_cap_no_grand_parent:
  "\<lbrakk>m \<Turnstile> pptr \<rightarrow>* slot ; reply_mdb m cs ; cs slot = Some (ReplyCap t False R)\<rbrakk>
    \<Longrightarrow> pptr = slot \<or> (m \<Turnstile> pptr \<leadsto> slot \<and> (\<exists> R'. cs pptr = Some (ReplyCap t True R')))"
  apply (clarsimp simp add:reply_mdb_def del:disjCI)
  apply (erule(1) reply_cap_mdbE)
  apply (drule(1) reply_masters_mdbD1)
  apply (erule rtrancl.cases,blast)
  apply (erule rtrancl.cases, simp add: cdt_parent_of_def)
  apply (simp add: cdt_parent_of_def)
  done


lemma set_cap_integrity_deletion_aux:
  "\<lbrace>integrity aag X st and valid_mdb and valid_objs and pas_refined aag and is_transferable_in slot and
     cdt_change_allowed' aag slot and K(\<not> is_subject aag (fst slot))\<rbrace>
      set_cap NullCap slot
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (integrity_trans_start)
  apply (rule hoare_pre)
   apply(unfold integrity_subjects_def arch_integrity_subjects_def)[1]
   apply (wp hoare_wp_combs)
    apply (unfold set_cap_def)[1]
    apply (wpc)
    apply (wp set_object_wp)
     apply wpc
         apply wp+
   apply (wp get_object_wp)
   apply wps
   apply wp
  apply (safe ; clarsimp simp add: cte_wp_at_caps_of_state dest!: ko_atD)
       (* cnode *)
       subgoal for s obj addr cnode_size content cap'
         apply (rule tro_cnode, simp, simp)
         apply (rule cnode_integrityI)
         apply simp
         apply (intro impI disjI2)
         apply (frule_tac addr=addr in caps_of_state_cnode, simp)
         apply clarsimp
         apply (erule is_transferable.cases, blast)
          apply (fastforce intro: reply_cap_deletion_integrity_intros)
         apply clarsimp
         apply (rule reply_cap_deletion_integrityI2[OF refl refl])
         apply (elim cdt_change_allowedE cdt_direct_change_allowed.cases)
          apply (drule reply_cap_no_grand_parent[where cs="caps_of_state s"]; fastforce?)
          apply (fastforce simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
                           dest: cap_auth_caps_of_state pas_refined_Control)
         apply (fastforce dest: tcb_states_of_state_kheapD descendant_of_caller_slot[OF _ _ tcb_atI]
                                parent_of_rtrancl_no_descendant)
         done
           (* tcb_ctable *)
       subgoal for s obj tcb
         apply (rule_tac tro_tcb_empty_ctable, simp, simp, simp)
         apply (frule_tac addr="tcb_cnode_index 0" in caps_of_state_tcb)
         apply clarsimp
         apply (elim is_transferable.cases, simp)
          apply (fastforce intro: reply_cap_deletion_integrity_intros)
         apply clarsimp
         apply (rule reply_cap_deletion_integrityI2[OF refl refl])
         apply (elim cdt_change_allowedE cdt_direct_change_allowed.cases)
          apply (force simp: aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
                       dest: reply_cap_no_grand_parent cap_auth_caps_of_state pas_refined_Control)
         apply (fastforce simp: direct_call_def
                          dest: tcb_caller_slot_empty_on_recieve parent_of_rtrancl_no_descendant
                                 descendant_of_caller_slot[OF _ _ tcb_atI] tcb_states_of_state_kheapD)
         done
     (* tcb_vtable *)
     apply (rename_tac s obj tcb)
     apply (rule tro_orefl)
     apply (fastforce simp: caps_of_state_tcb valid_obj_def valid_tcb_def ran_tcb_cap_cases
                      elim:pspace_valid_objsE[OF _ invs_valid_objs] elim!:is_transferable.cases)
    (* tcb_reply *)
    apply (rename_tac s obj tcb)
    apply (rule tro_orefl)
    apply (fastforce simp: is_cap_simps caps_of_state_tcb valid_obj_def valid_tcb_def
                           ran_tcb_cap_cases
                     elim: pspace_valid_objsE[OF _ invs_valid_objs] elim!:is_transferable.cases)
   (* tcb_caller *)
   subgoal for s obj tcb
     apply (rule_tac tro_tcb_empty_caller, simp, simp, simp)
     apply (frule_tac addr="tcb_cnode_index 3" in caps_of_state_tcb)
     apply clarsimp
     apply (elim is_transferable.cases, simp)
      apply (fastforce intro: reply_cap_deletion_integrity_intros)
     apply clarsimp
     apply (rule reply_cap_deletion_integrityI2[OF refl refl])
     apply (elim cdt_change_allowedE cdt_direct_change_allowed.cases)
      apply (force simp:aag_cap_auth_def cap_auth_conferred_def reply_cap_rights_to_auth_def
                   dest: reply_cap_no_grand_parent cap_auth_caps_of_state pas_refined_Control)
     apply (fastforce simp: direct_call_def
                      dest: tcb_caller_slot_empty_on_recieve parent_of_rtrancl_no_descendant
                            descendant_of_caller_slot[OF _ _ tcb_atI] tcb_states_of_state_kheapD)
     done
    (* tcb_ipcframe*)
  apply (rename_tac s obj tcb)
  apply (rule tro_orefl)
  apply (fastforce simp: is_nondevice_page_cap_simps caps_of_state_tcb
                         valid_obj_def valid_tcb_def ran_tcb_cap_cases
                   elim: pspace_valid_objsE[OF _ invs_valid_objs] elim!:is_transferable.cases)
  done


(* FIXME MOVE to lib*)
lemma pred_neg_simp[simp]:
  "(not P) s \<longleftrightarrow> \<not> (P s)"
  by (simp add:pred_neg_def)

lemma set_cap_integrity_deletion[wp_transferable]:
  "\<lbrace>integrity aag X st and valid_mdb and valid_objs and pas_refined aag and
     cdt_change_allowed' aag slot\<rbrace>
      set_cap NullCap slot
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (cases "is_subject aag (fst slot)")
   apply (wpsimp wp: set_cap_integrity_autarch)
  apply (wpsimp wp: set_cap_integrity_deletion_aux)
  by (fastforce dest:cca_to_transferable_or_subject simp:cte_wp_at_caps_of_state)


crunches set_original
  for pas_refined[wp]: "pas_refined aag"
  and valid_objs[wp]: "valid_objs"
  and cte_wp_at[wp]: "cte_wp_at P slot"
  and cdt_change_allowed[wp]: "cdt_change_allowed' aag slot"
  (simp:pas_refined_def state_objs_to_policy_def)

(* FIXME MOVE ?*)
crunches set_cdt_list, update_cdt_list
  for cdt[wp]: "\<lambda>s. P (cdt s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and is_original_cap[wp]: "\<lambda>s. P (is_original_cap s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and kheap[wp]: "\<lambda>s. P (kheap s)"
  and thread_states[wp]: "\<lambda>s. P (thread_states s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"
  and state_vrefs[wp]: "\<lambda>s. P (state_vrefs s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and valid_mdb[wp]: "valid_mdb"
  and valid_objs[wp]: "valid_objs"

lemma update_cdt_list_pas_refined[wp]:
   "\<lbrace> pas_refined aag \<rbrace> update_cdt_list f \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  by (wpsimp simp:pas_refined_def state_objs_to_policy_def | wps)+

text \<open>
  For the @{const empty_slot} proof, we need to rearrange the operations
  so that the CDT is updated after emptying the slot. Here we prove the
  rearrangement is valid.
\<close>

(* Flesh out the monad_commute framework.
 * FIXME: MOVE *)
lemma monad_commuteI2:
  "monad_commute P (f :: ('s, unit) nondet_monad) g \<Longrightarrow> (\<And>s. P s) \<Longrightarrow>
   (do f; g od) = (do g; f od)"
  by (monad_eq simp: monad_commute_def)

lemmas monad_commute_split2 = monad_commute_split[THEN commute_commute]

lemma modify_modify_commute:
  "monad_commute (\<lambda>s. f (g s) = g (f s)) (modify f) (modify g)"
  by (monad_eq simp: monad_commute_def)

lemma modify_gets_commute:
  "monad_commute (\<lambda>s. g (f s) = g s) (modify f) (gets g)"
  by (monad_eq simp: monad_commute_def)

lemma set_eq_iff_imp:
  "(A = B) = ((\<forall>x. x \<in> A \<longrightarrow> x \<in> B) \<and> (\<forall>x. x \<in> B \<longrightarrow> x \<in> A))"
  by blast

lemma modify_get_commute:
  "(\<And>s0. \<lbrace>(=) s0\<rbrace> g \<lbrace>\<lambda>r t. s0 = t\<rbrace>) \<Longrightarrow>
   monad_commute (\<lambda>s. fst ` fst (g (f s)) = fst ` fst (g s)
                      \<and> snd (g (f s)) = snd (g s)) (modify f) g"
  (* FIXME: proof cleanup *)
  apply (monad_eq simp: monad_commute_def valid_def
                        set_eq_iff_imp[where A="fst ` fst _"] image_iff)
  apply atomize
  apply (intro conjI; clarsimp)
   apply (rename_tac s0 r t)
   apply (clarsimp split: prod.splits)
   apply (rule_tac x=s0 in exI)
   apply (rule conjI)
    apply (drule_tac x=s0 in spec)
    apply fastforce
   apply fastforce

  apply (rename_tac s0 r t)
  apply (clarsimp split: prod.splits)
  apply (subgoal_tac "t = s0")
   apply (drule_tac x="f t" in spec)
   apply fastforce
  apply fastforce
  done

(* We use this version for the automation: the precond that falls out
 * will look like "\<forall>x. (\<exists>r. r \<in> fst (gets ?foo (?upd s)) \<and> x = fst r) = \<dots>"
 * which the monad_eq method can easily reduce with in_monad rules. *)
lemmas modify_get_commute' =
  modify_get_commute[simplified set_eq_iff image_iff Ball_def Bex_def]

lemma put_as_modify:
  "put t = modify (\<lambda>_. t)"
  by monad_eq

lemma put_commuteI:
  "monad_commute P f (modify (\<lambda>_. t)) \<Longrightarrow> monad_commute P f (put t)"
  by (simp add: put_as_modify)

lemma get_commuteI:
  "monad_commute P f (gets (\<lambda>s. s)) \<Longrightarrow> monad_commute P f get"
  by (simp add: gets_def)

lemma gets_gets_commute:
  "monad_commute \<top> (gets f) (gets g)"
  by (monad_eq simp: monad_commute_def)

lemma gets_get_commute:
  "(\<And>s0. \<lbrace>(=) s0\<rbrace> g \<lbrace>\<lambda>r t. s0 = t\<rbrace>) \<Longrightarrow>
   monad_commute \<top> (gets f) g"
  apply (monad_eq simp: monad_commute_def valid_def)
  by fastforce

lemma assert_commute':
  "empty_fail f \<Longrightarrow> monad_commute \<top> (assert G) f"
  apply (monad_eq simp: monad_commute_def empty_fail_def)
  by fastforce

named_theorems monad_commute_wp

lemmas[monad_commute_wp] =
  monad_commute_split
  monad_commute_split2
  modify_modify_commute
  gets_gets_commute
  put_commuteI put_commuteI[THEN commute_commute]
  get_commuteI get_commuteI[THEN commute_commute]
  return_commute return_commute[THEN commute_commute]
  assert_commute' assert_commute'[THEN commute_commute]

(* Sort-of VCG for monad_commute goals *)
lemma wpc_helper_monad_commute:
  "monad_commute P f g \<Longrightarrow> wpc_helper (P, P') (Q, Q') (monad_commute P f g)"
  by (clarsimp simp: wpc_helper_def)
wpc_setup "\<lambda>m. monad_commute P f m" wpc_helper_monad_commute

method monad_commute_wpc =
  (match conclusion in "monad_commute _ _ _" \<Rightarrow> succeed),
  (wpc | (rule commute_commute, wpc))

method monad_commute_step methods more_solver =
    determ \<open>wp monad_commute_wp\<close>
  | (* Conditional rules for fully schematic programs fragments:
     * make sure to solve the first condition before continuing *)
    (rule modify_get_commute' modify_get_commute'[THEN commute_commute],
     solves \<open>(changed \<open>wp | more_solver\<close>)+\<close>)
  | more_solver

method monad_commute methods more_solver =
    ((monad_commute_wpc; rule monad_commute_guard_imp),
     (monad_commute more_solver, more_solver)+)
  | (monad_commute_step more_solver,
     ((changed \<open>monad_commute more_solver\<close>)+)?)[1]

method monad_commute_default =
   monad_commute \<open>solves \<open>monad_eq\<close>
                 | solves \<open>(wpc, (changed \<open>wp | fastforce\<close>)+)\<close>
                 | solves \<open>(changed \<open>wp | fastforce\<close>)+\<close>
                 | fastforce\<close>


(* Now the commute steps *)
(* FIXME: remove and generalise version in ainvs *)
lemma set_original_set_cap_comm:
  "(do set_original slot' val; set_cap cap slot od) =
   (do set_cap cap slot; set_original slot' val od)"
  apply (rule ext)
  apply (clarsimp simp: bind_def split_def set_cap_def set_original_def
                        get_object_def set_object_def get_def put_def
                        simpler_gets_def simpler_modify_def
                        assert_def fail_def)
  apply (case_tac y; simp add: return_def fail_def)
  done


lemma set_cdt_set_cap_comm:
  "(do set_cdt c; set_cap cap slot od) =
   (do set_cap cap slot; set_cdt c od)"
  apply (rule ext)
  apply (clarsimp simp: bind_def split_def set_cap_def set_cdt_def
                        get_object_def set_object_def get_def put_def
                        simpler_gets_def simpler_modify_def
                        assert_def fail_def)
  apply (case_tac y; simp add: return_def fail_def)
  done


lemma set_cdt_set_original_comm:
  "(do set_cdt c; set_original slot val od) =
   (do set_original slot val; set_cdt c od)"
  apply (clarsimp simp: set_cdt_def[folded modify_def]
                        set_original_def[folded gets_modify_def]
                        get_object_def set_object_def
                  simp del: K_bind_def)
  apply (simp only: modify_def[symmetric])
  apply (rule monad_commuteI2)
   apply monad_commute_default
  apply monad_eq
  done

lemma set_cdt_empty_slot_ext_comm:
  "(do set_cdt c; empty_slot_ext slot slot_p od) =
   ((do empty_slot_ext slot slot_p; set_cdt c od) :: (det_ext state \<Rightarrow> _))"
  supply K_bind_def[simp del]
  apply (clarsimp simp: set_cdt_def empty_slot_ext_def
                        update_cdt_list_def set_cdt_list_def)
  apply (simp only: modify_def[symmetric])
  apply (rule monad_commuteI2)
   apply monad_commute_default
  apply monad_eq
  done

lemma set_cap_empty_slot_ext_comm:
  "(do set_cap cap slot; empty_slot_ext slot' slot_p od) =
   (do empty_slot_ext slot' slot_p; set_cap cap slot od :: (det_ext state \<Rightarrow> _))"
  apply (rule ext)
  apply (clarsimp simp: bind_def split_def set_cap_def empty_slot_ext_def
                        update_cdt_list_def set_cdt_list_def
                        get_object_def set_object_def get_def put_def
                        simpler_gets_def simpler_modify_def
                        assert_def fail_def)
  apply (case_tac y; simp add: return_def fail_def split: option.splits)
  done

(* FIXME: MOVE *)
lemmas bind_eqI' = NonDetMonadVCG.bind_eqI[OF _ refl]

lemma K_bind_assoc:
  "(do (do f; g od); h od) = (do f; g; h od)"
  by (simp add: bind_assoc)
lemmas K_bind_eqI = arg_cong2[where f="\<lambda>f g. do f; g od"]
lemmas K_bind_eqI' = K_bind_eqI[OF _ refl]

(* Putting it all together *)
lemma empty_slot_shuffle:
  "(do set_cdt c;
       empty_slot_ext slot slot_p;
       set_original slot False;
       set_cap NullCap slot od)
    =
   (do set_cap NullCap slot;
       empty_slot_ext slot slot_p;
       set_original slot False;
       set_cdt c od :: (det_ext state \<Rightarrow> _))"
  by (simp only:
            set_cdt_empty_slot_ext_comm[THEN K_bind_eqI', simplified K_bind_assoc]
            set_cdt_set_original_comm[THEN K_bind_eqI', simplified K_bind_assoc]
            set_cdt_set_cap_comm
            set_original_set_cap_comm[THEN K_bind_eqI', simplified K_bind_assoc]
            set_cap_empty_slot_ext_comm[THEN K_bind_eqI', simplified K_bind_assoc])

lemma empty_slot_integrity_transferable[wp_transferable]:
  "\<lbrace>integrity aag X st and valid_list and valid_objs and valid_mdb and pas_refined aag and
        cdt_change_allowed' aag slot and
        K (c = NullCap)\<rbrace>
       empty_slot slot c \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply integrity_trans_start
  apply (rule hoare_pre)
   apply (simp add: empty_slot_def)
   apply (simp add: empty_slot_shuffle[simplified])
   apply (simp add: set_cdt_def)
   apply (wp set_original_wp)
       apply (rename_tac cdtv x)
       apply (rule_tac Q = "\<lambda>_ s'. integrity aag X s s'\<and> cdtv = cdt s \<and>
                            is_original_cap s = is_original_cap s'"
                       in hoare_post_imp)
        apply (clarsimp simp add: integrity_def)
        apply (frule all_childrenD[OF cdt_change_allowed_all_children];fastforce)
       apply (wp empty_slot_extended.list_integ_lift)
          apply (rule hoare_pre)
           apply (rule_tac m = "cdt s" in empty_slot_list_integrity)
          apply simp
         apply wp+
      apply (wp set_cap_integrity_deletion gets_wp get_cap_wp)+
  by (fastforce intro: cdt_change_allowed_all_children)



lemma set_cdt_pas_refined:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrace>pas_refined aag and (\<lambda>s. \<forall>x y. c x = Some y \<and> cdt s x \<noteq> Some y
           \<longrightarrow> (is_transferable (caps_of_state s x) \<or>
               (pasObjectAbs aag (fst y), Control, pasObjectAbs aag (fst x)) \<in> pasPolicy aag)
             \<and> (pasObjectAbs aag (fst y), DeleteDerived, pasObjectAbs aag (fst x)) \<in> pasPolicy aag)\<rbrace>
      set_cdt c \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def set_cdt_def)
  apply (wp | simp | simp_all)+
  apply (clarsimp dest!: auth_graph_map_memD)
  apply (subgoal_tac
          "\<forall>x y. c x = Some y \<longrightarrow>
            (is_transferable (caps_of_state s x)
              \<or> (pasObjectAbs aag (fst y), Control, pasObjectAbs aag (fst x)) \<in> pasPolicy aag)
            \<and> (pasObjectAbs aag (fst y), DeleteDerived, pasObjectAbs aag (fst x)) \<in> pasPolicy aag")
   defer
   apply (intro allI, case_tac "cdt s x = Some y")
    apply (solves\<open>auto intro: auth_graph_map_memI state_bits_to_policy.intros\<close>)
   apply (fastforce dest!: spec elim!: mp)
  apply (erule state_bits_to_policy.cases)
  apply (auto intro: auth_graph_map_memI state_bits_to_policy.intros
              split: if_split_asm | blast)+
  done

lemma pas_refined_original_cap_update[simp]:
  "pas_refined aag (is_original_cap_update f s) = pas_refined aag s"
  by (simp add: pas_refined_def state_objs_to_policy_def)

lemma pas_refined_machine_state_update[simp]:
  "pas_refined aag (machine_state_update f s) = pas_refined aag s"
  by (simp add: pas_refined_def state_objs_to_policy_def state_refs_of_def)

lemma pas_refined_interrupt_states_update[simp]:
  "pas_refined aag (interrupt_states_update f s) = pas_refined aag s"
  by (simp add: pas_refined_def state_objs_to_policy_def state_refs_of_def)


crunch pas_refined[wp]: deleted_irq_handler "pas_refined aag"

lemma update_cdt_pas_refined:
  "\<lbrace>pas_refined aag and (\<lambda>s. \<forall>x y. c (cdt s) x = Some y \<and> cdt s x \<noteq> Some y
           \<longrightarrow> (is_transferable (caps_of_state s x) \<or>
               (pasObjectAbs aag (fst y), Control, pasObjectAbs aag (fst x)) \<in> pasPolicy aag)
             \<and> (pasObjectAbs aag (fst y), DeleteDerived, pasObjectAbs aag (fst x)) \<in> pasPolicy aag)\<rbrace>
     update_cdt c
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: update_cdt_def)
  apply (wp set_cdt_pas_refined)
  apply simp
  done

lemma aag_cap_auth_max_free_index_update[simp]:
  "aag_cap_auth aag (pasObjectAbs aag x)
     (max_free_index_update y) =
      aag_cap_auth aag (pasObjectAbs aag x) y"
  by (clarsimp simp: aag_cap_auth_def free_index_update_def split: cap.splits
               simp: cap_links_asid_slot_def cap_links_irq_def)

crunch pas_refined: set_untyped_cap_as_full "pas_refined aag"

lemmas set_untyped_cap_as_full_pas_refined'[wp] = set_untyped_cap_as_full_pas_refined[simplified]


lemma set_untyped_cap_as_full_cdt_is_original_cap:
  "\<lbrace> \<lambda> s. P (cdt s) (is_original_cap s) \<rbrace>
     set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace> \<lambda> rv s. P (cdt s) (is_original_cap s) \<rbrace>"
  unfolding set_untyped_cap_as_full_def
  apply(rule hoare_pre)
  apply (wp set_cap_caps_of_state2)
  apply clarsimp
  done

lemma state_objs_to_policy_more_update[simp]:
  "state_objs_to_policy (trans_state f s) =
   state_objs_to_policy s"
  by (simp add: state_objs_to_policy_def)

end

context is_extended begin

interpretation Arch . (*FIXME: arch_split*)

lemma pas_refined_tcb_domain_map_wellformed[wp]:
  assumes tdmw: "\<lbrace>tcb_domain_map_wellformed aag\<rbrace> f \<lbrace>\<lambda>_. tcb_domain_map_wellformed aag\<rbrace>"
  shows "\<lbrace>pas_refined aag\<rbrace> f \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def)
  apply (wp tdmw)
   apply (wp lift_inv)
   apply simp+
  done

end

context begin interpretation Arch . (*FIXME: arch_split*)

(* FIXME MOVE *)
lemma untyped_not_transferable:
  "is_untyped_cap cap \<Longrightarrow> \<not> is_transferable (Some cap)"
  by (fastforce simp: is_cap_simps elim!: is_transferable.cases)

(* FIXME MOVE *)
lemma is_transferable_max_free_index_update[simp]:
 "is_transferable (Some (max_free_index_update cap)) = is_transferable (Some cap)"
  by (simp add: is_transferable.simps free_index_update_def split: cap.splits)

lemma set_untyped_cap_as_full_is_transferable[wp]:
  "\<lbrace>\<lambda>s.\<not> is_transferable (caps_of_state s other_slot)\<rbrace>
     set_untyped_cap_as_full src_cap new_cap slot
   \<lbrace>\<lambda>rv s. \<not> is_transferable (caps_of_state s other_slot)\<rbrace>"
  apply (clarsimp simp: set_untyped_cap_as_full_def)
  apply wp
  using untyped_not_transferable max_free_index_update_preserve_untyped by simp

lemma set_untyped_cap_as_full_is_transferable':
  "\<lbrace>\<lambda>s. is_transferable ((caps_of_state s(slot2 \<mapsto> new_cap)) slot3) \<and> Some src_cap = (caps_of_state s slot)\<rbrace>
     set_untyped_cap_as_full src_cap new_cap slot
   \<lbrace>\<lambda>rv s. is_transferable ((caps_of_state s(slot2 \<mapsto> new_cap)) slot3)\<rbrace>"
  apply (clarsimp simp: set_untyped_cap_as_full_def)
  apply safe
  apply (wp,fastforce)+
  done

lemma cap_insert_pas_refined:
  "\<lbrace>pas_refined aag and valid_mdb and
    (\<lambda> s. (is_transferable_in src_slot s \<and> (\<not> Option.is_none (cdt s src_slot)))
    \<longrightarrow> is_transferable_cap new_cap)
     and K (is_subject aag (fst dest_slot)
                                 \<and> is_subject aag (fst src_slot)
                                 \<and> pas_cap_cur_auth aag new_cap) \<rbrace>
     cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cap_insert_def)
  apply (rule hoare_pre)
  apply (wp set_cap_pas_refined set_cdt_pas_refined update_cdt_pas_refined hoare_vcg_imp_lift
            hoare_weak_lift_imp hoare_vcg_all_lift set_cap_caps_of_state2
            set_untyped_cap_as_full_cdt_is_original_cap get_cap_wp
            tcb_domain_map_wellformed_lift hoare_vcg_disj_lift
            set_untyped_cap_as_full_is_transferable'
       | simp split del: if_split del: split_paired_All fun_upd_apply
       | strengthen update_one_strg)+
  by (fastforce split: if_split_asm
                simp: cte_wp_at_caps_of_state pas_refined_refl F[symmetric] valid_mdb_def2
                      mdb_cte_at_def Option.is_none_def
                simp del:split_paired_All
                dest: aag_cdt_link_Control aag_cdt_link_DeleteDerived cap_auth_caps_of_state)

lemma cap_insert_pas_refined':
  "\<lbrace>pas_refined aag and valid_mdb and
    (\<lambda> s. cte_wp_at is_transferable_cap src_slot s \<longrightarrow> is_transferable_cap new_cap)
     and K (is_subject aag (fst dest_slot)
                                 \<and> is_subject aag (fst src_slot)
                                 \<and> pas_cap_cur_auth aag new_cap) \<rbrace>
     cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  by (wp cap_insert_pas_refined)
     (fastforce dest: valid_mdb_mdb_cte_at[THEN mdb_cte_atD[rotated]]
                simp: cte_wp_at_caps_of_state Option.is_none_def)

lemma cap_insert_pas_refined_not_transferable:
   "\<lbrace>pas_refined aag and valid_mdb and
     not cte_wp_at is_transferable_cap src_slot
     and K (is_subject aag (fst dest_slot)
                                 \<and> is_subject aag (fst src_slot)
                                 \<and> pas_cap_cur_auth aag new_cap) \<rbrace>
     cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
   by (wpsimp wp: cap_insert_pas_refined')

lemma cap_insert_pas_refined_same_object_as:
   "\<lbrace>pas_refined aag and valid_mdb and
     cte_wp_at (same_object_as new_cap) src_slot
     and K (is_subject aag (fst dest_slot) \<and> is_subject aag (fst src_slot)
           \<and> (\<not> is_master_reply_cap new_cap)
                                 \<and> pas_cap_cur_auth aag new_cap) \<rbrace>
     cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (wp cap_insert_pas_refined)
  apply (clarsimp simp: Option.is_none_def cte_wp_at_caps_of_state)
  by (elim is_transferable_capE;
      fastforce simp: same_object_as_commute is_master_reply_cap_def same_object_as_def
               split: cap.splits)




lemma cap_links_irq_Nullcap [simp]:
  "cap_links_irq aag l cap.NullCap" unfolding cap_links_irq_def by simp

lemma aag_cap_auth_NullCap [simp]:
  "aag_cap_auth aag l cap.NullCap"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid)

lemma cap_move_pas_refined[wp]:
  "\<lbrace>pas_refined aag and valid_mdb and
    cte_wp_at (weak_derived new_cap) src_slot and
    cte_wp_at ((=) NullCap) dest_slot
    and K (is_subject aag (fst dest_slot)
                       \<and> is_subject aag (fst src_slot)
                       \<and> pas_cap_cur_auth aag new_cap)\<rbrace>
     cap_move new_cap src_slot dest_slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: cap_move_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: set_cap_pas_refined set_cdt_pas_refined tcb_domain_map_wellformed_lift
             set_cap_caps_of_state2)
  by (fastforce simp: is_transferable_weak_derived valid_mdb_def2 mdb_cte_at_def
                      Option.is_none_def cte_wp_at_caps_of_state
            simp del: split_paired_All
                elim: pas_refined_refl
                dest: invs_mdb pas_refined_mem[OF sta_cdt]
                      pas_refined_mem[OF sta_cdt_transferable])




lemma empty_slot_pas_refined[wp, wp_not_transferable]:
  "\<lbrace>pas_refined aag and valid_mdb and K (is_subject aag (fst slot))\<rbrace>
      empty_slot slot irqopt
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: empty_slot_def)
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp set_cdt_pas_refined
                    tcb_domain_map_wellformed_lift hoare_drop_imps)
  apply (strengthen aag_wellformed_delete_derived_trans[OF _ _ pas_refined_wellformed,
                                                            mk_strg I _ _ A])
  by (fastforce dest: all_childrenD is_transferable_all_children
                      pas_refined_mem[OF sta_cdt] pas_refined_mem[OF sta_cdt_transferable]
                      pas_refined_Control)

lemma empty_slot_pas_refined_transferable[wp_transferable]:
  "\<lbrace>pas_refined aag and valid_mdb and (\<lambda>s. is_transferable (caps_of_state s slot))\<rbrace>
     empty_slot slot irqopt
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: empty_slot_def)
  apply (wp set_cap_pas_refined get_cap_wp set_cdt_pas_refined tcb_domain_map_wellformed_lift
            hoare_drop_imps
        | simp | wpc)+
  apply clarsimp
  apply (strengthen aag_wellformed_delete_derived_trans[OF _ _ pas_refined_wellformed,
                                                            mk_strg I _ _ A])
  by (fastforce simp: cte_wp_at_caps_of_state
                dest: all_childrenD is_transferable_all_children
                      pas_refined_mem[OF sta_cdt] pas_refined_mem[OF sta_cdt_transferable])

lemma obj_ref_weak_derived:
  "weak_derived cap cap' \<Longrightarrow> obj_refs cap = obj_refs cap'"
  unfolding obj_refs_def aobj_ref'_def weak_derived_def copy_of_def same_object_as_def
  by (cases cap;
      (* also split arch caps *)
      (match premises in "cap = ArchObjectCap acap" for acap \<Rightarrow> \<open>cases acap\<close>)?;
      fastforce simp: is_cap_simps split: cap.splits arch_cap.splits)


crunch thread_states[wp]: set_cdt "\<lambda>s. P (thread_states s)"
crunch thread_bound_ntfns[wp]: set_cdt "\<lambda>s. P (thread_bound_ntfns s)"
crunch state_vrefs[wp]: set_cdt "\<lambda>s. P (state_vrefs s)"

lemma cap_swap_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and
    cte_wp_at (weak_derived cap) slot and
     cte_wp_at (weak_derived cap') slot' and
     K (is_subject aag (fst slot) \<and> is_subject aag (fst slot')
             \<and> pas_cap_cur_auth aag cap \<and> pas_cap_cur_auth aag cap')\<rbrace>
      cap_swap cap slot cap' slot'
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (rule hoare_pre)
   apply (wp add: tcb_domain_map_wellformed_lift | simp split del: if_split)+
        apply (simp only:pas_refined_def state_objs_to_policy_def)
        apply (wps | wp set_cdt_cdt_ct_ms_rvk set_cap_caps_of_state)+
  apply (clarsimp simp: pas_refined_def aag_cap_auth_def state_objs_to_policy_def
                        cte_wp_at_caps_of_state
                 split: if_split_asm
             split del: if_split)
  apply (rename_tac old_cap old_cap')
  apply (intro conjI)
    apply (find_goal \<open>match conclusion in "state_asids_to_policy_aux _ _ _ _ \<subseteq> _" \<Rightarrow> succeed\<close>)
    apply (erule(1) sata_update2[unfolded fun_upd_def]; fastforce)
   apply (find_goal \<open>match conclusion in "state_irqs_to_policy_aux _ _ \<subseteq> _" \<Rightarrow> succeed\<close>)
   apply (erule sita_caps_update2[unfolded fun_upd_def]; fastforce)
  apply (find_goal \<open>match conclusion in "auth_graph_map _ _ \<subseteq> _" \<Rightarrow> succeed\<close>)
  apply (rule subsetI)
  apply clarsimp
  apply (erule auth_graph_map_memE)
  apply (simp only: eq_commute[where b=slot'] eq_commute[where b=slot])
  apply (erule state_bits_to_policy.cases)
        apply (simp split: if_splits, blast intro: sbta_caps auth_graph_map_memI)
       apply (simp split: if_splits, blast intro: state_bits_to_policy.intros auth_graph_map_memI)
      apply (blast intro: state_bits_to_policy.intros auth_graph_map_memI)
     apply (blast intro: state_bits_to_policy.intros auth_graph_map_memI)
    apply clarsimp
    subgoal for s old_cap old_cap' child_obj child_index parent_obj parent_index
      apply (simp split: if_splits add: aag_wellformed_refl)
      by (erule subsetD;
          force simp: is_transferable_weak_derived intro!: sbta_cdt auth_graph_map_memI)+
   apply clarsimp
   subgoal for s old_cap old_cap' child_obj child_index parent_obj parent_index
     apply (simp split: if_splits add: aag_wellformed_refl)
     by (erule subsetD;
         force simp: is_transferable_weak_derived intro!: sbta_cdt_transferable auth_graph_map_memI)+
  by (blast intro: state_bits_to_policy.intros auth_graph_map_memI)


lemma cap_swap_for_delete_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and K (is_subject aag (fst slot) \<and> is_subject aag (fst slot'))\<rbrace>
      cap_swap_for_delete slot slot'
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state )
  apply (fastforce dest!: cap_cur_auth_caps_of_state)
  done

lemma sts_respects_restart_ep:
  "\<lbrace>integrity aag X st
     and (\<lambda>s. \<exists>ep. aag_has_auth_to aag Reset ep \<and> st_tcb_at (blocked_on ep) thread s)\<rbrace>
        set_thread_state thread Structures_A.Restart
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def obj_at_def st_tcb_at_def get_tcb_def)
  apply (rule_tac tro_tcb_restart [OF refl refl])
    apply (fastforce dest!: get_tcb_SomeD)
   apply (fastforce dest!: get_tcb_SomeD)
  apply simp
  done

lemma set_endpoinintegrity:
  "\<lbrace>integrity aag X st
          and ep_at epptr
          and K (\<exists>auth. aag_has_auth_to aag auth epptr \<and> auth \<in> {Receive, SyncSend, Reset})\<rbrace>
     set_endpoint epptr ep'
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def partial_inv_def a_type_def)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def tro_ep)
  done

lemma mapM_mapM_x_valid:
  "\<lbrace>P\<rbrace> mapM_x f xs \<lbrace>\<lambda>rv. Q\<rbrace> = \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  by (simp add: mapM_x_mapM liftM_def[symmetric] hoare_liftM_subst)

lemma sts_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def
                 elim!: rsubst[where P=P, OF _ ext]
                 dest!: get_tcb_SomeD)
  done

lemma sts_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: thread_bound_ntfns_def get_tcb_def
                 split: if_split option.splits kernel_object.splits
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma sts_thread_states[wp]:
  "\<lbrace>\<lambda>s. P ((thread_states s)(t := tcb_st_to_auth st))\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: get_tcb_def thread_states_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma sbn_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P ((thread_bound_ntfns s)(t := ntfn))\<rbrace>
     set_bound_notification t ntfn
   \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: get_tcb_def thread_bound_ntfns_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

(* FIXME move to AInvs *)
lemma set_thread_state_ekheap[wp]:
  "\<lbrace>\<lambda>s. P (ekheap s)\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_scheduler_action_wp simp: set_thread_state_ext_def)
  done

lemma set_thread_state_pas_refined:
  "\<lbrace>pas_refined aag and
        K (\<forall>r \<in> tcb_st_to_auth st. (pasObjectAbs aag t, snd r, pasObjectAbs aag (fst r)) \<in> pasPolicy aag)\<rbrace>
      set_thread_state t st
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply (clarsimp dest!: auth_graph_map_memD)
  apply (erule state_bits_to_policy.cases;
         auto intro: state_bits_to_policy.intros auth_graph_map_memI
              split: if_split_asm)
  done

lemma set_simple_ko_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> set_simple_ko f ptr val \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def obj_at_def
                        partial_inv_def a_type_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm if_splits)
  done

lemma set_simple_ko_tcb_states_of_state[wp]:
  "\<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace> set_simple_ko f ptr val \<lbrace>\<lambda>rv s. P (tcb_states_of_state s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                        partial_inv_def a_type_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm if_splits)
  done

lemma set_simple_ko_thread_states[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> set_simple_ko f ptr val \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                        partial_inv_def a_type_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm if_splits)
  done

lemma set_simple_ko_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> set_simple_ko f ptr val \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                        partial_inv_def a_type_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm if_splits)
  done

(* FIXME move to AInvs *)
lemma set_simple_ko_ekheap[wp]:
  "\<lbrace>\<lambda>s. P (ekheap s)\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  apply (simp add: set_simple_ko_def)
  apply (wpsimp wp: get_object_wp)
  done

lemma set_simple_ko_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> set_simple_ko f ptr ep \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply simp
  done

lemma thread_set_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def
                 elim!: rsubst[where P=P, OF _ ext] dest!: get_tcb_SomeD)
  done

lemma thread_set_thread_states_trivT:
  assumes st: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  shows "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: st get_tcb_def thread_states_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm)
  done

lemma thread_set_thread_bound_ntfns_trivT:
  assumes ntfn: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  shows "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: ntfn get_tcb_def thread_bound_ntfns_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm)
  done

lemma thread_set_pas_refined_triv:
  assumes cps: "\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb"
       and st: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
      and ntfn: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
     shows "\<lbrace>pas_refined aag\<rbrace> thread_set f t \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift
        | wps thread_set_caps_of_state_trivial[OF cps]
              thread_set_thread_states_trivT[OF st]
              thread_set_thread_bound_ntfns_trivT[OF ntfn]
        | simp)+
  done

lemmas thread_set_pas_refined = thread_set_pas_refined_triv[OF ball_tcb_cap_casesI]

lemma aag_owned_cdt_link:
  "\<lbrakk> cdt s x = Some y; is_subject aag (fst y); pas_refined aag s ;
     \<not> is_transferable (caps_of_state s x) \<rbrakk> \<Longrightarrow> is_subject aag (fst x)"
  by (fastforce dest: sta_cdt pas_refined_mem pas_refined_Control)

(* FIXME: MOVE *)
lemma descendants_of_owned_or_transferable:
  "\<lbrakk> valid_mdb s; pas_refined aag s; p \<in> descendants_of q (cdt s); is_subject aag (fst q) \<rbrakk>
       \<Longrightarrow> is_subject aag (fst p) \<or> is_transferable (caps_of_state s p)"
   using all_children_descendants_of pas_refined_all_children by blast

lemma pas_refined_arch_state_update_not_asids[simp]:
 "(arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s)) \<Longrightarrow> pas_refined aag (arch_state_update f s) = pas_refined aag s"
  by (simp add: pas_refined_def state_objs_to_policy_def)

crunch cdt[wp]: store_pte "\<lambda>s. P (cdt s)"

lemma store_pte_state_refs[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> store_pte p pte \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def state_refs_of_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma all_rsubst:
  "\<lbrakk> \<forall>v. P (f v); \<exists>v. f v = r \<rbrakk> \<Longrightarrow> P r"
  by clarsimp

lemma store_pte_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. \<forall>S. P ((state_vrefs s) (p && ~~ mask pt_bits :=
          (state_vrefs s (p && ~~ mask pt_bits) - S) \<union>
             (\<Union>(p', sz, auth)\<in>set_option (pte_ref pte).
                   (\<lambda>(p'', a). (p'', (p && mask pt_bits) >> 2, APageTable, a)) ` (ptr_range p' sz \<times> auth))))\<rbrace>
      store_pte p pte \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def obj_at_def)
  apply (simp add: fun_upd_def[symmetric] fun_upd_comp)
  apply (erule all_rsubst[where P=P])
  apply (subst fun_eq_iff, clarsimp simp: split_def)
  apply (cases "pte_ref pte")
   apply (auto simp: ucast_ucast_mask shiftr_over_and_dist
                     word_bw_assocs mask_def pt_bits_def pageBits_def)
  done

lemma store_pte_thread_states[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> store_pte p pte \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

lemma store_pte_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> store_pte p pte \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

lemma auth_graph_map_def2:
  "auth_graph_map f S = (\<lambda>(x, auth, y). (f x, auth, f y)) ` S"
  by (auto simp add: auth_graph_map_def image_def intro: rev_bexI)

(* FIXME move to AInvs *)
lemma store_pte_ekheap[wp]:
  "\<lbrace>\<lambda>s. P (ekheap s)\<rbrace> store_pte p pte \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
apply (simp add: store_pte_def set_pt_def)
apply (wp get_object_wp)
apply simp
done

crunch asid_table_inv [wp]: store_pte "\<lambda>s. P (asid_table s)"

lemma store_pte_pas_refined[wp]:
  "\<lbrace>pas_refined aag and K (\<forall>x. pte_ref pte = Some x \<longrightarrow> (\<forall>a \<in> snd (snd x).
         \<forall>p' \<in> (ptr_range (fst x) (fst (snd x))). auth_graph_map (pasObjectAbs aag) {(p && ~~ mask pt_bits, a, p')} \<subseteq> pasPolicy aag))\<rbrace>
        store_pte p pte \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: auth_graph_map_def2)
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD split del: if_split)
   apply (erule state_bits_to_policy.cases,
          auto intro: state_bits_to_policy.intros auth_graph_map_memI
               split: if_split_asm)[1]
  apply (erule_tac B="state_asids_to_policy_aux _ _ _ _" in subset_trans[rotated])
  apply (auto intro: state_asids_to_policy_aux.intros
              elim!: state_asids_to_policy_aux.cases
               elim: subset_trans[rotated]
              split: if_split_asm)
  done

lemma store_pde_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. \<forall>S. P ((state_vrefs s) (p && ~~ mask pd_bits :=
          (state_vrefs s (p && ~~ mask pd_bits) - S) \<union>
           (if ucast (kernel_base >> 20) \<le> (ucast (p && mask pd_bits >> 2)::12 word) then {}
            else
               (\<Union>(p', sz, auth)\<in>set_option (pde_ref2 pde).
                   (\<lambda>(p'', a). (p'', (p && mask pd_bits) >> 2, APageDirectory, a)) ` (ptr_range p' sz \<times> auth)))))\<rbrace>
      store_pde p pde \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def split del: if_split)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule all_rsubst[where P=P], subst fun_eq_iff)
  apply (clarsimp simp add: state_vrefs_def vs_refs_no_global_pts_def
                            fun_upd_def[symmetric] fun_upd_comp)
  apply (cases "pde_ref2 pde",
         simp_all add: split_def insert_Diff_if Un_ac ucast_ucast_mask_shift_helper)
  apply auto
  done

lemma store_pde_thread_states[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> store_pde p pde \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

lemma store_pde_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> store_pde p pde \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

lemma store_pde_pas_refined[wp]:
  "\<lbrace>pas_refined aag and K ((ucast (p && mask pd_bits >> 2)::12 word) < (ucast (kernel_base >> 20))
           \<longrightarrow> (\<forall>x. pde_ref2 pde = Some x \<longrightarrow>  (\<forall>a \<in> snd (snd x).
         \<forall>p' \<in> ptr_range (fst x) (fst (snd x)). auth_graph_map (pasObjectAbs aag) {(p && ~~ mask pd_bits, a, p')} \<subseteq> pasPolicy aag)))\<rbrace>
      store_pde p pde \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: auth_graph_map_def2)
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply (clarsimp split del: if_split)
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD split del: if_split)
   apply (erule state_bits_to_policy.cases,
          auto intro: state_bits_to_policy.intros auth_graph_map_memI
               split: if_split_asm)[1]
  apply (erule_tac B="state_asids_to_policy_aux _ _ _ _" in subset_trans[rotated])
  apply (auto intro: state_asids_to_policy_aux.intros
              elim!: state_asids_to_policy_aux.cases
              split: if_split_asm)
  done

lemmas pde_ref_simps = pde_ref_def[split_simps pde.split]
    pde_ref2_def[split_simps pde.split]

lemma set_asid_pool_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. P ((state_vrefs s) (p := (\<lambda>(r, p). (p, ucast r, AASIDPool, Control)) ` graph_of pool))\<rbrace>
      set_asid_pool p pool \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: state_vrefs_def fun_upd_def[symmetric] fun_upd_comp obj_at_def
                        vs_refs_no_global_pts_def
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma set_asid_pool_thread_states[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> set_asid_pool p pool \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

lemma set_asid_pool_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> set_asid_pool p pool \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

(* FIXME move to AInvs *)
lemma set_asid_pool_ekheap[wp]:
  "\<lbrace>\<lambda>s. P (ekheap s)\<rbrace> set_asid_pool p pool \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
apply (simp add: set_asid_pool_def)
apply (wp get_object_wp | simp)+
done

lemma set_asid_pool_pas_refined[wp]:
  "\<lbrace>pas_refined aag and (\<lambda>s. \<forall>(x, y) \<in> graph_of pool.
                  auth_graph_map (pasObjectAbs aag) {(p, Control, y)} \<subseteq> pasPolicy aag
               \<and> (\<forall>asid. arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some p
                       \<and> asid && mask asid_low_bits = ucast x
                       \<longrightarrow> (pasASIDAbs aag asid, Control, pasObjectAbs aag y) \<in> pasPolicy aag))\<rbrace>
         set_asid_pool p pool \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: auth_graph_map_def2 image_UN split_def)
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp dest!: auth_graph_map_memD)
   apply (erule state_bits_to_policy.cases,
          auto intro: state_bits_to_policy.intros auth_graph_map_memI
               split: if_split_asm)[1]
  apply (auto intro: state_asids_to_policy_aux.intros
               simp: subsetD[OF _ state_asids_to_policy_aux.intros(2)]
              elim!: state_asids_to_policy_aux.cases
              split: if_split_asm)
  apply fastforce+
  done

lemma auth_graph_map_mem_imageI:
  "(x, a, y) \<in> g \<Longrightarrow> (f x, a, f y) \<in> auth_graph_map f g"
  unfolding auth_graph_map_def by auto

lemma pas_refined_clear_asid:
  "pas_refined aag s \<Longrightarrow> pas_refined aag (s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := \<lambda>a. if a = asid then None else arm_asid_table (arch_state s) a\<rparr>\<rparr>)"
  unfolding pas_refined_def
  apply (auto simp: state_objs_to_policy_def elim!: state_asids_to_policy_aux.cases
             split: if_split_asm intro: state_asids_to_policy_aux.intros)
  apply (fastforce elim: state_asids_to_policy_aux.intros)+
  done

lemma set_ntfn_respects:
  "\<lbrace>integrity aag X st
          and K (\<exists>auth. aag_has_auth_to aag auth epptr \<and> auth \<in> {Receive, Notify, Reset})\<rbrace>
     set_notification epptr ep'
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def partial_inv_def a_type_def)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def tro_ntfn)
  done

crunch integrity_autarch: thread_set "integrity aag X st"

lemma sta_ts_mem:
  "\<lbrakk> thread_states s x = S; r \<in> S \<rbrakk>
      \<Longrightarrow> (x, snd r, fst r) \<in> state_objs_to_policy s"
  using sta_ts by force

lemma get_cap_auth_wp:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> is_subject aag (fst p)
       \<and> (\<forall>cap. caps_of_state s p = Some cap \<and> pas_cap_cur_auth aag cap \<longrightarrow> Q cap s)\<rbrace>
     get_cap p
   \<lbrace>Q\<rbrace>"
  apply (wp get_cap_wp)
  apply clarsimp
  apply (drule spec, erule mp)
  apply (fastforce simp: cte_wp_at_caps_of_state dest: cap_cur_auth_caps_of_state)
  done

lemma get_cap_auth_conferred:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst slot))\<rbrace>
     get_cap slot
   \<lbrace>\<lambda>rv s. \<forall>x\<in>obj_refs rv. \<forall>a \<in> cap_auth_conferred rv. aag_has_auth_to aag a x\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule sta_caps, simp+)
  apply (drule(1) pas_refined_mem)
  apply simp
  done

lemma cap_auth_conferred_cnode_cap:
  "is_cnode_cap cap \<Longrightarrow> Control \<in> cap_auth_conferred cap"
  by (clarsimp simp: is_cap_simps cap_auth_conferred_def)

lemma get_cap_ret_is_subject:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst slot))\<rbrace>
     get_cap slot
   \<lbrace>\<lambda>rv s. is_cnode_cap rv \<longrightarrow> is_subject aag (obj_ref_of rv)\<rbrace>"
  apply(clarsimp simp: valid_def)
  apply(frule get_cap_det)
  apply(drule_tac f=fst in arg_cong)
  apply(subst (asm) fst_conv)
  apply (drule in_get_cap_cte_wp_at[THEN iffD1])
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply(rule caps_of_state_pasObjectAbs_eq)
      apply(blast intro: sym)
     apply(blast intro: cap_auth_conferred_cnode_cap)
    apply assumption+
  apply(case_tac a, simp_all)
  done

definition
  auth_derived :: "cap \<Rightarrow> cap \<Rightarrow> bool"
where
 "auth_derived cap cap'
    \<equiv> (cap_asid' cap \<subseteq> cap_asid' cap')
    \<and> (untyped_range cap = untyped_range cap')
    \<and> (obj_refs cap = obj_refs cap')
    \<and> (cap_auth_conferred cap \<subseteq> cap_auth_conferred cap')
    \<and> (cap_irqs_controlled cap = cap_irqs_controlled cap')"

definition
  cnode_inv_auth_derivations :: "Invocations_A.cnode_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "cnode_inv_auth_derivations ci \<equiv> case ci of
    InsertCall cap ptr ptr' \<Rightarrow> cte_wp_at (auth_derived cap) ptr
  | MoveCall cap ptr ptr' \<Rightarrow> cte_wp_at (auth_derived cap) ptr
  | RotateCall s_cap p_cap src pivot dest
      \<Rightarrow> cte_wp_at (auth_derived s_cap) src and cte_wp_at (auth_derived p_cap) pivot
  | _ \<Rightarrow> \<top>"

lemma UNIV_eq_single_card:
  "(UNIV = {x :: 'a}) \<Longrightarrow> (card (UNIV :: 'a set) = 1)"
  apply (erule ssubst)
  apply simp
  done

lemma cli_cap_irqs_controlled:
  "(cap_irqs_controlled cap = cap_irqs_controlled cap') \<Longrightarrow>
    cap_links_irq aag (pasSubject aag) cap = cap_links_irq aag (pasSubject aag) cap'"
  by (auto simp add: card_word cap_links_irq_def split: cap.splits dest!: UNIV_eq_single_card UNIV_eq_single_card [OF sym])

lemma auth_derived_caps_of_state_impls:
  "\<lbrakk> auth_derived cap cap'; caps_of_state s ptr = Some cap'; pas_refined aag s;
     is_subject aag (fst ptr) \<rbrakk>
     \<Longrightarrow> pas_cap_cur_auth aag cap"
  unfolding aag_cap_auth_def
  apply (frule (1) clas_caps_of_state)
  apply (frule (1) cli_caps_of_state)
  apply (clarsimp simp: auth_derived_def cap_links_asid_slot_def)
  apply (auto dest: pas_refined_mem[OF sta_untyped] pas_refined_mem[OF sta_caps] cong: cli_cap_irqs_controlled)
  done

crunch integrity_autarch: set_asid_pool "integrity aag X st"
  (wp: crunch_wps)

(* FIXME: move *)
lemma a_type_arch_object_not_tcb[simp]:
  "a_type (ArchObj arch_kernel_obj) \<noteq> ATCB"
  by auto

crunch cur_domain[wp]: deleted_irq_handler "\<lambda>s. P (cur_domain s)"

lemma post_cap_deletion_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> post_cap_deletion c \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  by (wpsimp)

crunch cur_domain[wp]: cap_swap_for_delete, empty_slot, finalise_cap  "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps select_wp hoare_vcg_if_lift2 simp: unless_def)

lemma preemption_point_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> preemption_point \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
  by (wp preemption_point_inv', simp+)

lemma rec_del_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> rec_del call \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
  by (rule rec_del_preservation; wp)

crunch cur_domain[wp]: cap_delete  "\<lambda>s. P (cur_domain s)"

lemma cap_revoke_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> cap_revoke slot \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
  by (rule cap_revoke_preservation2; wp)

lemma cnode_inv_auth_derivations_If_Insert_Move:
  "cnode_inv_auth_derivations ((if P then MoveCall else InsertCall) cap src_slot dest_slot)
      = cnode_inv_auth_derivations (MoveCall cap src_slot dest_slot)"
  by (simp add: cnode_inv_auth_derivations_def)

lemma derive_cap_auth_derived:
  "\<lbrace>\<lambda>s. cap \<noteq> cap.NullCap \<longrightarrow> cte_wp_at (auth_derived cap) src_slot s\<rbrace>
      derive_cap src_slot cap
   \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> cte_wp_at (auth_derived rv) src_slot s\<rbrace>, -"
  apply (simp add: derive_cap_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp add: arch_derive_cap_def)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (safe, simp_all)
  apply (clarsimp simp: auth_derived_def arch_cap_auth_conferred_def cap_auth_conferred_def)
  done

lemma cap_rights_to_auth_mono:
  "R \<subseteq> R' \<Longrightarrow> cap_rights_to_auth R b \<subseteq> cap_rights_to_auth R' b"
  by (auto simp add: cap_rights_to_auth_def)

lemma auth_derived_mask_cap:
  "auth_derived cap cap' \<Longrightarrow> auth_derived (mask_cap R cap) cap'"
  apply (simp add: auth_derived_def mask_cap_def cap_rights_update_def
                   acap_rights_update_def validate_vm_rights_def
                   vm_kernel_only_def vm_read_only_def
            split: cap.split arch_cap.split bool.splits)
  apply safe
  apply (auto simp: cap_auth_conferred_def arch_cap_auth_conferred_def
                    cap_rights_to_auth_def reply_cap_rights_to_auth_def
                    vspace_cap_rights_to_auth_def
             split: if_split_asm)
  done

lemma auth_derived_update_cap_data:
  "\<lbrakk> auth_derived cap cap'; update_cap_data pres w cap \<noteq> cap.NullCap  \<rbrakk>
           \<Longrightarrow> auth_derived (update_cap_data pres w cap) cap'"
  apply (simp add: update_cap_data_def is_cap_simps arch_update_cap_data_def
                  split del: if_split cong: if_cong)
  apply (clarsimp simp: badge_update_def Let_def split_def is_cap_simps
                        is_page_cap_def
                  split: if_split_asm
              split del: if_split)
  apply (simp_all add: auth_derived_def the_cnode_cap_def)
  apply (simp_all add: cap_auth_conferred_def)
  done

lemma cte_wp_at_auth_derived_mask_cap_strg:
  "cte_wp_at (auth_derived cap) p s
      \<longrightarrow> cte_wp_at (auth_derived (mask_cap R cap)) p s"
  by (clarsimp simp: cte_wp_at_caps_of_state auth_derived_mask_cap)

lemma cte_wp_at_auth_derived_update_cap_data_strg:
  "cte_wp_at (auth_derived cap) p s \<and> update_cap_data pres w cap \<noteq> cap.NullCap
      \<longrightarrow> cte_wp_at (auth_derived (update_cap_data pres w cap)) p s"
  by (clarsimp simp: cte_wp_at_caps_of_state auth_derived_update_cap_data)

lemma get_cap_auth_derived:
  "\<lbrace>\<top>\<rbrace> get_cap slot \<lbrace>\<lambda>rv. cte_wp_at (auth_derived rv) slot\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state auth_derived_def)
  done

lemma decode_cnode_invocation_auth_derived:
  "\<lbrace>\<top>\<rbrace> decode_cnode_invocation label args cap excaps
   \<lbrace>cnode_inv_auth_derivations\<rbrace>,-"
  apply (simp add: decode_cnode_invocation_def split_def whenE_def unlessE_def
                 split del: if_split)
  apply (rule hoare_pre)
   apply (wp derive_cap_auth_derived get_cap_auth_derived
             hoare_vcg_all_lift
            | wpc
            | simp add: cnode_inv_auth_derivations_If_Insert_Move[unfolded cnode_inv_auth_derivations_def]
                        cnode_inv_auth_derivations_def split_def whenE_def
                    split del: if_split
            | strengthen cte_wp_at_auth_derived_mask_cap_strg
                         cte_wp_at_auth_derived_update_cap_data_strg
            | wp (once) hoare_drop_imps)+
  done


lemma derive_cap_clas:
  "\<lbrace>\<lambda>s. (\<not> is_pg_cap b) \<longrightarrow> cap_links_asid_slot aag p b \<rbrace>
     derive_cap a b
   \<lbrace>\<lambda>rv s. cap_links_asid_slot aag p rv\<rbrace>, -"
  apply (simp add: derive_cap_def arch_derive_cap_def  cong: cap.case_cong)
  apply (rule hoare_pre)
  apply (wp | wpc)+
  apply (auto simp: is_cap_simps cap_links_asid_slot_def)
  done

lemma arch_derive_cap_obj_refs_auth:
  "\<lbrace>K (\<forall>r\<in>obj_refs (cap.ArchObjectCap cap). \<forall>auth\<in>cap_auth_conferred (cap.ArchObjectCap cap). aag_has_auth_to aag auth r)\<rbrace>
  arch_derive_cap cap
  \<lbrace>(\<lambda>x s. \<forall>r\<in>obj_refs x. \<forall>auth\<in>cap_auth_conferred x. aag_has_auth_to aag auth r)\<rbrace>, -"
  unfolding arch_derive_cap_def
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply (clarsimp simp: cap_auth_conferred_def arch_cap_auth_conferred_def)
  done

lemma derive_cap_obj_refs_auth:
  "\<lbrace>K (\<forall>r\<in>obj_refs cap. \<forall>auth\<in>cap_auth_conferred cap. aag_has_auth_to aag auth r)\<rbrace>
  derive_cap slot cap
  \<lbrace>\<lambda>x s. (\<forall>r\<in>obj_refs x. \<forall>auth\<in>cap_auth_conferred x. aag_has_auth_to aag auth r) \<rbrace>, -"
  unfolding derive_cap_def
  apply (rule hoare_pre)
   apply (wp arch_derive_cap_obj_refs_auth | wpc | simp)+
  done

lemma arch_derive_cap_cli:
  "\<lbrace>K (cap_links_irq aag l (ArchObjectCap ac))\<rbrace>
   arch_derive_cap ac
   \<lbrace>\<lambda>x s. cap_links_irq aag l x\<rbrace>, -"
  by (wpsimp simp: arch_derive_cap_def comp_def cli_no_irqs)

lemma derive_cap_cli:
  "\<lbrace>K (cap_links_irq aag l cap)\<rbrace>
  derive_cap slot cap
  \<lbrace>\<lambda>x s. cap_links_irq aag l x \<rbrace>, -"
  unfolding derive_cap_def
  apply (rule hoare_pre)
  apply (wp arch_derive_cap_cli | wpc | simp add: comp_def cli_no_irqs)+
  apply fastforce
  done

(* FIXME: move *)
lemma derive_cap_obj_refs_subset:
  "\<lbrace>\<lambda>s. \<forall>x \<in> obj_refs cap. P x s\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs rv. P x s\<rbrace>, -"
  unfolding derive_cap_def arch_derive_cap_def
  apply (rule hoare_pre)
  apply (simp cong: cap.case_cong)
  apply (wp | wpc)+
  apply fastforce
  done

(* FIXME: move *)
lemma derive_cap_untyped_range_subset:
  "\<lbrace>\<lambda>s. \<forall>x \<in> untyped_range cap. P x s\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. \<forall>x \<in> untyped_range rv. P x s\<rbrace>, -"
  unfolding derive_cap_def arch_derive_cap_def
  apply (rule hoare_pre)
  apply (simp cong: cap.case_cong)
  apply (wp | wpc)+
  apply fastforce
  done

(* FIXME: move *)
lemma update_cap_obj_refs_subset:
  "x \<in> obj_refs (update_cap_data P dt cap) \<Longrightarrow> x \<in> obj_refs cap"
  apply (case_tac cap,
         simp_all add: update_cap_data_closedform
                split: if_split_asm)
  done

(* FIXME: move *)
lemma update_cap_untyped_range_subset:
  "x \<in> untyped_range (update_cap_data P dt cap) \<Longrightarrow> x \<in> untyped_range cap"
  apply (case_tac cap,
         simp_all add: update_cap_data_closedform
                split: if_split_asm)
  done

lemmas derive_cap_aag_caps =
  derive_cap_obj_refs_auth
  derive_cap_untyped_range_subset
  derive_cap_clas
  derive_cap_cli

lemma derive_cap_cap_cur_auth [wp]:
  "\<lbrace>\<lambda>s. pas_cap_cur_auth aag cap\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag rv\<rbrace>, -"
  unfolding aag_cap_auth_def
  apply (rule hoare_pre)
  apply (wp derive_cap_aag_caps)
  apply simp
  done

lemma P_0_1_spec:
  "\<lbrakk> (\<forall>x < length xs. P x); 2 \<le> length xs \<rbrakk> \<Longrightarrow> P 0 \<and> P 1"
  by fastforce

lemma clas_update_cap_data [simp]:
  "cap_links_asid_slot aag p (update_cap_data pres w cap) = cap_links_asid_slot aag p cap"
  unfolding cap_links_asid_slot_def update_cap_data_closedform arch_update_cap_data_def
  apply (cases cap)
  apply simp_all
  done

lemma update_cap_cap_auth_conferred_subset:
  "x \<in> cap_auth_conferred (update_cap_data b w cap) \<Longrightarrow> x \<in> cap_auth_conferred cap"
  unfolding update_cap_data_def
  apply (clarsimp split: if_split_asm simp: is_cap_simps cap_auth_conferred_def cap_rights_to_auth_def badge_update_def the_cnode_cap_def
    Let_def vspace_cap_rights_to_auth_def arch_update_cap_data_def)
  done

lemma update_cap_cli:
  "cap_links_irq aag l (update_cap_data b w cap) = cap_links_irq aag l cap"
  unfolding update_cap_data_def arch_update_cap_data_def
  by (cases cap, simp_all add: is_cap_simps cli_no_irqs badge_update_def the_cnode_cap_def Let_def)

lemma untyped_range_update_cap_data [simp]:
  "untyped_range (update_cap_data b w c) = untyped_range c"
  unfolding update_cap_data_def arch_update_cap_data_def
  by (cases c, simp_all add: is_cap_simps badge_update_def Let_def the_cnode_cap_def)

end

end
