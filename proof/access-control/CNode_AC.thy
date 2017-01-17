(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory CNode_AC
imports Access
begin

context begin interpretation Arch . (*FIXME: arch_split*)

(* FIXME: Move. *)
lemma tcb_domain_map_wellformed_ekheap[intro!, simp]:
  "ekheap (P s) = ekheap s \<Longrightarrow> tcb_domain_map_wellformed aag (P s) = tcb_domain_map_wellformed aag s"
by (simp add: tcb_domain_map_wellformed_aux_def get_etcb_def)

lemma integrity_irq_state_independent[intro!, simp]:
  "integrity x y z (s \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr> \<rparr>)
   = integrity x y z s"
  by (simp add: integrity_def)

lemma state_objs_to_policy_irq_state_independent[intro!, simp]:
  "state_objs_to_policy (s \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr> \<rparr>)
   = state_objs_to_policy s"
  by (simp add: state_objs_to_policy_def)

lemma tcb_domain_map_wellformed_independent[intro!, simp]:
  "tcb_domain_map_wellformed aag (s \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr> \<rparr>) = tcb_domain_map_wellformed aag s"
  by (simp add: tcb_domain_map_wellformed_aux_def get_etcb_def)

lemma pas_refined_irq_state_independent[intro!, simp]:
  "pas_refined x (s \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr> \<rparr>)
   = pas_refined x s"
  by (simp add: pas_refined_def)

section{* CNode-specific AC. *}

lemma set_original_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst slot))\<rbrace>
      set_original slot orig \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: set_original_def)
  apply wp
  apply (simp add: integrity_def)
  apply (clarsimp simp: integrity_cdt_def)
  done

lemma update_cdt_fun_upd_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst slot))\<rbrace>
      update_cdt (\<lambda>cdt. cdt (slot := v cdt)) \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: update_cdt_def set_cdt_def)
  apply wp
  apply (simp add: integrity_def)
  apply (clarsimp simp add: integrity_cdt_def)
  done


lemma pas_refined_all_children: "pas_refined aag s \<Longrightarrow> (cdt s) = m \<Longrightarrow> all_children (\<lambda>x. is_subject aag (fst x)) m"
  apply (clarsimp simp: all_children_def pas_refined_def)
  apply (subgoal_tac "(pasObjectAbs aag aa, Control, pasObjectAbs aag a) \<in> pasPolicy aag")
   apply (frule aag_wellformed_all_auth_is_owns(2))
   apply force
  apply (simp add: state_objs_to_policy_def auth_graph_map_def)
  apply (erule set_mp)
  apply (frule state_bits_to_policy.sbta_cdt)
  apply simp
  apply force
  done


(* FIXME: for some reason crunch does not discover the right precondition *)
lemma set_cap_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst param_b))\<rbrace> set_cap param_a param_b \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding set_cap_def
  apply (rule hoare_pre)
   apply (wp set_object_integrity_autarch get_object_wp | wpc)+
  apply clarsimp
  done

lemma integrity_cdt_list_as_list_integ: "(\<forall>x. cdt_list_integrity aag x (cdt_list st x) (cdt_list s x)) =
       (list_integ (\<lambda>x. pasObjectAbs aag (fst x) \<in> {pasSubject aag}) st s)"
  apply (simp add: list_integ_def integrity_cdt_list_def)
  apply force
  done

end

context is_extended begin

interpretation Arch . (*FIXME: arch_split*)

lemma list_integ_lift:
  assumes li: "\<lbrace>list_integ (\<lambda>x. is_subject aag (fst x)) st and Q\<rbrace> f \<lbrace>\<lambda>_. list_integ (\<lambda>x. is_subject aag (fst x)) st\<rbrace>"
  assumes ekh: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  assumes rq: "\<And>P. \<lbrace> \<lambda>s. P (ready_queues s) \<rbrace> f \<lbrace> \<lambda>rv s. P (ready_queues s) \<rbrace>"
  shows "\<lbrace>integrity aag X st and Q\<rbrace> f \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_pre)
   apply (unfold integrity_def[abs_def])
   apply (simp only: integrity_cdt_list_as_list_integ)
   apply (rule hoare_lift_Pf2[where f="ekheap"])
    apply (simp add: tcb_states_of_state_def get_tcb_def)
    apply (wp li ekh rq)+
  apply (simp only: integrity_cdt_list_as_list_integ)
  apply (simp add: tcb_states_of_state_def get_tcb_def)
  done

end

context begin interpretation Arch . (*FIXME: arch_split*)

crunch ekheap[wp]: cap_insert_ext,cap_swap_ext,cap_move_ext,empty_slot_ext,create_cap_ext "\<lambda>s. P (ekheap s)"

crunch ready_queues[wp]: cap_insert_ext,cap_swap_ext,cap_move_ext,empty_slot_ext,create_cap_ext "\<lambda>s. P (ready_queues s)"

crunch integrity_autarch: cap_insert "integrity aag X st"
  (simp: crunch_simps wp: crunch_wps update_cdt_fun_upd_integrity_autarch cap_insert_ext_extended.list_integ_lift cap_insert_list_integrity ignore:update_cdt cap_insert_ext)

text{*

Establish that the pointers this syscall will change are labelled with
the current agent's label.

NOTE: @{term "op \<subseteq>"} is used consciously here to block the simplifier
rewriting (the equivalent equalities) in the wp proofs.

*}

definition
  authorised_cnode_inv :: "'a PAS \<Rightarrow> Invocations_A.cnode_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "authorised_cnode_inv aag ci \<equiv> K (case ci of
    InsertCall cap ptr ptr' \<Rightarrow> pasObjectAbs aag ` {fst ptr, fst ptr'} \<subseteq> {pasSubject aag}
  | MoveCall cap ptr ptr' \<Rightarrow> pasObjectAbs aag ` {fst ptr, fst ptr'} \<subseteq> {pasSubject aag}
  | RotateCall s_cap p_cap src pivot dest \<Rightarrow> pasObjectAbs aag ` {fst src, fst pivot, fst dest} \<subseteq> {pasSubject aag}
  | SaveCall ptr \<Rightarrow> is_subject aag (fst ptr)
  | DeleteCall ptr \<Rightarrow> is_subject aag (fst ptr)
  | CancelBadgedSendsCall cap \<Rightarrow> pas_cap_cur_auth aag cap
  | RevokeCall ptr \<Rightarrow> is_subject aag (fst ptr))"

declare resolve_address_bits'.simps[simp del]

lemma resolve_address_bits_authorised_aux:
  "s \<turnstile> \<lbrace>pas_refined aag and K (is_cnode_cap (fst (cap, cref)) \<longrightarrow> (\<forall>x \<in> obj_refs (fst (cap, cref)). is_subject aag x))\<rbrace>
         resolve_address_bits (cap, cref)
       \<lbrace>\<lambda>rv s. is_subject aag (fst (fst rv))\<rbrace>, \<lbrace>\<lambda>rv. \<top>\<rbrace>"
unfolding resolve_address_bits_def
proof (induct arbitrary: s rule: resolve_address_bits'.induct)
  case (1 z cap' cref' s')
  have P: "\<And>s f P Q. s \<turnstile> \<lbrace>P\<rbrace> throwError f \<lbrace>Q\<rbrace>,\<lbrace>\<lambda>rv s. True\<rbrace>"
    by wp
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
              del: resolve_address_bits'.simps split_paired_All | clarsimp)+
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
        | wp_once get_cap_cur_auth)+
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
    state_irqs_to_policy_aux aag caps \<subseteq> pasPolicy aag; cap_links_irq aag (pasObjectAbs aag (fst ptr)) cap \<rbrakk> \<Longrightarrow>
    state_irqs_to_policy_aux aag (\<lambda>a. if a = ptr then Some cap else caps a)  \<subseteq> pasPolicy aag"
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
  apply (clarsimp simp: set_object_def)
  apply wp
  apply clarify
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (simp add: caps_of_state_cte_wp_at obj_at_def is_cap_table_def
                   is_tcb_def)
  apply (auto simp: cte_wp_at_cases)
  done

lemma set_object_domains_of_state[wp]:
  "\<lbrace> \<lambda>s. P (domains_of_state s) \<rbrace> set_object a b \<lbrace> \<lambda>_ s. P (domains_of_state s) \<rbrace>"
  unfolding set_object_def
  apply wp
  apply (rule rsubst[where P=P])
   apply assumption
  apply (clarsimp simp: get_etcb_def)
  done

crunch domains_of_state[wp]: set_cap "\<lambda>s. P (domains_of_state s)"

lemma set_cap_pas_refined [wp]:
  "\<lbrace>pas_refined aag and K (aag_cap_auth aag (pasObjectAbs aag (fst ptr)) cap)\<rbrace>
      set_cap cap ptr \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def aag_cap_auth_def)
  apply (rule hoare_pre)
   apply (wp set_cap_caps_of_state| wps)+
  apply clarsimp
  apply (intro conjI)  -- "auth_graph_map"
   apply (clarsimp dest!: auth_graph_map_memD)
   apply (erule state_bits_to_policy.cases, auto simp: cap_links_asid_slot_def label_owns_asid_slot_def intro: auth_graph_map_memI state_bits_to_policy.intros
        split: if_split_asm)[1]
  apply (erule (2) sata_update[unfolded fun_upd_def])
  apply (erule (2) sita_caps_update)
  done

declare set_original_wp[wp del]

lemma cap_move_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and  K (is_subject aag (fst dest) \<and> is_subject aag (fst src))\<rbrace>
       cap_move cap src dest \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cap_move_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp set_cap_integrity_autarch set_original_integrity_autarch
             cap_move_ext.list_integ_lift[where Q="\<top>"] cap_move_list_integrity
             | simp add: set_cdt_def split del: if_split)+
    apply (rule_tac Q="\<lambda>rv s. integrity aag X st s \<and> (\<forall>v. cdt s v = Some src \<longrightarrow> is_subject aag (fst v))"
                in hoare_post_imp)
     apply (simp add: integrity_def)
     apply (clarsimp simp: integrity_cdt_def)
     apply blast
    apply (wp set_cap_integrity_autarch set_cap_pas_refined | simp)+
  apply clarsimp
  apply (drule(1) pas_refined_mem[OF sta_cdt])
  apply (simp add: pas_refined_Control[symmetric])
  done

lemma integrity_cdt_fun_upd:
  "\<lbrakk> integrity aag X st (cdt_update f s); is_subject aag (fst slot) \<rbrakk>
       \<Longrightarrow> integrity aag X st (cdt_update (\<lambda>cdt. (f cdt) (slot := v cdt)) s)"
  apply (simp add: integrity_def)
  apply (clarsimp simp add: integrity_cdt_def)
  done

lemma cap_swap_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and
               K (is_subject aag (fst slot) \<and> is_subject aag (fst slot'))\<rbrace>
       cap_swap cap slot cap' slot' \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cap_swap_def)
  apply (wp get_cap_wp set_cap_integrity_autarch
            cap_swap_ext_extended.list_integ_lift[where Q="\<top>"] cap_swap_list_integrity
            set_original_integrity_autarch[unfolded pred_conj_def K_def]
            | simp add: set_cdt_def split del: if_split)+
   apply (rule_tac Q="\<lambda>rv s. integrity aag X st s
                       \<and> (\<forall>v. cdt s v = Some slot \<or> cdt s v = Some slot'
                              \<longrightarrow> is_subject aag (fst v))"
               in hoare_post_imp)
    apply (simp add: fun_upd_def[symmetric] split del: if_split)
    apply (intro integrity_cdt_fun_upd, simp_all)[1]
    apply (simp add: integrity_def)
    apply (clarsimp simp: integrity_cdt_def)
   apply (wp set_cap_integrity_autarch set_cap_pas_refined
            | simp | simp_all)+
  apply clarsimp
  apply (fastforce dest: pas_refined_mem[OF sta_cdt] pas_refined_Control)
  done

lemma cap_swap_for_delete_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag
            and K (is_subject aag (fst slot) \<and> is_subject aag (fst slot'))\<rbrace>
       cap_swap_for_delete slot slot' \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
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

(* MOVE *)
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

lemma empty_slointegrity_spec:
  notes split_paired_All[simp del]
  shows
  "s \<turnstile> \<lbrace>integrity aag X st and pas_refined aag and valid_list and
             K (is_subject aag (fst slot) \<and>
                (\<forall>irq. free_irq = Some irq \<longrightarrow> is_subject_irq aag irq))\<rbrace>
        empty_slot slot free_irq \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
   apply (simp add: spec_valid_def)
  apply (simp add: empty_slot_def)
  apply (wp get_cap_wp set_cap_integrity_autarch set_original_integrity_autarch
            hoare_vcg_all_lift static_imp_wp
            empty_slot_extended.list_integ_lift empty_slot_list_integrity[where m="cdt s"] |
         simp add: set_cdt_def |
         wpc)+
  apply (clarsimp simp: pas_refined_all_children)
  apply (simp add: integrity_def |
        (clarsimp simp: integrity_cdt_def) |
        (drule(1) pas_refined_mem[OF sta_cdt], simp) |
        (drule(1) pas_refined_Control,simp))+
  done


lemma empty_slointegrity[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag and valid_list and K (is_subject aag (fst slot) \<and> (\<forall> irq. free_irq = Some irq \<longrightarrow> is_subject_irq aag irq))\<rbrace>
       empty_slot slot free_irq \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule use_spec)
  apply (rule empty_slointegrity_spec)
  done

lemma set_cdt_pas_refined:
  "\<lbrace>pas_refined aag and (\<lambda>s. \<forall>x y. c x = Some y \<and> cdt s x \<noteq> Some y
           \<longrightarrow> (pasObjectAbs aag (fst y), Control, pasObjectAbs aag (fst x)) \<in> pasPolicy aag)\<rbrace>
      set_cdt c \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def set_cdt_def)
  apply (wp | simp | simp_all)+
  apply (clarsimp dest!: auth_graph_map_memD)
  apply (subgoal_tac "\<forall>x y. c x = Some y \<longrightarrow>
           (pasObjectAbs aag (fst y), Control, pasObjectAbs aag (fst x)) \<in> pasPolicy aag")
   defer
   apply (intro allI, case_tac "cdt s x = Some y")
    apply (auto intro: auth_graph_map_memI state_bits_to_policy.intros)[1]
   apply (fastforce dest!: spec elim!: mp)
  apply (thin_tac "\<forall>a b aa. P a b aa" for P)
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

crunch pas_refined[wp]: set_original "pas_refined aag"
crunch pas_refined[wp]: deleted_irq_handler "pas_refined aag"

lemma update_cdt_pas_refined:
  "\<lbrace>pas_refined aag and (\<lambda>s. \<forall>x y. c (cdt s) x = Some y \<and> cdt s x \<noteq> Some y
           \<longrightarrow> (pasObjectAbs aag (fst y), Control, pasObjectAbs aag (fst x)) \<in> pasPolicy aag)\<rbrace>
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
  apply(clarsimp simp: aag_cap_auth_def free_index_update_def split: cap.splits simp: cap_links_asid_slot_def cap_links_irq_def)
  done

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

lemma tcb_domain_map_wellformed_lift:
  assumes ekh: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  shows "\<lbrace>tcb_domain_map_wellformed aag\<rbrace> f \<lbrace>\<lambda>_. tcb_domain_map_wellformed aag\<rbrace>"
apply (simp add: tcb_domain_map_wellformed_aux_def get_etcb_def)
apply (wp ekh)
done

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

lemma cap_insert_pas_refined:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst dest_slot)
                       \<and> (is_subject aag (fst src_slot))
                       \<and> pas_cap_cur_auth aag new_cap)\<rbrace>
     cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: cap_insert_def)
  apply (rule hoare_pre)
  apply (wp set_cdt_pas_refined update_cdt_pas_refined hoare_vcg_imp_lift
            hoare_weak_lift_imp hoare_vcg_all_lift set_cap_caps_of_state2
            set_untyped_cap_as_full_cdt_is_original_cap get_cap_wp
            tcb_domain_map_wellformed_lift
       | simp split del: if_split del: split_paired_All fun_upd_apply
       | strengthen update_one_strg)+
  apply (clarsimp simp: pas_refined_refl split del: if_split)
  apply (erule impE)
   apply(clarsimp simp: cap_cur_auth_caps_of_state cte_wp_at_caps_of_state)
  apply (auto split: if_split_asm simp: pas_refined_refl dest: aag_cdt_link_Control)
  done

lemma cap_links_irq_Nullcap [simp]:
  "cap_links_irq aag l cap.NullCap" unfolding cap_links_irq_def by simp

lemma aag_cap_auth_NullCap [simp]:
  "aag_cap_auth aag l cap.NullCap"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid)

lemma cap_move_pas_refined[wp]:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst dest_slot)
                       \<and> is_subject aag (fst src_slot)
                       \<and> pas_cap_cur_auth aag new_cap)\<rbrace>
     cap_move new_cap src_slot dest_slot
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: cap_move_def)
  apply (rule hoare_pre)
   apply (wp set_cdt_pas_refined tcb_domain_map_wellformed_lift | simp)+
  apply (auto elim: pas_refined_refl dest: pas_refined_mem[OF sta_cdt])
  done

lemma empty_slot_pas_refined[wp]:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst slot))\<rbrace> empty_slot slot irqopt \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: empty_slot_def)
  apply (wp get_cap_wp set_cdt_pas_refined tcb_domain_map_wellformed_lift | simp | wpc)+
  apply (clarsimp simp: imp_disjL[symmetric] simp del: imp_disjL)
  apply (fastforce dest: pas_refined_mem[OF sta_cdt] pas_refined_Control)
  done

lemma cap_swap_pas_refined[wp]:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst slot) \<and> is_subject aag (fst slot')
             \<and> pas_cap_cur_auth aag cap \<and> pas_cap_cur_auth aag cap')\<rbrace>
      cap_swap cap slot cap' slot'
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (rule hoare_pre)
   apply (wp set_cdt_pas_refined tcb_domain_map_wellformed_lift | simp split del: if_split)+
   apply (clarsimp simp: pas_refined_refl split: if_split_asm split del: if_split)
  apply (fastforce dest: sta_cdt pas_refined_mem)+
  done

lemma cap_swap_for_delete_pas_refined[wp]:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst slot) \<and> is_subject aag (fst slot'))\<rbrace>
      cap_swap_for_delete slot slot'
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state )
  apply (fastforce dest!: cap_cur_auth_caps_of_state)
  done

lemma sts_respects_restart_ep:
  "\<lbrace>integrity aag X st and (\<lambda>s. \<exists>ep. aag_has_auth_to aag Reset ep \<and> st_tcb_at (blocked_on ep) thread s)\<rbrace>
   set_thread_state thread Structures_A.Restart
  \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply wp
  apply clarsimp
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def obj_at_def st_tcb_at_def)
  apply (rule_tac ntfn'="tcb_bound_notification tcb" in tro_tcb_restart [OF refl refl])
      apply (fastforce dest!: get_tcb_SomeD)
     apply (fastforce dest!: get_tcb_SomeD)
    apply (simp add: tcb_bound_notification_reset_integrity_def)+
  done

lemma set_endpoinintegrity:
  "\<lbrace>integrity aag X st
          and ep_at epptr
          and K (\<exists>auth. aag_has_auth_to aag auth epptr \<and> auth \<in> {Receive, SyncSend, Reset})\<rbrace>
     set_endpoint epptr ep'
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (case_tac koa, simp_all)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def tro_ep)
  done

lemma mapM_mapM_x_valid:
  "\<lbrace>P\<rbrace> mapM_x f xs \<lbrace>\<lambda>rv. Q\<rbrace> = \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  by (simp add: mapM_x_mapM liftM_def[symmetric] hoare_liftM_subst)

lemma sts_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp dxo_wp_weak |simp)+
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def
                 elim!: rsubst[where P=P, OF _ ext]
                 dest!: get_tcb_SomeD)
  done

lemma sts_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp dxo_wp_weak |simp)+
  apply (clarsimp simp: thread_bound_ntfns_def get_tcb_def 
                 split: if_split option.splits kernel_object.splits
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma sts_thread_states[wp]:
  "\<lbrace>\<lambda>s. P ((thread_states s)(t := tcb_st_to_auth st))\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp dxo_wp_weak |simp)+
  apply (clarsimp simp: get_tcb_def thread_states_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma sbn_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P ((thread_bound_ntfns s)(t := ntfn))\<rbrace> set_bound_notification t ntfn \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_bound_notification_def set_object_def)
  apply (wp dxo_wp_weak |simp)+
  apply (clarsimp simp: get_tcb_def thread_bound_ntfns_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

(* FIXME move to AInvs *)
lemma set_thread_state_ekheap[wp]:
  "\<lbrace>\<lambda>s. P (ekheap s)\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
apply (simp add: set_thread_state_def)
apply (wp set_scheduler_action_wp | simp add: set_thread_state_ext_def)+
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
  apply (erule state_bits_to_policy.cases)
  apply (auto intro: state_bits_to_policy.intros auth_graph_map_memI
              split: if_split_asm)
  done

lemma set_ep_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> set_endpoint ptr val \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def obj_at_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm)
  done

lemma set_ep_thread_states[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> set_endpoint ptr val \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

lemma set_ep_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> set_endpoint ptr val \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

(* FIXME move to AInvs *)
lemma set_endpoint_ekheap[wp]:
  "\<lbrace>\<lambda>s. P (ekheap s)\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
apply (simp add: set_endpoint_def)
apply (wp get_object_wp | simp)+
done

lemma set_endpoint_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply simp
  done

lemma set_ntfn_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> set_notification ptr val \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_notification_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def obj_at_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm)
  done

lemma set_ntfn_thread_states[wp]:
  "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> set_notification ptr val \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: set_notification_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

lemma set_ntfn_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> set_notification ptr val \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_notification_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

(* FIXME move to AInvs *)
lemma set_notification_ekheap[wp]:
  "\<lbrace>\<lambda>s. P (ekheap s)\<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
apply (simp add: set_notification_def)
apply (wp get_object_wp)
apply simp
done

lemma set_notification_pas_refined:
  "\<lbrace>pas_refined aag\<rbrace> set_notification ptr ntfn \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply simp
  done

lemma thread_set_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply (wp | simp)+
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def
                 elim!: rsubst[where P=P, OF _ ext] dest!: get_tcb_SomeD)
  done

lemma thread_set_thread_states_trivT:
  assumes st: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  shows "\<lbrace>\<lambda>s. P (thread_states s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (thread_states s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply (wp | simp)+
  apply (clarsimp simp: st get_tcb_def thread_states_def tcb_states_of_state_def split: option.split
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm)
  done

lemma thread_set_thread_bound_ntfns_trivT:
  assumes ntfn: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  shows "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply (wp | simp)+
  apply (clarsimp simp: ntfn get_tcb_def thread_bound_ntfns_def tcb_states_of_state_def split: option.split
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm)
  done

lemma thread_set_pas_refined_trivT:
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

lemmas thread_set_pas_refined_triv = thread_set_pas_refined_trivT[OF ball_tcb_cap_casesI]

lemma aag_owned_cdt_link:
  "\<lbrakk> cdt s x = Some y; is_subject aag (fst y); pas_refined aag s \<rbrakk> \<Longrightarrow> is_subject aag (fst x)"
  by (fastforce dest: sta_cdt pas_refined_mem pas_refined_Control)

lemma descendants_of_owned:
  "\<lbrakk> pas_refined aag s; p \<in> descendants_of q (cdt s); is_subject aag (fst q) \<rbrakk>
       \<Longrightarrow> is_subject aag (fst p)"
  apply (simp add: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)
  apply (erule_tac P="is_subject aag (fst q)" in rev_mp)
  apply (erule trancl.induct)
   apply (clarsimp simp: aag_owned_cdt_link)
  apply (clarsimp simp: aag_owned_cdt_link)
  done

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

lemma ucast_ucast_mask_pt_bits:
  "ucast (ucast (p && mask pt_bits >> 2) :: word8)
     = (p :: word32) && mask pt_bits >> 2"
  apply (simp add: ucast_ucast_mask shiftr_over_and_dist
                   word_bw_assocs)
  apply (simp add: mask_def pt_bits_def pageBits_def)
  done

lemma store_pte_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. \<forall>S. P ((state_vrefs s) (p && ~~ mask pt_bits :=
          (state_vrefs s (p && ~~ mask pt_bits) - S) \<union>
             (\<Union>(p', sz, auth)\<in>set_option (pte_ref pte).
                   (\<lambda>(p'', a). (p'', VSRef ((p && mask pt_bits) >> 2) (Some APageTable), a)) ` (ptr_range p' sz \<times> auth))))\<rbrace>
      store_pte p pte \<lbrace>\<lambda>rv s. P (state_vrefs s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def obj_at_def)
  apply (simp add: fun_upd_def[symmetric] fun_upd_comp)
  apply (erule all_rsubst[where P=P])
  apply (subst fun_eq_iff, clarsimp simp: split_def)
  apply (cases "pte_ref pte", auto simp: ucast_ucast_mask_pt_bits)
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
  apply (erule_tac B="state_asids_to_policy aag s" for s in subset_trans[rotated])
  apply (auto intro: state_asids_to_policy_aux.intros
              elim!: state_asids_to_policy_aux.cases
              split: if_split_asm)
  done

lemma store_pde_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. \<forall>S. P ((state_vrefs s) (p && ~~ mask pd_bits :=
          (state_vrefs s (p && ~~ mask pd_bits) - S) \<union>
           (if ucast (kernel_base >> 20) \<le> (ucast (p && mask pd_bits >> 2)::12 word) then {}
            else
               (\<Union>(p', sz, auth)\<in>set_option (pde_ref2 pde).
                   (\<lambda>(p'', a). (p'', VSRef ((p && mask pd_bits) >> 2) (Some APageDirectory), a)) ` (ptr_range p' sz \<times> auth)))))\<rbrace>
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
  apply (erule_tac B="state_asids_to_policy aag s" for s in subset_trans[rotated])
  apply (auto intro: state_asids_to_policy_aux.intros
              elim!: state_asids_to_policy_aux.cases
              split: if_split_asm)
  done

lemmas pde_ref_simps = pde_ref_def[split_simps pde.split]
    pde_ref2_def[split_simps pde.split]

lemma set_asid_pool_st_vrefs[wp]:
  "\<lbrace>\<lambda>s. P ((state_vrefs s) (p := (\<lambda>(r, p). (p, VSRef (ucast r)
               (Some AASIDPool), Control)) ` graph_of pool))\<rbrace>
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
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: thread_states_def obj_at_def get_tcb_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: Structures_A.kernel_object.split_asm option.split)
  done

lemma set_asid_pool_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace> set_asid_pool p pool \<lbrace>\<lambda>rv s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
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
  apply (simp add: set_notification_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (case_tac ko, simp_all)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def tro_ntfn)
  done

crunch integrity_autarch: thread_set "integrity aag X st"

lemma sta_ts_mem:
  "\<lbrakk> thread_states s x = S; r \<in> S \<rbrakk>
      \<Longrightarrow> (x, snd r, fst r) \<in> state_objs_to_policy s"
  using sta_ts by force

lemma get_cap_auth_wp:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> is_subject aag (fst p) \<and> (\<forall>cap. caps_of_state s p = Some cap \<and> pas_cap_cur_auth aag cap \<longrightarrow> Q cap s)\<rbrace> get_cap p \<lbrace>Q\<rbrace>"
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
  apply (clarsimp simp: auth_derived_def cap_auth_conferred_def is_page_cap_def)
  done

lemma cap_rights_to_auth_mono:
  "R \<subseteq> R' \<Longrightarrow> cap_rights_to_auth R b \<subseteq> cap_rights_to_auth R' b"
  by (auto simp add: cap_rights_to_auth_def)

lemma auth_derived_mask_cap:
  "auth_derived cap cap' \<Longrightarrow> auth_derived (mask_cap R cap) cap'"
  apply (simp add: auth_derived_def mask_cap_def cap_rights_update_def
                   is_cap_simps acap_rights_update_def
                   validate_vm_rights_def vm_kernel_only_def
                   vm_read_only_def
            split: cap.split arch_cap.split)
  apply (rule conjI | clarsimp
              | erule subsetD subsetD[OF cap_rights_to_auth_mono, rotated]
              | simp add: cap_auth_conferred_def vspace_cap_rights_to_auth_def
                          is_page_cap_def split: if_split_asm)+
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
                   del: hoare_post_taut hoare_True_E_R
                    split del: if_split
            | strengthen cte_wp_at_auth_derived_mask_cap_strg
                         cte_wp_at_auth_derived_update_cap_data_strg
            | wp_once hoare_drop_imps)+
  done


lemma derive_cap_clas:
  "\<lbrace>\<lambda>s. (\<not> is_pg_cap b) \<longrightarrow> cap_links_asid_slot aag p b \<rbrace> derive_cap a b \<lbrace>\<lambda>rv s. cap_links_asid_slot aag p rv\<rbrace>, -"
  apply (simp add: derive_cap_def arch_derive_cap_def  cong: cap.case_cong)
  apply (rule hoare_pre)
  apply (wp | wpc)+
  apply (auto simp: is_cap_simps cap_links_asid_slot_def)
  done

lemma arch_derive_cap_obj_refs_auth:
  "\<lbrace>K (\<forall>r\<in>obj_refs (cap.ArchObjectCap cap). \<forall>auth\<in>cap_auth_conferred (cap.ArchObjectCap cap). aag_has_auth_to aag auth r)\<rbrace>
  arch_derive_cap cap
  \<lbrace>(\<lambda>x s. \<forall>r\<in>obj_refs x. \<forall>auth\<in>cap_auth_conferred x. aag_has_auth_to aag auth r) \<circ> cap.ArchObjectCap\<rbrace>, -"
  unfolding arch_derive_cap_def
  apply (rule hoare_pre)
  apply (wp | wpc)+
  apply (clarsimp simp: cap_auth_conferred_def is_page_cap_def)
  done

lemma derive_cap_obj_refs_auth:
  "\<lbrace>K (\<forall>r\<in>obj_refs cap. \<forall>auth\<in>cap_auth_conferred cap. aag_has_auth_to aag auth r)\<rbrace>
  derive_cap slot cap
  \<lbrace>\<lambda>x s. (\<forall>r\<in>obj_refs x. \<forall>auth\<in>cap_auth_conferred x. aag_has_auth_to aag auth r) \<rbrace>, -"
  unfolding derive_cap_def
  apply (rule hoare_pre)
  apply (wp arch_derive_cap_obj_refs_auth | wpc | simp)+
  done

lemma derive_cap_cli:
  "\<lbrace>K (cap_links_irq aag l cap)\<rbrace>
  derive_cap slot cap
  \<lbrace>\<lambda>x s. cap_links_irq aag l x \<rbrace>, -"
  unfolding derive_cap_def
  apply (rule hoare_pre)
  apply (wp  | wpc | simp add: comp_def cli_no_irqs)+
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

lemmas derive_cap_aag_caps = derive_cap_obj_refs_auth derive_cap_untyped_range_subset derive_cap_clas derive_cap_cli

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
  apply (cases cap, simp_all add: is_cap_simps cli_no_irqs badge_update_def the_cnode_cap_def Let_def)
  done

lemma untyped_range_update_cap_data [simp]:
  "untyped_range (update_cap_data b w c) = untyped_range c"
  unfolding update_cap_data_def arch_update_cap_data_def
  by (cases c, simp_all add: is_cap_simps badge_update_def Let_def the_cnode_cap_def)

end

end
