(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CNode_AC
imports ArchAccess_AC
begin

section\<open>CNode-specific AC.\<close>


(* FIXME: Move. *)
lemma tcb_domain_map_wellformed_ekheap[intro!, simp]:
  "ekheap (P s) = ekheap s \<Longrightarrow> tcb_domain_map_wellformed aag (P s) = tcb_domain_map_wellformed aag s"
  by (simp add: tcb_domain_map_wellformed_aux_def get_etcb_def)

(* FIXME: for some reason crunch does not discover the right precondition *)
lemma set_cap_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst slot))\<rbrace> set_cap cap slot \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp: set_cap_def wp: set_object_integrity_autarch get_object_wp)

lemma integrity_cdt_list_as_list_integ:
  "cdt_list_integrity_state aag st s =
   list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st s"
  by (fastforce elim: integrity_cdt_listE list_integE intro: list_integI integrity_cdt_list_intros)

crunches cap_swap_ext,cap_move_ext,empty_slot_ext
  for ekheap[wp]: "\<lambda>s. P (ekheap s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"

crunches set_untyped_cap_as_full
  for integrity_autarch: "integrity aag X st"


locale CNode_AC_1 =
  fixes aag :: "'a PAS"
  and val_t :: "'b"
  assumes sata_cdt_update[simp]:
    "\<And>f. state_asids_to_policy aag (cdt_update f s) = state_asids_to_policy aag s"
  and sata_is_original_cap_update[simp]:
    "\<And>f. state_asids_to_policy aag (is_original_cap_update f s) = state_asids_to_policy aag s"
  and sata_interrupt_states_update[simp]:
    "\<And>f. state_asids_to_policy aag (interrupt_states_update f s) = state_asids_to_policy aag s"
  and sata_machine_state_update[simp]:
    "\<And>f. state_asids_to_policy aag (machine_state_update f s) = state_asids_to_policy aag s"
  and sata_update:
    "\<lbrakk> pas_wellformed aag; cap_links_asid_slot aag (pasObjectAbs aag (fst ptr)) cap;
       state_asids_to_policy_arch aag (caps :: cslot_ptr \<Rightarrow> cap option) as vrefs \<subseteq> pasPolicy aag \<rbrakk>
       \<Longrightarrow> state_asids_to_policy_arch aag (caps(ptr \<mapsto> cap)) as vrefs \<subseteq> pasPolicy aag"
  and sata_update2:
    "\<lbrakk> pas_wellformed aag; cap_links_asid_slot aag (pasObjectAbs aag (fst ptr)) cap;
       cap_links_asid_slot aag (pasObjectAbs aag (fst ptr')) cap';
       state_asids_to_policy_arch aag caps (as :: arch_state) vrefs \<subseteq> pasPolicy aag \<rbrakk>
       \<Longrightarrow> state_asids_to_policy_arch aag (caps(ptr \<mapsto> cap, ptr' \<mapsto> cap')) as vrefs \<subseteq> pasPolicy aag"
  and state_vrefs_tcb_upd:
    "\<lbrakk> pspace_aligned s; valid_vspace_objs s; valid_arch_state s; tcb_at tptr s \<rbrakk>
       \<Longrightarrow> state_vrefs (s\<lparr>kheap := (kheap s)(tptr \<mapsto> TCB tcb)\<rparr>) = state_vrefs s"
  and state_vrefs_simple_type_upd:
    "\<lbrakk> pspace_aligned s; valid_vspace_objs s; valid_arch_state s;
       ko_at ko p s; is_simple_type ko; a_type ko = a_type (f (val :: 'b)) \<rbrakk>
       \<Longrightarrow> state_vrefs (s\<lparr>kheap := (kheap s)(p \<mapsto> f val)\<rparr>) = state_vrefs s"
  and a_type_arch_object_not_tcb[simp]:
    "a_type (ArchObj arch_kernel_obj) \<noteq> ATCB"
  and set_cap_state_vrefs:
    "\<And>P. \<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
          set_cap cap slot
          \<lbrace>\<lambda>_ s :: det_ext state. P (state_vrefs s)\<rbrace>"
  and set_cdt_state_vrefs[wp]:
    "\<And>P. set_cdt t \<lbrace>\<lambda>s :: det_ext state. P (state_vrefs s)\<rbrace>"
  and set_cdt_state_asids_to_policy[wp]:
    "\<And>P. set_cdt t \<lbrace>\<lambda>s. P (state_asids_to_policy aag s)\<rbrace>"
  and arch_post_cap_deletion_integrity[wp]:
    "arch_post_cap_deletion acap \<lbrace>integrity aag X st\<rbrace>"
  and arch_post_cap_deletion_cur_domain[wp]:
    "\<And>P. arch_post_cap_deletion acap \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  and arch_finalise_cap_cur_domain:
    "\<And>P. arch_finalise_cap acap final \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  and prepare_thread_delete_cur_domain:
    "\<And>P. prepare_thread_delete p \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  and maskInterrupt_underlying_memory[wp]:
    "\<And>P. maskInterrupt m irq \<lbrace>\<lambda>s. P (underlying_memory s)\<rbrace>"
  and maskInterrupt_device_state[wp]:
    "\<And>P. maskInterrupt m irq \<lbrace>\<lambda>s. P (device_state s)\<rbrace>"
  and cap_insert_ext_extended_list_integ_lift:
    "\<And>Q a b c d e.
     \<lbrakk> \<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
       cap_insert_ext a b c d e
       \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st\<rbrace>;
       \<And>P. cap_insert_ext a b c d e \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>; \<And>P. cap_insert_ext a b c d e \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> \<rbrakk>
       \<Longrightarrow> \<lbrace>integrity aag X st and Q\<rbrace> cap_insert_ext a b c d e \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  and cap_move_ext_list_integ_lift:
    "\<And>Q a b c d.
     \<lbrakk> \<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
       cap_move_ext a b c d
       \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st\<rbrace>;
       \<And>P. cap_move_ext a b c d \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>; \<And>P. cap_move_ext a b c d \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> \<rbrakk>
       \<Longrightarrow> \<lbrace>integrity aag X st and Q\<rbrace> cap_move_ext a b c d \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  and cap_swap_ext_extended_list_integ_lift:
    "\<And>Q a b c d.
     \<lbrakk> \<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
       cap_swap_ext a b c d
       \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st\<rbrace>;
       \<And>P. cap_swap_ext a b c d \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>; \<And>P. cap_swap_ext a b c d \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> \<rbrakk>
       \<Longrightarrow> \<lbrace>integrity aag X st and Q\<rbrace> cap_swap_ext a b c d \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  and empty_slot_extended_list_integ_lift:
    "\<And>Q a b.
     \<lbrakk> \<lbrace>list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st and Q\<rbrace>
       empty_slot_ext a b
       \<lbrace>\<lambda>_. list_integ (cdt_change_allowed aag {pasSubject aag} (cdt st) (tcb_states_of_state st)) st\<rbrace>;
       \<And>P. empty_slot_ext a b \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>; \<And>P. empty_slot_ext a b \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> \<rbrakk>
       \<Longrightarrow> \<lbrace>integrity aag X st and Q\<rbrace> empty_slot_ext a b \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
begin

lemma set_original_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst slot))\<rbrace>
   set_original slot orig
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (wpsimp simp: set_original_def)
  apply (clarsimp simp: integrity_def intro!: integrity_cdt_direct)
  done

lemma set_original_integrity:
  "\<lbrace>integrity aag X st and cdt_change_allowed' aag slot\<rbrace>
   set_original slot orig
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply integrity_trans_start
  apply (wpsimp simp: set_original_def integrity_def)
  done

lemma update_cdt_fun_upd_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst slot))\<rbrace>
   update_cdt (\<lambda>cdt. cdt (slot := v cdt))
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (wpsimp simp: update_cdt_def set_cdt_def)
  apply (clarsimp simp: integrity_def intro!: integrity_cdt_direct)
  done

lemma cap_insert_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag (fst src_slot) \<and> is_subject aag (fst dest_slot))\<rbrace>
   cap_insert cap src_slot dest_slot
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: cap_insert_def)
  apply (wp set_original_integrity_autarch cap_insert_ext_extended_list_integ_lift
            cap_insert_list_integrity update_cdt_fun_upd_integrity_autarch gets_inv
            set_cap_integrity_autarch set_untyped_cap_as_full_integrity_autarch assert_inv)
  apply fastforce
  done

end


text\<open>

Establish that the pointers this syscall will change are labelled with
the current agent's label.

NOTE: @{term "(\<subseteq>)"} is used consciously here to block the simplifier
rewriting (the equivalent equalities) in the wp proofs.

\<close>

definition authorised_cnode_inv ::
  "'a PAS \<Rightarrow> Invocations_A.cnode_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
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
                               \<longrightarrow> (\<forall>x \<in> obj_refs_ac (fst (cap, cref)). is_subject aag x))\<rbrace>
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
  "\<lbrace>pas_refined aag and K (is_cnode_cap cap \<longrightarrow> (\<forall>x \<in> obj_refs_ac cap. is_subject aag x))\<rbrace>
   resolve_address_bits (cap, cref)
   \<lbrace>\<lambda>rv s. is_subject aag (fst (fst rv))\<rbrace>, -"
  apply (unfold validE_R_def)
  apply (rule hoare_pre)
   apply (rule use_spec(2)[OF resolve_address_bits_authorised_aux])
  apply simp
  done

lemma lookup_slot_for_cnode_op_authorised[wp]:
  "\<lbrace>pas_refined aag and K (is_cnode_cap croot \<longrightarrow> (\<forall>x \<in> obj_refs_ac croot. is_subject aag x))\<rbrace>
   lookup_slot_for_cnode_op is_source croot ptr depth
   \<lbrace>\<lambda>rv s. is_subject aag (fst rv)\<rbrace>, -"
  apply (simp add: lookup_slot_for_cnode_op_def split del: if_split)
  apply (wp whenE_throwError_wp hoare_drop_imps
            resolve_address_bits_authorised
              [THEN hoare_strengthen_postE_R[where Q'="\<lambda>x s. is_subject aag (fst (fst x))"]]
         | wpc | fastforce)+
  done

(* FIXME MOVE *)
lemma is_cnode_into_is_subject:
  "\<lbrakk> pas_cap_cur_auth aag cap; pas_refined aag s; is_cnode_cap cap \<rbrakk>
     \<Longrightarrow> \<forall>x\<in>obj_refs_ac cap. is_subject aag x"
  by (clarsimp simp: is_cap_simps cap_auth_conferred_def
                     pas_refined_all_auth_is_owns aag_cap_auth_def)

lemma get_cap_prop_imp:
  "\<lbrace>cte_wp_at (\<lambda>cap. P cap \<longrightarrow> Q cap) slot\<rbrace> get_cap slot \<lbrace>\<lambda>rv s. P rv \<longrightarrow> cte_wp_at Q slot s\<rbrace>"
  by (wpsimp wp: get_cap_wp simp: cte_wp_at_caps_of_state)

lemma get_cap_prop_imp2:
  "\<lbrace>cte_wp_at (\<lambda>cap. P cap) slot\<rbrace> get_cap slot \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  by (wpsimp wp: get_cap_wp simp: cte_wp_at_def)

lemma get_cap_cur_auth:
  "\<lbrace>pas_refined aag and cte_wp_at (\<lambda>_. True) slot and K (is_subject aag (fst slot))\<rbrace>
   get_cap slot
   \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag rv\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state cap_cur_auth_caps_of_state)
  done

lemma decode_cnode_inv_authorised:
  "\<lbrace>pas_refined aag and invs and valid_cap cap
                    and K (\<forall>c \<in> {cap} \<union> set excaps. pas_cap_cur_auth aag c)\<rbrace>
   decode_cnode_invocation label args cap excaps
   \<lbrace>\<lambda>rv s. authorised_cnode_inv aag rv s\<rbrace>,-"
  apply (simp add: authorised_cnode_inv_def decode_cnode_invocation_def
                   split_def whenE_def unlessE_def set_eq_iff
             cong: if_cong Invocations_A.cnode_invocation.case_cong split del: if_split)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_imp_lift_R hoare_vcg_all_liftE_R lsfco_cte_at
         | wp (once) get_cap_cur_auth)+
  apply (subgoal_tac "\<forall>n. n < length excaps
                          \<longrightarrow> (is_cnode_cap (excaps ! n)
                               \<longrightarrow> (\<forall>x\<in>obj_refs_ac (excaps ! n). is_subject aag x))")
   apply (fastforce simp: invs_valid_objs is_cnode_into_is_subject)
  apply (intro allI impI is_cnode_into_is_subject; fastforce)
  done

lemma set_cap_thread_st_auth[wp]:
  "set_cap cap ptr \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (wpsimp wp: get_object_wp simp: set_cap_def split_def set_object_def)
  apply (fastforce simp: obj_at_def get_tcb_def tcb_states_of_state_def
                         thread_st_auth_def rsubst[where P=P, OF _ ext])
  done

lemma set_cap_tcb_states_of_state[wp]:
  "set_cap cap ptr \<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def)
  apply (wpsimp wp: get_object_wp)
  apply (fastforce simp: obj_at_def get_tcb_def tcb_states_of_state_def rsubst[where P=P, OF _ ext])
  done

lemma set_cap_thread_bound_ntfns[wp]:
  "set_cap cap ptr \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (wpsimp wp: get_object_wp simp: set_cap_def split_def set_object_def)
  apply (fastforce simp: obj_at_def get_tcb_def thread_bound_ntfns_def rsubst[where P=P, OF _ ext])
  done

lemma sita_caps_update:
  "\<lbrakk> pas_wellformed aag; state_irqs_to_policy_aux aag caps \<subseteq> pasPolicy aag;
     cap_links_irq aag (pasObjectAbs aag (fst ptr)) cap \<rbrakk>
     \<Longrightarrow> state_irqs_to_policy_aux aag (caps(ptr \<mapsto> cap)) \<subseteq> pasPolicy aag"
  by (fastforce intro: state_irqs_to_policy_aux.intros
                 elim: state_irqs_to_policy_aux.cases
                 simp: cap_links_irq_def split: if_splits)

lemma sita_caps_update2:
  "\<lbrakk> pas_wellformed aag; state_irqs_to_policy_aux aag caps \<subseteq> pasPolicy aag;
     cap_links_irq aag (pasObjectAbs aag (fst ptr')) cap';
     cap_links_irq aag (pasObjectAbs aag (fst ptr)) cap \<rbrakk>
     \<Longrightarrow> state_irqs_to_policy_aux aag (caps(ptr \<mapsto> cap, ptr' \<mapsto> cap')) \<subseteq> pasPolicy aag"
  by (fastforce intro: state_irqs_to_policy_aux.intros
                 elim: state_irqs_to_policy_aux.cases
                 simp: cap_links_irq_def split: if_splits)


context CNode_AC_1 begin

lemma set_cap_pas_refined:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state and
    (\<lambda>s. (is_transferable_in ptr s \<and> (\<not> Option.is_none (cdt s ptr)))
          \<longrightarrow> is_transferable_cap cap \<or>
              abs_has_auth_to aag Control (fst $ the $ cdt s ptr) (fst ptr)) and
    K (aag_cap_auth aag (pasObjectAbs aag (fst ptr)) cap)\<rbrace>
   set_cap cap ptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def aag_cap_auth_def)
  apply (rule hoare_pre)
   apply (wp set_cap_caps_of_state set_cap_state_vrefs  | wps)+
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
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state
                    and cte_wp_at (\<lambda>c. \<not>is_transferable (Some c)) ptr
                    and K (aag_cap_auth aag (pasObjectAbs aag (fst ptr)) cap)\<rbrace>
   set_cap cap ptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  by (wpsimp wp: set_cap_pas_refined simp: cte_wp_at_caps_of_state)

end


(* FIXME MOVE *)
lemma parent_ofI[intro!]: "m x = Some src \<Longrightarrow> m \<Turnstile> src \<leadsto> x"
  by (simp add: cdt_parent_rel_def is_cdt_parent_def)

declare set_original_wp[wp del]


context CNode_AC_1 begin

lemma cap_move_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag
                       and K (is_subject aag (fst dest) \<and> is_subject aag (fst src))\<rbrace>
   cap_move cap src dest
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: cap_move_def)
   apply (wpsimp wp: get_cap_wp set_cap_integrity_autarch set_original_integrity_autarch
                     cap_move_ext_list_integ_lift[where Q="\<top>"] cap_move_list_integrity
               simp: set_cdt_def | blast)+
    apply (rule wp_integrity_clean')
     apply (simp add: integrity_def integrity_cdt_def)
     apply (blast intro: cca_owned)
    apply (wpsimp wp: set_cap_integrity_autarch)+
  done

lemma cap_swap_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag
                       and K (is_subject aag (fst slot) \<and> is_subject aag (fst slot'))\<rbrace>
   cap_swap cap slot cap' slot'
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: cap_swap_def)
  apply (wp get_cap_wp set_cap_integrity_autarch cap_swap_list_integrity
            cap_swap_ext_extended_list_integ_lift[where Q="\<top>"]
            set_original_integrity_autarch[unfolded pred_conj_def K_def]
         | simp add: set_cdt_def split del: if_split | blast)+
    apply (rule wp_integrity_clean')
     apply (simp add: integrity_def)
     apply (blast intro: cca_owned)
    apply (wpsimp wp: set_cap_integrity_autarch set_cap_pas_refined)+
  done

lemma cap_swap_for_delete_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag
                       and K (is_subject aag (fst slot) \<and> is_subject aag (fst slot'))\<rbrace>
   cap_swap_for_delete slot slot'
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (wpsimp simp: cap_swap_for_delete_def)

lemma dmo_no_mem_respects:
  assumes p: "\<And>P. mop \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes q: "\<And>P. mop \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  shows "do_machine_op mop \<lbrace>integrity aag X st\<rbrace>"
  unfolding do_machine_op_def
  apply (rule hoare_pre)
   apply (simp add: split_def)
   apply wp
  apply (clarsimp simp: integrity_def)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x = x in spec)+
   apply (erule (1) use_valid [OF _ p])
  apply clarsimp
  apply (drule_tac x = x in spec)+
  apply (erule (1) use_valid [OF _ q])
  done

lemma set_irq_state_respects[wp]:
  "\<lbrace>integrity aag X st and K (is_subject_irq aag irq)\<rbrace>
   set_irq_state irqst irq
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding set_irq_state_def
  by (wpsimp wp: dmo_no_mem_respects simp: integrity_subjects_def integrity_interrupts_def)

end


(* FIXME: MOVE *)
(* Only works after a hoare_pre! *)
lemma dmo_wp:
  assumes mopv: "\<And>s. \<lbrace>P s\<rbrace> mop \<lbrace>\<lambda>a b. R a (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P s (machine_state s)\<rbrace> do_machine_op mop \<lbrace>R\<rbrace>"
  by (wpsimp simp: do_machine_op_def use_valid[OF _ mopv])

lemmas cases_simp_options = cases_simp_option cases_simp_option[where 'a="'b \<times> 'c", simplified]

(* FIXME MOVE *)
lemma cdt_change_allowed_all_children:
  "all_children (cdt_change_allowed aag subject (cdt s) (tcb_states_of_state s)) (cdt s)"
  by (rule all_childrenI) (erule cdt_change_allowed_to_child)

abbreviation cleanup_info_wf :: "cap \<Rightarrow> 'a PAS \<Rightarrow> bool" where
  "cleanup_info_wf c aag \<equiv> c \<noteq> NullCap \<and> \<not>is_arch_cap c
                           \<longrightarrow> (\<exists>irq. c = (IRQHandlerCap irq) \<and> is_subject_irq aag irq)"

(* FIXME: MOVE *)
named_theorems wp_transferable
named_theorems wp_not_transferable


context CNode_AC_1 begin

crunches deleted_irq_handler
  for respects[wp]: "integrity aag X st"

lemma post_cap_deletion_integrity[wp]:
 "\<lbrace>integrity aag X s and K (cleanup_info_wf cleanup_info aag)\<rbrace>
  post_cap_deletion cleanup_info
  \<lbrace>\<lambda>_. integrity aag X s\<rbrace>"
  by (wpsimp simp: post_cap_deletion_def is_cap_simps wp: arch_post_cap_deletion_integrity)

lemma empty_slot_integrity_spec:
  notes split_paired_All[simp del]
  shows
  "s \<turnstile> \<lbrace>valid_list and valid_mdb and valid_objs and pas_refined aag
                   and K (is_subject aag (fst slot) \<and> cleanup_info_wf cleanup_info aag)\<rbrace>
       empty_slot slot cleanup_info
       \<lbrace>\<lambda>_. integrity aag X s\<rbrace>"
  apply (simp add: spec_valid_def)
  apply (simp add: empty_slot_def)
  apply (wp add: get_cap_wp set_cap_integrity_autarch set_original_integrity_autarch
                 empty_slot_extended_list_integ_lift empty_slot_list_integrity[where m="cdt s"]
         | simp add: set_cdt_def | wpc)+
  apply (safe; \<comment> \<open>for speedup\<close>
         (clarsimp simp add: integrity_def)?,
         blast intro: cca_owned cdt_change_allowed_all_children)
  done

lemma empty_slot_integrity[wp,wp_not_transferable]:
  "\<lbrace>integrity aag X st and valid_list and valid_objs and valid_mdb and pas_refined aag
                       and K (is_subject aag (fst slot) \<and> cleanup_info_wf c aag)\<rbrace>
   empty_slot slot c
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (integrity_trans_start)
  apply (rule hoare_pre)
   apply (wp empty_slot_integrity_spec[simplified spec_valid_def])
  by force

end

lemma reply_masters_mdbD1:
 "\<lbrakk> reply_masters_mdb m cs ; cs slot = Some (ReplyCap t True R) \<rbrakk>
    \<Longrightarrow> m slot = None"
  by (fastforce simp:reply_masters_mdb_def simp del:split_paired_All)

lemma reply_cap_no_grand_parent:
  "\<lbrakk> m \<Turnstile> pptr \<rightarrow>* slot ; reply_mdb m cs ; cs slot = Some (ReplyCap t False R) \<rbrakk>
     \<Longrightarrow> pptr = slot \<or> (m \<Turnstile> pptr \<leadsto> slot \<and> (\<exists> R'. cs pptr = Some (ReplyCap t True R')))"
  apply (clarsimp simp: reply_mdb_def del: disjCI)
  apply (erule(1) reply_caps_mdbE)
  apply (drule(1) reply_masters_mdbD1)
  apply (erule rtrancl.cases, blast)
  apply (erule rtrancl.cases, simp add: cdt_parent_of_def)
  apply (simp add: cdt_parent_of_def)
  done

(* FIXME MOVE ? *)
crunches set_cdt_list, update_cdt_list
  for cdt[wp]: "\<lambda>s. P (cdt s)"
  and kheap[wp]: "\<lambda>s. P (kheap s)"
  and valid_mdb[wp]: "\<lambda>s. P (valid_mdb s)"
  and valid_objs[wp]: "\<lambda>s. P (valid_objs s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and thread_st_auth[wp]: "\<lambda>s. P (thread_st_auth s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and is_original_cap[wp]: "\<lambda>s. P (is_original_cap s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"


locale CNode_AC_2 = CNode_AC_1 +
  assumes integrity_asids_set_cap_Nullcap:
    "\<lbrace>(=) s\<rbrace> set_cap NullCap slot \<lbrace>\<lambda>_. integrity_asids aag subjects x a (s :: det_ext state)\<rbrace>"
  and set_original_state_asids_to_policy[wp]:
    "\<And>P. set_original slot v \<lbrace>\<lambda>s. P (state_asids_to_policy aag s)\<rbrace>"
  and set_original_state_objs_to_policy[wp]:
    "\<And>P. set_original slot v \<lbrace>\<lambda>s. P (state_objs_to_policy s)\<rbrace>"
  and set_cdt_list_state_vrefs[wp]:
    "\<And>P. set_cdt_list t \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  and set_cdt_list_state_asids_to_policy[wp]:
    "\<And>P. set_cdt_list t \<lbrace>\<lambda>s. P (state_asids_to_policy aag s)\<rbrace>"
  and update_cdt_list_state_vrefs[wp]:
    "\<And>P. update_cdt_list f \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  and update_cdt_list_state_asids_to_policy[wp]:
    "\<And>P. update_cdt_list f \<lbrace>\<lambda>s. P (state_asids_to_policy aag s)\<rbrace>"
begin

crunches set_original
  for tcb_domain_map_wellformed[wp]: "\<lambda>s. P (tcb_domain_map_wellformed aag s)"
  and state_irqs_to_policy[wp]: "\<lambda>s. P (state_irqs_to_policy aag s)"
  and cdt_change_allowed[wp]: "\<lambda>s. P (cdt_change_allowed' aag slot s)"
  and irq_map_wellformed[wp]: "\<lambda>s. P (irq_map_wellformed aag s)"
  and pas_refined[wp]: "\<lambda>s. P (pas_refined aag s)"
  and valid_objs[wp]: "\<lambda>s. P (valid_objs s)"
  and cte_wp_at[wp]: "cte_wp_at P slot"
  (simp: state_objs_to_policy_def pas_refined_def)

lemma set_cap_integrity_deletion_aux:
  "\<lbrace>integrity aag X st and valid_mdb and valid_objs and pas_refined aag and is_transferable_in slot
                       and cdt_change_allowed' aag slot and K(\<not> is_subject aag (fst slot))\<rbrace>
   set_cap NullCap slot
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (integrity_trans_start)
  apply (rule hoare_pre)
   apply (unfold integrity_subjects_def)[1]
   apply (wp hoare_wp_combs)
    apply (unfold set_cap_def)[1]
    apply (wpc)
    apply (wp set_object_wp)
     apply wpc
         apply wp+
    apply (wp get_object_wp)
   apply wps
   apply (wp integrity_asids_set_cap_Nullcap hoare_vcg_all_lift)
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

lemma set_cap_integrity_deletion[wp_transferable]:
  "\<lbrace>integrity aag X st and valid_mdb and valid_objs
                       and pas_refined aag and cdt_change_allowed' aag slot\<rbrace>
   set_cap NullCap slot
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (cases "is_subject aag (fst slot)")
   apply (wpsimp wp: set_cap_integrity_autarch)
  apply (wpsimp wp: set_cap_integrity_deletion_aux)
  by (fastforce dest: cca_to_transferable_or_subject simp: cte_wp_at_caps_of_state)

lemma update_cdt_list_pas_refined[wp]:
  "update_cdt_list f \<lbrace>pas_refined aag\<rbrace>"
  by (wpsimp simp: pas_refined_def state_objs_to_policy_def | wps)+

end


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
  "(\<And>s0. \<lbrace>(=) s0\<rbrace> g \<lbrace>\<lambda>r t. s0 = t\<rbrace>)
   \<Longrightarrow> monad_commute (\<lambda>s. fst ` fst (g (f s)) = fst ` fst (g s) \<and>
                          snd (g (f s)) = snd (g s)) (modify f) g"
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
  by (monad_eq simp: monad_commute_def valid_def) fastforce

lemma assert_commute':
  "empty_fail f \<Longrightarrow> monad_commute \<top> (assert G) f"
  by (monad_eq simp: monad_commute_def empty_fail_def) fastforce


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
  "monad_commute P f g \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') (monad_commute P f g)"
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
   (do empty_slot_ext slot slot_p; set_cdt c od)"
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
   (do empty_slot_ext slot' slot_p; set_cap cap slot od)"
  apply (rule ext)
  apply (clarsimp simp: bind_def split_def set_cap_def empty_slot_ext_def
                        update_cdt_list_def set_cdt_list_def
                        get_object_def set_object_def get_def put_def
                        simpler_gets_def simpler_modify_def
                        assert_def fail_def)
  apply (case_tac y; simp add: return_def fail_def split: option.splits)
  done

lemma K_bind_assoc:
  "(do (do f; g od); h od) = (do f; g; h od)"
  by (simp add: bind_assoc)
lemmas K_bind_eqI = arg_cong2[where f="\<lambda>f g. do f; g od"]
lemmas K_bind_eqI' = K_bind_eqI[OF _ refl]

lemma aag_cap_auth_max_free_index_update[simp]:
  "aag_cap_auth aag (pasObjectAbs aag x) (max_free_index_update y) =
   aag_cap_auth aag (pasObjectAbs aag x) y"
  by (clarsimp simp: aag_cap_auth_def free_index_update_def cap_links_asid_slot_def cap_links_irq_def
              split: cap.splits)


context CNode_AC_2 begin

(* Putting it all together *)
lemma empty_slot_shuffle:
  "(do set_cdt c;
       empty_slot_ext slot slot_p;
       set_original slot False;
       set_cap NullCap slot;
       post_cap_deletion NullCap od) =
   (do set_cap NullCap slot;
       empty_slot_ext slot slot_p;
       set_original slot False;
       set_cdt c;
       post_cap_deletion NullCap od :: (det_ext state \<Rightarrow> _))"
  by (simp only: set_cdt_empty_slot_ext_comm[THEN K_bind_eqI', simplified K_bind_assoc]
                 set_cdt_set_original_comm[THEN K_bind_eqI', simplified K_bind_assoc]
                 set_cdt_set_cap_comm[THEN K_bind_eqI', simplified K_bind_assoc]
                 set_original_set_cap_comm[THEN K_bind_eqI', simplified K_bind_assoc]
                 set_cap_empty_slot_ext_comm[THEN K_bind_eqI', simplified K_bind_assoc])

lemma empty_slot_integrity_transferable[wp_transferable]:
  "\<lbrace>integrity aag X st and valid_list and valid_objs and valid_mdb and pas_refined aag
                       and cdt_change_allowed' aag slot and K (c = NullCap)\<rbrace>
   empty_slot slot c
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
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
       apply (wp empty_slot_extended_list_integ_lift)
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
                abs_has_auth_to aag Control (fst y) (fst x)) \<and>
               abs_has_auth_to aag DeleteDerived (fst y) (fst x))\<rbrace>
         set_cdt c
         \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def set_cdt_def)
  apply (wp | simp | simp_all)+
  apply (clarsimp dest!: auth_graph_map_memD)
  apply (subgoal_tac
          "\<forall>x y. c x = Some y \<longrightarrow>
            (is_transferable (caps_of_state s x) \<or> abs_has_auth_to aag Control (fst y) (fst x))
          \<and> abs_has_auth_to  aag DeleteDerived (fst y) (fst x)")
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

crunches deleted_irq_handler
  for pas_refined[wp]: "pas_refined aag"

crunches set_untyped_cap_as_full
  for pas_refined: "pas_refined aag"

lemmas set_untyped_cap_as_full_pas_refined'[wp] = set_untyped_cap_as_full_pas_refined[simplified]

lemma update_cdt_pas_refined:
  "\<lbrace>pas_refined aag and (\<lambda>s. \<forall>x y. c (cdt s) x = Some y \<and> cdt s x \<noteq> Some y
                                   \<longrightarrow> (is_transferable (caps_of_state s x) \<or>
                                        abs_has_auth_to aag Control (fst y) (fst x))
                                     \<and> abs_has_auth_to aag DeleteDerived (fst y) (fst x))\<rbrace>
   update_cdt c
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: update_cdt_def)
  apply (wp set_cdt_pas_refined)
  apply simp
  done

lemma state_objs_to_policy_more_update[simp]:
  "state_objs_to_policy (trans_state f s) =
   state_objs_to_policy s"
  by (simp add: state_objs_to_policy_def)

end


lemma set_untyped_cap_as_full_cdt_is_original_cap:
  "\<lbrace>\<lambda>s. P (cdt s) (is_original_cap s)\<rbrace>
   set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace>\<lambda>_ s. P (cdt s) (is_original_cap s)\<rbrace>"
  unfolding set_untyped_cap_as_full_def
  apply (rule hoare_pre)
  apply (wp set_cap_caps_of_state2)
  apply clarsimp
  done

(* FIXME MOVE *)
lemma untyped_not_transferable:
  "is_untyped_cap cap \<Longrightarrow> \<not> is_transferable (Some cap)"
  by (fastforce simp: is_cap_simps elim!: is_transferable.cases)

(* FIXME MOVE *)
lemma is_transferable_max_free_index_update[simp]:
 "is_transferable (Some (max_free_index_update cap)) = is_transferable (Some cap)"
  by (simp add: is_transferable.simps free_index_update_def split: cap.splits)

lemma set_untyped_cap_as_full_is_transferable[wp]:
  "set_untyped_cap_as_full src_cap new_cap slot \<lbrace>\<lambda>s. \<not> is_transferable (caps_of_state s other_slot)\<rbrace>"
  apply (clarsimp simp: set_untyped_cap_as_full_def)
  apply wp
  using untyped_not_transferable max_free_index_update_preserve_untyped by simp

lemma set_untyped_cap_as_full_is_transferable':
  "\<lbrace>\<lambda>s. is_transferable (((caps_of_state s)(slot2 \<mapsto> new_cap)) slot3) \<and>
        Some src_cap = (caps_of_state s slot)\<rbrace>
   set_untyped_cap_as_full src_cap new_cap slot
   \<lbrace>\<lambda>_ s. is_transferable (((caps_of_state s)(slot2 \<mapsto> new_cap)) slot3)\<rbrace>"
  apply (clarsimp simp: set_untyped_cap_as_full_def)
  apply safe
  apply (wp,fastforce)+
  done

lemma cap_links_irq_Nullcap [simp]:
  "cap_links_irq aag l NullCap" unfolding cap_links_irq_def by simp

lemma aag_cap_auth_NullCap [simp]:
  "aag_cap_auth aag l NullCap"
  unfolding aag_cap_auth_def
  by (simp add: clas_no_asid)

crunches set_cdt
  for thread_st_auth[wp]: "\<lambda>s. P (thread_st_auth s)"
crunches set_cdt
  for thread_bound_ntfns[wp]: "\<lambda>s. P (thread_bound_ntfns s)"


locale CNode_AC_3 = CNode_AC_2 +
  assumes cap_move_ext_pas_refined_tcb_domain_map_wellformed[wp]:
    "\<And>a b c d. cap_move_ext a b c d \<lbrace>tcb_domain_map_wellformed aag\<rbrace>
                \<Longrightarrow> cap_move_ext a b c d \<lbrace>pas_refined aag\<rbrace>"
  and cap_insert_ext_pas_refined_tcb_domain_map_wellformed[wp]:
    "\<And>a b c d e. cap_insert_ext a b c d e \<lbrace>tcb_domain_map_wellformed aag\<rbrace>
                  \<Longrightarrow> cap_insert_ext a b c d e \<lbrace>pas_refined aag\<rbrace>"
  and cap_swap_ext_extended_pas_refined_tcb_domain_map_wellformed[wp]:
    "\<And>a b c d. cap_swap_ext a b c d \<lbrace>tcb_domain_map_wellformed aag\<rbrace>
                \<Longrightarrow> cap_swap_ext a b c d \<lbrace>pas_refined aag\<rbrace>"
  and empty_slot_ext_pas_refined_tcb_domain_map_wellformed[wp]:
    "\<And>a b. empty_slot_ext a b \<lbrace>tcb_domain_map_wellformed aag\<rbrace>
            \<Longrightarrow> empty_slot_ext a b \<lbrace>pas_refined aag\<rbrace>"
  and arch_ost_cap_deletion_pas_refined[wp]:
    "arch_post_cap_deletion irqopt \<lbrace>pas_refined aag\<rbrace>"
  and aobj_ref'_same_aobject:
    "same_aobject_as ao' ao \<Longrightarrow> aobj_ref' ao = aobj_ref' ao'"
  and set_untyped_cap_as_full_valid_arch_state[wp]:
    "set_untyped_cap_as_full src_cap new_cap src_slot \<lbrace>\<lambda>s :: det_ext state. valid_arch_state s\<rbrace>"
begin

lemma cap_insert_pas_refined:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state and valid_mdb and
    (\<lambda>s. (is_transferable_in src_slot s \<and> (\<not> Option.is_none (cdt s src_slot)))
         \<longrightarrow> is_transferable_cap new_cap) and
    K (is_subject aag (fst dest_slot) \<and> is_subject aag (fst src_slot)
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
                 simp: cte_wp_at_caps_of_state pas_refined_refl F[symmetric]
                       valid_mdb_def2 mdb_cte_at_def Option.is_none_def
             simp del: split_paired_All
                 dest: aag_cdt_link_Control aag_cdt_link_DeleteDerived cap_auth_caps_of_state)

lemma cap_insert_pas_refined':
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state and valid_mdb and
    (\<lambda>s. cte_wp_at is_transferable_cap src_slot s \<longrightarrow> is_transferable_cap new_cap) and
    K (is_subject aag (fst dest_slot) \<and> is_subject aag (fst src_slot)
                                      \<and> pas_cap_cur_auth aag new_cap) \<rbrace>
   cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  by (wp cap_insert_pas_refined)
     (fastforce dest: valid_mdb_mdb_cte_at[THEN mdb_cte_atD[rotated]]
                simp: cte_wp_at_caps_of_state Option.is_none_def)

lemma cap_insert_pas_refined_not_transferable:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state and valid_mdb
                    and not cte_wp_at is_transferable_cap src_slot
                    and K (is_subject aag (fst dest_slot) \<and> is_subject aag (fst src_slot)
                                                          \<and> pas_cap_cur_auth aag new_cap) \<rbrace>
   cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
   by (wpsimp wp: cap_insert_pas_refined')

lemma cap_insert_pas_refined_same_object_as:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state and valid_mdb
                    and cte_wp_at (same_object_as new_cap) src_slot
                    and K (is_subject aag (fst dest_slot) \<and> is_subject aag (fst src_slot) \<and>
                           (\<not> is_master_reply_cap new_cap) \<and> pas_cap_cur_auth aag new_cap)\<rbrace>
   cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (wp cap_insert_pas_refined)
  apply (clarsimp simp: Option.is_none_def cte_wp_at_caps_of_state)
  by (fastforce simp: same_object_as_commute is_master_reply_cap_def same_object_as_def
                elim: is_transferable_capE split: cap.splits)

lemma cap_move_pas_refined[wp]:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state
                    and valid_mdb and cte_wp_at (weak_derived new_cap) src_slot
                    and cte_wp_at ((=) NullCap) dest_slot
                    and K (is_subject aag (fst dest_slot) \<and> is_subject aag (fst src_slot)
                                                          \<and> pas_cap_cur_auth aag new_cap)\<rbrace>
   cap_move new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: cap_move_def)
  apply (rule hoare_pre)
   apply (wpsimp wp: set_cap_caps_of_state2 set_cap_pas_refined set_cdt_pas_refined
                     tcb_domain_map_wellformed_lift)
  by (fastforce simp: is_transferable_weak_derived valid_mdb_def2 mdb_cte_at_def
                      Option.is_none_def cte_wp_at_caps_of_state
            simp del: split_paired_All
                elim: pas_refined_refl
                dest: invs_mdb pas_refined_mem[OF sta_cdt]
                      pas_refined_mem[OF sta_cdt_transferable])

crunches set_original, set_cdt
  for pspace_aligned[wp]: pspace_aligned
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_arch_state[wp]: valid_arch_state

lemma empty_slot_pas_refined[wp, wp_not_transferable]:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state
                    and valid_mdb and K (is_subject aag (fst slot))\<rbrace>
   empty_slot slot irqopt
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: empty_slot_def post_cap_deletion_def)
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp set_cdt_pas_refined
                    tcb_domain_map_wellformed_lift hoare_drop_imps)
  apply (strengthen aag_wellformed_delete_derived_trans[OF _ _ pas_refined_wellformed, mk_strg I _ _ A])
  by (fastforce dest: all_childrenD is_transferable_all_children
                      pas_refined_mem[OF sta_cdt] pas_refined_mem[OF sta_cdt_transferable]
                      pas_refined_Control)


lemma empty_slot_pas_refined_transferable[wp_transferable]:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state
                    and valid_mdb and (\<lambda>s. is_transferable (caps_of_state s slot))\<rbrace>
   empty_slot slot irqopt
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: empty_slot_def post_cap_deletion_def)
  apply (wpsimp wp: set_cap_pas_refined get_cap_wp set_cdt_pas_refined
                    tcb_domain_map_wellformed_lift hoare_drop_imps)
  apply (strengthen aag_wellformed_delete_derived_trans[OF _ _ pas_refined_wellformed, mk_strg I _ _ A])
  by (fastforce simp: cte_wp_at_caps_of_state
                dest: all_childrenD is_transferable_all_children
                      pas_refined_mem[OF sta_cdt] pas_refined_mem[OF sta_cdt_transferable])

lemma obj_ref_weak_derived:
  "weak_derived cap cap' \<Longrightarrow> obj_refs_ac cap = obj_refs_ac cap'"
  unfolding obj_refs_def weak_derived_def copy_of_def same_object_as_def
  by (cases cap; fastforce simp: is_cap_simps aobj_ref'_same_aobject split: cap.splits)

lemma cap_swap_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and cte_wp_at (weak_derived cap) slot
                    and cte_wp_at (weak_derived cap') slot'
                    and K (is_subject aag (fst slot) \<and> is_subject aag (fst slot') \<and>
                           pas_cap_cur_auth aag cap \<and> pas_cap_cur_auth aag cap')\<rbrace>
   cap_swap cap slot cap' slot'
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (rule hoare_pre)
   apply (wp add: tcb_domain_map_wellformed_lift | simp split del: if_split)+
        apply (simp only:pas_refined_def state_objs_to_policy_def)
        apply (wps | wp set_cap_state_vrefs set_cdt_cdt_ct_ms_rvk set_cap_caps_of_state)+
  apply (clarsimp simp: pas_refined_def aag_cap_auth_def state_objs_to_policy_def
                        cte_wp_at_caps_of_state
                 split: if_split_asm split del: if_split)
  apply (rename_tac old_cap old_cap')
  apply (intro conjI)
    apply (find_goal \<open>match conclusion in "state_asids_to_policy_arch _ _ _ _ \<subseteq> _" \<Rightarrow> succeed\<close>)
    apply (erule sata_update2[unfolded fun_upd_def]; fastforce)
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
         apply (blast intro: state_bits_to_policy.intros auth_graph_map_memI)
   by fastforce+

lemma cap_swap_for_delete_pas_refined[wp]:
  "\<lbrace>pas_refined aag and invs and K (is_subject aag (fst slot) \<and> is_subject aag (fst slot'))\<rbrace>
   cap_swap_for_delete slot slot'
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state )
  apply (fastforce dest!: cap_cur_auth_caps_of_state)
  done

lemma sts_respects_restart_ep:
  "\<lbrace>integrity aag X st and
    (\<lambda>s. \<exists>ep. aag_has_auth_to aag Reset ep \<and> st_tcb_at (blocked_on ep) thread s)\<rbrace>
   set_thread_state thread Restart
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def obj_at_def st_tcb_at_def get_tcb_def integrity_asids_kh_upds)
  apply (rule_tac tro_tcb_restart [OF refl refl])
    apply (fastforce dest!: get_tcb_SomeD)
   apply (fastforce dest!: get_tcb_SomeD)
  apply simp
  done

lemma set_endpoint_respects:
  "\<lbrace>integrity aag X st and ep_at epptr and
    K (\<exists>auth. aag_has_auth_to aag auth epptr \<and> auth \<in> {Receive, SyncSend, Reset})\<rbrace>
   set_endpoint epptr ep'
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def partial_inv_def a_type_def)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def tro_ep integrity_asids_kh_upds)
  done

end


lemma mapM_mapM_x_valid:
  "\<lbrace>P\<rbrace> mapM_x f xs \<lbrace>\<lambda>rv. Q\<rbrace> = \<lbrace>P\<rbrace> mapM f xs \<lbrace>\<lambda>rv. Q\<rbrace>"
  by (simp add: mapM_x_mapM liftM_def[symmetric] hoare_liftM_subst)


lemma sts_thread_bound_ntfns[wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: thread_bound_ntfns_def get_tcb_def
                 split: if_split option.splits kernel_object.splits
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma sts_thread_st_auth[wp]:
  "\<lbrace>\<lambda>s. P ((thread_st_auth s)(t := tcb_st_to_auth st))\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_ s. P (thread_st_auth s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: get_tcb_def thread_st_auth_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

lemma sbn_thread_bound_ntfns[wp]:
  "\<lbrace>\<lambda>s. P ((thread_bound_ntfns s)(t := ntfn))\<rbrace>
   set_bound_notification t ntfn
   \<lbrace>\<lambda>_ s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: get_tcb_def thread_bound_ntfns_def
                 elim!: rsubst[where P=P, OF _ ext])
  done

(* FIXME move to AInvs *)
lemma set_thread_state_ekheap[wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_scheduler_action_wp simp: set_thread_state_ext_def)
  done

lemma set_simple_ko_tcb_states_of_state[wp]:
  "set_simple_ko f ptr val \<lbrace>\<lambda>s. P (tcb_states_of_state s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (clarsimp simp: thread_st_auth_def obj_at_def get_tcb_def tcb_states_of_state_def
                        partial_inv_def a_type_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm if_splits)
  done

lemma set_simple_ko_thread_st_auth[wp]:
  "set_simple_ko f ptr val \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (clarsimp simp: thread_st_auth_def obj_at_def get_tcb_def tcb_states_of_state_def
                        partial_inv_def a_type_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm if_splits)
  done

lemma set_simple_ko_thread_bound_ntfns[wp]:
  "set_simple_ko f ptr val \<lbrace>\<lambda>s. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (clarsimp simp: thread_bound_ntfns_def obj_at_def get_tcb_def tcb_states_of_state_def
                        partial_inv_def a_type_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm if_splits)
  done

(* FIXME move to AInvs *)
lemma set_simple_ko_ekheap[wp]:
  "set_simple_ko f ptr ep \<lbrace>\<lambda>s. P (ekheap s)\<rbrace>"
  apply (simp add: set_simple_ko_def)
  apply (wpsimp wp: get_object_wp)
  done


context CNode_AC_3 begin

lemma sts_st_vrefs[wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_ s :: det_ext state. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_thread_state_def del: set_thread_state_ext_extended.dxo_eq)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: state_vrefs_tcb_upd obj_at_def is_obj_defs
                 elim!: rsubst[where P=P, OF _ ext]
                 dest!: get_tcb_SomeD)
  done

lemma set_thread_state_pas_refined:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state and
    K (\<forall>r \<in> tcb_st_to_auth st. abs_has_auth_to aag (snd r) t (fst r))\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply (clarsimp dest!: auth_graph_map_memD)
  apply (erule state_bits_to_policy.cases;
         auto intro: state_bits_to_policy.intros auth_graph_map_memI
              split: if_split_asm)
  done

lemma set_simple_ko_vrefs[wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
   set_simple_ko f ptr (val :: 'b)
   \<lbrace>\<lambda>_ s :: det_ext state. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply (fastforce simp: state_vrefs_simple_type_upd obj_at_def elim!: rsubst[where P=P, OF _ ext])
  done

lemma set_simple_ko_pas_refined[wp]:
  "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state\<rbrace>
    set_simple_ko f ptr (ep :: 'b) \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: pas_refined_def state_objs_to_policy_def)
  apply (rule hoare_pre)
   apply (wp tcb_domain_map_wellformed_lift | wps)+
  apply simp
  done

lemma thread_set_state_vrefs:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and (\<lambda>s. P (state_vrefs s))\<rbrace>
   thread_set f t
   \<lbrace>\<lambda>_ s :: det_ext state. P (state_vrefs s)\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: state_vrefs_tcb_upd obj_at_def is_obj_defs
                 dest!: get_tcb_SomeD)
  done

end


lemma thread_set_thread_st_auth_trivT:
  assumes st: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  shows "thread_set f t \<lbrace>\<lambda>s. P (thread_st_auth s)\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: st get_tcb_def thread_st_auth_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm)
  done

lemma thread_set_thread_bound_ntfns_trivT:
  assumes ntfn: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  shows "thread_set f t \<lbrace>\<lambda>s :: det_ext state. P (thread_bound_ntfns s)\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: ntfn get_tcb_def thread_bound_ntfns_def tcb_states_of_state_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: kernel_object.split_asm)
  done


context CNode_AC_3 begin

lemma thread_set_pas_refined_triv:
  assumes cps: "\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb"
       and st: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
      and ntfn: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
     shows "\<lbrace>pas_refined aag and pspace_aligned and valid_vspace_objs and valid_arch_state\<rbrace>
            thread_set f t \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  by (wpsimp wp: tcb_domain_map_wellformed_lift thread_set_state_vrefs
           simp: pas_refined_def state_objs_to_policy_def
      | wps thread_set_caps_of_state_trivial[OF cps]
            thread_set_thread_st_auth_trivT[OF st]
            thread_set_thread_bound_ntfns_trivT[OF ntfn])+

lemmas thread_set_pas_refined = thread_set_pas_refined_triv[OF ball_tcb_cap_casesI]

end


lemma aag_owned_cdt_link:
  "\<lbrakk> cdt s x = Some y; is_subject aag (fst y);
     pas_refined aag s; \<not> is_transferable (caps_of_state s x) \<rbrakk>
     \<Longrightarrow> is_subject aag (fst x)"
  by (fastforce dest: sta_cdt pas_refined_mem pas_refined_Control)

(* FIXME: MOVE *)
lemma descendants_of_owned_or_transferable:
  "\<lbrakk> valid_mdb s; pas_refined aag s; p \<in> descendants_of q (cdt s); is_subject aag (fst q) \<rbrakk>
     \<Longrightarrow> is_subject aag (fst p) \<or> is_transferable (caps_of_state s p)"
   using all_children_descendants_of pas_refined_all_children by blast


context CNode_AC_3 begin

lemma set_ntfn_respects:
  "\<lbrace>integrity aag X st and
    K (\<exists>auth. aag_has_auth_to aag auth epptr \<and> auth \<in> {Receive, Notify, Reset})\<rbrace>
   set_notification epptr ep'
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def partial_inv_def a_type_def)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def tro_ntfn integrity_asids_kh_upds)
  done

crunches thread_set
  for integrity_autarch: "integrity aag X st"

end


lemma sta_ts_mem:
  "\<lbrakk> thread_st_auth s x = S; r \<in> S \<rbrakk> \<Longrightarrow> (x, snd r, fst r) \<in> state_objs_to_policy s"
  using sta_ts by force

lemma get_cap_auth_wp:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and> is_subject aag (fst p) \<and>
        (\<forall>cap. caps_of_state s p = Some cap \<and> pas_cap_cur_auth aag cap \<longrightarrow> Q cap s)\<rbrace>
   get_cap p \<lbrace>Q\<rbrace>"
  apply (wp get_cap_wp)
  apply clarsimp
  apply (drule spec, erule mp)
  apply (fastforce simp: cte_wp_at_caps_of_state dest: cap_cur_auth_caps_of_state)
  done

lemma get_cap_auth_conferred:
  "\<lbrace>pas_refined aag and K (is_subject aag (fst slot))\<rbrace>
   get_cap slot
   \<lbrace>\<lambda>rv s. \<forall>x\<in>obj_refs_ac rv. \<forall>a \<in> cap_auth_conferred rv. aag_has_auth_to aag a x\<rbrace>"
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
  apply (clarsimp simp: valid_def)
  apply (frule get_cap_det)
  apply (drule_tac f=fst in arg_cong)
  apply (subst (asm) fst_conv)
  apply (drule in_get_cap_cte_wp_at[THEN iffD1])
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule caps_of_state_pasObjectAbs_eq)
      apply (blast intro: sym)
     apply (blast intro: cap_auth_conferred_cnode_cap)
    apply assumption+
  apply (case_tac a, simp_all)
  done

definition auth_derived :: "cap \<Rightarrow> cap \<Rightarrow> bool" where
 "auth_derived cap cap' \<equiv>
    (cap_asid' cap \<subseteq> cap_asid' cap')
  \<and> (untyped_range cap = untyped_range cap')
  \<and> (obj_refs_ac cap = obj_refs_ac cap')
  \<and> (cap_auth_conferred cap \<subseteq> cap_auth_conferred cap')
  \<and> (cap_irqs_controlled cap = cap_irqs_controlled cap')"

definition cnode_inv_auth_derivations ::
  "Invocations_A.cnode_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "cnode_inv_auth_derivations ci \<equiv> case ci of
     InsertCall cap ptr ptr' \<Rightarrow> cte_wp_at (auth_derived cap) ptr
   | MoveCall cap ptr ptr' \<Rightarrow> cte_wp_at (auth_derived cap) ptr
   | RotateCall s_cap p_cap src pivot dest \<Rightarrow>
       cte_wp_at (auth_derived s_cap) src and cte_wp_at (auth_derived p_cap) pivot
   | _ \<Rightarrow> \<top>"

lemma UNIV_eq_single_card:
  "(UNIV = {x :: 'a}) \<Longrightarrow> (card (UNIV :: 'a set) = 1)"
  by (erule ssubst) simp

lemma cli_cap_irqs_controlled:
  "(cap_irqs_controlled cap = cap_irqs_controlled cap') \<Longrightarrow>
    cap_links_irq aag (pasSubject aag) cap = cap_links_irq aag (pasSubject aag) cap'"
  by (auto simp: card_word cap_links_irq_def split: cap.splits
          dest!: UNIV_eq_single_card UNIV_eq_single_card [OF sym])

lemma auth_derived_caps_of_state_impls:
  "\<lbrakk> auth_derived cap cap'; caps_of_state s ptr = Some cap';
     pas_refined aag s; is_subject aag (fst ptr) \<rbrakk>
     \<Longrightarrow> pas_cap_cur_auth aag cap"
  unfolding aag_cap_auth_def
  apply (frule (1) clas_caps_of_state)
  apply (frule (1) cli_caps_of_state)
  apply (clarsimp simp: auth_derived_def cap_links_asid_slot_def cong: cli_cap_irqs_controlled)
  apply (auto dest: pas_refined_mem[OF sta_untyped] pas_refined_mem[OF sta_caps])
  done

crunches deleted_irq_handler
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"

lemma preemption_point_cur_domain[wp]:
  "preemption_point \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  by (wp preemption_point_inv', simp+)

lemma cnode_inv_auth_derivations_If_Insert_Move:
  "cnode_inv_auth_derivations ((if P then MoveCall else InsertCall) cap src_slot dest_slot) =
   cnode_inv_auth_derivations (MoveCall cap src_slot dest_slot)"
  by (simp add: cnode_inv_auth_derivations_def)


context CNode_AC_3 begin

lemma post_cap_deletion_cur_domain[wp]:
  "post_cap_deletion c \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  by (wpsimp simp: post_cap_deletion_def)

crunches cap_swap_for_delete, empty_slot
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps hoare_vcg_if_lift2 simp: unless_def)

crunches finalise_cap
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (wp: crunch_wps hoare_vcg_if_lift2 simp: unless_def)

lemma rec_del_cur_domain[wp]:
  "rec_del call \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  by (rule rec_del_preservation; wp)

crunches cap_delete
  for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"

lemma cap_revoke_cur_domain[wp]:
  "cap_revoke slot \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>"
  by (rule cap_revoke_preservation2; wp)

end


locale CNode_AC_4 = CNode_AC_3 +
  assumes cap_asid'_cap_rights_update[simp]:
    "acap_asid' (acap_rights_update rights ao) = acap_asid' ao"
  and untyped_range_cap_rights_update[simp]:
    "untyped_range (cap_rights_update rights (ArchObjectCap ao)) = untyped_range (ArchObjectCap ao)"
  and obj_refs_cap_rights_update[simp]:
    "aobj_ref' (acap_rights_update rights ao) = aobj_ref' ao"
  and auth_derived_arch_update_cap_data:
    "auth_derived (ArchObjectCap ao) cap' \<Longrightarrow> auth_derived (arch_update_cap_data pres w ao) cap'"
  and acap_auth_conferred_acap_rights_update:
    "arch_cap_auth_conferred (acap_rights_update (acap_rights acap \<inter> R) acap)
     \<subseteq> arch_cap_auth_conferred acap"
  and arch_derive_cap_auth_derived:
    "\<lbrace>\<lambda>s :: det_ext state. cte_wp_at (auth_derived (ArchObjectCap cap)) src_slot s\<rbrace>
     arch_derive_cap cap
     \<lbrace>\<lambda>rv s. cte_wp_at (auth_derived rv) src_slot s\<rbrace>, -"
  and arch_derive_cap_clas:
    "\<lbrace>\<lambda>s :: det_ext state. cap_links_asid_slot aag p (ArchObjectCap acap) \<rbrace>
     arch_derive_cap acap
     \<lbrace>\<lambda>rv s. cap_links_asid_slot aag p rv\<rbrace>, -"
  and arch_derive_cap_obj_refs_auth:
    "\<lbrace>K (\<forall>r\<in>obj_refs_ac (ArchObjectCap cap).
         \<forall>auth\<in>cap_auth_conferred (ArchObjectCap cap). aag_has_auth_to aag auth r)\<rbrace>
     arch_derive_cap cap
     \<lbrace>\<lambda>x s :: det_ext state. \<forall>r\<in>obj_refs_ac x.
                             \<forall>auth \<in> cap_auth_conferred x. aag_has_auth_to aag auth r\<rbrace>, -"
  and arch_derive_cap_obj_refs_subset:
    "\<lbrace>\<lambda>s :: det_ext state. (\<forall>x \<in> aobj_ref' acap. P x s)\<rbrace>
     arch_derive_cap acap
     \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs_ac rv. P x s\<rbrace>, -"
  and arch_derive_cap_cli:
    "\<lbrace>K (cap_links_irq aag l (ArchObjectCap ac))\<rbrace>
     arch_derive_cap ac
     \<lbrace>\<lambda>x (s :: det_ext state). cap_links_irq aag l x\<rbrace>, -"
  and arch_derive_cap_untyped_range_subset:
    "\<lbrace>\<lambda>s. \<forall>x \<in> untyped_range (ArchObjectCap acap). P x s\<rbrace>
     arch_derive_cap acap
     \<lbrace>\<lambda>rv s. \<forall>x \<in> untyped_range rv. P x s\<rbrace>, -"
  and arch_update_cap_obj_refs_subset:
    "\<lbrakk> x \<in> obj_refs_ac (arch_update_cap_data pres data cap) \<rbrakk> \<Longrightarrow> x \<in> aobj_ref' cap"
  and arch_update_cap_untyped_range_empty[simp]:
    "untyped_range (arch_update_cap_data pres data cap) = {}"
  and arch_update_cap_irqs_controlled_empty[simp]:
    "cap_irqs_controlled (arch_update_cap_data pres data cap) = {}"
  and arch_update_cap_links_asid_slot:
    "cap_links_asid_slot aag p (arch_update_cap_data pres w acap) =
     cap_links_asid_slot aag p (ArchObjectCap acap)"
  and arch_update_cap_cap_auth_conferred_subset:
    "y \<in> cap_auth_conferred (arch_update_cap_data b w acap)
     \<Longrightarrow> y \<in> arch_cap_auth_conferred acap"
begin

lemma derive_cap_auth_derived:
  "\<lbrace>\<lambda>s :: det_ext state. cap \<noteq> NullCap \<longrightarrow> cte_wp_at (auth_derived cap) src_slot s\<rbrace>
   derive_cap src_slot cap
   \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> cte_wp_at (auth_derived rv) src_slot s\<rbrace>, -"
  apply (wpsimp wp: arch_derive_cap_auth_derived simp: derive_cap_def | wp hoare_drop_imps)+
  apply (auto simp: cte_wp_at_caps_of_state)
  done

lemma cap_rights_to_auth_mono:
  "R \<subseteq> R' \<Longrightarrow> cap_rights_to_auth R b \<subseteq> cap_rights_to_auth R' b"
  by (auto simp add: cap_rights_to_auth_def)

lemma auth_derived_mask_cap:
  "auth_derived cap cap' \<Longrightarrow> auth_derived (mask_cap R cap) cap'"
  using cap_rights_update_def acap_auth_conferred_acap_rights_update
  by (simp add: mask_cap_def split: cap.splits)
     (fastforce simp: cap_auth_conferred_def auth_derived_def
                      cap_rights_to_auth_def reply_cap_rights_to_auth_def
               split: if_splits)

lemma auth_derived_update_cap_data:
  "\<lbrakk> auth_derived cap cap'; update_cap_data pres w cap \<noteq> NullCap \<rbrakk>
     \<Longrightarrow> auth_derived (update_cap_data pres w cap) cap'"
  apply (clarsimp simp: update_cap_data_def badge_update_def Let_def split_def
                        is_cap_simps auth_derived_arch_update_cap_data
                 split: if_split_asm)
  apply (simp_all add: auth_derived_def cap_auth_conferred_def the_cnode_cap_def)
  done

lemma cte_wp_at_auth_derived_mask_cap_strg:
  "cte_wp_at (auth_derived cap) p s
   \<longrightarrow> cte_wp_at (auth_derived (mask_cap R cap)) p s"
  by (clarsimp simp: cte_wp_at_caps_of_state auth_derived_mask_cap)

lemma cte_wp_at_auth_derived_update_cap_data_strg:
  "cte_wp_at (auth_derived cap) p s \<and> update_cap_data pres w cap \<noteq> NullCap
   \<longrightarrow> cte_wp_at (auth_derived (update_cap_data pres w cap)) p s"
  by (clarsimp simp: cte_wp_at_caps_of_state auth_derived_update_cap_data)

lemma get_cap_auth_derived:
  "\<lbrace>\<top>\<rbrace> get_cap slot \<lbrace>\<lambda>rv. cte_wp_at (auth_derived rv) slot\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state auth_derived_def)
  done

lemma decode_cnode_invocation_auth_derived:
  "\<lbrace>\<top> :: det_ext state \<Rightarrow> bool\<rbrace>
   decode_cnode_invocation label args cap excaps
   \<lbrace>cnode_inv_auth_derivations\<rbrace>,-"
  apply (simp add: decode_cnode_invocation_def split_def whenE_def unlessE_def split del: if_split)
  apply (wpsimp wp: derive_cap_auth_derived get_cap_auth_derived hoare_vcg_all_lift
              simp: cnode_inv_auth_derivations_If_Insert_Move[unfolded cnode_inv_auth_derivations_def]
                    cnode_inv_auth_derivations_def split_def whenE_def split_del: if_split
         | strengthen cte_wp_at_auth_derived_mask_cap_strg cte_wp_at_auth_derived_update_cap_data_strg
         | wp (once) hoare_drop_imps)+
  done

lemma derive_cap_clas:
  "\<lbrace>\<lambda>s :: det_ext state. cap_links_asid_slot aag p b \<rbrace>
   derive_cap a b
   \<lbrace>\<lambda>rv s. cap_links_asid_slot aag p rv\<rbrace>, -"
  apply (simp add: derive_cap_def  cong: cap.case_cong)
  apply (rule hoare_pre)
  apply (wp arch_derive_cap_clas | wpc)+
  apply (auto simp: is_cap_simps cap_links_asid_slot_def)
  done

lemma derive_cap_obj_refs_auth:
  "\<lbrace>\<lambda>s :: det_ext state. (\<forall>r\<in>obj_refs_ac cap. \<forall>auth\<in>cap_auth_conferred cap. aag_has_auth_to aag auth r)\<rbrace>
   derive_cap slot cap
   \<lbrace>\<lambda>x s. (\<forall>r\<in>obj_refs_ac x. \<forall>auth\<in>cap_auth_conferred x. aag_has_auth_to aag auth r) \<rbrace>, -"
  by (wpsimp wp: arch_derive_cap_obj_refs_auth simp: derive_cap_def)

lemma derive_cap_cli:
  "\<lbrace>K (cap_links_irq aag l cap)\<rbrace>
   derive_cap slot cap
   \<lbrace>\<lambda>x s :: det_ext state. cap_links_irq aag l x\<rbrace>, -"
  unfolding derive_cap_def
  apply (rule hoare_pre)
  apply (wp arch_derive_cap_cli | wpc | simp add: comp_def cli_no_irqs)+
  apply fastforce
  done

(* FIXME: move *)
lemma derive_cap_obj_refs_subset:
  "\<lbrace>\<lambda>s :: det_ext state. \<forall>x \<in> obj_refs_ac cap. P x s\<rbrace>
   derive_cap slot cap
   \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs_ac rv. P x s\<rbrace>, -"
  unfolding derive_cap_def
  apply (rule hoare_pre)
  apply (simp cong: cap.case_cong)
  apply (wp arch_derive_cap_obj_refs_subset | wpc)+
  apply fastforce
  done

(* FIXME: move *)
lemma derive_cap_untyped_range_subset:
  "\<lbrace>\<lambda>s :: det_ext state. \<forall>x \<in> untyped_range cap. P x s\<rbrace>
   derive_cap slot cap
   \<lbrace>\<lambda>rv s. \<forall>x \<in> untyped_range rv. P x s\<rbrace>, -"
  unfolding derive_cap_def
  apply (rule hoare_pre)
   apply (simp cong: cap.case_cong)
   apply (wp arch_derive_cap_untyped_range_subset | wpc)+
  apply fastforce
  done

lemmas derive_cap_aag_caps =
  derive_cap_obj_refs_auth
  derive_cap_untyped_range_subset
  derive_cap_clas
  derive_cap_cli

lemma derive_cap_cap_cur_auth [wp]:
  "\<lbrace>\<lambda>s :: det_ext state. pas_cap_cur_auth aag cap\<rbrace>
   derive_cap slot cap
   \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag rv\<rbrace>, -"
  unfolding aag_cap_auth_def
  apply (rule hoare_pre)
  apply (wp derive_cap_aag_caps)
  apply simp
  done

(* FIXME: move *)
lemma update_cap_obj_refs_subset:
  "x \<in> obj_refs_ac (update_cap_data P dt cap) \<Longrightarrow> x \<in> obj_refs_ac cap"
  by (cases cap; simp add: update_cap_data_closedform arch_update_cap_obj_refs_subset split: if_splits)

(* FIXME: move *)
lemma update_cap_untyped_range_subset:
  "x \<in> untyped_range (update_cap_data P dt cap) \<Longrightarrow> x \<in> untyped_range cap"
  by (cases cap; simp add: update_cap_data_closedform split: if_split_asm)

lemma P_0_1_spec:
  "\<lbrakk> (\<forall>x < length xs. P x); 2 \<le> length xs \<rbrakk> \<Longrightarrow> P 0 \<and> P 1"
  by fastforce

lemma clas_update_cap_data [simp]:
  "cap_links_asid_slot aag p (update_cap_data pres w cap) = cap_links_asid_slot aag p cap"
  unfolding cap_links_asid_slot_def update_cap_data_closedform
  by (cases cap) (auto simp: arch_update_cap_links_asid_slot[simplified cap_links_asid_slot_def])

lemma update_cap_cap_auth_conferred_subset:
  "x \<in> cap_auth_conferred (update_cap_data b w cap) \<Longrightarrow> x \<in> cap_auth_conferred cap"
  unfolding update_cap_data_def
  by (auto simp: is_cap_simps cap_auth_conferred_def cap_rights_to_auth_def badge_update_def
                 the_cnode_cap_def Let_def arch_update_cap_cap_auth_conferred_subset
          split: if_split_asm)

lemma update_cap_cli:
  "cap_links_irq aag l (update_cap_data b w cap) = cap_links_irq aag l cap"
  unfolding update_cap_data_def
  by (cases cap, simp_all add: is_cap_simps cli_no_irqs badge_update_def the_cnode_cap_def Let_def)

lemma untyped_range_update_cap_data [simp]:
  "untyped_range (update_cap_data b w c) = untyped_range c"
  unfolding update_cap_data_def
  by (cases c, simp_all add: is_cap_simps badge_update_def Let_def the_cnode_cap_def)

end

end
