(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Tcb_AC
imports Finalise_AC
begin

context begin interpretation Arch . (*FIXME: arch_split*)

(* FIXME-NTFN: The 'NotificationControl' case of the following definition needs to be changed. *)

definition
  authorised_tcb_inv :: "'a PAS \<Rightarrow> Invocations_A.tcb_invocation \<Rightarrow>  bool"
where
 "authorised_tcb_inv aag ti \<equiv> case ti of
     tcb_invocation.Suspend t \<Rightarrow> is_subject aag t
   | tcb_invocation.Resume t \<Rightarrow> is_subject aag t
   | tcb_invocation.ThreadControl t sl ep mcp priority croot vroot buf
          \<Rightarrow> is_subject aag t \<and>
            (\<forall>(cap, slot) \<in> (set_option croot \<union> set_option vroot \<union>
                            (case_option {} (set_option \<circ> snd) buf)).
                      pas_cap_cur_auth aag cap \<and> is_subject aag (fst slot))
   | tcb_invocation.NotificationControl t ntfn \<Rightarrow> is_subject aag t \<and>
         case_option True (\<lambda>a. \<forall>auth \<in> {Receive, Reset}.
                                 (pasSubject aag, auth, pasObjectAbs aag a) \<in> pasPolicy aag) ntfn
   | tcb_invocation.ReadRegisters src susp n arch \<Rightarrow> is_subject aag src
   | tcb_invocation.WriteRegisters dest res values arch \<Rightarrow> is_subject aag dest
   | tcb_invocation.CopyRegisters dest src susp res frame int_regs arch \<Rightarrow>
         is_subject aag src \<and> is_subject aag dest
   | tcb_invocation.SetTLSBase tcb tls_base \<Rightarrow> is_subject aag tcb"

subsection\<open>invoke\<close>

lemma setup_reply_master_respects:
  "\<lbrace>integrity aag X st and K (is_subject aag t)\<rbrace>
     setup_reply_master t
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: setup_reply_master_def)
  apply (wp get_cap_wp set_cap_integrity_autarch[unfolded K_def pred_conj_def]
            set_original_integrity_autarch)+
  apply simp
  done

crunch eintegrity[wp]: possible_switch_to "integrity aag X st"
  (ignore: tcb_sched_action)

lemma restart_integrity_autarch:
  "\<lbrace>integrity aag X st and K (is_subject aag t) and einvs
           and tcb_at t
           and pas_refined aag\<rbrace>
     restart t
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (simp add: restart_def)
  apply (wp set_thread_state_integrity_autarch setup_reply_master_respects
            hoare_drop_imps
        | simp add: if_apply_def2)+
  done

crunch integrity_autarch: option_update_thread "integrity aag X st"

crunch arch_state [wp]: cap_swap_for_delete "\<lambda>s. P (arch_state s)"

lemma schematic_lift_tuple3_l:
  "P (fst (a, b, c)) (fst (snd (a, b, c))) (snd (snd (a, b, c))) \<and> Q \<Longrightarrow> P a b c" by simp

lemma schematic_lift_tuple3_r:
  "Q \<and> P (fst (a, b, c)) (fst (snd (a, b, c))) (snd (snd (a, b, c))) \<Longrightarrow> P a b c" by simp

(* FIXME: MOVE *)
lemma invoke_tcb_cases:
  "invoke_tcb ti = (case ti of
     tcb_invocation.Suspend t \<Rightarrow> invoke_tcb (tcb_invocation.Suspend t)
   | tcb_invocation.Resume t \<Rightarrow> invoke_tcb (tcb_invocation.Resume t)
   | tcb_invocation.ThreadControl t sl ep mcp priority croot vroot buf \<Rightarrow>
         invoke_tcb (tcb_invocation.ThreadControl t sl ep mcp priority croot vroot buf)
   | tcb_invocation.NotificationControl t ntfn \<Rightarrow>
         invoke_tcb (tcb_invocation.NotificationControl t ntfn)
   | tcb_invocation.ReadRegisters src susp n arch \<Rightarrow>
         invoke_tcb (tcb_invocation.ReadRegisters src susp n arch)
   | tcb_invocation.WriteRegisters dest res values arch \<Rightarrow>
         invoke_tcb (tcb_invocation.WriteRegisters dest res values arch)
   | tcb_invocation.CopyRegisters dest src susp res frame int_regs arch \<Rightarrow>
         invoke_tcb (tcb_invocation.CopyRegisters dest src susp res frame int_regs arch)
   | tcb_invocation.SetTLSBase tcb tls_base \<Rightarrow> invoke_tcb (tcb_invocation.SetTLSBase tcb tls_base))"
  by (cases ti, simp_all)

lemmas itr_wps = restart_integrity_autarch as_user_integrity_autarch thread_set_integrity_autarch
              option_update_thread_integrity_autarch thread_set_pas_refined
              cap_insert_integrity_autarch cap_insert_pas_refined
              hoare_vcg_all_liftE wp_throw_const_impE hoare_weak_lift_imp hoare_vcg_all_lift
              check_cap_inv[where P="valid_cap c" for c]
              check_cap_inv[where P="tcb_cap_valid c p" for c p]
              check_cap_inv[where P="cte_at p0" for p0]
              check_cap_inv[where P="tcb_at p0" for p0]
              check_cap_inv[where P="ex_cte_cap_wp_to P p" for P p]
              check_cap_inv[where P="ex_nonz_cap_to p" for p]
              check_cap_inv2[where Q="\<lambda>_. integrity aag X st" for aag X st]
              check_cap_inv2[where Q="\<lambda>_. pas_refined aag" for aag]
              checked_insert_no_cap_to cap_insert_ex_cap
              cap_delete_valid_cap cap_delete_deletes
              hoare_case_option_wp thread_set_valid_cap
              thread_set_tcb_ipc_buffer_cap_cleared_invs
              thread_set_invs_trivial[OF ball_tcb_cap_casesI]
              thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
              thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]

(*FIXME MOVE *)

lemma aag_cap_auth_master_Reply:
  "\<lbrakk>pas_refined aag s ; AllowGrant \<in> R\<rbrakk>
     \<Longrightarrow>  pas_cap_cur_auth aag (cap.ReplyCap tcb True R) = is_subject aag tcb"
  unfolding aag_cap_auth_def
  by (fastforce intro: aag_wellformed_refl aag_wellformed_control_is_owns[THEN iffD1]
                 simp: pas_refined_def cli_no_irqs clas_no_asid cap_auth_conferred_def
                       reply_cap_rights_to_auth_def)



(* FIXME MOVE *)
lemma cdt_NullCap:
  "valid_mdb s \<Longrightarrow> caps_of_state s src = Some NullCap \<Longrightarrow> cdt s src = None"
  by (rule ccontr) (force dest: mdb_cte_atD simp: valid_mdb_def2)


lemma setup_reply_master_pas_refined:
  "\<lbrace>pas_refined aag and valid_mdb and K (is_subject aag t)\<rbrace>
     setup_reply_master t
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: setup_reply_master_def)
  apply (wp get_cap_wp set_cap_pas_refined set_original_wp)+
  by (force dest: cdt_NullCap simp: aag_cap_auth_master_Reply cte_wp_at_caps_of_state)

crunches possible_switch_to
  for tcb_domain_map_wellformed[wp]: " tcb_domain_map_wellformed aag"

lemma restart_pas_refined:
  "\<lbrace>pas_refined aag and invs and tcb_at t and K (is_subject aag t)\<rbrace> restart t \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (simp add: restart_def get_thread_state_def)
  apply (wp set_thread_state_pas_refined setup_reply_master_pas_refined thread_get_wp'
         | strengthen invs_mdb
         | simp)+
  done

lemma option_update_thread_set_safe_lift:
  "\<lbrakk> \<And>v. \<lbrace>P\<rbrace> thread_set (f v) t \<lbrace>\<lambda>rv. P\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>P\<rbrace> option_update_thread t f v \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: option_update_thread_def split: option.split)

lemmas option_update_thread_pas_refined
    = option_update_thread_set_safe_lift [OF thread_set_pas_refined]

crunch integrity_autarch[wp]: thread_set_priority "integrity aag X st"
  (ignore: tcb_sched_action)

lemma set_priority_integrity_autarch[wp]:
 "\<lbrace>integrity aag X st and pas_refined aag and K (is_subject aag tptr)\<rbrace>
    set_priority tptr prio \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by (simp add: set_priority_def | wp)+

lemma set_priority_pas_refined[wp]:
  "\<lbrace>pas_refined aag\<rbrace>
    set_priority tptr prio \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (simp add: set_priority_def thread_set_priority_def ethread_set_def set_eobject_def get_etcb_def
         | wp hoare_vcg_imp_lift')+
   apply (simp add: tcb_sched_action_def | wp)+
  apply (clarsimp simp: etcb_at_def pas_refined_def tcb_domain_map_wellformed_aux_def
                 split: option.splits)
  apply (erule_tac x="(a, b)" in ballE)
   apply simp
  apply (erule domains_of_state_aux.cases)
  apply (force intro: domtcbs split: if_split_asm)
  done

lemma gts_test[wp]: "\<lbrace>\<top>\<rbrace> get_thread_state t \<lbrace>\<lambda>rv s. test rv = st_tcb_at test t s\<rbrace>"
  apply (simp add: get_thread_state_def thread_get_def)
  apply wp
  apply (clarsimp simp add: st_tcb_def2)
  done

crunch exst[wp]: option_update_thread "\<lambda>s. P (exst s)"

lemma out_valid_sched: "(\<And>x a. tcb_state (f a x) = tcb_state x) \<Longrightarrow>
  \<lbrace>valid_sched\<rbrace> option_update_thread tptr f v \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: option_update_thread_def)
  apply (rule hoare_pre)
  apply (wp thread_set_not_state_valid_sched | wpc | simp)+
  done


definition "safe_id x \<equiv> x"

lemma use_safe_id: "safe_id x \<Longrightarrow> x"
  by (simp add: safe_id_def)

lemma simplify_post:
  "\<lbrakk>\<And>r s. x r s \<Longrightarrow> safe_id (Q' r s) \<Longrightarrow> Q r s; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. x r s \<and> Q' r s\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (rule hoare_post_impErr)
  apply assumption
  apply (clarsimp simp add: safe_id_def)+
  done

end

lemma (in is_extended') valid_cap_syn[wp]: "I (\<lambda>s. valid_cap_syn s a)" by (rule lift_inv,simp)

lemma (in is_extended') no_cap_to_obj_dr_emp[wp]: "I (no_cap_to_obj_dr_emp a)" by (rule lift_inv,simp)

lemma (in is_extended') cte_wp_at[wp]: "I (cte_wp_at P a)" by (rule lift_inv,simp)

crunch pas_refined[wp]: set_mcpriority "pas_refined aag"

crunch integrity_autarch: set_mcpriority "integrity aag X st"

context begin interpretation Arch . (*FIXME: arch_split*)

lemma checked_insert_pas_refined:
  "\<lbrace>pas_refined aag and valid_mdb and
       K(\<not> is_master_reply_cap new_cap \<and> is_subject aag target \<and>
       is_subject aag (fst src_slot) \<and> pas_cap_cur_auth aag new_cap)\<rbrace>
     check_cap_at new_cap src_slot (
     check_cap_at (ThreadCap target) slot(
     cap_insert new_cap src_slot (target, ref)))
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (unfold check_cap_at_def)
  apply (wp cap_insert_pas_refined_same_object_as get_cap_wp)
  by (fastforce simp:cte_wp_at_caps_of_state)

(* FIXME MOVE *)
lemma update_cdt_wp:
  "\<lbrace>\<lambda>s. P (s\<lparr>cdt := m (cdt s)\<rparr>)\<rbrace> update_cdt m \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: update_cdt_def set_cdt_def) wp

(* FIXME MOVE *)
lemma parent_ofD: "m \<Turnstile> src \<leadsto> x \<Longrightarrow> m x = Some src"
  by (simp add: cdt_parent_of_def)


crunch tcb_states_of_state[wp]: set_untyped_cap_as_full "\<lambda>s. P (tcb_states_of_state s)"


(* FIXME MOVE *)
lemma map_le_to_rtrancl:
  "m \<subseteq>\<^sub>m m' \<Longrightarrow> m \<Turnstile> pptr \<rightarrow>* ptr \<Longrightarrow> m' \<Turnstile> pptr \<rightarrow>* ptr"
  apply (erule subsetD[rotated])
  apply (rule rtrancl_mono)
  apply (fastforce simp:cdt_parent_of_def map_le_def dom_def)
  done

lemma map_le_to_cca:
  "m \<subseteq>\<^sub>m m' \<Longrightarrow> cdt_change_allowed aag subjects m tcbsts ptr
   \<Longrightarrow> cdt_change_allowed aag subjects m' tcbsts ptr"
  apply (elim cdt_change_allowedE cdt_change_allowedI[rotated])
  by (rule map_le_to_rtrancl)

lemma cap_insert_cdt_change_allowed[wp]:
  "\<lbrace> valid_mdb and cdt_change_allowed' aag slot\<rbrace>
     cap_insert new_cap src_slot dest_slot
  \<lbrace>\<lambda>_. cdt_change_allowed' aag slot \<rbrace>"
  apply (rule hoare_pre, unfold cap_insert_def)
   apply (wp add: dxo_wp_weak update_cdt_wp | simp)+
        apply (rule hoare_post_imp[of
        "\<lambda>_. cdt_change_allowed' aag slot and (\<lambda>s. cdt s dest_slot = None)"])
         apply (fastforce elim: map_le_to_cca[rotated] simp:map_le_def dom_def)
        apply (wps|wp get_cap_wp)+
  apply (clarsimp)
  apply (drule valid_mdb_mdb_cte_at)
  apply (subst not_Some_eq[symmetric])
  apply (intro allI notI)
  apply (drule(1) mdb_cte_atD[rotated])
  apply (simp add:cte_wp_at_caps_of_state)
  done


lemma invoke_tcb_tc_respects_aag:
  "\<lbrace> integrity aag X st and pas_refined aag
         and einvs and simple_sched_action
         and tcb_inv_wf (ThreadControl t sl ep mcp priority croot vroot buf)
         and K (authorised_tcb_inv aag (ThreadControl t sl ep mcp priority croot vroot buf))\<rbrace>
     invoke_tcb (ThreadControl t sl ep mcp priority croot vroot buf)
   \<lbrace>\<lambda>rv. integrity aag X st and pas_refined aag\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (subst invoke_tcb.simps)
  apply (subst set_priority_extended.dxo_eq)
  apply (rule hoare_vcg_precond_imp)
   apply (rule_tac P="case ep of Some v \<Rightarrow> length v = word_bits | _ \<Rightarrow> True"
                 in hoare_gen_asm)
   apply (simp only: split_def)
  apply ((simp add: conj_comms del: hoare_True_E_R,
                  strengthen imp_consequent[where Q="x = None" for x], simp cong: conj_cong)
        | rule wp_split_const_if wp_split_const_if_R
                   hoare_vcg_all_lift_R
                   hoare_vcg_E_elim hoare_vcg_const_imp_lift_R
                   hoare_vcg_R_conj
        | wp
             restart_integrity_autarch set_mcpriority_integrity_autarch
             as_user_integrity_autarch thread_set_integrity_autarch
             option_update_thread_integrity_autarch
             out_valid_sched static_imp_wp
             cap_insert_integrity_autarch checked_insert_pas_refined
             cap_delete_respects' cap_delete_pas_refined'
             check_cap_inv2[where Q="\<lambda>_. integrity aag X st"]
             as_user_pas_refined restart_pas_refined
             thread_set_pas_refined
             option_update_thread_pas_refined
             out_invs_trivial case_option_wpE cap_delete_deletes
             cap_delete_valid_cap cap_insert_valid_cap out_cte_at
             cap_insert_cte_at cap_delete_cte_at out_valid_cap out_tcb_valid
             hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
             thread_set_tcb_ipc_buffer_cap_cleared_invs
             thread_set_invs_trivial[OF ball_tcb_cap_casesI]
             hoare_vcg_all_lift thread_set_valid_cap out_emptyable
             check_cap_inv[where P="valid_cap c" for c]
             check_cap_inv[where P="tcb_cap_valid c p" for c p]
             check_cap_inv[where P="cte_at p0" for p0]
             check_cap_inv[where P="tcb_at p0" for p0]
             check_cap_inv[where P="simple_sched_action"]
             check_cap_inv[where P="valid_list"]
             check_cap_inv[where P="valid_sched"]
             thread_set_cte_at
             thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
             thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             checked_insert_no_cap_to
             out_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             thread_set_ipc_tcb_cap_valid
             cap_delete_pas_refined'[THEN valid_validE_E] thread_set_cte_wp_at_trivial
        | simp add: ran_tcb_cap_cases dom_tcb_cap_cases[simplified]
                    emptyable_def a_type_def partial_inv_def
               del: hoare_True_E_R
        | wpc
        | strengthen invs_mdb use_no_cap_to_obj_asid_strg
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index 0"]
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index (Suc 0)"]
        )+
  apply (clarsimp simp: authorised_tcb_inv_def)
  apply (clarsimp simp: tcb_at_cte_at_0 tcb_at_cte_at_1[simplified]
                        is_cap_simps is_valid_vtable_root_def
                        is_cnode_or_valid_arch_def tcb_cap_valid_def
                        tcb_at_st_tcb_at[symmetric] invs_valid_objs
                        cap_asid_def vs_cap_ref_def
                        clas_no_asid cli_no_irqs
                        emptyable_def
       | rule conjI | erule pas_refined_refl)+
  done

lemma invoke_tcb_unbind_notification_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and simple_sched_action
       and einvs and Tcb_AI.tcb_inv_wf (tcb_invocation.NotificationControl t None)
       and K (authorised_tcb_inv aag (tcb_invocation.NotificationControl t None))\<rbrace>
     invoke_tcb (tcb_invocation.NotificationControl t None)
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (clarsimp)
  apply (wp unbind_notification_respects)
  apply (clarsimp simp: authorised_tcb_inv_def tcb_at_def pred_tcb_def2)
  apply (clarsimp split: option.split)
  apply (frule(1) bound_tcb_at_implies_reset[unfolded pred_tcb_def2, OF _ exI, OF _ conjI])
   apply simp
  apply simp
  done

lemma sbn_bind_respects:
  "\<lbrace>integrity aag X st and bound_tcb_at ((=) None) t
    and K ((pasSubject aag, Receive, pasObjectAbs aag ntfn) \<in> pasPolicy aag \<and> is_subject aag t)\<rbrace>
       set_bound_notification t (Some ntfn)
   \<lbrace>\<lambda>rv. integrity aag X st \<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp)
  apply (erule integrity_trans)
  apply (clarsimp simp: integrity_def obj_at_def pred_tcb_at_def)
  done


lemma bind_notification_respects:
  "\<lbrace>integrity aag X st and pas_refined aag and bound_tcb_at ((=) None) t
      and K ((pasSubject aag, Receive, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag \<and>
             is_subject aag t)\<rbrace>
     bind_notification t ntfnptr
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: bind_notification_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (wp set_ntfn_respects hoare_vcg_imp_lift sbn_bind_respects | wpc | clarsimp)+
  apply fastforce
  done

lemma invoke_tcb_bind_notification_respects:
  "\<lbrace>integrity aag X st and pas_refined aag
      and einvs and Tcb_AI.tcb_inv_wf (tcb_invocation.NotificationControl t (Some ntfn))
      and simple_sched_action
      and K (authorised_tcb_inv aag (tcb_invocation.NotificationControl t (Some ntfn)))\<rbrace>
     invoke_tcb (tcb_invocation.NotificationControl t (Some ntfn))
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp)
  apply (wp bind_notification_respects)
  apply (clarsimp simp: authorised_tcb_inv_def)
  done

lemma invoke_tcb_ntfn_control_respects[wp]:
  "\<lbrace>integrity aag X st and pas_refined aag
      and einvs and Tcb_AI.tcb_inv_wf (tcb_invocation.NotificationControl t ntfn)
      and simple_sched_action
      and K (authorised_tcb_inv aag (tcb_invocation.NotificationControl t ntfn))\<rbrace>
     invoke_tcb (tcb_invocation.NotificationControl t ntfn)
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (case_tac ntfn, simp_all del: invoke_tcb.simps Tcb_AI.tcb_inv_wf.simps K_def)
   apply (wp invoke_tcb_bind_notification_respects invoke_tcb_unbind_notification_respects | simp)+
  done

lemma invoke_tcb_respects:
  "\<lbrace>integrity aag X st and pas_refined aag
         and einvs and simple_sched_action and Tcb_AI.tcb_inv_wf ti
         and K (authorised_tcb_inv aag ti)\<rbrace>
     invoke_tcb ti
   \<lbrace>\<lambda>rv. integrity aag X st\<rbrace>"
  apply (cases ti, simp_all add: hoare_conjD1 [OF invoke_tcb_tc_respects_aag [simplified simp_thms]]
                            del: invoke_tcb.simps Tcb_AI.tcb_inv_wf.simps K_def)
  apply (safe intro!: hoare_gen_asm)
  apply ((wp itr_wps mapM_x_wp' | simp add: if_apply_def2 split del: if_split
            | wpc | clarsimp simp: authorised_tcb_inv_def arch_get_sanitise_register_info_def
            | rule conjI | subst(asm) idle_no_ex_cap)+)
  done

subsubsection\<open>@{term "pas_refined"}\<close>

lemmas ita_wps = as_user_pas_refined restart_pas_refined cap_insert_pas_refined
                 thread_set_pas_refined cap_delete_pas_refined' check_cap_inv2 hoare_vcg_all_liftE
                 wp_throw_const_impE hoare_weak_lift_imp hoare_vcg_all_lift

lemma hoare_st_refl:
  "\<lbrakk>\<And>st. \<lbrace>P st\<rbrace> f \<lbrace>Q st\<rbrace>; \<And>r s st. Q st r s \<Longrightarrow> Q' r s\<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. P s s\<rbrace> f \<lbrace>Q'\<rbrace>"
  apply (clarsimp simp add: valid_def)
  apply (drule_tac x=s in meta_spec)
  apply force
  done

lemma bind_notification_pas_refined[wp]:
  "\<lbrace>pas_refined aag
      and K (\<forall>auth \<in> {Receive, Reset}.
                   (pasObjectAbs aag t, auth, pasObjectAbs aag ntfnptr) \<in> pasPolicy aag)\<rbrace>
     bind_notification t ntfnptr
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (clarsimp simp: bind_notification_def)
  apply (wp set_simple_ko_pas_refined | wpc | simp)+
  done

lemma invoke_tcb_ntfn_control_pas_refined[wp]:
  "\<lbrace>pas_refined aag and Tcb_AI.tcb_inv_wf (tcb_invocation.NotificationControl t ntfn)
     and einvs  and simple_sched_action
     and K (authorised_tcb_inv aag (tcb_invocation.NotificationControl t ntfn))\<rbrace>
     invoke_tcb (tcb_invocation.NotificationControl t ntfn)
   \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  apply (case_tac ntfn, simp_all del: K_def)
   apply (safe intro!: hoare_gen_asm)
   apply (wp | simp add: authorised_tcb_inv_def)+
  done

lemma invoke_tcb_pas_refined:
  "\<lbrace>pas_refined aag and Tcb_AI.tcb_inv_wf ti and einvs and simple_sched_action
       and K (authorised_tcb_inv aag ti)\<rbrace>
     invoke_tcb ti
   \<lbrace>\<lambda>rv. pas_refined aag\<rbrace>"
  apply (cases "\<exists>t sl ep mcp priority croot vroot buf.
              ti = tcb_invocation.ThreadControl t sl ep mcp priority croot vroot buf")
   apply safe
   apply (rule hoare_chain, rule_tac Q'="\<lambda>_. pas_refined aag" and st1="\<lambda>x. x" in
                                     hoare_st_refl[OF invoke_tcb_tc_respects_aag])
     apply force
    apply fastforce
   apply assumption
  apply (rule hoare_gen_asm)
  apply (cases ti, simp_all add: authorised_tcb_inv_def)
        apply (wp ita_wps hoare_drop_imps mapM_x_wp'
              | simp add: emptyable_def if_apply_def2 authorised_tcb_inv_def
                          arch_get_sanitise_register_info_def
              | rule ball_tcb_cap_casesI
              | wpc
              | fastforce intro: notE[rotated,OF idle_no_ex_cap,simplified]
                           simp: invs_valid_global_refs invs_valid_objs)+
  done

subsection\<open>TCB / decode\<close>

lemma decode_registers_authorised:
  "\<lbrace>K (is_subject aag t)\<rbrace> decode_read_registers msg (cap.ThreadCap t) \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  "\<lbrace>K (is_subject aag t)\<rbrace> decode_write_registers msg (cap.ThreadCap t) \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  "\<lbrace>pas_refined aag and K (is_subject aag t \<and> (\<forall>(cap, slot) \<in> set excaps. pas_cap_cur_auth aag cap \<and> is_subject aag (fst slot)))\<rbrace>
     decode_copy_registers msg (cap.ThreadCap t) (map fst excaps)
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  unfolding decode_read_registers_def decode_write_registers_def decode_copy_registers_def authorised_tcb_inv_def
  by (rule hoare_pre, simp cong: list.case_cong, (wp | wpc)+, clarsimp simp: cap_auth_conferred_def pas_refined_all_auth_is_owns aag_cap_auth_def)+


lemma stupid_strg:
  "cap_links_asid_slot aag (pasObjectAbs aag (fst y)) x \<longrightarrow>
  (x = cap \<and> (\<exists>b. y = (a, b)) \<longrightarrow> cap_links_asid_slot aag (pasObjectAbs aag a) cap)"
  by auto

lemma decode_set_ipc_buffer_authorised:
  "\<lbrace>K (is_subject aag t \<and> (\<forall>x \<in> set excaps. is_subject aag (fst (snd x)))
                      \<and> (\<forall>x \<in> set excaps. pas_cap_cur_auth aag (fst x))) \<rbrace>
    decode_set_ipc_buffer msg (cap.ThreadCap t) slot excaps
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  unfolding decode_set_ipc_buffer_def authorised_tcb_inv_def
  apply (cases "excaps ! 0")
  apply (clarsimp cong: list.case_cong split del: if_split)
  apply (rule hoare_pre)
  apply (clarsimp simp: ball_Un aag_cap_auth_def split del: if_split split: prod.split
       | strengthen stupid_strg
       | wp (once) derive_cap_obj_refs_auth derive_cap_untyped_range_subset derive_cap_clas derive_cap_cli
                 hoare_vcg_all_lift_R whenE_throwError_wp slot_long_running_inv
       | wpc)+
  apply (cases excaps, simp)
  apply fastforce
  done

lemma decode_set_space_authorised:
  "\<lbrace>K (is_subject aag t \<and> (\<forall>x \<in> set excaps. is_subject aag (fst (snd x)))
                      \<and> (\<forall>x \<in> set excaps. pas_cap_cur_auth aag (fst x))) \<rbrace>
     decode_set_space ws (cap.ThreadCap t) slot excaps
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  unfolding decode_set_space_def authorised_tcb_inv_def
  apply (rule hoare_pre)
  apply (simp cong: list.case_cong split del: if_split)
  apply (clarsimp simp: ball_Un split del: if_split
       | wp (once) derive_cap_obj_refs_auth derive_cap_untyped_range_subset derive_cap_clas derive_cap_cli
                 hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R whenE_throwError_wp slot_long_running_inv)+
  apply (clarsimp simp: not_less all_set_conv_all_nth dest!: P_0_1_spec)
  apply (auto simp: aag_cap_auth_def update_cap_cli intro: update_cap_obj_refs_subset dest!: update_cap_untyped_range_subset update_cap_cap_auth_conferred_subset)
  done

(* grot: this is from the bowels of decode_tcb_configure_authorised. *)
lemma decode_tcb_configure_authorised_helper:
  "\<lbrace>K True and K (is_subject aag t \<and> (\<forall>x \<in> set excaps. is_subject aag (fst (snd x)))
                      \<and> (\<forall>x \<in> set excaps. pas_cap_cur_auth aag (fst x))
                      \<and> authorised_tcb_inv aag set_param \<and> is_thread_control set_param)\<rbrace>
     decode_set_space ws (cap.ThreadCap t) slot excaps
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag (tcb_invocation.ThreadControl t slot (tc_new_fault_ep rv)
                                    None None (tc_new_croot rv)
                                    (tc_new_vroot rv) (tc_new_buffer set_param))\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (cases set_param)
  apply (simp_all add: is_thread_control_def decode_set_space_def authorised_tcb_inv_def
                 cong: list.case_cong option.case_cong prod.case_cong
                split: prod.split_asm split del: if_split)
  apply (cases "excaps!0")
  apply (cases "excaps!Suc 0")
  apply (rule hoare_pre)
   apply (clarsimp simp: ball_Un split del: if_split split: prod.split
        | strengthen stupid_strg
        | wp (once) derive_cap_obj_refs_auth derive_cap_untyped_range_subset derive_cap_clas derive_cap_cli
                  hoare_vcg_all_lift_R whenE_throwError_wp slot_long_running_inv)+
  apply (clarsimp cong: list.case_cong option.case_cong prod.case_cong split: prod.split_asm)
  apply (clarsimp simp: not_less all_set_conv_all_nth dest!: P_0_1_spec)
  apply (auto simp: aag_cap_auth_def update_cap_cli intro: update_cap_untyped_range_subset update_cap_obj_refs_subset dest!: update_cap_cap_auth_conferred_subset elim: bspec)
  done

lemma decode_tcb_configure_authorised:
  "\<lbrace>K (is_subject aag t \<and> (\<forall>x \<in> set excaps. is_subject aag (fst (snd x)))
                      \<and> (\<forall>x \<in> set excaps. pas_cap_cur_auth aag (fst x))) \<rbrace>
    decode_tcb_configure msg (cap.ThreadCap t) slot excaps
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  apply (wpsimp simp: decode_tcb_configure_def
                wp: whenE_throwError_wp decode_tcb_configure_authorised_helper
                    decode_set_ipc_buffer_authorised)
  apply (auto dest: in_set_takeD)
  done

lemma decode_set_priority_authorised:
  "\<lbrace>K (is_subject aag t)\<rbrace>
    decode_set_priority msg (ThreadCap t) slot excs
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  by (wpsimp simp: decode_set_priority_def check_prio_def authorised_tcb_inv_def)

lemma decode_set_mcpriority_authorised:
  "\<lbrace>K (is_subject aag t)\<rbrace>
    decode_set_mcpriority msg (ThreadCap t) slot excs
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  by (wpsimp simp: decode_set_mcpriority_def check_prio_def authorised_tcb_inv_def)

lemma decode_set_sched_params_authorised:
  "\<lbrace>K (is_subject aag t)\<rbrace>
    decode_set_sched_params msg (ThreadCap t) slot excs
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  by (wpsimp simp: decode_set_sched_params_def check_prio_def authorised_tcb_inv_def)

lemma decode_unbind_notification_authorised:
  "\<lbrace>K (is_subject aag t)\<rbrace>
    decode_unbind_notification (cap.ThreadCap t)
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  unfolding decode_unbind_notification_def authorised_tcb_inv_def
  apply clarsimp
  apply (wp gbn_wp, clarsimp)
  done

lemma decode_bind_notification_authorised:
  "\<lbrace>K (is_subject aag t \<and> (\<forall>x \<in> set excaps. is_subject aag (fst (snd x)))
                      \<and> (\<forall>x \<in> set excaps. pas_cap_cur_auth aag (fst x)) )\<rbrace>
    decode_bind_notification (cap.ThreadCap t) excaps
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  unfolding decode_bind_notification_def authorised_tcb_inv_def
  apply clarsimp
  apply (wp gbn_wp get_simple_ko_wp whenE_throwError_wp | wpc | simp add:)+
  apply (clarsimp dest!: hd_in_set)
  apply (drule_tac x="hd excaps"  in bspec, simp)+
  apply (auto simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def AllowRecv_def)
  done

lemma decode_set_tls_base_authorised:
  "\<lbrace>K (is_subject aag t)\<rbrace>
    decode_set_tls_base msg (cap.ThreadCap t)
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>, -"
  unfolding decode_set_tls_base_def authorised_tcb_inv_def
  apply clarsimp
  apply (wpsimp wp: gbn_wp)
  done

lemma decode_tcb_invocation_authorised:
  "\<lbrace>invs and pas_refined aag and K (is_subject aag t \<and> (\<forall>x \<in> set excaps. is_subject aag (fst (snd x)))
                                  \<and> (\<forall>x \<in> set excaps. pas_cap_cur_auth aag (fst x)))\<rbrace>
     decode_tcb_invocation label msg (cap.ThreadCap t) slot excaps
   \<lbrace>\<lambda>rv s. authorised_tcb_inv aag rv\<rbrace>,-"
  unfolding decode_tcb_invocation_def
  apply (rule hoare_pre)
   apply wpc
  apply (wp decode_registers_authorised decode_tcb_configure_authorised
            decode_set_priority_authorised decode_set_mcpriority_authorised
            decode_set_sched_params_authorised
            decode_set_ipc_buffer_authorised decode_set_space_authorised
            decode_bind_notification_authorised
            decode_unbind_notification_authorised
            decode_set_tls_base_authorised)+
  by (auto iff: authorised_tcb_inv_def)

text\<open>

@{term "decode_tcb_invocation"} preserves all invariants, so no need
to show @{term "integrity"} or @{term "pas_refined"}.

\<close>

end

end
