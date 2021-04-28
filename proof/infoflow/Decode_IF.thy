(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Decode_IF
imports Ipc_IF
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma data_to_obj_type_rev:
  "reads_equiv_valid_inv A aag \<top> (data_to_obj_type type)"
  unfolding data_to_obj_type_def fun_app_def arch_data_to_obj_type_def
  apply (wp | wpc)+
  apply simp
  done


lemma ensure_empty_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag (fst slot))) (ensure_empty slot)"
  unfolding ensure_empty_def fun_app_def
  apply (wp get_cap_rev | simp)+
  done


lemma prop_of_obj_ref_of_cnode_cap:
  "\<lbrakk>is_cnode_cap cap; \<forall>r\<in>obj_refs cap. P r\<rbrakk> \<Longrightarrow> P (obj_ref_of cap)"
  by(case_tac cap, simp_all)


lemma decode_untyped_invocation_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and
                                (K (cap = UntypedCap dev bs sz idx \<and>
                                    is_subject aag (fst slot) \<and>
                                    (\<forall>c\<in>set excaps. pas_cap_cur_auth aag c))))
        (decode_untyped_invocation label args slot cap excaps)"
  unfolding decode_untyped_invocation_def fun_app_def
  apply(rule gen_asm_ev)
  apply(simp add: unlessE_def[symmetric] unlessE_whenE
       split del: if_split)
  apply (wp (once) whenE_throwError_wp
       | wp mapME_x_ev' ensure_empty_rev get_cap_rev
             lookup_slot_for_cnode_op_rev
             ensure_no_children_rev
             const_on_failure_ev mapME_x_inv_wp
       | assumption
       | simp
       | rule validE_R_validE | strengthen aag_can_read_self)+
                  apply(rule hoare_strengthen_post[
                                  where Q="\<lambda> rv s. (is_cnode_cap rv
                                                         \<longrightarrow> is_subject aag (obj_ref_of rv))
                                                 \<and> pas_refined aag s"])
                   apply(wp (once) whenE_throwError_wp
                        |wp get_cap_ret_is_subject
                            data_to_obj_type_rev data_to_obj_type_inv
                        | simp
                        | wp (once) hoare_drop_imps)+
  apply(clarify, drule_tac x="excaps ! 0" in bspec, fastforce intro: bang_0_in_set)
  apply(auto dest: is_cnode_into_is_subject elim: prop_of_obj_ref_of_cnode_cap)
  done

lemma derive_cap_rev':
  "reads_equiv_valid_inv A aag (\<lambda> s. (\<exists>x xa xb dev. cap = cap.UntypedCap dev x xa xb) \<longrightarrow>
         pas_refined aag s \<and> is_subject aag (fst slot)) (derive_cap slot cap)"
  unfolding derive_cap_def arch_derive_cap_def
  apply(rule equiv_valid_guard_imp)
  apply(wp ensure_no_children_rev | wpc | simp)+
  done

lemma derive_cap_rev:
  "reads_equiv_valid_inv A aag (\<lambda> s. pas_refined aag s \<and> is_subject aag (fst slot)) (derive_cap slot cap)"
  by(blast intro: equiv_valid_guard_imp[OF derive_cap_rev'])

(* FIXME: move *)
lemma if_apply_ev:
  "equiv_valid I A B P (if a then b x  else c x) \<Longrightarrow>
   equiv_valid I A B P ((if a then b else c) x)"
  by(simp split: if_split_asm)

lemma whenE_throwError_bindE_ev:
  assumes ev: "\<not> b \<Longrightarrow> equiv_valid I A A P f"
  shows "equiv_valid I A A P (whenE b (throwError x) >>=E (\<lambda>_. f))"
  apply(rule_tac Q="\<lambda> rv s. \<not> b \<and> P s" in bindE_ev_pre)
     using ev apply(fastforce simp: equiv_valid_def2 equiv_valid_2_def)
    apply(wp whenE_throwError_sp)+
  by simp

lemma expand_len_gr_Suc_0:
  "Suc 0 < length xs = (xs \<noteq> [] \<and> Suc (Suc 0) \<le> length xs)"
  apply fastforce
  done

(* FIXME: remove *)
lemmas hoare_vcg_imp_lift_R = hoare_vcg_const_imp_lift_R

lemma decode_cnode_invocation_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and
                                K (\<forall>c\<in>{cap} \<union> set excaps. pas_cap_cur_auth aag c))
     (decode_cnode_invocation label args cap excaps)"
  unfolding decode_cnode_invocation_def fun_app_def
  apply (rule equiv_valid_guard_imp)
  apply (simp add: unlessE_whenE)
  apply wp
  apply ((wp if_apply_ev derive_cap_rev whenE_inv hoare_vcg_imp_lift_R
            lookup_slot_for_cnode_op_rev hoare_vcg_all_lift_R
            lookup_slot_for_cnode_op_authorised ensure_empty_rev get_cap_rev
        | simp add: split_def unlessE_whenE split del: if_split
               del: hoare_True_E_R
        | wpc
        | (wp (once) hoare_drop_imps, wp (once) lookup_slot_for_cnode_op_authorised)
        | strengthen aag_can_read_self)+)
  apply clarsimp
  apply (cases excaps; cases "tl excaps"; clarsimp)
    apply (auto dest: bspec[where x="excaps ! 0"] bspec[where x="excaps ! Suc 0"]
                      is_cnode_into_is_subject
               intro: nth_mem elim: prop_of_obj_ref_of_cnode_cap
               simp: expand_len_gr_Suc_0)
  done

lemma range_check_ev:
  "equiv_valid_inv I A \<top> (range_check v v_min v_max)"
  unfolding range_check_def fun_app_def unlessE_whenE
  apply (rule equiv_valid_guard_imp)
   apply wp
  apply simp
  done


(* FIXME: move *)
lemma cte_wp_at_caps_of_state:
  "cte_wp_at ((=) c) slot s \<Longrightarrow> caps_of_state s slot = Some c"
  by(simp add: caps_of_state_def cte_wp_at_def)

(* FIXME: move *)
lemma aag_has_auth_to_obj_refs_of_owned_cap:
  "\<lbrakk>pas_refined aag s;
    is_subject aag (fst slot);
    cte_wp_at ((=) cap) slot s;
    a \<in> cap_auth_conferred cap; x \<in> Access.obj_refs cap\<rbrakk> \<Longrightarrow>
   aag_has_auth_to aag a x"
  apply(drule sym, erule ssubst)
  apply(rule_tac s=s in pas_refined_mem)
   apply(fastforce intro: sta_caps[OF cte_wp_at_caps_of_state])
  apply assumption
  done

(* FIXME: move *)
lemma slot_cap_long_running_delete_reads_respects_f:
  "reads_respects_f aag l (silc_inv aag st and pas_refined aag and valid_objs and zombies_final
         and K (is_subject aag (fst slot)))
     (slot_cap_long_running_delete slot)"
  unfolding slot_cap_long_running_delete_def
  apply(rule bind_ev_pre)
  apply(wpc)
               apply(wp)[1]
              apply(fastforce simp: long_running_delete_def is_final_cap_def gets_bind_ign
                             intro: return_ev)+
          apply((wp is_final_cap_reads_respects[where slot=slot and st=st])+)[2]
        apply(fastforce simp: long_running_delete_def is_final_cap_def gets_bind_ign intro: return_ev)+
      apply(wp is_final_cap_reads_respects[where st=st])[1]
     apply(fastforce simp: long_running_delete_def is_final_cap_def gets_bind_ign intro: return_ev)+
    apply(wp reads_respects_f[OF get_cap_rev, where Q="\<top>" and st=st], blast)
   apply(wp get_cap_wp | simp)+
  apply(fastforce intro!: cte_wp_valid_cap aag_has_auth_to_obj_refs_of_owned_cap simp: is_zombie_def
                    dest: silc_inv_not_subject)
  done

lemma check_valid_ipc_buffer_rev:
  "reads_equiv_valid_inv A aag \<top> (check_valid_ipc_buffer vptr cap)"
  unfolding check_valid_ipc_buffer_def fun_app_def
  apply(rule equiv_valid_guard_imp)
  apply(wpc | wp)+
  apply simp
  done


lemma no_state_changes:
  "(\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>) \<Longrightarrow> f = (do s \<leftarrow> get; (rv,s') \<leftarrow> select_f (f s); return rv od)"
  apply (simp add: get_def select_f_def return_def bind_def)
  apply (rule ext)
  apply (subgoal_tac "\<forall>r s'. (r,s') \<in> fst (f s) \<longrightarrow> s' = s")
   defer
   apply clarsimp
   apply (rule use_valid,assumption+)
   apply simp
  apply (case_tac "f s")
  apply clarsimp
  apply force
  done



lemma OR_choice_def2:
  "(\<And>P. \<lbrace>P\<rbrace> (c :: bool det_ext_monad) \<lbrace>\<lambda>_.P\<rbrace>) \<Longrightarrow> empty_fail c \<Longrightarrow>
     (OR_choice c f g) = (do b \<leftarrow> c; if b then f else g od)"
  apply (simp add: OR_choice_def wrap_ext_bool_det_ext_ext_def ef_mk_ef)
  by (subst no_state_changes[where f=c], simp, fastforce simp: bind_assoc split_def)

lemma check_prio_rev:
  "reads_respects aag l (\<lambda>s. is_subject aag auth) (check_prio prio auth)"
  by (wpsimp simp: check_prio_def wp: thread_get_reads_respects hoare_drop_imps)


lemma decode_set_priority_rev:
  "reads_respects aag l (K(\<forall>x \<in> set excs. pas_cap_cur_auth aag (fst x)) and (pas_refined aag))
      (decode_set_priority args (ThreadCap t) slot excs)"
  apply (wpsimp simp: decode_set_priority_def aag_cap_auth_Thread[symmetric]
                wp: check_prio_rev whenE_throwError_wp)
  apply (case_tac excs; simp)
  done


lemma decode_set_mcpriority_rev:
  "reads_respects aag l (K(\<forall>x \<in> set excs. pas_cap_cur_auth aag (fst x)) and (pas_refined aag))
    (decode_set_mcpriority args cap slot excs)"
  apply (wpsimp simp: decode_set_mcpriority_def aag_cap_auth_Thread[symmetric]
                wp: check_prio_rev whenE_throwError_wp)
  apply (case_tac excs; simp)
  done


lemma decode_set_sched_params_rev:
  "reads_respects aag l (K(\<forall>x \<in> set excs. pas_cap_cur_auth aag (fst x)) and (pas_refined aag))
    (decode_set_sched_params args cap slot excs)"
  apply (wpsimp simp: decode_set_sched_params_def aag_cap_auth_Thread[symmetric]
                wp: check_prio_rev whenE_throwError_wp)
  apply (case_tac excs; clarsimp)
  done

lemma decode_tcb_invocation_reads_respects_f:
  notes respects_f = reads_respects_f[where st=st and Q=\<top>]
  shows
  "reads_respects_f aag l (silc_inv aag st and pas_refined aag and is_subject aag \<circ> cur_thread and
                           valid_objs and zombies_final and (K (is_subject aag t \<and>
                           (\<forall>x \<in> set excaps. is_subject aag (fst (snd x))) \<and>
                           (\<forall>x \<in> set excaps. pas_cap_cur_auth aag (fst x)))))
                           (decode_tcb_invocation label args (ThreadCap t) slot excaps)"
  unfolding decode_tcb_invocation_def decode_read_registers_def
  decode_write_registers_def decode_copy_registers_def
  decode_tcb_configure_def decode_set_space_def decode_bind_notification_def
  decode_set_ipc_buffer_def fun_app_def decode_unbind_notification_def
  decode_set_tls_base_def
  apply (simp add: unlessE_def[symmetric] unlessE_whenE
        split del: if_split
             cong: gen_invocation_labels.case_cong)
  apply (rule equiv_valid_guard_imp)
   apply (wp (once) requiv_cur_thread_eq range_check_ev
             respects_f[OF derive_cap_rev]
             derive_cap_inv slot_cap_long_running_delete_reads_respects_f[where st=st]
             respects_f[OF check_valid_ipc_buffer_rev]
             check_valid_ipc_buffer_inv
             respects_f[OF decode_set_priority_rev]
             respects_f[OF decode_set_mcpriority_rev]
             respects_f[OF decode_set_sched_params_rev]
             respects_f[OF get_simple_ko_reads_respects]
             respects_f[OF get_bound_notification_reads_respects']
        | wp (once) whenE_throwError_wp
        | wp (once) hoare_drop_imps
        | wpc
        | simp add: if_apply_def2 split del: if_split add: o_def split_def)+
  unfolding get_tcb_ctable_ptr_def get_tcb_vtable_ptr_def
  apply (subgoal_tac "\<not>length excaps < 3 \<longrightarrow> is_subject aag (fst (snd (excaps ! 2)))")
   prefer 2
   apply (fastforce intro: nth_mem)
  apply (subgoal_tac "excaps \<noteq> [] \<longrightarrow> is_subject aag (fst (snd (excaps ! 0)))")
   prefer 2
   apply (fastforce intro: nth_mem)
  apply (intro allI impI conjI; (rule disjI1 | fastforce simp: reads_equiv_f_def))
  apply (rule reads_ep[where auth="Receive",simplified])
  apply (cases excaps;simp)
  by (fastforce simp: aag_cap_auth_def cap_auth_conferred_def cap_rights_to_auth_def)


lemma get_irq_state_rev:
  "reads_equiv_valid_inv A aag (K (is_subject_irq aag irq)) (get_irq_state irq)"
  unfolding get_irq_state_def
  apply(rule equiv_valid_guard_imp[OF gets_ev])
  apply(fastforce simp: reads_equiv_def2 elim: states_equiv_forE_interrupt_states
                 intro: aag_can_read_irq_self)
  done

lemma is_irq_active_rev:
  "reads_equiv_valid_inv A aag (K (is_subject_irq aag irq)) (is_irq_active irq)"
  unfolding is_irq_active_def fun_app_def
  apply (wp get_irq_state_rev)
  done

lemma arch_decode_irq_control_invocation_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and
   K (is_subject aag (fst slot) \<and>
      (\<forall>cap\<in>set caps. pas_cap_cur_auth aag cap) \<and>
      (args \<noteq> [] \<longrightarrow>
       (pasSubject aag, Control, pasIRQAbs aag (ucast (args ! 0)))
       \<in> pasPolicy aag))) (arch_decode_irq_control_invocation label args slot caps)"
  unfolding arch_decode_irq_control_invocation_def arch_check_irq_def
  apply (wp ensure_empty_rev lookup_slot_for_cnode_op_rev
            is_irq_active_rev whenE_inv
        | wp (once) hoare_drop_imps
        | simp add: Let_def)+
  apply safe
       apply simp+
    apply(blast intro: aag_Control_into_owns_irq )
   apply(drule_tac x="caps ! 0" in bspec)
    apply(fastforce intro: bang_0_in_set)
   apply(drule (1) is_cnode_into_is_subject; blast dest: prop_of_obj_ref_of_cnode_cap)
  apply(fastforce dest: is_cnode_into_is_subject intro: bang_0_in_set)
  done

lemma decode_irq_control_invocation_rev:
  "reads_equiv_valid_inv A aag (pas_refined aag and
   K (is_subject aag (fst slot) \<and>
      (\<forall>cap\<in>set caps. pas_cap_cur_auth aag cap) \<and>
      (args \<noteq> [] \<longrightarrow>
       (pasSubject aag, Control, pasIRQAbs aag (ucast (args ! 0)))
       \<in> pasPolicy aag))) (decode_irq_control_invocation label args slot caps)"
  unfolding decode_irq_control_invocation_def arch_check_irq_def
  apply (wp ensure_empty_rev lookup_slot_for_cnode_op_rev
            is_irq_active_rev whenE_inv arch_decode_irq_control_invocation_rev
         | wp (once) hoare_drop_imps
         | simp add: Let_def)+
  apply safe
       apply simp+
    apply(blast intro: aag_Control_into_owns_irq )
   apply(drule_tac x="caps ! 0" in bspec)
    apply(fastforce intro: bang_0_in_set)
   apply(drule (1) is_cnode_into_is_subject; blast dest: prop_of_obj_ref_of_cnode_cap)
  apply(fastforce dest: is_cnode_into_is_subject intro: bang_0_in_set)
  done

(* this one doesn't read from the state at all *)
lemma decode_irq_handler_invocation_rev:
  "reads_equiv_valid_inv A aag \<top>
      (decode_irq_handler_invocation label irq cps)"
  unfolding decode_irq_handler_invocation_def
  apply (wp | simp add: split_def Let_def | rule conjI impI)+
  done


lemma ensure_safe_mapping_reads_respects:
  "reads_respects aag l (K (authorised_slots aag entries)) (ensure_safe_mapping entries)"
  apply(rule gen_asm_ev)
  apply(case_tac entries)
   apply(rename_tac a, case_tac a)
   apply(rename_tac aa b, case_tac aa)
     apply(fastforce intro: returnOk_ev_pre)
    apply(rule equiv_valid_guard_imp)
     apply(wp mapME_x_ev' get_master_pte_reads_respects get_pte_reads_respects | wpc | simp)+
    apply(clarsimp simp: authorised_slots_def)
   apply simp
   apply(rule equiv_valid_guard_imp)
    apply(wp mapME_x_ev' get_master_pte_reads_respects | wpc | simp)+
   apply(fastforce simp: authorised_slots_def)
  apply(rename_tac b, case_tac b)
  apply(rename_tac a ba, case_tac a)
     apply(fastforce intro: returnOk_ev)
    apply simp
    apply(rule fail_ev)
   apply simp
   apply(rule equiv_valid_guard_imp)
   apply(wp mapME_x_ev' get_master_pde_reads_respects | wpc | simp)+
   apply(fastforce simp: authorised_slots_def)
  apply simp
  apply(rule equiv_valid_guard_imp)
  apply(wp mapME_x_ev' get_master_pde_reads_respects | wpc | simp)+
  apply(fastforce simp: authorised_slots_def)
  done

lemma lookup_pt_slot_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag (lookup_pd_slot pd vptr && ~~ mask pd_bits)))
     (lookup_pt_slot pd vptr)"
  apply(simp add: lookup_pt_slot_def lookup_pd_slot_def)
  apply(wp get_pde_rev | wpc | simp)+
  done


lemma create_mapping_entries_rev:
  "reads_equiv_valid_inv A aag (K (typ \<in> {ARMSmallPage,ARMLargePage}
                                   \<longrightarrow> is_subject aag (lookup_pd_slot pd vptr && ~~ mask pd_bits)))
     (create_mapping_entries bast vptr typ vm_rights attrib pd)"
  apply(rule gen_asm_ev)
  apply(case_tac "typ")
     apply(wp lookup_error_on_failure_rev lookup_pt_slot_rev | simp)+
  done


lemma check_vp_alignment_rev:
  "reads_equiv_valid_inv A aag \<top> (check_vp_alignment sz vptr)"
  unfolding check_vp_alignment_def
  apply(wp | simp add: crunch_simps split del: if_split)+
  done

lemmas reads_respects_f_inv = reads_respects_f[where Q="\<top>", simplified]

lemma gets_applyE:
  "(liftE $ gets f) >>=E (\<lambda> f. g (f x)) = liftE (gets_apply f x) >>=E g"
  apply(simp add: liftE_bindE)
  apply(rule gets_apply)
  done

lemma gets_apply_wp:
  "\<lbrace>\<lambda> s. P (f s x) s\<rbrace> gets_apply f x \<lbrace>P\<rbrace>"
  apply(simp add: gets_apply_def)
  apply wp
  done

lemma asid_high_bits_of_1:
  "asid_high_bits_of 1 = 0"
  apply(simp add: asid_high_bits_of_def asid_low_bits_def)
  done

lemma requiv_arm_asid_table_asid_high_bits_of_asid_eq'':
  "\<lbrakk>\<forall> asid. is_subject_asid aag asid; reads_equiv aag s t; pas_refined aag x\<rbrakk>
   \<Longrightarrow>
   arm_asid_table (arch_state s) (asid_high_bits_of base) =
   arm_asid_table (arch_state t) (asid_high_bits_of base)"
  apply (subgoal_tac "asid_high_bits_of 0 = asid_high_bits_of 1")
   apply(case_tac "base = 0")
    apply(subgoal_tac "is_subject_asid aag 1")
     apply ((auto intro: requiv_arm_asid_table_asid_high_bits_of_asid_eq
                       ) |
            (auto simp: asid_high_bits_of_def asid_low_bits_def))+
  done

lemma pas_cap_cur_auth_ASIDControlCap:
  "\<lbrakk>pas_cap_cur_auth aag (ArchObjectCap ASIDControlCap);
   reads_equiv aag s t; pas_refined aag x\<rbrakk>
  \<Longrightarrow> arm_asid_table (arch_state s) =
     arm_asid_table (arch_state t)"
  apply(rule ext)
  apply(subst asid_high_bits_of_shift[symmetric])
  apply(subst (3) asid_high_bits_of_shift[symmetric])
  apply(rule requiv_arm_asid_table_asid_high_bits_of_asid_eq'')
    apply(clarsimp simp: aag_cap_auth_def cap_links_asid_slot_def label_owns_asid_slot_def)
    apply(rule pas_refined_Control_into_is_subject_asid, blast+)
  done

lemma owns_cnode_owns_obj_ref_of_child_cnodes:
  "\<lbrakk>pas_refined aag s; is_subject aag (fst slot);
        cte_wp_at ((=) cap) slot s; is_cnode_cap cap\<rbrakk>
       \<Longrightarrow> is_subject aag (obj_ref_of cap)"
  by (blast intro: owns_cnode_owns_obj_ref_of_child_cnodes_threads_and_zombies)

lemma vspace_cap_rights_to_auth_mono:
  "R \<subseteq> S \<Longrightarrow> vspace_cap_rights_to_auth R \<subseteq> vspace_cap_rights_to_auth S"
  apply(auto simp: vspace_cap_rights_to_auth_def)
  done

lemma vspace_cap_rights_to_auth_mask_vm_rights:
  "vspace_cap_rights_to_auth
              (mask_vm_rights R d) \<subseteq> vspace_cap_rights_to_auth R"
  apply(rule vspace_cap_rights_to_auth_mono)
  apply(auto simp: mask_vm_rights_def dest: subsetD[OF validate_vm_rights_subseteq])
  done

lemma select_ext_ev_bind: "(\<And>s t. \<lbrakk>I s t; A s t; a s \<in> S; a t \<in> S\<rbrakk>
       \<Longrightarrow> a s = a t) \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> equiv_valid_inv I A P (g x)) \<Longrightarrow>
       (equiv_valid_inv I A P ((select_ext a S) >>= (\<lambda>r (s :: det_ext state). g r s)))"
  apply (clarsimp simp add: equiv_valid_def2 equiv_valid_2_def
                            select_ext_def bind_def gets_def return_def
                            get_def assert_def fail_def)
  apply (drule_tac x=s in meta_spec)
  apply (drule_tac x="a s" in meta_spec)
  apply (drule_tac x=t in meta_spec)
  apply simp
  apply (drule_tac x=s in spec)
  apply (drule_tac x=t in spec)
  apply simp
  apply force
  done

lemma select_ext_ev_bind_lift: "(\<And>s t. \<lbrakk>I s t; A s t; a s \<in> S; a t \<in> S\<rbrakk>
       \<Longrightarrow> a s = a t) \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> equiv_valid_inv I A P (g x)) \<Longrightarrow>
       (equiv_valid_inv I A P (doE x \<leftarrow> (liftE $ ((select_ext a S) :: ('a,det_ext) s_monad)); g x odE))"
  apply (simp add: bindE_def liftE_def lift_def)
  apply (rule select_ext_ev_bind)
  apply simp+
  done

lemma resolve_vaddr_reads_respects:
  "reads_respects aag l (K (is_subject aag (lookup_pd_slot pd vptr && ~~ mask pd_bits)) and
    (\<lambda>s. case kheap s (lookup_pd_slot pd vptr && ~~ mask pd_bits)
         of Some (ArchObj (PageDirectory pd')) \<Rightarrow>
           (case pd' (ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2))
            of PageTablePDE x y z \<Rightarrow>
              is_subject aag (lookup_pt_slot_no_fail (ptrFromPAddr x) vptr && ~~ mask pt_bits)
            | _ \<Rightarrow> True)
         | _ \<Rightarrow> True)) (resolve_vaddr pd vptr)"
  apply (simp add: resolve_vaddr_def
        | wp get_master_pte_reads_respects get_master_pde_reads_respects get_master_pde_wp | wpc)+
  apply (fastforce simp: obj_at_def split: pde.splits)
  done

lemma lookup_pt_slot_no_fail_is_subject:
  "\<lbrakk>(\<exists>\<rhd> pd) s; valid_vspace_objs s; pspace_aligned s; pas_refined aag s;
    is_subject aag pd; is_aligned pd pd_bits; vptr < kernel_base;
    kheap s pd = Some (ArchObj (PageDirectory pdo));
    pdo (ucast (vptr >> 20)) = PageTablePDE p x xa\<rbrakk>
    \<Longrightarrow> is_subject aag (lookup_pt_slot_no_fail (ptrFromPAddr p) vptr && ~~ mask pt_bits)"
  apply (clarsimp simp: lookup_pt_slot_no_fail_def)
  apply (drule valid_vspace_objsD)
    apply (simp add: obj_at_def)
   apply assumption
  apply (drule kheap_eq_state_vrefs_pas_refinedD)
    apply (erule vs_refs_no_global_pts_pdI)
    apply (drule(1) less_kernel_base_mapping_slots)
    apply (simp add: kernel_mapping_slots_def lookup_pd_slot_def pd_shifting_dual' triple_shift_fun)
   apply assumption
  apply (simp add: aag_has_Control_iff_owns)
  apply (drule_tac f="\<lambda>pde. valid_pde pde s" in arg_cong, simp)
  apply (clarsimp simp: obj_at_def kernel_base_kernel_mapping_slots)
  apply (erule pspace_alignedE, erule domI)
  apply (simp add: pt_bits_def pageBits_def)
  apply (subst is_aligned_add_helper, assumption)
   apply (rule shiftl_less_t2n)
    apply (rule order_le_less_trans, rule word_and_le1, simp)
   apply simp
  apply simp
  done

lemma arch_decode_invocation_reads_respects_f:
  notes reads_respects_f_inv' = reads_respects_f_inv[where st=st]
  notes hoare_whenE_wps[wp_split del]
  shows
  "reads_respects_f aag l (silc_inv aag st and invs and pas_refined aag
        and cte_wp_at ((=) (cap.ArchObjectCap cap)) slot
        and (\<lambda>s. \<forall>(cap, slot) \<in> set excaps. cte_wp_at ((=) cap) slot s)
        and K (\<forall>(cap, slot) \<in> {(cap.ArchObjectCap cap, slot)} \<union> set excaps.
                      aag_cap_auth aag (pasObjectAbs aag (fst slot)) cap \<and> is_subject aag (fst slot)
                   \<and> (\<forall>v \<in> cap_asid' cap. is_subject_asid aag v)))
        (arch_decode_invocation label args cap_index slot cap excaps)"
  unfolding arch_decode_invocation_def
  apply(rule equiv_valid_guard_imp)
   apply(subst gets_applyE)+
   apply (wp check_vp_wpR  reads_respects_f_inv'[OF get_asid_pool_rev]
              reads_respects_f_inv'[OF ensure_empty_rev]
             reads_respects_f_inv'[OF lookup_slot_for_cnode_op_rev]
             reads_respects_f_inv'[OF ensure_no_children_rev] select_wp
             reads_respects_f_inv'[OF ensure_safe_mapping_reads_respects]
             reads_respects_f_inv'[OF resolve_vaddr_reads_respects]
             reads_respects_f_inv'[OF create_mapping_entries_rev]
             reads_respects_f_inv'[OF check_vp_alignment_rev]
             reads_respects_f_inv'[OF lookup_error_on_failure_rev]
             find_pd_for_asid_reads_respects gets_apply_ev
             reads_respects_f_inv'[OF get_master_pde_reads_respects]
             is_final_cap_reads_respects find_pd_for_asid_authority2
             select_ext_ev_bind_lift
             select_ext_ev_bind_lift[simplified]
         | wpc
         | simp add: Let_def unlessE_whenE
         | wp (once) whenE_throwError_wp)+
  apply (intro impI allI conjI)
                              apply(rule requiv_arm_asid_table_asid_high_bits_of_asid_eq')
                                apply fastforce
                               apply(simp add: reads_equiv_f_def)
                              apply blast
                             apply(fastforce simp: aag_cap_auth_ASIDPoolCap)
                            apply(rule pas_cap_cur_auth_ASIDControlCap[where aag=aag])
                              apply fastforce
                             apply(simp add: reads_equiv_f_def)
                            apply blast
                           apply clarify
                           apply(subgoal_tac "excaps ! 0 \<in> set excaps", fastforce)
                           apply(rule nth_mem)
                            apply(erule less_trans[rotated], simp)
                          apply(subgoal_tac "excaps ! (Suc 0) \<in> set excaps")
                           apply(rule_tac slot="snd (excaps ! (Suc 0))"
                                       in owns_cnode_owns_obj_ref_of_child_cnodes)
                              apply blast
                             apply(fastforce)
                            apply(fastforce)
                           apply assumption
                          apply(fastforce intro: nth_mem)
                         apply clarify
                         apply(subgoal_tac "excaps ! Suc 0 \<in> set excaps")
                          apply(rule_tac cap="fst (excaps ! Suc 0)" and p="snd (excaps ! Suc 0)"
                                      in caps_of_state_pasObjectAbs_eq)
                              apply(rule cte_wp_at_caps_of_state)
                              apply fastforce
                             apply(erule cap_auth_conferred_cnode_cap)
                            apply fastforce
                           apply assumption
                          apply(fastforce intro: nth_mem)
                         apply(fastforce intro: nth_mem)
                        apply(subgoal_tac "excaps ! 0 \<in> set excaps")
                         apply(fastforce intro: aag_cap_auth_PageDirectoryCap_asid)
                        apply fastforce
                       apply(simp add: lookup_pd_slot_def)
                       apply(subgoal_tac "excaps ! 0 \<in> set excaps")
                        apply(subst vaddr_segment_nonsense)
                         apply(fastforce dest: cte_wp_valid_cap cap_aligned_valid
                                         simp: obj_ref_of_def cap_aligned_def cap_bits_def)
                        apply(fastforce dest: aag_cap_auth_PageDirectoryCap)
                       apply fastforce
                      apply(simp add: lookup_pd_slot_def)
                      apply(subgoal_tac "excaps ! 0 \<in> set excaps")
                       apply(subst vaddr_segment_nonsense)
                        apply(fastforce dest: cte_wp_valid_cap cap_aligned_valid
                                        simp: obj_ref_of_def cap_aligned_def cap_bits_def)
                       apply(fastforce dest: aag_cap_auth_PageDirectoryCap)
                      apply fastforce
                     apply fastforce
                    apply(subgoal_tac "excaps ! 0 \<in> set excaps")
                     apply(fastforce dest: aag_cap_auth_PageDirectoryCap)
                    apply fastforce
                   apply fastforce
                  (* clagged from Arch_AI *)
                  apply (simp add: linorder_not_le kernel_base_less_observation
                                   vmsz_aligned_def p_assoc_help)
                  apply (subst(asm) mask_lower_twice[symmetric])
                   prefer 2
                   apply (subst(asm) is_aligned_add_helper,
                          assumption)
                   apply (rule word_power_less_1)
                    apply(case_tac xc, simp_all)[1]
                   apply simp
                  apply(case_tac xc, simp_all)[1]
                 apply(rule ball_subset[OF _ vspace_cap_rights_to_auth_mask_vm_rights])
                 apply(fastforce simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
                apply(simp add: lookup_pd_slot_def)
                apply(subgoal_tac "excaps ! 0 \<in> set excaps")
                 apply(subst vaddr_segment_nonsense)
                  apply(fastforce dest: cte_wp_valid_cap cap_aligned_valid
                                  simp: obj_ref_of_def cap_aligned_def cap_bits_def)
                 apply(fastforce dest: aag_cap_auth_PageDirectoryCap)
                apply fastforce
               apply(simp add: lookup_pd_slot_def)
               apply(subgoal_tac "excaps ! 0 \<in> set excaps")
                apply(subst vaddr_segment_nonsense)
                 apply(fastforce dest: cte_wp_valid_cap cap_aligned_valid
                                 simp: obj_ref_of_def cap_aligned_def cap_bits_def)
                apply(fastforce dest: aag_cap_auth_PageDirectoryCap)
               apply fastforce
              apply fastforce
             apply(subgoal_tac "excaps ! 0 \<in> set excaps")
              apply(fastforce dest: aag_cap_auth_PageDirectoryCap)
             apply fastforce
            apply fastforce
           apply(fastforce dest: cte_wp_valid_cap simp: valid_cap_simps)
          apply(rule ball_subset[OF _ vspace_cap_rights_to_auth_mask_vm_rights])
          apply(fastforce simp: aag_cap_auth_def cap_auth_conferred_def arch_cap_auth_conferred_def)
         apply(subgoal_tac "excaps ! 0 \<in> set excaps")
          apply(fastforce intro: aag_cap_auth_PageDirectoryCap_asid)
         apply fastforce
        apply(subgoal_tac "excaps ! 0 \<in> set excaps")
         apply(subst vaddr_segment_nonsense)
          apply(fastforce dest: cte_wp_valid_cap cap_aligned_valid
                          simp: obj_ref_of_def cap_aligned_def cap_bits_def)
         apply(fastforce dest: aag_cap_auth_PageDirectoryCap)
        apply fastforce
       apply blast
      apply blast
     apply (blast dest:aag_can_read_self)
    apply (force dest:silc_inv_not_subject)
   apply(simp add: lookup_pd_slot_def)
   apply(subst vaddr_segment_nonsense)
    apply(fastforce dest: cte_wp_valid_cap cap_aligned_valid
                    simp: obj_ref_of_def cap_aligned_def cap_bits_def)
   apply(fastforce dest: aag_cap_auth_PageDirectoryCap)
  apply(clarsimp simp: lookup_pd_slot_def
                split: option.splits kernel_object.splits arch_kernel_obj.splits pde.splits)
  apply(subst(asm) vaddr_segment_nonsense)
   apply(fastforce dest: cte_wp_valid_cap cap_aligned_valid
                   simp: obj_ref_of_def cap_aligned_def cap_bits_def)
  apply(subst(asm) vaddr_segment_nonsense2)
   apply(fastforce dest: cte_wp_valid_cap cap_aligned_valid
                   simp: obj_ref_of_def cap_aligned_def cap_bits_def)
  apply (rule_tac pd=x and s=s in lookup_pt_slot_no_fail_is_subject)
          apply (erule exI)
         apply (simp add: invs_def valid_state_def)
        apply (simp add: invs_def valid_state_def valid_pspace_def)
       apply assumption
      apply (erule(1) aag_cap_auth_PageDirectoryCap)
     apply(fastforce dest: cte_wp_valid_cap cap_aligned_valid simp: obj_ref_of_def cap_aligned_def cap_bits_def pd_bits)
    apply simp
   apply assumption
  apply assumption
  done

lemma decode_domain_invocation_reads_respects_f:
  "reads_respects_f aag l \<top> (decode_domain_invocation label args excaps)"
apply (simp add: decode_domain_invocation_def)
apply (wp | wpc | simp)+
done

lemma decode_invocation_reads_respects_f:
  "reads_respects_f aag l
  (silc_inv aag st and pas_refined aag and valid_cap cap and invs and ct_active and cte_wp_at ((=) cap) slot
           and ex_cte_cap_to slot
           and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
           and (\<lambda>s. \<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_to r s)
           and (\<lambda>s. \<forall>cap \<in> set excaps. \<forall>r\<in>cte_refs (fst cap) (interrupt_irq_node s). ex_cte_cap_to r s)
           and (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> (fst x))
           and (\<lambda>s. \<forall>x \<in> set excaps. \<forall>r\<in>zobj_refs (fst x). ex_nonz_cap_to r s)
           and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at ((=) (fst x)) (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. real_cte_at (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. ex_cte_cap_wp_to is_cnode_cap (snd x) s)
           and (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at (interrupt_derived (fst x)) (snd x) s)
           and (is_subject aag \<circ> cur_thread) and
              K (is_subject aag (fst slot) \<and> pas_cap_cur_auth aag cap
                \<and> (\<forall>slot \<in> set excaps. is_subject aag (fst (snd slot)))
                \<and> (\<forall>slot \<in> set excaps. pas_cap_cur_auth aag (fst slot))))
  (decode_invocation label args cap_index slot cap excaps)"
  apply(rule equiv_valid_guard_imp)
   unfolding decode_invocation_def fun_app_def
  apply (wp reads_respects_f[OF decode_untyped_invocation_rev, where Q="\<top>"]
            reads_respects_f[OF decode_cnode_invocation_rev, where Q="\<top>"]
            decode_tcb_invocation_reads_respects_f
            decode_domain_invocation_reads_respects_f
            reads_respects_f[OF decode_irq_control_invocation_rev, where Q="\<top>"]
            reads_respects_f[OF decode_irq_handler_invocation_rev, where Q="\<top>"]
            arch_decode_invocation_reads_respects_f
       | wpc
       | simp
       | (rule hoare_pre, wp (once)))+
  apply (clarsimp simp: aag_has_Control_iff_owns split_def aag_cap_auth_def)
  apply (cases cap, simp_all)
  apply ((clarsimp simp: valid_cap_def cte_wp_at_eq_simp
                        is_cap_simps
                        ex_cte_cap_wp_to_weakenE[OF _ TrueI]
                        cap_auth_conferred_def cap_rights_to_auth_def pas_refined_all_auth_is_owns
           | rule conjI | (subst split_paired_Ex[symmetric], erule exI)
           | erule cte_wp_at_weakenE
           | drule(1) bspec
           | erule eq_no_cap_to_obj_with_diff_ref
           | assumption)+)[1]
   apply (rule conjI, assumption)
   apply (rule impI, erule subst, rule pas_refined_sita_mem [OF sita_controlled], auto
          simp: cte_wp_at_caps_of_state)[1]
  apply (rename_tac arch_cap)
  apply (subgoal_tac "(\<forall>x\<in>cap_asid' (ArchObjectCap arch_cap). is_subject_asid aag x) \<and>
          (\<forall>x\<in>set excaps. \<forall>v\<in>cap_asid' (fst x). is_subject_asid aag v)")
  prefer 2
  apply (clarsimp simp: cap_links_asid_slot_def label_owns_asid_slot_def)
  apply (fastforce dest!: pas_refined_Control)

  apply auto
  done

lemmas decode_invocation_reads_respects_f_g =
       reads_respects_f_g[OF decode_invocation_reads_respects_f doesnt_touch_globalsI,
                          where Q="\<top>", simplified, OF decode_inv_inv]

end

end
