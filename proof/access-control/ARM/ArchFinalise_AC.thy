(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchFinalise_AC
imports Finalise_AC
begin

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for Finalise_AC locale *)

lemma sbn_st_vrefs[Arch_assms, wp]:
  "set_bound_notification t st \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp wp: set_object_wp dxo_wp_weak)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def
                 elim!: rsubst[where P=P, OF _ ext]
                 dest!: get_tcb_SomeD)
  done

lemma arch_finalise_cap_auth'[Arch_assms]:
  "\<lbrace>pas_refined aag\<rbrace> arch_finalise_cap x12 final \<lbrace>\<lambda>rv s. pas_cap_cur_auth aag (fst rv)\<rbrace>"
  unfolding arch_finalise_cap_def
  by (wp | wpc | simp add: comp_def hoare_TrueI[where P = \<top>] split del: if_split)+

lemma arch_finalise_cap_obj_refs[Arch_assms]:
  "\<lbrace>\<lambda>s. \<forall>x \<in> aobj_ref' acap. P x\<rbrace>
   arch_finalise_cap acap slot
   \<lbrace>\<lambda>rv s. \<forall>x \<in> obj_refs_ac (fst rv). P x\<rbrace>"
  by (wpsimp simp: arch_finalise_cap_def)

lemma arch_finalise_cap_makes_halted[Arch_assms]:
  "\<lbrace>\<top>\<rbrace> arch_finalise_cap arch_cap ex \<lbrace>\<lambda>rv s. \<forall>t\<in>obj_refs_ac (fst rv). halted_if_tcb t s\<rbrace>"
  apply (case_tac arch_cap, simp_all add: arch_finalise_cap_def)
  by (wpsimp simp: valid_cap_def split: option.split bool.split)+

lemma arch_cap_cleanup_wf[Arch_assms]:
  "\<lbrakk> arch_cap_cleanup_opt acap \<noteq> NullCap; \<not> is_arch_cap (arch_cap_cleanup_opt acap) \<rbrakk>
   \<Longrightarrow> (\<exists>irq. arch_cap_cleanup_opt acap = IRQHandlerCap irq \<and> is_subject_irq aag irq)"
  by simp

lemma arch_finalise_cap_respects[Arch_assms, wp]:
  "\<lbrace>integrity aag X st and invs and pas_refined aag and valid_cap (ArchObjectCap cap)
                       and K (pas_cap_cur_auth aag (ArchObjectCap cap))\<rbrace>
   arch_finalise_cap cap final
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (wpsimp wp: unmap_page_respects unmap_page_table_respects delete_asid_respects)
  apply (auto simp: cap_auth_conferred_def arch_cap_auth_conferred_def is_page_cap_def
                    aag_cap_auth_def pas_refined_all_auth_is_owns valid_cap_simps
                    cap_links_asid_slot_def label_owns_asid_slot_def
             intro: pas_refined_Control_into_is_subject_asid)
  done

crunch prepare_thread_delete
  for inv[Arch_assms,wp]: P

crunch arch_finalise_cap
  for pas_refined[wp]: "pas_refined aag"

(* strengthen preconditions for locale assumptions *)
lemma [Arch_assms]:
  shows
    "\<lbrace>pas_refined aag and invs and valid_arch_cap acap\<rbrace>
     arch_finalise_cap acap ex
     \<lbrace>\<lambda>_. pas_refined aag\<rbrace>"
  and
    "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s \<and> valid_mdb s \<and> valid_cur_fpu s \<and>
          cte_wp_at ((=) cap) sl s \<and> valid_objs s \<and> sym_refs (state_refs_of s) \<and>
          (cap_irqs cap \<noteq> {} \<longrightarrow> if_unsafe_then_cap s \<and> valid_global_refs s) \<and>
          (is_arch_cap cap \<longrightarrow> pspace_aligned s \<and> pspace_distinct s \<and> valid_vspace_objs s \<and>
                               valid_arch_state s \<and> valid_arch_caps s)\<rbrace>
     finalise_cap cap x
     \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) cap\<rbrace>"
  by (wpsimp wp: finalise_cap_replaceable)+

(* trivial assumptions *)
lemma [Arch_assms]:
  shows prepare_thread_delete_respects:
    "\<lbrace>integrity aag X st and pas_refined aag and valid_cur_fpu and K (is_subject aag p)\<rbrace>
     prepare_thread_delete p
     \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  by wpsimp

lemmas [Arch_assms] =
  finalise_cap_valid_list
  valid_cur_fpu_lift_arch

lemmas Finalise_AC_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

global_interpretation Finalise_AC?: Finalise_AC
proof goal_cases
  case 1 show ?case
    by (unfold_locales; (fact ARM.Finalise_AC_assms)?)
qed

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for Finalise_AC_2 locale *)

lemma cap_revoke_respects'[Arch_assms]:
  "s \<turnstile> \<lbrace>(\<lambda>s. trp \<longrightarrow> integrity aag X st s) and K (is_subject aag (fst slot))
                                           and pas_refined aag and einvs and simple_sched_action\<rbrace>
       cap_revoke slot
       \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>,
       \<lbrace>\<lambda>_. (\<lambda>s. trp \<longrightarrow> integrity aag X st s) and pas_refined aag\<rbrace>"
proof (induct rule: cap_revoke.induct[where ?a1.0=s])
  case (1 slot s)
  show ?case
    apply (subst cap_revoke.simps)
    apply (rule hoare_pre_spec_validE)
     apply (wp "1.hyps")
            apply ((wp preemption_point_inv' | simp add: integrity_subjects_def pas_refined_def)+)[1]
           apply (wp select_ext_weak_wp cap_delete_respects cap_delete_pas_refined
                  | simp split del: if_split | wp (once) hoare_vcg_const_imp_lift hoare_drop_imps)+
    by (auto simp: emptyable_def descendants_of_def
             dest: reply_slot_not_descendant
            intro: cca_owned)
qed

lemma finalise_cap_caps_of_state_nullinv[Arch_assms]:
  "\<lbrace>\<lambda>s. P (caps_of_state s) \<and> (\<forall>p. P ((caps_of_state s)(p \<mapsto> NullCap)))\<rbrace>
   finalise_cap cap final
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  by (cases cap;
      wpsimp wp: suspend_caps_of_state unbind_notification_caps_of_state
                 unbind_notification_cte_wp_at
                 hoare_vcg_all_lift hoare_drop_imps
                 deleting_irq_handler_caps_of_state_nullinv
           simp: fun_upd_def[symmetric] if_apply_def2 split_del: if_split)

lemma finalise_cap_fst_ret[Arch_assms]:
  "\<lbrace>\<lambda>_. P NullCap \<and> (\<forall>a b c. P (Zombie a b c))\<rbrace>
   finalise_cap cap is_final
   \<lbrace>\<lambda>rv _. P (fst rv)\<rbrace>"
  including classic_wp_pre
  apply (cases cap, simp_all add: arch_finalise_cap_def split del: if_split)
  apply (wp | simp add: comp_def split del: if_split | fastforce)+
  apply (rule hoare_pre)
  apply (wp | simp | (rule hoare_pre, wpc))+
  done

lemmas Finalise_AC_2_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

global_interpretation Finalise_AC_2?: Finalise_AC_2
proof goal_cases
  case 1 show ?case
    by (unfold_locales; (fact ARM.Finalise_AC_2_assms)?)
qed

end