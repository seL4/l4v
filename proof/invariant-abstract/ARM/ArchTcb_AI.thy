(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTcb_AI
imports Tcb_AI
begin

context Arch begin arch_global_naming

named_theorems Tcb_AI_assms


lemma activate_idle_invs[Tcb_AI_assms]:
  "\<lbrace>invs and ct_idle\<rbrace>
     arch_activate_idle_thread thread
   \<lbrace>\<lambda>rv. invs and ct_idle\<rbrace>"
  by (simp add: arch_activate_idle_thread_def)


lemma empty_fail_getRegister [intro!, simp, Tcb_AI_assms]:
  "empty_fail (getRegister r)"
  by (simp add: getRegister_def)


lemma same_object_also_valid:  (* arch specific *)
  "\<lbrakk> same_object_as cap cap'; s \<turnstile> cap'; wellformed_cap cap;
     cap_asid cap = None \<or> (\<exists>asid. cap_asid cap = Some asid \<and> 0 < asid \<and> asid \<le> 2^asid_bits - 1);
     cap_vptr cap = None; cap_asid_base cap = None \<rbrakk>
     \<Longrightarrow> s \<turnstile> cap"
  apply (cases cap,
         (clarsimp simp: same_object_as_def is_cap_simps cap_asid_def
                         wellformed_cap_def wellformed_acap_def
                         valid_cap_def bits_of_def cap_aligned_def
                   split: cap.split_asm arch_cap.split_asm option.splits)+)
  done

lemma same_object_obj_refs[Tcb_AI_assms]:
  "\<lbrakk> same_object_as cap cap' \<rbrakk>
     \<Longrightarrow> obj_refs cap = obj_refs cap'"
  apply (cases cap, simp_all add: same_object_as_def)
       apply ((clarsimp simp: is_cap_simps bits_of_def same_aobject_as_def
                      split: cap.split_asm )+)
  by (cases "the_arch_cap cap"; cases "the_arch_cap cap'"; simp)


definition
  is_cnode_or_valid_arch :: "cap \<Rightarrow> bool"
where
 "is_cnode_or_valid_arch cap \<equiv>
    is_cnode_cap cap
     \<or> (is_arch_cap cap
          \<and> (is_pt_cap cap \<longrightarrow> cap_asid cap \<noteq> None)
          \<and> (is_pd_cap cap \<longrightarrow> cap_asid cap \<noteq> None))"


definition (* arch specific *)
  "pt_pd_asid cap \<equiv> case cap of
    ArchObjectCap (PageTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PageDirectoryCap _ (Some asid)) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

lemmas pt_pd_asid_simps [simp] = (* arch specific *)
  pt_pd_asid_def [split_simps cap.split arch_cap.split option.split prod.split]

lemma checked_insert_is_derived: (* arch specific *)
  "\<lbrakk> same_object_as new_cap old_cap; is_cnode_or_valid_arch new_cap;
     obj_refs new_cap = obj_refs old_cap
         \<longrightarrow> table_cap_ref old_cap = table_cap_ref new_cap
            \<and> pt_pd_asid old_cap = pt_pd_asid new_cap\<rbrakk>
     \<Longrightarrow> is_derived m slot new_cap old_cap"
  apply (cases slot)
  apply (frule same_object_as_cap_master)
  apply (frule master_cap_obj_refs)
  apply (frule cap_master_eq_badge_none)
  apply (frule same_master_cap_same_types)
  apply (simp add: is_derived_def)
  apply clarsimp
  apply (auto simp: is_cap_simps cap_master_cap_def
                    is_cnode_or_valid_arch_def vs_cap_ref_def
                    table_cap_ref_def pt_pd_asid_def up_ucast_inj_eq
             split: cap.split_asm arch_cap.split_asm
                    option.split_asm)[1]
  done

lemma is_cnode_or_valid_arch_cap_asid: (* arch specific *)
  "is_cnode_or_valid_arch cap
       \<Longrightarrow> (is_pt_cap cap \<longrightarrow> cap_asid cap \<noteq> None)
             \<and> (is_pd_cap cap \<longrightarrow> cap_asid cap \<noteq> None)"
  by (auto simp add: is_cnode_or_valid_arch_def
                     is_cap_simps)

lemma checked_insert_tcb_invs[wp]: (* arch specific *)
  "\<lbrace>invs and cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref)
        and K (is_cnode_or_valid_arch new_cap) and valid_cap new_cap
        and tcb_cap_valid new_cap (target, ref)
        and K (is_pt_cap new_cap \<or> is_pd_cap new_cap
                         \<longrightarrow> cap_asid new_cap \<noteq> None)
        and (cte_wp_at (\<lambda>c. obj_refs c = obj_refs new_cap
                              \<longrightarrow> table_cap_ref c = table_cap_ref new_cap \<and>
                                 pt_pd_asid c = pt_pd_asid new_cap) src_slot)\<rbrace>
     check_cap_at new_cap src_slot
      (check_cap_at (cap.ThreadCap target) slot
       (cap_insert new_cap src_slot (target, ref))) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: check_cap_at_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule caps_of_state_valid_cap[where p=src_slot], fastforce)
  apply (frule caps_of_state_valid_cap[where p=slot], fastforce)
  apply (rule conjI, simp only: ex_cte_cap_wp_to_def)
   apply (rule_tac x=slot in exI)
   apply (clarsimp simp: cte_wp_at_caps_of_state same_object_as_cte_refs)
   apply (clarsimp simp: same_object_as_def2 cap_master_cap_simps
                  dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: valid_cap_def[where c="cap.ThreadCap x" for x])
   apply (erule cte_wp_atE[OF caps_of_state_cteD])
    apply (fastforce simp: obj_at_def is_obj_defs)
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (subgoal_tac "\<not> is_zombie new_cap")
    apply (simp add: same_object_zombies same_object_obj_refs)
    apply (erule(2) zombies_final_helperE)
      apply fastforce
     apply (fastforce simp add: cte_wp_at_caps_of_state)
    apply assumption
   apply (clarsimp simp: is_cnode_or_valid_arch_def is_cap_simps
                         is_valid_vtable_root_def)
  apply (rule conjI)
   apply (erule(1) checked_insert_is_derived, simp+)
  apply (auto simp: is_cnode_or_valid_arch_def is_cap_simps)
  done

crunch arch_get_sanitise_register_info, arch_post_modify_registers
  for tcb_at[wp, Tcb_AI_assms]: "tcb_at a"
crunch arch_get_sanitise_register_info, arch_post_modify_registers
  for invs[wp, Tcb_AI_assms]: "invs"
crunch arch_get_sanitise_register_info, arch_post_modify_registers
  for ex_nonz_cap_to[wp, Tcb_AI_assms]: "ex_nonz_cap_to a"

lemma finalise_cap_not_cte_wp_at[Tcb_AI_assms]:
  assumes x: "P cap.NullCap"
  shows      "\<lbrace>\<lambda>s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>
                finalise_cap cap fin
              \<lbrace>\<lambda>rv s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>"
  apply (cases cap, simp_all)
       apply (wp suspend_caps_of_state hoare_vcg_all_lift
            | simp
            | rule impI
            | rule hoare_drop_imps)+
     apply (clarsimp simp: ball_ran_eq x)
    apply (wp delete_one_caps_of_state
         | rule impI
         | simp add: deleting_irq_handler_def get_irq_slot_def x ball_ran_eq)+
    done


lemma table_cap_ref_max_free_index_upd[simp,Tcb_AI_assms]:
  "table_cap_ref (max_free_index_update cap) = table_cap_ref cap"
  by (simp add: free_index_update_def table_cap_ref_def split: cap.splits)

crunch arch_post_set_flags, arch_prepare_set_domain
  for typ_at[wp, Tcb_AI_assms]: "\<lambda>s. P (typ_at T p s)"
  and invs[wp, Tcb_AI_assms]: "invs"


interpretation Tcb_AI_1? : Tcb_AI_1
  where state_ext_t = state_ext_t
  and is_cnode_or_valid_arch = is_cnode_or_valid_arch
by (unfold_locales; fact Tcb_AI_assms)


lemma use_no_cap_to_obj_asid_strg: (* arch specific *)
  "(cte_at p s \<and> no_cap_to_obj_dr_emp cap s \<and> valid_cap cap s \<and> invs s)
         \<longrightarrow> cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap
                \<longrightarrow> table_cap_ref c = table_cap_ref cap \<and> pt_pd_asid c = pt_pd_asid cap) p s"
  apply (clarsimp simp: cte_wp_at_caps_of_state
                     no_cap_to_obj_with_diff_ref_def
           simp del: split_paired_All)
  apply (frule caps_of_state_valid_cap, fastforce)
  apply (erule allE)+
  apply (erule (1) impE)+
  apply (simp add: table_cap_ref_def pt_pd_asid_def split: cap.splits arch_cap.splits option.splits prod.splits)
  apply (fastforce simp: table_cap_ref_def valid_cap_simps elim!: asid_low_high_bits)+
  done

lemma cap_delete_no_cap_to_obj_asid[wp, Tcb_AI_assms]:
  "\<lbrace>no_cap_to_obj_dr_emp cap\<rbrace>
     cap_delete slot
   \<lbrace>\<lambda>rv. no_cap_to_obj_dr_emp cap\<rbrace>"
  apply (simp add: cap_delete_def
                   no_cap_to_obj_with_diff_ref_ran_caps_form)
  apply wp
  apply (rule use_spec)
  apply (rule rec_del_all_caps_in_range)
     apply (simp add: table_cap_ref_def[simplified, split_simps cap.split]
              | rule obj_ref_none_no_asid)+
  done

lemma as_user_valid_cap[wp]:
  "\<lbrace>valid_cap c\<rbrace> as_user a b \<lbrace>\<lambda>rv. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)

lemma as_user_ipc_tcb_cap_valid4[wp]:
  "\<lbrace>\<lambda>s. tcb_cap_valid cap (t, tcb_cnode_index 4) s\<rbrace>
    as_user a b
   \<lbrace>\<lambda>rv. tcb_cap_valid cap (t, tcb_cnode_index 4)\<rbrace>"
  apply (simp add: as_user_def set_object_def get_object_def)
  apply (wp | wpc | simp)+
  apply (clarsimp simp: tcb_cap_valid_def obj_at_def
                        pred_tcb_at_def is_tcb
                 dest!: get_tcb_SomeD)
  apply (clarsimp simp: get_tcb_def)
  done

lemma tc_invs[Tcb_AI_assms]:
  "\<lbrace>invs and tcb_at a
       and (case_option \<top> (valid_cap o fst) e)
       and (case_option \<top> (valid_cap o fst) f)
       and (case_option \<top> (case_option \<top> (valid_cap o fst) o snd) g)
       and (case_option \<top> (cte_at o snd) e)
       and (case_option \<top> (cte_at o snd) f)
       and (case_option \<top> (case_option \<top> (cte_at o snd) o snd) g)
       and (case_option \<top> (no_cap_to_obj_dr_emp o fst) e)
       and (case_option \<top> (no_cap_to_obj_dr_emp o fst) f)
       and (case_option \<top> (case_option \<top> (no_cap_to_obj_dr_emp o fst) o snd) g)
       \<comment> \<open>only set prio \<le> mcp of authorising thread\<close>
       and (\<lambda>s. case_option True (\<lambda>(pr, auth). mcpriority_tcb_at (\<lambda>mcp. pr \<le> mcp) auth s) pr)
       \<comment> \<open>only set mcp \<le> mcp of authorising thread\<close>
       and (\<lambda>s. case_option True (\<lambda>(mcp, auth). mcpriority_tcb_at (\<lambda>m. mcp \<le> m) auth s) mcp)
       and K (case_option True (is_cnode_cap o fst) e)
       and K (case_option True (is_valid_vtable_root o fst) f)
       and K (case_option True (\<lambda>v. case_option True
                          ((swp valid_ipc_buffer_cap (fst v)
                             and is_arch_cap and is_cnode_or_valid_arch)
                                o fst) (snd v)) g)
       and K (case_option True (\<lambda>bl. length bl = word_bits) b)\<rbrace>
      invoke_tcb (ThreadControl a sl b mcp pr e f g)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: split_def set_mcpriority_def cong: option.case_cong)
  apply (rule hoare_weaken_pre)
   apply wp
      (* takes long: (30 sec) *)
      apply ((simp only: simp_thms cong: conj_cong
        | (strengthen invs_strengthen)+
        | rule wp_split_const_if wp_split_const_if_R
                   hoare_vcg_all_liftE_R
                   hoare_vcg_conj_elimE hoare_vcg_const_imp_liftE_R
                   hoare_vcg_conj_liftE_R
        | (wp out_invs_trivial case_option_wpE cap_delete_deletes
             cap_delete_valid_cap cap_insert_valid_cap out_cte_at
             cap_insert_cte_at cap_delete_cte_at out_valid_cap
             hoare_vcg_const_imp_liftE_R hoare_vcg_all_liftE_R
             thread_set_tcb_ipc_buffer_cap_cleared_invs
             thread_set_invs_trivial[OF ball_tcb_cap_casesI]
             hoare_vcg_all_lift thread_set_valid_cap out_emptyable
             check_cap_inv [where P="valid_cap c" for c]
             check_cap_inv [where P="tcb_cap_valid c p" for c p]
             check_cap_inv[where P="cte_at p0" for p0]
             check_cap_inv[where P="tcb_at p0" for p0]
             thread_set_cte_at
             thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
             thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             checked_insert_no_cap_to
             out_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             thread_set_ipc_tcb_cap_valid
             hoare_weak_lift_imp hoare_weak_lift_imp_conj)[1]
        | simp add: ran_tcb_cap_cases dom_tcb_cap_cases[simplified]
                    emptyable_def
        | wpc
        | strengthen use_no_cap_to_obj_asid_strg
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index 0"]
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index (Suc 0)"])+)
  apply (clarsimp simp: tcb_at_cte_at_0 tcb_at_cte_at_1[simplified] is_nondevice_page_cap_arch_def
                        is_cap_simps is_valid_vtable_root_def is_nondevice_page_cap_simps
                        is_cnode_or_valid_arch_def tcb_cap_valid_def
                        invs_valid_objs cap_asid_def vs_cap_ref_def
                 split: option.split_asm )+
      apply (simp add: case_bool_If valid_ipc_buffer_cap_def is_nondevice_page_cap_simps
                       is_nondevice_page_cap_arch_def
                split: arch_cap.splits if_splits)+
  done


lemma check_valid_ipc_buffer_inv:
  "\<lbrace>P\<rbrace> check_valid_ipc_buffer vptr cap \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: check_valid_ipc_buffer_def whenE_def
             cong: cap.case_cong arch_cap.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp | simp add: whenE_def if_apply_def2 | wpcw)+
  done

lemma check_valid_ipc_buffer_wp[Tcb_AI_assms]:
  "\<lbrace>\<lambda>(s::'state_ext::state_ext state). is_arch_cap cap \<and> is_cnode_or_valid_arch cap
          \<and> valid_ipc_buffer_cap cap vptr
          \<and> is_aligned vptr msg_align_bits
             \<longrightarrow> P s\<rbrace>
     check_valid_ipc_buffer vptr cap
   \<lbrace>\<lambda>rv. P\<rbrace>,-"
  apply (simp add: check_valid_ipc_buffer_def whenE_def
             cong: cap.case_cong arch_cap.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp | simp add: whenE_def split del: if_split | wpc)+
  apply (clarsimp simp: is_cap_simps is_cnode_or_valid_arch_def
                        valid_ipc_buffer_cap_def)
  done

lemma derive_no_cap_asid[wp,Tcb_AI_assms]:
  "\<lbrace>(no_cap_to_obj_with_diff_ref cap S)::'state_ext::state_ext state\<Rightarrow>bool\<rbrace>
     derive_cap slot cap
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref rv S\<rbrace>,-"
  apply (simp add: derive_cap_def arch_derive_cap_def
             cong: cap.case_cong)
  apply (rule hoare_pre)
   apply (wp | simp | wpc)+
  apply (auto simp add: no_cap_to_obj_with_diff_ref_Null,
         auto simp add: no_cap_to_obj_with_diff_ref_def
                        table_cap_ref_def)
  done


lemma decode_set_ipc_inv[wp,Tcb_AI_assms]:
  "\<lbrace>P::'state_ext::state_ext state \<Rightarrow> bool\<rbrace> decode_set_ipc_buffer args cap slot excaps \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp   add: decode_set_ipc_buffer_def whenE_def
                     split_def
          split del: if_split)
  apply (rule hoare_pre, wp check_valid_ipc_buffer_inv)
  apply simp
  done

lemma no_cap_to_obj_with_diff_ref_update_cap_data[Tcb_AI_assms]:
  "no_cap_to_obj_with_diff_ref c S s \<longrightarrow>
    no_cap_to_obj_with_diff_ref (update_cap_data P x c) S s"
  apply (case_tac "update_cap_data P x c = NullCap")
   apply (simp add: no_cap_to_obj_with_diff_ref_Null)
  apply (subgoal_tac "vs_cap_ref (update_cap_data P x c)
                                 = vs_cap_ref c")
   apply (simp add: no_cap_to_obj_with_diff_ref_def
                    update_cap_objrefs)
  apply (clarsimp simp: update_cap_data_closedform
                        table_cap_ref_def
                        arch_update_cap_data_def
                 split: cap.split)
  apply simp
  done


lemma update_cap_valid[Tcb_AI_assms]:
  "valid_cap cap (s::'state_ext::state_ext state) \<Longrightarrow>
   valid_cap (case capdata of
              None \<Rightarrow> cap_rights_update rs cap
            | Some x \<Rightarrow> update_cap_data p x
                     (cap_rights_update rs cap)) s"
  apply (case_tac capdata, simp_all)[1]
  apply (case_tac cap,
         simp_all add: update_cap_data_def cap_rights_update_def
                       is_cap_defs Let_def split_def valid_cap_def
                       badge_update_def the_cnode_cap_def cap_aligned_def
                       arch_update_cap_data_def split: bool.splits)
   apply (simp add: word_bits_def)
  apply (rename_tac arch_cap)
  using valid_validate_vm_rights[simplified valid_vm_rights_def]
  apply (case_tac arch_cap, simp_all add: acap_rights_update_def
                                     split: option.splits prod.splits bool.splits)
  done

crunch switch_to_thread
  for pred_tcb_at: "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps)

crunch invoke_tcb
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (ignore: check_cap_at setNextPC zipWithM
       wp: hoare_drop_imps mapM_x_wp' check_cap_inv
     simp: crunch_simps)

end

global_interpretation Tcb_AI?: Tcb_AI
  where is_cnode_or_valid_arch = ARM.is_cnode_or_valid_arch
 proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (unfold_locales; fact Tcb_AI_assms)
qed

end
