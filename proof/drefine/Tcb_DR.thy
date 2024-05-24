(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Tcb_DR
imports Ipc_DR Arch_DR
begin

context begin interpretation Arch . (*FIXME: arch_split*)

(*
 * A "normal" TCB is a non-idle TCB. (Idle is special, because it
 * doesn't get lifted up to capDL.
 *)
abbreviation "normal_tcb_at x \<equiv> (tcb_at x) and (not_idle_thread x)"

(*
 * Translate an abstract spec TCB invocation into a CDL TCB invocation.
 *)
definition translate_tcb_invocation_thread_ctrl_buffer :: "(word32 \<times> (cap\<times> word32\<times> bool list) option) option \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) option"
where
  "translate_tcb_invocation_thread_ctrl_buffer buffer \<equiv>
  (case buffer of None \<Rightarrow> None | Some (a, None) \<Rightarrow> None
  | Some (a, Some (c,d)) \<Rightarrow> Some (transform_cap c, (transform_cslot_ptr d)))"

definition
  translate_tcb_invocation :: "Invocations_A.tcb_invocation \<Rightarrow> cdl_tcb_invocation"
where
  "translate_tcb_invocation x \<equiv>
    case x of
        Invocations_A.ReadRegisters oid' x' _ _ \<Rightarrow>
          Invocations_D.ReadRegisters oid' x' 0 0
      | Invocations_A.WriteRegisters oid' b' regs' _ \<Rightarrow>
          Invocations_D.WriteRegisters oid' b' [0] 0
      | Invocations_A.CopyRegisters dest_tcb src_tcb a b c d e \<Rightarrow>
          Invocations_D.CopyRegisters dest_tcb src_tcb a b c d 0
      | Invocations_A.ThreadControl target_tcb target_slot faultep _ _ croot vroot buffer \<Rightarrow>
          Invocations_D.ThreadControl
             target_tcb
             (transform_cslot_ptr target_slot)
             (option_map of_bl faultep)
             (option_map (\<lambda>r. ((transform_cap \<circ> fst) r,(transform_cslot_ptr \<circ> snd) r)) croot)
             (option_map (\<lambda>r. ((transform_cap \<circ> fst) r,(transform_cslot_ptr \<circ> snd) r)) vroot)
             (translate_tcb_invocation_thread_ctrl_buffer buffer)
      | Invocations_A.Suspend target_tcb \<Rightarrow>
          Invocations_D.Suspend target_tcb
      | Invocations_A.Resume target_tcb \<Rightarrow>
          Invocations_D.Resume target_tcb
      | Invocations_A.NotificationControl target_tcb opt \<Rightarrow>
          Invocations_D.NotificationControl target_tcb opt
      | Invocations_A.SetTLSBase target_tcb x \<Rightarrow>
          Invocations_D.SetTLSBase target_tcb"

lemma decode_set_ipc_buffer_translate_tcb_invocation:
  "\<lbrakk>x \<noteq> [];excaps ! 0 = (a,b,c)\<rbrakk> \<Longrightarrow>
    (\<And>s. \<lbrace>(=) s\<rbrace> decode_set_ipc_buffer x (cap.ThreadCap t) slot' excaps
    \<lbrace>\<lambda>rv s'. s' = s \<and> rv = tcb_invocation.ThreadControl t slot' None None None None None (tc_new_buffer rv) \<and>
      translate_tcb_invocation_thread_ctrl_buffer (tc_new_buffer rv) = (if (x ! 0) = 0 then None
      else Some (reset_mem_mapping (transform_cap a), transform_cslot_ptr (b, c)))
    \<rbrace>,\<lbrace>\<lambda>ft. (=) s\<rbrace>)"
  apply (clarsimp simp:decode_set_ipc_buffer_def whenE_def | rule conjI)+
    apply (wp , simp_all add:translate_tcb_invocation_thread_ctrl_buffer_def)
   apply (clarsimp | rule conjI)+
   apply (wp , clarsimp simp:translate_tcb_invocation_thread_ctrl_buffer_def)
  apply (wp | clarsimp | rule conjI)+
   apply (simp add:check_valid_ipc_buffer_def)
   apply (wpc|wp)+
   apply (simp add:derive_cap_def split del:if_split)
   apply (wpsimp simp: o_def arch_derive_cap_def split_del:if_split)
  apply clarsimp
  apply (clarsimp simp:transform_mapping_def)
  done

lemma derive_cap_translate_tcb_invocation:
 "\<lbrace>(=) s\<rbrace>derive_cap a b \<lbrace>\<lambda>rv. (=) s\<rbrace>,\<lbrace>\<lambda>rv. \<top>\<rbrace>"
  apply (simp add:derive_cap_def)
  apply (case_tac b)
             apply (clarsimp simp:ensure_no_children_def whenE_def |wp)+
   apply (clarsimp simp:arch_derive_cap_def)
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap)
       apply (clarsimp simp:ensure_no_children_def whenE_def |wp)+
    apply (clarsimp split:option.splits | rule conjI | wp)+
  done

lemma derive_cnode_cap_as_vroot:
  "\<lbrace>(=) s \<rbrace> derive_cap (ba, ca) aa
   \<lbrace>\<lambda>vroot_cap'.
      if is_valid_vtable_root vroot_cap' then \<lambda>sa. sa = s  \<and> vroot_cap' = aa
      else (=) s\<rbrace>, \<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (simp add:derive_cap_def is_valid_vtable_root_def)
  apply (case_tac aa)
             apply (clarsimp|wp)+
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap)
       apply (clarsimp simp:arch_derive_cap_def split:option.splits |wp)+
    apply (intro conjI)
     apply (clarsimp simp:arch_derive_cap_def split:option.splits |wp)+
   apply (intro conjI)
    apply (clarsimp simp:arch_derive_cap_def | wp)+
  done

lemma derive_cnode_cap_as_croot:
  "\<lbrace>(=) s\<rbrace> derive_cap (b, c) a
   \<lbrace>\<lambda>croot_cap'. if Structures_A.is_cnode_cap croot_cap' then \<lambda>sa. s = sa \<and> croot_cap' = a \<and> is_cnode_cap a else (=) s\<rbrace>,\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp:derive_cap_def is_cap_simps)
  apply (case_tac a)
             apply (clarsimp|wp)+
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap)
       apply (clarsimp simp:arch_derive_cap_def split:option.splits |wp)+
    apply (intro conjI)
     apply (clarsimp simp:arch_derive_cap_def split:option.splits |wp)+
   apply (intro conjI)
    apply (clarsimp simp:arch_derive_cap_def | wp)+
  done

lemma valid_vtable_root_update:
  "\<lbrakk> is_valid_vtable_root (CSpace_A.update_cap_data False x aa)\<rbrakk>
         \<Longrightarrow> CSpace_A.update_cap_data False x aa = aa"
  apply (clarsimp simp: update_cap_data_def badge_update_def is_valid_vtable_root_def Let_def
                        the_cnode_cap_def is_arch_cap_def arch_update_cap_data_def the_arch_cap_def
                  split: if_split_asm cap.split_asm)
  done

lemma decode_set_space_translate_tcb_invocation:
  "\<And>s. \<lbrace>(=) s\<rbrace> decode_set_space x (cap.ThreadCap t) slot' (excaps')
    \<lbrace>\<lambda>rv s'. s' = s \<and>
    (rv =  tcb_invocation.ThreadControl t slot' (tc_new_fault_ep rv) None None (tc_new_croot rv) (tc_new_vroot rv) None) \<and>
    (tc_new_fault_ep rv = Some (to_bl (x!0)))
    \<and> (option_map (\<lambda>c. snd c)  (tc_new_croot rv) = Some (snd (excaps' ! 0)))
    \<and> (option_map (\<lambda>c. snd c)  (tc_new_vroot rv) = Some (snd (excaps' ! Suc 0)))
    \<and> (option_map (\<lambda>c. fst c ) (tc_new_croot rv)
        = (if (x!1 = 0) then Some (fst (excaps' ! 0)) else Some (update_cap_data False (x ! Suc 0) (fst (excaps' ! 0)))))
    \<and> (option_map (\<lambda>c. fst c)  (tc_new_vroot rv) = Some (fst (excaps' ! Suc 0)))
    \<and> (option_map (\<lambda>c. is_cnode_cap (fst c)) (tc_new_croot rv) = Some True)
    \<rbrace>,\<lbrace>\<lambda>rv. (=) s\<rbrace>"
  supply if_cong[cong]
  apply (case_tac "excaps' ! 0")
  apply (case_tac "excaps' ! Suc 0")
  apply (clarsimp simp:decode_set_space_def whenE_def | rule conjI)+
     apply wp
    apply (clarsimp simp: | rule conjI)+
     apply (wp|clarsimp)+
         apply (rule_tac P ="croot_cap' = a \<and> is_cnode_cap a" in hoare_gen_asmE)
         apply clarsimp
         apply (rule validE_validE_R)
         apply (wp hoare_post_impErr[OF derive_cnode_cap_as_vroot],simp)
         apply (wp|clarsimp)+
       apply (wp hoare_post_impErr[OF derive_cnode_cap_as_croot],simp)
       apply (wp|clarsimp)+
   apply (clarsimp simp:whenE_def | rule conjI | wp)+
        apply (rule_tac P ="croot_cap' = update_cap_data False (x! 1) a \<and> is_cnode_cap croot_cap'" in hoare_gen_asmE)
        apply (rule validE_validE_R)
        apply simp
        apply (rule_tac s1 = s in hoare_post_impErr[OF derive_cnode_cap_as_vroot],simp)
         apply (rule conjI|simp split:if_split_asm)+
       apply (wp|clarsimp)+
      apply (rule validE_validE_R)
      apply (rule_tac s1 = s in hoare_post_impErr[OF derive_cnode_cap_as_croot])
       apply (wp|clarsimp)+
       apply (clarsimp simp:whenE_def | rule conjI | wp)+
        apply (rule_tac P ="croot_cap' = a \<and> is_cnode_cap a" in hoare_gen_asmE)
        apply clarsimp
        apply (rule validE_validE_R)
        apply (rule_tac s1 = s in hoare_post_impErr[OF derive_cnode_cap_as_vroot],simp)
         apply (clarsimp split:if_splits simp:valid_vtable_root_update)
        apply (wp|clarsimp)+
      apply (wp hoare_post_impErr[OF derive_cnode_cap_as_croot],simp)
      apply (wp|clarsimp)+
  apply (clarsimp simp: | rule conjI | wp)+
       apply (rule_tac P ="croot_cap' = update_cap_data False (x! 1) a \<and> is_cnode_cap croot_cap'" in hoare_gen_asmE)
       apply (rule validE_validE_R)
       apply simp
       apply (rule_tac s1 = s in hoare_post_impErr[OF derive_cnode_cap_as_vroot],simp)
        apply (rule conjI|simp split:if_split_asm)+
         apply (rule valid_vtable_root_update)
         apply clarsimp+
      apply (wp|clarsimp)+
     apply (rule validE_validE_R)
     apply (rule hoare_post_impErr[OF derive_cnode_cap_as_croot])
      apply fastforce+
    apply (wp|clarsimp)+
  done

lemma decode_tcb_cap_label_not_match:
  "\<lbrakk>\<forall>ui. Some (TcbIntent ui) \<noteq> transform_intent (invocation_type label') args'; cap' = Structures_A.ThreadCap t\<rbrakk>
    \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_tcb_invocation label' args' cap' slot' excaps' \<lbrace>\<lambda>r. \<bottom>\<rbrace>,\<lbrace>\<lambda>e. (=) s\<rbrace>"
  apply (simp add:Decode_A.decode_tcb_invocation_def)
  apply (case_tac "gen_invocation_type label'")
    apply (simp_all add:transform_intent_def flip: gen_invocation_type_eq)
    apply wp
    apply (simp_all add: whenE_def transform_intent_tcb_defs
                  split: option.splits)
    apply (simp_all split:List.list.split list.split_asm option.splits add: gen_invocation_type_eq)
      apply (simp add: decode_read_registers_def decode_write_registers_def decode_set_ipc_buffer_def
                       decode_copy_registers_def decode_set_space_def decode_tcb_configure_def
                       decode_set_priority_def decode_set_mcpriority_def decode_set_sched_params_def
            | wp)+
  done

lemma is_cnode_cap_update_cap_data:
  "Structures_A.is_cnode_cap (CSpace_A.update_cap_data x w a) \<Longrightarrow> is_cnode_cap a"
  apply (case_tac a)
    apply (clarsimp simp:update_cap_data_def arch_update_cap_data_def is_arch_cap_def badge_update_def
      is_cap_simps split:if_split_asm)+
done

lemma update_cnode_cap_data:
  "\<lbrakk>Some af = (if w = 0 then Some ab else Some (CSpace_A.update_cap_data False w ab)); Structures_A.is_cnode_cap af\<rbrakk>
  \<Longrightarrow> transform_cap af = cdl_update_cnode_cap_data (transform_cap ab) w"
  apply (clarsimp simp:is_cap_simps)
  apply (clarsimp split:if_splits)
    apply (simp add:cdl_update_cnode_cap_data_def CSpace_D.update_cap_data_def)
  apply (clarsimp simp: update_cap_data_def arch_update_cap_data_def split:if_splits)
  apply ((cases ab,simp_all add:badge_update_def)+)[2]
  apply (clarsimp simp:is_cap_simps the_cnode_cap_def word_size split:if_split_asm simp:Let_def)
  apply (clarsimp simp:cdl_update_cnode_cap_data_def word_bits_def of_drop_to_bl
    word_size mask_twice dest!:leI)
done

lemma decode_tcb_corres:
  "\<lbrakk> Some (TcbIntent ui) = transform_intent (invocation_type label') args';
     cap = transform_cap cap';
     cap' = Structures_A.ThreadCap t;
     slot = transform_cslot_ptr slot';
     excaps = transform_cap_list excaps' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> (\<lambda>x y. x = translate_tcb_invocation y)) \<top> \<top>
     (Tcb_D.decode_tcb_invocation cap slot excaps ui)
     (Decode_A.decode_tcb_invocation label' args' cap' slot' excaps')"
  supply if_cong[cong]
  apply (unfold Tcb_D.decode_tcb_invocation_def Decode_A.decode_tcb_invocation_def)
  apply (drule sym, frule transform_tcb_intent_invocation)
  apply (unfold transform_cap_def)
  apply (unfold transform_cap_list_def)
  apply (case_labels "invocation_type label'")
                                              apply (simp_all add: gen_invocation_type_eq)
                (* TCBReadRegisters *)
                apply (clarsimp simp: decode_read_registers_def split: list.split)
                apply (intro conjI impI allI)
                  apply (auto)[2]
                apply (unfold bindE_def)[1]
                apply (rule corres_symb_exec_r[where Q'="\<lambda> rv s. True"])
                   apply (case_tac rv)
                    apply (simp add: lift_def)
                    apply (rule corres_alternate2, simp)
                   apply (simp add: lift_def)
                   apply (simp add: liftE_def lift_def)
                   apply (rule corres_symb_exec_r[where Q'="\<lambda> rv s. True"])
                      apply (fold bindE_def)
                      apply (rule dcorres_whenE_throwError_abstract')
                       apply (rule corres_alternate2)
                       apply simp
                      apply (rule corres_alternate1)
                      apply (clarsimp simp: returnOk_def translate_tcb_invocation_def)
                     apply wp+
                apply (simp add: range_check_def unlessE_def[abs_def])
               (* TCBWriteRegisters *)
               apply (clarsimp simp: decode_write_registers_def split: list.split)
               apply (intro impI conjI allI)
                 (* IRQSetMode *)
                 apply (clarsimp simp: transform_intent_def)
                apply fastforce
               apply clarsimp
               apply (rule dcorres_whenE_throwError_abstract')
                apply (fastforce intro: corres_alternate2 simp: throwError_def)
               apply (simp add: liftE_def bindE_def lift_def)
               apply (rule corres_symb_exec_r[where Q'="\<lambda> rv s. True"])
                  apply (fold bindE_def, rule dcorres_whenE_throwError_abstract')
                   apply (fastforce intro: corres_alternate2 simp: throwError_def)
                  apply (fastforce intro: corres_alternate1
                                    simp: returnOk_def
                                          translate_tcb_invocation_def)
                 apply wp+
              (* TCBCopyRegisters *)
              apply (clarsimp simp: decode_copy_registers_def)
              apply (case_tac args')
               apply (clarsimp simp:whenE_def dcorres_alternative_throw split:option.splits)+
              apply (case_tac "map fst excaps'")
               apply (clarsimp simp: dcorres_alternative_throw split:option.splits)+
              apply (case_tac ab)
                         apply (clarsimp simp:throw_on_none_def get_index_def dcorres_alternative_throw split:option.splits)+
                   apply (rule corres_alternate1)
                   apply (clarsimp simp:returnOk_def corres_underlying_def translate_tcb_invocation_def return_def)
                  apply ((clarsimp simp:throw_on_none_def get_index_def dcorres_alternative_throw split:option.splits)+)[5]
             (* TCBConfigures *)
             apply (clarsimp simp: decode_tcb_configure_def dcorres_alternative_throw whenE_def)
             apply (case_tac "excaps' ! 2")
             apply (case_tac "excaps' ! Suc 0")
             apply (case_tac "excaps' ! 0")
             apply (rule split_return_throw_thingy)
               apply (rule_tac a = a and b = b and c = c in decode_set_ipc_buffer_translate_tcb_invocation)
                apply simp+
              apply (rule split_return_throw_thingy)
                apply (rule decode_set_space_translate_tcb_invocation)
               apply (clarsimp simp: get_index_def throw_on_none_def)
               apply (rule conjI | clarsimp)+
                 apply (rule corres_alternate1,rule dcorres_returnOk)
                 apply (clarsimp simp: translate_tcb_invocation_def update_cnode_cap_data)
                apply clarsimp
               apply (clarsimp | rule conjI)+
                apply (rule corres_alternate1,rule dcorres_returnOk)
                apply (clarsimp simp: translate_tcb_invocation_def update_cnode_cap_data)
               apply clarsimp+
            (* TCBSetPriority *)
            apply (clarsimp simp: decode_set_priority_def throw_on_none_def get_index_def dcorres_alternative_throw whenE_def)
            apply (case_tac "fst (excaps' ! 0)"; simp add: dcorres_alternative_throw)
            apply (rule corres_throw_skip_r)
              apply (rule corres_alternate1)
              apply (rule dcorres_returnOk)
              apply (clarsimp simp: translate_tcb_invocation_def translate_tcb_invocation_thread_ctrl_buffer_def)
             apply (rule check_prio_inv)
            apply fastforce
           (* TCBSetMCPriority *)
           apply (clarsimp simp: decode_set_mcpriority_def throw_on_none_def get_index_def dcorres_alternative_throw whenE_def)
           apply (case_tac "fst (excaps' ! 0)"; simp add: dcorres_alternative_throw)
           apply (rule corres_throw_skip_r)
             apply (rule corres_alternate1)
             apply (rule dcorres_returnOk)
             apply (clarsimp simp: translate_tcb_invocation_def translate_tcb_invocation_thread_ctrl_buffer_def)
            apply (rule check_prio_inv)
           apply fastforce
          (* TCBSetSchedParams *)
          apply (clarsimp simp: decode_set_sched_params_def throw_on_none_def get_index_def dcorres_alternative_throw whenE_def)
          apply (case_tac "fst (excaps' ! 0)"; simp add: dcorres_alternative_throw)
          apply (rule corres_throw_skip_r)+
              apply (rule corres_alternate1)
              apply (rule dcorres_returnOk)
              apply (clarsimp simp: translate_tcb_invocation_def translate_tcb_invocation_thread_ctrl_buffer_def)
             apply (rule check_prio_inv)
            apply fastforce
           apply (rule check_prio_inv)
          apply fastforce

         (* TCBSetIPCBuffer *)
         apply (clarsimp simp:transform_intent_def transform_intent_tcb_set_ipc_buffer_def)
         apply (case_tac args')
          apply clarsimp+
         apply (case_tac "excaps' ! 0")
          apply (clarsimp simp:throw_on_none_def get_index_def dcorres_alternative_throw | rule conjI)+
            apply (rule corres_return_throw_thingy)
              apply (rule decode_set_ipc_buffer_translate_tcb_invocation)
               apply fastforce+
            apply (clarsimp|rule conjI)+
            apply (clarsimp simp:translate_tcb_invocation_def translate_tcb_invocation_thread_ctrl_buffer_def
                           split:option.splits tcb_invocation.splits)
           apply (clarsimp simp:decode_set_ipc_buffer_def dcorres_alternative_throw)+
          apply (rule corres_alternate1[OF dcorres_returnOk])
          apply (clarsimp simp:translate_tcb_invocation_def translate_tcb_invocation_thread_ctrl_buffer_def)
         (* TCBSetSpace *)
         apply (clarsimp simp:throw_on_none_def get_index_def dcorres_alternative_throw | rule conjI)+
           apply (rule corres_return_throw_thingy)
             apply (rule decode_set_space_translate_tcb_invocation)
            apply (clarsimp split del: if_split)+
           apply (clarsimp simp:translate_tcb_invocation_def translate_tcb_invocation_thread_ctrl_buffer_def)
           apply (case_tac "excaps' ! 0",simp,case_tac "excaps' ! Suc 0",simp)
           apply (simp add:update_cnode_cap_data)
          apply (simp add:decode_set_space_def dcorres_alternative_throw | rule conjI)+

       (* TCBSuspend *)
       apply clarsimp
       apply (rule corres_alternate1[OF dcorres_returnOk])
       apply (simp add: translate_tcb_invocation_def)

      (* TCBResume *)
      apply clarsimp
      apply (rule corres_alternate1[OF dcorres_returnOk])
      apply (simp add: translate_tcb_invocation_def)

     (* TCBBindNotification *)
     apply (clarsimp simp: decode_bind_notification_def dcorres_alternative_throw whenE_def)
     apply (rule dcorres_symb_exec_rE)
       apply (case_tac rv, simp)
        (* please continue scrolling *)
        apply (case_tac "(fst (hd excaps'))", simp_all split del: if_split)[1]
                   prefer 4
                   apply (rename_tac rights)
                   apply (case_tac "AllowRead \<notin> rights", simp)
                    apply (rule corres_alternate2, rule dcorres_throw)
                   apply simp
                   apply (rule dcorres_symb_exec_rE)
                     apply (case_tac "ntfn_obj rva", simp_all split del: if_split)[1]
                       apply (case_tac "ntfn_bound_tcb rva", simp_all split del: if_split)[1]
                        apply (clarsimp simp: throw_on_none_def get_index_def dcorres_alternative_throw)
                        apply (case_tac "excaps' ! 0", clarsimp, rule corres_alternate1[OF dcorres_returnOk], simp add: translate_tcb_invocation_def hd_conv_nth)
                       apply (clarsimp simp: throw_on_none_def get_index_def dcorres_alternative_throw split del: if_split)+
                     apply (case_tac "ntfn_bound_tcb rva", simp split del: if_split)[1]
                      apply (rename_tac rva word)
                      apply ((case_tac "excaps' ! 0",clarsimp, rule corres_alternate1[OF dcorres_returnOk], simp add: translate_tcb_invocation_def hd_conv_nth)
                               | clarsimp simp: throw_on_none_def get_index_def dcorres_alternative_throw split del: if_split
                               | wp get_simple_ko_wp
                               | (case_tac "excaps' ! 0", rule dcorres_alternative_throw)
                               | (case_tac "AllowRead \<in> rights", simp))+

    (* TCBUnbindNotification *)
    apply (clarsimp simp: decode_unbind_notification_def dcorres_alternative_throw whenE_def)
    apply (rule dcorres_symb_exec_rE)
      apply (case_tac rv, simp, rule dcorres_alternative_throw)
      apply (clarsimp, rule corres_alternate1[OF dcorres_returnOk], simp add: translate_tcb_invocation_def)
     apply (wp gbn_wp | clarsimp)+

    (* TCBSetTLSBase *)
    apply (clarsimp simp: decode_set_tls_base_def whenE_def)
    apply (rule conjI; clarsimp)
     apply (rule dcorres_alternative_throw)
    apply (rule corres_alternate1[OF dcorres_returnOk])
    apply (simp add: translate_tcb_invocation_def)

  (* ARMASIDPoolAssign *)
  apply (clarsimp simp: transform_intent_def)

  (* ARMIRQIssueIRQHandler *)
  apply (clarsimp simp: transform_intent_def)
  done

(* If the argument to "as_user" is idempotent, then so is the call. *)
lemma dcorres_idempotent_as_user:
  "\<lbrakk> \<And>a. \<lbrace> \<lambda>s. s = a \<rbrace> x \<lbrace> \<lambda>_ s. s = a \<rbrace> \<rbrakk> \<Longrightarrow>
     dcorres dc \<top> (tcb_at u) (return q) (as_user u x)"
  apply (clarsimp simp: as_user_def)
  apply (clarsimp simp: corres_underlying_def bind_def split_def set_object_def get_object_def
                        return_def get_def put_def get_tcb_def gets_the_def gets_def assert_opt_def
                        tcb_at_def select_f_def valid_def
         split: option.split Structures_A.kernel_object.split)
  done

lemma transform_full_intent_kheap_update_eq:
  "q \<noteq> u' \<Longrightarrow>
   transform_full_intent (machine_state (s\<lparr>kheap := (kheap s)(u' \<mapsto> x')\<rparr>)) q =
   transform_full_intent (machine_state s) q"
  by simp

(* Suspend functions correspond. *)
lemma suspend_corres:
  "dcorres dc \<top> (tcb_at obj_id and not_idle_thread obj_id and invs and valid_etcbs)
     (Tcb_D.suspend obj_id) (IpcCancel_A.suspend obj_id)"
  apply (rule corres_guard_imp)
    apply (clarsimp simp: IpcCancel_A.suspend_def Tcb_D.suspend_def)
    apply (rule corres_split[OF finalise_cancel_ipc])
      apply (rule dcorres_symb_exec_r[OF _ gts_inv gts_inv])
      apply (rule dcorres_rhs_noop_above)
         apply (case_tac "rv = Running"; simp)
          apply (rule update_restart_pc_dcorres)
         apply simp
        apply (rule dcorres_rhs_noop_below_True[OF tcb_sched_action_dcorres])
        apply (rule set_thread_state_corres)
       apply wp
      apply (case_tac "rv = Running"; simp)
       apply wp+
       apply (wpsimp simp: not_idle_thread_def conj_comms)+
done

lemma dcorres_setup_reply_master:
  "dcorres dc \<top> (valid_objs and tcb_at obj_id and not_idle_thread obj_id and valid_idle and valid_etcbs)
             (KHeap_D.set_cap (obj_id, tcb_replycap_slot)
               (cdl_cap.MasterReplyCap obj_id))
             (setup_reply_master obj_id)"
  apply (clarsimp simp:setup_reply_master_def)
  apply (rule_tac Q'="\<lambda>rv. valid_objs and tcb_at obj_id and not_idle_thread obj_id and valid_idle and valid_etcbs and
     cte_wp_at (\<lambda>c. c = rv) (obj_id,tcb_cnode_index 2)" in corres_symb_exec_r)
     prefer 2
     apply (wp get_cap_cte_wp_at)
    apply (rule dcorres_expand_pfx)
    apply (clarsimp simp:tcb_at_def)
    apply (frule valid_tcb_objs)
     apply (simp add:tcb_at_def)
    apply (clarsimp simp:cte_wp_at_cases dest!:get_tcb_SomeD)
    apply (clarsimp simp:valid_tcb_def)
    apply (clarsimp simp:tcb_cap_cases_def)
    apply (case_tac "cap.NullCap = tcb_reply tcb")
     apply (clarsimp simp:when_def)
     apply (rule corres_guard_imp)
       apply (rule dcorres_symb_exec_r)
         apply (rule set_cap_corres)
          apply (clarsimp simp:transform_cap_def)
         apply (clarsimp simp:transform_tcb_slot_simp)
        apply (wp+)[2]
       apply (clarsimp simp:transform_def transform_current_thread_def)
      apply (rule TrueI)
     apply (clarsimp simp: not_idle_thread_def)
    apply (clarsimp simp:when_def is_master_reply_cap_def split:cap.split_asm)
    apply (rename_tac rc_rights)
    apply (subgoal_tac "opt_cap (obj_id,tcb_replycap_slot) (transform s')
      = Some (cdl_cap.MasterReplyCap obj_id)")
     apply (clarsimp simp:corres_underlying_def set_cap_is_noop_opt_cap return_def)
    apply (subgoal_tac "cte_wp_at ((=)  (cap.ReplyCap obj_id True rc_rights))
      (obj_id,tcb_cnode_index 2) s'")
     apply (clarsimp dest!:iffD1[OF cte_wp_at_caps_of_state])
     apply (drule caps_of_state_transform_opt_cap)
       apply simp
      apply (clarsimp simp:not_idle_thread_def)
     apply (simp add:transform_cap_def transform_tcb_slot_simp)
    apply (clarsimp simp:cte_wp_at_cases)
   apply wp
  apply simp
  done

lemma set_cdl_cap_noop:
  " dcorres dc \<top> (cte_wp_at (\<lambda>cap. cdlcap = transform_cap cap) slot and not_idle_thread (fst slot) and valid_etcbs)
             (KHeap_D.set_cap (transform_cslot_ptr slot) cdlcap)
             (return x)"
  apply (rule dcorres_expand_pfx)
  apply clarsimp
  apply (drule iffD1[OF cte_wp_at_caps_of_state])
  apply clarsimp
  apply (drule caps_of_state_transform_opt_cap)
   apply simp
    apply (simp add:not_idle_thread_def)
  apply (drule set_cap_is_noop_opt_cap)
  apply (clarsimp simp:corres_underlying_def return_def not_idle_thread_def set_cap_is_noop_opt_cap)
done


lemma runnable_imply:
  "runnable st
   \<Longrightarrow> (infer_tcb_pending_op obj_id st = RunningCap \<or>
    infer_tcb_pending_op obj_id st = RestartCap)"
  apply (case_tac st)
   apply (simp_all add:infer_tcb_pending_op_def)
  done

lemma dcorres_set_thread_state_Restart2:
  "dcorres dc (\<lambda>_. True)
   (\<lambda>a. valid_mdb a \<and> not_idle_thread recver a \<and> st_tcb_at idle (idle_thread a) a \<and> valid_etcbs a)
   (KHeap_D.set_cap (recver, tcb_pending_op_slot) RestartCap)
   (set_thread_state recver Structures_A.thread_state.Restart)"
  apply (simp add:KHeap_D.set_cap_def set_thread_state_def)
  apply (rule dcorres_gets_the)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
  apply (frule opt_object_tcb, simp)
    apply (clarsimp simp:not_idle_thread_def)
   apply (clarsimp simp:transform_tcb_def has_slots_def update_slots_def object_slots_def tcb_slots)
   apply (rule dcorres_rhs_noop_below_True[OF set_thread_state_ext_dcorres])
   apply (rule dcorres_set_object_tcb)
     apply (clarsimp simp:transform_tcb_def infer_tcb_pending_op_def tcb_slots)
apply (rule conjI, fastforce)
   apply (clarsimp simp:get_etcb_SomeD)
    apply (simp add:not_idle_thread_def)
   apply (clarsimp simp:get_tcb_SomeD)
  apply (clarsimp simp:get_etcb_SomeD)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (fastforce simp:not_idle_thread_def dest!:opt_object_tcb)
  done

(* Restart functions correspond. *)
lemma restart_corres:
  "dcorres dc \<top>
  (invs and tcb_at obj_id and not_idle_thread obj_id and valid_etcbs)
  (Tcb_D.restart obj_id) (Tcb_A.restart obj_id)"
  apply (clarsimp simp: Tcb_D.restart_def Tcb_A.restart_def
    when_def get_cap_def)
  apply (clarsimp simp: thread_get_def get_thread_state_def )
  apply (rule dcorres_gets_the)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (clarsimp simp:opt_cap_tcb not_idle_thread_def tcb_vspace_slot_def
    tcb_pending_op_slot_def tcb_caller_slot_def tcb_ipcbuffer_slot_def
    tcb_cspace_slot_def tcb_replycap_slot_def)
  apply (intro conjI impI)
       apply (rule corres_guard_imp)
         apply (rule corres_split[OF finalise_cancel_ipc])
           apply (rule corres_split[OF dcorres_setup_reply_master[unfolded tcb_replycap_slot_def] ])
            apply (rule dcorres_rhs_noop_below_True[OF dcorres_rhs_noop_below_True])
             apply (rule possible_switch_to_dcorres)
             apply (rule tcb_sched_action_dcorres)
             apply (rule dcorres_set_thread_state_Restart2[unfolded tcb_pending_op_slot_def])
            apply wp
           apply (simp add:not_idle_thread_def)
           apply ((wp|wps)+)[2]
         apply (rule_tac Q="(=) s' and invs" in  hoare_vcg_precond_imp)
          apply (rule hoare_strengthen_post
             [where Q="\<lambda>r. invs and tcb_at obj_id and not_idle_thread obj_id and valid_etcbs"])
           apply (simp add:not_idle_thread_def)
           apply (wp)
             apply (clarsimp simp:invs_def valid_state_def valid_pspace_def
                tcb_at_def not_idle_thread_def)+
         apply (clarsimp simp:valid_idle_def pred_tcb_at_def obj_at_def)
        apply assumption
       apply (clarsimp simp:not_idle_thread_def)+
      apply (clarsimp dest!:runnable_imply[where obj_id = obj_id])+
     apply (clarsimp simp:invs_def valid_state_def)
     apply (drule only_idleD[rotated])
      apply (fastforce simp:st_tcb_at_def obj_at_def dest!:get_tcb_SomeD)
     apply simp
    apply (clarsimp simp: runnable_def infer_tcb_pending_op_def
      split:Structures_A.thread_state.split_asm)+
    apply (frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (fastforce simp:opt_cap_tcb not_idle_thread_def)
  done

crunches get_thread, getRegister
  for inv [wp]: P
  (ignore_del: getRegister)

(* Read the registers of another thread. *)
lemma invoke_tcb_corres_read_regs:
  "\<lbrakk> t' = tcb_invocation.ReadRegisters obj_id resume data flags;
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (invs and tcb_at obj_id and not_idle_thread obj_id and valid_etcbs)
  (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (clarsimp simp: Tcb_D.invoke_tcb_def translate_tcb_invocation_def)
  apply (case_tac "resume")
   apply (rule corres_alternate1)
   apply clarsimp
   apply (subst bind_return [symmetric])
   apply (rule corres_guard_imp)
     apply (rule corres_split[where r'=dc])
        apply (rule suspend_corres, simp)
       apply (rule corres_symb_exec_r)
          apply (rule dcorres_idempotent_as_user)
          apply (rule hoare_mapM_idempotent)
          apply wpsimp+
  apply (rule corres_alternate2)
  apply (rule corres_symb_exec_r)
     apply (rule dcorres_idempotent_as_user)
     apply (rule hoare_mapM_idempotent)
     apply (wp | simp)+
  done

(* Write the registers of another thread. *)
lemma invoke_tcb_corres_write_regs:
  "\<lbrakk> t' = tcb_invocation.WriteRegisters obj_id resume data flags;
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (invs and not_idle_thread obj_id and tcb_at obj_id and valid_etcbs) (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (clarsimp simp: Tcb_D.invoke_tcb_def translate_tcb_invocation_def arch_get_sanitise_register_info_def
                        arch_post_modify_registers_def)
  apply (rule corres_symb_exec_r)
     apply (rule corres_guard_imp)
       apply (rule corres_split[where r'=dc])
          apply (rule corrupt_tcb_intent_as_user_corres)
         apply (rule corres_dummy_return_l)
         apply (rule corres_split[where r'=dc])
            apply (clarsimp simp: when_def)
            apply (clarsimp simp: dc_def, rule restart_corres [unfolded dc_def])
           apply (rule corres_split_noop_rhs[OF corres_trivial])
             apply (clarsimp simp: when_def)
             apply (rule reschedule_required_dcorres[THEN corres_trivial])
            apply simp
           apply wp
          apply (clarsimp simp: when_def)
          apply (wpsimp wp: when_wp)+
     apply (wp wp_post_taut | simp add:invs_def valid_state_def | fastforce)+
  done

lemma corres_mapM_x_rhs_induct:
  "\<lbrakk> corres_underlying sr nf nf' dc P P' g (return ());
     \<And>a. corres_underlying sr nf nf' dc P P' g (g' a);
     g = do g; g od;
     \<lbrace> P \<rbrace> g \<lbrace> \<lambda>_. P \<rbrace>;
     \<And>a. \<lbrace> P' \<rbrace> g' a \<lbrace> \<lambda>_. P'\<rbrace> \<rbrakk> \<Longrightarrow>
  corres_underlying sr nf nf' dc P P' g (mapM_x g' l)"
  apply (induct_tac l)
   apply (clarsimp simp: mapM_x_def sequence_x_def dc_def)
  apply (clarsimp simp: mapM_x_def sequence_x_def dc_def)
  apply (erule ssubst)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply assumption
      apply assumption
     apply assumption
    apply assumption
   apply simp
  apply simp
  done

(*
 * Copy registers loop.
 *
 * What we show here is that any number of individual register
 * copys from A to B merely results in a corruption of B's
 * registers.
 *)
lemma invoke_tcb_corres_copy_regs_loop:
  "dcorres dc \<top>
     (tcb_at target_id and tcb_at obj_id' and valid_idle and not_idle_thread target_id and not_idle_thread obj_id' and valid_etcbs)
     (corrupt_tcb_intent target_id)
     (mapM_x
        (\<lambda>r. do v \<leftarrow> as_user obj_id' (getRegister r);
                     as_user target_id (setRegister r v)
             od) x)"
   apply (clarsimp simp: mapM_x_mapM)
   apply (rule corres_guard_imp)
   apply (rule corres_dummy_return_l)
     apply (rule corres_split[OF Intent_DR.set_registers_corres corres_free_return[where P=\<top> and P'= \<top>]])
     apply (wp|simp)+
  done

crunch idle_thread_constant[wp]:
  "Tcb_A.restart", "IpcCancel_A.suspend" "\<lambda>s::'z::state_ext state. P (idle_thread s)"
  (wp: dxo_wp_weak)

lemma not_idle_after_restart [wp]:
  "\<lbrace>invs and not_idle_thread obj_id' :: det_state \<Rightarrow> bool\<rbrace> Tcb_A.restart obj_id'
           \<lbrace>\<lambda>rv. valid_idle \<rbrace>"
  including no_pre
  supply if_cong[cong]
  apply (simp add:Tcb_A.restart_def)
  apply wp
   apply (simp add:cancel_ipc_def)
   apply (wp not_idle_after_blocked_cancel_ipc not_idle_after_reply_cancel_ipc
             not_idle_thread_cancel_signal | wpc)+
   apply (rule hoare_strengthen_post[where Q="\<lambda>r. st_tcb_at ((=) r) obj_id'
                                                  and not_idle_thread obj_id' and invs"])
    apply (wp gts_sp)
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def not_idle_thread_def | rule conjI)+
  apply (rule hoare_strengthen_post, rule gts_inv)
  apply (clarsimp)
  done

lemma not_idle_after_suspend [wp]:
  "\<lbrace>invs and not_idle_thread obj_id' and tcb_at obj_id'\<rbrace> IpcCancel_A.suspend obj_id'
           \<lbrace>\<lambda>rv. valid_idle \<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule hoare_vcg_precond_imp)
    apply (rule suspend_invs)
   apply (simp add:not_idle_thread_def invs_def valid_state_def)+
  done

crunch valid_etcbs[wp]: "Tcb_A.restart"  "valid_etcbs"

(* Copy registers from one thread to another. *)
lemma invoke_tcb_corres_copy_regs:
  "\<lbrakk> t' = tcb_invocation.CopyRegisters obj_id' target_id' a b c d e;
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top>
   (invs and tcb_at obj_id' and tcb_at target_id' and Tcb_AI.tcb_inv_wf t' and not_idle_thread target_id' and not_idle_thread obj_id' and valid_etcbs)
     (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (clarsimp simp: Tcb_D.invoke_tcb_def translate_tcb_invocation_def arch_post_modify_registers_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'=dc])
       apply (rule corres_cases [where R="a"])
        apply (clarsimp simp: when_def)
        apply (rule corres_alternate1)
        apply (rule suspend_corres)
       apply (clarsimp simp: when_def dc_def[symmetric])+
       apply (rule corres_alternate2)
       apply (rule corres_free_return [where P="\<top>" and P'="\<top>"])
      apply (rule corres_split[where r'=dc])
         apply (rule corres_cases [where R="b"])
          apply (clarsimp simp: when_def)
          apply (rule corres_alternate1)
          apply (rule restart_corres, simp)
         apply (rule corres_alternate2)
         apply (rule corres_free_return [where P="\<top>" and P'="\<top>"])
        apply (rule corres_corrupt_tcb_intent_dupl)
        apply (rule corres_split[where r'=dc])
           apply (rule corres_cases [where R="c"])
            apply (clarsimp simp: when_def)
            apply (rule corres_bind_ignore_ret_rhs)
            apply (rule corres_corrupt_tcb_intent_dupl)
            apply (rule corres_split[where r'=dc])
               apply (rule invoke_tcb_corres_copy_regs_loop, simp)
              apply (rule corres_symb_exec_r)
                 apply (simp add:setNextPC_def)
                 apply (rule Intent_DR.set_register_corres[unfolded dc_def], simp)
                apply (wp | clarsimp simp:getRestartPC_def)+
            apply (wp mapM_x_wp [where S=UNIV])
            apply simp
           apply simp
           apply (rule dummy_corrupt_tcb_intent_corres)
          apply (rule corres_dummy_return_l)
          apply (rule corres_split[where r'=dc])
             apply (rule corres_cases [where R="d"])
              apply (clarsimp simp: when_def)
              apply (rule invoke_tcb_corres_copy_regs_loop)
             apply (clarsimp simp: when_def)
             apply (rule dummy_corrupt_tcb_intent_corres)
            apply (rule corres_symb_exec_r)
               apply (rule corres_split_noop_rhs[OF corres_trivial])
                 apply simp
                 apply (clarsimp simp: when_def)
                 apply (rule reschedule_required_dcorres[THEN corres_trivial])
                apply wpsimp+
        apply (wp mapM_x_wp [where S=UNIV])[1]
        apply simp
       apply (wp wp_post_taut)
      apply (clarsimp simp:conj_comms pred_conj_def cong: if_cong)
      apply (wpsimp simp: not_idle_thread_def | rule conjI | strengthen invs_cur)+
  done

lemma cnode_cap_unique_bits:
  "is_cnode_cap cap \<Longrightarrow>
  \<lbrace>\<lambda>s. (\<forall>a b. \<not> cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap \<and> table_cap_ref c \<noteq> table_cap_ref cap) (a, b) s)
        \<and> valid_cap cap s \<and> valid_objs s\<rbrace>
    CSpaceAcc_A.get_cap (ba, c)
  \<lbrace>\<lambda>rv s. (Structures_A.is_cnode_cap rv \<and> obj_refs rv = obj_refs cap) \<longrightarrow> (bits_of rv = bits_of cap)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule_tac Q="\<lambda>r s. (\<forall>a b. \<not> cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap \<and>
                                                    table_cap_ref c \<noteq> table_cap_ref cap) (a, b) s)
                            \<and> valid_cap cap s \<and> valid_objs s
                            \<and> valid_objs s \<and> cte_wp_at (\<lambda>x. x = r) (ba,c) s"
    in hoare_strengthen_post)
    apply (wp get_cap_cte_wp_at)
   apply (clarsimp simp:is_cap_simps)
   apply (drule_tac x = ba in spec)
   apply (drule_tac x = c in spec)
   apply (drule(1) cte_wp_at_valid_objs_valid_cap)
   apply (clarsimp simp:valid_cap_def obj_at_def is_ep_def is_ntfn_def is_cap_table_def,
          clarsimp split:Structures_A.kernel_object.split_asm)+
   apply (clarsimp simp:well_formed_cnode_n_def bits_of_def)
  apply simp
  done

lemma get_cap_ex_cte_cap_wp_to:
  "(tcb_cnode_index x)\<in> dom tcb_cap_cases  \<Longrightarrow> \<lbrace>\<top>\<rbrace> CSpaceAcc_A.get_cap a'
            \<lbrace>\<lambda>rv s. is_thread_cap rv \<and> obj_ref_of rv = obj_id' \<longrightarrow> ex_cte_cap_wp_to (\<lambda>_. True) (obj_id', tcb_cnode_index x) s\<rbrace>"
  apply (rule hoare_strengthen_post[OF get_cap_cte_wp_at])
  apply (case_tac a')
  apply (clarsimp simp:ex_cte_cap_wp_to_def)
  apply (rule exI)+
  apply (rule cte_wp_at_weakenE)
   apply simp
  apply (clarsimp simp:is_cap_simps)
  done

crunch idle[wp] : cap_delete "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps ignore: wrap_ext_bool OR_choiceE)

lemma imp_strengthen:
  "R \<and> (P x \<longrightarrow> Q x) \<Longrightarrow> P x \<longrightarrow> (Q x \<and> R) "
 by simp

lemma dcorres_corrupt_tcb_intent_ipcbuffer_upd:
  "dcorres dc \<top> (tcb_at y and valid_idle and not_idle_thread y and valid_etcbs)
    (corrupt_tcb_intent  y)
    (thread_set (tcb_ipc_buffer_update (\<lambda>_. a)) y)"
  apply (clarsimp simp:corrupt_tcb_intent_def thread_set_def get_thread_def bind_assoc)
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:update_thread_def tcb_at_def)
  apply (rule select_pick_corres[where S = UNIV,simplified])
  apply (frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (rule dcorres_gets_the)
   apply (clarsimp simp:opt_object_tcb not_idle_thread_def)
   apply (simp add:transform_tcb_def)
   apply (rule corres_guard_imp)
     apply (rule_tac s' = s'a in dcorres_set_object_tcb)
        apply (clarsimp simp:transform_tcb_def)
        apply (simp add: get_etcb_def)
       apply (clarsimp dest!: get_tcb_SomeD get_etcb_SomeD split:option.splits)+
  apply (clarsimp simp: opt_object_tcb not_idle_thread_def dest!:get_tcb_rev get_etcb_rev)
  done

lemma arch_same_obj_as_lift:
  "\<lbrakk>cap_aligned a;is_arch_cap a;ca = transform_cap a;cb=transform_cap b\<rbrakk>
  \<Longrightarrow> cdl_same_arch_obj_as (ca) (cb) = same_object_as a b"
  apply (clarsimp simp:is_arch_cap_def split:cap.split_asm)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap)
      apply (simp add:same_object_as_def)
      apply (clarsimp split:cap.splits simp:cdl_same_arch_obj_as_def)
      apply (rename_tac arch_cap)
      apply (case_tac arch_cap)
          apply (clarsimp simp:cdl_same_arch_obj_as_def)+
     apply (simp add:same_object_as_def)
     apply (clarsimp split:cap.splits simp:cdl_same_arch_obj_as_def)
     apply (rename_tac arch_cap)
     apply (case_tac arch_cap)
         apply ((clarsimp simp:cdl_same_arch_obj_as_def)+)[5]
    apply (simp add:same_object_as_def)
    apply (clarsimp split:cap.splits simp:cdl_same_arch_obj_as_def)
    apply (rename_tac arch_cap)
    apply (case_tac arch_cap)
        apply (fastforce simp:cdl_same_arch_obj_as_def cap_aligned_def)+
   apply (simp add:same_object_as_def)
   apply (clarsimp split:cap.splits simp:cdl_same_arch_obj_as_def)
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap)
       apply (fastforce simp:cdl_same_arch_obj_as_def cap_aligned_def)+
  apply (simp add:same_object_as_def)
  apply (clarsimp split:cap.splits simp:cdl_same_arch_obj_as_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap)
      apply (fastforce simp:cdl_same_arch_obj_as_def cap_aligned_def)+
  done

lemma thread_set_valid_irq_node:
  "(\<And>t getF v. (getF, v) \<in> ran tcb_cap_cases \<Longrightarrow> getF (f t) = getF t)
   \<Longrightarrow>
   \<lbrace>valid_irq_node\<rbrace> thread_set f p
   \<lbrace>\<lambda>rv s. valid_irq_node s\<rbrace>"
  apply (simp add: valid_irq_node_def thread_set_def)
  apply wp
   apply (simp add: KHeap_A.set_object_def get_object_def)
   apply wp+
  apply (clarsimp simp: obj_at_def is_cap_table_def dest!: get_tcb_SomeD)
  apply (drule_tac x = irq in spec)
  apply clarsimp
  done

lemma update_ipc_buffer_valid_objs:
  "\<lbrace>valid_objs and K(is_aligned a msg_align_bits)\<rbrace>
  thread_set (tcb_ipc_buffer_update (\<lambda>_. a)) ptr
  \<lbrace>\<lambda>rv s. valid_objs s \<rbrace>"
  apply (wp thread_set_valid_objs'')
  apply (clarsimp simp:valid_tcb_def)
  apply (intro conjI allI)
   apply (clarsimp simp:tcb_cap_cases_def)
  apply (auto simp: valid_ipc_buffer_cap_def split: cap.splits arch_cap.splits bool.splits)
  done

lemma dcorres_tcb_empty_slot:
  "(thread,idx) = (transform_cslot_ptr slot)
  \<Longrightarrow> dcorres (dc \<oplus> dc) (\<lambda>_. True)
  (cte_wp_at (\<lambda>_. True) slot and invs and emptyable slot and not_idle_thread (fst slot) and valid_pdpt_objs and valid_etcbs)
  (tcb_empty_thread_slot thread idx) (cap_delete slot)"
  apply (simp add:liftE_bindE tcb_empty_thread_slot_def)
  apply (simp add:opt_cap_def gets_the_def assert_opt_def gets_def bind_assoc split_def)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp add:cte_at_into_opt_cap)
  apply (erule impE)
   apply (clarsimp simp: not_idle_thread_def dest!:invs_valid_idle)
  apply (simp add:opt_cap_def whenE_def split_def)
  apply (intro conjI impI)
   apply (case_tac slot,clarsimp)
   apply (rule corres_guard_imp)
     apply (rule delete_cap_corres')
    apply simp
   apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (simp add:cap_delete_def)
  apply (subst rec_del_simps_ext)
  apply (subst rec_del_simps_ext)
  apply (clarsimp simp:bindE_assoc)
  apply (subst liftE_bindE)
  apply (rule corres_guard_imp[OF corres_symb_exec_r])
       apply (rule_tac F = "x = cap.NullCap" in corres_gen_asm2)
       apply (simp add:bindE_assoc when_def)
       apply (simp add:IpcCancel_A.empty_slot_def returnOk_liftE)
       apply (rule corres_symb_exec_r)
          apply (rule_tac F = "cap = cap.NullCap" in corres_gen_asm2)
          apply (rule corres_trivial)
          apply simp
         apply (simp | wp get_cap_wp)+
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  done

lemma dcorres_idempotent_as_user_strong:
  assumes prem: "\<And>tcb ms ref etcb P.
                 \<lbrace> \<lambda>cxt. P (transform_tcb ms ref (tcb\<lparr>tcb_arch:=arch_tcb_context_set cxt (tcb_arch tcb)\<rparr>) etcb)\<rbrace>
                 x
                 \<lbrace> \<lambda>_ cxt. P (transform_tcb ms ref (tcb\<lparr>tcb_arch:=arch_tcb_context_set cxt (tcb_arch tcb)\<rparr>) etcb)\<rbrace>"
  shows "dcorres dc \<top> (tcb_at u) (return q) (as_user u x)"
  supply option.case_cong[cong] if_cong[cong]
  apply (clarsimp simp: as_user_def)
  apply (clarsimp simp: corres_underlying_def bind_def split_def set_object_def get_object_def
                        return_def get_def put_def get_tcb_def gets_the_def gets_def assert_opt_def
                        tcb_at_def select_f_def valid_def
                 split: option.split Structures_A.kernel_object.split)
  apply (clarsimp simp: transform_def transform_current_thread_def transform_objects_def restrict_map_def)
  apply (rule ext)
   apply (clarsimp simp: map_add_def split:option.splits)
  apply (drule use_valid[OF _ prem])
   prefer 2
   apply force
  apply simp
  done

lemma TPIDRURW_notin_msg_registers[simp]:
 "TPIDRURW \<notin> set msg_registers"
  apply (auto simp: msgRegisters_def frameRegisters_def gpRegisters_def
                    syscallMessage_def exceptionMessage_def msg_registers_def)
  apply (rule ccontr)
  apply clarsimp
  apply (simp_all add: upto_enum_red image_def)
  apply (auto simp add: toEnum_eq_to_fromEnum_eq fromEnum_def enum_register maxBound_def
              dest!: toEnum_eq_to_fromEnum_eq[THEN iffD1,rotated,OF sym])
  done

lemma transform_full_intent_update_tpidrurw[simp]:
  "transform_full_intent ms ref (tcb\<lparr>tcb_arch := arch_tcb_set_registers (s(TPIDRURW := a)) (tcb_arch tcb)\<rparr>)
   = transform_full_intent ms ref (tcb\<lparr>tcb_arch := arch_tcb_set_registers s (tcb_arch tcb)\<rparr>)"
   apply (clarsimp simp: transform_full_intent_def cap_register_def ARM.capRegister_def
                         arch_tcb_set_registers_def arch_tcb_context_get_def Let_def)
   by (fastforce simp: get_tcb_message_info_def msg_info_register_def ARM.msgInfoRegister_def
                       get_tcb_mrs_def get_ipc_buffer_words_def Suc_le_eq Let_def
                       arch_tcb_context_get_def)

lemma as_user_valid_irq_node[wp]:
  "\<lbrace>valid_irq_node\<rbrace>
    as_user y (set_register a v)
  \<lbrace>\<lambda>rv. valid_irq_node\<rbrace>"
  apply (simp add: valid_irq_node_def cap_table_at_typ)
  apply (rule hoare_pre)
  apply (wp hoare_vcg_all_lift | wps )+
  apply auto
  done

lemma set_register_TPIDRURW_tcb_abstract_inv[wp]:
  "\<lbrace>\<lambda>cxt. P (transform_tcb ms ref (tcb\<lparr>tcb_arch := arch_tcb_context_set cxt (tcb_arch tcb)\<rparr>) etcb)\<rbrace>
     setRegister TPIDRURW a
   \<lbrace>\<lambda>_ cxt. P (transform_tcb ms ref (tcb\<lparr>tcb_arch := arch_tcb_context_set cxt (tcb_arch tcb)\<rparr>) etcb)\<rbrace>"
  supply transform_full_intent_update_tpidrurw[simplified arch_tcb_set_registers_def, simp]
  apply (simp add: setRegister_def simpler_modify_def valid_def arch_tcb_context_set_def
                   transform_tcb_def)
  done

lemma dcorres_tcb_update_ipc_buffer:
  "dcorres (dc \<oplus> dc) (\<top>) (invs and valid_etcbs and tcb_at obj_id' and not_idle_thread obj_id'
         and valid_pdpt_objs
     and
     (\<lambda>y. case ipc_buffer' of None \<Rightarrow> True
       | Some v \<Rightarrow> case_option True ((swp valid_ipc_buffer_cap (fst v) and is_arch_cap and cap_aligned) \<circ> fst) (snd v)
       \<and> (is_aligned (fst v) msg_align_bits) ) and
    case_option (\<lambda>_. True) (case_option (\<lambda>_. True) (cte_wp_at (\<lambda>_. True) \<circ> snd) \<circ> snd) ipc_buffer'
    and case_option (\<lambda>_. True) (case_option (\<lambda>_. True) (not_idle_thread \<circ> fst \<circ> snd) \<circ> snd) ipc_buffer' and
    (\<lambda>s. case_option True (\<lambda>x. not_idle_thread (fst a') s) ipc_buffer') )
     (case_option
         (returnOk () \<sqinter>
           (doE tcb_empty_thread_slot obj_id' tcb_ipcbuffer_slot;
                liftE $ corrupt_tcb_intent obj_id'
            odE))
           (tcb_update_ipc_buffer obj_id' (transform_cslot_ptr a'))
         (translate_tcb_invocation_thread_ctrl_buffer ipc_buffer'))
     (doE y \<leftarrow> case_option (returnOk ())
                       (case_prod
                         (\<lambda>ptr frame.
                             doE cap_delete (obj_id', tcb_cnode_index 4);
                                 liftE $ thread_set (tcb_ipc_buffer_update (\<lambda>_. ptr)) obj_id';
                                 liftE $
                                 case_option (return ())
                                  (case_prod
                                    (\<lambda>new_cap src_slot.
                                        check_cap_at new_cap src_slot $
                                        check_cap_at (cap.ThreadCap obj_id') a' $ cap_insert new_cap src_slot (obj_id', tcb_cnode_index 4)))
                                  frame;
                              cur \<leftarrow> liftE $ gets cur_thread;
                              liftE $ when (obj_id' = cur) (do_extended_op reschedule_required)
                             odE))
                       ipc_buffer';
                  returnOk []
              odE)"
  apply (case_tac ipc_buffer')
   apply (simp_all add:translate_tcb_invocation_thread_ctrl_buffer_def)
   apply (rule corres_alternate1)
   apply (rule corres_guard_imp[OF dcorres_returnOk],clarsimp+)
  apply (clarsimp simp:bindE_assoc split:option.splits,intro conjI)
   apply (clarsimp)
   apply (rule corres_alternate2)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        apply (rule dcorres_tcb_empty_slot)
        apply (simp add:transform_tcb_slot_4)
       apply (clarsimp simp:liftE_bindE)
       apply (simp add:liftE_def)
       apply (rule corres_split[OF dcorres_corrupt_tcb_intent_ipcbuffer_upd])
         apply (rule corres_dummy_return_pl)
         apply (clarsimp simp:returnOk_def)
         apply (rule corres_symb_exec_r)
            apply (rule corres_guard_imp)
              apply (rule corres_split_noop_rhs)
                apply (clarsimp simp: when_def)
                apply (rule reschedule_required_dcorres[THEN corres_trivial])
               apply (rule corres_trivial)
               apply simp
              apply wpsimp+
     apply (rule validE_validE_R)
     apply (rule_tac Q = "\<lambda>r s. invs s \<and> valid_etcbs s \<and> not_idle_thread obj_id' s  \<and> tcb_at obj_id' s"
        in hoare_post_impErr[where E="\<lambda>x. \<top>"])
       apply (simp add:not_idle_thread_def)
       apply (wp cap_delete_cte_at cap_delete_deletes)
      apply (clarsimp simp:invs_def valid_state_def not_idle_thread_def)
     apply (clarsimp simp :emptyable_def not_idle_thread_def)+
   apply (erule tcb_at_cte_at)
   apply (simp add:tcb_cap_cases_def)
  (* Main Part *)
  apply (clarsimp simp:tcb_update_ipc_buffer_def tcb_update_thread_slot_def  transform_tcb_slot_simp[symmetric])
  apply (drule_tac s="transform_cslot_ptr a" for a in sym)
  apply (clarsimp simp:check_cap_at_def)
  apply (rule dcorres_expand_pfx)
  apply (subst alternative_com)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule dcorres_tcb_empty_slot)
       apply (simp add:transform_tcb_slot_4)
      apply (clarsimp simp:tcb_update_thread_slot_def whenE_liftE)
      apply (clarsimp simp:liftE_bindE)
      apply (rule corres_split[OF dcorres_corrupt_tcb_intent_ipcbuffer_upd])
        apply (clarsimp simp:bind_assoc)
        apply (rule corres_dummy_return_pl)
        apply simp
        apply (rule corres_split)
           apply (rule get_cap_corres; simp)
          apply (clarsimp simp:liftE_def returnOk_def)
          apply (rule corres_split)
             apply (rule corres_when)
              apply (rule arch_same_obj_as_lift)
                 apply (simp add:valid_ipc_buffer_cap_def is_arch_cap_def split:cap.splits)
                apply (clarsimp simp: valid_cap_def is_arch_cap_def valid_ipc_buffer_cap_def
                            split: cap.split_asm arch_cap.split_asm)+
             apply (rule corres_split)
                apply (rule get_cap_corres; simp)
               apply (rule corres_when)
                apply (rule sym)
                apply (case_tac cap')
                           apply (clarsimp simp:same_object_as_def)+
                apply (simp add:transform_cap_def split:arch_cap.splits)
               apply (rule dcorres_insert_cap_combine)
               apply clarsimp
              apply wp
             apply (rule_tac Q = "\<lambda>r s. cte_wp_at ((=) cap.NullCap) (obj_id', tcb_cnode_index 4) s
                                        \<and> cte_wp_at (\<lambda>_. True) (ab, ba) s
                                        \<and> valid_global_refs s \<and> valid_idle s \<and> valid_irq_node s
                                        \<and> valid_mdb s \<and> valid_objs s\<and> not_idle_thread ab s \<and> valid_etcbs s
                                        \<and> ((is_thread_cap r \<and> obj_ref_of r = obj_id') \<longrightarrow>
                                            ex_cte_cap_wp_to (\<lambda>_. True) (obj_id', tcb_cnode_index 4) s)"
                    in hoare_strengthen_post)
              apply (wp get_cap_ex_cte_cap_wp_to,clarsimp)
             apply (clarsimp simp:same_object_as_def)
             apply (drule ex_cte_cap_to_not_idle, auto simp: not_idle_thread_def)[1]
            apply (rule corres_trivial,clarsimp simp:returnOk_def)
            apply (rule corres_symb_exec_r)
               apply (rule corres_guard_imp)
                 apply (rule corres_split_noop_rhs)
                   apply (clarsimp simp: when_def)
                   apply (rule reschedule_required_dcorres[THEN corres_trivial])
                  apply (rule corres_trivial)
                  apply simp
                 apply wp
                apply simp
               apply simp
              apply wp
             apply wp
            apply wpsimp
           apply (wp when_wp)+
        apply (wpsimp wp: wp_post_taut hoare_drop_imp get_cap_weak_wp simp_del: hoare_TrueI)+
      apply (clarsimp simp:conj_comms)
      apply (wp thread_set_global_refs_triv thread_set_valid_idle)
       apply (clarsimp simp:tcb_cap_cases_def)
      apply (wp thread_set_valid_idle thread_set_valid_irq_node)
       apply (fastforce simp:tcb_cap_cases_def)
      apply (wp thread_set_mdb)
       apply (fastforce simp:tcb_cap_cases_def)
      apply (simp add:not_idle_thread_def)
      apply (wp thread_set_cte_at update_ipc_buffer_valid_objs thread_set_valid_cap thread_set_cte_wp_at_trivial)
      apply (fastforce simp:tcb_cap_cases_def)
     apply (simp add: transform_tcb_slot_4)
     apply (rule hoare_post_impErr[OF validE_R_validE[OF hoare_True_E_R]])
      apply simp+
    apply (rule_tac Q = "\<lambda>r s. invs s \<and> valid_etcbs s \<and> not_idle_thread (fst a') s \<and> tcb_at obj_id' s
      \<and> not_idle_thread obj_id' s \<and> not_idle_thread ab s \<and> cte_wp_at (\<lambda>a. True) (ab,ba) s
      \<and> cte_wp_at (\<lambda>c. c = cap.NullCap) (obj_id', tcb_cnode_index 4) s \<and> is_aligned a msg_align_bits"
      in hoare_post_impErr[where E="\<lambda>x. \<top>"])
      apply (simp add:not_idle_thread_def)
      apply (wp cap_delete_cte_at cap_delete_deletes cap_delete_valid_cap)
     apply (clarsimp simp:invs_valid_objs invs_mdb invs_valid_idle)
     apply (clarsimp simp:invs_def  valid_state_def not_idle_thread_def)
     apply (erule cte_wp_at_weakenE, erule sym)
    apply simp
   apply simp
  apply (clarsimp simp:emptyable_def not_idle_thread_def)
  apply (erule tcb_at_cte_at,clarsimp)
  done

lemma dcorres_tcb_update_vspace_root:
  "dcorres (dc \<oplus> dc) (\<top>) ( invs and valid_etcbs and tcb_at obj_id'
      and not_idle_thread obj_id' and valid_pdpt_objs and
      (\<lambda>y. case_option True (\<lambda>x. not_idle_thread (fst a') y) vroot') and
      (\<lambda>y. case_option True (is_valid_vtable_root \<circ> fst) vroot') and
           case_option (\<lambda>_. True) (valid_cap \<circ> fst) vroot' and
           case_option (\<lambda>_. True) (not_idle_thread \<circ> fst \<circ> snd ) vroot' and
           case_option (\<lambda>_. True) (no_cap_to_obj_dr_emp \<circ> fst) vroot' and
           case_option (\<lambda>_. True) (cte_wp_at (\<lambda>_. True) \<circ> snd) vroot')
    (case_option (returnOk ()) (tcb_update_vspace_root obj_id' (transform_cslot_ptr a'))
      (map_option (\<lambda>r. (transform_cap (fst r), transform_cslot_ptr (snd r))) vroot'))
    (case_option (returnOk ())
      (case_prod
      (\<lambda>new_cap src_slot.
        doE cap_delete (obj_id', tcb_cnode_index 1);
          liftE $
          check_cap_at new_cap src_slot $
          check_cap_at (cap.ThreadCap obj_id') a' $ cap_insert new_cap src_slot (obj_id', tcb_cnode_index 1)
        odE))
      vroot')"
  apply (case_tac vroot')
    apply simp_all
    apply (rule corres_guard_imp[OF corres_returnOk],simp+)
  apply (case_tac a)
  apply (unfold tcb_update_vspace_root_def tcb_update_thread_slot_def)
  apply (clarsimp simp:tcb_update_thread_slot_def)
  apply (rule dcorres_expand_pfx)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule dcorres_tcb_empty_slot)
       apply (simp add: transform_tcb_slot_1[symmetric])
      apply (clarsimp simp: check_cap_at_def liftE_bindE)
      apply (clarsimp simp: whenE_liftE bind_assoc)
      apply (clarsimp simp: liftE_def bind_assoc)
      apply (clarsimp simp: is_valid_vtable_root_def )
      apply (rule corres_split)
         apply (rule get_cap_corres; simp)
          apply (rule corres_split)
           apply (rule corres_when)
            apply (rule arch_same_obj_as_lift)
               apply (clarsimp simp: valid_cap_def is_arch_cap_def)+
           apply (rule corres_split)
              apply (rule get_cap_corres; simp)
             apply (rule corres_when)
              apply (rule sym)
              apply (case_tac cap')
                         apply (clarsimp simp: same_object_as_def)+
              apply (simp add: transform_cap_def split: arch_cap.splits)
             apply (simp add: transform_tcb_slot_1[symmetric])
             apply (rule dcorres_insert_cap_combine[folded alternative_com])
             apply (simp add: transform_cap_def)
            apply wp
           apply (simp add: same_object_as_def)
           apply (rule_tac Q = "\<lambda>r s. cte_wp_at ((=) cap.NullCap) (obj_id', tcb_cnode_index (Suc 0)) s \<and> cte_wp_at (\<lambda>_. True) (ba, c) s
             \<and>  valid_global_refs s \<and> valid_idle s \<and> valid_irq_node s \<and> valid_mdb s \<and> not_idle_thread ba s \<and> valid_objs s \<and> valid_etcbs s
             \<and> ((is_thread_cap r \<and> obj_ref_of r = obj_id') \<longrightarrow> ex_cte_cap_wp_to (\<lambda>_. True) (obj_id', tcb_cnode_index (Suc 0)) s)"
             in hoare_strengthen_post)
            apply (wp get_cap_ex_cte_cap_wp_to,clarsimp)
           apply clarsimp
           apply (drule (3) ex_cte_cap_to_not_idle, simp add: not_idle_thread_def)
          apply (rule corres_trivial)
          apply clarsimp
         apply (wp when_wp)
        apply (rule hoare_strengthen_post[OF hoare_TrueI[where P =\<top> ]])
        apply clarsimp
       apply (rule hoare_strengthen_post[OF hoare_TrueI[where P =\<top> ]])
       apply clarsimp+
      apply (rule hoare_drop_imp)
      apply (wp | simp)+
    apply (rule validE_validE_R)
    apply (rule_tac Q = "\<lambda>r s. invs s \<and> valid_etcbs s \<and> not_idle_thread ba s \<and>
                 not_idle_thread (fst a') s \<and> cte_wp_at (\<lambda>_. True) (ba, c) s \<and>
                 cte_wp_at (\<lambda>c. c = cap.NullCap) (obj_id', tcb_cnode_index (Suc 0)) s"
          in hoare_post_impErr[where E="\<lambda>x. \<top>"])
      apply (simp add: not_idle_thread_def)
      apply (wp cap_delete_cte_at cap_delete_deletes)
     apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
     apply (erule cte_wp_at_weakenE,clarsimp+)
  apply (simp add: emptyable_def not_idle_thread_def)
  apply (erule tcb_at_cte_at,clarsimp)
  done

lemma dcorres_tcb_update_cspace_root:
  "dcorres (dc \<oplus> dc) (\<top> ) ( invs and valid_etcbs and valid_pdpt_objs
           and not_idle_thread obj_id' and tcb_at obj_id' and
           case_option (\<lambda>_. True) (valid_cap \<circ> fst) croot' and
      (\<lambda>y. case_option True (\<lambda>x. not_idle_thread (fst a') y) croot') and
      (\<lambda>y. case_option True (Structures_A.is_cnode_cap \<circ> fst) croot') and
           case_option (\<lambda>_. True) (not_idle_thread \<circ> fst \<circ> snd ) croot' and
           case_option (\<lambda>_. True) (cte_wp_at (\<lambda>_. True) \<circ> snd) croot' and
           case_option (\<lambda>_. True) (no_cap_to_obj_dr_emp \<circ> fst) croot')
    (case_option (returnOk ()) (tcb_update_cspace_root obj_id' (transform_cslot_ptr a'))
        (map_option (\<lambda>r. (transform_cap (fst r), transform_cslot_ptr (snd r))) croot'))
    (case_option (returnOk ())
        (case_prod
        (\<lambda>new_cap src_slot.
          doE cap_delete (obj_id', tcb_cnode_index 0);
            liftE $
            check_cap_at new_cap src_slot $
            check_cap_at (cap.ThreadCap obj_id') a' $ cap_insert new_cap src_slot (obj_id', tcb_cnode_index 0)
          odE))
      croot')"
  apply (case_tac croot')
    apply simp_all
    apply (rule corres_guard_imp[OF dcorres_returnOk],simp+)
  apply (case_tac a)
  apply (clarsimp simp:tcb_update_cspace_root_def tcb_update_thread_slot_def)
  apply (simp add:transform_tcb_slot_simp[symmetric])
  apply (rule dcorres_expand_pfx)
    apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule dcorres_tcb_empty_slot)
       apply (simp add:transform_tcb_slot_0)
      apply (simp add:check_cap_at_def liftE_bindE)
      apply (clarsimp simp:no_cap_to_obj_with_diff_ref_def)
      apply (clarsimp simp:whenE_liftE bind_assoc same_object_as_def)
      apply (clarsimp simp:liftE_def bind_assoc)
      apply (rule corres_split)
         apply (rule get_cap_corres; simp)
        apply (rule_tac F = "(is_cnode_cap x \<and> obj_refs x = obj_refs aaa) \<longrightarrow> (bits_of x = bits_of aaa)"
                in corres_gen_asm2)
        apply (rule corres_split)
           apply (rule corres_when)
            apply (rule iffI)
             apply (clarsimp simp:is_cap_simps bits_of_def cap_type_def transform_cap_def
               split:cap.split_asm arch_cap.split_asm if_split_asm)
            apply (clarsimp simp:cap_has_object_def is_cap_simps cap_type_def)
           apply (rule corres_split)
              apply (rule get_cap_corres; simp)
             apply (rule corres_when)
              apply (rule sym)
              apply (simp add:table_cap_ref_def)
              apply (case_tac rv')
    (* Following line is incredibly brittle. You may need to change the number if the proof breaks *)
                         apply ((clarsimp simp:transform_cap_def split: arch_cap.splits)+)[12]
             apply (simp)
             apply (rule dcorres_insert_cap_combine[folded alternative_com])
             apply (clarsimp simp:is_cap_simps)
            apply wp
           apply (rule_tac Q = "\<lambda>r s. cte_wp_at ((=) cap.NullCap) (obj_id', tcb_cnode_index 0) s \<and> cte_wp_at (\<lambda>_. True) (ba, c) s
             \<and>  valid_global_refs s \<and> valid_idle s \<and> valid_irq_node s \<and> valid_mdb s \<and> not_idle_thread ba s \<and> valid_objs s \<and> valid_etcbs s
             \<and> ((is_thread_cap r \<and> obj_ref_of r = obj_id') \<longrightarrow> ex_cte_cap_wp_to (\<lambda>_. True) (obj_id', tcb_cnode_index 0) s)"
             in hoare_strengthen_post)
            apply (wp get_cap_ex_cte_cap_wp_to)
            apply (clarsimp+)[2]
           apply (drule (3) ex_cte_cap_to_not_idle, simp add: not_idle_thread_def)
           apply (erule valid_cap_aligned)
          apply (rule corres_trivial)
          apply (clarsimp)
         apply (wp when_wp)
        apply (rule hoare_strengthen_post[OF hoare_TrueI[where P =\<top> ]])
        apply clarsimp
       apply wp+
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_drop_imp)
       apply wp
      apply simp
      apply (rule_tac cnode_cap_unique_bits)
      apply simp
     apply clarsimp
     apply wp
    apply (clarsimp simp:conj_comms)
    apply (rule_tac Q = "\<lambda>r s. invs s \<and> valid_etcbs s \<and> not_idle_thread ba s \<and> valid_cap aaa s \<and>
                 not_idle_thread (fst a') s \<and> cte_wp_at (\<lambda>_. True) (ba, c) s \<and>
                 cte_wp_at (\<lambda>c. c = cap.NullCap) (obj_id', tcb_cnode_index 0) s \<and>
                 no_cap_to_obj_dr_emp aaa s"
            in hoare_post_impErr[where E = "\<lambda>r. \<top>"])
      apply (simp add:not_idle_thread_def)
      apply (wp cap_delete_cte_at cap_delete_deletes cap_delete_valid_cap)
     apply (simp add:invs_valid_objs)
     apply (clarsimp simp: invs_def valid_state_def no_cap_to_obj_with_diff_ref_def
                           cte_wp_at_def valid_pspace_vo)
    apply (clarsimp simp:empty_set_eq not_idle_thread_def emptyable_def)+
  apply (erule tcb_at_cte_at)
  apply (simp add:tcb_cap_cases_def)
  done

lemma tcb_fault_fault_handler_upd:
  "tcb_fault (obj'\<lparr>tcb_fault_handler := a\<rparr>) = tcb_fault obj'"
  by simp

lemma option_update_thread_corres:
  "dcorres (dc \<oplus> dc) \<top> (not_idle_thread obj_id and valid_etcbs)
       (case map_option of_bl fault_ep' of None \<Rightarrow> returnOk ()
        | Some x \<Rightarrow> liftE $ update_thread obj_id (cdl_tcb_fault_endpoint_update (\<lambda>_. x)))
       (liftE (option_update_thread obj_id (tcb_fault_handler_update \<circ> (\<lambda>x y. x)) fault_ep'))"
  apply (simp add:option_update_thread_def not_idle_thread_def)
  apply (case_tac fault_ep')
    apply (simp add:liftE_def bindE_def returnOk_def)
  apply clarsimp
  apply (simp add:update_thread_def thread_set_def get_thread_def bind_assoc)
  apply (rule dcorres_gets_the)
   apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
    apply (clarsimp simp:opt_object_tcb transform_tcb_def)
    apply (rule dcorres_set_object_tcb)
    apply (clarsimp simp:transform_tcb_def infer_tcb_pending_op_def )
    apply (simp add: get_etcb_def cong:transform_full_intent_caps_cong_weak)
    apply simp
   apply (clarsimp simp: get_tcb_def split:option.splits)
   apply (clarsimp simp: get_etcb_def split:option.splits)
   apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (clarsimp simp:opt_object_tcb)
done

lemma check_cap_at_stable:
  "\<lbrace>P\<rbrace>f\<lbrace>\<lambda>r. P\<rbrace>
   \<Longrightarrow>\<lbrace>P\<rbrace>check_cap_at aa b (check_cap_at aaa bb (f)) \<lbrace>\<lambda>r. P\<rbrace>"
  apply (clarsimp simp:check_cap_at_def not_idle_thread_def)
  apply (wp | simp split:if_splits)+
done

lemma case_option_wp:
  "(\<And>x. \<lbrace>P x\<rbrace>a\<lbrace>\<lambda>r. Q x\<rbrace>) \<Longrightarrow> \<lbrace>case_option \<top> P z\<rbrace>a\<lbrace>\<lambda>r. case_option \<top> Q z\<rbrace>"
  by (clarsimp split:option.splits)

lemma hoare_case_some:
  "\<lbrace>P\<rbrace>a\<lbrace>\<lambda>r s. Q s\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. case x of None \<Rightarrow> True | Some y \<Rightarrow> P s\<rbrace> a
    \<lbrace>\<lambda>rv s. case x of None \<Rightarrow> True | Some y \<Rightarrow> Q s\<rbrace>"
  apply (case_tac x)
    apply clarsimp+
done

lemma hoare_case_someE:
  "\<lbrace>P\<rbrace>a\<lbrace>\<lambda>r s. Q s\<rbrace>,- \<Longrightarrow> \<lbrace>\<lambda>s. case x of None \<Rightarrow> True | Some y \<Rightarrow> P s\<rbrace> a
    \<lbrace>\<lambda>rv s. case x of None \<Rightarrow> True | Some y \<Rightarrow> Q s\<rbrace>,-"
  apply (case_tac x)
    apply clarsimp+
done

lemma case_option_wpE:
  "(\<And>x. \<lbrace>P x\<rbrace>a\<lbrace>\<lambda>r. Q x\<rbrace>,-) \<Longrightarrow> \<lbrace>case_option \<top> P z\<rbrace>a\<lbrace>\<lambda>r. case_option \<top> Q z\<rbrace>,-"
  by (clarsimp split:option.splits)

lemma option_update_thread_not_idle_thread[wp]:
  "\<lbrace>not_idle_thread x and not_idle_thread a\<rbrace>option_update_thread a b c\<lbrace>\<lambda>r. not_idle_thread x\<rbrace>"
  apply(simp add: option_update_thread_def)
  apply (rule hoare_pre)
  apply wpc
  apply wp
  apply (clarsimp simp: thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: not_idle_thread_def)
  done

lemma reschedule_required_transform: "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> reschedule_required \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  by (clarsimp simp: reschedule_required_def set_scheduler_action_def etcb_at_def
     | wp tcb_sched_action_transform | wpc | assumption)+

lemma thread_set_priority_transform: "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> thread_set_priority tptr prio \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (clarsimp simp: thread_set_priority_def ethread_set_def set_eobject_def | wp)+
  apply (clarsimp simp: transform_def transform_objects_def transform_cdt_def transform_current_thread_def transform_asid_table_def)
  apply (rule_tac y="\<lambda>ptr. map_option (transform_object (machine_state s) ptr ((ekheap s |` (- {idle_thread s})) ptr)) ((kheap s |` (- {idle_thread s})) ptr)" in arg_cong)
  apply (rule ext)
  apply (rule_tac y="transform_object (machine_state s) ptr ((ekheap s |` (- {idle_thread s})) ptr)" in arg_cong)
  apply (rule ext)
  apply (clarsimp simp: transform_object_def transform_tcb_def restrict_map_def get_etcb_def split: option.splits Structures_A.kernel_object.splits)
  done

lemma possible_switch_to_transform:
  "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> possible_switch_to tptr \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  unfolding possible_switch_to_def
  by (wpsimp wp: tcb_sched_action_transform reschedule_required_transform set_scheduler_action_transform_inv)

lemma option_set_priority_dcorres:
  "dcorres (dc \<oplus> dc) \<top> \<top>
        (returnOk ())
        (liftE (case prio' of None \<Rightarrow> return () | Some (prio, auth) \<Rightarrow> do_extended_op (set_priority obj_id' prio)))"
  supply option.case_cong[cong] if_cong[cong]
  apply (clarsimp)
  apply (case_tac prio')
   apply (clarsimp simp: liftE_def set_priority_def returnOk_def bind_assoc)+
  apply (rule corres_noop)
   apply (wpsimp wp: reschedule_required_transform possible_switch_to_transform
                     thread_set_priority_transform tcb_sched_action_transform)+
  done

lemma option_set_priority_dcorres_strong:
  "dcorres (dc \<oplus> dc) P Q
        (returnOk ())
        (liftE (case prio' of None \<Rightarrow> return () | Some (prio, auth) \<Rightarrow> do_extended_op (set_priority obj_id' prio)))"
  supply option.case_cong[cong] if_cong[cong]
 apply (clarsimp)
 apply (case_tac prio')
 apply (clarsimp simp: liftE_def set_priority_def returnOk_def bind_assoc)+
 apply (rule corres_noop)
    apply (wpsimp wp: reschedule_required_transform possible_switch_to_transform
                     thread_set_priority_transform tcb_sched_action_transform)+
 done

lemma transform_full_intent_set_mcpriority:
  "transform_full_intent ms t (tcb_mcpriority_update f tcb) = transform_full_intent ms t tcb"
  by (simp add: transform_full_intent_def Let_def get_ipc_buffer_words_def
                get_tcb_message_info_def get_tcb_mrs_def)

lemma set_mcpriority_transform:
  "\<lbrace>\<lambda>s. transform s = i \<and> valid_etcbs s\<rbrace> set_mcpriority t mcp \<lbrace>\<lambda>rv s. transform s = i\<rbrace>"
  apply (clarsimp simp: set_mcpriority_def thread_set_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: transform_def transform_current_thread_def transform_objects_def)
  apply (thin_tac "i = _")
  apply (rule_tac f="(++) ((\<lambda>ptr. Some cdl_object.Untyped) |` (- {idle_thread s}))" in arg_cong)
  apply (rule ext)
  apply (rename_tac s tcb ptr)
  apply (drule (1) valid_etcbs_get_tcb_get_etcb; clarsimp)
  apply (drule get_etcb_SomeD; drule get_tcb_SomeD)
  by (case_tac "ptr = idle_thread s";
      clarsimp simp: transform_tcb_def transform_full_intent_set_mcpriority)

lemma option_set_mcpriority_corres:
  "dcorres (dc \<oplus> dc) \<top> valid_etcbs
    (returnOk ())
    (liftE (case mcp' of None \<Rightarrow> return () | Some (mcp, auth) \<Rightarrow> set_mcpriority t mcp))"
  apply (cases mcp'; simp add: liftE_def returnOk_def)
  apply (rule corres_noop; clarsimp)
  apply (wp set_mcpriority_transform)
  by simp

crunch valid_etcbs[wp]: option_update_thread, set_priority, set_mcpriority "valid_etcbs"
  (wp: crunch_wps simp: crunch_simps)

lemma not_idle_thread_ekheap_update[iff]:
  "not_idle_thread ptr (ekheap_update f s) = not_idle_thread ptr s"
  by (simp add: not_idle_thread_def)

lemma not_idle_thread_scheduler_action_update[iff]:
  "not_idle_thread ptr (scheduler_action_update f s) = not_idle_thread ptr s"
  by (simp add: not_idle_thread_def)

crunch not_idle_thread[wp]: reschedule_required, set_priority, set_mcpriority "not_idle_thread ptr"
  (wp: crunch_wps simp: crunch_simps)



crunch emptyable[wp]: tcb_sched_action "emptyable ptr"
  (wp: crunch_wps simp: crunch_simps)

crunch emptyable[wp]: reschedule_required "emptyable ptr"
  (wp: crunch_wps simp: crunch_simps)

crunch emptyable[wp]: set_priority, set_mcpriority "emptyable ptr"
  (wp: crunch_wps simp: crunch_simps)

lemma set_priority_transform: "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> set_priority tptr prio \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  by (clarsimp simp: set_priority_def ethread_set_def set_eobject_def cong: if_cong |
      wp reschedule_required_transform tcb_sched_action_transform
         possible_switch_to_transform thread_set_priority_transform)+

(* Workaround for schematic that won't instantiate with the usual valid_cap rule
   in the following dcorres_thread_control proof. *)
lemma set_mcpriority_valid_cap_fst:
  "\<lbrace>(valid_cap \<circ> fst) caps\<rbrace> set_mcpriority obj_id' new_mcp \<lbrace>\<lambda>rv. (valid_cap \<circ> fst) caps\<rbrace>"
  by clarsimp wp

lemma dcorres_dummy_returnOk_pl':
  "dcorres c P P' (f >>=E (\<lambda>_. returnOk ())) g \<Longrightarrow> dcorres c P P' f g"
  by simp

lemma corres_underlying_returnOk_ignored:
  "corres_underlying sr nf nf' (erel \<oplus> dc) P P' f (g >>=E (\<lambda>_. returnOk v))
    = corres_underlying sr nf nf' (erel \<oplus> dc) P P' f g"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule ball_cong[OF refl], rename_tac ss)
  apply (case_tac ss, rename_tac s s', clarsimp)
  apply (rule imp_cong[OF refl])
  apply (clarsimp simp: bindE_def bind_def returnOk_def return_def lift_def throwError_def
                 split: prod.splits sum.splits)
  apply (rule imp_cong[OF refl], rule conj_cong[OF _ refl], rule ball_cong[OF refl], rename_tac rr)
  by (case_tac rr; rename_tac rvs' t'; case_tac rvs'; rename_tac rv'; clarsimp)

lemma dcorres_thread_control:
  notes option.case_cong_weak [cong]
  notes case_map_option [simp del]
  shows
  "\<lbrakk> t' = tcb_invocation.ThreadControl obj_id' a' fault_ep' mcp' prio' croot' vroot' ipc_buffer';
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (\<lambda>s. invs s \<and> valid_etcbs s \<and>
            not_idle_thread obj_id' s \<and>
            tcb_at obj_id' s \<and> valid_pdpt_objs s \<and>
            case_option (\<lambda>_. True) (valid_cap \<circ> fst) croot' s \<and>
            case_option True (Structures_A.is_cnode_cap \<circ> fst) croot' \<and>
            case_option (\<lambda>_. True) (not_idle_thread \<circ> fst \<circ> snd) croot' s \<and>
      (\<lambda>y.  case_option True (\<lambda>x. not_idle_thread (fst a') y) croot') s \<and>
            case_option (\<lambda>_. True) (cte_wp_at (\<lambda>_. True) \<circ> snd) croot' s \<and>
            case_option (\<lambda>_. True) (no_cap_to_obj_dr_emp \<circ> fst) croot' s \<and>
      (\<lambda>y.  case_option True (\<lambda>x. not_idle_thread (fst a') y) vroot') s \<and>
            case_option True (is_valid_vtable_root \<circ> fst) vroot' \<and>
            case_option (\<lambda>_. True) (valid_cap \<circ> fst) vroot' s \<and>
            case_option (\<lambda>_. True) (not_idle_thread \<circ> fst \<circ> snd) vroot' s \<and>
            case_option (\<lambda>_. True) (cte_wp_at (\<lambda>_. True) \<circ> snd) vroot' s \<and>
            case_option (\<lambda>_. True) (no_cap_to_obj_dr_emp \<circ> fst) vroot' s \<and>
            (\<lambda>s. case_option True (is_valid_vtable_root \<circ> fst) vroot') s \<and>
      (\<lambda>y.  case_option True (\<lambda>x. not_idle_thread (fst a') y) ipc_buffer') s \<and>
            case_option (\<lambda>_. True) (case_option (\<lambda>_. True) (not_idle_thread \<circ> fst \<circ> snd) \<circ> snd) ipc_buffer' s \<and>
            case_option (\<lambda>_. True) (case_option (\<lambda>_. True) (cte_wp_at (\<lambda>_. True) \<circ> snd) \<circ> snd) ipc_buffer' s \<and>
            (case ipc_buffer' of None \<Rightarrow> True
             | Some v \<Rightarrow> case_option True ((swp valid_ipc_buffer_cap (fst v) and is_arch_cap and cap_aligned) \<circ> fst) (snd v)
            \<and> is_aligned (fst v) msg_align_bits)
          \<and> case_option (\<lambda>_. True) (\<lambda>a. case snd a of None \<Rightarrow> \<lambda>_. True | Some a \<Rightarrow> cte_wp_at (\<lambda>_. True) (snd a)) ipc_buffer' s
          \<and> (case fault_ep' of None \<Rightarrow> True | Some bl \<Rightarrow> length bl = word_bits))
       (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  (is "\<lbrakk> ?eq; ?eq' \<rbrakk> \<Longrightarrow> dcorres (dc \<oplus> dc) \<top> ?P ?f ?g")
  apply (clarsimp simp: Tcb_D.invoke_tcb_def translate_tcb_invocation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE[OF option_update_thread_corres])
      apply (rule corres_dummy_returnOk_pl)
      apply (rule corres_splitEE[OF option_set_mcpriority_corres])
        apply (rule corres_splitEE[OF dcorres_tcb_update_cspace_root])
          apply (rule corres_splitEE[OF dcorres_tcb_update_vspace_root])
            apply (rule dcorres_dummy_returnOk_pl')
            apply (rule corres_splitEE[where r'="dc" and P="\<top>"])
               apply (rule corres_underlying_returnOk_ignored[THEN iffD1])
               apply (rule dcorres_tcb_update_ipc_buffer)
              apply (rule dcorres_dummy_returnOk_pl')
              apply (rule corres_splitEE[where r'="dc" and P="\<top>"])
                 apply (rule option_set_priority_dcorres_strong)
                apply (rule dcorres_returnOk')
                apply (simp add: dc_def)
               apply wpsimp+
           apply (rule check_cap_at_stable, (clarsimp simp: not_idle_thread_def | wp+)+)+
            apply (wp case_option_wp | simp add: o_def not_idle_thread_def)+
            apply (simp add: option.split[where P="\<lambda>x. x"] not_idle_thread_def)
            apply (wp hoare_vcg_const_imp_lift)
           apply (clarsimp simp: conj_comms)
           apply (clarsimp simp: not_idle_thread_def split: option.split_asm)
          apply (wp cap_delete_deletes cap_delete_valid_cap | simp)+
          apply (strengthen tcb_cap_always_valid_strg use_no_cap_to_obj_asid_strg)
          apply (clarsimp simp: tcb_cap_cases_def)
          apply (strengthen is_cnode_or_valid_arch_cap_asid[simplified,THEN conjunct1])
          apply (strengthen is_cnode_or_valid_arch_cap_asid[simplified,THEN conjunct2])
          apply (wp cap_delete_deletes cap_delete_cte_at cap_delete_valid_cap
                    case_option_wpE
                 | simp add: not_idle_thread_def option.split[where P="\<lambda>x. x"])+
        apply (rule_tac Q'="\<lambda>_. ?P" in hoare_post_imp_R[rotated])
         apply (clarsimp simp: is_valid_vtable_root_def is_cnode_or_valid_arch_def
                               is_arch_cap_def not_idle_thread_def emptyable_def
                        split: option.splits)
        apply (wpc|wp|simp)+
         apply (simp only: o_def)
         apply (wpe checked_insert_no_cap_to)
         apply (wpe hoare_case_option_wp[
                      where v=vroot' and f="\<lambda>_. f'" and
                            Q'="\<lambda>x rv. (no_cap_to_obj_dr_emp \<circ> fst) x" for f',
                      OF hoare_vcg_prop[where P=True],
                      simplified comp_apply,
                      OF checked_insert_no_cap_to])
         apply (rule check_cap_at_stable, (clarsimp simp: not_idle_thread_def | wp+)+)+
          apply (simp add: option.split[where P="\<lambda>x. x"] not_idle_thread_def)
          apply (wp hoare_vcg_const_imp_lift case_option_wp | simp add: not_idle_thread_def)+
         apply (clarsimp simp: conj_comms)
         apply (intro conjI; clarsimp simp: not_idle_thread_def split: option.split)
        apply (wp cap_delete_deletes cap_delete_valid_cap)+
        apply (strengthen tcb_cap_always_valid_strg use_no_cap_to_obj_asid_strg)
        apply (simp add: tcb_cap_cases_def)
        apply (strengthen is_cnode_or_valid_arch_cap_asid[simplified,THEN conjunct1])
        apply (strengthen is_cnode_or_valid_arch_cap_asid[simplified,THEN conjunct2])
        apply simp
        apply (wp cap_delete_deletes cap_delete_cte_at cap_delete_valid_cap)+
        apply ((wp case_option_wpE cap_delete_valid_cap cap_delete_deletes cap_delete_cte_at
                  hoare_case_someE)+
                | simp add: not_idle_thread_def)+
      apply (case_tac mcp', clarsimp, rule return_wp, clarsimp)
      subgoal by (wp case_option_wp dxo_wp_weak hoare_vcg_const_imp_lift hoare_vcg_all_lift
                  | simp add: option.split[where P="\<lambda>x. x"]
                  | intro conjI allI impI
                  | clarsimp split: option.split)+
     apply (wp case_option_wpE)+
    apply (rule_tac Q="\<lambda>_. ?P" in hoare_strengthen_post[rotated])
     apply (clarsimp simp: is_valid_vtable_root_def is_cnode_or_valid_arch_def
                           is_arch_cap_def not_idle_thread_def emptyable_def
                    split: option.splits)
    apply (rule_tac P = "(case fault_ep' of None \<Rightarrow> True | Some bl \<Rightarrow> length bl = word_bits)"
             in hoare_gen_asm)
    apply (wp out_invs_trivialT)
            apply (clarsimp simp: tcb_cap_cases_def)+
    apply (wp case_option_wp out_cte_at out_valid_cap hoare_case_some | simp)+
     apply (wp out_no_cap_to_trivial)
     apply (clarsimp simp: tcb_cap_cases_def)
    apply (wp case_option_wp out_cte_at out_valid_cap hoare_case_some | simp)+
     apply (wp out_no_cap_to_trivial)
     apply (clarsimp simp: tcb_cap_cases_def)
    apply (wp case_option_wp out_cte_at out_valid_cap hoare_case_some | simp)+
  by (clarsimp split: option.splits)

lemma invoke_tcb_corres_thread_control:
  "\<lbrakk> t' = tcb_invocation.ThreadControl obj_id' a' fault_ep' mcp' prio' croot' vroot' ipc_buffer';
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (\<lambda>s. invs s \<and> valid_etcbs s \<and> not_idle_thread obj_id' s
                   \<and> valid_pdpt_objs s \<and> Tcb_AI.tcb_inv_wf t' s)
       (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (rule corres_guard_imp[OF dcorres_thread_control])
     apply fastforce
    apply ((clarsimp simp:conj_comms valid_cap_aligned simp del:split_paired_All)+)[2]
  apply (elim conjE)
  apply (subgoal_tac "\<forall>x. ex_cte_cap_to x s \<longrightarrow> not_idle_thread (fst x) s")
   apply (intro conjI)
                          apply ((clarsimp simp del:split_paired_All split:option.splits)+)[19]
       apply (case_tac ipc_buffer',simp)
       apply (case_tac "snd a",simp)
       apply (clarsimp simp del:split_paired_All split:option.splits)
      apply (case_tac ipc_buffer',simp)
      apply (case_tac "snd a",simp)
      apply (clarsimp simp del:split_paired_All split:option.splits)
     apply (case_tac ipc_buffer',simp)
     apply (case_tac "snd a",simp)
     apply (clarsimp simp del:split_paired_All split:option.splits)
    apply (case_tac ipc_buffer',simp)
    apply (case_tac "snd a",simp)
    apply (clarsimp simp del:split_paired_All split:option.splits)
   apply (clarsimp simp del:split_paired_All split:option.splits)
  apply clarsimp
  apply (drule ex_cte_cap_wp_to_not_idle)+
      by (clarsimp simp:invs_def valid_state_def valid_pspace_def)+

lemma invoke_tcb_corres_suspend:
  "\<lbrakk> t' = tcb_invocation.Suspend obj_id';
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (invs and not_idle_thread obj_id' and tcb_at obj_id' and valid_etcbs)
    (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (clarsimp simp: Tcb_D.invoke_tcb_def translate_tcb_invocation_def)
  apply (rule corres_alternate1)
  apply (rule corres_bind_ignore_ret_rhs)
  apply (rule corres_return_dc_rhs)
  apply (rule corres_guard_imp)
    apply (rule suspend_corres, simp+)
  done

lemma invoke_tcb_corres_resume:
  "\<lbrakk> t' = tcb_invocation.Resume obj_id';
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (invs and not_idle_thread obj_id' and tcb_at obj_id' and valid_etcbs)
  (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (clarsimp simp: Tcb_D.invoke_tcb_def translate_tcb_invocation_def)
  apply (rule corres_bind_ignore_ret_rhs)
  apply (rule corres_return_dc_rhs)
  apply (rule corres_guard_imp[OF restart_corres],clarsimp+)
  done

lemma dcorres_bind_notification:
  "dcorres dc (\<lambda>_. True) (valid_etcbs and not_idle_thread t)
   (Tcb_D.bind_notification t a) (Tcb_A.bind_notification t a)"
  apply (clarsimp simp: Tcb_D.bind_notification_def Tcb_A.bind_notification_def
                        get_simple_ko_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (simp split: option.splits)
  apply (clarsimp simp: assert_def corres_free_fail partial_inv_def a_type_def
                 split: Structures_A.kernel_object.splits)
  apply (rule corres_dummy_return_pl)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_dummy_set_notification], simp)
      apply (rule set_bound_notification_corres)
     apply (wp |simp add: not_idle_thread_def infer_tcb_bound_notification_def)+
  done

lemma invoke_tcb_corres_bind:
  "\<lbrakk> t' = tcb_invocation.NotificationControl obj_id' (Some ntfnptr);
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (invs and not_idle_thread obj_id' and tcb_at obj_id' and valid_etcbs)
  (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (clarsimp simp: Tcb_D.invoke_tcb_def translate_tcb_invocation_def)
  apply (rule corres_dummy_return_l)
  apply (rule corres_guard_imp)
  apply (rule corres_split[OF dcorres_bind_notification corres_return_trivial])
  apply (wp | simp)+
  done

lemma invoke_tcb_corres_unbind:
  "\<lbrakk> t' = tcb_invocation.NotificationControl obj_id' None;
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (invs and not_idle_thread obj_id' and tcb_at obj_id' and valid_etcbs)
  (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (clarsimp simp: Tcb_D.invoke_tcb_def translate_tcb_invocation_def)
  apply (rule corres_dummy_return_l)
  apply (rule corres_guard_imp)
  apply (rule corres_split[OF dcorres_unbind_notification corres_return_trivial])
  apply (wp | simp)+
  done

lemma invoke_tcb_corres_setTLSBase:
  "\<lbrakk> t' = tcb_invocation.SetTLSBase obj_id' tls_base;
     t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (invs and not_idle_thread obj_id' and tcb_at obj_id' and valid_etcbs)
  (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (clarsimp simp: Tcb_D.invoke_tcb_def translate_tcb_invocation_def)
  apply (rule corres_dummy_return_l)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'=dc])
       apply (rule corrupt_tcb_intent_as_user_corres)
      apply (rule corres_symb_exec_r)
         apply (rule corres_split_noop_rhs[OF corres_trivial])
           apply simp
           apply (clarsimp simp: when_def)
           apply (rule reschedule_required_dcorres[THEN corres_trivial])
          apply wpsimp+
  done

lemma ex_nonz_cap_to_idle_from_invs:
  "invs s \<Longrightarrow> \<not> ex_nonz_cap_to (idle_thread s) s"
  apply (rule Invariants_AI.idle_no_ex_cap)
   apply (clarsimp simp: invs_def valid_state_def)
  apply (clarsimp simp: invs_def valid_state_def)
  done

lemma ex_nonz_cap_implies_normal_tcb:
  "\<lbrakk> invs s; tcb_at t' s; ex_nonz_cap_to t' s \<rbrakk> \<Longrightarrow> not_idle_thread t' s"
  by (auto simp: ex_nonz_cap_to_idle_from_invs not_idle_thread_def)

lemmas invoke_tcb_rules = ex_nonz_cap_implies_normal_tcb

lemma invoke_tcb_corres:
  "\<lbrakk> t = translate_tcb_invocation t' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc) \<top> (invs and valid_pdpt_objs and Tcb_AI.tcb_inv_wf t' and valid_etcbs)
     (Tcb_D.invoke_tcb t) (Tcb_A.invoke_tcb t')"
  apply (clarsimp)
  apply (case_tac t')
         apply (rule corres_guard_imp [OF invoke_tcb_corres_write_regs], assumption, auto intro:invoke_tcb_rules )[1]
        apply (rule corres_guard_imp [OF invoke_tcb_corres_read_regs], assumption, auto intro!:invoke_tcb_rules)[1]
       apply (rule corres_guard_imp [OF invoke_tcb_corres_copy_regs], assumption, auto intro!:invoke_tcb_rules)[1]
      apply (rule corres_guard_imp [OF invoke_tcb_corres_thread_control],assumption,auto intro!:invoke_tcb_rules)[1]
     apply (rule corres_guard_imp [OF invoke_tcb_corres_suspend], assumption, auto intro!:invoke_tcb_rules)[1]
    apply (rule corres_guard_imp [OF invoke_tcb_corres_resume], assumption, auto intro!:invoke_tcb_rules)[1]
   apply (rename_tac option)
   apply (case_tac option)
    apply (simp only:, rule corres_guard_imp[OF invoke_tcb_corres_unbind], simp , auto intro!: invoke_tcb_rules)[1]
   apply (simp only:, rule corres_guard_imp[OF invoke_tcb_corres_bind], simp , auto intro!: invoke_tcb_rules)[1]
  apply (rule corres_guard_imp [OF invoke_tcb_corres_setTLSBase], assumption, auto intro!:invoke_tcb_rules)[1]
  done

end

end
