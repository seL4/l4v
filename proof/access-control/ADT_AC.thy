(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ADT_AC
imports ArchSyscall_AC
begin


locale ADT_AC_1 =
  fixes aag :: "'a PAS"
  assumes user_op_access:
    "\<lbrakk> invs s; pas_refined aag s; is_subject aag tcb;
       ptable_lift tcb s x = Some ptr; auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x) \<rbrakk>
       \<Longrightarrow> abs_has_auth_to aag auth tcb (ptrFromPAddr ptr)"
  and write_in_vspace_cap_rights:
    "AllowWrite \<in> ptable_rights (cur_thread s) s va
     \<Longrightarrow> Write \<in> vspace_cap_rights_to_auth (ptable_rights (cur_thread s) s va)"
begin

lemma user_op_access':
  "\<lbrakk> invs s; pas_refined aag s; is_subject aag tcb;
     ptable_lift tcb s x = Some (addrFromPPtr ptr);
     auth \<in> vspace_cap_rights_to_auth (ptable_rights tcb s x) \<rbrakk>
     \<Longrightarrow> abs_has_auth_to aag auth tcb ptr"
  by (auto dest: user_op_access simp: ptrFormPAddr_addFromPPtr)

lemma integrity_underlying_mem_update:
  "\<lbrakk> integrity aag X st s; \<forall>x\<in>xs. aag_has_auth_to aag Write x;
     \<forall>x\<in>-xs. um' x = underlying_memory (machine_state s) x \<rbrakk>
     \<Longrightarrow> integrity aag X st (s\<lparr>machine_state := machine_state s\<lparr>underlying_memory := \<lambda>m. um' m\<rparr>\<rparr>)"
  apply (clarsimp simp: integrity_def)
  apply (case_tac "x \<in> xs")
   apply (erule_tac x=x in ballE)
    apply (rule trm_write)
    apply simp+
  done

lemma dmo_user_memory_update_respects_Write:
  "\<lbrace>integrity aag X st and K (\<forall>p \<in> dom um. aag_has_auth_to aag Write p)\<rbrace>
   do_machine_op (user_memory_update um)
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  unfolding user_memory_update_def
  apply (wp dmo_wp)
  apply clarsimp
  sorry (* FIXME: broken by touched-addrs -robs
  apply (rule integrity_underlying_mem_update; simp?)
  apply (simp add: dom_def)
  done
*)

lemma integrity_device_state_update:
  "\<lbrakk> integrity aag X st s; \<forall>x\<in>xs. aag_has_auth_to aag Write x; \<forall>x\<in>-xs. um' x = None \<rbrakk>
     \<Longrightarrow> integrity aag X st (machine_state_update (\<lambda>v. v\<lparr>device_state := device_state v ++ um'\<rparr>) s)"
  apply (clarsimp simp: integrity_def)
  apply (case_tac "x \<in> xs")
   apply (erule_tac x=x in ballE)
    apply (rule trd_write)
    apply simp+
  apply (erule_tac x = x in allE, erule integrity_device.cases)
    apply (erule trd_lrefl)
   apply (rule trd_orefl)
   apply (clarsimp simp: map_add_def)
  apply (erule trd_write)
  done

lemma dmo_device_update_respects_Write:
  "\<lbrace>integrity aag X st and (\<lambda>s. device_state (machine_state s) = um)
                       and K (\<forall>p \<in> dom um'. aag_has_auth_to aag Write p)\<rbrace>
   do_machine_op (device_memory_update um')
   \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: device_memory_update_def)
  apply (rule hoare_pre)
   apply (wp dmo_wp)
  apply clarsimp
  apply (simp cong: abstract_state.fold_congs)
  apply (rule integrity_device_state_update)
    apply simp
   apply clarify
   apply (drule (1) bspec)
   apply simp
  apply fastforce
  done

lemma dmo_um_upd_machine_state:
  "do_machine_op (user_memory_update ms) \<lbrace>\<lambda>s. P (device_state (machine_state s))\<rbrace>"
  by (rule dmo_wp) (simp add: user_memory_update_def simpler_modify_def valid_def)

lemma do_user_op_respects:
 "\<lbrace>invs and integrity aag X st and is_subject aag \<circ> cur_thread and pas_refined aag\<rbrace>
  do_user_op uop tc
  \<lbrace>\<lambda>_. integrity aag X st\<rbrace>"
  apply (simp add: do_user_op_def)
  apply wpsimp+
           apply (rule dmo_device_update_respects_Write)
          apply (wpsimp wp: dmo_um_upd_machine_state
                            dmo_user_memory_update_respects_Write
                            hoare_vcg_all_lift hoare_vcg_imp_lift)+
          apply (rule hoare_pre_cont)
         apply (wpsimp wp: select_wp)+
  apply (simp add: restrict_map_def split: if_splits)
  apply (rule conjI)
   apply (clarsimp split: if_splits)
   apply (drule_tac auth=Write in user_op_access')
       apply (simp add: write_in_vspace_cap_rights)+
  apply (rule conjI, simp)
  apply (clarsimp split: if_splits)
  apply (drule_tac auth=Write in user_op_access')
      apply (simp add: write_in_vspace_cap_rights)+
  done

end


lemma objs_valid_tcb_vtable:
  "\<lbrakk> valid_objs s; get_tcb False t s = Some tcb \<rbrakk> \<Longrightarrow> s \<turnstile> tcb_vtable tcb"
  apply (clarsimp simp: get_tcb_def split: option.splits Structures_A.kernel_object.splits)
  apply (erule cte_wp_valid_cap[rotated])
  apply (rule cte_wp_at_tcbI[where t="(a, b)" for a b, where b3="tcb_cnode_index 1"])
    apply fastforce+
  done

end
