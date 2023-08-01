(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

text \<open>
  This file sets up a kernel automaton, ADT_A_if, which is
  slightly different from ADT_A.
  It then setups a big step framework to transfrom this automaton in the
  big step automaton on which the infoflow theorem will be proved
\<close>

theory ArchADT_IF
imports ADT_IF
begin

context Arch begin global_naming ARM

named_theorems ADT_IF_assms

lemma dmo_getExMonitor_wp[wp]:
  "\<lbrace>\<lambda>s. P (exclusive_state (machine_state s)) s\<rbrace>
   do_machine_op getExMonitor
   \<lbrace>P\<rbrace>"
  apply (simp add: do_machine_op_def)
  apply (wp modify_wp | wpc)+
  apply clarsimp
  apply (erule use_valid)
   apply wp
  apply simp
  done

lemma setExMonitor_wp[wp]:
  "\<lbrace>\<lambda>ms. P (ms\<lparr>exclusive_state := es\<rparr>)\<rbrace>
   setExMonitor es
   \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: setExMonitor_def | wp)+

lemma dmo_setExMonitor_wp[wp]:
  "\<lbrace>\<lambda>s. P (s\<lparr>machine_state := machine_state s \<lparr>exclusive_state := es\<rparr>\<rparr>)\<rbrace>
   do_machine_op (setExMonitor es)
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: do_machine_op_def)
  apply (wp modify_wp | wpc)+
  apply clarsimp
  apply (erule use_valid)
   apply wp
  apply simp
  done

lemma valid_state_exclusive_state_update[iff]:
  "valid_state (s\<lparr>machine_state := machine_state s\<lparr>exclusive_state := es\<rparr>\<rparr>) = valid_state s"
  by (simp add: valid_state_def valid_irq_states_def valid_machine_state_def)

lemma cur_tcb_exclusive_state_update[iff]:
  "cur_tcb (s\<lparr>machine_state := machine_state s\<lparr>exclusive_state := es\<rparr>\<rparr>) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma invs_exclusive_state_update[iff]:
  "invs (s\<lparr>machine_state := machine_state s\<lparr>exclusive_state := es\<rparr>\<rparr>) = invs s"
  by (simp add: invs_def)

(* FIXME: clagged from AInvs.do_user_op_invs *)
lemma do_user_op_if_invs[ADT_IF_assms]:
  "\<lbrace>invs and ct_running\<rbrace>
   do_user_op_if f tc
   \<lbrace>\<lambda>_. invs and ct_running\<rbrace>"
  apply (simp add: do_user_op_if_def split_def)
  apply (wp do_machine_op_ct_in_state device_update_invs | wp (once) dmo_invs | simp)+
  apply (clarsimp simp: user_mem_def user_memory_update_def simpler_modify_def restrict_map_def
                        invs_def cur_tcb_def ptable_rights_s_def ptable_lift_s_def)
  apply (frule ptable_rights_imp_frame)
    apply fastforce
   apply simp
  apply (clarsimp simp: valid_state_def device_frame_in_device_region)
  done

crunch domain_sep_inv[ADT_IF_assms, wp]: do_user_op_if "domain_sep_inv irqs st"
  (ignore: user_memory_update)

crunch valid_sched[ADT_IF_assms, wp]: do_user_op_if "valid_sched"
  (ignore: user_memory_update)

crunch irq_masks[ADT_IF_assms, wp]: do_user_op_if "\<lambda>s. P (irq_masks_of_state s)"
  (ignore: user_memory_update wp: dmo_wp no_irq)

crunch valid_list[ADT_IF_assms, wp]: do_user_op_if "valid_list"
  (ignore: user_memory_update)

lemma do_user_op_if_scheduler_action[ADT_IF_assms, wp]:
  "do_user_op_if f tc \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace>"
  by (simp add: do_user_op_if_def | wp | wpc)+

lemma do_user_op_silc_inv[ADT_IF_assms, wp]:
  "do_user_op_if f tc \<lbrace>silc_inv aag st\<rbrace>"
  apply (simp add: do_user_op_if_def)
  apply (wp | wpc | simp)+
  done

lemma do_user_op_pas_refined[ADT_IF_assms, wp]:
  "do_user_op_if f tc \<lbrace>pas_refined aag\<rbrace>"
  apply (simp add: do_user_op_if_def)
  apply (wp | wpc | simp)+
  done

crunches do_user_op_if
  for cur_thread[ADT_IF_assms, wp]: "\<lambda>s. P (cur_thread s)"
  and cur_domain[ADT_IF_assms, wp]: "\<lambda>s. P (cur_domain s)"
  and idle_thread[ADT_IF_assms, wp]: "\<lambda>s. P (idle_thread s)"
  and domain_fields[ADT_IF_assms, wp]: "domain_fields P"
  (ignore: user_memory_update)

lemma do_use_op_guarded_pas_domain[ADT_IF_assms, wp]:
  "do_user_op_if f tc \<lbrace>guarded_pas_domain aag\<rbrace>"
  by (rule guarded_pas_domain_lift; wp)

lemma tcb_arch_ref_tcb_context_set[ADT_IF_assms, simp]:
  "tcb_arch_ref (tcb_arch_update (arch_tcb_context_set tc) tcb) = tcb_arch_ref tcb"
  by (simp add: tcb_arch_ref_def)

crunches arch_switch_to_idle_thread, arch_switch_to_thread
  for pspace_aligned[ADT_IF_assms, wp]: "\<lambda>s :: det_state. pspace_aligned s"
  and valid_vspace_objs[ADT_IF_assms, wp]: "\<lambda>s :: det_state. valid_vspace_objs s"
  and valid_arch_state[ADT_IF_assms, wp]: "\<lambda>s :: det_state. valid_arch_state s"
  (wp: crunch_wps)

crunches arch_activate_idle_thread, arch_switch_to_thread
  for cur_thread[ADT_IF_assms, wp]: "\<lambda>s. P (cur_thread s)"

lemma arch_activate_idle_thread_scheduler_action[ADT_IF_assms, wp]:
  "arch_activate_idle_thread t \<lbrace>\<lambda>s :: det_state. P (scheduler_action s)\<rbrace>"
  by (wpsimp simp: arch_activate_idle_thread_def)

crunch domain_fields[ADT_IF_assms, wp]: handle_vm_fault, handle_hypervisor_fault "domain_fields P"
  (ignore: getFAR getDFSR getIFSR)

lemma arch_perform_invocation_noErr[ADT_IF_assms, wp]:
  "\<lbrace>\<top>\<rbrace> arch_perform_invocation a -, \<lbrace>Q\<rbrace>"
  by (wpsimp simp: arch_perform_invocation_def)

lemma arch_invoke_irq_control_noErr[ADT_IF_assms, wp]:
  "\<lbrace>\<top>\<rbrace> arch_invoke_irq_control a -, \<lbrace>Q\<rbrace>"
  by (cases a; wpsimp)

crunch irq_state[wp]: cleanCacheRange_PoU "\<lambda>s. P (irq_state s)"
  (ignore_del: cleanCacheRange_PoU cleanByVA_PoU)

crunch irq_state_of_state[ADT_IF_assms, wp]: init_arch_objects "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp ignore: do_machine_op)

lemma getActiveIRQ_None[ADT_IF_assms]:
  "(None,s') \<in> fst (do_machine_op (getActiveIRQ in_kernel) s)  \<Longrightarrow>
   irq_at (irq_state (machine_state s) + 1) (irq_masks (machine_state s)) = None"
  apply (erule use_valid)
   apply (wp dmo_getActiveIRQ_wp)
  by simp

lemma getActiveIRQ_Some[ADT_IF_assms]:
  "(Some i, s') \<in> fst (do_machine_op (getActiveIRQ in_kernel) s)
   \<Longrightarrow> irq_at (irq_state (machine_state s) + 1) (irq_masks (machine_state s)) = Some i"
  apply (erule use_valid)
   apply (wp dmo_getActiveIRQ_wp)
  by simp

lemma idle_equiv_as_globals_equiv:
  "arm_global_pd (arch_state s) \<noteq> idle_thread s
   \<Longrightarrow> idle_equiv st s =
       globals_equiv (st\<lparr>arch_state := arch_state s, machine_state := machine_state s,
                         kheap:= (kheap st)(arm_global_pd (arch_state s) :=
                                              kheap s (arm_global_pd (arch_state s))),
                                            cur_thread := cur_thread s\<rparr>) s"
  by (clarsimp simp: idle_equiv_def globals_equiv_def tcb_at_def2)

lemma idle_globals_lift:
  assumes g: "\<And>st. \<lbrace>globals_equiv st and P\<rbrace> f \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  assumes i: "\<And>s. P s \<Longrightarrow> arm_global_pd (arch_state s) \<noteq> idle_thread s"
  shows "\<lbrace>idle_equiv st and P\<rbrace> f \<lbrace>\<lambda>_. idle_equiv st\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "arm_global_pd (arch_state s) \<noteq> idle_thread s")
   apply (subst (asm) idle_equiv_as_globals_equiv,simp+)
   apply (frule use_valid[OF _ g])
    apply simp+
   apply (clarsimp simp: idle_equiv_def globals_equiv_def tcb_at_def2)
  apply (erule i)
  done

lemma idle_equiv_as_globals_equiv_scheduler:
  "arm_global_pd (arch_state s) \<noteq> idle_thread s
   \<Longrightarrow> idle_equiv st s =
       globals_equiv_scheduler (st\<lparr>arch_state := arch_state s, machine_state := machine_state s,
                                   kheap:= (kheap st)(arm_global_pd (arch_state s) :=
                                                        kheap s (arm_global_pd (arch_state s)))\<rparr>) s"
  by (clarsimp simp: idle_equiv_def tcb_at_def2 globals_equiv_scheduler_def
                     arch_globals_equiv_scheduler_def)

lemma idle_globals_lift_scheduler:
  assumes g: "\<And>st. \<lbrace>globals_equiv_scheduler st and P\<rbrace> f \<lbrace>\<lambda>_. globals_equiv_scheduler st\<rbrace>"
  assumes i: "\<And>s. P s \<Longrightarrow> arm_global_pd (arch_state s) \<noteq> idle_thread s"
  shows "\<lbrace>idle_equiv st and P\<rbrace> f \<lbrace>\<lambda>_. idle_equiv st\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "arm_global_pd (arch_state s) \<noteq> idle_thread s")
   apply (subst (asm) idle_equiv_as_globals_equiv_scheduler,simp+)
   apply (frule use_valid[OF _ g])
    apply simp+
   apply (clarsimp simp: idle_equiv_def globals_equiv_scheduler_def tcb_at_def2)
  apply (erule i)
  done

lemma invs_pd_not_idle_thread[intro]:
  "invs s \<Longrightarrow> arm_global_pd (arch_state s) \<noteq> idle_thread s"
  by (fastforce simp: invs_def valid_state_def valid_global_objs_def
                      obj_at_def valid_idle_def pred_tcb_at_def empty_table_def)

lemma kernel_entry_if_idle_equiv[ADT_IF_assms]:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s) and idle_equiv st
         and (\<lambda>s. ct_idle s \<longrightarrow> tc = idle_context s)\<rbrace>
   kernel_entry_if e tc
   \<lbrace>\<lambda>_. idle_equiv st\<rbrace>"
  apply (rule hoare_pre)
   apply (rule idle_globals_lift)
    apply (wp kernel_entry_if_globals_equiv)
    apply force
   apply (fastforce intro!: invs_pd_not_idle_thread)+
  done

lemmas handle_preemption_idle_equiv[ADT_IF_assms, wp] =
  idle_globals_lift[OF handle_preemption_globals_equiv invs_pd_not_idle_thread, simplified]

lemmas schedule_if_idle_equiv[ADT_IF_assms, wp] =
  idle_globals_lift_scheduler[OF schedule_if_globals_equiv_scheduler invs_pd_not_idle_thread, simplified]

lemma do_user_op_if_idle_equiv[ADT_IF_assms, wp]:
  "\<lbrace>idle_equiv st and invs\<rbrace>
   do_user_op_if uop tc
   \<lbrace>\<lambda>_. idle_equiv st\<rbrace>"
  unfolding do_user_op_if_def
  by (wpsimp wp: dmo_user_memory_update_idle_equiv dmo_device_memory_update_idle_equiv)

lemma not_in_global_refs_vs_lookup:
  "\<lbrakk> (\<exists>\<unrhd>p) s; valid_vs_lookup s; valid_global_refs s; valid_arch_state s; valid_global_objs s \<rbrakk>
     \<Longrightarrow> p \<notin> global_refs s"
  apply (clarsimp dest!: valid_vs_lookupD)
  apply (drule(1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  apply blast
  done

lemma kernel_entry_if_valid_pdpt_objs[wp]:
 "\<lbrace>valid_pdpt_objs and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
  kernel_entry_if e tc
  \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (case_tac "e = Interrupt")
   apply (simp add: kernel_entry_if_def)
   apply (wp | wpc | simp add: kernel_entry_if_def)+
    apply (wpsimp simp: ran_tcb_cap_cases arch_tcb_update_aux2
                    wp: static_imp_wp thread_set_invs_trivial)+
  done

lemma kernel_entry_if_valid_vspace_objs_if[ADT_IF_assms, wp]:
  "\<lbrace>valid_vspace_objs_if and invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_active s)\<rbrace>
   kernel_entry_if e tc
   \<lbrace>\<lambda>_. valid_vspace_objs_if\<rbrace>"
  by wpsimp

lemma handle_preemption_if_valid_pdpt_objs[ADT_IF_assms, wp]:
  "\<lbrace>valid_vspace_objs_if\<rbrace> handle_preemption_if a \<lbrace>\<lambda>rv s. valid_vspace_objs_if s\<rbrace>"
  by (simp add: handle_preemption_if_def | wp)+

lemma schedule_if_valid_pdpt_objs[ADT_IF_assms, wp]:
  "\<lbrace>valid_vspace_objs_if\<rbrace> schedule_if a \<lbrace>\<lambda>rv s. valid_vspace_objs_if s\<rbrace>"
  by (simp add: schedule_if_def | wp)+

lemma do_user_op_if_valid_pdpt_objs[ADT_IF_assms, wp]:
  "\<lbrace>valid_vspace_objs_if\<rbrace> do_user_op_if a b \<lbrace>\<lambda>rv s. valid_vspace_objs_if s\<rbrace>"
  by (simp add: do_user_op_if_def | wp | wpc)+

lemma valid_vspace_objs_if_ms_update[ADT_IF_assms, simp]:
  "valid_vspace_objs_if (machine_state_update f s) = valid_vspace_objs_if s"
  by auto

lemma do_user_op_if_irq_state_of_state[ADT_IF_assms]:
  "do_user_op_if utf uc \<lbrace>\<lambda>s. P (irq_state_of_state s)\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: do_user_op_if_def user_memory_update_def | wp dmo_wp | wpc)+
  done

lemma do_user_op_if_irq_masks_of_state[ADT_IF_assms]:
  "do_user_op_if utf uc \<lbrace>\<lambda>s. P (irq_masks_of_state s)\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: do_user_op_if_def user_memory_update_def | wp dmo_wp | wpc)+
  done

lemma do_user_op_if_irq_measure_if[ADT_IF_assms]:
  "do_user_op_if utf uc \<lbrace>\<lambda>s. P (irq_measure_if s)\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: do_user_op_if_def user_memory_update_def irq_measure_if_def
         | wps |wp dmo_wp | wpc)+
  done

lemma invoke_tcb_irq_state_inv[ADT_IF_assms]:
  "\<lbrace>(\<lambda>s. irq_state_inv st s) and domain_sep_inv False sta
                             and tcb_inv_wf tinv and K (irq_is_recurring irq st)\<rbrace>
   invoke_tcb tinv
   \<lbrace>\<lambda>_ s. irq_state_inv st s\<rbrace>, \<lbrace>\<lambda>_. irq_state_next st\<rbrace>"
  apply (case_tac tinv)
       apply ((wp hoare_vcg_if_lift  mapM_x_wp[OF _ subset_refl]
               | wpc
               | simp split del: if_split add: check_cap_at_def
               | clarsimp
               | wp (once) irq_state_inv_triv)+)[3]
    defer
    apply ((wp irq_state_inv_triv | simp)+)[2]
  (* just ThreadControl left *)
  apply (simp add: split_def cong: option.case_cong)
  by (wp hoare_vcg_all_lift_R hoare_vcg_all_lift hoare_vcg_const_imp_lift_R
         checked_cap_insert_domain_sep_inv cap_delete_deletes
         cap_delete_irq_state_inv[where st=st and sta=sta and irq=irq]
         cap_delete_irq_state_next[where st=st and sta=sta and irq=irq]
         cap_delete_valid_cap cap_delete_cte_at
      | wpc
      | simp add: emptyable_def tcb_cap_cases_def tcb_cap_valid_def
                  tcb_at_st_tcb_at option_update_thread_def
      | strengthen use_no_cap_to_obj_asid_strg
      | wp (once) irq_state_inv_triv hoare_drop_imps
      | clarsimp split: option.splits | intro impI conjI allI)+

lemma reset_untyped_cap_irq_state_inv[ADT_IF_assms]:
  "\<lbrace>irq_state_inv st and K (irq_is_recurring irq st)\<rbrace>
   reset_untyped_cap slot
   \<lbrace>\<lambda>y. irq_state_inv st\<rbrace>, \<lbrace>\<lambda>y. irq_state_next st\<rbrace>"
  apply (cases "irq_is_recurring irq st", simp_all)
  apply (simp add: reset_untyped_cap_def)
  apply (rule hoare_pre)
   apply (wp no_irq_clearMemory mapME_x_wp' hoare_vcg_const_imp_lift
             get_cap_wp preemption_point_irq_state_inv'[where irq=irq]
          | rule irq_state_inv_triv
          | simp add: unless_def
          | wp (once) dmo_wp)+
  done

crunch irq_state_of_state[ADT_IF_assms, wp]:
  handle_vm_fault, handle_hypervisor_fault "\<lambda>s. P (irq_state_of_state s)"
  (wp: crunch_wps dmo_wp simp: crunch_simps simp: getDFSR_def getFAR_def getIFSR_def)

text \<open>Not true of invoke_untyped any more.\<close>
crunch irq_state_of_state[ADT_IF_assms, wp]: create_cap "\<lambda>s. P (irq_state_of_state s)"
  (ignore: freeMemory
      wp: dmo_wp modify_wp crunch_wps
    simp: freeMemory_def storeWord_def clearMemory_def
          machine_op_lift_def machine_rest_lift_def mapM_x_defsym)

crunch irq_state_of_state[ADT_IF_assms, wp]: arch_invoke_irq_control "\<lambda>s. P (irq_state_of_state s)"
  (wp: dmo_wp crunch_wps simp: setIRQTrigger_def machine_op_lift_def machine_rest_lift_def)

end


global_interpretation ADT_IF_1?: ADT_IF_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact ADT_IF_assms)?)
qed

sublocale valid_initial_state \<subseteq> valid_initial_state?: ADT_valid_initial_state ..

hide_fact ADT_IF_1.do_user_op_silc_inv
requalify_facts ARM.do_user_op_silc_inv
declare do_user_op_silc_inv[wp]

end
