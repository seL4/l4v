(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory ADT_DR
imports Syscall_DR
begin

type_synonym cdl_cspace = "cdl_object_id \<Rightarrow> cdl_cap \<Rightarrow> bool"

type_synonym abstract_cspace = "word32 \<Rightarrow> cap \<Rightarrow> bool"
type_synonym caps_observable = "word32 \<times> abstract_cspace \<times> mode \<times> event option"

definition monadic_extract_cspace_aobs :: "'z::state_ext state \<Rightarrow> abstract_cspace"
where "monadic_extract_cspace_aobs s \<equiv> \<lambda>oid cap. 
  (\<exists>ref r.
    sum_case (\<lambda>x. None) (\<lambda>x. Some x) 
      (fst $ the_elem $  fst (lookup_slot_for_thread oid ref s)) = Some r \<and> caps_of_state s (fst r) = Some cap
  )"

definition monadic_extract_cspace_cdlobs :: "cdl_state \<Rightarrow> cdl_cspace"
where "monadic_extract_cspace_cdlobs s \<equiv> \<lambda>oid cap. 
  (\<exists>ref r.
    sum_case (\<lambda>x. None) (\<lambda>x. Some x) 
      (fst $ the_elem $ fst (lookup_slot oid ref s)) = Some r \<and> opt_cap r s = Some cap
  )"

definition
 "cdl_kernel_entry e \<equiv> do
   t \<leftarrow> gets cdl_current_thread;
   case t of Some idt \<Rightarrow> corrupt_tcb_intent idt | _ \<Rightarrow> return ();
   Syscall_D.call_kernel e
   od"

type_synonym cdl_mem_ghost_state = "obj_ref \<times> user_mem \<times> machine_no_mem"
  -- "idle thread location, memory, thread context, machine state"

definition
   kernel_call_cdl :: "event \<Rightarrow> (cdl_state \<times> cdl_mem_ghost_state)
                      \<times> (cdl_state \<times> cdl_mem_ghost_state) \<times> mode \<times> user_context \<times> user_context \<Rightarrow> bool"
where
  "kernel_call_cdl e \<equiv>
  {((s, gs), (s', gs'), m, tc, tc'). \<exists>r. (r,s')\<in> fst (cdl_kernel_entry e s)
        \<and> m = (if (cdl_current_thread s' = None) then IdleMode else UserMode)}"

definition Init_cdl :: "(cdl_state \<times> cdl_mem_ghost_state) global_state set"
where 
"Init_cdl \<equiv> \<Union>((cxt, s), m, e) \<in> Init_A.
    {(((undefined :: (ARMMachineTypes.register \<Rightarrow> word32)),(transform s,idle_thread s,user_mem s,no_mem_machine (machine_state s))), m, e)}"

definition Fin_A_with_caps :: "state global_state \<Rightarrow> caps_observable"
where "Fin_A_with_caps \<equiv> \<lambda>((cxt, s),m,e). (cur_thread s, monadic_extract_cspace_aobs s,m,e)"

definition Fin_cdl :: "( user_context \<times> (cdl_state \<times> cdl_mem_ghost_state)) \<times> mode \<times> event option \<Rightarrow> observable"
where "Fin_cdl \<equiv> \<lambda>((ucon,(s, (idt, umem, ms))), m,e).
  ((ucon, umem), ms,
     (case cdl_current_thread s of None \<Rightarrow> idt | Some (Standard a) \<Rightarrow> a),
     m, e)"

definition Fin_cdl_with_caps :: "((cdl_state \<times> cdl_mem_ghost_state) \<times> user_context) \<times> mode \<times> event option \<Rightarrow> caps_observable"
where
  "Fin_cdl_with_caps \<equiv> \<lambda>(((s, (idt, umem, ms)),ucon), m,e).
     (case cdl_current_thread s of None \<Rightarrow> idt | Some (Standard a) \<Rightarrow> a,
        (\<lambda>w cap. monadic_extract_cspace_cdlobs s (transform_obj_ref w) (transform_cap cap),m,e))"

definition ADT_cdl
where "ADT_cdl = \<lparr>Init=\<lambda>s. Init_cdl,Fin = Fin_cdl,Step = global_automaton kernel_call_cdl\<rparr>"

lemma trivial_cdl_inv:
  "ADT_cdl \<Turnstile> UNIV"
  by (clarsimp simp:invariant_holds_def)

lemma set_cxt_corrupt_intent_corres:
  "dcorres dc \<top> (valid_idle and not_idle_thread y)
    (corrupt_tcb_intent (transform_obj_ref y))
    (thread_set (tcb_context_update (\<lambda>_. tc)) y)"
  apply (rule dcorres_expand_pfx)
  apply (simp add:thread_set_def)
  apply (rule dcorres_absorb_gets_the)
  apply (rule corres_guard_imp[OF set_cxt_none_det_intent_corres])
    apply (clarsimp dest!:get_tcb_SomeD)
  apply simp+
done

lemma call_kernel_corres:
  "dcorres dc \<top> (\<lambda>s. invs s \<and> (e \<noteq> Interrupt \<longrightarrow> ct_running s \<and> ct_active s))
    (Syscall_D.call_kernel e)
    (Syscall_A.call_kernel e)"
  apply (simp add:Syscall_D.call_kernel_def Syscall_A.call_kernel_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ corres_split_handle,where r1=dc and f1 = dc and f'1 = dc])
      apply (rule corres_dummy_return_l)
       apply (rule corres_split[OF activate_thread_corres schedule_dcorres])
     apply wp
     apply (clarsimp simp:handle_pending_interrupts_def)
     apply (rule corres_split[OF _ get_active_irq_corres])
       apply (rule dcorres_when_r)
       apply clarsimp
      apply (rule handle_interrupt_corres)
      apply (rule corres_trivial)
     apply clarsimp
    apply wp
   apply clarsimp
   apply (rule hoare_drop_imp)
   apply wp
   apply (rule handle_event_corres)
   apply (wp|clarsimp)+
done

lemma dcorres_dummy_option_corrupt_tcb:
  "dcorres dc \<top> (\<lambda>s. cur_thread s =  cur_thread s' \<and> idle_thread s = idle_thread s' \<and> invs s)
          (option_case (return ()) corrupt_tcb_intent (transform_current_thread s'))
          (return x)"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:cdl_current_thread transform_current_thread_def)
  apply (rule corres_guard_imp[OF corres_corrupt_tcb_intent_return])
  apply (clarsimp simp: invs_def cur_tcb_def tcb_at_def)+
    apply (clarsimp simp:transform_def transform_objects_def transform_tcb_def
      transform_obj_ref_def transform_object_def dest!:get_tcb_SomeD)+
done

lemma dwp_thread_set_idle:
  "\<lbrace>\<lambda>ps. transform ps = cs \<and> thread = idle_thread ps\<rbrace> thread_set (tcb_context_update (\<lambda>_. rv)) thread
   \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (clarsimp simp:thread_set_def)
  apply (wp)
    apply (rule_tac Q = "\<lambda>s. transform s = cs \<and> thread = idle_thread s"
      in hoare_vcg_precond_imp)
    apply (clarsimp simp:valid_def mem_def set_object_def
      put_def get_def return_def bind_def)
    apply (clarsimp simp:transform_def transform_current_thread_def transform_objects_def)
  apply (assumption)
 apply wp
 apply simp
done

crunch idle[wp] : activate_thread "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps mapM_x_def_symmetric Retype_A.detype_def ignore:clearMemory)

crunch idle[wp] : "Schedule_A.schedule" "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps alternative_wp select_wp simp: crunch_simps  ignore:clearMemory)

lemmas cap_revoke_idle[wp] = cap_revoke_preservation[THEN validE_valid, OF cap_delete_idle]

lemma invoke_cnode_idle[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> invoke_cnode i \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps get_cap_wp cap_recycle_idle
             | simp split del: split_if | wpc)+
  done

crunch idle_inv[wp]: perform_invocation "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps cap_move_idle_thread ignore: without_preemption
        simp: crunch_simps unless_def)

crunch idle[wp]: kernel_entry "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps wp: crunch_wps syscall_valid select_wp
     ignore: Syscall_A.syscall getActiveIRQ resetTimer ackInterrupt
             getFAR getDFSR getIFSR)

lemma dcorres_cdl_kernel_entry:
  "dcorres dc \<top> (invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s))
        (cdl_kernel_entry e) (kernel_entry e tc)"
  apply (clarsimp simp:cdl_kernel_entry_def kernel_entry_def gets_def)
  apply (rule dcorres_absorb_get_l)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:cdl_current_thread transform_current_thread_def)+
    apply (intro conjI)
     apply (clarsimp simp:transform_current_thread_def not_idle_thread_def)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF _ set_cxt_corrupt_intent_corres])
          apply (rule corres_split_noop_rhs2)
             apply (rule corres_noop[where P=\<top> and P'=\<top>])
              apply simp
              apply wp
             apply simp
            apply (rule call_kernel_corres)
           apply wp
     apply (wp thread_set_invs_trivial)
       apply (clarsimp simp:tcb_cap_cases_def)+
    apply (wp thread_set_ct_running|clarsimp)+
    apply (simp add:ct_in_state_def)
    apply (wps)
      apply (wp thread_set_no_change_tcb_state)
    apply clarsimp+
   apply (simp add: ct_in_state_def invs_def valid_state_def)
  apply (clarsimp simp:cdl_current_thread transform_current_thread_def not_idle_thread_def)+
  apply (clarsimp simp:st_tcb_at_def obj_at_def)
  apply clarsimp
  apply (rule dcorres_symb_exec_r_strong)
    apply (rule corres_guard_imp)
    apply (rule corres_split_noop_rhs2)
       apply (rule corres_noop[where P=\<top> and P'=\<top>])
        apply simp
        apply wp
       apply simp
      apply (rule call_kernel_corres)
     apply (wp | simp)+
   apply (rule hoare_pre)
    apply (wp thread_set_invs_trivial thread_set_no_change_tcb_state
                 | simp add: ct_in_state_def | rule ball_tcb_cap_casesI
                 | wps)+
   apply (clarsimp simp: st_tcb_def2)
  apply (wp dwp_thread_set_idle | simp)+
done

lemma ct_idle_cur_idle:
  "\<lbrakk>invs s;ct_idle s\<rbrakk>\<Longrightarrow> cur_thread s = idle_thread s"
  by (clarsimp simp:ct_in_state_def invs_def valid_state_def only_idle_def)

lemma ct_running_cur_not_idle:
  "\<lbrakk>invs s;ct_running s\<rbrakk>\<Longrightarrow> cur_thread s \<noteq> idle_thread s"
  apply (rule ccontr)
  apply (clarsimp simp:ct_in_state_def invs_def
    valid_state_def valid_idle_def st_tcb_at_def obj_at_def)
done

lemma ct_running_eq_cdl_current_thread_None:
  "\<lbrakk> ct_running s \<or> ct_idle s; invs s \<rbrakk>
        \<Longrightarrow> ct_running s = (cdl_current_thread (transform s) \<noteq> None)"
  using ct_running_cur_not_idle[where s=s] ct_idle_cur_idle[where s=s]
  by (auto simp add: transform_current_thread_def transform_def)

lemma abstract_capdl_step_relation:
  "lift_state_relation
          {((s, idt, umem, ms), s').
           s = transform s' \<and>
           idle_thread s' = idt \<and>
           umem = user_mem s' \<and> ms = no_mem_machine (machine_state s')} \<inter>
         UNIV \<times> full_invs ;;;
         global_automaton kernel_call_A j
         \<subseteq> global_automaton kernel_call_cdl j ;;;
           lift_state_relation
            {((s, idt, umem, ms), s').
             s = transform s' \<and>
             idle_thread s' = idt \<and>
             umem = user_mem s' \<and> ms = no_mem_machine (machine_state s')}"
  apply (clarsimp simp:rel_semi_def relcomp_unfold full_invs_def)
  apply (drule lift_state_relationD)
  apply (clarsimp simp: global_automaton_def)
  apply (case_tac j)
      apply (clarsimp simp: global_automaton_def lift_state_relation_def)
      apply (rule rev_mp)
       apply (rule_tac e = e in dcorres_cdl_kernel_entry)
      apply (clarsimp simp:corres_underlying_def Ball_def)
      apply (drule spec, drule(1) mp[OF _ conjI])
       apply fastforce
      apply (clarsimp simp:kernel_call_A_def)
      apply (drule spec, drule spec, drule(1) mp)
      apply (clarsimp simp: kernel_call_cdl_def Pair_fst_snd_eq)
      apply (frule_tac P1="\<lambda>v. v = ?v'" in use_valid[OF _ kernel_entry_idle], rule refl)
      apply (frule use_valid[OF _ kernel_entry_invs], clarsimp+)
      apply (simp add: ct_running_eq_cdl_current_thread_None)
     apply (clarsimp simp:ADT_cdl_def global_automaton_def lift_state_relation_def
                          Pair_fst_snd_eq)+
  done

lemma LI_abstract_capdl:
  "LI ADT_cdl ADT_A (lift_state_relation {((s, (idt, umem, ms)), s').
           s = transform s' \<and> idle_thread s' = idt \<and> umem = user_mem s'
                 \<and> ms = no_mem_machine (machine_state s')})
   (UNIV \<times> full_invs)"
  apply (simp add:LI_def abstract_capdl_step_relation ADT_A_def ADT_cdl_def)
  apply (intro conjI)
   apply (simp add: lift_state_relation_def ADT_cdl_def
                    ADT_A_def Init_A_def Init_cdl_def)
   apply (simp add: Pair_fst_snd_eq)
  apply (simp add: full_invs_def)
  apply (clarsimp simp: ADT_A_def Fin_A_def Fin_cdl_def ADT_cdl_def
                        lift_state_relation_def)
  apply (clarsimp simp:cdl_current_thread transform_current_thread_def transform_obj_ref_def)
  done

theorem abstract_refine_capdl: 
  "ADT_A \<sqsubseteq> ADT_cdl"
  apply (rule sim_imp_refines)
  apply (rule L_invariantI)
    apply (rule trivial_cdl_inv)
   apply (rule akernel_invariant)
  apply (rule LI_abstract_capdl)
done

definition
  "ADT_A_caps = \<lparr>Init = \<lambda>s. Init_A, Fin = Fin_A_with_caps, Step = global_automaton kernel_call_A\<rparr>"

definition
  "ADT_cdl_caps = \<lparr>Init = \<lambda>s. Init_cdl, Fin = Fin_cdl_with_caps, Step = global_automaton kernel_call_cdl\<rparr>"

lemma akernel_caps_invariant:
  "ADT_A_caps \<Turnstile> full_invs"
  using akernel_invariant
  by (simp add: ADT_A_caps_def ADT_A_def invariant_holds_def)

locale caps_refinement =
assumes extraction: "\<And>ab. monadic_extract_cspace_aobs ab =
          (\<lambda>w cap.
              monadic_extract_cspace_cdlobs (transform ab) (Standard w)
               (transform_cap cap))"
begin

lemma caps_LI_abstract_capdl:
  "LI ADT_cdl_caps ADT_A_caps 
    (lift_state_relation {((s, (idt, umem, ms)), s').
         s = transform s' \<and> idle_thread s' = idt \<and> umem = user_mem s'
               \<and> ms = no_mem_machine (machine_state s')})
    (UNIV \<times> full_invs)"
  apply (simp add:LI_def abstract_capdl_step_relation ADT_A_caps_def ADT_cdl_caps_def)
  apply (intro conjI)
   apply (simp add: lift_state_relation_def
                    Init_A_def Init_cdl_def)
   apply (simp add: Pair_fst_snd_eq)
  apply (simp add: full_invs_def)
  apply (clarsimp simp: Fin_A_with_caps_def Fin_cdl_with_caps_def
                        lift_state_relation_def)
  apply (clarsimp simp:cdl_current_thread transform_current_thread_def
                       transform_obj_ref_def extraction)
  done

theorem caps_abstract_refine_capdl: 
  "ADT_A_caps \<sqsubseteq> ADT_cdl_caps"
  apply (rule sim_imp_refines)
  apply (rule L_invariantI[OF _ _ caps_LI_abstract_capdl])
   apply simp
  apply (rule akernel_caps_invariant)
  done

end

end
