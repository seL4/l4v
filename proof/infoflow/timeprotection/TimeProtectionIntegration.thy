(*
 * Copyright 2021, UNSW (ABN 57 195 873 179),
 * Copyright 2021, The University of Melbourne (ABN 84 002 705 224).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TimeProtectionIntegration
imports TimeProtection
  "InfoFlow.Noninterference" schedule_oracle
begin

type_synonym context_and_state = "user_context \<times> det_ext Structures_A.state"
type_synonym if_other_state    = "context_and_state \<times> sys_mode"

(* domain-switch monad? *)


locale integration_setup = 
  Arch +
  time_protection_hardware
    gentypes
    PSched +
  Noninterference_valid_initial_state _ _ _ _ initial_aag
  for gentypes :: "('fch \<times> 'fch_cachedness \<times> 'pch \<times> 'pch_cachedness \<times> 'l partition \<times> 'colour) itself"
  and initial_aag :: "'l subject_label PAS"
+ fixes time_per_tick :: time
  fixes slice_length_min :: time
  fixes timer_delay_max :: time
  fixes ta :: "if_other_state \<Rightarrow> vpaddr set"
  assumes timer_delay_lt_slice_length:
    "timer_delay_max < slice_length_min"
begin

(* get the list of (domain, tickcount) from the initial state *)
(* this system assumes that domain_list_internal won't change *)
definition dom_list_internal where
  "dom_list_internal \<equiv> domain_list_internal $ exst $ snd $ fst s0"

(* map dom_list_internal into a list of (domain, totaltime) by multiplying
   by time_per_tick *)
definition schedule_list where
  "schedule_list \<equiv> map (\<lambda>(d, ticks). (data_to_nat ticks * time_per_tick, d)) dom_list_internal"

interpretation sched_o:schedule_oracle_delayed _ schedule_list slice_length_min timer_delay_max
  apply unfold_locales
   (* we need to know that the domain list has some minimum time *)
   subgoal sorry
  (* we need to know that the domain list is never empty *)
  subgoal sorry

  subgoal sorry
  done

definition nlds where
  "nlds \<equiv> sched_o.next_delayed_start"

lemma nlds_in_future:
  "t < nlds t"
  apply (clarsimp simp:nlds_def sched_o.next_delayed_start_in_future)
  done

lemma nlds_flatsteps:
  "\<lbrakk>t \<le> t'; t' < nlds t\<rbrakk> \<Longrightarrow> nlds t' = nlds t"
  apply (clarsimp simp:nlds_def sched_o.next_delayed_start_flatsteps)
  done
                    
interpretation tphuwr:time_protection_hardware_uwr gentypes PSched 
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ part uwr nlds ta
  apply unfold_locales
   apply (simp add: schedIncludesCurrentDom)
  using uwr_equiv_rel apply blast
  done

abbreviation ma_uwr where "ma_uwr \<equiv> tphuwr.uwr"

(*
(* the definition used in infoflow *)
definition if_A where
  "if_A \<equiv> big_step_ADT_A_if utf"

definition if_s0 where
  "if_s0 \<equiv> s0"

definition if_current_domain :: "if_other_state \<Rightarrow> 'l partition" where
  "if_current_domain \<equiv> part"

definition if_uwr :: "'l partition \<Rightarrow> (if_other_state \<times> if_other_state) set" where
  "if_uwr d \<equiv> uwr d"

(* the definition used in infoflow *)
definition if_policy :: "('l partition \<times> 'l partition) set" where
  "if_policy \<equiv> policyFlows (pasPolicy initial_aag)"
 *)

end

locale integration =
  ii?:integration_setup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gentypes +
  ts?:trace_selector
    "TYPE((if_other_state \<times> ('fch, 'pch) TimeProtection.state) \<times> 'l partition \<times> trace \<times> vpaddr set)"
    "ii.part \<circ> fst" ma_uwr PSched "[]" "step_is_uwr_determined \<circ> fst" "step_is_publicly_determined \<circ> fst" select_trace 
  for gentypes :: "('fch \<times> 'fch_cachedness \<times> 'pch \<times> 'pch_cachedness \<times> 'l partition \<times> 'colour) itself"
  and select_trace and step_is_uwr_determined and step_is_publicly_determined
  
begin

(* what do we know
  we definitely have interrupted_modes of os.
  but that incluedes both
  - KernelEntry ev
  - KernelPreempt

  im not yet sure if i should be including KernelPreempt here. I don't think you can Preempt into a
  domainswitch, but i'm not certain how preempt works.

*)

definition is_timer_irq :: "det_ext Structures_A.state \<Rightarrow> bool" where
  "is_timer_irq s \<equiv> let irq = irq_oracle (Suc (irq_state_of_state s)) in
                     \<exists>s'. (Some irq, s') \<in> fst (do_machine_op (getActiveIRQ False) s)
                           \<and> interrupt_states s irq = IRQTimer"

definition domain_time_zero :: "if_other_state \<Rightarrow> bool" where
  "domain_time_zero os \<equiv> domain_time_internal (exst (snd (fst os))) = 1"

definition will_domain_switch :: "if_other_state \<Rightarrow> bool" where
  "will_domain_switch os \<equiv> interrupted_modes (snd os)
                         \<and> is_timer_irq (snd (fst os))
                         \<and> domain_time_zero os"

lemma ex_eq:
  "(\<exists>y. (P y = P' y)) \<Longrightarrow>(\<exists>x. P x) = (\<exists>x. P' x)"
  oops

lemma will_domain_switch_from_uwr:
  "uwr2 os PSched ot \<Longrightarrow>
  will_domain_switch ot = will_domain_switch os"
  unfolding uwr_def
  apply (clarsimp simp: will_domain_switch_def uwr_def sameFor_def sameFor_scheduler_def)
  apply (case_tac bc; case_tac ba; clarsimp split:event.splits)
    
    apply (prop_tac "interrupt_states (internal_state_if ((aa, bb), KernelEntry Interrupt))
                   = interrupt_states (internal_state_if ((a , b ), KernelEntry Interrupt))")
     apply simp 
     subgoal sorry
  oops

definition can_split_four_ways where
  "can_split_four_ways s1 s5 oldclean dirty gadget newclean \<equiv>
   \<exists> s2 s3 s4. s2 \<in> oldclean s1 \<and> s3 \<in> dirty s2 \<and> s4 \<in> gadget s3 \<and> s4 \<in> newclean s4"

lemma step_bigstepR:
  "(s, s') \<in> Step () \<Longrightarrow>
  big_step_R s s'"
  apply (drule big_Step2, rule small_step_to_big_step; simp)
  done

term global_automaton_if
term ADT_A_if

find_theorems name:obs_det

lemma big_step_Init:
  "(s1, s3) \<in> Step () \<Longrightarrow>
  Init (ADT_A_if utf) s1 = {s1}"
  apply (clarsimp simp:system.Step_def execution_def big_step_ADT_A_if_def
    big_step_adt_def Fin_ADT_if)
  apply (prop_tac "s1 \<in> full_invs_if")
   apply (smt (verit, best) ImageE Init_ADT_if IntE empty_iff foldl.simps(1)
     foldl.simps(2) insert_iff steps_def)
  apply (prop_tac "step_restrict s1")
   apply (metis (no_types, lifting) ADT_A_if_def IntE Step_big_step_ADT_A_if big_step_ADT_A_if_def
     big_step_adt_def data_type.simps(1) mem_Collect_eq singletonD steps_eq_Run)
  apply (clarsimp simp: Init_ADT_if)
  done


inductive_set sub_big_steps_alt
  :: "('istate,'estate,'event) data_type \<Rightarrow> ('istate \<Rightarrow> bool) \<Rightarrow> ('istate \<times> 'istate \<times> 'event list) set"
  for A :: "('istate,'estate,'event) data_type" and J :: "('istate \<Rightarrow> bool)"
where
  nil: "\<lbrakk>evlist = []; s2 = s1; \<not> J s1\<rbrakk> \<Longrightarrow>  (s1, s2, evlist) \<in> sub_big_steps_alt A J" |
  step: "\<lbrakk>evlist = [e] @ evlist'; (s2, s3, evlist') \<in> sub_big_steps_alt A J;
          (s1, s2) \<in> data_type.Step A e; \<not> J s2\<rbrakk> \<Longrightarrow> (s1, s3, evlist) \<in> sub_big_steps_alt A J"
                                          


lemma sub_big_steps_sub_big_steps_alt_aux:
 " (s2, es1) \<in> sub_big_steps A R s1 \<Longrightarrow>    
   (s2, s3, es2) \<in> sub_big_steps_alt A (\<lambda> b. R s1 b) \<Longrightarrow>
   (s1, s3, es1 @ es2) \<in> sub_big_steps_alt A (\<lambda> b. R s1 b)"
  apply (induct s2 es1 arbitrary:s3 es2 rule:sub_big_steps.induct)
   apply clarsimp
  apply clarsimp
  apply (simp add: sub_big_steps_alt.step)
  done



lemma sub_big_steps_sub_big_steps_alt:
 "(s2, es1) \<in> sub_big_steps A R s1 \<Longrightarrow>    
  (s1, s2, es1) \<in> sub_big_steps_alt A (\<lambda> b. R s1 b)"
  by (metis (mono_tags) append_Nil2 sub_big_steps_Run sub_big_steps_alt.nil sub_big_steps_sub_big_steps_alt_aux)

(*
lemma big_stepsD:
  "(s,t) \<in> big_steps A R exmap ev
   \<Longrightarrow> \<exists>s' as a. (s',as) \<in> sub_big_steps A R s \<and> (s',t) \<in> Step A a \<and> R s t \<and> ev = exmap (as @ [a])"
  apply (erule big_steps.induct)
  apply blast
  done
*)

term global_automaton_if

lemma step_to_KernelExit:
  "(s1, s2) \<in> data_type.Step (ADT_A_if utf) () \<Longrightarrow>
  snd s2 = KernelExit \<Longrightarrow>
  \<exists>b. snd s1 = KernelSchedule b"
  apply (cases s2, clarsimp)
  apply (clarsimp simp: ADT_A_if_def global_automaton_if_def)
  apply (erule disjE; clarsimp)
  apply (clarsimp simp: kernel_exit_A_if_def split:if_splits)
  done

lemma schedule_step':
  assumes schedule:
    "\<And>r. \<lbrakk> (r,internal_state_if s') \<in> fst (schedule_if (user_context_of s) (internal_state_if s));
            sys_mode_of s' = KernelExit; r = user_context_of s; r = user_context_of s' \<rbrakk>
            \<Longrightarrow> P"
  shows
    "\<lbrakk> (sys_mode_of s') = KernelExit; (s,s') \<in> data_type.Step (ADT_A_if utf) () \<rbrakk>
       \<Longrightarrow> P"
  apply (frule step_to_KernelExit, simp add: sys_mode_of_def)
  apply (insert schedule)
  apply (metis schedule_step sys_mode_of_def)
  done

lemma step_to_KernelSchedule:
  "(s1, s2) \<in> data_type.Step (ADT_A_if utf) () \<Longrightarrow>
  snd s2 = KernelSchedule True \<Longrightarrow>
  interrupted_modes (snd s1)"
  apply (cases s2, clarsimp)
  apply (clarsimp simp: ADT_A_if_def global_automaton_if_def)
  apply (elim disjE; clarsimp)
   apply (clarsimp simp: kernel_exit_A_if_def split:if_splits)
  done

lemma interrupt_step':
  assumes interrupt:
    "\<And>r. (r,internal_state_if s')
            \<in> fst (kernel_entry_if Interrupt (user_context_of s) (internal_state_if s))
          \<Longrightarrow> sys_mode_of s = KernelEntry Interrupt \<Longrightarrow> (sys_mode_of s' = KernelSchedule True)
          \<Longrightarrow> snd r = user_context_of s \<Longrightarrow> snd r = user_context_of s'
          \<Longrightarrow> cur_domain (internal_state_if s') = cur_domain (internal_state_if s)
          \<Longrightarrow> P"
  assumes preemption:
    "\<And>r. (r,internal_state_if s')
            \<in> fst (handle_preemption_if (user_context_of s) (internal_state_if s))
          \<Longrightarrow> sys_mode_of s = KernelPreempted \<Longrightarrow> sys_mode_of s' = KernelSchedule True
          \<Longrightarrow> r = user_context_of s \<Longrightarrow> r = user_context_of s'
          \<Longrightarrow> cur_domain (internal_state_if s') = cur_domain (internal_state_if s)
          \<Longrightarrow> P"
  shows "\<lbrakk> interrupted_modes (sys_mode_of s); (s,s') \<in> data_type.Step (ADT_A_if utf) () \<rbrakk> \<Longrightarrow> P"
  apply (insert interrupt preemption)
  oops

lemma interrupted_modes_PSched:
 "interrupted_modes (snd s1) \<Longrightarrow>
  part s1 = PSched"
  apply (cases s1; clarsimp)
  apply (case_tac ba; clarsimp simp:part_def)
  done

lemma kernel_entry_if_Inr:
  "\<lbrace>\<top>\<rbrace> kernel_entry_if Interrupt ab \<lbrace>\<lambda>r s. fst r=Inr ()\<rbrace>"
  apply (wpsimp simp: kernel_entry_if_def liftE_def)
  done

lemma domainswitch_two_paths:
  "(s1, s3) \<in> Step () \<Longrightarrow>
  interrupted_modes (snd s1) \<Longrightarrow>
  \<exists>s2. (s2, (), fst s3) \<in> kernel_schedule_if \<and>
       ((fst s1, (), s2) \<in> kernel_handle_preemption_if
      \<or> (fst s1, False, s2) \<in> kernel_call_A_if Interrupt)"
  apply (drule big_Step2)
  apply (rule_tac s=s1 and s''=s3 in scheduler_steps)
    apply assumption
   apply (rule interrupted_modes_PSched; simp)
  apply (rename_tac s2, thin_tac "(s1, s3) \<in> _")
  apply (rule_tac x="fst s2" in exI)
  apply (intro conjI)

   \<comment> \<open>the second step (schedule)\<close>
   apply (rule schedule_step; simp)
   apply (clarsimp simp: kernel_schedule_if_def user_context_of_def)

  apply (rule_tac s=s1 and s'=s2 in interrupt_step; simp add:sys_mode_of_def)
   \<comment> \<open>the first step (kernel call, interrupt)\<close>
   apply (intro disjI2)
   apply (cases s1; clarsimp)
   apply (clarsimp simp: kernel_call_A_if_def)
   apply (rule_tac x=False in exI; simp)
   using use_valid kernel_entry_if_Inr apply fastforce

  \<comment> \<open>the first step (kernel preempted)\<close>
  apply (intro disjI1)
  apply (cases s1; clarsimp)
  apply (clarsimp simp: kernel_handle_preemption_if_def)
  done

lemma kernel_handle_preemption_if_handle_preemption_if:
  "((fst s1, (), s2) \<in> kernel_handle_preemption_if)
  = (s2 \<in> fst (handle_preemption_if (fst (fst s1)) (snd (fst s1))))"
  apply (clarsimp simp:kernel_handle_preemption_if_def split:prod.splits)
  done

crunches arch_mask_irq_signal
  for scheduler_action: "\<lambda>s. P (scheduler_action s)"

definition
  handle_interrupt_IRQTimer where
 "handle_interrupt_IRQTimer \<equiv>
   do
     modify (\<lambda>s. s\<lparr>machine_state :=
       machine_state s \<lparr>irq_state := irq_state_of_state s + 1\<rparr>\<rparr>);
     do_extended_op timer_tick;
     do_machine_op resetTimer
   od"

lemma weirdthing:
  "\<lbrakk>A; B\<rbrakk> \<Longrightarrow> A \<and> B"
  by simp

find_theorems getActiveIRQ name:wp

thm dmo_getActiveIRQ_wp

find_theorems name:gets

definition irq_at' :: "nat \<Rightarrow> irq option" where
  "irq_at' pos \<equiv> Some (irq_oracle pos)"

definition Psame :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "Psame a b = (\<lambda>a' b'. a'=a \<and> b'=b)"

lemma dmo_getActiveIRQ_timer:
  "\<lbrace>\<lambda>s. is_timer_irq s \<and> P (Some (irq_oracle (irq_state (machine_state s)+1)))
  (s\<lparr>machine_state := (machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>)\<rparr>)\<rbrace>
     do_machine_op (getActiveIRQ True)
   \<lbrace>\<lambda>r s. P r s \<and> interrupt_states s (the r) = IRQTimer\<rbrace>"
  apply (clarsimp simp: getActiveIRQ_no_non_kernel_IRQs)
  apply (rule hoare_weaken_pre)
  apply (rule dmo_getActiveIRQ_wp)
  apply (clarsimp simp: is_timer_irq_def check_active_irq_A_if_def check_active_irq_if_def)
  apply (clarsimp simp: bind_def do_machine_op_def return_def)
  apply (clarsimp simp: gets_def bind_def return_def)
  apply (clarsimp simp: modify_def bind_def get_def put_def select_f_def)
  apply (clarsimp simp: getActiveIRQ_def bind_def gets_def get_def return_def modify_def put_def)
  apply (clarsimp simp:irq_at_def Let_def)
  apply (clarsimp split:if_splits)
   apply (simp add: in_monad(12))
  (* apply (clarsimp simp:return_def) *)
  done
  
lemma dmo_getActiveIRQ_timer_withoutextras:
  "\<lbrace>\<lambda>s. is_timer_irq s \<and> P (Some (irq_oracle (irq_state (machine_state s)+1)))
  (s\<lparr>machine_state := (machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>)\<rparr>)\<rbrace>
     do_machine_op (getActiveIRQ True)
   \<lbrace>P\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule dmo_getActiveIRQ_timer)
  apply simp
  done


lemma dmo_getActiveIRQ_timer2:
  "\<lbrace>\<lambda>s. is_timer_irq s\<rbrace>
     do_machine_op (getActiveIRQ True)
   \<lbrace>\<lambda>r s. r = Some (irq_oracle (irq_state (machine_state s)))
      \<and> interrupt_states s (the r) = IRQTimer\<rbrace>"
  apply (clarsimp simp: getActiveIRQ_no_non_kernel_IRQs)
  apply (rule hoare_weaken_pre)
  apply (rule dmo_getActiveIRQ_wp)
  apply (clarsimp simp: is_timer_irq_def check_active_irq_A_if_def check_active_irq_if_def)
  apply (clarsimp simp: bind_def do_machine_op_def return_def)
  apply (clarsimp simp: gets_def bind_def return_def)
  apply (clarsimp simp: modify_def bind_def get_def put_def select_f_def)
  apply (clarsimp simp: getActiveIRQ_def bind_def gets_def get_def return_def modify_def put_def)
  apply (clarsimp simp:irq_at_def Let_def)
  apply (clarsimp split:if_splits)
   apply (simp add: in_monad(12))
  (* apply (clarsimp simp:return_def) *)
  done

find_theorems monadic_rewrite name:"wp"

find_theorems getActiveIRQ valid

thm dmo_getActiveIRQ_wp



term "do_machine_op (getActiveIRQ True)"

(*
lemma dmo_getActiveIRQ_wp[CNode_IF_assms]:
  "\<lbrace>\<lambda>s. is_timer_irq s \<and> (P (irq_at' (irq_state (machine_state s) + 1))
          (s\<lparr>machine_state := (machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>)\<rparr>))\<rbrace>
   do_machine_op (getActiveIRQ b) :: user_context \<times> det_ext Structures_A.state
   \<lbrace>P\<rbrace>"
  apply (simp add: do_machine_op_def getActiveIRQ_def non_kernel_IRQs_def)
  apply (wp modify_wp | wpc)+
  apply clarsimp
  apply (erule use_valid)
   apply (wp modify_wp)
  apply (auto simp: irq_at_def Let_def split: if_splits)
  done
*)

lemma set_ext:
  "(\<forall>x. (x \<in> S) = (x \<in> T)) \<Longrightarrow> (S = T)"
  apply blast
  done

lemma pair_eq:
  "(fst f = fst g) \<Longrightarrow> snd f = snd g \<Longrightarrow> (f = g)"
  by (simp add: prod.expand)

lemma ex_eq:
  "P = Q \<Longrightarrow> ((\<exists>x. P) = (\<exists>x. Q))"
  by simp


lemma det_empty_fail:
  "det f \<Longrightarrow> empty_fail f"
  apply (clarsimp simp:empty_fail_def det_def)
  by (metis insert_not_empty prod.sel(1))

lemma det_no_fail:
  "det f \<Longrightarrow> no_fail \<top> f"
  apply (clarsimp simp:no_fail_def det_def)
  by (metis prod.sel(2))

lemma weak_pre_to_strong_post:
  "\<forall>P. \<lbrace>\<lambda>s. P (Pr s) (Ps s)\<rbrace> f \<lbrace>P\<rbrace> \<Longrightarrow>
  \<forall>s. \<lbrace>\<lambda>s'. s'=s\<rbrace> f \<lbrace>\<lambda>r' s'. r'=Pr s \<and> s'=Ps s\<rbrace>"
  by (smt (verit, best) hoare_strengthen_pre_via_assert_forward)

lemma strong_post_elim:
  "empty_fail f \<Longrightarrow>
   no_fail \<top> f \<Longrightarrow>
    (\<forall>s. \<lbrace>\<lambda>s'. s'=s\<rbrace> f \<lbrace>\<lambda>r' s'. r'=Pr s \<and> s'=Ps s\<rbrace>) \<Longrightarrow>
    f = 
    (do s \<leftarrow> get; modify Ps; return (Pr s) od)"
  apply (rule ext)
  apply (clarsimp simp: valid_def)
  apply (drule_tac x=x in spec)
  apply (clarsimp simp:exec_get exec_modify)
  apply (clarsimp simp:return_def)
  apply (rule pair_eq; clarsimp)
   apply (rule set_ext; clarsimp)
   apply (case_tac "((a, b) \<in> fst (f x))"; clarsimp)
    apply (drule_tac x="(a, b)" in bspec, assumption)
    apply clarsimp
   apply (clarsimp simp: empty_fail_def no_fail_def)
   apply fastforce
  apply (clarsimp simp:no_fail_def)
  done

lemma weak_pre_elim:
  "empty_fail f \<Longrightarrow>
   no_fail \<top> f \<Longrightarrow>
    (\<forall>P. \<lbrace>\<lambda>s. P (Pr s) (Ps s)\<rbrace> f \<lbrace>P\<rbrace>) \<Longrightarrow>
    f = 
    (do s \<leftarrow> get; modify Ps; return (Pr s) od)"
  apply (drule weak_pre_to_strong_post)
  apply (erule strong_post_elim; simp)
  done

lemma weak_pre_elim_P:
  "empty_fail f \<Longrightarrow>
   no_fail \<top> f \<Longrightarrow>
    (\<forall>P. \<lbrace>\<lambda>s.(P' s \<and>  P (Pr s) (Ps s))\<rbrace> f \<lbrace>P\<rbrace>) \<Longrightarrow>
    P' s' \<Longrightarrow>
    f s' = 
    (do s \<leftarrow> get; modify Ps; return (Pr s) od) s'"
  apply (clarsimp simp: valid_def)
  apply (clarsimp simp:exec_get exec_modify)
  apply (clarsimp simp:return_def)
  apply (drule_tac x="\<lambda>r s. r=Pr s' \<and> s=Ps s'" in spec)
  apply (drule_tac x=s' in spec)
  apply (rule pair_eq; clarsimp)
   apply (rule set_ext; clarsimp)
   apply (case_tac "((a, b) \<in> fst (f s'))"; clarsimp)
    apply (drule_tac x="(a, b)" in bspec, assumption)
    apply clarsimp
   apply (clarsimp simp: empty_fail_def no_fail_def)
   apply fastforce
  apply (clarsimp simp:no_fail_def)
  done

lemma weak_pre_rewrite_P:
  "empty_fail f \<Longrightarrow>
   no_fail \<top> f \<Longrightarrow>
    (\<forall>P. \<lbrace>\<lambda>s.(P' s \<and>  P (Pr s) (Ps s))\<rbrace> f \<lbrace>P\<rbrace>) \<Longrightarrow>
    monadic_rewrite E F
      P'
      f
      (do z \<leftarrow> get; modify Ps; return (Pr z) od)"
  apply (clarsimp simp: monadic_rewrite_def)
  apply (drule(3) weak_pre_elim_P)
  apply simp
  done

lemma rewrite_return_bind:
  "monadic_rewrite E F
      P
      (do z \<leftarrow> f1; f2 z; return (f3 z) od >>= g)
      (do z \<leftarrow> f1; f2 z; g (f3 z) od)"
  apply (clarsimp simp: monadic_rewrite_def)
  apply (smt (verit, ccfv_SIG) NonDetMonad.bind_assoc arg_cong_bind1
    let_into_return set_eq_subset)
  done

lemma weak_pre_rewrite_bind_aux:
  "empty_fail f \<Longrightarrow>
   no_fail \<top> f \<Longrightarrow>
    (\<forall>P. \<lbrace>\<lambda>s.(P' s \<and>  P (Pr s) (Ps s))\<rbrace> f \<lbrace>P\<rbrace>) \<Longrightarrow>
    monadic_rewrite E F
      P'
      (f >>= g)
      (do z \<leftarrow> get; modify Ps; return (Pr z) od >>= g)"
  apply (rule monadic_rewrite_bind_head)
  apply (rule weak_pre_rewrite_P; simp)
  done

lemma weak_pre_rewrite_bind:
  "empty_fail f \<Longrightarrow>
   no_fail \<top> f \<Longrightarrow>
    (\<forall>P. \<lbrace>\<lambda>s.(P' s \<and>  P (Pr s) (Ps s))\<rbrace> f \<lbrace>P\<rbrace>) \<Longrightarrow>
    monadic_rewrite E F
      P'
      (f >>= g)
      (do z \<leftarrow> get; modify Ps; g (Pr z) od)"
  apply (rule monadic_rewrite_imp)
  apply (rule monadic_rewrite_trans)
  apply (rule weak_pre_rewrite_bind_aux, assumption+)
  apply (rule rewrite_return_bind)
  apply simp
  done


(* not needed i guess. they're true though
lemma and_refl [simp]:
  "(P and P) = P"
  by (simp add: pred_conj_def)

lemma no_fail_bind_simple:
  assumes f: "no_fail P f"
  assumes g: "\<And>rv. no_fail (R rv) (g rv)"
  assumes v: "\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>"
  shows "no_fail P (f >>= (\<lambda>rv. g rv))"
  apply (insert f g v)
  apply (rule no_fail_bind [where P=P and Q=P and R=R, simplified]; assumption)
  done

lemma no_fail_bind_simple_top:
  assumes f: "no_fail P f"
  assumes g: "\<And>rv. no_fail \<top> (g rv)"
  shows "no_fail P (f >>= (\<lambda>rv. g rv))"
  apply (insert f g)
  apply (rule no_fail_bind [where Q=\<top>, simplified])
    apply assumption
   apply assumption
  apply (clarsimp simp:valid_def)
  done
*)

lemma do_machine_op_no_fail [wp_unsafe]:
  "no_fail Q f \<Longrightarrow>
  (\<forall>s. P s \<longrightarrow> Q (machine_state s)) \<Longrightarrow>
  no_fail P (do_machine_op f)"
  apply (clarsimp simp:do_machine_op_def)
  apply wpsimp
  apply (clarsimp simp: no_fail_def)
  done

lemma dmo_getActiveIRQ_no_fail:
  "no_fail \<top> (do_machine_op (getActiveIRQ True))"
  apply (wpsimp wp:do_machine_op_no_fail)
  done

lemma monadic_rewrite_dmo_getActiveIRQ:
  "monadic_rewrite E F
    is_timer_irq
    (do_machine_op (getActiveIRQ True))
    (do s \<leftarrow> get;
       modify (\<lambda>s. s\<lparr>machine_state := machine_state s\<lparr>irq_state := irq_state_of_state s + 1\<rparr>\<rparr>);
       return (Some (irq_oracle (irq_state_of_state s + 1))) od)"
  apply (rule weak_pre_rewrite_P)
    apply (rule do_machine_op_empty_fail, rule getActiveIRQ_empty_fail)
   apply (rule dmo_getActiveIRQ_no_fail)
  using dmo_getActiveIRQ_timer_withoutextras apply clarsimp
  done

lemma monadic_rewrite_dmo_getActiveIRQ_bind:
  "monadic_rewrite E F
    is_timer_irq
    (do_machine_op (getActiveIRQ True) >>= g)
    (do s \<leftarrow> get;
       modify (\<lambda>s. s\<lparr>machine_state := machine_state s\<lparr>irq_state := irq_state_of_state s + 1\<rparr>\<rparr>);
       g (Some (irq_oracle (irq_state_of_state s + 1))) od)"
  apply (rule weak_pre_rewrite_bind)
    apply (rule do_machine_op_empty_fail, rule getActiveIRQ_empty_fail)
   apply (rule dmo_getActiveIRQ_no_fail)
  using dmo_getActiveIRQ_timer_withoutextras apply clarsimp
  done

lemma pred_conj_refl:
  "(P and P) = P"
  by (simp add: pred_conj_def)


lemma bind_assoc_sym:
  "do a \<leftarrow> f; b \<leftarrow> g a; h b od = 
  (do a \<leftarrow> f; g a od) >>= h"
  by (simp add: bind_subst_lift)

lemma get_modify_use_reorder:
  "(\<forall>s. Pr' (Ps s) = Pr s) \<Longrightarrow>
  (do z <- get;
     y \<leftarrow> modify Ps;
     handle_interrupt (Pr z)
   od) = 
  (do y \<leftarrow> modify Ps;
     z <- get;
     handle_interrupt (Pr' z)
   od)"
  apply (rule ext)
  apply (clarsimp simp: exec_get exec_modify)
  done

lemma monadic_rewrite_remove_get:
  "monadic_rewrite E F
    P
    (do s \<leftarrow> get; f od)
    f"
  by (simp add: exec_get monadic_rewrite_refl3)

lemma monadic_rewrite_remove_used_get:
  "(\<forall>s. Ps \<longrightarrow> Q (e s)) \<Longrightarrow>
  Q r \<Longrightarrow>
  monadic_rewrite E F
    P
    f
    (g r) \<Longrightarrow>
  monadic_rewrite E F
    P
    f
    (do s \<leftarrow> get; g (e s) od)"
  oops

lemma sdsdfsdfdd:
  "(do s \<leftarrow> get; f s od) =
    (\<lambda>s. f s s)"
  by (simp add: exec_get monadic_rewrite_refl3 monadic_rewrite_to_eq)

lemma monadic_rewrite_double_get:
  "monadic_rewrite E F P (do s \<leftarrow> get; s' \<leftarrow> get; m s s' od) (do s \<leftarrow> get; m s s od)"
  by (simp add: exec_get monadic_rewrite_refl3)

lemma monadic_rewrite_trans_simple:
  "\<lbrakk> monadic_rewrite F E P f g; monadic_rewrite F E P g h \<rbrakk>
      \<Longrightarrow> monadic_rewrite F E P f h"
  by (auto simp add: monadic_rewrite_def)

thm monadic_rewrite_bind_tail
lemma monadic_rewrite_bind_tail_result:
  "\<lbrakk>(\<And>x. Q x \<longrightarrow> monadic_rewrite F E P (h x) (j x)); \<lbrace>R\<rbrace> f \<lbrace>\<lambda>r s. Q r \<and> P s\<rbrace>\<rbrakk> \<Longrightarrow>
  monadic_rewrite F E R (f >>= h) (f >>= j)"
  by (smt (z3) monadic_rewrite_bind_tail monadic_rewrite_imp monadic_rewrite_refl3)

lemma monadic_rewrite_bind_get:
  "\<lbrakk>(\<And>x. P x \<longrightarrow> monadic_rewrite F E P (h x) (j x))\<rbrakk> \<Longrightarrow>
  monadic_rewrite F E P (get >>= h) (get >>= j)"
  apply (erule monadic_rewrite_bind_tail_result)
  apply (clarsimp simp:valid_def get_def)
  done

thm monadic_rewrite_name_pre

thm monadic_rewrite_refl
lemma monadic_rewrite_refl2:
  "monadic_rewrite F E P f f"
  by (simp add: monadic_rewrite_def)

lemma sdsdf:
  "monadic_rewrite E F
    is_timer_irq
    (handle_preemption_if tc)
    (do handle_interrupt_IRQTimer; return tc od)"
  apply (clarsimp simp: handle_preemption_if_def)
  (* get rid of the "return tc" at the end *)
  apply (subst bind_assoc_sym)
  apply (rule monadic_rewrite_bind_head)

  apply (rule monadic_rewrite_trans_simple)
   apply (rule monadic_rewrite_dmo_getActiveIRQ_bind)
  apply clarsimp

  apply (subst get_modify_use_reorder [where Pr'="\<lambda>s. irq_oracle (irq_state_of_state s)"])
   apply clarsimp

  apply (clarsimp simp: handle_interrupt_IRQTimer_def)
  
  apply (rule monadic_rewrite_bind_tail [
    where Q="\<lambda>r s. interrupt_states s (irq_oracle (irq_state_of_state s)) = IRQTimer"])
   defer
   apply (clarsimp simp: valid_def is_timer_irq_def Let_def)
   apply (clarsimp simp: simpler_modify_def)  
  apply clarsimp
  
  (*
  apply (rule monadic_rewrite_imp)
  apply (rule monadic_rewrite_trans)
  apply (rule monadic_rewrite_remove_used_get [where g=handle_interrupt])
  *)


  find_theorems monadic_rewrite If

  apply (clarsimp simp: handle_interrupt_def)
  apply (prop_tac "\<forall>z. maxIRQ < irq_oracle (irq_state_of_state z) = False")
   using irq_oracle_max_irq word_not_le apply blast
  apply clarsimp
  apply (thin_tac _)


  apply (clarsimp simp: get_irq_state_def gets_def)

  (* turn the two "get"s into one *)
  apply (rule monadic_rewrite_trans_simple)
  apply (rule monadic_rewrite_double_get)

  apply (rule monadic_rewrite_trans_simple)
   apply (rule monadic_rewrite_bind_get)
   apply clarsimp
   apply (rule monadic_rewrite_refl2)
  apply (clarsimp simp:ackInterrupt_def)

  find_theorems monadic_rewrite name:gen_asm

  apply (rule monadic_rewrite_trans_simple)
   apply (rule monadic_rewrite_remove_get)
  apply (rule monadic_rewrite_refl2)
  done
  
  
  
  



lemma handle_interrupt_for_IRQTimer_aux:
  "is_timer_irq (tc, s) \<Longrightarrow>
  handle_preemption_if tc s = (do handle_interrupt_IRQTimer; return tc od) s"
  apply (clarsimp simp: handle_preemption_if_def)
  apply (clarsimp simp: getActiveIRQ_def do_machine_op_def)
  oops

lemma handle_interrupt_for_IRQTimer:
  "\<lbrace>\<lambda>s. is_timer_irq (tc, s)\<rbrace> do handle_interrupt_IRQTimer; return tc od \<lbrace>Q\<rbrace> \<Longrightarrow>
  \<lbrace>\<lambda>s. is_timer_irq (tc, s)\<rbrace> handle_preemption_if tc \<lbrace>Q\<rbrace>"
  apply (wpsimp simp: handle_preemption_if_def)
    prefer 2
    apply (rule hoare_strengthen_post, rule dmo_getActiveIRQ_timer)
    apply clarsimp

  apply (clarsimp simp:valid_def)
  apply (drule_tac x=s in spec)
  using handle_interrupt_for_IRQTimer_aux apply fastforce
  done

lemma
  "\<lbrace>\<lambda>s. is_timer_irq (tc, s)\<rbrace>
    handle_preemption_if tc
  \<lbrace>\<lambda>r s. scheduler_action s = choose_new_thread\<rbrace>"
  apply (rule handle_interrupt_for_IRQTimer)
  apply (wpsimp simp: handle_interrupt_IRQTimer_def)
  (* more work to do here *)
  
  

lemma first_bit_whatever_meow:
  "(fst s1, (), s2) \<in> kernel_handle_preemption_if
 \<or> (fst s1, False, s2) \<in> kernel_call_A_if Interrupt \<Longrightarrow>
  scheduler_action (snd s2) = choose_new_thread"
  apply (elim disjE)
  apply (clarsimp simp: kernel_handle_preemption_if_handle_preemption_if)
  apply (cases s1; clarsimp)

lemma more_splits_test:
  "(s1, (), s3) \<in> kernel_schedule_if \<Longrightarrow>
   s1 = s3"
  apply (cases s1)
  pply (clarsimp simp: kernel_schedule_if_def schedule_if_def)


lemma domainswitch_splits_four_ways:
  "(s1, s5) \<in> Step () \<Longrightarrow>
  will_domain_switch s1 \<Longrightarrow>
  can_split_four_ways s1 s5 a b c d"
  apply (frule step_bigstepR)
  apply (clarsimp simp: big_step_R_def)
  apply (erule disjE)
   apply (clarsimp simp:will_domain_switch_def)
  apply clarsimp

  apply (drule(1) domainswitch_two_paths, clarsimp)
  apply (rename_tac s2a s2b)
  apply (simp add: kernel_handle_preemption_if_handle_preemption_if)

  (* 
     From big_step_R, we know that each step is either some user sequence,
     or we are starting from the scheduler modes:
     - KernelEntry Interrupt, or
     - KernelPreempted

     For each of these options, there are exactly TWO small steps that make up the big step,
     and the second is identical. In the first step we take either:
     - kernel_callf Interrupt
     - preemptionf
     ... and then we always perform `schedulef`.

     We should make some lemmas that break this down for us so we can reason about those
     individual steps.

     I am still kinda trying to figure out if preemption can ever cause a (domain) schedule switch,
     and if not, how do I prove this?
 *)
  apply (clarsimp simp:interrupted_modes_def)

  apply (clarsimp simp: Step_def big_step_ADT_A_if_def)

  apply (clarsimp simp:Step_def big_step_ADT_A_if_def system.Step_def big_step_adt_def
    )

interpretation ma?:time_protection_system PSched fch_lookup fch_read_impact fch_write_impact
  empty_fch fch_flush_cycles fch_flush_WCET pch_lookup pch_read_impact pch_write_impact do_pch_flush
  pch_flush_cycles pch_flush_WCET collides_in_pch read_cycles write_cycles addr_domain addr_colour
  colour_userdomain part uwr nlds ta select_trace
  "big_step_ADT_A_if utf" s0 "policyFlows (pasPolicy initial_aag)" _ _ _ will_domain_switch
  
  apply unfold_locales
               (* external_uwr_same_domain *)
               using schedIncludesCurrentDom apply presburger
              (* external_uwr_equiv *)
              apply (simp add: uwr_equiv_rel)
             (* will_domain_switch_public *)
             subgoal sorry
            (* next_latest_domainswitch_in_future *)
            apply (rule nlds_in_future)
           (* next_latest_domainswitch_flatsteps *)
           apply (rule nlds_flatsteps; simp)
          (* get_next_domain_public *)
          subgoal sorry
          (* get_domainswitch_middle_state_nonempty *)
         subgoal sorry
        subgoal sorry
       subgoal sorry
      subgoal sorry
     subgoal sorry
    subgoal sorry
   subgoal sorry
  subgoal sorry
  done
end

end