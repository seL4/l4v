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

type_synonym if_other_state = "(user_context \<times> det_ext Structures_A.state) \<times> sys_mode"

locale integration_setup = 
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
  +
  (*FIXME: getActiveIRQ is an Arch specific machine monad. I propose that we add this to the
  arch interface, so we can reference it here. It would be a function that will return the
  same result as getActiveIRQ, but does not increment the state. This function existing
  assumes that getActiveIRQ always returns a single output state/value. *)
  fixes peekActiveIRQ :: "bool \<Rightarrow> machine_state \<Rightarrow> irq option"
begin

term getActiveIRQ

lemma peekActiveIRQ_uwr:
  "peekActiveIRQ False (machine_state s) = peekActiveIRQ False (machine_state t)"
oops
(* what do we know
  we definitely have interrupted_modes of os.
  but that incluedes both
  - KernelEntry ev
  - KernelPreempt

  im not yet sure if i should be including KernelPreempt here. I don't think you can Preempt into a
  domainswitch, but i'm not certain how preempt works.

*)

(* check_active_irq_A_if *)

(* definition IsActiveIrq *)

definition will_domain_switch :: "if_other_state \<Rightarrow> bool" where
  "will_domain_switch os \<equiv> case snd os of
    KernelEntry Interrupt \<Rightarrow> (
      \<exists>irq s'. (fst os, Some irq, s') \<in> check_active_irq_A_if \<and>
        (case interrupt_states (snd (fst os)) irq of
         IRQTimer \<Rightarrow> domain_time_internal (exst (snd (fst os))) = 1
       | _ \<Rightarrow> False))
  | _ \<Rightarrow> False"

lemma ex_eq:
  "(\<exists>y. (P y = P' y)) \<Longrightarrow>(\<exists>x. P x) = (\<exists>x. P' x)"
  oops

lemma will_domain_switch_from_uwr:
  "uwr2 os PSched ot \<Longrightarrow>
  will_domain_switch ot = will_domain_switch os"
  apply (clarsimp simp: will_domain_switch_def uwr_def sameFor_def sameFor_scheduler_def)
  apply (case_tac bc; case_tac ba; clarsimp split:event.splits)
    
    apply (prop_tac "interrupt_states (internal_state_if ((aa, bb), KernelEntry Interrupt))
                   = interrupt_states (internal_state_if ((a , b ), KernelEntry Interrupt))")
     apply simp 
     
  

interpretation ma?:time_protection_system PSched fch_lookup fch_read_impact fch_write_impact
  empty_fch fch_flush_cycles fch_flush_WCET pch_lookup pch_read_impact pch_write_impact do_pch_flush
  pch_flush_cycles pch_flush_WCET collides_in_pch read_cycles write_cycles addr_domain addr_colour
  colour_userdomain part uwr nlds ta select_trace
  "big_step_ADT_A_if utf" s0 "policyFlows (pasPolicy initial_aag)" _ _ _ will_domain_switch
  
  apply unfold_locales
               using schedIncludesCurrentDom apply presburger
              apply (simp add: uwr_equiv_rel)
             subgoal sorry
            apply (rule nlds_in_future)
           apply (rule nlds_flatsteps; simp)
          subgoal sorry
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