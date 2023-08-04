(*
 * Copyright 2021, UNSW (ABN 57 195 873 179),
 * Copyright 2021, The University of Melbourne (ABN 84 002 705 224).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TimeProtectionIntegration
imports TimeProtection
  "InfoFlow.Noninterference" schedule_oracle
  CachePartitionIntegrity
begin

type_synonym context_and_state = "user_context \<times> det_ext Structures_A.state"
type_synonym if_other_state    = "context_and_state \<times> sys_mode"

(* note the 64 word it takes is a *physical address*. *)
definition addr_domain where
  "addr_domain initial_aag pa \<equiv> case pasObjectAbs initial_aag ((inv RISCV64.addrFromKPPtr) pa) of
     OrdinaryLabel l \<Rightarrow> Partition l | SilcLabel \<Rightarrow> PSched"

(* FIXME: addr_colour shouldn't even actually be consulting the policy.
   Instead we should specify an address-to-colour assignment and prove that it lines up with
   the policy. Case in point: We'll never know what the colour will be simply from knowing
   we're talking about a SilcLabel! We can only know it from the addr-to-colour assignment,
   which is what this parameter is supposed to be! -robs *)
definition addr_colour where
  "addr_colour initial_aag pa \<equiv> case pasObjectAbs initial_aag ((inv RISCV64.addrFromKPPtr) pa) of
     OrdinaryLabel l \<Rightarrow> l | SilcLabel \<Rightarrow> undefined"

definition colour_userdomain where
  "colour_userdomain \<equiv> Partition"

(* This is how we convert virtual addresses to physical addresses, when dealing with the
   kernel address space. Note that this will look like it's being applied everywhere, even
   though it wouldn't make sense to use this for non-kernel addresses. The idea is that we
   are only "tracking" touched addresses in seL4 for kernel operations -- user steps will
   have touched-addresses assumed to be any address they have a mapping to. We should make
   this distinction more clear in the names of these properties -scottb *)
definition vaddr_to_paddr where
  "vaddr_to_paddr v \<equiv> case v of VAddr v' \<Rightarrow> (RISCV64.addrFromKPPtr v')"

(* assume we have Arch, and some hardware, and set up some initial properties *)
locale integration_setup = 
  Arch +
  time_protection_hardware
    gentypes
    PSched
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    "addr_domain initial_aag"
    "addr_colour initial_aag"
    colour_userdomain +
  Noninterference_valid_initial_state _ _ _ _ initial_aag
  for gentypes :: "('fch \<times> 'fch_cachedness \<times> 'pch \<times> 'pch_cachedness \<times> 'l partition \<times> 'l) itself"
  and initial_aag :: "'l subject_label PAS" +

  (* seL4's domain scheduler is counted in ticks. Define the amount of time between ticks.
   This will be used with measured WCETs, so should be at whatever granularity WCETs are
   measured.*)
  fixes time_per_tick :: time

  (* Define the minimum length of a slice given by the domain scheduler. *)
  fixes slice_length_min :: time

  (* Define the maximum amount of time by which the timer interrupt might be delayed.
   This must be less than `slice_length_min`*)
  fixes timer_delay_max :: time
  assumes timer_delay_lt_slice_length:
    "timer_delay_max < slice_length_min"
  assumes initial_aag_separation_kernel:
    "separation_kernel_policy initial_aag"
  assumes initial_state_ta_subset_inv:
    "ta_subset_inv initial_aag (internal_state_if s0)"
begin

(* TA set extractors *)
definition touched_vaddrs :: "if_other_state \<Rightarrow> vaddr set" where
  "touched_vaddrs s \<equiv>
  VAddr ` (let is = internal_state_if s in (machine_state.touched_addresses (machine_state is)))"

definition touched_addresses :: "if_other_state \<Rightarrow> vpaddr set" where
  "touched_addresses s \<equiv> (\<lambda>v. (v, vaddr_to_paddr v)) ` (touched_vaddrs s)"

(* get the list of (domain, tickcount) from the initial state.
   this system assumes that `domain_list_internal` won't change. *)
definition dom_list_internal where
  "dom_list_internal \<equiv> domain_list_internal $ exst $ snd $ fst s0"

(* convert dom_list_internal into a list of (domain, totaltime) by multiplying
   by time_per_tick *)
definition schedule_list where
  "schedule_list \<equiv> map (\<lambda>(d, ticks). (data_to_nat ticks * time_per_tick, d)) dom_list_internal"

interpretation sched_o:schedule_oracle_delayed _ schedule_list slice_length_min timer_delay_max
  apply unfold_locales
    (* we need to know that the domain list we extract from seL4 has some minimum time.
     this seems reasonable. *)
    subgoal sorry
   (* we need to know that the domain list we extract from seL4 is never empty.
    this also seems reasonable. *)
   subgoal sorry
  (* timer_delay_max \<le> slice_length_min*)
  using timer_delay_lt_slice_length less_or_eq_imp_le apply presburger
  done

(* "next latest domain-switch start" - this is the point at which the next domain-switch
  will have started, even if it has been delayed the maximum amount it can be. *)
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


text \<open>current running partition\<close>
definition userPart where
  "userPart s \<equiv> Partition (partition (pasDomainAbs initial_aag) (internal_state_if s))"

interpretation tphuwr:time_protection_hardware_uwr gentypes PSched
  (* fch_lookup fch_read_impact fch_write_impact empty_fch fch_flush_cycles fch_flush_WCET
     pch_lookup pch_read_impact pch_write_impact do_pch_flush pch_flush_cycles pch_flush_WCET
     collides_in_pch read_cycles write_cycles *)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  "addr_domain initial_aag"
  "addr_colour initial_aag"
  colour_userdomain
  userPart
  uwr
  nlds
  apply unfold_locales
   apply (clarsimp simp: uwr_def sameFor_def sameFor_scheduler_def domain_fields_equiv_def
                         partition_def userPart_def)
  using uwr_equiv_rel apply blast
  done
abbreviation ma_uwr where "ma_uwr \<equiv> tphuwr.uwr"
end


(* here we actually define the expression that checks whether a step (or substep as in
   the four-way split) starting at `os` will be completely determined by the currently-running
   uwr. For now I think this is always true. *)
definition is_uwr_determined :: "if_other_state \<Rightarrow> bool" where
  "is_uwr_determined os \<equiv> case os of ((tc, s), k) \<Rightarrow> True"

(* here we actually define the expression that checks whether a step (or substep as in
   the four-way split) starting at `os` will be completely determined by the scheduler
   uwr. For now I think this is always false, as we don't allow any steps to have this
   property. This was intended for "dirty steps" that access memory in two domains, and
   need their paths to be exactly determined to preserve time protection. *)
definition is_publicly_determined :: "if_other_state \<Rightarrow> bool" where
  "is_publicly_determined os \<equiv> False"


locale integration =
  ii?:integration_setup
    (* fch_lookup fch_read_impact fch_write_impact empty_fch fch_flush_cycles fch_flush_WCET *)
    _ _ _ _ _ _
    (* pch_lookup pch_read_impact pch_write_impact do_pch_flush pch_flush_cycles pch_flush_WCET *)
    _ _ _ _ _ _
    (* collides_in_pch read_cycles write_cycles *)
    _ _ _
    (* arch_globals_equiv_strengthener det_inv utf s0_internal timer_irq
       s0 s0_context Invs current_aag *)
    _ _ _ _ _ _ _ _ _
    gentypes
    (* initial_aag time_per_tick slice_length_min timer_delay_max *)
    _ _ _ _ +
  ts?:trace_selector
    "TYPE((if_other_state \<times> ('fch, 'pch) TimeProtection.state) \<times> 'l partition \<times> trace \<times> vpaddr set)"
    "userPart \<circ> fst"
    ma_uwr PSched
    "[]"
    "is_uwr_determined \<circ> fst"
    "is_publicly_determined \<circ> fst"
    select_trace 
  for gentypes :: "('fch \<times> 'fch_cachedness \<times> 'pch \<times> 'pch_cachedness \<times> 'l partition \<times> 'l) itself"
  and select_trace
begin

(* this tells us, from the state, whether the next irq will be the timer *)
definition is_timer_irq :: "det_ext Structures_A.state \<Rightarrow> bool" where
  "is_timer_irq s \<equiv> let irq = irq_oracle (Suc (irq_state_of_state s)) in
                     \<exists>s'. (Some irq, s') \<in> fst (do_machine_op (getActiveIRQ False) s)
                           \<and> interrupt_states s irq = IRQTimer"

lemma is_timer_irq_def2:
  "is_timer_irq s = (\<lambda>ms is. let irq = irq_oracle (Suc (irq_state ms)) in
                            \<exists>s'. (Some irq, s') \<in> fst (getActiveIRQ False ms)
                                 \<and> is irq = IRQTimer) (machine_state s) (interrupt_states s)"
  apply (clarsimp simp: is_timer_irq_def Let_def do_machine_op_def exec_modify bind_def
    select_f_def simpler_modify_def split:prod.splits)
  apply (rule conj_left_cong)
  apply (clarsimp simp: simpler_gets_def return_def)
  apply fastforce
  done

(* this tells us if our domain time is about to be finished on the next timer irq *)
definition domain_time_zero :: "det_ext Structures_A.state \<Rightarrow> bool" where
  "domain_time_zero os \<equiv> domain_time_internal (exst os) = 1"

(* this combines a few things to decide that the next kernel call is about to do a domain switch *)
definition will_domain_switch :: "if_other_state \<Rightarrow> bool" where
  "will_domain_switch os \<equiv> interrupted_modes (snd os)
                         \<and> is_timer_irq (internal_state_if os)
                         \<and> domain_time_zero (internal_state_if os)"


lemma do_machine_op_spec_eq:
  "f (machine_state t) = f (machine_state s) \<Longrightarrow>
  (\<exists>t'. (a, t') \<in>fst (do_machine_op f t)) = (\<exists>s'. (a, s') \<in> fst (do_machine_op f s))"
  apply (clarsimp simp: do_machine_op_def bind_def simpler_gets_def simpler_modify_def return_def
                        select_f_def)
  apply force
  done  

lemma spec_dmo_getActiveURQ_from_uwr:
  "uwr2 os PSched ot \<Longrightarrow>
  (\<exists>t'. (a, t') \<in> fst (do_machine_op (getActiveIRQ False) (internal_state_if ot)))
= (\<exists>s'. (a, s') \<in> fst (do_machine_op (getActiveIRQ False) (internal_state_if os)))"
  apply (rule do_machine_op_spec_eq)
  apply (clarsimp simp: uwr_def sameFor_def sameFor_scheduler_def)
  apply (clarsimp simp: getActiveIRQ_def bind_def simpler_gets_def simpler_modify_def return_def)
  apply (intro conjI impI allI)
  sorry (* made as a helper for will_domain_switch_from_uwr below. not 100% sure it's
           true, but I think it is -scottb *)

(* PROPERTY will_domain_switch_public: this tells us that the public "uwr"
   decides whether we will perform a domain switch *)
lemma will_domain_switch_from_uwr:
  "uwr2 os PSched ot \<Longrightarrow>
  will_domain_switch ot = will_domain_switch os"
  unfolding uwr_def
  apply (clarsimp simp: will_domain_switch_def uwr_def sameFor_def sameFor_scheduler_def)
  apply (case_tac bc; case_tac ba; clarsimp split:event.splits)
     apply (rule refl_conj_eq, rule conj_cong)
      apply (clarsimp simp: is_timer_irq_def Let_def)
  (* NOTE: maybe we should use monadic_rewrite_dmo_getActiveIRQ here? *)
  sorry

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

(* PATHING: if we take a step, as long as we are in an interrupted mode,
  we will either go through kernel_handle_preemption_if or (kernel_call_A_if Interrupt),
  and then we will always go through kernel_schedule_if *)
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

(* this is what handle_interrupt will look like when the irq is the timer *)
definition
  handle_interrupt_IRQTimer where
 "handle_interrupt_IRQTimer \<equiv>
   do
     modify (\<lambda>s. s\<lparr>machine_state :=
       machine_state s \<lparr>irq_state := irq_state_of_state s + 1\<rparr>\<rparr>);
     timer_tick;
     do_machine_op resetTimer
   od"

definition irq_at' :: "nat \<Rightarrow> irq option" where
  "irq_at' pos \<equiv> Some (irq_oracle pos)"

definition Psame :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "Psame a b = (\<lambda>a' b'. a'=a \<and> b'=b)"

lemma dmo_getActiveIRQ_timer:
  "\<lbrace>\<lambda>s. is_timer_irq s \<and> P (Some (irq_oracle (irq_state (machine_state s)+1)))
  (s\<lparr>machine_state := (machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>)\<rparr>)\<rbrace>
     do_machine_op (getActiveIRQ b)
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

lemma dmo_getActiveIRQ_timer_interrupt_states:
  "\<lbrace>\<lambda>s. is_timer_irq s\<rbrace>
     do_machine_op (getActiveIRQ True)
   \<lbrace>\<lambda>r s. interrupt_states s (the r) = IRQTimer\<rbrace>"
  apply (rule hoare_weaken_pre, rule hoare_strengthen_post)
    apply (rule dmo_getActiveIRQ_timer [where P="\<top>\<top>"])
   apply clarsimp+
  done
  
lemma dmo_getActiveIRQ_timer_withoutextras:
  "\<lbrace>\<lambda>s. is_timer_irq s \<and> P (Some (irq_oracle (irq_state (machine_state s)+1)))
  (s\<lparr>machine_state := (machine_state s\<lparr>irq_state := irq_state (machine_state s) + 1\<rparr>)\<rparr>)\<rbrace>
     do_machine_op (getActiveIRQ b)
   \<lbrace>P\<rbrace>"
  apply (rule hoare_strengthen_post)
  apply (rule dmo_getActiveIRQ_timer)
  apply simp
  done

lemma dmo_getActiveIRQ_timer2:
  "\<lbrace>\<lambda>s. is_timer_irq s\<rbrace>
     do_machine_op (getActiveIRQ b)
   \<lbrace>\<lambda>r s. r = Some (irq_oracle (irq_state (machine_state s)))
      \<and> interrupt_states s (the r) = IRQTimer\<rbrace>"
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

lemma set_ext:
  "(\<forall>x. (x \<in> S) = (x \<in> T)) \<Longrightarrow> (S = T)"
  apply blast
  done

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
  apply (rule prod.expand; rule conjI; clarsimp)
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
  apply (rule prod.expand; rule conjI; clarsimp)
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

lemma do_machine_op_no_fail [wp_unsafe]:
  "no_fail Q f \<Longrightarrow>
  (\<forall>s. P s \<longrightarrow> Q (machine_state s)) \<Longrightarrow>
  no_fail P (do_machine_op f)"
  apply (clarsimp simp:do_machine_op_def)
  apply wpsimp
  apply (clarsimp simp: no_fail_def)
  done

lemma dmo_getActiveIRQ_no_fail:
  "no_fail \<top> (do_machine_op (getActiveIRQ b))"
  apply (wpsimp wp:do_machine_op_no_fail)
  done

lemma monadic_rewrite_dmo_getActiveIRQ:
  "monadic_rewrite E F
    is_timer_irq
    (do_machine_op (getActiveIRQ b))
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

(* FIXME: move this somewhere? PR this? *)
lemma pred_conj_refl [simp]:
  "(P and P) = P"
  by (simp add: pred_conj_def)

lemma bind_assoc_sym:
  "do a \<leftarrow> f; b \<leftarrow> g a; h b od = 
  (do a \<leftarrow> f; g a od) >>= h"
  by (simp add: bind_subst_lift)

lemma bind_assoc_sym_simple:
  "do f; g; h od = 
  (do f; g od) >>= (\<lambda>_. h)"
  by (simp add: bind_subst_lift)

lemma monadic_rewrite_if_lhs_true:
  "\<lbrakk> P \<Longrightarrow> monadic_rewrite F E Q b a \<rbrakk>
      \<Longrightarrow> monadic_rewrite F E ((\<lambda>_. P) and Q)
             (If P b c) a"
  by (clarsimp, rule monadic_rewrite_impossible)

lemma monadic_rewrite_if_lhs_false:
  "\<lbrakk> \<not>P \<Longrightarrow> monadic_rewrite F E R c a \<rbrakk>
      \<Longrightarrow> monadic_rewrite F E ((\<lambda>_. \<not>P) and R)
             (If P b c) a"
  by (clarsimp, rule monadic_rewrite_impossible)

(* the above are almost entirely generated by the following expressions  *)
thm monadic_rewrite_if_lhs [OF monadic_rewrite_impossible, simplified]
thm monadic_rewrite_if_lhs [rotated, OF monadic_rewrite_impossible, simplified]

lemma monadic_rewrite_unused_get:
  "monadic_rewrite F E \<top> (do x \<leftarrow> get; g od) g"
  by (simp add: exec_get monadic_rewrite_refl3)

lemma when_Some_case:
  "(case x of None \<Rightarrow> return ()
  | Some x \<Rightarrow> f x) = when (\<exists>y. x = Some y) (f (the x))"
  apply (cases x; simp)
  done

lemma dmo_getActiveIRQ_handle_interrupt_IRQTimer:
  "monadic_rewrite F E
    is_timer_irq
    (do irq \<leftarrow> do_machine_op (getActiveIRQ b);
        when (irq \<noteq> None) $ handle_interrupt (the irq) od)
    handle_interrupt_IRQTimer"
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
     apply (rule monadic_rewrite_bind_tail)
     unfolding when_def fun_app_def
     apply (rule monadic_rewrite_if_lhs_true)
     unfolding handle_interrupt_def
     apply (rule monadic_rewrite_if_lhs_false)
     apply (rule monadic_rewrite_bind_tail)
      apply (rule monadic_rewrite_bind)
        apply (rule_tac P="st=IRQTimer" in monadic_rewrite_gen_asm)
        apply simp
        apply (rule monadic_rewrite_refl)
       apply (clarsimp simp:ackInterrupt_def)
       apply (rule monadic_rewrite_refl)
      apply wp
     unfolding get_irq_state_def
     apply wp
    apply (rule dmo_getActiveIRQ_timer_withoutextras)
   apply clarsimp
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind)
      apply (rule monadic_rewrite_dmo_getActiveIRQ)
     apply (rule monadic_rewrite_gets_known [where rv=IRQTimer])
    apply wp
   apply (clarsimp simp: bind_assoc handle_interrupt_IRQTimer_def)
   apply (rule monadic_rewrite_unused_get)
  apply (clarsimp simp:is_timer_irq_def Let_def)
  using irq_oracle_max_irq word_not_le apply blast
  done


(* PATHING: if we have is_timer_irq (given by will_domain_switch), then
  handle_preemption_if is equivalent to handle_interrupt_IRQTimer (our very simple monad) *)
lemma handle_preemption_if_timer_irq:
  "monadic_rewrite F E
    is_timer_irq
    (handle_preemption_if tc)
    (do handle_interrupt_IRQTimer; return tc od)"
  unfolding handle_preemption_if_def
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (subst sym [OF bind_assoc])
    apply (rule monadic_rewrite_bind_head)
    apply (rule dmo_getActiveIRQ_handle_interrupt_IRQTimer)
   apply (rule monadic_rewrite_refl)
  apply simp
  done



definition kernel_entry_IRQTimer where
  "kernel_entry_IRQTimer tc \<equiv> do t \<leftarrow> gets cur_thread; return (Inr (), tc) od"

(* this isn't 100% true - we need machine_state ta agnosticism for P *)
lemma set_object_machine_state_interrupt_states [wp]:
  "set_object True a b \<lbrace>\<lambda>s. P (machine_state s) (interrupt_states s)\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (wps | wpsimp)+
  sorry
  

lemma thread_set_is_timer_irq:
  "thread_set a b \<lbrace>is_timer_irq\<rbrace>"
  sorry
(*
crunches thread_set
  for is_timer_irq: is_timer_irq
  (simp: is_timer_irq_def2 wp:crunch_wps)
*)

lemma kernel_entry_is_timer_irq:
  "monadic_rewrite F E
    is_timer_irq
    (kernel_entry_if Interrupt tc)
    (do t \<leftarrow> gets cur_thread;
       thread_set (\<lambda>tcb. tcb \<lparr>tcb_arch := arch_tcb_context_set tc (tcb_arch tcb)\<rparr>) t;
       handle_interrupt_IRQTimer;
       return (Inr (), tc)
    od)"
  apply (simp add: kernel_entry_if_def liftE_def bind_assoc)
  apply (subst when_Some_case)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind_tail)
      apply (subst sym [OF bind_assoc])
      apply (rule monadic_rewrite_bind_head)      
      apply (rule dmo_getActiveIRQ_handle_interrupt_IRQTimer [simplified])
     apply (wp thread_set_is_timer_irq)
    apply wp
   apply (rule monadic_rewrite_refl)
  apply simp
  done

\<comment> \<open>This is an important property, as we need to know that we will have
  scheduler_action s = choose_new_thread before we start to execute the
  `schedule` monad - this is what will get us into our domainswitch.
  (note: we may need a little more to know if we are changing domains, not just
  threads, but i'm pretty sure domain_time_zero should be enough for that.\<close>
lemma
  "numDomains > 1 \<Longrightarrow>
  \<lbrace>domain_time_zero\<rbrace> timer_tick \<lbrace>\<lambda>_ s. scheduler_action s = choose_new_thread\<rbrace>"
  apply (wpsimp simp:timer_tick_def domain_time_zero_def dec_domain_time_def)
  apply (intro conjI; clarsimp)
               apply (wpsimp simp: thread_set_time_slice_def ethread_set_def set_eobject_def)
              apply (wpsimp simp: reschedule_required_def)
             apply wpsimp+
     apply (wpsimp simp: get_thread_state_def thread_get_def touch_object_wp')
    apply (wp touch_object_wp')
   apply (wp touch_object_wp')
  apply (clarsimp simp:domain_time_zero_def)
  done
                
  
lemma schedule_if_choose_new_thread:
  "monadic_rewrite F E
    domain_time_zero
    (schedule_if tc)
    (do schedule_choose_new_thread; return tc od)"
  unfolding schedule_if_def
  apply (subst bind_assoc_sym_simple, simp)
  apply (rule monadic_rewrite_bind_head)
  apply (rule monadic_rewrite_imp)
   apply (rule monadic_rewrite_trans)
    apply (rule monadic_rewrite_bind_head)
    unfolding schedule_def
    apply (rule monadic_rewrite_bind_tail)
     apply (rule monadic_rewrite_bind_tail)
  sorry

(*
  SPLITS FOUR WAYS
  Let's figure out what the four ways are, precisely.

  WHAT WE HAVE SO FAR:
  - domainswitch_two_paths
    - This is a top-level theory about the entire path of the domainswitch step.
  - handle_preemption_if_timer_irq
  - kernel_entry_is_timer_irq
  - schedule_if_choose_new_thread (sorried)
  
*)


definition fourways_oldclean_monad where
  "fourways_oldclean_monad tc \<equiv>
  do
    handle_interrupt_IRQTimer;
    olddom \<leftarrow> gets cur_domain;
    next_domain;
    newdom \<leftarrow> gets cur_domain;
    assert (newdom \<noteq> olddom);
    irqs_of \<leftarrow> gets domain_irqs;
    arch_mask_interrupts True (irqs_of olddom);
    arch_switch_domain_kernel newdom;
    arch_mask_interrupts False (irqs_of newdom);
    return tc
  od"

definition timeprot_gadget_monad where
  "timeprot_gadget_monad tc \<equiv>
  do
    arch_domainswitch_flush;
    return tc
  od"

(* {(s, e, s'). s' \<in> fst (split schedule_if s)} *)
term schedule_if
term split

definition fourways_oldclean :: "(((user_context \<times> det_ext state) \<times> sys_mode) \<times> ((user_context \<times> det_ext state) \<times> sys_mode)) set" where
  "fourways_oldclean = {((s, k), (s', k')). s' \<in> (fst (split fourways_oldclean_monad s))}"

\<comment> \<open>the dirty transition is empty\<close>
definition fourways_dirty :: "(((user_context \<times> det_ext state) \<times> sys_mode) \<times> ((user_context \<times> det_ext state) \<times> sys_mode)) set" where
  "fourways_dirty \<equiv> {(s, s'). s' = s}"

\<comment> \<open>the gadget is all in arch_domainswitch_flush\<close>
definition fourways_gadget :: "(((user_context \<times> det_ext state) \<times> sys_mode) \<times> ((user_context \<times> det_ext state) \<times> sys_mode)) set" where
  "fourways_gadget \<equiv> {((s, k), (s', k')). s' \<in> (fst (split timeprot_gadget_monad s)) \<and> k'=k}"

\<comment> \<open>the newclean transition is also empty\<close>
definition fourways_newclean :: "(((user_context \<times> det_ext state) \<times> sys_mode) \<times> ((user_context \<times> det_ext state) \<times> sys_mode)) set" where
  "fourways_newclean \<equiv> {(s, s'). s' = s}"

lemma tfence_inv:
  "tfence \<lbrace>P\<rbrace>"
  sorry

lemma L2FlushAddr_inv:
  "L2FlushAddr x \<lbrace>P\<rbrace>"
  apply (clarsimp simp: L2FlushAddr_def)
  sorry (* hmm axiomatise this? not sure we can do it any other way *)


lemma simpler_do_machine_op_clearTouchedAddresses_def:
  "do_machine_op clearTouchedAddresses \<equiv> modify (ms_ta_update (\<lambda>_. {}))"
  by (clarsimp simp: bind_def do_machine_op_def clearTouchedAddresses_def simpler_gets_def
                        simpler_modify_def select_f_def return_def)

lemma fourways_gadget_simplechange:
  "(os, os') \<in> fourways_gadget \<Longrightarrow>
  os = ((tc, s), k) \<Longrightarrow>
  os' = ((tc', s'), k') \<Longrightarrow>
  tc' = tc \<and> k' = k \<and> s' = ms_ta_update (\<lambda>_. {}) s"
  apply (clarsimp simp: fourways_gadget_def timeprot_gadget_monad_def)
  apply (clarsimp simp: bind_def return_def)
  apply (clarsimp simp: arch_domainswitch_flush_def)
  apply (clarsimp simp: gets_def bind_def return_def)
  apply (drule_tac s'=ba in use_valid)
    apply (rule mapM_x_wp, rule_tac P="(=) b" in dmo_inv, rule L2FlushAddr_inv)
    apply (rule equalityD1 [OF refl], rule refl)
  apply (clarsimp simp: simpler_do_machine_op_clearTouchedAddresses_def simpler_modify_def)
  apply (clarsimp simp: get_def)
  apply (drule_tac s'=bb in use_valid, rule_tac P="(=) s" in dmo_inv, rule tfence_inv, rule refl)
  apply simp
  done

lemma fourways_gadget_simplechange':
  "(((tc, s), k), ((tc', ms_ta_update (\<lambda>_. {}) s), k')) \<in> fourways_gadget"
  oops

lemma monadic_rewrite_eq:
  "P s \<Longrightarrow>
  (\<And> F E. monadic_rewrite F E P f f') \<Longrightarrow>
  f s = f' s"
  apply (clarsimp simp: monadic_rewrite_def)
  apply force
  done

(* this will be where we need to do a bunch of monadic rewrite stuff *)
lemma domainswitch_fourways_stuffs:
  "(s1, s3) \<in> Step () \<Longrightarrow>
  will_domain_switch s1 \<Longrightarrow>
  \<exists> s2. (s1, s2) \<in> fourways_oldclean \<and>
    (s2, s3) \<in> fourways_gadget"
  sorry

lemma domainswitch_splits_four_ways:
  "can_split_four_ways
    will_domain_switch
    (Step ())
    fourways_oldclean
    fourways_dirty
    fourways_gadget
    fourways_newclean"
  apply (clarsimp simp: can_split_four_ways_def)
  apply (drule(1) domainswitch_fourways_stuffs)
  apply (clarsimp)
  apply (rule_tac x=ab in exI)
  apply (rule_tac x=bd in exI)
  apply (rule_tac x=be in exI)
  apply clarsimp
  apply (rule_tac x=ab in exI)
  apply (rule_tac x=bd in exI)
  apply (rule_tac x=be in exI)
  apply (clarsimp simp: fourways_dirty_def)
  apply (rule_tac x=ab in exI)
  apply (rule_tac x="ms_ta_update (\<lambda>_. {}) bd" in exI)
  apply (rule_tac x=be in exI)
  apply (frule fourways_gadget_simplechange, rule refl, rule refl)
  apply clarsimp
  apply (clarsimp simp: fourways_newclean_def)
  done

(* based on the monad next_domain and the functions part/partition.
  Never returns PSched. *)
definition get_next_domain
  :: "(user_context \<times> det_ext Structures_A.state) \<times> sys_mode \<Rightarrow> 'l partition" where
  "get_next_domain s \<equiv> 
    let ds = internal_state_if s in
    let domain_index' = (domain_index ds + 1) mod length (domain_list ds) in
    let next_dom = (domain_list ds)!domain_index' in
      Partition (label_of (the_elem ((pasDomainAbs initial_aag) (fst next_dom))))"

lemma get_next_domain_not_Sched:
  "get_next_domain os \<noteq> PSched"
  apply (clarsimp simp: get_next_domain_def)
  by (meson partition.distinct)

lemma current_domain_not_Sched:
  "userPart os \<noteq> PSched"
  by (simp add: userPart_def)

lemma get_next_domain_public:
  "uwr2 s PSched t \<Longrightarrow>
  get_next_domain t = get_next_domain s"
  apply (clarsimp simp: get_next_domain_def)
  apply (clarsimp simp: uwr_def sameFor_def sameFor_scheduler_def)
  apply (clarsimp simp: domain_fields_equiv_def)
  done

lemma uwr_equates_touched_addresses:
  "uwr2 s (userPart s) t \<Longrightarrow>
  touched_addresses s = touched_addresses t"
  apply (clarsimp simp: userPart_def)
  apply (drule uwr_partition_if, rule refl, rule refl)
  apply clarsimp
  apply (clarsimp simp: ii.touched_addresses_def touched_vaddrs_def)
  done

(* same as above, just rephrased for the locale *)
lemma external_uwr_same_touched_addrs:
  "\<lbrakk>uwr2 s d t;
  userPart s = d\<rbrakk> \<Longrightarrow>
  ii.touched_addresses t = ii.touched_addresses s"
  using uwr_equates_touched_addresses by presburger

definition all_paddrs_of :: "'l partition \<Rightarrow> paddr set" where
  "all_paddrs_of d \<equiv> {a. addr_domain initial_aag a = d}"

definition touched_addrs_inv :: "if_other_state \<Rightarrow> bool" where
  "touched_addrs_inv s \<equiv>
  snd ` touched_addresses s \<subseteq> all_paddrs_of (userPart s) \<union> kernel_shared_precise"

interpretation l2p?: ArchL2Partitioned "TYPE('l subject_label \<times> 'l)"
  "addr_colour initial_aag"
  "\<lambda>sl. case sl of OrdinaryLabel l \<Rightarrow> l"
  done

\<comment> \<open> Correspondence between "invariant lemmas" and "locale" form of the TA subset invariant. \<close>

lemma ta_vaddr_to_paddr:
  "snd ` ii.touched_addresses s =
   addrFromKPPtr ` machine_state.touched_addresses (machine_state (snd $ fst s))"
  unfolding touched_addresses_def touched_vaddrs_def image_def vaddr_to_paddr_def
  apply(clarsimp split:vaddr.splits)
  apply(rule set_eqI)
  apply clarsimp
  by (metis vaddr.exhaust vaddr.inject)

lemma addrFromKPPtr_inj:
  "inj addrFromKPPtr"
  unfolding addrFromKPPtr_def
  by force

lemma addrFromKPPtr_surj:
  "surj addrFromKPPtr"
  unfolding addrFromKPPtr_def
  by force

lemma addrFromKPPtr_bij:
  "bijection addrFromKPPtr"
  unfolding bijection_def bij_def
  using addrFromKPPtr_inj addrFromKPPtr_surj
  by blast


lemma accessible_vaddr_to_paddr:
  "separation_kernel_policy initial_aag \<Longrightarrow>
   all_paddrs_of (userPart s) \<comment> \<open>\<union> kernel_shared_precise\<close> =
   addrFromKPPtr ` pas_addrs_accessible_to initial_aag (cur_label initial_aag (snd $ fst s))"
  unfolding all_paddrs_of_def kernel_shared_precise_def
  unfolding addr_domain_def
  apply(clarsimp simp:userPart_def)
  apply(rule set_eqI)
  apply clarsimp
  apply(clarsimp simp:image_def)
  apply(rule iffI)
   (* Case: vaddr version of accessibility implies paddr one *)
   apply(clarsimp split:subject_label.splits)
   apply(drule_tac l="cur_label initial_aag (internal_state_if s)"
     in separation_kernel_only_owned_accessible)
   apply simp
   apply(clarsimp simp:pas_addrs_of_def)
   apply(rename_tac x)
   apply(rule_tac x="inv addrFromKPPtr x" in exI)
   apply(rule conjI)
    prefer 2
    apply(force simp:addrFromKPPtr_surj surj_f_inv_f)
   apply(clarsimp simp:partition_def)
   using domains_distinct
   unfolding pas_domains_distinct_def
   apply(erule_tac x="cur_domain (internal_state_if s)" in allE)
   apply force
  (* Case: paddr version of accessibility implies vaddr one *)
  apply(clarsimp split:subject_label.splits)
  apply(clarsimp simp:partition_def)
  using domains_distinct
  unfolding pas_domains_distinct_def
  apply(erule_tac x="cur_domain (internal_state_if s)" in allE)
  apply clarsimp
  using addrFromKPPtr_inj
  apply clarsimp
  apply(rename_tac x l)
  apply(drule_tac l=l in separation_kernel_only_owned_accessible)
  apply(clarsimp simp add:pas_addrs_of_def)
  using pasDomainAbs_not_SilcLabel
  by blast

lemma ta_subset_inv_to_locale_form:
  "separation_kernel_policy initial_aag \<Longrightarrow>
   ta_subset_inv initial_aag (snd $ fst s) \<Longrightarrow>
   touched_addrs_inv s"
  unfolding touched_addrs_inv_def
  unfolding ta_subset_inv_def
  apply(clarsimp simp: ta_vaddr_to_paddr accessible_vaddr_to_paddr)
  apply(clarsimp simp:image_def)
  by blast

crunch guarded_pas_domain[wp]: check_active_irq_if "guarded_pas_domain aag"
crunch ct_running[wp]: check_active_irq_if "ct_running"
crunch ct_idle[wp]: check_active_irq_if "ct_idle"
crunch schact_is_rct[wp]: check_active_irq_if "schact_is_rct"
  (simp: schact_is_rct_def)
crunch domain_sep_inv[wp]: check_active_irq_if "domain_sep_inv irqs st"
crunch pas_refined[wp]: check_active_irq_if "pas_refined aag"

definition invs_if_trimmed :: "observable_if \<Rightarrow> bool" where
  "invs_if_trimmed s \<equiv>
     (case (snd s) of
        KernelEntry e \<Rightarrow> (e \<noteq> Interrupt \<longrightarrow> ct_running (internal_state_if s)) \<and>
                         (ct_running (internal_state_if s) \<or> ct_idle (internal_state_if s)) \<and>
                         scheduler_action (internal_state_if s) = resume_cur_thread
      | KernelExit \<Rightarrow> (ct_running (internal_state_if s) \<or> ct_idle (internal_state_if s)) \<and>
                      scheduler_action (internal_state_if s) = resume_cur_thread
      | InUserMode \<Rightarrow> ct_running (internal_state_if s) \<and>
                      scheduler_action (internal_state_if s) = resume_cur_thread
      | InIdleMode \<Rightarrow> ct_idle (internal_state_if s) \<and>
                      scheduler_action (internal_state_if s) = resume_cur_thread
      | _ \<Rightarrow> True)"

lemma invs_if_trimmed:
  "invs_if s \<Longrightarrow> invs_if_trimmed s"
  unfolding invs_if_def invs_if_trimmed_def
  by blast

(* TODO: Move this to ADT_IF with the others? *)
thm pasObjectAbs_current_aag
lemma pasDomainAbs_current_aag:
  "pasDomainAbs (current_aag x) = pasDomainAbs initial_aag"
  by (simp add: current_aag_def)

lemma ta_subset_inv_current_aag:
  "ta_subset_inv (current_aag x) = ta_subset_inv initial_aag"
  unfolding ta_subset_inv_def pas_addrs_accessible_to_def pas_labels_accessible_to_def
  by (clarsimp simp:pasObjectAbs_current_aag pasDomainAbs_current_aag pasPolicy_current_aag)

(* Trivial relaxation to allow it to be the current_aag of a different state *)
(* TODO: Consider modifying the original? *)
lemma pas_refined_cur':
  "pas_refined (current_aag s') s = pas_refined initial_aag s"
  apply (rule iffI)
   apply (subst initial_aag_bak[where s=s'])
   apply (erule pas_refined_pasSubject_update)
    apply simp
   apply (simp add: current_aag_def)
   apply (subst the_subject_of_aag_domain[where l = "pasSubject initial_aag"])
    apply (rule cur_domain_subject_s0)
   apply (blast intro: cur_domain_subject_s0)
  apply (simp add: current_aag_def)
  apply (rule pas_refined_pasSubject_update)
    apply blast+
  done

(* Note: It's almost surely asking for the wrong thing if we're ever using lemmas in such a way
   as to demand `pas_cur_domain` or `is_subject` about the initial_aag, because they both concern
   the pasSubject of the given aag, which for the initial_aag is essentially arbitrary.
   Thus, in situations where this would occur we instead invoke the step lemmas to preserve them
   for (current_aag s) instead, then convert them back to the initial_aag version afterwards. *)
lemma ta_subset_inv_if_step:
  "\<lbrakk>(((uc, s), m), (uc', s'), m') \<in> global_automaton_if check_active_irq_A_if (do_user_op_A_if utf)
      kernel_call_A_if kernel_handle_preemption_if kernel_schedule_if kernel_exit_A_if;
    ta_subset_inv initial_aag s;
    invs_if_trimmed ((uc, s), m);
    guarded_pas_domain initial_aag s;
    einvs s;
    domain_sep_inv False s0_internal s;
    pas_refined initial_aag s;
    step_restrict ((uc', s'), m')\<rbrakk>
   \<Longrightarrow> ta_subset_inv initial_aag s' \<and> invs_if_trimmed ((uc', s'), m') \<and>
     guarded_pas_domain initial_aag s' \<and> einvs s' \<and> domain_sep_inv False s0_internal s' \<and>
     pas_refined initial_aag s'"
   apply(prop_tac "ta_subset_inv (current_aag s) s")
    apply(force simp:ta_subset_inv_current_aag)
  apply(clarsimp simp:global_automaton_if_def)
  apply(erule disjE)
   \<comment> \<open>Case: Kernel entry with preemption during event handling\<close>
   apply(clarsimp simp:kernel_call_A_if_def invs_if_trimmed_def)
   apply(prop_tac "ct_active s")
    apply(force simp:active_from_running)
   apply(prop_tac "is_subject (current_aag s) (cur_thread s)")
    apply(clarsimp simp:current_aag_def)
    using guarded_pas_domain_cur guarded_active_ct_cur_domain the_subject_of_aag_domain
    apply fastforce
   apply(rule conjI)
    apply(prop_tac "ta_subset_inv (current_aag s) s'")
     apply(force intro:use_valid[OF _ kernel_entry_if_ta_subset_inv]
       simp:pas_refined_cur pas_cur_domain_current_aag)
    apply(force simp:ta_subset_inv_current_aag)
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ kernel_entry_if_guarded_pas_domain])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ kernel_entry_if_invs])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ kernel_entry_if_valid_list])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ kernel_entry_if_valid_sched])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ kernel_entry_if_domain_sep_inv])
   apply(prop_tac "pas_refined (current_aag s) s'")
    apply(force intro:use_valid[OF _ kernel_entry_pas_refined] simp:schact_is_rct_def
      pas_refined_cur guarded_pas_domain_cur)
   apply(force simp:pas_refined_cur')
  apply(erule disjE)
   \<comment> \<open>Case: Kernel entry without preemption during event handling\<close>
   apply(clarsimp simp:kernel_call_A_if_def invs_if_trimmed_def)
   apply(prop_tac "ct_active s \<or> ct_idle s")
    apply(force simp:active_from_running)
   apply(rule conjI)
    apply(prop_tac "ta_subset_inv (current_aag s) s'")
     apply(force intro:use_valid[OF _ kernel_entry_if_ta_subset_inv]
       simp:pas_refined_cur pas_cur_domain_current_aag)
    apply(force simp:ta_subset_inv_current_aag)
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ kernel_entry_if_guarded_pas_domain])
   apply(prop_tac "e \<noteq> Interrupt \<longrightarrow> ct_active s")
     apply(prop_tac "ct_idle s \<longrightarrow> e = Interrupt")
      apply(force simp:active_from_running ct_active_not_idle')
    apply force
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ kernel_entry_if_invs])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ kernel_entry_if_valid_list])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ kernel_entry_if_valid_sched])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ kernel_entry_if_domain_sep_inv])
   apply(prop_tac "ct_active s \<longrightarrow> is_subject (current_aag s) (cur_thread s)")
    apply(clarsimp simp:current_aag_def)
    using guarded_pas_domain_cur guarded_active_ct_cur_domain the_subject_of_aag_domain
    apply fastforce
   apply(prop_tac "pas_refined (current_aag s) s'")
    apply(force intro:use_valid[OF _ kernel_entry_pas_refined] simp:schact_is_rct_def
      pas_refined_cur guarded_pas_domain_cur)
   apply(force simp:pas_refined_cur')
  apply(erule disjE)
   \<comment> \<open>Case: Handle in-kernel preemption\<close>
   apply(clarsimp simp:kernel_handle_preemption_if_def invs_if_trimmed_def)
   apply(rule conjI)
    apply(prop_tac "ta_subset_inv (current_aag s) s'")
     apply(force intro:use_valid[OF _ handle_preemption_if_ta_subset_inv]
       simp:pas_refined_cur pas_cur_domain_current_aag)
    apply(force simp: ta_subset_inv_current_aag)
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ handle_preemption_if_guarded_pas_domain])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ handle_preemption_if_invs])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ handle_preemption_if_valid_list])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ handle_preemption_if_valid_sched])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ handle_preemption_if_domain_sep_inv])
   apply(force intro:use_valid[OF _ handle_preemption_if_pas_refined])
  apply(erule disjE)
   \<comment> \<open>Case: Schedule\<close>
   apply(clarsimp simp:kernel_schedule_if_def invs_if_trimmed_def)
   apply(rule conjI)
    apply(force intro:use_valid[OF _ schedule_if_ta_subset_inv])
   apply(rule context_conjI)
    using use_valid[OF _ schedule_if_ct_running_or_ct_idle]
    apply presburger
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ schedule_if_scheduler_action])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ schedule_if_guarded_pas_domain])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ schedule_if_invs])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ schedule_if_valid_list])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ schedule_if_valid_sched])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ schedule_if_domain_sep_inv])
   apply(force intro:use_valid[OF _ schedule_if_pas_refined])
  apply(erule disjE)
   \<comment> \<open>Case: Kernel exit\<close>
   apply(clarsimp simp:kernel_exit_A_if_def invs_if_trimmed_def)
   apply(rule conjI)
    apply(force intro:use_valid[OF _ kernel_exit_if_inv])
   apply clarsimp
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ kernel_exit_if_inv])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ kernel_exit_if_inv])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ kernel_exit_if_inv])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ kernel_exit_if_inv])
   apply(rule context_conjI)
    apply(force simp:use_valid[OF _ kernel_exit_if_inv])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ kernel_exit_if_inv])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ kernel_exit_if_inv])
   apply(rule context_conjI)
    apply(force simp:use_valid[OF _ kernel_exit_if_inv])
   apply(force simp:use_valid[OF _ kernel_exit_if_inv])
  apply(erule disjE)
   \<comment> \<open>Case: User runs, causes exception\<close>
   apply(clarsimp simp:check_active_irq_A_if_def do_user_op_A_if_def invs_if_trimmed_def)
   apply(rule conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_ta_subset_inv]
      use_valid[OF _ check_active_irq_if_ta_subset_inv])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_invs, simplified, THEN conjunct2]
      use_valid[OF _ check_active_irq_if_invs]
      use_valid[OF _ check_active_irq_if_ct_running])
   apply clarsimp
   apply(rule context_conjI)
    apply(rename_tac uc'' s'' e)
    apply(rule_tac f="do_user_op_if utf uc''" and P = "\<lambda>s. scheduler_action s = resume_cur_thread"
      in use_valid)
      apply force
     apply(clarsimp simp:check_active_irq_if_def)
     apply(wpsimp wp:crunch_wps simp:crunch_simps ct_in_state_def st_tcb_at_def obj_at_def)
    apply(force simp:use_valid[OF _ check_active_irq_if_schact_is_rct, simplified schact_is_rct_def])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_use_op_guarded_pas_domain]
      use_valid[OF _ check_active_irq_if_guarded_pas_domain])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_invs, simplified, THEN conjunct1]
      use_valid[OF _ check_active_irq_if_invs]
      use_valid[OF _ check_active_irq_if_ct_running])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_valid_list]
      use_valid[OF _ check_active_irq_if_valid_list]
      use_valid[OF _ check_active_irq_if_ct_running])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ do_user_op_if_valid_sched]
      use_valid[OF _ check_active_irq_if_valid_sched]
      use_valid[OF _ check_active_irq_if_ct_running])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_domain_sep_inv]
      use_valid[OF _ check_active_irq_if_domain_sep_inv])
   apply(force intro:use_valid[OF _ do_user_op_pas_refined]
      use_valid[OF _ check_active_irq_if_pas_refined])
  apply(erule disjE)
   \<comment> \<open>Case: User runs, no exception happens\<close>
   apply(clarsimp simp:check_active_irq_A_if_def do_user_op_A_if_def invs_if_trimmed_def)
   apply(rule conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_ta_subset_inv]
      use_valid[OF _ check_active_irq_if_ta_subset_inv])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_invs, simplified, THEN conjunct2]
      use_valid[OF _ check_active_irq_if_invs]
      use_valid[OF _ check_active_irq_if_ct_running])
   apply(rule context_conjI)
    apply(rename_tac uc'' s'')
    apply(rule_tac f="do_user_op_if utf uc''" and P = "\<lambda>s. scheduler_action s = resume_cur_thread"
      in use_valid)
      apply force
     apply(clarsimp simp:check_active_irq_if_def)
     apply(wpsimp wp:crunch_wps simp:crunch_simps ct_in_state_def st_tcb_at_def obj_at_def)
    apply(force simp:use_valid[OF _ check_active_irq_if_schact_is_rct, simplified schact_is_rct_def])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_use_op_guarded_pas_domain]
      use_valid[OF _ check_active_irq_if_guarded_pas_domain])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_invs, simplified, THEN conjunct1]
      use_valid[OF _ check_active_irq_if_invs]
      use_valid[OF _ check_active_irq_if_ct_running])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_valid_list]
      use_valid[OF _ check_active_irq_if_valid_list]
      use_valid[OF _ check_active_irq_if_ct_running])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ do_user_op_if_valid_sched]
      use_valid[OF _ check_active_irq_if_valid_sched]
      use_valid[OF _ check_active_irq_if_ct_running])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ do_user_op_if_domain_sep_inv]
      use_valid[OF _ check_active_irq_if_domain_sep_inv])
   apply(force intro:use_valid[OF _ do_user_op_pas_refined]
      use_valid[OF _ check_active_irq_if_pas_refined])
  apply(erule disjE)
   \<comment> \<open>Case: Interrupt while in user mode\<close>
   apply(clarsimp simp:check_active_irq_A_if_def invs_if_trimmed_def)
   apply(rule conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_ta_subset_inv])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_ct_running])
   apply(rule context_conjI)
    apply(force simp:use_valid[OF _ check_active_irq_if_schact_is_rct, simplified schact_is_rct_def])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_guarded_pas_domain])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_invs])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_valid_list])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ check_active_irq_if_valid_sched])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ check_active_irq_if_domain_sep_inv])
   apply(fastforce intro:use_valid[OF _ check_active_irq_if_pas_refined])
  apply(erule disjE)
   \<comment> \<open>Case: Interrupt while in idle mode\<close>
   apply(clarsimp simp:check_active_irq_A_if_def invs_if_trimmed_def)
   apply(rule conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_ta_subset_inv])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_ct_idle])
   apply(rule context_conjI)
    apply(force simp:use_valid[OF _ check_active_irq_if_schact_is_rct, simplified schact_is_rct_def])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_guarded_pas_domain])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_invs])
   apply(rule context_conjI)
    apply(force intro:use_valid[OF _ check_active_irq_if_valid_list])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ check_active_irq_if_valid_sched])
   apply(rule context_conjI)
    apply(fastforce intro:use_valid[OF _ check_active_irq_if_domain_sep_inv])
   apply(fastforce intro:use_valid[OF _ check_active_irq_if_pas_refined])
  \<comment> \<open>Case: No interrupt while in idle mode\<close>
  apply(clarsimp simp:check_active_irq_A_if_def invs_if_trimmed_def)
  apply(rule conjI)
   apply(force intro:use_valid[OF _ check_active_irq_if_ta_subset_inv])
  apply(rule context_conjI)
   apply(force intro:use_valid[OF _ check_active_irq_if_ct_idle])
  apply(rule context_conjI)
   apply(force simp:use_valid[OF _ check_active_irq_if_schact_is_rct, simplified schact_is_rct_def])
  apply(rule context_conjI)
   apply(force intro:use_valid[OF _ check_active_irq_if_guarded_pas_domain])
  apply(rule context_conjI)
   apply(force intro:use_valid[OF _ check_active_irq_if_invs])
  apply(rule context_conjI)
   apply(force intro:use_valid[OF _ check_active_irq_if_valid_list])
  apply(rule context_conjI)
   apply(fastforce intro:use_valid[OF _ check_active_irq_if_valid_sched])
  apply(rule context_conjI)
   apply(fastforce intro:use_valid[OF _ check_active_irq_if_domain_sep_inv])
  apply(fastforce intro:use_valid[OF _ check_active_irq_if_pas_refined])
  done

(* Note: changing from initial_aag to current_aag doesn't work here because the locale wants
   something relative to the initial_aag, as that's what it's using for addr_domain.
   So instead we have the per-step lemma ta_subset_inv_if_step invoked by this one convert
   to current_aag to use the step lemmas, and convert back to initial_aag afterwards. *)
lemma ta_subset_inv_execution:
  "s \<in> execution (big_step_ADT_A_if utf) s0 js \<Longrightarrow>
   ta_subset_inv initial_aag (internal_state_if s)"
  apply(rule_tac Q="invs_if_trimmed s \<and> pas_refined initial_aag (internal_state_if s) \<and>
    guarded_pas_domain initial_aag (internal_state_if s) \<and>
    einvs (internal_state_if s) \<and>
    domain_sep_inv False s0_internal (internal_state_if s)"
    in conjunct1)
  apply(induct js arbitrary: s rule: rev_induct)
   apply(rule conjI)
    apply(force simp:execution_def steps_def
      big_step_ADT_A_if_def big_step_adt_def ADT_A_if_def
      initial_state_ta_subset_inv)
   apply(clarsimp simp:execution_def steps_def
     big_step_ADT_A_if_def big_step_adt_def ADT_A_if_def
     full_invs_if_def invs_if_trimmed)
   apply(rule conjI)
    using reachable_s0[THEN pas_refined_if] pas_refined_cur
    apply blast
   apply(rule conjI)
    using reachable_s0[THEN guarded_pas_domain_if] internal_state_s0 current_aag_initial
    apply fastforce
   using Invs_def Invs_s0_internal internal_state_s0
   apply presburger
  apply(clarsimp simp: execution_def steps_def
     big_step_ADT_A_if_def big_step_adt_def ADT_A_if_def)
  apply(drule big_steps_I_holds[where I="{s'. ta_subset_inv initial_aag (internal_state_if s') \<and>
    invs_if_trimmed s' \<and> pas_refined initial_aag (internal_state_if s') \<and>
    guarded_pas_domain initial_aag (internal_state_if s') \<and>
    einvs (internal_state_if s') \<and>
    domain_sep_inv False s0_internal (internal_state_if s')}"])
    apply force
   apply(clarsimp simp:inv_holds_def)
   using ta_subset_inv_if_step
   apply blast
  by force

lemma ta_subset_inv_reachable:
  (* According to Scott, initial_aag should be fine here rather than `current_aag (snd $ fst s0)` *)
  "reachable s \<Longrightarrow>
  ta_subset_inv initial_aag (snd $ fst s)"
  (* `reachable` is defined in Noninterference_Base.thy so it's not used in AInvs/Access.
     Even though `silc_inv` is of IF session, it doesn't look like it's proved for `reachable`. *)
  unfolding reachable_def
  using ta_subset_inv_execution
  by fastforce

lemma subset_inv_proof_aux:
  "separation_kernel_policy initial_aag \<Longrightarrow>
   reachable s \<Longrightarrow>
   touched_addrs_inv s"
  using ta_subset_inv_reachable ta_subset_inv_to_locale_form
  by blast

lemma subset_inv_proof:
  "separation_kernel_policy initial_aag \<Longrightarrow>
   reachable s \<Longrightarrow>
         snd ` ii.touched_addresses s
         \<subseteq> {a. addr_domain initial_aag a = userPart s} \<union>
            kernel_shared_precise"
  using all_paddrs_of_def subset_inv_proof_aux touched_addrs_inv_def
  by blast

lemma ta_subset_inv_to_locale_form':
  "separation_kernel_policy initial_aag \<Longrightarrow>
   \<comment> \<open>This is @{term\<open>ta_subset_inv\<close>} but with the TA set required to be a subset
     of the addresses of the old domain (in s), not the new domain (in s').\<close>
   machine_state.touched_addresses (machine_state (snd $ fst s')) \<subseteq>
     pas_addrs_accessible_to initial_aag (cur_label initial_aag (snd $ fst s)) \<Longrightarrow>
   \<comment> \<open>Similarly for @{term\<open>touched_addrs_inv\<close>}.\<close>
   snd ` touched_addresses s' \<subseteq> all_paddrs_of (userPart s) \<union> kernel_shared_precise"
  unfolding touched_addrs_inv_def
  unfolding ta_subset_inv_def
  apply(clarsimp simp: ta_vaddr_to_paddr accessible_vaddr_to_paddr)
  apply(clarsimp simp:image_def)
  by blast

(* TODO: This might be worth moving back to somewhere in AInvs. -robs *)
lemma resetTimer_ta_inv:
  "\<lbrace>\<lambda>s. P (machine_state.touched_addresses (machine_state s))\<rbrace>
     do_machine_op resetTimer
   \<lbrace>\<lambda>_ s. P (machine_state.touched_addresses (machine_state s))\<rbrace>"
  unfolding do_machine_op_def resetTimer_def machine_op_lift_def machine_rest_lift_def
  by (wpsimp wp: crunch_wps simp:crunch_simps simpler_gets_def simpler_modify_def bind_def
    select_f_def return_def)

(* FIXME: Turns out this sorried lemma is not true because timer_tick adds cur_thread to TA,
  which is what's leading wp down a bad path. Actually need to fix this all the way back in
  Deterministic_AI. For now we'll just remove it from the wp set. -robs *)
thm timer_tick_all_but_exst
declare timer_tick_all_but_exst[wp del]
declare timer_tick_extended.all_but_exst[wp del]

(* FIXME: This is something we actually need to prove all the way back in AInvs along with a new
  version of timer_tick_all_but_exst, but I'm leaving this sorry here as moving it back to AInvs
  right now might cause an unpredictable number of breakages that we'll just have to deal with
  when the time comes. I'm moderately confident this is true from inspecting timer_tick. -robs *)
lemma timer_tick_ta:
  "\<lbrace>\<lambda>s. machine_state.touched_addresses (machine_state s) = ta \<and> ct = cur_thread s \<and> kh = kheap s\<rbrace>
     timer_tick
   \<lbrace>\<lambda>rv s. machine_state.touched_addresses (machine_state s) = ta \<union> obj_range ct (the (kh ct))\<rbrace>"
  unfolding timer_tick_def
  sorry

lemma handle_interrupt_IRQTimer_ta:
  "\<lbrace>\<lambda>s. machine_state.touched_addresses (machine_state s) = ta \<and> ct = cur_thread s \<and> kh = kheap s\<rbrace>
     handle_interrupt_IRQTimer
   \<lbrace>\<lambda>rv s. machine_state.touched_addresses (machine_state s) = ta \<union> obj_range ct (the (kh ct))\<rbrace>"
  unfolding handle_interrupt_IRQTimer_def
  by (wpsimp wp:crunch_wps resetTimer_ta_inv timer_tick_ta simp:crunch_simps)

lemma arch_mask_interrupts_preserves_ta:
  "arch_mask_interrupts b irqs
   \<lbrace>\<lambda>s. machine_state.touched_addresses (machine_state s) = ta\<rbrace>"
  unfolding arch_mask_interrupts_def do_machine_op_def maskInterrupt_def
  apply(wpsimp wp:crunch_wps simp:crunch_simps)
   apply(wpsimp simp:simpler_modify_def)
  by force

lemma arch_switch_domain_kernel_preserves_ta:
  "arch_switch_domain_kernel d
   \<lbrace>\<lambda>s. machine_state.touched_addresses (machine_state s) = ta\<rbrace>"
  unfolding arch_switch_domain_kernel_def do_machine_op_def setVSpaceRoot_def
  by (wpsimp wp:crunch_wps simp:crunch_simps machine_op_lift_def machine_rest_lift_def
    select_f_def simpler_gets_def simpler_modify_def bind_def return_def)

lemma oldclean_preserves_ta_subset_inv:
  "reachable s \<Longrightarrow>
   (s, s') \<in> fourways_oldclean \<Longrightarrow>
   machine_state.touched_addresses (machine_state (snd $ fst s')) \<subseteq>
     pas_addrs_accessible_to initial_aag (cur_label initial_aag (snd $ fst s))"
  apply(frule ta_subset_inv_reachable)
  apply clarsimp
  (* That fourways_oldclean only touches the current thread. *)
  apply(prop_tac "machine_state.touched_addresses (machine_state (snd $ fst s')) =
    machine_state.touched_addresses (machine_state (snd $ fst s)) \<union>
    obj_range (cur_thread (snd $ fst s)) (the (kheap (snd $ fst s) (cur_thread (snd $ fst s))))")
   apply(clarsimp simp:fourways_oldclean_def fourways_oldclean_monad_def)
   apply(clarsimp simp:bind_def simpler_gets_def)
   apply(drule use_valid[OF _ handle_interrupt_IRQTimer_ta], force)
   apply(clarsimp simp:next_domain_def simpler_modify_def assert_def)
   apply(clarsimp split:if_splits simp:fail_def)
   apply(drule use_valid[OF _ arch_mask_interrupts_preserves_ta], force)
   apply(drule use_valid[OF _ arch_switch_domain_kernel_preserves_ta], force)
   apply(drule use_valid[OF _ arch_mask_interrupts_preserves_ta], force)
   apply(clarsimp simp:return_def Let_def)
  (* That the current thread is always accessible to the currently running domain. *)
  apply(prop_tac
    "obj_range (cur_thread (snd $ fst s)) (the (kheap (snd $ fst s) (cur_thread (snd $ fst s)))) \<subseteq>
    pas_addrs_accessible_to initial_aag (cur_label initial_aag (snd $ fst s))")
   unfolding pas_addrs_accessible_to_def
   apply(case_tac "ct_idle (internal_state_if s)")
    (* When the current thread is idle, it's also accessible to the current label. *)
    unfolding pas_labels_accessible_to_def
    (* FIXME: Actually I'm pretty sure the problem here is the idle thread is treated specially as
       a global, not with a label. However, the latest kernel cloning implementation *does* clone
       the idle thread for each domain. As the impact of this on the ASpec and all current proofs
       is unknown, I think for now we'll just have to document this as a semi-major TODO. -robs *)
    apply(frule reachable_invs_if[THEN invs_if_Invs])
    apply(clarsimp simp:Invs_def)
    apply(frule cur_thread_idle)
    apply clarsimp
    subgoal sorry
   using initial_aag_separation_kernel
   unfolding separation_kernel_policy_def
   apply clarsimp
   apply(frule pas_refined_initial_aag_reachable[THEN pas_refined_no_label_straddling_objs])
   unfolding no_label_straddling_objs_def
   apply clarsimp
   apply(erule_tac x="cur_thread (internal_state_if s)" in allE)
   apply(clarsimp split:option.splits)
    (* That the cur_thread actually exists on the kheap. *)
    apply(frule reachable_invs_if[THEN invs_if_Invs])
    apply(force simp:Invs_def invs_def cur_tcb_def tcb_at_def get_tcb_def)
   apply(rename_tac x xa x2)
   apply(erule_tac x=xa in ballE)
    prefer 2
    apply(force simp:obj_range_def)
   apply clarsimp
   apply(prop_tac "guarded_pas_domain initial_aag (internal_state_if s)")
    apply(frule guarded_pas_domain_if)
    apply(metis guarded_pas_domain_cur)
   apply(clarsimp simp:guarded_pas_domain_def)
   apply(erule impE)
    (* That the current thread isn't the idle thread. *)
    apply(frule reachable_invs_if[THEN invs_if_Invs, simplified Invs_def])
    apply clarsimp
    apply(frule cur_thread_idle)
    apply blast
   using domains_distinct
   unfolding pas_domains_distinct_def
   apply(erule_tac x="cur_domain (internal_state_if s)" in allE)
   apply force
  unfolding ta_subset_inv_def pas_addrs_accessible_to_def pas_labels_accessible_to_def
  apply clarsimp
  by force

(* note here that we are talking about the TA set being a subset of the
   STARTING state's domain *)
lemma oldclean_preserves_touched_addrs_inv:
  "reachable s \<Longrightarrow>
  (s, s') \<in> fourways_oldclean \<Longrightarrow>
  \<comment> \<open>This is @{term\<open>touched_addrs_inv\<close>} but with the TA set required to be a subset
    of the addresses of the old domain (in s), not the new domain (in s').\<close>
  snd ` touched_addresses s' \<subseteq> all_paddrs_of (userPart s) \<union> kernel_shared_precise"
  using oldclean_preserves_ta_subset_inv ta_subset_inv_to_locale_form' initial_aag_separation_kernel
  by blast


(* I don't think this should be too bad. Can do this with hoare logic stuff I think. *)
lemma domainswitch_follows_get_next_domain:
  "(s1, s2) \<in> Step () \<Longrightarrow>
  will_domain_switch s1 \<Longrightarrow>
  userPart s2 = get_next_domain s1"
  sorry

lemma non_domainswitch_unchanged_domain:
  "(s1, s2) \<in> Step () \<Longrightarrow>
  \<not>will_domain_switch s1 \<Longrightarrow>
  userPart s2 = userPart s1"
  sorry

lemma non_domainswitch_uwr_determined:
  "(s1, s2) \<in> Step () \<Longrightarrow>
  \<not>will_domain_switch s1 \<Longrightarrow>
  is_uwr_determined s1"
  by (simp add: is_uwr_determined_def)

lemma external_uwr_same_domain:
  "uwr2 s PSched t \<Longrightarrow>
  userPart s = userPart t"
  apply (clarsimp simp: uwr_def sameFor_def sameFor_scheduler_def domain_fields_equiv_def
                        userPart_def partition_def)
  done

(* "simple_steps", which states that steps will or won't domain-switch,
            and some basic properties about these steps *)
lemma simple_steps:
  "(s, s') \<in> ni.Step () \<Longrightarrow>
       \<not> will_domain_switch s \<and>
       userPart s' = userPart s \<and> is_uwr_determined s \<or>
       will_domain_switch s \<and> userPart s' = get_next_domain s"
  apply (case_tac "will_domain_switch s"; clarsimp)
   apply (erule domainswitch_follows_get_next_domain; simp)
  apply (rule conjI, erule(1) non_domainswitch_unchanged_domain)
  apply (rule non_domainswitch_uwr_determined; simp)
  done

lemma part_is_userPart_or_Sched:
  "part s = userPart s \<or> part s = PSched"
  apply (clarsimp simp: userPart_def part_def)
  done

lemma uwr_and_normal_step_gives_ta_equiv:
  "\<lbrakk>reachable s; reachable t; uwr2 s PSched t;
     uwr2 s (userPart s) t; \<not> will_domain_switch s;
     (s, s') \<in> ni.Step (); (t, t') \<in> ni.Step ()\<rbrakk>
    \<Longrightarrow> ii.touched_addresses t' = ii.touched_addresses s'"
  apply (prop_tac "uwr2 s' (userPart s') t'")
   apply (prop_tac "uwr2 s' (userPart s) t'")
    apply (insert confidentiality_u [simplified confidentiality_u_def])
    apply (drule_tac x="()" in spec)
    apply (drule_tac x="userPart s" in spec)
    apply (drule_tac x=s in spec)
    apply (drule_tac x=t in spec)
    apply clarsimp
    apply (prop_tac "(policy2 (part s) (userPart s) \<longrightarrow> uwr2 s (part s) t)"; clarsimp)
     apply (insert part_is_userPart_or_Sched [of s], erule disjE; clarsimp)
    apply (cases s', clarsimp, cases t', clarsimp)
   using non_domainswitch_unchanged_domain apply presburger
  apply (rule sym, rule uwr_equates_touched_addresses, assumption)
  done

(* here we require that the output of oldclean will hold equality on TA *)
lemma oldclean_preserves_ta_equiv:
  "\<lbrakk>reachable s; reachable t;
  uwr2 s PSched t;
  uwr2 s (userPart s) t;
  is_uwr_determined s;
  (s, s') \<in> fourways_oldclean; (t, t') \<in> fourways_oldclean\<rbrakk> \<Longrightarrow>
  ii.touched_addresses t' = ii.touched_addresses s'"
  sorry

lemma uwr_determined_steps_ta_equiv:
  "\<lbrakk>reachable s; reachable t;
    uwr2 s PSched t;
    uwr2 s d t; userPart s = d; is_uwr_determined s;
        step = ni.Step () \<and> \<not> will_domain_switch s \<or>
        step = fourways_oldclean \<or> step = fourways_newclean;
        (s, s') \<in> step; (t, t') \<in> step\<rbrakk>
       \<Longrightarrow> ii.touched_addresses t' = ii.touched_addresses s'"
  apply (elim disjE; clarsimp)
    apply (erule uwr_and_normal_step_gives_ta_equiv; assumption)
   apply (erule oldclean_preserves_ta_equiv; assumption)
  apply (clarsimp simp: fourways_newclean_def)
  apply (rule sym, rule uwr_equates_touched_addresses, assumption)  
  done

lemma dirty_step_ta_equiv:
  "\<lbrakk>ii.touched_addresses t = ii.touched_addresses s;
  (s, s') \<in> fourways_dirty;
  (t, t') \<in> fourways_dirty\<rbrakk> \<Longrightarrow>
  ii.touched_addresses t' = ii.touched_addresses s'"
  apply (clarsimp simp: fourways_dirty_def)
  done

(* we discharge a few locale assumptions that assume `is_publicly_determined`,
   as we never allow this property for this integration. *)
lemma ex_publicly_determined_quodlibet:
  "is_publicly_determined s \<Longrightarrow> P"
  by (simp add: is_publicly_determined_def)

(* here we require that the we have the UWR at the start of the dirty step. *)
lemma running_uwr_available_for_newclean:
  "\<lbrakk>uwr2 s PSched t;
  uwr2 s d t;
  d = userPart sc;
  reachable s; reachable t;
  will_domain_switch s;
  (s, sa) \<in> fourways_oldclean; (t, ta) \<in> fourways_oldclean;
  (sa, sb) \<in> fourways_dirty;   (ta, tb) \<in> fourways_dirty;
  (sb, sc) \<in> fourways_gadget;  (tb, tc) \<in> fourways_gadget;
  is_uwr_determined sc; is_uwr_determined tc\<rbrakk> \<Longrightarrow>
  uwr2 sc d tc"
  sorry

lemma fourways_properties:
  "\<lbrakk>(s1, s5) \<in> ni.Step (); reachable s1; will_domain_switch s1;
        (s1, s2) \<in> fourways_oldclean; (s2, s3) \<in> fourways_dirty;
        (s3, s4) \<in> fourways_gadget\<rbrakk>
       \<Longrightarrow> is_uwr_determined s1 \<and>
           snd ` ii.touched_addresses s2
           \<subseteq> {a. addr_domain initial_aag a = userPart s1} \<union>
              kernel_shared_precise \<and>
           s3 = s2 \<and>
           step_is_only_timeprotection_gadget s3 s4 \<and>
           is_uwr_determined s4
          \<and> userPart s2 = get_next_domain s1 \<and>
           userPart s3 = get_next_domain s1 \<and>
           userPart s4 = get_next_domain s1"
  apply (clarsimp simp: fourways_dirty_def fourways_newclean_def is_uwr_determined_def)
  apply (intro conjI)
   apply (rule oldclean_preserves_touched_addrs_inv[simplified all_paddrs_of_def]; simp)
  (* here we need a definition of "step_is_only_timeprotection_gadget" to do something
      useful *)
  sorry

interpretation ma?:time_protection_system PSched fch_lookup fch_read_impact fch_write_impact
  empty_fch fch_flush_cycles fch_flush_WCET pch_lookup pch_read_impact pch_write_impact do_pch_flush
  pch_flush_cycles pch_flush_WCET collides_in_pch read_cycles write_cycles
  "addr_domain initial_aag" "addr_colour initial_aag" colour_userdomain
  userPart uwr nlds select_trace
  "big_step_ADT_A_if utf" s0 "policyFlows (pasPolicy initial_aag)"
  _ is_publicly_determined is_uwr_determined touched_addresses all_paddrs_of
  "\<lambda>u s. snd ` touched_addresses s \<subseteq> all_paddrs_of u \<union> kernel_shared_precise"
  "\<lambda>u u' s. touched_addresses s \<subseteq> {(v, p) |v p.
                           p \<in> all_paddrs_of u \<union> all_paddrs_of u' \<union> kernel_shared_precise}"
  will_domain_switch _ _ _ _ get_next_domain
  fourways_oldclean fourways_dirty fourways_gadget fourways_newclean
  _ True
  
  (* separate the locale instantiation obligations from definitions, and
     dispatch the definition subgoals. *)
  apply (try_solve_all \<open>simp add: all_paddrs_of_def\<close>)
  
  (* now we prove the locale assumptions *)
  apply unfold_locales
                      (* external uwr is equivalence *)
                      apply (rule uwr_equiv_rel)
                     (* external uwr (sched) equalises curdomain *)
                     apply (erule external_uwr_same_domain)
                    (* the policy allows flows from the scheduler to everybody *)
                    apply (rule schedFlowsToAll)
                   (* only the scheduler can flow to the scheduler *)
                   apply (erule schedNotGlobalChannel)
                  (* external uwr (sched) equalises curdomain (again...) *)
                  apply (erule external_uwr_same_domain [OF uwr_sym])
                 (* will_domain_switch_public *)
                 apply (erule will_domain_switch_from_uwr)
                (* next_latest_domainswitch_in_future *)
                apply (rule nlds_in_future)
               (* next_latest_domainswitch_flatsteps *)
               apply (erule nlds_flatsteps; assumption)
              (* get_next_domain_not_sched *)
              apply (rule get_next_domain_not_Sched)
             (* current_domain_not_Sched *)
             apply (rule current_domain_not_Sched)
            (* get_next_domain_public *)
            apply (erule get_next_domain_public)
           (* touched addresses inv *)
           using initial_aag_separation_kernel
           apply (erule subset_inv_proof; assumption)
          (* simple_steps *)
          apply (erule simple_steps)
         (* external_uwr_step_same_touched_addrs:
            step_is_uwr_determimed for particular steps tells us that the
            output touchedaddresses depend only on uwr *)
         apply (rule uwr_determined_steps_ta_equiv; assumption)
        (* external_uwr_same_touched_addrs *)
        apply (rule external_uwr_same_touched_addrs; assumption)
       (* dirty step TA equivalence *)
       apply (erule dirty_step_ta_equiv; assumption)
      (* public_uwr_available_for_dirty_step *)
      apply (rule ex_publicly_determined_quodlibet; assumption)
     (* same_ta_available_for_dirty_step *)
     apply (rule ex_publicly_determined_quodlibet; assumption)
    (* running_uwr_available_for_newclean *)
    apply (rule running_uwr_available_for_newclean; assumption)
   (* can_split_four_ways *)
   apply (rule domainswitch_splits_four_ways)
  (* fourways_properties - facts about various states
     within the fourways transitions *)
  apply (simp only: if_True)
  apply (erule fourways_properties; assumption)
  done
end

end
