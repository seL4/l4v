(*
 * Copyright 2021, UNSW (ABN 57 195 873 179),
 * Copyright 2021, The University of Melbourne (ABN 84 002 705 224).
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory TimeProtectionIntegration
imports TimeProtection
  "InfoFlow.Noninterference"
begin


locale integration = 
  Noninterference_valid_initial_state _ _ _ _ initial_aag +
  tph?:time_protection_hardware
    "TYPE('fch \<times> 'fch_cachedness \<times> 'pch \<times> 'pch_cachedness \<times> 'partition \<times> 'colour)"
  (* re-fixed here just to align the 'partition type *)
  for initial_aag :: "'partition subject_label PAS"
begin

type_alias tpdomain = TimeProtection.domain

type_synonym if_other_state = "(user_context \<times> det_ext Structures_A.state) \<times> sys_mode"

\<comment> \<open> since we define the 'domain' type in TimeProtection, we need to convert the
    'partition' type from InfoFlow indo this type (and back)\<close>
definition partition_to_domain :: "'partition partition \<Rightarrow> 'partition tpdomain" where
  "partition_to_domain p \<equiv> case p of
                             PSched \<Rightarrow> Sched |
                             Partition x \<Rightarrow> User x"

definition domain_to_partition :: "'partition tpdomain \<Rightarrow> 'partition partition" where
  "domain_to_partition d \<equiv> case d of
                             Sched \<Rightarrow> PSched |
                             User x \<Rightarrow> Partition x"

lemma partition_is_domain [simp]:
  "domain_to_partition (partition_to_domain p) = p"
  by (clarsimp simp:partition_to_domain_def domain_to_partition_def split:partition.split)

lemma domain_is_partition [simp]:
  "partition_to_domain (domain_to_partition d) = d"
  by (clarsimp simp:partition_to_domain_def domain_to_partition_def split:domain.split)

\<comment> \<open> parameters to the tp locales \<close>
definition if_A where
  "if_A \<equiv> big_step_ADT_A_if utf"

definition if_s0 where
  "if_s0 \<equiv> s0"

definition if_current_domain :: "if_other_state \<Rightarrow> 'partition tpdomain" where
  "if_current_domain os \<equiv> partition_to_domain (part os)"

definition if_uwr :: "'partition tpdomain \<Rightarrow> (if_other_state \<times> if_other_state) set" where
  "if_uwr d \<equiv> uwr (domain_to_partition d)"

(*FIXME: all of this domain/policy stuff is getting messy *)
definition if_policy :: "('partition tpdomain \<times> 'partition tpdomain) set" where
  "if_policy \<equiv> {(u, u'). policy2 (domain_to_partition u) (domain_to_partition u')}"

thm confidentiality_u


interpretation ma?:time_protection_system _ if_A if_s0 if_current_domain if_uwr if_policy
  apply unfold_locales


  (*
  fixes
    select_trace ::
      "('other_state \<times> ('fch, 'pch) state \<Rightarrow> (vaddr \<times> paddr) set \<Rightarrow> trace_unit list set)
       \<Rightarrow> 'other_state \<times> ('fch, 'pch) state \<Rightarrow> (vaddr \<times> paddr) set \<Rightarrow> trace_unit list"
    and A :: "('a, 'other_state, unit) data_type"
    and s0 :: "'other_state"
    and current_domain :: "'other_state \<Rightarrow> 'userdomain domain"
    and external_uwr :: "'userdomain domain \<Rightarrow> ('other_state \<times> 'other_state) set"
    and policy :: "('userdomain domain \<times> 'userdomain domain) set"
    and out :: "'userdomain domain \<Rightarrow> 'other_state \<Rightarrow> 'p"
    and collides_in_pch :: "paddr \<Rightarrow> paddr \<Rightarrow> bool"  (infix \<open>coll\<close> 50)
    and fch_lookup :: "'fch \<Rightarrow> vaddr \<Rightarrow> 'fch_cachedness"
    and pch_lookup :: "'pch \<Rightarrow> paddr \<Rightarrow> 'pch_cachedness"
    and fch_read_impact :: "vaddr \<Rightarrow> 'fch \<Rightarrow> 'fch"
    and pch_read_impact :: "paddr \<Rightarrow> 'pch \<Rightarrow> 'pch"
    and fch_write_impact :: "vaddr \<Rightarrow> 'fch \<Rightarrow> 'fch"
    and pch_write_impact :: "paddr \<Rightarrow> 'pch \<Rightarrow> 'pch"
    and read_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> nat"
    and write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> nat"
    and empty_fch :: "'fch"
    and fch_flush_cycles :: "'fch \<Rightarrow> nat"
    and pch_flush_WCET :: "paddr set \<Rightarrow> nat"
    and fch_flush_WCET :: "nat"
    and do_pch_flush :: "'pch \<Rightarrow> paddr set \<Rightarrow> 'pch"
    and pch_flush_cycles :: "'pch \<Rightarrow> paddr set \<Rightarrow> nat"
    and addr_domain :: "paddr \<Rightarrow> 'userdomain domain"
    and addr_colour :: "paddr \<Rightarrow> 'colour"
    and colour_userdomain :: "'colour \<Rightarrow> 'userdomain"
    and touched_addrs :: "'other_state \<Rightarrow> (vaddr \<times> paddr) set"
    and step_is_publicly_determined :: "'other_state \<Rightarrow> bool"
    and step_is_uwr_determined :: "'other_state \<Rightarrow> bool"
    and next_latest_domainswitch_start :: "nat \<Rightarrow> nat"
    and will_domain_switch :: "'other_state \<Rightarrow> bool"
    and domainswitch_start_delay_WCT :: "nat"
    and dirty_step_WCET :: "nat"
    and initial_pch :: "'pch"
    and get_next_domain :: "'other_state \<Rightarrow> 'userdomain domain"
    and get_domainswitch_middle_state :: "'other_state \<Rightarrow> 'other_state"
    and get_domainswitch_final_state :: "'other_state \<Rightarrow> 'other_state"
    and step_is_only_timeprotection_gadget :: "'other_state \<Rightarrow> 'other_state \<Rightarrow> bool"
*)
end

end