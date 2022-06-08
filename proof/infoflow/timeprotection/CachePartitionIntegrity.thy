(*
 * Copyright 2022, The University of Melbourne (ABN 84 002 705 224)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CachePartitionIntegrity
imports InfoFlow.ADT_IF
begin

context Arch begin

definition policy_owned_addrs :: "'a PAS \<Rightarrow> domain \<Rightarrow> obj_ref set" where
  "policy_owned_addrs aag d \<equiv> {p. pasObjectAbs aag p \<in> pasDomainAbs aag d}"

definition all_labels_are_owned :: "'a PAS \<Rightarrow> bool" where
  "all_labels_are_owned aag \<equiv> \<forall>l. \<exists>d. l \<in> pasDomainAbs aag d"

definition policy_accessible_labels :: "'a PAS \<Rightarrow> domain \<Rightarrow> 'a set" where
  "policy_accessible_labels aag d \<equiv> pasDomainAbs aag d \<union>
     \<Union> {ls. \<exists>l \<in> pasDomainAbs aag d.
       ls = subjectReads (pasPolicy aag) l \<or>
       ls = subjectAffects (pasPolicy aag) l}"

definition policy_accessible_addrs :: "'a PAS \<Rightarrow> domain \<Rightarrow> obj_ref set" where
  "policy_accessible_addrs aag d \<equiv> {p. pasObjectAbs aag p \<in> policy_accessible_labels aag d}"

definition policy_accessible_domains :: "'a PAS \<Rightarrow> domain \<Rightarrow> domain set" where
  "policy_accessible_domains aag d \<equiv>
     {d'. policy_owned_addrs aag d' \<inter> policy_accessible_addrs aag d \<noteq> {}}"

end

locale ArchL2Partitioned = Arch +
  fixes paddr_L2_domain :: "paddr \<Rightarrow> domain"
begin

definition domain_L2_partition :: "domain \<Rightarrow> paddr set" where
  "domain_L2_partition d \<equiv> {pa. paddr_L2_domain pa = d}"

definition policy_accessible_partitions :: "'a PAS \<Rightarrow> domain \<Rightarrow> paddr set" where
  "policy_accessible_partitions aag d \<equiv>
     \<Union> {as. \<exists>d \<in> policy_accessible_domains aag d. as = domain_L2_partition d}"

abbreviation touched_addresses' :: "det_state \<Rightarrow> machine_word set" where
  "touched_addresses' s \<equiv> touched_addresses (machine_state s)"

\<comment> \<open>Important: We assume that the @{term\<open>touched_addresses\<close>} set will only be used to track the
    virtual addresses of kernel objects; therefore its physical address footprint is just the
    image of @{term\<open>addrFromKPPtr\<close>} because @{term\<open>pspace_in_kernel_window\<close>} tells us all
    kernel objects live in the kernel window.\<close>
abbreviation p_footprint :: "machine_word set \<Rightarrow> paddr set" where
  "p_footprint vas \<equiv> addrFromKPPtr ` vas"

definition ta_subset_owned_partition :: "det_state \<Rightarrow> bool" where
  "ta_subset_owned_partition s \<equiv>
     p_footprint (touched_addresses' s) \<subseteq>
     domain_L2_partition (cur_domain s)"

\<comment> \<open>Partition subset property: That only paddrs in policy-accessible partitions are ever accessed.\<close>
definition ta_subset_accessible_partitions :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_partitions aag s \<equiv>
     p_footprint (touched_addresses' s) \<subseteq>
     policy_accessible_partitions aag (cur_domain s)"

\<comment> \<open>That each domain's labels' addresses are located in that domain's partition.\<close>
definition owned_addrs_well_partitioned :: "'a PAS \<Rightarrow> bool" where
  "owned_addrs_well_partitioned aag \<equiv> \<forall> d.
     p_footprint (policy_owned_addrs aag d) \<subseteq> domain_L2_partition d"

\<comment> \<open>That accessible labels' addresses are located in accessible domains' partitions.\<close>
definition accessible_addrs_well_partitioned :: "'a PAS \<Rightarrow> bool" where
  "accessible_addrs_well_partitioned aag \<equiv> \<forall> d.
     p_footprint (policy_accessible_addrs aag d) \<subseteq> policy_accessible_partitions aag d"

\<comment> \<open>If every domain's address is confined to its partition, then all accessible addresses, due to
  belonging to accessible domains, are confined to the union of those domains' partitions.\<close>
lemma owned_to_accessible_addrs_well_partitioned:
  "owned_addrs_well_partitioned aag \<Longrightarrow>
   all_labels_are_owned aag \<Longrightarrow>
   accessible_addrs_well_partitioned aag"
  unfolding accessible_addrs_well_partitioned_def
  apply clarsimp
  apply(rename_tac d va)
  \<comment> \<open>We consider each address \<open>va\<close> that is accessible to, though not necessarily owned by, \<open>d\<close>.
      We know the L2 partitioning scheme assigns the physical address of \<open>va\<close> to some domain
        \<open>paddr_L2_domain (addrFromKPPtr va)\<close>
      But instead of that, we use the domain \<open>d'\<close> determined by the domain assignment
      (via @{term\<open>pasDomainAbs\<close>}) of \<open>va\<close>'s label (given by @{term\<open>pasObjectAbs\<close>}),
      which @{term\<open>all_labels_are_owned\<close>} tells us exists.\<close>
  apply(prop_tac "\<exists>d'. pasObjectAbs aag va \<in> pasDomainAbs aag d'")
   apply(force simp:all_labels_are_owned_def)
  apply(clarsimp simp:policy_accessible_partitions_def policy_accessible_domains_def)
  apply(rename_tac d va d')
  apply(rule_tac x="domain_L2_partition d'" in exI)
  apply(rule conjI)
   apply(rule_tac x=d' in exI)
   apply clarsimp
   \<comment> \<open>Note: \<open>va \<in> policy_accessible_addrs aag d\<close> is what tells
       the intersection of the two sets is nonempty.\<close>
   apply(erule_tac x=va in in_empty_interE)
    apply(force simp:policy_owned_addrs_def)
   apply force
  \<comment> \<open>We now use @{term\<open>owned_addrs_well_partitioned\<close>} to tell us \<open>va\<close> is in \<open>d'\<close>'s partition.\<close>
  apply(force simp:owned_addrs_well_partitioned_def policy_owned_addrs_def)
  done

section \<open> Subset of accessible addresses \<close>

\<comment> \<open>Address subset property: That only the paddrs of policy-accessible labels are ever accessed.\<close>
definition ta_subset_accessible_addrs :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_addrs aag s \<equiv>
     p_footprint (touched_addresses' s) \<subseteq>
     p_footprint (policy_accessible_addrs aag (cur_domain s))"

theorem ta_subset_accessible_addrs_to_partitions:
  "ta_subset_accessible_addrs aag s \<Longrightarrow>
   accessible_addrs_well_partitioned aag \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  unfolding ta_subset_accessible_partitions_def ta_subset_accessible_addrs_def
    accessible_addrs_well_partitioned_def
  by blast

(* If it's easier to prove `owned_addrs_well_partitioned` than
   `accessible_addrs_well_partitioned` then we'll additionally need `all_labels_are_owned`.
   But the benefit is questionable - after all, neither of them rely on the state. *)
lemma ta_subset_accessible_addrs_to_partitions_alternative:
  "ta_subset_accessible_addrs aag s \<Longrightarrow>
   all_labels_are_owned aag \<Longrightarrow>
   owned_addrs_well_partitioned aag \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  by (force intro:ta_subset_accessible_addrs_to_partitions
    owned_to_accessible_addrs_well_partitioned)

\<comment> \<open>Proofs of TA subset invariance over seL4 kernel\<close>

abbreviation ta_subset_inv :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_inv \<equiv> ta_subset_accessible_addrs"

(* For check_active_irq_if *)

lemma do_machine_op_ta_subset_inv:
  "do_machine_op mop \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

(* For kernel_entry_if *)

lemma set_object_ta_subset_inv:
  "set_object ptr obj \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma syscall_ta_subset_inv:
  "syscall m_fault h_fault m_error h_error m_finalise \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma resolve_address_bits'_ta_subset_inv:
  "resolve_address_bits' z capcref \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma lookup_extra_caps_ta_subset_inv:
  "lookup_extra_caps thread buffer mi \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma set_thread_state_ta_subset_inv:
  "set_thread_state ref ts \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma get_receive_slots_ta_subset_inv:
  "get_receive_slots thread bufopt \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma set_cdt_ta_subset_inv:
  "set_cdt t \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma set_original_ta_subset_inv:
  "set_original slot v \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma cap_insert_ta_subset_inv:
  "cap_insert new_cap src_slot dest_slot \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma transfer_caps_loop_ta_subset_inv:
  "transfer_caps_loop ep rcv_buffer n caps slots mi \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma send_ipc_ta_subset_inv:
  "send_ipc block call badge can_grant can_grant_reply thread epptr \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_read_registers_ta_subset_inv:
  "decode_read_registers data cap \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_write_registers_ta_subset_inv:
  "decode_write_registers data cap \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_copy_registers_ta_subset_inv:
  "decode_copy_registers data cap extra_caps \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma send_fault_ipc_ta_subset_inv:
  "send_fault_ipc tptr fault \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_invocation_ta_subset_inv:
  "decode_invocation label args cap_index slot cap excaps \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma delete_objects_ta_subset_inv:
  "delete_objects ptr bits \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma reset_untyped_cap_ta_subset_inv:
  "reset_untyped_cap src_slot \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma retype_region_ta_subset_inv:
  "retype_region ptr numObjects o_bits type dev \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma create_cap_ta_subset_inv:
  "create_cap type bits untyped is_device dest_oref \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma invoke_untyped_ta_subset_inv:
  "invoke_untyped ui \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma cancel_all_ipc_ta_subset_inv:
  "cancel_all_ipc epptr \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma cancel_all_signals_ta_subset_inv:
  "cancel_all_signals ntftnptr \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma set_irq_state_ta_subset_inv:
  "set_irq_state state irq \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma reply_cancel_ipc_ta_subset_inv:
  "reply_cancel_ipc tptr \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma update_waiting_ntfn_ta_subset_inv:
  "update_waiting_ntfn ntfnptr queue bound_tcb badge \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma send_signal_ta_subset_inv:
  "send_signal ntfnptr badge \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma suspend_ta_subset_inv:
  "suspend thread \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma restart_ta_subset_inv:
  "restart thread \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma cap_swap_ta_subset_inv:
  "cap_swap cap1 slot1 cap2 slot2 \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma empty_slot_ta_subset_inv:
  "empty_slot slot cleanup_info \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma delete_asid_pool_ta_subset_inv:
  "delete_asid_pool base ptr \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma rec_del_ta_subset_inv:
  "rec_del rdc \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma check_cap_at_ta_subset_inv:
  "check_cap_at cap slot m \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma invoke_domain_ta_subset_inv:
  "invoke_domain thread domain \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma do_reply_transfer_ta_subset_inv:
  "do_reply_transfer sender receiver slot grant  \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma cap_move_ta_subset_inv:
  "cap_move new_cap src_slot dest_slot \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma cancel_badged_sends_ta_subset_inv:
  "cancel_badged_sends epptr badge \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma invoke_irq_handler_ta_subset_inv:
  "invoke_irq_handler irqh_invocation \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma cap_revoke_ta_subset_inv:
  "cap_revoke slot \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma perform_asid_control_invocation_ta_subset_inv:
  "perform_asid_control_invocation iv \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma handle_yield_ta_subset_inv:
  "handle_yield \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma handle_interrupt_ta_subset_inv:
  "handle_interrupt irq \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma handle_event_ta_subset_inv:
  "handle_event ev \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

(* For schedule_if *)

lemma switch_to_idle_thread_ta_subset_inv:
  "switch_to_idle_thread \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma schedule_choose_new_thread_ta_subset_inv:
  "schedule_choose_new_thread \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma switch_to_thread_ta_subset_inv:
  "switch_to_thread t \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma schedule_ta_subset_inv:
  "schedule \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

\<comment> \<open> Instead of @{term\<open>call_kernel\<close>}, prove for monads used for each step of @{term\<open>ADT_A_if\<close>}. \<close>

crunches check_active_irq_if
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps)

lemma do_user_op_if_ta_subset_inv:
  "do_user_op_if uop tc \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

crunches kernel_entry_if
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps simp:crunch_simps)

crunches handle_preemption_if
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps)

crunches schedule_if
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps)

crunches kernel_exit_if
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps)

\<comment> \<open> Now that it's true for the monads of @{term\<open>ADT_A_if\<close>}, seems it's true
     for @{term\<open>call_kernel\<close>} as well. \<close>

crunches call_kernel
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps)

end

locale ADT_IF_L2Partitioned = ArchL2Partitioned +
  fixes initial_aag :: "'a PAS"
  fixes s0 :: det_state
  assumes init_ta_empty:
    "touched_addresses' s0 = {}"
begin

lemma "ta_subset_accessible_addrs aag s0"
  unfolding ta_subset_accessible_addrs_def
  using init_ta_empty
  by blast

end

end