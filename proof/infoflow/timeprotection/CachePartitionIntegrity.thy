(*
 * Copyright 2022, The University of Melbourne (ABN 84 002 705 224)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CachePartitionIntegrity
imports InfoFlow.ADT_IF
begin

section \<open> Kernel heap-agnostic subset property definitions \<close>

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
   fixes paddr_L2_colour :: "paddr \<Rightarrow> 'colour"
   fixes L2_colour_domains :: "'colour \<Rightarrow> domain set"
begin

definition domain_L2_partition :: "domain \<Rightarrow> paddr set" where
  "domain_L2_partition d \<equiv> {pa. d \<in> L2_colour_domains (paddr_L2_colour pa)}"

definition policy_accessible_partitions :: "'a PAS \<Rightarrow> domain \<Rightarrow> paddr set" where
  "policy_accessible_partitions aag d \<equiv>
     \<Union> {as. \<exists>d \<in> policy_accessible_domains aag d. as = domain_L2_partition d}"

\<comment> \<open>Important: We assume that the @{term\<open>touched_addresses\<close>} set will only be used to track the
    virtual addresses of kernel objects; therefore its physical address footprint is just the
    image of @{term\<open>addrFromKPPtr\<close>} because @{term\<open>pspace_in_kernel_window\<close>} tells us all
    kernel objects live in the kernel window.\<close>
abbreviation to_phys :: "machine_word set \<Rightarrow> paddr set" where
  "to_phys vas \<equiv> addrFromKPPtr ` vas"

abbreviation phys_touched :: "det_state \<Rightarrow> paddr set" where
  "phys_touched s \<equiv> to_phys (touched_addresses (machine_state s))"

definition ta_subset_owned_partition :: "det_state \<Rightarrow> bool" where
  "ta_subset_owned_partition s \<equiv>
     phys_touched s \<subseteq> domain_L2_partition (cur_domain s)"

\<comment> \<open>Partition subset property: That only paddrs in policy-accessible partitions are ever accessed.\<close>
definition ta_subset_accessible_partitions :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_partitions aag s \<equiv>
     phys_touched s \<subseteq> policy_accessible_partitions aag (cur_domain s)"

\<comment> \<open>That each domain's labels' addresses are located in that domain's partition.\<close>
definition owned_addrs_well_partitioned :: "'a PAS \<Rightarrow> bool" where
  "owned_addrs_well_partitioned aag \<equiv> \<forall> d.
     to_phys (policy_owned_addrs aag d) \<subseteq> domain_L2_partition d"

\<comment> \<open>That accessible labels' addresses are located in accessible domains' partitions.\<close>
definition accessible_addrs_well_partitioned :: "'a PAS \<Rightarrow> bool" where
  "accessible_addrs_well_partitioned aag \<equiv> \<forall> d.
     to_phys (policy_accessible_addrs aag d) \<subseteq> policy_accessible_partitions aag d"

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
      We know the L2 partitioning scheme assigns the physical address of \<open>va\<close> to some colour
        \<open>paddr_L2_colour (addrFromKPPtr va)\<close>
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

\<comment> \<open>Address subset property: That only the paddrs of policy-accessible labels are ever accessed.\<close>
definition ta_subset_accessible_addrs :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_addrs aag s \<equiv>
     phys_touched s \<subseteq> to_phys (policy_accessible_addrs aag (cur_domain s))"

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

end

section \<open> Subset property definitions that rely on the kernel heap status of objects \<close>

context Arch begin

\<comment> \<open> Adapted from Scott's definition of @{term\<open>touch_objects\<close>}.
  I don't believe any existing definition gets the @{term\<open>obj_addrs\<close>}
  conditionally on whether the object is on the @{term\<open>kheap\<close>} like this. -robs \<close>
definition obj_kheap_addrs :: "'a state \<Rightarrow> obj_ref \<Rightarrow> machine_word set" where
  "obj_kheap_addrs s p \<equiv> case kheap s p of
     None \<Rightarrow> {} |
     Some ko \<Rightarrow> obj_addrs ko p"

\<comment> \<open>That no object is allocated on the @{term\<open>kheap\<close>} such that it straddles the addresses
    assigned to two different labels according to @{term\<open>pasObjectAbs\<close>}}.\<close>
definition no_label_straddling_objs :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "no_label_straddling_objs aag s \<equiv> \<forall>l p. pasObjectAbs aag p = l \<longrightarrow>
     (case kheap s p of
       Some ko \<Rightarrow> \<forall>va \<in> obj_addrs ko p. pasObjectAbs aag va = l |
       None \<Rightarrow> True)"

\<comment> \<open>New property discussed with Gerwin Klein (@lsf37) - haven't figured out its application yet.\<close>
definition ta_obj_projections_subset_ta :: "det_state \<Rightarrow> bool" where
  "ta_obj_projections_subset_ta  s \<equiv>
     (\<Union> (obj_kheap_addrs s ` (touched_addresses (machine_state s)))) \<subseteq>
     (touched_addresses (machine_state s)) "

end

context ArchL2Partitioned begin

\<comment> \<open>That each domain's objects stay confined to that domain's partition.\<close>
definition owned_objs_well_partitioned :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "owned_objs_well_partitioned aag s \<equiv> \<forall> d.
     to_phys (\<Union> (obj_kheap_addrs s ` policy_owned_addrs aag d)) \<subseteq>
     domain_L2_partition d"

\<comment> \<open>That accessible objects will only lie inside accessible domains' partitions.\<close>
definition accessible_objs_well_partitioned :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "accessible_objs_well_partitioned aag s \<equiv>
     to_phys (\<Union> (obj_kheap_addrs s ` policy_accessible_addrs aag (cur_domain s))) \<subseteq>
     policy_accessible_partitions aag (cur_domain s)"

lemma accessible_objs_subset_accessible_addrs:
  "no_label_straddling_objs aag s \<Longrightarrow>
   to_phys (\<Union> (obj_kheap_addrs s ` policy_accessible_addrs aag (cur_domain s))) \<subseteq>
   to_phys (policy_accessible_addrs aag (cur_domain s))"
  unfolding no_label_straddling_objs_def
  apply(clarsimp simp:obj_kheap_addrs_def image_def split:option.splits)
  apply(rename_tac vas p va)
  apply(rule_tac x=va in bexI)
   apply force
  apply(erule_tac x=p in allE)
  apply(case_tac "kheap s p")
   apply force
  apply clarsimp
  apply(erule_tac x=va in ballE)
   apply(force simp:policy_accessible_addrs_def)
  apply(force simp:policy_accessible_addrs_def)
  done

\<comment> \<open>That it's sufficient here to prove an invariant that's agnostic of colours, domains, etc.
    rather than proving \<open>owned_objs_well_partitioned\<close> as an invariant directly.\<close>
lemma owned_addrs_to_objs_well_partitioned:
  "owned_addrs_well_partitioned aag \<Longrightarrow>
   no_label_straddling_objs aag s \<Longrightarrow>
   owned_objs_well_partitioned aag s"
  unfolding owned_addrs_well_partitioned_def no_label_straddling_objs_def
    owned_objs_well_partitioned_def
  apply clarsimp
  apply(rename_tac d va p)
  apply(clarsimp simp:obj_kheap_addrs_def image_def split:option.splits)
  apply(erule_tac x=d in allE)
  apply(erule_tac x=p in allE)
  apply clarsimp
  apply(rename_tac d va p ko)
  apply(erule_tac x=va in ballE)
   apply(erule_tac c="addrFromKPPtr va" in subsetCE)
    apply(clarsimp simp:policy_owned_addrs_def)
    apply metis
   apply force
  apply force
  done

\<comment> \<open>If every domain's objects is confined to its partition, then all accessible objects, due to
  belonging to accessible domains, are confined to the union of those domains' partitions. -robs\<close>
lemma owned_to_accessible_objs_well_partitioned:
  "\<lbrakk>all_labels_are_owned aag; owned_objs_well_partitioned aag s\<rbrakk> \<Longrightarrow>
   accessible_objs_well_partitioned aag s"
  unfolding accessible_objs_well_partitioned_def
  apply clarsimp
  apply(rename_tac va y)
  \<comment> \<open>We consider each accessible object, call it \<open>y\<close>.\<close>
  (* Things that matter for 'y' to be a valid object reference:
     - It is allocated, i.e. kheap s y \<noteq> None.
       This follows from the definition of obj_kheap_addrs. *)
  \<comment> \<open>We know the L2 partitioning scheme assigns the physical address of \<open>y\<close> to some domain
        \<open>paddr_L2_colour (addrFromKPPtr y)\<close>
      But instead of that, we use the domain determined by the domain assignment
      (via @{term\<open>pasDomainAbs\<close>}) of y's label (given by @{term\<open>pasObjectAbs\<close>}),
      which @{term\<open>all_labels_are_owned\<close>} tells us exists.\<close>
  apply(prop_tac "\<exists>yd. pasObjectAbs aag y \<in> pasDomainAbs aag yd")
   apply(force simp:all_labels_are_owned_def)
  apply(clarsimp simp:policy_accessible_partitions_def policy_accessible_domains_def)
  apply(rule_tac x="domain_L2_partition yd" in exI)
  apply(rule conjI)
   apply(rule_tac x=yd in exI)
   apply clarsimp
   \<comment> \<open>Note: \<open>y \<in> policy_accessible_addrs aag (cur_domain s)\<close> is what tells
       the intersection of the two sets is nonempty.\<close>
   apply(erule_tac x=y in in_empty_interE)
    apply(force simp:policy_owned_addrs_def)
   apply force
  apply(rename_tac va y yd)
  \<comment> \<open>We now use @{term\<open>owned_objs_well_partitioned\<close>} to tell us \<open>y\<close> is in its domain's partition.\<close>
  unfolding owned_objs_well_partitioned_def
  apply(erule_tac x=yd in allE)
  apply(subgoal_tac
    "addrFromKPPtr va \<in> to_phys (\<Union> (obj_kheap_addrs s ` policy_owned_addrs aag yd))")
   apply force
  \<comment> \<open>Finally, \<open>va\<close> should be in the footprint of the @{term\<open>policy_owned_addrs\<close>} of \<open>yd\<close>
      because that should include \<open>y\<close>.\<close>
  apply(force simp:obj_kheap_addrs_def policy_owned_addrs_def)
  done

\<comment> \<open>Object subset property: That only the paddrs of policy-accessible objects are ever accessed.\<close>
definition ta_subset_accessible_objects :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_objects aag s \<equiv>
     phys_touched s \<subseteq>
     to_phys (\<Union> (obj_kheap_addrs s ` policy_accessible_addrs aag (cur_domain s)))"

(* If it is easier to prove `ta_subset_accessible_objects` than
   `ta_subset_accessible_addrs` as an invariant,
   then we need `no_label_straddling_objs` as an invariant too. *)
lemma ta_subset_accessible_objs_to_addrs:
  "ta_subset_accessible_objects aag s \<Longrightarrow>
   no_label_straddling_objs aag s \<Longrightarrow>
   ta_subset_accessible_addrs aag s"
  unfolding ta_subset_accessible_addrs_def ta_subset_accessible_objects_def
  using accessible_objs_subset_accessible_addrs
  by blast

(* This is one potential way to get from `ta_subset_accessible_objects` to
   `ta_subset_accessible_partitions`.
   But we wouldn't want to prove `accessible_objs_well_partitioned` invariant directly
   because it depends on the state of the `kheap`. *)
lemma ta_subset_accessible_objs_to_partitions_HARD:
  "ta_subset_accessible_objects aag s \<Longrightarrow>
   accessible_objs_well_partitioned aag s \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  unfolding ta_subset_accessible_partitions_def ta_subset_accessible_objects_def
    accessible_objs_well_partitioned_def
  by blast

(* We can avoid proving `accessible_objs_well_partitioned` (which depends on the kheap)
   if it's straightforward enough to prove `accessible_addrs_well_partitioned`,
   but in exchange we need to prove `no_label_straddling_objs`. *)
theorem ta_subset_accessible_objs_to_partitions:
  "ta_subset_accessible_objects aag s \<Longrightarrow>
   no_label_straddling_objs aag s \<Longrightarrow>
   accessible_addrs_well_partitioned aag \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  apply(drule ta_subset_accessible_objs_to_addrs)
   apply force
  apply(drule ta_subset_accessible_addrs_to_partitions)
   apply force
  apply force
  done

(* Finally, if it's easier to prove `owned_addrs_well_partitioned` than
   `accessible_addrs_well_partitioned` then we'll additionally need `all_labels_are_owned`.
   Though, again, the difference in difficulty between the two is questionable because
   neither of them depend on the state anyway. *)
lemma ta_subset_accessible_objs_to_partitions_alternative:
  "ta_subset_accessible_objects aag s \<Longrightarrow>
   no_label_straddling_objs aag s \<Longrightarrow>
   all_labels_are_owned aag \<Longrightarrow>
   owned_addrs_well_partitioned aag \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  by (force intro:ta_subset_accessible_objs_to_partitions_HARD
    owned_addrs_to_objs_well_partitioned owned_to_accessible_objs_well_partitioned)

section \<open>Proofs of TA subset invariance over seL4 kernel\<close>

abbreviation ta_subset_inv :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_inv \<equiv> ta_subset_accessible_addrs" \<comment> \<open>Right now we're trying the kheap-agnostic one.\<close>

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

(* Scott (@scottbuckley) recommends trying to prove this one -robs. *)
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

locale ADT_IF_L2Partitioned = ArchL2Partitioned paddr_L2_colour L2_colour_domains
  (* FIXME: Not sure how to get rid of this "RISCV64." -robs *)
  for paddr_L2_colour :: "RISCV64.paddr \<Rightarrow> 'colour"
  and L2_colour_domains :: "'colour \<Rightarrow> domain set" +
  fixes initial_aag :: "'a PAS"
  fixes s0 :: det_state
  assumes init_ta_empty: "touched_addresses (machine_state s0) = {}"
begin

lemma "ta_subset_accessible_addrs aag s0"
  unfolding ta_subset_accessible_addrs_def
  using init_ta_empty
  by blast

end

end