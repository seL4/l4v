(*
 * Copyright 2022, The University of Melbourne (ABN 84 002 705 224)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CachePartitionIntegrity
imports InfoFlow.InfoFlow
begin

context Arch begin global_naming RISCV64

\<comment> \<open> Adapted from Scott's definition of @{term\<open>touch_objects\<close>}. -robs \<close>
definition obj_v_footprint :: "'a state \<Rightarrow> obj_ref \<Rightarrow> machine_word set" where
  "obj_v_footprint s p \<equiv> case kheap s p of
     None \<Rightarrow> {} |
     Some obj \<Rightarrow> obj_range p obj"

definition policy_owned_objs :: "'a PAS \<Rightarrow> domain \<Rightarrow> obj_ref set" where
  "policy_owned_objs aag d \<equiv> {p. pasObjectAbs aag p \<in> pasDomainAbs aag d}"

definition all_labels_are_owned :: "'a PAS \<Rightarrow> bool" where
  "all_labels_are_owned aag \<equiv> \<forall>l. \<exists>d. l \<in> pasDomainAbs aag d"

definition policy_accessible_labels :: "'a PAS \<Rightarrow> domain \<Rightarrow> 'a set" where
  "policy_accessible_labels aag d \<equiv> pasDomainAbs aag d \<union>
     \<Union> {ls. \<exists>l \<in> pasDomainAbs aag d.
       ls = subjectReads (pasPolicy aag) l \<or>
       ls = subjectAffects (pasPolicy aag) l}"

definition policy_accessible_objs :: "'a PAS \<Rightarrow> domain \<Rightarrow> obj_ref set" where
  "policy_accessible_objs aag d \<equiv> {p. pasObjectAbs aag p \<in> policy_accessible_labels aag d}"

definition policy_accessible_domains :: "'a PAS \<Rightarrow> domain \<Rightarrow> domain set" where
  "policy_accessible_domains aag d \<equiv>
     {d'. policy_owned_objs aag d' \<inter> policy_accessible_objs aag d \<noteq> {}}"

definition v_to_p_kernel_nonelf_opt :: "arch_state \<Rightarrow> machine_word \<Rightarrow> paddr option" where
  "v_to_p_kernel_nonelf_opt s va \<equiv> case riscv_kernel_vspace s va of
     RISCVVSpaceKernelWindow \<Rightarrow> Some (addrFromKPPtr va) |
     _ \<Rightarrow> None"

definition v_to_p_kernel_nonelf :: "arch_state \<Rightarrow> machine_word set \<Rightarrow> paddr set" where
  "v_to_p_kernel_nonelf s vas \<equiv> {pa. \<exists>va \<in> vas. v_to_p_kernel_nonelf_opt s va = Some pa}"

lemma owned_subset_accessible_objs:
  "policy_owned_objs aag d \<subseteq> policy_accessible_objs aag d"
  unfolding policy_owned_objs_def policy_accessible_objs_def policy_accessible_labels_def
  by blast

lemma nonempty_domains_self_accessible:
  "policy_owned_objs aag d \<noteq> {} \<Longrightarrow> d \<in> policy_accessible_domains aag d"
  unfolding policy_accessible_domains_def
  apply clarsimp
  using owned_subset_accessible_objs
  by blast

end

locale ArchL2Partitioned = Arch +
  fixes paddr_L2_domain :: "RISCV64.paddr \<Rightarrow> domain"
begin

definition domain_L2_partition :: "domain \<Rightarrow> RISCV64.paddr set" where
  "domain_L2_partition d \<equiv> {pa. paddr_L2_domain pa = d}"

lemma domain_L2_partitions_distinct:
  "d1 \<noteq> d2 \<Longrightarrow> domain_L2_partition d1 \<inter> domain_L2_partition d2 = {}"
  unfolding domain_L2_partition_def
  by blast

definition policy_accessible_partitions :: "'a PAS \<Rightarrow> det_state \<Rightarrow> RISCV64.paddr set" where
  "policy_accessible_partitions aag s \<equiv>
     \<Union> {as. \<exists>d \<in> policy_accessible_domains aag (cur_domain s). as = domain_L2_partition d}"

definition p_footprint :: "det_state \<Rightarrow> machine_word set \<Rightarrow> RISCV64.paddr set" where
  "p_footprint s as \<equiv> v_to_p_kernel_nonelf (arch_state s) as"

abbreviation touched_addresses' :: "det_state \<Rightarrow> machine_word set" where
  "touched_addresses' s \<equiv> touched_addresses (machine_state s)"

definition ta_subset_owned_partition :: "det_state \<Rightarrow> bool" where
  "ta_subset_owned_partition s \<equiv>
     p_footprint s (touched_addresses' s) \<subseteq>
     domain_L2_partition (cur_domain s)"

\<comment> \<open>Partition subset property: That only paddrs in policy-accessible partitions are ever accessed.\<close>
definition ta_subset_accessible_partitions :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_partitions aag s \<equiv>
     p_footprint s (touched_addresses' s) \<subseteq>
     policy_accessible_partitions aag s"

\<comment> \<open>That each domain's objects stay confined to that domain's partition.\<close>
definition owned_objs_well_partitioned :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "owned_objs_well_partitioned aag s \<equiv> \<forall> d.
     p_footprint s (\<Union> (obj_v_footprint s ` policy_owned_objs aag d)) \<subseteq>
     domain_L2_partition d"

\<comment> \<open>That accessible objects will only lie inside accessible domains' partitions.\<close>
definition accessible_objs_well_partitioned :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "accessible_objs_well_partitioned aag s \<equiv>
     p_footprint s (\<Union> (obj_v_footprint s ` policy_accessible_objs aag (cur_domain s))) \<subseteq>
     policy_accessible_partitions aag s"

\<comment> \<open>If every domain's objects is confined to its partition, then all accessible objects, due to
  belonging to accessible domains, are confined to the union of those domains' partitions. -robs\<close>
lemma owned_to_accessible_objs_well_partitioned:
  "\<lbrakk>all_labels_are_owned aag; owned_objs_well_partitioned aag s\<rbrakk> \<Longrightarrow>
   accessible_objs_well_partitioned aag s"
  unfolding accessible_objs_well_partitioned_def
  apply(clarsimp simp:p_footprint_def)
  apply(clarsimp simp:v_to_p_kernel_nonelf_def)
  apply(rename_tac pa y va)
  \<comment> \<open>We consider each accessible object, call it \<open>y\<close>.\<close>
  (* Things that matter for 'y' to be a valid object reference:
     - It is allocated, i.e. kheap s y \<noteq> None.
       This follows from the definition of obj_v_footprint.
     - Everything in its object footprint is in the kernel window, i.e.
       \<forall>va \<in> obj_v_footprint s y.
         riscv_kernel_vspace (arch_state s) va = RISCVVSpaceKernelWindow
       This follows from the definition of v_to_p_kernel_nonelf_opt_def. *)
  \<comment> \<open>We know the L2 partitioning scheme assigns the physical address of \<open>y\<close> to some domain
        \<open>paddr_L2_domain (addrFromKPPtr y)\<close>
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
   \<comment> \<open>Note: \<open>y \<in> policy_accessible_objs aag (cur_domain s)\<close> is what tells
       the intersection of the two sets is nonempty.\<close>
   apply(erule_tac x=y in in_empty_interE)
    apply(force simp:policy_owned_objs_def)
   apply force
  apply(rename_tac pa y va yd)
  \<comment> \<open>Reminder: \<open>pa\<close> is the physical translation of some \<open>va\<close> in \<open>y\<close>'s @{term\<open>obj_v_footprint\<close>}.\<close>
  apply(clarsimp simp:v_to_p_kernel_nonelf_def v_to_p_kernel_nonelf_opt_def
    split:riscvvspace_region_use.splits)
  \<comment> \<open>We now use @{term\<open>owned_objs_well_partitioned\<close>} to tell us \<open>y\<close> is in its domain's partition.\<close>
  unfolding owned_objs_well_partitioned_def
  apply(erule_tac x=yd in allE)
  apply(subgoal_tac
    "addrFromKPPtr va \<in> p_footprint s (\<Union> (obj_v_footprint s ` policy_owned_objs aag yd))")
   apply force
  \<comment> \<open>Finally, \<open>va\<close> should be in the footprint of the @{term\<open>policy_owned_objs\<close>} of \<open>yd\<close>
      because that should include \<open>y\<close>.\<close>
  apply(clarsimp simp:obj_v_footprint_def p_footprint_def v_to_p_kernel_nonelf_def policy_owned_objs_def)
  apply(rule_tac x=y in exI)
  apply clarsimp
  apply(rule_tac x=va in bexI)
   apply(force simp:v_to_p_kernel_nonelf_opt_def)
  apply force
  done

\<comment> \<open>Object subset property: Only the paddrs of policy-accessible objects are ever accessed.\<close>
definition ta_subset_accessible_objects :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_objects aag s \<equiv>
     p_footprint s (touched_addresses' s) \<subseteq>
     p_footprint s (\<Union> (obj_v_footprint s ` policy_accessible_objs aag (cur_domain s)))"

lemma ta_subset_accessible_partitions':
  "\<lbrakk>accessible_objs_well_partitioned aag s; ta_subset_accessible_objects aag s\<rbrakk> \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  unfolding ta_subset_accessible_partitions_def ta_subset_accessible_objects_def
    accessible_objs_well_partitioned_def
  by blast

theorem ta_subset_accessible_partitions:
  "\<lbrakk>all_labels_are_owned aag; owned_objs_well_partitioned aag s;
    ta_subset_accessible_objects aag s\<rbrakk> \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  by (force intro:ta_subset_accessible_partitions' owned_to_accessible_objs_well_partitioned)

end

locale ADT_IF_L2Partitioned = ArchL2Partitioned +
  fixes initial_aag :: "'a PAS"
  fixes s0 :: det_state
  assumes init_well_partitioned:
    "owned_objs_well_partitioned initial_aag s0"
  assumes init_ta_empty:
    "touched_addresses' s0 = {}"
begin

lemma "ta_subset_accessible_objects aag s0"
  unfolding ta_subset_accessible_objects_def p_footprint_def v_to_p_kernel_nonelf_def
  using init_ta_empty
  by blast

end

end