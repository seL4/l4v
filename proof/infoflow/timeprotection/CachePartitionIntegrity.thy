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

(* XXX: Why should this matter?
definition no_empty_domains :: "'a PAS \<Rightarrow> bool" where
  "no_empty_domains aag \<equiv> \<forall>d. policy_owned_objs aag d \<noteq> {}"
*)

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
lemma partitioning_owned_partitions_accessible:
  (* no_empty_domains aag \<Longrightarrow> *)
  (* pas_domains_distinct aag \<Longrightarrow> Apparently we might not even need this either? *)
  "owned_objs_well_partitioned aag s \<Longrightarrow> accessible_objs_well_partitioned aag s"
  unfolding accessible_objs_well_partitioned_def
  apply(clarsimp simp:p_footprint_def)
  apply(clarsimp simp:v_to_p_kernel_nonelf_def)
  (* For each accessible object, call it 'y' *)
  (* Things that matter for 'y' to be a valid object reference:
     - It is allocated, i.e. kheap s y \<noteq> None
     - Everything in its object footprint is in the kernel window, i.e.
       \<forall>va \<in> obj_v_footprint s y.
         riscv_kernel_vspace (arch_state s) va = RISCVVSpaceKernelWindow *)
  apply(subgoal_tac "kheap s y \<noteq> None")
  apply(subgoal_tac "\<forall>va \<in> obj_v_footprint s y.
         riscv_kernel_vspace (arch_state s) va = RISCVVSpaceKernelWindow")
  (* We know the L2 partitioning scheme assigns the physical address of 'y' to some domain.
  define yd_addr_partition where "yd_addr_partition = paddr_L2_domain (addrFromKPPtr y)"  *)
  (* 'y' has a label given by pasObjectAbs, which is not necessarily assigned to any domain.
  define yl where "yl = pasObjectAbs aag y"  *)

  (* Attempt 1: Plug in the domain determined by the partitioning scheme.
  apply(erule_tac x="paddr_L2_domain (addrFromKPPtr y)" in allE)
  apply clarsimp
  apply(clarsimp simp:policy_accessible_partitions_def policy_accessible_domains_def)
  unfolding owned_objs_well_partitioned_def
  apply(rule_tac x="domain_L2_partition (paddr_L2_domain (addrFromKPPtr y))" in exI)
  apply(erule_tac x="paddr_L2_domain (addrFromKPPtr y)" in allE)
  apply(rule conjI)
   apply(rule_tac x="paddr_L2_domain (addrFromKPPtr y)" in exI)
  *)

  (* Attempt 2: Plug in the domain determined by the domain assignment of y's label. *)
  (* First, assume there is one. *)
  apply(subgoal_tac "\<exists>yd. pasDomainAbs aag yd = {pasObjectAbs aag y}")
  apply clarsimp
  (* Note: pas_domains_distinct not even needed?
  apply(erule_tac x=yd in allE)
  apply clarsimp *)
  apply(clarsimp simp:policy_accessible_partitions_def policy_accessible_domains_def)
  apply(rule_tac x="domain_L2_partition yd" in exI)
  apply(rule conjI)
   apply(rule_tac x=yd in exI)
   apply clarsimp
   (* Note: From here we're trying to get something about policy_owned_objs to tell us
      its intersection with accessible_objs is nonempty. *)
   (* Note: `y \<in> policy_accessible_objs aag (cur_domain s)` is what should be telling us
      what we need to know. So I should try to say that the physical address of `y`
      is the element that is in the (non-empty) intersection of the two sets. *)
   apply(erule_tac x=y in in_empty_interE)
    apply(force simp:policy_owned_objs_def)
   apply force
  apply(rename_tac pa y va yobj yd)
  (* Reminder: pa is the physical translation of some va in y's obj_v_footprint *)
  apply(clarsimp simp:v_to_p_kernel_nonelf_def v_to_p_kernel_nonelf_opt_def
    split:riscvvspace_region_use.splits)
  (* We now use owned_objs_well_partitioned to tell us that y is in its domain's partition *)
  unfolding owned_objs_well_partitioned_def
  apply(erule_tac x=yd in allE)
  apply(subgoal_tac "addrFromKPPtr va \<in> p_footprint s (\<Union> (obj_v_footprint s ` policy_owned_objs aag yd))")
   apply force
  (* va should be in the footprint of policy_owned_objs of yd because that should include y *)
  apply(clarsimp simp:obj_v_footprint_def p_footprint_def v_to_p_kernel_nonelf_def policy_owned_objs_def)
  apply(rule_tac x=y in exI)
  apply clarsimp
  apply(rule_tac x=va in bexI)
   apply(force simp:v_to_p_kernel_nonelf_opt_def)
  apply force
  sorry

\<comment> \<open>Object subset property: Only the paddrs of policy-accessible objects are ever accessed.\<close>
definition ta_subset_accessible_objects :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_objects aag s \<equiv>
     p_footprint s (touched_addresses' s) \<subseteq>
     p_footprint s (\<Union> (obj_v_footprint s ` policy_accessible_objs aag (cur_domain s)))"

lemma ta_subset_accessible_partitions':
  (* XXX: Needed? no_empty_domains aag \<Longrightarrow> pas_domains_distinct aag \<Longrightarrow> *)
  "\<lbrakk>accessible_objs_well_partitioned aag s;
    ta_subset_accessible_objects aag s\<rbrakk> \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  sorry

lemma ta_subset_accessible_partitions:
  (* XXX: Needed? no_empty_domains aag \<Longrightarrow> pas_domains_distinct aag \<Longrightarrow> *)
  "\<lbrakk>owned_objs_well_partitioned aag s;
    ta_subset_accessible_objects aag s\<rbrakk> \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  apply(force intro:ta_subset_accessible_partitions' partitioning_owned_partitions_accessible)
  done

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