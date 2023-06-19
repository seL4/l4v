(*
 * Copyright 2022, The University of Melbourne (ABN 84 002 705 224)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CachePartitionIntegrity
imports InfoFlow.InfoFlow_IF
  InfoFlow.Noninterference (* InfoFlow ADT definitions and key invariant lemmas *)
begin

section \<open> Kernel heap-agnostic subset property definitions \<close>

context Arch begin

\<comment> \<open> Note: \<open>pas_addrs_of aag (pasSubject aag) = {p. is_subject aag p}\<close>
     but we need to use this for other labels than the subject. \<close>
definition pas_addrs_of :: "'a PAS \<Rightarrow> 'a \<Rightarrow> obj_ref set" where
  "pas_addrs_of aag l \<equiv> {p. pasObjectAbs aag p = l}"

\<comment> \<open> Note: When \<open>l = pasSubject aag\<close> this could be rephrased in terms of
     @{term\<open>aag_can_read\<close>} and @{term\<open>subject_can_affect_label_directly\<close>}
     but we need to use this for other labels than the subject. \<close>
definition pas_labels_accessible_to :: "'a PAS \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "pas_labels_accessible_to aag l \<equiv> {l} \<union>
     subjectReads (pasPolicy aag) l \<union> subjectAffects (pasPolicy aag) l"

definition pas_addrs_accessible_to :: "'a PAS \<Rightarrow> 'a \<Rightarrow> obj_ref set" where
  "pas_addrs_accessible_to aag l \<equiv> {p. pasObjectAbs aag p \<in> pas_labels_accessible_to aag l}"

lemma pas_addrs_accessible_to_def2:
  "pas_addrs_accessible_to aag l = \<Union> (pas_addrs_of aag ` pas_labels_accessible_to aag l)"
  unfolding pas_addrs_accessible_to_def
  apply(clarsimp simp:image_def pas_addrs_of_def)
  by blast

definition separation_kernel_policy where
  "separation_kernel_policy aag \<equiv> \<forall>l. pas_labels_accessible_to aag l = {l}"

lemma separation_kernel_only_owned_accessible:
  "separation_kernel_policy aag \<Longrightarrow>
   pas_addrs_accessible_to aag l = pas_addrs_of aag l"
  unfolding pas_addrs_accessible_to_def pas_addrs_of_def separation_kernel_policy_def
  by simp

\<comment> \<open>Important: We assume that the @{term\<open>touched_addresses\<close>} set will only be used to track the
    virtual addresses of kernel objects; therefore its physical address footprint is just the
    image of @{term\<open>addrFromKPPtr\<close>} because @{term\<open>pspace_in_kernel_window\<close>} tells us all
    kernel objects live in the kernel window.\<close>
abbreviation to_phys :: "machine_word set \<Rightarrow> paddr set" where
  "to_phys vas \<equiv> addrFromKPPtr ` vas"

abbreviation phys_touched :: "det_state \<Rightarrow> paddr set" where
  "phys_touched s \<equiv> to_phys (touched_addresses (machine_state s))"

abbreviation cur_label :: "'a PAS \<Rightarrow> det_state \<Rightarrow> 'a" where
  "cur_label aag s \<equiv> THE l. pasDomainAbs aag (cur_domain s) = {l}"

\<comment> \<open>Right now we're trying a simplified version of the kheap-agnostic property.
  It's possible to simplify out the @{term\<open>to_phys\<close>} because, assuming the TA set tracks only
  kernel object addresses, it's just a simple subtraction of the @{term\<open>kernelELFBaseOffset\<close>}. \<close>
definition ta_subset_inv :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_inv aag s \<equiv>
     touched_addresses (machine_state s) \<subseteq> pas_addrs_accessible_to aag (cur_label aag s)"

end

locale ArchL2Partitioned = Arch +
   fixes gentypes :: "('a \<times> 'colour) itself"
   fixes paddr_L2_colour :: "paddr \<Rightarrow> 'colour"
   fixes label_L2_colour :: "'a \<Rightarrow> 'colour"
begin

definition L2_partition_of :: "'a \<Rightarrow> paddr set" where
  "L2_partition_of l \<equiv> {pa. paddr_L2_colour pa = label_L2_colour l}"

definition pas_partitions_accessible_to :: "'a PAS \<Rightarrow> 'a \<Rightarrow> paddr set" where
  "pas_partitions_accessible_to aag l \<equiv>
     \<Union> {as. \<exists>l' \<in> pas_labels_accessible_to aag l. as = L2_partition_of l'}"

lemma pas_partitions_accessible_to_def2:
  "pas_partitions_accessible_to aag l = \<Union> (L2_partition_of ` pas_labels_accessible_to aag l)"
  unfolding pas_partitions_accessible_to_def
  by blast

\<comment> \<open>When we have that the @{term\<open>cur_domain\<close>} matches the PAS record's @{term\<open>pasSubject\<close>} (as
    per @{term\<open>pas_cur_domain\<close>}) we can simplify it out thanks to @{term\<open>pas_domains_distinct\<close>}.\<close>
lemma cur_label_to_subj[intro]:
  "pas_domains_distinct aag \<Longrightarrow>
   pas_cur_domain aag s \<Longrightarrow>
   cur_label aag s = pasSubject aag"
  unfolding pas_domains_distinct_def
  by (metis singletonD the_elem_def the_elem_eq)

lemma cur_label_to_subj':
  "pas_domains_distinct aag \<Longrightarrow>
   \<forall>s. pas_cur_domain aag s \<longrightarrow> cur_label aag s = pasSubject aag"
  using cur_label_to_subj
  by blast

\<comment> \<open>However, we expect @{term\<open>cur_domain\<close>} to get out of alignment with the @{term\<open>pasSubject\<close>}
    halfway through the domain-switch step of the Access automaton, over which we verify integrity.
      As we will make the steps of the InfoFlow time-protection extension automaton finer grained
    than this, so we can verify time protection, @{term\<open>pasSubject\<close>} will not accurately reflect
    the @{term\<open>cur_domain\<close>} (i.e. @{term\<open>pas_cur_domain\<close>} will not hold) for some of its states.
      To ensure we have no such mismatch, we will define the subset properties here directly in
    terms of @{term\<open>cur_domain\<close>} (via @{term\<open>cur_label\<close>}) rather than the @{term\<open>pasSubject\<close>}.\<close>

definition ta_subset_owned_partition :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_owned_partition aag s \<equiv>
     phys_touched s \<subseteq> L2_partition_of (cur_label aag s)"

\<comment> \<open>Partition subset property: That only paddrs in policy-accessible partitions are ever accessed.\<close>
definition ta_subset_accessible_partitions :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_partitions aag s \<equiv>
     phys_touched s \<subseteq> pas_partitions_accessible_to aag (cur_label aag s)"

\<comment> \<open>That @{term\<open>pasObjectAbs\<close>} assigns each label only addresses located in its L2 partition.\<close>
definition owned_addrs_well_partitioned :: "'a PAS \<Rightarrow> bool" where
  "owned_addrs_well_partitioned aag \<equiv> \<forall> l.
     to_phys (pas_addrs_of aag l) \<subseteq> L2_partition_of l"

\<comment> \<open>That for every label \<open>l\<close>, every label directly accessible to it according to the
    @{term\<open>pasPolicy\<close>} is assigned by @{term\<open>pasObjectAbs\<close>} only addresses located
    in the union of the L2 partitions accessible to \<open>l\<close>.\<close>
definition accessible_addrs_well_partitioned :: "'a PAS \<Rightarrow> bool" where
  "accessible_addrs_well_partitioned aag \<equiv> \<forall> l.
     to_phys (pas_addrs_accessible_to aag l) \<subseteq> pas_partitions_accessible_to aag l"

\<comment> \<open>If every label's addresses is confined to its partition, then all accessible addresses, due to
  belonging to accessible labels, are confined to the union of those labels' partitions.\<close>
lemma owned_to_accessible_addrs_well_partitioned:
  "owned_addrs_well_partitioned aag \<Longrightarrow>
   accessible_addrs_well_partitioned aag"
  unfolding accessible_addrs_well_partitioned_def owned_addrs_well_partitioned_def
    pas_labels_accessible_to_def pas_addrs_accessible_to_def2 pas_partitions_accessible_to_def2
  by blast

\<comment> \<open>Address subset property: That only the paddrs of policy-accessible labels are ever accessed.\<close>
definition ta_subset_accessible_addrs :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_addrs aag s \<equiv>
     phys_touched s \<subseteq> to_phys (pas_addrs_accessible_to aag (cur_label aag s))"

lemma ta_subset_accessible_addrs_to_partitions:
  "ta_subset_accessible_addrs aag s \<Longrightarrow>
   accessible_addrs_well_partitioned aag \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  unfolding ta_subset_accessible_partitions_def ta_subset_accessible_addrs_def
    accessible_addrs_well_partitioned_def
  by fast

(* If it's easier to prove `owned_addrs_well_partitioned` than
   `accessible_addrs_well_partitioned` then it's just as suitable. *)
theorem ta_subset_accessible_addrs_to_partitions_alternative:
  "ta_subset_accessible_addrs aag s \<Longrightarrow>
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

\<comment> \<open>That each label's objects stay confined to its partition.\<close>
definition owned_objs_well_partitioned :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "owned_objs_well_partitioned aag s \<equiv> \<forall> l.
     to_phys (\<Union> (obj_kheap_addrs s ` pas_addrs_of aag l)) \<subseteq>
     L2_partition_of l"

\<comment> \<open>That accessible objects will only lie inside accessible domains' partitions.\<close>
definition accessible_objs_well_partitioned :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "accessible_objs_well_partitioned aag s \<equiv>
     to_phys (\<Union> (obj_kheap_addrs s ` pas_addrs_accessible_to aag (cur_label aag s))) \<subseteq>
     pas_partitions_accessible_to aag (cur_label aag s)"

lemma accessible_objs_subset_accessible_addrs:
  "no_label_straddling_objs aag s \<Longrightarrow>
   to_phys (\<Union> (obj_kheap_addrs s ` pas_addrs_accessible_to aag l)) \<subseteq>
   to_phys (pas_addrs_accessible_to aag l)"
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
   apply(force simp:pas_addrs_accessible_to_def)
  apply(force simp:pas_addrs_accessible_to_def)
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
    apply(clarsimp simp:pas_addrs_of_def)
    apply metis
   apply force
  apply force
  done

\<comment> \<open>If every label's objects is confined to its partition, then all accessible objects, due to
  belonging to accessible labels, are confined to the union of those labels' partitions. -robs\<close>
lemma owned_to_accessible_objs_well_partitioned:
  "owned_objs_well_partitioned aag s \<Longrightarrow>
   accessible_objs_well_partitioned aag s"
  unfolding accessible_objs_well_partitioned_def
  apply clarsimp
  apply(rename_tac va y)
  \<comment> \<open>We consider each accessible object, call it \<open>y\<close>.\<close>
  (* Things that matter for 'y' to be a valid object reference:
     - It is allocated, i.e. kheap s y \<noteq> None.
       This follows from the definition of obj_kheap_addrs. *)
  \<comment> \<open>We know the L2 partitioning scheme @{term\<open>paddr_L2_colour\<close>}
      assigns the physical address of \<open>y\<close> to some colour
      which belongs to some (possibly empty) set of labels (according to @{term\<open>label_L2_colour\<close>}.
      But instead of that, we use y's label, given by @{term\<open>pasObjectAbs\<close>}.\<close>
  apply(clarsimp simp:pas_partitions_accessible_to_def pas_labels_accessible_to_def
    pas_addrs_accessible_to_def2)
  apply(clarsimp simp:owned_objs_well_partitioned_def pas_addrs_of_def)
  apply(rule_tac x="L2_partition_of (pasObjectAbs aag y)" in exI)
  apply(rule context_conjI)
   apply blast
  apply force
  done

\<comment> \<open>Object subset property: That only the paddrs of policy-accessible objects are ever accessed.\<close>
definition ta_subset_accessible_objects :: "'a PAS \<Rightarrow> det_state \<Rightarrow> bool" where
  "ta_subset_accessible_objects aag s \<equiv>
     phys_touched s \<subseteq>
     to_phys (\<Union> (obj_kheap_addrs s ` pas_addrs_accessible_to aag (cur_label aag s)))"

(* If it is easier to prove `ta_subset_accessible_objects` than
   `ta_subset_accessible_addrs` as an invariant,
   then we need `no_label_straddling_objs` as an invariant too. *)
lemma ta_subset_accessible_objs_to_addrs:
  "ta_subset_accessible_objects aag s \<Longrightarrow>
   no_label_straddling_objs aag s \<Longrightarrow>
   ta_subset_accessible_addrs aag s"
  unfolding ta_subset_accessible_addrs_def ta_subset_accessible_objects_def
  using accessible_objs_subset_accessible_addrs
  by fast

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
lemma ta_subset_accessible_objs_to_partitions:
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
   `accessible_addrs_well_partitioned` then it's just as suitable. *)
theorem ta_subset_accessible_objs_to_partitions_alternative:
  "ta_subset_accessible_objects aag s \<Longrightarrow>
   no_label_straddling_objs aag s \<Longrightarrow>
   owned_addrs_well_partitioned aag \<Longrightarrow>
   ta_subset_accessible_partitions aag s"
  by (force intro:ta_subset_accessible_objs_to_partitions_HARD
    owned_addrs_to_objs_well_partitioned owned_to_accessible_objs_well_partitioned)

section \<open>Proofs of TA subset invariance over seL4 kernel\<close>

lemma ta_subset_to_phys_property:
  "ta_subset_inv \<equiv> ta_subset_accessible_addrs"
  unfolding ta_subset_inv_def ta_subset_accessible_addrs_def
  apply(rule eq_reflection)
  apply(rule ext)+
  apply(rule iffI)
   apply blast
  by (force simp:image_def addrFromKPPtr_def)

(* XXX: no theorems proven for any of these
crunches touch_objects, touch_object, get_cap, get_object
  for pas_cur_domain: "pas_cur_domain aag"
  and ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp')
*)

(* KHeap_A *)
(* If objects in TA are a subset of the policy-allowed ones before modifying the object,
   that will remain the case after modifying the object using `set_object`. *)
lemma set_object_ta_subset_inv:
  "\<lbrace>\<lambda>s. ta_subset_inv aag (ms_ta_update ((\<union>) (obj_range p (the (kheap s p)))) s) \<rbrace>
   set_object ta_f p obj \<lbrace>\<lambda>_ s. ta_subset_inv aag s\<rbrace>"
  apply(wpsimp wp:touch_object_wp' get_object_wp simp:crunch_simps ta_subset_inv_def set_object_def)
  apply(subgoal_tac "x \<in> obj_range p (the (kheap s p))")
   apply force
  (* By cases, for all kinds of kernel objects: The change cannot have affected its size. *)
  by (clarsimp simp:obj_at_def a_type_def obj_range_def
    split:kernel_object.splits if_splits arch_kernel_obj.splits)

(* Note: The fact that `pas_refined` is `ta_agnostic` is now proved earlier, in Access_AC. *)
thm pas_refined_ta_agnostic

(* Note: If we need it, `no_label_straddling_objs` is an invariant we've discussed
   adding as a new conjunct of `pas_refined`. Looks like we might need it. -robs *)
lemma pas_refined_no_label_straddling_objs[intro]:
  "pas_refined aag s \<Longrightarrow> no_label_straddling_objs aag s"
  sorry

(* If there are no label-straddling objects on the kheap, then adding a policy-accessible
   kheap object to the TA set cannot falsify the ta_subset_inv. *)
lemma safe_addition_to_ta:
  "ta_subset_inv aag s \<Longrightarrow>
   no_label_straddling_objs aag s \<Longrightarrow>
   pasObjectAbs aag p \<in> pas_labels_accessible_to aag (cur_label aag s) \<Longrightarrow>
   ko_at ko p s \<Longrightarrow>
   ta_subset_inv aag (ms_ta_update ((\<union>) (obj_range p ko)) s)"
  apply(clarsimp simp:ta_subset_inv_def)
  apply(clarsimp simp:no_label_straddling_objs_def)
  apply(erule_tac x=p in allE)
  apply(clarsimp split:option.splits)
   apply(clarsimp simp:obj_at_def)
  apply(clarsimp simp:obj_at_def)
  apply(clarsimp simp:pas_addrs_accessible_to_def obj_range_def)
  done

(* XXX: Thinking about how to tackle lookup_cap_and_slot_ta_subset_inv but not sure this helps. *)
lemma safe_addition_to_ta_validI:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. ta_subset_inv aag and no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag p \<in> pas_labels_accessible_to aag (cur_label aag s)) and ko_at ko p\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_ s. ta_subset_inv aag (ms_ta_update ((\<union>) (obj_range p ko)) s)\<rbrace>"
  using safe_addition_to_ta
  unfolding valid_def
  by blast

(* KHeap_A *)
(* FIXME: Perhaps there is a better form for this that avoids us having to use it in the
   convoluted way we do in lookup_cap_and_slot_ta_subset_inv (see further below). *)
(* Toby: Consider rephrasing to be in terms of is_subject, or at least having a version
   that is in terms of that.
   Or, the *weakest precondition* rule will have this more generic version,
   and we have another lemma that says is_subject gives us this. *)
lemma touch_object_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
   (\<lambda>s. pasObjectAbs aag p \<in> pas_labels_accessible_to aag (cur_label aag s)) and obj_at P p\<rbrace>
     touch_object p \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  by (wpsimp wp:touch_object_wp' simp:safe_addition_to_ta obj_at_def)

(* CSpaceAcc_A *)
(* Need something like this *)
thm get_tcb_Some_True_False get_cap_det
(* FIXME: Move back far enough to be useful everywhere else this was needed. -robs *)
lemma get_cap_True_False[dest]:
  "get_cap True cap s = ({(r, s)}, False) \<Longrightarrow> get_cap False cap s = ({(r, s)}, False)"
  (* Kitchen sink was good enough for this. *)
  apply(clarsimp simp:get_cap_def bind_def get_object_def simpler_gets_def obind_def ta_filter_def
    assert_def return_def assert_opt_def
    split:prod.splits kernel_object.splits option.splits if_splits)
   apply auto
  done

lemma pas_cur_domain_ta_agnostic: "ta_agnostic (pas_cur_domain aag)"
  by (clarsimp simp:ta_agnostic_def)

(* CSpace_A *)

thm CNode_AC.resolve_address_bits_authorised_aux
(* Scott (@scottbuckley) recommends trying to prove this one -robs. *)
lemma resolve_address_bits'_ta_subset_inv:
  assumes domains_distinct: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and pas_refined aag and
    \<comment> \<open>Assume that the cur_domain is still consistent with the PAS record when we're
      at resolve_address_bits. I think this is reasonable if we don't expect it to get
      out of alignment until the domainswitch sequence anyway. -robs\<close>
    pas_cur_domain aag and
    \<comment> \<open>Additional precondition from \<open>resolve_address_bits_authorised_aux\<close>. We use this
      to obtain that the obj_ref is policy-accessible to the current domain. -robs\<close>
    K (is_cnode_cap (fst capcref) \<longrightarrow> (\<forall>x \<in> obj_refs_ac (fst capcref). is_subject aag x))\<rbrace>
     resolve_address_bits' z capcref
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
(* Following the proof structure of rab_inv (now called rab_tainv) in CSpaceInv_AI *)
proof (induct capcref rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
  apply (clarsimp simp add: valid_def)
  apply (subst (asm) resolve_address_bits'.simps)
  apply (cases cap)
             apply (auto simp: in_monad)[5]
        defer
        apply (auto simp: in_monad)[6]
  apply (rename_tac obj_ref nat list)
  apply (simp only: cap.simps)
  apply(rename_tac s rv s' obj_ref nat list)
  (* We'll use this in a number of places, so insert it back here. -robs *)
  apply(insert touch_object_wp[where Q="\<lambda>_. ta_subset_inv aag",simplified valid_def])
  (* Obtain that obj_ref is policy-accessible to the current domain. *)
  apply(subgoal_tac "pasObjectAbs aag obj_ref \<in> pas_labels_accessible_to aag (cur_label aag s)")
   prefer 2
   apply(clarsimp simp:pas_labels_accessible_to_def)
   using domains_distinct cur_label_to_subj
   apply force
  apply (case_tac "nat + length list = 0")
   apply (simp add: fail_def)
  apply (simp only: if_False)
  apply (case_tac rv)
   (* Case Inl: lookup_failure *)
   apply (simp only: K_bind_def)
   apply (drule in_bindE_L, elim disjE conjE exE)+
       apply (simp only: split: if_split_asm)
        apply (simp add: returnOk_def return_def)
       apply (drule in_bindE_L, elim disjE conjE exE)+
         apply (simp only: split: if_split_asm)
          prefer 2
          apply (clarsimp simp: in_monad)
         apply (frule(9) 1) (* get the IH into context *)
         apply (clarsimp simp: in_monad)
         apply (frule in_inv_by_hoareD [OF get_cap_inv])
         (* (Other than the `insert` and `subgoal_tac` earlier)
            Here's where I deviate from the rab_tainv proof. -robs *)
         apply clarsimp
         apply(rename_tac s s' obj_ref nat list exception s'' next_cap)
         apply(drule (1) use_valid)
          apply(frule_tac P="pas_refined aag" in touch_object_tainv.in_inv_by_hoare)
           using pas_refined_ta_agnostic unfolding ta_agnostic_def
           apply blast
          apply(frule_tac P="pas_cur_domain aag" in touch_object_tainv.in_inv_by_hoare)
           using pas_cur_domain_ta_agnostic unfolding ta_agnostic_def
           apply blast
          apply(prop_tac "ta_subset_inv aag s''")
           apply(erule_tac x=obj_ref in meta_allE)
           apply clarsimp
           apply(erule_tac x=s in allE)
           apply(erule impE)
            using safe_addition_to_ta apply fastforce
           apply force
          apply(rule conjI)
           apply force
          apply(rule conjI)
           apply force
          apply clarsimp
          (* Adapted from resolve_address_bits_authorised_aux proof *)
          apply(subgoal_tac "cte_wp_at ((=) next_cap) (obj_ref, take nat (drop (length list) cref)) s''")
           prefer 2
           apply(force dest:get_cap_det simp:cte_wp_at_def)
          apply(auto simp:cte_wp_at_caps_of_state is_cap_simps cap_auth_conferred_def
            dest:caps_of_state_pasObjectAbs_eq)[1]
         apply force
        apply (clarsimp simp: in_monad)
       apply (clarsimp simp: in_monad)
      apply (clarsimp simp: in_monad)
     apply (clarsimp simp: in_monad)
    apply (clarsimp simp: in_monad)
   apply (clarsimp simp: in_monad)
  (* Case Inr: (64 word \<times> bool list) \<times> bool list *)
  apply (simp only: K_bind_def in_bindE_R)
  apply (elim conjE exE)
  apply (simp only: split: if_split_asm)
   apply (simp add: in_monad split: if_split_asm)
  apply (simp only: K_bind_def in_bindE_R)
  apply (elim conjE exE)
  apply (simp only: split: if_split_asm)
   prefer 2
   (* If it's not a cnode cap, we'll just return it, so it's enough to know that
      touch_object preserved ta_subset_inv. -robs *)
   apply (clarsimp simp: in_monad)
   apply (drule in_inv_by_hoareD [OF get_cap_inv])
   apply(erule_tac x=obj_ref in meta_allE)
   apply(erule_tac x=s in allE)
   apply(erule impE)
    using safe_addition_to_ta apply fastforce
   apply blast
  (* If it's a cnode cap we'll need to know that its recursive call to rab
     preserved ta_subset_inv. The inductive hypothesis gives us that. -robs *)
  apply (drule (8) "1")
   apply (clarsimp simp: in_monad valid_def)
  apply clarsimp
  (* First move past all the stuff like get_cap and touch_object before it *)
  apply (clarsimp simp: in_monad)
  (* Use frule instead of drule because we'll need the get_cap assumption for later *)
  apply (frule in_inv_by_hoareD [OF get_cap_inv])
  apply clarsimp
  apply(rename_tac s b obj_ref nat list aa ba bb s'' next_cap)
  apply(prop_tac "ta_subset_inv aag s''")
   apply(erule_tac x=obj_ref in meta_allE)
   apply(erule_tac x=s in allE)
   apply(erule impE)
    using safe_addition_to_ta apply fastforce
   apply force
  apply(clarsimp simp:valid_def)
  apply(erule_tac x=s'' in allE)
  apply clarsimp
  (* We need pas_refined and pas_cur_domain too *)
  apply(frule_tac P="pas_refined aag" in touch_object_tainv.in_inv_by_hoare)
   using pas_refined_ta_agnostic unfolding ta_agnostic_def
   apply blast
  apply(frule_tac P="pas_cur_domain aag" in touch_object_tainv.in_inv_by_hoare)
   using pas_cur_domain_ta_agnostic unfolding ta_agnostic_def
   apply blast
  apply clarsimp
  apply(erule_tac x=obj_ref in meta_allE)
  apply(erule_tac x=s in allE)
  apply(rotate_tac -1)
  apply(erule impE)
   using safe_addition_to_ta apply fastforce
  apply(erule impE)
   (* Adapted from resolve_address_bits_authorised_aux proof *)
   apply(subgoal_tac "cte_wp_at ((=) next_cap) (obj_ref, take nat (drop (length list) cref)) s''")
    prefer 2
    apply(force dest:get_cap_det simp:cte_wp_at_def)
   apply(auto simp:cte_wp_at_caps_of_state is_cap_simps cap_auth_conferred_def
     dest:caps_of_state_pasObjectAbs_eq)[1]
  apply force
  done
qed

(* Note: Needs `pas_domains_distinct` to give to resolve_address_bits'_ta_subset_inv.
  ADT_IF seems to have that from context valid_initial_state, a locale that it defines. *)
lemma resolve_address_bits_ta_subset_inv:
  (* Follow convention used in Noninterference.thy for handling pas_domains_distinct assumption. *)
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and pas_refined aag and pas_cur_domain aag and
    K (is_cnode_cap (fst capcref) \<longrightarrow> (\<forall>x \<in> obj_refs_ac (fst capcref). is_subject aag x))\<rbrace>
     resolve_address_bits capcref
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding resolve_address_bits_def
  by (wpsimp wp: resolve_address_bits'_ta_subset_inv)

lemma resolve_address_bits'_pas_cur_domain:
  "\<lbrace>pas_cur_domain aag\<rbrace>
     resolve_address_bits' z capcref
   \<lbrace>\<lambda>_. pas_cur_domain aag\<rbrace>"
(* Following the proof structure of rab_inv (now called rab_tainv) in CSpaceInv_AI *)
proof (induct capcref rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
  apply (clarsimp simp add: valid_def)
  apply (subst (asm) resolve_address_bits'.simps)
  apply (cases cap)
             apply (auto simp: in_monad)[5]
        defer
        apply (auto simp: in_monad)[6]
  apply (rename_tac obj_ref nat list)
  apply (simp only: cap.simps)
  apply(rename_tac s rv s' obj_ref nat list)
  (* We'll use this in a number of places, so insert it back here. -robs *)
  apply(insert touch_object_wp[where Q="\<lambda>_. pas_cur_domain aag",simplified valid_def])
  apply (case_tac "nat + length list = 0")
   apply (simp add: fail_def)
  apply (simp only: if_False)
  apply (case_tac rv)
   (* Case Inl: lookup_failure *)
   apply (simp only: K_bind_def)
   apply (drule in_bindE_L, elim disjE conjE exE)+
       apply (simp only: split: if_split_asm)
        apply (simp add: returnOk_def return_def)
       apply (drule in_bindE_L, elim disjE conjE exE)+
         apply (simp only: split: if_split_asm)
          prefer 2
          apply (clarsimp simp: in_monad)
         apply (frule(9) 1) (* get the IH into context *)
         apply (clarsimp simp: in_monad)
         apply (frule in_inv_by_hoareD [OF get_cap_inv])
         apply clarsimp
         apply(rename_tac s s' obj_ref nat list exception s'' next_cap)
         apply(drule (1) use_valid)
          apply(frule_tac P="pas_cur_domain aag" in touch_object_tainv.in_inv_by_hoare)
           using pas_cur_domain_ta_agnostic unfolding ta_agnostic_def
           apply blast
          apply clarsimp
         apply force
        apply (clarsimp simp: in_monad)
       apply (clarsimp simp: in_monad)
      apply (clarsimp simp: in_monad)
     apply (clarsimp simp: in_monad)
    apply (clarsimp simp: in_monad)
   apply (clarsimp simp: in_monad)
  (* Case Inr: (64 word \<times> bool list) \<times> bool list *)
  apply (simp only: K_bind_def in_bindE_R)
  apply (elim conjE exE)
  apply (simp only: split: if_split_asm)
   apply (simp add: in_monad split: if_split_asm)
  apply (simp only: K_bind_def in_bindE_R)
  apply (elim conjE exE)
  apply (simp only: split: if_split_asm)
   prefer 2
   apply (clarsimp simp: in_monad)
   apply (drule in_inv_by_hoareD [OF get_cap_inv])
   apply(erule_tac x=obj_ref in meta_allE)
   apply(erule_tac x=s in allE)
   apply blast
  apply (drule (8) "1")
   apply (clarsimp simp: in_monad valid_def)
  apply clarsimp
  (* First move past all the stuff like get_cap and touch_object before it *)
  apply (clarsimp simp: in_monad)
  (* Use frule instead of drule because we'll need the get_cap assumption for later *)
  apply (frule in_inv_by_hoareD [OF get_cap_inv])
  apply clarsimp
  apply(rename_tac s b obj_ref nat list aa ba bb s'' next_cap)
  apply(prop_tac "pas_cur_domain aag s''")
   apply(erule_tac x=obj_ref in meta_allE)
   apply(erule_tac x=s in allE)
   apply force
  apply(clarsimp simp:valid_def)
  apply(erule_tac x=s'' in allE)
  apply force
  done
qed

(* Tcb_A *)
(* FIXME: I think this needs a manual proof like for resolve_address_bits. -robs
crunch ta_subset_inv: load_word_offs "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp simp: crunch_simps ignore: do_machine_op)
*)
lemma load_word_offs_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag\<rbrace> load_word_offs ptr offs \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* TcbAcc_A *)
(* FIXME: This will probably be along the same vein as load_word_offs
crunch ta_subset_inv: store_word_offs "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp simp: crunch_simps ignore: do_machine_op)
*)
lemma store_word_offs_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Ipc_A *)
(* FIXME: Needs manual proof? liftM/mapM wp rules don't seem to help. -robs
crunch ta_subset_inv: get_extra_cptrs "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' liftM_wp liftME_wp mapM_wp mapM_wp'
   simp: crunch_simps return_def)
*)
lemma get_extra_cptrs_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag\<rbrace> get_extra_cptrs buf mi \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* CSpace_A *)

(* Toby: Consider fixing broken Access proofs enough to repair old reasoning
   that affects the proofs in this file too, especially anything to do with
   invariant preservation lemmas that got broken: Can we make them such that
   they say if P (e.g. pas_refined) ignores TA then P is preserved by the
   function f if f *only* changes TA. *)
(* Note: Needed manual proof with customised precondition, just like rab. -robs *)
thm lookup_slot_for_thread_authorised
(* FIXME: Perhaps there is a better form for this that avoids us having to use it in the
   convoluted way we do in lookup_cap_and_slot_ta_subset_inv (see below). *)
lemma lookup_slot_for_thread_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and pas_refined aag and pas_cur_domain aag and K (is_subject aag thread)\<rbrace>
     lookup_slot_for_thread thread cref
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  apply(wpsimp wp: resolve_address_bits'_ta_subset_inv touch_object_wp
    simp: lookup_slot_for_thread_def resolve_address_bits_def)
  apply(rule conjI)
   using safe_addition_to_ta
   apply(clarsimp simp:pas_labels_accessible_to_def)
   using domains_distinct cur_label_to_subj
   apply force
  apply clarsimp
  apply(drule get_tcb_Some_True_False)
  using owns_thread_owns_cspace by blast

crunches lookup_slot_for_thread
  for pas_cur_domain: "pas_cur_domain aag"
  (wp: touch_object_wp')

(* Use this to simplify so stuff in the RHS of the antecedent is in terms of the return value,
   before using hoare_drop_imp_R to drop the antecedent. -robs *)
lemma hoare_imp_rev_unfold_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. (a = fst (fst r) \<and> b = snd (fst r) \<and> c = snd r) \<longrightarrow> Q r s\<rbrace>, - \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. r = ((a, b), c) \<longrightarrow> Q r s\<rbrace>, -"
  by (auto simp: validE_R_def validE_def)

(* Derived from proof of resolve_address_bits_real_cte_at. -robs *)
thm resolve_address_bits_real_cte_at
lemma resolve_address_bits_rv_ko_at:
  "\<lbrace> valid_objs and valid_cap (fst args) \<rbrace>
  resolve_address_bits args
  \<lbrace> \<lambda>rv s. ko_at (the (kheap s (fst (fst rv)))) (fst (fst rv)) s \<rbrace>, -"
unfolding resolve_address_bits_def
proof (induct args rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]
    apply (rename_tac obj_ref nat list)
    apply (simp only: cap.simps)
    apply (case_tac "nat + length list = 0")
     apply (simp add: fail_def)
    apply (simp only: if_False)
    apply (simp only: K_bind_def in_bindE_R)
    apply (elim conjE exE)
    apply (simp only: split: if_split_asm)
     apply (clarsimp simp add: in_monad)
     apply (clarsimp simp add: valid_cap_def obj_at_def)
    apply (simp only: K_bind_def in_bindE_R)
    apply (elim conjE exE)
    apply (simp only: split: if_split_asm)
     apply (frule (9) "1.hyps")
     apply (clarsimp simp: in_monad validE_def validE_R_def valid_def)
     apply (frule in_inv_by_hoareD [OF get_cap_inv])
     apply simp
     apply clarsimp
     apply (frule(1) post_by_hoare [OF touch_object_tainv.valid_objs.m_inv])
     apply (frule(1) post_by_hoare [OF get_cap_valid])
     apply (erule allE, erule impE, blast)
     apply (drule (1) bspec, simp)
    apply (clarsimp simp: in_monad)
    apply (frule in_inv_by_hoareD [OF get_cap_inv])
    apply (frule(1) post_by_hoare [OF touch_object_tainv.valid_cap.m_inv])
    apply (clarsimp simp add: valid_cap_def obj_at_def)
    done
qed

(* Derived from proof of lookup_slot_real_cte_at_wp. -robs *)
thm lookup_slot_real_cte_at_wp
lemma lookup_slot_rv_ko_at_wp [wp]:
  "\<lbrace> \<lambda>s. valid_objs s \<rbrace> lookup_slot_for_thread t addr
   \<lbrace> \<lambda>rv s. ko_at (the (kheap s (fst (fst rv)))) (fst (fst rv)) s \<rbrace>,-"
  apply (simp add: lookup_slot_for_thread_def)
  apply wp
     apply (rule resolve_address_bits_rv_ko_at)
    apply simp
    apply wp
   apply(wp touch_object_wp')
  apply clarsimp
  apply(drule get_tcb_to_unfiltered_Some)
  apply(erule_tac t=t in objs_valid_tcb_ctable)
  apply(clarsimp simp:get_tcb_def ta_filter_def split:option.splits)
  done

(* This variant is needed at times to deal with typical postconditions on its retval. -robs *)
lemma lookup_slot_for_thread_ta_subset_inv':
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  assumes Q_def: "Q = (\<lambda>rv s. (\<forall>a b c. rv = ((a, b), c) \<longrightarrow>
    ta_subset_inv aag s \<and>
    no_label_straddling_objs aag s \<and>
    pasObjectAbs aag a \<in> pas_labels_accessible_to aag (cur_label aag s) \<and>
    obj_at ((=) (the (kheap s (fst (fst rv))))) (fst (fst rv)) s))"
  shows
  (* Toby: Note, when you do stuff in your cspace, or arch-specific stuff (because it pertains
     to your own address space) everything will typically be is_subject.
     It'll only be otherwise for Notifications, Ipc etc. *)
  "\<lbrace>ta_subset_inv aag and pas_refined aag and pas_cur_domain aag and K (is_subject aag thread) and
    valid_objs\<rbrace>
     lookup_slot_for_thread thread cref
   \<lbrace>Q\<rbrace>,
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding Q_def
  apply(rule validE_allI)+
  apply(wp lookup_slot_for_thread_ta_subset_inv)
   (* Simplify to be in terms of the rv then drop antecedent and bound variables. -robs *)
   apply(rule hoare_imp_rev_unfold_R)
   apply clarsimp
   apply(rule hoare_drop_impE_R)
   apply(wpsimp wp: touch_object_ta_subset_inv lookup_slot_for_thread_ta_subset_inv)
   apply(rule hoare_vcg_conj_lift_R)
    apply(rule_tac Q'="\<lambda>_. pas_refined aag" in hoare_post_imp_R)
     apply wp
    apply(force simp:pas_refined_no_label_straddling_objs)
   apply(rule_tac Q'="\<lambda>rv s. pas_cur_domain aag s \<and> is_subject aag (fst (fst rv)) \<and>
     obj_at ((=) (the (kheap s (fst (fst rv))))) (fst (fst rv)) s" in hoare_post_imp_R)
    apply(wpsimp wp:lookup_slot_for_thread_pas_cur_domain lookup_slot_for_thread_authorised
      lookup_slot_real_cte_at_wp)
   apply(clarsimp simp:pas_labels_accessible_to_def obj_at_def)
   apply(force dest:cur_label_to_subj[OF domains_distinct])
  apply force
  done

lemma lookup_cap_and_slot_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and pas_refined aag and pas_cur_domain aag and K (is_subject aag thread) and
    valid_objs\<rbrace> \<comment> \<open>Needed for lookup_slot_rv_ko_at_wp, new version of lookup_slot_real_cte_at_wp.\<close>
     lookup_cap_and_slot thread cptr
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding lookup_cap_and_slot_def
  by (wpsimp wp: touch_object_ta_subset_inv lookup_slot_for_thread_ta_subset_inv'
    | fastforce simp: obj_at_def)+

(* Ipc_A *)
thm lookup_extra_caps_authorised lookup_cap_and_slot_authorised
lemma lookup_extra_caps_ta_subset_inv:
  (* Follow convention used in Noninterference.thy for handling pas_domains_distinct assumption. *)
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and pas_refined aag and pas_cur_domain aag and K (is_subject aag thread)\<rbrace>
     lookup_extra_caps thread buffer mi
   \<lbrace>\<lambda>_. ta_subset_inv aag
     \<comment> \<open>and pas_refined aag and pas_cur_domain aag and K (is_subject aag thread)\<close>\<rbrace>"
  apply(wpsimp wp: crunch_wps lookup_cap_and_slot_ta_subset_inv mapME_wp'
      (* lookup_extra_caps_authorised lookup_cap_and_slot_authorised *)
    simp: lookup_extra_caps_def resolve_address_bits_def)
    (* FIXME: I guess mapME_wp' will demand that all iterations will preserve every one of
       the preconditions, does this mean we have to copy them all to the postcondition too? *)
  sorry

(* KHeap_A *)
thm set_thread_state_cur_domain
(* FIXME: I think this needs a manual proof like for resolve_address_bits. -robs
crunch ta_subset_inv: set_thread_state "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp')
*)
lemma set_thread_state_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
    (\<lambda>s. pasObjectAbs aag ref \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Maybe we can trim this one out using safe_addition_to_ta. -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update ref (the (kheap s ref)) s))\<rbrace>
      set_thread_state ref ts
    \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* CSpace_A *)

lemma lookup_cap_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and (pas_refined aag and pas_cur_domain aag and K (is_subject aag thread)) and
    valid_objs\<rbrace>
     lookup_cap thread ref
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding lookup_cap_def
  by (wpsimp wp: touch_object_ta_subset_inv lookup_slot_for_thread_ta_subset_inv'
    | fastforce simp: obj_at_def)+

thm lookup_slot_for_cnode_op_authorised (* preconds taken from here *)
lemma lookup_slot_for_cnode_op_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and (pas_refined aag and pas_cur_domain aag and
      K (is_cnode_cap croot \<longrightarrow> (\<forall>x\<in>obj_refs_ac croot. is_subject aag x)))\<rbrace>
     lookup_slot_for_cnode_op is_source croot ptr depth
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding lookup_slot_for_cnode_op_def
  apply wpsimp
       apply(rule validE_allI)+
       apply(wpsimp wp: hoare_drop_impE_R resolve_address_bits_ta_subset_inv)+
  done

crunch pas_cur_domain: lookup_slot_for_cnode_op "pas_cur_domain aag"
  (wp: crunch_wps touch_objects_wp resolve_address_bits'_pas_cur_domain simp: crunch_simps)

lemma captransfer_from_words_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag\<rbrace> captransfer_from_words ptr \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  (* FIXME *)
  sorry

thm get_receive_slots_authorised (* preconds taken from here *)
lemma get_receive_slots_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and (pas_refined aag and pas_cur_domain aag and
      K (\<forall>rbuf. recv_buf = Some rbuf \<longrightarrow> is_subject aag receiver))\<rbrace>
     get_receive_slots receiver recv_buf
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  apply(cases recv_buf)
   apply(wpsimp wp: crunch_wps touch_objects_wp touch_object_wp')
  apply(wpsimp wp: crunch_wps touch_objects_wp touch_object_wp'
    (* XXX: Not helpful... *)
    lookup_slot_for_cnode_op_ta_subset_inv)
  (* FIXME *)
  sorry

(* CSpaceAcc_A *)

crunches set_cdt, set_original
  for ta_subset_inv: "ta_subset_inv aag"
  (simp: ta_subset_inv_def)

(* Note: Couldn't find an auth rule for set_cap to give a clue as to the precondition.
find_theorems set_cap name:auth *)
lemma set_cap_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and (pas_refined aag and pas_cur_domain aag
     \<comment> \<open>Note: This might be too strong. What's an appropriate condition for set_cap otherwise?\<close>
     and K (is_subject aag (fst capcref)))\<rbrace>
     set_cap cap capcref
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding set_cap_def
  apply (wpsimp wp: touch_objects_wp set_object_ta_subset_inv get_object_wp)
  using domains_distinct cur_label_to_subj
  by (fastforce intro:safe_addition_to_ta simp:pas_labels_accessible_to_def obj_at_def)

crunch ta_subset_inv: update_cdt "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp')

(* CSpace_A *)
lemma set_untyped_cap_as_full_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  (* The preconditions suggested to us by crunch. These may need some re-examining. *)
  "\<lbrace>ta_subset_inv aag and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update (fst src_slot) (the (kheap s (fst src_slot))) s)) and
    (pas_refined aag and pas_cur_domain aag and K (is_subject aag (fst src_slot)))\<rbrace>
     set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding set_untyped_cap_as_full_def
  by (wpsimp wp: crunch_wps touch_objects_wp touch_object_wp' set_cap_ta_subset_inv)

(* Deterministic_A *)

lemma set_cdt_list_ta_subset_inv:
  (* FIXME: We need a new precondition that says this object is accessible. What is reasonable? *)
  "\<lbrace>ta_subset_inv aag\<rbrace> set_cdt_list t \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding set_cdt_list_def
  apply (wpsimp wp: crunch_wps touch_objects_wp touch_object_wp')
  sorry

thm update_cdt_list_pas_refined
lemma cap_insert_ext_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag
    \<comment> \<open>Do we even need this stuff?
    and pas_refined aag
    and (pas_cur_domain aag and)
     K (is_subject aag (fst src_slot)) and K (is_subject aag (fst dest_slot))\<close>\<rbrace>
     cap_insert_ext src_parent src_slot dest_slot src_p dest_p
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding cap_insert_ext_def
  apply (wpsimp wp: crunch_wps touch_objects_wp touch_object_wp')
  sorry (* FIXME *)

(* CSpace_A *)
(* Note: cap_insert is an example of a function for which crunching with `touch_object_wp`
   propagates up a new "true for state if object was added to TA" precondition for each object
   it calls touch_object on. But we will use `safe_addition_to_ta` to discharge these. -robs *)
thm set_cap_pas_refined get_cap_wp
lemma cap_insert_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst src_slot)) and K (is_subject aag (fst dest_slot)) and
     \<comment> \<open>Demanded by set_cap_pas_refined\<close>
     pspace_aligned and valid_vspace_objs and valid_arch_state and
     (\<lambda>s. is_transferable_in src_slot s \<and> \<not> Option.is_none (cdt s src_slot) \<longrightarrow>
          (pasObjectAbs aag (fst $ the $ cdt s src_slot), Control, pasSubject aag) \<in> pasPolicy aag))\<rbrace>
     cap_insert new_cap src_slot dest_slot
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding cap_insert_def
  apply (wpsimp wp: crunch_wps touch_objects_wp touch_object_wp'
    set_original_ta_subset_inv cap_insert_ext_ta_subset_inv update_cdt_ta_subset_inv
    set_cap_ta_subset_inv set_untyped_cap_as_full_ta_subset_inv get_cap_wp)
  apply(rename_tac s cap cap')
  (* FIXME: There must a better intro/dest rule we can prove and use to improve this process. *)
  apply(drule_tac p="fst src_slot" and ko="the (kheap s (fst src_slot))" in safe_addition_to_ta)
     apply force
    apply(clarsimp simp:pas_labels_accessible_to_def)
    using domains_distinct cur_label_to_subj
    apply force
   apply(force dest:cte_at_pspace simp:obj_at_def)
  apply(drule_tac p="fst dest_slot" and ko="the (kheap s (fst dest_slot))" in safe_addition_to_ta)
     apply force
    apply(clarsimp simp:pas_labels_accessible_to_def)
    using domains_distinct cur_label_to_subj
    apply force
   apply(force dest:cte_at_pspace simp:obj_at_def)
  apply clarsimp
  apply(drule_tac p="fst src_slot" and ko="the (kheap s (fst src_slot))" in safe_addition_to_ta)
     apply force
    apply(clarsimp simp:pas_labels_accessible_to_def)
    using domains_distinct cur_label_to_subj
    apply force
   apply(force dest:cte_at_pspace simp:obj_at_def)
  apply clarsimp
  by (metis (full_types) cap_auth_caps_of_state cte_wp_at_caps_of_state)

(* Ipc_A *)
(* FIXME: Prove or improve. Preconditions below were found using crunch.
crunch ta_subset_inv: transfer_caps_loop "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp')
*)
lemma transfer_caps_loop_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and (pas_refined aag and pas_cur_domain aag and
    pspace_aligned and valid_vspace_objs and valid_arch_state)\<rbrace>
     transfer_caps_loop ep rcv_buffer n caps slots mi
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* KHeap_A *)
(* FIXME: Prove or improve.
crunch ta_subset_inv: as_user "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp')
*)
lemma as_user_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
   (no_label_straddling_objs aag and
   (\<lambda>s. pasObjectAbs aag tptr \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
   (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update tptr (the (kheap s tptr)) s))\<rbrace>
     as_user tptr f
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

crunch pas_cur_domain: get_receive_slots "pas_cur_domain aag"
  (wp: crunch_wps touch_objects_wp resolve_address_bits'_pas_cur_domain
     lookup_slot_for_cnode_op_pas_cur_domain)

(* Ipc_A *)
lemma transfer_caps_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and (pas_refined aag and pas_cur_domain aag and
      K (\<forall>rbuf. recv_buf = Some rbuf \<longrightarrow> is_subject aag receiver) and
      pspace_aligned and valid_vspace_objs and valid_arch_state)\<rbrace>
     transfer_caps info caps endpoint receiver recv_buf
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding transfer_caps_def
  by (wpsimp wp: crunch_wps touch_objects_wp touch_object_wp'
    transfer_caps_loop_ta_subset_inv get_receive_slots_ta_subset_inv get_receive_slots_authorised
    get_receive_slots_pas_cur_domain)

(* TcbAcc_A *)
(* FIXME: Prove or improve.
crunch ta_subset_inv: set_mrs "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp')
*)
lemma set_mrs_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
    (\<lambda>s. pasObjectAbs aag thread \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update thread (the (kheap s thread)) s))\<rbrace>
     set_mrs thread buf msgs
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Tcb_A *)

(* FIXME: Prove or improve.
crunch ta_subset_inv: copy_mrs "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp')
*)
lemma copy_mrs_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
    (\<lambda>s. pasObjectAbs aag sender \<in> pas_labels_accessible_to aag (cur_label aag s)) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update sender (the (kheap s sender)) s))) and
    ((\<lambda>s. pasObjectAbs aag receiver \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update receiver (the (kheap s receiver)) s)))\<rbrace>
     copy_mrs sender sbuf receiver rbuf n
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
crunch ta_subset_inv: do_normal_transfer "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp')
*)
lemma do_normal_transfer_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag sender \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update sender (the (kheap s sender)) s))) and
    (pas_refined aag and pas_cur_domain aag and K (is_subject aag sender)) and
    ((\<lambda>s. pasObjectAbs aag receiver \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update receiver (the (kheap s receiver)) s)))\<rbrace>
     do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Ipc_A *)
lemma setup_caller_cap_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag sender
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update sender (the (kheap s sender)) s))) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst (sender, tcb_cnode_index 2))) and
     K (is_subject aag (fst (receiver, tcb_cnode_index 3))) and
     pspace_aligned and
     valid_vspace_objs and
     valid_arch_state and
     (\<lambda>s. is_transferable_in (sender, tcb_cnode_index 2) s \<and>
           \<not> Option.is_none (cdt s (sender, tcb_cnode_index 2)) \<longrightarrow>
           (pasObjectAbs aag
             (fst $ the $ cdt s (sender, tcb_cnode_index 2)),
            Control, pasSubject aag)
           \<in> pasPolicy aag))\<rbrace>
   setup_caller_cap sender receiver grant \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
crunch ta_subset_inv: do_ipc_transfer "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma do_ipc_transfer_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag sender
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    ((\<lambda>s. ta_subset_inv aag (ms_ta_obj_update sender (the (kheap s sender)) s)) and
     pas_refined aag and
     pas_cur_domain aag and
     K (is_subject aag sender) and
     (\<lambda>s. pasObjectAbs aag receiver
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update receiver (the (kheap s receiver)) s)))\<rbrace>
   do_ipc_transfer sender ep badge grant receiver
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
crunch ta_subset_inv: send_ipc "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp') *)
lemma send_ipc_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag epptr \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    ((\<lambda>s. pasObjectAbs aag thread \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim these out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update thread (the (kheap s thread)) s))) and
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update epptr (the (kheap s epptr)) s)) and
    (pas_refined aag and pas_cur_domain aag and K (is_subject aag thread)) and
    (pspace_aligned and valid_vspace_objs and valid_arch_state and
     (\<lambda>s. is_transferable_in (thread, tcb_cnode_index 2) s \<and>
           \<not> Option.is_none (cdt s (thread, tcb_cnode_index 2)) \<longrightarrow>
           (pasObjectAbs aag (fst $ the $ cdt s (thread, tcb_cnode_index 2)), Control, pasSubject aag)
           \<in> pasPolicy aag))\<rbrace>
     send_ipc block call badge can_grant can_grant_reply thread epptr
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Decode_A *)

(* FIXME: Prove or improve.
   NB: Those Hoare triples targetting undefined look worrying.
crunch ta_subset_inv: decode_read_registers "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma decode_read_registers_ta_subset_inv:
  "decode_read_registers data cap \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_read_registers_pas_cur_domain:
  "decode_read_registers data cap \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
   NB: More Hoare triples targetting undefined here.
crunch ta_subset_inv: decode_write_registers "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma decode_write_registers_ta_subset_inv:
  "decode_write_registers data cap \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_write_registers_pas_cur_domain:
  "decode_write_registers data cap \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
   NB: More Hoare triples targetting undefined here.
   Is this a case of it not being reasonable to prove this lemma at this level of granularity?
crunch ta_subset_inv: decode_copy_registers "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma decode_copy_registers_ta_subset_inv:
  "decode_copy_registers data cap extra_caps \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_copy_registers_pas_cur_domain:
  "decode_copy_registers data cap extra_caps \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

(* KHeap_A *)
(* FIXME: Prove or improve.
crunch ta_subset_inv: thread_set "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma thread_set_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag tptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update tptr (the (kheap s tptr)) s))\<rbrace>
   thread_set f tptr \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Ipc_A *)
(* FIXME: Prove or improve.
crunch ta_subset_inv: send_fault_ipc "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma send_fault_ipc_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag tptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag tptr)) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update tptr (the (kheap s tptr)) s)) and
    (pspace_aligned and valid_vspace_objs and valid_arch_state and
     (\<lambda>s. is_transferable_in (tptr, tcb_cnode_index 2) s \<and>
           \<not> Option.is_none (cdt s (tptr, tcb_cnode_index 2)) \<longrightarrow>
           (pasObjectAbs aag
             (fst $ the $ cdt s (tptr, tcb_cnode_index 2)),
            Control, pasSubject aag)
           \<in> pasPolicy aag))\<rbrace>
   send_fault_ipc tptr fault \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* CSpace_A *)
lemma lookup_target_slot_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and
     K (is_cnode_cap croot \<longrightarrow>
        (\<forall>x\<in>obj_refs_ac croot. is_subject aag x)))\<rbrace>
   lookup_target_slot croot ptr depth \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* CSpaceAcc_A *)
lemma ensure_empty_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag (fst slot)
           \<in> pas_labels_accessible_to aag (cur_label aag s)))\<rbrace>
   ensure_empty slot \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Decode_A *)

lemma check_prio_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag auth_tcb
           \<in> pas_labels_accessible_to aag (cur_label aag s)))\<rbrace>
   check_prio new_prio auth_tcb \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_set_priority_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   decode_set_priority args cap slot extra_caps
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_set_sched_params_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   decode_set_sched_params args cap slot extra_caps
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_set_mcpriority_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   decode_set_mcpriority args cap slot extra_caps
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_unbind_notification_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   decode_unbind_notification cap \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma arch_decode_irq_control_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and
     K (is_cnode_cap (cps ! 0) \<longrightarrow>
        (\<forall>x\<in>obj_refs_ac (cps ! 0). is_subject aag x))) and
    no_label_straddling_objs aag\<rbrace>
   arch_decode_irq_control_invocation label args src_slot cps
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_irq_control_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and
     K (is_cnode_cap (cps ! 0) \<longrightarrow>
        (\<forall>x\<in>obj_refs_ac (cps ! 0). is_subject aag x))) and
    no_label_straddling_objs aag\<rbrace>
   decode_irq_control_invocation label args src_slot cps
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_asid_control_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and
     K (is_cnode_cap (fst (extra_caps ! 1)) \<longrightarrow>
        (\<forall>x\<in>obj_refs_ac (fst (extra_caps ! 1)). is_subject aag x))) and
    no_label_straddling_objs aag\<rbrace>
   decode_asid_control_invocation label args cte cap extra_caps
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma check_slot_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
       (\<lambda>s. pasObjectAbs aag slot
             \<in> pas_labels_accessible_to aag (cur_label aag s)))\<rbrace>
   check_slot slot test
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_untyped_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and (pas_refined aag and pas_cur_domain aag) and
    no_label_straddling_objs aag\<rbrace>
   decode_untyped_invocation label args slot cap excaps
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_untyped_invocation_pas_cur_domain:
  "decode_untyped_invocation label args slot cap excaps \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

lemma decode_asid_pool_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag (acap_obj cap)
           \<in> pas_labels_accessible_to aag (cur_label aag s)))\<rbrace>
   decode_asid_pool_invocation label args cte cap extra_caps
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_asid_pool_invocation_pas_cur_domain:
  "decode_asid_pool_invocation label args cte cap extra_caps \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

(* IpcCancel_A *)
lemma is_final_cap_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag\<rbrace> is_final_cap cap \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Decode_A *)
lemma decode_bind_notification_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   decode_bind_notification cap extra_caps \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_bind_notification_pas_cur_domain:
  "decode_bind_notification cap extra_caps \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

(* ArchDecode_A *)
lemma arch_decode_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
    (pas_refined aag and pas_cur_domain aag and
     K (is_cnode_cap (fst (extra_caps ! 1)) \<longrightarrow>
        (\<forall>x\<in>obj_refs_ac (fst (extra_caps ! 1)). is_subject aag x)))\<rbrace>
   arch_decode_invocation label args x_slot cte cap extra_caps
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma arch_decode_invocation_pas_cur_domain:
  "arch_decode_invocation label args x_slot cte cap extra_caps \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
crunch ta_subset_inv: decode_invocation "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
(* Decode_A *)
lemma decode_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and
     no_label_straddling_objs aag) and
    K (is_cnode_cap (map fst excaps ! 0) \<longrightarrow>
       (\<forall>x\<in>obj_refs_ac (map fst excaps ! 0). is_subject aag x)) and
    K (is_cnode_cap (fst (excaps ! 1)) \<longrightarrow>
       (\<forall>x\<in>obj_refs_ac (fst (excaps ! 1)). is_subject aag x))\<rbrace>
   decode_invocation label args cap_index slot cap excaps 
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma decode_invocation_pas_cur_domain:
  "decode_invocation label args cap_index slot cap excaps \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

(* Retype_A *)

(* FIXME: Prove or improve.
crunch ta_subset_inv: delete_objects "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore: do_machine_op)
*)
lemma delete_objects_ta_subset_inv:
  "delete_objects ptr bits \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove.
crunch ta_subset_inv: reset_untyped_cap "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore: do_machine_op)
*)
lemma reset_untyped_cap_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag (fst src_slot)
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst src_slot)))\<rbrace>
   reset_untyped_cap src_slot \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove.
crunch ta_subset_inv: retype_region "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma retype_region_ta_subset_inv:
  "retype_region ptr numObjects o_bits type dev \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove.
crunch ta_subset_inv: create_cap "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma create_cap_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
    (pas_refined aag and pas_cur_domain aag)\<rbrace>
   create_cap type bits untyped is_device dest_oref \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove.
crunch ta_subset_inv: invoke_untyped "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma invoke_untyped_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and pas_refined aag and
     pas_cur_domain aag)\<rbrace>
   invoke_untyped ui \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* IpcCancel_A *)

(* FIXME: Prove or improve.
crunch ta_subset_inv: cancel_all_ipc "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma cancel_all_ipc_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag epptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update epptr (the (kheap s epptr)) s))\<rbrace>
   cancel_all_ipc epptr \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
crunch ta_subset_inv: cancel_all_signals "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma cancel_all_signals_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag ntfnptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update ntfnptr (the (kheap s ntfnptr)) s))\<rbrace>
   cancel_all_signals ntfnptr \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* KHeap_A *)
(* FIXME: Prove.
crunch ta_subset_inv: set_irq_state "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)
lemma set_irq_state_ta_subset_inv:
  "set_irq_state state irq \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma set_bound_notification_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag ref
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update ref (the (kheap s ref)) s))\<rbrace>
   set_bound_notification ref ntfn \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* IpcCancel_A *)

lemma empty_slot_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag (fst slot)
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst slot)))\<rbrace>
   empty_slot slot cleanup_info \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma cap_delete_one_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag (fst slot)
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst slot)))\<rbrace>
   cap_delete_one slot \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
crunch ta_subset_inv: reply_cancel_ipc "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma reply_cancel_ipc_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag tptr
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update tptr (the (kheap s tptr)) s))) and
    (pas_refined aag and pas_cur_domain aag)\<rbrace>
   reply_cancel_ipc tptr \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
crunch ta_subset_inv: cancel_ipc "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma cancel_ipc_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag tptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update tptr (the (kheap s tptr)) s)) and
    (pas_refined aag and pas_cur_domain aag)\<rbrace>
   cancel_ipc tptr \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME
crunch ta_subset_inv: unbind_maybe_notification "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma unbind_maybe_notification_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag ntfnptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update ntfnptr (the (kheap s ntfnptr)) s))\<rbrace>
   unbind_maybe_notification ntfnptr \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Ipc_A *)

(* FIXME: Prove or improve.
crunch ta_subset_inv: update_waiting_ntfn "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma update_waiting_ntfn_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag ntfnptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update ntfnptr (the (kheap s ntfnptr)) s))\<rbrace>
   update_waiting_ntfn ntfnptr queue bound_tcb badge 
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove or improve.
crunch ta_subset_inv: send_signal "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma send_signal_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag ntfnptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update ntfnptr (the (kheap s ntfnptr)) s)) and
    (pas_refined aag and pas_cur_domain aag)\<rbrace>
   send_signal ntfnptr badge \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* IpcCancel_A *)
(* FIXME: Prove or improve.
crunch ta_subset_inv: suspend "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma suspend_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag thread
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update thread (the (kheap s thread)) s)) and
     pas_refined aag and
     pas_cur_domain aag)\<rbrace>
   suspend thread \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Tcb_A *)

(* FIXME: Prove
crunch ta_subset_inv: setup_reply_master "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma setup_reply_master_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag thread
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst (thread, tcb_cnode_index 2))))\<rbrace>
   setup_reply_master thread \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME: Prove or improve
crunch ta_subset_inv: restart "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma restart_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag thread
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    ((\<lambda>s. ta_subset_inv aag (ms_ta_obj_update thread (the (kheap s thread)) s)) and
     pas_refined aag and
     pas_cur_domain aag) and
    K (is_subject aag (fst (thread, tcb_cnode_index 2)))\<rbrace>
   restart thread \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* CSpace_A *)
(* FIXME
crunch ta_subset_inv: cap_swap "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma cap_swap_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag
           (machine_state_update
             (touched_addresses_update
               ((\<union>) (\<Union>(x, y)\<in>{(p, ko).
                                p \<in> {fst slot1, fst slot2} \<and>
                                ko_at ko p s}.
                         obj_range x y)))
             s)) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst slot1))) and
    K (is_subject aag (fst slot2))\<rbrace>
   cap_swap cap1 slot1 cap2 slot2 \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* ArchVSpace_A *)

(* FIXME
crunch ta_subset_inv: set_vm_root "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)
lemma set_vm_root_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   set_vm_root tcb \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME
crunch ta_subset_inv: delete_asid_pool "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)
lemma delete_asid_pool_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag ptr
           \<in> pas_labels_accessible_to aag (cur_label aag s)))\<rbrace>
   delete_asid_pool base ptr \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* CSpace_A *)

lemma cap_swap_for_delete_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (\<lambda>s. ta_subset_inv aag
           (machine_state_update
             (touched_addresses_update
               ((\<union>) (\<Union>(x, y)\<in>{(p, ko).
                                p \<in> {fst slot1, fst slot2} \<and>
                                ko_at ko p s}.
                         obj_range x y)))
             s)) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst slot1)) and
     K (is_subject aag (fst slot2)))\<rbrace>
   cap_swap_for_delete slot1 slot2 \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma deleting_irq_handler_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and pas_refined aag and
     pas_cur_domain aag)\<rbrace>
   deleting_irq_handler irq \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* ArchVSpaceAcc_A *)

lemma store_pte_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   store_pte p pte \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma copy_global_mappings_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   copy_global_mappings new_pm \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* ArchVSpace_A *)

lemma unmap_page_table_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   unmap_page_table asid vaddr pt \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma delete_asid_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   delete_asid asid pt \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma arch_finalise_cap_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   arch_finalise_cap c x \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* CSpace_A *)
(* FIXME: Prove or improve.
crunch ta_subset_inv: rec_del "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma rec_del_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and (pas_refined aag and pas_cur_domain aag) and
   no_label_straddling_objs aag\<rbrace>
   rec_del rdc \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Tcb_A *)

(* FIXME
crunch ta_subset_inv: check_cap_at "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma check_cap_at_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag (fst slot)
           \<in> pas_labels_accessible_to aag (cur_label aag s)))\<rbrace>
  check_cap_at cap slot m \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma check_cap_at_pas_cur_domain:
  "check_cap_at cap slot m \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

(* FIXME
crunch ta_subset_inv: invoke_domain "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma invoke_domain_ta_subset_inv:
  "invoke_domain thread domain \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma get_mrs_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag thread
           \<in> pas_labels_accessible_to aag (cur_label aag s)))\<rbrace>
   get_mrs thread buf info \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma bind_notification_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag ntfnptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update ntfnptr (the (kheap s ntfnptr)) s)) and
    ((\<lambda>s. pasObjectAbs aag tcbptr
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update tcbptr (the (kheap s tcbptr)) s)))\<rbrace>
   bind_notification tcbptr ntfnptr \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Ipc_A *)

lemma handle_fault_reply_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   handle_fault_reply fault thread label msg 
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME
crunch ta_subset_inv: do_reply_transfer "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma do_reply_transfer_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag receiver
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    ((\<lambda>s. pasObjectAbs aag sender
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update sender (the (kheap s sender)) s)) and
     pas_refined aag and
     pas_cur_domain aag and
     K (is_subject aag sender) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update receiver (the (kheap s receiver)) s))) and
    ((\<lambda>s. pasObjectAbs aag (fst slot)
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     K (is_subject aag (fst slot)))\<rbrace>
  do_reply_transfer sender receiver slot grant 
  \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma handle_fault_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag thread
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag thread) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update thread (the (kheap s thread)) s)) and
     pspace_aligned and
     valid_vspace_objs and
     valid_arch_state and
     (\<lambda>s. is_transferable_in (thread, tcb_cnode_index 2) s \<and>
           \<not> Option.is_none (cdt s (thread, tcb_cnode_index 2)) \<longrightarrow>
           (pasObjectAbs aag
             (fst $ the $ cdt s (thread, tcb_cnode_index 2)),
            Control, pasSubject aag)
           \<in> pasPolicy aag))\<rbrace>
   handle_fault thread ex \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma reply_from_kernel_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag thread
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update thread (the (kheap s thread)) s)))\<rbrace>
   reply_from_kernel thread x \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma complete_signal_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag ntfnptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    ((\<lambda>s. pasObjectAbs aag tcb
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update tcb (the (kheap s tcb)) s))) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update ntfnptr (the (kheap s ntfnptr)) s))\<rbrace>
   complete_signal ntfnptr tcb  \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma receive_signal_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
    ((\<lambda>s. pasObjectAbs aag thread
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
     (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update thread (the (kheap s thread)) s)))\<rbrace>
   receive_signal thread cap is_blocking \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* CSpace_A *)
(* FIXME
crunch ta_subset_inv: cap_move "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma cap_move_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag
           (machine_state_update
             (touched_addresses_update
               ((\<union>) (\<Union>(x, y)\<in>{(p, ko).
                                p \<in> {fst dest_slot, fst src_slot} \<and>
                                ko_at ko p s}.
                         obj_range x y)))
             s)) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst dest_slot))) and
    K (is_subject aag (fst src_slot))\<rbrace>
   cap_move new_cap src_slot dest_slot \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* IpcCancel_A *)
(* FIXME
crunch ta_subset_inv: cancel_badged_sends "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma cancel_badged_sends_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag epptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update epptr (the (kheap s epptr)) s))\<rbrace>
  cancel_badged_sends epptr badge \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma unbind_notification_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag tcb
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close> 
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update tcb (the (kheap s tcb)) s))\<rbrace>
   unbind_notification tcb \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>" 
  sorry

(* ArchInterrupt_A *)
lemma arch_invoke_irq_handler_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag\<rbrace> arch_invoke_irq_handler irqh_invocation \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Interrupt_A *)

(* FIXME:
crunch ta_subset_inv: invoke_irq_handler "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)
lemma invoke_irq_handler_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and pas_refined aag and
     pas_cur_domain aag) and
    (pspace_aligned and valid_vspace_objs and valid_arch_state)\<rbrace>
   invoke_irq_handler irqh_invocation \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME
crunch ta_subset_inv: handle_interrupt "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)
lemma handle_interrupt_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
    (pas_refined aag and pas_cur_domain aag)\<rbrace>
   handle_interrupt irq \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma invoke_irq_control_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and pspace_aligned and
     valid_vspace_objs and
     valid_arch_state)\<rbrace>
   invoke_irq_control invok \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* CSpace_A *)

crunch ta_subset_inv: cap_delete "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)

(* FIXME: There seems to be a type error here!?
crunch ta_subset_inv: cap_revoke "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma cap_revoke_ta_subset_inv:
  "cap_revoke slot \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma invoke_cnode_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and pspace_aligned and
     valid_vspace_objs and
     valid_arch_state) and
    no_label_straddling_objs aag\<rbrace>
   invoke_cnode i \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Arch_A *)
(* FIXME
crunch ta_subset_inv: perform_asid_control_invocation "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
lemma perform_asid_control_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
    (pas_refined aag and pas_cur_domain aag) and
    (pspace_aligned and valid_vspace_objs and valid_arch_state)\<rbrace>
   perform_asid_control_invocation iv \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma arch_invoke_irq_control_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and pspace_aligned and
     valid_vspace_objs and
     valid_arch_state)\<rbrace>
   arch_invoke_irq_control invok \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma perform_pt_inv_map_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (\<lambda>s. ta_subset_inv aag
           (machine_state_update
             (touched_addresses_update
               ((\<union>) (\<Union>(x, y)\<in>{(p, ko).
                                p \<in> {fst ct_slot, slot} \<and>
                                ko_at ko p s}.
                         obj_range x y)))
             s)) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst ct_slot))) and
    no_label_straddling_objs aag\<rbrace>
   perform_pt_inv_map cap ct_slot pte slot
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma perform_pt_inv_unmap_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
    (\<lambda>s. pasObjectAbs aag (fst ct_slot)
          \<in> pas_labels_accessible_to aag (cur_label aag s)) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst ct_slot)))\<rbrace>
   perform_pt_inv_unmap cap ct_slot \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma perform_page_table_invocation_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and
     no_label_straddling_objs aag)\<rbrace>
   perform_page_table_invocation iv \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma perform_pg_inv_map_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag
           (machine_state_update
             (touched_addresses_update
               ((\<union>) (\<Union>(x, y)\<in>{(p, ko).
                                p \<in> {fst ct_slot, slot} \<and>
                                ko_at ko p s}.
                         obj_range x y)))
             s)) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst ct_slot))) and
    no_label_straddling_objs aag\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot 
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma perform_pg_inv_unmap_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
    (\<lambda>s. pasObjectAbs aag (fst ct_slot)
          \<in> pas_labels_accessible_to aag (cur_label aag s)) and
    (pas_refined aag and pas_cur_domain aag and
     K (is_subject aag (fst ct_slot)))\<rbrace>
   perform_pg_inv_unmap cap ct_slot \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma perform_page_invocation_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and
     no_label_straddling_objs aag)\<rbrace>
   perform_page_invocation iv \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma store_asid_pool_entry_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag pool_ptr
           \<in> pas_labels_accessible_to aag (cur_label aag s))) and
    \<comment> \<open> FIXME: Trim this out using safe_addition_to_ta? -robs \<close>
    (\<lambda>s. ta_subset_inv aag (ms_ta_obj_update pool_ptr (the (kheap s pool_ptr)) s))\<rbrace>
   store_asid_pool_entry pool_ptr asid ptr
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma arch_perform_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (pas_refined aag and pas_cur_domain aag and
     no_label_straddling_objs aag) and
    (pspace_aligned and valid_vspace_objs and valid_arch_state)\<rbrace>
   arch_perform_invocation i \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* Syscall_A *)
(* FIXME
crunch ta_subset_inv: handle_yield "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
thm handle_yield_pas_refined
lemma handle_yield_ta_subset_inv:
  "handle_yield \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma syscall_ta_subset_inv:
  "syscall m_fault h_fault m_error h_error m_finalise \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma syscall_pas_cur_domain:
  "syscall m_fault h_fault m_error h_error m_finalise \<lbrace>pas_cur_domain aag\<rbrace>"
  sorry

thm perform_invocation_pas_refined
lemma perform_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and pas_refined aag and pas_cur_domain aag) and
    (pspace_aligned and valid_vspace_objs and valid_arch_state)\<rbrace>
   perform_invocation calling blocking oper \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

thm invoke_tcb_pas_refined
lemma invoke_tcb_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and pas_refined aag and pas_cur_domain aag) and
    (pspace_aligned and valid_vspace_objs and valid_arch_state)\<rbrace>
   invoke_tcb tcbi \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME
crunch ta_subset_inv: handle_invocation "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
*)
thm handle_invocation_pas_refined
lemma handle_invocation_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
    (pas_refined aag and pas_cur_domain aag) and
    (pspace_aligned and valid_vspace_objs and valid_arch_state)\<rbrace>
   handle_invocation calling blocking \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace> "
  sorry

lemma delete_caller_cap_ta_subset_inv:
  assumes domains_distinct[wp]: "pas_domains_distinct aag"
  shows
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag (fst (t, tcb_cnode_index 3))
           \<in> pas_labels_accessible_to aag (cur_label aag s)) and
     pas_refined aag and
     pas_cur_domain aag and
     K (is_subject aag (fst (t, tcb_cnode_index 3))))\<rbrace>
   delete_caller_cap t \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma handle_reply_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag and
    (pas_refined aag and pas_cur_domain aag)\<rbrace>
   handle_reply \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* FIXME
crunch ta_subset_inv: handle_event "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)
lemma handle_event_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and pas_refined aag and
     pas_cur_domain aag and
     pspace_aligned and
     valid_vspace_objs and
     valid_arch_state)\<rbrace>
   handle_event ev \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

(* For schedule_if *)

(* Arch_A *)
lemma arch_mask_interrupts_ta_subset_inv:
  "arch_mask_interrupts m irqs \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma arch_domainswitch_flush_ta_subset_inv:
  "arch_domainswitch_flush \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

(* ArchVSpace_A *)
lemma arch_switch_domain_kernel_ta_subset_inv:
  "arch_switch_domain_kernel newdom \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

(* Deterministic_A *)
lemma set_scheduler_action_ta_subset_inv:
  "set_scheduler_action action \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

(* Schedule_A *)

(* FIXME
crunch ta_subset_inv: switch_to_idle_thread "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)
lemma switch_to_idle_thread_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   switch_to_idle_thread \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma guarded_switch_to_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag thread
           \<in> pas_labels_accessible_to aag (cur_label aag s)))\<rbrace>
   guarded_switch_to thread \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

lemma choose_thread_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace> choose_thread 
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding choose_thread_def
  apply (wpsimp wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
  sorry

(* FIXME
crunch ta_subset_inv: schedule_choose_new_thread "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)
lemma schedule_choose_new_thread_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace>
   schedule_choose_new_thread \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding schedule_choose_new_thread_def
  apply (wpsimp wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
  sorry

(* FIXME
crunch ta_subset_inv: switch_to_thread "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)

lemma switch_to_thread_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and
    (no_label_straddling_objs aag and
     (\<lambda>s. pasObjectAbs aag t
           \<in> pas_labels_accessible_to aag (cur_label aag s)))\<rbrace>
   switch_to_thread t \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding switch_to_thread_def
  apply (wpsimp wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
  sorry

(* FIXME
crunch ta_subset_inv: schedule "ta_subset_inv aag"
  (wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps ignore:do_machine_op)
*)
lemma schedule_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace> schedule 
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  unfolding schedule_def
  apply (wpsimp wp: crunch_wps touch_objects_wp touch_object_wp' simp: crunch_simps)
  sorry

(* Need to import InfoFlow.ADT_IF or later theories for the following section: *)

\<comment> \<open> Instead of @{term\<open>call_kernel\<close>}, prove for monads used for each step of @{term\<open>ADT_A_if\<close>}. \<close>

crunches check_active_irq_if
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps simp: ta_subset_inv_def ignore: do_machine_op)

lemma do_user_op_if_ta_subset_inv:
  "do_user_op_if uop tc \<lbrace>ta_subset_inv aag\<rbrace>"
  sorry

lemma thread_set_as_user_side_invs:
  "\<lbrace>\<lambda>s. pas_refined aag s \<and>
        pas_cur_domain aag s \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_arch_state s\<rbrace>
   thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set uc (tcb_arch tcb)\<rparr>) t
   \<lbrace>\<lambda>_ s. no_label_straddling_objs aag s \<and>
        pas_refined aag s \<and>
        pas_cur_domain aag s \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_arch_state s\<rbrace>"
  apply(rule_tac Q="\<lambda>_ s. pas_refined aag s \<and> pas_cur_domain aag s \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_arch_state s"
    in hoare_strengthen_post)
   apply(clarsimp simp:thread_set_as_user[where f="\<lambda>_. uc", simplified])
   apply(wpsimp wp:crunch_wps simp:crunch_simps)
  by force

lemma cur_thread_accessible:
  (* assumes domains_distinct: "pas_domains_distinct aag" *)
  shows
  "\<lbrakk>ta_subset_inv aag s; no_label_straddling_objs aag s;
    pas_refined aag s; pas_cur_domain aag s; pspace_aligned s;
    valid_vspace_objs s; valid_arch_state s\<rbrakk>
   \<Longrightarrow> pasObjectAbs aag (cur_thread s) \<in> pas_labels_accessible_to aag (cur_label aag s)"
  (* using domains_distinct
  apply(frule cur_label_to_subj) *)
  apply(clarsimp simp:pas_labels_accessible_to_def)
  (* FIXME: We need to know something about cur_thread here. *)
  sorry

lemma cur_thread_ta_update:
  "\<lbrakk>ta_subset_inv aag s; no_label_straddling_objs aag s\<rbrakk>
   \<Longrightarrow> ta_subset_inv aag (ms_ta_obj_update (cur_thread s) (the (kheap s (cur_thread s))) s)"
  sorry

crunches kernel_entry_if
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps thread_set_as_user_side_invs touch_object_wp'
       cur_thread_accessible cur_thread_ta_update
   simp: crunch_simps )

crunches handle_preemption_if
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps simp: crunch_simps ta_subset_inv_def no_label_straddling_objs_def
   ignore: do_machine_op)

lemma schedule_no_label_straddling_objs:
  "schedule \<lbrace>no_label_straddling_objs aag\<rbrace>"
  sorry

lemma activate_thread_ta_subset_inv:
  "\<lbrace>ta_subset_inv aag and no_label_straddling_objs aag\<rbrace> activate_thread 
   \<lbrace>\<lambda>_. ta_subset_inv aag\<rbrace>"
  sorry

crunches schedule_if
  for ta_subset_inv: "ta_subset_inv aag"
  (wp: crunch_wps schedule_no_label_straddling_objs)

\<comment> \<open> Now that it's true for the monads of @{term\<open>ADT_A_if\<close>}, seems it's true
     for @{term\<open>call_kernel\<close>} as well. \<close>

(* End of part that needs InfoFlow.ADT_IF *)

end

locale ADT_IF_L2Partitioned = ArchL2Partitioned gentypes paddr_L2_colour label_L2_colour
  (* FIXME: Not sure how to get rid of this "RISCV64." -robs *)
  for gentypes :: "('a \<times> 'colour) itself"
  and paddr_L2_colour :: "RISCV64.paddr \<Rightarrow> 'colour"
  and label_L2_colour :: "'a \<Rightarrow> 'colour" +
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