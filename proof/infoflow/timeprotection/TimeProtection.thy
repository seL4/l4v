(*
 * Copyright 2021, UNSW (ABN 57 195 873 179),
 * Copyright 2021, The University of Melbourne (ABN 84 002 705 224).
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory TimeProtection
imports "Word_Lib.WordSetup"
  InfoFlow.Noninterference_Base
  InfoFlow.Noninterference_Base_Refinement
  Lib.Eisbach_Methods
begin

datatype vaddr = VAddr machine_word
datatype paddr = PAddr machine_word


(*
     cache(s)
     time
     other_state
     regs
*)

(*
  FLUSHABLE
  everything changes it somehow
  it affects everything

  PARTITIONABLE
  address \<Rightarrow> time

  the cache touch fn, given some 'a'


cache impact fn
inputs:
  - address
  - fch
  - pch
outputs:
  - new fch
  - new pch
  - time taken
*)



\<comment> \<open> flushable (fch) and partitionable (pch) caches\<close>
type_synonym 'fch_cachedness fch = "vaddr \<Rightarrow> 'fch_cachedness"
type_synonym 'pch_cachedness pch = "paddr \<Rightarrow> 'pch_cachedness"
type_synonym 'fch fch_impact = "vaddr \<Rightarrow> 'fch \<Rightarrow> 'fch"
(* Note: This `pch_impact` version only supports a writethrough `fch`. *)
type_synonym 'pch pch_impact = "paddr \<Rightarrow> 'pch \<Rightarrow> 'pch"
(* FIXME: If we want to support a writeback `fch`, we'll need to use a type signature like this
  instead (note we'll also need to add the page table state as an argument, to get the paddr).
  This is because when a read or write evicts a dirty `fch` entry, that dirty bit (and value)
  will need to be propagated to the corresponding `pch` entry. -robs.
type_synonym ('fch,'pch) pch_impact = "vaddr \<Rightarrow> 'fch \<Rightarrow> 'pch \<Rightarrow> 'pch" *)

type_synonym time = nat

datatype 'userdomain domain = Sched | User 'userdomain

record ('fch,'pch,'regs,'other_state) state =
  fch :: "'fch" \<comment> \<open> flushable cache\<close>
  pch :: "'pch" \<comment> \<open> partitionable cache \<close>
  tm :: time
  regs :: 'regs
  other_state :: 'other_state


locale time_protection =
  (* "(a, b) \<in> collides_in_pch" = "a may cause b to be evicted from or loaded to the pch" *)
  fixes collides_in_pch :: "paddr rel"
  assumes collides_with_equiv: "equiv UNIV collides_in_pch"

  fixes fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  fixes pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"

  fixes fch_read_impact :: "'fch fch_impact"
  fixes pch_read_impact :: "'pch pch_impact"

  assumes pch_partitioned_read:
    "(a1, a2) \<notin> collides_in_pch \<Longrightarrow> pch_lookup p a2 = pch_lookup (pch_read_impact a1 p) a2"
  (* if a2 can be impacted by a read from a1,
     we require that this impact depends only on the prior state of the fch
     and the prior cachedness of the rest of their collision set in the pch *)
  assumes pch_collision_read: "\<And>a1 a2 pchs pcht. (a1, a2) \<in> collides_in_pch \<Longrightarrow>
    \<forall>a3. (a2, a3) \<in> collides_in_pch \<longrightarrow> pch_lookup pchs a3 = pch_lookup pcht a3 \<Longrightarrow>
    \<comment> \<open>This might be stronger than is met by hardware that just promises
        a 'random' replacement algorithm. Essentially we are requiring that
        any such 'randomness' cannot be influenced by the prior cachedness of
        addresses outside the collision set in question. \<close>
    pchs' = pch_read_impact a1 pchs \<Longrightarrow>
    pcht' = pch_read_impact a1 pcht \<Longrightarrow>
    pch_lookup pchs' a2 = pch_lookup pcht' a2"

  fixes fch_write_impact :: "'fch fch_impact"
  fixes pch_write_impact :: "'pch pch_impact"
  assumes pch_partitioned_write:
    "(a1, a2) \<notin> collides_in_pch \<Longrightarrow> pch_lookup p a2 = pch_lookup (pch_write_impact a1 p) a2"

  assumes pch_collision_write: "\<And>a1 a2 pchs pcht. (a1, a2) \<in> collides_in_pch \<Longrightarrow>
    \<forall>a3. (a2, a3) \<in> collides_in_pch \<longrightarrow> pch_lookup pchs a3 = pch_lookup pcht a3 \<Longrightarrow>
    \<comment> \<open>The same strong requirement placing limits on the 'randomness'
        of the cache replacement algorithm as for @{term pch_collision_read}\<close>
    pchs' = pch_write_impact a1 pchs \<Longrightarrow>
    pcht' = pch_write_impact a1 pcht \<Longrightarrow>
    pch_lookup pchs' a2 = pch_lookup pcht' a2"

  fixes read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  fixes write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"

  fixes do_read :: "vaddr \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'regs"
  fixes do_write :: "vaddr \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'other_state"

  fixes store_time :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"

  fixes padding_regs_impact :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"

  fixes empty_fch :: "'fch"
  fixes fch_flush_cycles :: "'fch \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

  fixes do_pch_flush :: "'pch \<Rightarrow> paddr set \<Rightarrow> 'pch"
  fixes pch_flush_cycles :: "'pch \<Rightarrow> paddr set \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

  assumes pch_partitioned_flush:
   "(\<forall>a'\<in>as. (a, a') \<notin> collides_in_pch) \<Longrightarrow> pch_lookup (do_pch_flush p as) a = pch_lookup p a"
  assumes pch_collision_flush:
    "\<exists>a1\<in>as. (a, a1) \<in> collides_in_pch \<Longrightarrow>
    \<forall>a1. (\<exists>a2\<in>as. (a1, a2) \<in> collides_in_pch) \<longrightarrow> pch_lookup pchs a1 = pch_lookup pcht a1 \<Longrightarrow>
    pch_lookup (do_pch_flush pchs as) a = pch_lookup (do_pch_flush pcht as) a"
  assumes pch_flush_cycles_localised:
    "\<forall>a1. (\<exists>a2\<in>as. (a1, a2) \<in> collides_in_pch) \<longrightarrow> pch_lookup pchs a1 = pch_lookup pcht a1 \<Longrightarrow>
    pch_flush_cycles pchs as = pch_flush_cycles pcht as"

  fixes addr_domain :: "paddr \<Rightarrow> 'userdomain domain" \<comment> \<open>for each address, this is the security domain\<close>
  fixes addr_colour :: "paddr \<Rightarrow> 'colour" \<comment> \<open>for each address, this is the cache colour\<close>
  fixes colour_userdomain :: "'colour \<Rightarrow> 'userdomain"
  assumes no_cross_colour_collisions:
    "(a1, a2) \<in> collides_in_pch \<Longrightarrow> addr_colour a1 = addr_colour a2"
  assumes addr_domain_valid: "addr_domain a = Sched
                            \<or> addr_domain a = User (colour_userdomain (addr_colour a))"
\<comment> \<open>do we assert this here
  or just put it in the type so it has to be asserted before instantiation? or assert it differently
  later?\<close>


  fixes current_domain :: "'other_state \<Rightarrow> 'userdomain domain"
  fixes external_uwr :: "'userdomain domain \<Rightarrow> ('other_state \<times> 'other_state) set"
  assumes external_uwr_equiv_rel:
    "equiv UNIV (external_uwr d)"
  (* The parent locale requires current_domain to be equated by Sched uwr, which confidentiality_u
     then treats as specifying public information; assuming that it is instead equated by every
     domain's uwr arguably simplifies things without changing the strength of the property.
       Without this assumption, I expect we'll need to add the Sched uwr explicitly to the
     pre-equivalence of many lemmas; it may also be a bit harder to prove that our uwr is an
     equivalence relation without it. It may be reasonable to keep this if it holds (or can
     reasonably be made to hold) for the seL4 infoflow theory's unwinding relation. -robs. *)
  assumes external_uwr_same_domain:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain s1 = current_domain s2"
\<comment> \<open>we will probably needs lots more info about this external uwr\<close>

  (* This is an abstraction for the page table. -robs *)
  fixes v_to_p :: "'other_state \<Rightarrow> vaddr \<Rightarrow> paddr"
  assumes page_table_not_in_mem:
    "\<And>a s r. v_to_p (do_write a s r) = v_to_p s"
  assumes external_uwr_current_page_table:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain s1 = d \<Longrightarrow> v_to_p s1 = v_to_p s2"

  assumes do_write_maintains_external_uwr_out:
    "\<And>s a r. addr_domain (v_to_p s a) \<noteq> d \<and> addr_domain (v_to_p s a) \<noteq> Sched \<Longrightarrow>
     (s, do_write a s r) \<in> external_uwr d"

  (*NOTE: we can only invoke this if we have already equalised the "regs" fields *)
  assumes do_write_maintains_external_uwr_in:
    "\<And>s t a r. addr_domain (v_to_p s a) = d \<or> addr_domain (v_to_p s a) = Sched \<Longrightarrow>
     (s, t) \<in> external_uwr d \<Longrightarrow>
     (do_write a s r, do_write a t r) \<in> external_uwr d"

  assumes do_write_outside_kernelshared_same_domain:
    "\<And>s a r. addr_domain (v_to_p s a) \<noteq> Sched \<Longrightarrow>
     current_domain (do_write a s r) = current_domain s"

  (* do_read depends only on things bound in its external uwr *)
  assumes do_read_from_external_uwr_domain:
    "\<And>s t a r. (s, t) \<in> external_uwr d \<Longrightarrow>
     addr_domain (v_to_p s a) = d \<Longrightarrow>
     v_to_p s a = v_to_p t a \<Longrightarrow>
     do_read a s r = do_read a t r"

  (* do_read of kernel_shared depends only on things bound in any external uwr *)
  (* Note: This is a simplifying assumption that might need to be temporary,
     in effect, pulling the Sched uwr into everybody else's uwr.
     Compare to external_uwr_same_domain, and note for the seL4 instantiation we'll expect
     current_domain just to be some designated part of kernel shared memory too. -robs. *)
  assumes do_read_from_external_uwr_sched:
    "\<And>s t a r. (s, t) \<in> external_uwr d \<Longrightarrow>
     addr_domain (v_to_p s a) = Sched \<Longrightarrow>
     v_to_p s a = v_to_p t a \<Longrightarrow>
     do_read a s r = do_read a t r"

  fixes touched_addrs :: "'other_state \<Rightarrow> vaddr set"
  assumes external_uwr_same_touched_addrs:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain s1 = d\<Longrightarrow> touched_addrs s1 = touched_addrs s2"
  assumes touched_addrs_not_in_mem:
    "\<And>a s r. touched_addrs (do_write a s r) = touched_addrs s"
  fixes do_add_to_TA :: "'other_state \<Rightarrow> vaddr set \<Rightarrow> 'other_state"
  assumes do_add_to_TA_correct:
    "\<And>s vas. touched_addrs (do_add_to_TA s vas) = touched_addrs s \<union> vas"
    "\<And>s vas. current_domain (do_add_to_TA s vas) = current_domain s"
    "\<And>s vas. v_to_p (do_add_to_TA s vas) = v_to_p s"
  assumes do_add_to_TA_maintains_external_uwr_in:
    "\<And>s t d vas.
       (s, t) \<in> external_uwr d \<Longrightarrow>
       current_domain s = d \<Longrightarrow>
       (do_add_to_TA s vas, do_add_to_TA t vas) \<in> external_uwr d"
  assumes do_add_to_TA_maintains_external_uwr_out:
    "\<And>s vas.
       current_domain s \<noteq> d \<Longrightarrow>
       (s, do_add_to_TA s vas) \<in> external_uwr d"
  fixes do_empty_TA :: "'other_state \<Rightarrow> 'other_state"
  assumes do_empty_TA_correct:
    "\<And>s. touched_addrs (do_empty_TA s) = {}"
    "\<And>s. current_domain (do_empty_TA s) = current_domain s"
    "\<And>s. v_to_p (do_empty_TA s) = v_to_p s"
  assumes do_empty_TA_maintains_external_uwr_in:
    "\<And>s t d.
       (s, t) \<in> external_uwr d \<Longrightarrow>
       current_domain s = d \<Longrightarrow>
       (do_empty_TA s, do_empty_TA t) \<in> external_uwr d"
  assumes do_empty_TA_maintains_external_uwr_out:
    "\<And>s.
       current_domain s \<noteq> d \<Longrightarrow>
       (s, do_empty_TA s) \<in> external_uwr d"

  (* We expect this to be true for, say, seL4's KSched \<rightarrow> KExit step. -robs. *)
  fixes can_domain_switch :: "'other_state \<Rightarrow> bool"
  assumes can_domain_switch_public:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> can_domain_switch s1 = can_domain_switch s2"
begin

corollary colours_not_shared:
  "colour_userdomain c1 \<noteq> colour_userdomain c2 \<Longrightarrow> c1 \<noteq> c2"
  by blast

definition all_addrs_of :: "'userdomain domain \<Rightarrow> paddr set" where
  "all_addrs_of d = {a. addr_domain a = d}"

abbreviation current_domain' :: "('fch,'pch,'regs,'other_state)state \<Rightarrow> 'userdomain domain"
  where
  "current_domain' s \<equiv> current_domain (other_state s)"

abbreviation v_to_p' :: "('fch,'pch,'regs,'other_state)state \<Rightarrow> vaddr \<Rightarrow> paddr"
  where
  "v_to_p' s \<equiv> v_to_p (other_state s)"

abbreviation collision_set :: "paddr \<Rightarrow> paddr set" where
  "collision_set a \<equiv> {b. (a, b) \<in> collides_in_pch}"

lemma collision_set_contains_itself: "a \<in> collision_set a"
  using collides_with_equiv
  by (clarsimp simp:equiv_def refl_on_def)

lemma external_uwr_refl [simp]:
  "(s, s) \<in> external_uwr d"
  using external_uwr_equiv_rel
  by (clarsimp simp: equiv_def refl_on_def)

lemma collision_sym [simp]:
  "(a, b) \<in> collides_in_pch \<Longrightarrow>
  (b, a) \<in> collides_in_pch"
  by (meson collides_with_equiv equiv_def symE)

\<comment> \<open> the addresses in kernel shared memory (which for now is everything in the sched domain)\<close>
definition kernel_shared_precise :: "paddr set" where
  "kernel_shared_precise \<equiv> {a. addr_domain a = Sched}"

\<comment> \<open> the kernel shared memory, including cache colliding addresses \<close>
definition kernel_shared_expanded :: "paddr set" where
  "kernel_shared_expanded \<equiv> {a. \<exists> z \<in> kernel_shared_precise. a \<in> collision_set z}"

\<comment> \<open> a full collision set contains all of its own collisions \<close>
definition full_collision_set :: "paddr set \<Rightarrow> bool" where
  "full_collision_set S \<equiv> \<forall>a1\<in>S. \<forall>a2. (a1, a2) \<in> collides_in_pch \<longrightarrow> a2 \<in> S"

lemma collision_set_full_collision_set:
  "full_collision_set (collision_set a)"
  apply (clarsimp simp: full_collision_set_def)
  apply (meson collides_with_equiv equiv_def trans_def)
  done

lemma kernel_shared_expanded_full_collision_set:
  "full_collision_set kernel_shared_expanded"
  apply (clarsimp simp: kernel_shared_expanded_def full_collision_set_def)
  apply (meson collides_with_equiv equiv_def trans_def)
  done

lemma collision_in_full_collision_set:
  "full_collision_set S \<Longrightarrow>
  (a1, a2) \<in> collides_in_pch \<Longrightarrow>
  a1 \<notin> S \<Longrightarrow>
  a2 \<notin> S"
  apply (clarsimp simp: full_collision_set_def)
  done

abbreviation touched_addrs' ::
  "('fch,'pch,'regs,'other_state)state \<Rightarrow> vaddr set"
  where
  "touched_addrs' s \<equiv> touched_addrs (other_state s)"

definition paddrs_of ::
  "'other_state \<Rightarrow> vaddr set \<Rightarrow> paddr set"
  where
  "paddrs_of s vas \<equiv> {a. \<exists>v. a = v_to_p s v \<and> v \<in> vas}"

definition touched_paddrs ::
  "'other_state \<Rightarrow> paddr set"
  where
  "touched_paddrs s \<equiv> paddrs_of s (touched_addrs s)"

abbreviation touched_paddrs' ::
  "('fch,'pch,'regs,'other_state)state \<Rightarrow> paddr set"
  where
  "touched_paddrs' s \<equiv> touched_paddrs (other_state s)"

(*FIXME: Move these? These seem more of an IF framework thing. -Scott B *)
\<comment> \<open> the invariant that touched_addresses is always sensible for its current domain \<close>
definition touched_addrs_inv :: "'other_state \<Rightarrow> bool" where
  "touched_addrs_inv s \<equiv>
     touched_paddrs s \<subseteq> all_addrs_of (current_domain s) \<union> kernel_shared_precise"

abbreviation touched_addrs_inv' :: "('fch,'pch,'regs,'other_state)state \<Rightarrow> bool" where
  "touched_addrs_inv' s \<equiv> touched_addrs_inv (other_state s)"

definition page_table_inv :: "'other_state \<Rightarrow> bool" where
  "page_table_inv s \<equiv>
     \<forall> a. v_to_p s a \<in> all_addrs_of (current_domain s) \<union> kernel_shared_precise"

abbreviation page_table_inv' :: "('fch,'pch,'regs,'other_state)state \<Rightarrow> bool" where
  "page_table_inv' s \<equiv> page_table_inv (other_state s)"

definition pch_same_for_domain ::
  "'userdomain domain \<Rightarrow> 'pch \<Rightarrow> 'pch \<Rightarrow> bool"
  where
 "pch_same_for_domain d p1 p2 \<equiv> \<forall> a. addr_domain a = d \<longrightarrow> pch_lookup p1 a = pch_lookup p2 a"

definition pch_same_for_domain_and_shared ::
  "'userdomain domain \<Rightarrow> 'pch \<Rightarrow> 'pch \<Rightarrow> bool"
  where
 "pch_same_for_domain_and_shared d p1 p2 \<equiv>
    \<forall> a. addr_domain a = d \<or> a \<in> kernel_shared_expanded \<longrightarrow> pch_lookup p1 a = pch_lookup p2 a"

definition pch_same_for_domain_except_shared ::
  "'userdomain domain \<Rightarrow> 'pch \<Rightarrow> 'pch \<Rightarrow> bool"
  where
 "pch_same_for_domain_except_shared d p1 p2 \<equiv>
    \<forall> a. addr_domain a = d \<and> a \<notin> kernel_shared_expanded \<longrightarrow> pch_lookup p1 a = pch_lookup p2 a"

definition uwr_running ::
  "'userdomain domain \<Rightarrow> ('fch,'pch,'regs,'other_state)state rel"
  where
  "uwr_running d \<equiv> {(s1, s2). fch s1 = fch s2
                            \<and> pch_same_for_domain_and_shared d (pch s1) (pch s2)
                            \<and> tm s1 = tm s2
                            \<and> regs s1 = regs s2
                            \<and> (other_state s1, other_state s2) \<in> external_uwr d }"
\<comment> \<open>how do we know we have the same program?\<close>


definition uwr_notrunning ::
  "'userdomain domain \<Rightarrow> ('fch,'pch,'regs,'other_state)state rel"
  where
  "uwr_notrunning d \<equiv> {(s1, s2). pch_same_for_domain_except_shared d (pch s1) (pch s2)
                               \<and> (other_state s1, other_state s2) \<in> external_uwr d }"
\<comment> \<open>external uwr needs to be held in the right conditions as an axiom\<close>

definition uwr ::
  "'userdomain domain \<Rightarrow> ('fch,'pch,'regs,'other_state)state rel"
  where
  "uwr d \<equiv> {(s1, s2). if (current_domain' s1 = d)
                      then (s1, s2) \<in> uwr_running d
                      else (s1, s2) \<in> uwr_notrunning d }"

lemma uwr_to_external:
  "(s, t) \<in> uwr d \<Longrightarrow> (other_state s, other_state t) \<in> external_uwr d"
  by (clarsimp simp:uwr_def uwr_running_def uwr_notrunning_def split:if_splits)

lemma uwr_same_domain:
  "(s, t) \<in> uwr d \<Longrightarrow> current_domain' s = current_domain' t"
  by (force dest:uwr_to_external external_uwr_same_domain)

lemma uwr_same_touched_addrs:
  "(s, t) \<in> uwr d \<Longrightarrow> current_domain' s = d \<Longrightarrow> touched_addrs' s = touched_addrs' t"
  by (force dest:uwr_to_external external_uwr_same_touched_addrs)

lemma extended_uwr_equiv_rel:
  "equiv UNIV (uwr u)"
  using external_uwr_equiv_rel
  apply(erule_tac x=u in meta_allE)
  apply(clarsimp simp:equiv_def)
  apply(rule conjI)
   apply(clarsimp simp:uwr_def refl_on_def uwr_running_def uwr_notrunning_def)
   apply(force simp:pch_same_for_domain_and_shared_def pch_same_for_domain_except_shared_def)
  apply(rule conjI)
   apply(clarsimp simp:sym_def)
   apply(frule uwr_same_domain)
   apply(erule_tac x="other_state x" in allE)
   apply(erule_tac x="other_state y" in allE)
   apply(clarsimp simp:uwr_def split:if_splits)
    apply(force simp:uwr_running_def pch_same_for_domain_and_shared_def)
   apply(force simp:uwr_notrunning_def pch_same_for_domain_except_shared_def)
  apply(clarsimp simp:trans_def)
  apply(frule_tac s=x in uwr_same_domain)
  apply(frule_tac s=y in uwr_same_domain)
  apply(erule_tac x="other_state x" in allE)
  apply(erule_tac x="other_state y" in allE)
  apply(erule impE)
   apply(force simp:uwr_to_external)
  apply(erule_tac x="other_state z" in allE)
  apply(erule impE)
   apply(force simp:uwr_to_external)
  apply(clarsimp simp:uwr_def split:if_splits)
   apply(force simp:uwr_running_def pch_same_for_domain_and_shared_def)
  apply(force simp:uwr_notrunning_def pch_same_for_domain_except_shared_def)
  done

lemma uwr_refl [simp]:
  "(s, s) \<in> uwr d"
  using extended_uwr_equiv_rel
  by (clarsimp simp: equiv_def refl_on_def)

lemma uwr_trans:
  "(a, b) \<in> uwr d \<Longrightarrow>
  (b, c) \<in> uwr d \<Longrightarrow>
  (a, c) \<in> uwr d"
  using extended_uwr_equiv_rel
  apply (clarsimp simp: equiv_def)
  by (meson trans_def)

lemma uwr_sym:
  "((a, b) \<in> uwr d) = ((b, a) \<in> uwr d)"
  using extended_uwr_equiv_rel
  apply (clarsimp simp: equiv_def sym_def)
  apply blast
  done

(* notes about confidentiality properties with this model:
   
  for some step (let's say the user step for example), for a step of the NOT CURRENTLY RUNNING
  domain d:
  - we have two programs derived from touched_addresses - may not be the same touched_addresses (? ? ?)
    - we may not have concrete touched_addresses-es - we may overapprox this to the whole currently running domain
  - these touched_addresses does NOT contain any addresses from d
  - initial states s and t hold uwr_notrunning
  - we execute both programs
  - new state s' and t' hold uwr_notrunning
  - this will rely on infoflow properties of external_uwr

  ...and for a step of the CURRENTLY RUNNING domain d:
  - we have two programs derived from the same touched_addresses
    - these have to be the same program (so we need to know that the choice depends on stuff in
      other_state in the external uwr)
  - that touched_addresses ONLY contains addresses in d
  - initial states s and t hold uwr_running
  - we execute the program on both states
  - new states s' and t' hold uwr_running
  - this will rely on infoflow properties of external_uwr
  
  


*)






(* now we make some basic isntructions, which contain addresses etc *)
datatype 'r instr = IRead vaddr            \<comment> \<open>read from some address into regs\<close>
                  | IWrite vaddr           \<comment> \<open>write to some address from regs\<close>
                  | IRegs "'r \<Rightarrow> 'r"       \<comment> \<open>modify the regs somehow\<close>
                  | IFlushL1               \<comment> \<open>flush the entire L1 cache(s)\<close>
                  | IFlushL2 "paddr set"   \<comment> \<open>flush some part L2 cache(s)\<close>
                  | IReadTime              \<comment> \<open>read the time into some regs\<close>
                  | IPadToTime time        \<comment> \<open>pad the time up to some point\<close>
                  | IAddToTA "vaddr set"   \<comment> \<open>add addresses to the touched_addrs set\<close>
                  | IEmptyTA               \<comment> \<open>empty the touched_addrs set\<close>
(* FIXME: I expect we'll want page table manipulation primitives eventually. -robs. *)

primrec
  instr_step :: "'regs instr \<Rightarrow>
    ('fch,'pch,'regs,'other_state)state \<Rightarrow>
    ('fch,'pch,'regs,'other_state)state" where
 "instr_step (IRead a) s =
      s\<lparr>fch := fch_read_impact a (fch s),
        pch := pch_read_impact (v_to_p' s a) (pch s),
        tm  := tm s + read_cycles (fch_lookup (fch s) a) (pch_lookup (pch s) (v_to_p' s a)),
        regs := do_read a (other_state s) (regs s)\<rparr>"
  | "instr_step (IWrite a) s =
      s\<lparr>fch := fch_write_impact a (fch s),
        pch := pch_write_impact (v_to_p' s a) (pch s),
        tm  := tm s + write_cycles (fch_lookup (fch s) a) (pch_lookup (pch s) (v_to_p' s a)),
        other_state := do_write a (other_state s) (regs s)\<rparr>"
  | "instr_step (IRegs m) s =
      s\<lparr>regs := m (regs s),
        tm := tm s + 1 \<rparr>" \<comment> \<open>we increment by the smallest possible amount - different instruction
                            lengths can be encoded with strings of consecutive IRegs intructions.\<close>
  | "instr_step IReadTime s =
      s\<lparr>regs := store_time (tm s) (regs s),
        tm := tm s + 1\<rparr>"
  | "instr_step (IPadToTime t) s =     \<comment> \<open>TODO: is it possible that this changes anything other than regs? what about going backwards?\<close>
      s\<lparr>regs := padding_regs_impact t (regs s),
        tm := t\<rparr>"
  | "instr_step IFlushL1 s =
      s\<lparr>fch := empty_fch,
        tm := tm s + fch_flush_cycles (fch s)\<rparr>"
  | "instr_step (IFlushL2 as) s =
      s\<lparr>pch := do_pch_flush (pch s) as,
        tm := tm s + pch_flush_cycles (pch s) as\<rparr>"
  | "instr_step (IAddToTA vas) s =
      s\<lparr>other_state := do_add_to_TA (other_state s) vas\<rparr>"
  | "instr_step IEmptyTA s =
      s\<lparr>other_state := do_empty_TA (other_state s)\<rparr>"

type_synonym 'r program = "'r instr list"

primrec instr_multistep :: "'regs program \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state" where
  "instr_multistep [] s = s"
| "instr_multistep (i#is) s = instr_multistep is (instr_step i s)"

definition
  instrs_obeying_ta :: "'other_state \<Rightarrow> 'regs instr set" where
 "instrs_obeying_ta s \<equiv> {i. case i of
                            IRead a  \<Rightarrow> a \<in> touched_addrs s
                          | IWrite a \<Rightarrow> a \<in> touched_addrs s
                          | IFlushL2 as \<Rightarrow> as \<subseteq> touched_paddrs s
                          | _        \<Rightarrow> True }"

(* "safe" instructions. for now this just means they don't write to kernel shared memory *)
definition
  instrs_safe :: "'other_state \<Rightarrow> 'regs instr set" where
 "instrs_safe s \<equiv> {i. case i of
                    IWrite a \<Rightarrow> v_to_p s a \<notin> kernel_shared_precise
                  | IAddToTA vas \<Rightarrow> paddrs_of s vas \<subseteq> all_addrs_of (current_domain s) \<union> kernel_shared_precise
                  | IEmptyTA \<Rightarrow> False
                  | _ \<Rightarrow> True}"

(* these are the programs that could have created this ta *)
definition
  programs_obeying_ta :: "'other_state \<Rightarrow> 'regs program set" where
 "programs_obeying_ta s \<equiv> {p. list_all (\<lambda>i. i \<in> instrs_obeying_ta s) p}"


definition
  programs_safe :: "'other_state \<Rightarrow> 'regs program set" where
 "programs_safe s \<equiv> {p. list_all (\<lambda>i. i \<in> instrs_safe s) p}"


lemma hd_instr_obeying_ta [dest]:
  "a # p \<in> programs_obeying_ta ta \<Longrightarrow> a \<in> instrs_obeying_ta ta"
  by (force simp:programs_obeying_ta_def)



(* trying to replace this with instrs_safe

(* this program never changes the current domain *)
primrec program_no_domainswitch :: "'regs program \<Rightarrow> bool" where
  "program_no_domainswitch [] = True" |
  "program_no_domainswitch (i#is) =
     ((\<forall> s. current_domain' s = current_domain' (instr_step i s)) \<and> program_no_domainswitch is)"



definition
  programs_no_domainswitch :: "'regs program set" where
  "programs_no_domainswitch \<equiv> {p. program_no_domainswitch p}"

*)

lemma safe_no_domainswitch:
  "i \<in> instrs_safe (other_state s) \<Longrightarrow>
  current_domain' s = current_domain' (instr_step i s)"
  apply (cases i; clarsimp simp: instrs_safe_def)
   apply (force simp: kernel_shared_precise_def do_write_outside_kernelshared_same_domain)
  using do_add_to_TA_correct apply force
  done

lemma safe_no_TA_removals:
  "i \<in> instrs_safe (other_state s) \<Longrightarrow>
  touched_addrs' s \<subseteq> touched_addrs' (instr_step i s)"
  apply (cases i; clarsimp simp: instrs_safe_def)
   using touched_addrs_not_in_mem apply force
  using do_add_to_TA_correct apply force
  done

lemma safe_remains_safe:
  "i \<in> instrs_safe (other_state s) \<Longrightarrow>
   a \<in> instrs_safe (other_state s) \<Longrightarrow>
   i \<in> instrs_safe (other_state (instr_step a s))"
  apply (cases i; cases a; clarsimp simp: instrs_safe_def all_addrs_of_def paddrs_of_def)
     using page_table_not_in_mem apply force
    using do_add_to_TA_correct apply force
   using do_write_outside_kernelshared_same_domain kernel_shared_precise_def page_table_not_in_mem
   apply auto[1]
  using do_add_to_TA_correct(2) do_add_to_TA_correct(3) by auto

lemma no_domainswitch_inv:
  "p \<in> programs_safe (other_state s) \<Longrightarrow>
     current_domain' s = current_domain' (instr_multistep p s)
   \<and> touched_addrs' s \<subseteq> touched_addrs' (instr_multistep p s)"
  apply(induct p arbitrary:s)
   apply force
  unfolding programs_safe_def list_all_def
  apply clarsimp
  apply(frule safe_no_domainswitch)
  apply(frule safe_no_TA_removals)
  by (simp add:safe_remains_safe subset_trans)

definition is_secure_nondomainswitch ::
  "'regs program \<Rightarrow> ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "is_secure_nondomainswitch p s \<equiv>
      \<comment> \<open>Oblige the original system not to reach any system-step that would require either
          (1) straying out of touched_addresses or (2) switching domains to implement.\<close>
      p \<in> programs_obeying_ta (other_state s) \<inter> programs_safe (other_state s)"

definition kludge_uwr_same_programs ::
  "'regs program \<Rightarrow> ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "kludge_uwr_same_programs p s =
     (\<forall>t q. (s, t) \<in> uwr (current_domain' s) \<and> is_secure_nondomainswitch q t \<longrightarrow> p = q)"

definition has_secure_nondomainswitch :: "('fch,'pch,'regs,'other_state)state \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "has_secure_nondomainswitch s s' \<equiv>
     \<comment> \<open>The original definition.\<close>
     \<exists>p. s' = instr_multistep p s \<and> is_secure_nondomainswitch p s \<and>
       \<comment> \<open>Assume the currently running domain's uwr ensures the program stays deterministic.
             Actually, as discussed with Toby, we should add machinery to capture that the program
           might become nondeterministic after the current domain reads from outside
           `touched_addresses + kernel_shared_memory`, assuming pessimistically it might branch
           on some secret data it read -- thus, forcing ourselves to prove that won't happen before
           or during a non-domainswitch step. We should then remove the line below.\<close>
       kludge_uwr_same_programs p s"


lemma collides_with_set_or_doesnt:
  "\<lbrakk>\<forall>a'\<in>as. (a, a') \<notin> collides_in_pch \<Longrightarrow> P;
    \<exists>a'\<in>as. (a, a') \<in> collides_in_pch \<Longrightarrow> P \<rbrakk> \<Longrightarrow>
  P"
  by blast


lemma diff_domain_no_collision:
  "\<lbrakk>a \<notin> kernel_shared_expanded;
  addr_domain a' \<noteq> addr_domain a;
  (a, a') \<in> collides_in_pch\<rbrakk> \<Longrightarrow>
  False"
  apply (frule(1) collision_in_full_collision_set [OF kernel_shared_expanded_full_collision_set])
  apply (metis (mono_tags, lifting) addr_domain_valid collision_set_contains_itself
               kernel_shared_expanded_def kernel_shared_precise_def mem_Collect_eq
               no_cross_colour_collisions)
  done



lemma in_inter_empty:
  "\<lbrakk>x \<in> S1;              
  S1 \<inter> S2 = {} \<rbrakk> \<Longrightarrow>
  x \<notin> S2"
  by blast

lemma in_sub_inter_empty:
  "\<lbrakk>x \<in> S1;
  S1 \<subseteq> S2;
  S2 \<inter> S3 = {} \<rbrakk> \<Longrightarrow>
  x \<notin> S3"
  by blast

lemma in_sub_union:
  "\<lbrakk>x \<in> S1;
  S1 \<subseteq> S2;
  S2 \<subseteq> S3 \<union> S4\<rbrakk> \<Longrightarrow>
  x \<in> S3 \<or> x \<in> S4"
  by blast

(* this helps avoid/reverse some unhelpful clarsimp behaviour *)
lemma and_or_specific:
  "(\<And>x. (P x \<or> Q x \<Longrightarrow> R x)) \<Longrightarrow>
   \<forall>a. (P a \<longrightarrow> R a) \<and> (Q a \<longrightarrow> R a)"
  apply blast
  done

lemma d_running_step:
  assumes
    "i \<in> instrs_obeying_ta (other_state s)"
    "i \<in> instrs_safe (other_state s)"
    "touched_addrs_inv (other_state s)"
    "page_table_inv (other_state s)"
    "(s, t) \<in> uwr d"
    "current_domain' s = d"
    "s' = instr_step i s"
    "t' = instr_step i t"
    "current_domain' s' = d"
  shows
    "(s', t') \<in> uwr d"
  proof (cases i)
    case (IRead a)
    thus ?thesis using assms
      apply(clarsimp simp:uwr_def uwr_running_def)
      apply(clarsimp simp:instrs_obeying_ta_def touched_addrs_inv_def)
      apply(frule external_uwr_current_page_table[symmetric])
       apply force
      apply(clarsimp simp:page_table_inv_def)
      (* First obtain that `a` belongs to the current domain or shared memory (i.e. Sched) *)
      apply(clarsimp simp:all_addrs_of_def)
      apply(erule_tac x=a in allE)
      apply(erule_tac c="v_to_p' s a" in subsetCE)
       apply(force simp:touched_paddrs_def paddrs_of_def)
      apply clarsimp
      apply(rule conjI)
       (* equivalence on part of pch *)
       apply(clarsimp simp:pch_same_for_domain_and_shared_def kernel_shared_expanded_def)
       apply(rename_tac a')
       apply(case_tac "a' \<in> collision_set (v_to_p' s a)")
        (* for colliding addresses *)
        apply clarsimp
        apply(rule conjI)
         apply clarsimp
         apply(rule pch_collision_read[where pchs="pch s" and pcht="pch t" and ?a1.0="v_to_p' s a"])
            apply force
           apply(metis (mono_tags, lifting) addr_domain_valid collision_set_contains_itself kernel_shared_precise_def mem_Collect_eq no_cross_colour_collisions)
          apply force
         apply force
        apply clarsimp
        apply(rule pch_collision_read[where pchs="pch s" and pcht="pch t" and ?a1.0="v_to_p' s a"])
           apply force
          apply(metis collision_in_full_collision_set collision_set_contains_itself collision_set_full_collision_set mem_Collect_eq)
         apply force
        apply force
       apply clarsimp
       (* for non-colliding addresses *)
       using pch_partitioned_read
       apply metis
      apply(rule conjI)
       (* equivalence of read cycles *)
       apply(erule disjE)
        apply(force simp:pch_same_for_domain_and_shared_def)
       apply(clarsimp simp:pch_same_for_domain_and_shared_def kernel_shared_expanded_def)
       using collision_set_contains_itself
       apply fastforce
      apply (erule disjE)
       (* equivalence of what is read from external state, from external uwr *)
       apply (erule(1) do_read_from_external_uwr_domain)
       apply force
      (* equivalence of what is read from kernel shared memory *)
      apply (erule do_read_from_external_uwr_sched)
       apply (clarsimp simp: kernel_shared_precise_def)
      apply force
      done
  next
    case (IWrite a)
    (* NB: Reasoning is mostly identical to that for IRead -robs. *)
    thus ?thesis using assms
      apply(clarsimp simp:uwr_def uwr_running_def)
      apply(clarsimp simp:instrs_obeying_ta_def touched_addrs_inv_def)
      apply(frule external_uwr_current_page_table[symmetric])
       apply force
      apply(clarsimp simp:page_table_inv_def)
      (* First obtain that `a` belongs to the current domain or shared memory (i.e. Sched) *)
      apply(clarsimp simp:all_addrs_of_def)
      apply(erule_tac x=a in allE)
      apply(erule_tac c="v_to_p' s a" in subsetCE)
       apply(force simp:touched_paddrs_def paddrs_of_def)
      apply clarsimp
      apply(rule conjI)
       (* equivalence on part of pch *)
       apply(clarsimp simp:pch_same_for_domain_and_shared_def kernel_shared_expanded_def)
       apply(rename_tac a')
       apply(case_tac "a' \<in> collision_set (v_to_p' s a)")
        (* for colliding addresses *)
        apply clarsimp
        apply(rule conjI)
         apply clarsimp
         apply(rule pch_collision_write[where pchs="pch s" and pcht="pch t" and ?a1.0="v_to_p' s a"])
            apply force
           apply(metis (mono_tags, lifting) addr_domain_valid collision_set_contains_itself kernel_shared_precise_def mem_Collect_eq no_cross_colour_collisions)
          apply force
         apply force
        apply clarsimp
        apply(rule pch_collision_write[where pchs="pch s" and pcht="pch t" and ?a1.0="v_to_p' s a"])
           apply force
          apply(metis collision_in_full_collision_set collision_set_contains_itself collision_set_full_collision_set mem_Collect_eq)
         apply force
        apply force
       apply clarsimp
       (* for non-colliding addresses *)
       using pch_partitioned_write
       apply metis
      apply(rule conjI)
       (* equivalence of write cycles *)
       apply(erule disjE)
        apply(force simp:pch_same_for_domain_and_shared_def)
       apply(clarsimp simp:pch_same_for_domain_and_shared_def kernel_shared_expanded_def)
       using collision_set_contains_itself
       apply fastforce
      (* equivalence of the written impact on other_state *)
      using do_write_maintains_external_uwr_in kernel_shared_precise_def
      by blast
  next
    case (IRegs x3)
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  next
    case IFlushL1
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  next
    case (IFlushL2 fa)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_running_def pch_same_for_domain_and_shared_def
                            instrs_obeying_ta_def)
      apply (thin_tac "s' = _", thin_tac "t' = _") (* messy and not needed *)
      apply (subgoal_tac "\<forall>a1. (\<exists>a2\<in>fa. (a1, a2) \<in> collides_in_pch) \<longrightarrow> pch_lookup (pch s) a1 = pch_lookup (pch t) a1")
       defer
        apply clarsimp
        apply (drule_tac x=a1 in spec)
        apply clarsimp
        (* Adapted from an Isar proof found by Sledgehammer -robs. *)
        apply(prop_tac "full_collision_set {p. \<exists>pa. pa \<in> kernel_shared_precise \<and> p \<in> collision_set pa}")
         apply(metis (no_types) kernel_shared_expanded_def kernel_shared_expanded_full_collision_set)
        apply(prop_tac "fa \<subseteq> {v_to_p' s v |v. v \<in> touched_addrs' s}")
         apply(force simp:touched_paddrs_def paddrs_of_def)
        apply(prop_tac "addr_domain a2 \<noteq> current_domain' s")
         apply(metis (no_types) diff_domain_no_collision)
        apply(prop_tac "addr_domain a2 = Sched")
         using all_addrs_of_def kernel_shared_precise_def touched_addrs_inv_def
         apply blast
        apply(prop_tac "addr_domain a1 = Sched")
         apply(metis diff_domain_no_collision)
        using collision_in_full_collision_set kernel_shared_expanded_def kernel_shared_precise_def
        apply blast
      apply (intro conjI)
       (* pch flush affects are partitioned or deterministic on collision *)
       apply (rule and_or_specific)
       apply (rename_tac a)
       apply (rule_tac a=a and as=fa in collides_with_set_or_doesnt)
        (* a has no collision with fa *)
        apply (frule pch_partitioned_flush [where p = "pch s"])
        apply (frule pch_partitioned_flush [where p = "pch t"])
        apply (clarsimp, blast)
       (* a collides with fa *)
       apply (erule(1) pch_collision_flush)
      (* pch flush cycles depend only on equiv state *)
      apply (erule pch_flush_cycles_localised)
      done
  next
    case IReadTime
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  next
    case (IPadToTime x7)
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  next
    case (IAddToTA vas)
    thus ?thesis using assms
      apply(clarsimp simp:uwr_def uwr_running_def)
      using do_add_to_TA_maintains_external_uwr_in
      by blast
  next
    case IEmptyTA
    thus ?thesis using assms
      by (clarsimp simp:uwr_def uwr_running_def instrs_safe_def)
  qed

lemma touched_addrs_inv_preserved:
  "\<lbrakk>touched_addrs_inv' s; page_table_inv' s;
    s' = instr_multistep p (instr_step a s);
    current_domain' (instr_step a s) = current_domain' s;
    a \<in> instrs_safe (other_state s)\<rbrakk>
   \<Longrightarrow> touched_addrs_inv' (instr_step a s)"
  apply(clarsimp simp:instrs_obeying_ta_def
    programs_safe_def instrs_safe_def list_all_def split:instr.splits)
   using page_table_inv_def page_table_not_in_mem touched_addrs_inv_def touched_paddrs_def paddrs_of_def
   apply(force simp add: touched_addrs_not_in_mem)
  using do_add_to_TA_correct(3) page_table_inv_def touched_addrs_inv_def touched_paddrs_def paddrs_of_def
  apply auto[1]
  done

lemma touched_addrs_inv_preserved':
  "\<lbrakk>a # p \<in> programs_obeying_ta (other_state s); a # p \<in> programs_safe (other_state s);
    touched_addrs_inv' s; page_table_inv' s; (s, t) \<in> uwr (current_domain' s);
    s' = instr_multistep p (instr_step a s); t' = instr_multistep p (instr_step a t);
    d = current_domain' s; current_domain' (instr_step a s) = d\<rbrakk>
   \<Longrightarrow> touched_addrs_inv' (instr_step a s)"
  apply(clarsimp simp:programs_obeying_ta_def programs_safe_def)
  using touched_addrs_inv_preserved by blast

lemma page_table_inv_preserved:
  "\<lbrakk>touched_addrs_inv' s; page_table_inv' s;
    s' = instr_multistep p (instr_step a s);
    current_domain' (instr_step a s) = current_domain' s;
    a \<in> instrs_safe (other_state s)\<rbrakk>
   \<Longrightarrow> page_table_inv' (instr_step a s)"
  apply(clarsimp simp:programs_obeying_ta_def instrs_obeying_ta_def
    programs_safe_def instrs_safe_def list_all_def split:instr.splits)
   using page_table_inv_def page_table_not_in_mem touched_addrs_inv_def touched_paddrs_def
   apply force
  using do_add_to_TA_correct(3) page_table_inv_def touched_addrs_inv_def touched_paddrs_def
  apply force
  done

lemma page_table_inv_preserved':
  "\<lbrakk>a # p \<in> programs_obeying_ta (other_state s); a # p \<in> programs_safe (other_state s);
    touched_addrs_inv' s; page_table_inv' s; (s, t) \<in> uwr (current_domain' s);
    s' = instr_multistep p (instr_step a s); t' = instr_multistep p (instr_step a t);
    d = current_domain' s; current_domain' (instr_step a s) = d\<rbrakk>
   \<Longrightarrow> page_table_inv' (instr_step a s)"
  apply(clarsimp simp:programs_obeying_ta_def programs_safe_def)
  using page_table_inv_preserved by blast

(* d running \<rightarrow> d running *)
lemma d_running: "\<lbrakk>
   \<comment> \<open>Note: The \<open>programs_obeying_ta_preserve_uwr\<close> lemma that uses this should extract whatever
     we'll need here from its guards that s and t are reachable. We can't have these reachability
     guards here because it will mess up the induction proof (won't hold for intermediate states).\<close>
   \<comment> \<open>we have two programs derived from the same touched_addresses -
     these have to be the same program (so we need to know that the choice depends on stuff in
     other_state in the external uwr)\<close>
   p \<in> programs_obeying_ta (other_state s);
   p \<in> programs_safe (other_state s);
   \<comment> \<open>that touched_addresses ONLY contains addresses in d\<close>
   touched_addrs_inv (other_state s);
   page_table_inv (other_state s);
   \<comment> \<open>initial states s and t hold uwr_running\<close>
   (s, t) \<in> uwr d;
   current_domain' s = d;
   \<comment> \<open>NB: external_uwr should give us current_domain' t = d\<close>
   \<comment> \<open>we execute the program on both states\<close>
   s' = instr_multistep p s;
   t' = instr_multistep p t
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new states s' and t' hold uwr_running\<close>
   (s', t') \<in> uwr d"
  apply(induct p arbitrary:s t)
   apply force
  apply clarsimp
  apply(erule_tac x="instr_step a s" in meta_allE)
  apply(erule_tac x="instr_step a t" in meta_allE)
  apply clarsimp
  apply(erule meta_impE)
   apply(clarsimp simp:programs_obeying_ta_def instrs_obeying_ta_def list_all_def split:instr.splits)
     apply(force simp add:touched_paddrs_def paddrs_of_def page_table_not_in_mem touched_addrs_not_in_mem)
    unfolding touched_paddrs_def paddrs_of_def
    using do_add_to_TA_correct(1,3)
    apply clarsimp
    apply blast
   apply(force simp:programs_safe_def instrs_safe_def)
  apply(erule meta_impE)
   apply(clarsimp simp: programs_safe_def instrs_safe_def list_all_def split:instr.splits)
    (* Isar proof found by sledgehammer -robs. *)
    subgoal proof -
      fix pa :: "'regs instr list" and sa :: "('fch, 'pch, 'regs, 'other_state) state" and ta :: "('fch, 'pch, 'regs, 'other_state) state" and x2 :: vaddr and x :: "'regs instr"
      assume a1: "\<forall>x\<in>set pa. (\<forall>x2. x = IWrite x2 \<longrightarrow> v_to_p' sa x2 \<notin> kernel_shared_precise) \<and> (\<forall>x8. x = IAddToTA x8 \<longrightarrow> paddrs_of (other_state sa) x8 \<subseteq> all_addrs_of (current_domain' sa) \<union> kernel_shared_precise) \<and> x \<noteq> IEmptyTA"
      assume a2: "x \<in> set pa"
      assume a3: "page_table_inv' sa"
      assume a4: "v_to_p' sa x2 \<notin> kernel_shared_precise"
      obtain vv :: vaddr and VV :: "vaddr set" where
        f5: "((\<exists>v. x = IWrite v \<and> v_to_p (do_write x2 (other_state sa) (regs sa)) v \<in> kernel_shared_precise) \<or> (\<exists>V. x = IAddToTA V \<and> \<not> paddrs_of (do_write x2 (other_state sa) (regs sa)) V \<subseteq> all_addrs_of (current_domain (do_write x2 (other_state sa) (regs sa))) \<union> kernel_shared_precise)) = (x = IWrite vv \<and> v_to_p (do_write x2 (other_state sa) (regs sa)) vv \<in> kernel_shared_precise \<or> x = IAddToTA VV \<and> \<not> paddrs_of (do_write x2 (other_state sa) (regs sa)) VV \<subseteq> all_addrs_of (current_domain (do_write x2 (other_state sa) (regs sa))) \<union> kernel_shared_precise)"
        by moura
      obtain pp :: "paddr set \<Rightarrow> paddr set \<Rightarrow> paddr" where
        "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pp x0 x1 \<in> x1 \<and> pp x0 x1 \<notin> x0)"
        by moura
      then have f6: "\<forall>P Pa. pp Pa P \<in> P \<and> pp Pa P \<notin> Pa \<or> P \<subseteq> Pa"
        by (meson subsetI)
      obtain vva :: "paddr \<Rightarrow> vaddr set \<Rightarrow> 'other_state \<Rightarrow> vaddr" where
        "\<forall>x0 x1 x2a. (\<exists>v3. x0 = v_to_p x2a v3 \<and> v3 \<in> x1) = (x0 = v_to_p x2a (vva x0 x1 x2a) \<and> vva x0 x1 x2a \<in> x1)"
        by moura
      then have f7: "pp (all_addrs_of (current_domain (do_write x2 (other_state sa) (regs sa))) \<union> kernel_shared_precise) (paddrs_of (do_write x2 (other_state sa) (regs sa)) VV) \<in> paddrs_of (do_write x2 (other_state sa) (regs sa)) VV \<and> pp (all_addrs_of (current_domain (do_write x2 (other_state sa) (regs sa))) \<union> kernel_shared_precise) (paddrs_of (do_write x2 (other_state sa) (regs sa)) VV) \<notin> all_addrs_of (current_domain (do_write x2 (other_state sa) (regs sa))) \<union> kernel_shared_precise \<longrightarrow> pp (all_addrs_of (current_domain (do_write x2 (other_state sa) (regs sa))) \<union> kernel_shared_precise) (paddrs_of (do_write x2 (other_state sa) (regs sa)) VV) = v_to_p (do_write x2 (other_state sa) (regs sa)) (vva (pp (all_addrs_of (current_domain (do_write x2 (other_state sa) (regs sa))) \<union> kernel_shared_precise) (paddrs_of (do_write x2 (other_state sa) (regs sa)) VV)) VV (do_write x2 (other_state sa) (regs sa))) \<and> vva (pp (all_addrs_of (current_domain (do_write x2 (other_state sa) (regs sa))) \<union> kernel_shared_precise) (paddrs_of (do_write x2 (other_state sa) (regs sa)) VV)) VV (do_write x2 (other_state sa) (regs sa)) \<in> VV"
        by (simp add: paddrs_of_def)
      have "addr_domain (v_to_p' sa x2) \<noteq> Sched"
        using a4 by (simp add: kernel_shared_precise_def)
      then have "current_domain (do_write x2 (other_state sa) (regs sa)) = current_domain' sa"
        by (meson time_protection.do_write_outside_kernelshared_same_domain time_protection_axioms)
      then show "(\<forall>v. x = IWrite v \<longrightarrow> v_to_p (do_write x2 (other_state sa) (regs sa)) v \<notin> kernel_shared_precise) \<and> (\<forall>V. x = IAddToTA V \<longrightarrow> paddrs_of (do_write x2 (other_state sa) (regs sa)) V \<subseteq> all_addrs_of (current_domain (do_write x2 (other_state sa) (regs sa))) \<union> kernel_shared_precise)"
        using f7 f6 f5 a3 a2 a1 by (metis (no_types) page_table_inv_def page_table_not_in_mem)
    qed
   apply(force simp add: do_add_to_TA_correct(2) do_add_to_TA_correct(3) paddrs_of_def)
  apply (subgoal_tac "current_domain' (instr_step a s) = d")
   apply (erule meta_impE)
    apply(clarsimp simp:programs_obeying_ta_def programs_safe_def)
    using touched_addrs_inv_preserved
    apply blast
   apply (erule meta_impE)
    apply(clarsimp simp:programs_obeying_ta_def programs_safe_def)
    using page_table_inv_preserved
    apply blast
   apply(metis (no_types, lifting) d_running_step hd_instr_obeying_ta list_all_simps(1) mem_Collect_eq time_protection.programs_safe_def time_protection_axioms)
  using safe_no_domainswitch
  apply (metis list_all_simps(1) mem_Collect_eq programs_safe_def)
  done




lemma d_not_running_step:
  assumes
  "i \<in> instrs_obeying_ta (other_state s)"
  "i \<in> instrs_safe (other_state s)"
  "touched_addrs_inv' s"
  "page_table_inv' s"
  "current_domain' s \<noteq> d"
  "s' = instr_step i s"
  shows
  "(s, s') \<in> uwr d"
  proof (cases i)
    case (IRead x1)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def
                            instrs_obeying_ta_def)
      (* show that the instruction hasn't affected our visible part of pch *)
      apply (drule in_inter_empty)
       apply force
      apply (clarsimp simp: all_addrs_of_def)
      apply (rule pch_partitioned_read, clarsimp)
      using diff_domain_no_collision
      by (metis (mono_tags, lifting) Un_iff all_addrs_of_def collision_sym
        kernel_shared_expanded_def mem_Collect_eq page_table_inv_def)
  next
    case (IWrite x2)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def
                            instrs_obeying_ta_def)
      apply (thin_tac "s' = _")
      apply (drule in_inter_empty)
       apply force
      apply (intro conjI)
       apply (clarsimp simp: all_addrs_of_def)
       apply (rule pch_partitioned_write, clarsimp)
       using diff_domain_no_collision
       apply (metis (mono_tags, lifting) Un_iff all_addrs_of_def collision_sym
         kernel_shared_expanded_def mem_Collect_eq page_table_inv_def)
      apply (rule do_write_maintains_external_uwr_out)
      apply (clarsimp simp: all_addrs_of_def)
      apply (clarsimp simp: instrs_safe_def kernel_shared_precise_def)
      by (metis (mono_tags) Un_iff all_addrs_of_def kernel_shared_precise_def mem_Collect_eq
        page_table_inv_def)
  next
    case (IRegs x3)
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
  next
    case IFlushL1
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
  next
    case (IFlushL2 x5)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def
                            instrs_obeying_ta_def)
      apply (rule sym, rule pch_partitioned_flush, clarsimp)
      apply(clarsimp simp:touched_addrs_inv_def all_addrs_of_def)
      (* Adapted from Isar proof found by Sledgehammer -robs. *)
      apply(prop_tac "addr_domain a' = d")
       using diff_domain_no_collision
       apply blast
      apply(prop_tac "a \<in> kernel_shared_precise")
       apply(force simp:kernel_shared_precise_def)
      using collision_set_contains_itself kernel_shared_expanded_def
      apply blast
      done
  next
    case IReadTime
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
  next
    case (IPadToTime x7)
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
  next
    case (IAddToTA vas)
    thus ?thesis using assms
      apply(clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
      using do_add_to_TA_maintains_external_uwr_out
      by blast
  next
    case IEmptyTA
    thus ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def
        instrs_safe_def)
qed



lemma programs_obeying_ta_head_and_rest:
  "h # r \<in> programs_obeying_ta ta \<Longrightarrow>
   h \<in> instrs_obeying_ta ta \<and> r \<in> programs_obeying_ta ta"
  apply (clarsimp simp: programs_obeying_ta_def)
  done

lemma programs_safe_head_and_rest:
  "h # r \<in> programs_safe s \<Longrightarrow>
   h \<in> instrs_safe s \<and> r \<in> programs_safe s"
  apply (clarsimp simp: programs_safe_def)
  done                          

lemma d_not_running_integrity_uwr:
  "\<lbrakk>p \<in> programs_obeying_ta (other_state s);
  p \<in> programs_safe (other_state s);
  current_domain' s \<noteq> d;
  touched_addrs_inv' s;
  page_table_inv' s
  \<rbrakk> \<Longrightarrow>
  (s, instr_multistep p s) \<in> uwr d"
  apply (induct p arbitrary: s; clarsimp)
  apply (drule programs_obeying_ta_head_and_rest, clarsimp)
  apply (drule programs_safe_head_and_rest, clarsimp)
  apply (subgoal_tac "current_domain' (instr_step a s) \<noteq> d")
   defer
   using safe_no_domainswitch
   apply blast
  unfolding programs_obeying_ta_def programs_safe_def
  apply (drule_tac x="instr_step a s" in meta_spec)
  apply(erule meta_impE)
   apply(clarsimp simp:instrs_obeying_ta_def instrs_safe_def list_all_def split:instr.splits)
    using page_table_not_in_mem touched_paddrs_def
    apply(force simp add: touched_addrs_not_in_mem paddrs_of_def)
   (* Isar proof found by Sledgehammer -robs. *)
   subgoal
   proof -
     fix pa :: "'regs instr list" and sa :: "('fch, 'pch, 'regs, 'other_state) state" and x8 :: "vaddr set" and x :: "'regs instr"
     assume a1: "\<forall>x\<in>set pa. (\<forall>x1. x = IRead x1 \<longrightarrow> x1 \<in> touched_addrs' sa) \<and> (\<forall>x2. x = IWrite x2 \<longrightarrow> x2 \<in> touched_addrs' sa) \<and> (\<forall>x5. x = IFlushL2 x5 \<longrightarrow> x5 \<subseteq> touched_paddrs' sa)"
     assume a2: "x \<in> set pa"
     have f3: "((\<forall>v. x = IRead v \<longrightarrow> v \<in> touched_addrs (do_add_to_TA (other_state sa) x8)) \<and> (\<forall>v. x = IWrite v \<longrightarrow> v \<in> touched_addrs (do_add_to_TA (other_state sa) x8)) \<and> (\<forall>P. x = IFlushL2 P \<longrightarrow> P \<subseteq> touched_paddrs (do_add_to_TA (other_state sa) x8))) = ((\<forall>v. x \<noteq> IRead v \<or> v \<in> touched_addrs (do_add_to_TA (other_state sa) x8)) \<and> (\<forall>v. x \<noteq> IWrite v \<or> v \<in> touched_addrs (do_add_to_TA (other_state sa) x8)) \<and> (\<forall>P. x \<noteq> IFlushL2 P \<or> P \<subseteq> touched_paddrs (do_add_to_TA (other_state sa) x8)))"
       by presburger
     obtain vv :: vaddr and vva :: vaddr and PP :: "paddr set" where
       f4: "((\<exists>v. x = IRead v \<and> v \<notin> touched_addrs (do_add_to_TA (other_state sa) x8)) \<or> (\<exists>v. x = IWrite v \<and> v \<notin> touched_addrs (do_add_to_TA (other_state sa) x8)) \<or> (\<exists>P. x = IFlushL2 P \<and> \<not> P \<subseteq> touched_paddrs (do_add_to_TA (other_state sa) x8))) = (x = IRead vva \<and> vva \<notin> touched_addrs (do_add_to_TA (other_state sa) x8) \<or> x = IWrite vv \<and> vv \<notin> touched_addrs (do_add_to_TA (other_state sa) x8) \<or> x = IFlushL2 PP \<and> \<not> PP \<subseteq> touched_paddrs (do_add_to_TA (other_state sa) x8))"
       by moura
     obtain pp :: "paddr set \<Rightarrow> paddr set \<Rightarrow> paddr" where
       f5: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pp x0 x1 \<in> x1 \<and> pp x0 x1 \<notin> x0)"
       by moura
     have "x = IFlushL2 PP \<and> \<not> PP \<subseteq> touched_paddrs (do_add_to_TA (other_state sa) x8) \<longrightarrow> PP \<subseteq> {v_to_p' sa v |v. v \<in> touched_addrs' sa}"
       using a2 a1 by (simp add: touched_paddrs_def paddrs_of_def)
     then have f6: "x = IFlushL2 PP \<and> \<not> PP \<subseteq> touched_paddrs (do_add_to_TA (other_state sa) x8) \<longrightarrow> (\<exists>v. pp (touched_paddrs (do_add_to_TA (other_state sa) x8)) PP = v_to_p' sa v \<and> v \<in> touched_addrs' sa)"
       using f5 by blast
     have "x = IFlushL2 PP \<and> \<not> PP \<subseteq> touched_paddrs (do_add_to_TA (other_state sa) x8) \<longrightarrow> pp (touched_paddrs (do_add_to_TA (other_state sa) x8)) PP \<notin> {v_to_p (do_add_to_TA (other_state sa) x8) v |v. v \<in> touched_addrs (do_add_to_TA (other_state sa) x8)}"
       using f5 by (metis subsetI touched_paddrs_def paddrs_of_def)
     then show "(\<forall>v. x = IRead v \<longrightarrow> v \<in> touched_addrs (do_add_to_TA (other_state sa) x8)) \<and> (\<forall>v. x = IWrite v \<longrightarrow> v \<in> touched_addrs (do_add_to_TA (other_state sa) x8)) \<and> (\<forall>P. x = IFlushL2 P \<longrightarrow> P \<subseteq> touched_paddrs (do_add_to_TA (other_state sa) x8))"
       using f6 f4 f3 a2 a1 do_add_to_TA_correct(1) do_add_to_TA_correct(3) by force
   qed
  apply(erule meta_impE)
   apply(clarsimp simp:instrs_obeying_ta_def instrs_safe_def list_all_def split:instr.splits)
    using page_table_not_in_mem touched_paddrs_def paddrs_of_def touched_addrs_not_in_mem
    apply (force simp add: do_write_outside_kernelshared_same_domain kernel_shared_precise_def)
   using do_add_to_TA_correct(3)
   apply (force simp add: do_add_to_TA_correct(2) paddrs_of_def)
  apply(erule meta_impE)
   apply force
  apply(erule meta_impE)
   using touched_addrs_inv_preserved
   apply(force simp add: safe_no_domainswitch)
  apply(erule meta_impE)
   using page_table_inv_preserved
   apply(force simp add: safe_no_domainswitch)
  apply (rule_tac b="instr_step a s" in uwr_trans)
   defer
   apply assumption
  (* now we are down to the single step *)
  defer
  apply (erule_tac i=a in d_not_running_step; simp)
  done

(* d not running \<rightarrow> d not running *)
lemma d_not_running: "\<lbrakk>
   \<comment> \<open>we have two programs derived from touched_addresses - may not be the same touched_addresses\<close>
   p\<^sub>s \<in> programs_obeying_ta (other_state s);
   p\<^sub>t \<in> programs_obeying_ta (other_state t);
   p\<^sub>s \<in> programs_safe (other_state s);
   p\<^sub>t \<in> programs_safe (other_state t);
   \<comment> \<open>we may not have concrete touched_addresses -
     we may overapprox this to the whole currently running domain.
     NB: I think it's enough just to require it not contain any of d's addresses. -robs.\<close>
   \<comment> \<open>these touched_addresses does NOT contain any addresses from d\<close>
   touched_addrs_inv' s;
   touched_addrs_inv' t;
   page_table_inv' s;
   page_table_inv' t;
   \<comment> \<open>initial states s and t hold uwr_notrunning\<close>
   (s, t) \<in> uwr d;
   current_domain' s \<noteq> d;
   \<comment> \<open>NB: external_uwr should give us current_domain' t \<noteq> d\<close>
   \<comment> \<open>we execute both programs\<close>
   s' = instr_multistep p\<^sub>s s;
   t' = instr_multistep p\<^sub>t t;
   current_domain' s' \<noteq> d
   \<comment> \<open>NB: external_uwr should oblige us to prove current_domain' t' \<noteq> d\<close>
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new state s' and t' hold uwr_notrunning\<close>
   (s', t') \<in> uwr d"
  apply clarsimp
  apply (subgoal_tac "current_domain' t \<noteq> d")
   apply (drule(4) d_not_running_integrity_uwr [where s=s])
   apply (drule(4) d_not_running_integrity_uwr [where s=t])
  apply (rule uwr_trans, subst uwr_sym, assumption)
   apply (rule uwr_trans, assumption, assumption)
  using uwr_same_domain apply blast
  done
  
  

(* --- notes for domainswitch step stuff ---- *)


(*

  
  - firstly, a ta-based step
  - then, SPECIFIC OPERATIONS



  A domainswitch step from u1 to u2 will look like:
  - some operations that obey TA as with other steps (and therefore
    also preserve the appropriate UWR.
  - now a very speifically defined set of operations, at the instruction level:
    - change the domain (this changes other_state memory)
    - flush pch for kernel shared precise
    - flush fch
    - pad to time
    - load registers
      - this is a series of reads from u2's memory, and it results in a total "regs" state
        that is dependent only upon u2's memory.

  We conceptualise a domainswitch in those two stages. first, something underdefined
  that follows normal TA rules, so the existing proofs will work happily with those.
  Then, we have a strictly defined program that is 


  Why this works:
  For the to-running case:
  - start with u2 running. uwr u1 gives:
    - same pch for that domain except kernel_shared_extended
    - same external uwr (means external memory for u1)
  - we end with u1 running. uwr u1 now requires:
    - same pch for that domain PLUS kernel_shared_expanded
      - we can get this from the pch flush, and the exit-path only reading from u1 AND
        being a totally defined set of instructions will create a uniform impact on all
        of the pch that we care about.
    - same fch totally
      - this becomes the same on fch flush, then padding and exitpath/regload must
        have a uniform impact on it.
    - same time
      - at the start we have no idea about time, so we need some way of knowing that
        pad-to-time will both pad to exactly the same time. after that, the exit path is
        deterministic isntructions that depend only on state on u1, so will be consistent.
    - same regs
      - we need to konw that the exit path overrides all regs, from u1's memory,
        so they will be the same at the end.
    - same other_state
      - this will be given by an external property.

  For the from-running case:
  - start with u1 running. uwr u1 gives:
    - same pch for that domain PLUS kernel shared
    - same fch
    - same time
    - same regs
    - other_state from external_uwr
  - we end with u2 running. uwr u1 requires:
    - same pch for that domain EXCEPT kernel shared
      - none of the operations will affect u1's part of pch
    - same other_state
      - this will be given by an external property


*)

(* this will mostly mimic the requirements for non-domainswitch step requirements *)
(*FIXME: define this *)
definition
  is_simple_program_d :: "'userdomain domain \<Rightarrow> 'regs program \<Rightarrow> bool" where
  "is_simple_program_d d p \<equiv> True"

(* this is an instruction that sets the domain to d. *)
(*FIXME: perhaps "\<forall>s" is too strong? Perhaps not.*)
definition
  is_domainswitch_instr :: "'userdomain domain \<Rightarrow> 'regs instr \<Rightarrow> bool" where
  "is_domainswitch_instr d i \<equiv> \<forall> s. current_domain' (instr_step i s) = d"

(* this is the time that will end current domain slice *)
(*FIXME: implement properly
  notes: schedule_oracle might be the way to implement this. however,
    there needs to be some point at which the concept of time in this model
    is connected to the looser concepts of time in seL4 spec. Not sure if this
    is one of the places for that connection to occur though.

 *)
definition
  fully_padded_time :: "time \<Rightarrow> time" where
  "fully_padded_time t \<equiv> 12345"

(* this is a (very specific) program that reads registers from memory.
   requirements:
   - leaves regs in a state that is dependent ONLY on domain `d` (ie removes all previous regs state)
   - needs to have an impact on fch and pch that is dependent only on stuff visible to d2
   - needs to take a bounded amount of time

   implementation ideas:
   - i think this is only a series of reads.
   - probably a set number of reads.
   - the list of addresses is probably set too - determined by the domain.
   - the read addresses are domain-confined.
   - how do we bound the time? a set number of reads, and a read has a max time?
   - regs impact of read isn't strongly defined in this model. we just assert here that
     regs will be overwritten completely. knowing that regs state might require a state input.
*)
definition
  is_loadregs_program :: "'userdomain domain \<Rightarrow> 'regs program \<Rightarrow> bool" where
  "is_loadregs_program d p \<equiv> True"

(* the given program is a domainswitch program. This means a program that starts in domain d1,
  at time t, switches to domain d2, and performs all the appropriate steps along the way. *)
definition
  is_domainswitch_program :: "'userdomain domain \<Rightarrow> 'userdomain domain \<Rightarrow> time \<Rightarrow> 'regs program \<Rightarrow> bool" where
  "is_domainswitch_program d1 d2 t p \<equiv> \<exists> p1 iswitch pregs.
                                       p = p1
                                         @ [iswitch,
                                            IFlushL2 kernel_shared_precise,
                                            IFlushL1,
                                            IPadToTime (fully_padded_time t)]
                                         @ pregs
                                     \<and> is_simple_program_d d1 p1
                                     \<and> is_domainswitch_instr d2 iswitch
                                     \<and> is_loadregs_program d2 pregs"

(* major questions:

  - is there anything else in the exit path apart from loadregs?
  - exit path doesn't need to take constant time - it only needs to take time dependent on the new
    domain. obviously it needs to take a bounded amount of time though.
  - time in this model and in seL4. does there need to be some relationship between time in this
    model and time in the seL4 model? at what point is this link made? This probably needs to be
    part of the integration, but then our use of a scheduler oracle needs to line up with that
    somehow.
*)



(* XXX: Just commenting it out unchanged to avoid any nasty merge conflicts -robs.
(*FIXME: This is a draft *)
(* d running \<rightarrow> d not running *)
lemma context_switch_from_d: "\<lbrakk>
   p \<in> programs_obeying_ta ta;
   ta \<inter> all_addrs_of d = {};
   (s, t) \<in> uwr d;
   current_domain' s = d;
   \<comment> \<open>NB: external_uwr should give us current_domain' t = d\<close>
   s' = instr_multistep p s;
   t' = instr_multistep p t;
   current_domain' s' \<noteq> d
   \<comment> \<open>NB: external_uwr should oblige us to prove current_domain' t' \<noteq> d\<close>
   \<rbrakk> \<Longrightarrow>
   (s', t') \<in> uwr d"
  oops

(* d not running \<rightarrow> d running *)
lemma context_switch_to_d: "\<lbrakk>
   p\<^sub>s \<in> programs_obeying_ta ta\<^sub>s;
   p\<^sub>t \<in> programs_obeying_ta ta\<^sub>t;
   ta\<^sub>s \<inter> all_addrs_of d \<subseteq> kernel_shared_precise;
   ta\<^sub>t \<inter> all_addrs_of d \<subseteq> kernel_shared_precise;
   (s, t) \<in> uwr d;
   current_domain' s \<noteq> d;
   \<comment> \<open>external_uwr should give us current_domain' t \<noteq> d\<close>
   s' = instr_multistep (p\<^sub>s @ [IFlushL1, IPadToTime detTime]) s;
   t' = instr_multistep (p\<^sub>t @ [IFlushL1, IPadToTime detTime]) t;
   current_domain' s' = d
   \<comment> \<open>external_uwr should oblige us to prove current_domain' t' = d\<close>
   \<rbrakk> \<Longrightarrow>
   (s', t') \<in> uwr d"
  oops
*)



(* ------------------------- end ----------------- *)












(*

  existing infoflow structure:

  we have lots of transitions

  S1  ---------> S2

  these preserve UWRs

  


  if we have, for every possible step in the above transition system:
  - that step was some monad m, which executes from state s to state s'.
  - we know from infoflow that uwr is maintained
  - we say there is some program p, representing m in the timeprot model.
  - we then show that uwr (incl caches and time) is also held.



  things we need:
  - given some monad m, give some program(s) that are equivalent.
  - OR given some final touched_addresses ta, give some programs(s) that represent the monads.






  we have some program derived from:
  - the other_state at the start
  - the touched_addresses at the end

  given that it's derived from touched_addresses, we know it does not stray from touched_addresses

  
  - there exists some function from other_state to a program that will execute next
  - that function generates the same program on two states if uwr holds (uwr including fch etc) 
  - 


  get_program :: other_state \<Rightarrow> program

  is_running d \<Longrightarrow>
  (s, t) \<in> uwr d \<Longrightarrow>
  get_program s = get_program t

  



  do we need to prove that our programs derived from touched_addresses are "equivalent" to monads
  that generated those touched_addresses?













*)




























lemma programs_obeying_ta_preserve_uwr: "\<lbrakk>
   \<not> can_domain_switch (other_state s);
   \<not> can_domain_switch (other_state t);
   touched_addrs_inv' s;
   touched_addrs_inv' t;
   page_table_inv' s;
   page_table_inv' t;
   is_secure_nondomainswitch p\<^sub>s s;
   is_secure_nondomainswitch p\<^sub>t t;
   (s, t) \<in> uwr d;
   current_domain' s = d \<longrightarrow> p\<^sub>s = p\<^sub>t;
   s' = instr_multistep p\<^sub>s s;
   t' = instr_multistep p\<^sub>t t
   \<rbrakk> \<Longrightarrow>
   (s', t') \<in> uwr d"
  apply(clarsimp simp:is_secure_nondomainswitch_def)
  apply(frule uwr_same_domain)
  apply(case_tac "current_domain' s = d")
   apply clarsimp
   apply(prop_tac "current_domain' s' = d")
    apply(metis no_domainswitch_inv)
   apply(force intro:d_running)
  apply(prop_tac "current_domain' s' \<noteq> d")
   apply(metis no_domainswitch_inv)
  apply clarsimp
  apply(force intro:d_not_running[where s=s and t=t and p\<^sub>s=p\<^sub>s and p\<^sub>t=p\<^sub>t])
  done

end

(* XXX: defunct -robs.
locale time_protection_system =
  us?: unwinding_system A s0 "\<lambda>_. current_domain" external_uwr policy out Sched +
  tp?: time_protection collides_in_pch fch_lookup pch_lookup
    fch_read_impact pch_read_impact fch_write_impact pch_write_impact
    read_cycles write_cycles do_read do_write store_time padding_regs_impact
    empty_fch fch_flush_cycles do_pch_flush pch_flush_cycles addr_domain addr_colour colour_userdomain
    current_domain external_uwr  touched_addrs can_domain_switch
  for A :: "('a,'other_state,unit) data_type"
  and s0 :: "'other_state"
  and current_domain :: "'other_state \<Rightarrow> 'userdomain domain"
  and external_uwr :: "'userdomain domain \<Rightarrow> ('other_state \<times> 'other_state) set"
  and policy :: "('userdomain domain \<times> 'userdomain domain) set"
  and out :: "'userdomain domain \<Rightarrow> 'other_state \<Rightarrow> 'p"
  and collides_in_pch :: "address rel"
  and fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  and pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"
  and fch_read_impact :: "'fch fch_impact"
  and pch_read_impact :: "('fch, 'pch) pch_impact"
  and fch_write_impact :: "'fch fch_impact"
  and pch_write_impact :: "('fch, 'pch) pch_impact"
  and read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and do_read :: "address \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and do_write :: "address \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'other_state"
  and store_time :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and padding_regs_impact :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and empty_fch :: "'fch"
  and fch_flush_cycles :: "'fch \<Rightarrow> time"
  and do_pch_flush :: "'pch \<Rightarrow> address set \<Rightarrow> 'pch"
  and pch_flush_cycles :: "'pch \<Rightarrow> address set \<Rightarrow> time"
  and addr_domain :: "address \<Rightarrow> 'userdomain domain"
  and addr_colour :: "address \<Rightarrow> 'colour"
  and colour_userdomain :: "'colour \<Rightarrow> 'userdomain"
  and touched_addrs :: "'other_state \<Rightarrow> address set"
  and can_domain_switch :: "'other_state \<Rightarrow> bool" +
  fixes initial_regs :: "'regs"
  fixes initial_pch :: "'pch"
  assumes touched_addrs_inv:
    "reachable s \<Longrightarrow> touched_addrs_inv s"

begin

(* XXX: defunct -robs.
definition has_secure_domainswitch :: "('fch,'pch,'regs,'other_state)state \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "has_secure_domainswitch s s' \<equiv>
     \<comment> \<open>Oblige the instantiator to ensure that in all possible reachable situations where the
         uwr holds there exists a domain-switch implementation pair that would preserve it.\<close>
     \<forall>d t t'. reachable (other_state t) \<and>
       (s, t) \<in> uwr d \<and> \<comment> \<open>The \<open>uwr\<close> should give us \<open>can_domain_switch (other_state t)\<close>.\<close>
       (other_state t, other_state t') \<in> Step () \<longrightarrow>
        (\<exists> p q.
           s' = instr_multistep p s \<and>
           t' = instr_multistep q t \<and>
           (s', t') \<in> uwr d)"

definition has_secure_implementation :: "('fch,'pch,'regs,'other_state)state \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "has_secure_implementation s s' \<equiv>
     if can_domain_switch (other_state s)
       then has_secure_domainswitch s s'
       else has_secure_nondomainswitch s s'"
*)

end
*)

locale time_protection_refinement =
  (* Can we expect C to be a Step_system?
    Locale `complete_noninterference_refinement` enforces this.
    But it doesn't look like we use this for seL4 infoflow refinement... -robs. *)
  nir?: complete_noninterference_refinement A s0 "\<lambda>_. current_domain" external_uwr policy out Sched C +
  tp?: time_protection collides_in_pch fch_lookup pch_lookup
    fch_read_impact pch_read_impact fch_write_impact pch_write_impact
    read_cycles write_cycles do_read do_write store_time padding_regs_impact
    empty_fch fch_flush_cycles do_pch_flush pch_flush_cycles addr_domain addr_colour colour_userdomain
    current_domain external_uwr v_to_p touched_addrs do_add_to_TA do_empty_TA can_domain_switch
  for A :: "('a,'other_state,unit) data_type"
  and C :: "('c,'other_state,unit) data_type"
  and s0 :: "'other_state"
  and current_domain :: "'other_state \<Rightarrow> 'userdomain domain"
  and external_uwr :: "'userdomain domain \<Rightarrow> ('other_state \<times> 'other_state) set"
  and policy :: "('userdomain domain \<times> 'userdomain domain) set"
  and out :: "'userdomain domain \<Rightarrow> 'other_state \<Rightarrow> 'p"
  and collides_in_pch :: "paddr rel"
  and fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  and pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"
  and fch_read_impact :: "'fch fch_impact"
  and pch_read_impact :: "'pch pch_impact"
  and fch_write_impact :: "'fch fch_impact"
  and pch_write_impact :: "'pch pch_impact"
  and read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and do_read :: "vaddr \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and do_write :: "vaddr \<Rightarrow> 'other_state \<Rightarrow> 'regs \<Rightarrow> 'other_state"
  and store_time :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and padding_regs_impact :: "time \<Rightarrow> 'regs \<Rightarrow> 'regs"
  and empty_fch :: "'fch"
  and fch_flush_cycles :: "'fch \<Rightarrow> time"
  and do_pch_flush :: "'pch \<Rightarrow> paddr set \<Rightarrow> 'pch"
  and pch_flush_cycles :: "'pch \<Rightarrow> paddr set \<Rightarrow> time"
  and addr_domain :: "paddr \<Rightarrow> 'userdomain domain"
  and addr_colour :: "paddr \<Rightarrow> 'colour"
  and colour_userdomain :: "'colour \<Rightarrow> 'userdomain"
  and v_to_p :: "'other_state \<Rightarrow> vaddr \<Rightarrow> paddr"
  and touched_addrs :: "'other_state \<Rightarrow> vaddr set"
  and do_add_to_TA :: "'other_state \<Rightarrow> vaddr set \<Rightarrow> 'other_state"
  and do_empty_TA :: "'other_state \<Rightarrow> 'other_state"
  and can_domain_switch :: "'other_state \<Rightarrow> bool" +
  fixes initial_regs :: "'regs"
  fixes initial_pch :: "'pch"
  assumes A_touched_addrs_inv:
    "abs.reachable s \<Longrightarrow> touched_addrs_inv s"
  assumes A_page_table_inv:
    "abs.reachable s \<Longrightarrow> page_table_inv s"
  fixes C_step_program :: "'other_state \<Rightarrow> 'other_state \<Rightarrow> 'regs program"
  assumes reachable_C_nondomainswitch_reqs:
    "(\<And> s s' p.
       (other_state s, other_state s') \<in> conc.Step () \<Longrightarrow>
       p = C_step_program (other_state s) (other_state s') \<Longrightarrow>
       conc.reachable (other_state s) \<Longrightarrow>
       \<not> can_domain_switch (other_state s) \<Longrightarrow>
       s' = instr_multistep p s \<and> is_secure_nondomainswitch p s \<and> kludge_uwr_same_programs p s)"
  assumes reachable_C_domainswitch_reqs:
    "(\<And> d s s' t t' p q.
       (other_state s, other_state s') \<in> conc.Step () \<Longrightarrow>
       p = C_step_program (other_state s) (other_state s') \<Longrightarrow>
       q = C_step_program (other_state t) (other_state t') \<Longrightarrow>
       conc.reachable (other_state s) \<Longrightarrow>
       conc.reachable (other_state t) \<Longrightarrow>
       (other_state t, other_state t') \<in> conc.Step () \<Longrightarrow>
       can_domain_switch (other_state s) \<Longrightarrow>
       (s, t) \<in> uwr d \<Longrightarrow> \<comment> \<open>The \<open>uwr\<close> should give us \<open>can_domain_switch (other_state t)\<close>.\<close>
       s' = instr_multistep p s \<and> t' = instr_multistep q t \<and> (s', t') \<in> uwr d)"
begin

(* What I would have wanted is something like this. But the `data_type`'s Step field
   doesn't keep the monads, only the state pairs it derived from them. -robs.
definition retrieve_C_monad :: "'other_state \<Rightarrow> 'other_state \<Rightarrow> monad"
definition C_monad_program :: "monad \<Rightarrow> 'regs program"
*)

definition is_secure_domainswitch :: "'regs program \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state \<Rightarrow> ('fch,'pch,'regs,'other_state)state \<Rightarrow> bool"
  where
  "is_secure_domainswitch p s s' \<equiv>
     \<forall>d t t'. reachable (other_state t) \<and>
       (s, t) \<in> uwr d \<and> \<comment> \<open>The \<open>uwr\<close> should give us \<open>can_domain_switch (other_state t)\<close>.\<close>
       (other_state t, other_state t') \<in> conc.Step () \<and>
       s' = instr_multistep (C_step_program (other_state s) (other_state s')) s \<and>
       t' = instr_multistep (C_step_program (other_state t) (other_state t')) t \<longrightarrow>
       (s', t') \<in> uwr d"

lemma reachable_C_domainswitch_secure:
  "conc.reachable (other_state s) \<Longrightarrow>
   (other_state s, other_state (s'::('fch,'pch,'regs,'other_state)state)) \<in> conc.Step () \<Longrightarrow>
   can_domain_switch (other_state s) \<Longrightarrow>
   is_secure_domainswitch (C_step_program (other_state s) (other_state s')) s s'"
  unfolding is_secure_domainswitch_def
  apply clarsimp
  apply(frule reachable_C_domainswitch_reqs, simp_all)
  by force

lemma reachable_C_nondomainswitch_reqs_nonspecific:
  "(\<And> s so' p.
     (other_state s, so') \<in> conc.Step () \<Longrightarrow>
     p = C_step_program (other_state s) so' \<Longrightarrow>
     conc.reachable (other_state s) \<Longrightarrow>
     \<not> can_domain_switch (other_state s) \<Longrightarrow>
     \<exists>s'. so' = other_state s' \<and>
       s' = instr_multistep p s \<and> is_secure_nondomainswitch p s \<and> kludge_uwr_same_programs p s)"
  using reachable_C_nondomainswitch_reqs
  by (metis state.select_convs(5))

lemma reachable_C_domainswitch_reqs_nonspecific:
  "(\<And> d s t so' to' p q.
     (other_state s, so') \<in> conc.Step () \<Longrightarrow>
     p = C_step_program (other_state s) so' \<Longrightarrow>
     q = C_step_program (other_state t) to' \<Longrightarrow>
     conc.reachable (other_state s) \<Longrightarrow>
     conc.reachable (other_state t) \<Longrightarrow>
     (other_state t, to') \<in> conc.Step () \<Longrightarrow>
     can_domain_switch (other_state s) \<Longrightarrow>
     (s, t) \<in> uwr d \<Longrightarrow> \<comment> \<open>The \<open>uwr\<close> should give us \<open>can_domain_switch (other_state t)\<close>.\<close>
     \<exists>s' t'. so' = other_state s' \<and> to' = other_state t' \<and>
       s' = instr_multistep p s \<and> t' = instr_multistep q t \<and> (s', t') \<in> uwr d)"
  using reachable_C_domainswitch_reqs
  by (metis state.select_convs(5))

definition A_extended_Step :: "unit \<Rightarrow>
  ('fch,'pch,'regs,'other_state)state rel"
  where
  "A_extended_Step \<equiv> \<lambda>_. {(s, s').
     (other_state s, other_state s') \<in> Step () \<and>
     (let p = C_step_program (other_state s) (other_state s') in
       s' = instr_multistep p s \<and>
       (\<not> can_domain_switch (other_state s) \<longrightarrow>
         is_secure_nondomainswitch p s \<and> kludge_uwr_same_programs p s))}"

definition A_extended ::
  "(('fch,'pch,'regs,'other_state)state,
    ('fch,'pch,'regs,'other_state)state,unit) data_type"
  where
  "A_extended = \<lparr> Init = \<lambda>s. {s}, Fin = id, Step = A_extended_Step \<rparr>"

definition A_extended_state ::
  "'other_state \<Rightarrow> ('fch,'pch,'regs,'other_state)state"
  where
  "A_extended_state s =
     \<lparr> fch = empty_fch, pch = initial_pch, tm = 0, regs = initial_regs, other_state = s \<rparr>"

(* This is now redundant with the Init_inv_Fin_system interpretation below, but I'll commit this
   at least once in case we change something and are left only with Init_Fin_system. -robs. *)
interpretation tpni: Init_Fin_system A_extended "A_extended_state s0"
  apply unfold_locales
     (* Init_Fin_system.reachable_s0 *)
     apply(clarsimp simp:A_extended_state_def A_extended_def A_extended_Step_def)
     apply(clarsimp simp:system.reachable_def execution_def)
     apply(metis (no_types, lifting) foldl_Nil singletonI steps_def)
    (* Init_Fin_system.Fin_Init *)
    apply(force simp:A_extended_def)
   (* Init_Fin_system.Init_Fin *)
   apply(force simp:A_extended_def)
  (* Init_Fin_system.obs_det_or_no_abs *)
  apply(rule disjI2)
  apply(force simp:system.no_abs_def A_extended_def)
  done

interpretation tpni: Init_inv_Fin_system A_extended "A_extended_state s0"
  apply unfold_locales
    (* Init_Fin_system.Fin_Init_s0 *)
    apply(force simp:A_extended_state_def A_extended_def)
   (* Init_Fin_system.Init_inv_Fin *)
   apply(force simp:A_extended_def)
  (* Init_Fin_system.Fin_inj *)
  apply(force simp:A_extended_def)
  done

lemma to_C_step:
  "(x, y) \<in> tpni.Step () \<Longrightarrow>
   (other_state x, other_state y) \<in> Step ()"
  by (clarsimp simp:tpni.Step_def system.Step_def execution_def
      A_extended_def A_extended_Step_def steps_def)

lemma to_C_run:
  "(s, s') \<in> Run tpni.Step as \<Longrightarrow>
   (other_state s, other_state s') \<in> Run local.Step as"
  apply(induct as arbitrary:s)
   apply(force simp:A_extended_state_def)
  apply clarsimp
  apply(erule_tac x=y in meta_allE)
  apply clarsimp
  apply(subgoal_tac "(other_state x, other_state y) \<in> Step ()")
   apply blast
  using to_C_step by blast

lemma to_C_run':
  "(A_extended_state s, s') \<in> Run tpni.Step as \<Longrightarrow>
   (s, other_state s') \<in> Run local.Step as"
  apply(clarsimp simp:A_extended_state_def)
  using to_C_run by force

lemma to_C_reachability:
  "tpni.reachable s \<Longrightarrow> conc.reachable (other_state s)"
  (* Note: We're relying on C to be a Step_system here. Is this reasonable? -robs. *)
  apply(rule conc.Run_reachable)
  apply(drule tpni.reachable_Run)
  apply clarsimp
  apply(rule_tac x=as in exI)
  using to_C_run' by blast

lemma to_original_step:
  "(x, y) \<in> tpni.Step () \<Longrightarrow>
   (other_state x, other_state y) \<in> abs.Step ()"
  apply(drule to_C_step)
  using refines unfolding refines_def execution_def steps_def conc.Step_def abs.Step_def
  by blast

lemma to_original_run:
  "tpni.reachable s \<Longrightarrow>
   (s, s') \<in> Run tpni.Step as \<Longrightarrow>
   (other_state s, other_state s') \<in> Run abs.Step as"
  apply(drule to_C_run)
  apply(frule to_C_reachability)
  apply(frule reachable)
  using refines conc.execution_Run abs.execution_Run unfolding refines_def
  by blast

lemma to_original_run':
  "tpni.reachable (A_extended_state s) \<Longrightarrow>
   (A_extended_state s, s') \<in> Run tpni.Step as \<Longrightarrow>
   (s, other_state s') \<in> Run abs.Step as"
  using to_original_run A_extended_state_def
  by fastforce

lemma to_original_reachability:
  "tpni.reachable s \<Longrightarrow> abs.reachable (other_state s)"
  using to_C_reachability reachable by blast

lemma to_extended_step_enabledness:
 "\<lbrakk>reachable (other_state s);
   \<exists>s'. (other_state s, other_state (s'::('fch,'pch,'regs,'other_state)state)) \<in> Step ()
  \<rbrakk> \<Longrightarrow> \<exists>s'. (s, s') \<in> system.Step A_extended ()"
  apply clarsimp
  apply(case_tac "can_domain_switch (other_state s)")
   apply(frule reachable_C_domainswitch_reqs, simp_all)
    apply(force simp:uwr_equiv)
   apply(clarsimp simp:uwr_equiv)
   apply(rule_tac x=s' in exI)
   apply(force simp:system.Step_def execution_def A_extended_def A_extended_Step_def steps_def)
  apply(frule reachable_C_nondomainswitch_reqs, simp_all)
  apply(rule_tac x=s' in exI)
  apply(force simp:system.Step_def execution_def A_extended_def A_extended_Step_def steps_def)
  done

lemma to_some_extended_step:
 "\<lbrakk>conc.reachable (other_state s);
   (other_state s, os') \<in> conc.Step ()
  \<rbrakk> \<Longrightarrow> \<exists>s'. os' = other_state s' \<and> (s, s') \<in> system.Step A_extended ()"
  apply(prop_tac "os' = other_state (instr_multistep (C_step_program (other_state s) os') s)")
   apply(case_tac "can_domain_switch (other_state s)")
    apply(frule_tac so'=os' in reachable_C_domainswitch_reqs_nonspecific, simp_all)
     apply(force simp:uwr_equiv)
    apply(clarsimp simp:uwr_equiv)
   apply(frule_tac so'=os' in reachable_C_nondomainswitch_reqs_nonspecific, simp_all)
   apply force
  apply(rule_tac x="(instr_multistep (C_step_program (other_state s) os') s)" in exI)
  apply(rule conjI)
   apply force
  unfolding tpni.Step_def (* Warning: This unfold has to happen first for some reason -robs. *)
  apply(clarsimp simp:execution_def A_extended_def A_extended_Step_def steps_def Let_def)
  using reachable_C_nondomainswitch_reqs_nonspecific apply blast
  done

lemma to_specific_extended_step:
 "\<lbrakk>reachable (other_state s);
   (other_state s, other_state s') \<in> Step ()
  \<rbrakk> \<Longrightarrow> (s, s') \<in> system.Step A_extended ()"
  apply(case_tac "can_domain_switch (other_state s)")
   apply(frule reachable_C_domainswitch_reqs, simp_all)
    apply(force simp:uwr_equiv)
   apply(clarsimp simp:uwr_equiv)
   apply(force simp:system.Step_def execution_def A_extended_def A_extended_Step_def steps_def)
  apply(frule reachable_C_nondomainswitch_reqs, simp_all)
  apply(force simp:system.Step_def execution_def A_extended_def A_extended_Step_def steps_def)
  done

lemma to_extended_execution_enabledness:
 "\<lbrakk>tpni.reachable s;
   reachable (other_state s);
   \<exists>os'. os' \<in> execution C (other_state s) js \<comment> \<open>enabledness of original system at (other_state s)\<close>\<rbrakk>
  \<Longrightarrow> \<exists>s'. s' \<in> execution A_extended s js" \<comment> \<open>enabledness of extended system at s\<close>
  apply(induct js arbitrary:s)
   apply(force simp:execution_def steps_def A_extended_def)
  apply clarsimp
  apply(rename_tac js s os')
  (* We need s' to be an extension of os'. But we also need it to be
     a state we arrive at after one tpni.Step from s. *)
  apply(frule_tac as="() # js" in conc.execution_Run)
  apply clarsimp
  apply(rename_tac js s os'' os')
  apply(prop_tac "os'' = other_state (instr_multistep (C_step_program (other_state s) os'') s)")
   apply(case_tac "can_domain_switch (other_state s)")
    apply(frule_tac so'=os'' in reachable_C_domainswitch_reqs_nonspecific, simp_all)
     apply(force simp:uwr_equiv)
    apply(force simp:uwr_equiv)
   apply(frule_tac so'=os'' in reachable_C_nondomainswitch_reqs_nonspecific, simp_all)
   apply force
  apply(erule_tac x="instr_multistep (C_step_program (other_state s) os'') s" in meta_allE)
  apply(erule meta_impE)
   apply(rule_tac a="()" in tpni.reachable_Step)
    apply force
   unfolding tpni.Step_def (* For some reason this can't just be in the simps on the next line. *)
   apply(clarsimp simp:execution_def A_extended_def A_extended_Step_def steps_def Let_def)
   using reachable_C_nondomainswitch_reqs_nonspecific apply blast
  apply(erule meta_impE)
   using conc.reachable_Step apply force
  apply(erule meta_impE)
   using conc.reachable_Step reachable_enabled apply force
  apply clarsimp
  apply(frule_tac s'="instr_multistep (C_step_program (other_state s) os'') s" in to_specific_extended_step)
   apply force
  apply(prop_tac "tpni.reachable (instr_multistep (C_step_program (other_state s) os'') s)")
   using tpni.reachable_Step apply blast
  apply(prop_tac "tpni.reachable s'")
   using tpni.reachable_execution apply blast
  apply(rule_tac x=s' in exI)
  apply(drule_tac as="() # js" in tpni.execution_Run)
  apply clarsimp
  using tpni.execution_Run by auto

interpretation tpni: unwinding_system A_extended "A_extended_state s0" "\<lambda>_. current_domain'" uwr
  policy "\<lambda>d s. out d (other_state s)" Sched
  apply unfold_locales
      (* enabled_system.enabled *)
      apply(prop_tac "reachable (other_state s)")
       apply(simp only:system.reachable_def[symmetric])
       apply(force dest:to_C_reachability)
      apply(simp only:tpni.reachable_def[symmetric])
      apply(frule_tac js=js in enabled[simplified reachable_def[symmetric]])
      using to_extended_execution_enabledness apply blast
     (* noninterference_policy.uwr_equiv_rel *)
     using extended_uwr_equiv_rel apply blast
    (* noninterference_policy.schedIncludesCurrentDom *)
    using uwr_same_domain apply blast
   (* noninterference_policy.schedFlowsToAll *)
   using schedFlowsToAll apply blast
  (* noninterference_policy.schedNotGlobalChannel *)
  using schedNotGlobalChannel apply blast
  done

theorem extended_confidentiality_u:
  "conc.confidentiality_u \<Longrightarrow> tpni.confidentiality_u"
  apply(clarsimp simp:confidentiality_u_def tpni.confidentiality_u_def)
  apply(erule_tac x=u in allE)
  apply(erule_tac x="other_state s" in allE)
  apply(erule_tac x="other_state t" in allE)
  apply(prop_tac "reachable (other_state s) \<and> reachable (other_state t)")
   using to_C_reachability apply force
  apply(prop_tac "uwr2 (other_state s) Sched (other_state t)")
   using uwr_to_external apply blast
  apply(prop_tac "((current_domain (other_state s), u) \<in> policy) \<longrightarrow>
        uwr2 (other_state s) (current_domain (other_state s)) (other_state t)")
   using uwr_to_external apply blast
  apply(prop_tac "uwr2 (other_state s) u (other_state t)")
   using uwr_to_external apply blast
  apply clarsimp
  apply(erule_tac x="other_state s'" in allE)
  apply(erule_tac x="other_state t'" in allE)
  apply(frule_tac x=s in to_C_step)
  apply(frule_tac x=t in to_C_step)
  apply clarsimp
  (* The reachability assumptions just unfold into something messy - get rid of them. -robs. *)
  apply(thin_tac "tpni.reachable x" for x)+
  apply(clarsimp simp:tpni.Step_def system.Step_def A_extended_def execution_def A_extended_Step_def steps_def)
  apply(frule can_domain_switch_public)
  apply(case_tac "can_domain_switch (other_state s)")
   apply(clarsimp simp:Let_def)
   apply(frule_tac s'="instr_multistep (C_step_program (other_state s) (Fin C x)) s"
         in reachable_C_domainswitch_secure)
     apply(clarsimp simp:conc.Step_def execution_def steps_def)
     apply blast
    apply force
   apply(clarsimp simp:is_secure_domainswitch_def)
   apply(erule_tac x=u in allE)
   apply(erule_tac x=t in allE)
   apply clarsimp
   apply(rename_tac u s t s_priv' s_priv t_priv' t_priv)
   apply(erule_tac x="instr_multistep (C_step_program (other_state t) (Fin C t_priv')) t" in allE)
   apply(clarsimp simp:conc.Step_def execution_def steps_def)
   apply blast
  apply(clarsimp simp:Let_def)
  apply(rename_tac u s t s_priv' s_priv t_priv' t_priv)
  apply(rule programs_obeying_ta_preserve_uwr, simp_all)
      apply(force simp:A_touched_addrs_inv reachable)
     apply(force simp:A_touched_addrs_inv reachable)
    apply(force simp:A_page_table_inv reachable)
   apply(force simp:A_page_table_inv reachable)
  apply(force simp:kludge_uwr_same_programs_def)
  done

theorem extended_Nonleakage:
  "abs.Nonleakage_gen \<Longrightarrow> tpni.Nonleakage_gen"
  apply(prop_tac "conc.Nonleakage_gen")
   apply(force intro:Nonleakage_gen_refinement_closed)
  using conc.Nonleakage_gen_confidentiality_u extended_confidentiality_u tpni.Nonleakage_gen
  by blast

end
end