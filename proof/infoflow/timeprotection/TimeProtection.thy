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
  "Lib.Apply_Trace_Cmd"
begin

(* questions:
  - do we want to support a writeback `fch`?
    - We know how we'd implement it, we dont think it would be heaps more work. we just need
      to know if it's needed.


*)

datatype vaddr = VAddr machine_word
datatype paddr = PAddr machine_word

type_synonym vpaddr = "vaddr \<times> paddr"

\<comment> \<open> flushable (fch) and partitionable (pch) caches\<close>
type_synonym 'fch_cachedness fch = "vaddr \<Rightarrow> 'fch_cachedness"
type_synonym 'pch_cachedness pch = "paddr \<Rightarrow> 'pch_cachedness"
type_synonym 'fch fch_impact = "vaddr \<Rightarrow> 'fch \<Rightarrow> 'fch"
(* Note: This `pch_impact` version only supports a writethrough `fch`. *)
type_synonym 'pch pch_impact = "paddr \<Rightarrow> 'pch \<Rightarrow> 'pch"
(* FIXME: If we want to support a writeback `fch`, we'll need to use a type signature like this
  instead. This is because when a read or write evicts a dirty `fch` entry, that dirty bit (and value)
  will need to be propagated to the corresponding `pch` entry. -robs.
type_synonym ('fch,'pch) pch_impact = "vaddr \<Rightarrow> 'fch \<Rightarrow> 'pch \<Rightarrow> 'pch" *)

type_synonym time = nat

datatype 'userdomain domain = Sched | User 'userdomain

record ('fch,'pch) state =
  fch :: "'fch" \<comment> \<open> flushable cache\<close>
  pch :: "'pch" \<comment> \<open> partitionable cache \<close>
  tm :: time

locale time_protection =
  (* "a coll b" = "a may cause b to be evicted from or loaded to the pch" *)
  fixes collides_in_pch :: "paddr \<Rightarrow> paddr \<Rightarrow> bool" (infix "coll" 50)

  (* collides_in_pch isn't a relation, but it is kind of an equivalence *)
  assumes collides_with_equiv: "equiv UNIV ({(x, y). x coll y})"

  (* instead of making fch and pch functions, we leave them unspecified but
     require lookup functions for them *)
  fixes fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  fixes pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"

  (* we require read_impact functions for both pch and fch *)
  fixes fch_read_impact :: "'fch fch_impact"
  fixes pch_read_impact :: "'pch pch_impact"

  \<comment> \<open> pch_read_impact only impacts colliding addresses \<close>
  assumes pch_partitioned_read:
    "\<not>a coll b \<Longrightarrow> pch_lookup p b = pch_lookup (pch_read_impact a p) b"


  \<comment> \<open> if `b` can be impacted by a read from `a`,
     we require that this impact depends only on the prior state of the fch
     and the prior cachedness of the rest of their collision set in the pch \<close>
  assumes pch_collision_read: "\<And>a b pchs pcht.
    a coll b \<Longrightarrow>
    \<forall>c. a coll c \<longrightarrow> pch_lookup pchs c = pch_lookup pcht c \<Longrightarrow>
    \<comment> \<open>This might be stronger than is met by hardware that just promises
        a 'random' replacement algorithm. Essentially we are requiring that
        any such 'randomness' cannot be influenced by the prior cachedness of
        addresses outside the collision set in question. \<close>
    pchs' = pch_read_impact a pchs \<Longrightarrow>
    pcht' = pch_read_impact a pcht \<Longrightarrow>
    pch_lookup pchs' b = pch_lookup pcht' b"
  
  (* we require write_impact functions for both pch and fch *)
  fixes fch_write_impact :: "'fch fch_impact"
  fixes pch_write_impact :: "'pch pch_impact"

  \<comment> \<open>pch_write_impact only impacts colliding addresses\<close>
  assumes pch_partitioned_write:
    "\<not>a coll b \<Longrightarrow> pch_lookup p b = pch_lookup (pch_write_impact a p) b"

  \<comment> \<open> similar to pch_collision_read \<close>
  assumes pch_collision_write: "\<And>a b pchs pcht.
    a coll b \<Longrightarrow>
    \<forall>c. a coll c \<longrightarrow> pch_lookup pchs c = pch_lookup pcht c \<Longrightarrow>
    \<comment> \<open>The same strong requirement placing limits on the 'randomness'
        of the cache replacement algorithm as for @{term pch_collision_read}\<close>
    pchs' = pch_write_impact a pchs \<Longrightarrow>
    pcht' = pch_write_impact a pcht \<Longrightarrow>
    pch_lookup pchs' b = pch_lookup pcht' b"

  (* given the fch_cachedness and the pch_cachedness of some access, tell me how long it took *)
  fixes read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  fixes write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"

  fixes empty_fch :: "'fch"
  (* how long it takes to flush a particular fch *)
  fixes fch_flush_cycles :: "'fch \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>

  fixes do_pch_flush :: "'pch \<Rightarrow> paddr set \<Rightarrow> 'pch"
  fixes pch_flush_cycles :: "'pch \<Rightarrow> paddr set \<Rightarrow> time" \<comment> \<open>could this be dependent on anything else?\<close>


  \<comment> \<open>pch flush only affects addresses that collide with the set\<close>
  assumes pch_partitioned_flush:
   "(\<forall>a'\<in>as. \<not> a coll a') \<Longrightarrow> pch_lookup (do_pch_flush p as) a = pch_lookup p a"

  
  assumes pch_collision_flush:
    "\<exists>a1\<in>as. a coll a1 \<Longrightarrow>
    \<forall>a1. (\<exists>a2\<in>as. a1 coll a2) \<longrightarrow> pch_lookup pchs a1 = pch_lookup pcht a1 \<Longrightarrow>
    pch_lookup (do_pch_flush pchs as) a = pch_lookup (do_pch_flush pcht as) a"

  \<comment> \<open> if all colliding addresses to @{term as} are the same, then the flush will take the same amount of time \<close>
  assumes pch_flush_cycles_localised:
    "\<forall>a1. (\<exists>a2\<in>as. a1 coll a2) \<longrightarrow> pch_lookup pchs a1 = pch_lookup pcht a1 \<Longrightarrow>
    pch_flush_cycles pchs as = pch_flush_cycles pcht as"

  \<comment> \<open>for each address, this is the security domain\<close>
  fixes addr_domain :: "paddr \<Rightarrow> 'userdomain domain"

  \<comment> \<open>for each address, this is the cache colour\<close>
  fixes addr_colour :: "paddr \<Rightarrow> 'colour"

  fixes colour_userdomain :: "'colour \<Rightarrow> 'userdomain"

  assumes no_cross_colour_collisions:
    "a1 coll a2 \<Longrightarrow> addr_colour a1 = addr_colour a2"
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
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain s2 = current_domain s1"
\<comment> \<open>we will probably needs lots more info about this external uwr\<close>

  (*TODO: is this a good way to do this? or should we carry around Sched uwr all the time separately? *)
  assumes external_uwr_Sched:
    "(s, t) \<in> external_uwr d \<Longrightarrow> (s, t) \<in> external_uwr Sched"

  fixes touched_addrs :: "'other_state \<Rightarrow> vpaddr set"
  (* the external uwr maintains that touched_addrs is the same for the currently running user *)
  assumes external_uwr_same_touched_addrs:
    "(s1, s2) \<in> external_uwr d \<Longrightarrow> current_domain s1 = d \<Longrightarrow> touched_addrs s1 = touched_addrs s2"

  (* We expect this to be true for, say, seL4's KSched \<rightarrow> KExit step. -robs. *)
  fixes will_domain_switch :: "'other_state \<Rightarrow> bool"
  assumes will_domain_switch_public:
    "(os, ot) \<in> external_uwr d \<Longrightarrow> will_domain_switch ot = will_domain_switch os"
begin

corollary colours_not_shared:
  "colour_userdomain c1 \<noteq> colour_userdomain c2 \<Longrightarrow> c1 \<noteq> c2"
  by blast

definition all_paddrs_of :: "'userdomain domain \<Rightarrow> paddr set" where
  "all_paddrs_of d = {a. addr_domain a = d}"

abbreviation collision_set :: "paddr \<Rightarrow> paddr set" where
  "collision_set a \<equiv> {b. a coll b}"

lemma collision_set_contains_itself: "a \<in> collision_set a"
  using collides_with_equiv
  by (clarsimp simp:equiv_def refl_on_def)

lemma external_uwr_refl [simp]:
  "(s, s) \<in> external_uwr d"
  using external_uwr_equiv_rel
  by (clarsimp simp: equiv_def refl_on_def)

lemma collision_collect:
  "a coll b = ((a, b) \<in> (Collect (case_prod collides_in_pch)))"
  by simp

lemma collision_sym [simp]:
  "a coll b \<Longrightarrow> b coll a"
  using collision_collect
  by (meson collides_with_equiv equiv_def symE)

\<comment> \<open> the addresses in kernel shared memory (which for now is everything in the sched domain)\<close>
definition kernel_shared_precise :: "paddr set" where
  "kernel_shared_precise \<equiv> {a. addr_domain a = Sched}"

\<comment> \<open> the kernel shared memory, including cache colliding addresses \<close>
definition kernel_shared_expanded :: "paddr set" where
  "kernel_shared_expanded \<equiv> {a. \<exists> z \<in> kernel_shared_precise. a \<in> collision_set z}"

\<comment> \<open> a full collision set contains all of its own collisions \<close>
definition full_collision_set :: "paddr set \<Rightarrow> bool" where
  "full_collision_set S \<equiv> \<forall>a1\<in>S. \<forall>a2. a1 coll a2 \<longrightarrow> a2 \<in> S"

lemma collision_set_full_collision_set:
  "full_collision_set (collision_set a)"
  apply (clarsimp simp: full_collision_set_def)
  using collision_collect
  apply (meson collides_with_equiv equiv_def trans_def)
  done

lemma kernel_shared_expanded_full_collision_set:
  "full_collision_set kernel_shared_expanded"
  apply (clarsimp simp: kernel_shared_expanded_def full_collision_set_def)
  using collision_collect
  apply (meson collides_with_equiv equiv_def trans_def)
  done

\<comment> \<open> in a full collision set S, if two addresses collide and one is not in the set, the other
     is also not in the set. \<close>
lemma collision_in_full_collision_set:
  "full_collision_set S \<Longrightarrow>
  a1 coll a2 \<Longrightarrow>
  a1 \<notin> S \<Longrightarrow>
  a2 \<notin> S"
  apply (clarsimp simp: full_collision_set_def)
  done

\<comment> \<open> the invariant that touched_addresses is always sensible for its current domain \<close>
definition touched_addrs_inv :: "'other_state \<Rightarrow> bool" where
  "touched_addrs_inv s \<equiv>
     snd ` touched_addrs s \<subseteq> all_paddrs_of (current_domain s) \<union> kernel_shared_precise"

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
  "'userdomain domain \<Rightarrow> ('fch,'pch)state rel"
  where
  "uwr_running d \<equiv> {(s1, s2). fch s1 = fch s2
                            \<and> pch_same_for_domain_and_shared d (pch s1) (pch s2)
                            \<and> tm s1 = tm s2 }"

definition uwr_notrunning ::
  "'userdomain domain \<Rightarrow> ('fch,'pch)state rel"
  where
  "uwr_notrunning d \<equiv> {(s1, s2). pch_same_for_domain_except_shared d (pch s1) (pch s2) }"

definition uwr ::
  "'userdomain domain \<Rightarrow> ('other_state \<times> ('fch,'pch)state) rel"
  where
  "uwr d \<equiv> {((os1, s1), (os2, s2)). (os1, os2) \<in> external_uwr d \<and>
                      (if (current_domain os1 = d)
                      then (s1, s2) \<in> uwr_running d
                      else (s1, s2) \<in> uwr_notrunning d ) }"

lemma uwr_external_uwr:
  "((so, s), (to, t)) \<in> uwr d \<Longrightarrow>
  (so, to) \<in> external_uwr d"
  apply (clarsimp simp: uwr_def)
  done

(*
lemma uwr_to_external:
  "(s, t) \<in> uwr d \<Longrightarrow> (other_state s, other_state t) \<in> external_uwr d"
  by (clarsimp simp:uwr_def uwr_running_def uwr_notrunning_def split:if_splits)

lemma uwr_same_domain:
  "(s, t) \<in> uwr d \<Longrightarrow> current_domain' s = current_domain' t"
  by (force dest:uwr_to_external external_uwr_same_domain)

lemma uwr_same_touched_addrs:
  "(s, t) \<in> uwr d \<Longrightarrow> current_domain' s = d \<Longrightarrow> touched_addrs' s = touched_addrs' t"
  by (force dest:uwr_to_external external_uwr_same_touched_addrs)
*)

lemma uwr_refl [simp]:
  "(s, s) \<in> uwr d"
  apply (clarsimp simp:uwr_def)
  apply (clarsimp simp: uwr_running_def pch_same_for_domain_and_shared_def)
  apply (clarsimp simp:uwr_notrunning_def pch_same_for_domain_except_shared_def)
  done

lemma uwr_sym':
  "((a, b) \<in> uwr d) \<Longrightarrow> ((b, a) \<in> uwr d)"
  apply (clarsimp simp: uwr_def)
  apply (frule external_uwr_same_domain; clarsimp)
  apply (case_tac "current_domain os2 = d"; clarsimp)
   apply (intro conjI, meson equiv_def external_uwr_equiv_rel symE)
   apply (clarsimp simp:uwr_running_def pch_same_for_domain_and_shared_def)
  apply (intro conjI, meson equiv_def external_uwr_equiv_rel symE)
  apply (clarsimp simp: uwr_notrunning_def pch_same_for_domain_except_shared_def)
  done

lemma uwr_trans:
  "(a, b) \<in> uwr d \<Longrightarrow>
  (b, c) \<in> uwr d \<Longrightarrow>
  (a, c) \<in> uwr d"
  apply (clarsimp simp: uwr_def)
  apply (frule external_uwr_same_domain; clarsimp)
  apply (case_tac "current_domain x = d"; clarsimp)
   apply (intro conjI, meson equiv_def external_uwr_equiv_rel transE)
   apply (clarsimp simp:uwr_running_def pch_same_for_domain_and_shared_def)
  apply (intro conjI, meson equiv_def external_uwr_equiv_rel transE)
  apply (clarsimp simp: uwr_notrunning_def pch_same_for_domain_except_shared_def)
  done

lemma uwr_equiv_rel:
  "equiv UNIV (uwr u)"
  apply(clarsimp simp:equiv_def)
  apply(intro conjI)
    \<comment> \<open>refl\<close>
    apply (clarsimp simp: refl_on_def)
   \<comment> \<open>sym\<close>
   apply (clarsimp simp:sym_def, erule uwr_sym')
  \<comment> \<open>trans\<close>
  apply (clarsimp simp:trans_def, erule uwr_trans, simp)
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






(* the different ways our trace can interact with microarch state *)
datatype trace_unit = IRead vpaddr           \<comment> \<open>read from some address\<close>
                    | IWrite vpaddr          \<comment> \<open>write to some address\<close>
                    | IFlushL1               \<comment> \<open>flush the entire L1 cache(s)\<close>
                    | IFlushL2 "paddr set"   \<comment> \<open>flush some part L2 cache(s)\<close>
                    | IPadToTime time        \<comment> \<open>pad the time up to some point, if that time is in the future\<close>

primrec
  trace_step :: "trace_unit \<Rightarrow>
    ('fch,'pch)state \<Rightarrow>
    ('fch,'pch)state" where
 "trace_step (IRead a) s =
      s\<lparr>fch := fch_read_impact (fst a) (fch s),
        pch := pch_read_impact (snd a) (pch s),
        tm  := tm s + read_cycles (fch_lookup (fch s) (fst a)) (pch_lookup (pch s) (snd a))\<rparr>"
  | "trace_step (IWrite a) s =
      s\<lparr>fch := fch_write_impact (fst a) (fch s),
        pch := pch_write_impact (snd a) (pch s),
        tm  := tm s + write_cycles (fch_lookup (fch s) (fst a)) (pch_lookup (pch s) (snd a))\<rparr>"
  | "trace_step (IPadToTime t) s =
      s\<lparr>tm := max (tm s) t\<rparr>" \<comment> \<open>will not step backwards\<close>
  | "trace_step IFlushL1 s =
      s\<lparr>fch := empty_fch,
        tm := tm s + fch_flush_cycles (fch s)\<rparr>"
  | "trace_step (IFlushL2 as) s =
      s\<lparr>pch := do_pch_flush (pch s) as,
        tm := tm s + pch_flush_cycles (pch s) as\<rparr>"

type_synonym trace = "trace_unit list"

primrec trace_multistep :: "trace \<Rightarrow>
  ('fch,'pch)state \<Rightarrow>
  ('fch,'pch)state" where
  "trace_multistep [] s = s"
| "trace_multistep (i#is) s = trace_multistep is (trace_step i s)"

definition
  trace_units_obeying_set :: "vpaddr set \<Rightarrow> trace_unit set" where
 "trace_units_obeying_set vps \<equiv> {i. case i of
                                 IRead a  \<Rightarrow> a \<in> vps
                               | IWrite a \<Rightarrow> a \<in> vps
                               | IFlushL2 as \<Rightarrow> as \<subseteq> snd ` vps
                               | _        \<Rightarrow> True }"

abbreviation
  trace_units_obeying_ta :: "'other_state \<Rightarrow> trace_unit set" where
 "trace_units_obeying_ta os \<equiv> trace_units_obeying_set (touched_addrs os)"

(* these are the programs that could have created this ta *)
definition
  traces_obeying_set :: "vpaddr set \<Rightarrow> trace set" where
 "traces_obeying_set vps \<equiv> {p. list_all (\<lambda>i. i \<in> trace_units_obeying_set vps) p}"

abbreviation
  traces_obeying_ta :: "'other_state \<Rightarrow> trace set" where
 "traces_obeying_ta os \<equiv> traces_obeying_set (touched_addrs os)"

lemma hd_trace_obeying_set [dest]:
  "a # p \<in> traces_obeying_set ta \<Longrightarrow> a \<in> trace_units_obeying_set ta \<and> p \<in> traces_obeying_set ta"
  by (force simp:traces_obeying_set_def)



\<comment> \<open>this is (current a draft of) the mechanisms that will allow us to define a 'dirty' trace
    that accesses memory belonging to two different domains. however, we enforce that the EXACT
    trace is dependent only upon the to- and from-domain, as well as things visible to the Sched
    uwr\<close>
type_synonym ('os, 'ud) dirty_trace_getter = "'ud domain \<Rightarrow> 'ud domain \<Rightarrow> 'os \<Rightarrow> trace"

type_synonym 'os next_time_getter = "'os \<Rightarrow> time"

definition same_next_time :: "'other_state next_time_getter \<Rightarrow> bool" where
  "same_next_time ntg \<equiv> \<forall> os os'. ((os, os') \<in> external_uwr Sched \<longrightarrow> ntg os' = ntg os)"

definition same_dirty_traces :: " ('other_state, 'userdomain) dirty_trace_getter \<Rightarrow> bool" where
  "same_dirty_traces dtg \<equiv> \<forall> u v os os'. ((os, os') \<in> external_uwr Sched \<longrightarrow> dtg u v os' = dtg u v os)"

definition correct_dirty_traces :: " ('other_state, 'userdomain) dirty_trace_getter \<Rightarrow> bool" where
  "correct_dirty_traces dtg \<equiv> \<forall> u v os. dtg u v os \<in> traces_obeying_set {(va, pa) | va pa. pa \<in> (all_paddrs_of u \<union> all_paddrs_of v \<union> kernel_shared_precise)}"

(* sketching out some definitions for domain-switch programs -scott *)
(*TODO: right now we only flush kernel_shared_precise. i hope that the proofs fail here, as we really
  need to be flushing kernel_shared_extended *)
definition get_domain_switch_trace ::
  "('other_state, 'userdomain) dirty_trace_getter \<Rightarrow> 'other_state next_time_getter \<Rightarrow> 'userdomain domain \<Rightarrow> 'userdomain domain \<Rightarrow> 'other_state \<Rightarrow> trace"
  where
  "get_domain_switch_trace dtg ntg u v os \<equiv> dtg u v os @ [IFlushL1, IFlushL2 kernel_shared_precise, IPadToTime (ntg os)]"

lemma collides_with_set_or_doesnt:
  "\<lbrakk>\<forall>a'\<in>as. \<not> a coll a' \<Longrightarrow> P;
    \<exists>a'\<in>as. a coll a' \<Longrightarrow> P \<rbrakk> \<Longrightarrow>
    P"
  by blast

lemma diff_domain_no_collision:
  "\<lbrakk>a \<notin> kernel_shared_expanded;
  addr_domain a' \<noteq> addr_domain a;
  a coll a'\<rbrakk> \<Longrightarrow>
  False"
  apply (frule(1) collision_in_full_collision_set [OF kernel_shared_expanded_full_collision_set])
  apply (metis (mono_tags, lifting) addr_domain_valid collision_set_contains_itself
               kernel_shared_expanded_def kernel_shared_precise_def mem_Collect_eq
               no_cross_colour_collisions)
  done

lemma in_image_union:
  "\<lbrakk>x \<in> S;
  f ` S \<subseteq> A \<union> B \<rbrakk> \<Longrightarrow>
  f x \<in> A \<or> f x \<in> B"
  apply blast
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

lemma and_or_specific':
  "((P \<or> Q \<Longrightarrow> R)) \<Longrightarrow>
   (P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)"
  apply simp
  done


(*
lemma d_not_running_step:
  assumes
  "i \<in> trace_units_obeying_ta os"
  "touched_addrs_inv os"
  "current_domain os \<noteq> d"
  "s' = instr_step i s"
  shows
  "((os, s), (os, s')) \<in> uwr d"
*)

lemma in_touched_addrs_expand:
  "a \<in> touched_addrs os \<Longrightarrow>
  touched_addrs_inv os \<Longrightarrow>
  snd a \<in> all_paddrs_of (current_domain os) \<or> snd a \<in> kernel_shared_precise"
  apply (clarsimp simp:touched_addrs_inv_def)
  apply blast
  done


lemma d_running_step:
  assumes
    "i \<in> trace_units_obeying_ta os'"
    "touched_addrs_inv os'"
    "((os, s), (ot, t)) \<in> uwr d"
    "(os', ot') \<in> external_uwr d"
    "current_domain os = d"
    "s' = trace_step i s"
    "t' = trace_step i t"
    (* the only thing we care about output other_state is that the domain hasn't changed *)
    "current_domain os' = current_domain os"
    "current_domain ot' = current_domain ot"
  shows
    "((os', s'), (ot', t')) \<in> uwr d"
  proof (cases i)
    case (IRead a)
    thus ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_running_def trace_units_obeying_set_def)
      apply (thin_tac "s' = _", thin_tac "t' = _")
      apply (intro conjI)
       (* pch *)
       apply (clarsimp simp: pch_same_for_domain_and_shared_def)
       apply (rule and_or_specific')
       apply (case_tac "snd a coll aa")
        (* colliding addresses *)
        apply (rule pch_collision_read [where pchs="pch s" and pcht="pch t" and a="snd a"]; clarsimp)
        apply (metis collision_in_full_collision_set collision_sym diff_domain_no_collision kernel_shared_expanded_full_collision_set)
       (* non-colliding addresses *)
       apply (metis pch_partitioned_read)
      (* time *)
      apply (metis (mono_tags, lifting) all_paddrs_of_def collision_set_contains_itself in_touched_addrs_expand kernel_shared_expanded_def mem_Collect_eq pch_same_for_domain_and_shared_def)
      done
  next
    case (IWrite a)
    thus ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_running_def trace_units_obeying_set_def)
      apply (thin_tac "s' = _", thin_tac "t' = _")
      apply (intro conjI)
       (* pch *)
       apply (clarsimp simp: pch_same_for_domain_and_shared_def)
       apply (rule and_or_specific')
       apply (case_tac "snd a coll aa")
        (* colliding addresses *)
        apply (rule pch_collision_write [where pchs="pch s" and pcht="pch t" and a="snd a"]; clarsimp)
        apply (metis collision_in_full_collision_set collision_sym diff_domain_no_collision kernel_shared_expanded_full_collision_set)        
       (* non-colliding addresses *)
       apply (metis pch_partitioned_write)
      (* time *)
      apply (metis (mono_tags, lifting) all_paddrs_of_def collision_set_contains_itself in_touched_addrs_expand kernel_shared_expanded_def mem_Collect_eq pch_same_for_domain_and_shared_def)
      done
  next
    case IFlushL1
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  next
    case (IFlushL2 fa)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_running_def pch_same_for_domain_and_shared_def
                            trace_units_obeying_set_def)
      apply (thin_tac "s' = _", thin_tac "t' = _") (* messy and not needed *)
      apply (prop_tac "\<forall>a1. (\<exists>a2\<in>fa. a1 coll a2) \<longrightarrow> pch_lookup (pch s) a1 = pch_lookup (pch t) a1")
       apply (smt all_paddrs_of_def collision_sym diff_domain_no_collision in_sub_union kernel_shared_expanded_def mem_Collect_eq touched_addrs_inv_def)
      apply (intro conjI)
       apply clarsimp
       apply (rule and_or_specific')
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
    case (IPadToTime x7)
    thus ?thesis using assms by (force simp:uwr_def uwr_running_def)
  qed

(* d running \<rightarrow> d running *)
lemma d_running: "\<lbrakk>
   p \<in> traces_obeying_ta os';
   touched_addrs_inv os';
   \<comment> \<open>initial states s and t hold uwr\<close>
   ((os, s), (ot, t)) \<in> uwr d;
   \<comment> \<open>external states hold external uwr\<close>
   (os', ot') \<in> external_uwr d;
   \<comment> \<open>NB: external_uwr should give us current_domain' t = d\<close>
   current_domain os = d;
   \<comment> \<open>we execute the program on both states\<close>
   s' = trace_multistep p s;
   t' = trace_multistep p t;
   \<comment> \<open>the external state's domain hasn't changed\<close>
   current_domain os' = current_domain os
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new states s' and t' hold uwr\<close>
   ((os', s'), (ot', t')) \<in> uwr d"
  apply(induct p arbitrary:s t os ot)
   apply (solves \<open>clarsimp simp:uwr_def\<close>)
  apply clarsimp
  apply(erule_tac x="trace_step a s" in meta_allE)
  apply(erule_tac x="trace_step a t" in meta_allE)
  apply(erule_tac x="os'" in meta_allE)
  apply(erule_tac x="ot'" in meta_allE)
  apply (prop_tac "current_domain ot' = current_domain ot")
   apply (metis external_uwr_same_domain uwr_external_uwr)
  apply(erule meta_impE)
   apply blast
  apply(erule meta_impE)
   apply (frule hd_trace_obeying_set, clarsimp)
   apply (erule(3) d_running_step; simp)
  apply simp
  done

\<comment> \<open>we prove this via an integrity step\<close>
lemma d_not_running_step:
  assumes
  "i \<in> trace_units_obeying_ta os'"
  "touched_addrs_inv os'"
  "current_domain os \<noteq> d"
  "s' = trace_step i s"
  "current_domain os' = current_domain os"
  shows
  "((os, s), (os, s')) \<in> uwr d"
  proof (cases i)
    case (IRead a)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def trace_units_obeying_set_def)
      apply (thin_tac "s' = _")
      apply (clarsimp simp:pch_same_for_domain_except_shared_def)
      apply (rule pch_partitioned_read)
      apply (clarsimp simp: touched_addrs_inv_def)
      apply (drule(1) in_image_union)
      apply (erule disjE)
       apply (clarsimp simp: all_paddrs_of_def)
       apply (metis collision_sym diff_domain_no_collision)
      using kernel_shared_expanded_def apply blast
      done
  next
    case (IWrite x2)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def trace_units_obeying_set_def)
      apply (thin_tac "s' = _")
      apply (clarsimp simp:pch_same_for_domain_except_shared_def)
      apply (rule pch_partitioned_write)
      apply (clarsimp simp: touched_addrs_inv_def)
      apply (drule(1) in_image_union)
      apply (erule disjE)
       apply (clarsimp simp: all_paddrs_of_def)
       apply (metis collision_sym diff_domain_no_collision)
      using kernel_shared_expanded_def apply blast
      done
  next
    case IFlushL1
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
  next
    case (IFlushL2 x5)
    then show ?thesis using assms
      apply (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def
                            trace_units_obeying_set_def)
      apply (rule sym, rule pch_partitioned_flush, clarsimp)
      apply(clarsimp simp:touched_addrs_inv_def all_paddrs_of_def)
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
    case (IPadToTime x7)
    then show ?thesis using assms
      by (clarsimp simp: uwr_def uwr_notrunning_def pch_same_for_domain_except_shared_def)
qed

lemma d_not_running_integrity_uwr:
  "\<lbrakk>p \<in> traces_obeying_ta os';
  touched_addrs_inv os';
  current_domain os \<noteq> d;
  current_domain os' = current_domain os
  \<rbrakk> \<Longrightarrow>
  ((os, s), (os, trace_multistep p s)) \<in> uwr d"
  apply (induct p arbitrary: s; clarsimp)
  apply (drule hd_trace_obeying_set, clarsimp)
  apply (drule_tac s'="trace_step a s" in d_not_running_step, simp+)
  apply (clarsimp simp:uwr_trans)
  done

(* d not running \<rightarrow> d not running *)
lemma d_not_running: "\<lbrakk>
   \<comment> \<open>we have two programs derived from touched_addresses - may not be the same touched_addresses\<close>
   ps \<in> traces_obeying_ta os';
   pt \<in> traces_obeying_ta ot';
   \<comment> \<open>these touched_addresses does NOT contain any addresses from d\<close>
   current_domain os \<noteq> d;
   current_domain os' = current_domain os;
   touched_addrs_inv os';
   touched_addrs_inv ot';
   \<comment> \<open>initial states s and t hold uwr\<close>
   ((os, s), (ot, t)) \<in> uwr d;
   (os', ot') \<in> external_uwr d;
   \<comment> \<open>we execute both programs\<close>
   s' = trace_multistep ps s;
   t' = trace_multistep pt t
   \<rbrakk> \<Longrightarrow>
   \<comment> \<open>new state s' and t' hold uwr_notrunning\<close>
   ((os', s'), (ot', t')) \<in> uwr d"
  apply (drule(3) d_not_running_integrity_uwr [where s=s and os=os])
  apply (drule(1) d_not_running_integrity_uwr [where s=t and os=ot and d=d])
    using external_uwr_same_domain uwr_external_uwr apply fastforce
   using external_uwr_same_domain uwr_external_uwr apply force
  apply (prop_tac "((os, trace_multistep ps s), ot, trace_multistep pt t) \<in> uwr d")
   apply (rule uwr_trans, rule uwr_sym', assumption)
   apply (rule uwr_trans, assumption, assumption)
  apply (simp add:uwr_def)
  done

(* --- notes for domainswitch step stuff ---- *)
(*

lemma dirty_step_u_1of3:
  assumes
    "i \<in> instrs_obeying_set os (all_paddrs_of u)"
    "((os, s), (ot, t)) \<in> uwr u"
    "(os', ot') \<in> external_uwr u"
    "s' = instr_step i os s"
    "t' = instr_step i ot t"
    "current_domain os = u"
  shows
    "((os, s'), (os, t')) \<in> uwr u"
  proof (cases i)
case (IRead x1)
  then show ?thesis using assms
   apply (clarsimp simp: instrs_obeying_set_def)
   apply (clarsimp simp: uwr_def uwr_running_def)
   apply (intro conjI)
    apply (clarsimp simp: pch_same_for_domain_and_shared_def)
    apply (prop_tac "v_to_p ot x1 = v_to_p os x1")
      subgoal sorry
    apply (intro conjI; clarsimp)
     apply (metis (mono_tags, lifting) collision_sym diff_domain_no_collision pch_collision_read pch_partitioned_read)
    apply (metis (no_types, lifting) external_uwr_current_page_table full_collision_set_def kernel_shared_expanded_full_collision_set pch_collision_read pch_partitioned_read)
   apply (simp add: all_paddrs_of_def external_uwr_current_page_table pch_same_for_domain_and_shared_def)
  done
  oops

(* one step of a dirty program holding uwr apart from time *)
lemma dirty_step_u:
  assumes
    (* "i \<in> trace_units_obeying_set os (all_paddrs_of u \<union> all_paddrs_of v \<union> kernel_shared_precise)" *)
    "((os, s), (ot, t)) \<in> uwr u"
    (* "(os', ot') \<in> external_uwr u" *)
    "s' = instr_step i os s"
    "t' = instr_step i ot t"
    "current_domain os = u"
  shows
    "((os, s'), (os, t'\<lparr>tm:=tm s'\<rparr>)) \<in> uwr u"
  proof (cases i)
  case (IRead a)
  then show ?thesis using assms
   apply (clarsimp simp: uwr_def uwr_running_def)
   apply (thin_tac "s' = _", thin_tac "t' = _")
   apply (prop_tac "v_to_p ot = v_to_p os")
    using external_uwr_current_page_table apply blast
  apply (clarsimp simp: pch_same_for_domain_and_shared_def)
  apply (intro conjI; clarsimp)
   apply (metis (no_types, lifting) collision_sym diff_domain_no_collision pch_collision_read pch_partitioned_read)
  apply (metis (no_types, lifting) full_collision_set_def kernel_shared_expanded_full_collision_set pch_collision_read pch_partitioned_read)
  done
next
  case (IWrite a)
  then show ?thesis using assms
   apply (clarsimp simp: uwr_def uwr_running_def)
   apply (thin_tac "s' = _", thin_tac "t' = _")
   apply (prop_tac "v_to_p ot = v_to_p os")
    using external_uwr_current_page_table apply blast
  apply (clarsimp simp: pch_same_for_domain_and_shared_def)
  apply (intro conjI; clarsimp)
   apply (rule pch_collision_write)
      defer
      
next
  case IFlushL1
  then show ?thesis sorry
next
  case (IFlushL2 x4)
  then show ?thesis sorry
next
  case (IPadToTime x5)
  then show ?thesis sorry
qed

lemma dirty_step:
  assumes
  "i \<in> instrs_obeying_set os (all_paddrs_of u \<union> all_paddrs_of v \<union> kernel_shared_precise)"
  "s' = instr_step i os s"
  shows
  "((os, s), (os, s')) \<in> uwr d"
  proof (cases i)
case (IRead x1)
  then show ?thesis using assms
   apply (clarsimp simp: instrs_obeying_set_def)
   next
     case (IWrite x2)
     then show ?thesis sorry
   next
     case IFlushL1
     then show ?thesis sorry
   next
     case (IFlushL2 x4)
     then show ?thesis sorry
   next
     case (IPadToTime x5)
  then show ?thesis sorry
qed

lemma dirty_domainswitch_semi_uwr: "\<lbrakk>
  correct_dirty_programs dtg;
  same_dirty_programs dtg;
  ((os, s), (ot, t)) \<in> uwr d;
  (os', ot') \<in> external_uwr d;
  ps = dtg u v os;
  pt = dtg u v ot;
  s' = instr_multistep ps os s;
  t' = instr_multistep pt ot t;
  True
  \<rbrakk> \<Longrightarrow>
  ((os', s'), (ot', t')) \<in> uwr d"
  apply (prop_tac "pt = ps")
   apply (metis external_uwr_Sched same_dirty_programs_def uwr_external_uwr)
  apply clarsimp
  apply (clarsimp simp:correct_dirty_programs_def)
  

lemma domainswitch_uwr: "\<lbrakk>
  correct_dirty_programs dtg;
  same_dirty_programs dtg;
  same_next_time ntg;
  ps = get_domain_switch_program dtg ntg u v os;
  pt = get_domain_switch_program dtg ntg u v ot;
  ((os, s), (ot, t)) \<in> uwr d;
  (os', ot') \<in> external_uwr d;
  s' = instr_multistep ps os s;
  t' = instr_multistep pt ot t;
  True
  \<rbrakk> \<Longrightarrow>
  ((os', s'), (ot', t')) \<in> uwr d"
  nitpick


*)







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

(*

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

*)

(* question:

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
   ta \<inter> all_paddrs_of d = {};
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
   ta\<^sub>s \<inter> all_paddrs_of d \<subseteq> kernel_shared_precise;
   ta\<^sub>t \<inter> all_paddrs_of d \<subseteq> kernel_shared_precise;
   (s, t) \<in> uwr d;
   current_domain' s \<noteq> d;
   \<comment> \<open>external_uwr should give us current_domain' t \<noteq> d\<close>do_read
   s' = instr_multistep (p\<^sub>s @ [IFlushL1, IPadToTime detTime]) s;
   t' = instr_multistep (p\<^sub>t @ [IFlushL1, IPadToTime detTime]) t;
   current_domain' s' = d
   \<comment> \<open>external_uwr should oblige us to prove current_domain' t' = d\<close>
   \<rbrakk> \<Longrightarrow>
   (s', t') \<in> uwr d"
  oops
*)




(* not sure if we need this any more.
   if it's just combining running and not_running, it could be useful.
   will leave it here for now. -scott

lemma programs_obeying_ta_preserve_uwr: "\<lbrakk>
   \<not> will_domain_switch (other_state s);
   \<not> will_domain_switch (other_state t);
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
 *)
end


(* give me:
   - a domain extractor
   - an unwinding relation
   - a state
   - a set of trace
   - a default trace
   and i'll give you a trace. i only use information inside the uwr to decide which trace
   to choose, and i will always choose from the given set of traces. However, the default
   trace must be in the set of traces given by get_ps *)
axiomatization
  SelectTrace :: "('s \<Rightarrow> 'd) \<Rightarrow>('d \<Rightarrow> ('s \<times> 's) set) \<Rightarrow> ('s \<Rightarrow> 'p set) \<Rightarrow> 's \<Rightarrow> 'p \<Rightarrow> 'p"
where
  trace_uwr_determined : "(s, t) \<in> uwr (cdom s) \<Longrightarrow>
                            SelectTrace cdom uwr get_ps s p0 = SelectTrace cdom uwr get_ps t p0"
and
  trace_from_set : "p0 \<in> get_ps s \<Longrightarrow> SelectTrace cdom uwr get_ps s p0 \<in> get_ps s"


locale time_protection_system =
  ab: unwinding_system A s0 "\<lambda>_. current_domain" external_uwr policy out Sched +
  tp?: time_protection collides_in_pch fch_lookup pch_lookup
    fch_read_impact pch_read_impact fch_write_impact pch_write_impact
    read_cycles write_cycles empty_fch fch_flush_cycles do_pch_flush pch_flush_cycles
    addr_domain addr_colour colour_userdomain current_domain external_uwr
    touched_addrs will_domain_switch
  for A :: "('a,'other_state,unit) data_type"
  and s0 :: "'other_state"
  and current_domain :: "'other_state \<Rightarrow> 'userdomain domain"
  and external_uwr :: "'userdomain domain \<Rightarrow> ('other_state \<times> 'other_state) set"
  and policy :: "('userdomain domain \<times> 'userdomain domain) set"
  and out :: "'userdomain domain \<Rightarrow> 'other_state \<Rightarrow> 'p"
  and collides_in_pch :: "paddr \<Rightarrow> paddr \<Rightarrow> bool"
  and fch_lookup :: "'fch \<Rightarrow> 'fch_cachedness fch"
  and pch_lookup :: "'pch \<Rightarrow> 'pch_cachedness pch"
  and fch_read_impact :: "'fch fch_impact"
  and pch_read_impact :: "'pch pch_impact"
  and fch_write_impact :: "'fch fch_impact"
  and pch_write_impact :: "'pch pch_impact"
  and read_cycles  :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and write_cycles :: "'fch_cachedness \<Rightarrow> 'pch_cachedness \<Rightarrow> time"
  and empty_fch :: "'fch"
  and fch_flush_cycles :: "'fch \<Rightarrow> time"
  and do_pch_flush :: "'pch \<Rightarrow> paddr set \<Rightarrow> 'pch"
  and pch_flush_cycles :: "'pch \<Rightarrow> paddr set \<Rightarrow> time"
  and addr_domain :: "paddr \<Rightarrow> 'userdomain domain"
  and addr_colour :: "paddr \<Rightarrow> 'colour"
  and colour_userdomain :: "'colour \<Rightarrow> 'userdomain"
  and v_to_p :: "'other_state \<Rightarrow> vaddr \<Rightarrow> paddr"
  and touched_addrs :: "'other_state \<Rightarrow> vpaddr set"
  and will_domain_switch :: "'other_state \<Rightarrow> bool" +
  fixes initial_pch :: "'pch"
  fixes choose_next_domain :: "'userdomain domain \<Rightarrow> 'userdomain domain"
  assumes reachable_touched_addrs_inv:
    "ab.reachable s \<Longrightarrow> touched_addrs_inv s"
  \<comment> \<open> we need to know that for any non-domainswitch step, touched_addresses
       will not be empty at the end of the step. otherwise, we can't derive
       a trace. \<close>
  assumes touched_addrs_not_empty:
    "(s, s') \<in> ab.Step () \<Longrightarrow>
     \<not>will_domain_switch s \<Longrightarrow>
     touched_addrs s' \<noteq> {}"
  assumes simple_steps:
    "(s, s') \<in> ab.Step () \<Longrightarrow>
    (\<not>will_domain_switch s \<and> current_domain s' = current_domain s)
    \<or> (will_domain_switch s \<and> current_domain s' = choose_next_domain (current_domain s))"
begin

(* this is an axiomatised selector that gets one program from a set.
  it is not defined which program will be selected. *)
abbreviation selectTrace :: "'other_state \<Rightarrow> trace"
  where
  "selectTrace s \<equiv> SelectTrace current_domain external_uwr traces_obeying_ta s []::trace"

lemma trace_from_ta:
  "selectTrace s \<in> traces_obeying_ta s"
  apply (rule trace_from_set)
  apply (clarsimp simp:traces_obeying_set_def)
  done

(* this used to be called A_extened_Step *)
definition maStep :: "unit \<Rightarrow>
  (('other_state\<times>('fch, 'pch)state) \<times> ('other_state\<times>('fch, 'pch)state)) set"
  where
  "maStep _ \<equiv> {((os, s), (os', s')) | os os' s s' p.
              (os, os') \<in> ab.Step () \<and>
               ((\<not>will_domain_switch os
                 \<and> p = selectTrace os'
                 \<and> s' = trace_multistep p s ) \<comment> \<open>TA step\<close>
               \<or> (will_domain_switch os
                 \<and> True \<comment> \<open>this needs to be something like is_domainswitch_gadget p \<close>
                 \<and> s' = trace_multistep p s ) \<comment> \<open>gadget step\<close>
              )}"

definition maA :: "(('other_state\<times>('fch, 'pch)state), ('other_state\<times>('fch, 'pch)state), unit) data_type" where
  "maA \<equiv> \<lparr> Init = \<lambda>s. {s}, Fin = id, Step = maStep \<rparr>"

(* instead of A_extended_state *)
definition mas0 :: "'other_state\<times>('fch, 'pch)state" where
  "mas0 \<equiv> (s0, \<lparr> fch=empty_fch, pch=initial_pch, tm=0 \<rparr>)"

interpretation ma?:Init_inv_Fin_system maA mas0
  apply unfold_locales
    (* Init_Fin_system.Fin_Init_s0 *)
    apply(force simp:maA_def mas0_def)
   (* Init_Fin_system.Init_inv_Fin *)
   apply(force simp:maA_def)
  (* Init_Fin_system.Fin_inj *)
  apply(force simp:maA_def)
  done

lemma ma_to_ab_step:
  "((os, s), (os', s')) \<in> ma.Step () \<Longrightarrow>
   (os, os') \<in> ab.Step ()"
  apply (clarsimp simp: ma.Step_def execution_def maA_def system.Step_def steps_def maStep_def)
  done

lemma ma_to_ab_run:
  "((os, s), (os', s')) \<in> Run ma.Step as \<Longrightarrow>
   (os, os') \<in> Run ab.Step as"
  apply(induct as arbitrary:s os, solves \<open>simp\<close>)
  apply clarsimp
  apply(erule_tac x=ba in meta_allE)
  apply(erule_tac x=aa in meta_allE)
  apply (drule ma_to_ab_step)
  apply clarsimp
  by blast

lemma ma_to_ab_reachable:
  "ma.reachable (os, s) \<Longrightarrow> ab.reachable os"
  apply(rule ab.Run_reachable)
  apply(drule ma.reachable_Run, clarsimp)
  apply(rule_tac x=as in exI)
  apply (clarsimp simp:mas0_def)
  using ma_to_ab_run apply blast
  done

lemma ma_to_ab_reachable':
  "ma.reachable s \<Longrightarrow> ab.reachable (fst s)"
  apply (cases s, clarsimp simp:ma_to_ab_reachable)
  done

lemma ma_single_step_enabled:
  "ab.reachable os \<Longrightarrow>
   \<exists>s' os'. ((os, s), os', s') \<in> {(s, s'). s' \<in> steps maStep {s} [()]} \<and> ab.reachable os'"
  apply (clarsimp simp: steps_def maStep_def)
  apply (cases "will_domain_switch os"; clarsimp)
  using ab.enabled_Step ab.reachable_Step apply fastforce
  using ab.enabled_Step ab.reachable_Step apply blast
done

lemma ma_execution_enabledness:
  "ab.reachable os \<Longrightarrow>
   ma.reachable (os, s) \<Longrightarrow>
   \<exists>s' os'. (os', s') \<in> execution maA (os, s) js"
  apply (subst ma.execution_Run [OF _], simp)
  apply (thin_tac "ma.reachable _")
  apply (induct js arbitrary:os s)
   apply (clarsimp simp: execution_def steps_def maA_def)
  apply clarsimp
  apply (clarsimp simp:ma.Step_def execution_def maA_def maStep_def system.Step_def)
  apply (simp only:maA_def [symmetric])
  using ma_single_step_enabled apply (meson relcomp.relcompI)
  done

(* note: we're given an 'out' in time_protection_system, and here we just adjust it to look at
   the other_state part of the new ma state *)
interpretation ma: unwinding_system maA mas0 "\<lambda>_ s. current_domain (fst s)" uwr policy "\<lambda>d s. out d (fst s)" Sched
  apply unfold_locales
      (* enabled_system.enabled *)
      apply(simp only:system.reachable_def[symmetric])
      apply (frule ma_to_ab_reachable')
      apply (simp only:ab.reachable_def)
      apply (frule_tac js=js in ab.enabled)
      apply (frule ma_to_ab_reachable')
      using ma_execution_enabledness apply fastforce 
     (* noninterference_policy.uwr_equiv_rel *)
     using uwr_equiv_rel apply blast
    (* noninterference_policy.schedIncludesCurrentDom *)
    using external_uwr_same_domain uwr_external_uwr apply fastforce
   (* noninterference_policy.schedFlowsToAll *)
   using ab.schedFlowsToAll apply blast
  (* noninterference_policy.schedNotGlobalChannel *)
  using ab.schedNotGlobalChannel apply blast
  done

lemma ma_confidentiality_u_ta:
  "\<lbrakk>\<not>will_domain_switch os;
  touched_addrs_inv os';
  touched_addrs_inv ot';
  ma.uwr2 (os, s) u (ot, t);
  ab.uwr2 os' u ot';
  ((os, s), os', s') \<in> maStep ();
  ((ot, t), ot', t') \<in> maStep ()\<rbrakk>
  \<Longrightarrow> ma.uwr2 (os', s') u (ot', t')"
  apply (frule uwr_external_uwr)
  apply (frule will_domain_switch_public [where os=os])
  apply (clarsimp simp:maStep_def)

  (* show that the domain hasn't changed *)
  apply (frule simple_steps [where s=os]; clarsimp)
  apply (frule simple_steps [where s=ot]; clarsimp)

  (* show that the programs obey the TAs *)
  apply (prop_tac "selectTrace os' \<in> traces_obeying_ta os'
                 \<and> selectTrace ot' \<in> traces_obeying_ta ot'")
   apply (intro conjI; rule trace_from_ta)
  apply clarsimp

  apply (case_tac "current_domain os = u")
   (* u is executing *)
   apply (prop_tac "selectTrace ot' = selectTrace os'")
    apply (subst eq_sym_conv)
    apply (rule trace_uwr_determined, simp)
   apply (erule(2) d_running, simp+)
  (* u is not executing *)
  apply (rule d_not_running [where os=os and ot=ot], simp+)
  done

theorem ma_confidentiality_u:
  "ab.confidentiality_u \<Longrightarrow> ma.confidentiality_u"
  apply(clarsimp simp:ma.confidentiality_u_def)
  apply (rename_tac u os s ot t os' s' ot' t')

  apply (prop_tac "ab.uwr2 os' u ot'")
   apply (simp only:ab.confidentiality_u_def)
   apply (meson ma_to_ab_reachable ma_to_ab_step uwr_external_uwr)
  
  apply (drule(1) ma.reachable_Step)+

  apply (frule_tac os=os' in ma_to_ab_reachable)
  apply (frule_tac os=ot' in ma_to_ab_reachable)
  apply (drule reachable_touched_addrs_inv)+
  
  apply (thin_tac "_ \<longrightarrow> _")
  apply (thin_tac "ma.uwr2 _ Sched _")

  (* let's get this all in terms of maStep *)
  apply (clarsimp simp:ma.Step_def execution_def steps_def maA_def system.Step_def)
  apply (simp only:maA_def [symmetric])

  apply (case_tac "will_domain_switch os")
   defer
   apply (erule ma_confidentiality_u_ta; simp)

  

  apply(frule will_domain_switch_public)
  apply(case_tac "will_domain_switch (other_state s)")
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