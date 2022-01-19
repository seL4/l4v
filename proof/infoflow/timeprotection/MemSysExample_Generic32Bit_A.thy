(*
 * Copyright 2021, The University of Melbourne (ABN 84 002 705 224)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory MemSysExample_Generic32Bit_A
imports TimeProtection
begin

(* Generic 32-bit example memory system A:
  - L1-D (write-through)
  - L2 (write-back) *)

(* As for now we just need something generic to test-instantiate our locale to completion,
   these numbers are plucked from thin air for a hypothetical memory system whose L2 cache
   supports 4 colours given a page size of 4KiB.

   L1:
   4 index bits \<Rightarrow> 2^4 = 16 cache sets.
   6 block offset bits \<Rightarrow> 2^6 bytes = 64 bytes per cache block.
   - If it was 4-way set associative, it would have 16 * 4 = 64 cache blocks,
     making a total cache size of 64 * 64 = 4096 bytes (i.e. 4 KiB).
   - If direct mapped, it would have 16 cache blocks and thus be 16 * 64 bytes = 1 KiB large.
   (NOT TO SCALE)
   | tag (22 bits)  ...                  |index(4bit)|    block offset    |
   |31                                 10|9         6|5                  0|

   L2:
   4KiB page size = 4096 bytes = 2^12 bytes per page \<Rightarrow> 12 page offset bits.
   6 index bits \<Rightarrow> 2^6 = 64 cache sets.
   8 block offset bits \<Rightarrow> 2^8 bytes = 256 bytes per cache block.
   - If it was 8-way set associative, it would have 64 * 8 = 512 cache blocks,
     making a total cache size of 512 * 256 = 131072 bytes (i.e. 128 KiB).
   - If direct mapped, it would have 64 cache blocks and thus be 64 * 256 bytes = 16 KiB large.
   (NOT TO SCALE)
   |31              ...        12|11                                     0|
   | page (20 bits) ...          |              page offset               |
                        | colour |
                        | (2bit) |
   | tag (18 bits)  ... |     index (6bit)    |       block offset        |
   |31                14|13                  8|7                         0|
*)
(* Note: There should be "x" mask bits for an "x word" type, and the offset
   should match the number of zeroes to the right of the mask. *)
type_synonym L1_tag_A = "22 word"
definition L1_tag_mask :: machine_word where "L1_tag_mask = 0b11111111111111111111110000000000"
definition L1_tag_offset :: nat where "L1_tag_offset = 10"
type_synonym L1_index_A = "4 word"
definition L1_index_mask :: machine_word where "L1_index_mask = 0b1111000000"
definition L1_index_offset :: nat where "L1_index_offset = 6"
type_synonym L2_tag_A = "18 word"
definition L2_tag_mask :: machine_word where "L2_tag_mask = 0b11111111111111111100000000000000"
definition L2_tag_offset :: nat where "L2_tag_offset = 14"
type_synonym L2_index_A = "6 word"
definition L2_index_mask :: machine_word where "L2_index_mask = 0b11111100000000"
definition L2_index_offset :: nat where "L2_index_offset = 8"
type_synonym colour_A = "2 word"
definition colour_mask :: machine_word where "colour_mask = 0b11000000000000"
definition colour_offset :: nat where "colour_offset = 12"

definition L1_tag_of :: "vaddr \<Rightarrow> L1_tag_A" where
  "L1_tag_of a' \<equiv> case a' of VAddr a \<Rightarrow> ucast ((a AND L1_tag_mask) >> L1_tag_offset)"
definition L1_index_of :: "vaddr \<Rightarrow> L1_index_A" where
  "L1_index_of a' \<equiv> case a' of VAddr a \<Rightarrow> ucast ((a AND L1_index_mask) >> L1_index_offset)"
definition L2_tag_of :: "paddr \<Rightarrow> L2_tag_A" where
  "L2_tag_of a' \<equiv> case a' of PAddr a \<Rightarrow> ucast ((a AND L2_tag_mask) >> L2_tag_offset)"
definition L2_index_of :: "paddr \<Rightarrow> L2_index_A" where
  "L2_index_of a' \<equiv> case a' of PAddr a \<Rightarrow> ucast ((a AND L2_index_mask) >> L2_index_offset)"
definition colour_of :: "paddr \<Rightarrow> colour_A" where
  "colour_of a' \<equiv> case a' of PAddr a \<Rightarrow> ucast ((a AND colour_mask) >> colour_offset)"

(* So it just takes a `simp` to get rid of the constructor case-split *)
declare paddr.splits [split]
declare vaddr.splits [split]

(* Some more made-up numbers. *)
definition L1_fetch_cycles :: nat where "L1_fetch_cycles = 2"
definition L2_fetch_cycles :: nat where "L2_fetch_cycles = 8"
definition Mem_fetch_cycles :: nat where "Mem_fetch_cycles = 200"
definition Default_cycle :: nat where "Default_cycle = 1"

(* In this system let's choose to have the max number of user domains possible on the hardware
   - that is, as many as there are colours. -robs. *)
type_synonym userdomain_A = colour_A
abbreviation addr_colour_A :: "paddr \<Rightarrow> colour_A" where "addr_colour_A \<equiv> colour_of"
abbreviation colour_userdomain_A :: "colour_A \<Rightarrow> userdomain_A" where "colour_userdomain_A \<equiv> id"

datatype sys_mode = KEntry | KSchedule | KExit

record orig_state_A =
  mem :: "paddr \<Rightarrow> machine_word"
  curdom :: "userdomain_A domain"
  taddrs :: "vaddr set"

type_synonym other_state_A = "orig_state_A \<times> sys_mode"

record regs_A =
  r0 :: "machine_word"

definition collides_in_pch_A :: "paddr rel" where
  "collides_in_pch_A = {(a, a'). L2_index_of a = L2_index_of a'}"

lemma collides_with_equiv_A: "equiv UNIV collides_in_pch_A"
  unfolding collides_in_pch_A_def equiv_def
  apply(rule conjI)
   unfolding refl_on_def apply blast
  apply(rule conjI)
   unfolding sym_def apply force
  unfolding trans_def by force

(* As our cache impact model is not distinguishing yet between I-cache and D-cache nor counting
   timing impacts of instruction fetching itself, let's say fch is just the L1-D.
   Also a big TODO here still is to distinguish between virtual and physical addresses. *)

datatype writethru_cachedness = WT_Absent | WT_Valid
datatype writeback_cachedness = WB_Absent | WB_Valid | WB_DirtyValid

type_synonym fch_cachedness_A = writethru_cachedness
type_synonym pch_cachedness_A = writeback_cachedness

(* Let's keep things simple and go with direct mapped for both caches to begin with.
  Later we should convince ourselves we can model n-way set associative caches; this should amount
  to keeping for each index a set/queue (depending on replacement algorithm) of max size n tags. *)
type_synonym fch_A = "L1_index_A \<Rightarrow> L1_tag_A option"
(* As the L2 for this example is writeback, we need a bool here to serve as a dirty bit. *)
type_synonym pch_A = "L2_index_A \<Rightarrow> (L2_tag_A \<times> bool) option"

definition fch_lookup_A :: "fch_A \<Rightarrow> fch_cachedness_A fch" where
  "fch_lookup_A f a \<equiv> if f (L1_index_of a) = Some (L1_tag_of a) then WT_Valid else WT_Absent"

definition pch_lookup_A :: "pch_A \<Rightarrow> pch_cachedness_A pch" where
  "pch_lookup_A p a \<equiv> case p (L2_index_of a) of
     Some (tag, dirty) \<Rightarrow>
       if tag = L2_tag_of a then (if dirty then WB_DirtyValid else WB_Valid) else WB_Absent |
     None \<Rightarrow> WB_Absent"

(* Read and write have the same impact on the fch. *)
definition fch_access_impact_A :: "fch_A fch_impact" where
  "fch_access_impact_A a f = f(L1_index_of a := Some (L1_tag_of a))"

(* In this case the L1 is writethrough, so we don't need to consult it.
  If it were writeback, we would have to check the dirty bit of any block evicted from it
  to propagate it to the L2 if it is set. *)
definition pch_read_impact_A :: "pch_A pch_impact" where
  "pch_read_impact_A a p \<equiv>
     if \<exists> dirty. p (L2_index_of a) = Some (L2_tag_of a, dirty)
       then p
       else p(L2_index_of a := Some (L2_tag_of a, False))"

lemma pch_partitioned_read_A:
  "(a1, a2) \<notin> collides_in_pch_A \<Longrightarrow> pch_lookup_A p a2 = pch_lookup_A (pch_read_impact_A a1 p) a2"
  unfolding collides_in_pch_A_def pch_lookup_A_def pch_read_impact_A_def
  by auto

lemma pch_collision_read_A:
  assumes
    a2_evicts_a1: "(a1, a2) \<in> collides_in_pch_A" and
    set_lookup_eq:
      "\<forall>a3. (a2, a3) \<in> collides_in_pch_A \<longrightarrow> pch_lookup_A pchs a3 = pch_lookup_A pcht a3"
  shows
    "pch_lookup_A (pch_read_impact_A a1 pchs) a2 = pch_lookup_A (pch_read_impact_A a1 pcht) a2"
  proof -
    have "pch_lookup_A pchs a1 = pch_lookup_A pcht a1 \<and>
          pch_lookup_A pchs a2 = pch_lookup_A pcht a2"
      using a2_evicts_a1 set_lookup_eq unfolding collides_in_pch_A_def
      by force
    thus ?thesis unfolding pch_read_impact_A_def pch_lookup_A_def
      by (force split:option.splits if_splits)
qed

(* As the L1 is writethrough, we always set the block's dirty bit in the L2 immediately. *)
definition pch_write_impact_A :: "pch_A pch_impact" where
  "pch_write_impact_A a p \<equiv> p(L2_index_of a := Some (L2_tag_of a, True))"

lemma pch_partitioned_write_A:
  "(a1, a2) \<notin> collides_in_pch_A \<Longrightarrow> pch_lookup_A p a2 = pch_lookup_A (pch_write_impact_A a1 p) a2"
  unfolding collides_in_pch_A_def pch_lookup_A_def pch_write_impact_A_def
  by auto

lemma pch_collision_write_A:
  assumes
    a2_evicts_a1: "(a1, a2) \<in> collides_in_pch_A" and
    set_lookup_eq:
      "\<forall>a3. (a2, a3) \<in> collides_in_pch_A \<longrightarrow> pch_lookup_A pchs a3 = pch_lookup_A pcht a3"
  shows
    "pch_lookup_A (pch_write_impact_A a1 pchs) a2 = pch_lookup_A (pch_write_impact_A a1 pcht) a2"
  proof -
    have "pch_lookup_A pchs a1 = pch_lookup_A pcht a1 \<and>
          pch_lookup_A pchs a2 = pch_lookup_A pcht a2"
      using a2_evicts_a1 set_lookup_eq unfolding collides_in_pch_A_def
      by force
    thus ?thesis unfolding pch_write_impact_A_def pch_lookup_A_def
      by (force split:option.splits if_splits)
qed

definition read_cycles_A :: "fch_cachedness_A \<Rightarrow> pch_cachedness_A \<Rightarrow> time" where
  "read_cycles_A in_f in_p \<equiv> case in_f of
     WT_Valid \<Rightarrow> L1_fetch_cycles |
     WT_Absent \<Rightarrow> (case in_p of WB_Absent \<Rightarrow> Mem_fetch_cycles | _ \<Rightarrow> L2_fetch_cycles)"

definition write_cycles_A :: "fch_cachedness_A \<Rightarrow> pch_cachedness_A \<Rightarrow> time" where
  "write_cycles_A _ _ = Default_cycle"

definition v_to_p_A :: "other_state_A \<Rightarrow> vaddr \<Rightarrow> paddr" where
  "v_to_p_A s v \<equiv> case v of VAddr a \<Rightarrow> PAddr a" (* id just to get the types to line up first *)

definition do_read_A :: "vaddr \<Rightarrow> other_state_A \<Rightarrow> regs_A \<Rightarrow> regs_A" where
  "do_read_A a s _ = \<lparr> r0 = mem (fst s) (v_to_p_A s a) \<rparr>"

definition do_write_A :: "vaddr \<Rightarrow> other_state_A \<Rightarrow> regs_A \<Rightarrow> other_state_A" where
  "do_write_A a s rs = ((fst s)\<lparr> mem := (mem (fst s))(v_to_p_A s a := r0 rs) \<rparr>, snd s)"

definition store_time_A :: "time \<Rightarrow> regs_A \<Rightarrow> regs_A" where
  "store_time_A t r = \<lparr> r0 = of_nat t \<rparr>"

(* The IPadToTime is a bit of an abstraction... Presumably in reality we would do this by invoking
  IReadTime/IRegs repeatedly (busy wait until the time equals a value IRead earlier from memory)
  for a sufficient number of steps. Just say there's a primitive that's no-op on regs for now. *)
definition padding_regs_impact_A :: "time \<Rightarrow> regs_A \<Rightarrow> regs_A" where
  "padding_regs_impact_A t r = r"

definition empty_fch_A :: fch_A where
  "empty_fch_A idx = None"

(* Let's just say there's a primitive for it that will do it in 1 cycle. *)
definition fch_flush_cycles_A:: "fch_A \<Rightarrow> time" where
  "fch_flush_cycles_A _ = Default_cycle"

definition L2_indices_of :: "paddr set \<Rightarrow> L2_index_A set" where
  "L2_indices_of as \<equiv> {idx. \<exists> a. L2_index_of a = idx \<and> a \<in> as}"

definition do_pch_flush_A :: "pch_A \<Rightarrow> paddr set \<Rightarrow> pch_A" where
  "do_pch_flush_A p as \<equiv> \<lambda> idx. if idx \<in> L2_indices_of as then None else p idx"

(* Let's say the flush time is proportional to the number of sets we're asking to be flushed
   -- to begin with, *not* sensitive to the current cachedness status of those sets.
   We may later want to try this for manual flushing schemes whose timing might depend on
   whether each index has an entry loaded in the cache or not, whether it is dirty, etc. *)
definition pch_flush_cycles_A :: "pch_A \<Rightarrow> paddr set \<Rightarrow> time" where
  "pch_flush_cycles_A p as = Default_cycle + length (sorted_list_of_set (L2_indices_of as))"

lemma pch_partitioned_flush_A:
  "\<forall>a'\<in>as. (a, a') \<notin> collides_in_pch_A \<Longrightarrow> pch_lookup_A (do_pch_flush_A p as) a = pch_lookup_A p a"
  unfolding collides_in_pch_A_def pch_lookup_A_def do_pch_flush_A_def L2_indices_of_def
  by (auto split:option.splits if_splits)

lemma pch_collision_flush_A:
  "\<exists>a1\<in>as. (a, a1) \<in> collides_in_pch_A \<Longrightarrow>
   \<forall>a1. (\<exists>a2\<in>as. (a1, a2) \<in> collides_in_pch_A) \<longrightarrow> pch_lookup_A pchs a1 = pch_lookup_A pcht a1 \<Longrightarrow>
   pch_lookup_A (do_pch_flush_A pchs as) a = pch_lookup_A (do_pch_flush_A pcht as) a"
  unfolding pch_lookup_A_def do_pch_flush_A_def
  by simp

lemma pch_flush_cycles_localised_A:
  assumes
    (* For all addresses a1 that collide with some address a2 in as,
       the lookup status of a1 is the same in s and t. *)
    "\<forall>a1. (\<exists>a2\<in>as. (a1, a2) \<in> collides_in_pch_A) \<longrightarrow> pch_lookup_A pchs a1 = pch_lookup_A pcht a1"
  shows
    (* A flush of the `as` set will take equal time in s and t *)
    "pch_flush_cycles_A pchs as = pch_flush_cycles_A pcht as"
  (* By this flush_cycles definition, we don't need the assumption after all. *)
  by (clarsimp simp:pch_flush_cycles_A_def)

definition addr_domain_A :: "paddr \<Rightarrow> userdomain_A domain" where
  "addr_domain_A a = User (colour_userdomain_A (addr_colour_A a))"

lemma same_index_same_colour:
  "L2_index_of a = L2_index_of b \<Longrightarrow> colour_of a = colour_of b"
  unfolding L2_index_of_def colour_of_def
    L2_index_mask_def L2_index_offset_def colour_mask_def colour_offset_def
  apply simp
  by (word_bitwise, simp)

lemma no_cross_colour_collisions_A:
  "(a1, a2) \<in> collides_in_pch_A \<Longrightarrow> addr_colour_A a1 = addr_colour_A a2"
  unfolding collides_in_pch_A_def
  using same_index_same_colour by blast

lemma addr_domain_valid_A:
  "addr_domain_A a = Sched \<or> addr_domain_A a = User (colour_userdomain_A (addr_colour_A a))"
  unfolding addr_domain_A_def
  by force

definition current_domain_A :: "other_state_A \<Rightarrow> userdomain_A domain" where
  "current_domain_A s = curdom (fst s)"

abbreviation orig_uwr_A :: "userdomain_A domain \<Rightarrow> (orig_state_A \<times> orig_state_A) set" where
  "orig_uwr_A d \<equiv> {(s, t). curdom s = curdom t \<and>
     (\<forall> a. addr_domain_A a = d \<longrightarrow> mem s a = mem t a) \<and>
     \<comment> \<open>Simplifying assumption: everybody's uwr includes the Scheduler uwr \<close>
     (\<forall> a. addr_domain_A a = Sched \<longrightarrow> mem s a = mem t a) \<and>
     (curdom s = d \<longrightarrow> taddrs s = taddrs t)}"

definition external_uwr_A :: "userdomain_A domain \<Rightarrow> (other_state_A \<times> other_state_A) set" where
  "external_uwr_A d \<equiv> {(s, t). snd s = snd t \<and> (fst s, fst t) \<in> orig_uwr_A d}"

lemma external_uwr_equiv_rel_A:
  "equiv UNIV (external_uwr_A d)"
  unfolding external_uwr_A_def equiv_def
  apply(rule conjI)
   unfolding refl_on_def apply blast
  apply(rule conjI)
   unfolding sym_def apply force
  unfolding trans_def by force

lemma external_uwr_same_domain_A:
  "(s1, s2) \<in> external_uwr_A d \<Longrightarrow> current_domain_A s1 = current_domain_A s2"
  unfolding external_uwr_A_def current_domain_A_def by blast

lemma page_table_not_in_mem_A:
  "\<And>a s r. v_to_p_A (do_write_A a s r) = v_to_p_A s"
  unfolding v_to_p_A_def do_write_A_def
  by blast

lemma external_uwr_current_page_table_A:
  "(s1, s2) \<in> external_uwr_A d \<Longrightarrow> current_domain_A s1 = d \<Longrightarrow> v_to_p_A s1 = v_to_p_A s2"
  unfolding external_uwr_A_def current_domain_A_def v_to_p_A_def
  by blast

lemma do_write_maintains_external_uwr_out_A:
  "addr_domain_A (v_to_p_A s a) \<noteq> d \<and> addr_domain_A (v_to_p_A s a) \<noteq> Sched \<Longrightarrow>
   (s, do_write_A a s r) \<in> external_uwr_A d"
  unfolding do_write_A_def external_uwr_A_def
  by force

lemma do_write_maintains_external_uwr_in_A:
  "addr_domain_A (v_to_p_A s a) = d \<or> addr_domain_A (v_to_p_A s a) = Sched \<Longrightarrow>
   (s, t) \<in> external_uwr_A d \<Longrightarrow>
   (do_write_A a s r, do_write_A a t r) \<in> external_uwr_A d"
  unfolding do_write_A_def external_uwr_A_def v_to_p_A_def
  by force

lemma do_write_outside_kernelshared_same_domain_A:
  assumes "addr_domain_A (v_to_p_A s a) \<noteq> Sched"
  shows "current_domain_A (do_write_A a s r) = current_domain_A s"
  (* Note: We didn't need the assumption *)
  unfolding current_domain_A_def do_write_A_def
  by force

lemma do_read_from_external_uwr_domain_A:
  "\<lbrakk>(s, t) \<in> external_uwr_A d;
   addr_domain_A (v_to_p_A s a) = d \<rbrakk> \<Longrightarrow>
   do_read_A a s r = do_read_A a t r"
  unfolding external_uwr_A_def do_read_A_def v_to_p_A_def
  by force

lemma do_read_from_external_uwr_sched_A:
  "\<lbrakk>(s, t) \<in> external_uwr_A d;
   addr_domain_A (v_to_p_A s a) = Sched \<rbrakk> \<Longrightarrow>
   do_read_A a s r = do_read_A a t r"
  unfolding external_uwr_A_def do_read_A_def v_to_p_A_def
  by force

definition touched_addrs_A :: "other_state_A \<Rightarrow> vaddr set" where
  "touched_addrs_A s = taddrs (fst s)"

lemma external_uwr_same_touched_addrs_A:
  "(s1, s2) \<in> external_uwr_A d \<Longrightarrow> current_domain_A s1 = d \<Longrightarrow>
   touched_addrs_A s1 = touched_addrs_A s2"
  unfolding external_uwr_A_def current_domain_A_def touched_addrs_A_def
  by blast

lemma touched_addrs_not_in_mem_A:
  "\<And>a s r. touched_addrs_A (do_write_A a s r) = touched_addrs_A s"
  unfolding touched_addrs_A_def do_write_A_def
  by force
 
definition do_add_to_TA_A :: "other_state_A \<Rightarrow> vaddr set \<Rightarrow> other_state_A" where
  "do_add_to_TA_A s vas \<equiv> (fst s \<lparr> taddrs := taddrs (fst s) \<union> vas \<rparr>, snd s)"

lemma do_add_to_TA_correct_A:
  "\<And>s vas. touched_addrs_A (do_add_to_TA_A s vas) = touched_addrs_A s \<union> vas"
  "\<And>s vas. current_domain_A (do_add_to_TA_A s vas) = current_domain_A s"
  "\<And>s vas. v_to_p_A (do_add_to_TA_A s vas) = v_to_p_A s"
  apply -
    unfolding touched_addrs_A_def do_add_to_TA_A_def
    apply force
   unfolding current_domain_A_def
   apply force
  unfolding v_to_p_A_def
  by blast

lemma do_add_to_TA_maintains_external_uwr_in_A:
  "\<And>s t d vas.
     (s, t) \<in> external_uwr_A d \<Longrightarrow>
     current_domain_A s = d \<Longrightarrow>
     (do_add_to_TA_A s vas, do_add_to_TA_A t vas) \<in> external_uwr_A d"
  unfolding external_uwr_A_def current_domain_A_def do_add_to_TA_A_def
  by force

lemma do_add_to_TA_maintains_external_uwr_out_A:
  "\<And>s vas.
     current_domain_A s \<noteq> d \<Longrightarrow>
     (s, do_add_to_TA_A s vas) \<in> external_uwr_A d"
  unfolding external_uwr_A_def current_domain_A_def do_add_to_TA_A_def
  by force

definition do_empty_TA_A :: "other_state_A \<Rightarrow> other_state_A" where
  "do_empty_TA_A s \<equiv> (fst s \<lparr> taddrs := {} \<rparr>, snd s)"

lemma do_empty_TA_correct_A:
  "\<And>s. touched_addrs_A (do_empty_TA_A s) = {}"
  "\<And>s. current_domain_A (do_empty_TA_A s) = current_domain_A s"
  "\<And>s. v_to_p_A (do_empty_TA_A s) = v_to_p_A s"
    apply -
    unfolding touched_addrs_A_def do_empty_TA_A_def
    apply force
   unfolding current_domain_A_def
   apply force
  unfolding v_to_p_A_def
  by blast

lemma do_empty_TA_maintains_external_uwr_in_A:
  "\<And>s t d.
     (s, t) \<in> external_uwr_A d \<Longrightarrow>
     current_domain_A s = d \<Longrightarrow>
     (do_empty_TA_A s, do_empty_TA_A t) \<in> external_uwr_A d"
  unfolding external_uwr_A_def current_domain_A_def do_empty_TA_A_def
  by force

lemma do_empty_TA_maintains_external_uwr_out_A:
  "\<And>s.
     current_domain_A s \<noteq> d \<Longrightarrow>
     (s, do_empty_TA_A s) \<in> external_uwr_A d"
  unfolding external_uwr_A_def current_domain_A_def do_empty_TA_A_def
  by force

definition can_domain_switch_A :: "other_state_A \<Rightarrow> bool" where
  "can_domain_switch_A s \<equiv> snd s = KSchedule"

lemma can_domain_switch_public_A:
  "(s1, s2) \<in> external_uwr_A d \<Longrightarrow> can_domain_switch_A s1 = can_domain_switch_A s2"
  unfolding external_uwr_A_def can_domain_switch_A_def
  by force

interpretation time_protection_A: time_protection collides_in_pch_A
  fch_lookup_A pch_lookup_A
  fch_access_impact_A pch_read_impact_A
  fch_access_impact_A pch_write_impact_A
  read_cycles_A write_cycles_A
  do_read_A do_write_A
  store_time_A padding_regs_impact_A
  empty_fch_A fch_flush_cycles_A do_pch_flush_A pch_flush_cycles_A
  addr_domain_A addr_colour_A colour_userdomain_A
  current_domain_A external_uwr_A v_to_p_A touched_addrs_A
  do_add_to_TA_A do_empty_TA_A
  can_domain_switch_A
  apply unfold_locales
    (* Forget the indentation: it'll just keep fluctuating as we experiment
       with the interface -robs. *)
    using collides_with_equiv_A apply blast
    using pch_partitioned_read_A apply blast
    using pch_collision_read_A apply blast
    using pch_partitioned_write_A apply blast
    using pch_collision_write_A apply blast
    using pch_partitioned_flush_A apply blast
    using pch_collision_flush_A apply blast
    using pch_flush_cycles_localised_A apply blast
    using no_cross_colour_collisions_A apply blast
    using addr_domain_valid_A apply blast
    using external_uwr_equiv_rel_A apply blast
    using external_uwr_same_domain_A apply blast
    using page_table_not_in_mem_A apply blast
    using external_uwr_current_page_table_A apply blast
    using do_write_maintains_external_uwr_out_A apply blast
    using do_write_maintains_external_uwr_in_A apply blast
    using do_write_outside_kernelshared_same_domain_A apply blast
    using do_read_from_external_uwr_domain_A apply blast
    using do_read_from_external_uwr_sched_A apply blast
    using external_uwr_same_touched_addrs_A apply blast
    using touched_addrs_not_in_mem_A apply blast
    using do_add_to_TA_correct_A apply auto[3]
    using do_add_to_TA_maintains_external_uwr_in_A apply blast
    using do_add_to_TA_maintains_external_uwr_out_A apply blast
    using do_empty_TA_correct_A apply auto[3]
    using do_empty_TA_maintains_external_uwr_in_A apply blast
    using do_empty_TA_maintains_external_uwr_out_A apply blast
    using can_domain_switch_public_A apply blast
  done
(* Gerwin's feedback: at least get to the end of this once
   so we know it's satisfiable even if not flexible *)

definition s0_A :: other_state_A where
  "s0_A = (\<lparr> mem = (\<lambda>a. 0), curdom = Sched, taddrs = {}\<rparr>, KExit)"

definition system_step_A :: "other_state_A rel" where
  "system_step_A =
    {((s, KExit), (s', KEntry)) | s s'. s = s'} \<union>
    {((s, KEntry), (s', KExit)) | s s'. s = s'} \<union>
    {((s, KEntry), (s', KSchedule)) | s s'. s = s'} \<union>
    {((s, KSchedule), (s', KExit)) | s s'. s = s'}"

definition original_system_A ::
  "(orig_state_A \<times> sys_mode, orig_state_A \<times> sys_mode, 'a) data_type"
  where
  "original_system_A = \<lparr> Init = \<lambda>s. {s}, Fin = id, Step = \<lambda>_. system_step_A \<rparr>"

definition policy_A :: "userdomain_A domain rel" where
  "policy_A = {(d, d'). d = Sched}"

definition out_A where
  "out_A = (\<lambda>_. id)"

interpretation time_protection_system_A: Init_inv_Fin_system original_system_A s0_A
  apply unfold_locales
    (* Init_Fin_system.Fin_Init_s0 *)
    apply(force simp:original_system_A_def)
   (* Init_Fin_system.Init_inv_Fin *)
   apply(force simp:original_system_A_def)
  (* Init_Fin_system.Fin_inj *)
  apply(force simp:original_system_A_def)
  (* FIXME: Don't know what the issue here is. *)
  done
  oops

(* XXX: defunct -robs.
interpretation time_protection_system_A: time_protection_system
  original_system_A s0_A
  current_domain_A external_uwr_A
  policy_A out_A
  collides_in_pch_A
  fch_lookup_A pch_lookup_A
  fch_access_impact_A pch_read_impact_A
  fch_access_impact_A pch_write_impact_A
  read_cycles_A write_cycles_A
  do_read_A do_write_A
  store_time_A padding_regs_impact_A
  empty_fch_A fch_flush_cycles_A do_pch_flush_A pch_flush_cycles_A
  addr_domain_A addr_colour_A colour_userdomain_A
  touched_addrs_A can_domain_switch_A
  apply unfold_locales
  sorry
*)

definition initial_regs_A :: regs_A where
  "initial_regs_A = \<lparr> r0 = 0 \<rparr>"

definition initial_pch_A :: pch_A where
  "initial_pch_A = (\<lambda> idx. None)"

interpretation time_protection_refinement_A: time_protection_refinement
  original_system_A
  refined_system (* TODO *)
  s0_A
  current_domain_A external_uwr_A
  policy_A out_A
  collides_in_pch_A
  fch_lookup_A pch_lookup_A
  fch_access_impact_A pch_read_impact_A
  fch_access_impact_A pch_write_impact_A
  read_cycles_A write_cycles_A
  do_read_A do_write_A
  store_time_A padding_regs_impact_A
  empty_fch_A fch_flush_cycles_A do_pch_flush_A pch_flush_cycles_A
  addr_domain_A addr_colour_A colour_userdomain_A v_to_p_A
  touched_addrs_A do_add_to_TA_A do_empty_TA_A can_domain_switch_A
  initial_regs_A initial_pch_A
  refined_step_to_program (* TODO *)
  apply unfold_locales
  sorry

end