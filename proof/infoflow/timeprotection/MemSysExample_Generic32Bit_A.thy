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

record other_state_A =
  mem :: "address \<Rightarrow> machine_word"

record regs_A =
  r0 :: "machine_word"

(* This part is all just for the L2 cache.
   As for now we just need something generic to test-instantiate our locale to completion,
   these numbers are plucked from thin air for a hypothetical cache that supports 4 colours.
   31               ...          8                             0
   | page (24 bits) ...          |        page offset          |
                        | colour |
                        | (2bit) |
   | tag (22 bits)  ... |     index (6bit)      | block offset |
   31                  10                       4              0 *)
(* Note: There should be "x" mask bits for an "x word" type, and the offset
   should match the number of zeroes to the right of the mask. *)
type_synonym tag_A = "22 word"
definition tag_mask :: address where "tag_mask = 0b11111111111111111111110000000000"
definition tag_offset :: nat where "tag_offset = 10"
type_synonym index_A = "6 word"
definition index_mask :: address where "index_mask = 0b1111110000"
definition index_offset :: nat where "index_offset = 4"
type_synonym colour_A = "2 word"
definition colour_mask :: address where "colour_mask = 0b1100000000"
definition colour_offset :: nat where "colour_offset = 8"

definition tag_of :: "address \<Rightarrow> tag_A" where
  "tag_of a = ucast ((a AND tag_mask) >> tag_offset)"
definition index_of :: "address \<Rightarrow> index_A" where
  "index_of a = ucast ((a AND index_mask) >> index_offset)"
definition colour_of :: "address \<Rightarrow> colour_A" where
  "colour_of a = ucast ((a AND colour_mask) >> colour_offset)"

(* In this system let's choose to have the max number of user domains possible on the hardware
   - that is, as many as there are colours. -robs. *)
type_synonym userdomain_A = colour_A
abbreviation addr_colour_A :: "address \<Rightarrow> colour_A" where "addr_colour_A \<equiv> colour_of"
abbreviation colour_userdomain_A :: "colour_A \<Rightarrow> userdomain_A" where "colour_userdomain_A \<equiv> id"

definition collides_in_pch_A :: "address rel" where
  "collides_in_pch_A = {(a, a'). index_of a = index_of a'}"

(* As our cache impact model is not distinguishing yet between I-cache and D-cache nor counting
   timing impacts of instruction fetching itself, let's say fch is just the L1-D.
   Also a big TODO here still is to distinguish between virtual and physical addresses. *)

datatype writethru_cachedness = WT_Absent | WT_Valid
datatype writeback_cachedness = WB_Absent | WB_Valid | WB_DirtyValid

type_synonym fch_cachedness_A = writethru_cachedness
type_synonym pch_cachedness_A = writeback_cachedness
type_synonym fch_A = "fch_cachedness_A fch"
type_synonym pch_A = "pch_cachedness_A pch"

definition fch_read_impact_A :: "fch_A fch_impact" where
  "fch_read_impact_A a f = f" (* TODO *)

definition pch_read_impact_A :: "(fch_A, pch_A) pch_impact" where
  "pch_read_impact_A a f p = p" (* TODO *)

definition fch_write_impact_A :: "fch_A fch_impact" where
  "fch_write_impact_A a f = f" (* TODO *)

definition pch_write_impact_A :: "(fch_A, pch_A) pch_impact" where
  "pch_write_impact_A a f p = p" (* TODO *)

definition read_cycles_A :: "fch_cachedness_A \<Rightarrow> pch_cachedness_A \<Rightarrow> time" where
  "read_cycles_A a p = 0" (* TODO *)

definition write_cycles_A :: "fch_cachedness_A \<Rightarrow> pch_cachedness_A \<Rightarrow> time" where
  "write_cycles_A a p = 0" (* TODO *)

definition do_read_A :: "address \<Rightarrow> other_state_A \<Rightarrow> regs_A \<Rightarrow> regs_A" where
  "do_read_A a s r = r" (* TODO *)

definition do_write_A :: "address \<Rightarrow> other_state_A \<Rightarrow> regs_A \<Rightarrow> other_state_A" where
  "do_write_A a s r = s" (* TODO *)

definition store_time_A :: "time \<Rightarrow> regs_A \<Rightarrow> regs_A" where
  "store_time_A t r = r" (* TODO *)

definition padding_regs_impact_A :: "time \<Rightarrow> regs_A \<Rightarrow> regs_A" where
  "padding_regs_impact_A t r = r"  (* TODO *)

definition empty_fch_A :: fch_A where
  "empty_fch_A a = WT_Absent"

definition fch_flush_cycles_A:: "fch_A \<Rightarrow> time" where
  "fch_flush_cycles_A f = 0" (* TODO *)

definition do_pch_flush_A :: "pch_A \<Rightarrow> address set \<Rightarrow> pch_A" where
  "do_pch_flush_A p as = p" (* TODO *)

definition addr_domain_A :: "address \<Rightarrow> userdomain_A domain" where
  "addr_domain_A a = Sched" (* TODO *)

lemma colours_not_shared_A:
  "colour_userdomain_A c1 \<noteq> colour_userdomain_A c2 \<Longrightarrow> c1 \<noteq> c2"
  using distinct_lemma by blast

lemma same_index_same_colour:
  "index_of a = index_of b \<Longrightarrow> colour_of a = colour_of b"
  unfolding index_of_def colour_of_def
    index_mask_def index_offset_def colour_mask_def colour_offset_def
  by (word_bitwise, simp)

lemma no_cross_colour_collisions_A:
  "(a1, a2) \<in> collides_in_pch_A \<Longrightarrow> addr_colour_A a1 = addr_colour_A a2"
  unfolding collides_in_pch_A_def
  using same_index_same_colour by blast

lemma addr_domain_valid_A:
  "addr_domain_A a = Sched \<or> addr_domain_A a = User (colour_userdomain_A (addr_colour_A a))"
  oops (* TODO: Define addr_domain_A first. *)

definition current_domain_A :: "other_state_A \<Rightarrow> userdomain_A domain" where
  "current_domain_A s = Sched" (* TODO *)

definition external_uwr_A :: "userdomain_A domain \<Rightarrow> (other_state_A \<times> other_state_A) set" where
  "external_uwr_A d = UNIV" (* TODO *)

lemma external_uwr_equiv_rel_A:
  "equiv UNIV (external_uwr_A d)"
  oops

lemma external_uwr_same_domain_A:
  "(s1, s2) \<in> external_uwr_A d \<Longrightarrow> current_domain_A s1 = current_domain_A s2"
  oops

lemma do_write_maintains_external_uwr_out_A:
  "addr_domain_A a \<noteq> d \<and> addr_domain_A a \<noteq> Sched \<Longrightarrow>
   (s, do_write_A a s r) \<in> external_uwr_A d"
  oops

lemma do_write_maintains_external_uwr_in:
  "addr_domain_A a = d \<or> addr_domain_A a = Sched \<Longrightarrow>
   (s, t) \<in> external_uwr_A d \<Longrightarrow>
   (do_write_A a s r, do_write_A a t r) \<in> external_uwr_A d"
  oops

definition pch_flush_cycles_A :: "pch_A \<Rightarrow> address set \<Rightarrow> time" where
  "pch_flush_cycles_A p as = 0" (* TODO *)

definition touched_addrs_A :: "other_state_A \<Rightarrow> address set" where
  "touched_addrs_A s = {}" (* TODO *)

lemma external_uwr_same_touched_addrs_A:
  "(s1, s2) \<in> external_uwr_A d \<Longrightarrow> current_domain_A s1 = d \<Longrightarrow>
   touched_addrs_A s1 = touched_addrs_A s2"
  oops

definition can_domain_switch_A :: "other_state_A \<Rightarrow> bool" where
  "can_domain_switch_A s = False" (* TODO *)

lemma can_domain_switch_public_A:
  "(s1, s2) \<in> external_uwr_A d \<Longrightarrow> can_domain_switch_A s1 = can_domain_switch_A s2"
  oops

interpretation time_protection_A: time_protection collides_in_pch_A
  fch_read_impact_A pch_read_impact_A
  fch_write_impact_A pch_write_impact_A
  read_cycles_A write_cycles_A
  do_read_A do_write_A
  store_time_A padding_regs_impact_A
  empty_fch_A fch_flush_cycles_A do_pch_flush_A pch_flush_cycles_A
  addr_domain_A addr_colour_A colour_userdomain_A
  current_domain_A external_uwr_A touched_addrs_A can_domain_switch_A
  apply unfold_locales
  oops
(* Gerwin's feedback: at least get to the end of this once
   so we know it's satisfiable even if not flexible *)

end