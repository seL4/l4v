(*
 * Copyright 2021, The University of Melbourne (ABN 84 002 705 224)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory MemSysExample_RISCV64_A
imports TimeProtection
begin

(* RISCV64 example memory system A:
  - 8-way 32KiB L1-D (write-through)
  - 4-way 16KiB L1-I
  - ?-way 512KiB L2 (write-back) *)

(* Recall this is just for the L2 cache. *)
definition collision_set_A :: "address \<Rightarrow> address set" where
  "collision_set_A a = {a}" (* TODO *)

(* As our cache impact model is not distinguishing yet between I-cache and D-cache nor counting
   timing impacts of instruction fetching itself, let's say fch is just the L1-D. *)
type_synonym fch_cachedness_A = bool
type_synonym pch_cachedness_A = bool
type_synonym fch_A = "fch_cachedness_A fch"
type_synonym pch_A = "pch_cachedness_A pch"

definition read_impact_A :: "(fch_A, pch_A) cache_impact" where
  "read_impact_A a f p = (f, p)" (* TODO *)

definition write_impact_A :: "(fch_A, pch_A) cache_impact" where
  "write_impact_A a f p = (f, p)" (* TODO *)

interpretation time_protection_A: time_protection collision_set_A read_impact_A write_impact_A
  apply unfold_locales
   (* pch_partitioned_read *)
   defer
  (* pch_partitioned_write *)
  defer
  oops

end