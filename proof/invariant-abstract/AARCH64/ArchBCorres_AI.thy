(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBCorres_AI
imports
  BCorres_AI
begin

(* This context block finds all lemmas with names *.bit1.* or *.bit0.* depending on the size
   of vm_level, and locally re-declares them under the prefix vm_level.* so that their name
   is available generically without reference to whether vm_level is even or odd *)
context begin global_naming vm_level

local_setup \<open>
  let
    (* From find_theorems.ML *)
    fun all_facts_of lthy =
      let
        val ctxt = Local_Theory.target_of lthy;
        val thy = Proof_Context.theory_of ctxt;
        val transfer = Global_Theory.transfer_theories thy;
        val global_facts = Global_Theory.facts_of thy;
      in
       (Facts.dest_all (Context.Proof ctxt) false [] global_facts)
       |> maps Facts.selections
       |> map (apsnd transfer)
      end;

    (* We will not be referencing lemma collections, only single names *)
    fun is_single (Facts.Named (_, NONE)) = true
      | is_single _ = false

    fun name_of (Facts.Named ((name, _), _)) = name
      | name_of _ = raise ERROR "name_of: no name"

    (* Add a single theorem with name to the local theory *)
    fun add_thm (name, thm) lthy =
       Local_Theory.notes [((Binding.name name, []), [([thm], [])])] lthy |> #2

    (* Add a list of theorems with names to the local theory *)
    fun add_thms lthy xs = fold add_thm xs lthy

    (* The top-level constructor name of the vm_level numeral type tells us whether to match
       on bit0 or bit1 *)
    val bit_name = dest_Type @{typ AARCH64_A.vm_level} |> fst |> Long_Name.base_name

    (* Check whether an exploded long name does have a bit0/bit1 name *)
    fun matches_bit_name names = member (op =) names bit_name

    fun redeclare_short_names lthy =
      all_facts_of lthy
      |> filter (matches_bit_name o Long_Name.explode o Facts.ref_name o fst)
      |> filter (is_single o fst)
      |> map (fn (thm_ref, thm) => (name_of thm_ref |> Long_Name.base_name, thm))
      |> add_thms lthy
  in
    redeclare_short_names
  end
\<close>

end

context Arch begin global_naming AARCH64

lemma entry_for_asid_truncate[simp]:
  "entry_for_asid asid (truncate_state s) = entry_for_asid asid s"
  by (simp add: entry_for_asid_def pool_for_asid_def obind_def
         split: option.splits)

lemma vspace_for_asid_truncate[simp]:
  "vspace_for_asid asid (truncate_state s) = vspace_for_asid asid s"
  by (simp add: vspace_for_asid_def obind_def oreturn_def)

lemma pool_for_asid_truncate[simp]:
  "pool_for_asid asid (truncate_state s) = pool_for_asid asid s"
  by (simp add: pool_for_asid_def)

lemma vs_lookup_table_truncate[simp]:
  "vs_lookup_table l asid vptr (truncate_state s) = vs_lookup_table l asid vptr s"
  by (simp add: vs_lookup_table_def obind_def oreturn_def split: option.splits)

lemma vs_lookup_slot_truncate[simp]:
  "vs_lookup_slot l asid vptr (truncate_state s) = vs_lookup_slot l asid vptr s"
  by (simp add: vs_lookup_slot_def obind_def oreturn_def split: option.splits)

lemma pt_lookup_from_level_bcorres[wp]:
  "bcorres (pt_lookup_from_level l r b c) (pt_lookup_from_level l r b c)"
  by (induct l arbitrary: r b c rule: vm_level.minus_induct; wpsimp simp: pt_lookup_from_level_simps)

crunch (bcorres) bcorres[wp]: arch_finalise_cap truncate_state
crunch (bcorres) bcorres[wp]: prepare_thread_delete truncate_state

end

requalify_facts AARCH64.arch_finalise_cap_bcorres AARCH64.prepare_thread_delete_bcorres

declare arch_finalise_cap_bcorres[wp] prepare_thread_delete_bcorres[wp]

end
