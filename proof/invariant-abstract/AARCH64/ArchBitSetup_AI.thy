(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBitSetup_AI
imports
  Include_AI
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

end