(*
 * Copyright 2020, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(* Arch specific lemmas that should be moved into theory files before Refine *)

theory ArchMove_R
imports
  "../Move_R"

begin

(* Use one of these forms everywhere, rather than choosing at random. *)
lemmas cte_index_repair = mult.commute[where a="(2::'a::len word) ^ cte_level_bits"]
lemmas cte_index_repair_sym = cte_index_repair[symmetric]

lemmas of_nat_inj32 = of_nat_inj[where 'a=32, folded word_bits_def]

context begin
interpretation Arch .

(* Move to Deterministic_AI*)
crunch valid_etcbs[wp]: copy_global_mappings valid_etcbs (wp: mapM_x_wp')

end

end
