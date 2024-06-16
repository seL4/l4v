(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch specific lemmas that should be moved into theory files before Refine *)

theory ArchMove_R
imports
  Move_R
begin

(* Use one of these forms everywhere, rather than choosing at random. *)
lemmas cte_index_repair = mult.commute[where a="(2::'a::len word) ^ cte_level_bits"]
lemmas cte_index_repair_sym = cte_index_repair[symmetric]

lemmas of_nat_inj32 = of_nat_inj[where 'a=32, folded word_bits_def]

context begin
interpretation Arch .

(* Move to Deterministic_AI*)
crunches copy_global_mappings
  for valid_etcbs[wp]: valid_etcbs (wp: mapM_x_wp')

end

end
