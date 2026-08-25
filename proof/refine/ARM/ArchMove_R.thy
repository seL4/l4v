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

context Arch begin arch_global_naming

(* FIXME arch-split: missing from ArchCSpaceInvPre_AI on this architecture *)
lemma set_cap_aobjs_of[wp]:
  "set_cap cap ptr \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  unfolding set_cap_def
  apply (wpsimp wp: set_object_wp get_object_wp)
  apply (auto simp: opt_map_def obj_at_def aobj_of_def split: option.splits elim!: rsubst[where P=P])
  done

end (* Arch *)

end
