(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory SEL4GlobalsSwap

imports "../../tools/asmrefine/GlobalsSwap"
  "../../tools/asmrefine/FieldAccessors"
  "../../spec/cspec/Substitute"
  (* FIXME CommonOps only needed because ptr_inverse_safe in wrong place *)
  "../../tools/asmrefine/CommonOps"

begin

lemma globals_update_id:
  "globals_update id = id"
  by (rule ext, simp)

lemma globals_update_eq_iff:
  "(globals_update f s = globals_update g s)
        = (f (globals s) = g (globals s))"
  apply (rule iffI)
   apply (drule_tac f=globals in arg_cong)
   apply simp
  apply (rule state.fold_congs, simp+)
  done

instance ptr :: (c_type)oneMB_packed ..
instance tcb_queue_C :: oneMB_packed ..
instance region_C :: oneMB_packed ..

locale graph_refine_locale = kernel_all_substitute
    + assumes globals_list_distinct:
        "globals_list_distinct domain symbol_table globals_list"
      assumes globals_list_ok:
        "\<forall>g \<in> set globals_list. global_data_ok symbol_table g"
begin

lemmas globals_list_def = kernel_all_global_addresses.global_data_list_def
lemmas global_data_defs = kernel_all_global_addresses.global_data_defs

lemma globals_list_valid:
  "globals_list_valid symbol_table t_hrs_' t_hrs_'_update globals_list"
  apply (rule globals_list_valid_optimisation[OF _ _ globals_list_ok])
  apply (simp_all add: globals_list_def globals_list_valid_def
                       global_data_defs
                  del: distinct_prop.simps split del: split_if)
   apply (simp add: global_data_swappable_def global_data_def)
  apply (simp_all add: global_data_valid)
  apply (simp_all add: global_data_valid_def addressed_global_data_def
                   const_global_data_def global_data_ok_def global_data_def
                   to_bytes_p_from_bytes)
  done

lemma global_acc_valid:
  "global_acc_valid t_hrs_' t_hrs_'_update"
  by (simp add: global_acc_valid_def)

abbreviation "gswap == globals_swap t_hrs_' t_hrs_'_update symbol_table globals_list"

lemma globals_swap_twice:
  "globals_list_distinct D symbol_table globals_list
    \<Longrightarrow> gswap (gswap gs) = gs"
  by (intro globals_swap_twice_helper globals_list_valid global_acc_valid)

lemma ghost'state_update_globals_swap:
  "gswap (ghost'state_'_update f gs) = ghost'state_'_update f (gswap gs)"
  apply (simp add: globals_swap_def)
  apply (rule foldr_update_commutes[symmetric])
  apply (auto simp: globals_list_def global_data_defs global_swap_def
                    global_data_def const_global_data_def addressed_global_data_def)
  done

(* FIXME: this has to be done and should be standardised *)
lemma t_hrs_ghost'state_update_globals_swap[simp]:
  "t_hrs_' (gswap (ghost'state_'_update f gs)) = t_hrs_' (gswap gs)"
  by (simp add: ghost'state_update_globals_swap)

end

end

