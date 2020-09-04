(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SEL4GlobalsSwap
imports
  "AsmRefine.GlobalsSwap"
  "AsmRefine.AsmSemanticsRespects"
  "AsmRefine.FieldAccessors"
  "CSpec.Substitute"
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

instance ptr :: (c_type)array_outer_packed ..
instance tcb_queue_C :: array_outer_packed ..
instance region_C :: array_outer_packed ..

locale graph_refine_locale = kernel_all_substitute
    + assumes globals_list_distinct:
        "globals_list_distinct domain symbol_table globals_list"
      assumes globals_list_ok:
        "\<forall>g \<in> set globals_list. global_data_ok symbol_table g"
      assumes asm_semantics_respects:
        "asm_ops_are_swap t_hrs_' t_hrs_'_update
            phantom_machine_state_' phantom_machine_state_'_update
            symbol_table (\<lambda>s. (ghost'state_' s, hrs_htd (t_hrs_' s))) globals_list"

begin

lemmas globals_list_def = kernel_all_global_addresses.global_data_list_def
lemmas global_data_defs = kernel_all_global_addresses.global_data_defs
declare asm_semantics_respects[unfolded Let_def, simp]

lemma globals_list_valid:
  "globals_list_valid symbol_table t_hrs_' t_hrs_'_update globals_list"
  apply (rule globals_list_valid_optimisation[OF _ _ globals_list_ok])
  apply (simp_all add: globals_list_def globals_list_valid_def
                       global_data_defs
                  del: distinct_prop.simps split del: if_split)
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

lemma globals_swap_ex_swap:
  "\<forall>x \<in> set gxs. is_global_data x \<longrightarrow> (case x of GlobalData nm sz tg g' s'
        \<Rightarrow> (\<forall>v v' gs. s' v (s v' gs) = s v' (s' v gs))
            \<and> (\<forall>v gs. g' (s v gs) = g' gs)
            \<and> (\<forall>v gs. g (s' v gs) = g gs))
    \<Longrightarrow> (\<forall>v v' gs. th_s v (s v' gs) = s v' (th_s v gs))
            \<and> (\<forall>v gs. g (th_s v gs) = g gs)
            \<and> (\<forall>v gs. th_g (s v gs) = th_g gs)
    \<Longrightarrow> g (globals_swap th_g th_s symt gxs gs) = g gs
    \<and> globals_swap th_g th_s symt gxs (s v gs) = s v (globals_swap th_g th_s symt gxs gs)"
  apply (simp add: globals_swap_def)
  apply (rule conjI)
   apply (rule foldr_does_nothing_to_xf)
   apply (drule(1) bspec)
   apply (case_tac x, simp_all add: global_swap_def is_global_data_def K_def)
  apply (rule foldr_update_commutes[symmetric])
  apply (drule(1) bspec)
  apply (case_tac x, simp_all add: global_swap_def is_global_data_def K_def)
  done

lemma ghost'state_update_globals_swap:
  "ghost'state_' (gswap gs) = ghost'state_' gs
    \<and> gswap (ghost'state_'_update f gs) = ghost'state_'_update f (gswap gs)"
  apply (rule globals_swap_ex_swap)
   apply (simp only: globals_list_def global_data_defs list.simps ball_simps
                     is_global_data_simps simp_thms)
   apply (simp add: global_data_def)
  apply simp
  done

lemma phantom_machine_state_'_update_globals_swap[simp]:
  "phantom_machine_state_' (gswap gs) = phantom_machine_state_' gs
    \<and> gswap (phantom_machine_state_'_update f gs) = phantom_machine_state_'_update f (gswap gs)"
  apply (rule globals_swap_ex_swap)
   apply (simp only: globals_list_def global_data_defs list.simps ball_simps
                     is_global_data_simps simp_thms)
   apply (simp add: global_data_def)
  apply simp
  done

(* FIXME: this has to be done and should be standardised *)
lemma t_hrs_ghost'state_update_globals_swap[simp]:
  "t_hrs_' (gswap (ghost'state_'_update f gs)) = t_hrs_' (gswap gs)"
  by (simp add: ghost'state_update_globals_swap)

lemma t_hrs_phantom_machine_state_'_update_globals_swap[simp]:
  "t_hrs_' (gswap (phantom_machine_state_'_update f gs)) = t_hrs_' (gswap gs)"
  by (simp add: phantom_machine_state_'_update_globals_swap)

lemma globals_swap_twice[simp]:
  "gswap (gswap gs) = gs"
  by (metis globals_swap_twice_helper globals_list_distinct
            globals_list_valid global_acc_valid)

lemma t_hrs_'_update_hmu_triv[simp]:
  "f (hrs_mem (t_hrs_' gs)) = hrs_mem (t_hrs_' gs)
    \<Longrightarrow> t_hrs_'_update (hrs_mem_update f) gs = gs"
  by (cases gs, auto simp add: hrs_mem_update_def hrs_mem_def)

(* This is needed during graph_refine_proof_tacs, but t_hrs_' isn't accessible in that context. *)
lemma t_hrs_'_heap_update_id[simp]:
  fixes p :: "'a::packed_type ptr"
  shows "t_hrs_'_update (hrs_mem_update (heap_update p ((h_val (hrs_mem (t_hrs_' s)) p)))) s = s"
  by (simp add: heap_update_id)

end

end

