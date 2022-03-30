(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory global_asm_stmt_gref
imports global_asm_stmt "AsmRefine.SimplExport" "AsmRefine.ProveGraphRefine"
begin

locale g_asm_graph_refine = g_asm_target
    + fixes domain
      assumes globals_list_distinct:
        "globals_list_distinct domain symbol_table globals_list"
      assumes globals_list_ok:
        "\<forall>g \<in> set globals_list. global_data_ok symbol_table g"
      assumes asm_semantics_respects:
        "asm_ops_are_swap t_hrs_' t_hrs_'_update
            phantom_machine_state_' phantom_machine_state_'_update
            symbol_table (\<lambda>s. (ghost'state_' s, hrs_htd (t_hrs_' s))) globals_list"

begin

lemmas globals_list_def = global_asm_stmt_global_addresses.global_data_list_def
declare asm_semantics_respects[unfolded Let_def, simp]

ML \<open>
emit_C_everything_relative @{context}
  (CalculateState.get_csenv @{theory} "global_asm_stmt.c" |> the)
  "global_asm_stmt_Cfuns.txt" "global_asm_stmt"
\<close>

lemma globals_list_valid:
  "globals_list_valid symbol_table t_hrs_' t_hrs_'_update globals_list"
  apply (rule globals_list_valid_optimisation[OF _ _ globals_list_ok])
  apply (simp_all add: globals_list_def globals_list_valid_def
                       global_data_defs
                  del: distinct_prop.simps split del: if_split)
   apply (simp add: global_data_swappable_def global_data_def)
  apply (simp_all add: global_data_valid)?
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
   apply (simp_all add: global_data_def)
  done

lemma phantom_machine_state_'_update_globals_swap[simp]:
  "phantom_machine_state_' (gswap gs) = phantom_machine_state_' gs
    \<and> gswap (phantom_machine_state_'_update f gs) = phantom_machine_state_'_update f (gswap gs)"
  apply (rule globals_swap_ex_swap)
   apply (simp only: globals_list_def global_data_defs list.simps ball_simps
                     is_global_data_simps simp_thms)
   apply (simp_all add: global_data_def)
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

end

consts
  encode_machine_state :: "machine_state \<Rightarrow> unit \<times> nat"

ML \<open>
val funs = ParseGraph.funs @{theory} "global_asm_stmt_Cfuns.txt"
\<close>

local_setup \<open>add_field_h_val_rewrites #> add_field_to_bytes_rewrites\<close>

context g_asm_graph_refine begin

local_setup \<open>add_globals_swap_rewrites @{thms global_asm_stmt_global_addresses.global_data_mems}\<close>

definition
  simpl_invariant :: "globals myvars set"
where
  "simpl_invariant = {s. const_globals_in_memory symbol_table globals_list
            (hrs_mem (t_hrs_' (globals s)))
        \<and> htd_safe domain (hrs_htd (t_hrs_' (globals s)))}"

abbreviation(input) "ghost_assns_from_globals
    \<equiv> (K (K 0 :: ghost_assertions) o ghost'state_' :: globals \<Rightarrow> _)"

text \<open>Test everything.\<close>
ML \<open>
val dbg = ProveSimplToGraphGoals.no_debug ();

ProveSimplToGraphGoals.test_all_graph_refine_proofs_parallel
    funs
    (CalculateState.get_csenv @{theory} "global_asm_stmt.c" |> the)
    @{context}
    dbg
\<close>

text \<open>The remainder is debug code for when things fail.\<close>

ML \<open>val nm = "global_asm_stmt.g"\<close>

local_setup \<open>define_graph_fun_short funs nm\<close>

ML \<open>
val hints = SimplToGraphProof.mk_hints funs @{context} nm
\<close>

ML \<open>
val init_thm = SimplToGraphProof.simpl_to_graph_upto_subgoals funs hints nm
    @{context}
\<close>

ML \<open>
ProveSimplToGraphGoals.simpl_to_graph_thm funs
  (CalculateState.get_csenv @{theory} "global_asm_stmt.c" |> the)
  @{context} nm;
\<close>

ML \<open>
val tacs = ProveSimplToGraphGoals.graph_refine_proof_tacs
  (CalculateState.get_csenv @{theory} "global_asm_stmt.c" |> the)
    #> map snd
val full_tac = ProveSimplToGraphGoals.graph_refine_proof_full_tac
  (CalculateState.get_csenv @{theory} "global_asm_stmt.c" |> the)
val full_goal_tac = ProveSimplToGraphGoals.graph_refine_proof_full_goal_tac
  (CalculateState.get_csenv @{theory} "global_asm_stmt.c" |> the)
val debug_tac = ProveSimplToGraphGoals.debug_tac
  (CalculateState.get_csenv @{theory} "global_asm_stmt.c" |> the)
\<close>

schematic_goal "PROP ?P"
  apply (tactic \<open>resolve_tac @{context} [init_thm] 1\<close>)
  apply (tactic \<open>ALLGOALS (TRY o (debug_tac @{context} THEN_ALL_NEW K no_tac))\<close>)
  oops

end

end
