(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TestGraphRefine
imports
  "AsmRefine.ProveGraphRefine"
  "CSpec.Substitute"
  "SEL4GlobalsSwap"
  "SimplExport.SEL4SimplExport"
begin

\<comment>\<open> Name of the C function to investigate. \<close>
ML \<open>
val nm = "Kernel_C.dist_init"
\<close>

\<comment>\<open> Double-check we're reading the right graphlang file. \<close>
ML \<open>
writeln CFunDump_filename;
val funs = ParseGraph.funs @{theory} CFunDump_filename
\<close>

\<comment>\<open>
  These functions split up each part of "step 4", which is usually where
  SimplExportAndRefine breaks.

  Step 4 is roughly equivalent to:

  debug_decompose_mem_goals ctxt
    THEN_ALL_NEW debug_prove_mem_equality ctxt
    THEN_ALL_NEW ProveSimplToGraphGoals.dest_ptr_add_assertion

  `debug_decompse_mem_goals` lets you see what the actual memory update
  goal looks like.

  `debug_prove_mem_equality` let you "pause" in the middle of step 4, after
  "prove_mem_equality" would normally error out because of a remaining
  memory update goal.

  Once paused, you can look for a simp rule that you
  think will resolve the issue, then try adding it to
  @{ML ProveSimplToGraphGoals.prove_mem_equality_unpack_simpset}.
\<close>
ML \<open>
local
  open ProveSimplToGraphGoals;
in
  val debug_decompose_mem_goals = decompose_mem_goals_init (K (K all_tac)) true;
  fun debug_prove_mem_equality ctxt = DETERM o
    (prove_mem_equality_unchecked ctxt
    THEN_ALL_NEW SUBGOAL (fn (t, _) =>
      (if exists_Const (fn (s, _) =>
                 s = @{const_name store_word8}
          orelse s = @{const_name store_word32}
          orelse s = @{const_name store_word64}
          orelse s = @{const_name heap_update}
          orelse s = @{const_name heap_update_list}) t
      then warning "prove_mem_equality: remaining mem upds. This would be a failure normally!"
      else (); all_tac)))
end
\<close>

\<comment>\<open>
  A safe and easy way to attach a vacuous premise to your current goal,
  with a message attached.
\<close>
definition Tag :: "'a \<Rightarrow> bool" where
  "Tag data \<equiv> True"

lemma tagI: "(Tag data \<Longrightarrow> P) \<Longrightarrow> P" by (simp add: Tag_def)

ML \<open>
fun tag_subgoals_tac ctxt idx: tactic =
    let
      val data = HOLogic.mk_string ("Subgoal " ^ Int.toString idx) |> Thm.cterm_of ctxt;
      val typInst = ("'a", 0) |> rpair @{sort type} |> rpair @{ctyp string}
      val termInst = ("data", 0) |> rpair @{typ string} |> rpair data;
      val tagI = Thm.instantiate (TVars.make [typInst], Vars.make [termInst]) @{thm tagI};
    in resolve0_tac [tagI] idx end
\<close>

\<comment>\<open>
#####################################################################
                     BEGIN SETUP BOILERPLATE
#####################################################################
\<close>

ML \<open>
fun define_all funs = fold (fn s => let val s' = Long_Name.base_name s
    val _ = tracing ("defining " ^ s) in
  ParseGraph.define_graph_fun funs (s' ^ "_graph") (Binding.name (s' ^ "_graph_fun")) s end)
  (Symtab.dest funs |> filter (fn (_, v) => #3 v <> NONE) |> map fst)
\<close>

consts
  encode_machine_state :: "machine_state \<Rightarrow> unit \<times> nat"

context graph_refine_locale begin

local_setup \<open>
  add_field_h_val_rewrites
  #> add_field_to_bytes_rewrites
  #> add_field_offset_rewrites
  #> add_globals_swap_rewrites @{thms kernel_all_global_addresses.global_data_mems}
  #> define_graph_fun_short funs nm
\<close>

definition
  simpl_invariant :: "globals myvars set"
where
  "simpl_invariant = {s. const_globals_in_memory symbol_table globals_list
            (hrs_mem (t_hrs_' (globals s)))
        \<and> htd_safe domain (hrs_htd (t_hrs_' (globals s)))}"

abbreviation(input) "ghost_assns_from_globals
    \<equiv> (snd o snd o ghost'state_' :: globals \<Rightarrow> _)"

lemma snd_snd_gs_new_frames_new_cnodes[simp]:
  "snd (snd (gs_new_frames sz ptr bits gs)) = snd (snd gs)"
  "snd (snd (gs_new_cnodes sz' ptr bits gs)) = snd (snd gs)"
  "snd (snd (gs_clear_region ptr sz' gs)) = snd (snd gs)"
  "snd (snd ((if P then f else g) gs)) = (if P then snd (snd (f gs)) else snd (snd (g gs)))"
  by (simp_all add: gs_new_frames_def gs_new_cnodes_def gs_clear_region_def)

ML \<open>
val cfile = "../c/build/$L4V_ARCH/kernel_all.c_pp"

val csenv = let
    val the_csenv = CalculateState.get_csenv @{theory} cfile |> the
  in fn () => the_csenv end

val tacs = ProveSimplToGraphGoals.graph_refine_proof_tacs (csenv ())
    #> map snd
val full_tac = ProveSimplToGraphGoals.graph_refine_proof_full_tac
    (csenv ())
val full_goal_tac = ProveSimplToGraphGoals.graph_refine_proof_full_goal_tac
    (csenv ())
val debug_tac = ProveSimplToGraphGoals.debug_tac
    (csenv ())
val debug_step_tac = ProveSimplToGraphGoals.debug_step_tac
    (csenv ())
\<close>

ML \<open>
val hints = SimplToGraphProof.mk_hints funs @{context} nm
val init_thm =
    SimplToGraphProof.simpl_to_graph_upto_subgoals funs hints nm @{context}
\<close>

\<comment>\<open>
#####################################################################
                      END SETUP BOILERPLATE
#####################################################################
\<close>

declare [[show_types]]
declare [[show_sorts]]
declare [[goals_limit = 100]]

\<comment>\<open>
  Investigate the failure.
\<close>
schematic_goal "PROP ?P"
  apply (tactic \<open>resolve_tac @{context} [init_thm] 1\<close>)

  \<comment>\<open>
    Mark each subgoal. Later, you can restrict your focus to the failing
    initial goal.
  \<close>
  apply (tactic \<open>ALLGOALS (tag_subgoals_tac @{context})\<close>)

(*
  \<comment>\<open> `Goal.restrict x 1` selects subgoal `x`. \<close>
  apply (tactic \<open>PRIMITIVE (Goal.restrict 102 1)\<close>)
*)

  \<comment>\<open>
    Apply the "all steps" debug tactic to every goal, but restore any
    unproven goals.

    This can take a while for cases where there are lots of subgoals.
    In that case, comment out this line and use the separate calls to
    `debug_step_tac` below in order to find the failure.
  \<close>
  apply (all \<open>(solves \<open>tactic \<open>HEADGOAL (debug_tac @{context})\<close>\<close>)?\<close>)

  \<comment>\<open> Lets us edit the following lines without re-running the above line. \<close>
  apply (tactic \<open>all_tac\<close>)

  apply (tactic \<open>ALLGOALS (debug_step_tac @{context} 1)\<close>)
  apply (tactic \<open>ALLGOALS (debug_step_tac @{context} 2)\<close>)
  apply (tactic \<open>ALLGOALS (debug_step_tac @{context} 3)\<close>)
  \<comment>\<open>
    Step 4 is often where things break. You can use
    @{ML "debug_decompose_mem_goals"} and @{ML "debug_prove_mem_equality"}
    to investigate more closely - see their definitions for details.
  \<close>
  apply (tactic \<open>ALLGOALS (debug_step_tac @{context} 4)\<close>)
  apply (tactic \<open>ALLGOALS (debug_step_tac @{context} 5)\<close>)
  apply (tactic \<open>ALLGOALS (debug_step_tac @{context} 6)\<close>)
  apply (tactic \<open>ALLGOALS (debug_step_tac @{context} 7)\<close>)
  apply (tactic \<open>ALLGOALS (debug_step_tac @{context} 8)\<close>)
  apply (tactic \<open>ALLGOALS (debug_step_tac @{context} 9)\<close>)
  oops

end

end
