(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory SEL4GraphRefine
imports
  "AsmRefine.ProveGraphRefine"
  "CSpec.Substitute"
  "SEL4GlobalsSwap"
  "SEL4SimplExport"
begin

declare ptr_add_assertion_uint [simp del]

ML \<open>
val funs = ParseGraph.funs @{theory} "CFunDump.txt"
\<close>

ML \<open>
fun define_all funs = fold (fn s => let val s' = Long_Name.base_name s
    val _ = tracing ("defining " ^ s) in
  ParseGraph.define_graph_fun funs (s' ^ "_graph") (Binding.name (s' ^ "_graph_fun")) s end)
  (Symtab.dest funs |> filter (fn (_, v) => #3 v <> NONE) |> map fst)
\<close>

ML \<open>
val csenv = let
    val the_csenv = CalculateState.get_csenv @{theory} "../c/build/$L4V_ARCH/kernel_all.c_pp" |> the
  in fn () => the_csenv end
\<close>

consts
  encode_machine_state :: "machine_state \<Rightarrow> unit \<times> nat"

local_setup \<open>add_field_h_val_rewrites #> add_field_to_bytes_rewrites\<close>

context graph_refine_locale begin

ML \<open>SimplToGraphProof.globals_swap
 := (fn t => @{term "globals_swap t_hrs_' t_hrs_'_update symbol_table globals_list"} $ t)
\<close>

local_setup \<open>add_globals_swap_rewrites @{thms kernel_all_global_addresses.global_data_mems}\<close>

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

(* If this fails, it can be debugged with the assistance of the
   script in TestGraphRefine.thy *)

ML \<open>ProveSimplToGraphGoals.test_all_graph_refine_proofs_parallel
    funs (csenv ()) @{context}\<close>

end

end
