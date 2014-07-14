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

imports "../../tools/asmrefine/GraphRefine"
  "../../tools/asmrefine/FieldAccessors"
  "../../spec/cspec/Substitute"
  "SEL4GlobalsSwap"

begin

ML {* Toplevel.debug := true *}

ML {*
val funs = ParseGraph.funs @{theory} "../../spec/cspec/CFunDump.txt"
*}

ML {*
fun define_all funs = fold (fn s => let val s' = Long_Name.base_name s
    val _ = tracing ("defining " ^ s) in
  ParseGraph.define_graph_fun funs (s' ^ "_graph") (Binding.name (s' ^ "_graph_fun")) s end)
  (Symtab.dest funs |> filter (fn (_, v) => #3 v <> NONE) |> map fst)
*}

consts
  encode_machine_state :: "machine_state \<Rightarrow> unit \<times> nat"

definition
  simpl_invariant :: "globals myvars set"
where
  "simpl_invariant = UNIV"

local_setup {* add_field_h_val_rewrites #> add_field_to_bytes_rewrites *}

ML {* val nm = "Kernel_C.lookupSlotForCNodeOp" *}

locale graph_refine = kernel_all_substitute
    + assumes globals_list_distinct:
        "globals_list_distinct domain symbol_table globals_list"
      assumes halt_halts: "\<exists>ft. (\<forall>s xs. (\<Gamma> \<turnstile> \<langle>com.Call halt_'proc, Normal s\<rangle> \<Rightarrow> xs)
            = (xs = Fault ft))"
begin

local_setup {* define_graph_fun_short funs nm *}

ML {* UseHints.globals_swap
 := (fn t => @{term "globals_swap t_hrs_' t_hrs_'_update symbol_table globals_list"} $ t)
*}

ML {*
val hints = UseHints.mk_var_deps_hints funs @{context} @{typ "globals myvars"} nm
*}

ML {* init_graph_refines_proof funs nm @{context} *}
thm c_guard_to_word_ineq
find_theorems name: twice
find_theorems globals_list_valid

find_theorems name: ptr_inverse

ML {*

val global_data_mems = @{thms kernel_all_global_addresses.global_data_mems[
       unfolded global_data_defs]}

val pglobal_valids = (*
(global_data_mems RL
    @{thms ptr_inverse_safe_htd_safe_global_data[OF globals_list_distinct]
            ptr_inverse_safe_htd_safe_const_global_data[OF globals_list_distinct]})
  |> map (full_simplify (HOL_basic_ss addsimps @{thms symbols_in_table_simps
                    pglobal_valid_fold c_guard_to_word_ineq}))
  |> map (full_simplify (@{simpset} addsimps @{thms align_td_array' mask_def}))
*) []

val globals_swap_rewrites2
    = @{thms globals_list_distinct} RL globals_swap_rewrites

*}

schematic_lemma "PROP ?P"
  apply (tactic {* rtac it 1 *})
  apply (tactic {* full_simpl_to_graph_tac funs [] hints nm @{context} *})


  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 0) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 1) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 2) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 3) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 4) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 5) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 6) *})

  apply (simp_all add: field_h_val_rewrites field_to_bytes_rewrites heap_update_def
                       to_bytes_array upt_rec take_heap_list_min drop_heap_list_general
                       heap_update_list_append heap_list_update_ptr heap_list_update_word32
                       store_store_word32_commute_offset
                       heap_access_Array_element h_val_word32 h_val_ptr
                       field_lvalue_offset_eq)
  apply (auto simp: mex_def meq_def)
  done


end
