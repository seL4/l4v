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

thm take_heap_list_min

ML {*
val funs = ParseGraph.funs @{theory} "CFunDump.txt"
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
  at_addr :: "'a \<Rightarrow> bool"
where
  "at_addr addr = True"

lemma eq_impl_at_addrI:
  "\<lbrakk> \<And>sst gst. at_addr addr \<Longrightarrow> sst \<in> S \<Longrightarrow> eqs gst sst \<Longrightarrow> eqs2 gst sst \<rbrakk>
    \<Longrightarrow> eq_impl addr eqs eqs2 S"
  by (simp add: eq_impl_def at_addr_def)

local_setup {* add_field_h_val_rewrites #> add_field_to_bytes_rewrites *}

ML {* val nm = "Kernel_C.getSyscallArg" *}

locale graph_refine = kernel_all_substitute
    + assumes globals_list_distinct:
        "globals_list_distinct domain symbol_table globals_list"
      assumes halt_halts: "\<exists>ft. (\<forall>s xs. (\<Gamma> \<turnstile> \<langle>com.Call halt_'proc, Normal s\<rangle> \<Rightarrow> xs)
            = (xs = Fault ft))"
begin

definition
  simpl_invariant :: "globals myvars set"
where
  "simpl_invariant = {s. const_globals_in_memory symbol_table globals_list
            (hrs_mem (t_hrs_' (globals s)))
        \<and> htd_safe domain (hrs_htd (t_hrs_' (globals s)))}"

local_setup {* define_graph_fun_short funs nm *}

ML {* UseHints.globals_swap
 := (fn t => @{term "globals_swap t_hrs_' t_hrs_'_update symbol_table globals_list"} $ t)
*}

ML {*
val hints = UseHints.mk_var_deps_hints funs @{context} @{typ "globals myvars"} nm
*}

ML {* init_graph_refines_proof funs nm @{context} *}

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

ML {*
mk_graph_refines_proof funs [] hints globals_swap_rewrites2 nm
  (@{context} addsimps @{thms simpl_invariant_def})
*}

lemma store_word32s_equality_refl:
  "store_word32s_equality addr xs xs hp hp"
  by (simp add: store_word32s_equality_def)

schematic_lemma "PROP ?P"
  apply (tactic {* rtac it 1 *})
  apply (tactic {* full_simpl_to_graph_tac funs [] hints nm @{context} *})
  apply (tactic {* ALLGOALS (TRY o rtac @{thm eq_impl_at_addrI}) *})
  apply (tactic {* ALLGOALS (simp_tac ((put_simpset HOL_basic_ss @{context})
      addsimps @{thms mex_def meq_def simpl_invariant_def})) *})


  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 0) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 1) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 2) *})

  apply (tactic {* ALLGOALS (simp_tac (@{context} addsimps @{thms
                       hrs_mem_update
                       hrs_htd_globals_swap mex_def meq_def}
                       addsimps globals_swap_rewrites2)) *})

  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 3) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 4) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 5) *})
  apply (tactic {* ALLGOALS (nth (graph_refine_proof_tacs @{context}) 6) *})


  apply (simp_all add: field_h_val_rewrites field_to_bytes_rewrites heap_update_def
                       to_bytes_array upt_rec take_heap_list_min drop_heap_list_general
                       heap_update_list_append heap_list_update_ptr heap_list_update_word32
                       store_store_word32_commute_offset field_simps
                       heap_access_Array_element h_val_word32 h_val_ptr
                       field_lvalue_offset_eq ucast_eq_0s)

  apply (tactic {* simp_tac (@{context} addsimps @{thms store_word32s_equality_fold store_word32s_equality_final add_commute}
    ) |>ALLGOALS *})

   apply (tactic {* simp_tac (@{context} addsimprocs [store_word32s_equality_simproc]
    addsimps @{thms store_word32s_equality_final add_commute}
    ) |>ALLGOALS *})

  done


end
