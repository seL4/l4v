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

imports "../../tools/asmrefine/ProveGraphRefine"
  "../../spec/cspec/Substitute"
  "SEL4GlobalsSwap"

begin

ML {* Toplevel.debug := true *}

ML {*
val funs = ParseGraph.funs @{theory} "CFunDump.txt"
*}

ML {*
fun define_all funs = fold (fn s => let val s' = Long_Name.base_name s
    val _ = tracing ("defining " ^ s) in
  ParseGraph.define_graph_fun funs (s' ^ "_graph") (Binding.name (s' ^ "_graph_fun")) s end)
  (Symtab.dest funs |> filter (fn (_, v) => #3 v <> NONE) |> map fst)
*}

ML {*
val csenv = let
    val the_csenv = CalculateState.get_csenv @{theory} "c/kernel_all.c_pp" |> the
  in fn () => the_csenv end
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

locale graph_refine_locale = kernel_all_substitute
    + assumes globals_list_distinct:
        "globals_list_distinct domain symbol_table globals_list"
      assumes halt_halts: "\<exists>ft. (\<forall>s xs. (\<Gamma> \<turnstile> \<langle>com.Call halt_'proc, Normal s\<rangle> \<Rightarrow> xs)
            = (xs = Fault ft))"
begin

local_setup {* add_globals_swap_rewrites @{thms kernel_all_global_addresses.global_data_mems} *}

definition
  simpl_invariant :: "globals myvars set"
where
  "simpl_invariant = {s. const_globals_in_memory symbol_table globals_list
            (hrs_mem (t_hrs_' (globals s)))
        \<and> htd_safe domain (hrs_htd (t_hrs_' (globals s)))}"

ML {* ProveSimplToGraphGoals.test_afll_graph_refine_proofs_after
    funs (csenv ()) [] @{context} (SOME "Kernel_C.makeUserPDE")  *} 

ML {* val nm = "Kernel_C.makeUserPDE" *}

local_setup {* define_graph_fun_short funs nm *}

ML {* SimplToGraphProof.globals_swap
 := (fn t => @{term "globals_swap t_hrs_' t_hrs_'_update symbol_table globals_list"} $ t)
*}

ML {*
val hints = SimplToGraphProof.mk_hints funs @{context} nm
*}

ML {*
val init_thm = SimplToGraphProof.simpl_to_graph_upto_subgoals funs [@{thm halt_halts}] hints nm
    @{context}
*}

ML {*
ProveSimplToGraphGoals.simpl_to_graph_thm funs (csenv ()) [@{thm halt_halts}] @{context} nm;
*}


ML {*
val tacs = ProveSimplToGraphGoals.graph_refine_proof_tacs (csenv ())
    #> map snd
val full_tac = ProveSimplToGraphGoals.graph_refine_proof_full_tac
    (csenv ())
val full_goal_tac = ProveSimplToGraphGoals.graph_refine_proof_full_goal_tac
    (csenv ())
*}

schematic_lemma "PROP ?P"
  apply (tactic {* rtac init_thm 1 *})
  

  apply (tactic {* ALLGOALS (TRY o (full_goal_tac @{context} THEN_ALL_NEW K no_tac)) *})

(*  apply (tactic {* ALLGOALS (TRY o rtac @{thm eq_impl_at_addrI}) *}) *)

  apply (tactic {* ALLGOALS (nth (tacs @{context}) 0) *})
apply simp
  apply (tactic {* ALLGOALS (nth (tacs @{context}) 1) *})
  apply (tactic {* ALLGOALS (nth (tacs @{context}) 2) *})


  apply (tactic {* full_tac @{context} *})

  apply (simp_all add: word_sle_def[THEN arg_cong[where f=Not], THEN iffD2])

defer

  apply (tactic {* full_tac @{context} *})[2]

ML_val {* nth (ProveSimplToGraphGoals.graph_refine_proof_tacs (csenv ()) @{context}) 3 *}

  apply (tactic {* (nth (tacs @{contfext}) 3) 1 *})


  apply (tactic {* ProveSimplToGraphGoals.decompose_graph_refine_memory_problems false
          (@{context} |> Splitter.del_split @{thm split_if}
        (* |> Simplifier.del_cong @{thm if_weak_cong} *)) 1 *})[1]

  apply (tactic {* full_tac @{context} *})[1]

  apply (rule sym, tactic {* ProveSimplToGraphGoals.clean_heap_upd_swap @{context} 1 *})

  apply (tactic {* ProveSimplToGraphGoals.prove_mem_equality @{context} 1 *})

  apply (simp add: heap_update_def to_bytes_array
               heap_update_list_append heap_list_update_ptr heap_list_update_word32
               field_lvalue_offset_eq ptr_add_def
               array_ptr_index_def
               h_val_word32 h_val_ptr
               upt_rec take_heap_list_min drop_heap_list_general
        field_to_bytes_rewrites)

  apply (rule double_heap_update_eq[symmetric])

thm cteInsert_body_def


  apply (tafctic {* ALLGOALS (nth (tacs @{context}) 3) *})[1]

  apply (tactic {* ALLGOALS (nth (tacs @{context}) 4) *})

  apply (tactic {* ALLGOALS (nth (tacs @{context}) 5) *})

  apply (tactic {* ALLGOALS (nth (tacs @{context}) 6) *})

  apply (simp_all add: h_val_ptr h_val_word32)
using [[show_consts]]

term "drop_sign x"
using [[show_types]]
thm drop_sign_isomorphism_bitwise(10)[where 'a=32]
using [[simp_trace]]
apply (tactic {* ALLGOALS (full_simp_tac (put_simpset HOL_basic_ss @{context}
      addsimps @{thms drop_sign_isomorphism_bitwise(10)})) *})


  apply (tactifc {* ALLGOALS (nth (tacs @{context}) 7) *})

done



end
