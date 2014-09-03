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

ML {* SimplToGraphProof.globals_swap
 := (fn t => @{term "globals_swap t_hrs_' t_hrs_'_update symbol_table globals_list"} $ t)
*}

local_setup {* add_globals_swap_rewrites @{thms kernel_all_global_addresses.global_data_mems} *}

definition
  simpl_invariant :: "globals myvars set"
where
  "simpl_invariant = {s. const_globals_in_memory symbol_table globals_list
            (hrs_mem (t_hrs_' (globals s)))
        \<and> htd_safe domain (hrs_htd (t_hrs_' (globals s)))}"

ML {* ProveSimplToGraphGoals.test_all_graph_refine_proofs_after
    funs (csenv ()) @{context} NONE  *} 

end
