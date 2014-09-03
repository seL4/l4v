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

lemma involution_member_def:
  "\<lbrakk> \<And>x. f (f x) = x \<rbrakk> \<Longrightarrow> (x \<in> f ` S) = (f x \<in> S)"
  apply (safe, simp_all)
  apply (erule image_eqI[rotated])
  apply simp
  done

instance ptr :: (c_type)oneMB_packed ..
instance tcb_queue_C :: oneMB_packed ..
instance region_C :: oneMB_packed ..

context substitute_pre begin

lemmas globals_list_def = kernel_all_global_addresses.global_data_list_def
lemmas global_data_defs = kernel_all_global_addresses.global_data_defs

lemma globals_list_valid:
  "globals_list_valid t_hrs_' t_hrs_'_update globals_list"
  apply (rule globals_list_valid_optimisation)
  apply (simp_all add: globals_list_def globals_list_valid_def
                       global_data_defs
                  del: distinct_prop.simps split del: split_if)
   apply (simp add: global_data_swappable_def global_data_def)
  apply (simp_all add: global_data_valid)
  apply (simp_all add: global_data_valid_def addressed_global_data_def
                   const_global_data_def
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

lemma globals_swap_bij:
  "globals_list_distinct D symbol_table globals_list
    \<Longrightarrow> bij gswap"
  apply (rule bijI)
   apply (rule inj_onI)
   apply (drule_tac f=gswap in arg_cong)
   apply (simp add: globals_swap_twice)
  apply (rule_tac f="gswap" in surjI)
  apply (simp add: globals_swap_twice)
  done

lemma globals_update_globals_swap_bij:
  "globals_list_distinct D symbol_table globals_list
    \<Longrightarrow> bij (globals_update gswap)"
  apply (intro bijI inj_onI surjI[where f="globals_update gswap"])
   apply (drule arg_cong[where f="globals_update gswap"])
   apply (simp_all add: o_def globals_swap_twice)
  apply (erule trans[OF trans, rotated], simp+)
  done

lemma globals_swap_eqI:
  "\<lbrakk> g = gswap g';
    globals_list_distinct D symbol_table globals_list \<rbrakk>
     \<Longrightarrow> gswap g = g'"
  by (simp add: globals_swap_twice)

lemma globals_update_globals_swap_eqI:
  "\<lbrakk> g = globals_update gswap g';
    globals_list_distinct D symbol_table globals_list \<rbrakk>
     \<Longrightarrow> globals_update gswap g = g'"
  by (simp add: o_def globals_swap_twice)

lemmas globals_unfold = globals_swap_def global_swap_def
    globals_list_def global_data_def split_def

lemma globals_update_globals_swap_twice:
  "globals_list_distinct D symbol_table globals_list
    \<Longrightarrow> globals_update gswap
    (globals_update gswap gs) = gs"
  by (simp add: globals_swap_twice)

lemmas involution_member_defs
    = involution_member_def[OF globals_update_globals_swap_twice]
        involution_member_def[OF globals_swap_twice]

lemmas msb_0 = msb_nth[where w=0, simplified]

lemma heap_update_Array_element_thrs:
  fixes ptr :: "(('a :: packed_type)['b :: finite]) ptr"
  shows "\<lbrakk> n < CARD('b) \<and> CARD('b) * size_of TYPE('a) < 2 ^ 32 \<rbrakk>
    \<Longrightarrow> t_hrs_'_update (hrs_mem_update (heap_update ptr
             (Arrays.update (h_val (hrs_mem (t_hrs_' gs)) ptr) n v))) gs
        = t_hrs_'_update (hrs_mem_update (heap_update (CTypesDefs.ptr_add (ptr_coerce ptr) (of_nat n)) v)) gs"
  apply (rule globals.fold_congs[OF refl refl], clarsimp)
  apply (simp add: hrs_mem_update_def hrs_mem_def heap_update_Array_element'[OF refl])
  done

lemma unat_ucast_less_helper:
  "ucast (x :: word8) < (of_nat m :: word32) \<Longrightarrow> unat x < m"
  by (simp add: unat_ucast_8_32[symmetric] unat_less_helper)

lemma globals_list_distinct_filter_member:
  "x \<in> set xs \<Longrightarrow> globals_list_distinct D symtab xs
    \<Longrightarrow> \<not> P x
    \<Longrightarrow> globals_list_distinct (global_data_region symtab x) symtab
        (filter P xs)"
  apply (clarsimp simp: globals_list_distinct_def)
  apply (rule conjI)
   apply (clarsimp simp: in_set_conv_decomp[where x="x"]
                         distinct_prop_append)
   apply auto[1]
  apply (simp add: distinct_prop_map distinct_prop_filter)
  apply (erule distinct_prop_weaken, simp)
  done

lemma s_footprint_intvl:
  "s_footprint (p :: 'a ptr) \<subseteq> {ptr_val p ..+ size_of TYPE ('a :: c_type)} \<times> UNIV"
  by (auto simp: s_footprint_def s_footprint_untyped_def
                 intvl_def size_of_def)

lemma h_val_globals_swap_in_const_global:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
        globals_list_distinct D symtab xs;
        const_global_data s (v :: 'a :: c_type) \<in> set xs;
        unat offs + size_of TYPE('b) \<le> size_of TYPE('a) \<rbrakk>
    \<Longrightarrow> h_val (hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs gs)))
            (Ptr (symtab s + offs) :: ('b :: c_type) ptr)
         = h_val (hrs_mem (g_hrs gs)) (Ptr (symtab s + offs))"
  apply (erule disjoint_h_val_globals_swap_filter,
    erule(1) globals_list_distinct_filter_member)
   apply simp
  apply (rule order_trans, rule s_footprint_intvl)
  apply (simp add: global_data_region_def const_global_data_def
                   Times_subset_cancel2)
  apply (erule intvl_sub_offset)
  done

lemmas h_val_globals_swap_in_const_global_both
    = h_val_globals_swap_in_const_global
        h_val_globals_swap_in_const_global[where offs=0, simplified]

lemma const_globals_in_memory_to_h_val_with_swap:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
    globals_list_distinct D symtab xs;
    const_global_data nm v \<in> set xs;
    const_globals_in_memory symtab xs (hrs_mem (g_hrs gs)) \<rbrakk>
    \<Longrightarrow> v = h_val (hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs gs)))
        (Ptr (symtab nm))"
  apply (subst disjoint_h_val_globals_swap_filter, assumption,
    erule(1) globals_list_distinct_filter_member)
    apply simp
   apply (simp add: global_data_region_def const_global_data_def)
   apply (rule order_trans, rule s_footprint_intvl)
   apply simp
  apply (erule(1) const_globals_in_memory_h_val[symmetric])
  done

ML {*
fun add_globals_swap_rewrites member_thms ctxt = let
    val gav = Proof_Context.get_thm ctxt "global_acc_valid"
    val glv = Proof_Context.get_thm ctxt "globals_list_valid"
    val gld = Proof_Context.get_thm ctxt "globals_list_distinct"
    val acc = [Thm.trivial @{cpat "PROP ?P"}, gav, glv, gld]
        MRS @{thm globals_swap_access_mem2}
    val upd = [Thm.trivial @{cpat "PROP ?P"}, gav, glv, gld]
        MRS @{thm globals_swap_update_mem2}
    val cg_with_swap = [gav, gld]
        MRS @{thm const_globals_in_memory_to_h_val_with_swap}
    val empty_ctxt = put_simpset HOL_basic_ss ctxt
    fun unfold_mem thm = let
        val (x, _) = HOLogic.dest_mem (HOLogic.dest_Trueprop (concl_of thm))
        val (s, _) = dest_Const (head_of x)
      in if s = @{const_name global_data} orelse s = @{const_name const_global_data}
        orelse s = @{const_name addressed_global_data}
        then thm
        else simplify (empty_ctxt addsimps [Proof_Context.get_thm ctxt (s ^ "_def")]) thm
      end

    val member_thms = map unfold_mem member_thms

    val globals_swap_rewrites = member_thms RL [acc, upd]
    val const_globals_rewrites = member_thms RL @{thms const_globals_in_memory_h_val[symmetric]}
    val const_globals_swap_rewrites = member_thms RL [cg_with_swap]
  in ctxt
    |> Local_Theory.note ((@{binding "globals_swap_rewrites"}, []),
            globals_swap_rewrites)
    |> snd
    |> Local_Theory.note ((@{binding "const_globals_rewrites"}, []),
            const_globals_rewrites)
    |> snd
    |> Local_Theory.note ((@{binding "const_globals_rewrites_with_swap"}, []),
            const_globals_swap_rewrites)
    |> snd
  end
*}

end

end

