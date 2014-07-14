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

lemmas globals_list_mems = kernel_all_global_addresses.global_data_mems

ML {*
val globals_swap_rewrites = @{thms globals_list_mems[unfolded global_data_defs]}
    RL @{thms
        globals_swap_update_mem[OF _ global_acc_valid globals_list_valid]
        globals_swap_access_mem[OF _ global_acc_valid globals_list_valid]}
*}

end

end

