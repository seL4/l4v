(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
   Test proofs for corres methods. Builds on AInvs image.
*)

theory Corres_Test
imports "../proof/refine/ARM/VSpace_R" Corres_Method
begin

context begin interpretation Arch .

(* VSpace_R *)


lemma invalidate_asid_entry_corres:
  notes [where pd=pd, corres] =
    load_hw_asid_corres
    invalidate_asid_corres
  notes [corres] =
    invalidate_hw_asid_entry_corres
  shows
  "corres dc (valid_arch_objs and valid_asid_map
                and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0)
                and vspace_at_asid asid pd and valid_vs_lookup
                and unique_table_refs o caps_of_state
                and valid_global_objs and valid_arch_state
                and pspace_aligned and pspace_distinct)
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             (invalidate_asid_entry asid) (invalidateASIDEntry asid)"
  apply (simp add: invalidate_asid_entry_def invalidateASIDEntry_def)
  apply_debug (trace) (* apply_trace between steps *)
   (tags "corres") (* break at breakpoints labelled "corres" *)
   corres (* weaken precondition *)
   continue (* split *)
   continue (* solve load_hw_asid *)
   continue (* split *)
   continue (* apply corres_when *)
   continue (* trivial simplification *)
   continue (* invalidate _hw_asid_entry *)
   finish (* invalidate_asid *)

  apply (wp load_hw_asid_wp | simp)+
  apply (fastforce simp: pd_at_asid_uniq)
  done

(* Push assumptions into precondition *)

lemma set_asid_pool_corres:
  "corres dc (asid_pool_at p and valid_etcbs and K (a = inv ASIDPool a' o ucast)) (asid_pool_at' p)
            (set_asid_pool p a) (setObject p a')"
   apply (rule corres_name_pre)
   apply simp
   apply (rule corres_guard_imp)
   apply (rule set_asid_pool_corres)
   by simp+

crunch typ_at'[wp]: invalidateASIDEntry, flushSpace "typ_at' T t"
crunch pspace_aligned'[wp]: invalidateASIDEntry "pspace_aligned'"
crunch pspace_distinct'[wp]: invalidateASIDEntry "pspace_distinct'"
crunch ksCurThread[wp]: invalidateASIDEntry, flushSpace "\<lambda>s. P (ksCurThread s)"
crunch obj_at'[wp]: invalidateASIDEntry, flushSpace "obj_at' P p"


lemma delete_asid_corresb:
  notes [where pd=pd, corres] =
    flush_space_corres invalidate_asid_entry_corres

  notes [corres] = corres_gets_asid get_asid_pool_corres_inv'
                   invalidate_asid_entry_corres
                   set_asid_pool_corres gct_corres
                   set_vm_root_corres
  notes [wp] = set_asid_pool_asid_map_unmap[unfolded fun_upd_def] set_asid_pool_vs_lookup_unmap'
               set_asid_pool_arch_objs_unmap'
               invalidate_asid_entry_invalidates
               getASID_wp
  shows
  "corres dc
          (invs and valid_etcbs and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0))
          (pspace_aligned' and pspace_distinct' and no_0_obj'
              and valid_arch_state' and cur_tcb')
          (delete_asid asid pd) (deleteASID asid pd)"
  apply (simp add: delete_asid_def deleteASID_def)
  apply_debug (trace) (* apply_trace between steps *)
    (tags "corres") (* break at breakpoints labelled "corres" *)
    (corres | (corresc, #break))+ (* weaken precondition *)
    continue (* split *)
    continue (* gets rule *)
    continue (* simplification *)
    continue (* backtracking (no corres progress after simp) *)
    continue (* continue backtracking *)
    continue (* case split with corresc *)
    continue (* focus on first goal *)
    continue (* trivially solved *)
    continue (* split *)
    continue (* simplification *)
    continue (* successful corres_once with liftM after simplification *)
    continue (* get_asid_pool applied *)
    continue (* simplification *)
    continue (* when rule *)
    continue (* split *)
    continue (* flush_space corres rule *)
    continue (* split *)
    continue (* apply invalidate_asid_entry_corres (issue with tracing?) *)
    continue (* split *)
    continue (* set_asid_pool (issue with tracing?) *)
    continue (* split *)
    continue (* gets rule *)
    continue (* simplification *)
    finish (* set_vm_root *)
  apply (wp | simp add: mask_asid_low_bits_ucast_ucast | fold cur_tcb_def | wps)+
  apply (rule conjI)
  apply (intro impI allI)
  apply (rule context_conjI)
  apply (fastforce simp: o_def dest: valid_asid_tableD invs_valid_asid_table)
  apply (intro allI impI)
  apply (subgoal_tac "vspace_at_asid asid pd s")
  prefer 2
  apply (simp add: vspace_at_asid_def)
         apply (rule vs_lookupI)
        apply (simp add: vs_asid_refs_def)
        apply (rule image_eqI[OF refl])
        apply (rule graph_ofI)
        apply fastforce
        apply (rule r_into_rtrancl)
               apply simp
       apply (rule vs_lookup1I [OF _ _ refl], assumption)
       apply (simp add: vs_refs_def)
       apply (rule image_eqI[rotated], erule graph_ofI)
       apply (simp add: mask_asid_low_bits_ucast_ucast)
  apply (simp add: o_def)
  apply (safe; assumption?)
 apply (simp add: inv_def mask_asid_low_bits_ucast_ucast)
  apply (rule ext)
  apply clarsimp
  apply (fastforce dest: ucast_ucast_eq)
  apply (erule ko_at_weakenE)
  apply (clarsimp simp: graph_of_def)
  apply (fastforce split: if_split_asm)
  apply clarsimp
  apply (frule invs_arch_objs)
  apply (drule (2) valid_arch_objsD)
  apply (erule ranE)
  apply (fastforce split: if_split_asm)
    apply (erule ko_at_weakenE)
  apply (clarsimp simp: graph_of_def)
  apply (fastforce split: if_split_asm)
  apply clarsimp
  apply safe
  apply (simp add: typ_at_to_obj_at_arches)
  apply (clarsimp simp add: obj_at'_def)
  apply (simp add: cur_tcb'_def)
  done

lemma getSlotCap_corres:
  "corres cap_relation (K(cte_ptr' = cte_map cte_ptr ) and cte_wp_at (\<lambda>_. True) cte_ptr) (pspace_distinct' and pspace_aligned')
 (get_cap cte_ptr) (getSlotCap cte_ptr')"
 apply (rule corres_name_pre)
 apply (rule corres_guard_imp)
 apply (rule getSlotCap_corres)
 by simp+

lemma cte_wp_at_ex:
  "cte_wp_at (\<lambda>_. True) p s \<Longrightarrow> (\<exists>cap. cte_wp_at (op = cap) p s)"
  by (simp add: cte_wp_at_def)

lemma set_vm_root_for_flush_corres:
  notes [corres] = gct_corres getSlotCap_corres
  shows
  "corres (op =)
          (cur_tcb and vspace_at_asid asid pd
           and K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits)
           and valid_asid_map and valid_vs_lookup
           and valid_arch_objs and valid_global_objs
           and unique_table_refs o caps_of_state
           and valid_arch_state
           and pspace_aligned and pspace_distinct)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (set_vm_root_for_flush pd asid)
          (setVMRootForFlush pd asid)"
  apply (simp add: set_vm_root_for_flush_def setVMRootForFlush_def getThreadVSpaceRoot_def locateSlot_conv)
  apply corres
  apply_debug (trace) (tags "corres_search")
     (corres_search search: arm_context_switch_corres)
    continue (* step left *)
    continue (* if rule *)
    continue (* failed corres on first subgoal, trying next *)
    continue (* fail corres on last subgoal, trying reverse if rule *)
    continue (* successful goal discharged by corres *)
    finish (* successful terminal goal discharged by corres_once with given rule *)

  apply corres+
  apply (wp get_cap_wp getSlotCap_wp | wpc| simp)+
  apply (rule context_conjI)
  subgoal by (simp add: cte_map_def objBits_simps tcb_cnode_index_def
                         tcbVTableSlot_def to_bl_1 cte_level_bits_def)
  apply (rule context_conjI)
          subgoal by (fastforce simp: cur_tcb_def intro!: tcb_at_cte_at_1[simplified])
          apply (rule conjI)
          subgoal by (auto simp: isCap_simps)
          apply (drule cte_wp_at_ex)
          apply clarsimp
          apply (drule (1) pspace_relation_cte_wp_at[rotated 1]; (assumption | clarsimp)?)
          apply (drule cte_wp_at_norm')
          apply clarsimp
          apply (rule_tac x="cteCap cte" in exI)
          subgoal premises prems for s s' cap cte
          apply safe
          apply (thin_tac _)+
          subgoal cte_wp_at'
          apply (insert prems)
          apply (rule rsubst[where P="\<lambda>s. cte_wp_at' x s s'" for x])
          apply (erule cte_wp_at_weakenE', simp)
          apply (clarsimp dest!: curthread_relation)
          done
          apply (safe intro!: cte_wp_at')
        done
        done


end
end
