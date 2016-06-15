(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
 Arch-specific retype invariants
*)

theory ArchRetype_AI
imports "../Retype_AI"
begin

context Arch begin global_naming ARM

named_theorems Retype_AI_assms

lemma clearMemoryVM_return[simp, Retype_AI_assms]:
  "clearMemoryVM a b = return ()"
  by (simp add: clearMemoryVM_def)

lemma slot_bits_def2 [Retype_AI_assms]: "slot_bits = cte_level_bits"
  by (simp add: slot_bits_def cte_level_bits_def)

definition
  "no_gs_types \<equiv> UNIV - {Structures_A.CapTableObject,
     ArchObject SmallPageObj, ArchObject LargePageObj,
     ArchObject SectionObj, ArchObject SuperSectionObj}"

lemma no_gs_types_simps [simp, Retype_AI_assms]:
  "Untyped \<in> no_gs_types"
  "TCBObject \<in> no_gs_types"
  "EndpointObject \<in> no_gs_types"
  "NotificationObject \<in> no_gs_types"
  "ArchObject PageTableObj \<in> no_gs_types"
  "ArchObject PageDirectoryObj \<in> no_gs_types"
  "ArchObject ASIDPoolObj \<in> no_gs_types"
  by (simp_all add: no_gs_types_def)

lemma retype_region_ret_folded [Retype_AI_assms]:
  "\<lbrace>\<top>\<rbrace> retype_region y n bits ty 
   \<lbrace>\<lambda>r s. r = retype_addrs y ty n bits\<rbrace>"
  unfolding retype_region_def
  apply (simp add: pageBits_def)
  apply wp
   apply (simp add:retype_addrs_def)
  done

declare store_pde_state_refs_of [wp]

(* FIXME: move to Machine_R.thy *)
lemma clearMemory_corres:
  "corres_underlying Id False True dc \<top> (\<lambda>_. is_aligned y 2)
     (clearMemory y a) (clearMemory y a)"
  apply (rule corres_Id)
   apply simp+
  done

(* These also prove facts about copy_global_mappings *)
crunch pspace_aligned[wp]: init_arch_objects "pspace_aligned"
  (ignore: clearMemory wp: crunch_wps)
crunch pspace_distinct[wp]: init_arch_objects "pspace_distinct"
  (ignore: clearMemory wp: crunch_wps)
crunch mdb_inv[wp]: init_arch_objects "\<lambda>s. P (cdt s)"
  (ignore: clearMemory wp: crunch_wps)
crunch valid_mdb[wp]: init_arch_objects "valid_mdb"
  (ignore: clearMemory wp: crunch_wps)
crunch cte_wp_at[wp]: init_arch_objects "\<lambda>s. P (cte_wp_at P' p s)"
  (ignore: clearMemory wp: crunch_wps)
crunch typ_at[wp]: init_arch_objects "\<lambda>s. P (typ_at T p s)"
  (ignore: clearMemory wp: crunch_wps)

lemma mdb_cte_at_store_pde[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s)\<rbrace>
   store_pde y pde
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
done

lemma get_pde_valid[wp]:
  "\<lbrace>valid_arch_objs 
    and \<exists>\<rhd> (x && ~~mask pd_bits) 
    and K (ucast (x && mask pd_bits >> 2) \<notin> kernel_mapping_slots)\<rbrace> 
   get_pde x 
   \<lbrace>valid_pde\<rbrace>"
  apply (simp add: get_pde_def)
  apply wp
  apply clarsimp
  apply (drule (2) valid_arch_objsD)
  apply simp
  done

lemma get_master_pde_valid[wp]:
  "\<lbrace>valid_arch_objs
    and \<exists>\<rhd> (x && ~~mask pd_bits)
    and K (ucast (x && mask pd_bits >> 2) \<notin> kernel_mapping_slots)\<rbrace>
   get_master_pde x
   \<lbrace>valid_pde\<rbrace>"
  apply (simp add: get_master_pde_def get_pde_def)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift | wpc)+
     defer
     apply (clarsimp simp: mask_lower_twice pd_bits_def pageBits_def)+
  apply (drule sym)
  apply (drule (1) ko_at_obj_congD, clarsimp)
  apply (drule (2) valid_arch_objsD)
  apply simp
  apply (erule notE, erule bspec)
  apply (clarsimp simp: kernel_mapping_slots_def not_le)
  apply (erule le_less_trans[rotated])
  apply (rule ucast_mono_le)
   apply (rule le_shiftr)
   apply (clarsimp simp: word_bw_comms)
   apply (clarsimp simp: word_bool_alg.conj_assoc[symmetric])
   apply (subst word_bw_comms, rule word_and_le2)
  apply (rule shiftr_less_t2n)
  apply (clarsimp simp: pd_bits_def pageBits_def and_mask_less'[where n=14, simplified])
  done


lemma get_pde_wellformed[wp]:
  "\<lbrace>valid_objs\<rbrace> get_pde x \<lbrace>\<lambda>rv _. wellformed_pde rv\<rbrace>"
  apply (simp add: get_pde_def)
  apply wp
  apply (fastforce simp add: valid_objs_def dom_def obj_at_def valid_obj_def)
  done

crunch valid_objs[wp]: init_arch_objects "valid_objs"
  (ignore: clearMemory wp: crunch_wps)

lemma set_pd_arch_state[wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_pd ptr val \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (rule set_pd_valid_arch)

crunch valid_arch_state[wp]: init_arch_objects "valid_arch_state"
  (ignore: clearMemory set_object wp: crunch_wps)

lemmas init_arch_objects_valid_cap[wp] = valid_cap_typ [OF init_arch_objects_typ_at]

lemmas init_arch_objects_cap_table[wp] = cap_table_at_lift_valid [OF init_arch_objects_typ_at]

lemma clearMemory_vms:
  "valid_machine_state s \<Longrightarrow>
   \<forall>x\<in>fst (clearMemory ptr bits (machine_state s)).
     valid_machine_state (s\<lparr>machine_state := snd x\<rparr>)"
  apply (clarsimp simp: valid_machine_state_def
                        disj_commute[of "in_user_frame p s" for p s])
  apply (drule_tac x=p in spec, simp)
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = 0"
         in use_valid[where P=P and Q="\<lambda>_. P" for P], simp_all)
  apply (simp add: clearMemory_def cleanCacheRange_PoU_def machine_op_lift_def
                   machine_rest_lift_def split_def)
  apply (wp hoare_drop_imps | simp | wp mapM_x_wp_inv)+
  apply (simp add: storeWord_def | wp)+
  apply (simp add: word_rsplit_0)
  done

lemma create_word_objects_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace>
   create_word_objects ptr bits sz
   \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (clarsimp simp: create_word_objects_def
    reserve_region_def mapM_x_mapM do_machine_op_return_foo)
  apply (rule hoare_pre)
  apply wp
  apply (subst dom_mapM)
    apply ((simp add:clearMemory_def
      | wp empty_fail_cleanCacheRange_PoU ef_storeWord
      empty_fail_mapM_x empty_fail_bind)+)[1]
   apply (wp mapM_wp')
  apply (clarsimp simp: create_word_objects_def reserve_region_def
    clearMemory_vms
    do_machine_op_def split_def | wp)+
  done

lemma create_word_objects_valid_irq_states[wp]:
  "\<lbrace>valid_irq_states\<rbrace>
   create_word_objects ptr bits sz
   \<lbrace>\<lambda>_. valid_irq_states\<rbrace>"
  apply (clarsimp simp: create_word_objects_def
    reserve_region_def mapM_x_mapM do_machine_op_return_foo)
  apply (rule hoare_pre)
  apply wp
  apply (subst dom_mapM)
    apply ((simp add:clearMemory_def
      | wp empty_fail_cleanCacheRange_PoU ef_storeWord
      empty_fail_mapM_x empty_fail_bind)+)[1]
   apply (wp mapM_wp' | simp add: do_machine_op_def | wpc)+
   apply clarsimp
   apply (erule use_valid)
   apply (simp add: valid_irq_states_def | wp no_irq_clearMemory no_irq)+
  done

lemma create_word_objects_invs[wp]:
  "\<lbrace>invs\<rbrace> create_word_objects ptr bits sz \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add:invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post)
    apply (rule hoare_vcg_conj_lift[OF create_word_objects_vms])
    apply (rule hoare_vcg_conj_lift[OF create_word_objects_valid_irq_states])
    prefer 2
    apply clarsimp
    apply assumption
   apply (clarsimp simp: create_word_objects_def reserve_region_def
                        split_def do_machine_op_def)
   apply wp
  apply (simp add: invs_def cur_tcb_def valid_state_def)
  done

crunch invs [wp]: reserve_region "invs"

crunch invs [wp]: reserve_region "invs"

crunch iflive[wp]: copy_global_mappings "if_live_then_nonz_cap"
  (wp: crunch_wps)

crunch zombies[wp]: copy_global_mappings "zombies_final"
  (wp: crunch_wps)

crunch state_refs_of[wp]: copy_global_mappings "\<lambda>s. P (state_refs_of s)"
  (wp: crunch_wps)

crunch valid_idle[wp]: copy_global_mappings "valid_idle"
  (wp: crunch_wps)

crunch only_idle[wp]: copy_global_mappings "only_idle"
  (wp: crunch_wps)

crunch ifunsafe[wp]: copy_global_mappings "if_unsafe_then_cap"
  (wp: crunch_wps)

crunch reply_caps[wp]: copy_global_mappings "valid_reply_caps"
  (wp: crunch_wps)

crunch reply_masters[wp]: copy_global_mappings "valid_reply_masters"
  (wp: crunch_wps)

crunch valid_global[wp]: copy_global_mappings "valid_global_refs"
  (wp: crunch_wps)

crunch irq_node[wp]: copy_global_mappings "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

crunch irq_states[wp]: copy_global_mappings "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

crunch caps_of_state[wp]: copy_global_mappings "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps)

crunch pspace_in_kernel_window[wp]: copy_global_mappings "pspace_in_kernel_window"
  (wp: crunch_wps)

crunch cap_refs_in_kernel_window[wp]: copy_global_mappings "cap_refs_in_kernel_window"
  (wp: crunch_wps)


(* FIXME: move to VSpace_R *)
lemma vs_refs_add_one'':
  "p \<in> kernel_mapping_slots \<Longrightarrow>
   vs_refs (ArchObj (PageDirectory (pd(p := pde)))) =
   vs_refs (ArchObj (PageDirectory pd))"
 by (auto simp: vs_refs_def graph_of_def split: split_if_asm)


lemma glob_vs_refs_add_one':
  "glob_vs_refs (ArchObj (PageDirectory (pd(p := pde)))) =
   glob_vs_refs (ArchObj (PageDirectory pd)) 
   - Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref (pd p)) 
   \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref pde)"
  apply (simp add: glob_vs_refs_def)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp del: disjCI dest!: graph_ofD split: split_if_asm)
   apply (rule disjI1)
   apply (rule conjI)
    apply (rule_tac x="(aa, ba)" in image_eqI)
     apply simp
    apply (simp add:  graph_of_def)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp dest!: graph_ofD)
   apply (rule_tac x="(aa,ba)" in image_eqI)
    apply simp
   apply (clarsimp simp: graph_of_def)
  apply clarsimp
  apply (rule_tac x="(p,x)" in image_eqI)
   apply simp
  apply (clarsimp simp: graph_of_def)
  done


lemma store_pde_map_global_valid_arch_caps:
  "\<lbrace>valid_arch_caps and valid_objs and valid_arch_objs
     and valid_arch_state and valid_global_objs
     and K (valid_pde_mappings pde)
     and K (VSRef (p && mask pd_bits >> 2) (Some APageDirectory)
                \<in> kernel_vsrefs)
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p
             \<longrightarrow> p \<in> set (arm_global_pts (arch_state s)))\<rbrace>
      store_pde p pde
   \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  apply (simp add: store_pde_def)
  apply (wp set_pd_valid_arch_caps
            [where T="{}" and S="{}" and T'="{}" and S'="{}"])
  apply (clarsimp simp:obj_at_def kernel_vsrefs_kernel_mapping_slots[symmetric])
  apply (intro conjI)
       apply (erule vs_refs_add_one'')
      apply (rule set_eqI)
      apply (clarsimp simp add:  vs_refs_pages_def graph_of_def image_def)
      apply (rule arg_cong[where f=Ex], rule ext, fastforce)
     apply clarsimp
     apply (rule conjI, clarsimp)
     apply (drule valid_arch_objsD, simp add: obj_at_def, simp+)[1]
    apply (rule impI, rule disjI2)
    apply (simp add: empty_table_def)
   apply clarsimp
   apply (rule conjI, clarsimp)
   apply (thin_tac "All P" for P)
   apply clarsimp
   apply (frule_tac ref'="VSRef (ucast c) (Some APageDirectory) # r" and
                    p'=q in vs_lookup_pages_step)
    apply (clarsimp simp: vs_lookup_pages1_def vs_refs_pages_def
                          obj_at_def graph_of_def image_def)
   apply (clarsimp simp: valid_arch_caps_def valid_vs_lookup_def)
  apply clarsimp
  apply (rule conjI, clarsimp)
  apply (thin_tac "All P" for P)
  apply clarsimp
  apply (drule_tac ref'="VSRef (ucast c) (Some APageDirectory) # r" and
                   p'=q in vs_lookup_pages_step)
   apply (clarsimp simp: vs_lookup_pages1_def vs_refs_pages_def
                         obj_at_def graph_of_def image_def)
  apply (drule_tac ref'="VSRef (ucast d) (Some APageTable) #
                         VSRef (ucast c) (Some APageDirectory) # r" and
                   p'=q' in vs_lookup_pages_step)
   apply (fastforce simp: vs_lookup_pages1_def vs_refs_pages_def
                         obj_at_def graph_of_def image_def)
  apply (clarsimp simp: valid_arch_caps_def valid_vs_lookup_def)
  done


lemma store_pde_map_global_valid_arch_objs:
  "\<lbrace>valid_arch_objs and valid_arch_state and valid_global_objs
     and K (valid_pde_mappings pde)
     and K (VSRef (p && mask pd_bits >> 2) (Some APageDirectory)
                \<in> kernel_vsrefs)
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p
             \<longrightarrow> p \<in> set (arm_global_pts (arch_state s)))\<rbrace>
        store_pde p pde
   \<lbrace>\<lambda>rv. valid_arch_objs\<rbrace>"
  apply (simp add: store_pde_def)
  apply (wp set_pd_arch_objs_map[where T="{}" and S="{}"])
  apply (clarsimp simp:obj_at_def kernel_vsrefs_kernel_mapping_slots[symmetric])
  apply (intro conjI)
   apply (erule vs_refs_add_one'')
  apply clarsimp
  apply (drule valid_arch_objsD, simp add: obj_at_def, simp+)
  apply clarsimp
  done


lemma store_pde_global_objs[wp]:
  "\<lbrace>valid_global_objs and valid_global_refs and
    valid_arch_state and
    (\<lambda>s. (\<forall>pd. (obj_at (empty_table (set (arm_global_pts (arch_state s))))
                   (p && ~~ mask pd_bits) s
           \<and> ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s
             \<longrightarrow> empty_table (set (arm_global_pts (arch_state s)))
                                 (ArchObj (PageDirectory (pd(ucast (p && mask pd_bits >> 2) := pde))))))
        \<or> (\<exists>slot. cte_wp_at (\<lambda>cap. p && ~~ mask pd_bits \<in> obj_refs cap) slot s))\<rbrace>
     store_pde p pde \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (simp add: store_pde_def)
  apply wp
  apply clarsimp
  done


lemma store_pde_valid_kernel_mappings_map_global:
  "\<lbrace>valid_kernel_mappings and valid_arch_state and valid_global_objs
     and K (VSRef (p && mask pd_bits >> 2) (Some APageDirectory)
                \<in> kernel_vsrefs)
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p
             \<longrightarrow> p \<in> set (arm_global_pts (arch_state s)))\<rbrace>
     store_pde p pde
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: store_pde_def)
  apply (wp set_pd_valid_kernel_mappings_map)
  apply (clarsimp simp: obj_at_def)
  apply (rule conjI, rule glob_vs_refs_add_one')
  apply (clarsimp simp: ucast_ucast_mask_shift_helper)
  done


crunch valid_asid_map[wp]: store_pde "valid_asid_map"

crunch cur[wp]: store_pde "cur_tcb"

lemma mapM_x_store_pde_eq_kernel_mappings_restr:
  "pd \<in> S \<and> is_aligned pd pd_bits \<and> is_aligned pd' pd_bits
        \<and> set xs \<subseteq> {..< 2 ^ (pd_bits - 2)}
     \<Longrightarrow>
   \<lbrace>\<lambda>s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>)\<rbrace>
     mapM_x (\<lambda>idx. get_pde (pd' + (idx << 2)) >>=
                   store_pde (pd + (idx << 2))) xs
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>)
               \<and> (\<forall>x \<in> set xs.
                    (\<exists>pdv pdv'. ko_at (ArchObj (PageDirectory pdv)) pd s
                      \<and> ko_at (ArchObj (PageDirectory pdv')) pd' s
                      \<and> pdv (ucast x) = pdv' (ucast x)))\<rbrace>"
  apply (induct xs rule: rev_induct, simp_all add: mapM_x_Nil mapM_x_append mapM_x_singleton)
  apply (erule hoare_seq_ext[rotated])
  apply (simp add: store_pde_def set_pd_def set_object_def cong: bind_cong)
  apply (wp get_object_wp get_pde_wp)
  apply (clarsimp simp: obj_at_def split del: split_if)
  apply (frule shiftl_less_t2n)
   apply (simp add: pd_bits_def pageBits_def)
  apply (simp add: is_aligned_add_helper split del: split_if)
  apply (cut_tac x=x and n=2 in shiftl_shiftr_id)
    apply (simp add: word_bits_def)
   apply (simp add: word_bits_def pd_bits_def pageBits_def)
   apply (erule order_less_le_trans, simp)
  apply (clarsimp simp: fun_upd_def[symmetric] is_aligned_add_helper)
  done


lemma equal_kernel_mappings_specific_def:
  "ko_at (ArchObj (PageDirectory pd)) p s
    \<Longrightarrow> equal_kernel_mappings s
          = (\<forall>p' pd'. ko_at (ArchObj (PageDirectory pd')) p' s
                        \<longrightarrow> (\<forall>w \<in> kernel_mapping_slots. pd' w = pd w))"
  apply (rule iffI)
   apply (clarsimp simp: equal_kernel_mappings_def)
  apply (clarsimp simp: equal_kernel_mappings_def)
  apply (subgoal_tac "pda w = pd w \<and> pd' w = pd w")
   apply (erule conjE, erule(1) trans[OF _ sym])
  apply blast
  done   

lemma copy_global_equal_kernel_mappings_restricted:
  "is_aligned pd pd_bits \<Longrightarrow>
   \<lbrace>\<lambda>s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- (insert pd S)) \<rparr>)
              \<and> arm_global_pd (arch_state s) \<notin> (insert pd S)
              \<and> pspace_aligned s \<and> valid_arch_state s\<rbrace>
     copy_global_mappings pd
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>)\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule_tac P="global_pd \<notin> (insert pd S)" in hoare_vcg_prop)
    apply (rule_tac P="is_aligned global_pd pd_bits"
           in hoare_gen_asm(1))
    apply (rule_tac S="insert pd S" in mapM_x_store_pde_eq_kernel_mappings_restr)
    apply clarsimp
    apply (erule order_le_less_trans)
    apply (simp add: pd_bits_def pageBits_def)
   apply (clarsimp simp: invs_aligned_pdD)
  apply clarsimp
  apply (frule_tac x="kernel_base >> 20" in spec)
  apply (drule mp)
   apply (simp add: kernel_base_def pd_bits_def pageBits_def)
  apply (clarsimp simp: obj_at_def)
  apply (case_tac "global_pd = pd")
   apply simp
  apply (subst equal_kernel_mappings_specific_def)
   apply (fastforce simp add: obj_at_def restrict_map_def)
  apply (subst(asm) equal_kernel_mappings_specific_def)
   apply (fastforce simp add: obj_at_def restrict_map_def)
  apply (clarsimp simp: restrict_map_def obj_at_def)
  apply (drule_tac x="ucast w" in spec, drule mp)
   apply (clarsimp simp: kernel_mapping_slots_def)
   apply (rule conjI)
    apply (simp add: word_le_nat_alt unat_ucast_kernel_base_rshift)
    apply (simp only: unat_ucast, subst mod_less)
     apply (rule order_less_le_trans, rule unat_lt2p)
     apply simp
    apply simp
   apply (rule minus_one_helper3)
   apply (rule order_less_le_trans, rule ucast_less)
    apply simp
   apply (simp add: pd_bits_def pageBits_def)
  apply (simp add: ucast_down_ucast_id word_size source_size_def
                   target_size_def is_down_def)
  apply (drule_tac x=p' in spec)
  apply (simp split: split_if_asm)
  done

lemma store_pde_valid_global_pd_mappings[wp]:
  "\<lbrace>valid_global_objs and valid_global_pd_mappings
          and (\<lambda>s. p && ~~ mask pd_bits \<notin> global_refs s)\<rbrace>
     store_pde p pde
   \<lbrace>\<lambda>rv. valid_global_pd_mappings\<rbrace>"
  apply (simp add: store_pde_def set_pd_def)
  apply (wp set_object_global_pd_mappings get_object_wp)
  apply simp
  done

lemma store_pde_valid_ioc[wp]:
 "\<lbrace>valid_ioc\<rbrace> store_pde ptr pde \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (simp add: store_pde_def, wp) simp


lemma store_pde_vms[wp]:
 "\<lbrace>valid_machine_state\<rbrace> store_pde ptr pde \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (simp add: store_pde_def, wp) clarsimp

crunch valid_irq_states[wp]: store_pde "valid_irq_states"

lemma copy_global_invs_mappings_restricted:
  "\<lbrace>(\<lambda>s. all_invs_but_equal_kernel_mappings_restricted (insert pd S) s)
          and (\<lambda>s. insert pd S \<inter> global_refs s = {})
          and K (is_aligned pd pd_bits)\<rbrace>
     copy_global_mappings pd
   \<lbrace>\<lambda>rv. all_invs_but_equal_kernel_mappings_restricted S\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: valid_pspace_def pred_conj_def)
  apply (rule hoare_conjI, wp copy_global_equal_kernel_mappings_restricted)
    apply assumption
   apply (clarsimp simp: global_refs_def)
  apply (rule valid_prove_more, rule hoare_vcg_conj_lift, rule hoare_TrueI)
  apply (simp add: copy_global_mappings_def valid_pspace_def)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp[where S="{x. kernel_base >> 20 \<le> x
                                       \<and> x < 2 ^ (pd_bits - 2)}"])
    apply simp_all
   apply (rule hoare_pre)
    apply (wp valid_irq_node_typ valid_irq_handlers_lift
              store_pde_map_global_valid_arch_caps
              store_pde_map_global_valid_arch_objs
              store_pde_valid_kernel_mappings_map_global
              get_pde_wp)
   apply (clarsimp simp: valid_global_objs_def)
   apply (frule(1) invs_aligned_pdD)
   apply (frule shiftl_less_t2n)
    apply (simp add: pd_bits_def pageBits_def)
   apply (clarsimp simp: is_aligned_add_helper)
   apply (cut_tac x=x and n=2 in shiftl_shiftr_id)
     apply (simp add: word_bits_def)
    apply (erule order_less_le_trans)
    apply (simp add: word_bits_def pd_bits_def pageBits_def)
   apply (rule conjI)
    apply (simp add: valid_objs_def dom_def obj_at_def valid_obj_def)
    apply (drule spec, erule impE, fastforce, clarsimp)
   apply (clarsimp simp: obj_at_def empty_table_def kernel_vsrefs_def)
  apply clarsimp
  apply (erule minus_one_helper5[rotated])
  apply (simp add: pd_bits_def pageBits_def)
  done

lemma copy_global_mappings_valid_ioc[wp]:
 "\<lbrace>valid_ioc\<rbrace> copy_global_mappings pd \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (simp add: copy_global_mappings_def, wp mapM_x_wp[of UNIV]) simp+

lemma copy_global_mappings_vms[wp]:
 "\<lbrace>valid_machine_state\<rbrace> copy_global_mappings pd \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (simp add: copy_global_mappings_def, wp mapM_x_wp[of UNIV]) simp+

lemma copy_global_mappings_invs:
  "\<lbrace>invs and (\<lambda>s. pd \<notin> global_refs s)
         and K (is_aligned pd pd_bits)\<rbrace>
     copy_global_mappings pd \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (fold all_invs_but_equal_kernel_mappings_restricted_eq)
  apply (rule hoare_pre, rule copy_global_invs_mappings_restricted)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def
                        restrict_map_def)
  done

crunch global_refs_inv[wp]: copy_global_mappings "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)

lemma mapM_copy_global_invs_mappings_restricted:
  "\<lbrace>\<lambda>s. all_invs_but_equal_kernel_mappings_restricted (set pds) s
            \<and> (set pds \<inter> global_refs s = {})
            \<and> (\<forall>pd \<in> set pds. is_aligned pd pd_bits)\<rbrace>
     mapM_x copy_global_mappings pds
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (fold all_invs_but_equal_kernel_mappings_restricted_eq)
  apply (induct pds, simp_all only: mapM_x_Nil mapM_x_Cons K_bind_def)
   apply (wp, simp)
  apply (rule hoare_seq_ext, assumption, thin_tac "P" for P)
  apply (rule hoare_conjI)
   apply (rule hoare_pre, rule copy_global_invs_mappings_restricted)
   apply clarsimp
  apply (rule hoare_pre, wp)
  apply clarsimp
  done


lemma dmo_eq_kernel_restricted [wp, Retype_AI_assms]:
  "\<lbrace>\<lambda>s. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>
       do_machine_op m
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (simp add: equal_kernel_mappings_def obj_at_def)
  done


definition
  "post_retype_invs_check tp \<equiv> tp = ArchObject PageDirectoryObj"

declare post_retype_invs_check_def[simp]

end


context begin interpretation Arch .
requalify_consts post_retype_invs_check
end

definition
  post_retype_invs :: "apiobject_type \<Rightarrow> word32 list \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "post_retype_invs tp refs \<equiv>
      if post_retype_invs_check tp
        then all_invs_but_equal_kernel_mappings_restricted (set refs)
        else invs"

global_interpretation Retype_AI_post_retype_invs?: Retype_AI_post_retype_invs
  where post_retype_invs_check = post_retype_invs_check
    and post_retype_invs = post_retype_invs
  by (unfold_locales; fact post_retype_invs_def)


context Arch begin global_naming ARM

lemma dmo_mapM_x_ccr_invs[wp]:
  "\<lbrace>invs\<rbrace>
   do_machine_op (mapM_x (\<lambda>ptr. cleanCacheRange_PoU ptr (w ptr) (addrFromPPtr ptr)) xs)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: mapM_x_mapM do_machine_op_return_foo)
  apply (rule hoare_pre)
  apply (subst dom_mapM)
    apply ((simp add:clearMemory_def
      | wp empty_fail_cleanCacheRange_PoU ef_storeWord
      empty_fail_mapM_x empty_fail_bind)+)[1]
   apply (wp mapM_wp' | clarsimp)+
  done


lemma init_arch_objects_invs_from_restricted:
  "\<lbrace>post_retype_invs new_type refs
         and (\<lambda>s. global_refs s \<inter> set refs = {})
         and K (\<forall>ref \<in> set refs. is_aligned ref (obj_bits_api new_type obj_sz))\<rbrace>
     init_arch_objects new_type ptr bits obj_sz refs
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: init_arch_objects_def)
  apply (rule hoare_pre)
   apply (wp mapM_copy_global_invs_mappings_restricted
             hoare_vcg_const_Ball_lift
             valid_irq_node_typ
                  | wpc)+
  apply (auto simp: post_retype_invs_def default_arch_object_def
                    pd_bits_def pageBits_def obj_bits_api_def
                    global_refs_def)
  done


lemma obj_bits_api_neq_0 [Retype_AI_assms]:
  "ty \<noteq> Untyped \<Longrightarrow> 0 < obj_bits_api ty us"
  unfolding obj_bits_api_def
  by (clarsimp simp: slot_bits_def default_arch_object_def pageBits_def 
               split: Structures_A.apiobject_type.splits aobject_type.splits)


lemma vs_lookup_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup s \<subseteq> vs_lookup s'"
  unfolding vs_lookup_def
  apply (rule Image_mono)
   apply (rule vs_lookup_trans_sub2)
   apply (erule (1) ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
  done


lemma vs_lookup_pages_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs_pages ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup_pages s \<subseteq> vs_lookup_pages s'"
  unfolding vs_lookup_pages_def
  apply (rule Image_mono)
   apply (rule vs_lookup_pages_trans_sub2)
   apply (erule (1) ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
  done

end


global_interpretation Retype_AI_slot_bits?: Retype_AI_slot_bits
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; fact Retype_AI_assms)
  qed


context Arch begin global_naming ARM

lemma valid_untyped_helper [Retype_AI_assms]:
  assumes valid_c : "s  \<turnstile> c" 
  and   cte_at  : "cte_wp_at (op = c) q s"
  and     tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  and   cover  : "range_cover ptr sz (obj_bits_api ty us) n"
  and   range  : "is_untyped_cap c \<Longrightarrow> usable_untyped_range c \<inter> {ptr..ptr + of_nat (n * 2 ^ (obj_bits_api ty us)) - 1} = {}"
  and     pn   : "pspace_no_overlap ptr sz s"
  and     cn   : "caps_no_overlap ptr sz s"
  and     vp   : "valid_pspace s"
  shows "valid_cap c
           (s\<lparr>kheap := \<lambda>x. if x \<in> set (retype_addrs ptr ty n us) then Some (default_object ty us) else kheap s x\<rparr>)"
  (is "valid_cap c ?ns")
  proof -
  have obj_at_pres: "\<And>P x. obj_at P x s \<Longrightarrow> obj_at P x ?ns"
  by (clarsimp simp: obj_at_def dest: domI)
   (erule pspace_no_overlapC [OF pn _ _ cover vp])
  note blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff
  have cover':"range_cover ptr sz (obj_bits (default_object ty us)) n"
    using cover tyunt
    by (clarsimp simp:obj_bits_api_def3)

  show ?thesis
  using cover valid_c range usable_range_emptyD[where cap = c] cte_at
  apply (clarsimp simp: valid_cap_def elim!: obj_at_pres
                 split: cap.splits option.splits arch_cap.splits)
      defer
     apply (fastforce elim!: obj_at_pres)
    apply (fastforce elim!: obj_at_pres)
   apply (fastforce elim!: obj_at_pres)
  apply (rename_tac word nat1 nat2)
  apply (clarsimp simp:valid_untyped_def is_cap_simps obj_at_def split:split_if_asm)
    apply (thin_tac "\<forall>x. Q x" for Q)
     apply (frule retype_addrs_obj_range_subset_strong[OF _ cover' tyunt])
     apply (frule usable_range_subseteq)
       apply (simp add:is_cap_simps)
     apply (clarsimp simp:cap_aligned_def split:split_if_asm)
      apply (frule aligned_ranges_subset_or_disjoint)
      apply (erule retype_addrs_aligned[where sz = sz])
         apply (simp add:range_cover_def)
        apply (simp add:range_cover_def word_bits_def)
       apply (simp add:range_cover_def)
      apply (clarsimp simp:obj_range_def[symmetric] obj_bits_api_def3 Int_ac tyunt
        split:split_if_asm)
     apply (elim disjE)
      apply (drule(2) subset_trans[THEN disjoint_subset2])
      apply (drule Int_absorb2)+
       apply (simp add:is_cap_simps free_index_of_def)
    apply simp
    apply (drule(1) disjoint_subset2[rotated])
    apply (simp add:Int_ac)
   apply (thin_tac "\<forall>x. Q x" for Q)
   apply (frule retype_addrs_obj_range_subset[OF _ cover' tyunt])
   apply (clarsimp simp:cap_aligned_def)
    apply (frule aligned_ranges_subset_or_disjoint)
     apply (erule retype_addrs_aligned[where sz = sz])
         apply (simp add:range_cover_def)
        apply (simp add:range_cover_def word_bits_def)
       apply (simp add:range_cover_def)
      apply (clarsimp simp:obj_range_def[symmetric] obj_bits_api_def3 Int_ac tyunt
        split:split_if_asm)
   apply (case_tac "{word..word + 2 ^ nat1 - 1} = obj_range p (default_object ty us)")
     apply simp
   apply (erule disjE)
     apply (simp add:subset_iff_psubset_eq)
     apply (simp add:subset_iff_psubset_eq[symmetric])
     apply (drule(1) psubset_subset_trans)
    apply (simp add:cte_wp_at_caps_of_state)
    apply (drule cn[unfolded caps_no_overlap_def,THEN bspec,OF ranI])
    apply simp
  apply blast+
  done
  qed

end


global_interpretation Retype_AI_valid_untyped_helper?: Retype_AI_valid_untyped_helper
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; fact Retype_AI_assms)
  qed


locale retype_region_proofs_arch
  = retype_region_proofs s ty us ptr sz n ps s'
  + Arch
  for s :: "'state_ext :: state_ext state"
  and ty us ptr sz n ps s'


context retype_region_proofs begin

interpretation Arch .

lemma valid_cap:
  assumes cap:
    "(s::'state_ext state) \<turnstile> cap \<and> untyped_range cap \<inter> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} = {}"
  shows "s' \<turnstile> cap"
  proof - 
  note blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff
  have cover':"range_cover ptr sz (obj_bits (default_object ty us)) n"
    using cover tyunt
    by (clarsimp simp:obj_bits_api_def3)
  show ?thesis
  using cap
  apply (case_tac cap)
    unfolding valid_cap_def
    apply (simp_all add: valid_cap_def obj_at_pres cte_at_pres
                              split: option.split_asm arch_cap.split_asm
                                     option.splits)
     apply (clarsimp simp add: valid_untyped_def ps_def s'_def)
     apply (intro conjI)
       apply clarsimp
       apply (drule disjoint_subset [OF retype_addrs_obj_range_subset [OF _ cover' tyunt]])
        apply (simp add:Int_ac)
       apply simp
      apply clarsimp
     apply (drule disjoint_subset [OF retype_addrs_obj_range_subset [OF _ cover' tyunt]])
      apply (simp add:Int_ac)
     apply simp
     using cover tyunt
     apply (simp add: obj_bits_api_def2 split:Structures_A.apiobject_type.splits)
     apply clarsimp+
    apply (fastforce elim!: obj_at_pres)+
  done
  qed

lemma valid_global_refs:
  "valid_global_refs s \<Longrightarrow> valid_global_refs s'"
  apply (simp add: valid_global_refs_def valid_refs_def global_refs_def idle_s')
  apply (simp add: cte_retype cap_range_def)
  done

lemma valid_arch_state:
  "valid_arch_state s \<Longrightarrow> valid_arch_state s'"
  by (clarsimp simp: valid_arch_state_def obj_at_pres 
                     valid_asid_table_def valid_global_pts_def)

lemma vs_refs_default [simp]:
  "vs_refs (default_object ty us) = {}"
  by (simp add: default_object_def default_arch_object_def tyunt vs_refs_def 
                o_def pde_ref_def graph_of_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)

lemma vs_refs_pages_default [simp]:
  "vs_refs_pages (default_object ty us) = {}"
  by (simp add: default_object_def default_arch_object_def tyunt vs_refs_pages_def 
                o_def pde_ref_pages_def pte_ref_pages_def graph_of_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)

lemma vs_lookup':
  "vs_lookup s' = vs_lookup s"
  apply (rule order_antisym)
   apply (rule vs_lookup_sub2)
    apply (clarsimp simp: obj_at_def s'_def ps_def split: split_if_asm)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: obj_at_def s'_def ps_def split: split_if_asm dest!: orthr)
  apply simp
  done

lemma vs_lookup_pages': 
  "vs_lookup_pages s' = vs_lookup_pages s"
  apply (rule order_antisym)
   apply (rule vs_lookup_pages_sub2)
    apply (clarsimp simp: obj_at_def s'_def ps_def split: split_if_asm)
   apply simp
  apply (rule vs_lookup_pages_sub)
   apply (clarsimp simp: obj_at_def s'_def ps_def split: split_if_asm dest!: orthr)
  apply simp
  done

end


context retype_region_proofs_arch begin

lemma obj_at_valid_pte:
  "\<lbrakk>valid_pte pte s; \<And>P p. obj_at P p s \<Longrightarrow> obj_at P p s'\<rbrakk> 
   \<Longrightarrow> valid_pte pte s'"
  by (cases pte, auto simp: obj_at_def)

lemma obj_at_valid_pde:
  "\<lbrakk>valid_pde pde s; \<And>P p. obj_at P p s \<Longrightarrow> obj_at P p s'\<rbrakk> 
   \<Longrightarrow> valid_pde pde s'"
  by (cases pde, auto simp: obj_at_def)

end


context retype_region_proofs begin

interpretation retype_region_proofs_arch ..

lemma valid_arch_objs':
  assumes va: "valid_arch_objs s" 
  shows "valid_arch_objs s'"
proof
  fix p ao
  assume p: "(\<exists>\<rhd> p) s'"
  assume "ko_at (ArchObj ao) p s'"
  hence "ko_at (ArchObj ao) p s \<or> ArchObj ao = default_object ty us"
    by (simp add: ps_def obj_at_def s'_def split: split_if_asm)
  moreover
  { assume "ArchObj ao = default_object ty us" with tyunt
    have "valid_arch_obj ao s'" by (rule valid_arch_obj_default)
  }
  moreover
  { assume "ko_at (ArchObj ao) p s"
    with va p
    have "valid_arch_obj ao s"
      by (auto simp: vs_lookup' elim: valid_arch_objsD)
    hence "valid_arch_obj ao s'"
      apply (cases ao, simp_all add: obj_at_pres)
       apply (erule allEI)
       apply (erule (1) obj_at_valid_pte[OF _ obj_at_pres])
      apply (erule ballEI)
      apply (erule (1) obj_at_valid_pde[OF _ obj_at_pres])
      done
  }
  ultimately
  show "valid_arch_obj ao s'" by blast
qed

(* ML \<open>val pre_ctxt_0 = @{context}\<close> *)
sublocale retype_region_proofs_gen?: retype_region_proofs_gen ..
(* local_setup \<open>note_new_facts pre_ctxt_0\<close> *)

end


context Arch begin global_naming ARM (*FIXME: arch_split*)

definition
  valid_vs_lookup2 :: "(vs_ref list \<times> word32) set \<Rightarrow> word32 set \<Rightarrow> (cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
 "valid_vs_lookup2 lookup S caps \<equiv>
    \<forall>p ref. (ref, p) \<in> lookup \<longrightarrow>
          ref \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None] \<and>
         (\<exists>p' cap. caps p' = Some cap \<and> p \<in> obj_refs cap \<and> vs_cap_ref cap = Some ref)"


lemma valid_vs_lookup_def2:
  "valid_vs_lookup s = valid_vs_lookup2
         (vs_lookup_pages s) (set (arm_global_pts (arch_state s)))
         (null_filter (caps_of_state s))"
  apply (simp add: valid_vs_lookup_def valid_vs_lookup2_def)
  apply (intro iff_allI imp_cong[OF refl] disj_cong[OF refl]
               iff_exI conj_cong[OF refl])
  apply (auto simp: null_filter_def)
  done


lemma unique_table_caps_null:
  "unique_table_caps (null_filter s)
       = unique_table_caps s"
  apply (simp add: unique_table_caps_def)
  apply (intro iff_allI)
  apply (clarsimp simp: null_filter_def)
  done


lemma unique_table_refs_null:
  "unique_table_refs (null_filter s)
       = unique_table_refs s"
  apply (simp only: unique_table_refs_def)
  apply (intro iff_allI)
  apply (clarsimp simp: null_filter_def)
  apply (auto dest!: obj_ref_none_no_asid[rule_format]
               simp: table_cap_ref_def)
  done


definition
  region_in_kernel_window :: "word32 set \<Rightarrow> 'z state \<Rightarrow> bool"
where 
 "region_in_kernel_window S \<equiv>
     \<lambda>s. \<forall>x \<in> S. arm_kernel_vspace (arch_state s) x = ArmVSpaceKernelWindow"

end


context begin interpretation Arch .
requalify_consts region_in_kernel_window
end


context retype_region_proofs_arch begin

lemmas unique_table_caps_eq
    = arg_cong[where f=unique_table_caps, OF null_filter,
               simplified unique_table_caps_null]

lemmas unique_table_refs_eq
    = arg_cong[where f=unique_table_refs, OF null_filter,
               simplified unique_table_refs_null]

lemma valid_table_caps:
  "valid_table_caps s \<Longrightarrow> valid_table_caps s'"
  apply (simp add: valid_table_caps_def
              del: imp_disjL)
  apply (elim allEI, intro impI, simp)
  apply (frule caps_retype[rotated])
   apply clarsimp
  apply (rule obj_at_pres)
  apply simp
  done

lemma valid_arch_caps:
  "valid_arch_caps s \<Longrightarrow> valid_arch_caps s'"
  by (clarsimp simp add: valid_arch_caps_def null_filter
                         valid_vs_lookup_def2 vs_lookup_pages'
                         unique_table_caps_eq
                         unique_table_refs_eq
                         valid_table_caps)

lemma valid_arch_obj_pres:
  "valid_arch_obj ao s \<Longrightarrow> valid_arch_obj ao s'"
  apply (cases ao, simp_all)
    apply (simp add: obj_at_pres)
   apply (erule allEI)
   apply (erule (1) obj_at_valid_pte[OF _ obj_at_pres])
  apply (erule ballEI)
  apply (erule (1) obj_at_valid_pde[OF _ obj_at_pres])
  done

lemma valid_global_objs:
  "valid_global_objs s \<Longrightarrow> valid_global_objs s'"
  apply (simp add: valid_global_objs_def valid_ao_at_def)
  apply (elim conjE, intro conjI ballI)
    apply (erule exEI)
    apply (simp add: obj_at_pres valid_arch_obj_pres)
   apply (simp add: obj_at_pres)
  apply (rule exEI, erule(1) bspec)
  apply (simp add: obj_at_pres valid_arch_obj_pres)
  done

lemma valid_kernel_mappings:
  "valid_kernel_mappings s \<Longrightarrow> valid_kernel_mappings s'"
  apply (simp add: valid_kernel_mappings_def s'_def
                   ball_ran_eq ps_def)
  apply (simp add: default_object_def valid_kernel_mappings_if_pd_def
                   tyunt default_arch_object_def pde_ref_def
            split: Structures_A.apiobject_type.split
                   aobject_type.split)
  done

lemma valid_asid_map:
  "valid_asid_map s \<Longrightarrow> valid_asid_map s'"
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: pd_at_asid_def)
  apply (drule vs_lookup_2ConsD)
  apply clarsimp
  apply (erule vs_lookup_atE)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (drule obj_at_pres)
  apply (fastforce simp: vs_asid_refs_def graph_of_def 
                  intro: vs_lookupI vs_lookup1I)
  done

lemma equal_kernel_mappings:
  "equal_kernel_mappings s \<Longrightarrow>
      if ty = ArchObject PageDirectoryObj
      then equal_kernel_mappings
           (s'\<lparr>kheap := kheap s' |` (- set (retype_addrs ptr ty n us))\<rparr>)
      else equal_kernel_mappings s'"
  apply (simp add: equal_kernel_mappings_def)
  apply (intro conjI impI)
   apply (elim allEI)
   apply (simp add: obj_at_def restrict_map_def)
   apply (simp add: s'_def ps_def)
  apply (elim allEI)
  apply (simp add: obj_at_def restrict_map_def)
  apply (simp add: s'_def ps_def)
  apply (simp add: default_object_def default_arch_object_def tyunt
            split: Structures_A.apiobject_type.split
                   aobject_type.split)
  done

lemma valid_global_pd_mappings:
  "valid_global_pd_mappings s
         \<Longrightarrow> valid_global_pd_mappings s'"
  apply (erule valid_global_pd_mappings_pres)
     apply (simp | erule obj_at_pres)+
  done

lemma pspace_in_kernel_window:
  "\<lbrakk> pspace_in_kernel_window (s :: 'state_ext state);
     region_in_kernel_window {ptr .. (ptr &&~~ mask sz) + 2 ^ sz - 1} s \<rbrakk>
          \<Longrightarrow> pspace_in_kernel_window s'"
  apply (simp add: pspace_in_kernel_window_def s'_def ps_def)
  apply (clarsimp simp: region_in_kernel_window_def
                   del: ballI)
  apply (drule retype_addrs_mem_subset_ptr_bits[OF cover tyunt])
  apply (fastforce simp: field_simps obj_bits_api_default_object[OF tyunt])
  done

lemma vms:
  "valid_machine_state s \<Longrightarrow> valid_machine_state s'"
  apply (simp add: s'_def ps_def valid_machine_state_def in_user_frame_def)
  apply (rule allI, erule_tac x=p in allE, clarsimp)
  apply (rule_tac x=sz in exI, clarsimp simp: obj_at_def orthr)
  done

end


context retype_region_proofs begin

interpretation retype_region_proofs_arch ..

lemma post_retype_invs:
  "\<lbrakk> invs s; region_in_kernel_window {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} s \<rbrakk>
        \<Longrightarrow> post_retype_invs ty (retype_addrs ptr ty n us) s'"
  using equal_kernel_mappings
  by (clarsimp simp: invs_def post_retype_invs_def valid_state_def
                     unsafe_rep2 null_filter valid_idle
                     valid_reply_caps valid_reply_masters
                     valid_global_refs valid_arch_state
                     valid_irq_node_def obj_at_pres
                     valid_arch_caps valid_global_objs
                     valid_arch_objs' valid_irq_handlers
                     valid_mdb_rep2 mdb_and_revokable
                     valid_pspace cur_tcb only_idle
                     valid_kernel_mappings valid_asid_map
                     valid_global_pd_mappings valid_ioc vms
                     pspace_in_kernel_window
                     cap_refs_in_kernel_window valid_irq_states)

(* ML \<open>val pre_ctxt_1 = @{context}\<close> *)

sublocale retype_region_proofs_invs?: retype_region_proofs_invs
  where region_in_kernel_window = region_in_kernel_window
    and post_retype_invs_check = post_retype_invs_check
    and post_retype_invs = post_retype_invs
  using post_retype_invs valid_cap valid_global_refs valid_arch_state valid_arch_objs'
  by unfold_locales (auto simp: s'_def ps_def)

(* local_setup \<open>note_new_facts pre_ctxt_1\<close> *)

lemmas post_retype_invs_axioms = retype_region_proofs_invs_axioms

end


context Arch begin global_naming ARM

named_theorems Retype_AI_assms'

lemma invs_post_retype_invs [Retype_AI_assms']:
  "invs s \<Longrightarrow> post_retype_invs ty refs s"
  apply (clarsimp simp: post_retype_invs_def invs_def valid_state_def)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def
                        restrict_map_def)
  done

lemmas equal_kernel_mappings_trans_state
  = more_update.equal_kernel_mappings_update

lemmas retype_region_proofs_assms [Retype_AI_assms']
  = retype_region_proofs.post_retype_invs_axioms

end


global_interpretation Retype_AI?: Retype_AI
  where no_gs_types = ARM.no_gs_types
    and post_retype_invs_check = post_retype_invs_check
    and post_retype_invs = post_retype_invs
    and region_in_kernel_window = region_in_kernel_window
  proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact Retype_AI_assms)?)
     (simp add: Retype_AI_axioms_def Retype_AI_assms')
  qed


context Arch begin global_naming ARM

lemma retype_region_plain_invs:
  "\<lbrace>invs and caps_no_overlap ptr sz and pspace_no_overlap ptr sz 
      and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
      and region_in_kernel_window {ptr .. (ptr &&~~ mask sz) + 2 ^ sz - 1}
      and K (ty = Structures_A.CapTableObject \<longrightarrow> 0 < us)
      and K (range_cover ptr sz (obj_bits_api ty us) n)
      and K (ty \<noteq> ArchObject PageDirectoryObj)\<rbrace>
      retype_region ptr n us ty \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post[OF retype_region_post_retype_invs])
  apply (simp add: post_retype_invs_def)
  done


lemma storeWord_um_eq_0:
  "\<lbrace>\<lambda>m. underlying_memory m p = 0\<rbrace>
    storeWord x 0
   \<lbrace>\<lambda>_ m. underlying_memory m p = 0\<rbrace>"
  by (simp add: storeWord_def word_rsplit_0 | wp)+


lemma clearMemory_um_eq_0:
  "\<lbrace>\<lambda>m. underlying_memory m p = 0\<rbrace>
    clearMemory ptr bits
   \<lbrace>\<lambda>_ m. underlying_memory m p = 0\<rbrace>"
  apply (clarsimp simp: clearMemory_def)
  apply (wp mapM_x_wp_inv | simp)+
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps storeWord_um_eq_0)
  apply (fastforce simp: ignore_failure_def split: split_if_asm)
  done


lemma cleanCacheRange_PoU_um_inv[wp]:
  "\<lbrace>\<lambda>m. P (underlying_memory m)\<rbrace>
    cleanCacheRange_PoU ptr w p
   \<lbrace>\<lambda>_ m. P (underlying_memory m)\<rbrace>"
  by (simp add: cleanCacheRange_PoU_def cleanByVA_PoU_def machine_op_lift_def machine_rest_lift_def
                split_def | wp)+

end

end
