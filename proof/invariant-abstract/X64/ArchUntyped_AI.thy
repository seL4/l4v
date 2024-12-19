(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchUntyped_AI
imports Untyped_AI
begin

context Arch begin arch_global_naming

named_theorems Untyped_AI_assms

lemma of_bl_nat_to_cref[Untyped_AI_assms]:
    "\<lbrakk> x < 2 ^ bits; bits < word_bits \<rbrakk>
      \<Longrightarrow> (of_bl (nat_to_cref bits x) :: word64) = of_nat x"
  apply (clarsimp intro!: less_mask_eq
                  simp: nat_to_cref_def of_drop_to_bl
                        word_size word_less_nat_alt word_bits_def)
  by (metis add_lessD1 le_unat_uoi nat_le_iff_add nat_le_linear)


lemma cnode_cap_ex_cte[Untyped_AI_assms]:
  "\<lbrakk> is_cnode_cap cap; cte_wp_at (\<lambda>c. \<exists>m. cap = mask_cap m c) p s;
     (s::'state_ext::state_ext state) \<turnstile> cap; valid_objs s; pspace_aligned s \<rbrakk> \<Longrightarrow>
    ex_cte_cap_wp_to is_cnode_cap (obj_ref_of cap, nat_to_cref (bits_of cap) x) s"
  apply (simp only: ex_cte_cap_wp_to_def)
  apply (rule exI, erule cte_wp_at_weakenE)
  apply (clarsimp simp: is_cap_simps bits_of_def)
  apply (case_tac c, simp_all add: mask_cap_def cap_rights_update_def split:bool.splits)
  apply (clarsimp simp: nat_to_cref_def word_bits_def)
  apply (erule(2) valid_CNodeCapE)
  apply (simp add: word_bits_def cte_level_bits_def)
  done



lemma inj_on_nat_to_cref[Untyped_AI_assms]:
  "bits < word_bits \<Longrightarrow> inj_on (nat_to_cref bits) {..< 2 ^ bits}"
  apply (rule inj_onI)
  apply (drule arg_cong[where f="\<lambda>x. replicate (64 - bits) False @ x"])
  apply (subst(asm) word_bl.Abs_inject[where 'a=64, symmetric])
    apply (simp add: nat_to_cref_def word_bits_def)
   apply (simp add: nat_to_cref_def word_bits_def)
  apply (simp add: of_bl_rep_False of_bl_nat_to_cref)
  apply (erule word_unat.Abs_eqD)
   apply (simp only: unats_def mem_simps)
   apply (erule order_less_le_trans)
   apply (rule power_increasing, (simp add: word_bits_def) +)
  apply (simp only: unats_def mem_simps)
  apply (erule order_less_le_trans)
  apply (rule power_increasing, simp+)
  done


lemma data_to_obj_type_sp[Untyped_AI_assms]:
  "\<lbrace>P\<rbrace> data_to_obj_type x \<lbrace>\<lambda>ts (s::'state_ext::state_ext state). ts \<noteq> ArchObject ASIDPoolObj \<and> P s\<rbrace>, -"
  unfolding data_to_obj_type_def
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply clarsimp
  apply (simp add: arch_data_to_obj_type_def split: if_split_asm)
  done

lemma dui_inv_wf[wp, Untyped_AI_assms]:
  "\<lbrace>invs and cte_wp_at ((=) (cap.UntypedCap dev w sz idx)) slot
     and (\<lambda>s. \<forall>cap \<in> set cs. is_cnode_cap cap
                      \<longrightarrow> (\<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s))
    and (\<lambda>s. \<forall>x \<in> set cs. s \<turnstile> x)\<rbrace>
     decode_untyped_invocation label args slot (cap.UntypedCap dev w sz idx) cs
   \<lbrace>valid_untyped_inv\<rbrace>,-"
proof -
  have inj: "\<And>node_cap s. \<lbrakk>is_cnode_cap node_cap;
    unat (args ! 5) \<le> 2 ^ bits_of node_cap - unat (args ! 4);valid_cap node_cap s\<rbrakk> \<Longrightarrow>
    inj_on (Pair (obj_ref_of node_cap) \<circ> nat_to_cref (bits_of node_cap))
                      {unat (args ! 4)..<unat (args ! 4) + unat (args ! 5)}"
    apply (simp add: comp_def)
    apply (rule inj_on_split)
    apply (rule subset_inj_on [OF inj_on_nat_to_cref])
     apply (clarsimp simp: is_cap_simps bits_of_def valid_cap_def word_bits_def cap_aligned_def)
    apply clarsimp
    apply (rule less_le_trans)
     apply assumption
    apply (simp add: le_diff_conv2)
    done
  have nasty_strengthen:
    "\<And>S a f s. (\<forall>x\<in>S. cte_wp_at ((=) cap.NullCap) (a, f x) s)
    \<Longrightarrow> cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) slot s
    \<longrightarrow> slot \<notin> (Pair a \<circ> f) ` S"
    by (auto simp:cte_wp_at_caps_of_state)
  show ?thesis
    apply (simp add: decode_untyped_invocation_def unlessE_def[symmetric] unlessE_whenE
          split del: if_split)
    apply (rule validE_R_sp[OF whenE_throwError_sp]
                validE_R_sp[OF data_to_obj_type_sp]
                validE_R_sp[OF dui_sp_helper] validE_R_sp[OF map_ensure_empty])+
     apply clarsimp
    apply (rule hoare_pre)
     apply (wp whenE_throwError_wp[THEN validE_validE_R] check_children_wp
               map_ensure_empty_wp)
    apply (clarsimp simp: distinct_map cases_imp_eq)
    apply (subgoal_tac "s \<turnstile> node_cap")
     prefer 2
     apply (erule disjE)
      apply (drule bspec [where x = "cs ! 0"],clarsimp)+
      apply fastforce
     apply clarsimp
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (drule(1) caps_of_state_valid[rotated])+
     apply assumption
    apply (subgoal_tac "\<forall>r\<in>cte_refs node_cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s")
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (frule(1) caps_of_state_valid[rotated])
     apply (clarsimp simp: not_less)
     apply (frule(2) inj)
     apply (clarsimp simp: comp_def)
     apply (frule(1) caps_of_state_valid)
     apply (simp add: nasty_strengthen[unfolded o_def] cte_wp_at_caps_of_state)
     apply (intro conjI)
      apply (intro impI)
      apply (frule range_cover_stuff[where w=w and rv = 0 and sz = sz], simp_all)[1]
        apply (clarsimp simp: valid_cap_simps cap_aligned_def)+
      apply (frule alignUp_idem[OF is_aligned_weaken,where a = w])
        apply (erule range_cover.sz)
       apply (simp add: range_cover_def)
      apply (clarsimp simp: get_free_ref_def empty_descendants_range_in)
      apply (rule conjI[rotated], blast, clarsimp)
      apply (drule_tac x = "(obj_ref_of node_cap, nat_to_cref (bits_of node_cap) slota)" in bspec)
       apply (clarsimp simp: is_cap_simps nat_to_cref_def word_bits_def
                             bits_of_def valid_cap_simps cap_aligned_def)+
     apply (simp add: free_index_of_def)
     apply (frule(1) range_cover_stuff[where sz = sz])
        apply (clarsimp dest!: valid_cap_aligned simp:cap_aligned_def word_bits_def)+
      apply simp+
     apply (clarsimp simp: get_free_ref_def)
    apply (erule disjE)
     apply (drule_tac x= "cs!0" in bspec, clarsimp)
     apply simp
    apply (clarsimp simp: cte_wp_at_caps_of_state ex_cte_cap_wp_to_def)
    apply (rule_tac x=aa in exI, rule exI, rule exI)
    apply (rule conjI, assumption)
    apply (rule conjI, assumption)
    apply (clarsimp simp: is_cap_simps mask_cap_def cap_rights_update_def)
    done
qed

lemma asid_bits_ge_0:
  "(0::word32) < 2 ^ asid_bits" by (simp add: asid_bits_def)

lemma retype_ret_valid_caps_captable[Untyped_AI_assms]:
  "\<lbrakk>pspace_no_overlap_range_cover ptr sz (s::'state_ext::state_ext state) \<and> 0 < us
      \<and> range_cover ptr sz (obj_bits_api CapTableObject us) n \<and> ptr \<noteq> 0
       \<rbrakk>
         \<Longrightarrow> \<forall>y\<in>{0..<n}. s
                \<lparr>kheap := foldr (\<lambda>p kh. kh(p \<mapsto> default_object CapTableObject dev us)) (map (\<lambda>p. ptr_add ptr (p * 2 ^ obj_bits_api CapTableObject us)) [0..<n])
                           (kheap s)\<rparr> \<turnstile> CNodeCap (ptr_add ptr (y * 2 ^ obj_bits_api CapTableObject us)) us []"
by ((clarsimp simp:valid_cap_def default_object_def cap_aligned_def
        cte_level_bits_def is_obj_defs well_formed_cnode_n_def empty_cnode_def
        dom_def arch_default_cap_def ptr_add_def | rule conjI | intro conjI obj_at_foldr_intro imageI
      | rule is_aligned_add_multI[OF _ le_refl],
        (simp add:range_cover_def word_bits_def obj_bits_api_def slot_bits_def)+)+)[1]

lemma retype_ret_valid_caps_aobj[Untyped_AI_assms]:
  "\<And>ptr sz (s::'state_ext::state_ext state) x6 us n.
  \<lbrakk>pspace_no_overlap_range_cover ptr sz s \<and> x6 \<noteq> ASIDPoolObj \<and>
  range_cover ptr sz (obj_bits_api (ArchObject x6) us) n \<and> ptr \<noteq> 0\<rbrakk>
            \<Longrightarrow> \<forall>y\<in>{0..<n}. s
                   \<lparr>kheap := foldr (\<lambda>p kh. kh(p \<mapsto> default_object (ArchObject x6) dev us)) (map (\<lambda>p. ptr_add ptr (p * 2 ^ obj_bits_api (ArchObject x6) us)) [0..<n])
                              (kheap s)\<rparr> \<turnstile> ArchObjectCap (arch_default_cap x6 (ptr_add ptr (y * 2 ^ obj_bits_api (ArchObject x6) us)) us dev)"
  apply (rename_tac aobject_type us n)
  apply (case_tac aobject_type)
  by (clarsimp simp: valid_cap_def default_object_def cap_aligned_def
                     cte_level_bits_def is_obj_defs well_formed_cnode_n_def empty_cnode_def
                     dom_def arch_default_cap_def ptr_add_def
      | intro conjI obj_at_foldr_intro
        imageI valid_vm_rights_def
      | rule is_aligned_add_multI[OF _ le_refl]
      | fastforce simp:range_cover_def obj_bits_api_def
        default_arch_object_def valid_vm_rights_def  word_bits_def a_type_def)+



lemma copy_global_mappings_hoare_lift:(*FIXME: arch-split  \<rightarrow> these do not seem to be used globally *)
  assumes wp: "\<And>ptr val. \<lbrace>Q\<rbrace> store_pml4e ptr val \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows       "\<lbrace>Q\<rbrace> copy_global_mappings pd \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply (wp mapM_x_wp' wp)
  done

lemma init_arch_objects_hoare_lift:
  assumes wp:  "\<And>ptr val. \<lbrace>P\<rbrace> store_pml4e ptr val \<lbrace>\<lambda>rv. P\<rbrace>"
  shows       "\<lbrace>P\<rbrace> init_arch_objects tp dev ptr sz us adds \<lbrace>\<lambda>rv. P\<rbrace>"
proof -
  have pres: "\<lbrace>P\<rbrace> return () \<lbrace>\<lambda>rv. P\<rbrace>"
    by (wp wp | simp)+
  show ?thesis
    apply (simp add: init_arch_objects_def
                  pres reserve_region_def unless_def when_def
           split: Structures_A.apiobject_type.split
                  aobject_type.split)
    apply clarsimp
    apply (rule hoare_pre)
     apply (wp mapM_x_wp' copy_global_mappings_hoare_lift wp)
    apply simp
    done
qed

lemma cap_refs_in_kernel_windowD2:
  "\<lbrakk> cte_wp_at P p (s::'state_ext::state_ext state); cap_refs_in_kernel_window s \<rbrakk>
       \<Longrightarrow> \<exists>cap. P cap \<and> region_in_kernel_window (cap_range cap) s"
  apply (clarsimp simp: cte_wp_at_caps_of_state region_in_kernel_window_def)
  apply (drule(1) cap_refs_in_kernel_windowD)
  apply fastforce
  done

lemma init_arch_objects_descendants_range[wp,Untyped_AI_assms]:
  "\<lbrace>\<lambda>(s::'state_ext::state_ext state). descendants_range x cref s \<rbrace> init_arch_objects ty dev ptr n us y
          \<lbrace>\<lambda>rv s. descendants_range x cref s\<rbrace>"
  apply (simp add:descendants_range_def)
  apply (rule hoare_pre)
   apply (wp retype_region_mdb init_arch_objects_hoare_lift)
    apply (simp add: store_pml4e_def set_arch_obj_simps)
    apply (wp hoare_vcg_ball_lift | wps)+
   apply simp
  apply fastforce
  done



lemma init_arch_objects_caps_overlap_reserved[wp,Untyped_AI_assms]:
  "\<lbrace>\<lambda>(s::'state_ext::state_ext state). caps_overlap_reserved S s\<rbrace>
   init_arch_objects ty dev ptr n us y
   \<lbrace>\<lambda>rv s. caps_overlap_reserved S s\<rbrace>"
  apply (simp add:caps_overlap_reserved_def)
  apply (rule hoare_pre)
   apply (wp retype_region_mdb init_arch_objects_hoare_lift)
  apply fastforce
  done

(* FIXME ioportcontrol: move *)
lemma cap_ioports_not_ioport_cap[simp]:
  "\<not>is_ioport_cap cap \<Longrightarrow> cap_ioports cap = {}"
  by (clarsimp simp: is_cap_simps cap_ioports_def split: arch_cap.splits cap.splits)

lemma default_cap_not_ioport:
  "\<not> is_ioport_cap (default_cap tp oref sz dev)"
  apply (case_tac tp; clarsimp simp: is_cap_simps)
  by (case_tac x6; clarsimp simp: arch_default_cap_def)

lemma safe_ioport_insert_not_ioport[simp]:
  "\<not>is_ioport_cap newcap \<Longrightarrow> safe_ioport_insert newcap oldcap s"
  by (clarsimp simp: safe_ioport_insert_def)

lemma set_untyped_cap_invs_simple[Untyped_AI_assms]:
  "\<lbrace>\<lambda>s. descendants_range_in {ptr .. ptr+2^sz - 1} cref s \<and> pspace_no_overlap_range_cover ptr sz s \<and> invs s
  \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz \<and> obj_ref_of c = ptr \<and> cap_is_device c = dev) cref s \<and> idx \<le> 2^ sz\<rbrace>
  set_cap (cap.UntypedCap dev ptr sz idx) cref
 \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: cte_wp_at_caps_of_state invs_def valid_state_def)
  apply (rule hoare_pre)
  apply (wp set_free_index_valid_pspace_simple set_cap_valid_mdb_simple
    set_cap_idle update_cap_ifunsafe)
  apply (simp add:valid_irq_node_def)
  apply wps
  apply (wp hoare_vcg_all_lift set_cap_irq_handlers set_cap_valid_arch_caps
    set_cap_irq_handlers cap_table_at_lift_valid set_cap_typ_at
    set_untyped_cap_refs_respects_device_simple set_cap_no_new_ioports_arch_valid_arch_state)
  apply (clarsimp simp:cte_wp_at_caps_of_state is_cap_simps)
  apply (intro conjI,clarsimp)
        apply (rule ext,clarsimp simp:is_cap_simps)
       apply (clarsimp split:cap.splits simp:is_cap_simps appropriate_cte_cap_def)
      apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
       apply clarsimp
      apply (clarsimp simp:is_cap_simps ex_cte_cap_wp_to_def appropriate_cte_cap_def cte_wp_at_caps_of_state)
     apply (clarsimp dest!:valid_global_refsD2 simp:cap_range_def)
    apply (simp add:valid_irq_node_def)
   apply (clarsimp simp:valid_irq_node_def)
  apply (clarsimp simp:no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state vs_cap_ref_def)
  apply (case_tac cap)
   apply (simp_all add:vs_cap_ref_def table_cap_ref_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap)
   apply simp_all
  apply (clarsimp simp:cap_refs_in_kernel_window_def
              valid_refs_def simp del:split_paired_All)
  apply (drule_tac x = cref in spec)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply fastforce
  done


lemma pbfs_atleast_pageBits':
  "pageBits \<le> pageBitsForSize sz"by (cases sz, simp_all add: pageBits_def)


lemma pbfs_less_wb':
  "pageBitsForSize sz < word_bits"by (cases sz, simp_all add: word_bits_conv pageBits_def bit_simps)

lemma delete_objects_rewrite[Untyped_AI_assms]:
  "\<lbrakk> word_size_bits \<le> sz; sz\<le> word_bits;ptr && ~~ mask sz = ptr\<rbrakk> \<Longrightarrow> delete_objects ptr sz =
    do y \<leftarrow> modify (clear_um {ptr + of_nat k |k. k < 2 ^ sz});
    modify (detype {ptr && ~~ mask sz..ptr + 2 ^ sz - 1})
    od"
  apply (clarsimp simp:delete_objects_def freeMemory_def word_size_def word_size_bits_def)
  apply (subgoal_tac "is_aligned (ptr &&~~ mask sz) sz")
  apply (subst mapM_storeWord_clear_um[simplified word_size_def word_size_bits_def])
  apply (simp)
  apply simp
  apply (simp add:range_cover_def)
  apply clarsimp
  apply (rule is_aligned_neg_mask)
  apply simp
  done

declare store_pde_pred_tcb_at [wp]

(* nonempty_table *)
definition
  nonempty_table :: "machine_word set \<Rightarrow> Structures_A.kernel_object \<Rightarrow> bool"
where
 "nonempty_table S ko \<equiv>
    (a_type ko \<in> AArch ` { APageTable, APageDirectory, APDPointerTable, APageMapL4 })
       \<and> \<not> empty_table S ko"

lemma reachable_pg_cap_exst_update[simp]:
  "reachable_pg_cap x (trans_state f (s::'state_ext::state_ext state)) = reachable_pg_cap x s"
  by (simp add: reachable_pg_cap_def vs_lookup_pages_def
                vs_lookup_pages1_def obj_at_def)

lemma default_PDPT_capD:
  "default_cap tp oref sz dev = ArchObjectCap (PDPointerTableCap p None)
  \<Longrightarrow>oref = p \<and> tp = ArchObject PDPTObj"
  apply (case_tac tp, simp_all)
  apply (case_tac x6, simp_all add: arch_default_cap_def)
  done

lemma create_cap_valid_arch_caps[wp, Untyped_AI_assms]:
  "\<lbrace>valid_arch_caps
      and valid_cap (default_cap tp oref sz dev)
      and (\<lambda>(s::'state_ext::state_ext state). \<forall>r\<in>obj_refs (default_cap tp oref sz dev).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
      and cte_wp_at ((=) cap.NullCap) cref
      and K (tp \<noteq> ArchObject ASIDPoolObj)\<rbrace>
     create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: create_cap_def set_cdt_def)
  apply (wp set_cap_valid_arch_caps)
  apply (simp add: trans_state_update[symmetric] del: trans_state_update)
  apply (wp hoare_vcg_disj_lift hoare_vcg_conj_lift hoare_vcg_all_lift hoare_vcg_imp_lift | simp)+

  apply (clarsimp simp del: split_paired_All split_paired_Ex
                            imp_disjL
                      simp: cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                         cte_wp_at_caps_of_state)
   apply (case_tac "\<exists>x. x \<in> obj_refs cap")
    apply (clarsimp dest!: obj_ref_elemD)
    apply (case_tac cref, fastforce)
   apply (simp add: obj_ref_none_no_asid)
  apply (rule conjI)
   apply (auto simp: is_cap_simps valid_cap_def second_level_tables_def
                     obj_at_def nonempty_table_def a_type_simps)[1]
  apply (clarsimp simp del: imp_disjL)
  apply (case_tac "\<exists>x. x \<in> obj_refs cap")
   apply (clarsimp dest!: obj_ref_elemD)
   apply fastforce
  apply (auto simp: is_cap_simps)[1]
  done


lemma create_cap_cap_refs_in_kernel_window[wp, Untyped_AI_assms]:
  "\<lbrace>cap_refs_in_kernel_window and cte_wp_at (\<lambda>c. cap_range (default_cap tp oref sz dev) \<subseteq> cap_range c) p\<rbrace>
     create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) cap_refs_in_kernel_windowD)
  apply blast
  done

lemma create_cap_ioports[wp]:
  "\<lbrace>valid_ioports and cte_wp_at (\<lambda>_. True) cref\<rbrace> create_cap tp sz p dev (cref,oref) \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  by (wpsimp wp: set_cap_ioports_safe set_cdt_cte_wp_at
              simp: safe_ioport_insert_not_ioport[OF default_cap_not_ioport] create_cap_def)

lemma create_cap_valid_arch_state[wp, Untyped_AI_assms]:
  "\<lbrace>valid_arch_state and cte_wp_at (\<lambda>_. True) cref\<rbrace>
   create_cap tp sz p dev (cref,oref)
   \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (wp valid_arch_state_lift_ioports_aobj_at create_cap_aobj_at)+
     (simp add: valid_arch_state_def)

(* FIXME: move *)
lemma simpler_store_pml4e_def:
  "store_pml4e p pde s =
    (case (kheap s)(p && ~~ mask pml4_bits) of
          Some (ArchObj (PageMapL4 pml4)) =>
            ({((), s\<lparr>kheap := (kheap s)(p && ~~ mask pml4_bits \<mapsto>
                                       (ArchObj (PageMapL4 (pml4(ucast (p && mask pml4_bits >> word_size_bits) := pde)))))\<rparr>)}, False)
        | _ => ({}, True))"
  apply     (auto simp: store_pml4e_def set_object_def get_object_def simpler_gets_def assert_def a_type_simps
                        return_def fail_def set_object_def get_def put_def bind_def get_pml4_def aa_type_simps
                        set_arch_obj_simps
                 split: Structures_A.kernel_object.splits option.splits arch_kernel_obj.splits if_split_asm)
  done

lemma neg_mask_pml4_bits_3_aligned[simp]:
  "is_aligned (p && ~~ mask pml4_bits) 3"
  apply (rule_tac x = 3 in is_aligned_weaken[OF is_aligned_neg_mask])
  apply (simp add: bit_simps)+
  done

lemma store_pml4e_weaken:
  "\<lbrace>\<lambda>s. pml4e_at (p && ~~ mask pml4_bits) s \<longrightarrow> P s\<rbrace> store_pml4e p e \<lbrace>Q\<rbrace> =
   \<lbrace>P\<rbrace> store_pml4e p e \<lbrace>Q\<rbrace>"
  apply (rule iffI)
   apply (simp add: valid_def)
   apply (erule allEI)
   apply clarsimp
  apply (simp add: valid_def)
  apply (erule allEI)
  apply clarsimp
  apply (rule use_valid, assumption)
   apply (simp add: store_pml4e_def set_arch_obj_simps set_object_def)
   apply (wp get_object_wp)
  apply (clarsimp simp: pml4e_at_def obj_at_def a_type_simps)
  apply (drule bspec, assumption)
  apply (simp add: simpler_store_pml4e_def obj_at_def fun_upd_def
            split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  done

lemma store_pml4e_nonempty_table:
  "\<lbrace>\<lambda>s. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
           \<and> (\<forall>rf. pml4e_ref pml4e = Some rf \<longrightarrow>
                   rf \<in> set (second_level_tables (arch_state s)))
           \<and> ucast (pml4e_ptr && mask pml4_bits >> 3) \<in> kernel_mapping_slots\<rbrace>
     store_pml4e pml4e_ptr pml4e
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)\<rbrace>"
  apply (simp add: store_pml4e_def set_arch_obj_simps set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def nonempty_table_def a_type_def word_size_bits_def empty_table_def)
  done

lemma store_pml4e_global_global_objs:
  "\<lbrace>\<lambda>s. valid_global_objs s \<and> valid_arch_state s
           \<and> (\<forall>rf. pml4e_ref pml4e = Some rf \<longrightarrow>
                   rf \<in> set (second_level_tables (arch_state s)))
           \<and> ucast (pml4e_ptr && mask pml4_bits >> 3) \<in> kernel_mapping_slots
   \<rbrace>
   store_pml4e pml4e_ptr pml4e
   \<lbrace>\<lambda>rv s. valid_global_objs s\<rbrace>"
  apply (simp add: store_pml4e_def set_arch_obj_simps set_pd_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def fun_upd_def[symmetric] bit_simps
                        valid_global_objs_upd_def empty_table_def valid_global_objs_def)
  done

lemma valid_arch_state_global_pml4:
  "\<lbrakk> valid_arch_state s; pspace_aligned s \<rbrakk>
    \<Longrightarrow> obj_at (\<lambda>ko. \<exists>pd. ko = ArchObj (PageMapL4 pd)) (x64_global_pml4 (arch_state s)) s
           \<and> is_aligned (x64_global_pml4 (arch_state s)) pml4_bits"
  apply (clarsimp simp: valid_arch_state_def obj_at_def
                        pd_bits_def pageBits_def
                 elim!: obj_at_weakenE)
  apply (clarsimp dest!: pspace_alignedD simp: pml4_bits_def)
  done

lemmas pml4_shifting' = pml4_shifting(2)

lemma pml4_bits_ptTranslationBits_diff:
  "pml4_bits - word_size_bits = ptTranslationBits"
  by (simp add: bit_simps)

lemma copy_global_mappings_nonempty_table:
  "is_aligned pm pml4_bits \<Longrightarrow>
   \<lbrace>\<lambda>s. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s) \<and>
        valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s\<rbrace>
   copy_global_mappings pm
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table
                        (set (second_level_tables (arch_state s)))) r s) \<and>
           valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply (rule bind_wp [OF _ gets_sp])
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp[where S="{x. get_pml4_index pptr_base \<le> x
                                       \<and> x < 2 ^ (pml4_bits - word_size_bits)}"])
    apply (wp get_pml4e_wp hoare_vcg_ball_lift
              store_pml4e_weaken[THEN iffD2,OF store_pml4e_nonempty_table]
              store_pml4e_weaken[THEN iffD2,OF store_pml4e_global_global_objs]
           | simp)+
    apply clarsimp
    apply (subst (asm) is_aligned_add_helper[THEN conjunct2])
      apply (clarsimp simp: valid_arch_state_def pspace_aligned_def dom_def
                            obj_at_def)
      apply (drule_tac x="x64_global_pml4 (arch_state s)" in spec, erule impE,
             fastforce)
      apply (simp add: pml4_bits_def pageBits_def)
     apply (erule shiftl_less_t2n)
     apply (simp add: bit_simps)
    apply (clarsimp simp: valid_arch_state_def valid_global_objs_def obj_at_def
                          empty_table_def imp_conjR)
    apply (clarsimp simp: is_aligned_neg_mask_eq mask_add_aligned)
    apply (fold word_size_bits_def)
    apply (strengthen in_kernel_mapping_slotsI[mk_strg] shiftl_shiftr_id[mk_strg]
                       shiftr_less_t2n3[mk_strg])+
    apply (clarsimp simp: pml4_bits_ptTranslationBits_diff pml4_translation_bits)
    apply (simp add: is_aligned_shiftr_shiftl[OF aligned_after_mask,OF is_aligned_shiftl])
    apply (cut_tac x = "x << word_size_bits" and n = pml4_bits in less_mask_eq)
     apply (rule shiftl_less_t2n)
      apply (simp add: pml4_bits_ptTranslationBits_diff)
     apply (simp add: bit_simps)
    apply (simp add: word_size_bits_def)
    apply (subst shiftl_shiftr_id)
      apply simp
     apply (erule less_le_trans, simp add: bit_simps)
    apply simp
    apply (rule shiftl_less_t2n, simp add: bit_simps)
    apply (simp add: bit_simps)
   apply (clarsimp simp: bit_simps le_less_trans)
  apply simp
  done


lemma mapM_copy_global_mappings_nonempty_table[wp]:
  "\<lbrace>(\<lambda>s. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
        \<and> valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s) and
    K (\<forall>pd\<in>set pds. is_aligned pd pml4_bits)\<rbrace>
   mapM_x copy_global_mappings pds
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp', rule copy_global_mappings_nonempty_table)
   apply simp_all
  done

lemma init_arch_objects_nonempty_table[Untyped_AI_assms, wp]:
  "\<lbrace>(\<lambda>s. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
         \<and> valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s) and
    K (\<forall>ref\<in>set refs. is_aligned ref (obj_bits_api tp us))\<rbrace>
        init_arch_objects tp dev ptr bits us refs
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: init_arch_objects_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp unless_wp | wpc | simp add: reserve_region_def second_level_tables_def)+
  apply (clarsimp simp: obj_bits_api_def default_arch_object_def pml4_bits_def pageBits_def)
  done

lemma nonempty_table_caps_of[Untyped_AI_assms]:
  "nonempty_table S ko \<Longrightarrow> caps_of ko = {}"
  by (auto simp: caps_of_def cap_of_def nonempty_table_def a_type_def
          split: Structures_A.kernel_object.split if_split_asm)


lemma nonempty_default[simp, Untyped_AI_assms]:
  "tp \<noteq> Untyped \<Longrightarrow> \<not> nonempty_table S (default_object tp dev us)"
  apply (case_tac tp, simp_all add: default_object_def nonempty_table_def
                                    a_type_def)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type, simp_all add: default_arch_object_def)
   apply (simp_all add: empty_table_def pde_ref_def)
  done

lemma set_pml4e_cte_wp_at_iin[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at (P' (interrupt_irq_node s)) p s)\<rbrace>
   store_pml4e q pml4
   \<lbrace>\<lambda>_ s. P (cte_wp_at (P' (interrupt_irq_node s)) p s)\<rbrace>"
  apply (clarsimp simp: store_pml4e_def set_arch_obj_simps)
  apply (rule hoare_pre)
  apply (wp set_aobject_cte_wp_at | wps | simp)+
  done

crunch init_arch_objects
  for cte_wp_at_iin[wp]: "\<lambda>s. P (cte_wp_at (P' (interrupt_irq_node s)) p s)"
  (ignore: clearMemory store_pml4e wp: crunch_wps unless_wp)

lemmas init_arch_objects_ex_cte_cap_wp_to
    = init_arch_objects_excap

lemma obj_is_device_vui_eq[Untyped_AI_assms]:
  "valid_untyped_inv ui s
      \<Longrightarrow> case ui of Retype slot reset ptr_base ptr tp us slots dev
          \<Rightarrow> obj_is_device tp dev = dev"
  apply (cases ui, clarsimp)
  apply (clarsimp simp: obj_is_device_def
                 split: apiobject_type.split)
  apply (intro impI conjI allI, simp_all add: is_frame_type_def default_object_def)
  apply (simp add: default_arch_object_def split: aobject_type.split)
  apply (auto simp: arch_is_frame_type_def)
  done

lemmas [Untyped_AI_assms] = set_cap_non_arch_valid_arch_state

end

global_interpretation Untyped_AI? : Untyped_AI
  where nonempty_table = X64.nonempty_table
  proof goal_cases
    interpret Arch .
    case 1 show ?case
    by (unfold_locales; (fact Untyped_AI_assms)?)
  qed

end
