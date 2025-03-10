(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchCNodeInv_AI
imports CNodeInv_AI
begin

context Arch begin arch_global_naming

named_theorems CNodeInv_AI_assms

lemma valid_cnode_capI:
  "\<lbrakk>cap_table_at n w s; valid_objs s; pspace_aligned s; n > 0; length g \<le> 64\<rbrakk>
   \<Longrightarrow> s \<turnstile> cap.CNodeCap w n g"
  apply (simp add: valid_cap_def cap_aligned_def)
  apply (rule conjI)
   apply (clarsimp simp add: pspace_aligned_def obj_at_def)
   apply (drule bspec, fastforce)
   apply (clarsimp simp: is_obj_defs wf_obj_bits)
  apply (clarsimp simp add: obj_at_def is_obj_defs valid_objs_def dom_def)
  apply (erule allE, erule impE, blast)
  apply (simp add: valid_obj_def valid_cs_def valid_cs_size_def)
  apply (simp add: word_bits_def cte_level_bits_def)
  done

(* unused *)
lemma derive_cap_objrefs [CNodeInv_AI_assms]:
  "\<lbrace>\<lambda>s. P (obj_refs cap)\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> P (obj_refs rv)\<rbrace>,-"
  apply (cases cap, simp_all add: derive_cap_def is_zombie_def)
          apply ((wp ensure_no_children_inv | simp add: o_def | rule hoare_pre)+)[11]
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all add: arch_derive_cap_def)
         by (wp | wpc | simp add: o_def)+

lemma derive_cap_zobjrefs [CNodeInv_AI_assms]:
  "\<lbrace>\<lambda>s. P (zobj_refs cap)\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> P (zobj_refs rv)\<rbrace>,-"
  apply (cases cap, simp_all add: derive_cap_def is_zombie_def)
          apply ((wp ensure_no_children_inv | simp add: o_def | rule hoare_pre)+)[11]
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all add: arch_derive_cap_def)
         by (wp | wpc |simp add: o_def)+

lemma update_cap_objrefs [CNodeInv_AI_assms]:
  "\<lbrakk> update_cap_data P dt cap \<noteq> NullCap \<rbrakk> \<Longrightarrow>
     obj_refs (update_cap_data P dt cap) = obj_refs cap"
  by (case_tac cap,
      simp_all add: update_cap_data_closedform arch_update_cap_data_def Let_def
             split: if_split_asm arch_cap.splits)


lemma update_cap_zobjrefs [CNodeInv_AI_assms]:
  "\<lbrakk> update_cap_data P dt cap \<noteq> cap.NullCap \<rbrakk> \<Longrightarrow>
     zobj_refs (update_cap_data P dt cap) = zobj_refs cap"
  apply (case_tac cap,
      simp_all add: update_cap_data_closedform arch_update_cap_data_def Let_def
             split: if_split_asm arch_cap.splits)
  done


lemma copy_mask [simp, CNodeInv_AI_assms]:
  "copy_of (mask_cap R c) = copy_of c"
  apply (rule ext)
  apply (auto simp: copy_of_def is_cap_simps mask_cap_def
                    cap_rights_update_def same_object_as_def
                    bits_of_def acap_rights_update_def
         split: cap.splits arch_cap.splits bool.splits)
  done

lemma update_cap_data_mask_Null [simp, CNodeInv_AI_assms]:
  "(update_cap_data P x (mask_cap m c) = NullCap) = (update_cap_data P x c = NullCap)"
  unfolding update_cap_data_def mask_cap_def
  apply (cases c)
  apply (clarsimp simp: is_cap_simps cap_rights_update_def badge_update_def split: if_splits)+
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; clarsimp simp: arch_update_cap_data_def acap_rights_update_def split: if_splits)
  done

lemma cap_master_update_cap_data [CNodeInv_AI_assms]:
  "\<lbrakk> update_cap_data P x c \<noteq> NullCap \<rbrakk>
        \<Longrightarrow> cap_master_cap (update_cap_data P x c) = cap_master_cap c"
  apply (simp add: update_cap_data_def split del: if_split split: if_split_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done

lemma same_object_as_def2:
  "same_object_as cp cp' = (cap_master_cap cp = cap_master_cap cp'
                                \<and> \<not> cp = NullCap \<and> \<not> is_untyped_cap cp
                                \<and> \<not> is_zombie cp
                                \<and> cp \<noteq> IRQControlCap
                                \<and> (is_arch_cap cp \<longrightarrow>
                                     (case the_arch_cap cp of
                                         PageCap d x rs tp sz v \<Rightarrow> x \<le> x + 2 ^ pageBitsForSize sz - 1
                                       | _ \<Rightarrow> True)))"
  apply (simp add: same_object_as_def is_cap_simps split: cap.split)
  apply (auto simp: cap_master_cap_def bits_of_def is_cap_simps
             split: cap.splits arch_cap.splits)
  done

lemma same_object_as_cap_master [CNodeInv_AI_assms]:
  "same_object_as cap cap' \<Longrightarrow> cap_master_cap cap = cap_master_cap cap'"
  by (simp add: same_object_as_def2)

lemma weak_derived_cap_is_device[CNodeInv_AI_assms]:
  "\<lbrakk>weak_derived c' c\<rbrakk> \<Longrightarrow>  cap_is_device c = cap_is_device c'"
  apply (auto simp: weak_derived_def copy_of_def is_cap_simps
                    same_object_as_def2
             split: if_split_asm
             dest!: master_cap_eq_is_device_cap_eq)
  done

lemma cap_asid_update_cap_data [CNodeInv_AI_assms]:
  "update_cap_data P x c \<noteq> NullCap
         \<Longrightarrow> cap_asid (update_cap_data P x c) = cap_asid c"
  apply (simp add: update_cap_data_def split del: if_split split: if_split_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done

lemma cap_vptr_update_cap_data [CNodeInv_AI_assms]:
  "update_cap_data P x c \<noteq> NullCap
         \<Longrightarrow> cap_vptr (update_cap_data P x c) = cap_vptr c"
  apply (simp add: update_cap_data_def split del: if_split split: if_split_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done

lemma cap_asid_base_update_cap_data [CNodeInv_AI_assms]:
  "update_cap_data P x c \<noteq> NullCap
         \<Longrightarrow> cap_asid_base (update_cap_data P x c) = cap_asid_base c"
  apply (simp add: update_cap_data_def split del: if_split split: if_split_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done

lemma same_object_as_update_cap_data [CNodeInv_AI_assms]:
  "\<lbrakk> update_cap_data P x c \<noteq> NullCap; same_object_as c' c \<rbrakk> \<Longrightarrow>
  same_object_as c' (update_cap_data P x c)"
  apply (clarsimp simp: same_object_as_def is_cap_simps
                  split: cap.split_asm arch_cap.splits if_split_asm)
  apply (auto simp: update_cap_data_def badge_update_def cap_rights_update_def is_cap_simps
                   arch_update_cap_data_def
                   Let_def split_def the_cnode_cap_def bits_of_def
              split: if_split_asm cap.splits)
  done

lemma is_reply_update_cap_data[simp]:
  "is_reply_cap (update_cap_data P x c) = is_reply_cap c"
  by (simp add:is_reply_cap_def update_cap_data_def arch_update_cap_data_def the_cnode_cap_def
               is_arch_cap_def badge_update_def split:cap.split)

lemma is_master_reply_update_cap_data[simp]:
  "is_master_reply_cap (update_cap_data P x c) = is_master_reply_cap c"
  by (simp add:is_master_reply_cap_def update_cap_data_def arch_update_cap_data_def
               the_cnode_cap_def is_arch_cap_def badge_update_def split:cap.split)

lemma weak_derived_update_cap_data [CNodeInv_AI_assms]:
  "\<lbrakk>update_cap_data P x c \<noteq> NullCap; weak_derived c c'\<rbrakk>
  \<Longrightarrow> weak_derived (update_cap_data P x c) c'"
  apply (simp add: weak_derived_def copy_of_def
                   cap_master_update_cap_data cap_asid_update_cap_data
                   cap_asid_base_update_cap_data
                   cap_vptr_update_cap_data
              split del: if_split cong: if_cong)
  apply (erule disjE)
   apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: is_cap_simps)
     apply (simp add: update_cap_data_def arch_update_cap_data_def is_cap_simps)
   apply (erule (1) same_object_as_update_cap_data)
  apply clarsimp
  apply (rule conjI, clarsimp simp: is_cap_simps update_cap_data_def split del: if_split)+
  apply clarsimp
  apply (clarsimp simp: same_object_as_def is_cap_simps
                 split: cap.split_asm arch_cap.splits if_split_asm)
  apply (auto simp: update_cap_data_def badge_update_def cap_rights_update_def is_cap_simps
                    arch_update_cap_data_def
                    Let_def split_def the_cnode_cap_def bits_of_def
             split: if_split_asm cap.splits arch_cap.splits)
  done

lemma cap_badge_update_cap_data [CNodeInv_AI_assms]:
  "update_cap_data False x c \<noteq> NullCap \<and> (bdg, cap_badge c) \<in> capBadge_ordering False
       \<longrightarrow> (bdg, cap_badge (update_cap_data False x c)) \<in> capBadge_ordering False"
  apply clarsimp
  apply (erule capBadge_ordering_trans)
  apply (simp add: update_cap_data_def split del: if_split split: if_split_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done


lemma cap_vptr_rights_update[simp, CNodeInv_AI_assms]:
  "cap_vptr (cap_rights_update f c) = cap_vptr c"
  by (simp add: cap_vptr_def cap_rights_update_def acap_rights_update_def
           split: cap.splits arch_cap.splits bool.splits)

lemma cap_vptr_mask[simp, CNodeInv_AI_assms]:
  "cap_vptr (mask_cap m c) = cap_vptr c"
  by (simp add: mask_cap_def)

lemma cap_asid_base_rights [simp, CNodeInv_AI_assms]:
  "cap_asid_base (cap_rights_update R c) = cap_asid_base c"
  by (auto simp add: cap_rights_update_def acap_rights_update_def
           split: cap.splits arch_cap.splits bool.splits)

lemma cap_asid_base_mask[simp, CNodeInv_AI_assms]:
  "cap_asid_base (mask_cap m c) = cap_asid_base c"
  by (simp add: mask_cap_def)

lemma weak_derived_mask [CNodeInv_AI_assms]:
  "\<lbrakk> weak_derived c c'; cap_aligned c \<rbrakk> \<Longrightarrow> weak_derived (mask_cap m c) c'"
  unfolding weak_derived_def
  apply simp
  apply (erule disjE)
   apply simp
  apply (simp add: mask_cap_def cap_rights_update_def
                   copy_of_def same_object_as_def bits_of_def
                   is_cap_simps acap_rights_update_def
            split: cap.split arch_cap.split)+
  apply (clarsimp simp: cap_aligned_def
                        is_aligned_no_overflow)
  done


lemma vs_cap_ref_update_cap_data[simp, CNodeInv_AI_assms]:
  "vs_cap_ref (update_cap_data P d cap) = vs_cap_ref cap"
  by (simp add: vs_cap_ref_def update_cap_data_closedform
                arch_update_cap_data_def Let_def
         split: arch_cap.splits cap.split if_splits)


lemma invs_irq_state_independent[intro!, simp, CNodeInv_AI_assms]:
  "invs (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = invs s"
  by (clarsimp simp: irq_state_independent_A_def invs_def
      valid_state_def valid_pspace_def valid_mdb_def valid_ioc_def valid_idle_def
      only_idle_def if_unsafe_then_cap_def valid_reply_caps_def
      valid_reply_masters_def valid_global_refs_def valid_arch_state_def
      valid_irq_node_def valid_irq_handlers_def valid_machine_state_def
      valid_arch_caps_def valid_global_objs_def
      valid_kernel_mappings_def equal_kernel_mappings_def
      valid_asid_map_def valid_global_vspace_mappings_def
      pspace_in_kernel_window_def cap_refs_in_kernel_window_def
      cur_tcb_def sym_refs_def state_refs_of_def vspace_at_asid_def
      swp_def valid_irq_states_def)


lemma cte_at_nat_to_cref_zbits [CNodeInv_AI_assms]:
  "\<lbrakk> s \<turnstile> Zombie oref zb n; m < n \<rbrakk>
     \<Longrightarrow> cte_at (oref, nat_to_cref (zombie_cte_bits zb) m) s"
  apply (subst(asm) valid_cap_def)
  apply (cases zb, simp_all add: valid_cap_def)
   apply (clarsimp simp: obj_at_def is_tcb)
   apply (drule(1) tcb_cap_cases_lt [OF order_less_le_trans])
   apply clarsimp
   apply (rule cte_wp_at_tcbI, fastforce+)
  apply (clarsimp elim!: cap_table_at_cte_at simp: cap_aligned_def)
  apply (simp add: nat_to_cref_def word_bits_conv)
  done


lemma copy_of_cap_range [CNodeInv_AI_assms]:
  "copy_of cap cap' \<Longrightarrow> cap_range cap = cap_range cap'"
  apply (clarsimp simp: copy_of_def split: if_split_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def cap_range_def
                      split: cap.split_asm)+
  apply (rename_tac acap' acap)
   apply (case_tac acap, simp_all)
       apply (clarsimp split: arch_cap.split_asm cap.split_asm)+
  done


lemma copy_of_zobj_refs [CNodeInv_AI_assms]:
  "copy_of cap cap' \<Longrightarrow> zobj_refs cap = zobj_refs cap'"
  apply (clarsimp simp: copy_of_def split: if_split_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm)+
  apply (rename_tac acap' acap)
   apply (case_tac acap, simp_all)
       apply (clarsimp split: arch_cap.split_asm cap.split_asm)+
  done


lemma vs_cap_ref_master [CNodeInv_AI_assms]:
  "\<lbrakk> cap_master_cap cap = cap_master_cap cap';
           cap_asid cap = cap_asid cap';
           cap_asid_base cap = cap_asid_base cap';
           cap_vptr cap = cap_vptr cap' \<rbrakk>
        \<Longrightarrow> vs_cap_ref cap = vs_cap_ref cap'"
  apply (rule ccontr)
  apply (clarsimp simp: vs_cap_ref_def cap_master_cap_def
                 split: cap.split_asm)
  apply (clarsimp simp: cap_asid_def split: arch_cap.split_asm option.split_asm)
  done

lemma weak_derived_vs_cap_ref [CNodeInv_AI_assms]:
  "weak_derived c c' \<Longrightarrow> vs_cap_ref c = vs_cap_ref c'"
  by (auto simp: weak_derived_def copy_of_def
                 same_object_as_def2
          split: if_split_asm elim: vs_cap_ref_master[OF sym])

lemma weak_derived_table_cap_ref [CNodeInv_AI_assms]:
  "weak_derived c c' \<Longrightarrow> table_cap_ref c = table_cap_ref c'"
  apply (clarsimp simp: weak_derived_def copy_of_def
                 same_object_as_def2
          split: if_split_asm)
   apply (elim disjE,simp_all add:is_cap_simps)
  apply (elim disjE,simp_all)
  apply clarsimp
  apply (frule vs_cap_ref_master[OF sym],simp+)
  apply (drule vs_cap_ref_eq_imp_table_cap_ref_eq')
   apply simp
  apply simp
  done


lemma weak_derived_vspace_asid:
  "weak_derived c c' \<Longrightarrow> cap_asid c = cap_asid c'
                       \<and> is_pt_cap c = is_pt_cap c'
                       \<and> is_pd_cap c = is_pd_cap c'
                       \<and> is_pdpt_cap c = is_pdpt_cap c'
                       \<and> is_pml4_cap c = is_pml4_cap c'"
  by (auto simp: weak_derived_def copy_of_def is_cap_simps
                 same_object_as_def2 is_pt_cap_def
                 cap_master_cap_simps
          split: if_split_asm
          dest!: cap_master_cap_eqDs)

lemma weak_derived_ASIDPool1:
  "weak_derived (cap.ArchObjectCap (ASIDPoolCap ap asid)) cap =
  (cap = cap.ArchObjectCap (ASIDPoolCap ap asid))"
  apply (rule iffI)
   prefer 2
   apply simp
  apply (clarsimp simp: weak_derived_def copy_of_def split: if_split_asm)
  apply (clarsimp simp: same_object_as_def2 cap_master_cap_simps dest!: cap_master_cap_eqDs)
  done

lemma weak_derived_ASIDPool2:
  "weak_derived cap (ArchObjectCap (ASIDPoolCap ap asid)) =
  (cap = ArchObjectCap (ASIDPoolCap ap asid))"
  apply (rule iffI)
   prefer 2
   apply simp
  apply (clarsimp simp: weak_derived_def copy_of_def split: if_split_asm)
  apply (auto simp: same_object_as_def2 cap_master_cap_simps dest!: cap_master_cap_eqDs)
  done

lemmas weak_derived_ASIDPool [simp] =
  weak_derived_ASIDPool1 weak_derived_ASIDPool2


lemma swap_of_caps_valid_arch_caps [CNodeInv_AI_assms]:
  "\<lbrace>valid_arch_caps and
    cte_wp_at (weak_derived c) a and
    cte_wp_at (weak_derived c') b\<rbrace>
   do
     y \<leftarrow> set_cap c b;
     set_cap c' a
   od
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: valid_arch_caps_def
                    valid_vs_lookup_def valid_table_caps_def pred_conj_def
               del: split_paired_Ex split_paired_All imp_disjL)
   apply (wp hoare_vcg_all_lift hoare_convert_imp[OF set_cap.vs_lookup_pages]
             hoare_vcg_disj_lift hoare_convert_imp[OF set_cap_caps_of_state]
             hoare_use_eq[OF set_cap_arch set_cap_obj_at_impossible[where P="\<lambda>x. x"]])
  apply (clarsimp simp: valid_arch_caps_def cte_wp_at_caps_of_state
              simp del: split_paired_Ex split_paired_All imp_disjL)
  apply (frule weak_derived_obj_refs[where dcap=c])
  apply (frule weak_derived_obj_refs[where dcap=c'])
  apply (frule weak_derived_vspace_asid[where c=c])
  apply (frule weak_derived_vspace_asid[where c=c'])
  apply (intro conjI)
     apply (simp add: valid_vs_lookup_def del: split_paired_Ex split_paired_All)
     apply (elim allEI)
     apply (intro impI disjCI2)
     apply (simp del: split_paired_Ex split_paired_All)
     apply (elim conjE)
     apply (erule exfEI[where f="id (a := b, b := a)"])
     subgoal by (clarsimp dest!: weak_derived_vs_cap_ref, intro conjI; clarsimp)
    apply (simp add: valid_table_caps_def empty_table_caps_of
                del: split_paired_Ex split_paired_All imp_disjL)
   apply (simp add: unique_table_caps_def
               del: split_paired_Ex split_paired_All imp_disjL
                    split del: if_split)
   apply (erule allfEI[where f="id (a := b, b := a)"])
   apply (erule allfEI[where f="id (a := b, b := a)"])
   apply (clarsimp split del: if_split split: if_split_asm)
  apply (simp add: unique_table_refs_def
              del: split_paired_All split del: if_split)
  apply (erule allfEI[where f="id (a := b, b := a)"])
  apply (erule allfEI[where f="id (a := b, b := a)"])
  apply (clarsimp split del: if_split split: if_split_asm dest!:vs_cap_ref_to_table_cap_ref
                      dest!: weak_derived_table_cap_ref)
  done


lemma cap_swap_asid_map[wp, CNodeInv_AI_assms]:
  "\<lbrace>valid_asid_map and
    cte_wp_at (weak_derived c) a and
    cte_wp_at (weak_derived c') b\<rbrace>
     cap_swap c a c' b \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: cap_swap_def set_cdt_def valid_asid_map_def vspace_at_asid_def)
  apply (rule hoare_pre)
   apply (wp set_cap.vs_lookup|simp
          |rule hoare_lift_Pf [where f=arch_state])+
  done


lemma cap_swap_cap_refs_in_kernel_window[wp, CNodeInv_AI_assms]:
  "\<lbrace>cap_refs_in_kernel_window and
    cte_wp_at (weak_derived c) a and
    cte_wp_at (weak_derived c') b\<rbrace>
     cap_swap c a c' b \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (rule hoare_pre)
   apply (wp | simp split del: if_split)+
  apply (auto dest!: cap_refs_in_kernel_windowD
               simp: cte_wp_at_caps_of_state weak_derived_cap_range)
  done


lemma cap_swap_ioports[wp]:
  "\<lbrace>valid_ioports and cte_wp_at (weak_derived c) a and cte_wp_at (weak_derived c') b\<rbrace>
     cap_swap c a c' b
   \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  apply (simp add: valid_ioports_def all_ioports_issued_def ioports_no_overlap_def issued_ioports_def)
  apply (rule hoare_pre)
   apply (wp hoare_use_eq [where f=arch_state,
                           OF cap_swap_arch cap_swap_caps_of_state])
  apply (clarsimp simp: cte_wp_at_caps_of_state
                 elim!: ranE split: if_split_asm
                 dest!: weak_derived_cap_ioports)
  by (fastforce elim!: ranE split: if_split_asm)

lemma same_object_as_IOPortControlCap_eq:
  "same_object_as cap (ArchObjectCap IOPortControlCap) = (cap = ArchObjectCap IOPortControlCap)"
  unfolding same_object_as_def
  by (simp split: cap.splits arch_cap.splits)

lemma copy_of_IOPortControlCap_eq:
  "(copy_of (ArchObjectCap IOPortControlCap) cap) = (cap = ArchObjectCap IOPortControlCap)"
  unfolding copy_of_def
  by (auto simp: is_cap_simps same_object_as_IOPortControlCap_eq)

lemma weak_derived_IOPortControlCap_eq[simp]:
  "weak_derived (ArchObjectCap IOPortControlCap) cap = (cap = ArchObjectCap IOPortControlCap)"
  unfolding weak_derived_def
  by (auto simp: copy_of_IOPortControlCap_eq)

lemma cap_swap_ioport_control[wp]:
  "\<lbrace>ioport_control_unique and cte_wp_at (weak_derived c) a and cte_wp_at (weak_derived c') b\<rbrace>
   cap_swap c a c' b
   \<lbrace>\<lambda>_. ioport_control_unique\<rbrace>"
  apply (wpsimp wp: cap_swap_caps_of_state simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp: ioport_control_unique_def)
  apply (cases a, cases b)
  by (rule conjI; clarsimp)+

lemma cap_swap_valid_arch_state[wp, CNodeInv_AI_assms]:
  "\<lbrace>valid_arch_state and cte_wp_at (weak_derived c) a and cte_wp_at (weak_derived c') b\<rbrace>
   cap_swap c a c' b
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (wp valid_arch_state_lift_ioports_aobj_at cap_swap_aobj_at)+
     (simp add: valid_arch_state_def)

lemma cap_swap_vms[wp, CNodeInv_AI_assms]:
  "\<lbrace>valid_machine_state\<rbrace> cap_swap c a c' b \<lbrace>\<lambda>rv. valid_machine_state\<rbrace>"
  apply (simp add: valid_machine_state_def in_user_frame_def)
  apply (wp cap_swap_typ_at
            hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_disj_lift)
  done

(* FIXME x64: this could probably be generic *)
lemma unat_of_bl_nat_to_cref[CNodeInv_AI_assms]:
  "\<lbrakk> n < 2 ^ len; len < word_bits \<rbrakk>
    \<Longrightarrow> unat (of_bl (nat_to_cref len n) :: machine_word) = n"
  apply (simp add: nat_to_cref_def word_bits_conv of_drop_to_bl
                   word_size)
  apply (subst less_mask_eq)
   apply (rule order_less_le_trans)
    apply (erule of_nat_mono_maybe[rotated])
    apply (rule power_strict_increasing)
     apply simp
    apply simp
   apply simp
  apply (rule unat_of_nat_eq[where 'a=machine_word_len, unfolded word_bits_len_of])
  apply (erule order_less_trans)
  apply (rule power_strict_increasing)
   apply (simp add: word_bits_conv)
  apply simp
  done

lemma zombie_is_cap_toE_pre[CNodeInv_AI_assms]:
  "\<lbrakk> s \<turnstile> Zombie ptr zbits n; invs s; m < n \<rbrakk>
     \<Longrightarrow> (ptr, nat_to_cref (zombie_cte_bits zbits) m) \<in> cte_refs (Zombie ptr zbits n) irqn"
  apply (clarsimp simp add: valid_cap_def cap_aligned_def)
  apply (clarsimp split: option.split_asm)
   apply (simp add: unat_of_bl_nat_to_cref)
   apply (simp add: nat_to_cref_def word_bits_conv)
  apply (simp add: unat_of_bl_nat_to_cref)
  apply (simp add: nat_to_cref_def word_bits_conv)
  done

crunch prepare_thread_delete
  for st_tcb_at_halted[wp]: "st_tcb_at halted t"

lemma finalise_cap_makes_halted_proof[CNodeInv_AI_assms]:
  "\<lbrace>invs and valid_cap cap and (\<lambda>s. ex = is_final_cap' cap s)
         and cte_wp_at ((=) cap) slot\<rbrace>
    finalise_cap cap ex
   \<lbrace>\<lambda>rv s. \<forall>t \<in> obj_refs (fst rv). halted_if_tcb t s\<rbrace>"
  apply (case_tac cap, simp_all)
            apply (wp unbind_notification_valid_objs
                   | clarsimp simp: o_def valid_cap_def cap_table_at_typ
                                    is_tcb obj_at_def
                   | clarsimp simp: halted_if_tcb_def
                             split: option.split
                   | intro impI conjI
                   | rule hoare_drop_imp)+
  apply (drule_tac final_zombie_not_live; (assumption | simp add: invs_iflive)?)
   apply (clarsimp simp: pred_tcb_at_def is_tcb obj_at_def live_def, elim disjE)
    apply (clarsimp; case_tac "tcb_state tcb"; simp)+
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all add: arch_finalise_cap_def)
      apply (wp
             | clarsimp simp: valid_cap_def obj_at_def is_tcb_def is_cap_table_def
                        split: option.splits bool.split
             | intro impI conjI)+
  done

lemmas finalise_cap_makes_halted = finalise_cap_makes_halted_proof

crunch finalise_cap
  for emptyable[wp,CNodeInv_AI_assms]: "\<lambda>s. emptyable sl s"
  (simp: crunch_simps rule: emptyable_lift
     wp: crunch_wps suspend_emptyable unbind_notification_invs unbind_maybe_notification_invs)


lemma finalise_cap_not_reply_master_unlifted [CNodeInv_AI_assms]:
  "(rv, s') \<in> fst (finalise_cap cap sl s) \<Longrightarrow>
   \<not> is_master_reply_cap (fst rv)"
  by (case_tac cap, auto simp: is_cap_simps in_monad liftM_def
                               arch_finalise_cap_def
                        split: if_split_asm arch_cap.split_asm bool.split_asm option.split_asm)


lemma nat_to_cref_0_replicate [CNodeInv_AI_assms]:
  "\<And>n. n < word_bits \<Longrightarrow> nat_to_cref n 0 = replicate n False"
  apply (subgoal_tac "nat_to_cref n (unat (of_bl (replicate n False))) = replicate n False")
   apply simp
  apply (rule nat_to_cref_unat_of_bl')
   apply (simp add: word_bits_def)
  apply simp
  done

lemma prepare_thread_delete_thread_cap [CNodeInv_AI_assms]:
  "\<lbrace>\<lambda>s. caps_of_state s x = Some (cap.ThreadCap p)\<rbrace>
    prepare_thread_delete t
   \<lbrace>\<lambda>rv s. caps_of_state s x = Some (cap.ThreadCap p)\<rbrace>"
  by (wpsimp simp: prepare_thread_delete_def)

end


global_interpretation CNodeInv_AI?: CNodeInv_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact CNodeInv_AI_assms)?)
  qed


termination rec_del by (rule rec_del_termination)


context Arch begin arch_global_naming

lemma post_cap_delete_pre_is_final_cap':
  "\<And>rv s'' rva s''a s.
       \<lbrakk>valid_ioports s; caps_of_state s slot = Some cap; is_final_cap' cap s; cap_cleanup_opt cap \<noteq> NullCap\<rbrakk>
       \<Longrightarrow> post_cap_delete_pre (cap_cleanup_opt cap) ((caps_of_state s)(slot \<mapsto> NullCap))"
  apply (clarsimp simp: cap_cleanup_opt_def cte_wp_at_def post_cap_delete_pre_def
                      split: cap.split_asm if_split_asm
                      elim!: ranE dest!: caps_of_state_cteD)
   (* IRQHandlerCap case *)
   apply (drule(2) final_cap_duplicate_irq)
     apply simp+
   (* IOPort case *)
  apply (clarsimp simp: arch_cap_cleanup_opt_def arch_post_cap_delete_pre_def
                        clearable_ioport_range_def get_cap_caps_of_state
                 elim!: ranE
                 split: arch_cap.split_asm if_split_asm)
  apply (drule_tac s="Some c" for c in sym)
  apply (rule ccontr)
  apply (frule_tac p=slot and cap="ArchObjectCap (IOPortCap x31 x32)" and cap'=cap'
                  in valid_ioportsD; (fastforce simp: ran_def)?)
  apply (case_tac cap'; clarsimp)
  apply (case_tac x12; clarsimp)
  apply (frule_tac p=slot and p'="(a,b)" and cap''=cap and cap'=cap
                         in is_final_cap_caps_of_state_2D; auto simp: gen_obj_refs_def)
  done

lemma rec_del_invs'':
  notes Inr_in_liftE_simp[simp del]
  assumes set_cap_Q[wp]: "\<And>cap p. \<lbrace>Q and invs\<rbrace> set_cap cap p \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes empty_slot_Q[wp]: "\<And>slot free_irq. \<lbrace>Q and invs\<rbrace> empty_slot slot free_irq\<lbrace>\<lambda>_.Q\<rbrace>"
  assumes finalise_cap_Q[wp]: "\<And>cap final. \<lbrace>Q and invs\<rbrace> finalise_cap cap final \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes cap_swap_for_delete_Q[wp]: "\<And>a b. \<lbrace>Q and invs and cte_at a and cte_at b and K (a \<noteq> b)\<rbrace>
                                              cap_swap_for_delete a b
                                             \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes preemption_point_Q: "\<And>cap final. \<lbrace>Q and invs\<rbrace> preemption_point \<lbrace>\<lambda>_.Q\<rbrace>"
  shows
  "s \<turnstile> \<lbrace>Q and invs and valid_rec_del_call call
           and (\<lambda>s. \<not> exposed_rdcall call
                       \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {})
                                (slot_rdcall call) s)
           and emptyable (slot_rdcall call)
           and (\<lambda>s. case call of ReduceZombieCall cap sl ex \<Rightarrow>
                               \<not> cap_removeable cap sl
                               \<and> (\<forall>t\<in>obj_refs cap. halted_if_tcb t s)
                        | _ \<Rightarrow> True)\<rbrace>
         rec_del call
       \<lbrace>\<lambda>rv s. Q s \<and> invs s \<and>
               (case call of FinaliseSlotCall sl x \<Rightarrow>
                             ((fst rv \<or> x) \<longrightarrow> cte_wp_at (replaceable s sl cap.NullCap) sl s)
                             \<and> (snd rv \<noteq> NullCap \<longrightarrow>
                                   post_cap_delete_pre (snd rv) ((caps_of_state s) (sl \<mapsto> cap.NullCap)))
                          | ReduceZombieCall cap sl x \<Rightarrow>
                             (\<not> x \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) sl s)
                          | _ \<Rightarrow> True) \<and>
               emptyable (slot_rdcall call) s\<rbrace>,
       \<lbrace>\<lambda>rv. Q and invs\<rbrace>"
proof (induct rule: rec_del.induct,
       simp_all only: rec_del_fails)
  case (1 slot exposed s)
  show ?case
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply wp
     apply (simp(no_asm))
     apply (wp empty_slot_invs empty_slot_emptyable)[1]
    apply (rule hoare_pre_spec_validE)
     apply (rule spec_strengthen_postE, unfold slot_rdcall.simps)
      apply (rule "1.hyps"[simplified rec_del_call.simps slot_rdcall.simps])
     apply clarsimp
     apply (auto simp: cte_wp_at_caps_of_state)
    done
next
  case (2 slot exposed s)
  show ?case
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply (rule split_spec_bindE[rotated])
     apply (rule drop_spec_validE, simp)
     apply (rule get_cap_sp)
    apply (rule hoare_pre_spec_validE)
     apply (wp replace_cap_invs | simp)+
        apply (erule finalise_cap_not_reply_master)
       apply (wp "2.hyps")
         apply (wp preemption_point_Q | simp)+
         apply (wp preemption_point_inv, simp+)
         apply (wp preemption_point_Q)
         apply ((wp preemption_point_inv irq_state_independent_A_conjI irq_state_independent_AI
                    emptyable_irq_state_independent invs_irq_state_independent
               | simp add: valid_rec_del_call_def irq_state_independent_A_def)+)[1]
        apply (simp(no_asm))
        apply (rule spec_strengthen_postE)
        apply (rule "2.hyps"[simplified rec_del_call.simps slot_rdcall.simps conj_assoc], assumption+)
       apply (simp add: cte_wp_at_eq_simp
                | wp replace_cap_invs set_cap_sets final_cap_same_objrefs
                     set_cap_cte_cap_wp_to hoare_weak_lift_imp
                | erule finalise_cap_not_reply_master)+
       apply (wp hoare_vcg_const_Ball_lift)+
      apply (rule hoare_strengthen_post)
       apply (rule_tac Q="\<lambda>fin s. Q s \<and> invs s \<and> replaceable s slot (fst fin) rv
                                 \<and> cte_wp_at ((=) rv) slot s \<and> s \<turnstile> (fst fin)
                                 \<and> ex_cte_cap_wp_to (appropriate_cte_cap rv) slot s
                                 \<and> emptyable slot s
                                 \<and> (\<forall>t\<in>obj_refs (fst fin). halted_if_tcb t s)"
                  in hoare_vcg_conj_lift)
        apply (wp finalise_cap_invs[where slot=slot]
                  finalise_cap_replaceable[where sl=slot]
                  finalise_cap_makes_halted[where slot=slot])[1]
       apply (rule finalise_cap_cases[where slot=slot])
      apply (clarsimp simp: cte_wp_at_caps_of_state)
      apply (erule disjE)
       apply clarsimp
       apply (rule post_cap_delete_pre_is_final_cap', clarsimp+)
      apply (rule conjI)
       apply clarsimp
       apply (subst replaceable_def)
       apply (clarsimp simp: is_cap_simps tcb_cap_valid_NullCapD
                             no_cap_to_obj_with_diff_ref_Null gen_obj_refs_eq
                        del: disjCI)
       apply (thin_tac "appropriate_cte_cap a = appropriate_cte_cap b" for a b)
       apply (rule conjI)
        apply (clarsimp simp: replaceable_def)
        apply (erule disjE)
         apply (simp only: zobj_refs.simps mem_simps)
        apply clarsimp+
       subgoal
         apply (drule sym, simp)
         apply (drule sym, simp)
         apply clarsimp
         apply (simp add: unat_eq_0)
         apply (drule of_bl_eq_0)
          apply (drule zombie_cte_bits_less, simp add: word_bits_def)
         by (clarsimp simp: cte_wp_at_caps_of_state)
      apply (drule_tac s="appropriate_cte_cap c" for c in sym)
      apply (clarsimp simp: is_cap_simps appropriate_Zombie gen_obj_refs_eq)
     apply (simp add: is_final_cap_def)
     apply wp
    apply (clarsimp simp: cte_wp_at_eq_simp)
    apply (rule conjI)
     apply (clarsimp simp: cte_wp_at_caps_of_state replaceable_def)
    apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp+)
    apply (frule invs_valid_asid_table)
    apply (frule invs_sym_refs)
    apply (clarsimp simp: invs_def valid_state_def
                          invs_valid_objs invs_psp_aligned)
    apply (drule(1) if_unsafe_then_capD, clarsimp+)
    done
next
  have replicate_helper:
    "\<And>x n. True \<in> set x \<Longrightarrow> replicate n False \<noteq> x"
   by (clarsimp simp: replicate_not_True)
  case (3 ptr bits n slot s)
  show ?case
    apply simp
    apply wp+
    apply clarsimp
    apply (rule context_conjI')
     apply (rule context_conjI')
      apply (rule conjI)
       apply (erule zombie_is_cap_toE2)
        apply simp+
      apply (clarsimp simp: halted_emptyable)
      apply (rule conjI, clarsimp simp: cte_wp_at_caps_of_state)
       apply (erule tcb_valid_nonspecial_cap)
         apply fastforce
        apply (clarsimp simp: ran_tcb_cap_cases is_cap_simps
                       split: Structures_A.thread_state.splits)
       apply (clarsimp simp: is_cap_simps)
      apply (rule conjI)
       apply (drule cte_wp_valid_cap, clarsimp)
       apply (frule cte_at_nat_to_cref_zbits [where m=0], simp)
       apply (rule cte_wp_at_not_reply_master)
          apply (simp add: replicate_helper tcb_cnode_index_def)
         apply (subst(asm) nat_to_cref_0_replicate)
          apply (simp add: zombie_cte_bits_less)
         apply assumption
        apply clarsimp
       apply (simp add: invs_def valid_state_def)
      apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
     apply (erule cte_wp_at_weakenE | clarsimp)+
    done
next
  have nat_helper:
    "\<And>x n. \<lbrakk> x < Suc n; x \<noteq> n \<rbrakk> \<Longrightarrow> x < n"
    by (simp add: le_simps)
  case (4 ptr bits n slot s)
  show ?case
    apply simp
    apply (rule hoare_pre_spec_validE)
     apply (wp replace_cap_invs | simp add: is_cap_simps)+
      apply (rule_tac Q'="\<lambda>rv s. Q s \<and> invs s \<and> cte_wp_at (\<lambda>cap. cap = rv) slot s
                             \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap
                                        \<or> \<not> False \<and> is_zombie cap
                                            \<and> (ptr, nat_to_cref (zombie_cte_bits bits) n)
                                                 \<in> fst_cte_ptrs cap)
                                    (ptr, nat_to_cref (zombie_cte_bits bits) n) s
                             \<and> \<not> cap_removeable (cap.Zombie ptr bits (Suc n)) slot"
                  in hoare_post_imp)
       apply (thin_tac "(a, b) \<in> fst c" for a b c)
       apply clarsimp
       apply (frule cte_wp_at_emptyableD, clarsimp, assumption)
       apply (rule conjI[rotated], (clarsimp simp: is_cap_simps)+)
       apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp+)
       apply (frule if_unsafe_then_capD, clarsimp+)
       apply (rule conjI)
        apply (frule zombies_finalD, (clarsimp simp: is_cap_simps)+)
        apply (clarsimp simp: cte_wp_at_caps_of_state)
        apply (erule disjE[where P="val = cap.NullCap" for val])
         apply (clarsimp simp: replaceable_def cap_range_def is_cap_simps
                               gen_obj_refs_subset vs_cap_ref_def)
         apply (rule conjI[rotated])
          apply (rule conjI)
           apply (rule mp [OF tcb_cap_valid_imp'])
           apply (fastforce simp: ran_tcb_cap_cases is_cap_simps
                                 is_pt_cap_def vs_cap_ref_def
                                 valid_ipc_buffer_cap_def
                          split: Structures_A.thread_state.splits)
          apply (drule unique_table_refs_no_cap_asidD)
           apply (simp add: invs_def valid_state_def valid_arch_caps_def)
          apply (simp add: no_cap_to_obj_with_diff_ref_def Ball_def
                           table_cap_ref_def)
         apply clarsimp
         apply (rule ccontr, erule notE, erule nat_helper)
         apply clarsimp
         apply (erule disjE[where Q="val = slot" for val])
          apply (clarsimp simp: cte_wp_at_caps_of_state)
          apply (erule notE[rotated, where P="val = Some cap.NullCap" for val])
          apply (drule sym, simp, subst nat_to_cref_unat_of_bl)
           apply (drule zombie_cte_bits_less, simp add: word_bits_def)
          apply assumption
         apply clarsimp
         apply (drule sym, simp)
         apply (subst(asm) nat_to_cref_unat_of_bl)
          apply (drule zombie_cte_bits_less, simp add: word_bits_conv)
         apply simp
        apply (clarsimp simp: is_final_cap'_def3 simp del: split_paired_All)
        apply (frule_tac x=slot in spec)
        apply (drule_tac x="(ptr, nat_to_cref (zombie_cte_bits bits) n)" in spec)
        apply (clarsimp simp: cte_wp_at_caps_of_state fst_cte_ptrs_def
                              gen_obj_refs_Int)
        apply (drule(1) nat_to_cref_replicate_Zombie[OF sym])
         apply simp
        apply simp
       apply (clarsimp simp: valid_cap_def cap_aligned_def is_cap_simps
                             cte_wp_at_cte_at appropriate_Zombie
                      split: option.split_asm)
      apply (wp get_cap_cte_wp_at)[1]
     apply simp
     apply (subst conj_assoc[symmetric])
     apply (rule spec_valid_conj_liftE2)
      apply (wp rec_del_delete_cases[where ex=False, simplified])[1]
     apply (rule spec_strengthen_postE)
      apply (rule "4.hyps"[simplified rec_del_call.simps slot_rdcall.simps simp_thms pred_conj_def])
      apply (simp add: in_monad)
     apply simp
    apply (clarsimp simp: halted_emptyable)
    apply (erule(1) zombie_is_cap_toE)
     apply simp
    apply simp
    done
qed


lemmas rec_del_invs'[CNodeInv_AI_assms] = rec_del_invs'' [where Q=\<top>,
  simplified hoare_TrueI pred_conj_def simp_thms, OF TrueI TrueI TrueI TrueI, simplified]

end


global_interpretation CNodeInv_AI_2?: CNodeInv_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact CNodeInv_AI_assms)?)
  qed


context Arch begin arch_global_naming

lemma finalise_cap_rvk_prog [CNodeInv_AI_assms]:
   "\<lbrace>\<lambda>s. revoke_progress_ord m (\<lambda>x. map_option cap_to_rpo (caps_of_state s x))\<rbrace>
   finalise_cap a b
   \<lbrace>\<lambda>_ s. revoke_progress_ord m (\<lambda>x. map_option cap_to_rpo (caps_of_state s x))\<rbrace>"
  apply (case_tac a,simp_all add:liftM_def)
    apply (wp suspend_rvk_prog deleting_irq_handler_rvk_prog
      | clarsimp simp:is_final_cap_def comp_def)+
  done


lemma rec_del_rvk_prog [CNodeInv_AI_assms]:
  "st \<turnstile> \<lbrace>\<lambda>s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)
          \<and> (case args of ReduceZombieCall cap sl ex \<Rightarrow>
               cte_wp_at (\<lambda>c. c = cap) sl s \<and> is_final_cap' cap s
             | _ \<Rightarrow> True)\<rbrace>
     rec_del args
   \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
proof (induct rule: rec_del.induct,
       simp_all only: rec_del_fails)
  case (1 slot exposed s)
  note wp = "1.hyps"[simplified rdcall_simps simp_thms]
  show ?case
    apply (subst rec_del.simps)
    apply (simp only: rdcall_simps simp_thms split_def)
    apply wp
     apply (simp(no_asm) del: o_apply)
     apply (wp empty_slot_rvk_prog)[1]
    apply (simp del: o_apply)
    apply (rule wp)
    done
next
  case (2 sl exp s)
  note wp = "2.hyps" [simplified rdcall_simps simp_thms]
  show ?case
    apply (subst rec_del.simps)
    apply (simp only: rdcall_simps simp_thms split_def)
    apply (rule hoare_pre_spec_validE)
     apply wp
         apply ((wp | simp)+)[1]
        apply (wp wp)
          apply ((wp preemption_point_inv | simp)+)[1]
         apply (simp(no_asm))
         apply (rule wp, assumption+)
        apply (wp final_cap_same_objrefs
                  set_cap_cte_wp_at_cases
                   | simp)+
       apply (rule hoare_strengthen_post)
        apply (rule_tac Q="\<lambda>fc s. cte_wp_at ((=) rv) sl s
                              \<and> revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)"
                 in hoare_vcg_conj_lift)
         apply (wp finalise_cap_rvk_prog[folded o_def])[1]
        apply (rule finalise_cap_cases[where slot=sl])
       apply (clarsimp simp: o_def)
       apply (strengthen rvk_prog_update_strg[unfolded fun_upd_def o_def])
       apply (clarsimp simp: cte_wp_at_caps_of_state)
       apply (erule disjE)
        apply clarsimp
       apply (clarsimp simp: is_cap_simps)
       apply (case_tac "is_zombie rv")
        apply (clarsimp simp: cap_to_rpo_def is_cap_simps fst_cte_ptrs_def)
        apply (simp add: is_final_cap'_def)
       apply (case_tac rv, simp_all add: cap_to_rpo_def is_cap_simps gen_obj_refs_eq)[1]
       apply (rename_tac arch_cap)
       apply (case_tac arch_cap, simp_all)[1]
      apply (simp add: is_final_cap_def, wp)
     apply (simp, wp get_cap_wp)
    apply (clarsimp simp: o_def)
    done
next
  case (3 ptr bits n slot s)
  show ?case
    apply simp
    apply (fold o_def)
    apply (rule hoare_pre_spec_validE)
     apply (simp del: o_apply | wp (once) cap_swap_fd_rvk_prog)+
    apply (clarsimp simp: cte_wp_at_caps_of_state cap_to_rpo_def)
    done
next
  case (4 ptr zb znum sl s)
  note wp = "4.hyps"[simplified rdcall_simps]
  show ?case
    apply (subst rec_del.simps)
    apply wp
        apply (wp | simp)+
      apply (wp get_cap_wp)[1]
     apply (rule spec_strengthen_postE)
      apply (rule wp, assumption+)
     apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_defs)
     apply (strengthen rvk_prog_update_strg[unfolded fun_upd_def o_def])
     apply (clarsimp simp: cte_wp_at_caps_of_state cap_to_rpo_def)
    apply (wp | simp add: o_def)+
    done
qed

end


global_interpretation CNodeInv_AI_3?: CNodeInv_AI_3
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact CNodeInv_AI_assms)?)
  qed


termination cap_revoke by (rule cap_revoke_termination)

declare cap_revoke.simps[simp del]


context Arch begin arch_global_naming

crunch finalise_slot
  for typ_at[wp, CNodeInv_AI_assms]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps filterM_mapM unless_def
   ignore: without_preemption filterM set_object clearMemory)


lemma weak_derived_appropriate [CNodeInv_AI_assms]:
  "weak_derived cap cap' \<Longrightarrow> appropriate_cte_cap cap = appropriate_cte_cap cap'"
  by (auto simp: weak_derived_def copy_of_def same_object_as_def2
                 appropriate_cte_master
          split: if_split_asm
          dest!: arg_cong[where f=appropriate_cte_cap])

end


global_interpretation CNodeInv_AI_4?: CNodeInv_AI_4
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact CNodeInv_AI_assms)?)
  qed


context Arch begin arch_global_naming

lemma cap_move_ioports:
  "\<lbrace>valid_ioports and cte_wp_at ((=) cap.NullCap) ptr'
         and cte_wp_at (weak_derived cap) ptr
         and cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) ptr and K (ptr \<noteq> ptr')\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  apply (simp add: valid_ioports_def all_ioports_issued_def ioports_no_overlap_def issued_ioports_def)
  apply (rule hoare_pre)
   apply (wp hoare_use_eq [where f=arch_state,
                           OF cap_move_arch cap_move_caps_of_state])
  apply (clarsimp simp: cte_wp_at_caps_of_state
                 elim!: ranE split: if_split_asm
                 dest!: weak_derived_cap_ioports)
  by (fastforce elim!: ranE split: if_split_asm)

lemma cap_move_ioport_control[wp]:
  "\<lbrace>ioport_control_unique and cte_wp_at (weak_derived cap) ptr\<rbrace>
   cap_move cap ptr ptr'
   \<lbrace>\<lambda>_. ioport_control_unique\<rbrace>"
  apply (wpsimp wp: cap_move_caps_of_state simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp: ioport_control_unique_def)
  apply (cases ptr)
  apply (rule conjI; clarsimp)
  done

lemma cap_move_valid_arch:
  "\<lbrace>valid_arch_state and cte_wp_at ((=) cap.NullCap) ptr'
    and cte_wp_at (weak_derived cap) ptr
    and cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) ptr and K (ptr \<noteq> ptr')\<rbrace>
   cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (wp valid_arch_state_lift_ioports_typ_at cap_move_ioports cap_move_typ_at)
     (simp add: valid_arch_state_def)

lemma cap_move_invs[wp, CNodeInv_AI_assms]:
  "\<lbrace>invs and valid_cap cap and cte_wp_at ((=) cap.NullCap) ptr'
         and tcb_cap_valid cap ptr'
         and cte_wp_at (weak_derived cap) ptr
         and cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) ptr
         and ex_cte_cap_wp_to (appropriate_cte_cap cap) ptr' and K (ptr \<noteq> ptr')
         and K (\<not> is_master_reply_cap cap)\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  apply (simp add: pred_conj_def conj_comms [where Q = "valid_mdb S" for S])
  apply wp
   apply (wpe cap_move_zombies_final)
   apply (wpe cap_move_if_live)
   apply (wpe cap_move_if_unsafe)
   apply (wpe cap_move_irq_handlers)
   apply (wpe cap_move_replies)
   apply (wpe cap_move_valid_arch_caps)
   apply (wpe cap_move_valid_ioc)
   apply (wpe cap_move_valid_arch)
   apply (simp add: cap_move_def set_cdt_def)
   apply (rule hoare_pre)
    apply (wp set_cap_valid_objs set_cap_idle set_cap_typ_at
              cap_table_at_lift_irq tcb_at_typ_at
              hoare_vcg_disj_lift hoare_vcg_all_lift
              set_cap_cap_refs_respects_device_region_NullCap
            | wp set_cap_cap_refs_respects_device_region_spec[where ptr=ptr]
            | simp del: split_paired_Ex split_paired_All
            | simp add: valid_irq_node_def valid_machine_state_def
                   del: split_paired_All split_paired_Ex)+
   apply (clarsimp simp: tcb_cap_valid_def cte_wp_at_caps_of_state)
   apply (frule(1) valid_global_refsD2[where ptr=ptr])
   apply (frule(1) cap_refs_in_kernel_windowD[where ptr=ptr])
   apply (frule weak_derived_cap_range)
   apply (frule weak_derived_is_reply_master)
   apply (simp add: cap_range_NullCap valid_ipc_buffer_cap_def[where c=cap.NullCap])
   apply (simp add: is_cap_simps)
   apply (subgoal_tac "tcb_cap_valid cap.NullCap ptr s")
    apply (simp add: tcb_cap_valid_def weak_derived_cap_is_device is_cap_simps)
   apply (rule tcb_cap_valid_NullCapD)
    apply (erule(1) tcb_cap_valid_caps_of_stateD)
   apply (simp add: is_cap_simps)
   done

lemma arch_derive_is_arch:
  "\<lbrace>\<top>\<rbrace> arch_derive_cap c \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> is_arch_cap rv\<rbrace>,-"
  by (wpsimp simp: is_arch_cap_def arch_derive_cap_def)

end


global_interpretation CNodeInv_AI_5?: CNodeInv_AI_5
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact CNodeInv_AI_assms)?)
  qed


end
