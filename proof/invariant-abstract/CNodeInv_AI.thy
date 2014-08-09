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
Results about CNode Invocations, particularly the
recursive revoke and delete operations.
*)

theory CNodeInv_AI
imports Ipc_AI
begin

primrec
  valid_cnode_inv :: "Invocations_A.cnode_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_cnode_inv (InsertCall cap ptr ptr') =
   (valid_cap cap and real_cte_at ptr and real_cte_at ptr' and
    (\<lambda>s. cte_wp_at (is_derived (cdt s) ptr cap) ptr s) and
    cte_wp_at (\<lambda>c. c = cap.NullCap) ptr' and
    ex_cte_cap_wp_to is_cnode_cap ptr' and K (ptr \<noteq> ptr') and
    (\<lambda>s. \<forall>r\<in>obj_refs cap. \<forall>p'.
           ptr' \<noteq> p' \<and> cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') p' s \<longrightarrow>
           cte_wp_at (Not \<circ> is_zombie) p' s \<and> \<not> is_zombie cap))"
| "valid_cnode_inv (MoveCall cap ptr ptr') =
   (valid_cap cap and cte_wp_at (op = cap.NullCap) ptr' and
    cte_wp_at (op \<noteq> cap.NullCap) ptr and cte_wp_at (weak_derived cap) ptr and
    cte_wp_at (\<lambda>c. is_untyped_cap c \<longrightarrow> c = cap) ptr and 
    ex_cte_cap_wp_to is_cnode_cap ptr' and
    real_cte_at ptr and real_cte_at ptr')"
| "valid_cnode_inv (RevokeCall ptr) = cte_at ptr"
| "valid_cnode_inv (DeleteCall ptr) = real_cte_at ptr"
| "valid_cnode_inv (RotateCall s_cap p_cap src pivot dest) =
   (valid_cap s_cap and valid_cap p_cap and
    real_cte_at src and real_cte_at dest and real_cte_at pivot and
    cte_wp_at (weak_derived s_cap) src and
    cte_wp_at (\<lambda>c. is_untyped_cap c \<longrightarrow> c = s_cap) src and 
    cte_wp_at (op \<noteq> cap.NullCap) src and
    cte_wp_at (weak_derived p_cap) pivot and
    cte_wp_at (\<lambda>c. is_untyped_cap c \<longrightarrow> c = p_cap) pivot and 
    cte_wp_at (op \<noteq> cap.NullCap) pivot and K (src \<noteq> pivot \<and> pivot \<noteq> dest) and
    (\<lambda>s. src \<noteq> dest \<longrightarrow> cte_wp_at (\<lambda>c. c = cap.NullCap) dest s) and 
    ex_cte_cap_wp_to is_cnode_cap pivot and ex_cte_cap_wp_to is_cnode_cap dest)"
| "valid_cnode_inv (SaveCall ptr) =
   (ex_cte_cap_wp_to is_cnode_cap ptr and
    cte_wp_at (\<lambda>c. c = cap.NullCap) ptr and real_cte_at ptr)"
| "valid_cnode_inv (RecycleCall ptr) =
   (cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) ptr and real_cte_at ptr)"


lemma mask_cap_all:
  "mask_cap (all_rights \<inter> r) c = mask_cap r c"
  unfolding all_rights_def by simp


lemma decode_cnode_cases2:
  assumes mvins: "\<And>index bits src_index src_depth args' src_root_cap exs'.
                    \<lbrakk> args = index # bits # src_index # src_depth # args';
                      exs = src_root_cap # exs';
                      invocation_type label \<in> set [CNodeCopy .e. CNodeMutate];
                      invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller];
                      invocation_type label \<notin> {CNodeRevoke, CNodeDelete,
                      CNodeRecycle, CNodeRotate, CNodeSaveCaller} \<rbrakk> \<Longrightarrow> P"
  assumes rvk: "\<And>index bits args'. \<lbrakk> args = index # bits # args';
                          invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate];
                          invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller];
                          invocation_type label = CNodeRevoke \<rbrakk> \<Longrightarrow> P"
  assumes dlt: "\<And>index bits args'. \<lbrakk> args = index # bits # args';
                          invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate];
                          invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller];
                          invocation_type label = CNodeDelete \<rbrakk> \<Longrightarrow> P"
  assumes svc: "\<And>index bits args'. \<lbrakk> args = index # bits # args';
                          invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate];
                          invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller];
                          invocation_type label = CNodeSaveCaller \<rbrakk> \<Longrightarrow> P"
  assumes rcy: "\<And>index bits args'. \<lbrakk> args = index # bits # args';
                          invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate];
                          invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller];
                          invocation_type label = CNodeRecycle \<rbrakk> \<Longrightarrow> P"
  assumes rot: "\<And>index bits pivot_new_data pivot_index pivot_depth src_new_data
                  src_index src_depth args' pivot_root_cap src_root_cap exs'.
                     \<lbrakk> args = index # bits # pivot_new_data # pivot_index # pivot_depth
                                 # src_new_data # src_index # src_depth # args';
                       exs = pivot_root_cap # src_root_cap # exs';
                       invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate];
                       invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller];
                       invocation_type label = CNodeRotate \<rbrakk> \<Longrightarrow> P"
  assumes errs:
      "\<lbrakk> invocation_type label \<notin> set [CNodeRevoke .e. CNodeSaveCaller] \<or>
         args = [] \<or> (\<exists>x. args = [x]) \<or> (\<exists>index bits args'. args = index # bits # args' \<and>
                             invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller] \<and>
                             (invocation_type label \<in> set [CNodeCopy .e. CNodeMutate]
                                        \<and> invocation_type label \<notin> {CNodeRevoke, CNodeDelete,
                                             CNodeRecycle, CNodeRotate, CNodeSaveCaller}
                                        \<and> (case (args', exs) of (src_index # src_depth # args'',
                                                    src_root_cap # exs') \<Rightarrow> False | _ \<Rightarrow> True) \<or>
                              invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate] \<and>
                              invocation_type label = CNodeRotate \<and> (case (args', exs) of
                              (pivot_new_data # pivot_index # pivot_depth
                                 # src_new_data # src_index # src_depth # args'',
                               pivot_root_cap # src_root_cap # exs') \<Rightarrow> False
                                         | _ \<Rightarrow> True))) \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  have simps: "[CNodeRevoke .e. CNodeSaveCaller]
                     = [CNodeRevoke, CNodeDelete, CNodeRecycle, CNodeCopy, CNodeMint,
                        CNodeMove, CNodeMutate, CNodeRotate, CNodeSaveCaller]"
              "[CNodeCopy .e. CNodeMutate] = [CNodeCopy, CNodeMint,
                        CNodeMove, CNodeMutate]"
    by (simp_all add: upto_enum_def fromEnum_def toEnum_def enum_invocation_label)
  show ?thesis
    apply (cases args)
     apply (simp add: errs)
    apply (case_tac list)
     apply (simp add: errs)
    apply (case_tac "invocation_type label \<in> set [CNodeCopy .e. CNodeMutate]")
     apply (case_tac "case (lista, exs) of (src_index # src_depth # args'',
                             src_root_cap # exs'') \<Rightarrow> False | _ \<Rightarrow> True")
      apply (rule errs)
      apply (simp add: simps)
      apply (rule disjI2)
      apply auto[1]
     apply (simp split: prod.split_asm list.split_asm)
     apply (erule(2) mvins, auto simp: simps)[1]
    apply (case_tac "invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller]")
     apply (simp_all add: errs)
    apply (insert rvk dlt svc rcy rot)
    apply (simp add: simps)
    apply atomize
    apply (elim disjE, simp_all)
    apply (case_tac "case (lista, exs) of
                         (pivot_new_data # pivot_index # pivot_depth
                             # src_new_data # src_index # src_depth # args'',
                          pivot_root_cap # src_root_cap # exs') \<Rightarrow> False
                                         | _ \<Rightarrow> True")
     apply (rule errs)
     apply (simp add: simps)
    apply (simp split: prod.split_asm list.split_asm)
  done
qed

lemma valid_cnode_capI:
  "\<lbrakk>cap_table_at n w s; valid_objs s; pspace_aligned s; n > 0; length g \<le> 32\<rbrakk>
   \<Longrightarrow> s \<turnstile> cap.CNodeCap w n g"
  apply (simp add: valid_cap_def cap_aligned_def)
  apply (rule conjI)
   apply (clarsimp simp add: pspace_aligned_def obj_at_def)
   apply (drule bspec, fastforce)
   apply (clarsimp simp: is_obj_defs wf_obj_bits cte_level_bits_def)
  apply (clarsimp simp add: obj_at_def is_obj_defs valid_objs_def dom_def)
  apply (erule allE, erule impE, blast)
  apply (simp add: valid_obj_def valid_cs_def valid_cs_size_def)
  apply (simp add: cte_level_bits_def word_bits_def)
  done


lemma Suc_length_not_empty: 
  "length xs = length xs' \<Longrightarrow> Suc 0 \<le> length xs' = (xs \<noteq> [])"
  by (fastforce simp: le_simps)


lemma update_cap_hoare_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. valid_cap (C rv s) s\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. valid_cap (update_cap_data prs n (C rv s)) s\<rbrace>"
  apply (erule hoare_strengthen_post)
  apply (erule update_cap_data_validI)
  done


lemma mask_cap_hoare_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. valid_cap (C rv s) s\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. valid_cap (mask_cap (M rv s) (C rv s)) s\<rbrace>"
  by (fastforce simp add: valid_def mask_cap_valid)


lemma derive_cap_objrefs:
  "\<lbrace>\<lambda>s. P (obj_refs cap)\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> P (obj_refs rv)\<rbrace>,-"
  apply (cases cap, simp_all add: derive_cap_def is_zombie_def)
          apply ((wp ensure_no_children_inv | simp add: o_def | rule hoare_pre)+)[11]
  apply (case_tac arch_cap, simp_all add: arch_derive_cap_def)
      apply (wp | simp add: o_def)+
   apply (case_tac option)
    apply simp
    apply (rule hoare_pre, wp)
   apply simp
   apply (rule hoare_pre, wp)
   apply (simp add: aobj_ref_cases)
  apply (case_tac option, simp)
   apply (rule hoare_pre, wp)
  apply simp
  apply (rule hoare_pre, wp)
  apply clarsimp
  done


lemma derive_cap_untyped:
  "\<lbrace>\<lambda>s. P (untyped_range cap)\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> P (untyped_range rv)\<rbrace>,-"
  apply (cases cap, simp_all add: derive_cap_def is_zombie_def)
          apply (wp ensure_no_children_inv | simp add: o_def | rule hoare_pre)+
  done


lemma derive_cap_zobjrefs:
  "\<lbrace>\<lambda>s. P (zobj_refs cap)\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> P (zobj_refs rv)\<rbrace>,-"
  apply (cases cap, simp_all add: derive_cap_def is_zombie_def)
          apply ((wp ensure_no_children_inv | simp add: o_def | rule hoare_pre)+)[11]
  apply (case_tac arch_cap, simp_all add: arch_derive_cap_def)
      apply (wp | simp add: o_def)+
   apply (case_tac option)
    apply simp
    apply (rule hoare_pre, wp)
   apply simp
   apply (rule hoare_pre, wp)
   apply (simp add: aobj_ref_cases)
  apply (case_tac option, simp)
   apply (rule hoare_pre, wp)
  apply simp
  apply (rule hoare_pre, wp)
  apply clarsimp
  done


lemma update_cap_objrefs:
  "\<lbrakk> update_cap_data P dt cap \<noteq> cap.NullCap \<rbrakk> \<Longrightarrow>
     obj_refs (update_cap_data P dt cap) = obj_refs cap"
  apply (case_tac cap,
      simp_all add: update_cap_data_closedform
             split: split_if_asm)
  apply (case_tac arch_cap, simp_all add: aobj_ref_cases arch_update_cap_data_def)
  done


lemma update_cap_zobjrefs:
  "\<lbrakk> update_cap_data P dt cap \<noteq> cap.NullCap \<rbrakk> \<Longrightarrow>
     zobj_refs (update_cap_data P dt cap) = zobj_refs cap"
  apply (case_tac cap,
      simp_all add: update_cap_data_closedform arch_update_cap_data_def
             split: split_if_asm)
  done

lemma zombies_final_helper:
  "\<lbrakk> cte_wp_at (\<lambda>c. c = cap) p s; \<not> is_zombie cap; zombies_final s \<rbrakk>
     \<Longrightarrow> (\<forall>r\<in>obj_refs cap. \<forall>a b.
            cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') (a, b) s \<longrightarrow> cte_wp_at (Not \<circ> is_zombie) (a, b) s)"
  apply (clarsimp simp: cte_wp_at_def)
  apply (case_tac "p = (a, b)")
   apply simp
  apply (drule(2) zombies_finalD2)
    apply clarsimp
   apply blast
  apply simp
  done

lemma copy_mask [simp]:
  "copy_of (mask_cap R c) = copy_of c"
  apply (rule ext)
  apply (auto simp: copy_of_def is_cap_simps mask_cap_def 
                    cap_rights_update_def same_object_as_def 
                    bits_of_def acap_rights_update_def
         split: cap.splits arch_cap.splits)
  done


lemma update_cap_data_mask_Null [simp]:
  "(update_cap_data P x (mask_cap m c) = cap.NullCap) = (update_cap_data P x c = cap.NullCap)"
  unfolding update_cap_data_def mask_cap_def
  apply (cases c)
  apply (auto simp add: the_cnode_cap_def Let_def is_cap_simps cap_rights_update_def badge_update_def)
  done


lemma cap_master_update_cap_data:
  "\<lbrakk> update_cap_data P x c \<noteq> cap.NullCap \<rbrakk>
        \<Longrightarrow> cap_master_cap (update_cap_data P x c) = cap_master_cap c"
  apply (simp add: update_cap_data_def split del: split_if split: split_if_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done


lemma same_object_as_def2:
  "same_object_as cp cp' = (cap_master_cap cp = cap_master_cap cp'
                                \<and> \<not> cp = cap.NullCap \<and> \<not> is_untyped_cap cp
                                \<and> \<not> is_zombie cp
                                \<and> (is_arch_cap cp \<longrightarrow>
                                     (case the_arch_cap cp of arch_cap.PageCap x rs sz v
                                              \<Rightarrow> x \<le> x + 2 ^ pageBitsForSize sz - 1
                                          | _ \<Rightarrow> True)))"
  apply (simp add: same_object_as_def is_cap_simps split: cap.split)
  apply (auto simp: cap_master_cap_def bits_of_def
             split: arch_cap.split_asm)
  apply (auto split: arch_cap.split)
  done


lemma same_object_as_cap_master:
  "same_object_as cap cap' \<Longrightarrow> cap_master_cap cap = cap_master_cap cap'"
  by (simp add: same_object_as_def2)


lemma cap_asid_update_cap_data:
  "\<lbrakk>(update_cap_data P x c) \<noteq> cap.NullCap \<rbrakk>
         \<Longrightarrow> cap_asid (update_cap_data P x c) = cap_asid c"
  apply (simp add: update_cap_data_def split del: split_if split: split_if_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done


lemma cap_vptr_update_cap_data:
  "\<lbrakk>(update_cap_data P x c) \<noteq> cap.NullCap \<rbrakk>
         \<Longrightarrow> cap_vptr (update_cap_data P x c) = cap_vptr c"
  apply (simp add: update_cap_data_def split del: split_if split: split_if_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done


lemma cap_asid_base_update_cap_data:
  "\<lbrakk>(update_cap_data P x c) \<noteq> cap.NullCap \<rbrakk>
         \<Longrightarrow> cap_asid_base (update_cap_data P x c) = cap_asid_base c"
  apply (simp add: update_cap_data_def split del: split_if split: split_if_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done


lemma same_object_as_update_cap_data:
  "\<lbrakk> update_cap_data P x c \<noteq> cap.NullCap; same_object_as c' c \<rbrakk> \<Longrightarrow> 
  same_object_as c' (update_cap_data P x c)"
  apply (clarsimp simp: same_object_as_def is_cap_simps 
                  split: cap.split_asm arch_cap.splits split_if_asm)
  apply (simp add: update_cap_data_def badge_update_def cap_rights_update_def is_cap_simps arch_update_cap_data_def
                   Let_def split_def the_cnode_cap_def bits_of_def split: split_if_asm cap.splits)+
  done


lemma weak_derived_update_cap_data:
  "\<lbrakk>(update_cap_data P x c) \<noteq> cap.NullCap; weak_derived c c'\<rbrakk> 
  \<Longrightarrow> weak_derived (update_cap_data P x c) c'" 
  apply (simp add: weak_derived_def copy_of_def 
                   cap_master_update_cap_data cap_asid_update_cap_data 
                   cap_asid_base_update_cap_data
                   cap_vptr_update_cap_data
              split del: split_if cong: if_cong)  
  apply (erule disjE)
   apply (clarsimp split: split_if_asm)
   apply (erule disjE)
    apply (clarsimp simp: is_cap_simps)
    apply (simp add: update_cap_data_def arch_update_cap_data_def is_cap_simps)
   apply (erule disjE)
    apply (clarsimp simp: is_cap_simps)
    apply (simp add: update_cap_data_def arch_update_cap_data_def is_cap_simps)
   apply (clarsimp simp: is_cap_simps)
   apply (simp add: update_cap_data_def arch_update_cap_data_def is_cap_simps)
   apply (erule (1) same_object_as_update_cap_data)
  apply clarsimp
  apply (rule conjI, clarsimp simp: is_cap_simps update_cap_data_def split del: split_if)+
  apply clarsimp
  apply (clarsimp simp: same_object_as_def is_cap_simps 
                  split: cap.split_asm arch_cap.splits split_if_asm)
  apply (simp add: update_cap_data_def badge_update_def cap_rights_update_def is_cap_simps arch_update_cap_data_def
                   Let_def split_def the_cnode_cap_def bits_of_def split: split_if_asm cap.splits)+
  done


lemma cap_badge_update_cap_data:
  "update_cap_data False x c \<noteq> cap.NullCap \<and> (bdg, cap_badge c) \<in> capBadge_ordering False
       \<longrightarrow> (bdg, cap_badge (update_cap_data False x c)) \<in> capBadge_ordering False"
  apply clarsimp
  apply (erule capBadge_ordering_trans)
  apply (simp add: update_cap_data_def split del: split_if split: split_if_asm)
  apply (auto simp: is_cap_simps Let_def the_cnode_cap_def cap_master_cap_def
                    badge_update_def arch_update_cap_data_def
             split: arch_cap.split)
  done


lemma cap_asid_mask[simp]:
  "cap_asid (mask_cap m c) = cap_asid c"
  by (simp add: mask_cap_def)


lemma cap_vptr_rights_update[simp]:
  "cap_vptr (cap_rights_update f c) = cap_vptr c"
  by (simp add: cap_vptr_def cap_rights_update_def acap_rights_update_def 
           split: cap.splits arch_cap.splits)


lemma cap_vptr_mask[simp]:
  "cap_vptr (mask_cap m c) = cap_vptr c"
  by (simp add: mask_cap_def)


lemma cap_asid_base_rights [simp]:
  "cap_asid_base (cap_rights_update R c) = cap_asid_base c"
  by (simp add: cap_rights_update_def acap_rights_update_def 
           split: cap.splits arch_cap.splits)


lemma cap_asid_base_mask[simp]:
  "cap_asid_base (mask_cap m c) = cap_asid_base c"
  by (simp add: mask_cap_def)


lemma weak_derived_mask:
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


lemma cap_master_mask[simp]:
  "cap_master_cap (mask_cap rs cap) = cap_master_cap cap"
  by (simp add: mask_cap_def)


lemma cap_badge_mask[simp]:
  "cap_badge (mask_cap rs cap) = cap_badge cap"
  by (simp add: mask_cap_def)


lemma ensure_empty_cte_wp_at:
  "\<lbrace>\<top>\<rbrace> ensure_empty c \<lbrace>\<lambda>rv s. cte_wp_at (op = cap.NullCap) c s\<rbrace>, -"
  unfolding ensure_empty_def
  apply (wp whenE_throwError_wp get_cap_wp)
  apply simp
  done


lemmas get_cap_cte_caps_to_no_wp[wp]
    = get_cap_cte_caps_to[where P="\<top>", simplified]


lemma lookup_cap_ex[wp]:
  "\<lbrace>\<top>\<rbrace> lookup_cap t c \<lbrace>\<lambda>rv s. \<forall>r\<in>cte_refs rv (interrupt_irq_node s). ex_cte_cap_to r s\<rbrace>, -"
  by (simp add: split_def lookup_cap_def) wp


lemma cap_aligned_valid[elim!]:
  "s \<turnstile> cap \<Longrightarrow> cap_aligned cap"
  by (simp add: valid_cap_def)


lemma vs_cap_ref_update_cap_data[simp]:
  "vs_cap_ref (update_cap_data P d cap) = vs_cap_ref cap"
  by (simp add: vs_cap_ref_def update_cap_data_closedform
                arch_update_cap_data_def
         split: cap.split)


lemma cap_derive_not_null_helper2:
  "\<lbrace>P\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> Q rv s\<rbrace>, -
      \<Longrightarrow>
   \<lbrace>\<lambda>s. cap \<noteq> cap.NullCap \<and> \<not> is_zombie cap \<and> cap \<noteq> cap.IRQControlCap \<longrightarrow> P s\<rbrace>
     derive_cap slot cap
   \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> Q rv s\<rbrace>, -"
  apply (drule cap_derive_not_null_helper)
  apply (erule hoare_post_imp_R)
  apply simp
  done

lemma has_recycle_rights_not_Null:
  "has_recycle_rights cap \<Longrightarrow> cap \<noteq> cap.NullCap"
  by (clarsimp simp: has_recycle_rights_def)

lemma decode_cnode_inv_wf[wp]:
  "\<lbrace>invs and valid_cap cap
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
         and (\<lambda>s. is_cnode_cap cap \<longrightarrow> (\<forall>r\<in>cte_refs cap (interrupt_irq_node s).
                                           ex_cte_cap_wp_to is_cnode_cap r s))
         and (\<lambda>s. \<forall>cap \<in> set cs. s \<turnstile> cap)
         and (\<lambda>s. \<forall>cap \<in> set cs. is_cnode_cap cap \<longrightarrow>
                  (\<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s)) \<rbrace>
     decode_cnode_invocation mi args cap cs \<lbrace>valid_cnode_inv\<rbrace>,-"
  apply (rule decode_cnode_cases2[where args=args and exs=cs and label=mi])
         -- "Move/Insert"
        apply (simp add: decode_cnode_invocation_def unlessE_whenE
                     split del: split_if)
        apply (wp lsfco_cte_at ensure_no_children_wp whenE_throwError_wp
          | simp add: split_beta split del: split_if
          | (fold validE_R_def)[1])+
              apply (rule cap_derive_not_null_helper2)
              apply (simp only: imp_conjR)
              apply ((wp derive_cap_is_derived
                         derive_cap_valid_cap
                         derive_cap_zobjrefs derive_cap_objrefs_iszombie
                           | wp_once hoare_drop_imps)+ )[1]
             apply (wp whenE_throwError_wp | wpcw)+
           apply simp
           apply (rule_tac Q="\<lambda>src_cap. valid_cap src_cap and ex_cte_cap_wp_to is_cnode_cap x
                                      and zombies_final and valid_objs
                                      and real_cte_at src_slot and real_cte_at x
                                      and cte_wp_at (\<lambda>c. c = src_cap) src_slot
                                      and cte_wp_at (op = cap.NullCap) x"
                      in hoare_post_imp)
            apply (clarsimp simp: cte_wp_at_caps_of_state all_rights_def)
            apply (simp add: cap_master_update_cap_data weak_derived_update_cap_data
                             cap_asid_update_cap_data
                             update_cap_data_validI update_cap_objrefs)
            apply (strengthen cap_badge_update_cap_data)
            apply simp
            apply (frule (1) caps_of_state_valid_cap)
            apply (case_tac "is_zombie r")
             apply (clarsimp simp add: valid_cap_def2 update_cap_data_def
                                       is_cap_simps
                             split: split_if_asm)
            apply (frule(2) zombies_final_helper [OF caps_of_state_cteD[simplified cte_wp_at_eq_simp]])
            apply (clarsimp simp: valid_cap_def2 cte_wp_at_caps_of_state)
            apply (rule conjI, clarsimp+)+
            apply (auto simp add: update_cap_data_def arch_update_cap_data_def
                       is_cap_simps Let_def the_cnode_cap_def weak_derived_def
                       copy_of_def same_object_as_def bits_of_def
                     split: split_if_asm)[1]
           apply (wp get_cap_cte_wp_at ensure_empty_cte_wp_at)
        apply simp
        apply (fold validE_R_def)
        apply (rule hoare_pre)
         apply (wp lookup_slot_for_cnode_op_cap_to)
        apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
       -- "Revoke"
       apply (simp add: decode_cnode_invocation_def unlessE_whenE cong: if_cong)
       apply (wp lsfco_cte_at hoare_drop_imps whenE_throwError_wp
                  | simp add: split_beta validE_R_def[symmetric])+
       apply clarsimp
      -- "Delete"
      apply (simp add: decode_cnode_invocation_def unlessE_whenE cong: if_cong)
      apply (wp lsfco_cte_at hoare_drop_imps whenE_throwError_wp
                 | simp add: split_beta validE_R_def[symmetric])+
      apply clarsimp
     -- "Save"
     apply (simp add: decode_cnode_invocation_def unlessE_whenE cong: if_cong)
     apply (rule hoare_pre)
      apply (wp ensure_empty_stronger whenE_throwError_wp
                lsfco_cte_at lookup_slot_for_cnode_op_cap_to
                hoare_vcg_const_imp_lift
                | simp add: split_beta
                | wp_once hoare_drop_imps)+
     apply clarsimp
    -- "Recycle"
    apply (simp add: decode_cnode_invocation_def
                     unlessE_def whenE_def
               split del: split_if)
    apply (wp get_cap_wp | simp add: split_beta)+
    apply (simp add: cte_wp_at_caps_of_state has_recycle_rights_not_Null)
    apply (rule hoare_pre, wp hoare_vcg_all_lift_R hoare_drop_imps)
    apply clarsimp
   -- "Rotate"
   apply (simp add: decode_cnode_invocation_def split_def
                    whenE_def unlessE_def)
   apply (rule hoare_pre)
    apply (wp get_cap_wp ensure_empty_stronger | simp)+
      apply (rule_tac Q'="\<lambda>rv s. real_cte_at rv s \<and> real_cte_at x s
                              \<and> real_cte_at src_slot s
                              \<and> ex_cte_cap_wp_to is_cnode_cap rv s
                              \<and> ex_cte_cap_wp_to is_cnode_cap x s
                              \<and> invs s" in hoare_post_imp_R)
       apply wp
      apply (clarsimp simp: cte_wp_at_caps_of_state
                     dest!: real_cte_at_cte del: impI)
      apply (frule invs_valid_objs)
      apply (simp add: update_cap_data_validI weak_derived_update_cap_data
                       caps_of_state_valid_cap)
      apply (auto,(clarsimp simp:is_cap_simps update_cap_data_def)+)[1](* Bad practise *)
     apply wp
   apply clarsimp
  apply (elim disjE exE conjE,
         simp_all add: decode_cnode_invocation_def validE_R_def
                       split_def unlessE_whenE
                split: list.split_asm
            split del: split_if)
  apply (wp | simp)+
  done

lemma decode_cnode_inv_inv[wp]:
  "\<lbrace>P\<rbrace> decode_cnode_invocation mi args cap cs \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding decode_cnode_invocation_def
  apply (simp add: split_def unlessE_def whenE_def
             cong: if_cong split del: split_if)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | simp | wpcw)+
  done

lemma in_preempt[simp,intro]:
  "(Inr rv, s') \<in> fst (preemption_point s) \<Longrightarrow>
  (\<exists>f es. s' = s \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr>, exst := es\<rparr>)"  
  apply (clarsimp simp: preemption_point_def in_monad do_machine_op_def 
                        return_def returnOk_def throwError_def o_def
                        select_f_def select_def getActiveIRQ_def) 
  done

definition
  not_recursive_cspaces :: "'z::state_ext state \<Rightarrow> cslot_ptr set"
where
 "not_recursive_cspaces s \<equiv> {ptr. cte_wp_at (\<lambda>cap. ptr \<notin> fst_cte_ptrs cap) ptr s}"

definition
  state_cte_ptrs :: "'z::state_ext state \<Rightarrow> cslot_ptr set"
where
 "state_cte_ptrs s \<equiv> {ptr. cte_at ptr s}"

lemma fixed_length_finite:
  "finite (UNIV :: 'a set) \<Longrightarrow> finite {x :: 'a list. length x = n}"
  apply (induct n)
   apply simp
  apply (subgoal_tac "{x :: 'a list. length x = Suc n} = image (split Cons) (UNIV \<times> {x. length x = n})")
   apply clarsimp
  apply safe
   apply (case_tac x, simp_all add: image_def)
  done

lemma state_cte_ptrs_finite:
  "finite (state_cte_ptrs s)"
  apply (clarsimp simp add: state_cte_ptrs_def cte_at_cases Collect_disj_eq
                            Collect_conj_eq set_pair_UN tcb_cap_cases_def)
  apply (clarsimp simp: well_formed_cnode_n_def fixed_length_finite)
  done

lemma cte_wp_at_set_finite:
  "finite {p. cte_wp_at (P p) p s}"
  apply (rule finite_subset [OF _ state_cte_ptrs_finite[where s=s]])
  apply (clarsimp simp: state_cte_ptrs_def elim!: cte_wp_at_weakenE)
  done


lemma not_recursive_cspaces_finite:
  "finite (not_recursive_cspaces s)"
  unfolding not_recursive_cspaces_def
  by (rule cte_wp_at_set_finite)


lemma set_cdt_not_recursive[wp]:
  "\<lbrace>\<lambda>s. P (not_recursive_cspaces s)\<rbrace> set_cdt f \<lbrace>\<lambda>rv s. P (not_recursive_cspaces s)\<rbrace>"
  apply (simp add: set_cdt_def, wp)
  apply (simp add: not_recursive_cspaces_def)
  done


lemma not_recursive_mdb[simp]:
  "not_recursive_cspaces (is_original_cap_update f s) =
   not_recursive_cspaces s"
  "not_recursive_cspaces (cdt_update f' s) =
   not_recursive_cspaces s"
  by (simp add: not_recursive_cspaces_def)+


lemma set_cap_no_new_recursive:
  "\<lbrace>\<lambda>s. x \<notin> not_recursive_cspaces s
      \<and> cte_wp_at (\<lambda>cap. ptr \<notin> fst_cte_ptrs cap) ptr s\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. x \<notin> not_recursive_cspaces s\<rbrace>"
  apply (simp add: not_recursive_cspaces_def)
  apply (wp set_cap_cte_wp_at_neg)
  apply (clarsimp simp: cte_wp_at_neg split: split_if)
  done


lemma not_recursive_set_cap_shrinks:
  "\<lbrace>\<lambda>s. card (not_recursive_cspaces s) \<le> n
      \<and> cte_wp_at (\<lambda>cap. ptr \<notin> fst_cte_ptrs cap) ptr s
      \<and> ptr \<in> fst_cte_ptrs cap\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. card (not_recursive_cspaces s) < n\<rbrace>"
  apply (rule shrinks_proof[where x=ptr])
     apply (rule not_recursive_cspaces_finite)
    apply (wp set_cap_no_new_recursive)
    apply simp
   apply (simp add: not_recursive_cspaces_def)
   apply (wp set_cap_cte_wp_at_neg)
   apply (clarsimp elim!: cte_wp_at_weakenE)
  apply (simp add: not_recursive_cspaces_def)
  done


lemma not_recursive_set_cap_doesn't_grow:
  "\<lbrace>\<lambda>s. card (not_recursive_cspaces s) < n
      \<and> cte_wp_at (\<lambda>cap. ptr \<notin> fst_cte_ptrs cap) ptr s\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. card (not_recursive_cspaces s) < n\<rbrace>"
  apply (rule doesn't_grow_proof)
   apply (rule not_recursive_cspaces_finite)
  apply (rule set_cap_no_new_recursive)
  done


lemma final_cap_duplicate_obj_ref:
  "\<lbrakk> fst (get_cap p1 s) = {(cap1, s)}; fst (get_cap p2 s) = {(cap2, s)}; is_final_cap' cap1 s;
     x \<in> obj_refs cap1; p1 \<noteq> p2 \<rbrakk> \<Longrightarrow> x \<notin> obj_refs cap2"
  apply (clarsimp simp: is_final_cap'_def)
  apply (subgoal_tac "{p1, p2} \<subseteq> {(a, b)}")
   apply simp
  apply (drule sym[where s="Collect p",standard], simp)
  apply blast
  done


lemma final_cap_duplicate_irq:
  "\<lbrakk> fst (get_cap p1 s) = {(cap1, s)}; fst (get_cap p2 s) = {(cap2, s)}; is_final_cap' cap1 s;
     x \<in> cap_irqs cap1; p1 \<noteq> p2 \<rbrakk> \<Longrightarrow> x \<notin> cap_irqs cap2"
  apply (clarsimp simp: is_final_cap'_def)
  apply (subgoal_tac "{p1, p2} \<subseteq> {(a, b)}")
   apply simp
  apply (drule sym[where s="Collect p",standard], simp)
  apply blast
  done


lemma fst_cte_ptrs_link_obj_refs:
  "x \<in> fst_cte_ptrs cap \<Longrightarrow> fst x \<in> obj_refs cap"
  by (case_tac cap, simp_all add: fst_cte_ptrs_def)


lemma final_cap_duplicate_cte_ptr:
  "\<lbrakk> fst (get_cap p s) = {(cap, s)}; fst (get_cap p' s) = {(cap', s)}; is_final_cap' cap s;
     x \<in> fst_cte_ptrs cap; p \<noteq> p' \<rbrakk> \<Longrightarrow> x \<notin> fst_cte_ptrs cap'"
  apply (drule(2) final_cap_duplicate_obj_ref)
    apply (erule fst_cte_ptrs_link_obj_refs)
   apply assumption
  apply (clarsimp simp: fst_cte_ptrs_link_obj_refs)
  done

lemma not_recursive_cspaces_more_update[iff]:
  "not_recursive_cspaces (trans_state f s) = not_recursive_cspaces s"
  by (simp add: not_recursive_cspaces_def)

lemma cap_swap_not_recursive:
  "\<lbrace>\<lambda>s. card (not_recursive_cspaces s) \<le> n
     \<and> cte_wp_at (\<lambda>cap. is_final_cap' cap s
                      \<and> p1 \<in> fst_cte_ptrs cap) p2 s
     \<and> cte_wp_at (op = c1) p1 s
     \<and> cte_wp_at (op = c2) p2 s
     \<and> p1 \<noteq> p2\<rbrace>
     cap_swap c1 p1 c2 p2
   \<lbrace>\<lambda>rv s. card (not_recursive_cspaces s) < n\<rbrace>"
  apply (cases "p1 = p2", simp_all)
  apply (simp add: cap_swap_def set_cdt_def when_def)
  apply (rule hoare_vcg_precond_imp)
   apply (wp | simp)+
      apply (rule not_recursive_set_cap_doesn't_grow)
     apply (wp not_recursive_set_cap_shrinks set_cap_cte_wp_at' get_cap_wp hoare_vcg_disj_lift)
  apply (clarsimp simp: cte_wp_at_def)
  apply (frule(3) final_cap_duplicate_cte_ptr)
   apply simp
  apply (case_tac c2, simp_all add: fst_cte_ptrs_def)
  done


lemma cap_swap_fd_not_recursive:
  "\<lbrace>\<lambda>s. card (not_recursive_cspaces s) \<le> n
     \<and> cte_wp_at (\<lambda>cap. is_final_cap' cap s
                      \<and> p1 \<in> fst_cte_ptrs cap) p2 s
     \<and> p1 \<noteq> p2\<rbrace>
     cap_swap_for_delete p1 p2
   \<lbrace>\<lambda>rv s. card (not_recursive_cspaces s) < n\<rbrace>"
  apply(simp add: cap_swap_for_delete_def)
  apply(wp cap_swap_not_recursive)
    apply(clarsimp)
    apply(wp get_cap_wp)
  apply(clarsimp)
  done


lemma set_mrs_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_mrs p' b m \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>" 
  apply (simp add: set_mrs_def bind_assoc set_object_def)
  apply (cases b)
   apply simp
   apply wp
   apply clarsimp
   apply (drule get_tcb_SomeD)
   apply (clarsimp simp: obj_at_def a_type_def split: split_if)
  apply (clarsimp simp: zipWithM_x_mapM split_def
             split del: split_if)
  apply (wp mapM_wp')
  apply clarsimp
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def a_type_def split: split_if)
  done


lemma cte_wp_and:
  "cte_wp_at (P and Q) c s = (cte_wp_at P c s \<and> cte_wp_at Q c s)"
  by (auto simp: cte_wp_at_def)


lemma set_ep_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_endpoint e p \<lbrace>\<lambda>_. cte_wp_at P c\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def get_object_def)
  apply wp
  apply (auto simp: cte_wp_at_cases split: split_if)
  done


lemma set_aep_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_async_ep e p \<lbrace>\<lambda>_. cte_wp_at P c\<rbrace>"
  apply (simp add: set_async_ep_def set_object_def get_object_def)
  apply wp
  apply (auto simp: cte_wp_at_cases)
  done


crunch cte_wp_at[wp]: get_mrs "cte_wp_at P c"
  (wp: crunch_wps simp: crunch_simps) 


lemmas cte_wp_and' = cte_wp_and [unfolded pred_conj_def]


lemma in_pspace_typ_at:
  "r \<notin> dom (kheap s) = (\<forall>T. \<not> typ_at T r s)"
  apply (simp add: dom_def)
  apply (subst simp_thms(2)[symmetric])
  apply (fastforce simp: obj_at_def)
  done


lemma suspend_not_recursive:
  "\<lbrace>\<lambda>s. P (not_recursive_cspaces s)\<rbrace>
     IpcCancel_A.suspend t
   \<lbrace>\<lambda>rv s. P (not_recursive_cspaces s)\<rbrace>"
  apply (simp add: not_recursive_cspaces_def cte_wp_at_caps_of_state)
  apply (wp suspend_caps_of_state)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (erule rsubst[where P=P])
  apply (intro set_eqI iffI)
   apply (clarsimp simp: fst_cte_ptrs_def)
  apply clarsimp
  apply (clarsimp simp: fst_cte_ptrs_def can_fast_finalise_def
                 split: cap.split_asm)
  done


lemma get_cap_det2:
  "(r, s') \<in> fst (get_cap p s) \<Longrightarrow> get_cap p s = ({(r, s)}, False) \<and> s' = s"
  apply (rule conjI)
   apply (erule get_cap_det)
  apply (erule use_valid [OF _ get_cap_inv])
  apply simp
  done


lemma set_zombie_not_recursive:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>c. fst_cte_ptrs c = fst_cte_ptrs (cap.Zombie p zb n)) slot s
     \<and> P (not_recursive_cspaces s)\<rbrace>
     set_cap (cap.Zombie p zb n) slot
   \<lbrace>\<lambda>rv s. P (not_recursive_cspaces s)\<rbrace>"
  apply (simp add: not_recursive_cspaces_def)
  apply (rule set_preserved_proof[where P=P])
   apply simp_all
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift set_cap_cte_wp_at)
   apply (fastforce simp: cte_wp_at_def fst_cte_ptrs_def)
  apply (simp only: cte_wp_at_neg imp_conv_disj de_Morgan_conj simp_thms)
  apply (wp hoare_vcg_ex_lift valid_cte_at_neg_typ[OF set_cap_typ_at]
            hoare_vcg_disj_lift set_cap_cte_wp_at)
  apply (fastforce simp: fst_cte_ptrs_def cte_wp_at_def)
  done


definition
  rdcall_finalise_ord_lift :: "((cslot_ptr \<times> 'z state) \<times> (cslot_ptr \<times> 'z state)) set
                                  \<Rightarrow> ((rec_del_call \<times> 'z state) \<times> (rec_del_call \<times> 'z state)) set"
where
 "rdcall_finalise_ord_lift S \<equiv>
      (\<lambda>(x, s). case x of CTEDeleteCall a b \<Rightarrow> 3 | FinaliseSlotCall a b \<Rightarrow> 2
                            | ReduceZombieCall cap a b \<Rightarrow> 1)
          <*mlex*>
       ((map_pair (\<lambda>(x, s). (FinaliseSlotCall x True, s)) (\<lambda>(x, s). (FinaliseSlotCall x True, s)) ` S)
         \<union> (map_pair (\<lambda>(x, s). (FinaliseSlotCall x False, s)) (\<lambda>(x, s). (FinaliseSlotCall x False, s)) ` S))"


lemma wf_rdcall_finalise_ord_lift:
  "wf S \<Longrightarrow> wf (rdcall_finalise_ord_lift S)"
  unfolding rdcall_finalise_ord_lift_def
  by (auto intro!: wf_mlex wf_Un wf_map_pair_image inj_onI)


definition
  rec_del_recset :: "((rec_del_call \<times> 'z::state_ext state) \<times> (rec_del_call \<times> 'z::state_ext state)) set"
where
 "rec_del_recset \<equiv>
    wf_sum (exposed_rdcall \<circ> fst)
      (rdcall_finalise_ord_lift (inv_image
                   (less_than <*lex*> less_than)
                   (\<lambda>(x, s). case caps_of_state s x of 
                              Some cap.NullCap \<Rightarrow> (0, 0)
                            | Some (cap.Zombie p zb n) \<Rightarrow>
                               (if fst_cte_ptrs (cap.Zombie p zb n) = {x} then 1 else 2, n)
                            | _ \<Rightarrow> (3, 0))))
      (rdcall_finalise_ord_lift (measure (\<lambda>(x, s). card (not_recursive_cspaces s))))"


lemma rec_del_recset_wf: "wf rec_del_recset"
  unfolding rec_del_recset_def
  by (intro wf_sum_wf wf_rdcall_finalise_ord_lift wf_measure
            wf_inv_image wf_lex_prod wf_less_than)


lemma in_get_cap_cte_wp_at:
  "(rv, s') \<in> fst (get_cap p s) = (s = s' \<and> cte_wp_at (op = rv) p s)"
  apply (rule iffI)
   apply (clarsimp dest!: get_cap_det2 simp: cte_wp_at_def)
  apply (clarsimp simp: cte_wp_at_def)
  done


lemma fst_cte_ptrs_first_cte_of:
  "fst_cte_ptrs (cap.Zombie ptr zb n) = {first_cslot_of (cap.Zombie ptr zb n)}"
  by (simp add: fst_cte_ptrs_def tcb_cnode_index_def)


lemma final_cap_still_at:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>c. obj_refs cap = obj_refs c \<and> cap_irqs cap = cap_irqs c
                         \<and> P cap (is_final_cap' c s)) ptr s\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. P c (is_final_cap' c s)) ptr s\<rbrace>"
  apply (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state)
  apply wp
  apply (clarsimp elim!: rsubst[where P="P cap"])
  apply (intro ext arg_cong[where f=Ex] arg_cong[where f=All])
  apply (case_tac "(aa, ba) = ptr", simp_all add: obj_irq_refs_def)
  done


lemma suspend_thread_cap:
  "\<lbrace>\<lambda>s. caps_of_state s x = Some (cap.ThreadCap p)\<rbrace>
     IpcCancel_A.suspend t
   \<lbrace>\<lambda>rv s. caps_of_state s x = Some (cap.ThreadCap p)\<rbrace>"
  apply (rule hoare_chain)
    apply (rule suspend_cte_wp_at_preserved
                  [where p=x and P="op = (cap.ThreadCap p)"])
    apply (clarsimp simp add: can_fast_finalise_def)
   apply (simp add: cte_wp_at_caps_of_state)+
  done

lemma not_recursive_cspaces_irq_state_independent[intro!, simp]:
  "not_recursive_cspaces (s \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr> \<rparr>)  
   = not_recursive_cspaces s"
  by (simp add: not_recursive_cspaces_def)


lemma cte_wp_at_irq_state_independent[intro!, simp]:
  "is_final_cap' x (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = is_final_cap' x s"
  by (simp add: is_final_cap'_def)


lemma zombies_final_irq_state_independent[intro!, simp]:
  "zombies_final (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = zombies_final s"
  by (simp add: zombies_final_def)


lemma ex_cte_cap_wp_to_irq_state_independent[intro!, simp]:
  "ex_cte_cap_wp_to x y (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = ex_cte_cap_wp_to x y s"
  by (simp add: ex_cte_cap_wp_to_def)


lemma invs_irq_state_independent[intro!, simp]:
  "invs (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = invs s"
  by (clarsimp simp: irq_state_independent_A_def invs_def 
      valid_state_def valid_pspace_def valid_mdb_def valid_ioc_def valid_idle_def
      only_idle_def if_unsafe_then_cap_def valid_reply_caps_def
      valid_reply_masters_def valid_global_refs_def valid_arch_state_def
      valid_irq_node_def valid_irq_handlers_def valid_machine_state_def
      valid_arch_objs_def valid_arch_caps_def valid_global_objs_def
      valid_kernel_mappings_def equal_kernel_mappings_def
      valid_asid_map_def valid_global_pd_mappings_def
      pspace_in_kernel_window_def cap_refs_in_kernel_window_def
      cur_tcb_def sym_refs_def state_refs_of_def pd_at_asid_def 
      swp_def valid_irq_states_def)


lemma emptyable_irq_state_independent[intro!, simp]:
  "emptyable x (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = emptyable x s"
  by (auto simp: emptyable_def)


termination rec_del
  apply (rule rec_del.termination,
         rule rec_del_recset_wf,
         simp_all add: rec_del_recset_def wf_sum_def
                       in_monad is_final_cap_def 
                       is_zombie_def rdcall_finalise_ord_lift_def
                       mlex_prod_def,
         drule in_preempt)
  apply (case_tac exposed, simp_all)
   apply (rule disjI1, rule map_pair_split_imageI)
   apply (simp only: trans_state_update'[symmetric])
   apply (clarsimp)
   apply (case_tac aa, simp_all add: fail_def rec_del.psimps)[1]
   apply (case_tac nat, simp_all)[1]
   apply (clarsimp simp: in_monad rec_del.psimps)
   apply (clarsimp simp: in_monad in_get_cap_cte_wp_at
                         cte_wp_at_caps_of_state rec_del.psimps
                  split: split_if_asm)
    apply (erule use_valid [OF _ set_cap_caps_of_state])+
    apply (simp add: fst_cte_ptrs_first_cte_of cong: if_cong)
    apply (case_tac rv, simp_all)[1]
    apply (clarsimp simp: in_monad fst_cte_ptrs_first_cte_of)
   apply (case_tac new_cap, simp_all add: is_cap_simps)[1]
    apply (case_tac rv, simp_all)[1]
   apply (clarsimp simp: fst_cte_ptrs_first_cte_of)
   apply (case_tac rv, simp_all)[1]
   apply (clarsimp simp: fst_cte_ptrs_first_cte_of in_monad)
  apply (rule disjI2, rule map_pair_split_imageI)
  apply clarsimp
  apply (case_tac aa, simp_all add: fail_def rec_del.psimps)[1]
  apply (case_tac nat, simp_all)
  apply (simp only: trans_state_update'[symmetric] not_recursive_cspaces_more_update)
  apply (clarsimp simp: in_monad Pair_fst_snd_eq rec_del.psimps)
  apply (erule use_valid [OF _ cap_swap_fd_not_recursive])
  apply (frule use_valid [OF _ get_cap_cte_wp_at], simp)
  apply (drule in_inv_by_hoareD [OF get_cap_inv])
  apply clarsimp
  apply (erule use_valid [OF _ hoare_vcg_conj_lift [OF set_zombie_not_recursive
                                                      final_cap_still_at]])
  apply (frule use_valid [OF _ finalise_cap_cases])
   apply (fastforce simp add: cte_wp_at_eq_simp)
  apply clarsimp
  apply (case_tac rv, simp_all add: fst_cte_ptrs_def)
    apply (clarsimp simp: in_monad cte_wp_at_caps_of_state
                          fst_cte_ptrs_def
                   split: split_if_asm)
   apply (clarsimp simp: in_monad cte_wp_at_caps_of_state
                         fst_cte_ptrs_def
                  split: split_if_asm)
   apply (frule(1) use_valid [OF _ suspend_thread_cap])
   apply clarsimp
   apply (erule use_valid [OF _ suspend_not_recursive])
   apply simp
  apply (clarsimp simp: in_monad cte_wp_at_caps_of_state
                        fst_cte_ptrs_def zombie_cte_bits_def
                        tcb_cnode_index_def
                 split: option.split_asm)
  done


lemmas rec_del_simps_ext =
    rec_del.simps [THEN ext[where f="rec_del args", standard]]


lemmas rec_del_fails = spec_validE_fail rec_del_simps_ext(5-)


declare assertE_wp[wp]


declare unlessE_wp[wp_split]


lemma without_preemption_wp [wp_split]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> without_preemption f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp


lemma rec_del_preservation':
  assumes wp:
    "\<And>sl1 sl2. \<lbrace>P\<rbrace> cap_swap_for_delete sl1 sl2 \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl cap. \<lbrace>P\<rbrace> set_cap sl cap \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl opt. \<lbrace>P\<rbrace> empty_slot sl opt \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>cap fin. \<lbrace>P\<rbrace> finalise_cap cap fin \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>cap fin. \<lbrace>P\<rbrace> preemption_point \<lbrace>\<lambda>rv. P\<rbrace>"
  shows
  "s \<turnstile> \<lbrace>P\<rbrace> rec_del call \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
proof (induct rule: rec_del.induct, simp_all only: rec_del_fails)
  case (1 slot exposed s)
  show ?case
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply wp
     apply (wp wp)[1]
    apply (rule spec_strengthen_postE)
     apply (rule "1.hyps")
    apply simp
    done
next
  case (2 slot exposed s)
  show ?case
    apply (subst rec_del.simps)
    apply (simp only: split_def)
    apply (wp wp "2.hyps", assumption+)
         apply (wp wp)[1]
        apply (simp only: simp_thms)
        apply (rule "2.hyps", assumption+)
       apply (wp wp hoare_drop_imps | simp add: is_final_cap_def)+
    done
next
  case 3
  show ?case
    apply (simp | wp wp)+
    done
next
  case (4 ptr bits n slot s)
  show ?case
    apply (subst rec_del.simps)
    apply (wp wp)
      apply (wp hoare_drop_imps)[1]
     apply (simp only: simp_thms)
     apply (rule "4.hyps", assumption+)
    apply wp
    done
qed


lemmas rec_del_preservation =
       validE_valid [OF use_spec(2) [OF rec_del_preservation']]


lemma cap_swap_fd_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> cap_swap_for_delete src dst \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply(simp add: cap_swap_for_delete_def)
  apply(wp cap_swap_typ_at)
  apply(simp)
  done


lemma cap_swap_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> cap_swap_for_delete x y \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  apply(simp add: cap_swap_for_delete_def)
  apply(wp cap_swap_valid_cap)
  apply(simp)
  done


lemma cap_swap_cte_at:
  "\<lbrace>cte_at p\<rbrace> cap_swap_for_delete x y \<lbrace>\<lambda>_. cte_at p\<rbrace>"
  apply(simp add: cap_swap_for_delete_def) 
  apply(wp cap_swap_cte_at)
  apply(simp)
  done


lemma obj_at_interrupt_states[simp]:
  "obj_at P p (interrupt_states_update f s) = obj_at P p s"
  by (simp add: obj_at_def)


lemma obj_at_arch_state[simp]:
  "obj_at P p (arch_state_update f s) = obj_at P p s"
  by (simp add: obj_at_def)


lemma set_pt_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_pt ptr pt \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply wp
  apply (clarsimp simp: obj_at_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  apply (simp add: a_type_def)
  done


lemma set_pd_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_pd ptr pd \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply wp
  apply (clarsimp simp: obj_at_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  apply (simp add: a_type_def)
  done


lemma set_asid_pool_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply wp
  apply (clarsimp simp: obj_at_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  apply (simp add: a_type_def)
  done


lemma rec_del_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> rec_del call \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wp rec_del_preservation ep_cancel_all_typ_at aep_cancel_all_typ_at
           cap_swap_fd_typ_at empty_slot_typ_at set_cap_typ_at
           irq_state_independent_AI preemption_point_inv
       | simp)+


lemma rec_del_cte_at:
  "\<lbrace>cte_at c\<rbrace> rec_del call \<lbrace>\<lambda>_. cte_at c\<rbrace>"
  by (wp valid_cte_at_typ rec_del_typ_at)


lemma cte_at_nat_to_cref_zbits:
  "\<lbrakk> s \<turnstile> cap.Zombie oref zb n; m < n \<rbrakk>
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


lemma dom_valid_cap[wp]:
  "\<lbrace>valid_cap c\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply simp
  done


lemma dom_cte_at:
  "\<lbrace>cte_at c\<rbrace> do_machine_op f \<lbrace>\<lambda>_. cte_at c\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (simp add: cte_at_cases)
  done


lemma cnode_to_zombie_valid:
  "\<lbrakk> s \<turnstile> cap.CNodeCap oref bits guard \<rbrakk>
    \<Longrightarrow> s \<turnstile> cap.Zombie oref (Some bits) (2 ^ bits)"
  by (clarsimp simp: valid_cap_def cap_table_at_cte_at
                     word_unat_power cap_aligned_def)


lemma tcb_to_zombie_valid:
  "\<lbrakk> s \<turnstile> cap.ThreadCap t \<rbrakk>
    \<Longrightarrow> s \<turnstile> cap.Zombie t None 5"
  apply (simp add: valid_cap_def)
  apply (simp add: cap_aligned_def)
  done


lemmas do_machine_op_cte_at [wp] = dom_cte_at 


declare set_cap_cte_at[wp]
        set_cap_valid_cap [wp]


lemma set_original_valid_pspace:
  "\<lbrace>valid_pspace\<rbrace> set_original p v \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply wp
  apply (erule valid_pspace_eqI)
  apply simp
  done


locale mdb_swap_abs_invs = mdb_swap_abs +
  fixes cs cs' cap cap' scap dcap
  defines "cs \<equiv> caps_of_state s"
  defines "cs' \<equiv> cs (src \<mapsto> dcap, dest \<mapsto> scap)"

  assumes cap: "cs src = Some cap"
  assumes cap': "cs dest = Some cap'"

  assumes sder: "weak_derived scap cap"
  assumes dder: "weak_derived dcap cap'"


lemma obj_ref_untyped_empty [simp]:
  "obj_refs c \<inter> untyped_range c = {}"
  by (cases c, auto)


lemma weak_derived_Reply_eq:
  "\<lbrakk> weak_derived c c'; c = cap.ReplyCap t m \<rbrakk> \<Longrightarrow> c' = cap.ReplyCap t m"
  "\<lbrakk> weak_derived c c'; c' = cap.ReplyCap t m \<rbrakk> \<Longrightarrow> c = cap.ReplyCap t m"
  by (auto simp: weak_derived_def copy_of_def
                 same_object_as_def is_cap_simps
          split: split_if_asm cap.split_asm arch_cap.split_asm)



lemma copy_of_cap_range:
  "copy_of cap cap' \<Longrightarrow> cap_range cap = cap_range cap'"
  apply (clarsimp simp: copy_of_def split: split_if_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def cap_range_def
                      split: cap.split_asm)+
  apply (subgoal_tac "\<exists>acap . cap = cap.ArchObjectCap acap", clarsimp)
   apply (case_tac acap, simp_all)
       apply (clarsimp split: arch_cap.split_asm cap.split_asm)+
  done


context mdb_swap_abs_invs
begin
lemmas src_ranges [simp] = weak_derived_ranges [OF sder]

lemmas dest_ranges [simp] = weak_derived_ranges [OF dder]


lemma no_mloop_n:
  "no_mloop n"
  by (simp add: no_mloop_def parency)


lemma mdb_cte_n:
  "mdb_cte_at (\<lambda>p. \<exists>c. cs' p = Some c \<and> cap.NullCap \<noteq> c) n"
proof -
  from valid_mdb
  have "mdb_cte_at (\<lambda>p. \<exists>c. cs p = Some c \<and> cap.NullCap \<noteq> c) m"
    by (simp add: cs_def m valid_mdb_def2)
  thus ?thesis using cap cap' sder dder
  apply (clarsimp simp add: mdb_cte_at_def)
  apply (cases src, cases dest)
  apply (simp add: n_def n'_def cs'_def split: split_if_asm)
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  apply fastforce
  done
qed


lemma descendants_no_loop [simp]:
  "x \<notin> descendants_of x m"
  by (simp add: descendants_of_def)


lemma untyped_mdb_n:
  "untyped_mdb n cs'"
proof -
  from valid_mdb
  have "untyped_mdb m cs"
    by (simp add: cs_def m valid_mdb_def2)
  thus ?thesis using cap cap'
    by (simp add: untyped_mdb_def cs'_def descendants_of_def parency 
                  s_d_swap_def
             del: split_paired_All)
qed


lemma descendants_inc_n:
  shows "descendants_inc n cs'"
proof -
  from valid_mdb
  have "descendants_inc m cs"
    by (simp add:cs_def m valid_mdb_def2)
  thus ?thesis using cap cap' sder dder
    apply (simp add:descendants_inc_def descendants_of_def del: split_paired_All)
    apply (intro impI allI)
    apply (simp add:parency cs'_def del:split_paired_All)
    apply (drule spec)+
    apply (erule(1) impE)
    apply (simp add:weak_derived_cap_class weak_derived_cap_range)
    apply (intro conjI impI)
    apply (simp add:s_d_swap_other)+
   done
 qed


lemma untyped_inc_n:
  assumes untyped_eq:"(is_untyped_cap cap \<Longrightarrow> scap = cap)" "(is_untyped_cap cap' \<Longrightarrow> dcap = cap')"
  shows "untyped_inc n cs'"
proof -
  from valid_mdb
  have "untyped_inc m cs"
    by (simp add: cs_def m valid_mdb_def2)
  thus ?thesis using cap cap'
    apply (simp add: untyped_inc_def cs'_def descendants_of_def parency s_d_swap_def 
                del: split_paired_All)
    apply (intro allI)
   apply (intro conjI)
    apply (intro impI allI)
    apply (intro conjI)
    apply (drule_tac x = p in spec)
    apply (drule_tac x = p' in spec)
    apply (clarsimp simp:untyped_eq)
   apply (intro impI allI)
   apply (drule_tac x = p' in spec)
   apply (drule_tac x = dest in spec)
   apply (clarsimp simp:untyped_eq)
   apply (intro impI)
    apply (intro conjI)
    apply (intro impI allI)
     apply (drule_tac x = src in spec)
     apply (intro conjI)
      apply (drule_tac x = dest in spec)
      apply (clarsimp simp:untyped_eq)
     apply (drule_tac x = p' in spec)
     apply (clarsimp simp:untyped_eq)
   apply (intro impI allI)
    apply (intro conjI)
     apply (drule_tac x = dest in spec)
     apply (drule_tac x = p in spec)
     apply (clarsimp simp:untyped_eq)
   apply (drule_tac x = src in spec)
   apply (drule_tac x = p in spec)
   apply (clarsimp simp:untyped_eq)
   done
qed


lemmas src_replies[simp] = weak_derived_replies [OF sder]

lemmas dest_replies[simp] = weak_derived_replies [OF dder]


lemma reply_caps_mdb_n:
  "reply_caps_mdb n cs'"
proof -
  from valid_mdb
  have "reply_caps_mdb m cs"
    by (simp add: cs_def m valid_mdb_def2 reply_mdb_def)
  thus ?thesis using cap cap' unfolding reply_caps_mdb_def cs'_def n_def n'_def
    apply (intro allI impI)
    apply (simp split: split_if_asm del: split_paired_All split_paired_Ex)
      apply (elim allE)
      apply (drule weak_derived_Reply_eq(1) [OF sder], simp del: split_paired_Ex)
      apply (erule(1) impE)
      apply (intro conjI impI)
       apply (clarsimp elim!: weak_derived_Reply_eq(2) [OF dder])
      apply (erule exEI, clarsimp)
     apply (elim allE)
     apply (drule weak_derived_Reply_eq(1) [OF dder], simp del: split_paired_Ex)
     apply (erule(1) impE)
     apply (intro conjI impI)
      apply (clarsimp elim!: weak_derived_Reply_eq(2) [OF sder])
     apply (erule exEI, clarsimp)
    apply (erule_tac x=ptr in allE, erule_tac x=t in allE)
    apply (erule(1) impE)
    apply (intro conjI impI)
      apply (clarsimp elim!: weak_derived_Reply_eq(2) [OF dder])
     apply (clarsimp elim!: weak_derived_Reply_eq(2) [OF sder])
    apply fastforce 
    done
qed


lemma reply_masters_mdb_n:
  "reply_masters_mdb n cs'"
proof -
  from valid_mdb
  have r: "reply_masters_mdb m cs"
    by (simp add: cs_def m valid_mdb_def2 reply_mdb_def)
  have n_None:
    "\<And>t. scap = cap.ReplyCap t True \<Longrightarrow> n dest = None"
    "\<And>t. dcap = cap.ReplyCap t True \<Longrightarrow> n src = None"
    using r cap cap' unfolding reply_masters_mdb_def n_def
     by (drule_tac weak_derived_Reply_eq(1) [OF sder]
                   weak_derived_Reply_eq(1) [OF dder],
         fastforce simp: n'_def simp del: split_paired_All)+
  show ?thesis unfolding reply_masters_mdb_def cs'_def using cap cap' r
    apply (intro allI impI)
    apply (simp add: n_None descendants s_d_swap_def
              split: split_if_asm del: split_paired_All)
      apply (unfold reply_masters_mdb_def)[1]
      apply (drule weak_derived_Reply_eq(1) [OF sder], simp del: split_paired_All)
      apply (elim allE, erule(1) impE, elim conjE)
      apply (intro impI conjI)
       apply (drule(1) bspec, rule weak_derived_Reply_eq(2) [OF dder], simp)
      apply fastforce
     apply (unfold reply_masters_mdb_def)[1]
     apply (drule weak_derived_Reply_eq(1) [OF dder], simp del: split_paired_All)
     apply (elim allE, erule(1) impE, elim conjE)
     apply (intro impI conjI)
      apply (drule(1) bspec, rule weak_derived_Reply_eq(2) [OF sder], simp)
     apply fastforce
    apply (unfold reply_masters_mdb_def)[1]
    apply (erule_tac x=ptr in allE, erule_tac x=t in allE)
    apply (erule(1) impE, erule conjE, simp add: n_def n'_def)
    apply (intro impI conjI)
        apply (rule weak_derived_Reply_eq(2) [OF dder]
                    weak_derived_Reply_eq(2) [OF sder],
               simp)+
    apply fastforce
    done
qed


lemma reply_mdb_n:
  "reply_mdb n cs'"
  by (simp add: reply_mdb_def reply_masters_mdb_n reply_caps_mdb_n)


end


definition
  "swap_mdb m src dest \<equiv> 
  let n' = (\<lambda>n. if m n = Some src then Some dest 
                else if m n = Some dest then Some src 
                else m n) in 
           n' (src := n' dest, dest := n' src)"


lemma cap_swap_mdb [wp]:
  "\<lbrace>valid_mdb and 
  cte_wp_at (weak_derived c) a and 
  cte_wp_at (\<lambda>cc. is_untyped_cap cc \<longrightarrow> cc = c) a and  
  cte_wp_at (weak_derived c') b and K (a \<noteq> b) and cte_wp_at (\<lambda>cc. is_untyped_cap cc \<longrightarrow> cc = c') b\<rbrace> 
  cap_swap c a c' b 
  \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: valid_mdb_def2 cap_swap_def set_cdt_def bind_assoc set_original_def)
  apply (wp | simp del: fun_upd_apply split del: split_if)+
  apply (fold swap_mdb_def [simplified Let_def])
  apply (wp set_cap_caps_of_state2 get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state simp del: fun_upd_apply)
  apply (subgoal_tac "mdb_swap_abs_invs (cdt s) a b s cap capb c c'")
   prefer 2
   apply (rule mdb_swap_abs_invs.intro)
    apply (rule mdb_swap_abs.intro)
        apply (simp add: valid_mdb_def2)
       apply (fastforce simp: cte_wp_at_caps_of_state)
      apply (fastforce simp: cte_wp_at_caps_of_state)
     apply (rule refl)
    apply assumption
   apply (erule (3) mdb_swap_abs_invs_axioms.intro)
  apply (unfold swap_mdb_def Let_def)
  apply (simp add: mdb_swap_abs_invs.no_mloop_n 
                   mdb_swap_abs_invs.untyped_mdb_n 
                   mdb_swap_abs_invs.mdb_cte_n
                   mdb_swap_abs_invs.reply_mdb_n
              del: fun_upd_apply
              split del: split_if)
  apply (rule conjI)
   apply (erule mdb_swap_abs_invs.descendants_inc_n)
  apply (rule conjI)
   apply (erule mdb_swap_abs_invs.untyped_inc_n)
     apply (clarsimp simp:cte_wp_at_caps_of_state)+
  apply (rule conjI)
   apply (simp add: ut_revocable_def weak_derived_ranges del: split_paired_All)
  apply (rule conjI)
   apply (simp add: irq_revocable_def del: split_paired_All)
   apply (intro conjI impI allI)
    apply (simp del: split_paired_All)
   apply (simp del: split_paired_All)
  apply (simp add: reply_master_revocable_def weak_derived_replies
              del: split_paired_All)
  done


lemma set_cdt_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> set_cdt m \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (simp add: set_cdt_def | wp)+


lemma cap_swap_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_cap c and valid_cap c'
        and tcb_cap_valid c b and tcb_cap_valid c' a\<rbrace>
     cap_swap c a c' b
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (wp set_cap_valid_objs
           | simp split del: split_if)+
  done


crunch aligned[wp]: cap_swap "pspace_aligned"

crunch disctinct[wp]: cap_swap "pspace_distinct"


lemma cap_swap_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap and cte_wp_at (\<lambda>x. zobj_refs x = zobj_refs c) a
          and cte_wp_at (\<lambda>x. zobj_refs x = zobj_refs c') b\<rbrace>
     cap_swap c a c' b
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (wp | simp split del: split_if)+
     apply (rule hoare_post_imp)
      apply (simp only: if_live_then_nonz_cap_def ex_nonz_cap_to_def
                        cte_wp_at_caps_of_state imp_conv_disj)
     apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_ex_lift
               get_cap_wp)
  apply (clarsimp simp add: cte_wp_at_caps_of_state)
  apply (frule(1) if_live_then_nonz_capD)
   apply assumption
  apply (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_caps_of_state)
  apply (subst split_paired_Ex[symmetric])
  apply (rule_tac x="if (aa, ba) = a then b else if (aa, ba) = b then a else (aa, ba)"
                    in exI)
  apply (clarsimp | rule conjI)+
  done


lemma cap_swap_fd_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace>
     cap_swap_for_delete a b
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma set_cdt_caps_of[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_cdt m \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by wp


lemma cap_swap_ex_cte_cap[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p
          and cte_wp_at (\<lambda>x. cte_refs x = cte_refs c
                             \<and> ((\<exists>y. cte_refs x y \<noteq> {}) \<longrightarrow> P x = P c)) a
          and cte_wp_at (\<lambda>x. cte_refs x = cte_refs c'
                             \<and> ((\<exists>y. cte_refs x y \<noteq> {}) \<longrightarrow> P x = P c')) b\<rbrace>
     cap_swap c a c' b
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  apply (simp add: cap_swap_def ex_cte_cap_wp_to_def
                   cte_wp_at_caps_of_state
              del: split_paired_Ex)
  apply (wp get_cap_wp | simp split del: split_if del: split_paired_Ex)+
  apply (simp del: split_paired_Ex | intro allI impI | erule conjE)+
  apply (erule exfEI [where f="id ( a := b, b := a )"])
  apply (clarsimp simp: cte_wp_at_caps_of_state | rule conjI)+
  done


lemma cap_swap_fd_ex_cte_cap[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace> cap_swap_for_delete a b \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma cap_swap_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P ((caps_of_state s) ( a := Some c', b := Some c ))\<rbrace>
     cap_swap c a c' b
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (wp get_cap_wp | simp split del: split_if)+
  done


lemma cap_swap_fd_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P ((caps_of_state s) \<circ> (id ( a := b, b := a )))\<rbrace>
     cap_swap_for_delete a b
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp)
  apply (cases "a = b")
   apply (simp add: fun_upd_def id_def[symmetric] cong: if_cong)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (erule rsubst[where P=P])
  apply (clarsimp intro!: ext)
  done


lemma cap_irqs_appropriateness:
  "cap_irqs cap = cap_irqs cap'
    \<Longrightarrow> \<forall>cp. appropriate_cte_cap cp cap = appropriate_cte_cap cp cap'"
  by (simp add: appropriate_cte_cap_irqs)


lemma cap_swap_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap
          and ex_cte_cap_wp_to (appropriate_cte_cap c') a
          and ex_cte_cap_wp_to (appropriate_cte_cap c) b
          and cte_wp_at (\<lambda>x. cte_refs x = cte_refs c
                             \<and> ((\<exists>y. cte_refs x y \<noteq> {}) \<longrightarrow> cap_irqs x = cap_irqs c)) a
          and cte_wp_at (\<lambda>x. cte_refs x = cte_refs c'
                             \<and> ((\<exists>y. cte_refs x y \<noteq> {}) \<longrightarrow> cap_irqs x = cap_irqs c')) b\<rbrace>
     cap_swap c a c' b 
   \<lbrace>\<lambda>rv s. if_unsafe_then_cap s\<rbrace>"
  apply (simp only: if_unsafe_then_cap_def cte_wp_at_caps_of_state
                    imp_conv_disj not_ex)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply (clarsimp split del: split_if del: disjCI intro!: disjCI2)
  apply (intro conjI)
    apply (clarsimp split: split_if_asm)
    apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
     apply clarsimp
    apply (erule ex_cte_cap_wp_to_weakenE)
    apply clarsimp
   apply (auto dest!: cap_irqs_appropriateness elim!: cte_wp_at_weakenE)
  done


lemma cap_irqs_appropriate_strengthen:
  "ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) x s
     \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) x s"
  by (auto simp: appropriate_cte_cap_def
          elim!: ex_cte_cap_wp_to_weakenE
          split: cap.split)


lemma cap_swap_fd_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap
         and ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) a
         and ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) b\<rbrace>
     cap_swap_for_delete a b 
   \<lbrace>\<lambda>rv s. if_unsafe_then_cap s\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state
           | strengthen cap_irqs_appropriate_strengthen)+
  done


lemma cap_swap_zombies[wp]:
  "\<lbrace>zombies_final and cte_wp_at (\<lambda>x. is_zombie x = is_zombie c
                                   \<and> obj_refs x = obj_refs c
                                   \<and> cap_irqs x = cap_irqs c) a
          and cte_wp_at (\<lambda>x. is_zombie x = is_zombie c' \<and> obj_refs x = obj_refs c'
                                 \<and> cap_irqs x = cap_irqs c') b\<rbrace>
     cap_swap c a c' b
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp only: zombies_final_def final_cap_at_eq
                    cte_wp_at_caps_of_state simp_thms pred_conj_def)
  apply wp
  apply (elim conjE)
  apply (erule allfEI[where f="id ( a := b, b := a )"])
  apply (intro impI)
  apply (drule mp)
   apply (clarsimp split: split_if_asm)
  apply (elim exE conjE, simp only: simp_thms option.simps)
  apply (rule conjI)
   apply (clarsimp simp: is_cap_simps obj_irq_refs_def)
  apply (erule allfEI[where f="id ( a := b, b := a )"])
  apply (intro impI, elim exE conjE, simp only: simp_thms option.simps)
  apply (clarsimp simp: obj_irq_refs_Int split: split_if_asm)
  done


lemma cap_swap_fd_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace>
     cap_swap_for_delete p p'
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma cap_swap_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> cap_swap c sl c' sl' \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding cap_swap_def by (wp | simp)+
  

lemma unique_reply_caps_cap_swap:
  assumes u: "unique_reply_caps cs"
  and     c: "cs p = Some cap"
  and    c': "cs p' = Some cap'"
  and    wd: "weak_derived c cap"
  and   wd': "weak_derived c' cap'"
  and  pneq: "p \<noteq> p'"
  shows "unique_reply_caps (cs (p \<mapsto> c', p' \<mapsto> c))"
proof -
  have new_cap_is_unique[elim]:
    "\<And>p'' c''.
     \<lbrakk> is_reply_cap c''; p'' \<noteq> p; p'' \<noteq> p'; cs p'' = Some c''; c'' = c \<or> c'' = c' \<rbrakk>
     \<Longrightarrow> False"
    using u unfolding unique_reply_caps_def
    apply (erule_tac disjE)
     apply (elim allE)
     apply (erule (1) impE, erule (1) impE)
     apply (erule impE, rule c)
     apply (simp add: weak_derived_reply_eq[OF wd])
    apply (elim allE)
    apply (erule (1) impE, erule (1) impE)
    apply (erule impE, rule c')
    apply (simp add: weak_derived_reply_eq[OF wd'])
    done
  have old_caps_differ:
    "\<And>cap''.
     \<lbrakk> is_reply_cap cap; is_reply_cap cap'; cap = cap''; cap' = cap'' \<rbrakk>
     \<Longrightarrow> False"
    using u unfolding unique_reply_caps_def
    apply (elim allE)
    apply (erule impE, rule c)
    apply (erule impE, simp)
    apply (erule impE, rule c')
    apply (simp add: pneq)
    done
  have new_caps_differ:
    "\<And>c''. \<lbrakk> is_reply_cap c''; c = c''; c' = c'' \<rbrakk> \<Longrightarrow> False"
    apply (subgoal_tac "is_reply_cap c", subgoal_tac "is_reply_cap c'")
      apply (subst(asm) weak_derived_replies [OF wd])
      apply (subst(asm) weak_derived_replies [OF wd'])
      apply (frule(1) old_caps_differ)
          apply (simp add: weak_derived_reply_eq [OF wd])
         apply (simp add: weak_derived_reply_eq [OF wd'])
        apply simp+
    done
  show ?thesis
    using u unfolding unique_reply_caps_def
    apply (intro allI impI)
    apply (simp split: split_if_asm del: split_paired_All)
         apply (erule(2) new_caps_differ | fastforce)+
    done
qed


lemma cap_swap_no_reply_caps:
  assumes cap: "cs p = Some cap"
  and    cap': "cs p' = Some cap'"
  and      wd: "weak_derived c cap"
  and     wd': "weak_derived c' cap'"
  and      nr: "\<forall>sl. cs sl \<noteq> Some (cap.ReplyCap t False)"
  shows        "\<forall>sl. (cs(p \<mapsto> c', p' \<mapsto> c)) sl \<noteq> Some (cap.ReplyCap t False)"
proof -
  have
    "cap \<noteq> cap.ReplyCap t False"
    "cap' \<noteq> cap.ReplyCap t False"
    using cap cap' nr by clarsimp+
  hence
    "c \<noteq> cap.ReplyCap t False"
    "c' \<noteq> cap.ReplyCap t False"
    by (rule_tac ccontr, simp,
        drule_tac weak_derived_Reply_eq [OF wd]
                  weak_derived_Reply_eq [OF wd'],
        simp)+
  thus ?thesis
    using nr unfolding fun_upd_def
    by (clarsimp split: split_if_asm)
qed


lemma cap_swap_has_reply_cap_neg:
  "\<lbrace>\<lambda>s. \<not> has_reply_cap t s \<and>
    cte_wp_at (weak_derived c) p s \<and>
    cte_wp_at (weak_derived c') p' s \<and>
    p \<noteq> p'\<rbrace>
   cap_swap c p c' p' \<lbrace>\<lambda>rv s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: has_reply_cap_def cte_wp_at_caps_of_state
              del: split_paired_All split_paired_Ex)
  apply (wp cap_swap_caps_of_state)
  apply (elim conjE exE)
  apply (erule(4) cap_swap_no_reply_caps)
  done


lemma cap_swap_replies:
  "\<lbrace>\<lambda>s. valid_reply_caps s
       \<and> cte_wp_at (weak_derived c) p s
       \<and> cte_wp_at (weak_derived c') p' s
       \<and> p \<noteq> p'\<rbrace>
     cap_swap c p c' p'
   \<lbrace>\<lambda>rv s. valid_reply_caps s\<rbrace>"
  apply (simp add: valid_reply_caps_def)
  apply (rule hoare_pre)
   apply (simp only: imp_conv_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift cap_swap_has_reply_cap_neg)
  apply (clarsimp simp: fun_upd_def cte_wp_at_caps_of_state
                        unique_reply_caps_cap_swap [simplified fun_upd_def])
  done


lemma cap_swap_fd_replies[wp]:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
     cap_swap_for_delete p p'
   \<lbrace>\<lambda>rv s. valid_reply_caps s\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp cap_swap_replies get_cap_wp)
  apply (fastforce elim: cte_wp_at_weakenE)
  done


lemma cap_swap_reply_masters:
  "\<lbrace>valid_reply_masters and K(\<not> is_master_reply_cap c \<and> \<not> is_master_reply_cap c')\<rbrace>
   cap_swap c p c' p' \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  apply (simp add: valid_reply_masters_def cte_wp_at_caps_of_state)
  apply (rule hoare_pre)
  apply (simp only: imp_conv_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift cap_swap_caps_of_state
             cap_swap_typ_at tcb_at_typ_at)
  apply (auto simp: is_cap_simps)
  done


lemma cap_swap_fd_reply_masters[wp]:
  "\<lbrace>valid_reply_masters and
        cte_wp_at (\<lambda>c. \<not> is_master_reply_cap c) p and
        cte_wp_at (\<lambda>c. \<not> is_master_reply_cap c) p'\<rbrace>
     cap_swap_for_delete p p'
   \<lbrace>\<lambda>rv. valid_reply_masters\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp cap_swap_reply_masters get_cap_wp)
  apply (clarsimp simp: cte_wp_at_def)
  done


crunch refs_of[wp]: cap_swap "\<lambda>s. P (state_refs_of s)"
  (ignore: set_cap simp: state_refs_of_pspaceI)


crunch cur_tcb[wp]: cap_swap "cur_tcb"


lemma copy_of_cte_refs:
  "copy_of cap cap' \<Longrightarrow> cte_refs cap = cte_refs cap'"
  apply (rule ext, clarsimp simp: copy_of_def split: split_if_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm arch_cap.split_asm)+
  done


lemma copy_of_zobj_refs:
  "copy_of cap cap' \<Longrightarrow> zobj_refs cap = zobj_refs cap'"
  apply (clarsimp simp: copy_of_def split: split_if_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm)+
  apply (subgoal_tac "\<exists>acap . cap = cap.ArchObjectCap acap", clarsimp)
   apply (case_tac acap, simp_all)
       apply (clarsimp split: arch_cap.split_asm cap.split_asm)+
  done


lemma copy_of_is_zombie:
  "copy_of cap cap' \<Longrightarrow> is_zombie cap = is_zombie cap'"
  apply (clarsimp simp: copy_of_def split: split_if_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def
                      split: arch_cap.split_asm cap.split_asm)+
  done


lemma copy_of_reply_cap:
  "copy_of (cap.ReplyCap t False) cap \<Longrightarrow> cap = cap.ReplyCap t False"
  apply (clarsimp simp: copy_of_def is_cap_simps)
  apply (cases cap, simp_all add: same_object_as_def)
  apply (case_tac arch_cap, simp_all)
  done


lemma copy_of_cap_irqs:
  "copy_of cap cap' \<Longrightarrow> cap_irqs cap = cap_irqs cap'"
  apply (clarsimp simp: copy_of_def cap_irqs_def split: split_if_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def cap_range_def
                      split: cap.split_asm)+
  apply (case_tac arch_cap, simp_all)
      apply (clarsimp split: arch_cap.split_asm cap.split_asm)+
  done


lemma cap_swap_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace>
   cap_swap c a c' b \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: cap_swap_def set_cdt_def)
  apply (wp set_cap_idle set_cap_it|simp)+
  done


lemma cap_swap_global_refs[wp]:
  "\<lbrace>valid_global_refs and
      (\<lambda>s. global_refs s \<inter> cap_range c = {}) and
      (\<lambda>s. global_refs s \<inter> cap_range c' = {})\<rbrace>
    cap_swap c a c' b \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (simp add: cap_swap_def set_cdt_def)
  apply (wp set_cap_globals | simp)+
  done


crunch arch[wp]: cap_swap "\<lambda>s. P (arch_state s)"

crunch irq_node[wp]: cap_swap "\<lambda>s. P (interrupt_irq_node s)"


lemma valid_reply_caps_of_stateD:
  "\<And>p t s. \<lbrakk> valid_reply_caps s; caps_of_state s p = Some (cap.ReplyCap t False) \<rbrakk>
   \<Longrightarrow> st_tcb_at awaiting_reply t s"
  by (auto simp: valid_reply_caps_def has_reply_cap_def cte_wp_at_caps_of_state)


crunch interrupt_states[wp]: cap_swap "\<lambda>s. P (interrupt_states s)"


lemma weak_derived_cap_irqs:
  "weak_derived c c' \<Longrightarrow> cap_irqs c = cap_irqs c'"
  by (auto simp add: weak_derived_def copy_of_cap_irqs)


lemma cap_swap_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers and
    cte_wp_at (weak_derived c) a and
    cte_wp_at (weak_derived c') b\<rbrace> 
     cap_swap c a c' b \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: valid_irq_handlers_def irq_issued_def)
  apply (rule hoare_pre)
   apply (wp hoare_use_eq [where f=interrupt_states, 
                           OF cap_swap_interrupt_states cap_swap_caps_of_state])
  apply (clarsimp simp: cte_wp_at_caps_of_state
                 elim!: ranE split: split_if_asm
                 dest!: weak_derived_cap_irqs)
    apply auto
  done


crunch arch_objs [wp]: cap_swap "valid_arch_objs"

crunch arch_objs [wp]: cap_move "valid_arch_objs"

crunch arch_objs [wp]: empty_slot "valid_arch_objs"

crunch executable_arch_objs [wp]: cap_swap "executable_arch_objs"

crunch executable_arch_objs [wp]: cap_move "executable_arch_objs"

crunch executable_arch_objs [wp]: empty_slot "executable_arch_objs"


crunch valid_global_objs [wp]: cap_swap "valid_global_objs"


lemma vs_cap_ref_master:
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


lemma weak_derived_vs_cap_ref:
  "weak_derived c c' \<Longrightarrow> vs_cap_ref c = vs_cap_ref c'"
  by (auto simp: weak_derived_def copy_of_def
                 same_object_as_def2
          split: split_if_asm elim: vs_cap_ref_master[OF sym])


lemma weak_derived_table_cap_ref:
  "weak_derived c c' \<Longrightarrow> table_cap_ref c = table_cap_ref c'"
  apply (clarsimp simp: weak_derived_def copy_of_def
                 same_object_as_def2 
          split: split_if_asm)
   apply (elim disjE,simp_all add:is_cap_simps)
  apply (elim disjE,simp_all)
  apply clarsimp
  apply (frule vs_cap_ref_master[OF sym],simp+)
  apply (drule vs_cap_ref_eq_imp_table_cap_ref_eq')
   apply simp
  apply simp
  done


lemma weak_derived_pd_pt_asid:
  "weak_derived c c' \<Longrightarrow> cap_asid c = cap_asid c'
                       \<and> is_pt_cap c = is_pt_cap c'
                       \<and> is_pd_cap c = is_pd_cap c'"
  by (auto simp: weak_derived_def copy_of_def is_cap_simps
                 same_object_as_def2 is_pt_cap_def
                 cap_master_cap_simps
          split: split_if_asm
          dest!: cap_master_cap_eqDs)


lemma weak_derived_ASIDPool1:
  "weak_derived (cap.ArchObjectCap (arch_cap.ASIDPoolCap ap asid)) cap =
  (cap = cap.ArchObjectCap (arch_cap.ASIDPoolCap ap asid))"
  apply (rule iffI)
   prefer 2
   apply simp
  apply (clarsimp simp: weak_derived_def copy_of_def split: split_if_asm)
  apply (clarsimp simp: same_object_as_def2 cap_master_cap_simps dest!: cap_master_cap_eqDs)
  done
  

lemma weak_derived_ASIDPool2:
  "weak_derived cap (cap.ArchObjectCap (arch_cap.ASIDPoolCap ap asid)) =
  (cap = cap.ArchObjectCap (arch_cap.ASIDPoolCap ap asid))"
  apply (rule iffI)
   prefer 2
   apply simp
  apply (clarsimp simp: weak_derived_def copy_of_def split: split_if_asm)
  apply (auto simp: same_object_as_def2 cap_master_cap_simps dest!: cap_master_cap_eqDs)
  done


lemmas weak_derived_ASIDPool [simp] = 
  weak_derived_ASIDPool1 weak_derived_ASIDPool2


lemma swap_of_caps_valid_arch_caps:
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
   apply (wp hoare_vcg_all_lift hoare_convert_imp[OF set_cap_vs_lookup_pages]
             hoare_vcg_disj_lift hoare_convert_imp[OF set_cap_caps_of_state]
             hoare_use_eq[OF set_cap_arch set_cap_obj_at_impossible[where P="\<lambda>x. x"]])
  apply (clarsimp simp: valid_arch_caps_def cte_wp_at_caps_of_state
              simp del: split_paired_Ex split_paired_All imp_disjL)
  apply (frule weak_derived_obj_refs[where dcap=c])
  apply (frule weak_derived_obj_refs[where dcap=c'])
  apply (frule weak_derived_pd_pt_asid[where c=c])
  apply (frule weak_derived_pd_pt_asid[where c=c'])
  apply (intro conjI)
     apply (simp add: valid_vs_lookup_def del: split_paired_Ex split_paired_All)
     apply (elim allEI)
     apply (intro impI disjCI2)
     apply (simp del: split_paired_Ex split_paired_All)
     apply (elim conjE)
     apply (erule exfEI[where f="id (a := b, b := a)"])
     apply (auto dest!: weak_derived_vs_cap_ref)[1]
    apply (simp add: valid_table_caps_def empty_table_caps_of
                del: split_paired_Ex split_paired_All imp_disjL)
   apply (simp add: unique_table_caps_def
               del: split_paired_Ex split_paired_All imp_disjL
                    split del: split_if)
   apply (erule allfEI[where f="id (a := b, b := a)"])
   apply (erule allfEI[where f="id (a := b, b := a)"])
   apply (clarsimp split del: split_if split: split_if_asm)
  apply (simp add: unique_table_refs_def
              del: split_paired_All split del: split_if)
  apply (erule allfEI[where f="id (a := b, b := a)"])
  apply (erule allfEI[where f="id (a := b, b := a)"])
  apply (clarsimp split del: split_if split: split_if_asm dest!:vs_cap_ref_to_table_cap_ref
                      dest!: weak_derived_table_cap_ref)
  done


lemma cap_swap_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps and
    cte_wp_at (weak_derived c) a and
    cte_wp_at (weak_derived c') b\<rbrace> 
     cap_swap c a c' b \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (rule hoare_pre)
   apply (subst bind_assoc[symmetric],
          rule hoare_seq_ext [rotated],
          rule swap_of_caps_valid_arch_caps)
   apply (wp | simp split del: split_if)+
  done


crunch v_ker_map[wp]: cap_swap "valid_kernel_mappings"


crunch eq_ker_map[wp]: cap_swap "equal_kernel_mappings"


lemma cap_swap_asid_map[wp]:
  "\<lbrace>valid_asid_map and
    cte_wp_at (weak_derived c) a and
    cte_wp_at (weak_derived c') b\<rbrace> 
     cap_swap c a c' b \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: cap_swap_def set_cdt_def valid_asid_map_def pd_at_asid_def)
  apply (rule hoare_pre)
   apply (wp set_cap_vs_lookup|simp
          |rule hoare_lift_Pf [where f=arch_state])+
  done


crunch only_idle [wp]: cap_swap only_idle


crunch global_pd_mappings[wp]: cap_swap "valid_global_pd_mappings"


crunch pspace_in_kernel_window[wp]: cap_swap "pspace_in_kernel_window"


lemma cap_swap_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window and
    cte_wp_at (weak_derived c) a and
    cte_wp_at (weak_derived c') b\<rbrace> 
     cap_swap c a c' b \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (rule hoare_pre)
   apply (wp | simp split del: split_if)+
  apply (auto dest!: cap_refs_in_kernel_windowD
               simp: cte_wp_at_caps_of_state weak_derived_cap_range)
  done


lemma cap_swap_valid_ioc[wp]:
  "\<lbrace>\<lambda>s. valid_ioc s \<and>
    cte_wp_at (weak_derived c) p s \<and>
    cte_wp_at (weak_derived c') p' s\<rbrace>
    cap_swap c p c' p'
   \<lbrace>\<lambda>_ s. valid_ioc s\<rbrace>"
  apply (simp add: cap_swap_def valid_ioc_def cte_wp_at_caps_of_state)
  apply (wp set_cdt_cos_ioc set_cap_caps_of_state2 | simp split del: split_if)+
  apply (cases p, cases p')
  apply fastforce
  done


crunch machine_state[wp]: cap_swap "\<lambda>s. P(machine_state s)"


lemma cap_swap_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace>  cap_swap c a c' b \<lbrace>\<lambda>rv. valid_machine_state\<rbrace>"
  apply (simp add: valid_machine_state_def in_user_frame_def)
  apply (wp cap_swap_typ_at
            hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_disj_lift)
  done

crunch valid_irq_states[wp]: cap_swap "valid_irq_states"

lemma cap_swap_invs[wp]:
  "\<lbrace>invs and ex_cte_cap_wp_to (appropriate_cte_cap c') a
         and ex_cte_cap_wp_to (appropriate_cte_cap c) b and
    valid_cap c and valid_cap c' and
    tcb_cap_valid c b and tcb_cap_valid c' a and
    cte_wp_at (weak_derived c) a and
    cte_wp_at (\<lambda>cc. is_untyped_cap cc \<longrightarrow> cc = c) a and 
    cte_wp_at (weak_derived c') b and
    cte_wp_at (\<lambda>cc. is_untyped_cap cc \<longrightarrow> cc = c') b and 
    K (a \<noteq> b \<and> \<not> is_master_reply_cap c \<and> \<not> is_master_reply_cap c')\<rbrace>
   cap_swap c a c' b \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  apply (wp cap_swap_replies cap_swap_reply_masters valid_arch_state_lift
            cap_swap_typ_at valid_irq_node_typ
         | simp
         | erule disjE
         | clarsimp simp: cte_wp_at_caps_of_state copy_of_cte_refs weak_derived_def
                          copy_obj_refs copy_of_zobj_refs copy_of_is_zombie
                          copy_of_cap_irqs
         | clarsimp simp: valid_global_refs_def valid_refs_def copy_of_cap_range
                          cte_wp_at_caps_of_state
                simp del: split_paired_Ex split_paired_All
         | rule conjI
         | fastforce dest!: valid_reply_caps_of_stateD)+
  done


lemma cap_swap_fd_invs[wp]:
  "\<lbrace>invs and ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) a
        and ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) b
        and (\<lambda>s. \<forall>c. tcb_cap_valid c a s)
        and (\<lambda>s. \<forall>c. tcb_cap_valid c b s)
        and cte_wp_at (\<lambda>c. \<not> is_master_reply_cap c) a
        and cte_wp_at (\<lambda>c. \<not> is_master_reply_cap c) b\<rbrace>
   cap_swap_for_delete a b \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp)
  apply (clarsimp)
  apply (strengthen cap_irqs_appropriate_strengthen, simp)
  apply (rule conjI, fastforce dest: cte_wp_at_valid_objs_valid_cap)
  apply (rule conjI, fastforce dest: cte_wp_at_valid_objs_valid_cap)
  apply (clarsimp simp: cte_wp_at_caps_of_state weak_derived_def)
  done


lemma final_cap_unchanged:
  assumes x: "\<And>P p. \<lbrace>cte_wp_at P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  assumes y: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>is_final_cap' cap\<rbrace> f \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  apply (simp only: is_final_cap'_def3 imp_conv_disj de_Morgan_conj)
  apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift x hoare_vcg_disj_lift
            valid_cte_at_neg_typ [OF y])
  done


lemmas set_cap_cte_wp_at_cases = set_cap_cte_wp_at[unfolded if_bool_eq_conj pred_conj_def conj_ac]


lemma cyclic_zombieD[dest!]:
  "cap_cyclic_zombie cap sl
    \<Longrightarrow> \<exists>p zb n. cap = cap.Zombie p zb n
        \<and> sl = (p, replicate (zombie_cte_bits zb) False)"
  by (cases cap, simp_all add: cap_cyclic_zombie_def)


lemma rec_del_abort_cases:
  "case args of FinaliseSlotCall sl ex \<Rightarrow> s \<turnstile> \<lbrace>\<top>\<rbrace>
     rec_del (FinaliseSlotCall sl ex)
   \<lbrace>\<lambda>rv s. (fst rv) \<or> (\<not> ex \<and> cte_wp_at (\<lambda>c. is_zombie c \<and> sl \<in> fst_cte_ptrs c) sl s)\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>
      | _ \<Rightarrow> True"
proof (induct rule: rec_del.induct)
  case (2 slot exposed)
  note wp = "2.hyps"[simplified rec_del_call.cases]
  show ?case
    apply (subst rec_del_simps_ext)
    apply (simp only: rec_del_call.cases split_def)
    apply wp
        apply (simp add: cte_wp_at_caps_of_state)
        apply (wp wp, assumption+)
         apply (wp irq_state_independent_AI | simp)+
      apply (rule hoare_strengthen_post)
       apply (rule finalise_cap_cases[where slot=slot])
      apply clarsimp
      apply (fastforce simp: fst_cte_ptrs_def)
     apply (simp add: is_final_cap_def | wp get_cap_wp)+
    done
qed (simp_all add: rec_del_fails)


lemma rec_del_delete_cases:
  "\<lbrace>\<top>\<rbrace>
     rec_del (CTEDeleteCall sl ex)
   \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. c = cap.NullCap \<or> \<not> ex \<and> is_zombie c \<and> sl \<in> fst_cte_ptrs c) sl s\<rbrace>,-"
  using rec_del_abort_cases [where args="FinaliseSlotCall sl ex"]
  apply (subst rec_del_simps_ext, simp add: split_def)
  apply wp
   apply (rule hoare_strengthen_post [OF empty_slot_deletes])
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule use_spec, rule spec_strengthen_postE)
   apply assumption
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma cap_delete_deletes:
  "\<lbrace>\<top>\<rbrace>
     cap_delete p
   \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) p\<rbrace>,-"
  unfolding cap_delete_def
  using rec_del_delete_cases[where sl=p and ex=True]
  apply (simp add: validE_R_def)
  apply wp
  apply simp
  done


primrec
  valid_rec_del_call :: "rec_del_call \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_rec_del_call (CTEDeleteCall slot exp) = \<top>"
| "valid_rec_del_call (FinaliseSlotCall slot exp) = \<top>"
| "valid_rec_del_call (ReduceZombieCall cap slot exp) =
       (cte_wp_at (op = cap) slot and is_final_cap' cap
            and K (is_zombie cap))"



lemma final_cap_same_objrefs:
  "\<lbrace>is_final_cap' cap and cte_wp_at (\<lambda>c. obj_refs cap \<inter> obj_refs c \<noteq> {}
                                          \<or> cap_irqs cap \<inter> cap_irqs c \<noteq> {}) ptr\<rbrace>
     set_cap cap ptr \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  apply (simp only: is_final_cap'_def3 pred_conj_def
                    cte_wp_at_caps_of_state)
  apply wp
  apply (clarsimp simp del: split_paired_Ex split_paired_All)
  apply (rule_tac x=ptr in exI)
  apply (subgoal_tac "(a, b) = ptr")
   apply clarsimp
  apply (erule_tac x="ptr" in allE)
  apply (fastforce simp: obj_irq_refs_Int)
  done


lemma cte_wp_at_weakenE_customised:
  "\<lbrakk>cte_wp_at P t s; \<And>c. \<lbrakk> P c; cte_wp_at (op = c) t s \<rbrakk> \<Longrightarrow> P' c\<rbrakk> \<Longrightarrow> cte_wp_at P' t s"
  by (clarsimp simp: cte_wp_at_def)


lemma final_cap_at_same_objrefs:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>c.  obj_refs c \<noteq> {} \<and> is_final_cap' c s) p s
      \<and> cte_wp_at (\<lambda>c. obj_refs cap = obj_refs c
                         \<and> cap_irqs cap = cap_irqs c) ptr s \<and> p \<noteq> ptr\<rbrace>
     set_cap cap ptr \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s\<rbrace>"
  apply (simp only: final_cap_at_eq cte_wp_at_conj)
  apply (simp add: cte_wp_at_caps_of_state)
  apply wp
  apply (clarsimp simp del: split_paired_All split_paired_Ex
                      simp: obj_irq_refs_Int obj_irq_refs_empty)
  apply fastforce
  done


lemma cap_swap_fd_final_cap_at_one_case:
  "\<lbrace>\<lambda>s. p \<noteq> p'' \<and> ((p = p') \<longrightarrow> cte_wp_at (\<lambda>c. is_final_cap' c s) p'' s)
     \<and> ((p \<noteq> p') \<longrightarrow> cte_wp_at (\<lambda>c. is_final_cap' c s) p s)\<rbrace>
   cap_swap_for_delete p' p''
  \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s\<rbrace>"
  apply (simp only: final_cap_at_eq cte_wp_at_conj)
  apply (simp add: cte_wp_at_caps_of_state)
  apply wp
  apply (cases "p = p'")
   apply (cases p', clarsimp)
  apply clarsimp
  apply (cases p', cases p'', clarsimp)
  done


lemma cap_swap_fd_cte_wp_at_one_case:
  "\<lbrace>\<lambda>s. p \<noteq> p'' \<and> ((p = p') \<longrightarrow> cte_wp_at P p'' s) \<and> ((p \<noteq> p') \<longrightarrow> cte_wp_at P p s)\<rbrace>
     cap_swap_for_delete p' p''
   \<lbrace>\<lambda>rv s. cte_wp_at P p s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply wp
  apply clarsimp
  done


lemma valid_cte_wp_at_prop:
  assumes x: "\<And>P p. \<lbrace>cte_wp_at P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  assumes y: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P' (cte_wp_at P p s)\<rbrace> f \<lbrace>\<lambda>rv s. P' (cte_wp_at P p s)\<rbrace>"
proof -
  have cte_wp_at_neg2:
    "\<And>P p s. (\<not> cte_wp_at P p s) = (\<not> cte_at p s \<or> cte_wp_at (\<lambda>c. \<not> P c) p s)"
    by (fastforce simp: cte_wp_at_def)
  have rev_iffI:
    "\<And>P Q. \<lbrakk> P \<Longrightarrow> Q; \<not> P \<Longrightarrow> \<not> Q \<rbrakk> \<Longrightarrow> P = Q"
    by fastforce
  show ?thesis
    apply (clarsimp simp: valid_def elim!: rsubst[where P=P'])
    apply (rule rev_iffI)
     apply (erule(1) use_valid [OF _ x])
    apply (subst cte_wp_at_neg2)
    apply (erule use_valid)
     apply (wp hoare_vcg_disj_lift x y valid_cte_at_neg_typ)
    apply (simp only: cte_wp_at_neg2[symmetric] simp_thms)
    done
qed


lemma final_cap_at_unchanged:
  assumes x: "\<And>P p. \<lbrace>cte_wp_at (\<lambda>c. P (obj_refs c) (cap_irqs c)) p\<rbrace> f
                       \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. P (obj_refs c) (cap_irqs c)) p\<rbrace>"
  assumes y: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s\<rbrace> f
                \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s\<rbrace>"
proof -
  have final_cap_at_eq':
    "\<And>p s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s =
    (\<exists>cp. cte_wp_at (\<lambda>c. obj_refs c = obj_refs cp \<and> cap_irqs c = cap_irqs cp) p s
              \<and> (obj_refs cp \<noteq> {} \<or> cap_irqs cp \<noteq> {})
       \<and> (\<forall>p'. (cte_at p' s \<and> p' \<noteq> p) \<longrightarrow>
                cte_wp_at (\<lambda>c. obj_refs cp \<inter> obj_refs c = {}
                               \<and> cap_irqs cp \<inter> cap_irqs c = {}) p' s))"
    apply (simp add: final_cap_at_eq cte_wp_at_def)
    apply (rule iffI)
     apply (clarsimp simp: obj_irq_refs_Int obj_irq_refs_empty)
     apply (rule exI, rule conjI, rule refl)
     apply clarsimp
    apply (clarsimp simp: obj_irq_refs_Int obj_irq_refs_empty)
    done
  show ?thesis
    apply (simp only: final_cap_at_eq' imp_conv_disj de_Morgan_conj)
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift x hoare_vcg_disj_lift
              valid_cte_at_neg_typ y)
    done
qed


lemma zombie_has_objrefs:
  "is_zombie c \<Longrightarrow> obj_refs c \<noteq> {}"
  by (case_tac c, simp_all add: is_zombie_def)


lemma word_same_bl_memo_unify_word_type:
  "\<lbrakk> of_bl xs = (of_bl ys :: ('a :: len) word); length xs = length ys;
     length xs \<le> len_of TYPE('a) \<rbrakk> \<Longrightarrow> xs = ys"
  apply (subst same_append_eq[symmetric])
  apply (rule word_bl.Abs_eqD)
    apply (subst of_bl_rep_False)+
    apply simp
   apply simp
   apply (erule le_add_diff_inverse2)
  apply simp
  done


lemma word_and_bl_proof:
  "\<lbrakk> invs s; kheap s x = Some (CNode sz cs);
     unat (of_bl y :: word32) = 0; unat (of_bl z :: word32) = 0;
     y \<in> dom cs; z \<in> dom cs \<rbrakk> \<Longrightarrow> y = z"
  apply (simp add: unat_eq_0)
  apply (frule invs_valid_objs, erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_cs_def
                        valid_cs_size_def well_formed_cnode_n_def)
  apply (rule word_same_bl_memo_unify_word_type[where 'a=32])
    apply simp
   apply simp
  apply (simp add: word_bits_def)
  done


lemma final_zombie_not_live:
  "\<lbrakk> is_final_cap' (cap.Zombie ptr b n) s; cte_wp_at (op = (cap.Zombie ptr b n)) p s;
     if_live_then_nonz_cap s \<rbrakk>
     \<Longrightarrow> \<not> obj_at live ptr s"
  apply clarsimp
  apply (drule(1) if_live_then_nonz_capD, simp)
  apply (clarsimp simp: ex_nonz_cap_to_def zobj_refs_to_obj_refs)
  apply (subgoal_tac "(a, ba) \<noteq> p")
   apply (clarsimp simp: is_final_cap'_def)
   apply (erule(1) obvious)
    apply (clarsimp simp: cte_wp_at_def is_zombie_def)+
  done


lemma suspend_ex_cte_cap[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace> IpcCancel_A.suspend t \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  apply (simp add: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state
              del: split_paired_Ex)
  apply (wp hoare_use_eq_irq_node [OF suspend_irq_node suspend_caps_of_state])
  apply (simp del: split_paired_Ex split_paired_All)
  apply (intro allI impI, erule exEI)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp: can_fast_finalise_def
                 split: cap.split_asm)
  done


lemma of_bl_eq_0:
  "\<lbrakk> of_bl xs = (0 :: ('a :: len) word); length xs \<le> len_of TYPE('a) \<rbrakk>
    \<Longrightarrow> \<exists>n. xs = replicate n False"
  apply (rule exI)
  apply (rule word_same_bl_memo_unify_word_type[where 'a='a])
    apply simp
   apply simp
  apply simp
  done


lemma cte_at_length:
  "\<lbrakk> cte_at p s; valid_objs s \<rbrakk> 
     \<Longrightarrow> length (snd p) < (word_bits - cte_level_bits)"
  unfolding cte_at_cases
  apply (erule disjE)
   apply clarsimp
   apply (drule cap_table_at_length[rotated, where oref="fst p"])
    apply (fastforce simp: obj_at_def is_cap_table_def)
   apply (clarsimp simp: well_formed_cnode_n_def)
   apply (drule(1) dom_eqD)
   apply clarsimp
  apply (clarsimp simp: tcb_cap_cases_def tcb_cnode_index_def to_bl_1
                        word_bits_def cte_level_bits_def)
  apply auto
  done


lemma unat_of_bl_nat_to_cref:
  "\<lbrakk> n < 2 ^ ln; ln < word_bits \<rbrakk>
    \<Longrightarrow> unat (of_bl (nat_to_cref ln n) :: word32) = n"
  apply (simp add: nat_to_cref_def word_bits_conv of_drop_to_bl
                   word_size)
  apply (subst less_mask_eq)
   apply (rule order_less_le_trans)
    apply (erule of_nat_mono_maybe[rotated])
    apply (rule power_strict_increasing)
     apply simp
    apply simp
   apply simp
  apply (rule unat_of_nat32)
  apply (erule order_less_trans)
  apply (rule power_strict_increasing)
   apply (simp add: word_bits_conv)
  apply simp
  done


lemma zombie_is_cap_toE_pre:
  "\<lbrakk> s \<turnstile> cap.Zombie ptr zbits n; invs s; m < n \<rbrakk>
     \<Longrightarrow> (ptr, nat_to_cref (zombie_cte_bits zbits) m) \<in> cte_refs (cap.Zombie ptr zbits n) irqn"
  apply (clarsimp simp add: valid_cap_def cap_aligned_def)
  apply (clarsimp split: option.split_asm)
   apply (simp add: unat_of_bl_nat_to_cref)
   apply (simp add: nat_to_cref_def word_bits_conv)
  apply (simp add: unat_of_bl_nat_to_cref)
  apply (simp add: nat_to_cref_def word_bits_conv)
  done


lemma zombie_is_cap_toE:
  "\<lbrakk> cte_wp_at (op = (cap.Zombie ptr zbits n)) p s; invs s; m < n;
               P (cap.Zombie ptr zbits n) \<rbrakk>
     \<Longrightarrow> ex_cte_cap_wp_to P (ptr, nat_to_cref (zombie_cte_bits zbits) m) s"
  unfolding ex_cte_cap_wp_to_def
  apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp)
  apply (intro exI, erule cte_wp_at_weakenE)
  apply clarsimp
  apply (drule(2) zombie_is_cap_toE_pre, simp)
  done


lemma zombie_is_cap_toE2:
  "\<lbrakk> cte_wp_at (op = (cap.Zombie ptr zbits n)) p s; 0 < n;
             P (cap.Zombie ptr zbits n) \<rbrakk>
     \<Longrightarrow> ex_cte_cap_wp_to P (ptr, replicate (zombie_cte_bits zbits) False) s"
  unfolding ex_cte_cap_wp_to_def
  apply (rule exI, erule cte_wp_at_weakenE)
  apply clarsimp
  done


lemma set_cap_emptyable[wp]:
  "\<not> is_master_reply_cap cap \<Longrightarrow> 
   \<lbrace>emptyable sl and cte_at p\<rbrace> set_cap cap p \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  apply (simp add: emptyable_def)
  apply (subst imp_conv_disj)+
  apply (wp hoare_vcg_disj_lift set_cap_typ_at set_cap_cte_wp_at
       | simp add: tcb_at_typ)+
  done


lemma set_cap_halted_if_tcb[wp]:
  "\<lbrace>halted_if_tcb t\<rbrace> set_cap cap p \<lbrace>\<lambda>rv. halted_if_tcb t\<rbrace>"
  apply (simp add: halted_if_tcb_def)
  apply (subst imp_conv_disj)+
  apply (wp hoare_vcg_disj_lift set_cap_typ_at | simp add: tcb_at_typ)+
  done


lemma valid_Zombie_n_less_cte_bits:
  "s \<turnstile> cap.Zombie p zb n \<Longrightarrow> n \<le> 2 ^ zombie_cte_bits zb"
  by (clarsimp simp: valid_cap_def split: option.split_asm)


lemma zombie_cte_bits_less:
  "s \<turnstile> cap.Zombie p zb m \<Longrightarrow> zombie_cte_bits zb < word_bits"
  by (clarsimp simp: valid_cap_def cap_aligned_def
              split: option.split_asm)


lemma nat_to_cref_replicate_Zombie:
  "\<lbrakk> nat_to_cref (zombie_cte_bits zb) n = replicate (zombie_cte_bits zb) False;
     s \<turnstile> cap.Zombie p zb m; n < m \<rbrakk>
     \<Longrightarrow> n = 0"
  apply (subgoal_tac "unat (of_bl (nat_to_cref (zombie_cte_bits zb) n)) = 0")
   apply (subst(asm) unat_of_bl_nat_to_cref)
     apply (drule valid_Zombie_n_less_cte_bits, simp)
    apply (erule zombie_cte_bits_less)
   apply simp
  apply simp
  done


lemma replicate_False_tcb_valid[simp]:
  "tcb_cap_valid cap (p, replicate n False) s"
  apply (clarsimp simp: tcb_cap_valid_def st_tcb_def2 tcb_at_def)
  apply (rule conjI)
   apply (clarsimp split: option.split)
   apply (frule tcb_cap_cases_length[OF domI])
   apply (clarsimp simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1)
  apply (cases n, simp_all add: tcb_cnode_index_def)
  done


lemma tcb_valid_nonspecial_cap:
  "\<lbrakk> caps_of_state s p = Some cap; valid_objs s;
       \<forall>ptr st. \<forall>(getF, setF, restr) \<in> ran tcb_cap_cases.
                    \<not> restr ptr st cap \<or> (\<forall>cap. restr ptr st cap);
       \<forall>ptr. (is_arch_cap cap \<or> cap = cap.NullCap) \<and>
             valid_ipc_buffer_cap cap ptr
                \<longrightarrow> valid_ipc_buffer_cap cap' ptr \<rbrakk>
      \<Longrightarrow> tcb_cap_valid cap' p s"
  apply (drule cte_wp_tcb_cap_valid[rotated])
   apply (erule caps_of_state_cteD)
  apply (clarsimp simp: tcb_cap_valid_def st_tcb_def2)
  apply (clarsimp split: option.split_asm)
  apply (rule conjI)
   apply (drule spec, drule spec, drule bspec, erule ranI)
   apply fastforce
  apply (clarsimp simp: eq_commute)
  done


lemma suspend_makes_halted[wp]:
  "\<lbrace>valid_objs\<rbrace> IpcCancel_A.suspend thread \<lbrace>\<lambda>_. st_tcb_at halted thread\<rbrace>"
  unfolding IpcCancel_A.suspend_def
  by (wp hoare_strengthen_post [OF sts_st_tcb_at]
    | clarsimp elim!: st_tcb_weakenE)+


lemma finalise_cap_makes_halted:
  "\<lbrace>invs and valid_cap cap and (\<lambda>s. ex = is_final_cap' cap s)
         and cte_wp_at (op = cap) slot\<rbrace>
    finalise_cap cap ex
   \<lbrace>\<lambda>rv s. \<forall>t \<in> obj_refs (fst rv). halted_if_tcb t s\<rbrace>"
  apply (case_tac cap, simp_all)
            apply (wp
                 | clarsimp simp: o_def valid_cap_def cap_table_at_typ
                                  is_tcb obj_at_def 
                 | clarsimp simp: halted_if_tcb_def
                           split: option.split
                 | intro impI conjI
                 | rule hoare_drop_imp)+
   apply (fastforce simp: st_tcb_at_def obj_at_def is_tcb
                  dest!: final_zombie_not_live)
  apply (case_tac arch_cap, simp_all add: arch_finalise_cap_def)
      apply (wp
           | clarsimp simp: valid_cap_def split: option.split bool.split
           | intro impI conjI)+
  done


lemma empty_slot_emptyable[wp]:
  "\<lbrace>emptyable sl and cte_at slot'\<rbrace> empty_slot slot' opt \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_weaken_pre)
   apply (simp add: emptyable_def)
   apply (subst imp_conv_disj)+
   apply (wp hoare_vcg_disj_lift | simp add: tcb_at_typ)+
  apply (simp add: is_cap_simps emptyable_def tcb_at_typ)
  done


crunch emptyable[wp]: blocked_ipc_cancel "emptyable sl"
  (ignore: set_thread_state wp: emptyable_lift sts_st_tcb_at_cases static_imp_wp)

crunch emptyable[wp]: async_ipc_cancel "emptyable sl"
  (ignore: set_thread_state wp: emptyable_lift sts_st_tcb_at_cases static_imp_wp)


lemma cap_delete_one_emptyable[wp]:
  "\<lbrace>invs and emptyable sl and cte_at sl'\<rbrace> cap_delete_one sl' \<lbrace>\<lambda>_. emptyable sl\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def is_final_cap_def)
  apply (wp hoare_strengthen_post [OF get_cap_inv])
  apply simp
  done


lemmas tcb_at_cte_at_2 = tcb_at_cte_at [where ref="tcb_cnode_index 2",
                                        simplified dom_tcb_cap_cases]


declare thread_set_Pmdb [wp]


lemma reply_ipc_cancel_emptyable[wp]:
  "\<lbrace>invs and emptyable sl and valid_mdb\<rbrace> reply_ipc_cancel ptr \<lbrace>\<lambda>_. emptyable sl\<rbrace>"
  apply (simp add: reply_ipc_cancel_def)
  apply (wp select_wp select_inv hoare_drop_imps | simp add: Ball_def)+
    apply (wp hoare_vcg_all_lift hoare_convert_imp thread_set_Pmdb
              thread_set_invs_trivial thread_set_emptyable thread_set_cte_at
         | simp add: tcb_cap_cases_def descendants_of_cte_at)+
  done


crunch emptyable[wp]: ipc_cancel "emptyable sl"


lemma suspend_emptyable[wp]: 
  "\<lbrace>invs and emptyable sl and valid_mdb\<rbrace> IpcCancel_A.suspend l \<lbrace>\<lambda>_. emptyable sl\<rbrace>"
  apply (simp add: IpcCancel_A.suspend_def)
  apply (wp|simp)+
  apply (wp emptyable_lift sts_st_tcb_at_cases)
    apply simp
   apply (wp set_thread_state_cte_wp_at | simp)+
  done


crunch emptyable[wp]: do_machine_op "emptyable sl"
  (lift: emptyable_lift)

crunch emptyable[wp]: set_irq_state "emptyable sl"
  (lift: emptyable_lift)


declare get_irq_slot_real_cte [wp]

lemma get_irq_slot_cte_at[wp]:
  "\<lbrace>invs\<rbrace> get_irq_slot irq \<lbrace>cte_at\<rbrace>"
  by wp

crunch emptyable[wp]: deleting_irq_handler "emptyable sl"
  (simp: crunch_simps lift: emptyable_lift 
     wp: crunch_wps suspend_emptyable)

crunch emptyable[wp]: arch_finalise_cap "emptyable sl"
  (simp: crunch_simps lift: emptyable_lift 
     wp: crunch_wps suspend_emptyable)

lemma finalise_cap_emptyable[wp]:
"\<lbrace>invs and emptyable sl\<rbrace> finalise_cap a b \<lbrace>\<lambda>_. emptyable sl\<rbrace>"
  apply (case_tac a,simp_all)
   apply (wp|clarsimp|intro conjI)+
  done

(* Why the following is no longer true ?
crunch emptyable[wp]: finalise_cap "emptyable sl"
  (simp: crunch_simps lift: emptyable_lift 
     wp: crunch_wps suspend_emptyable)
*)

lemma cap_swap_for_delete_emptyable[wp]:
  "\<lbrace>emptyable sl and emptyable sl'\<rbrace> cap_swap_for_delete sl' sl \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  apply (simp add: emptyable_def cap_swap_for_delete_def cap_swap_def tcb_at_typ)
  apply (rule hoare_pre)
   apply (subst imp_conv_disj)+
   apply (wp hoare_vcg_disj_lift set_cdt_typ_at set_cap_typ_at | simp split del: split_if)+
  done


lemma finalise_cap_not_reply_master:
  "(Inr rv, s') \<in> fst (liftE (finalise_cap cap sl) s) \<Longrightarrow>
   \<not> is_master_reply_cap (fst rv)"
  by (case_tac cap, auto simp: is_cap_simps in_monad liftM_def 
                               arch_finalise_cap_def
                        split: split_if_asm arch_cap.split_asm bool.split_asm option.split_asm)


crunch cte_at_pres[wp]: empty_slot "cte_at sl"


lemma nat_to_cref_0_replicate:
  "\<And>n. n < word_bits \<Longrightarrow> nat_to_cref n 0 = replicate n False"
  apply (subgoal_tac "nat_to_cref n (unat (of_bl (replicate n False))) = replicate n False")
   apply simp
  apply (rule nat_to_cref_unat_of_bl')
   apply (simp add: word_bits_def)
  apply simp
  done


lemma cte_wp_at_emptyableD:
  "\<And>P. \<lbrakk> cte_wp_at (\<lambda>c. c = cap) p s; valid_objs s; \<And>cap. P cap \<Longrightarrow> \<not> is_master_reply_cap cap \<rbrakk> \<Longrightarrow>
   P cap \<longrightarrow> emptyable p s"
  apply (simp add: emptyable_def)
  apply (clarsimp simp add: obj_at_def is_tcb)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: cte_wp_at_cases valid_obj_def valid_tcb_def
                        tcb_cap_cases_def st_tcb_at_def obj_at_def
                 split: Structures_A.thread_state.splits)
  done


lemma cte_wp_at_not_reply_master:
  "\<And>a b s. \<lbrakk> tcb_at a s \<longrightarrow> b \<noteq> tcb_cnode_index 2; cte_at (a, b) s;
              valid_objs s; valid_reply_masters s \<rbrakk>
   \<Longrightarrow> cte_wp_at (\<lambda>c. \<not> is_master_reply_cap c) (a, b) s"
  by (fastforce simp: valid_reply_masters_def cte_wp_at_caps_of_state
                     is_cap_simps valid_cap_def
               dest: caps_of_state_valid_cap)


declare finalise_cap_cte_cap_to [wp]


lemma appropriate_Zombie:
  "\<And>ptr zbits n. appropriate_cte_cap (cap.Zombie ptr zbits n)
                     = (\<lambda>cap. cap_irqs cap = {})"
  by (rule ext, simp add: appropriate_cte_cap_def)


lemma no_cap_to_obj_with_diff_ref_eqE:
  "\<lbrakk> no_cap_to_obj_with_diff_ref cap S s;
        obj_refs cap' = obj_refs cap; table_cap_ref cap' = table_cap_ref cap;
        S \<subseteq> S' \<rbrakk>
      \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' S' s"
  by (auto simp add: no_cap_to_obj_with_diff_ref_def Ball_def)


lemma context_conjI': "\<lbrakk>P; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q \<and> P"
  apply simp
done


lemma rec_del_invs'':
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
                             \<and> (\<forall>irq. snd rv = Some irq \<longrightarrow>
                                   cap.IRQHandlerCap irq \<notin> ran ((caps_of_state s) (sl \<mapsto> cap.NullCap)))
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
      apply (rule "1.hyps"[simplified rec_del_call.cases slot_rdcall.simps])
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
       apply (wp "2.hyps", assumption+)
         apply (wp preemption_point_Q | simp)+
         apply (wp preemption_point_inv, simp+)
         apply (wp preemption_point_Q)
         apply ((wp preemption_point_inv irq_state_independent_A_conjI irq_state_independent_AI 
                    emptyable_irq_state_independent invs_irq_state_independent
               | simp add: valid_rec_del_call_def irq_state_independent_A_def)+)[1]
        apply (simp(no_asm))
        apply (rule spec_strengthen_postE)
        apply (rule "2.hyps"[simplified rec_del_call.cases slot_rdcall.simps conj_assoc], assumption+)
       apply (simp add: cte_wp_at_eq_simp
                | wp replace_cap_invs set_cap_sets final_cap_same_objrefs
                     set_cap_cte_cap_wp_to static_imp_wp
                | erule finalise_cap_not_reply_master)+
       apply (wp hoare_vcg_const_Ball_lift)
      apply (rule hoare_strengthen_post)
       apply (rule_tac Q="\<lambda>fin s. Q s \<and> invs s \<and> replaceable s slot (fst fin) rv
                                 \<and> cte_wp_at (op = rv) slot s \<and> s \<turnstile> (fst fin)
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
       apply (clarsimp simp: cap_irq_opt_def cte_wp_at_def
                      split: cap.split_asm split_if_asm
                      elim!: ranE dest!: caps_of_state_cteD)
       apply (drule(2) final_cap_duplicate_irq)
         apply simp+
      apply clarsimp
      apply (rule conjI)
       apply clarsimp
       apply (subst replaceable_def)
       apply (clarsimp simp: is_cap_simps tcb_cap_valid_NullCapD
                             no_cap_to_obj_with_diff_ref_Null
                        del: disjCI)
       apply (thin_tac "appropriate_cte_cap ?a = appropriate_cte_cap ?b")
       apply (rule conjI)
        apply (clarsimp simp: replaceable_def)
        apply (erule disjE)
         apply (simp only: zobj_refs.simps mem_simps)
        apply clarsimp+
       apply (drule sym, simp)
       apply (drule sym, simp)
       apply clarsimp
       apply (simp add: unat_eq_0)
       apply (drule of_bl_eq_0)
        apply (drule zombie_cte_bits_less, simp add: word_bits_def)
       apply (clarsimp simp: cte_wp_at_caps_of_state)
      apply (drule_tac s="appropriate_cte_cap ?c" in sym)
      apply (clarsimp simp: is_cap_simps appropriate_Zombie)
     apply (simp add: is_final_cap_def)
     apply wp
    apply (clarsimp simp: cte_wp_at_eq_simp)
    apply (rule conjI)
     apply (clarsimp simp: cte_wp_at_caps_of_state replaceable_def)
    apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp+)
    apply (frule invs_valid_asid_table)
    apply (clarsimp simp add: invs_def valid_state_def 
      invs_valid_objs invs_psp_aligned)
    apply (drule(1) if_unsafe_then_capD, clarsimp+)
    done
next
  have replicate_helper:
    "\<And>x n. True \<in> set x \<Longrightarrow> replicate n False \<noteq> x"
   by (clarsimp simp: replicate_not_True)
  case (3 ptr bits n slot s)
  show ?case
    apply (simp add: rec_del_call.cases simp_thms)
    apply wp
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
      apply (rule_tac Q="\<lambda>rv s. Q s \<and> invs s \<and> cte_wp_at (\<lambda>cap. cap = rv) slot s
                             \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap
                                        \<or> \<not> False \<and> is_zombie cap
                                            \<and> (ptr, nat_to_cref (zombie_cte_bits bits) n)
                                                 \<in> fst_cte_ptrs cap)
                                    (ptr, nat_to_cref (zombie_cte_bits bits) n) s
                             \<and> \<not> cap_removeable (cap.Zombie ptr bits (Suc n)) slot"
                  in hoare_post_imp)
       apply (thin_tac "(?a, ?b) \<in> fst ?c")
       apply clarsimp
       apply (frule cte_wp_at_emptyableD, clarsimp, assumption)
       apply (rule conjI[rotated], (clarsimp simp: is_cap_simps)+)
       apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp+)
       apply (frule if_unsafe_then_capD, clarsimp+)
       apply (rule conjI)
        apply (frule zombies_finalD, (clarsimp simp: is_cap_simps)+)
        apply (clarsimp simp: cte_wp_at_caps_of_state)
        apply (erule disjE[where P="val = cap.NullCap", standard])
         apply (clarsimp simp: replaceable_def cap_range_def is_cap_simps
                               obj_irq_refs_subset vs_cap_ref_def)
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
         apply (erule disjE[where Q="val = slot", standard])
          apply (clarsimp simp: cte_wp_at_caps_of_state)
          apply (erule notE[rotated, where P="val = Some cap.NullCap", standard])
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
                              obj_irq_refs_Int)
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
      apply (rule "4.hyps"[simplified rec_del_call.cases slot_rdcall.simps simp_thms pred_conj_def])
      apply (simp add: in_monad)
     apply simp
    apply (clarsimp simp: halted_emptyable)
    apply (erule(1) zombie_is_cap_toE)
     apply simp
    apply simp
    done
qed

lemmas rec_del_invs' = rec_del_invs''[where Q=\<top>,simplified hoare_post_taut pred_conj_def simp_thms, OF TrueI TrueI TrueI TrueI, simplified]

lemma real_cte_at_not_tcb:
  "real_cte_at sl s \<Longrightarrow> \<not> tcb_at (fst sl) s"
  apply (simp add: tcb_at_typ obj_at_def)
  apply (clarsimp  simp: is_cap_table_def a_type_def split: split_if_asm
    Structures_A.kernel_object.split)[1]
  done

lemma rec_del_invs:
 "\<lbrace>invs and valid_rec_del_call args
      and (\<lambda>s. \<not> exposed_rdcall args
                 \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall args) s)
      and emptyable (slot_rdcall args)
      and (\<lambda>s. case args of ReduceZombieCall cap sl ex \<Rightarrow>
                         \<not> cap_removeable cap sl
                         \<and> (\<forall>t\<in>obj_refs cap. halted_if_tcb t s)
                  | _ \<Rightarrow> True)\<rbrace>
    rec_del args
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule validE_valid)
  apply (rule hoare_post_impErr)
  apply (rule hoare_pre)
    apply (rule use_spec)
    apply (rule rec_del_invs')
   apply simp+
  done

lemma cap_delete_invs[wp]:
  "\<lbrace>invs and emptyable ptr\<rbrace>
     cap_delete ptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding cap_delete_def
  apply (rule hoare_pre, wp rec_del_invs)
  apply simp
  done

lemma cap_delete_tcb[wp]:
 "\<lbrace>tcb_at t\<rbrace> cap_delete ptr \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  unfolding cap_delete_def
  by (simp add: tcb_at_typ | wp rec_del_typ_at)+

lemma cap_delete_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> cap_delete p \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  unfolding cap_delete_def
  by (wp valid_cap_typ rec_del_typ_at | simp)+


lemma cap_delete_cte_at:
  "\<lbrace>cte_at c\<rbrace> cap_delete p \<lbrace>\<lambda>_. cte_at c\<rbrace>"
  unfolding cap_delete_def by (wp rec_del_cte_at | simp)+


lemma cap_delete_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> cap_delete cref \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  unfolding cap_delete_def by (wp rec_del_typ_at | simp)+


lemma cap_swap_fd_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> cap_swap_for_delete sl sl' \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding cap_swap_for_delete_def
  by (wp, simp)


declare if_cong[cong]


lemma cases2 [case_names pos_pos neg_pos pos_neg neg_neg]:
  "\<lbrakk> \<lbrakk>p; q\<rbrakk> \<Longrightarrow> R; \<lbrakk>\<not> p; q\<rbrakk> \<Longrightarrow> R; \<lbrakk>p; \<not> q\<rbrakk> \<Longrightarrow> R; \<lbrakk>\<not> p; \<not> q\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by auto

definition
  rpo_measure :: "'a \<Rightarrow> ('a option \<times> nat) option \<Rightarrow> nat"
where
 "rpo_measure x v \<equiv> case v of Some (y, n) \<Rightarrow> (if y = Some x then n - 1 else n)"


lemma rpo_measure_simps[simp]:
  "rpo_measure x (Some (y, n)) = (if y = Some x then n - 1 else n)"
  by (simp add: rpo_measure_def)

definition
  revoke_progress_ord :: "('a \<rightharpoonup> 'a option \<times> nat) \<Rightarrow> ('a \<rightharpoonup> 'a option \<times> nat) \<Rightarrow> bool"
where
 "revoke_progress_ord mapa mapb \<equiv> (mapa = mapb)
     \<or> (mapb, mapa) \<in> measure (\<lambda>mp. setsum (\<lambda>x. rpo_measure x (mp x)) (dom mp))"


lemma rpo_trans:
  "\<lbrakk> revoke_progress_ord mapa mapb; revoke_progress_ord mapb mapc \<rbrakk>
     \<Longrightarrow> revoke_progress_ord mapa mapc"
  apply (simp add: revoke_progress_ord_def)
  apply (elim disjE, simp_all)
  done


interpretation mult_is_add: comm_monoid_mult "op +" "0::'a::comm_monoid_add"
    by (unfold_locales) (auto simp: field_simps)


lemma fold_Int_sub:
  assumes "finite S" "finite T"
  shows "setsum (f :: 'a \<Rightarrow> nat) (S \<inter> T)
          = setsum f T - setsum f (T - S)"
proof -
  from assms setsum_Un_disjoint[where A="S \<inter> T" and B="T - S" and g=f]
  show ?thesis
  apply simp
  apply (drule meta_mp)
   apply blast
  apply (subgoal_tac "S \<inter> T \<union> (T - S) = T")
   apply simp
  apply blast
  done
qed


lemma rpo_delta:
  assumes x: "\<And>x. x \<notin> S \<Longrightarrow> mapa x = mapb x"
  assumes F: "finite S" "finite (dom mapa)" "finite (dom mapb)"
  assumes y:
    "(mapb, mapa) \<in> measure (\<lambda>mp. setsum (\<lambda>x. rpo_measure x (mp x)) (S \<inter> dom mp))"
  shows "revoke_progress_ord mapa mapb"
proof -
  have P: "(dom mapa - S) = (dom mapb - S)"
    by (fastforce simp: x)
  have Q: "setsum (\<lambda>x. rpo_measure x (mapa x)) (dom mapa - S)
            = setsum (\<lambda>x. rpo_measure x (mapb x)) (dom mapb - S)"
    apply (rule setsum.cong)
     apply (simp add: P)
    apply (simp add: x)
    done
  show ?thesis using y
    apply (simp add: revoke_progress_ord_def)
    apply (rule disjI2)
    apply (fastforce simp: fold_Int_sub F Q)
    done
qed


definition
  cap_to_rpo :: "cap \<Rightarrow> cslot_ptr option \<times> nat"
where
 "cap_to_rpo cap \<equiv> case cap of
     cap.NullCap \<Rightarrow> (None, 0)
   | cap.Zombie p zb n \<Rightarrow> (Some (p, replicate (zombie_cte_bits zb) False), 2)
   | _ \<Rightarrow> (None, 3)"


lemmas caps_of_state_set_finite'
   = cte_wp_at_set_finite[simplified cte_wp_at_caps_of_state]
    

lemmas caps_of_state_set_finite
   = caps_of_state_set_finite'
     caps_of_state_set_finite'[where P="\<top>\<top>", simplified]


lemma empty_slot_rvk_prog:
  "\<lbrace>\<lambda>s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)\<rbrace>
     empty_slot sl opt
   \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)\<rbrace>"
  apply (simp add: empty_slot_def)
  apply (rule hoare_pre)
   apply (wp opt_return_pres_lift | simp split del: split_if)+
   apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (erule rpo_trans)
  apply (rule rpo_delta[where S="{sl}"],
         simp_all add: dom_def caps_of_state_set_finite exception_set_finite)
  apply (case_tac cap, simp_all add: cap_to_rpo_def)
  done


lemma rvk_prog_update_strg:
  "revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)
        \<and> cte_wp_at (\<lambda>cp. cap_to_rpo cp = cap_to_rpo cap
                         \<or> rpo_measure p (Some (cap_to_rpo cp))
                             > rpo_measure p (Some (cap_to_rpo cap))) p s
      \<longrightarrow> revoke_progress_ord m (option_map cap_to_rpo \<circ> ((caps_of_state s) (p \<mapsto> cap)))"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (erule disjE)
   apply (erule rsubst[where P="\<lambda>mp. revoke_progress_ord m mp"])
   apply (rule ext, simp)
  apply (erule rpo_trans)
  apply (rule rpo_delta[where S="{p}"],
         simp_all add: dom_def caps_of_state_set_finite)
  apply (rule exception_set_finite)
  apply (rule finite_subset [OF _ caps_of_state_set_finite(2)[where s=s]])
  apply clarsimp
  done


lemma cap_swap_fd_rvk_prog:
  "\<lbrace>\<lambda>s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)
           \<and> cte_wp_at (\<lambda>cp. cap_to_rpo cp = (Some p1, 2) \<and> is_final_cap' cp s) p2 s\<rbrace>
     cap_swap_for_delete p1 p2
   \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)\<rbrace>"
  apply (simp add: cap_swap_for_delete_def cap_swap_def)
  apply (wp get_cap_wp | simp split del: split_if)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (erule rpo_trans)
  apply (rule rpo_delta[where S="{p1, p2}"],
         simp_all add: caps_of_state_set_finite exception_set_finite
                       dom_def)
  apply (clarsimp simp: is_final_cap'_def2)
  apply (frule spec[where x="fst p1"], drule spec[where x="snd p1"])
  apply (drule spec[where x="fst p2"], drule spec[where x="snd p2"])
  apply (clarsimp simp: cap_to_rpo_def split: cap.split_asm)
  apply (simp split: cap.split)
  apply (clarsimp simp: cte_wp_at_caps_of_state obj_irq_refs_empty)
  apply (drule iffD1)
   apply (simp add: obj_irq_refs_Int)
  apply simp
  done


lemmas empty_slot_rvk_prog' = empty_slot_rvk_prog[unfolded o_def]


crunch rvk_prog: ipc_cancel "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map cap_to_rpo (caps_of_state s x))"
  (simp: crunch_simps o_def unless_def is_final_cap_def tcb_cap_cases_def
     wp: hoare_drop_imps empty_slot_rvk_prog' select_wp
         thread_set_caps_of_state_trivial)

crunch rvk_prog: ep_cancel_all "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map cap_to_rpo (caps_of_state s x))"
  (simp: crunch_simps o_def unless_def is_final_cap_def
     wp: crunch_wps empty_slot_rvk_prog' select_wp)

crunch rvk_prog: aep_cancel_all "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map cap_to_rpo (caps_of_state s x))"
  (simp: crunch_simps o_def unless_def is_final_cap_def
     wp: crunch_wps empty_slot_rvk_prog' select_wp)

crunch rvk_prog: suspend "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map cap_to_rpo (caps_of_state s x))"
  (simp: crunch_simps o_def unless_def is_final_cap_def
     wp: crunch_wps empty_slot_rvk_prog' select_wp)

crunch rvk_prog: deleting_irq_handler "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map cap_to_rpo (caps_of_state s x))"
  (simp: crunch_simps o_def unless_def is_final_cap_def
     wp: crunch_wps empty_slot_rvk_prog' select_wp)

lemma finalise_cap_rvk_prog:
   "\<lbrace>\<lambda>s. revoke_progress_ord m (\<lambda>x. map_option cap_to_rpo (caps_of_state s x))\<rbrace>
   finalise_cap a b 
   \<lbrace>\<lambda>_ s. revoke_progress_ord m (\<lambda>x. map_option cap_to_rpo (caps_of_state s x))\<rbrace>"
  apply (case_tac a,simp_all add:liftM_def)
    apply (wp ep_cancel_all_rvk_prog aep_cancel_all_rvk_prog
      suspend_rvk_prog deleting_irq_handler_rvk_prog
      | clarsimp simp:is_final_cap_def comp_def)+
  done

lemmas rdcall_simps = rec_del_call.simps exposed_rdcall.simps slot_rdcall.simps


lemma rec_del_rvk_prog:
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
        apply (wp wp, assumption+)
          apply ((wp preemption_point_inv | simp)+)[1]
         apply (simp(no_asm))
         apply (rule wp, assumption+)
        apply (wp final_cap_same_objrefs
                  set_cap_cte_wp_at_cases
                   | simp)+
       apply (rule hoare_strengthen_post)
        apply (rule_tac Q="\<lambda>fc s. cte_wp_at (op = rv) sl s
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
       apply (case_tac rv, simp_all add: cap_to_rpo_def is_cap_simps)[1]
       apply (case_tac arch_cap, simp_all)[1]
      apply (simp add: is_final_cap_def, wp)
     apply (simp, wp get_cap_wp)
    apply (clarsimp simp: o_def)
    done
next
  case (3 ptr bits n slot s)
  show ?case
    apply (simp add: rec_del.simps)
    apply (fold o_def)
    apply (rule hoare_pre_spec_validE)
     apply (simp del: o_apply | wp_once cap_swap_fd_rvk_prog)+
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


lemma cap_delete_rvk_prog:
  "\<lbrace>\<lambda>s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)\<rbrace>
     cap_delete ptr
   \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)\<rbrace>,-"
  unfolding cap_delete_def validE_R_def
  apply (wp | simp)+
  apply (rule hoare_pre,
         rule use_spec)
   apply (rule rec_del_rvk_prog)
  apply simp
  done

lemma set_cap_id:
  "cte_wp_at (op = c) p s \<Longrightarrow> set_cap c p s = ({((),s)}, False)"
  apply (clarsimp simp: cte_wp_at_cases)
  apply (cases p)
  apply (erule disjE)
   apply clarsimp
   apply (simp add: set_cap_def get_object_def bind_assoc exec_gets)
   apply (rule conjI)
    apply (clarsimp simp: set_object_def exec_get put_def)
    apply (cases s)
    apply simp
    apply (rule ext)
    apply auto[1]
   apply clarsimp
  apply clarsimp
  apply (simp add: set_cap_def get_object_def bind_assoc
                   exec_gets set_object_def exec_get put_def)
  apply (clarsimp simp: tcb_cap_cases_def
                 split: split_if_asm,
         simp_all add: map_upd_triv)
  done


declare Inr_in_liftE_simp[simp]


lemma get_cap_fail_or_not:
  "fst (get_cap slot s) \<noteq> {} \<Longrightarrow> snd (get_cap slot s) = False"
  by (clarsimp elim!: nonemptyE dest!: get_cap_det)


function(sequential) red_zombie_will_fail :: "cap \<Rightarrow> bool"
 where
  "red_zombie_will_fail (cap.Zombie ptr zb 0) = True"
| "red_zombie_will_fail (cap.Zombie ptr zb (Suc n)) = False"
| "red_zombie_will_fail cap = True"
  apply simp_all
  apply (case_tac x)
            prefer 11
            apply (case_tac nat, simp_all)[1]
             apply fastforce+
  done

termination red_zombie_will_fail
  by (rule red_zombie_will_fail.termination [OF Wellfounded.wf_empty])


lemma rec_del_emptyable:
 "\<lbrace>invs and valid_rec_del_call args
      and (\<lambda>s. \<not> exposed_rdcall args
                 \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall args) s)
      and emptyable (slot_rdcall args)
      and (\<lambda>s. case args of ReduceZombieCall cap sl ex \<Rightarrow>
                         \<not> cap_removeable cap sl
                         \<and> (\<forall>t\<in>obj_refs cap. halted_if_tcb t s)
                  | _ \<Rightarrow> True)\<rbrace>
    rec_del args
  \<lbrace>\<lambda>rv. emptyable (slot_rdcall args)\<rbrace>, -"
  apply (rule validE_validE_R)
  apply (rule hoare_post_impErr)
  apply (rule hoare_pre)
    apply (rule use_spec)
    apply (rule rec_del_invs')
   apply simp+
  done

lemma reduce_zombie_cap_to:
  "\<lbrace>invs and valid_rec_del_call (ReduceZombieCall cap slot exp) and
       emptyable slot and
       (\<lambda>s. \<not> exp \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s) and
       K (\<not> cap_removeable cap slot) and
       (\<lambda>s. \<forall>t\<in>obj_refs cap. halted_if_tcb t s)\<rbrace>
      rec_del (ReduceZombieCall cap slot exp)
   \<lbrace>\<lambda>rv s. \<not> exp \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s\<rbrace>, -"
  apply (rule validE_validE_R)
  apply (rule hoare_post_impErr)
    apply (rule hoare_pre)
     apply (rule use_spec)
     apply (rule rec_del_invs')
    apply simp+
  done


lemma cte_at_replicate_zbits:
  "\<lbrakk> s \<turnstile> cap.Zombie oref zb n \<rbrakk> \<Longrightarrow> cte_at (oref, replicate (zombie_cte_bits zb) False) s"
  apply (clarsimp simp: valid_cap_def obj_at_def is_tcb is_cap_table
                 split: option.split_asm)
   apply (rule cte_wp_at_tcbI, simp)
    apply (fastforce simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1)
   apply simp
  apply (subgoal_tac "replicate a False \<in> dom cs")
   apply safe[1]
   apply (rule cte_wp_at_cteI, fastforce)
     apply (simp add: well_formed_cnode_n_def length_set_helper)
    apply simp
   apply simp
  apply (clarsimp simp: well_formed_cnode_n_def)
  done


lemma reduce_zombie_cap_somewhere:
  "\<lbrace>\<lambda>s. \<not> exp \<longrightarrow> (\<exists>oref cref. cte_wp_at P (oref, cref) s)\<rbrace>
     rec_del (ReduceZombieCall cap slot exp)
   \<lbrace>\<lambda>rv s. \<not> exp \<longrightarrow> (\<exists>oref cref. cte_wp_at P (oref, cref) s)\<rbrace>"
  apply (cases exp, simp_all, wp)
  apply (cases cap, simp_all add: rec_del_fails)
  apply (case_tac nat, simp_all add: rec_del_simps_ext)
  apply (simp add: cte_wp_at_caps_of_state)
  apply wp
  apply safe
  apply (rule_tac x="fst ((id ((word, replicate (zombie_cte_bits option) False) := slot,
                            slot := (word, replicate (zombie_cte_bits option) False))) (oref, cref))"
             in exI)
  apply (rule_tac x="snd ((id ((word, replicate (zombie_cte_bits option) False) := slot,
                            slot := (word, replicate (zombie_cte_bits option) False))) (oref, cref))"
             in exI)
  apply fastforce
  done


lemma set_cap_cap_somewhere:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cp. P (fst slot) (snd slot) cp \<longrightarrow> P (fst slot) (snd slot) cap) slot s
         \<and> (\<exists>oref cref. cte_wp_at (P oref cref) (oref, cref) s)\<rbrace>
     set_cap cap slot
   \<lbrace>\<lambda>rv s. \<exists>oref cref. cte_wp_at (P oref cref) (oref, cref) s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply wp
  apply clarsimp
  apply (rule_tac x=oref in exI)
  apply (rule_tac x=cref in exI)
  apply fastforce
  done


lemma rec_del_ReduceZombie_emptyable:
  "\<lbrace>invs
      and (cte_wp_at (op = cap) slot and is_final_cap' cap
      and (\<lambda>y. is_zombie cap)) and
         (\<lambda>s. \<not> ex \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s) and
         emptyable slot and
         (\<lambda>s. \<not> cap_removeable cap slot \<and> (\<forall>t\<in>obj_refs cap. halted_if_tcb t s))\<rbrace>
   rec_del (ReduceZombieCall cap slot ex) \<lbrace>\<lambda>rv. emptyable slot\<rbrace>, -"
  by (rule rec_del_emptyable [where args="ReduceZombieCall cap slot ex", simplified])


text {* The revoke function and its properties are
        slightly easier to deal with than the delete
        function. However, its termination argument
        is complex, requiring that the delete function
        reduces the number of non-null capabilities. *}
definition
  cap_revoke_recset :: "((cslot_ptr \<times> 'z::state_ext state) \<times> (cslot_ptr \<times> 'z::state_ext state)) set"
where
 "cap_revoke_recset \<equiv> measure (\<lambda>(sl, s). (\<lambda>mp. setsum (\<lambda>x. rpo_measure x (mp x)) (dom mp))
                                   (option_map cap_to_rpo \<circ> caps_of_state s))"


lemma wf_cap_revoke_recset:
  "wf cap_revoke_recset"
  by (simp add: cap_revoke_recset_def)


lemma rpo_sym:
  "revoke_progress_ord m m"
  by (simp add: revoke_progress_ord_def)

lemma in_select_ext_weak: "(a,b) \<in> fst (select_ext f S s)  \<Longrightarrow>
       (a,b) \<in> fst (select S s)"
  apply (drule_tac Q="\<lambda>r s'. r \<in> S \<and> s' =s" in  use_valid[OF _ select_ext_weak_wp])
  apply (simp add: select_def)+
  done

termination cap_revoke
  apply (rule cap_revoke.termination)
   apply (rule wf_cap_revoke_recset)
  apply (clarsimp simp add: cap_revoke_recset_def in_monad select_def
                  dest!:    iffD1[OF in_get_cap_cte_wp_at] in_select_ext_weak)
  apply (frule use_validE_R [OF _ cap_delete_rvk_prog])
   apply (rule rpo_sym)
  apply (frule use_validE_R [OF _ cap_delete_deletes])
   apply simp
  apply (simp add: revoke_progress_ord_def)
  apply (erule disjE)
   apply (drule_tac f="\<lambda>f. f (aa, ba)" in arg_cong)
   apply (clarsimp simp: cte_wp_at_caps_of_state cap_to_rpo_def)
   apply (simp split: cap.split_asm)
  apply (drule in_preempt, clarsimp simp: trans_state_update'[symmetric])
  done

lemma cap_revoke_preservation':
  assumes x: "\<And>p. \<lbrace>P\<rbrace> cap_delete p \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes p: "\<lbrace>P\<rbrace> preemption_point \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "s \<turnstile> \<lbrace>P\<rbrace> cap_revoke ptr \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. P\<rbrace>"
proof (induct rule: cap_revoke.induct)
  case (1 slot)
  show ?case
    apply (subst cap_revoke.simps)
    apply (wp "1.hyps", assumption+)
           apply (wp x p hoare_drop_imps select_wp)
     apply simp_all
    done
qed

lemmas cap_revoke_preservation = use_spec(2) [OF cap_revoke_preservation']

lemmas cap_revoke_preservation2 = cap_revoke_preservation[THEN validE_valid]

lemma ball_subset: "\<forall>x\<in>A. Q x \<Longrightarrow> B \<subseteq> A \<Longrightarrow> \<forall>x\<in>B. Q x"
  apply blast
  done

lemma cap_revoke_preservation_desc_of':
  assumes x: "\<And>p. \<lbrace>P and Q p\<rbrace> cap_delete p \<lbrace>\<lambda>rv. P\<rbrace>"
  and     y: "\<And>sl s. P s \<Longrightarrow> \<forall>sl' \<in> descendants_of sl (cdt s). Q sl' s"
  assumes p: "\<lbrace>P\<rbrace> preemption_point \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "s \<turnstile> \<lbrace>P\<rbrace> cap_revoke ptr \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. P\<rbrace>"
proof (induct rule: cap_revoke.induct)
  case (1 slot)
  show ?case
    apply (subst cap_revoke.simps)
    apply (wp "1.hyps", assumption+)
           apply (wp x p hoare_drop_imps select_wp)
     apply (simp_all add: y)
    done
qed

lemmas cap_revoke_preservation_desc_of =
       use_spec(2) [OF cap_revoke_preservation_desc_of']

lemma cap_revoke_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> cap_revoke ptr \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wp cap_delete_typ_at cap_revoke_preservation irq_state_independent_AI preemption_point_inv, simp+)

lemma cap_revoke_invs:
  "\<lbrace>\<lambda>s. invs s\<rbrace> cap_revoke ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wp cap_revoke_preservation_desc_of)
   apply (fastforce simp: emptyable_def dest: reply_slot_not_descendant)
  apply (wp preemption_point_inv)
   apply simp+
  done

declare cap_revoke.simps[simp del]

lemma descendants_of_cdt_parent:
  "\<lbrakk> p' \<in> descendants_of p (cdt s) \<rbrakk> \<Longrightarrow> \<exists>p''. cdt s \<Turnstile> p'' \<leadsto> p'"
  apply (simp add: descendants_of_def del: split_paired_Ex)
  apply (erule tranclE)
   apply (erule exI)
  apply (erule exI)
  done


lemma cap_revoke_mdb_stuff3:
  "\<lbrakk> p' \<in> descendants_of p (cdt s); valid_mdb s \<rbrakk>
     \<Longrightarrow> cte_wp_at (op \<noteq> cap.NullCap) p' s"
  apply (clarsimp simp add: valid_mdb_def
                     dest!: descendants_of_cdt_parent)
  apply (simp add: cdt_parent_of_def)
  apply (drule(1) mdb_cte_atD)
  apply simp
  done


crunch typ_at[wp]: cap_recycle "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps filterM_mapM unless_def
    ignore: without_preemption filterM set_object
            clearMemory)


lemma inv_cnode_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> invoke_cnode ci \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (case_tac ci, simp_all add: invoke_cnode_def split del: split_if)
        apply (wp cap_insert_typ_at cap_move_typ_at cap_swap_typ_at hoare_drop_imps
                  cap_delete_typ_at cap_revoke_typ_at hoare_vcg_all_lift | wpc | 
               simp | rule conjI impI)+     
  done


lemma invoke_cnode_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_cnode ci \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ, wp inv_cnode_typ_at)


lemma iflive_mdb[simp]:
  "if_live_then_nonz_cap (cdt_update f s) = if_live_then_nonz_cap s"
  by (fastforce elim!: iflive_pspaceI)


lemma duplicate_creation:
  "\<lbrace>cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap
                  \<and> cap_irqs c = cap_irqs cap) p
     and cte_at p' and K (p \<noteq> p')\<rbrace>
     set_cap cap p'
  \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>cap. \<not> is_final_cap' cap s) p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_post_imp [where Q="\<lambda>rv. cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap
                                                       \<and>cap_irqs c = cap_irqs cap) p
                                        and cte_wp_at (op = cap) p'"])
   apply (clarsimp simp: cte_wp_at_def)
   apply (case_tac "\<exists>x. x \<in> obj_refs cap \<and> x \<in> obj_refs capa")
    apply (elim exE conjE)
    apply (frule (4) final_cap_duplicate_obj_ref)
    apply simp
   apply (case_tac "\<exists>x. x \<in> cap_irqs cap \<and> x \<in> cap_irqs capa")
    apply (elim exE conjE)
    apply (frule (4) final_cap_duplicate_irq, simp)
   apply (simp add: is_final_cap'_def)
  apply (wp set_cap_cte_wp_at)
   apply simp_all
  done


lemma state_refs_mdb[simp]:
  "state_refs_of (cdt_update f s) = state_refs_of s"
  by (rule state_refs_of_pspaceI [OF refl], simp)


lemma ifunsafe_mdb[simp]:
  "if_unsafe_then_cap (cdt_update f s) = if_unsafe_then_cap s"
  by (fastforce elim!: ifunsafe_pspaceI)


lemma zombies_final_mdb[simp]:
  "zombies_final (cdt_update f s) = zombies_final s"
  by (fastforce elim!: zombies_final_pspaceI)


definition
  zombies_final_caps :: "(cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
 "zombies_final_caps \<equiv> \<lambda>cps. \<forall>p p' cap cap'.
    cps p = Some cap \<and> cps p' = Some cap'
      \<and> obj_refs cap \<inter> obj_refs cap' \<noteq> {} \<and> p \<noteq> p'
   \<longrightarrow> \<not> is_zombie cap \<and> \<not> is_zombie cap'"


lemma zombies_final_caps_of_state:
  "zombies_final = zombies_final_caps \<circ> caps_of_state"
  by (rule ext,
      simp add: zombies_final_def2 zombies_final_caps_def
                cte_wp_at_caps_of_state)


lemma zombies_final_injective:
  "\<lbrakk> zombies_final_caps (caps_of_state s); inj f \<rbrakk>
     \<Longrightarrow> zombies_final_caps (caps_of_state s \<circ> f)"
  apply (simp only: zombies_final_caps_def o_def)
  apply (intro allI impI)
  apply (elim conjE allE, erule mp)
  apply (erule conjI)+
  apply (simp add: inj_eq)
  done


lemma set_cdt_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_cdt p \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_cdt_def)
  apply wp
  apply (simp add: caps_of_state_cte_wp_at)
  done


lemma caps_of_state_revokable[simp]:
  "caps_of_state (is_original_cap_update f s) = caps_of_state s"
  by (simp add: caps_of_state_cte_wp_at)


lemma cap_move_caps_of_state:
  "\<lbrace>\<lambda>s. P ((caps_of_state s) (ptr' \<mapsto> cap, ptr \<mapsto> cap.NullCap ))\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: cap_move_def)
  apply (wp | simp)+
  done


lemma zombies_duplicate_creation:
  "\<lbrace>\<lambda>s. zombies_final s \<and> \<not> is_zombie cap
        \<and> (\<exists>p'. cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap \<and> \<not> is_zombie c) p' s)
        \<and> cte_wp_at (op = cap.NullCap) p s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (wp set_cap_zombies)
  apply (clarsimp simp: cte_wp_at_def)
  apply (thin_tac "?x \<noteq> ?y")
  apply (case_tac "(a, b) = (aa, ba)")
   apply clarsimp
  apply (drule(3) zombies_finalD2)
   apply blast
  apply simp
  done


lemma state_refs_of_rvk[simp]:
  "state_refs_of (is_original_cap_update f s) = state_refs_of s"
  by (simp add: state_refs_of_def)


lemma weak_derived_is_zombie:
  "weak_derived cap cap' \<Longrightarrow> is_zombie cap = is_zombie cap'"
  by (auto simp: weak_derived_def copy_of_def is_cap_simps same_object_as_def 
           split: split_if_asm cap.splits arch_cap.splits)


lemma cap_move_zombies_final[wp]:
  "\<lbrace>zombies_final and cte_wp_at (op = cap.NullCap) ptr'
         and cte_wp_at (weak_derived cap) ptr
         and K (ptr \<noteq> ptr')\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  unfolding cap_move_def zombies_final_caps_of_state o_def set_cdt_def
  apply (rule hoare_pre)
   apply (wp|simp)+
  apply (simp add: cte_wp_at_caps_of_state zombies_final_caps_def del: split_paired_All)
  apply (elim conjE exE)
  apply (intro impI allI)
  apply (simp add: weak_derived_obj_refs weak_derived_is_zombie del: split_paired_All)
  apply blast  
  done


lemma cap_move_if_live[wp]:
  "\<lbrace>cte_wp_at (op = cap.NullCap) ptr'
         and cte_wp_at (weak_derived cap) ptr
         and K (ptr \<noteq> ptr')
         and if_live_then_nonz_cap\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap s\<rbrace>"
  unfolding cap_move_def
  apply (rule hoare_pre)
   apply (wp|simp)+
    apply (rule hoare_post_imp, simp only: if_live_then_nonz_cap_def)
    apply (simp only: ex_nonz_cap_to_def cte_wp_at_caps_of_state
                      imp_conv_disj)
    apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
  apply (clarsimp simp: if_live_then_nonz_cap_def
                        ex_nonz_cap_to_def cte_wp_at_caps_of_state
                   del: allI
              simp del: split_paired_Ex)
  apply (erule allEI, rule impI, drule(1) mp)
  apply (erule exfEI[where f="id (ptr := ptr', ptr' := ptr)"])
  apply (clarsimp simp: weak_derived_obj_refs zobj_refs_to_obj_refs)
  apply (rule conjI)
   apply (clarsimp simp: weak_derived_is_zombie)
  apply clarsimp
  done


lemma weak_derived_cte_refs':
  "weak_derived cap cap' \<Longrightarrow> cte_refs cap = cte_refs cap'"
  by (fastforce simp: copy_of_cte_refs weak_derived_def)


lemma appropriate_cte_master:
  "appropriate_cte_cap (cap_master_cap cap) = appropriate_cte_cap cap"
  apply (rule ext)
  apply (simp add: cap_master_cap_def appropriate_cte_cap_def
            split: cap.split)
  done


lemma weak_derived_appropriate:
  "weak_derived cap cap' \<Longrightarrow> appropriate_cte_cap cap = appropriate_cte_cap cap'"
  by (auto simp: weak_derived_def copy_of_def same_object_as_def2
                 appropriate_cte_master
          split: split_if_asm
          dest!: arg_cong[where f=appropriate_cte_cap])


lemma cap_move_if_unsafe [wp]:
  "\<lbrace>cte_wp_at (op = cap.NullCap) ptr'
         and cte_wp_at (weak_derived cap) ptr
         and K (ptr \<noteq> ptr')
         and if_unsafe_then_cap
         and ex_cte_cap_wp_to (appropriate_cte_cap cap) ptr'\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: cap_move_def)
  apply (wp | simp)+
   apply (rule hoare_post_imp, simp only: if_unsafe_then_cap_def)
   apply (simp only: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
   apply wp
  apply (clarsimp simp: if_unsafe_then_cap_def
                        ex_cte_cap_wp_to_def cte_wp_at_caps_of_state
              simp del: split_paired_All split_paired_Ex
                   del: allI
             split del: split_if)
  apply (frule weak_derived_Null)
  apply (frule weak_derived_cte_refs')
  apply (frule cap_irqs_appropriateness [OF weak_derived_cap_irqs])
  apply (frule weak_derived_appropriate)
  apply (erule allfEI[where f="id (ptr := ptr', ptr' := ptr)"])
  apply (case_tac "cref = ptr'")
   apply (intro allI impI,
          rule_tac x="(id (ptr := ptr', ptr' := ptr)) (a, b)" in exI)
   apply fastforce
  apply (clarsimp split: split_if_asm split del: split_if del: exE
               simp del: split_paired_All split_paired_Ex)
  apply (erule exfEI[where f="id (ptr := ptr', ptr' := ptr)"])
  apply (clarsimp split: split_if_asm)
  apply fastforce
  done


crunch arch[wp]: cap_move "\<lambda>s. P (arch_state s)"

crunch irq_node[wp]: cap_move "\<lambda>s. P (interrupt_irq_node s)"


lemma cap_range_NullCap:
  "cap_range cap.NullCap = {}"
  by (simp add: cap_range_def)


crunch interrupt_states[wp]: cap_move "\<lambda>s. P (interrupt_states s)"


lemma cap_move_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers and cte_wp_at (op = cap.NullCap) ptr'
           and cte_wp_at (weak_derived cap) ptr\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: valid_irq_handlers_def irq_issued_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=interrupt_states, OF cap_move_interrupt_states])
   apply (simp add: cap_move_def set_cdt_def)
    apply (wp | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state
                 elim!: ranE split: split_if_asm
                 dest!: weak_derived_cap_irqs)
   apply auto
  done


lemma cap_move_has_reply_cap_neg:
  "\<lbrace>\<lambda>s. \<not> has_reply_cap t s \<and>
    cte_wp_at (weak_derived c) p s \<and>
    cte_wp_at (op = cap.NullCap) p' s \<and>
    p \<noteq> p'\<rbrace>
   cap_move c p p' \<lbrace>\<lambda>rv s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: has_reply_cap_def cte_wp_at_caps_of_state
              del: split_paired_All split_paired_Ex)
  apply (wp cap_move_caps_of_state)
  apply (elim conjE exE)
  apply (erule(1) cap_swap_no_reply_caps, clarsimp+)
  done


lemma cap_move_replies:
  "\<lbrace>\<lambda>s. valid_reply_caps s
       \<and> cte_wp_at (weak_derived c) p s
       \<and> cte_wp_at (op = cap.NullCap) p' s
       \<and> p \<noteq> p'\<rbrace>
     cap_move c p p'
   \<lbrace>\<lambda>rv s. valid_reply_caps s\<rbrace>"
  apply (simp add: valid_reply_caps_def)
  apply (rule hoare_pre)
   apply (simp only: imp_conv_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift cap_move_has_reply_cap_neg)
    apply (simp add: cap_move_def, (wp|simp)+)
   apply (rule cap_move_caps_of_state)
  apply (clarsimp simp: fun_upd_def cte_wp_at_caps_of_state
                        unique_reply_caps_cap_swap [simplified fun_upd_def])
  done


lemma copy_of_reply_master:
  "copy_of cap cap' \<Longrightarrow> is_master_reply_cap cap = is_master_reply_cap cap'"
  apply (clarsimp simp: copy_of_def is_cap_simps)
  apply (clarsimp simp: same_object_as_def split: cap.splits arch_cap.splits)
  done


lemma cap_move_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps
         and cte_wp_at (weak_derived cap) ptr
         and cte_wp_at (op = cap.NullCap) ptr'\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: cap_move_def)
  apply (rule hoare_pre)
   apply (subst bind_assoc[symmetric],
          rule hoare_seq_ext [rotated],
          rule swap_of_caps_valid_arch_caps)
   apply (wp | simp)+
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done


crunch valid_global_objs[wp]: cap_move "valid_global_objs"


lemma cap_move_valid_ioc[wp]:
  "\<lbrace>valid_ioc and
    cte_wp_at (weak_derived cap) ptr and cte_wp_at (op = cap.NullCap) ptr'\<rbrace>
   cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  apply (simp add: cap_move_def valid_ioc_def[abs_def] cte_wp_at_caps_of_state
                   pred_conj_def)
  apply (wp set_cdt_cos_ioc set_cap_caps_of_state2 | simp)+
  apply (cases ptr, clarsimp simp add: cte_wp_at_caps_of_state valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply clarsimp
  done


lemma cap_move_invs[wp]:
  "\<lbrace>invs and valid_cap cap and cte_wp_at (op = cap.NullCap) ptr'
         and tcb_cap_valid cap ptr'
         and cte_wp_at (weak_derived cap) ptr
         and cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) ptr
         and ex_cte_cap_wp_to (appropriate_cte_cap cap) ptr' and K (ptr \<noteq> ptr')
         and K (\<not> is_master_reply_cap cap)\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  apply (simp add: pred_conj_def conj_ac [where Q = "valid_mdb S", standard])
  apply wp
   apply (rule hoare_vcg_mp)
    apply (rule hoare_pre, rule cap_move_zombies_final)
    apply clarsimp
   apply (rule hoare_vcg_mp)
    apply (rule hoare_pre, rule cap_move_if_live)
    apply clarsimp
   apply (rule hoare_vcg_mp)
    apply (rule hoare_pre, rule cap_move_if_unsafe)
    apply clarsimp
   apply (rule hoare_vcg_mp)
    apply (rule hoare_pre, rule cap_move_irq_handlers)
    apply clarsimp
   apply (rule hoare_vcg_mp)
    apply (rule hoare_pre, rule cap_move_replies)
    apply clarsimp
   apply (rule hoare_vcg_mp)
    apply (rule hoare_pre, rule cap_move_valid_arch_caps)
    apply clarsimp
   apply (rule hoare_vcg_mp)
    apply (rule hoare_pre, rule cap_move_valid_global_objs)
    apply clarsimp
   apply (rule hoare_vcg_mp)
    apply (rule hoare_pre, rule cap_move_valid_ioc)
    apply clarsimp
   apply simp
   apply (rule hoare_drop_imps)+
   apply (simp add: cap_move_def set_cdt_def)
   apply (rule hoare_pre)
    apply (wp set_cap_valid_objs set_cap_idle set_cap_typ_at
              cap_table_at_lift_irq tcb_at_typ_at
              hoare_vcg_disj_lift hoare_vcg_all_lift
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
    apply (simp add: tcb_cap_valid_def)
   apply (rule tcb_cap_valid_NullCapD)
    apply (erule(1) tcb_cap_valid_caps_of_stateD)
   apply (simp add: is_cap_simps)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma cte_wp_at_use2:
  "\<lbrakk>cte_wp_at P p s; cte_wp_at P' p s; \<And>c. \<lbrakk>cte_wp_at (op = c) p s; P c; P' c\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (auto simp: cte_wp_at_caps_of_state)


lemma cte_wp_at_use3:
  "\<lbrakk>cte_wp_at P p s; cte_wp_at P' p s; cte_wp_at P'' p s; \<And>c. \<lbrakk>cte_wp_at (op = c) p s; P c; P' c; P'' c\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (auto simp: cte_wp_at_caps_of_state)


lemma cap_move_valid_cap[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap'\<rbrace> cap_move cap p p' \<lbrace>\<lambda>_ s. s \<turnstile> cap'\<rbrace>"
  unfolding cap_move_def
  by (wp set_cdt_valid_cap | simp)+


lemma weak_derived_cte_refs_abs:
  "weak_derived c c' \<Longrightarrow> cte_refs c' = cte_refs c"
  apply (clarsimp simp: weak_derived_def copy_of_def)
  apply (auto simp: same_object_as_def is_cap_simps bits_of_def
             split: split_if_asm cap.splits arch_cap.split_asm
            intro!: ext)
  done


lemma cap_move_ex_cap_cte:
  "\<lbrace>ex_cte_cap_wp_to P ptr and 
    cte_wp_at (weak_derived cap) p and 
    cte_wp_at (op = cap.NullCap) p' and 
    K (p \<noteq> p') and K (\<forall>cap'. weak_derived cap cap' \<longrightarrow> P cap = P cap')\<rbrace>
  cap_move cap p p'
  \<lbrace>\<lambda>_. ex_cte_cap_wp_to P ptr\<rbrace>"
  unfolding cap_move_def ex_cte_cap_wp_to_def cte_wp_at_caps_of_state set_cdt_def 
  apply (rule hoare_pre)
   apply wp
    apply (simp del: split_paired_Ex)
    apply (wp set_cap_caps_of_state | simp del: split_paired_Ex add: cte_wp_at_caps_of_state)+
  apply (elim conjE exE)
  apply (case_tac "cref = p")
   apply (rule_tac x=p' in exI)
   apply clarsimp
   apply (drule weak_derived_cte_refs_abs)
   apply simp
  apply (rule_tac x=cref in exI)
  apply clarsimp
  done


lemma cap_move_src_slot_Null:
  "\<lbrace>cte_at src and K(src \<noteq> dest)\<rbrace> cap_move cap src dest \<lbrace>\<lambda>_ s. cte_wp_at (op = cap.NullCap) src s\<rbrace>"
  unfolding cap_move_def
  by (wp set_cdt_cte_wp_at set_cap_cte_wp_at' | simp)+


crunch st_tcb[wp]: cap_move "st_tcb_at P t"


lemmas cap_revoke_cap_table[wp] = cap_table_at_lift_valid [OF cap_revoke_typ_at]


lemmas appropriate_cte_cap_simps = appropriate_cte_cap_def [split_simps cap.split]


lemma recycle_cap_appropriateness:
  "\<lbrace>valid_cap cap\<rbrace> recycle_cap is_final cap \<lbrace>\<lambda>rv s. appropriate_cte_cap rv = appropriate_cte_cap cap\<rbrace>"
  apply (simp add: recycle_cap_def)
  apply (rule hoare_pre)
   apply (wp gts_st_tcb_at | wpc | simp)+
   apply (simp add: arch_recycle_cap_def o_def split del: split_if)   
   apply (wp | wpc | simp add: | wp_once hoare_drop_imps)+
  apply (auto simp: appropriate_cte_cap_def fun_eq_iff valid_cap_def tcb_at_st_tcb_at)
  done


lemma recycle_cap_appropriate_cap_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to (appropriate_cte_cap cap) p and valid_cap cap\<rbrace>
     recycle_cap is_final cap
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to (appropriate_cte_cap rv) p\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (subst pred_conj_def, rule hoare_vcg_conj_lift)
    apply (rule recycle_cap_cte_cap_to)
   apply (rule recycle_cap_appropriateness)
  apply clarsimp
  done

crunch inv [wp]: is_final_cap "P"

lemma is_final_cap_is_final[wp]:
  "\<lbrace>\<top>\<rbrace> is_final_cap cap \<lbrace>\<lambda>rv s. rv = is_final_cap' cap s\<rbrace>"
  unfolding is_final_cap_def 
  by wp simp

lemma cap_recycle_invs:
  "\<lbrace>invs and (cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) p)
         and real_cte_at p\<rbrace> 
     cap_recycle p
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cap_recycle_def unless_def)
  apply (wp replace_cap_invs_arch_update recycle_cap_invs[where slot=p]
            cap_recycle_cte_replaceable)
    apply (rule hoare_strengthen_post, rule get_cap_sp[where P=invs])
    apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (frule caps_of_state_valid_cap, clarsimp+)
    apply (frule if_unsafe_then_capD[OF caps_of_state_cteD], clarsimp+)
    apply auto[1]
   apply (simp add: finalise_slot_def)
   apply (wp rec_del_invs)
  apply simp
  apply (rule hoare_pre)
   apply (wp cap_revoke_invs | strengthen real_cte_emptyable_strg)+
  apply simp
  done

lemma real_cte_not_reply_masterD:
  "\<And>P ptr.
   \<lbrakk> real_cte_at ptr s; valid_reply_masters s; valid_objs s \<rbrakk> \<Longrightarrow> 
   cte_wp_at (\<lambda>cap. \<not> is_master_reply_cap cap) ptr s"
  apply clarsimp
  apply (subgoal_tac "\<not> tcb_at a s")
   apply (clarsimp simp: cap_table_at_cte_at cte_wp_at_not_reply_master)
  apply (clarsimp simp: obj_at_def is_tcb is_cap_table)
  done

lemma real_cte_weak_derived_not_reply_masterD:
  "\<And>cap ptr.
   \<lbrakk> cte_wp_at (weak_derived cap) ptr s; real_cte_at ptr s;
     valid_reply_masters s; valid_objs s \<rbrakk> \<Longrightarrow>
   \<not> is_master_reply_cap cap"
  by (fastforce simp: cte_wp_at_caps_of_state weak_derived_replies
              dest!: real_cte_not_reply_masterD)

lemma real_cte_is_derived_not_replyD:
  "\<And>m p cap ptr.
   \<lbrakk> cte_wp_at (is_derived m p cap) ptr s; real_cte_at ptr s;
     valid_reply_masters s; valid_objs s \<rbrakk> \<Longrightarrow>
   \<not> is_reply_cap cap"
  by (fastforce simp: cte_wp_at_caps_of_state is_derived_def
              dest!: real_cte_not_reply_masterD)


lemma cap_irqs_is_derived:
  "is_derived m ptr cap cap' \<Longrightarrow> cap_irqs cap = cap_irqs cap'"
  by (clarsimp simp: is_derived_def cap_master_cap_irqs split: split_if_asm)


lemma tcb_cap_valid_mdb[simp]:
  "tcb_cap_valid cap p (cdt_update mfn s) = tcb_cap_valid cap p s"
  by (simp add: tcb_cap_valid_def)


lemma tcb_cap_valid_is_original_cap[simp]:
  "tcb_cap_valid cap p (is_original_cap_update mfn s) = tcb_cap_valid cap p s"
  by (simp add: tcb_cap_valid_def)


crunch tcb_cap_valid[wp]: cap_move "tcb_cap_valid cap p"

lemma invoke_cnode_invs[wp]:
  "\<lbrace>invs and valid_cnode_inv i\<rbrace> invoke_cnode i \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding invoke_cnode_def
  apply (cases i)
        apply simp
        apply wp
        apply (simp add: ex_cte_cap_to_cnode_always_appropriate_strg
                         real_cte_tcb_valid)
        apply (rule conjI)
         apply (clarsimp simp: cte_wp_at_caps_of_state dest!: cap_irqs_is_derived)
        apply (rule conjI)
          apply (elim conjE)
           apply (drule real_cte_is_derived_not_replyD)
           apply (simp add:invs_valid_objs invs_valid_reply_masters)+
         apply (clarsimp simp:is_cap_simps)
        apply (elim conjE)
        apply (drule real_cte_not_reply_masterD)
         apply (simp add:invs_valid_objs invs_valid_reply_masters)+
        apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def)
       apply simp
       apply wp
       apply (fastforce simp: real_cte_tcb_valid cte_wp_at_caps_of_state
                             ex_cte_cap_to_cnode_always_appropriate_strg
                       dest: real_cte_weak_derived_not_reply_masterD)
      apply simp
      apply (wp cap_revoke_invs)
      apply simp
     apply simp
     apply wp
     apply (clarsimp simp: emptyable_def obj_at_def is_tcb is_cap_table)
    apply simp
    apply (rule conjI)
     apply (rule impI)
     apply wp
     apply (fastforce simp: real_cte_tcb_valid
                           ex_cte_cap_to_cnode_always_appropriate_strg
                     dest: real_cte_weak_derived_not_reply_masterD)
    apply (rule impI)
    apply (rule hoare_pre)
     apply wp
     apply (simp add: cte_wp_at_caps_of_state)
     apply (wp cap_move_caps_of_state cap_move_ex_cap_cte)
    apply (simp add: pred_conj_def)
    apply (elim conjE exE)
    apply (simp add: real_cte_tcb_valid ex_cte_cap_to_cnode_always_appropriate_strg
                     cap_irqs_appropriateness [OF weak_derived_cap_irqs])
    apply (intro conjI,
          (fastforce simp: cte_wp_at_caps_of_state
                    dest: real_cte_weak_derived_not_reply_masterD)+)[1]
   apply simp
   apply (rule hoare_pre)
    apply (wp hoare_drop_imps|wpc)+
     apply simp
     apply (wp get_cap_wp)
   apply (clarsimp simp: all_rights_def)
   apply (rule conjI)
    apply (clarsimp elim!: cte_wp_valid_cap)
   apply (clarsimp simp: real_cte_tcb_valid cte_wp_at_caps_of_state
                         is_cap_simps ex_cte_cap_to_cnode_always_appropriate_strg)
  apply simp
  apply (wp cap_recycle_invs)
  apply simp
  done


crunch st_tcb_at[wp]: cap_move "st_tcb_at P t"


(* FIXME: rename, move *)
lemma omgwtfbbq[simp]:
  "(\<forall>x. y \<noteq> x) = False"
  by clarsimp


lemma corres_underlying_lift_ex1:
  assumes c: "\<And>v. corres_underlying sr nf r (P v and Q) P' a c" 
  shows "corres_underlying sr nf r ((\<lambda>s. \<exists>v. P v s) and Q) P' a c" 
  unfolding corres_underlying_def
  apply clarsimp
  apply (cut_tac v = v in c)
  apply (auto simp: corres_underlying_def)
  done


lemmas corres_underlying_lift_ex1' = corres_underlying_lift_ex1 [where Q = \<top>, simplified]


lemma corres_underlying_lift_ex2:
  assumes c: "\<And>v. corres_underlying sr nf r P (P' v and Q) a c" 
  shows "corres_underlying sr nf r P ((\<lambda>s. \<exists>v. P' v s) and Q) a c" 
  unfolding corres_underlying_def
  apply clarsimp
  apply (cut_tac v = v in c)
  apply (auto simp: corres_underlying_def)
  done


lemmas corres_underlying_lift_ex2' = corres_underlying_lift_ex2 [where Q = \<top>, simplified]


lemma reset_mem_mapping_master:
  "cap_master_cap (cap.ArchObjectCap (arch_reset_mem_mapping arch_cap)) = cap_master_cap (cap.ArchObjectCap arch_cap)"
  unfolding cap_master_cap_def
  by (cases arch_cap, simp_all)


lemma real_cte_halted_if_tcb[simp]:
  "real_cte_at (a, b) s \<Longrightarrow> halted_if_tcb a s"
  by (clarsimp simp: halted_if_tcb_def obj_at_def is_cap_table is_tcb)


end
