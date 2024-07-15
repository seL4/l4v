(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Results about CNode Invocations, particularly the
recursive revoke and delete operations.
*)

theory CNodeInv_AI
imports ArchIpc_AI
begin


context begin interpretation Arch .
requalify_facts
  set_cap_arch
  cte_at_length_limit
  arch_derive_cap_untyped
  valid_arch_mdb_cap_swap
end

declare set_cap_arch[wp]


primrec
  valid_cnode_inv :: "cnode_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_cnode_inv (InsertCall cap ptr ptr') =
   (valid_cap cap and real_cte_at ptr and real_cte_at ptr' and
    (\<lambda>s. cte_wp_at (is_derived (cdt s) ptr cap) ptr s) and
    cte_wp_at (\<lambda>c. c = NullCap) ptr' and
    ex_cte_cap_wp_to is_cnode_cap ptr' and K (ptr \<noteq> ptr') and
    (\<lambda>s. \<forall>r\<in>obj_refs cap. \<forall>p'.
           ptr' \<noteq> p' \<and> cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') p' s \<longrightarrow>
           cte_wp_at (Not \<circ> is_zombie) p' s \<and> \<not> is_zombie cap))"
| "valid_cnode_inv (MoveCall cap ptr ptr') =
   (valid_cap cap and cte_wp_at ((=) cap.NullCap) ptr' and
    cte_wp_at ((\<noteq>) NullCap) ptr and cte_wp_at (weak_derived cap) ptr and
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
    cte_wp_at ((\<noteq>) NullCap) src and
    cte_wp_at (weak_derived p_cap) pivot and
    cte_wp_at (\<lambda>c. is_untyped_cap c \<longrightarrow> c = p_cap) pivot and
    cte_wp_at ((\<noteq>) NullCap) pivot and K (src \<noteq> pivot \<and> pivot \<noteq> dest) and
    (\<lambda>s. src \<noteq> dest \<longrightarrow> cte_wp_at (\<lambda>c. c = NullCap) dest s) and
    ex_cte_cap_wp_to is_cnode_cap pivot and ex_cte_cap_wp_to is_cnode_cap dest)"
(*| "valid_cnode_inv (SaveCall ptr) =
   (ex_cte_cap_wp_to is_cnode_cap ptr and
    cte_wp_at (\<lambda>c. c = NullCap) ptr and real_cte_at ptr)"*)
| "valid_cnode_inv (CancelBadgedSendsCall cap) =
   (valid_cap cap and K (has_cancel_send_rights cap))"


primrec
  valid_rec_del_call :: "rec_del_call \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_rec_del_call (CTEDeleteCall slot _) = \<top>"
| "valid_rec_del_call (FinaliseSlotCall slot _) = \<top>"
| "valid_rec_del_call (ReduceZombieCall cap slot _) =
       (cte_wp_at ((=) cap) slot and is_final_cap' cap
            and K (is_zombie cap))"


locale CNodeInv_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes derive_cap_objrefs:
    "\<And>P cap slot.
      \<lbrace>\<lambda>s::'state_ext state. P (obj_refs cap)\<rbrace>
        derive_cap slot cap
      \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> P (obj_refs rv)\<rbrace>,-"
  assumes derive_cap_zobjrefs:
    "\<And>P cap slot.
      \<lbrace>\<lambda>s::'state_ext state. P (zobj_refs cap)\<rbrace>
        derive_cap slot cap
      \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow> P (zobj_refs rv)\<rbrace>,-"
  assumes update_cap_objrefs:
    "\<And>P dt cap. \<lbrakk> update_cap_data P dt cap \<noteq> NullCap \<rbrakk> \<Longrightarrow>
      obj_refs (update_cap_data P dt cap) = obj_refs cap"
  assumes update_cap_zobjrefs:
    "\<And>P dt cap. \<lbrakk> update_cap_data P dt cap \<noteq> cap.NullCap \<rbrakk> \<Longrightarrow>
      zobj_refs (update_cap_data P dt cap) = zobj_refs cap"
  assumes copy_mask [simp]:
    "\<And>R c. copy_of (mask_cap R c) = copy_of c"
  assumes update_cap_data_mask_Null [simp]:
    "\<And>P x m c. (update_cap_data P x (mask_cap m c) = NullCap) = (update_cap_data P x c = NullCap)"
  assumes cap_master_update_cap_data:
    "\<And>P x c. \<lbrakk> update_cap_data P x c \<noteq> NullCap \<rbrakk> \<Longrightarrow>
      cap_master_cap (update_cap_data P x c) = cap_master_cap c"
  assumes same_object_as_cap_master:
    "\<And>cap cap'. same_object_as cap cap' \<Longrightarrow> cap_master_cap cap = cap_master_cap cap'"
  assumes cap_asid_update_cap_data:
    "\<And>P x c. update_cap_data P x c \<noteq> NullCap \<Longrightarrow> cap_asid (update_cap_data P x c) = cap_asid c"
  assumes cap_vptr_update_cap_data:
    "\<And>P x c. update_cap_data P x c \<noteq> NullCap \<Longrightarrow> cap_vptr (update_cap_data P x c) = cap_vptr c"
  assumes cap_asid_base_update_cap_data:
    "\<And>P x c. update_cap_data P x c \<noteq> NullCap \<Longrightarrow>
      cap_asid_base (update_cap_data P x c) = cap_asid_base c"
  assumes same_object_as_update_cap_data:
    "\<And>P x c c'. \<lbrakk> update_cap_data P x c \<noteq> NullCap; same_object_as c' c \<rbrakk> \<Longrightarrow>
      same_object_as c' (update_cap_data P x c)"
  assumes weak_derived_update_cap_data:
    "\<And>P x c c'. \<lbrakk>update_cap_data P x c \<noteq> NullCap; weak_derived c c'\<rbrakk> \<Longrightarrow>
      weak_derived (update_cap_data P x c) c'"
  assumes cap_badge_update_cap_data:
    "\<And>x c bdg. update_cap_data False x c \<noteq> NullCap \<and> (bdg, cap_badge c) \<in> capBadge_ordering False
       \<longrightarrow> (bdg, cap_badge (update_cap_data False x c)) \<in> capBadge_ordering False"
  assumes cap_vptr_rights_update[simp]:
    "\<And>f c. cap_vptr (cap_rights_update f c) = cap_vptr c"
  assumes cap_vptr_mask[simp]:
    "\<And>m c. cap_vptr (mask_cap m c) = cap_vptr c"
  assumes cap_asid_base_rights [simp]:
    "\<And>R c. cap_asid_base (cap_rights_update R c) = cap_asid_base c"
  assumes cap_asid_base_mask[simp]:
    "\<And>m c. cap_asid_base (mask_cap m c) = cap_asid_base c"
  assumes weak_derived_mask:
    "\<And>c c' m. \<lbrakk> weak_derived c c'; cap_aligned c \<rbrakk> \<Longrightarrow> weak_derived (mask_cap m c) c'"
  assumes vs_cap_ref_update_cap_data[simp]:
    "\<And>P d cap. vs_cap_ref (update_cap_data P d cap) = vs_cap_ref cap"
  assumes weak_derived_cap_is_device:
    "\<And>c c'. \<lbrakk>weak_derived c' c\<rbrakk> \<Longrightarrow>  cap_is_device c = cap_is_device c'"
  assumes invs_irq_state_independent[intro!, simp]:
    "\<And>(s::'state_ext state) f.
      invs (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
        = invs s"
  assumes cte_at_nat_to_cref_zbits:
    "\<And>(s::'state_ext state) oref zb n m.
      \<lbrakk> s \<turnstile> Zombie oref zb n; m < n \<rbrakk> \<Longrightarrow> cte_at (oref, nat_to_cref (zombie_cte_bits zb) m) s"
  assumes copy_of_cap_range:
    "\<And>cap cap'. copy_of cap cap' \<Longrightarrow> cap_range cap = cap_range cap'"
  assumes copy_of_zobj_refs:
    "\<And>cap cap'. copy_of cap cap' \<Longrightarrow> zobj_refs cap = zobj_refs cap'"
  assumes vs_cap_ref_master:
  "\<And> cap cap'.
    \<lbrakk> cap_master_cap cap = cap_master_cap cap';
      cap_asid cap = cap_asid cap';
      cap_asid_base cap = cap_asid_base cap';
      cap_vptr cap = cap_vptr cap' \<rbrakk>
    \<Longrightarrow> vs_cap_ref cap = vs_cap_ref cap'"
  assumes weak_derived_vs_cap_ref:
    "\<And>c c'. weak_derived c c' \<Longrightarrow> vs_cap_ref c = vs_cap_ref c'"
  assumes weak_derived_table_cap_ref:
    "\<And>c c'. weak_derived c c' \<Longrightarrow> table_cap_ref c = table_cap_ref c'"
  assumes swap_of_caps_valid_arch_caps:
    "\<And>c a c' b.
      \<lbrace>valid_arch_caps and cte_wp_at (weak_derived c) a and cte_wp_at (weak_derived c') b\<rbrace>
        do
          y \<leftarrow> set_cap c b;
          set_cap c' a
        od
      \<lbrace>\<lambda>rv. valid_arch_caps :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes cap_swap_asid_map[wp]:
    "\<And>c a c' b.
      \<lbrace>valid_asid_map and cte_wp_at (weak_derived c) a and cte_wp_at (weak_derived c') b\<rbrace>
        cap_swap c a c' b
      \<lbrace>\<lambda>rv. valid_asid_map :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes cap_swap_cap_refs_in_kernel_window[wp]:
    "\<And>c a c' b.
      \<lbrace>cap_refs_in_kernel_window and cte_wp_at (weak_derived c) a and cte_wp_at (weak_derived c') b\<rbrace>
        cap_swap c a c' b
      \<lbrace>\<lambda>rv. cap_refs_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes cap_swap_ioports[wp]:
  "\<lbrace>valid_ioports and cte_wp_at (weak_derived c) a and cte_wp_at (weak_derived c') b\<rbrace>
     cap_swap c a c' b
   \<lbrace>\<lambda>rv (s::'state_ext state). valid_ioports s\<rbrace>"
  assumes cap_swap_vms[wp]:
    "\<And>c a c' b.
      \<lbrace>valid_machine_state :: 'state_ext state \<Rightarrow> bool\<rbrace>
        cap_swap c a c' b
      \<lbrace>\<lambda>rv. valid_machine_state\<rbrace>"
  assumes unat_of_bl_nat_to_cref:
    "\<And>n ln. \<lbrakk> n < 2 ^ ln; ln < word_bits \<rbrakk>
      \<Longrightarrow> unat (of_bl (nat_to_cref ln n) :: machine_word) = n"
  assumes zombie_is_cap_toE_pre:
    "\<And>(s::'state_ext state) ptr zbits n m irqn.
      \<lbrakk> s \<turnstile> Zombie ptr zbits n; invs s; m < n \<rbrakk>
        \<Longrightarrow> (ptr, nat_to_cref (zombie_cte_bits zbits) m) \<in> cte_refs (Zombie ptr zbits n) irqn"
  assumes nat_to_cref_0_replicate:
    "\<And>n. n < word_bits \<Longrightarrow> nat_to_cref n 0 = replicate n False"
  assumes prepare_thread_delete_thread_cap:
  "\<And>x p t. \<lbrace>\<lambda>(s::'state_ext state). caps_of_state s x = Some (cap.ThreadCap p)\<rbrace>
     prepare_thread_delete t
   \<lbrace>\<lambda>rv s. caps_of_state s x = Some (cap.ThreadCap p)\<rbrace>"

locale CNodeInv_AI_2 = CNodeInv_AI state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself" +
  assumes rec_del_invs':
    "\<And>(s::'state_ext state) call.
      s \<turnstile> \<lbrace>\<lambda>x. invs x \<and> valid_rec_del_call call x \<and>
              (\<not> exposed_rdcall call \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall call) x) \<and>
              (case call of ReduceZombieCall cap sl ex \<Rightarrow> \<not> cap_removeable cap sl \<and>
                    (\<forall>t\<in>obj_refs cap. halted_if_tcb t x)
                | _ \<Rightarrow> True)\<rbrace>
          rec_del call
          \<lbrace>\<lambda>rv s. invs s \<and>
              (case call of CTEDeleteCall _ bool \<Rightarrow> True
                | FinaliseSlotCall sl x \<Rightarrow> (fst rv \<or> x \<longrightarrow> cte_wp_at (replaceable s sl NullCap) sl s) \<and>
                    (snd rv \<noteq> NullCap \<longrightarrow> post_cap_delete_pre (snd rv) ((caps_of_state s) (sl \<mapsto> cap.NullCap)))
                | ReduceZombieCall cap sl x \<Rightarrow> \<not> x \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) sl s)\<rbrace>,
          \<lbrace>\<lambda>rv. invs\<rbrace>"


lemma mask_cap_all:
  "mask_cap (all_rights \<inter> r) c = mask_cap r c"
  unfolding all_rights_def by simp


lemma decode_cnode_cases2:
  assumes mvins: "\<And>index bits src_index src_depth args' src_root_cap exs'.
                    \<lbrakk> args = index # bits # src_index # src_depth # args';
                      exs = src_root_cap # exs';
                      gen_invocation_type label \<in> set [CNodeCopy .e. CNodeMutate];
                      gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeRotate];
                      gen_invocation_type label \<notin> {CNodeRevoke, CNodeDelete,
                      CNodeCancelBadgedSends, CNodeRotate} \<rbrakk> \<Longrightarrow> P"
  assumes rvk: "\<And>index bits args'. \<lbrakk> args = index # bits # args';
                          gen_invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate];
                          gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeRotate];
                          gen_invocation_type label = CNodeRevoke \<rbrakk> \<Longrightarrow> P"
  assumes dlt: "\<And>index bits args'. \<lbrakk> args = index # bits # args';
                          gen_invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate];
                          gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeRotate];
                          gen_invocation_type label = CNodeDelete \<rbrakk> \<Longrightarrow> P"
  assumes rcy: "\<And>index bits args'. \<lbrakk> args = index # bits # args';
                          gen_invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate];
                          gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeRotate];
                          gen_invocation_type label = CNodeCancelBadgedSends \<rbrakk> \<Longrightarrow> P"
  assumes rot: "\<And>index bits pivot_new_data pivot_index pivot_depth src_new_data
                  src_index src_depth args' pivot_root_cap src_root_cap exs'.
                     \<lbrakk> args = index # bits # pivot_new_data # pivot_index # pivot_depth
                                 # src_new_data # src_index # src_depth # args';
                       exs = pivot_root_cap # src_root_cap # exs';
                       gen_invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate];
                       gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeRotate];
                       gen_invocation_type label = CNodeRotate \<rbrakk> \<Longrightarrow> P"
  assumes errs:
      "\<lbrakk> gen_invocation_type label \<notin> set [CNodeRevoke .e. CNodeRotate] \<or>
         args = [] \<or> (\<exists>x. args = [x]) \<or> (\<exists>index bits args'. args = index # bits # args' \<and>
                             gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeRotate] \<and>
                             (gen_invocation_type label \<in> set [CNodeCopy .e. CNodeMutate]
                                        \<and> gen_invocation_type label \<notin> {CNodeRevoke, CNodeDelete,
                                             CNodeCancelBadgedSends, CNodeRotate}
                                        \<and> (case (args', exs) of (src_index # src_depth # args'',
                                                    src_root_cap # exs') \<Rightarrow> False | _ \<Rightarrow> True) \<or>
                              gen_invocation_type label \<notin> set [CNodeCopy .e. CNodeMutate] \<and>
                              gen_invocation_type label = CNodeRotate \<and> (case (args', exs) of
                              (pivot_new_data # pivot_index # pivot_depth
                                 # src_new_data # src_index # src_depth # args'',
                               pivot_root_cap # src_root_cap # exs') \<Rightarrow> False
                                         | _ \<Rightarrow> True))) \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  have simps: "[CNodeRevoke .e. CNodeRotate]
                     = [CNodeRevoke, CNodeDelete, CNodeCancelBadgedSends, CNodeCopy, CNodeMint,
                        CNodeMove, CNodeMutate, CNodeRotate]"
              "[CNodeCopy .e. CNodeMutate] = [CNodeCopy, CNodeMint,
                        CNodeMove, CNodeMutate]"
    by (simp_all add: upto_enum_def fromEnum_def toEnum_def enum_invocation_label enum_gen_invocation_labels)
  show ?thesis
    apply (cases args)
     apply (simp add: errs)
    apply (case_tac list)
     apply (simp add: errs)
    apply (case_tac "gen_invocation_type label \<in> set [CNodeCopy .e. CNodeMutate]")
     apply (case_tac "case (lista, exs) of (src_index # src_depth # args'',
                             src_root_cap # exs'') \<Rightarrow> False | _ \<Rightarrow> True")
      apply (rule errs)
      apply (simp add: simps)
      apply (rule disjI2)
      apply auto[1]
     apply (simp split: prod.split_asm list.split_asm)
     apply (erule(2) mvins, auto simp: simps)[1]
    apply (case_tac "gen_invocation_type label \<in> set [CNodeRevoke .e. CNodeRotate]")
     apply (simp_all add: errs)
    apply (insert rvk dlt rcy rot)
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
  by (fastforce simp add: valid_def)

lemma derive_cap_untyped:
  "\<lbrace>\<lambda>s. P (untyped_range cap)\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> P (untyped_range rv)\<rbrace>,-"
  unfolding derive_cap_def is_zombie_def
  by (cases cap; (wp ensure_no_children_inv arch_derive_cap_untyped | simp add: o_def)+)

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

lemma cap_asid_mask[simp]:
  "cap_asid (mask_cap m c) = cap_asid c"
  by (simp add: mask_cap_def)


lemma cap_master_mask[simp]:
  "cap_master_cap (mask_cap rs cap) = cap_master_cap cap"
  by (simp add: mask_cap_def)


lemma cap_badge_mask[simp]:
  "cap_badge (mask_cap rs cap) = cap_badge cap"
  by (simp add: mask_cap_def)


lemma ensure_empty_cte_wp_at:
  "\<lbrace>\<top>\<rbrace> ensure_empty c \<lbrace>\<lambda>rv s. cte_wp_at ((=) cap.NullCap) c s\<rbrace>, -"
  unfolding ensure_empty_def
  apply (wp whenE_throwError_wp get_cap_wp)
  apply simp
  done


lemmas get_cap_cte_caps_to_no_wp[wp]
    = get_cap_cte_caps_to[where P="\<top>", simplified]


lemma lookup_cap_ex[wp]:
  "\<lbrace>\<top>\<rbrace> lookup_cap t c \<lbrace>\<lambda>rv s. \<forall>r\<in>cte_refs rv (interrupt_irq_node s). ex_cte_cap_to r s\<rbrace>, -"
  by (simp add: split_def lookup_cap_def) wp


lemmas cap_aligned_valid[elim!] = valid_cap_aligned


lemma cap_derive_not_null_helper2:
  "\<lbrace>P\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> Q rv s\<rbrace>, -
      \<Longrightarrow>
   \<lbrace>\<lambda>s. cap \<noteq> cap.NullCap \<and> \<not> is_zombie cap \<and> cap \<noteq> cap.IRQControlCap \<longrightarrow> P s\<rbrace>
     derive_cap slot cap
   \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> Q rv s\<rbrace>, -"
  apply (drule cap_derive_not_null_helper)
  apply (erule hoare_strengthen_postE_R)
  apply simp
  done

lemma has_cancel_send_rights_ep_cap:
  "has_cancel_send_rights cap \<Longrightarrow> is_ep_cap cap"
  by (clarsimp simp: has_cancel_send_rights_def split: cap.splits)


lemma is_untyped_update_cap_data[intro]:
  "is_untyped_cap r \<Longrightarrow> update_cap_data c x r = r"
  by (cases r; clarsimp simp: update_cap_data_def is_arch_cap_def)

context CNodeInv_AI begin

lemma decode_cnode_inv_wf[wp]:
  "\<And>cap.
    \<lbrace>invs and valid_cap cap
          and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
          and (\<lambda>s. is_cnode_cap cap \<longrightarrow> (\<forall>r\<in>cte_refs cap (interrupt_irq_node s).
                 ex_cte_cap_wp_to is_cnode_cap r s))
          and (\<lambda>s. \<forall>cap \<in> set cs. s \<turnstile> cap)
          and (\<lambda>s. \<forall>cap \<in> set cs. is_cnode_cap cap \<longrightarrow>
                 (\<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s)) \<rbrace>
      decode_cnode_invocation mi args cap cs
    \<lbrace>valid_cnode_inv\<rbrace>,-"
  apply (rule decode_cnode_cases2[where args=args and exs=cs and label=mi])
         \<comment> \<open>Move/Insert\<close>
        apply (simp add: decode_cnode_invocation_def unlessE_whenE
                     split del: if_split)
        apply (wp lsfco_cte_at ensure_no_children_wp whenE_throwError_wp
          | simp add: split_beta split del: if_split
          | (fold validE_R_def)[1])+
               apply (rule cap_derive_not_null_helper2)
               apply (simp only: imp_conjR)
               apply ((wp derive_cap_is_derived
                          derive_cap_valid_cap
                          derive_cap_zobjrefs derive_cap_objrefs_iszombie
                            | wp (once) hoare_drop_imps)+ )[1]
              apply (wp whenE_throwError_wp | wpcw)+
            apply (rename_tac dest_slot y src_slot)
            apply simp
            apply (rule_tac Q'="\<lambda>src_cap. valid_cap src_cap and ex_cte_cap_wp_to is_cnode_cap dest_slot
                                       and zombies_final and valid_objs
                                       and real_cte_at src_slot and real_cte_at dest_slot
                                       and cte_wp_at (\<lambda>c. c = src_cap) src_slot
                                       and cte_wp_at ((=) cap.NullCap) dest_slot"
                       in hoare_post_imp)
             apply (rename_tac src_cap s)
             apply (clarsimp simp: cte_wp_at_caps_of_state all_rights_def)
             apply (simp add: cap_master_update_cap_data weak_derived_update_cap_data
                              cap_asid_update_cap_data
                              update_cap_data_validI update_cap_objrefs)
             apply (strengthen cap_badge_update_cap_data)
             apply simp
             apply (frule (1) caps_of_state_valid_cap)
             apply (case_tac "is_zombie src_cap")
              apply (clarsimp simp add: valid_cap_def2 update_cap_data_def
                                        is_cap_simps
                              split: if_split_asm)
             apply (frule(2) zombies_final_helper [OF caps_of_state_cteD[simplified cte_wp_at_eq_simp]])
             apply (clarsimp simp: valid_cap_def2 cte_wp_at_caps_of_state)
             apply (rule conjI, clarsimp+)+

             apply (fastforce simp: is_untyped_update_cap_data
                                    weak_derived_update_cap_data[OF _ weak_derived_refl])
            apply (wp get_cap_cte_wp_at ensure_empty_cte_wp_at)+
        apply simp
        apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
       \<comment> \<open>Revoke\<close>
       apply (simp add: decode_cnode_invocation_def unlessE_whenE cong: if_cong)
       apply (wp lsfco_cte_at hoare_drop_imps whenE_throwError_wp
                  | simp add: split_beta validE_R_def[symmetric])+
       apply clarsimp
      \<comment> \<open>Delete\<close>
      apply (simp add: decode_cnode_invocation_def unlessE_whenE cong: if_cong)
      apply (wp lsfco_cte_at hoare_drop_imps whenE_throwError_wp
                 | simp add: split_beta validE_R_def[symmetric])+
      apply clarsimp
    \<comment> \<open>CancelBadgedSends\<close>
    apply (simp add: decode_cnode_invocation_def
                     unlessE_def whenE_def
               split del: if_split)
    apply (wp get_cap_wp hoare_vcg_all_liftE_R | simp add: )+
     apply (rule_tac Q'="\<lambda>rv. invs and cte_wp_at (\<lambda>_. True) rv" in hoare_strengthen_postE_R)
      apply (wp lsfco_cte_at)
     apply (clarsimp simp: cte_wp_valid_cap invs_valid_objs has_cancel_send_rights_ep_cap)+
   \<comment> \<open>Rotate\<close>
   apply (simp add: decode_cnode_invocation_def split_def
                    whenE_def unlessE_def)
   apply (rule hoare_pre)
    apply (wp get_cap_wp ensure_empty_stronger | simp)+
      apply (rename_tac dest_slot src_slot)
      apply (rule_tac Q'="\<lambda>rv s. real_cte_at rv s \<and> real_cte_at dest_slot s
                              \<and> real_cte_at src_slot s
                              \<and> ex_cte_cap_wp_to is_cnode_cap rv s
                              \<and> ex_cte_cap_wp_to is_cnode_cap dest_slot s
                              \<and> invs s" in hoare_strengthen_postE_R)
       apply wp+
      apply (clarsimp simp: cte_wp_at_caps_of_state
                     dest!: real_cte_at_cte del: impI)
      apply (frule invs_valid_objs)
      apply (simp add: update_cap_data_validI weak_derived_update_cap_data
                       caps_of_state_valid_cap)
      subgoal by (auto,(clarsimp simp:is_cap_simps update_cap_data_def)+)[1](* Bad practise *)
     apply wp+
   apply clarsimp
  apply (elim disjE exE conjE,
         simp_all add: decode_cnode_invocation_def validE_R_def
                       split_def unlessE_whenE
                split: list.split_asm
            split del: if_split)
  apply (wp | simp)+
  done

end


lemma decode_cnode_inv_inv[wp]:
  "\<lbrace>P\<rbrace> decode_cnode_invocation mi args cap cs \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding decode_cnode_invocation_def
  apply (simp add: split_def unlessE_def whenE_def
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | simp | wpcw)+
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
  apply (clarsimp simp: cte_wp_at_neg split: if_split)
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
  apply (clarsimp simp: is_final_cap'_def gen_obj_refs_def)
  apply (subgoal_tac "{p1, p2} \<subseteq> {(a, b)}")
   apply simp
  apply (drule sym[where s="Collect p" for p], simp)
  apply blast
  done


lemma final_cap_duplicate_irq:
  "\<lbrakk> fst (get_cap p1 s) = {(cap1, s)}; fst (get_cap p2 s) = {(cap2, s)}; is_final_cap' cap1 s;
     x \<in> cap_irqs cap1; p1 \<noteq> p2 \<rbrakk> \<Longrightarrow> x \<notin> cap_irqs cap2"
  apply (clarsimp simp: is_final_cap'_def gen_obj_refs_def)
  apply (subgoal_tac "{p1, p2} \<subseteq> {(a, b)}")
   apply simp
  apply (drule sym[where s="Collect p" for p], simp)
  apply blast
  done

lemma final_cap_duplicate_arch_refs:
  "\<lbrakk> fst (get_cap p1 s) = {(cap1, s)}; fst (get_cap p2 s) = {(cap2, s)}; is_final_cap' cap1 s;
     x \<in> arch_gen_refs cap1; p1 \<noteq> p2 \<rbrakk> \<Longrightarrow> x \<notin> arch_gen_refs cap2"
  apply (clarsimp simp: is_final_cap'_def gen_obj_refs_def)
  apply (subgoal_tac "{p1, p2} \<subseteq> {(a, b)}")
   apply simp
  apply (drule sym[where s="Collect p" for p], simp)
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
     \<and> cte_wp_at ((=) c1) p1 s
     \<and> cte_wp_at ((=) c2) p2 s
     \<and> p1 \<noteq> p2\<rbrace>
     cap_swap c1 p1 c2 p2
   \<lbrace>\<lambda>rv s. card (not_recursive_cspaces s) < n\<rbrace>"
  apply (cases "p1 = p2", simp_all)
  apply (simp add: cap_swap_def set_cdt_def when_def)
  apply (rule hoare_weaken_pre)
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
   unfolding cap_swap_for_delete_def
   by (wpsimp wp: cap_swap_not_recursive get_cap_wp)


lemma set_mrs_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_mrs p' b m \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_mrs_def bind_assoc set_object_def get_object_def)
  apply (cases b)
   apply simp
   apply wp
   apply clarsimp
   apply (drule get_tcb_SomeD)
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: zipWithM_x_mapM split_def
             split del: if_split)
  apply (wp mapM_wp')
  apply clarsimp
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def)
  done


lemma cte_wp_and:
  "cte_wp_at (P and Q) c s = (cte_wp_at P c s \<and> cte_wp_at Q c s)"
  by (auto simp: cte_wp_at_def)


lemmas cte_wp_and' = cte_wp_and [unfolded pred_conj_def]


lemma in_pspace_typ_at:
  "r \<notin> dom (kheap s) = (\<forall>T. \<not> typ_at T r s)"
  apply (simp add: dom_def)
  apply (subst simp_thms(2)[symmetric])
  apply (fastforce simp: obj_at_def)
  done

lemma prepare_thread_delete_not_recursive:
  "\<lbrace>\<lambda>s. P (not_recursive_cspaces s)\<rbrace>
     prepare_thread_delete t
   \<lbrace>\<lambda>rv s. P (not_recursive_cspaces s)\<rbrace>"
  apply (simp add: not_recursive_cspaces_def cte_wp_at_caps_of_state)
  apply (wp prepare_thread_delete_caps_of_state)
  done


lemma suspend_not_recursive:
  "\<lbrace>\<lambda>s. P (not_recursive_cspaces s)\<rbrace>
     SchedContext_A.suspend t
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


lemma unbind_notification_not_recursive:
  "\<lbrace>\<lambda>s. P (not_recursive_cspaces s)\<rbrace>
     unbind_notification tcb
   \<lbrace>\<lambda>rv s. P (not_recursive_cspaces s)\<rbrace>"
  apply (simp add: not_recursive_cspaces_def cte_wp_at_caps_of_state)
  apply (wp unbind_notification_caps_of_state)
  done

lemma unbind_from_sc_not_recursive:
  "\<lbrace>\<lambda>s. P (not_recursive_cspaces s)\<rbrace>
     unbind_from_sc tcb
   \<lbrace>\<lambda>rv s. P (not_recursive_cspaces s)\<rbrace>"
  apply (simp add: not_recursive_cspaces_def cte_wp_at_caps_of_state)
  apply (wp unbind_notification_caps_of_state)
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
       ((map_prod (\<lambda>(x, s). (FinaliseSlotCall x True, s)) (\<lambda>(x, s). (FinaliseSlotCall x True, s)) ` S)
         \<union> (map_prod (\<lambda>(x, s). (FinaliseSlotCall x False, s)) (\<lambda>(x, s). (FinaliseSlotCall x False, s)) ` S))"


lemma wf_rdcall_finalise_ord_lift:
  "wf S \<Longrightarrow> wf (rdcall_finalise_ord_lift S)"
  unfolding rdcall_finalise_ord_lift_def
  by (auto intro!: wf_mlex wf_Un wf_map_prod_image inj_onI)


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
  "(rv, s') \<in> fst (get_cap p s) = (s = s' \<and> cte_wp_at ((=) rv) p s)"
  apply (rule iffI)
   apply (clarsimp dest!: get_cap_det2 simp: cte_wp_at_def)
  apply (clarsimp simp: cte_wp_at_def)
  done


lemma fst_cte_ptrs_first_cte_of:
  "fst_cte_ptrs (cap.Zombie ptr zb n) = {first_cslot_of (cap.Zombie ptr zb n)}"
  by (simp add: fst_cte_ptrs_def tcb_cnode_index_def)


lemma final_cap_still_at:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>c. gen_obj_refs cap = gen_obj_refs c
                         \<and> P cap (is_final_cap' c s)) ptr s\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. P c (is_final_cap' c s)) ptr s\<rbrace>"
  apply (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state)
  apply wp
  apply (clarsimp elim!: rsubst[where P="P cap"])
  apply (intro ext arg_cong[where f=Ex] arg_cong[where f=All])
  apply (case_tac "(aa, ba) = ptr", simp_all add: gen_obj_refs_def)
  done


lemma suspend_thread_cap:
  "\<lbrace>\<lambda>s. caps_of_state s x = Some (cap.ThreadCap p)\<rbrace>
     SchedContext_A.suspend t
   \<lbrace>\<lambda>rv s. caps_of_state s x = Some (cap.ThreadCap p)\<rbrace>"
  apply (rule hoare_chain)
    apply (rule suspend_cte_wp_at_preserved
                  [where p=x and P="(=) (cap.ThreadCap p)"])
    apply (clarsimp simp add: can_fast_finalise_def)
   apply (simp add: cte_wp_at_caps_of_state)+
  done

lemma not_recursive_cspaces_preemption_point_independent[intro!, simp]:
  "not_recursive_cspaces (s\<lparr>machine_state := ms\<rparr>) = not_recursive_cspaces s"
  by (simp add: not_recursive_cspaces_def)

lemma not_recursive_cspaces_time_independent_simple[simp]:
  "not_recursive_cspaces (s \<lparr> cur_time := t \<rparr>) = not_recursive_cspaces s"
  "not_recursive_cspaces (s \<lparr> consumed_time := t' \<rparr>) = not_recursive_cspaces s"
  "not_recursive_cspaces (s \<lparr> domain_time := t'' \<rparr>) = not_recursive_cspaces s"
  "not_recursive_cspaces (s \<lparr> reprogram_timer := t''' \<rparr>) = not_recursive_cspaces s"
  by (simp add: not_recursive_cspaces_def)+

context CNodeInv_AI begin

crunch update_time_stamp
   for not_recursive_cspaces[wp]: "\<lambda>s. P (not_recursive_cspaces s)"
   and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
   (simp: crunch_simps wp: crunch_wps)

crunch preemption_point
  for not_recursive_cspaces[wp]: "\<lambda>s. P (not_recursive_cspaces s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: OR_choiceE_weak_wp hoare_drop_imp simp: preemption_point_def)

lemma rec_del_termination:
  "All (rec_del_dom :: rec_del_call \<times> 'state_ext state \<Rightarrow> bool)"
  apply (rule rec_del.termination[OF rec_del_recset_wf]
         ; simp add: rec_del_recset_def wf_sum_def rdcall_finalise_ord_lift_def mlex_prod_def
                     is_final_cap_def)
  apply (case_tac exposed; simp)
   apply (rule disjI1, rule map_prod_split_imageI, clarsimp)
   apply (erule use_valid [OF _ preemption_point_caps_of_state])
   apply (case_tac aa, simp_all add: fail_def rec_del.psimps)[1]
   apply (rename_tac word option nat)
    apply (case_tac nat; simp)
   apply (clarsimp simp: in_monad rec_del.psimps)
   apply (clarsimp simp: in_monad in_get_cap_cte_wp_at cte_wp_at_caps_of_state rec_del.psimps
                  split: if_split_asm)
    apply (erule use_valid [OF _ set_cap_caps_of_state])+
    apply (simp add: fst_cte_ptrs_first_cte_of cong: if_cong)
    apply (case_tac rv, simp_all)[1]
    apply (clarsimp simp: in_monad fst_cte_ptrs_first_cte_of)
   apply (case_tac new_cap, simp_all add: is_cap_simps)[1]
    apply (case_tac rv, simp_all)[1]
   apply (clarsimp simp: fst_cte_ptrs_first_cte_of)
   apply (case_tac rv, simp_all)[1]
   apply (clarsimp simp: fst_cte_ptrs_first_cte_of in_monad)
  apply (rule disjI2, rule map_prod_split_imageI, clarsimp)
  apply (erule use_valid [OF _ preemption_point_not_recursive_cspaces])
  apply (case_tac aa, simp_all add: fail_def rec_del.psimps)[1]
  apply (rename_tac word option nat)
  apply (case_tac nat, simp_all)
  apply (clarsimp simp: in_monad prod_eqI rec_del.psimps)
  apply (erule use_valid [OF _ cap_swap_fd_not_recursive])
  apply (frule use_valid [OF _ get_cap_cte_wp_at], simp)
  apply (drule in_inv_by_hoareD [OF get_cap_inv])
  apply clarsimp
  apply (erule use_valid [OF _ hoare_vcg_conj_lift [OF set_zombie_not_recursive final_cap_still_at]])
  apply (frule use_valid [OF _ finalise_cap_cases])
   apply (fastforce simp add: cte_wp_at_eq_simp)
  apply clarsimp
  apply (case_tac rv, simp_all add: fst_cte_ptrs_def in_monad cte_wp_at_caps_of_state)
  apply (clarsimp split: if_split_asm)
  apply (frule (1) use_valid [OF _ unbind_notification_caps_of_state],
         frule (1) use_valid [OF _ unbind_from_sc_caps_of_state],
         frule (1) use_valid [OF _ suspend_thread_cap],
         frule (1) use_valid [OF _ prepare_thread_delete_thread_cap])
  apply (erule use_valid [OF _ prepare_thread_delete_not_recursive])
  apply (erule use_valid [OF _ suspend_not_recursive])
  apply (erule use_valid [OF _ unbind_from_sc_not_recursive])
  apply (erule use_valid [OF _ unbind_notification_not_recursive])
  apply simp
  done

lemma rec_del_dom: "\<And> (p :: rec_del_call \<times> 'state_ext state). rec_del_dom p"
  using rec_del_termination by blast

lemmas rec_del_simps = rec_del.psimps[OF rec_del_dom]

lemmas rec_del_simps_ext =
    rec_del_simps [THEN ext[where f="rec_del args" for args]]

lemmas rec_del_fails = spec_validE_fail rec_del_simps_ext(5-)

declare assertE_wp[wp]
declare unlessE_wp[wp_split]

lemma without_preemption_wp [wp_split]:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> without_preemption f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by simp

lemmas rec_del_induct = rec_del.pinduct[OF rec_del_dom]

lemma rec_del_preservationE':
  fixes s :: "'state_ext state"
  fixes P :: "'state_ext state \<Rightarrow> bool"
  assumes wp:
    "\<And>sl1 sl2. \<lbrace>P\<rbrace> cap_swap_for_delete sl1 sl2 \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl cap. \<lbrace>P\<rbrace> set_cap sl cap \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>sl opt. \<lbrace>P\<rbrace> empty_slot sl opt \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<And>cap fin. \<lbrace>P\<rbrace> finalise_cap cap fin \<lbrace>\<lambda>rv. P\<rbrace>"
    "\<lbrace>P\<rbrace> preemption_point \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. E\<rbrace>"
  shows
  "s \<turnstile> \<lbrace>P\<rbrace> rec_del call \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. E\<rbrace>"
proof (induct rule: rec_del_induct)
  case (1 slot exposed s)
  show ?case
    apply (subst rec_del_simps)
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
    apply (subst rec_del_simps)
    apply (simp only: split_def)
    apply (wp wp "2.hyps")
         apply (wp wp)[1]
        apply (rule "2.hyps", assumption+)
       apply (wp wp hoare_drop_imps | simp add: is_final_cap_def)+
    done
next
  case 3
  show ?case
    apply (simp add: rec_del_simps | wp wp)+
    done
next
  case (4 ptr bits n slot s)
  show ?case
    apply (subst rec_del_simps)
    apply (wp wp)
      apply (wp hoare_drop_imps)[1]
     apply (simp only: simp_thms)
     apply (rule "4.hyps", assumption+)
    apply wp
    done
qed (auto simp: rec_del_dom rec_del_fails)

lemmas rec_del_preservation'
  = rec_del_preservationE'[where P=P and E=P for P, OF _ _ _ _ valid_validE]

lemmas rec_del_preservationE =
       use_spec(2)[OF rec_del_preservationE']

lemmas rec_del_preservation[crunch_rules] =
       validE_valid [OF use_spec(2) [OF rec_del_preservation']]

end


crunch cap_swap_for_delete
  for typ_at: "\<lambda>s. P (typ_at T p s)"

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


context CNodeInv_AI begin

crunch rec_del
 for typ_at[wp]: "\<lambda>s::'state_ext state. P (typ_at T p s)"
  (ignore: preemption_point wp: preemption_point_inv)

lemma rec_del_cte_at[wp]:
  "rec_del call \<lbrace>cte_at c :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cte_at_typ)

lemma rec_del_cap_table_at[wp]:
  "rec_del call \<lbrace>cap_table_at bits c :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  by (wp cap_table_at_typ_at)

end


lemma cnode_to_zombie_valid:
  "\<lbrakk> s \<turnstile> cap.CNodeCap oref bits guard \<rbrakk>
    \<Longrightarrow> s \<turnstile> cap.Zombie oref (Some bits) (2 ^ bits)"
  by (clarsimp simp: valid_cap_def cap_table_at_cte_at
                     word_unat_power cap_aligned_def)


lemma tcb_to_zombie_valid:
  "\<lbrakk> s \<turnstile> cap.ThreadCap t \<rbrakk>
    \<Longrightarrow> s \<turnstile> cap.Zombie t None 5"  (* RT? *)
  apply (simp add: valid_cap_def)
  apply (simp add: cap_aligned_def)
  done


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


context mdb_swap_abs_invs begin

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
  apply (simp add: n_def n'_def cs'_def split: if_split_asm)
        apply fastforce+
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
    apply (simp add: weak_derived_cap_range)
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
  apply (wp | simp del: fun_upd_apply split del: if_split)+
  apply (fold swap_mdb_def [simplified Let_def])
  apply (wp set_cap_caps_of_state2 get_cap_wp)+
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
              del: fun_upd_apply
              split del: if_split)
  apply (rule conjI)
   apply (erule mdb_swap_abs_invs.descendants_inc_n)
  apply (rule conjI)
   apply (erule mdb_swap_abs_invs.untyped_inc_n)
    apply (clarsimp simp:cte_wp_at_caps_of_state)+
  apply (rule conjI)
   apply (simp add: ut_revocable_def weak_derived_ranges del: split_paired_All)
   apply (simp add: irq_revocable_def del: split_paired_All)
   apply (intro conjI impI allI)
    apply (simp del: split_paired_All)
   apply (simp del: split_paired_All)
  apply (clarsimp simp: valid_arch_mdb_cap_swap)
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
           | simp split del: if_split)+
  done


crunch cap_swap
  for aligned[wp]: "pspace_aligned"

crunch cap_swap
  for disctinct[wp]: "pspace_distinct"


lemma cap_swap_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap and cte_wp_at (\<lambda>x. zobj_refs x = zobj_refs c) a
          and cte_wp_at (\<lambda>x. zobj_refs x = zobj_refs c') b\<rbrace>
     cap_swap c a c' b
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (wp | simp split del: if_split)+
     apply (rule hoare_post_imp)
      apply (simp only: if_live_then_nonz_cap_def ex_nonz_cap_to_def
                        cte_wp_at_caps_of_state imp_conv_disj)
     apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_ex_lift
               get_cap_wp)+
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
  apply (wp get_cap_wp | simp split del: if_split del: split_paired_Ex)+
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
  apply (wp get_cap_wp | simp del: fun_upd_apply split del: if_split)+
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
  apply fastforce
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
  apply (clarsimp split del: if_split del: disjCI intro!: disjCI2)
  apply (intro conjI)
    apply (clarsimp split: if_split_asm)
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
                                   \<and> gen_obj_refs x = gen_obj_refs c) a
          and cte_wp_at (\<lambda>x. is_zombie x = is_zombie c' \<and> gen_obj_refs x = gen_obj_refs c') b\<rbrace>
     cap_swap c a c' b
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp only: zombies_final_def final_cap_at_eq
                    cte_wp_at_caps_of_state simp_thms pred_conj_def)
  apply wp
  apply (elim conjE)
  apply (erule allfEI[where f="id ( a := b, b := a )"])
  apply (intro impI)
  apply (drule mp)
   apply (clarsimp split: if_split_asm)
  apply (elim exE conjE, simp only: simp_thms option.simps)
  apply (rule conjI)
   apply (clarsimp simp: is_cap_simps gen_obj_refs_def)
  apply (erule allfEI[where f="id ( a := b, b := a )"])
  apply (intro impI, elim exE conjE, simp only: simp_thms option.simps gen_obj_refs_eq)
  apply (clarsimp simp: gen_obj_refs_Int split: if_split_asm)
  done


lemma cap_swap_fd_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace>
     cap_swap_for_delete p p'
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma cap_swap_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> cap_swap c sl c' sl' \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  unfolding cap_swap_def by (wp | simp)+


crunch cap_swap
 for refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  (ignore: set_cap simp: state_refs_of_pspaceI)

crunch cap_swap
  for hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (ignore: set_cap simp: state_refs_of_pspaceI)

crunch cap_swap
  for cur_tcb[wp]: "cur_tcb"

crunch cap_swap
 for cur_sc_tcb[wp]: "cur_sc_tcb"

lemma copy_of_cte_refs:
  "copy_of cap cap' \<Longrightarrow> cte_refs cap = cte_refs cap'"
  apply (rule ext, clarsimp simp: copy_of_def split: if_split_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm)+
  done


lemma copy_of_is_zombie:
  "copy_of cap cap' \<Longrightarrow> is_zombie cap = is_zombie cap'"
  apply (clarsimp simp: copy_of_def split: if_split_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       apply (clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm)+
  done


lemma copy_of_cap_irqs:
  "copy_of cap cap' \<Longrightarrow> cap_irqs cap = cap_irqs cap'"
  apply (clarsimp simp: copy_of_def cap_irqs_def split: if_split_asm)
  apply (cases cap', simp_all add: same_object_as_def)
       by (clarsimp simp: is_cap_simps bits_of_def cap_range_def
                      split: cap.split_asm)+

lemma copy_of_arch_gen_obj_refs:
  "copy_of cap cap' \<Longrightarrow> arch_gen_refs cap = arch_gen_refs cap'"
  apply (clarsimp simp: copy_of_def split: if_split_asm)
  by (cases cap'; clarsimp simp: same_object_as_def is_cap_simps same_aobject_same_arch_gen_refs
                          split: cap.split_asm)

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

crunch cap_swap
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_global_objs[wp]: valid_global_objs
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and fault_tcbs_valid_states[wp]: fault_tcbs_valid_states

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
                 elim!: ranE split: if_split_asm
                 dest!: weak_derived_cap_irqs)
    apply auto
  done

context CNodeInv_AI begin

lemma cap_swap_valid_arch_caps[wp]:
  "\<And>c a c' b.
    \<lbrace>valid_arch_caps and cte_wp_at (weak_derived c) a and cte_wp_at (weak_derived c') b\<rbrace>
      cap_swap c a c' b
    \<lbrace>\<lambda>rv. valid_arch_caps :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (simp add: cap_swap_def)
  apply (rule hoare_pre)
   apply (subst bind_assoc[symmetric],
          rule bind_wp_fwd,
          rule swap_of_caps_valid_arch_caps)
   apply (wp | simp split del: if_split)+
  done

end

crunch cap_swap
  for valid_kernel_mappings[wp]: valid_kernel_mappings
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and only_idle[wp]: only_idle
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and machine_state[wp]: "\<lambda>s. P(machine_state s)"
  and valid_irq_states[wp]: valid_irq_states
  and pspace_respects_device_region[wp]: pspace_respects_device_region

lemma cap_swap_valid_ioc[wp]:
  "\<lbrace>\<lambda>s. valid_ioc s \<and>
    cte_wp_at (weak_derived c) p s \<and>
    cte_wp_at (weak_derived c') p' s\<rbrace>
    cap_swap c p c' p'
   \<lbrace>\<lambda>_ s. valid_ioc s\<rbrace>"
  apply (simp add: cap_swap_def valid_ioc_def cte_wp_at_caps_of_state)
  apply (wp set_cdt_cos_ioc set_cap_caps_of_state2 | simp split del: if_split)+
  apply (cases p, cases p')
  apply fastforce
  done

lemma cap_refs_respects_device_region_original_cap[wp]:
  "cap_refs_respects_device_region
                (s\<lparr>is_original_cap := ocp\<rparr>) = cap_refs_respects_device_region s"
  by (simp add:cap_refs_respects_device_region_def)

crunch set_cdt
  for obj_at[wp]: "\<lambda>s. P (obj_at P' p s)"

global_interpretation cap_swap: cspace_op "cap_swap c a c' b"
  supply if_split[split del]
  apply unfold_locales
  apply (wpsimp simp: cap_swap_def wp: set_cap.cspace_agnostic_obj_at)
  done

context CNodeInv_AI begin
lemma cap_swap_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region and cte_wp_at (weak_derived c) a and cte_wp_at (weak_derived c') b\<rbrace>
    cap_swap c a c' b \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add:cap_swap_def)
  apply wp
         apply (simp add: cap_refs_respects_device_region_def)
        apply (rule hoare_strengthen_post[OF CSpace_AI.set_cdt_cap_refs_respects_device_region])
        apply simp
       apply wp+
    apply (clarsimp simp add: cap_refs_respects_device_region_def cte_wp_at_caps_of_state
                              cap_range_respects_device_region_def
                    simp del: split_paired_All split_paired_Ex
           | (wp hoare_vcg_all_lift hoare_vcg_imp_lift)+)+
  apply (frule_tac x = a in spec)
  apply (frule_tac x = b in spec)
  apply (clarsimp simp: weak_derived_cap_range)
  apply (intro conjI impI allI)
       apply (simp add: weak_derived_cap_range weak_derived_cap_is_device)+
      apply (rule ccontr)
      apply simp
     apply (rule disjI2)
     apply (intro conjI impI)
      apply (simp add: weak_derived_cap_range weak_derived_cap_is_device)+
     apply (rule ccontr)
     apply simp
    apply (simp add: weak_derived_cap_range weak_derived_cap_is_device)+
   apply (rule ccontr)
   apply simp
  apply (rule disjI2)
  apply (rule ccontr)
  apply (clarsimp simp add: weak_derived_cap_range weak_derived_cap_is_device)+
  apply fastforce
  done

lemma cap_swap_invs[wp]:
  "\<And>c' a c b.
  \<lbrace>invs and ex_cte_cap_wp_to (appropriate_cte_cap c') a
         and ex_cte_cap_wp_to (appropriate_cte_cap c) b and
    valid_cap c and valid_cap c' and
    tcb_cap_valid c b and tcb_cap_valid c' a and
    cte_wp_at (weak_derived c) a and
    cte_wp_at (\<lambda>cc. is_untyped_cap cc \<longrightarrow> cc = c) a and
    cte_wp_at (weak_derived c') b and
    cte_wp_at (\<lambda>cc. is_untyped_cap cc \<longrightarrow> cc = c') b and K (a \<noteq> b)\<rbrace>
   cap_swap c a c' b \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  apply (wp valid_arch_state_lift_aobj_at
            cap_swap_typ_at valid_irq_node_typ cap_swap.aobj_at
         | simp
         | erule disjE
         | clarsimp simp: cte_wp_at_caps_of_state copy_of_cte_refs weak_derived_def
                          copy_obj_refs copy_of_zobj_refs copy_of_is_zombie
                          copy_of_cap_irqs gen_obj_refs_eq copy_of_arch_gen_obj_refs
         | clarsimp simp: valid_global_refs_def valid_refs_def copy_of_cap_range
                          cte_wp_at_caps_of_state
                simp del: split_paired_Ex split_paired_All
         | rule conjI
         | clarsimp dest!: )+
  done

lemma cap_swap_fd_invs[wp]:
  "\<And>a b.
  \<lbrace>invs and ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) a
        and ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) b
        and (\<lambda>s. \<forall>c. tcb_cap_valid c a s)
        and (\<lambda>s. \<forall>c. tcb_cap_valid c b s)
        and cte_at a and cte_at b\<rbrace>
   cap_swap_for_delete a b \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (simp add: cap_swap_for_delete_def)
  apply (wp get_cap_wp)
  apply (clarsimp)
  apply (strengthen cap_irqs_appropriate_strengthen, simp)
  apply (rule conjI, fastforce dest: cte_wp_at_valid_objs_valid_cap)
  apply (rule conjI, fastforce dest: cte_wp_at_valid_objs_valid_cap)
  apply (clarsimp simp: cte_wp_at_caps_of_state weak_derived_def)
  done

end


lemma final_cap_unchanged:
  assumes x: "\<And>P p. \<lbrace>cte_wp_at P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  assumes y: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>is_final_cap' cap\<rbrace> f \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  apply (simp only: is_final_cap'_def3 imp_conv_disj de_Morgan_conj)
  apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift x hoare_vcg_disj_lift
            valid_cte_at_neg_typ [OF y])
  done


lemmas set_cap_cte_wp_at_cases = set_cap_cte_wp_at[simplified if_bool_eq_conj pred_conj_def conj_comms]


lemma cyclic_zombieD[dest!]:
  "cap_cyclic_zombie cap sl
    \<Longrightarrow> \<exists>p zb n. cap = cap.Zombie p zb n
        \<and> sl = (p, replicate (zombie_cte_bits zb) False)"
  by (cases cap, simp_all add: cap_cyclic_zombie_def)


context CNodeInv_AI begin

lemma rec_del_abort_cases:
  "\<And>args (s::'state_ext state).
  case args of FinaliseSlotCall sl ex \<Rightarrow> s \<turnstile> \<lbrace>\<top>\<rbrace>
     rec_del (FinaliseSlotCall sl ex)
   \<lbrace>\<lambda>rv s. (fst rv) \<or> (\<not> ex \<and> cte_wp_at (\<lambda>c. is_zombie c \<and> sl \<in> fst_cte_ptrs c) sl s)\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>
      | _ \<Rightarrow> True"
  subgoal for args s
  proof (induct rule: rec_del_induct)
    case (2 slot exposed)
    note wp = "2.hyps"[simplified rec_del_call.simps]
    show ?case
      apply (subst rec_del_simps_ext)
      apply (simp only: rec_del_call.simps split_def)
      apply wp
          apply (simp add: cte_wp_at_caps_of_state)
          apply (wp wp)+
           apply (wp irq_state_independent_AI | simp)+
        apply (rule hoare_strengthen_post)
         apply (rule finalise_cap_cases[where slot=slot])
        apply clarsimp
        apply (fastforce simp: fst_cte_ptrs_def)
       apply (simp add: is_final_cap_def | wp get_cap_wp)+
      done
  qed (simp_all add: rec_del_fails)
  done


lemma rec_del_delete_cases:
  "\<And>sl ex.
    \<lbrace>\<top> :: 'state_ext state \<Rightarrow> bool\<rbrace>
      rec_del (CTEDeleteCall sl ex)
    \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. c = cap.NullCap \<or> \<not> ex \<and> is_zombie c \<and> sl \<in> fst_cte_ptrs c) sl s\<rbrace>,-"
  subgoal for sl ex
  using rec_del_abort_cases [where args="FinaliseSlotCall sl ex"]
  apply (subst rec_del_simps_ext, simp add: split_def)
  apply wp
    apply (rule hoare_strengthen_post [OF empty_slot_deletes])
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (rule use_spec, rule spec_strengthen_postE, assumption)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply assumption
  done
  done

lemma cap_delete_deletes:
  notes hoare_pre [wp_pre del]
  shows
    "\<And>p.
    \<lbrace>\<top> :: 'state_ext state \<Rightarrow> bool\<rbrace>
      cap_delete p
    \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) p\<rbrace>,-"
  subgoal for p
    unfolding cap_delete_def
    using rec_del_delete_cases[where sl=p and ex=True]
    apply (simp add: validE_R_def)
    apply wp
    done
  done

end


lemma final_cap_same_objrefs:
  "\<lbrace>is_final_cap' cap and
    cte_wp_at (\<lambda>c. obj_refs cap \<inter> obj_refs c \<noteq> {}
                     \<or> cap_irqs cap \<inter> cap_irqs c \<noteq> {}
                     \<or> arch_gen_refs cap \<inter>
                            arch_gen_refs c \<noteq> {}) ptr\<rbrace>
     set_cap cap ptr \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  apply (simp only: is_final_cap'_def3 pred_conj_def
                    cte_wp_at_caps_of_state)
  apply wp
  apply (clarsimp simp del: split_paired_Ex split_paired_All)
  apply (rule_tac x=ptr in exI)
  apply (subgoal_tac "(a, b) = ptr")
   apply clarsimp
  apply (erule_tac x="ptr" in allE)
  apply (fastforce simp: gen_obj_refs_Int)
  done


lemma cte_wp_at_weakenE_customised:
  "\<lbrakk>cte_wp_at P t s; \<And>c. \<lbrakk> P c; cte_wp_at ((=) c) t s \<rbrakk> \<Longrightarrow> P' c\<rbrakk> \<Longrightarrow> cte_wp_at P' t s"
  by (clarsimp simp: cte_wp_at_def)


lemma final_cap_at_same_objrefs:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>c.  obj_refs c \<noteq> {} \<and> is_final_cap' c s) p s
      \<and> cte_wp_at (\<lambda>c. gen_obj_refs cap = gen_obj_refs c) ptr s \<and> p \<noteq> ptr\<rbrace>
     set_cap cap ptr \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s\<rbrace>"
  apply (simp only: final_cap_at_eq cte_wp_at_conj)
  apply (simp add: cte_wp_at_caps_of_state)
  apply wp
  apply (clarsimp simp del: split_paired_All split_paired_Ex
                      simp: gen_obj_refs_Int gen_obj_refs_empty gen_obj_refs_eq)
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
  assumes x: "\<And>P p. \<lbrace>cte_wp_at (\<lambda>c. P (gen_obj_refs c)) p\<rbrace> f
                  \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. P (gen_obj_refs c)) p\<rbrace>"
  assumes y: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s\<rbrace> f
                \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s\<rbrace>"
proof -
  have final_cap_at_eq':
    "\<And>p s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s =
    (\<exists>cp. cte_wp_at (\<lambda>c. gen_obj_refs c = gen_obj_refs cp) p s
              \<and> (obj_refs cp \<noteq> {} \<or> cap_irqs cp \<noteq> {} \<or> arch_gen_refs cp \<noteq> {})
       \<and> (\<forall>p'. (cte_at p' s \<and> p' \<noteq> p) \<longrightarrow>
                cte_wp_at (\<lambda>c. gen_obj_refs cp \<inter> gen_obj_refs c = {}) p' s))"
    apply (simp add: final_cap_at_eq cte_wp_at_def)
    apply (rule iffI)
     apply (clarsimp simp: gen_obj_refs_Int gen_obj_refs_empty gen_obj_refs_eq)
     apply (rule exI, rule conjI, rule refl)
     apply clarsimp
    apply (clarsimp simp: gen_obj_refs_Int gen_obj_refs_empty gen_obj_refs_eq)
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
     unat (of_bl y :: machine_word) = 0; unat (of_bl z :: machine_word) = 0;
     y \<in> dom cs; z \<in> dom cs \<rbrakk> \<Longrightarrow> y = z"
  apply (simp add: unat_eq_0)
  apply (frule invs_valid_objs, erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_cs_def
                        valid_cs_size_def well_formed_cnode_n_def)
  apply (rule word_same_bl_memo_unify_word_type[where 'a=machine_word_len])
    apply simp
   apply simp
  apply (simp add: word_bits_def)
  done


lemma final_zombie_not_live:
  "\<lbrakk> is_final_cap' (cap.Zombie ptr b n) s; cte_wp_at ((=) (cap.Zombie ptr b n)) p s;
     if_live_then_nonz_cap s \<rbrakk>
     \<Longrightarrow> \<not> obj_at live ptr s"
  apply clarsimp
  apply (drule(1) if_live_then_nonz_capD, simp)
  apply (clarsimp simp: ex_nonz_cap_to_def zobj_refs_to_obj_refs)
  apply (subgoal_tac "(a, ba) \<noteq> p")
   apply (clarsimp simp: is_final_cap'_def)
   apply (erule(1) obvious)
    apply (clarsimp simp: cte_wp_at_def is_zombie_def gen_obj_refs_Int)+
  done


lemma suspend_ex_cte_cap[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace> SchedContext_A.suspend t \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
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
  apply (rule word_same_bl_memo_unify_word_type[where 'a='a]; simp)
  done


context CNodeInv_AI begin

lemma zombie_is_cap_toE:
  "\<And>ptr zbits n p (s::'state_ext state) m P.
    \<lbrakk> cte_wp_at ((=) (Zombie ptr zbits n)) p s; invs s; m < n; P (Zombie ptr zbits n) \<rbrakk>
      \<Longrightarrow> ex_cte_cap_wp_to P (ptr, nat_to_cref (zombie_cte_bits zbits) m) s"
  unfolding ex_cte_cap_wp_to_def
  apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp)
  apply (intro exI, erule cte_wp_at_weakenE)
  apply clarsimp
  apply (drule(2) zombie_is_cap_toE_pre, simp)
  done

end

lemma zombie_is_cap_toE2:
  "\<lbrakk> cte_wp_at ((=) (cap.Zombie ptr zbits n)) p s; 0 < n;
             P (cap.Zombie ptr zbits n) \<rbrakk>
     \<Longrightarrow> ex_cte_cap_wp_to P (ptr, replicate (zombie_cte_bits zbits) False) s"
  unfolding ex_cte_cap_wp_to_def
  apply (rule exI, erule cte_wp_at_weakenE)
  apply clarsimp
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


context CNodeInv_AI begin

lemma nat_to_cref_replicate_Zombie:
  "\<And>zb n (s::'state_ext state) p m.
    \<lbrakk> nat_to_cref (zombie_cte_bits zb) n = replicate (zombie_cte_bits zb) False;
        s \<turnstile> cap.Zombie p zb m; n < m \<rbrakk>
      \<Longrightarrow> n = 0"
  apply (subgoal_tac "unat (of_bl (nat_to_cref (zombie_cte_bits zb) n)) = 0")
   apply (subst(asm) unat_of_bl_nat_to_cref)
     apply (drule valid_Zombie_n_less_cte_bits, simp)
    apply (erule zombie_cte_bits_less)
   apply simp
  apply simp
  done

end


lemma replicate_False_tcb_valid[simp]:
  "tcb_cap_valid cap (p, replicate n False) s"
  apply (clarsimp simp: tcb_cap_valid_def st_tcb_def2 tcb_at_def)
  apply (rule conjI)
   apply (clarsimp split: option.split)
   apply (frule tcb_cap_cases_length[OF domI])
   apply (clarsimp simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1)
  apply (cases n; clarsimp simp: tcb_cnode_index_def dest!: replicate_not_True[OF sym])
  done


lemma tcb_valid_nonspecial_cap:
  "\<lbrakk> caps_of_state s p = Some cap; valid_objs s;
       \<forall>ptr st. \<forall>(getF, setF, restr) \<in> ran tcb_cap_cases.
                    \<not> restr ptr st cap \<or> (\<forall>cap. restr ptr st cap);
       \<forall>ptr. (is_nondevice_page_cap cap \<or> cap = cap.NullCap) \<and>
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

lemma sched_context_cancel_yield_to_halted:
  "sched_context_cancel_yield_to thread \<lbrace>st_tcb_at halted thread\<rbrace>"
  apply (clarsimp simp: sched_context_cancel_yield_to_def get_tcb_obj_ref_def)
  apply (wpsimp wp: thread_get_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb_def)
  done

lemma suspend_makes_halted[wp]:
  "\<lbrace>valid_objs\<rbrace> SchedContext_A.suspend thread \<lbrace>\<lambda>_. st_tcb_at halted thread\<rbrace>"
  unfolding SchedContext_A.suspend_def
  apply (simp flip: bind_assoc)
  apply (rule bind_wp[OF sched_context_cancel_yield_to_halted])
  apply (simp add: bind_assoc)
  apply (wp hoare_strengthen_post [OF sts_st_tcb_at] gbn_wp
         | clarsimp elim!: pred_tcb_weakenE)+
  done

lemmas tcb_at_cte_at_2 = tcb_at_cte_at [where ref="tcb_cnode_index 2",
                                        simplified dom_tcb_cap_cases]


declare thread_set_Pmdb [wp]


declare get_irq_slot_real_cte [wp]

crunch empty_slot
 for cte_at_pres[wp]: "cte_at sl"


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


lemma real_cte_at_not_tcb:
  "real_cte_at sl s \<Longrightarrow> \<not> tcb_at (fst sl) s"
  apply (simp add: tcb_at_typ obj_at_def)
  apply (clarsimp simp: is_cap_table_def)
  done


context CNodeInv_AI_2 begin

lemma rec_del_invs:
 "\<And>args.
    \<lbrace>invs and valid_rec_del_call args
          and (\<lambda>s. \<not> exposed_rdcall args
                 \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) (slot_rdcall args) s)
          and (\<lambda>s. case args of ReduceZombieCall cap sl ex \<Rightarrow>
                         \<not> cap_removeable cap sl
                         \<and> (\<forall>t\<in>obj_refs cap. halted_if_tcb t s)
                    | _ \<Rightarrow> True)\<rbrace>
      rec_del args
    \<lbrace>\<lambda>rv. invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule validE_valid)
  apply (rule hoare_strengthen_postE)
  apply (rule hoare_pre)
    apply (rule use_spec)
    apply (rule rec_del_invs')
   apply simp+
  done

lemma cap_delete_invs[wp]:
  "\<And>ptr.
    \<lbrace>invs :: 'state_ext state \<Rightarrow> bool\<rbrace>
      cap_delete ptr
    \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding cap_delete_def
  apply (rule hoare_pre, wp rec_del_invs)
  apply simp
  done

lemma cap_delete_tcb[wp]:
 "\<And>t ptr. \<lbrace>tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace> cap_delete ptr \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  unfolding cap_delete_def
  by (simp add: tcb_at_typ | wp rec_del_typ_at)+

lemma cap_delete_valid_cap[wp]:
  "\<And>c p. \<lbrace>valid_cap c :: 'state_ext state \<Rightarrow> bool\<rbrace> cap_delete p \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  unfolding cap_delete_def
  by (wp valid_cap_typ | simp)+

lemma cap_delete_cte_at[wp]:
  "\<And>c p. \<lbrace>cte_at c :: 'state_ext state \<Rightarrow> bool\<rbrace> cap_delete p \<lbrace>\<lambda>_. cte_at c\<rbrace>"
  unfolding cap_delete_def by wpsimp

lemma cap_delete_cap_table_at[wp]:
  "cap_delete p \<lbrace>cap_table_at bits c :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  unfolding cap_delete_def by wpsimp

lemma cap_delete_typ_at[wp]:
  "\<And>P T p cref. \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace> cap_delete cref \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  unfolding cap_delete_def by wpsimp

end


lemma cap_swap_fd_st_tcb_at[wp]:
  "cap_swap_for_delete sl sl' \<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s)\<rbrace>"
  unfolding cap_swap_for_delete_def
  by (wp, simp)


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
     \<or> (mapb, mapa) \<in> measure (\<lambda>mp. \<Sum>x\<in>dom mp. rpo_measure x (mp x))"

lemma rpo_trans:
  "\<lbrakk> revoke_progress_ord mapa mapb; revoke_progress_ord mapb mapc \<rbrakk>
     \<Longrightarrow> revoke_progress_ord mapa mapc"
  apply (simp add: revoke_progress_ord_def)
  apply (elim disjE, simp_all)
  done


interpretation mult_is_add: comm_monoid_mult "(+)" "0::'a::comm_monoid_add"
    by (unfold_locales) (auto simp: field_simps)


lemma fold_Int_sub:
  assumes "finite S" "finite T"
  shows "(\<Sum>x \<in> (S \<inter> T). (f x :: nat)) = (\<Sum>x \<in> T. f x) - (\<Sum>x \<in> (T - S). f x)"
proof -
  from assms sum.union_disjoint[where A="S \<inter> T" and B="T - S" and g=f]
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
    "(mapb, mapa) \<in> measure (\<lambda>mp. \<Sum>x \<in> S \<inter> dom mp. rpo_measure x (mp x))"
  shows "revoke_progress_ord mapa mapb"
proof -
  have P: "(dom mapa - S) = (dom mapb - S)"
    by (fastforce simp: x)
  have Q: "(\<Sum>x \<in> dom mapa - S. rpo_measure x (mapa x))
            = (\<Sum>x \<in> dom mapb - S. rpo_measure x (mapb x))"
    apply (rule sum.cong)
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
   apply (wp opt_return_pres_lift | simp split del: if_split)+
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
  apply (wp get_cap_wp | simp split del: if_split)+
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
  apply (clarsimp simp: cte_wp_at_caps_of_state gen_obj_refs_empty)
  apply (drule iffD1)
   apply (simp add: gen_obj_refs_Int)
  apply (simp only:)
  apply simp
  done


lemmas empty_slot_rvk_prog' = empty_slot_rvk_prog[unfolded o_def]


crunch cancel_ipc
  for rvk_prog: "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map cap_to_rpo (caps_of_state s x))"
  (simp: crunch_simps o_def unless_def is_final_cap_def tcb_cap_cases_def
     wp: hoare_drop_imps empty_slot_rvk_prog'
         thread_set_caps_of_state_trivial)

crunch suspend
  for rvk_prog: "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map cap_to_rpo (caps_of_state s x))"
  (simp: crunch_simps o_def unless_def is_final_cap_def
     wp: crunch_wps empty_slot_rvk_prog' maybeM_inv ignore: set_tcb_obj_ref)

crunch deleting_irq_handler
  for rvk_prog: "\<lambda>s. revoke_progress_ord m (\<lambda>x. option_map cap_to_rpo (caps_of_state s x))"
  (simp: crunch_simps o_def unless_def is_final_cap_def
     wp: crunch_wps empty_slot_rvk_prog')

locale CNodeInv_AI_3 = CNodeInv_AI_2 state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself" +
  assumes finalise_cap_rvk_prog:
    "\<And>a b.
      \<lbrace>\<lambda>s::'state_ext state. revoke_progress_ord m (\<lambda>x. map_option cap_to_rpo (caps_of_state s x))\<rbrace>
        finalise_cap a b
      \<lbrace>\<lambda>_ s. revoke_progress_ord m (\<lambda>x. map_option cap_to_rpo (caps_of_state s x))\<rbrace>"
  assumes rec_del_rvk_prog:
    "\<And>(st::'state_ext state) args.
      st \<turnstile> \<lbrace>\<lambda>s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)
              \<and> (case args of ReduceZombieCall cap sl ex \<Rightarrow>
                   cte_wp_at (\<lambda>c. c = cap) sl s \<and> is_final_cap' cap s
                 | _ \<Rightarrow> True)\<rbrace>
        rec_del args
      \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"


lemmas rdcall_simps = rec_del_call.simps exposed_rdcall.simps slot_rdcall.simps


context CNodeInv_AI_3 begin

lemma cap_delete_rvk_prog:
  "\<And>m ptr.
    \<lbrace>\<lambda>s::'state_ext state. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)\<rbrace>
      cap_delete ptr
    \<lbrace>\<lambda>rv s. revoke_progress_ord m (option_map cap_to_rpo \<circ> caps_of_state s)\<rbrace>,-"
  unfolding cap_delete_def validE_R_def
  apply wpsimp
  apply (unfold validE_R_def)
  apply (rule use_spec)
   apply (rule rec_del_rvk_prog rec_del_rvk_prog[unfolded o_def])
  apply (simp add: o_def)
  done

end


lemma get_object_some: "kheap s ptr = Some ko \<Longrightarrow> get_object ptr s = ({(ko, s)}, False)"
  by (clarsimp simp: get_object_def gets_def get_def bind_def assert_def return_def gets_the_def)

lemma set_cap_id:
  "cte_wp_at ((=) c) p s \<Longrightarrow> set_cap c p s = ({((),s)}, False)"
  apply (clarsimp simp: cte_wp_at_cases)
  apply (cases p)
  apply (erule disjE)
   apply clarsimp
   apply (simp add: set_cap_def get_object_def bind_assoc exec_gets gets_the_def)
   apply (rule conjI)
    apply (clarsimp simp: set_object_def)
    apply (frule get_object_some)
    apply (drule_tac t="fun" in map_upd_triv)
    apply (clarsimp simp: bind_def get_def return_def put_def a_type_def)
    apply (cases s)
    apply simp
    apply (rule ext, simp)
   apply (clarsimp simp: get_object_def gets_def get_def bind_def assert_def return_def)
  apply clarsimp
  apply (simp add: set_cap_def get_object_def bind_assoc gets_the_def
                   exec_gets set_object_def exec_get put_def)
  apply (clarsimp simp: tcb_cap_cases_def
                 split: if_split_asm,
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
            prefer 13
            apply (rename_tac nat)
            apply (case_tac nat, simp_all)[1]
             apply fastforce+
  done


termination red_zombie_will_fail
  by (rule red_zombie_will_fail.termination [OF Wellfounded.wf_empty])


context CNodeInv_AI_3 begin

lemma reduce_zombie_cap_to:
  "\<And>cap slot exp.
    \<lbrace>invs and valid_rec_del_call (ReduceZombieCall cap slot exp) and
          (\<lambda>s. \<not> exp \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s) and
          K (\<not> cap_removeable cap slot) and
          (\<lambda>s. \<forall>t\<in>obj_refs cap. halted_if_tcb t s)\<rbrace>
      rec_del (ReduceZombieCall cap slot exp)
    \<lbrace>\<lambda>rv (s::'state_ext state). \<not> exp \<longrightarrow> ex_cte_cap_wp_to (\<lambda>cp. cap_irqs cp = {}) slot s\<rbrace>, -"
  apply (rule validE_validE_R)
  apply (rule hoare_strengthen_postE)
    apply (rule hoare_pre)
     apply (rule use_spec)
     apply (rule rec_del_invs')
    apply simp+
  done


lemma cte_at_replicate_zbits:
  "\<And>(s::'state_ext state) oref zb n.
    \<lbrakk> s \<turnstile> cap.Zombie oref zb n \<rbrakk> \<Longrightarrow> cte_at (oref, replicate (zombie_cte_bits zb) False) s"
  apply (clarsimp simp: valid_cap_def obj_at_def is_tcb is_cap_table
                 split: option.split_asm)
   apply (rule cte_wp_at_tcbI, simp)
    apply (fastforce simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1)
   apply simp
  apply (subgoal_tac "replicate x2 False \<in> dom cs")
   apply safe[1]
   apply (rule cte_wp_at_cteI, fastforce)
     apply (simp add: well_formed_cnode_n_def length_set_helper)
    apply simp
   apply simp
  apply (clarsimp simp: well_formed_cnode_n_def)
  done


lemma reduce_zombie_cap_somewhere:
  "\<And>exp cap slot.
    \<lbrace>\<lambda>s::'state_ext state. \<not> exp \<longrightarrow> (\<exists>oref cref. cte_wp_at P (oref, cref) s)\<rbrace>
      rec_del (ReduceZombieCall cap slot exp)
     \<lbrace>\<lambda>rv s. \<not> exp \<longrightarrow> (\<exists>oref cref. cte_wp_at P (oref, cref) s)\<rbrace>"
  subgoal for exp cap slot
  apply (cases exp, simp_all, wp)
  apply (cases cap, simp_all add: rec_del_fails)
  apply (rename_tac word option nat)
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
  done

end


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


text \<open>The revoke function and its properties are
        slightly easier to deal with than the delete
        function. However, its termination argument
        is complex, requiring that the delete function
        reduces the number of non-null capabilities.\<close>
definition
  cap_revoke_recset :: "((cslot_ptr \<times> 'z::state_ext state) \<times> (cslot_ptr \<times> 'z::state_ext state)) set"
where
 "cap_revoke_recset \<equiv> measure (\<lambda>(sl, s). (\<lambda>mp. \<Sum>x \<in> dom mp. rpo_measure x (mp x))
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


context CNodeInv_AI_3 begin

lemma cap_revoke_termination:
  "All (cap_revoke_dom :: (machine_word \<times> bool list) \<times> 'state_ext state \<Rightarrow> bool)"
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
  apply (erule use_valid[OF _ preemption_point_caps_of_state], simp)
  done

lemma cap_revoke_dom: "\<And> (p :: (machine_word \<times> bool list) \<times> 'state_ext state). cap_revoke_dom p"
  using cap_revoke_termination by blast

lemmas cap_revoke_simps = cap_revoke.psimps[OF cap_revoke_dom]

lemmas cap_revoke_induct = cap_revoke.pinduct[OF cap_revoke_dom]

lemma cap_revoke_preservationE':
  fixes P and s :: "'state_ext state" and ptr
  assumes x: "\<And>p. \<lbrace>P\<rbrace> cap_delete p \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. E\<rbrace>"
  assumes p: "\<lbrace>P\<rbrace> preemption_point \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. E\<rbrace>"
  shows      "s \<turnstile> \<lbrace>P\<rbrace> cap_revoke ptr \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. E\<rbrace>"
proof (induct rule: cap_revoke_induct)
  case (1 slot)
  show ?case
    apply (subst cap_revoke_simps)
    apply (wp "1.hyps")
           apply (wp x p hoare_drop_imps)+
     apply simp_all
    done
qed

lemmas cap_revoke_preservationE = use_spec(2) [OF cap_revoke_preservationE']

lemmas cap_revoke_preservation'
  = cap_revoke_preservationE'
      [where P=P and E=P for P, simplified, OF valid_validE, OF _ valid_validE]

lemmas cap_revoke_preservation = use_spec(2) [OF cap_revoke_preservation']

lemmas cap_revoke_preservation2 = cap_revoke_preservation[THEN validE_valid]

lemma ball_subset: "\<forall>x\<in>A. Q x \<Longrightarrow> B \<subseteq> A \<Longrightarrow> \<forall>x\<in>B. Q x"
  apply blast
  done

lemma cap_revoke_preservation_desc_of':
  fixes P Q and s :: "'state_ext state"
  assumes x: "\<And>p. \<lbrace>P and Q p\<rbrace> cap_delete p \<lbrace>\<lambda>rv. P\<rbrace>"
  and     y: "\<And>sl s. P s \<Longrightarrow> \<forall>sl' \<in> descendants_of sl (cdt s). Q sl' s"
  assumes p: "\<lbrace>P\<rbrace> preemption_point \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "s \<turnstile> \<lbrace>P\<rbrace> cap_revoke ptr \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>\<lambda>rv. P\<rbrace>"
proof (induct rule: cap_revoke_induct)
  case (1 slot)
  show ?case
    apply (subst cap_revoke_simps)
    apply (wp "1.hyps")
           apply (wp x p hoare_drop_imps)+
     apply (simp_all add: y)
    done
qed

lemmas cap_revoke_preservation_desc_of =
       use_spec(2) [OF cap_revoke_preservation_desc_of']

lemma cap_revoke_typ_at:
  "\<And>P T p. \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace> cap_revoke ptr \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp wp: cap_delete_typ_at cap_revoke_preservation irq_state_independent_AI
                 preemption_point_inv)

lemma cap_revoke_invs:
  "\<And>ptr. \<lbrace>\<lambda>s::'state_ext state. invs s\<rbrace> cap_revoke ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp wp: cap_revoke_preservation_desc_of[where Q="\<lambda>_ _ _. True", simplified]
                 preemption_point_inv)

end


lemma descendants_of_cdt_parent:
  "\<lbrakk> p' \<in> descendants_of p (cdt s) \<rbrakk> \<Longrightarrow> \<exists>p''. cdt s \<Turnstile> p'' \<leadsto> p'"
  apply (simp add: descendants_of_def del: split_paired_Ex)
  apply (erule tranclE)
   apply (erule exI)
  apply (erule exI)
  done


lemma cap_revoke_mdb_stuff3:
  "\<lbrakk> p' \<in> descendants_of p (cdt s); valid_mdb s \<rbrakk>
     \<Longrightarrow> cte_wp_at ((\<noteq>) cap.NullCap) p' s"
  apply (clarsimp simp add: valid_mdb_def
                     dest!: descendants_of_cdt_parent)
  apply (simp add: cdt_parent_of_def)
  apply (drule(1) mdb_cte_atD)
  apply simp
  done

crunch cancel_badged_sends
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps filterM_mapM unless_def
   ignore: without_preemption filterM set_object clearMemory)

locale CNodeInv_AI_4 = CNodeInv_AI_3 state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself" +
  assumes finalise_slot_typ_at [wp]:
    "\<And>P T p. \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace> finalise_slot a b \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  assumes weak_derived_appropriate:
    "\<And>cap cap'. weak_derived cap cap' \<Longrightarrow> appropriate_cte_cap cap = appropriate_cte_cap cap'"

context CNodeInv_AI_4 begin

lemma inv_cnode_typ_at:
  "\<And>P T p ci. \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace> invoke_cnode ci \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (case_tac ci, simp_all add: invoke_cnode_def split del: if_split)
        apply (wp cap_insert_typ_at cap_move_typ_at cap_swap_typ_at hoare_drop_imps
                  cap_delete_typ_at cap_revoke_typ_at hoare_vcg_all_lift | wpc |
               simp | rule conjI impI | rule hoare_pre)+
  done

lemma invoke_cnode_tcb[wp]:
  "\<And>tptr ci. \<lbrace>tcb_at tptr::'state_ext state \<Rightarrow> bool\<rbrace> invoke_cnode ci \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ, wp inv_cnode_typ_at)

end


lemma duplicate_creation:
  "\<lbrace>cte_wp_at (\<lambda>c. gen_obj_refs c = gen_obj_refs cap) p
     and cte_at p' and K (p \<noteq> p')\<rbrace>
     set_cap cap p'
  \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>cap. \<not> is_final_cap' cap s) p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_post_imp[where Q'="\<lambda>rv. cte_wp_at (\<lambda>c. gen_obj_refs c = gen_obj_refs cap) p
                                        and cte_wp_at ((=) cap) p'"])
   apply (clarsimp simp: cte_wp_at_def)
   apply (case_tac "\<exists>x. x \<in> obj_refs cap \<and> x \<in> obj_refs capa")
    apply (elim exE conjE)
    apply (frule (4) final_cap_duplicate_obj_ref)
    apply simp
   apply (case_tac "\<exists>x. x \<in> cap_irqs cap \<and> x \<in> cap_irqs capa")
    apply (elim exE conjE)
    apply (frule (4) final_cap_duplicate_irq, simp)
   apply (case_tac "\<exists>x. x \<in> arch_gen_refs cap \<and> x \<in> arch_gen_refs capa")
    apply (elim exE conjE)
    apply (frule (4) final_cap_duplicate_arch_refs, simp)
   apply (simp add: is_final_cap'_def gen_obj_refs_eq gen_obj_refs_Int)
  apply (wp set_cap_cte_wp_at)
   apply simp_all
  done


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

lemmas set_cdt_caps_of_state[wp] = set_cdt_caps_of_state[of P p for P p]

lemma cap_move_caps_of_state:
  notes fun_upd_apply [simp del]
  shows "\<lbrace>\<lambda>s. P ((caps_of_state s) (ptr' \<mapsto> cap, ptr \<mapsto> cap.NullCap ))\<rbrace>
           cap_move cap ptr ptr'
         \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by (wpsimp simp: cap_move_def)


lemma zombies_duplicate_creation:
  "\<lbrace>\<lambda>s. zombies_final s \<and> \<not> is_zombie cap
        \<and> (\<exists>p'. cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap \<and> \<not> is_zombie c) p' s)
        \<and> cte_wp_at ((=) cap.NullCap) p s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (wp set_cap_zombies)
  apply (clarsimp simp: cte_wp_at_def)
  apply (thin_tac "x \<noteq> y" for x y)
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
           split: if_split_asm cap.splits)


lemma cap_move_zombies_final[wp]:
  "\<lbrace>zombies_final and cte_wp_at ((=) cap.NullCap) ptr'
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
  "\<lbrace>cte_wp_at ((=) cap.NullCap) ptr'
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
    apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)+
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


context CNodeInv_AI_4 begin

lemma cap_move_if_unsafe [wp]:
  "\<And>ptr' cap ptr.
    \<lbrace>cte_wp_at ((=) cap.NullCap) ptr'
          and cte_wp_at (weak_derived cap) ptr
          and K (ptr \<noteq> ptr')
          and if_unsafe_then_cap
          and ex_cte_cap_wp_to (appropriate_cte_cap cap) ptr'\<rbrace>
      cap_move cap ptr ptr'
    \<lbrace>\<lambda>rv. if_unsafe_then_cap :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  subgoal for ptr' cap ptr
  apply (simp add: cap_move_def)
  apply (wp | simp)+
   apply (rule hoare_post_imp, simp only: if_unsafe_then_cap_def)
   apply (simp only: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
   apply wp+
  apply (clarsimp simp: if_unsafe_then_cap_def
                        ex_cte_cap_wp_to_def cte_wp_at_caps_of_state
              simp del: split_paired_All split_paired_Ex
                   del: allI
             split del: if_split)
  apply (frule weak_derived_Null)
  apply (frule weak_derived_cte_refs')
  apply (frule cap_irqs_appropriateness [OF weak_derived_cap_irqs])
  apply (frule weak_derived_appropriate)
  apply (erule allfEI[where f="id (ptr := ptr', ptr' := ptr)"])
  apply (case_tac "cref = ptr'")
   apply (intro allI impI,
          rule_tac x="(id (ptr := ptr', ptr' := ptr)) (a, b)" in exI)
   apply fastforce
  apply (clarsimp split: if_split_asm split del: if_split del: exE
               simp del: split_paired_All split_paired_Ex)
  apply (erule exfEI[where f="id (ptr := ptr', ptr' := ptr)"])
  apply (clarsimp split: if_split_asm)
  apply fastforce
  done
  done

end


crunch cap_move
  for arch[wp]: "\<lambda>s. P (arch_state s)"

crunch cap_move
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"

lemma cap_range_NullCap:
  "cap_range cap.NullCap = {}"
  by (simp add: cap_range_def)

crunch cap_move
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"


lemma cap_move_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers and cte_wp_at ((=) cap.NullCap) ptr'
           and cte_wp_at (weak_derived cap) ptr\<rbrace>
     cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: valid_irq_handlers_def irq_issued_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=interrupt_states, OF cap_move_interrupt_states])
   apply (simp add: cap_move_def set_cdt_def)
    apply (wp | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state
                 elim!: ranE split: if_split_asm
                 dest!: weak_derived_cap_irqs)
   apply auto
  done


context CNodeInv_AI_4 begin

lemma cap_move_valid_arch_caps[wp]:
  "\<And>cap ptr.
    \<lbrace>valid_arch_caps
          and cte_wp_at (weak_derived cap) ptr
          and cte_wp_at ((=) cap.NullCap) ptr'\<rbrace>
      cap_move cap ptr ptr'
    \<lbrace>\<lambda>rv. valid_arch_caps :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (simp add: cap_move_def)
  apply (rule hoare_pre)
   apply (subst bind_assoc[symmetric],
          rule bind_wp_fwd,
          rule swap_of_caps_valid_arch_caps)
   apply (wp | simp)+
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done

end



lemma cap_move_valid_ioc[wp]:
  "\<lbrace>valid_ioc and
    cte_wp_at (weak_derived cap) ptr and cte_wp_at ((=) cap.NullCap) ptr'\<rbrace>
   cap_move cap ptr ptr'
   \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  apply (simp add: cap_move_def valid_ioc_def[abs_def] cte_wp_at_caps_of_state
                   pred_conj_def)
  apply (wp set_cdt_cos_ioc set_cap_caps_of_state2 | simp)+
  apply (cases ptr, clarsimp simp add: cte_wp_at_caps_of_state valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply clarsimp
  done

declare cdt_update.state_refs_update [simp]

locale CNodeInv_AI_5 = CNodeInv_AI_4 state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself" +
  assumes cap_move_invs[wp]:
    "\<And>cap ptr' ptr.
      \<lbrace>invs and valid_cap cap and cte_wp_at ((=) cap.NullCap) ptr'
            and tcb_cap_valid cap ptr'
            and cte_wp_at (weak_derived cap) ptr
            and cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) ptr
            and ex_cte_cap_wp_to (appropriate_cte_cap cap) ptr' and K (ptr \<noteq> ptr')\<rbrace>
        cap_move cap ptr ptr'
      \<lbrace>\<lambda>rv. invs::'state_ext state \<Rightarrow> bool\<rbrace>"

lemma cte_wp_at_use2:
  "\<lbrakk>cte_wp_at P p s; cte_wp_at P' p s; \<And>c. \<lbrakk>cte_wp_at ((=) c) p s; P c; P' c\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (auto simp: cte_wp_at_caps_of_state)

lemma cte_wp_at_use3:
  "\<lbrakk>cte_wp_at P p s; cte_wp_at P' p s; cte_wp_at P'' p s; \<And>c. \<lbrakk>cte_wp_at ((=) c) p s; P c; P' c; P'' c\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (auto simp: cte_wp_at_caps_of_state)

lemma cap_move_valid_cap[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap'\<rbrace> cap_move cap p p' \<lbrace>\<lambda>_ s. s \<turnstile> cap'\<rbrace>"
  unfolding cap_move_def
  by (wp set_cdt_valid_cap | simp)+

lemma weak_derived_cte_refs_abs:
  "weak_derived c c' \<Longrightarrow> cte_refs c' = cte_refs c"
  apply (clarsimp simp: weak_derived_def copy_of_def)
  apply (auto simp: same_object_as_def is_cap_simps bits_of_def
             split: if_split_asm cap.splits)
  done

lemma cap_move_ex_cap_cte:
  "\<lbrace>ex_cte_cap_wp_to P ptr and
    cte_wp_at (weak_derived cap) p and
    cte_wp_at ((=) cap.NullCap) p' and
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
  "\<lbrace>cte_at src and K(src \<noteq> dest)\<rbrace> cap_move cap src dest \<lbrace>\<lambda>_ s. cte_wp_at ((=) cap.NullCap) src s\<rbrace>"
  unfolding cap_move_def
  by (wp set_cdt_cte_wp_at set_cap_cte_wp_at' | simp)+


crunch cap_move
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"

lemmas (in CNodeInv_AI_5) cap_revoke_cap_table[wp]
  = cap_table_at_typ_at [OF cap_revoke_typ_at]

lemmas appropriate_cte_cap_simps = appropriate_cte_cap_def [split_simps cap.split]

context CNodeInv_AI_5 begin

crunch is_final_cap
  for inv[wp]: "P"

lemma is_final_cap_is_final[wp]:
  "\<lbrace>\<top>\<rbrace> is_final_cap cap \<lbrace>\<lambda>rv s. rv = is_final_cap' cap s\<rbrace>"
  unfolding is_final_cap_def
  by wp simp

end


lemma cap_irqs_is_derived:
  "is_derived m ptr cap cap' \<Longrightarrow> cap_irqs cap = cap_irqs cap'"
  by (clarsimp simp: is_derived_def cap_master_cap_irqs split: if_split_asm)


lemma tcb_cap_valid_mdb[simp]:
  "tcb_cap_valid cap p (cdt_update mfn s) = tcb_cap_valid cap p s"
  by (simp add: tcb_cap_valid_def)


lemma tcb_cap_valid_is_original_cap[simp]:
  "tcb_cap_valid cap p (is_original_cap_update mfn s) = tcb_cap_valid cap p s"
  by (simp add: tcb_cap_valid_def)


crunch cap_move
  for tcb_cap_valid[wp]: "tcb_cap_valid cap p"


context CNodeInv_AI_5 begin

lemma invoke_cnode_invs[wp]:
  fixes i shows
  "\<lbrace>invs and valid_cnode_inv i\<rbrace> invoke_cnode i \<lbrace>\<lambda>rv. invs::'state_ext state \<Rightarrow> bool\<rbrace>"
  unfolding invoke_cnode_def
  apply (cases i)
       apply simp
       apply wp
       apply (simp add: ex_cte_cap_to_cnode_always_appropriate_strg
                        real_cte_tcb_valid)
       apply (clarsimp simp: cte_wp_at_caps_of_state dest!: cap_irqs_is_derived)
      apply simp
      apply wp
      apply (fastforce simp: real_cte_tcb_valid cte_wp_at_caps_of_state
                             ex_cte_cap_to_cnode_always_appropriate_strg)
     apply simp
     apply (wp cap_revoke_invs)
     apply simp
    apply simp
    apply wp
    apply (clarsimp simp: obj_at_def is_tcb is_cap_table)
   apply simp
   apply (rule conjI)
    apply (rule impI)
    apply wp
    apply (fastforce simp: real_cte_tcb_valid ex_cte_cap_to_cnode_always_appropriate_strg)
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
           (fastforce simp: cte_wp_at_caps_of_state)+)[1]
  apply (wpsimp wp: hoare_drop_imps get_cap_wp)+
  done

end


lemma corres_underlying_lift_ex1:
  assumes c: "\<And>v. corres_underlying sr nf nf' r (P v and Q) P' a c"
  shows "corres_underlying sr nf nf' r ((\<lambda>s. \<exists>v. P v s) and Q) P' a c"
  unfolding corres_underlying_def
  apply clarsimp
  apply (cut_tac v = v in c)
  apply (auto simp: corres_underlying_def)
  done


lemmas corres_underlying_lift_ex1' = corres_underlying_lift_ex1 [where Q = \<top>, simplified]


lemma corres_underlying_lift_ex2:
  assumes c: "\<And>v. corres_underlying sr nf nf' r P (P' v and Q) a c"
  shows "corres_underlying sr nf nf' r P ((\<lambda>s. \<exists>v. P' v s) and Q) a c"
  unfolding corres_underlying_def
  apply clarsimp
  apply (cut_tac v = v in c)
  apply (auto simp: corres_underlying_def)
  done


lemmas corres_underlying_lift_ex2' = corres_underlying_lift_ex2 [where Q = \<top>, simplified]


lemma real_cte_halted_if_tcb[simp]:
  "real_cte_at (a, b) s \<Longrightarrow> halted_if_tcb a s"
  by (clarsimp simp: halted_if_tcb_def obj_at_def is_cap_table is_tcb)

lemma descendants_of_empty:
  "x \<notin> descendants_of cref Map.empty"
  by (simp add: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)

lemma has_parent_cte_at:"valid_mdb s \<Longrightarrow> (cdt s) c = Some p \<Longrightarrow> cte_at c s"
  apply (rule cte_wp_cte_at)
  apply (simp add: valid_mdb_def mdb_cte_at_def del: split_paired_All)
  apply blast
  done

lemma preemption_point_ex_cte_cap_wp_to[wp]:
  "preemption_point \<lbrace>ex_cte_cap_wp_to P ptr\<rbrace>"
  by (wpsimp wp: ex_cte_cap_to_pres preemption_point_inv)

lemma preemption_point_invs[wp]:
  "preemption_point \<lbrace>invs\<rbrace>"
  by (wpsimp wp: preemption_point_inv)

end
