(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KHeap_DR
imports Intent_DR
begin

context begin interpretation Arch . (*FIXME: arch_split*)

declare arch_post_cap_deletion_def[simp]
lemmas post_cap_deletion_simps[simp] = post_cap_deletion_def[simplified arch_post_cap_deletion_def]

declare arch_mask_irq_signal_def[simp]

lemma nat_bl_to_bin_surj:
  "\<exists>bl. n = nat (bl_to_bin bl)"
  using n_less_equal_power_2[where n=n, folded of_nat_less_iff, simplified]
  apply (rule_tac x="bin_to_bl n (int n)" in exI)
  apply (simp only: bin_bl_bin bintrunc_mod2p)
  apply simp
  done

lemma transform_tcb_slot_0:
  "transform_cslot_ptr (a, tcb_cnode_index 0) = (a,tcb_cspace_slot)"
  apply (clarsimp simp:transform_cslot_ptr_def)
  apply (unfold tcb_cspace_slot_def)
  apply (simp add: tcb_cnode_index_def bl_to_bin_def)
  done

lemma transform_tcb_slot_1:
  "transform_cslot_ptr (a,tcb_cnode_index 1) = (a,tcb_vspace_slot)"
  apply (clarsimp simp:transform_cslot_ptr_def)
  apply (unfold tcb_vspace_slot_def)
  apply (simp add: tcb_cnode_index_def)
  done

lemma transform_tcb_slot_2:
  "transform_cslot_ptr (a,tcb_cnode_index 2) = (a,tcb_replycap_slot)"
  apply (clarsimp simp:transform_cslot_ptr_def)
  apply (unfold tcb_replycap_slot_def)
  apply (simp add: tcb_cnode_index_def)
  apply (simp add:bl_to_bin_def)
  done

lemma transform_tcb_slot_3:
  "transform_cslot_ptr (a,tcb_cnode_index 3) = (a,tcb_caller_slot)"
  apply (clarsimp simp:transform_cslot_ptr_def)
  apply (unfold tcb_caller_slot_def)
  apply (simp add: tcb_cnode_index_def)
  apply (simp add:bl_to_bin_def)
  done

lemma transform_tcb_slot_4:
  "transform_cslot_ptr (a,tcb_cnode_index 4) = (a,tcb_ipcbuffer_slot)"
  apply (clarsimp simp:transform_cslot_ptr_def)
  apply (unfold tcb_ipcbuffer_slot_def)
  apply (simp add: tcb_cnode_index_def)
  apply (simp add:bl_to_bin_def)
  done

lemmas transform_tcb_slot_simp =
  transform_tcb_slot_0 transform_tcb_slot_1
  transform_tcb_slot_2 transform_tcb_slot_3
  transform_tcb_slot_4

lemma cap_table_at_cte_wp_at_length:
  "\<lbrakk> cap_table_at n p s; cte_wp_at P (p, p') s \<rbrakk>
        \<Longrightarrow> length p' = n"
  by (auto simp: cte_wp_at_cases obj_at_def is_cap_table well_formed_cnode_n_def length_set_helper)

context
begin

(* avoid spurious warning in termination proof below *)
declare CSpace_D.resolve_address_bits.simps [simp del]

termination CSpace_D.resolve_address_bits
  by (relation "measure (\<lambda>(a,b,c). c)") (clarsimp simp:in_monad)+

end

crunch
  "KHeap_D.set_cap", "PageTableUnmap_D.cancel_all_ipc", "PageTableUnmap_D.unbind_maybe_notification"
  for cdl_cdt [wp]: "\<lambda>s. P (cdl_cdt s)"
  (wp: crunch_wps simp: crunch_simps)

lemma descendants_cdl_cdt_lift:
  "(\<And>P. \<lbrace>\<lambda>s. P (cdl_cdt s)\<rbrace> f \<lbrace>\<lambda>_ s. P (cdl_cdt s)\<rbrace>) \<Longrightarrow>
   \<lbrace>\<lambda>s. P (KHeap_D.descendants_of slot s)\<rbrace> f \<lbrace>\<lambda>_ s. P (KHeap_D.descendants_of slot s)\<rbrace>"
  apply (simp add: KHeap_D.descendants_of_def KHeap_D.cdt_parent_rel_def
                   KHeap_D.is_cdt_parent_def)
  apply assumption
  done

lemma fast_finalise_descendants:
  "\<lbrace>\<lambda>s. P (KHeap_D.descendants_of slot s)\<rbrace>
   PageTableUnmap_D.fast_finalise cap fin
  \<lbrace>\<lambda>_ s. P (KHeap_D.descendants_of slot s) \<rbrace>"
  apply (cases cap, simp_all)
   apply (wp descendants_cdl_cdt_lift|simp)+
  done

lemmas set_cap_descendants = descendants_cdl_cdt_lift [OF KHeap_D_set_cap_cdl_cdt]

lemma removed_descendants_subset:
  assumes slot: "slot \<in> KHeap_D.descendants_of p s"
  defines "s' \<equiv> s\<lparr>cdl_cdt :=
                     \<lambda>x. if x = slot
                         then None
                         else if cdl_cdt s x = Some slot
                         then cdl_cdt s slot
                         else cdl_cdt s x\<rparr>"
  shows "KHeap_D.descendants_of p s' \<subset> KHeap_D.descendants_of p s" (is "?new \<subset> ?old")
proof
  have "slot \<notin> ?new"
    apply (clarsimp simp: KHeap_D.descendants_of_def)
    apply (erule tranclE)
     apply (clarsimp simp: KHeap_D.cdt_parent_rel_def KHeap_D.is_cdt_parent_def s'_def)
    apply (clarsimp simp: KHeap_D.cdt_parent_rel_def KHeap_D.is_cdt_parent_def s'_def)
    done
  with slot show "?new \<noteq> ?old" by auto

  { fix p' assume p': "p' \<in> ?new"
    then
    have "p' \<in> ?old"
      unfolding KHeap_D.descendants_of_def
      apply clarsimp
      apply (induct rule: trancl_induct)
       apply (fastforce simp: KHeap_D.cdt_parent_rel_def KHeap_D.is_cdt_parent_def s'_def
                       split: if_split_asm
                       intro: trancl_trans)
      apply (erule trancl_trans)
      apply (fastforce simp: KHeap_D.cdt_parent_rel_def KHeap_D.is_cdt_parent_def s'_def
                      split: if_split_asm
                      intro: trancl_trans)
      done
  }
  thus "?new \<subseteq> ?old" by auto
qed

lemma always_empty_slot_card:
  "\<lbrace>\<lambda>s'. s' = s \<and> slot \<in> KHeap_D.descendants_of x s' \<and>
         finite (KHeap_D.descendants_of x s') \<rbrace>
    always_empty_slot slot
  \<lbrace>\<lambda>_ s'. card (KHeap_D.descendants_of x s') < card (KHeap_D.descendants_of x s)\<rbrace>"
  apply (clarsimp simp: always_empty_slot_def remove_parent_def)
  apply (wp set_cap_descendants)
  apply clarsimp
  apply (erule psubset_card_mono)
  apply (erule removed_descendants_subset)
  done

termination revoke_cap_simple
  apply (relation "measure (\<lambda>(a,b). card (KHeap_D.descendants_of a b))")
   apply (rule wf_measure)
  apply (simp add: in_monad select_def)
  apply (clarsimp simp: delete_cap_simple_def in_monad gets_the_def)
  apply (clarsimp simp: PageTableUnmap_D.is_final_cap_def in_monad)
  apply (drule use_valid,
         rule_tac P="(=) (KHeap_D.descendants_of (a,b) s)" in
                  fast_finalise_descendants,
         rule refl)
  apply clarsimp
  apply (drule use_valid, rule always_empty_slot_card)
   apply (rule conjI, rule refl)
   apply (erule conjI)
   apply assumption
  apply simp
  done

declare revoke_cap_simple.simps [simp del]
declare KHeap_DR.resolve_address_bits.simps [simp del]

lemma dcorres_revoke_cap_simple_helper:
  "\<lbrakk> dcorres r P P'
    (do descendants \<leftarrow> gets $ KHeap_D.descendants_of victim;
      assert (finite descendants);
      non_null \<leftarrow> gets (\<lambda>s. {slot. opt_cap slot s \<noteq> Some cdl_cap.NullCap \<and> opt_cap slot s \<noteq> None});
      non_null_descendants \<leftarrow> return (descendants \<inter> non_null);
      if non_null_descendants \<noteq> {}
      then do a \<leftarrow> select non_null_descendants;
              y \<leftarrow> delete_cap_simple a;
              revoke_cap_simple victim
           od
      else return ()
     od)
     h \<rbrakk> \<Longrightarrow> dcorres r P P' (revoke_cap_simple victim) h"
  apply (rule corres_dummy_get_pl)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp:corres_underlying_def)
  apply (rename_tac s' a b)
  apply (subst revoke_cap_simple.simps)
  apply (erule_tac x=s' in allE, simp)
  apply (clarsimp cong: if_cong)
  apply (drule_tac x="(a,b)" in bspec)
   apply simp
  apply clarsimp
  done

lemma valid_irq_node_cte_at_irq_slot:
 "valid_irq_node s \<Longrightarrow> cte_at (interrupt_irq_node s x,[]) s"
  apply (clarsimp simp:valid_irq_node_def)
  apply (drule_tac x = x in spec)
  apply (clarsimp simp:obj_at_def is_cap_table_def)
  apply (clarsimp split: Structures_A.kernel_object.splits
                  simp: cte_wp_at_cases well_formed_cnode_n_def)
  apply auto
done

lemma transform_cslot_ptr_inj:
  "\<lbrakk> cte_at p s; cte_at p' s \<rbrakk> \<Longrightarrow>
   (transform_cslot_ptr p = transform_cslot_ptr p') = (p = p')"
  apply (clarsimp simp: transform_cslot_ptr_def
                        bl_to_bin_ge0 eq_nat_nat_iff split_def
                        valid_irq_node_def)
  apply (cases p, cases p')
  apply (safe, simp_all)
  apply (drule bl_to_bin_inj)
   apply (erule(1) cte_at_cref_len)
  apply simp
  done

lemma transform_cdt_slot_inj_on_cte_at:
  "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> cte_wp_at P x s \<rbrakk> \<Longrightarrow>
       inj_on (transform_cslot_ptr) S"
  apply (rule inj_onI)
  apply (subst(asm) transform_cslot_ptr_inj, simp_all)
  apply (fastforce simp: cte_wp_at_caps_of_state)+
  done

lemma get_cur_thread_corres:
  "dcorres (\<lambda>rv rv'. rv = rv') \<top>
         (\<lambda>s. not_idle_thread (cur_thread s) s)
     (gets_the cdl_current_thread)
     (gets cur_thread)"
  apply (simp add:gets_the_def gets_def)
  apply (rule dcorres_absorb_get_l)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_opt_def transform_def transform_current_thread_def)
  apply (simp add:corres_underlying_def not_idle_thread_def)
  done

lemma not_in_dom_dest:
  "\<lbrakk>dom f = P; f x = None\<rbrakk> \<Longrightarrow> x\<notin> P"
  by (clarsimp simp:dom_def)

lemma in_dom_dest:
  "\<lbrakk>dom f = P; f x \<noteq> None\<rbrakk> \<Longrightarrow> x\<in> P"
  by (clarsimp simp:dom_def)

lemma nat_to_bl_dest:
  "b\<in>Collect (%x. length x= n)\<Longrightarrow> nat_to_bl n (nat (bl_to_bin b)) = Some b"
  apply (unfold nat_to_bl_def)
  apply (subgoal_tac "0 \<le> bl_to_bin b")
   apply (subst nat_0_le)
    apply simp
   apply (subgoal_tac "length b = n")
    apply (erule subst[where s="length b" and t=n])
    apply (subst bl_bin_bl)
    apply (simp add: not_le)
    apply (clarsimp simp: bl_to_bin_lt2p)
   apply clarsimp
  apply (simp add:not_less)
  apply (rule bl_to_bin_ge0)
  done

lemma bl_to_bin_tcb_cnode_index_le0:
  "n < 8 \<Longrightarrow> (bl_to_bin (tcb_cnode_index n) \<le> 0) = (n = 0)"
  by (simp add: tcb_cnode_index_def uint_nat unat_of_nat)

lemma nat_bl_to_bin_lt2p: "nat(bl_to_bin b) < 2 ^ length b"
  apply (rule iffD2[OF nat_less_iff[OF bl_to_bin_ge0]])
  apply (simp add:bl_to_bin_lt2p)
done

lemma caps_of_state_transform_opt_cap:
  "\<lbrakk> caps_of_state s p = Some cap; valid_etcbs s;
          fst p \<noteq> idle_thread s \<rbrakk>
       \<Longrightarrow> opt_cap (transform_cslot_ptr p) (transform s)
            = Some (transform_cap cap)"
  apply (frule caps_of_state_cteD)
  apply (cases p)
  apply (erule cte_wp_atE)
   apply (clarsimp simp: opt_cap_def transform_cslot_ptr_def
                         slots_of_def transform_objects_def
                         transform_def object_slots_def
                         transform_cnode_contents_def well_formed_cnode_n_def
                  split: nat.splits)
   apply (frule(1) eqset_imp_iff[THEN iffD1, OF _ domI])
   apply (simp add: option_map_join_def nat_to_bl_dest)
   apply (fastforce simp: nat_to_bl_def split: nat.splits)
  apply (frule(1) valid_etcbs_tcb_etcb)
  apply (clarsimp simp: opt_cap_def transform_cslot_ptr_def slots_of_def
                        transform_def transform_objects_def object_slots_def
                        valid_irq_node_def obj_at_def is_cap_table_def
                        transform_tcb_def tcb_slots tcb_cap_cases_def
                        bl_to_bin_tcb_cnode_index bl_to_bin_tcb_cnode_index_le0
                 split: if_split_asm)
  done

lemma cap_slot_cnode_property_lift:
  "\<lbrakk>valid_etcbs s'; kheap s' a = Some (kernel_object.CNode sz cs); valid_idle s'; well_formed_cnode_n sz cs; b\<in> dom cs\<rbrakk>
  \<Longrightarrow> (opt_cap (transform_cslot_ptr (a, b)) (transform s')) =
     (case (cs b) of None \<Rightarrow> None | Some y \<Rightarrow> Some (transform_cap y))"
  apply clarsimp
  apply (subgoal_tac "cte_wp_at ((=) y) (a, b) s'")
   apply (subst caps_of_state_transform_opt_cap, simp_all)
    apply (simp add: cte_wp_at_caps_of_state)
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  apply (rule cte_wp_at_cteI, fastforce, simp+)
  done

lemma get_cap_no_fail:
  "dcorres r P (P' and cte_at slot) f (get_cap slot>>=h) \<Longrightarrow> dcorres r P P' f (get_cap slot>>=h)"
  apply (rule dcorres_expand_pfx)
  apply (case_tac "cte_at slot s'")
   apply (drule dcorres_absorb_pfx)
      apply simp+
  apply (case_tac slot)
  apply (simp(no_asm) add:get_cap_def[simplified tcb_cnode_map_def])
  apply (clarsimp simp:bind_assoc get_object_def gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp: assert_def corres_free_fail)
  apply (case_tac y)
      apply (simp_all add:corres_free_fail assert_def cte_at_cases)
   apply (rule impI)
   apply (simp add:dom_def  assert_opt_def corres_free_fail)
  apply (simp add:assert_opt_def corres_free_fail)
  apply auto
  done

lemma get_cap_helper:
  "dcorres r P (P') f (get_cap slot >>= g) \<Longrightarrow> dcorres r P (P' and (cte_wp_at ((=) cap) slot)) f  (g cap)"
  by (clarsimp simp:bind_def corres_underlying_def cte_wp_at_def)

lemma get_cap_corres:
  "ptr' = transform_cslot_ptr ptr \<Longrightarrow>
   dcorres (\<lambda>rv rv'. rv = transform_cap rv') \<top>
   (valid_idle and not_idle_thread (fst ptr) and valid_etcbs)
     (KHeap_D.get_cap ptr')
     (CSpaceAcc_A.get_cap ptr)"
  apply (case_tac ptr)
  apply (clarsimp simp:CSpaceAcc_A.get_cap_def[simplified tcb_cnode_map_def]
                       gets_def get_object_def gets_the_def bind_assoc)
  apply (rule dcorres_get)
  apply (clarsimp simp:assert_def corres_free_fail assert_opt_def)
  apply (case_tac y)
      apply (simp_all add:assert_def corres_free_fail)
   apply (rename_tac nat "fun")
   apply (case_tac "fun b")
    apply (simp add:corres_free_fail)
   apply clarsimp
   apply (drule (2) cap_slot_cnode_property_lift, simp, fastforce)
   apply simp
  apply (clarsimp simp:transform_tcb_slot_simp[simplified])
  apply (drule get_tcb_rev)
  apply (drule(1) valid_etcbs_get_tcb_get_etcb)
  apply (clarsimp simp:lift_simp not_idle_thread_def)
  done

definition
  opt_cap_wp_at :: "(cdl_cap \<Rightarrow> bool) \<Rightarrow> (cdl_object_id \<times> nat) \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "opt_cap_wp_at P slot s \<equiv>  \<exists>cap. fst (KHeap_D.get_cap slot s) = {(cap, s)} \<and> P cap"

lemma opt_cap_wp_at_def':
  "opt_cap_wp_at P slot s = (case (opt_cap slot s) of Some a \<Rightarrow> P a | _ \<Rightarrow> False) "
  apply (clarsimp simp:opt_cap_wp_at_def opt_cap_def gets_the_def gets_def get_def return_def assert_opt_def bind_def)
  apply (auto simp:fail_def return_def split:option.splits)
  done

lemma nat2p: "nat (2^(x::nat)) = 2^(x::nat)"
  by (rule nat_int.Rep_inverse',simp)

lemma nat_to_bl_to_bin:
  "nat_to_bl bits n = Some xs \<Longrightarrow> n = nat (bl_to_bin xs)"
  by (clarsimp simp:nat_to_bl_def bin_bl_bin' bintrunc_mod2p split: if_split_asm)

lemma cap_counts_inv:
assumes "\<And>cap. P cap\<Longrightarrow> cap_counts cap"
shows "\<lbrakk>opt_cap_wp_at P slot (transform s);valid_objs s; valid_etcbs s\<rbrakk>
  \<Longrightarrow> \<exists>slot'. slot = transform_cslot_ptr slot' \<and> cte_wp_at (\<lambda>cap'. P (transform_cap cap')) slot' s"
  apply (clarsimp simp:opt_cap_wp_at_def' split:option.splits)
  apply (case_tac slot)
  apply (rename_tac ptr offset)
  apply (clarsimp simp:slots_of_def KHeap_D.opt_cap_def transform_def split:option.splits)
  apply (rule_tac x = ptr in exI)
  apply (clarsimp simp:transform_objects_def restrict_map_Some_iff object_slots_def split:cdl_object.splits)
       apply (frule assms)
       apply (clarsimp simp: cte_wp_at_cases transform_object_def transform_tcb_def
                             tcb_pending_op_slot_def tcb_boundntfn_slot_def
                       split: Structures_A.kernel_object.splits nat.splits if_splits
              | drule(1) valid_etcbs_tcb_etcb)+
         apply (clarsimp simp: cap_counts_def infer_tcb_bound_notification_def split:option.splits)
             apply (clarsimp simp:cap_counts_def infer_tcb_pending_op_def split:Structures_A.thread_state.splits nat.splits)
            using transform_tcb_slot_simp[simplified,symmetric]
            apply (rule_tac x= "tcb_cnode_index 4" in exI)
            apply (clarsimp)
           using transform_tcb_slot_simp[simplified,symmetric]
           apply (rule_tac x= "tcb_cnode_index 3" in exI)
           apply (clarsimp)
          using transform_tcb_slot_simp[simplified,symmetric]
          apply (rule_tac x= "tcb_cnode_index 2" in exI)
          apply (clarsimp)
         using transform_tcb_slot_simp[simplified,symmetric]
         apply (rule_tac x= "tcb_cnode_index 1" in exI)
         apply (clarsimp)
        using transform_tcb_slot_simp[simplified,symmetric]
        apply (rule_tac x= "tcb_cnode_index 0" in exI)
        apply (clarsimp)
       apply (rename_tac arch_kernel_obj)
       apply (case_tac arch_kernel_obj,simp_all)
      apply (simp_all add:object_slots_def transform_object_def)
      apply (clarsimp simp:transform_cnode_contents_def option_map_join_def
                     split:option.splits Structures_A.kernel_object.splits nat.splits)
         apply (clarsimp simp:cte_wp_at_cases well_formed_cnode_invsI transform_cslot_ptr_def split:if_splits)
         apply (rule_tac x = x2b in exI,simp add: nat_to_bl_to_bin)
        apply (drule(1) valid_etcbs_tcb_etcb, simp)
       prefer 6 (* IRQ Node *)
       apply (clarsimp split: Structures_A.kernel_object.splits nat.splits option.splits)
          apply (clarsimp simp:transform_cnode_contents_def option_map_join_def
                         split:option.splits Structures_A.kernel_object.splits nat.splits)
          apply (clarsimp simp:cte_wp_at_cases well_formed_cnode_invsI transform_cslot_ptr_def split:if_splits)
          apply (rule_tac x = x2a in exI,simp add: nat_to_bl_to_bin)
         apply (frule assms)
         apply ((simp_all add:Let_def cap_counts_def transform_tcb_def
                        split:option.splits if_splits arch_kernel_obj.splits
                              Structures_A.kernel_object.splits cdl_object.splits nat.splits|
                drule(1) valid_etcbs_tcb_etcb |
                clarsimp simp: unat_map_def transform_page_table_contents_def cap_counts_def
                          transform_page_directory_contents_def transform_asid_pool_contents_def
                          transform_pte_def transform_pde_def transform_asid_pool_entry_def
                    split:option.splits if_splits ARM_A.pte.splits ARM_A.pde.splits
                    dest!:assms)+)
  done

lemma eqset_imp': "A = B \<Longrightarrow> \<forall>x. ((x\<in> A) = (x\<in> B))" by simp

lemma eq_singleton_set: "\<lbrakk>A = f` B; \<forall>x\<in>B. \<forall>y\<in> B. x\<noteq> y \<longrightarrow> f x\<noteq> f y \<rbrakk>\<Longrightarrow> (\<exists>a. A = {a}) = (\<exists>b. B = {b})"
  apply (subgoal_tac "card A = card B")
   apply (auto simp: trans[OF eq_commute card_Suc_eq])[1]
  apply (metis card_image inj_onI)
  done

lemma final_cap_set_map:
  "\<lbrakk>valid_idle s'; valid_irq_node s';valid_objs s';if_unsafe_then_cap s'; valid_global_refs s'; cap_counts (transform_cap cap); valid_etcbs s'\<rbrakk>
    \<Longrightarrow> {cref. opt_cap_wp_at (\<lambda>cap'. cap_object (transform_cap cap) = cap_object cap'
                                    \<and> cdl_cap_irq (transform_cap cap) = cdl_cap_irq cap' \<and> cap_counts cap') cref (transform s')}
    = transform_cslot_ptr ` {cref. cte_wp_at (\<lambda>cap'. cap_irqs cap \<inter> cap_irqs cap' = {} \<longrightarrow> obj_refs cap \<inter> obj_refs cap' = {} \<longrightarrow> arch_gen_refs cap \<inter> arch_gen_refs cap' \<noteq> {}) cref s'}"
  apply (rule set_eqI)
  apply (rule iffI)
   apply (clarsimp simp: image_def)
   apply (drule cap_counts_inv[rotated])
      apply simp+
   apply clarsimp
   apply (rule_tac x=aa in exI)
   apply (rule_tac x=ba in exI)
   apply simp+
   apply (erule cte_wp_at_weakenE_customised)
   (*defer till the otherway around comes up*)
   defer
   apply (clarsimp simp:image_def opt_cap_wp_at_def')
   apply (drule iffD1[OF cte_wp_at_caps_of_state])
   apply clarsimp
   apply (frule caps_of_state_transform_opt_cap, simp)
    apply clarsimp
    apply (frule valid_idle_has_null_cap)
        (*It is true since idle thread should not get any cap installed *)
        apply simp+
   apply (thin_tac "opt_cap x y = Q" for x y Q)
   by (auto simp: transform_cap_def cap_has_object_def cap_counts_def cdl_cap_irq_def
            split: cap.splits arch_cap.splits if_split_asm)

lemma opt_cap_wp_at_ex_opt_cap:
  "opt_cap_wp_at P p s = (\<exists>cap'. opt_cap p s = Some cap' \<and> P cap')"
  by (simp add: opt_cap_wp_at_def' split: option.split)

lemma is_final_cap_corres:
  "\<lbrakk>cdl_cap = transform_cap cap;cap\<noteq> cap.NullCap\<rbrakk>
    \<Longrightarrow> dcorres ((=)) \<top> (valid_objs and valid_irq_node and valid_idle and if_unsafe_then_cap and valid_global_refs and valid_etcbs)
          (PageTableUnmap_D.is_final_cap (cdl_cap))
          (IpcCancel_A.is_final_cap (cap))"
  apply (clarsimp simp: IpcCancel_A.is_final_cap_def PageTableUnmap_D.is_final_cap_def)
  apply (clarsimp simp: IpcCancel_A.is_final_cap'_def PageTableUnmap_D.is_final_cap'_def)
  apply (subst cte_wp_at_def[symmetric])
  apply (subst opt_cap_wp_at_ex_opt_cap[symmetric])
  apply (rule iffI)
   apply clarsimp
   apply (drule final_cap_set_map)
         apply (simp+)[6] (* sseefried: Brittle proof! May need to change number there *)
   apply (drule eq_singleton_set)
    apply (clarsimp)
    apply (subst(asm) transform_cslot_ptr_inj, (erule cte_wp_at_cte_at)+)
    apply simp
   apply (clarsimp simp: gen_obj_refs_Int)
  apply (rule context_conjI[rotated])
   apply clarsimp
   apply (drule final_cap_set_map)
         apply (simp+)[6] (* sseefried: Brittle proof! May need to change number there *)
   apply (drule eq_singleton_set)
    apply (clarsimp simp: gen_obj_refs_Int)
   apply (clarsimp simp: gen_obj_refs_Int)
  apply (clarsimp|drule_tac x = "(a,b)" in eqset_imp_iff)+
  apply (clarsimp simp:cte_wp_at_cases)
  apply (case_tac cap)
             apply (clarsimp simp:cap_counts_def transform_cap_def gen_obj_refs_Int)+
  apply (clarsimp split:arch_cap.splits cap.splits)
  done

lemma dcorres_exec_is_final_cap:
  assumes c: "\<And>final. dcorres r (P final) P' (f final) f'"
  shows "dcorres r (\<lambda>s. P (PageTableUnmap_D.is_final_cap' cap s) s) P' (PageTableUnmap_D.is_final_cap cap >>= f) f'"
  unfolding PageTableUnmap_D.is_final_cap_def
  apply (rule corres_underlying_gets_pre_lhs)
  apply (rule c)
  done

lemma set_original_dummy_corres:
  "dcorres dc \<top> \<top> (return a) (set_original slot tag)"
  apply (clarsimp simp:set_original_def gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:return_def simpler_modify_def corres_underlying_def)
  apply (clarsimp simp:transform_def transform_current_thread_def)
  done

lemma corres_dummy_set_notification:
  "dcorres dc \<top> \<top> (return a) (set_notification epptr b)"
  apply (simp add: set_simple_ko_def get_object_def bind_assoc gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp: corres_free_fail assert_def a_type_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (rule corres_free_set_object)
  apply (clarsimp simp:transform_def transform_current_thread_def)
  apply (subst transform_objects_update_kheap_same_caps)
     apply (simp add: transform_objects_update_same)+
  done

lemma corres_dummy_set_sync_ep:
  "dcorres dc \<top> \<top> (return a) (set_endpoint epptr b)"
  apply (simp add: set_simple_ko_def get_object_def bind_assoc gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp: corres_free_fail assert_def a_type_def partial_inv_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (rule corres_free_set_object)
  apply (clarsimp simp:transform_def transform_current_thread_def)
  apply (subst transform_objects_update_kheap_same_caps)
     apply (simp add: transform_objects_update_same)+
  done

lemma thread_set_fault_corres:
  assumes r: "\<And>t. f (tcb_has_fault (t::Structures_A.tcb)) = (case (ft (tcb_fault t)) of None \<Rightarrow> False | _ \<Rightarrow> True)"
  shows "dcorres dc \<top> (tcb_at thread and not_idle_thread thread and valid_etcbs) (update_thread_fault thread f )
    (thread_set (tcb_fault_update ft) thread)"
  apply (clarsimp simp:thread_set_def update_thread_fault_def)
  apply (rule dcorres_gets_the)
   apply (simp_all)
   apply (clarsimp, drule(1) valid_etcbs_get_tcb_get_etcb)
   apply (clarsimp simp:opt_object_tcb not_idle_thread_def transform_tcb_def)
   apply (rule dcorres_set_object_tcb)
      apply (clarsimp simp: transform_tcb_def tcb_at_def cong: transform_full_intent_cong
                      dest!: get_tcb_SomeD get_etcb_SomeD )
      apply (cut_tac t = obj' in r)
      apply (clarsimp split:option.splits)
     apply ((clarsimp simp:opt_object_tcb tcb_at_def get_etcb_def dest!:get_tcb_SomeD get_etcb_SomeD)+)[3]
  apply (clarsimp, drule(1) valid_etcbs_get_tcb_get_etcb, clarsimp simp:opt_object_tcb not_idle_thread_def get_etcb_def)
  done

lemma get_object_corres:
  "ptr = ptr' \<Longrightarrow>
   dcorres (\<lambda>rv rv'. rv = transform_object undefined 0 etcb' rv')
      \<top> (not_idle_thread ptr' and obj_at (Not o is_tcb) ptr')
      (KHeap_D.get_object ptr) (KHeap_A.get_object ptr')"
  apply (clarsimp simp: KHeap_A.get_object_def gets_the_def)
  apply (rule corres_underlying_split[OF _ _ gets_sp gets_sp, where r'=dc])
   apply simp
  apply (clarsimp simp: assert_def corres_free_fail split: if_split)
  apply (rule_tac F="rv = Some (transform_object undefined 0 etcb' y)" in corres_req)
   apply (simp_all add: assert_opt_def)
  apply (clarsimp simp: transform_def transform_objects_def
                        not_idle_thread_def obj_at_def)
  apply (clarsimp simp: transform_object_def
                 split: Structures_A.kernel_object.splits)
  done

lemma nat_to_bl_id2:
  shows "nat_to_bl (length p) (nat (bl_to_bin p)) = Some p"
  unfolding nat_to_bl_def
  by (simp add: not_le bl_to_bin_ge0 bl_to_bin_lt2p nat_less_iff del: bin_to_bl_def)

lemma xf_cnode_contents:
  "\<lbrakk> well_formed_cnode_n sz cn; cn p = Some cap \<rbrakk> \<Longrightarrow>
  transform_cnode_contents sz cn (nat (bl_to_bin p)) = Some (transform_cap cap)"
  unfolding transform_cnode_contents_def
  apply clarsimp
  apply (frule (1) wf_cs_nD [symmetric], simp)
  apply (simp add: nat_to_bl_id2 word_bits_conv option_map_join_simps option_map_join_def)
  done

lemma transform_cnode_contents_upd:
  "\<lbrakk>well_formed_cnode_n sz cn; cn sl' = Some ocap'\<rbrakk> \<Longrightarrow>
    (transform_cnode_contents sz cn)(nat (bl_to_bin sl') \<mapsto> transform_cap cap') =
    transform_cnode_contents sz (cn(sl' \<mapsto> cap'))"
  apply (rule ext)
  apply clarsimp
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp: transform_cnode_contents_def option_map_def
                         option_map_join_def nat_to_bl_to_bin
                   split: option.splits)
  apply (clarsimp simp: transform_cnode_contents_def option_map_def
                         option_map_join_def
                   split: option.splits)
  apply (frule (1) wf_cs_nD [symmetric])
  apply (simp add: nat_to_bl_id2)
  done

lemma caps_of_state_cnode_upd:
  "\<lbrakk> kheap s p' = Some (CNode sz cn); well_formed_cnode_n sz cn;
     cn sl' = Some ocap' \<rbrakk> \<Longrightarrow>
  caps_of_state (update_kheap ((kheap s)(p' \<mapsto> CNode sz (cn(sl' \<mapsto> cap')))) s) =
   (caps_of_state s) ((p',sl') \<mapsto> cap')"
  apply (rule ext)
  apply (auto simp: caps_of_state_cte_wp_at cte_wp_at_cases wf_cs_upd)
  done

lemma caps_of_state_cnode:
  "\<lbrakk> kheap s p = Some (CNode sz cn); well_formed_cnode_n sz cn; cn sl = Some cap \<rbrakk> \<Longrightarrow>
  caps_of_state s (p, sl) = Some cap"
  by (simp add: caps_of_state_cte_wp_at cte_wp_at_cases)


lemma cdl_objects_tcb:
  "\<lbrakk>kheap s' p = Some (TCB tcb); ekheap s' p = Some etcb; p \<noteq> idle_thread s'\<rbrakk>
\<Longrightarrow> cdl_objects (transform s') p =
   Some (Tcb \<lparr>cdl_tcb_caps =
              [tcb_cspace_slot \<mapsto> transform_cap (tcb_ctable tcb),
               tcb_vspace_slot \<mapsto> transform_cap (tcb_vtable tcb),
               tcb_replycap_slot \<mapsto> transform_cap (tcb_reply tcb),
               tcb_caller_slot \<mapsto> transform_cap (tcb_caller tcb),
               tcb_ipcbuffer_slot \<mapsto> transform_cap (tcb_ipcframe tcb),
               tcb_pending_op_slot \<mapsto> infer_tcb_pending_op p (tcb_state tcb),
               tcb_boundntfn_slot \<mapsto> infer_tcb_bound_notification (tcb_bound_notification tcb)],
              cdl_tcb_fault_endpoint = of_bl (tcb_fault_handler tcb),
              cdl_tcb_intent = transform_full_intent (machine_state s') p tcb,
              cdl_tcb_has_fault = (tcb_has_fault tcb),
              cdl_tcb_domain = tcb_domain etcb
            \<rparr>)"
  apply (simp add: transform_def transform_objects_def)
  apply (clarsimp simp: transform_tcb_def)
  done

lemma get_ipc_buffer_words_caps_cong:
  "\<lbrakk> tcb_ipc_buffer tcb = tcb_ipc_buffer tcb';
     is_pg_cap (tcb_ipcframe tcb) = is_pg_cap (tcb_ipcframe tcb');
     \<lbrakk> is_pg_cap (tcb_ipcframe tcb); is_pg_cap (tcb_ipcframe tcb') \<rbrakk>
     \<Longrightarrow> obj_ref_of (tcb_ipcframe tcb) = obj_ref_of (tcb_ipcframe tcb') \<and>
        cap_bits (tcb_ipcframe tcb) = cap_bits (tcb_ipcframe tcb') \<and>
        cap_rights (tcb_ipcframe tcb) = cap_rights (tcb_ipcframe tcb')\<rbrakk>
  \<Longrightarrow> get_ipc_buffer_words ms tcb ns = get_ipc_buffer_words ms tcb' ns"
  apply (clarsimp simp: get_ipc_buffer_words_def is_cap_simps)
  by (auto split: cap.splits arch_cap.splits)

lemma transform_full_intent_caps_cong:
  "\<lbrakk> arch_tcb_context_get (tcb_arch tcb) = arch_tcb_context_get (tcb_arch tcb');
     tcb_ipc_buffer tcb = tcb_ipc_buffer tcb';
     is_pg_cap (tcb_ipcframe tcb) = is_pg_cap (tcb_ipcframe tcb');
     \<lbrakk> is_pg_cap (tcb_ipcframe tcb); is_pg_cap (tcb_ipcframe tcb') \<rbrakk>
     \<Longrightarrow> obj_ref_of (tcb_ipcframe tcb) = obj_ref_of (tcb_ipcframe tcb') \<and>
        cap_bits (tcb_ipcframe tcb) = cap_bits (tcb_ipcframe tcb') \<and>
        cap_rights (tcb_ipcframe tcb) = cap_rights (tcb_ipcframe tcb')
        \<rbrakk> \<Longrightarrow>
  transform_full_intent ms p tcb = transform_full_intent ms p tcb'"
  apply (clarsimp simp: transform_full_intent_def Let_def get_tcb_mrs_def
                        get_tcb_message_info_def
                  cong: get_ipc_buffer_words_caps_cong)
  done

lemma transform_full_intent_caps_cong_weak:
  "\<lbrakk> arch_tcb_context_get (tcb_arch tcb) = arch_tcb_context_get (tcb_arch tcb');
     tcb_ipc_buffer tcb = tcb_ipc_buffer tcb';
     tcb_ipcframe tcb = tcb_ipcframe tcb' \<rbrakk> \<Longrightarrow>
  transform_full_intent ms p tcb = transform_full_intent ms p tcb'"
  by (rule transform_full_intent_caps_cong) auto

lemma transform_full_intent_same_cap:
  "\<lbrakk> transform_cap (tcb_ipcframe tcb) = transform_cap cap' \<rbrakk>
  \<Longrightarrow> transform_full_intent ms p' (tcb\<lparr>tcb_ipcframe := cap'\<rparr>) =
     transform_full_intent ms p' tcb"
  apply (rule transform_full_intent_caps_cong)
     apply simp
    apply simp
   apply (simp add: is_cap_simps)
   apply (cases "tcb_ipcframe tcb", simp_all)
              by (simp add:transform_cap_def is_cap_simps
                     split:cap.splits if_split_asm arch_cap.splits)+

lemma set_cap_corres:
assumes "cap = transform_cap cap'"  "slot = transform_cslot_ptr slot'"
shows "dcorres dc \<top>
           (\<lambda>s. valid_idle s \<and> fst slot' \<noteq> idle_thread s \<and> valid_etcbs s)
           (KHeap_D.set_cap slot cap)
           (CSpaceAcc_A.set_cap cap' slot')"
proof -
  note if_cong[cong]
  from assms show ?thesis
  apply (case_tac slot')
  apply (rename_tac p' sl')
  apply (case_tac slot)
  apply (rename_tac p sl)
  apply (clarsimp simp: KHeap_D.set_cap_def CSpaceAcc_A.set_cap_def)
  apply (drule sym)
  apply (clarsimp simp:get_object_def gets_the_def bind_assoc gets_def split:if_splits)
  apply (clarsimp simp: transform_cslot_ptr_def)
  apply (rule dcorres_get)
  apply (rename_tac s s')
  apply (clarsimp simp: assert_def corres_free_fail)
  apply (rename_tac obj')
  apply (case_tac obj', simp_all add:corres_free_fail split del: if_split)
   \<comment> \<open>cnode or IRQ Node case\<close>
   apply (clarsimp simp: corres_free_fail split: if_split)
   apply (rename_tac sz cn ocap)
   apply (clarsimp simp: corres_underlying_def in_monad set_object_def get_object_def
                         cte_wp_at_cases caps_of_state_cte_wp_at)
   apply (case_tac sz, simp)
    apply (frule (1) cdl_objects_irq_node)
    apply (clarsimp simp: assert_opt_def has_slots_def)
    apply (clarsimp simp: update_slots_def object_slots_def transform_cnode_contents_upd)
    apply (clarsimp simp: KHeap_D.set_object_def simpler_modify_def)
    apply (clarsimp simp: transform_def transform_current_thread_def)
    apply (clarsimp simp: transform_objects_def)
    apply (rule ext)
    apply clarsimp
    apply (simp add: option_map_def restrict_map_def map_add_def split: option.splits)
   apply (frule (1) cdl_objects_cnode, simp)
   apply (clarsimp simp: assert_opt_def has_slots_def)
   apply (clarsimp simp: update_slots_def object_slots_def transform_cnode_contents_upd)
   apply (clarsimp simp: KHeap_D.set_object_def simpler_modify_def)
   apply (clarsimp simp: transform_def transform_current_thread_def)
   apply (clarsimp simp: transform_objects_def)
   apply (rule ext)
   apply clarsimp
   apply (simp add: option_map_def restrict_map_def map_add_def split: option.splits)
  \<comment> \<open>tcb case\<close>
  apply (drule(1) valid_etcbs_tcb_etcb)
  apply (clarsimp simp: cdl_objects_tcb assert_opt_def has_slots_def object_slots_def
                        update_slots_def
                  split del: if_split)
  apply (case_tac "nat (bl_to_bin sl') = tcb_ipcbuffer_slot")
   apply (simp add: tcb_slots)
   apply (clarsimp simp: bl_to_bin_tcb_cnode_index|rule conjI)+
     apply (rule corres_guard_imp)
       apply (rule select_pick_corres)
       apply (rule_tac s'=s' in dcorres_set_object_tcb)
         apply (clarsimp simp: transform_tcb_def)
         apply (rule conjI)
          apply (rule ext)
          apply (clarsimp simp: transform_tcb_def tcb_slots)
         apply (rule refl)
        apply assumption
       apply simp
      apply simp
     apply simp
    apply clarsimp
    apply (rule impI)
    apply (rule dcorres_set_object_tcb)
       apply (clarsimp simp: transform_tcb_def)
       apply (rule conjI)
        apply (rule ext)
        apply (clarsimp simp: transform_tcb_def tcb_slots)
       apply (erule transform_full_intent_same_cap)
      apply simp
     apply simp
    apply ((clarsimp simp: bl_to_bin_tcb_cnode_index corres_free_fail|rule conjI)+)[2] (* sseefried: brittle. Try changing number on end *)
  apply (simp add: bl_to_bin_tcb_cnode_index tcb_slot_defs)
  apply (rule conjI)
   apply (clarsimp simp: bl_to_bin_tcb_cnode_index)
  by (rule conjI ext dcorres_set_object_tcb|simp|
         clarsimp simp: transform_tcb_def tcb_slot_defs corres_free_fail
                  cong: transform_full_intent_caps_cong_weak)+
qed

lemma tcb_slot_pending_ipc_neq [simp]:
  "tcb_pending_op_slot \<noteq> tcb_ipcbuffer_slot"
  by (simp add: tcb_pending_op_slot_def tcb_ipcbuffer_slot_def)

lemma transform_full_intent_update_tcb_state[simp]:
  "transform_full_intent m ptr (update_tcb_state st a)
  = transform_full_intent m ptr a"
  apply (case_tac a)
  apply (simp add:transform_full_intent_def Let_def)
  apply (simp add:get_tcb_message_info_def
    get_tcb_mrs_def get_ipc_buffer_words_def)
  done

(*Special set_cap case which is related to thread_state *)
lemma set_pending_cap_corres:
  "dcorres dc \<top> (not_idle_thread y and ko_at (TCB obj) y
    and K (cap = infer_tcb_pending_op y tcb_st) and valid_etcbs)
    (KHeap_D.set_cap (y, tcb_pending_op_slot) cap)
  (KHeap_A.set_object y (TCB (update_tcb_state tcb_st obj)))"
  apply (simp add: KHeap_D.set_cap_def gets_def gets_the_def bind_assoc not_idle_thread_def)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) valid_etcbs_tcb_etcb, clarsimp)
  apply (frule opt_object_tcb[rotated, rotated])
    apply (fastforce simp: get_tcb_def)
   apply (fastforce simp: get_etcb_rev)
  apply (clarsimp simp: assert_opt_def has_slots_def transform_tcb_def object_slots_def update_slots_def)
  apply (clarsimp simp: corres_underlying_def in_monad set_object_def get_object_def
                        KHeap_D.set_object_def simpler_modify_def)
  apply (simp add: transform_def transform_current_thread_def)
  apply (rule ext)
  apply (subst transform_objects_update_kheap_same_caps)
     apply ((simp add: obj_at_def transform_tcb_def
       not_generates_pending_is_null tcb_slots)+)[3]
  apply (auto simp: obj_at_def not_generates_pending_is_null transform_tcb_def tcb_slots)
  done

lemma transform_scheduler_action_update[simp]: "transform (s\<lparr> scheduler_action := a \<rparr>) = transform s"
  by (auto simp: transform_def transform_cdt_def transform_current_thread_def transform_asid_table_def transform_objects_def)

lemma transform_cdt_list_update[simp]: "transform (s\<lparr> cdt_list := a \<rparr>) = transform s"
  by (auto simp: transform_def transform_cdt_def transform_current_thread_def transform_asid_table_def transform_objects_def)

lemma transform_ready_queues_update[simp]: "transform (s\<lparr> ready_queues := a \<rparr>) = transform s"
  by (auto simp: transform_def transform_cdt_def transform_current_thread_def transform_asid_table_def transform_objects_def)

lemma set_thread_state_ext_dcorres: "dcorres dc P P' (return ()) (set_thread_state_ext y)"
  apply (clarsimp simp: set_thread_state_ext_def)
  apply (rule dcorres_symb_exec_r)
    apply (rule dcorres_symb_exec_r)
      apply (rule dcorres_symb_exec_r)
        apply (clarsimp simp: corres_underlying_def when_def set_scheduler_action_def
                              modify_def bind_def put_def gets_def get_def return_def
                        split: option.splits)
       apply wp+
  done

(*Special set_cap case which is related to thread_state *)
lemma set_thread_state_corres:
  "dcorres dc \<top> (not_idle_thread y and K (cap = infer_tcb_pending_op y st) and valid_etcbs)
    (KHeap_D.set_cap (y, tcb_pending_op_slot) cap)
    (KHeap_A.set_thread_state y st)"
  apply (simp add:set_thread_state_def)
  apply (rule dcorres_absorb_gets_the)
  apply (rule dcorres_rhs_noop_below)
     apply (rule set_thread_state_ext_dcorres)
    apply (rule corres_guard_imp)
      apply (rule set_pending_cap_corres)
     apply simp
    apply (clarsimp dest!:get_tcb_SomeD simp:obj_at_def)
   apply (rule hoare_TrueI)+
  done

lemma set_cap_null_cap_corres:
  "dcorres dc \<top> (valid_idle and (\<lambda>s. fst slot \<noteq> idle_thread s) and valid_etcbs)
    (KHeap_D.set_cap (transform_cslot_ptr slot) cdl_cap.NullCap)
    (do set_original slot False;
        CSpaceAcc_A.set_cap cap.NullCap slot
    od)"
  apply (rule corres_dummy_return_pl)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="dc"])
       apply (rule set_original_dummy_corres)
      apply clarsimp
      apply (rule set_cap_corres)
       apply (clarsimp simp:transform_cap_def)
      apply (rule refl)
     apply wp+
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma mdb_cte_at_cte_wp_at:
  "\<lbrakk>mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s); cdt s slot = Some slot'\<rbrakk>
    \<Longrightarrow> (cte_wp_at ((\<noteq>) cap.NullCap) slot s)"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (case_tac slot,case_tac slot')
  apply (drule spec)+
  apply (auto)
  done

lemma mdb_cte_at_cte_wp_at':
  "\<lbrakk>mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s); cdt s slot = Some slot'\<rbrakk>
   \<Longrightarrow>(cte_wp_at ((\<noteq>) cap.NullCap) slot' s)"
  apply (case_tac slot,case_tac slot')
  apply (clarsimp simp:mdb_cte_at_def)
  done


lemma transform_cdt_slot_inj_on_mdb_cte_at:
  "\<lbrakk> mdb_cte_at (swp (cte_wp_at P) s) (cdt s) \<rbrakk> \<Longrightarrow>
       inj_on transform_cslot_ptr (dom (cdt s) \<union> ran (cdt s))"
  apply (rule transform_cdt_slot_inj_on_cte_at[where P=P and s=s], simp_all)
  apply (safe elim!: ranE)
   apply (drule(1) mdb_cte_atD | clarsimp simp: cte_wp_at_caps_of_state)+
  done

lemma transform_cdt_none:
  "\<lbrakk> cte_at slot s; mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s);
       (cdt s) slot = None \<rbrakk>
    \<Longrightarrow> transform_cdt s (transform_cslot_ptr slot) = None"
  apply (case_tac slot)
  apply (clarsimp simp: transform_cdt_def map_lift_over_eq_None)
  apply (rule ccontr, clarsimp)
  apply (subst(asm) transform_cslot_ptr_inj, simp_all)
  apply (drule(1) mdb_cte_atD)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma transform_cdt_some:
  "\<lbrakk> mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s);
      (cdt s) slot = Some slot' \<rbrakk>
  \<Longrightarrow> transform_cdt s (transform_cslot_ptr slot)
          = Some (transform_cslot_ptr slot')"
  apply (case_tac slot)
  apply (case_tac slot')
  apply (clarsimp simp: transform_cdt_def map_lift_over_eq_Some
                        transform_cdt_slot_inj_on_mdb_cte_at)
  apply auto
  done

lemma mdb_cte_transform_cdt_lift:
  "\<lbrakk>cte_at slot s; mdb_cte_at (swp (cte_wp_at((\<noteq>) cap.NullCap)) s ) (cdt s) \<rbrakk>
   \<Longrightarrow> transform_cdt s (transform_cslot_ptr slot)
        = (case ((cdt s) slot ) of
      None \<Rightarrow> None
    | Some slot' \<Rightarrow> Some (transform_cslot_ptr slot'))"
  apply (case_tac "(cdt s) slot")
    apply (clarsimp simp:transform_cdt_none transform_cdt_some)+
done

lemma cte_at_to_bl_eq:
  "\<lbrakk>bl_to_bin b = uint w; cte_at (a,b) s; cte_at (a,to_bl w) s\<rbrakk>
  \<Longrightarrow> to_bl w = b"
  apply (subgoal_tac "length b = length (to_bl w)")
    apply (simp add:uint_nat[symmetric])
    apply (rule to_bl_use_of_bl[THEN iffD2])
    apply (clarsimp simp:of_bl_def)
  apply (drule iffD1[OF cte_at_cases])+
  apply (erule disjE)
   apply (clarsimp simp: well_formed_cnode_n_def dom_def)
   apply (subgoal_tac "length b = sz")
    apply (subgoal_tac "length (to_bl w) = sz")
     apply simp
    apply (drule_tac x="to_bl w" in eqset_imp_iff)
    apply simp
   apply (drule_tac x=b in eqset_imp_iff)
   apply simp
  apply clarsimp
  apply (subgoal_tac "(b\<in> dom tcb_cap_cases)")
   apply (subgoal_tac  "((to_bl w)\<in> dom tcb_cap_cases)")
    apply (drule tcb_cap_cases_length)
    apply (drule tcb_cap_cases_length)
    apply clarsimp
   apply (clarsimp simp:dom_def)+
done

lemma transform_cdt_some_rev:
  "\<lbrakk> transform_cdt s (transform_cslot_ptr slot_a)
           = Some (transform_cslot_ptr slot);
    cte_at slot s; mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s)(cdt s) \<rbrakk>
  \<Longrightarrow>\<exists>slot_b. transform_cslot_ptr slot_b
        = transform_cslot_ptr slot_a \<and> (cdt s) slot_b = Some slot"
  apply (clarsimp simp: transform_cdt_def map_lift_over_eq_Some)
  apply (subst(asm) transform_cslot_ptr_inj, assumption, simp_all)
   apply (drule(1) mdb_cte_atD, clarsimp simp: cte_wp_at_caps_of_state)
  apply fastforce
  done

lemma page_table_not_in_cdt:"\<lbrakk>page_table_at a s;cte_wp_at P (a, ba) s\<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp:obj_at_def a_type_def)
  apply (clarsimp split:Structures_A.kernel_object.split_asm if_splits arch_kernel_obj.split_asm)
  apply (clarsimp simp:cte_wp_at_cases)
done

lemma page_directory_not_in_cdt:"\<lbrakk>page_directory_at a s;cte_wp_at P (a, ba) s\<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp:obj_at_def a_type_def)
  apply (clarsimp split:Structures_A.kernel_object.split_asm if_splits arch_kernel_obj.split_asm)
  apply (clarsimp simp:cte_wp_at_cases)
done

lemma asid_pool_not_in_cdt:"\<lbrakk>asid_pool_at a s;cte_wp_at P (a, ba) s\<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp:obj_at_def a_type_def)
  apply (clarsimp split:Structures_A.kernel_object.split_asm if_splits arch_kernel_obj.split_asm)
  apply (clarsimp simp:cte_wp_at_cases)
done

lemma dummy_remove_cdt_pt_slot:
  "dcorres dc \<top> ( (\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)) and valid_idle and page_table_at a)
    (remove_parent (a, y)) (return x)"
  supply if_cong[cong]
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:remove_parent_def corres_underlying_def return_def simpler_modify_def)
  apply (clarsimp simp:remove_parent_def exs_valid_def simpler_modify_def transform_def)
  apply (rule ext)
  apply (clarsimp simp:transform_cdt_def| rule conjI)+
    apply (clarsimp simp: map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (frule_tac slot="(aa,b)" in mdb_cte_at_cte_wp_at)
      apply simp
    apply (drule page_table_not_in_cdt)
      apply (simp add:transform_cslot_ptr_def)+
    apply (clarsimp simp:map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (frule_tac slot'="(a,bb)" in mdb_cte_at_cte_wp_at')
      apply simp
    apply (drule page_table_not_in_cdt)
      apply simp+
    apply (clarsimp simp: option_map_def  map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at
      split:if_splits option.splits| rule conjI)+
    apply (clarsimp simp:transform_cslot_ptr_def)
    apply (frule_tac slot="(a,bc)" in mdb_cte_at_cte_wp_at)
      apply simp
    apply (drule page_table_not_in_cdt)
      apply simp+
    apply (clarsimp simp: transform_cslot_ptr_def)
    apply (frule_tac slot="(a,bc)" in mdb_cte_at_cte_wp_at)
      apply simp
    apply (drule page_table_not_in_cdt)
      apply simp+
done

lemma dummy_remove_cdt_pd_slot:
  "dcorres dc \<top> ( (\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)) and valid_idle and page_directory_at a)
    (remove_parent (a,y)) (return x)"
  supply if_cong[cong]
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:remove_parent_def corres_underlying_def return_def simpler_modify_def)
  apply (clarsimp simp:remove_parent_def exs_valid_def simpler_modify_def transform_def)
  apply (rule ext)
  apply (clarsimp simp:transform_cdt_def| rule conjI)+
    apply (clarsimp simp: map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (frule_tac slot="(aa,b)" in mdb_cte_at_cte_wp_at)
      apply simp
    apply (drule page_directory_not_in_cdt)
      apply (simp add:transform_cslot_ptr_def)+
    apply (clarsimp simp:map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (frule_tac slot'="(a,bb)" in mdb_cte_at_cte_wp_at')
      apply simp
    apply (drule page_directory_not_in_cdt)
      apply simp+
    apply (clarsimp simp: option_map_def  map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at
      split:if_splits option.splits| rule conjI)+
    apply (clarsimp simp:transform_cslot_ptr_def)
    apply (frule_tac slot="(a,bc)" in mdb_cte_at_cte_wp_at)
      apply simp
    apply (drule page_directory_not_in_cdt)
      apply simp+
    apply (clarsimp simp: transform_cslot_ptr_def)
    apply (frule_tac slot="(a,bc)" in mdb_cte_at_cte_wp_at)
      apply simp
    apply (drule page_directory_not_in_cdt)
      apply simp+
done

lemma dummy_remove_cdt_asid_pool_slot:
  "dcorres dc \<top> ( (\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)) and valid_idle and asid_pool_at a)
    (remove_parent (a,y)) (return x)"
  supply if_cong[cong]
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:remove_parent_def corres_underlying_def return_def simpler_modify_def)
  apply (clarsimp simp:remove_parent_def exs_valid_def simpler_modify_def transform_def)
  apply (rule ext)
  apply (clarsimp simp:transform_cdt_def| rule conjI)+
    apply (clarsimp simp: map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (frule_tac slot="(aa,b)" in mdb_cte_at_cte_wp_at)
      apply simp
    apply (drule asid_pool_not_in_cdt)
      apply (simp add:transform_cslot_ptr_def)+
    apply (clarsimp simp:map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (frule_tac slot'="(a,bb)" in mdb_cte_at_cte_wp_at')
      apply simp
    apply (drule asid_pool_not_in_cdt)
      apply simp+
    apply (clarsimp simp: option_map_def  map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at
      split:if_splits option.splits| rule conjI)+
    apply (clarsimp simp:transform_cslot_ptr_def)
    apply (frule_tac slot="(a,bc)" in mdb_cte_at_cte_wp_at)
      apply simp
    apply (drule asid_pool_not_in_cdt)
      apply simp+
    apply (clarsimp simp: transform_cslot_ptr_def)
    apply (frule_tac slot="(a,bc)" in mdb_cte_at_cte_wp_at)
      apply simp
    apply (drule asid_pool_not_in_cdt)
      apply simp+
done

definition cdl_cdt_single_update :: "cdl_state \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_state"
where "cdl_cdt_single_update s c p \<equiv> s\<lparr>cdl_cdt:=(\<lambda>x. if x = c then Some p else (cdl_cdt s) x)\<rparr>"

definition abs_cdt_single_update :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> cslot_ptr \<Rightarrow> 'z::state_ext state"
where "abs_cdt_single_update s c p = s\<lparr>cdt:=(\<lambda>x. if x = c then Some p else (cdt s) x)\<rparr>"

definition cdl_cdt_single_remove :: "cdl_state \<Rightarrow> cdl_cap_ref  \<Rightarrow> cdl_state"
where "cdl_cdt_single_remove s c \<equiv> s\<lparr>cdl_cdt:=(\<lambda>x. if x = c then None else (cdl_cdt s) x)\<rparr>"

definition abs_cdt_single_remove :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> 'z::state_ext state"
where "abs_cdt_single_remove s c = s\<lparr>cdt:=(\<lambda>x. if x = c then None else (cdt s) x)\<rparr>"

definition cdl_cdt_set_update :: "cdl_state \<Rightarrow> cdl_cap_ref set \<Rightarrow> (cdl_cap_ref \<Rightarrow> cdl_cap_ref option) \<Rightarrow> cdl_state"
where "cdl_cdt_set_update s d f = s\<lparr>cdl_cdt:=(\<lambda>x. if x\<in> d then f x else (cdl_cdt s) x)\<rparr>"

definition abs_cdt_set_update :: "'z::state_ext state \<Rightarrow> cslot_ptr set \<Rightarrow> (cslot_ptr \<Rightarrow> cslot_ptr option) \<Rightarrow> 'z::state_ext state"
where "abs_cdt_set_update s d f = s\<lparr>cdt:=(\<lambda>x. if x\<in> d then f x else (cdt s) x)\<rparr>"

lemma cte_at_single_update : "cte_at x s \<Longrightarrow> cte_at x (abs_cdt_single_update s c p)"
  by (clarsimp simp:abs_cdt_single_update_def)

lemma cdt_single_update_eq:
assumes mdb:"mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)"
shows
"\<lbrakk>cte_at p s; cte_at c s\<rbrakk> \<Longrightarrow> cdl_cdt (cdl_cdt_single_update (transform s) (transform_cslot_ptr c) (transform_cslot_ptr p)) = transform_cdt (abs_cdt_single_update s c p)"
  apply (simp add: transform_cdt_def abs_cdt_single_update_def)
  apply (subst map_lift_over_upd[unfolded fun_upd_def])
   defer
   apply (rule ext)
   apply (clarsimp simp:cdl_cdt_single_update_def transform_def transform_cdt_def)
  apply (rule transform_cdt_slot_inj_on_cte_at[where P=\<top>])
  apply (auto simp: cte_wp_at_caps_of_state ran_def dest!: mdb_cte_atD [OF _ mdb])
  done

lemma cdt_single_remove_eq:
assumes mdb:"mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)"
shows
"\<lbrakk>cte_at c s\<rbrakk> \<Longrightarrow> cdl_cdt (cdl_cdt_single_remove (transform s) (transform_cslot_ptr c)) = transform_cdt (abs_cdt_single_remove s c)"
  apply (simp add: transform_cdt_def abs_cdt_single_remove_def)
  apply (subst map_lift_over_upd[unfolded fun_upd_def])
   defer
   apply (rule ext)
   apply (clarsimp simp:cdl_cdt_single_remove_def transform_def transform_cdt_def)
  apply (rule transform_cdt_slot_inj_on_cte_at[where P=\<top>])
  apply (auto simp: cte_wp_at_caps_of_state ran_def dest!: mdb_cte_atD [OF _ mdb])
  done

lemma dom_onto_ex:
  "\<lbrakk>f =  h` g ; x\<in> f\<rbrakk> \<Longrightarrow> \<exists>t. h t = x \<and> t\<in> g"
  apply (clarsimp simp:dom_def image_def | rule conjI)
  apply auto
done

lemma dom_onto_is:
  "\<lbrakk>f =  h` g ; x\<in> g\<rbrakk> \<Longrightarrow> h x \<in> f"
  apply (clarsimp simp: image_def)
  apply (rule bexI)
  apply auto
done

lemma cdt_set_update_eq:
assumes dom_onto: "df =  transform_cslot_ptr ` dg"
assumes exc:  "\<forall>x\<in> dg. \<forall>y. transform_cslot_ptr x = transform_cslot_ptr y \<longrightarrow> ((y\<in> dg) \<or> (\<not> cte_at y s))"
assumes ran_map:"\<forall>x\<in>dg. f (transform_cslot_ptr x) = map_option transform_cslot_ptr (g x)"
assumes mdb1:"mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)"
assumes mdb2:"mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) (abs_cdt_set_update s dg g)) (cdt (abs_cdt_set_update s dg g))"
shows
"cdl_cdt (cdl_cdt_set_update (transform s) df f)  = transform_cdt (abs_cdt_set_update s dg g)"
  apply (rule ext)
  apply (simp add:transform_cdt_def)
  apply (case_tac "x\<in> df")
    apply (clarsimp,rule sym)
    apply (clarsimp simp: map_lift_over_eq_cases cdl_cdt_set_update_def abs_cdt_set_update_def split:option.splits| rule conjI)+
using ran_map
      apply (drule_tac x = "(aa,ba)" in bspec)
        apply simp
      apply (clarsimp)
      apply (frule dom_onto[THEN dom_onto_ex])
      apply clarsimp
using exc
      apply (drule_tac x ="(ab,bb)" in bspec,simp)
      apply (drule_tac x ="(aa,ba)" in spec)
      apply clarsimp
      apply (rule classical)
      apply clarsimp
      apply (drule mdb_cte_atD[OF _ mdb1])
      apply (clarsimp simp:cte_wp_at_cte_at)
    apply (drule dom_onto[THEN dom_onto_ex])
      apply clarsimp
    apply (rule_tac x = aa in exI,rule_tac x = ba in exI)
    apply clarsimp
using ran_map
    apply (drule_tac x = "(aa,ba)" in bspec)
      apply simp
    apply (clarsimp simp:option_map_def split:option.splits)
using transform_cdt_slot_inj_on_mdb_cte_at[OF mdb2]
      apply (clarsimp simp:domI abs_cdt_set_update_def)
  apply (clarsimp simp:cdl_cdt_set_update_def transform_def transform_cdt_def)
  apply (clarsimp simp:map_lift_over_eq_cases split:option.splits)
  apply (simp add: transform_cdt_slot_inj_on_mdb_cte_at[OF mdb2] transform_cdt_slot_inj_on_mdb_cte_at[OF mdb1])
  apply (clarsimp simp:abs_cdt_set_update_def| rule conjI)+
    apply (drule_tac x= aa in spec,drule_tac x = ba in spec)
    apply (clarsimp split:if_splits)
    apply (drule dom_onto_is[OF dom_onto])
    apply simp
  apply (clarsimp simp:abs_cdt_set_update_def | rule conjI)+
using dom_onto_is[OF dom_onto]
  apply auto
done

definition weak_valid_mdb :: "'z::state_ext state \<Rightarrow>bool"
where "weak_valid_mdb s \<equiv> mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s) \<and> no_mloop (cdt s)"

lemma cdl_remove_parent_def':
 "remove_parent slot =
  modify (\<lambda>s. cdl_cdt_single_remove (cdl_cdt_set_update s
                                       {x. if cdl_cdt s x = Some slot then True else False}
                                       (\<lambda>x. cdl_cdt s slot)) slot)"
  apply (clarsimp simp:remove_parent_def simpler_modify_def bind_def)
  apply (rule ext)
  apply (clarsimp simp:cdl_cdt_single_remove_def cdl_cdt_set_update_def cong: if_cong)
done

lemma abs_remove_parent_def':
 "(do a\<leftarrow> gets cdt;set_cdt ((\<lambda>p. if a p = Some slot then a slot else a p) (slot := None)) od)= (modify (\<lambda>s. abs_cdt_single_remove(abs_cdt_set_update s {x. if cdt s x = Some slot then True else False} (\<lambda>x. cdt s slot)) slot))"
  apply (clarsimp simp:remove_parent_def simpler_modify_def bind_def set_cdt_def put_def get_def gets_def return_def)
  apply (rule ext)
  apply (clarsimp simp:abs_cdt_single_remove_def abs_cdt_set_update_def)
  apply (case_tac s)
  apply clarsimp
  apply (rule ext)
  apply clarsimp
done

lemma transform_cdt_single_update_helper:
  "s' = transform s \<Longrightarrow> cdl_cdt (cdl_cdt_single_update s' a b) = transform_cdt (abs_cdt_single_update s a' b') \<Longrightarrow> (cdl_cdt_single_update s' a b ) = transform (abs_cdt_single_update s a' b')"
  by (clarsimp simp:cdl_cdt_single_update_def abs_cdt_single_update_def transform_def transform_current_thread_def transform_asid_table_def)

lemma transform_cdt_set_update_helper:
  "s' = transform s \<Longrightarrow> cdl_cdt (cdl_cdt_set_update s' df f) = transform_cdt (abs_cdt_set_update s dg g) \<Longrightarrow> (cdl_cdt_set_update s' df f ) = transform (abs_cdt_set_update s dg g)"
  by (clarsimp simp:cdl_cdt_set_update_def abs_cdt_set_update_def transform_def transform_current_thread_def transform_asid_table_def)

lemma transform_cdt_single_remove_helper:
  "s'= transform s \<Longrightarrow> cdl_cdt (cdl_cdt_single_remove s' a) = transform_cdt (abs_cdt_single_remove s a') \<Longrightarrow> (cdl_cdt_single_remove (transform s) a) = transform (abs_cdt_single_remove s a')"
  by (clarsimp simp:cdl_cdt_single_remove_def abs_cdt_single_remove_def transform_def transform_current_thread_def transform_asid_table_def)

lemma remove_parent_corres:
  "dcorres dc \<top> (cte_at slot and weak_valid_mdb)
   (remove_parent (transform_cslot_ptr slot))
   (do a \<leftarrow> gets cdt;
           set_cdt
           ((\<lambda>p. if a p = Some slot then a slot else a p)
           (slot := None))
   od)"
  apply (subst cdl_remove_parent_def'[where slot = "(transform_cslot_ptr slot)"])
  apply (subst abs_remove_parent_def')
  apply (clarsimp simp:bind_def corres_underlying_def simpler_modify_def)
  apply (cut_tac df=" {x. cdl_cdt (transform b) x = Some (transform_cslot_ptr slot)}"
             and dg = "{x. cdt b x = Some slot}"
    and f = "\<lambda>x. cdl_cdt (transform b) (transform_cslot_ptr slot)" and g = "\<lambda>x. cdt b slot"
    and s = b
    in cdt_set_update_eq)
defer
    apply (clarsimp simp: weak_valid_mdb_def)
    apply (frule(1) mdb_cte_atD)
    apply (drule sym, subst(asm) transform_cslot_ptr_inj, assumption)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply clarsimp
defer
    apply (simp add:weak_valid_mdb_def)+
    apply (case_tac slot)
    apply (fastforce simp:mdb_cte_at_def abs_cdt_set_update_def dom_def)
    apply (drule transform_cdt_set_update_helper[rotated])
      apply simp
    apply clarsimp
    apply (rule sym, rule transform_cdt_single_remove_helper)
      apply simp
  apply (rule cdt_single_remove_eq)
  apply (case_tac slot)
    apply (simp add:weak_valid_mdb_def)
    apply (fastforce simp:mdb_cte_at_def abs_cdt_set_update_def dom_def)
    apply ((clarsimp simp:abs_cdt_set_update_def valid_irq_node_def)+)[3]
    apply (rule set_eqI)
    apply (clarsimp simp:dom_def image_def | rule conjI)+
    apply (rule iffI)
      apply (clarsimp simp:transform_cdt_def transform_def map_lift_over_eq_Some)
      apply (clarsimp simp:weak_valid_mdb_def)
      apply (subst(asm) transform_cslot_ptr_inj, assumption)
       apply (drule(1) mdb_cte_atD, clarsimp simp: cte_wp_at_caps_of_state)
      apply fastforce
    apply (clarsimp simp:weak_valid_mdb_def)
    apply (subgoal_tac "cte_at (aa,bb) b")
      apply (drule_tac slot = "(aa,bb)" in transform_cdt_some,simp+)
  apply (clarsimp simp:transform_def option_map_def split:if_splits option.splits |rule conjI)+
    apply (erule mdb_cte_at_cte_wp_at[THEN cte_wp_at_cte_at])
    apply simp
  apply (clarsimp simp:option_map_def split:option.splits|rule conjI)+
    apply (drule transform_cdt_none)
      apply (simp add:weak_valid_mdb_def transform_def)+
  apply clarsimp
  apply (rule transform_cdt_some)
    apply simp+
done

lemma dmo_maskIRQ_dcorres:
  "dcorres dc \<top> \<top> (return ()) (do_machine_op (maskInterrupt b st))"
  supply option.case_cong[cong]
  apply (clarsimp simp: do_machine_op_def corres_underlying_def return_def select_f_def in_monad)
  apply (clarsimp simp: maskInterrupt_def in_monad)
  apply (clarsimp simp: transform_def transform_current_thread_def)
  apply (rule ext)
  apply (simp add: transform_objects_def option_map_def map_add_def
            split: option.split)
  apply (simp add: transform_object_def transform_tcb_def
                   transform_full_intent_def Let_def
            split: Structures_A.kernel_object.split)
  apply (clarsimp simp: transform_intent_def cong: get_tcb_mrs_cong get_ipc_buffer_words_cong)
  done

lemma set_irq_state_dcorres:
  "dcorres dc \<top> \<top> (return ()) (set_irq_state irq st)"
  apply (simp add: set_irq_state_def)
  apply (rule corres_dummy_return_pl [where b="()"])
  apply (rule corres_underlying_split [where r'=dc])
     apply (clarsimp simp: corres_underlying_def in_monad return_def)
     apply (clarsimp simp: transform_def transform_current_thread_def
                           transform_objects_def transform_cdt_def
                           transform_asid_table_def)
    apply simp
    apply (rule dmo_maskIRQ_dcorres)
   apply wp+
  done

lemma dcorres_gets_all_param:
  "(\<And>x. dcorres R P P' h (g x)) \<Longrightarrow> dcorres R P P' h (do x \<leftarrow> gets f; g x od)"
  by (clarsimp simp: corres_underlying_def bind_def gets_def get_def return_def)

lemma empty_slot_ext_dcorres: "dcorres dc P P' (return ()) (empty_slot_ext slot v)"
  apply (clarsimp simp: empty_slot_ext_def)
  apply (auto simp: corres_underlying_def update_cdt_list_def set_cdt_list_def
                        modify_def bind_def put_def gets_def get_def return_def  split: option.splits if_split)
  done

lemma cap_case_irq_handler_not[simp]: "\<forall>irq. v \<noteq> cap.IRQHandlerCap irq \<Longrightarrow> (case v of cap.IRQHandlerCap irq \<Rightarrow> f irq | _ \<Rightarrow> g) = g"
  by (case_tac v; simp)

lemma empty_slot_corres:
  "dcorres dc \<top>
           (weak_valid_mdb and valid_idle and not_idle_thread (fst slot) and valid_etcbs)
           (PageTableUnmap_D.empty_slot (transform_cslot_ptr slot))
           (IpcCancel_A.empty_slot slot v)"
  apply (clarsimp simp:PageTableUnmap_D.empty_slot_def IpcCancel_A.empty_slot_def)
  apply (rule get_cap_no_fail)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where r'="%x y. x=transform_cap y"])
       apply (rule get_cap_corres)
       apply simp
      apply (case_tac "capa = cap.NullCap")
       apply (subgoal_tac "cap = cdl_cap.NullCap")
        apply clarsimp
       apply (clarsimp simp:transform_cap_def split:cap.splits arch_cap.splits)
      apply (subgoal_tac "cap \<noteq> cdl_cap.NullCap")
       apply clarsimp
       apply (rule dcorres_gets_all_param)
       apply (rule_tac P="%a. dcorres dc P P' h a" for P P' h in subst[OF bind_assoc[where m="gets cdt"]])
       apply (rule corres_split[where r'="dc"])
          apply (rule remove_parent_corres)
         apply (rule corres_add_noop_lhs)
         apply (rule_tac Q'="\<lambda>_. valid_etcbs and valid_idle and (\<lambda>s. fst slot \<noteq> idle_thread s)"
                in corres_split_forwards')
            apply (rule empty_slot_ext_dcorres)
           apply (wp empty_slot_ext_valid_etcbs | simp)+
         apply (rule corres_guard_imp)
           apply (rule corres_dummy_return_pl)
           apply (rule corres_split[OF set_original_dummy_corres])
             apply (rule corres_dummy_return_l)
             apply (rule corres_split[where r'=dc])
                apply simp
                apply (rule set_cap_corres; simp)
               apply (case_tac "\<exists>irq. v = cap.IRQHandlerCap irq"; clarsimp)
               apply (clarsimp simp: deleted_irq_handler_def)
               apply (fold dc_def)
               apply (rule set_irq_state_dcorres)
              apply (wp | simp del: fun_upd_apply)+
        apply (wp|simp add: set_cdt_def dc_def)+
      apply (clarsimp simp:transform_cap_def split:cap.splits arch_cap.splits)
     apply wp+
   apply clarsimp
   apply (simp add: not_idle_thread_def)+
  done

lemma valid_idle_fast_finalise[wp]:
  "\<lbrace>invs\<rbrace> IpcCancel_A.fast_finalise p q \<lbrace>%r. valid_idle\<rbrace>"
  apply (case_tac p)
             apply simp_all
     apply (wp,simp add:valid_state_def invs_def)
    apply (rule hoare_post_imp[where Q="%r. invs"])
     apply (clarsimp simp:valid_state_def invs_def,wp cancel_all_ipc_invs)
    apply clarsimp
   apply (rule hoare_post_imp[where Q="%r. invs"])
    apply (clarsimp simp:valid_state_def invs_def,wp unbind_maybe_notification_invs cancel_all_signals_invs)
   apply clarsimp
  apply wp
  apply (simp add:valid_state_def invs_def)
  done

lemma valid_irq_node_fast_finalise[wp]:
  "\<lbrace>invs\<rbrace> IpcCancel_A.fast_finalise p q \<lbrace>%r. valid_irq_node\<rbrace>"
  apply (case_tac p; simp)
     apply (wp,simp add:valid_state_def invs_def)
    apply (rule hoare_post_imp[where Q="%r. invs"])
      apply (clarsimp simp:valid_state_def invs_def,wp cancel_all_ipc_invs)
      apply clarsimp
    apply (rule hoare_post_imp[where Q="%r. invs"])
      apply (clarsimp simp:valid_state_def invs_def,wp unbind_maybe_notification_invs cancel_all_signals_invs)
      apply clarsimp
  apply wp
  apply (simp add:valid_state_def invs_def)
  done

lemma invs_mdb_fast_finalise[wp]:
  "\<lbrace>invs\<rbrace> IpcCancel_A.fast_finalise p q \<lbrace>%r. valid_mdb\<rbrace>"
  apply (case_tac p; simp)
     apply (wp,simp add:valid_state_def invs_def)
    apply (rule hoare_post_imp[where Q="%r. invs"])
      apply (clarsimp simp:valid_state_def invs_def,wp cancel_all_ipc_invs)
      apply clarsimp
    apply (rule hoare_post_imp[where Q="%r. invs"])
      apply (clarsimp simp:valid_state_def invs_def,wp unbind_maybe_notification_invs cancel_all_signals_invs)
      apply clarsimp
  apply wp
  apply (simp add:valid_state_def invs_def)
  done

lemma fast_finalise_not_idle_thread[wp]:
  "\<lbrace>not_idle_thread y\<rbrace> IpcCancel_A.fast_finalise p q \<lbrace>%r. not_idle_thread y\<rbrace>"
  apply (simp add:not_idle_thread_def)
  apply (wp fast_finalise_it)
  done

lemma block_lift:
  "\<lbrakk>kheap b word = Some (TCB tcb_type); ekheap b word = Some etcb; transform_tcb (machine_state b) word tcb_type etcb = Tcb cdl_tcb_type\<rbrakk>
  \<Longrightarrow> is_thread_blocked_on_endpoint cdl_tcb_type ep = (case tcb_state tcb_type of
      Structures_A.thread_state.BlockedOnReceive p _ \<Rightarrow> ep = p
    | Structures_A.thread_state.BlockedOnSend p _ \<Rightarrow> ep = p
    | Structures_A.thread_state.BlockedOnNotification p \<Rightarrow> ep = p
    | _ \<Rightarrow> False)"
  apply (clarsimp simp:is_thread_blocked_on_endpoint_def transform_tcb_def infer_tcb_pending_op_def infer_tcb_bound_notification_def tcb_slots)
  apply (case_tac "tcb_state tcb_type")
         apply (auto)
  done

(* Before we handle fast_finalise, we need sth form invs that can give us some preconditions of ep and ntfn *)

definition ntfn_waiting_set :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref set"
where "ntfn_waiting_set epptr s \<equiv>
  {tcb. \<exists>t. ((kheap s tcb) = Some (TCB t))
      \<and> ((tcb_state t) = Structures_A.thread_state.BlockedOnNotification epptr)}"




definition none_is_waiting_ntfn :: "obj_ref \<Rightarrow> 'z::state_ext state\<Rightarrow>bool"
where "none_is_waiting_ntfn epptr s \<equiv> (ntfn_waiting_set epptr s) = {}"

definition ep_waiting_set_send :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref set"
where "ep_waiting_set_send epptr s \<equiv>
   {tcb. \<exists>t payload can_grant.
        kheap s tcb = Some (TCB t)
      \<and> tcb_state t = Structures_A.thread_state.BlockedOnSend epptr payload
      \<and> can_grant = sender_can_grant payload}"

definition none_is_sending_ep:: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where "none_is_sending_ep epptr s \<equiv> (ep_waiting_set_send epptr s) = {}"

definition ep_waiting_set_recv :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref set"
where "ep_waiting_set_recv epptr s \<equiv>
   {tcb. \<exists>t payload can_grant.
        kheap s tcb = Some (TCB t)
      \<and> tcb_state t = Structures_A.thread_state.BlockedOnReceive epptr payload
      \<and> can_grant = receiver_can_grant payload}"

definition none_is_receiving_ep:: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where "none_is_receiving_ep epptr s \<equiv> (ep_waiting_set_recv epptr s) = {}"

lemma ep_waiting_set_send_lift:
  "\<lbrakk>valid_idle s; valid_etcbs s\<rbrakk> \<Longrightarrow>
   get_waiting_sync_send_threads epptr (transform s) =
   ep_waiting_set_send epptr s"
  apply (rule set_eqI)
  apply (clarsimp simp: get_waiting_sync_send_threads_def)
  apply (rule iffI)
   apply (clarsimp simp: ep_waiting_set_send_def
                         transform_def transform_objects_def restrict_map_Some_iff)
   apply (clarsimp simp: infer_tcb_pending_op_def transform_object_def
                         transform_tcb_def tcb_slots infer_tcb_bound_notification_def
                   split: Structures_A.kernel_object.splits nat.splits
                          Structures_A.thread_state.splits | drule(1) valid_etcbs_tcb_etcb)+
   apply (simp split: arch_kernel_obj.splits)
  apply (clarsimp simp: ep_waiting_set_send_def map_add_def
                        transform_def transform_objects_def
                  split: option.splits if_splits)
  apply (clarsimp simp: restrict_map_Some_iff)
  apply (rule conjI)
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
   apply (drule(1) valid_etcbs_tcb_etcb)
  apply (clarsimp simp: infer_tcb_pending_op_def transform_tcb_def tcb_slots)
  done

lemma ep_waiting_set_recv_lift:
  "\<lbrakk>valid_idle s; valid_etcbs s\<rbrakk> \<Longrightarrow>
  get_waiting_sync_recv_threads epptr (transform s) =
  ep_waiting_set_recv epptr s"
  apply (rule set_eqI)
  apply (clarsimp simp: get_waiting_sync_recv_threads_def)
  apply (rule iffI)
   apply (clarsimp simp: ep_waiting_set_recv_def
                         transform_def transform_objects_def)
   apply (clarsimp simp: restrict_map_Some_iff)
   apply (clarsimp simp: infer_tcb_pending_op_def transform_object_def tcb_slots
                         transform_tcb_def restrict_map_Some_iff
                   split: Structures_A.kernel_object.splits nat.splits
                          Structures_A.thread_state.splits | drule(1) valid_etcbs_tcb_etcb)+
   apply (simp split:arch_kernel_obj.splits)
  apply (clarsimp simp: ep_waiting_set_recv_def map_add_def
                        transform_def transform_objects_def
                        transform_object_def restrict_map_Some_iff
                 split: option.splits)
  apply (clarsimp simp: valid_idle_def obj_at_def pred_tcb_at_def)
  apply (clarsimp simp: infer_tcb_pending_op_def transform_tcb_def tcb_slots | drule(1) valid_etcbs_tcb_etcb)+
  done

lemma ntfn_waiting_set_lift:
  "\<lbrakk>valid_idle s; valid_etcbs s\<rbrakk> \<Longrightarrow>
  get_waiting_ntfn_recv_threads ntfnptr (transform s) =
  ntfn_waiting_set ntfnptr s"
  supply option.case_cong[cong]
  apply (rule set_eqI)
  apply (clarsimp simp: get_waiting_ntfn_recv_threads_def)
  apply (rule iffI)
   apply (clarsimp simp: transform_def transform_objects_def)
   apply (clarsimp simp: restrict_map_Some_iff)
   apply (clarsimp simp: infer_tcb_pending_op_def transform_object_def
                         transform_tcb_def restrict_map_Some_iff tcb_slots
                  split: Structures_A.kernel_object.splits nat.splits
                         Structures_A.thread_state.splits | drule(1) valid_etcbs_tcb_etcb)+
    apply (clarsimp simp: ntfn_waiting_set_def)
   apply(drule(1) valid_etcbs_tcb_etcb, clarsimp)
   apply (simp split: arch_kernel_obj.splits)
  apply (clarsimp simp: ntfn_waiting_set_def
                 split: Structures_A.kernel_object.splits)
  apply (clarsimp simp: valid_idle_def obj_at_def pred_tcb_at_def)
  apply (clarsimp simp: transform_def transform_object_def
                        transform_tcb_def transform_objects_def tcb_slots
                        infer_tcb_pending_op_def map_add_def restrict_map_Some_iff
                 split: option.splits | drule(1) valid_etcbs_tcb_etcb)+
  done

definition ntfn_bound_set :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> obj_ref set"
where "ntfn_bound_set ntfnptr s \<equiv>
  {tcb. \<exists>t. ((kheap s tcb) = Some (TCB t))
      \<and> ((tcb_bound_notification t) = Some ntfnptr)}"

lemma ntfn_bound_set_lift:
  "\<lbrakk>valid_idle s; valid_etcbs s\<rbrakk> \<Longrightarrow>
  get_bound_notification_threads ntfnptr (transform s) =
  ntfn_bound_set ntfnptr s"
  apply (rule set_eqI)
  apply (clarsimp simp: get_bound_notification_threads_def ntfn_bound_set_def)
  apply (rule iffI)
   apply (clarsimp simp: transform_def transform_objects_def)
   apply (clarsimp simp: restrict_map_Some_iff)
   apply (clarsimp simp: infer_tcb_bound_notification_def transform_object_def
                         transform_tcb_def restrict_map_Some_iff tcb_slots
                  split: Structures_A.kernel_object.splits option.splits
                         Structures_A.thread_state.splits
                         ARM_A.arch_kernel_obj.splits| drule(1) valid_etcbs_tcb_etcb)+
  apply (clarsimp simp: transform_def transform_object_def
                        transform_tcb_def transform_objects_def tcb_slots valid_idle_def obj_at_def
                        infer_tcb_bound_notification_def map_add_def restrict_map_Some_iff pred_tcb_at_def
                 split: nat.splits option.splits | drule(1) valid_etcbs_tcb_etcb)+
  done

definition
valid_ntfn_abstract :: "Structures_A.notification \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where "valid_ntfn_abstract ntfn ptr s \<equiv> kheap s ptr = Some (kernel_object.Notification ntfn) \<and> (set_option (ntfn_bound_tcb ntfn) = ntfn_bound_set ptr s) \<and> (
  case ntfn_obj ntfn of
    Structures_A.ntfn.IdleNtfn \<Rightarrow> none_is_waiting_ntfn ptr s
  | Structures_A.ntfn.WaitingNtfn queue \<Rightarrow> queue\<noteq>[] \<and>
        ((set queue) = (ntfn_waiting_set ptr s)) \<and>
        (\<forall>p'. (kheap s ptr = kheap s p') \<longrightarrow> (ptr=p'))
  | Structures_A.ntfn.ActiveNtfn _ \<Rightarrow> none_is_waiting_ntfn ptr s)"

definition
valid_ep_abstract :: "Structures_A.endpoint \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where "valid_ep_abstract ep ptr s \<equiv> kheap s ptr = Some (kernel_object.Endpoint ep) \<and> (
  case ep of
    Structures_A.endpoint.IdleEP \<Rightarrow> (none_is_sending_ep ptr s \<and> none_is_receiving_ep ptr s)
  | Structures_A.endpoint.RecvEP queue \<Rightarrow> queue\<noteq>[] \<and>
        (set queue = ep_waiting_set_recv ptr s) \<and>
        (none_is_sending_ep ptr s)\<and>
        (\<forall>p'. (kheap s ptr = kheap s p') \<longrightarrow> (ptr=p'))
  | Structures_A.endpoint.SendEP queue \<Rightarrow> queue\<noteq>[] \<and>
        (set queue = ep_waiting_set_send ptr s) \<and>
        (none_is_receiving_ep ptr s) \<and>
        (\<forall>p'. (kheap s ptr = kheap s p') \<longrightarrow> (ptr=p'))
  )"

lemma ntfn_not_waiting_ep_send:
  "\<lbrakk> valid_objs s;kheap s epptr = Some (kernel_object.Notification ntfn) \<rbrakk>
       \<Longrightarrow> ep_waiting_set_send epptr s = {}"
  apply (rule set_eqI)
  apply (clarsimp simp: ep_waiting_set_send_def)
  apply (simp add: valid_objs_def)
  apply (rename_tac ptr t payload)
  apply (drule_tac x=ptr in bspec)
   apply (clarsimp simp: dom_def)
  apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def obj_at_def is_ep_def
                 split: Structures_A.kernel_object.splits)
  done

lemma ntfn_not_waiting_ep_recv:
  "\<lbrakk> valid_objs s;kheap s epptr = Some (kernel_object.Notification ntfn) \<rbrakk>
        \<Longrightarrow> ep_waiting_set_recv epptr s = {}"
  apply (rule set_eqI)
  apply (clarsimp simp: ep_waiting_set_recv_def)
  apply (simp add: valid_objs_def)
  apply (rename_tac ptr t payload)
  apply (drule_tac x=ptr in bspec)
   apply (clarsimp simp: dom_def)
  apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def obj_at_def is_ep_def
                 split: Structures_A.kernel_object.splits)
  done

lemma ep_not_waiting_ntfn:
  "\<lbrakk> valid_objs s;kheap s epptr = Some (kernel_object.Endpoint ep) \<rbrakk>
       \<Longrightarrow> ntfn_waiting_set epptr s = {}"
  apply (rule set_eqI)
  apply (clarsimp simp:ntfn_waiting_set_def)
  apply (simp add:valid_objs_def)
  apply (drule_tac x= x in bspec)
   apply (clarsimp simp:dom_def)
  by (clarsimp simp:valid_obj_def valid_tcb_def valid_tcb_state_def obj_at_def is_ntfn_def
              split:Structures_A.kernel_object.splits)

(* Following 2 lemmas is useful, it tells us that under certain condition, we can get valid_ep and valid_ntfn,
   which helps us ruling out the idle thread and constract a map between the waiting list and waiting set
*)
lemma get_endpoint_pick:
  "\<lbrakk>valid_state s; kheap s epptr = Some (kernel_object.Endpoint endpoint)\<rbrakk>
  \<Longrightarrow> valid_ep_abstract endpoint epptr s"
  apply (clarsimp simp:valid_ep_abstract_def)
  apply (case_tac  endpoint)
    apply (clarsimp simp:valid_state_def valid_pspace_def sym_refs_def)
    apply (clarsimp simp:none_is_sending_ep_def none_is_receiving_ep_def)
    apply (rule conjI)
     apply (rule set_eqI)
     apply (clarsimp simp:ep_waiting_set_send_def)
     apply (rename_tac ptr t payload)
     apply (drule_tac x=ptr in spec)
     apply (clarsimp simp: state_refs_of_def)
    apply (rule set_eqI)
    apply (clarsimp simp:ep_waiting_set_recv_def)
    apply (rename_tac ptr t payload)
    apply (drule_tac x=ptr in spec)
    apply (clarsimp simp:state_refs_of_def)
   apply (clarsimp simp:valid_state_def valid_pspace_def valid_objs_def)
   apply (drule_tac x=epptr in bspec)
    apply (clarsimp simp:dom_def)
   apply (clarsimp simp:valid_obj_def valid_ep_def)
   apply (rule conjI)
    apply (rule sym)
    apply (rule antisym)
     apply (clarsimp simp:ep_waiting_set_send_def sym_refs_def)
     apply (rename_tac ptr t payload)
     apply (drule_tac x=ptr in spec)
     apply (clarsimp simp:state_refs_of_def)
    apply (clarsimp simp:ep_waiting_set_send_def sym_refs_def)
    apply (drule_tac x= epptr in spec)
    apply (clarsimp simp:state_refs_of_def ep_waiting_set_send_def split:option.splits)
    apply (drule_tac x= x in bspec)
     apply simp
    apply clarsimp
    apply (case_tac y)
        apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
               split:Structures_A.kernel_object.splits)+
       apply (force simp:tcb_bound_refs_def2 split:Structures_A.thread_state.splits)
      apply (clarsimp simp:ep_waiting_set_send_def)
      apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
             split:Structures_A.kernel_object.splits)+
      apply (clarsimp split:Structures_A.endpoint.splits)
     apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
            split:Structures_A.kernel_object.splits)+
     apply (clarsimp simp: ntfn_bound_refs_def2 split:Structures_A.ntfn.splits)
    apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
           split:Structures_A.kernel_object.splits)+
   apply (rule conjI)
    apply (clarsimp simp:none_is_receiving_ep_def)
    apply (rule set_eqI)
    apply (clarsimp simp: ep_waiting_set_recv_def sym_refs_def)
    apply (rename_tac ptr t payload)
    apply (drule_tac x = ptr in spec)
    apply (clarsimp simp:state_refs_of_def)
   apply clarsimp
   defer
   apply (clarsimp simp:valid_state_def valid_pspace_def valid_objs_def)
   apply (drule_tac x=epptr in bspec)
    apply (clarsimp simp:dom_def)
   apply (clarsimp simp:valid_obj_def valid_ep_def)
   apply (rule conjI)
    apply (rule sym)
    apply (rule antisym)
     apply (clarsimp simp:ep_waiting_set_recv_def sym_refs_def)
     apply (rename_tac ptr t payload)
     apply (drule_tac x = ptr in spec)
     apply (clarsimp simp:state_refs_of_def)
    apply (clarsimp simp:ep_waiting_set_recv_def sym_refs_def)
    apply (drule_tac x= epptr in spec)
    apply (clarsimp simp:state_refs_of_def ep_waiting_set_recv_def split:option.splits)
    apply (drule_tac x= x in bspec)
     apply simp
    apply clarsimp
    apply (case_tac y)
        apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
               split:Structures_A.kernel_object.splits)+
       apply (force simp: tcb_bound_refs_def2 split:Structures_A.thread_state.splits)
      apply (clarsimp simp:ep_waiting_set_recv_def)
      apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
             split:Structures_A.kernel_object.splits)+
      apply (clarsimp split:Structures_A.endpoint.splits)
     apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
           split:Structures_A.kernel_object.splits)+
     apply (clarsimp simp: ntfn_bound_refs_def2 split:Structures_A.ntfn.splits)
    apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
           split:Structures_A.kernel_object.splits)+
   apply (rule conjI)
    apply (clarsimp simp:none_is_sending_ep_def)
    apply (rule set_eqI)
    apply (clarsimp simp: ep_waiting_set_send_def sym_refs_def)
    apply (rename_tac ptr t payload)
    apply (drule_tac x = ptr in spec)
    apply (clarsimp simp:state_refs_of_def)
   apply (rename_tac list)
   apply clarsimp
   apply (subgoal_tac "ko_at (Endpoint (Structures_A.endpoint.RecvEP list)) epptr s
                    \<and> ko_at (Endpoint (Structures_A.endpoint.RecvEP list)) p' s")
    apply (clarsimp simp: neq_Nil_conv)
    apply (drule(1) sym_refs_ko_atD)+
    apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_def2)
   apply (clarsimp simp: obj_at_def)
  apply (rename_tac list p')
  apply (subgoal_tac "ko_at (Endpoint (Structures_A.endpoint.SendEP list)) epptr s
                    \<and> ko_at (Endpoint (Structures_A.endpoint.SendEP list)) p' s")
   apply (clarsimp simp: neq_Nil_conv)
   apply (drule(1) sym_refs_ko_atD)+
   apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_def2)
  apply (clarsimp simp:obj_at_def)
  done

lemma ep_q_refs_of_no_TCBBound[simp]:
  "(x, TCBBound) \<notin> ep_q_refs_of ep"
  by (clarsimp simp: ep_q_refs_of_def split: Structures_A.endpoint.splits)

lemma ntfn_bound_refs_no_TCBBound[simp]:
  "(x, TCBBound) \<notin> ntfn_bound_refs ep"
  by (clarsimp simp: ntfn_bound_refs_def split: option.splits)

lemma kheap_to_ko_at:
  "kheap s x = Some aa \<Longrightarrow> ko_at aa x s"
  by (clarsimp simp: obj_at_def)

lemma get_notification_pick:
  "\<lbrakk>kheap s epptr = Some (kernel_object.Notification notification);
    valid_state s\<rbrakk>
      \<Longrightarrow> valid_ntfn_abstract notification epptr s"
  apply (clarsimp simp:valid_ntfn_abstract_def)
  apply (rule conjI[rotated])
   apply (case_tac "ntfn_obj notification")
     apply (clarsimp simp:valid_state_def valid_pspace_def sym_refs_def)
     apply (clarsimp simp:none_is_waiting_ntfn_def)
     apply (rule set_eqI)
     apply (clarsimp simp:ntfn_waiting_set_def)
     apply (drule_tac x=x in spec)
     apply (clarsimp simp: state_refs_of_def ntfn_bound_refs_def2)
    apply (clarsimp simp:valid_state_def valid_pspace_def valid_objs_def)
    apply (drule_tac x=epptr in bspec)
     apply (clarsimp simp:dom_def)
    apply (clarsimp simp:valid_obj_def valid_ntfn_def)
    apply (rule conjI)
     apply (rule sym)
     apply (rule antisym)
      apply (clarsimp simp:ntfn_waiting_set_def sym_refs_def)
      apply (drule_tac x = x in spec)
      apply (clarsimp simp:state_refs_of_def ntfn_bound_refs_def2)
     apply (clarsimp simp:ntfn_waiting_set_def sym_refs_def)
     apply (drule_tac x= epptr in spec)
     apply (clarsimp simp:state_refs_of_def ntfn_waiting_set_def ntfn_bound_refs_def2 split: option.splits)
      apply (drule_tac x= x in bspec)
       apply simp
      apply (clarsimp)
      apply (case_tac y)
          apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
                 split:Structures_A.kernel_object.splits)+
         apply (clarsimp simp: tcb_bound_refs_def2 split:Structures_A.thread_state.splits)
        apply (clarsimp simp:ntfn_waiting_set_def)
        apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
               split:Structures_A.kernel_object.splits)+
        apply (clarsimp simp: split:Structures_A.endpoint.splits)
       apply (clarsimp simp:refs_of_def tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
              split:Structures_A.kernel_object.splits)+
       apply (clarsimp simp: ntfn_bound_refs_def2 split:Structures_A.ntfn.splits)
      apply (clarsimp simp:refs_of_def tcb_bound_refs_def2 ntfn_bound_refs_def2 tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
             split:Structures_A.kernel_object.splits split: Structures_A.thread_state.splits Structures_A.endpoint.splits Structures_A.ntfn.splits)+
    apply (subgoal_tac "ko_at (Notification notification) epptr s
                      \<and> ko_at (Notification notification) p' s")
     apply (clarsimp simp: neq_Nil_conv)
     apply (drule(1) sym_refs_ko_atD)+
     apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_def2)
    apply (clarsimp simp: obj_at_def)
   apply (clarsimp simp:valid_state_def valid_pspace_def sym_refs_def)
   apply (clarsimp simp:none_is_waiting_ntfn_def)
   apply (rule set_eqI)
   apply (clarsimp simp:ntfn_waiting_set_def)
   apply (drule_tac x=x in spec)
   apply (clarsimp simp: state_refs_of_def ntfn_bound_refs_def2)
  apply (case_tac "ntfn_bound_tcb notification")
   apply (clarsimp simp: valid_state_def ntfn_bound_set_def valid_pspace_def)
   apply (drule_tac x=x in sym_refsD[rotated])
    apply (fastforce simp: state_refs_of_def)
   apply (clarsimp simp: symreftype_inverse' state_refs_of_def ntfn_q_refs_no_NTFNBound)
  apply (clarsimp simp: ntfn_bound_set_def valid_state_def valid_pspace_def)
  apply (frule_tac x=epptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def)
  apply (clarsimp simp: symreftype_inverse' state_refs_of_def)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp simp: refs_of_def ntfn_q_refs_no_TCBBound tcb_st_refs_no_TCBBound tcb_bound_refs_def split: option.splits Structures_A.kernel_object.splits)
  apply clarsimp
  apply (drule_tac x=x in kheap_to_ko_at)
  apply (drule sym_refs_ko_atD, simp add: state_refs_of_def)
  apply (clarsimp split: option.splits)
  apply (drule_tac x=a in kheap_to_ko_at)
  apply (drule sym_refs_ko_atD, simp add: state_refs_of_def)
  apply (case_tac a)
      apply (simp_all add: ntfn_q_refs_no_TCBBound)
  apply (clarsimp simp: tcb_bound_refs_def2)
  apply (clarsimp simp: refs_of_def obj_at_def ntfn_q_refs_no_NTFNBound)
  done

definition tcb_filter_modify ::"cdl_object_id set\<Rightarrow>(cdl_object option \<Rightarrow> cdl_object option)\<Rightarrow> unit k_monad"
where "tcb_filter_modify filter_set f \<equiv> modify
 (\<lambda>s. s\<lparr>cdl_objects := (\<lambda>x. if x\<in> filter_set then (f (cdl_objects s x)) else (cdl_objects s x)) \<rparr>)"

lemma tcb_filter_modify_decompose:
  "\<lbrakk> filter_set = setA \<union> setB; (setA \<inter> setB) = {}\<rbrakk>
    \<Longrightarrow> (do tcb_filter_modify setA f;tcb_filter_modify setB f od) = (tcb_filter_modify filter_set f)"
  apply (simp add:bind_def)
  apply (rule ext)
  apply (clarsimp simp:tcb_filter_modify_def bind_def simpler_modify_def)
  apply (case_tac s)
  apply (clarsimp simp:option_map_def)
  apply (rule ext)
  apply (clarsimp split:option.splits|rule conjI)+
  apply (fastforce)
  done

lemma set_list_modify_corres_helper:
  "\<lbrakk> distinct update_list;
    inj_on lift_func (set update_list);
    filter_set = (lift_func ` set update_list);
    \<forall>a\<in> set update_list. dcorres dc \<top> (P a) (tcb_filter_modify {lift_func a} f) (f' a);
    \<forall>x\<in>set update_list. \<forall>y \<in> set update_list. x \<noteq> y \<longrightarrow> \<lbrace>P y\<rbrace> f' x \<lbrace>\<lambda>rv. P y\<rbrace>
    \<rbrakk> \<Longrightarrow> dcorres dc \<top> (\<lambda>s. \<forall>x\<in>(set update_list). (P x s)) (tcb_filter_modify filter_set f)
             (mapM_x (\<lambda>t. f' t) update_list)"
  apply simp
  apply (thin_tac "filter_set = lift_func ` set update_list")
  proof (induct update_list)
    case Nil
    show ?case
      apply (clarsimp simp:tcb_filter_modify_def)
      apply (clarsimp simp: return_def simpler_modify_def mapM_x_def sequence_x_def corres_underlying_def)
     done
   next
   case (Cons a ls)
   show ?case
      using Cons.prems
      apply clarsimp
      apply (subgoal_tac "insert (lift_func a) (lift_func ` set ls) = {lift_func a} \<union> (lift_func ` set ls)")
       apply (drule_tac tcb_filter_modify_decompose [where f=f])
        apply simp
       apply (drule sym)
       apply (clarsimp simp:mapM_x_Cons)
       apply (rule corres_guard_imp)
         apply (rule corres_split)
            apply simp
           apply (rule Cons.hyps[simplified]; clarsimp)
          apply wp
         apply (rule hoare_vcg_ball_lift)
         apply fastforce+
      done
qed

lemma filter_modify_empty_corres:
  "filter_set = {}  \<Longrightarrow> dcorres dc \<top> \<top> (tcb_filter_modify filter_set f)
             (return a)"
  by (clarsimp simp:corres_underlying_def tcb_filter_modify_def return_def simpler_modify_def)


lemma cancel_all_ipc_def_alt1: "PageTableUnmap_D.cancel_all_ipc ep =
  (  do s\<leftarrow>get;
     tcb_filter_modify {x. \<exists>tcb. (cdl_objects s) x = Some (Tcb tcb) \<and> is_thread_blocked_on_endpoint tcb ep}
       (\<lambda>x. (case x of Some (Tcb tcb) \<Rightarrow> Some (Tcb (remove_pending_operation tcb RestartCap))))
  od)"
  apply (simp add:PageTableUnmap_D.cancel_all_ipc_def get_def simpler_modify_def tcb_filter_modify_def)
  apply (clarsimp simp:bind_def)
  apply (rule ext)
  apply clarsimp
  apply (case_tac s)
  apply clarsimp
  apply (rule ext)
  apply (clarsimp simp:option_map_def split:option.splits)
  apply (case_tac x2)
    apply simp_all
done

lemma valid_objs_valid_ep_simp:
  "\<lbrakk>valid_objs s;kheap s epptr = Some (kernel_object.Endpoint ep)\<rbrakk> \<Longrightarrow> valid_ep ep s"
   apply (simp add:valid_objs_def)
   apply (drule_tac x = epptr in bspec)
     apply (simp add: dom_def)
   apply (clarsimp simp: valid_obj_def)
done

lemma valid_objs_valid_ntfn_simp:
  "\<lbrakk>valid_objs s;kheap s epptr = Some (kernel_object.Notification ep)\<rbrakk> \<Longrightarrow> valid_ntfn ep s"
   apply (simp add:valid_objs_def)
   apply (drule_tac x = epptr in bspec)
     apply (simp add: dom_def)
   apply (clarsimp simp: valid_obj_def)
done

lemma tcb_type_set_obj_ep:
  "\<lbrace>(=) s'a\<rbrace> KHeap_A.set_object word1 (kernel_object.Endpoint Structures_A.endpoint.IdleEP)
   \<lbrace>\<lambda>r s. \<forall>x. tcb_at x s \<longrightarrow> tcb_at x s'a\<rbrace>"
  including unfold_objects
  by (wpsimp wp: set_object_wp_strong simp: a_type_def is_tcb_def)

lemma tcb_type_at_set_ep:
  "\<lbrace>(=) s'a\<rbrace> set_endpoint word1 Structures_A.endpoint.IdleEP \<lbrace>\<lambda>r s. \<forall>x. tcb_at x s \<longrightarrow> tcb_at x s'a\<rbrace>"
  apply (clarsimp simp: set_simple_ko_def)
  apply (wp tcb_type_set_obj_ep)
   apply (clarsimp simp: get_object_def)
   apply wp
  apply (clarsimp)
  done

(* The following filter function is infact a combinition of 3 sets *)
lemma is_thread_blocked_on_sth:
  "{x. \<exists>tcb. cdl_objects s x = Some (Tcb tcb) \<and> is_thread_blocked_on_endpoint tcb ep}
    = (get_waiting_sync_recv_threads ep s) \<union> (get_waiting_sync_send_threads ep s) \<union> (get_waiting_ntfn_recv_threads ep s)"
  apply (rule set_eqI)
  apply (rule iffI)
   apply (clarsimp simp: is_thread_blocked_on_endpoint_def split: option.splits)
   apply (case_tac y; simp add: get_waiting_sync_recv_threads_def get_waiting_sync_send_threads_def
                                get_waiting_ntfn_recv_threads_def)
  apply (fastforce simp: is_thread_blocked_on_endpoint_def get_waiting_sync_recv_threads_def
                         get_waiting_sync_send_threads_def get_waiting_ntfn_recv_threads_def)
  done

lemma set_ep_exec_wp: (* generalise? *)
  "\<lbrace>(=) s\<rbrace> set_endpoint epptr ep \<lbrace>\<lambda>r s'. s' = update_kheap ((kheap s)(epptr \<mapsto> Endpoint ep)) s\<rbrace> "
  by (wpsimp simp: set_simple_ko_def set_object_def get_object_def a_type_def fun_upd_def
            split: option.splits Structures_A.kernel_object.splits)

lemma set_ntfn_exec_wp:
  "\<lbrace>(=) s\<rbrace> set_notification epptr ep \<lbrace>\<lambda>r s'. s' = update_kheap ((kheap s)(epptr \<mapsto> Notification ep)) s\<rbrace> "
  by (wpsimp simp: set_simple_ko_def set_object_def get_object_def a_type_def fun_upd_def
            split: option.splits Structures_A.kernel_object.splits)

lemma pending_thread_in_recv_not_idle:
  "\<lbrakk>valid_state s'; valid_idle s';
    ko_at (kernel_object.Endpoint (Structures_A.endpoint.RecvEP list)) epptr s'; a\<in> set list\<rbrakk> \<Longrightarrow> not_idle_thread a s'"
  apply (frule get_endpoint_pick)
    apply (fastforce simp:obj_at_def is_ep_def)
  apply (clarsimp simp:valid_ep_abstract_def)
  apply (clarsimp simp:ep_waiting_set_recv_def)
  apply (clarsimp simp:not_idle_thread_def pred_tcb_at_def valid_idle_def obj_at_def)
done

lemma pending_thread_in_send_not_idle:
  "\<lbrakk> valid_state s';valid_idle s'; a\<in> set list;
          ko_at (kernel_object.Endpoint (Structures_A.endpoint.SendEP list)) epptr s'\<rbrakk>
  \<Longrightarrow> not_idle_thread a s'"
  apply (frule get_endpoint_pick)
    apply (fastforce simp:obj_at_def is_ep_def)
  apply (clarsimp simp:valid_ep_abstract_def)
  apply (clarsimp simp:ep_waiting_set_send_def)
  apply (clarsimp simp:not_idle_thread_def pred_tcb_at_def valid_idle_def obj_at_def)
done

lemma pending_thread_in_wait_not_idle:
  "\<lbrakk> valid_state s'; valid_idle s'; a \<in> set list;
     ko_at (kernel_object.Notification ntfn) epptr s';
     ntfn_obj ntfn = (Structures_A.ntfn.WaitingNtfn list)\<rbrakk>
  \<Longrightarrow> not_idle_thread a s'"
  apply (frule get_notification_pick[rotated])
    apply (fastforce simp:obj_at_def is_ep_def)
  apply (clarsimp simp:valid_ntfn_abstract_def)
  apply (clarsimp simp:ntfn_waiting_set_def)
  apply (clarsimp simp:not_idle_thread_def pred_tcb_at_def valid_idle_def obj_at_def)
done


lemma cnode_not_idle:
  "\<lbrakk>valid_idle s'; kheap s' ptr = Some (CNode sz cnode)\<rbrakk> \<Longrightarrow> not_idle_thread ptr s'"
  by (clarsimp simp:valid_idle_def not_idle_thread_def pred_tcb_at_def obj_at_def)

lemma irq_node_image_not_idle:
  "\<lbrakk>valid_idle s'; valid_irq_node s'\<rbrakk>
  \<Longrightarrow> not_idle_thread (interrupt_irq_node s' y) s' "
  apply (clarsimp simp:valid_irq_node_def)
  apply (drule_tac x = y in spec)
  apply (clarsimp simp:obj_at_def is_cap_table_def)
  apply (clarsimp split:Structures_A.kernel_object.splits)
  apply (erule cnode_not_idle)
  apply fastforce
  done

lemma generates_pending_not_idle:
  "\<lbrakk>valid_idle s';st_tcb_at generates_pending y s'\<rbrakk> \<Longrightarrow> not_idle_thread y s'"
  by (clarsimp simp :valid_idle_def pred_tcb_at_def obj_at_def generates_pending_def not_idle_thread_def)

lemma valid_idle_set_thread_state_wp:
  "\<lbrace>valid_idle and not_idle_thread a\<rbrace>set_thread_state a Structures_A.thread_state.Restart \<lbrace>\<lambda>x. valid_idle\<rbrace>"
  apply wp
  apply (simp add: not_idle_thread_def)
done

lemma tcb_at_set_thread_state_wp:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set list. tcb_at x s \<and> not_idle_thread x s)\<rbrace>
  set_thread_state a Structures_A.thread_state.Restart
  \<lbrace>\<lambda>x s. (\<forall>x\<in>set list. tcb_at x s \<and> not_idle_thread x s)\<rbrace>"
  apply (rule hoare_Ball_helper)
   apply (wpsimp simp:not_idle_thread_def)+
 done

lemma invalid_cte_wp_at_pending_slot:
  "\<lbrakk>tcb_at y s;transform_cslot_ptr (ad, bd) = (y, tcb_pending_op_slot);
    cte_wp_at ((\<noteq>) cap.NullCap) (ad, bd) s\<rbrakk> \<Longrightarrow> False"
    apply (clarsimp simp:transform_cslot_ptr_def
      cte_wp_at_cases tcb_at_def dest!:get_tcb_SomeD)
      apply (clarsimp simp:tcb_cap_cases_def tcb_cnode_index_def tcb_pending_op_slot_def
        split:if_splits)
    apply (clarsimp simp:bl_to_bin_def)+
done

(* cap_dl wp rule: a pending cap will never have parent *)
lemma remove_parent_dummy_when_pending_slot:
  "\<lbrakk>mdb_cte_at (swp (cte_wp_at ((\<noteq>)cap.NullCap) ) s) (cdt s); tcb_at y s\<rbrakk>
  \<Longrightarrow>\<lbrace>(=) (transform s)\<rbrace> remove_parent (y, tcb_pending_op_slot) \<exists>\<lbrace>\<lambda>r. (=) (transform s)\<rbrace>"
  apply (clarsimp simp:remove_parent_def exs_valid_def simpler_modify_def transform_def)
  apply (rule ext)
  apply (clarsimp simp:transform_cdt_def| rule conjI)+
    apply (clarsimp simp: map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (frule_tac slot'="(aa,bb)" in mdb_cte_at_cte_wp_at')
      apply simp
    apply (drule_tac ad = aa in  invalid_cte_wp_at_pending_slot)
      apply fastforce+
    apply (clarsimp simp: map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at split:if_splits)
    apply (drule_tac ad = ab in invalid_cte_wp_at_pending_slot)
      apply fastforce+
      apply (erule mdb_cte_at_cte_wp_at')
        apply simp+
    apply (clarsimp simp: map_lift_over_def transform_cdt_slot_inj_on_mdb_cte_at | rule conjI)+
      apply (drule_tac ad = ac in invalid_cte_wp_at_pending_slot)
        apply fastforce+
      apply (erule mdb_cte_at_cte_wp_at)
        apply simp+
    apply clarsimp
      apply (drule_tac ad = aa in invalid_cte_wp_at_pending_slot)
        apply fastforce+
done

lemma corres_dummy_set_thread_state:
  "\<not>generates_pending st \<Longrightarrow>
  dcorres dc \<top> (st_tcb_at (Not \<circ> generates_pending) thread)
          (return ()) (set_thread_state thread st)"
  supply option.case_cong[cong]
  apply (simp add:set_thread_state_def)
  apply (rule dcorres_absorb_gets_the)
  apply (rule dcorres_rhs_noop_below)
  apply (rule set_thread_state_ext_dcorres)
  apply (rule corres_free_set_object)
  apply (clarsimp simp: transform_def)
  apply (clarsimp simp:transform_current_thread_def)
  apply (clarsimp dest!:get_tcb_SomeD simp:st_tcb_at_def obj_at_def)
  apply (rule ext)
  apply (clarsimp simp: restrict_map_def map_add_def generates_pending_def
                        st_tcb_at_def obj_at_def
                  cong: transform_full_intent_cong
                 split: Structures_A.thread_state.split_asm
                  simp: transform_tcb_def transform_objects_def
                        infer_tcb_pending_op_def)
  apply (rule hoare_TrueI)+
  done

lemma corres_dummy_set_thread_inactive:
  "dcorres dc \<top> (st_tcb_at (Not \<circ> generates_pending) thread) (return ())
  (set_thread_state thread Structures_A.thread_state.Inactive)"
  by (rule corres_dummy_set_thread_state) simp

lemma corres_dummy_set_thread_state_Running:
  "dcorres dc \<top> (not_idle_thread thread and valid_etcbs)
  (KHeap_D.set_cap (thread, tcb_pending_op_slot) RunningCap)
  (set_thread_state thread Structures_A.Running)"
  apply (simp add:set_thread_state_def)
  apply (rule dcorres_absorb_gets_the)
  apply (rule dcorres_rhs_noop_below)
  apply (rule set_thread_state_ext_dcorres)
  apply (rule corres_guard_imp)
    apply (rule set_pending_cap_corres)
   apply simp
  apply (clarsimp simp: infer_tcb_pending_op_def
    tcb_at_def obj_at_def
    dest!: get_tcb_SomeD)
  apply (rule hoare_TrueI)+
  done

lemma fast_finalise_no_effect:
  "\<lbrakk>opt_cap (y, tcb_pending_op_slot) (transform s) = Some cap;
   not_idle_thread y s;tcb_at y s; valid_etcbs s \<rbrakk>
  \<Longrightarrow> PageTableUnmap_D.fast_finalise cap (PageTableUnmap_D.is_final_cap' cap x) = return ()"
  apply (clarsimp simp:opt_cap_def transform_def tcb_at_def dest!:get_tcb_SomeD)
  apply (clarsimp simp:slots_of_def transform_objects_def
    not_idle_thread_def restrict_map_def
    split:option.splits if_splits)
  apply (drule(1) valid_etcbs_tcb_etcb, clarsimp)
  apply (clarsimp simp:object_slots_def transform_tcb_def)
  apply (clarsimp simp:infer_tcb_pending_op_def tcb_slots
    split:Structures_A.thread_state.splits | drule(1) valid_etcbs_tcb_etcb)+
  done

lemma tcb_sched_action_dcorres: "dcorres dc P P' (return ()) (tcb_sched_action f t)"
  apply (clarsimp simp: tcb_sched_action_def)
  apply (rule dcorres_symb_exec_r)
    apply (rule dcorres_symb_exec_r)
      apply (rule dcorres_symb_exec_r)
       apply (clarsimp simp: set_tcb_queue_def modify_def bind_def return_def get_def put_def corres_underlying_def)
       apply (wp | simp)+
  done

lemma tcb_sched_action_transform: "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> tcb_sched_action f t \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  by (clarsimp simp: tcb_sched_action_def etcb_at_def| wp )+

lemma reschedule_required_dcorres: "dcorres dc P P' (return ()) reschedule_required"
  apply (clarsimp simp: reschedule_required_def)
  apply (rule dcorres_symb_exec_r)
    apply (rule dcorres_symb_exec_r)
      apply (clarsimp simp: set_scheduler_action_def (*switch_thread_def*) modify_def bind_def return_def get_def put_def corres_underlying_def)
     apply (case_tac "\<exists>t. rv = switch_thread t")
      apply (clarsimp | wp)+
    apply (clarsimp split: Deterministic_A.scheduler_action.splits | rule tcb_sched_action_transform | wp )+
  done

lemma fast_finalise_recv_ep:
  "dcorres dc \<top> (valid_state and valid_idle and ko_at (kernel_object.Endpoint (Structures_A.endpoint.RecvEP list)) epptr and valid_etcbs)
  (PageTableUnmap_D.cancel_all_ipc epptr)
  (do queue \<leftarrow> get_ep_queue (Structures_A.endpoint.RecvEP list);
      _ \<leftarrow> set_endpoint epptr Structures_A.endpoint.IdleEP;
      _ \<leftarrow> mapM_x (\<lambda>t. do _ \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                         tcb_sched_action tcb_sched_enqueue t
                  od) queue;
      reschedule_required
  od)"
  supply if_cong[cong]
  apply (simp add:get_ep_queue_def cancel_all_ipc_def_alt1)
  apply (rule dcorres_absorb_get_l)
  apply clarsimp
  apply (rule corres_dummy_return_pl)
  apply (rule_tac Q="\<lambda>r. \<top>" and
                  Q'="\<lambda>r s. (s = update_kheap ((kheap s')(epptr\<mapsto> (Endpoint Structures_A.endpoint.IdleEP))) s')"
          in corres_split_forwards' [where r'="dc"])
     apply (rule corres_dummy_set_sync_ep[THEN corres_guard_imp],(simp|wp)+)
   apply (rule set_ep_exec_wp)
  apply clarsimp
  apply (rule_tac
    Q'="\<lambda>s. (\<forall>x\<in> (set list). valid_idle s \<and> tcb_at x s \<and> not_idle_thread x s \<and> idle_thread s = idle_thread s' \<and> is_etcb_at x s)"
    in corres_guard_imp[where Q=\<top>])
    apply (rule dcorres_rhs_noop_below_True[OF reschedule_required_dcorres])
    apply (rule_tac lift_func = id in set_list_modify_corres_helper)
        apply (clarsimp simp:obj_at_def)
        apply (drule valid_objs_valid_ep_simp[rotated])
         apply (simp add:valid_state_def valid_pspace_def)
        apply (simp add:valid_ep_def)
       apply (simp add:inj_on_def)
      apply (frule_tac epptr=epptr in get_endpoint_pick,simp add:obj_at_def)
      apply (simp add:valid_ep_abstract_def none_is_sending_ep_def none_is_receiving_ep_def obj_at_def)+
      apply (subst is_thread_blocked_on_sth[simplified])
      apply (clarsimp simp:ntfn_waiting_set_lift ep_waiting_set_send_lift ep_waiting_set_recv_lift)
      apply (drule ep_not_waiting_ntfn[rotated])
       apply (simp add:valid_state_def valid_pspace_def)
      apply clarsimp
     apply (clarsimp simp:set_thread_state_def tcb_filter_modify_def bind_assoc)
     apply (rule dcorres_absorb_gets_the)
     apply (rule dcorres_rhs_noop_below_True[OF dcorres_rhs_noop_below_True[OF tcb_sched_action_dcorres _],
                                             OF set_thread_state_ext_dcorres _])
     apply (clarsimp simp: set_object_def get_object_def in_monad simpler_modify_def put_def
                           return_def get_def bind_def corres_underlying_def mk_ef_def select_f_def)
     apply (frule ep_not_idle)
      apply (fastforce simp:obj_at_def is_ep_def)
     apply (simp add:transform_def transform_current_thread_def)
     apply (rule ext)
     apply (clarsimp dest!: get_tcb_SomeD simp:transform_objects_update_other split:if_splits option.splits)
     apply (drule get_tcb_rev)+
     apply (simp add:obj_at_def)
     apply (frule_tac epptr = epptr in get_endpoint_pick,simp,clarsimp simp:valid_ep_abstract_def)
     apply (clarsimp simp:ep_waiting_set_recv_def)
     apply (drule get_tcb_rev)+
     apply  (clarsimp simp:lift_simp not_idle_thread_def)
     apply (drule(1) valid_etcbs_get_tcb_get_etcb)+
     apply (auto simp: transform_tcb_def remove_pending_operation_def infer_tcb_pending_op_def
                       restrict_map_def tcb_slots infer_tcb_bound_notification_def
                       map_add_def get_tcb_def get_etcb_def is_etcb_at_def is_tcb
                 cong: transform_full_intent_cong split: option.splits)[1]
    apply (clarsimp simp:not_idle_thread_def | wp)+
    apply (frule_tac pending_thread_in_recv_not_idle)
       apply (simp add:not_idle_thread_def)+
  apply (frule ep_not_idle)
   apply (fastforce simp:obj_at_def is_ep_def)
  apply (clarsimp simp:valid_idle_def pred_tcb_at_def obj_at_def ep_not_idle not_idle_thread_def)
  apply (drule_tac epptr=epptr in get_endpoint_pick)
   apply (simp add:obj_at_def)
  apply (clarsimp simp:valid_ep_abstract_def)
  apply (clarsimp simp:ep_waiting_set_recv_def)
  apply (drule_tac ptr=x in valid_etcbs_tcb_etcb)
   apply (auto simp: is_etcb_at_def)
  done

lemma fast_finalise_send_ep:
  "dcorres dc \<top> (valid_state and valid_idle and ko_at (kernel_object.Endpoint (Structures_A.endpoint.SendEP list)) epptr and valid_etcbs)
  (PageTableUnmap_D.cancel_all_ipc epptr)
  (do queue \<leftarrow> get_ep_queue (Structures_A.endpoint.SendEP list);
      _ \<leftarrow> set_endpoint epptr Structures_A.endpoint.IdleEP;
      _ \<leftarrow> mapM_x (\<lambda>t. do _ \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                          tcb_sched_action tcb_sched_enqueue t
                  od)
              queue;
      reschedule_required
  od)"
  supply if_cong[cong]
  apply (simp add:get_ep_queue_def cancel_all_ipc_def_alt1)
  apply (rule dcorres_absorb_get_l)
  apply clarsimp
  apply (rule corres_dummy_return_pl)
  apply (rule_tac Q="\<lambda>r. \<top>" and
                  Q'="\<lambda>r s. (s = update_kheap ((kheap s')(epptr\<mapsto> (Endpoint Structures_A.endpoint.IdleEP))) s')"
          in corres_split_forwards' [where r'="dc"])
     apply (rule corres_dummy_set_sync_ep[THEN corres_guard_imp],simp+)
   apply (rule set_ep_exec_wp)
  apply clarsimp
  apply (rule_tac Q'="\<lambda>s. (\<forall>x\<in> (set list). tcb_at x s \<and> is_etcb_at x s \<and> not_idle_thread x s \<and> valid_idle s \<and> idle_thread s = idle_thread s')"
    in corres_guard_imp[where Q=\<top>])
    apply (rule dcorres_rhs_noop_below_True[OF reschedule_required_dcorres])
    apply (rule_tac lift_func = id in set_list_modify_corres_helper)
        apply (clarsimp simp: obj_at_def)
        apply (drule valid_objs_valid_ep_simp[rotated])
         apply (simp add: valid_state_def valid_pspace_def)
        apply (simp add: valid_ep_def)
       apply (simp add: inj_on_def)
      apply (frule_tac epptr=epptr in get_endpoint_pick)
       apply (simp add: valid_ep_abstract_def none_is_sending_ep_def none_is_receiving_ep_def obj_at_def)+
      apply (subst is_thread_blocked_on_sth[simplified])
      apply (clarsimp simp: ntfn_waiting_set_lift ep_waiting_set_send_lift ep_waiting_set_recv_lift)
      apply (drule ep_not_waiting_ntfn[rotated])
       apply (simp add: valid_state_def valid_pspace_def)
      apply clarsimp
     apply (clarsimp simp: set_thread_state_def tcb_filter_modify_def bind_assoc)
     apply (rule dcorres_absorb_gets_the)
     apply (rule dcorres_rhs_noop_below_True[OF dcorres_rhs_noop_below_True[OF tcb_sched_action_dcorres _],
                                             OF set_thread_state_ext_dcorres _])
     apply (clarsimp simp: set_object_def get_object_def in_monad simpler_modify_def put_def
                           return_def get_def bind_def corres_underlying_def select_f_def mk_ef_def)
     apply (frule ep_not_idle)
      apply (fastforce simp: obj_at_def is_ep_def)
     apply (simp add: transform_def transform_current_thread_def)
     apply (rule ext)
     apply (clarsimp dest!: get_tcb_SomeD simp:transform_objects_update_other split:if_splits option.splits)
     apply (drule get_tcb_rev)+
     apply (simp add: obj_at_def)
     apply (frule_tac epptr = epptr in get_endpoint_pick,simp,clarsimp simp:valid_ep_abstract_def)
     apply (clarsimp simp: ep_waiting_set_send_def)
     apply (drule get_tcb_rev)+
     apply  (clarsimp simp: lift_simp not_idle_thread_def)
     apply (auto simp: transform_tcb_def remove_pending_operation_def infer_tcb_pending_op_def restrict_map_def infer_tcb_bound_notification_def tcb_slots
                            map_add_def is_tcb get_tcb_def is_etcb_at_def split: option.splits
                      cong: transform_full_intent_cong)[1]
    apply clarsimp
    apply (clarsimp simp: not_idle_thread_def | wp)+
    apply (frule_tac a = "idle_thread s" in   pending_thread_in_send_not_idle)
       apply (simp add: not_idle_thread_def)+
  apply (frule ep_not_idle)
   apply (fastforce simp: obj_at_def is_ep_def)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def ep_not_idle not_idle_thread_def)
  apply (drule_tac epptr=epptr in get_endpoint_pick)
   apply (simp add: obj_at_def)
  apply (clarsimp simp: valid_ep_abstract_def ep_waiting_set_send_def)
  apply (drule_tac ptr=x in valid_etcbs_tcb_etcb)
   apply (auto simp: is_etcb_at_def)
  done

lemma fast_finalise_wait_ntfn:
  "dcorres dc \<top>
     (valid_state and valid_idle and valid_etcbs
      and ko_at (kernel_object.Notification ntfn) epptr
      and (\<lambda>_. ntfn_obj ntfn = (Structures_A.ntfn.WaitingNtfn list)))
     (PageTableUnmap_D.cancel_all_ipc epptr)
     (do _ \<leftarrow> set_notification epptr $ ntfn_set_obj ntfn Structures_A.ntfn.IdleNtfn;
         _ \<leftarrow> mapM_x (\<lambda>t. do _ \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                             tcb_sched_action tcb_sched_enqueue t
                          od) list;
         reschedule_required
      od)"
  supply if_cong[cong] option.case_cong[cong]
  apply (simp add:cancel_all_ipc_def_alt1)
  apply (rule dcorres_absorb_get_l)
  apply clarsimp
  apply (rule corres_dummy_return_pl)
  apply (rule corres_split_forwards'[where r'=dc and Q="\<lambda>_. \<top>", OF _ _ set_ntfn_exec_wp])
    apply (rule corres_dummy_set_notification[THEN corres_guard_imp],simp+)
  apply (rule_tac Q'=
    "\<lambda>s. (\<forall>x\<in> (set list). tcb_at x s \<and> is_etcb_at x s \<and> not_idle_thread x s \<and> valid_idle s \<and> idle_thread s = idle_thread s')"
    in corres_guard_imp[where Q=\<top>])
    apply (rule dcorres_rhs_noop_below_True[OF reschedule_required_dcorres])
    apply (rule_tac lift_func = id in set_list_modify_corres_helper)
        apply (clarsimp simp:obj_at_def)
        apply (drule valid_objs_valid_ntfn_simp[rotated])
         apply (simp add:valid_state_def valid_pspace_def)
        apply (simp add:valid_ntfn_def)
       apply (simp add:inj_on_def)
      apply (clarsimp simp:obj_at_def)
      apply (frule_tac epptr=epptr in get_notification_pick)
       apply (simp add:valid_ntfn_abstract_def)+
      apply (subst is_thread_blocked_on_sth[simplified])
      apply (clarsimp simp:ntfn_waiting_set_lift ep_waiting_set_send_lift ep_waiting_set_recv_lift)
      apply (frule ntfn_not_waiting_ep_recv[rotated])
       apply (simp add:valid_state_def valid_pspace_def)
      apply (drule ntfn_not_waiting_ep_send[rotated])
       apply (simp add:valid_state_def valid_pspace_def)
      apply clarsimp
     apply (clarsimp simp:set_thread_state_def tcb_filter_modify_def bind_assoc)
     apply (rule dcorres_absorb_gets_the)
     apply (rule dcorres_rhs_noop_below_True[OF dcorres_rhs_noop_below_True[OF tcb_sched_action_dcorres _], OF set_thread_state_ext_dcorres _])
     apply (clarsimp simp: set_object_def get_object_def in_monad simpler_modify_def put_def
                           return_def get_def bind_def corres_underlying_def select_f_def mk_ef_def)
     apply (frule ntfn_not_idle)
      apply (fastforce simp: obj_at_def is_ntfn_def)
     apply (clarsimp dest!:get_tcb_SomeD split:if_splits)
     apply (drule get_tcb_rev)+
     apply (clarsimp simp:transform_def transform_current_thread_def)
     apply (rule ext)
     apply (clarsimp dest!: get_tcb_SomeD simp:transform_objects_update_other split:if_splits option.splits)
     apply (drule get_tcb_rev)+
     apply (clarsimp simp:obj_at_def)
     apply (frule_tac epptr = epptr in get_notification_pick,simp,clarsimp simp:valid_ntfn_abstract_def)
     apply (clarsimp split:option.splits simp:lift_simp not_idle_thread_def transform_tcb_def)
     apply (fastforce simp: remove_pending_operation_def transform_tcb_def infer_tcb_pending_op_def restrict_map_def infer_tcb_bound_notification_def tcb_slots
                            map_add_def is_tcb get_tcb_def is_etcb_at_def split: option.splits
                      cong: transform_full_intent_cong)
    apply (clarsimp simp:not_idle_thread_def | wp)+
    apply (frule_tac a = "idle_thread s" in   pending_thread_in_wait_not_idle)
        apply (simp add:not_idle_thread_def)+
  apply (frule ntfn_not_idle)
   apply (fastforce simp:obj_at_def is_ntfn_def)
  apply (clarsimp simp:valid_idle_def st_tcb_at_def obj_at_def ep_not_idle not_idle_thread_def)
  apply (drule_tac epptr=epptr in get_notification_pick)
   apply (simp)
  apply (clarsimp simp:valid_ntfn_abstract_def ntfn_waiting_set_def)
  apply (drule_tac ptr=x in valid_etcbs_tcb_etcb)
   apply (auto simp: is_etcb_at_def pred_tcb_at_def obj_at_def)
  done

lemma dcorres_cancel_all_ipc:
  "dcorres dc \<top> (valid_state and valid_idle and valid_etcbs) (PageTableUnmap_D.cancel_all_ipc oid)
          (IpcCancel_A.cancel_all_ipc oid)"
  apply (simp add:IpcCancel_A.cancel_all_ipc_def IpcCancel_A.cancel_all_signals_def
                  PageTableUnmap_D.fast_finalise_def partial_inv_def)
  apply (clarsimp simp:get_simple_ko_def get_object_def bind_assoc gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_def corres_free_fail partial_inv_def a_type_def
          split:Structures_A.kernel_object.splits, safe)
  apply (rename_tac endpoint y)
  apply (case_tac endpoint)
    apply (clarsimp simp:cancel_all_ipc_def_alt1)
    apply (rule dcorres_absorb_get_l)
    apply (rule filter_modify_empty_corres[THEN corres_guard_imp])
      apply (subst is_thread_blocked_on_sth[simplified])
      apply clarsimp
      apply (frule_tac epptr = oid in get_endpoint_pick,simp)
      apply (simp add:valid_ep_abstract_def none_is_sending_ep_def none_is_receiving_ep_def)
      apply (simp add:ntfn_waiting_set_lift ep_waiting_set_send_lift ep_waiting_set_recv_lift)
      apply (drule ep_not_waiting_ntfn[rotated])
       apply (simp add:valid_state_def valid_pspace_def)
      apply simp
     apply clarsimp+
   apply (rule corres_guard_imp)
     apply (rule fast_finalise_send_ep)
    apply (simp add:obj_at_def)+
  apply (rule corres_guard_imp)
    apply (rule fast_finalise_recv_ep)
   apply (simp add:obj_at_def)+
  done

lemma dcorres_cancel_all_signals:
  "dcorres dc \<top> (valid_state and valid_idle and valid_etcbs) (PageTableUnmap_D.cancel_all_ipc oid)
          (cancel_all_signals oid)"
  apply (clarsimp simp: cancel_all_signals_def get_simple_ko_def get_object_def bind_assoc gets_def)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:assert_def corres_free_fail partial_inv_def a_type_def
                 split:Structures_A.kernel_object.splits, safe)
  apply (rename_tac ntfn_ext y)
  apply (case_tac "ntfn_obj ntfn_ext")
    apply (clarsimp simp:cancel_all_ipc_def_alt1)
    apply (rule dcorres_absorb_get_l)
    apply (rule filter_modify_empty_corres[THEN corres_guard_imp])
      apply (subst is_thread_blocked_on_sth[simplified])
      apply clarsimp
      apply (frule_tac epptr = oid in get_notification_pick,simp)
      apply (simp add:valid_ntfn_abstract_def none_is_waiting_ntfn_def)
      apply (simp add:ntfn_waiting_set_lift ep_waiting_set_send_lift ep_waiting_set_recv_lift)
      apply (frule ntfn_not_waiting_ep_send[rotated])
       apply (simp add:valid_state_def valid_pspace_def)
      apply (drule ntfn_not_waiting_ep_recv[rotated])
       apply (simp add:valid_state_def valid_pspace_def)
      apply clarsimp+
   apply (rule corres_guard_imp)
     apply (rule fast_finalise_wait_ntfn[simplified])
    apply (simp add:obj_at_def)+
  apply (clarsimp simp:cancel_all_ipc_def_alt1)
  apply (rule dcorres_absorb_get_l)
  apply (rule filter_modify_empty_corres[THEN corres_guard_imp])
    apply (subst is_thread_blocked_on_sth[simplified])
    apply clarsimp
    apply (frule_tac epptr = oid in get_notification_pick,simp)
    apply (simp add:valid_ntfn_abstract_def none_is_waiting_ntfn_def)
    apply (simp add:ntfn_waiting_set_lift ep_waiting_set_send_lift ep_waiting_set_recv_lift)
    apply (frule ntfn_not_waiting_ep_send[rotated])
     apply (simp add:valid_state_def valid_pspace_def)
    apply (drule ntfn_not_waiting_ep_recv[rotated])
     apply (simp add:valid_state_def valid_pspace_def)
    apply clarsimp+
  done

lemma transform_full_intent_update_tcb_boundntfn[simp]:
  "transform_full_intent m ptr (update_tcb_boundntfn ntfn_opt a)
  = transform_full_intent m ptr a"
  apply (case_tac a)
  apply (simp add:transform_full_intent_def Let_def)
  apply (simp add:get_tcb_message_info_def
    get_tcb_mrs_def get_ipc_buffer_words_def)
  done

lemma set_boundntfn_cap_corres:
  "dcorres dc (\<lambda>_. True)
   (not_idle_thread y and ko_at (TCB obj) y and K (cap = infer_tcb_bound_notification ntfn_opt) and
    valid_etcbs)
   (KHeap_D.set_cap (y, tcb_boundntfn_slot) cap)
   (KHeap_A.set_object y (TCB (update_tcb_boundntfn ntfn_opt obj)))"
apply (simp add: KHeap_D.set_cap_def gets_def gets_the_def bind_assoc not_idle_thread_def)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: obj_at_def)
 apply (drule(1) valid_etcbs_tcb_etcb, clarsimp)
  apply (frule opt_object_tcb[rotated, rotated])
    apply (fastforce simp: get_tcb_def)
     apply (fastforce simp: get_etcb_rev)
  apply (clarsimp simp: assert_opt_def has_slots_def
    transform_tcb_def object_slots_def update_slots_def tcb_slots)
  apply (clarsimp simp: corres_underlying_def in_monad
    set_object_def KHeap_D.set_object_def get_object_def simpler_modify_def)
  apply (simp add: transform_def transform_current_thread_def)
  apply (rule ext)
  apply (subst transform_objects_update_kheap_same_caps)
     apply ((simp add: obj_at_def transform_tcb_def
       not_generates_pending_is_null tcb_slots)+)[3]
  apply (auto simp: obj_at_def not_generates_pending_is_null transform_tcb_def tcb_slots)
  done

lemma set_bound_notification_corres:
  "dcorres dc \<top> (not_idle_thread y and valid_etcbs and K (cap = infer_tcb_bound_notification ntfn_opt))
    (KHeap_D.set_cap (y, tcb_boundntfn_slot) cap)
    (KHeap_A.set_bound_notification y ntfn_opt)"
  apply (simp add:set_bound_notification_def)
  apply (rule dcorres_absorb_gets_the)
  apply (rule corres_guard_imp)
   apply (rule set_boundntfn_cap_corres)
   apply simp
  apply (clarsimp dest!: get_tcb_SomeD simp: obj_at_def)
  done

lemma dcorres_unbind_notification:
  "dcorres dc \<top> (valid_etcbs and not_idle_thread t) (PageTableUnmap_D.unbind_notification t) (IpcCancel_A.unbind_notification t)"
  apply (simp add: PageTableUnmap_D.unbind_notification_def IpcCancel_A.unbind_notification_def
                   get_bound_notification_def thread_get_def)
  apply (rule dcorres_gets_the)
   apply (clarsimp simp: opt_object_tcb transform_tcb_def not_idle_thread_def)
   apply (frule (1) valid_etcbs_get_tcb_get_etcb)
   apply (clarsimp simp: opt_cap_tcb tcb_slots infer_tcb_bound_notification_def split: option.splits)
   apply (clarsimp simp: get_simple_ko_def get_object_def gets_def bind_assoc)
   apply (rule dcorres_absorb_get_r)
   apply (clarsimp simp: assert_def corres_free_fail partial_inv_def a_type_def
                  split: Structures_A.kernel_object.splits, safe)
   apply (rule corres_dummy_return_pl[where b="()"])
   apply (rule corres_split_forwards'[where r'=dc and Q="\<lambda>_. \<top>", OF _ _ set_ntfn_exec_wp])
     apply (rule corres_dummy_set_notification[THEN corres_guard_imp],simp+)
   apply (rule corres_guard_imp)
     apply (rule set_bound_notification_corres[where ntfn_opt=None, unfolded infer_tcb_bound_notification_def
                                      not_idle_thread_def tcb_slots, simplified])
    apply simp
   apply (clarsimp simp: valid_etcbs_def pred_tcb_at_def obj_at_def is_etcb_at_def)[1]
   apply (rule ccontr, clarsimp)
   apply (drule ekheap_tcb_at)
    apply ((clarsimp simp: valid_etcbs_def pred_tcb_at_def obj_at_def is_etcb_at_def is_tcb)+)[2]
  apply (clarsimp simp: not_idle_thread_def)
  apply (frule (1) valid_etcbs_get_tcb_get_etcb, clarsimp)
  apply (clarsimp simp: opt_cap_tcb)
  done

lemma dcorres_ntfn_bound_tcb:
  "dcorres (\<lambda>rv rv'. rv = set_option (ntfn_bound_tcb rv'))  \<top> (valid_state and valid_etcbs)
     (gets $ get_bound_notification_threads ntfn)
     (get_notification ntfn)"
    apply (clarsimp simp: gets_def get_simple_ko_def
                  get_object_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: assert_def corres_free_fail a_type_def partial_inv_def
                 split: Structures_A.kernel_object.splits, rule conjI, clarsimp+)
  apply (frule get_notification_pick, simp)
  apply (clarsimp simp: valid_ntfn_abstract_def ntfn_bound_set_lift valid_state_def option_select_def split del: if_split)
  done

lemma option_set_option_select:
  "option_select (set_option x) = return x"
  by (auto simp: option_select_def)

(* FIXME!!! *)
definition set_to_option
where
  "set_to_option x \<equiv> if x = {} then None else (if \<exists>y. x = {y} then Some (the_elem x) else undefined)"

lemma set_to_option_Option_set:
  "set_to_option (set_option x) = x"
  by (auto simp: set_to_option_def)

lemma dcorres_do_unbind_notification:
  "dcorres dc \<top> (valid_etcbs and valid_state and not_idle_thread t) (PageTableUnmap_D.do_unbind_notification t) (IpcCancel_A.do_unbind_notification ntfnptr ntfn t)"
  apply (clarsimp)
  apply (rule corres_guard_imp)
    apply (rule corres_dummy_return_pl[where b="()"])
    apply (rule corres_split[OF corres_dummy_set_notification])
      apply (clarsimp simp: tcb_slots)
      apply (rule set_bound_notification_corres[where ntfn_opt=None, unfolded infer_tcb_bound_notification_def
                                       not_idle_thread_def tcb_slots, simplified])
     apply wp+
   apply simp
  apply (clarsimp simp: not_idle_thread_def)
  done

lemma dcorres_unbind_maybe_notification:
  "dcorres dc \<top> (valid_etcbs and valid_idle and valid_state)
   (PageTableUnmap_D.unbind_maybe_notification ntfn)
   (unbind_maybe_notification ntfn)"
  apply (simp add: PageTableUnmap_D.unbind_maybe_notification_def IpcCancel_A.unbind_maybe_notification_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF dcorres_ntfn_bound_tcb, unfolded  fun_app_def, simplified])
      apply (simp add: option_set_option_select)
      apply (rule_tac P'="case (ntfn_bound_tcb ntfna) of None \<Rightarrow> R' | Some x \<Rightarrow> R''" for R' R'' in corres_inst)
      apply (rule_tac P="case (set_to_option (set_option (ntfn_bound_tcb ntfna))) of None \<Rightarrow> R | Some x \<Rightarrow> R'''" for R R''' in corres_inst)
      (* apply (rule_tac P'="?R' (ntfn_bound_tcb ntfn_obj)" and P="?R (ntfn_bound_tcb ntfn_obj)" in corres_inst) *)
      apply (simp add: set_to_option_Option_set)
      apply (rule_tac v="ntfn_bound_tcb ntfna" and v'="ntfn_bound_tcb ntfna" in corres_option_split)
        apply simp
       apply (rule corres_trivial)
       apply simp
      apply (rule_tac P'="R' (the (ntfn_bound_tcb ntfna)) ntfna" for R' in corres_inst)
      apply simp
      apply (rule dcorres_do_unbind_notification[unfolded dc_def, simplified])
     apply (wp get_simple_ko_wp)+
   apply (clarsimp split: option.splits)
  apply (clarsimp simp: valid_state_def valid_pspace_def split: option.splits)
  apply (simp add: obj_at_def)
  apply (frule (3) ntfn_bound_tcb_at[where P="\<lambda>a. a = Some ntfn"], simp)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def not_idle_thread_def obj_at_def)
  done


lemma unbind_notification_valid_state[wp]:
  "\<lbrace>valid_state\<rbrace> IpcCancel_A.unbind_notification t \<lbrace>\<lambda>rv. valid_state\<rbrace>"
  supply if_cong[cong]
  apply (simp add: unbind_notification_def valid_state_def valid_pspace_def)
  apply (rule bind_wp [OF _ gbn_sp])
  apply (case_tac ntfnptr, clarsimp, wp, simp)
  apply clarsimp
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (wp valid_irq_node_typ set_simple_ko_valid_objs
       | clarsimp split del: if_split)+
  apply (intro conjI impI;
    (match conclusion in "sym_refs r" for r \<Rightarrow> \<open>-\<close>
      | auto elim!: obj_at_weakenE obj_at_valid_objsE if_live_then_nonz_capD2
                       simp: valid_ntfn_set_bound_None is_ntfn valid_obj_def
                             live_def hyp_live_def a_type_def))
  apply (clarsimp simp: if_split)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def is_tcb
                   dest!: pred_tcb_at_tcb_at ko_at_state_refs_ofD
                   split: if_split_asm)
  apply (clarsimp split: if_split_asm)
   apply (frule pred_tcb_at_tcb_at)
   apply (frule_tac p=t in obj_at_ko_at, clarsimp)
   apply (subst (asm) ko_at_state_refs_ofD, assumption)
   apply (fastforce simp: obj_at_def is_tcb ntfn_q_refs_no_NTFNBound tcb_at_no_ntfn_bound refs_of_rev
                          tcb_ntfn_is_bound_def
                   dest!: pred_tcb_at_tcb_at bound_tcb_at_state_refs_ofD)
  apply (subst (asm) ko_at_state_refs_ofD, assumption)
  apply (fastforce simp: ntfn_bound_refs_def obj_at_def ntfn_q_refs_no_TCBBound
                  elim!: pred_tcb_weakenE
                  dest!: bound_tcb_bound_notification_at refs_in_ntfn_bound_refs symreftype_inverse'
                  split: option.splits)
  done

lemma unbind_maybe_notification_valid_state[wp]:
  "\<lbrace>valid_state\<rbrace> IpcCancel_A.unbind_maybe_notification a \<lbrace>\<lambda>rv. valid_state\<rbrace>"
  supply if_cong[cong]
  apply (simp add: unbind_maybe_notification_def valid_state_def valid_pspace_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_bound_tcb ntfn", clarsimp, wp, simp+)
  apply (wp valid_irq_node_typ set_simple_ko_valid_objs
       | clarsimp split del: if_split)+
  apply (intro conjI impI;
    (match conclusion in "sym_refs r" for r \<Rightarrow> \<open>-\<close>
      | auto elim!: obj_at_weakenE obj_at_valid_objsE if_live_then_nonz_capD2
                       simp: valid_ntfn_set_bound_None is_ntfn valid_obj_def
                             live_def hyp_live_def a_type_def))
  apply (clarsimp simp: if_split)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def
                   dest!: pred_tcb_at_tcb_at ko_at_state_refs_ofD
                   split: if_split_asm)
  apply (clarsimp split: if_split_asm)
   apply (clarsimp simp: obj_at_def)
   apply (frule_tac P="(=) (Some a)" in ntfn_bound_tcb_at, simp+)
   apply (frule pred_tcb_at_tcb_at)
   apply (frule_tac p=aa in obj_at_ko_at, clarsimp)
   apply (subst (asm) ko_at_state_refs_ofD, assumption)
   apply (fastforce simp: obj_at_def is_tcb ntfn_q_refs_no_NTFNBound tcb_at_no_ntfn_bound refs_of_rev
                          tcb_ntfn_is_bound_def
                   dest!: pred_tcb_at_tcb_at bound_tcb_at_state_refs_ofD)
  apply (subst (asm) ko_at_state_refs_ofD, assumption)
  apply (fastforce simp: ntfn_bound_refs_def obj_at_def ntfn_q_refs_no_TCBBound
                  elim!: pred_tcb_weakenE
                  dest!: bound_tcb_bound_notification_at refs_in_ntfn_bound_refs symreftype_inverse'
                  split: option.splits)
  done

lemma unbind_notification_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> IpcCancel_A.unbind_notification t \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: unbind_notification_def)
  apply (rule bind_wp[OF _ gbn_sp])
  apply (case_tac ntfnptr, clarsimp, wp, simp)
  apply clarsimp
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (wp | clarsimp)+
  apply (auto simp: obj_at_def is_ntfn_def)
  done

lemma unbind_maybe_notification_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> IpcCancel_A.unbind_maybe_notification a \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: unbind_maybe_notification_def)
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_bound_tcb ntfn", clarsimp, wp, simp)
  apply clarsimp
  apply (wp | clarsimp)+
  apply (auto simp: obj_at_def is_ntfn_def)
  done

lemma fast_finalise_corres:
  "dcorres dc \<top> (valid_state and valid_idle and valid_etcbs) (PageTableUnmap_D.fast_finalise (transform_cap rv') final)
   (IpcCancel_A.fast_finalise rv' final)"
  apply (case_tac rv')
  apply (simp_all add:transform_cap_def)
           apply (simp_all add:PageTableUnmap_D.fast_finalise_def corres_free_fail)
   apply (simp_all add:when_def)
   apply (clarsimp simp:dcorres_cancel_all_ipc)
apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule dcorres_unbind_maybe_notification)
      apply (rule dcorres_cancel_all_signals)
     apply (wp unbind_notification_valid_etcbs unbind_maybe_notification_valid_etcbs | simp add:  | wpc)+
  done

lemma cdl_cdt_transform:
  "cdl_cdt (transform s) = transform_cdt s"
  by (simp add:transform_def)

lemma set_parent_corres:
  "\<lbrakk>slot = transform_cslot_ptr slot';pslot = transform_cslot_ptr pslot'\<rbrakk>
    \<Longrightarrow>dcorres dc \<top> ((cte_wp_at ((\<noteq>)cap.NullCap) slot') and
             weak_valid_mdb and (cte_wp_at ((\<noteq>)cap.NullCap) pslot')
             and (\<lambda>s. cdt s slot' = None))
             (set_parent slot pslot)
             (update_cdt (\<lambda>cdt a. if a = slot' then Some pslot' else cdt a))"
  supply if_cong[cong]
  apply (clarsimp simp:set_parent_def update_cdt_def gets_def)
  apply (rule dcorres_absorb_get_l)
  apply (rule dcorres_absorb_get_r)
  apply clarsimp
  apply (frule transform_cdt_none[OF cte_wp_at_weakenE])
     apply simp
    apply (simp add:weak_valid_mdb_def)
   apply simp
  apply (clarsimp simp:corres_underlying_def cdl_cdt_transform
    fail_def assert_def simpler_modify_def put_def gets_def
    get_def set_cdt_def return_def bind_def)
  apply (simp add:transform_current_thread_def weak_valid_mdb_def)
  apply (rename_tac s')
  apply (subgoal_tac "transform s'\<lparr>cdl_cdt:=(cdl_cdt(transform s'))
    (transform_cslot_ptr slot' \<mapsto> transform_cslot_ptr pslot')\<rparr>
    = cdl_cdt_single_update (transform s') (transform_cslot_ptr slot') (transform_cslot_ptr pslot')")
   apply (clarsimp simp:cdl_cdt_transform)
   apply (subgoal_tac "s'\<lparr>cdt := \<lambda>a. if a = slot' then Some pslot' else cdt s' a\<rparr> = abs_cdt_single_update s' slot' pslot'")
    apply simp
    apply (rule sym, rule transform_cdt_single_update_helper,simp)
    apply (rule cdt_single_update_eq,simp)
     apply (clarsimp simp:cte_wp_at_cte_at)+
   apply (clarsimp simp:abs_cdt_single_update_def)
  apply (clarsimp simp:cdl_cdt_single_update_def cdl_cdt_transform)
  apply (case_tac "transform s'")
  apply (clarsimp simp:cdl_cdt_transform)
  apply (rule ext)
  apply (clarsimp split:if_splits)
  done

lemma set_tcb_capslot_weak_valid_mdb:
  "\<lbrace>weak_valid_mdb and cte_wp_at ((=) cap.NullCap) slot\<rbrace> set_cap cap slot \<lbrace>\<lambda>r s. weak_valid_mdb s\<rbrace> "
  apply (simp add: weak_valid_mdb_def cte_wp_at_caps_of_state swp_def)
  apply (wp set_cap_caps_of_state2)
  apply (case_tac slot)
  apply (clarsimp simp: valid_def set_cap_def cte_wp_at_caps_of_state weak_valid_mdb_def swp_def)
  apply (simp only: mdb_cte_at_def)
  apply fastforce
  done

lemma get_tcb_reply_cap_wp_cte_at:
    "\<lbrace>tcb_at sid and valid_objs and cte_wp_at ((\<noteq>) cap.NullCap) (sid, tcb_cnode_index 2)\<rbrace> CSpaceAcc_A.get_cap (sid, tcb_cnode_index 2)
    \<lbrace>\<lambda>rv. cte_wp_at ((\<noteq>) cap.NullCap) (obj_ref_of rv, tcb_cnode_index 2)\<rbrace>"
  apply (rule hoare_post_imp
     [where Q="\<lambda>r. cte_wp_at (\<lambda>c. r \<noteq> cap.NullCap) (sid,tcb_cnode_index 2)
       and tcb_at sid and valid_objs and cte_wp_at ((=) r) (sid,tcb_cnode_index 2)"])
   apply clarsimp
   apply (frule cte_wp_tcb_cap_valid)
    apply simp+
   apply (clarsimp simp :cte_wp_at_def tcb_cap_valid_def st_tcb_at_def obj_at_def is_master_reply_cap_def split:cap.splits)
  apply (wp get_cap_cte_wp_at_rv)
  apply (clarsimp simp:cte_wp_at_def)
  done

lemma get_tcb_reply_cap_wp_master_cap:
  "\<lbrace>tcb_at sid and valid_objs and cte_wp_at ((\<noteq>) cap.NullCap) (sid,tcb_cnode_index 2) \<rbrace> CSpaceAcc_A.get_cap (sid, tcb_cnode_index 2)
    \<lbrace>\<lambda>rv s. (is_master_reply_cap rv)  \<rbrace>"
  apply (rule hoare_post_imp
     [where Q="\<lambda>r. cte_wp_at (\<lambda>c. r \<noteq> cap.NullCap) (sid,tcb_cnode_index 2)
       and tcb_at sid and valid_objs and cte_wp_at ((=) r) (sid,tcb_cnode_index 2)"])
   apply clarsimp
   apply (frule cte_wp_tcb_cap_valid)
    apply simp+
   apply (clarsimp simp :cte_wp_at_def tcb_cap_valid_def st_tcb_at_def obj_at_def is_master_reply_cap_def split:cap.splits)
  apply (wp get_cap_cte_wp_at_rv)
  apply (clarsimp simp:cte_wp_at_def)+
  done

lemma get_tcb_reply_cap_wp_original_cap:
    "\<lbrace>tcb_at sid and valid_objs and cte_wp_at ((\<noteq>) cap.NullCap) (sid,tcb_cnode_index 2) and valid_mdb \<rbrace> CSpaceAcc_A.get_cap (sid, tcb_cnode_index 2)
    \<lbrace>\<lambda>rv s. is_original_cap s (obj_ref_of rv, tcb_cnode_index 2)\<rbrace>"
  apply (rule hoare_post_imp
     [where Q="\<lambda>r. cte_wp_at (\<lambda>c. r \<noteq> cap.NullCap) (sid,tcb_cnode_index 2) and valid_mdb
       and tcb_at sid and valid_objs and cte_wp_at ((=) r) (sid,tcb_cnode_index 2)"])
   apply (rename_tac rv s)
   apply clarsimp
   apply (subgoal_tac "is_master_reply_cap rv \<and> obj_ref_of rv = sid")
    apply clarsimp
    apply (frule cte_wp_tcb_cap_valid)
     apply simp+
    apply (clarsimp simp:valid_mdb_def reply_master_revocable_def)
    apply (drule_tac x = "obj_ref_of rv" in spec)
    apply (drule_tac x = "tcb_cnode_index 2" in spec)
    apply (drule_tac x = rv in spec)
    apply (drule iffD1[OF cte_wp_at_caps_of_state])+
    apply clarsimp
   apply (frule cte_wp_tcb_cap_valid)
    apply (clarsimp simp :cte_wp_at_def tcb_cap_valid_def st_tcb_at_def obj_at_def is_master_reply_cap_def split:cap.splits)+
  apply (wp get_cap_cte_wp_at_rv)
  apply (clarsimp simp:cte_wp_at_def)+
  done

lemma get_tcb_reply_cap_wp_obj_ref:
    "\<lbrace>tcb_at sid and valid_objs and cte_wp_at ((\<noteq>) cap.NullCap) (sid,tcb_cnode_index 2) \<rbrace> CSpaceAcc_A.get_cap (sid, tcb_cnode_index 2)
    \<lbrace>\<lambda>rv s. (obj_ref_of rv = sid) \<rbrace>"
  apply (rule hoare_post_imp
     [where Q="\<lambda>r. cte_wp_at (\<lambda>c. r \<noteq> cap.NullCap) (sid,tcb_cnode_index 2)
       and tcb_at sid and valid_objs and cte_wp_at ((=) r) (sid,tcb_cnode_index 2)"])
   apply clarsimp
   apply (frule cte_wp_tcb_cap_valid)
    apply simp+
   apply (clarsimp simp :cte_wp_at_def tcb_cap_valid_def st_tcb_at_def obj_at_def is_master_reply_cap_def split:cap.splits)
  apply (wp get_cap_cte_wp_at_rv)
  apply (clarsimp simp:cte_wp_at_def)+
  done

lemma tcb_reply_cap_cte_wp_at:
  "\<lbrakk>valid_objs s;st_tcb_at (\<lambda>r. \<not> inactive r \<and> \<not> idle r) sid s\<rbrakk>
     \<Longrightarrow> cte_wp_at ((\<noteq>) cap.NullCap) (sid, tcb_cnode_index 2) s"
  apply (clarsimp simp:valid_objs_def)
  apply (drule_tac x = sid in bspec)
    apply (clarsimp simp:st_tcb_at_def obj_at_def)
  apply (clarsimp simp:cte_wp_at_cases st_tcb_at_def obj_at_def valid_obj_def valid_tcb_def)
  apply (clarsimp simp:tcb_cap_cases_def split:Structures_A.thread_state.splits)
done

lemma transform_objects_update_kheap_simp:
  "\<lbrakk>kheap s ptr = Some ko; ekheap s ptr = opt_etcb\<rbrakk>
    \<Longrightarrow> transform_objects (update_kheap ((kheap s)(ptr \<mapsto> obj)) s) =
    (\<lambda>x. if x \<noteq> ptr then transform_objects s x else
    (if ptr = idle_thread s then None else
           Some (transform_object (machine_state s) ptr opt_etcb obj)))"
  apply (rule ext)
  apply (clarsimp split:if_splits)
  apply (case_tac "x = ptr")
   apply (clarsimp simp: map_add_def transform_objects_def)
  apply (simp add:restrict_map_def map_add_def transform_objects_def)
  done

lemma set_cap_is_noop_opt_cap:
   "opt_cap ptr s = Some cap \<Longrightarrow> KHeap_D.set_cap ptr cap s = return () s"
  apply (clarsimp simp: opt_cap_def slots_of_def split_def
                 split: option.split_asm)
  apply (simp add: KHeap_D.set_cap_def split_def exec_gets gets_the_def
                   bind_assoc assert_opt_def has_slots_def
                   KHeap_D.set_object_def)
  apply (simp add: object_slots_def update_slots_def fun_upd_idem
            split: cdl_object.split_asm)
  apply (simp_all add: simpler_modify_def
                       return_def fun_upd_idem)
  done

lemma opt_cap_objects_cong:
  "cdl_objects s = cdl_objects s' \<Longrightarrow> opt_cap slot s = opt_cap slot s'"
  apply (cases slot)
  apply (clarsimp simp: opt_cap_def slots_of_def)
  done

lemma always_empty_slot_NullCap_corres:
  "dcorres dc \<top>
           (weak_valid_mdb and not_idle_thread (fst slot) and
            cte_wp_at ((=) cap.NullCap) slot and valid_etcbs)
           (do y \<leftarrow> remove_parent (transform_cslot_ptr slot);
               KHeap_D.set_cap (transform_cslot_ptr slot) cdl_cap.NullCap
            od)
           (return ())"
  supply if_cong[cong]
  apply (simp add: remove_parent_def)
  apply (clarsimp simp: corres_underlying_def in_monad simpler_modify_def bind_def)
  apply (subst set_cap_is_noop_opt_cap)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (drule caps_of_state_transform_opt_cap)
    apply clarsimp
    apply (clarsimp simp: not_idle_thread_def)
   apply (clarsimp cong: opt_cap_objects_cong)
  apply (clarsimp simp: return_def transform_def)
  apply (rule ext)
  apply clarsimp
  apply (subgoal_tac "transform_cdt b (transform_cslot_ptr slot) = None")
   prefer 2
   apply (rule transform_cdt_none)
     apply (erule cte_wp_at_weakenE, rule TrueI)
    apply (simp add: weak_valid_mdb_def)
   apply (clarsimp simp: weak_valid_mdb_def mdb_cte_at_def)
   apply (rule classical)
   apply (cases slot)
   apply clarsimp
   apply (erule allE)+
   apply (erule (1) impE)
   apply (clarsimp simp: cte_wp_at_def)
  apply (cases slot)
  apply clarsimp
  apply (subgoal_tac "\<exists>p. (a,ba) = transform_cslot_ptr p")
   apply clarsimp
   apply (drule transform_cdt_some_rev)
     apply (erule cte_wp_at_weakenE, rule TrueI)
    apply (simp add: weak_valid_mdb_def)
   apply (clarsimp simp: weak_valid_mdb_def mdb_cte_at_def)
   apply (erule allE)+
   apply (erule (1) impE)
   apply (clarsimp simp: cte_wp_at_def)
  apply (clarsimp simp: transform_cslot_ptr_def)
  apply (rule nat_bl_to_bin_surj)
  done

lemma always_empty_slot_corres:
  "dcorres dc \<top> (weak_valid_mdb and valid_idle and not_idle_thread (fst slot) and valid_etcbs)
   (always_empty_slot (transform_cslot_ptr slot)) (IpcCancel_A.empty_slot slot cap.NullCap)"
  apply (clarsimp simp: always_empty_slot_def IpcCancel_A.empty_slot_def)
  apply (rule corres_symb_exec_r)
     apply (rule corres_guard_imp)
       apply (rule_tac R="cap = cap.NullCap" in corres_cases)
        apply simp
        apply (rule always_empty_slot_NullCap_corres)
       apply simp
       apply (rule dcorres_gets_all_param)
       apply (rule_tac P="%a. dcorres dc P P' h a" for P P' h in subst[OF bind_assoc[where m="gets cdt"]])
       apply (rule corres_split[where r'="dc"])
          apply (rule remove_parent_corres)
         apply (rule dcorres_rhs_noop_above[OF empty_slot_ext_dcorres])
           apply (rule corres_bind_ignore_ret_rhs)
           apply (rule set_cap_null_cap_corres)
          apply wp+
      apply (wp get_cap_wp|simp add: set_cdt_def)+
    apply (clarsimp simp: cte_wp_at_def not_idle_thread_def)
   apply (wp get_cap_wp)
   apply simp
  apply simp
  done

lemma delete_cap_simple_corres:
  "dcorres dc \<top> (invs and (not_idle_thread (fst slot)) and valid_etcbs)
             (delete_cap_simple (transform_cslot_ptr slot)) (cap_delete_one slot)"
  apply (clarsimp simp:delete_cap_simple_def cap_delete_one_def)
  apply (rule get_cap_no_fail)
  apply (rule corres_guard_imp)
    apply (rule_tac r'="%r r'. r = transform_cap r'" in corres_split)
       apply (rule get_cap_corres)
       apply simp
      apply (case_tac "rv' = cap.NullCap")
       apply (subgoal_tac "rv = cdl_cap.NullCap")
        apply (clarsimp simp:transform_cap_def unless_def when_def)
       apply (clarsimp simp:transform_cap_def)
      apply (subgoal_tac "rv\<noteq>cdl_cap.NullCap")
       apply (clarsimp simp:unless_def when_def)
       apply(rule corres_split[where r'="%x y. x=y"])
          apply (subst is_final_cap_corres; simp)
         apply (rule corres_split[where r'="dc"])
            apply simp
            apply (rule fast_finalise_corres)
           apply (rule always_empty_slot_corres)
          apply simp
         apply wp
         apply (rule hoare_post_imp [where Q="\<lambda>r. valid_mdb and valid_idle
                      and  not_idle_thread (fst slot) and valid_etcbs"])
          apply (simp add:valid_mdb_def weak_valid_mdb_def)
         apply wp
        apply (wp|clarsimp)+
      apply (clarsimp simp:transform_cap_def split:cap.splits arch_cap.splits if_split_asm)
     apply (clarsimp simp:not_idle_thread_def |wp get_cap_cte_wp_at_rv)+
  apply (simp add:invs_def valid_state_def valid_pspace_def)+
  done

lemma cap_delete_one_valid_mdb[wp]:
  "\<lbrace>invs and emptyable slot\<rbrace> cap_delete_one slot \<lbrace>\<lambda>yc. valid_mdb\<rbrace>"
  apply (rule hoare_post_imp [where Q="%x. invs"])
   apply (simp add:invs_def valid_state_def valid_pspace_def)
  apply (rule delete_one_invs)
  done

lemma thread_get_corres:
  "\<lbrakk>did = thread; dcorres rv \<top> P' (f tcb) (g (t tcb')) \<rbrakk>
  \<Longrightarrow> dcorres rv \<top> (P' and not_idle_thread thread and valid_irq_node
    and (\<lambda>s. transform_tcb (machine_state s) thread tcb' etcb' = Tcb tcb) and ko_at (TCB tcb') thread
    and (\<lambda>s. get_etcb thread s = Some etcb'))
    (get_thread did >>= f) (thread_get t thread >>= g)"
  apply (clarsimp simp:get_thread_def thread_get_def bind_assoc)
  apply (rule dcorres_gets_the)
   apply (clarsimp dest!:get_tcb_SomeD get_etcb_SomeD simp:obj_at_def opt_object_tcb is_etcb_at_def)
   apply (clarsimp dest!:get_tcb_rev get_etcb_rev)
   apply (frule opt_object_tcb)
     apply (simp add:not_idle_thread_def)+
   apply (case_tac obj)
            apply ((simp add:transform_tcb_def)+)[2]
          apply clarsimp
          apply (rule dcorres_absorb_pfx)
             apply (assumption)
            apply simp+
  apply (clarsimp simp:obj_at_def dest!:get_tcb_rev)
  apply (drule opt_object_tcb)
    apply (simp add:not_idle_thread_def get_etcb_def)+
done

lemma thread_get_corresE:
  "\<lbrakk>did = thread; dcorres rv \<top> P' (f tcb) (g (t tcb')) \<rbrakk>
  \<Longrightarrow> dcorres rv \<top>
    (P' and not_idle_thread thread and valid_irq_node and (\<lambda>s. transform_tcb (machine_state s) thread tcb' etcb' = Tcb tcb)
     and ko_at (TCB tcb') thread
     and (\<lambda>s. get_etcb thread s = Some etcb'))
    (liftE (get_thread did) >>=E f) (liftE(thread_get t thread) >>=E g)"
  apply (simp add:liftE_def bindE_def lift_def)
  apply (rule thread_get_corres)
   apply simp+
  done

definition in_terminate_branch :: "bool list \<Rightarrow> cap \<Rightarrow> bool"
  where "in_terminate_branch ref cap \<equiv> case cap of
  cap.CNodeCap oref radix_bits guard \<Rightarrow>
    (0 < radix_bits \<or> guard \<noteq> [])\<and>(length ref = radix_bits + length guard)\<and>(guard \<le> ref)
  | _ \<Rightarrow> False"

definition in_recursive_branch :: "bool list \<Rightarrow> cap \<Rightarrow> bool"
  where "in_recursive_branch ref cap \<equiv> case cap of
  cap.CNodeCap oref radix_bits guard \<Rightarrow>
    (0 < radix_bits \<or> guard \<noteq> [])\<and>(radix_bits + length guard < length ref)\<and>(guard \<le> ref)
  | _ \<Rightarrow> False"

lemma resolve_address_bits_error_branch1:
  " \<not> is_cnode_cap cap \<Longrightarrow> resolve_address_bits (cap,cref) = throwError ExceptionTypes_A.lookup_failure.InvalidRoot"
  unfolding resolve_address_bits_def
  apply (clarsimp simp:is_cap_simps)
  apply (case_tac cap)
             apply (clarsimp simp:CSpace_A.resolve_address_bits'.simps)+
  done

lemma resolve_address_bits_error_branch2:
  "\<lbrakk>0 < radix_bits \<or> guard \<noteq> []; \<not> in_terminate_branch ref cap; \<not> in_recursive_branch ref cap;cap = cap.CNodeCap oref radix_bits guard\<rbrakk>
   \<Longrightarrow> \<exists>excep. CSpace_A.resolve_address_bits (cap,ref) = throwError excep"
  unfolding resolve_address_bits_def
  apply (case_tac cap)
             apply (simp_all add:CSpace_A.resolve_address_bits'.simps in_terminate_branch_def in_recursive_branch_def)
  apply (clarsimp | rule conjI)+
   apply (clarsimp simp:whenE_def | rule conjI)+
     apply auto
  done

lemma resolve_address_bits_terminate_branch:
  "\<lbrakk>in_terminate_branch ref cap; cap = cap.CNodeCap oref radix_bits guard\<rbrakk>
      \<Longrightarrow> CSpace_A.resolve_address_bits (cap,ref) = returnOk ((oref, drop (length guard) ref), [])"
  unfolding resolve_address_bits_def
  by (clarsimp simp: CSpace_A.resolve_address_bits'.simps in_terminate_branch_def)

lemma resolve_address_bits_recursive_branch:
  "\<lbrakk>in_recursive_branch ref cap;cap = cap.CNodeCap oref radix_bits guard\<rbrakk>
   \<Longrightarrow> CSpace_A.resolve_address_bits (cap,ref ) =
         doE next_cap \<leftarrow> liftE (CSpaceAcc_A.get_cap (oref, take radix_bits (drop (length guard) ref)));
             if Structures_A.is_cnode_cap next_cap then CSpace_A.resolve_address_bits (next_cap, drop (radix_bits + length guard) ref)
             else returnOk ((oref, take radix_bits (drop (length guard) ref)), drop (radix_bits + length guard) ref)
         odE"
  unfolding resolve_address_bits_def
  by (clarsimp simp: in_recursive_branch_def CSpace_A.resolve_address_bits'.simps)

lemmas cap_type_simps = cap_type_def[split_simps cdl_cap.split]

lemma is_cnode_cap_transform_cap:
  "Types_D.is_cnode_cap (transform_cap cap) = is_cnode_cap cap"
  apply (case_tac cap)
             apply (simp_all add:transform_cap_def cap_type_simps split:cdl_cap.splits arch_cap.splits)
  done

lemma cdl_resolve_address_bits_error_branch1:
  "\<not> is_cnode_cap cap\<Longrightarrow> CSpace_D.resolve_address_bits (transform_cap cap) cap_ptr remaining_size = Monads_D.throw"
  apply (subst KHeap_DR.resolve_address_bits.simps)
  apply (simp add:unlessE_def is_cnode_cap_transform_cap)
  done

lemma branch_map_simp1:
  "\<lbrakk>length ref \<le> 32;length ref = radix_bits + length guard\<rbrakk> \<Longrightarrow>
  ( (((of_bl ref)::word32) >> radix_bits) && mask (length guard) = (of_bl guard)) = (guard \<le> ref)"
  apply (rule iffI)
   apply (subst(asm) shiftr_bl_of)
    apply simp
   apply (rule_tac cref1=ref and cref'1="of_bl ref::word32" in iffD1[OF guard_mask_shift])
    apply (simp add: word_rep_drop)
   apply (subst shiftr_bl_of)
    apply simp+
  apply (drule_tac cref1=ref and cref'1="of_bl ref::word32" in iffD2[OF guard_mask_shift,rotated])
   apply (simp add: word_rep_drop)+
  done

lemma take_drop:
  "replicate n k @ a = (replicate n k @ (take s a)) @ (drop s a)"
  by auto

lemma branch_map_simp2:
  " \<lbrakk>length cref \<le> 32; 0 < nata;nata + length list < length cref; list \<le> cref\<rbrakk>
  \<Longrightarrow> unat ((((of_bl cref)::word32) >> length cref - (nata + length list)) && mask nata) = nat (bl_to_bin (take nata (drop (length list) cref)))"
  apply (subgoal_tac "take nata (drop (length list) cref) \<le> drop (length list) cref")
   apply (frule_tac iffD2[OF guard_mask_shift,rotated,where cref1="drop (length list) cref" and cref'1="of_bl cref::word32"])
    defer
    apply clarsimp
    apply (subgoal_tac "nata\<le> length cref - length list")
     apply (drule min.absorb2[where b = nata])
     apply simp
     apply (clarsimp simp: add.commute)
     apply (simp only: unat_def)
     apply (rule iffD2[OF eq_nat_nat_iff])
       apply (simp add:bl_to_bin_ge0 )+
     apply (subst bl_to_bin_rep_F[symmetric])
     apply (subst to_bl_bin[symmetric])
     apply (rule arg_cong[where f = bl_to_bin])
     apply (simp add:word_rep_drop)+
   apply (clarsimp simp:List.take_drop prefix_def less_eq_list_def)
   apply (rule_tac x = "(drop nata zs)" in exI)
   apply simp
  apply (simp add:word_rep_drop)
  apply (rule take_drop)
  done


lemma resolve_address_bits_error_corres:
  "\<lbrakk> cap'= transform_cap cap;
     0<radix_bits \<or> guard \<noteq> [];
     \<not>in_terminate_branch ref cap;
     \<not> in_recursive_branch ref cap;
     cap = cap.CNodeCap oref radix_bits guard;
     valid_cap cap s;valid_idle s;length ref \<le> 32;valid_objs s\<rbrakk>
    \<Longrightarrow> dcorres (dc \<oplus> (\<lambda>r r'. (fst r) = transform_cslot_ptr (fst r') \<and> snd r = length (snd r'))) \<top> ((=) s)
    ( CSpace_D.resolve_address_bits (cap') (of_bl ref) (length ref) )
    ( CSpace_A.resolve_address_bits (cap,ref) )"
  apply (subst KHeap_DR.resolve_address_bits.simps)
  apply (frule resolve_address_bits_error_branch2[where 'a=det_ext])
     apply simp+
  apply (clarsimp)
  apply (simp add:transform_cap_def cap_type_simps unlessE_def)
  apply (clarsimp simp: in_terminate_branch_def in_recursive_branch_def | rule conjI)+
   apply (clarsimp simp: assertE_def get_cnode_def bind_assoc liftE_bindE)
   apply (clarsimp simp: valid_cap_def obj_at_def is_cap_table_def)
   apply (clarsimp split:Structures_A.kernel_object.splits)
   apply (rename_tac "fun")
   apply (rule dcorres_expand_pfx)
   apply clarsimp
   apply (rule_tac Q="\<lambda>x y. y = transform s \<and>
                            x = transform_object (machine_state s) oref etcb_opt
                                                 (kernel_object.CNode radix_bits fun) "
                   in corres_symb_exec_l)
      apply (rule dcorres_expand_pfx)
      apply (clarsimp simp:whenE_def branch_map_simp1 split: nat.splits|rule conjI)+
     apply (drule (1) transform_objects_cnode, simp,
            clarsimp simp:transform_objects_cnode gets_the_def gets_def get_def
                          bind_def return_def valid_def exs_valid_def
                          assert_opt_def transform_def
                     split: nat.splits)+
  apply (clarsimp simp: get_cnode_def bind_assoc liftE_bindE)
  apply (clarsimp simp: valid_cap_def obj_at_def is_cap_table_def)
  apply (clarsimp split: Structures_A.kernel_object.splits)
  apply (rule dcorres_expand_pfx)
  apply clarsimp
  apply (rename_tac "fun")
  apply (rule_tac Q="\<lambda>x y. y = (transform s) \<and> x = (transform_object (machine_state s) oref etcb_opt (kernel_object.CNode radix_bits fun))" in corres_symb_exec_l)
     apply (rule dcorres_expand_pfx)
     apply (clarsimp simp:whenE_def branch_map_simp1|rule conjI)+
     apply (drule (1) transform_objects_cnode, simp,
            clarsimp simp: transform_objects_cnode gets_the_def gets_def get_def
                           bind_def return_def valid_def exs_valid_def
                           assert_opt_def transform_def
                     split: nat.splits)+
  done

lemma resolve_address_bits_terminate_corres:
  "\<lbrakk>in_terminate_branch ref cap; cap = cap.CNodeCap oref radix_bits guard; cap'=transform_cap cap; valid_cap cap s;valid_idle s;length ref \<le> 32;valid_objs s\<rbrakk>
      \<Longrightarrow> dcorres (dc \<oplus> (\<lambda>r r'. fst r = transform_cslot_ptr (fst r') \<and> snd r = length (snd r'))) \<top> ((=) s)
    ( CSpace_D.resolve_address_bits cap' (of_bl ref) (length ref) )
    ( CSpace_A.resolve_address_bits (cap,ref) )"
  apply (subst KHeap_DR.resolve_address_bits.simps,frule resolve_address_bits_terminate_branch[where 'a=det_ext],fastforce)
  apply (clarsimp simp:in_terminate_branch_def)
  apply (clarsimp simp:unlessE_def cap_type_simps assertE_def)
  apply (subgoal_tac "(of_bl ref >> radix_bits) && mask (length guard) = of_bl guard")
   apply (clarsimp | rule conjI)+
    apply (clarsimp simp:get_cnode_def bind_assoc liftE_bindE)
    apply (clarsimp simp:valid_cap_def obj_at_def is_cap_table_def)
    apply (clarsimp split:Structures_A.kernel_object.splits)
    apply (rename_tac "fun")
    apply (rule dcorres_expand_pfx)
    apply clarsimp
    apply (rule_tac Q="\<lambda>x y. y = (transform s) \<and> x = (transform_object (machine_state s) oref etcb_opt (kernel_object.CNode radix_bits fun))" in corres_symb_exec_l)
       apply (rule dcorres_expand_pfx)
       apply (simp split: nat.splits)
       apply (clarsimp simp: returnOk_def return_def corres_underlying_def transform_cslot_ptr_def)
       apply (simp only: unat_def)
       apply (subst eq_nat_nat_iff)
         apply (simp add:bl_to_bin_ge0)+
       apply (subst to_bl_bin[symmetric])
       apply (subst bl_and_mask)
       apply (simp add:word_rep_drop bl_to_bin_rep_F)
       apply ((drule (1) transform_objects_cnode;
               clarsimp simp: gets_the_def gets_def get_def bind_def return_def valid_def
                              exs_valid_def assert_opt_def transform_def
                       split: nat.splits)+)[3]
    apply fastforce
   apply (frule_tac cref1=ref and cref'1="of_bl ref::word32" in iffD2[OF guard_mask_shift,rotated])
    apply (simp add: word_rep_drop)+
  done

lemma length_drop:
  "length cref - a = length (drop a cref)"
  by auto

lemma bind_eqI' :"\<lbrakk>a=b;a=b\<Longrightarrow>c=d\<rbrakk>\<Longrightarrow> (a >>= c) = (b >>= d)"
  by simp

lemma cdl_resolve_address_bits_eq:
  "a+t\<le> length cref \<and> length cref \<le> 32\<longrightarrow>
  CSpace_D.resolve_address_bits cap (of_bl cref) t =
  CSpace_D.resolve_address_bits cap (of_bl (drop a cref)) t"
proof (induct t  arbitrary: a cap cref rule: less_induct)
  case (less t)
  show ?case
  apply clarify
  apply (subst KHeap_DR.resolve_address_bits.simps,rule sym)
  apply (subst KHeap_DR.resolve_address_bits.simps)
  apply (subst bindE_def,rule sym,subst bindE_def)
  apply (rule bind_eqI,rule arg_cong[where f="\<lambda>x. lift (K_bind x)"])
  apply (subst bindE_def,rule sym,subst bindE_def,rule bind_eqI,rule arg_cong[where f=lift],rule ext)
  apply (subst bindE_def,rule sym,subst bindE_def,rule bind_eqI,rule arg_cong[where f=lift],rule ext)
  apply (subst bindE_def,rule sym,subst bindE_def,rule bind_eqI,rule arg_cong[where f=lift],rule ext)
  apply (subst bindE_def,rule sym,subst bindE_def,rule bind_eqI,rule arg_cong[where f=lift],rule ext)
  apply (subst bindE_def,rule sym,subst bindE_def)
  apply (rule ext,simp add:returnOk_def lift_def)
    apply (case_tac "\<not> (0<radix_size \<or> 0<guard_size)")
      apply (clarsimp simp:assertE_def)
    apply (clarsimp simp:assertE_def)
    apply (rule_tac x=x in fun_cong)
    apply (subst bindE_def,rule sym,subst bindE_def)
    apply (case_tac "\<not> guard_size \<le> t")
    apply (clarsimp simp:unlessE_def bind_def return_def returnOk_def lift_def)
    apply (rule bind_eqI')
    apply (clarsimp simp:returnOk_def return_def)
      apply (rule ext)
      apply (clarsimp simp:of_bl_drop shiftr_over_and_dist)
      apply (subst shiftr_mask2)
      apply clarsimp
      apply arith
      apply (simp add: mask_twice)
    apply (rule arg_cong[where f=lift],rule ext)
    apply (clarsimp simp:unlessE_def whenE_def return_def)
    apply (subst bindE_def,rule sym,subst bindE_def,rule bind_eqI')
      apply (rule ext)
      apply (clarsimp simp:of_bl_drop shiftr_over_and_dist)
      apply (subst shiftr_mask2)
      apply clarsimp
      apply arith
      apply (simp add:return_def mask_twice)
    apply (rule arg_cong[where f=lift],rule ext)
    apply (subst bindE_def,rule sym,subst bindE_def,rule bind_eqI')
      apply clarsimp
    apply (rule arg_cong[where f=lift],rule ext)
    apply (subst bindE_def,rule sym,subst bindE_def)
    apply (rule ext,clarsimp simp:bind_def lift_def)
    apply (rule_tac x = x in fun_cong)
    apply (subst bindE_def,rule sym,subst bindE_def,rule bind_eqI,rule arg_cong[where f=lift],rule ext)+
    apply (clarsimp split:if_splits)
    apply (rule "less.hyps"[rule_format])
    apply fastforce+
  done
qed

lemma nat_case_split:
  "0 < n \<Longrightarrow> (case n of 0 \<Rightarrow> a | Suc nat' \<Rightarrow> f nat') = f (n - 1)"
  "0 < n \<Longrightarrow> (case (case n of 0 \<Rightarrow> a' | Suc sz' \<Rightarrow> cdl_object.CNode (f' sz')) of
                 cdl_object.CNode x \<Rightarrow> return x
               | _ \<Rightarrow> fail) = return  (f' (n - 1))"
  by (auto split: nat.splits)

lemma resolve_address_bits_corres':
shows "\<lbrakk>length cref \<le> n ; length cref \<le> 32; cap = transform_cap cap'; wlen = length cref\<rbrakk> \<Longrightarrow>
  dcorres (dc \<oplus> (\<lambda>x y. fst x = transform_cslot_ptr (fst y) \<and> snd x = length (snd y)))
   \<top>
   (valid_objs and valid_cap cap' and valid_global_refs and valid_idle and valid_etcbs)
  (CSpace_D.resolve_address_bits cap (of_bl cref) wlen)
  (CSpace_A.resolve_address_bits (cap', cref) :: ((cslot_ptr * cap_ref),det_ext) lf_monad)"
  apply (subgoal_tac "length cref \<le> n \<and> (length cref \<le> 32) \<and> cap = transform_cap cap' \<longrightarrow>
    dcorres (dc\<oplus>(\<lambda>x y. fst x = transform_cslot_ptr (fst y) \<and> snd x = length (snd y)))
    \<top> (valid_objs and valid_cap cap' and valid_global_refs and valid_idle and valid_etcbs)
    (CSpace_D.resolve_address_bits cap (of_bl cref) (length cref)) (resolve_address_bits (cap', cref) :: ((cslot_ptr * cap_ref),det_ext) lf_monad)")
  apply clarsimp
  apply (thin_tac "P" for P)+
proof (induct n arbitrary: cref cap' cap)
  case 0
  show ?case
    apply clarify
    apply (case_tac "\<not> is_cnode_cap cap'")
     apply (subst cdl_resolve_address_bits_error_branch1,simp)
     apply (subst resolve_address_bits_error_branch1,simp)
     apply simp
    apply (rule dcorres_expand_pfx)
    apply (clarsimp simp:gets_the_def gets_def valid_cap_def obj_at_def split:Structures_A.kernel_object.splits cap.splits)
    apply (clarsimp simp:dc_def[symmetric] is_cap_table_def split:Structures_A.kernel_object.splits cap.splits)
    apply (rename_tac word nat list "fun")
    apply (rule corres_guard_imp)
      apply (rule_tac radix_bits = nat and guard = list and s = s' in resolve_address_bits_error_corres[where ref="[]",simplified])
             apply ((simp add:transform_cap_def in_terminate_branch_def in_recursive_branch_def valid_cap_def obj_at_def is_cap_table_def)+)[10]
    done
next
  case (Suc m)
  show ?case
  supply if_cong[cong]
  apply clarify
  apply (case_tac "\<not> is_cnode_cap cap'")
   apply (subst cdl_resolve_address_bits_error_branch1,simp)
   apply (subst resolve_address_bits_error_branch1,simp)
   apply simp
  apply (clarsimp simp:dc_def[symmetric])
  apply (rule dcorres_expand_pfx)
  apply (case_tac "in_terminate_branch cref cap'")
   apply (clarsimp simp:gets_the_def gets_def valid_cap_def obj_at_def split:Structures_A.kernel_object.splits cap.splits)
   apply (clarsimp simp:dc_def[symmetric] is_cap_table_def split:Structures_A.kernel_object.splits cap.splits)
   apply (rule corres_guard_imp)
     apply (rule_tac s=s' in resolve_address_bits_terminate_corres)
           apply (simp_all |rule conjI)+
   apply (clarsimp simp:valid_cap_def obj_at_def is_cap_table_def)
  apply (case_tac "\<not> in_recursive_branch cref cap'")
   apply (clarsimp simp:gets_the_def gets_def valid_cap_def obj_at_def split:Structures_A.kernel_object.splits cap.splits)
   apply (clarsimp simp:dc_def[symmetric] is_cap_table_def split:Structures_A.kernel_object.splits cap.splits)
   apply (rename_tac word nat list "fun")
   apply (rule corres_guard_imp)
     apply (rule_tac s=s' and radix_bits = nat and guard = list in resolve_address_bits_error_corres)
             apply (simp_all | rule conjI)+
   apply (clarsimp simp:valid_cap_def obj_at_def is_cap_table_def)
  apply (clarsimp simp:gets_the_def gets_def valid_cap_def obj_at_def split:Structures_A.kernel_object.splits cap.splits)
  apply (clarsimp simp:dc_def[symmetric] is_cap_table_def split:Structures_A.kernel_object.splits cap.splits)
  apply (subst KHeap_DR.resolve_address_bits.simps,subst resolve_address_bits_recursive_branch)
    apply (clarsimp simp:cap_type_simps is_cap_simps)+
   apply fastforce
  apply (rename_tac word nat list "fun")
  apply (simp add:cap_type_simps)
  apply (simp add:in_recursive_branch_def in_terminate_branch_def unlessE_def branch_map_simp1)
  apply (clarsimp simp:get_cnode_def bind_assoc liftE_bindE)
  apply (rule dcorres_expand_pfx)
  apply clarsimp
  apply (rule_tac Q="\<lambda>x y. y = (transform s'a) \<and> x = (transform_object (machine_state s'a) word etcb_opt (kernel_object.CNode nat fun))" in corres_symb_exec_l)
     apply (rule dcorres_expand_pfx)
     apply (clarsimp simp: nat_case_split)
     apply (rule corres_split_forwards' [where
                 Q = "\<lambda>rv s. True" and
                 Q' = "\<lambda>next_cap. valid_objs and (\<lambda>a. a \<turnstile> next_cap) and valid_global_refs and
                                  valid_idle and valid_etcbs"])
        apply (rule get_cap_corres[THEN corres_guard_imp])
          apply (clarsimp simp:transform_cslot_ptr_def)
          apply (simp add: branch_map_simp2)
         apply clarsimp
        apply clarsimp
        apply (erule (1) cnode_not_idle)
       apply (wp |simp)+
     apply (clarsimp simp:cdl_resolve_address_bits_eq is_cnode_cap_transform_cap | rule conjI)+
      apply (subst cdl_resolve_address_bits_eq)
       apply (subgoal_tac "a+b-a \<le> b" for a b)
        apply simp+
      apply (subst length_drop)
      apply (rule Suc.hyps[rule_format])
      apply fastforce
     apply (clarsimp simp:returnOk_def transform_cslot_ptr_def)
     apply (simp add: branch_map_simp2)
    apply (drule (1) transform_objects_cnode, simp,
             clarsimp simp: transform_objects_cnode gets_the_def gets_def get_def
                             bind_def return_def valid_def exs_valid_def assert_opt_def
                             transform_def nat_case_split)+
  done
qed

lemmas resolve_address_bits_corres = resolve_address_bits_corres' [OF eq_refl, OF refl]

lemma dcorres_injection_handler_rhs:
  "dcorres (dc \<oplus> r) P P' f g
     \<Longrightarrow> dcorres (dc \<oplus> r) P P' f (injection_handler h g)"
  apply (clarsimp simp:injection_handler_def)
  apply (clarsimp simp:handleE'_def)
  apply (rule corres_dummy_return_l)
  apply (rule corres_guard_imp)
    apply (rule corres_split_forwards'[where Q'="\<lambda>a. \<top>" and Q = "\<lambda>a. \<top>"])
       apply assumption
      apply wp+
    apply (clarsimp simp:return_def)
    apply (case_tac v)
     apply (clarsimp simp:throwError_def return_def corres_underlying_def)+
  done

lemma not_idle_thread_resolve_address_bits:
  "\<lbrace>valid_global_refs and valid_objs and valid_idle and valid_irq_node and ko_at (TCB obj) thread and valid_etcbs\<rbrace>
    CSpace_A.resolve_address_bits (tcb_ctable obj, blist)
            \<lbrace>\<lambda>rv s. not_idle_thread (fst (fst rv)) s \<and> valid_etcbs s\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>"
  apply (rule validE_R_validE)
  apply (rule_tac hoare_weaken_preE_R)
   apply (rule validE_validE_R)
   apply (rule_tac Q="\<lambda>r. valid_etcbs and valid_global_refs and valid_objs and valid_idle and
                          valid_irq_node and ex_cte_cap_to (fst r)"
          in hoare_strengthen_postE[where E="\<lambda>x y. True"])
     apply (wp rab_cte_cap_to)
    apply (auto intro: ex_cte_cap_wp_to_not_idle)[2]
  apply (clarsimp simp:ex_cte_cap_to_def)
  apply (rule_tac x = thread in exI,rule_tac x = "tcb_cnode_index 0" in exI)
  apply (clarsimp simp:cte_wp_at_cases obj_at_def is_cap_simps)
  done

lemma lookup_cap_corres:
  "\<lbrakk>w = of_bl blist;length blist = word_bits\<rbrakk> \<Longrightarrow>
  dcorres (dc \<oplus> (\<lambda>x y. x = transform_cap y)) \<top>
     (valid_global_refs and valid_objs and valid_irq_node and valid_idle and not_idle_thread thread and valid_etcbs)
     (CSpace_D.lookup_cap thread w)
     (lookup_cap thread blist)"
  apply (simp add:CSpace_D.lookup_cap_def lookup_cap_def)
  apply (simp add:lookup_slot_def lookup_slot_for_thread_def bindE_assoc)
  apply (clarsimp simp: liftE_bindE)
  apply (rule dcorres_gets_the)
   apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE[where r'="\<lambda>x y. fst x = transform_cslot_ptr (fst y)"])
        apply (rule corres_rel_imp)
         apply (rule resolve_address_bits_corres)
           apply (simp add: word_bits_def)
          apply (clarsimp simp: obj_at_def opt_cap_tcb not_idle_thread_def transform_cap_def word_bits_def)+
        apply (case_tac x, auto)[1]
       apply (simp add:liftE_bindE split_def)
       apply (rule get_cap_corres[unfolded split_def])
       apply simp
      apply wp
     apply wp
     apply (rule validE_validE_R)
     apply (wp not_idle_thread_resolve_address_bits[where thread = thread])
    apply simp+
   apply (simp add:objs_valid_tcb_ctable)+
   apply clarsimp
  apply (clarsimp simp:not_idle_thread_def opt_cap_tcb | drule(1) valid_etcbs_get_tcb_get_etcb)+
  done

lemma cdl_current_thread:
  "(cdl_current_thread (transform s')) = transform_current_thread s'"
  by (clarsimp simp:transform_def )

lemma get_cap_get_tcb_dcorres:
  "dcorres (\<lambda>r t. r = transform_cap (tcb_ctable t)) \<top> (not_idle_thread thread and valid_etcbs)
  (KHeap_D.get_cap (thread, tcb_cspace_slot))
  (gets_the (get_tcb thread))"
  apply (clarsimp simp: corres_underlying_def)
  apply (clarsimp simp: gets_the_def bind_def simpler_gets_def assert_opt_def fail_def return_def
                  split: option.splits)
  apply (frule(1) valid_etcbs_get_tcb_get_etcb, clarsimp)
  apply (drule opt_cap_tcb [where sl=tcb_cspace_slot])
    apply clarsimp
   apply (simp add: not_idle_thread_def)
  apply simp
  done

lemma dcorres_lookup_slot:
  "\<lbrakk>w = of_bl ptr;length ptr = word_bits\<rbrakk> \<Longrightarrow>
  dcorres (dc \<oplus> (\<lambda>x y. x = transform_cslot_ptr (fst y))) \<top>
  (not_idle_thread thread and valid_global_refs and valid_objs and valid_irq_node and valid_idle and valid_etcbs)
  (CSpace_D.lookup_slot thread w)
  (CSpace_A.lookup_slot_for_thread thread ptr)"
  apply (simp add: CSpace_D.lookup_slot_def lookup_slot_for_thread_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply simp
       apply (rule get_cap_get_tcb_dcorres)
      apply (rule corres_dummy_returnOk_r)
      apply (rule corres_splitEE[OF resolve_address_bits_corres])
           apply (clarsimp simp: word_bits_def)+
        apply (rule corres_returnOk [where P=\<top> and P'=\<top>])
        apply clarsimp
       apply wpsimp+
  apply (erule (1) objs_valid_tcb_ctable)
  done


lemma dcorres_lookup_cap_and_slot:
  "\<lbrakk>w = of_bl ptr;length ptr = word_bits\<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> (\<lambda>x y. fst x = transform_cap (fst y) \<and> snd x = transform_cslot_ptr (snd y))) \<top>
  (not_idle_thread thread and valid_global_refs and valid_objs and valid_irq_node and valid_idle and valid_etcbs)
  (CSpace_D.lookup_cap_and_slot thread w)
  (cap_fault_on_failure w False $ CSpace_A.lookup_cap_and_slot thread ptr)"
  apply (simp add: CSpace_D.lookup_cap_and_slot_def cap_fault_injection
                   CSpace_A.lookup_cap_and_slot_def split_def)
  apply (rule dcorres_injection_handler_rhs)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule dcorres_lookup_slot; clarsimp)
      apply (rule corres_splitEE)
         apply simp
         apply (rule get_cap_corres, rule refl)
        apply (rule dcorres_returnOk, simp)
       apply ((wp|simp)+)
    apply (rule hoare_strengthen_postE_R [where Q'="\<lambda>rv. valid_idle and valid_etcbs and real_cte_at (fst rv)"])
     apply (wp lookup_slot_real_cte_at_wp)
    apply (clarsimp simp: valid_idle_def not_idle_thread_def
                          pred_tcb_at_def obj_at_def is_cap_table_def)
   apply simp
  apply simp
  done

lemma dcorres_machine_op_noop:
  "\<lbrakk> \<And>m. \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> mop \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace> \<rbrakk>
       \<Longrightarrow> dcorres dc \<top> \<top> (return ()) (do_machine_op mop)"
  supply if_cong[cong]
  apply (simp add: do_machine_op_def)
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_r[OF _ _ gets_wp])
      apply (rule corres_symb_exec_r)
         apply (simp add: split_beta)
         apply (rule corres_split[where r'=dc, THEN corres_add_noop_lhs,
                                  OF _ _ return_wp])
           apply (simp add: return_modify)
           apply (rule_tac P=\<top> and P'="\<lambda>s. underlying_memory (snd rv)
                    = underlying_memory (machine_state s)" in corres_modify)
           apply (clarsimp simp: transform_def transform_objects_def2
                                 transform_current_thread_def)
          apply (rule corres_trivial, simp)
         apply (wp | simp)+
  apply clarsimp
  apply (drule use_valid, assumption, rule refl)
  apply simp
  done

lemma set_cap_noop_dcorres1:
  "dcorres dc
           (\<lambda>s. opt_cap (transform_cslot_ptr ptr) s = Some (transform_cap cap))
           (valid_idle and not_idle_thread (fst ptr) and valid_etcbs)
    (return ()) (set_cap cap ptr)"
  apply (rule corres_cong[OF refl refl _ refl refl, THEN iffD1])
   apply (erule set_cap_is_noop_opt_cap)
  apply (rule corres_guard_imp, rule set_cap_corres, simp_all add: not_idle_thread_def)
  done

lemma set_cap_noop_dcorres2:
  "dcorres dc \<top> (cte_wp_at (\<lambda>cap'. transform_cap cap = transform_cap cap') ptr
                     and not_idle_thread (fst ptr)
                     and valid_idle and valid_etcbs)
    (return ()) (set_cap cap ptr)"
  apply (rule stronger_corres_guard_imp, rule set_cap_noop_dcorres1, simp_all)
  apply (clarsimp simp: cte_wp_at_caps_of_state not_idle_thread_def
                        caps_of_state_transform_opt_cap)
  done

end

end
