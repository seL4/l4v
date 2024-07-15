(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchKHeap_AI
imports KHeapPre_AI
begin

context Arch begin global_naming RISCV64

definition "non_vspace_obj \<equiv> non_arch_obj"
definition "vspace_obj_pred \<equiv> arch_obj_pred"

end

locale vspace_only_obj_pred = Arch +
  fixes P :: "kernel_object \<Rightarrow> bool"
  assumes vspace_only: "vspace_obj_pred P"

sublocale vspace_only_obj_pred < arch_only_obj_pred
  using vspace_only[unfolded vspace_obj_pred_def] by unfold_locales

context Arch begin global_naming RISCV64

lemma valid_vspace_obj_lift:
  assumes "\<And>T p. f \<lbrace>typ_at (AArch T) p\<rbrace>"
  shows "f \<lbrace>valid_vspace_obj level obj\<rbrace>"
  by ((cases obj; simp),
      safe; wpsimp wp: assms hoare_vcg_ball_lift hoare_vcg_all_lift valid_pte_lift)

lemma aobjs_of_atyp_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace>"
  by (wpsimp simp: typ_at_aobjs wp: assms)

lemma valid_vspace_objs_lift_vs_lookup:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_kernel_vspace (arch_state s)) \<rbrace>"
  shows   "\<lbrace>valid_vspace_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def
  apply (wp hoare_vcg_all_lift)
   apply (rule hoare_lift_Pf[where f="aobjs_of"])
    apply (rule hoare_lift_Pf[where f="\<lambda>s. riscv_kernel_vspace (arch_state s)"])
     apply (rule_tac f="vs_lookup" in hoare_lift_Pf)
      apply (wpsimp wp: assms hoare_vcg_imp_lift valid_vspace_obj_lift aobjs_of_atyp_lift)+
  done

lemma vspace_obj_imp:
  "non_arch_obj ko \<Longrightarrow> non_vspace_obj ko"
  unfolding non_vspace_obj_def by assumption

lemma non_vspace_objs[intro!]:
  "non_vspace_obj (Endpoint ep)"
  "non_vspace_obj (CNode sz cnode_contents)"
  "non_vspace_obj (TCB tcb)"
  "non_vspace_obj (Notification notification)"
  "non_vspace_obj (SchedContext sc n)"
  "non_vspace_obj (Reply r)"
  by (auto simp: non_vspace_obj_def)

lemma vspace_obj_predE:
  "\<lbrakk>vspace_obj_pred P; non_vspace_obj ko; non_vspace_obj ko'\<rbrakk> \<Longrightarrow> P ko = P ko'"
  unfolding  vspace_obj_pred_def non_vspace_obj_def by (rule arch_obj_predE)

lemmas vspace_obj_pred_defs = non_vspace_objs vspace_obj_pred_def

lemma vspace_pred_imp:
  "vspace_obj_pred P \<Longrightarrow> arch_obj_pred P"
  using vspace_obj_pred_def by simp

lemma vspace_obj_pred_a_type[intro!, simp]:
  "vspace_obj_pred (\<lambda>ko. a_type ko = AArch T)"
  by (auto simp: vspace_obj_pred_def)

lemma vspace_obj_pred_arch_obj_l[intro!, simp]:
  "vspace_obj_pred (\<lambda>ko. ArchObj ako = ko)"
  by (auto simp: vspace_obj_pred_def)

lemma vspace_obj_pred_arch_obj_r[intro!, simp]:
  "vspace_obj_pred (\<lambda>ko. ko = ArchObj ako)"
  by (auto simp: vspace_obj_pred_def)

lemma vspace_obj_pred_const_conjI[intro]:
  "\<lbrakk> vspace_obj_pred P; vspace_obj_pred P' \<rbrakk> \<Longrightarrow> vspace_obj_pred (\<lambda>ko. P ko \<and> P' ko)"
  unfolding vspace_obj_pred_def by blast

lemma vspace_obj_pred_fI:
  "(\<And>x. vspace_obj_pred (P x)) \<Longrightarrow> vspace_obj_pred (\<lambda>ko. f (\<lambda>x. P x ko))"
  by (simp only: vspace_obj_pred_def arch_obj_pred_fI)

lemmas [intro!] = vspace_obj_pred_fI[where f=All] vspace_obj_pred_fI[where f=Ex]

lemma kheap_typ_only:
  "(\<forall>p ko. kheap s p = Some ko \<longrightarrow> P p (a_type ko)) = (\<forall>p T. typ_at T p s \<longrightarrow> P p T)"
  by (auto simp: obj_at_def)

lemma pspace_in_kernel_window_atyp_lift_strong:
  assumes "\<And>P p T. f \<lbrace>\<lambda>s. P (typ_at T p s) \<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_kernel_vspace (arch_state s))\<rbrace>"
  shows      "\<lbrace>\<lambda>s. pspace_in_kernel_window s\<rbrace> f \<lbrace>\<lambda>rv s. pspace_in_kernel_window s\<rbrace>"
  unfolding pspace_in_kernel_window_def obj_bits_T
  apply (rule hoare_lift_Pf[where f="\<lambda>s. riscv_kernel_vspace (arch_state s)"])
   apply (subst kheap_typ_only)+
   apply (wpsimp wp: hoare_vcg_all_lift wp: assms)+
  done

lemma pspace_in_kernel_window_atyp_lift:
  assumes "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. pspace_in_kernel_window s\<rbrace> f \<lbrace>\<lambda>rv s. pspace_in_kernel_window s\<rbrace>"
  by (rule pspace_in_kernel_window_atyp_lift_strong[OF assms])

lemma cap_refs_in_kernel_window_arch_update[simp]:
  "riscv_kernel_vspace (f (arch_state s)) = riscv_kernel_vspace (arch_state s)
   \<Longrightarrow> cap_refs_in_kernel_window (arch_state_update f s) = cap_refs_in_kernel_window s"
  by (simp add: cap_refs_in_kernel_window_def)

lemma in_user_frame_obj_pred_lift:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  shows "f \<lbrace>in_user_frame p\<rbrace> "
  unfolding in_user_frame_def
  by (wpsimp wp: hoare_vcg_ex_lift assms simp: vspace_obj_pred_def)

lemma pool_for_asid_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_asid_table (arch_state s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  by (wpsimp simp: pool_for_asid_def wp: assms)

lemma vs_lookup_table_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_asid_table (arch_state s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_table level asid vref s)\<rbrace>"
  apply (simp add: vs_lookup_table_def obind_def split: option.splits)
  apply (wpsimp wp: assms hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift' pool_for_asid_lift
                simp: not_le)
  done

lemma vs_lookup_slot_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_asid_table (arch_state s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_slot level asid vref s)\<rbrace>"
  apply (simp add: vs_lookup_slot_def obind_def split: option.splits)
  apply (wpsimp wp: assms hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift' pool_for_asid_lift
                    vs_lookup_table_lift
                simp: not_le)
  done

lemma vs_lookup_target_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_asid_table (arch_state s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_target level asid vref s)\<rbrace>"
  apply (simp add: vs_lookup_target_def obind_def split: option.splits)
  apply (wpsimp wp: assms hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift' pool_for_asid_lift
                    vs_lookup_slot_lift
                simp: not_le)
  done

lemma vs_lookup_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_asid_table (arch_state s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  apply (rule_tac P=P in hoare_liftP_ext)+
  apply (rename_tac P asid)
  apply (rule_tac P=P in hoare_liftP_ext)
  by (rule vs_lookup_table_lift; rule assms)

lemma vs_lookup_vspace_aobjs_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows " f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  by (rule vs_lookup_lift; rule assms)

lemma valid_vspace_objs_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows   "f \<lbrace>valid_vspace_objs\<rbrace>"
  by (rule valid_vspace_objs_lift_vs_lookup, rule vs_lookup_lift; rule assms)

lemma aobjs_of_ako_at_Some:
  "(aobjs_of s p = Some ao) = ako_at ao p s"
  by (simp add: obj_at_def in_opt_map_eq)

lemma aobjs_of_ako_at_None:
  "(aobjs_of s p = None) = (\<not> obj_at (\<lambda>obj. \<exists>ao. obj = ArchObj ao) p s)"
  apply (clarsimp simp: obj_at_def opt_map_def split: option.splits)
  apply (rename_tac ao, case_tac ao; simp)
  done

(* The only arch objects on RISC-V are vspace_objs *)
lemma vspace_obj_pred_aobjs:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  shows "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule_tac P=P in rsubst)
  apply (rule ext, rename_tac s' p)
  apply (case_tac "aobjs_of s p")
   apply (simp add: aobjs_of_ako_at_None)
   apply (drule use_valid)
     prefer 2
     apply assumption
    apply (rule assms)
    apply (clarsimp simp: vspace_obj_pred_def arch_obj_pred_def non_arch_obj_def)
   apply (simp flip: aobjs_of_ako_at_None)
  apply (simp add: aobjs_of_ako_at_Some)
  apply (drule use_valid)
    prefer 2
    apply assumption
   apply (rule assms)
   apply simp
  apply (simp flip: aobjs_of_ako_at_Some)
  done

lemma pts_of_lift:
  assumes aobj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (pts_of s)\<rbrace>"
  by (rule hoare_lift_Pf2[where f=aobjs_of], (wp vspace_obj_pred_aobjs aobj_at)+)

lemma ptes_of_lift:
  assumes aobj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  by (rule hoare_lift_Pf2[where f=aobjs_of], (wp vspace_obj_pred_aobjs aobj_at)+)

lemma asid_pools_of_lift:
  assumes aobj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  by (rule hoare_lift_Pf2[where f=aobjs_of], (wp vspace_obj_pred_aobjs aobj_at)+)

lemma vs_lookup_vspace_obj_at_lift:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  by (rule vs_lookup_vspace_aobjs_lift, rule vspace_obj_pred_aobjs; rule assms)

lemma vs_lookup_arch_obj_at_lift:
  assumes "\<And>P P' p. arch_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  by (intro vs_lookup_vspace_obj_at_lift assms vspace_pred_imp)

lemma vs_lookup_pages_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_asid_table (arch_state s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  apply (rule_tac P=P in hoare_liftP_ext)+
  apply (rename_tac P asid)
  apply (rule_tac P=P in hoare_liftP_ext)
  by (rule vs_lookup_target_lift; fact)

lemma vs_lookup_pages_vspace_aobjs_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  by (wpsimp wp: vs_lookup_pages_lift assms)

lemma vs_lookup_pages_vspace_obj_at_lift:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  by (rule vs_lookup_pages_vspace_aobjs_lift, rule vspace_obj_pred_aobjs; rule assms)

lemma vs_lookup_pages_arch_obj_at_lift:
  assumes "\<And>P P' p. arch_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  by (intro vs_lookup_pages_vspace_obj_at_lift assms vspace_pred_imp)

lemma valid_vspace_objs_lift_weak:
  assumes "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>valid_vspace_objs\<rbrace> f \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  by (rule valid_vspace_objs_lift, rule vspace_obj_pred_aobjs; rule assms)

lemma translate_address_lift_weak:
  assumes aobj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (translate_address pt_root vref (ptes_of s)) \<rbrace>"
  unfolding translate_address_def pt_lookup_target_def
  apply (clarsimp simp: comp_def obind_def)
  apply (rule hoare_lift_Pf2[where f=ptes_of, OF _ ptes_of_lift[OF aobj_at]]; simp)
   apply (clarsimp split: option.splits)
   apply (rule hoare_lift_Pf2[where f=pte_refs_of])
   apply (rule hoare_lift_Pf2[where f=aobjs_of], (wp vspace_obj_pred_aobjs aobj_at)+)
  done

lemma set_pt_pts_of:
  "\<lbrace>\<lambda>s. pts_of s p \<noteq> None \<longrightarrow> P ((pts_of s)(p \<mapsto> pt)) \<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (pts_of s)\<rbrace>"
  unfolding set_pt_def
  by (wpsimp wp: set_object_wp)
     (auto elim!: rsubst[where P=P] simp: opt_map_def split: option.splits)

lemma pte_ptr_eq:
  "\<lbrakk> (ucast (p && mask pt_bits >> pte_bits) :: pt_index) =
     (ucast (p' && mask pt_bits >> pte_bits) :: pt_index);
     p && ~~ mask pt_bits = p' && ~~ mask pt_bits;
     is_aligned p pte_bits; is_aligned p' pte_bits \<rbrakk>
   \<Longrightarrow> p = p'"
  apply (simp add: ucast_eq_mask)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size is_aligned_nth)
  apply (case_tac "n < pte_bits", simp)
  apply (drule_tac x="n-pte_bits" in word_eqD)
  apply (drule_tac x="n" in word_eqD)
  apply (simp add: word_size neg_mask_test_bit nth_shiftr not_less)
  apply (case_tac "pt_bits \<le> n", simp)
  by (fastforce simp: not_le bit_simps)

lemma store_pte_ptes_of:
  "\<lbrace>\<lambda>s. ptes_of s p \<noteq> None \<longrightarrow> P ((ptes_of s)(p \<mapsto> pte)) \<rbrace> store_pte p pte \<lbrace>\<lambda>_ s. P (ptes_of s)\<rbrace>"
  unfolding store_pte_def pte_of_def
  apply (wpsimp wp: set_pt_pts_of simp: in_omonad)
  by (auto simp: obind_def opt_map_def split: option.splits dest!: pte_ptr_eq elim!: rsubst[where P=P])

lemma vspace_for_pool_not_pte:
  "\<lbrakk> vspace_for_pool p asid (asid_pools_of s) = Some p';
     ptes_of s p = Some pte; pspace_aligned s \<rbrakk>
   \<Longrightarrow> False"
  by (fastforce simp: in_omonad ptes_of_def bit_simps vspace_for_pool_def dest: pspace_alignedD)

definition level_of_slot :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> vm_level"
  where
  "level_of_slot asid vref p s \<equiv>
     GREATEST level. vs_lookup_slot level asid vref s = Some (level, p)"

lemma level_of_slotI:
  "\<lbrakk> vs_lookup_slot level' asid vref s = Some (level', p); level < level'\<rbrakk>
   \<Longrightarrow> vs_lookup_slot (level_of_slot asid vref p s) asid vref s = Some (level_of_slot asid vref p s, p)
       \<and> level < level_of_slot asid vref p s"
  by (auto simp: level_of_slot_def dest: bit0.GreatestI bit0.Greatest_le)

lemma pool_for_asid_no_pt:
  "\<lbrakk> pool_for_asid asid s = Some p; pts_of s p = Some pte; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> False"
  unfolding pool_for_asid_def
  by (fastforce dest: pspace_alignedD dest!: valid_asid_tableD
                simp: bit_simps obj_at_def ptes_of_Some in_omonad)

lemma pool_for_asid_no_pte:
  "\<lbrakk> pool_for_asid asid s = Some p; ptes_of s p = Some pte; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> False"
  unfolding pool_for_asid_def
  by (fastforce dest: pspace_alignedD dest!: valid_asid_tableD
                simp: bit_simps obj_at_def ptes_of_Some in_omonad)

lemma vs_lookup_table_no_asid:
  "\<lbrakk> vs_lookup_table asid_pool_level asid vref s = Some (asid_pool_level, p);
     ptes_of s p = Some pte; valid_asid_table s; pspace_aligned s \<rbrakk>
  \<Longrightarrow> False"
  unfolding vs_lookup_table_def
  by (fastforce dest: pool_for_asid_no_pte simp: in_omonad)

lemma vs_lookup_table_no_asid_pt:
  "\<lbrakk> vs_lookup_table asid_pool_level asid vref s = Some (asid_pool_level, p);
     pts_of s p = Some pte; valid_asid_table s; pspace_aligned s \<rbrakk>
  \<Longrightarrow> False"
  unfolding vs_lookup_table_def
  by (fastforce dest: pool_for_asid_no_pt simp: in_omonad)

lemma vs_lookup_slot_no_asid:
  "\<lbrakk> vs_lookup_slot asid_pool_level asid vref s = Some (asid_pool_level, p);
     ptes_of s p = Some pte; valid_asid_table s; pspace_aligned s \<rbrakk>
  \<Longrightarrow> False"
  unfolding vs_lookup_slot_def vs_lookup_table_def
  by (fastforce dest: pool_for_asid_no_pte simp: in_omonad)

(* Removing a page table pte entry at p will cause lookups to stop at higher levels than requested.
   If performing a shallower lookup than the one requested results in p, then any deeper lookup
   in the updated state will return a higher level result along the original path. *)
lemma vs_lookup_non_PageTablePTE:
  "\<lbrakk> ptes_of s p \<noteq> None; ptes_of s' = (ptes_of s)(p \<mapsto> pte);
     \<not> is_PageTablePTE pte;
     asid_pools_of s' = asid_pools_of s;
     asid_table s' = asid_table s;
     valid_asid_table s; pspace_aligned s \<rbrakk> \<Longrightarrow>
   vs_lookup_table level asid vref s' =
     (if \<exists>level'. vs_lookup_slot level' asid vref s = Some (level', p) \<and> level < level'
      then vs_lookup_table (level_of_slot asid vref p s) asid vref s
      else vs_lookup_table level asid vref s)"
  apply (induct level rule: bit0.from_top_full_induct[where y=max_pt_level])
   apply (clarsimp simp: geq_max_pt_level)
   apply (erule disjE; clarsimp)
    apply (rule conjI; clarsimp)
     apply (fastforce dest!: vs_lookup_slot_no_asid)
    apply (simp add: vs_lookup_table_def pool_for_asid_def obind_def split: option.splits)
   apply (simp add: vs_lookup_table_def pool_for_asid_def obind_def split: option.splits)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (drule (1) level_of_slotI, clarsimp)
   apply (subst vs_lookup_split[where level'="level_of_slot asid vref p s"], simp)
    apply (rule ccontr)
    apply (fastforce dest!: vs_lookup_slot_no_asid simp: not_le)
   apply (clarsimp simp: vs_lookup_slot_def in_obind_eq)
   apply (simp split: if_split_asm)
    apply (fastforce dest!: vs_lookup_table_no_asid)
   apply (subst pt_walk.simps)
   apply (simp add: in_obind_eq)
  subgoal for x y
  apply (subst vs_lookup_split[where level'="x+1"])
    apply (simp add: less_imp_le)
   apply (simp add: bit0.plus_one_leq)
  apply (subst (2) vs_lookup_split[where level'="x+1"])
    apply (simp add: less_imp_le)
   apply (simp add: bit0.plus_one_leq)
  apply (erule_tac x="x+1" in allE)
  apply (simp add: less_imp_le)
  apply (simp  split: if_split_asm)
   apply (erule_tac x="level'" in allE, simp)
   apply (meson max_pt_level_less_Suc less_imp_le less_trans)
  apply (clarsimp simp: obind_def split: option.splits)
  apply (subst pt_walk.simps)
  apply (subst (2) pt_walk.simps)
  apply (simp add: less_imp_le cong: if_cong)
  apply (subgoal_tac "((ptes_of s)(p \<mapsto> pte)) (pt_slot_offset (x + 1) b vref)
                      = ptes_of s (pt_slot_offset (x + 1) b vref)")
   apply (simp add: obind_def split: option.splits)
  apply clarsimp
  apply (subgoal_tac "vs_lookup_slot (x+1) asid vref s = Some (x+1, p)")
   apply fastforce
  apply (clarsimp simp: vs_lookup_slot_def in_obind_eq)
  using bit0.plus_one_leq by fastforce
  done

lemma set_pt_typ_at[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (typ_at T p' s)\<rbrace>"
  unfolding set_pt_def
  by (wpsimp wp: set_object_wp simp: in_opt_map_eq obj_at_def)

crunch store_pte
  for kernel_vspace[wp]: "\<lambda>s. P (riscv_kernel_vspace (arch_state s))"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imps)

lemma store_pte_non_PageTablePTE_vs_lookup:
  "\<lbrace>\<lambda>s. (ptes_of s p \<noteq> None \<longrightarrow>
         P (if \<exists>level'. vs_lookup_slot level' asid vref s = Some (level', p) \<and> level < level'
            then vs_lookup_table (level_of_slot asid vref p s) asid vref s
            else vs_lookup_table level asid vref s)) \<and> pspace_aligned s \<and> valid_asid_table s
        \<and> \<not> is_PageTablePTE pte \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_ s. P (vs_lookup_table level asid vref s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp simp: in_opt_map_eq ptes_of_Some)
  apply (erule rsubst[where P=P])
  apply (subst (3) vs_lookup_non_PageTablePTE)
      apply (fastforce simp: in_omonad pte_of_def)
     apply (fastforce simp: pte_of_def obind_def opt_map_def split: option.splits dest!: pte_ptr_eq)
    apply (fastforce simp: opt_map_def)+
  done

lemma store_pte_not_ao[wp]:
  "\<lbrace>\<lambda>s. \<forall>pt. aobjs_of s (p && ~~mask pt_bits) = Some (PageTable pt) \<longrightarrow>
             P ((aobjs_of s)(p && ~~mask pt_bits \<mapsto>
                              PageTable (pt (ucast (p && mask pt_bits >> pte_bits) := pte))))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_ s. P (aobjs_of s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp simp: in_opt_map_eq)
  apply (fastforce simp: opt_map_def elim!: rsubst[where P=P])
  done

lemma valid_vspace_obj_PT_invalidate:
  "valid_vspace_obj level (PageTable pt) s \<Longrightarrow>
   valid_vspace_obj level (PageTable (pt(i := InvalidPTE))) s"
  by clarsimp

lemma store_pte_InvalidPTE_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs and pspace_aligned and valid_asid_table\<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' valid_vspace_obj_lift
                    store_pte_non_PageTablePTE_vs_lookup)
  apply (rule conjI; clarsimp)
   apply (rename_tac level slot pte ao pt)
   apply (drule (1) level_of_slotI)
   apply (case_tac "slot = table_base p"; clarsimp simp del: valid_vspace_obj.simps)
   apply (fastforce intro!: valid_vspace_obj_PT_invalidate)
  apply (rename_tac s bot_level vref asid level slot pte ao pt)
  apply (clarsimp simp: vs_lookup_slot_def)
  apply (case_tac "slot = table_base p"; clarsimp simp del: valid_vspace_obj.simps)
  apply (fastforce intro!: valid_vspace_obj_PT_invalidate)
  done

lemma set_object_valid_kernel_mappings:
  "set_object ptr ko \<lbrace>valid_kernel_mappings\<rbrace>"
  unfolding set_object_def
  by (wpsimp simp: valid_kernel_mappings_def split: if_split_asm)

(* interface lemma *)
lemmas set_object_v_ker_map = set_object_valid_kernel_mappings

lemma valid_vs_lookup_lift:
  assumes lookup: "\<And>P. f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. f \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  assumes archvspace: "\<And>P. f \<lbrace>\<lambda>s. P (riscv_kernel_vspace (arch_state s))\<rbrace>"
  shows "f \<lbrace>valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply clarsimp
  apply (rule hoare_lift_Pf [where f=vs_lookup_pages])
   apply (rule hoare_lift_Pf [where f="\<lambda>s. (caps_of_state s)"])
    apply (rule hoare_lift_Pf [where f="\<lambda>s. (riscv_kernel_vspace (arch_state s))"])
     apply (wpsimp wp: lookup cap archvspace)+
  done

lemma valid_arch_caps_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes pts: "\<And>P. f \<lbrace>\<lambda>s. P (pts_of s)\<rbrace>"
  assumes archvspace: "\<And>P. f \<lbrace>\<lambda>s. P (riscv_kernel_vspace (arch_state s))\<rbrace>"
  assumes asidtable: "\<And>P. f \<lbrace>\<lambda>s. P (riscv_asid_table (arch_state s))\<rbrace>"
  shows "\<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding valid_arch_caps_def
  apply (wpsimp wp: valid_vs_lookup_lift lookup cap archvspace)
   apply (rule hoare_lift_Pf2[where f="\<lambda>s. (caps_of_state s)"])
    apply (wpsimp wp: cap archvspace asidtable pts)+
  done

context
  fixes f :: "'a::state_ext state \<Rightarrow> ('b \<times> 'a state) set \<times> bool"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
begin

context
  assumes aobj_at:
    "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow> \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
begin

lemma valid_global_vspace_mappings_lift:
  "f \<lbrace>valid_global_vspace_mappings\<rbrace>"
  unfolding valid_global_vspace_mappings_def
  supply validNF_prop[wp_unsafe del]
  by (rule hoare_lift_Pf2[where f=arch_state, OF _ arch])
     (wpsimp simp: Let_def wp: hoare_vcg_ball_lift translate_address_lift_weak aobj_at)

lemma valid_arch_caps_lift_weak:
  assumes cap: "(\<And>P. f \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>)"
  shows "f \<lbrace>valid_arch_caps\<rbrace>"
  supply validNF_prop[wp_unsafe del]
  by (rule valid_arch_caps_lift)
     (wpsimp wp: vs_lookup_pages_vspace_obj_at_lift[OF aobj_at] pts_of_lift[OF aobj_at]
                 arch cap)+

lemma valid_global_objs_lift_weak:
  "\<lbrace>valid_global_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  unfolding valid_global_objs_def by wp

lemma valid_asid_map_lift:
    "\<lbrace>valid_asid_map\<rbrace> f \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  by (wpsimp simp: valid_asid_map_def)

lemma valid_kernel_mappings_lift:
    "\<lbrace>valid_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  unfolding valid_kernel_mappings_def by wp

end

context
  assumes aobj_at: "\<And>P P' pd. arch_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace>"
begin

lemma aobjs_of_lift_aobj_at:
  "f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule_tac P=P in rsubst)
  apply (rule ext, rename_tac s' p)
  apply (case_tac "aobjs_of s p")
   apply (simp add: aobjs_of_ako_at_None)
   apply (drule use_valid)
     prefer 2
     apply assumption
    apply (rule aobj_at)
    apply (clarsimp simp: arch_obj_pred_def non_arch_obj_def)
   apply (simp flip: aobjs_of_ako_at_None)
  apply (simp add: aobjs_of_ako_at_Some)
  apply (drule use_valid)
    prefer 2
    apply assumption
   apply (rule aobj_at)
   apply simp
  apply (simp flip: aobjs_of_ako_at_Some)
  done

lemma valid_arch_state_lift_aobj_at:
  "f \<lbrace>valid_arch_state\<rbrace>"
  unfolding valid_arch_state_def valid_asid_table_def valid_global_arch_objs_def pt_at_eq
  apply (wp_pre, wps arch aobjs_of_lift_aobj_at)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_ball_lift)
  apply simp
  done

end
end

lemma equal_kernel_mappings_lift:
  assumes aobj_at: "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace>"
  assumes [wp]: "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows "f \<lbrace>equal_kernel_mappings\<rbrace>"
proof -
  have [wp]: "\<And>P. f \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
    by (rule vspace_obj_pred_aobjs[OF aobj_at])
  show ?thesis
    unfolding equal_kernel_mappings_def has_kernel_mappings_def
    apply (wp_pre, wps, wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' vspace_for_asid_lift)
    apply simp
    done
qed

lemma valid_machine_state_lift:
  assumes memory: "\<And>P. \<lbrace>\<lambda>s. P (underlying_memory (machine_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (underlying_memory (machine_state s))\<rbrace>"
  assumes aobj_at: "\<And>P' pd. arch_obj_pred P' \<Longrightarrow> \<lbrace>obj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. obj_at P' pd s\<rbrace>"
  shows "\<lbrace>valid_machine_state\<rbrace> f \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def
  apply (rule hoare_lift_Pf[where f="\<lambda>s. underlying_memory (machine_state s)", OF _ memory])
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_vcg_disj_lift[OF _ hoare_vcg_prop])
  apply (rule in_user_frame_lift)
  apply (wp aobj_at; simp)
  done

lemma valid_vso_at_lift:
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p s)\<rbrace>"
      and y: "\<And>ao. \<lbrace>\<lambda>s. ko_at (ArchObj ao) p s\<rbrace> f \<lbrace>\<lambda>rv s. ko_at (ArchObj ao) p s\<rbrace>"
  shows      "\<lbrace>valid_vso_at level p\<rbrace> f \<lbrace>\<lambda>rv. valid_vso_at level p\<rbrace>"
  unfolding valid_vso_at_def
  by (wpsimp wp: hoare_vcg_ex_lift y valid_vspace_obj_typ z simp: aobjs_of_ako_at_Some)

lemma valid_vso_at_lift_aobj_at:
  assumes [wp]: "\<And>P' pd. vspace_obj_pred P' \<Longrightarrow> f \<lbrace>obj_at P' pd\<rbrace>"
  shows "f \<lbrace>valid_vso_at level p\<rbrace>"
  unfolding valid_vso_at_def
  by (wpsimp wp: hoare_vcg_ex_lift valid_vspace_obj_typ simp: aobjs_of_ako_at_Some)

lemma valid_global_vspace_mappings_arch_update[simp]:
  "\<lbrakk> riscv_global_pt (arch_state (f s)) = riscv_global_pt (arch_state s);
     riscv_kernel_vspace (arch_state (f s)) = riscv_kernel_vspace (arch_state s);
     ptes_of (f s) = ptes_of s \<rbrakk>
     \<Longrightarrow> valid_global_vspace_mappings (f s) = valid_global_vspace_mappings s"
  unfolding valid_global_vspace_mappings_def
  by simp

lemma valid_table_caps_ptD:
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PageTableCap p' None));
     valid_table_caps s \<rbrakk> \<Longrightarrow>
   \<exists>pt. pts_of s p' = Some pt \<and> valid_vspace_obj level (PageTable pt) s"
  by (fastforce simp: valid_table_caps_def simp del: split_paired_Ex)

lemma store_pde_pred_tcb_at:
  "store_pte ptr val \<lbrace>\<lambda>s. N (pred_tcb_at proj P t s)\<rbrace>"
  apply (wpsimp simp: store_pte_def set_pt_def wp: set_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def in_opt_map_eq)
  done

lemma in_user_frame_obj_upd:
  "\<lbrakk>kheap s p = Some ko; a_type k = a_type ko\<rbrakk> \<Longrightarrow>
   in_user_frame x (s\<lparr>kheap := \<lambda>a. if a = p then Some k else kheap s a\<rparr>)
   = in_user_frame x s"
  apply (rule iffI)
  apply (clarsimp simp: in_user_frame_def obj_at_def split: if_split_asm)
   apply (elim disjE)
    apply clarsimp
    apply (intro exI)
    apply (rule conjI,assumption)
    apply (simp add: a_type_def)
   apply (fastforce simp: a_type_def)
  apply (clarsimp simp: in_user_frame_def obj_at_def split: if_split_asm)
  apply (rule_tac x = sz in exI)
  apply (intro conjI impI)
    apply (fastforce simp: a_type_def)+
  done

lemma user_mem_obj_upd_dom:
  "\<lbrakk>kheap s p = Some ko; a_type k = a_type ko\<rbrakk> \<Longrightarrow>
   dom (user_mem (s\<lparr>kheap := \<lambda>a. if a = p then Some k else kheap s a\<rparr>))
   = dom (user_mem s)"
  by (clarsimp simp: user_mem_def in_user_frame_obj_upd dom_def)

lemma in_device_frame_obj_upd:
  "\<lbrakk>kheap s p = Some ko; a_type k = a_type ko\<rbrakk> \<Longrightarrow>
   in_device_frame x (s\<lparr>kheap := \<lambda>a. if a = p then Some k else kheap s a\<rparr>)
   = in_device_frame x s"
  apply (rule iffI)
  apply (clarsimp simp: in_device_frame_def obj_at_def split: if_split_asm)
   apply (elim disjE)
    apply clarsimp
    apply (intro exI)
    apply (rule conjI,assumption)
    apply (simp add: a_type_def)
   apply (fastforce simp: a_type_def)
  apply (clarsimp simp: in_device_frame_def obj_at_def split: if_split_asm)
  apply (rule_tac x = sz in exI)
  apply (intro conjI impI)
    apply (fastforce simp: a_type_def)+
  done

lemma device_mem_obj_upd_dom:
  "\<lbrakk>kheap s p = Some ko; a_type k = a_type ko\<rbrakk> \<Longrightarrow>
   dom (device_mem (s\<lparr>kheap := \<lambda>a. if a = p then Some k else kheap s a\<rparr>))
   = dom (device_mem s)"
  by (clarsimp simp: device_mem_def in_device_frame_obj_upd dom_def)

lemma pspace_respects_region_cong[cong]:
  "\<lbrakk>kheap a  = kheap b; device_state (machine_state a) = device_state (machine_state b)\<rbrakk>
  \<Longrightarrow> pspace_respects_device_region a = pspace_respects_device_region b"
  by (simp add: pspace_respects_device_region_def device_mem_def user_mem_def in_device_frame_def
    in_user_frame_def obj_at_def dom_def)

definition "obj_is_device tp dev \<equiv>
  case tp of Untyped \<Rightarrow> dev
    | _ \<Rightarrow>(case default_object tp dev 0 0 of ArchObj (DataPage dev _) \<Rightarrow> dev
          | _ \<Rightarrow> False)"

lemma cap_is_device_obj_is_device[simp]:
  "cap_is_device (default_cap tp a sz dev) = obj_is_device tp dev"
  by (simp add: default_cap_def arch_default_cap_def obj_is_device_def
                default_object_def  default_arch_object_def
         split: apiobject_type.splits aobject_type.splits)

crunch storeWord
  for device_state_inv: "\<lambda>ms. P (device_state ms)"
  (ignore_del: storeWord)

(* some hyp_ref invariants *)

lemma state_hyp_refs_of_ep_update:
  "typ_at AEndpoint ep s \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(ep \<mapsto> Endpoint val)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def hyp_refs_of_def)
  done

lemma state_hyp_refs_of_ntfn_update:
  "typ_at ANTFN ep s \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(ep \<mapsto> Notification val)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def hyp_refs_of_def)
  done

lemma state_hyp_refs_of_sc_update:
  "typ_at (ASchedContext n) sc s \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(sc \<mapsto> SchedContext val n)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp: RISCV64.state_hyp_refs_of_def obj_at_def RISCV64.hyp_refs_of_def
                 split: kernel_object.splits)
  done

lemma state_hyp_refs_of_reply_update:
  "typ_at AReply r s \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(r \<mapsto> Reply val)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: RISCV64.state_hyp_refs_of_def obj_at_def RISCV64.hyp_refs_of_def)
  done

lemma state_hyp_refs_of_tcb_bound_ntfn_update:
  "kheap s t = Some (TCB tcb) \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_bound_notification := ntfn\<rparr>))\<rparr>)
     = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_sched_context_update:
  "kheap s t = Some (TCB tcb) \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_sched_context := sc\<rparr>))\<rparr>)
     = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: RISCV64.state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_yield_to_update:
  "kheap s t = Some (TCB tcb) \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_yield_to := sc\<rparr>))\<rparr>)
     = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: RISCV64.state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_state_update:
  "kheap s t = Some (TCB tcb) \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_state := ts\<rparr>))\<rparr>)
     = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_domain_update:
  "kheap s t = Some (TCB tcb) \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_domain := d\<rparr>))\<rparr>)
     = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_priority_update:
  "kheap s t = Some (TCB tcb) \<Longrightarrow>
   state_hyp_refs_of (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_priority := d\<rparr>))\<rparr>)
     = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma default_arch_object_not_live[simp]: "\<not> live (ArchObj (default_arch_object aty dev us))"
  by (clarsimp simp: default_arch_object_def live_def hyp_live_def arch_live_def
               split: aobject_type.splits)

lemma default_tcb_not_live[simp]: "\<not> live (TCB (default_tcb d))"
  by (clarsimp simp: default_tcb_def default_arch_tcb_def live_def hyp_live_def)

lemma valid_arch_tcb_same_type:
  "\<lbrakk> valid_arch_tcb t s; valid_obj p k s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> valid_arch_tcb t (s\<lparr>kheap := (kheap s)(p \<mapsto> k)\<rparr>)"
  by (auto simp: valid_arch_tcb_def obj_at_def)


(* interface lemma *)
lemma valid_ioports_lift:
  assumes x: "\<And>P. f \<lbrace>\<lambda>rv. P (caps_of_state s)\<rbrace>"
  assumes y: "\<And>P. f \<lbrace>\<lambda>s. P (arch_state s)\<rbrace>"
  shows      "f \<lbrace>valid_ioports\<rbrace>"
  by wpsimp

(* interface lemma *)
lemma valid_arch_mdb_lift:
  assumes c: "\<And>P. f \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  assumes r: "\<And>P. f \<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace>"
  shows "f \<lbrace>\<lambda>s. valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrace>"
  by (wpsimp simp: valid_arch_mdb_def)

(* interface lemma *)
lemma arch_valid_obj_same_type:
  "\<lbrakk> arch_valid_obj ao s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> arch_valid_obj ao (s\<lparr>kheap := (kheap s)(p \<mapsto> k)\<rparr>)"
  by simp

lemma valid_vspace_obj_same_type:
  "\<lbrakk>valid_vspace_obj l ao s;  kheap s p = Some ko; a_type ko' = a_type ko\<rbrakk>
  \<Longrightarrow> valid_vspace_obj l ao (s\<lparr>kheap := (kheap s)(p \<mapsto> ko')\<rparr>)"
    apply (rule hoare_to_pure_kheap_upd[OF valid_vspace_obj_typ])
    by (auto simp: obj_at_def)

lemma invs_valid_uses[elim!]:
  "invs s \<Longrightarrow> valid_uses s"
  by (simp add: invs_def valid_state_def valid_arch_state_def)

lemma set_tcb_obj_ref_asid_map[wp]:
  "set_tcb_obj_ref f t ko \<lbrace>valid_asid_map\<rbrace>"
  by (wpsimp simp: valid_asid_map_def)

lemma update_sched_context_hyp_refs_of[wp]:
  "update_sched_context ptr f \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule all_ext)
  apply (clarsimp simp: state_hyp_refs_of_def obj_at_def hyp_refs_of_def
                 split: kernel_object.splits)
  done

lemma update_valid_tcb[simp]:
  "\<And>f. valid_tcb ptr tcb (release_queue_update f s) = valid_tcb ptr tcb s"
  "\<And>f. valid_tcb ptr tcb (reprogram_timer_update f s) = valid_tcb ptr tcb s"
  "\<And>f. valid_tcb ptr tcb (ready_queues_update f s) = valid_tcb ptr tcb s"
  "\<And>f. valid_tcb ptr tcb (scheduler_action_update f s) = valid_tcb ptr tcb s"
  by (auto simp: valid_tcb_def valid_tcb_state_def valid_bound_obj_def valid_arch_tcb_def
          split: thread_state.splits option.splits)

lemma valid_tcbs_machine_state_update[iff]:
  "valid_tcbs (machine_state_update f s) = valid_tcbs s"
  by (rule iffI;
      clarsimp simp: valid_tcbs_def valid_tcb_def valid_bound_obj_def valid_tcb_state_def
                     valid_arch_tcb_def obj_at_def;
      rename_tac ptr tcb; drule_tac x=ptr and y=tcb in spec2; clarsimp;
      case_tac "tcb_state tcb"; clarsimp split: option.splits)

end
end
