(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ArchKHeap_AI
imports "../KHeapPre_AI"
begin

(* FIXME: move to Word *)
lemma ucast_eq_mask:
  "(UCAST('a::len \<rightarrow> 'b::len) x = UCAST('a \<rightarrow> 'b) y) =
   (x && mask LENGTH('b) = y && mask LENGTH('b))"
  apply (cases "LENGTH('b) < LENGTH('a)")
   apply (auto simp: nth_ucast word_size intro!: word_eqI dest: word_eqD)[1]
  apply (auto simp: shiftr_eq_0 and_mask_eq_iff_shiftr_0[THEN iffD2] dest: ucast_up_inj)
  done

(* FIXME RISCV: move *)
lemma hoare_liftP_ext:
  assumes "\<And>P x. m \<lbrace>\<lambda>s. P (f s x)\<rbrace>"
  shows "m \<lbrace>\<lambda>s. P (f s)\<rbrace>"
  unfolding valid_def
  apply clarsimp
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (drule use_valid, rule assms, rule refl)
  apply simp
  done


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

lemma vs_lookup_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_asid_table (arch_state s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  apply (rule_tac P=P in hoare_liftP_ext)+
  apply (rename_tac P asid)
  apply (rule_tac P=P in hoare_liftP_ext)
  apply (simp add: vs_lookup_table_def obind_def split: option.splits)
  apply (wpsimp wp: assms hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift' pool_for_asid_lift
                simp: not_le)
  done

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

lemma vs_lookup_target_lift:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (ptes_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (riscv_asid_table (arch_state s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vs_lookup_target level asid vref s)\<rbrace>"
  apply (simp add: vs_lookup_target_def vs_lookup_slot_def obind_def split: option.splits)
  apply (wpsimp wp: assms hoare_vcg_all_lift hoare_vcg_imp_lift' pool_for_asid_lift vs_lookup_lift
                simp: not_le)
  done

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
  "\<lbrace>\<lambda>s. pts_of s p \<noteq> None \<longrightarrow> P (pts_of s (p \<mapsto> pt)) \<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (pts_of s)\<rbrace>"
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
  apply (simp add: word_size neg_mask_bang nth_shiftr not_less)
  apply (case_tac "pt_bits \<le> n", simp)
  by (fastforce simp: not_le bit_simps)

lemma store_pte_ptes_of:
  "\<lbrace>\<lambda>s. ptes_of s p \<noteq> None \<longrightarrow> P (ptes_of s (p \<mapsto> pte)) \<rbrace> store_pte p pte \<lbrace>\<lambda>_ s. P (ptes_of s)\<rbrace>"
  unfolding store_pte_def pte_of_def
  apply (wpsimp wp: set_pt_pts_of simp: in_omonad)
  by (auto simp: obind_def opt_map_def split: option.splits dest!: pte_ptr_eq elim!: rsubst[where P=P])

lemma vspace_for_pool_not_pte:
  "\<lbrakk> vspace_for_pool p asid (asid_pools_of s) = Some p';
     ptes_of s p = Some pte; pspace_aligned s \<rbrakk>
   \<Longrightarrow> False"
  by (fastforce simp: in_omonad ptes_of_def bit_simps vspace_for_pool_def dest: pspace_alignedD)

lemma vs_lookup_slot_pte_level:
  "\<lbrakk> vs_lookup_slot level asid vref s = Some (level, p);
     ptes_of s p = Some pte; pspace_aligned s \<rbrakk>
   \<Longrightarrow> level \<le> max_pt_level"
  sorry

definition level_of_slot :: "asid \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> vm_level"
  where
  "level_of_slot asid vref p s \<equiv>
     SOME level'. vs_lookup_slot level' asid vref s = Some (level', p)"

(* Invalidating an entry at p will cause lookups to stop at higher levels than requested.
   If performing a shallower lookup than the one requested results in p, then any deeper lookup
   in the updated state will return None. *)
lemma vs_lookup_InvalidPTE:
  "\<lbrakk> ptes_of s p \<noteq> None; ptes_of s' = ptes_of s (p \<mapsto> InvalidPTE);
     asid_pools_of s' = asid_pools_of s;
     asid_table s' = asid_table s;
     pspace_aligned s \<rbrakk> \<Longrightarrow>
   vs_lookup_table level asid vref s' =
     (if \<exists>level'. vs_lookup_slot level' asid vref s = Some (level', p) \<and> level < level'
      then vs_lookup_table (level_of_slot asid vref p s) asid vref s
      else vs_lookup_table level asid vref s)"
  apply (induct level rule: bit0.from_top_full_induct[where y=max_pt_level])
   apply (clarsimp simp: geq_max_pt_level)
   apply (erule disjE; clarsimp)
    apply (rule conjI; clarsimp)
     apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def obind_def pool_for_asid_def in_omonad
                    split: option.splits)
  sorry (*
     apply (fastforce dest!: vspace_for_pool_not_pte)
    apply (fastforce dest: vs_lookup_max_pt_level_eq)
   apply (fastforce dest: vs_lookup_asid_pool_level_eq)
  apply (rename_tac level)
  apply clarsimp
  apply (rename_tac pte)
  apply (rule conjI; clarsimp)
   apply (frule (2) vs_lookup_slot_pte_level)
   apply (subst (asm) (2) vs_lookup_slot_def)
   apply (clarsimp simp: in_omonad split: if_split_asm)

   apply (subst vs_lookup_split, erule less_imp_le, assumption)
   apply (clarsimp simp: obind_def split: option.splits)
   apply (rule conjI; clarsimp)
    apply (subst (asm) (2) vs_lookup_slot_def)
    apply (clarsimp simp: in_omonad split: if_split_asm)
    apply (subst pt_walk.simps)
    apply (simp add: obind_def)
  oops *)

lemma set_pt_typ_at[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (typ_at T p' s)\<rbrace>"
  unfolding set_pt_def
  by (wpsimp wp: set_object_wp simp: in_opt_map_eq obj_at_def)

crunches store_pte
  for kernel_vspace[wp]: "\<lambda>s. P (riscv_kernel_vspace (arch_state s))"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imps)

lemma store_pte_InvalidPTE_vs_lookup[wp]:
  "\<lbrace>\<lambda>s. (ptes_of s p \<noteq> None \<longrightarrow>
         P (if \<exists>level'. vs_lookup_slot level' asid vref s = Some (level', p) \<and> level < level'
            then vs_lookup_table (level_of_slot asid vref p s) asid vref s
            else vs_lookup_table level asid vref s)) \<and> pspace_aligned s \<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_ s. P (vs_lookup_table level asid vref s)\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp simp: in_opt_map_eq ptes_of_Some)
  apply (erule rsubst[where P=P])
  apply (subst (3) vs_lookup_InvalidPTE)
      apply (fastforce simp: in_omonad pte_of_def)
     apply (fastforce simp: pte_of_def obind_def opt_map_def split: option.splits dest!: pte_ptr_eq)
    apply (fastforce simp: opt_map_def)+
  done

lemma store_pte_not_ao[wp]:
  "\<lbrace>\<lambda>s. \<forall>pt. aobjs_of s (p && ~~mask pt_bits) = Some (PageTable pt) \<longrightarrow>
             P (aobjs_of s (p && ~~mask pt_bits \<mapsto>
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

lemma level_of_slot_eq:
  "\<lbrakk> vs_lookup_slot level' vref asid s = Some (level', p);
     vs_lookup_table (level_of_slot vref asid p s) vref asid s = Some (level, slot) \<rbrakk>
  \<Longrightarrow> level_of_slot vref asid p s = level'"
  apply (clarsimp simp: vs_lookup_slot_def in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
  sorry (* FIXME RISCV: not really true with just "SOME" *)

lemma store_pte_InvalidPTE_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs and pspace_aligned\<rbrace> store_pte p InvalidPTE \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' valid_vspace_obj_lift)
  apply (rule conjI; clarsimp)
   apply (rename_tac s bot_level vref asid level' level slot pte ao pt)
   apply (frule (1) level_of_slot_eq)
   apply (case_tac "slot = p && ~~ mask pt_bits"; clarsimp simp del: valid_vspace_obj.simps)
   apply (fastforce intro!: valid_vspace_obj_PT_invalidate)
  apply (rename_tac s bot_level vref asid level slot pte ao pt)
  apply (clarsimp simp: vs_lookup_slot_def)
  apply (rename_tac s bot_level vref asid level slot pte ao pt)
  apply (case_tac "slot = p && ~~ mask pt_bits"; clarsimp simp del: valid_vspace_obj.simps)
  apply (fastforce intro!: valid_vspace_obj_PT_invalidate)
  done

(*
lemma set_object_vspace_objs:
  "\<lbrace>valid_vspace_objs and typ_at (a_type ko) p and
    (\<lambda>s. aobjs_of s p = Some ao \<longrightarrow> ko = ArchObj ao' \<longrightarrow> ao' \<le> ao) and
    obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p  and
    (\<lambda>s. case ko of ArchObj ao \<Rightarrow>
             \<forall>level asid vref. vs_lookup level asid vref s = Some (level, p) \<longrightarrow> valid_vspace_obj level ao s
            | _ \<Rightarrow> True)\<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (simp add: valid_vspace_objs_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply (subst imp_conv_disj)
  apply (subst imp_conv_disj)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift set_object_neg_lookup set_object_neg_ko)
  apply (wp valid_vspace_obj_typ2 [where Q="typ_at (a_type ko) p"] set_object_typ_at | simp)+
  apply (clarsimp simp: pred_neg_def obj_at_def)
  apply (case_tac ko; auto)
  done
*)

lemma set_object_valid_kernel_mappings:
  "set_object ptr ko \<lbrace>valid_kernel_mappings\<rbrace>"
  unfolding set_object_def
  by (wpsimp simp: valid_kernel_mappings_def split: if_split_asm)

(* interface lemma *)
lemmas set_object_v_ker_map = set_object_valid_kernel_mappings


(* FIXME RISCV: TODO
lemma valid_vs_lookup_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>valid_vs_lookup\<rbrace> f \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply (rule hoare_lift_Pf [where f=vs_lookup_pages])
   apply (rule hoare_lift_Pf [where f="\<lambda>s. (caps_of_state s)"])
     apply (wp lookup cap)+
  done
*)

(* FIXME RISCV: TODO, statement
lemma valid_table_caps_lift:
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes obj: "\<And>S p. \<lbrace>obj_at empty_table p\<rbrace> f \<lbrace>\<lambda>rv. obj_at empty_table p\<rbrace>"
  shows "\<lbrace>valid_table_caps\<rbrace> f \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def
   apply (rule hoare_lift_Pf [where f="\<lambda>s. (caps_of_state s)"])
    apply (rule hoare_lift_Pf [where f="\<lambda>s. second_level_tables (arch_state s)"])
     apply (wp cap pts hoare_vcg_all_lift hoare_vcg_const_imp_lift obj)+
  done
*)

(* FIXME RISCV: TODO
lemma valid_arch_caps_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes obj: "\<And>S p. \<lbrace>obj_at (empty_table S) p\<rbrace> f \<lbrace>\<lambda>rv. obj_at (empty_table S) p\<rbrace>"
  shows "\<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding valid_arch_caps_def
  apply (rule hoare_pre)
   apply (wp valid_vs_lookup_lift valid_table_caps_lift lookup cap pts obj)
  apply simp
  done
*)

(* FIXME RISCV: TODO
lemma valid_global_objs_lift':
  assumes pts: "\<And>P. \<lbrace>\<lambda>s. P (riscv_global_pts (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (riscv_global_pts (arch_state s))\<rbrace>"
  assumes obj: "\<And>p. \<lbrace>valid_vso_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_vso_at p\<rbrace>"
  assumes ko: "\<And>ako p. \<lbrace>ko_at (ArchObj ako) p\<rbrace> f \<lbrace>\<lambda>_. ko_at (ArchObj ako) p\<rbrace>"
  assumes emp: "\<And>pd S.
       \<lbrace>\<lambda>s. (v \<longrightarrow> pd = riscv_global_pml4 (arch_state s) \<and> S = set (second_level_tables (arch_state s)) \<and> P s)
            \<and> obj_at (empty_table S) pd s\<rbrace>
                 f \<lbrace>\<lambda>rv. obj_at (empty_table S) pd\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_global_objs s \<and> (v \<longrightarrow> P s)\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  unfolding valid_global_objs_def second_level_tables_def
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f="\<lambda>s. riscv_global_pts (arch_state s)", OF pts])
   apply (rule hoare_use_eq [where f="\<lambda>s. riscv_global_pds (arch_state s)", OF pds])
   apply (rule hoare_use_eq [where f="\<lambda>s. riscv_global_pdpts (arch_state s)", OF pdpts])
   apply (rule hoare_use_eq [where f="\<lambda>s. riscv_global_pml4 (arch_state s)", OF pml4])
   apply (wp obj ko emp hoare_vcg_const_Ball_lift hoare_ex_wp)
  apply (clarsimp simp: second_level_tables_def)
  done
*)

(* FIXME RISCV: TODO
lemmas valid_global_objs_lift
    = valid_global_objs_lift' [where v=False, simplified]
*)

context
  fixes f :: "'a::state_ext state \<Rightarrow> ('b \<times> 'a state) set \<times> bool"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
begin

context
  assumes aobj_at:
    "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow> \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
begin

lemma valid_global_vspace_mappings_lift:
  "\<lbrace>valid_global_vspace_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  sorry (* FIXME RISCV: TODO
  proof -
    have arch_obj_at_pres:
      "\<And>r s t N P Q p. \<lbrakk> (r,t) \<in> fst (f s); P = Q \<rbrakk>
        \<Longrightarrow> obj_at (vspace_obj_fun_lift P N) p s = obj_at (vspace_obj_fun_lift Q N) p t"
      apply safe
       apply (erule use_valid[OF _ aobj_at[where P="\<lambda>x. x"]]; simp)
      apply (rule classical;
             drule use_valid[OF _ aobj_at[where P="\<lambda>x. \<not>x", OF vspace_obj_pred_fun_lift_id]])
      by auto
    show ?thesis
      apply (simp only: valid_global_vspace_mappings_def valid_pml4_kernel_mappings_def)
      apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
      apply (rule_tac f="valid_pml4_kernel_mappings_arch (riscv_kernel_vspace x)" in hoare_lift_Pf)
       apply (rule aobj_at; simp)
      apply (simp only: valid_pml4_kernel_mappings_arch_def valid_pml4e_kernel_mappings_def)
      apply (clarsimp simp: valid_def)
      apply (erule_tac P=P in rsubst; rule ext)
      apply (clarsimp intro!: iff_allI split: arch_kernel_obj.splits)
      apply (rename_tac pml4 i)
      apply (case_tac "pml4 i"; simp)
      apply (simp only: valid_pdpt_kernel_mappings_def)
      apply (rule arch_obj_at_pres; simp; rule ext)
      apply (clarsimp simp: valid_pdpte_kernel_mappings_def
                     split: kernel_object.splits arch_kernel_obj.splits
                    intro!: iff_allI)
      apply (rename_tac pdpt j)
      apply (case_tac "pdpt j"; simp)
      apply (simp only: valid_pd_kernel_mappings_def)
      apply (rule arch_obj_at_pres; simp; rule ext)
      apply (clarsimp simp: valid_pde_kernel_mappings_def
                     split: kernel_object.splits arch_kernel_obj.splits
                    intro!: iff_allI)
      apply (rename_tac pd k)
      apply (case_tac "pd k"; simp)
      apply (simp only: valid_pt_kernel_mappings_def)
      apply (rule arch_obj_at_pres; simp)
      done
  qed *)

lemma valid_arch_caps_lift_weak:
    "(\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>) \<Longrightarrow>
      \<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  sorry (* FIXME RISCV: TODO
  apply (rule valid_arch_caps_lift[OF _ _ arch aobj_at])
    apply (rule vs_lookup_pages_vspace_obj_at_lift[OF aobj_at arch], assumption+)
  apply (rule empty_table.vspace_only)
  done *)

lemma valid_global_objs_lift_weak:
    "\<lbrace>valid_global_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  sorry (* FIXME RISCV: TODO
  apply (rule valid_global_objs_lift)
      apply (wp arch)+
    apply (simp add: valid_vso_at_def)
    apply (rule hoare_vcg_ex_lift)
    apply (rule hoare_vcg_conj_lift)
     apply (wp aobj_at valid_vspace_obj_typ | simp | rule empty_table.vspace_only)+
  done *)

lemma valid_asid_map_lift:
    "\<lbrace>valid_asid_map\<rbrace> f \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  by (wpsimp simp: valid_asid_map_def)

lemma valid_kernel_mappings_lift:
    "\<lbrace>valid_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  sorry (* FIXME RISCV: TODO
  apply (simp add: valid_kernel_mappings_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (simp add: valid_kernel_mappings_if_pm_def ran_def
              del: valid_kernel_mappings_if_pm_arch_def)
  apply (rule hoare_vcg_all_lift)
  apply (case_tac "\<exists>ao. xa = ArchObj ao")
   apply (rule hoare_convert_imp)
    apply clarsimp
    apply (rule hoare_vcg_all_lift)
    subgoal for ao a
    by (rule aobj_at[where P=Not and P'="\<lambda>x. x = ArchObj ao", simplified obj_at_def, simplified])
   apply clarsimp
   apply (case_tac ao; simp add: hoare_vcg_prop)
  apply (clarsimp simp del: valid_kernel_mappings_if_pm_arch_def)
  apply (case_tac xa; simp add: hoare_vcg_prop)
  done *)

end

context
  assumes aobj_at:
    "\<And>P P' pd. arch_obj_pred P' \<Longrightarrow> \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
begin

lemma valid_arch_state_lift_aobj_at:
    "\<lbrace>valid_arch_state\<rbrace> f \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  sorry (* FIXME RISCV: TODO
  apply (simp add: valid_arch_state_def valid_asid_table_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (wp hoare_vcg_conj_lift hoare_vcg_ball_lift
            valid_global_pts_lift valid_global_pds_lift valid_global_pdpts_lift
        | (rule aobj_at, clarsimp))+
  apply simp
  done *)

end
end

lemma equal_kernel_mappings_lift:
  assumes aobj_at:
    "\<And>P P' pd. vspace_obj_pred P' \<Longrightarrow> \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
  shows "\<lbrace>equal_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  sorry (* FIXME RISCV: TODO
  apply (simp add: equal_kernel_mappings_def)
  apply (rule hoare_vcg_all_lift)+
  apply (rule hoare_convert_imp)
   apply simp
   apply (rule hoare_convert_imp)
    apply (wp aobj_at[OF vspace_obj_pred_arch_obj_l])+
  done *)

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

(* FIXME RISCV: TODO
lemma valid_ao_at_lift:
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p s)\<rbrace>"
      and y: "\<And>ao. \<lbrace>\<lambda>s. ko_at (ArchObj ao) p s\<rbrace> f \<lbrace>\<lambda>rv s. ko_at (ArchObj ao) p s\<rbrace>"
  shows      "\<lbrace>valid_ao_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_ao_at p\<rbrace>"
  unfolding valid_ao_at_def
  by (wp hoare_vcg_ex_lift y valid_vspace_obj_typ z)
*)

(* FIXME RISCV: TODO
lemma valid_ao_at_lift_aobj_at:
  assumes aobj_at: "\<And>P' pd. arch_obj_pred P' \<Longrightarrow> \<lbrace>obj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. obj_at P' pd s\<rbrace>"
  shows      "\<lbrace>valid_ao_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_ao_at p\<rbrace>"
  unfolding valid_ao_at_def
  by (wp hoare_vcg_ex_lift valid_vspace_obj_typ aobj_at | clarsimp)+
*)

lemma valid_vso_at_lift:
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at (AArch T) p s)\<rbrace>"
      and y: "\<And>ao. \<lbrace>\<lambda>s. ko_at (ArchObj ao) p s\<rbrace> f \<lbrace>\<lambda>rv s. ko_at (ArchObj ao) p s\<rbrace>"
  shows      "\<lbrace>valid_vso_at level p\<rbrace> f \<lbrace>\<lambda>rv. valid_vso_at level p\<rbrace>"
  sorry (* FIXME RISCV: TODO
  unfolding valid_vso_at_def
  by (wpsimp wp: hoare_vcg_ex_lift y valid_vspace_obj_typ z)+
  *)

lemma valid_vso_at_lift_aobj_at:
  assumes aobj_at: "\<And>P' pd. vspace_obj_pred P' \<Longrightarrow> \<lbrace>obj_at P' pd\<rbrace> f \<lbrace>\<lambda>r s. obj_at P' pd s\<rbrace>"
  shows      "\<lbrace>valid_vso_at level p\<rbrace> f \<lbrace>\<lambda>rv. valid_vso_at level p\<rbrace>"
  sorry (* FIXME RISCV: TODO
  unfolding valid_vso_at_def
  apply (rule hoare_vcg_ex_lift)
  apply (rule hoare_vcg_conj_lift aobj_at)+
   apply (clarsimp simp: vspace_obj_pred_def)
  apply (wpsimp wp: valid_vspace_obj_typ)
   apply (wpsimp wp: aobj_at)
  apply assumption
  done *)

(* FIXME RISCV: TODO
lemma set_object_equal_mappings:
  "\<lbrace>\<lambda>s. equal_kernel_mappings s
          \<and> (\<forall>pml4. ko = ArchObj (PageMapL4 pml4)
                \<longrightarrow> (\<forall>x pml4'. ko_at (ArchObj (PageMapL4 pml4')) x s
                         \<longrightarrow> (\<forall>w \<in> kernel_mapping_slots. pml4 w = pml4' w)))\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: set_object_def, wp)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def
             split del: if_split)
  apply (simp split: if_split_asm)
  done *)

(* FIXME RISCV: TODO
lemma valid_global_vspace_mappings_pres:
  fixes s :: "'z::state_ext state" and s' :: "'z::state_ext state"
  assumes global_vspace_mappings_init:
    "valid_global_vspace_mappings s"
  assumes global_pml4_pres:
    "\<And>pm. ko_at (ArchObj (PageMapL4 pm)) (riscv_global_pml4 (arch_state s)) s
            \<Longrightarrow> ko_at (ArchObj (PageMapL4 pm)) (riscv_global_pml4 (arch_state s)) s'"
  assumes global_pts_pres:
    "\<And>pt p. \<lbrakk> ko_at (ArchObj (PageTable pt)) p s;
               valid_global_objs s \<Longrightarrow> p \<in> set (riscv_global_pts (arch_state s)) \<rbrakk>
            \<Longrightarrow> ko_at (ArchObj (PageTable pt)) p s'"
  assumes global_pdpts_pres:
    "\<And>pdpt p. \<lbrakk>ko_at (ArchObj (PDPointerTable pdpt)) p s;
                 valid_global_objs s \<Longrightarrow> p \<in> set (riscv_global_pdpts (arch_state s)) \<rbrakk>
            \<Longrightarrow> ko_at (ArchObj (PDPointerTable pdpt)) p s'"
  assumes global_pds_pres:
    "\<And>pd p. \<lbrakk>ko_at (ArchObj (PageDirectory pd)) p s;
               valid_global_objs s \<Longrightarrow> p \<in> set (riscv_global_pds (arch_state s)) \<rbrakk>
            \<Longrightarrow> ko_at (ArchObj (PageDirectory pd)) p s'"
  assumes state_pres[simp]:
    "riscv_global_pml4 (arch_state s') = riscv_global_pml4 (arch_state s)"
    "riscv_kernel_vspace (arch_state s') = riscv_kernel_vspace (arch_state s)"
  shows
    "valid_global_vspace_mappings s'"
  apply (insert global_vspace_mappings_init)
  apply (clarsimp simp: valid_global_vspace_mappings_def obj_at_def)
  apply (rename_tac pm_ko)
  apply (rule_tac x=pm_ko in exI)
  apply (valid_global_vspace_mappings pres: global_pml4_pres)
  apply (rename_tac pm i)
  apply (drule_tac x=i in spec)
  apply (clarsimp simp: valid_pml4e_kernel_mappings_def obj_at_def split: pml4e.splits)
  apply (rename_tac pdpt_ref pdpt_attr pdpt_perms pdpt_ko)
  apply (rule_tac x=pdpt_ko in exI)
  apply (valid_global_vspace_mappings pres: global_pdpts_pres)
  apply (rename_tac pdpt j)
  apply (drule_tac x=j in spec)
  apply (clarsimp simp: valid_pdpte_kernel_mappings_def obj_at_def split: pdpte.splits)
  apply (rename_tac pd_ref pd_attr pd_perms pd_ko)
  apply (rule_tac x=pd_ko in exI)
  apply (valid_global_vspace_mappings pres: global_pds_pres)
  apply (rename_tac pd k)
  apply (drule_tac x=k in spec)
  apply (clarsimp simp: valid_pde_kernel_mappings_def obj_at_def split: pde.splits)
  apply (rename_tac pt_ref pt_attr pt_perms pt_ko)
  apply (rule_tac x=pt_ko in exI)
  apply (valid_global_vspace_mappings pres: global_pts_pres)
  done
*)

lemma translate_address_pte_update:
  "ptes_of (f s) = ptes_of s \<Longrightarrow> translate_address pt vref (f s) = translate_address pt vref s"
  by (simp add: translate_address_def obind_def split: option.split)

lemma valid_global_vspace_mappings_arch_update[simp]:
  "\<lbrakk> riscv_global_pt (arch_state (f s)) = riscv_global_pt (arch_state s);
     riscv_kernel_vspace (arch_state (f s)) = riscv_kernel_vspace (arch_state s);
     ptes_of (f s) = ptes_of s \<rbrakk>
     \<Longrightarrow> valid_global_vspace_mappings (f s) = valid_global_vspace_mappings s"
  unfolding valid_global_vspace_mappings_def
  by (simp add: translate_address_pte_update)

lemma set_object_global_vspace_mappings:
  "\<lbrace>valid_global_vspace_mappings and (\<lambda>s. pt_at p s \<longrightarrow> p \<notin> global_refs s)\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_object_def, wp)
  apply clarsimp
  sorry (* FIXME RISCV: TODO *)


lemma valid_table_caps_ptD:
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PageTableCap p' None));
     valid_table_caps s \<rbrakk> \<Longrightarrow>
   \<exists>pt. pts_of s p' = Some pt \<and> valid_vspace_obj level (PageTable pt) s"
  by (fastforce simp: valid_table_caps_def simp del: split_paired_Ex)

lemma store_pde_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> store_pte ptr val \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
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
    | _ \<Rightarrow>(case (default_object tp dev 0) of (ArchObj (DataPage dev _)) \<Rightarrow> dev
          | _ \<Rightarrow> False)"

lemma cap_is_device_obj_is_device[simp]:
  "cap_is_device (default_cap tp a sz dev) = obj_is_device tp dev"
  by (simp add: default_cap_def arch_default_cap_def obj_is_device_def
                default_object_def  default_arch_object_def
         split: apiobject_type.splits aobject_type.splits)

crunch device_state_inv: storeWord "\<lambda>ms. P (device_state ms)"

(* some hyp_ref invariants *)

lemma state_hyp_refs_of_ep_update: "\<And>s ep val. typ_at AEndpoint ep s \<Longrightarrow>
       state_hyp_refs_of (s\<lparr>kheap := kheap s(ep \<mapsto> Endpoint val)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def hyp_refs_of_def)
  done

lemma state_hyp_refs_of_ntfn_update: "\<And>s ep val. typ_at ANTFN ep s \<Longrightarrow>
       state_hyp_refs_of (s\<lparr>kheap := kheap s(ep \<mapsto> Notification val)\<rparr>) = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def hyp_refs_of_def)
  done

lemma state_hyp_refs_of_tcb_bound_ntfn_update:
       "kheap s t = Some (TCB tcb) \<Longrightarrow>
          state_hyp_refs_of (s\<lparr>kheap := kheap s(t \<mapsto> TCB (tcb\<lparr>tcb_bound_notification := ntfn\<rparr>))\<rparr>)
            = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma state_hyp_refs_of_tcb_state_update:
       "kheap s t = Some (TCB tcb) \<Longrightarrow>
          state_hyp_refs_of (s\<lparr>kheap := kheap s(t \<mapsto> TCB (tcb\<lparr>tcb_state := ts\<rparr>))\<rparr>)
            = state_hyp_refs_of s"
  apply (rule all_ext)
  apply (clarsimp simp add: state_hyp_refs_of_def obj_at_def split: option.splits)
  done

lemma default_arch_object_not_live[simp]: "\<not> live (ArchObj (default_arch_object aty dev us))"
  by (clarsimp simp: default_arch_object_def live_def hyp_live_def arch_live_def
               split: aobject_type.splits)

lemma default_tcb_not_live[simp]: "\<not> live (TCB default_tcb)"
  by (clarsimp simp: default_tcb_def default_arch_tcb_def live_def hyp_live_def)

lemma valid_arch_tcb_same_type:
  "\<lbrakk> valid_arch_tcb t s; valid_obj p k s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> valid_arch_tcb t (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  by (auto simp: valid_arch_tcb_def obj_at_def)

lemma valid_ioports_lift[wp]:
  "f \<lbrace>valid_ioports\<rbrace>"
  by wpsimp

lemma valid_arch_mdb_lift[wp]:
  "f \<lbrace>\<lambda>s. valid_arch_mdb (is_original_cap s) (caps_of_state s)\<rbrace>"
  by (wpsimp simp: valid_arch_mdb_def)

(* interface lemma *)
lemma arch_valid_obj_same_type:
  "\<lbrakk> arch_valid_obj ao s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> arch_valid_obj ao (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  by simp

end
end
