(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Lemmas on arch get/set object etc
*)

theory ArchAcc_AI
imports
  SubMonad_AI
 "Lib.Crunch_Instances_NonDet"
begin

context Arch begin global_naming ARM


bundle unfold_objects =
  obj_at_def[simp]
  kernel_object.splits[split]
  arch_kernel_obj.splits[split]
  get_object_wp [wp]

bundle unfold_objects_asm =
  obj_at_def[simp]
  kernel_object.split_asm[split]
  arch_kernel_obj.split_asm[split]

definition
  "valid_asid asid s \<equiv> arm_asid_map (arch_state s) asid \<noteq> None"


lemma get_asid_pool_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pool. ko_at (ArchObj (ASIDPool pool)) p s \<longrightarrow> Q pool s\<rbrace>
  get_asid_pool p
  \<lbrace>Q\<rbrace>"
  apply (simp add: get_asid_pool_def get_object_def)
   apply (wp|wpc)+
  apply (clarsimp simp: obj_at_def)
  done


lemma set_asid_pool_typ_at [wp]:
  "set_asid_pool ptr pool \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def get_object_def)
  apply wp
  including unfold_objects
  by clarsimp


lemmas set_asid_pool_typ_ats [wp] = abs_typ_at_lifts [OF set_asid_pool_typ_at]


lemma get_pd_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) p s \<longrightarrow> Q pd s\<rbrace> get_pd p \<lbrace>Q\<rbrace>"
  unfolding get_pd_def including unfold_objects by wpsimp


lemma get_pde_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s \<longrightarrow>
        Q (pd (ucast (p && mask pd_bits >> 2))) s\<rbrace>
  get_pde p
  \<lbrace>Q\<rbrace>"
  by (simp add: get_pde_def) wp


lemma get_pde_inv [wp]: "get_pde p \<lbrace>P\<rbrace>"
  by (wpsimp wp: get_pde_wp)

bundle pagebits =
  pd_bits_def[simp] pt_bits_def[simp]
  pageBits_def[simp] mask_lower_twice[simp]
  and.assoc[where ?'a = \<open>'a::len word\<close>,symmetric,simp] obj_at_def[simp]
  pde.splits[split]
  pte.splits[split]

lemma get_master_pde_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s
        \<longrightarrow> Q (case (pd (ucast (p && ~~ mask 6 && mask pd_bits >> 2))) of
               SuperSectionPDE x xa xb \<Rightarrow> pd (ucast (p && ~~ mask 6 && mask pd_bits >> 2))
             | _ \<Rightarrow> pd (ucast (p && mask pd_bits >> 2))) s\<rbrace>
   get_master_pde p
   \<lbrace>Q\<rbrace>"
  apply (simp add: get_master_pde_def)
  apply (wp get_pde_wp | wpc)+
  including pagebits
  by auto

lemma store_pde_typ_at [wp]:
  "store_pde ptr pde \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def get_object_def)
  apply (wpsimp simp: obj_at_def a_type_def)
  done


lemmas store_pde_typ_ats [wp] = abs_typ_at_lifts [OF store_pde_typ_at]


lemma get_pt_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) p s \<longrightarrow> Q pt s\<rbrace> get_pt p \<lbrace>Q\<rbrace>"
  apply (simp add: get_pt_def get_object_def)
  apply (wpsimp simp: obj_at_def)
  done


lemma get_pte_wp:
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (p && ~~mask pt_bits) s \<longrightarrow>
        Q (pt (ucast (p && mask pt_bits >> 2))) s\<rbrace>
  get_pte p
  \<lbrace>Q\<rbrace>"
  by (simp add: get_pte_def) wp


lemma get_pte_inv [wp]:
  "\<lbrace>P\<rbrace> get_pte p \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp wp: get_pte_wp)


lemma get_master_pte_wp:
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (p && ~~ mask pt_bits) s \<longrightarrow>
          Q (case pt (ucast (p && ~~ mask 6 && mask pt_bits >> 2)) of
              LargePagePTE x xa xb \<Rightarrow>
                pt (ucast (p && ~~ mask 6 && mask pt_bits >> 2))
              | _ \<Rightarrow> pt (ucast (p && mask pt_bits >> 2)))
           s\<rbrace>
  get_master_pte p \<lbrace>Q\<rbrace>"
  apply (simp add: get_master_pte_def)
  apply (wp get_pte_wp | wpc)+
  including pagebits
  by auto

lemma store_pte_typ_at:
    "store_pte ptr pte \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def get_object_def)
  apply (wpsimp simp: obj_at_def a_type_def)
  done


lemmas store_pte_typ_ats [wp] = abs_typ_at_lifts [OF store_pte_typ_at]


lemma lookup_pt_slot_inv:
  "lookup_pt_slot pd vptr \<lbrace>P\<rbrace>"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp|wpc)+
  apply clarsimp
  done

lemma lookup_pt_slot_inv_any:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> lookup_pt_slot pd vptr \<lbrace>Q\<rbrace>,-"
  "\<lbrace>E\<rbrace> lookup_pt_slot pd vptr -, \<lbrace>\<lambda>ft. E\<rbrace>"
   apply (simp_all add: lookup_pt_slot_def)
   apply (wpsimp wp: get_pde_wp)+
  done

crunch cte_wp_at[wp]: set_irq_state "\<lambda>s. P (cte_wp_at P' p s)"

lemma set_pt_cte_wp_at:
  "set_pt ptr val \<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (subst cte_wp_at_after_update')
   apply (clarsimp simp: a_type_def obj_at_def split: if_splits kernel_object.splits)+
  done


lemma set_pd_cte_wp_at:
  "set_pd ptr val \<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (subst cte_wp_at_after_update')
  including unfold_objects
   apply (clarsimp simp: a_type_def split: if_splits)+
  done


lemma set_asid_pool_cte_wp_at:
  "set_asid_pool ptr val \<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects_asm
  by (wpsimp wp: set_object_wp_strong
           simp: a_type_def cte_wp_at_after_update'
          split: if_splits)

lemma set_pt_pred_tcb_at[wp]:
  "set_pt ptr val \<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s)\<rbrace>"
  apply (simp add: set_pt_def)
  supply rsubst[where P=Q, elim!]
  apply (wpsimp wp: set_object_wp_strong simp: pred_tcb_at_def obj_at_def)
  done

lemma set_pd_pred_tcb_at[wp]:
  "set_pd ptr val \<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s)\<rbrace>"
  apply (simp add: set_pd_def)
  supply rsubst[where P=Q, elim!]
  apply (wpsimp wp: set_object_wp_strong simp: pred_tcb_at_def obj_at_def)
  done


lemma set_asid_pool_pred_tcb_at[wp]:
  "set_asid_pool ptr val \<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s)\<rbrace>"
  apply (simp add: set_asid_pool_def)
  supply rsubst[where P=Q, elim!]
  apply (wpsimp wp: set_object_wp_strong simp: pred_tcb_at_def obj_at_def)
  done


lemma mask_pd_bits_inner_beauty:
  "is_aligned p 2 \<Longrightarrow>
  (p && ~~ mask pd_bits) + (ucast ((ucast (p && mask pd_bits >> 2))::12 word) << 2) = (p::word32)"
  by (rule mask_split_aligned; simp add: pd_bits_def pageBits_def)

lemma more_pd_inner_beauty:
  fixes x :: "12 word"
  fixes p :: word32
  assumes x: "x \<noteq> ucast (p && mask pd_bits >> 2)"
  shows "(p && ~~ mask pd_bits) + (ucast x << 2) = p \<Longrightarrow> False"
  by (rule mask_split_aligned_neg[OF _ _ x]; simp add: pd_bits_def pageBits_def)

lemma mask_pt_bits_inner_beauty:
  "is_aligned p 2 \<Longrightarrow>
  (p && ~~ mask pt_bits) + (ucast ((ucast (p && mask pt_bits >> 2))::word8) << 2) = (p::word32)"
  by (rule mask_split_aligned; simp add: pt_bits_def pageBits_def)

lemma more_pt_inner_beauty:
  fixes x :: "word8"
  fixes p :: word32
  assumes x: "x \<noteq> ucast (p && mask pt_bits >> 2)"
  shows "(p && ~~ mask pt_bits) + (ucast x << 2) = p \<Longrightarrow> False"
  by (rule mask_split_aligned_neg[OF _ _ x]; simp add: pt_bits_def pageBits_def)


lemma set_pd_aligned [wp]:
  "set_pd base pd \<lbrace>pspace_aligned\<rbrace>"
  by (wpsimp simp: set_pd_def)


crunch aligned [wp]: store_pde pspace_aligned
  (wp: hoare_drop_imps)


lemmas undefined_validE_R = hoare_FalseE_R[where f=undefined]


lemma arch_derive_cap_valid_cap:
  "\<lbrace>valid_cap (cap.ArchObjectCap arch_cap)\<rbrace>
  arch_derive_cap arch_cap
  \<lbrace>valid_cap\<rbrace>, -"
  apply(simp add: arch_derive_cap_def)
  apply(cases arch_cap, simp_all add: arch_derive_cap_def o_def)
      apply(rule hoare_pre, wpc?, wp+;
            clarsimp simp add: cap_aligned_def valid_cap_def split: option.splits)+
  done


lemma arch_derive_cap_inv:
  "arch_derive_cap arch_cap \<lbrace>P\<rbrace>"
  apply(simp add: arch_derive_cap_def, cases arch_cap, simp_all)
      apply(rule hoare_pre, wpc?, wp+; simp)+
  done

definition
  "valid_mapping_entries m \<equiv> case m of
    Inl (InvalidPTE, _) \<Rightarrow> \<top>
  | Inl (LargePagePTE _ _ _, xs) \<Rightarrow> \<lambda>s. \<forall>p \<in> set xs. pte_at p s
  | Inl (SmallPagePTE _ _ _, xs) \<Rightarrow> \<lambda>s. \<forall>p \<in> set xs. pte_at p s
  | Inr (InvalidPDE, _) \<Rightarrow> \<top>
  | Inr (PageTablePDE _ _ _, _) \<Rightarrow> \<bottom>
  | Inr (SectionPDE _ _ _ _, xs) \<Rightarrow> \<lambda>s. \<forall>p \<in> set xs. pde_at p s
  | Inr (SuperSectionPDE _ _ _, xs) \<Rightarrow> \<lambda>s. \<forall>p \<in> set xs. pde_at p s"

definition "invalid_pte_at p \<equiv> obj_at (\<lambda>ko. \<exists>pt. ko = (ArchObj (PageTable pt))
  \<and> pt (ucast (p && mask pt_bits) >> 2) = pte.InvalidPTE) (p && ~~ mask pt_bits)"

definition "invalid_pde_at p \<equiv> obj_at (\<lambda>ko. \<exists>pd. ko = (ArchObj (PageDirectory pd))
  \<and> pd (ucast (p && mask pd_bits) >> 2) = pde.InvalidPDE) (p && ~~ mask pd_bits)"

definition
  "valid_slots m \<equiv> case m of
    Inl (pte, xs) \<Rightarrow>
      \<lambda>s. xs \<noteq> [] \<and>
          (\<forall>p \<in> set xs. (\<exists>\<rhd> (p && ~~ mask pt_bits) and pte_at p) s) \<and>
          wellformed_pte pte \<and> valid_pte pte s
  | Inr (pde, xs) \<Rightarrow>
      \<lambda>s. xs \<noteq> [] \<and>
          (\<forall>p \<in> set xs. (\<exists>\<rhd> (p && ~~ mask pd_bits) and pde_at p) s \<and>
             ucast (p && mask pd_bits >> 2) \<notin> kernel_mapping_slots) \<and>
          wellformed_pde pde \<and> valid_pde pde s"

crunch inv[wp]: get_master_pte P
crunch inv[wp]: get_master_pde P

lemma ucast_mask_asid_low_bits [simp]:
  "ucast ((asid::word32) && mask asid_low_bits) = (ucast asid :: 10 word)"
  by (word_eqI_solve simp: asid_low_bits_def)


lemma ucast_ucast_asid_high_bits [simp]:
  "ucast (ucast (asid_high_bits_of asid)::word32) = asid_high_bits_of asid"
  by word_eqI_solve


lemma mask_asid_low_bits_ucast_ucast:
  "((asid::word32) && mask asid_low_bits) = ucast (ucast asid :: 10 word)"
  by (word_eqI_solve simp: asid_low_bits_def)


lemma set_asid_pool_cur [wp]:
  "set_asid_pool p a \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"
  unfolding set_asid_pool_def by (wpsimp wp: get_object_wp simp: set_object_def)


lemma set_asid_pool_cur_tcb [wp]:
  "set_asid_pool p a \<lbrace>\<lambda>s. cur_tcb s\<rbrace>"
  unfolding cur_tcb_def
  by (rule hoare_lift_Pf [where f=cur_thread]; wpsimp wp: tcb_at_typ_at)

lemma set_asid_pool_cur_sc_tcb [wp]:
  "set_asid_pool p a \<lbrace>cur_sc_tcb\<rbrace>"
  by (wpsimp simp: set_asid_pool_def set_object_def get_object_def cur_sc_tcb_def sc_tcb_sc_at_def
                   obj_at_def a_type_simps)

crunch arch [wp]: set_asid_pool "\<lambda>s. P (arch_state s)"
  (wp: get_object_wp)


lemma set_asid_pool_valid_arch [wp]:
  "set_asid_pool p a \<lbrace>valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) (wp set_asid_pool_typ_at)+


lemma set_asid_pool_valid_objs [wp]:
  "set_asid_pool p a \<lbrace>valid_objs\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_objs get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def valid_obj_def arch_valid_obj_def)

lemma pde_at_aligned_vptr:
  "\<lbrakk>x \<in> set [0 , 4 .e. 0x3C]; page_directory_at pd s;
   pspace_aligned s; is_aligned vptr 24 \<rbrakk>
  \<Longrightarrow> pde_at (x + lookup_pd_slot pd vptr) s"
  apply (clarsimp simp: lookup_pd_slot_def Let_def
                        obj_at_def pde_at_def)
  apply (drule(1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm if_split_asm
                 cong: kernel_object.case_cong)
  apply (prop_tac "is_aligned x 2")
  subgoal
    apply (clarsimp simp: upto_enum_step_def word_shift_by_2)
    by (rule is_aligned_shiftl_self)
  apply (simp add: aligned_add_aligned word_bits_conv
                   is_aligned_shiftl_self)+
  apply (prop_tac "pd = (x + (pd + (vptr >> 20 << 2)) && ~~ mask pd_bits)")
  subgoal
    supply bit_simps[simp del]
    apply (subst mask_lower_twice[symmetric, where n=6])
     apply (simp add: pd_bits_def pageBits_def)
    apply (subst add.commute, subst add_mask_lower_bits)
      apply (erule aligned_add_aligned)
       apply (intro is_aligned_shiftl is_aligned_shiftr)
       apply simp
      apply (simp add: word_bits_conv)
     apply simp
     apply (subst upper_bits_unset_is_l2p_32[unfolded word_bits_conv])
      apply simp
     apply (clarsimp simp: upto_enum_step_def word_shift_by_2)
     apply (rule shiftl_less_t2n[where m=6, simplified])
      apply (rule word_leq_minus_one_le)
       apply simp+
    apply (rule sym, rule add_mask_lower_bits)
     apply (simp add: pd_bits_def pageBits_def)
    apply simp
    apply (subst upper_bits_unset_is_l2p_32[unfolded word_bits_conv])
     apply (simp add: pd_bits_def pageBits_def)
    apply (rule shiftl_less_t2n)
     apply (rule shiftr_less_t2n')
      apply (simp add: pd_bits_def pageBits_def)
     by (simp add: pd_bits_def pageBits_def)+
  apply simp
  done


lemma pde_shifting:
  "\<lbrakk>is_aligned (vptr::word32) 24; x \<le> 0xF\<rbrakk> \<Longrightarrow> x + (vptr >> 20) < 0x1000"
  apply (rule order_less_le_trans)
   apply (subst upper_bits_unset_is_l2p_32 [where n=12, symmetric])
    apply (clarsimp simp: word_bits_def)
   prefer 2
   apply simp
  apply (clarsimp simp: word_bits_def)
  subgoal premises prems for n'
  proof -
  have H: "(0xF::word32) < 2 ^ 4" by simp
  from prems show ?thesis
    apply (subst (asm) word_plus_and_or_coroll)
     apply word_eqI
     subgoal for n
       apply (spec "20 + n")
       apply (simp add: word_size)
       apply (insert H)
        apply (drule (1) order_le_less_trans)
        apply (drule bang_is_le)
        apply (drule_tac z="2 ^ 4" in order_le_less_trans, assumption)
        apply (drule word_power_increasing)
        by simp+
    apply (clarsimp simp: word_size nth_shiftl nth_shiftr is_aligned_nth)
    apply (erule disjE)
     apply (insert H)[1]
      apply (drule (1) order_le_less_trans)
      apply (drule bang_is_le)
      apply (drule order_le_less_trans[where z="2 ^ 4"], assumption)
      apply (drule word_power_increasing; simp)
    apply (spec "20 + n'")
    apply (frule test_bit_size)
    by (simp add: word_size)
  qed
  done

lemma p_le_0xF_helper:
  "((p::word32) \<le> 0xF) = (\<forall>n'\<ge>4. n'< word_bits \<longrightarrow> \<not> p !! n')"
  apply (subst upper_bits_unset_is_l2p_32)
   apply (simp add: word_bits_def)
  apply (auto intro: plus_one_helper dest: plus_one_helper2)
  done

lemma pd_shifting:
  "is_aligned (pd::word32) 14 \<Longrightarrow> pd + (vptr >> 20 << 2) && ~~ mask pd_bits = pd"
  apply (rule word_eqI[rule_format])
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
  subgoal for \<dots> na
   apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth)
   apply (spec na)
   apply (simp add: linorder_not_less)
   apply (drule test_bit_size)+
   by (simp add: word_size)
  subgoal for n
    apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth word_ops_nth_size
                          pd_bits_def pageBits_def linorder_not_less)
    apply (rule iffI)
     apply clarsimp
     apply (drule test_bit_size)+
     apply (simp add: word_size)
    apply clarsimp
    apply (spec n)
    by simp
  done

lemma pd_shifting_dual:
  "is_aligned (pd::word32) 14 \<Longrightarrow> pd + (vptr >> 20 << 2) && mask pd_bits = vptr >> 20 << 2"
  apply (simp add: pd_bits_def pageBits_def)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   subgoal for n
     apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth)
     apply (spec n)
     apply (simp add: linorder_not_less)
     apply (drule test_bit_size)+
     by (simp add: word_size)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth word_ops_nth_size
                        pd_bits_def pageBits_def linorder_not_less)
  apply (rule iffI)
   apply clarsimp
  apply clarsimp
  apply (drule test_bit_size)+
  apply (simp add: word_size)
  done

lemma pd_shifting_at:
  "\<lbrakk> page_directory_at pd s; pspace_aligned s \<rbrakk> \<Longrightarrow>
  pd + (vptr >> 20 << 2) && ~~ mask pd_bits = pd"
  apply (rule pd_shifting)
  apply (clarsimp simp: pspace_aligned_def obj_at_def)
  apply (drule bspec, blast)
  including unfold_objects
  by (clarsimp simp: a_type_def)

lemma kernel_mapping_slots_empty_pdeI:
  "\<lbrakk>equal_kernel_mappings s; valid_global_objs s; valid_arch_state s;
    kheap s p = Some (ArchObj (PageDirectory pd)); x \<in> kernel_mapping_slots\<rbrakk> \<Longrightarrow>
   (\<forall>r. pde_ref (pd x) = Some r \<longrightarrow> r \<in> set (second_level_tables (arch_state s))) \<and> valid_pde_mappings (pd x)"
  apply (clarsimp simp: invs_def valid_state_def equal_kernel_mappings_def valid_global_objs_def)
  apply (erule_tac x=p in allE, erule_tac x="arm_global_pd (arch_state s)" in allE)
  including unfold_objects
  apply clarsimp
  by (simp add: empty_table_def valid_arch_state_def a_type_def)

lemma invs_valid_global_pts:
  "invs s \<Longrightarrow> valid_global_pts s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_state_def)

lemma is_aligned_pt:
  "page_table_at pt s \<Longrightarrow> pspace_aligned s
    \<Longrightarrow> is_aligned pt pt_bits"
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_alignedD)
  apply (simp add: pt_bits_def pageBits_def)
  done

lemma is_aligned_global_pt:
  "\<lbrakk>x \<in> set (arm_global_pts (arch_state s)); pspace_aligned s; valid_arch_state s\<rbrakk>
   \<Longrightarrow> is_aligned x pt_bits"
  by (metis valid_arch_state_def valid_global_pts_def
            is_aligned_pt)

lemma data_at_aligned:
  "\<lbrakk> data_at sz p s; pspace_aligned s \<rbrakk> \<Longrightarrow> is_aligned p (pageBitsForSize sz)"
  by (erule pspace_alignedE[where x=p]; fastforce simp: data_at_def obj_at_def)

lemma page_table_pte_at_diffE:
  "\<lbrakk> page_table_at p s; q - p = x << 2;
    x < 2^(pt_bits - 2); pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at q s"
  apply (clarsimp simp: diff_eq_eq add.commute)
  apply (erule(2) page_table_pte_atI)
  done

lemma pte_at_aligned_vptr:
  "\<lbrakk>x \<in> set [0 , 4 .e. 0x3C]; page_table_at pt s;
   pspace_aligned s; is_aligned vptr 16 \<rbrakk>
  \<Longrightarrow> pte_at (x + (pt + (((vptr >> 12) && 0xFF) << 2))) s"
  apply (erule page_table_pte_at_diffE[where x="(x >> 2) + ((vptr >> 12) && 0xFF)"];simp?)
   apply (simp add: word_shiftl_add_distrib upto_enum_step_def)
   apply (clarsimp simp: word_shift_by_2 shiftr_shiftl1 is_aligned_shift)
  apply (subst add.commute, rule is_aligned_add_less_t2n)
      apply (rule is_aligned_andI1[where n=4], rule is_aligned_shiftr, simp)
     apply (rule shiftr_less_t2n)
    apply (clarsimp dest!: upto_enum_step_subset[THEN subsetD])
    apply (erule order_le_less_trans, simp)
   apply (simp add: pt_bits_def pageBits_def)
  apply (simp add: pt_bits_def pageBits_def)
  apply (rule order_le_less_trans, rule word_and_le1, simp)
  done

lemma lookup_pt_slot_ptes_aligned_valid:
  "\<lbrace>valid_vspace_objs and valid_arch_state
    and equal_kernel_mappings and pspace_aligned
    and valid_global_objs
    and \<exists>\<rhd> pd and page_directory_at pd
    and K (is_aligned vptr 16)\<rbrace>
  lookup_pt_slot pd vptr
  \<lbrace>\<lambda>r s. is_aligned r 6 \<and> (\<forall>x\<in>set [0 , 4 .e. 0x3C]. pte_at (x + r) s)\<rbrace>, -"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp|wpc)+
  apply (clarsimp simp: lookup_pd_slot_def Let_def)
  apply (simp add: pd_shifting_at)
  apply (frule (2) valid_vspace_objsD)
  apply (clarsimp simp: )
  subgoal for s _ _ x
    apply (prop_tac "page_table_at (ptrFromPAddr x) s")
    subgoal
      apply (bspec "(ucast (pd + (vptr >> 20 << 2) && mask pd_bits >> 2))";clarsimp)
      apply (frule kernel_mapping_slots_empty_pdeI)
      apply ((simp add: obj_at_def pte_at_def;fail)+)[4]
      by (clarsimp simp: pde_ref_def valid_global_pts_def valid_arch_state_def second_level_tables_def)
    apply (rule conjI)
     apply (rule is_aligned_add)
      apply (rule is_aligned_weaken, erule(1) is_aligned_pt)
      apply (simp add: pt_bits_def pageBits_def)
     apply (rule is_aligned_shiftl)
     apply (rule is_aligned_andI1)
     apply (rule is_aligned_shiftr, simp)
    apply clarsimp
    by (erule(1) pte_at_aligned_vptr, simp+)
  done

lemma p_0x3C_shift:
  "is_aligned (p :: word32) 6 \<Longrightarrow>
  (\<forall>p\<in>set [p , p + 4 .e. p + 0x3C]. f p) = (\<forall>x\<in>set [0, 4 .e. 0x3C]. f (x + p))"
  apply (clarsimp simp: upto_enum_step_def add.commute)
  apply (frule is_aligned_no_overflow, simp add: word_bits_def)
  apply (simp add: linorder_not_le [symmetric])
  apply (erule notE)
  apply (simp add: add.commute)
  apply (erule word_random)
  apply simp
  done

lemma lookup_pt_slot_pte [wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state
   and equal_kernel_mappings and valid_global_objs
   and \<exists>\<rhd> pd and page_directory_at pd\<rbrace>
  lookup_pt_slot pd vptr \<lbrace>pte_at\<rbrace>,-"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp|wpc)+
  apply (clarsimp simp: lookup_pd_slot_def Let_def)
  apply (simp add: pd_shifting_at)
  apply (drule (2) valid_vspace_objsD)
  apply (clarsimp simp: )
  apply (bspec "ucast (pd + (vptr >> 20 << 2) && mask pd_bits >> 2)")
   apply clarsimp
   apply (erule page_table_pte_atI, simp_all)
   apply (simp add: pt_bits_def pageBits_def)
   apply (rule order_le_less_trans, rule word_and_le1, simp)
  apply (frule kernel_mapping_slots_empty_pdeI)
    apply (simp add: obj_at_def)+
  apply (clarsimp simp: pde_ref_def)
  apply (rule page_table_pte_atI, simp_all)
   apply (simp add: valid_arch_state_def valid_global_pts_def second_level_tables_def)
  apply (simp add: pt_bits_def pageBits_def)
  apply (rule order_le_less_trans, rule word_and_le1, simp)
  done

lemma shiftr_w2p:
  "x < len_of TYPE('a) \<Longrightarrow>
  2 ^ x = (2^(len_of TYPE('a) - 1) >> (len_of TYPE('a) - 1 - x) :: 'a :: len word)"
  apply simp
  apply (rule word_eqI)
  apply (auto simp: word_size nth_shiftr nth_w2p)
  done

lemma vptr_shiftr_le_2p:
  "(vptr :: word32)  >> 20 < 2 ^ pageBits"
  apply (rule le_less_trans[rotated])
   apply (rule and_mask_less' [where w=max_word])
   apply (simp add: pageBits_def)
  apply (rule word_leI)
  apply (simp add: word_size nth_shiftr)
  apply (drule test_bit_size)
  apply (simp add: pageBits_def word_size)
  done

lemma page_directory_pde_at_lookupI:
  "\<lbrakk>page_directory_at pd s; pspace_aligned s\<rbrakk> \<Longrightarrow> pde_at (lookup_pd_slot pd vptr) s"
  apply (simp add: lookup_pd_slot_def Let_def)
  apply (erule (1) page_directory_pde_atI[rotated 2])
  apply (rule vptr_shiftr_le_2p)
  done

lemma vptr_shiftr_le_2pt:
  "((vptr :: word32) >> 12) && 0xFF < 2 ^ (pt_bits - 2)"
  apply (clarsimp simp: word_FF_is_mask pt_bits_def pageBits_def)
  apply (rule and_mask_less_size[where n=8, simplified])
  apply (clarsimp simp: word_size)
  done

lemma page_table_pte_at_lookupI:
  "\<lbrakk>page_table_at pt s; pspace_aligned s\<rbrakk> \<Longrightarrow> pte_at (lookup_pt_slot_no_fail pt vptr) s"
  apply (simp add: lookup_pt_slot_no_fail_def)
  apply (erule (1) page_table_pte_atI[rotated 2])
  apply (rule vptr_shiftr_le_2pt)
  done

lemmas lookup_pt_slot_ptes[wp] =
 lookup_pt_slot_ptes_aligned_valid
   [@ \<open>post_asm \<open>thin_tac "is_aligned x y" for x y\<close>\<close>]

lemmas lookup_pt_slot_ptes2[wp] =
 lookup_pt_slot_ptes_aligned_valid
   [@ \<open>post_asm \<open>drule (1) p_0x3C_shift[THEN iffD2], thin_tac _\<close>\<close>]


lemma create_mapping_entries_valid [wp]:
  "\<lbrace>pspace_aligned and valid_arch_state and valid_vspace_objs
   and equal_kernel_mappings and valid_global_objs
   and \<exists>\<rhd> pd and page_directory_at pd and
    K ((sz = ARMLargePage \<longrightarrow> is_aligned vptr 16) \<and>
       (sz = ARMSuperSection \<longrightarrow> is_aligned vptr 24)) \<rbrace>
  create_mapping_entries base vptr sz vm_rights attrib pd
  \<lbrace>\<lambda>m. valid_mapping_entries m\<rbrace>, -"
  apply (cases sz)
     apply (rule hoare_pre)
      apply (wp|simp add: valid_mapping_entries_def largePagePTE_offsets_def)+
   apply clarsimp
   apply (erule (1) page_directory_pde_at_lookupI)
  apply (rule hoare_pre)
   apply (clarsimp simp add: valid_mapping_entries_def)
   apply wp
  apply (simp add: lookup_pd_slot_def Let_def)
  apply (prop_tac "is_aligned pd 14")
   apply (clarsimp simp: obj_at_def add.commute invs_def valid_state_def valid_pspace_def pspace_aligned_def)
   apply (drule bspec, blast)
   apply (clarsimp simp: a_type_def split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (clarsimp simp: superSectionPDE_offsets_def)
  apply (clarsimp simp: upto_enum_step_def word_shift_by_2)
  apply (clarsimp simp: pde_at_def)
  apply (simp add: add.commute add.left_commute)
  apply (subst add_mask_lower_bits)
    apply (simp add: pd_bits_def pageBits_def)
   apply (clarsimp simp: pd_bits_def pageBits_def)
   apply (subst (asm) word_plus_and_or_coroll)
    prefer 2
    apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth p_le_0xF_helper word_bits_def)
    apply (drule test_bit_size)+
    apply (simp add: word_size)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth p_le_0xF_helper word_bits_def)
   apply (frule_tac w=vptr in test_bit_size)
   apply (simp add: word_size)
   apply (thin_tac "All _")
   subgoal for \<dots> n
     apply (spec "18+n")
     by simp
  apply (clarsimp simp: a_type_simps)
  apply (rule aligned_add_aligned is_aligned_shiftl_self
                 | simp add: word_bits_conv)+
  done


lemma set_pt_distinct [wp]:
  "set_pt p pt \<lbrace>pspace_distinct\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp: obj_at_def a_type_def pspace_distinct_same_type
                 split: kernel_object.splits arch_kernel_obj.splits if_splits)
  done


lemma set_pd_distinct [wp]:
  "set_pd p pd \<lbrace>pspace_distinct\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_distinct[THEN hoare_set_object_weaken_pre] get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  done


lemma store_pte_valid_objs [wp]:
  "\<lbrace>(%s. wellformed_pte pte) and valid_objs\<rbrace> store_pte p pte \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: store_pte_def set_pt_def get_pt_def bind_assoc set_object_def get_object_def)
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply (clarsimp simp: valid_objs_def dom_def simp del: fun_upd_apply)
  subgoal for \<dots> ptr _
  apply (rule valid_obj_same_type)
     apply (cases "ptr = p && ~~ mask pt_bits")
      apply (erule allE, erule impE, blast)
      apply (clarsimp simp: valid_obj_def arch_valid_obj_def)
     apply clarsimp
     apply fastforce
    apply (erule allE, erule impE, blast)
    apply (clarsimp simp: valid_obj_def arch_valid_obj_def)
   apply assumption
  by (simp add: a_type_def)
  done


lemma set_pt_caps_of_state [wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def a_type_simps)
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  apply (auto simp: cte_wp_at_cases a_type_def)
  done


lemma set_pd_caps_of_state [wp]:
  "set_pd p pd \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_pd_def bind_assoc)
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def)
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  by (case_tac ko; simp add: cte_wp_at_cases a_type_simps split: if_splits)


lemma store_pte_aligned [wp]:
  "store_pte pt p \<lbrace>pspace_aligned\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp set_object_aligned)
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma store_pde_valid_objs [wp]:
  "\<lbrace>(%s. wellformed_pde pde) and valid_objs\<rbrace> store_pde p pde \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: store_pde_def set_pd_def get_pd_def bind_assoc set_object_def get_object_def)
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply (clarsimp simp: valid_objs_def dom_def simp del: fun_upd_apply)
  subgoal for \<dots> ptr _
  apply (rule valid_obj_same_type)
     apply (cases "ptr = p && ~~ mask pd_bits")
      apply (erule allE, erule impE, blast)
      apply (clarsimp simp: valid_obj_def arch_valid_obj_def)
     apply clarsimp
     apply fastforce
    apply (erule allE, erule impE, blast)
    apply (clarsimp simp: valid_obj_def arch_valid_obj_def)
   apply assumption
  by (simp add: a_type_def)
  done


lemma set_asid_pool_aligned [wp]:
  "set_asid_pool p ptr \<lbrace>pspace_aligned\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  apply (wpsimp wp: set_object_wp_strong pspace_aligned_obj_update[rotated])
  done


lemma set_asid_pool_distinct [wp]:
  "set_asid_pool p ptr \<lbrace>pspace_distinct\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  by (wpsimp wp: set_object_wp_strong pspace_distinct_same_type)


lemma store_pde_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> store_pde p pde \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  by (simp add: store_pde_def set_pd_def get_object_def) wpsimp


lemma store_pte_valid_pte [wp]:
  "\<lbrace>valid_pte pt\<rbrace> store_pte p pte \<lbrace>\<lambda>_. valid_pte pt\<rbrace>"
  by (wp valid_pte_lift store_pte_typ_at)


lemma store_pde_valid_pde [wp]:
  "\<lbrace>valid_pde pde\<rbrace> store_pde slot pde' \<lbrace>\<lambda>rv. valid_pde pde\<rbrace>"
  by (wp valid_pde_lift store_pde_typ_at)


lemma set_pd_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_pd ptr pd \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_pd_def)
  by (wpsimp wp: set_object_wp_strong simp: obj_at_def)


lemma set_pd_valid_objs:
  "\<lbrace>(%s. \<forall>i. wellformed_pde (pd i)) and valid_objs\<rbrace>
   set_pd p pd
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_pd_def)
  by (wpsimp wp: set_object_valid_objs simp: valid_obj_def)


lemma set_pd_iflive:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (subst set_pd_def)
  including unfold_objects
  by (wpsimp wp: set_object_iflive[THEN hoare_set_object_weaken_pre]
           simp: live_def hyp_live_def a_type_def)


lemma set_pd_zombies:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (subst set_pd_def)
  apply (wp set_object_zombies[THEN hoare_set_object_weaken_pre])
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_pd_zombies_state_refs:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (subst set_pd_def)
  including unfold_objects
  apply (wpsimp wp: set_object_wp_strong
              simp: a_type_def)
  apply (erule rsubst [where P=P], rule ext)
  apply (simp add: state_refs_of_def)
  done

lemma set_pd_zombies_state_hyp_refs:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  apply (subst set_pd_def)
  including unfold_objects
  apply (wpsimp wp: set_object_wp_strong
              simp: a_type_def)
  apply (erule rsubst [where P=P], rule ext)
  apply (simp add: state_hyp_refs_of_def)
  done

lemma set_pd_cdt:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> set_pd p pd \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_pd_def by (wpsimp wp: get_object_wp)


lemma set_pd_valid_mdb:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  apply (rule valid_mdb_lift)
  by (wpsimp wp: set_pd_cdt set_object_wp simp: set_pd_def)+

lemma set_pd_valid_idle:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace> set_pd p pd \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  by (wpsimp simp: set_pd_def)

lemma set_pd_ifunsafe:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  unfolding set_pd_def including unfold_objects
  by (wpsimp wp: set_object_ifunsafe[THEN hoare_set_object_weaken_pre]
           simp: a_type_def)


lemma global_refs_kheap [simp]:
  "global_refs (kheap_update f s) = global_refs s"
  by (simp add: global_refs_def)

crunches set_pd
  for global_ref [wp]: "\<lambda>s. P (global_refs s)"
  and arch [wp]: "\<lambda>s. P (arch_state s)"
  and idle [wp]: "\<lambda>s. P (idle_thread s)"
  and irq [wp]: "\<lambda>s. P (interrupt_irq_node s)"
    (wp: crunch_wps)

lemma set_pd_valid_global:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


lemma set_pd_valid_arch:
  "\<lbrace>\<lambda>s. valid_arch_state s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. valid_arch_state s\<rbrace>"
  by (wp valid_arch_state_lift)


lemma set_pd_cur:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  apply (simp add: cur_tcb_def set_pd_def)
  including unfold_objects
  apply (wpsimp wp: set_object_wp_strong simp: a_type_simps)
  apply (simp add: is_tcb_def)
  done

lemma set_pd_cur_sc_tcb:
  "set_pd p pd \<lbrace>cur_sc_tcb\<rbrace>"
  by (wpsimp simp: set_pd_def set_object_def get_object_def cur_sc_tcb_def sc_tcb_sc_at_def
                   obj_at_def a_type_simps)

crunch interrupt_states[wp]: set_pd "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)


lemma set_pd_vspace_objs_unmap:
  "\<lbrace>valid_vspace_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd') s) and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd')) \<subseteq> vs_refs ko) p\<rbrace>
  set_pd p pd' \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wpsimp wp: set_object_vspace_objs[THEN hoare_set_object_weaken_pre])
  including unfold_objects
  apply (clarsimp simp: a_type_def)
  done

declare graph_of_None_update[simp]
declare graph_of_Some_update[simp]


lemma set_pt_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_pt ptr pt \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_pt_def)
  by (wpsimp wp: set_object_wp_strong simp: obj_at_def)


lemma set_pt_valid_objs:
  "\<lbrace>(%s. \<forall>i. wellformed_pte (pt i)) and valid_objs\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_valid_objs)
  apply (clarsimp split: kernel_object.splits
                         arch_kernel_obj.splits)
  apply (clarsimp simp: valid_obj_def obj_at_def a_type_def
                        arch_valid_obj_def)
  done


lemma set_pt_iflive:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  unfolding set_pt_def including unfold_objects
  apply (wpsimp wp: set_object_iflive[THEN hoare_set_object_weaken_pre]
              simp: live_def hyp_live_def a_type_def)
  done


lemma set_pt_zombies:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  unfolding set_pt_def including unfold_objects
  apply (wpsimp wp: set_object_zombies[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  done


lemma set_pt_zombies_state_refs:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  unfolding set_pt_def including unfold_objects
  apply (wpsimp wp: set_object_wp_strong simp: a_type_def)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: state_refs_of_def)
  done

lemma set_pt_zombies_state_hyp_refs:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding set_pt_def including unfold_objects
  apply (wpsimp wp: set_object_wp_strong simp: a_type_def)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: state_hyp_refs_of_def)
  done

lemma set_pt_cdt:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_pt_def including unfold_objects by wpsimp


lemma set_pt_valid_mdb:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: set_pt_cdt valid_mdb_lift simp: set_pt_def set_object_def)

lemma set_pt_valid_idle:
  "set_pt p pt \<lbrace>valid_idle\<rbrace>"
  by (wpsimp simp: set_pt_def)

lemma set_pt_ifunsafe:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  including unfold_objects by (wpsimp wp: set_object_ifunsafe[THEN hoare_set_object_weaken_pre]
                                    simp: set_pt_def a_type_def)

crunches set_pt
  for global_ref [wp]: "\<lambda>s. P (global_refs s)"
  and arch [wp]: "\<lambda>s. P (arch_state s)"
  and idle [wp]: "\<lambda>s. P (idle_thread s)"
  and irq [wp]: "\<lambda>s. P (interrupt_irq_node s)"
    (wp: crunch_wps)

lemma set_pt_valid_global:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


lemma set_pt_valid_arch_state[wp]:
  "\<lbrace>\<lambda>s. valid_arch_state s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_arch_state s\<rbrace>"
  by (wp valid_arch_state_lift)


lemma set_pt_cur:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  unfolding set_pt_def cur_tcb_def including unfold_objects
  by (wpsimp wp: set_object_wp_strong simp: a_type_def is_tcb)

lemma set_pt_cur_sc_tcb:
  "set_pt p pt \<lbrace>cur_sc_tcb\<rbrace>"
  by (wpsimp simp: set_pt_def cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def a_type_simps
             wp: set_object_wp_strong
             split: if_split_asm)

lemma set_pt_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_pt p pt \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp wp: set_object_aligned[THEN hoare_set_object_weaken_pre])

crunch interrupt_states[wp]: set_pt "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)


lemma set_pt_vspace_objs [wp]:
  "\<lbrace>valid_vspace_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (PageTable pt) s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding set_pt_def including unfold_objects
  apply (wpsimp wp: set_object_vspace_objs[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  by (simp add: vs_refs_def)


lemma set_pt_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> set_pt p pt \<lbrace>\<lambda>x s. P (vs_lookup s)\<rbrace>"
  unfolding set_pt_def including unfold_objects
  apply (wpsimp wp: set_object_wp_strong simp: a_type_def)
  apply (erule rsubst [where P=P])
  apply (rule order_antisym)
   apply (rule vs_lookup_sub)
    apply (clarsimp simp: vs_refs_def)
    prefer 3
    apply (rule vs_lookup_sub)
     apply (clarsimp simp: vs_refs_def split: if_split_asm)
      apply blast+
    apply auto
  done


lemma store_pte_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> store_pte x pte \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  unfolding store_pte_def by wpsimp


lemma unique_table_caps_ptD:
  "\<lbrakk> cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; is_pt_cap cap; is_pt_cap cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs\<rbrakk>
  \<Longrightarrow> p = p'"
  by (fastforce simp add: unique_table_caps_def)


lemma unique_table_caps_pdD:
  "\<lbrakk> cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; is_pd_cap cap; is_pd_cap cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs\<rbrakk>
  \<Longrightarrow> p = p'"
  by (fastforce simp add: unique_table_caps_def)


lemma valid_objs_caps:
  "valid_objs s \<Longrightarrow> valid_caps (caps_of_state s) s"
  apply (clarsimp simp: valid_caps_def)
  apply (erule (1) caps_of_state_valid_cap)
  done


lemma simpler_set_pt_def:
  "set_pt p pt =
   (\<lambda>s. if \<exists>pt. kheap s p = Some (ArchObj (PageTable pt)) then
           ({((), s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (PageTable pt))\<rparr>)}, False)
        else ({}, True))"
  apply (rule ext)
  apply (clarsimp simp: set_pt_def set_object_def get_object_def assert_def read_object_def assert_opt_def
                        put_def get_def simpler_gets_def bind_def return_def fail_def gets_the_def
                 split: option.split)
  apply (rule conjI)
   apply (clarsimp simp: set_pt_def set_object_def get_object_def assert_def
                         put_def get_def simpler_gets_def bind_def
                         return_def fail_def a_type_def
                  split: kernel_object.splits
                         arch_kernel_obj.splits)
  using a_type_def aa_type_APageTableE apply fastforce
  done


lemma valid_set_ptI:
  "(!!s opt. \<lbrakk>P s; kheap s p = Some (ArchObj (PageTable opt))\<rbrakk>
         \<Longrightarrow> Q () (s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (PageTable pt))\<rparr>))
   \<Longrightarrow> \<lbrace>P\<rbrace> set_pt p pt \<lbrace>Q\<rbrace>"
  by (rule validI) (clarsimp simp: simpler_set_pt_def split: if_split_asm)

lemma set_pt_table_caps [wp]:
  "\<lbrace>valid_table_caps and (\<lambda>s. valid_caps (caps_of_state s) s) and
    (\<lambda>s. ((\<exists>slot. caps_of_state s slot =
                 Some (ArchObjectCap (PageTableCap p None))) \<longrightarrow>
          pt = (\<lambda>x. InvalidPTE)) \<or>
         (\<forall>slot. \<exists>asid. caps_of_state s slot =
             Some (ArchObjectCap (PageTableCap p (Some asid)))))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def
  apply (rule valid_set_ptI)
  apply (intro allI impI, simp add: obj_at_def del: HOL.imp_disjL)
  apply (cut_tac s=s and val= "ArchObj (PageTable pt)" and p=p
              in caps_of_state_after_update[folded fun_upd_def])
   apply (simp add: obj_at_def)
  apply (clarsimp simp del: HOL.imp_disjL)
  apply (thin_tac "ALL x. P x" for P)
  apply (case_tac cap, simp_all add: is_pd_cap_def is_pt_cap_def)
  apply (erule disjE)
   apply (simp add: valid_caps_def)
   apply ((drule spec)+, erule impE, assumption)
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap,
          simp_all add: valid_cap_def obj_at_def aa_type_simps)
  apply clarsimp
  apply (erule impE, fastforce simp: cap_asid_def split: option.splits)
  apply (erule disjE, simp add: empty_table_def)
  apply (drule_tac x=a in spec, drule_tac x=b in spec)
  apply (clarsimp simp add: cap_asid_def split: option.splits)
  done


lemma set_object_caps_of_state:
  "\<lbrace>(\<lambda>s. \<not>(tcb_at p s) \<and> \<not>(\<exists>n. cap_table_at n p s)) and
    K ((\<forall>x y. obj \<noteq> CNode x y) \<and> (\<forall>x. obj \<noteq> TCB x)) and
    (\<lambda>s. P (caps_of_state s))\<rbrace>
   set_object p obj
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong)
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (simp add: caps_of_state_cte_wp_at obj_at_def is_cap_table_def
                   is_tcb_def)
  apply (auto simp: cte_wp_at_cases)
  done

lemma set_pt_valid_vspace_objs[wp]:
  "valid (\<lambda>s. valid_vspace_objs s \<and> ((\<exists>\<rhd> p) s \<longrightarrow> (\<forall>x. valid_pte (pt x) s)))
             (set_pt p pt) (\<lambda>_. valid_vspace_objs)"
  apply (rule valid_set_ptI)
  apply (clarsimp simp: valid_vspace_objs_def)
  subgoal for s opt pa rs ao
    apply (spec pa)
    apply (prop_tac "(\<exists>\<rhd> pa) s")
     apply (rule exI[where x=rs])
     apply (erule vs_lookupE)
     apply clarsimp
     apply (erule vs_lookupI)
     apply (erule rtrancl.induct, simp)
     subgoal for \<dots> b c
       apply (prop_tac "(b \<rhd>1 c) s")
       apply (thin_tac "_ : rtrancl _")+
       apply (clarsimp simp add: vs_lookup1_def obj_at_def vs_refs_def
                            split: if_split_asm)
       by simp
    apply simp
    apply (spec ao)
    apply (cases "pa = p")
     apply (clarsimp simp: obj_at_def)
     subgoal for _ x
       apply (drule_tac x=x in spec)
       by (cases "pt x"; clarsimp simp: data_at_def obj_at_def a_type_simps)
    apply (cases ao; simp add: obj_at_def a_type_simps)
      apply clarsimp
      apply (drule bspec, assumption, clarsimp)
     apply clarsimp
     subgoal for "fun" _ x
       apply (spec x)
       by (cases "fun x"; clarsimp simp: obj_at_def data_at_def a_type_simps)
    apply clarsimp
    apply (drule bspec,fastforce)
    subgoal for "fun" x
      by (cases "fun x"; clarsimp simp: data_at_def obj_at_def a_type_simps)
    done
  done


lemma set_pt_valid_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. valid_vs_lookup s \<and> valid_arch_state s \<and>
        valid_vspace_objs s \<and> ((\<exists>\<rhd> p) s \<longrightarrow> (\<forall>x. valid_pte (pt x) s)) \<and>
        (\<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
            (\<forall>x p. pte_ref_pages (pt x) = Some p \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         p \<in> obj_refs cap \<and>
                         vs_cap_ref cap =
                         Some (VSRef (ucast x) (Some APageTable) # ref))))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_vs_lookup\<rbrace>"
  using set_pt_valid_vspace_objs[of p pt] set_pt_valid_arch_state[of p pt]
  apply (clarsimp simp: valid_def simpler_set_pt_def)
  apply (drule_tac x=s in spec)+
  apply (clarsimp simp: valid_vs_lookup_def  split: if_split_asm)
  apply (erule (1) vs_lookup_pagesE_alt)
      apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                            fun_upd_def)
     apply (drule_tac x=pa in spec)
     apply (drule_tac x="[VSRef (ucast a) None]" in spec)+
     apply simp
     apply (drule vs_lookup_pages_atI)
     apply simp
     apply (subst caps_of_state_after_update, simp add: obj_at_def)
     apply simp
    apply (drule_tac x=pa in spec)
    apply (drule_tac x="[VSRef (ucast b) (Some AASIDPool),
                         VSRef (ucast a) None]" in spec)+
    apply simp
    apply (drule vs_lookup_pages_apI)
      apply (simp split: if_split_asm)
     apply simp+
    apply (subst caps_of_state_after_update, simp add: obj_at_def)
    apply simp
   apply (drule_tac x=pa in spec)
   apply (drule_tac x="[VSRef (ucast c) (Some APageDirectory),
                        VSRef (ucast b) (Some AASIDPool),
                        VSRef (ucast a) None]" in spec)+
   apply simp
   apply (drule vs_lookup_pages_pdI)
        apply (simp split: if_split_asm)+
   apply (subst caps_of_state_after_update, simp add: obj_at_def)
   apply fastforce
  apply (clarsimp simp: fun_upd_def  split: if_split_asm)
   apply (thin_tac "valid_vspace_objs s" for s, thin_tac "valid_arch_state s" for s)
   apply (subst caps_of_state_after_update, simp add: obj_at_def)
   apply (thin_tac "\<forall>p ref. P p ref" for P)
   apply (drule_tac x="[VSRef (ucast c) (Some APageDirectory),
                        VSRef (ucast b) (Some AASIDPool),
                        VSRef (ucast a) None]" in spec)
   apply (thin_tac "valid_pte pte s" for pte s)
   apply (erule impE, fastforce intro: vs_lookup_pdI)
   apply (drule_tac x=d in spec)
   apply (erule impE)
    apply (erule (5) vs_lookup_pdI[THEN vs_lookup_pages_vs_lookupI])
   apply (drule spec, drule spec, erule impE, assumption)
   apply assumption
  apply (thin_tac "valid_vspace_objs s" for s, thin_tac "valid_arch_state s" for s)
  apply (subst caps_of_state_after_update, simp add: obj_at_def)
  apply (thin_tac "\<forall>ref. (ref \<unrhd> p) s \<longrightarrow> P ref" for P)
  apply (drule_tac x=pa in spec)
  apply (drule_tac x="[VSRef (ucast d) (Some APageTable),
                       VSRef (ucast c) (Some APageDirectory),
                       VSRef (ucast b) (Some AASIDPool),
                       VSRef (ucast a) None]" in spec)
  apply (thin_tac "(\<exists>\<rhd> p) s \<longrightarrow> P" for P)
  apply (erule impE, fastforce intro: vs_lookup_pages_ptI)
  apply simp
  done


lemma set_pt_arch_caps [wp]:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_vspace_objs and
    (\<lambda>s. valid_caps (caps_of_state s) s) and
    (\<lambda>s. ((\<exists>slot. caps_of_state s slot =
                 Some (ArchObjectCap (PageTableCap p None))) \<longrightarrow>
          pt = (\<lambda>x. InvalidPTE)) \<or>
         (\<forall>slot. \<exists>asid. caps_of_state s slot =
           Some (ArchObjectCap (PageTableCap p (Some asid))))) and
    (\<lambda>s. ((\<exists>\<rhd> p) s \<longrightarrow> (\<forall>x. valid_pte (pt x) s)) \<and>
         (\<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
            (\<forall>x p. pte_ref_pages (pt x) = Some p \<longrightarrow>
                   (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                        p \<in> obj_refs cap \<and>
                        vs_cap_ref cap =
                        Some (VSRef (ucast x) (Some APageTable) # ref)))))\<rbrace>
  set_pt p pt \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding valid_arch_caps_def
  apply (rule hoare_pre)
   apply (wp set_pt_valid_vs_lookup)
  apply clarsimp
  done


lemma valid_global_refsD2:
  "\<lbrakk> caps_of_state s ptr = Some cap; valid_global_refs s \<rbrakk>
      \<Longrightarrow> global_refs s \<inter> cap_range cap = {}"
  by (cases ptr,
      simp add: valid_global_refs_def valid_refs_def
                cte_wp_at_caps_of_state)


lemma valid_global_refsD:
  "\<lbrakk> valid_global_refs s; cte_wp_at ((=) cap) ptr s;
         r \<in> global_refs s \<rbrakk>
        \<Longrightarrow> r \<notin> cap_range cap"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) valid_global_refsD2)
  apply fastforce
  done

lemma set_pt_global_objs [wp]:
  "\<lbrace>valid_global_objs and valid_arch_state and
    (\<lambda>s. p \<in> set (arm_global_pts (arch_state s)) \<longrightarrow>
         (\<forall>x. aligned_pte (pt x)))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (rule valid_set_ptI)
  apply (clarsimp simp: valid_global_objs_def valid_arch_state_def valid_vspace_obj_def
                        valid_vso_at_def obj_at_def empty_table_def)
  done


crunch v_ker_map[wp]: set_pt "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_pt_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: valid_asid_map_def vspace_at_asid_def)
  apply (rule hoare_lift_Pf2 [where f="arch_state"])
   apply wp+
  done


lemma set_pt_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_pt p pt \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)


lemma set_pt_equal_mappings [wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (simp add: set_pt_def | wp set_object_equal_mappings get_object_wp)+


lemma set_pt_valid_global_vspace_mappings:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_objs s \<and> p \<notin> global_refs s\<rbrace>
      set_pt p pt
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp wp: set_object_global_vspace_mappings)


lemma set_pt_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp wp: set_object_pspace_in_kernel_window[THEN hoare_set_object_weaken_pre])

lemma set_pt_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp wp: set_object_pspace_respects_device_region[THEN hoare_set_object_weaken_pre])

lemma set_pt_caps_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp wp: set_object_cap_refs_in_kernel_window[THEN hoare_set_object_weaken_pre]
           simp: a_type_def)

lemma set_pt_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp wp: set_object_cap_refs_respects_device_region[THEN hoare_set_object_weaken_pre]
           simp: a_type_def)

lemma set_pt_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp wp: set_object_valid_ioc_no_caps[THEN hoare_set_object_weaken_pre]
           simp: is_tcb is_cap_table)


lemma valid_machine_stateE:
  assumes vm: "valid_machine_state s"
  assumes e: "\<lbrakk>in_user_frame p s
    \<or> underlying_memory (machine_state s) p = 0 \<rbrakk> \<Longrightarrow> E "
  shows E
  using vm
  apply (clarsimp simp: valid_machine_state_def)
  apply (drule_tac x = p in spec)
  apply (rule e)
  apply auto
  done

lemma in_user_frame_same_type_upd:
  "\<lbrakk>typ_at type p s; type = a_type obj; in_user_frame q s\<rbrakk>
    \<Longrightarrow> in_user_frame q (s\<lparr>kheap := kheap s(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: in_user_frame_def obj_at_def)
  apply (rule_tac x=sz in exI)
  apply (auto simp: a_type_simps)
  done

lemma in_device_frame_same_type_upd:
  "\<lbrakk>typ_at type p s; type = a_type obj ; in_device_frame q s\<rbrakk>
    \<Longrightarrow> in_device_frame q (s\<lparr>kheap := kheap s(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: in_device_frame_def obj_at_def)
  apply (rule_tac x=sz in exI)
  apply (auto simp: a_type_simps)
  done

lemma store_word_offs_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> store_word_offs a x w \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma store_word_offs_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> store_word_offs a x w \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)


lemma as_user_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> as_user t m \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma as_user_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> as_user t m \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)

crunch obj_at[wp]: load_word_offs "\<lambda>s. P (obj_at Q p s)"

lemma load_word_offs_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> load_word_offs a x \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma valid_machine_state_heap_updI:
assumes vm : "valid_machine_state s"
assumes tyat : "typ_at type p s"
shows
  " a_type obj = type \<Longrightarrow> valid_machine_state (s\<lparr>kheap := kheap s(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: valid_machine_state_def)
  subgoal for p
   apply (rule valid_machine_stateE[OF vm,where p = p])
   apply (elim disjE,simp_all)
   apply (drule(1) in_user_frame_same_type_upd[OF tyat])
    apply simp+
   done
  done

lemma set_pt_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding set_pt_def including unfold_objects
  apply (wpsimp wp: set_object_wp_strong simp: a_type_def)
  apply (erule valid_machine_state_heap_updI)
   apply (fastforce simp: a_type_simps)+
  done

crunch valid_irq_states[wp]: set_pt "valid_irq_states"
  (wp: crunch_wps)

crunch valid_irq_states[wp]: set_pd "valid_irq_states"
  (wp: crunch_wps)

lemma set_pt_reply_at_ppred[wp]:
  "set_pt p pt \<lbrace> \<lambda>s. P (reply_at_pred P' r s) \<rbrace>"
  by (wpsimp simp: set_pt_def wp: set_object_wp_strong get_object_wp)
     (fastforce elim!: bool_to_boolE[of P]
                 simp: obj_at_def reply_at_ppred_def
                split: kernel_object.splits if_splits)

sublocale set_pt: non_reply_op "set_pt p pt"
  by unfold_locales wp

lemma set_pt_sc_at_pred_n[wp]:
  "set_pt p pt \<lbrace> \<lambda>s. P (sc_at_pred_n N (\<lambda>sc. sc) P' r s) \<rbrace>"
  by (wpsimp simp: set_pt_def wp: set_object_wp_strong get_object_wp)
     (fastforce elim!: bool_to_boolE[of P]
                 simp: obj_at_def sc_at_pred_n_def a_type_simps
                split: kernel_object.splits if_splits)

sublocale set_pt: non_sc_op "set_pt p pt"
  by unfold_locales wp

lemma set_pt_valid_replies[wp]:
  "set_pt p pt \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

lemma set_pt_fault_tcbs_valid_states[wp]:
  "set_pt p pt \<lbrace> fault_tcbs_valid_states \<rbrace>"
  by (wpsimp wp: fault_tcbs_valid_states_lift)

lemma set_pt_invs:
  "\<lbrace>invs and (\<lambda>s. \<forall>i. wellformed_pte (pt i)) and
    (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (PageTable pt) s) and
    (\<lambda>s. \<exists>slot asid. caps_of_state s slot =
         Some (cap.ArchObjectCap (arch_cap.PageTableCap p asid)) \<and>
         (pt = (\<lambda>x. InvalidPTE) \<or> asid \<noteq> None)) and
    (\<lambda>s. \<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
            (\<forall>x p. pte_ref_pages (pt x) = Some p \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         p \<in> obj_refs cap \<and>
                         vs_cap_ref cap =
                         Some (VSRef (ucast x) (Some APageTable) # ref))))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_pt_valid_objs set_pt_iflive set_pt_zombies
             set_pt_zombies_state_refs set_pt_zombies_state_hyp_refs set_pt_valid_mdb
             set_pt_valid_idle set_pt_ifunsafe
             set_pt_valid_arch_state set_pt_valid_global set_pt_cur set_pt_cur_sc_tcb
             valid_irq_node_typ
             valid_irq_handlers_lift
             set_pt_valid_global_vspace_mappings)
  apply (clarsimp dest!: valid_objs_caps)
  apply (rule conjI[rotated])
  apply (subgoal_tac "p \<notin> global_refs s", simp add: global_refs_def)
  apply (frule (1) valid_global_refsD2)
  apply (clarsimp simp add: cap_range_def is_pt_cap_def)
  apply (thin_tac "ALL x. P x" for P)+
  apply (clarsimp simp: valid_arch_caps_def unique_table_caps_def)
  apply (drule_tac x=aa in spec, drule_tac x=ba in spec)
  apply (drule_tac x=a in spec, drule_tac x=b in spec)
  apply (clarsimp simp: is_pt_cap_def cap_asid_def)
  done


lemma vs_lookup_pages_pt_eq:
  "\<lbrakk>valid_vspace_objs s;
    \<forall>p\<in>ran (arm_asid_table (arch_state s)). asid_pool_at p s;
    page_table_at p s\<rbrakk>
   \<Longrightarrow> (ref \<unrhd> p) s = (ref \<rhd> p) s"
  apply (rule iffI[rotated])
   apply (erule vs_lookup_pages_vs_lookupI)
  apply (erule (2) vs_lookup_pagesE_alt)
     apply (clarsimp simp: obj_at_def)+
   apply (clarsimp simp: obj_at_def pde_ref_pages_def
                  split: pde.splits)
   apply (erule (5) vs_lookup_pdI)
  apply (auto simp: obj_at_def pte_ref_pages_def data_at_def
                 split: pte.splits)
  done

(* NOTE: we use vs_lookup in the precondition because in this case,
         both are equivalent, but vs_lookup is generally preserved
         by store_pte while vs_lookup_pages might not. *)
lemma store_pte_invs [wp]:
  "\<lbrace>invs and (\<lambda>s. (\<exists>\<rhd>(p && ~~ mask pt_bits)) s \<longrightarrow> valid_pte pte s) and
    (\<lambda>s. wellformed_pte pte) and
    (\<lambda>s. \<exists>slot asid. caps_of_state s slot =
         Some (ArchObjectCap
                 (PageTableCap (p && ~~ mask pt_bits) asid)) \<and>
         (pte = InvalidPTE \<or> asid \<noteq> None)) and
    (\<lambda>s. \<forall>ref. (ref \<rhd> (p && ~~ mask pt_bits)) s \<longrightarrow>
            (\<forall>q. pte_ref_pages pte = Some q \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         q \<in> obj_refs cap \<and>
                         vs_cap_ref cap =
                         Some (VSRef (p && mask pt_bits >> 2)
                                     (Some APageTable) # ref))))\<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pte_def)
  apply (wp dmo_invs set_pt_invs)
  apply clarsimp
  apply (intro conjI)
     apply (drule invs_valid_objs)
     apply (fastforce simp: valid_objs_def dom_def obj_at_def valid_obj_def arch_valid_obj_def)
    apply clarsimp
    apply (drule (1) valid_vspace_objsD, fastforce)
    apply simp
   apply (thin_tac "All _")
   apply (rule exI)+
   apply (rule conjI, assumption)
   subgoal premises prems for \<dots> asid
   proof (cases asid)
    case (Some a) from this show ?thesis
     by fastforce
    next
    case None from this prems show ?thesis
     apply clarsimp
     apply (rule ext)
     apply clarsimp
     apply (frule invs_pd_caps)
     apply (clarsimp simp add: valid_table_caps_def simp del: HOL.imp_disjL)
     apply (spec "p && ~~ mask pt_bits")
     apply (drule spec)+
     apply (erule impE, assumption)
     by (simp add: is_pt_cap_def cap_asid_def empty_table_def obj_at_def)
  qed
  apply (clarsimp simp: obj_at_def)
  apply (intro impI conjI allI)
   apply (drule (2) vs_lookup_pages_pt_eq[OF invs_vspace_objs invs_ran_asid_table,
                                          THEN iffD1, rotated -1])
    apply (clarsimp simp: obj_at_def a_type_simps)
   apply (drule spec, erule impE, assumption)+
   apply (erule exEI)+
   apply clarsimp
   apply (rule sym)
   apply (rule ucast_ucast_len)
   apply (rule shiftr_less_t2n)
   using and_mask_less'[of 10 p]
   apply (simp add: pt_bits_def pageBits_def)
  subgoal for \<dots> pa
   apply (thin_tac "All _", thin_tac "_ \<longrightarrow> _", thin_tac "_ \<or> _")
   apply (frule invs_valid_vs_lookup)
   apply (simp add: valid_vs_lookup_def)
   apply (spec pa)
   apply (drule spec, erule impE)
    apply (erule vs_lookup_pages_step)
    by (fastforce simp: vs_lookup_pages1_def obj_at_def
                          vs_refs_pages_def graph_of_def image_def) simp
  done


lemma set_asid_pool_iflive [wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  including unfold_objects
  by (wpsimp wp: set_object_iflive[THEN hoare_set_object_weaken_pre]
           simp: a_type_def live_def hyp_live_def)


lemma set_asid_pool_zombies [wp]:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by (wpsimp wp: set_object_zombies[THEN hoare_set_object_weaken_pre]
           simp: a_type_def)


lemma set_asid_pool_zombies_state_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  apply (wpsimp wp: set_object_wp_strong
              simp: a_type_def)
  apply (erule rsubst [where P=P], rule ext)
  apply (clarsimp simp: state_refs_of_def)
  done

lemma set_asid_pool_zombies_state_hyp_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  apply (wpsimp wp: set_object_wp_strong
              simp: a_type_def)
  apply (erule rsubst [where P=P], rule ext)
  apply (simp add: state_hyp_refs_of_def)
  done

lemma set_asid_pool_cdt [wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by wpsimp

lemma set_asid_pool_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  apply (wpsimp wp: set_object_wp_strong
              simp: a_type_def)
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  apply (clarsimp simp: cte_wp_at_cases)
  done


lemma set_asid_pool_valid_mdb [wp]:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_mdb_lift simp: set_asid_pool_def set_object_def)


lemma set_asid_pool_valid_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  by (wpsimp simp: set_asid_pool_def set_object_def get_object_def obj_at_def a_type_simps
             wp: valid_idle_lift)


lemma set_asid_pool_ifunsafe [wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by (wpsimp wp: set_object_ifunsafe[THEN hoare_set_object_weaken_pre]
           simp: a_type_def)


crunch global_ref [wp]: set_asid_pool "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)


crunch idle [wp]: set_asid_pool "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)


crunch irq [wp]: set_asid_pool "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

crunch valid_irq_states[wp]: set_asid_pool "valid_irq_states"
  (wp: crunch_wps)

lemma set_asid_pool_valid_global [wp]:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


crunch interrupt_states[wp]: set_asid_pool "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

lemma set_asid_pool_vspace_objs_unmap':
  "\<lbrace>valid_vspace_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (ASIDPool ap) s) and
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p\<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  apply (wpsimp wp: set_object_vspace_objs simp: a_type_simps)
  apply (fastforce simp: vs_refs_def)
  done

lemma set_asid_pool_vspace_objs_unmap:
  "\<lbrace>valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S)  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (wp set_asid_pool_vspace_objs_unmap')
  apply (clarsimp simp: obj_at_def graph_of_restrict_map)
  apply (drule valid_vspace_objsD, simp add: obj_at_def, assumption)
  apply simp
  by (auto simp: obj_at_def dest!: ran_restrictD)

lemma set_asid_pool_table_caps [wp]:
  "\<lbrace>valid_table_caps\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  apply (rule valid_table_caps_lift)
    apply (rule set_asid_pool_caps_of_state)
   apply wpsimp
  unfolding set_asid_pool_def including unfold_objects
  apply (wpsimp wp: set_object_wp_strong simp: a_type_def empty_table_def)
  apply (metis kernel_object_exhaust)
  done

lemma set_asid_pool_vs_lookup_unmap':
  "\<lbrace>valid_vs_lookup and
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p\<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def simp del: fun_upd_apply del: disjCI
                  split: kernel_object.splits arch_kernel_obj.splits)
  subgoal for \<dots> pa ref
    apply (spec pa)
    apply (spec ref)
    apply (erule impE)
     apply (erule vs_lookup_pages_stateI)
      by (clarsimp simp: obj_at_def vs_refs_pages_def split: if_split_asm)
         fastforce+
  done


lemma set_asid_pool_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (wp set_asid_pool_vs_lookup_unmap')
  by (clarsimp simp: obj_at_def
                 elim!: subsetD [OF graph_of_restrict_map])


lemma valid_pte_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pte pte s = valid_pte pte s'"
  by (case_tac pte, auto simp add: data_at_def)


lemma valid_pde_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pde pde s = valid_pde pde s'"
  by (case_tac pde, auto simp add: data_at_def)

lemma valid_vspace_obj_same_type:
  "\<lbrakk>valid_vspace_obj ao s;  kheap s p = Some ko; a_type ko' = a_type ko\<rbrakk>
  \<Longrightarrow> valid_vspace_obj ao (s\<lparr>kheap := kheap s(p \<mapsto> ko')\<rparr>)"
    apply (rule hoare_to_pure_kheap_upd[OF valid_vspace_obj_typ])
    by (auto simp: obj_at_def)

lemma set_asid_pool_global_objs [wp]:
  "\<lbrace>valid_global_objs and valid_arch_state\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def a_type_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: valid_global_objs_def valid_vso_at_def)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def)
   apply (rule conjI)
    subgoal by (clarsimp simp: valid_arch_state_def obj_at_def a_type_def)
   apply clarsimp
   apply (erule (1) valid_vspace_obj_same_type)
   subgoal by (simp add: a_type_def)
  apply (rule conjI)
   subgoal by (clarsimp simp: obj_at_def valid_arch_state_def a_type_def)
  apply (clarsimp simp: obj_at_def)
  apply (drule (1) bspec)
  by clarsimp


crunch v_ker_map[wp]: set_asid_pool "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_asid_pool_restrict_asid_map:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow> ucast asid \<notin> S \<longrightarrow>
                arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                arm_asid_map (arch_state s) asid = None)\<rbrace>
  set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: set_asid_pool_def valid_asid_map_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits
                  simp del: fun_upd_apply)
  apply (drule(1) bspec)
  apply (clarsimp simp: vspace_at_asid_def obj_at_def graph_of_def)
  apply (drule subsetD, erule domI)
  apply simp
  apply (drule spec, drule(1) mp)
  apply simp
  apply (erule vs_lookupE)
  apply (rule vs_lookupI, simp)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (drule rtranclD)
  apply (erule disjE, clarsimp)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (rule r_into_rtrancl)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (subst vs_lookup1_def)
  apply (clarsimp simp: obj_at_def)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_refs_def graph_of_def)
   apply (rule image_eqI[where x="(_, _)"])
    apply (simp add: split_def)
   apply (clarsimp simp: restrict_map_def)
   apply (drule ucast_up_inj, simp)
   apply (simp add: mask_asid_low_bits_ucast_ucast)
   apply (drule ucast_up_inj, simp)
   apply clarsimp
  apply clarsimp
  apply (drule vs_lookup1_trans_is_append)
  apply clarsimp
  apply (drule vs_lookup1D)
  by clarsimp


lemma set_asid_pool_asid_map_unmap:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow>
                ucast asid = x \<longrightarrow>
                arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                arm_asid_map (arch_state s) asid = None)\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  using set_asid_pool_restrict_asid_map[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)


lemma set_asid_pool_vspace_objs_unmap_single:
  "\<lbrace>valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  using set_asid_pool_vspace_objs_unmap[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

lemma set_asid_pool_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift set_asid_pool_typ_at)


lemma set_asid_pool_equal_mappings [wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (simp add: set_asid_pool_def | wp set_object_equal_mappings get_object_wp)+

lemma set_asid_pool_valid_global_vspace_mappings[wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace>
      set_asid_pool p ap \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_global_vspace_mappings[THEN hoare_set_object_weaken_pre])
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_asid_pool_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by (wpsimp wp: set_object_pspace_in_kernel_window[THEN hoare_set_object_weaken_pre])

lemma set_asid_pool_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by (wpsimp wp: set_object_pspace_respects_device_region[THEN hoare_set_object_weaken_pre])


lemma set_asid_pool_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by (wpsimp wp: set_object_cap_refs_in_kernel_window[THEN hoare_set_object_weaken_pre]
           simp: a_type_def)

lemma set_asid_pool_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_cap_refs_respects_device_region[THEN hoare_set_object_weaken_pre])
  including unfold_objects
  by (simp add: a_type_def)


lemma set_asid_pool_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_ioc_no_caps[THEN hoare_set_object_weaken_pre])
  including unfold_objects
  by (clarsimp simp: valid_def get_object_def simpler_gets_def assert_def
          return_def fail_def bind_def
          a_type_simps is_tcb is_cap_table)


lemma set_asid_pool_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_asid_pool p S \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (erule valid_machine_state_heap_updI)
  apply (fastforce simp: a_type_def obj_at_def
                  split: kernel_object.splits arch_kernel_obj.splits)+
  done

lemma cur_tcb_more_update[iff]:
  "cur_tcb (trans_state f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma set_asid_pool_reply_at_ppred[wp]:
  "set_asid_pool p ap \<lbrace> \<lambda>s. P (reply_at_pred P' r s) \<rbrace>"
  by (wpsimp simp: set_asid_pool_def wp: set_object_wp_strong get_object_wp)
     (fastforce elim!: bool_to_boolE[of P]
                 simp: obj_at_def reply_at_ppred_def
                split: kernel_object.splits if_splits)

sublocale set_asid_pool: non_reply_op "set_asid_pool p ap"
  by unfold_locales wp

lemma set_asid_pool_sc_at_pred_n[wp]:
  "set_asid_pool p ap \<lbrace> \<lambda>s. P (sc_at_pred_n N (\<lambda>sc. sc) P' r s) \<rbrace>"
  by (wpsimp simp: set_asid_pool_def wp: set_object_wp_strong get_object_wp)
     (fastforce elim!: bool_to_boolE[of P]
                 simp: obj_at_def sc_at_pred_n_def a_type_simps
                split: kernel_object.splits if_splits)

sublocale set_asid_pool: non_sc_op "set_asid_pool p pt"
  by unfold_locales wp

lemma set_asid_pool_valid_replies[wp]:
  "set_asid_pool p ap \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

lemma set_asid_pool_fault_tcbs_valid_states[wp]:
  "set_asid_pool p ap \<lbrace> fault_tcbs_valid_states \<rbrace>"
  by (wpsimp wp: fault_tcbs_valid_states_lift)

lemma set_asid_pool_invs_restrict:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow> ucast asid \<notin> S \<longrightarrow>
                arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                arm_asid_map (arch_state s) asid = None)\<rbrace>
        (set_asid_pool p (ap |` S)) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def
                   valid_arch_caps_def)
  apply (wp valid_irq_node_typ set_asid_pool_typ_at
            set_asid_pool_vspace_objs_unmap valid_irq_handlers_lift
            set_asid_pool_vs_lookup_unmap set_asid_pool_restrict_asid_map)
  apply simp_all
  done


lemmas set_asid_pool_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF set_asid_pool_caps_of_state]


lemma mdb_cte_at_set_asid_pool[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>
   set_asid_pool y pool
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
done

lemma set_asid_pool_invs_unmap:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow> ucast asid = x \<longrightarrow>
                arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                arm_asid_map (arch_state s) asid = None)\<rbrace>
        (set_asid_pool p (ap(x := None))) \<lbrace>\<lambda>_. invs\<rbrace>"
  using set_asid_pool_invs_restrict[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)


lemma valid_slots_typ_at:
  assumes x: "\<And>T p. \<lbrace>typ_at (AArch T) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (AArch T) p\<rbrace>"
  assumes y: "\<And>p. \<lbrace>\<exists>\<rhd> p\<rbrace> f \<lbrace>\<lambda>rv. \<exists>\<rhd> p\<rbrace>"
  shows "\<lbrace>valid_slots m\<rbrace> f \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  unfolding valid_slots_def
  by (cases m; clarsimp; wp x y hoare_vcg_const_Ball_lift valid_pte_lift
                            valid_pde_lift pte_at_atyp pde_at_atyp)


lemma ucast_ucast_id:
  "(len_of TYPE('a)) < (len_of TYPE('b)) \<Longrightarrow> ucast ((ucast (x::('a::len) word))::('b::len) word) = x"
  by (auto intro: ucast_up_ucast_id simp: is_up_def source_size_def target_size_def word_size)


lemma kernel_base_kernel_mapping_slots:
  "x < kernel_base \<Longrightarrow> ucast (x >> 20) \<notin> kernel_mapping_slots"
  apply (simp add: kernel_mapping_slots_def kernel_base_def)
  apply (subst ucast_le_ucast[symmetric, where 'a=12 and 'b=32])
   apply simp
  apply (subst ucast_ucast_mask)
  apply (simp add: ucast_def)
  apply (subst less_mask_eq)
   apply (rule vptr_shiftr_le_2p[unfolded pageBits_def])
  apply (subst word_not_le)
  apply word_bitwise
done


lemma lookup_pt_slot_looks_up [wp]:
  "\<lbrace>ref \<rhd> pd and K (is_aligned pd 14 \<and> vptr < kernel_base)
   and valid_arch_state and valid_vspace_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs\<rbrace>
  lookup_pt_slot pd vptr
  \<lbrace>\<lambda>pt_slot. (VSRef (vptr >> 20 << 2 >> 2) (Some APageDirectory) # ref) \<rhd> (pt_slot && ~~ mask pt_bits)\<rbrace>, -"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp|wpc)+
  apply clarsimp
  apply (rule vs_lookup_step, assumption)
  apply (clarsimp simp: vs_lookup1_def lookup_pd_slot_def Let_def pd_shifting pd_shifting_dual)
  apply (rule exI, rule conjI, assumption)
  subgoal for s _ x
    apply (prop_tac "ptrFromPAddr x + ((vptr >> 12) && 0xFF << 2) && ~~ mask pt_bits = ptrFromPAddr x")
     apply (prop_tac "is_aligned (ptrFromPAddr x) 10")
      apply (drule (2) valid_vspace_objsD)
      apply clarsimp
      apply (erule_tac x="ucast (vptr >> 20 << 2 >> 2)" in ballE)
      apply (thin_tac "obj_at P x s" for P x)+
      apply (clarsimp simp: obj_at_def invs_def valid_state_def valid_pspace_def pspace_aligned_def)
      apply (drule bspec, blast)
      apply (clarsimp simp: a_type_def
                      split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
      apply (frule kernel_mapping_slots_empty_pdeI)
        apply ((simp add: obj_at_def)+)[4]
      apply (clarsimp simp: pde_ref_def second_level_tables_def)
      apply (erule is_aligned_global_pt[unfolded pt_bits_def pageBits_def, simplified])
      apply simp+
     apply (subgoal_tac "(vptr >> 12) && 0xFF << 2 < 2 ^ 10")
      apply (subst is_aligned_add_or, (simp add: pt_bits_def pageBits_def)+)
      apply (subst word_ao_dist)
      apply (subst mask_out_sub_mask [where x="(vptr >> 12) && 0xFF << 2"])
      apply (subst less_mask_eq, simp)
      apply (subst is_aligned_neg_mask_eq, simp)
      apply (clarsimp simp: valid_arch_state_def valid_global_pts_def)
     apply (rule shiftl_less_t2n, simp)
      apply (rule and_mask_less'[where n=8, unfolded mask_def, simplified], (simp )+)
    apply (subst shiftl_shiftr_id)
      apply (simp add: word_bits_def)+
     apply word_bitwise
    apply (subst (asm) shiftl_shiftr_id)
      apply (simp add: word_bits_def)+
     apply word_bitwise
    apply (erule vs_refs_pdI)
     apply (erule kernel_base_kernel_mapping_slots)
    apply (intro allI impI)
    apply (simp add: nth_shiftr)
    apply (rule bang_big[simplified])
    by (simp add: word_size)
  done


lemma lookup_pt_slot_reachable [wp]:
  "\<lbrace>\<exists>\<rhd> pd and K (is_aligned pd 14 \<and> vptr < kernel_base)
   and valid_arch_state and valid_vspace_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs\<rbrace>
  lookup_pt_slot pd vptr
  \<lbrace>\<lambda>pt_slot. \<exists>\<rhd> (pt_slot && ~~ mask pt_bits)\<rbrace>, -"
  apply (simp add: pred_conj_def ex_simps [symmetric] del: ex_simps)
  apply (rule hoare_vcg_ex_lift_R1)
  apply (rule hoare_pre)
   apply (rule hoare_post_imp_R)
    apply (rule lookup_pt_slot_looks_up)
   prefer 2
   apply clarsimp
   apply assumption
  apply fastforce
  done


lemma lookup_pt_slot_reachable2 [wp]:
  "\<lbrace>\<exists>\<rhd> pd and K (is_aligned pd 14 \<and> is_aligned vptr 16 \<and> vptr < kernel_base)
   and valid_arch_state and valid_vspace_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs\<rbrace>
   lookup_pt_slot pd vptr
  \<lbrace>\<lambda>rv s. \<forall>x\<in>set [0 , 4 .e. 0x3C]. (\<exists>\<rhd> (x + rv && ~~ mask pt_bits)) s\<rbrace>, -"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp|wpc)+
  apply clarsimp
  apply (rule exI)
  apply (rule vs_lookup_step, assumption)
  apply (clarsimp simp: vs_lookup1_def lookup_pd_slot_def Let_def pd_shifting pd_shifting_dual
                        add.commute add.left_commute)
  apply (rule exI, rule conjI, assumption)
  apply (rule_tac x="VSRef (vptr >> 20 << 2 >> 2) (Some APageDirectory)" in exI)
  apply (subgoal_tac "ptrFromPAddr x + (xa + ((vptr >> 12) && 0xFF << 2)) && ~~ mask pt_bits = ptrFromPAddr x")
   prefer 2
   apply (subgoal_tac "is_aligned (ptrFromPAddr x) 10")
    prefer 2
    apply (drule (2) valid_vspace_objsD)
    apply clarsimp
    apply (erule_tac x="ucast (vptr >> 20 << 2 >> 2)" in ballE)
    apply (thin_tac "obj_at P x s" for P x)+
    apply (clarsimp simp: obj_at_def pspace_aligned_def)
    apply (drule bspec, blast)
    apply (clarsimp simp: a_type_def
                    split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
    apply (frule kernel_mapping_slots_empty_pdeI)
    apply (simp add: obj_at_def)+
    apply clarsimp
    apply (erule_tac x="ptrFromPAddr x" in allE)
    apply (clarsimp simp: pde_ref_def second_level_tables_def)
    apply (rule is_aligned_global_pt[unfolded pt_bits_def pageBits_def, simplified])
    apply simp+
   apply (subst add_mask_lower_bits)
     apply (simp add: pt_bits_def pageBits_def)
    prefer 2
    apply simp
   apply (clarsimp simp: pt_bits_def pageBits_def)
   apply (clarsimp simp: upto_enum_step_def word_shift_by_2 p_le_0xF_helper)
   apply (thin_tac "pda x = t" for x t)
   apply (subst (asm) word_plus_and_or_coroll)
    apply (rule word_eqI)
    apply (clarsimp simp: word_size word_bits_def nth_shiftr nth_shiftl is_aligned_nth word_FF_is_mask)
    apply (erule_tac x="n - 2" in allE)
    apply simp
   apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth word_FF_is_mask word_bits_def)
  apply (rule conjI, rule refl)
  apply (simp add: add.commute add.left_commute)
  apply (rule vs_refs_pdI)
    prefer 3
    apply (clarsimp simp: word_ops_nth_size word_size nth_shiftr nth_shiftl)
    apply (drule test_bit_size)
    apply (simp add: word_size)
   apply fastforce
  apply (subst shiftl_shiftr_id)
    apply (simp add: word_bits_def)+
   apply word_bitwise
  apply (erule kernel_base_kernel_mapping_slots)
  done

lemma lookup_pt_slot_reachable3 [wp]:
  "\<lbrace>\<exists>\<rhd> pd and K (is_aligned pd 14 \<and> is_aligned vptr 16 \<and> vptr < kernel_base)
   and valid_arch_state and valid_vspace_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs\<rbrace>
   lookup_pt_slot pd vptr
  \<lbrace>\<lambda>p s. \<forall>x\<in>set [p, p + 4 .e. p + 0x3C]. (\<exists>\<rhd> (x && ~~ mask pt_bits)) s\<rbrace>, -"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp|wpc)+
  apply (clarsimp del: ballI)
  apply (clarsimp simp: lookup_pd_slot_def Let_def del: ballI)
  apply (simp add: pd_shifting)
  apply (frule (2) valid_vspace_objsD)
  apply (clarsimp del: ballI)
  apply (erule_tac x="(ucast (pd + (vptr >> 20 << 2) && mask pd_bits >> 2))" in ballE)
  apply (clarsimp del: ballI)
  apply (subgoal_tac "is_aligned (ptrFromPAddr x) 10")
   prefer 2
   apply (thin_tac "ko_at P p s" for P p)+
   apply (clarsimp simp: obj_at_def add.commute add.left_commute pspace_aligned_def)
   apply (drule bspec, blast)
   apply (clarsimp simp: a_type_def split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (subst p_0x3C_shift)
   apply (rule aligned_add_aligned, assumption)
     apply (clarsimp intro!: is_aligned_andI1 is_aligned_shiftl is_aligned_shiftr)
   apply simp
  apply clarsimp
  apply (rule exI)
  apply (rule vs_lookup_step, assumption)
  apply (clarsimp simp: vs_lookup1_def lookup_pd_slot_def Let_def pd_shifting pd_shifting_dual add.commute add.left_commute)
  apply (rule exI, rule conjI, assumption)
  apply (rule_tac x="VSRef (vptr >> 20 << 2 >> 2) (Some APageDirectory)" in exI)
  apply (rule conjI, rule refl)
  apply (subgoal_tac "ptrFromPAddr x + (xc + ((vptr >> 12) && 0xFF << 2)) && ~~ mask pt_bits = ptrFromPAddr x")
   prefer 2
   apply (subst add_mask_lower_bits)
     apply (simp add: pt_bits_def pageBits_def)
    prefer 2
    apply simp
   apply (clarsimp simp: pt_bits_def pageBits_def)
   apply (clarsimp simp: upto_enum_step_def word_shift_by_2 p_le_0xF_helper)
   apply (thin_tac "pda x = t" for x t)
   apply (subst (asm) word_plus_and_or_coroll)
    apply (rule word_eqI)
    apply (clarsimp simp: word_size word_bits_def nth_shiftr nth_shiftl is_aligned_nth word_FF_is_mask)
    apply (erule_tac x="n - 2" in allE)
    apply simp
   apply (clarsimp simp: word_size nth_shiftr nth_shiftl is_aligned_nth word_FF_is_mask word_bits_def)
  apply (simp add: add.commute add.left_commute)
  apply (rule vs_refs_pdI)
   prefer 3
   apply (clarsimp simp: word_ops_nth_size word_size nth_shiftr nth_shiftl)
   apply (drule test_bit_size)
   apply (simp add: word_size)
  apply fastforce
   apply (subst shiftl_shiftr_id)
     apply (simp add: word_bits_def)+
    apply word_bitwise
   apply (erule kernel_base_kernel_mapping_slots)
  apply clarsimp
  apply (subst (asm) mask_add_aligned, simp add: pd_bits_def pageBits_def)+
  apply (simp add: shiftr_over_and_dist)
  apply (subst (asm) shiftl_shiftr_id, (simp add: word_bits_conv)+, word_bitwise)+
  apply (subst (asm) shiftr_mask2, (simp add: pd_bits_def pageBits_def)+)+
  apply (simp add: shiftr_mask_eq[where x=vptr and n=20, unfolded word_size, simplified])
  apply (drule kernel_base_kernel_mapping_slots, simp)
  done


lemma pd_aligned:
  "\<lbrakk>pspace_aligned s; page_directory_at pd s\<rbrakk> \<Longrightarrow> is_aligned pd 14"
  apply (clarsimp simp: pspace_aligned_def obj_at_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: a_type_def split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  done


lemma shiftr_shiftl_mask_pd_bits:
  "(((vptr :: word32) >> 20) << 2) && mask pd_bits = (vptr >> 20) << 2"
  apply (rule iffD2 [OF mask_eq_iff_w2p])
   apply (simp add: pd_bits_def pageBits_def word_size)
  apply (rule shiftl_less_t2n)
   apply (rule shiftr_less_t2n3,
          simp_all add: pd_bits_def word_bits_def pageBits_def)
  done


lemma triple_shift_fun:
  "x >> 20 << 2 >> 2 = (x :: ('a :: len) word) >> 20"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftr nth_shiftl)
  apply safe
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done


lemma shiftr_20_unat_ucast:
  "unat (ucast (x >> 20 :: word32) :: 12 word) = unat (x >> 20)"
  using vptr_shiftr_le_2p[where vptr=x]
  apply (simp only: unat_ucast)
  apply (rule mod_less)
  apply (rule unat_less_power)
   apply (simp add: word_bits_def)
  apply (simp add: pageBits_def)
  done


lemma shiftr_20_less:
  "((ucast (x >> 20) :: 12 word) < ucast (y >> 20)) = ((x >> 20 :: word32) < y >> 20)"
  "((ucast (x >> 20) :: 12 word) \<le> ucast (y >> 20)) = ((x >> 20 :: word32) \<le> y >> 20)"
  by (simp add: word_less_nat_alt word_le_nat_alt shiftr_20_unat_ucast)+


lemma kernel_base_ge_observation:
  "(kernel_base \<le> x) = (x && ~~ mask 29 = kernel_base)"
  apply (subst mask_in_range)
   apply (simp add: kernel_base_def is_aligned_def)
  apply (simp add: kernel_base_def)
  done


lemma kernel_base_less_observation:
  "(x < kernel_base) = (x && ~~ mask 29 \<noteq> kernel_base)"
  apply (simp add: linorder_not_le[symmetric] kernel_base_ge_observation)
  done

lemma vptr_shifting_helper_magic:
  "(x = 0) \<or> (x < 2 ^ 4 \<and> vmsz_aligned (vptr::word32) ARMSuperSection)
   \<Longrightarrow> (x << 2) + (vptr >> 20 << 2) = ((vptr + (x << 20)) >> 20 << 2)"
  apply (erule disjE, simp_all)
  apply (clarsimp simp: vmsz_aligned_def)
  apply (subst is_aligned_add_or, assumption)
   apply (rule shiftl_less_t2n)
    apply simp
   apply simp
  apply (simp add: shiftl_over_or_dist shiftr_over_or_dist)
  apply (subst shiftl_shiftr_id)
    apply (simp add: word_bits_def)
   apply (simp add: word_bits_def)
   apply unat_arith
  apply (subst field_simps, rule is_aligned_add_or[where n=6])
   apply (intro is_aligned_shiftl is_aligned_shiftr)
   apply simp
  apply (rule shiftl_less_t2n, simp_all)
  done


lemma less_kernel_base_mapping_slots_both:
  "\<lbrakk> vptr < kernel_base; is_aligned pd pd_bits;
          (x = 0)
           \<or> (x < 2 ^ 4 \<and> vmsz_aligned vptr ARMSuperSection) \<rbrakk>
       \<Longrightarrow> ucast ((x << 2) + lookup_pd_slot pd vptr && mask pd_bits >> 2)
                \<notin> kernel_mapping_slots"
  apply (simp add: lookup_pd_slot_def Let_def)
  apply (subst field_simps, subst mask_add_aligned, assumption)
  apply (subst vptr_shifting_helper_magic)
   apply simp
  apply (simp add: shiftr_shiftl_mask_pd_bits triple_shift_fun)
  apply (simp add: kernel_mapping_slots_def linorder_not_le
                   shiftr_20_less)
  apply (rule le_m1_iff_lt[THEN iffD1,THEN iffD1])
   apply (simp add:kernel_base_def)
  apply (erule disjE)
   apply (drule word_less_sub_1)
   apply simp
   apply (drule le_shiftr[where n=20])
   apply (clarsimp simp :kernel_base_def vmsz_aligned_def)+
  apply (drule(1) gap_between_aligned)
    apply (simp add:is_aligned_def)
   apply simp
  apply (rule order.trans[OF le_shiftr])
   apply (rule word_plus_mono_right[OF _ is_aligned_no_wrap'[where off = "2^24-1"]])
     apply (rule word_less_sub_1)
     apply (rule shiftl_less_t2n)
      apply simp+
  apply (clarsimp dest!:word_less_sub_1)
  apply (erule order.trans[OF le_shiftr])
  apply simp
done

lemmas less_kernel_base_mapping_slots
    = less_kernel_base_mapping_slots_both[where x=0, simplified]


lemma is_aligned_lookup_pd_slot:
  "\<lbrakk>is_aligned vptr 24; is_aligned pd 6\<rbrakk>
   \<Longrightarrow> is_aligned (lookup_pd_slot pd vptr) 6"
   apply (clarsimp simp: lookup_pd_slot_def)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl)
    apply (rule is_aligned_shiftr)
    apply simp
   apply (simp add: word_bits_conv)
   done

lemma lookup_pd_slot_eq:
  "is_aligned pd pd_bits \<Longrightarrow>
   (lookup_pd_slot pd vptr && ~~ mask pd_bits) = pd"
  apply (clarsimp simp: lookup_pd_slot_def)
  apply (erule conjunct2[OF is_aligned_add_helper])
  apply (rule shiftl_less_t2n)
   apply (rule shiftr_less_t2n3)
    apply (simp_all add: pd_bits_def pageBits_def)
  done

lemma is_aligned_lookup_pt_slot_no_fail:
  "\<lbrakk>is_aligned vptr 16; is_aligned pt 6\<rbrakk>
   \<Longrightarrow> is_aligned (lookup_pt_slot_no_fail pt vptr) 6"
   apply (clarsimp simp: lookup_pt_slot_no_fail_def)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl)
    apply (rule is_aligned_andI1)
    apply (rule is_aligned_shiftr)
    apply simp
   apply simp
   done

lemma lookup_pt_slot_non_empty:
  "\<lbrace>valid_vspace_objs and \<exists>\<rhd> pd and page_directory_at pd and pspace_aligned
  and K (is_aligned vptr 16 \<and> vptr < kernel_base)\<rbrace>
  lookup_pt_slot pd vptr \<lbrace>\<lambda>rv s. [rv , rv + 4 .e. rv + 0x3C] \<noteq> []\<rbrace>, -"
   apply (simp add:lookup_pt_slot_def)
   apply (wp get_pde_wp| wpc | clarsimp)+
   apply (simp add:valid_vspace_objs_def)
   apply (drule_tac x = "(lookup_pd_slot pd vptr && ~~ mask pd_bits)" in spec)
   apply (erule impE)
    apply (subst lookup_pd_slot_eq)
    apply (clarsimp simp: obj_at_def)
     apply (drule_tac p = pd in pspace_alignedD)
      apply simp
     apply (simp add:obj_bits_def pageBits_def pd_bits_def)
    apply fastforce
   apply (drule spec)
   apply (erule(1) impE)
   apply (clarsimp simp:)
   apply (drule_tac x = "(ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2))" in bspec)
    apply (drule less_kernel_base_mapping_slots)
     apply (clarsimp simp: obj_at_def)
     apply (drule_tac p = pd in pspace_alignedD)
      apply simp
     apply (simp add:obj_bits_def pageBits_def pd_bits_def)
    apply simp
   apply (clarsimp simp: obj_at_def)
   apply (drule_tac p = "(ptrFromPAddr x)" in pspace_alignedD)
    apply simp
   apply (drule arg_cong[where f = length])
   apply (subst (asm) length_upto_enum_step)
    apply (rule_tac sz = 6 in is_aligned_no_wrap'[rotated])
     apply simp
    apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl)
     apply (rule is_aligned_andI1[OF is_aligned_shiftr])
     apply simp
    apply (simp add:word_bits_conv)
   apply (simp add:word_bits_conv)
  done

(* FIXME: move *)
lemma pd_bits: "pd_bits = 14"
   by (simp add: pd_bits_def pageBits_def)

lemma word_shift_by_n:
  "x * (2^n) = (x::'a::len word) << n"
  by (simp add: shiftl_t2n)

lemma create_mapping_entries_valid_slots [wp]:
  "\<lbrace>valid_arch_state and valid_vspace_objs and equal_kernel_mappings
   and pspace_aligned and valid_global_objs
   and \<exists>\<rhd> pd and page_directory_at pd and data_at sz (ptrFromPAddr base) and
    K (vmsz_aligned base sz \<and> vmsz_aligned vptr sz \<and> vptr < kernel_base
       \<and> vm_rights \<in> valid_vm_rights)\<rbrace>
  create_mapping_entries base vptr sz vm_rights attrib pd
  \<lbrace>\<lambda>m. valid_slots m\<rbrace>, -"
  apply (cases sz)
     apply (rule hoare_pre)
      apply (wp lookup_pt_slot_inv | simp add: valid_slots_def)+
     apply (clarsimp simp: vmsz_aligned_def pd_aligned pageBits_def)
    apply (rule hoare_pre)
     apply (simp add: valid_slots_def largePagePTE_offsets_def pd_bits_def)
     apply (wpsimp wp: lookup_pt_slot_inv lookup_pt_slot_non_empty
           | simp add: valid_slots_def ball_conj_distrib largePagePTE_offsets_def)+
    apply (clarsimp simp: pd_aligned vmsz_aligned_def upto_enum_def upto_enum_step_def
                          is_aligned_weaken pageBits_def)
   apply (clarsimp simp add: valid_slots_def)
   apply (rule hoare_pre)
    apply wp
   apply (clarsimp simp: valid_slots_def)
   apply (rule conjI)
    apply (simp add: lookup_pd_slot_def Let_def)
    apply (fastforce simp: pd_shifting pd_aligned)
   apply (simp add: page_directory_pde_at_lookupI)
   apply (erule less_kernel_base_mapping_slots)
   apply (simp add: pd_aligned pd_bits)
  apply simp
  apply (clarsimp simp: superSectionPDE_offsets_def)
  apply (rule hoare_pre)
   apply (clarsimp simp add: valid_slots_def)
   apply wp
  apply simp
  apply (elim conjE)
  apply (thin_tac "vmsz_aligned base b" for b)
  apply (subgoal_tac "is_aligned pd 14")
   prefer 2
   apply (clarsimp simp: pd_aligned)
  apply (clarsimp simp: upto_enum_step_def  word_shift_by_2)
  apply (clarsimp simp: obj_at_def pde_at_def)
  apply (subgoal_tac "is_aligned pd pd_bits")
   prefer 2
   apply (simp add: pd_bits)
  apply (rule conjI, simp add: upto_enum_def)
  apply (intro allI impI)
  apply (subst less_kernel_base_mapping_slots_both,assumption+)
   apply (simp add: word_leq_minus_one_le)
  apply (simp add: pd_bits vmsz_aligned_def)
  apply (frule (1) is_aligned_lookup_pd_slot
                   [OF _ is_aligned_weaken[of _ 14 6, simplified]])
  apply (subgoal_tac "(p<<2) + lookup_pd_slot pd vptr && ~~ mask 14 = pd")
   prefer 2
   apply (subst add.commute add.left_commute)
   apply (subst and_not_mask_twice[where n=6 and m=14, simplified, symmetric])
   apply (subst is_aligned_add_helper[THEN conjunct2], simp)
    apply (rule shiftl_less_t2n)
     apply (rule word_less_sub_le[THEN iffD1], simp+)
   apply (erule lookup_pd_slot_eq[simplified pd_bits])
  apply (simp add: a_type_simps)
  apply (subst add.commute)
  apply (fastforce intro!: aligned_add_aligned is_aligned_shiftl_self)
  done

lemma is_aligned_addrFromPPtr_n:
  "\<lbrakk> is_aligned p n; n \<le> 28 \<rbrakk> \<Longrightarrow> is_aligned (Platform.ARM.addrFromPPtr p) n"
  apply (simp add: Platform.ARM.addrFromPPtr_def)
  apply (erule aligned_sub_aligned, simp_all)
  apply (simp add: pptrBaseOffset_def physBase_def
                   pptrBase_def pageBits_def)
  apply (erule is_aligned_weaken[rotated])
  apply (simp add: is_aligned_def)
  done

lemma is_aligned_addrFromPPtr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (Platform.ARM.addrFromPPtr p) pageBits"
  by (simp add: is_aligned_addrFromPPtr_n pageBits_def)

lemma is_aligned_ptrFromPAddr_n:
  "\<lbrakk>is_aligned x sz; sz\<le> 28\<rbrakk>
  \<Longrightarrow> is_aligned (ptrFromPAddr x) sz"
  apply (simp add:ptrFromPAddr_def pptrBaseOffset_def
    pptrBase_def physBase_def)
  apply (erule aligned_add_aligned)
   apply (erule is_aligned_weaken[rotated])
   apply (simp add:is_aligned_def)
  apply (simp add:word_bits_def)
  done

lemma is_aligned_ptrFromPAddr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (ptrFromPAddr p) pageBits"
  by (simp add: is_aligned_ptrFromPAddr_n pageBits_def)

lemma pbfs_le_28[simp]:
  "pageBitsForSize sz \<le> 28"
  by (cases sz; simp)

lemma store_pde_lookup_pd:
  "\<lbrace>\<exists>\<rhd> pd and page_directory_at pd and valid_vspace_objs
     and (\<lambda>s. valid_asid_table (arm_asid_table (arch_state s)) s)\<rbrace>
  store_pde p pde \<lbrace>\<lambda>_. \<exists>\<rhd> pd\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp simp: obj_at_def)
  apply (erule vs_lookupE)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (drule rtranclD)
  apply (erule disjE)
   apply clarsimp
   apply (rule exI)
   apply (rule vs_lookup_atI)
   apply simp
  apply clarsimp
  apply (frule (1) valid_asid_tableD)
  apply (frule vs_lookup_atI)
  apply (frule (2) stronger_vspace_objsD)
  apply (clarsimp simp: obj_at_def a_type_def)
  apply (case_tac ao, simp_all, clarsimp)
  apply (drule tranclD)
  apply clarsimp
  apply (drule rtranclD)
  apply (erule disjE)
   apply clarsimp
   apply (rule_tac x=ref in exI)
   apply (rule vs_lookup_step)
    apply (rule vs_lookup_atI)
    apply simp
   apply (clarsimp simp: vs_lookup1_def)
   apply (clarsimp simp: obj_at_def vs_refs_def graph_of_def)
  apply clarsimp
  apply (drule (1) vs_lookup_step)
  apply (frule (2) stronger_vspace_objsD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (erule obj_atE)+
  apply (clarsimp simp: vs_refs_def graph_of_def)
  apply (drule bspec, blast)
  apply (erule obj_atE)+
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule rtranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (erule obj_atE)+
  apply (clarsimp simp: vs_refs_def graph_of_def)
  apply (erule_tac x=ab in ballE)
   apply (case_tac "pdb ab", simp_all add: pde_ref_def split: if_split_asm)
  apply (erule obj_atE)
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: a_type_def)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (erule obj_atE)+
  apply (clarsimp simp: vs_refs_def graph_of_def)
  done

lemma store_pde_vspace_objs_unmap:
  "\<lbrace>valid_vspace_objs
    and valid_pde pde
    and K (pde_ref pde = None)\<rbrace>
  store_pde p pde \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (simp add: store_pde_def)
  apply (wp set_pd_vspace_objs_unmap)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) valid_vspace_objsD, fastforce)
   apply (simp add:)
  apply (clarsimp simp add: obj_at_def vs_refs_def)
  apply (rule pair_imageI)
  apply (simp add: graph_of_def split: if_split_asm)
  done


(* FIXME: remove magic numbers in other lemmas, use in pde_at_aligned_vptr et al *)
lemma lookup_pd_slot_add_eq:
  "\<lbrakk> is_aligned pd pd_bits; is_aligned vptr 24; x \<in> set [0 , 4 .e. 0x3C] \<rbrakk>
  \<Longrightarrow> (x + lookup_pd_slot pd vptr && ~~ mask pd_bits) = pd"
    apply (simp add: pageBits_def add.commute add.left_commute lookup_pd_slot_def Let_def)
  apply (clarsimp simp: upto_enum_step_def word_shift_by_2)
  apply (erule add_mask_lower_bits2)
  apply (subgoal_tac "2 < pd_bits \<and> size vptr \<le> 18 + pd_bits")
   apply (simp add: and_mask_0_iff_le_mask le_mask_iff)
   apply (subst word_plus_and_or_coroll)
    apply (subst word_bw_comms)
    apply (rule aligned_mask_disjoint[where n=6])
     apply (rule is_aligned_shiftl, rule is_aligned_shiftr, simp)
    apply (rule order.trans, rule leq_high_bits_shiftr_low_bits_leq_bits[where high_bits=4])
     apply (clarsimp simp: mask_def, simp)
   apply (clarsimp simp: shiftr_over_or_dist word_or_zero)
   apply (intro conjI)
    apply (clarsimp simp: shiftl_shiftr3)
    apply (subgoal_tac "xa >> pd_bits - 2 = 0", simp)
    apply (rule shiftr_le_0, rule unat_less_helper)
    apply (erule order.strict_trans1, simp)
    apply (clarsimp simp: pd_bits_def pageBits_def)
   apply (clarsimp simp: shiftl_shiftr2 shiftr_shiftr shiftr_zero_size)
  apply (clarsimp simp: pd_bits_def pageBits_def word_bits_size word_bits_def)
  done


lemma vs_lookup_arch_update:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s) \<Longrightarrow>
  vs_lookup (arch_state_update f s) = vs_lookup s"
  apply (rule order_antisym)
   apply (rule vs_lookup_sub)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: obj_at_def)
  apply simp
  done


lemma vs_lookup_pages_arch_update:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s) \<Longrightarrow>
  vs_lookup_pages (arch_state_update f s) = vs_lookup_pages s"
  apply (rule order_antisym)
   apply (rule vs_lookup_pages_sub)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply (rule vs_lookup_pages_sub)
   apply (clarsimp simp: obj_at_def)
  apply simp
  done


lemma vs_lookup_asid_map [iff]:
  "vs_lookup (s\<lparr>arch_state := arm_asid_map_update f (arch_state s)\<rparr>) = vs_lookup s"
  by (simp add: vs_lookup_arch_update)


lemma vs_lookup_hwasid_table [iff]:
  "vs_lookup (s\<lparr>arch_state := arm_hwasid_table_update f (arch_state s)\<rparr>) = vs_lookup s"
  by (simp add: vs_lookup_arch_update)


lemma vs_lookup_next_asid [iff]:
  "vs_lookup (s\<lparr>arch_state := arm_next_asid_update f (arch_state s)\<rparr>) = vs_lookup s"
  by (simp add: vs_lookup_arch_update)


lemma vs_lookup_pages_asid_map[iff]:
  "vs_lookup_pages (s\<lparr>arch_state := arm_asid_map_update f (arch_state s)\<rparr>) =
   vs_lookup_pages s"
  by (simp add: vs_lookup_pages_arch_update)


lemma vs_lookup_pages_hwasid_table[iff]:
  "vs_lookup_pages (s\<lparr>arch_state := arm_hwasid_table_update f (arch_state s)\<rparr>) =
   vs_lookup_pages s"
  by (simp add: vs_lookup_pages_arch_update)


lemma vs_lookup_pages_next_asid[iff]:
  "vs_lookup_pages (s\<lparr>arch_state := arm_next_asid_update f (arch_state s)\<rparr>) =
   vs_lookup_pages s"
  by (simp add: vs_lookup_pages_arch_update)

lemma valid_vspace_objs_arch_update:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s) \<Longrightarrow>
  valid_vspace_objs (arch_state_update f s) = valid_vspace_objs s"
  apply (rule iffI)
   apply (erule valid_vspace_objs_stateI)
     apply (clarsimp simp: obj_at_def)
    apply simp
   apply simp
  apply (erule valid_vspace_objs_stateI)
    apply (clarsimp simp: obj_at_def)
   apply simp
  apply simp
  done

lemma store_pte_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs and valid_pte pte\<rbrace>
    store_pte p pte
  \<lbrace>\<lambda>_. (valid_vspace_objs)\<rbrace>"
  unfolding store_pte_def
  apply wp
  apply clarsimp
  apply (unfold valid_vspace_objs_def)
  apply (erule_tac x="p && ~~ mask pt_bits" in allE)
  apply auto
done

crunch valid_arch [wp]: store_pte valid_arch_state

lemma set_pd_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) \<subseteq> vs_refs_pages ko) p\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state])
   prefer 2
   apply wp
  apply (simp add: set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply del: disjCI
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule allE)+
  apply (erule impE)
   apply (erule vs_lookup_pages_stateI)
    apply (clarsimp simp: obj_at_def split: if_split_asm)
   apply simp
  apply simp
  done


lemma unique_table_caps_pdE:
  "\<lbrakk> unique_table_caps cs; cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap'; cap_asid cap' = Some v; is_pd_cap cap;
     is_pd_cap cap'; obj_refs cap' = obj_refs cap \<rbrakk>
       \<Longrightarrow> P"
  apply (frule(6) unique_table_caps_pdD[where cs=cs])
  apply simp
  done

lemma set_pd_table_caps [wp]:
  "\<lbrace>valid_table_caps and (\<lambda>s.
    (obj_at (empty_table (set (second_level_tables (arch_state s)))) p s \<longrightarrow>
     empty_table (set (second_level_tables (arch_state s))) (ArchObj (PageDirectory pd))) \<or>
    (\<exists>slot cap. caps_of_state s slot = Some cap \<and> is_pd_cap cap \<and> p \<in> obj_refs cap \<and> cap_asid cap \<noteq> None) \<and>
    valid_caps (caps_of_state s) s \<and>
    unique_table_caps (caps_of_state s))\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def
  apply (simp add: pred_conj_def
              del: split_paired_All split_paired_Ex imp_disjL)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state])
   prefer 2
   apply wp
  apply (unfold set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (rule allI, intro impI)
  apply (elim exE conjE)
  apply (elim allEI)
  apply (intro impI, simp)
  apply (clarsimp simp: obj_at_def)
  apply (erule disjE)
   apply (erule(6) unique_table_caps_pdE)
   apply (clarsimp simp: is_arch_cap_simps)
  apply (simp add: valid_caps_def)
  apply (erule_tac x=a in allE, erule allE, erule allE, erule (1) impE)
  apply (clarsimp simp: is_arch_cap_simps valid_cap_def)
  apply (clarsimp simp: obj_at_def)
  done


lemma set_pd_global_objs[wp]:
  "\<lbrace>valid_global_objs and valid_global_refs and
    valid_arch_state and
    (\<lambda>s. (obj_at (empty_table (set (second_level_tables (arch_state s)))) p s
             \<longrightarrow> empty_table (set (second_level_tables (arch_state s)))
                                 (ArchObj (PageDirectory pd)))
        \<or> (\<exists>slot. cte_wp_at (\<lambda>cap. p \<in> obj_refs cap) slot s))\<rbrace>
  set_pd p pd \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (simp add: set_pd_def second_level_tables_def)
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp add: valid_global_objs_def valid_vso_at_def
                            cte_wp_at_caps_of_state second_level_tables_def)
  apply (intro conjI)
    apply (clarsimp simp: obj_at_def
                simp del: valid_vspace_obj.simps)
    apply (intro conjI impI)
     apply (clarsimp simp del: valid_vspace_obj.simps)
     apply (erule disjE)
      apply (drule(1) empty_table_is_valid)+
      apply (rule valid_vspace_obj_same_type, (simp add: valid_vspace_obj_def)+)
      apply (clarsimp simp: a_type_def)
     apply (drule (1) valid_global_refsD2)
     apply (simp add: cap_range_def global_refs_def)
    apply (rule valid_vspace_obj_same_type, simp+)
    apply (simp add: a_type_def)
   apply (clarsimp simp: obj_at_def)
   apply (drule (1) valid_global_refsD2)
   apply (simp add: cap_range_def global_refs_def)
  apply clarsimp
  apply (clarsimp simp: obj_at_def
              simp del: valid_vspace_obj.simps)
  apply (drule(1) bspec, clarsimp simp: a_type_def)
  done

lemma eq_ucast_word12[simp]:
  "((ucast (x :: 12 word) :: word32) = ucast y) = (x = y)"
  apply safe
  apply (drule_tac f="ucast :: (word32 \<Rightarrow> 12 word)" in arg_cong)
  apply (simp add: ucast_up_ucast_id is_up_def
                   source_size_def target_size_def word_size)
  done

lemma set_pd_unmap_mappings:
  "\<lbrace>valid_kernel_mappings and
        obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) \<subseteq> vs_refs ko) p
    and obj_at (\<lambda>ko. \<exists>pd'. ko = ArchObj (PageDirectory pd')
                       \<and> (\<forall>x \<in> kernel_mapping_slots. pd x = pd' x)) p\<rbrace>
     set_pd p pd
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_v_ker_map get_object_wp)
  apply (clarsimp simp: obj_at_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  apply (simp add: vs_refs_def)
  subgoal premises prems for s x r x3
    apply (cases "x \<in> kernel_mapping_slots")
    proof goal_cases
     case False
     with prems show ?thesis
     apply -
     apply (drule subsetD)
      apply (rule image_eqI[rotated])
       apply (rule pde_graph_ofI[rotated, rotated])
          apply ((simp;fail)+)[4]
      apply (clarsimp simp: valid_kernel_mappings_def
                      dest!: graph_ofD)
      apply (drule bspec, erule ranI)
      by (simp add: valid_kernel_mappings_if_pd_def)
    next
     case True
     with prems show ?thesis
     apply clarsimp
     apply (bspec x)
      apply (clarsimp simp: valid_kernel_mappings_def ran_def valid_kernel_mappings_if_pd_def)
      apply (erule allE[where x="ArchObj (PageDirectory x3)"])
      apply clarsimp
      apply (erule impE)
        apply (erule exI[where x=p])
       apply (erule allE[where x=x], erule allE[where x=r])
       by clarsimp+
    qed
  done


lemma set_pd_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_pd p pd \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: a_type_def simp del: fun_upd_apply
                  split: kernel_object.splits
                         arch_kernel_obj.splits)
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: vspace_at_asid_def obj_at_def)
  apply (erule vs_lookupE)
  apply (rule vs_lookupI, simp)
  apply (clarsimp simp: vs_asid_refs_def dest!: graph_ofD)
  apply (frule vs_lookup1_trans_is_append)
  apply clarsimp
  apply (drule rtranclD)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (rule rtrancl_trans)
   apply (rule r_into_rtrancl)
   apply (rule vs_lookup1I)
     apply (clarsimp simp: obj_at_def)
     apply (rule conjI, clarsimp)
      prefer 2
      apply clarsimp
      apply (rule refl)
     apply clarsimp
     apply (clarsimp simp: vs_refs_def)
     apply (drule vs_lookup1_trans_is_append)
     apply clarsimp
    apply assumption
   apply (rule refl)
  apply (frule vs_lookup1_trans_is_append, clarsimp)
  apply (drule rtranclD)
  apply (erule disjE, clarsimp)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (drule vs_lookup1_trans_is_append, clarsimp)
  done


lemma set_pd_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_pd p pd \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)


lemma set_pd_equal_kernel_mappings_triv:
  "\<lbrace>obj_at (\<lambda>ko. \<exists>pd'. ko = (ArchObj (PageDirectory pd'))
                       \<and> (\<forall>x \<in> kernel_mapping_slots. pd x = pd' x)) p
          and equal_kernel_mappings\<rbrace>
     set_pd p pd
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_equal_mappings get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (simp add: equal_kernel_mappings_def obj_at_def)
  done


lemma set_pd_global_mappings[wp]:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_objs s
               \<and> p \<notin> global_refs s\<rbrace>
     set_pd p pd
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_global_vspace_mappings get_object_wp)
  apply simp
  done


lemma set_pd_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_pd p pd \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_pd_def)
  including unfold_objects
  apply (wpsimp wp: set_object_pspace_in_kernel_window[THEN hoare_set_object_weaken_pre])
  done

lemma set_pd_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_pd p pd \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  apply (simp add: set_pd_def)
  including unfold_objects
  apply (wpsimp wp: set_object_pspace_respects_device_region[THEN hoare_set_object_weaken_pre])
  done


lemma set_pd_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_pd p pd \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_pd_def)
  including unfold_objects
  apply (wpsimp wp: set_object_cap_refs_in_kernel_window[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  done

lemma set_pd_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_pd p pd \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_pd_def)
  including unfold_objects
  apply (wpsimp wp: set_object_cap_refs_respects_device_region[THEN hoare_set_object_weaken_pre]
              simp: a_type_def)
  done

lemma set_pd_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_pd p pt \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_pd_def)
  including unfold_objects
  apply (wpsimp wp: set_object_valid_ioc_no_caps[THEN hoare_set_object_weaken_pre]
              simp: a_type_def is_tcb is_cap_table)
  done


lemma set_pd_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_pd p pt \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_wp_strong)
  apply clarify
  apply (erule valid_machine_state_heap_updI)
  apply (fastforce simp: a_type_def obj_at_def
           split: Structures_A.kernel_object.splits arch_kernel_obj.splits)+
  done


lemma vs_refs_pages_subset2:
  "\<lbrakk>vs_refs_pages ko \<subseteq> vs_refs_pages ko';
    (\<forall>ao. (ko = ArchObj ao) \<longrightarrow> valid_vspace_obj ao s);
    (\<forall>ao'. (ko' = ArchObj ao') \<longrightarrow> valid_vspace_obj ao' s)\<rbrakk>
   \<Longrightarrow> vs_refs ko \<subseteq> vs_refs ko'"
  apply clarsimp
  apply (drule (1) subsetD[OF _ subsetD[OF vs_refs_pages_subset]])
  apply (case_tac ko; simp add: vs_refs_def)
  subgoal for fstref b arch_kernel_obj
    apply (cases arch_kernel_obj; simp add: vs_refs_def)
     apply (cases ko'; simp add: vs_refs_pages_def)
     subgoal for \<dots> arch_kernel_obja
     by (cases arch_kernel_obja;clarsimp)
    apply (cases ko'; simp add: vs_refs_pages_def)
    subgoal for \<dots> arch_kernel_obja
      apply (cases arch_kernel_obja; clarsimp)
      apply (clarsimp simp: graph_of_def split: if_splits)
      subgoal for "fun" a
        apply (cut_tac
        imageI[where
               A="{(x, y). (if x \<in> kernel_mapping_slots then None else pde_ref (fun x)) = Some y}"
               and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageDirectory), y))" and x="(a,b)"])
         apply simp
        apply (clarsimp simp: pde_ref_def pde_ref_pages_def
          split: pde.splits)
         apply (drule bspec,simp)+
         apply (simp add: valid_pde_def)
         apply (clarsimp simp: data_at_def obj_at_def a_type_def)
        apply (drule bspec, simp split: if_splits)+
      by (clarsimp simp: obj_at_def a_type_def data_at_def)
    done
  done
  done

lemma set_pd_reply_at_ppred[wp]:
  "set_pd p pt \<lbrace> \<lambda>s. P (reply_at_pred P' r s) \<rbrace>"
  by (wpsimp simp: set_pd_def wp: set_object_wp_strong get_object_wp)
     (fastforce elim!: bool_to_boolE[of P]
                 simp: obj_at_def reply_at_ppred_def
                split: kernel_object.splits if_splits)

sublocale set_pd: non_reply_op "set_pd p pt"
  by unfold_locales wp

lemma set_pd_sc_at_pred_n[wp]:
  "set_pd p pd \<lbrace> \<lambda>s. P (sc_at_pred_n N (\<lambda>sc. sc) P' r s) \<rbrace>"
  by (wpsimp simp: set_pd_def wp: set_object_wp_strong get_object_wp)
     (fastforce elim!: bool_to_boolE[of P]
                 simp: obj_at_def sc_at_pred_n_def a_type_simps
                split: kernel_object.splits if_splits)

sublocale set_pd: non_sc_op "set_pd p pt"
  by unfold_locales wp

lemma set_pd_valid_replies[wp]:
  "set_pd p pt \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

lemma set_pd_fault_tcbs_valid_states[wp]:
  "set_pd p pt \<lbrace> fault_tcbs_valid_states \<rbrace>"
  by (wpsimp wp: fault_tcbs_valid_states_lift)

lemma set_pd_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>i. wellformed_pde (pd i)) and
    (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd) s) and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) \<subseteq> vs_refs_pages ko) p and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) \<subseteq> vs_refs ko) p and
    obj_at (\<lambda>ko. \<exists>pd'. ko = ArchObj (PageDirectory pd')
                       \<and> (\<forall>x \<in> kernel_mapping_slots. pd x = pd' x)) p and
    (\<lambda>s. p \<notin> global_refs s) and
    (\<lambda>s. (obj_at (empty_table (set (second_level_tables (arch_state s)))) p s \<longrightarrow>
     empty_table (set (second_level_tables (arch_state s))) (ArchObj (PageDirectory pd))))\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_caps_def)
  apply (rule hoare_pre)
   apply (wp set_pd_valid_objs set_pd_iflive set_pd_zombies
             set_pd_zombies_state_refs set_pd_valid_mdb
             set_pd_valid_idle set_pd_ifunsafe
             set_pd_valid_arch set_pd_valid_global set_pd_cur set_pd_cur_sc_tcb
             valid_irq_node_typ set_pd_zombies_state_hyp_refs
             set_pd_vspace_objs_unmap set_pd_vs_lookup_unmap
             valid_irq_handlers_lift
             set_pd_unmap_mappings set_pd_equal_kernel_mappings_triv)
  apply simp
  done


lemma store_pde_invs_unmap:
  "\<lbrace>invs and valid_pde pde and (\<lambda>s. wellformed_pde pde)
            and K (ucast (p && mask pd_bits >> 2) \<notin> kernel_mapping_slots)
            and (\<lambda>s. p && ~~ mask pd_bits \<notin> global_refs s)
            and K (pde = InvalidPDE)\<rbrace>
  store_pde p pde \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pde_def del: split_paired_Ex)
  apply (wp set_pd_invs_unmap)
  apply (clarsimp simp del: split_paired_Ex del: exE)
  apply (rule conjI)
   apply (drule invs_valid_objs)
   apply (fastforce simp: valid_objs_def dom_def obj_at_def valid_obj_def)
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) valid_vspace_objsD, fastforce)
   apply simp
  apply (rule conjI)
   apply (clarsimp intro!: pair_imageI
                   simp: obj_at_def vs_refs_def vs_refs_pages_def map_conv_upd graph_of_def pde_ref_def pde_ref_pages_def
                   split: if_split_asm)+
  apply (clarsimp simp: empty_table_def)
  apply (cases pde, (auto simp: pde_ref_def  valid_pde_mappings_def split:if_split_asm))
  done



lemma store_pde_state_refs_of:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> store_pde ptr val \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  apply (clarsimp simp: state_refs_of_def obj_at_def)
  done

lemma store_pde_state_hyp_refs_of:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> store_pde ptr val \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  apply (clarsimp simp: state_hyp_refs_of_def obj_at_def)
  done

lemma valid_asid_map_next_asid [iff]:
  "valid_asid_map (s\<lparr>arch_state := arm_next_asid_update f (arch_state s)\<rparr>) =
  valid_asid_map s"
  by (simp add: valid_asid_map_def vspace_at_asid_def)

lemma pspace_respects_device_region_dmo:
  assumes valid_f: "\<And>P. \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> f \<lbrace>\<lambda>r ms. P (device_state ms)\<rbrace>"
  shows "\<lbrace>pspace_respects_device_region\<rbrace>do_machine_op f\<lbrace>\<lambda>r. pspace_respects_device_region\<rbrace>"
  apply (clarsimp simp: do_machine_op_def gets_def select_f_def simpler_modify_def bind_def valid_def
    get_def return_def)
  apply (drule_tac P1 = "(=) (device_state (machine_state s))" in use_valid[OF _ valid_f])
  apply auto
  done

lemma cap_refs_respects_device_region_dmo:
  assumes valid_f: "\<And>P. \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> f \<lbrace>\<lambda>r ms. P (device_state ms)\<rbrace>"
  shows "\<lbrace>cap_refs_respects_device_region\<rbrace>do_machine_op f\<lbrace>\<lambda>r. cap_refs_respects_device_region\<rbrace>"
  apply (clarsimp simp: do_machine_op_def gets_def select_f_def simpler_modify_def bind_def valid_def
    get_def return_def)
  apply (drule_tac P1 = "(=) (device_state (machine_state s))" in use_valid[OF _ valid_f])
  apply auto
  done

lemma machine_op_lift_device_state[wp]:
  "\<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> machine_op_lift f \<lbrace>\<lambda>_ ms. P (device_state ms)\<rbrace>"
  by (clarsimp simp: machine_op_lift_def NonDetMonad.valid_def bind_def
                     machine_rest_lift_def gets_def simpler_modify_def get_def return_def
                     select_def ignore_failure_def select_f_def
              split: if_splits)

crunches invalidateLocalTLB_ASID, invalidateLocalTLB_VAASID, setHardwareASID, isb, dsb,
         set_current_pd, storeWord, cleanByVA_PoU, cleanL2Range
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
  (simp: writeTTBR0_def
   ignore_del: invalidateLocalTLB_ASID invalidateLocalTLB_VAASID setHardwareASID isb
               dsb storeWord cleanByVA_PoU cleanL2Range)

lemma as_user_inv:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> as_user t f \<lbrace>\<lambda>x. P\<rbrace>"
proof -
  have P: "\<And>a b input. (a, b) \<in> fst (f input) \<Longrightarrow> b = input"
    by (rule use_valid [OF _ x], assumption, rule refl)
  have Q: "\<And>s ps. ps (kheap s) = kheap s \<Longrightarrow> kheap_update ps s = s"
    by simp
  show ?thesis
    apply (simp add: as_user_def gets_the_def assert_opt_def set_object_def get_object_def split_def)
    apply wp
    apply (clarsimp dest!: P)
    apply (subst Q)
     prefer 2
     apply assumption
    apply (rule ext)
    apply (simp add: get_tcb_def read_object_def)
    apply (case_tac "kheap s t"; simp)
    apply (case_tac a; simp)
    apply (clarsimp simp: arch_tcb_context_set_def arch_tcb_context_get_def)
    done
qed


crunches getRegister
  for inv[wp]: P
  (simp: getRegister_def)

lemmas user_getreg_inv[wp] = as_user_inv[OF getRegister_inv]

end

end
