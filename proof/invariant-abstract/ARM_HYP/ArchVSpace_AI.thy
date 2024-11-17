(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
ARM_HYP-specific VSpace invariants
*)

theory ArchVSpace_AI
imports VSpacePre_AI
begin

(* FIXME: move *)
lemma get_tcb_None_tcb_at:
  "(get_tcb p s = None) = (\<not>tcb_at p s)"
  by (auto simp: get_tcb_def obj_at_def is_tcb_def split: kernel_object.splits option.splits)

(* FIXME: move *)
lemma get_tcb_Some_ko_at:
  "(get_tcb p s = Some t) = ko_at (TCB t) p s"
  by (auto simp: get_tcb_def obj_at_def is_tcb_def split: kernel_object.splits option.splits)

context Arch begin arch_global_naming

lemma kernel_base_shift_cast_le: (* ARMHYP *)
  fixes x :: "11 word"
  shows
  "(kernel_base >> 21 \<le> ucast x) =
        (ucast (kernel_base >> 21) \<le> x)"
  apply (simp add: word_le_def)
  apply (subst uint_ucast, simp, simp add: kernel_base_def)
  apply (simp only: ucast_def)
  apply (subst word_uint.Abs_inverse)
   apply (cut_tac x=x in word_uint.Rep)
   apply (simp add: uints_num)
  apply simp
  done

sublocale
  set_vcpu: non_vspace_non_cap_non_mem_op "set_vcpu p vcpu" +
  get_vcpu: non_vspace_non_cap_non_mem_op "get_vcpu p"
  apply unfold_locales
  unfolding set_vcpu_def get_vcpu_def
  apply (wpsimp wp: set_object_non_pagetable[THEN hoare_set_object_weaken_pre] get_object_wp
                    set_object_caps_of_state[THEN hoare_set_object_weaken_pre] |
         clarsimp simp: is_tcb_def is_cap_table_def obj_at_def a_type_def
                 split: if_splits kernel_object.splits
                        arch_kernel_obj.splits)+
  done

crunch get_vcpu
  for inv[wp]: "P"

lemma set_vcpu_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wpsimp wp: set_object_typ_at)
  done

lemma modify_obj_at : "\<lbrakk>\<forall>s. kheap s p = kheap (f s) p\<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> modify f \<lbrace> \<lambda>rv s. P (obj_at P' p s)\<rbrace>"
  by (wpsimp simp: obj_at_def)

sublocale
  vcpu_disable: non_vspace_non_cap_op "vcpu_disable vcpu" +
  vcpu_enable: non_vspace_non_cap_op "vcpu_enable p" +
  vcpu_restore: non_vspace_non_cap_op "vcpu_restore p" +
  vcpu_save: non_vspace_non_cap_op "vcpu_save vcpu'"
  apply unfold_locales
  unfolding vcpu_disable_def vcpu_enable_def vcpu_restore_def vcpu_save_def
  apply (wpsimp wp: set_vcpu.vsobj_at get_vcpu.vsobj_at mapM_wp mapM_x_wp
                simp: vcpu_update_def vgic_update_def vcpu_save_reg_def vcpu_restore_reg_def
                      vcpu_restore_reg_range_def vcpu_save_reg_range_def vgic_update_lr_def
                      save_virt_timer_def vcpu_write_reg_def restore_virt_timer_def
                      vcpu_read_reg_def is_irq_active_def get_irq_state_def
         | assumption)+
  done

crunch
  vcpu_read_reg, vcpu_write_reg, vcpu_disable, vcpu_save, vcpu_enable, vcpu_restore,
  read_vcpu_register, write_vcpu_register, vcpu_switch
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (simp: assertE_def crunch_simps wp: crunch_wps ignore: do_machine_op)

crunch vcpu_read_reg
  for inv[wp]: P

(* FIXME: move to Invariant_AI *)
definition
  glob_vs_refs_arch :: "arch_kernel_obj \<Rightarrow> (vs_ref \<times> obj_ref) set"
  where  "glob_vs_refs_arch \<equiv> \<lambda>ko. case ko of
     (ASIDPool pool) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  |  (PageDirectory pd) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p))
                          ` graph_of (pde_ref o pd)
  | _ \<Rightarrow> {}"

declare glob_vs_refs_arch_def[simp]

definition
  "glob_vs_refs \<equiv> arch_obj_fun_lift glob_vs_refs_arch {}"

crunch_ignore (add: writeContextIDAndPD_impl addressTranslateS1_impl
           setSCTLR_impl setHCR_impl
           set_gic_vcpu_ctrl_vmcr_impl
           set_gic_vcpu_ctrl_apr_impl
           get_gic_vcpu_ctrl_lr_impl set_gic_vcpu_ctrl_lr_impl
           writeVCPUHardwareReg_impl
           set_gic_vcpu_ctrl_hcr_impl
           dsb_impl)

crunch do_machine_op
  for pspace_in_kerbel_window[wp]: "pspace_in_kernel_window"

lemma pspace_in_kernel_window_set_vcpu[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_vcpu p vcpu \<lbrace>\<lambda>_.pspace_in_kernel_window\<rbrace>"
  by (rule pspace_in_kernel_window_atyp_lift, wp+)

crunch vcpu_switch
  for pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  (simp: Metis.not_atomize crunch_simps a_type_def when_def
     wp: crunch_wps ignore: do_machine_op)

lemma find_free_hw_asid_pspace_in_kernel_window[wp]:
   "\<lbrace>pspace_in_kernel_window\<rbrace> find_free_hw_asid
   \<lbrace>\<lambda>_. pspace_in_kernel_window\<rbrace>"
  by (simp add: find_free_hw_asid_def invalidate_hw_asid_entry_def invalidate_asid_def
                   do_machine_op_def split_def
              cong: option.case_cong) wpsimp


crunch arm_context_switch
  for pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  (simp: crunch_simps wp: crunch_wps ignore: do_machine_op writeContextIDAndPD_impl)

crunch set_vm_root
  for pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  (simp: crunch_simps wp: crunch_wps ignore: set_current_pd writeContextIDAndPD do_machine_op)

crunch perform_page_invocation
  for pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  (simp: crunch_simps wp: crunch_wps)

definition
 "pd_at_uniq asid pd \<equiv> \<lambda>s. pd \<notin> ran ((option_map snd o arm_asid_map (arch_state s) |` (- {asid})))"


crunch find_pd_for_asid_assert
  for inv[wp]: "P"
  (simp: crunch_simps)

lemma asid_word_bits [simp]: "asid_bits < word_bits"
  by (simp add: asid_bits_def word_bits_def)


lemma asid_low_high_bits:
  "\<lbrakk> x && mask asid_low_bits = y && mask asid_low_bits;
    ucast (asid_high_bits_of x) = (ucast (asid_high_bits_of y)::word32);
    x \<le> 2 ^ asid_bits - 1; y \<le> 2 ^ asid_bits - 1 \<rbrakk>
  \<Longrightarrow> x = y"
  apply (rule word_eqI)
  apply (simp add: upper_bits_unset_is_l2p_32 [symmetric] bang_eq nth_ucast word_size)
  apply (clarsimp simp: asid_high_bits_of_def nth_ucast nth_shiftr)
  apply (simp add: asid_high_bits_def asid_bits_def asid_low_bits_def word_bits_def)
  subgoal premises prems[rule_format] for n
  apply (cases "n < 10")
   using prems(1)
   apply fastforce
  apply (cases "n < 17")
   using prems(2)[where n="n - 10"]
   apply fastforce
  using prems(3-)
  by (simp add: linorder_not_less)
  done

lemma asid_low_high_bits':
  "\<lbrakk> ucast x = (ucast y :: 10 word);
    asid_high_bits_of x = asid_high_bits_of y;
    x \<le> 2 ^ asid_bits - 1; y \<le> 2 ^ asid_bits - 1 \<rbrakk>
  \<Longrightarrow> x = y"
  by (rule asid_low_high_bits; (assumption|word_eqI_solve simp: asid_low_bits_def)?)

lemma table_cap_ref_at_eq:
  "table_cap_ref c = Some [x] \<longleftrightarrow> vs_cap_ref c = Some [x]"
  by (auto simp: table_cap_ref_def vs_cap_ref_simps vs_cap_ref_def
          split: cap.splits arch_cap.splits vmpage_size.splits option.splits)


lemma table_cap_ref_ap_eq:
  "table_cap_ref c = Some [x,y] \<longleftrightarrow> vs_cap_ref c = Some [x,y]"
  by (auto simp: table_cap_ref_def vs_cap_ref_simps vs_cap_ref_def
          split: cap.splits arch_cap.splits vmpage_size.splits option.splits)

lemma pd_at_asid_unique:
  "\<lbrakk> vspace_at_asid asid pd s; vspace_at_asid asid' pd s;
     unique_table_refs (caps_of_state s);
     valid_vs_lookup s; valid_vspace_objs s;
     valid_arch_state s; asid < 2 ^ asid_bits; asid' < 2 ^ asid_bits \<rbrakk>
       \<Longrightarrow> asid = asid'"
  apply (clarsimp simp: vspace_at_asid_def)
  apply (subgoal_tac "pd \<notin> {}")
   apply (drule(1) valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])+
   apply (clarsimp simp: table_cap_ref_ap_eq[symmetric])
   apply (clarsimp simp: table_cap_ref_def
                  split: cap.split_asm arch_cap.split_asm option.split_asm)
   apply (drule(2) unique_table_refsD,
          simp+, clarsimp simp: table_cap_ref_def,
          erule(1) asid_low_high_bits)
    apply simp+
  done

lemma pd_at_asid_unique2:
  "\<lbrakk> vspace_at_asid asid pd s; vspace_at_asid asid pd' s \<rbrakk>
         \<Longrightarrow> pd = pd'"
  apply (clarsimp simp: vspace_at_asid_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup_2ConsD vs_lookup_atD
                        vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits
                 dest!: graph_ofD)
  apply (drule ucast_up_inj, simp+)
  done


lemma pd_at_asid_uniq:
  "\<lbrakk> vspace_at_asid asid pd s; asid \<le> mask asid_bits; valid_asid_map s;
      unique_table_refs (caps_of_state s); valid_vs_lookup s;
      valid_vspace_objs s; valid_arch_state s \<rbrakk>
       \<Longrightarrow> pd_at_uniq asid pd s"
  apply (clarsimp simp: pd_at_uniq_def ran_option_map
                 dest!: ran_restrictD)
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, erule graph_ofI)
  apply clarsimp
  apply (rule pd_at_asid_unique, assumption+)
   apply (drule subsetD, erule domI)
   apply (simp add: mask_def)
  apply (simp add: mask_def)
  done


lemma find_free_hw_asid_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> find_free_hw_asid \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (simp add: find_free_hw_asid_def invalidate_hw_asid_entry_def
                   invalidate_asid_def do_machine_op_def split_def
              cong: option.case_cong)
  apply (wp|wpc|simp)+
  apply (clarsimp simp: valid_arch_state_def split: option.splits)
   apply (frule is_inv_inj)
   apply (drule findNoneD)
   apply (drule_tac x="arm_next_asid (arch_state s)" in bspec)
    apply (simp add: minBound_word)
   apply (clarsimp simp: is_inv_def ran_upd dom_option_map
                         dom_upd)
   apply (drule_tac x="x" and y="arm_next_asid (arch_state s)" in inj_onD)
      apply simp
     apply blast
    apply blast
   apply simp
  apply (frule is_inv_inj)
  apply (drule findNoneD)
  apply (drule_tac x="arm_next_asid (arch_state s)" in bspec)
   apply (simp add: minBound_word)
  apply (clarsimp simp: is_inv_def ran_upd dom_option_map
                        dom_upd)
  apply (drule_tac x="x" and y="arm_next_asid (arch_state s)" in inj_onD)
     apply simp
    apply blast
   apply blast
  apply simp
  done

lemma valid_vs_lookupE:
  "\<lbrakk> valid_vs_lookup s; \<And>ref p. (ref \<unrhd> p) s' \<Longrightarrow> (ref \<unrhd> p) s;
           {} \<subseteq> {};
           caps_of_state s = caps_of_state s' \<rbrakk>
     \<Longrightarrow> valid_vs_lookup s'"
  by (simp add: valid_vs_lookup_def, blast)

lemma find_free_hw_asid_arch_objs [wp]:
  "\<lbrace>valid_vspace_objs\<rbrace> find_free_hw_asid \<lbrace>\<lambda>asid. valid_vspace_objs\<rbrace>"
  apply (simp add: find_free_hw_asid_def invalidate_hw_asid_entry_def invalidate_asid_def
                   do_machine_op_def split_def
              cong: option.case_cong)
  apply (wp|wpc)+
  apply (simp add: valid_vspace_objs_arch_update)
  done

lemma find_free_hw_asid_pd_at_asid [wp]:
  "\<lbrace>vspace_at_asid pd asid\<rbrace> find_free_hw_asid \<lbrace>\<lambda>_. vspace_at_asid pd asid\<rbrace>"
  apply (simp add: find_free_hw_asid_def invalidate_hw_asid_entry_def invalidate_asid_def
                   do_machine_op_def split_def
              cong: option.case_cong)
  apply (wp|wpc)+
  apply (clarsimp simp: vspace_at_asid_def vs_lookup_arch_update)
  done


lemma find_free_hw_asid_pd_at_uniq [wp]:
  "\<lbrace>pd_at_uniq pd asid\<rbrace> find_free_hw_asid \<lbrace>\<lambda>_. pd_at_uniq pd asid\<rbrace>"
  apply (simp add: find_free_hw_asid_def invalidate_hw_asid_entry_def invalidate_asid_def
                   do_machine_op_def split_def
              cong: option.case_cong)
  apply (wp|wpc)+
  apply (clarsimp simp: pd_at_uniq_def ran_option_map
                 dest!: ran_restrictD split: if_split_asm)
  apply (rule ccontr, erule notE, rule image_eqI[rotated],
         rule ranI)
   apply (fastforce simp add: restrict_map_def)
  apply simp
  done


lemma load_hw_asid_wp:
  "\<lbrace>\<lambda>s. P (option_map fst (arm_asid_map (arch_state s) asid)) s\<rbrace>
         load_hw_asid asid \<lbrace>P\<rbrace>"
  apply (simp add: load_hw_asid_def)
  apply wp
  apply simp
  done


crunch find_free_hw_asid
  for aligned[wp]: pspace_aligned

crunch find_free_hw_asid
  for "distinct"[wp]: pspace_distinct


lemma invalidate_hw_asid_entry_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> invalidate_hw_asid_entry asid \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: invalidate_hw_asid_entry_def)
  apply wp
  apply (simp add: valid_asid_map_def vspace_at_asid_def)
  done





lemma invalidate_asid_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> invalidate_asid asid \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: invalidate_asid_def)
  apply wp
  apply (auto simp add: valid_asid_map_def vspace_at_asid_def graph_of_def split: if_split_asm)
  done


lemma find_free_hw_asid_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> find_free_hw_asid \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: find_free_hw_asid_def)
  apply (rule hoare_pre)
   apply (wp|wpc|simp)+
  done


lemma dmo_pd_at_asid [wp]:
  "\<lbrace>vspace_at_asid a pd\<rbrace> do_machine_op f \<lbrace>\<lambda>_. vspace_at_asid a pd\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (simp add: vspace_at_asid_def)
  done

lemma find_pd_for_asid_pd_at_asid [wp]:
  "\<lbrace>\<top>\<rbrace> find_pd_for_asid asid \<lbrace>\<lambda>pd. vspace_at_asid asid pd\<rbrace>, -"
  apply (simp add: find_pd_for_asid_def assertE_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply (clarsimp simp: vspace_at_asid_def)
  apply (rule vs_lookupI)
   apply (simp add: vs_asid_refs_def graph_of_def)
   apply fastforce
  apply (rule r_into_rtrancl)
  apply (erule vs_lookup1I)
   prefer 2
   apply (rule refl)
  apply (simp add: vs_refs_def graph_of_def mask_asid_low_bits_ucast_ucast)
  apply fastforce
  done

crunch do_machine_op
  for valid_vs_lookup2[wp]: "\<lambda>s. P (valid_vs_lookup s)"
  (ignore: get_object set_object)

lemma valid_asid_mapD:
  "\<lbrakk> arm_asid_map (arch_state s) asid = Some (vasid, pd); valid_asid_map s \<rbrakk>
      \<Longrightarrow> vspace_at_asid asid pd s \<and> asid \<le> mask asid_bits"
  by (auto simp add: valid_asid_map_def graph_of_def)


lemma page_directory_cap_pd_at_uniq:
  "\<lbrakk> cte_wp_at ((=) (cap.ArchObjectCap (arch_cap.PageDirectoryCap pd (Some asid)))) slot s;
     valid_asid_map s; valid_vs_lookup s; unique_table_refs (caps_of_state s);
     valid_arch_state s; valid_objs s \<rbrakk>
          \<Longrightarrow> pd_at_uniq asid pd s"
  apply (frule(1) cte_wp_at_valid_objs_valid_cap)
  apply (clarsimp simp: pd_at_uniq_def restrict_map_def valid_cap_def
                        elim!: ranE split: if_split_asm)
  apply (drule(1) valid_asid_mapD)
  apply (clarsimp simp: vspace_at_asid_def)
  apply (frule(1) valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])
  apply (clarsimp simp: cte_wp_at_caps_of_state dest!: obj_ref_elemD)
  apply (drule(1) unique_table_refsD[rotated, where cps="caps_of_state s"],
         simp+)
  apply (clarsimp simp: table_cap_ref_ap_eq[symmetric] table_cap_ref_def
                 split: cap.splits arch_cap.splits option.splits)
  apply (drule(1) asid_low_high_bits, simp_all add: mask_def)
  done

lemma invalidateLocalTLB_ASID_underlying_memory:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace>
   invalidateLocalTLB_ASID asid
   \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: invalidateLocalTLB_ASID_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+

lemma isb_underlying_memory[wp]:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace>
   isb
   \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: isb_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+

lemma dsb_underlying_memory[wp]:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace>
   dsb
   \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: dsb_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+

lemma dmb_underlying_memory[wp]:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace>
   dmb
   \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: dmb_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+

lemma invalidateLocalTLB_underlying_memory:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace>
   invalidateLocalTLB
   \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: invalidateLocalTLB_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+

lemmas invalidateLocalTLB_ASID_irq_masks = no_irq[OF no_irq_invalidateLocalTLB_ASID]

lemma dmo_invalidateLocalTLB_ASID_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (invalidateLocalTLB_ASID asid) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule invalidateLocalTLB_ASID_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ invalidateLocalTLB_ASID_irq_masks])
  done

lemma load_hw_asid_invs[wp]: "\<lbrace>invs\<rbrace> load_hw_asid asid \<lbrace>\<lambda>y. invs\<rbrace>"
  by (simp add: load_hw_asid_def) wp

lemma invalidate_tlb_by_asid_invs[wp]:
  "\<lbrace>invs\<rbrace> invalidate_tlb_by_asid asid \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp simp: invalidate_tlb_by_asid_def)+
  apply (rule_tac Q'="K invs" in hoare_post_imp)
  apply (wpsimp simp: load_hw_asid_invs)+
  done

crunch flush_space
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"


lemmas flush_space_typ_ats [wp] = abs_typ_at_lifts [OF flush_space_typ_at]


crunch flush_space
  for cur_tcb[wp]: cur_tcb


crunch flush_space
  for valid_arch[wp]: valid_arch_state

crunch flush_space
  for valid_objs[wp]: valid_objs


lemma invalidate_hw_asid_vspace_objs [wp]:
  "\<lbrace>valid_vspace_objs\<rbrace> invalidate_hw_asid_entry asid \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (simp add: invalidate_hw_asid_entry_def)
  apply wp
  apply (simp add: valid_vspace_objs_arch_update)
  done

lemma invalidate_hw_asid_entry_pd_at_asid_uniq[wp]:
  "\<lbrace>vspace_at_asid asid pd\<rbrace>
     invalidate_hw_asid_entry y
   \<lbrace>\<lambda>rv. vspace_at_asid asid pd\<rbrace>"
  "\<lbrace>pd_at_uniq asid pd\<rbrace>
     invalidate_hw_asid_entry y
   \<lbrace>\<lambda>rv. pd_at_uniq asid pd\<rbrace>"
 by (simp add: vspace_at_asid_def pd_at_uniq_def
               invalidate_hw_asid_entry_def
          | wp)+


lemma invalidate_hw_asid_entry_pd_still_uniq[wp]:
  "\<lbrace>\<lambda>s. \<forall>pd. vspace_at_asid asid pd s \<longrightarrow> pd_at_uniq asid pd s\<rbrace>
     invalidate_hw_asid_entry y
   \<lbrace>\<lambda>rv s. \<forall>pd. vspace_at_asid asid pd s \<longrightarrow> pd_at_uniq asid pd s\<rbrace>"
   (* this could be generalised to other functions on pd_at_* *)
  apply (simp add: vspace_at_asid_def pd_at_uniq_def
                   invalidate_hw_asid_entry_def)
  apply (wp | simp)+
  done

lemma invalidate_asid_entry_arch_state [wp]:
  "\<lbrace>valid_arch_state\<rbrace> invalidate_asid_entry asid \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (simp add: invalidate_asid_entry_def invalidate_asid_def invalidate_hw_asid_entry_def)
  apply (wp load_hw_asid_wp)
  apply (clarsimp simp: valid_arch_state_def is_inv_None_upd comp_upd_simp
                  simp del: fun_upd_apply split: option.split)
  done

lemma flush_space_asid_map[wp]:
  "\<lbrace>valid_asid_map\<rbrace> flush_space space \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: flush_space_def)
  apply (wp load_hw_asid_wp | wpc | simp | rule_tac Q'="\<lambda>_. valid_asid_map" in hoare_strengthen_post)+
  done


crunch invalidate_asid_entry
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"


lemmas invalidate_asid_entry_typ_ats [wp] =
  abs_typ_at_lifts [OF invalidate_asid_entry_typ_at]


crunch invalidate_asid_entry
  for cur[wp]: cur_tcb


crunch invalidate_asid_entry
  for valid_objs[wp]: valid_objs


lemma invalidate_asid_entry_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> invalidate_asid_entry asid \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: invalidate_asid_entry_def invalidate_asid_def invalidate_hw_asid_entry_def)
  apply (wp load_hw_asid_wp)
  apply (clarsimp simp: valid_asid_map_def simp del: fun_upd_apply None_upd_eq)
  apply (clarsimp simp: vspace_at_asid_def vs_lookup_arch_update)
  apply blast
  done


crunch invalidate_asid_entry
  for obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"



lemma invalidate_asid_entry_invalidates:
  "\<lbrace>valid_asid_map and valid_arch_state and K (asid \<le> mask asid_bits) and
    (\<lambda>s. arm_asid_table (arch_state s) (asid_high_bits_of asid) = Some ap)\<rbrace>
   invalidate_asid_entry asid
   \<lbrace>\<lambda>rv s. \<forall>asida. asida \<le> mask asid_bits \<longrightarrow>
              ucast asida = (ucast asid :: 10 word) \<longrightarrow>
              arm_asid_table (arch_state s) (asid_high_bits_of asida) =
                Some ap \<longrightarrow>
              arm_asid_map (arch_state s) asida = None\<rbrace>"
  apply (simp add: invalidate_asid_entry_def invalidate_asid_def invalidate_hw_asid_entry_def)
  apply (wp load_hw_asid_wp)
  apply (clarsimp simp del: None_upd_eq)
  apply (rule drop_imp)
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
  apply (drule_tac x="asid_high_bits_of asid" and y="asid_high_bits_of asida" in inj_onD)
     apply simp
    apply blast
   apply blast
  apply clarsimp
  apply (drule asid_low_high_bits', simp)
    apply (fastforce simp: mask_def)
   apply (fastforce simp: mask_def)
  apply (erule (1) notE)
  done

crunch invalidate_asid_entry
  for vspace_objs[wp]: valid_vspace_objs
  (simp: valid_vspace_objs_arch_update)


lemma flush_space_pd_at_asid [wp]:
  "\<lbrace>vspace_at_asid a pd\<rbrace> flush_space asid \<lbrace>\<lambda>_. vspace_at_asid a pd\<rbrace>"
  apply (simp add: flush_space_def)
  apply (wp load_hw_asid_wp|wpc|rule_tac Q'="\<lambda>_. vspace_at_asid a pd" in hoare_strengthen_post|simp)+
  done


crunch flush_space
  for obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"


lemma flush_space_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> flush_space asid \<lbrace>\<lambda>rv s. P (arch_state s)\<rbrace>"
  apply (simp add: flush_space_def)
  apply (wp load_hw_asid_wp|wpc)+
  apply simp
  done


crunch invalidate_asid_entry
  for aligned[wp]: pspace_aligned

crunch invalidate_asid_entry
  for "distinct"[wp]: pspace_distinct

crunch flush_space
  for aligned[wp]: pspace_aligned

crunch flush_space
  for "distinct"[wp]: pspace_distinct


crunch invalidate_asid_entry
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"


lemma pd_at_asid_arch_up':
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s)
    \<Longrightarrow> vspace_at_asid asid pd (arch_state_update f s) = vspace_at_asid asid pd s"
  by (clarsimp simp add: vspace_at_asid_def vs_lookup_def vs_lookup1_def)


lemma pd_at_asid_arch_up:
  "vspace_at_asid asid pd (s\<lparr>arch_state := arch_state s \<lparr>arm_asid_map := a, arm_hwasid_table := b\<rparr>\<rparr>) =
  vspace_at_asid asid pd s"
  by (simp add: pd_at_asid_arch_up')


lemma invalidate_asid_entry_invs [wp]:
  "\<lbrace>invs\<rbrace> invalidate_asid_entry asid \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invalidate_asid_entry_def invalidate_asid_def
                   invalidate_hw_asid_entry_def)
  apply (rule hoare_pre, wp load_hw_asid_wp)
  apply (clarsimp simp del: fun_upd_apply)
  apply (clarsimp simp: invs_def valid_state_def valid_irq_node_def
                        valid_arch_caps_def valid_table_caps_def
                        valid_kernel_mappings_def valid_global_vspace_mappings_def
                        valid_global_refs_def global_refs_def
                        valid_vs_lookup_def valid_global_objs_def
                        vs_lookup_arch_update vs_lookup_pages_arch_update
                        valid_vspace_objs_def valid_arch_state_def
                  simp del: fun_upd_apply split: option.split)
  apply (rule conjI; clarsimp; rule conjI)
   apply (clarsimp simp: comp_upd_simp is_inv_None_upd)
   apply (clarsimp simp: valid_asid_map_def valid_machine_state_def)
   apply (rule conjI)
    apply (erule order_trans[rotated], clarsimp)
   apply (simp add: pd_at_asid_arch_up')
  apply (clarsimp simp: comp_upd_simp)
   apply (clarsimp simp: comp_upd_simp is_inv_None_upd)
  apply (clarsimp simp: valid_asid_map_def valid_machine_state_def)
  apply (rule conjI)
   apply (erule order_trans[rotated], clarsimp)
  apply (simp add: pd_at_asid_arch_up')
  done

lemmas cleanCaches_PoU_irq_masks = no_irq[OF no_irq_cleanCaches_PoU]

lemmas ackInterrupt_irq_masks = no_irq[OF no_irq_ackInterrupt]

lemmas setIRQTrigger_irq_masks = no_irq[OF no_irq_setIRQTrigger]

lemma invalidate_I_PoU_underlying_memory[wp]:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace>
   invalidate_I_PoU
   \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: invalidate_I_PoU_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+

lemma clean_D_PoU_underlying_memory[wp]:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace>
   clean_D_PoU
   \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: clean_D_PoU_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+

crunch dsb, invalidate_I_PoU, clean_D_PoU, cleanCaches_PoU
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
  and underlying_memory_inv[wp]: "\<lambda>ms. P (underlying_memory ms)"
  (ignore_del: dsb invalidate_I_PoU clean_D_PoU cleanCaches_PoU)

lemma dmo_cleanCaches_PoU_invs[wp]: "\<lbrace>invs\<rbrace> do_machine_op cleanCaches_PoU \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply clarsimp
  apply safe
  apply (simp add: use_valid[OF _ cleanCaches_PoU_underlying_memory_inv[where P="\<lambda>x. x = v" for v]])
  apply(erule(1) use_valid[OF _ cleanCaches_PoU_irq_masks])
  done

lemma flush_space_invs[wp]: "\<lbrace>invs\<rbrace> flush_space asid \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wpsimp simp: flush_space_def)
  apply (rule_tac Q'="K invs" in hoare_post_imp, wpsimp+)
  done

crunch flush_space
  for valid_vs_lookup[wp]: "valid_vs_lookup"

crunch flush_space
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"


lemma ucast_ucast_low_bits:
  fixes x :: word32
  shows "x \<le> 2^asid_low_bits - 1 \<Longrightarrow> ucast (ucast x:: 10 word) = x"
  apply (simp add: ucast_ucast_mask)
  apply (rule less_mask_eq)
  apply (subst (asm) word_less_sub_le)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply (simp add: asid_low_bits_def)
  done


lemma asid_high_bits_of_or:
 "x \<le> 2^asid_low_bits - 1 \<Longrightarrow> asid_high_bits_of (base || x) = asid_high_bits_of base"
  apply (rule word_eqI)
  apply (drule le_2p_upper_bits)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply (simp add: asid_high_bits_of_def word_size nth_ucast nth_shiftr asid_low_bits_def word_bits_def)
  done


crunch invalidate_asid_entry
  for vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"

crunch flush_space
  for vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"


lemma vs_lookup_clear_asid_table:
  "(rf \<rhd> p) (s\<lparr>arch_state := arch_state s
                \<lparr>arm_asid_table := (arm_asid_table (arch_state s))
                   (pptr := None)\<rparr>\<rparr>)
        \<longrightarrow> (rf \<rhd> p) s"
  apply (simp add: vs_lookup_def vs_lookup1_def)
  apply (rule impI, erule subsetD[rotated])
  apply (rule Image_mono[OF order_refl])
  apply (simp add: vs_asid_refs_def graph_of_def)
  apply (rule image_mono)
  apply (clarsimp split: if_split_asm)
  done


lemma vs_lookup_pages_clear_asid_table:
  "(rf \<unrhd> p) (s\<lparr>arch_state := arch_state s
                \<lparr>arm_asid_table := (arm_asid_table (arch_state s))
                   (pptr := None)\<rparr>\<rparr>)
   \<Longrightarrow> (rf \<unrhd> p) s"
  apply (simp add: vs_lookup_pages_def vs_lookup_pages1_def)
  apply (erule subsetD[rotated])
  apply (rule Image_mono[OF order_refl])
  apply (simp add: vs_asid_refs_def graph_of_def)
  apply (rule image_mono)
  apply (clarsimp split: if_split_asm)
  done


lemma valid_arch_state_unmap_strg:
  "valid_arch_state s \<longrightarrow>
   valid_arch_state(s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
  apply (rule conjI)
   apply (clarsimp simp add: ran_def)
   apply blast
  apply (clarsimp simp: inj_on_def split: option.split)
  done

lemma valid_vspace_objs_unmap_strg:
  "valid_vspace_objs s \<longrightarrow>
   valid_vspace_objs(s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vspace_objs_def)
  apply (drule vs_lookup_clear_asid_table [rule_format])
  apply blast
  done


lemma valid_vs_lookup_unmap_strg:
  "valid_vs_lookup s \<longrightarrow>
   valid_vs_lookup(s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vs_lookup_def)
  apply (drule vs_lookup_pages_clear_asid_table)
  apply blast
  done


lemma ex_asid_high_bits_plus:
  "asid \<le> mask asid_bits \<Longrightarrow> \<exists>x \<le> 2^asid_low_bits - 1. asid = (ucast (asid_high_bits_of asid) << asid_low_bits) + x"
  apply (rule_tac x="asid && mask asid_low_bits" in exI)
  apply (rule conjI)
   apply (simp add: mask_def)
   apply (rule word_and_le1)
  apply (subst (asm) mask_def)
  apply (simp add: upper_bits_unset_is_l2p_32 [symmetric])
  apply (subst word_plus_and_or_coroll; word_eqI)
  apply (clarsimp simp: asid_high_bits_of_def asid_low_bits_def word_bits_def asid_bits_def)
  apply (rule iffI)
   prefer 2
   apply fastforce
  apply (clarsimp simp: linorder_not_less)
  by (metis add_One_commute add_diff_inverse_nat le_add1 less_diff_conv2 less_imp_diff_less
            numeral_plus_numeral semiring_norm(10) semiring_norm(2) semiring_norm(3)
            semiring_norm(4) semiring_norm(9))


lemma asid_high_bits_shl:
  "\<lbrakk> is_aligned base asid_low_bits; base \<le> mask asid_bits \<rbrakk> \<Longrightarrow> ucast (asid_high_bits_of base) << asid_low_bits = base"
  apply (simp add: mask_def upper_bits_unset_is_l2p_32 [symmetric])
  apply word_eqI
  apply (simp add: asid_low_bits_def asid_high_bits_of_def word_bits_conv asid_bits_def)
  apply (rule iffI, clarsimp)
  apply (rule context_conjI)
   apply (clarsimp simp add: linorder_not_less [symmetric])
  apply simp
  by (metis less_imp_le_nat linorder_neqE_nat nat_diff_less numeral_plus_numeral pl_pl_rels
            semiring_norm(10) semiring_norm(2) semiring_norm(3) semiring_norm(8) semiring_norm(9)
            trans_less_add1)


lemma valid_asid_map_unmap:
  "valid_asid_map s \<and> is_aligned base asid_low_bits \<and> base \<le> mask asid_bits \<and>
   (\<forall>x \<in> set [0.e.2^asid_low_bits - 1]. arm_asid_map (arch_state s) (base + x) = None) \<longrightarrow>
   valid_asid_map(s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (arm_asid_table (arch_state s))(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_asid_map_def vspace_at_asid_def)
  apply (drule bspec, blast)
  apply clarsimp
  apply (erule vs_lookupE)
  apply (clarsimp simp: vs_asid_refs_def dest!: graph_ofD)
  apply (frule vs_lookup1_trans_is_append, clarsimp)
  apply (drule ucast_up_inj, simp)
  apply clarsimp
  apply (rule_tac ref'="([VSRef (ucast (asid_high_bits_of a)) None],ba)" in vs_lookupI)
   apply (simp add: vs_asid_refs_def)
   apply (simp add: graph_of_def)
   apply (rule_tac x="(asid_high_bits_of a, ba)" in image_eqI)
    apply simp
   apply clarsimp
   apply (subgoal_tac "a \<le> mask asid_bits")
    prefer 2
    apply fastforce
   apply (drule_tac asid=a in ex_asid_high_bits_plus)
   apply (clarsimp simp: asid_high_bits_shl)
  apply (drule rtranclD, simp)
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (frule vs_lookup1_trans_is_append, clarsimp)
  apply (drule vs_lookup_trans_ptr_eq, clarsimp)
  apply (rule r_into_rtrancl)
  apply (rule vs_lookup1I)
    apply simp
   apply assumption
  apply simp
  done


lemma invalidate_asid_entry_asid_map_None_inv:
  "\<lbrace>\<lambda>s. arm_asid_map (arch_state s) y = None\<rbrace>
  invalidate_asid_entry (base + x)
  \<lbrace>\<lambda>_ s. arm_asid_map (arch_state s) y = None\<rbrace>"
  apply (simp add: invalidate_asid_entry_def invalidate_asid_def
                   invalidate_hw_asid_entry_def)
  apply (wp load_hw_asid_wp)
  apply simp
  done


lemma mapM_invalidate:
  "\<lbrace>[VSRef (ucast (asid_high_bits_of base)) None] \<rhd> ptr and
    ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) ptr and
    valid_asid_map and K (is_aligned base asid_low_bits)\<rbrace>
       mapM (\<lambda>offset. when (\<exists>y. pool (ucast offset) = Some y)
                       (do y \<leftarrow> flush_space (base + offset);
                           invalidate_asid_entry (base + offset)
                        od))
        [0.e.2 ^ asid_low_bits - 1]
       \<lbrace>\<lambda>rv s. \<forall>x\<le>2 ^ asid_low_bits - 1. arm_asid_map (arch_state s) (base + x) = None\<rbrace>"
proof -
  have ball: "\<And>P w::word32. (\<forall>x\<le>w. P x) = (\<forall>x \<in> set [0.e.w]. P x)" by simp
  show ?thesis
    apply (subst ball)
    apply (rule mapM_set)
      apply (wp, simp)
     apply (wp |
            simp add: invalidate_asid_entry_def invalidate_asid_def
                      invalidate_hw_asid_entry_def
                 cong: if_cong)+
     apply clarsimp
     apply (rule ccontr)
     apply clarsimp
     apply (clarsimp simp: valid_asid_map_def)
     apply (drule bspec, erule graph_ofI)
     apply (erule vs_lookup_atE)
     apply (clarsimp simp: vspace_at_asid_def)
     apply (drule vs_lookup_2ConsD)
     apply clarsimp
     apply (erule vs_lookup_atE)
     apply (drule vs_lookup1D)
     apply clarsimp
     apply (subgoal_tac "p' = ptr")
      apply (clarsimp simp: obj_at_def vs_refs_def graph_of_def)
      apply (subgoal_tac "base + x && mask asid_low_bits = x")
       apply (simp add: ucast_ucast_mask)
       apply (subgoal_tac "aa && mask 32 = aa")
        apply simp
       apply (rule word_eqI)
       apply (simp add: word_size)
      apply (subst add_mask_eq, assumption+)
       apply (simp add: asid_low_bits_def word_bits_def)
      apply (rule refl)
     apply (subst (asm) asid_high_bits_of_add, assumption+)
     apply simp
    apply (wp invalidate_asid_entry_asid_map_None_inv)
    apply simp
    done
qed


lemma asid_low_bits_word_bits:
  "asid_low_bits < word_bits"
  by (simp add: asid_low_bits_def word_bits_def)

crunch invalidate_hw_asid_entry
  for valid_vs_lookup[wp]: "valid_vs_lookup"
  (simp: valid_vs_lookup_def)

crunch invalidate_asid
  for valid_vs_lookup[wp]: "valid_vs_lookup"
  (simp: valid_vs_lookup_def)

crunch invalidate_asid_entry
  for valid_vs_lookup[wp]: "valid_vs_lookup"


crunch invalidate_asid_entry
  for arm_asid_table_inv[wp]: "\<lambda>s. P (arm_asid_table (arch_state s))"


crunch find_free_hw_asid
  for pred_tcb_at_P[wp]: "\<lambda>s. P (pred_tcb_at proj Q p s)"


lemma hw_asid_Some [wp]:
  "\<lbrace>valid_asid asid\<rbrace>
  load_hw_asid asid
  \<lbrace>\<lambda>rv s. \<exists>y. rv = Some y\<rbrace>"
  by (simp add: load_hw_asid_def, wp) (simp add: valid_asid_def)

crunch set_vm_root_for_flush
  for typ_at [wp]: "\<lambda>s. P (typ_at T p s)"
  and cur [wp]: cur_tcb
  and valid_objs [wp]: valid_objs
  and aligned [wp]: pspace_aligned

lemmas set_vm_root_for_flush_typ_ats [wp] = abs_typ_at_lifts [OF set_vm_root_for_flush_typ_at]

lemma store_hw_asid_valid_arch:
  "\<lbrace>valid_arch_state and
    (\<lambda>s. arm_asid_map (arch_state s) asid = None \<and>
         arm_hwasid_table (arch_state s) hw_asid = None)\<rbrace>
  store_hw_asid asid hw_asid
  \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  including no_pre apply (wpsimp simp: store_hw_asid_def)
  apply (simp add: valid_arch_state_def fun_upd_def[symmetric]
                   comp_upd_simp
              split: option.split)
  apply (rule hoare_pre, (wp|wpc)+)
  apply (rule conjI; clarsimp)
   apply (frule is_inv_NoneD[rotated])
    apply simp
   apply (simp add: ran_def)
   apply (simp add: is_inv_def)
  apply (frule is_inv_NoneD[rotated])
   apply simp
  apply (simp add: ran_def)
  apply (simp add: is_inv_def)
  done


lemma invalidate_hw_asid_None [wp]:
  "\<lbrace>\<top>\<rbrace> invalidate_hw_asid_entry hw_asid \<lbrace>\<lambda>_ s. arm_hwasid_table (arch_state s) hw_asid = None\<rbrace>"
  apply (simp add: invalidate_hw_asid_entry_def)
  apply wp
  apply simp
  done


lemma find_free_hw_asid_None_hw [wp]:
  "\<lbrace>\<top>\<rbrace> find_free_hw_asid \<lbrace>\<lambda>rv s. arm_hwasid_table (arch_state s) rv = None\<rbrace>"
  apply (simp add: find_free_hw_asid_def)
  apply (wp|wpc|simp)+
  apply (clarsimp dest!: findSomeD)
  done


lemma find_free_hw_asid_None_asid_map [wp]:
  "\<lbrace>\<lambda>s. arm_asid_map (arch_state s) asid = None\<rbrace>
  find_free_hw_asid
  \<lbrace>\<lambda>rv s. arm_asid_map (arch_state s) asid = None\<rbrace>"
  apply (simp add: find_free_hw_asid_def invalidate_hw_asid_entry_def invalidate_asid_def
              cong: option.case_cong)
  apply (wp|wpc|simp)+
  done


lemma get_hw_asid_valid_arch:
  "\<lbrace>valid_arch_state\<rbrace> get_hw_asid asid \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (simp add: get_hw_asid_def)
  apply (wp load_hw_asid_wp store_hw_asid_valid_arch|wpc)+
  apply simp
  done


crunch set_vm_root_for_flush
  for valid_arch[wp]: valid_arch_state


lemma svmrff_asid_mapped [wp]:
  "\<lbrace>valid_asid asid\<rbrace>
  set_vm_root_for_flush pd asid
  \<lbrace>\<lambda>rv. valid_asid asid\<rbrace>"
  apply (simp add: set_vm_root_for_flush_def arm_context_switch_def
                   get_hw_asid_def store_hw_asid_def find_free_hw_asid_def
                   load_hw_asid_def
              cong: if_cong option.case_cong)
  apply (wpsimp simp: valid_asid_def)+
   apply (wp hoare_vcg_all_lift hoare_drop_imps)+
  apply (simp add: valid_asid_def)
  done


crunch set_vm_root_for_flush
  for vspace_at_asid[wp]: "vspace_at_asid asid pd"
  (simp: pd_at_asid_arch_up)


lemma find_pd_for_asid_assert_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. vspace_at_asid asid pd s \<and> asid \<noteq> 0 \<longrightarrow> P pd s\<rbrace> find_pd_for_asid_assert asid \<lbrace>P\<rbrace>"
  apply (simp add: find_pd_for_asid_assert_def
                   find_pd_for_asid_def assertE_def
                 split del: if_split)
  apply (rule hoare_pre)
   apply (wp get_pde_wp get_asid_pool_wp | wpc)+
  apply clarsimp
  apply (drule spec, erule mp)
  apply (clarsimp simp: vspace_at_asid_def word_neq_0_conv)
  apply (rule vs_lookupI)
   apply (simp add: vs_asid_refs_def)
   apply (rule image_eqI[OF refl])
   apply (erule graph_ofI)
  apply (rule r_into_rtrancl, simp)
  apply (erule vs_lookup1I)
   apply (simp add: vs_refs_def)
   apply (rule image_eqI[rotated])
    apply (erule graph_ofI)
   apply simp
  apply (simp add: mask_asid_low_bits_ucast_ucast)
  done


lemma store_hw_asid_asid_map [wp]:
  "\<lbrace>valid_asid_map and K (asid \<le> mask asid_bits)\<rbrace>
  store_hw_asid asid hw_asid \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: store_hw_asid_def)
  apply (wp find_pd_for_asid_assert_wp)
  apply (clarsimp simp: valid_asid_map_def fun_upd_def[symmetric]
                        pd_at_asid_arch_up)
  done


lemma arm_context_switch_asid_map [wp]:
  "\<lbrace>valid_asid_map and K (asid \<le> mask asid_bits)\<rbrace>
  arm_context_switch pd asid \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: arm_context_switch_def get_hw_asid_def)
  apply (wp load_hw_asid_wp|wpc|simp)+
  done


lemma set_vm_root_for_flush_asid_map [wp]:
  "\<lbrace>valid_asid_map and K (asid \<le> mask asid_bits)\<rbrace>
  set_vm_root_for_flush pd asid \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: set_vm_root_for_flush_def)
  apply (wp|wpc|simp)+
   apply (rule hoare_strengthen_post [where
               Q'="\<lambda>_. valid_asid_map and K (asid \<le> mask asid_bits)"])
    apply wp
   apply simp
  apply wp
  apply simp
  done


crunch set_vm_root_for_flush
  for distinct [wp]: pspace_distinct
  and caps_of_state [wp]: "\<lambda>s. P (caps_of_state s)"

lemma valid_vs_lookup_arch_update:
  "arm_asid_table (f (arch_state s)) = arm_asid_table (arch_state s)
     \<Longrightarrow> valid_vs_lookup (arch_state_update f s) = valid_vs_lookup s"
  by (simp add: valid_vs_lookup_def vs_lookup_pages_arch_update)

crunch set_vm_root_for_flush
  for valid_vs_lookup[wp]: valid_vs_lookup
  and vspace_objs [wp]: valid_vspace_objs
  (simp: valid_vs_lookup_arch_update valid_vspace_objs_arch_update)

crunch set_vm_root, vcpu_switch, flush_table
  for typ_at [wp]: "\<lambda>s. P (typ_at T p s)"
  (simp: assertE_def crunch_simps wp: crunch_wps ignore: do_machine_op)


lemmas flush_table_typ_ats [wp] = abs_typ_at_lifts [OF flush_table_typ_at]

lemmas find_pd_for_asid_typ_ats [wp] = abs_typ_at_lifts [OF find_pd_for_asid_inv]

lemma set_vcpu_pspace_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_aligned[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: obj_at_def get_object_def)
  done

crunch vcpu_save, vcpu_disable, set_vm_root, flush_table
  for aligned [wp]: pspace_aligned
  (simp: crunch_simps wp: crunch_wps)

lemma find_pd_for_asid_page_directory [wp]:
  "\<lbrace>valid_vspace_objs\<rbrace>
  find_pd_for_asid asid
  \<lbrace>\<lambda>pd. page_directory_at pd\<rbrace>, -"
  apply (simp add: find_pd_for_asid_def assertE_def whenE_def split del: if_split)
  apply (wp|wpc|clarsimp|rule conjI)+
  apply (drule vs_lookup_atI)
  apply (drule (2) valid_vspace_objsD)
  apply clarsimp
  apply (drule bspec, blast)
  apply (clarsimp simp: obj_at_def)
  done


lemma find_pd_for_asid_lookup_ref:
  "\<lbrace>\<top>\<rbrace> find_pd_for_asid asid \<lbrace>\<lambda>pd. ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                                      VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd)\<rbrace>, -"
  apply (simp add: find_pd_for_asid_def assertE_def whenE_def split del: if_split)
  apply (wp|wpc|clarsimp|rule conjI)+
  apply (drule vs_lookup_atI)
  apply (erule vs_lookup_step)
  apply (erule vs_lookup1I [OF _ _ refl])
  apply (simp add: vs_refs_def)
  apply (rule image_eqI[rotated], erule graph_ofI)
  apply (simp add: mask_asid_low_bits_ucast_ucast)
  done


lemma find_pd_for_asid_lookup[wp]:
  "\<lbrace>\<top>\<rbrace> find_pd_for_asid asid \<lbrace>\<lambda>pd. \<exists>\<rhd> pd\<rbrace>,-"
  apply (rule hoare_strengthen_postE_R, rule find_pd_for_asid_lookup_ref)
  apply auto
  done

lemma find_pd_for_asid_pde [wp]:
  "\<lbrace>valid_vspace_objs and pspace_aligned\<rbrace>
  find_pd_for_asid asid
  \<lbrace>\<lambda>pd. pde_at (pd + (vptr >> pageBits + pt_bits - pte_bits << pde_bits))\<rbrace>, -"
proof -
  have x:
    "\<lbrace>valid_vspace_objs and pspace_aligned\<rbrace> find_pd_for_asid asid
     \<lbrace>\<lambda>pd. pspace_aligned and page_directory_at pd\<rbrace>, -"
    by (rule hoare_pre) (wp, simp)
  show ?thesis
    apply (rule hoare_strengthen_postE_R, rule x)
    apply clarsimp
    apply (erule page_directory_pde_atI)
     prefer 2
     apply assumption
    apply (rule vptr_shiftr_le_2p_gen)
    done
qed

lemma set_vcpu_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_obj t (ArchObj (VCPU vcpu))\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_valid_objs)
  done

lemma do_machine_op_valid_obj[wp]: "\<lbrace>valid_obj t obj\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_obj t obj\<rbrace>"
  by (rule valid_obj_typ) wp

lemma get_vcpu_valid[wp]: "\<lbrace>valid_objs\<rbrace> get_vcpu t \<lbrace>\<lambda>r. valid_obj t (ArchObj (VCPU r))\<rbrace>"
  apply (wpsimp simp: get_vcpu_def)
  apply (rule hoare_allI)
  apply (subst eq_commute)
  apply (subst (2) eq_commute)
  apply simp
  apply (rule hoare_drop_imp)+
  apply wpsimp+
  done

lemma get_vcpu_valid'[wp]:
  fixes val :: "'a::state_ext state"
  assumes valid_vcpu_eq: "\<And>x. valid_vcpu (P x) = (valid_vcpu x :: 'a state \<Rightarrow> bool)"
  shows "\<lbrace>valid_objs :: 'a state \<Rightarrow> bool\<rbrace> get_vcpu t \<lbrace>\<lambda>r. valid_obj t (ArchObj (VCPU (P r)))\<rbrace>"
  apply (simp add: get_vcpu_def valid_obj_def[abs_def] valid_vcpu_eq)
  apply (wp | wpc | clarsimp)+
  apply (subst valid_obj_def[of t "ArchObj (VCPU _)", simplified, symmetric])
  apply (rule hoare_allI)
  apply (subst eq_commute)
  apply (subst (2) eq_commute)
  apply simp
  apply (rule hoare_drop_imp)+
  apply wpsimp+
  done

lemma valid_obj_valid_vcpu:
  "\<lbrace>valid_vcpu vcpu\<rbrace> F \<lbrace>\<lambda>r. valid_vcpu (P r vcpu)\<rbrace>
   \<Longrightarrow> \<lbrace>valid_obj t (ArchObj (VCPU vcpu))\<rbrace> F \<lbrace>\<lambda>r. valid_obj t (ArchObj (VCPU (P r vcpu)))\<rbrace>"
  by (simp add: valid_obj_def[abs_def])

lemma valid_vcpu_typ_at:
  "\<lbrakk>\<And>x. vcpu_tcb (P x vcpu) = vcpu_tcb vcpu;
    \<And>a. \<lbrace>typ_at ATCB a\<rbrace> F \<lbrace>\<lambda>r. typ_at ATCB a\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>valid_vcpu vcpu\<rbrace> F \<lbrace>\<lambda>r. valid_vcpu (P r vcpu )\<rbrace>"
  by (wpsimp simp: valid_vcpu_def split: option.splits)

crunch vgic_update_lr, vcpu_write_reg, vcpu_save_reg, vcpu_disable, vcpu_restore,
          save_virt_timer, restore_virt_timer, vcpu_save, vcpu_switch, vcpu_save_reg_range
  for valid_objs[wp]: valid_objs
  (ignore: vcpu_update simp: vcpu_update_def valid_vcpu_def wp: crunch_wps)

crunch flush_page
  for valid_objs[wp]: "valid_objs"
  (wp: crunch_wps hoare_drop_imps simp: crunch_simps)

lemma arch_thread_set_is_thread_set:
  "arch_thread_set f t = thread_set (tcb_arch_update f) t"
  by (simp add: thread_set_def arch_thread_set_def cong: tcb.fold_congs)

lemma arch_thread_set_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> arch_thread_set f t \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  by (wpsimp wp: thread_set_caps_of_state_trivial2 simp: arch_thread_set_is_thread_set)

lemma arch_thread_set_wp:
  "\<lbrace>\<lambda>s. get_tcb p s \<noteq> None \<longrightarrow> Q (s\<lparr>kheap := (kheap s)(p \<mapsto> TCB (the (get_tcb p s)\<lparr>tcb_arch := f (tcb_arch (the (get_tcb p s)))\<rparr>))\<rparr>) \<rbrace>
    arch_thread_set f p
   \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_wp)
  apply simp
  done

lemma a_type_VCPU [simp]:
  "a_type (ArchObj (VCPU v)) = AArch AVCPU"
  by (simp add: a_type_def)

lemma set_vcpu_wp:
  "\<lbrace>\<lambda>s. vcpu_at p s \<longrightarrow> Q (s\<lparr>kheap := (kheap s)(p \<mapsto> (ArchObj (VCPU vcpu))) \<rparr>) \<rbrace> set_vcpu p vcpu \<lbrace>\<lambda>_. Q\<rbrace>"
  unfolding set_vcpu_def
  apply (wp set_object_wp_strong)
  apply (clarsimp simp: obj_at_def split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma get_vcpu_wp:
  "\<lbrace>\<lambda>s. \<forall>v. ko_at (ArchObj (VCPU v)) p s \<longrightarrow> Q v s\<rbrace> get_vcpu p \<lbrace>Q\<rbrace>"
  by (wpsimp simp: get_vcpu_def wp: get_object_wp)

lemma arch_thread_get_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at (TCB tcb) t s \<longrightarrow> Q (f (tcb_arch tcb)) s\<rbrace> arch_thread_get f t \<lbrace>Q\<rbrace>"
  apply (wpsimp simp: arch_thread_get_def)
  apply (auto dest!: get_tcb_ko_atD)
  done

lemma set_vcpu_valid_arch_state_hyp_live:
  "\<lbrace>valid_arch_state and K (hyp_live (ArchObj (VCPU vcpu)))\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (simp add: valid_arch_state_def)
  apply (wp set_vcpu_wp)
  apply (fastforce simp: obj_at_def valid_asid_table_def is_vcpu_def split: option.splits)
  done

(* FIXME: move *)
lemma obj_at_conj_distrib:
  "obj_at (P and Q) p = (obj_at P p and obj_at Q p)"
  by (rule ext) (auto simp: obj_at_def)

(* FIXME: move *)
lemma obj_at_conj_distrib':
  "obj_at (\<lambda>ko. P ko \<and> Q ko) p = (obj_at P p and obj_at Q p)"
  by (rule ext) (auto simp: obj_at_def)

(* FIXME: move *)
lemma obj_at_typ_at [simp]:
  "obj_at is_vcpu p = vcpu_at p"
  by (rule ext) (auto simp: obj_at_def is_vcpu_def)

lemma set_vcpu_obj_at:
 "\<lbrace>\<lambda>s. obj_at P p s \<and> (p = t \<longrightarrow> P (ArchObj (VCPU vcpu)))\<rbrace>
    set_vcpu t vcpu \<lbrace>\<lambda>_. obj_at P p\<rbrace>"
 by (wpsimp wp: set_vcpu_wp simp: obj_at_def)

lemma vcpu_update_obj_at:
  "\<lbrace>\<lambda>s. obj_at P p s
        \<and> (p = vcpuptr \<longrightarrow> (\<forall>vcpu. ako_at (VCPU vcpu) p s \<longrightarrow> P (ArchObj (VCPU (f vcpu))))) \<rbrace>
   vcpu_update vcpuptr f
   \<lbrace>\<lambda>_. obj_at P p\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp wp: set_vcpu_obj_at get_vcpu_wp)

lemma hyp_live_vcpu_VGIC_update[simp]:
  "hyp_live (ArchObj (VCPU (vcpu_vgic_update f vcpu))) = hyp_live (ArchObj (VCPU vcpu))"
  by (simp add: hyp_live_def arch_live_def)

lemma hyp_live_vcpu_sctlr[simp]:
  "hyp_live (ArchObj (VCPU (vcpu_regs_update f vcpu))) = hyp_live (ArchObj (VCPU vcpu))"
  by (simp add: hyp_live_def arch_live_def)

lemmas vgic_update_obj_at =
  vcpu_update_obj_at[where f="\<lambda>vcpu. vcpu\<lparr>vcpu_vgic := f (vcpu_vgic vcpu)\<rparr>" for f,
                     folded vgic_update_def]

lemma vgic_update_hyp_live[wp]:
  "\<lbrace>obj_at hyp_live p\<rbrace> vgic_update vcpuptr f \<lbrace>\<lambda>_. obj_at hyp_live p\<rbrace>"
  by (wpsimp wp: vgic_update_obj_at simp: obj_at_def)

(* specialised form of obj_at_ko_atE to be abused as a simp rule *)
lemma obj_at_ko_atD:
  "\<lbrakk> obj_at P ptr s; ko_at k ptr s \<rbrakk> \<Longrightarrow> P k"
  by (erule (2) obj_at_ko_atE)

lemma hyp_live_vcpu_vtimer_idem[simp]:
  "hyp_live (ArchObj (VCPU (vcpu_vtimer_update f vcpu))) = hyp_live (ArchObj (VCPU vcpu))"
  by (simp add: hyp_live_def arch_live_def)

lemma vcpu_update_vtimer_hyp_live[wp]:
  "vcpu_update vcpu_ptr (vcpu_vtimer_update f) \<lbrace> obj_at hyp_live p \<rbrace>"
  by (wpsimp wp: vcpu_update_obj_at simp: crunch_simps obj_at_ko_atD)

crunch vcpu_save_reg, vcpu_save_reg_range, vgic_update_lr, vcpu_disable, vcpu_save, vcpu_restore,
          save_virt_timer, restore_virt_timer
  for hyp_live[wp]: "obj_at hyp_live p"
  (wp: vcpu_update_vtimer_hyp_live vcpu_update_obj_at hoare_vcg_imp_lift' hoare_vcg_all_lift
       crunch_wps
   simp: crunch_simps obj_at_ko_atD)

crunch vcpu_disable, vcpu_restore, vcpu_save, vcpu_enable
  for valid_arch_state[wp]: valid_arch_state
  (rule: valid_arch_state_lift simp: obj_at_conj_distrib)

lemma get_vcpu_typ_at'[wp]:
  "\<lbrace>\<top>\<rbrace> get_vcpu vcpu \<lbrace>\<lambda>_. typ_at (AArch AVCPU) vcpu\<rbrace>"
  unfolding get_vcpu_def get_object_def
  by (wpsimp simp: obj_at_def)

lemma vcpu_restore_typ_at'[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_restore vcpu \<lbrace>\<lambda>_. typ_at (AArch AVCPU) vcpu\<rbrace>"
  unfolding vcpu_restore_def by wp

lemma vcpu_enable_typ_at'[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_enable vcpu \<lbrace>\<lambda>_. typ_at (AArch AVCPU) vcpu\<rbrace>"
  unfolding vcpu_enable_def by wp

lemma valid_arch_state_update_vcpu:
  "\<lbrakk>valid_arch_state s ; typ_at (AArch AVCPU) t s; obj_at hyp_live t s\<rbrakk>
   \<Longrightarrow> valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (t, a)\<rparr>\<rparr>)"
   by (auto simp: valid_arch_state_def obj_at_def is_vcpu_def)

lemma vcpu_switch_valid_arch[wp]:
  "\<lbrace>valid_arch_state and (\<lambda>s. vcpu_opt \<noteq> None \<longrightarrow> obj_at hyp_live (the vcpu_opt) s)\<rbrace>
  vcpu_switch vcpu_opt \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding vcpu_switch_def
  apply (rule hoare_pre)
  apply (wpsimp | strengthen valid_arch_state_update_vcpu)+
  apply (auto simp: valid_arch_state_def obj_at_conj_distrib)
  done

crunch store_pde
  for valid_arch[wp]: "valid_arch_state"

lemma gets_the_get_tcb_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at (TCB tcb) t s \<longrightarrow> Q tcb s\<rbrace> gets_the $ get_tcb t \<lbrace>Q\<rbrace>"
  by wpsimp (clarsimp simp: get_tcb_Some_ko_at)

crunch arm_context_switch
  for P_obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"

lemma sym_refs_VCPU_hyp_live:
  assumes tcb: "ko_at (TCB tcb) t s"
  assumes vcpu: "tcb_vcpu (tcb_arch tcb) = Some v"
  assumes sym: "sym_refs (state_hyp_refs_of s)"
  shows "obj_at hyp_live v s"
proof -
  from tcb vcpu have "(v,TCBHypRef) \<in> state_hyp_refs_of s t"
    by (clarsimp simp: state_hyp_refs_of_def obj_at_def)
  with sym have "(t,HypTCBRef) \<in> state_hyp_refs_of s v"
    by (auto dest: sym_refsD)
  thus ?thesis
    by (clarsimp simp: state_hyp_refs_of_def obj_at_def hyp_live_def hyp_refs_of_def
                       tcb_vcpu_refs_def refs_of_a_def arch_live_def vcpu_tcb_refs_def
                split: option.splits kernel_object.splits arch_kernel_obj.splits)
qed

lemma set_vm_root_valid_arch[wp]:
  "\<lbrace>valid_arch_state and sym_refs o state_hyp_refs_of\<rbrace> set_vm_root pd \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding set_vm_root_def
  apply (wpsimp wp: gets_the_get_tcb_wp get_hw_asid_valid_arch
                    hoare_vcg_imp_lift hoare_vcg_all_lift whenE_wp
                    hoare_drop_imps get_cap_wp
              simp: if_apply_def2)
  done

crunch get_hw_asid
  for sym_refs_hyp[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"

lemma flush_page_valid_arch[wp]:
  "\<lbrace>valid_arch_state and sym_refs o state_hyp_refs_of\<rbrace>
  flush_page page_size pd asid vptr \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding flush_page_def load_hw_asid_def set_vm_root_for_flush_def arm_context_switch_def
  by (wpsimp wp: hoare_vcg_if_lift hoare_drop_imps get_hw_asid_valid_arch get_cap_wp simp: hoare_if_r_and)

lemma vs_lookup1_rtrancl_iterations:
  "(tup, tup') \<in> (vs_lookup1 s)\<^sup>*
    \<Longrightarrow> (length (fst tup) \<le> length (fst tup')) \<and>
       (tup, tup') \<in> ((vs_lookup1 s)
           ^^ (length (fst tup') - length (fst tup)))"
  apply (erule rtrancl_induct)
   apply simp
  apply (elim conjE)
  apply (subgoal_tac "length (fst z) = Suc (length (fst y))")
   apply (simp add: Suc_diff_le)
   apply (erule(1) relcompI)
  apply (clarsimp simp: vs_lookup1_def)
  done


lemma find_pd_for_asid_lookup_none:
  "\<lbrace>\<top>\<rbrace>
    find_pd_for_asid asid
   -, \<lbrace>\<lambda>e s. \<forall>p. \<not> ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
   VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> p) s\<rbrace>"
  apply (simp add: find_pd_for_asid_def assertE_def
                 split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply clarsimp
  apply (intro allI conjI impI)
   apply (clarsimp simp: vs_lookup_def vs_asid_refs_def up_ucast_inj_eq
                  dest!: vs_lookup1_rtrancl_iterations
                         graph_ofD vs_lookup1D)
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: vs_lookup1_rtrancl_iterations
                        graph_ofD vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def up_ucast_inj_eq
                        mask_asid_low_bits_ucast_ucast
                 dest!: graph_ofD)
  done

lemma find_pd_for_asid_aligned_pd [wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace> find_pd_for_asid asid \<lbrace>\<lambda>rv s. is_aligned rv 14\<rbrace>,-"
  apply (simp add: find_pd_for_asid_def assertE_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply clarsimp
  apply (drule vs_lookup_atI)
  apply (drule (2) valid_vspace_objsD)
  apply clarsimp
  apply (drule bspec, blast)
  apply (thin_tac "ko_at ko p s" for ko p)
  apply (clarsimp simp: pspace_aligned_def obj_at_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: a_type_def vspace_bits_defs
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
  done


lemma find_pd_for_asid_aligned_pd_bits[wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace>
      find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. is_aligned rv pd_bits\<rbrace>, -"
  by (simp add: vspace_bits_defs, rule find_pd_for_asid_aligned_pd)


lemma find_pd_for_asid_lots:
  "\<lbrace>\<lambda>s. (\<forall>rv. ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
   VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> rv) s
           \<longrightarrow> (valid_vspace_objs s \<longrightarrow> page_directory_at rv s)
           \<longrightarrow> Q rv s)
       \<and> ((\<forall>rv. \<not> ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
   VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> rv) s) \<longrightarrow> (\<forall>e. E e s))\<rbrace>
    find_pd_for_asid asid
  \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_def valid_def)
  apply (frule in_inv_by_hoareD [OF find_pd_for_asid_inv])
  apply (frule use_valid [OF _ find_pd_for_asid_lookup_none
                                [unfolded validE_E_def validE_def]])
   apply simp
  apply (frule use_valid [OF _ find_pd_for_asid_lookup_ref
                                [unfolded validE_R_def validE_def]])
   apply simp
  apply (clarsimp split: sum.split_asm)
  apply (drule spec, drule uncurry, erule mp)
  apply clarsimp
  apply (frule use_valid [OF _ find_pd_for_asid_page_directory
                                [unfolded validE_R_def validE_def]])
   apply simp
  apply simp
  done


lemma vs_lookup1_inj:
  "\<lbrakk> ((ref, p), (ref', p')) \<in> vs_lookup1 s ^^ n;
     ((ref, p), (ref', p'')) \<in> vs_lookup1 s ^^ n \<rbrakk>
       \<Longrightarrow> p' = p''"
  apply (induct n arbitrary: ref ref' p p' p'')
   apply simp
  apply (clarsimp dest!: vs_lookup1D)
  apply (subgoal_tac "pa = pb", simp_all)
  apply (simp add: obj_at_def)
  apply (auto simp: vs_refs_def up_ucast_inj_eq dest!: graph_ofD
             split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm)
  done


lemma vs_lookup_Cons_eq:
  "(ref \<rhd> p) s \<Longrightarrow> ((v # ref) \<rhd> p') s = ((ref, p) \<rhd>1 (v # ref, p')) s"
  apply (rule iffI)
   apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                  dest!: graph_ofD)
   apply (frule vs_lookup1_trans_is_append[where ys=ref])
   apply (frule vs_lookup1_trans_is_append[where ys="v # ref"])
   apply (clarsimp dest!: vs_lookup1_rtrancl_iterations vs_lookup1D)
   apply (clarsimp simp add: up_ucast_inj_eq)
   apply (drule(1) vs_lookup1_inj)
   apply (simp add: vs_lookup1I)
  apply (erule vs_lookup_trancl_step)
  apply simp
  done


lemma vptr_shifting_3_ways:
  fixes vptr :: word32 shows
  "vptr >> pageBits + pt_bits - pte_bits << pde_bits >> pde_bits
            = vptr >> pageBits + pt_bits - pte_bits"
  apply (rule shiftl_shiftr_id, simp add: vspace_bits_defs)
  apply (rule shiftr_less_t2n', simp_all add: vspace_bits_defs)
  apply (cut_tac word_log_esimps[where x=vptr])
  apply (simp add: mask_def)
  done


lemma page_table_mapped_wp: (* ARMHYP *)
  "\<lbrace>\<lambda>s. valid_vspace_objs s \<and> pspace_aligned s
        \<and> (\<not> ([VSRef (vptr >> pageBits + pt_bits - pte_bits) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pt) s
                  \<longrightarrow> Q None s)
        \<and> (\<forall>pd. vspace_at_asid asid pd s \<and> page_directory_at pd s
                 \<and> is_aligned pd pd_bits
                    \<longrightarrow> Q (Some pd) s)\<rbrace>
     page_table_mapped asid vptr pt
   \<lbrace>Q\<rbrace>"
  (is "\<lbrace>?P\<rbrace> page_table_mapped asid vptr pt \<lbrace>Q\<rbrace>")
  apply (simp add: page_table_mapped_def)
  apply (rule hoare_pre)
   apply (wp get_pde_wp find_pd_for_asid_lots | wpc)+
  apply (clarsimp simp: lookup_pd_slot_def Let_def vspace_at_asid_def)
  apply (rule conjI[rotated])
   apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                  dest!: graph_ofD vs_lookup1D vs_lookup1_rtrancl_iterations)
   apply (drule spec, erule notE, rule ImageI[rotated])
    apply (rule image_eqI, rule refl, erule graph_ofI)
   apply (rule r_into_rtrancl, simp)
   apply (erule(1) vs_lookup1I)
   apply simp
  apply (clarsimp simp: vs_lookup_Cons_eq)
  apply (frule(1) pd_aligned)
  apply (clarsimp simp: vs_lookup1_def obj_at_def pd_shifting
                        vs_refs_def pd_shifting_dual)
  apply (simp add: vspace_bits_defs vptr_shifting_3_ways[simplified vspace_bits_defs, simplified])
  apply (auto simp: pde_ref_def ucast_up_ucast_id is_up_def a_type_simps
                    source_size_def target_size_def word_size
                    addrFromPPtr_def ptrFromPAddr_def
             split: if_split_asm
             dest!: graph_ofD)
  done


crunch flush_page
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps hoare_drop_imps)


lemmas flush_page_typ_ats [wp] = abs_typ_at_lifts [OF flush_page_typ_at]


crunch flush_page
  for aligned[wp]: "pspace_aligned"
  (wp: crunch_wps hoare_drop_imps)


definition
  valid_unmap :: "vmpage_size \<Rightarrow> asid * vspace_ref \<Rightarrow> bool"
where
  "valid_unmap sz \<equiv> \<lambda>(asid, vptr). 0 < asid \<and> is_aligned vptr pageBits \<and>
                                   (sz = ARMSuperSection \<longrightarrow> is_aligned vptr 25) \<and>
                                   (sz = ARMLargePage \<longrightarrow> is_aligned vptr 16) \<and>
                                   (sz = ARMSection \<longrightarrow> is_aligned vptr 21)"


lemma modify_valid_lift: "\<lbrakk> \<And>s. P s = P (f s) ; \<lbrace>P\<rbrace> f' \<lbrace> \<lambda>_ s. P s\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f' \<lbrace> \<lambda>rv s. P (f s)\<rbrace>"
  by simp

lemma vcpu_switch_vs_lookup[wp]: "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (cases vcpu; simp)
   apply (wp | wpc | rule modify_valid_lift | clarsimp simp: vs_lookup_def vs_lookup1_def)+
  done

crunch set_vm_root
  for vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"
  (wp: crunch_wps simp: crunch_simps vs_lookup_arch_update)

crunch flush_page
  for vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"
  (wp: crunch_wps simp: crunch_simps vs_lookup_arch_update)

lemma vcpu_switch_vs_lookup_pages[wp]: "\<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (cases vcpu; simp)
   apply (wp | wpc | rule modify_valid_lift | clarsimp simp: vs_lookup_pages_def vs_lookup_pages1_def)+
  done

crunch set_vm_root
  for vs_lookup_pages[wp]: "\<lambda>s. P (vs_lookup_pages s)"
  (wp: crunch_wps simp: crunch_simps vs_lookup_pages_arch_update)

crunch flush_page
  for vs_lookup_pages[wp]: "\<lambda>s. P (vs_lookup_pages s)"
  (wp: crunch_wps simp: crunch_simps vs_lookup_pages_arch_update)

lemma store_pde_pd_at_asid:
  "\<lbrace>vspace_at_asid asid pd\<rbrace>
  store_pde p pde \<lbrace>\<lambda>_. vspace_at_asid asid pd\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def vspace_at_asid_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp simp: obj_at_def)
  apply (drule vs_lookup_2ConsD)
  apply clarsimp
  apply (erule vs_lookup_atE)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (rule_tac ref'="([VSRef (ucast (asid_high_bits_of asid)) None],p')" in vs_lookupI)
   apply (fastforce simp: vs_asid_refs_def graph_of_def)
  apply (rule r_into_rtrancl)
  apply (rule_tac ko=ko in vs_lookup1I)
    prefer 3
    apply (rule refl)
   prefer 2
   apply assumption
  apply (clarsimp simp: obj_at_def vs_refs_def)
  done


lemma flush_page_pd_at_asid [wp]:
  "\<lbrace>vspace_at_asid a pd\<rbrace> flush_page pgsz pd asid vptr \<lbrace>\<lambda>_. vspace_at_asid a pd\<rbrace>"
  apply (simp add: vspace_at_asid_def)
  apply wp
  done

crunch store_pde
  for "distinct"[wp]: pspace_distinct

lemma set_vcpu_pspace_distinct[wp]: "\<lbrace>pspace_distinct\<rbrace>set_vcpu p vcpu\<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_distinct[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: get_object_def obj_at_def)
  done

crunch vcpu_update,vgic_update,vgic_update_lr,vcpu_disable,vcpu_restore,vcpu_save_reg_range,
          vcpu_save, vcpu_switch
  for distinct[wp]: pspace_distinct
  (wp: mapM_x_wp mapM_wp subset_refl)

lemmas arm_context_switch_distinct_aux =
  hoare_drop_imp[of pspace_distinct "arm_context_switch _ _" "\<lambda>_ s. pspace_distinct s"
                , OF arm_context_switch_distinct]

crunch set_vm_root
  for "distinct"[wp]: pspace_distinct
  (simp: crunch_simps ignore: vcpu_switch wp: arm_context_switch_distinct_aux)

crunch flush_page
  for "distinct"[wp]: pspace_distinct (simp: crunch_simps)

definition "pg_entry_align pgsz \<equiv> case pgsz of
    ARMSmallPage \<Rightarrow> 3
  | ARMLargePage \<Rightarrow> 7
  | ARMSection \<Rightarrow> 3
  | ARMSuperSection \<Rightarrow> 7"  (* ARMHYP  change 6 to 7? *)


crunch check_mapping_pptr
  for inv[wp]: "P"

lemmas lookup_pd_slot_pd = lookup_pd_slot_eq

lemma vcpu_switch_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (cases vcpu; simp)
  apply (wp
        | wpc
        | rule modify_valid_lift
        | clarsimp simp: valid_vspace_objs_def vs_lookup_def vs_lookup1_def)+
  done

lemmas arm_context_switch_valid_vspace_objs_aux =
  hoare_drop_imp[of valid_vspace_objs "arm_context_switch _ _" "\<lambda>_ s. valid_vspace_objs s"
                , OF arm_context_switch_vspace_objs]

crunch set_vm_root
  for vspace_objs[wp]: valid_vspace_objs
  (simp: crunch_simps valid_vspace_objs_arch_update wp: arm_context_switch_valid_vspace_objs_aux)

lemma vcpu_switch_equal__mappings[wp]: "\<lbrace>equal_kernel_mappings\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_. equal_kernel_mappings\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (cases vcpu; simp)
  apply (wp | wpc | rule modify_valid_lift | clarsimp simp: equal_kernel_mappings_def)+
  done

crunch arm_context_switch
  for equal_mappings[wp]: equal_kernel_mappings
  (simp: crunch_simps)

lemmas arm_context_switch_equal_mappings_aux =
  hoare_drop_imp[of equal_kernel_mappings "arm_context_switch _ _" "\<lambda>_ s. equal_kernel_mappings s"
                , OF arm_context_switch_equal_mappings]

crunch set_vm_root
  for equal_mappings[wp]: equal_kernel_mappings
  (simp: crunch_simps wp: arm_context_switch_equal_mappings_aux)

crunch flush_page
  for equal_mappings[wp]: equal_kernel_mappings
  (simp: crunch_simps)

lemma lookup_pt_slot_is_aligned: (* ARMHYP *)
  "\<lbrace>(\<exists>\<rhd> pd) and K (vmsz_aligned vptr sz) and K (is_aligned pd pd_bits)
    and valid_arch_state and valid_vspace_objs and equal_kernel_mappings
    and pspace_aligned\<rbrace>
     lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s. is_aligned rv (pg_entry_align sz)\<rbrace>,-"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp | wpc)+
  apply (clarsimp simp: lookup_pd_slot_pd)
  apply (frule(2) valid_vspace_objsD[rotated])
  apply simp
  apply (rule is_aligned_add)
   apply (erule_tac x="ucast (lookup_pd_slot pd vptr && mask pd_bits >> pde_bits)" in allE)
   apply (clarsimp simp: obj_at_def valid_pde_def a_type_def)
   apply (simp split: Structures_A.kernel_object.split_asm if_split_asm
                     arch_kernel_obj.split_asm)
   apply (erule is_aligned_weaken[OF pspace_alignedD], simp)
   apply (simp add: obj_bits_def pg_entry_align_def vspace_bits_defs split: vmpage_size.splits)
  apply (rule is_aligned_shiftl)
  apply (rule is_aligned_andI1)
  apply (rule is_aligned_shiftr)
  apply (case_tac sz; simp add: vspace_bits_defs)
     apply (clarsimp simp: vmsz_aligned_def pg_entry_align_def
                    elim!: is_aligned_weaken  split: vmpage_size.splits)+
  done

lemmas lookup_pt_slot_is_aligned_6 =
  lookup_pt_slot_is_aligned[where sz=ARMLargePage,
    unfolded pg_entry_align_def, simplified vmpage_size.simps]

lemma lookup_pd_slot_aligned_6:
  "\<lbrakk> vmsz_aligned vptr ARMSuperSection; is_aligned pd 14 \<rbrakk>
        \<Longrightarrow> is_aligned (lookup_pd_slot pd vptr) 7" (* ARMHYP 6\<rightarrow>7? correct? *)
  apply (simp add: lookup_pd_slot_def)
  apply (erule aligned_add_aligned, simp_all add: word_bits_conv)
  apply (intro is_aligned_shiftl is_aligned_shiftr)
  apply (simp add: vmsz_aligned_def vspace_bits_defs)
  done

lemma page_directory_at_aligned_pd_bits:
  "\<lbrakk>page_directory_at pd s;pspace_aligned s\<rbrakk>
       \<Longrightarrow> is_aligned pd pd_bits"
  apply (clarsimp simp:obj_at_def)
  apply (drule(1) pspace_alignedD)
  apply (simp add:pd_bits_def pageBits_def)
  done

crunch flush_page
  for vspace_objs[wp]: valid_vspace_objs
  (simp: crunch_simps valid_vspace_objs_arch_update)

definition
  "empty_refs m \<equiv> case m of Inr (pde, _) \<Rightarrow> pde_ref pde = None | _ \<Rightarrow> True"


definition
  "parent_for_refs m \<equiv> \<lambda>cap.
   case m of Inl (_, slots)
      \<Rightarrow> (\<lambda>x. x && ~~ mask pt_bits) ` set slots \<subseteq> obj_refs cap
              \<and> is_pt_cap cap \<and> cap_asid cap \<noteq> None
    | Inr (_, slots)
      \<Rightarrow> (\<lambda>x. x && ~~ mask pd_bits) ` set slots \<subseteq> obj_refs cap
              \<and> is_pd_cap cap \<and> cap_asid cap \<noteq> None"

definition
  "same_refs m cap s \<equiv>
      case m of
      Inl (pte, slots) \<Rightarrow>
        (\<exists>p. pte_ref_pages pte = Some p \<and> p \<in> obj_refs cap) \<and>
        (case slots of
           [] \<Rightarrow> True
         | x # xs \<Rightarrow> \<forall>ref. (ref \<rhd> (x && ~~ mask pt_bits)) s \<longrightarrow>
                      vs_cap_ref cap = Some (VSRef (x && mask pt_bits >> 3) (Some APageTable) # ref))
      | Inr (pde, slots) \<Rightarrow>
          (\<exists>p. pde_ref_pages pde = Some p \<and> p \<in> obj_refs cap) \<and>
          (case slots of
             [] \<Rightarrow> True
           | x # xs \<Rightarrow> \<forall>ref. (ref \<rhd> (x && ~~ mask pd_bits)) s \<longrightarrow>
                        vs_cap_ref cap = Some (VSRef (x && mask pd_bits >> 3) (Some APageDirectory) # ref))"


definition
  "valid_page_inv pg_inv \<equiv> case pg_inv of
    PageMap asid cap ptr m \<Rightarrow>
      cte_wp_at (is_arch_update cap) ptr
      and (cte_wp_at (\<lambda>c. vs_cap_ref c = None) ptr or (\<lambda>s. cte_wp_at (\<lambda>c. same_refs m c s) ptr s))
      and cte_wp_at is_pg_cap ptr
      and (\<lambda>s. same_refs m cap s)
      and valid_slots m
      and valid_cap cap
      and K (is_pg_cap cap \<and> empty_refs m \<and> asid \<le> mask asid_bits \<and> asid \<noteq> 0)
      and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs m) slot s)
      and (\<lambda>s. \<exists>pd. vspace_at_asid asid pd s)
  | PageUnmap cap ptr \<Rightarrow>
     \<lambda>s. \<exists>dev r R sz m. cap = PageCap dev r R sz m \<and>
         case_option True (valid_unmap sz) m \<and>
         cte_wp_at ((=) (cap.ArchObjectCap cap)) ptr s \<and>
         s \<turnstile> (cap.ArchObjectCap cap)
  | PageFlush typ start end pstart pd asid \<Rightarrow>
      vspace_at_asid asid pd and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0)
  | PageGetAddr ptr \<Rightarrow> \<top>"

definition
  "valid_pdi pdi \<equiv> case pdi of
    PageDirectoryFlush typ start end pstart pd asid \<Rightarrow>
      vspace_at_asid asid pd and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0)
  | PageDirectoryNothing \<Rightarrow> \<top>"


crunch unmap_page
  for aligned[wp]: pspace_aligned
  (wp: crunch_wps)


crunch unmap_page
  for "distinct"[wp]: pspace_distinct
  (wp: crunch_wps simp: crunch_simps)


crunch unmap_page
  for valid_objs[wp]: "valid_objs"
  (wp: crunch_wps)

(* this is weird *)
lemma vcpu_switch_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (cases vcpu; simp)
  apply (wp | wpc | clarsimp)+
  done

crunch set_vm_root
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)

crunch unmap_page
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_cap_valid_slots[wp]:
  "\<lbrace>valid_slots x2\<rbrace> set_cap cap (a, b)
          \<lbrace>\<lambda>rv s. valid_slots x2 s \<rbrace>"
   apply (case_tac x2)
   apply (clarsimp simp:valid_slots_def)
   apply (wp hoare_vcg_ball_lift)
  apply (clarsimp simp:valid_slots_def)
  apply (wp hoare_vcg_ball_lift)
  done

definition
  empty_pde_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "empty_pde_at p \<equiv> \<lambda>s.
  \<exists>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s \<and>
       pd (ucast (p && mask pd_bits >> 3)) = InvalidPDE"


definition
  kernel_vsrefs :: "vs_ref set"
where
 "kernel_vsrefs \<equiv> {}" (* ARMHYP *)
(* "kernel_vsrefs \<equiv> {r. case r of VSRef x y \<Rightarrow> (kernel_base >> 20) \<le> x}"*)


definition
  "valid_pti pti \<equiv> case pti of
     PageTableMap cap ptr pde p \<Rightarrow>
     pde_at p and (\<lambda>s. wellformed_pde pde) and
     valid_pde pde and valid_cap cap and
     cte_wp_at (\<lambda>c. is_arch_update cap c \<and> cap_asid c = None) ptr and
     empty_pde_at p and
     (\<lambda>s. \<exists>p' ref. vs_cap_ref cap = Some (VSRef (p && mask pd_bits >> 3) (Some APageDirectory) # ref)
              \<and> (ref \<rhd> (p && ~~ mask pd_bits)) s
              \<and> pde_ref pde = Some p' \<and> p' \<in> obj_refs cap
              \<and> (\<exists>ao. ko_at (ArchObj ao) p' s \<and> valid_vspace_obj ao s)
           \<comment> \<open>\<and> hd (the (vs_cap_ref cap)) \<notin> kernel_vsrefs\<close>) and
     K (is_pt_cap cap \<and> cap_asid cap \<noteq> None)
   | PageTableUnmap cap ptr \<Rightarrow>
     cte_wp_at ((=) cap) ptr and valid_cap cap
       and is_final_cap' cap
       and K (is_pt_cap cap)"

crunch unmap_page_table
  for aligned[wp]: pspace_aligned
  (wp: crunch_wps)


crunch unmap_page_table
  for valid_objs[wp]: valid_objs
  (wp: crunch_wps simp: crunch_simps)


crunch unmap_page_table
  for "distinct"[wp]: pspace_distinct
  (wp: crunch_wps simp: crunch_simps)


crunch unmap_page_table
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)


crunch unmap_page_table
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps hoare_drop_imps)


definition
  "valid_apinv ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow>
  (\<lambda>s. \<exists>pool. ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) p s \<and>
              pool (ucast asid) = None)
  and cte_wp_at (\<lambda>cap. is_pd_cap cap \<and> cap_asid cap = None) slot
  and K (0 < asid \<and> asid \<le> 2^asid_bits - 1)
  and ([VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> p)"


lemma store_hw_asid_invs:
  "\<lbrace>invs and
   (\<lambda>s. arm_asid_map (arch_state s) asid = None \<and>
        arm_hwasid_table (arch_state s) hw_asid = None \<and>
        asid \<le> mask asid_bits)\<rbrace>
  store_hw_asid asid hw_asid
  \<lbrace>\<lambda>x. invs\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule store_hw_asid_valid_arch)
   apply fastforce
  apply (simp add: store_hw_asid_def)
  apply (wp find_pd_for_asid_assert_wp)
  apply (clarsimp simp: invs_def valid_state_def)
  apply (simp add: valid_global_refs_def global_refs_def
                   valid_irq_node_def valid_vspace_objs_arch_update
                   valid_arch_caps_def valid_global_objs_def
                   valid_global_vspace_mappings_def
                   valid_table_caps_def valid_kernel_mappings_def
                   valid_machine_state_def valid_vs_lookup_arch_update)
  apply (simp add: valid_asid_map_def fun_upd_def[symmetric]
                   pd_at_asid_arch_up)
  done

lemma invalidateLocalTLB_ASID_valid_irq_states:
  "\<lbrace>\<lambda>m. valid_irq_states (s\<lparr>machine_state := m\<rparr>)\<rbrace> invalidateLocalTLB_ASID x
   \<lbrace>\<lambda>a b. valid_irq_states (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  apply(simp add: valid_irq_states_def | wp no_irq | simp add: no_irq_invalidateLocalTLB_ASID)+
  done

lemma find_free_hw_asid_invs [wp]:
  "\<lbrace>invs\<rbrace> find_free_hw_asid \<lbrace>\<lambda>asid. invs\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule find_free_hw_asid_valid_arch)
   apply fastforce
  apply (simp add: find_free_hw_asid_def invalidate_hw_asid_entry_def invalidate_asid_def
                   do_machine_op_def split_def
              cong: option.case_cong)
  apply (wp|wpc)+
  apply (clarsimp simp: invs_def valid_state_def split del: if_split)
  apply (simp add: valid_global_refs_def global_refs_def cur_tcb_def
                   valid_irq_node_def valid_vspace_objs_arch_update
                   valid_arch_caps_def valid_global_objs_def
                   valid_global_vspace_mappings_def
                   valid_table_caps_def valid_kernel_mappings_def
                   valid_machine_state_def valid_vs_lookup_arch_update)
  apply (elim conjE)
  apply (rule conjI)
   apply(erule use_valid[OF _ invalidateLocalTLB_ASID_valid_irq_states])
   apply fastforce
  apply(rule conjI)
   apply clarsimp
   apply (drule use_valid)
     apply (rule_tac p=p in invalidateLocalTLB_ASID_underlying_memory, simp, fastforce)
  apply (clarsimp simp: valid_asid_map_def fun_upd_def[symmetric]
                        pd_at_asid_arch_up')
  apply (rule conjI, blast)
  apply (clarsimp simp: vspace_at_asid_def)
  apply (drule_tac P1 = "(=) (device_state (machine_state s))" in
    use_valid[OF _ invalidateLocalTLB_ASID_device_state_inv])
   apply simp
  apply clarsimp
  done

lemma get_hw_asid_invs [wp]:
  "\<lbrace>invs and K (a \<le> mask asid_bits)\<rbrace> get_hw_asid a \<lbrace>\<lambda>hw_asid. invs\<rbrace>"
  apply (simp add: get_hw_asid_def)
  apply (wp store_hw_asid_invs load_hw_asid_wp|wpc)+
  apply simp
  done

lemma arm_context_switch_invs [wp]:
  "\<lbrace>invs and K (a \<le> mask asid_bits)\<rbrace> arm_context_switch pd a \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: arm_context_switch_def writeContextIDAndPD_def)
  apply (wp dmo_invs)
  apply (rule hoare_post_imp[rotated])
  apply (rule get_hw_asid_invs[simplified])
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp | wp)+)[3]
  apply(erule use_valid)
  apply(wp no_irq | simp add: no_irq_setHardwareASID no_irq_set_current_pd)+
  done

lemmas set_current_pd_irq_masks = no_irq[OF no_irq_set_current_pd]
lemmas setHardwareASID_irq_masks = no_irq[OF no_irq_setHardwareASID]

lemma dmo_set_current_pd_invs[wp]: "\<lbrace>invs\<rbrace> do_machine_op (set_current_pd addr) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: set_current_pd_def writeTTBR0_def dsb_def isb_def machine_op_lift_def
                           machine_rest_lift_def split_def setCurrentPDPL2_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ set_current_pd_irq_masks])
  done

crunch ackInterrupt
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
lemma dmo_ackInterrupt[wp]: "\<lbrace>invs\<rbrace> do_machine_op (ackInterrupt irq) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: ackInterrupt_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ ackInterrupt_irq_masks])
  done

(* lemmas for vcpu_switch invs *)

(* FIXME move to Machine_AI? *)

crunch writeContextIDAndPD
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
crunch addressTranslateS1
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
crunch getSCTLR,get_gic_vcpu_ctrl_hcr,set_gic_vcpu_ctrl_hcr
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
crunch writeVCPUHardwareReg, readVCPUHardwareReg
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
crunch setSCTLR,setHCR,getSCTLR,get_gic_vcpu_ctrl_vmcr,set_gic_vcpu_ctrl_vmcr
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
crunch
  get_gic_vcpu_ctrl_apr,set_gic_vcpu_ctrl_apr,get_gic_vcpu_ctrl_lr,set_gic_vcpu_ctrl_lr
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"

crunch setSCTLR,getSCTLR,setHCR
  for underlying_memory: "\<lambda>m'. underlying_memory m' p = um"
crunch dsb,isb,writeContextIDAndPD,addressTranslateS1
  for underlying_memory: "\<lambda>m'. underlying_memory m' p = um"
crunch get_gic_vcpu_ctrl_vmcr,set_gic_vcpu_ctrl_vmcr
  for underlying_memory: "\<lambda>m'. underlying_memory m' p = um"
crunch get_gic_vcpu_ctrl_apr,set_gic_vcpu_ctrl_apr
  for underlying_memory: "\<lambda>m'. underlying_memory m' p = um"
crunch get_gic_vcpu_ctrl_lr,set_gic_vcpu_ctrl_lr
  for underlying_memory: "\<lambda>m'. underlying_memory m' p = um"
crunch get_gic_vcpu_ctrl_hcr,set_gic_vcpu_ctrl_hcr
  for underlying_memory: "\<lambda>m'. underlying_memory m' p = um"
crunch writeVCPUHardwareReg, readVCPUHardwareReg
  for underlying_memory: "\<lambda>m'. underlying_memory m' p = um"

crunch writeVCPUHardwareReg, readVCPUHardwareReg
  for underlying_memory_pred: "\<lambda>m'. P (underlying_memory m')"

lemmas isb_irq_masks = no_irq[OF no_irq_isb]
lemmas dsb_irq_masks = no_irq[OF no_irq_dsb]
lemmas setHCR_irq_masks = no_irq[OF no_irq_setHCR]
lemmas setSCTLR_irq_masks = no_irq[OF no_irq_setSCTLR]
lemmas getSCTLR_irq_masks = no_irq[OF no_irq_getSCTLR]
lemmas get_gic_vcpu_ctrl_vmcr_irq_masks = no_irq[OF no_irq_get_gic_vcpu_ctrl_vmcr]
lemmas set_gic_vcpu_ctrl_vmcr_irq_masks = no_irq[OF no_irq_set_gic_vcpu_ctrl_vmcr]
lemmas get_gic_vcpu_ctrl_apr_irq_masks = no_irq[OF no_irq_get_gic_vcpu_ctrl_apr]
lemmas set_gic_vcpu_ctrl_apr_irq_masks = no_irq[OF no_irq_set_gic_vcpu_ctrl_apr]
lemmas get_gic_vcpu_ctrl_lr_irq_masks = no_irq[OF no_irq_get_gic_vcpu_ctrl_lr]
lemmas set_gic_vcpu_ctrl_lr_irq_masks = no_irq[OF no_irq_set_gic_vcpu_ctrl_lr]
lemmas get_gic_vcpu_ctrl_hcr_irq_masks = no_irq[OF no_irq_get_gic_vcpu_ctrl_hcr]
lemmas set_gic_vcpu_ctrl_hcr_irq_masks = no_irq[OF no_irq_set_gic_vcpu_ctrl_hcr]
(* end of move to Machine_AI *)

(* FIXME this whole next chunk of do_machine_op and invs lemmas looks like a candidate for a
   lifting rule *)
lemma dmo_isb_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op isb \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule isb_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ isb_irq_masks])
  done

lemma dmo_dsb_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op dsb \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule dsb_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ dsb_irq_masks])
  done

lemma dmo_setHCR_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (setHCR w) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule setHCR_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ setHCR_irq_masks])
  done

lemma dmo_setSCTLR_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (setSCTLR x) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule setSCTLR_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ setSCTLR_irq_masks])
  done

lemma dmo_getSCTLR_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (getSCTLR) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule getSCTLR_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ getSCTLR_irq_masks])
  done

lemma dmo_get_gic_vcpu_ctrl_vmcr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (get_gic_vcpu_ctrl_vmcr) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule get_gic_vcpu_ctrl_vmcr_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ get_gic_vcpu_ctrl_vmcr_irq_masks])
  done

lemma dmo_set_gic_vcpu_ctrl_vmcr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (set_gic_vcpu_ctrl_vmcr x) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule set_gic_vcpu_ctrl_vmcr_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ set_gic_vcpu_ctrl_vmcr_irq_masks])
  done

lemma dmo_get_gic_vcpu_ctrl_apr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (get_gic_vcpu_ctrl_apr) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule get_gic_vcpu_ctrl_apr_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ get_gic_vcpu_ctrl_apr_irq_masks])
  done

lemma dmo_set_gic_vcpu_ctrl_apr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (set_gic_vcpu_ctrl_apr x) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule set_gic_vcpu_ctrl_apr_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ set_gic_vcpu_ctrl_apr_irq_masks])
  done

lemma dmo_get_gic_vcpu_ctrl_lr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (get_gic_vcpu_ctrl_lr n) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule get_gic_vcpu_ctrl_lr_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ get_gic_vcpu_ctrl_lr_irq_masks])
  done

lemma dmo_set_gic_vcpu_ctrl_lr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (set_gic_vcpu_ctrl_lr n x) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule set_gic_vcpu_ctrl_lr_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ set_gic_vcpu_ctrl_lr_irq_masks])
  done

lemma dmo_get_gic_vcpu_ctrl_hcr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (get_gic_vcpu_ctrl_hcr) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule get_gic_vcpu_ctrl_hcr_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ get_gic_vcpu_ctrl_hcr_irq_masks])
  done

lemma dmo_set_gic_vcpu_ctrl_hcr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (set_gic_vcpu_ctrl_hcr x) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule set_gic_vcpu_ctrl_hcr_underlying_memory)
    apply fastforce+
  apply(erule (1) use_valid[OF _ set_gic_vcpu_ctrl_hcr_irq_masks])
  done

lemma dmo_writeVCPUHardwareReg_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (writeVCPUHardwareReg r v) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (fastforce intro: writeVCPUHardwareReg_underlying_memory)+
  apply (erule (1) use_valid[OF _ no_irq[OF no_irq_writeVCPUHardwareReg]])
  done

lemma dmo_readVCPUHardwareReg_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (readVCPUHardwareReg r) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (fastforce intro: readVCPUHardwareReg_underlying_memory)+
  apply (erule (1) use_valid[OF _ no_irq[OF no_irq_readVCPUHardwareReg]])
  done

(* set_vcpu invariants *)
lemma set_vcpu_cur_tcb[wp]: "\<lbrace>cur_tcb\<rbrace> set_vcpu p v \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  unfolding cur_tcb_def[abs_def]
  apply (rule hoare_lift_Pf [where f=cur_thread])
  apply (simp add: tcb_at_typ)
  apply wp
  apply (simp add: set_vcpu_def)
  apply (wp hoare_drop_imp)
  done

lemma set_vcpu_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace>
     set_vcpu p vcpu
   \<lbrace>\<lambda>s. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_cap_refs_respects_device_region[THEN hoare_set_object_weaken_pre])
  including unfold_objects_asm
  apply (clarsimp simp: a_type_def split: if_splits)
  done

lemma set_vcpu_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace>
     set_vcpu p vcpu
   \<lbrace>\<lambda>s. pspace_respects_device_region\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_pspace_respects_device_region[THEN hoare_set_object_weaken_pre])
  including unfold_objects_asm
  apply (clarsimp simp: a_type_def split: if_splits)
  done

lemma set_vcpu_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_vcpu p v \<lbrace>\<lambda>_. cap_refs_in_kernel_window\<rbrace>"
  unfolding cap_refs_in_kernel_window_def[abs_def]
  apply (rule hoare_lift_Pf [where f="\<lambda>s. not_kernel_window_arch (arch_state s)"])
  apply (rule valid_refs_cte_lift)
  apply wp+
  done

crunch set_vcpu
  for valid_irq_states[wp]: valid_irq_states
  (wp: crunch_wps simp: crunch_simps)

crunch set_vcpu
  for interrupt_state[wp]: "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas set_vcpu_valid_irq_handlers[wp] = valid_irq_handlers_lift[OF set_vcpu.caps set_vcpu_interrupt_state]

crunch set_vcpu
  for interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas set_vcpu_valid_irq_node[wp] = valid_irq_node_typ[OF set_vcpu_typ_at set_vcpu_interrupt_irq_node]

crunch set_vcpu
  for idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_vcpu_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp+

lemma set_vcpu_valid_reply_masters[wp]:
  "\<lbrace>valid_reply_masters\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_reply_masters\<rbrace>"
  by (rule valid_reply_masters_cte_lift) wp

lemma set_vcpu_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_vcpu_def set_object_def)
  including no_pre apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma set_vcpu_valid_reply_caps[wp]:
  "\<lbrace>valid_reply_caps\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_reply_caps\<rbrace>"
  by (rule valid_reply_caps_st_cte_lift) wp+

lemma set_vcpu_if_unsafe_then_cap[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_ifunsafe[THEN hoare_set_object_weaken_pre])
  including unfold_objects
  apply (clarsimp simp: a_type_def)
  done

lemma set_vcpu_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  by (wp only_idle_lift set_asid_pool_typ_at)+

lemma set_vcpu_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  by (wp valid_idle_lift)

lemma set_vcpu_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_valid_ioc_no_caps[THEN hoare_set_object_weaken_pre] get_object_inv)
  including unfold_objects
  apply (clarsimp simp: valid_def get_object_def simpler_gets_def assert_def
          return_def fail_def bind_def
          a_type_simps is_tcb is_cap_table a_type_def)
  done

lemma set_vcpu_valid_mdb[wp]: "\<lbrace>valid_mdb\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  by (wpsimp wp: valid_mdb_lift get_object_wp simp: set_vcpu_def set_object_def)

lemma set_vcpu_zombies_final[wp]: "\<lbrace>zombies_final\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_vcpu_def)
  including unfold_objects
  apply (wp set_object_zombies[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: a_type_def)
  done

lemma set_vcpu_if_live_then_nonz_cap_full:
  "\<lbrace>if_live_then_nonz_cap and (\<lambda>s. obj_at live p s \<or> (arch_live (VCPU v) \<longrightarrow> ex_nonz_cap_to p s))\<rbrace>
    set_vcpu p v \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  unfolding set_vcpu_def
  including unfold_objects
  apply (wp get_object_wp set_object_iflive[THEN hoare_set_object_weaken_pre])
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: live_def hyp_live_def arch_live_def a_type_def split: if_splits)
  apply (rule if_live_then_nonz_capD; simp add: live_def hyp_live_def arch_live_def)
  done

lemma set_vcpu_if_live_then_nonz_cap_None[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_vcpu p (vcpu\<lparr>vcpu_tcb := None\<rparr>) \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp wp: set_vcpu_if_live_then_nonz_cap_full simp: arch_live_def)

lemma set_vcpu_if_live_then_nonz_cap_Some[wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to p\<rbrace> set_vcpu p (vcpu\<lparr>vcpu_tcb := Some tcb\<rparr>) \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp wp: set_vcpu_if_live_then_nonz_cap_full simp: arch_live_def)

(* FIXME: kind of ugly but hey! it works!! *)

lemma state_refs_of_simp: "\<lbrakk> a \<noteq> p \<rbrakk> \<Longrightarrow> state_refs_of (s\<lparr>kheap := (kheap s)(p \<mapsto> v) \<rparr>) a = state_refs_of s a "
  by (simp add: state_refs_of_def)

lemma state_refs_of_vcpu_simp: "typ_at (AArch AVCPU) p s \<Longrightarrow> state_refs_of s p = {}"
  apply (clarsimp simp: obj_at_def state_refs_of_def a_type_def aa_type_def)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma set_object_vcpu_sym_refs:
  "\<lbrace>\<lambda>s. typ_at (AArch AVCPU) p s \<and> sym_refs (state_refs_of s)\<rbrace>
     set_object p (ArchObj (VCPU v))
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  including unfold_objects
  apply (wpsimp wp: set_object_wp
              simp: state_refs_of_def sym_refs_def)
  by force


lemma set_vcpu_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s)\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_vcpu_sym_refs[THEN hoare_set_object_weaken_pre])
  apply (simp add: get_object_def)
  apply (clarsimp simp: obj_at_def)
  done

lemma state_hyp_refs_of_simp_neq: "\<lbrakk> a \<noteq> p \<rbrakk> \<Longrightarrow> state_hyp_refs_of (s\<lparr>kheap := (kheap s)(p \<mapsto> v) \<rparr>) a = state_hyp_refs_of s a "
  by (simp add: state_hyp_refs_of_def)

lemma state_hyp_refs_of_simp_eq:
  "obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of v) p s
   \<Longrightarrow> state_hyp_refs_of (s\<lparr>kheap := (kheap s)(p \<mapsto> v) \<rparr>) p = state_hyp_refs_of s p"
  by (clarsimp simp: state_hyp_refs_of_def obj_at_def)

lemma set_object_vcpu_sym_refs_hyp:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of ko) p s
      \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv s. sym_refs (state_hyp_refs_of s)\<rbrace>"
   apply (wpsimp wp: set_object_wp)
   apply (erule rsubst[where P = sym_refs])
   apply (rule ext)
   by (clarsimp simp: state_hyp_refs_of_def obj_at_def
                  split: option.splits if_splits)

lemma set_vcpu_sym_refs_refs_hyp:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of (ArchObj (VCPU v))) p s
      \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
     set_vcpu p v
   \<lbrace>\<lambda>rv s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_vcpu_sym_refs_hyp hoare_drop_imp)
  apply (clarsimp simp: hyp_refs_of_def)
  done


lemma set_vcpu_valid_pspace:
  "\<lbrace>valid_obj p (ArchObj (VCPU v))
    and valid_pspace
    and obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of (ArchObj (VCPU v))) p\<rbrace>
     set_vcpu p v
   \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply (wpsimp simp: valid_pspace_def pred_conj_def
                  wp: set_vcpu_if_live_then_nonz_cap_full set_vcpu_sym_refs_refs_hyp)
  apply (clarsimp simp: obj_at_def live_def)
  apply (clarsimp simp: arch_live_def hyp_refs_of_def refs_of_a_def vcpu_tcb_refs_def hyp_live_def
                 split: kernel_object.splits arch_kernel_obj.splits option.splits)
  done


lemma set_vcpu_valid_arch_eq_hyp:
  "\<lbrace>valid_arch_state and obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of (ArchObj (VCPU v))) p\<rbrace>
     set_vcpu p v
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding valid_arch_state_def
  apply (wp set_vcpu_wp)
  apply clarsimp
  apply (rule conjI)
   apply (fastforce simp: valid_asid_table_def obj_at_def)
  apply (clarsimp split: option.splits)
  apply (clarsimp simp: obj_at_def is_vcpu_def vcpu_tcb_refs_def hyp_live_def arch_live_def
                 split: option.splits)
  done

lemma set_vcpu_invs_eq_hyp:
  "\<lbrace>obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of (ArchObj (VCPU v))) p
    and valid_obj p (ArchObj (VCPU v))
    and  invs \<rbrace>
     set_vcpu p v
   \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (clarsimp simp add: invs_def pred_conj_def)
  apply (subst conj_assoc[symmetric])
  apply (subst conj_assoc[symmetric])
  apply (rule hoare_vcg_conj_lift[rotated])
   apply wp
  apply (subst valid_state_def)+
  apply (simp add: pred_conj_def)
  apply (subst conj_assoc[symmetric])
  apply (subst conj_assoc[symmetric])
   apply (rule hoare_pre)
    apply (wp set_vcpu_valid_pspace set_vcpu_obj_at)
  apply ((rule hoare_vcg_conj_lift[rotated])+ ; (wp set_vcpu_valid_pspace set_vcpu_valid_arch_eq_hyp)?)
  apply simp
  done

(* FIXME: move both this and the original still in Retype_AI *)
lemmas do_machine_op_bind =
    submonad_bind [OF submonad_do_machine_op submonad_do_machine_op
                      submonad_do_machine_op]

lemma vcpu_restore_reg_invs[wp]:
  "\<lbrace>\<lambda> s. invs s\<rbrace> vcpu_restore_reg v r \<lbrace> \<lambda>_ . invs \<rbrace>"
  unfolding vcpu_restore_reg_def by wp

lemma valid_obj_vcpu_regs_simp[simp]:
  "valid_obj v (ArchObj (VCPU (vcpu\<lparr>vcpu_regs := regs\<rparr>)))
     = valid_obj v (ArchObj (VCPU (vcpu)))"
  unfolding valid_obj_def
  by (rule ext, clarsimp simp: valid_vcpu_def)

lemma valid_obj_vcpu_vgic_simp[simp]:
  "valid_obj v (ArchObj (VCPU (vcpu\<lparr>vcpu_vgic := vgic\<rparr>)))
     = valid_obj v (ArchObj (VCPU (vcpu)))"
  unfolding valid_obj_def
  by (rule ext, clarsimp simp: valid_vcpu_def)

lemma vcpu_save_reg_invs[wp]:
  "\<lbrace>\<lambda> s. invs s\<rbrace> vcpu_save_reg v r \<lbrace> \<lambda>_ . invs \<rbrace>"
  unfolding vcpu_save_reg_def vcpu_update_def
  apply (wpsimp wp: set_vcpu_invs_eq_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (fastforce simp: obj_at_def dest: invs_valid_objs)
  done

lemma vcpu_update_trivial_invs:
  assumes tcb: "\<And>vcpu. vcpu_tcb (upd f vcpu) = vcpu_tcb vcpu"
  shows "vcpu_update vcpu_ptr (upd f) \<lbrace> invs \<rbrace>"
  unfolding vcpu_update_def
  apply (wpsimp wp: tcb set_vcpu_invs_eq_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (erule (1) obj_at_valid_objsE[OF _ invs_valid_objs])
  apply (clarsimp simp: obj_at_def valid_obj_def valid_vcpu_def tcb dest!: invs_valid_objs)
  done

lemmas vcpu_update_invs[wp] =
  vcpu_update_trivial_invs[where upd="vcpu_vtimer_update", simplified]
  vcpu_update_trivial_invs[where upd="vcpu_regs_update", simplified]
  vcpu_update_trivial_invs[where upd="vcpu_vppi_masked_update", simplified]
  vcpu_update_trivial_invs[where upd="vcpu_vgic_update", simplified]
  vcpu_update_trivial_invs[where upd="\<lambda>f vcpu. vcpu\<lparr>vcpu_vgic := f (vcpu_vgic vcpu)\<rparr>"
                           , folded vgic_update_def, simplified]

(* FIXME: move *)
lemma dmo_gets_inv[wp]:
  "\<lbrace>P\<rbrace> do_machine_op (gets f) \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding do_machine_op_def by (wpsimp simp: simpler_gets_def)

(* FIXME: move *)
lemma dmo_machine_op_lift_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (machine_op_lift f) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  by (auto simp add: machine_op_lift_def machine_rest_lift_def in_monad select_f_def)

crunch vcpu_restore_reg_range, vcpu_save_reg_range, vgic_update_lr, vcpu_read_reg
  for invs[wp]: invs
  (wp: mapM_x_wp)

lemma vcpu_write_reg_invs[wp]:
  "vcpu_write_reg vcpu_ptr reg val \<lbrace>invs\<rbrace>"
  unfolding vcpu_write_reg_def
  by (wpsimp cong: vcpu.fold_congs) (* crunch can't do cong yet *)

lemma save_virt_timer_invs[wp]:
  "\<lbrace>\<lambda> s. invs s\<rbrace> save_virt_timer vcpu_ptr \<lbrace>\<lambda>_ . invs\<rbrace>"
  unfolding save_virt_timer_def read_cntpct_def get_cntv_off_64_def get_cntv_cval_64_def
  by (wpsimp wp: set_vcpu_invs_eq_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift')

(* migrated from ArchInterrupt_AI, which is not visible from here *)
lemma maskInterrupt_invs:
  "\<lbrace>invs and (\<lambda>s. \<not>b \<longrightarrow> interrupt_states s irq \<noteq> IRQInactive)\<rbrace>
   do_machine_op (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
   by (wpsimp simp: do_machine_op_def split_def maskInterrupt_def)
      (clarsimp simp: in_monad invs_def valid_state_def valid_machine_state_def cur_tcb_def
                      valid_irq_states_def valid_irq_masks_def)

lemma restore_virt_timer_invs[wp]:
  "\<lbrace>\<lambda> s. invs s\<rbrace> restore_virt_timer vcpu_ptr \<lbrace>\<lambda>_ . invs\<rbrace>"
  unfolding restore_virt_timer_def read_cntpct_def set_cntv_off_64_def set_cntv_cval_64_def
             is_irq_active_def get_irq_state_def
  by (wpsimp wp: set_vcpu_invs_eq_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
                 maskInterrupt_invs)

lemma vcpu_enable_invs[wp]:
"\<lbrace>\<lambda> s. invs s\<rbrace> vcpu_enable v \<lbrace> \<lambda>_ . invs \<rbrace>"
  apply (simp add: vcpu_enable_def)
  apply (wp get_vcpu_inv | wpc)
  apply (subst do_machine_op_bind | rule empty_fail_bind | simp add: empty_fail_isb)+
  apply (wp get_vcpu_inv | wpc | simp)+
  done

lemma vcpu_restore_invs[wp]:
  "\<lbrace>\<lambda>s. invs s\<rbrace> vcpu_restore v \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: vcpu_restore_def do_machine_op_bind dom_mapM empty_fail_cond)
  apply (wpsimp wp: mapM_wp_inv)
  done

lemma valid_obj_update:
  fixes val :: "'a::state_ext state"
  assumes valid_obj_f: "\<lbrace> valid_obj p v \<rbrace> f \<lbrace> \<lambda>rv (s :: 'a state). valid_obj p v s\<rbrace>"
  assumes eq : "\<And>r. valid_obj p (P v r) = ((valid_obj p v) :: 'a state \<Rightarrow> bool)"
  shows "\<lbrace>valid_obj p v\<rbrace> f \<lbrace>\<lambda>rv. valid_obj p (P v rv)\<rbrace>"
  by(simp add: eq valid_obj_f)

lemma modify_valid_lift_rv:
  "\<lbrakk> \<And>s rv. P x s = P (f x rv s) s ; \<lbrace>P x\<rbrace> f' \<lbrace> \<lambda>_ s. P x s\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P x\<rbrace> f' \<lbrace> \<lambda>rv s. P (f x rv s) s\<rbrace>"
  by simp

lemma valid_vcpu_regs_update[simp]:
  "valid_obj p (ArchObj (VCPU (vcpu_regs_update f vcpu))) s = valid_obj p (ArchObj (VCPU vcpu)) s"
  by (simp add: valid_vcpu_def valid_obj_def)

lemma valid_vcpu_vgic_update[simp]:
  "valid_obj p (ArchObj (VCPU (vcpu_vgic_update f vcpu))) s = valid_obj p (ArchObj (VCPU vcpu)) s"
  by (simp add: valid_vcpu_def valid_obj_def)

lemma vcpu_save_invs[wp]:
  "\<lbrace>\<lambda>s. invs s\<rbrace> vcpu_save v \<lbrace>\<lambda>_ . invs\<rbrace>"
  apply (clarsimp simp: vcpu_save_def dom_mapM split: option.splits)
  apply (wpsimp wp: set_vcpu_invs_eq_hyp mapM_wp_inv get_vcpu_wp
        | wp hoare_vcg_all_lift hoare_vcg_imp_lift)+
  done

lemma vcpu_disable_invs[wp]:
  "\<lbrace>\<lambda> s. invs s\<rbrace> vcpu_disable v \<lbrace>\<lambda>_ s . invs s\<rbrace>"
  apply (simp add: vcpu_disable_def)
  apply (wpsimp simp: do_machine_op_bind empty_fail_isb empty_fail_cond
                  wp: set_vcpu_invs_eq_hyp get_vcpu_wp maskInterrupt_invs
        | wp hoare_vcg_all_lift hoare_vcg_imp_lift')+
  done

lemma valid_machine_state_arch_state_update [simp]:
  "valid_machine_state (arch_state_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

lemma arm_asid_table_current_vcpu_update[simp]:
  "arm_asid_table ((arm_current_vcpu_update v) (arch_state s)) = arm_asid_table (arch_state s)"
  apply (clarsimp simp add: )
  done

lemma valid_irq_node_arch_state_update [simp]:
  "valid_irq_node (arch_state_update f s) = valid_irq_node s"
  by (simp add: valid_irq_node_def)

lemma valid_vspace_objs_arch_state_update [simp]:
  "valid_vspace_objs (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := v\<rparr>\<rparr>) = valid_vspace_objs s"
  by (simp add: valid_vspace_objs_def vs_lookup_arch_update)

lemma vspace_at_asid_current_vcpu_update [simp]:
  "vspace_at_asid a b (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := v\<rparr>\<rparr>) = vspace_at_asid a b s"
  apply (rule pd_at_asid_arch_up', simp)
  done

lemma valid_kernel_mappings_arch_state_update [simp]:
  "valid_kernel_mappings (arch_state_update f s) = valid_kernel_mappings s"
  by (simp add: valid_kernel_mappings_def)

lemma valid_arch_caps_current_vcpu_update [simp]:
  "valid_arch_caps (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := v\<rparr>\<rparr>) = valid_arch_caps s"
  apply (simp add: valid_arch_caps_def valid_vs_lookup_arch_update)
  by (simp add: valid_table_caps_def arch_cap_fun_lift_def valid_vs_lookup_def
              split: arch_cap.splits option.split)

lemma global_refs_arch_update_eq:
  "\<lbrakk> arm_us_global_pd (f (arch_state s)) = arm_us_global_pd (arch_state s) \<rbrakk>
       \<Longrightarrow> global_refs (arch_state_update f s) = global_refs s"
  by (simp add: global_refs_def)

lemma valid_global_refs_arch_state_update[simp]:
  "valid_refs (global_refs (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := v\<rparr>\<rparr>)) s  = valid_refs (global_refs s) s"
  by (simp add: global_refs_arch_update_eq)

definition "cur_vcpu_at v s \<equiv> case v of None \<Rightarrow> True | Some (vp, _) \<Rightarrow> vcpu_at vp s \<and> obj_at hyp_live vp s"

lemma invs_current_vcpu_update:
  "\<lbrakk>cur_vcpu_at v s; valid_arch_state s\<rbrakk> \<Longrightarrow>
      invs (s\<lparr>arch_state := arch_state s
               \<lparr>arm_current_vcpu := v\<rparr>\<rparr>) = invs s"
  by (auto simp: invs_def valid_state_def cur_tcb_def cur_vcpu_at_def obj_at_conj_distrib
                    valid_global_refs_def valid_asid_map_def valid_arch_state_def
                    valid_global_objs_def valid_global_vspace_mappings_def
          split: option.split)

lemma invs_current_vcpu_update': "\<lbrakk> cur_vcpu_at v s \<and> invs s \<rbrakk>
  \<Longrightarrow> invs (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := v\<rparr>\<rparr>)"
  by (auto simp add: invs_def valid_state_def cur_tcb_def cur_vcpu_at_def obj_at_conj_distrib
            valid_global_refs_def valid_asid_map_def valid_arch_state_def
            valid_global_objs_def valid_global_vspace_mappings_def
           split: option.split)

lemma vgic_update_sym_refs_hyp[wp]:
  "vgic_update vcpuptr f \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vgic_update_def vcpu_update_def
  by (wpsimp wp: set_vcpu_sym_refs_refs_hyp get_vcpu_wp simp: obj_at_def)

lemma vcpu_save_reg_sym_refs_hyp[wp]:
  "vcpu_save_reg vcpuptr r \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vcpu_save_reg_def vcpu_update_def
  by (wpsimp wp: set_vcpu_sym_refs_refs_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift)
     (simp add: obj_at_def)

lemma vcpu_update_regs_sym_refs_hyp[wp]:
  "vcpu_update vcpu_ptr (vcpu_regs_update f) \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp wp: set_vcpu_sym_refs_refs_hyp get_vcpu_wp)
     (simp add: obj_at_def)

lemma vcpu_write_reg_sym_refs_hyp[wp]:
  "vcpu_write_reg vcpu_ptr reg val \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vcpu_write_reg_def by (wpsimp cong: vcpu.fold_congs)

lemma vcpu_update_vtimer_sym_refs_hyp[wp]:
  "vcpu_update vcpu_ptr (vcpu_vtimer_update f) \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp wp: set_vcpu_sym_refs_refs_hyp get_vcpu_wp)
     (simp add: obj_at_def)

crunch save_virt_timer, vcpu_disable, vcpu_invalidate_active, vcpu_restore, vcpu_save, vcpu_switch
  for sym_refs_hyp[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"
  (ignore: vcpu_update wp: crunch_wps)

lemma vcpu_switch_invs[wp]:
"\<lbrace>invs and (\<lambda>s. v \<noteq> None \<longrightarrow> obj_at hyp_live (the v) s)\<rbrace> vcpu_switch v \<lbrace> \<lambda>_ . invs \<rbrace>"
  unfolding vcpu_switch_def
  apply (cases v; clarsimp)
   apply (wpsimp simp: cur_vcpu_at_def | strengthen invs_current_vcpu_update')+
   apply (clarsimp simp: invs_def valid_state_def valid_arch_state_def obj_at_conj_distrib)
  apply (wpsimp simp: cur_vcpu_at_def | strengthen invs_current_vcpu_update')+
  done

crunch setIRQTrigger
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"

lemma dmo_setIRQTrigger_invs[wp]: "\<lbrace>invs\<rbrace> do_machine_op (setIRQTrigger irq b) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: setIRQTrigger_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ setIRQTrigger_irq_masks])
  done

lemma svr_invs [wp]:
  "\<lbrace>invs\<rbrace> set_vm_root t' \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding set_vm_root_def
  apply (wpsimp wp: gets_the_get_tcb_wp hoare_vcg_all_lift hoare_vcg_imp_lift whenE_wp
                    hoare_vcg_disj_lift hoare_drop_imps get_cap_wp
              simp: if_apply_def2)
  apply (thin_tac "cte_wp_at ((=) x) t s" for t)
  apply (drule cte_wp_at_valid_objs_valid_cap, fastforce)
  apply (clarsimp simp: valid_cap_def mask_def)
  done

crunch
  arm_context_switch, vcpu_update, vgic_update, vcpu_disable, vcpu_enable,
  vcpu_restore, vcpu_switch, set_vm_root
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"
  (simp: crunch_simps wp: crunch_wps mapM_x_wp)

lemmas set_vm_root_typ_ats [wp] = abs_typ_at_lifts [OF set_vm_root_typ_at]

lemma valid_pte_lift3:
  assumes x: "(\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>)"
  shows "\<lbrace>\<lambda>s. P (valid_pte pte s)\<rbrace> f \<lbrace>\<lambda>rv s. P (valid_pte pte s)\<rbrace>"
  apply (cases P rule: bool_to_bool_cases; wpsimp; cases pte)
       apply (wpsimp simp:data_at_def wp: hoare_vcg_disj_lift hoare_vcg_const_imp_lift x)+
  done


lemma set_cap_valid_pte_stronger:
  "\<lbrace>\<lambda>s. P (valid_pte pte s)\<rbrace> set_cap cap p \<lbrace>\<lambda>rv s. P (valid_pte pte s)\<rbrace>"
  by (wp valid_pte_lift3 set_cap_typ_at)

end

locale vs_lookup_map_some_pdes = Arch +
  fixes pd pdp s s' S T pd'
  defines "s' \<equiv> s\<lparr>kheap := (kheap s)(pdp \<mapsto> ArchObj (PageDirectory pd'))\<rparr>"
  assumes refs: "vs_refs (ArchObj (PageDirectory pd')) =
                 (vs_refs (ArchObj (PageDirectory pd)) - T) \<union> S"
  assumes old: "kheap s pdp = Some (ArchObj (PageDirectory pd))"
  assumes pts: "\<forall>x \<in> S. page_table_at (snd x) s"
begin

definition
  "new_lookups \<equiv> {((rs,p),(rs',p')). \<exists>r. rs' = r # rs \<and> (r,p') \<in> S \<and> p = pdp}"


lemma vs_lookup1:
  "vs_lookup1 s' \<subseteq> vs_lookup1 s \<union> new_lookups"
  apply (simp add: vs_lookup1_def)
  apply (clarsimp simp: obj_at_def s'_def new_lookups_def)
  apply (auto split: if_split_asm simp: refs old)
  done


lemma vs_lookup_trans:
  "(vs_lookup1 s')^* \<subseteq> (vs_lookup1 s)^* \<union> (vs_lookup1 s)^* O new_lookups^*"
  apply (rule ord_le_eq_trans, rule rtrancl_mono, rule vs_lookup1)
  apply (rule union_trans)
  apply (clarsimp simp add: new_lookups_def)
  apply (drule bspec [OF pts])
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def)
  done


lemma double_new_lookup:
  "\<lbrakk> (x, y) \<in> new_lookups; (y, z) \<in> new_lookups \<rbrakk> \<Longrightarrow> False"
  by (auto simp: new_lookups_def obj_at_def old a_type_def
          dest!: bspec [OF pts])


lemma new_lookups_trans:
  "new_lookups^* = (new_lookups \<union> Id)"
  apply (rule set_eqI, clarsimp, rule iffI)
   apply (erule rtranclE)
    apply simp
   apply (erule rtranclE)
    apply simp
   apply (drule(1) double_new_lookup)
   apply simp
  apply auto
  done


lemma arch_state [simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)


lemma vs_lookup:
  "vs_lookup s' \<subseteq> vs_lookup s \<union> new_lookups^* `` vs_lookup s"
  unfolding vs_lookup_def
  apply (rule order_trans)
   apply (rule Image_mono [OF _ order_refl])
   apply (rule vs_lookup_trans)
  apply (clarsimp simp: relcomp_Image Un_Image)
  done

lemma vs_lookup2:
  "vs_lookup s' \<subseteq> vs_lookup s \<union> (new_lookups `` vs_lookup s)"
  apply (rule order_trans, rule vs_lookup)
  apply (auto simp add: vs_lookup new_lookups_trans)
  done


end

context Arch begin arch_global_naming

lemma set_pd_vspace_objs_map: (* ARMHYP *)
  notes valid_vspace_obj.simps[simp del] and a_type_elims[rule del]
  shows
  "\<lbrace>valid_vspace_objs and
   obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) = vs_refs ko - T \<union> S) p and
   (\<lambda>s. \<forall>x \<in> S. page_table_at (snd x) s) and
   (\<lambda>s. \<forall>(r,p') \<in> S. \<forall>ao. (\<exists>\<rhd>p) s \<longrightarrow> ko_at (ArchObj ao) p' s
                      \<longrightarrow> valid_vspace_obj ao s) and
   (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd) s)\<rbrace>
  set_pd p pd \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (simp add: set_pd_def set_object_def
                   a_type_def[split_simps kernel_object.split arch_kernel_obj.split])
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def valid_vspace_objs_def
           simp del: fun_upd_apply
           split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (frule (1) vs_lookup_map_some_pdes.intro, simp add: obj_at_def)
  apply (frule vs_lookup_map_some_pdes.vs_lookup2)
  apply (drule(1) subsetD)
  apply (erule UnE)
   apply (simp only: fun_upd_apply split: if_split_asm)
    apply (rule valid_vspace_obj_same_type)
      apply fastforce
     apply assumption
    apply (clarsimp simp add: a_type_def)
   apply (rule valid_vspace_obj_same_type)
     apply fastforce
    apply assumption
   apply (clarsimp simp: a_type_def)
  apply (clarsimp simp add: vs_lookup_map_some_pdes.new_lookups_def)
  apply (drule(1) bspec)+
  apply (clarsimp simp add: a_type_simps  split: if_split_asm)
  apply (drule mp, erule exI)+
  apply (erule(1) valid_vspace_obj_same_type)
  apply (simp add: a_type_def)
  done

(* FIXME: move *)
lemma simpler_set_pd_def:
  "set_pd p pd =
   (\<lambda>s. if \<exists>pd. kheap s p = Some (ArchObj (PageDirectory pd))
        then ({((), s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj (PageDirectory pd))\<rparr>)},
              False)
        else ({}, True))"
  apply (rule ext)
  by (auto simp: set_pd_def get_object_def simpler_gets_def assert_def
                 return_def fail_def set_object_def get_def put_def bind_def a_type_def
          split: Structures_A.kernel_object.split arch_kernel_obj.split)

lemma set_pd_valid_vs_lookup_map: (* ARMHYP *)
  "\<lbrace>valid_vs_lookup and valid_arch_state and valid_vspace_objs and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) =
                 vs_refs ko - T \<union> S) p and
    (\<lambda>s. \<forall>x\<in>S. page_table_at (snd x) s) and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) =
                 vs_refs_pages ko - T' \<union> S') p and
    (\<lambda>s. \<forall>(r, p')\<in>S. \<forall>ao. (\<exists>\<rhd> p) s \<longrightarrow>
                           ko_at (ArchObj ao) p' s \<longrightarrow> valid_vspace_obj ao s) and
    (\<lambda>s. (\<exists>\<rhd> p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd) s) and
    (\<lambda>s. \<forall>r. (r \<unrhd> p) s \<longrightarrow>
             (\<forall>c q.
                 pde_ref_pages (pd c) = Some q \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         q \<in> obj_refs cap \<and> vs_cap_ref cap =
         Some (VSRef (ucast c) (Some APageDirectory) # r)))) and
    (\<lambda>s. \<forall>r. (r \<unrhd> p) s \<longrightarrow>
             (\<forall>c q.
                 pde_ref (pd c) = Some q \<longrightarrow>
                    (\<forall>q' pt d. ko_at (ArchObj (PageTable pt)) q s \<longrightarrow>
                        pte_ref_pages (pt d) = Some q' \<longrightarrow>
                        (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                  q' \<in> obj_refs cap \<and> vs_cap_ref cap =
         Some (VSRef (ucast d) (Some APageTable) #
               VSRef (ucast c) (Some APageDirectory) # r)))))\<rbrace>
   set_pd p pd
   \<lbrace>\<lambda>rv. valid_vs_lookup\<rbrace>"
  using set_pd_vspace_objs_map[where p=p and pd=pd and T=T and S=S]
        set_pd_valid_arch[of p pd]
  apply (clarsimp simp: valid_def simpler_set_pd_def)
  apply (drule_tac x=s in spec)+
  apply (clarsimp simp: valid_vs_lookup_def  split: if_split_asm)
  apply (subst caps_of_state_after_update[folded fun_upd_apply],
         simp add: obj_at_def)
  apply (erule (1) vs_lookup_pagesE_alt)
      apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                            fun_upd_def)
     apply (drule_tac x=pa in spec)
     apply simp
     apply (drule vs_lookup_pages_atI)
     apply simp
    apply (drule_tac x=pa in spec)
    apply (drule_tac x="[VSRef (ucast b) (Some AASIDPool),
                         VSRef (ucast a) None]" in spec)+
    apply simp
    apply (drule vs_lookup_pages_apI)
      apply (simp split: if_split_asm)
     apply (simp+)[2]
   apply (frule_tac s="s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj (PageDirectory pd))\<rparr>"
                 in vs_lookup_pages_pdI[rotated -1])
        apply (simp del: fun_upd_apply)+
   apply (frule vs_lookup_pages_apI)
     apply (simp split: if_split_asm)+
   apply (thin_tac "\<forall>r. (r \<unrhd> p) s \<longrightarrow> Q r" for Q)+
   apply (thin_tac "P \<longrightarrow> Q" for P Q)+
   apply (drule_tac x=pa in spec)
   apply (drule_tac x="[VSRef (ucast c) (Some APageDirectory),
                        VSRef (ucast b) (Some AASIDPool),
                        VSRef (ucast a) None]" in spec)
   apply (erule impE)
   apply (erule vs_lookup_pages_pdI)
     apply simp+
  apply (thin_tac "\<forall>r. (r \<unrhd> p) s \<longrightarrow> Q r" for Q)
  apply (thin_tac "P \<longrightarrow> Q" for P Q)+
  apply (case_tac "p=p\<^sub>2")
   apply (thin_tac "\<forall>p ref. P p ref" for P)
   apply (frule vs_lookup_pages_apI)
     apply (simp split: if_split_asm)
    apply simp+
   apply (drule spec, erule impE, assumption)
   apply (clarsimp split: if_split_asm)
   apply (drule_tac x=c in spec)
   apply (simp add: pde_ref_def obj_at_def)
  apply (thin_tac "\<forall>r. (r \<unrhd> p) s \<longrightarrow> Q r" for Q)
  apply (clarsimp split: if_split_asm)
  apply (drule (6) vs_lookup_pages_ptI)
  apply simp
done


lemma set_pd_valid_arch_caps: (* ARMHYP *)
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_vspace_objs and
    valid_objs and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) =
                 vs_refs ko - T \<union> S) p and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) =
                 vs_refs_pages ko - T' \<union> S') p and
    (\<lambda>s. \<forall>x\<in>S. page_table_at (snd x) s) and
    (\<lambda>s. \<forall>p. (VSRef 0 (Some AASIDPool), p) \<notin> S) and
    (\<lambda>s. \<forall>(r, p')\<in>S. \<forall>ao. (\<exists>\<rhd> p) s \<longrightarrow>
                           ko_at (ArchObj ao) p' s \<longrightarrow> valid_vspace_obj ao s) and
    (\<lambda>s. (\<exists>\<rhd> p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd) s) and
    (\<lambda>s. (\<exists>p' cap. caps_of_state s p' = Some cap \<and> is_pd_cap cap \<and>
                   p \<in> obj_refs cap \<and> cap_asid cap \<noteq> None)
       \<or> (obj_at (empty_table {}) p s \<longrightarrow>
                  empty_table {}
                              (ArchObj (PageDirectory pd)))) and
    (\<lambda>s. \<forall>r. (r \<unrhd> p) s \<longrightarrow>
             (\<forall>c q.
                 pde_ref_pages (pd c) = Some q \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         q \<in> obj_refs cap \<and> vs_cap_ref cap =
         Some (VSRef (ucast c) (Some APageDirectory) # r)))) and
    (\<lambda>s. \<forall>r. (r \<unrhd> p) s \<longrightarrow>
             (\<forall>c q.
                 pde_ref (pd c) = Some q \<longrightarrow>
                    (\<forall>q' pt d. ko_at (ArchObj (PageTable pt)) q s \<longrightarrow>
                        pte_ref_pages (pt d) = Some q' \<longrightarrow>
                        (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                  q' \<in> obj_refs cap \<and> vs_cap_ref cap =
         Some (VSRef (ucast d) (Some APageTable) #
               VSRef (ucast c) (Some APageDirectory) # r)))))\<rbrace>
   set_pd p pd
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: set_pd_def set_object_def
                   a_type_def[split_simps kernel_object.split arch_kernel_obj.split])
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def simp del: fun_upd_apply
                 split: Structures_A.kernel_object.split arch_kernel_obj.split)
  apply (clarsimp simp: valid_arch_caps_def)
  apply (subst caps_of_state_after_update[folded fun_upd_def],
         simp add: obj_at_def)+
  apply simp
  apply (rule conjI)
  using set_pd_valid_vs_lookup_map[where p=p and pd=pd and T=T and S=S
      and T'=T' and S'=S']
   apply (clarsimp simp add: valid_def)
   apply (drule_tac x=s in spec)
   apply (simp add: simpler_set_pd_def obj_at_def)
  apply (simp add: valid_table_caps_def obj_at_def
                   caps_of_state_after_update[folded fun_upd_def]
              del: imp_disjL)
  apply (drule_tac x=p in spec, elim allEI, intro impI)
  apply clarsimp
  apply (erule_tac P="is_pd_cap cap" in disjE)
   prefer 2
   apply (frule_tac p="(a,b)" in caps_of_state_valid_cap, simp)
   apply (clarsimp simp add: is_pt_cap_def valid_cap_def obj_at_def
                             valid_arch_cap_def
                             a_type_def)
  apply (frule_tac cap=cap and cap'="ArchObjectCap acap" and cs="caps_of_state s" in unique_table_caps_pdD)
        apply (simp add: is_pd_cap_def)+
    apply (clarsimp simp: is_pd_cap_def)+
  done

(* FIXME: move to wellformed *)
lemma global_pde_graph_ofI:
 " \<lbrakk>pd x = pde; pde_ref pde = Some v\<rbrakk>
  \<Longrightarrow> (x, v) \<in> graph_of (pde_ref o pd)"
  by (clarsimp simp: graph_of_def pde_ref_def comp_def)



lemma set_pd_valid_kernel_mappings_map:
  "\<lbrace>valid_kernel_mappings and
     obj_at (\<lambda>ko. glob_vs_refs (ArchObj (PageDirectory pd)) = glob_vs_refs ko - T \<union> S) p and
     (\<lambda>s. \<forall>(r,p) \<in> S. (r \<in> kernel_vsrefs)
                         = (p \<in> {}))\<rbrace>
     set_pd p pd
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_v_ker_map get_object_wp)
  apply (clarsimp simp: obj_at_def valid_kernel_mappings_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma glob_vs_refs_subset:
  " vs_refs x \<subseteq> glob_vs_refs x"
  apply (clarsimp simp: glob_vs_refs_def vs_refs_def)
  apply (clarsimp split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule pair_imageI)
  apply (simp add: graph_of_def split:if_split_asm)
  done

lemma vs_refs_pages_pdI:
  "\<lbrakk>pde_ref_pages (pd x) = Some a\<rbrakk>
    \<Longrightarrow> (VSRef (ucast x) (Some APageDirectory), a) \<in> vs_refs_pages (ArchObj (PageDirectory pd))"
  by (auto simp: pde_ref_pages_def vs_refs_pages_def graph_of_def image_def split: pde.splits)

lemma pde_ref_pde_ref_pagesI[elim!]:
  "pde_ref (pd x) = Some a \<Longrightarrow> pde_ref_pages (pd x) = Some a"
  by (auto simp: pde_ref_def pde_ref_pages_def split: pde.splits)

lemma vs_refs_pdI2:
  "\<lbrakk>pd r = PageTablePDE x\<rbrakk>
   \<Longrightarrow> (VSRef (ucast r) (Some APageDirectory), ptrFromPAddr x) \<in> vs_refs (ArchObj (PageDirectory pd))"
  by (auto simp: vs_refs_def pde_ref_def graph_of_def)


lemma set_pd_invs_map:
  "\<lbrace>invs and (\<lambda>s. \<forall>i. wellformed_pde (pd i)) and
     obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) = vs_refs ko \<union> S) p and
     obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) = vs_refs_pages ko - T' \<union> S') p and
     obj_at (\<lambda>ko. \<exists>pd'. ko = ArchObj (PageDirectory pd')
                 \<comment> \<open>\<and> (\<forall>x. pd x = pd' x)\<close>) p and
     (\<lambda>s. \<forall>(r,p) \<in> S. \<forall>ao. ko_at (ArchObj ao) p s \<longrightarrow> valid_vspace_obj ao s) and
     (\<lambda>s. \<forall>(r,p) \<in> S. page_table_at p s) and
     (\<lambda>s. \<forall>(r,p) \<in> S. (r \<in> kernel_vsrefs)
                         = (p \<in> {})) and
     (\<lambda>s. \<exists>p' cap. caps_of_state s p' = Some cap \<and> is_pd_cap cap
                  \<and> p \<in> obj_refs cap \<and> cap_asid cap \<noteq> None) and
     (\<lambda>s. \<forall>p. (VSRef 0 (Some AASIDPool), p) \<notin> S) and
     (\<lambda>s. \<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
              (\<forall>(r, p) \<in> S'. \<exists>p' cap. caps_of_state s p' = Some cap \<and> p \<in> obj_refs cap
                                       \<and> vs_cap_ref cap = Some (r # ref))) and
     (\<lambda>s. \<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
              (\<forall>(r, p) \<in> S. (\<forall>q' pt d.
                      ko_at (ArchObj (PageTable pt)) p s \<longrightarrow>
                      pte_ref_pages (pt d) = Some q' \<longrightarrow>
                      (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                q' \<in> obj_refs cap \<and>
                                vs_cap_ref cap =
                                Some (VSRef (ucast d) (Some APageTable) # r # ref))))) and

     valid_vspace_obj (PageDirectory pd)\<rbrace>
  set_pd p pd \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_pd_valid_objs set_pd_iflive set_pd_zombies
             set_pd_zombies_state_refs set_pd_zombies_state_hyp_refs set_pd_valid_mdb
             set_pd_valid_idle set_pd_ifunsafe set_pd_reply_caps
             set_pd_valid_arch set_pd_valid_global set_pd_cur
             set_pd_reply_masters valid_irq_node_typ
             set_pd_vspace_objs_map[where S=S and T="{}"]
             set_pd_valid_arch_caps[where S=S and T="{}" and S'=S' and T'=T']
             valid_irq_handlers_lift
             set_pd_valid_kernel_mappings_map[where S=S and T="{}"]
             set_pd_equal_kernel_mappings_triv)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule(1) valid_global_refsD2)
  apply (clarsimp simp: cap_range_def split_def)
  apply (rule conjI)
   apply clarsimp
   apply (frule vs_refs_pages_pdI)
   apply (clarsimp simp: obj_at_def)
   apply (erule disjE)
    apply (clarsimp simp: valid_arch_caps_def)
    apply (drule valid_vs_lookupD[OF vs_lookup_pages_step])
      apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
      apply (rule_tac x="VSRef (ucast c) (Some APageDirectory)" in exI)
      apply (erule conjI[OF refl])
     apply simp
    apply clarsimp
   apply (erule_tac x=r in allE, drule (1) mp, drule (1) bspec)
   apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: pde_ref_def split: pde.splits)
   apply (frule vs_refs_pdI2)
   apply (clarsimp simp: obj_at_def)
   apply (erule disjE)
    apply (clarsimp simp: valid_arch_caps_def)
    apply (drule valid_vs_lookupD[OF vs_lookup_pages_step[OF vs_lookup_pages_step]])
       apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
       apply (rule_tac x="VSRef (ucast c) (Some APageDirectory)" in exI)
       apply (rule conjI[OF refl])
       apply (erule subsetD[OF vs_refs_pages_subset])
      apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
      apply (rule_tac x="VSRef (ucast d) (Some APageTable)" in exI)
      apply (rule conjI[OF refl])
      apply (erule pte_ref_pagesD)
     apply simp
    apply clarsimp
   apply (erule_tac x=r in allE, drule (1) mp, drule_tac P="(%x. \<forall>q' pt. Q x q' pt y s)" for Q s in bspec)
    apply simp
   apply clarsimp
  apply (clarsimp simp add: obj_at_def glob_vs_refs_def)
  apply safe
    apply (rule pair_imageI)
    apply (clarsimp simp add: graph_of_def)+
    apply (frule_tac pde="pd ab" in pde_graph_ofI[rotated])
     prefer 2
     apply (clarsimp simp: vs_refs_def)
     apply (drule_tac x="(ab,bb)" and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageDirectory), y))" in imageI)
     prefer 2
     apply (rule refl)
    apply simp
    apply (erule imageE)
    apply (simp add: graph_of_def split_def)
   apply (rule pair_imageI)
   apply (clarsimp simp add: graph_of_def)+
   apply (frule_tac pde_graph_ofI[rotated])
    prefer 2
    apply (clarsimp simp: vs_refs_def)
    apply (drule_tac x="(ab,bb)" and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageDirectory), y))" in imageI)
    prefer 2
    apply (rule refl)
   apply (drule_tac s="(\<lambda>(r, y). (VSRef (ucast r) (Some APageDirectory), y)) ` graph_of (\<lambda>x. pde_ref (pd x)) " in sym)
   apply simp
   apply (drule_tac c="(VSRef (ucast ab) (Some APageDirectory), bb)" and B=S in UnI1)
   apply simp
   apply (erule imageE)
   apply (simp add: graph_of_def split_def)
  apply (subst (asm) Un_commute[where B=S])
  apply (drule_tac c="(aa,ba)" and B="vs_refs (ArchObj (PageDirectory pd'))" in UnI1)
  apply (drule_tac t="S \<union> vs_refs (ArchObj (PageDirectory pd'))" in sym)
  apply (simp del:Un_iff)
  apply (drule rev_subsetD[OF _ glob_vs_refs_subset])
  apply (simp add: glob_vs_refs_def)
done

lemma vs_refs_add_one': (* ARMHYP does this hold for all p? *)
  "vs_refs (ArchObj (PageDirectory (pd (p := pde)))) =
   vs_refs (ArchObj (PageDirectory pd))
       - Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref (pd p))
       \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref pde)"
  apply (simp add: vs_refs_def)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp del: disjCI dest!: graph_ofD split: if_split_asm)
   apply (rule disjI1)
   apply (rule conjI)
    apply (rule_tac x="(aa,ba)" in image_eqI)
     apply simp
    apply (simp add: graph_of_def)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp dest!: graph_ofD)
   apply (rule_tac x="(aa,ba)" in image_eqI)
    apply simp
   apply (clarsimp simp: graph_of_def split:if_split_asm)
  apply clarsimp
  apply (rule_tac x="(p,x)" in image_eqI)
   apply simp
  apply (clarsimp simp: graph_of_def)
  done


lemma vs_refs_add_one:
  "\<lbrakk>pde_ref (pd p) = None\<rbrakk> \<Longrightarrow>
   vs_refs (ArchObj (PageDirectory (pd (p := pde)))) =
   vs_refs (ArchObj (PageDirectory pd))
       \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref pde)"
  by (simp add: vs_refs_add_one')


lemma vs_refs_pages_add_one': (* AARMHYP does this hold for all p? *)
  "vs_refs_pages (ArchObj (PageDirectory (pd (p := pde)))) =
   vs_refs_pages (ArchObj (PageDirectory pd))
       - Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref_pages (pd p))
       \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref_pages pde)"
  apply (simp add: vs_refs_pages_def)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp del: disjCI dest!: graph_ofD split: if_split_asm)
   apply (rule disjI1)
   apply (rule conjI)
    apply (rule_tac x="(aa,ba)" in image_eqI)
     apply simp
    apply (simp add: graph_of_def)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp dest!: graph_ofD)
   apply (rule_tac x="(aa,ba)" in image_eqI)
    apply simp
   apply (clarsimp simp: graph_of_def split:if_split_asm)
  apply clarsimp
  apply (rule_tac x="(p,x)" in image_eqI)
   apply simp
  apply (clarsimp simp: graph_of_def)
  done

lemma vs_refs_pages_add_one:
  "\<lbrakk>pde_ref_pages (pd p) = None\<rbrakk> \<Longrightarrow>
   vs_refs_pages (ArchObj (PageDirectory (pd (p := pde)))) =
   vs_refs_pages (ArchObj (PageDirectory pd))
       \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref_pages pde)"
  by (simp add: vs_refs_pages_add_one')

definition is_asid_pool_cap :: "cap \<Rightarrow> bool"
 where "is_asid_pool_cap cap \<equiv> \<exists>ptr asid. cap = cap.ArchObjectCap (arch_cap.ASIDPoolCap ptr asid)"


(* FIXME: move *)
lemma valid_cap_to_pt_cap:
  "\<lbrakk>valid_cap c s; obj_refs c = {p}; page_table_at p s\<rbrakk> \<Longrightarrow> is_pt_cap c"
  by (clarsimp simp: valid_cap_def obj_at_def is_obj_defs is_pt_cap_def
              split: cap.splits option.splits arch_cap.splits if_splits)

lemma ref_is_unique: (* ARMHYP *)
  "\<lbrakk>(ref \<rhd> p) s; (ref' \<rhd> p) s; p \<notin> {};
    valid_vs_lookup s; unique_table_refs (caps_of_state s);
    valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s;
    valid_caps (caps_of_state s) s\<rbrakk>
   \<Longrightarrow> ref = ref'"
  apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
    apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
      apply (clarsimp simp: valid_asid_table_def up_ucast_inj_eq)
      apply (erule (2) inj_on_domD)
     apply ((clarsimp simp: obj_at_def)+)[2]
   apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
     apply (clarsimp simp: obj_at_def)
    apply (drule (2) vs_lookup_apI)+
    apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI]
                           obj_ref_elemD
                     simp: table_cap_ref_ap_eq[symmetric])
    apply (drule_tac cap=cap and cap'=capa in unique_table_refsD, simp+)[1]
   apply (clarsimp simp: obj_at_def)
  apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
    apply ((clarsimp simp: obj_at_def)+)[2]
  apply (simp add: pde_ref_def split: pde.splits)
  apply (drule (4) vs_lookup_pdI)+
  apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI]
                         obj_ref_elemD)
  apply (drule_tac cap=cap and cap'=capa in unique_table_refsD, simp+)[1]
  apply (drule (3) valid_capsD[THEN valid_cap_to_pt_cap])+
  apply (clarsimp simp: is_pt_cap_def table_cap_ref_simps vs_cap_ref_simps)
  done

lemma mask_shift_mask_helper:
  "(p && mask pd_bits >> pde_bits) && mask 11 = (p && mask pd_bits >> pde_bits)"
  apply (rule word_eqI)
  apply (simp add: word_size vspace_bits_defs nth_shiftr conj_comms)
  done

lemma ucast_ucast_mask_shift_helper:
  "ucast (ucast (p && mask pd_bits >> pde_bits :: word32) :: 11 word)
        = (p && mask pd_bits >> pde_bits :: word32)"
  apply (rule ucast_ucast_len)
  apply (rule shiftr_less_t2n)
  apply (simp add: vspace_bits_defs)
  apply (rule order_less_le_trans, rule and_mask_less_size)
   apply (simp add: word_size)+
  done

lemma unat_ucast_pd_bits_shift:
  "unat (ucast ((p :: word32) && mask pd_bits >> pde_bits) :: 11 word)
       = unat (p && mask pd_bits >> pde_bits)"
  apply (simp only: unat_ucast)
  apply (rule mod_less)
  apply (rule unat_less_power)
   apply (simp add: word_bits_def)
  apply (rule shiftr_less_t2n)
  apply (rule order_le_less_trans [OF word_and_le1])
  apply (simp add: vspace_bits_defs mask_def)
  done

lemma vs_lookup_typI: (* ARMHYP *)
  "\<lbrakk>(r \<rhd> p) s; valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> page_table_at p s
    \<or> page_directory_at p s
    \<or> asid_pool_at p s"
  apply (erule (1) vs_lookupE_alt)
     apply (clarsimp simp: ran_def)
     apply (drule (2) valid_asid_tableD)
    apply simp+
  done

lemma vs_lookup_vs_lookup_pagesI':
  "\<lbrakk>(r \<unrhd> p) s; page_table_at p s \<or> page_directory_at p s \<or> asid_pool_at p s;
    valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> (r \<rhd> p) s"
  apply (erule (1) vs_lookup_pagesE_alt)
      apply (clarsimp simp:ran_def)
      apply (drule (2) valid_asid_tableD)
     apply (rule vs_lookupI)
      apply (fastforce simp: vs_asid_refs_def graph_of_def)
     apply simp
    apply (rule vs_lookupI)
     apply (fastforce simp: vs_asid_refs_def graph_of_def)
    apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
    apply (fastforce simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
   apply (rule vs_lookupI)
    apply (fastforce simp: vs_asid_refs_def graph_of_def)
   apply (rule_tac y="([VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None], p\<^sub>2)" in rtrancl_trans)
    apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
    apply (fastforce simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
   apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
   apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
   apply (rule_tac x="(c, p)" in image_eqI)
    apply simp
   apply (fastforce simp: pde_ref_def pde_ref_pages_def valid_pde_def obj_at_def
                         a_type_def data_at_def
                   split:pde.splits)
  apply (rule vs_lookupI)
   apply (fastforce simp: vs_asid_refs_def graph_of_def)
  apply (rule_tac y="([VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None], p\<^sub>2)" in rtrancl_trans)
   apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
   apply (fastforce simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
  apply (rule_tac y="([VSRef (ucast c) (Some APageDirectory), VSRef (ucast b) (Some AASIDPool),
           VSRef (ucast a) None], (ptrFromPAddr addr))" in rtrancl_trans)
   apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
   apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
   apply (rule_tac x="(c,(ptrFromPAddr addr))" in image_eqI)
    apply simp
   apply (clarsimp simp: pde_ref_def)
  apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
  apply (auto simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def pte_ref_pages_def a_type_def data_at_def
                  split: pte.splits)
  done

lemma vs_lookup_vs_lookup_pagesI:
  "\<lbrakk>(r \<rhd> p) s; (r' \<unrhd> p) s; valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> (r' \<rhd> p) s"
  by (erule (5) vs_lookup_vs_lookup_pagesI'[OF _ vs_lookup_typI])

(* FIXME: move *)
lemma valid_cap_to_pd_cap:
  "\<lbrakk>valid_cap c s; obj_refs c = {p}; page_directory_at p s\<rbrakk> \<Longrightarrow> is_pd_cap c"
  by (clarsimp simp: valid_cap_def obj_at_def is_obj_defs is_pd_cap_def
              split: cap.splits option.splits arch_cap.splits if_splits)

lemma store_pde_map_invs:
  "\<lbrace>(\<lambda>s. wellformed_pde pde) and invs and empty_pde_at p and valid_pde pde
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p \<longrightarrow> (\<exists>ao. ko_at (ArchObj ao) p s \<and> valid_vspace_obj ao s))
     and K (VSRef (p && mask pd_bits >> pde_bits) (Some APageDirectory)
               \<notin> kernel_vsrefs)
     and (\<lambda>s. \<exists>r. (r \<rhd> (p && (~~ mask pd_bits))) s \<and>
           (\<forall>p'. pde_ref_pages pde = Some p' \<longrightarrow>
              (\<exists>p'' cap. caps_of_state s p'' = Some cap \<and> p' \<in> obj_refs cap
                      \<and> vs_cap_ref cap = Some (VSRef (p && mask pd_bits >> pde_bits) (Some APageDirectory) # r))
                 \<and> (\<forall>p'''. pde = PageTablePDE p''' \<longrightarrow>
                      (\<forall>pt. ko_at (ArchObj (PageTable pt)) (ptrFromPAddr p''') s \<longrightarrow>
                         (\<forall>x word. pte_ref_pages (pt x) = Some word \<longrightarrow>
                            (\<exists>p'' cap. caps_of_state s p'' = Some cap \<and> word \<in> obj_refs cap
                                \<and> vs_cap_ref cap =
                                   Some (VSRef (ucast x) (Some APageTable)
                                    # VSRef (p && mask pd_bits >> pde_bits) (Some APageDirectory)
                                    # r)))))))\<rbrace>
  store_pde p pde \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pde_def kernel_vsrefs_def)
  apply (wp dmo_invs set_pd_invs_map)
  apply clarsimp
  apply (rule conjI)
   apply (drule invs_valid_objs)
   apply (fastforce simp: valid_objs_def dom_def obj_at_def valid_obj_def)
  apply (rule conjI)
   apply (clarsimp simp: empty_pde_at_def)
   apply (clarsimp simp: obj_at_def)
   apply (rule vs_refs_add_one)
    subgoal by (auto simp add: pde_ref_def vspace_bits_defs)
  apply (rule conjI)
   apply (clarsimp simp: empty_pde_at_def)
   apply (clarsimp simp: obj_at_def)
   apply (rule vs_refs_pages_add_one')

  apply (rule conjI)
   apply (clarsimp simp: obj_at_def)
   defer
  apply (rule conjI)
   subgoal by (clarsimp simp: obj_at_def)

  apply (rule conjI)
   apply clarsimp
   subgoal by (case_tac pde, simp_all add: pde_ref_def)
  apply (rule conjI)
   apply (clarsimp simp: kernel_vsrefs_def
                         ucast_ucast_mask_shift_helper)
  apply (rule conjI)
   apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp+)
   apply (rule_tac x=a in exI, rule_tac x=b in exI, rule_tac x=cap in exI)
   apply (clarsimp dest!: obj_ref_elemD)
   apply (frule caps_of_state_valid_cap, clarsimp)
   apply (drule (1) valid_cap_to_pd_cap, simp add: obj_at_def a_type_simps)
   apply (thin_tac " \<forall>p. Q p \<longrightarrow> P p" for Q P)+
   subgoal by (simp add: is_pd_cap_def vs_cap_ref_def vspace_bits_defs arch_cap_fun_lift_def
                  split: cap.split_asm arch_cap.split_asm option.split_asm)
  apply (rule conjI)
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (frule (2) ref_is_unique[OF _ vs_lookup_vs_lookup_pagesI])
           apply ((clarsimp simp: invs_def valid_state_def valid_arch_caps_def
                                  valid_arch_state_def)+)[2]
         apply (auto dest!: simp: obj_at_def)[1]
        apply clarsimp+
    apply (rule valid_objs_caps)
    apply clarsimp
   apply (simp add: ucast_ucast_mask mask_shift_mask_helper)
   apply auto[1]

  apply clarsimp
  apply (frule (1) valid_vspace_objsD, fastforce)
  apply clarsimp
  apply (drule pde_ref_pde_ref_pagesI)
  apply clarsimp
  apply (simp add: ucast_ucast_mask mask_shift_mask_helper)
  apply (clarsimp simp: pde_ref_pages_def obj_at_def
                 split: pde.splits)
  apply (erule_tac x=d in allE, erule_tac x=q' in allE)
  apply (frule (2) ref_is_unique[OF _ vs_lookup_vs_lookup_pagesI])
          apply ((clarsimp simp: invs_def valid_state_def valid_arch_caps_def
                                 valid_arch_state_def)+)[2]
        apply (auto simp: obj_at_def)[1]
       apply (clarsimp simp add: data_at_def)+
   apply (rule valid_objs_caps)
   apply ((clarsimp elim!: impE)+)[2]
  apply (auto simp add: obj_at_def data_at_def ucast_ucast_mask mask_shift_mask_helper)
  done

lemma set_cap_empty_pde:
  "\<lbrace>empty_pde_at p and cte_at p'\<rbrace> set_cap cap p' \<lbrace>\<lambda>_. empty_pde_at p\<rbrace>"
  apply (simp add: empty_pde_at_def)
  apply (rule hoare_pre)
   apply (wp set_cap_obj_at_other hoare_vcg_ex_lift)
  apply clarsimp
  apply (rule exI, rule conjI, assumption)
  apply (erule conjI)
  apply (clarsimp simp: cte_wp_at_cases obj_at_def)
  done

lemma valid_cap_obj_ref_pt_pd:
  "\<lbrakk> s \<turnstile> cap; s \<turnstile> cap'; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> (is_pt_cap cap \<longrightarrow> is_pt_cap cap')
         \<and> (is_pd_cap cap \<longrightarrow> is_pd_cap cap')"
  by (auto simp: is_cap_simps valid_cap_def
                 obj_at_def is_ep is_ntfn is_cap_table
                 is_tcb a_type_def
          split: cap.split_asm if_split_asm
                 arch_cap.split_asm option.split_asm)



lemma is_pt_pd_cap_asid_None_table_ref:
  "is_pt_cap cap \<or> is_pd_cap cap
     \<Longrightarrow> ((table_cap_ref cap = None) = (cap_asid cap = None))"
  by (auto simp: is_cap_simps table_cap_ref_def cap_asid_def
          split: option.split_asm)

lemma no_cap_to_obj_with_diff_ref_map:
  "\<lbrakk> caps_of_state s p = Some cap; is_pt_cap cap \<or> is_pd_cap cap;
     table_cap_ref cap = None;
     unique_table_caps (caps_of_state s);
     valid_objs s; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' {p} s"
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid_cap[where p=p])
  apply (frule(1) caps_of_state_valid_cap[where p="(a, b)" for a b])
  apply (drule(1) valid_cap_obj_ref_pt_pd, simp)
  apply (drule(1) unique_table_capsD[rotated, where cps="caps_of_state s"])
      apply simp
     apply (simp add: is_pt_pd_cap_asid_None_table_ref)
    apply fastforce
   apply assumption
  apply simp
  done


lemmas store_pte_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pte_caps_of_state]

lemma mdb_cte_at_store_pte[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>
   store_pte y pte
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
    apply (simp add:store_pte_def set_pt_def)
    apply (wp|simp)+
  done

lemma valid_idle_store_pte[wp]:
  "\<lbrace>valid_idle\<rbrace> store_pte y pte \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: store_pte_def)
  apply wp
    apply (simp add: set_pt_def)
    apply (rule set_object_idle[THEN hoare_set_object_weaken_pre])
   apply wpsimp
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma mapM_swp_store_pte_invs[wp]:
  "\<lbrace>invs and (\<lambda>s. (\<exists>p\<in>set slots. (\<exists>\<rhd> (p && ~~ mask pt_bits)) s) \<longrightarrow>
                  valid_pte pte s) and
    (\<lambda>s. wellformed_pte pte) and
    (\<lambda>s. \<exists>slot. cte_wp_at
           (\<lambda>c. image (\<lambda>x. x && ~~ mask pt_bits) (set slots) \<subseteq> obj_refs c \<and>
                is_pt_cap c \<and> (pte = InvalidPTE \<or>
                               cap_asid c \<noteq> None)) slot s) and
   (\<lambda>s. \<forall>p\<in>set slots. \<forall>ref. (ref \<rhd> (p && ~~ mask pt_bits)) s \<longrightarrow>
              (\<forall>q. pte_ref_pages pte = Some q \<longrightarrow>
                   (\<exists>p' cap.
                       caps_of_state s p' = Some cap \<and>
                       q \<in> obj_refs cap \<and>
                       vs_cap_ref cap =
                       Some
                        (VSRef (p && mask pt_bits >> 3) (Some APageTable) #
                         ref))))\<rbrace>
     mapM (swp store_pte pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp_all
  apply (wp hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_ball_lift
            hoare_vcg_all_lift hoare_vcg_imp_lift)
      apply clarsimp+
  apply (intro conjI)
   apply clarsimp+
by (fastforce simp: vspace_bits_defs cte_wp_at_caps_of_state is_pt_cap_def cap_asid_def)+


lemmas store_pde_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pde_caps_of_state]

crunch store_pde
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"
    (wp: get_object_wp) (* added by sjw, something dropped out of some set :( *)

lemma mapM_swp_store_pde_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>sl\<in>set slots. sl && ~~ mask pd_bits \<notin> global_refs s) and
    K (pde = InvalidPDE)\<rbrace>
  mapM (swp store_pde pde) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (rule hoare_pre, wp store_pde_invs_unmap hoare_vcg_const_Ball_lift
                             hoare_vcg_ex_lift)
    apply clarsimp+
  done

lemma vs_refs_pdI3:
  "\<lbrakk>pde_ref (pd x) = Some p\<rbrakk>
   \<Longrightarrow> (VSRef (ucast x) (Some APageDirectory), p) \<in> vs_refs (ArchObj (PageDirectory pd))"
  by (auto simp: pde_ref_def vs_refs_def graph_of_def)


lemma set_pd_invs_unmap':
  "\<lbrace>invs and (\<lambda>s. \<forall>i. wellformed_pde (pd i)) and
    (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd) s) and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) = vs_refs ko - T) p and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) = vs_refs_pages ko - T' \<union> S') p and
    obj_at (\<lambda>ko. \<exists>pd'. ko = ArchObj (PageDirectory pd')) p and
    (\<lambda>s. p \<notin> global_refs s) and
    (\<lambda>s. \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and>
                   is_pd_cap cap \<and>
                   p \<in> obj_refs cap \<and> (\<exists>y. cap_asid cap = Some y)) and
    (\<lambda>s. \<forall>(a,b)\<in>S'. (\<forall>ref.
                  (ref \<unrhd> p) s \<longrightarrow>
                    (\<exists>p' cap.
                      caps_of_state s p' = Some cap \<and>
                      b \<in> obj_refs cap \<and> vs_cap_ref cap = Some (a # ref))))\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_caps_def)
  apply (rule hoare_pre)
   apply (wp set_pd_valid_objs set_pd_iflive set_pd_zombies
             set_pd_zombies_state_refs set_pd_zombies_state_hyp_refs set_pd_valid_mdb
             set_pd_valid_idle set_pd_ifunsafe set_pd_reply_caps
             set_pd_valid_arch set_pd_valid_global set_pd_cur
             set_pd_reply_masters valid_irq_node_typ
             set_pd_vspace_objs_unmap set_pd_valid_vs_lookup_map[where T=T and S="{}" and T'=T' and S'=S']
             valid_irq_handlers_lift
             set_pd_unmap_mappings set_pd_equal_kernel_mappings_triv)
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_arch_caps_def valid_objs_caps obj_at_def
    del: disjCI)
  apply (rule conjI, clarsimp)
   apply (erule_tac x="(VSRef (ucast c) (Some APageDirectory), q)" in ballE)
    apply clarsimp
   apply (frule vs_refs_pages_pdI)
   apply (clarsimp simp: valid_arch_caps_def)
    apply (drule_tac p'=q and ref'="VSRef (ucast c) (Some APageDirectory) # r" in vs_lookup_pages_step)
    apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
   apply (drule (1) valid_vs_lookupD)
   apply (clarsimp)
   apply clarsimp
   apply (drule vs_refs_pdI3)
   apply clarsimp
   apply (drule_tac p'=q and ref'="VSRef (ucast c) (Some APageDirectory) # r" in vs_lookup_pages_step)
    apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
    apply (erule subsetD[OF vs_refs_pages_subset])
   apply (drule_tac p'=q' and ref'="VSRef (ucast d) (Some APageTable) # VSRef (ucast c) (Some APageDirectory) # r"
                 in vs_lookup_pages_step)
    apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
    apply (erule pte_ref_pagesD)
   apply (drule (1) valid_vs_lookupD)
   apply clarsimp
  done

lemma same_refs_lD:
  "\<lbrakk>same_refs (Inl(pte,p # slots)) cap s\<rbrakk>
 \<Longrightarrow> (\<exists>p. pte_ref_pages pte = Some p \<and> p \<in> obj_refs cap) \<and>
  (\<forall>ref. (ref \<rhd> (p && ~~ mask pt_bits)) s \<longrightarrow>
  vs_cap_ref cap = Some (VSRef (p && mask pt_bits >> 3) (Some APageTable) # ref))"
  apply (clarsimp simp:same_refs_def split:list.splits)
  done

lemma same_refs_rD:
  "\<lbrakk>same_refs (Inr(pde,p # slots)) cap s\<rbrakk>
 \<Longrightarrow>  (\<exists>p. pde_ref_pages pde = Some p \<and> p \<in> obj_refs cap) \<and>
         (\<forall>ref. (ref \<rhd> (p && ~~ mask pd_bits)) s \<longrightarrow>
               vs_cap_ref cap =
               Some (VSRef (p && mask pd_bits >> 3) (Some APageDirectory) # ref))"
   by (clarsimp simp:same_refs_def split:list.splits)

lemma store_pde_invs_unmap':
  "\<lbrace>invs
    and (\<exists>\<rhd> (p && ~~ mask pd_bits))
    and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs (Inr (pde, slots))) slot s)
    and (\<lambda>s. \<exists>ptr cap. caps_of_state s ptr = Some cap
                    \<and> is_pg_cap cap
                    \<and> same_refs (Inr (pde, slots)) cap s)
    and valid_pde pde
    and (\<lambda>s. p && ~~ mask pd_bits \<notin> global_refs s)
    and K (wellformed_pde pde \<and> pde_ref pde = None)
    and K (\<comment> \<open>ucast (p && mask pd_bits >> 2) \<notin> kernel_mapping_slots
           \<and>\<close>(\<exists>xs. slots = p # xs) )
    and (\<lambda>s. \<exists>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s)\<rbrace>
   store_pde p pde
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_name_pre_state)
   apply (clarsimp simp: store_pde_def | wp)+
    apply (rule_tac T ="  Pair (VSRef (p && mask pd_bits >> 3) (Some APageDirectory))
                        ` set_option (pde_ref (pd (ucast (p && mask pd_bits >> 3))))"
                and T'="  Pair (VSRef (p && mask pd_bits >> 3) (Some APageDirectory))
                        ` set_option (pde_ref_pages (pd (ucast (p && mask pd_bits >> 3))))"
                and S'="  Pair (VSRef (p && mask pd_bits >> 3) (Some APageDirectory))
                        ` set_option (pde_ref_pages pde)" in set_pd_invs_unmap')
  apply wp
  apply (clarsimp simp: obj_at_def)
  apply (rule conjI)
   apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def
                             valid_objs_def valid_obj_def dom_def)
   apply (erule_tac P="\<lambda>x. (\<exists>y. a y x) \<longrightarrow> b x" for a b in allE[where x="(p && ~~ mask pd_bits)"])
   apply (erule impE)
    apply (clarsimp simp: obj_at_def vs_refs_def)+

  apply (rule conjI)
   apply (clarsimp simp add: invs_def valid_state_def valid_vspace_objs_def)
   apply (erule_tac P="\<lambda>x. (\<exists>y. a y x) \<longrightarrow> b x" for a b in allE[where x="(p && ~~ mask pd_bits)"])
   apply (erule impE)
    apply (erule_tac x=ref in exI)
   apply (erule_tac x="PageDirectory pd" in allE)
   apply (clarsimp simp: obj_at_def)

  apply (rule conjI)
   apply (safe)[1]
     apply (clarsimp simp add: vs_refs_def graph_of_def split: if_split_asm)
     apply (rule pair_imageI)
     apply (clarsimp)
    apply (clarsimp simp: vs_refs_def graph_of_def pde_bits_def split: if_split_asm)
    apply (subst (asm) ucast_ucast_mask_shift_helper[simplified pde_bits_def, symmetric], simp)
   apply (clarsimp simp: vs_refs_def graph_of_def vspace_bits_defs split: if_split_asm)
   apply (rule_tac x="(ac, bc)" in image_eqI)
    apply clarsimp
   apply (clarsimp simp: ucast_ucast_mask_shift_helper[simplified vspace_bits_defs, simplified])
  apply (rule conjI)
   apply safe[1]
      apply (clarsimp simp: vs_refs_pages_def graph_of_def vspace_bits_defs
                            ucast_ucast_mask_shift_helper[simplified vspace_bits_defs, simplified]
                      split: if_split_asm)
      apply (rule_tac x="(ac, bc)" in image_eqI)
       apply clarsimp
      apply clarsimp
     apply (clarsimp simp: vs_refs_pages_def graph_of_def ucast_ucast_id vspace_bits_defs
                     split: if_split_asm)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def
                    split: if_split_asm)
    apply (rule_tac x="(ac,bc)" in image_eqI)
     apply clarsimp
    apply (clarsimp simp: ucast_ucast_mask_shift_helper[simplified vspace_bits_defs, simplified]
                          vspace_bits_defs)
   apply (clarsimp simp: vs_refs_pages_def graph_of_def)
   apply (rule_tac x="(ucast (p && mask pd_bits >> 3), x)" in image_eqI)
    apply (clarsimp simp: ucast_ucast_mask_shift_helper[simplified pde_bits_def])
   apply (clarsimp simp: vspace_bits_defs)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_caps_of_state parent_for_refs_def vspace_bits_defs)
   apply (drule same_refs_rD)
   apply (clarsimp split: list.splits)
   apply fastforce
  apply (drule same_refs_rD)
  apply clarsimp
  apply (drule spec, drule (2) mp[OF _ vs_lookup_vs_lookup_pagesI])
    apply ((clarsimp simp: invs_def valid_state_def valid_arch_state_def)+)[2]
  apply (rule_tac x=aa in exI, rule_tac x=ba in exI, rule_tac x=cap in exI)
  apply clarsimp
  done

lemma update_self_reachable:
  "\<lbrakk>(ref \<rhd> p) s; valid_asid_table (arm_asid_table (arch_state s)) s;
    valid_vspace_objs s\<rbrakk>
   \<Longrightarrow> (ref \<rhd> p) (s \<lparr>kheap := \<lambda>a. if a = p then Some y else kheap s a\<rparr>)"
  apply (erule (2) vs_lookupE_alt[OF _ _ valid_asid_table_ran])
    apply (rule vs_lookup_atI, clarsimp)
   apply (rule_tac ap=ap in vs_lookup_apI, auto simp: obj_at_def)[1]
  apply (clarsimp simp: pde_ref_def split: pde.splits)
  apply (rule_tac ap=ap and pd=pd in vs_lookup_pdI, auto simp: obj_at_def)[1]
  done

lemma update_self_reachable_pages:
  "\<lbrakk>(ref \<unrhd> p) s; valid_asid_table (arm_asid_table (arch_state s)) s;
    valid_vspace_objs s\<rbrakk>
   \<Longrightarrow> (ref \<unrhd> p) (s \<lparr>kheap := \<lambda>a. if a = p then Some y else kheap s a\<rparr>)"
  apply (erule (2) vs_lookup_pagesE_alt[OF _ _ valid_asid_table_ran])
     apply (rule vs_lookup_pages_atI, clarsimp)
    apply (rule_tac ap=ap in vs_lookup_pages_apI, auto simp: obj_at_def)[1]
   apply (rule_tac ap=ap and pd=pd in vs_lookup_pages_pdI,
          auto simp: obj_at_def pde_ref_pages_def data_at_def
              split: pde.splits)[1]
  apply (rule_tac ap=ap and pd=pd in vs_lookup_pages_ptI,
          auto simp: obj_at_def pde_ref_pages_def pte_ref_pages_def data_at_def
              split: pde.splits pte.splits)[1]
  done

lemma pd_slots_helper:
  "\<lbrakk>a \<in> set slots; b \<in> set slots;
    cte_wp_at (parent_for_refs (Inr (pde, slots))) cptr s\<rbrakk>
   \<Longrightarrow> a && ~~ mask pd_bits = b && ~~ mask pd_bits"
  apply (clarsimp simp add: cte_wp_at_def parent_for_refs_def)
  apply (drule imageI[where f="\<lambda>x. x && ~~ mask pd_bits"])
  apply (drule imageI[where f="\<lambda>x. x && ~~ mask pd_bits"])
  apply (simp add: obj_refs_def vspace_bits_defs)
  apply (rename_tac cap)
  apply (case_tac cap, simp+)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp+)
     apply (drule (1) set_rev_mp)
     apply (drule (1) set_rev_mp)
     apply force
    apply (drule (1) set_rev_mp)
    apply (drule (1) set_rev_mp)
    apply force
   apply (drule (1) set_rev_mp)
   apply (drule (1) set_rev_mp)
   apply force
  apply force
  done

(* FIXME: move *)
lemma simpler_store_pde_def:
  "store_pde p pde s =
    (case kheap s (p && ~~ mask pd_bits) of
          Some (ArchObj (PageDirectory pd)) =>
            ({((), s\<lparr>kheap := (kheap s)(p && ~~ mask pd_bits \<mapsto>
                                       (ArchObj (PageDirectory (pd(ucast (p && mask pd_bits >> 3) := pde)))))\<rparr>)}, False)
        | _ => ({}, True))"
  by (auto simp: store_pde_def simpler_set_pd_def get_object_def simpler_gets_def assert_def
                        return_def fail_def set_object_def get_def put_def bind_def get_pd_def vspace_bits_defs
                  split: Structures_A.kernel_object.splits option.splits arch_kernel_obj.splits if_split_asm)

lemma pde_update_valid_vspace_objs:
  "[|valid_vspace_objs s; valid_pde pde s; pde_ref pde = None;
    kheap s (p && ~~ mask pd_bits) = Some (ArchObj (PageDirectory pd))|]
   ==> valid_vspace_objs
         (s\<lparr>kheap := (kheap s)(p && ~~ mask pd_bits \<mapsto> ArchObj (PageDirectory (pd(ucast (p && mask pd_bits >> 3) := pde))))\<rparr>)"
  apply (cut_tac pde=pde and p=p in store_pde_arch_objs_unmap)
  apply (clarsimp simp: valid_def)
  apply (erule allE[where x=s])
  apply (clarsimp simp: split_def simpler_store_pde_def obj_at_def a_type_def vspace_bits_defs
                  split: if_split_asm option.splits Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
  done

lemma mapM_x_swp_store_pte_invs [wp]:
  "\<lbrace>invs and (\<lambda>s. (\<exists>p\<in>set slots. (\<exists>\<rhd> (p && ~~ mask pt_bits)) s) \<longrightarrow>
                  valid_pte pte s) and
    (\<lambda>s. wellformed_pte pte) and
    (\<lambda>s. \<exists>slot. cte_wp_at
           (\<lambda>c. image (\<lambda>x. x && ~~ mask pt_bits) (set slots) \<subseteq> obj_refs c \<and>
                is_pt_cap c \<and> (pte = InvalidPTE \<or>
                               cap_asid c \<noteq> None)) slot s) and
   (\<lambda>s. \<forall>p\<in>set slots. \<forall>ref. (ref \<rhd> (p && ~~ mask pt_bits)) s \<longrightarrow>
              (\<forall>q. pte_ref_pages pte = Some q \<longrightarrow>
                   (\<exists>p' cap.
                       caps_of_state s p' = Some cap \<and>
                       q \<in> obj_refs cap \<and>
                       vs_cap_ref cap =
                       Some
                        (VSRef (p && mask pt_bits >> 3) (Some APageTable) #
                         ref))))\<rbrace>
     mapM_x (swp store_pte pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM vspace_bits_defs | wp)+

lemma mapM_x_swp_store_pde_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>sl \<in> set slots. sl && ~~ mask pd_bits \<notin> global_refs s) and
    K (pde = InvalidPDE)\<rbrace>
  mapM_x (swp store_pde pde) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM vspace_bits_defs | wp mapM_swp_store_pde_invs_unmap)+

(* FIXME: move *)
lemma vs_cap_ref_table_cap_ref_None:
  "vs_cap_ref x = None \<Longrightarrow> table_cap_ref x = None"
  by (simp add: vs_cap_ref_def table_cap_ref_simps arch_cap_fun_lift_def
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemma master_cap_eq_is_pg_cap_eq:
  "cap_master_cap c = cap_master_cap d \<Longrightarrow> is_pg_cap c = is_pg_cap d"
  by (simp add: cap_master_cap_def is_pg_cap_def
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemma master_cap_eq_is_device_cap_eq:
  "cap_master_cap c = cap_master_cap d \<Longrightarrow> cap_is_device c = cap_is_device d"
  by (simp add: cap_master_cap_def
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemmas vs_cap_ref_eq_imp_table_cap_ref_eq' =
       vs_cap_ref_eq_imp_table_cap_ref_eq[OF master_cap_eq_is_pg_cap_eq]

lemma arch_update_cap_invs_map:
  "\<lbrace>cte_wp_at (is_arch_update cap and
               (\<lambda>c. \<forall>r. vs_cap_ref c = Some r \<longrightarrow> vs_cap_ref cap = Some r)) p
             and invs and valid_cap cap\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply (clarsimp simp: cte_wp_at_caps_of_state
              simp del: imp_disjL)
  apply (frule(1) valid_global_refsD2)
  apply (frule(1) cap_refs_in_kernel_windowD)
  apply (clarsimp simp: is_cap_simps is_arch_update_def
              simp del: imp_disjL)
  apply (frule master_cap_cap_range, simp del: imp_disjL)
  apply (thin_tac "cap_range a = cap_range b" for a b)
  apply (rule conjI)
   apply (fastforce simp:is_valid_vtable_root_def vs_cap_ref_def split:arch_cap.splits vmpage_size.splits option.splits)
  apply (rule conjI)
   apply (rule ext)
   apply (simp add: cap_master_cap_def split: cap.splits arch_cap.splits)
  apply (rule context_conjI)
   apply (simp add: appropriate_cte_cap_irqs)
   apply (clarsimp simp: cap_irqs_def cap_irq_opt_def cap_master_cap_def
                  split: cap.split)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def cap_master_cap_def
                  split: cap.split_asm)
  apply (rule conjI)
   apply (frule master_cap_obj_refs)
   apply simp
  apply (rule conjI)
   apply (frule master_cap_obj_refs)
   apply (case_tac "table_cap_ref capa =
                    table_cap_ref (ArchObjectCap a)")
    apply (frule unique_table_refs_no_cap_asidE[where S="{p}"])
     apply (simp add: valid_arch_caps_def)
    apply (simp add: no_cap_to_obj_with_diff_ref_def Ball_def)
   apply (case_tac "table_cap_ref capa")
    apply clarsimp
    apply (erule no_cap_to_obj_with_diff_ref_map,
           simp_all)[1]
      apply (clarsimp simp: table_cap_ref_def cap_master_cap_simps
                            is_cap_simps
                     split: cap.split_asm arch_cap.split_asm
                     dest!: cap_master_cap_eqDs)
     apply (simp add: valid_arch_caps_def)
    apply (simp add: valid_pspace_def)
   apply (erule swap)
   apply (erule vs_cap_ref_eq_imp_table_cap_ref_eq'[symmetric])
   apply (frule table_cap_ref_vs_cap_ref_Some)
   apply simp
  apply (rule conjI)
   apply (clarsimp simp del: imp_disjL)
   apply (erule disjE)
    apply (clarsimp simp: is_pt_cap_def cap_master_cap_simps
                          cap_asid_def vs_cap_ref_def
                   dest!: cap_master_cap_eqDs split: option.split_asm prod.split_asm)
    apply (drule valid_table_capsD[OF caps_of_state_cteD])
       apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
      apply (simp add: is_pt_cap_def)
     apply (simp add: cap_asid_def)
    apply simp
   apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                          cap_asid_def vs_cap_ref_def
                   dest!: cap_master_cap_eqDs split: option.split_asm prod.split_asm)
   apply (drule valid_table_capsD[OF caps_of_state_cteD])
      apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
     apply (simp add: is_cap_simps)
    apply (simp add: cap_asid_def)
   apply simp
  apply (clarsimp simp: is_cap_simps is_pt_cap_def cap_master_cap_simps
                        cap_asid_def vs_cap_ref_def ranI
                 dest!: cap_master_cap_eqDs split: option.split_asm if_split_asm
                 elim!: ranE cong: master_cap_eq_is_device_cap_eq
             | rule conjI)+
  apply (clarsimp dest!: master_cap_eq_is_device_cap_eq)
  done

    (* Want something like
       cte_wp_at (\<lambda>c. \<forall>p'\<in>obj_refs c. \<not>(vs_cap_ref c \<unrhd> p') s \<and> is_arch_update cap c) p
       So that we know the new cap isn't clobbering a cap with necessary mapping info.
       invs is fine here (I suspect) because we unmap the page BEFORE we replace the cap.
    *)

lemma arch_update_cap_invs_unmap_page:
  "\<lbrace>(\<lambda>s. cte_wp_at (\<lambda>c. (\<forall>p'\<in>obj_refs c. \<forall>ref. vs_cap_ref c = Some ref \<longrightarrow> \<not> (ref \<unrhd> p') s) \<and> is_arch_update cap c) p s)
             and invs and valid_cap cap
             and K (is_pg_cap cap)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                        is_cap_simps cap_master_cap_simps
                        fun_eq_iff appropriate_cte_cap_irqs
                        is_pt_cap_def is_valid_vtable_root_def
                 dest!: cap_master_cap_eqDs
              simp del: imp_disjL)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def)
  apply (rule conjI)
   apply (drule valid_global_refsD2, clarsimp)
   subgoal by (simp add: cap_range_def)
  apply (rule conjI[rotated])
   apply (frule(1) cap_refs_in_kernel_windowD)
   apply (simp add: cap_range_def)
  apply (drule unique_table_refs_no_cap_asidE[where S="{p}"])
   apply (simp add: valid_arch_caps_def)
  apply (simp add: no_cap_to_obj_with_diff_ref_def table_cap_ref_def Ball_def)
  done

lemma arch_update_cap_invs_unmap_page_table:
  "\<lbrace>cte_wp_at (is_arch_update cap) p
             and invs and valid_cap cap
             and (\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s)
             and obj_at (empty_table {}) (obj_ref_of cap)
             and (\<lambda>s. cte_wp_at (\<lambda>c. \<forall>r. vs_cap_ref c = Some r
                                \<longrightarrow> \<not> (r \<unrhd> obj_ref_of cap) s) p s)
             and K (is_pt_cap cap \<and> vs_cap_ref cap = None)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply (simp add: final_cap_at_eq)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                        is_cap_simps cap_master_cap_simps is_valid_vtable_root_def
                        appropriate_cte_cap_irqs is_pt_cap_def
                        fun_eq_iff[where f="cte_refs cap" for cap]
                 dest!: cap_master_cap_eqDs
              simp del: imp_disjL)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def)
  apply (rule conjI)
   apply (drule valid_global_refsD2, clarsimp)
   apply (simp add: cap_range_def)
  apply (frule(1) cap_refs_in_kernel_windowD)
  apply (simp add: cap_range_def gen_obj_refs_def image_def)
  apply (intro conjI)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: obj_at_def empty_table_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm
                          arch_kernel_obj.split_asm)
  apply fastforce+
  done

lemma set_vm_root_for_flush_invs:
  "\<lbrace>invs and K (asid \<le> mask asid_bits)\<rbrace>
  set_vm_root_for_flush pd asid \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: set_vm_root_for_flush_def)
  apply (wp hoare_drop_imps hoare_vcg_all_lift |wpc|simp)+
  done

lemma flush_table_invs[wp]:
  "\<lbrace>invs and K (asid \<le> mask asid_bits)\<rbrace>
  flush_table pd asid vptr pt \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: flush_table_def)
  apply (wp dmo_invalidateLocalTLB_ASID_invs | simp)+
  apply (simp only: if_cancel
            | clarsimp simp: machine_op_lift_def
                             machine_rest_lift_def split_def
            | wp set_vm_root_for_flush_invs)+
  done

crunch flush_table
  for vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_vcpu_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_vcpu_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update)

crunch vcpu_disable, vcpu_enable, vcpu_save, vcpu_restore
  for cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

(* this is again, weird *)
lemma vcpu_switch_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (cases vcpu; simp)
  apply (wp | wpc | clarsimp)+
  done

crunch flush_table
  for cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)


crunch vcpu_enable, vcpu_disable, vcpu_restore, vcpu_save
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps simp: crunch_simps global_refs_arch_update_eq)

lemma vcpu_switch_global_refs_inv[wp]:
  "\<lbrace>\<lambda>s. P (global_refs s)\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_ s. P (global_refs s)\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (cases vcpu; simp)
  apply (wp | wpc | rule modify_valid_lift | clarsimp simp: global_refs_def)+
  done

crunch flush_table
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps simp: crunch_simps global_refs_arch_update_eq)

lemma not_in_global_refs_vs_lookup:
  "(\<exists>\<rhd> p) s \<and> valid_vs_lookup s \<and> valid_global_refs s
            \<and> valid_arch_state s
            \<and> page_directory_at p s
        \<longrightarrow> p \<notin> global_refs s"
  apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])
  apply (drule(1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  apply blast
  done

lemma cleanByVA_PoU_underlying_memory[wp]:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace> cleanByVA_PoU w q \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: cleanByVA_PoU_def machine_op_lift_def machine_rest_lift_def split_def | wp)+

lemma unmap_page_table_invs[wp]:
  "\<lbrace>invs and K (asid \<le> mask asid_bits \<and> vaddr < kernel_base
                     \<and> vmsz_aligned vaddr ARMSection)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (rule hoare_pre)
   apply (wp dmo_invs | wpc | simp)+
      apply (rule_tac Q'="\<lambda>_. invs and K (asid \<le> mask asid_bits)" in hoare_post_imp)
       apply safe
        apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p =
                                   underlying_memory m p" in use_valid)
          apply ((wp | simp)+)[3]
       apply(erule use_valid, wp no_irq_cleanByVA_PoU no_irq, assumption)
   apply (wp store_pde_invs_unmap page_table_mapped_wp | wpc | simp)+
  apply (simp add: lookup_pd_slot_pd pde_ref_def)
  apply (strengthen not_in_global_refs_vs_lookup)
  apply (auto simp: vspace_at_asid_def)
  done

lemma final_cap_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (is_final_cap' cap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (is_final_cap' cap s)\<rbrace>"
  by (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state, rule x)

lemmas dmo_final_cap[wp] = final_cap_lift [OF do_machine_op_caps_of_state]
lemmas store_pte_final_cap[wp] = final_cap_lift [OF store_pte_caps_of_state]
lemmas unmap_page_table_final_cap[wp] = final_cap_lift [OF unmap_page_table_caps_of_state]

lemma mapM_x_swp_store_empty_table':
  "\<lbrace>obj_at (\<lambda>ko. \<exists>pt. ko = ArchObj (PageTable pt)
                 \<and> (\<forall>x. x \<in> (\<lambda>sl. ucast ((sl && mask pt_bits) >> 3)) ` set slots
                           \<or> pt x = InvalidPTE)) p
         and K (is_aligned p pt_bits \<and> (\<forall>x \<in> set slots. x && ~~ mask pt_bits = p))\<rbrace>
      mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (induct slots, simp_all add: mapM_x_Nil mapM_x_Cons)
   apply wp
   apply (clarsimp simp: obj_at_def empty_table_def fun_eq_iff)
  apply (rule bind_wp, assumption)
  apply (thin_tac "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q)
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def vspace_bits_defs)
  apply auto
  done

lemma mapM_x_swp_store_empty_table:
  "\<lbrace>page_table_at p and pspace_aligned
       and K ((UNIV :: (9 word) set) \<subseteq> (\<lambda>sl. ucast ((sl && mask pt_bits) >> 3)) ` set slots
                       \<and> (\<forall>x\<in>set slots. x && ~~ mask pt_bits = p))\<rbrace>
     mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (wp mapM_x_swp_store_empty_table')
  apply (clarsimp simp: obj_at_def a_type_def )
  apply (clarsimp split: Structures_A.kernel_object.split_asm
                         arch_kernel_obj.split_asm if_split_asm)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp: vspace_bits_defs)
  apply blast
  done

lemma pd_shifting_again:
  "\<lbrakk> is_aligned pd pd_bits \<rbrakk>
    \<Longrightarrow> pd + (ucast (ae :: 11 word) << 3) && ~~ mask pd_bits = pd"
  apply (erule add_mask_lower_bits)
  apply (clarsimp simp add: nth_shiftl nth_ucast word_size
                            vspace_bits_defs
                     dest!: test_bit_size)
  apply arith
done

lemma ucast_less_shiftl3_helper:
  "\<lbrakk> len_of TYPE('b) + 3 < len_of TYPE('a); 2 ^ (len_of TYPE('b) + 3) \<le> n\<rbrakk>
    \<Longrightarrow> (ucast (x :: 'b::len word) << 3) < (n :: 'a::len word)"
  apply (erule order_less_le_trans[rotated])
  using ucast_less[where x=x and 'a='a]
  apply (simp only: shiftl_t2n field_simps)
  apply (rule word_less_power_trans2; simp)
  done

lemma pd_shifting_again2:
  "is_aligned (pd::word32) pd_bits \<Longrightarrow>
   pd + (ucast (ae::11 word) << 3) && mask pd_bits = (ucast ae << 3)"
  apply (rule conjunct1, erule is_aligned_add_helper)
  apply (simp add: vspace_bits_defs)
  apply (rule ucast_less_shiftl3_helper)
   apply (simp add: word_bits_def)+
done

(* FIXME: move near Invariants_A.vs_lookup_2ConsD *)
lemma vs_lookup_pages_2ConsD:
  "((v # v' # vs) \<unrhd> p) s \<Longrightarrow>
   \<exists>p'. ((v' # vs) \<unrhd> p') s \<and> ((v' # vs, p') \<unrhd>1 (v # v' # vs, p)) s"
  apply (clarsimp simp: vs_lookup_pages_def)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def)
  apply (fastforce simp: vs_lookup_pages1_def)
  done

(* FIXME: move to Invariants_A *)
lemma vs_lookup_pages_eq_at:
  "[VSRef a None] \<rhd> pd = [VSRef a None] \<unrhd> pd"
  apply (simp add: vs_lookup_pages_def vs_lookup_def Image_def)
  apply (rule ext)
  apply (rule iffI)
   apply (erule bexEI)
   apply (erule rtranclE, simp)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def
                  dest!: vs_lookup1D
                  split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
  apply (erule bexEI)
  apply (erule rtranclE, simp)
  apply (clarsimp simp: vs_refs_pages_def graph_of_def image_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  done

(* FIXME: move to Invariants_A *)
lemma vs_lookup_pages_eq_ap:
  "[VSRef b (Some AASIDPool), VSRef a None] \<rhd> pd =
   [VSRef b (Some AASIDPool), VSRef a None] \<unrhd> pd"
  apply (simp add: vs_lookup_pages_def vs_lookup_def Image_def)
  apply (rule ext)
  apply (rule iffI)
   apply (erule bexEI)
   apply (erule rtranclE, simp)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def
                  dest!: vs_lookup1D
                  split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
   apply (erule rtranclE)
    apply (clarsimp simp: vs_asid_refs_def graph_of_def image_def)
    apply (rule converse_rtrancl_into_rtrancl[OF _ rtrancl_refl])
    apply (fastforce simp: vs_refs_pages_def graph_of_def image_def
                          vs_lookup_pages1_def)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def
                  dest!: vs_lookup1D
                  split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
  apply (erule bexEI)
  apply (erule rtranclE, simp)
  apply (clarsimp simp: vs_refs_pages_def graph_of_def image_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def image_def)
   apply (rule converse_rtrancl_into_rtrancl[OF _ rtrancl_refl])
   apply (fastforce simp: vs_refs_def graph_of_def image_def
                         vs_lookup1_def)
  apply (clarsimp simp: vs_refs_pages_def graph_of_def image_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  done

lemma store_pde_unmap_pt:
  "\<lbrace>[VSRef (asid && mask asid_low_bits) (Some AASIDPool),
            VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd
        and K (is_aligned pd pd_bits)\<rbrace>
     store_pde (pd + (vaddr >> 21 << 3)) InvalidPDE
   \<lbrace>\<lambda>rv s.
        \<not> ([VSRef (vaddr >> 21) (Some APageDirectory),
            VSRef (asid && mask asid_low_bits) (Some AASIDPool),
            VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pt) s\<rbrace>"
  apply (simp add: store_pde_def)
  apply wp
   apply (simp add: set_pd_def set_object_def)
   apply (wp get_object_wp)+
  apply (clarsimp simp: obj_at_def fun_upd_def[symmetric])
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def
                 dest!: graph_ofD
                 split: if_split_asm
                        Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
    apply (simp add: pde_ref_def)
   apply (simp_all add: pd_shifting_again pd_shifting_again2 pde_bits_def
                        pd_casting_shifting word_size)
  apply (simp add: up_ucast_inj_eq)
done

lemma vs_lookup_pages1_rtrancl_iterations:
  "(tup, tup') \<in> (vs_lookup_pages1 s)\<^sup>*
    \<Longrightarrow> (length (fst tup) \<le> length (fst tup')) \<and>
       (tup, tup') \<in> ((vs_lookup_pages1 s)
           ^^ (length (fst tup') - length (fst tup)))"
  apply (erule rtrancl_induct)
   apply simp
  apply (elim conjE)
  apply (subgoal_tac "length (fst z) = Suc (length (fst y))")
   apply (simp add: Suc_diff_le)
   apply (erule(1) relcompI)
  apply (clarsimp simp: vs_lookup_pages1_def)
  done

(* FIXME move to VSpacePre *)
lemma pd_casting_shifting3:
  "size x + 3 < len_of TYPE('a) \<Longrightarrow>
     ucast (ucast x << 3 >> 3 :: ('a :: len) word) = x"
  apply (rule word_eqI)
  apply (simp add: nth_ucast nth_shiftr nth_shiftl word_size)
  done


lemma store_pde_unmap_page:
  "\<lbrace>[VSRef (asid && mask asid_low_bits) (Some AASIDPool),
            VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd
        and K (is_aligned pd pd_bits)\<rbrace>
     store_pde (pd + (vaddr >> 21 << 3)) InvalidPDE
   \<lbrace>\<lambda>rv s.
        \<not> ([VSRef (vaddr >> 21) (Some APageDirectory),
            VSRef (asid && mask asid_low_bits) (Some AASIDPool),
            VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pde) s\<rbrace>"
  apply (simp add: store_pde_def vs_lookup_pages_eq_ap)
  apply wp
   apply (simp add: set_pd_def set_object_def)
   apply (wp get_object_wp)+
  apply (clarsimp simp: obj_at_def fun_upd_def[symmetric])
  apply (clarsimp simp: vs_lookup_pages_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup_pages1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                 dest!: graph_ofD
                 split: if_split_asm
                        Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
    apply (simp add: pde_ref_pages_def)
   apply (simp_all add: pd_shifting_again pd_shifting_again2)
   apply (simp_all add: pd_casting_shifting3 word_size vspace_bits_defs)
  apply (simp add: up_ucast_inj_eq)
done

lemma store_pte_no_lookup_pages:
  "\<lbrace>\<lambda>s. \<not> (r \<unrhd> q) s\<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_ s. \<not> (r \<unrhd> q) s\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule swap, simp)
  apply (erule vs_lookup_pages_induct)
   apply (simp add: vs_lookup_pages_atI)
  apply (thin_tac "(ref \<unrhd> p) (kheap_update f s)" for ref p f)
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                     graph_of_def image_def
              split: if_split_asm)


lemma store_pde_no_lookup_pages:
  "\<lbrace>\<lambda>s. \<not> (r \<unrhd> q) s\<rbrace> store_pde p InvalidPDE \<lbrace>\<lambda>_ s. \<not> (r \<unrhd> q) s\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule swap, simp)
  apply (erule vs_lookup_pages_induct)
   apply (simp add: vs_lookup_pages_atI)
  apply (thin_tac "(ref \<unrhd> p) (kheap_update f s)" for ref p f)
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                     graph_of_def image_def
              split: if_split_asm)

lemma flush_table_vs_lookup_pages[wp]:
  "\<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>
   flush_table a b c d
   \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  by (simp add: flush_table_def | wp mapM_UNIV_wp hoare_drop_imps | wpc
     | intro conjI impI)+

crunch page_table_mapped
  for vs_lookup_pages[wp]: "\<lambda>s. P (vs_lookup_pages s)"

lemma unmap_page_table_unmapped[wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (vaddr >> 21) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pt) s\<rbrace>"
  apply (simp add: unmap_page_table_def lookup_pd_slot_def Let_def
             cong: option.case_cong)
  apply (rule hoare_pre)
   apply ((wp store_pde_unmap_pt page_table_mapped_wp | wpc | simp add: vspace_bits_defs)+)[1]
  apply (clarsimp simp: vspace_at_asid_def pd_aligned vspace_bits_defs)
  done

lemma unmap_page_table_unmapped2:
  "\<lbrace>pspace_aligned and valid_vspace_objs and
      K (ref = [VSRef (vaddr >> 21) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None]
           \<and> p = pt)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv s. \<not> (ref \<rhd> p) s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply simp
  apply wp
  done

lemma cacheRangeOp_lift[wp]:
  assumes o: "\<And>a b. \<lbrace>P\<rbrace> oper a b \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> cacheRangeOp oper x y z \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding cacheRangeOp_def
  by (wpsimp wp: mapM_x_wp_inv o)

lemma cleanCacheRange_PoU_underlying_memory[wp]:
  "cleanCacheRange_PoU a b c \<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: cleanCacheRange_PoU_def, wp)

lemma unmap_page_table_unmapped3:
  "\<lbrace>pspace_aligned and valid_vspace_objs and page_table_at pt and
      K (ref = [VSRef (vaddr >> 21) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None]
           \<and> p = pt)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv s. \<not> (ref \<unrhd> p) s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_page_table_def lookup_pd_slot_def Let_def
             cong: option.case_cong)
  apply (rule hoare_pre)
   apply ((wp store_pde_unmap_page | wpc | simp add: vspace_bits_defs)+)[1]
   apply (rule page_table_mapped_wp)
  apply (clarsimp simp: vspace_at_asid_def pd_aligned pd_bits_def pageBits_def)
  apply (drule vs_lookup_pages_2ConsD)
  apply (clarsimp simp: obj_at_def vs_refs_pages_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (drule vs_lookup_pages_eq_ap[THEN fun_cong, symmetric, THEN iffD1])
  apply (erule swap)
  apply (drule (1) valid_vspace_objsD[rotated 2])
   apply (simp add: obj_at_def)
  apply (erule vs_lookup_step)
  apply (clarsimp simp: obj_at_def vs_refs_def vs_lookup1_def
                        graph_of_def image_def
                 split: if_split_asm)
  apply (drule_tac x=a in spec)
  apply (auto simp: vspace_bits_defs obj_at_def valid_pde_def pde_ref_def pde_ref_pages_def data_at_def
                 split: pde.splits)
  done

lemma is_final_cap_caps_of_state_2D:
  "\<lbrakk> caps_of_state s p = Some cap; caps_of_state s p' = Some cap';
     is_final_cap' cap'' s; gen_obj_refs cap \<inter> gen_obj_refs cap'' \<noteq> {};
     gen_obj_refs cap' \<inter> gen_obj_refs cap'' \<noteq> {} \<rbrakk>
       \<Longrightarrow> p = p'"
  apply (clarsimp simp: is_final_cap'_def3)
  apply (frule_tac x="fst p" in spec)
  apply (drule_tac x="snd p" in spec)
  apply (drule_tac x="fst p'" in spec)
  apply (drule_tac x="snd p'" in spec)
  apply (clarsimp simp: cte_wp_at_caps_of_state Int_commute
                        prod_eqI)
  done

(* FIXME: move *)
lemma empty_table_pt_capI:
  "\<lbrakk>caps_of_state s p =
    Some (cap.ArchObjectCap (arch_cap.PageTableCap pt None));
    valid_table_caps s\<rbrakk>
   \<Longrightarrow> obj_at (empty_table {}) pt s"
    apply (case_tac p)
    apply (clarsimp simp: valid_table_caps_def simp del: imp_disjL)
    apply (drule spec)+
    apply (erule impE, simp add: is_cap_simps)+
    by assumption

crunch cleanCacheRange_PoC, cleanL2Range, invalidateL2Range, invalidateByVA,
                              cleanInvalidateL2Range, cleanInvalByVA, invalidateCacheRange_I,
                              branchFlushRange, ackInterrupt
  for underlying_memory[wp]: "\<lambda>m'. underlying_memory m' p = um"
  (simp: cache_machine_op_defs)

crunch cleanCacheRange_RAM, invalidateCacheRange_RAM,
                              cleanInvalidateCacheRange_RAM, do_flush
  for underlying_memory[wp]: "\<lambda>m'. underlying_memory m' p = um"
  (simp: crunch_simps)


lemma no_irq_do_flush:
  "no_irq (do_flush a b c d)"
  apply (simp add: do_flush_def)
  apply (case_tac a)
  apply (wpsimp wp: no_irq_dsb no_irq_invalidateCacheRange_I no_irq_branchFlushRange no_irq_isb
                simp: Let_def)+
  done


lemma cleanCacheRange_PoU_respects_device_region[wp]:
  "\<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> cleanCacheRange_PoU a b c \<lbrace>\<lambda>_ ms. P (device_state ms)\<rbrace>"
  including no_pre
  apply (wpsimp wp: mapM_x_wp  simp: cleanCacheRange_PoU_def cacheRangeOp_def)+
  apply fastforce
  done

lemma cacheRangeOp_respects_device_region[wp]:
  assumes valid_f: "\<And>a b P. \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> f a b \<lbrace>\<lambda>_ ms. P (device_state ms)\<rbrace>"
  shows "\<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> cacheRangeOp f a b c\<lbrace>\<lambda>_ ms. P (device_state ms)\<rbrace>"
  by (wpsimp simp: do_flush_def cacheRangeOp_def wp: mapM_x_wp valid_f)+

crunch cleanByVA, cleanCacheRange_PoC, cleanCacheRange_RAM,
  cleanInvalByVA, invalidateByVA, invalidateL2Range,
  invalidateCacheRange_RAM, branchFlush, branchFlushRange,
  invalidateByVA_I, cleanInvalidateL2Range, do_flush, storeWord
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
  (simp: crunch_simps
   ignore_del: cleanByVA cleanInvalByVA invalidateByVA invalidateL2Range
               branchFlush invalidateByVA_I cleanInvalidateL2Range storeWord)

lemma dmo_maskInterrupt_pspace_respects_device_region[wp]:
  "do_machine_op (maskInterrupt b irq) \<lbrace>pspace_respects_device_region\<rbrace>"
  unfolding maskInterrupt_def
  by (wpsimp wp: pspace_respects_device_region_dmo)

crunch vcpu_enable, vcpu_write_reg, vcpu_update, vcpu_restore, vcpu_enable, vcpu_disable
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  (wp: crunch_wps dmo_maskInterrupt_pspace_respects_device_region
       pspace_respects_device_region_dmo
   simp: crunch_simps set_cntv_off_64_def read_cntpct_def get_cntv_off_64_def get_cntv_cval_64_def
         set_cntv_cval_64_def)

crunch perform_page_invocation
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  (simp: crunch_simps when_def
     wp: crunch_wps set_object_pspace_respects_device_region pspace_respects_device_region_dmo)

crunch do_machine_op
  for cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  (simp: valid_kernel_mappings_def)

lemma dmo_invs_lift:
  assumes dev: "\<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  assumes mem: "\<And>P. f \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  assumes irq: "\<And>P. f \<lbrace>\<lambda>ms. P (irq_masks ms)\<rbrace>"
  shows "do_machine_op f \<lbrace>invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def valid_irq_states_def valid_machine_state_def
  by (wpsimp wp: dev hoare_vcg_all_lift hoare_vcg_disj_lift
                 dmo_inv_prop_lift[where g=underlying_memory, OF mem]
                 pspace_respects_device_region_dmo
                 cap_refs_respects_device_region_dmo
     | wps dmo_inv_prop_lift[where g=irq_masks, OF irq])+

crunch do_flush
  for underlying_memory_inv[wp]: "\<lambda>ms. P (underlying_memory ms)"
  and irq_masks[wp]: "\<lambda>ms. P (irq_masks ms)"
  (simp: cleanByVA_def cleanByVA_PoU_def invalidateByVA_I_def cleanInvalByVA_def
         cleanInvalidateL2Range_def cleanL2Range_def invalidateByVA_def invalidateL2Range_def
         branchFlush_def isb_def dsb_def
         crunch_simps
   wp: no_irq)

lemma perform_page_directory_invocation_invs[wp]:
  "\<lbrace>invs and valid_pdi pdi\<rbrace>
     perform_page_directory_invocation pdi
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (cases pdi)
   apply (clarsimp simp: perform_page_directory_invocation_def)
   apply (wpsimp wp: dmo_invs_lift set_vm_root_for_flush_invs simp: valid_pdi_def)
  apply (clarsimp simp: perform_page_directory_invocation_def)
  apply wpsimp
  done

lemma perform_page_table_invocation_invs[wp]:
  notes no_irq[wp]
  shows
  "\<lbrace>invs and valid_pti pti\<rbrace>
   perform_page_table_invocation pti
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (cases pti)
   apply (clarsimp simp: valid_pti_def perform_page_table_invocation_def)
   apply (wp dmo_invs)
    apply (rule_tac Q'="\<lambda>_. invs" in hoare_post_imp)
     apply safe
     apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p =
                                underlying_memory m p" in use_valid)
       apply ((clarsimp simp: machine_op_lift_def
                             machine_rest_lift_def split_def | wp)+)[3]
     apply(erule use_valid, wp no_irq_cleanByVA_PoU no_irq, assumption)
    apply (wp store_pde_map_invs)[1]
   apply simp
   apply (wp arch_update_cap_invs_map arch_update_cap_pspace
             arch_update_cap_valid_mdb set_cap_idle update_cap_ifunsafe
             valid_irq_node_typ valid_pde_lift set_cap_typ_at
             set_cap_irq_handlers set_cap_empty_pde
             hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift
             set_cap_arch_obj set_cap_obj_at_impossible set_cap_valid_arch_caps)+
    apply (simp; intro conjI; clarsimp simp: cte_wp_at_caps_of_state kernel_vsrefs_def)
     apply (clarsimp simp: is_pt_cap_def is_arch_update_def cap_master_cap_def
                           vs_cap_ref_simps
                    split: cap.splits arch_cap.splits option.splits)
    apply fastforce
   apply (rule exI, rule conjI, assumption)
   apply (clarsimp simp: is_pt_cap_def is_arch_update_def
                         cap_master_cap_def cap_asid_def vs_cap_ref_simps
                         is_arch_cap_def pde_ref_def pde_ref_pages_def
                  split: cap.splits arch_cap.splits option.splits
                         pde.splits)
   apply (intro allI impI conjI)
    apply (clarsimp simp: pde_bits_def)
    apply fastforce
   apply (clarsimp simp: caps_of_def cap_of_def)
   apply (frule invs_pd_caps)
   apply (drule (1) empty_table_pt_capI)
   apply (clarsimp simp: obj_at_def empty_table_def pte_ref_pages_def)
  apply (clarsimp simp: perform_page_table_invocation_def
                 split: cap.split arch_cap.split)
  apply (rename_tac word option)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_invs_unmap_page_table get_cap_wp)
   apply (simp add: cte_wp_at_caps_of_state)
   apply (wpc, wp, wpc)
   apply (rule hoare_lift_Pf2[where f=caps_of_state])
    apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift dmo_invs_lift
              valid_cap_typ[OF do_machine_op_obj_at]
              mapM_x_swp_store_pte_invs[unfolded cte_wp_at_caps_of_state]
              mapM_x_swp_store_empty_table
              valid_cap_typ[OF unmap_page_table_typ_at]
              unmap_page_table_unmapped3 store_pte_no_lookup_pages
           | wp (once) hoare_vcg_conj_lift
           | wp (once) mapM_x_wp'
           | simp)+
  apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state is_cap_simps
                        is_arch_update_def cap_rights_update_def
                        acap_rights_update_def cap_master_cap_simps
                        update_map_data_def)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
   apply (drule invs_pd_caps)
   apply (simp add: valid_table_caps_def)
   apply (elim allE, drule(1) mp)
   apply (simp add: is_cap_simps cap_asid_def)
   apply (drule mp, rule refl)
   apply (clarsimp simp: obj_at_def valid_cap_def empty_table_def
                         a_type_def)
  apply (clarsimp simp: valid_cap_def mask_def[where n=asid_bits]
                        vmsz_aligned_def cap_aligned_def vs_cap_ref_def
                        invs_psp_aligned invs_vspace_objs)
  apply (subgoal_tac "(\<forall>x\<in>set [word , word + 8 .e. word + 2 ^ pt_bits - 1].
                             x && ~~ mask pt_bits = word)")
   apply (intro conjI)
     apply (fastforce simp: vspace_bits_defs)
    apply (clarsimp simp: image_def vspace_bits_defs)
    apply (subgoal_tac "word + (ucast x << 3)
                   \<in> set [word, word + 8 .e. word + 2 ^ pt_bits - 1]")
     apply (simp add: vspace_bits_defs)
     apply (rule rev_bexI, assumption)
     apply (rule ccontr, erule more_pt_inner_beauty[simplified vspace_bits_defs, simplified])
     apply simp
    apply (clarsimp simp: upto_enum_step_def linorder_not_less)
    apply (subst is_aligned_no_overflow,
           erule is_aligned_weaken,
           (simp_all add: vspace_bits_defs)[2])+
    apply (clarsimp simp: image_def word_shift_by_3)
    apply (rule exI, rule conjI[OF _ refl])
    apply (rule plus_one_helper)
    apply (rule order_less_le_trans, rule ucast_less, (simp add: vspace_bits_defs)+)
  apply (clarsimp simp: upto_enum_step_def)
  apply (rule conjunct2, rule is_aligned_add_helper)
   apply (simp add: vspace_bits_defs)
  apply (simp only: word_shift_by_3)
  apply (rule shiftl_less_t2n)
   apply (rule word_leq_minus_one_le)
    apply (simp add: vspace_bits_defs)+
  done

crunch unmap_page
  for cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch unmap_page
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas unmap_page_typ_ats [wp] = abs_typ_at_lifts [OF unmap_page_typ_at]

lemma invalidateLocalTLB_VAASID_underlying_memory[wp]:
  "invalidateLocalTLB_VAASID v \<lbrace>\<lambda>ms. P (underlying_memory ms)\<rbrace>"
  by (wpsimp simp: invalidateLocalTLB_VAASID_def)

lemma flush_page_invs:
  "\<lbrace>invs and K (asid \<le> mask asid_bits)\<rbrace>
  flush_page sz pd asid vptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding flush_page_def
  by (wpsimp wp: dmo_invs_lift no_irq no_irq_invalidateLocalTLB_VAASID set_vm_root_for_flush_invs)

lemma find_pd_for_asid_lookup_slot [wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace> find_pd_for_asid asid
  \<lbrace>\<lambda>rv. \<exists>\<rhd> (lookup_pd_slot rv vptr && ~~ mask pd_bits)\<rbrace>, -"
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_postE_R)
    apply (rule hoare_vcg_conj_liftE_R)
     apply (rule find_pd_for_asid_lookup)
    apply (rule find_pd_for_asid_aligned_pd)
   apply (simp add: pd_shifting lookup_pd_slot_def Let_def)
  apply simp
  done

lemma find_pd_for_asid_lookup_slot_large_page [wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and K (x \<in> set [0, 8 .e. 0x78] \<and> is_aligned vptr 25)\<rbrace>
  find_pd_for_asid asid
  \<lbrace>\<lambda>rv. \<exists>\<rhd> (x + lookup_pd_slot rv vptr && ~~ mask pd_bits)\<rbrace>, -"
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_postE_R)
    apply (rule hoare_vcg_conj_liftE_R)
      apply (rule hoare_vcg_conj_liftE_R)
       apply (rule find_pd_for_asid_inv [where P="K (x \<in> set [0, 8 .e. 0x78] \<and> is_aligned vptr 25)", THEN valid_validE_R])
     apply (rule find_pd_for_asid_lookup)
    apply (rule find_pd_for_asid_aligned_pd)
   apply (subst lookup_pd_slot_add_eq)
      apply (simp_all add: vspace_bits_defs)
  done

lemma find_pd_for_asid_pde_at_add [wp]:
 "\<lbrace>K (x \<in> set [0,8 .e. 0x78] \<and> is_aligned vptr 25) and pspace_aligned and valid_vspace_objs\<rbrace>
  find_pd_for_asid asid \<lbrace>\<lambda>rv. pde_at (x + lookup_pd_slot rv vptr)\<rbrace>, -"
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_postE_R)
    apply (rule hoare_vcg_conj_liftE_R)
     apply (rule find_pd_for_asid_inv [where P=
                 "K (x \<in> set [0, 8 .e. 0x78] \<and> is_aligned vptr 25) and pspace_aligned", THEN valid_validE_R])
    apply (rule find_pd_for_asid_page_directory)
   apply (auto intro!: pde_at_aligned_vptr)
  done

lemma lookup_pt_slot_cap_to:
  shows "\<lbrace>invs and \<exists>\<rhd>pd and K (is_aligned pd pd_bits)
                  and K (vptr < kernel_base)\<rbrace> lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> is_pt_cap cap
                                \<and> rv && ~~ mask pt_bits \<in> obj_refs cap
                                \<and>  s \<turnstile> cap \<and> cap_asid cap \<noteq> None
                                \<and> (is_aligned vptr 16 \<longrightarrow> is_aligned rv 7)\<rbrace>, -"
  proof -
    have shift: "(2::word32) ^ pt_bits = 2 ^ 9 << 3"
      by (simp add: vspace_bits_defs)
  show ?thesis
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp | wpc)+
  apply (clarsimp simp: lookup_pd_slot_pd)
  apply (frule(1) valid_vspace_objsD)
   apply fastforce
  apply (drule vs_lookup_step)
   apply (erule vs_lookup1I[OF _ _ refl])
   apply (simp add: vs_refs_def image_def)
   apply (rule rev_bexI)
    apply (erule pde_graph_ofI)
    apply (simp add: pde_ref_def)
   apply fastforce
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply simp
  apply (elim exEI, clarsimp)
  apply (subst is_aligned_add_helper[THEN conjunct2])
    apply (drule caps_of_state_valid)
     apply fastforce
    apply (clarsimp dest!:valid_cap_aligned simp:cap_aligned_def vs_cap_ref_def
      obj_refs_def obj_ref_of_def pageBitsForSize_def vspace_bits_defs
      elim!:is_aligned_weaken
      split:arch_cap.split_asm cap.splits option.split_asm vmpage_size.split_asm)
   apply (simp add: vspace_bits_defs mask_2pm1)
   apply (rule less_le_trans[OF shiftl_less_t2n[where m = 12]])
     apply (rule le_less_trans[OF word_and_le1])
     apply (simp add: vspace_bits_defs)
    apply simp
   apply (simp add:vspace_bits_defs)

  apply (drule caps_of_state_valid)
   apply fastforce
  apply (drule_tac x="ucast (lookup_pd_slot pd vptr && mask pd_bits >> pde_bits)" in spec)
  apply (clarsimp simp: valid_pde_def obj_at_def vspace_bits_defs
                        vs_cap_ref_def is_pt_cap_def valid_cap_simps cap_aligned_def
                 split: cap.split_asm arch_cap.split_asm vmpage_size.splits
                        option.split_asm if_splits)
    apply (erule is_aligned_add[OF is_aligned_weaken],simp
      ,rule is_aligned_shiftl[OF is_aligned_andI1,OF is_aligned_shiftr],simp)+
  done
qed

lemma lookup_pt_slot_cap_to1[wp]:
  "\<lbrace>invs and \<exists>\<rhd>pd and K (is_aligned pd pd_bits)
                  and K (vptr < kernel_base)\<rbrace> lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> is_pt_cap cap \<and> rv && ~~ mask pt_bits \<in> obj_refs cap\<rbrace>,-"
  apply (rule hoare_strengthen_postE_R)
   apply (rule lookup_pt_slot_cap_to)
  apply auto
  done

lemma lookup_pt_slot_cap_to_multiple1:
  "\<lbrace>invs and \<exists>\<rhd>pd and K (is_aligned pd pd_bits)
                  and K (vptr < kernel_base)
                  and K (is_aligned vptr 16)\<rbrace>
     lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s. is_aligned rv 7 \<and>
             (\<exists>a b. cte_wp_at (\<lambda>c. is_pt_cap c \<and> cap_asid c \<noteq> None
                                  \<and> (\<lambda>x. x && ~~ mask pt_bits) ` set [rv , rv + 8 .e. rv + 0x78] \<subseteq> obj_refs c) (a, b) s)\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (rule hoare_strengthen_postE_R)
   apply (rule lookup_pt_slot_cap_to)
  apply (rule conjI, clarsimp)
  apply (elim exEI)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_pt_cap_def
                        valid_cap_def cap_aligned_def
                   del: subsetI)
  apply (simp add: subset_eq p_0x3C_shift[simplified add.commute])
  apply (clarsimp simp: set_upto_enum_step_8)
  apply (fold mask_def[where n=4, simplified])
  apply (subst(asm) le_mask_iff)
  apply (subst word_plus_and_or_coroll)
   apply (rule shiftr_eqD[where n=7])
     apply (simp add: shiftr_over_and_dist shiftl_shiftr2)
    apply (simp add: is_aligned_andI2)
   apply simp
  apply (simp add: word_ao_dist)
  apply (simp add: and_not_mask vspace_bits_defs)
  apply (drule arg_cong[where f="\<lambda>x. x >> 5"])
  apply (simp add: shiftl_shiftr2 shiftr_shiftr)
  done

lemma lookup_pt_slot_cap_to_multiple[wp]:
  "\<lbrace>invs and \<exists>\<rhd>pd and K (is_aligned pd pd_bits)
                  and K (vptr < kernel_base)
                  and K (is_aligned vptr 16)\<rbrace>
     lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s. \<exists>a b. cte_wp_at (\<lambda>c. (\<lambda>x. x && ~~ mask pt_bits) ` (\<lambda>x. x + rv) ` set [0 , 8 .e. 0x78] \<subseteq> obj_refs c) (a, b) s\<rbrace>, -"
  apply (rule hoare_strengthen_postE_R, rule lookup_pt_slot_cap_to_multiple1)
  apply (elim conjE exEI cte_wp_at_weakenE)
  apply (simp add: subset_eq p_0x3C_shift add.commute)
  done

lemma find_pd_for_asid_cap_to:
  "\<lbrace>invs\<rbrace> find_pd_for_asid asid
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> rv \<in> obj_refs cap
                                \<and> is_pd_cap cap \<and> s \<turnstile> cap
                                \<and> is_aligned rv pd_bits\<rbrace>, -"
  apply (simp add: find_pd_for_asid_def assertE_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply clarsimp
  apply (drule vs_lookup_atI)
  apply (frule(1) valid_vspace_objsD, clarsimp)
  apply (drule vs_lookup_step)
   apply (erule vs_lookup1I [OF _ _ refl])
   apply (simp add: vs_refs_def image_def)
   apply (rule rev_bexI)
    apply (erule graph_ofI)
   apply fastforce
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply (simp, elim exEI)
  apply clarsimp
  apply (frule caps_of_state_valid_cap, clarsimp+)
  apply (clarsimp simp: table_cap_ref_ap_eq[symmetric] table_cap_ref_def
                        is_pd_cap_def valid_cap_def cap_aligned_def
                        pd_bits_def pageBits_def
                 split: cap.split_asm arch_cap.split_asm option.split_asm)
  done

lemma find_pd_for_asid_cap_to1[wp]:
  "\<lbrace>invs\<rbrace> find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> lookup_pd_slot rv vptr && ~~ mask pd_bits \<in> obj_refs cap\<rbrace>, -"
  apply (rule hoare_strengthen_postE_R, rule find_pd_for_asid_cap_to)
  apply (clarsimp simp: lookup_pd_slot_pd)
  apply auto
  done

lemma find_pd_for_asid_cap_to2[wp]:
  "\<lbrace>invs\<rbrace> find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. \<exists>a b. cte_wp_at
            (\<lambda>cp. lookup_pd_slot rv vptr && ~~ mask pd_bits \<in> obj_refs cp \<and> is_pd_cap cp)
                  (a, b) s\<rbrace>, -"
  apply (rule hoare_strengthen_postE_R, rule find_pd_for_asid_cap_to)
  apply (clarsimp simp: lookup_pd_slot_pd cte_wp_at_caps_of_state)
  apply auto
  done

lemma find_pd_for_asid_cap_to_multiple[wp]:
  "\<lbrace>invs and K (is_aligned vptr 25)\<rbrace> find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. \<exists>x xa. cte_wp_at (\<lambda>a. (\<lambda>x. x && ~~ mask pd_bits) ` (\<lambda>x. x + lookup_pd_slot rv vptr) ` set [0 , 8 .e. 0x78] \<subseteq> obj_refs a) (x, xa) s\<rbrace>, -"
  apply (rule hoare_gen_asmE, rule hoare_strengthen_postE_R, rule find_pd_for_asid_cap_to)
  apply (elim exEI, clarsimp simp: cte_wp_at_caps_of_state)
  apply (simp add: lookup_pd_slot_add_eq)
  done

lemma find_pd_for_asid_cap_to_multiple2[wp]:
  "\<lbrace>invs and K (is_aligned vptr 25)\<rbrace>
     find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. \<forall>x\<in>set [0 , 8 .e. 0x78]. \<exists>a b.
             cte_wp_at (\<lambda>cp. x + lookup_pd_slot rv vptr && ~~ mask pd_bits
                             \<in> obj_refs cp \<and> is_pd_cap cp) (a, b) s\<rbrace>, -"
  apply (rule hoare_gen_asmE, rule hoare_strengthen_postE_R,
         rule find_pd_for_asid_cap_to)
  apply (intro ballI, elim exEI,
         clarsimp simp: cte_wp_at_caps_of_state)
  apply (simp add: lookup_pd_slot_add_eq)
  done

lemma unat_ucast_kernel_base_rshift:
  "unat (ucast (kernel_base >> 21) :: 11 word)
     = unat (kernel_base >> 21)"
  by (simp add: kernel_base_def)

lemma lookup_pt_slot_cap_to2:
  "\<lbrace>invs and \<exists>\<rhd> pd and K (is_aligned pd pd_bits) and K (vptr < kernel_base)\<rbrace>
     lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s. \<exists>oref cref cap. caps_of_state s (oref, cref) = Some cap
         \<and> rv && ~~ mask pt_bits \<in> obj_refs cap \<and> is_pt_cap cap\<rbrace>, -"
  apply (rule hoare_strengthen_postE_R, rule lookup_pt_slot_cap_to)
  apply fastforce
  done

lemma lookup_pt_slot_cap_to_multiple2:
  "\<lbrace>invs and \<exists>\<rhd> pd and K (is_aligned pd pd_bits) and K (vptr < kernel_base) and K (is_aligned vptr 16)\<rbrace>
      lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s. \<exists>oref cref. cte_wp_at
              (\<lambda>c. (\<lambda>x. x && ~~ mask pt_bits) ` (\<lambda>x. x + rv) ` set [0 , 8 .e. 0x78] \<subseteq> obj_refs c \<and> is_pt_cap c)
                  (oref, cref) s\<rbrace>, -"
  apply (rule hoare_strengthen_postE_R, rule lookup_pt_slot_cap_to_multiple1)
  apply (clarsimp simp: upto_enum_step_def image_image field_simps
                        linorder_not_le[symmetric]
                 split: if_split_asm)
   apply (erule notE, erule is_aligned_no_wrap')
   apply simp
  apply (fastforce simp: cte_wp_at_caps_of_state)
  done

crunch flush_page
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"
  (simp: global_refs_arch_update_eq crunch_simps)

lemma page_directory_at_lookup_mask_aligned_strg:
  "is_aligned pd pd_bits \<and> page_directory_at pd s
      \<longrightarrow> page_directory_at (lookup_pd_slot pd vptr && ~~ mask pd_bits) s"
  by (clarsimp simp: lookup_pd_slot_pd)

lemma page_directory_at_lookup_mask_add_aligned_strg:
  "is_aligned pd pd_bits \<and> page_directory_at pd s
               \<and> vmsz_aligned vptr ARMSuperSection
               \<and> x \<in> set [0, 8 .e. 0x78]
      \<longrightarrow> page_directory_at (x + lookup_pd_slot pd vptr && ~~ mask pd_bits) s"
  by (clarsimp simp: lookup_pd_slot_add_eq vmsz_aligned_def)

lemma dmo_ccMVA_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (cleanByVA_PoU a b) \<lbrace>\<lambda>r. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp | wp)+)[3]
  apply(erule use_valid, wp no_irq_cleanByVA_PoU no_irq, assumption)
  done


lemma dmo_ccr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (cleanCacheRange_PoU a b c) \<lbrace>\<lambda>r. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp | wp)+)[3]
  apply(erule use_valid, wp no_irq_cleanCacheRange_PoU no_irq, assumption)
  done

lemma ex_pt_cap_eq:
  "(\<exists>ref cap. caps_of_state s ref = Some cap \<and>
              p \<in> obj_refs cap \<and> is_pt_cap cap) =
   (\<exists>ref asid. caps_of_state s ref =
               Some (cap.ArchObjectCap (arch_cap.PageTableCap p asid)))"
  by (fastforce simp add: is_pt_cap_def obj_refs_def)

lemmas lookup_pt_slot_cap_to2' =
  lookup_pt_slot_cap_to2[simplified ex_pt_cap_eq[simplified split_paired_Ex]]

lemma unmap_page_invs:
  "\<lbrace>invs and K (asid \<le> mask asid_bits \<and> vptr < kernel_base \<and>
                vmsz_aligned vptr sz)\<rbrace>
      unmap_page sz asid vptr pptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unmap_page_def)
  apply (subgoal_tac "largePagePTE_offsets = [0 , 8 .e. 0x78]")
   prefer 2
   apply (clarsimp simp: largePagePTE_offsets_def vspace_bits_defs)
  apply (subgoal_tac "superSectionPDE_offsets = [0 , 8 .e. 0x78]")
   prefer 2
   apply (clarsimp simp: superSectionPDE_offsets_def vspace_bits_defs)
  apply (erule ssubst)
  apply (erule ssubst)
  apply (rule hoare_pre)
   apply (wp flush_page_invs hoare_vcg_const_imp_lift)
    apply (wp hoare_drop_imp[where f="check_mapping_pptr a b c" for a b c]
              hoare_drop_impE_R[where Q'="\<lambda>x y. x && mask b = c" for b c]
              store_pde_invs_unmap lookup_pt_slot_inv lookup_pt_slot_cap_to2'
              lookup_pt_slot_cap_to_multiple2
              store_pde_invs_unmap mapM_swp_store_pde_invs_unmap
              mapM_swp_store_pte_invs
           | wpc | simp)+
   apply (strengthen not_in_global_refs_vs_lookup
                     page_directory_at_lookup_mask_aligned_strg
                     page_directory_at_lookup_mask_add_aligned_strg)+
   apply (wp find_pd_for_asid_page_directory
             hoare_vcg_const_imp_liftE_R hoare_vcg_const_Ball_liftE_R
          | wp (once) hoare_drop_imps)+
  apply (auto simp: vmsz_aligned_def)
  done

lemma "\<lbrace>\<lambda>s. P (vs_lookup s) (valid_pte pte s)\<rbrace> set_cap cap cptr \<lbrace>\<lambda>_ s. P (vs_lookup s) (valid_pte pte s)\<rbrace>"
  apply (rule hoare_lift_Pf[where f=vs_lookup])
  apply (rule hoare_lift_Pf[where f="valid_pte pte"])
  apply (wp set_cap.vs_lookup set_cap_valid_pte_stronger)+
  done

lemma reachable_page_table_not_global:
  "\<lbrakk>(ref \<rhd> p) s; valid_kernel_mappings s;
    valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> p \<notin> {}"
  apply clarsimp
  done

lemma store_pte_unmap_page: (* ARMHYP write with xxx_bits? *)
  "\<lbrace>(\<lambda>s. \<exists>pt. ([VSRef (vaddr >> 21) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pt) s
     \<and> is_aligned pt pt_bits \<and> p = (pt + ((vaddr >> 12) && mask 9 << 3 )))\<rbrace>
     store_pte p InvalidPTE
   \<lbrace>\<lambda>rv s.\<not> ([VSRef ((vaddr >> 12) && mask 9) (Some APageTable),
             VSRef (vaddr >> 21) (Some APageDirectory),
             VSRef (asid && mask asid_low_bits) (Some AASIDPool),
             VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pptr) s\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def fun_upd_def[symmetric] vs_lookup_pages_def vs_asid_refs_def)
  apply (drule vs_lookup_pages1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup_pages1_def vs_lookup_def vs_asid_refs_def)
  apply (drule vs_lookup1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup1_def obj_at_def split: if_split_asm)
         apply (clarsimp simp: vs_refs_pages_def)+
      apply (thin_tac "(VSRef a (Some AASIDPool), b) \<in> c" for a b c)
      apply (clarsimp simp: graph_of_def
                     split: Structures_A.kernel_object.split_asm
                            arch_kernel_obj.splits
                            if_split_asm)
      apply (erule_tac P="a = c" for c in swap)
      apply (rule up_ucast_inj[where 'a=9 and 'b=32])
       apply (subst ucast_ucast_len)
        apply (simp add: vspace_bits_defs
                         is_aligned_add_helper less_le_trans[OF ucast_less]
                         shiftl_less_t2n'[where m=9 and n=3, simplified]
                         shiftr_less_t2n'[where m=9 and n=3, simplified]
                         word_bits_def shiftl_shiftr_id)+
     apply (clarsimp simp: graph_of_def vs_refs_def vs_refs_pages_def
                          pde_ref_def pde_ref_pages_def pte_ref_pages_def)+
  apply (simp add: vspace_bits_defs
                   is_aligned_add_helper less_le_trans[OF ucast_less]
                   shiftl_less_t2n'[where m=9 and n=3, simplified]
                   shiftr_less_t2n'[where m=9 and n=3, simplified]
                   word_bits_def shiftl_shiftr_id)+
  including unfold_objects
  by (clarsimp simp: pde_ref_def pte_ref_pages_def pde_ref_pages_def data_at_def
                     is_aligned_add_helper less_le_trans[OF ucast_less]
                     shiftl_less_t2n'[where m=9 and n=3, simplified]
               dest!: graph_ofD ucast_up_inj[where 'a=10 and 'b=32, simplified]
                      ucast_up_inj[where 'a=7 and 'b=32, simplified]
               split: if_split_asm  pde.splits pte.splits if_splits) (* slow *)

lemma set_vcpu_nonvcpu_at: (* generalise? this holds except when the ko is a vcpu *)
  "\<lbrace>\<lambda>s. P (ko_at ko x s) \<and> a_type ko \<noteq> AArch AVCPU\<rbrace>
      set_vcpu p v
        \<lbrace>\<lambda>_ s. P (ko_at ko x s)\<rbrace>"
  apply (simp add: set_vcpu_def)
  including unfold_objects
  by (wpsimp wp: set_object_wp_strong simp: a_type_def)

lemma set_vcpu_pd_at:
  "\<lbrace>\<lambda>s. P (ko_at (ArchObj (PageDirectory pd)) x s)\<rbrace>
      set_vcpu p v
        \<lbrace>\<lambda>_ s. P (ko_at (ArchObj (PageDirectory pd)) x s)\<rbrace>"
  by (wp set_vcpu_nonvcpu_at; auto)

lemma set_vcpu_pt_at:
  "\<lbrace>\<lambda>s. P (ko_at (ArchObj (PageTable pt)) x s)\<rbrace>
      set_vcpu p v
        \<lbrace>\<lambda>_ s. P (ko_at (ArchObj (PageTable pt)) x s)\<rbrace>"
  by (wp set_vcpu_nonvcpu_at; auto)

crunch vcpu_switch, flush_page
  for pd_at: "\<lambda>s. P (ko_at (ArchObj (PageDirectory pd)) x s)"
  and pt_at: "\<lambda>s. P (ko_at (ArchObj (PageTable pt)) x s)"
  (wp: crunch_wps simp: crunch_simps when_def)

lemma vs_lookup_pages_pteD: (* ARMHYP rewrite with xxx_bits *)
  "([VSRef ((vaddr >> 12) && mask 9) (Some APageTable),
     VSRef (vaddr >> 21) (Some APageDirectory),
     VSRef (asid && mask asid_low_bits) (Some AASIDPool),
     VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pg) s
   \<Longrightarrow>  \<exists>ap fun pd funa pt funb. ([VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> ap) s
               \<and> (arm_asid_table (arch_state s)) (asid_high_bits_of asid) = Some ap
               \<and> ko_at (ArchObj (ASIDPool fun)) ap s
               \<and> ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                  VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pd) s
               \<and> fun (ucast (asid && mask asid_low_bits)) = Some pd
               \<and> ko_at (ArchObj (PageDirectory funa)) pd s
               \<and> ([VSRef (vaddr >> 21) (Some APageDirectory),
                  VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                  VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pt) s
               \<and> pde_ref_pages (funa (ucast (vaddr >> 21))) = Some pt
               \<and> ko_at (ArchObj (PageTable funb)) pt s
               \<and> pte_ref_pages (funb (ucast ((vaddr >> 12) && mask 9 ))) = Some pg"

  apply (frule vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (frule_tac vs="[z]" for z in vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (frule_tac vs="[]" in vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (rule_tac x=p'b in exI)
  apply (frule vs_lookup_atD[OF iffD2[OF fun_cong[OF vs_lookup_pages_eq_at]]])
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                 dest!: graph_ofD
                 split: if_split_asm)
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)
  apply (simp add: up_ucast_inj_eq graph_of_def kernel_base_def
                   not_le ucast_less_ucast_weak[symmetric, where 'a=11 and 'b=32]
                   mask_asid_low_bits_ucast_ucast pde_ref_pages_def pte_ref_pages_def
            split: if_split_asm)
  apply (simp add: ucast_ucast_id
            split: pde.split_asm pte.split_asm)
  done

lemma vs_lookup_pages_pdeD:
  "([VSRef (vaddr >> 21) (Some APageDirectory),
     VSRef (asid && mask asid_low_bits) (Some AASIDPool),
     VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> p) s
   \<Longrightarrow>  \<exists>ap fun pd funa. ([VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> ap) s
               \<and> (arm_asid_table (arch_state s)) (asid_high_bits_of asid) = Some ap
               \<and> ko_at (ArchObj (ASIDPool fun)) ap s
               \<and> ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                  VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pd) s
               \<and> fun (ucast (asid && mask asid_low_bits)) = Some pd
               \<and> ko_at (ArchObj (PageDirectory funa)) pd s
               \<and> pde_ref_pages (funa (ucast (vaddr >> 21))) = Some p"

  apply (frule vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (frule_tac vs="[]" in vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (rule_tac x=p'a in exI)
  apply (frule vs_lookup_atD[OF iffD2[OF fun_cong[OF vs_lookup_pages_eq_at]]])
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                 dest!: graph_ofD
                 split: if_split_asm)
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)
  apply (simp add: up_ucast_inj_eq graph_of_def kernel_base_def
                   mask_asid_low_bits_ucast_ucast pde_ref_pages_def
            split: if_split_asm)
  apply (simp add: ucast_ucast_id
            split: pde.split_asm)
  done

lemma vs_lookup_ap_mappingD:
  "([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
     VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd) s
   \<Longrightarrow> \<exists>ap fun. (arm_asid_table (arch_state s)) (asid_high_bits_of asid) = Some ap
               \<and> ko_at (ArchObj (ASIDPool fun)) ap s
               \<and> fun (ucast (asid && mask asid_low_bits)) = Some pd"
apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def
                 dest!: graph_ofD
                 split: if_split_asm)
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)
  apply (simp add: up_ucast_inj_eq graph_of_def kernel_base_def
                   mask_asid_low_bits_ucast_ucast pde_ref_pages_def pte_ref_pages_def
            split: if_split_asm)
  done

lemma pt_aligned:
  "\<lbrakk>page_table_at pt s; pspace_aligned s\<rbrakk> \<Longrightarrow> is_aligned pt 12"
  by (auto simp: obj_at_def pspace_aligned_def vspace_bits_defs dom_def)

lemma vaddr_segment_nonsense:
  "is_aligned (p :: word32) 14 \<Longrightarrow> p + (vaddr >> 21 << 3) && ~~ mask pd_bits = p"
  by (simp add:  shiftl_less_t2n'[where m=11 and n=3, simplified]
    shiftr_less_t2n'[where m=11 and n=21, simplified]
                 vspace_bits_defs is_aligned_add_helper[THEN conjunct2])

lemma vaddr_segment_nonsense2:
  "is_aligned (p :: word32) 14 \<Longrightarrow>
   p + (vaddr >> 21 << 3) && mask pd_bits >> 3 = vaddr >> 21"
  by (simp add: shiftl_less_t2n'[where m=11 and n=3, simplified]
                shiftr_less_t2n'[where m=11 and n=21, simplified] vspace_bits_defs
                is_aligned_add_helper[THEN conjunct1] triple_shift_fun)

lemma vaddr_segment_nonsense3:
  "is_aligned (p :: word32) 12 \<Longrightarrow>
   (p + ((vaddr >> 12) && 0x1FF << 3) && ~~ mask pt_bits) = p"
  apply (rule is_aligned_add_helper[THEN conjunct2])
   apply (simp add: vspace_bits_defs)+
  apply (rule shiftl_less_t2n[where m=12 and n=3, simplified, OF and_mask_less'[where n=9, unfolded mask_def, simplified]])
   apply simp+
  done

lemma vaddr_segment_nonsense4:
  "is_aligned (p :: word32) 12 \<Longrightarrow>
   p + ((vaddr >> 12) && 0x1FF << 3) && mask pt_bits = (vaddr >> 12) && 0x1FF << 3"
  apply (subst is_aligned_add_helper[THEN conjunct1])
    apply (simp_all add: vspace_bits_defs)
   apply (rule shiftl_less_t2n'[where n=3 and m=9, simplified])
    apply (rule and_mask_less'[where n=9, unfolded mask_def, simplified])
    apply simp+
  done

(* FIXME: move near ArchAcc_R.lookup_pt_slot_inv? *)
lemma lookup_pt_slot_inv_validE:
  "\<lbrace>P\<rbrace> lookup_pt_slot pd vptr \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_inv hoare_drop_imp lookup_pt_slot_inv | wpc | simp)+
  done

lemma unmap_page_no_lookup_pages:
  "\<lbrace>\<lambda>s. \<not> (ref \<unrhd> p) s\<rbrace>
   unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>_ s. \<not> (ref \<unrhd> p) s\<rbrace>"
  apply (rule hoare_pre)
  apply (wp store_pte_no_lookup_pages hoare_drop_imps lookup_pt_slot_inv_validE
         mapM_UNIV_wp store_pde_no_lookup_pages
      | wpc | simp add: unmap_page_def swp_def | strengthen imp_consequent)+
  done

lemma vs_refs_pages_inj:
  "\<lbrakk> (r, p) \<in> vs_refs_pages ko; (r, p') \<in> vs_refs_pages ko \<rbrakk> \<Longrightarrow> p = p'"
  by (clarsimp simp: vs_refs_pages_def up_ucast_inj_eq dest!: graph_ofD
              split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)

lemma unique_vs_lookup_pages_loop:
  "\<lbrakk> (([r], x), a # list, p) \<in> vs_lookup_pages1 s ^^ length list;
      (([r'], y), a # list, p') \<in> vs_lookup_pages1 s ^^ length list;
      r = r' \<longrightarrow> x = y \<rbrakk>
       \<Longrightarrow> p = p'"
  apply (induct list arbitrary: a p p')
   apply simp
  apply (clarsimp simp: obj_at_def dest!: vs_lookup_pages1D)
  apply (erule vs_refs_pages_inj)
  apply fastforce
  done

lemma unique_vs_lookup_pages:
  "\<lbrakk>(r \<unrhd> p) s; (r \<unrhd> p') s\<rbrakk> \<Longrightarrow> p = p'"
  apply (clarsimp simp: vs_lookup_pages_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup_pages1_rtrancl_iterations)
  apply (case_tac r, simp_all)
  apply (erule(1) unique_vs_lookup_pages_loop)
  apply (clarsimp simp: up_ucast_inj_eq)
  done

lemma unmap_page_unmapped:
  "\<lbrace>pspace_aligned and valid_vspace_objs and data_at sz pptr and
    valid_objs and (\<lambda>s. valid_asid_table (arm_asid_table (arch_state s)) s) and
    K ((sz = ARMSmallPage \<or> sz = ARMLargePage \<longrightarrow> ref =
              [VSRef ((vaddr >> 12) && mask 9) (Some APageTable),
               VSRef (vaddr >> 21) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None]) \<and>
       (sz = ARMSection \<or> sz = ARMSuperSection \<longrightarrow> ref =
              [VSRef (vaddr >> 21) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None]) \<and>
        p = pptr)\<rbrace>
  unmap_page sz asid vaddr pptr
  \<lbrace>\<lambda>rv s. \<not> (ref \<unrhd> p) s\<rbrace>"
  apply (rule hoare_gen_asm)

    (* Establish that pptr reachable, otherwise trivial *)
  apply (rule hoare_name_pre_state2)
  apply (case_tac "\<not> (ref \<unrhd> p) s")
   apply (rule hoare_weaken_pre[OF unmap_page_no_lookup_pages])
   apply clarsimp+

     (* This should be somewhere else but isn't *)
  apply (subgoal_tac "\<exists>xs. [0 :: word32, 8 .e. 0x78] = 0 # xs")
   prefer 2
   apply (simp add: upto_enum_step_def upto_enum_word upt_rec; blast)
  apply (clarsimp simp: unmap_page_def[unfolded largePagePTE_offsets_def superSectionPDE_offsets_def
                                                vspace_bits_defs, simplified]
                        lookup_pd_slot_def lookup_pt_slot_def Let_def
                        mapM_Cons vspace_bits_defs
                  cong: option.case_cong vmpage_size.case_cong)

    (* Establish that pde in vsref chain isn't kernel mapping,
       otherwise trivial *)
(*  apply (case_tac "ucast (vaddr >> 21) \<in> kernel_mapping_slots")
   apply (case_tac sz)
       apply ((clarsimp simp: kernel_slot_impossible_vs_lookup_pages | wp)+)[2]
     apply ((clarsimp simp: kernel_slot_impossible_vs_lookup_pages2 | wp)+)[1]
    apply ((clarsimp simp: kernel_slot_impossible_vs_lookup_pages2 | wp)+)[1]
*)
      (* Proper cases *)
  apply (wp store_pte_unmap_page
            mapM_UNIV_wp[OF store_pte_no_lookup_pages]
            get_pte_wp get_pde_wp store_pde_unmap_page
            mapM_UNIV_wp[OF store_pde_no_lookup_pages]
            flush_page_vs_lookup flush_page_vs_lookup_pages
            hoare_vcg_all_lift hoare_vcg_const_imp_lift
            hoare_vcg_imp_lift[OF flush_page_pd_at]
            hoare_vcg_imp_lift[OF flush_page_pt_at]
            find_pd_for_asid_lots
         | wpc | simp add: swp_def check_mapping_pptr_def vspace_bits_defs)+
  apply clarsimp
  apply (case_tac sz, simp_all)
     apply (drule vs_lookup_pages_pteD)
     apply (rule conjI[rotated])
      apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
     apply clarsimp
     apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
     apply (frule (1) pd_aligned)
     apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr, simplified vspace_bits_defs, simplified]
                      vaddr_segment_nonsense2[where vaddr=vaddr, simplified vspace_bits_defs, simplified])
     apply (frule valid_vspace_objsD)
       apply (clarsimp simp: obj_at_def a_type_def)
       apply (rule refl)
      apply assumption
     apply (simp, drule_tac x="(ucast (vaddr >> 21))" in spec, clarsimp)
     apply (clarsimp simp: pde_ref_pages_def
                    split: pde.splits
                    dest!: )
       apply (frule pt_aligned[rotated])
        apply (simp add: obj_at_def a_type_def)
        apply (simp split: Structures_A.kernel_object.splits arch_kernel_obj.splits, blast)
       apply (clarsimp simp: obj_at_def)
       apply (simp add: vaddr_segment_nonsense3[where vaddr=vaddr, simplified vspace_bits_defs, simplified]
                        vaddr_segment_nonsense4[where vaddr=vaddr, simplified vspace_bits_defs, simplified]
                        word_1FF_is_mask[symmetric])
       apply (drule_tac p="ptrFromPAddr x" for x in vs_lookup_vs_lookup_pagesI')
          apply ((simp add: obj_at_def a_type_def)+)[3]
       apply (frule_tac p="ptrFromPAddr a" for a in valid_vspace_objsD)
         apply ((simp add: obj_at_def)+)[2]
       apply (clarsimp simp add: valid_vspace_obj_def)
(*       apply (intro conjI impI)
        apply (simp add: vspace_bits_defs mask_def) *)
       apply (erule allE[where x="(ucast ((vaddr >> 12) && mask 9))"])

       apply (fastforce simp: pte_ref_pages_def mask_def obj_at_def a_type_def data_at_def
                             shiftl_shiftr_id[where n=3,
                                             OF _ less_le_trans[OF and_mask_less'[where n=9]],
                                             unfolded mask_def word_bits_def, simplified]
                      split: pte.splits if_splits)

      apply ((clarsimp simp: obj_at_def a_type_def data_at_def)+)[2]

    apply (drule vs_lookup_pages_pteD)
    apply (rule conjI[rotated])
     apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
    apply clarsimp
    apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
    apply (frule (1) pd_aligned)
    apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr, simplified vspace_bits_defs, simplified]
                     vaddr_segment_nonsense2[where vaddr=vaddr, simplified vspace_bits_defs, simplified])
    apply (frule valid_vspace_objsD)
      apply (clarsimp simp: obj_at_def a_type_def)
      apply (rule refl)
     apply assumption
    apply (simp, drule_tac x="ucast (vaddr >> 21)" in spec)
    apply (clarsimp simp: pde_ref_pages_def
                   split: pde.splits
                   dest!: )
      apply (frule pt_aligned[rotated])
       apply (simp add: obj_at_def a_type_def)
       apply (simp split: Structures_A.kernel_object.splits arch_kernel_obj.splits, blast)
      apply (clarsimp simp: obj_at_def)
      apply (simp add: vaddr_segment_nonsense3[where vaddr=vaddr, simplified vspace_bits_defs, simplified]
                       vaddr_segment_nonsense4[where vaddr=vaddr, simplified vspace_bits_defs, simplified]
                       word_1FF_is_mask[symmetric])
      apply (drule_tac p="ptrFromPAddr x" for x in vs_lookup_vs_lookup_pagesI')
         apply ((simp add: obj_at_def a_type_def)+)[3]
      apply (frule_tac p="ptrFromPAddr a" for a in valid_vspace_objsD)
        apply ((simp add: obj_at_def)+)[2]
      apply (simp add: valid_vspace_obj_def)
(*      apply (intro conjI impI)
       apply (simp add: vspace_bits_defs mask_def) *)
      apply (erule allE[where x="(ucast ((vaddr >> 12) && mask 9))"])
     apply (fastforce simp: pte_ref_pages_def mask_def obj_at_def a_type_def data_at_def
                           shiftl_shiftr_id[where n=3,
                                            OF _ less_le_trans[OF and_mask_less'[where n=9]],
                                            unfolded mask_def word_bits_def, simplified]
                    split: pte.splits if_splits)
     apply ((clarsimp simp: obj_at_def a_type_def data_at_def)+)[2]

   apply (drule vs_lookup_pages_pdeD)
   apply (rule conjI[rotated])
    apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
   apply clarsimp
   apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
   apply (frule (1) pd_aligned)
   apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr, simplified vspace_bits_defs, simplified]
                    vaddr_segment_nonsense2[where vaddr=vaddr, simplified vspace_bits_defs, simplified])
   apply (frule valid_vspace_objsD)
     apply (clarsimp simp: obj_at_def a_type_def)
     apply (rule refl)
    apply assumption
   apply (simp, drule_tac x="ucast (vaddr >> 21)" in spec)
   apply (clarsimp simp: pde_ref_pages_def
                  split: pde.splits)
     apply (clarsimp simp: obj_at_def data_at_def)
    apply (drule_tac p="rv" in vs_lookup_vs_lookup_pagesI')
       apply ((simp add: obj_at_def a_type_def)+)[3]
    apply (frule_tac p="rv" in valid_vspace_objsD)
      apply ((simp add: obj_at_def)+)[2]
    apply (fastforce simp: valid_vspace_obj_def data_at_def)
(*    apply (drule_tac x="ucast (vaddr >> 21)" in spec) *)
    apply (fastforce simp: obj_at_def a_type_def pd_bits_def pageBits_def data_at_def
                   split: pde.splits)
   apply (fastforce simp: obj_at_def a_type_def data_at_def)

  apply (drule vs_lookup_pages_pdeD)
  apply (rule conjI[rotated])
   apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
  apply clarsimp
  apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
  apply (frule (1) pd_aligned)
  apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr, simplified vspace_bits_defs, simplified]
                   vaddr_segment_nonsense2[where vaddr=vaddr, simplified vspace_bits_defs, simplified])
  apply (frule valid_vspace_objsD)
    apply (clarsimp simp: obj_at_def a_type_def)
    apply (rule refl)
   apply assumption
  apply (simp, drule_tac x="ucast (vaddr >> 21)" in spec)
  apply (clarsimp simp: pde_ref_pages_def
                 split: pde.splits)
    apply (fastforce simp: obj_at_def data_at_def)
   apply (drule_tac p="rv" in vs_lookup_vs_lookup_pagesI')
      apply ((simp add: obj_at_def a_type_def)+)[3]
   apply (frule_tac p="rv" in valid_vspace_objsD)
     apply ((simp add: obj_at_def)+)[2]
   apply (simp add: valid_vspace_obj_def)
   apply (drule_tac x="ucast (vaddr >> 21)" in spec)
   apply (fastforce simp: obj_at_def a_type_def vspace_bits_defs data_at_def
                  split: pde.splits if_splits)
  apply (clarsimp simp: obj_at_def a_type_def vspace_bits_defs)
done

lemma unmap_page_page_unmapped:
  "\<lbrace>pspace_aligned and valid_objs and valid_vspace_objs and
    (\<lambda>s. valid_asid_table (arm_asid_table (arch_state s)) s) and
    data_at sz pptr and
    K (p = pptr) and K (sz = ARMSmallPage \<or> sz = ARMLargePage)\<rbrace>
   unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>rv s. \<not> ([VSRef ((vaddr >> 12) && mask 9) (Some APageTable),
               VSRef (vaddr >> 21) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> p) s\<rbrace>"
  by (rule hoare_pre_imp[OF _ unmap_page_unmapped]) (auto simp add: vspace_bits_defs)

lemma unmap_page_section_unmapped:
  "\<lbrace>pspace_aligned and valid_objs and valid_vspace_objs and
    (\<lambda>s. valid_asid_table (arm_asid_table (arch_state s)) s) and
    data_at sz pptr and
    K (p = pptr) and K (sz = ARMSection \<or> sz = ARMSuperSection)\<rbrace>
   unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (vaddr >> 21) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> p) s\<rbrace>"
  by (rule hoare_pre_imp[OF _ unmap_page_unmapped]) auto

crunch pte_check_if_mapped, pde_check_if_mapped
  for invs[wp]: "invs"

crunch pte_check_if_mapped, pde_check_if_mapped
  for vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"

crunch pte_check_if_mapped
  for valid_pte[wp]: "\<lambda>s. P (valid_pte p s)"

lemma set_mi_invs[wp]: "\<lbrace>invs\<rbrace> set_message_info t a \<lbrace>\<lambda>x. invs\<rbrace>"
  by (simp add: set_message_info_def, wp)

lemma data_at_orth_vcpu:
  "data_at a p s \<Longrightarrow> \<not> ep_at p s
  \<and> \<not> ntfn_at p s \<and>\<not> cap_table_at sz p s \<and> \<not> tcb_at p s \<and> \<not> asid_pool_at p s
  \<and> \<not> page_table_at p s \<and> \<not> page_directory_at p s \<and> \<not> asid_pool_at p s \<and> \<not> vcpu_at p s"
  apply (clarsimp simp: data_at_def obj_at_def a_type_def)
  apply (case_tac "kheap s p",simp)
  subgoal for ko
   by (case_tac ko,auto simp add: is_ep_def is_ntfn_def is_cap_table_def is_tcb_def)
  done

lemma data_at_pg_cap:
  "\<lbrakk>data_at sz p s;valid_cap cap s; p \<in> obj_refs cap\<rbrakk> \<Longrightarrow> is_pg_cap cap"
  apply (case_tac cap)
   apply (clarsimp simp: is_pg_cap_def valid_cap_def data_at_orth_vcpu option.split)+
  apply (clarsimp split: arch_cap.split_asm simp: data_at_orth_vcpu)
done

lemma perform_page_invs [wp]:
  "\<lbrace>invs and valid_page_inv pinv\<rbrace> perform_page_invocation pinv \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases pinv, simp_all)
     \<comment> \<open>PageMap\<close>
     apply (rename_tac asid cap cslot_ptr sum)
     apply clarsimp
     apply (rule hoare_pre)
      apply (wp get_master_pte_wp get_master_pde_wp mapM_swp_store_pde_invs_unmap store_pde_invs_unmap' hoare_vcg_const_imp_lift hoare_vcg_all_lift set_cap_arch_obj arch_update_cap_invs_map
             | wpc
             | simp add: pte_check_if_mapped_def pde_check_if_mapped_def del: fun_upd_apply
             | subst cte_wp_at_caps_of_state)+
       apply (wp (once) hoare_drop_imp)
       apply (wp arch_update_cap_invs_map)
       apply (rule hoare_vcg_conj_lift)
        apply (rule hoare_lift_Pf[where f=vs_lookup, OF _ set_cap.vs_lookup])
        apply (rule_tac f="valid_pte xa" in hoare_lift_Pf[OF _ set_cap_valid_pte_stronger])
        apply wp
       apply (rule hoare_lift_Pf2[where f=vs_lookup, OF _ set_cap.vs_lookup])
       apply ((wp dmo_ccr_invs arch_update_cap_invs_map
                 hoare_vcg_const_Ball_lift
                 hoare_vcg_const_imp_lift hoare_vcg_all_lift set_cap_typ_at
                 hoare_vcg_ex_lift hoare_vcg_ball_lift set_cap_arch_obj
                 set_cap.vs_lookup
              | wpc | simp add: same_refs_def del: fun_upd_apply split del: if_split
              | subst cte_wp_at_caps_of_state)+)
      apply (wp (once) hoare_drop_imp)
      apply (wp arch_update_cap_invs_map hoare_vcg_ex_lift set_cap_arch_obj)
     apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state neq_Nil_conv
                           valid_slots_def empty_refs_def parent_for_refs_def
                 simp del: fun_upd_apply del: exE
                    split: sum.splits)
      apply (rule conjI)
       apply (clarsimp simp: is_cap_simps is_arch_update_def
                             cap_master_cap_simps
                      dest!: cap_master_cap_eqDs)
       apply (clarsimp simp: same_refs_def)
      apply clarsimp
      apply (rule conjI)
       apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
       apply (rule conjI)
        apply (clarsimp simp: is_arch_update_def is_pt_cap_def is_pg_cap_def
                              cap_master_cap_def image_def
                        split: Structures_A.cap.splits arch_cap.splits)
       apply (clarsimp simp: is_pt_cap_def cap_asid_def image_def neq_Nil_conv Collect_disj_eq
                      split: Structures_A.cap.splits arch_cap.splits option.splits)
      apply (rule conjI)
       apply (drule same_refs_lD)
       apply clarsimp
       apply (fastforce simp: vspace_bits_defs)
      apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
      apply (clarsimp simp: is_arch_update_def
                            cap_master_cap_def is_cap_simps
                     split: Structures_A.cap.splits arch_cap.splits)
     apply (rule conjI)
      apply (erule exEI)
      apply (clarsimp simp: same_refs_def)
     apply (rule conjI)
      apply clarsimp
      apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
      apply (clarsimp simp: is_arch_update_def
                            cap_master_cap_def is_cap_simps
                     split: Structures_A.cap.splits arch_cap.splits)
     apply (rule conjI)
      apply (rule_tac x=a in exI, rule_tac x=b in exI, rule_tac x=cap in exI)
      apply (clarsimp simp: same_refs_def)
     apply (rule conjI)
      apply (clarsimp simp: pde_at_def obj_at_def
                            caps_of_state_cteD'[where P=\<top>, simplified])
      apply (drule_tac cap="ArchObjectCap acap" and ptr="(aa,ba)"
                    in valid_global_refsD[OF invs_valid_global_refs])
        apply assumption+
      apply (clarsimp simp: cap_range_def)
     apply (clarsimp)
     apply (rule conjI)
      apply (clarsimp simp: pde_at_def obj_at_def a_type_def)
      apply (clarsimp split: Structures_A.kernel_object.split_asm
                            if_split_asm arch_kernel_obj.splits)
     apply (erule ballEI)
     apply (clarsimp simp: pde_at_def obj_at_def
                            caps_of_state_cteD'[where P=\<top>, simplified])
     apply (drule_tac cap="ArchObjectCap acap" and ptr="(aa,ba)"
                    in valid_global_refsD[OF invs_valid_global_refs])
       apply assumption+
     apply (drule_tac x=sl in imageI[where f="\<lambda>x. x && ~~ mask pd_bits"])
     apply (drule (1) subsetD)
     apply (clarsimp simp: cap_range_def)
   \<comment> \<open>PageUnmap\<close>
   apply (rename_tac arch_cap cslot_ptr)
   apply (rule hoare_pre)
    apply (wp dmo_invs arch_update_cap_invs_unmap_page get_cap_wp
              hoare_vcg_const_imp_lift | wpc | simp)+
      apply (rule_tac Q'="\<lambda>_ s. invs s \<and>
                               cte_wp_at (\<lambda>c. is_pg_cap c \<and>
                                 (\<forall>ref. vs_cap_ref c = Some ref \<longrightarrow>
                                        \<not> (ref \<unrhd> obj_ref_of c) s)) cslot_ptr s"
                   in hoare_strengthen_post)
       prefer 2
       apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps
                             update_map_data_def
                             is_arch_update_def cap_master_cap_simps)
       apply (drule caps_of_state_valid, fastforce)
       apply (clarsimp simp: valid_cap_def cap_aligned_def vs_cap_ref_def
                      split: option.splits vmpage_size.splits cap.splits)
      apply (simp add: cte_wp_at_caps_of_state)
      apply (wp unmap_page_invs hoare_vcg_ex_lift hoare_vcg_all_lift
                hoare_vcg_imp_lift unmap_page_unmapped)+
   apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: is_cap_simps cap_master_cap_simps is_arch_update_def
                         update_map_data_def cap_rights_update_def
                         acap_rights_update_def)
   using valid_validate_vm_rights[simplified valid_vm_rights_def]
   apply (auto simp: valid_cap_def cap_aligned_def mask_def vs_cap_ref_def vspace_bits_defs data_at_def
                   split: vmpage_size.splits option.splits if_splits)[1]
   \<comment> \<open>PageFlush\<close>
   apply (wpsimp wp: dmo_invs_lift set_vm_root_for_flush_invs simp: valid_page_inv_def)
  apply wpsimp
  done

end

locale asid_pool_map = Arch +
  fixes s ap pool asid pdp pd s'
  defines "(s' :: ('a::state_ext) state) \<equiv>
           s\<lparr>kheap := (kheap s)(ap \<mapsto> ArchObj (ASIDPool (pool(asid \<mapsto> pdp))))\<rparr>"
  assumes ap:  "kheap s ap = Some (ArchObj (ASIDPool pool))"
  assumes new: "pool asid = None"
  assumes pd:  "kheap s pdp = Some (ArchObj (PageDirectory pd))"
  assumes pde: "empty_table {}
                            (ArchObj (PageDirectory pd))"
begin

definition
  "new_lookups \<equiv>
   {((rs,p),(rs',p')). rs' = VSRef (ucast asid) (Some AASIDPool) # rs \<and>
                       p = ap \<and> p' = pdp}"

lemma vs_lookup1:
  "vs_lookup1 s' = vs_lookup1 s \<union> new_lookups"
  using pde pd new ap
  apply (clarsimp simp: vs_lookup1_def new_lookups_def)
  apply (rule set_eqI)
  apply (clarsimp simp: obj_at_def s'_def vs_refs_def graph_of_def)
  apply (rule iffI)
   apply (clarsimp simp: image_def split: if_split_asm)
   apply fastforce
  apply fastforce
  done

lemma vs_lookup_trans:
  "(vs_lookup1 s')^* = (vs_lookup1 s)^* \<union> (vs_lookup1 s)^* O new_lookups^*"
  using pd pde
  apply (simp add: vs_lookup1)
  apply (rule union_trans)
  apply (subst (asm) new_lookups_def)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def
                        empty_table_def pde_ref_def
                 split: if_split_asm)
  done

lemma arch_state [simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)

lemma new_lookups_rtrancl:
  "new_lookups^* = Id \<union> new_lookups"
  using ap pd
  apply -
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (erule rtrancl_induct2)
    apply clarsimp
   apply (clarsimp del: disjCI)
   apply (erule disjE)
    apply clarsimp
   apply (thin_tac "x \<in> R^*" for x R)
   apply (subgoal_tac "False", simp+)
   apply (clarsimp simp: new_lookups_def)
  apply (erule disjE, simp+)
  done

lemma vs_lookup:
  "vs_lookup s' = vs_lookup s \<union> new_lookups^* `` vs_lookup s"
  unfolding vs_lookup_def
  by (simp add: vs_lookup_trans relcomp_Image Un_Image)

lemma vs_lookup2:
  "vs_lookup s' = vs_lookup s \<union> (new_lookups `` vs_lookup s)"
  by (auto simp add: vs_lookup new_lookups_rtrancl)

lemma vs_lookup_pages1:
  "vs_lookup_pages1 s' = vs_lookup_pages1 s \<union> new_lookups"
  using pde pd new ap
  apply (clarsimp simp: vs_lookup_pages1_def new_lookups_def)
  apply (rule set_eqI)
  apply (clarsimp simp: obj_at_def s'_def vs_refs_pages_def graph_of_def)
  apply (rule iffI)
   apply (clarsimp simp: image_def split: if_split_asm)
   apply fastforce
  apply fastforce
  done

lemma vs_lookup_pages_trans:
  "(vs_lookup_pages1 s')^* =
   (vs_lookup_pages1 s)^* \<union> (vs_lookup_pages1 s)^* O new_lookups^*"
  using pd pde
  apply (simp add: vs_lookup_pages1)
  apply (rule union_trans)
  apply (subst (asm) new_lookups_def)
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                        graph_of_def empty_table_def pde_ref_pages_def
                 split: if_split_asm)
  done

lemma vs_lookup_pages:
  "vs_lookup_pages s' =
   vs_lookup_pages s \<union> new_lookups^* `` vs_lookup_pages s"
  unfolding vs_lookup_pages_def
  by (simp add: vs_lookup_pages_trans relcomp_Image Un_Image)

lemma vs_lookup_pages2:
  "vs_lookup_pages s' = vs_lookup_pages s \<union> (new_lookups `` vs_lookup_pages s)"
  by (auto simp add: vs_lookup_pages new_lookups_rtrancl)

end

context Arch begin arch_global_naming

lemma not_kernel_slot_not_global_pt: (* ARMHYP? remove? *)
  "\<lbrakk>pde_ref (pd x) = Some p;
    kheap s p' = Some (ArchObj (PageDirectory pd)); valid_kernel_mappings s\<rbrakk>
   \<Longrightarrow> p \<notin> {}"
  apply (clarsimp simp: valid_kernel_mappings_def)
  done

lemma set_asid_pool_vspace_objs_map:
  "\<lbrace>valid_vspace_objs and valid_arch_state and
    valid_kernel_mappings and
    ko_at (ArchObj (ASIDPool pool)) ap and
    K (pool asid = None) and
    \<exists>\<rhd> ap and page_directory_at pd and
    (\<lambda>s. obj_at (empty_table {}) pd s) \<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def
                   a_type_def[split_simps kernel_object.split arch_kernel_obj.split])
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (frule (2) valid_vspace_objsD)
  apply (clarsimp simp: valid_vspace_objs_def simp del: valid_vspace_obj.simps)
  apply (case_tac "p = ap")
   apply (clarsimp simp: obj_at_def
               simp del: fun_upd_apply valid_vspace_obj.simps)
   apply (clarsimp simp: ran_def)
   apply (case_tac "a = asid")
    apply clarsimp
      apply (rule typ_at_same_type)
      apply (simp add: obj_at_def a_type_simps)
     prefer 2
     apply assumption
    apply (simp add: a_type_def)
   apply clarsimp
   apply (erule allE, erule impE, rule exI, assumption)+
   apply clarsimp
   apply (erule typ_at_same_type)
    prefer 2
    apply assumption
   apply (simp add: a_type_def)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (frule (3) asid_pool_map.intro)
  apply (subst (asm) asid_pool_map.vs_lookup, assumption)
  apply clarsimp
  apply (erule disjE)
   apply (erule_tac x=p in allE, simp)
   apply (erule impE, blast)
   apply (erule valid_vspace_obj_same_type)
    apply (simp add: obj_at_def a_type_def)
   apply (simp add: a_type_def)
  apply (clarsimp simp: asid_pool_map.new_lookups_rtrancl)
  apply (erule disjE)
   apply clarsimp
   apply (erule_tac x=p in allE, simp)
   apply (erule impE, blast)
   apply (erule valid_vspace_obj_same_type)
    apply (simp add: obj_at_def a_type_def)
   apply (simp add: a_type_def)
  apply (clarsimp simp: asid_pool_map.new_lookups_def empty_table_def)
  done

lemma obj_at_not_pt_not_in_global_pts: (* ARMHYP remove? *)
  "\<lbrakk> obj_at P p s; valid_arch_state s; \<And>pt. \<not> P (ArchObj (PageTable pt)) \<rbrakk>
          \<Longrightarrow> p \<notin> {}"
  apply (rule notI)
  apply (clarsimp simp: obj_at_def)
  done

lemma set_asid_pool_valid_arch_caps_map:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_objs
    and valid_vspace_objs and ko_at (ArchObj (ASIDPool pool)) ap
    and (\<lambda>s. \<exists>rf. (rf \<rhd> ap) s \<and> (\<exists>ptr cap. caps_of_state s ptr = Some cap
                                   \<and> pd \<in> obj_refs cap \<and> vs_cap_ref cap = Some ((VSRef (ucast asid) (Some AASIDPool)) # rf))
                              \<and> (VSRef (ucast asid) (Some AASIDPool) # rf \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None]))
    and page_directory_at pd
    and (\<lambda>s. obj_at (empty_table {}) pd s)
    and K (pool asid = None)\<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (frule obj_at_not_pt_not_in_global_pts[where p=pd], clarsimp+)
   apply (simp add: a_type_def)
  apply (frule obj_at_not_pt_not_in_global_pts[where p=ap], clarsimp+)
  apply (clarsimp simp: obj_at_def valid_arch_caps_def
                        caps_of_state_after_update)
  apply (clarsimp simp: a_type_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm)
  apply (frule(3) asid_pool_map.intro)
  apply (simp add: fun_upd_def[symmetric])
  apply (rule conjI)
   apply (simp add: valid_vs_lookup_def
                    caps_of_state_after_update[folded fun_upd_def]
                    obj_at_def)
   apply (subst asid_pool_map.vs_lookup_pages2, assumption)
   apply simp
   apply (clarsimp simp: asid_pool_map.new_lookups_def)
   apply (frule(2) vs_lookup_vs_lookup_pagesI, simp add: valid_arch_state_def)
   apply (drule(1) ref_is_unique)
        apply (simp add: valid_vs_lookup_def)+
     apply (simp add: valid_arch_state_def)
    apply (rule valid_objs_caps, simp)
   apply fastforce
  apply (simp add: valid_table_caps_def
                   caps_of_state_after_update[folded fun_upd_def] obj_at_def
              del: imp_disjL)
  apply (clarsimp simp del: imp_disjL)
  apply (drule(1) caps_of_state_valid_cap)+
  apply (auto simp add: valid_cap_def is_pt_cap_def is_pd_cap_def obj_at_def
                        a_type_def)[1]
  done

lemma set_asid_pool_asid_map:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (ASIDPool pool)) ap
    and K (pool asid = None)\<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def a_type_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: vspace_at_asid_def)
  apply (drule vs_lookup_2ConsD)
  apply clarsimp
  apply (erule vs_lookup_atE)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (case_tac "p'=ap")
   apply (clarsimp simp: obj_at_def)
   apply (rule vs_lookupI)
    apply (clarsimp simp: vs_asid_refs_def graph_of_def)
    apply fastforce
   apply (rule r_into_rtrancl)
   apply (rule_tac r="VSRef (a && mask asid_low_bits) (Some AASIDPool)" in vs_lookup1I)
     apply (simp add: obj_at_def)
    apply (simp add: vs_refs_def graph_of_def)
    apply fastforce
   apply simp
  apply (rule vs_lookupI)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def)
   apply fastforce
  apply (rule r_into_rtrancl)
  apply (rule vs_lookup1I)
    apply (simp add: obj_at_def split: if_splits)+
  done

lemma set_asid_pool_invs_map:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool pool)) ap
    and (\<lambda>s. \<exists>rf. (rf \<rhd> ap) s \<and> (\<exists>ptr cap. caps_of_state s ptr = Some cap
                                  \<and> pd \<in> obj_refs cap \<and> vs_cap_ref cap = Some ((VSRef (ucast asid) (Some AASIDPool)) # rf))
                              \<and> (VSRef (ucast asid) (Some AASIDPool) # rf \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None]))
    and page_directory_at pd
    and (\<lambda>s. obj_at (empty_table {}) pd s)
    and K (pool asid = None)\<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre, wp valid_irq_node_typ set_asid_pool_typ_at set_asid_pool_vspace_objs_map valid_irq_handlers_lift
                            set_asid_pool_valid_arch_caps_map set_asid_pool_asid_map)
  apply clarsimp
  apply auto
  done

lemma perform_asid_pool_invs [wp]:
  "\<lbrace>invs and valid_apinv api\<rbrace> perform_asid_pool_invocation api \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: perform_asid_pool_invocation_def split: asid_pool_invocation.splits)
  apply (wp arch_update_cap_invs_map set_asid_pool_invs_map
            get_cap_wp set_cap_typ_at empty_table_lift[OF _ hoare_weaken_pre]
            set_cap_obj_at_other
               |wpc|simp|wp (once) hoare_vcg_ex_lift)+
  apply (clarsimp simp: valid_apinv_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps cap_master_cap_simps)
  apply (frule caps_of_state_cteD)
  apply (drule cte_wp_valid_cap, fastforce)
  apply (simp add: valid_cap_def cap_aligned_def)
  apply (clarsimp simp: cap_asid_def split: option.splits)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
  apply (rule conjI)
   apply (erule vs_lookup_atE)
   apply clarsimp
   apply (drule caps_of_state_cteD)
   apply (clarsimp simp: cte_wp_at_cases obj_at_def)
  apply (rule conjI)
   apply (rule exI)
   apply (rule conjI, assumption)
   apply (rule conjI)
    apply (rule_tac x=a in exI)
    apply (rule_tac x=b in exI)
    apply (clarsimp simp: vs_cap_ref_def mask_asid_low_bits_ucast_ucast)
   apply (clarsimp simp: asid_low_bits_def[simplified, symmetric] ucast_ucast_mask
                         word_neq_0_conv[symmetric])
   apply (erule notE, rule asid_low_high_bits, simp_all)[1]
   apply (simp add: asid_high_bits_of_def)
  apply (rule conjI)
   apply (erule(1) valid_table_caps_pdD [OF _ invs_pd_caps])
  apply (rule conjI)
   apply clarsimp
   apply (drule caps_of_state_cteD)
   apply (clarsimp simp: obj_at_def cte_wp_at_cases a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done

lemma valid_vspace_obj_default:
  assumes tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  shows "ArchObj ao = default_object ty dev us \<Longrightarrow> valid_vspace_obj ao s'"
  apply (cases ty, simp_all add: default_object_def tyunt)
  apply (simp add: valid_vspace_obj_default')
  done

end
end
