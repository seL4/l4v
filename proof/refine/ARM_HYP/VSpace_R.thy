(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   ARM VSpace refinement
*)

theory VSpace_R
imports TcbAcc_R
begin
context Arch begin global_naming ARM (*FIXME: arch_split*)

lemmas store_pte_typ_ats[wp] = store_pte_typ_ats abs_atyp_at_lifts[OF store_pte_typ_at]
lemmas store_pde_typ_ats[wp] = store_pde_typ_ats abs_atyp_at_lifts[OF store_pde_typ_at]

end

context begin interpretation Arch . (*FIXME: arch_split*)

lemma option_case_all_conv:
  "(case x of None \<Rightarrow> True | Some v \<Rightarrow> P v) = (\<forall>v. x = Some v \<longrightarrow> P v)"
  by (auto split: option.split)

lemma cteCaps_of_ctes_of_lift:
  "(\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P (cteCaps_of s) \<rbrace> f \<lbrace>\<lambda>_ s. P (cteCaps_of s)\<rbrace>"
  unfolding cteCaps_of_def .

abbreviation
 "injectKOS \<equiv> (injectKO :: ('a :: pspace_storable) \<Rightarrow> kernel_object)"

definition
  "pd_at_asid' pd asid \<equiv> \<lambda>s. \<exists>ap pool.
             armKSASIDTable (ksArchState s) (ucast (asid_high_bits_of asid)) = Some ap \<and>
             ko_at' (ASIDPool pool) ap s \<and> pool (asid && mask asid_low_bits) = Some pd \<and>
             page_directory_at' pd s"

defs checkPDASIDMapMembership_def:
  "checkPDASIDMapMembership pd asids
     \<equiv> stateAssert (\<lambda>s. pd \<notin> ran ((option_map snd o armKSASIDMap (ksArchState s) |` (- set asids)))) []"

crunches checkPDAt, getIRQState
  for inv[wp]: P

lemma findPDForASID_pd_at_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. (page_directory_at' pd s \<longrightarrow> pd_at_asid' pd asid s)
            \<longrightarrow> P pd s\<rbrace> findPDForASID asid \<lbrace>P\<rbrace>,-"
  apply (simp add: findPDForASID_def assertE_def
             cong: option.case_cong
               split del: if_split)
  apply (rule hoare_pre)
   apply (wp getASID_wp | wpc | simp add: o_def split del: if_split)+
  apply (clarsimp simp: pd_at_asid'_def)
  apply (case_tac ko, simp)
  apply (subst(asm) inv_f_f)
   apply (rule inj_onI, simp+)
  apply fastforce
  done

lemma findPDForASIDAssert_pd_at_wp:
  "\<lbrace>(\<lambda>s. \<forall>pd. pd_at_asid' pd asid  s
               \<and> pd \<notin> ran ((option_map snd o armKSASIDMap (ksArchState s) |` (- {asid})))
                \<longrightarrow> P pd s)\<rbrace>
       findPDForASIDAssert asid \<lbrace>P\<rbrace>"
  apply (simp add: findPDForASIDAssert_def const_def
                   checkPDAt_def checkPDUniqueToASID_def
                   checkPDASIDMapMembership_def)
  apply (rule hoare_pre, wp getPDE_wp findPDForASID_pd_at_wp)
  apply simp
  done

crunch inv[wp]: findPDForASIDAssert "P"
  (simp: const_def crunch_simps wp: loadObject_default_inv crunch_wps ignore_del: getObject)

lemma pspace_relation_pd:
  assumes p: "pspace_relation (kheap a) (ksPSpace c)"
  assumes pa: "pspace_aligned a"
  assumes pad: "pspace_aligned' c" "pspace_distinct' c"
  assumes t: "page_directory_at p a"
  shows "page_directory_at' p c" using assms pd_aligned [OF pa t]
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp split: Structures_A.kernel_object.split_asm
                        if_split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: page_directory_at'_def vspace_bits_defs
                        typ_at_to_obj_at_arches)
  apply (drule_tac x="ucast y" in spec, clarsimp)
  apply (simp add: ucast_ucast_mask iffD2 [OF mask_eq_iff_w2p] word_size)
  apply (clarsimp simp add: pde_relation_def)
  apply (drule(2) aligned_distinct_pde_atI')
  apply (erule obj_at'_weakenE)
  apply simp
  done

lemma find_pd_for_asid_eq_helper:
  "\<lbrakk> vspace_at_asid asid pd s; valid_vspace_objs s;
         asid \<noteq> 0; pspace_aligned s \<rbrakk>
    \<Longrightarrow> find_pd_for_asid asid s = returnOk pd s
             \<and> page_directory_at pd s \<and> is_aligned pd pdBits"
  apply (clarsimp simp: vspace_at_asid_def valid_vspace_objs_def)
  apply (frule spec, drule mp, erule exI)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def
                 elim!: vs_lookupE)
  apply (erule rtranclE)
   apply simp
  apply (clarsimp dest!: vs_lookup1D)
  apply (erule rtranclE)
   defer
   apply (drule vs_lookup1_trans_is_append')
   apply (clarsimp dest!: vs_lookup1D)
  apply (clarsimp dest!: vs_lookup1D)
  apply (drule spec, drule mp, rule exI,
         rule vs_lookupI[unfolded vs_asid_refs_def])
    apply (rule image_eqI[OF refl])
    apply (erule graph_ofI)
   apply clarsimp
   apply (rule rtrancl.intros(1))
  apply (clarsimp simp: vs_refs_def graph_of_def
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  apply (drule bspec, erule ranI)
  apply clarsimp
  apply (drule ucast_up_inj, simp)
  apply (simp add: find_pd_for_asid_def bind_assoc
                   word_neq_0_conv[symmetric] liftE_bindE)
  apply (simp add: exec_gets liftE_bindE bind_assoc
                   get_asid_pool_def get_object_def)
  apply (simp add: mask_asid_low_bits_ucast_ucast)
  apply (drule ucast_up_inj, simp)
  apply (clarsimp simp: returnOk_def get_pde_def
                        get_pd_def get_object_def
                        bind_assoc)
  apply (frule(1) pspace_alignedD[where p=pd])
  apply (simp add: pdBits_def pageBits_def)
  done

lemma find_pd_for_asid_assert_eq:
  "\<lbrakk> vspace_at_asid asid pd s; valid_vspace_objs s;
         asid \<noteq> 0; pspace_aligned s \<rbrakk>
    \<Longrightarrow> find_pd_for_asid_assert asid s = return pd s"
  apply (drule(3) find_pd_for_asid_eq_helper)
  apply (simp add: find_pd_for_asid_assert_def
                   catch_def bind_assoc)
  apply (clarsimp simp: returnOk_def obj_at_def
                        a_type_def
                  cong: bind_apply_cong)
  apply (clarsimp split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits if_split_asm)
  apply (simp add: get_pde_def get_pd_def get_object_def
                   bind_assoc is_aligned_neg_mask_eq
                   pd_bits_def pdBits_def)
  apply (simp add: exec_gets)
  done

lemma find_pd_for_asid_valids:
  "\<lbrace> vspace_at_asid asid pd and valid_vspace_objs
         and pspace_aligned and K (asid \<noteq> 0) \<rbrace>
     find_pd_for_asid asid \<lbrace>\<lambda>rv s. pde_at rv s\<rbrace>,-"
  "\<lbrace> vspace_at_asid asid pd and valid_vspace_objs
         and pspace_aligned and K (asid \<noteq> 0)
         and K (is_aligned pd pdBits \<longrightarrow> P pd) \<rbrace>
     find_pd_for_asid asid \<lbrace>\<lambda>rv s. P rv\<rbrace>,-"
  "\<lbrace> vspace_at_asid asid pd and valid_vspace_objs
         and pspace_aligned and K (asid \<noteq> 0)
         and pd_at_uniq asid pd \<rbrace>
     find_pd_for_asid asid \<lbrace>\<lambda>rv s. pd_at_uniq asid rv s\<rbrace>,-"
  "\<lbrace> vspace_at_asid asid pd and valid_vspace_objs
         and pspace_aligned and K (asid \<noteq> 0) \<rbrace>
     find_pd_for_asid asid -,\<lbrace>\<bottom>\<bottom>\<rbrace>"
  apply (simp_all add: validE_def validE_R_def validE_E_def
                       valid_def split: sum.split)
  apply (auto simp: returnOk_def return_def
                    pde_at_def pd_bits_def pdBits_def
                    pageBits_def is_aligned_neg_mask_eq
             dest!: find_pd_for_asid_eq_helper
             elim!: is_aligned_weaken)
  done


lemma asidBits_asid_bits[simp]:
  "asidBits = asid_bits"
  by (simp add: asid_bits_def asidBits_def
                asidHighBits_def asid_low_bits_def)

lemma findPDForASIDAssert_corres:
  "corres (\<lambda>rv rv'. rv = pd \<and> rv' = pd)
           (K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits)
                 and pspace_aligned and pspace_distinct
                 and valid_vspace_objs and valid_asid_map
                 and vspace_at_asid asid pd and pd_at_uniq asid pd)
           (pspace_aligned' and pspace_distinct' and no_0_obj')
       (find_pd_for_asid_assert asid)
       (findPDForASIDAssert asid)"
  apply (simp add: find_pd_for_asid_assert_def const_def
                   findPDForASIDAssert_def liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_split_catch[OF find_pd_for_asid_corres'[where pd=pd]])
         apply (rule_tac P="\<bottom>" and P'="\<top>" in corres_inst)
         apply (simp add: corres_fail)
        apply (wp find_pd_for_asid_valids[where pd=pd])+
      apply (rule_tac F="is_aligned pda pdBits
                              \<and> pda = pd" in corres_gen_asm)
      apply (clarsimp simp add: is_aligned_mask[symmetric])
      apply (rule_tac P="pde_at pd and pd_at_uniq asid pd
                            and pspace_aligned and pspace_distinct
                            and vspace_at_asid asid pd and valid_asid_map"
                 and P'="pspace_aligned' and pspace_distinct'"
                 in stronger_corres_guard_imp)
        apply (rule corres_symb_exec_l[where P="pde_at pd and pd_at_uniq asid pd
                                                and valid_asid_map and vspace_at_asid asid pd"])
           apply (rule corres_symb_exec_r[where P'="page_directory_at' pd"])
              apply (simp add: checkPDUniqueToASID_def ran_option_map
                               checkPDASIDMapMembership_def)
              apply (rule_tac P'="pd_at_uniq asid pd" in corres_stateAssert_implied)
               apply (simp add: gets_def bind_assoc[symmetric]
                                stateAssert_def[symmetric, where L="[]"])
               apply (rule_tac P'="valid_asid_map and vspace_at_asid asid pd"
                                in corres_stateAssert_implied)
                apply (rule corres_trivial, simp)
               apply (clarsimp simp: state_relation_def arch_state_relation_def
                                     valid_asid_map_def
                              split: option.split)
               apply (drule bspec, erule graph_ofI)
               apply clarsimp
               apply (drule(1) pd_at_asid_unique2)
               apply simp
              apply (clarsimp simp: state_relation_def arch_state_relation_def
                                    pd_at_uniq_def ran_option_map)
             apply wp+
           apply (simp add: checkPDAt_def stateAssert_def)
           apply (rule no_fail_pre, wp)
           apply simp
          apply (clarsimp simp: pde_at_def obj_at_def a_type_def)
          apply (clarsimp split: Structures_A.kernel_object.splits
                                 arch_kernel_obj.splits if_split_asm)
          apply (simp add: get_pde_def exs_valid_def bind_def return_def
                           get_pd_def get_object_def simpler_gets_def)
         apply wp
         apply simp
        apply (simp add: get_pde_def get_pd_def)
        apply (rule no_fail_pre)
         apply (wp get_object_wp | wpc)+
        apply (clarsimp simp: pde_at_def obj_at_def a_type_def)
        apply (clarsimp split: Structures_A.kernel_object.splits
                               arch_kernel_obj.splits if_split_asm)
       apply simp
      apply (clarsimp simp: state_relation_def)
      apply (erule(3) pspace_relation_pd)
      apply (simp add: pde_at_def pd_bits_def pdBits_def)
     apply (wp find_pd_for_asid_valids[where pd=pd])+
   apply (clarsimp simp: word_neq_0_conv)
  apply simp
  done

lemma findPDForASIDAssert_known_corres:
  "corres r P P' f (g pd) \<Longrightarrow>
  corres r (vspace_at_asid asid pd and pd_at_uniq asid pd
               and valid_vspace_objs and valid_asid_map
               and pspace_aligned and pspace_distinct
               and K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits) and P)
           (P' and pspace_aligned' and pspace_distinct' and no_0_obj')
       f (findPDForASIDAssert asid >>= g)"
  apply (subst return_bind[symmetric])
  apply (subst corres_cong [OF refl refl _ refl refl])
   apply (rule bind_apply_cong [OF _ refl])
   apply clarsimp
   apply (erule(3) find_pd_for_asid_assert_eq[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF findPDForASIDAssert_corres[where pd=pd]])
      apply simp
     apply wp+
   apply clarsimp
  apply simp
  done

lemma loadHWASID_corres:
  "corres (=)
          (valid_vspace_objs and pspace_distinct
                 and pspace_aligned and valid_asid_map
                 and vspace_at_asid a pd
                 and (\<lambda>s. \<forall>pd. vspace_at_asid a pd s \<longrightarrow> pd_at_uniq a pd s)
                 and K (a \<noteq> 0 \<and> a \<le> mask asid_bits))
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (load_hw_asid a) (loadHWASID a)"
  apply (simp add: load_hw_asid_def loadHWASID_def)
  apply (rule_tac r'="(=)" in corres_underlying_split [OF _ _ gets_sp gets_sp])
   apply (clarsimp simp: state_relation_def arch_state_relation_def)
  apply (case_tac "rv' a")
   apply simp
   apply (rule corres_guard_imp)
     apply (rule_tac pd=pd in findPDForASIDAssert_known_corres)
     apply (rule corres_trivial, simp)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (rule corres_guard_imp)
    apply (rule_tac pd=b in findPDForASIDAssert_known_corres)
    apply (rule corres_trivial, simp)
   apply (clarsimp simp: valid_arch_state_def valid_asid_map_def)
   apply (drule subsetD, erule domI)
   apply (drule bspec, erule graph_ofI)
   apply clarsimp
  apply simp
  done

crunch inv[wp]: loadHWASID "P"
  (wp: crunch_wps)

lemma storeHWASID_corres:
  "corres dc
          (vspace_at_asid a pd and pd_at_uniq a pd
                  and valid_vspace_objs and pspace_distinct
                  and pspace_aligned and K (a \<noteq> 0 \<and> a \<le> mask asid_bits)
                  and valid_asid_map)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (store_hw_asid a h) (storeHWASID a h)"
  apply (simp add: store_hw_asid_def storeHWASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF findPDForASIDAssert_corres[where pd=pd]])
      apply (rule corres_split_eqr)
         apply (rule corres_trivial)
         apply (clarsimp simp: state_relation_def arch_state_relation_def)
        apply (rule corres_split)
           apply (rule corres_trivial, rule corres_modify)
           apply (clarsimp simp: state_relation_def)
           apply (simp add: arch_state_relation_def)
           apply (rule ext)
           apply simp
          apply (rule corres_split_eqr)
             apply (rule corres_trivial)
             apply (clarsimp simp: state_relation_def arch_state_relation_def)
            apply (rule corres_trivial, rule corres_modify)
            apply (clarsimp simp: state_relation_def arch_state_relation_def)
            apply (rule ext)
            apply simp
           apply (wp | simp)+
  done

lemma invalidateASID_corres:
  "corres dc
          (valid_asid_map and valid_vspace_objs
               and pspace_aligned and pspace_distinct
               and vspace_at_asid a pd and pd_at_uniq a pd
               and K (a \<noteq> 0 \<and> a \<le> mask asid_bits))
          (pspace_aligned' and pspace_distinct' and no_0_obj')
     (invalidate_asid a) (invalidateASID a)"
  (is "corres dc ?P ?P' ?f ?f'")
  apply (simp add: invalidate_asid_def invalidateASID_def)
  apply (rule corres_guard_imp)
    apply (rule_tac pd=pd in findPDForASIDAssert_known_corres)
    apply (rule_tac P="?P" and P'="?P'" in corres_inst)
    apply (rule_tac r'="(=)" in corres_underlying_split [OF _ _ gets_sp gets_sp])
     apply (clarsimp simp: state_relation_def arch_state_relation_def)
    apply (rule corres_modify)
    apply (simp add: state_relation_def arch_state_relation_def
                     fun_upd_def)
   apply simp
  apply simp
  done

lemma invalidate_asid_ext_corres:
  "corres dc
          (\<lambda>s. \<exists>pd. valid_asid_map s \<and> valid_vspace_objs s
               \<and> pspace_aligned s \<and> pspace_distinct s
               \<and> vspace_at_asid a pd s \<and> pd_at_uniq a pd s
               \<and> a \<noteq> 0 \<and> a \<le> mask asid_bits)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
     (invalidate_asid a) (invalidateASID a)"
  apply (insert invalidateASID_corres)
  apply (clarsimp simp: corres_underlying_def)
  apply fastforce
  done

lemma invalidateHWASIDEntry_corres:
  "corres dc \<top> \<top> (invalidate_hw_asid_entry a) (invalidateHWASIDEntry a)"
  apply (simp add: invalidate_hw_asid_entry_def invalidateHWASIDEntry_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule corres_trivial)
       apply (clarsimp simp: state_relation_def arch_state_relation_def)
      apply (rule corres_trivial, rule corres_modify)
      apply (clarsimp simp: state_relation_def arch_state_relation_def)
      apply (rule ext)
      apply (wp | clarsimp)+
  done

lemma findFreeHWASID_corres:
  "corres (=)
          (valid_asid_map and valid_vspace_objs
              and pspace_aligned and pspace_distinct
              and (unique_table_refs o caps_of_state)
              and valid_vs_lookup and valid_arch_state
              and valid_global_objs)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          find_free_hw_asid findFreeHWASID"
  apply (simp add: find_free_hw_asid_def findFreeHWASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF corres_trivial])
       apply (clarsimp simp: arch_state_relation_def state_relation_def)
      apply (rule corres_split_eqr[OF corres_trivial])
         apply (clarsimp simp: arch_state_relation_def state_relation_def)
        apply (subgoal_tac "take (length [minBound .e. maxBound :: hardware_asid])
                              ([next_asid .e. maxBound] @ [minBound .e. next_asid])
                              = [next_asid .e. maxBound] @ init [minBound .e. next_asid]")
         apply (cut_tac option="find (\<lambda>a. hw_asid_table a = None)
           ([next_asid .e. maxBound] @ init [minBound .e. next_asid])"
                   in option.nchotomy[rule_format])
         apply (erule corres_disj_division)
          apply (clarsimp split del: if_split)
          apply (rule corres_split[OF invalidate_asid_ext_corres])
            apply (rule corres_underlying_split [where r'=dc])
               apply (rule corres_trivial, rule corres_machine_op)
               apply (rule corres_no_failI)
                apply (rule no_fail_invalidateLocalTLB_ASID)
               apply fastforce
              apply (rule corres_split)
                 apply (rule invalidateHWASIDEntry_corres)
                apply (rule corres_split)
                   apply (rule corres_trivial)
                   apply (rule corres_modify)
                   apply (simp add: minBound_word maxBound_word
                                    state_relation_def arch_state_relation_def)
                  apply (rule corres_trivial)
                  apply simp
                 apply (wp | simp split del: if_split)+
         apply (rule corres_trivial, clarsimp)
        apply (cut_tac x=next_asid in leq_maxBound)
        apply (simp only: word_le_nat_alt)
        apply (simp add: init_def upto_enum_word
                         minBound_word
                    del: upt.simps)
       apply wp+
   apply (clarsimp dest!: findNoneD)
   apply (drule bspec, rule UnI1, simp, rule order_refl)
   apply (clarsimp simp: valid_arch_state_def)
   apply (frule(1) is_inv_SomeD)
   apply (clarsimp simp: valid_asid_map_def)
   apply (frule bspec, erule graph_ofI, clarsimp)
   apply (frule pd_at_asid_uniq, simp_all add: valid_asid_map_def valid_arch_state_def)[1]
    apply (drule subsetD, erule domI)
    apply simp
   apply fastforce
  apply clarsimp
  done

crunch aligned'[wp]: findFreeHWASID "pspace_aligned'"
  (simp: crunch_simps)

crunch distinct'[wp]: findFreeHWASID "pspace_distinct'"
  (simp: crunch_simps)

crunch no_0_obj'[wp]: getHWASID "no_0_obj'"

lemma getHWASID_corres:
  "corres (=)
          (vspace_at_asid a pd and K (a \<noteq> 0 \<and> a \<le> mask asid_bits)
           and unique_table_refs o caps_of_state
           and valid_vs_lookup
           and valid_asid_map and valid_vspace_objs
           and pspace_aligned and pspace_distinct
           and valid_arch_state)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (get_hw_asid a) (getHWASID a)"
  apply (simp add: get_hw_asid_def getHWASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF loadHWASID_corres[where pd=pd]])
      apply (case_tac maybe_hw_asid, simp_all)[1]
      apply (rule corres_split_eqr[OF findFreeHWASID_corres])
         apply (rule corres_split[OF storeHWASID_corres[where pd=pd]])
           apply (rule corres_trivial, simp)
          apply (wp load_hw_asid_wp | simp)+
   apply (simp add: pd_at_asid_uniq valid_global_objs_def)
  apply simp
  done

lemma armv_contextSwitch_corres:
  "corres dc
          (vspace_at_asid a pd and K (a \<noteq> 0 \<and> a \<le> mask asid_bits)
           and unique_table_refs o caps_of_state
           and valid_vs_lookup
           and valid_asid_map and valid_vspace_objs
           and pspace_aligned and pspace_distinct
           and valid_arch_state)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (arm_context_switch pd a) (armv_contextSwitch pd a)"
  apply (simp add: arm_context_switch_def armv_contextSwitch_def armv_contextSwitch_HWASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF getHWASID_corres[where pd=pd]])
      apply (rule corres_machine_op)
      apply (rule corres_rel_imp)
       apply (rule corres_underlying_trivial)
       apply (rule no_fail_pre)
        apply wpsimp+
  done

(* setObject for VCPU invariant preservation *)

lemma setObject_vcpu_cur_domain[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ct[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_it[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_sched[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_L1[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_L2[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ksInt[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ksArch[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_gs[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_maschine_state[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ksDomSchedule[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ksDomScheduleIdx[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_gsUntypedZeroRanges[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>\<lambda>s. P (gsUntypedZeroRanges s)\<rbrace>"
    by (wpsimp wp: updateObject_default_inv simp: setObject_def)

lemma setObject_vcpu_ctes_of[wp]:
  "\<lbrace> \<lambda>s. P (ctes_of s)\<rbrace> setObject p (t :: vcpu) \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  apply (rule ctes_of_from_cte_wp_at[where Q="\<top>", simplified])
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad
                          projectKO_opts_defs projectKOs)
   apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad
                         projectKOs projectKO_opts_defs)
  apply simp
  done

lemma setObject_vcpu_untyped_ranges_zero'[wp]:
  "setObject ptr (vcpu::vcpu) \<lbrace>untyped_ranges_zero'\<rbrace>"
    by (rule hoare_lift_Pf[where f=cteCaps_of]; wp cteCaps_of_ctes_of_lift)

lemma setVCPU_if_live[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> (live' (injectKOS vcpu) \<longrightarrow> ex_nonz_cap_to' v s)\<rbrace>
   setObject v (vcpu::vcpu) \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp wp: setObject_iflive' [where P=\<top>]
         | simp add: objBits_simps archObjSize_def vcpu_bits_def pageBits_def)+
    apply (clarsimp simp: updateObject_default_def in_monad projectKOs)
   apply (clarsimp simp: updateObject_default_def in_monad projectKOs bind_def)
  apply simp
  done

lemma setVCPU_if_unsafe[wp]:
  "setObject v (vcpu::vcpu) \<lbrace>if_unsafe_then_cap'\<rbrace>"
  apply (wp setObject_ifunsafe')
     apply (clarsimp simp: updateObject_default_def in_monad projectKOs)
    apply (clarsimp simp: updateObject_default_def in_monad projectKOs bind_def)
   apply wp
  apply simp
  done

lemma projectKO_opt_no_vcpu[simp]:
  "projectKO_opt (KOArch (KOVCPU v)) = (None::'a::no_vcpu option)"
    by (rule ccontr) (simp add: project_koType not_vcpu[symmetric])

lemma setObject_vcpu_obj_at'_no_vcpu[wp]:
  "setObject ptr (v::vcpu) \<lbrace>\<lambda>s. P (obj_at' (P'::'a::no_vcpu \<Rightarrow> bool) t s)\<rbrace>"
  apply (wp setObject_ko_wp_at[where
        P'="\<lambda>ko. \<exists>obj. projectKO_opt ko = Some obj \<and> P' (obj::'a::no_vcpu)" for P',
        folded obj_at'_real_def])
     apply (clarsimp simp: updateObject_default_def in_monad not_vcpu[symmetric])
    apply (simp add: objBits_simps archObjSize_def)
   apply (simp add: vcpu_bits_def pageBits_def)
  apply (clarsimp split del: if_split)
  apply (erule rsubst[where P=P])
  apply normalise_obj_at'
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKOs)
  done

lemmas setVCPU_pred_tcb'[wp] =
  setObject_vcpu_obj_at'_no_vcpu
      [where P'="\<lambda>ko. P (proj (tcb_to_itcb' ko))" for P proj, folded pred_tcb_at'_def]

lemma setVCPU_valid_idle'[wp]:
  "setObject v (vcpu::vcpu) \<lbrace>valid_idle'\<rbrace>"
    unfolding valid_idle'_def by (rule hoare_lift_Pf[where f=ksIdleThread]; wp)

lemma setVCPU_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject p (v::vcpu) \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv | simp)+

lemma setVCPU_ct_not_inQ[wp]:
  "setObject v (vcpu::vcpu) \<lbrace>ct_not_inQ\<rbrace>"
  apply (wp ct_not_inQ_lift)
   apply (rule hoare_lift_Pf[where f=ksCurThread]; wp)
  apply assumption
  done

lemma handleVMFault_corres:
  "corres (fr \<oplus> dc) (tcb_at thread and pspace_aligned and pspace_distinct) \<top>
     (handle_vm_fault thread fault) (handleVMFault thread fault)"
  apply (simp add: ARM_HYP_H.handleVMFault_def)
  apply (cases fault)
   apply simp
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE, simp,
            rule corres_machine_op [where r="(=)"],
            rule corres_Id refl, rule refl, simp, simp)+
           apply (rule corres_trivial)
           apply (simp add: arch_fault_map_def)
          apply wpsimp+
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE,simp)
       apply (rule asUser_corres')
       apply (rule corres_no_failI [where R="(=)"])
        apply (rule no_fail_getRestartPC)
       apply fastforce
      apply (rule corres_splitEE,simp,
             rule corres_machine_op [where r="(=)"],
             rule corres_Id refl, rule refl, simp, simp)+
          apply (rule corres_trivial, simp add: arch_fault_map_def)
         apply wpsimp+
  done

lemma flushSpace_corres:
  "corres dc
          (K (asid \<le> mask asid_bits \<and> asid \<noteq> 0)
           and valid_asid_map and valid_vspace_objs
           and pspace_aligned and pspace_distinct
           and unique_table_refs o caps_of_state
           and valid_vs_lookup
           and valid_arch_state and vspace_at_asid asid pd)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (flush_space asid) (flushSpace asid)"
  apply (simp add: flushSpace_def flush_space_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule loadHWASID_corres[where pd=pd])
      apply (rule corres_split[where R="\<lambda>_. \<top>" and R'="\<lambda>_. \<top>"])
         apply (rule corres_machine_op [where r=dc])
         apply (rule corres_Id, rule refl, simp)
         apply (rule no_fail_cleanCaches_PoU)
        apply (case_tac maybe_hw_asid)
         apply simp
        apply clarsimp
        apply (rule corres_machine_op)
        apply (rule corres_Id, rule refl, simp)
        apply (rule no_fail_invalidateLocalTLB_ASID)
       apply wp+
   apply clarsimp
   apply (simp add: pd_at_asid_uniq)
  apply simp
  done

lemma invalidateTLBByASID_corres:
  "corres dc
          (K (asid \<le> mask asid_bits \<and> asid \<noteq> 0)
           and valid_asid_map and valid_vspace_objs
           and pspace_aligned and pspace_distinct
           and unique_table_refs o caps_of_state
           and valid_vs_lookup
           and valid_arch_state and vspace_at_asid asid pd)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (invalidate_tlb_by_asid asid) (invalidateTLBByASID asid)"
  apply (simp add: invalidate_tlb_by_asid_def invalidateTLBByASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[where R="\<lambda>_. \<top>" and R'="\<lambda>_. \<top>"])
       apply (rule loadHWASID_corres[where pd=pd])
      apply (case_tac maybe_hw_asid)
       apply simp
      apply clarsimp
      apply (rule corres_machine_op)
      apply (rule corres_Id, rule refl, simp)
      apply (rule no_fail_invalidateLocalTLB_ASID)
     apply wp+
   apply clarsimp
   apply (simp add: pd_at_asid_uniq)
  apply simp
  done

lemma invalidate_tlb_by_asid_corres_ex:
  "corres dc
          (\<lambda>s. asid \<le> mask asid_bits \<and> asid \<noteq> 0
            \<and> valid_asid_map s \<and> valid_vspace_objs s
            \<and> pspace_aligned s \<and> pspace_distinct s
            \<and> unique_table_refs (caps_of_state s)
            \<and> valid_global_objs s \<and> valid_vs_lookup s
            \<and> valid_arch_state s \<and> (\<exists>pd. vspace_at_asid asid pd s))
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (invalidate_tlb_by_asid asid) (invalidateTLBByASID asid)"
  apply (rule corres_name_pre, clarsimp)
  apply (rule corres_guard_imp)
    apply (rule_tac pd=pd in invalidateTLBByASID_corres)
   apply simp+
  done

lemma state_relation_asid_map:
  "(s, s') \<in> state_relation \<Longrightarrow> armKSASIDMap (ksArchState s') = arm_asid_map (arch_state s)"
  by (simp add: state_relation_def arch_state_relation_def)

lemma find_pd_for_asid_pd_at_asid_again:
  "\<lbrace>\<lambda>s. (\<forall>pd. vspace_at_asid asid pd s \<longrightarrow> P pd s)
       \<and> (\<forall>ex. (\<forall>pd. \<not> vspace_at_asid asid pd s) \<longrightarrow> Q ex s)
       \<and> valid_vspace_objs s \<and> pspace_aligned s \<and> asid \<noteq> 0\<rbrace>
      find_pd_for_asid asid
   \<lbrace>P\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (unfold validE_def, rule hoare_name_pre_state, fold validE_def)
  apply (case_tac "\<exists>pd. vspace_at_asid asid pd s")
   apply clarsimp
   apply (rule_tac Q="\<lambda>rv s'. s' = s \<and> rv = pd" and E="\<bottom>\<bottom>" in hoare_post_impErr)
     apply (rule hoare_pre, wp find_pd_for_asid_valids)
     apply fastforce
    apply simp+
  apply (rule_tac Q="\<lambda>rv s'. s' = s \<and> vspace_at_asid asid rv s'"
              and E="\<lambda>rv s'. s' = s" in hoare_post_impErr)
    apply (rule hoare_pre, wp)
    apply clarsimp+
  done

(* TODO: maybe move? *)
lemma mapM_mapM_x: "do y \<leftarrow> mapM f l;
                g
             od =
             do mapM_x f l;
                g
             od"
  by (simp add: mapM_x_mapM)

(* TODO: move *)
lemma getObject_ko_at_vcpu [wp]:
  "\<lbrace>\<top>\<rbrace> getObject p \<lbrace>\<lambda>rv::vcpu. ko_at' rv p\<rbrace>"
  by (rule getObject_ko_at | simp add: objBits_simps archObjSize_def vcpu_bits_def pageBits_def)+

lemma corres_gets_gicvcpu_numlistregs:
  "corres (=) \<top> \<top> (gets (arm_gicvcpu_numlistregs \<circ> arch_state))
                      (gets (armKSGICVCPUNumListRegs \<circ> ksArchState))"
  by (simp add: state_relation_def arch_state_relation_def)

lemmas corres_split_forward = corres_underlying_split[rule_format, where Q="\<lambda>_. P" and P=P  and Q'="\<lambda>_. P'" and P'=P' for P P']

lemma setObject_VCPU_corres:
  "vcpu_relation vcpuObj vcpuObj'
   \<Longrightarrow>  corres dc (vcpu_at  vcpu)
                  (vcpu_at' vcpu)
                  (set_vcpu vcpu vcpuObj)
                  (setObject vcpu vcpuObj')"
  apply (simp add: set_vcpu_def)
  apply (rule corres_guard_imp)
    apply (rule setObject_other_corres [where P="\<lambda>ko::vcpu. True"], simp)
         apply (clarsimp simp: obj_at'_def projectKOs)
         apply (erule map_to_ctes_upd_other, simp, simp)
        apply (simp add: a_type_def is_other_obj_relation_type_def)
       apply (simp add: objBits_simps archObjSize_def)
      apply simp
     apply (simp add: objBits_simps archObjSize_def vcpu_bits_def pageBits_def)
    apply (simp add: other_obj_relation_def asid_pool_relation_def)
   apply (clarsimp simp: typ_at_to_obj_at'[symmetric] obj_at_def exs_valid_def
                         assert_def a_type_def return_def fail_def)
   apply (fastforce split: Structures_A.kernel_object.split_asm if_split_asm)
  apply (simp add: typ_at_to_obj_at_arches)
  done

crunches
  vgicUpdate, vgicUpdateLR, vcpuWriteReg, vcpuReadReg, vcpuRestoreRegRange, vcpuSaveRegRange,
  vcpuSave
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  and no_0_obj'[wp]: no_0_obj'
  and vcpu_at'[wp]: "\<lambda>s. P (vcpu_at' p s)"
  (wp: crunch_wps ignore_del: setObject)

lemma vcpuUpdate_corres[corres]:
  "\<forall>v1 v2. vcpu_relation v1 v2 \<longrightarrow> vcpu_relation (f v1) (f' v2) \<Longrightarrow>
    corres dc (vcpu_at v) (vcpu_at' v)
           (vcpu_update v f) (vcpuUpdate v f')"
  by (corresKsimp corres: getObject_vcpu_corres setObject_VCPU_corres
                 simp: vcpu_update_def vcpuUpdate_def vcpu_relation_def)

lemma vgicUpdate_corres[corres]:
  "\<forall>vgic vgic'. vgic_map vgic = vgic' \<longrightarrow> vgic_map (f vgic) = (f' vgic')
   \<Longrightarrow> corres dc (vcpu_at v) (vcpu_at' v) (vgic_update v f) (vgicUpdate v f')"
  by (corresKsimp simp: vgic_update_def vgicUpdate_def vcpu_relation_def)

lemma vgicUpdateLR_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v)
          (vgic_update_lr v idx val) (vgicUpdateLR v idx val)"
  by (corresKsimp simp: vgic_update_lr_def vgicUpdateLR_def vgic_map_def)

lemma vcpuReadReg_corres[corres]:
  "corres (=) (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_read_reg v r) (vcpuReadReg v r)"
  apply (simp add: vcpu_read_reg_def vcpuReadReg_def)
  apply (rule corres_guard_imp)
    apply (rule corres_assert_gen_asm2)
    apply (rule corres_underlying_split[OF getObject_vcpu_corres])
      apply (wpsimp simp: vcpu_relation_def)+
  done

lemma vcpuWriteReg_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_write_reg v r val) (vcpuWriteReg v r val)"
  apply (simp add: vcpu_write_reg_def vcpuWriteReg_def)
  apply (rule corres_guard_imp)
    apply (rule corres_assert_gen_asm2)
    apply (rule vcpuUpdate_corres)
    apply (fastforce simp: vcpu_relation_def)+
  done

lemma vcpuSaveReg_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_save_reg v r) (vcpuSaveReg v r)"
  apply (clarsimp simp: vcpu_save_reg_def vcpuSaveReg_def)
  apply (rule corres_guard_imp)
    apply (rule corres_assert_gen_asm2)
    apply (rule corres_split[OF corres_machine_op[where r="(=)"]])
       apply (rule corres_Id; simp)
      apply (rule vcpuUpdate_corres, fastforce simp: vcpu_relation_def vgic_map_def)
     apply wpsimp+
  done

lemma vcpuSaveRegRange_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_save_reg_range v rf rt) (vcpuSaveRegRange v rf rt)"
  apply (clarsimp simp: vcpu_save_reg_range_def vcpuSaveRegRange_def)
  apply (rule corres_mapM_x[OF _ _ _ _ subset_refl])
     apply (wpsimp wp: vcpuSaveReg_corres)+
  done

lemma vcpuRestoreReg_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_restore_reg v r) (vcpuRestoreReg v r)"
  apply (clarsimp simp: vcpu_restore_reg_def vcpuRestoreReg_def)
  apply (rule corres_guard_imp)
    apply (rule corres_assert_gen_asm2)
    apply (rule corres_split[OF getObject_vcpu_corres])
      apply (rule corres_machine_op)
      apply (rule corres_Id)
        apply (fastforce simp: vcpu_relation_def)
       apply (wpsimp wp: corres_Id simp: vcpu_relation_def vgic_map_def)+
  done

lemma vcpuRestoreRegRange_corres[corres]:
  "corres dc (vcpu_at v) (vcpu_at' v and no_0_obj')
          (vcpu_restore_reg_range v rf rt) (vcpuRestoreRegRange v rf rt)"
  apply (clarsimp simp: vcpu_restore_reg_range_def vcpuRestoreRegRange_def)
  apply (rule corres_mapM_x[OF _ _ _ _ subset_refl])
     apply (wpsimp wp: vcpuRestoreReg_corres)+
  done

lemma saveVirtTimer_corres[corres]:
  "corres dc (vcpu_at vcpu_ptr) (vcpu_at' vcpu_ptr and no_0_obj')
             (save_virt_timer vcpu_ptr) (saveVirtTimer vcpu_ptr)"
  unfolding save_virt_timer_def saveVirtTimer_def
  apply (rule corres_guard_imp)
    apply (rule corres_split_dc[OF vcpuSaveReg_corres], simp)
      apply (rule corres_split_dc[OF corres_machine_op], (rule corres_Id; simp))
        apply (rule corres_split_eqr[OF corres_machine_op], (rule corres_Id; simp))+
            apply (rule corres_split_dc[OF vcpuWriteReg_corres], simp)+
                    apply (rule corres_split_eqr[OF corres_machine_op])
                       apply (rule corres_Id; simp)
                      apply (fold dc_def)
                      apply (rule vcpuUpdate_corres)
                      apply (simp add: vcpu_relation_def)
                     apply wpsimp+
  done

lemma isIRQActive_corres:
  "corres (=) \<top> \<top> (is_irq_active irqVTimerEvent) (isIRQActive irqVTimerEvent)"
  apply (clarsimp simp: isIRQActive_def getIRQState_def is_irq_active_def get_irq_state_def)
  apply (clarsimp simp: is_irq_active_def isIRQActive_def
                        get_irq_state_def irq_state_relation_def
                        getIRQState_def getInterruptState_def
                        state_relation_def interrupt_state_relation_def)
  apply (fastforce split: irq_state.splits irqstate.splits)
  done

lemma restoreVirtTimer_corres[corres]:
  "corres dc (vcpu_at vcpu_ptr) (vcpu_at' vcpu_ptr and no_0_obj')
             (restore_virt_timer vcpu_ptr) (restoreVirtTimer vcpu_ptr)"
  unfolding restore_virt_timer_def restoreVirtTimer_def IRQ_def
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF vcpuReadReg_corres], simp)
      apply (rule corres_split_eqr[OF vcpuReadReg_corres])
        apply (rule corres_split_eqr[OF corres_machine_op], (rule corres_Id; simp))+
            apply (rule corres_split[OF getObject_vcpu_corres])
              apply (rule corres_split_eqr[OF vcpuReadReg_corres])
                apply (rule corres_split_eqr[OF vcpuReadReg_corres])
                  apply (clarsimp simp: vcpu_relation_def)
                  apply (rule corres_split_dc[OF vcpuWriteReg_corres])+
                      apply (rule corres_split_dc[OF corres_machine_op])
                         apply (rule corres_Id; simp)
                        apply (rule corres_split_eqr[OF isIRQActive_corres])
                          apply (rule corres_split_dc[OF corres_when], simp)
                             apply (simp add: irq_vppi_event_index_def irqVPPIEventIndex_def IRQ_def)
                             apply (rule corres_machine_op, simp)
                             apply (rule corres_Id; wpsimp)
                            apply (rule vcpuRestoreReg_corres)
                           apply (wpsimp simp: if_apply_def2 isIRQActive_def)+
  done

lemma vcpuSave_corres:
  "corres dc (vcpu_at (fst cvcpu)) (vcpu_at' (fst cvcpu) and no_0_obj')
             (vcpu_save (Some cvcpu)) (vcpuSave (Some cvcpu))"
  supply no_fail_isb[wp] no_fail_dsb[wp]
  apply (clarsimp simp add: vcpu_save_def vcpuSave_def armvVCPUSave_def)
  apply (cases cvcpu, clarsimp, rename_tac v active)
  apply (rule corres_guard_imp)
    apply (rule corres_split_dc[OF corres_machine_op])
       apply (rule corres_Id; wpsimp)
      apply (rule corres_split[where r'=dc])
         apply (rule corres_when, simp)
         apply (rule corres_split[OF vcpuSaveReg_corres])
           apply (rule corres_split_eqr[OF corres_machine_op])
              apply (rule corres_Id; wpsimp)
             apply (rule corres_split[OF vgicUpdate_corres])
                apply (clarsimp simp: vgic_map_def)
               apply (rule saveVirtTimer_corres)
              apply wpsimp+
          apply (rule corres_split_eqr[OF corres_machine_op])
           apply (rule corres_Id; wpsimp)
          apply (rule corres_split[OF vgicUpdate_corres])
             apply (clarsimp simp: vgic_map_def)
            apply (rule corres_split_eqr[OF corres_machine_op])
               apply (rule corres_Id; wpsimp)
              apply (rule corres_split[OF vgicUpdate_corres])
                 apply (clarsimp simp: vgic_map_def)
                apply (rule corres_split_eqr)
                   apply (rule corres_trivial)
                   apply (fastforce simp add: state_relation_def arch_state_relation_def)
                  apply (simp add: mapM_discarded)
                  apply (rule corres_split[OF corres_mapM_x[OF _ _ _ _ subset_refl]])
                        apply (rule corres_split_eqr[OF corres_machine_op])
                           apply (rule corres_Id; wpsimp)
                          apply (clarsimp, fold dc_def)
                          apply (rule vgicUpdateLR_corres)
                         apply wpsimp+
                    apply (rule corres_split[OF vcpuSaveRegRange_corres])
                      apply (rule corres_machine_op)
                      apply (rule corres_Id; wpsimp)
                     apply (wpsimp wp: mapM_x_wp_inv hoare_vcg_imp_lift'
                                 simp: if_apply_def2)+
  done

lemma vcpuDisable_corres:
  "corres dc (\<lambda>s. (\<exists>v. vcpuopt = Some v) \<longrightarrow> vcpu_at  (the vcpuopt) s)
             (\<lambda>s. ((\<exists>v. vcpuopt = Some v) \<longrightarrow> vcpu_at' (the vcpuopt) s) \<and> no_0_obj' s)
             (vcpu_disable vcpuopt)
             (vcpuDisable vcpuopt)"
  (* FIXME these should be in wp/simp sets *)
  supply no_fail_isb[wp] no_fail_dsb[wp] empty_fail_isb[wp,simp] empty_fail_dsb[wp,simp]
  apply (cases vcpuopt; clarsimp simp: vcpu_disable_def vcpuDisable_def)
   (* no current VCPU *)
   subgoal
     apply (clarsimp simp: doMachineOp_bind do_machine_op_bind empty_fail_cond)
     apply (rule corres_guard_imp)
       apply (rule corres_split_dc[OF corres_machine_op]
         | rule corres_machine_op corres_Id
         | wpsimp)+
     done
  (* have current VCPU *)
   apply (rename_tac vcpu)
   apply (clarsimp simp: doMachineOp_bind do_machine_op_bind bind_assoc IRQ_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split_dc[OF corres_machine_op])
        apply (rule corres_Id; wpsimp)
       apply (rule corres_split_eqr[OF corres_machine_op])
          apply (rule corres_Id; wpsimp)
         apply (rule corres_split_dc[OF vgicUpdate_corres])
            apply (clarsimp simp: vgic_map_def)
           apply (rule corres_split_dc[OF vcpuSaveReg_corres])
             apply (rule corres_split_dc[OF corres_machine_op]
                         corres_split_dc[OF saveVirtTimer_corres]
                    | rule corres_machine_op corres_Id
                    | wpsimp)+
   done

lemma vcpuEnable_corres:
  "corres dc (vcpu_at  vcpu) (vcpu_at' vcpu and no_0_obj')
             (vcpu_enable vcpu) (vcpuEnable vcpu)"
  (* FIXME these should be in wp/simp sets *)
  supply no_fail_isb[wp] no_fail_dsb[wp] empty_fail_isb[wp,simp] empty_fail_dsb[wp,simp]
  apply (simp add: vcpu_enable_def vcpuEnable_def doMachineOp_bind do_machine_op_bind bind_assoc)
  apply (rule corres_guard_imp)
    apply (rule corres_split_dc[OF vcpuRestoreReg_corres])+
      apply (rule corres_split[OF getObject_vcpu_corres], rename_tac vcpu')
        apply (case_tac vcpu')
        apply (rule corres_split_dc[OF corres_machine_op]
               | rule corres_machine_op corres_Id restoreVirtTimer_corres
               | wpsimp simp: vcpu_relation_def vgic_map_def)+
  done

lemma vcpuRestore_corres:
  "corres dc (vcpu_at vcpu)
             (vcpu_at' vcpu and no_0_obj')
             (vcpu_restore vcpu)
             (vcpuRestore vcpu)"
  (* FIXME these should be in wp/simp sets *)
  supply no_fail_isb[wp] no_fail_dsb[wp] empty_fail_isb[wp,simp] empty_fail_dsb[wp,simp]
  apply (simp add: vcpu_restore_def vcpuRestore_def gicVCPUMaxNumLR_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_dc[OF corres_machine_op]
           | (rule corres_machine_op corres_Id; wpsimp))+
        apply (rule corres_split[OF getObject_vcpu_corres], rename_tac vcpu')
          apply (rule corres_split[OF corres_gets_gicvcpu_numlistregs])
            apply (case_tac vcpu'
                   , clarsimp simp: comp_def vcpu_relation_def vgic_map_def mapM_x_mapM
                                    uncurry_def split_def mapM_map_simp)
            apply (simp add: doMachineOp_bind do_machine_op_bind bind_assoc empty_fail_cond)
            apply (rule corres_split_dc[OF corres_machine_op])
               apply (rule corres_Id; wpsimp)
              apply (rule corres_split_dc[OF corres_machine_op])
                 apply (rule corres_Id; wpsimp)
                apply (rule corres_split)
                   apply (rule corres_machine_op, rule corres_Id; wpsimp wp: no_fail_mapM)
                  apply (rule corres_split_dc[OF vcpuRestoreRegRange_corres])
                    apply (rule vcpuEnable_corres)
                   apply wpsimp+
  done

crunches
  vcpuUpdate for vcpu_at'[wp]: "\<lambda>s. P (vcpu_at' p s)"

lemma vcpuSwitch_corres:
  assumes "vcpu' = vcpu"
  shows
  "corres dc (\<lambda>s. (vcpu \<noteq> None \<longrightarrow> vcpu_at  (the vcpu) s) \<and>
                  ((arm_current_vcpu \<circ> arch_state) s \<noteq> None
                    \<longrightarrow> vcpu_at ((fst \<circ> the \<circ> arm_current_vcpu \<circ> arch_state) s) s))
             (\<lambda>s. (vcpu' \<noteq> None \<longrightarrow> vcpu_at'  (the vcpu') s) \<and>
                  ((armHSCurVCPU \<circ> ksArchState) s \<noteq> None
                    \<longrightarrow> vcpu_at' ((fst \<circ> the \<circ> armHSCurVCPU \<circ> ksArchState) s) s) \<and>
                  no_0_obj' s)
             (vcpu_switch vcpu)
             (vcpuSwitch vcpu')"
  proof -
    have modify_current_vcpu:
      "\<And>a b. corres dc \<top> \<top> (modify (\<lambda>s. s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (a, b)\<rparr>\<rparr>))
                             (modifyArchState (armHSCurVCPU_update (\<lambda>_. Some (a, b))))"
      by (clarsimp simp add: modifyArchState_def state_relation_def arch_state_relation_def
                   intro!: corres_modify)
    have get_current_vcpu: "corres (=) \<top> \<top> (gets (arm_current_vcpu \<circ> arch_state))
                                               (gets (armHSCurVCPU \<circ> ksArchState))"
      apply clarsimp
      apply (rule_tac P = "(arm_current_vcpu (arch_state s)) = (armHSCurVCPU (ksArchState s'))"
                     in TrueE;
             simp add: state_relation_def arch_state_relation_def)
      done
    show ?thesis
      apply (simp add: vcpu_switch_def vcpuSwitch_def assms)
      apply (cases vcpu)
         apply (all \<open>simp, rule corres_underlying_split[OF  _ _ gets_sp gets_sp],
                           rule corres_guard_imp[OF get_current_vcpu TrueI TrueI],
                           rename_tac rv rv', case_tac rv ;
                           clarsimp simp add: when_def\<close>)
        apply (rule corres_machine_op[OF corres_underlying_trivial[OF no_fail_isb]] TrueI TrueI
                    vcpuDisable_corres modify_current_vcpu
                    vcpuEnable_corres
                    vcpuRestore_corres
                    vcpuSave_corres
                    hoare_post_taut conjI
                    corres_underlying_split corres_guard_imp
               | clarsimp simp add: when_def | wpsimp | assumption)+
      done
  qed

lemma aligned_distinct_relation_vcpu_atI'[elim]:
  "\<lbrakk> vcpu_at p s; pspace_relation (kheap s) (ksPSpace s');
     pspace_aligned' s'; pspace_distinct' s' \<rbrakk>
        \<Longrightarrow> vcpu_at' p s'"
  apply (clarsimp simp add: pde_at_def obj_at_def a_type_def)
  apply (simp split: Structures_A.kernel_object.split_asm
                     if_split_asm arch_kernel_obj.split_asm)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: other_obj_relation_def)
    apply (case_tac z ; simp)
    apply (rename_tac vcpu)
    apply (case_tac vcpu; simp)
  apply (clarsimp simp: vcpu_relation_def obj_at'_def typ_at'_def ko_wp_at'_def projectKOs)
  apply (fastforce simp add: pspace_aligned'_def pspace_distinct'_def dom_def)
  done

lemma vcpuSwitch_corres':
  assumes "vcpu' = vcpu"
  shows
  "corres dc (\<lambda>s. (vcpu \<noteq> None \<longrightarrow> vcpu_at  (the vcpu) s) \<and>
                  ((arm_current_vcpu \<circ> arch_state) s \<noteq> None
                    \<longrightarrow> vcpu_at ((fst \<circ> the \<circ> arm_current_vcpu \<circ> arch_state) s) s))
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             (vcpu_switch vcpu)
             (vcpuSwitch vcpu')"
  apply (rule stronger_corres_guard_imp,
         rule vcpuSwitch_corres[OF assms])
   apply simp
  apply (simp add: assms)
  apply (rule conjI)
   apply clarsimp
   apply (rule aligned_distinct_relation_vcpu_atI' ; clarsimp simp add: state_relation_def, assumption?)
  apply (clarsimp simp add: state_relation_def arch_state_relation_def)
  apply (rule aligned_distinct_relation_vcpu_atI'; assumption)
  done

lemma no_fail_setCurrentPDPL2: "no_fail \<top> (setCurrentPDPL2 w)"
  by (simp add: set_current_pd_def setCurrentPDPL2_def)

lemma setCurrentPD_corres:
  "addr = addr' \<Longrightarrow> corres dc \<top> \<top> (do_machine_op (set_current_pd addr)) (doMachineOp (setCurrentPD addr'))"
  apply (simp add: setCurrentPD_def set_current_pd_def)
  apply (rule corres_machine_op)
  apply (rule corres_guard_imp)
    apply (rule corres_rel_imp)
     apply (rule corres_underlying_trivial)
    apply (rule no_fail_setCurrentPDPL2)
    apply simp+
  done

crunch tcb_at'[wp]: armv_contextSwitch "tcb_at' t"
crunch ko_at'[wp]: armv_contextSwitch "ko_at' p t"

crunch tcb_at[wp]: arm_context_switch "tcb_at p"
crunch ko_at[wp]: arm_context_switch "ko_at p t"

crunch pspace_distinct'[wp]: getHWASID "pspace_distinct'"
crunch pspace_aligned'[wp]: getHWASID "pspace_aligned'"

(* TODO: move CSpaceInv_AI *)
lemma assert_get_tcb_ko':
  shows "\<lbrace>P\<rbrace> gets_the (get_tcb thread) \<lbrace>\<lambda>t. P and ko_at (TCB t) thread\<rbrace>"
  by (clarsimp simp: valid_def in_monad gets_the_def get_tcb_def
                     obj_at_def
               split: option.splits Structures_A.kernel_object.splits)

lemma valid_objs_valid_tcb: "\<lbrakk> valid_objs s ; ko_at (TCB t) p s \<rbrakk> \<Longrightarrow> valid_tcb p t s"
  by (fastforce simp add: valid_objs_def valid_obj_def obj_at_def)

lemma valid_objs_valid_tcb': "\<lbrakk> valid_objs' s ; ko_at' (t :: tcb) p s \<rbrakk> \<Longrightarrow> valid_tcb' t s"
  by (fastforce simp add: obj_at'_def ran_def valid_obj'_def projectKOs valid_objs'_def)

lemma setVMRoot_corres:
  "corres dc (tcb_at t and valid_arch_state and valid_objs and valid_asid_map
              and unique_table_refs o caps_of_state and valid_vs_lookup
              and pspace_aligned and pspace_distinct
              and valid_vspace_objs)
             (pspace_aligned' and pspace_distinct'
                 and valid_arch_state' and tcb_at' t and no_0_obj')
             (set_vm_root t) (setVMRoot t)"
proof -
  have Q: "\<And>P P'. corres dc P P'
        (throwError ExceptionTypes_A.lookup_failure.InvalidRoot <catch>
         (\<lambda>_. do global_us_pd \<leftarrow> gets (arm_us_global_pd \<circ> arch_state);
                 do_machine_op $ set_current_pd $ addrFromKPPtr global_us_pd
              od))
        (throwError Fault_H.lookup_failure.InvalidRoot <catch>
         (\<lambda>_ . do globalPD \<leftarrow> gets (armUSGlobalPD \<circ> ksArchState);
                  doMachineOp $ setCurrentPD $ addrFromKPPtr globalPD
               od))"
    apply (rule corres_guard_imp)
      apply (rule corres_split_catch [where f=lfr])
         apply (rule corres_trivial)
         apply (subst corres_throwError, simp add: lookup_failure_map_def)
        apply (rule corres_underlying_split [where P=\<top> and P'=\<top> and r'="(=)"])
           apply (clarsimp simp: state_relation_def arch_state_relation_def)
          apply (simp, rule setCurrentPD_corres, rule refl)
         apply wpsimp+
    done
  have valid_tcb_vcpu: "\<And>s t p v.\<lbrakk> valid_tcb p t s; tcb_vcpu (tcb_arch t) = Some v \<rbrakk>
                        \<Longrightarrow> vcpu_at v s"
    by (clarsimp simp add: valid_tcb_def valid_arch_tcb_def)
  have valid_arch_state_curr_vcpu:
    "\<And>a b s. \<lbrakk>valid_arch_state s; arm_current_vcpu (arch_state s) = Some (a, b)\<rbrakk>
     \<Longrightarrow> vcpu_at a s"
    by (clarsimp simp add: valid_arch_state_def obj_at_def is_vcpu_def)
  show ?thesis
    unfolding set_vm_root_def setVMRoot_def locateSlot_conv
                     getThreadVSpaceRoot_def
    apply (rule corres_guard_imp)
      apply (rule corres_underlying_split [where r'="(=) \<circ> cte_map"])
         apply (simp add: tcbVTableSlot_def cte_map_def objBits_def cte_level_bits_def
                          objBitsKO_def tcb_cnode_index_def to_bl_1)
        apply (rule_tac R="\<lambda>thread_root. valid_arch_state and valid_asid_map and
                                         valid_vspace_objs and valid_vs_lookup and
                                         unique_table_refs o caps_of_state and
                                         valid_objs and
                                         tcb_at t and
                                         pspace_aligned and pspace_distinct and
                                         cte_wp_at ((=) thread_root) thread_root_slot"
                     and R'="\<lambda>thread_root. pspace_aligned' and pspace_distinct' and no_0_obj' and tcb_at' t"
                     in corres_split[OF getSlotCap_corres])
           apply simp
          apply (case_tac rv, simp_all add: isCap_simps Q[simplified])[1]
          apply (rename_tac arch_cap)
          apply (case_tac arch_cap, simp_all add: isCap_simps Q[simplified])[1]
          apply (rename_tac word option)
          apply (case_tac option, simp_all add: Q[simplified])[1]
          apply (clarsimp simp: cap_asid_def)
          apply (rule corres_guard_imp)
            apply (rule corres_split_catch [where f=lfr])
               apply (rule corres_split_eqrE[OF find_pd_for_asid_corres])
                  apply simp
                 apply (rule whenE_throwError_corres)
                   apply (simp add: lookup_failure_map_def)
                  apply simp
                 apply simp
                 apply (rule armv_contextSwitch_corres)
                apply simp
                apply (wpsimp wp: assert_get_tcb_ko' find_pd_for_asid_pd_at_asid_again
                            simp: armv_contextSwitch_def if_apply_def2
                       | wp (once) hoare_drop_imps)+
              apply (simp add: checkPDNotInASIDMap_def
                               checkPDASIDMapMembership_def)
              apply (rule_tac P'="(Not \<circ> vspace_at_asid aa word) and K (aa \<le> mask asid_bits)
                                    and pd_at_uniq aa word
                                    and valid_asid_map and valid_vs_lookup
                                    and (unique_table_refs o caps_of_state)
                                    and valid_vspace_objs
                                    and valid_arch_state"
                          in corres_stateAssert_implied)
               apply (rule corres_underlying_split [where P=\<top> and P'=\<top> and r'="(=)"])
                  apply (clarsimp simp: state_relation_def arch_state_relation_def)
                 apply (rule setCurrentPD_corres, simp)
                apply wp+
              apply (clarsimp simp: restrict_map_def state_relation_asid_map
                             elim!: ranE)
              apply (frule(1) valid_asid_mapD)
              apply (case_tac "x = aa")
               apply clarsimp
              apply (clarsimp simp: pd_at_uniq_def restrict_map_def)
              apply (erule notE, rule_tac a=x in ranI)
              apply simp
             apply ((wp find_pd_for_asid_pd_at_asid_again
                     | simp add: if_apply_def2 | wp (once) hoare_drop_imps)+)
           apply clarsimp
           apply (frule page_directory_cap_pd_at_uniq, simp+)
           apply (frule(1) cte_wp_at_valid_objs_valid_cap)
           apply (clarsimp simp: valid_cap_def mask_def
                                 word_neq_0_conv)
           apply (drule(1) pd_at_asid_unique2, simp)
          apply simp+
         apply (wp get_cap_wp | simp)+
     apply (clarsimp simp: tcb_at_cte_at_1 [simplified])
    apply simp
    done
qed

lemma invalidateTLBByASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> invalidateTLBByASID param_a \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: invalidateTLBByASID_def loadHWASID_def
         | wp dmo_invs' no_irq_invalidateLocalTLB_ASID no_irq | wpc)+
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply (clarsimp simp: invalidateLocalTLB_ASID_def machine_op_lift_def
                          machine_rest_lift_def split_def | wp)+
  done

crunches flushSpace
  for aligned' [wp]: pspace_aligned'
  and distinct' [wp]: pspace_distinct'
  and valid_arch' [wp]: valid_arch_state'
  and cur_tcb' [wp]: cur_tcb'

lemma get_asid_pool_corres_inv':
  "corres (\<lambda>p. (\<lambda>p'. p = p' o ucast) \<circ> inv ASIDPool)
          (asid_pool_at p) (pspace_aligned' and pspace_distinct')
          (get_asid_pool p) (getObject p)"
  apply (rule corres_rel_imp)
   apply (rule getObject_ASIDPool_corres')
  apply simp
  done

lemma loadHWASID_wp [wp]:
  "\<lbrace>\<lambda>s. P (option_map fst (armKSASIDMap (ksArchState s) asid)) s\<rbrace>
         loadHWASID asid \<lbrace>P\<rbrace>"
  apply (simp add: loadHWASID_def)
  apply (wp findPDForASIDAssert_pd_at_wp
            | wpc | simp | wp (once) hoare_drop_imps)+
  apply (auto split: option.split)
  done

lemma invalidateASIDEntry_corres:
  "corres dc (valid_vspace_objs and valid_asid_map
                and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0)
                and vspace_at_asid asid pd and valid_vs_lookup
                and unique_table_refs o caps_of_state
                and valid_arch_state
                and pspace_aligned and pspace_distinct)
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             (invalidate_asid_entry asid) (invalidateASIDEntry asid)"
  apply (simp add: invalidate_asid_entry_def invalidateASIDEntry_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF loadHWASID_corres[where pd=pd]])
      apply (rule corres_split[OF corres_when])
          apply simp
         apply simp
         apply (rule invalidateHWASIDEntry_corres)
        apply (rule invalidateASID_corres[where pd=pd])
       apply (wp load_hw_asid_wp
                | clarsimp cong: if_cong)+
   apply (simp add: pd_at_asid_uniq)
  apply simp
  done

crunch aligned'[wp]: invalidateASID "pspace_aligned'"
crunch distinct'[wp]: invalidateASID "pspace_distinct'"

lemma invalidateASID_cur' [wp]:
  "\<lbrace>cur_tcb'\<rbrace> invalidateASID x \<lbrace>\<lambda>_. cur_tcb'\<rbrace>"
  by (simp add: invalidateASID_def|wp)+

crunch aligned' [wp]: invalidateASIDEntry pspace_aligned'
crunch distinct' [wp]: invalidateASIDEntry pspace_distinct'
crunch cur' [wp]: invalidateASIDEntry cur_tcb'

lemma invalidateASID_valid_arch_state [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> invalidateASIDEntry x \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  supply option.case_cong_weak[cong]
  apply (simp add: invalidateASID_def
                   invalidateASIDEntry_def invalidateHWASIDEntry_def)
  apply (wp | simp)+
  apply (clarsimp simp: valid_arch_state'_def simp del: fun_upd_apply)
  apply (rule conjI)
   apply (clarsimp simp: is_inv_None_upd fun_upd_def[symmetric] comp_upd_simp
                         inj_on_fun_upd_elsewhere valid_asid_map'_def)
   apply (auto elim!: subset_inj_on dest!: ran_del_subset split: option.splits)
  done

crunches vcpuDisable, vcpuEnable, vcpuSave, vcpuRestore
  for no_0_obj'[wp]: no_0_obj'
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

lemma vcpuSwitch_no_0_obj'[wp]: "\<lbrace>no_0_obj'\<rbrace> vcpuSwitch v \<lbrace>\<lambda>_. no_0_obj'\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

crunch no_0_obj'[wp]: deleteASID "no_0_obj'"
  (simp: crunch_simps
   wp: crunch_wps getObject_inv loadObject_default_inv)

lemma deleteASID_corres:
  "corres dc
          (invs and valid_etcbs and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0))
          (pspace_aligned' and pspace_distinct' and no_0_obj'
              and valid_arch_state' and cur_tcb')
          (delete_asid asid pd) (deleteASID asid pd)"
  apply (simp add: delete_asid_def deleteASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_asid])
      apply (case_tac "asid_table (asid_high_bits_of asid)", simp)
      apply clarsimp
      apply (rule_tac P="\<lambda>s. asid_high_bits_of asid \<in> dom (asidTable o ucast) \<longrightarrow>
                             asid_pool_at (the ((asidTable o ucast) (asid_high_bits_of asid))) s" and
                      P'="pspace_aligned' and pspace_distinct'" and
                      Q="invs and valid_etcbs and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0) and
                         (\<lambda>s. arm_asid_table (arch_state s) = asidTable \<circ> ucast)" in
                      corres_split)
         apply (simp add: dom_def)
         apply (rule get_asid_pool_corres_inv')
        apply (rule corres_when, simp add: mask_asid_low_bits_ucast_ucast)
        apply (rule corres_split[OF flushSpace_corres[where pd=pd]])
          apply (rule corres_split[OF invalidateASIDEntry_corres[where pd=pd]])
            apply (rule_tac P="asid_pool_at (the (asidTable (ucast (asid_high_bits_of asid))))
                               and valid_etcbs"
                        and P'="pspace_aligned' and pspace_distinct'"
                         in corres_split)
               apply (simp del: fun_upd_apply)
               apply (rule setObject_ASIDPool_corres')
               apply (simp add: inv_def mask_asid_low_bits_ucast_ucast)
               apply (rule ext)
               apply (clarsimp simp: o_def)
               apply (erule notE)
               apply (erule ucast_ucast_eq, simp, simp)
              apply (rule corres_split[OF getCurThread_corres])
                apply simp
                apply (rule setVMRoot_corres)
               apply wp+
             apply (simp del: fun_upd_apply)
             apply (fold cur_tcb_def)
             apply (wp set_asid_pool_asid_map_unmap
                       set_asid_pool_vspace_objs_unmap_single
                       set_asid_pool_vs_lookup_unmap')+
            apply simp
            apply (fold cur_tcb'_def)
            apply (wp invalidate_asid_entry_invalidates)+
         apply (wp | clarsimp simp: o_def)+
       apply (subgoal_tac "vspace_at_asid asid pd s")
        apply (auto simp: obj_at_def a_type_def graph_of_def
                   split: if_split_asm)[1]
       apply (simp add: vspace_at_asid_def)
       apply (rule vs_lookupI)
        apply (simp add: vs_asid_refs_def)
        apply (rule image_eqI[OF refl])
        apply (erule graph_ofI)
       apply (rule r_into_rtrancl)
       apply simp
       apply (erule vs_lookup1I [OF _ _ refl])
       apply (simp add: vs_refs_def)
       apply (rule image_eqI[rotated], erule graph_ofI)
       apply (simp add: mask_asid_low_bits_ucast_ucast)
      \<comment> \<open>rewrite assumption so that the goal can refer to the C variable instead of the abstract's.\<close>
      apply (drule Some_to_the)
      apply (wpsimp wp: getASID_wp)+
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                  dest!: invs_arch_state)
   apply blast
  apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def)
  done

lemma valid_arch_state_unmap_strg':
  "valid_arch_state' s \<longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState :=
                        armKSASIDTable_update (\<lambda>_. (armKSASIDTable (ksArchState s))(ptr := None))
                         (ksArchState s)\<rparr>)"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def)
  apply (auto simp: ran_def split: if_split_asm option.splits)
  done

crunch armKSASIDTable_inv[wp]: invalidateASIDEntry
    "\<lambda>s. P (armKSASIDTable (ksArchState s))"
crunch armKSASIDTable_inv[wp]: flushSpace
    "\<lambda>s. P (armKSASIDTable (ksArchState s))"

lemma deleteASIDPool_corres:
  "corres dc
          (invs and K (is_aligned base asid_low_bits
                         \<and> base \<le> mask asid_bits)
           and asid_pool_at ptr)
          (pspace_aligned' and pspace_distinct' and no_0_obj'
               and valid_arch_state' and cur_tcb')
          (delete_asid_pool base ptr) (deleteASIDPool base ptr)"
  apply (simp add: delete_asid_pool_def deleteASIDPool_def)
  apply (rule corres_assume_pre, simp add: is_aligned_mask
                                     cong: corres_weak_cong)
  apply (thin_tac P for P)+
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_asid])
      apply (rule corres_when)
       apply simp
      apply (simp add: liftM_def)
      apply (rule corres_split[OF getObject_ASIDPool_corres'])
        apply (rule corres_split)
           apply (rule corres_mapM [where r=dc and r'=dc], simp, simp)
               prefer 5
               apply (rule order_refl)
              apply (drule_tac t="inv f x \<circ> g" for f x g in sym)
              apply (rule_tac P="invs and
                                 ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) ptr and
                                 [VSRef (ucast (asid_high_bits_of base)) None] \<rhd> ptr and
                                 K (is_aligned base asid_low_bits
                                      \<and> base \<le> mask asid_bits)"
                         and P'="pspace_aligned' and pspace_distinct' and no_0_obj'"
                              in corres_guard_imp)
                apply (rule corres_when)
                 apply (clarsimp simp: ucast_ucast_low_bits)
                apply simp
                apply (rule_tac pd1="the (pool (ucast xa))"
                          in corres_split[OF flushSpace_corres])
                  apply (rule_tac pd="the (pool (ucast xa))"
                             in invalidateASIDEntry_corres)
                 apply wp
                 apply clarsimp
                 apply wp+
               apply (clarsimp simp: invs_def valid_state_def
                                     valid_arch_caps_def valid_pspace_def
                                     vspace_at_asid_def cong: conj_cong)
               apply (rule conjI)
                apply (clarsimp simp: mask_def asid_low_bits_word_bits
                               elim!: is_alignedE)
                apply (subgoal_tac "of_nat q < (2 ^ asid_high_bits :: word32)")
                 apply (subst mult.commute, rule word_add_offset_less)
                     apply assumption
                    apply assumption
                   apply (simp add: asid_bits_def word_bits_def)
                  apply (erule order_less_le_trans)
                  apply (simp add: word_bits_def asid_low_bits_def asid_high_bits_def)
                 apply (simp add: asid_bits_def asid_high_bits_def asid_low_bits_def)
                apply (drule word_power_less_diff)
                   apply (drule of_nat_mono_maybe[where 'a=32, rotated])
                    apply (simp add: word_bits_def asid_low_bits_def)
                   apply (subst word_unat_power, simp)
                  apply (simp add: asid_bits_def word_bits_def)
                 apply (simp add: asid_low_bits_def word_bits_def)
                apply (simp add: asid_bits_def asid_low_bits_def asid_high_bits_def)
               apply (subst conj_commute, rule context_conjI)
                apply (erule vs_lookup_trancl_step)
                apply (rule r_into_trancl)
                apply (erule vs_lookup1I)
                 apply (simp add: vs_refs_def)
                 apply (rule image_eqI[rotated])
                  apply (rule graph_ofI, simp)
                 apply clarsimp
                 apply fastforce
                apply (simp add: add_mask_eq asid_low_bits_word_bits
                                 ucast_ucast_mask asid_low_bits_def[symmetric]
                                 asid_high_bits_of_def)
                apply (rule conjI)
                 apply (rule sym)
                 apply (simp add: is_aligned_add_helper[THEN conjunct1]
                                  mask_eq_iff_w2p asid_low_bits_def word_size)
                apply (rule_tac f="\<lambda>a. a && mask n" for n in arg_cong)
                apply (rule shiftr_eq_mask_eq)
                apply (simp add: is_aligned_add_helper is_aligned_neg_mask_eq)
               apply clarsimp
               apply (subgoal_tac "base \<le> base + xa")
                apply (simp add: valid_vs_lookup_def asid_high_bits_of_def)
                subgoal by (fastforce intro: vs_lookup_pages_vs_lookupI)
               apply (erule is_aligned_no_wrap')
                apply (simp add: asid_low_bits_word_bits)
               apply (simp add: asid_low_bits_word_bits)
              apply clarsimp
             apply ((wp|clarsimp simp: o_def)+)[3]
          apply (rule corres_split)
             apply (rule corres_modify [where P=\<top> and P'=\<top>])
             apply (simp add: state_relation_def arch_state_relation_def)
             apply (rule ext)
             apply clarsimp
             apply (erule notE)
             apply (rule word_eqI[rule_format])
             apply (drule_tac x1="ucast xa" in bang_eq [THEN iffD1])
             apply (erule_tac x=n in allE)
             apply (simp add: word_size nth_ucast)
            apply (rule corres_split)
               apply (rule getCurThread_corres)
              apply (simp only:)
              apply (rule setVMRoot_corres)
             apply wp+
         apply (rule_tac R="\<lambda>_ s. rv = arm_asid_table (arch_state s)"
                    in hoare_post_add)
         apply (drule sym, simp only: )
         apply (drule sym, simp only: )
         apply (thin_tac "P" for P)+
         apply (simp only: pred_conj_def cong: conj_cong)
         apply simp
         apply (fold cur_tcb_def)
         apply (strengthen valid_arch_state_unmap_strg
                           valid_vspace_objs_unmap_strg
                           valid_asid_map_unmap
                           valid_vs_lookup_unmap_strg, simp)
         apply (rule hoare_vcg_conj_lift,
                 (rule mapM_invalidate[where ptr=ptr])?,
                 ((wp mapM_wp' | simp)+)[1])+
        apply (rule_tac R="\<lambda>_ s. rv' = armKSASIDTable (ksArchState s)"
                     in hoare_post_add)
        apply (simp only: pred_conj_def cong: conj_cong)
        apply simp
        apply (strengthen valid_arch_state_unmap_strg')
        apply (fold cur_tcb'_def)
        apply (wp mapM_wp')+
       apply (clarsimp simp: cur_tcb'_def)
      apply (simp add: o_def pred_conj_def)
      apply wp
     apply (wp getASID_wp)+
   apply (clarsimp simp: conj_comms)
   apply (auto simp: vs_lookup_def intro: vs_asid_refsI)[1]
  apply clarsimp
done

lemma setVMRootForFlush_corres:
  "corres (=)
          (cur_tcb and vspace_at_asid asid pd
           and K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits)
           and valid_asid_map and valid_vs_lookup
           and valid_vspace_objs
           and unique_table_refs o caps_of_state
           and valid_arch_state
           and pspace_aligned and pspace_distinct)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (set_vm_root_for_flush pd asid)
          (setVMRootForFlush pd asid)"
proof -
  have X: "corres (=) (vspace_at_asid asid pd and K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits)
                          and valid_asid_map and valid_vs_lookup
                          and valid_vspace_objs
                          and unique_table_refs o caps_of_state
                          and valid_arch_state
                          and pspace_aligned and pspace_distinct)
                       (pspace_aligned' and pspace_distinct' and no_0_obj')
           (do arm_context_switch pd asid;
               return True
            od)
           (do armv_contextSwitch pd asid;
               return True
            od)"
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF armv_contextSwitch_corres])
        apply (rule corres_trivial)
        apply (wp | simp)+
    done
  show ?thesis
  apply (simp add: set_vm_root_for_flush_def setVMRootForFlush_def getThreadVSpaceRoot_def locateSlot_conv)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres])
      apply (rule corres_split [where R="\<lambda>_. vspace_at_asid asid pd and K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits)
                                               and valid_asid_map and valid_vs_lookup
                                               and valid_vspace_objs
                                               and unique_table_refs o caps_of_state
                                               and valid_arch_state
                                               and pspace_aligned and pspace_distinct"
                                  and R'="\<lambda>_. pspace_aligned' and pspace_distinct' and no_0_obj'",
                                  OF getSlotCap_corres])
         apply (simp add: cte_map_def objBits_simps tcb_cnode_index_def
                          tcbVTableSlot_def to_bl_1 cte_level_bits_def)
        apply (case_tac "isArchObjectCap rv' \<and>
                         isPageDirectoryCap (capCap rv') \<and>
                         capPDMappedASID (capCap rv') \<noteq> None \<and>
                         capPDBasePtr (capCap rv') = pd")
         apply (case_tac rv, simp_all add: isCap_simps)[1]
         apply (rename_tac arch_cap)
         apply (case_tac arch_cap, auto)[1]
        apply (case_tac rv, simp_all add: isCap_simps[simplified] X[simplified])[1]
        apply (rename_tac arch_cap)
        apply (case_tac arch_cap, auto simp: X[simplified] split: option.splits)[1]
       apply wp+
   apply (clarsimp simp: cur_tcb_def)
   apply (erule tcb_at_cte_at)
   apply (simp add: tcb_cap_cases_def)
  apply clarsimp
  done
qed

crunch typ_at' [wp]: armv_contextSwitch "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps)

crunch typ_at' [wp]: findPDForASID "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps loadObject_default_def)

crunches vcpuEnable, vcpuDisable, vcpuSave, vcpuRestore
  for typ_at' [wp]: "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps
     wp: crunch_wps getObject_inv loadObject_default_inv)

lemma vcpuSwitch_typ_at'[wp]:
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_ s. P (typ_at' T p s) \<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

crunch typ_at' [wp]: setVMRoot "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps
     wp: crunch_wps getObject_inv loadObject_default_inv)

lemmas setVMRoot_typ_ats [wp] = typ_at_lifts [OF setVMRoot_typ_at']

lemmas loadHWASID_typ_ats [wp] = typ_at_lifts [OF loadHWASID_inv]

crunch typ_at' [wp]: setVMRootForFlush "\<lambda>s. P (typ_at' T p s)"
  (wp: hoare_drop_imps)

lemmas setVMRootForFlush_typ_ats' [wp] = typ_at_lifts [OF setVMRootForFlush_typ_at']

crunch aligned' [wp]: setVMRootForFlush pspace_aligned'
  (wp: hoare_drop_imps)
crunch distinct' [wp]: setVMRootForFlush pspace_distinct'
  (wp: hoare_drop_imps)

crunch cur' [wp]: setVMRootForFlush cur_tcb'
  (wp: hoare_drop_imps)

lemma findPDForASID_inv2:
  "\<lbrace>\<lambda>s. asid \<noteq> 0 \<and> asid \<le> mask asid_bits \<longrightarrow> P s\<rbrace> findPDForASID asid \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases "asid \<noteq> 0 \<and> asid \<le> mask asid_bits")
   apply (simp add: findPDForASID_inv)
  apply (simp add: findPDForASID_def assertE_def asidRange_def mask_def)
  apply clarsimp
  done

lemma storeHWASID_valid_arch' [wp]:
  "\<lbrace>valid_arch_state' and
    (\<lambda>s. armKSASIDMap (ksArchState s) asid = None \<and>
         armKSHWASIDTable (ksArchState s) hw_asid = None)\<rbrace>
  storeHWASID asid hw_asid
  \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  supply image_cong_simp [cong del]
  apply (simp add: storeHWASID_def)
  apply wp
   prefer 2
   apply assumption
  apply (simp add: valid_arch_state'_def comp_upd_simp fun_upd_def[symmetric] cong: option.case_cong)
  apply wp
   apply (simp add: findPDForASIDAssert_def const_def
                    checkPDUniqueToASID_def checkPDASIDMapMembership_def)
   apply wp
   apply (rule_tac Q'="\<lambda>rv s. valid_asid_map' (armKSASIDMap (ksArchState s))
                               \<and> asid \<noteq> 0 \<and> asid \<le> mask asid_bits
                               \<and> armKSGICVCPUNumListRegs (ksArchState s) \<le> max_armKSGICVCPUNumListRegs"
              in hoare_post_imp_R)
    apply (wp findPDForASID_inv2)+
   apply clarsimp
   apply (clarsimp simp: valid_asid_map'_def)
   apply (subst conj_commute, rule context_conjI)
    apply clarsimp
    apply (rule ccontr, erule notE, rule_tac a=x in ranI)
    apply (simp add: restrict_map_def)
   apply (erule(1) inj_on_fun_updI2)
  apply clarsimp
  apply (frule is_inv_NoneD[rotated], simp)
  apply (simp add: ran_def)
  apply (simp add: is_inv_def)
  done

lemma storeHWASID_obj_at [wp]:
  "\<lbrace>\<lambda>s. P (obj_at' P' t s)\<rbrace> storeHWASID x y \<lbrace>\<lambda>rv s. P (obj_at' P' t s)\<rbrace>"
  apply (simp add: storeHWASID_def)
  apply (wp | simp)+
  done

lemma findFreeHWASID_obj_at [wp]:
  "\<lbrace>\<lambda>s. P (obj_at' P' t s)\<rbrace> findFreeHWASID \<lbrace>\<lambda>rv s. P (obj_at' P' t s)\<rbrace>"
  apply (simp add: findFreeHWASID_def invalidateASID_def
                   invalidateHWASIDEntry_def bind_assoc
              cong: option.case_cong)
  apply (wp doMachineOp_obj_at|wpc|simp)+
  done

lemma findFreeHWASID_valid_arch [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> findFreeHWASID \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: findFreeHWASID_def invalidateHWASIDEntry_def
                   invalidateASID_def doMachineOp_def split_def
              cong: option.case_cong)
  apply (wp|wpc|simp split del: if_split)+
  apply (clarsimp simp: valid_arch_state'_def fun_upd_def[symmetric]
                        comp_upd_simp valid_asid_map'_def cong: option.case_cong)
  apply (frule is_inv_inj)
  apply (drule findNoneD)
  apply (drule_tac x="armKSNextASID (ksArchState s)" in bspec)
   apply clarsimp
  apply (clarsimp simp: is_inv_def ran_upd[folded fun_upd_def]
                        dom_option_map inj_on_fun_upd_elsewhere)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x="x" and y="armKSNextASID (ksArchState s)" in inj_onD)
      apply simp
     apply blast
    apply blast
   apply simp
  apply (rule conjI)
   apply (erule subset_inj_on, clarsimp)
  apply (erule order_trans[rotated])
  apply clarsimp
  done

lemma findFreeHWASID_None_map [wp]:
  "\<lbrace>\<lambda>s. armKSASIDMap (ksArchState s) asid = None\<rbrace>
  findFreeHWASID
  \<lbrace>\<lambda>rv s. armKSASIDMap (ksArchState s) asid = None\<rbrace>"
  apply (simp add: findFreeHWASID_def invalidateHWASIDEntry_def invalidateASID_def
                   doMachineOp_def split_def
              cong: option.case_cong)
  apply (rule hoare_pre)
   apply (wp|wpc|simp split del: if_split)+
  apply auto
  done

lemma findFreeHWASID_None_HWTable [wp]:
  "\<lbrace>\<top>\<rbrace> findFreeHWASID \<lbrace>\<lambda>rv s. armKSHWASIDTable (ksArchState s) rv = None\<rbrace>"
  apply (simp add: findFreeHWASID_def invalidateHWASIDEntry_def invalidateASID_def
                   doMachineOp_def
              cong: option.case_cong)
  apply (wp|wpc|simp)+
  apply (auto dest!: findSomeD)
  done

lemma getHWASID_valid_arch':
  "\<lbrace>valid_arch_state'\<rbrace>
      getHWASID asid \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: getHWASID_def)
  apply (wp | wpc | simp)+
  done

crunch valid_arch' [wp]: setVMRootForFlush "valid_arch_state'"
  (wp: hoare_drop_imps)

lemma load_hw_asid_corres2:
  "corres (=)
     (valid_vspace_objs and pspace_distinct and pspace_aligned
       and valid_asid_map and vspace_at_asid a pd
       and valid_vs_lookup and valid_global_objs
       and unique_table_refs o caps_of_state
       and valid_arch_state and K (a \<noteq> 0 \<and> a \<le> mask asid_bits))
     (pspace_aligned' and pspace_distinct' and no_0_obj')
    (load_hw_asid a) (loadHWASID a)"
  apply (rule stronger_corres_guard_imp)
    apply (rule loadHWASID_corres[where pd=pd])
   apply (clarsimp simp: pd_at_asid_uniq)
  apply simp
  done

crunch no_0_obj'[wp]: flushTable "no_0_obj'"
  (wp: crunch_wps simp: crunch_simps)

lemma flushTable_corres:
  "corres dc
          (pspace_aligned and valid_objs and valid_arch_state and
           cur_tcb and vspace_at_asid asid pd and valid_asid_map and valid_vspace_objs and
           pspace_aligned and pspace_distinct and valid_vs_lookup
           and unique_table_refs o caps_of_state and
           K (is_aligned vptr (pageBitsForSize ARMSection) \<and> asid \<le> mask asid_bits \<and> asid \<noteq> 0))
          (pspace_aligned' and pspace_distinct' and no_0_obj' and
           valid_arch_state' and cur_tcb')
          (flush_table pd asid vptr ptr)
          (flushTable pd asid vptr)"
  apply (simp add: flush_table_def flushTable_def)
  apply (rule corres_assume_pre)
  apply (simp add: ptBits_def pt_bits_def pageBits_def is_aligned_mask cong: corres_weak_cong)
  apply (thin_tac "P" for P)+
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF setVMRootForFlush_corres])
      apply (rule corres_split[OF load_hw_asid_corres2[where pd=pd]])
        apply (clarsimp cong: corres_weak_cong)
        apply (rule corres_when, rule refl)
        apply (rule corres_split[where r' = dc, OF corres_machine_op corres_when])
            apply (rule corres_Id[OF refl])
             apply simp
            apply (rule no_fail_invalidateLocalTLB_ASID)
           apply simp
          apply (rule corres_split[OF getCurThread_corres])
            apply (simp, rule setVMRoot_corres)
           apply ((wp mapM_wp' hoare_vcg_const_imp_lift get_pte_wp getPTE_wp|
                   wpc|simp|fold cur_tcb_def cur_tcb'_def)+)[4]
       apply (wpsimp wp: hoare_drop_imps | fold cur_tcb_def cur_tcb'_def)+
       apply (wpsimp wp: hoare_post_taut load_hw_asid_wp simp: valid_global_objs_def
            | rule hoare_drop_imps)+
  done

lemma flushPage_corres:
  "corres dc
          (K (is_aligned vptr pageBits \<and> asid \<le> mask asid_bits \<and> asid \<noteq> 0) and
           cur_tcb and valid_arch_state and valid_objs and
           vspace_at_asid asid pd and valid_asid_map and valid_vspace_objs and
           valid_vs_lookup and valid_global_objs and
           unique_table_refs o caps_of_state and
           pspace_aligned and pspace_distinct)
          (pspace_aligned' and pspace_distinct' and no_0_obj'
             and valid_arch_state' and cur_tcb')
          (flush_page pageSize pd asid vptr)
          (flushPage pageSize pd asid vptr)"
  apply (clarsimp simp: flush_page_def flushPage_def)
  apply (rule corres_assume_pre)
  apply (simp add: is_aligned_mask cong: corres_weak_cong)
  apply (thin_tac P for P)+
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF setVMRootForFlush_corres])
      apply (rule corres_split[OF load_hw_asid_corres2[where pd=pd]])
        apply (clarsimp cong: corres_weak_cong)
        apply (rule corres_when, rule refl)
        apply (rule corres_split[OF corres_machine_op [where r=dc]])
           apply (rule corres_Id, rule refl, simp)
           apply (rule no_fail_pre, wp no_fail_invalidateLocalTLB_VAASID)
           apply simp
          apply (rule corres_when, rule refl)
          apply (rule corres_split[OF getCurThread_corres])
            apply simp
            apply (rule setVMRoot_corres)
           apply wp+
         apply (simp add: cur_tcb_def [symmetric] cur_tcb'_def [symmetric])
         apply (wpsimp wp: hoare_post_taut load_hw_asid_wp simp: valid_global_objs_def
               | rule hoare_drop_imps
               | fold cur_tcb_def cur_tcb'_def)+
  done

crunch typ_at' [wp]: flushTable "\<lambda>s. P (typ_at' T p s)"
  (simp: assertE_def when_def wp: crunch_wps)

lemmas flushTable_typ_ats' [wp] = typ_at_lifts [OF flushTable_typ_at']

lemmas findPDForASID_typ_ats' [wp] = typ_at_lifts [OF findPDForASID_inv]

crunch inv [wp]: findPDForASID P
  (simp: assertE_def whenE_def loadObject_default_def
   wp: crunch_wps getObject_inv)

crunches vcpuEnable, vcpuSave, vcpuDisable, vcpuRestore
  for pspace_aligned'[wp]: pspace_aligned'
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

lemma vcpuSwitch_aligned'[wp]: "\<lbrace>pspace_aligned'\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_. pspace_aligned'\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

crunches vcpuEnable, vcpuSave, vcpuDisable, vcpuRestore
  for pspace_distinct'[wp]: pspace_distinct'
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

lemma vcpuSwitch_distinct'[wp]: "\<lbrace>pspace_distinct'\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_. pspace_distinct'\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

crunch aligned'[wp]: unmapPageTable "pspace_aligned'"
  (simp: crunch_simps
     wp: crunch_wps getObject_inv loadObject_default_inv)
crunch distinct'[wp]: unmapPageTable "pspace_distinct'"
  (simp: crunch_simps
     wp: crunch_wps getObject_inv loadObject_default_inv)

lemma pageTableMapped_corres:
  "corres (=) (valid_arch_state and valid_vspace_objs and pspace_aligned
                       and K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits))
                 (pspace_aligned' and pspace_distinct' and no_0_obj')
       (page_table_mapped asid vaddr pt)
       (pageTableMapped asid vaddr pt)"
  apply (simp add: page_table_mapped_def pageTableMapped_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch)
       apply (rule corres_split_eqrE[OF find_pd_for_asid_corres])
          apply simp
         apply (simp add: liftE_bindE)
         apply (rule corres_split[OF getObject_PDE_corres'])
           apply (rule corres_trivial)
           apply (case_tac rv,
             simp_all add: returnOk_def pde_relation_aligned_def
             split:if_splits ARM_HYP_H.pde.splits)[1]
          apply (wp | simp add: lookup_pd_slot_def Let_def)+
   apply (simp add: word_neq_0_conv)
  apply simp
  done

lemma storePDE_ko_wp_vcpu_at'[wp]:
  "storePDE p pde \<lbrace>\<lambda>s. P (ko_wp_at' (is_vcpu' and hyp_live') p' s)\<rbrace>"
  apply (clarsimp simp: storePDE_def)
  apply (wp hoare_drop_imps setObject_ko_wp_at, simp, simp add: objBits_simps archObjSize_def)
   apply (simp add: pde_bits_def)
  apply (clarsimp split del: if_split)
  apply (erule_tac P=P in rsubst)
  apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKOs is_vcpu'_def)
  done

lemma storePTE_ko_wp_vcpu_at'[wp]:
  "storePTE p pde \<lbrace>\<lambda>s. P (ko_wp_at' (is_vcpu' and hyp_live') p' s)\<rbrace>"
  apply (clarsimp simp: storePTE_def)
  apply (wp hoare_drop_imps setObject_ko_wp_at, simp, simp add: objBits_simps archObjSize_def)
   apply (simp add: pte_bits_def)
  apply (clarsimp split del: if_split)
  apply (erule_tac P=P in rsubst)
  apply (clarsimp simp: ko_wp_at'_def obj_at'_def projectKOs is_vcpu'_def)
  done

crunch inv[wp]: pageTableMapped "P"
  (wp: loadObject_default_inv)

crunch no_0_obj'[wp]: storePDE no_0_obj'
 (wp: setObject_cte_wp_at2' headM_inv hoare_drop_imp)

crunch no_0_obj'[wp]: storePTE no_0_obj'
 (wp: setObject_cte_wp_at2' headM_inv hoare_drop_imp)

lemma storePDE_valid_arch'[wp]: "\<lbrace>valid_arch_state'\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (wpsimp wp: setObject_cte_wp_at2' headM_inv hoare_drop_imp simp: storePDE_def)

lemma storePTE_valid_arch'[wp]: "\<lbrace>valid_arch_state'\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (wpsimp wp: setObject_cte_wp_at2' headM_inv hoare_drop_imp simp: storePTE_def)

lemma storePDE_cur_tcb'[wp]: "\<lbrace>cur_tcb'\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_. cur_tcb'\<rbrace>"
  by (wpsimp wp: setObject_cte_wp_at2' headM_inv hoare_drop_imp simp: storePDE_def)

lemma storePTE_cur_tcb'[wp]: "\<lbrace>cur_tcb'\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_. cur_tcb'\<rbrace>"
  by (wpsimp wp: setObject_cte_wp_at2' headM_inv hoare_drop_imp simp: storePTE_def)

lemma unmapPageTable_corres:
  "corres dc
          (invs and valid_etcbs and page_table_at pt and
           K (0 < asid \<and> is_aligned vptr 21 \<and> asid \<le> mask asid_bits))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_page_table asid vptr pt)
          (unmapPageTable asid vptr pt)"
  apply (clarsimp simp: unmapPageTable_def unmap_page_table_def ignoreFailure_def const_def cong: option.case_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF pageTableMapped_corres])
      apply (simp add: case_option_If2 split del: if_split)
      apply (rule corres_if2[OF refl])
       apply (rule corres_split)
          apply (rule storePDE_corres')
          apply (simp add:pde_relation_aligned_def)
         apply (rule corres_split[OF corres_machine_op])
            apply (rule corres_Id, rule refl, simp)
            apply (wp no_fail_cleanByVA_PoU)
           apply (rule flushTable_corres)
          apply (wpsimp wp: store_pde_pd_at_asid store_pde_vspace_objs_invalid)+
        apply (rule hoare_vcg_conj_lift)
         apply (simp add: store_pde_def)
         apply (wp set_pd_vs_lookup_unmap)+
      apply (rule corres_trivial, simp)
     apply (wp page_table_mapped_wp)
    apply (wp hoare_drop_imps)[1]
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_arch_caps_def
                         Word.word_gt_0)
   apply (frule (1) page_directory_pde_at_lookupI)
   apply (auto elim: simp: empty_table_def valid_pde_mappings_def pde_ref_def obj_at_def
                     vs_refs_pages_def graph_of_def split: if_splits)
  done

crunch typ_at' [wp]: flushPage "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps hoare_drop_imps)

lemmas flushPage_typ_ats' [wp] = typ_at_lifts [OF flushPage_typ_at']

lemma valid_objs_valid_vcpu': "\<lbrakk> valid_objs' s ; ko_at' (t :: vcpu) p s \<rbrakk> \<Longrightarrow> valid_vcpu' t s"
  by (fastforce simp add: obj_at'_def ran_def valid_obj'_def projectKOs valid_objs'_def)

lemma setObject_vcpu_no_tcb_update:
  "\<lbrakk> vcpuTCBPtr (f vcpu) = vcpuTCBPtr vcpu \<rbrakk>
  \<Longrightarrow> \<lbrace> valid_objs' and ko_at' (vcpu :: vcpu) p\<rbrace> setObject p (f vcpu) \<lbrace> \<lambda>_. valid_objs' \<rbrace>"
  apply (rule_tac Q="valid_objs' and (ko_at' vcpu p and valid_obj' (KOArch (KOVCPU vcpu)))" in hoare_pre_imp)
   apply (clarsimp)
   apply (frule valid_objs_valid_vcpu')
    apply assumption+
   apply (simp add: valid_obj'_def)
  apply (rule setObject_valid_objs')
  apply (clarsimp simp add: obj_at'_def projectKOs)
  apply (frule updateObject_default_result)
  apply (clarsimp simp add: projectKOs valid_obj'_def valid_vcpu'_def)
  done

lemma vcpuUpdate_valid_objs'[wp]:
  "\<forall>vcpu. vcpuTCBPtr (f vcpu) = vcpuTCBPtr vcpu \<Longrightarrow>
   \<lbrace>valid_objs'\<rbrace> vcpuUpdate vr f \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wpsimp simp: vcpuUpdate_def)
  apply (rule_tac vcpu=vcpu in setObject_vcpu_no_tcb_update)
  apply wpsimp+
  done

crunches
  vgicUpdate, vcpuSaveReg, vgicUpdateLR, vcpuSaveRegRange, vcpuSave,
  vcpuDisable, vcpuEnable, vcpuRestore, vcpuSwitch
  for valid_objs'[wp]: valid_objs'
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (wp: mapM_wp_inv simp: mapM_x_mapM)

crunch valid_objs' [wp]: flushPage "valid_objs'"
  (wp: crunch_wps hoare_drop_imps simp: crunch_simps)

crunch inv: lookupPTSlot "P"
  (wp: loadObject_default_inv)

crunch aligned' [wp]: unmapPage pspace_aligned'
  (wp: crunch_wps simp: crunch_simps)

crunch distinct' [wp]: unmapPage pspace_distinct'
  (wp: crunch_wps simp: crunch_simps)

lemma corres_split_strengthen_ftE:
  "\<lbrakk> corres (ftr \<oplus> r') P P' f j;
      \<And>rv rv'. r' rv rv' \<Longrightarrow> corres (ftr' \<oplus> r) (R rv) (R' rv') (g rv) (k rv');
      \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,-; \<lbrace>Q'\<rbrace> j \<lbrace>R'\<rbrace>,- \<rbrakk>
    \<Longrightarrow> corres (dc \<oplus> r) (P and Q) (P' and Q') (f >>=E (\<lambda>rv. g rv)) (j >>=E (\<lambda>rv'. k rv'))"
  apply (rule_tac r'=r' in corres_splitEE)
     apply (erule corres_rel_imp)
     apply (case_tac x, auto)[1]
    apply (rule corres_rel_imp, assumption)
    apply (case_tac x, auto)[1]
   apply (simp add: validE_R_def)+
  done

lemma checkMappingPPtr_corres:
  "corres (dc \<oplus> dc)
            ((case slotptr of Inl ptr \<Rightarrow> pte_at ptr | Inr ptr \<Rightarrow> pde_at ptr) and
             (\<lambda>s. (case slotptr of Inl ptr \<Rightarrow> is_aligned ptr (pg_entry_align sz)
                   | Inr ptr \<Rightarrow> is_aligned ptr (pg_entry_align sz))))
            (pspace_aligned' and pspace_distinct')
      (throw_on_false v (check_mapping_pptr pptr sz slotptr))
      (checkMappingPPtr pptr sz slotptr)"
  apply (rule corres_gen_asm)
  apply (simp add: throw_on_false_def liftE_bindE check_mapping_pptr_def
                   checkMappingPPtr_def)
  apply (cases slotptr, simp_all add: liftE_bindE)
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF getObject_PTE_corres'])
       apply (rule corres_trivial)
       subgoal by (cases sz,
         auto simp add: is_aligned_mask[symmetric]
         is_aligned_shiftr pg_entry_align_def pte_bits_def
         unlessE_def returnOk_def pte_relation_aligned_def
         split: ARM_A.pte.split if_splits ARM_HYP_H.pte.split )
      apply wp+
    apply simp
   apply (simp add:is_aligned_mask[symmetric] is_aligned_shiftr pg_entry_align_def)
  apply (rule corres_guard_imp)
   apply (rule corres_split[OF getObject_PDE_corres'])
      apply (rule corres_trivial)
      subgoal by (cases sz,
         auto simp add: is_aligned_mask[symmetric]
         is_aligned_shiftr pg_entry_align_def pde_bits_def
         unlessE_def returnOk_def pde_relation_aligned_def
         split: ARM_A.pde.split if_splits ARM_HYP_H.pde.split )
     apply wp+
   apply simp+
  done

crunch inv[wp]: checkMappingPPtr "P"
  (wp: crunch_wps loadObject_default_inv simp: crunch_simps)

lemma store_pte_pd_at_asid[wp]:
  "\<lbrace>vspace_at_asid asid pd\<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. vspace_at_asid asid pd\<rbrace>"
  apply (simp add: store_pte_def set_pd_def set_object_def vspace_at_asid_def)
  apply (wp get_object_wp)
  apply clarsimp
  done

lemma is_aligned_dvd_k: "\<lbrakk>  2 ^ m  * (k :: nat) = 2 ^ n  ; is_aligned p n \<rbrakk> \<Longrightarrow> is_aligned p m"
  apply (simp add: is_aligned_def)
  apply (rule dvd_mult_left[where b=k])
  apply (drule sym)
  apply simp
  done

lemma unmapPage_corres:
  "corres dc (invs and valid_etcbs and
              K (valid_unmap sz (asid,vptr) \<and> vptr < kernel_base \<and> asid \<le> mask asid_bits))
             (valid_objs' and valid_arch_state' and pspace_aligned' and
              pspace_distinct' and no_0_obj' and cur_tcb')
             (unmap_page sz asid vptr pptr)
             (unmapPage sz asid vptr pptr)"
  apply (clarsimp simp: unmap_page_def unmapPage_def ignoreFailure_def const_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch [where E="\<lambda>_. \<top>" and E'="\<lambda>_. \<top>"])
       apply (rule corres_split_strengthen_ftE[where ftr'=dc],
              rule find_pd_for_asid_corres[OF refl])
         apply (rule corres_splitEE)
            apply (rule_tac F = "vptr < kernel_base" in corres_gen_asm)
            apply (rule_tac P="\<exists>\<rhd> pd and page_directory_at pd and vspace_at_asid asid pd
                               and (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits))
                               and valid_arch_state and valid_vspace_objs
                               and equal_kernel_mappings
                               and pspace_aligned and valid_etcbs and
                               K (valid_unmap sz (asid,vptr) )" and
                            P'="pspace_aligned' and pspace_distinct'" in corres_inst)
            apply clarsimp
            apply (rename_tac pd)
            apply (cases sz, simp_all)[1]
               apply (rule corres_guard_imp)
                 apply (rule_tac F = "vptr < kernel_base" in corres_gen_asm)
                 apply (rule corres_split_strengthen_ftE[OF lookupPTSlot_corres])
                   apply simp
                   apply (rule corres_splitEE[OF checkMappingPPtr_corres])
                     apply simp
                     apply (rule corres_split[OF storePTE_corres'])
                        apply (clarsimp simp: pte_relation_aligned_def)
                       apply (rule corres_machine_op)
                       apply (rule corres_Id, rule refl, simp)
                       apply (rule no_fail_cleanByVA_PoU)
                      apply (wp hoare_drop_imps lookup_pt_slot_inv
                        lookupPTSlot_inv lookup_pt_slot_is_aligned
                                  | simp add: valid_global_objs_def)+
                apply (clarsimp simp: page_directory_pde_at_lookupI
                  page_directory_at_aligned_pd_bits vmsz_aligned_def)
                apply (simp add:valid_unmap_def pageBits_def)+
              apply (rule corres_guard_imp)
                apply (rule corres_split_strengthen_ftE[OF lookupPTSlot_corres])
                  apply (rule_tac F="is_aligned p 7" in corres_gen_asm)
                  apply (simp add: is_aligned_mask[symmetric])
                  apply (rule corres_split_strengthen_ftE[OF checkMappingPPtr_corres])
                    apply simp
                    apply (rule corres_split[OF corres_mapM])
                             prefer 8
                             apply (rule corres_machine_op)
                             apply (clarsimp simp: last_byte_pte_def objBits_simps archObjSize_def)
                             apply (rule corres_Id, rule refl, simp)
                             apply (rule no_fail_cleanCacheRange_PoU)
                            prefer 7
                            apply (rule order_refl)
                           apply simp
                          apply simp
                         apply clarsimp
                         apply (rule_tac P="(\<lambda>s. \<forall>x\<in>set largePagePTEOffsets. pte_at (x + pa) s) and pspace_aligned and valid_etcbs"
                                        and P'="pspace_aligned' and pspace_distinct'"
                                        in corres_guard_imp)
                           apply (rule storePTE_corres',  simp add:pte_relation_aligned_def)
                          apply clarsimp
                         apply clarsimp
                        apply (wp store_pte_typ_at hoare_vcg_const_Ball_lift | clarsimp | wp (once) hoare_drop_imps)+
    (* this is dumb... *)
                 apply (subst mult_is_add.mult_commute)
                 apply (wpsimp wp: lookup_pt_slot_ptes lookup_pt_slot_inv lookupPTSlot_inv
                             lookup_pt_slot_is_aligned lookup_pt_slot_is_aligned_6
                         simp: largePagePTEOffsets_def pte_bits_def)+
               apply (clarsimp simp: page_directory_pde_at_lookupI vmsz_aligned_def pd_aligned
                                     pd_bits_def pageBits_def valid_unmap_def valid_global_objs_def
                                     page_directory_at_aligned_pd_bits pde_bits_def)
              apply (simp add:pd_bits_def pageBits_def)
             apply (rule corres_guard_imp)
               apply (rule corres_split_strengthen_ftE[OF checkMappingPPtr_corres])
                 apply simp
                 apply (rule corres_split[OF storePDE_corres'])
                    apply (simp add: pde_relation_aligned_def)
                   apply (rule corres_machine_op)
                   apply (rule corres_Id, rule refl, simp)
                   apply (rule no_fail_cleanByVA_PoU)
                  apply (rule wp_post_taut)+
                apply (wp | simp add:pde_relation_aligned_def
                      | wp (once) hoare_drop_imps)+
              apply (clarsimp simp: page_directory_pde_at_lookupI
                                    pg_entry_align_def)
              apply (clarsimp simp:lookup_pd_slot_def)
              apply (clarsimp simp add: pd_bits_def pageBits_def
                                        word_bits_conv pt_bits_def pde_bits_def)
              apply (rule is_aligned_add[rotated])
               apply (rule is_aligned_shift)
              apply (clarsimp simp add: obj_at_def pspace_aligned_def Ball_def dom_def)
              apply (erule_tac x=pd in allE)
              apply (clarsimp simp add: pd_bits_def pde_bits_def)
              apply (rule is_aligned_dvd_k[where k=2048 and n=14]; clarsimp)
             apply clarsimp
            apply (simp add:pd_bits_def pageBits_def)
            apply (rule corres_guard_imp)
              apply (rule corres_split_strengthen_ftE[OF checkMappingPPtr_corres])
                apply (rule_tac F="is_aligned (lookup_pd_slot pd vptr) 7"
                              in corres_gen_asm)
                apply (simp add: is_aligned_mask[symmetric])
                apply (rule corres_split)
                   apply (rule_tac P="page_directory_at pd and pspace_aligned and valid_etcbs
                                         and K (valid_unmap sz (asid, vptr))"
                               in corres_mapM [where r=dc], simp, simp)
                       prefer 5
                       apply (rule order_refl)
                      apply clarsimp
                      apply (rule corres_guard_imp, rule storePDE_corres')
                        apply (simp add:pde_relation_aligned_def)+
                       apply clarsimp
                       apply (rule pde_at_aligned_vptr)
                          apply (simp add: superSectionPDEOffsets_def pde_bits_def)+
                       apply (simp add: lookup_pd_slot_def vspace_bits_defs)
                       apply (simp add: valid_unmap_def)
                      apply assumption
                     apply (wp | simp | wp (once) hoare_drop_imps)+
                  apply (rule corres_machine_op)
                  apply (clarsimp simp: last_byte_pde_def objBits_simps archObjSize_def)
                  apply (rule corres_Id, rule refl, simp)
                  apply (rule no_fail_cleanCacheRange_PoU)
                 apply (wpsimp | wp (once) hoare_drop_imps)+
             apply (clarsimp simp: valid_unmap_def page_directory_pde_at_lookupI
                                   lookup_pd_slot_aligned_6 pg_entry_align_def
                                   pd_aligned vmsz_aligned_def)
            apply simp
           apply clarsimp
           apply (rule flushPage_corres)
          apply wp
          apply (rule_tac Q'="\<lambda>_. invs and vspace_at_asid asid pda" in hoare_post_imp_R)
           apply (wpsimp wp: lookup_pt_slot_inv lookup_pt_slot_cap_to2' lookup_pt_slot_cap_to_multiple2
                             store_pde_invs_unmap store_pde_pd_at_asid mapM_swp_store_pde_invs_unmap
                         simp: largePagePTEOffsets_def pte_bits_def
                 | wp hoare_drop_imps
                 | wp mapM_wp' | assumption)+
          apply auto[1]
         apply (wpsimp wp: hoare_vcg_const_imp_lift_R lookupPTSlot_inv
               | strengthen not_in_global_refs_vs_lookup
                 page_directory_at_lookup_mask_aligned_strg
                 page_directory_at_lookup_mask_add_aligned_strg
               | wp hoare_vcg_const_Ball_lift_R mapM_wp')+
   apply (clarsimp simp add: valid_unmap_def valid_asid_def)
   apply (case_tac sz)
      apply (auto simp: invs_def valid_state_def
        valid_arch_state_def pageBits_def
        superSectionPDEOffsets_def pde_bits_def
        valid_arch_caps_def vmsz_aligned_def)
  done

definition
  "flush_type_map type \<equiv> case type of
     ARM_A.flush_type.Clean \<Rightarrow> ARM_HYP_H.flush_type.Clean
   | ARM_A.flush_type.Invalidate \<Rightarrow> ARM_HYP_H.flush_type.Invalidate
   | ARM_A.flush_type.CleanInvalidate \<Rightarrow> ARM_HYP_H.flush_type.CleanInvalidate
   | ARM_A.flush_type.Unify \<Rightarrow> ARM_HYP_H.flush_type.Unify"

lemma doFlush_corres:
  "corres_underlying Id nf nf' dc \<top> \<top>
             (do_flush typ start end pstart) (doFlush (flush_type_map typ) start end pstart)"
  apply (simp add: do_flush_def doFlush_def)
  apply (cases "typ", simp_all add: flush_type_map_def Let_def)
     apply (rule corres_Id [where r=dc], rule refl, simp)
     apply (wp no_fail_cleanCacheRange_RAM)
    apply (rule corres_Id [where r=dc], rule refl, simp)
    apply (wp no_fail_invalidateCacheRange_RAM)
   apply (rule corres_Id [where r=dc], rule refl, simp)
   apply (wp no_fail_cleanInvalidateCacheRange_RAM)
  apply (rule corres_Id [where r=dc], rule refl, simp)
  apply (rule no_fail_pre, wp add: no_fail_cleanCacheRange_PoU no_fail_invalidateCacheRange_I
                              no_fail_dsb no_fail_isb del: no_irq)
  apply clarsimp
  done

definition
  "page_directory_invocation_map pdi pdi' \<equiv> case pdi of
    ARM_A.PageDirectoryNothing \<Rightarrow> pdi' = PageDirectoryNothing
  | ARM_A.PageDirectoryFlush typ start end pstart pd asid \<Rightarrow>
      pdi' = PageDirectoryFlush (flush_type_map typ) start end pstart pd asid"

lemma performPageDirectoryInvocation_corres:
  "page_directory_invocation_map pdi pdi' \<Longrightarrow>
   corres dc (invs and valid_pdi pdi)
             (valid_objs' and pspace_aligned' and pspace_distinct' and no_0_obj'
               and cur_tcb' and valid_arch_state')
             (perform_page_directory_invocation pdi) (performPageDirectoryInvocation pdi')"
  apply (simp add: perform_page_directory_invocation_def performPageDirectoryInvocation_def)
  apply (cases pdi)
   apply (clarsimp simp: page_directory_invocation_map_def)
   apply (rule corres_guard_imp)
     apply (rule corres_when, simp)
     apply (rule corres_split[OF setVMRootForFlush_corres])
       apply (rule corres_split[OF corres_machine_op])
          apply (rule doFlush_corres)
         apply (rule corres_when, simp)
         apply (rule corres_split[OF getCurThread_corres])
           apply clarsimp
           apply (rule setVMRoot_corres)
          apply wp+
        apply (simp add: cur_tcb_def[symmetric])
        apply (wp hoare_drop_imps)
       apply (simp add: cur_tcb'_def[symmetric])
       apply (wp hoare_drop_imps)+
    apply clarsimp
    apply (auto simp: valid_pdi_def)[2]
  apply (clarsimp simp: page_directory_invocation_map_def)
  done

definition
  "page_invocation_map pgi pgi' \<equiv> case pgi of
    ARM_A.PageMap a c ptr m \<Rightarrow>
      \<exists>c' m'. pgi' = PageMap a c' (cte_map ptr) m' \<and>
              cap_relation c c' \<and>
              mapping_map m m'
  | ARM_A.PageUnmap c ptr \<Rightarrow>
      \<exists>c'. pgi' = PageUnmap c' (cte_map ptr) \<and>
         acap_relation c c'
  | ARM_A.PageFlush typ start end pstart pd asid \<Rightarrow>
      pgi' = PageFlush (flush_type_map typ) start end pstart pd asid
  | ARM_A.PageGetAddr ptr \<Rightarrow>
      pgi' = PageGetAddr ptr"

definition
  "valid_pde_slots' m \<equiv> case m of Inl (pte, xs) \<Rightarrow> True
           | Inr (pde, xs) \<Rightarrow> \<forall>x \<in> set xs. valid_pde_mapping' (x && mask pdBits) pde"

definition
  "vs_entry_align obj \<equiv>
   case obj of KOArch (KOPTE pte) \<Rightarrow> pte_align' pte
             | KOArch (KOPDE pde) \<Rightarrow> pde_align' pde
             | _ \<Rightarrow> 0"

definition "valid_slots_duplicated' \<equiv> \<lambda>m s. case m of
  Inl (pte, xs) \<Rightarrow> (case pte of
    pte.LargePagePTE _ _ _ _ \<Rightarrow> \<exists>p. xs = [p, p+8 .e. p + mask 7] \<and> is_aligned p 7
        \<and> page_table_at' (p && ~~ mask ptBits) s
    | _ \<Rightarrow> \<exists>p. xs = [p] \<and> ko_wp_at' (\<lambda>ko. vs_entry_align ko = 0) p s
      \<and> page_table_at' (p && ~~ mask ptBits) s)
  | Inr (pde, xs) \<Rightarrow> (case pde of
    pde.SuperSectionPDE _ _ _ _ \<Rightarrow> \<exists>p. xs = [p, p+8 .e. p + mask 7] \<and> is_aligned p 7
        \<and> page_directory_at' (p && ~~ mask pdBits) s
    | _ \<Rightarrow> \<exists>p. xs = [p] \<and> ko_wp_at' (\<lambda>ko. vs_entry_align ko = 0) p s
      \<and> page_directory_at' (p && ~~ mask pdBits) s)"

lemma valid_slots_duplicated_pteD':
  assumes "valid_slots_duplicated' (Inl (pte, xs)) s"
  shows "(is_aligned (hd xs >> pte_bits) (pte_align' pte))
     \<and> (\<forall>p \<in> set (tl xs). \<not> is_aligned (p >> pte_bits) (pte_align' pte))"
proof -
  have is_aligned_estimate:
    "\<And>x. is_aligned (x::word32) 4 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> 2 ^ 4 \<le> x"
    apply (simp add:is_aligned_mask mask_def)
    apply word_bitwise
    apply auto
    done
  show ?thesis
  using assms
  apply -
  apply (clarsimp simp:valid_slots_duplicated'_def pte_bits_def
    split:ARM_HYP_H.pte.splits)
  apply (subgoal_tac "p \<le> p + mask 7")
   apply (clarsimp simp:upto_enum_step_def not_less vspace_bits_defs)
   apply (intro conjI impI,simp)
    apply (simp add:hd_map_simp mask_def is_aligned_shiftr upto_enum_word vspace_bits_defs)
   apply (clarsimp simp:mask_def upto_enum_word vspace_bits_defs)
   apply (subst (asm) tl_map_simp upto_enum_word)
    apply simp
   apply (clarsimp simp:image_def)
   apply (cut_tac w = "of_nat x :: word32" in shiftl_t2n[where n = pte_bits,simplified,symmetric])
   apply (clarsimp simp:field_simps)
   apply (drule is_aligned_shiftl[where n = 7 and m = 3, simplified])
   apply (subst (asm) shiftr_shiftl1)
    apply simp
   apply (simp add: tl_nat_list_simp pte_bits_def)
   apply (subst (asm) is_aligned_neg_mask_eq)
    apply (erule aligned_add_aligned[OF _ is_aligned_shiftl_self])
    apply simp
   apply (drule(1) is_aligned_addD1)
   apply (drule_tac w = "(of_nat x::word32) << 3" in
     is_aligned_shiftr[where n = 4 and m = 3,simplified])
   apply (clarsimp simp: shiftl_shiftr_id word_of_nat_less)+
   apply (drule is_aligned_estimate)
    apply (rule of_nat_neq_0)
     apply simp
    apply simp
   apply (drule unat_le_helper)
   apply simp
  apply (erule is_aligned_no_wrap')
  apply (simp add:mask_def)
  done
qed

lemma valid_slots_duplicated_pdeD':
  assumes "valid_slots_duplicated' (Inr (pde, xs)) s"
  shows "(is_aligned (hd xs >> pde_bits) (pde_align' pde))
     \<and> (\<forall>p \<in> set (tl xs). \<not> is_aligned (p >> pde_bits) (pde_align' pde))"
proof -
  have is_aligned_estimate:
    "\<And>x. is_aligned (x::word32) 4 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> 2 ^ 4 \<le> x"
    apply (simp add:is_aligned_mask mask_def)
    apply word_bitwise
    apply auto
    done
  show ?thesis
  using assms
  apply -
  apply (clarsimp simp:valid_slots_duplicated'_def pte_bits_def
    split:ARM_HYP_H.pde.splits)
  apply (subgoal_tac "p \<le> p + mask 7")
   apply (clarsimp simp:upto_enum_step_def not_less)
   apply (intro conjI impI,simp)
    apply (simp add:hd_map_simp mask_def is_aligned_shiftr upto_enum_word pde_bits_def)
   apply (clarsimp simp:mask_def upto_enum_word)
   apply (subst (asm) tl_map_simp upto_enum_word)
    apply simp
   apply (clarsimp simp:image_def)
   apply (cut_tac w = "of_nat x :: word32" in shiftl_t2n[where n = 3,simplified,symmetric])
   apply (clarsimp simp:field_simps vspace_bits_defs)
   apply (drule is_aligned_shiftl[where n = 7 and m = 3,simplified])
   apply (subst (asm) shiftr_shiftl1)
    apply simp
   apply (simp add: tl_nat_list_simp)
   apply (subst (asm) is_aligned_neg_mask_eq)
    apply (erule aligned_add_aligned[OF _ is_aligned_shiftl_self])
    apply simp
   apply (drule(1) is_aligned_addD1)
   apply (drule_tac w = "(of_nat x::word32) << 3" in
     is_aligned_shiftr[where n = 4 and m = 3,simplified])
   apply (clarsimp simp: shiftl_shiftr_id word_of_nat_less)+
   apply (drule is_aligned_estimate)
    apply (rule of_nat_neq_0)
     apply simp
    apply simp
   apply (drule unat_le_helper)
   apply simp
  apply (erule is_aligned_no_wrap')
  apply (simp add:mask_def)
  done
qed

lemma setCTE_vs_entry_align[wp]:
  "\<lbrace>\<lambda>s. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p s\<rbrace>
    setCTE ptr cte
  \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p\<rbrace>"
  apply (clarsimp simp: setCTE_def setObject_def split_def
                        valid_def in_monad ko_wp_at'_def
             split del: if_split
                 elim!: rsubst[where P=P])
  apply (drule(1) updateObject_cte_is_tcb_or_cte [OF _ refl, rotated])
  apply (elim exE conjE disjE)
   apply (clarsimp simp: ps_clear_upd objBits_simps
                         lookupAround2_char1)
   apply (simp add:vs_entry_align_def)
  apply (clarsimp simp: ps_clear_upd objBits_simps vs_entry_align_def)
  done

lemma updateCap_vs_entry_align[wp]:
 "\<lbrace>ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p \<rbrace> updateCap ptr cap
  \<lbrace>\<lambda>rv. ko_wp_at' (\<lambda>ko. P (vs_entry_align ko)) p\<rbrace>"
  apply (simp add:updateCap_def)
  apply wp
  done

lemma valid_slots_duplicated_updateCap[wp]:
  "\<lbrace>valid_slots_duplicated' m'\<rbrace> updateCap cap c'
  \<lbrace>\<lambda>rv s. valid_slots_duplicated' m' s\<rbrace>"
  apply (case_tac m')
   apply (simp_all add:valid_slots_duplicated'_def)
   apply (case_tac a,case_tac aa,simp_all)
     apply (wp hoare_vcg_ex_lift)+
  apply (case_tac b,case_tac a,simp_all)
     apply (wp hoare_vcg_ex_lift)+
  done

definition
  "valid_page_inv' pgi \<equiv> case pgi of
    PageMap asid cap ptr m \<Rightarrow>
      cte_wp_at' (is_arch_update' cap) ptr and valid_slots' m and valid_cap' cap
          and K (valid_pde_slots' m) and (valid_slots_duplicated' m)
  | PageUnmap cap ptr \<Rightarrow>
      \<lambda>s. \<exists>d r R sz m. cap = PageCap d r R sz m \<and>
          cte_wp_at' (is_arch_update' (ArchObjectCap cap)) ptr s \<and>
          s \<turnstile>' (ArchObjectCap cap)
  | PageFlush typ start end pstart pd asid \<Rightarrow> \<top>
  | PageGetAddr ptr \<Rightarrow> \<top>"

crunch ctes[wp]: doMachineOp "\<lambda>s. P (ctes_of s)"

lemma setObject_vcpu_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace>
     setObject ptr (vcpu::vcpu)
   \<lbrace>\<lambda>rv s. P (cte_wp_at' P' p s)\<rbrace>"
  apply (wp setObject_cte_wp_at2'[where Q="\<top>"])
    apply (clarsimp simp: updateObject_default_def in_monad
                          projectKO_opts_defs projectKOs)
                         apply (rule equals0I)
   apply (clarsimp simp: updateObject_default_def in_monad
                         projectKOs projectKO_opts_defs)
  apply simp
  done

crunches vcpuSave, vcpuRestore, vcpuDisable, vcpuEnable
  for ctes[wp]: "\<lambda>s. P (ctes_of s)"
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

lemma vcpuSwitch_ctes[wp]: "\<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> vcpuSwitch vcpu \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

crunch ctes [wp]: unmapPage "\<lambda>s. P (ctes_of s)"
  (simp: crunch_simps
     wp: crunch_wps loadObject_default_inv getObject_inv)

lemma triple_set_zip_eq:
  "(a, b, c) \<in> set (zip ys (zip ys xs)) \<Longrightarrow> a = b \<and> a \<in> set ys"
  apply (induct ys arbitrary: xs; clarsimp)
  apply (case_tac xs, auto)
  done

lemma corres_store_pde_with_invalid_tail:
  "\<lbrakk> \<forall>slot \<in>set ys. \<not> is_aligned (slot >> pde_bits) (pde_align' ab); length ys < 2^word_bits \<rbrakk>
  \<Longrightarrow>corres dc ((\<lambda>s. \<forall>y\<in> set ys. pde_at y s) and pspace_aligned and valid_etcbs)
           (pspace_aligned' and pspace_distinct')
           (mapM (swp store_pde ARM_A.pde.InvalidPDE) ys)
           (mapM (\<lambda>(slot, i). storePDE slot (addPDEOffset ab i)) (zip ys [1.e.of_nat (length ys)]))"
  apply (rule_tac S ="{(x,y). x = fst y \<and> x \<in> set ys}" in corres_mapM[where r = dc and r' = dc])
        apply simp
       apply simp
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (rule storePDE_corres')
        apply (drule bspec)
         apply simp
        apply (simp add:pde_relation_aligned_def addPDEOffset_def)
        apply (auto split: pde.splits)[1]
       apply (drule bspec,simp)
       apply simp
      apply simp
     apply (wpsimp wp: hoare_vcg_ball_lift)+
   apply (simp add: word_bits_def unat_of_nat_word_bits)
  apply (fastforce dest: triple_set_zip_eq)
  done

lemma corres_store_pte_with_invalid_tail:
  "\<lbrakk> \<forall>slot\<in> set ys. \<not> is_aligned (slot >> pte_bits) (pte_align' aa); length ys < 2^word_bits\<rbrakk>
  \<Longrightarrow> corres dc ((\<lambda>s. \<forall>y\<in>set ys. pte_at y s) and pspace_aligned and valid_etcbs)
                (pspace_aligned' and pspace_distinct')
             (mapM (swp store_pte ARM_A.pte.InvalidPTE) ys)
             (mapM (\<lambda>(slot, i). storePTE slot (addPTEOffset aa i)) (zip ys [1.e.of_nat (length ys)]))"
  apply (rule_tac S ="{(x,y). x = fst y \<and> x \<in> set ys}" in corres_mapM[where r = dc and r' = dc])
        apply simp
       apply simp
      apply clarsimp
      apply (rule corres_guard_imp)
        apply (rule storePTE_corres')
        apply (drule bspec)
         apply simp
        apply (simp add:pte_relation_aligned_def addPTEOffset_def)
        apply (auto split: pte.splits)[1]
       apply (drule bspec,simp)
       apply simp
      apply simp
     apply (wpsimp wp: hoare_vcg_ball_lift)+
   apply (simp add: word_bits_def unat_of_nat_word_bits)
  apply (fastforce dest: triple_set_zip_eq)
  done

lemma updateCap_valid_slots'[wp]:
  "\<lbrace>valid_slots' x2\<rbrace> updateCap cte cte' \<lbrace>\<lambda>_ s. valid_slots' x2 s \<rbrace>"
  apply (case_tac x2)
   apply (clarsimp simp:valid_slots'_def)
   apply (wp hoare_vcg_ball_lift)
  apply (clarsimp simp:valid_slots'_def)
  apply (wp hoare_vcg_ball_lift)
  done

lemma pteCheckIfMapped_corres:
  "corres (=) (pte_at slot) ((\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and pspace_aligned' and pspace_distinct') (pte_check_if_mapped slot) (pteCheckIfMapped slot)"
  apply (simp add: pte_check_if_mapped_def pteCheckIfMapped_def)
    apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_master_pte_corres', simplified])
      apply (rule corres_return[where P="pte_at slot" and
                          P'="pspace_aligned' and pspace_distinct'", THEN iffD2])
      apply (clarsimp simp: master_pte_relation_def isLargePage_def' split: if_split_asm)
      apply (case_tac pt, simp_all)[1]
     apply wp+
   apply (simp)
  apply simp
  done

lemma pdeCheckIfMapped_corres:
  "corres (=) (pde_at slot) ((\<lambda>s. vs_valid_duplicates' (ksPSpace s)) and pspace_aligned' and pspace_distinct') (pde_check_if_mapped slot) (pdeCheckIfMapped slot)"
  apply (simp add: pde_check_if_mapped_def pdeCheckIfMapped_def)
    apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_master_pde_corres', simplified])
      apply (rule corres_return[where P="pde_at slot" and
                          P'="pspace_aligned' and pspace_distinct'", THEN iffD2])
      apply (clarsimp simp: master_pde_relation_def isSuperSection_def' split: if_split_asm)
      apply (case_tac pd, simp_all)[1]
     apply wp+
   apply (clarsimp simp: pte_relation_aligned_def split: if_split_asm)
  apply simp
  done

crunch valid_asid_map[wp]: store_pte "valid_asid_map"

lemma set_cap_pd_at_asid [wp]:
  "\<lbrace>vspace_at_asid asid pd\<rbrace> set_cap t st \<lbrace>\<lambda>rv. vspace_at_asid asid pd\<rbrace>"
  apply (simp add: vspace_at_asid_def)
  apply wp
  done

lemma set_cap_valid_slots_inv[wp]:
  "\<lbrace>valid_slots m\<rbrace> set_cap t st \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  by (cases m, (clarsimp simp: valid_slots_def, wp hoare_vcg_ball_lift set_cap.vs_lookup set_cap_typ_ats)+)

lemma set_cap_same_refs_inv[wp]:
  "\<lbrace>\<lambda>s. same_refs m cap s\<rbrace> set_cap t st \<lbrace>\<lambda>rv s. same_refs m cap s\<rbrace>"
  by (cases m, (clarsimp simp: same_refs_def, wp)+)

definition
  "valid_page_map_inv asid cap ptr m \<equiv> (\<lambda>s. caps_of_state s ptr = Some cap) and same_refs m cap and
  valid_slots m and
  valid_cap cap and
  K (is_pg_cap cap \<and> empty_refs m \<and> asid \<le> mask asid_bits \<and> asid \<noteq> 0) and
  (\<lambda>s. \<exists>sl. cte_wp_at (parent_for_refs m) sl s) and
  (\<lambda>s. \<exists>pd. vspace_at_asid asid pd s)"

lemma set_cap_valid_page_map_inv:
  "\<lbrace>valid_page_inv (ARM_A.page_invocation.PageMap asid cap slot m)\<rbrace> set_cap cap slot \<lbrace>\<lambda>rv. valid_page_map_inv asid cap slot m\<rbrace>"
  apply (simp add: valid_page_inv_def valid_page_map_inv_def)
  apply (wp set_cap_cte_wp_at_cases hoare_vcg_ex_lift| simp)+
  apply clarsimp
  apply (rule conjI, fastforce simp: cte_wp_at_def)
  apply (rule_tac x=a in exI, rule_tac x=b in exI)
  apply (subgoal_tac "(a,b) \<noteq> slot")
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_def parent_for_refs_def)
  apply (auto simp: is_pt_cap_def is_pg_cap_def is_pd_cap_def split: sum.splits)
  done

lemma setCTE_valid_duplicates'[wp]:
 "\<lbrace>\<lambda>s. vs_valid_duplicates' (ksPSpace s)\<rbrace>
  setCTE p cte \<lbrace>\<lambda>rv s. vs_valid_duplicates' (ksPSpace s)\<rbrace>"
  apply (simp add:setCTE_def)
  apply (clarsimp simp: setObject_def split_def valid_def in_monad
                        projectKOs pspace_aligned'_def ps_clear_upd
                        objBits_def[symmetric] lookupAround2_char1
                 split: if_split_asm)
  apply (frule pspace_storable_class.updateObject_type[where v = cte,simplified])
  apply (clarsimp simp:ObjectInstances_H.updateObject_cte assert_def bind_def
    alignCheck_def in_monad when_def alignError_def magnitudeCheck_def
    assert_opt_def return_def fail_def typeError_def
    split:if_splits option.splits Structures_H.kernel_object.splits)
     apply (erule valid_duplicates'_non_pd_pt_I[rotated 3],simp+)+
  done

crunch valid_duplicates'[wp]: updateCap "\<lambda>s. vs_valid_duplicates' (ksPSpace s)"
  (wp: crunch_wps
   simp: crunch_simps unless_def)


lemma message_info_to_data_eqv:
  "wordFromMessageInfo (message_info_map mi) = message_info_to_data mi"
  apply (cases mi)
  apply (simp add: wordFromMessageInfo_def
    msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def
    shiftL_nat)
  done

lemma message_info_from_data_eqv:
  "message_info_map (data_to_message_info rv) = messageInfoFromWord rv"
  by (auto simp: data_to_message_info_def messageInfoFromWord_def Let_def not_less
                 msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def mask_def
                 shiftL_nat msgMaxLength_def msgLabelBits_def)

lemma setMessageInfo_corres:
 "mi' = message_info_map mi \<Longrightarrow>
  corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
    (set_message_info t mi) (setMessageInfo t mi')"
  apply (simp add: setMessageInfo_def set_message_info_def)
  apply (subgoal_tac "wordFromMessageInfo (message_info_map mi) =
                      message_info_to_data mi")
   apply (simp add: asUser_setRegister_corres msg_info_register_def
                    msgInfoRegister_def)
  apply (simp add: message_info_to_data_eqv)
  done


lemma set_mi_invs'[wp]: "\<lbrace>invs' and tcb_at' t\<rbrace> setMessageInfo t a \<lbrace>\<lambda>x. invs'\<rbrace>"
  by (simp add: setMessageInfo_def) wp

lemma set_mi_tcb' [wp]:
  "\<lbrace> tcb_at' t \<rbrace> setMessageInfo receiver msg \<lbrace>\<lambda>rv. tcb_at' t\<rbrace>"
  by (simp add: setMessageInfo_def) wp


lemma setMRs_typ_at':
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  by (simp add: setMRs_def zipWithM_x_mapM split_def, wp crunch_wps)

lemmas setMRs_typ_at_lifts[wp] = typ_at_lifts [OF setMRs_typ_at']

lemma set_mrs_invs'[wp]:
  "\<lbrace> invs' and tcb_at' receiver \<rbrace> setMRs receiver recv_buf mrs \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: setMRs_def)
  apply (wp dmo_invs' no_irq_mapM no_irq_storeWord crunch_wps|
         simp add: zipWithM_x_mapM split_def)+
  done

lemma same_refs_vs_cap_ref_eq:
  assumes "valid_slots entries s"
  assumes "same_refs entries cap s"
  assumes "same_refs entries cap' s"
  shows "vs_cap_ref cap = vs_cap_ref cap'"
  using assms
  apply (cases entries; clarsimp simp: same_refs_def valid_slots_def)
  apply (all \<open>rename_tac pte slots p; case_tac slots; clarsimp\<close>)
  done

lemma addPAddr_0[simp]:
  "addPAddr p 0 = p"
  by (cases p; simp add: addPAddr_def fromPAddr_def)

lemma addPTEOffset_0[simp]:
  "addPTEOffset pte 0 = pte"
  by (cases pte; simp add: addPTEOffset_def pteFrame_def pteFrame_update_def)

lemma addPDEOffset_0[simp]:
  "addPDEOffset pde 0 = pde"
  by (cases pde; simp add: addPDEOffset_def pdeFrame_def pdeFrame_update_def)

lemma zip_cons_idx[simp]:
  "length ys < 2 ^ LENGTH('a) \<Longrightarrow>
  zip (y # ys) [0.e.of_nat (length ys)] = (y,0) # zip ys [1.e.of_nat (length ys)::'a::len word]"
  by (clarsimp simp: upto_enum_def unat_of_nat_eq not_le Suc_le_eq upto_0_to_n2)

lemma valid_slots_duplicated'_length_Inl:
  "valid_slots_duplicated' (Inl (a, b)) s
   \<Longrightarrow> length b = (case a of LargePagePTE _ _ _ _ \<Rightarrow> 16 | _ \<Rightarrow> 1)"
  by (auto simp: valid_slots_duplicated'_def upto_enum_step_def upto_enum_def mask_def
           dest: is_aligned_no_overflow'
          split: pte.splits)

lemma valid_slots_duplicated'_length_Inr:
  "valid_slots_duplicated' (Inr (a, b)) s
   \<Longrightarrow> length b = (case a of SuperSectionPDE _ _ _ _ \<Rightarrow> 16 | _ \<Rightarrow> 1)"
  by (auto simp: valid_slots_duplicated'_def upto_enum_step_def upto_enum_def mask_def
           dest: is_aligned_no_overflow'
          split: pde.splits)

lemma performPageInvocation_corres:
  assumes "page_invocation_map pgi pgi'"
  shows "corres (=) (invs and valid_etcbs and valid_page_inv pgi)
            (invs' and valid_page_inv' pgi' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s)))
            (perform_page_invocation pgi) (performPageInvocation pgi')"
proof -
  have pull_out_P:
    "\<And>P s Q c p. P s \<and> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> Q s c) \<longrightarrow> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> P s \<and> Q s c)"
   by blast
  show ?thesis
  using assms
  apply (cases pgi)
      apply (rename_tac word cap prod sum)
     \<comment> \<open>PageMap\<close>
     apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def page_invocation_map_def)
     apply (rule corres_guard_imp)
       apply (rule_tac R="\<lambda>_. invs and (valid_page_map_inv word cap (a,b) sum) and valid_etcbs
                          and (\<lambda>s. caps_of_state s (a,b) = Some cap)"
                and R'="\<lambda>_. invs' and valid_slots' m' and pspace_aligned' and valid_slots_duplicated' m'
                        and pspace_distinct' and (\<lambda>s. vs_valid_duplicates' (ksPSpace s))" in corres_split)
          apply (erule updateCap_same_master)
         apply (case_tac sum, case_tac aa)
          apply (rename_tac slots)
          apply (clarsimp simp: mapping_map_def valid_slots'_def valid_slots_def valid_page_inv_def
                                neq_Nil_conv valid_page_map_inv_def)
          apply (rule corres_name_pre)
          apply (subgoal_tac "length slots \<le> 16")
           prefer 2
           apply clarsimp
           apply (drule valid_slots_duplicated'_length_Inl)
           apply (fastforce split: pte.splits)
          apply (clarsimp simp: mapM_Cons bind_assoc split del: if_split)
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF pteCheckIfMapped_corres])
              apply (rule corres_split[OF storePTE_corres'])
                 apply (clarsimp simp: pte_relation_aligned_def)
                 apply (clarsimp dest!: valid_slots_duplicated_pteD')
                apply (rule corres_split[where r' = dc, OF corres_store_pte_with_invalid_tail])
                    apply (clarsimp simp: pte_relation_aligned_def)
                    apply (clarsimp dest!: valid_slots_duplicated_pteD')
                   apply (clarsimp simp: word_bits_def)
                  apply (rule corres_split[where r'=dc, OF corres_machine_op[OF corres_Id]])
                       apply (simp add: last_byte_pte_def objBits_simps archObjSize_def)
                      apply simp
                     apply (rule no_fail_cleanCacheRange_PoU)
                    apply (rule corres_split[where r'=dc, OF _ corres_return_eq_same[OF refl]])
                      apply (clarsimp simp add: when_def)
                      apply (rule invalidate_tlb_by_asid_corres_ex)
                     apply wp
                    apply wp
                   apply (wpsimp, safe; wpsimp wp: hoare_vcg_ex_lift)
                  apply wpsimp
                 apply (rule_tac Q="\<lambda>_. K (word \<le> mask asid_bits \<and> word \<noteq> 0) and invs
                                    and (\<lambda>s. \<exists>pd. vspace_at_asid word pd s)" in hoare_strengthen_post)
                  prefer 2
                  apply auto[1]
                 apply (wp mapM_swp_store_pte_invs[where pte="ARM_A.pte.InvalidPTE", simplified]
                           hoare_vcg_ex_lift)
                 apply (wp mapM_UNIV_wp
                        | clarsimp simp add: swp_def split: prod.split simp del: fun_upd_apply)+
               apply (clarsimp simp del: fun_upd_apply simp add: cte_wp_at_caps_of_state)
               apply (wp add: hoare_vcg_const_Ball_lift store_pte_typ_at store_pte_cte_wp_at
                              hoare_vcg_ex_lift)+
            apply (wp | simp add: pteCheckIfMapped_def)+
           apply (clarsimp simp: cte_wp_at_caps_of_state valid_slots_def parent_for_refs_def
                                 empty_refs_def invs_psp_aligned
                       simp del: fun_upd_apply)
           apply (rule conjI)
            apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
            apply (clarsimp simp: is_pt_cap_def cap_asid_def image_def neq_Nil_conv Collect_disj_eq
                           split: Structures_A.cap.splits arch_cap.splits option.splits)
           apply (rule conjI)
            apply clarsimp
            apply (drule same_refs_lD)
            apply (rule_tac x=a in exI, rule_tac x=b in exI)
            apply clarify
            apply (drule_tac x=refa in spec)
            apply (clarsimp simp add: vspace_bits_defs)
           apply (rule conjI[rotated])
            apply (fold_subgoals (prefix))[3]
  subgoal apply (unfold_subgoals) by (fastforce simp add: vspace_bits_defs)+
         apply (case_tac ba)
         apply (rename_tac slots)
         apply (clarsimp simp: mapping_map_def valid_slots_def valid_slots'_def neq_Nil_conv
                               valid_page_inv_def valid_page_map_inv_def)
         apply (rule corres_name_pre)
         apply (subgoal_tac "length slots \<le> 16")
          prefer 2
          apply clarsimp
          apply (drule valid_slots_duplicated'_length_Inr)
          apply (fastforce split: pde.splits)
         apply (clarsimp simp:mapM_Cons bind_assoc split del:if_split)
         apply (rule corres_guard_imp)
           apply (rule corres_split[OF pdeCheckIfMapped_corres])
             apply (rule corres_split[OF storePDE_corres'])
                apply (clarsimp simp: pde_relation_aligned_def)
                apply (clarsimp dest!: valid_slots_duplicated_pdeD')
               apply (rule corres_split[where r'=dc, OF corres_store_pde_with_invalid_tail])
                   apply (clarsimp simp: pde_relation_aligned_def)
                   apply (clarsimp dest!: valid_slots_duplicated_pdeD')
                  apply (simp add: word_bits_def)
                 apply (rule corres_split[where r'=dc,OF corres_machine_op[OF corres_Id]])
                      apply (simp add: last_byte_pde_def objBits_simps archObjSize_def)
                     apply simp
                    apply (rule no_fail_cleanCacheRange_PoU)
                   apply (rule corres_split[where r'=dc, OF _ corres_return_eq_same[OF refl]])
                     apply (clarsimp simp: when_def)
                     apply (rule invalidate_tlb_by_asid_corres_ex)
                    apply wp
                   apply wp
                  apply (wpsimp, safe ; wpsimp wp: hoare_vcg_ex_lift)
                 apply wpsimp
                apply (rule_tac Q="\<lambda>_. K (word \<le> mask asid_bits \<and> word \<noteq> 0) and invs
                                   and (\<lambda>s. \<exists>pd. vspace_at_asid word pd s)" in hoare_strengthen_post)
                 prefer 2
                 apply auto[1]
                apply (wp mapM_swp_store_pde_invs_unmap[where pde="ARM_A.pde.InvalidPDE", simplified]
                          hoare_vcg_ex_lift)
                apply (wp mapM_UNIV_wp store_pde_pd_at_asid | clarsimp simp add: swp_def)+
              apply (clarsimp simp add: cte_wp_at_caps_of_state  simp del: fun_upd_apply)
              apply (wp hoare_vcg_const_Ball_lift store_pde_typ_at hoare_vcg_ex_lift store_pde_pd_at_asid)
              apply (rule hoare_vcg_conj_lift)
               apply (rule_tac slots="y # ys" in store_pde_invs_unmap')
              apply (wp hoare_vcg_const_Ball_lift store_pde_pd_at_asid hoare_vcg_ex_lift)
             apply (wp | simp add: pdeCheckIfMapped_def)+
          apply (clarsimp simp add: cte_wp_at_caps_of_state valid_slots_def parent_for_refs_def
                                    empty_refs_def invs_psp_aligned
                          simp del: fun_upd_apply)
          apply (rule conjI, rule_tac x=ref in exI, clarsimp)
          apply (rule conjI)
           apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
           apply (auto simp add: arch_cap_fun_lift_def)[1]
          apply (rule conjI)
           apply (rule_tac x=a in exI, rule_tac x=b in exI, auto simp: same_refs_def)[1]
          apply (rule conjI)
           apply (clarsimp simp: pde_at_def obj_at_def
                                 caps_of_state_cteD'[where P=\<top>, simplified])
           apply (drule_tac cap="cap.ArchObjectCap acap" and ptr="(aa,ba)"
                         in valid_global_refsD[OF invs_valid_global_refs])
             apply assumption+
           apply (clarsimp simp: cap_range_def)
          apply (rule conjI)
           apply (clarsimp simp: pde_at_def obj_at_def a_type_def)
           apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                                  ARM_A.arch_kernel_obj.splits)
          apply (rule conjI[rotated], fastforce)
          apply (erule ballEI)
          apply (clarsimp simp: pde_at_def obj_at_def
                                caps_of_state_cteD'[where P=\<top>, simplified])
          apply (drule_tac cap="cap.ArchObjectCap acap" and ptr="(aa,ba)"
                         in valid_global_refsD[OF invs_valid_global_refs])
            apply assumption+
          apply (drule_tac x=x in imageI[where f="\<lambda>x. x && ~~ mask pd_bits"])
          apply (drule (1) subsetD)
          apply (clarsimp simp: cap_range_def)
         apply clarsimp
        apply (wp arch_update_cap_invs_map set_cap_valid_page_map_inv)
       apply (wp arch_update_updateCap_invs)
      apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct valid_page_inv_def
                            cte_wp_at_caps_of_state is_arch_update_def is_cap_simps
                            cap_master_cap_simps)
      apply (erule (3) subst[OF same_refs_vs_cap_ref_eq, rotated 2])
     apply (clarsimp simp: invs_pspace_aligned' invs_pspace_distinct' valid_page_inv'_def cte_wp_at'_def)
    \<comment> \<open>PageUnmap\<close>
    apply (clarsimp simp: performPageInvocation_def perform_page_invocation_def
                          page_invocation_map_def)
    apply (rule corres_assume_pre)
    apply (clarsimp simp: valid_page_inv_def valid_page_inv'_def isCap_simps is_page_cap_def
                    cong: option.case_cong prod.case_cong)
    apply (case_tac m)
     apply simp
     apply (rule corres_guard_imp)
       apply (rule corres_split[where r'="acap_relation"])
          apply simp
          apply (rule corres_rel_imp)
           apply (rule get_cap_corres_all_rights_P[where P=is_arch_cap], rule refl)
          apply (clarsimp simp: is_cap_simps)
         apply (rule corres_split[where r'=dc, OF _ corres_return_eq_same[OF refl]])
           apply (rule_tac F="is_page_cap cap" in corres_gen_asm)
           apply (rule updateCap_same_master)
           apply (clarsimp simp: is_page_cap_def update_map_data_def)
          apply (wp get_cap_wp getSlotCap_wp)+
      apply (clarsimp simp: cte_wp_at_caps_of_state)
      apply (clarsimp simp: cap_rights_update_def acap_rights_update_def update_map_data_def is_cap_simps)
      apply auto[1]
     apply (auto simp: cte_wp_at_ctes_of)[1]
    apply clarsimp
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule unmapPage_corres)
        apply (rule corres_split[where r'=acap_relation])
           apply simp
           apply (rule corres_rel_imp)
            apply (rule get_cap_corres_all_rights_P[where P=is_arch_cap], rule refl)
           apply (clarsimp simp: is_cap_simps)
          apply (rule corres_split[where r'=dc, OF _ corres_return_eq_same[OF refl]])
            apply (rule_tac F="is_page_cap cap" in corres_gen_asm)
            apply (rule updateCap_same_master)
            apply (clarsimp simp: is_page_cap_def update_map_data_def)
           apply (wp get_cap_wp getSlotCap_wp)+
       apply (simp add: cte_wp_at_caps_of_state)
       apply (strengthen pull_out_P)+
       apply wp
      apply (simp add: cte_wp_at_ctes_of)
      apply wp
     apply (clarsimp simp: valid_unmap_def cte_wp_at_caps_of_state is_cap_simps
                    split: cap.splits arch_cap.splits)
     apply (clarsimp simp: cap_rights_update_def is_page_cap_def cap_master_cap_simps
                           update_map_data_def acap_rights_update_def valid_cap_def mask_def)
     apply auto[1]
     apply (auto simp: cte_wp_at_ctes_of)[1]
   \<comment> \<open>PageFlush\<close>
   apply (clarsimp simp: performPageInvocation_def perform_page_invocation_def
                         page_invocation_map_def)
   apply (rule corres_guard_imp)
     apply (rule corres_split[where r'=dc, OF _ corres_return_eq_same[OF refl]])
       apply (rule corres_when, simp)
       apply (rule corres_split[OF setVMRootForFlush_corres])
         apply (rule corres_split[OF corres_machine_op])
            apply (rule doFlush_corres)
           apply (rule corres_when, simp)
           apply (rule corres_split[OF getCurThread_corres])
             apply simp
             apply (rule setVMRoot_corres)
            apply wp+
          apply (simp add: cur_tcb_def [symmetric] cur_tcb'_def [symmetric])
          apply (wp hoare_drop_imps)
         apply (simp add: cur_tcb_def [symmetric] cur_tcb'_def [symmetric])
         apply (wp hoare_drop_imps)+
    apply (auto simp: valid_page_inv_def invs_vspace_objs[simplified])[2]
  \<comment> \<open>PageGetAddr\<close>
  apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def page_invocation_map_def fromPAddr_def)
  done
qed

definition
  "page_table_invocation_map pti pti' \<equiv> case pti of
     ARM_A.PageTableMap cap ptr pde p \<Rightarrow>
    \<exists>cap' pde'. pti' = PageTableMap cap' (cte_map ptr) pde' p \<and>
                cap_relation cap cap' \<and>
                pde_relation' pde pde' \<and> is_aligned (p >> pde_bits) (pde_align' pde')
   | ARM_A.PageTableUnmap cap ptr \<Rightarrow>
    \<exists>cap'. pti' = PageTableUnmap cap' (cte_map ptr) \<and>
           cap_relation cap (ArchObjectCap cap')"

definition
  "valid_pti' pti \<equiv> case pti of
     PageTableMap cap slot pde pdeSlot \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     ko_wp_at' (\<lambda>ko. vs_entry_align ko = 0) pdeSlot and
     valid_cap' cap and
     valid_pde' pde and
     K (valid_pde_mapping' (pdeSlot && mask pdBits) pde \<and> vs_entry_align (KOArch (KOPDE pde)) = 0)
   | PageTableUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPageTableCap cap)"

lemma clear_page_table_corres:
  "corres dc (pspace_aligned and page_table_at p and valid_etcbs)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pte ARM_A.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])
    (mapM_x (swp storePTE ARM_HYP_H.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])"
  apply (rule_tac F="is_aligned p ptBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: ptBits_def pageBits_def)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow vspace_bits_defs
                   upto_enum_step_red[where us=2, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="(=)"
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pte_at x s \<and> pspace_aligned s \<and> valid_etcbs s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule storePTE_corres')
        apply (simp add:pte_relation_aligned_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule page_table_pte_atI[simplified shiftl_t2n mult.commute, simplified vspace_bits_defs, simplified])
   apply (simp add: ptBits_def pageBits_def pt_bits_def word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

crunch typ_at'[wp]: unmapPageTable "\<lambda>s. P (typ_at' T p s)"
lemmas unmapPageTable_typ_ats[wp] = typ_at_lifts[OF unmapPageTable_typ_at']

lemma performPageTableInvocation_corres:
  "page_table_invocation_map pti pti' \<Longrightarrow>
   corres dc
          (invs and valid_etcbs and valid_pti pti)
          (invs' and valid_pti' pti')
          (perform_page_table_invocation pti)
          (performPageTableInvocation pti')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_page_table_invocation_def performPageTableInvocation_def)
  apply (cases pti)
   apply (clarsimp simp: page_table_invocation_map_def)
   apply (rule corres_guard_imp)
      apply (rule corres_split[OF updateCap_same_master])
         apply assumption
       apply (rule corres_split)
          apply (rule storePDE_corres')
          apply (simp add: pde_relation_aligned_def)
         apply (rule corres_machine_op)
         apply (rule corres_Id, rule refl, simp)
         apply (rule no_fail_cleanByVA_PoU)
        apply (wp set_cap_typ_at)+
    apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state is_arch_update_def)
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                    dest!: cap_master_cap_eqDs)
    apply auto[1]
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
   apply auto[1]
   apply (clarsimp simp:valid_pde_mapping'_def split:ARM_HYP_H.pde.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: page_table_invocation_map_def)
  apply (rule_tac F="is_pt_cap cap" in corres_req)
   apply (clarsimp simp: valid_pti_def)
  apply (clarsimp simp: is_pt_cap_def split_def
                        vspace_bits_defs objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_if[OF refl])
        apply (rule corres_split[OF unmapPageTable_corres])
          apply (rule corres_split_nor)
             apply (rule clear_page_table_corres[simplified ptBits_def pteBits_def, simplified])
            apply (rule corres_machine_op, rule corres_Id)
              apply simp+
           apply wp+
       apply (rule corres_trivial, simp)
      apply (simp add: liftM_def)
      apply (rule corres_split[OF get_cap_corres])
        apply (rule_tac F="is_pt_cap x" in corres_gen_asm)
        apply (rule updateCap_same_master)
        apply (clarsimp simp: is_pt_cap_def update_map_data_def)
       apply ((wp get_cap_wp)+)[2]
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
                  split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+
   apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
              split: option.split_asm)[1]
  apply (auto simp: valid_pti'_def cte_wp_at_ctes_of)
  done

definition
  "asid_pool_invocation_map ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow> Assign asid p (cte_map slot)"

definition
  "isPDCap cap \<equiv> \<exists>p asid. cap = ArchObjectCap (PageDirectoryCap p asid)"

definition
  "valid_apinv' ap \<equiv> case ap of Assign asid p slot \<Rightarrow>
  asid_pool_at' p and cte_wp_at' (isPDCap o cteCap) slot and K
  (0 < asid \<and> asid \<le> 2^asid_bits - 1)"

definition (* ARMHYP: need review *)
  "valid_vcpuinv' vi \<equiv> case vi of
    VCPUSetTCB v t \<Rightarrow> vcpu_at' v and tcb_at' t and ex_nonz_cap_to' v and ex_nonz_cap_to' t
  | VCPUInjectIRQ v n q \<Rightarrow> vcpu_at' v
  | VCPUReadRegister v rg \<Rightarrow> vcpu_at' v
  | VCPUWriteRegister v _ _ \<Rightarrow> vcpu_at' v
  | VCPUAckVPPI v _ \<Rightarrow> vcpu_at' v"

lemma performASIDPoolInvocation_corres:
  "ap' = asid_pool_invocation_map ap \<Longrightarrow>
  corres dc
          (valid_objs and pspace_aligned and pspace_distinct and valid_apinv ap and valid_etcbs)
          (pspace_aligned' and pspace_distinct' and valid_apinv' ap')
          (perform_asid_pool_invocation ap)
          (performASIDPoolInvocation ap')"
  apply (clarsimp simp: perform_asid_pool_invocation_def performASIDPoolInvocation_def)
  apply (cases ap, simp add: asid_pool_invocation_map_def)
  apply (rename_tac word1 word2 prod)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getSlotCap_corres])
       apply simp
      apply (rule_tac F="\<exists>p asid. rv = Structures_A.ArchObjectCap (ARM_A.PageDirectoryCap p asid)" in corres_gen_asm)
      apply clarsimp
      apply (rule_tac Q="valid_objs and pspace_aligned and pspace_distinct and asid_pool_at word2 and valid_etcbs and
                         cte_wp_at (\<lambda>c. cap_master_cap c =
                                        cap_master_cap (cap.ArchObjectCap (arch_cap.PageDirectoryCap p asid))) (a,b)"
                      in corres_split)
         apply simp
         apply (rule get_asid_pool_corres_inv')
        apply (rule corres_split)
           apply (rule updateCap_same_master)
           apply simp
          apply (rule corres_rel_imp)
           apply simp
           apply (rule setObject_ASIDPool_corres)
           apply (simp add: inv_def)
           apply (rule ext)
           apply (clarsimp simp: mask_asid_low_bits_ucast_ucast)
           apply (drule ucast_ucast_eq, simp, simp, simp)
          apply assumption
         apply (wp set_cap_typ_at)+
       apply clarsimp
       apply (erule cte_wp_at_weakenE)
       apply (clarsimp simp: is_cap_simps cap_master_cap_simps dest!: cap_master_cap_eqDs)
      apply (wp getASID_wp)
     apply (wp get_cap_wp getCTE_wp)+
   apply (clarsimp simp: valid_apinv_def cte_wp_at_def cap_master_cap_def is_pd_cap_def obj_at_def)
   apply (clarsimp simp: a_type_def)
  apply (clarsimp simp: cte_wp_at_ctes_of valid_apinv'_def)
  done

lemma armv_contextSwitch_obj_at' [wp]:
  "\<lbrace>\<lambda>s. P (obj_at' P' t s)\<rbrace> armv_contextSwitch pd a \<lbrace>\<lambda>rv s. P (obj_at' P' t s)\<rbrace>"
  apply (simp add: armv_contextSwitch_def armv_contextSwitch_HWASID_def getHWASID_def)
  apply (wp doMachineOp_obj_at|wpc|simp)+
  done

crunches vcpuSave, vcpuDisable, vcpuEnable, vcpuRestore
  for obj_at'_no_vcpu[wp]: "\<lambda>s. P (obj_at' (P' :: ('a :: no_vcpu) \<Rightarrow> bool) t s)"
  (simp: crunch_simps wp: crunch_wps)

lemma vcpuSwitch_obj_at'_no_vcpu[wp]:
  "vcpuSwitch param_a \<lbrace>\<lambda>s. P (obj_at' (P' :: ('a :: no_vcpu) \<Rightarrow> bool) t s)\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

crunch obj_at'_no_vcpu[wp]: setVMRoot "\<lambda>s. P (obj_at' (P' :: ('a :: no_vcpu) \<Rightarrow> bool) t s)"
  (simp: crunch_simps)

lemma storeHWASID_invs:
  "\<lbrace>invs' and
   (\<lambda>s. armKSASIDMap (ksArchState s) asid = None \<and>
        armKSHWASIDTable (ksArchState s) hw_asid = None)\<rbrace>
  storeHWASID asid hw_asid
  \<lbrace>\<lambda>x. invs'\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule storeHWASID_valid_arch')
   apply fastforce
  apply (simp add: storeHWASID_def)
  apply (wp findPDForASIDAssert_pd_at_wp)
  apply (clarsimp simp: invs'_def valid_state'_def valid_arch_state'_def
             valid_global_refs'_def global_refs'_def valid_machine_state'_def
             ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma storeHWASID_invs_no_cicd':
  "\<lbrace>invs_no_cicd' and
   (\<lambda>s. armKSASIDMap (ksArchState s) asid = None \<and>
        armKSHWASIDTable (ksArchState s) hw_asid = None)\<rbrace>
  storeHWASID asid hw_asid
  \<lbrace>\<lambda>x. invs_no_cicd'\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule storeHWASID_valid_arch')
   apply (fastforce simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
  apply (simp add: storeHWASID_def)
  apply (wp findPDForASIDAssert_pd_at_wp)
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_arch_state'_def
             valid_global_refs'_def global_refs'_def valid_machine_state'_def
             ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma findFreeHWASID_invs:
  "\<lbrace>invs'\<rbrace> findFreeHWASID \<lbrace>\<lambda>asid. invs'\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule findFreeHWASID_valid_arch)
   apply fastforce
  apply (simp add: findFreeHWASID_def invalidateHWASIDEntry_def invalidateASID_def
                   doMachineOp_def split_def
              cong: option.case_cong)
  apply (wp findPDForASIDAssert_pd_at_wp | wpc)+
  apply (clarsimp simp: invs'_def valid_state'_def valid_arch_state'_def
             valid_global_refs'_def global_refs'_def valid_machine_state'_def
             ct_not_inQ_def
           split del: if_split)
  apply (intro conjI)
   apply (fastforce dest: no_irq_use [OF no_irq_invalidateLocalTLB_ASID])
  apply clarsimp
  apply (drule_tac x=p in spec)
  apply (drule use_valid)
    apply (rule_tac p=p in invalidateLocalTLB_ASID_underlying_memory)
   apply blast
  apply clarsimp
  done

lemma findFreeHWASID_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> findFreeHWASID \<lbrace>\<lambda>asid. invs_no_cicd'\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule findFreeHWASID_valid_arch)
   apply (fastforce simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
  apply (simp add: findFreeHWASID_def invalidateHWASIDEntry_def invalidateASID_def
                   doMachineOp_def split_def
              cong: option.case_cong)
  apply (wp findPDForASIDAssert_pd_at_wp | wpc)+
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_arch_state'_def
             valid_global_refs'_def global_refs'_def valid_machine_state'_def
             ct_not_inQ_def
           split del: if_split)
  apply (intro conjI)
    apply (fastforce dest: no_irq_use [OF no_irq_invalidateLocalTLB_ASID])
   apply clarsimp
   apply (drule_tac x=p in spec)
   apply (drule use_valid)
    apply (rule_tac p=p in invalidateLocalTLB_ASID_underlying_memory)
    apply blast
   apply clarsimp
  done

lemma getHWASID_invs [wp]:
  "\<lbrace>invs'\<rbrace> getHWASID asid \<lbrace>\<lambda>hw_asid. invs'\<rbrace>"
  apply (simp add: getHWASID_def)
  apply (wp storeHWASID_invs findFreeHWASID_invs|wpc)+
  apply simp
  done

lemma getHWASID_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> getHWASID asid \<lbrace>\<lambda>hw_asid. invs_no_cicd'\<rbrace>"
  apply (simp add: getHWASID_def)
  apply (wp storeHWASID_invs_no_cicd' findFreeHWASID_invs_no_cicd'|wpc)+
  apply simp
  done

lemmas armv_ctxt_sw_defs = armv_contextSwitch_HWASID_def writeContextIDAndPD_def

lemma no_irq_armv_contextSwitch_HWASID:
  "no_irq (armv_contextSwitch_HWASID pd hwasid)"
  apply (simp add: armv_contextSwitch_HWASID_def)
  apply (wp no_irq_writeContextIDAndPD)
  done

lemma armv_contextSwitch_invs [wp]:
  "\<lbrace>invs'\<rbrace> armv_contextSwitch pd asid \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: armv_contextSwitch_def)
  apply (wp dmo_invs' no_irq_armv_contextSwitch_HWASID no_irq)
  apply (rule hoare_post_imp[rotated], rule getHWASID_invs)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply (simp add: machine_op_lift_def machine_rest_lift_def split_def armv_ctxt_sw_defs
              | wp)+
  done

lemma armv_contextSwitch_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> armv_contextSwitch pd asid \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: armv_contextSwitch_def armv_contextSwitch_HWASID_def)
  apply (wp dmo_invs_no_cicd' no_irq_writeContextIDAndPD no_irq)
  apply (rule hoare_post_imp[rotated], rule getHWASID_invs_no_cicd')
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply (clarsimp simp: machine_op_lift_def machine_rest_lift_def split_def armv_ctxt_sw_defs | wp)+
  done

lemma no_irq_setCurrentPD: "no_irq (setCurrentPD addr)"
  by (simp add: setCurrentPD_def setCurrentPDPL2_def)

lemma dmo_setCurrentPD_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (setCurrentPD addr) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_setCurrentPD no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (clarsimp simp: setCurrentPD_def machine_op_lift_def writeTTBR0_def dsb_def isb_def
                        setCurrentPDPL2_def machine_rest_lift_def split_def | wp)+
  done

lemma dmo_setCurrentPD_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (setCurrentPD addr) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wp dmo_invs_no_cicd' no_irq_setCurrentPD no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (clarsimp simp: setCurrentPD_def machine_op_lift_def writeTTBR0_def dsb_def isb_def
                        machine_rest_lift_def split_def setCurrentPDPL2_def| wp)+
  done

lemma valid_irq_node_lift_asm:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_node' s)\<rbrace>"
  assumes y: "\<And>p. \<lbrace>real_cte_at' p and Q\<rbrace> f \<lbrace>\<lambda>rv. real_cte_at' p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_irq_node' (irq_node' s) s \<and> Q s\<rbrace> f \<lbrace>\<lambda>rv s. valid_irq_node' (irq_node' s) s\<rbrace>"
  apply (simp add: valid_irq_node'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF x])
   apply (wp hoare_vcg_all_lift y)
  apply simp
  done

crunches storeWordUser, armv_contextSwitch, doMachineOp
  for ksQ[wp]: "\<lambda>s. P (ksReadyQueues s)"

crunches
  vcpuDisable, vcpuRestore, vcpuEnable, vgicUpdateLR, vcpuWriteReg, vcpuReadReg,
  vcpuRestoreRegRange, vcpuSaveRegRange
  for ksQ[wp]:  "\<lambda>s. P (ksReadyQueues s)"
  (wp: crunch_wps)

lemma vcpuSave_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> vcpuSave param_a \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  supply option.case_cong_weak[cong]
  apply (wpsimp simp: vcpuSave_def modifyArchState_def armvVCPUSave_def | simp)+
  apply (rule_tac S="set gicIndices" in mapM_x_wp)
  apply wpsimp+
  done

lemma vcpuSwitch_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | simp)+

lemma setVMRoot_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setVMRoot param_a \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpcw
          | simp add: if_apply_def2 checkPDNotInASIDMap_def split del: if_split)+
  done

crunch ksIdleThread[wp]: storeWordUser "\<lambda>s. P (ksIdleThread s)"
crunch ksIdleThread[wp]: asUser "\<lambda>s. P (ksIdleThread s)"
(wp: crunch_wps simp: crunch_simps)
crunch ksQ[wp]: asUser "\<lambda>s. P (ksReadyQueues s)"
(wp: crunch_wps simp: crunch_simps)

lemma dmo_machine_op_lift_invs'[wp]:
  "doMachineOp (machine_op_lift f) \<lbrace>invs'\<rbrace>"
    by (wpsimp wp: dmo_invs' simp: machine_op_lift_def in_monad machine_rest_lift_def select_f_def)

lemma dmo'_gets_wp:
  "\<lbrace>\<lambda>s. Q (f (ksMachineState s)) s\<rbrace> doMachineOp (gets f) \<lbrace>Q\<rbrace>"
    unfolding doMachineOp_def by (wpsimp simp: in_monad)

lemma hyp_live'_vcpu_regs[simp]:
  "hyp_live' (KOArch (KOVCPU (vcpuRegs_update f vcpu))) = hyp_live' (KOArch (KOVCPU vcpu))"
    by (simp add: hyp_live'_def arch_live'_def)

lemma hyp_live'_vcpu_vgic[simp]:
  "hyp_live' (KOArch (KOVCPU (vcpuVGIC_update f' vcpu))) = hyp_live' (KOArch (KOVCPU vcpu))"
    by (simp add: hyp_live'_def arch_live'_def)

lemma hyp_live'_vcpu_VPPIMasked[simp]:
  "hyp_live' (KOArch (KOVCPU (vcpuVPPIMasked_update f' vcpu))) = hyp_live' (KOArch (KOVCPU vcpu))"
    by (simp add: hyp_live'_def arch_live'_def)

lemma hyp_live'_vcpu_VTimer[simp]:
  "hyp_live' (KOArch (KOVCPU (vcpuVTimer_update f' vcpu))) = hyp_live' (KOArch (KOVCPU vcpu))"
    by (simp add: hyp_live'_def arch_live'_def)

lemma live'_vcpu_regs[simp]:
  "live' (KOArch (KOVCPU (vcpuRegs_update f vcpu))) = live' (KOArch (KOVCPU vcpu))"
    by (simp add: live'_def)

lemma live'_vcpu_vgic[simp]:
  "live' (KOArch (KOVCPU (vcpuVGIC_update f' vcpu))) = live' (KOArch (KOVCPU vcpu))"
    by (simp add: live'_def)

lemma live'_vcpu_VPPIMasked[simp]:
  "live' (KOArch (KOVCPU (vcpuVPPIMasked_update f' vcpu))) = live' (KOArch (KOVCPU vcpu))"
    by (simp add: live'_def)

lemma live'_vcpu_VTimer[simp]:
  "live' (KOArch (KOVCPU (vcpuVTimer_update f' vcpu))) = live' (KOArch (KOVCPU vcpu))"
    by (simp add: live'_def)

lemma setVCPU_regs_vcpu_live:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuRegs_update f vcpu) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps archObjSize_def)
   apply (clarsimp simp: vcpu_bits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def projectKOs)
  done

lemma setVCPU_vgic_vcpu_live[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVGIC_update f vcpu) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps archObjSize_def)
   apply (clarsimp simp: vcpu_bits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def projectKOs)
  done

lemma setVCPU_VPPIMasked_vcpu_live[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVPPIMasked_update f vcpu) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps archObjSize_def)
   apply (clarsimp simp: vcpu_bits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def projectKOs)
  done

lemma setVCPU_VTimer_vcpu_live[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVTimer_update f vcpu) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps archObjSize_def)
   apply (clarsimp simp: vcpu_bits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def projectKOs)
  done

lemma vgicUpdate_vcpu_live[wp]:
  "vgicUpdate v f \<lbrace> ko_wp_at' (is_vcpu' and hyp_live') p \<rbrace>"
  by (wpsimp simp: vgicUpdate_def vcpuUpdate_def wp: setVCPU_vgic_vcpu_live)

lemma setVCPU_regs_vgic_vcpu_live:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') p and ko_at' vcpu v\<rbrace>
   setObject v (vcpuRegs_update f (vcpuVGIC_update f' vcpu)) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') p\<rbrace>"
  apply (wp setObject_ko_wp_at, simp)
    apply (simp add: objBits_simps archObjSize_def)
   apply (clarsimp simp: vcpu_bits_def pageBits_def)
  apply (clarsimp simp: pred_conj_def is_vcpu'_def ko_wp_at'_def obj_at'_real_def projectKOs)
  done

(* FIXME: move *)
lemma setVCPU_regs_vgic_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuRegs_update f (vcpuVGIC_update f' vcpu)) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_regs_vgic_vcpu_live
          | rule hoare_lift_Pf[where f=ksArchState])+
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma setVCPU_regs_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuRegs_update f vcpu) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_regs_vcpu_live
           | rule hoare_lift_Pf[where f=ksArchState])
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma setVCPU_vgic_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuVGIC_update f vcpu) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_vgic_vcpu_live
           | rule hoare_lift_Pf[where f=ksArchState])
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma setVCPU_VPPIMasked_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuVPPIMasked_update f vcpu) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_vgic_vcpu_live
           | rule hoare_lift_Pf[where f=ksArchState])
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma setVCPU_VTimer_valid_arch':
  "\<lbrace>valid_arch_state' and ko_at' vcpu v\<rbrace> setObject v (vcpuVTimer_update f vcpu) \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv)
    apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setVCPU_vgic_vcpu_live
           | rule hoare_lift_Pf[where f=ksArchState])
  apply (clarsimp simp: pred_conj_def o_def)
  done

lemma state_refs_of'_vcpu_empty:
  "ko_at' (vcpu::vcpu) v s \<Longrightarrow> (state_refs_of' s)(v := {}) = state_refs_of' s"
    by (rule ext) (clarsimp simp: state_refs_of'_def obj_at'_def projectKOs)

lemma state_hyp_refs_of'_vcpu_absorb:
  "ko_at' vcpu v s \<Longrightarrow>
   (state_hyp_refs_of' s)(v := vcpu_tcb_refs' (vcpuTCBPtr vcpu)) = state_hyp_refs_of' s"
     by (rule ext) (clarsimp simp: state_hyp_refs_of'_def obj_at'_def projectKOs)

lemma setObject_vcpu_valid_objs':
  "\<lbrace>valid_objs' and valid_vcpu' vcpu\<rbrace> setObject v vcpu \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (wp setObject_valid_objs'[where P="valid_vcpu' vcpu"])
   apply (clarsimp simp: in_monad updateObject_default_def projectKOs valid_obj'_def)
  apply simp
  done

lemma setVCPU_valid_arch':
 "\<lbrace>valid_arch_state' and (\<lambda>s. \<forall>a. armHSCurVCPU (ksArchState s) = Some (v,a) \<longrightarrow> hyp_live' (KOArch (KOVCPU vcpu))) \<rbrace>
    setObject v (vcpu::vcpu)
  \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def option_case_all_conv pred_conj_def)
  apply (rule hoare_vcg_conj_lift[rotated])
   apply (rule hoare_vcg_conj_lift[rotated])
    apply (subst conj_commute[where P="\<forall>a. _ a \<longrightarrow> _ a"])
    apply (subst conj_commute[where P="\<forall>a. _ a \<longrightarrow> _ a"])
    apply (subst conj_assoc)+
    apply (rule hoare_vcg_conj_lift[rotated])
     apply (rule hoare_vcg_conj_lift[rotated])
      apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)
       apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift  setObject_ko_wp_at)
        apply (simp add: objBits_simps archObjSize_def vcpu_bits_def pageBits_def)+
      apply safe
         apply (clarsimp simp: is_vcpu'_def ko_wp_at'_def)+
     apply (wp hoare_vcg_all_lift hoare_drop_imp)+
done

lemma isb_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp isb \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq no_irq_isb)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def machine_rest_lift_def split_def)+
  done

lemma dsb_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp dsb \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq no_irq_dsb)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def machine_rest_lift_def split_def)+
  done

lemma setSCTLR_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (setSCTLR w) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq_setSCTLR no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def setSCTLR_def
                        machine_rest_lift_def split_def)+
  done

lemma set_gic_vcpu_ctrl_hcr_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (set_gic_vcpu_ctrl_hcr w) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq_set_gic_vcpu_ctrl_hcr no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def set_gic_vcpu_ctrl_hcr_def
                        machine_rest_lift_def split_def)+
  done

lemma set_gic_vcpu_ctrl_lr_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (set_gic_vcpu_ctrl_lr w x) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq_set_gic_vcpu_ctrl_lr no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def set_gic_vcpu_ctrl_lr_def
                        machine_rest_lift_def split_def)+
  done

lemma set_gic_vcpu_ctrl_apr_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (set_gic_vcpu_ctrl_apr w) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq_set_gic_vcpu_ctrl_apr no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def set_gic_vcpu_ctrl_apr_def
                        machine_rest_lift_def split_def)+
  done

lemma set_gic_vcpu_ctrl_vmcr_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (set_gic_vcpu_ctrl_vmcr w) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq_set_gic_vcpu_ctrl_vmcr no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def set_gic_vcpu_ctrl_vmcr_def
                        machine_rest_lift_def split_def)+
  done

lemma setHCR_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (setHCR w) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq_setHCR no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def setHCR_def
                        machine_rest_lift_def split_def)+
  done

lemma get_gic_vcpu_ctrl_hcr_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp get_gic_vcpu_ctrl_hcr \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  by (wpsimp wp: dmo_invs_no_cicd' no_irq_get_gic_vcpu_ctrl_hcr no_irq
           simp: get_gic_vcpu_ctrl_hcr_def gets_def in_monad)

lemma get_gic_vcpu_ctrl_lr_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (get_gic_vcpu_ctrl_lr w) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq_get_gic_vcpu_ctrl_lr no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def get_gic_vcpu_ctrl_lr_def
                        machine_rest_lift_def split_def)+
  done

lemma get_gic_vcpu_ctrl_apr_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp get_gic_vcpu_ctrl_apr \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  by (wpsimp wp: dmo_invs_no_cicd' no_irq_get_gic_vcpu_ctrl_apr no_irq
           simp: get_gic_vcpu_ctrl_apr_def gets_def in_monad)

lemma get_gic_vcpu_ctrl_vmcr_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp get_gic_vcpu_ctrl_vmcr \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  by (wpsimp wp: dmo_invs_no_cicd' no_irq_get_gic_vcpu_ctrl_vmcr no_irq
           simp: get_gic_vcpu_ctrl_vmcr_def gets_def in_monad)

lemma setVCPU_tcbs_of'[wp]:
  "setObject v (vcpu :: vcpu) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setVCPU_regs_r_invs_cicd':
  "\<lbrace>invs_no_cicd' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuRegs_update (\<lambda>_. (vcpuRegs vcpu)(r:=rval)) vcpu) \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding valid_state'_def valid_pspace'_def valid_mdb'_def invs_no_cicd'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuRegs_update (\<lambda>_. (vcpuRegs vcpu)(r:=rval)) vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    valid_pde_mappings_lift' setObject_typ_at' cur_tcb_lift
                    setVCPU_regs_valid_arch' setVCPU_regs_vcpu_live valid_bitmaps_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def projectKOs)
  done

lemma setVCPU_vgic_invs_cicd':
  "\<lbrace>invs_no_cicd' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVGIC_update f vcpu)
   \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding valid_state'_def valid_pspace'_def valid_mdb'_def invs_no_cicd'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. (vcpuVGIC_update f vcpu)"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    valid_pde_mappings_lift' setObject_typ_at' cur_tcb_lift
                    setVCPU_vgic_valid_arch' valid_bitmaps_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def projectKOs)
  done

lemma setVCPU_VPPIMasked_invs_cicd':
  "\<lbrace>invs_no_cicd' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVPPIMasked_update f vcpu)
   \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding valid_state'_def valid_pspace'_def valid_mdb'_def invs_no_cicd'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. (vcpuVPPIMasked_update f vcpu)"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    valid_pde_mappings_lift' setObject_typ_at' cur_tcb_lift
                    setVCPU_VPPIMasked_valid_arch' valid_bitmaps_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def projectKOs)
  done

lemma setVCPU_VTimer_invs_cicd':
  "\<lbrace>invs_no_cicd' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVTimer_update f vcpu)
   \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  unfolding valid_state'_def valid_pspace'_def valid_mdb'_def invs_no_cicd'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. (vcpuVTimer_update f vcpu)"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    valid_pde_mappings_lift' setObject_typ_at' cur_tcb_lift
                    setVCPU_VTimer_valid_arch' valid_bitmaps_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def projectKOs)
  done

lemma readVCPUHardwareReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (readVCPUHardwareReg r) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  by (wpsimp wp: dmo_invs_no_cicd' no_irq_readVCPUHardwareReg no_irq
             simp: readVCPUHardwareReg_def gets_def in_monad)

lemma writeVCPUHardwareReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (writeVCPUHardwareReg r v) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq_writeVCPUHardwareReg no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def writeVCPUHardwareReg_def
                        machine_rest_lift_def split_def)+
  done

lemma vgicUpdate_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vgicUpdate f v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vgicUpdate_def vcpuUpdate_def wp: setVCPU_vgic_invs_cicd')

lemma vcpuRestoreReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuRestoreReg v r \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuRestoreReg_def | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuReadReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuReadReg v r \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuReadReg_def | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuSaveReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuSaveReg v r \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuSaveReg_def vcpuUpdate_def wp: setVCPU_regs_r_invs_cicd'
     | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuWriteReg_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuWriteReg vcpu_ptr r v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuWriteReg_def vcpuUpdate_def wp: setVCPU_regs_r_invs_cicd'
     | subst doMachineOp_bind | rule empty_fail_bind)+

crunches vcpuRestoreRegRange, vcpuSaveRegRange, vgicUpdateLR
  for invs_no_cicd'[wp]: invs_no_cicd'
  (wp: mapM_x_wp ignore: loadObject)

lemma maskInterrupt_irq_states':
  "\<lbrace>valid_irq_states'
    and (\<lambda>s. \<not>b \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)\<rbrace>
   doMachineOp (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. valid_irq_states'\<rbrace>"
  by (wpsimp wp: dmo_maskInterrupt)
     (auto simp add: valid_irq_states_def valid_irq_masks'_def)

lemma maskInterrupt_invs_no_cicd':
  "\<lbrace>invs_no_cicd'
    and (\<lambda>s. \<not>b \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)\<rbrace>
   doMachineOp (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  by (wpsimp wp: maskInterrupt_irq_states' dmo_maskInterrupt simp: invs_no_cicd'_def)
     (auto simp: valid_irq_states_def valid_irq_masks'_def valid_machine_state'_def
                 ct_not_inQ_def)

lemma getIRQState_wp:
  "\<lbrace>\<lambda>s. P (intStateIRQTable (ksInterruptState s) irq) s \<rbrace> getIRQState irq \<lbrace>\<lambda>rv s. P rv s\<rbrace>"
  unfolding getIRQState_def getInterruptState_def
  by (wpsimp simp: comp_def)

lemma saveVirtTimer_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> saveVirtTimer vcpu_ptr \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: saveVirtTimer_def vcpuUpdate_def read_cntpct_def get_cntv_off_64_def
                   get_cntv_cval_64_def
             wp: setVCPU_VTimer_invs_cicd' dmo'_gets_wp)+

lemma set_cntv_off_64_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (set_cntv_off_64 v) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def set_cntv_off_64_def
                        machine_rest_lift_def split_def)+
  done

lemma set_cntv_cval_64_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (set_cntv_cval_64 v) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wpsimp wp: dmo_invs_no_cicd' no_irq)
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: machine_op_lift_def set_cntv_cval_64_def
                        machine_rest_lift_def split_def)+
  done

lemma restoreVirtTimer_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> restoreVirtTimer vcpu_ptr \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: restoreVirtTimer_def vcpuUpdate_def read_cntpct_def if_apply_def2
                   isIRQActive_def
             wp: setVCPU_VTimer_invs_cicd' maskInterrupt_invs_no_cicd' getIRQState_wp dmo'_gets_wp)

lemma vcpuEnable_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuEnable v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuEnable_def | subst doMachineOp_bind | rule empty_fail_bind)+

lemma dmo_maskInterrupt_True_invs_no_cicd'[wp]:
  "doMachineOp (maskInterrupt True irq) \<lbrace>invs_no_cicd'\<rbrace>"
  apply (wp dmo_maskInterrupt)
  apply (clarsimp simp: invs_no_cicd'_def valid_state'_def)
  apply (simp add: valid_irq_masks'_def valid_machine_state'_def
                   ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma vcpuDisable_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuDisable v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp wp: doMachineOp_typ_ats
             simp: vcpuDisable_def valid_vcpu'_def doMachineOp_typ_at' split: option.splits
      | subst doMachineOp_bind | rule empty_fail_bind conjI)+

lemma vcpuRestore_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuRestore v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  including no_pre
  apply (wpsimp simp: vcpuRestore_def uncurry_def split_def doMachineOp_mapM_x gets_wp
       | subst doMachineOp_bind | rule empty_fail_bind)+
       apply (rule_tac S="(\<lambda>i. (of_nat i, vgicLR (vcpuVGIC vcpu) i)) ` {0..<numListRegs+1}" in mapM_x_wp)
       apply wpsimp
       apply (auto simp: image_def gicVCPUMaxNumLR_def)[1]
      apply wpsimp+
  done

lemma vcpuSave_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> vcpuSave v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  by (wpsimp simp: vcpuSave_def armvVCPUSave_def wp: mapM_x_wp cong: option.case_cong_weak
      | assumption)+

lemma valid_arch_state'_armHSCurVCPU_update[simp]:
  "\<lbrakk> ko_wp_at' (is_vcpu' and hyp_live') v s; valid_arch_state' s \<rbrakk> \<Longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState := armHSCurVCPU_update (\<lambda>_. Some (v, b)) (ksArchState s)\<rparr>)"
  by (clarsimp simp: invs'_def valid_state'_def
                     bitmapQ_defs valid_global_refs'_def valid_arch_state'_def global_refs'_def
                     valid_irq_node'_def valid_irq_handlers'_def
                     irq_issued'_def irqs_masked'_def valid_machine_state'_def cur_tcb'_def)

lemma dmo_vcpu_hyp:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace> doMachineOp f \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: doMachineOp_def)

lemma vcpuSaveReg_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v \<rbrace> vcpuSaveReg v' r \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuSaveReg_def vcpuUpdate_def wp: setVCPU_regs_vcpu_live dmo_vcpu_hyp)

lemma vcpuWriteReg_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v \<rbrace> vcpuWriteReg v' r val \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuWriteReg_def vcpuUpdate_def wp: setVCPU_regs_vcpu_live dmo_vcpu_hyp)

crunches
  vcpuRestoreRegRange, vcpuSaveRegRange, vgicUpdateLR, vcpuReadReg
  for hyp[wp]: "ko_wp_at' (is_vcpu' and hyp_live') v"
  (wp: crunch_wps setVCPU_regs_vcpu_live dmo_vcpu_hyp)

lemma saveVirtTimer_hyp[wp]:
  "saveVirtTimer vcpu_ptr \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: saveVirtTimer_def vcpuUpdate_def wp: dmo_vcpu_hyp vgicUpdate_vcpu_live)

lemma restoreVirtTimer_hyp[wp]:
  "restoreVirtTimer vcpu_ptr \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: restoreVirtTimer_def vcpuUpdate_def isIRQActive_def
             wp: dmo_vcpu_hyp vgicUpdate_vcpu_live)

lemma vcpuDisable_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace> vcpuDisable (Some x) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuDisable_def wp: dmo_vcpu_hyp vgicUpdate_vcpu_live | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuEnable_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace> vcpuEnable x \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuEnable_def wp: dmo_vcpu_hyp | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuRestore_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace> vcpuRestore x \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: vcpuRestore_def wp: dmo_vcpu_hyp | subst doMachineOp_bind | rule empty_fail_bind)+

lemma getObject_vcpu_ko_at':
  "(vcpu::vcpu, s') \<in> fst (getObject p s) \<Longrightarrow> s' = s \<and> ko_at' vcpu p s"
  apply (rule context_conjI)
   apply (drule use_valid, rule getObject_inv[where P="(=) s"]; simp add: loadObject_default_inv)
  apply (drule use_valid, rule getObject_ko_at; clarsimp simp: obj_at_simps vcpu_bits_def)
  done

lemma vcpuSave_hyp[wp]:
  "\<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace> vcpuSave (Some (x, b)) \<lbrace>\<lambda>_. ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  apply (wpsimp simp: vcpuSave_def armvVCPUSave_def
                wp: dmo_vcpu_hyp | subst doMachineOp_bind | rule empty_fail_bind)+
  apply (rule_tac S="set [0..<numListRegs]" in mapM_x_wp)
  by (wpsimp wp: dmo_vcpu_hyp | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuUpdate_valid_arch_state'[wp]:
  "\<forall>vcpu. vcpuTCBPtr (f vcpu) = vcpuTCBPtr vcpu \<Longrightarrow>
   \<lbrace>valid_arch_state'\<rbrace> vcpuUpdate vr f \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  including no_pre
  apply (wpsimp simp: vcpuUpdate_def
            wp: setVCPU_valid_arch')
  by (clarsimp simp: valid_def in_monad hyp_live'_def arch_live'_def valid_arch_state'_def
                     obj_at'_real_def ko_wp_at'_def projectKOs is_vcpu'_def
               dest!: getObject_vcpu_ko_at')+

crunches vgicUpdateLR, vcpuSave, vcpuDisable, vcpuEnable, vcpuRestore
  for valid_arch_state'[wp]: valid_arch_state'
  (wp: crunch_wps ignore: doMachineOp)

lemma vcpuSwitch_valid_arch_state'[wp]:
   "\<lbrace>valid_arch_state' and (case v of None \<Rightarrow> \<top> | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x)\<rbrace>
       vcpuSwitch v \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (wpsimp simp: vcpuSwitch_def modifyArchState_def
         wp: vcpuDisable_hyp[simplified pred_conj_def] vcpuSave_hyp[unfolded pred_conj_def]
             dmo_vcpu_hyp vcpuSave_valid_arch_state'
        | strengthen valid_arch_state'_armHSCurVCPU_update | simp)+
  apply (auto simp: valid_arch_state'_def pred_conj_def)
  done

lemma invs_no_cicd'_armHSCurVCPU_update[simp]:
  "ko_wp_at' (is_vcpu' and hyp_live') v s \<Longrightarrow> invs_no_cicd' s \<Longrightarrow>
     invs_no_cicd' (s\<lparr>ksArchState := armHSCurVCPU_update (\<lambda>_. Some (v, b)) (ksArchState s)\<rparr>)"
  by (clarsimp simp: invs_no_cicd'_def valid_state'_def
                     bitmapQ_defs valid_global_refs'_def valid_arch_state'_def global_refs'_def
                     valid_irq_node'_def valid_irq_handlers'_def
                     irq_issued'_def irqs_masked'_def valid_machine_state'_def cur_tcb'_def)

lemma invs'_armHSCurVCPU_update[simp]:
  "ko_wp_at' (is_vcpu' and hyp_live') v s \<Longrightarrow>
   invs' s \<Longrightarrow> invs' (s\<lparr>ksArchState := armHSCurVCPU_update (\<lambda>_. Some (v, b)) (ksArchState s)\<rparr>)"
  apply (clarsimp simp: invs'_def valid_state'_def
                        bitmapQ_defs valid_global_refs'_def valid_arch_state'_def global_refs'_def
                        valid_irq_node'_def valid_irq_handlers'_def
                        irq_issued'_def irqs_masked'_def valid_machine_state'_def cur_tcb'_def)
  done

lemma armHSCurVCPU_None_invs'[wp]:
  "modifyArchState (armHSCurVCPU_update Map.empty) \<lbrace>invs'\<rbrace>"
  apply (wpsimp simp: modifyArchState_def)
  by (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                        valid_arch_state'_def valid_global_refs'_def global_refs'_def)

lemma setVCPU_vgic_invs':
  "\<lbrace>invs' and ko_at' vcpu v\<rbrace>
   setObject v (vcpuVGIC_update f vcpu) \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuVGIC_update f vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    valid_pde_mappings_lift' setObject_typ_at' cur_tcb_lift
                    setVCPU_vgic_valid_arch' valid_bitmaps_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def projectKOs)
  done

lemma setVCPU_regs_invs':
  "\<lbrace>invs' and ko_at' vcpu v\<rbrace> setObject v (vcpuRegs_update f vcpu) \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuRegs_update f vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    valid_pde_mappings_lift' setObject_typ_at' cur_tcb_lift
                    setVCPU_regs_valid_arch' valid_bitmaps_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def projectKOs)
  done

lemma setVCPU_VPPIMasked_invs':
  "\<lbrace>invs' and ko_at' vcpu v\<rbrace> setObject v (vcpuVPPIMasked_update f vcpu) \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuVPPIMasked_update f vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    valid_pde_mappings_lift' setObject_typ_at' cur_tcb_lift
                    setVCPU_VPPIMasked_valid_arch' valid_bitmaps_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def projectKOs)
  done

lemma setVCPU_VTimer_invs':
  "\<lbrace>invs' and ko_at' vcpu v\<rbrace> setObject v (vcpuVTimer_update f vcpu) \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def
            valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: setObject_vcpu_no_tcb_update
                      [where f="\<lambda>vcpu. vcpuVTimer_update f vcpu"]
                    sch_act_wf_lift tcb_in_cur_domain'_lift valid_queues_lift
                    setObject_state_refs_of' setObject_state_hyp_refs_of' valid_global_refs_lift'
                    valid_irq_node_lift_asm [where Q=\<top>] valid_irq_handlers_lift'
                    cteCaps_of_ctes_of_lift irqs_masked_lift ct_idle_or_in_cur_domain'_lift
                    valid_irq_states_lift' hoare_vcg_all_lift hoare_vcg_disj_lift
                    valid_pde_mappings_lift' setObject_typ_at' cur_tcb_lift
                    setVCPU_VTimer_valid_arch' valid_bitmaps_lift
              simp: objBits_simps archObjSize_def vcpu_bits_def pageBits_def
                    state_refs_of'_vcpu_empty state_hyp_refs_of'_vcpu_absorb)
  apply (clarsimp simp: if_live_then_nonz_cap'_def obj_at'_real_def)
  apply (fastforce simp: ko_wp_at'_def projectKOs)
  done

lemma read_writeVCPUHardwareReg_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (writeVCPUHardwareReg r v) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  "\<lbrace>invs'\<rbrace> doMachineOp (readVCPUHardwareReg r) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by ((wpsimp wp: dmo_invs' no_irq no_irq_writeVCPUHardwareReg)
       , drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid
       , (wpsimp simp: writeVCPUHardwareReg_def readVCPUHardwareReg_def)+)+

lemma vcpuWriteReg_invs'[wp]:
  "vcpuWriteReg vcpu_ptr r v \<lbrace>invs'\<rbrace>"
  by (wpsimp simp: vcpuWriteReg_def vcpuUpdate_def wp: setVCPU_regs_invs')

lemma vcpuSaveReg_invs'[wp]:
  "vcpuSaveReg v r \<lbrace>invs'\<rbrace>"
  by (wpsimp simp: vcpuSaveReg_def vcpuUpdate_def wp: setVCPU_regs_invs')

lemma saveVirtTimer_invs'[wp]:
  "saveVirtTimer vcpu_ptr \<lbrace>invs'\<rbrace>"
  unfolding saveVirtTimer_def
  by (wpsimp wp: dmo'_gets_wp setVCPU_vgic_invs' setVCPU_regs_invs' dmo_maskInterrupt_True
                 setVCPU_VTimer_invs'
             simp: doMachineOp_bind vcpuUpdate_def read_cntpct_def  get_cntv_off_64_def
                   get_cntv_cval_64_def)

lemma vcpuDisable_invs'[wp]:
  "vcpuDisable v \<lbrace>invs'\<rbrace>"
  unfolding vcpuDisable_def isb_def setHCR_def setSCTLR_def set_gic_vcpu_ctrl_hcr_def
             getSCTLR_def get_gic_vcpu_ctrl_hcr_def dsb_def vgicUpdate_def vcpuUpdate_def
             vcpuSaveReg_def
  by (wpsimp wp: dmo'_gets_wp setVCPU_vgic_invs' setVCPU_regs_invs' dmo_maskInterrupt_True
                 hoare_drop_imps
             simp: doMachineOp_bind empty_fail_cond)

lemma vcpuInvalidateActive_invs'[wp]:
  "vcpuInvalidateActive \<lbrace>invs'\<rbrace>"
    unfolding vcpuInvalidateActive_def by wpsimp

lemma dmo_set_gic_vcpu_ctrl_hcr_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (set_gic_vcpu_ctrl_hcr addr) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_set_gic_vcpu_ctrl_hcr no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: set_gic_vcpu_ctrl_hcr_def)+
  done

lemma dmo_set_gic_vcpu_ctrl_apr_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (set_gic_vcpu_ctrl_apr addr) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_set_gic_vcpu_ctrl_apr no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: set_gic_vcpu_ctrl_apr_def)+
  done

lemma dmo_set_gic_vcpu_ctrl_vmcr_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (set_gic_vcpu_ctrl_vmcr addr) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_set_gic_vcpu_ctrl_vmcr no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: set_gic_vcpu_ctrl_vmcr_def)+
  done

lemma dmo_set_gic_vcpu_ctrl_lr_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (set_gic_vcpu_ctrl_lr addr w) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_set_gic_vcpu_ctrl_lr no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: set_gic_vcpu_ctrl_lr_def)+
  done

lemma dmo_get_gic_vcpu_ctrl_lr_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (get_gic_vcpu_ctrl_lr addr) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_get_gic_vcpu_ctrl_lr no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: get_gic_vcpu_ctrl_lr_def)+
  done

lemma dmo_setSCTLR_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (setSCTLR addr) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_setSCTLR no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: setSCTLR_def)+
  done

lemma dmo_setHCR_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (setHCR addr) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_setHCR no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (wpsimp simp: setHCR_def)+
  done

lemma dmo_isb_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp isb \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_isb no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply wpsimp+
  done

lemma dmo_dsb_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp dsb \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_dsb no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply wpsimp+
  done

crunches
  vcpuRestoreReg, vcpuRestoreRegRange, vcpuSaveReg, vcpuSaveRegRange, vgicUpdateLR, vcpuReadReg
  for invs'[wp]: invs'
  (wp: crunch_wps setVCPU_regs_invs' setVCPU_vgic_invs' simp: vcpuUpdate_def
   ignore: doMachineOp vcpuUpdate)

lemma maskInterrupt_invs':
  "\<lbrace>invs'
    and (\<lambda>s. \<not>b \<longrightarrow> intStateIRQTable (ksInterruptState s) irq \<noteq> irqstate.IRQInactive)\<rbrace>
   doMachineOp (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
   by (wpsimp wp: maskInterrupt_irq_states' dmo_maskInterrupt simp: invs'_def valid_state'_def)
      (auto simp: valid_irq_states_def valid_irq_masks'_def valid_machine_state'_def
                  ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)

lemma restoreVirtTimer_invs'[wp]:
  "restoreVirtTimer vcpu_ptr \<lbrace> invs'\<rbrace>"
  unfolding restoreVirtTimer_def
  by (wpsimp wp: maskInterrupt_invs' getIRQState_wp dmo'_gets_wp dmo_machine_op_lift_invs'
             simp: IRQ_def if_apply_def2 set_cntv_off_64_def read_cntpct_def set_cntv_cval_64_def
                   isIRQActive_def)

lemma vcpuEnable_invs'[wp]:
  "vcpuEnable v \<lbrace> invs'\<rbrace>"
  unfolding vcpuEnable_def
  by (wpsimp | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuRestore_invs'[wp]:
  "\<lbrace>invs'\<rbrace> vcpuRestore v \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding vcpuRestore_def
  by (wpsimp simp: vcpuRestore_def uncurry_def split_def doMachineOp_mapM_x
                wp: mapM_x_wp[OF _ subset_refl]
     | subst doMachineOp_bind | rule empty_fail_bind)+

lemma vcpuSave_invs':
  "\<lbrace>invs'\<rbrace> vcpuSave v \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wpsimp simp: vcpuSave_def doMachineOp_mapM armvVCPUSave_def
                   get_gic_vcpu_ctrl_apr_def get_gic_vcpu_ctrl_vmcr_def
                   get_gic_vcpu_ctrl_hcr_def getSCTLR_def
             wp: dmo'_gets_wp vgicUpdate_invs' mapM_x_wp[OF _ subset_refl])

lemma vcpuSwitch_invs'[wp]:
  "\<lbrace>invs' and (case v of None \<Rightarrow> \<top> | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x)\<rbrace>
       vcpuSwitch v \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wpsimp simp: vcpuSwitch_def modifyArchState_def
         wp: vcpuDisable_hyp[simplified pred_conj_def] vcpuSave_hyp[unfolded pred_conj_def]
             dmo_isb_invs' dmo_vcpu_hyp vcpuSave_invs'
        | strengthen invs'_armHSCurVCPU_update | simp)+
  apply (auto simp: invs'_def valid_state'_def valid_arch_state'_def pred_conj_def)
  done

lemma vcpuSwitch_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd' and (case v of None \<Rightarrow> \<top> | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x)\<rbrace>
       vcpuSwitch v \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  apply (wpsimp simp: vcpuSwitch_def modifyArchState_def
                  wp: vcpuDisable_hyp[simplified pred_conj_def] vcpuSave_hyp[unfolded pred_conj_def]
                       gets_wp vcpuSave_invs_no_cicd'
                       dmo_isb_invs' dmo_vcpu_hyp
        | strengthen invs_no_cicd'_armHSCurVCPU_update | simp)+
  apply (auto simp: invs_no_cicd'_def valid_state'_def valid_arch_state'_def pred_conj_def)
  done

crunch valid_arch_state'[wp]: checkPDNotInASIDMap valid_arch_state'
crunch valid_arch_state'[wp]: findPDForASID  valid_arch_state'
crunch valid_arch_state'[wp]: armv_contextSwitch valid_arch_state'
crunch ko_wp_at'[wp]: armv_contextSwitch "ko_wp_at' P' t"

lemma valid_case_option_post_wp':
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>\<lambda>rv. Q x\<rbrace>) \<Longrightarrow>
    \<lbrace>case ep of Some x \<Rightarrow> P x | _ \<Rightarrow> \<lambda>_. True\<rbrace>
       f \<lbrace>\<lambda>rv. case ep of Some x \<Rightarrow> Q x | _ \<Rightarrow> \<lambda>_. True\<rbrace>"
  by (cases ep, simp_all add: hoare_vcg_prop)

abbreviation
  "live_vcpu_at_tcb p s \<equiv> \<exists>x. ko_at' x p s \<and>
    (case atcbVCPUPtr (tcbArch x) of None \<Rightarrow> \<lambda>_. True
                                   | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x) s"

lemma setVMRoot_valid_arch_state'[wp]:
  "\<lbrace>valid_arch_state' and live_vcpu_at_tcb p\<rbrace>
     setVMRoot p
   \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def)
  apply ((wpsimp wp: hoare_vcg_ex_lift hoare_drop_imps
                    getObject_tcb_wp valid_case_option_post_wp'
               simp: if_apply_def2
          | wp hoare_vcg_all_lift)+)
  done

lemma modifyArchState_hyp[wp]:
  "modifyArchState x \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  by (wpsimp simp: modifyArchState_def wp: | subst doMachineOp_bind)+

lemma vcpuSwitch_hyp[wp]:
  "vcpuSwitch x \<lbrace>ko_wp_at' (is_vcpu' and hyp_live') v\<rbrace>"
  apply (simp add: vcpuSwitch_def)
  apply wpc
    apply wpsimp
   apply wpsimp
  apply (clarsimp simp: ko_wp_at'_def)
  done

lemma switchToThread_valid_arch_state[wp]:
  "\<lbrace>valid_arch_state' and live_vcpu_at_tcb p\<rbrace> ARM_HYP_H.switchToThread p \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: ARM_HYP_H.switchToThread_def)
  by (wpsimp wp: hoare_vcg_ex_lift getObject_tcb_wp valid_case_option_post_wp')+

crunches switchToThread
  for valid_arch_state'[wp]: valid_arch_state'
  (wp: hoare_vcg_ex_lift)

lemma getObject_tcb_hyp_sym_refs:
      "\<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of' s)\<rbrace> getObject p
       \<lbrace>\<lambda>rv. case atcbVCPUPtr (tcbArch rv) of None \<Rightarrow> \<lambda>_. True
             | Some x \<Rightarrow> ko_wp_at' (is_vcpu' and hyp_live') x\<rbrace>"
  apply (wpsimp wp: getObject_tcb_wp)
  apply (clarsimp simp: typ_at_tcb'[symmetric] typ_at'_def ko_wp_at'_def[of _ p]
                split: option.splits)
  apply (case_tac ko; simp)
  apply (rename_tac tcb)
  apply (rule_tac x=tcb in exI; rule conjI, clarsimp simp: obj_at'_def projectKOs)
  apply (clarsimp, rule context_conjI, clarsimp simp: obj_at'_def projectKOs)
  apply (drule ko_at_state_hyp_refs_ofD')
  apply (simp add: hyp_refs_of'_def sym_refs_def)
  apply (erule_tac x=p in allE, simp)
  apply (drule state_hyp_refs_of'_elemD)
  apply (clarsimp simp: hyp_refs_of_rev')
  apply (simp add: ko_wp_at'_def, erule exE,
         clarsimp simp: is_vcpu'_def hyp_live'_def arch_live'_def)
  done

lemma setVMRoot_invs'[wp]:
  "\<lbrace>invs'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def)
   apply (wp hoare_drop_imps getObject_tcb_hyp_sym_refs
          | wpcw
          | simp add: if_apply_def2 checkPDNotInASIDMap_def split del: if_split)+
  done

lemma setVMRoot_invs_no_cicd'[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def)
   apply (wp hoare_drop_imps getObject_tcb_hyp_sym_refs
             armv_contextSwitch_invs_no_cicd' getHWASID_invs_no_cicd'
             dmo_setCurrentPD_invs_no_cicd'
          | wpcw
          | simp add: if_apply_def2 checkPDNotInASIDMap_def split del: if_split)+
  done

crunches
  vgicUpdateLR, vcpuWriteReg, vcpuReadReg, vcpuRestoreRegRange, vcpuSaveRegRange, vcpuSave,
  vcpuSwitch
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  (ignore: doMachineOp wp: crunch_wps)

crunch nosch [wp]: setVMRoot "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps
       loadObject_default_def)

crunch it' [wp]: findPDForASID "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv)

crunch it' [wp]: deleteASIDPool "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv mapM_wp')

crunch it' [wp]: lookupPTSlot "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv)

lemma storePTE_it'[wp]: "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePDE_it'[wp]: "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

crunch it' [wp]: flushTable "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def
   wp: setObject_idle' hoare_drop_imps mapM_wp')

crunch it' [wp]: deleteASID "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def updateObject_default_def
   wp: getObject_inv)

lemma valid_slots_lift':
  assumes t: "\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at' T p\<rbrace>"
  shows "\<lbrace>valid_slots' x\<rbrace> f \<lbrace>\<lambda>rv. valid_slots' x\<rbrace>"
  apply (clarsimp simp: valid_slots'_def split: sum.splits prod.splits)
  apply safe
   apply (rule hoare_pre, wp hoare_vcg_const_Ball_lift t valid_pde_lift' valid_pte_lift', simp)+
  done

crunch typ_at' [wp]: performPageTableInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch typ_at' [wp]: performPageDirectoryInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch typ_at' [wp]: performPageInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch typ_at' [wp]: performASIDPoolInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: getObject_cte_inv getASID_wp)

lemmas performPageTableInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageTableInvocation_typ_at']

lemmas performPageDirectoryInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageDirectoryInvocation_typ_at']

lemmas performPageInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performPageInvocation_typ_at']

lemmas performASIDPoolInvocation_typ_ats' [wp] =
  typ_at_lifts [OF performASIDPoolInvocation_typ_at']

lemma storePDE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: pred_tcb_at'_def storePDE_def)
  apply (wp hoare_drop_imp obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  apply (clarsimp simp:  obj_at'_def tcb_to_itcb'_def)
  done

lemma storePTE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePTE_def pred_tcb_at'_def)
  apply (wp hoare_drop_imp obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  apply (clarsimp simp:  obj_at'_def tcb_to_itcb'_def)
  done

lemma setASID_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma dmo_ct[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> doMachineOp m \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply clarsimp
  done

lemma storePDE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma storePDE_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  by (wpsimp wp: setObject_nosch headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePDE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePDE_def)
  apply (wp setObject_ko_wp_at hoare_drop_imp | simp add: objBits_simps archObjSize_def vspace_bits_defs)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

lemma storePDE_nordL1[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_ s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_nordL2[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_ s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: storePDE_def objBits_simps archObjSize_def vspace_bits_defs
                wp: hoare_drop_imp setObject_iflive' [where P=\<top>])
     apply (auto simp: updateObject_default_def in_monad live'_def hyp_live'_def arch_live'_def projectKOs)
  done

lemma setObject_pde_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pde::pde) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma storePDE_ksInterruptState[wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_ s. P (ksInterruptState s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (wp setObject_ifunsafe'[where P=\<top>] hoare_drop_imp, simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

method valid_idle'_setObject uses simp =
  simp add: valid_idle'_def, rule hoare_lift_Pf [where f="ksIdleThread"]; wpsimp?;
  (wpsimp wp: obj_at_setObject2[where P="idle_tcb'", simplified] hoare_drop_imp
        simp: simp
   | clarsimp dest!: updateObject_default_result)+

lemma storePDE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. valid_idle'\<rbrace>" by (valid_idle'_setObject simp: storePDE_def)

lemma storePDE_arch'[wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_cur'[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> storePDE param_a param_b \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePDE pde p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv hoare_drop_imp)
  done

lemma storePDE_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings' and K (valid_pde_mapping' (p && mask pdBits) pde)\<rbrace>
      storePDE p pde
   \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp valid_pde_mappings_lift')
   apply (rule hoare_post_imp)
    apply (simp only: obj_at'_real_def)
   apply (simp add: storePDE_def)
   apply (wp setObject_ko_wp_at hoare_drop_imp)
      apply simp
     apply (simp add: objBits_simps archObjSize_def vspace_bits_defs)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  apply assumption
  done

lemma setObject_pde_machine_state[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setObject t (v::pde) \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePDE_machine_state[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePDE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  by (wpsimp simp: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
             wp: setObject_typ_at_inv setObject_ksMachine updateObject_default_inv hoare_vcg_all_lift hoare_vcg_disj_lift)

crunch pspace_domain_valid[wp]: storePDE "pspace_domain_valid"
  (wp: hoare_drop_imp)

lemma storePDE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePDE p pde \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePDE_nosch])
  apply (wpsimp simp: storePDE_def updateObject_default_def wp: hoare_drop_imp)
   apply (wps setObject_PDE_ct)
   apply (wpsimp wp: obj_at_setObject2 simp: updateObject_default_def in_monad)+
  done

lemma setObject_pde_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pde) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pde_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pde) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePDE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePDE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  by (wpsimp wp: hoare_drop_imp obj_at_setObject2 simp: storePDE_def updateObject_default_def in_monad)

lemma storePDE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePDE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePDE p pde \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pte_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma setObject_pde_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pde::pde) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma storePDE_ksDomScheduleIdx[wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def)

lemma storePTE_ksDomScheduleIdx[wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePDE_gsMaxObjectSize[wp]:
  "\<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (gsMaxObjectSize s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def setObject_def)

lemma storePTE_gsMaxObjectSize[wp]:
  "\<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (gsMaxObjectSize s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def setObject_def)

lemma storePDE_gsUntypedZeroRanges[wp]:
  "\<lbrace>\<lambda>s. P (gsUntypedZeroRanges s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (gsUntypedZeroRanges s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePDE_def updateObject_default_def setObject_def)

lemma storePTE_gsUntypedZeroRanges[wp]:
  "\<lbrace>\<lambda>s. P (gsUntypedZeroRanges s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (gsUntypedZeroRanges s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def setObject_def)

lemma setObject_pte_tcb_of'[wp]:
  "setObject slote (pte::pte) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

crunches storePTE
  for tcbs_of'[wp]: "\<lambda>s. P (tcbs_of' s)"
  (wp: crunch_wps)

lemma setObject_pde_tcb_of'[wp]:
  "setObject slote (pde::pde) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

crunches storePDE
  for tcbs_of'[wp]: "\<lambda>s. P (tcbs_of' s)"
  (wp: crunch_wps)

lemma storePDE_invs[wp]:
  "\<lbrace>invs' and valid_pde' pde
          and (\<lambda>s. valid_pde_mapping' (p && mask pdBits) pde)\<rbrace>
      storePDE p pde
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift'
             irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift sym_heap_sched_pointers_lift valid_bitmaps_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma storePTE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma storePTE_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  by (wpsimp wp: setObject_nosch headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePTE_ksQ[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePTE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePTE_def)
  apply (wp setObject_ko_wp_at hoare_drop_imp | simp add: objBits_simps archObjSize_def vspace_bits_defs)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

lemma storePTE_nordL1[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_ s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePTE_nordL2[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_ s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePTE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (wpsimp simp: storePTE_def objBits_simps archObjSize_def vspace_bits_defs
                wp: hoare_drop_imp setObject_iflive' [where P=\<top>])
     apply (auto simp: updateObject_default_def in_monad live'_def hyp_live'_def arch_live'_def projectKOs)
  done

lemma setObject_pte_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma storePTE_ksInt'[wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_ s. P (ksInterruptState s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imp setObject_ksInterrupt updateObject_default_inv simp: storePTE_def)

lemma storePTE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wp setObject_ifunsafe'[where P=\<top>] hoare_drop_imp, simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_idle'\<rbrace>" by (valid_idle'_setObject simp: storePTE_def)

lemma storePTE_arch'[wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePTE_cur'[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> storePTE param_a param_b \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePTE pte p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wpsimp wp: hoare_drop_imp valid_irq_states_lift' dmo_lift' no_irq_storeWord
                    setObject_ksMachine updateObject_default_inv)
  done

lemma storePTE_valid_objs [wp]:
  "\<lbrace>valid_objs' and valid_pte' pte\<rbrace> storePTE p pte \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: storePTE_def doMachineOp_def split_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps|wpc|simp)+
   apply (rule setObject_valid_objs')
   prefer 2
   apply assumption
  apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: valid_obj'_def)
  done

lemma storePTE_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (wp valid_pde_mappings_lift')
   apply (simp add: storePTE_def)
   apply (wp hoare_drop_imp obj_at_setObject2)
   apply (auto dest!: updateObject_default_result)
  done

lemma setObject_pte_machine_state[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePTE_machine_state[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)


lemma storePTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePTE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  by (wpsimp simp: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def
             wp: setObject_typ_at_inv setObject_ksMachine updateObject_default_inv hoare_vcg_all_lift hoare_vcg_disj_lift)

crunch pspace_domain_valid[wp]: storePTE "pspace_domain_valid"
  (wp: hoare_drop_imp)

lemma storePTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePTE_nosch])
  apply (wpsimp simp: storePTE_def updateObject_default_def wp: hoare_drop_imp)
   apply (wps setObject_PDE_ct)
   apply (wpsimp wp: obj_at_setObject2 simp: updateObject_default_def in_monad)+
  done

lemma setObject_pte_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pte_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pte) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePTE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  by (wpsimp wp: headM_inv hoare_drop_imp simp: storePTE_def updateObject_default_def)

lemma storePTE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  by (wpsimp wp: hoare_drop_imp obj_at_setObject2 simp: storePTE_def updateObject_default_def in_monad)

lemma storePTE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePTE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma storePTE_invs [wp]:
  "\<lbrace>invs' and valid_pte' pte\<rbrace> storePTE p pte \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
            valid_arch_state_lift' valid_irq_node_lift
            cur_tcb_lift valid_irq_handlers_lift''
            untyped_ranges_zero_lift valid_bitmaps_lift
          | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma setASIDPool_valid_objs [wp]:
  "\<lbrace>valid_objs' and valid_asid_pool' ap\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_valid_objs')
   prefer 2
   apply assumption
  apply (clarsimp simp: updateObject_default_def in_monad)
  apply (clarsimp simp: valid_obj'_def)
  done

lemma setASIDPool_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

lemma setASIDPool_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (wp setObject_nosch updateObject_default_inv|simp)+

lemma setASIDPool_ksQ [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueues s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace>
     setObject ptr (ap::asidpool)
   \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def)
  apply (wp setObject_ko_wp_at
            | simp add: objBits_simps archObjSize_def)+
   apply (simp add: pageBits_def)
  apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  done

lemma setASIDPool_qsL1 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_qsL2 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  by (wp setObject_qs updateObject_default_inv|simp)+

lemma setASIDPool_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma setASIDPool_state_hyp_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_hyp_refs_of'_def ps_clear_upd
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma setASIDPool_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad live'_def hyp_live'_def arch_live'_def projectKOs pageBits_def)
  done

lemma setASIDPool_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

lemma setASIDPool_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma setASIDPool_it' [wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksIdleThread s)\<rbrace>"
  by (wp setObject_it updateObject_default_inv|simp)+

lemma setASIDPool_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_idle'\<rbrace>" by valid_idle'_setObject

lemma setASIDPool_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=ksInterruptState, OF setObject_ksInterrupt])
    apply (simp, rule updateObject_default_inv)
   apply (rule hoare_use_eq [where f=ksMachineState, OF setObject_ksMachine])
    apply (simp, rule updateObject_default_inv)
   apply wp
  apply assumption
  done

lemma setObject_asidpool_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (wp valid_pde_mappings_lift')
   apply (rule obj_at_setObject2)
   apply (clarsimp dest!: updateObject_default_result)
  apply assumption
  done

lemma setASIDPool_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

lemma setASIDPool_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF setObject_nosch])
   apply (simp add: updateObject_default_def | wp)+
  apply (rule hoare_weaken_pre)
   apply (wps setObject_ASID_ct)
  apply (rule obj_at_setObject2)
   apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_asidpool_cur'[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  apply (simp add: setObject_def)
  apply (wp | wpc | simp add: updateObject_default_def)+
  done

lemma setObject_asidpool_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_asidpool_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma setObject_asidpool_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma setObject_asidpool_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
      apply (wp hoare_vcg_disj_lift)+
  done

lemma setObject_ap_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma setObject_asidpool_tcbs_of'[wp]:
  "setObject c (asidpool::asidpool) \<lbrace>\<lambda>s. P' (tcbs_of' s)\<rbrace>"
  by setObject_easy_cases

lemma setASIDPool_invs [wp]:
  "\<lbrace>invs' and valid_asid_pool' ap\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
              valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
             updateObject_default_inv valid_bitmaps_lift
           | simp add: cteCaps_of_def
           | rule setObject_ksPSpace_only)+
  apply (clarsimp simp add: setObject_def o_def)
  done

crunches vcpuSave, vcpuRestore, vcpuDisable, vcpuEnable
  for cte_wp_at'[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"
  (simp: crunch_simps wp: crunch_wps getObject_inv_vcpu loadObject_default_inv)

lemma vcpuSwitch_cte_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at' P' p s)\<rbrace> vcpuSwitch param_a \<lbrace>\<lambda>_ s. P (cte_wp_at' P' p s)\<rbrace> "
  by (wpsimp simp: vcpuSwitch_def modifyArchState_def | assumption)+

crunch cte_wp_at'[wp]: unmapPageTable "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas storePDE_Invalid_invs = storePDE_invs[where pde=InvalidPDE, simplified]

lemma setVMRootForFlush_invs'[wp]: "\<lbrace>invs'\<rbrace> setVMRootForFlush a b \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: setVMRootForFlush_def)
  apply (wp storePDE_Invalid_invs mapM_wp' crunch_wps | simp add: crunch_simps)+
  apply (simp add: getThreadVSpaceRoot_def)
  apply (wp storePDE_Invalid_invs mapM_wp' crunch_wps | simp add: crunch_simps)+
  done


lemma dmo_invalidateLocalTLB_VAASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (invalidateLocalTLB_VAASID x) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_invalidateLocalTLB_VAASID no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply (clarsimp simp: invalidateLocalTLB_VAASID_def machine_op_lift_def
                          machine_rest_lift_def split_def | wp)+
  done

lemma dmo_cVA_PoU_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (cleanByVA_PoU w p) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_cleanByVA_PoU no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' pa = underlying_memory m pa"
         in use_valid)
    apply (clarsimp simp: cleanByVA_PoU_def machine_op_lift_def
                          machine_rest_lift_def split_def | wp)+
  done

lemma dmo_ccr_PoU_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (cleanCacheRange_PoU s e p) \<lbrace>\<lambda>r. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_cleanCacheRange_PoU no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' pa = underlying_memory m pa"
         in use_valid)
    apply (clarsimp simp: cleanCacheRange_PoU_def machine_op_lift_def
                          machine_rest_lift_def split_def | wp)+
  done

(* FIXME: Move *)
lemma dmo_invalidateLocalTLB_ASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (invalidateLocalTLB_ASID a) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_invalidateLocalTLB_ASID no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: invalidateLocalTLB_ASID_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_cleanCaches_PoU_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp cleanCaches_PoU \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_cleanCaches_PoU no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: cleanCaches_PoU_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

crunch invs'[wp]: unmapPageTable "invs'"
  (ignore: storePDE doMachineOp
       wp: dmo_invalidateLocalTLB_VAASID_invs' dmo_setCurrentPD_invs'
           storePDE_Invalid_invs mapM_wp' no_irq_setCurrentPD
           crunch_wps
     simp: crunch_simps)

lemma perform_pti_invs [wp]:
  "\<lbrace>invs' and valid_pti' pti\<rbrace> performPageTableInvocation pti \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performPageTableInvocation_def getSlotCap_def
                 split: page_table_invocation.splits)
  apply (intro conjI allI impI)
   apply (rule hoare_pre)
    apply (wp arch_update_updateCap_invs getCTE_wp
              hoare_vcg_ex_lift no_irq_cleanCacheRange_PoU mapM_x_wp'
                | wpc | simp add: o_def
                | (simp only: imp_conv_disj, rule hoare_vcg_disj_lift))+
   apply (clarsimp simp: valid_pti'_def cte_wp_at_ctes_of
                         is_arch_update'_def isCap_simps valid_cap'_def
                         capAligned_def)
  apply (rule hoare_pre)
   apply (wp arch_update_updateCap_invs valid_pde_lift'
             no_irq_cleanByVA_PoU
          | simp)+
  apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
  done

crunch invs'[wp]: setVMRootForFlush "invs'"

lemma addPTEOffset_Invalid[simp]:
  "addPTEOffset InvalidPTE x = InvalidPTE"
  by (simp add: addPTEOffset_def)

lemma in_set_zip_singleton[simp]:
  "(x, y) \<in> set (zip xs [z]) = ((\<exists>xs'. xs = x#xs') \<and> y = z)"
  by (cases xs) auto

lemma valid_pte'_offset:
  "\<lbrakk> valid_pte' pte s; x \<le> 15; pte = LargePagePTE p a b c; vmsz_aligned' p ARMLargePage \<rbrakk>
  \<Longrightarrow> valid_pte' (addPTEOffset pte x) s"
  using is_aligned_mult_triv2[of x 12, simplified] is_aligned_pptrBaseOffset [of ARMLargePage]
  apply (clarsimp simp: addPTEOffset_def valid_mapping'_def addPAddr_def fromPAddr_def is_aligned_add)
  apply (clarsimp simp: ptrFromPAddr_def vmsz_aligned'_def)
  apply (drule aligned_offset_non_zero[rotated -1, where n=16 and y="x * 0x1000"])
    apply (erule is_aligned_add, simp)
   apply simp
   apply (rule word_less_power_trans2[where k=12 and m=16, simplified])
    apply unat_arith
   apply simp
  apply (simp add: add_ac)
  done

lemma mapM_x_storePTE_invs:
  "\<lbrace>invs' and valid_pte' pte and
    K (pte_vmsz_aligned' pte \<and> length slots = (case pte of LargePagePTE _ _ _ _ \<Rightarrow> 16 | _ \<Rightarrow> 1))\<rbrace>
     mapM_x (\<lambda>(slot, i). storePTE slot (addPTEOffset pte i))
            (zip slots [(0::32 word).e.of_nat (length slots - Suc 0)])
  \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_x_wp')
   apply (wpsimp wp: valid_pte_lift')
   apply (clarsimp split: pte.splits)
   apply (rule valid_pte'_offset; simp?)
   apply (drule in_set_zip2, simp)
  apply simp
  done

lemma valid_pde'_offset:
  "\<lbrakk> valid_pde' pde s; x \<le> 15; pde = SuperSectionPDE p a b c; vmsz_aligned' p ARMSuperSection \<rbrakk>
  \<Longrightarrow> valid_pde' (addPDEOffset pde x) s"
  using is_aligned_mult_triv2[of x 21, simplified] is_aligned_pptrBaseOffset [of ARMSuperSection]
  apply (clarsimp simp: addPDEOffset_def valid_mapping'_def addPAddr_def fromPAddr_def is_aligned_add)
  apply (clarsimp simp: ptrFromPAddr_def vmsz_aligned'_def)
  apply (drule aligned_offset_non_zero[rotated -1, where n=25 and y="x * 0x200000"])
    apply (erule is_aligned_add, simp)
   apply simp
   apply (rule word_less_power_trans2[where k=21 and m=25, simplified])
    apply unat_arith
   apply simp
  apply (simp add: add_ac)
  done

lemma addPDEOffset_InvalidPDE[simp]:
  "(addPDEOffset pde x = InvalidPDE) = (pde = InvalidPDE)"
  by (cases pde; simp add: addPDEOffset_def)

lemma mapM_x_storePDE_invs:
  "\<lbrace>invs' and valid_pde' pde and K (\<forall>p \<in> set slots. valid_pde_mapping' (p && mask pdBits) pde) and
    K (pde_vmsz_aligned' pde \<and> length slots = (case pde of SuperSectionPDE _ _ _ _ \<Rightarrow> 16 | _ \<Rightarrow> 1))\<rbrace>
     mapM_x (\<lambda>(slot, i). storePDE slot (addPDEOffset pde i))
            (zip slots [(0::32 word).e.of_nat (length slots - Suc 0)])
  \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_x_wp')
   apply (wpsimp wp: valid_pde_lift')
   apply (rule conjI)
    apply (clarsimp split: pde.splits)
    apply (rule valid_pde'_offset; simp?)
    apply (drule in_set_zip2, simp)
   apply (clarsimp simp: valid_pde_mapping'_def)
   apply (drule in_set_zip1, simp)
  apply simp
  done

lemma mapM_storePTE_invs:
  "\<lbrace>invs' and valid_pte' pte\<rbrace> mapM (swp storePTE pte) ps \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (wp valid_pte_lift')
    apply simp+
  done

lemma mapM_storePDE_invs:
  "\<lbrace>invs' and valid_pde' pde
       and K (\<forall>p \<in> set ps. valid_pde_mapping' (p && mask pdBits) pde)\<rbrace>
       mapM (swp storePDE pde) ps \<lbrace>\<lambda>xa. invs'\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (wp valid_pde_lift')
    apply simp+
  done

crunch cte_wp_at': unmapPage "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas unmapPage_typ_ats [wp] = typ_at_lifts [OF unmapPage_typ_at']

crunch inv: lookupPTSlot P
  (wp: crunch_wps simp: crunch_simps)

lemma flushPage_invs' [wp]:
  "\<lbrace>invs'\<rbrace> flushPage sz pd asid vptr \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: flushPage_def)
  apply (wp dmo_invalidateLocalTLB_VAASID_invs' hoare_drop_imps setVMRootForFlush_invs'
            no_irq_invalidateLocalTLB_VAASID
         |simp)+
  done

lemma unmapPage_invs' [wp]:
  "\<lbrace>invs'\<rbrace> unmapPage sz asid vptr pptr \<lbrace>\<lambda>_. invs'\<rbrace>"
  unfolding unmapPage_def
  by (wpsimp wp: lookupPTSlot_inv mapM_storePTE_invs mapM_storePDE_invs
                 hoare_vcg_const_imp_lift)

crunch (no_irq) no_irq[wp]: doFlush
  (simp: Let_def)

crunches pteCheckIfMapped, pdeCheckIfMapped
  for invs'[wp]: "invs'"
  and valid_pte'[wp]: "valid_pte' pte"
  and valid_pde'[wp]: "valid_pde' pde"

lemma perform_pt_invs [wp]:
  notes no_irq[wp]
  shows
  "\<lbrace>invs' and valid_page_inv' pt\<rbrace> performPageInvocation pt \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: performPageInvocation_def)
  apply (cases pt)
     apply clarsimp
     apply ((wp dmo_invs' hoare_vcg_all_lift setVMRootForFlush_invs' | simp add: tcb_at_invs')+)[2]
       apply (rule hoare_pre_imp[of _ \<top>], assumption)
       apply (clarsimp simp: valid_def
                             disj_commute[of "pointerInUserData p s" for p s])
       apply (thin_tac "x : fst (setVMRootForFlush a b s)" for x a b)
       apply (erule use_valid)
        apply (clarsimp simp: doFlush_def Let_def split: flush_type.splits)
        apply (clarsimp simp: mapM_mapM_x split: sum.split | intro conjI impI
               | wp mapM_x_storePTE_invs mapM_x_storePDE_invs)
     apply (clarsimp simp: valid_page_inv'_def valid_slots'_def
                           valid_pde_slots'_def mapM_mapM_x
                    split: sum.split option.splits
            | intro conjI impI
            | wp mapM_storePTE_invs mapM_storePDE_invs
                 mapM_x_storePTE_invs mapM_x_storePDE_invs
                 hoare_vcg_all_lift hoare_vcg_const_imp_lift
                 arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp
            | wpc
            | drule valid_slots_duplicated'_length_Inl valid_slots_duplicated'_length_Inr)+
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (case_tac cte)
   apply clarsimp
   apply (drule ctes_of_valid_cap', fastforce)
   apply (clarsimp simp: valid_cap'_def cte_wp_at_ctes_of valid_page_inv'_def
                         capAligned_def is_arch_update'_def isCap_simps)
  apply clarsimp
  apply (wp arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp|wpc)+
  apply (rename_tac acap word a b)
  apply (rule_tac Q="\<lambda>_. invs' and cte_wp_at' (\<lambda>cte. \<exists>d r R sz m. cteCap cte =
                                       ArchObjectCap (PageCap d r R sz m)) word"
               in hoare_strengthen_post)
    apply (wp unmapPage_cte_wp_at')
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (case_tac cte)
   apply clarsimp
   apply (frule ctes_of_valid_cap')
    apply (auto simp: valid_page_inv'_def valid_slots'_def
                      cte_wp_at_ctes_of valid_pde_slots'_def)[1]
   apply (simp add: is_arch_update'_def isCap_simps)
   apply (simp add: valid_cap'_def capAligned_def)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (simp add: is_arch_update'_def isCap_simps)
  apply (case_tac cte)
  apply clarsimp+
  done

lemma ucast_ucast_le_low_bits [simp]:
  "ucast (ucast x :: 10 word) \<le> (2 ^ asid_low_bits - 1 :: word32)"
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
   apply (rule ucast_less)
   apply simp
  apply (simp add: asid_low_bits_def)
  done

lemma perform_aci_invs [wp]:
  "\<lbrace>invs' and valid_apinv' api\<rbrace> performASIDPoolInvocation api \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (clarsimp simp: performASIDPoolInvocation_def split: asidpool_invocation.splits)
  apply (wp arch_update_updateCap_invs getASID_wp getSlotCap_wp)
  apply (clarsimp simp: valid_apinv'_def cte_wp_at_ctes_of)
  apply (case_tac cte)
  apply clarsimp
  apply (drule ctes_of_valid_cap', fastforce)
  apply (clarsimp simp: isPDCap_def valid_cap'_def capAligned_def is_arch_update'_def isCap_simps)
  apply (drule ko_at_valid_objs', fastforce, simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def ran_def mask_asid_low_bits_ucast_ucast
                 split: if_split_asm)
  apply (case_tac ko, clarsimp simp: inv_def)
  apply (clarsimp simp: page_directory_at'_def, drule_tac x=0 in spec)
  apply auto
  done

lemma capMaster_isPDCap:
  "capMasterCap cap' = capMasterCap cap \<Longrightarrow> isPDCap cap' = isPDCap cap"
  by (simp add: capMasterCap_def isPDCap_def split: capability.splits arch_capability.splits)

lemma isPDCap_PD :
  "isPDCap (ArchObjectCap (PageDirectoryCap r m))"
  by (simp add: isPDCap_def)


end

end
