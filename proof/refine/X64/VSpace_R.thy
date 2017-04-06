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
   X64 VSpace refinement
*)

theory VSpace_R
imports TcbAcc_R
begin
context Arch begin global_naming X64 (*FIXME: arch_split*)

(* FIXME x64: move *)
lemmas store_pde_typ_ats' [wp] = abs_typ_at_lifts [OF store_pde_typ_at]
lemmas store_pdpte_typ_ats' [wp] = abs_typ_at_lifts [OF store_pdpte_typ_at]
lemmas store_pte_typ_ats[wp] = store_pte_typ_ats abs_atyp_at_lifts[OF store_pte_typ_at]
lemmas store_pde_typ_ats[wp] = store_pde_typ_ats' abs_atyp_at_lifts[OF store_pde_typ_at]
lemmas store_pdpte_typ_ats[wp] = store_pdpte_typ_ats' abs_atyp_at_lifts[OF store_pdpte_typ_at]

end

context begin interpretation Arch . (*FIXME: arch_split*)

crunch_ignore (add: throw_on_false)

definition
  "vspace_at_asid' vs asid \<equiv> \<lambda>s. \<exists>ap pool.
             x64KSASIDTable (ksArchState s) (ucast (asid_high_bits_of asid)) = Some ap \<and>
             ko_at' (ASIDPool pool) ap s \<and> pool (asid && mask asid_low_bits) = Some vs \<and>
             page_map_l4_at' vs s"

defs checkPML4ASIDMapMembership_def:
  "checkPML4ASIDMapMembership pd asids
     \<equiv> stateAssert (\<lambda>s. pd \<notin> ran ((x64KSASIDMap (ksArchState s) |` (- set asids)))) []"

crunch inv[wp]:checkPDAt P

lemma findVSpaceForASID_vs_at_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. (page_map_l4_at' pd s \<longrightarrow> vspace_at_asid' pd asid s)
            \<longrightarrow> P pd s\<rbrace> findVSpaceForASID asid \<lbrace>P\<rbrace>,-"
  apply (simp add: findVSpaceForASID_def assertE_def
             cong: option.case_cong
               split del: if_split)
  apply (rule hoare_pre)
   apply (wp getASID_wp | wpc | simp add: o_def split del: if_split)+
  apply (clarsimp simp: vspace_at_asid'_def)
  apply (case_tac ko, simp)
  apply (subst(asm) inv_f_f)
   apply (rule inj_onI, simp+)
  apply fastforce
  done

lemma findVSpaceForASIDAssert_vs_at_wp:
  "\<lbrace>(\<lambda>s. \<forall>pd. vspace_at_asid' pd asid  s
               \<and> pd \<notin> ran (( x64KSASIDMap (ksArchState s) |` (- {asid})))
                \<longrightarrow> P pd s)\<rbrace>
       findVSpaceForASIDAssert asid \<lbrace>P\<rbrace>"
  apply (simp add: findVSpaceForASIDAssert_def const_def
                   checkPML4At_def checkPML4UniqueToASID_def
                   checkPML4ASIDMapMembership_def)
  apply (rule hoare_pre, wp getPDE_wp findVSpaceForASID_vs_at_wp)
  apply simp
  done

crunch inv[wp]: findVSpaceForASIDAssert "P"
  (simp: const_def crunch_simps wp: loadObject_default_inv crunch_wps)

lemma pspace_relation_pml4:
  assumes p: "pspace_relation (kheap a) (ksPSpace c)"
  assumes pa: "pspace_aligned a"
  assumes pad: "pspace_aligned' c" "pspace_distinct' c"
  assumes t: "page_map_l4_at p a"
  shows "page_map_l4_at' p c"
  using assms is_aligned_pml4 [OF t pa]
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_relation_absD)
  apply (clarsimp simp: a_type_def
                 split: Structures_A.kernel_object.split_asm
                        if_split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: page_map_l4_at'_def bit_simps
                        typ_at_to_obj_at_arches)
  apply (drule_tac x="ucast y" in spec, clarsimp)
  apply (simp add: ucast_ucast_mask iffD2 [OF mask_eq_iff_w2p] word_size)
  apply (clarsimp simp add: pml4e_relation_def)
  apply (drule(2) aligned_distinct_pml4e_atI')
  apply (erule obj_at'_weakenE)
  apply simp
  done

lemma find_vspace_for_asid_eq_helper:
  "\<lbrakk> vspace_at_asid asid pd s; valid_arch_objs s;
         asid \<noteq> 0; pspace_aligned s \<rbrakk>
    \<Longrightarrow> find_vspace_for_asid asid s = returnOk pd s
             \<and> page_map_l4_at pd s \<and> is_aligned pd pml4Bits"
  apply (clarsimp simp: vspace_at_asid_def valid_arch_objs_def)
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
  apply (simp add: find_vspace_for_asid_def bind_assoc
                   word_neq_0_conv[symmetric] liftE_bindE)
  apply (simp add: exec_gets liftE_bindE bind_assoc
                   get_asid_pool_def get_object_def)
  apply (simp add: mask_asid_low_bits_ucast_ucast)
  apply (clarsimp simp: returnOk_def get_pml4e_def
                        get_pml4_def get_object_def
                        bind_assoc)
  apply (frule(1) pspace_alignedD[where p=pd])
  apply (simp add: bit_simps)
  done

lemma find_vspace_for_asid_assert_eq:
  "\<lbrakk> vspace_at_asid asid pd s; valid_arch_objs s;
         asid \<noteq> 0; pspace_aligned s \<rbrakk>
    \<Longrightarrow> find_vspace_for_asid_assert asid s = return pd s"
  apply (drule(3) find_vspace_for_asid_eq_helper)
  apply (simp add: find_vspace_for_asid_assert_def
                   catch_def bind_assoc)
  apply (clarsimp simp: returnOk_def obj_at_def
                        a_type_def
                  cong: bind_apply_cong)
  apply (clarsimp split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits if_split_asm)
  apply (simp add: get_pml4e_def get_pml4_def get_object_def
                   bind_assoc is_aligned_neg_mask_eq
                   bit_simps)
  apply (simp add: exec_gets)
  done

lemma find_vspace_for_asid_valids:
  "\<lbrace> vspace_at_asid asid pd and valid_arch_objs
         and pspace_aligned and K (asid \<noteq> 0) \<rbrace>
     find_vspace_for_asid asid \<lbrace>\<lambda>rv s. pml4e_at rv s\<rbrace>,-"
  "\<lbrace> vspace_at_asid asid pd and valid_arch_objs
         and pspace_aligned and K (asid \<noteq> 0)
         and K (is_aligned pd pml4Bits \<longrightarrow> P pd) \<rbrace>
     find_vspace_for_asid asid \<lbrace>\<lambda>rv s. P rv\<rbrace>,-"
  "\<lbrace> vspace_at_asid asid pd and valid_arch_objs
         and pspace_aligned and K (asid \<noteq> 0)
         and vspace_at_uniq asid pd \<rbrace>
     find_vspace_for_asid asid \<lbrace>\<lambda>rv s. vspace_at_uniq asid rv s\<rbrace>,-"
  "\<lbrace> vspace_at_asid asid pd and valid_arch_objs
         and pspace_aligned and K (asid \<noteq> 0) \<rbrace>
     find_vspace_for_asid asid -,\<lbrace>\<bottom>\<bottom>\<rbrace>"
  apply (simp_all add: validE_def validE_R_def validE_E_def
                       valid_def split: sum.split)
  apply (auto simp: returnOk_def return_def
                    pml4e_at_def bit_simps
                     is_aligned_neg_mask_eq
             dest!: find_vspace_for_asid_eq_helper
             elim!: is_aligned_weaken)
  done

lemma valid_asid_map_inj_map:
  "\<lbrakk> valid_asid_map s; (s, s') \<in> state_relation;
        unique_table_refs (caps_of_state s);
        valid_vs_lookup s; valid_arch_objs s;
        valid_arch_state s; valid_global_objs s \<rbrakk>
        \<Longrightarrow> inj_on (x64KSASIDMap (ksArchState s'))
                   (dom (x64KSASIDMap (ksArchState s')))"
  apply (rule inj_onI)
  apply (clarsimp simp: valid_asid_map_def state_relation_def
                        arch_state_relation_def)
  apply (frule_tac c=x in subsetD, erule domI)
  apply (frule_tac c=y in subsetD, erule domI)
  apply (drule(1) bspec [rotated, OF graph_ofI])+
  apply clarsimp
  apply (erule(6) vspace_at_asid_unique)
   apply (simp add: mask_def)+
  done

lemma asidBits_asid_bits[simp]:
  "asidBits = asid_bits"
  by (simp add: asid_bits_def asidBits_def
                asidHighBits_def asid_low_bits_def)

lemma find_vspace_for_asid_assert_corres:
  "corres (\<lambda>rv rv'. rv = pm \<and> rv' = pm)
           (K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits)
                 and pspace_aligned and pspace_distinct
                 and valid_arch_objs and valid_asid_map
                 and vspace_at_asid asid pm and vspace_at_uniq asid pm)
           (pspace_aligned' and pspace_distinct' and no_0_obj')
       (find_vspace_for_asid_assert asid)
       (findVSpaceForASIDAssert asid)"
  apply (simp add: find_vspace_for_asid_assert_def const_def
                   findVSpaceForASIDAssert_def liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr)
       apply (rule_tac F="is_aligned pml4 pml4Bits
                               \<and> pml4 = pm" in corres_gen_asm)
       apply (clarsimp simp add: is_aligned_mask[symmetric])
       apply (rule_tac P="pml4e_at pm and vspace_at_uniq asid pm
                             and pspace_aligned and pspace_distinct
                             and vspace_at_asid asid pm and valid_asid_map"
                  and P'="pspace_aligned' and pspace_distinct'"
                  in stronger_corres_guard_imp)
        apply (rule corres_symb_exec_l[where P="pml4e_at pm and vspace_at_uniq asid pm
                                                and valid_asid_map and vspace_at_asid asid pm"])
            apply (rule corres_symb_exec_r[where P'="page_map_l4_at' pm"])
               apply (simp add: checkPML4UniqueToASID_def ran_option_map
                                checkPML4ASIDMapMembership_def)
               apply (rule_tac P'="vspace_at_uniq asid pm" in corres_stateAssert_implied)
                apply (simp add: gets_def bind_assoc[symmetric]
                                 stateAssert_def[symmetric, where L="[]"])
                apply (rule_tac P'="valid_asid_map and vspace_at_asid asid pm"
                                 in corres_stateAssert_implied)
                 apply (rule corres_trivial, simp)
                apply (clarsimp simp: state_relation_def arch_state_relation_def
                                      valid_asid_map_def
                               split: option.split)
                apply (drule bspec, erule graph_ofI)
                apply clarsimp
                apply (drule(1) vspace_at_asid_unique2)
                apply simp
               apply (clarsimp simp: state_relation_def arch_state_relation_def
                                     vspace_at_uniq_def ran_option_map)
              apply wp+
            apply (simp add: checkPML4At_def stateAssert_def)
            apply (rule no_fail_pre, wp)
            apply simp
           apply (clarsimp simp: pml4e_at_def obj_at_def a_type_def is_aligned_neg_mask_eq)
           apply (clarsimp split: Structures_A.kernel_object.splits
                                  arch_kernel_obj.splits if_split_asm)
           apply (simp add: get_pml4e_def exs_valid_def bind_def return_def
                            get_pml4_def get_object_def simpler_gets_def)
          apply wp
          apply simp
         apply (simp add: get_pml4e_def get_pml4_def)
         apply (rule no_fail_pre)
          apply (wp get_object_wp | wpc)+
         apply (clarsimp simp: pml4e_at_def obj_at_def a_type_def is_aligned_neg_mask_eq)
         apply (clarsimp split: Structures_A.kernel_object.splits
                                arch_kernel_obj.splits if_split_asm)
        apply simp
       apply (clarsimp simp: state_relation_def)
       apply (erule(3) pspace_relation_pml4)
       apply (simp add: pml4e_at_def bit_simps
                        is_aligned_neg_mask_eq)
      apply (rule corres_split_catch [OF _ find_vspace_for_asid_corres'[where pd=pm]])
        apply (rule_tac P="\<bottom>" and P'="\<top>" in corres_inst)
        apply (simp add: corres_fail)
       apply (wp find_vspace_for_asid_valids[where pd=pm])+
   apply (clarsimp simp: word_neq_0_conv)
  apply simp
  done

lemma findVSpaceForASIDAssert_known_corres:
  "corres r P P' f (g pd) \<Longrightarrow>
  corres r (vspace_at_asid asid pd and vspace_at_uniq asid pd
               and valid_arch_objs and valid_asid_map
               and pspace_aligned and pspace_distinct
               and K (asid \<noteq> 0 \<and> asid \<le> mask asid_bits) and P)
           (P' and pspace_aligned' and pspace_distinct' and no_0_obj')
       f (findVSpaceForASIDAssert asid >>= g)"
  apply (subst return_bind[symmetric])
  apply (subst corres_cong [OF refl refl _ refl refl])
   apply (rule bind_apply_cong [OF _ refl])
   apply clarsimp
   apply (erule(3) find_vspace_for_asid_assert_eq[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ find_vspace_for_asid_assert_corres[where pm=pd]])
      apply simp
     apply wp+
   apply clarsimp
  apply simp
  done

lemma invalidate_asid_corres:
  "corres dc
          (valid_asid_map and valid_arch_objs
               and pspace_aligned and pspace_distinct
               and vspace_at_asid a pd and vspace_at_uniq a pd
               and K (a \<noteq> 0 \<and> a \<le> mask asid_bits))
          (pspace_aligned' and pspace_distinct' and no_0_obj')
     (invalidate_asid a) (invalidateASID' a)"
  (is "corres dc ?P ?P' ?f ?f'")
  apply (simp add: invalidate_asid_def invalidateASID'_def)
  apply (rule corres_guard_imp)
    apply (rule_tac pd=pd in findVSpaceForASIDAssert_known_corres)
    apply (rule_tac P="?P" and P'="?P'" in corres_inst)
    apply (rule_tac r'="op =" in corres_split' [OF _ _ gets_sp gets_sp])
     apply (clarsimp simp: state_relation_def arch_state_relation_def)
    apply (rule corres_modify)
    apply (simp add: state_relation_def arch_state_relation_def
                     fun_upd_def)
   apply simp
  apply simp
  done

lemma invalidate_asid_ext_corres:
  "corres dc
          (\<lambda>s. \<exists>pd. valid_asid_map s \<and> valid_arch_objs s
               \<and> pspace_aligned s \<and> pspace_distinct s
               \<and> vspace_at_asid a pd s \<and> vspace_at_uniq a pd s
               \<and> a \<noteq> 0 \<and> a \<le> mask asid_bits)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
     (invalidate_asid a) (invalidateASID' a)"
  apply (insert invalidate_asid_corres)
  apply (clarsimp simp: corres_underlying_def)
  apply fastforce
  done

(* FIXME x64: move *)
lemma no_fail_getFaultAddress[wp]: "no_fail \<top> getFaultAddress"
  by (simp add: getFaultAddress_def)

lemma hv_corres:
  "corres (fr \<oplus> dc) (tcb_at thread) (tcb_at' thread)
          (handle_vm_fault thread fault) (handleVMFault thread fault)"
  apply (simp add: X64_H.handleVMFault_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqrE)
       apply (rule corres_split_eqrE)
          apply (cases fault; simp)
         apply simp
         apply (rule user_getreg_corres[simplified get_register_eq[symmetric]])
        apply (simp, wp as_user_tcb_at)
       apply (simp, wp asUser_typ_ats)
      apply simp
      apply (rule corres_machine_op [where r="op ="])
      apply (rule corres_Id, rule refl, simp)
      apply (rule no_fail_getFaultAddress)
     apply wpsimp+
  done

crunch valid_global_objs[wp]: do_machine_op "valid_global_objs"

lemma state_relation_asid_map:
  "(s, s') \<in> state_relation \<Longrightarrow> x64KSASIDMap (ksArchState s') = x64_asid_map (arch_state s)"
  by (simp add: state_relation_def arch_state_relation_def)

lemma find_vspace_for_asid_vspace_at_asid_again:
  "\<lbrace>\<lambda>s. (\<forall>pd. vspace_at_asid asid pd s \<longrightarrow> P pd s)
       \<and> (\<forall>ex. (\<forall>pd. \<not> vspace_at_asid asid pd s) \<longrightarrow> Q ex s)
       \<and> valid_arch_objs s \<and> pspace_aligned s \<and> asid \<noteq> 0\<rbrace>
      find_vspace_for_asid asid
   \<lbrace>P\<rbrace>,\<lbrace>Q\<rbrace>"
  apply (unfold validE_def, rule hoare_name_pre_state, fold validE_def)
  apply (case_tac "\<exists>pd. vspace_at_asid asid pd s")
   apply clarsimp
   apply (rule_tac Q="\<lambda>rv s'. s' = s \<and> rv = pd" and E="\<bottom>\<bottom>" in hoare_post_impErr)
     apply (rule hoare_pre, wp find_vspace_for_asid_valids)
     apply fastforce
    apply simp+
  apply (rule_tac Q="\<lambda>rv s'. s' = s \<and> vspace_at_asid asid rv s'"
              and E="\<lambda>rv s'. s' = s" in hoare_post_impErr)
    apply (rule hoare_pre, wp)
    apply clarsimp+
  done

(* FIXME x64: move *)
lemma no_fail_writeCR3[wp]: "no_fail \<top> (writeCR3 a b)"
  by (simp add: writeCR3_def)

lemma setCurrentCR3_corres:
  "cr3_relation cr3 cr3' \<Longrightarrow> corres dc \<top> \<top> (X64_A.setCurrentCR3 cr3) (setCurrentCR3 cr3')"
  apply (clarsimp simp add: X64_A.setCurrentCR3_def setCurrentCR3_def cr3_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule corres_machine_op)
       apply (rule corres_Id, rule refl, simp)
       apply (rule no_fail_writeCR3)
      apply (rule corres_modify')
       apply (clarsimp simp: state_relation_def arch_state_relation_def cr3_relation_def)
      apply (simp add: dc_def)
     apply wpsimp+
  done

lemma getCurrentCR3_corres:
  "corres cr3_relation \<top> \<top> (X64_A.getCurrentCR3) (getCurrentCR3)"
  apply (simp add: getCurrentCR3_def X64_A.getCurrentCR3_def)
  by (clarsimp simp: state_relation_def arch_state_relation_def)

lemma update_asid_map_corres:
  "corres dc
          (K (a \<noteq> 0 \<and> a \<le> mask asid_bits) and
                pspace_aligned and pspace_distinct and
                valid_arch_objs and valid_asid_map and
                vspace_at_asid a pm and vspace_at_uniq a pm)
          (pspace_aligned' and pspace_distinct' and no_0_obj')
          (update_asid_map a) (updateASIDMap a)"
  apply (simp add: update_asid_map_def updateASIDMap_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split')
       apply (rule find_vspace_for_asid_assert_corres[where pm=pm])
      apply (rule corres_split_eqr)
         apply (rule corres_modify')
          apply (clarsimp simp: state_relation_def arch_state_relation_def)
          apply fastforce
         apply (simp add: dc_def)
        apply (clarsimp simp add: state_relation_def arch_state_relation_def)
       apply wpsimp+
  done

lemma set_vm_root_corres:
  "corres dc (tcb_at t and valid_arch_state and valid_objs and valid_asid_map
              and unique_table_refs o caps_of_state and valid_vs_lookup
              and valid_global_objs and pspace_aligned and pspace_distinct
              and valid_arch_objs)
             (pspace_aligned' and pspace_distinct'
                 and valid_arch_state' and tcb_at' t and no_0_obj')
             (set_vm_root t) (setVMRoot t)"
proof -
  have P: "corres dc \<top> \<top>
        (do global_pml4 \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
            X64_A.setCurrentVSpaceRoot (X64.addrFromKPPtr global_pml4) 0
         od)
        (do globalPML4 \<leftarrow> gets (x64KSGlobalPML4 \<circ> ksArchState);
            X64_H.setCurrentVSpaceRoot (addrFromKPPtr globalPML4) 0
         od)"
    apply (simp add: X64_H.setCurrentVSpaceRoot_def X64_A.setCurrentVSpaceRoot_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split_eqr)
         apply (rule setCurrentCR3_corres, simp add: cr3_relation_def addrFromKPPtr_def)
        apply (subst corres_gets)
        apply (clarsimp simp: state_relation_def arch_state_relation_def)
       apply (wp | simp)+
    done
  have Q: "\<And>P P'. corres dc P P'
        (throwError ExceptionTypes_A.lookup_failure.InvalidRoot <catch>
         (\<lambda>_ . do global_pml4 \<leftarrow> gets (x64_global_pml4 \<circ> arch_state);
                  X64_A.setCurrentVSpaceRoot (X64.addrFromKPPtr global_pml4) 0
               od))
        (throwError Fault_H.lookup_failure.InvalidRoot <catch>
         (\<lambda>_ . do globalPML4 \<leftarrow> gets (x64KSGlobalPML4 \<circ> ksArchState);
                  setCurrentVSpaceRoot (addrFromKPPtr globalPML4) 0
               od))"
    apply (rule corres_guard_imp)
      apply (rule corres_split_catch [where f=lfr])
         apply (simp, rule P)
        apply (subst corres_throwError, simp add: lookup_failure_map_def)
       apply (wp | simp)+
    done
  show ?thesis
    unfolding set_vm_root_def setVMRoot_def locateSlot_conv
                     getThreadVSpaceRoot_def
    apply (rule corres_guard_imp)
      apply (rule corres_split' [where r'="op = \<circ> cte_map"])
         apply (simp add: tcbVTableSlot_def cte_map_def objBits_def cte_level_bits_def
                          objBitsKO_def tcb_cnode_index_def to_bl_1)
        apply (rule_tac R="\<lambda>thread_root. valid_arch_state and valid_asid_map and
                                         valid_arch_objs and valid_vs_lookup and
                                         unique_table_refs o caps_of_state and
                                         valid_global_objs and valid_objs and
                                         pspace_aligned and pspace_distinct and
                                         cte_wp_at (op = thread_root) thread_root_slot"
                     and R'="\<lambda>thread_root. pspace_aligned' and pspace_distinct' and no_0_obj'"
                     in corres_split [OF _ getSlotCap_corres])
           apply (insert Q)
           apply (case_tac rv, simp_all add: isCap_simps Q[simplified])[1]
           apply (rename_tac arch_cap)
           apply (case_tac arch_cap, simp_all add: isCap_simps Q[simplified])[1]
           apply (rename_tac word option)
           apply (case_tac option, simp_all add: Q[simplified])[1]
           apply (clarsimp simp: cap_asid_def)
           apply (rule corres_guard_imp)
             apply (rule corres_split_catch [where f=lfr])
                 apply (rule P)
               apply (rule corres_split_eqrE [OF _ find_vspace_for_asid_corres])
                 apply (rule whenE_throwError_corres)
                   apply (simp add: lookup_failure_map_def)
                  apply simp
                 apply simp
apply (rule corres_split_norE)
apply (simp only: liftE_bindE)
apply (rule corres_split'[OF getCurrentCR3_corres])
apply (rule corres_whenE)
apply (clarsimp simp: cr3_relation_def)
apply (case_tac rv, case_tac rv', simp)
apply simp
apply (rule setCurrentCR3_corres[unfolded dc_def], simp add: cr3_relation_def)
apply (simp add: dc_def)
apply wpsimp+
apply (rule update_asid_map_corres)
apply wpsimp+
apply (wp find_vspace_for_asid_valids | simp | wp_once hoare_drop_imps)+
apply clarsimp
sorry (*
apply (rule corres_split_eqrE)
apply simp
apply (rule update_asid_map_corres)
apply
                 apply (rule x64_context_switch_corres)
                apply (wp | simp | wp_once hoare_drop_imps)+
               apply (simp add: whenE_def split del: if_split, wp)[1]
              apply (rule find_vspace_for_asid_vspace_at_asid_again)
             apply wp
            apply clarsimp
            apply (frule page_directory_cap_vspace_at_uniq, simp+)
            apply (frule(1) cte_wp_at_valid_objs_valid_cap)
            apply (clarsimp simp: valid_cap_def mask_def
                                  word_neq_0_conv)
            apply (drule(1) vspace_at_asid_unique2, simp)
           apply simp+
         apply (wp get_cap_wp | simp)+
     apply (clarsimp simp: tcb_at_cte_at_1 [simplified])
    apply simp
    done *)
qed

lemma get_asid_pool_corres_inv':
  "corres (\<lambda>p. (\<lambda>p'. p = p' o ucast) \<circ> inv ASIDPool)
          (asid_pool_at p) (pspace_aligned' and pspace_distinct')
          (get_asid_pool p) (getObject p)"
  apply (rule corres_rel_imp)
   apply (rule get_asid_pool_corres')
  apply simp
  done

(* FIXME x64: move *)
lemma no_fail_invalidateASID[wp]: "no_fail \<top> (invalidateASID a b)"
  by (simp add: invalidateASID_def)

(* FIXME x64: move *)
lemma no_fail_hwASIDInvalidate[wp]: "no_fail \<top> (hwASIDInvalidate a b)"
  by (simp add: hwASIDInvalidate_def no_fail_invalidateASID)

lemma dmo_vspace_at_uniq [wp]:
  "\<lbrace>vspace_at_uniq a pd\<rbrace> do_machine_op f \<lbrace>\<lambda>_. vspace_at_uniq a pd\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (simp add: vspace_at_uniq_def)
  done

lemma dMo_no_0_obj'[wp]:
  "\<lbrace>no_0_obj'\<rbrace> doMachineOp f \<lbrace>\<lambda>_. no_0_obj'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (simp add: no_0_obj'_def)

lemma invalidate_asid_entry_corres:
  "corres dc (valid_arch_objs and valid_asid_map
                and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0)
                and vspace_at_asid asid pm and valid_vs_lookup
                and unique_table_refs o caps_of_state
                and valid_global_objs and valid_arch_state
                and pspace_aligned and pspace_distinct)
             (pspace_aligned' and pspace_distinct' and no_0_obj')
             (invalidate_asid_entry asid pm) (invalidateASIDEntry asid pm)"
  apply (simp add: invalidate_asid_entry_def invalidateASIDEntry_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule invalidate_asid_corres[where pd=pm])
      apply (rule corres_machine_op)
      apply (rule corres_Id, rule refl, simp)
      apply wp
     apply (wp | clarsimp cong: if_cong)+
   apply (simp add: vspace_at_asid_uniq)
  apply simp
  done

crunch aligned'[wp]: invalidateASID' "pspace_aligned'"
crunch distinct'[wp]: invalidateASID' "pspace_distinct'"

lemma invalidateASID_cur' [wp]:
  "\<lbrace>cur_tcb'\<rbrace> invalidateASID' x \<lbrace>\<lambda>_. cur_tcb'\<rbrace>"
  by (simp add: invalidateASID'_def|wp)+

crunch aligned' [wp]: invalidateASIDEntry pspace_aligned'
crunch distinct' [wp]: invalidateASIDEntry pspace_distinct'
crunch cur' [wp]: invalidateASIDEntry cur_tcb'

lemma dMo_x64KSASIDTable_inv[wp]:
  "\<lbrace>\<lambda>s. P (x64KSASIDTable (ksArchState s))\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (x64KSASIDTable (ksArchState s))\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

lemma dMo_valid_arch_state'[wp]:
  "\<lbrace>\<lambda>s. P (valid_arch_state' s)\<rbrace> doMachineOp f \<lbrace>\<lambda>_ s. P (valid_arch_state' s)\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  by (clarsimp)

lemma invalidateASID_valid_arch_state [wp]:
  "\<lbrace>valid_arch_state'\<rbrace> invalidateASIDEntry x y \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  apply (simp add: invalidateASID'_def invalidateASIDEntry_def hwASIDInvalidate_def)
  apply (wpsimp simp: valid_arch_state'_def doMachineOp_def split_def)
  apply (clarsimp simp: is_inv_None_upd fun_upd_def[symmetric]
                        comp_upd_simp inj_on_fun_upd_elsewhere
                        valid_asid_map'_def)
  by (auto elim!: subset_inj_on dest!: ran_del_subset)[1]

crunch no_0_obj'[wp]: deleteASID "no_0_obj'"
  (ignore: getObject simp: crunch_simps
       wp: crunch_wps getObject_inv loadObject_default_inv)

(* FIXME x64: move *)
lemma set_asid_pool_asid_map_unmap:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (X64_A.ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow>
                ucast asid = x \<longrightarrow>
                x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                x64_asid_map (arch_state s) asid = None)\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  using set_asid_pool_restrict_asid_map[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

(* FIXME x64: move *)
lemma set_asid_pool_arch_objs_unmap_single:
  "\<lbrace>valid_arch_objs and ko_at (ArchObj (X64_A.ASIDPool ap)) p\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  using set_asid_pool_arch_objs_unmap[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

(* FIXME x64: move *)
lemma invalidate_asid_entry_valid_arch_state[wp]:
  "\<lbrace>valid_arch_state\<rbrace> invalidate_asid_entry asid pm \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (simp add: invalidate_asid_entry_def invalidate_asid_def)
  apply wp
   apply (simp add: do_machine_op_def split_def)
   apply wp
  by (clarsimp simp: valid_arch_state_def simp del: fun_upd_apply)

lemma valid_global_objs_asid_map_update_inv[simp]:
  "valid_global_objs s \<Longrightarrow> valid_global_objs (s\<lparr>arch_state := arch_state s \<lparr>x64_asid_map := b\<rparr>\<rparr>)"
  by (clarsimp simp: valid_global_objs_def)

crunch valid_global_objs[wp]: invalidate_asid_entry "valid_global_objs"


lemma delete_asid_corres:
  notes set_asid_pool_simpler_def[simp del]
  shows "corres dc
          (invs and valid_etcbs and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0))
          (pspace_aligned' and pspace_distinct' and no_0_obj'
              and valid_arch_state' and cur_tcb')
          (delete_asid asid pm) (deleteASID asid pm)"
  apply (simp add: delete_asid_def deleteASID_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split [OF _ corres_gets_asid])
      apply (case_tac "asid_table (asid_high_bits_of asid)", simp)
      apply clarsimp
      apply (rule_tac P="\<lambda>s. asid_high_bits_of asid \<in> dom (asidTable o ucast) \<longrightarrow>
                             asid_pool_at (the ((asidTable o ucast) (asid_high_bits_of asid))) s" and
                      P'="pspace_aligned' and pspace_distinct'" and
                      Q="invs and valid_etcbs and K (asid \<le> mask asid_bits \<and> asid \<noteq> 0) and
                         (\<lambda>s. x64_asid_table (arch_state s) = asidTable \<circ> ucast)" in
                      corres_split)
         prefer 2
         apply (simp add: dom_def)
         apply (rule get_asid_pool_corres_inv')
        apply (rule corres_when, simp add: mask_asid_low_bits_ucast_ucast)
apply (rule corres_split [OF _ invalidate_asid_entry_corres[where pm=pm]])
            apply (rule_tac P="asid_pool_at (the (asidTable (ucast (asid_high_bits_of asid))))
                               and valid_etcbs"
                        and P'="pspace_aligned' and pspace_distinct'"
                         in corres_split)
               prefer 2
               apply (simp del: fun_upd_apply)
               apply (rule set_asid_pool_corres')
               apply (simp add: inv_def mask_asid_low_bits_ucast_ucast)
               apply (rule ext)
               apply (clarsimp simp: o_def)
              apply (rule corres_split [OF _ gct_corres])
                apply simp
                apply (rule set_vm_root_corres)
               apply wp+
             apply (thin_tac "x = f o g" for x f g)
             apply (simp del: fun_upd_apply)
             apply (fold cur_tcb_def)
           apply (wp set_asid_pool_asid_map_unmap
                     set_asid_pool_vs_lookup_unmap'
                     set_asid_pool_arch_objs_unmap_single)+
          apply simp
            apply (fold cur_tcb'_def)
          apply (wp add: invalidate_asid_entry_invalidates | clarsimp simp: o_def)+
       apply (subgoal_tac "vspace_at_asid asid pm s")
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
      apply wp
      apply (simp add: o_def)
      apply (wp getASID_wp)
      apply clarsimp
      apply assumption
     apply wp+
   apply clarsimp
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                  dest!: invs_arch_state)
   apply blast
  apply (clarsimp simp: valid_arch_state'_def valid_asid_table'_def)
  done

lemma valid_arch_state_unmap_strg':
  "valid_arch_state' s \<longrightarrow>
   valid_arch_state' (s\<lparr>ksArchState :=
                        x64KSASIDTable_update (\<lambda>_. (x64KSASIDTable (ksArchState s))(ptr := None))
                         (ksArchState s)\<rparr>)"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def)
  apply (auto simp: ran_def split: if_split_asm)
  done

crunch x64KSASIDTable_inv[wp]: invalidateASIDEntry
    "\<lambda>s. P (x64KSASIDTable (ksArchState s))"

lemma delete_asid_pool_corres:
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
    apply (rule corres_split [OF _ corres_gets_asid])
      apply (rule corres_when)
       apply simp
      apply (simp add: liftM_def)
      apply (rule corres_split [OF _ get_asid_pool_corres'])
        apply (rule corres_split)
           prefer 2
           apply (rule corres_mapM [where r=dc and r'=dc], simp, simp)
               prefer 5
               apply (rule order_refl)

              apply (rule_tac P="invs and
                                 ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) ptr and
                                 [VSRef (ucast (asid_high_bits_of base)) None] \<rhd> ptr and
                                 K (is_aligned base asid_low_bits
                                      \<and> base \<le> mask asid_bits)"
                         and P'="pspace_aligned' and pspace_distinct' and no_0_obj'"
                              in corres_guard_imp)
                apply (rule corres_when)
                 apply (clarsimp simp: ucast_ucast_low_bits)
                apply (simp add: ucast_ucast_low_bits)
                apply (rule_tac pm="the (inv ASIDPool x xa)"
                               in invalidate_asid_entry_corres)
               apply (clarsimp simp: invs_def valid_state_def
                                     valid_arch_caps_def valid_pspace_def
                                     vspace_at_asid_def cong: conj_cong)
               apply (rule conjI)
                apply (clarsimp simp: mask_def asid_low_bits_word_bits
                               elim!: is_alignedE)
                apply (subgoal_tac "of_nat q < (2 ^ asid_high_bits :: machine_word)")
                 apply (subst mult.commute, rule word_add_offset_less)
                     apply assumption
                    apply assumption
                   apply (simp add: asid_bits_def word_bits_def)
                  apply (erule order_less_le_trans)
                  apply (simp add: word_bits_def asid_low_bits_def asid_high_bits_def)
                 apply (simp add: asid_bits_def asid_high_bits_def asid_low_bits_def)
                apply (drule word_power_less_diff)
                   apply (drule of_nat_mono_maybe[where 'a=machine_word_len, rotated])
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
                 apply (clarsimp simp: ucast_ucast_low_bits)
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
             prefer 2
             apply (rule corres_modify [where P=\<top> and P'=\<top>])
             apply (simp add: state_relation_def arch_state_relation_def)
             apply (rule ext)
             apply clarsimp
             apply (erule notE)
             apply (rule word_eqI)
             apply (drule_tac x1="ucast xa" in bang_eq [THEN iffD1])
             apply (erule_tac x=n in allE)
             apply (simp add: word_size nth_ucast)
            apply (rule corres_split)
               prefer 2
               apply (rule gct_corres)
              apply (simp only:)
              apply (rule set_vm_root_corres)
             apply wp+
         apply (rule_tac R="\<lambda>_ s. rv = x64_asid_table (arch_state s)"
                    in hoare_post_add)
         apply (drule sym, simp only: )
         apply (drule sym, simp only: )
         apply (thin_tac "P" for P)+
         apply (simp only: pred_conj_def cong: conj_cong)
         apply simp
         apply (fold cur_tcb_def)
         apply (strengthen valid_arch_state_unmap_strg
                           valid_arch_objs_unmap_strg
                           valid_asid_map_unmap
                           valid_vs_lookup_unmap_strg)
         apply (simp add: valid_global_objs_arch_update)
         apply (rule hoare_vcg_conj_lift,
                 (rule mapM_invalidate[where ptr=ptr, simplified])?,
                 ((wp mapM_wp' | simp)+)[1])+
        apply (rule_tac R="\<lambda>_ s. rv' = x64KSASIDTable (ksArchState s)"
                     in hoare_post_add)
        apply (simp only: pred_conj_def cong: conj_cong)
        apply simp
        apply (strengthen valid_arch_state_unmap_strg')
        apply (fold cur_tcb'_def)
        apply (wp mapM_wp')
       apply (clarsimp simp: cur_tcb'_def)
      apply (simp add: o_def pred_conj_def)
      apply wp
     apply (wp getASID_wp)+
   apply (clarsimp simp: conj_comms)
   apply (auto simp: vs_lookup_def intro: vs_asid_refsI)[1]
  apply clarsimp
  done

crunch typ_at' [wp]: findVSpaceForASID "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps loadObject_default_def ignore: getObject)

crunch typ_at' [wp]: setVMRoot "\<lambda>s. P (typ_at' T p s)"
  (simp: crunch_simps)

lemmas setVMRoot_typ_ats [wp] = typ_at_lifts [OF setVMRoot_typ_at']

lemma findVSpaceForASID_inv2:
  "\<lbrace>\<lambda>s. asid \<noteq> 0 \<and> asid \<le> mask asid_bits \<longrightarrow> P s\<rbrace> findVSpaceForASID asid \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases "asid \<noteq> 0 \<and> asid \<le> mask asid_bits")
   apply (simp add: findVSpaceForASID_inv)
  apply (simp add: findVSpaceForASID_def assertE_def asidRange_def mask_def)
  apply clarsimp
  done

crunch no_0_obj'[wp]: flushTable "no_0_obj'"
  (ignore: getObject wp: crunch_wps simp: crunch_simps loadObject_default_inv)

lemma flush_table_corres:
  "corres dc
          (pspace_aligned and valid_objs and valid_arch_state and
           cur_tcb and vspace_at_asid asid pm and valid_asid_map and valid_arch_objs and
           pspace_aligned and pspace_distinct and valid_vs_lookup and valid_global_objs
           and unique_table_refs o caps_of_state and
           K (is_aligned vptr pd_shift_bits \<and> asid \<le> mask asid_bits \<and> asid \<noteq> 0))
          (pspace_aligned' and pspace_distinct' and no_0_obj' and
           valid_arch_state' and cur_tcb')
          (flush_table pm vptr pt asid)
          (flushTable pm vptr pt asid)"
  apply (simp add: flush_table_def flushTable_def)
thm flush_table_def
  apply (rule corres_assume_pre)
  apply (simp add: bit_simps is_aligned_mask cong: corres_weak_cong)
  apply (thin_tac "P" for P)+
  apply (rule corres_guard_imp)
  sorry (* FIXME x64: this is very different on x64
        apply (clarsimp)
        apply (rule corres_when, rule refl)
        apply (rule corres_split[where r' = dc, OF corres_when corres_machine_op])
            apply simp
           apply (rule corres_split[OF _ gct_corres])
             apply (simp, rule set_vm_root_corres)
            apply ((wp mapM_wp' hoare_vcg_const_imp_lift get_pte_wp getPTE_wp|
                    wpc|simp|fold cur_tcb_def cur_tcb'_def)+)[4]
          apply (rule corres_Id[OF refl])
           apply simp
          apply (rule no_fail_invalidateTLB_ASID)
         apply (wp hoare_drop_imps | simp)+
       apply (wp load_hw_asid_wp hoare_drop_imps |
                simp add: cur_tcb'_def [symmetric] cur_tcb_def [symmetric])+
  done *)

crunch typ_at' [wp]: flushTable "\<lambda>s. P (typ_at' T p s)"
  (simp: assertE_def when_def wp: crunch_wps ignore: getObject)

lemmas flushTable_typ_ats' [wp] = typ_at_lifts [OF flushTable_typ_at']

lemmas findVSpaceForASID_typ_ats' [wp] = typ_at_lifts [OF findVSpaceForASID_typ_at']

crunch inv [wp]: findVSpaceForASID P
  (simp: assertE_def whenE_def loadObject_default_def
   wp: crunch_wps getObject_inv ignore: getObject)

crunch aligned'[wp]: unmapPageTable, unmapPageDirectory, unmapPDPT "pspace_aligned'"
  (ignore: getObject simp: crunch_simps
       wp: crunch_wps getObject_inv loadObject_default_inv)
crunch distinct'[wp]: unmapPageTable, unmapPageDirectory, unmapPDPT "pspace_distinct'"
  (ignore: getObject simp: crunch_simps
       wp: crunch_wps getObject_inv loadObject_default_inv)


crunch no_0_obj'[wp]: storePDE, storePTE, storePDPTE, storePML4E no_0_obj'

crunch valid_arch'[wp]: storePDE, storePTE, storePDPTE, storePML4E valid_arch_state'
(ignore: setObject)

crunch cur_tcb'[wp]: storePDE, storePTE, storePDPTE, storePML4E cur_tcb'
(ignore: setObject)

lemma getCurrentCR3_inv': "\<lbrace>P\<rbrace> getCurrentCR3 \<lbrace>\<lambda>_. P\<rbrace>"
  by (simp add: getCurrentCR3_def)

lemma invalidateLocalPageStructureCacheASID_corres:
  shows
  "corres dc \<top> \<top>
     (X64_A.invalidateLocalPageStructureCacheASID a b)
     (X64_H.invalidateLocalPageStructureCacheASID a b)"
  apply (simp add: X64_A.invalidateLocalPageStructureCacheASID_def
                   X64_H.invalidateLocalPageStructureCacheASID_def)
  by (corressimp corres: getCurrentCR3_corres setCurrentCR3_corres
                        wp: getCurrentCR3_inv getCurrentCR3_inv'
                      simp: cr3_relation_def)

lemmas invalidatePageStructureCacheASID_corres = invalidateLocalPageStructureCacheASID_corres
                      [folded invalidatePageStructureCacheASID_def]

(* FIXME x64: move *)
lemma flush_table_pde_at[wp]: "\<lbrace>pde_at p\<rbrace> flush_table a b c d \<lbrace>\<lambda>_. pde_at p\<rbrace>"
  by (wpsimp simp: flush_table_def pde_at_def wp: flush_table_typ_at mapM_x_wp')

crunch inv[wp]: lookupPTSlot "P"
  (wp: loadObject_default_inv)

lemma unmap_page_table_corres:
  notes liftE_get_pde_corres = get_pde_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and valid_etcbs and page_table_at pt and
           K (0 < asid \<and> is_aligned vptr pd_shift_bits \<and> vptr < pptr_base \<and> canonical_address vptr \<and> asid \<le> mask asid_bits))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_page_table asid vptr pt)
          (unmapPageTable asid vptr pt)"
  apply (clarsimp simp: unmapPageTable_def unmap_page_table_def ignoreFailure_def const_def cong: option.case_cong)
  apply (rule corres_guard_imp)
apply  (rule corres_split_catch, simp)
    apply (rule corres_split_eqrE [OF _ find_vspace_for_asid_corres'])
apply (rule corres_split_eqrE[OF _ lookup_pd_slot_corres])
apply (rule corres_splitEE[OF _ liftE_get_pde_corres])
apply (rule corres_splitEE[where r'=dc])
prefer 2
apply (case_tac "\<exists>addr x xa. pde = X64_A.PageTablePDE addr x xa")
apply (clarsimp split del: if_split)
apply (auto intro!: corres_returnOkTT simp: lookup_failure_map_def)[1]
apply (auto simp: pde_relation_def lookup_failure_map_def
           split: X64_A.pde.splits)[1]
apply simp
       apply (rule corres_split [OF _ flush_table_corres])
          apply (rule corres_split[OF _ store_pde_corres'])
apply (rule invalidatePageStructureCacheASID_corres)
apply (simp)
apply ((wpsimp wp: hoare_if get_pde_wp getPDE_wp)+)[8]
apply ((wpsimp wp: lookup_pd_slot_wp hoare_vcg_all_lift_R | wp_once hoare_drop_imps)+)[2]
apply (wpsimp wp: hoare_vcg_all_lift_R)+
sorry (*
apply (clarsimp simp: lookup_failure_map_def split del: if_split)
apply (wp get_pde_wp getPDE_wp)
apply_trace ((wp hoare_if | simp)+)[3]
apply_trace wp
apply (wp hoare_if)
apply simp
apply (wp hoare_if)
apply wpsimp
thm flush_table_typ_ats
             apply (rule flush_table_corres)
            apply (rule corres_Id, rule refl, simp)
            apply (wp no_fail_cleanByVA_PoU)+
           apply (simp, wp+)
         apply (simp add:pde_relation_aligned_def)+
        apply (wp store_pde_vspace_at_asid store_pde_arch_objs_invalid)
        apply (rule hoare_vcg_conj_lift)
         apply (simp add: store_pde_def)
         apply (wp set_pd_vs_lookup_unmap)+
      apply (rule corres_trivial, simp)
     apply (wp page_table_mapped_wp)
    apply (wp hoare_drop_imps)[1]
   apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_arch_caps_def word_gt_0)
   apply (frule (1) page_directory_pde_at_lookupI)
   apply (auto elim: simp: empty_table_def valid_pde_mappings_def pde_ref_def obj_at_def
                     vs_refs_pages_def graph_of_def split: if_splits)
  done *)

crunch aligned' [wp]: unmapPage pspace_aligned'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

crunch distinct' [wp]: unmapPage pspace_distinct'
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

lemma corres_split_strengthen_ftE:
  "\<lbrakk> corres (ftr \<oplus> r') P P' f j;
      \<And>rv rv'. r' rv rv' \<Longrightarrow> corres (ftr' \<oplus> r) (R rv) (R' rv') (g rv) (k rv');
      \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,-; \<lbrace>Q'\<rbrace> j \<lbrace>R'\<rbrace>,- \<rbrakk>
    \<Longrightarrow> corres (dc \<oplus> r) (P and Q) (P' and Q') (f >>=E (\<lambda>rv. g rv)) (j >>=E (\<lambda>rv'. k rv'))"
  apply (rule_tac r'=r' in corres_splitEE)
     apply (rule corres_rel_imp, assumption)
     apply (case_tac x, auto)[1]
    apply (erule corres_rel_imp)
    apply (case_tac x, auto)[1]
   apply (simp add: validE_R_def)+
  done

lemma check_mapping_corres:
  "page_entry_map m m' \<Longrightarrow> corres (dc \<oplus> dc) \<top> \<top>
      (unlessE (check_mapping_pptr pptr m) $ throwError ExceptionTypes_A.InvalidRoot)
      (checkMappingPPtr pptr m')"
  apply (simp add: liftE_bindE check_mapping_pptr_def
                   checkMappingPPtr_def)
  apply (cases m, simp_all add: liftE_bindE)
    apply (clarsimp simp: page_entry_map_def)
    apply (case_tac x1; auto simp: unlessE_def corres_returnOk)
   apply (clarsimp simp: page_entry_map_def)
   apply (case_tac x2; auto simp: unlessE_def corres_returnOk)
  apply (clarsimp simp: page_entry_map_def)
  apply (case_tac x3; auto simp: unlessE_def corres_returnOk)
  done

crunch inv[wp]: checkMappingPPtr "P"
  (wp: crunch_wps loadObject_default_inv simp: crunch_simps)

lemma store_pte_vspace_at_asid[wp]:
  "\<lbrace>vspace_at_asid asid pm\<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. vspace_at_asid asid pm\<rbrace>"
  apply (simp add: store_pte_def set_pd_def set_object_def update_object_def vspace_at_asid_def)
  apply (wp get_object_wp)
  apply clarsimp
  sorry

(* FIXME x64: move *)
lemma no_fail_invalidateTranslationSingleASID[wp]:
  "no_fail \<top> (invalidateTranslationSingleASID v a)"
  by (simp add: invalidateTranslationSingleASID_def)

lemmas liftE_get_pde_corres = get_pde_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
lemmas liftE_get_pte_corres = get_pte_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
lemmas liftE_get_pdpte_corres = get_pdpte_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]

(* Wrap up the standard usage pattern of wp/wpc/simp into its own command: *)
method wpsimp' uses wp wp_del simp simp_del split split_del cong =
  ((determ \<open>wp add: wp del: wp_del |wpc|clarsimp simp add: simp simp del: simp_del split: split split del: split_del cong: cong\<close>)+)[1]

lemma unmap_page_corres:
  "corres dc (invs and valid_etcbs and
              K (valid_unmap sz (asid,vptr) \<and> vptr < pptr_base \<and> asid \<le> mask asid_bits \<and> canonical_address vptr))
             (valid_objs' and valid_arch_state' and pspace_aligned' and
              pspace_distinct' and no_0_obj' and cur_tcb')
             (unmap_page sz asid vptr pptr)
             (unmapPage sz asid vptr pptr)"
  apply (clarsimp simp: unmap_page_def unmapPage_def ignoreFailure_def const_def)
thm unmap_page_def
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch [where E="\<lambda>_. \<top>" and E'="\<lambda>_. \<top>"], simp)
      apply (rule corres_split_strengthen_ftE[where ftr'=dc],
             rule find_vspace_for_asid_corres)
        apply (rule corres_splitEE)
           apply clarsimp
           apply (rule corres_machine_op, rule corres_Id, rule refl, simp)
           apply (rule no_fail_invalidateTranslationSingleASID)
          apply (rule_tac F = "vptr < pptr_base" in corres_gen_asm)
          apply (rule_tac P="\<exists>\<rhd> vspace and page_map_l4_at vspace and vspace_at_asid asid vspace
                             and (\<exists>\<rhd> vspace)
                             and valid_arch_state and valid_arch_objs
                             and equal_kernel_mappings
                             and pspace_aligned and valid_global_objs and valid_etcbs and
                             K (valid_unmap sz (asid,vptr) \<and> canonical_address vptr )" and
                          P'="pspace_aligned' and pspace_distinct'" in corres_inst)
          apply clarsimp
          apply (rename_tac vspace)
          apply (cases sz, simp_all)[1]
             apply (rule corres_guard_imp)
               apply (rule_tac F = "vptr < pptr_base" in corres_gen_asm)
               apply (rule corres_split_strengthen_ftE[OF lookup_pt_slot_corres])
                 apply simp
                 apply (rule corres_splitEE[OF _ liftE_get_pte_corres])
                   apply simp
                   apply (rule corres_split_norE[OF _ check_mapping_corres, where r=dc, simplified])
                   apply simp
                   apply (rule store_pte_corres')
                   apply (((wpsimp' wp: hoare_vcg_all_lift_R get_pte_wp getPTE_wp lookup_pt_slot_wp
                                  simp: page_entry_map_def unlessE_def is_aligned_pml4
                             split_del: if_split
                              simp_del: dc_simp)+
                           | wp_once hoare_drop_imps)+)[10]
         apply (rule corres_guard_imp)
           apply (rule corres_split_strengthen_ftE[OF lookup_pd_slot_corres])
             apply (simp del: dc_simp)
             apply (rule corres_splitEE[OF _ liftE_get_pde_corres])
               apply (rule corres_split_norE[OF _ check_mapping_corres, where r=dc, simplified])
                  apply simp
                  apply (rule store_pde_corres')
                  apply (((wpsimp' wp: hoare_vcg_all_lift_R get_pde_wp getPDE_wp lookup_pd_slot_wp
                                 simp: page_entry_map_def unlessE_def is_aligned_pml4
                            split_del: if_split
                             simp_del: dc_simp)+
                         | wp_once hoare_drop_imps)+)[10]
        apply (rule corres_guard_imp)
          apply (rule corres_split_strengthen_ftE[OF lookup_pdpt_slot_corres])
            apply (simp del: dc_simp)
            apply (rule corres_splitEE[OF _ liftE_get_pdpte_corres])
              apply (rule corres_split_norE[OF _ check_mapping_corres, where r=dc, simplified])
                 apply simp
                 apply (rule store_pdpte_corres')
                 apply (((wpsimp' wp: hoare_vcg_all_lift_R get_pdpte_wp getPDPTE_wp
                                      lookup_pdpt_slot_wp
                                simp: page_entry_map_def unlessE_def is_aligned_pml4
                           split_del: if_split
                            simp_del: dc_simp)+
                         | wp_once hoare_drop_imps)+)
   apply (rule conjI[OF disjI1], clarsimp)
   apply (clarsimp simp: invs_arch_objs invs_psp_aligned valid_unmap_def invs_arch_state
                         invs_equal_kernel_mappings)
  apply (clarsimp)
  done

definition
  "page_directory_invocation_map pdi pdi' \<equiv> case pdi of
   X64_A.PageDirectoryMap cap cte pdpte pdpt_slot pml4  \<Rightarrow>
      \<exists>cap' pdpte'. pdi' = PageDirectoryMap cap' (cte_map cte) pdpte' pdpt_slot pml4
            \<and> cap_relation cap cap' \<and> pdpte_relation' pdpte pdpte'
 | X64_A.PageDirectoryUnmap cap ptr \<Rightarrow>
      \<exists>cap'. pdi' = PageDirectoryUnmap cap' (cte_map ptr) \<and> cap_relation cap (ArchObjectCap cap')"

definition
  "page_invocation_map pgi pgi' \<equiv> case pgi of
    X64_A.PageMap c slot m vs \<Rightarrow>
      \<exists>c' m'. pgi' = PageMap c' (cte_map slot) m' vs \<and>
              cap_relation c c' \<and>
              mapping_map m m'
  | X64_A.PageRemap m a vs \<Rightarrow>
      \<exists>m'. pgi' = PageRemap m' a vs \<and> mapping_map m m'
  | X64_A.PageUnmap c ptr \<Rightarrow>
      \<exists>c'. pgi' = PageUnmap c' (cte_map ptr) \<and>
         acap_relation c c'
  | X64_A.PageGetAddr ptr \<Rightarrow>
      pgi' = PageGetAddr ptr"

lemma tl_nat_list_simp:
 "tl [a..<b] = [a + 1 ..<b]"
  by (induct b,auto)

definition
  "valid_page_inv' pgi \<equiv> case pgi of
    PageMap cap ptr m vs \<Rightarrow>
      cte_wp_at' (is_arch_update' cap) ptr and valid_slots' m and valid_cap' cap
      and K (page_entry_map_corres m)
  | PageRemap m asid vs \<Rightarrow> valid_slots' m and K (page_entry_map_corres m)
  | PageUnmap cap ptr \<Rightarrow>
      \<lambda>s. \<exists>r mt R sz d m. cap = PageCap r R mt sz d m \<and>
          cte_wp_at' (is_arch_update' (ArchObjectCap cap)) ptr s \<and>
          s \<turnstile>' (ArchObjectCap cap)
  | PageGetAddr ptr \<Rightarrow> \<top>"

crunch ctes [wp]: unmapPage "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

lemma updateCap_valid_slots'[wp]:
  "\<lbrace>valid_slots' x2\<rbrace> updateCap cte cte' \<lbrace>\<lambda>_ s. valid_slots' x2 s \<rbrace>"
  apply (case_tac x2, case_tac a)
    by (wpsimp simp: valid_slots'_def wp: hoare_vcg_ball_lift)+


crunch unique_table_refs[wp]: do_machine_op, store_pte, store_pde, store_pdpte "\<lambda>s. (unique_table_refs (caps_of_state s))"

lemma set_cap_vspace_at_asid [wp]:
  "\<lbrace>vspace_at_asid asid pd\<rbrace> set_cap t st \<lbrace>\<lambda>rv. vspace_at_asid asid pd\<rbrace>"
  apply (simp add: vspace_at_asid_def)
  apply wp
  done

lemma set_cap_valid_slots_inv[wp]:
  "\<lbrace>valid_slots m\<rbrace> set_cap t st \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  apply (cases m; simp)
  apply (case_tac a; simp)
    by  (clarsimp simp: valid_slots_def, wp hoare_vcg_ball_lift set_cap.vs_lookup set_cap_typ_ats)+

lemma set_cap_same_refs_inv[wp]:
  "\<lbrace>\<lambda>s. same_refs m cap s\<rbrace> set_cap t st \<lbrace>\<lambda>rv s. same_refs m cap s\<rbrace>"
  by (cases m, (clarsimp simp: same_refs_def, wp)+)

definition
  "valid_page_map_inv cap ptr m vs \<equiv> (\<lambda>s. caps_of_state s ptr = Some cap) and same_refs m cap and
  valid_slots m and
  valid_cap cap and
  K (is_pg_cap cap \<and> empty_refs m) and
  (\<lambda>s. \<exists>sl. cte_wp_at (parent_for_refs m) sl s)"

lemma set_cap_valid_page_map_inv:
  "\<lbrace>valid_page_inv (X64_A.page_invocation.PageMap cap slot m vs)\<rbrace> set_cap cap slot \<lbrace>\<lambda>rv. valid_page_map_inv cap slot m vs\<rbrace>"
  apply (simp add: valid_page_inv_def valid_page_map_inv_def)
  apply (wp set_cap_cte_wp_at_cases hoare_vcg_ex_lift| simp)+
  apply clarsimp
  apply (rule conjI, fastforce simp: cte_wp_at_def)
  apply (rule_tac x=a in exI, rule_tac x=b in exI)
  apply (subgoal_tac "(a,b) \<noteq> slot")
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_def parent_for_refs_def)
  apply (auto simp: is_pt_cap_def is_pg_cap_def is_pd_cap_def is_pdpt_cap_def split: vm_page_entry.splits)
  done

lemma message_info_to_data_eqv:
  "wordFromMessageInfo (message_info_map mi) = message_info_to_data mi"
  apply (cases mi)
  apply (simp add: wordFromMessageInfo_def
    msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def
    shiftL_nat)
  done

lemma message_info_from_data_eqv:
  "message_info_map (data_to_message_info rv) = messageInfoFromWord rv"
  apply (auto simp add: data_to_message_info_def messageInfoFromWord_def
    msgLengthBits_def msgExtraCapBits_def msgMaxExtraCaps_def
    shiftL_nat Let_def not_less msgMaxLength_def)
  done

lemma set_mi_corres:
 "mi' = message_info_map mi \<Longrightarrow>
  corres dc (tcb_at t) (tcb_at' t)
         (set_message_info t mi) (setMessageInfo t mi')"
  apply (simp add: setMessageInfo_def set_message_info_def)
  apply (subgoal_tac "wordFromMessageInfo (message_info_map mi) =
                      message_info_to_data mi")
   apply (simp add: user_setreg_corres msg_info_register_def
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

lemma perform_page_corres:
  assumes "page_invocation_map pgi pgi'"
  notes mapping_map_simps = mapping_map_def page_entry_map_def attr_mask_def attr_mask'_def page_entry_ptr_map_def
  shows "corres dc (invs and valid_etcbs and valid_page_inv pgi)
            (invs' and valid_page_inv' pgi')
            (perform_page_invocation pgi) (performPageInvocation pgi')"
proof -
  have pull_out_P:
    "\<And>P s Q c p. P s \<and> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> Q s c) \<longrightarrow> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> P s \<and> Q s c)"
   by blast
  show ?thesis
  using assms
  apply (cases pgi)
       apply (rename_tac cap prod entry vspace)
       apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def
                             page_invocation_map_def)
       apply (rule corres_guard_imp)
         apply (rule_tac R="\<lambda>_. invs and (valid_page_map_inv cap (a,b) (aa,ba) vspace) and valid_etcbs and (\<lambda>s. caps_of_state s (a,b) = Some cap)"
           and R'="\<lambda>_. invs' and valid_slots' (ab,bb) and pspace_aligned'
           and pspace_distinct' and K (page_entry_map_corres (ab,bb))" in corres_split)
            prefer 2
            apply (erule updateCap_same_master)
           apply (simp, rule corres_gen_asm2)
           apply (case_tac aa)
             apply clarsimp
             apply (frule (1) mapping_map_pte, clarsimp)
             apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def neq_Nil_conv valid_page_map_inv_def)
            apply (rule corres_name_pre)
           apply (clarsimp simp:mapM_Cons bind_assoc split del: if_split)
           apply (rule corres_guard_imp)
             apply (rule corres_split[OF _ store_pte_corres'])
                apply (rule corres_split[where r'="op ="])
                   apply simp
                   apply (rule invalidateLocalPageStructureCacheASID_corres)
                  apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                  apply (case_tac m; clarsimp)
                  apply (rule corres_fail)
                  apply (simp add: same_refs_def)
                 apply (wpsimp simp: invs_psp_aligned)+
          apply (frule (1) mapping_map_pde, clarsimp)
          apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def neq_Nil_conv valid_page_map_inv_def)
          apply (rule corres_name_pre)
          apply (clarsimp simp:mapM_Cons bind_assoc split del: if_split)
          apply (rule corres_guard_imp)
            apply (rule corres_split[OF _ store_pde_corres'])
               apply (rule corres_split[where r'="op ="])
                  apply simp
                  apply (rule invalidateLocalPageStructureCacheASID_corres)
                 apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                 apply (case_tac m; clarsimp)
                 apply (rule corres_fail)
                 apply (simp add: same_refs_def)
                apply (wpsimp simp: invs_psp_aligned)+
         apply (frule (1) mapping_map_pdpte, clarsimp)
         apply (clarsimp simp: mapping_map_simps valid_slots'_def valid_slots_def valid_page_inv_def neq_Nil_conv valid_page_map_inv_def)
         apply (rule corres_name_pre)
         apply (clarsimp simp:mapM_Cons bind_assoc split del: if_split)
         apply (rule corres_guard_imp)
                apply (rule corres_split[OF _ store_pdpte_corres'])
              apply (rule corres_split[where r'="op ="])
                 apply simp
                 apply (rule invalidateLocalPageStructureCacheASID_corres)
                apply (case_tac cap; clarsimp simp add: is_pg_cap_def)
                apply (case_tac m; clarsimp)
                apply (rule corres_fail)
                apply (simp add: same_refs_def)
               apply (wpsimp simp: invs_psp_aligned)+
        apply (wp_trace arch_update_cap_invs_map set_cap_valid_page_map_inv)
       apply (wp arch_update_updateCap_invs)
      apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct valid_page_inv_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps)
     apply (simp add: cap_master_cap_def split: cap.splits arch_cap.splits)
     apply (auto simp: cte_wp_at_ctes_of valid_page_inv'_def)[1]
       -- "PageRemap"
      apply (rename_tac asid vspace)
      apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def
      page_invocation_map_def)
    apply (rule corres_name_pre)
    apply (clarsimp simp: mapM_Cons mapM_x_mapM bind_assoc valid_slots_def valid_page_inv_def
                          neq_Nil_conv valid_page_inv'_def split del: if_split)
    apply (case_tac a; simp)
      apply (frule (1) mapping_map_pte, clarsimp)
      apply (clarsimp simp: mapping_map_simps)
      apply (rule corres_guard_imp)
        apply (rule corres_split[OF _ store_pte_corres'])
           apply (rule invalidateLocalPageStructureCacheASID_corres)
          apply (wpsimp simp: invs_pspace_aligned')+
     apply (frule (1) mapping_map_pde, clarsimp)
     apply (clarsimp simp: mapping_map_simps)
     apply (rule corres_guard_imp)
       apply (rule corres_split[OF _ store_pde_corres'])
          apply (rule invalidateLocalPageStructureCacheASID_corres)
         apply (wpsimp simp: invs_pspace_aligned')+
    apply (frule (1) mapping_map_pdpte, clarsimp)
    apply (clarsimp simp: mapping_map_simps)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF _ store_pdpte_corres'])
         apply (rule invalidateLocalPageStructureCacheASID_corres)
        apply (wpsimp simp: invs_pspace_aligned')+
     -- "PageUnmap"
   apply (clarsimp simp: performPageInvocation_def perform_page_invocation_def
                         page_invocation_map_def)
   apply (rule corres_assume_pre)
   apply (clarsimp simp: valid_page_inv_def valid_page_inv'_def isCap_simps is_page_cap_def cong: option.case_cong prod.case_cong)
   apply (case_tac m)
    apply simp
    apply (rule corres_guard_imp)
      apply (rule corres_split [where r'="acap_relation"])
         prefer 2
         apply simp
         apply (rule corres_rel_imp)
          apply (rule get_cap_corres_all_rights_P[where P=is_arch_cap], rule refl)
         apply (clarsimp simp: is_cap_simps)
        apply (rule_tac F="is_page_cap cap" in corres_gen_asm)
        apply (rule updateCap_same_master)
        apply (clarsimp simp: is_page_cap_def update_map_data_def)
       apply (wp get_cap_wp getSlotCap_wp)+
     apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_diminished_def)
     apply (drule (2) diminished_is_update')+
     apply (clarsimp simp: cap_rights_update_def acap_rights_update_def update_map_data_def is_cap_simps)
     apply auto[1]
    apply (auto simp: cte_wp_at_ctes_of)[1]
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        prefer 2
        apply (rule unmap_page_corres)
       apply (rule corres_split [where r'=acap_relation])
          prefer 2
          apply simp
          apply (rule corres_rel_imp)
           apply (rule get_cap_corres_all_rights_P[where P=is_arch_cap], rule refl)
          apply (clarsimp simp: is_cap_simps)
         apply (rule_tac F="is_page_cap cap" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_page_cap_def update_map_data_def)
        apply (wp get_cap_wp getSlotCap_wp)+
      apply (simp add: cte_wp_at_caps_of_state)
      apply (strengthen pull_out_P)+
      apply wp
     apply (simp add: cte_wp_at_ctes_of)
     apply wp
    apply (clarsimp simp: valid_unmap_def cte_wp_at_caps_of_state)
    apply (clarsimp simp: is_arch_diminished_def is_cap_simps split: cap.splits arch_cap.splits)
    apply (drule (2) diminished_is_update')+
    apply (clarsimp simp: cap_rights_update_def is_page_cap_def cap_master_cap_simps update_map_data_def acap_rights_update_def)
    apply (clarsimp simp add: valid_cap_def mask_def)
    apply auto[1]
   apply (auto simp: cte_wp_at_ctes_of)[1]
    -- "PageGetAddr"
  apply (clarsimp simp: perform_page_invocation_def performPageInvocation_def page_invocation_map_def fromPAddr_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF _ gct_corres])
      apply simp
      apply (rule corres_split[OF set_mi_corres set_mrs_corres])
         apply (simp add: message_info_map_def)
        apply clarsimp
       apply (wp)+
   apply (clarsimp simp: tcb_at_invs)
  apply (clarsimp simp: tcb_at_invs')
  done
qed

definition
  "page_table_invocation_map pti pti' \<equiv> case pti of
     X64_A.PageTableMap cap ptr pde pd_slot vspace \<Rightarrow>
    \<exists>cap' pde'. pti' = PageTableMap cap' (cte_map ptr) pde' pd_slot vspace \<and>
                cap_relation cap cap' \<and>
                pde_relation' pde pde'
   | X64_A.PageTableUnmap cap ptr \<Rightarrow>
    \<exists>cap'. pti' = PageTableUnmap cap' (cte_map ptr) \<and>
           cap_relation cap (ArchObjectCap cap')"

definition
  "valid_pti' pti \<equiv> case pti of
     PageTableMap cap slot pde pdeSlot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pde' pde and K (case cap of ArchObjectCap (PageTableCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PageTableUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPageTableCap cap)"

lemma clear_page_table_corres:
  "corres dc (pspace_aligned and page_table_at p and valid_etcbs)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pte X64_A.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])
    (mapM_x (swp storePTE X64_H.InvalidPTE)
       [p , p + 8 .e. p + 2 ^ ptBits - 1])"
  apply (rule_tac F="is_aligned p ptBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="op ="
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pte_at x s \<and> pspace_aligned s \<and> valid_etcbs s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule store_pte_corres')
        apply (simp add:pte_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule page_table_pte_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

lemma clear_page_directory_corres:
  "corres dc (pspace_aligned and page_directory_at p and valid_etcbs)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pde X64_A.InvalidPDE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])
    (mapM_x (swp storePDE X64_H.InvalidPDE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])"
  apply (rule_tac F="is_aligned p pdBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="op ="
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pde_at x s \<and> pspace_aligned s \<and> valid_etcbs s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule store_pde_corres')
        apply (simp add:pde_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule page_directory_pde_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

lemma clear_pdpt_corres:
  "corres dc (pspace_aligned and pd_pointer_table_at p and valid_etcbs)
             (pspace_aligned' and pspace_distinct')
    (mapM_x (swp store_pdpte X64_A.InvalidPDPTE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])
    (mapM_x (swp storePDPTE X64_H.InvalidPDPTE)
       [p , p + 8 .e. p + 2 ^ pdBits - 1])"
  apply (rule_tac F="is_aligned p pdptBits" in corres_req)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm if_split_asm
                          arch_kernel_obj.split_asm)
   apply (drule(1) pspace_alignedD)
   apply (simp add: bit_simps)
  apply (simp add: upto_enum_step_subtract[where x=p and y="p + 8"]
                   is_aligned_no_overflow bit_simps
                   upto_enum_step_red[where us=3, simplified]
                   mapM_x_mapM liftM_def[symmetric])
  apply (rule corres_guard_imp,
         rule_tac r'=dc and S="op ="
               and Q="\<lambda>xs s. \<forall>x \<in> set xs. pdpte_at x s \<and> pspace_aligned s \<and> valid_etcbs s"
               and Q'="\<lambda>xs. pspace_aligned' and pspace_distinct'"
                in corres_mapM_list_all2, simp_all)
      apply (rule corres_guard_imp, rule store_pdpte_corres')
        apply (simp add:pde_relation_def)+
     apply (wp hoare_vcg_const_Ball_lift | simp)+
   apply (simp add: list_all2_refl)
  apply (clarsimp simp: upto_enum_step_def)
  apply (erule pd_pointer_table_pdpte_atI[simplified shiftl_t2n mult.commute bit_simps, simplified])
   apply (simp add: bit_simps word_less_nat_alt word_le_nat_alt unat_of_nat)
  apply simp
  done

crunch typ_at'[wp]: invalidatePageStructureCacheASID, unmapPageTable, unmapPageDirectory, unmapPDPT "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps hoare_vcg_all_lift_R ignore: getObject)

lemmas unmapPageTable_typ_ats[wp] = typ_at_lifts[OF unmapPageTable_typ_at']
lemmas unmapPageDirectory_typ_ats[wp] = typ_at_lifts[OF unmapPageDirectory_typ_at']
lemmas unmapPDPT_typ_ats[wp] = typ_at_lifts[OF unmapPDPT_typ_at']

lemma perform_page_table_corres:
  "page_table_invocation_map pti pti' \<Longrightarrow>
   corres dc
          (invs and valid_etcbs and valid_pti pti)
          (invs' and valid_pti' pti')
          (perform_page_table_invocation pti)
          (performPageTableInvocation pti')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_page_table_invocation_def performPageTableInvocation_def)
  apply (cases pti)
   apply (rename_tac cap slot pde pd_slot vspace)
   apply (clarsimp simp: page_table_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pti_def valid_pti'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split [OF _ updateCap_same_master])
        prefer 2
        apply assumption
       apply (rule corres_split [OF _ store_pde_corres'])
          apply (rule corres_split[where r'="op =" and P="\<top>" and P'="\<top>"])
             apply simp
             apply (rule invalidatePageStructureCacheASID_corres)
            apply (case_tac cap; clarsimp simp add: is_pt_cap_def)
            apply (case_tac asid; clarsimp)
           apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
  subgoal sorry (* FIXME x64: this will be solved by adding "pde_at pd_slot" to valid_pti *)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pti'_def)
   apply auto[1]
  apply (clarsimp simp: split:X64_H.pde.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: page_table_invocation_map_def)
  apply (rule_tac F="is_pt_cap cap" in corres_req)
   apply (clarsimp simp: valid_pti_def)
  apply (clarsimp simp: is_pt_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (simp add: liftM_def)
       apply (rule corres_split [OF _ get_cap_corres])
         apply (rule_tac F="is_pt_cap x" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_pt_cap_def update_map_data_def)
        apply (wp get_cap_wp)+
      apply (rule corres_if[OF refl])
       apply (rule corres_split [OF _ unmap_page_table_corres])
         apply (rule clear_page_table_corres[simplified bit_simps bitSimps, simplified])
        apply wp+
      apply (rule corres_trivial, simp)
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply_trace ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state
                         is_arch_diminished_def
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (frule (2) diminished_is_update')
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
              split: option.split_asm)[1]
   apply (auto simp: valid_pti'_def cte_wp_at_ctes_of bit_simps)
  done

definition
  "valid_pdi' pdi \<equiv> case pdi of
     PageDirectoryMap cap slot pdpte pdptSlot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pdpte' pdpte and K (case cap of ArchObjectCap (PageDirectoryCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PageDirectoryUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPageTableCap cap)"

lemma unmap_pd_corres:
  notes liftE_get_pdpte_corres = get_pdpte_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and valid_etcbs and page_directory_at pd and
           K (0 < asid \<and> is_aligned vptr pdpt_shift_bits \<and> vptr < pptr_base \<and> canonical_address vptr \<and> asid \<le> mask asid_bits))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_pd asid vptr pd)
          (unmapPageDirectory asid vptr pd)"
  sorry (* copy proof from unmap_page_table_corres *)

crunch valid_objs[wp]: unmap_pd, unmap_pdpt "valid_objs"
crunch pspace_aligned[wp]: unmap_pd, unmap_pdpt "pspace_aligned"
crunch pspace_distinct[wp]: unmap_pd, unmap_pdpt "pspace_distinct"

lemma perform_page_directory_corres:
  "page_directory_invocation_map pdi pdi' \<Longrightarrow>
   corres dc
          (invs and valid_etcbs and valid_pdi pdi)
          (invs' and valid_pdi' pdi')
          (perform_page_directory_invocation pdi)
          (performPageDirectoryInvocation pdi')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_page_directory_invocation_def performPageDirectoryInvocation_def)
  apply (cases pdi)
   apply (rename_tac cap slot pdpte pdpt_slot vspace)
   apply (clarsimp simp: page_directory_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pdi_def valid_pdi'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split [OF _ updateCap_same_master])
        prefer 2
        apply assumption
       apply (rule corres_split [OF _ store_pdpte_corres'])
          apply (rule corres_split[where r'="op =" and P="\<top>" and P'="\<top>"])
             apply simp
             apply (rule invalidatePageStructureCacheASID_corres)
            apply (case_tac cap; clarsimp simp add: is_pd_cap_def)
            apply (case_tac asid; clarsimp)
           apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
  subgoal sorry (* FIXME x64: this will be solved by adding "pdpte_at pdpt_slot" to valid_pdi *)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pdi'_def)
   apply auto[1]
  apply (clarsimp split:X64_H.pdpte.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: page_directory_invocation_map_def)
  apply (rule_tac F="is_pd_cap cap" in corres_req)
   apply (clarsimp simp: valid_pdi_def)
  apply (clarsimp simp: is_pd_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (simp add: liftM_def)
       apply (rule corres_split [OF _ get_cap_corres])
         apply (rule_tac F="is_pd_cap x" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_pd_cap_def update_map_data_def)
        apply (wp get_cap_wp)+
      apply (rule corres_if[OF refl])
       apply (rule corres_split [OF _ unmap_pd_corres])
         apply (rule clear_page_directory_corres[simplified bit_simps bitSimps, simplified])
        apply wp+
      apply (rule corres_trivial, simp)
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pdi_def cte_wp_at_caps_of_state
                         is_arch_diminished_def
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (frule (2) diminished_is_update')
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
                     wellformed_mapdata_def vmsz_aligned_def
              split: option.split_asm)[1]
   apply (auto simp: valid_pdi'_def cte_wp_at_ctes_of bit_simps)
  done

definition
  "valid_pdpti' pdi \<equiv> case pdi of
     PDPTMap cap slot pml4e pml4Slot vspace \<Rightarrow>
     cte_wp_at' (is_arch_update' cap) slot and
     valid_cap' cap and
     valid_pml4e' pml4e and K (case cap of ArchObjectCap (PDPointerTableCap _ (Some (asid, vs))) \<Rightarrow> True | _ \<Rightarrow> False)
   | PDPTUnmap cap slot \<Rightarrow> cte_wp_at' (is_arch_update' (ArchObjectCap cap)) slot
                                 and valid_cap' (ArchObjectCap cap)
                                 and K (isPageTableCap cap)"

lemma unmap_pdpt_corres:
  notes liftE_get_pml4e_corres = get_pml4e_corres'[THEN corres_liftE_rel_sum[THEN iffD2]]
  shows "corres dc
          (invs and valid_etcbs and pd_pointer_table_at pd and
           K (0 < asid \<and> is_aligned vptr pml4_shift_bits \<and> vptr < pptr_base \<and> canonical_address vptr \<and> asid \<le> mask asid_bits))
          (valid_arch_state' and pspace_aligned' and pspace_distinct'
            and no_0_obj' and cur_tcb' and valid_objs')
          (unmap_pdpt asid vptr pd)
          (unmapPDPT asid vptr pd)"
  sorry (* copy proof from unmap_page_table_corres *)

definition
  "pdpt_invocation_map pdpti pdpti' \<equiv> case pdpti of
   X64_A.PDPTMap cap cte pml4e pml4_slot vspace  \<Rightarrow>
      \<exists>cap' pml4e'. pdpti' = PDPTMap cap' (cte_map cte) pml4e' pml4_slot vspace
            \<and> cap_relation cap cap' \<and> pml4e_relation' pml4e pml4e'
 | X64_A.PDPTUnmap cap ptr \<Rightarrow>
      \<exists>cap'. pdpti' = PDPTUnmap cap' (cte_map ptr) \<and> cap_relation cap (ArchObjectCap cap')"

lemma perform_pdpt_corres:
  "pdpt_invocation_map pdpti pdpti' \<Longrightarrow>
   corres dc
          (invs and valid_etcbs and valid_pdpti pdpti)
          (invs' and valid_pdpti' pdpti')
          (perform_pdpt_invocation pdpti)
          (performPDPTInvocation pdpti')"
  (is "?mp \<Longrightarrow> corres dc ?P ?P' ?f ?g")
  apply (simp add: perform_pdpt_invocation_def performPDPTInvocation_def)
  apply (cases pdpti)
   apply (rename_tac cap slot pml4e pml4_slot vspace)
   apply (clarsimp simp: pdpt_invocation_map_def)
   apply (rule corres_name_pre)
   apply (clarsimp simp: valid_pdpti_def valid_pdpti'_def split: capability.split_asm arch_capability.split_asm)
   apply (rule corres_guard_imp)
     apply (rule corres_split [OF _ updateCap_same_master])
        prefer 2
        apply assumption
       apply (rule corres_split [OF _ store_pml4e_corres'])
          apply (rule corres_split[where r'="op =" and P="\<top>" and P'="\<top>"])
             apply simp
             apply (rule invalidatePageStructureCacheASID_corres)
            apply (case_tac cap; clarsimp simp add: is_pdpt_cap_def)
            apply (case_tac asid; clarsimp)
           apply (wpsimp wp: set_cap_typ_at)+
    apply (clarsimp simp: invs_valid_objs invs_psp_aligned invs_distinct is_arch_update_def
                          cte_wp_at_caps_of_state )
    apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                   dest!: cap_master_cap_eqDs)
  subgoal sorry (* FIXME x64: this will be solved by adding "pml4e_at pml4_slot" to valid_pdpti *)
   apply (clarsimp simp: cte_wp_at_ctes_of valid_pdpti'_def)
   apply auto[1]
  apply (clarsimp split:X64_H.pml4e.split)
  apply (rename_tac cap a b)
  apply (clarsimp simp: pdpt_invocation_map_def)
  apply (rule_tac F="is_pdpt_cap cap" in corres_req)
   apply (clarsimp simp: valid_pdpti_def)
  apply (clarsimp simp: is_pdpt_cap_def split_def
                        bit_simps objBits_simps archObjSize_def
                  cong: option.case_cong)
  apply (simp add: case_option_If2 getSlotCap_def split del: if_split)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (simp add: liftM_def)
       apply (rule corres_split [OF _ get_cap_corres])
         apply (rule_tac F="is_pdpt_cap x" in corres_gen_asm)
         apply (rule updateCap_same_master)
         apply (clarsimp simp: is_pdpt_cap_def update_map_data_def)
        apply (wp get_cap_wp)+
      apply (rule corres_if[OF refl])
       apply (rule corres_split [OF _ unmap_pdpt_corres])
         apply (rule clear_pdpt_corres[simplified bit_simps bitSimps, simplified])
        apply wp+
      apply (rule corres_trivial, simp)
     apply (simp add: cte_wp_at_caps_of_state pred_conj_def
           split del: if_split)
     apply (rule hoare_lift_Pf2[where f=caps_of_state])
      apply ((wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                mapM_x_wp' | simp split del: if_split)+)
   apply (clarsimp simp: valid_pdpti_def cte_wp_at_caps_of_state
                         is_arch_diminished_def
                         cap_master_cap_simps
                         update_map_data_def is_cap_simps
                         cap_rights_update_def acap_rights_update_def
                  dest!: cap_master_cap_eqDs)
   apply (frule (2) diminished_is_update')
   apply (auto simp: valid_cap_def mask_def cap_master_cap_def
                     cap_rights_update_def acap_rights_update_def
                     wellformed_mapdata_def vmsz_aligned_def
              split: option.split_asm)[1]
   apply (auto simp: valid_pdpti'_def cte_wp_at_ctes_of bit_simps)
  done

definition
  "asid_pool_invocation_map ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow> Assign asid p (cte_map slot)"

definition
  "isPML4Cap' cap \<equiv> \<exists>p asid. cap = (ArchObjectCap (PML4Cap p asid))"

definition
  "valid_apinv' ap \<equiv> case ap of Assign asid p slot \<Rightarrow>
  asid_pool_at' p and cte_wp_at' (isPML4Cap' o cteCap) slot and K
  (0 < asid \<and> asid \<le> 2^asid_bits - 1)"

lemma pap_corres:
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
    apply (rule corres_split [OF _ getSlotCap_corres])
      apply (rule_tac F="\<exists>p asid. rv = Structures_A.ArchObjectCap (X64_A.PML4Cap p asid)" in corres_gen_asm)
      apply clarsimp
      apply (rule_tac Q="valid_objs and pspace_aligned and pspace_distinct and asid_pool_at word2 and valid_etcbs and
                         cte_wp_at (\<lambda>c. cap_master_cap c =
                                        cap_master_cap (cap.ArchObjectCap (arch_cap.PML4Cap p asid))) (a,b)"
                      in corres_split)
         prefer 2
         apply simp
         apply (rule get_asid_pool_corres_inv')
        apply (rule corres_split)
           prefer 2
           apply (rule updateCap_same_master)
           apply simp
          apply (rule corres_rel_imp)
           apply simp
           apply (rule set_asid_pool_corres)
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
     apply (rule refl)
    apply (wp get_cap_wp getCTE_wp)+
   apply (clarsimp simp: valid_apinv_def cte_wp_at_def cap_master_cap_def is_pd_cap_def obj_at_def)
   apply (clarsimp simp: a_type_def)
  apply (clarsimp simp: cte_wp_at_ctes_of valid_apinv'_def)
  done

lemma armv_contextSwitch_obj_at [wp]:
  "\<lbrace>\<lambda>s. P (obj_at' P' t s)\<rbrace> armv_contextSwitch pd a \<lbrace>\<lambda>rv s. P (obj_at' P' t s)\<rbrace>"
  apply (simp add: armv_contextSwitch_def armv_contextSwitch_HWASID_def getHWASID_def)
  apply (wp doMachineOp_obj_at|wpc|simp)+
  done

crunch obj_at[wp]: setVMRoot "\<lambda>s. P (obj_at' P' t s)"
  (simp: crunch_simps)

lemma storeHWASID_invs:
  "\<lbrace>invs' and
   (\<lambda>s. x64KSASIDMap (ksArchState s) asid = None \<and>
        x64KSHWASIDTable (ksArchState s) hw_asid = None)\<rbrace>
  storeHWASID asid hw_asid
  \<lbrace>\<lambda>x. invs'\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule storeHWASID_valid_arch')
   apply fastforce
  apply (simp add: storeHWASID_def)
  apply (wp findVSpaceForASIDAssert_pd_at_wp)
  apply (clarsimp simp: invs'_def valid_state'_def valid_arch_state'_def
             valid_global_refs'_def global_refs'_def valid_machine_state'_def
             ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma storeHWASID_invs_no_cicd':
  "\<lbrace>invs_no_cicd' and
   (\<lambda>s. x64KSASIDMap (ksArchState s) asid = None \<and>
        x64KSHWASIDTable (ksArchState s) hw_asid = None)\<rbrace>
  storeHWASID asid hw_asid
  \<lbrace>\<lambda>x. invs_no_cicd'\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule storeHWASID_valid_arch')
   apply (fastforce simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
  apply (simp add: storeHWASID_def)
  apply (wp findVSpaceForASIDAssert_pd_at_wp)
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
  apply (wp findVSpaceForASIDAssert_pd_at_wp | wpc)+
  apply (clarsimp simp: invs'_def valid_state'_def valid_arch_state'_def
             valid_global_refs'_def global_refs'_def valid_machine_state'_def
             ct_not_inQ_def
           split del: if_split)
  apply (intro conjI)
    apply (fastforce dest: no_irq_use [OF no_irq_invalidateTLB_ASID])
   apply clarsimp
   apply (drule_tac x=p in spec)
   apply (drule use_valid)
    apply (rule_tac p=p in invalidateTLB_ASID_underlying_memory)
    apply blast
   apply clarsimp
  apply (simp add: ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def)
  done

lemma findFreeHWASID_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> findFreeHWASID \<lbrace>\<lambda>asid. invs_no_cicd'\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule findFreeHWASID_valid_arch)
   apply (fastforce simp: all_invs_but_ct_idle_or_in_cur_domain'_def)
  apply (simp add: findFreeHWASID_def invalidateHWASIDEntry_def invalidateASID_def
                   doMachineOp_def split_def
              cong: option.case_cong)
  apply (wp findVSpaceForASIDAssert_pd_at_wp | wpc)+
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_arch_state'_def
             valid_global_refs'_def global_refs'_def valid_machine_state'_def
             ct_not_inQ_def
           split del: if_split)
  apply (intro conjI)
    apply (fastforce dest: no_irq_use [OF no_irq_invalidateTLB_ASID])
   apply clarsimp
   apply (drule_tac x=p in spec)
   apply (drule use_valid)
    apply (rule_tac p=p in invalidateTLB_ASID_underlying_memory)
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

lemmas armv_ctxt_sw_defs = armv_contextSwitch_HWASID_def setHardwareASID_def setCurrentPD_def
                           writeTTBR0_def isb_def dsb_def

lemma dmo_armv_contextSwitch_HWASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (armv_contextSwitch_HWASID pd hwasid) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs')
   apply (simp add: armv_contextSwitch_HWASID_def)
   apply (wp no_irq_setCurrentPD no_irq_setHardwareASID no_irq)
  apply safe
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply (simp add: machine_op_lift_def machine_rest_lift_def split_def armv_ctxt_sw_defs
              | wp)+
  done


lemma dmo_armv_contextSwitch_HWASID_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (armv_contextSwitch_HWASID pd hwasid) \<lbrace>\<lambda>_. invs_no_cicd'\<rbrace>"
  apply (wp dmo_invs_no_cicd')
   apply (simp add: armv_contextSwitch_HWASID_def)
   apply (wp no_irq_setCurrentPD no_irq_setHardwareASID no_irq)
  apply safe
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply (simp add: machine_op_lift_def machine_rest_lift_def split_def armv_ctxt_sw_defs
              | wp)+
  done

lemma no_irq_armv_contextSwitch_HWASID:
  "no_irq (armv_contextSwitch_HWASID pd hwasid)"
  apply (simp add: armv_contextSwitch_HWASID_def)
  apply (wp no_irq_setCurrentPD no_irq_setHardwareASID)
  done

lemma armv_contextSwitch_invs [wp]:
  "\<lbrace>invs'\<rbrace> armv_contextSwitch pd asid \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: armv_contextSwitch_def)
  apply (wp dmo_invs' no_irq_armv_contextSwitch_HWASID no_irq)
  apply (rule hoare_post_imp[rotated], wp)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply (simp add: machine_op_lift_def machine_rest_lift_def split_def armv_ctxt_sw_defs
              | wp)+
  done

lemma armv_contextSwitch_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> armv_contextSwitch pd asid \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: armv_contextSwitch_def armv_contextSwitch_HWASID_def)
  apply (wp dmo_invs_no_cicd' no_irq_setHardwareASID no_irq_setCurrentPD no_irq)
  apply (rule hoare_post_imp[rotated], wp getHWASID_invs_no_cicd')
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply (clarsimp simp: machine_op_lift_def machine_rest_lift_def split_def armv_ctxt_sw_defs | wp)+
  done

lemma dmo_setCurrentPD_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (setCurrentPD addr) \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_setCurrentPD no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (clarsimp simp: setCurrentPD_def machine_op_lift_def writeTTBR0_def dsb_def isb_def
                        machine_rest_lift_def split_def | wp)+
  done

lemma dmo_setCurrentPD_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> doMachineOp (setCurrentPD addr) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (wp dmo_invs_no_cicd' no_irq_setCurrentPD no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
  apply (clarsimp simp: setCurrentPD_def machine_op_lift_def writeTTBR0_def dsb_def isb_def
                        machine_rest_lift_def split_def | wp)+
  done

lemma setVMRoot_invs [wp]:
  "\<lbrace>invs'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | wpcw
          | simp add: whenE_def checkPDNotInASIDMap_def split del: if_split)+
  done

lemma setVMRoot_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> setVMRoot p \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
  apply (simp add: setVMRoot_def getThreadVSpaceRoot_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps armv_contextSwitch_invs_no_cicd' getHWASID_invs_no_cicd'
             dmo_setCurrentPD_invs_no_cicd'
          | wpcw
          | simp add: whenE_def checkPDNotInASIDMap_def split del: if_split)+
  done

crunch nosch [wp]: setVMRoot "\<lambda>s. P (ksSchedulerAction s)"
  (wp: crunch_wps getObject_inv simp: crunch_simps
       loadObject_default_def ignore: getObject)

crunch it' [wp]: findVSpaceForASID "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv ignore: getObject)

crunch it' [wp]: deleteASIDPool "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv mapM_wp'
   ignore: getObject)

crunch it' [wp]: lookupPTSlot "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def wp: getObject_inv
   ignore: getObject)

crunch it' [wp]: storePTE "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle'
   ignore: setObject)

crunch it' [wp]: storePDE "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps updateObject_default_def wp: setObject_idle'
   ignore: setObject)

crunch it' [wp]: flushTable "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def
   wp: setObject_idle' hoare_drop_imps mapM_wp'
   ignore: getObject)

crunch it' [wp]: deleteASID "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps loadObject_default_def updateObject_default_def
   wp: getObject_inv
   ignore: getObject setObject)

lemma valid_slots_lift':
  assumes t: "\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at' T p\<rbrace>"
  shows "\<lbrace>valid_slots' x\<rbrace> f \<lbrace>\<lambda>rv. valid_slots' x\<rbrace>"
  apply (clarsimp simp: valid_slots'_def split: sum.splits prod.splits)
  apply safe
   apply (rule hoare_pre, wp hoare_vcg_const_Ball_lift t valid_pde_lift' valid_pte_lift', simp)+
  done

crunch typ_at' [wp]: performPageTableInvocation "\<lambda>s. P (typ_at' T p s)"
  (ignore: getObject wp: crunch_wps)

crunch typ_at' [wp]: performPageDirectoryInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps)

crunch typ_at' [wp]: performPageInvocation "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps ignore: getObject)

crunch typ_at' [wp]: performASIDPoolInvocation "\<lambda>s. P (typ_at' T p s)"
  (ignore: getObject wp: getObject_cte_inv getASID_wp)

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
  apply (simp add: storePDE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePTE_pred_tcb_at' [wp]:
  "\<lbrace>pred_tcb_at' proj P t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. pred_tcb_at' proj P t\<rbrace>"
  apply (simp add: storePTE_def pred_tcb_at'_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
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

crunch nosch [wp]: storePDE "\<lambda>s. P (ksSchedulerAction s)"
  (simp: updateObject_default_def)

crunch ksQ [wp]: storePDE "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePDE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePDE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePDE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

crunch norqL1[wp]: storePDE "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

crunch norqL2[wp]: storePDE "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePDE_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> storePDE p pde \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma storePDE_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> storePDE p pde \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma storePDE_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: storePDE_def)
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd'
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma storePDE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs)
  done

lemma setObject_pde_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pde::pde) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

crunch ksInterruptState [wp]: storePDE "\<lambda>s. P (ksInterruptState s)"
  (ignore: setObject)

lemma storePDE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePDE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePDE p pde \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

crunch arch' [wp]: storePDE "\<lambda>s. P (ksArchState s)"
  (ignore: setObject)

crunch cur' [wp]: storePDE "\<lambda>s. P (ksCurThread s)"
  (ignore: setObject)

lemma storePDE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePDE pde p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePDE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
  done

crunch no_0_obj' [wp]: storePDE no_0_obj'

lemma storePDE_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings' and K (valid_pde_mapping' (p && mask pdBits) pde)\<rbrace>
      storePDE p pde
   \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp valid_pde_mappings_lift')
   apply (rule hoare_post_imp)
    apply (simp only: obj_at'_real_def)
   apply (simp add: storePDE_def)
   apply (wp setObject_ko_wp_at)
      apply simp
     apply (simp add: objBits_simps archObjSize_def)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def projectKOs)
  apply assumption
  done

lemma storePDE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePDE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePDE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

crunch pspace_domain_valid[wp]: storePDE "pspace_domain_valid"

lemma storePDE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePDE p pde \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePDE_nosch])
  apply (simp add: storePDE_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_PDE_ct)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)+
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
by (simp add: storePDE_def) wp

lemma storePDE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePDE p pde \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
by (simp add: storePDE_def) wp

lemma storePDE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePDE p pde \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePDE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

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

lemma storePDPTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePDPTE_nosch])
  apply (simp add: storePDPTE_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_PDPTE_ct)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_pdpte_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pdpte) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pdpte_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pdpte) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePDPTE_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
by (simp add: storePDPTE_def) wp

lemma storePDPTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
by (simp add: storePDPTE_def) wp

lemma storePDPTE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePDPTE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePDPTE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePDPTE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePDPTE p pdpte \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pdpte_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pdpte::pdpte) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

lemma storePML4E_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePML4E_nosch])
  apply (simp add: storePML4E_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_PML4E_ct)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)+
  done

lemma setObject_pml4e_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> setObject t (v::pml4e) \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma setObject_pml4e_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> setObject t (v::pml4e) \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_default_inv | simp)+
  done

lemma storePML4E_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
by (simp add: storePML4E_def) wp

lemma storePML4E_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
by (simp add: storePML4E_def) wp

lemma storePML4E_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePML4E_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePML4E_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePML4E_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePML4E p pml4e \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma setObject_pml4e_ksDomScheduleIdx [wp]:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject p (pml4e::pml4e) \<lbrace>\<lambda>_. \<lambda>s. P (ksDomScheduleIdx s)\<rbrace>"
  by (wp updateObject_default_inv|simp add:setObject_def | wpc)+

crunch ksDomScheduleIdx[wp]: storePTE, storePDE, storePDPTE, storePML4E "\<lambda>s. P (ksDomScheduleIdx s)"
(ignore: getObject setObject)

crunch gsMaxObjectSize[wp]: storePTE, storePDE, storePDPTE, storePML4E "\<lambda>s. P (gsMaxObjectSize s)"
(ignore: getObject setObject wp: setObject_ksPSpace_only updateObject_default_inv)

crunch gsUntypedZeroRanges[wp]: storePTE, storePDE, storePDPTE, storePML4E "\<lambda>s. P (gsUntypedZeroRanges s)"
(ignore: getObject setObject wp: setObject_ksPSpace_only updateObject_default_inv)

lemma storePDE_invs[wp]:
  "\<lbrace>invs' and valid_pde' pde\<rbrace>
      storePDE p pde
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift'
             irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
           | simp add: cteCaps_of_def o_def)+
  apply clarsimp
  done

lemma storePTE_valid_mdb [wp]:
  "\<lbrace>valid_mdb'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  by (simp add: valid_mdb'_def) wp

crunch nosch [wp]: storePTE "\<lambda>s. P (ksSchedulerAction s)"
  (simp: updateObject_default_def)

crunch ksQ [wp]: storePTE "\<lambda>s. P (ksReadyQueues s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> storePTE ptr pde \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: obj_at'_real_def storePTE_def)
  apply (wp setObject_ko_wp_at | simp add: objBits_simps archObjSize_def)+
  apply (clarsimp simp: projectKOs obj_at'_def ko_wp_at'_def)
  done

crunch norqL1[wp]: storePTE "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

crunch norqL2[wp]: storePTE "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  (simp: updateObject_default_def ignore: setObject)

lemma storePTE_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> storePTE p pde \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma storePTE_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> storePTE p pde \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma storePTE_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> storePTE p pte \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: storePTE_def)
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd'
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma storePTE_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs)
  done

lemma setObject_pte_ksInt [wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_. \<lambda>s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_default_inv|simp)+

crunch ksInt' [wp]: storePTE "\<lambda>s. P (ksInterruptState s)"
  (ignore: setObject)

lemma storePTE_ifunsafe [wp]:
  "\<lbrace>if_unsafe_then_cap'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. if_unsafe_then_cap'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule hoare_pre)
   apply (rule setObject_ifunsafe' [where P=\<top>], simp)
     apply (auto simp: updateObject_default_def in_monad projectKOs)[2]
   apply wp
  apply simp
  done

lemma storePTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

crunch arch' [wp]: storePTE "\<lambda>s. P (ksArchState s)"
  (ignore: setObject)

crunch cur' [wp]: storePTE "\<lambda>s. P (ksCurThread s)"
  (ignore: setObject)

lemma storePTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> storePTE pte p \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (simp add: storePTE_def)
  apply (wpsimp wp: valid_irq_states_lift' dmo_lift' no_irq_storeWord setObject_ksMachine
                    updateObject_default_inv)
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

crunch no_0_obj' [wp]: storePTE no_0_obj'

lemma storePTE_pde_mappings'[wp]:
  "\<lbrace>valid_pde_mappings'\<rbrace> storePTE p pte \<lbrace>\<lambda>rv. valid_pde_mappings'\<rbrace>"
  apply (wp valid_pde_mappings_lift')
   apply (simp add: storePTE_def)
   apply (rule obj_at_setObject2)
   apply (clarsimp dest!: updateObject_default_result)
  apply assumption
  done

lemma storePTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> storePTE p pde \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: storePTE_def valid_machine_state'_def pointerInUserData_def
                   pointerInDeviceData_def)
  apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv
            hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  done

crunch pspace_domain_valid[wp]: storePTE "pspace_domain_valid"

lemma storePTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF storePTE_nosch])
  apply (simp add: storePTE_def)
  apply (rule hoare_weaken_pre)
   apply (wps setObject_pte_ct)
  apply (rule obj_at_setObject2)
   apply (clarsimp simp: updateObject_default_def in_monad)+
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
  by (simp add: storePTE_def) wp

lemma storePTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace> storePTE p pde \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  by (simp add: storePTE_def) wp


lemma storePTE_tcb_obj_at'[wp]:
  "\<lbrace>obj_at' (P::tcb \<Rightarrow> bool) t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: storePTE_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp add: updateObject_default_def in_monad)
  done

lemma storePTE_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t\<rbrace> storePTE p pte \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma storePTE_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain'\<rbrace> storePTE p pte \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
  by (wp ct_idle_or_in_cur_domain'_lift hoare_vcg_disj_lift)

lemma storePTE_invs [wp]:
  "\<lbrace>invs' and valid_pte' pte\<rbrace> storePTE p pte \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
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

lemma setASIDPool_valid_queues [wp]:
  "\<lbrace>Invariants_H.valid_queues\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. Invariants_H.valid_queues\<rbrace>"
  by (wp valid_queues_lift | simp add: pred_tcb_at'_def)+

lemma setASIDPool_valid_queues' [wp]:
  "\<lbrace>valid_queues'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. valid_queues'\<rbrace>"
  by (wp valid_queues_lift')

lemma setASIDPool_state_refs' [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of' s)\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  apply (clarsimp simp: setObject_def valid_def in_monad split_def
                        updateObject_default_def projectKOs objBits_simps
                        in_magnitude_check state_refs_of'_def ps_clear_upd'
                 elim!: rsubst[where P=P] intro!: ext
             split del: if_split cong: option.case_cong if_cong)
  apply (simp split: option.split)
  done

lemma setASIDPool_iflive [wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule setObject_iflive' [where P=\<top>], simp)
      apply (simp add: objBits_simps archObjSize_def)
     apply (auto simp: updateObject_default_def in_monad projectKOs pageBits_def)
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
  "\<lbrace>valid_idle'\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  unfolding valid_idle'_def
  by (rule hoare_lift_Pf [where f="ksIdleThread"]; wp)

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

lemma setASIDPool_invs [wp]:
  "\<lbrace>invs' and valid_asid_pool' ap\<rbrace> setObject p (ap::asidpool) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (rule hoare_pre)
   apply (wp sch_act_wf_lift valid_global_refs_lift' irqs_masked_lift
             valid_arch_state_lift' valid_irq_node_lift
             cur_tcb_lift valid_irq_handlers_lift''
             untyped_ranges_zero_lift
             updateObject_default_inv
           | simp add: cteCaps_of_def
           | rule setObject_ksPSpace_only)+
  apply (clarsimp simp add: setObject_def o_def)
  done

crunch cte_wp_at'[wp]: unmapPageTable "\<lambda>s. P (cte_wp_at' P' p s)"
  (wp: crunch_wps simp: crunch_simps ignore: getObject setObject)

lemmas storePDE_Invalid_invs = storePDE_invs[where pde=InvalidPDE, simplified]

lemma setVMRootForFlush_invs'[wp]: "\<lbrace>invs'\<rbrace> setVMRootForFlush a b \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: setVMRootForFlush_def)
  apply (wp storePDE_Invalid_invs mapM_wp' crunch_wps | simp add: crunch_simps)+
  apply (simp add: getThreadVSpaceRoot_def)
  apply (wp storePDE_Invalid_invs mapM_wp' crunch_wps | simp add: crunch_simps)+
  done


lemma dmo_invalidateTLB_VAASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (invalidateTLB_VAASID x) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_invalidateTLB_VAASID no_irq)
  apply clarsimp
  apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
         in use_valid)
    apply (clarsimp simp: invalidateTLB_VAASID_def machine_op_lift_def
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
lemma dmo_invalidateTLB_ASID_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (invalidateTLB_ASID a) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_invalidateTLB_ASID no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: invalidateTLB_ASID_def machine_op_lift_def
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
  (ignore: getObject setObject storePDE doMachineOp
       wp: dmo_invalidateTLB_VAASID_invs' dmo_setCurrentPD_invs'
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

lemma mapM_x_storePTE_invs:
  "\<lbrace>invs' and valid_pte' pte\<rbrace> mapM_x (swp storePTE pte) ps \<lbrace>\<lambda>xa. invs'\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_x_wp')
   apply simp
   apply (wp valid_pte_lift')
    apply simp+
  done

lemma mapM_x_storePDE_invs:
  "\<lbrace>invs' and valid_pde' pde \<rbrace>
         mapM_x (swp storePDE pde) ps \<lbrace>\<lambda>xa. invs'\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_x_wp[OF _ subset_refl])
   apply simp
   apply (wp valid_pde_lift')
    apply simp+
  done

lemma mapM_storePTE_invs:
  "\<lbrace>invs' and valid_pte' pte\<rbrace> mapM (swp storePTE pte) ps \<lbrace>\<lambda>xa. invs'\<rbrace>"
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
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

lemmas unmapPage_typ_ats [wp] = typ_at_lifts [OF unmapPage_typ_at']

crunch inv: lookupPTSlot P
  (wp: crunch_wps simp: crunch_simps ignore: getObject)

lemma flushPage_invs' [wp]:
  "\<lbrace>invs'\<rbrace> flushPage sz pd asid vptr \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: flushPage_def)
  apply (wp dmo_invalidateTLB_VAASID_invs' hoare_drop_imps setVMRootForFlush_invs'
            no_irq_invalidateTLB_VAASID
         |simp)+
  done

lemma unmapPage_invs' [wp]:
  "\<lbrace>invs'\<rbrace> unmapPage sz asid vptr pptr \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: unmapPage_def)
  apply (rule hoare_pre)
   apply (wp lookupPTSlot_inv
             mapM_storePTE_invs mapM_storePDE_invs
             hoare_vcg_const_imp_lift
         |wpc
         |simp)+
  done

crunch (no_irq) no_irq[wp]: doFlush

crunch invs'[wp]: pteCheckIfMapped, pdeCheckIfMapped "invs'"
  (ignore: getObject)

crunch valid_pte'[wp]: pteCheckIfMapped, pdeCheckIfMapped "valid_pte' pte"
  (ignore: getObject)

crunch valid_pde'[wp]: pteCheckIfMapped, pdeCheckIfMapped "valid_pde' pde"
  (ignore: getObject)

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
        apply (clarsimp simp: doFlush_def split: flush_type.splits)
        apply (clarsimp split: sum.split | intro conjI impI
               | wp mapM_x_storePTE_invs mapM_x_storePDE_invs)+
     apply (clarsimp simp: valid_page_inv'_def valid_slots'_def
                           valid_pde_slots'_def
                    split: sum.split option.splits | intro conjI impI
            | wp mapM_storePTE_invs mapM_storePDE_invs
                 mapM_x_storePTE_invs mapM_x_storePDE_invs
                 hoare_vcg_all_lift hoare_vcg_const_imp_lift
                 arch_update_updateCap_invs unmapPage_cte_wp_at' getSlotCap_wp
            | wpc)+
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


lemma diminished_valid':
  "diminished' cap cap' \<Longrightarrow> valid_cap' cap = valid_cap' cap'"
  apply (clarsimp simp add: diminished'_def)
  apply (rule ext)
  apply (simp add: maskCapRights_def Let_def split del: if_split)
  apply (cases cap'; simp add: isCap_simps valid_cap'_def capAligned_def split del: if_split)
  by (simp add: X64_H.maskCapRights_def isPageCap_def Let_def split del: if_split split: arch_capability.splits)

lemma diminished_isPDCap:
  "diminished' cap cap' \<Longrightarrow> isPDCap cap' = isPDCap cap"
  by (blast dest: diminished_capMaster capMaster_isPDCap)

end

lemma cteCaps_of_ctes_of_lift:
  "(\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>) \<Longrightarrow> \<lbrace>\<lambda>s. P (cteCaps_of s) \<rbrace> f \<lbrace>\<lambda>_ s. P (cteCaps_of s)\<rbrace>"
  unfolding cteCaps_of_def .
end
