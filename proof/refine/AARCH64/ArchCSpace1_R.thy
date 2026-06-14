(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* CSpace refinement - architecture-specific *)

theory ArchCSpace1_R
imports CSpace1_R
begin

context Arch begin arch_global_naming

named_theorems CSpace1_R_assms

lemma ghost_relation_wrapper_same_abs_set_cap[CSpace1_R_assms]:
  "\<lbrakk> ghost_relation_wrapper a c; ((), a') \<in> fst (set_cap cap dest a);
     ksArchState c' = ksArchState c; gsUserPages c' = gsUserPages c; gsCNodes c' = gsCNodes c \<rbrakk>
   \<Longrightarrow> ghost_relation_wrapper a' c'"
  by (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv data_at_def)

lemma ghost_relation_wrapper_set_cap_twice[CSpace1_R_assms]:
  "\<lbrakk> ghost_relation_wrapper a c;
     ((), a') \<in> fst (set_cap dcap src a); ((), a'') \<in> fst (set_cap scap dest a');
     ksArchState c' = ksArchState c; gsUserPages c' = gsUserPages c; gsCNodes c' = gsCNodes c \<rbrakk>
   \<Longrightarrow> ghost_relation_wrapper a'' c'"
  by (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv data_at_def)

lemma archMDBAssertions_cross[CSpace1_R_assms]:
  "\<lbrakk> valid_arch_mdb (is_original_cap s) (caps_of_state s); valid_arch_state s; valid_objs s;
     (s, s') \<in> state_relation \<rbrakk>
   \<Longrightarrow> archMDBAssertions s'"
  unfolding archMDBAssertions_def
  by (simp add: arch_mdb_assert_def)

lemma isArchMDBParentOf_def2:
  "isArchMDBParentOf cap cap' firstBadged =
   ((isArchSGISignalCap cap \<longrightarrow> isArchSGISignalCap cap' \<longrightarrow> \<not>firstBadged) \<and>
    (isArchSMCCap cap \<longrightarrow> isArchSMCCap cap' \<longrightarrow>
       archSMCBadge cap = 0 \<or> archSMCBadge cap = archSMCBadge cap' \<and> \<not>firstBadged))"
  by (auto simp: isArchMDBParentOf_def isCap_simps split: capability.splits arch_capability.splits)

lemma sameRegionAs_SGISignalCap[simp]:
  "sameRegionAs (ArchObjectCap (SGISignalCap irq target)) cap' =
   (cap' = ArchObjectCap (SGISignalCap irq target))"
  by (auto simp add: global.sameRegionAs_def AARCH64_H.sameRegionAs_def isCap_simps split: if_splits)

lemma sameRegionAs_SMCCap[simp]:
  "sameRegionAs (ArchObjectCap (SMCCap smc_badge)) cap' =
   (\<exists>smc_badge'. cap' = ArchObjectCap (SMCCap smc_badge'))"
  by (auto simp add: global.sameRegionAs_def AARCH64_H.sameRegionAs_def isCap_simps split: if_splits)

lemma isMDBParentOf_CTE1:
  "isMDBParentOf (CTE cap node) cte =
   (\<exists>cap' node'. cte = CTE cap' node' \<and> sameRegionAs cap cap'
      \<and> mdbRevocable node
      \<and> (isArchSGISignalCap cap \<longrightarrow> \<not> mdbFirstBadged node')
      \<and> (isArchSMCCap cap \<longrightarrow>
           archSMCBadge cap = 0 \<or> archSMCBadge cap = archSMCBadge cap' \<and> \<not> mdbFirstBadged node')
      \<and> (isEndpointCap cap \<longrightarrow> capEPBadge cap \<noteq> 0 \<longrightarrow>
           capEPBadge cap = capEPBadge cap' \<and> \<not> mdbFirstBadged node')
      \<and> (isNotificationCap cap \<longrightarrow> capNtfnBadge cap \<noteq> 0 \<longrightarrow>
           capNtfnBadge cap = capNtfnBadge cap' \<and> \<not> mdbFirstBadged node'))"
  apply (simp add: isMDBParentOf_def isArchMDBParentOf_def2 Let_def
              split: cte.splits split del: if_split
              cong: if_cong)
  apply (clarsimp simp: Let_def isCap_simps)
  apply (fastforce simp: isCap_simps)
  done

lemma isMDBParentOf_CTE:
  "isMDBParentOf (CTE cap node) cte =
   (\<exists>cap' node'. cte = CTE cap' node' \<and> sameRegionAs cap cap'
      \<and> mdbRevocable node
      \<and> (isArchSGISignalCap cap \<longrightarrow> \<not> mdbFirstBadged node')
      \<and> (capBadge cap, capBadge cap') \<in> capBadge_ordering (mdbFirstBadged node'))"
  apply (simp add: isMDBParentOf_CTE1)
  apply (intro arg_cong[where f=Ex] ext conj_cong refl)
  apply (cases cap, simp_all add: isCap_simps)
    apply (auto elim!: sameRegionAsE simp: isCap_simps)[2]
  apply (rename_tac acap, case_tac acap; simp)
  apply (auto elim!: sameRegionAsE simp: isCap_simps)
  done

lemma isMDBParentOf_trans:
  "\<lbrakk> isMDBParentOf a b; isMDBParentOf b c \<rbrakk> \<Longrightarrow> isMDBParentOf a c"
  apply (cases a)
  apply (clarsimp simp: isMDBParentOf_CTE)
  apply (frule(1) sameRegionAs_trans, simp)
  apply (rule conjI, clarsimp simp: isCap_simps)
  apply (erule(1) capBadge_ordering_trans)
  done

lemma parentOf_trans[CSpace1_R_assms]:
  "\<lbrakk> s \<turnstile> a parentOf b; s \<turnstile> b parentOf c \<rbrakk> \<Longrightarrow> s \<turnstile> a parentOf c"
  by (auto simp: parentOf_def elim: isMDBParentOf_trans)

lemma same_arch_region_as_relation:
  "\<lbrakk>acap_relation c d; acap_relation c' d'\<rbrakk> \<Longrightarrow>
   arch_same_region_as c c' = sameRegionAs (ArchObjectCap d) (ArchObjectCap d')"
  by (cases c; cases c')
     (auto simp: AARCH64_H.sameRegionAs_def global.sameRegionAs_def Let_def isCap_simps mask_def
                 add_diff_eq up_ucast_inj_eq)

lemma is_physical_relation:
  "cap_relation c c' \<Longrightarrow> is_physical c = isPhysicalCap c'"
  by (auto simp: is_physical_def arch_is_physical_def
           split: cap.splits arch_cap.splits)

lemma obj_ref_of_relation[CSpace1_R_assms]:
  "\<lbrakk> cap_relation c c'; capClass c' = PhysicalClass \<rbrakk> \<Longrightarrow>
   obj_ref_of c = capUntypedPtr c'"
  by (cases c; simp) (rename_tac arch_cap, case_tac arch_cap, auto)

lemma isIRQControlCapDescendant_ex:
  "isIRQControlCapDescendant cap = (\<exists>irq target. cap = SGISignalCap irq target)"
  by (simp add: isIRQControlCapDescendant_def split: capability.splits arch_capability.splits)

lemma acap_relation_SGISignalCap:
  "acap_relation acap (SGISignalCap irq target) =
   (\<exists>irq' target'. acap = arch_cap.SGISignalCap irq' target' \<and>
                    irq = ucast irq' \<and> target = ucast target')"
  by (cases acap) auto

lemma obj_size_relation:
  "\<lbrakk> cap_relation c c'; capClass c' = PhysicalClass \<rbrakk> \<Longrightarrow>
   obj_size c = capUntypedSize c'"
  apply (cases c, simp_all add: objBits_simps' zbits_map_def
                                cte_level_bits_def
                         split: option.splits sum.splits)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; simp add: objBits_def AARCH64_H.capUntypedSize_def bit_simps')
  done

lemma same_region_as_relation[CSpace1_R_assms]:
  "\<lbrakk> cap_relation c d; cap_relation c' d' \<rbrakk> \<Longrightarrow> same_region_as c c' = sameRegionAs d d'"
  apply (cases c)
             apply clarsimp
            apply (clarsimp simp: global.sameRegionAs_def isCap_simps Let_def is_physical_relation)
            apply (auto simp: obj_ref_of_relation obj_size_relation cong: conj_cong)[1]
           apply (cases c', auto simp: global.sameRegionAs_def isCap_simps Let_def)[1]
          apply (cases c', auto simp: global.sameRegionAs_def isCap_simps Let_def)[1]
         apply (cases c', auto simp: global.sameRegionAs_def isCap_simps Let_def)[1]
        apply (cases c', auto simp: global.sameRegionAs_def isCap_simps Let_def bits_of_def)[1]
       apply (cases c', auto simp: global.sameRegionAs_def isCap_simps Let_def)[1]
      apply (cases c', auto simp: global.sameRegionAs_def isCap_simps Let_def)[1]
     apply (cases c', auto simp: global.sameRegionAs_def isCap_simps Let_def is_irq_control_descendant_def
                                 arch_cap.is_SGISignalCap_def isIRQControlCapDescendant_ex
                                 acap_relation_SGISignalCap)[1]
    apply (cases c', auto simp: global.sameRegionAs_def isCap_simps Let_def)[1]
   apply (cases c', auto simp: global.sameRegionAs_def isCap_simps Let_def)[1]
  apply simp
  apply (cases c')
             apply (clarsimp simp: same_arch_region_as_relation |
                    clarsimp simp: global.sameRegionAs_def isCap_simps Let_def)+
  done

lemma acap_relation_SGISignalCapD:
  "acap_relation acap (SGISignalCap irq target) \<Longrightarrow>
   acap = arch_cap.SGISignalCap (ucast irq) (ucast target)"
  by (cases acap) (auto simp: ucast_down_ucast_id is_down)

lemma acap_relation_SMCCap[simp]:
  "acap_relation acap (SMCCap smc_badge) = (acap = arch_cap.SMCCap smc_badge)"
  by (cases acap) auto

lemma cap_relation_SMCCap[simp]:
  "cap_relation cap (ArchObjectCap (SMCCap smc_badge)) =
     (cap = cap.ArchObjectCap (arch_cap.SMCCap smc_badge))"
  by (cases cap) auto

lemma can_be_is[CSpace1_R_assms]:
  "\<lbrakk> cap_relation c (cteCap cte); cap_relation c' (cteCap cte');
     mdbRevocable (cteMDBNode cte) = r;
     mdbFirstBadged (cteMDBNode cte') = r' \<rbrakk> \<Longrightarrow>
   should_be_parent_of c r c' r' = isMDBParentOf cte cte'"
  unfolding should_be_parent_of_def should_be_arch_parent_of_def isMDBParentOf_def
  apply (cases cte)
  apply (rename_tac cap mdbnode)
  apply (cases cte')
  apply (rename_tac cap' mdbnode')
  apply (clarsimp split del: if_split)
  apply (case_tac "mdbRevocable mdbnode")
   prefer 2
   apply simp
  apply (clarsimp split del: if_split)
  apply (case_tac "RetypeDecls_H.sameRegionAs cap cap'")
   prefer 2
   apply (simp add: same_region_as_relation)
  apply (simp add: same_region_as_relation split del: if_split)
  apply (cases c, simp_all add: isCap_simps arch_cap.is_SGISignalCap_def isArchMDBParentOf_def2)
    apply (cases c', auto simp: global.sameRegionAs_def Let_def isCap_simps)[1]
   apply (cases c', auto simp: global.sameRegionAs_def isCap_simps is_cap_simps)[1]
  apply (auto simp: Let_def isCap_simps is_cap_simps dest!: acap_relation_SGISignalCapD)[1]
  done

lemma maskCap_valid[simp]:
  "s \<turnstile>' global.maskCapRights R cap = s \<turnstile>' cap"
  by (clarsimp simp: valid_cap'_def global.maskCapRights_def isCap_simps
                     capAligned_def AARCH64_H.maskCapRights_def
              split: capability.split arch_capability.split
               cong: if_cong)

lemma cap_map_update_data:
  assumes "cap_relation c c'"
  shows   "cap_relation (update_cap_data p x c) (updateCapData p x c')"
proof -
  note simps = update_cap_data_def global.updateCapData_def word_size
               isCap_defs is_cap_defs Let_def badge_bits_def
               cap_rights_update_def badge_update_def
  { fix x :: machine_word
    define y where "y \<equiv> (x >> 6) && mask 58" (* guard_bits *)
    define z where "z \<equiv> unat (x && mask 6)" (* cnode_guard_size_bits *)
    have "of_bl (to_bl (y && mask z)) = (of_bl (replicate (64-z) False @ drop (64-z) (to_bl y))::machine_word)"
      by (simp add: bl_and_mask)
    then
    have "y && mask z = of_bl (drop (64 - z) (to_bl y))"
      apply simp
      apply (subst test_bit_eq_iff [symmetric])
      apply (rule ext)
      apply (clarsimp simp: test_bit_of_bl nth_append)
      done
  } note x = this
  from assms
  show ?thesis
  apply (cases c)
            apply (simp_all add: simps)[5]
       defer
       apply (simp_all add: simps)[4]
   apply (clarsimp simp: simps the_arch_cap_def)
   apply (rename_tac arch_cap)
   apply (case_tac arch_cap; simp add: simps arch_update_cap_data_def
                             AARCH64_H.updateCapData_def)
  \<comment> \<open>CNodeCap\<close>
  apply (simp add: simps word_bits_def the_cnode_cap_def andCapRights_def
                   rightsFromWord_def data_to_rights_def nth_ucast cteRightsBits_def cteGuardBits_def)
  apply (insert x)
  apply (subgoal_tac "unat (x && mask 6) < unat (2^6::machine_word)")
   prefer 2
   apply (fold word_less_nat_alt)[1]
   apply (rule and_mask_less_size)
   apply (simp add: word_size)
  apply (simp add: word_bw_assocs cnode_padding_bits_def cnode_guard_size_bits_def)
  done
qed

lemmas setCTE_typ_ats[wp] = typ_at_lifts[OF setCTE_typ_at']

context begin (* private method *)

private method updateCapData_cases for c =
  (cases c; simp add: global.updateCapData_def isCap_simps Let_def),
  (rename_tac arch_capability),
  (case_tac arch_capability; simp add: AARCH64_H.updateCapData_def isCap_simps Let_def)

lemma capASID_update[simp]:
  "capASID (RetypeDecls_H.updateCapData P x c) = capASID c"
  unfolding capASID_def
  by (updateCapData_cases c)

lemma cap_vptr_update'[simp]:
  "cap_vptr' (RetypeDecls_H.updateCapData P x c) = cap_vptr' c"
  unfolding capASID_def
  by (updateCapData_cases c)

lemma cap_asid_base_update'[simp]:
  "cap_asid_base' (RetypeDecls_H.updateCapData P x c) = cap_asid_base' c"
  unfolding cap_asid_base'_def
  by (updateCapData_cases c)

lemma arch_updateCapData_Master:
  "Arch.updateCapData P d acap \<noteq> NullCap \<Longrightarrow>
   capMasterCap (Arch.updateCapData P d acap) = capMasterCap (ArchObjectCap acap)"
  by (cases acap; simp add: AARCH64_H.updateCapData_def split: if_split_asm)

lemma updateCapData_Master:
  "updateCapData P d cap \<noteq> NullCap \<Longrightarrow> capMasterCap (updateCapData P d cap) = capMasterCap cap"
  apply (cases cap; simp add: global.updateCapData_def isCap_simps Let_def split: if_split_asm)
  apply (simp add: arch_updateCapData_Master)
  done

lemma updateCapData_Reply:
  "isReplyCap (updateCapData P x c) = isReplyCap c"
  by (updateCapData_cases c)

end (* context private method *)

lemma capASID_mask[simp]:
  "capASID (maskCapRights x c) = capASID c"
  unfolding capASID_def
  apply (cases c, simp_all add: global.maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: AARCH64_H.maskCapRights_def isCap_simps Let_def)
  done

lemma cap_vptr_mask'[simp]:
  "cap_vptr' (maskCapRights x c) = cap_vptr' c"
  unfolding cap_vptr'_def
  apply (cases c, simp_all add: global.maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: AARCH64_H.maskCapRights_def isCap_simps Let_def)
  done

lemma cap_asid_base_mask'[simp]:
  "cap_asid_base' (maskCapRights x c) = cap_asid_base' c"
  unfolding cap_vptr'_def
  apply (cases c, simp_all add: global.maskCapRights_def isCap_simps Let_def)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability,
         simp_all add: AARCH64_H.maskCapRights_def isCap_simps Let_def)
  done

lemma tcb_cases_related2:
  "tcb_cte_cases (v - x) = Some (getF, setF) \<Longrightarrow>
   \<exists>getF' setF' restr. tcb_cap_cases (tcb_cnode_index (unat ((v - x) >> cte_level_bits))) = Some (getF', setF', restr)
          \<and> cte_map (x, tcb_cnode_index (unat ((v - x) >> cte_level_bits))) = v
          \<and> (\<forall>tcb tcb'. tcb_relation tcb tcb' \<longrightarrow> cap_relation (getF' tcb) (cteCap (getF tcb')))
          \<and> (\<forall>tcb tcb' cap cte. tcb_relation tcb tcb' \<longrightarrow> cap_relation cap (cteCap cte)
                        \<longrightarrow> tcb_relation (setF' (\<lambda>x. cap) tcb) (setF (\<lambda>x. cte) tcb'))"
  apply (clarsimp simp: tcb_cte_cases_def tcb_relation_def cte_level_bits_def cteSizeBits_def
                        tcb_cap_cases_simps[simplified]
                 split: if_split_asm)
  apply (simp_all add: tcb_cnode_index_def cte_level_bits_def cte_map_def field_simps to_bl_1)
  done

lemma cte_map_pulls_tcb_to_abstract:
  "\<lbrakk> y = cte_map z; pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' x = Some (KOTCB tcb);
     pspace_aligned s; pspace_distinct s; valid_objs s;
     cte_at z s; (y - x) \<in> dom tcb_cte_cases \<rbrakk>
     \<Longrightarrow> \<exists>tcb'. kheap s x = Some (TCB tcb') \<and> tcb_relation tcb' tcb
                  \<and> (z = (x, tcb_cnode_index (unat ((y - x) >> cte_level_bits))))"
  apply (rule pspace_dom_relatedE, assumption+)
  apply (erule(1) obj_relation_cutsE;
         clarsimp simp: other_obj_relation_def other_aobj_relation_def
                  split: Structures_A.kernel_object.split_asm
                         AARCH64_A.arch_kernel_obj.split_asm if_split_asm)
  apply (drule tcb_cases_related2)
  apply clarsimp
  apply (frule(1) cte_wp_at_tcbI [OF _ _ TrueI, where t="(a, b)" for a b, simplified])
  apply (erule(5) cte_map_inj_eq [OF sym])
  done

lemma pspace_relation_update_tcbs:
  "\<lbrakk> pspace_relation s s'; s x = Some (TCB otcb); s' x = Some (KOTCB otcb');
        tcb_relation tcb tcb' \<rbrakk>
       \<Longrightarrow> pspace_relation (s(x \<mapsto> TCB tcb)) (s'(x \<mapsto> KOTCB tcb'))"
  apply (simp add: pspace_relation_def pspace_dom_update
                   dom_fun_upd2
              del: dom_fun_upd)
  apply (erule conjE)
  apply (rule ballI, drule(1) bspec)
  apply (clarsimp simp: tcb_relation_cut_def split: Structures_A.kernel_object.split_asm)
  apply (drule bspec, fastforce)
  apply clarsimp
  apply (erule(1) obj_relation_cutsE, simp_all split: if_split_asm)
  done

lemma cte_map_pulls_cte_to_abstract:
  "\<lbrakk> y = cte_map z; pspace_relation (kheap s) (ksPSpace s');
     ksPSpace s' y = Some (KOCTE cte);
     valid_objs s; pspace_aligned s; pspace_distinct s; cte_at z s \<rbrakk>
     \<Longrightarrow> \<exists>sz cs cap. kheap s (fst z) = Some (CNode sz cs) \<and> cs (snd z) = Some cap
                  \<and> cap_relation cap (cteCap cte)"
  apply (rule pspace_dom_relatedE, assumption+)
  apply (erule(1) obj_relation_cutsE, simp_all)
  apply clarsimp
  apply (frule(1) cte_map_inj_eq[OF sym], simp_all)
  apply (rule cte_wp_at_cteI, (fastforce split: if_split_asm)+)
  done

lemma pspace_relation_update_ctes:
  assumes ps: "pspace_relation s s'"
    and octe: "s' z = Some (KOCTE octe)"
    and  s'': "\<And>x. s'' x = (case (s x) of None \<Rightarrow> None | Some ko \<Rightarrow>
                    (case ko of CNode sz cs \<Rightarrow>
                          Some (CNode sz (\<lambda>y. if y \<in> dom cs \<and> cte_map (x, y) = z
                                              then Some cap else cs y))
                                    | _ \<Rightarrow> Some ko))"
     and rel: "cap_relation cap (cteCap cte')"
       shows  "pspace_relation s'' (s'(z \<mapsto> KOCTE cte'))"
proof -
  have funny_update_no_dom:
    "\<And>fun P v. dom (\<lambda>y. if y \<in> dom fun \<and> P y then Some v else fun y)
      = dom fun"
    by (rule set_eqI, simp add: domIff)

  have funny_update_well_formed_cnode:
    "\<And>sz fun P v.
      well_formed_cnode_n sz (\<lambda>y. if y \<in> dom fun \<and> P y then Some v else fun y)
      = well_formed_cnode_n sz fun"
    by (simp add: well_formed_cnode_n_def funny_update_no_dom)

  have obj_relation_cuts1:
  "\<And>ko x. obj_relation_cuts (the (case ko of CNode sz cs \<Rightarrow>
                                       Some (CNode sz (\<lambda>y. if y \<in> dom cs \<and> cte_map (x, y) = z
                                                           then Some cap else cs y))
                                    | _ \<Rightarrow> Some ko)) x
             = obj_relation_cuts ko x"
    by (simp split: Structures_A.kernel_object.split
               add: funny_update_well_formed_cnode funny_update_no_dom)

  have domEq[simp]:
    "dom s'' = dom s"
    using s''
    apply (intro set_eqI)
    apply (simp add: domIff split: option.split Structures_A.kernel_object.split)
    done

  have obj_relation_cuts2:
  "\<And>x. x \<in> dom s'' \<Longrightarrow> obj_relation_cuts (the (s'' x)) x = obj_relation_cuts (the (s x)) x"
    using s''
    by (clarsimp simp add: obj_relation_cuts1 dest!: domD)

  show ?thesis using ps octe
    apply (clarsimp simp add: pspace_relation_def dom_fun_upd2
                    simp del: dom_fun_upd split del: if_split)
    apply (rule conjI)
     apply (erule subst[where t="dom s'"])
     apply (simp add: pspace_dom_def obj_relation_cuts2)
    apply (simp add: obj_relation_cuts2)
    apply (rule ballI, drule(1) bspec)+
    apply clarsimp
    apply (intro conjI impI)
     apply (simp add: s'')
     apply (rule obj_relation_cutsE, assumption+, simp_all split: if_split_asm)[1]
     apply (clarsimp simp: cte_relation_def rel)
    apply (rule obj_relation_cutsE, assumption+, simp_all add: s'')
     apply (clarsimp simp: cte_relation_def)
    apply (clarsimp simp: is_other_obj_relation_type other_obj_relation_def
                   split: Structures_A.kernel_object.split_asm)
    done
qed

lemma set_cap_not_quite_corres_prequel[CSpace1_R_assms]:
  assumes cr:
  "pspace_relation (kheap s) (ksPSpace s')"
  "(x,t') \<in> fst (setCTE p' c' s')"
  "valid_objs s" "pspace_aligned s" "pspace_distinct s" "cte_at p s"
  "pspace_aligned' s'" "pspace_distinct' s'"
  assumes c: "cap_relation c (cteCap c')"
  assumes p: "p' = cte_map p"
  shows "\<exists>t. ((),t) \<in> fst (set_cap c p s) \<and>
             pspace_relation (kheap t) (ksPSpace t')"
  using cr
  apply (clarsimp simp: setCTE_def setObject_def in_monad split_def)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (elim disjE exE conjE)
   apply (clarsimp simp: lookupAround2_char1)
   apply (frule(5) cte_map_pulls_tcb_to_abstract[OF p])
    apply (simp add: domI)
   apply (frule tcb_cases_related2)
   apply (clarsimp simp: set_cap_def2 split_def bind_def get_object_def
                         simpler_gets_def assert_def fail_def return_def
                         set_object_def get_def put_def)
   apply (erule(2) pspace_relation_update_tcbs)
   apply (simp add: c)
  apply clarsimp
  apply (frule(5) cte_map_pulls_cte_to_abstract[OF p])
  apply (clarsimp simp: set_cap_def split_def bind_def get_object_def
                        simpler_gets_def assert_def a_type_def fail_def return_def
                        set_object_def get_def put_def domI)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_cs_def valid_cs_size_def exI)
  apply (rule conjI, clarsimp)
   apply (erule(1) pspace_relation_update_ctes[where cap=c])
    apply clarsimp
    apply (intro conjI impI)
     apply (rule ext, clarsimp simp add: domI p)
     apply (drule cte_map_inj_eq [OF _ _ cr(6) cr(3-5)])
      apply (simp add: cte_at_cases domI)
     apply (simp add: prod_eq_iff)
    apply (insert p)[1]
    apply (clarsimp split: option.split Structures_A.kernel_object.split
                    del: ext intro!: ext)
    apply (drule cte_map_inj_eq [OF _ _ cr(6) cr(3-5)])
     apply (simp add: cte_at_cases domI well_formed_cnode_invsI[OF cr(3)])
    apply clarsimp
   apply (simp add: c)
  apply (simp add: wf_cs_insert)
  done

(* FIXME: move *)
lemma pspace_relation_cte_wp_atI'[CSpace1_R_assms]:
  "\<lbrakk> pspace_relation (kheap s) (ksPSpace s');
     cte_wp_at' ((=) cte) x s'; valid_objs s \<rbrakk>
   \<Longrightarrow> \<exists>c slot. cte_wp_at ((=) c) slot s \<and> cap_relation c (cteCap cte) \<and> x = cte_map slot"
  apply (simp add: cte_wp_at_cases')
  apply (elim disjE conjE exE)
   apply (erule(1) pspace_dom_relatedE)
   apply (erule(1) obj_relation_cutsE, simp_all split: if_split_asm)[1]
   apply (intro exI, rule conjI[OF _ conjI [OF _ refl]])
    apply (simp add: cte_wp_at_cases domI well_formed_cnode_invsI)
   apply (simp split: if_split_asm)
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE, simp_all split: if_split_asm)
   apply (subgoal_tac "n = x - y", clarsimp)
    apply (drule tcb_cases_related2, clarsimp)
    apply (intro exI, rule conjI)
     apply (erule(1) cte_wp_at_tcbI[where t="(a, b)" for a b, simplified])
     apply fastforce
    apply simp
   apply clarsimp
  apply (simp add: other_obj_relation_def
            split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm)
  done

lemma same_region_as_final_matters[CSpace1_R_assms]:
  "\<lbrakk>same_region_as c c'; final_matters c\<rbrakk> \<Longrightarrow> final_matters c'"
  by (rule ccontr)
     (simp add: final_matters_def final_matters_arch_def cap_relation_split_asm
           split: cap.split_asm arch_cap.splits)

lemma same_region_as_arch_gen_refs[CSpace1_R_assms]:
  "\<lbrakk>same_region_as c c'; final_matters c \<rbrakk> \<Longrightarrow> arch_gen_refs c = arch_gen_refs c'"
  by (auto simp: final_matters_def cap_relation_split_asm is_cap_simps
           split: cap.split_asm arch_cap.splits)

lemma arch_same_region_aobj_ref[CSpace1_R_assms]:
  "\<lbrakk>arch_same_region_as ac ac'; final_matters_arch ac; final_matters_arch ac'\<rbrakk>
   \<Longrightarrow> aobj_ref ac = aobj_ref ac'"
   by (simp add: final_matters_arch_def split: AARCH64_A.arch_cap.splits)

lemma obj_refs_relation_Master[CSpace1_R_assms]:
  "cap_relation cap cap' \<Longrightarrow>
   obj_refs cap = (if capClass (capMasterCap cap') = PhysicalClass \<and> \<not> isUntypedCap (capMasterCap cap')
                   then {capUntypedPtr (capMasterCap cap')}
                   else {})"
  by (simp add: isCap_simps
         split: cap_relation_split_asm arch_cap.split_asm)

lemma arch_gen_refs_relation_Master:
  "cap_relation cap cap' \<Longrightarrow> arch_gen_refs cap = {}"
  by (simp split: cap_relation_split_asm arch_cap.split_asm)

lemma arch_gen_refs_cap_relation_Master_eq[CSpace1_R_assms]:
  "\<lbrakk>cap_relation c (cteCap cte); capMasterCap (cteCap cte') = capMasterCap (cteCap cte);
    cap_relation c' (cteCap cte')\<rbrakk>
   \<Longrightarrow> arch_gen_refs c = arch_gen_refs c'"
  by (simp split: cap_relation_split_asm arch_cap.split_asm)

lemma descendants_of_update_ztc:
  assumes c: "\<And>x. \<lbrakk> m \<turnstile> x \<rightarrow> slot; \<not> P \<rbrakk> \<Longrightarrow>
                  \<exists>cte'. m x = Some cte'
                    \<and> capMasterCap (cteCap cte') \<noteq> capMasterCap (cteCap cte)
                    \<and> sameRegionAs (cteCap cte') (cteCap cte)"
  assumes m: "m slot = Some cte"
  assumes z: "isZombie cap \<or> isCNodeCap cap \<or> isThreadCap cap"
  defines "cap' \<equiv> cteCap cte"
  assumes F: "\<And>x cte'. \<lbrakk> m x = Some cte'; x \<noteq> slot; P \<rbrakk>
               \<Longrightarrow> isUntypedCap (cteCap cte') \<or> capClass (cteCap cte') \<noteq> PhysicalClass
                    \<or> capUntypedPtr (cteCap cte') \<noteq> capUntypedPtr cap'"
  assumes pu: "capRange cap' = capRange cap \<and> capUntypedPtr cap' = capUntypedPtr cap"
  assumes a: "capAligned cap'"
  assumes t: "isZombie cap' \<or> isCNodeCap cap' \<or> isThreadCap cap'"
  assumes n: "no_loops m"
  defines "m' \<equiv> m(slot \<mapsto> cteCap_update (\<lambda>_. cap) cte)"
  shows "((c \<noteq> slot \<or> P) \<longrightarrow> descendants_of' c m \<subseteq> descendants_of' c m')
           \<and> (P \<longrightarrow> descendants_of' c m' \<subseteq> descendants_of' c m)"
proof (simp add: descendants_of'_def subset_iff,
       simp only: all_simps(6)[symmetric], intro conjI allI)
  note isMDBParentOf_CTE[simp]

  have utp: "capUntypedPtr cap' \<in> capRange cap'"
    using t a
    by (auto elim!: capAligned_capUntypedPtr simp: isCap_simps)

  have ztc_parent: "\<And>cap cap'. isZombie cap \<or> isCNodeCap cap \<or> isThreadCap cap
                            \<Longrightarrow> sameRegionAs cap cap'
                            \<Longrightarrow> capUntypedPtr cap = capUntypedPtr cap'
                                 \<and> capClass cap' = PhysicalClass \<and> \<not> isUntypedCap cap'"
    by (auto simp: isCap_simps sameRegionAs_def3)

  have ztc_child: "\<And>cap cap'. isZombie cap \<or> isCNodeCap cap \<or> isThreadCap cap
                            \<Longrightarrow> sameRegionAs cap' cap
                            \<Longrightarrow> capClass cap' = PhysicalClass \<and>
                                  (isUntypedCap cap' \<or> capUntypedPtr cap' = capUntypedPtr cap)"
    by (auto simp: gen_isCap_simps sameRegionAs_def3)

  have notparent: "\<And>x cte'. \<lbrakk> m x = Some cte'; x \<noteq> slot; P \<rbrakk>
                               \<Longrightarrow> \<not> isMDBParentOf cte cte'"
    using t utp
    apply clarsimp
    apply (drule_tac cte'=cte' in F, simp+)
    apply (simp add: cap'_def)
    apply (cases cte, case_tac cte', clarsimp)
    apply (frule(1) ztc_parent, clarsimp)
    done

  have notparent2: "\<And>x cte'. \<lbrakk> m x = Some cte'; x \<noteq> slot; P \<rbrakk>
                               \<Longrightarrow> \<not> isMDBParentOf (cteCap_update (\<lambda>_. cap) cte) cte'"
    using z utp
    apply clarsimp
    apply (drule_tac cte'=cte' in F, simp+)
    apply (cases cte, case_tac cte', clarsimp)
    apply (frule(1) ztc_parent)
    apply (clarsimp simp: pu)
    done

  fix x
  { assume cx: "m \<turnstile> c \<rightarrow> x" and cP: "c \<noteq> slot \<or> P"
    hence c_neq_x [simp]: "c \<noteq> x"
      by (clarsimp simp: n no_loops_no_subtree)
    from cx c_neq_x cP m
    have s_neq_c [simp]: "c \<noteq> slot"
      apply (clarsimp simp del: c_neq_x)
      apply (drule subtree_parent)
      apply (clarsimp simp: parentOf_def notparent)
      done

    have parent: "\<And>x cte'. \<lbrakk> m x = Some cte'; isMDBParentOf cte' cte; m \<turnstile> x \<rightarrow> slot; x \<noteq> slot \<rbrakk>
                                \<Longrightarrow> isMDBParentOf cte' (cteCap_update (\<lambda>_. cap) cte)"
      using t z pu
      apply -
      apply (cases P)
       apply (frule(2) F)
       apply (clarsimp simp: cap'_def)
       apply (case_tac cte')
       apply (rename_tac capability mdbnode)
       apply (case_tac cte)
       apply clarsimp
       apply (frule(1) ztc_child)
       apply (case_tac "isUntypedCap capability")
        apply (simp add: isCap_simps)
        apply (clarsimp simp: sameRegionAs_def3 isCap_simps)
       apply simp
      apply (frule(1) c, clarsimp)
      apply (clarsimp simp: cap'_def)
      apply (case_tac cte')
      apply (case_tac cte)
      apply clarsimp
      apply (erule sameRegionAsE)
         apply (clarsimp simp: sameRegionAs_def3 isCap_simps)+
      done

    from cx
    have "m' \<turnstile> c \<rightarrow> x"
    proof induct
      case (direct_parent c')
      hence "m \<turnstile> c \<rightarrow> c'" by (rule subtree.direct_parent)
      with direct_parent m
      show ?case
        apply -
        apply (rule subtree.direct_parent)
          apply (clarsimp simp add: mdb_next_unfold m'_def m)
         apply assumption
        apply (clarsimp simp: parentOf_def)
        apply (clarsimp simp add: m'_def)
        apply (erule(2) parent)
        apply simp
        done
    next
      case (trans_parent c' c'')
      moreover
      from trans_parent
      have "m \<turnstile> c \<rightarrow> c''" by - (rule subtree.trans_parent)
      ultimately
      show ?case using  z m pu t
        apply -
        apply (erule subtree.trans_parent)
          apply (clarsimp simp: mdb_next_unfold m'_def m)
         apply assumption
        apply (clarsimp simp: parentOf_def m'_def)
        apply (erule(2) parent)
        apply simp
        done
    qed
  }
    thus "(c = slot \<longrightarrow> P) \<longrightarrow> m \<turnstile> c \<rightarrow> x \<longrightarrow> m' \<turnstile> c \<rightarrow> x"
      by blast

  { assume subcx: "m' \<turnstile> c \<rightarrow> x" and P: "P"

    have mdb_next_eq: "\<And>x y. m' \<turnstile> x \<leadsto> y = m \<turnstile> x \<leadsto> y"
      by (simp add: mdb_next_unfold m'_def m)
    have mdb_next_eq_trans: "\<And>x y. m' \<turnstile> x \<leadsto>\<^sup>+ y = m \<turnstile> x \<leadsto>\<^sup>+ y"
      apply (rule arg_cong[where f="\<lambda>S. v \<in> S\<^sup>+" for v])
      apply (simp add: set_eq_iff mdb_next_eq)
      done

    have subtree_neq: "\<And>x y. m' \<turnstile> x \<rightarrow> y \<Longrightarrow> x \<noteq> y"
      apply clarsimp
      apply (drule subtree_mdb_next)
      apply (clarsimp simp: mdb_next_eq_trans n no_loops_trancl_simp)
      done

    have parent2: "\<And>x cte'. \<lbrakk> m x = Some cte'; isMDBParentOf cte' (cteCap_update (\<lambda>_. cap) cte);
                                         x \<noteq> slot \<rbrakk>
                                \<Longrightarrow> isMDBParentOf cte' cte"
      using t z pu P
      apply (drule_tac cte'=cte' in F, simp, simp)
      apply (simp add: cap'_def)
      apply (cases cte)
      apply (case_tac cte')
      apply (rename_tac cap' node')
      apply (clarsimp)
      apply (frule(1) ztc_child)
      apply (case_tac "isUntypedCap cap'")
       apply (simp add:isCap_simps)
       apply (clarsimp simp: isCap_simps sameRegionAs_def3)
      apply clarsimp
      done

    from subcx have "m \<turnstile> c \<rightarrow> x"
    proof induct
      case (direct_parent c')
      thus ?case
        using subtree_neq [OF subtree.direct_parent [OF direct_parent(1-3)]]
        apply -
        apply (rule subtree.direct_parent)
          apply (clarsimp simp: mdb_next_unfold m'_def m split: if_split_asm)
         apply assumption
        apply (insert z m t pu)
        apply (simp add: cap'_def)
        apply (simp add: m'_def parentOf_def split: if_split_asm)
         apply (clarsimp simp: parent2)
        apply (clarsimp simp add: notparent2 [OF _ _ P])
        done
    next
      case (trans_parent c' c'')
      thus ?case
        using subtree_neq [OF subtree.trans_parent [OF trans_parent(1, 3-5)]]
        apply -
        apply (erule subtree.trans_parent)
          apply (clarsimp simp: mdb_next_unfold m'_def m split: if_split_asm)
         apply assumption
        apply (insert z m t pu)
        apply (simp add: cap'_def)
        apply (simp add: m'_def parentOf_def split: if_split_asm)
         apply (clarsimp simp: parent2)
        apply (clarsimp simp: notparent2 [OF _ _ P])
        done
    qed
  }
    thus "P \<longrightarrow> m' \<turnstile> c \<rightarrow> x \<longrightarrow> m \<turnstile> c \<rightarrow> x"
      by simp
qed

lemma capRange_cap_relation[CSpace1_R_assms]:
  "\<lbrakk> cap_relation cap cap'; capClass cap' = PhysicalClass \<rbrakk>
   \<Longrightarrow> capRange cap' = {obj_ref_of cap .. obj_ref_of cap + obj_size cap - 1}"
  by (simp add: capRange_def objBits_simps' cte_level_bits_def
                asid_low_bits_def zbits_map_def word_size_bits_def pageBits_def
         split: cap_relation_split_asm arch_cap.split_asm
                option.split sum.split)

lemma obj_refs_cap_relation_untyped_ptr[CSpace1_R_assms]:
  "\<lbrakk> cap_relation cap cap'; obj_refs cap \<noteq> {} \<rbrakk> \<Longrightarrow> capUntypedPtr cap' \<in> obj_refs cap"
  by (clarsimp split: cap_relation_split_asm arch_cap.split_asm)

lemma ghost_relation_wrapper_same_concrete_set_cap[CSpace1_R_assms]:
  "\<lbrakk> ghost_relation_wrapper s c; ((), s') \<in> fst (set_cap cap src s) \<rbrakk>
   \<Longrightarrow> ghost_relation_wrapper s' c"
  by (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv data_at_def)

lemma revokable_plus_orderD[CSpace1_R_assms]:
  "\<lbrakk> isCapRevocable new old; (capBadge old, capBadge new) \<in> capBadge_ordering P;
     capMasterCap old = capMasterCap new \<rbrakk>
   \<Longrightarrow> (isUntypedCap new \<or> (\<exists>x. capBadge old = Some 0 \<and> capBadge new = Some x \<and> x \<noteq> 0))"
  by (clarsimp simp: Retype_H.isCapRevocable_def AARCH64_H.isCapRevocable_def isCap_simps
              split: if_split_asm capability.split_asm arch_capability.split_asm)

lemma valid_arch_badges_SMC:
  "valid_arch_badges (ArchObjectCap (SMCCap badge)) cap' node' =
   ((isArchSGISignalCap cap' \<longrightarrow> mdbFirstBadged node') \<and>
    (isArchSMCCap cap' \<longrightarrow> badge \<noteq> archSMCBadge cap' \<longrightarrow> archSMCBadge cap' \<noteq> 0 \<longrightarrow>
      mdbFirstBadged node'))"
  unfolding valid_arch_badges_def
  by (auto simp: isCap_simps)

lemma valid_badges_def2[CSpace1_R_assms]:
  "valid_badges m =
   (\<forall>p p' cap node cap' node'.
    m p = Some (CTE cap node) \<longrightarrow>
    m p' = Some (CTE cap' node') \<longrightarrow>
    m \<turnstile> p \<leadsto> p' \<longrightarrow>
    (capMasterCap cap = capMasterCap cap' \<longrightarrow>
     capBadge cap \<noteq> None \<longrightarrow>
     capBadge cap \<noteq> capBadge cap' \<longrightarrow>
     capBadge cap' \<noteq> Some 0 \<longrightarrow>
     mdbFirstBadged node') \<and>
    valid_arch_badges cap cap' node')"
  apply (simp add: valid_badges_def)
  apply (intro arg_cong[where f=All] ext imp_cong [OF refl])
  apply (case_tac cap; clarsimp simp: gen_isCap_simps)
       apply (fastforce simp: sameRegionAs_def3 isCap_simps)+
  apply (rename_tac acap node)
  apply (case_tac acap; simp)
  apply (auto simp: isCap_simps valid_arch_badges_SMC)
  done

lemma capRange_SMC[simp]:
  "capRange (ArchObjectCap (SMCCap smc_badge)) = {}"
  by (simp add: capRange_def)

lemma is_cap_revocable_eq[CSpace1_R_assms]:
  "\<lbrakk> cap_relation c c'; cap_relation src_cap src_cap'; sameRegionAs src_cap' c';
     is_untyped_cap src_cap \<longrightarrow> \<not> is_ep_cap c \<and> \<not> is_ntfn_cap c\<rbrakk>
   \<Longrightarrow> is_cap_revocable c src_cap = isCapRevocable c' src_cap'"
  apply (clarsimp simp: isCap_simps objBits_simps bit_simps arch_is_cap_revocable_def
                        bits_of_def is_cap_revocable_def Retype_H.isCapRevocable_def
                        sameRegionAs_def3 isCapRevocable_def
                 split: cap_relation_split_asm arch_cap.split_asm)
  done

lemmas use_update_ztc_one_descendants[CSpace1_R_assms] =
  use_update_ztc_one[OF AARCH64.descendants_of_update_ztc, simplified]

lemma is_derived'_genD[CSpace1_R_assms]:
  "is_derived' m p cap' cap \<Longrightarrow>
   cap' \<noteq> NullCap \<and>
   \<not> isZombie cap \<and>
   \<not> isIRQControlCap cap' \<and>
   badge_derived' cap' cap \<and>
   (isUntypedCap cap \<longrightarrow> descendants_of' p m = {}) \<and>
   (isReplyCap cap = isReplyCap cap') \<and>
   (isReplyCap cap \<longrightarrow> capReplyMaster cap) \<and>
   (isReplyCap cap' \<longrightarrow> \<not> capReplyMaster cap')"
  by (simp add: AARCH64.is_derived'_def)

lemma acap_relation_capBadge[CSpace1_R_assms]:
  "acap_relation acap acap' \<Longrightarrow> arch_capBadge acap' = arch_cap_badge acap"
  by (cases acap; simp)

end (* Arch *)

interpretation CSpace1_R?: CSpace1_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact CSpace1_R_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems CSpace1_R_2_assms

lemma weak_derived_updateCapData:
  "\<lbrakk> updateCapData P x c \<noteq> NullCap; weak_derived' c c';
     capBadge (updateCapData P x c) = capBadge c' \<rbrakk>
  \<Longrightarrow> weak_derived' (updateCapData P x c) c'"
  apply (clarsimp simp add: weak_derived'_def updateCapData_Master)
  apply (clarsimp elim: impE dest!: iffD1[OF updateCapData_Reply])
  apply (clarsimp simp: gen_isCap_simps)
  apply (clarsimp simp: Let_def gen_isCap_simps global.updateCapData_def)
  done

lemma updateMDB_pspace_relation[CSpace1_R_2_assms]:
  assumes "(x, s'') \<in> fst (updateMDB p f s')"
  assumes "pspace_relation (kheap s) (ksPSpace s')"
  assumes "pspace_aligned' s'" "pspace_distinct' s'"
  shows "pspace_relation (kheap s) (ksPSpace s'')" using assms
  apply (clarsimp simp: updateMDB_def Let_def in_monad split: if_split_asm)
  apply (drule_tac P="(=) s'" in use_valid [OF _ getCTE_sp], rule refl)
  apply clarsimp
  apply (clarsimp simp: setCTE_def setObject_def in_monad
                        split_def)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (elim disjE conjE exE)
   apply (clarsimp simp: cte_wp_at_cases' lookupAround2_char1)
   apply (erule disjE)
    apply (clarsimp simp: tcb_ctes_clear cte_level_bits_def objBits_defs)
   apply clarsimp
   apply (rule pspace_dom_relatedE, assumption+)
   apply (rule obj_relation_cutsE, assumption+;
          clarsimp split: Structures_A.kernel_object.split_asm
                          AARCH64_A.arch_kernel_obj.split_asm if_split_asm
                    simp: other_obj_relation_def)
   apply (frule(1) tcb_cte_cases_aligned_helpers(1))
   apply (frule(1) tcb_cte_cases_aligned_helpers(2))
   apply (clarsimp simp del: diff_neg_mask)
   apply (subst map_upd_triv[symmetric, where t="kheap s"], assumption)
   apply (erule(2) pspace_relation_update_tcbs)
   apply (case_tac tcba)
   apply (simp add: tcb_cte_cases_def tcb_relation_def del: diff_neg_mask
             split: if_split_asm)
  apply (clarsimp simp: cte_wp_at_cases')
  apply (erule disjE)
   apply (rule pspace_dom_relatedE, assumption+)
   apply (rule obj_relation_cutsE, assumption+, simp_all split: if_split_asm)[1]
   apply (clarsimp simp: cte_relation_def)
   apply (simp add: pspace_relation_def dom_fun_upd2
               del: dom_fun_upd)
   apply (erule conjE)
   apply (rule ballI, drule(1) bspec)
   apply (rule ballI, drule(1) bspec)
   apply clarsimp
   apply (rule obj_relation_cutsE, assumption+, simp_all split: if_split_asm)[1]
   apply (clarsimp simp: cte_relation_def)
  apply clarsimp
  apply (drule_tac y=p in tcb_ctes_clear[rotated], assumption+)
   apply fastforce
  apply fastforce
  done

lemma master_cap_relation:
  "\<lbrakk> cap_relation c c'; cap_relation d d' \<rbrakk> \<Longrightarrow>
   (capMasterCap c' = capMasterCap d') = (cap_master_cap c = cap_master_cap d)"
  by (auto simp add: cap_master_cap_def capMasterCap_def up_ucast_inj_eq
           split: cap.splits arch_cap.splits)

lemma cap_asid_cap_relation:
  "cap_relation c c' \<Longrightarrow> capASID c' = map_option ucast (cap_asid c)"
  by (auto simp: capASID_def cap_asid_def split: cap.splits arch_cap.splits option.splits)

lemma is_derived_eq[CSpace1_R_2_assms]:
  "\<lbrakk> cap_relation c c'; cap_relation d d';
     cdt_relation (swp cte_at s) (cdt s) (ctes_of s'); cte_at p s \<rbrakk> \<Longrightarrow>
   is_derived (cdt s) p c d = is_derived' (ctes_of s') (cte_map p) c' d'"
  unfolding cdt_relation_def
  apply (erule allE, erule impE, simp)
  apply (clarsimp simp: is_derived_def is_derived'_def badge_derived'_def)
  apply (rule conjI)
   apply (clarsimp simp: is_cap_simps isCap_simps)
   apply (cases c, auto simp: isCap_simps cap_master_cap_def capMasterCap_def)[1]
  apply (cases "isIRQControlCap d'")
   apply (frule(1) master_cap_relation)
   apply (clarsimp simp: isCap_simps cap_master_cap_def
                         is_zombie_def is_reply_cap_def is_master_reply_cap_def
                  split: cap_relation_split_asm arch_cap.split_asm)[1]
  apply (frule(1) master_cap_relation)
  apply (frule(1) cap_badge_relation)
  apply (frule cap_asid_cap_relation)
  apply (frule(1) capBadge_ordering_relation)
  apply (case_tac d)
             apply (simp_all add: isCap_simps is_cap_simps cap_master_cap_def
                                  capMasterCap_def
                           split: cap_relation_split_asm arch_cap.split_asm)
      apply fastforce
     by (auto simp: up_ucast_inj_eq split:arch_cap.splits arch_capability.splits option.splits)

lemma isMDBParentOf_eq_parent:
  "\<lbrakk> isMDBParentOf c cte;
     weak_derived' (cteCap c) (cteCap c');
     mdbRevocable (cteMDBNode c') = mdbRevocable (cteMDBNode c) \<rbrakk>
  \<Longrightarrow> isMDBParentOf c' cte"
  apply (cases c)
  apply (cases c')
  apply (cases cte)
  apply clarsimp
  apply (clarsimp simp: weak_derived'_def isMDBParentOf_CTE)
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps)
  done

lemma isMDBParentOf_eq_child:
  "\<lbrakk> isMDBParentOf cte c;
     weak_derived' (cteCap c) (cteCap c');
     mdbFirstBadged (cteMDBNode c') = mdbFirstBadged (cteMDBNode c) \<rbrakk>
  \<Longrightarrow> isMDBParentOf cte c'"
  apply (cases c)
  apply (cases c')
  apply (cases cte)
  apply clarsimp
  apply (clarsimp simp: weak_derived'_def isMDBParentOf_CTE)
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps)
  done

lemma isMDBParentOf_eq[CSpace1_R_2_assms]:
  "\<lbrakk> isMDBParentOf c d;
     weak_derived' (cteCap c) (cteCap c');
     mdbRevocable (cteMDBNode c') = mdbRevocable (cteMDBNode c);
     weak_derived' (cteCap d) (cteCap d');
     mdbFirstBadged (cteMDBNode d') = mdbFirstBadged (cteMDBNode d) \<rbrakk>
   \<Longrightarrow> isMDBParentOf c' d'"
  by (drule (2) isMDBParentOf_eq_parent)
     (erule (2) isMDBParentOf_eq_child)

lemma derived_sameRegionAs:
  "\<lbrakk> is_derived' m p cap' cap; s \<turnstile>' cap' \<rbrakk>
   \<Longrightarrow> sameRegionAs cap cap'"
  unfolding is_derived'_def badge_derived'_def
  apply (simp add: sameRegionAs_def3)
  apply (cases "isUntypedCap cap \<or> isArchFrameCap cap")
   apply (rule disjI2, rule disjI1)
   apply (erule disjE)
    apply (clarsimp simp: isCap_simps valid_cap'_def capAligned_def
                          is_aligned_no_overflow capRange_def
                   split: capability.splits arch_capability.splits option.splits)
   apply (clarsimp simp: isCap_simps valid_cap'_def capAligned_def
                         is_aligned_no_overflow capRange_def arch_capMasterCap_def
                  split: capability.splits arch_capability.splits option.splits)
  apply (clarsimp simp: isCap_simps valid_cap'_def
                        is_aligned_no_overflow capRange_def vs_cap_ref_arch'_def
                 split: capability.splits arch_capability.splits option.splits)
  done

lemma is_derived_maskedAsFull[simp]:
  "is_derived' m slot c (maskedAsFull src_cap' a) = is_derived' m slot c src_cap'"
  apply (clarsimp simp: maskedAsFull_def isCap_simps split:if_splits)
  apply (case_tac c)
             apply (clarsimp simp: is_derived'_def isCap_simps badge_derived'_def)+
  done

lemma maskedAsFull_revokable:
  "is_derived' x y c' src_cap' \<Longrightarrow>
   isCapRevocable c' (maskedAsFull src_cap' a) = isCapRevocable c' src_cap'"
  apply (case_tac src_cap'; simp add: maskedAsFull_def isCap_simps)
  apply (case_tac c'; clarsimp simp: maskedAsFull_def is_derived'_def isCap_simps badge_derived'_def
                                     Retype_H.isCapRevocable_def AARCH64_H.isCapRevocable_def
                               split: arch_capability.splits if_splits)
  done

lemma sameRegionAs_SGISignalCap2[simp]:
  "sameRegionAs cap (ArchObjectCap (SGISignalCap irq target)) =
   (cap = IRQControlCap \<or> cap = ArchObjectCap (SGISignalCap irq target))"
  by (auto simp: global.sameRegionAs_def AARCH64_H.sameRegionAs_def isCap_simps
                 isIRQControlCapDescendant_def
           split: if_splits)

lemma arch_mdb_preservation_refl[simp, intro!, CSpace1_R_2_assms]:
  "arch_mdb_preservation cap cap"
  by (simp add: arch_mdb_preservation_def)

lemma arch_mdb_preservation_sym[CSpace1_R_2_assms]:
  "arch_mdb_preservation cap cap' = arch_mdb_preservation cap' cap"
  by (auto simp: arch_mdb_preservation_def)

lemma arch_mdb_preservation_non_arch:
  "\<lbrakk> \<not>isArchObjectCap cap; \<not>isArchObjectCap cap' \<rbrakk> \<Longrightarrow> arch_mdb_preservation cap cap'"
  by (simp add: arch_mdb_preservation_def isCap_simps)

lemma arch_mdb_preservation_Untyped[simp, CSpace1_R_2_assms]:
  "arch_mdb_preservation (UntypedCap d p sz idx) (UntypedCap d' p' sz' idx')"
  by (simp add: arch_mdb_preservation_non_arch isCap_simps)

lemma parentOf_preserve_oneway[CSpace1_R_2_assms]:
  assumes dom: "\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:
    "\<And>x cte cte'. \<lbrakk>m x = Some cte; m' x = Some cte'\<rbrakk> \<Longrightarrow>
                     sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte') \<and>
                     (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes misc:
    "\<And>x cte cte'. \<lbrakk>m x =Some cte;m' x = Some cte'\<rbrakk> \<Longrightarrow>
                     isUntypedCap (cteCap cte) = isUntypedCap (cteCap cte') \<and>
                     isNotificationCap (cteCap cte)  = isNotificationCap (cteCap cte') \<and>
                     (isNotificationCap (cteCap cte) \<longrightarrow> capNtfnBadge (cteCap cte) =
                                                         capNtfnBadge (cteCap cte')) \<and>
                     (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte')) \<and>
                     (isEndpointCap (cteCap cte) \<longrightarrow> capEPBadge (cteCap cte) =
                                                     capEPBadge (cteCap cte')) \<and>
                     arch_mdb_preservation (cteCap cte) (cteCap cte') \<and>
                     cteMDBNode cte = cteMDBNode cte'"
  assumes node:"\<And>p. mdb_next m p = mdb_next m' p"
  shows "m \<turnstile> p parentOf x \<Longrightarrow> m'  \<turnstile> p parentOf x"
  supply if_split[split del]
  apply (clarsimp simp: parentOf_def)
  apply (frule iffD1[OF dom, OF domI])
  apply (frule iffD1[OF dom[where x = p], OF domI])
  apply clarsimp
  apply (frule_tac x1=p in conjunct1[OF sameRegion])
   apply assumption
  apply (frule_tac x1=x in conjunct2[OF sameRegion])
   apply assumption
  apply (drule_tac x="cteCap y" in fun_cong)
  apply (drule_tac x="cteCap cte'" in fun_cong)
  apply (drule_tac x=p in misc)
   apply assumption
  apply (drule_tac x=x in misc)
   apply assumption
  apply ((simp only: isMDBParentOf_def isArchMDBParentOf_def2 split_def
               split: cte.splits if_split_asm); clarsimp)
    apply (clarsimp simp: global.sameRegionAs_def isCap_simps Let_def)
   apply (clarsimp simp: global.sameRegionAs_def isCap_simps Let_def)
  apply (clarsimp simp: arch_mdb_preservation_def split: if_splits)
  apply blast
  done

lemma mdb_chunked_preserve_oneway[CSpace1_R_2_assms]:
  assumes dom: "\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes sameRegion:
    "\<And>x cte cte'.
       \<lbrakk> m x = Some cte; m' x = Some cte'\<rbrakk> \<Longrightarrow>
           cteMDBNode cte = cteMDBNode cte'
         \<and> arch_mdb_preservation (cteCap cte) (cteCap cte')
         \<and> sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
         \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes node: "\<And>p. mdb_next m p = mdb_next m' p"
  shows "mdb_chunked m \<Longrightarrow> mdb_chunked m'"
  apply (clarsimp simp:mdb_chunked_def)
  apply (drule_tac x=p in spec)
  apply (drule_tac x=p' in spec)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply (frule iffD2[OF dom,OF domI],rotate_tac)
  apply clarsimp
  apply (case_tac ya)
  apply (case_tac y)
  apply (frule_tac x = p in sameRegion,assumption)
  apply (frule_tac x = p' in sameRegion,assumption)
  apply clarsimp
  apply (erule impE)
   apply (drule fun_cong)+
   apply fastforce
  apply (subgoal_tac "m \<turnstile> p \<leadsto>\<^sup>+ p' = m' \<turnstile> p \<leadsto>\<^sup>+ p'")
   apply (subgoal_tac "m \<turnstile> p' \<leadsto>\<^sup>+ p = m' \<turnstile> p' \<leadsto>\<^sup>+ p")
    apply (frule_tac m = m and x = p and c = cap and p = p and p'=p'
                     in is_chunk_preserve[rotated -1])
        apply (simp add:dom)
       apply (simp add: sameRegion)
      apply simp+
      apply (rule node)
     apply assumption
    apply (frule_tac x = p' and c = cap' and p = p' and p'=p in is_chunk_preserve[rotated -1])
        apply (rule dom)
       apply (simp add: sameRegion)
      apply (rule node)
     apply assumption
    apply (clarsimp simp: mdb_chunked_arch_assms_def arch_mdb_preservation_def)
   apply (rule connect_eqv_singleE)
   apply (clarsimp simp:mdb_next_rel_def node)
  apply (rule connect_eqv_singleE)
  apply (clarsimp simp:mdb_next_rel_def node)
  done

lemma valid_badges_preserve_oneway[CSpace1_R_2_assms]:
  assumes dom: "\<And>x. (x \<in> dom m) = (x \<in> dom m')"
  assumes misc:
    "\<And>x cte cte'.
       \<lbrakk> m x =Some cte; m' x = Some cte'\<rbrakk> \<Longrightarrow>
           isNotificationCap (cteCap cte)  = isNotificationCap (cteCap cte')
         \<and> (isNotificationCap (cteCap cte) \<longrightarrow> capNtfnBadge (cteCap cte) = capNtfnBadge (cteCap cte'))
         \<and> (isEndpointCap (cteCap cte) = isEndpointCap (cteCap cte'))
         \<and> (isEndpointCap (cteCap cte) \<longrightarrow> capEPBadge (cteCap cte) = capEPBadge (cteCap cte'))
         \<and> arch_mdb_preservation (cteCap cte) (cteCap cte')
         \<and> isIRQHandlerCap (cteCap cte) = isIRQHandlerCap (cteCap cte')
         \<and> isIRQControlCap (cteCap cte) = isIRQControlCap (cteCap cte')
         \<and> cteMDBNode cte = cteMDBNode cte'"
  assumes sameRegion:
    "\<And>x cte cte'. \<lbrakk> m x = Some cte; m' x = Some cte' \<rbrakk> \<Longrightarrow>
                        sameRegionAs (cteCap cte) = sameRegionAs (cteCap cte')
                     \<and> (\<lambda>x. sameRegionAs x (cteCap cte)) = (\<lambda>x. sameRegionAs x (cteCap cte'))"
  assumes mdb_next: "\<And>p. mdb_next m p = mdb_next m' p"
  shows "valid_badges m \<Longrightarrow> valid_badges m'"
  apply (clarsimp simp:valid_badges_def)
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p' in spec)
  apply (frule iffD2[OF dom,OF domI], rotate_tac)
  apply (frule iffD2[OF dom,OF domI], rotate_tac)
  apply clarsimp
  apply (rename_tac cte cte', case_tac cte, case_tac cte')
  apply (rename_tac m_cap m_node m_cap' m_node')
  apply clarsimp
  apply (erule impE)
   apply (simp add: mdb_next mdb_next_rel_def)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (erule impE)
    apply (drule(1) sameRegion)+
    apply clarsimp
    apply (drule fun_cong)+
    apply fastforce
   apply (drule(1) misc)+
   apply (clarsimp simp: isCap_simps global.sameRegionAs_def split: if_splits)
  apply (clarsimp simp: valid_arch_badges_def)
  apply (drule(1) misc)+
  apply (clarsimp simp: arch_mdb_preservation_def)
  done

(* corresponds to safe_parent_for_arch in AInvs, used by safe_parent_for' *)
definition
  "safe_parent_for_arch' m cap parent \<equiv>
     parent = IRQControlCap \<and> isArchSGISignalCap cap"

definition is_simple_cap' :: "capability \<Rightarrow> bool" where
  "is_simple_cap' cap \<equiv>
     cap \<noteq> NullCap \<and>
     cap \<noteq> IRQControlCap \<and>
     \<not> isUntypedCap cap \<and>
     \<not> isReplyCap cap \<and>
     \<not> isEndpointCap cap \<and>
     \<not> isNotificationCap cap \<and>
     \<not> isThreadCap cap \<and>
     \<not> isCNodeCap cap \<and>
     \<not> isZombie cap \<and>
     \<not> isArchFrameCap cap \<and>
     \<not> isArchSMCCap cap"

end (* Arch *)

interpretation CSpace1_R_2?: CSpace1_R_2
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact CSpace1_R_2_assms)?))
qed

(* needed to prove dest_no_parent_n in Arch, then export to mdb_insert_der *)
locale Arch_mdb_insert_der = mdb_insert_der + Arch

(*The newly inserted cap should never have children.*)
lemma (in Arch_mdb_insert_der) dest_no_parent_n:
  "n \<turnstile> dest \<rightarrow> p = False"
  using src partial_is_derived' valid_badges ut_rev
  apply clarsimp
  apply (erule subtree.induct)
   prefer 2
   apply simp
  apply (clarsimp simp: parentOf_def mdb_next_unfold n_dest new_dest_def n)
  apply (cases "mdbNext src_node = dest")
   apply (subgoal_tac "m \<turnstile> src \<leadsto> dest")
    apply simp
   apply (subst mdb_next_unfold)
   apply (simp add: src)
  apply (case_tac "isUntypedCap src_cap")
  apply (clarsimp simp: gen_isCap_simps AARCH64.isMDBParentOf_CTE is_derived'_def
                        badge_derived'_def freeIndex_update_def capMasterCap_def
                 split: capability.splits)
   apply (simp add: ut_revocable'_def)
   apply (drule spec[where x=src], simp add: gen_isCap_simps)
   apply (simp add: descendants_of'_def)
   apply (drule spec[where x="mdbNext src_node"])
   apply (erule notE, rule direct_parent)
     apply (simp add: mdb_next_unfold)
    apply simp
   apply (simp add: parentOf_def src isMDBParentOf_CTE isCap_simps
              cong: sameRegionAs_update_untyped)
  apply (clarsimp simp: isMDBParentOf_CTE is_derived'_def badge_derived'_def)
  apply (drule(2) revokable_plus_orderD)
  apply (erule sameRegionAsE, simp_all)
     apply (simp add: valid_badges_def2)
     apply (erule_tac x=src in allE)
     apply (erule_tac x="mdbNext src_node" in allE)
     apply (clarsimp simp: src mdb_next_unfold)
     apply (case_tac "capBadge cap'", simp_all)
    apply (clarsimp simp add: gen_isCap_simps capMasterCap_def
                    simp del: not_ex
                       split: capability.splits)
   apply (clarsimp simp: isCap_simps)+
  done

(* requalify dest_no_parent_n back into mdb_insert_der *)
context mdb_insert_der begin

interpretation Arch_mdb_insert_der by unfold_locales

lemmas dest_no_parent_n = dest_no_parent_n

end

locale Arch_mdb_insert_sib = mdb_insert_sib + Arch

context Arch_mdb_insert_sib begin

(* If dest is inserted as sibling, src can not have had children.
   If it had had children, then dest_node which is just a derived copy
   of src_node would be a child as well. *)
lemma src_no_mdb_parent:
  "isMDBParentOf (CTE src_cap src_node) cte = False"
  using no_child partial_is_derived'
  apply clarsimp
  apply (case_tac cte)
  apply (clarsimp simp: isMDBParentOf_CTE is_derived'_def badge_derived'_def)
  apply (erule sameRegionAsE)
     apply (clarsimp simp add: sameRegionAs_def3)
     subgoal by (cases src_cap; auto simp: capMasterCap_def arch_capMasterCap_def Retype_H.isCapRevocable_def AARCH64_H.isCapRevocable_def
                                           freeIndex_update_def isCap_simps
                                       split: capability.split_asm arch_capability.split_asm) (* long *)
    apply (clarsimp simp: isCap_simps sameRegionAs_def3 capMasterCap_def freeIndex_update_def
       split:capability.splits arch_capability.splits)
   apply (clarsimp simp: isCap_simps sameRegionAs_def3 freeIndex_update_def
                         capRange_def split:capability.splits
               simp del: Int_atLeastAtMost atLeastAtMost_iff)
   apply auto[1]
  apply (clarsimp simp: isCap_simps sameRegionAs_def3)+
  done

lemma parent_preserved:
  "isMDBParentOf cte (CTE src_cap src_node) \<Longrightarrow> isMDBParentOf cte new_dest"
  using partial_is_derived'
  apply (cases cte)
  apply (case_tac "isUntypedCap src_cap")
   apply (clarsimp simp:isCap_simps isMDBParentOf_CTE freeIndex_update_def new_dest_def)
   apply (clarsimp simp:is_derived'_def isCap_simps badge_derived'_def capMasterCap_def split:capability.splits)
   apply (clarsimp simp:sameRegionAs_def2 capMasterCap_def isCap_simps split:capability.splits)
  apply (clarsimp simp: isMDBParentOf_CTE)
  apply (clarsimp simp: new_dest_def)
  apply (rename_tac cap node)
  apply (clarsimp simp: is_derived'_def badge_derived'_def)
  apply (rule conjI)
   apply (simp add: sameRegionAs_def2)
  apply (cases "isCapRevocable c' src_cap")
   apply simp
   apply (drule(2) revokable_plus_orderD)
   apply (erule disjE)
     apply (clarsimp simp: isCap_simps)
     by ((fastforce elim: capBadge_ordering_trans simp: isCap_simps)+)

lemma not_untyped:
  "capAligned c' \<Longrightarrow> \<not>isUntypedCap src_cap"
  using no_child partial_is_derived' ut_rev src
  apply (clarsimp simp: ut_revocable'_def isMDBParentOf_CTE)
  apply (erule_tac x=src in allE)
  apply simp
  apply (clarsimp simp: is_derived'_def freeIndex_update_def isCap_simps capAligned_def
                        badge_derived'_def)
  apply (clarsimp simp: sameRegionAs_def3 capMasterCap_def arch_capMasterCap_def
                        gen_isCap_simps is_aligned_no_overflow
                  split: capability.splits)
  done

end (* Arch_mdb_insert_sib *)

(* requalify src_no_mdb_parent+parent_preserved back into mdb_insert_sib *)
context mdb_insert_sib begin

interpretation Arch_mdb_insert_sib by unfold_locales

lemmas src_no_mdb_parent = src_no_mdb_parent
lemmas parent_preserved = parent_preserved
lemmas not_untyped = not_untyped

end

context Arch begin arch_global_naming

named_theorems CSpace1_R_3_assms

lemmas [CSpace1_R_3_assms] =
  is_derived_maskedAsFull derived_sameRegionAs maskedAsFull_revokable
  mdb_insert_der.dest_no_parent_n
  mdb_insert_sib.src_no_mdb_parent mdb_insert_sib.parent_preserved

end

interpretation CSpace1_R_3?: CSpace1_R_3
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact CSpace1_R_3_assms)?))
qed

locale Arch_masterCap = Arch + masterCap
begin

lemma isArchFrameCap[simp]:
  "isArchFrameCap cap' = isArchFrameCap cap" using master
  by (simp add: capMasterCap_def arch_capMasterCap_def isArchFrameCap_def
           del: isNull isDomain
           split: capability.splits arch_capability.splits)

lemma isArchSGISignalCap[simp]:
  "isArchSGISignalCap cap' = isArchSGISignalCap cap" using master
  by (simp add: capMasterCap_def arch_capMasterCap_def isCap_simps
           del: isNull isDomain
           split: capability.splits arch_capability.splits)

lemma capRange[simp]:
  "capRange cap' = capRange cap" using master
  by (simp add: capRange_def capMasterCap_def arch_capMasterCap_def
           del: isNull isDomain
           split: capability.splits arch_capability.splits)

lemma sameRegionAs1:
  "sameRegionAs c cap' = sameRegionAs c cap" using master
  by (simp add: sameRegionAs_def3)

lemma sameRegionAs2:
  "sameRegionAs cap' c = sameRegionAs cap c" using master
  by (simp add: sameRegionAs_def3)

lemma capBadgeNone:
  "(capBadge cap' = None) = (capBadge cap = None)"
  using master
  apply (clarsimp simp: capBadge_def)
  apply (clarsimp simp: isCap_simps capMasterCap_def capMasterCap_ArchObjectCap
                  split: capability.splits)
  apply (clarsimp simp: arch_capMasterCap_def split: arch_capability.splits)
  done

lemmas sameRegionAs[simp] = sameRegionAs1 sameRegionAs2

lemma isMDBParentOf1:
  assumes "capBadge cap = None"
  shows "isMDBParentOf c (CTE cap' m) = isMDBParentOf c (CTE cap m)"
proof -
  from assms
  have "capBadge cap' = None"
    by (auto simp: capBadgeNone)
  with assms
  show ?thesis
    by (cases c, clarsimp simp add: isMDBParentOf_CTE)
qed

lemma isMDBParentOf2:
  assumes "capBadge cap = None"
  shows "isMDBParentOf (CTE cap' m) c = isMDBParentOf (CTE cap m) c"
proof -
  from assms
  have "capBadge cap' = None"
    by (auto simp: capBadgeNone)
  with assms
  show ?thesis
    by (cases c, simp add: isMDBParentOf_CTE)
qed

lemmas isMDBParentOf = isMDBParentOf1 isMDBParentOf2

end (* Arch_masterCap *)

end
