(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchKHeap_R
imports
  KHeap_R
begin

context Arch begin arch_global_naming

named_theorems KHeap_R_assms

lemma getObject_inv_vcpu[wp]:
  "\<lbrace>P\<rbrace> getObject l \<lbrace>\<lambda>_::ArchStructures_H.vcpu. P\<rbrace>"
  apply (rule getObject_inv)
  apply simp
  apply (rule loadObject_default_inv)
  done

lemmas typ_at_to_obj_at_arches
  = typ_at_to_obj_at'[where 'a=pte, simplified]
    typ_at_to_obj_at'[where 'a=asidpool, simplified]
    typ_at_to_obj_at'[where 'a=user_data, simplified]
    typ_at_to_obj_at'[where 'a=user_data_device, simplified]
    typ_at_to_obj_at'[where 'a=vcpu, simplified]

lemmas page_table_at_obj_at'
  = page_table_at'_def[unfolded typ_at_to_obj_at_arches]

lemma no_fail_getObject_vcpu[wp]:
  "no_fail (vcpu_at' vcpu) (getObject vcpu :: vcpu kernel)"
  supply lookupAround2_same1[simp del]
  apply (simp add: getObject_def split_def)
  apply wp
  apply (clarsimp simp add: obj_at'_def objBits_simps typ_at_to_obj_at_arches
                      cong: conj_cong option.case_cong)
  apply (rule ps_clear_lookupAround2; assumption?)
    apply simp
   apply (erule is_aligned_no_overflow)
  apply clarsimp
  done

lemma vcpu_at_ko:
  "typ_at (AArch AVCPU) p s \<Longrightarrow> \<exists>vcpu. ko_at (ArchObj (arch_kernel_obj.VCPU vcpu)) p s "
  by (clarsimp simp add: obj_at_def)

 (* If we ever copy this: consider lifting Haskell precondition to \<top> here first. Not strictly
    necessary since the rest of the proofs manage to lift later, but might be more convenient
    for new proofs. *)
lemma getObject_vcpu_corres:
  "corres vcpu_relation (vcpu_at vcpu) (vcpu_at' vcpu)
                        (get_vcpu vcpu) (getObject vcpu)"
  apply (simp add: getObject_def get_vcpu_def get_object_def split_def)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
    apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
   apply (case_tac ko; simp)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object, simp_all)[1]
   apply (clarsimp simp: lookupAround2_known1)
   apply (clarsimp simp: obj_at'_def objBits_simps)
   apply (erule (1) ps_clear_lookupAround2)
     apply simp
    apply (erule is_aligned_no_overflow)
   apply simp
   apply (clarsimp simp: objBits_simps split: option.split)
  apply (clarsimp simp: in_monad loadObject_default_def)
  apply (simp add: bind_assoc exec_gets gets_map_def assert_opt_def fail_def split: option.split)
  apply (drule vcpu_at_ko)
  apply (clarsimp simp: obj_at_def in_omonad)
  apply (simp add: return_def)
  apply (simp add: in_magnitude_check objBits_simps pageBits_def)
  apply (frule in_inv_by_hoareD [OF magnitudeCheck_inv])
  apply (clarsimp simp: state_relation_def pspace_relation_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: other_aobj_relation_def)
  done

lemma koType_objBitsKO[KHeap_R_assms]:
  "koTypeOf k = koTypeOf k' \<Longrightarrow> objBitsKO k = objBitsKO k'"
  by (auto simp: objBitsKO_def archObjSize_def
          split: kernel_object.splits arch_kernel_object.splits)

lemma pspace_dom_update[KHeap_R_assms]:
  "\<lbrakk> ps ptr = Some x; a_type x = a_type v \<rbrakk> \<Longrightarrow> pspace_dom (ps(ptr \<mapsto> v)) = pspace_dom ps"
  apply (simp add: pspace_dom_def dom_fun_upd2 del: dom_fun_upd)
  apply (rule SUP_cong [OF refl])
  apply clarsimp
  apply (simp add: obj_relation_cuts_def3)
  done

lemma cte_wp_at_ctes_of[KHeap_R_assms]:
  "cte_wp_at' P p s = (\<exists>cte. ctes_of s p = Some cte \<and> P cte)"
  supply diff_neg_mask[simp del]
  apply (simp add: cte_wp_at_cases' map_to_ctes_def Let_def
                   cte_level_bits_def objBits_simps'
          split del: if_split)
  apply (safe del: disjCI)
    apply (clarsimp simp: ps_clear_def3 field_simps)
   apply (clarsimp simp: ps_clear_def3 field_simps
              split del: if_split)
   apply (frule is_aligned_sub_helper)
    apply (clarsimp simp: tcb_cte_cases_def cteSizeBits_def split: if_split_asm)
   apply (case_tac "n = 0")
    apply (clarsimp simp: field_simps)
   apply (subgoal_tac "ksPSpace s p = None")
    apply clarsimp
    apply (clarsimp simp: field_simps)
   apply (elim conjE)
   apply (subst(asm) mask_in_range, assumption)
   apply (drule arg_cong[where f="\<lambda>S. p \<in> S"])
   apply (simp add: dom_def field_simps)
   apply (erule mp)
   apply (rule ccontr, simp add: linorder_not_le)
   apply (drule word_le_minus_one_leq)
   apply clarsimp
   apply (simp add: field_simps)
  apply (clarsimp split: if_split_asm del: disjCI)
   apply (simp add: ps_clear_def3 field_simps)
  apply (rule disjI2, rule exI[where x="(p - (p && ~~ mask tcb_bits))"])
  apply (clarsimp simp: ps_clear_def3[where na=tcb_bits] is_aligned_mask add_ac
                        word_bw_assocs)
  done

lemma ctes_of_canonical[KHeap_R_assms]:
  assumes canonical: "pspace_canonical' s"
  assumes ctes_of: "ctes_of s p = Some cte"
  shows "canonical_address p"
proof -
  from ctes_of have "cte_wp_at' ((=) cte) p s"
    by (simp add: cte_wp_at_ctes_of)
  thus ?thesis using canonical canonical_bit_def
    by (fastforce simp: pspace_canonical'_def tcb_cte_cases_def field_simps objBits_defs take_bit_Suc
                 split: if_splits
                  elim: cte_wp_atE' canonical_address_add)
qed

lemma valid_updateCapDataI[KHeap_R_assms]:
  "s \<turnstile>' c \<Longrightarrow> s \<turnstile>' updateCapData b x c"
  unfolding global.updateCapData_def Let_def updateCapData_def
  by (cases c, auto simp: gen_isCap_defs valid_cap'_def global.capUntypedPtr_def gen_isCap_simps
                          capAligned_def word_size word_bits_def word_bw_assocs
                    split: capability.splits arch_capability.splits)

lemma obj_relation_cut_same_type:
  "\<lbrakk> (y, P) \<in> obj_relation_cuts ko x; P ko z;
     (y', P') \<in> obj_relation_cuts ko' x'; P' ko' z \<rbrakk>
     \<Longrightarrow> (a_type ko = a_type ko')
         \<or> (\<exists>n n'. a_type ko = ACapTable n \<and> a_type ko' = ACapTable n')
         \<or> (\<exists>sz sz'. a_type ko = AArch (AUserData sz) \<and> a_type ko' = AArch (AUserData sz'))
         \<or> (\<exists>sz sz'. a_type ko = AArch (ADeviceData sz) \<and> a_type ko' = AArch (ADeviceData sz'))
         \<or> (\<exists>pt_t pt_t'. a_type ko = AArch (APageTable pt_t) \<and> a_type ko' = AArch (APageTable pt_t'))"
  apply (rule ccontr)
  apply (simp add: obj_relation_cuts_def2 a_type_def)
  apply (auto simp: other_obj_relation_def tcb_relation_cut_def cte_relation_def pte_relation_def
                    other_aobj_relation_def
             split: Structures_A.kernel_object.split_asm if_split_asm
                    Structures_H.kernel_object.split_asm
                    arch_kernel_obj.split_asm arch_kernel_object.split_asm)
  done

lemmas obj_at_simps = gen_obj_at_simps is_other_obj_relation_type_def
                      objBits_simps pageBits_def

lemma setObject_other_corres:
  fixes ob' :: "'a :: pspace_storable"
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
  assumes P: "\<And>v::'a::pspace_storable. (1 :: machine_word) < 2 ^ objBits v"
  assumes a: "\<not> is_ArchObj ob"
  shows      "other_obj_relation ob (injectKO (ob' :: 'a :: pspace_storable)) \<Longrightarrow>
  corres dc (obj_at (\<lambda>ko. a_type ko = a_type ob) ptr and obj_at (same_caps ob) ptr)
            (obj_at' (P :: 'a \<Rightarrow> bool) ptr)
            (set_object ptr ob) (setObject ptr ob')"
  supply image_cong_simp [cong del] projectKOs[simp del]
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply wp
    apply (rule x)
   apply (clarsimp simp: b elim!: obj_at'_weakenE)
  apply (unfold set_object_def setObject_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                        put_def return_def modify_def get_object_def x
                        projectKOs obj_at_def
                        updateObject_default_def in_magnitude_check [OF _ P])
  apply (rename_tac ko)
  apply (clarsimp simp add: state_relation_def z)
  apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                            swp_def fun_upd_def obj_at_def)
  apply (subst conj_assoc[symmetric])
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x=ptr in allE)+
   apply (clarsimp simp: obj_at_def a_type_def
                   split: Structures_A.kernel_object.splits if_split_asm)
   apply (simp split: arch_kernel_obj.splits if_splits)
  apply (fold fun_upd_def)
  apply (simp only: pspace_relation_def pspace_dom_update dom_fun_upd2 simp_thms)
  apply (elim conjE)
  apply (frule bspec, erule domI)
  apply (prop_tac "typ_at' (koTypeOf (injectKO ob')) ptr b")
   subgoal
     by (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def projectKO_opts_defs
                        a_type_def other_obj_relation_def a
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        kernel_object.split_asm)
  apply (insert a)
  apply (frule a_type_eq_is_ArchObj)
  apply clarsimp
  apply (rule conjI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: is_other_obj_relation_type t a)
   apply (drule(1) bspec)
   apply clarsimp
   apply (frule_tac ko'=ko and x'=ptr in obj_relation_cut_same_type,
           (fastforce simp add: is_other_obj_relation_type t)+)
   apply (insert t)
   apply ((erule disjE
          | clarsimp simp: is_other_obj_relation_type is_other_obj_relation_type_def a_type_def)+)[1]
  \<comment> \<open>ready_queues_relation\<close>
  apply (prop_tac "koTypeOf (injectKO ob') \<noteq> TCBT")
   subgoal
     by (clarsimp simp: other_obj_relation_def; cases ob; cases "injectKO ob'";
         simp)
  by (fastforce dest: tcbs_of'_non_tcb_update)

(* analogous to setObject_other_corres, but for arch objects *)
lemma setObject_other_arch_corres:
  fixes ob' :: "'a :: pspace_storable"
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
  assumes e: "\<And>ko. P ko \<Longrightarrow> exst_same' (injectKO ko) (injectKO ob')"
  assumes P: "\<And>v::'a::pspace_storable. (1 :: machine_word) < 2 ^ objBits v"
  assumes a: "is_ArchObj ob"
  shows      "other_aobj_relation ob (injectKO (ob' :: 'a :: pspace_storable)) \<Longrightarrow>
  corres dc (obj_at (\<lambda>ko. a_type ko = a_type ob) ptr and obj_at (same_caps ob) ptr)
            (obj_at' (P :: 'a \<Rightarrow> bool) ptr)
            (set_object ptr ob) (setObject ptr ob')"
  supply image_cong_simp [cong del] projectKOs[simp del]
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply wp
    apply (rule x)
   apply (clarsimp simp: b elim!: obj_at'_weakenE)
  apply (unfold set_object_def setObject_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                        put_def return_def modify_def get_object_def x
                        projectKOs obj_at_def
                        updateObject_default_def in_magnitude_check [OF _ P])
  apply (rename_tac ko)
  apply (clarsimp simp add: state_relation_def z)
  apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                            swp_def fun_upd_def obj_at_def)
  apply (subst conj_assoc[symmetric])
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x=ptr in allE)+
   apply (clarsimp simp: obj_at_def a_type_def
                   split: Structures_A.kernel_object.splits if_split_asm)
   apply (simp split: arch_kernel_obj.splits if_splits)
  apply (fold fun_upd_def)
  apply (simp only: pspace_relation_def pspace_dom_update dom_fun_upd2 simp_thms)
  apply (elim conjE)
  apply (frule bspec, erule domI)
  apply (prop_tac "is_ArchObj ko", clarsimp simp: a dest!: a_type_eq_is_ArchObj)
  apply (prop_tac "typ_at' (koTypeOf (injectKO ob')) ptr b")
   subgoal
     by (clarsimp simp: typ_at'_def ko_wp_at'_def obj_at'_def projectKO_opts_defs
                        is_other_obj_relation_type_def a_type_def other_aobj_relation_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm kernel_object.split_asm
                        arch_kernel_object.split_asm)
  apply clarsimp
  apply (rule conjI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: is_other_obj_relation_type t a)
   apply (drule(1) bspec)
   apply clarsimp
   apply (frule_tac ko'=ko and x'=ptr in obj_relation_cut_same_type)
   apply ((fastforce simp add: is_other_obj_relation_type t)+)[3] (* loops when folded into above *)
   apply (insert t)
   apply ((erule disjE
          | clarsimp simp: is_other_obj_relation_type is_other_obj_relation_type_def a_type_def)+)[1]
  \<comment> \<open>ready_queues_relation\<close>
  apply (prop_tac "koTypeOf (injectKO ob') \<noteq> TCBT")
   subgoal
     by (clarsimp simp: other_aobj_relation_def; cases ob; cases "injectKO ob'";
         simp split: arch_kernel_obj.split_asm)
  by (fastforce dest: tcbs_of'_non_tcb_update)

lemmas [KHeap_R_assms] =
  setObject_other_corres[where 'a=endpoint]
  setObject_other_corres[where 'a=notification]

lemma dmo_storeWordVM' [simp]:
  "doMachineOp (storeWordVM x y) = return ()"
  by (simp add: storeWordVM_def)

(* only on arches without kernel mappings *)
lemma pspace_in_kernel_mappings'_wp[wp]:
  "\<lbrace>\<top>\<rbrace> f \<lbrace>\<lambda>_. pspace_in_kernel_mappings'\<rbrace>"
  unfolding pspace_in_kernel_mappings'_def
  by wp

lemma setEndpoint_pspace_in_kernel_mappings'[KHeap_R_assms]:
  "setEndpoint p ko \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  by wp

lemma setNotification_pspace_in_kernel_mappings'[KHeap_R_assms]:
  "setNotification p ko \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  by wp

(* interface lemma, but can't be done via locale *)
lemma setObject_pspace_in_kernel_mappings':
  "setObject p ko \<lbrace>pspace_in_kernel_mappings'\<rbrace>"
  by wp

(* interface lemma, but can't be done via locale *)
lemma valid_global_refs_lift':
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (ctes_of s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ctes_of s)\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  assumes idle: "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  assumes irqn: "\<And>P. \<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> f \<lbrace>\<lambda>_ s. P (irq_node' s)\<rbrace>"
  assumes maxObj: "\<And>P. \<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace> f \<lbrace>\<lambda>_ s. P (gsMaxObjectSize s)\<rbrace>"
  shows "\<lbrace>valid_global_refs'\<rbrace> f \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_refs'_def global_refs'_def valid_cap_sizes'_def)
  apply (rule hoare_lift_Pf [where f="ksArchState"])
   apply (rule hoare_lift_Pf [where f="ksIdleThread"])
    apply (rule hoare_lift_Pf [where f="irq_node'"])
     apply (rule hoare_lift_Pf [where f="gsMaxObjectSize"])
      apply (wp ctes hoare_vcg_const_Ball_lift arch idle irqn maxObj)+
  done

lemma valid_arch_state_lift':
  assumes typs: "\<And>T p P. f \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace>"
  assumes arch: "\<And>P. f \<lbrace>\<lambda>s. P (ksArchState s)\<rbrace>"
  assumes vcpu: "\<And>P p. f \<lbrace>\<lambda>s. P (ko_wp_at' (is_vcpu' and hyp_live') p s)\<rbrace>"
  shows "f \<lbrace>valid_arch_state'\<rbrace>"
  apply (simp add: valid_arch_state'_def valid_asid_table'_def vspace_table_at'_defs)
  apply (wp_pre, wps arch)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_const_imp_lift vcpu[unfolded pred_conj_def]
                 split: option.split)
  apply (clarsimp simp: pred_conj_def)
  done

lemma set_ntfn_hyp[wp]:
  "setNotification ptr val \<lbrace>\<lambda>s. P (ko_wp_at' (is_vcpu' and hyp_live') p s)\<rbrace>"
  unfolding setNotification_def
  by (wpsimp wp: setObject_ko_wp_at simp: gen_objBits_simps, rule refl, simp)
     (clarsimp simp: is_vcpu'_def ko_wp_at'_def obj_at'_def)

lemma set_ep_hyp[wp]:
  "setEndpoint ptr val \<lbrace>\<lambda>s. P (ko_wp_at' (is_vcpu' and hyp_live') p s)\<rbrace>"
  unfolding setEndpoint_def
  by (wpsimp wp: setObject_ko_wp_at simp: objBits_simps', rule refl, simp)
     (clarsimp simp: is_vcpu'_def ko_wp_at'_def obj_at'_def)

lemma idle_is_global[KHeap_R_assms, intro!]:
  "ksIdleThread s \<in> global_refs' s"
  by (simp add: global_refs'_def)

end

interpretation KHeap_R?: KHeap_R
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact KHeap_R_assms)?)
qed

context Arch begin arch_global_naming

named_theorems KHeap_R_assms_2

lemmas setEndpoint_valid_globals[KHeap_R_assms_2, wp]
  = valid_global_refs_lift'[OF set_ep_ctes_of set_ep_arch'
                               setEndpoint_it setEndpoint_ksInterruptState]

lemma set_ntfn_global_refs'[KHeap_R_assms_2, wp]:
  "\<lbrace>valid_global_refs'\<rbrace> setNotification ptr val \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  by (rule valid_global_refs_lift'; wp)

crunch setEndpoint, setNotification
  for valid_arch'[wp]: valid_arch_state'
  (wp: valid_arch_state_lift')

lemmas [KHeap_R_assms_2] = setEndpoint_valid_arch' setNotification_valid_arch'

lemmas setObject_typ_ats[wp] = typ_at_lifts[OF setObject_typ_at']

lemmas doMachineOp_typ_ats[wp] = typ_at_lifts[OF doMachineOp_typ_at']

lemmas setEndpoint_typ_ats[wp] = typ_at_lifts[OF setEndpoint_typ_at']

end

interpretation KHeap_R_2?: KHeap_R_2
proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact KHeap_R_assms_2)?)
qed

(* requalify interface lemmas which can't be locale assumptions due to free type variable *)
arch_requalify_facts
  setObject_other_corres
  setObject_pspace_in_kernel_mappings'
  valid_global_refs_lift'

end
