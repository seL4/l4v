theory New_R
imports
  "$L4V_ARCH/Refine"
  "$L4V_ARCH/RAB_FN"
  "$L4V_ARCH/EmptyFail_H"
  "$L4V_ARCH/Init_R"
begin

context begin interpretation Arch .
lemma getObject_cinv_lift[wp, simp]:
  "\<lbrace>P\<rbrace> getObject p \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P and (\<lambda>s. isInDomainColour (ksCurDomain s) p)\<rbrace> getObjectInCurDomain p \<lbrace>Q\<rbrace>"
  apply (simp add: getObject_def getObjectInCurDomain_def)
apply wpsimp
oops

lemma setObject_cinv_lift[wp, simp]:
  "\<lbrace>P\<rbrace> setObject p v \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P and (\<lambda>s. isInDomainColour (ksCurDomain s) p)\<rbrace> setObjectInCurDomain p v \<lbrace>Q\<rbrace>"
  apply (simp add: setObject_def setObjectInCurDomain_def)
apply wpsimp
oops

lemma no_fail_setObjectInCurDomain_other [wp]:
  fixes ob :: "'a :: pspace_storable"
  assumes x: "updateObject ob = updateObject_default ob"
  shows "no_fail (obj_at' (\<lambda>k::'a. objBits k = objBits ob) ptr and (\<lambda>s. isInDomainColour (ksCurDomain s) ptr))
                  (setObjectInCurDomain ptr ob)"
  apply (simp add: setObjectInCurDomain_def x split_def updateObject_default_def
                   projectKO_def2 alignCheck_def alignError_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp: is_aligned_mask[symmetric] obj_at'_def
                        objBits_def[symmetric] project_inject lookupAround2_known1)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (erule is_aligned_get_word_bits)
    apply (subst add_diff_eq[symmetric])
    apply (erule is_aligned_no_wrap')
    apply simp
   apply simp
  apply fastforce
  done

lemma no_fail_setObject_tcb [wp]:
  "no_fail (tcb_at' t and (\<lambda>s. isInDomainColour (ksCurDomain s) t)) (setObjectInCurDomain t (t'::tcb))"
  apply (rule no_fail_pre, wp)
   apply (rule ext)+
   apply simp
  apply (simp add: objBits_simps)
  done

lemma setObjectInCurDomain_update_TCB_corres':
  assumes tcbs: "tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb'"
  assumes tables: "\<forall>(getF, v) \<in> ran tcb_cap_cases. getF new_tcb = getF tcb"
  assumes tables': "\<forall>(getF, v) \<in> ran tcb_cte_cases. getF new_tcb' = getF tcb'"
  assumes sched_pointers: "tcbSchedPrev new_tcb' = tcbSchedPrev tcb'"
                          "tcbSchedNext new_tcb' = tcbSchedNext tcb'"
  assumes flag: "\<And>d p. inQ d p new_tcb' = inQ d p tcb'"
  assumes r: "r () ()"
  shows
    "corres r
       (ko_at (TCB tcb) ptr) (ko_at' tcb' ptr and (\<lambda>s. isInDomainColour (ksCurDomain s) ptr))
       (set_object ptr (TCB new_tcb)) (setObjectInCurDomain ptr new_tcb')"
  apply (rule_tac F="tcb_relation tcb tcb'" in corres_req)
   apply (clarsimp simp: state_relation_def obj_at_def obj_at'_def)
   apply (frule(1) pspace_relation_absD)
   apply (clarsimp simp: tcb_relation_cut_def)
  apply (rule corres_no_failI)
   apply wp
   apply (clarsimp simp: obj_at'_def)
  apply (unfold set_object_def setObjectInCurDomain_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                        put_def return_def modify_def get_object_def obj_at_def
                        updateObject_default_def in_magnitude_check objBits_less_word_bits)
  apply (rename_tac s s' ko)
  apply (prop_tac "ko = tcb'")
   apply (clarsimp simp: obj_at'_def project_inject)
  apply (clarsimp simp: state_relation_def)
  apply (prop_tac "map_to_ctes ((ksPSpace s') (ptr \<mapsto> injectKO new_tcb'))
                   = map_to_ctes (ksPSpace s')")
   apply (frule_tac tcb=new_tcb' and tcb=tcb' in map_to_ctes_upd_tcb)
     apply (clarsimp simp: objBits_simps)
    apply (clarsimp simp: objBits_simps ps_clear_def3 field_simps objBits_defs mask_def)
   apply (insert tables')[1]
   apply (rule ext)
   subgoal by auto
  apply (prop_tac "obj_at (same_caps (TCB new_tcb)) ptr s")
   using tables
   apply (fastforce simp: obj_at_def)
  apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update swp_def fun_upd_def
                        obj_at_def assms)
  apply (subst conj_assoc[symmetric])
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp: ghost_relation_def)
   apply (erule_tac x=ptr in allE)+
   apply clarsimp
  apply (extract_conjunct \<open>match conclusion in "pspace_relation _ _" \<Rightarrow> -\<close>)
   apply (fold fun_upd_def)
   apply (simp only: pspace_relation_def simp_thms
                     pspace_dom_update[where x="kernel_object.TCB _"
                                         and v="kernel_object.TCB _",
                                       simplified a_type_def, simplified])
   using assms
   apply (simp only: dom_fun_upd2 simp_thms)
   apply (elim conjE)
   apply (frule bspec, erule domI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: project_inject tcb_relation_cut_def
                  split: if_split_asm kernel_object.split_asm)
   apply (rename_tac aa ba)
   apply (drule_tac x="(aa, ba)" in bspec, simp)
   apply clarsimp
   apply (frule_tac ko'="kernel_object.TCB tcb" and x'=ptr in obj_relation_cut_same_type)
      apply (simp add: tcb_relation_cut_def)+
   apply clarsimp
  apply (insert sched_pointers flag)
  apply (clarsimp simp: ready_queues_relation_def Let_def)
  apply (prop_tac "(tcbSchedNexts_of s')(ptr := tcbSchedNext new_tcb') = tcbSchedNexts_of s'")
   apply (fastforce simp: opt_map_def)
  apply (prop_tac "(tcbSchedPrevs_of s')(ptr := tcbSchedPrev new_tcb') = tcbSchedPrevs_of s'")
   apply (fastforce simp: opt_map_def)
  by (clarsimp simp: ready_queue_relation_def opt_pred_def opt_map_def split: option.splits)

lemma setObjectInCurDomain_update_TCB_corres:
  "\<lbrakk>tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb';
     \<forall>(getF, v) \<in> ran tcb_cap_cases. getF new_tcb = getF tcb;
     \<forall>(getF, v) \<in> ran tcb_cte_cases. getF new_tcb' = getF tcb';
     tcbSchedPrev new_tcb' = tcbSchedPrev tcb'; tcbSchedNext new_tcb' = tcbSchedNext tcb';
     \<And>d p. inQ d p new_tcb' = inQ d p tcb';
     r () ()\<rbrakk> \<Longrightarrow>
   corres r
     (\<lambda>s. get_tcb ptr s = Some tcb) ((\<lambda>s'. (tcb', s') \<in> fst (getObject ptr s'))and (\<lambda>s. isInDomainColour (ksCurDomain s) ptr))
     (set_object ptr (TCB new_tcb)) (setObjectInCurDomain ptr new_tcb')"
  apply (rule corres_guard_imp)
    apply (erule (4) setObjectInCurDomain_update_TCB_corres')
   apply (clarsimp simp: getObject_def in_monad split_def obj_at'_def
                         loadObject_default_def objBits_simps' in_magnitude_check)+
  done

lemma setObjectInCurDomain_other_corres:
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
  assumes P: "\<And>(v::'a::pspace_storable). 0 < objBits v"
  shows      "other_obj_relation ob (injectKO (ob' :: 'a :: pspace_storable)) \<Longrightarrow>
  corres dc (obj_at (\<lambda>ko. a_type ko = a_type ob) ptr and obj_at (same_caps ob) ptr)
            (obj_at' (P :: 'a \<Rightarrow> bool) ptr and (\<lambda>s. isInDomainColour (ksCurDomain s) ptr))
            (set_object ptr ob) (setObjectInCurDomain ptr ob')"
  supply image_cong_simp [cong del] projectKOs[simp del]
  apply (rule corres_no_failI)
   apply (rule no_fail_pre)
    apply wp
    apply (rule x)
   apply (clarsimp simp: b elim!: obj_at'_weakenE)
  apply (unfold set_object_def setObjectInCurDomain_def)
  apply (clarsimp simp: in_monad split_def bind_def gets_def get_def Bex_def
                        put_def return_def modify_def get_object_def x
                        projectKOs obj_at_def
                        updateObject_default_def in_magnitude_check[OF _ P])
  apply (rename_tac ko)
  apply (clarsimp simp add: state_relation_def z)
  apply (clarsimp simp add: caps_of_state_after_update cte_wp_at_after_update
                            swp_def fun_upd_def obj_at_def)
  apply (subst conj_assoc[symmetric])
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
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
                        is_other_obj_relation_type_def a_type_def other_obj_relation_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm kernel_object.split_asm
                        arch_kernel_object.split_asm)
  apply clarsimp
  apply (rule conjI)
   apply (rule ballI, drule(1) bspec)
   apply (drule domD)
   apply (clarsimp simp: is_other_obj_relation_type t)
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
         simp split: arch_kernel_obj.split_asm)
  by (fastforce dest: tcbs_of'_non_tcb_update)

term "state_relation"
term "pspace_relation"
term "obj_relation_cuts"


lemma getObjectInCurDomain_inv:
  assumes x: "\<And>p q n ko. \<lbrace>P\<rbrace> loadObject p q n ko \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> getObjectInCurDomain p \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  by (simp add: getObjectInCurDomain_def split_def | wp x)+

lemma getObjectInCurDomain_inv_tcb [wp]: "\<lbrace>P\<rbrace> getObjectInCurDomain l \<lbrace>\<lambda>(rv :: Structures_H.tcb). P\<rbrace>"
  apply (rule getObjectInCurDomain_inv)
  apply simp
  apply (rule loadObject_default_inv)
  done

lemma no_fail_getObject_tcb [wp]:
  "no_fail (tcb_at' t) (getObject t :: tcb kernel)"
  apply (simp add: getObject_def split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp add: obj_at'_def objBits_simps'
                      cong: conj_cong)
  apply (rule ps_clear_lookupAround2, assumption+)
    apply simp
   apply (simp add: field_simps)
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (fastforce split: option.split_asm simp: objBits_simps')
  done
sorry

lemma no_fail_getObjectInCurDomain_tcb [wp]:
  "no_fail (tcb_at' t and (\<lambda>s. isInDomainColour (ksCurDomain s) t)) (getObjectInCurDomain t :: tcb kernel)"
  apply (simp add: getObjectInCurDomain_def split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp add: obj_at'_def objBits_simps'
                      cong: conj_cong)
  apply (rule ps_clear_lookupAround2, assumption+)
    apply simp
   apply (simp add: field_simps)
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (rule conjI)
  apply (fastforce split: option.split_asm simp: objBits_simps')
  apply (rule conjI)
   apply (metis Some_to_the prod.sel(1))
  apply (rule exI)
  apply (rule conjI)
  apply (fastforce split: option.split_asm simp: objBits_simps')
  sorry

lemma corres_get_tcb_inCurDomain:
  "corres (tcb_relation \<circ> the) (tcb_at t) (tcb_at' t and (\<lambda>s. isInDomainColour (ksCurDomain s) t)) (gets (get_tcb t)) (getObjectInCurDomain t)"
    apply (rule corres_no_failI)
   apply wp
  apply (clarsimp simp add: gets_def get_def return_def bind_def get_tcb_def)
  apply (frule in_inv_by_hoareD [OF getObjectInCurDomain_inv_tcb])
  apply (clarsimp simp add: obj_at_def is_tcb obj_at'_def projectKO_def
                            projectKO_opt_tcb split_def
                            getObjectInCurDomain_def loadObject_default_def in_monad)
  apply (case_tac bb)
   apply (simp_all add: fail_def return_def)
  apply (clarsimp simp add: state_relation_def pspace_relation_def)
  apply (drule bspec)
   apply clarsimp
   apply blast
  apply (clarsimp simp: tcb_relation_cut_def lookupAround2_known1)
  done

lemma getObject_TCB_corres:
  "corres tcb_relation (tcb_at t and pspace_aligned and pspace_distinct) \<top>
          (gets_the (get_tcb t)) (getObjectInCurDomain t)"
  apply (rule corres_cross_over_guard[where Q="tcb_at' t and (\<lambda>s. isInDomainColour (ksCurDomain s) t)"])
   defer
  apply (rule corres_guard_imp)
    apply (rule corres_gets_the)
    apply (rule corres_get_tcb_inCurDomain)
   apply (simp add: tcb_at_def)
  apply assumption
  apply (simp add: state_relation_def)
  apply (rule conjI)
   apply (fastforce simp: tcb_at_cross)
  apply (fastforce simp: tcb_at_cross state_relation_def)
  done
  sorry

end
end