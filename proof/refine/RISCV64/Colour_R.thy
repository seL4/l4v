(*
 * Copyright 2026, UNSW (ABN 57 195 873 179)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Colour_R
imports
  "$L4V_ARCH/Refine"
  "$L4V_ARCH/RAB_FN"
  "$L4V_ARCH/EmptyFail_H"
  "$L4V_ARCH/Init_R"
  "AInvs.ColourInv_AI"
begin

axiomatization colourOracle :: "domain \<Rightarrow> obj_ref set"
  where oracle_corres: "colourOracle d = colour_oracle d"

context begin interpretation Arch .

section \<open>Colour Oracle Defn + Lemma\<close>

definition isInDomainColour' :: "domain \<Rightarrow> machine_word \<Rightarrow> bool"
  where "isInDomainColour' d p \<equiv> p \<in> colourOracle d"

lemma colour_invariant_isInDomColour':
  "\<lbrakk>(s, s')\<in>state_relation; ptr \<in> colour_oracle (cur_domain s)\<rbrakk> \<Longrightarrow> isInDomainColour' (ksCurDomain s') ptr"
  by (simp add: isInDomainColour'_def oracle_corres curdomain_relation)

section \<open>Modified Method Defns\<close>

consts' getObjectColoured :: "machine_word \<Rightarrow> ('a :: pspace_storable) kernel"
defs getObjectColoured_def:
"getObjectColoured ptr \<equiv> do
        stateAssert (\<lambda>s. isInDomainColour' (ksCurDomain s) ptr) [];
        getObject ptr
od"

consts' setObjectColoured :: "machine_word \<Rightarrow> ('a :: pspace_storable) \<Rightarrow> unit kernel"
defs setObjectColoured_def:
"setObjectColoured ptr val\<equiv> do
        stateAssert (\<lambda>s. isInDomainColour' (ksCurDomain s) ptr) [];
        setObject ptr val
od"

consts' getCTEColoured :: "machine_word \<Rightarrow> cte kernel"
defs getCTEColoured_def:
"getCTEColoured \<equiv> getObjectColoured"

consts' threadSetInCurDomain :: "(tcb \<Rightarrow> tcb) \<Rightarrow> machine_word \<Rightarrow> unit kernel"
defs threadSetInCurDomain_def:
"threadSetInCurDomain f tptr \<equiv> do
   stateAssert (\<lambda>s. isInDomainColour' (ksCurDomain s) tptr) [];
   threadSet f tptr
od"

section \<open>Modified lemmas for methods\<close>

lemma getObjectColoured_inv [wp]:
  assumes x: "\<And>p q n ko. \<lbrace>P\<rbrace> loadObject p q n ko \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> getObjectColoured p \<lbrace>\<lambda>(rv :: 'a :: pspace_storable). P\<rbrace>"
  by (simp add: getObjectColoured_def split_def | wp x getObject_inv)+

lemma getObjectColoured_inv_tcb [wp]:
  "\<lbrace>P\<rbrace> getObjectColoured l \<lbrace>\<lambda>(rv :: Structures_H.tcb). P\<rbrace>"
  apply (rule getObjectColoured_inv)
  apply simp
  apply (rule loadObject_default_inv)
  done

lemma no_fail_getObjectColoured_tcb [wp]:
  "no_fail (tcb_at' t and (\<lambda>s. isInDomainColour' (ksCurDomain s) t)) (getObjectColoured t :: tcb kernel)"
  apply (simp add: getObjectColoured_def split_def)
  apply (rule no_fail_pre)
   apply wp
  apply (rule no_fail_stateAssert)
  by (clarsimp simp add: obj_at'_def objBits_simps'
                      cong: conj_cong)

lemma no_fail_setObjectColoured_other [wp]:
  fixes ob :: "'a :: pspace_storable"
  assumes x: "updateObject ob = updateObject_default ob"
  shows "no_fail (obj_at' (\<lambda>k::'a. objBits k = objBits ob) ptr and (\<lambda>s. isInDomainColour' (ksCurDomain s) ptr))
                  (setObjectColoured ptr ob)"
  apply (simp add: setObjectColoured_def x split_def updateObject_default_def
                   projectKO_def2 alignCheck_def alignError_def)
  apply (rule no_fail_pre)
   apply wp
  apply (clarsimp simp: is_aligned_mask[symmetric] obj_at'_def
                        objBits_def[symmetric] project_inject lookupAround2_known1 x)
  apply (rule stateAssert_inv)
apply (rule no_fail_stateAssert)
  by simp

lemma no_fail_setObject_tcb [wp]:
  "no_fail (tcb_at' t and (\<lambda>s. isInDomainColour' (ksCurDomain s) t)) (setObjectColoured t (t'::tcb))"
  apply (rule no_fail_pre, wp)
   apply (rule ext)+
   apply simp
  apply (simp add: objBits_simps)
  done

lemma no_fail_getCTE_inCurDomain [wp]:
  "no_fail (cte_at' p and (\<lambda>s. isInDomainColour' (ksCurDomain s) p)) (getCTEColoured p)"
  apply (simp add: getCTEColoured_def getObjectColoured_def split_def
                   loadObject_cte alignCheck_def unless_def
                   alignError_def is_aligned_mask[symmetric]
             cong: kernel_object.case_cong)
  apply (rule no_fail_pre, (wp | wpc)+)
  apply (clarsimp simp: cte_wp_at'_def getObject_def
                        loadObject_cte split_def in_monad
                 dest!: in_singleton
             split del: if_split)
  apply (clarsimp simp: in_monad typeError_def objBits_simps
                        magnitudeCheck_def
                 split: kernel_object.split_asm if_split_asm option.split_asm
             split del: if_split)
  apply auto (* simp+ satisfies the non-domain-colour subgoals *)
  done
sorry

lemma getCTE_inv_inCurDomain [wp]: "\<lbrace>P\<rbrace> getCTEColoured addr \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: getCTEColoured_def)
  apply (simp add: loadObject_cte)
  apply (case_tac ko)
  apply safe
  by wpsimp+

lemma getObject_cte_inv_inCurDomain [wp]: "\<lbrace>P\<rbrace> (getObjectColoured addr :: cte kernel) \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: getObjectColoured_def loadObject_cte split_def)
  by wpsimp

lemma getObject_cte_det_inCurDomain: (* TODO: update cte_wp_at' to use curDomain version of getObject *)
  "(r::cte,s') \<in> fst (getObjectColoured p s) \<Longrightarrow> fst (getObject p s) = {(r,s)} \<and> s' = s"
  apply (clarsimp simp add: getObjectColoured_def bind_def get_def gets_def
                            return_def loadObject_cte split_def)
  apply (clarsimp split: kernel_object.split_asm if_split_asm option.split_asm
                   simp: in_monad typeError_def alignError_def magnitudeCheck_def)
       apply (simp_all add: bind_def return_def assert_opt_def split_def
                            alignCheck_def is_aligned_mask[symmetric]
                            unless_def when_def magnitudeCheck_def)
  done
sorry (* broken for same reason as no_fail - need restriction on domains being aligned *)

lemma getCTE_cte_wp_at_inCurDomain:
  "\<lbrace>\<top>\<rbrace> getCTEColoured p \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. c = rv) p\<rbrace>"
  apply (clarsimp simp: valid_def cte_wp_at'_def getCTEColoured_def)
  apply (frule state_unchanged [OF getObject_cte_inv_inCurDomain])
  apply simp
  apply (drule getObject_cte_det_inCurDomain, simp)
  done

lemma getCTE_sp_inCurDomain:
  "\<lbrace>P\<rbrace> getCTEColoured p \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>c. c = rv) p and P\<rbrace>"
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule getCTE_cte_wp_at_inCurDomain)
    apply (rule getCTE_inv_inCurDomain)
   apply (rule conjI, rule TrueI, assumption)
  apply simp
  done

lemma getObject_obj_at'_inCurDomain:
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows      "\<lbrace> \<top> \<rbrace> getObjectColoured p \<lbrace>\<lambda>r::'a::pspace_storable. obj_at' ((=) r) p\<rbrace>"
  by (wpsimp simp: getObjectColoured_def x P wp: getObject_obj_at')

lemma getObject_ko_at_inCurDomain:
  assumes x: "\<And>q n ko. loadObject p q n ko =
                (loadObject_default p q n ko :: ('a :: pspace_storable) kernel)"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows      "\<lbrace> \<top> \<rbrace> getObjectColoured p \<lbrace>\<lambda>r::'a::pspace_storable. ko_at' r p\<rbrace>"
  by (subst eq_commute, rule getObject_obj_at'_inCurDomain [OF x P])

lemma getObject_ko_at_tcb_inCurDomain [wp]:
  "\<lbrace>\<top>\<rbrace> getObjectColoured p \<lbrace>\<lambda>rv::tcb. ko_at' rv p\<rbrace>"
  by (rule getObject_ko_at_inCurDomain | simp add: objBits_simps')+

section \<open>corres lemmas\<close>

lemma corres_get_tcb_inCurDomain':
  "corres (tcb_relation \<circ> the) (tcb_at t) (tcb_at' t and (\<lambda>s. isInDomainColour' (ksCurDomain s) t)) (gets (get_tcb t)) (getObjectColoured t)"
  apply (simp add: getObjectColoured_def)
  apply (rule corres_stateAssert_r)
  by (rule corres_get_tcb)

lemma corres_get_tcb_inCurDomain:
  "corres (tcb_relation \<circ> the)
    (tcb_at t and (\<lambda>s. t \<in> colour_oracle (cur_domain s))) (tcb_at' t)
  (gets (get_tcb t)) (getObjectColoured t)"
  apply (rule stronger_corres_guard_imp[where Q="tcb_at t" and Q'="tcb_at' t and (\<lambda>s. isInDomainColour' (ksCurDomain s) t)"])
  by (simp add: corres_get_tcb_inCurDomain' colour_invariant_isInDomColour')+

lemma getObject_TCB_corres_inCurDomain':
  "corres tcb_relation (tcb_at t and pspace_aligned and pspace_distinct) (\<lambda>s. isInDomainColour' (ksCurDomain s) t)
          (gets_the (get_tcb t)) (getObjectColoured t)"
  apply (rule corres_cross_over_guard[where Q="tcb_at' t and (\<lambda>s. isInDomainColour' (ksCurDomain s) t)"])
   apply (fastforce simp: tcb_at_cross state_relation_def)
  apply (rule corres_guard_imp)
    apply (rule corres_gets_the)
    apply (rule corres_get_tcb_inCurDomain')
   apply (simp add: tcb_at_def)
  apply assumption
  done

lemma getObject_TCB_corres_inCurDomain:
  "corres tcb_relation (tcb_at t and pspace_aligned and pspace_distinct and (\<lambda>s. t \<in> colour_oracle (cur_domain s))) \<top>
          (gets_the (get_tcb t)) (getObjectColoured t)"
  apply (rule stronger_corres_guard_imp[where Q="tcb_at t and pspace_aligned and pspace_distinct" and Q'="\<lambda>s. isInDomainColour' (ksCurDomain s) t"])
  by (simp add: getObject_TCB_corres_inCurDomain' colour_invariant_isInDomColour')+

lemma corres_stateAssert_r':
  "corres_underlying sr nf nf' r P Q f (g ()) \<Longrightarrow>
   corres_underlying sr nf nf' r P (P' and Q) f (stateAssert P' [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (rule corres_symb_exec_r [OF _ get_sp])
    apply (rule corres_assert_assume)
     apply (rule corres_assume_pre)
     apply (erule corres_guard_imp, clarsimp+)
   apply (wp | rule no_fail_pre)+
  done

lemma getObject_ASIDPool_corres_inCurDomain':
  "p' = p \<Longrightarrow>
   corres (\<lambda>p p'. p = inv ASIDPool p' o ucast)
          (asid_pool_at p and pspace_aligned and pspace_distinct) (\<lambda>s. isInDomainColour' (ksCurDomain s) p')
          (get_asid_pool p) (getObjectColoured p')"
  apply (rule corres_cross_over_asid_pool_at, fastforce)
  apply (simp add: getObjectColoured_def)
  apply (rule corres_stateAssert_r')
by (simp add: corres_cross_over_guard
    getObject_ASIDPool_corres)

lemma getObject_ASIDPool_corres_inCurDomain:
  "p' = p \<Longrightarrow>
   corres (\<lambda>p p'. p = inv ASIDPool p' o ucast)
          (asid_pool_at p and pspace_aligned and pspace_distinct and (\<lambda>s. p \<in> colour_oracle (cur_domain s))) \<top>
          (get_asid_pool p) (getObjectColoured p')"
  apply (rule stronger_corres_guard_imp[where Q="asid_pool_at p and pspace_aligned and pspace_distinct" and Q'="\<lambda>s. isInDomainColour' (ksCurDomain s) p'"])
  by (simp add: getObject_ASIDPool_corres_inCurDomain' colour_invariant_isInDomColour')+

lemma getObject_PTE_corres_inCurDomain':
  "p = p' \<Longrightarrow>
   corres pte_relation' (pte_at p and pspace_aligned and pspace_distinct) (\<lambda>s. isInDomainColour' (ksCurDomain s) p')
          (get_pte p) (getObjectColoured p')"
  apply (rule corres_cross_over_pte_at, fastforce)
  apply (simp add: getObjectColoured_def)
  apply (rule corres_stateAssert_r')
by (simp add: corres_cross_over_guard
    getObject_PTE_corres)

lemma getObject_PTE_corres_inCurDomain[corres]:
  "p = p' \<Longrightarrow>
   corres pte_relation' (pte_at p and pspace_aligned and pspace_distinct and (\<lambda>s. p \<in> colour_oracle (cur_domain s))) \<top>
          (get_pte p) (getObjectColoured p')"
  apply (rule stronger_corres_guard_imp[where Q="pte_at p and pspace_aligned and pspace_distinct" and Q'="\<lambda>s. isInDomainColour' (ksCurDomain s) p'"])
  by (simp add: getObject_PTE_corres_inCurDomain' colour_invariant_isInDomColour')+

lemma setObject_update_TCB_corres_inCurDomain'':
  assumes tcbs: "tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb'"
  assumes tables: "\<forall>(getF, v) \<in> ran tcb_cap_cases. getF new_tcb = getF tcb"
  assumes tables': "\<forall>(getF, v) \<in> ran tcb_cte_cases. getF new_tcb' = getF tcb'"
  assumes sched_pointers: "tcbSchedPrev new_tcb' = tcbSchedPrev tcb'"
                          "tcbSchedNext new_tcb' = tcbSchedNext tcb'"
  assumes flag: "\<And>d p. inQ d p new_tcb' = inQ d p tcb'"
  assumes r: "r () ()"
  shows
    "corres r
       (ko_at (TCB tcb) ptr) (ko_at' tcb' ptr and (\<lambda>s. isInDomainColour' (ksCurDomain s) ptr))
       (set_object ptr (TCB new_tcb)) (setObjectColoured ptr new_tcb')"
  apply (simp add: setObjectColoured_def)
  apply (rule corres_stateAssert_r)
  apply (rule setObject_update_TCB_corres')
  by (simp_all add: assms)

lemma setObject_update_TCB_corres_inCurDomain':
  "\<lbrakk>tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb';
     \<forall>(getF, v) \<in> ran tcb_cap_cases. getF new_tcb = getF tcb;
     \<forall>(getF, v) \<in> ran tcb_cte_cases. getF new_tcb' = getF tcb';
     tcbSchedPrev new_tcb' = tcbSchedPrev tcb'; tcbSchedNext new_tcb' = tcbSchedNext tcb';
     \<And>d p. inQ d p new_tcb' = inQ d p tcb';
     r () ()\<rbrakk> \<Longrightarrow>
   corres r
     (\<lambda>s. get_tcb ptr s = Some tcb) ((\<lambda>s'. (tcb', s') \<in> fst (getObject ptr s')) and (\<lambda>s. isInDomainColour' (ksCurDomain s) ptr))
     (set_object ptr (TCB new_tcb)) (setObjectColoured ptr new_tcb')"
  apply (rule corres_guard_imp)
    apply (erule (4) setObject_update_TCB_corres_inCurDomain'')
   apply (clarsimp simp: getObject_def in_monad split_def obj_at'_def
                         loadObject_default_def objBits_simps' in_magnitude_check)+
  done

lemma setObject_update_TCB_corres_inCurDomain:
  "\<lbrakk>tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb';
     \<forall>(getF, v) \<in> ran tcb_cap_cases. getF new_tcb = getF tcb;
     \<forall>(getF, v) \<in> ran tcb_cte_cases. getF new_tcb' = getF tcb';
     tcbSchedPrev new_tcb' = tcbSchedPrev tcb'; tcbSchedNext new_tcb' = tcbSchedNext tcb';
     \<And>d p. inQ d p new_tcb' = inQ d p tcb';
     r () ()\<rbrakk> \<Longrightarrow>
   corres r
     ((\<lambda>s. get_tcb ptr s = Some tcb) and (\<lambda>s. ptr \<in> colour_oracle (cur_domain s))) ((\<lambda>s'. (tcb', s') \<in> fst (getObject ptr s')))
     (set_object ptr (TCB new_tcb)) (setObjectColoured ptr new_tcb')"
  apply (rule stronger_corres_guard_imp[where Q="\<lambda>s. get_tcb ptr s = Some tcb" and Q'="(\<lambda>s'. (tcb', s') \<in> fst (getObject ptr s')) and (\<lambda>s. isInDomainColour' (ksCurDomain s) ptr)"])
  by (simp add: setObject_update_TCB_corres_inCurDomain' colour_invariant_isInDomColour')+

lemma setObject_other_corres_inCurDomain':
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows      "other_obj_relation ob (injectKO (ob' :: 'a :: pspace_storable)) \<Longrightarrow>
  corres dc (obj_at (\<lambda>ko. a_type ko = a_type ob) ptr and obj_at (same_caps ob) ptr)
            (obj_at' (P :: 'a \<Rightarrow> bool) ptr and (\<lambda>s. isInDomainColour' (ksCurDomain s) ptr))
            (set_object ptr ob) (setObjectColoured ptr ob')"
  apply (simp add: setObjectColoured_def)
  apply (rule corres_stateAssert_r)
  apply (rule setObject_other_corres)
  by (simp_all add: assms)

lemma setObject_other_corres_inCurDomain:
  assumes x: "updateObject ob' = updateObject_default ob'"
  assumes z: "\<And>s. obj_at' P ptr s
               \<Longrightarrow> map_to_ctes ((ksPSpace s) (ptr \<mapsto> injectKO ob')) = map_to_ctes (ksPSpace s)"
  assumes t: "is_other_obj_relation_type (a_type ob)"
  assumes b: "\<And>ko. P ko \<Longrightarrow> objBits ko = objBits ob'"
  assumes P: "\<And>(v::'a::pspace_storable). (1 :: machine_word) < 2 ^ (objBits v)"
  shows      "other_obj_relation ob (injectKO (ob' :: 'a :: pspace_storable)) \<Longrightarrow>
  corres dc (obj_at (\<lambda>ko. a_type ko = a_type ob) ptr and obj_at (same_caps ob) ptr and (\<lambda>s. ptr \<in> colour_oracle (cur_domain s)))
            (obj_at' (P :: 'a \<Rightarrow> bool) ptr)
            (set_object ptr ob) (setObjectColoured ptr ob')"
  apply (rule stronger_corres_guard_imp[where Q="obj_at (\<lambda>ko. a_type ko = a_type ob) ptr and obj_at (same_caps ob) ptr" and Q'="obj_at' (P :: 'a \<Rightarrow> bool) ptr  and (\<lambda>s. isInDomainColour' (ksCurDomain s) ptr)"])
  by (simp add: setObject_other_corres_inCurDomain' colour_invariant_isInDomColour' x z t b P)+

lemma setObject_PT_corres_inCurDomain':
  "pte_relation' pte pte' \<Longrightarrow>
   corres dc ((\<lambda>s. pts_of s (table_base p) = Some pt) and K (is_aligned p pte_bits) and
              pspace_aligned and pspace_distinct) (\<lambda>s. isInDomainColour' (ksCurDomain s) p)
          (set_pt (table_base p) (pt(table_index p := pte)))
          (setObjectColoured p pte')"
  supply opt_mapE[elim!]
  apply (rule corres_cross_over_pte_at[where p=p])
   apply (simp add: pte_at_eq ptes_of_def in_omonad)
  apply (simp add: setObjectColoured_def)
  apply (rule corres_stateAssert_r')
  apply (simp add: set_pt_def get_object_def bind_assoc set_object_def gets_map_def)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
    apply simp
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def typ_at'_def lookupAround2_known1)
   apply (case_tac ko; simp)
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object; simp)
   apply (simp add: objBits_simps word_bits_def)
  apply (clarsimp simp: setObject_def in_monad split_def updateObject_default_def)
  apply (simp add: in_magnitude_check objBits_simps a_type_simps)
  apply (clarsimp simp: obj_at_def exec_gets a_type_simps opt_map_def exec_get put_def)
  apply (clarsimp simp: state_relation_def mask_pt_bits_inner_beauty)
  apply (rule conjI)
   apply (clarsimp simp: pspace_relation_def split del: if_split)
   apply (rule conjI)
    apply (subst pspace_dom_update, assumption)
     apply (simp add: a_type_def)
    apply (auto simp: dom_def)[1]
   apply (rule conjI)
    apply (drule bspec, blast)
    apply clarsimp
    apply (drule_tac x = x in spec)
    apply (clarsimp simp: pte_relation_def mask_pt_bits_inner_beauty
                   dest!: more_pt_inner_beauty)
   apply (rule ballI)
   apply (drule (1) bspec)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: pte_relation_def mask_pt_bits_inner_beauty
                   dest!: more_pt_inner_beauty)
   apply clarsimp
   apply (drule bspec, assumption)
   apply clarsimp
   apply (erule (1) obj_relation_cutsE)
      apply simp
     apply simp
     apply clarsimp
     apply (frule (1) pspace_alignedD)
     apply (drule_tac p=x in pspace_alignedD, assumption)
     apply simp
     apply (drule mask_alignment_ugliness)
        apply (simp add: pt_bits_def pageBits_def)
       apply (simp add: pt_bits_def pageBits_def)
      apply clarsimp
      apply (drule test_bit_size)
      apply (clarsimp simp: word_size bit_simps)
      apply arith
     apply ((simp split: if_split_asm)+)[2]
   apply (simp add: other_obj_relation_def
               split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (extract_conjunct \<open>match conclusion in "ghost_relation _ _ _" \<Rightarrow> -\<close>)
   apply (clarsimp simp add: ghost_relation_def)
   apply (erule_tac x="p && ~~ mask pt_bits" in allE)+
   apply fastforce
  apply (extract_conjunct \<open>match conclusion in "ready_queues_relation_2 _ _ _ _ _" \<Rightarrow> -\<close>)
   apply (prop_tac "typ_at' (koTypeOf (injectKO pte')) p b")
    apply (simp add: typ_at'_def ko_wp_at'_def)
   subgoal by (fastforce dest: tcbs_of'_non_tcb_update)
  apply (simp add: map_to_ctes_upd_other)
  apply (simp add: fun_upd_def)
  apply (simp add: caps_of_state_after_update obj_at_def swp_cte_at_caps_of)
  done

lemma setObject_PT_corres_inCurDomain:
  "pte_relation' pte pte' \<Longrightarrow>
   corres dc ((\<lambda>s. pts_of s (table_base p) = Some pt) and K (is_aligned p pte_bits) and
              pspace_aligned and pspace_distinct and (\<lambda>s. p \<in> colour_oracle (cur_domain s))) \<top>
          (set_pt (table_base p) (pt(table_index p := pte)))
          (setObjectColoured p pte')"
  apply (rule stronger_corres_guard_imp[where Q="(\<lambda>s. pts_of s (table_base p) = Some pt) and K (is_aligned p pte_bits) and  pspace_aligned and pspace_distinct" and Q'="\<lambda>s. isInDomainColour' (ksCurDomain s) p"])
  by (simp only: setObject_PT_corres_inCurDomain'|simp add: colour_invariant_isInDomColour')+

lemma setObject_ASIDPool_corres_inCurDomain':
  "\<lbrakk> a = inv ASIDPool a' o ucast; p' = p \<rbrakk> \<Longrightarrow>
  corres dc (asid_pool_at p and pspace_aligned and pspace_distinct) (\<lambda>s. isInDomainColour' (ksCurDomain s) p')
            (set_asid_pool p a) (setObjectColoured p' a')"
  apply (simp add: set_asid_pool_def)
  apply (rule corres_underlying_symb_exec_l[where P=P and Q="\<lambda>_. P" for P])
    apply (rule corres_no_failI; clarsimp)
    apply (simp add:
      TcbAcc_R.no_fail_return)
    apply (clarsimp simp: gets_map_def bind_def simpler_gets_def assert_opt_def fail_def return_def
                          obj_at_def in_omonad
                    split: option.splits)
   prefer 2
   apply wpsimp
  apply (rule corres_cross_over_asid_pool_at, fastforce)
  apply (rule corres_guard_imp)
    apply (rule setObject_other_corres_inCurDomain' [where P="\<lambda>ko::asidpool. True"])
          apply simp
         apply (clarsimp simp: obj_at'_def)
         apply (erule map_to_ctes_upd_other, simp, simp)
        apply (simp add: a_type_def is_other_obj_relation_type_def)
       apply (simp add: objBits_simps)
      apply simp
     apply (simp add: objBits_simps pageBits_def)
    apply (simp add: other_obj_relation_def asid_pool_relation_def)
   apply (simp add: typ_at'_def obj_at'_def ko_wp_at'_def)
   apply clarsimp
   apply (rename_tac arch_kernel_object)
   apply (case_tac arch_kernel_object; simp)
   apply (clarsimp simp: obj_at_def exs_valid_def assert_def a_type_def return_def fail_def)
   apply (auto split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm if_split_asm)[1]
  apply (simp add: typ_at_to_obj_at_arches)
  done

lemma setObject_ASIDPool_corres_inCurDomain[corres]:
  "\<lbrakk> a = inv ASIDPool a' o ucast; p' = p \<rbrakk> \<Longrightarrow>
  corres dc (asid_pool_at p and pspace_aligned and pspace_distinct and (\<lambda>s. p \<in> colour_oracle (cur_domain s))) \<top>
            (set_asid_pool p a) (setObjectColoured p' a')"
  apply (rule stronger_corres_guard_imp[where Q="asid_pool_at p and pspace_aligned and pspace_distinct" and Q'="\<lambda>s. isInDomainColour' (ksCurDomain s) p"])
  by (simp add: colour_invariant_isInDomColour' setObject_ASIDPool_corres_inCurDomain')+

lemma get_cap_inCurDomain_corres_P':
  "corres (\<lambda>x y. cap_relation x (cteCap y) \<and> P x)
          (cte_wp_at P cslot_ptr)
          (pspace_aligned' and pspace_distinct' and (\<lambda>s. isInDomainColour' (ksCurDomain s) (cte_map cslot_ptr)))
          (get_cap cslot_ptr) (getCTEColoured (cte_map cslot_ptr))"
  apply (rule corres_stronger_no_failI)
   apply (rule no_fail_pre, wp)
   apply clarsimp
   apply (drule cte_wp_at_norm)
   apply (clarsimp simp: state_relation_def)
   apply (drule (3) pspace_relation_ctes_ofI)
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (cases cslot_ptr)
  apply (rename_tac oref cref)
  apply (clarsimp simp: cte_wp_at_def)
  apply (frule in_inv_by_hoareD[OF getCTE_inv_inCurDomain])
  apply (drule use_valid [where P="\<top>", OF _ getCTE_sp_inCurDomain TrueI])
  apply (clarsimp simp: state_relation_def)
  apply (drule pspace_relation_ctes_ofI)
     apply (simp add: cte_wp_at_def)
    apply assumption+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma get_cap_inCurDomain_corres_P:
  "corres (\<lambda>x y. cap_relation x (cteCap y) \<and> P x)
          (cte_wp_at P cslot_ptr and (\<lambda>s. cte_map cslot_ptr \<in> colour_oracle (cur_domain s)))
          (pspace_aligned' and pspace_distinct')
          (get_cap cslot_ptr) (getCTEColoured (cte_map cslot_ptr))"
  apply (rule stronger_corres_guard_imp[where Q="cte_wp_at P cslot_ptr" and Q'="pspace_aligned' and pspace_distinct' and (\<lambda>s. isInDomainColour' (ksCurDomain s) (cte_map cslot_ptr))"])
  by (simp add: colour_invariant_isInDomColour' get_cap_inCurDomain_corres_P')+

lemmas get_cap_inCurDomain_corres = get_cap_inCurDomain_corres_P[where P="\<top>", simplified]

lemma threadsetInCurDomain_corresT':
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation (f tcb) (f' tcb')"
  assumes y: "\<And>tcb. \<forall>(getF, setF) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb"
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (f' tcb) = getF tcb"
  assumes sched_pointers: "\<And>tcb. tcbSchedPrev (f' tcb) = tcbSchedPrev tcb"
                          "\<And>tcb. tcbSchedNext (f' tcb) = tcbSchedNext tcb"
  assumes flag: "\<And>d p tcb'. inQ d p (f' tcb') = inQ d p tcb'"
  shows      "corres dc (tcb_at t and pspace_aligned and pspace_distinct)
                        (\<lambda>s. isInDomainColour' (ksCurDomain s) t)
                        (thread_set f t) (threadSetInCurDomain f' t)"
  apply (simp add: threadSetInCurDomain_def)
  apply (rule corres_guard_imp)
  apply (rule corres_stateAssert_r')
  apply (rule threadset_corresT)
  by (simp_all add: assms)

lemma threadsetInCurDomain_corresT:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow>
                         tcb_relation (f tcb) (f' tcb')"
  assumes y: "\<And>tcb. \<forall>(getF, setF) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb"
  assumes z: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases.
                 getF (f' tcb) = getF tcb"
  assumes sched_pointers: "\<And>tcb. tcbSchedPrev (f' tcb) = tcbSchedPrev tcb"
                          "\<And>tcb. tcbSchedNext (f' tcb) = tcbSchedNext tcb"
  assumes flag: "\<And>d p tcb'. inQ d p (f' tcb') = inQ d p tcb'"
  shows      "corres dc (tcb_at t and pspace_aligned and pspace_distinct and (\<lambda>s. t \<in> colour_oracle (cur_domain s)))
                        \<top>
                        (thread_set f t) (threadSetInCurDomain f' t)"
  apply (rule stronger_corres_guard_imp[where Q="tcb_at t and pspace_aligned and pspace_distinct" and Q'="(\<lambda>s. isInDomainColour' (ksCurDomain s) t)"])
  by (simp add: colour_invariant_isInDomColour' threadsetInCurDomain_corresT' x y z sched_pointers flag)+

lemmas threadsetInCurDomain_corres =
    threadsetInCurDomain_corresT [OF _ _ all_tcbI, OF _ ball_tcb_cap_casesI ball_tcb_cte_casesI]
end
end
