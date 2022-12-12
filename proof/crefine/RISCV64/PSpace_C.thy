(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory PSpace_C
imports Ctac_lemmas_C
begin

context kernel begin

lemma setObject_obj_at_pre:
  "\<lbrakk> updateObject ko = updateObject_default ko;
       (1 :: machine_word) < 2 ^ objBits ko \<rbrakk>
   \<Longrightarrow>
   setObject p ko
     = (stateAssert (typ_at' (koTypeOf (injectKO ko)) p) []
           >>= (\<lambda>_. setObject p ko))"
  apply (rule ext)
  apply (case_tac "typ_at' (koTypeOf (injectKO ko)) p x")
   apply (simp add: stateAssert_def bind_def get_def return_def)
  apply (simp add: stateAssert_def bind_def get_def assert_def)
  apply (simp add: setObject_def exec_gets split_def assert_opt_def split: option.split)
  apply (clarsimp simp: fail_def)
  apply (simp add: bind_def simpler_modify_def split_def)
  apply (rule context_conjI)
   apply clarsimp
   apply (clarsimp simp: updateObject_default_def in_monad in_magnitude_check)
   apply (frule project_koType[THEN iffD1, OF exI])
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def objBits_simps koTypeOf_injectKO)
  apply (rule empty_failD[OF empty_fail_updateObject_default])
  apply (rule ccontr, erule nonemptyE)
  apply clarsimp
  done

lemma setObject_ccorres_helper_variable_size:
  fixes ko :: "'a :: pspace_storable"
  assumes valid: "\<And>\<sigma> (ko' :: 'a).
        \<Gamma> \<turnstile> {s. (\<sigma>, s) \<in> rf_sr \<and> P \<sigma> \<and> s \<in> P' \<and> ko_at' ko' p \<sigma>}
              c {s. (\<sigma>\<lparr>ksPSpace := (ksPSpace \<sigma>)(p \<mapsto> injectKO ko)\<rparr>, s) \<in> rf_sr}"
  shows "\<lbrakk> \<And>ko :: 'a. updateObject ko = updateObject_default ko;
           (1 :: machine_word) < 2 ^ objBits ko \<rbrakk>
    \<Longrightarrow> ccorres dc xfdc (P and obj_at' (\<lambda>obj. objBits ko = objBits obj) p) P' hs (setObject p ko) c"
  apply (rule ccorres_guard_imp2)
   apply (subst setObject_obj_at_pre)
     apply simp+
   apply (rule ccorres_symb_exec_l[where Q'="\<lambda>_. P'"])
      defer
      apply (rule stateAssert_inv)
     apply (rule stateAssert_sp[where P="P and obj_at' (\<lambda>obj. objBits ko = objBits obj) p"])
    apply (rule empty_fail_stateAssert)
   apply fastforce
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule hoare_complete)
  apply (clarsimp simp: HoarePartialDef.valid_def)
  apply (simp add: typ_at_to_obj_at' koTypeOf_injectKO)
  apply (drule obj_at_ko_at', clarsimp)
  apply (drule obj_at_ko_at', clarsimp)
  apply (cut_tac \<sigma>1=\<sigma> and ko'1=koaa in valid)
  apply (drule hoare_sound,
         clarsimp simp: cvalid_def HoarePartialDef.valid_def)
  apply (elim allE, drule(1) mp)
  apply (drule mp, simp)
  apply clarsimp
  apply (rule imageI[OF CollectI])
  apply (frule_tac v=ko in setObject_eq_variable_size)
     apply fastforce
    apply fastforce
   apply (fastforce simp: obj_at'_def)
  apply fastforce
  done

(* FIXME RT: prove via setObject_ccorres_helper_variable_size, or remove this lemma
             in favour of setObject_ccorres_helper_variable_size *)
lemma setObject_ccorres_helper:
  fixes ko :: "'a :: pspace_storable"
  assumes valid: "\<And>\<sigma> (ko' :: 'a).
        \<Gamma> \<turnstile> {s. (\<sigma>, s) \<in> rf_sr \<and> P \<sigma> \<and> s \<in> P' \<and> ko_at' ko' p \<sigma>}
              c {s. (\<sigma>\<lparr>ksPSpace := (ksPSpace \<sigma>)(p \<mapsto> injectKO ko)\<rparr>, s) \<in> rf_sr}"
  shows "\<lbrakk> \<And>ko :: 'a. updateObject ko = updateObject_default ko;
           \<And>ko :: 'a. (1 :: machine_word) < 2 ^ objBits ko;
           \<And>(v :: 'a) (v' :: 'a). objBits v = objBits v' \<rbrakk>
    \<Longrightarrow> ccorres dc xfdc P P' hs (setObject p ko) c"
  apply (rule ccorres_guard_imp2)
   apply (subst setObject_obj_at_pre)
     apply simp+
   apply (rule ccorres_symb_exec_l[where Q'="\<lambda>_. P'"])
      defer
      apply (rule stateAssert_inv)
     apply (rule stateAssert_sp[where P=P])
    apply (rule empty_fail_stateAssert)
   apply simp
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule hoare_complete)
  apply (clarsimp simp: HoarePartialDef.valid_def)
  apply (simp add: typ_at_to_obj_at' koTypeOf_injectKO)
  apply (drule obj_at_ko_at', clarsimp)
  apply (cut_tac \<sigma>1=\<sigma> and ko'1=koa in valid)
  apply (drule hoare_sound,
         clarsimp simp: cvalid_def HoarePartialDef.valid_def)
  apply (elim allE, drule(1) mp)
  apply (drule mp, simp)
  apply clarsimp
  apply (rule imageI[OF CollectI])
  by (fastforce intro!: setObject_eq rev_bexI)

lemma carray_map_relation_upd_triv:
  "f x = Some (v :: 'a :: pspace_storable) \<Longrightarrow>
   carray_map_relation n (f (x \<mapsto> y)) hp ptrf = carray_map_relation n f hp ptrf"
  by (auto simp: carray_map_relation_def objBits_def koTypeOf_injectKO)

lemma storePTE_Basic_ccorres':
  "cpte_relation pte pte' \<Longrightarrow>
   ccorres dc xfdc \<top> {s. ptr_val (f s) = p} hs
     (storePTE p pte)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c f s}
        (Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (f s) pte'))) s)))"
  apply (simp add: storePTE_def)
  apply (rule setObject_ccorres_helper)
    apply (simp_all add: objBits_simps bit_simps)
  apply (rule conseqPre, vcg)
  apply (rule subsetI, clarsimp simp: Collect_const_mem)
  apply (rule cmap_relationE1, erule rf_sr_cpte_relation,
         erule ko_at_projectKO_opt)
  apply (rule conjI, fastforce intro: typ_heap_simps)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (rule conjI)
   apply (clarsimp simp: cpspace_relation_def typ_heap_simps refill_buffer_relation_def
                         update_pte_map_to_ptes
                         update_pte_map_tos
                         carray_map_relation_upd_triv)
   apply (case_tac "f x", simp)
   apply (erule cmap_relation_updI)
      by (fastforce simp: cready_queues_relation_def carch_state_relation_def
                          cmachine_state_relation_def Let_def typ_heap_simps
                          cteCaps_of_def update_pte_map_tos bit_simps refill_buffer_relation_def
                  intro!: refill_buffer_relation_pte_update)+

lemma storePTE_Basic_ccorres:
  "\<lbrakk> cpte_relation pte pte' \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc \<top> {s. f s = p} hs
     (storePTE p pte)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c pte_Ptr (f s)}
        (Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (pte_Ptr (f s)) pte'))) s)))"
  apply (rule ccorres_guard_imp2)
   apply (erule storePTE_Basic_ccorres')
  apply simp
  done

lemma ccorres_pre_getObject_sc:
  assumes cc: "\<And>rv. ccorres r xf (P rv) (P' rv) hs (f rv) c"
  shows   "ccorres r xf
                  (\<lambda>s. (\<forall>sc. ko_at' sc p s \<longrightarrow> P sc s))
                  {s. \<forall> sc sc'. cslift s (Ptr p) = Some sc' \<and> csched_context_relation sc sc'
                           \<longrightarrow> s \<in> P' sc}
                          hs (getSchedContext p >>= (\<lambda>rv :: sched_context. f rv)) c"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_guard_imp2)
       apply (rule cc)
      apply (rule conjI)
       apply (rule_tac Q="ko_at' rv p s" in conjunct1)
       apply assumption
      apply assumption
     apply (wpsimp wp: set_sc'.getObject_wp empty_fail_getObject simp: getSchedContext_def)+
  apply (erule cmap_relationE1[OF cmap_relation_sched_context],
         erule ko_at_projectKO_opt)
  apply simp
  done

lemma updateSchedContext_eq:
  "\<lbrakk>ko_at' sc scPtr s; objBits sc < word_bits; \<And>sc. scSize (f sc) = scSize sc\<rbrakk>
   \<Longrightarrow> ((), s\<lparr> ksPSpace := (ksPSpace s)(scPtr \<mapsto> injectKO (f sc))\<rparr>)
       \<in> fst (updateSchedContext scPtr f s)"
  unfolding updateSchedContext_def
  apply (clarsimp simp add: in_monad)
  apply (rule exI)
  apply (rule exI)
  apply (rule conjI)
   apply (clarsimp simp: getSchedContext_def)
   apply (rule getObject_eq)
     apply simp
   apply assumption
  apply (frule_tac v="f sc" in setObject_eq_variable_size)
     apply simp
    apply (simp add: objBits_simps')
    using scBits_pos_power2 apply fastforce
   apply (simp add: obj_at'_def)
   apply (rule_tac x=sc in exI)
   apply (simp add: objBits_simps)
  apply (clarsimp simp: setSchedContext_def)
  done

end
end
