(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory PSpace_C
imports Ctac_lemmas_C
begin

context begin interpretation Arch . (*FIXME: arch-split*)

lemma setObject_obj_at_pre:
  "\<lbrakk> updateObject ko = updateObject_default ko;
       (1 :: word32) < 2 ^ objBits ko \<rbrakk>
   \<Longrightarrow>
   setObject p ko
     = (stateAssert (typ_at' (koTypeOf (injectKO ko)) p) []
           >>= (\<lambda>_. setObject p ko))"
  apply (rule ext)
  apply (case_tac "typ_at' (koTypeOf (injectKO ko)) p x")
   apply (simp add: stateAssert_def bind_def
                    get_def return_def)
  apply (simp add: stateAssert_def bind_def
                   get_def assert_def fail_def)
  apply (simp add: setObject_def exec_gets split_def
                   assert_opt_def split: option.split)
  apply (clarsimp simp add: fail_def)
  apply (simp add: bind_def simpler_modify_def split_def)
  apply (rule context_conjI)
   apply (clarsimp simp: updateObject_default_def
                         in_monad)
   apply (clarsimp simp: projectKOs in_magnitude_check)
   apply (frule iffD1[OF project_koType, OF exI])
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def)
   apply (simp only: objBitsT_koTypeOf[symmetric] objBits_def)
   apply simp
   apply (simp add: koTypeOf_injectKO)
  apply (rule empty_failD[OF empty_fail_updateObject_default])
  apply (rule ccontr, erule nonemptyE)
  apply clarsimp
  done

end

context kernel begin

lemma setObject_ccorres_helper:
  fixes ko :: "'a :: pspace_storable"
  assumes valid: "\<And>\<sigma> (ko' :: 'a).
        \<Gamma> \<turnstile> {s. (\<sigma>, s) \<in> rf_sr \<and> P \<sigma> \<and> s \<in> P' \<and> ko_at' ko' p \<sigma>}
              c {s. (\<sigma>\<lparr>ksPSpace := (ksPSpace \<sigma>)(p \<mapsto> injectKO ko)\<rparr>, s) \<in> rf_sr}"
  shows "\<lbrakk> \<And>ko :: 'a. updateObject ko = updateObject_default ko;
           \<And>ko :: 'a. (1 :: word32) < 2 ^ objBits ko \<rbrakk>
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
  apply (rule rev_bexI)
   apply (rule setObject_eq, simp+)
    apply (simp add: objBits_def)
    apply (simp only: objBitsT_koTypeOf[symmetric]
                      koTypeOf_injectKO)
   apply assumption
  apply simp
  done


lemma carray_map_relation_upd_triv:
  "f x = Some (v :: 'a :: pspace_storable)
    \<Longrightarrow> carray_map_relation n (f (x \<mapsto> y)) hp ptrf = carray_map_relation n f hp ptrf"
  by (simp add: carray_map_relation_def objBits_def objBitsT_koTypeOf[symmetric]
                koTypeOf_injectKO
           del: objBitsT_koTypeOf)

lemma storePTE_Basic_ccorres':
  "\<lbrakk> cpte_relation pte pte' \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc \<top> {s. ptr_val (f s) = p} hs
     (storePTE p pte)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c f s}
        (Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (f s) pte'))) s)))"
  apply (simp add: storePTE_def)
  apply (rule setObject_ccorres_helper)
    apply (simp_all add: objBits_simps archObjSize_def)
  apply (rule conseqPre, vcg)
  apply (rule subsetI, clarsimp simp: Collect_const_mem)
  apply (rule cmap_relationE1, erule rf_sr_cpte_relation,
         erule ko_at_projectKO_opt)
  apply (rule conjI, fastforce intro: typ_heap_simps)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (rule conjI)
   apply (clarsimp simp: cpspace_relation_def typ_heap_simps
                         update_pte_map_to_ptes
                         update_pte_map_tos
                         carray_map_relation_upd_triv)

   apply (case_tac "f x", simp)

   apply (erule cmap_relation_updI,
          erule ko_at_projectKO_opt, simp+)
  apply (simp add: cready_queues_relation_def
                   carch_state_relation_def
                   cmachine_state_relation_def
                   Let_def typ_heap_simps
                   cteCaps_of_def update_pte_map_tos
                   )
  apply (simp add: pteBits_def)
  done


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

lemma pde_stored_asid_update_valid_offset:
  "valid_pde_mapping_offset' (ptr_val p && mask pdBits)
      \<Longrightarrow> (pde_stored_asid  \<circ>\<^sub>m (clift (t_hrs_' cstate))(p \<mapsto> pde) \<circ>\<^sub>m pd_pointer_to_asid_slot)
            = (pde_stored_asid  \<circ>\<^sub>m clift (t_hrs_' cstate) \<circ>\<^sub>m pd_pointer_to_asid_slot)"
  apply (rule ext, clarsimp simp add: pd_pointer_to_asid_slot_def map_comp_eq)
  apply (simp add: valid_pde_mapping_offset'_def mask_add_aligned)
  apply (simp add: pd_asid_slot_def pdBits_def pageBits_def mask_def pdeBits_def)
  done

lemma storePDE_Basic_ccorres':
  "\<lbrakk> cpde_relation pde pde' \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc
     (\<lambda>_. valid_pde_mapping_offset' (p && mask pdBits))
     {s. ptr_val (f s) = p} hs
     (storePDE p pde)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c f s}
        (Basic (\<lambda>s. globals_update( t_hrs_'_update
            (hrs_mem_update (heap_update (f s) pde'))) s)))"
  apply (simp add: storePDE_def)
  apply (rule setObject_ccorres_helper)
    apply (simp_all add: objBits_simps archObjSize_def)
  apply (rule conseqPre, vcg)
  apply (rule subsetI, clarsimp simp: Collect_const_mem)
  apply (rule cmap_relationE1, erule rf_sr_cpde_relation,
         erule ko_at_projectKO_opt)
  apply (rule conjI, fastforce intro: typ_heap_simps)
  apply (case_tac "f x", clarsimp)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (rule conjI)
   apply (clarsimp simp: cpspace_relation_def typ_heap_simps
                         update_pde_map_to_pdes
                         update_pde_map_tos
                         carray_map_relation_upd_triv)
   apply (erule cmap_relation_updI,
          erule ko_at_projectKO_opt, simp+)
  apply (simp add: cready_queues_relation_def
                   carch_state_relation_def
                   cmachine_state_relation_def
                   Let_def typ_heap_simps
                   pde_stored_asid_update_valid_offset
                   cteCaps_of_def update_pde_map_tos)
  apply (simp add: pdeBits_def)
  done

lemma storePDE_Basic_ccorres:
  "\<lbrakk> cpde_relation pde pde' \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc (\<lambda>_. valid_pde_mapping_offset' (p && mask pdBits)) {s. f s = p} hs
     (storePDE p pde)
     (Guard C_Guard {s. s \<Turnstile>\<^sub>c pde_Ptr (f s)}
        (Basic (\<lambda>s. globals_update(t_hrs_'_update
            (hrs_mem_update (heap_update (pde_Ptr (f s)) pde'))) s)))"
  apply (rule ccorres_guard_imp2)
   apply (erule storePDE_Basic_ccorres')
  apply simp
  done

end
end
