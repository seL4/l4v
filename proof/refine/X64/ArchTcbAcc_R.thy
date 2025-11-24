(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTcbAcc_R
imports TcbAcc_R
begin

context Arch begin arch_global_naming

named_theorems TcbAcc_R_assms

(* FIXME: move & the versions in Machine_AI could use word_size_bits form instead of specific number *)
lemma no_fail_loadWord_bits[TcbAcc_R_assms, wp]:
  "no_fail (\<lambda>_. is_aligned p word_size_bits) (loadWord p)"
  by (wpsimp simp: loadWord_def is_aligned_mask[symmetric] word_size_bits_def)

(* FIXME: move & the versions in Machine_AI could use word_size_bits form instead of specific number *)
lemma no_fail_storeWord_bits[TcbAcc_R_assms]:
  "no_fail (\<lambda>_. is_aligned p word_size_bits) (storeWord p w)"
  by (wpsimp simp: storeWord_def is_aligned_mask[symmetric] word_size_bits_def)

lemma prioToL1Index_l1IndexToPrio_or_id[TcbAcc_R_assms]:
  "\<lbrakk> unat (w'::priority) < 2 ^ wordRadix ; w < 2^(size w' - wordRadix) \<rbrakk>
   \<Longrightarrow> prioToL1Index ((l1IndexToPrio w) || w') = w"
  unfolding l1IndexToPrio_def prioToL1Index_def
  apply (simp add: shiftr_over_or_dist shiftr_le_0 wordRadix_def')
  apply (subst shiftl_shiftr_id, simp, simp add: word_size)
   apply (simp add: word_of_nat_less)
  apply (subst unat_of_nat_eq, simp_all add: word_size)
  done

lemma l1IndexToPrio_wordRadix_mask[TcbAcc_R_assms, simp]:
  "l1IndexToPrio i && mask wordRadix = 0"
  unfolding l1IndexToPrio_def
  by (simp add: wordRadix_def')

lemma st_tcb_at_coerce_abstract[TcbAcc_R_assms]:
  assumes t: "st_tcb_at' P t c"
  assumes sr: "(a, c) \<in> state_relation"
  shows "st_tcb_at (\<lambda>st. \<exists>st'. thread_state_relation st st' \<and> P st') t a"
  using assms
  apply (clarsimp simp: state_relation_def pred_tcb_at'_def obj_at'_def objBits_simps)
  apply (erule(1) pspace_dom_relatedE)
  apply (erule(1) obj_relation_cutsE, simp_all)
  apply (fastforce simp: st_tcb_at_def obj_at_def other_obj_relation_def
                         tcb_relation_def
                   split: Structures_A.kernel_object.split_asm if_split_asm
                          X64_A.arch_kernel_obj.split_asm)+
  done

lemma setObject_update_TCB_corres'[TcbAcc_R_assms]:
  assumes tcbs: "tcb_relation tcb tcb' \<Longrightarrow> tcb_relation new_tcb new_tcb'"
  assumes tables: "\<forall>(getF, v) \<in> ran tcb_cap_cases. getF new_tcb = getF tcb"
  assumes tables': "\<forall>(getF, v) \<in> ran tcb_cte_cases. getF new_tcb' = getF tcb'"
  assumes sched_pointers: "tcbSchedPrev new_tcb' = tcbSchedPrev tcb'"
                          "tcbSchedNext new_tcb' = tcbSchedNext tcb'"
  assumes flag: "\<And>d p. inQ d p new_tcb' = inQ d p tcb'"
  assumes r: "r () ()"
  shows
    "corres r
       (ko_at (TCB tcb) ptr) (ko_at' tcb' ptr)
       (set_object ptr (TCB new_tcb)) (setObject ptr new_tcb')"
  apply (rule_tac F="tcb_relation tcb tcb'" in corres_req)
   apply (clarsimp simp: state_relation_def obj_at_def obj_at'_def)
   apply (frule(1) pspace_relation_absD)
   apply (clarsimp simp: tcb_relation_cut_def)
  apply (rule corres_no_failI)
   apply wp
   apply (clarsimp simp: obj_at'_def)
  apply (unfold set_object_def setObject_def)
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
     apply (clarsimp simp: gen_objBits_simps)
    apply (clarsimp simp: gen_objBits_simps ps_clear_def3 field_simps mask_def)
   apply (insert tables')[1]
   apply (rule ext)
   subgoal by auto
  apply (prop_tac "obj_at (same_caps (TCB new_tcb)) ptr s")
   using tables
   apply (fastforce simp: obj_at_def)
  apply (clarsimp simp: caps_of_state_after_update cte_wp_at_after_update swp_def fun_upd_def
                        obj_at_def assms)
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

lemma setObject_tcb_valid_arch'[TcbAcc_R_assms, wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setObject t (v :: tcb) \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  by (wp valid_arch_state_lift' setObject_typ_at')

lemma setObject_tcb_refs'[TcbAcc_R_assms, wp]:
  "\<lbrace>\<lambda>s. P (global_refs' s)\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>rv s. P (global_refs' s)\<rbrace>"
  apply (clarsimp simp: setObject_def split_def updateObject_default_def)
  apply wp
  apply (simp add: global_refs'_def)
  done

lemma threadSet_state_hyp_refs_of':
  shows "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace> threadSet F t \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wpsimp wp: setObject_state_hyp_refs_of' getObject_tcb_wp
                simp: gen_objBits_simps obj_at'_def state_hyp_refs_of'_def)
  done

lemma threadSet_iflive'T:
  assumes x: "\<forall>tcb. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
  shows
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> ((\<exists>tcb. \<not> bound (tcbBoundNotification tcb) \<and> bound (tcbBoundNotification (F tcb))
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. (tcbState tcb = Inactive \<or> tcbState tcb = IdleThreadState)
              \<and> tcbState (F tcb) \<noteq> Inactive
              \<and> tcbState (F tcb) \<noteq> IdleThreadState
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. tcbSchedNext tcb = None \<and> tcbSchedNext (F tcb) \<noteq> None
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. tcbSchedPrev tcb = None \<and> tcbSchedPrev (F tcb) \<noteq> None
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)
      \<and> ((\<exists>tcb. \<not> tcbQueued tcb \<and> tcbQueued (F tcb)
              \<and> ko_at' tcb t s) \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
     threadSet F t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: threadSet_def)
  apply (wp setObject_tcb_iflive' getObject_tcb_wp)
  apply (clarsimp simp: obj_at'_def live'_def hyp_live'_def)
  apply (subst conj_assoc[symmetric], subst imp_disjL[symmetric])+
  apply (rule conjI)
   apply (rule impI, clarsimp)
   apply (erule if_live_then_nonz_capE')
   apply (clarsimp simp: ko_wp_at'_def live'_def hyp_live'_def)
  apply (clarsimp simp: bspec_split [OF spec [OF x]])
  done

lemmas threadSet_iflive' =
    threadSet_iflive'T [OF all_tcbI, OF ball_tcb_cte_casesI]

lemmas threadSet_typ_at_lifts[wp] = typ_at_lifts[OF threadSet_typ_at']

lemma zobj_refs'_capRange[TcbAcc_R_assms]:
  "s \<turnstile>' cap \<Longrightarrow> zobj_refs' cap \<subseteq> capRange cap"
  by (cases cap; simp add: valid_cap'_def capAligned_def capRange_def is_aligned_no_overflow)

lemma asUser_valid_tcbs'[wp]:
  "asUser t f \<lbrace>valid_tcbs'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wpsimp wp: threadSet_valid_tcbs' hoare_drop_imps
              simp: valid_tcb'_def valid_arch_tcb'_def tcb_cte_cases_def objBits_simps')
  done

lemmas addToBitmap_typ_ats[wp] = typ_at_lifts[OF addToBitmap_typ_at']
lemmas removeFromBitmap_typ_ats[wp] = typ_at_lifts[OF removeFromBitmap_typ_at']

lemma threadSet_ghost_relation[wp]:
  "threadSet f tcbPtr \<lbrace>\<lambda>s'. ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')\<rbrace>"
  unfolding threadSet_def setObject_def updateObject_default_def
  apply (wpsimp wp: getObject_tcb_wp simp: updateObject_default_def)
  apply (clarsimp simp: obj_at'_def)
  done

lemma removeFromBitmap_ghost_relation[wp]:
  "removeFromBitmap tdom prio
   \<lbrace>\<lambda>s'. ghost_relation (kheap s) (gsUserPages s') (gsCNodes s')\<rbrace>"
  by (rule_tac f=gsUserPages in hoare_lift_Pf2; wpsimp simp: bitmap_fun_defs)

crunch tcbQueueRemove, tcbQueuePrepend, tcbQueueAppend, tcbQueueInsert,
         setQueue, removeFromBitmap
  for ghost_relation_projs[wp]: "\<lambda>s. P (gsUserPages s) (gsCNodes s)"
  (wp: crunch_wps getObject_tcb_wp simp: setObject_def updateObject_default_def obj_at'_def)

schematic_goal l2BitmapSize_def': (* arch specific consequence *)
  "l2BitmapSize = numeral ?X"
  by (simp add: l2BitmapSize_def wordBits_def word_size numPriorities_def)

lemma prioToL1Index_size[TcbAcc_R_assms, simp]:
  "prioToL1Index w < l2BitmapSize"
  unfolding prioToL1Index_def wordRadix_def l2BitmapSize_def'
  by (fastforce simp: shiftr_div_2n' nat_divide_less_eq
                intro: order_less_le_trans[OF unat_lt2p])

lemma prioToL1Index_max:
  "prioToL1Index p < 2 ^ wordRadix"
  unfolding prioToL1Index_def wordRadix_def
  by (insert unat_lt2p[where x=p], simp add: shiftr_div_2n')

lemma prioToL1Index_bit_set[TcbAcc_R_assms]:
  "((2 :: machine_word) ^ prioToL1Index p) !! prioToL1Index p"
  using l2BitmapSize_def'
  by (fastforce simp: nth_w2p_same intro: order_less_le_trans[OF prioToL1Index_size])

lemma prioL2Index_bit_set[TcbAcc_R_assms]:
  fixes p :: priority
  shows "((2::machine_word) ^ unat (ucast p && (mask wordRadix :: machine_word))) !! unat (p && mask wordRadix)"
  apply (simp add: nth_w2p wordRadix_def ucast_and_mask[symmetric] unat_ucast_upcast is_up)
  apply (rule unat_less_helper)
  apply (insert and_mask_less'[where w=p and n=wordRadix], simp add: wordRadix_def)
  done

lemma prioToL1Index_lt:
  "2 ^ wordRadix \<le> x \<Longrightarrow> prioToL1Index p < x"
  unfolding prioToL1Index_def wordRadix_def
  by (insert unat_lt2p[where x=p], simp add: shiftr_div_2n')

lemma prioToL1Index_bits_low_high_eq:
  "\<lbrakk> pa \<noteq> p; prioToL1Index pa = prioToL1Index (p::priority) \<rbrakk>
   \<Longrightarrow>  unat (pa && mask wordRadix) \<noteq> unat (p && mask wordRadix)"
  unfolding prioToL1Index_def
  by (fastforce simp: nth_w2p wordRadix_def is_up bits_low_high_eq)

lemma prioToL1Index_bit_not_set[TcbAcc_R_assms]:
  "\<not> (~~ ((2 :: machine_word) ^ prioToL1Index p)) !! prioToL1Index p"
  apply (subst word_ops_nth_size, simp_all add: prioToL1Index_bit_set del: bit_exp_iff)
  apply (fastforce simp: prioToL1Index_def wordRadix_def word_size
                  intro: order_less_le_trans[OF word_shiftr_lt])
  done

lemma prioToL1Index_complement_nth_w2p[TcbAcc_R_assms]:
  fixes p p' :: priority
  shows "(~~ ((2 :: machine_word) ^ prioToL1Index p)) !! prioToL1Index p'
          = (prioToL1Index p \<noteq> prioToL1Index p')"
  by (fastforce simp: complement_nth_w2p prioToL1Index_lt wordRadix_def word_size)+

lemma invertL1Index_eq_cancelD[TcbAcc_R_assms]:
  "\<lbrakk>  invertL1Index i = invertL1Index j ; i < l2BitmapSize ; j < l2BitmapSize \<rbrakk>
   \<Longrightarrow> i = j"
   by (simp add: invertL1Index_def l2BitmapSize_def')

lemma pspace_dom_dom[TcbAcc_R_assms]:
  "dom ps \<subseteq> pspace_dom ps"
  unfolding pspace_dom_def
  apply clarsimp
  apply (rule rev_bexI[OF domI], assumption)
  apply (simp add: obj_relation_cuts_def2 image_Collect cte_map_def range_composition[symmetric]
              split: Structures_A.kernel_object.splits arch_kernel_obj.splits
              cong: arch_kernel_obj.case_cong)
  apply safe
     apply (drule wf_cs_0)
     apply clarsimp
     apply (rule_tac x = n in exI)
     apply (clarsimp simp: of_bl_def)
    apply (rule range_eqI[where x = 0], simp)+
  apply (rename_tac vmpage_size)
  apply (rule exI[where x = 0])
  apply (case_tac vmpage_size, simp_all add: bit_simps)
  done

lemmas [TcbAcc_R_assms] =
  dmo_getirq_inv
  getActiveIRQ_masked
  tcb_at'_cross
  pspace_relation_update_tcbs

end (* Arch *)

interpretation TcbAcc_R?: TcbAcc_R
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact TcbAcc_R_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems TcbAcc_R_2_assms

lemmas asUser_typ_ats[wp] = typ_at_lifts[OF asUser_typ_at']

lemma threadSet_invs_trivialT:
  assumes
    "\<forall>tcb. \<forall>(getF,setF) \<in> ran tcb_cte_cases. getF (F tcb) = getF tcb"
    "\<forall>tcb. tcbState (F tcb) = tcbState tcb"
    "\<forall>tcb. is_aligned (tcbIPCBuffer tcb) msg_align_bits
           \<longrightarrow> is_aligned (tcbIPCBuffer (F tcb)) msg_align_bits"
    "\<forall>tcb. tcbBoundNotification (F tcb) = tcbBoundNotification tcb"
    "\<forall>tcb. tcbSchedPrev (F tcb) = tcbSchedPrev tcb"
    "\<forall>tcb. tcbSchedNext (F tcb) = tcbSchedNext tcb"
    "\<forall>tcb. tcbQueued (F tcb) = tcbQueued tcb"
    "\<forall>tcb. tcbDomain (F tcb) = tcbDomain tcb"
    "\<forall>tcb. tcbPriority (F tcb) = tcbPriority tcb"
    "\<forall>tcb. tcbMCP tcb \<le> maxPriority \<longrightarrow> tcbMCP (F tcb) \<le> maxPriority"
    "\<forall>tcb. tcbFlags tcb && ~~ tcbFlagMask = 0 \<longrightarrow> tcbFlags (F tcb) && ~~ tcbFlagMask = 0"
  shows "threadSet F t \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def split del: if_split)
  apply (wp threadSet_valid_pspace'T
            threadSet_sch_actT_P[where P=False, simplified]
            threadSet_state_refs_of'T[where f'=id]
            threadSet_state_hyp_refs_of'
            threadSet_iflive'T
            threadSet_ifunsafe'T
            threadSet_idle'T
            threadSet_global_refsT
            irqs_masked_lift
            valid_irq_node_lift
            valid_irq_handlers_lift''
            threadSet_ctes_ofT
            threadSet_not_inQ
            threadSet_ct_idle_or_in_cur_domain'
            threadSet_valid_dom_schedule'
            threadSet_cur
            untyped_ranges_zero_lift
            sym_heap_sched_pointers_lift threadSet_valid_sched_pointers
            threadSet_tcbQueued
            threadSet_tcbSchedPrevs_of threadSet_tcbSchedNexts_of valid_bitmaps_lift
         | clarsimp simp: assms cteCaps_of_def valid_arch_tcb'_def | rule refl)+
  apply (clarsimp simp: o_def)
  by (auto simp: assms obj_at'_def)

lemmas threadSet_invs_trivial =
    threadSet_invs_trivialT [OF all_tcbI all_tcbI all_tcbI all_tcbI, OF ball_tcb_cte_casesI]

(* interface lemma, but can't be done via locale *)
lemma asUser_corres':
  assumes y: "corres_underlying Id False True r \<top> \<top> f g"
  shows      "corres r (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                       (as_user t f) (asUser t g)"
proof -
  note arch_tcb_context_get_def[simp]
  note atcbContextGet_def[simp]
  note arch_tcb_context_set_def[simp]
  note atcbContextSet_def[simp]
  have L1: "corres (\<lambda>tcb con. (arch_tcb_context_get o tcb_arch) tcb = con)
              (tcb_at t and pspace_aligned and pspace_distinct) \<top>
              (gets_the (get_tcb t)) (threadGet (atcbContextGet o tcbArch) t)"
    apply (rule corres_cross_over_guard[where Q="tcb_at' t"])
     apply (fastforce simp: tcb_at_cross state_relation_def)
    apply (rule corres_guard_imp)
      apply (rule corres_gets_the)
      apply (simp add: threadGet_def)
      apply (rule corres_rel_imp [OF corres_get_tcb])
      apply (simp add: tcb_relation_def arch_tcb_relation_def)
     apply (simp add: tcb_at_def)+
    done
  have L2: "\<And>tcb tcb' con con'. \<lbrakk> tcb_relation tcb tcb'; con = con'\<rbrakk>
              \<Longrightarrow> tcb_relation (tcb \<lparr> tcb_arch := arch_tcb_context_set con (tcb_arch tcb) \<rparr>)
                               (tcb' \<lparr> tcbArch := atcbContextSet con' (tcbArch tcb') \<rparr>)"
    by (simp add: tcb_relation_def arch_tcb_relation_def)
  have L3: "\<And>r add tcb tcb' con con'. \<lbrakk> r () (); con = con'\<rbrakk> \<Longrightarrow>
            corres r (\<lambda>s. get_tcb add s = Some tcb)
                     (\<lambda>s'. (tcb', s') \<in> fst (getObject add s'))
                     (set_object add (TCB (tcb \<lparr> tcb_arch := arch_tcb_context_set con (tcb_arch tcb) \<rparr>)))
                     (setObject add (tcb' \<lparr> tcbArch := atcbContextSet con' (tcbArch tcb') \<rparr>))"
    by (rule setObject_update_TCB_corres [OF L2],
        (simp add: tcb_cte_cases_def tcb_cap_cases_def cteSizeBits_def)+)
  have L4: "\<And>con con'. con = con' \<Longrightarrow>
            corres (\<lambda>(irv, nc) (irv', nc'). r irv irv' \<and> nc = nc')
                   \<top> \<top> (select_f (f con)) (select_f (g con'))"
    using y
    by (fastforce simp: corres_underlying_def select_f_def split_def Id_def)
  show ?thesis
    apply (rule corres_cross_over_guard[where Q="tcb_at' t"])
     apply (fastforce simp: tcb_at_cross state_relation_def)
    apply (simp add: as_user_def asUser_def)
    apply (rule corres_guard_imp)
      apply (rule_tac r'="\<lambda>tcb con. (arch_tcb_context_get o tcb_arch) tcb = con"
              in corres_split)
         apply simp
         apply (rule L1[simplified])
        apply (rule corres_split[OF L4])
           apply simp
          apply clarsimp
          apply (rule corres_split_nor)
             apply (simp add: threadSet_def)
             apply (rule corres_symb_exec_r)
                apply (rule L3[simplified])
                 prefer 5
                 apply (rule no_fail_pre_and, wp)
                apply (wp select_f_inv | simp)+
    done
qed

(* interface lemma, but can't be done via locale *)
lemma asUser_corres:
  assumes y: "corres_underlying Id False True r \<top> \<top> f g"
  shows      "corres r (tcb_at t and invs) invs' (as_user t f) (asUser t g)"
  apply (rule corres_guard_imp)
    apply (rule asUser_corres'[OF y])
   apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  done

lemma asUser_getRegister_corres[TcbAcc_R_2_assms]:
 "corres (=) (tcb_at t and pspace_aligned and pspace_distinct) \<top>
        (as_user t (getRegister r)) (asUser t (getRegister r))"
  apply (rule asUser_corres')
  apply (clarsimp simp: getRegister_def)
  done

lemma user_getreg_inv'[TcbAcc_R_2_assms, wp]:
  "\<lbrace>P\<rbrace> asUser t (getRegister r) \<lbrace>\<lambda>x. P\<rbrace>"
  apply (rule asUser_inv)
   apply (simp_all add: getRegister_def)
  done

lemma asUser_invs[wp]:
  "\<lbrace>invs' and tcb_at' t\<rbrace> asUser t m \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  apply (wp threadSet_invs_trivial hoare_drop_imps | simp)+
  done

(* interface lemma, but can't be done via locale *)
lemma asUser_valid_objs[wp]:
  "\<lbrace>valid_objs'\<rbrace> asUser t f \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  by (simp add: asUser_def split_def)
     (wpsimp wp: threadSet_valid_objs' hoare_drop_imps
             simp: valid_tcb'_def tcb_cte_cases_def valid_arch_tcb'_def cteSizeBits_def
                   atcbContextSet_def)+

lemma asUser_valid_pspace'[wp]:
  "\<lbrace>valid_pspace'\<rbrace> asUser t m \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: asUser_def)
  apply (wpsimp wp: threadSet_valid_pspace' hoare_drop_imps
                simp: atcbContextSet_def valid_arch_tcb'_def)+
  done

lemma asUser_st_hyp_refs_of'[wp]:
  "asUser t m \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  unfolding asUser_def
  by (wpsimp wp: threadSet_state_hyp_refs_of' hoare_drop_imps simp: atcbContextSet_def)

lemma asUser_iflive'[wp]:
  "asUser t m \<lbrace>if_live_then_nonz_cap'\<rbrace> "
  unfolding asUser_def
  by (wpsimp wp: threadSet_iflive' hoare_drop_imps, auto)

lemma asUser_setRegister_corres:
  "corres dc (tcb_at t and pspace_aligned and pspace_distinct) \<top>
             (as_user t (setRegister r v))
             (asUser t (setRegister r v))"
  apply (simp add: setRegister_def)
  apply (rule asUser_corres')
  apply (rule corres_modify'; simp)
  done

lemma removeFromBitmap_bitmapQ_no_L1_orphans[TcbAcc_R_2_assms, wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> removeFromBitmap d p \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  unfolding bitmap_fun_defs
  apply (wp | simp add: bitmap_fun_defs bitmapQ_no_L1_orphans_def)+
  apply (fastforce simp: invertL1Index_eq_cancel prioToL1Index_bit_not_set
                         prioToL1Index_complement_nth_w2p)
  done

lemma removeFromBitmap_bitmapQ_no_L2_orphans[TcbAcc_R_2_assms, wp]:
  "\<lbrace> bitmapQ_no_L2_orphans and bitmapQ_no_L1_orphans \<rbrace>
   removeFromBitmap d p
   \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  unfolding bitmap_fun_defs
  apply (wp, clarsimp simp: bitmap_fun_defs bitmapQ_no_L2_orphans_def)+
  apply (rule conjI, clarsimp)
   apply (clarsimp simp: complement_nth_w2p l2BitmapSize_def')
  apply clarsimp
  apply metis
  done

lemma removeFromBitmap_valid_bitmapQ_except[TcbAcc_R_2_assms]:
  "\<lbrace> valid_bitmapQ_except d p \<rbrace>
   removeFromBitmap d p
   \<lbrace>\<lambda>_. valid_bitmapQ_except d p \<rbrace>"
proof -
  have unat_ucast_mask[simp]:
   "\<And>x. unat ((ucast (p::priority) :: machine_word) && mask x) = unat (p && mask x)"
   by (simp add: ucast_and_mask[symmetric] unat_ucast_upcast is_up)

  note bit_exp_iff[simp del] bit_not_iff[simp del] bit_not_exp_iff[simp del]
  show ?thesis
  unfolding removeFromBitmap_def
  apply (simp add: let_into_return[symmetric])
  unfolding bitmap_fun_defs when_def
  apply wp
  apply clarsimp
  apply (rule conjI)
   (* after clearing bit in L2, all bits in L2 field are clear *)
   apply clarsimp
   apply (subst valid_bitmapQ_except_def, clarsimp)+
   apply (clarsimp simp: bitmapQ_def)
   apply (rule conjI; clarsimp)
    apply (rename_tac p')
    apply (rule conjI; clarsimp simp: invertL1Index_eq_cancel)
     apply (drule_tac p=p' in valid_bitmapQ_exceptE[where d=d], clarsimp)
     apply (clarsimp simp: bitmapQ_def)
     apply (drule_tac n'="unat (p' && mask wordRadix)" in no_other_bits_set)
        apply (erule (1) prioToL1Index_bits_low_high_eq)
       apply (rule order_less_le_trans[OF word_unat_mask_lt])
        apply ((simp add: wordRadix_def' word_size)+)[2]
      apply (rule order_less_le_trans[OF word_unat_mask_lt])
       apply ((simp add: wordRadix_def' word_size)+)[3]
    apply (drule_tac p=p' and d=d in valid_bitmapQ_exceptE, simp)
    apply (clarsimp simp: bitmapQ_def prioToL1Index_complement_nth_w2p)
   apply (drule_tac p=pa and d=da in valid_bitmapQ_exceptE, simp)
   apply (clarsimp simp: bitmapQ_def prioToL1Index_complement_nth_w2p)
  (* after clearing bit in L2, some bits in L2 field are still set *)
  apply clarsimp
  apply (subst valid_bitmapQ_except_def, clarsimp)+
  apply (clarsimp simp: bitmapQ_def invertL1Index_eq_cancel)
  apply (rule conjI; clarsimp)
   apply (frule (1) prioToL1Index_bits_low_high_eq)
   apply (drule_tac d=d and p=pa in valid_bitmapQ_exceptE, simp)
   apply (clarsimp simp: bitmapQ_def)
   apply (subst complement_nth_w2p)
    apply (rule order_less_le_trans[OF word_unat_mask_lt])
     apply ((simp add: wordRadix_def' word_size)+)[3]
  apply (clarsimp simp: valid_bitmapQ_except_def bitmapQ_def)
  done
qed

lemma addToBitmap_bitmapQ_no_L1_orphans[TcbAcc_R_2_assms, wp]:
  "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> addToBitmap d p \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  unfolding bitmap_fun_defs bitmapQ_defs
  using word_unat_mask_lt[where w=p and m=wordRadix]
  apply wp
  apply (clarsimp simp: word_or_zero prioToL1Index_bit_set ucast_and_mask[symmetric]
                        unat_ucast_upcast is_up wordRadix_def' word_size nth_w2p
                        wordBits_def numPriorities_def)
  done

lemma addToBitmap_valid_bitmapQ_except[TcbAcc_R_2_assms]:
  "\<lbrace> valid_bitmapQ_except d p and bitmapQ_no_L2_orphans \<rbrace>
     addToBitmap d p
   \<lbrace>\<lambda>_. valid_bitmapQ_except d p \<rbrace>"
  unfolding bitmap_fun_defs bitmapQ_defs
  apply wp
  apply (clarsimp simp: bitmapQ_def invertL1Index_eq_cancel
                        ucast_and_mask[symmetric] unat_ucast_upcast is_up nth_w2p)
  apply (fastforce simp: priority_mask_wordRadix_size[simplified wordBits_def']
                   dest: prioToL1Index_bits_low_high_eq)
  done

lemma valid_ipc_buffer_ptr'D:
  assumes yv: "y < unat max_ipc_words"
  and    buf: "valid_ipc_buffer_ptr' a s"
  shows "pointerInUserData (a + of_nat y * 8) s"
  using buf unfolding valid_ipc_buffer_ptr'_def pointerInUserData_def
  apply clarsimp
  apply (subgoal_tac
         "(a + of_nat y * 8) && ~~ mask pageBits = a  && ~~ mask pageBits")
   apply simp
  apply (rule mask_out_first_mask_some [where n = msg_align_bits])
   apply (erule is_aligned_add_helper [THEN conjunct2])
   apply (rule word_less_power_trans_ofnat [where k = 3, simplified])
     apply (rule order_less_le_trans [OF yv])
     apply (simp add: msg_align_bits max_ipc_words)
    apply (simp add: msg_align_bits)
   apply (simp_all add: msg_align_bits pageBits_def)
  done

lemma in_user_frame_eq:
  assumes y: "y < unat max_ipc_words"
  and    al: "is_aligned a msg_align_bits"
  shows "in_user_frame (a + of_nat y * 8) s = in_user_frame a s"
proof -
  have "\<And>sz. (a + of_nat y * 8) && ~~ mask (pageBitsForSize sz) =
             a && ~~ mask (pageBitsForSize sz)"
  apply (rule mask_out_first_mask_some [where n = msg_align_bits])
   apply (rule is_aligned_add_helper [OF al, THEN conjunct2])
   apply (rule word_less_power_trans_ofnat [where k = 3, simplified])
     apply (rule order_less_le_trans [OF y])
     apply (simp add: msg_align_bits max_ipc_words)
    apply (simp add: msg_align_bits)
   apply (simp add: msg_align_bits pageBits_def)
  apply (case_tac sz, simp_all add: msg_align_bits bit_simps)
  done

  thus ?thesis by (simp add: in_user_frame_def)
qed

lemma loadWordUser_corres:
  assumes y: "y < unat max_ipc_words"
  shows "corres (=) \<top> (valid_ipc_buffer_ptr' a) (load_word_offs a y) (loadWordUser (a + of_nat y * 8))"
  unfolding loadWordUser_def
  apply (rule corres_stateAssert_assume [rotated])
   apply (erule valid_ipc_buffer_ptr'D[OF y])
  apply (rule corres_guard_imp)
    apply (simp add: load_word_offs_def word_size_def)
    apply (rule_tac F = "is_aligned a msg_align_bits" in corres_gen_asm2)
    apply (rule corres_machine_op)
    apply (rule corres_Id [OF refl refl])
    apply (rule no_fail_pre)
     apply wp
    apply (simp add: word_size_bits_def)
    apply (erule aligned_add_aligned)
      apply (rule is_aligned_mult_triv2[where n = 3, simplified])
      apply (simp add: word_bits_conv msg_align_bits)+
  apply (simp add: valid_ipc_buffer_ptr'_def msg_align_bits)
  done

lemma storeWordUser_corres:
  assumes y: "y < unat max_ipc_words"
  shows "corres dc (in_user_frame a) (valid_ipc_buffer_ptr' a)
                   (store_word_offs a y w) (storeWordUser (a + of_nat y * 8) w)"
  apply (simp add: storeWordUser_def bind_assoc[symmetric]
                   store_word_offs_def word_size_def)
  apply (rule corres_guard2_imp)
   apply (rule_tac F = "is_aligned a msg_align_bits" in corres_gen_asm2)
   apply (rule corres_guard1_imp)
    apply (rule_tac r'=dc in corres_split)
       apply (simp add: stateAssert_def)
       apply (rule_tac r'=dc in corres_split)
          apply (rule corres_trivial)
          apply simp
         apply (rule corres_assert)
        apply wp+
      apply (rule corres_machine_op)
      apply (rule corres_Id [OF refl])
       apply simp
      apply (rule no_fail_pre)
       apply (wp no_fail_storeWord)
      apply (erule_tac n=msg_align_bits in aligned_add_aligned)
       apply (rule is_aligned_mult_triv2 [where n = 3, simplified])
      apply (simp add: word_bits_conv msg_align_bits)+
     apply wp+
   apply (simp add: in_user_frame_eq[OF y])
  apply simp
  apply (rule conjI)
   apply (frule (1) valid_ipc_buffer_ptr'D [OF y])
  apply (simp add: valid_ipc_buffer_ptr'_def)
  done

lemmas msgRegisters_unfold
  = X64_H.msgRegisters_def
    X64_A.msg_registers_def
    X64.msgRegisters_def
        [unfolded upto_enum_def, simplified,
         unfolded fromEnum_def enum_register, simplified,
         unfolded toEnum_def enum_register, simplified]

lemma thread_get_registers:
  "thread_get (arch_tcb_get_registers \<circ> tcb_arch) t = as_user t (gets user_regs)"
  apply (simp add: thread_get_def as_user_def arch_tcb_get_registers_def
                   arch_tcb_context_get_def arch_tcb_context_set_def)
  apply (rule bind_cong [OF refl])
  apply (clarsimp simp: gets_the_member)
  apply (simp add: get_def the_run_state_def set_object_def get_object_def
                   put_def bind_def return_def gets_def)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: map_upd_triv select_f_def image_def return_def)
  done

lemma getMRs_corres:
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct)
              (case_option \<top> valid_ipc_buffer_ptr' buf)
              (get_mrs t buf mi) (getMRs t buf (message_info_map mi))"
  proof -
  have S: "get = gets id"
    by (simp add: gets_def)
  have T: "corres (\<lambda>con regs. regs = map con msg_registers)
                  (tcb_at t and pspace_aligned and pspace_distinct) \<top>
                  (thread_get (arch_tcb_get_registers o tcb_arch) t)
                  (asUser t (mapM getRegister X64_H.msgRegisters))"
   apply (subst thread_get_registers)
    apply (rule asUser_corres')
    apply (subst mapM_gets)
     apply (simp add: getRegister_def)
    apply (simp add: S X64_H.msgRegisters_def msg_registers_def)
    done
  show ?thesis
  apply (case_tac mi, simp add: get_mrs_def getMRs_def split del: if_split)
  apply (case_tac buf)
   apply (rule corres_guard_imp)
     apply (rule corres_split [where R = "\<lambda>_. \<top>" and R' =  "\<lambda>_. \<top>", OF T])
       apply simp
      apply wp+
    apply simp
   apply simp
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF T])
      apply (simp only: option.simps return_bind fun_app_def
                        load_word_offs_def doMachineOp_mapM loadWord_empty_fail)
      apply (rule corres_split_eqr)
         apply (simp only: mapM_map_simp msgMaxLength_def msgLengthBits_def
                           msg_max_length_def o_def upto_enum_word)
         apply (rule corres_mapM [where r'="(=)" and S="{a. fst a = snd a \<and> fst a < unat max_ipc_words}"])
               apply simp
              apply simp
             apply (simp add: word_size wordSize_def wordBits_def)
             apply (rule loadWordUser_corres)
             apply simp
            apply wp+
          apply simp
          apply (unfold msgRegisters_unfold)[1]
          apply simp
         apply (clarsimp simp: set_zip)
         apply (simp add: msgRegisters_unfold max_ipc_words nth_append)
        apply (rule corres_trivial, simp)
       apply (wp hoare_vcg_all_lift | simp add: valid_ipc_buffer_ptr'_def)+
  done
qed

lemma thread_set_as_user_registers:
  "thread_set (\<lambda>tcb. tcb \<lparr> tcb_arch := arch_tcb_set_registers (f (arch_tcb_get_registers (tcb_arch tcb)))
                          (tcb_arch tcb) \<rparr>) t
    = as_user t (modify (modify_registers f))"
proof -
  have P: "\<And>f. det (modify f)"
    by (simp add: modify_def)
  thus ?thesis
    apply (simp add: as_user_def P thread_set_def)
    apply (clarsimp simp: select_f_def simpler_modify_def bind_def image_def modify_registers_def
                          arch_tcb_set_registers_def arch_tcb_get_registers_def
                          arch_tcb_context_set_def arch_tcb_context_get_def)
    done
qed

lemma UserContext_fold:
  "UserContext (user_fpu_state s) (foldl (\<lambda>s (x, y). s(x := y)) (user_regs s) xs) =
   foldl (\<lambda>s (r, v). UserContext (user_fpu_state s) ((user_regs s)(r := v))) s xs"
  apply (induct xs arbitrary: s; simp)
  apply (clarsimp split: prod.splits)
  apply (metis user_context.sel)
  done

lemma setMRs_corres:
  assumes m: "mrs' = mrs"
  shows
  "corres (=) (tcb_at t and pspace_aligned and pspace_distinct and case_option \<top> in_user_frame buf)
              (case_option \<top> valid_ipc_buffer_ptr' buf)
              (set_mrs t buf mrs) (setMRs t buf mrs')"
proof -
  have setRegister_def2:
    "setRegister = (\<lambda>r v.  modify (\<lambda>s. UserContext (user_fpu_state s) ((user_regs s)(r := v))))"
    by ((rule ext)+, simp add: setRegister_def)

  have S: "\<And>xs ys n m. m - n \<ge> length xs \<Longrightarrow> (zip xs (drop n (take m ys))) = zip xs (drop n ys)"
    by (simp add: zip_take_triv2 drop_take)

  note upt.simps[simp del] upt_rec_numeral[simp del]

  show ?thesis using m
    unfolding setMRs_def set_mrs_def
    apply (clarsimp  cong: option.case_cong split del: if_split)
    apply (subst bind_assoc[symmetric])
    apply (fold thread_set_def[simplified])
    apply (subst thread_set_as_user_registers)
    apply (cases buf)
     apply (clarsimp simp: msgRegisters_unfold setRegister_def2 zipWithM_x_modify
                           take_min_len zip_take_triv2 min.commute)
     apply (rule corres_guard_imp)
       apply (rule corres_split_nor[OF asUser_corres'])
         apply (rule corres_modify')
          apply (fastforce simp: fold_fun_upd[symmetric] msgRegisters_unfold UserContext_fold
                                 modify_registers_def
                           cong: if_cong simp del: the_index.simps)
          apply simp
         apply (rule corres_trivial, simp)
         apply ((wp |simp)+)[4]
    \<comment> \<open>buf = Some a\<close>
    using if_split[split del]
    apply (clarsimp simp: msgRegisters_unfold setRegister_def2 zipWithM_x_modify
                          take_min_len zip_take_triv2 min.commute
                          msgMaxLength_def msgLengthBits_def)
    apply (simp add: msg_max_length_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split_nor[OF asUser_corres'])
         apply (rule corres_modify')
          apply (simp only: msgRegisters_unfold cong: if_cong)
          apply (fastforce simp: fold_fun_upd[symmetric] modify_registers_def UserContext_fold)
         apply simp
        apply (rule corres_split_nor)
           apply (rule_tac S="{((x, y), (x', y')). y = y' \<and> x' = (a + (of_nat x * 8)) \<and> x < unat max_ipc_words}"
                         in zipWithM_x_corres)
               apply (fastforce intro: storeWordUser_corres)
              apply wp+
            apply (clarsimp simp add: S msgMaxLength_def msg_max_length_def set_zip)
            apply (simp add: wordSize_def wordBits_def word_size max_ipc_words
                              upt_Suc_append[symmetric] upto_enum_word)
           apply simp
          apply (rule corres_trivial, clarsimp simp: min.commute)
         apply wp+
      apply (wp | clarsimp simp: valid_ipc_buffer_ptr'_def)+
    done
qed

lemma copyMRs_corres:
  "corres (=) (tcb_at s and tcb_at r and pspace_aligned and pspace_distinct
               and case_option \<top> in_user_frame sb
               and case_option \<top> in_user_frame rb
               and K (unat n \<le> msg_max_length))
              (case_option \<top> valid_ipc_buffer_ptr' sb
               and case_option \<top> valid_ipc_buffer_ptr' rb)
              (copy_mrs s sb r rb n) (copyMRs s sb r rb n)"
proof -
  have U: "unat n \<le> msg_max_length \<Longrightarrow>
           map (toEnum :: nat \<Rightarrow> machine_word) [7 ..< Suc (unat n)] = map of_nat [7 ..< Suc (unat n)]"
    unfolding msg_max_length_def by auto
  note R'=msgRegisters_unfold[THEN meta_eq_to_obj_eq, THEN arg_cong[where f=length]]
  note R=R'[simplified]

  have as_user_bit:
    "\<And>v :: machine_word.
       corres dc (tcb_at s and tcb_at r and pspace_aligned and pspace_distinct)
                 \<top>
           (mapM
             (\<lambda>ra. do v \<leftarrow> as_user s (getRegister ra);
                      as_user r (setRegister ra v)
                   od)
             (take (unat n) msg_registers))
           (mapM
             (\<lambda>ra. do v \<leftarrow> asUser s (getRegister ra);
                      asUser r (setRegister ra v)
                   od)
             (take (unat n) msgRegisters))"
    apply (rule corres_guard_imp)
    apply (rule_tac S=Id in corres_mapM, simp+)
        apply (rule corres_split_eqr[OF asUser_getRegister_corres asUser_setRegister_corres])
        apply (wp | clarsimp simp: msg_registers_def msgRegisters_def)+
        done

  have wordSize[simp]: "of_nat wordSize = 8"
    by (simp add: wordSize_def wordBits_def word_size)

  show ?thesis
    apply (rule corres_assume_pre)
    apply (simp add: copy_mrs_def copyMRs_def word_size
               cong: option.case_cong
          split del: if_split del: upt.simps)
    apply (cases sb)
     apply (simp add: R)
     apply (rule corres_guard_imp)
       apply (rule corres_split_nor[OF as_user_bit])
         apply (rule corres_trivial, simp)
        apply wp+
      apply simp
     apply simp
    apply (cases rb)
     apply (simp add: R)
     apply (rule corres_guard_imp)
       apply (rule corres_split_nor[OF as_user_bit])
         apply (rule corres_trivial, simp)
        apply wp+
      apply simp
     apply simp
    apply (simp add: R del: upt.simps)
    apply (rule corres_guard_imp)
      apply (rename_tac sb_ptr rb_ptr)
      apply (rule corres_split_nor[OF as_user_bit])
        apply (rule corres_split_eqr)
           apply (rule_tac S="{(x, y). y = of_nat x \<and> x < unat max_ipc_words}"
                   in corres_mapM, simp+)
               apply (rule corres_split_eqr)
                  apply (rule loadWordUser_corres)
                  apply simp
                 apply (rule storeWordUser_corres)
                 apply simp
                apply (wp hoare_vcg_all_lift | simp)+
            apply (clarsimp simp: upto_enum_def)
            apply arith
           apply (subst set_zip)
           apply (simp add: upto_enum_def U del: upt.simps)
           apply (clarsimp simp del: upt.simps)
           apply (clarsimp simp: msg_max_length_def word_le_nat_alt nth_append
                                 max_ipc_words)
           apply (erule order_less_trans)
           apply simp
          apply (rule corres_trivial, simp)
         apply (wp hoare_vcg_all_lift mapM_wp'
                | simp add: valid_ipc_buffer_ptr'_def)+
    done
qed

lemma cte_at_tcb_at_32': (* FIXME arch-split: can't be generic with this 32 *)
  "tcb_at' t s \<Longrightarrow> cte_at' (t + 32) s"
  by (simp add: cte_at'_obj_at' tcb_cte_cases_def cteSizeBits_def)

lemmas valid_ipc_buffer_cap_simps = valid_ipc_buffer_cap_def [split_simps cap.split arch_cap.split]

lemma lookupIPCBuffer_corres'[TcbAcc_R_2_assms]:
  "corres (=) (tcb_at t and valid_objs and pspace_aligned and pspace_distinct)
               (valid_objs' and no_0_obj')
               (lookup_ipc_buffer w t) (lookupIPCBuffer w t)"
  apply (rule corres_cross_add_guard[where Q'="pspace_aligned' and pspace_distinct'"])
   apply (fastforce simp: pspace_aligned_cross pspace_distinct_cross state_relation_def)
  apply (simp add: lookup_ipc_buffer_def X64_H.lookupIPCBuffer_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF threadGet_corres])
       apply (simp add: tcb_relation_def)
      apply (simp add: getThreadBufferSlot_def locateSlot_conv)
      apply (rule corres_split[OF getSlotCap_corres])
         apply (simp add: cte_map_def tcb_cnode_index_def cte_level_bits_def tcbIPCBufferSlot_def)
        apply (rule_tac F="valid_ipc_buffer_cap rv buffer_ptr"
                    in corres_gen_asm)
        apply (rule_tac P="valid_cap rv" and Q="no_0_obj'"
                    in corres_assume_pre)
        apply (simp add: Let_def split: cap.split arch_cap.split
              split del: if_split cong: if_cong)
        apply (safe, simp_all add: isCap_simps valid_ipc_buffer_cap_simps split:bool.split_asm)[1]
        apply (rename_tac word rights mt vmpage_size option)
        apply (subgoal_tac "word + (buffer_ptr &&
                                    mask (pageBitsForSize vmpage_size)) \<noteq> 0")
         apply (simp add: cap_aligned_def
                          valid_ipc_buffer_cap_def
                          vmrights_map_def vm_read_only_def vm_read_write_def)
        apply auto[1]
        apply (subgoal_tac "word \<noteq> 0")
         apply (subgoal_tac "word \<le> word + (buffer_ptr &&
                               mask (pageBitsForSize vmpage_size))")
          apply fastforce
         apply (rule_tac b="2 ^ (pageBitsForSize vmpage_size) - 1"
                   in word_plus_mono_right2)
          apply (clarsimp simp: valid_cap_def cap_aligned_def
                        intro!: is_aligned_no_overflow')
         apply (clarsimp simp: word_bits_def bit_simps
                       intro!: word_less_sub_1 and_mask_less')
         apply (case_tac vmpage_size, simp_all add: bit_simps)[1]
        apply (drule state_relation_pspace_relation)
        apply (clarsimp simp: valid_cap_def obj_at_def no_0_obj_kheap
                              obj_relation_cuts_def3 no_0_obj'_def
                       split: if_split_asm)
       apply (wp get_cap_valid_ipc get_cap_aligned)+
     apply (wp thread_get_obj_at_eq)+
   apply (clarsimp elim!: tcb_at_cte_at)
  apply clarsimp
  done

crunch lookupIPCBuffer
  for inv[wp]: P
  (wp: crunch_wps simp: crunch_simps)

crunch rescheduleRequired, tcbSchedEnqueue
  for hyp_refs_of'[wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  (simp: unless_def crunch_simps wp: threadSet_state_hyp_refs_of' ignore: threadSet)

lemmas [TcbAcc_R_2_assms] =
  lookupIPCBuffer_inv
  rescheduleRequired_hyp_refs_of'
  tcbSchedEnqueue_hyp_refs_of'

lemma setThreadState_state_hyp_refs_of'[TcbAcc_R_2_assms, wp]:
  "\<lbrace>\<lambda>s. P ((state_hyp_refs_of' s))\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  apply (simp add: setThreadState_def fun_upd_def
        | wp threadSet_state_hyp_refs_of')+
  done

lemma setBoundNotification_state_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of' s) (t := tcb_bound_refs' ntfn
                                 \<union> {r \<in> state_refs_of' s t. snd r \<noteq> TCBBound}))\<rbrace>
     setBoundNotification ntfn t
   \<lbrace>\<lambda>rv s. P (state_refs_of' s)\<rbrace>"
  by (simp add: setBoundNotification_def Un_commute fun_upd_def
        | wp threadSet_state_refs_of' )+

lemma setBoundNotification_state_hyp_refs_of'[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>
     setBoundNotification ntfn t
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of' s)\<rbrace>"
  by (simp add: setBoundNotification_def fun_upd_def
        | wp threadSet_state_hyp_refs_of')+

lemma tcbSchedNext_update_iflive'[TcbAcc_R_2_assms]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> ex_nonz_cap_to' t s\<rbrace>
   threadSet (tcbSchedNext_update f) t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: threadSet_iflive'T simp: update_tcb_cte_cases)

lemma tcbSchedPrev_update_iflive'[TcbAcc_R_2_assms]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> ex_nonz_cap_to' t s\<rbrace>
   threadSet (tcbSchedPrev_update f) t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: threadSet_iflive'T simp: update_tcb_cte_cases)

lemma tcbQueued_update_iflive'[TcbAcc_R_2_assms, wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> ex_nonz_cap_to' t s\<rbrace>
   threadSet (tcbQueued_update f) t
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  by (wpsimp wp: threadSet_iflive'T simp: update_tcb_cte_cases)

lemma sbn_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> (bound ntfn \<longrightarrow> ex_nonz_cap_to' t s)\<rbrace>
     setBoundNotification ntfn t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (rule hoare_pre)
   apply (wp threadSet_iflive' | simp)+
  apply auto
  done

lemma storeWord_invs'[TcbAcc_R_2_assms, wp]:
  "\<lbrace>pointerInUserData p and invs'\<rbrace> doMachineOp (storeWord p w) \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>l. l<8 \<Longrightarrow> p && mask word_size_bits = 0 \<Longrightarrow> p + l && ~~ mask 12 = p && ~~ mask 12"
  proof -
    fix l
    assume al: "p && mask word_size_bits = 0"
    assume "(l::machine_word) < 8" hence less: "l<2^word_size_bits" by (simp add: word_size_bits_def)
    have le: "(word_size_bits::nat) \<le> 12" by (simp add: word_size_bits_def)
    show "?thesis l"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs' no_irq_storeWord no_irq)
    apply (clarsimp simp: storeWord_def invs'_def valid_state'_def)
    apply (clarsimp simp: valid_machine_state'_def pointerInUserData_def
                          assert_def simpler_modify_def fail_def bind_def return_def
                          aligned_offset_ignore bit_simps upto0_7_def
            split: if_split_asm)
  done
qed

lemma storeWord_invs_no_cicd'[TcbAcc_R_2_assms, wp]:
  "\<lbrace>pointerInUserData p and invs_no_cicd'\<rbrace> doMachineOp (storeWord p w) \<lbrace>\<lambda>rv. invs_no_cicd'\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>l. l<8 \<Longrightarrow> p && mask 3 = 0 \<Longrightarrow> p + l && ~~ mask 12 = p && ~~ mask 12"
  proof -
    fix l
    assume al: "p && mask 3 = 0"
    assume "(l::machine_word) < 8" hence less: "l<2^3" by simp
    have le: "(3::nat) \<le> 12" by simp
    show "?thesis l"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs_no_cicd' no_irq_storeWord no_irq)
    apply (clarsimp simp: storeWord_def invs'_def valid_state'_def)
    apply (clarsimp simp: valid_machine_state'_def pointerInUserData_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore upto0_7_def
            split: if_split_asm)
  done
qed

crunch tcbSchedAppend
  for pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'

lemmas [TcbAcc_R_2_assms] = tcbSchedAppend_pspace_in_kernel_mappings'

end (* Arch *)

interpretation TcbAcc_R_2?: TcbAcc_R_2
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact TcbAcc_R_2_assms)?)?)
qed

context Arch begin arch_global_naming

named_theorems TcbAcc_R_3_assms

lemma sts_iflive'[TcbAcc_R_3_assms, wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
        \<and> (st \<noteq> Inactive \<and> \<not> idle' st \<longrightarrow> ex_nonz_cap_to' t s)
        \<and> pspace_aligned' s \<and> pspace_distinct' s\<rbrace>
     setThreadState st t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setThreadState_def setQueue_def)
  apply wpsimp
   apply (rule_tac Q'="\<lambda>rv. if_live_then_nonz_cap' and pspace_aligned' and pspace_distinct'"
                in hoare_post_imp)
    apply clarsimp
   apply (wpsimp wp: threadSet_iflive')
  apply fastforce
  done

lemmas setThreadState_typ_ats[wp] = typ_at_lifts [OF setThreadState_typ_at']
lemmas setBoundNotification_typ_ats[wp] = typ_at_lifts [OF setBoundNotification_typ_at']

end (* Arch *)

interpretation TcbAcc_R_3?: TcbAcc_R_3
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact TcbAcc_R_3_assms)?)?)
qed

(* requalify interface lemmas which can't be locale assumptions due to free type variable *)
arch_requalify_facts
  asUser_corres'
  asUser_corres
  asUser_valid_objs
  asUser_invs

lemmas [wp] =
  asUser_valid_objs
  asUser_invs

end
