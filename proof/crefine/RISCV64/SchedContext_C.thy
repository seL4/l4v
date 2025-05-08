(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2022, UNSW (ABN 57 195 873 197)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SchedContext_C
imports Schedule_C
begin

context kernel_m begin

lemma maybe_add_empty_tail_ccorres:
  "ccorres dc xfdc
     (active_sc_at' scPtr and invs') \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (maybeAddEmptyTail scPtr) (Call maybe_add_empty_tail_'proc)"
  apply (cinit lift: sc_')
   apply (ctac add: isRoundRobin_ccorres)
     apply (clarsimp simp: when_def)
     apply (rule ccorres_cond[where R=\<top>])
       apply (clarsimp simp: to_bool_def)
      apply (rule ccorres_rhs_assoc)
      apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s)))
                                     (ret__ptr_to_struct_refill_C_' s)"
                   in ccorres_split_nothrow)
          apply (rule ccorres_call)
             apply (rule refill_head_ccorres, clarsimp+)
         apply ceqv
        apply (rule ccorres_Guard_Seq)
        apply (rule ccorres_symb_exec_r)
          apply (ctac add: refill_add_tail_ccorres)
         apply vcg
        apply (rule conseqPre, vcg)
        apply clarsimp
       apply (wpsimp wp: getRefillHead_wp)
      apply vcg
     apply (rule ccorres_return_Skip')
    apply (wpsimp wp: isRoundRobin_wp)
   apply (vcg exspec=isRoundRobin_modifies)
  apply (rule conjI)
   apply fastforce
  apply (clarsimp simp: active_sc_at'_rewrite)
  apply (frule (1) obj_at_cslift_sc)
  apply normalise_obj_at'
  apply (rename_tac sc sc')
  apply (frule (1) invs'_ko_at_valid_sched_context')
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n="scRefillHead sc" and scPtr=scPtr in h_t_valid_refill; fastforce?)
   apply (clarsimp simp: valid_sched_context'_def obj_at'_def is_active_sc'_def in_omonad)
  apply (clarsimp simp: h_val_field_from_bytes' crefill_relation_def typ_heap_simps
                        sc_ptr_to_crefill_ptr_def csched_context_relation_def)
  done

lemma maxRefills_helper:
  "obj_at' (\<lambda>sc :: sched_context. maxRefills \<le> refillAbsoluteMax' (objBits sc)) scPtr s
   \<Longrightarrow> maxRefills < 2 ^ LENGTH(64)"
  supply len_bit0[simp del]
  apply normalise_obj_at'
  apply (rename_tac sc)
  apply (rule_tac y="refillAbsoluteMax' (objBits sc)" in le_less_trans)
   apply fastforce
  apply (clarsimp simp: obj_at'_def)
  apply (cut_tac n="objBits sc" in refillAbsoluteMax'_leq)
   apply (rule_tac y="2 ^ minSchedContextBits" in order_trans)
    apply (fastforce intro: schedContextStructSize_minSchedContextBits)
   apply (clarsimp simp: objBits_simps)
  apply (rule_tac y="2 ^ objBits sc" in le_less_trans)
   apply (fastforce simp: refillSizeBytes_def)
  apply (fastforce simp: objBits_simps word_bits_def)
  done

lemma refill_new_ccorres:
  "ccorres dc xfdc
     (invs'
      and K (0 < maxRefills)
      and obj_at' (\<lambda>sc :: sched_context. maxRefills \<le> refillAbsoluteMax' (objBits sc)) scPtr)
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> \<lbrace>\<acute>max_refills = of_nat maxRefills\<rbrace> \<inter> \<lbrace>\<acute>budget = budget\<rbrace>
      \<inter> \<lbrace>\<acute>period = period\<rbrace>) []
     (refillNew scPtr maxRefills budget period) (Call refill_new_'proc)"
  (is "ccorres _ _ ?abs _ _ _ _")
  supply len_bit0[simp del] sched_context_C_size[simp del] refill_C_size[simp del]

  apply (cinit lift: sc_' max_refills_' budget_' period_')
   apply (rule ccorres_pre_getCurTime, rename_tac curTime)
  \<comment> \<open>bundle individual updateSchedContext steps updating the scPeriod, scRefillHead, scRefillTail,
      and scRefillMax into one large updateSchedContext\<close>
   apply (rule_tac Q5="?abs and (\<lambda>s. ksCurTime s = curTime)"
                in monadic_rewrite_ccorres_assemble[rotated, where P=Q and Q=Q for Q, simplified],
          subst bind_assoc[symmetric],
          rule monadic_rewrite_bind_head,
          subst bind_dummy_ret_val,
          rule monadic_rewrite_guard_imp,
          rule updateSchedContext_decompose[THEN monadic_rewrite_sym],
          clarsimp simp: objBits_simps active_sc_at'_rewrite)+
   apply (rule stronger_ccorres_guard_imp[where A'=Q' and Q'=Q' for Q', simplified])
     apply (rule ccorres_move_c_guard_sc)
     \<comment> \<open>break off the part of the C corresponding to the bundled updateSchedContext step\<close>
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
         apply (rule updateSchedContext_ccorres_lemma3
                      [where P=\<top> and P'="K (maxRefills < 2 ^ LENGTH(64))"])
           apply (vcg exspec=refill_index_modifies)
          apply fastforce
         apply clarsimp
         apply (rule conjI)
          apply (fastforce dest: obj_at_cslift_sc simp: typ_heap_simps')
         apply (rule rf_sr_sc_update_no_refill_buffer_update2; fastforce?)
           apply (fastforce simp: typ_heap_simps' packed_heap_update_collapse_hrs)
          apply (clarsimp simp: csched_context_relation_def)
          apply (subst unat_of_nat_eq)
           apply (simp add: word_bits_def)
          apply (rule refl)
         apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
        apply ceqv
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow)
           apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
           apply (rule_tac P'="invs' and (\<lambda>s. ksCurTime s = curTime)"
                        in updateSchedContext_ccorres_lemma3
                            [where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)"])
             apply (vcg expsec=refill_head_modifies )
            apply fastforce
           apply clarsimp
           apply (rename_tac sc sc')
           apply (frule (1) obj_at_cslift_sc)
           apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
           apply (frule rf_sr_refill_buffer_relation)
           apply (intro conjI)
              apply (clarsimp simp: typ_heap_simps)
             apply (rule disjCI2)
             apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
              apply (rule sc_at_array_assertion'; assumption?)
              apply (clarsimp simp: valid_sched_context'_def MIN_REFILLS_def)
             apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
            apply (frule_tac n=0 in h_t_valid_refill; fastforce?)
              apply clarsimp
             apply fastforce
            apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps)
            apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
             apply fastforce
            apply (clarsimp simp: sc_ptr_to_crefill_ptr_def csched_context_relation_def)
           apply (clarsimp simp: ret__ptr_to_struct_refill_C_'_update_rf_sr_helper
                           cong: StateSpace.state.fold_congs)
           apply (rule_tac old_sc=sc and n="scRefillHead sc"
                       and fa="\<lambda>refill. rAmount_update (\<lambda>_. budget) refill"
                        in rf_sr_refill_update2;
                  fastforce?)
              apply (fastforce simp: sched_context.expand)
             apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
              apply fastforce
             apply (clarsimp simp: valid_sched_context'_def)
             apply (fastforce simp: typ_heap_simps sc_ptr_to_crefill_ptr_def
                                    csched_context_relation_def)
            apply (clarsimp simp: csched_context_relation_def)
           apply (drule_tac n="scRefillHead sc" in crefill_relationD; fastforce?)
           apply (fastforce simp: crefill_relation_def sc_ptr_to_crefill_ptr_def
                                  csched_context_relation_def)
          apply ceqv
         apply (rule ccorres_rhs_assoc2)
         apply (rule ccorres_split_nothrow)
             apply (clarsimp simp: setRefillHd_def updateRefillHd_def)
             apply (rule_tac P'="invs' and (\<lambda>s. ksCurTime s = curTime)"
                          in updateSchedContext_ccorres_lemma3
                              [where P="\<lambda>sc. scRefillHead sc < length (scRefills sc)"])
               apply (vcg expsec=refill_head_modifies)
              apply fastforce
             apply normalise_obj_at'
             apply (rename_tac sc sc')
             apply (frule (1) obj_at_cslift_sc)
             apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
             apply (frule rf_sr_refill_buffer_relation)
             apply (intro conjI impI allI)
                apply (clarsimp simp: ptr_add_assertion_def typ_heap_simps)
               apply (rule disjCI2)
               apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                apply (rule sc_at_array_assertion'; assumption?)
                apply (clarsimp simp: valid_sched_context'_def MIN_REFILLS_def)
               apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
              apply (frule_tac n=0 in h_t_valid_refill; fastforce?)
                apply clarsimp
               apply fastforce
              apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps)
              apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
               apply fastforce
              apply (clarsimp simp: sc_ptr_to_crefill_ptr_def csched_context_relation_def)
             apply (clarsimp simp: ret__ptr_to_struct_refill_C_'_update_rf_sr_helper
                             cong: StateSpace.state.fold_congs)
             apply (rule_tac old_sc=sc and n="scRefillHead sc"
                         and fa="\<lambda>refill. rTime_update (\<lambda>_. ksCurTime s) refill"
                          in rf_sr_refill_update2;
                    fastforce?)
                apply (fastforce simp: sched_context.expand)
               apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
                apply fastforce
               apply (clarsimp simp: valid_sched_context'_def)
               apply (fastforce simp: typ_heap_simps sc_ptr_to_crefill_ptr_def
                                      csched_context_relation_def)
              apply (clarsimp simp: csched_context_relation_def)
             apply (drule_tac n="scRefillHead sc" in crefill_relationD; fastforce?)
             apply (clarsimp simp: crefill_relation_def sc_ptr_to_crefill_ptr_def
                                   csched_context_relation_def
                            dest!: rf_sr_ksCurTime)
            apply ceqv
           apply (ctac add: maybe_add_empty_tail_ccorres)
          apply (wpsimp wp: updateRefillHd_invs')
         apply (vcg exspec=refill_head_modifies)
        apply ((rule hoare_vcg_conj_lift
                | wpsimp wp: updateRefillHd_invs'
                | wpsimp simp: updateRefillHd_def wp: updateSchedContext_wp)+)[1]
       apply (vcg exspec=refill_head_modifies)
      apply (rule_tac Q'="\<lambda>_ s. active_sc_at' scPtr s \<and> invs' s \<and> ksCurTime s = curTime
                               \<and> obj_at' (\<lambda>sc. scRefillHead sc < length (scRefills sc)) scPtr s"
                   in hoare_post_imp)
       apply (fastforce simp: obj_at'_def objBits_simps opt_map_def ps_clear_def)
      apply ((rule hoare_vcg_conj_lift
              | wpsimp wp: updateSchedContext_refills_invs'
              | wpsimp simp: updateRefillHd_def
                         wp: updateSchedContext_wp)+)[1]
     apply vcg
    defer
    apply fastforce
   apply fastforce
  apply clarsimp
  apply (frule maxRefills_helper)
  apply normalise_obj_at'
  apply (frule (1) invs'_ko_at_valid_sched_context')
  apply (fastforce simp: obj_at'_def valid_sched_context'_def opt_map_def active_sc_at'_def
                         refillSize_def objBits_simps ps_clear_def)
  done

lemma refill_update_ccorres:
  "ccorres dc xfdc
     (active_sc_at' scPtr and invs'
      and K (0 < newMaxRefills)
      and obj_at' (\<lambda>sc :: sched_context. newMaxRefills \<le> refillAbsoluteMax' (objBits sc)) scPtr)
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> \<lbrace>\<acute>new_period = newPeriod\<rbrace> \<inter> \<lbrace>\<acute>new_budget = newBudget\<rbrace>
      \<inter> \<lbrace>\<acute>new_max_refills = of_nat newMaxRefills\<rbrace>) []
     (refillUpdate scPtr newPeriod newBudget newMaxRefills) (Call refill_update_'proc)"
  supply len_bit0[simp del] sched_context_C_size[simp del] refill_C_size[simp del]

  apply (cinit lift: sc_' new_period_' new_budget_' new_max_refills_')
   \<comment> \<open>break off the part of the C corresponding to update to the scRefills field\<close>
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_rhs_assoc2)
   apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
       apply (rule updateSchedContext_ccorres_lemma3
                   [where P=\<top> and P'="invs' and active_sc_at' scPtr"])
         apply (vcg expsec=refill_index_modifies)
        apply fastforce
       apply normalise_obj_at'
       apply (rename_tac sc sc')
       apply (frule (1) obj_at_cslift_sc)
       apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
       apply (frule rf_sr_refill_buffer_relation)
       apply (intro conjI)
            apply (clarsimp simp: ptr_add_assertion_def)
           apply (clarsimp simp: typ_heap_simps)
          apply (rule disjCI2)
          apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
           apply (fastforce intro: sc_at_array_assertion'
                             simp: valid_sched_context'_def MIN_REFILLS_def)
          apply (clarsimp simp: typ_heap_simps valid_sched_context'_def obj_at'_def
                                active_sc_at'_def csched_context_relation_def)
         apply (frule_tac n=0 in h_t_valid_refill; fastforce?)
           apply (clarsimp simp: csched_context_relation_def valid_sched_context'_def
                                 active_sc_at'_def obj_at'_def)
          apply fastforce
         apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps)
        apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
          apply (clarsimp simp: csched_context_relation_def valid_sched_context'_def
                                active_sc_at'_def obj_at'_def)
         apply fastforce
        apply (clarsimp simp: sc_ptr_to_crefill_ptr_def csched_context_relation_def
                              typ_heap_simps)
       apply (clarsimp simp: ret__ptr_to_struct_refill_C_'_update_rf_sr_helper
                       cong: StateSpace.state.fold_congs)
       apply (rule_tac n=0 and fa="\<lambda>_. refillHd sc" in rf_sr_refill_update2; fastforce?)
           apply (clarsimp simp: valid_sched_context'_def MIN_REFILLS_def)
          apply (fastforce simp: sched_context.expand)
         apply (fastforce simp: typ_heap_simps' sc_ptr_to_crefill_ptr_def)
        apply (clarsimp simp: csched_context_relation_def)
       apply (drule_tac n="scRefillHead sc" in crefill_relationD; fastforce?)
        apply (clarsimp simp: csched_context_relation_def valid_sched_context'_def
                              active_sc_at'_def obj_at'_def)
       apply (clarsimp simp: sc_ptr_to_crefill_ptr_def refillHd_def csched_context_relation_def)
      apply ceqv

     \<comment> \<open>bundle all updates to the sched context into one updateSchedContext step\<close>
     apply (rule monadic_rewrite_ccorres_assemble[rotated], clarsimp,
            subst bind_assoc[symmetric],
            rule monadic_rewrite_bind_head, subst bind_dummy_ret_val,
            rule monadic_rewrite_guard_imp,
            rule updateSchedContext_decompose[THEN monadic_rewrite_sym],
            clarsimp simp: objBits_simps active_sc_at'_rewrite, assumption)+
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule ccorres_rhs_assoc2)
     apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
         \<comment> \<open>show correspondence between the updates to the sched context struct fields\<close>
         apply clarsimp
         apply (rule updateSchedContext_ccorres_lemma2[where P="K (newMaxRefills < 2 ^ word_bits)"])
           apply vcg
          apply fastforce
         apply (clarsimp simp: typ_heap_simps)
         apply (rule_tac sc'="scRefillTail_C_update (\<lambda>_. 0)
                               (scRefillHead_C_update (\<lambda>_. 0)
                                (scRefillMax_C_update (\<lambda>_. word_of_nat newMaxRefills)
                                 (scPeriod_C_update (\<lambda>_. newPeriod) sc')))"
                      in rf_sr_sc_update_no_refill_buffer_update2;
                fastforce?)
           apply (clarsimp simp: typ_heap_simps' packed_heap_update_collapse_hrs)
          apply (fastforce simp: csched_context_relation_def unat_of_nat_eq word_bits_def)
         apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
        apply ceqv

       apply (clarsimp simp: whenM_def ifM_def bind_assoc)
       apply (ctac add: refill_ready_ccorres)
         apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
             apply (rule ccorres_cond[where R=\<top>])
               apply (clarsimp simp: to_bool_def)
              apply (rule ccorres_pre_getCurTime, rename_tac curTime)
              apply (clarsimp simp: updateRefillHd_def)
              apply (rule_tac P=\<top>
                          and P'="\<lambda>s. ksCurTime s = curTime \<and> invs' s \<and> active_sc_at' scPtr s"
                          and Q="\<lambda>s sc. {s'. (s, s') \<in> rf_sr \<and> ko_at' sc scPtr s \<and> invs' s
                                             \<and> active_sc_at' scPtr s \<and> ksCurTime s = curTime}"
                           in updateSchedContext_ccorres_lemma3)
                apply (rule conseqPre, vcg)
                apply normalise_obj_at'
                apply (rename_tac sc sc')
                apply (frule (1) obj_at_cslift_sc)
                apply clarsimp
                apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
                apply (frule rf_sr_refill_buffer_relation)
                apply (intro conjI)
                   apply (clarsimp simp: typ_heap_simps)
                  apply (rule disjCI2)
                  apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                   apply (fastforce intro: sc_at_array_assertion'
                                     simp: valid_sched_context'_def MIN_REFILLS_def)
                  apply (clarsimp simp: typ_heap_simps valid_sched_context'_def obj_at'_def
                                        active_sc_at'_def csched_context_relation_def)
                 apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
                   apply (clarsimp simp: csched_context_relation_def valid_sched_context'_def
                                         active_sc_at'_def obj_at'_def)
                  apply fastforce
                 apply (clarsimp simp: sc_ptr_to_crefill_ptr_def csched_context_relation_def
                                       typ_heap_simps)
                apply (clarsimp simp: ret__ptr_to_struct_refill_C_'_update_rf_sr_helper
                                cong: StateSpace.state.fold_congs)
                apply (rule_tac old_sc=sc and n="scRefillHead sc"
                                and fa="\<lambda>refill. rTime_update (\<lambda>_. ksCurTime s) refill"
                                 in rf_sr_refill_update2;
                       fastforce?)
                    apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_def)
                   apply (fastforce simp: sched_context.expand)
                  apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
                    apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_def)
                   apply fastforce
                  apply (clarsimp simp: valid_sched_context'_def)
                  apply (fastforce simp: h_val_field_from_bytes' typ_heap_simps
                                         sc_ptr_to_crefill_ptr_def csched_context_relation_def)
                 apply (clarsimp simp: csched_context_relation_def)
                apply (drule_tac n="scRefillHead sc" in crefill_relationD; fastforce?)
                 apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_def
                                       csched_context_relation_def)
                apply (fastforce simp: crefill_relation_def sc_ptr_to_crefill_ptr_def
                                       csched_context_relation_def
                                 dest: rf_sr_ksCurTime)
               apply fastforce
              apply clarsimp
             apply (rule ccorres_return_Skip')
            apply ceqv

           apply (rule_tac xf'="\<lambda>s. h_val (hrs_mem (t_hrs_' (globals s)))
                                          (ret__ptr_to_struct_refill_C_' s)"
                        in ccorres_split_nothrow)
               apply (rule ccorres_call)
                  apply (rule refill_head_ccorres, clarsimp+)
              apply ceqv
             apply (rename_tac refill refill')
             apply (rule ccorres_Guard)
             apply (rule_tac R="sc_at' scPtr"
                         and R'="\<lbrace>h_val (hrs_mem \<acute>t_hrs) \<acute>ret__ptr_to_struct_refill_C = refill'\<rbrace>"
                         and Pt="invs' and active_sc_at' scPtr"
                         and Pf="invs' and active_sc_at' scPtr
                                 and (obj_at' (\<lambda>sc. refillHd sc = refill) scPtr)"
                         and Rt=UNIV
                         and Rf="\<lbrace>h_val (hrs_mem \<acute>t_hrs) \<acute>ret__ptr_to_struct_refill_C = refill'\<rbrace>"
                          in ccorres_cond_strong)
               apply (clarsimp simp: h_val_field_from_bytes' crefill_relation_def)

              \<comment> \<open>newBudget \<le> rAmount refill - update the rAmount and perform maybeAddEmptyTail\<close>
              apply (rule stronger_ccorres_guard_imp)
                apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                    apply (clarsimp simp: updateRefillHd_def)
                    apply (rule_tac P=\<top> and P'="\<lambda>s. invs' s \<and> active_sc_at' scPtr s"
                                and Q="\<lambda>s sc. {s'. (s, s') \<in> rf_sr \<and> ko_at' sc scPtr s \<and> invs' s
                                                   \<and> active_sc_at' scPtr s}"
                                 in updateSchedContext_ccorres_lemma3)
                      apply (rule conseqPre, vcg)
                      apply normalise_obj_at'
                      apply (rename_tac sc sc')
                      apply (frule (1) obj_at_cslift_sc)
                      apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
                      apply (frule rf_sr_refill_buffer_relation)
                      apply (intro conjI impI allI)
                         apply (clarsimp simp: typ_heap_simps)
                        apply (rule disjCI2)
                        apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                         apply (fastforce intro: sc_at_array_assertion'
                                           simp: valid_sched_context'_def MIN_REFILLS_def)
                        apply (clarsimp simp: typ_heap_simps valid_sched_context'_def obj_at'_def
                                              active_sc_at'_def csched_context_relation_def)
                       apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
                         apply (clarsimp simp: csched_context_relation_def valid_sched_context'_def
                                               active_sc_at'_def obj_at'_def)
                        apply fastforce
                       apply (clarsimp simp: sc_ptr_to_crefill_ptr_def csched_context_relation_def
                                             typ_heap_simps)
                      apply (clarsimp simp: ret__ptr_to_struct_refill_C_'_update_rf_sr_helper
                                      cong: StateSpace.state.fold_congs)
                      apply (rule_tac old_sc=sc and n="scRefillHead sc"
                                  and fa="\<lambda>refill. rAmount_update (\<lambda>_. newBudget) refill"
                                   in rf_sr_refill_update2,
                             fastforce+)
                            apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def
                                                  obj_at'_def)
                           apply (fastforce simp: sched_context.expand)
                          apply fastforce
                         apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
                           apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def
                                                 obj_at'_def)
                          apply fastforce
                         apply (clarsimp simp: valid_sched_context'_def)
                         apply (fastforce simp: typ_heap_simps sc_ptr_to_crefill_ptr_def
                                                csched_context_relation_def)
                        apply (fastforce simp: csched_context_relation_def)
                       apply (rule refl)
                      apply (drule_tac n="scRefillHead sc" in crefill_relationD; fastforce?)
                       apply (clarsimp simp: csched_context_relation_def valid_sched_context'_def
                                             active_sc_at'_def obj_at'_def)
                      apply (fastforce simp: crefill_relation_def sc_ptr_to_crefill_ptr_def
                                             csched_context_relation_def)
                     apply fastforce
                    apply fastforce
                   apply ceqv
                  apply clarsimp
                  apply (ctac add: maybe_add_empty_tail_ccorres)
                 apply (wpsimp wp: updateRefillHd_invs')
                apply vcg
               apply (clarsimp simp: active_sc_at'_rewrite)
              apply clarsimp

             \<comment> \<open>rAmount refill < newBudget - perform refillAddTail\<close>
             apply (rule stronger_ccorres_guard_imp)
               apply clarsimp
               apply (rule ccorres_rhs_assoc)+
               apply (rule ccorres_symb_exec_r)
                 apply (rule ccorres_symb_exec_r)
                   apply (rule ccorres_Guard_Seq)+
                   apply (rule ccorres_symb_exec_r)
                     apply (ctac add: refill_add_tail_ccorres)
                    apply vcg
                   apply (rule conseqPre, vcg)
                   apply clarsimp
                  apply vcg
                 apply (rule conseqPre, vcg)
                 apply clarsimp
                apply vcg
               apply (rule conseqPre, vcg)
               apply clarsimp
              apply wpsimp
             apply wpsimp
             apply (clarsimp cong: conj_cong)
             apply normalise_obj_at'
             apply (rename_tac sc)
             apply (frule (1) obj_at_cslift_sc)
             apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
             apply (frule rf_sr_refill_buffer_relation)
             apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
               apply (fastforce simp: valid_sched_context'_def obj_at_simps active_sc_at'_def)
              apply fastforce
             apply (intro conjI impI allI)
                apply (clarsimp simp: typ_heap_simps)
               apply (rule disjCI2)
               apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
                apply (fastforce intro: sc_at_array_assertion'
                                  simp: valid_sched_context'_def MIN_REFILLS_def)
               apply (fastforce simp: typ_heap_simps valid_sched_context'_def obj_at_simps
                                      active_sc_at'_def csched_context_relation_def)
              apply (frule_tac n="scRefillHead sc" in crefill_relationD; fastforce?)
               apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_def)
              apply (clarsimp simp: h_val_field_from_bytes' sc_ptr_to_crefill_ptr_def typ_heap_simps
                                    crefill_relation_def csched_context_relation_def refillHd_def)
             apply (clarsimp simp: sc_ptr_to_crefill_ptr_def csched_context_relation_def
                                   typ_heap_simps)
            apply (rule_tac Q'="\<lambda>refill s. (invs' s \<and> active_sc_at' scPtr s)
                                          \<and> (\<exists>sc. scs_of' s scPtr = Some sc \<and> refillHd sc = refill)"
                         in hoare_post_imp)
             apply (clarsimp simp: active_sc_at'_rewrite obj_at'_def opt_map_def)
            apply (rule getRefillHead_sp)
           apply vcg
          apply ((wpsimp wp: updateRefillHd_invs' | strengthen invs_valid_objs')+)[1]
         apply (vcg exspec=refill_index_modifies)
        apply (rule_tac Q'="\<lambda>_. active_sc_at' scPtr and invs'" in hoare_post_imp)
         apply (clarsimp simp: active_sc_at'_rewrite)
        apply wpsimp
       apply (vcg exspec=refill_ready_modifies)
      apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> active_sc_at' scPtr s" in hoare_post_imp)
       apply fastforce
      apply (wpsimp wp: updateSchedContext_refills_invs' updateSchedContext_active_sc_at')
     apply (vcg exspec=refill_index_modifies)
    apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> active_sc_at' scPtr s \<and> 0 < newMaxRefills
                             \<and> obj_at' (\<lambda>sc. newMaxRefills \<le> refillAbsoluteMax' (objBits sc)) scPtr s"
                 in hoare_post_imp)
     apply (clarsimp simp: active_sc_at'_def)
     apply normalise_obj_at'
     apply (frule maxRefills_helper)
     apply (frule invs_valid_objs')
     apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
     apply (clarsimp simp: valid_sched_context'_def refillSize_def objBits_simps word_bits_def
                           obj_at'_def)
    apply (wpsimp wp: updateSchedContext_refills_invs' updateSchedContext_active_sc_at'
                      updateSchedContext_wp)
   apply (vcg exspec=refill_index_modifies)
  apply normalise_obj_at'
  apply (rename_tac sc)
  apply (frule (1) obj_at_cslift_sc)
  apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
  apply (frule rf_sr_refill_buffer_relation)
  apply (frule_tac n=0 in h_t_valid_refill; fastforce?)
    apply (clarsimp simp: valid_sched_context'_def MIN_REFILLS_def)
   apply fastforce
  apply (frule_tac n="scRefillHead sc" in h_t_valid_refill; fastforce?)
    apply (clarsimp simp: valid_sched_context'_def MIN_REFILLS_def obj_at'_def active_sc_at'_def)
   apply fastforce
  apply (clarsimp simp: valid_sched_context'_def refillSize_def objBits_simps word_bits_def)
  apply (rule conjI)
   apply (clarsimp split: if_splits)
  apply (rule conjI)
   apply (fastforce simp: objBits_simps obj_at'_def opt_map_def ps_clear_def)
  by (clarsimp simp: typ_heap_simps sc_ptr_to_crefill_ptr_def) (* takes ~ 1 minute *)

lemma invokeSchedContext_UnbindObject_ThreadCap_ccorres:
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and sc_at' scPtr)
     (\<lbrace>\<acute>sc = sched_context_Ptr scPtr\<rbrace>
      \<inter> \<lbrace>ccap_relation (ThreadCap ptr) \<acute>cap\<rbrace>) hs
     (liftE (invokeSchedContext (InvokeSchedContextUnbindObject scPtr (ThreadCap ptr))))
     (Call invokeSchedContext_UnbindObject_'proc)"
  apply (cinit' lift: sc_' cap_')
   apply (simp add: invokeSchedContext_def)
   apply csymbr
   \<comment> \<open>the given cap is a ThreadCap\<close>
   apply (rule ccorres_cond_seq)
   apply (rule ccorres_cond_true)
   apply (rule ccorres_liftE')
   apply (ctac add: schedContext_unbindTCB_ccorres)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wpsimp
   apply (vcg exspec=schedContext_unbindTCB_modifies)
  apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
  done

lemma invokeSchedContext_UnbindObject_NotificationCap_ccorres:
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and sc_at' scPtr)
     (\<lbrace>\<acute>sc = sched_context_Ptr scPtr\<rbrace>
      \<inter> \<lbrace>ccap_relation (NotificationCap ptr badge canSend canReceive) \<acute>cap\<rbrace>) hs
     (liftE (invokeSchedContext
              (InvokeSchedContextUnbindObject scPtr (NotificationCap ptr badge canSend canReceive))))
     (Call invokeSchedContext_UnbindObject_'proc)"
  apply (cinit' lift: sc_' cap_')
   apply (clarsimp simp: invokeSchedContext_def)
   apply csymbr
   \<comment> \<open>the given cap is a NotificationCap\<close>
   apply (rule ccorres_cond_seq)
   apply (rule ccorres_cond_false)
   apply (rule ccorres_cond_seq)
   apply (rule ccorres_cond_true)
   apply (rule ccorres_liftE')
   apply (ctac add: schedContext_unbindNtfn_ccorres)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wpsimp
   apply (vcg exspec=schedContext_unbindNtfn_modifies)
  apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
  done

lemma decodeSchedContext_UnbindObject_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and sch_act_simple
      and (\<lambda>s. ksCurThread s = thread) and ct_active' and ex_nonz_cap_to' scPtr
      and (excaps_in_mem extraCaps o ctes_of)
      and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
      and (\<lambda>s. \<forall>v \<in> set extraCaps. s \<turnstile>' fst v))
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace>
      \<inter> \<lbrace>\<acute>current_extra_caps = extraCaps'\<rbrace>) hs
     (decodeSchedContext_UnbindObject scPtr (map fst extraCaps)
      >>= invocationCatch thread isBlocking isCall canDonate InvokeSchedContext)
     (Call decodeSchedContext_UnbindObject_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: sc_' current_extra_caps_'   simp: decodeSchedContext_UnbindObject_def)
   apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
   apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
      apply vcg
     apply (clarsimp simp: interpret_excaps_test_null excaps_map_def)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply clarsimp
   apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
   apply (rule ccorres_move_c_guard_cte)
   apply ctac
     apply csymbr
     apply (simp add: cap_get_tag_isCap)
     apply (rule ccorres_assert2)
     apply (simp add: hd_map hd_conv_nth)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (clarsimp simp: isCap_defs split: capability.splits)
      apply (simp add: liftE_bindE bind_bindE_assoc bind_assoc)
      apply (rule ccorres_pre_getObject_sc, rename_tac sc)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply (rule ccorres_move_c_guard_sc)
      apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
      apply (wpfix add: capability.sel)
      apply (rule ccorres_cond_seq)
      apply ccorres_rewrite
      apply (rule_tac Q="\<lambda>s. ko_at' sc scPtr s \<and> s \<turnstile>' fst (extraCaps ! 0) \<and> no_0_obj' s"
                   in ccorres_cond_both'[where Q'=\<top>])
        apply clarsimp
        apply (frule (1) obj_at_cslift_sc)
        apply (frule capTCBPtr_eq)
         apply (clarsimp simp: isCap_defs split: capability.splits)
        apply (clarsimp simp: csched_context_relation_def ccap_relation_def option_to_ctcb_ptr_def
                              valid_cap'_def typ_heap_simps)
        apply (case_tac "scTCB sc"; fastforce dest: tcb_at_not_NULL)
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply clarsimp
      apply (rule ccorres_move_c_guard_sc)
      apply (simp add: liftE_bindE bind_bindE_assoc bind_assoc)
      apply (rule ccorres_pre_getCurThread, rename_tac curThread)
      apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
      apply (rule ccorres_cond_seq)
      apply ccorres_rewrite
      apply (rule_tac Q="\<lambda>s. ko_at' sc scPtr s \<and> ksCurThread s = curThread \<and> no_0_obj' s"
                   in ccorres_cond_both'[where Q'=\<top>])
        apply clarsimp
        apply (frule (1) obj_at_cslift_sc)
        apply (frule rf_sr_ksCurThread)
        apply (fastforce simp: typ_heap_simps csched_context_relation_def option_to_ctcb_ptr_def)
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply (simp add: returnOk_bind bindE_assoc ccorres_invocationCatch_Inr performInvocation_def)
      apply (ctac add: setThreadState_ccorres)
        apply (ctac add: invokeSchedContext_UnbindObject_ThreadCap_ccorres)
           apply simp
           apply (rename_tac reply exception)
           apply (rule_tac P="reply = []" in ccorres_gen_asm)
           apply clarsimp
           apply (rule ccorres_alternative2)
           apply (rule ccorres_return_CE, simp+)[1]
          apply (rule ccorres_return_C_errorE, simp+)[1]
         apply (wpsimp simp: invokeSchedContext_def)
        apply (vcg exspec=invokeSchedContext_UnbindObject_modifies)
       apply (wp sts_invs_minor')
      apply (vcg exspec=setThreadState_modifies)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (clarsimp simp: isCap_defs split: capability.splits)
      apply (simp add: liftE_bindE bind_bindE_assoc bind_assoc)
      apply (rule ccorres_pre_getObject_sc, rename_tac sc)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply (rule ccorres_move_c_guard_sc)
      apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
      apply (wpfix add: capability.sel)
      apply (rule ccorres_cond_seq)
      apply ccorres_rewrite
      apply (rule_tac Q="\<lambda>s. ko_at' sc scPtr s \<and> s \<turnstile>' fst (extraCaps ! 0) \<and> no_0_obj' s"
                   in ccorres_cond_both'[where Q'=\<top>])
        apply clarsimp
        apply (frule (1) obj_at_cslift_sc)
        apply (clarsimp simp: csched_context_relation_def option_to_ctcb_ptr_def valid_cap'_def
                              typ_heap_simps)
        apply (frule cap_get_tag_NotificationCap)
        apply (simp add: cap_get_tag_isCap)
        apply (clarsimp simp: isCap_defs split: capability.splits)
        apply (case_tac "scNtfn sc"; fastforce)
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply (simp add: returnOk_bind bindE_assoc ccorres_invocationCatch_Inr performInvocation_def)
      apply (ctac add: setThreadState_ccorres)
        apply (ctac add: invokeSchedContext_UnbindObject_NotificationCap_ccorres)
           apply (rename_tac reply exception)
           apply (rule_tac P="reply = []" in ccorres_gen_asm)
           apply clarsimp
           apply (rule ccorres_alternative2)
           apply (rule ccorres_return_CE, simp+)[1]
          apply (rule ccorres_return_C_errorE, simp+)[1]
         apply (wpsimp simp: invokeSchedContext_def)
        apply (vcg exspec=invokeSchedContext_UnbindObject_modifies)
       apply (wp sts_invs_minor')
      apply (vcg exspec=setThreadState_modifies)
     apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
      apply vcg
     apply (rule conseqPre, vcg)
     apply (simp add: hd_map isCap_simps hd_conv_nth)
     apply (clarsimp simp: invocationCatch_def throwError_bind split: capability.split,
            clarsimp simp: throwError_def return_def syscall_error_rel_def syscall_error_to_H_cases
                           exception_defs)
    apply (simp add: getSlotCap_def)
    apply (wp getCTE_wp)
   apply (simp add: cap_get_tag_isCap)
   apply vcg
  apply clarsimp
  apply (frule rf_sr_ksCurThread)
  apply (intro conjI impI)
      apply (force simp: cte_wp_at_ctes_of ct_in_state'_def st_tcb_at'_def obj_at'_def)
     apply (clarsimp simp: excaps_map_def neq_Nil_conv cte_wp_at_ctes_of dest!: interpret_excaps_eq)
    using interpret_excaps_empty
    apply (fastforce dest: interpret_excaps_eq[rule_format] simp: excaps_map_def split_def)
   apply fastforce
  apply fastforce
  done

lemma invokeSchedContext_Bind_ThreadCap_ccorres:
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and sc_at' scPtr and tcb_at' ptr)
     (\<lbrace>\<acute>sc = sched_context_Ptr scPtr\<rbrace>
      \<inter> \<lbrace>ccap_relation (ThreadCap ptr) \<acute>cap\<rbrace>) hs
     (liftE (invokeSchedContext (InvokeSchedContextBind scPtr (ThreadCap ptr))))
     (Call invokeSchedContext_Bind_'proc)"
  apply (cinit' lift: sc_' cap_')
   apply (clarsimp simp: invokeSchedContext_def)
   apply csymbr
   \<comment> \<open>the given cap is a ThreadCap\<close>
   apply (rule ccorres_cond_seq)
   apply (rule ccorres_cond_true)
   apply (rule ccorres_liftE')
   apply (rule ccorres_rhs_assoc)+
   apply csymbr
   apply (ctac add: schedContext_bindTCB_ccorres)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wpsimp
   apply (vcg exspec=schedContext_bindTCB_modifies)
  apply (frule cap_get_tag_ThreadCap)
  apply (fastforce simp: cap_get_tag_isCap isCap_simps)
  done

lemma invokeSchedContext_Bind_NotificationCap_ccorres:
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and sc_at' scPtr)
     (\<lbrace>\<acute>sc = sched_context_Ptr scPtr\<rbrace>
      \<inter> \<lbrace>ccap_relation (NotificationCap ptr badge canSend canReceive) \<acute>cap\<rbrace>) hs
     (liftE (invokeSchedContext
              (InvokeSchedContextBind scPtr (NotificationCap ptr badge canSend canReceive))))
     (Call invokeSchedContext_Bind_'proc)"
  apply (cinit' lift: sc_' cap_')
   apply (clarsimp simp: invokeSchedContext_def)
   apply csymbr
   \<comment> \<open>the given cap is a NotificationCap\<close>
   apply (rule ccorres_cond_seq)
   apply (rule ccorres_cond_false)
   apply (rule ccorres_cond_seq)
   apply (rule ccorres_cond_true)
   apply (rule ccorres_liftE')
   apply (rule ccorres_rhs_assoc)+
   apply csymbr
   apply (ctac add: schedContext_bindNtfn_ccorres)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply wpsimp
   apply (vcg exspec=schedContext_bindNtfn_modifies)
  apply (frule cap_get_tag_NotificationCap)
  apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
  done

lemma decodeSchedContext_Bind_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s) and sch_act_simple
      and (\<lambda>s. ksCurThread s = thread) and ct_active' and ex_nonz_cap_to' scPtr
      and (excaps_in_mem extraCaps o ctes_of)
      and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
      and (\<lambda>s. \<forall>v \<in> set extraCaps. s \<turnstile>' fst v))
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace>
      \<inter> \<lbrace>\<acute>current_extra_caps = extraCaps'\<rbrace>) hs
     (decodeSchedContext_Bind scPtr (map fst extraCaps)
      >>= invocationCatch thread isBlocking isCall canDonate InvokeSchedContext)
     (Call decodeSchedContext_Bind_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: sc_' current_extra_caps_' simp: decodeSchedContext_Bind_def)
   apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
   apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
      apply vcg
     apply (clarsimp simp: interpret_excaps_test_null excaps_map_def)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply clarsimp
   apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
   apply (rule ccorres_move_c_guard_cte)
   apply ctac
     apply csymbr
     apply (simp add: cap_get_tag_isCap)
     apply (rule ccorres_assert2)
      apply (simp add: liftE_bindE bind_bindE_assoc  bind_assoc)
      apply (rule ccorres_pre_getObject_sc, rename_tac sc)
     apply (simp add: hd_map hd_conv_nth)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (clarsimp simp: isCap_defs split: capability.splits)
      apply (rename_tac tcb)
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_move_c_guard_sc)
      apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
      apply (wpfix add: capability.sel)
      apply (rule ccorres_cond_seq)
      apply ccorres_rewrite
      apply (rule_tac Q="\<lambda>s. ko_at' sc scPtr s \<and> s \<turnstile>' fst (extraCaps ! 0)
                             \<and> valid_objs' s \<and> no_0_obj' s"
                   in ccorres_cond_both'[where Q'=\<top>])
        apply clarsimp
        apply (frule (1) obj_at_cslift_sc)
        apply (frule (1) sc_ko_at_valid_objs_valid_sc')
        apply (frule capTCBPtr_eq)
         apply (clarsimp simp: isCap_defs split: capability.splits)
        apply (clarsimp simp: csched_context_relation_def option_to_ctcb_ptr_def
                              valid_cap'_def typ_heap_simps)
        apply (case_tac "scTCB sc"; fastforce simp: valid_sched_context'_def dest: tcb_at_not_NULL)
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply clarsimp
      apply (rule_tac xf'=ret__unsigned_longlong_'
                  and val="ptr_val (tcb_ptr_to_ctcb_ptr tcb)"
                   in ccorres_symb_exec_r_known_rv[where R=\<top> and R'="UNIV"])
         apply (rule conseqPre, vcg)
         apply clarsimp
         apply (frule cap_get_tag_ThreadCap)
         apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
        apply ceqv
       apply (simp add: liftE_bindE bind_bindE_assoc bind_assoc)
       apply (rule ccorres_pre_threadGet, rename_tac threadCap_tcbSC)
       apply ccorres_rewrite
       apply (rule ccorres_move_c_guard_tcb)
       apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
       apply (rule ccorres_cond_seq)
       apply ccorres_rewrite
       apply (rule_tac Q="\<lambda>s. obj_at' (\<lambda>tcb. tcbSchedContext tcb = threadCap_tcbSC) tcb s
                              \<and> valid_objs' s \<and> no_0_obj' s"
                    in ccorres_cond_both'[where Q'=\<top>])
         apply normalise_obj_at'
         apply (frule (1) obj_at_cslift_tcb)
         apply clarsimp
         apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
         apply (frule cap_get_tag_ThreadCap)
         apply (clarsimp simp: ctcb_relation_def typ_heap_simps' valid_tcb'_def)
         apply (case_tac "tcbSchedContext ko"; clarsimp)
        apply (simp add: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (simp add: returnOk_bind bindE_assoc ccorres_invocationCatch_Inr performInvocation_def)
       apply (simp add: liftE_bindE bind_bindE_assoc bind_assoc)
       apply csymbr
       apply (ctac add: isBlocked_ccorres, rename_tac blocked blocked')
         apply csymbr
         apply (rule_tac r'="\<lambda>rv rv'. rv' = from_bool (blocked \<and> \<not> rv)"
                     and xf'=ret__int_'
                      in ccorres_split_nothrow)
             apply (clarsimp simp: to_bool_def)
             apply (rule ccorres_Cond_rhs)
              apply (rule ccorres_add_return2)
              apply (ctac add: sc_released_ccorres, rename_tac released released')
                apply (rule ccorres_return[where R=\<top> and R'=UNIV])
                apply (rule conseqPre, vcg)
                apply (clarsimp simp: to_bool_def from_bool_def split: if_splits)
               apply wpsimp
              apply (vcg exspec=sc_released_modifies)
             apply (rule ccorres_add_return2)
             apply (rule ccorres_symb_exec_l)
                apply (rule ccorres_return_Skip')
               apply wpsimp+
            apply ceqv
           apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
           apply (wpfix add: capability.sel)
           apply (rule ccorres_cond_seq)
           apply ccorres_rewrite
           apply (rule ccorres_cond_both'[where Q=\<top> and Q'=\<top>])
             apply (clarsimp simp: to_bool_def)
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule syscall_error_throwError_ccorres_n)
            apply (simp add: syscall_error_to_H_cases)
           apply (simp add: returnOk_bind ccorres_invocationCatch_Inr performInvocation_def)
           apply (ctac add: setThreadState_ccorres)
             apply (ctac add: invokeSchedContext_Bind_ThreadCap_ccorres)
                apply (rename_tac reply exception)
                apply (rule_tac P="reply = []" in ccorres_gen_asm)
                apply clarsimp
                apply (rule ccorres_alternative2)
                apply (rule ccorres_return_CE, simp+)[1]
               apply (rule ccorres_return_C_errorE, simp+)[1]
              apply (wpsimp simp: invokeSchedContext_def)
             apply (vcg exspec=invokeSchedContext_Bind_modifies)
            apply (wpsimp wp: sts_invs_minor')
           apply (vcg exspec=setThreadState_modifies)
          apply (wpsimp simp: scReleased_def)
         apply (vcg exspec=sc_released_modifies)
        apply (wpsimp simp: isBlocked_def wp: gts_wp')
       apply (vcg exspec=isBlocked_modifies)
      apply (vcg exspec=cap_thread_cap_get_capTCBPtr_modifies)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (clarsimp simp: isCap_defs split: capability.splits)
      apply (rename_tac capNtfnPtr badge canSend canReceive)
      apply (simp add: liftE_bindE bind_bindE_assoc bind_assoc)
      apply (rule ccorres_rhs_assoc)+
      apply (rule ccorres_move_c_guard_sc)
      apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
      apply (wpfix add: capability.sel)
      apply (rule ccorres_cond_seq)
      apply ccorres_rewrite
      apply (rule_tac Q="\<lambda>s. ko_at' sc scPtr s \<and> valid_objs' s \<and> no_0_obj' s"
                   in ccorres_cond_both'[where Q'=\<top>])
        apply clarsimp
        apply (frule (1) obj_at_cslift_sc)
        apply (frule (1) sc_ko_at_valid_objs_valid_sc')
        apply (clarsimp simp: csched_context_relation_def typ_heap_simps valid_sched_context'_def)
        apply (case_tac "scNtfn sc"; clarsimp)
       apply (simp add: throwError_bind invocationCatch_def)
       apply (rule syscall_error_throwError_ccorres_n)
       apply (simp add: syscall_error_to_H_cases)
      apply (simp add: liftE_bindE bind_bindE_assoc bind_assoc liftM_def)
      apply (rule ccorres_pre_getNotification, rename_tac ntfn)
      apply csymbr
      apply (rule_tac xf'=unsigned_longlong_eret_2_'
                  and val="ptr_val (option_to_ptr (ntfnSc ntfn))"
                  and R="ko_at' ntfn capNtfnPtr"
                 in ccorres_symb_exec_r_known_rv[where R'=UNIV])
         apply (rule conseqPre, vcg)
         apply clarsimp
         apply (erule cmap_relationE1 [OF cmap_relation_ntfn])
          apply (erule ko_at_projectKO_opt)
         apply (frule cap_get_tag_NotificationCap)
         apply (clarsimp simp: typ_heap_simps' cnotification_relation_def Let_def
                               cap_get_tag_isCap isCap_simps)
         apply (case_tac "ntfnSc ntfn"; clarsimp)
        apply ceqv
       apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
       apply (rule_tac Q="\<lambda>s. ko_at' ntfn capNtfnPtr s \<and> valid_objs' s \<and> no_0_obj' s"
                    in ccorres_if_cond_throws[rotated -1, where Q'=\<top>])
          apply vcg
         apply clarsimp
         apply (frule (1) obj_at_cslift_ntfn)
         apply (frule (1) ntfn_ko_at_valid_objs_valid_ntfn')
         apply (clarsimp simp: valid_ntfn'_def valid_bound_obj'_def split: option.splits)
        apply (simp add: throwError_bind invocationCatch_def)
        apply (rule syscall_error_throwError_ccorres_n)
        apply (simp add: syscall_error_to_H_cases)
       apply (simp add: returnOk_bind bindE_assoc ccorres_invocationCatch_Inr performInvocation_def)
       apply (ctac add: setThreadState_ccorres)
         apply (ctac add: invokeSchedContext_Bind_NotificationCap_ccorres)
            apply simp
            apply (rename_tac reply exception)
            apply (rule_tac P="reply = []" in ccorres_gen_asm)
            apply clarsimp
            apply (rule ccorres_alternative2)
            apply (rule ccorres_return_CE, simp+)[1]
           apply (rule ccorres_return_C_errorE, simp+)[1]
          apply (wpsimp simp: invokeSchedContext_def)
         apply (vcg exspec=invokeSchedContext_Bind_modifies)
        apply (wp sts_invs_minor')
       apply (vcg exspec=setThreadState_modifies)
      apply (vcg exspec=notification_ptr_get_ntfnSchedContext_modifies)
     apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
      apply vcg
     apply (rule conseqPre, vcg)
     apply (simp add: hd_map isCap_simps hd_conv_nth)
     apply (clarsimp simp: invocationCatch_def throwError_bind split: capability.split,
            clarsimp simp: throwError_def return_def syscall_error_rel_def syscall_error_to_H_cases
                           exception_defs)
    apply (simp add: getSlotCap_def)
    apply (wp getCTE_wp)
   apply (simp add: cap_get_tag_isCap)
   apply vcg
  apply (frule rf_sr_ksCurThread)
  apply simp
  apply (intro conjI impI allI)
      apply (force simp: cte_wp_at_ctes_of ct_in_state'_def st_tcb_at'_def obj_at'_def)
     apply (clarsimp simp: excaps_map_def neq_Nil_conv cte_wp_at_ctes_of dest!: interpret_excaps_eq)
    using interpret_excaps_empty
    apply (fastforce dest: interpret_excaps_eq[rule_format] simp: excaps_map_def split_def)
   apply (frule cap_get_tag_ThreadCap)
   apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap)
  apply (clarsimp simp: to_bool_def)
  done

crunch schedContextUnbindNtfn, schedContextUnbindAllTCBs
  for scReply[wp]: "\<lambda>s. Q (obj_at' (\<lambda>sc. P (scReply sc)) scPtr s)"
  and no_0_obj'[wp]: no_0_obj'
  and reply_at'[wp]: "reply_at' replyPtr"
  (wp: updateSchedContext_sc_obj_at'_inv)

lemma invokeSchedContext_Unbind_ccorres:
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and sc_at' scPtr and ex_nonz_cap_to' scPtr)
     \<lbrace>\<acute>sc = sched_context_Ptr scPtr\<rbrace> []
     (liftE (invokeSchedContext (InvokeSchedContextUnbind scPtr)))
     (Call invokeSchedContext_Unbind_'proc)"
  apply (cinit' lift: sc_')
   apply (simp add: liftE_bindE bind_assoc)
   apply (clarsimp simp: invokeSchedContext_def liftE_bindE)
   apply (simp add: liftE_bindE bind_liftE_distrib)
   apply (ctac add: schedContext_unbindAllTCBs_ccorres)
     apply (ctac add: schedContext_unbindNtfn_ccorres)
       apply (ctac add: schedContext_unbindReply_ccorres)
         apply (simp add: liftE_def return_returnOk)
         apply (rule ccorres_return_CE, simp+)[1]
        apply wpsimp
       apply (vcg exspec=schedContext_unbindReply_modifies)
      apply (rule_tac Q'="\<lambda>_. invs' and sc_at' scPtr" in hoare_post_imp)
       apply (fastforce dest: sc_ko_at_valid_objs_valid_sc'
                        simp: obj_at'_def valid_sched_context'_def)
      apply wpsimp
     apply (vcg exspec=schedContext_unbindNtfn_modifies)
    apply ((wpsimp | strengthen invs'_implies)+)[1]
   apply (vcg exspec=schedContext_unbindAllTCBs_modifies)
  apply clarsimp
  apply (frule global'_sc_no_ex_cap[OF invs_valid_global'])
   apply fastforce
  apply fastforce
  done

crunch replyFromKernel, schedContextUpdateConsumed
  for weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"

lemma invokeSchedContext_Consumed_ccorres:
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. ksCurThread s = thread) and ct_in_state' ((=) Restart)
      and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s))
     (\<lbrace>\<acute>sc = sched_context_Ptr scPtr\<rbrace> \<inter> \<lbrace>\<acute>call = from_bool isCall\<rbrace>) hs
     (do reply \<leftarrow> returnConsumed scPtr;
         liftE (replyOnRestart thread reply isCall)
      od)
     (Call invokeSchedContext_Consumed_'proc)"
  apply (rule monadic_rewrite_ccorres_assemble[where P=P and Q=P for P, simplified, rotated])
   apply (rule monadic_rewrite_bind_tail)
    apply (rule monadic_rewrite_liftE)
    apply (rule replyOnRestart_replyFromKernel_rewrite)
   apply (wpsimp simp: returnConsumed_def)
   apply (clarsimp simp: ct_in_state'_def)
  apply (cinit' lift: sc_' call_')
   apply (clarsimp simp: replyOnRestart_def liftE_def bind_assoc)
   apply (subst bind_assoc[symmetric])
   apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
       apply (ctac add: setConsumed_returnConsumed_ccorres)
      apply ceqv
     apply (ctac add: setThreadState_ccorres)
       apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply wpsimp
     apply (vcg exspec=setThreadState_modifies)
    apply ((wpsimp wp: rfk_invs' hoare_vcg_if_lift2 hoare_drop_imps
                 simp: returnConsumed_def
            | strengthen invs'_implies)+)[1]
   apply (vcg exspec=setConsumed_modifies)
  apply (fastforce intro: rf_sr_ksCurThread simp: ct_in_state'_def)
  done

crunch schedContextYieldTo
  for st_tcb_at'[wp]: "st_tcb_at' P tcbPtr"
  (wp: threadSet_st_tcb_at2)

crunch schedContextResume, schedContextCompleteYieldTo, schedContextCompleteYieldTo
  for scTCB[wp]: "\<lambda>s. Q (obj_at' (\<lambda>sc. P (scTCB sc)) scPtr s)"
  and weak_sch_act_wf[wp]: "\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s"
  (wp: crunch_wps updateSchedContext_sc_obj_at'_inv simp: crunch_simps)

lemma returnConsumed_returns_nonempty_rewrite:
  "monadic_rewrite False True \<top>
     (do reply \<leftarrow> returnConsumed scPtr;
         if reply = []
         then liftE (replyOnRestart thread [] isCall) \<sqinter> returnOk ()
         else liftE (replyOnRestart thread reply isCall)
      od)
     (do reply \<leftarrow> returnConsumed scPtr; liftE (replyOnRestart thread reply isCall) od)"
  supply wordsOfTime_eq_words_from_time[simp del]
  apply (rule monadic_rewrite_bind_tail)
   apply (rule monadic_rewrite_if_l)
    apply (rule monadic_rewrite_impossible)
   apply (rule monadic_rewrite_refl)
  apply (wpsimp simp: returnConsumed_def simp: wordsOfTime_def)
  done

crunch schedContextResume
  for ko_at'_sc[wp]: "ko_at' (sc :: sched_context) scPtr"
  and valid_sched_context'[wp]: "valid_sched_context' sc"
  (wp: crunch_wps simp: crunch_simps)

lemma invokeSchedContext_YieldTo_ccorres:
  "ccorres ((intr_and_se_rel \<circ> Inr) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. ksCurThread s = thread) and ct_in_state' ((=) Restart)
      and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s))
     (\<lbrace>\<acute>sc = sched_context_Ptr scPtr\<rbrace> \<inter> \<lbrace>\<acute>call = from_bool isCall\<rbrace>) hs
     (doE reply \<leftarrow> liftE (schedContextYieldTo scPtr);
          if reply = []
          then liftE (replyOnRestart thread [] isCall) \<sqinter> returnOk ()
          else liftE (replyOnRestart thread reply isCall)
      odE)
     (Call invokeSchedContext_YieldTo_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: sc_' call_')
   apply (simp add: liftE_bindE bind_assoc)
   apply (clarsimp simp: schedContextYieldTo_def bind_assoc)
   apply (rule ccorres_pre_getObject_sc, rename_tac sc)
   apply (rule ccorres_move_c_guard_sc)
   apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
       apply (clarsimp simp: when_def)
       apply (rule_tac Q="ko_at' sc scPtr and valid_sched_context' sc and no_0_obj'"
                    in ccorres_cond_both'[where Q'=\<top>])
         apply normalise_obj_at'
         apply (frule (1) obj_at_cslift_sc)
         apply (clarsimp simp: csched_context_relation_def valid_sched_context'_def valid_bound_obj'_def
                               option_to_ctcb_ptr_def)
         apply (case_tac "scYieldFrom sc"; force dest!: tcb_at_not_NULL simp: typ_heap_simps)
        apply (rule ccorres_move_c_guard_sc)
        apply (ctac add: schedContext_completeYieldTo_ccorres)
       apply (rule ccorres_return_Skip)
      apply ceqv
     apply (ctac add: schedContext_resume_ccorres)
       apply (rule ccorres_move_c_guard_sc)
       apply (clarsimp simp: contextYieldToUpdateQueues_def)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_rhs_assoc2)
       apply (rule_tac r'="\<lambda> rv rv'. rv' = from_bool rv" and xf'=return_now_'
                    in ccorres_split_nothrow)
           apply (rule ccorres_pre_getObject_sc, rename_tac new_sc)
           apply (rule ccorres_assert2)
           apply (rule ccorres_rhs_assoc)+
           apply (rule_tac xf'=tcb_'
                       and val="option_to_ctcb_ptr (scTCB new_sc)"
                       and R="ko_at' new_sc scPtr"
                        in ccorres_symb_exec_r_known_rv[where R'="UNIV"])
              apply (rule conseqPre, vcg)
              apply normalise_obj_at'
              apply (frule (1) obj_at_cslift_sc)
              apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
             apply ceqv
            apply csymbr
            apply (ctac add: isSchedulable_ccorres)
              apply (rule ccorres_cond[where R=\<top>])
                apply (fastforce simp: to_bool_def)
               apply (rule ccorres_pre_getCurThread, rename_tac curThread)
               apply (rule ccorres_pre_threadGet, rename_tac prio)
               apply (rule ccorres_pre_threadGet, rename_tac curprio)
               apply (rule ccorres_Guard)
               apply (rule ccorres_move_c_guard_tcb)
               apply (rule_tac Q="\<lambda>s. obj_at' (\<lambda>tcb. tcbPriority tcb = prio) (the (scTCB new_sc)) s
                                      \<and> obj_at' (\<lambda>tcb. tcbPriority tcb = curprio) curThread s
                                      \<and> ksCurThread s = curThread"
                            in ccorres_cond_both'[where Q'=\<top>])
                 apply normalise_obj_at'
                 apply (drule (1) obj_at_cslift_tcb)+
                 apply (clarsimp simp: ucast_less_ucast_weak[symmetric, where 'b=machine_word_len]
                                       rf_sr_ksCurThread option_to_ctcb_ptr_def ctcb_relation_def
                                       typ_heap_simps')
                apply (rule ccorres_rhs_assoc)+
                apply (ctac add: tcbSchedDequeue_ccorres)
                  apply (clarsimp simp: option_to_ctcb_ptr_def)
                  apply (drule Some_to_the)
                  apply clarsimp
                  apply (ctac add: tcbSchedEnqueue_ccorres)
                    apply (rule ccorres_return[where R=\<top> and R'=UNIV])
                    apply (rule conseqPre, vcg)
                    apply fastforce
                   apply wpsimp
                  apply (vcg exspec=tcbSchedEnqueue_modifies)
                 apply wpsimp
                apply (vcg exspec=tcbSchedDequeue_modifies)
               apply (rule ccorres_rhs_assoc)+
               apply (rule ccorres_Guard_Seq)
               apply (rule ccorres_split_nothrow)
                   apply (rule_tac Q="\<lambda>s tcb. {s'. (s,s') \<in> rf_sr \<and> ko_at' tcb curThread s
                                                   \<and> ksCurThread s = curThread}"
                                in threadSet_ccorres_lemma3[where P=\<top>])
                    apply (rule conseqPre, vcg)
                    apply clarsimp
                    apply (frule (1) obj_at_cslift_tcb)
                    apply (frule rf_sr_ksCurThread)
                    subgoal
                      by (fastforce intro!: rf_sr_tcb_update_no_queue2
                                      simp: typ_heap_simps' tcb_cte_cases_def cteSizeBits_def
                                            ctcb_relation_def)
                   apply simp
                  apply ceqv
                 apply clarsimp
                 apply (rule ccorres_move_c_guard_sc)
                 apply (rule ccorres_split_nothrow)
                     apply (rule_tac P'="\<lambda>s. ksCurThread s = curThread"
                                  in updateSchedContext_ccorres_lemma3)
                       apply vcg
                      apply simp
                     apply clarsimp
                     apply (frule rf_sr_ksCurThread)
                     apply (rule_tac sc'="scYieldFrom_C_update
                                            (\<lambda>_. tcb_ptr_to_ctcb_ptr (ksCurThread s)) sc'"
                                  in rf_sr_sc_update_no_refill_buffer_update2)
                         apply fastforce
                        apply force
                       apply (simp add: typ_heap_simps' csched_context_relation_def)
                      apply (simp add: typ_heap_simps' csched_context_relation_def)
                     apply (fastforce intro: refill_buffer_relation_sc_no_refills_update
                                       simp: typ_heap_simps' csched_context_relation_def)
                    apply ceqv
                   apply (ctac add: tcbSchedDequeue_ccorres)
                     apply (ctac add: tcbSchedEnqueue_ccorres)
                       apply (ctac add: tcbSchedEnqueue_ccorres)
                         apply (ctac add: rescheduleRequired_ccorres)
                           apply (rule ccorres_return[where R=\<top> and R'=UNIV])
                           apply (rule conseqPre, vcg)
                           apply clarsimp
                          apply wpsimp
                         apply (vcg exspec=rescheduleRequired_modifies)
                        apply wpsimp
                       apply (vcg exspec=tcbSchedEnqueue_modifies)
                      apply wpsimp
                     apply (vcg exspec=tcbSchedEnqueue_modifies)
                    apply wpsimp
                   apply (vcg exspec=tcbSchedDequeue_modifies)
                  apply (drule Some_to_the)
                  apply clarsimp
                  apply wpsimp
                 apply (drule Some_to_the)
                 apply clarsimp
                 apply vcg
                apply (rule_tac Q'="\<lambda>_ s. ko_at' new_sc scPtr s \<and> valid_sched_context' new_sc s
                                          \<and> no_0_obj' s \<and> pspace_aligned' s \<and> pspace_distinct' s
                                          \<and> tcb_at' curThread s \<and> ksCurThread s = curThread
                                          \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                             in hoare_post_imp)
                 apply (fastforce simp: option_to_ctcb_ptr_def valid_sched_context'_def)
                apply wpsimp
               apply vcg
              apply (rule ccorres_return[where R=\<top>])
              apply (rule conseqPre, vcg)
              apply clarsimp
             apply (rule_tac Q'="\<lambda>_ s. ko_at' new_sc scPtr s \<and> no_0_obj' s
                                       \<and> pspace_aligned' s \<and> pspace_distinct' s
                                       \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                       \<and> tcb_at' thread s
                                       \<and> valid_sched_context' new_sc s"
                          in hoare_post_imp)
              apply (fastforce simp: obj_at'_def)
             apply (wpsimp wp: getSchedulable_wp)
            apply (vcg exspec=isSchedulable_modifies)
           apply vcg
          apply ceqv
         apply (rename_tac return_now return_now')
         apply (rule_tac P=return_now in ccorres_cases; clarsimp)
          apply ccorres_rewrite
          apply (rule monadic_rewrite_ccorres_assemble[rotated])
           apply (rule returnConsumed_returns_nonempty_rewrite)
          apply (rule monadic_rewrite_ccorres_assemble[rotated])
           apply (rule monadic_rewrite_bind_tail)
            apply (rule monadic_rewrite_liftE)
            apply (rule replyOnRestart_replyFromKernel_rewrite)
           apply wpsimp
          apply (simp add: liftE_bindE bind_assoc liftE_bindE_assoc bind_liftE_distrib)
          apply (subst bind_assoc[symmetric])
          apply (rule ccorres_rhs_assoc)+
          apply (ctac add: setConsumed_returnConsumed_ccorres)
            apply (rule ccorres_add_returnOk)
            apply (rule ccorres_liftE_Seq)
            apply (ctac add: setThreadState_ccorres)
              apply (rule ccorres_return_CE, simp+)[1]
             apply wpsimp
            apply (vcg exspec=setThreadState_modifies)
           apply (wpsimp simp: returnConsumed_def wp: hoare_vcg_if_lift2)
          apply (vcg exspec=setConsumed_modifies)
         apply ccorres_rewrite
         apply clarsimp
         apply (rule ccorres_alternative2)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule_tac Q'="\<lambda>_ s. cur_tcb' s \<and> no_0_obj' s \<and> pspace_aligned' s \<and> pspace_distinct' s
                                  \<and> st_tcb_at' ((=) Restart) thread s
                                  \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                     in hoare_post_imp)
         apply (clarsimp simp: st_tcb_at'_def obj_at'_def cur_tcb'_def)
        apply (wpsimp wp: threadSet_cur threadSet_st_tcb_at2 hoare_drop_imp)
       apply (vcg exspec=isSchedulable_modifies
                  exspec=rescheduleRequired_modifies
                  exspec=tcbSchedEnqueue_modifies
                  exspec=tcbSchedDequeue_modifies)
      apply (rule_tac Q'="\<lambda>_ s. obj_at' (\<lambda>sc'. scTCB sc' = scTCB sc) scPtr s
                                \<and> invs' s \<and> weak_sch_act_wf (ksSchedulerAction s) s \<and> cur_tcb' s
                                \<and> st_tcb_at' ((=) Restart) thread s"
                   in hoare_post_imp)
       apply normalise_obj_at'
       apply (frule (1) invs'_ko_at_valid_sched_context')
       apply (fastforce simp: valid_sched_context'_def valid_bound_obj'_def)
      apply wpsimp
     apply (vcg exspec=schedContext_resume_modifies)
    apply ((wp | strengthen invs'_implies)+)[1]
   apply (vcg exspec=schedContext_completeYieldTo_modifies)
  apply (frule rf_sr_ksCurThread)
  apply (clarsimp cong: conj_cong split: if_splits)
  by (safe;
      force dest!: invs'_ko_at_valid_sched_context'
             simp: typ_heap_simps' ct_in_state'_def st_tcb_at'_def obj_at'_def  cur_tcb'_def
                   csched_context_relation_def option_to_ctcb_ptr_def valid_sched_context'_def
            split: option.splits)

lemma decodeSchedContext_YieldTo_ccorres:
  "ccorres (intr_and_se_rel \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and (\<lambda>s. ksCurThread s = thread)
      and ct_active' and sc_at' scPtr and sch_act_simple)
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace>
      \<inter> \<lbrace>\<acute>call = from_bool isCall\<rbrace>) hs
     (decodeSchedContext_YieldTo scPtr
      >>= invocationCatch thread isBlocking isCall canDonate InvokeSchedContext)
     (Call decodeSchedContext_YieldTo_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: sc_' call_' simp: decodeSchedContext_YieldTo_def)
   apply (simp cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (clarsimp simp: liftE_bindE bind_assoc)
   apply (rule ccorres_move_c_guard_sc)
   apply (rule ccorres_pre_getObject_sc, rename_tac sc)
   apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
   apply (rule_tac Q="\<lambda>s. ko_at' sc scPtr s \<and> valid_objs' s \<and> no_0_obj' s"
                in ccorres_if_cond_throws[rotated -1, where Q'=\<top>])
      apply vcg
     apply normalise_obj_at'
     apply (frule (1) obj_at_cslift_sc)
     apply (frule (1) sc_ko_at_valid_objs_valid_sc')
     apply (clarsimp simp: typ_heap_simps csched_context_relation_def option_to_ctcb_ptr_def)
     apply (case_tac "scTCB sc"; clarsimp)
     apply (fastforce dest: tcb_at_not_NULL
                      simp: valid_sched_context'_def valid_bound_obj'_def)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (simp add: liftE_bindE bind_assoc)
   apply (rule ccorres_pre_getCurThread, rename_tac curThread)
   apply (rule ccorres_move_c_guard_sc)
   apply (rule_tac xf'=tcb_'
               and val="option_to_ctcb_ptr (scTCB sc)"
               and R="obj_at' (\<lambda>sc'. scTCB sc' = scTCB sc) scPtr and valid_objs'"
                in ccorres_symb_exec_r_known_rv[where R'="UNIV"])
      apply (rule conseqPre, vcg)
      apply normalise_obj_at'
      apply (frule (1) obj_at_cslift_sc)
      apply (clarsimp simp: typ_heap_simps csched_context_relation_def)
     apply ceqv
    apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
    apply (rule_tac Q="\<lambda>s. ko_at' sc scPtr s \<and> valid_objs' s \<and> no_0_obj' s
                           \<and> ksCurThread s = curThread"
                 in ccorres_if_cond_throws[rotated -1, where Q'=\<top>])
       apply vcg
      apply (fastforce simp: rf_sr_ksCurThread option_to_ctcb_ptr_def)
     apply (simp add: throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: liftE_bindE bind_assoc)
    apply (rule ccorres_pre_threadGet, rename_tac priority)
    apply (rule ccorres_pre_threadGet, rename_tac ct_mcp)
    apply (rule ccorres_move_c_guard_tcb)
    apply (rule ccorres_Guard_Seq)
    apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
    apply (rule_tac Q="\<lambda>s. obj_at' (\<lambda>tcb. tcbPriority tcb = priority) (the (scTCB sc)) s
                           \<and> obj_at' (\<lambda>tcb. tcbMCP tcb = ct_mcp) curThread s
                           \<and> ksCurThread s = curThread"
                 in ccorres_if_cond_throws[rotated -1, where Q'=\<top>])
       apply vcg
      apply normalise_obj_at'
      apply (drule (1) obj_at_cslift_tcb)+
      apply (clarsimp simp: ucast_less_ucast_weak[symmetric, where 'b=machine_word_len]
                            ctcb_relation_def rf_sr_ksCurThread typ_heap_simps'
                            option_to_ctcb_ptr_def)
     apply (simp add: throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: liftE_bindE bind_assoc)
    apply (rule ccorres_pre_threadGet, rename_tac yt_ptr)
    apply (rule ccorres_Guard_Seq)
    apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
    apply (rule_tac Q="\<lambda>s. ksCurThread s = curThread
                           \<and> obj_at' (\<lambda>tcb. tcbYieldTo tcb = yt_ptr) curThread s
                           \<and> valid_objs' s \<and> no_0_obj' s"
                 in ccorres_if_cond_throws[rotated -1, where Q'=\<top>])
       apply vcg
      apply normalise_obj_at'
      apply (rename_tac tcb)
      apply (frule (1) obj_at_cslift_tcb)
      apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
      apply (clarsimp simp: typ_heap_simps rf_sr_ksCurThread ctcb_relation_def valid_tcb'_def)
      apply (case_tac "tcbYieldTo tcb"; clarsimp)
     apply (simp add: throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: returnOk_bind bindE_assoc ccorres_invocationCatch_Inr
                     performInvocation_def invokeSchedContext_def)
    apply (ctac add: setThreadState_ccorres)
      apply (rule ccorres_add_returnOk)
      apply (ctac add: invokeSchedContext_YieldTo_ccorres)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_return_C_errorE, simp+)[1]
       apply wpsimp
      apply (vcg exspec=invokeSchedContext_YieldTo_modifies)
     apply ((wpsimp wp: sts_invs_minor' sts_st_tcb' setThreadState_ct'
                  simp: ct_in_state'_def
             | wps)+)[1]
    apply (vcg exspec=setThreadState_modifies)
   apply vcg
  by (force simp: st_tcb_at'_def obj_at'_def ct_in_state'_def
                  csched_context_relation_def typ_heap_simps rf_sr_ksCurThread)

lemma decodeSchedContextInvocation_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc)  (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and sch_act_simple
      and (\<lambda>s. ksCurThread s = thread) and ct_active' and sc_at' scPtr and ex_nonz_cap_to' scPtr
      and (excaps_in_mem extraCaps o ctes_of)
      and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
      and (\<lambda>s. \<forall>v \<in> set extraCaps. s \<turnstile>' fst v))
     (\<lbrace>\<acute>label___unsigned_long = label\<rbrace>
      \<inter> \<lbrace>\<acute>sc = Ptr scPtr\<rbrace>
      \<inter> \<lbrace>\<acute>current_extra_caps = extraCaps'\<rbrace>
      \<inter> \<lbrace>\<acute>call = from_bool isCall\<rbrace>) hs
     (decodeSchedContextInvocation label scPtr (map fst extraCaps)
      >>= invocationCatch thread isBlocking isCall canDonate InvokeSchedContext)
     (Call decodeSchedContextInvocation_'proc)"
  supply Collect_const[simp del] if_cong[cong] option.case_cong[cong]
  apply (cinit' lift: label___unsigned_long_' sc_' current_extra_caps_' call_')
   apply (simp add: decodeSchedContextInvocation_def invocation_eq_use_types gen_invocation_type_eq
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: returnOk_bind bindE_assoc ccorres_invocationCatch_Inr
                     performInvocation_def invokeSchedContext_def)
    apply (rule ccorres_rhs_assoc)
    apply (ctac add: setThreadState_ccorres)
      apply (rule ccorres_nondet_refinement)
       apply (rule is_nondet_refinement_bindE)
        apply (rule is_nondet_refinement_refl)
       apply (simp split: if_split, rule conjI[rotated])
        apply (rule impI, rule is_nondet_refinement_refl)
       apply (rule impI, rule is_nondet_refinement_alternative1)
      apply (clarsimp simp: liftE_bindE)
      apply (rule ccorres_add_returnOk)
      apply (ctac(no_vcg) add: invokeSchedContext_Consumed_ccorres)
        apply (rule ccorres_return_CE, simp+)[1]
       apply (rule ccorres_return_C_errorE, simp+)[1]
      apply (wpsimp wp: sts_invs_minor' ct_in_state'_set)+
    apply (vcg exspec=setThreadState_modifies)
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac (no_vcg) add: decodeSchedContext_Bind_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wpsimp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac (no_vcg) add: decodeSchedContext_UnbindObject_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wpsimp
   apply (rule ccorres_Cond_rhs)
    apply (clarsimp simp: liftE_bindE bind_assoc)
    apply (rule ccorres_pre_getObject_sc, rename_tac sc)
    apply (rule ccorres_pre_getCurThread, rename_tac curThread)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_move_c_guard_sc)
    apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
    apply (rule_tac Q="\<lambda>s. ko_at' sc scPtr s \<and> ksCurThread s = curThread \<and> cur_tcb' s \<and> no_0_obj' s"
                 in ccorres_if_cond_throws[rotated -1, where Q'=\<top>])
       apply vcg
      apply clarsimp
      apply (frule (1) obj_at_cslift_sc)
      apply normalise_obj_at'
      apply (simp add: rf_sr_ksCurThread typ_heap_simps csched_context_relation_def
                       option_to_ctcb_ptr_def cur_tcb'_def)
      apply (case_tac "scTCB sc"; fastforce dest: tcb_at_not_NULL)
     apply (simp add: throwError_bind invocationCatch_def)
     apply (rule syscall_error_throwError_ccorres_n)
     apply (simp add: syscall_error_to_H_cases)
    apply (simp add: returnOk_bind ccorres_invocationCatch_Inr)
    apply (ctac add: setThreadState_ccorres)
      apply (simp add: performInvocation_def)
      apply (ctac add: invokeSchedContext_Unbind_ccorres)
         apply clarsimp
         apply (rename_tac reply)
         apply (rule_tac P="reply = []" in ccorres_gen_asm)
         apply clarsimp
         apply (rule ccorres_alternative2)
         apply (rule ccorres_return_CE, simp+)[1]
        apply (rule ccorres_return_C_errorE, simp+)[1]
       apply (wpsimp simp: invokeSchedContext_def)
      apply (vcg exspec=invokeSchedContext_Unbind_modifies)
     apply (wp sts_invs_minor')
    apply (vcg exspec=setThreadState_modifies)
   apply clarsimp
   apply (rule ccorres_Cond_rhs)
    apply simp
    apply (rule ccorres_add_returnOk, ctac (no_vcg) add: decodeSchedContext_YieldTo_ccorres)
      apply (rule ccorres_return_CE, simp+)[1]
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply wpsimp
   apply (rule ccorres_equals_throwError)
    apply (fastforce simp: throwError_bind invocationCatch_def
                    split: invocation_label.split gen_invocation_labels.split)
   apply (rule syscall_error_throwError_ccorres_n)
   apply (simp add: syscall_error_to_H_cases)
  by (force simp: ct_in_state'_def st_tcb_at'_def obj_at'_def rf_sr_ksCurThread cur_tcb'_def)

lemma invokeSchedControl_ConfigureFlags_ccorres:
  "ccorres (K (K \<bottom>) \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and valid_sc_ctrl_inv'
            (InvokeSchedControlConfigureFlags scPtr budget period mRefills badge flags))
     (\<lbrace>\<acute>target___ptr_to_struct_sched_context_C = Ptr scPtr\<rbrace>
      \<inter> \<lbrace>\<acute>budget = budget\<rbrace> \<inter> \<lbrace>\<acute>period = period\<rbrace> \<inter> \<lbrace>\<acute>max_refills = of_nat mRefills\<rbrace>
      \<inter> \<lbrace>\<acute>badge___unsigned_long = badge\<rbrace> \<inter> \<lbrace>\<acute>flags = flags\<rbrace>) hs
     (liftE (invokeSchedControlConfigureFlags
              (InvokeSchedControlConfigureFlags scPtr budget period mRefills badge flags)))
     (Call invokeSchedControl_ConfigureFlags_'proc)"
  supply Collect_const [simp del]
  apply (cinit' lift: target___ptr_to_struct_sched_context_C_' budget_' period_' max_refills_'
                      badge___unsigned_long_' flags_'
                simp: invokeSchedControlConfigureFlags_def gets_bind_ign liftE_liftM)
   apply (rule ccorres_pre_getObject_sc, rename_tac sc)
   apply (rule ccorres_move_c_guard_sc)
   apply (rule_tac xf'=thread_'
               and val="option_to_ctcb_ptr (scTCB sc)"
               and R="obj_at' (\<lambda>sc'. scTCB sc' = scTCB sc) scPtr and valid_objs'"
                in ccorres_symb_exec_r_known_rv[where R'="UNIV"])
      apply (rule conseqPre, vcg)
      apply (fastforce dest: obj_at_cslift_sc simp: csched_context_relation_def typ_heap_simps)
     apply ceqv
    apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
        apply (clarsimp simp: when_def)
        apply (rule_tac Q="obj_at' (\<lambda>sc'. scTCB sc' = scTCB sc) scPtr and valid_objs'"
                     in ccorres_cond_both'[where Q'=\<top>])
          apply normalise_obj_at'
          apply (frule (1) sc_ko_at_valid_objs_valid_sc')
          apply (clarsimp simp: valid_sched_context'_def option_to_ctcb_ptr_def)
          apply (case_tac "scTCB sc"; clarsimp)
          apply (fastforce dest: tcb_at_not_NULL)
         (* target sc is associated with a thread, which we remove from scheduler queues,
            and then possibly commit the time *)
         apply clarsimp
         apply (drule Some_to_the)
         apply (clarsimp simp: option_to_ctcb_ptr_def split: option.splits)
         apply (rule ccorres_rhs_assoc)
         apply (ctac (no_vcg) add: tcbReleaseRemove_ccorres)
          apply (ctac (no_vcg) add: tcbSchedDequeue_ccorres)
           apply (rule ccorres_pre_getCurSc)
           apply (rule_tac Q="\<lambda>s. curSc = ksCurSc s" in ccorres_cond_both'[where Q'=\<top>])
             apply (fastforce dest: rf_sr_ksCurSC)
            apply (ctac (no_vcg) add: commitTime_ccorres)
           apply (rule ccorres_return_Skip)
          apply (wpsimp wp: hoare_drop_imps)
         apply (wpsimp wp: tcbReleaseRemove_invs')
        apply (rule ccorres_return_Skip)
       apply ceqv
      apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
          apply (rule ccorres_cond_both'[where Q="\<top>" and Q'=\<top>])
            apply fastforce
           apply (ctac (no_vcg) add: refill_new_ccorres)
          apply clarsimp
          apply (rule ccorres_rhs_assoc)+
          apply (ctac (no_vcg) add: sc_active_ccorres, rename_tac active)
           apply csymbr
           apply clarsimp
           apply (rule_tac P="to_bool active" in ccorres_cases)
            apply ccorres_rewrite
            apply (rule ccorres_cond_seq)
            apply (rule ccorres_cond_true)
            apply (rule_tac xf'=ret__int_'
                        and val="from_bool (scTCB sc \<noteq> None)"
                        and R="obj_at' (\<lambda>sc'. scTCB sc' = scTCB sc) scPtr and valid_objs'"
                         in ccorres_symb_exec_r_known_rv[where R'="UNIV"])
               apply (rule conseqPre, vcg)
               apply normalise_obj_at'
               apply (frule (1) sc_ko_at_valid_objs_valid_sc')
               apply (frule (1) obj_at_cslift_sc)
               apply (clarsimp simp: option_to_ctcb_ptr_def valid_sched_context'_def)
               apply (case_tac "scTCB sc"; clarsimp)
               apply (fastforce dest: tcb_at_not_NULL)
              apply ceqv
             apply (rule ccorres_cond_seq)
             apply (rule ccorres_cond_both'[where Q="\<top>" and Q'=\<top>])
               apply fastforce
              apply clarsimp
              apply (drule Some_to_the)
              apply (clarsimp simp: option_to_ctcb_ptr_def split: option.splits)
              apply (rule ccorres_rhs_assoc)+
              apply (ctac (no_vcg) add: isRunnable_ccorres)
               apply csymbr
               apply (rule ccorres_cond_both'[where Q="\<top>" and Q'=\<top>])
                 apply (clarsimp simp: to_bool_def)
                apply (ctac (no_vcg) add: refill_update_ccorres)
               apply (ctac (no_vcg) add: refill_new_ccorres)
              apply wpsimp
             (* target sc is not associated with a thread, so we call refill_new *)
             apply ccorres_rewrite
             apply (rule ccorres_cond_false)
             apply (ctac add: refill_new_ccorres)
            apply vcg
           (* target sc is not active, so we call refill_new *)
           apply (clarsimp simp: to_bool_def)
           apply ccorres_rewrite
           apply (rule ccorres_cond_seq)
           apply (rule ccorres_cond_false)
           apply ccorres_rewrite
           apply (rule ccorres_cond_false)
           apply ccorres_rewrite
           apply (ctac (no_vcg) add: refill_new_ccorres)
          apply wpsimp
         apply ceqv
        apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
            apply (clarsimp simp: when_def)
            apply (rule_tac Q="obj_at' (\<lambda>sc'. scTCB sc' = scTCB sc) scPtr and valid_objs'"
                         in ccorres_cond_both'[where Q'=\<top>])
              apply normalise_obj_at'
              apply (frule (1) sc_ko_at_valid_objs_valid_sc')
              apply (frule (1) obj_at_cslift_sc)
              apply (clarsimp simp: option_to_ctcb_ptr_def valid_sched_context'_def)
              apply (case_tac "scTCB sc"; clarsimp)
              apply (fastforce dest: tcb_at_not_NULL)
             apply (rule ccorres_rhs_assoc)
             apply (ctac add: schedContext_resume_ccorres)
               apply (rule ccorres_rhs_assoc)+
               apply (ctac add: isRunnable_ccorres, rename_tac runnable)
                 apply (rule ccorres_pre_getCurThread, rename_tac ctPtr)
                 apply (rule ccorres_cond_seq)
                 apply ccorres_rewrite
                 apply clarsimp
                 apply (drule Some_to_the)
                 apply (rule_tac P="the (scTCB sc) = ctPtr" in ccorres_cases)
                  (* the target sc is associated with the current thread,
                     so we call rescheduleRequired *)
                  apply clarsimp
                  apply (rule ccorres_cond_false)
                  apply ccorres_rewrite
                  apply (rule ccorres_cond_true)
                  apply (ctac add: rescheduleRequired_ccorres)
                 apply (clarsimp simp: when_def to_bool_def)
                 apply (rule_tac Q="\<lambda>s. ctPtr = ksCurThread s" in ccorres_cond_both'[where Q'=\<top>])
                   apply (clarsimp dest!: rf_sr_ksCurThread simp: option_to_ctcb_ptr_def)
                  (* the target sc is not associated with the current thread, but is associated
                     with a runnable thread, so we call possibleSwitchTo *)
                  apply (rule ccorres_add_return2)
                  apply (ctac add: possibleSwitchTo_ccorres)
                    apply (rule ccorres_cond_false)
                    apply (rule ccorres_return_Skip)
                   apply wpsimp
                  apply (vcg exspec=possibleSwitchTo_modifies)
                 (* the target sc is associated with a thread that is not runnable - do nothing *)
                 apply (rule ccorres_cond_false)
                 apply (rule ccorres_return_Skip)
                apply wpsimp
               apply (vcg exspec=isRunnable_modifies)
              apply (rule_tac Q'="\<lambda>_ s. tcb_at' (the (scTCB sc)) s
                                        \<and> weak_sch_act_wf (ksSchedulerAction s) s
                                        \<and> ksCurDomain s \<le> maxDomain \<and> valid_objs' s \<and> no_0_obj' s
                                        \<and> pspace_aligned' s \<and> pspace_distinct' s"
                           in hoare_post_imp)
               apply clarsimp
              apply wpsimp
             apply (vcg exspec=schedContext_resume_modifies)
            apply ccorres_rewrite
            apply (rule ccorres_return_Skip)
           apply ceqv
          apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
              apply (rule updateSchedContext_ccorres_lemma2[where P=\<top>])
                apply vcg
               apply simp
              apply (fastforce intro: rf_sr_sc_update_no_refill_buffer_update2
                                      refill_buffer_relation_sc_no_refills_update
                                simp: typ_heap_simps' csched_context_relation_def)
             apply ceqv
            apply (rule ccorres_add_return2)
            apply (rule ccorres_split_nothrow)
                apply (rule updateSchedContext_ccorres_lemma2[where P=\<top>])
                  apply vcg
                 apply simp
                apply (fastforce intro: rf_sr_sc_update_no_refill_buffer_update2
                                        refill_buffer_relation_sc_no_refills_update
                                  simp: typ_heap_simps' csched_context_relation_def
                                        seL4_SchedContext_Sporadic_def schedContextSporadicFlag_def
                                        nth_is_and_neq_0
                                 split: if_splits)
               apply ceqv
              apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: return_def)
             apply wpsimp
            apply vcg
           apply wpsimp
          apply (clarsimp simp: guard_is_UNIV_def)
         apply wpsimp
        apply (clarsimp simp: guard_is_UNIV_def)
       apply ((wpsimp wp: refillNew_invs' hoare_vcg_imp_lift' hoare_vcg_if_lift2
               | strengthen invs'_implies)+)[1]
           apply (drule Some_to_the)
           apply ((wpsimp wp: refillUpdate_invs' | strengthen invs'_implies)+)[1]
          apply clarsimp
          apply (drule Some_to_the)
          apply ((wpsimp wp: refillNew_invs' | strengthen invs'_implies)+)[1]
         apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> obj_at' (\<lambda>sc'. scTCB sc' = scTCB sc) scPtr s
                                   \<and> (\<exists>n. sc_at'_n n scPtr s \<and> valid_refills_number' mRefills n)
                                   \<and> ex_nonz_cap_to' scPtr s \<and> MIN_REFILLS \<le> mRefills
                                   \<and> (\<exists>tcbPtr. scTCB sc = Some tcbPtr \<longrightarrow> tcb_at' tcbPtr s)
                                   \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                      in hoare_post_imp)
          apply (clarsimp split: if_splits)
          apply normalise_obj_at'
          apply (intro conjI;
                 fastforce dest!: invs'_ko_at_valid_sched_context' simp: valid_sched_context'_def)
         apply (wpsimp wp: isRunnable_wp)
        apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> obj_at' (\<lambda>sc'. scTCB sc' = scTCB sc) scPtr s
                                  \<and> MIN_REFILLS \<le> mRefills
                                  \<and> (\<exists>tcbPtr. scTCB sc = Some tcbPtr \<longrightarrow> tcb_at' tcbPtr s)
                                  \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                     in hoare_post_imp)
         apply normalise_obj_at'
         apply (intro conjI impI allI;
                fastforce dest!: invs'_ko_at_valid_sched_context' simp: valid_sched_context'_def
                          split: if_splits)
        apply ((wpsimp wp: refillNew_invs' hoare_vcg_ex_lift | strengthen invs'_implies)+)[1]
       apply wpsimp
      apply (clarsimp simp: guard_is_UNIV_def option_to_ctcb_ptr_def split: option.splits)
     apply (rule_tac Q'="\<lambda>_ s. invs' s
                               \<and> obj_at' (\<lambda>sc'. scTCB sc' = scTCB sc) scPtr s
                               \<and> (\<exists>n. sc_at'_n n scPtr s \<and> valid_refills_number' mRefills n)
                               \<and> MIN_REFILLS \<le> mRefills \<and> ex_nonz_cap_to' scPtr s
                               \<and> (\<exists>tcbPtr. scTCB sc = Some tcbPtr \<longrightarrow> tcb_at' tcbPtr s)
                               \<and> weak_sch_act_wf (ksSchedulerAction s) s"
                  in hoare_post_imp)
      apply clarsimp
      subgoal
        by (intro conjI impI allI;
            normalise_obj_at'?,
            fastforce dest!: invs'_ko_at_valid_sched_context'
                      intro: obj_at'_weakenE
                       simp: valid_refills_number'_def valid_sched_context'_def MIN_REFILLS_def
                             objBits_simps active_sc_at'_def)
     apply (wpsimp wp: commitTime_invs' hoare_vcg_ex_lift)
      apply (drule Some_to_the)
      apply (wpsimp wp: commitTime_invs' hoare_vcg_ex_lift)
     apply (wpsimp wp: commitTime_invs' tcbReleaseRemove_invs' hoare_vcg_ex_lift)
    apply (clarsimp simp: guard_is_UNIV_def to_bool_def from_bool_def MIN_REFILLS_def)
   apply vcg
  apply (clarsimp split: if_splits)
  apply (intro conjI impI allI;
         fastforce dest!: invs'_ko_at_valid_sched_context' intro: obj_at'_weakenE
                    simp: valid_sched_context'_def)
  done

lemma mode_parseTimeArg_ccorres_foo:
  "ccorres (\<lambda>a rv. rv = args ! n) ret__unsigned_longlong_'
     (sysargs_rel args buffer and sysargs_rel_n args buffer n)
     (\<lbrace>unat \<acute>i = n\<rbrace> \<inter> \<lbrace>\<acute>buffer = option_to_ptr buffer\<rbrace>) []
     (return ()) (Call mode_parseTimeArg_'proc)"
  apply (cinit' lift: i_' buffer_')
   apply (rule ccorres_add_return2)
   apply (ctac add: getSyscallArg_ccorres_foo'[where n=n and args=args and buffer=buffer])
     apply (fastforce intro: ccorres_return_C)
    apply wp
   apply (vcg exspec=getSyscallArg_modifies)
  apply clarsimp
  done

lemma mode_parseTimeArg_ccorres_foo':
  "ccorres (\<lambda>a rv. rv = ucast (args ! n)) (\<lambda>x. ucast (ret__unsigned_longlong_' x))
     (sysargs_rel args buffer and sysargs_rel_n args buffer n)
     (\<lbrace>unat \<acute>i = n\<rbrace> \<inter> \<lbrace>\<acute>buffer = option_to_ptr buffer\<rbrace>) []
     (return ()) (Call mode_parseTimeArg_'proc)"
  apply (insert mode_parseTimeArg_ccorres_foo[where args=args and n=n and buffer=buffer])
  apply (clarsimp simp: ccorres_underlying_def)
  apply (erule (1) my_BallE)
  apply clarsimp
  apply (erule allE, erule allE, erule (1) impE)
  apply (clarsimp simp: return_def unif_rrel_def split: xstate.splits)
  done

lemma refillAbsoluteMax_size_helper:
  "\<lbrakk>valid_cap' cap s; isSchedContextCap cap\<rbrakk>
   \<Longrightarrow> MIN_REFILLS \<le> refillAbsoluteMax cap \<and> refillAbsoluteMax cap < 2 ^ word_bits"
  supply len_bit0[simp del]
  apply (clarsimp simp: refillAbsoluteMax_def isSchedContextCap_def split: capability.splits)
  apply (rule conjI)
   apply (fastforce intro: MIN_REFILLS_refillAbsoluteMax' simp: valid_cap'_def)
  apply (simp flip: max_num_refills_eq_refillAbsoluteMax'
               add: max_num_refils_rewrite max_num_refills'_def valid_cap'_def)
  apply (rename_tac n)
  apply (clarsimp simp: refillSizeBytes_sizeof maxUntypedSizeBits_def)
  apply (rule_tac y="2 ^ n" in le_less_trans)
   apply fastforce
  apply (simp add: word_less_nat_alt word_bits_def)
  apply (simp add: len_bit0)
  done

lemma MIN_BUDGET_def2:
  "MIN_BUDGET = us_to_ticks (2 * kernelWCET_us)"
  by (clarsimp simp: MIN_BUDGET_def kernelWCET_ticks_def timer_defs)

lemma decodeSchedControl_ConfigureFlags_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc)  (liftxf errstate id (K ()) ret__unsigned_long_')
     (\<lambda>s. (invs' s \<and> sch_act_wf (ksSchedulerAction s) s
           \<and> ksCurThread s = thread \<and> ct_active' s
           \<and> (excaps_in_mem extraCaps (ctes_of s))
           \<and> (\<forall>v \<in> set extraCaps. s \<turnstile>' fst v)
           \<and> (\<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v). ex_nonz_cap_to' y s)
           \<and> sysargs_rel args buffer s)
          \<and> isSchedControlCap cp)
     (\<lbrace>\<acute>current_extra_caps = extraCaps'\<rbrace>
      \<inter> \<lbrace>unat \<acute>length___unsigned_long = length args\<rbrace>
      \<inter> \<lbrace>\<acute>buffer = option_to_ptr buffer\<rbrace>
      \<inter> \<lbrace>ccap_relation cp \<acute>cap\<rbrace>) hs
     (decodeSchedControl_ConfigureFlags (map fst extraCaps) args
      >>= invocationCatch thread isBlocking isCall canDonate InvokeSchedControl)
     (Call decodeSchedControl_ConfigureFlags_'proc)"
  apply (intro ccorres_gen_asm[simplified pred_conj_def])
  supply Collect_const[simp del] if_cong[cong] option.case_cong[cong]
  apply (cinit' lift: current_extra_caps_' length___unsigned_long_' buffer_' cap_')
   apply (simp add: decodeSchedControl_ConfigureFlags_def timeArgSize_def wordBits_def'
                    invocation_eq_use_types gen_invocation_type_eq
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
   \<comment> \<open>throw an error if extraCaps is empty\<close>
   apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
      apply vcg
     apply (force simp: interpret_excaps_test_null excaps_map_def)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   \<comment> \<open>throw an error if args is of length less than timeArgSize * 2 + 3\<close>
   apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
      apply vcg
     apply (clarsimp simp: word_less_nat_alt)
    apply (simp add: throwError_bind invocationCatch_def)
    apply (rule syscall_error_throwError_ccorres_n)
    apply (simp add: syscall_error_to_H_cases)
   apply (rule ccorres_add_return,
          ctac add: mode_parseTimeArg_ccorres_foo'[where args=args and n=0 and buffer=buffer])
     apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
     \<comment> \<open>throw an error if the budget is greater than the period\<close>
     apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
        apply vcg
       apply (clarsimp simp: parseTimeArg_def timer_defs maxPeriodUs_def)
      apply (simp add: throwError_bind invocationCatch_def)
      apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: throwError_def syscall_error_rel_def syscall_error_to_H_cases
                            exception_defs return_def minBudgetUs_def maxPeriodUs_def
                            kernelWCET_us_def timer_defs)
     apply (rule_tac xf'=budget_ticks_'
                 and val="usToTicks (parseTimeArg 0 args)"
                  in ccorres_symb_exec_r_known_rv[where R=\<top> and R'="UNIV"])
        apply (rule conseqPre, vcg)
        using getCurrentTime_buffer_bound
        apply (clarsimp simp: parseTimeArg_def timer_defs maxPeriodUs_def word_less_nat_alt)
       apply ceqv
      apply (rule ccorres_add_return,
             ctac add: mode_parseTimeArg_ccorres_foo'[where args=args and n=1 and buffer=buffer])
        apply (simp add: whenE_def if_to_top_of_bind if_to_top_of_bindE)
        \<comment> \<open>throw an error if period is greater than maxPeriodUs\<close>
        apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
           apply vcg
          apply (clarsimp simp: parseTimeArg_def timer_defs maxPeriodUs_def)
         apply (simp add: throwError_bind invocationCatch_def)
         apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: throwError_def syscall_error_rel_def syscall_error_to_H_cases
                               exception_defs return_def minBudgetUs_def maxPeriodUs_def
                               kernelWCET_us_def timer_defs)
        apply (rule_tac xf'=period_ticks_'
                    and val="usToTicks (parseTimeArg 1 args)"
                     in ccorres_symb_exec_r_known_rv[where R=\<top> and R'="UNIV"])
           apply (rule conseqPre, vcg)
           using getCurrentTime_buffer_bound
           apply (clarsimp simp: parseTimeArg_def timer_defs maxPeriodUs_def word_less_nat_alt)
          apply ceqv
         apply (rule_tac xf'=ret__unsigned_longlong_'
                     and val=kernelWCET_ticks
                      in ccorres_symb_exec_r_known_rv[where R=\<top> and R'="UNIV"])
            apply (rule conseqPre, vcg)
            apply (clarsimp simp: kernelWCETTicks_def)
           apply ceqv
          \<comment> \<open>throw an error if budget is less than minBudget\<close>
          apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
             apply vcg
            using getCurrentTime_buffer_bound
            subgoal
              by (fastforce simp: minBudgetUs_def kernelWCET_ticks_def usToTicks_def
                                  word_mult_div_assoc timer_defs maxPeriodUs_def
                                  word_less_nat_alt)
           apply (simp add: throwError_bind invocationCatch_def)
           apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: throwError_def syscall_error_rel_def
                                 syscall_error_to_H_cases exception_defs return_def
                                 minBudgetUs_def maxPeriodUs_def MAX_PERIOD_US_def
                                 kernelWCET_us_def)
          apply clarsimp
          apply (rule_tac xf'=ret__unsigned_longlong_'
                      and val=kernelWCET_ticks
                       in ccorres_symb_exec_r_known_rv[where R=\<top> and R'="UNIV"])
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: kernelWCETTicks_def)
            apply ceqv
          \<comment> \<open>throw an error if the period is less than minBudget\<close>
           apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
              apply vcg
             using getCurrentTime_buffer_bound
             subgoal
               by (fastforce simp: minBudgetUs_def kernelWCET_ticks_def usToTicks_def
                                   word_mult_div_assoc timer_defs maxPeriodUs_def
                                   word_less_nat_alt)
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: throwError_def syscall_error_rel_def
                                  syscall_error_to_H_cases exception_defs return_def
                                  minBudgetUs_def maxPeriodUs_def MAX_PERIOD_US_def
                                  kernelWCET_us_def)
           \<comment> \<open>throw an error if period is less than budget\<close>
           apply (rule ccorres_if_cond_throws[rotated -1, where Q=\<top> and Q'=\<top>])
              apply vcg
             using getCurrentTime_buffer_bound
             subgoal
               by (fastforce simp: minBudgetUs_def kernelWCET_ticks_def usToTicks_def
                                   word_mult_div_assoc timer_defs maxPeriodUs_def
                                   word_less_nat_alt)
            apply (simp add: throwError_bind invocationCatch_def)
            apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: throwError_def syscall_error_rel_def
                                  syscall_error_to_H_cases exception_defs return_def
                                  minBudgetUs_def kernelWCET_us_def parseTimeArg_def)
           apply (rule getSlotCap_ccorres_fudge_n[where vals=extraCaps and n=0])
           apply (rule ccorres_move_c_guard_cte)
           apply ctac
             apply csymbr
             apply (simp add: cap_get_tag_isCap cong: call_ignore_cong)
             apply (rule ccorres_assert2)
             apply (rule ccorres_Cond_rhs_Seq)
              \<comment> \<open>the head of extraCaps is not a SchedContextCap; throw\<close>
              apply (rule ccorres_rhs_assoc)
              apply ccorres_rewrite
              apply (prop_tac "\<not> isSchedContextCap (hd (map fst extraCaps))")
               apply (cases extraCaps; clarsimp)
              apply (simp add: throwError_bind invocationCatch_def)
              apply (rule syscall_error_throwError_ccorres_n)
              apply (simp add: syscall_error_to_H_cases)
             apply (clarsimp simp: hd_conv_nth)
             apply (rule ccorres_add_return,
                    ctac add: getSyscallArg_ccorres_foo'[where args=args and n=2 and buffer=buffer])
               apply (rule_tac xf'=max_refills_'
                           and val="word_of_nat (refillAbsoluteMax (fst (extraCaps ! 0)))"
                           and R="\<lambda>s. s \<turnstile>' fst (extraCaps ! 0)"
                            in ccorres_symb_exec_r_known_rv[where R'="UNIV"])
                  apply (rule conseqPre, vcg)
                  apply clarsimp
                  apply (intro conjI impI allI)
                     apply (simp add: cap_get_tag_isCap)
                    apply (clarsimp simp: refill_C_size)
                   apply (clarsimp simp: valid_cap'_def)
                   apply (frule_tac cap'=targetCap in cap_get_tag_SchedContextCap)
                   apply (clarsimp simp: isSchedContextCap_def cap_get_tag_isCap)
                   apply (rule_tac y="word_of_nat maxUntypedSizeBits" in le_less_trans)
                    apply (clarsimp simp:maxUntypedSizeBits_def word_le_nat_alt)
                   apply (clarsimp simp: maxUntypedSizeBits_def)
                  apply (clarsimp simp: refillAbsoluteMax_def
                                        max_num_refills_eq_refillAbsoluteMax'[symmetric]
                                        max_num_refils_rewrite max_num_refills'_def
                                        schedContextStructSize_sizeof refillSizeBytes_sizeof
                                 split: capability.splits)
                  apply (frule_tac cap'=targetCap in cap_get_tag_SchedContextCap)
                  apply (clarsimp simp: valid_cap'_def isSchedContextCap_def cap_get_tag_isCap
                                        sched_context_C_size refill_C_size)
                  apply (subst word_of_nat_div)
                    apply (rule_tac y="2 ^ maxUntypedSizeBits" in le_less_trans)
                     apply (rule_tac y="2 ^ unat (capSCSizeBits_CL
                                                   (cap_sched_context_cap_lift targetCap))"
                                  in order_trans)
                      apply fastforce
                     apply clarsimp
                    apply (clarsimp simp: maxUntypedSizeBits_def)
                   apply (clarsimp simp: refill_C_size)
                  apply (subst word_of_nat_minus)
                   apply (rule_tac y="2 ^ minSchedContextBits" in order_trans)
                    apply (clarsimp simp: sched_context_C_size minSchedContextBits_def)
                   apply fastforce
                  apply fastforce
                 apply ceqv
                \<comment> \<open>the number of extra refills requested is too large for the cap; throw\<close>
                apply (rule_tac Q="\<lambda>s. s \<turnstile>' fst (extraCaps ! 0)"
                            in ccorres_if_cond_throws[rotated -1, where Q'=\<top>])
                   apply vcg
                  apply (clarsimp simp: MIN_REFILLS_def word_less_nat_alt)
                  apply (frule (1) refillAbsoluteMax_size_helper[simplified word_bits_def])
                  apply (rule_tac arg_cong[where f="\<lambda>t. t < unsigned (args ! 2)"])
                  apply (subst unat_sub)
                   apply (rule unat_le_fold[THEN iffD1])
                    apply fastforce
                   apply (clarsimp simp: MIN_REFILLS_def)
                  apply clarsimp
                  apply (fastforce simp: unat_of_nat64')
                 apply (rule_tac P="2 \<le> refillAbsoluteMax (fst (extraCaps ! 0))"
                              in ccorres_gen_asm)
                 apply (simp add: throwError_bind invocationCatch_def)
                 apply (rule syscall_error_throwError_ccorres_n)
                 apply (simp add: syscall_error_to_H_cases)
                 apply (clarsimp simp: MIN_REFILLS_def)
                apply (rule ccorres_add_return,
                       ctac add: getSyscallArg_ccorres_foo'[where args=args and n=3 and buffer=buffer])
                  apply (rule ccorres_add_return,
                         ctac add: getSyscallArg_ccorres_foo'[where args=args and n=4 and buffer=buffer])
                    apply (simp add: returnOk_bind ccorres_invocationCatch_Inr)
                    apply (ctac (no_vcg) add: setThreadState_ccorres)
                     apply csymbr
                     apply csymbr
                     apply (simp add: performInvocation_def bindE_assoc)
                     apply (ctac add: invokeSchedControl_ConfigureFlags_ccorres)
                        apply clarsimp
                        apply (rule ccorres_alternative2)
                        apply (rule ccorres_return_CE, simp+)[1]
                       apply (rule ccorres_return_C_errorE, simp+)[1]
                      apply (wpsimp simp: invokeSchedContext_def)
                     apply (vcg exspec=invokeSchedControl_ConfigureFlags_modifies)
                    apply (wpsimp wp: sts_invs_minor' hoare_vcg_ex_lift)
                   apply clarsimp
                   apply wpsimp
                  apply (vcg exspec=setThreadState_modifies)
                 apply clarsimp
                 apply wpsimp
                apply (vcg exspec=getSyscallArg_modifies)
               apply (vcg exspec=refill_absolute_max_modifies)
              apply wpsimp
             apply (vcg exspec=getSyscallArg_modifies)
            apply ((wp | simp | wpc | wp (once) hoare_drop_imps)+)[1]
           apply vcg
          apply (vcg exspec=getKernelWcetTicks_modifies)
         apply (vcg exspec=getKernelWcetTicks_modifies)
        apply simp
        apply (vcg exspec=usToTicks_modifies)
       apply clarsimp
       apply wpsimp
      apply simp
      apply (vcg exspec=mode_parseTimeArg_modifies)
     apply simp
     apply (vcg exspec=usToTicks_modifies)
    apply clarsimp
    apply wpsimp
   apply simp
   apply (vcg exspec=mode_parseTimeArg_modifies)
  apply clarsimp
  apply (frule sysargs_rel_to_n[where n=0])
  apply (frule sysargs_rel_to_n[where n=1])
  apply (frule sysargs_rel_to_n[where n=2])
  apply (frule sysargs_rel_to_n[where n=3])
  apply (frule sysargs_rel_to_n[where n=4])
  apply (insert getCurrentTime_buffer_bound)
  apply (frule rf_sr_ksCurThread)
  apply (prop_tac "(of_nat (size_of TYPE(refill_C)) :: 32 word) \<noteq> 0")
   apply (rule of_nat_neq_0[where 'a=32])
    apply clarsimp
   apply (simp add: refill_C_size len32)
  apply (simp add: cap_get_tag_isCap MIN_REFILLS_def usToTicks_def parseTimeArg_def len64)
  apply (prop_tac "excaprefs_C (current_extra_caps_' (globals s')).[0] \<noteq> NULL
                   \<longrightarrow> excaprefs_C (current_extra_caps_' (globals s')).[0]
                       = cte_Ptr (snd (extraCaps ! 0))")
   using interpret_excaps_empty
   subgoal
     by (fastforce dest: interpret_excaps_eq[rule_format] simp: excaps_map_def split_def)[1]
  apply (prop_tac "\<forall>acap ccap. (isSchedContextCap acap \<and> ccap_relation acap ccap)
                               \<longrightarrow> (capSCPtr_CL (cap_sched_context_cap_lift ccap)
                                   = capSchedContextPtr acap)")
   apply clarsimp
   apply (frule_tac cap=acap in cap_get_tag_SchedContextCap)
   apply (simp add: cap_get_tag_isCap isSchedContextCap_def)
  apply (intro context_conjI impI allI; clarsimp?)
           apply (drule_tac x="extraCaps ! 0" in bspec, fastforce)+
           apply (fastforce simp: refillAbsoluteMax_size_helper[simplified MIN_REFILLS_def])
          apply (clarsimp simp: pred_tcb_at'_def ct_in_state'_def)
         apply (fastforce intro: pred_tcb'_weakenE[where P=active'] simp: ct_in_state'_def)
        apply (drule_tac x="extraCaps ! 0" in bspec, fastforce)+
        apply (frule (1) refillAbsoluteMax_size_helper)
        subgoal
          by (clarsimp simp: refillAbsoluteMax_def MIN_REFILLS_def valid_refills_number'_def
                             isCap_simps valid_cap'_def
                      split: capability.splits)
             (fastforce simp: refillAbsoluteMax_def MIN_REFILLS_def)
       apply (drule_tac x="extraCaps ! 0" in bspec, fastforce)+
       subgoal
         by (force simp: valid_cap'_def isSchedContextCap_def refillAbsoluteMax_def
                  split: capability.splits)[1]
      apply (clarsimp simp: MAX_PERIOD_def)
      apply (rule us_to_ticks_mono)
       apply (fastforce simp: timer_defs maxPeriodUs_def)
      apply fastforce
     apply (clarsimp simp: minBudgetUs_def MIN_BUDGET_def2)
     apply (rule us_to_ticks_mono)
      apply fastforce
     apply (clarsimp simp: maxPeriodUs_def word_less_nat_alt)
     apply (force intro: mult_le_mono3[where a="5 * unat MAX_PERIOD_US"])
    apply (clarsimp simp: MAX_PERIOD_def)
    apply (rule us_to_ticks_mono)
     apply (clarsimp simp: maxPeriodUs_def word_le_nat_alt word_less_nat_alt)
    apply (force intro: mult_le_mono3[where a="5 * unat MAX_PERIOD_US"])
   apply (clarsimp simp: minBudgetUs_def MIN_BUDGET_def2)
   apply (rule us_to_ticks_mono)
    apply fastforce
   apply (clarsimp simp: maxPeriodUs_def word_less_nat_alt)
   apply (force intro: mult_le_mono3[where a="5 * unat MAX_PERIOD_US"])
  apply (clarsimp simp: excaps_map_def neq_Nil_conv cte_wp_at_ctes_of dest!: interpret_excaps_eq)
  done

lemma decodeSchedControlInvocation_ccorres:
  "interpret_excaps extraCaps' = excaps_map extraCaps \<Longrightarrow>
   ccorres (intr_and_se_rel \<currency> dc)  (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and (\<lambda>s. sch_act_wf (ksSchedulerAction s) s) and sch_act_simple
      and (\<lambda>s. ksCurThread s = thread) and ct_active'
      and (excaps_in_mem extraCaps o ctes_of)
      and (\<lambda>s. \<forall>v \<in> set extraCaps. ex_cte_cap_wp_to' isCNodeCap (snd v) s)
      and (\<lambda>s. \<forall>v \<in> set extraCaps. s \<turnstile>' fst v)
      and (\<lambda>s. \<forall>v \<in> set extraCaps. \<forall>y \<in> zobj_refs' (fst v). ex_nonz_cap_to' y s)
      and sysargs_rel args buffer
      and K (isSchedControlCap cp))
     (\<lbrace>\<acute>label___unsigned_long = label\<rbrace>
      \<inter> \<lbrace>\<acute>current_extra_caps = extraCaps'\<rbrace>
      \<inter> \<lbrace>unat \<acute>length___unsigned_long = length args\<rbrace>
      \<inter> \<lbrace>\<acute>buffer = option_to_ptr buffer\<rbrace>
      \<inter> \<lbrace>ccap_relation cp \<acute>cap\<rbrace>) hs
     (decodeSchedControlInvocation label args (map fst extraCaps)
      >>= invocationCatch thread isBlocking isCall canDonate InvokeSchedControl)
     (Call decodeSchedControlInvocation_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: label___unsigned_long_' current_extra_caps_' length___unsigned_long_'
                      buffer_' cap_')
   apply (simp add: decodeSchedControlInvocation_def invocation_eq_use_types gen_invocation_type_eq
              cong: StateSpace.state.fold_congs globals.fold_congs)
   apply (rule ccorres_Cond_rhs)
    apply (simp add: returnOk_bind bindE_assoc ccorres_invocationCatch_Inr
                     performInvocation_def invokeSchedContext_def)
    apply (rule ccorres_add_returnOk)
    apply (ctac (no_vcg) add: decodeSchedControl_ConfigureFlags_ccorres)
      apply (fastforce intro: ccorres_return_CE)
     apply (fastforce intro: ccorres_return_C_errorE)
    apply wpsimp
   apply (rule ccorres_equals_throwError)
    apply (fastforce simp: throwError_bind invocationCatch_def
                    split: gen_invocation_labels.split)
   apply (rule syscall_error_throwError_ccorres_n)
   apply (simp add: syscall_error_to_H_cases)
  apply fastforce
  done

end

end
