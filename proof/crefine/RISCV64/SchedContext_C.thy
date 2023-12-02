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

lemma refill_next_ccorres:
  "ccorres (\<lambda>next next'. next = unat next') ret__unsigned_long_'
     (active_sc_at' scPtr and invs' and K (Suc idx < 2 ^ word_bits))
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> \<lbrace>\<acute>index = word_of_nat idx\<rbrace>) []
     (getRefillNext scPtr idx) (Call refill_next_'proc)"
  supply len_bit0[simp del]
  apply (cinit lift: sc_' index_'
               simp: readRefillNext_def refillNext_def readSchedContext_def getObject_def[symmetric]
                     getSchedContext_def[symmetric])
   apply (rule ccorres_pre_getObject_sc, rename_tac sc)
   apply (rule ccorres_move_c_guard_sc)
   apply (rule ccorres_return_C; clarsimp)
  apply (rule conjI)
   apply clarsimp
  apply (clarsimp simp: active_sc_at'_def)
  apply normalise_obj_at'
  apply (rename_tac sc' sc)
  apply (frule (1) obj_at_cslift_sc)
  apply (clarsimp simp: typ_heap_simps csched_context_relation_def split: if_splits)
  apply (prop_tac "0 < scRefillMax sc")
   apply (clarsimp simp: active_sc_at'_def obj_at'_def)
  apply (frule (1) invs'_ko_at_valid_sched_context')
  apply (clarsimp simp: word_bits_def)
  apply (frule (1) length_scRefills_bounded)
  apply (intro conjI impI allI)
   apply (cut_tac x=idx
              and y="unat (scRefillMax_C sc') - Suc 0"
              and 'a1=machine_word_len
               in inj_on_contraD[OF inj_on_word_of_nat])
      apply assumption
     apply fastforce
    apply (fastforce simp: valid_sched_context'_def word_bits_def)
   apply fastforce
  apply (fastforce simp: unat_of_nat_eq unat_add_lem')
  done

lemma getRefillSize_exs_valid[wp]:
  "\<lbrace>(=) s\<rbrace> getRefillSize scPtr \<lbrace>\<lambda>r. (=) s\<rbrace>"
  by (wpsimp simp: getRefillSize_def)

crunch (empty_fail) empty_fail[wp]: getRefillSize

lemma refill_add_tail_ccorres:
  "ccorres dc xfdc
     (active_sc_at' scPtr and invs')
     (\<lbrace>\<acute>sc = Ptr scPtr\<rbrace> \<inter> {s'. crefill_relation new (refill_' s')}) []
     (refillAddTail scPtr new) (Call refill_add_tail_'proc)"
  supply sched_context_C_size[simp del] refill_C_size[simp del] len_bit0[simp del]

  apply (simp add: refillAddTail_def)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ getRefillSize_sp]; wpsimp)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ get_sc_sp']; wpsimp?)
  apply (rule ccorres_symb_exec_l'[rotated, OF _ assert_sp]; wpsimp)

  apply (cinit' lift: sc_' refill_' simp: updateRefillIndex_def)
   apply (rule ccorres_move_c_guard_sc)
   apply (ctac add: refill_next_ccorres)
     apply (rule ccorres_move_c_guard_sc)
     apply clarsimp
     apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc])
         apply (rule_tac P=\<top> in updateSchedContext_ccorres_lemma2)
           apply vcg
          apply fastforce
         apply clarsimp
         apply (rule_tac sc'="scRefillTail_C_update (\<lambda>_. new_tail) sc'"
                      in rf_sr_sc_update_no_refill_buffer_update2;
                fastforce?)
           apply (clarsimp simp: typ_heap_simps')
          apply (clarsimp simp: csched_context_relation_def)
         apply (fastforce intro: refill_buffer_relation_sc_no_refills_update)
        apply ceqv
       apply (rule_tac P="\<lambda>sc. scRefillTail sc = unat new_tail"
                   and P'="active_sc_at' scPtr and invs'"
                    in updateSchedContext_ccorres_lemma3)
         apply vcg
        apply fastforce
       apply normalise_obj_at'
       apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
       apply (intro conjI)
          apply (fastforce dest: sc_at_h_t_valid[rotated])
         apply (rule disjCI2)
         apply (rule_tac n="length (scRefills sc)" in array_assertion_shrink_right)
          apply (fastforce intro: sc_at_array_assertion'
                            simp: valid_sched_context'_def MIN_REFILLS_def)
         apply (clarsimp simp: typ_heap_simps valid_sched_context'_def obj_at_simps
                               active_sc_at'_def csched_context_relation_def)
        apply (frule rf_sr_refill_buffer_relation)
        apply (frule_tac n="scRefillTail sc" in h_t_valid_refill; fastforce?)
          apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_def)
         apply fastforce
        apply (clarsimp simp: sc_ptr_to_crefill_ptr_def typ_heap_simps csched_context_relation_def)
       apply (clarsimp simp: ret__ptr_to_struct_refill_C_'_update_rf_sr_helper
                       cong: StateSpace.state.fold_congs)
       apply (rule_tac old_sc=sc and n="scRefillTail sc" and refill=new and refill'=refill
                    in rf_sr_refill_update2;
              fastforce?)
          apply (clarsimp simp: valid_sched_context'_def active_sc_at'_def obj_at'_def)
         apply (fastforce simp: sched_context.expand)
        apply (clarsimp simp: typ_heap_simps sc_ptr_to_crefill_ptr_def csched_context_relation_def)
       apply (clarsimp simp: csched_context_relation_def)
      apply ((rule hoare_vcg_conj_lift
              | wpsimp wp: updateSchedContext_active_sc_at' updateSchedContext_refills_invs'
              | wpsimp wp: updateSchedContext_wp)+)[1]
     apply vcg
    apply (wpsimp wp: getRefillNext_wp)
   apply vcg
  apply normalise_obj_at'
  apply (frule (1) sc_ko_at_valid_objs_valid_sc'[OF _ invs_valid_objs'])
  apply (elim conjE)
  apply (frule (1) length_scRefills_bounded)
  apply (intro conjI)
      apply (clarsimp simp: valid_sched_context'_def word_bits_len_of refillSizeBytes_def)
     apply (fastforce simp: obj_at'_def objBits_simps opt_map_def ps_clear_def)
    apply (fastforce simp: valid_sched_context'_def refillNext_def refillSize_def split: if_splits)
   apply (clarsimp simp: valid_sched_context_size'_def)
  apply (fastforce dest: obj_at_cslift_sc simp: csched_context_relation_def typ_heap_simps)
  done

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
      apply (rule_tac Q="\<lambda>_ s. active_sc_at' scPtr s \<and> invs' s \<and> ksCurTime s = curTime
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
                                   in rf_sr_refill_update2)
                                apply fastforce
                               apply fastforce
                              apply fastforce
                             apply fastforce
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
            apply (rule_tac Q="\<lambda>refill s. (invs' s \<and> active_sc_at' scPtr s)
                                          \<and> (\<exists>sc. scs_of' s scPtr = Some sc \<and> refillHd sc = refill)"
                         in hoare_post_imp)
             apply (clarsimp simp: active_sc_at'_rewrite obj_at'_def opt_map_def)
            apply (rule getRefillHead_sp)
           apply vcg
          apply ((wpsimp wp: updateRefillHd_invs' | strengthen invs_valid_objs')+)[1]
         apply (vcg exspec=refill_index_modifies)
        apply (rule_tac Q="\<lambda>_. active_sc_at' scPtr and invs'" in hoare_post_imp)
         apply (clarsimp simp: active_sc_at'_rewrite)
        apply wpsimp
       apply (vcg exspec=refill_ready_modifies)
      apply (wpsimp wp: updateSchedContext_refills_invs' updateSchedContext_active_sc_at'
                        hoare_drop_imps)
     apply (vcg exspec=refill_index_modifies)
    apply (rule_tac Q="\<lambda>_ s. invs' s \<and> active_sc_at' scPtr s \<and> 0 < newMaxRefills
                             \<and> obj_at' (\<lambda>sc. newMaxRefills \<le> refillAbsoluteMax' (objBits sc)) scPtr s"
                 in hoare_post_imp)
     apply (clarsimp simp: active_sc_at'_def)
     apply normalise_obj_at'
     apply (frule maxRefills_helper)
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

lemma decodeSchedContext_UnbindObject_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (decodeSchedContext_UnbindObject scPtr excaps) (Call decodeSchedContext_UnbindObject_'proc)"
sorry (* FIXME RT: decodeSchedContext_UnbindObject_ccorres *)

lemma decodeSchedContext_Bind_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (decodeSchedContext_Bind scPtr excaps) (Call decodeSchedContext_Bind_'proc)"
sorry (* FIXME RT: decodeSchedContext_Bind_ccorres *)

lemma setConsumed_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (setConsumed scPtr buffer) (Call setConsumed_'proc)"
sorry (* FIXME RT: setConsumed_ccorres *)

lemma decodeSchedContext_YieldTo_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (decodeSchedContext_YieldTo scPtr buffer) (Call decodeSchedContext_YieldTo_'proc)"
sorry (* FIXME RT: decodeSchedContext_YieldTo_ccorres *)

lemma decodeSchedContextInvocation_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (decodeSchedContextInvocation label scPtr excaps buffer)
     (Call decodeSchedContextInvocation_'proc)"
sorry (* FIXME RT: decodeSchedContextInvocation_ccorres *)

lemma schedContext_updateConsumed_ccorres:
  "ccorres dc xfdc
     invs' \<lbrace>\<acute>sc = Ptr scPtr\<rbrace> []
     (schedContextUpdateConsumed scPtr)
     (Call schedContext_updateConsumed_'proc)"
sorry (* FIXME RT: schedContext_updateConsumed_ccorres *)

lemma invokeSchedControl_ConfigureFlags_ccorres:
  "ccorres dc xfdc
     invs' UNIV []
     (invokeSchedControlConfigureFlags iv)
     (Call invokeSchedControl_ConfigureFlags_'proc)"
sorry (* FIXME RT: invokeSchedControl_ConfigureFlags_ccorres *)

end

end
