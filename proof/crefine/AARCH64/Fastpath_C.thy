(*
 * Copyright 2024, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Proof that the C fast path functions are refinements of their design
   specifications in Fastpath_Defs. *)

theory Fastpath_C
imports
  SyscallArgs_C
  Delete_C
  Syscall_C
  Fastpath_Defs
  "CLib.MonadicRewrite_C"
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma setCTE_obj_at'_queued:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t\<rbrace> setCTE p v \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t\<rbrace>"
  unfolding setCTE_def
  by (rule setObject_cte_obj_at_tcb', simp+)

crunch obj_at'_queued: cteInsert "obj_at' (\<lambda>tcb. P (tcbQueued tcb)) t"
  (wp: setCTE_obj_at'_queued crunch_wps)

crunch obj_at'_not_queued: emptySlot "obj_at' (\<lambda>a. \<not> tcbQueued a) p"
  (wp: setCTE_obj_at'_queued)

lemma getEndpoint_obj_at':
  "\<lbrace>obj_at' P ptr\<rbrace> getEndpoint ptr \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (wp getEndpoint_wp)
  apply (clarsimp simp: obj_at'_def )
  done

lemmas setEndpoint_obj_at_tcb' = setEndpoint_obj_at'_tcb

lemma tcbSchedEnqueue_tcbContext[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
     tcbSchedEnqueue t'
   \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (rule tcbSchedEnqueue_obj_at_unchangedT[OF all_tcbI])
  apply simp
  done

lemma setCTE_tcbContext:
  "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
  setCTE slot cte
  \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

lemma seThreadState_tcbContext:
 "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
    setThreadState a b
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (rule setThreadState_obj_at_unchanged)
  apply (clarsimp simp: atcbContext_def)+
  done

lemma setBoundNotification_tcbContext:
 "\<lbrace>obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>
    setBoundNotification a b
  \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t\<rbrace>"
  apply (rule setBoundNotification_obj_at_unchanged)
  apply (clarsimp simp: atcbContext_def)+
  done

declare comp_apply [simp del]
crunch tcbContext[wp]: deleteCallerCap "obj_at' (\<lambda>tcb. P ((atcbContextGet o tcbArch) tcb)) t"
  (wp: setEndpoint_obj_at_tcb' setBoundNotification_tcbContext
       setNotification_tcb crunch_wps seThreadState_tcbContext
   simp: crunch_simps unless_def)
declare comp_apply [simp]


crunch ksArch[wp]: asUser "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps)

(* FIXME AARCH64 consider moving this, on MCS there is a tcbs_of as well *)
definition tcbs_of :: "kernel_state \<Rightarrow> machine_word \<Rightarrow> tcb option" where
  "tcbs_of s = (\<lambda>x. if tcb_at' x s then projectKO_opt (the (ksPSpace s x)) else None)"

lemma obj_at_tcbs_of:
  "obj_at' P t s = (EX tcb. tcbs_of s t = Some tcb & P tcb)"
  apply (simp add: tcbs_of_def split: if_split)
  apply (intro conjI impI)
   apply (clarsimp simp: obj_at'_def)
  apply (clarsimp simp: obj_at'_weakenE[OF _ TrueI])
  done

lemma st_tcb_at_tcbs_of:
  "st_tcb_at' P t s = (EX tcb. tcbs_of s t = Some tcb & P (tcbState tcb))"
  by (simp add: st_tcb_at'_def obj_at_tcbs_of)

lemma tcbs_of_ko_at':
  "\<lbrakk> tcbs_of s p = Some tcb \<rbrakk> \<Longrightarrow> ko_at' tcb p s"
  by (simp add: obj_at_tcbs_of)

lemma tcbs_of_valid_tcb':
  "\<lbrakk> valid_objs' s; tcbs_of s p = Some tcb \<rbrakk> \<Longrightarrow> valid_tcb' tcb s"
  by (frule tcbs_of_ko_at')
     (drule (1) ko_at_valid_objs', auto simp:  valid_obj'_def)


end

context kernel_m begin

lemma getCTE_h_val_ccorres_split:
  assumes var: "\<And>s f s'. var (var_update f s) = f (var s)
                  \<and> ((s', var_update f s) \<in> rf_sr) = ((s', s) \<in> rf_sr)"
     and "\<And>rv' t t'. ceqv \<Gamma> var rv' t t' g (g' rv')"
     and "\<And>rv rv'. \<lbrakk> ccap_relation (cteCap rv) rv'; P rv \<rbrakk>
                \<Longrightarrow> ccorres r xf (Q rv) (Q' rv rv') hs (f rv) (g' rv')"
  shows
  "ccorres r xf (\<lambda>s. \<forall>cte. ctes_of s slot = Some cte \<longrightarrow> P cte \<and> Q cte s)
                {s. (\<forall>cte cap. ccap_relation (cteCap cte) cap \<and> P cte
                          \<longrightarrow> var_update (\<lambda>_. cap) s \<in> Q' cte cap)
                           \<and> slot' = cte_Ptr slot} hs
       (getCTE slot >>= (\<lambda>rv. f rv))
   ((Basic (\<lambda>s. var_update (\<lambda>_. h_val (hrs_mem (t_hrs_' (globals s))) (cap_Ptr &(slot' \<rightarrow>[''cap_C'']))) s));; g)"
    (is "ccorres r xf ?G ?G' hs ?f ?g")
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_pre_getCTE)
   apply (rule_tac A="cte_wp_at' ((=) rv and P) slot and Q rv" and A'="?G'" in ccorres_guard_imp2)
    apply (rule_tac P="P rv" in ccorres_gen_asm)
    apply (rule ccorres_symb_exec_r)
      apply (rule_tac xf'=var in ccorres_abstract)
       apply (rule assms)
      apply (rule ccorres_gen_asm2, erule(1) assms)
     apply vcg
    apply (rule conseqPre, vcg, clarsimp simp: var)
   apply (clarsimp simp: cte_wp_at_ctes_of var)
   apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
   apply (clarsimp simp: typ_heap_simps' dest!: ccte_relation_ccap_relation)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma cap_'_cap_'_update_var_props:
  "cap_' (cap_'_update f s) = f (cap_' s) \<and>
         ((s', cap_'_update f s) \<in> rf_sr) = ((s', s) \<in> rf_sr)"
  by simp

lemmas getCTE_cap_h_val_ccorres_split
    = getCTE_h_val_ccorres_split[where var_update=cap_'_update and P=\<top>,
                                 OF cap_'_cap_'_update_var_props]

lemma getCTE_ccorres_helper:
  "\<lbrakk> \<And>\<sigma> cte cte'. \<Gamma> \<turnstile> {s. (\<sigma>, s) \<in> rf_sr \<and> P \<sigma> \<and> s \<in> P' \<and> ctes_of \<sigma> slot = Some cte
                               \<and> cslift s (cte_Ptr slot) = Some cte'
                               \<and> ccte_relation cte cte'}
                       f {s. (\<sigma>, s) \<in> rf_sr \<and> r cte (xf s)} \<rbrakk> \<Longrightarrow>
     ccorres r xf P P' hs (getCTE slot) f"
  apply atomize
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return2)
   apply (rule ccorres_pre_getCTE)
   apply (rule_tac P="cte_wp_at' ((=) x) slot and P"
                in ccorres_from_vcg[where P'=P'])
   apply (erule allEI)
   apply (drule_tac x="the (ctes_of \<sigma> slot)" in spec)
   apply (erule HoarePartial.conseq)
   apply (clarsimp simp: return_def cte_wp_at_ctes_of)
   apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
   apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma acc_CNodeCap_repr:
  "isCNodeCap cap
     \<Longrightarrow> cap = CNodeCap (capCNodePtr cap) (capCNodeBits cap)
                        (capCNodeGuard cap) (capCNodeGuardSize cap)"
  by (clarsimp simp: isCap_simps)

lemma valid_cnode_cap_cte_at':
  "\<lbrakk> s \<turnstile>' c; isCNodeCap c; ptr = capCNodePtr c; v < 2 ^ capCNodeBits c \<rbrakk>
      \<Longrightarrow> cte_at' (ptr + v * 2^cteSizeBits) s"
  apply (drule less_mask_eq)
  apply (drule(1) valid_cap_cte_at'[where addr=v])
  apply (simp add: mult.commute mult.left_commute)
  done

lemmas valid_cnode_cap_cte_at''
  = valid_cnode_cap_cte_at'[simplified objBits_defs, simplified]

lemma ccorres_abstract_all:
  "\<lbrakk>\<And>rv' t t'. ceqv Gamm xf' rv' t t' d (d' rv');
    \<And>rv'. ccorres_underlying sr Gamm r xf arrel axf (G rv') (G' rv') hs a (d' rv')\<rbrakk>
       \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf (\<lambda>s. \<forall>rv'. G rv' s) {s. s \<in> G' (xf' s)} hs a d"
  apply (erule ccorres_abstract)
  apply (rule ccorres_guard_imp2)
   apply assumption
  apply simp
  done

declare of_int_sint_scast[simp]

lemma isCNodeCap_capUntypedPtr_capCNodePtr:
  "isCNodeCap c \<Longrightarrow> capUntypedPtr c = capCNodePtr c"
  by (clarsimp simp: isCap_simps)

lemma of_bl_from_bool:
  "of_bl [x] = from_bool x"
  by (cases x, simp_all)

lemma lookup_fp_ccorres':
  assumes bits: "bits = size cptr"
  shows
  "ccorres (\<lambda>mcp ccp. ccap_relation (case mcp of Inl v => NullCap | Inr v => v) ccp)
                ret__struct_cap_C_'
           (valid_cap' cap and valid_objs')
           ({s. ccap_relation cap (cap_' s)} \<inter> {s. cptr_' s = cptr}) []
       (cutMon ((=) s) (doE t \<leftarrow> resolveAddressBits cap cptr bits;
                             liftE (getSlotCap (fst t))
                         odE))
       (Call lookup_fp_'proc)"
  apply (cinit' lift: cptr_')
   apply (rule ccorres_rhs_assoc2)
   apply (rule ccorres_symb_exec_r)
     apply (rule_tac xf'=ret__int_' in ccorres_abstract, ceqv)
     apply (rule_tac P="rv' = from_bool (isCNodeCap cap)" in ccorres_gen_asm2)
     apply (simp add: from_bool_0 del: Collect_const)
     apply (rule ccorres_Cond_rhs_Seq)
      apply (simp add: resolveAddressBits.simps split_def del: Collect_const)
      apply (rule ccorres_drop_cutMon)
      apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
       apply vcg
      apply (rule conseqPre, vcg)
      apply (clarsimp simp: throwError_def return_def isRight_def isLeft_def
                            ccap_relation_NullCap_iff)
     apply (clarsimp simp del: Collect_const)
     apply (rule_tac P="valid_cap' cap and valid_objs'"
                 and P'="{s. ccap_relation cap (cap_' s) \<and> isCNodeCap cap}
                         \<inter> {s. bits_' s = 64 - of_nat bits \<and> bits \<le> 64 \<and> bits \<noteq> 0}" (* FIXME AARCH64 64 *)
                  in ccorres_inst)
     apply (thin_tac "isCNodeCap cap")
     defer
     apply vcg
    apply (rule conseqPre, vcg)
    apply clarsimp
   apply (clarsimp simp: word_size cap_get_tag_isCap bits
                         of_bl_from_bool from_bool_0)
  proof (induct cap cptr bits arbitrary: s
            rule: resolveAddressBits.induct)
  case (1 acap acptr abits as)

    have valid_cnode_bits_0:
      "\<And>s acap. \<lbrakk> isCNodeCap acap; s \<turnstile>' acap \<rbrakk> \<Longrightarrow> capCNodeBits acap \<noteq> 0"
      by (clarsimp simp: isCap_simps valid_cap'_def)

    have cap_get_tag_update_1:
      "\<And>f cap. cap_get_tag (cap_C.words_C_update (\<lambda>w. Arrays.update w (Suc 0) (f w)) cap) = cap_get_tag cap"
      by (simp add: cap_get_tag_def cong: if_cong)

    show ?case
      supply if_cong[cong] option.case_cong[cong]
      apply (cinitlift cap_' bits_')
      apply (rename_tac cbits ccap)
      apply (elim conjE)
      apply (rule_tac F="capCNodePtr_CL (cap_cnode_cap_lift ccap)
                               = capCNodePtr acap
                          \<and> capCNodeGuardSize acap < 64
                          \<and> capCNodeBits acap < 64
                          \<and> capCNodeGuard_CL (cap_cnode_cap_lift ccap)
                               = capCNodeGuard acap
                          \<and> unat (capCNodeGuardSize_CL (cap_cnode_cap_lift ccap))
                               = capCNodeGuardSize acap
                          \<and> unat (capCNodeRadix_CL (cap_cnode_cap_lift ccap))
                               = capCNodeBits acap
                          \<and> unat (0x40 - capCNodeRadix_CL (cap_cnode_cap_lift ccap))
                               = 64 - capCNodeBits acap
                          \<and> unat ((0x40 :: machine_word) - of_nat abits) = 64 - abits
                          \<and> unat (capCNodeGuardSize_CL (cap_cnode_cap_lift ccap)
                                   + capCNodeRadix_CL (cap_cnode_cap_lift ccap))
                               = capCNodeGuardSize acap + capCNodeBits acap"
                      in Corres_UL_C.ccorres_req)
       apply (clarsimp simp: cap_get_tag_isCap[symmetric])
       apply (clarsimp simp: cap_lift_cnode_cap cap_to_H_simps valid_cap'_def
                             capAligned_def cap_cnode_cap_lift_def objBits_simps
                             word_mod_2p_is_mask[where n=6, simplified]
                      elim!: ccap_relationE)
       apply (simp add: unat_sub[unfolded word_le_nat_alt]
                        unat_of_nat64 word_bits_def)
       apply (subst unat_plus_simple[symmetric], subst no_olen_add_nat)
       apply (rule order_le_less_trans, rule add_le_mono)
         apply (rule word_le_nat_alt[THEN iffD1], rule word_and_le1)+
       apply (simp add: mask_def)
      apply (rule ccorres_guard_imp2)
       apply csymbr+
       apply (rule ccorres_Guard_Seq, csymbr)
       apply (simp add: resolveAddressBits.simps bindE_assoc extra_sle_sless_unfolds
                        Collect_True
                   split del: if_split del: Collect_const)
       apply (simp add: cutMon_walk_bindE del: Collect_const
                           split del: if_split)
       apply (rule ccorres_drop_cutMon_bindE, rule ccorres_assertE)
       apply (rule ccorres_cutMon)
       apply csymbr
       apply (simp add: locateSlot_conv liftE_bindE cutMon_walk_bind)
       apply (rule ccorres_drop_cutMon_bind, rule ccorres_stateAssert)

       apply (rule_tac P="abits < capCNodeBits acap + capCNodeGuardSize acap"
                    in ccorres_case_bools2)
        apply (rule ccorres_drop_cutMon)
        apply csymbr+
        apply (rule ccorres_symb_exec_r)
          apply (rule_tac xf'=ret__int_' in ccorres_abstract_all, ceqv)
          apply (rule ccorres_Cond_rhs_Seq)
           apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
            apply vcg
           apply (rule conseqPre, vcg)
           apply (clarsimp simp: unlessE_def split: if_split)
           apply (simp add: throwError_def return_def cap_tag_defs
                            isRight_def isLeft_def
                            ccap_relation_NullCap_iff
                            in_bindE)
           apply auto[1]
          apply (simp del: Collect_const)
          apply (rule ccorres_Guard_Seq)+
          apply csymbr+
          apply (simp del: Collect_const)
          apply (rule ccorres_move_array_assertion_cnode_ctes ccorres_move_c_guard_cte
                 | csymbr)+
          apply (rule ccorres_symb_exec_r)
            apply ccorres_remove_UNIV_guard
            apply csymbr+
            apply (rule ccorres_cond_false_seq)
            apply (simp add: ccorres_expand_while_iff_Seq[symmetric]
                             whileAnno_def)
            apply (rule ccorres_cond_false)
            apply (rule ccorres_cond_true_seq)
            apply (rule ccorres_from_vcg_split_throws[where P=\<top> and P'=UNIV])
             apply vcg
            apply (rule conseqPre, vcg)
            apply (clarsimp simp: unlessE_def split: if_split)
            apply (simp add: throwError_def return_def cap_tag_defs isRight_def
                             isLeft_def ccap_relation_NullCap_iff)
            apply fastforce
           apply (simp del: Collect_const)
           apply vcg
          apply (rule conseqPre, vcg, clarsimp)
         apply (simp del: Collect_const)
         apply vcg
        apply (rule conseqPre, vcg, clarsimp)
       apply (rule ccorres_cutMon)
       apply (simp add: cutMon_walk_bindE unlessE_whenE
                   del: Collect_const
                   split del: if_split)
       apply (rule ccorres_drop_cutMon_bindE)
       apply csymbr+
       apply (rule ccorres_rhs_assoc2)
       apply (rule_tac r'=dc and xf'=xfdc in ccorres_splitE[OF _ ceqv_refl])
          apply (rule ccorres_Cond_rhs_Seq)
           apply (rule ccorres_Guard_Seq)+
           apply csymbr
           apply (simp add: unat_sub word_le_nat_alt if_1_0_0 shiftl_shiftr3 word_size
                       del: Collect_const)
           apply (rule ccorres_Cond_rhs)
            apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply clarsimp
            apply (clarsimp simp: whenE_def throwError_def return_def
                                  ccap_relation_NullCap_iff isRight_def isLeft_def split_def split: if_split)
           apply (simp add: whenE_def)
           apply (prop_tac "(acptr >> abits - capCNodeGuardSize acap) && mask (capCNodeGuardSize acap) = capCNodeGuard acap")
            apply clarsimp
           apply simp
           apply (rule ccorres_returnOk_skip)
          apply simp
          apply (rule ccorres_cond_false)
          apply (rule_tac P="valid_cap' acap" in ccorres_from_vcg[where P'=UNIV])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: valid_cap'_def isCap_simps if_1_0_0)
          apply (simp add: unat_eq_0[symmetric] whenE_def returnOk_def return_def)
         apply (rule ccorres_cutMon)
         apply (simp add: liftE_bindE locateSlot_conv
                     del: Collect_const)
         apply (rule_tac P="abits = capCNodeBits acap + capCNodeGuardSize acap"
                      in ccorres_case_bools2)
          apply (rule ccorres_drop_cutMon)
          apply (simp del: Collect_const)
          apply (simp add: liftE_def getSlotCap_def del: Collect_const)
          apply (rule ccorres_Guard_Seq)+
          apply csymbr+
          apply simp
          apply (rule ccorres_move_array_assertion_cnode_ctes
                      ccorres_move_c_guard_cte
                      ccorres_rhs_assoc | csymbr)+
          apply (rule getCTE_cap_h_val_ccorres_split)
           apply ceqv
          apply (rename_tac "getCTE_cap")
          apply (csymbr | rule ccorres_Guard_Seq)+
          apply (rule ccorres_cond_false_seq)
          apply (simp add: ccorres_expand_while_iff_Seq[symmetric]
                           whileAnno_def del: Collect_const)
          apply (rule ccorres_cond_false)
          apply (rule ccorres_cond_false_seq)
          apply (simp del: Collect_const)
          apply (rule_tac P'="{s. cap_' s = getCTE_cap}"
                       in ccorres_from_vcg_throws[where P=\<top>])
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: word_sle_def return_def returnOk_def
                                isRight_def)
         apply (simp add: bind_bindE_assoc
                     del: Collect_const if_cong)
         apply (simp add: liftE_bindE "1.prems" unlessE_def
                          cutMon_walk_bind cnode_cap_case_if
                     del: Collect_const cong: if_cong call_ignore_cong)
         apply (rule ccorres_Guard_Seq)+
         apply csymbr+
         apply (simp del: Collect_const)
         apply (rule ccorres_drop_cutMon_bind)
         apply (rule ccorres_getSlotCap_cte_at)
         apply (rule ccorres_move_c_guard_cte
                     ccorres_move_array_assertion_cnode_ctes
                   | csymbr)+
         apply ctac
           apply (csymbr | rule ccorres_Guard_Seq)+
           apply (rule ccorres_cond_true_seq)
           apply (rule ccorres_rhs_assoc | csymbr)+
           apply (simp add: ccorres_expand_while_iff_Seq[symmetric]
                            whileAnno_def if_to_top_of_bindE bindE_assoc
                            split_def
                      cong: if_cong call_ignore_cong)
           apply (rule ccorres_cutMon)
           apply (simp add: cutMon_walk_if)
           apply (rule_tac Q'="\<lambda>s. ret__int_' s = from_bool (isCNodeCap rv)"
                        in ccorres_cond_both'[where Q=\<top>])
             apply (clarsimp simp: from_bool_0)
            apply (rule ccorres_rhs_assoc)+
            apply (rule_tac P="ccorres r xf Gd Gd' hs a" for r xf Gd Gd' hs a in rsubst)
             apply (rule "1.hyps",
                    (rule refl in_returns in_bind[THEN iffD2, OF exI, OF exI, OF conjI]
                         acc_CNodeCap_repr
                          | assumption
                          | clarsimp simp: unlessE_whenE locateSlot_conv
                                           "1.prems"
                          | clarsimp simp: whenE_def[where P=False])+)[1]
            apply (simp add: whileAnno_def extra_sle_sless_unfolds)
           apply (rule ccorres_drop_cutMon)
           apply (simp add: liftE_def getSlotCap_def)
           apply (rule ccorres_pre_getCTE)
           apply (rule ccorres_cond_false_seq)
           apply (rule_tac P="\<lambda>s. cteCap rva = rv" and P'="{s. cap_' s = cap}"
                        in ccorres_from_vcg_throws)
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: return_def returnOk_def word_sle_def isRight_def)
          apply simp
          apply (wp getSlotCap_wp)
         apply simp
         apply vcg
        apply (wp whenE_throwError_wp)
       apply (simp add: ccHoarePost_def del: Collect_const)
       apply vcg
      apply (clarsimp simp: of_bl_from_bool cong: if_cong)
      apply (clarsimp simp: cap_get_tag_isCap
                            option.split[where P="\<lambda>x. x"]
                            isCNodeCap_capUntypedPtr_capCNodePtr)
      apply (clarsimp simp: word_less_nat_alt word_le_nat_alt linorder_not_less
                      cong: conj_cong)
      apply (clarsimp simp: word_less_nat_alt word_le_nat_alt linorder_not_less
                      cong: rev_conj_cong)
      apply (subgoal_tac "\<not> isZombie acap \<and> \<not> isThreadCap acap")
       prefer 2
       apply (clarsimp simp: isCap_simps)
      apply (simp add: imp_conjL)
      apply (simp only: all_simps[symmetric] imp_conjL cong: imp_cong,
             simp only: all_simps, simp)
      apply (simp add: unat_shiftr_le_bound)
      apply (frule(1) valid_cnode_bits_0, clarsimp)
      apply (intro conjI impI)
                     apply (simp add: size_of_def)
                     apply (erule (1) valid_cnode_cap_cte_at'')
                      apply simp
                     apply (rule shiftr_less_t2n')
                      apply simp
                     apply simp
                    apply (simp add:size_of_def)
                    apply (erule (1) valid_cnode_cap_cte_at'')
                     apply simp
                    apply (rule shiftr_less_t2n')
                     apply simp
                    apply simp
                   apply (clarsimp simp: cte_wp_at_ctes_of)
                   apply (clarsimp dest!: ctes_of_valid')
                  apply (simp add: cte_level_bits_def size_of_def field_simps)
                  apply (simp add: shiftl_shiftr3 word_size)
                  apply (simp add: word_bw_assocs mask_and_mask)
                 apply (simp_all add: unat_sub word_le_nat_alt unat_eq_0[symmetric])
               apply (simp_all add: unat_plus_if' if_P)
           apply (clarsimp simp: shiftr_over_and_dist
                                 size_of_def cte_level_bits_def field_simps shiftl_shiftl
                                 shiftl_shiftr3 word_size)+
         apply (clarsimp simp: unat_gt_0 from_bool_0 trans [OF eq_commute from_bool_eq_if])
         apply (intro conjI impI, simp_all)[1]
         apply (rule word_unat.Rep_inject[THEN iffD1], subst unat_plus_if')
         apply (simp add: unat_plus_if' unat_of_nat64 word_bits_def)
        apply (clarsimp simp: shiftr_over_and_dist
                              size_of_def cte_level_bits_def field_simps shiftl_shiftl
                              shiftl_shiftr3 word_size)+
      apply (clarsimp simp: unat_gt_0 from_bool_0 trans [OF eq_commute from_bool_eq_if])

      apply (intro conjI impI, simp_all)[1]
      apply (rule word_unat.Rep_inject[THEN iffD1], simp add: unat_of_nat64 word_bits_def)
      done
qed

lemmas lookup_fp_ccorres
    = lookup_fp_ccorres'[OF refl, THEN ccorres_use_cutMon]

lemma ccap_relation_case_sum_Null_endpoint:
  "ccap_relation (case x of Inl v => NullCap | Inr v => v) ccap
     \<Longrightarrow> (cap_get_tag ccap = scast cap_endpoint_cap)
           = (isRight x \<and> isEndpointCap (theRight x))"
  by (clarsimp simp: cap_get_tag_isCap isRight_def isCap_simps
              split: sum.split_asm)

(* FIXME AARCH64 move *)
lemma ccorres_catch_bindE_symb_exec_l:
  "\<lbrakk> \<And>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>rv. (=) s\<rbrace>; empty_fail f;
      \<And>rv. ccorres_underlying sr G r xf ar axf (Q rv) (Q' rv) hs (catch (g rv) h >>= j) c;
      \<And>ex. ccorres_underlying sr G r xf ar axf (R ex) (R' ex) hs (h ex >>= j) c;
      \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>R\<rbrace> \<rbrakk>
    \<Longrightarrow>
  ccorres_underlying sr G r xf ar axf P {s. (\<forall>rv. s \<in> Q' rv) \<and> (\<forall>ex. s \<in> R' ex)} hs
          (catch (f >>=E g) h >>= j) c"
  apply (simp add: catch_def bindE_def bind_assoc lift_def)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_symb_exec_l[where G=P])
      apply wpc
       apply (simp add: throwError_bind)
       apply assumption+
    apply (clarsimp simp: valid_def validE_def split_def split: sum.split_asm)
   apply assumption
  apply clarsimp
  done

lemma vcpuSwitch_armKSVMIDTable[wp]:
  "vcpuSwitch v \<lbrace>\<lambda>s. P (armKSVMIDTable (ksArchState s))\<rbrace>"
  by (wpsimp simp: vcpuSwitch_def split_def modifyArchState_def)

lemmas vcpuSwitch_typ_ats[wp] = typ_at_lifts [OF vcpuSwitch_typ_at']

crunches findVSpaceForASID
  for (empty_fail) empty_fail[wp,intro!]
  (wp: empty_fail_getObject ignore: withoutFailure)

(* FIXME AARCH64 move to Monadic_Rewrite, also duplicated in Fastpath_Equiv *)
lemma monadic_rewrite_fail:
  "monadic_rewrite True E \<top> fail g"
  by (simp add: monadic_rewrite_def)

(* FIXME AARCH64 move to Monadic_Rewrite in lib *)
lemma monadic_rewrite_return_eq:
  "monadic_rewrite F E (\<lambda>_. (x = y)) (return x) (return y)"
  unfolding monadic_rewrite_def
  by fastforce

(* FIXME AARCH64 taken from EmptyFail_H which is not visible here *)
lemma empty_fail_getObject_ap [intro!, wp, simp]:
  "empty_fail (getObject p :: asidpool kernel)"
  by (simp add: empty_fail_getObject)

(* specific ASID has a specific entry in its ASID pool, or no entry meaning it's not in the pool *)
definition asid_has_entry :: "asid \<Rightarrow> asidpool_entry option \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "asid_has_entry asid asid_map_entry_opt \<equiv> \<lambda>s.
     case armKSASIDTable (ksArchState s) (ucast (asid_high_bits_of (ucast asid)))
       of Some ap_ptr \<Rightarrow> \<exists>pool. ko_at' (asidpool.ASIDPool pool) ap_ptr s
                               \<and> pool (asid && mask asid_low_bits) = asid_map_entry_opt
        | None \<Rightarrow> asid_map_entry_opt = None"

(* the minimum needed to ensure the given asid is mapped to the given vmid *)
(* FIXME AARCH64 consider rename to asid_has_vsroot *)
definition asid_has_vmid :: "asid \<Rightarrow> vmid \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "asid_has_vmid asid vmid vsroot \<equiv> asid_has_entry asid (Some (ASIDPoolVSpace (Some vmid) vsroot))"

lemma getASIDPoolEntry_wp:
  "\<lbrace>\<lambda>s. (\<forall>asid_entry. asid_has_entry asid (Some asid_entry) s \<longrightarrow> P (Some asid_entry) s)
        \<and> (asid_has_entry asid None s \<longrightarrow> P None s) \<rbrace>
   getASIDPoolEntry asid
   \<lbrace>\<lambda>rv s. P rv s \<rbrace>"
  unfolding getASIDPoolEntry_def asid_has_entry_def getPoolPtr_def
  apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift getASID_wp simp: comp_def)
  apply normalise_obj_at'
  apply (rename_tac pool)
  apply (case_tac "pool (asid AND mask asid_low_bits)"; simp)
  done

(* after fastpath checks, next time we getVMID (during thread switch) we know what we'll get *)
lemma getVMID_fp_rewrite:
  "monadic_rewrite True False
     (\<lambda>s. \<exists>vsroot. asid_has_vmid asid vmid vsroot s)
     (getVMID asid) (return vmid)"
  unfolding getVMID_def loadVMID_def getASIDPoolEntry_def getPoolPtr_def liftM_def
  apply (clarsimp simp: bind_assoc)
  apply monadic_rewrite_pre
   apply (rule monadic_rewrite_assert)+
   apply monadic_rewrite_symb_exec_l (* get ASID table *)
    apply (subst case_option_If2)
    apply (monadic_rewrite_l monadic_rewrite_if_l_True)
    apply (clarsimp simp: bind_assoc)
    apply monadic_rewrite_symb_exec_l (* get pool *)
     apply wpc
     apply monadic_rewrite_symb_exec_l (* get entry in pool *)
      apply wpc
       apply simp
       apply (rule monadic_rewrite_fail) (* no entry *)
      apply wpc
      apply simp
      apply (wpc, rule monadic_rewrite_impossible) (* no VMID *)
      apply (drule Some_to_the, simp)+
      apply (rule_tac P="the x1 = vmid" in monadic_rewrite_gen_asm, simp)
      apply (rule monadic_rewrite_refl)
     apply clarsimp
     apply (wpsimp wp: getASID_wp)+
  apply (clarsimp simp: asid_has_vmid_def asid_has_entry_def cong: conj_cong split: option.splits)
  apply normalise_obj_at'
  done

(* after fastpath checks (during thread switch), returned ASID map entry is known *)
lemma getASIDPoolEntry_rewrite_fp:
  "monadic_rewrite True False
     (asid_has_vmid asid vmid vsroot)
     (getASIDPoolEntry asid) (return (Some (asidpool_entry.ASIDPoolVSpace (Some vmid) vsroot)))"
  unfolding getASIDPoolEntry_def getPoolPtr_def
  apply monadic_rewrite_pre
   apply (clarsimp simp: bind_assoc)
   apply (rule monadic_rewrite_assert)+
   apply monadic_rewrite_symb_exec_l (* get ASID table *)
    apply wpc
     apply (rule monadic_rewrite_impossible) (* not found in ASID table *)
    apply (clarsimp simp: liftM_def)
    apply monadic_rewrite_symb_exec_l (* pool ptr *)
    apply wpc
    apply clarsimp
    apply (rule monadic_rewrite_return_eq)
    apply (wpsimp wp: getASID_wp)+
  apply (clarsimp simp: asid_has_vmid_def asid_has_entry_def split: option.splits)
  apply normalise_obj_at'
  done

(* after fastpath checks (during thread switch), returned vspace for ASID is known *)
lemma findVSpaceForASID_rewrite_fp:
  "monadic_rewrite True False
     (asid_has_vmid asid vmid vsroot)
     (findVSpaceForASID asid) (returnOk vsroot)"
  unfolding findVSpaceForASID_def
  apply monadic_rewrite_pre
   apply (clarsimp simp: liftE_bindE)
   apply (monadic_rewrite_l getASIDPoolEntry_rewrite_fp[where vmid=vmid and vsroot=vsroot])
   apply (clarsimp simp: assertE_liftE liftE_bindE)
   apply (rule monadic_rewrite_assert)
   apply (monadic_rewrite_symb_exec_l) (* checkPTAt *)
    apply (rule monadic_rewrite_refl)
   apply wpsimp+
  done

(* After fastpath checks, we know the VMID that armContextSwitch will use.
   Note: there is some confusion here, because the "asid" on the C side is actually a VMID
         (or "hardware asid"), and setVSpaceRoot in Haskell also takes an "asid" that is really
         a VMID, while armContextSwitch takes an actual ASID. *)
lemma armv_contextSwitch_HWASID_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. asid_has_vmid asid vmid vsroot s \<and> canonical_address (addrFromPPtr vsroot))
     (\<lbrace>\<acute>vspace = pte_Ptr vsroot\<rbrace> \<inter> \<lbrace>\<acute>asid___unsigned_long = ucast (vmid :: vmid) \<rbrace>) hs
     (armContextSwitch vsroot asid)
     (Call armv_contextSwitch_HWASID_'proc)"
  apply (cinit lift: vspace_' asid___unsigned_long_')
   apply (rule monadic_rewrite_ccorres_assemble[rotated])
    apply (rule monadic_rewrite_bind_head)
    apply (rule getVMID_fp_rewrite[where vmid=vmid])
   apply clarsimp
   apply csymbr+
   apply (ctac add: setVSpaceRoot_ccorres)
  apply (clarsimp simp: ucast_and_mask_drop canonical_address_and_maskD)
  apply blast
  done

lemma modifyArchState_valid_lift:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> P (f s) \<rbrakk> \<Longrightarrow> modifyArchState f \<lbrace>\<lambda>s. P (ksArchState s) \<rbrace>"
  unfolding modifyArchState_def
  by wpsimp

lemma asid_has_vmid_lift:
  assumes asids: "\<And>P. f \<lbrace>\<lambda>s. P (armKSASIDTable (ksArchState s)) \<rbrace>"
  assumes kos: "\<And>ko p. f \<lbrace>\<lambda>s. ko_at' (ko::asidpool) p s \<rbrace>"
  shows "f \<lbrace> asid_has_vmid asid vmid vsroot \<rbrace>"
  unfolding asid_has_vmid_def asid_has_entry_def
  apply (subst case_option_If2)+
  apply wp_pre
   apply (wps asids)
   apply (rule hoare_vcg_if_lift) (* does not work when combined with wpsimp *)
   apply (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_ex_lift hoare_vcg_conj_lift[OF kos])
  apply auto
  done

lemma vcpuSwitch_asid_has_vmid[wp]:
  "vcpuSwitch t \<lbrace>asid_has_vmid asid vmid vsroot\<rbrace>"
  unfolding vcpuSwitch_def
  by (wpc
      | wpsimp wp: asid_has_vmid_lift modifyArchState_valid_lift simp: split_def
      | simp add: modifyArchState_def)+

(* FIXME AARCH64 for the 0x20, see valid_cnode_cap_cte_at'' *)
lemma switchToThread_fp_ccorres:
  "ccorres dc xfdc
     (pspace_aligned' and pspace_distinct' and valid_objs' and no_0_obj' and valid_arch_state'
      and tcb_at' thread
      and cte_wp_at' (\<lambda>cte. isValidVTableRoot (cteCap cte)
                            \<and> capPTBasePtr (capCap (cteCap cte)) = vsroot
                            \<and> (\<exists>vaddr. capPTMappedAddress (capCap (cteCap cte))
                                       = Some (asid, vaddr)))
                     (thread + tcbVTableSlot * 0x20)
      and asid_has_vmid asid vmid vsroot)
     (\<lbrace> \<acute>thread = tcb_ptr_to_ctcb_ptr thread \<rbrace>
      \<inter> \<lbrace> \<acute>vroot = pte_Ptr vsroot\<rbrace>
      \<inter> \<lbrace> pte_C.words_C \<acute>stored_hw_asid.[unat 0] = ucast vmid \<rbrace>) []
     (do _ <- Arch.switchToThread thread;
         setCurThread thread
      od)
     (Call switchToThread_fp_'proc)"
  supply Collect_const[simp del]
  apply (cinit' lift: thread_' vroot_' stored_hw_asid_')
   apply (simp add: AARCH64_H.switchToThread_def bind_assoc setVMRoot_def
                    cap_case_isPageTableCap)
   apply (simp add: getThreadVSpaceRoot_def locateSlot_conv getSlotCap_def)
   apply (rule ccorres_pre_getObject_tcb)
   apply (ctac (no_vcg) add: vcpu_switch_ccorres)
    apply (rule ccorres_getCTE, rename_tac cte)
    apply (rule_tac P="isValidVTableRoot (cteCap cte)
                       \<and> capPTBasePtr (capCap (cteCap cte)) = vsroot
                       \<and> (\<exists>vaddr. capPTMappedAddress (capCap (cteCap cte))
                                  = Some (asid, vaddr))" in ccorres_gen_asm)
    apply (erule conjE, drule isValidVTableRootD)
    apply (rule ccorres_assert)
    apply simp
    apply (prop_tac "cteCap cte \<noteq> capability.NullCap")
     apply (clarsimp simp: isArchObjectCap_def)
    apply (clarsimp simp: isValidVTableRoot_def2)
    (* rewrite findVSpaceForASID within a bindE+catch *)
    apply (rule monadic_rewrite_ccorres_assemble[rotated])
     apply (rule monadic_rewrite_bind_head)
     apply (rule monadic_rewrite_catch)
       apply (monadic_rewrite_l findVSpaceForASID_rewrite_fp[where vmid=vmid and vsroot=vsroot])
       apply (rule monadic_rewrite_refl)
      apply (rule monadic_rewrite_refl)
     apply wpsimp (* findVSpaceForASID rewrite complete *)
    apply clarsimp
    apply (simp add: catch_liftE bind_assoc assertE_liftE
                flip: bind_liftE_distrib)
    apply (rule ccorres_assert2)
    apply csymbr
    apply (ctac (no_vcg) add: armv_contextSwitch_HWASID_ccorres[where vmid=vmid])
     apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
     apply (clarsimp, rule conseqPre, vcg)
     apply (clarsimp simp: setCurThread_def simpler_modify_def rf_sr_def cstate_relation_def
                           Let_def carch_state_relation_def cmachine_state_relation_def)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift')+

  apply (rule conjI)
   (* haskell precondition *)
   apply (clarsimp simp: cte_level_bits_def field_simps cte_wp_at_ctes_of
                         addrFromPPtr_canonical_in_kernel_window split: option.splits)
   apply (erule (3) valid_tcb'_vcpuE[OF valid_objs_valid_tcb'])
  (* C precondition *)
  apply (clarsimp simp: typ_heap_simps' ctcb_relation_tcbVCPU
                        ucast_and_mask_drop[where n=16, simplified mask_def, simplified])
  done

lemma thread_state_ptr_set_tsType_np_spec:
  defines "ptr s \<equiv> cparent \<^bsup>s\<^esup>ts_ptr [''tcbState_C''] :: tcb_C ptr"
  shows
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ptr s
                 \<and> (tsType_' s = scast ThreadState_Running \<or> tsType_' s = scast ThreadState_Restart
                          \<or> tsType_' s = scast ThreadState_BlockedOnReply)\<rbrace>
              Call thread_state_ptr_set_tsType_np_'proc
       {t. (\<exists>thread_state.
               tsType_CL (thread_state_lift thread_state) = tsType_' s \<and>
               tcbQueued_CL (thread_state_lift thread_state)
                    = tcbQueued_CL (thread_state_lift (tcbState_C (the (cslift s (ptr s))))) \<and>
               t_hrs_' (globals t) = hrs_mem_update (heap_update (ptr s)
                          (the (cslift s (ptr s))\<lparr>tcbState_C := thread_state\<rparr>))
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: ptr_def)
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (frule h_t_valid_c_guard_cparent[OF h_t_valid_clift], simp+,
         simp add: typ_uinfo_t_def)
  apply (frule clift_subtype, simp+)
  apply (clarsimp simp: typ_heap_simps' word_sle_def word_sless_def)
  apply (subst parent_update_child, erule typ_heap_simps', simp+)
  apply (clarsimp simp: typ_heap_simps')
  apply (rule exI, rule conjI[OF _ conjI [OF _ refl]])
  apply (simp_all add: thread_state_lift_def)
  apply (auto simp: "StrictC'_thread_state_defs" mask_def)
  done

(* from the bitfield generator: ep_ref and tsType are stored in the same word, tsType is the lowest
   4 bits, while the at-least-4-aligned ep_ref takes up the next 44 bits (i.e. must be less than
   48 in total, due to canonicity); see structures_64.bf *)
lemma thread_state_ptr_mset_blockingObject_tsType_spec:
  defines "ptr s \<equiv> cparent \<^bsup>s\<^esup>ts_ptr [''tcbState_C''] :: tcb_C ptr"
  shows
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ptr s
              \<and> is_aligned (ep_ref_' s) 4 \<and> canonical_address (ep_ref_' s)
              \<and> tsType_' s && mask 4 = tsType_' s\<rbrace>
          Call thread_state_ptr_mset_blockingObject_tsType_'proc
       {t. (\<exists>thread_state.
               tsType_CL (thread_state_lift thread_state) = tsType_' s
             \<and> blockingObject_CL (thread_state_lift thread_state) = ep_ref_' s
             \<and> tcbQueued_CL (thread_state_lift thread_state)
               = tcbQueued_CL (thread_state_lift (tcbState_C (the (cslift s (ptr s)))))
             \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ptr s)
                       (the (cslift s (ptr s))\<lparr>tcbState_C := thread_state\<rparr>))
                       (t_hrs_' (globals s)))}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: ptr_def)
  apply (frule h_t_valid_c_guard_cparent, simp+)
   apply (simp add: typ_uinfo_t_def)
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (frule clift_subtype, simp+)
  apply (clarsimp simp: typ_heap_simps')
  apply (subst parent_update_child, erule typ_heap_simps', simp+)
  apply (clarsimp simp: typ_heap_simps' word_sless_def word_sle_def)
  apply (rule exI, intro conjI[rotated], rule refl)
    apply (simp_all add: thread_state_lift_def word_ao_dist canonical_address_mask_shift
                         canonical_bit_def is_aligned_mask)
  apply (simp add: and_mask_eq_iff_shiftr_0 shiftr_and_eq_shiftl)
  done

(* FIXME AARCH64 move and consider name, based on or.left_neutral *)
lemma or_left_neutral_eq:
  "x = 0 \<Longrightarrow> x OR y = y"
  by simp

(* FIXME AARCH64 move and consider name *)
lemma or_right_neutral_eq:
  "y = 0 \<Longrightarrow> x OR y = x"
  by simp

(* FIXME AARCH64 move to word lib *)
lemma smaller_mask_0:
  "\<lbrakk> x && mask n = 0; m \<le> n; k \<le> n - m \<rbrakk> \<Longrightarrow> (x >> m) && mask k = 0"
  by (metis and_mask_eq_iff_shiftr_0 linorder_linear mask_AND_less_0 mask_eq_0_eq_x mask_exceed
            shiftr_mask2 shiftr_over_and_dist)

(* FIXME AARCH64 move to word lib *)
lemma shiftr_0_shiftr:
  "\<lbrakk> x >> n = 0; n \<le> m \<rbrakk> \<Longrightarrow> x >> m = 0"
  by (metis Groups.add_ac(2) drop_bit_drop_bit le_add_diff_inverse shiftr_0 shiftr_def)

(* FIXME AARCH64 move to word lib *)
lemma shiftl_shiftr_0_low:
  "\<lbrakk> x >> (m - n) = 0 \<rbrakk> \<Longrightarrow> x << n >> m = 0"
  by (metis shiftl_def shiftr_def take_bit_eq_self_iff_drop_bit_eq_0 take_bit_push_bit)

lemma mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged_spec:
  defines "ptr s \<equiv> cparent \<^bsup>s\<^esup>node_ptr [''cteMDBNode_C''] :: cte_C ptr"
  shows
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ptr s
              \<and> is_aligned (mdbNext___unsigned_long_' s) 4
              \<and> canonical_address (mdbNext___unsigned_long_' s)
              \<and> mdbRevocable___unsigned_long_' s && mask 1 = mdbRevocable___unsigned_long_' s
              \<and> mdbFirstBadged___unsigned_long_' s && mask 1 = mdbFirstBadged___unsigned_long_' s\<rbrace>
          Call mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged_'proc
       {t. (\<exists>mdb_node.
               mdb_node_lift mdb_node = mdb_node_lift (cteMDBNode_C (the (cslift s (ptr s))))
                           \<lparr> mdbNext_CL := mdbNext___unsigned_long_' s, mdbRevocable_CL := mdbRevocable___unsigned_long_' s,
                             mdbFirstBadged_CL := mdbFirstBadged___unsigned_long_' s \<rparr>
               \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ptr s)
                          (the (cslift s (ptr s)) \<lparr> cteMDBNode_C := mdb_node \<rparr>))
                  (t_hrs_' (globals s))
           )}"
  supply shiftl_of_Suc[simp del]
  (* FIXME AARCH64 More_Word.mask_Suc_0 is unnecessary given the other mask_Suc_0, but that one has
     a \<equiv> intead of a =, probably how this confusion started *)
  supply More_Word.mask_Suc_0[simp del] semiring_bit_operations_class.mask_Suc_0[simp del]
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: ptr_def h_t_valid_clift_Some_iff)
  apply (frule h_t_valid_c_guard_cparent[OF h_t_valid_clift], simp+,
         simp add: typ_uinfo_t_def)
  apply (frule clift_subtype, simp+)
  apply (clarsimp simp: typ_heap_simps' word_sle_def word_sless_def)
  apply (subst parent_update_child, erule typ_heap_simps', simp+)
  apply (clarsimp simp: typ_heap_simps')
  apply (rule exI, rule conjI[OF _ refl])
  apply (simp add: mdb_node_lift_def word_ao_dist shiftr_over_or_dist)
  (* rest of proof is resolving magic number shifts+masks based on fields in bitfield generator *)
  apply (simp add: canonical_address_mask_shift canonical_bit_def is_aligned_mask or.assoc)
  apply (fold limited_and_def)
  apply (simp add: limited_and_simps and_mask2 word_size word_and_mask_shiftl)
  apply (simp add: limited_and_def)
  apply (intro conjI)
    apply (rule or_right_neutral_eq)
    apply (simp add: word_or_zero)
    apply (simp add: shiftl_shiftr_0_low and_mask_eq_iff_shiftr_0)
    apply (fastforce simp: shiftr_0_shiftr[where m=2])
   apply (rule or_left_neutral_eq[OF smaller_mask_0[where m=1 and k=1, simplified]], simp+)
  apply (rule or_left_neutral_eq[OF smaller_mask_0[where m=0 and k=1, simplified]], simp+)
  done

lemma mdb_node_ptr_set_mdbPrev_np_spec:
  defines "ptr s \<equiv> cparent \<^bsup>s\<^esup>node_ptr [''cteMDBNode_C''] :: cte_C ptr"
  shows
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ptr s \<and> is_aligned (mdbPrev___unsigned_long_' s) 4\<rbrace>
              Call mdb_node_ptr_set_mdbPrev_np_'proc
       {t. (\<exists>mdb_node.
               mdb_node_lift mdb_node = mdb_node_lift (cteMDBNode_C (the (cslift s (ptr s))))
                           \<lparr> mdbPrev_CL := mdbPrev___unsigned_long_' s \<rparr>
               \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ptr s)
                          (the (cslift s (ptr s)) \<lparr> cteMDBNode_C := mdb_node \<rparr>))
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: ptr_def)
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (frule h_t_valid_c_guard_cparent[OF h_t_valid_clift], simp+,
         simp add: typ_uinfo_t_def)
  apply (frule clift_subtype, simp+)
  apply (clarsimp simp: typ_heap_simps')
  apply (subst parent_update_child, erule typ_heap_simps', simp+)
  apply (clarsimp simp: typ_heap_simps' word_sle_def word_sless_def)
  apply (rule exI, rule conjI [OF _ refl])
  apply (simp add: mdb_node_lift_def limited_and_simps mask_def)
  done

lemma endpoint_ptr_mset_epQueue_tail_state_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ep_ptr_' s
              \<and> is_aligned (epQueue_tail_' s) 4 \<and> canonical_address (epQueue_tail_' s)
              \<and> state_' s && mask 2 = state_' s\<rbrace>
              Call endpoint_ptr_mset_epQueue_tail_state_'proc
       {t. (\<exists>endpoint.
               endpoint_lift endpoint = endpoint_lift (the (cslift s (ep_ptr_' s)))
                           \<lparr> endpoint_CL.state_CL := state_' s, epQueue_tail_CL := epQueue_tail_' s \<rparr>
               \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ep_ptr_' s)
                          endpoint)
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: h_t_valid_clift_Some_iff typ_heap_simps'
                        word_sle_def word_sless_def)
  apply (rule exI, rule conjI[OF _ refl])
  apply (simp add: endpoint_lift_def word_ao_dist)
  apply (subst canonical_address_mask_shift, (simp add: canonical_bit_def)+)
  apply (fold limited_and_def)
  apply (simp add: limited_and_simps mask_def)
  done

lemma endpoint_ptr_set_epQueue_head_np_spec:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. hrs_htd \<^bsup>s\<^esup>t_hrs \<Turnstile>\<^sub>t ep_ptr_' s \<and> is_aligned (epQueue_head_' s) 4\<rbrace>
              Call endpoint_ptr_set_epQueue_head_np_'proc
       {t. (\<exists>endpoint.
               endpoint_lift endpoint = endpoint_lift (the (cslift s (ep_ptr_' s)))
                           \<lparr> epQueue_head_CL := epQueue_head_' s \<rparr>
               \<and> t_hrs_' (globals t) = hrs_mem_update (heap_update (ep_ptr_' s)
                          endpoint)
                  (t_hrs_' (globals s))
           )}"
  apply (intro allI, rule conseqPre, vcg)
  apply (clarsimp simp: h_t_valid_clift_Some_iff typ_heap_simps'
                        word_sless_def word_sle_def)
  apply (rule exI, rule conjI[OF _ refl])
  apply (simp add: endpoint_lift_def word_ao_dist
                   mask_def)
  done

lemma ccorres_call_hSkip':
  assumes  cul: "ccorres_underlying sr \<Gamma> r xf' r xf' P (i ` P') [SKIP] a (Call f)"
  and      gsr: "\<And>a b x s t. (x, t) \<in> sr \<Longrightarrow> (x, g a b (clean s t)) \<in> sr"
  and      csr: "\<And>x s t. (x, t) \<in> sr \<Longrightarrow> (x, clean s t) \<in> sr"
  and      res: "\<And>a s t rv. r rv (xf' t) \<Longrightarrow> r rv (xf (g a t (clean s t)))"
  and     ares: "\<And>s t rv. r rv (xf' t) \<Longrightarrow> r rv (xf (clean s t))"
  and      ist: "\<And>x s. (x, s) \<in> sr \<Longrightarrow> (x, i s) \<in> sr"
  shows "ccorres_underlying sr \<Gamma> r xf r xf P P' [SKIP] a (call i f clean (\<lambda>x y. Basic (g x y)))"
  apply (rule ccorresI')
  apply (erule exec_handlers.cases, simp_all)[1]
   apply clarsimp
   apply (erule exec_call_Normal_elim, simp_all)[1]
    apply (clarsimp elim!: exec_Normal_elim_cases)
   apply (rule ccorresE[OF cul ist], assumption+, simp+)
    apply (rule EHAbrupt)
     apply (erule(1) exec.Call)
    apply (rule EHOther, rule exec.Skip, simp)
   apply clarsimp
   apply (erule exec_handlers.cases, simp_all)[1]
    apply (clarsimp elim!: exec_Normal_elim_cases)
   apply (clarsimp elim!: exec_Normal_elim_cases)
   apply (erule rev_bexI)
   apply (simp add: unif_rrel_simps csr ares)
  apply clarsimp
  apply (erule exec_call_Normal_elim, simp_all)[1]
     apply (clarsimp elim!: exec_Normal_elim_cases)
     apply (rule ccorresE[OF cul ist], assumption+, simp+)
      apply (rule EHOther, erule(1) exec.Call)
      apply simp
     apply (simp add: unif_rrel_simps)
     apply (erule rev_bexI)
     apply (simp add: gsr res)
    apply (rule ccorresE[OF cul ist], assumption+, simp+)
     apply (rule EHOther, erule(1) exec.Call)
     apply simp
    apply simp
   apply (rule ccorresE[OF cul ist], assumption+, simp+)
    apply (rule EHOther, erule(1) exec.Call)
    apply simp
   apply simp
  apply (rule ccorresE[OF cul ist], assumption+, simp+)
   apply (rule EHOther, erule exec.CallUndefined)
   apply simp
  apply simp
  done

(* The naming convention here is that xf', xfr, and xfru are the terms we instantiate *)
lemma ccorres_call_hSkip:
  assumes  cul: "ccorres_underlying rf_sr \<Gamma> r xfdc r xfdc A C' [SKIP] a (Call f)"
  and      ggl: "\<And>x y s. globals (g x y s) = globals s"
  and      igl: "\<And>s. globals (i s) = globals s"
  shows "ccorres_underlying rf_sr \<Gamma> r xfdc r xfdc
          A {s. i s \<in> C'} [SKIP] a (call i f (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>x y. Basic (g x y)))"
  using cul
  unfolding rf_sr_def
  apply -
  apply (rule ccorres_call_hSkip')
       apply (erule ccorres_guard_imp)
        apply (clarsimp simp: ggl igl xfdc_def)+
  done

lemma bind_case_sum_rethrow:
  "rethrowFailure fl f >>= case_sum e g
   = f >>= case_sum (e \<circ> fl) g"
  apply (simp add: rethrowFailure_def handleE'_def bind_assoc)
  apply (rule bind_cong[OF refl])
  apply (simp add: throwError_bind split: sum.split)
  done

lemma ccorres_pre_getCTE2:
  "(\<And>rv. ccorresG rf_sr \<Gamma> r xf (P rv) (P' rv) hs (f rv) c) \<Longrightarrow>
   ccorresG rf_sr \<Gamma> r xf (\<lambda>s. \<forall>cte. ctes_of s p = Some cte \<longrightarrow> P cte s)
                         {s. \<forall>cte cte'. cslift s (cte_Ptr p) = Some cte' \<and> ccte_relation cte cte'
                                          \<longrightarrow> s \<in> P' cte} hs
         (getCTE p >>= (\<lambda>rv. f rv)) c"
  apply (rule ccorres_guard_imp2, erule ccorres_pre_getCTE)
  apply (clarsimp simp: map_comp_Some_iff ccte_relation_def c_valid_cte_def cl_valid_cte_def
                        c_valid_cap_def)
  done

declare empty_fail_resolveAddressBits[iff]

(* this condition is copied directly from fastpath_mi_check_spec, which comes out of guards there *)
lemma fastpath_mi_check:
  "(\<not> 4 < mi && 0x1FF)
      = (msgExtraCaps (messageInfoFromWord mi) = 0
            \<and> msgLength (messageInfoFromWord mi) \<le> scast n_msgRegisters
            \<and> length_CL (seL4_MessageInfo_lift (seL4_MessageInfo_C (FCP (K mi))))
                  \<le> scast n_msgRegisters)"
  (is "?P = (?Q \<and> ?R \<and> ?S)")
proof -
  have le_Q: "?P = (?Q \<and> ?S)"
    apply (simp add: mask_def messageInfoFromWord_def Let_def
                     msgExtraCapBits_def msgLengthBits_def
                     seL4_MessageInfo_lift_def fcp_beta n_msgRegisters_def)
    apply word_bitwise
    apply blast
    done
  have Q_R: "?S \<Longrightarrow> ?R"
    apply (clarsimp simp: messageInfoFromWord_def Let_def msgLengthBits_def
                          msgExtraCapBits_def mask_def n_msgRegisters_def
                          seL4_MessageInfo_lift_def fcp_beta)
    apply (subst if_not_P, simp_all)
    apply (simp add: msgMaxLength_def linorder_not_less)
    apply (erule order_trans, simp)
    done
  from le_Q Q_R show ?thesis
    by blast
qed

lemma messageInfoFromWord_raw_spec:
  "\<forall>s. \<Gamma>\<turnstile> {s} Call messageInfoFromWord_raw_'proc
       \<lbrace>\<acute>ret__struct_seL4_MessageInfo_C
    = (seL4_MessageInfo_C (FCP (K \<^bsup>s\<^esup>w)))\<rbrace>"
  apply vcg
  apply (clarsimp simp: word_sless_def word_sle_def)
  apply (case_tac v)
  apply (simp add: cart_eq)
  done

lemma mi_check_messageInfo_raw:
  "length_CL (seL4_MessageInfo_lift (seL4_MessageInfo_C (FCP (K mi)))) \<le> scast n_msgRegisters
    \<Longrightarrow> seL4_MessageInfo_lift (seL4_MessageInfo_C (FCP (K mi)))
       = mi_from_H (messageInfoFromWord mi)"
  apply (simp add: messageInfoFromWord_def Let_def mi_from_H_def
                   seL4_MessageInfo_lift_def msgLengthBits_def msgExtraCapBits_def
                   msgMaxExtraCaps_def shiftL_nat mask_def msgLabelBits_def)
  apply (subst if_not_P)
   apply (simp add: linorder_not_less msgMaxLength_def n_msgRegisters_def)
   apply (erule order_trans, simp)
  apply simp
  done

lemma fastpath_mi_check_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. True\<rbrace> Call fastpath_mi_check_'proc
           \<lbrace>(\<acute>ret__int = 0) = (msgExtraCaps (messageInfoFromWord \<^bsup>s\<^esup>msgInfo) = 0
              \<and> msgLength (messageInfoFromWord \<^bsup>s\<^esup>msgInfo) \<le> scast n_msgRegisters
              \<and> seL4_MessageInfo_lift (seL4_MessageInfo_C (FCP (K \<^bsup>s\<^esup>msgInfo)))
                = mi_from_H (messageInfoFromWord \<^bsup>s\<^esup>msgInfo))\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: seL4_MsgLengthBits_def seL4_MsgExtraCapBits_def word_sle_def if_1_0_0)
  apply (cut_tac mi="msgInfo_' s" in fastpath_mi_check)
  apply (auto intro: mi_check_messageInfo_raw[unfolded K_def])
  done

lemma isValidVTableRoot_fp_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call isValidVTableRoot_fp_'proc
       {t. ret__unsigned_long_' t = from_bool (isValidVTableRoot_C (vspace_root_cap_' s))}"
  apply vcg
  apply (clarsimp simp: word_sle_def word_sless_def cong: if_cong)
  (* FIXME AARCH64 how are most of these not in the simpset already? *)
  apply (simp add: to_bool_if of_bl_from_bool from_bool_eq_if' from_bool_0)
  apply (clarsimp simp: isValidVTableRoot_C_def)
  done

lemma isRecvEP_endpoint_case:
  "isRecvEP ep \<Longrightarrow> case_endpoint f g h ep = f (epQueue ep)"
  by (clarsimp simp: isRecvEP_def split: endpoint.split_asm)

lemma unifyFailure_catch_If:
  "catch (unifyFailure f >>=E g) h
     = f >>= (\<lambda>rv. if isRight rv then catch (g (theRight rv)) h else h ())"
  apply (simp add: unifyFailure_def rethrowFailure_def
                   handleE'_def catch_def bind_assoc
                   bind_bindE_assoc cong: if_cong)
  apply (rule bind_cong[OF refl])
  apply (simp add: throwError_bind isRight_def return_returnOk
            split: sum.split)
  done

end

abbreviation "tcb_Ptr_Ptr \<equiv> (Ptr :: machine_word \<Rightarrow> tcb_C ptr ptr)"

abbreviation(input)
  "ptr_basic_update ptrfun vfun
      \<equiv> Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update
                    (heap_update (ptrfun s) (vfun s)))) s)"

context kernel_m begin

lemma fastpath_dequeue_ccorres:
  "dest1 = dest2 \<and> dest2 = tcb_ptr_to_ctcb_ptr dest \<and> ep_ptr1 = ep_Ptr ep_ptr \<Longrightarrow>
   ccorres dc xfdc
       (ko_at' (RecvEP (dest # xs)) ep_ptr and invs')
            {s. dest2 = tcb_ptr_to_ctcb_ptr dest
               \<and> dest1 = tcb_ptr_to_ctcb_ptr dest
               \<and> ep_ptr1 = ep_Ptr ep_ptr} hs
   (setEndpoint ep_ptr (case xs of [] \<Rightarrow> IdleEP | _ \<Rightarrow> RecvEP xs))
   (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t dest1\<rbrace>
     (CALL endpoint_ptr_set_epQueue_head_np(ep_ptr1,ptr_val (h_val (hrs_mem \<acute>t_hrs) (tcb_Ptr_Ptr &(dest2\<rightarrow>[''tcbEPNext_C''])))));;
      Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t dest1\<rbrace>
     (IF h_val (hrs_mem \<acute>t_hrs) (tcb_Ptr_Ptr &(dest1\<rightarrow>[''tcbEPNext_C''])) \<noteq> tcb_Ptr 0 THEN
      Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t h_val (hrs_mem \<acute>t_hrs) (tcb_Ptr_Ptr &(dest1\<rightarrow>[''tcbEPNext_C'']))\<rbrace>
       (Guard C_Guard {s. s \<Turnstile>\<^sub>c dest1} (
       (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &(h_val (hrs_mem (t_hrs_' (globals s)))
                                (tcb_Ptr_Ptr &(dest1\<rightarrow>[''tcbEPNext_C'']))\<rightarrow>[''tcbEPPrev_C''])) (\<lambda>_. NULL))))
      ELSE
        CALL endpoint_ptr_mset_epQueue_tail_state(ep_ptr1,0,scast EPState_Idle)
      FI))"
  unfolding setEndpoint_def
  apply (rule setObject_ccorres_helper[rotated])
    apply simp
   apply (simp add: objBits_simps')
  apply (rule conseqPre, vcg)
  apply clarsimp
  apply (drule(1) ko_at_obj_congD')
  apply (frule ko_at_valid_ep', clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_ep], assumption,
         erule ko_at_projectKO_opt)
  apply (clarsimp simp: typ_heap_simps' valid_ep'_def
                        isRecvEP_endpoint_case neq_Nil_conv)
  apply (drule(1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps')
  apply (case_tac "xs")
   apply (clarsimp simp: cendpoint_relation_def Let_def
                         isRecvEP_endpoint_case
                         tcb_queue_relation'_def
                         typ_heap_simps' endpoint_state_defs)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
   apply (rule conjI)
    apply (clarsimp simp: cpspace_relation_def update_ep_map_tos
                          typ_heap_simps')
    apply (erule(1) cpspace_relation_ep_update_ep2)
     apply (simp add: cendpoint_relation_def endpoint_state_defs)
    apply simp
   apply (simp add: carch_state_relation_def cmachine_state_relation_def
                    h_t_valid_clift_Some_iff update_ep_map_tos
                    typ_heap_simps')
  apply (clarsimp simp: neq_Nil_conv cendpoint_relation_def Let_def
                        isRecvEP_endpoint_case tcb_queue_relation'_def
                        typ_heap_simps' endpoint_state_defs)
  apply (simp add: is_aligned_weaken[OF is_aligned_tcb_ptr_to_ctcb_ptr, simplified ctcb_size_bits_def])
  apply (drule(1) obj_at_cslift_tcb)+
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        typ_heap_simps' tcb_at_not_NULL[OF obj_at'_weakenE, OF _ TrueI])
  apply (rule conjI)
   apply (clarsimp simp: cpspace_relation_def update_ep_map_tos
                         update_tcb_map_tos typ_heap_simps')
   apply (rule conjI, erule ctcb_relation_null_queue_ptrs)
    apply (rule ext, simp add: tcb_null_queue_ptrs_def
                     split: if_split)
   apply (rule conjI)
    apply (rule cpspace_relation_ep_update_ep, assumption+)
     apply (simp add: Let_def cendpoint_relation_def EPState_Recv_def)
     apply (simp add: tcb_queue_relation'_def tcb_queue_update_other)
    apply (simp add: isRecvEP_def)
   apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
   apply simp
   apply (rule cnotification_relation_ep_queue [OF invs_sym'], assumption+)
     apply (simp add: isRecvEP_def)
    apply simp
   apply (erule (1) map_to_ko_atI')
  apply (simp add: carch_state_relation_def typ_heap_simps'
                   cmachine_state_relation_def h_t_valid_clift_Some_iff
                   update_ep_map_tos)
  apply (erule cready_queues_relation_null_queue_ptrs)
  apply (rule ext, simp add: tcb_null_ep_ptrs_def split: if_split)
  done

lemma st_tcb_at_not_in_ep_queue:
  "\<lbrakk> st_tcb_at' P t s; ko_at' ep epptr s; sym_refs (state_refs_of' s);
     ep \<noteq> IdleEP; \<And>ts. P ts \<Longrightarrow> tcb_st_refs_of' ts = {} \<rbrakk>
      \<Longrightarrow> t \<notin> set (epQueue ep)"
  apply clarsimp
  apply (drule(1) sym_refs_ko_atD')
  apply (cases ep, simp_all add: st_tcb_at_refs_of_rev')
   apply (fastforce simp: st_tcb_at'_def obj_at'_def)+
  done

lemma st_tcb_at_not_in_ntfn_queue:
  "\<lbrakk> st_tcb_at' P t s; ko_at' ntfn ntfnptr s; sym_refs (state_refs_of' s); ntfnObj ntfn = WaitingNtfn xs;
     \<And>ts. P ts \<Longrightarrow> (ntfnptr, TCBSignal) \<notin> tcb_st_refs_of' ts \<rbrakk>
      \<Longrightarrow> t \<notin> set xs"
  apply (drule(1) sym_refs_ko_atD')
  apply (clarsimp simp: st_tcb_at_refs_of_rev')
  apply (drule_tac x="(t, NTFNSignal)" in bspec, simp)
  apply (fastforce simp: st_tcb_at'_def obj_at'_def ko_wp_at'_def tcb_bound_refs'_def)
  done

lemma cntfn_relation_double_fun_upd:
  "\<lbrakk> cnotification_relation mp ntfn ntfn'
       = cnotification_relation (mp(a := b)) ntfn ntfn';
     cnotification_relation (mp(a := b)) ntfn ntfn'
       = cnotification_relation (mp(a := b, c := d)) ntfn ntfn' \<rbrakk>
   \<Longrightarrow> cnotification_relation mp ntfn ntfn'
         = cnotification_relation (mp(a := b, c := d)) ntfn ntfn'"
  by simp

lemma sym_refs_upd_sD:
  "\<lbrakk> sym_refs ((state_refs_of' s) (p := S)); valid_pspace' s;
            ko_at' ko p s; refs_of' (injectKO koEx) = S;
            objBits koEx = objBits ko \<rbrakk>
      \<Longrightarrow> \<exists>s'. sym_refs (state_refs_of' s')
               \<and> (\<forall>p' (ko' :: endpoint). ko_at' ko' p' s \<and> injectKO ko' \<noteq> injectKO ko
                          \<longrightarrow> ko_at' ko' p' s')
               \<and> (\<forall>p' (ko' :: Structures_H.notification). ko_at' ko' p' s \<and> injectKO ko' \<noteq> injectKO ko
                          \<longrightarrow> ko_at' ko' p' s')
               \<and> (ko_at' koEx p s')"
  apply (rule exI, rule conjI)
   apply (rule state_refs_of'_upd[where ko'="injectKO koEx" and ptr=p and s=s,
                                  THEN ssubst[where P=sym_refs], rotated 2])
     apply simp+
   apply (clarsimp simp: obj_at'_def ko_wp_at'_def)
   apply (clarsimp simp: project_inject objBits_def)
  apply (clarsimp simp: obj_at'_def ps_clear_upd
                 split: if_split)
  apply (clarsimp simp: project_inject objBits_def)
  apply auto
  done

lemma sym_refs_upd_tcb_sD:
  "\<lbrakk> sym_refs ((state_refs_of' s) (p := {r \<in> state_refs_of' s p. snd r = TCBBound})); valid_pspace' s;
            ko_at' (tcb :: tcb) p s \<rbrakk>
      \<Longrightarrow> \<exists>s'. sym_refs (state_refs_of' s')
               \<and> (\<forall>p' (ko' :: endpoint).
                          ko_at' ko' p' s \<longrightarrow> ko_at' ko' p' s')
               \<and> (\<forall>p' (ko' :: Structures_H.notification).
                          ko_at' ko' p' s \<longrightarrow> ko_at' ko' p' s')
               \<and> (st_tcb_at' ((=) Running) p s')"
  apply (drule(2) sym_refs_upd_sD[where koEx="makeObject\<lparr>tcbState := Running, tcbBoundNotification := tcbBoundNotification tcb\<rparr>"])
    apply (clarsimp dest!: ko_at_state_refs_ofD')
   apply (simp add: objBits_simps)
  apply (erule exEI)
  apply clarsimp
  apply (auto simp: st_tcb_at'_def elim!: obj_at'_weakenE)
  done

lemma fastpath_enqueue_ccorres:
  "\<lbrakk> epptr' = ep_Ptr epptr \<rbrakk> \<Longrightarrow>
   ccorres dc xfdc
         (ko_at' ep epptr and (\<lambda>s. thread = ksCurThread s)
                and (\<lambda>s. sym_refs ((state_refs_of' s) (thread := {r \<in> state_refs_of' s thread. snd r = TCBBound})))
                and K (\<not> isSendEP ep) and valid_pspace' and cur_tcb')
         UNIV hs
     (setEndpoint epptr (case ep of IdleEP \<Rightarrow> RecvEP [thread] | RecvEP ts \<Rightarrow> RecvEP (ts @ [thread])))
     (\<acute>ret__unsigned_longlong :== CALL endpoint_ptr_get_epQueue_tail(epptr');;
      \<acute>endpointTail :== tcb_Ptr \<acute>ret__unsigned_longlong;;
      IF \<acute>endpointTail = tcb_Ptr 0 THEN
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>ksCurThread\<rbrace>
            (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((ksCurThread_' (globals s))\<rightarrow>[''tcbEPPrev_C''])) (\<lambda>_. NULL)));;
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>ksCurThread\<rbrace>
          (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((ksCurThread_' (globals s))\<rightarrow>[''tcbEPNext_C''])) (\<lambda>_. NULL)));;
           (CALL endpoint_ptr_set_epQueue_head_np(epptr',ucast (ptr_val \<acute>ksCurThread)));;
           (CALL endpoint_ptr_mset_epQueue_tail_state(epptr',ucast (ptr_val \<acute>ksCurThread),
            scast EPState_Recv))
      ELSE
        Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>endpointTail\<rbrace>
          (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((endpointTail_' s)\<rightarrow>[''tcbEPNext_C'']))
                      (ksCurThread_' o globals));;
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>ksCurThread\<rbrace>
          (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((ksCurThread_' (globals s))\<rightarrow>[''tcbEPPrev_C'']))
                      endpointTail_'));;
         (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>ksCurThread\<rbrace>
          (ptr_basic_update (\<lambda>s. tcb_Ptr_Ptr &((ksCurThread_' (globals s))\<rightarrow>[''tcbEPNext_C'']))
                      (\<lambda>_. NULL)));;
           (CALL endpoint_ptr_mset_epQueue_tail_state(epptr',ucast (ptr_val \<acute>ksCurThread),
            scast EPState_Recv))
      FI)"
  unfolding setEndpoint_def
  apply clarsimp
  apply (rule setObject_ccorres_helper[rotated])
    apply simp
   apply (simp add: objBits_simps')
  apply (rule conseqPre, vcg)
  apply clarsimp
  apply (drule(1) ko_at_obj_congD')
  apply (frule ko_at_valid_ep', clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_ep], assumption,
         erule ko_at_projectKO_opt)
  apply (simp add: cur_tcb'_def)
  apply (frule(1) obj_at_cslift_tcb)
  apply (clarsimp simp: typ_heap_simps' valid_ep'_def rf_sr_ksCurThread)
  apply (prop_tac "canonical_address (ptr_val (tcb_ptr_to_ctcb_ptr (ksCurThread \<sigma>)))")
   apply (fastforce intro!: canonical_address_tcb_ptr intro: obj_at'_is_canonical tcb_aligned')
  apply (prop_tac "is_aligned (ptr_val (tcb_ptr_to_ctcb_ptr (ksCurThread \<sigma>))) 4")
   apply (meson is_aligned_tcb_ptr_to_ctcb_ptr is_aligned_weaken kernel.ctcb_size_bits_ge_4)
  apply (cases ep,
         simp_all add: isSendEP_def cendpoint_relation_def Let_def
                       tcb_queue_relation'_def)
   apply (rename_tac list)
   apply (clarsimp simp: NULL_ptr_val[symmetric] tcb_queue_relation_last_not_NULL
                         ct_in_state'_def
                  dest!: trans [OF sym [OF ptr_val_def] arg_cong[where f=ptr_val]])
   apply (frule obj_at_cslift_tcb[rotated], erule(1) bspec[OF _ last_in_set])
   apply clarsimp
   apply (drule(2) sym_refs_upd_tcb_sD)
   apply clarsimp
   apply (frule st_tcb_at_not_in_ep_queue,
          fastforce, simp+)
   apply (prop_tac "ksCurThread \<sigma> \<noteq> last list")
    apply clarsimp
   apply (clarsimp simp: typ_heap_simps' EPState_Recv_def mask_def
                         is_aligned_weaken[OF is_aligned_tcb_ptr_to_ctcb_ptr])
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
   apply (rule conjI)
    apply (clarsimp simp: cpspace_relation_def update_ep_map_tos
                          typ_heap_simps')
    apply (rule conjI, erule ctcb_relation_null_queue_ptrs)
     apply (rule ext, simp add: tcb_null_queue_ptrs_def
                         split: if_split)
    apply (rule conjI)
     apply (rule_tac S="tcb_ptr_to_ctcb_ptr ` set (ksCurThread \<sigma> # list)"
                  in cpspace_relation_ep_update_an_ep,
                 assumption+)
         apply (simp add: cendpoint_relation_def Let_def EPState_Recv_def
                          tcb_queue_relation'_def)
         apply (drule_tac qend="tcb_ptr_to_ctcb_ptr (last list)"
                     and qend'="tcb_ptr_to_ctcb_ptr (ksCurThread \<sigma>)"
                     and tn_update="tcbEPNext_C_update"
                     and tp_update="tcbEPPrev_C_update"
                     in tcb_queue_relation_append,
                    clarsimp+, simp_all)[1]
           apply (rule sym, erule init_append_last)
          apply (fastforce simp: tcb_at_not_NULL)
         apply (clarsimp simp add: tcb_at_not_NULL[OF obj_at'_weakenE[OF _ TrueI]])
        apply clarsimp+
     apply (subst st_tcb_at_not_in_ep_queue, assumption, blast, clarsimp+)
     apply (drule(1) ep_ep_disjoint[rotated -1, where epptr=epptr],
            blast, blast,
            simp_all add: Int_commute endpoint_not_idle_cases image_image)[1]
    apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
    apply simp
    apply (rule cntfn_relation_double_fun_upd)
     apply (rule cnotification_relation_ep_queue, assumption+)
        apply fastforce
       apply (simp add: isRecvEP_def)
      apply simp
     apply (fastforce dest!: map_to_ko_atI)

    apply (rule cnotification_relation_q_cong)
    apply (clarsimp split: if_split)
    apply (clarsimp simp: restrict_map_def ntfn_q_refs_of'_def
                   split: if_split Structures_H.notification.split_asm Structures_H.ntfn.split_asm)
    apply (erule notE[rotated], erule_tac ntfnptr=p and ntfn=a in st_tcb_at_not_in_ntfn_queue,
           auto dest!: map_to_ko_atI)[1]
   apply (simp add: carch_state_relation_def typ_heap_simps' update_ep_map_tos
                    cmachine_state_relation_def h_t_valid_clift_Some_iff)
   apply (erule cready_queues_relation_null_queue_ptrs)
   apply (rule ext, simp add: tcb_null_ep_ptrs_def split: if_split)
  apply (clarsimp simp: typ_heap_simps' EPState_Recv_def mask_def
                        is_aligned_weaken[OF is_aligned_tcb_ptr_to_ctcb_ptr])
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (drule(2) sym_refs_upd_tcb_sD)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: cpspace_relation_def update_ep_map_tos
                         typ_heap_simps' ct_in_state'_def)
   apply (rule conjI, erule ctcb_relation_null_queue_ptrs)
    apply (rule ext, simp add: tcb_null_queue_ptrs_def
                        split: if_split)
   apply (rule conjI)
    apply (rule_tac S="{tcb_ptr_to_ctcb_ptr (ksCurThread \<sigma>)}"
                 in cpspace_relation_ep_update_an_ep, assumption+)
        apply (simp add: cendpoint_relation_def Let_def EPState_Recv_def
                         tcb_queue_relation'_def)
       apply clarsimp+
    apply (erule notE[rotated], erule st_tcb_at_not_in_ep_queue,
           auto)[1]
   apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
   apply simp
   apply (rule cnotification_relation_q_cong)
   apply (clarsimp split: if_split)
   apply (clarsimp simp: restrict_map_def ntfn_q_refs_of'_def
                  split: if_split Structures_H.notification.split_asm Structures_H.ntfn.split_asm)
   apply (erule notE[rotated], rule_tac ntfnptr=p and ntfn=a in st_tcb_at_not_in_ntfn_queue,
          assumption+, auto dest!: map_to_ko_atI)[1]
  apply (simp add: carch_state_relation_def typ_heap_simps' update_ep_map_tos
                   cmachine_state_relation_def h_t_valid_clift_Some_iff)
  apply (erule cready_queues_relation_null_queue_ptrs)
  apply (rule ext, simp add: tcb_null_ep_ptrs_def split: if_split)
  done

lemma setCTE_rf_sr:
  "\<lbrakk> (\<sigma>, s) \<in> rf_sr; ctes_of \<sigma> ptr = Some cte'';
     t_hrs_' (globals s') = hrs_mem_update
        (heap_update (cte_Ptr ptr) cte')
        (t_hrs_' (globals s));
     ccte_relation cte cte';
     (globals s')\<lparr> t_hrs_' := undefined \<rparr>
          = (globals s)\<lparr> t_hrs_' := undefined \<rparr> \<rbrakk>
      \<Longrightarrow>
   \<exists>x\<in>fst (setCTE ptr cte \<sigma>).
             (snd x, s') \<in> rf_sr"
  apply (rule fst_setCTE[OF ctes_of_cte_at], assumption)
  apply (erule rev_bexI)
  apply clarsimp
  apply (frule(1) rf_sr_ctes_of_clift)
  apply (subgoal_tac "\<exists>hrs. globals s' = globals s
                          \<lparr> t_hrs_' := hrs \<rparr>")
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         typ_heap_simps' cpspace_relation_def)
   apply (rule conjI)
    apply (erule(2) cmap_relation_updI, simp)
   apply (erule_tac t = s'a in ssubst)
   apply (simp add: heap_to_user_data_def)
   apply (rule conjI)
    apply (erule(1) setCTE_tcb_case)
   apply (simp add: carch_state_relation_def cmachine_state_relation_def
                    cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                    typ_heap_simps' h_t_valid_clift_Some_iff)
  apply (cases "globals s", cases "globals s'")
  apply simp
  done

lemma getCTE_setCTE_rf_sr:
  "\<lbrakk> (\<sigma>, s) \<in> rf_sr; ctes_of \<sigma> ptr = Some cte;
     t_hrs_' (globals s') = hrs_mem_update
        (heap_update (cte_Ptr ptr) cte')
        (t_hrs_' (globals s));
     ccte_relation (f cte) cte';
     (globals s')\<lparr> t_hrs_' := undefined \<rparr>
          = (globals s)\<lparr> t_hrs_' := undefined \<rparr> \<rbrakk>

      \<Longrightarrow>
   \<exists>x\<in>fst ((do cte \<leftarrow> getCTE ptr;
                      setCTE ptr (f cte)
                    od)
                    \<sigma>).
             (snd x, s') \<in> rf_sr"
  apply (drule setCTE_rf_sr, assumption+)
  apply (clarsimp simp: Bex_def in_bind_split in_getCTE2 cte_wp_at_ctes_of)
  done

lemma ccte_relation_eq_ccap_relation:
  notes option.case_cong_weak [cong]
  shows
  "ccte_relation cte ccte
      = (ccap_relation (cteCap cte) (cte_C.cap_C ccte)
            \<and> mdb_node_to_H (mdb_node_lift (cteMDBNode_C ccte))
                   = (cteMDBNode cte))"
  apply (simp add: ccte_relation_def map_option_Some_eq2 cte_lift_def
                   ccap_relation_def)
  apply (simp add: cte_to_H_def split: option.split)
  apply (cases cte, clarsimp simp: c_valid_cte_def conj_comms)
  done

lemma cap_reply_cap_ptr_new_np_updateCap_ccorres:
  "ccorres dc xfdc
        (cte_at' ptr and tcb_at' thread)
        ({s. cap_ptr_' s = cap_Ptr &(cte_Ptr ptr \<rightarrow> [''cap_C''])}
         \<inter> {s. capTCBPtr___unsigned_long_' s = ptr_val (tcb_ptr_to_ctcb_ptr thread)}
         \<inter> {s. capReplyMaster___unsigned_long_' s = from_bool m}
         \<inter> {s. capReplyCanGrant___unsigned_long_' s = from_bool canGrant}) []
     (updateCap ptr (ReplyCap thread m canGrant))
     (Call cap_reply_cap_ptr_new_np_'proc)"
  apply (rule ccorres_from_vcg, rule allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp simp: cte_wp_at_ctes_of word_sle_def)
  apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
  apply (clarsimp simp: updateCap_def split_def typ_heap_simps'
                        word_sless_def word_sle_def)
  apply (erule(1) getCTE_setCTE_rf_sr, simp_all add: packed_heap_update_collapse_hrs typ_heap_simps')
  apply (clarsimp simp: ccte_relation_eq_ccap_relation ccap_relation_def c_valid_cap_def)
  apply (frule is_aligned_tcb_ptr_to_ctcb_ptr)
  apply (rule ssubst[OF cap_lift_reply_cap])
   apply (simp add: cap_get_tag_def cap_reply_cap_def mask_def)
   apply (cases m ; cases canGrant ; clarsimp simp: true_def false_def)
  apply (simp add: cap_to_H_simps cl_valid_cap_def cap_reply_cap_def
                   limited_and_simps1[OF lshift_limited_and, OF limited_and_from_bool])
  apply (cases m ; cases canGrant ; clarsimp simp: true_def false_def)
  done

lemma fastpath_copy_mrs_ccorres:
notes nat_min_simps [simp del]
shows
  "ccorres dc xfdc (\<top> and (\<lambda>_. len <= length AARCH64_H.msgRegisters))
     (UNIV \<inter> {s. unat (length___unsigned_long_' s) = len}
           \<inter> {s. src_' s = tcb_ptr_to_ctcb_ptr src}
           \<inter> {s. dest_' s = tcb_ptr_to_ctcb_ptr dest}) []
     (forM_x (take len AARCH64_H.msgRegisters)
             (\<lambda>r. do v \<leftarrow> asUser src (getRegister r);
                    asUser dest (setRegister r v) od))
     (Call fastpath_copy_mrs_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit' lift: length___unsigned_long_' src_' dest_' simp: word_sle_def word_sless_def)
   apply (unfold whileAnno_def)
   apply (rule ccorres_rel_imp)
    apply (rule_tac F="K \<top>" in ccorres_mapM_x_while)
        apply clarsimp
        apply (rule ccorres_guard_imp2)
         apply (rule ccorres_rhs_assoc)+
         apply (rule_tac xf'="i_'" in ccorres_abstract, ceqv)
         apply csymbr
         apply (ctac(no_vcg))
          apply ctac
         apply wp
        apply (clarsimp simp: rf_sr_ksCurThread)
        apply (simp add: msgRegisters_ccorres[symmetric] length_msgRegisters)
        apply (simp add: n_msgRegisters_def msgRegisters_unfold)
        apply (drule(1) order_less_le_trans)
        apply ((clarsimp simp: "StrictC'_register_defs" msgRegistersC_def fupdate_def
                | drule nat_less_cases' | erule disjE)+)[2]
      apply (rule allI, rule conseqPre, vcg)
      apply simp
     apply (simp add: length_msgRegisters n_msgRegisters_def word_bits_def hoare_TrueI)+
  done

lemma updateCap_cte_wp_at_cteMDBNode:
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteMDBNode cte)) p\<rbrace>
     updateCap ptr cap
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteMDBNode cte)) p\<rbrace>"
  apply (wp updateCap_cte_wp_at_cases)
  apply (simp add: o_def)
  done

lemma ctes_of_Some_cte_wp_at:
  "ctes_of s p = Some cte \<Longrightarrow> cte_wp_at' P p s = P cte"
  by (clarsimp simp: cte_wp_at_ctes_of)

lemma user_getreg_wp:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> (\<forall>rv. obj_at' (\<lambda>tcb. (user_regs \<circ> atcbContextGet \<circ> tcbArch) tcb r = rv) t s
        \<longrightarrow> Q rv s)\<rbrace>
   asUser t (getRegister r) \<lbrace>Q\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. \<exists>rv'. rv' = rv \<and> Q rv' s" in hoare_post_imp)
   apply simp
  apply (rule hoare_pre, wp hoare_vcg_ex_lift user_getreg_rv)
  apply (clarsimp simp: obj_at'_def)
  done

lemma ccorres_flip_Guard2:
  assumes cc: "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F S (Guard F1 S1 c) ;; d)"
  shows "ccorres_underlying sr \<Gamma> r xf arrel axf A C hs a (Guard F1 S1 (Guard F S c) ;; d)"
  apply (rule ccorres_name_pre_C)
  using cc
  apply (case_tac "s \<in> (S1 \<inter> S)")
   apply (clarsimp simp: ccorres_underlying_def)
   apply (erule exec_handlers.cases;
    fastforce elim!: exec_Normal_elim_cases intro: exec_handlers.intros exec.Guard exec.Seq)
  apply (clarsimp simp: ccorres_underlying_def)
  apply (case_tac "s \<in> S")
   apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros exec.Seq)
  apply (fastforce intro: exec.Guard exec.GuardFault exec_handlers.intros exec.Seq)
  done

lemmas cte_C_numeral_fold =
  cte_C_size[THEN meta_eq_to_obj_eq,
             THEN arg_cong[where f="of_nat :: _ \<Rightarrow> machine_word"], simplified, symmetric]

lemmas ccorres_move_c_guard_tcb_ctes2 = ccorres_move_c_guard_tcb_ctes[unfolded cte_C_numeral_fold]

lemma setUntypedCapAsFull_replyCap[simp]:
  "setUntypedCapAsFull cap (ReplyCap curThread False cg) slot =  return ()"
   by (clarsimp simp:setUntypedCapAsFull_def isCap_simps)

end

context kernel_m begin

lemma obj_at_bound_tcb_grandD:
  "\<lbrakk> obj_at' P t s; valid_objs' s; no_0_obj' s; (s, s') \<in> rf_sr \<rbrakk>
    \<Longrightarrow> \<exists>tcb tcb' ntfn ntfn'. ko_at' tcb t s \<and> P tcb
       \<and> cslift s' (tcb_ptr_to_ctcb_ptr t) = Some tcb'
       \<and> ctcb_relation tcb tcb'
       \<and> ((tcbBoundNotification_C tcb' = NULL) = (tcbBoundNotification tcb = None))
       \<and> (tcbBoundNotification tcb \<noteq> None \<longrightarrow> ko_at' ntfn (the (tcbBoundNotification tcb)) s)
       \<and> (tcbBoundNotification tcb \<noteq> None \<longrightarrow> cslift s' (tcbBoundNotification_C tcb') = Some ntfn')
       \<and> (tcbBoundNotification tcb \<noteq> None \<longrightarrow> cnotification_relation (cslift s') ntfn ntfn')"
  apply (clarsimp simp: pred_tcb_at'_def)
  apply (drule(1) obj_at_cslift_tcb, clarsimp)
  apply (rule exI, rule conjI, assumption)
  apply (clarsimp simp: ctcb_relation_def
                                 option_to_ptr_def option_to_0_def)
  apply (simp add: return_def split: option.split_asm)
  apply (drule_tac s="ntfn_Ptr x"for x in sym)
  apply (drule(1) ko_at_valid_objs', clarsimp simp: )
  apply (clarsimp simp:  valid_obj'_def valid_tcb'_def)
  apply (drule obj_at_ko_at', clarsimp)
  apply (rule conjI, clarsimp)
  apply (rule cmap_relationE1[OF cmap_relation_ntfn], assumption, erule ko_at_projectKO_opt)
  apply auto
  done

lemma cnotification_relation_isActive:
  "cnotification_relation tcbs ntfn ntfn'
       \<Longrightarrow> (notification_CL.state_CL (notification_lift ntfn') = scast NtfnState_Active)
     = EndpointDecls_H.isActive ntfn"
  apply (clarsimp simp: cnotification_relation_def Let_def)
  apply (cases ntfn, simp)
  apply (rename_tac ntfna ooeuoue)
  apply (case_tac ntfna, simp_all add: notification_state_defs isActive_def)
  done

lemma option_case_liftM_getNotification_wp:
  "\<lbrace>\<lambda>s. \<forall>rv. (case x of None \<Rightarrow> rv = v | Some p \<Rightarrow> obj_at' (\<lambda>ntfn. f ntfn = rv) p s)
    \<longrightarrow> Q rv s\<rbrace> case x of None \<Rightarrow> return v | Some ptr \<Rightarrow> liftM f $ getNotification ptr \<lbrace> Q \<rbrace>"
  apply (rule hoare_pre, (wpc; wp getNotification_wp))
  apply (auto simp: obj_at'_def)
  done

lemma threadSet_st_tcb_at_state:
  "\<lbrace>\<lambda>s. tcb_at' t s \<longrightarrow> (if p = t
        then obj_at' (\<lambda>tcb. P (tcbState (f tcb))) t s
        else st_tcb_at' P p s)\<rbrace>
  threadSet f t \<lbrace>\<lambda>_. st_tcb_at' P p\<rbrace>"
  apply (rule hoare_chain)
    apply (rule threadSet_obj_at'_really_strongest)
   prefer 2
   apply (simp add: st_tcb_at'_def)
  apply (clarsimp split: if_splits simp: st_tcb_at'_def o_def)
  done

lemma recv_ep_queued_st_tcb_at':
  "\<lbrakk> ko_at' (Structures_H.endpoint.RecvEP ts) epptr s ;
     t \<in> set ts;
     sym_refs (state_refs_of' s) \<rbrakk>
   \<Longrightarrow> st_tcb_at' isBlockedOnReceive t s"
  apply (drule obj_at_ko_at')
  apply clarsimp
  apply (drule (1) sym_refs_ko_atD')
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_real_def refs_of_rev')
  apply (erule_tac x=t in ballE; clarsimp?)
  apply (erule ko_wp_at'_weakenE)
  apply (clarsimp simp: isBlockedOnReceive_def )
  done

lemma signed_n_msgRegisters_to_H:
  "(signed n_msgRegisters :: machine_word) = of_nat size_msgRegisters"
  by (simp add: n_msgRegisters_def size_msgRegisters_def)

(* FIXME AARCH64 isValidVTableRootD is too weak, doesn't enforce pt_t *)
lemma isValidVTableRootD':
  "isValidVTableRoot cap
   \<Longrightarrow> isArchObjectCap cap \<and> isArchVSpacePTCap cap
      \<and> capPTMappedAddress (capCap cap) \<noteq> None"
  by (simp add: isValidVTableRoot_def isVTableRoot_def isCap_simps
         split: capability.split_asm arch_capability.split_asm
                option.split_asm)

(* FIXME AARCH64 in this file, we see ptr + 0x20 * tcbVTableSlot a lot, where the 0x20 is
   2 ^ cte_level_bits
   This used to be 0x10 on 32-bit, so unlikely to change soon, but still might be worth a cleanup
   or abbreviation. This is one way it could work (and can go outside Arch locale): *)
declare cte_level_bits_def[code]
value_abbreviation (input) cte_size "(2::machine_word) ^ cte_level_bits"

lemma casid_map_relation_get_tag_None:
  "(casid_map_relation amap_opt amap')
   \<Longrightarrow> (asid_map_get_tag amap' = scast asid_map_asid_map_none) = (amap_opt = None)"
  apply (cases amap_opt, clarsimp)
  apply (rename_tac amap)
  apply (case_tac amap, clarsimp simp: casid_map_relation_vspace_tag)
  done

lemma vspace_cap_capUntypedPtr_capPTBasePtr:
  "isArchVSpacePTCap cap \<Longrightarrow> capUntypedPtr cap = capPTBasePtr (capCap cap)"
  unfolding isArchVSpacePTCap_def
  by (clarsimp split: capability.splits arch_capability.splits)

(* FIXME AARCH64 move *)
lemma setObject_tcb_asidpool_obj_at'[wp]:
  "\<lbrace>obj_at' (P :: asidpool \<Rightarrow> bool) ptr\<rbrace> setObject ptr' (tcb :: tcb) \<lbrace>\<lambda>rv. obj_at' P ptr\<rbrace>"
  apply (rule obj_at_setObject2, simp_all)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

(* FIXME AARCH64 move *)
crunch asidpool_obj_at'[wp]: setThreadState "obj_at' (P :: asidpool \<Rightarrow> bool) ptr"
  (simp: unless_def)

(* FIXME AARCH64 move, used to be in CNodeInv_R *)
lemma updateMDB_cte_wp_at_other:
 "\<lbrace>cte_wp_at' P p and (\<lambda>s. m \<noteq> p)\<rbrace>
  updateMDB m f
  \<lbrace>\<lambda>uu. cte_wp_at' P p\<rbrace>"
  unfolding updateMDB_def
  by (wpsimp wp: setCTE_cte_wp_at_other)+

(* This is needed since the fast path takes the capVSBasePtr_CL of a cap before it knows it's
   a vspace cap, then it checks that it's a vspace cap afterwards. Using the normal spec rule would
   result in an unprovable obligation that we're reading a vspace cap *)
lemma cap_vspace_cap_get_capVSBasePtr_spec2:
  "\<forall>s. \<Gamma>\<turnstile> \<lbrace>s. True\<rbrace>
          Call cap_vspace_cap_get_capVSBasePtr_'proc
          \<lbrace>cap_get_tag \<^bsup>s\<^esup>cap = scast cap_vspace_cap
           \<longrightarrow> \<acute>ret__unsigned_longlong = capVSBasePtr_CL (cap_vspace_cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply (clarsimp simp: word_sle_def word_sless_def
                        cap_vspace_cap_lift_def
                        cap_lift_vspace_cap mask_def)
  done

lemma asUser_obj_at_asidpool[wp]:
  "\<lbrace>obj_at' (P :: asidpool \<Rightarrow> bool) t\<rbrace>
   asUser t' f
   \<lbrace>\<lambda>rv. obj_at' P t\<rbrace>"
  apply (simp add: asUser_def threadGet_stateAssert_gets_asUser)
  apply (wp threadSet_ko_wp_at2', clarsimp) (* FIXME AARCH64 wpsimp fails here *)
  done

(* FIXME AARCH64 original setCTE_asidpool' is too specific by demanding a constructor!  *)
lemma setCTE_asidpool'[wp]:
  "\<lbrace> ko_at' (ko :: asidpool) p \<rbrace> setCTE c p' \<lbrace>\<lambda>_. ko_at' ko p\<rbrace>"
  by (cases ko, simp)
     (wp setCTE_asidpool')

lemma updateMDB_ko_at'_asidpool[wp]:
  "\<lbrace>ko_at' (ko :: asidpool) p \<rbrace> updateMDB ptr f \<lbrace>\<lambda>_. ko_at' ko p \<rbrace>"
  unfolding updateMDB_def Let_def
  by (wpsimp wp: setCTE_asidpool')

lemma isArchVSpacePTCap_def2:
  "isArchVSpacePTCap cap
   = (\<exists>base map_data. cap = ArchObjectCap (PageTableCap base VSRootPT_T map_data))"
  by (clarsimp simp: isArchVSpacePTCap_def
              split: capability.splits arch_capability.splits pt_type.splits)

lemma capVSBasePtr_CL_capUntypedPtr_helper:
  "\<lbrakk> ccap_relation cap cap'; isValidVTableRoot cap \<rbrakk>
   \<Longrightarrow> capVSBasePtr_CL (cap_vspace_cap_lift cap') = global.capUntypedPtr cap"
  by (clarsimp simp: cap_get_tag_isCap vspace_cap_capUntypedPtr_capPTBasePtr
                     isArchVSpacePTCap_def2 ccap_relation_vspace_base
               dest!: isValidVTableRootD')

lemma casid_map_relation_Some_get_tag:
  "casid_map_relation (Some asid_entry) asid_entry'
   \<Longrightarrow> asid_map_get_tag asid_entry' = signed asid_map_asid_map_vspace"
  by (clarsimp simp: casid_map_relation_def asid_map_lift_def Let_def
               split: option.splits if_splits asid_map_CL.splits)

lemma setObject_endpoint_asidpool_obj_at'[wp]:
  "\<lbrace>obj_at' (P :: asidpool \<Rightarrow> bool) ptr\<rbrace> setObject ptr' (ep :: endpoint) \<lbrace>\<lambda>rv. obj_at' P ptr\<rbrace>"
  apply (rule obj_at_setObject2, simp_all)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma setEndpoint_obj_at'_asidpool[wp]:
  "\<lbrace>obj_at' (P :: asidpool \<Rightarrow> bool) t \<rbrace> setEndpoint ptr (e::endpoint) \<lbrace>\<lambda>_. obj_at' (P :: asidpool \<Rightarrow> bool) t\<rbrace>"
  by (clarsimp simp: setEndpoint_def, wp)

lemma casid_map_relation_Some_c_lift_eqs:
  "\<lbrakk> casid_map_relation (Some asid_map_entry) asid_map_entry' \<rbrakk>
   \<Longrightarrow> (apVMID asid_map_entry = Some vmid
       \<longrightarrow> stored_hw_vmid_CL (asid_map_asid_map_vspace_lift asid_map_entry') = ucast vmid)
      \<and> (stored_vmid_valid_CL (asid_map_asid_map_vspace_lift asid_map_entry') = 0)
        = (apVMID asid_map_entry = None)
      \<and> vspace_root_CL (asid_map_asid_map_vspace_lift asid_map_entry') = apVSpace asid_map_entry"
  apply (clarsimp simp: casid_map_relation_def casid_map_relation_Some_get_tag
                        to_bool_def asid_map_asid_map_vspace_lift_def
                  split: option.splits asid_map_CL.splits)
  apply (clarsimp simp: asid_map_lift_def Let_def ucast_ucast_mask
                  split: if_splits)
  done

(* when we know P is true, but we can't use subst or clarsimp due to schematics *)
lemma ccorres_If_True_drop:
  "\<lbrakk> P; ccorres_underlying sr Gamm r xf arrel axf R R' hs a c \<rbrakk>
   \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf R R' hs (If P a b) c"
  by simp

lemma fastpath_call_ccorres:
  notes hoare_TrueI[simp] if_cong[cong] option.case_cong[cong]
  notes from_bool_0[simp] (* FIXME AARCH64 should go in simpset *)
  shows "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> ct_in_state' ((=) Running) s
          \<and> obj_at' (\<lambda>tcb. (user_regs o atcbContextGet o tcbArch) tcb AARCH64_H.capRegister = cptr
          \<and>  (user_regs o atcbContextGet o tcbArch) tcb AARCH64_H.msgInfoRegister = msginfo)
                (ksCurThread s) s)
     ({s. cptr_' s = cptr} \<inter> {s. msgInfo_' s = msginfo}) []
     (fastpaths SysCall) (Call fastpath_call_'proc)"
proof -
    have [simp]: "scast Kernel_C.tcbCaller = tcbCallerSlot"
     by (simp add: Kernel_C.tcbCaller_def tcbCallerSlot_def)
    have [simp]: "scast Kernel_C.tcbVTable = tcbVTableSlot"
     by (simp add: Kernel_C.tcbVTable_def tcbVTableSlot_def)

    have tcbs_of_cte_wp_at_vtable:
      "\<And>s tcb ptr. tcbs_of s ptr = Some tcb \<Longrightarrow>
      cte_wp_at' \<top> (ptr + 0x20 * tcbVTableSlot) s"
    apply (clarsimp simp: tcbs_of_def cte_at'_obj_at'
                    split: if_splits)
    apply (drule_tac x = "0x20 * tcbVTableSlot" in bspec)
     apply (simp add: tcb_cte_cases_def tcbVTableSlot_def cteSizeBits_def)
    apply simp
    done

  have tcbs_of_cte_wp_at_caller:
    "\<And>s tcb ptr. tcbs_of s ptr = Some tcb \<Longrightarrow>
    cte_wp_at' \<top> (ptr + 0x20 * tcbCallerSlot) s"
    apply (clarsimp simp: tcbs_of_def cte_at'_obj_at'
                    split: if_splits)
    apply (drule_tac x = "0x20 * tcbCallerSlot" in bspec)
     apply (simp add: tcb_cte_cases_def tcbCallerSlot_def cteSizeBits_def)
    apply simp
    done

  have tcbs_of_aligned':
    "\<And>s ptr tcb. \<lbrakk>tcbs_of s ptr = Some tcb;pspace_aligned' s\<rbrakk> \<Longrightarrow> is_aligned ptr tcbBlockSizeBits"
    apply (clarsimp simp: tcbs_of_def obj_at'_def split: if_splits)
    apply (drule pspace_alignedD')
    apply simp+
    apply (simp add: projectKO_opt_tcb objBitsKO_def
                split: Structures_H.kernel_object.splits)
    done

  show ?thesis
    supply if_cong[cong] option.case_cong[cong] Collect_const[simp del]
    apply (cinit lift: cptr_' msgInfo_')
     (* this also lifts out pickFastpath alternative to general alternative, but not clear what
        pickFastpath is for  *)
     apply (simp add: catch_liftE_bindE unlessE_throw_catch_If
                      unifyFailure_catch_If catch_liftE
                      getMessageInfo_def alternative_bind
                cong: if_cong call_ignore_cong)
     apply (rule ccorres_pre_getCurThread)
     apply (rename_tac curThread)
     apply (rule ccorres_symb_exec_l3[OF _ user_getreg_inv' _ empty_fail_user_getreg])+
       apply (rename_tac msginfo' cptr')
       apply (rule_tac P="msginfo' = msginfo \<and> cptr' = cptr" in ccorres_gen_asm)
       (* the call_ignore_cong in this proof is required to prevent corruption of arguments in
          endpoint_ptr_mset_epQueue_tail_state_'proc so that eventually fastpath_dequeue_ccorres
          can apply  *)
       apply (simp cong: call_ignore_cong)
       apply (simp only:)
       apply (csymbr, csymbr)
       (* get fault type *)
       apply csymbr
       apply (rule_tac r'="\<lambda>ft ft'. (ft' = scast seL4_Fault_NullFault) = (ft = None)" and
                       xf'=ret__unsigned_longlong_' in ccorres_split_nothrow)
           apply (rule_tac P="cur_tcb' and (\<lambda>s. curThread = ksCurThread s)"
                           in ccorres_from_vcg[where P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: cur_tcb'_def rf_sr_ksCurThread)
           apply (drule(1) obj_at_cslift_tcb, clarsimp)
           apply (clarsimp simp: typ_heap_simps' ctcb_relation_def cfault_rel_def)
           apply (rule rev_bexI, erule threadGet_eq)
           apply (clarsimp simp: seL4_Fault_lift_def Let_def split: if_split_asm)
          apply ceqv
         apply (rename_tac fault fault')
         apply (rule ccorres_alternative1) (* pick pickFastpath = True, still not clear what it's for *)
         apply csymbr
         apply csymbr
         apply (simp cong: call_ignore_cong)
         apply (rule ccorres_if_cond_throws2[where Q=\<top> and Q'=\<top>, rotated -1])
            (* fault, message info overflows registers, or extra caps present: abort *)
            apply (vcg exspec=slowpath_noreturn_spec)
           apply (clarsimp simp: signed_n_msgRegisters_to_H messageInfoFromWord_def Let_def mi_from_H_def
                                 seL4_MessageInfo_lift_def msgLengthBits_def msgExtraCapBits_def
                                 msgMaxExtraCaps_def shiftL_nat mask_def msgLabelBits_def)
           apply (fastforce simp: size_msgRegisters_def msgMaxLength_def split: if_splits)
          apply (rule ccorres_call_hSkip)
            apply (rule slowpath_ccorres)
           apply simp
          apply simp

         apply (simp cong: call_ignore_cong)
         apply (elim conjE)
         (* look up invoked cap *)
         apply (rule ccorres_abstract_ksCurThread, ceqv)
         apply (rule_tac P="ct = curThread" in ccorres_gen_asm, simp only:, thin_tac "ct = curThread")
         apply (simp add: getThreadCSpaceRoot_def locateSlot_conv cong: call_ignore_cong)
         apply (rule ccorres_pre_getCTE2)
         apply (rule ccorres_move_array_assertion_tcb_ctes
                     ccorres_move_c_guard_tcb_ctes2
                     ccorres_move_const_guard
                     ccorres_rhs_assoc)+
         apply (ctac add: lookup_fp_ccorres)
           apply (rename_tac luRet ep_cap)
           apply (rule ccorres_abstract_ksCurThread, ceqv)
           apply (rule_tac P="ct = curThread" in ccorres_gen_asm, simp only:, thin_tac "ct = curThread")
           apply (rule ccorres_move_array_assertion_tcb_ctes | simp cong: call_ignore_cong)+
           (* check invoked cap *)
           apply (csymbr, csymbr)
           apply (simp add: ccap_relation_case_sum_Null_endpoint of_bl_from_bool cong: call_ignore_cong)
           apply (rule ccorres_Cond_rhs_Seq)
            (* not an endpoint cap *)
            apply (simp cong: if_cong)
            apply (rule ccorres_cond_true_seq)
            apply (rule ccorres_split_throws)
             apply (rule ccorres_call_hSkip)
               apply (erule disjE; simp; rule slowpath_ccorres)
              apply simp
             apply simp
            apply (vcg exspec=slowpath_noreturn_spec)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr+
           apply (simp add: isRight_case_sum cong: call_ignore_cong)
           apply (elim conjE)
           apply (frule (1) cap_get_tag_isCap[THEN iffD2])
           apply (simp add: ccap_relation_ep_helpers cong: call_ignore_cong)
           apply (rule ccorres_Cond_rhs_Seq)
            (* can't send to ep *)
            apply simp
            apply (rule ccorres_split_throws)
             apply (rule ccorres_call_hSkip)
               apply (rule slowpath_ccorres, simp+)
            apply (vcg exspec=slowpath_noreturn_spec)
           apply (simp cong: call_ignore_cong)
           (* get the endpoint address *)
           apply (csymbr, csymbr)
           apply (simp add: ccap_relation_ep_helpers cong: call_ignore_cong)
           (* get destination thread from ep queue, get endpoint / get endpoint state on C side *)
           apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
           apply (rule_tac xf'="\<lambda>s. (dest_' s, ret__unsigned_longlong_' s)"
                       and r'="\<lambda>ep v. snd v = scast EPState_Recv = isRecvEP ep
                                      \<and> (isRecvEP ep \<longrightarrow> epQueue ep \<noteq> []
                                      \<and> fst v = tcb_ptr_to_ctcb_ptr (hd (epQueue ep)))"
                        in ccorres_split_nothrow)
               apply (rule ccorres_add_return2)
               apply (rule ccorres_pre_getEndpoint, rename_tac ep)
               apply (rule_tac P="ko_at' ep (capEPPtr (theRight luRet)) and valid_objs'"
                               in ccorres_from_vcg[where P'=UNIV])
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: return_def)
               apply (erule cmap_relationE1[OF cmap_relation_ep], erule ko_at_projectKO_opt)
               apply (frule(1) ko_at_valid_ep')
               apply (clarsimp simp: typ_heap_simps')
               apply (simp add: cendpoint_relation_def Let_def isRecvEP_def
                                endpoint_state_defs valid_ep'_def
                         split: endpoint.split_asm)
               apply (clarsimp simp: tcb_queue_relation'_def neq_Nil_conv)
              apply (rule ceqv_tuple2)
               apply ceqv
              apply ceqv
             apply (rename_tac send_ep dest_and_ep_state')
             apply (rule_tac P="ko_at' send_ep (capEPPtr (theRight luRet))
                                and valid_objs'" in ccorres_cross_over_guard)
             apply (simp cong: call_ignore_cong)
             apply (rule ccorres_Cond_rhs_Seq)
              (* ep state not ready to receive *)
              apply simp
              apply (rule ccorres_split_throws)
               apply (rule ccorres_call_hSkip)
                 apply (rule slowpath_ccorres, simp+)
              apply (vcg exspec=slowpath_noreturn_spec)

             (* get vspace root *)
             apply (simp add: getThreadVSpaceRoot_def locateSlot_conv cong: call_ignore_cong)
             apply (rule ccorres_move_c_guard_tcb_ctes2
                         ccorres_move_array_assertion_tcb_ctes
                         ccorres_move_const_guard)+
             apply (rule_tac var="newVTable_'" and var_update="newVTable_'_update"
                          in getCTE_h_val_ccorres_split[where P=\<top>])
               apply simp
              apply ceqv
             apply (rename_tac vs_cap vs_cap')
             (* get capVSBasePtr from the vspace cap on C side (we don't know it's vspace cap yet) *)
             apply (rule ccorres_symb_exec_r) (* can't use csymbr, we need use alternative spec rule *)
               apply (rule_tac xf'=ret__unsigned_longlong_' in ccorres_abstract, ceqv)
               apply (rename_tac vspace_cap_c_ptr_maybe)
               apply csymbr+
               apply (simp add: isValidVTableRoot_conv cong: call_ignore_cong)
               apply (rule ccorres_Cond_rhs_Seq)
                (* \<not> isValidVTableRoot (cteCap vs_cap) *)
                apply simp
                apply (rule ccorres_split_throws)
                 apply (rule ccorres_call_hSkip)
                   apply (rule slowpath_ccorres, simp+)
                apply (vcg exspec=slowpath_noreturn_spec)
               apply (simp cong: call_ignore_cong)

               (* AARCH64+hyp specific *)
               apply (drule isValidVTableRootD')
               (* we now know base address we read on the C side was from a vspace cap *)
               apply (rule_tac P="vspace_cap_c_ptr_maybe = capUntypedPtr (cteCap vs_cap)"
                            in ccorres_gen_asm2)
               apply (simp cong: call_ignore_cong)

               (* C: get the asid *)
               apply (rule ccorres_rhs_assoc2)
               apply (rule_tac xf'=asid___unsigned_long_'
                           and val="fst (the (capPTMappedAddress (capCap (cteCap vs_cap))))"
                            in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
                  apply (rule conseqPre, vcg)
                  apply (clarsimp simp: cap_get_tag_isCap isArchVSpacePTCap_def2
                                        ccap_relation_vspace_mapped_asid[symmetric])
                 apply ceqv
                (* get asid_entry for asid *)
                apply (ctac add: findMapForASID_ccorres)
                  apply (rename_tac asid_map_entry_opt asid_map_entry')
                  apply csymbr
                  apply csymbr
                  apply (simp add: casid_map_relation_get_tag_None cong: call_ignore_cong)
                  apply (rule ccorres_Cond_rhs_Seq)
                   (* no asid map entry for asid *)
                   apply simp
                   apply (rule ccorres_cond_true_seq)
                   apply (rule ccorres_split_throws)
                    apply (rule ccorres_call_hSkip)
                      apply (rule slowpath_ccorres, simp+)
                   apply (vcg exspec=slowpath_noreturn_spec)
                  apply (simp cong: call_ignore_cong)

               apply (rule_tac xf'=ret__int_'
                           and val="from_bool (apVSpace (the asid_map_entry_opt)
                                               \<noteq> capPTBasePtr (capCap (cteCap vs_cap)))"
                            in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
                  apply (rule conseqPre, vcg)
                     apply (clarsimp simp: from_bool_eq_if' vspace_cap_capUntypedPtr_capPTBasePtr
                                           casid_map_relation_Some_get_tag
                                           casid_map_relation_Some_c_lift_eqs)
                    apply ceqv
                   apply (simp cong: call_ignore_cong)

                   (* C does two checks/aborts, but Haskell only one, so direct If-condition
                      equivalence doesn't match. Step over C side, resolve Haskell check using
                      resulting non-abort conditions. *)
                   apply (rule ccorres_Cond_rhs_Seq)
                    (* vspace in asid map entry doesn't match vspace cap *)
                    apply clarsimp
                    apply (rule ccorres_split_throws)
                     apply (rule ccorres_call_hSkip)
                       apply (rule slowpath_ccorres, simp+)
                    apply (vcg exspec=slowpath_noreturn_spec)
                   apply (simp cong: call_ignore_cong)
                   (* we can't directly relate getting stored_vmid_valid_CL to None/Some on the
                      Haskell side, but we can relate equating the result to 0 (i.e. no valid vmid) *)
                   apply csymbr
                   apply (simp cong: call_ignore_cong)
                   apply (rule_tac C'="{_. apVMID (the asid_map_entry_opt) = None}"
                                in ccorres_rewrite_cond_sr_Seq[where Q=\<top> and Q'=UNIV])
                    apply (clarsimp simp: casid_map_relation_Some_c_lift_eqs)
                   apply (rule ccorres_Cond_rhs_Seq)
                    (* no valid VMID *)
                    apply clarsimp
                    apply (rule ccorres_split_throws)
                     apply (rule ccorres_call_hSkip)
                       apply (rule slowpath_ccorres, simp+)
                    apply (vcg exspec=slowpath_noreturn_spec)
                   (* ap_entry/VMID check on Haskell side is now trivially true with clarsimp, but we
                      have to avoid exploding our free variables to avoid having to wrap them
                      back up during wp reasoning (e.g. \<exists>y. asid_map_entry_opt = Some y) *)
                   apply (simp cong: call_ignore_cong)
                   apply (rule ccorres_If_True_drop, solves clarsimp)

                   (* store VMID in first word of stored_hw_asid, which will be used later on the C side *)
                   apply (rule_tac xf'=ret__unsigned_longlong_'
                               and val="ucast (the (apVMID (the asid_map_entry_opt)))"
                                in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
                      apply (rule conseqPre, vcg)
                      apply (clarsimp simp: casid_map_relation_Some_get_tag
                                            casid_map_relation_Some_c_lift_eqs)
                     apply ceqv
                    apply (simp cong: call_ignore_cong)
                    apply csymbr

                    (* checking for highest priority *)
                    apply (rule ccorres_abstract_ksCurThread, ceqv)
                    apply (rule_tac P="ct = curThread" in ccorres_gen_asm, simp only:, thin_tac "ct = curThread")
                    apply (simp cong: call_ignore_cong if_cong)
                    apply (ctac add: getCurDomain_maxDom_ccorres_dom_')
                      apply (rename_tac curDom curDom')
                      apply (rule ccorres_move_c_guard_tcb ccorres_move_const_guard)+
                      apply (simp add: prio_and_dom_limit_helpers cong: call_ignore_cong)
                      apply (rule ccorres_pre_threadGet)
                      apply (rule ccorres_pre_threadGet)
                      apply (rename_tac curPrio destPrio)
                      (* use isHighestPrio on the left, but entire if condition on the right *)
                      apply (rule ccorres_rhs_assoc2)
                      (* we can do this with just knowledge from abstract and state relation,
                         which avoids some False schematic instantiation on the C side *)
                      apply (rule_tac xf'=ret__int_'
                                and r'="\<lambda>hi rv'. rv' = from_bool (\<not> (curPrio \<le> destPrio \<or> hi))"
                                and P'=UNIV in ccorres_split_nothrow)
                          apply (rule ccorres_guard_impR)
                           apply (simp add: from_bool_eq_if from_bool_eq_if' if_1_0_0
                                             ccorres_IF_True)
                           (* but as a result, we have to duplicate some info to the C side *)
                           apply (rule_tac P="obj_at' ((=) curPrio \<circ> tcbPriority) curThread
                                              and obj_at' ((=) destPrio \<circ> tcbPriority)
                                                          (hd (epQueue send_ep))
                                              and (\<lambda>s. ksCurThread s = curThread)"
                                           in ccorres_cross_over_guard)
                           apply (rule_tac xf'=ret__int_' and val="from_bool (destPrio < curPrio)"
                                     and R="obj_at' ((=) curPrio \<circ> tcbPriority) curThread
                                            and obj_at' ((=) destPrio \<circ> tcbPriority)
                                                        (hd (epQueue send_ep))
                                            and (\<lambda>s. ksCurThread s = curThread)"
                                     and R'=UNIV in ccorres_symb_exec_r_known_rv)
                              apply (rule conseqPre, vcg)
                              apply clarsimp
                              apply (simp add: from_bool_eq_if from_bool_eq_if' ccorres_IF_True)
                              apply (drule(1) obj_at_cslift_tcb)+
                              apply (clarsimp simp: typ_heap_simps' rf_sr_ksCurThread)
                              apply (simp add: ctcb_relation_unat_tcbPriority_C
                                                word_less_nat_alt linorder_not_le)
                             apply ceqv
                            apply (simp add: from_bool_eq_if from_bool_eq_if' ccorres_IF_True )

                            apply (rule ccorres_Cond_rhs)
                             apply (rule ccorres_Guard_Seq)
                             apply (rule ccorres_add_return2)
                             apply (ctac add: isHighestPrio_ccorres)
                               apply (simp add: from_bool_eq_if from_bool_eq_if' ccorres_IF_True )
                               apply (clarsimp simp: to_bool_def)
                               apply (rule_tac P=\<top> and P'=UNIV in ccorres_from_vcg)
                               apply clarsimp
                               apply (rule conseqPre, vcg)
                               apply (clarsimp simp: from_bool_eq_if' word_le_not_less)
                               apply (clarsimp simp: return_def)
                              apply (rule wp_post_taut)
                             apply (vcg exspec=isHighestPrio_modifies)
                            apply (rule_tac P=\<top> and P'="{s. ret__int_' s = 0}" in ccorres_from_vcg)
                            apply (clarsimp simp: isHighestPrio_def' simpler_gets_def)
                            apply (rule conseqPre, vcg)
                            apply clarsimp
                           apply clarsimp
                           apply vcg
                          apply (simp add: from_bool_eq_if from_bool_eq_if' ccorres_IF_True)
                          apply clarsimp
                          apply (drule(1) obj_at_cslift_tcb)+
                          apply (clarsimp simp: typ_heap_simps' rf_sr_ksCurThread)
                          apply (simp add: ctcb_relation_unat_tcbPriority_C ctcb_relation_tcbPriority
                                            word_less_nat_alt linorder_not_le)
                         apply ceqv
                        apply (simp cong: call_ignore_cong)
                        apply (rule ccorres_Cond_rhs_Seq)
                         apply (simp add: bindE_assoc catch_throwError )
                         apply (rule ccorres_split_throws)
                          apply (rule ccorres_call_hSkip)
                            apply (rule slowpath_ccorres, simp+)
                         apply (vcg exspec=slowpath_noreturn_spec)
                        apply (simp cong: call_ignore_cong)
                        apply (rule ccorres_rhs_assoc2)
                        apply (rule ccorres_rhs_assoc2)
                        apply (rule_tac val="from_bool (\<not> (capEPCanGrant (theRight luRet)
                                                            \<or> capEPCanGrantReply (theRight luRet)))"
                                             and xf'=ret__int_' and R=\<top> and R'=UNIV
                                        in ccorres_symb_exec_r_known_rv)
                           apply (clarsimp, rule conseqPre, vcg)
                           apply (fastforce simp: ccap_relation_ep_helpers from_bool_eq_if')
                          apply ceqv
                         apply (rule ccorres_Cond_rhs_Seq)
                          apply simp
                          apply (rule ccorres_split_throws)
                           apply (rule ccorres_call_hSkip)
                             apply (rule slowpath_ccorres, simp+)
                          apply (vcg exspec=slowpath_noreturn_spec)
                         (* Note: AArch32 has pde_pde_invalid_get_stored_asid_valid check here *)
                         apply (simp cong: call_ignore_cong)
                         apply (rule ccorres_move_c_guard_tcb ccorres_move_const_guard)+
                         apply (rule ccorres_pre_threadGet)
                         apply (rename_tac destDom)
                         (* The C does not compare domains when maxDomain is 0, since then both
                            threads will be in the current domain. Since we can show both threads
                            must be \<le> maxDomain, we can rewrite this test to only comparing domains
                            even when maxDomain is 0, making the check identical to the Haskell. *)
                         apply (rule_tac C'="{s. destDom \<noteq> curDom}"
                                   and Q="obj_at' ((=) destDom \<circ> tcbDomain) (hd (epQueue send_ep))
                                            and (\<lambda>s. ksCurDomain s = curDom \<and> curDom \<le> maxDomain
                                                     \<and> destDom \<le> maxDomain)"
                                   and Q'=UNIV in ccorres_rewrite_cond_sr_Seq)
                          apply (simp add: from_bool_eq_if from_bool_eq_if' ccorres_IF_True)
                          apply clarsimp
                          apply (drule(1) obj_at_cslift_tcb)+
                          apply (clarsimp simp: typ_heap_simps' rf_sr_ksCurDomain)
                          apply (drule ctcb_relation_tcbDomain[symmetric])
                          apply (case_tac "0 < maxDomain"
                                 ; solves \<open>clarsimp simp: maxDom_sgt_0_maxDomain not_less\<close>)
                         apply (rule ccorres_seq_cond_raise[THEN iffD2])
                         apply (rule_tac R=\<top> in ccorres_cond2', blast)
                          apply (rule ccorres_split_throws)
                           apply (rule ccorres_call_hSkip)
                             apply (rule slowpath_ccorres, simp+)
                          apply (vcg exspec=slowpath_noreturn_spec)
                         apply (simp cong: call_ignore_cong)

                         (* Now fully committed to fastpath *)
                         apply (rule ccorres_rhs_assoc2)
                         apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                             apply (simp only: ucast_id tl_drop_1 One_nat_def scast_0)
                             apply (rule fastpath_dequeue_ccorres)
                             apply simp
                            apply ceqv
                           apply csymbr
                           apply csymbr
                           apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                               apply (rule_tac P="cur_tcb' and (\<lambda>s. ksCurThread s = curThread)"
                                            in ccorres_from_vcg[where P'=UNIV])
                               apply (rule allI, rule conseqPre, vcg)
                               apply (clarsimp simp: cur_tcb'_def rf_sr_ksCurThread)
                               apply (drule(1) obj_at_cslift_tcb)
                               apply (clarsimp simp: typ_heap_simps')
                               apply (rule rev_bexI, erule threadSet_eq)
                               apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
                               apply (rule conjI)
                                apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                                      update_tcb_map_tos map_to_tcbs_upd)
                                apply (subst map_to_ctes_upd_tcb_no_ctes, assumption)
                                 apply (rule ball_tcb_cte_casesI, simp_all)[1]
                                apply (simp add: cep_relations_drop_fun_upd)
                                apply (erule cmap_relation_updI, erule ko_at_projectKO_opt)
                                 apply (simp add: ctcb_relation_def cthread_state_relation_def)
                                apply simp
                               apply (rule conjI, erule cready_queues_relation_not_queue_ptrs)
                                 apply (rule ext, simp split: if_split add: typ_heap_simps')
                                apply (rule ext, simp split: if_split add: typ_heap_simps')
                               apply (simp add: carch_state_relation_def cmachine_state_relation_def
                                                typ_heap_simps' map_comp_update projectKO_opt_tcb
                                                cvariable_relation_upd_const ko_at_projectKO_opt)
                              apply ceqv
                             apply (rule ccorres_abstract_ksCurThread, ceqv)
                             apply (rule ccorres_move_c_guard_tcb_ctes
                                         ccorres_move_array_assertion_tcb_ctes
                                         ccorres_move_const_guard)+
                             apply (simp add: getThreadReplySlot_def getThreadCallerSlot_def
                                              locateSlot_conv)
                             apply (rule ccorres_symb_exec_r)
                               apply (rule_tac xf'="replySlot_'" in ccorres_abstract, ceqv)
                               apply (rename_tac replySlot,
                                      rule_tac P="replySlot
                                                  = cte_Ptr (curThread
                                                             + (tcbReplySlot << cte_level_bits))"
                                               in ccorres_gen_asm2)
                               apply (rule ccorres_move_const_guard
                                           ccorres_move_array_assertion_tcb_ctes
                                           ccorres_move_c_guard_tcb_ctes)+
                               apply csymbr
                               apply (simp add: cteInsert_def bind_assoc)
                               apply (rule ccorres_pre_getCTE2, rename_tac curThreadReplyCTE)
                               apply (simp only: getThreadState_def)
                               apply (rule ccorres_assert2)
                               apply (rule ccorres_pre_threadGet, rename_tac destState)
                               apply (rule_tac P="isReceive destState" in ccorres_gen_asm)
                               apply (rule ccorres_pre_getCTE2, rename_tac curThreadReplyCTE2)
                               apply (rule ccorres_pre_getCTE2, rename_tac destCallerCTE)
                               apply (rule ccorres_assert2)+
                               apply (rule_tac xf'=ret__unsigned_longlong_'
                                        and val="from_bool (blockingIPCCanGrant destState)"
                                        and R="st_tcb_at' ((=) destState) (hd (epQueue send_ep))
                                               and K(isReceive destState)"
                                        and R'=UNIV in ccorres_symb_exec_r_known_rv)
                                  apply (clarsimp, rule conseqPre, vcg)
                                  apply (clarsimp simp: typ_heap_simps' st_tcb_at_h_t_valid
                                                        pred_tcb_at'_def)
                                  apply (drule (1) obj_at_cslift_tcb)
                                  apply clarsimp
                                  apply (drule ctcb_relation_blockingIPCCanGrantD, blast)
                                  apply fastforce
                                 apply ceqv
                                apply csymbr

                                apply (rule_tac P="curThreadReplyCTE2 = curThreadReplyCTE"
                                                in ccorres_gen_asm)
                                apply (rule ccorres_move_c_guard_tcb_ctes2)
                                apply (ctac add: cap_reply_cap_ptr_new_np_updateCap_ccorres)
                                  apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                                      apply (rule_tac P="cte_wp_at' (\<lambda>cte. cteMDBNode cte = nullMDBNode)
                                                           (hd (epQueue send_ep)
                                                                 + (tcbCallerSlot << cte_level_bits))
                                                     and cte_wp_at' ((=) curThreadReplyCTE) (curThread
                                                                 + (tcbReplySlot << cte_level_bits))
                                                     and tcb_at' curThread and (no_0 o ctes_of)
                                                     and tcb_at' (hd (epQueue send_ep))"
                                                   in ccorres_from_vcg[where P'=UNIV])
                                      apply (rule allI, rule conseqPre, vcg)
                                      apply (clarsimp simp: cte_wp_at_ctes_of size_of_def
                                                            tcb_cnode_index_defs tcbCallerSlot_def
                                                            tcbReplySlot_def cte_level_bits_def
                                                            valid_mdb'_def valid_mdb_ctes_def)
                                      apply (subst aligned_add_aligned, erule tcb_aligned',
                                             simp add: is_aligned_def, simp add: objBits_defs, simp)
                                      apply (rule_tac x="hd (epQueue send_ep) + v" for v
                                                   in cmap_relationE1[OF cmap_relation_cte], assumption+)
                                      apply (clarsimp simp: typ_heap_simps' updateMDB_def Let_def)
                                      apply (subst if_not_P)
                                       apply clarsimp
                                      apply (simp add: split_def)
                                      apply (rule getCTE_setCTE_rf_sr, simp_all)[1]
                                      apply (case_tac destCallerCTE, case_tac curThreadReplyCTE,
                                             case_tac "cteMDBNode curThreadReplyCTE")
                                      apply (clarsimp simp: ccte_relation_eq_ccap_relation nullMDBNode_def)
                                     apply ceqv
                                    apply (rule ccorres_move_c_guard_cte)
                                    apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                                        apply (rule_tac P="pspace_canonical'
                                                           and cte_at' (hd (epQueue send_ep)
                                                                        + (tcbCallerSlot << cte_level_bits))
                                                           and cte_wp_at' ((=) curThreadReplyCTE) (curThread
                                                                     + (tcbReplySlot << cte_level_bits))
                                                           and tcb_at' (hd (epQueue send_ep))
                                                           and (no_0 o ctes_of)"
                                                      in ccorres_from_vcg[where P'=UNIV])
                                        apply (rule allI, rule conseqPre, vcg)
                                        apply (clarsimp simp: cte_wp_at_ctes_of size_of_def
                                                              tcb_cnode_index_defs tcbCallerSlot_def
                                                              tcbReplySlot_def cte_level_bits_def
                                                              ctes_of_canonical)
                                        apply (subst aligned_add_aligned, erule tcb_aligned',
                                               simp add: is_aligned_def, simp add: objBits_defs, simp)
                                        apply (rule_tac x="curThread + 0x40" in cmap_relationE1[OF cmap_relation_cte],
                                               assumption+)
                                        apply (clarsimp simp: typ_heap_simps' updateMDB_def Let_def)
                                        apply (subst if_not_P)
                                         apply clarsimp
                                        apply (simp add: split_def)
                                        apply (rule getCTE_setCTE_rf_sr, simp_all)[1]
                                        apply (simp add: ccte_relation_eq_ccap_relation)
                                        apply (case_tac curThreadReplyCTE,
                                               case_tac "cteMDBNode curThreadReplyCTE",
                                               simp)
                                       apply ceqv
                                      apply (simp add: updateMDB_def)
                                      apply (rule ccorres_split_nothrow_dc)
                                         apply (ctac add: fastpath_copy_mrs_ccorres[unfolded forM_x_def])
                                        apply (rule ccorres_move_c_guard_tcb)
                                        apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                                            apply (simp add: setThreadState_runnable_simp)
                                            apply (rule_tac P=\<top> in threadSet_ccorres_lemma2, vcg)
                                            apply (clarsimp simp: typ_heap_simps' rf_sr_def
                                                                  cstate_relation_def Let_def)
                                            apply (rule conjI)
                                            apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                                                  update_tcb_map_tos map_to_tcbs_upd)
                                            apply (subst map_to_ctes_upd_tcb_no_ctes, assumption)
                                            apply (rule ball_tcb_cte_casesI, simp_all)[1]
                                            apply (simp add: cep_relations_drop_fun_upd)
                                            apply (erule cmap_relation_updI, erule ko_at_projectKO_opt)
                                            apply (simp add: ctcb_relation_def cthread_state_relation_def)
                                            apply simp
                                            apply (rule conjI, erule cready_queues_relation_not_queue_ptrs)
                                            apply (rule ext, simp split: if_split)
                                            apply (rule ext, simp split: if_split)
                                            apply (simp add: carch_state_relation_def cmachine_state_relation_def
                                                             typ_heap_simps' map_comp_update projectKO_opt_tcb
                                                             cvariable_relation_upd_const ko_at_projectKO_opt)
                                           apply ceqv
                                          apply (simp only: bind_assoc[symmetric])
                                          apply (rule ccorres_stateAssert_after)
                                          apply (rule ccorres_split_nothrow_novcg_dc)
                                            apply simp
                                            apply (rule ccorres_call,
                                                   rule_tac vmid="ucast (the (apVMID (the asid_map_entry_opt)))"
                                                        and vsroot="capUntypedPtr (cteCap vs_cap)"
                                                        and asid="fst (the (capPTMappedAddress (capCap (cteCap vs_cap))))"
                                                         in switchToThread_fp_ccorres,
                                                   simp+)[1]
                                            apply (rule_tac P="\<lambda>s. ksCurThread s = hd (epQueue send_ep)"
                                                         in ccorres_cross_over_guard)
                                            apply csymbr
                                            apply csymbr
                                            apply (rule ccorres_call_hSkip)
                                              apply (rule fastpath_restore_ccorres)
                                             apply simp
                                            apply simp
                                           apply (simp add: setCurThread_def)
                                           apply wp
                                            apply (rule_tac P=\<top> in hoare_triv, simp)
                                           apply simp
                                          apply (simp add: imp_conjL rf_sr_ksCurThread)
                                          apply (clarsimp simp: signed_n_msgRegisters_to_H
                                                                messageInfoFromWord_def Let_def
                                                                mi_from_H_def
                                                                seL4_MessageInfo_lift_def
                                                                msgLengthBits_def msgExtraCapBits_def
                                                                msgMaxExtraCaps_def shiftL_nat
                                                                mask_def msgLabelBits_def
                                                                guard_is_UNIV_def)
                                          apply (force simp: size_msgRegisters_def msgMaxLength_def
                                                             ccap_relation_ep_helpers
                                                       split: if_splits)
                                         apply (wp sts_valid_objs' asid_has_vmid_lift)
                                        apply simp
                                        apply (vcg exspec=thread_state_ptr_set_tsType_np_modifies)
                                       apply (simp add: pred_conj_def)
                                       apply (rule mapM_x_wp'[OF hoare_weaken_pre])
                                        apply (wp asid_has_vmid_lift)
                                       apply clarsimp
                                      apply simp
                                      apply (vcg exspec=fastpath_copy_mrs_modifies)
                                     apply (simp add: valid_tcb_state'_def)
                                     apply wp
                                     apply (wp updateMDB_weak_cte_wp_at asid_has_vmid_lift)
                                    apply simp
                                    apply (vcg exspec=mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged_modifies)
                                   apply simp
                                   apply (wp asid_has_vmid_lift | simp
                                          | wp (once) updateMDB_weak_cte_wp_at
                                          | wp (once) updateMDB_cte_wp_at_other)+
                                  apply (vcg exspec=mdb_node_ptr_set_mdbPrev_np_modifies)
                                 apply (wp updateCap_cte_wp_at_cteMDBNode
                                           updateCap_cte_wp_at_cases
                                           updateCap_no_0 asid_has_vmid_lift | simp)+
                                apply (vcg exspec=cap_reply_cap_ptr_new_np_modifies)
                               (* imp_disjL causes duplication of conclusions of implications involving
                                  disjunctions which chokes the vcg; we want fewer implications at the
                                  expense of disjunctions on asm side *)
                               supply imp_disjL[simp del]
                               supply imp_disjL[symmetric, simp]
                               apply clarsimp
                               apply (vcg exspec=thread_state_ptr_get_blockingIPCCanGrant_modifies)
                              apply (simp add: word_sle_def)
                              apply vcg

                             apply (rule conseqPre, vcg, clarsimp)
                            apply (simp add: cte_level_bits_def field_simps shiftl_t2n
                                             ctes_of_Some_cte_wp_at
                                        del: all_imp_to_ex cong: imp_cong conj_cong)
                            apply (wp hoare_vcg_all_lift threadSet_ctes_of
                                      hoare_vcg_imp_lift' threadSet_valid_objs'
                                      threadSet_st_tcb_at_state threadSet_cte_wp_at'
                                      threadSet_cur asid_has_vmid_lift
                                    | simp add: cur_tcb'_def[symmetric]
                                    | strengthen not_obj_at'_strengthen)+
                           apply (vcg exspec=thread_state_ptr_set_tsType_np_modifies)
                          apply (wp hoare_vcg_all_lift threadSet_ctes_of
                                    hoare_vcg_imp_lift' threadSet_valid_objs'
                                    threadSet_st_tcb_at_state threadSet_cte_wp_at'
                                    threadSet_cur
                                  | simp add: cur_tcb'_def[symmetric])+
                            apply (simp add: valid_tcb'_def tcb_cte_cases_def
                                             valid_tcb_state'_def cteSizeBits_def)
                            apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift
                                      set_ep_valid_objs' asid_has_vmid_lift
                                      setObject_no_0_obj'[where 'a=endpoint, folded setEndpoint_def]
                                   | strengthen not_obj_at'_strengthen)+
                             apply (rule_tac Q="\<lambda>_ s. hd (epQueue send_ep) \<noteq> curThread
                                                      \<and> pred_tcb_at' itcbState ((=) (tcbState xa)) (hd (epQueue send_ep)) s"
                                          in hoare_post_imp)
                              apply fastforce
                             apply wp+
                         apply simp
                         apply (vcg exspec=endpoint_ptr_mset_epQueue_tail_state_modifies
                                  exspec=endpoint_ptr_set_epQueue_head_np_modifies)
                        apply simp
                        apply (vcg exspec=cap_endpoint_cap_get_capCanGrant_modifies
                                   exspec=cap_endpoint_cap_get_capCanGrantReply_modifies)
                       apply simp
                       (* throw away results of isHighestPrio and the fastfail shortcut *)
                       apply (wp (once) hoare_drop_imp, wp)
                       apply (wp (once) hoare_drop_imp, wp)

(* FIXME AARCH64 this is frustrating:
   - can't use clarsimp because it'll introduce new free variables (\<exists>_. _ = Some _) that will
     cause schematic unification problems
   - for this same reason, can't use wpsimp
   So we are restricted to simp. But:
   - if there are any unification problems, wp will generate a goal that has a schematic assumption
   - the next simp will immediately instantiate that assumption to False
   - vcg will happily do the same thing as wp if there's a unification problem, but *also* has a
     built-in simp so we won't immediately see anything went wrong.
   This results in using rule rather than wp in several cases below, but the proof still remains
   fragile and very difficult to get right. *)
                      apply simp
                      apply (vcg exspec=isHighestPrio_modifies)
                     apply simp
                     apply (rule cd_wp)
                    apply simp
                    apply vcg
                   apply simp
                   apply vcg
                  apply simp
                  apply wpfix
                  apply vcg
                 apply simp
                 apply (rule getASIDPoolEntry_wp)
                apply simp
                apply (vcg exspec=findMapForASID_modifies)
               apply simp
               apply (vcg exspec=cap_vspace_cap_get_capVSMappedASID_modifies)
              apply simp
              (* accessing VSBasePtr without knowing it's a VSpace, can't use default spec *)
              apply (rule conseqPre, vcg exspec=cap_vspace_cap_get_capVSBasePtr_spec2)
              apply (rule subset_refl)
             apply (rule conseqPre, vcg exspec=cap_vspace_cap_get_capVSBasePtr_spec2)
             apply clarsimp
            apply clarsimp
            apply (rule getEndpoint_wp)
           apply simp
           apply (vcg exspec=endpoint_ptr_get_epQueue_head_modifies
                      exspec=endpoint_ptr_get_state_modifies)
          apply (simp add: getSlotCap_def)
          apply (rule valid_isLeft_theRight_split)
          apply simp
          apply (wp getCTE_wp')
          apply (rule validE_R_abstract_rv)
          apply wp
         apply simp
         apply (vcg exspec=lookup_fp_modifies)
        apply simp
        apply (rule threadGet_wp)
       apply clarsimp
       apply vcg
      apply simp
      apply (rule user_getreg_wp)
     apply simp
     apply (rule user_getreg_wp)

    apply (rule conjI)
     (* Haskell precondition *)
     apply (clarsimp simp: obj_at_tcbs_of ct_in_state'_def st_tcb_at_tcbs_of
                           invs_cur' invs_valid_objs' ctes_of_valid'
                           word_sle_def
                           tcb_ptr_to_ctcb_ptr_mask[OF tcb_at_invs']
                           invs'_bitmapQ_no_L1_orphans)
     apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp)
     apply (clarsimp simp: isCap_simps valid_cap'_def maskCapRights_def)
     apply (clarsimp simp add: obj_at'_def) (* FIXME AARCH64 not a fan of obj_at' expansion *)
     apply (frule invs_valid_objs')
     apply (erule valid_objsE')
      apply simp
     apply (clarsimp simp: isRecvEP_def valid_obj'_def valid_ep'_def
                     split: Structures_H.endpoint.split_asm)
     apply (erule not_NilE)

     (* sort out destination being queued in the endpoint, hence not the current thread *)
     apply (prop_tac "st_tcb_at' isBlockedOnReceive x s")
      apply (rule_tac ts="x # xs'" and epptr=v0 in recv_ep_queued_st_tcb_at'
             ; clarsimp simp: obj_at'_def  invs_sym')
     apply (prop_tac "x \<noteq> ksCurThread s")
      apply (fastforce simp: st_tcb_at_tcbs_of isBlockedOnReceive_def)
     apply (drule_tac x = x in bspec)
      apply fastforce
     apply (clarsimp simp:obj_at_tcbs_of)
     apply (frule_tac ptr2 = x in tcbs_of_aligned')
      apply (simp add:invs_pspace_aligned')
     apply (frule_tac ptr2 = x in tcbs_of_cte_wp_at_vtable)
     apply (clarsimp simp: size_of_def field_simps word_sless_def word_sle_def
                     dest!: ptr_val_tcb_ptr_mask2[unfolded mask_def])
     apply (frule_tac p="x + offs" for offs in ctes_of_valid', clarsimp)
     apply (rule conjI, fastforce) (* valid_arch_state' *)
     apply (rule conjI) (* asid_wf *)
      apply (clarsimp simp: isCap_simps valid_cap'_def
                     dest!: isValidVTableRootD)
      apply (clarsimp simp: wellformed_mapdata'_def)
     apply (clarsimp simp: invs_sym' tcbCallerSlot_def
                           tcbVTableSlot_def tcbReplySlot_def
                           conj_comms tcb_cnode_index_defs field_simps
                           obj_at_tcbs_of)
     apply (clarsimp simp: cte_level_bits_def isValidVTableRoot_def
                           cte_wp_at_ctes_of capAligned_def objBits_simps)
     apply (simp cong: conj_cong)
     apply (clarsimp simp add: invs_ksCurDomain_maxDomain')
     apply (rule conjI)
    subgoal (* dest thread domain \<le> maxDomain *)
      by (drule (1) tcbs_of_valid_tcb'[OF invs_valid_objs'], solves \<open>clarsimp simp: valid_tcb'_def\<close>)
     apply clarsimp
     apply (rule conjI) (* isReceive on queued tcb state *)
      apply (fastforce simp: st_tcb_at_tcbs_of isBlockedOnReceive_def isReceive_def)
     apply clarsimp
     apply (rule conjI, solves clarsimp)+ (* a bunch of consequences of invs' *)
     apply (frule invs_mdb', clarsimp simp: valid_mdb'_def valid_mdb_ctes_def)
     apply (case_tac xb, clarsimp, drule(1) nullcapsD')
     apply (clarsimp simp: to_bool_def length_msgRegisters word_le_nat_alt[symmetric])
     apply (frule tcb_aligned'[OF obj_at_tcbs_of[THEN iffD2], OF exI, simplified])
     apply (clarsimp simp: objBits_defs signed_n_msgRegisters_to_H)
     apply (rule conjI, clarsimp simp: word_bits_def)
     apply (prop_tac "capPTBasePtr (capCap (cteCap cteb)) = global.capUntypedPtr (cteCap cteb)")
      apply (solves \<open>clarsimp simp add: isVTableRoot_ex\<close>)
     apply simp
   apply (rule conjI)
    apply (clarsimp simp: asid_has_vmid_def asid_has_entry_def split: option.splits)
    apply (rule_tac x=pool in exI)
    apply clarsimp
    apply (case_tac asid_entry, clarsimp)

     apply (safe del: notI disjE)[1]
       apply (rule not_sym, clarsimp)
       apply (drule Aligned.aligned_sub_aligned[where x="x + 0x20" and y=x for x])
         apply (erule tcbs_of_aligned')
         apply (simp add:invs_pspace_aligned')
        apply (simp add: objBits_defs)
       apply (simp add: objBits_defs is_aligned_def dvd_def)
      apply (clarsimp simp: tcbs_of_def obj_at'_def projectKO_opt_tcb
                      split: if_splits Structures_H.kernel_object.splits) (* slow *)
      apply (drule pspace_distinctD')
       apply (simp add: invs_pspace_distinct')
      apply (simp add: objBits_simps)

     apply (clarsimp simp: obj_at_tcbs_of split: list.split)
     apply (erule_tac x = v0 in valid_objsE'[OF invs_valid_objs',rotated])
      apply (clarsimp simp: valid_obj'_def valid_ep'_def isRecvEP_def neq_Nil_conv size_of_def
                      split: Structures_H.endpoint.split_asm
                      cong: list.case_cong)
      apply (simp add: obj_at_tcbs_of)
     apply simp

    (* C precondition *)
    apply (clarsimp simp: syscall_from_H_def[split_simps syscall.split]
                          word_sle_def word_sless_def rf_sr_ksCurThread
                          size_of_def cte_level_bits_def
                          tcb_cnode_index_defs tcbCTableSlot_def tcbVTableSlot_def
                          tcbReplySlot_def tcbCallerSlot_def)
    apply (drule (1) obj_at_cslift_tcb)
    apply (clarsimp simp: ccte_relation_eq_ccap_relation of_bl_from_bool
                          ccap_relation_case_sum_Null_endpoint from_bool_eq_if'
                          isRight_case_sum typ_heap_simps')
    apply (frule (1) cap_get_tag_isCap[THEN iffD2])
    apply (clarsimp simp: typ_heap_simps' ccap_relation_ep_helpers)
    apply (erule cmap_relationE1[OF cmap_relation_ep],
           erule ko_at_projectKO_opt)
    apply (frule (1) ko_at_valid_ep')
    apply (clarsimp simp: cendpoint_relation_def Let_def
                          isRecvEP_endpoint_case neq_Nil_conv
                          tcb_queue_relation'_def valid_ep'_def
                          mi_from_H_def)
    apply (rule conjI; clarsimp?)
     apply (rule conjI; clarsimp simp: casid_map_relation_Some_get_tag)
    (* cap_get_tag_isCap hides info obtained from isValidVTableRootD' *)
    apply (frule (1) capVSBasePtr_CL_capUntypedPtr_helper)
    apply (clarsimp simp: cap_get_tag_isCap dest!: isValidVTableRootD')
   done
qed

lemma ccap_relation_reply_helper:
  "\<lbrakk> ccap_relation cap cap'; isReplyCap cap \<rbrakk>
     \<Longrightarrow> cap_reply_cap_CL.capTCBPtr_CL (cap_reply_cap_lift cap')
           = ptr_val (tcb_ptr_to_ctcb_ptr (capTCBPtr cap))"
  by (clarsimp simp: cap_get_tag_isCap[symmetric]
                     cap_lift_reply_cap cap_to_H_simps
                     cap_reply_cap_lift_def
              elim!: ccap_relationE)

lemma valid_ep_typ_at_lift':
  "\<lbrakk> \<And>p. \<lbrace>typ_at' TCBT p\<rbrace> f \<lbrace>\<lambda>rv. typ_at' TCBT p\<rbrace> \<rbrakk>
      \<Longrightarrow> \<lbrace>\<lambda>s. valid_ep' ep s\<rbrace> f \<lbrace>\<lambda>rv s. valid_ep' ep s\<rbrace>"
  apply (cases ep, simp_all add: valid_ep'_def)
   apply (wp hoare_vcg_const_Ball_lift typ_at_lifts | assumption)+
  done

lemma threadSet_tcbState_valid_objs:
  "\<lbrace>valid_tcb_state' st and valid_objs'\<rbrace>
     threadSet (tcbState_update (\<lambda>_. st)) t
   \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
  apply (wp threadSet_valid_objs')
  apply (clarsimp simp: valid_tcb'_def tcb_cte_cases_def cteSizeBits_def)
  done

lemmas array_assertion_abs_tcb_ctes_add
    = array_assertion_abs_tcb_ctes_add[where
          tcb="\<lambda>s. Ptr (tcb' s)" for tcb', simplified]

lemmas ccorres_move_array_assertion_tcb_ctes [ccorres_pre]
    = ccorres_move_array_assertions [OF array_assertion_abs_tcb_ctes(1)[where
          tcb="\<lambda>s. Ptr (tcb' s)" for tcb', simplified]]
      ccorres_move_array_assertions [OF array_assertion_abs_tcb_ctes(2)]
      ccorres_move_Guard_Seq[OF array_assertion_abs_tcb_ctes_add]
      ccorres_move_Guard[OF array_assertion_abs_tcb_ctes_add]

lemmas ccorres_move_c_guard_tcb_ctes3
    = ccorres_move_c_guards  [OF c_guard_abs_tcb_ctes[where
          tcb="\<lambda>s. Ptr (tcb' s)" for tcb', simplified],
       unfolded cte_C_numeral_fold]

lemma fastpath_reply_cap_check_ccorres:
  "ccorres (\<lambda>rv rv'. \<forall>cap. ccap_relation cap ccap
                           \<longrightarrow> rv' = from_bool (isReplyCap cap))
      ret__int_'
      \<top> (\<lbrace> \<acute>cap = ccap \<rbrace>) hs
      (return ()) (Call fastpath_reply_cap_check_'proc)"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: from_bool_def return_def of_bl_from_bool cap_get_tag_isCap)
  done

lemma fastpath_reply_recv_ccorres:
  notes hoare_TrueI[simp] if_cong[cong] option.case_cong[cong]
  notes from_bool_0[simp] (* FIXME AARCH64 should go in simpset *)
  shows "ccorres dc xfdc
       (\<lambda>s. invs' s \<and> ct_in_state' ((=) Running) s
            \<and> obj_at' (\<lambda>tcb.  (user_regs o atcbContextGet o tcbArch) tcb capRegister = cptr
                              \<and>  (user_regs o atcbContextGet o tcbArch) tcb msgInfoRegister = msginfo)
                      (ksCurThread s) s)
       ({s. cptr_' s = cptr} \<inter> {s. msgInfo_' s = msginfo}) []
       (fastpaths SysReplyRecv) (Call fastpath_reply_recv_'proc)"
proof -
  have [simp]: "Kernel_C.tcbCaller = scast tcbCallerSlot"
    by (simp add:Kernel_C.tcbCaller_def tcbCallerSlot_def)
  have [simp]: "Kernel_C.tcbVTable = scast tcbVTableSlot"
    by (simp add:Kernel_C.tcbVTable_def tcbVTableSlot_def)

  have tcbs_of_cte_wp_at_vtable:
    "\<And>s tcb ptr. tcbs_of s ptr = Some tcb \<Longrightarrow> cte_wp_at' \<top> (ptr + 0x20 * tcbVTableSlot) s"
    apply (clarsimp simp: tcbs_of_def cte_at'_obj_at'
                    split: if_splits)
    apply (drule_tac x = "0x20 * tcbVTableSlot" in bspec)
     apply (simp add: tcb_cte_cases_def tcbVTableSlot_def cteSizeBits_def)
    apply simp
    done

  have tcbs_of_cte_wp_at_caller:
    "\<And>s tcb ptr. tcbs_of s ptr = Some tcb \<Longrightarrow> cte_wp_at' \<top> (ptr + 0x20 * tcbCallerSlot) s"
    apply (clarsimp simp: tcbs_of_def cte_at'_obj_at'
                    split: if_splits)
    apply (drule_tac x = "0x20 * tcbCallerSlot" in bspec)
     apply (simp add:tcb_cte_cases_def tcbCallerSlot_def cteSizeBits_def)
    apply simp
    done

  have tcbs_of_aligned':
    "\<And>s ptr tcb. \<lbrakk>tcbs_of s ptr = Some tcb; pspace_aligned' s\<rbrakk> \<Longrightarrow> is_aligned ptr tcbBlockSizeBits"
    apply (clarsimp simp: tcbs_of_def obj_at'_def split: if_splits)
    apply (drule pspace_alignedD')
    apply simp+
    apply (simp add: projectKO_opt_tcb objBitsKO_def
                split: Structures_H.kernel_object.splits)
    done

  (* FIXME indentation is wonky in this proof, fix will come in a future patch, hopefully when
     automatic indentation is improved *)
  show ?thesis
    supply option.case_cong_weak[cong del]
    supply if_cong[cong] option.case_cong[cong] Collect_const[simp del]

  apply (cinit lift: cptr_' msgInfo_')

     (* this also lifts out pickFastpath alternative to general alternative, but not clear what
        pickFastpath is for  *)
     apply (simp add: catch_liftE_bindE unlessE_throw_catch_If
                      unifyFailure_catch_If catch_liftE
                      getMessageInfo_def alternative_bind
                cong: if_cong call_ignore_cong)
     apply (rule ccorres_pre_getCurThread)
     apply (rename_tac curThread)
     apply (rule ccorres_symb_exec_l3[OF _ user_getreg_inv' _ empty_fail_user_getreg])+
       apply (rename_tac msginfo' cptr')
       apply (rule_tac P="msginfo' = msginfo \<and> cptr' = cptr" in ccorres_gen_asm)
       (* the call_ignore_cong in this proof is required to prevent corruption of arguments in
          endpoint_ptr_mset_epQueue_tail_state_'proc so that eventually fastpath_enqueue_ccorres
          can apply *)
       apply (simp cong: call_ignore_cong)
       apply (simp only:)
       apply (csymbr, csymbr)
       (* get fault type *)
       apply csymbr
       apply (rule_tac r'="\<lambda>ft ft'. (ft' = scast seL4_Fault_NullFault) = (ft = None)" and
                       xf'=ret__unsigned_longlong_' in ccorres_split_nothrow)
           apply (rule_tac P="cur_tcb' and (\<lambda>s. curThread = ksCurThread s)"
                           in ccorres_from_vcg[where P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: cur_tcb'_def rf_sr_ksCurThread)
           apply (drule(1) obj_at_cslift_tcb, clarsimp)
           apply (clarsimp simp: typ_heap_simps' ctcb_relation_def cfault_rel_def)
           apply (rule rev_bexI, erule threadGet_eq)
           apply (clarsimp simp: seL4_Fault_lift_def Let_def split: if_split_asm)
          apply ceqv
         apply (rename_tac fault fault')
         apply (rule ccorres_alternative1) (* pick pickFastpath = True, still not clear what it's for *)
         apply csymbr
         apply csymbr
         apply (simp cong: call_ignore_cong)
         apply (rule ccorres_if_cond_throws2[where Q=\<top> and Q'=\<top>, rotated -1])
            (* fault, message info overflows registers, or extra caps present: abort *)
            apply (vcg exspec=slowpath_noreturn_spec)
           apply (clarsimp simp: signed_n_msgRegisters_to_H messageInfoFromWord_def Let_def mi_from_H_def
                                 seL4_MessageInfo_lift_def msgLengthBits_def msgExtraCapBits_def
                                 msgMaxExtraCaps_def shiftL_nat mask_def msgLabelBits_def)
           apply (fastforce simp: size_msgRegisters_def msgMaxLength_def split: if_splits)
          apply (rule ccorres_call_hSkip)
            apply (rule slowpath_ccorres)
           apply simp
          apply simp

         apply (simp cong: call_ignore_cong)
         apply (elim conjE)
         (* look up invoked cap *)
         apply (rule ccorres_abstract_ksCurThread, ceqv)
         apply (rule_tac P="ct = curThread" in ccorres_gen_asm, simp only:, thin_tac "ct = curThread")
         apply (simp add: getThreadCSpaceRoot_def locateSlot_conv cong: call_ignore_cong)
         apply (rule ccorres_pre_getCTE2)
         apply (rule ccorres_move_array_assertion_tcb_ctes
                     ccorres_move_c_guard_tcb_ctes2
                     ccorres_move_const_guard
                     ccorres_rhs_assoc)+
         apply (ctac add: lookup_fp_ccorres)
           apply (rename_tac luRet ep_cap)
           apply (rule ccorres_abstract_ksCurThread, ceqv)
           apply (rule_tac P="ct = curThread" in ccorres_gen_asm, simp only:, thin_tac "ct = curThread")
           apply (rule ccorres_move_array_assertion_tcb_ctes | simp cong: call_ignore_cong)+
           (* check invoked cap *)
           apply (csymbr, csymbr)
           apply (simp add: ccap_relation_case_sum_Null_endpoint of_bl_from_bool cong: call_ignore_cong)
           apply (rule ccorres_Cond_rhs_Seq)
            (* not an endpoint cap *)
            apply (simp cong: if_cong)
            apply (rule ccorres_cond_true_seq)
            apply (rule ccorres_split_throws)
             apply (rule ccorres_call_hSkip)
               apply (erule disjE; simp; rule slowpath_ccorres)
              apply simp
             apply simp
            apply (vcg exspec=slowpath_noreturn_spec)
           apply (rule ccorres_rhs_assoc)+
           apply csymbr+
           apply (simp add: isRight_case_sum cong: call_ignore_cong)
           apply (elim conjE)
           apply (frule (1) cap_get_tag_isCap[THEN iffD2])
           apply (simp add: ccap_relation_ep_helpers cong: call_ignore_cong)
           apply (rule ccorres_Cond_rhs_Seq)
            (* can't receive from ep *)
            apply simp
            apply (rule ccorres_split_throws)
             apply (rule ccorres_call_hSkip)
               apply (rule slowpath_ccorres, simp+)
            apply (vcg exspec=slowpath_noreturn_spec)
           apply (simp cong: call_ignore_cong)
           (* check there is nothing waiting on the notification *)
           apply (rule ccorres_pre_getBoundNotification)
           apply (rule ccorres_rhs_assoc2)
           apply (rule_tac xf'=ret__int_' and r'="\<lambda>rv rv'. rv' = from_bool rv"
                        in ccorres_split_nothrow)
               apply (rule_tac P="bound_tcb_at' ((=) bound_ntfn) curThread and valid_objs'
                                  and no_0_obj' and (\<lambda>s. curThread = ksCurThread s)"
                            in ccorres_from_vcg[where P'=UNIV])
               apply (rule allI, rule conseqPre, vcg)
               apply (clarsimp simp: rf_sr_ksCurThread pred_tcb_at'_def)
               apply (drule(3) obj_at_bound_tcb_grandD, clarsimp simp: typ_heap_simps return_def)
               apply (simp add: in_liftM Bex_def getNotification_def getObject_return objBits_simps'
                                return_def cnotification_relation_isActive
                                trans [OF eq_commute from_bool_eq_if])
              apply ceqv
             apply (simp only:)
             apply (rule ccorres_Cond_rhs_Seq)
              apply (rule ccorres_split_throws)
               apply simp
               apply (rule ccorres_call_hSkip)
                 apply (rule slowpath_ccorres, simp+)
              apply (vcg exspec=slowpath_noreturn_spec)
             apply (simp cong: call_ignore_cong)
             (* get the endpoint address *)
             apply (csymbr, csymbr)
             apply (simp add: ccap_relation_ep_helpers cong: call_ignore_cong)
             (* consolidate enpoint state \<noteq> EPState_Send check on C side with result of getEndpoint *)
             apply (rule_tac xf'="ret__unsigned_longlong_'"
                         and r'="\<lambda>ep v. (v = scast EPState_Send) = isSendEP ep"
                          in ccorres_split_nothrow)
                 apply (rule ccorres_add_return2)
                 apply (rule ccorres_pre_getEndpoint, rename_tac ep)
                 apply (rule_tac P="ko_at' ep (capEPPtr (theRight luRet)) and valid_objs'"
                              in ccorres_from_vcg[where P'=UNIV])
                 apply (rule allI, rule conseqPre, vcg)
                 apply (clarsimp simp: return_def)
                 apply (erule cmap_relationE1[OF cmap_relation_ep], erule ko_at_projectKO_opt)
                 apply (clarsimp simp: typ_heap_simps')
                 apply (simp add: cendpoint_relation_def Let_def isSendEP_def endpoint_state_defs
                             split: endpoint.split_asm)
                apply ceqv
               apply (rename_tac send_ep send_ep_is_send)
               apply (rule_tac P="ko_at' send_ep (capEPPtr (theRight luRet)) and valid_objs'"
                            in ccorres_cross_over_guard)
               apply (simp cong: call_ignore_cong)
               apply (rule ccorres_Cond_rhs_Seq)
                (* endpoint has a thread waiting to send *)
                apply simp
                apply (rule ccorres_split_throws)
                 apply (rule ccorres_call_hSkip)
                   apply (rule slowpath_ccorres, simp+)
                apply (vcg exspec=slowpath_noreturn_spec)
               apply (simp cong: call_ignore_cong)

               (* get caller slot of current thread *)
               apply (simp add: locateSlot_conv getThreadCallerSlot_def
                           cong: if_cong call_ignore_cong)
               apply (rule ccorres_abstract_ksCurThread, ceqv)
               apply (rule_tac P="ct = curThread" in ccorres_gen_asm, simp only:, thin_tac "ct = curThread")
               apply (rule ccorres_move_const_guard
                           ccorres_move_c_guard_tcb_ctes2
                           ccorres_move_array_assertion_tcb_ctes)+
               apply csymbr
               (* get caller cap *)
               apply (rule ccorres_move_c_guard_cte)
               apply (rule_tac var="callerCap_'" and var_update="callerCap_'_update"
                            in getCTE_h_val_ccorres_split[where P=\<top>])
                 apply simp
                apply ceqv
               apply (rename_tac caller_cap caller_cap')
               apply (rule_tac P="\<lambda>_. capAligned (cteCap caller_cap)"
                            in ccorres_cross_over_guard)
               (* check caller cap is reply cap *)
               apply (rule ccorres_add_return, ctac add: fastpath_reply_cap_check_ccorres)
                 apply (drule spec, drule_tac P="ccap_relation cp caller_cap'" for cp in mp, assumption)
               apply (simp cong: call_ignore_cong)
                 apply (rule ccorres_Cond_rhs_Seq)
                  (* not reply cap *)
                  apply (simp cong: conj_cong)
                  apply (rule ccorres_split_throws)
                   apply (rule ccorres_call_hSkip)
                     apply (rule slowpath_ccorres, simp+)
                  apply (vcg exspec=slowpath_noreturn_spec)
                 apply (simp cong: call_ignore_cong)
                 (* get caller from cap on C side *)
                 apply (csymbr, csymbr)
                 apply (rename_tac caller')
                 (* get caller fault, reducing relation to whether there is no fault
                    Note: CONFIG_EXCEPTION_FASTPATH is not set, otherwise we'd need to deal with
                          generating fault replies for other fault types (currently only VM faults) *)
                 apply (rule ccorres_rhs_assoc2)
                 apply (rule_tac r'="\<lambda>ft ft'. (ft' = scast seL4_Fault_NullFault) = (ft = None)"
                          and xf'=fault_type_' in ccorres_split_nothrow)
                     apply (rule threadGet_vcg_corres)
                     apply (rule allI, rule conseqPre, vcg)
                     apply (clarsimp simp: obj_at_tcbs_of)
                     apply (clarsimp simp: typ_heap_simps' ctcb_relation_def cfault_rel_def
                                           ccap_relation_reply_helper)
                     apply (clarsimp simp: seL4_Fault_lift_def Let_def split: if_split_asm)
                    apply ceqv
                   apply (rename_tac fault fault')
                   apply (simp cong: call_ignore_cong)
                   apply (rule ccorres_Cond_rhs_Seq)
                    (* caller has faulted *)
                    apply (simp flip: not_None_eq)
                    apply (rule ccorres_split_throws)
                     apply (rule ccorres_call_hSkip)
                       apply (rule slowpath_ccorres, simp+)
                    apply (vcg exspec=slowpath_noreturn_spec)
                   apply (simp cong: call_ignore_cong)

                   (* get vspace root *)
                   apply (simp add: getThreadVSpaceRoot_def locateSlot_conv cong: call_ignore_cong)
                   apply (rule ccorres_move_c_guard_tcb_ctes3
                               ccorres_move_array_assertion_tcb_ctes
                               ccorres_move_const_guard)+
                   apply (rule_tac var="newVTable_'" and var_update="newVTable_'_update"
                                in getCTE_h_val_ccorres_split[where P=\<top>])
                     apply simp
                    apply ceqv
                   apply (rename_tac vs_cap vs_cap')
                   (* get capVSBasePtr from the vspace cap on C side (we don't know it's vspace cap yet) *)
                   apply (rule ccorres_symb_exec_r) (* can't use csymbr, we need to use alternative spec rule *)
                     apply (rule_tac xf'=ret__unsigned_longlong_' in ccorres_abstract, ceqv)
                     apply (rename_tac vspace_cap_c_ptr_maybe)
                     apply csymbr+
                     apply (simp add: isValidVTableRoot_conv cong: call_ignore_cong)
                     apply (rule ccorres_Cond_rhs_Seq)
                     (* \<not> isValidVTableRoot (cteCap vs_cap) *)
                      apply simp
                      apply (rule ccorres_split_throws)
                       apply (rule ccorres_call_hSkip)
                         apply (rule slowpath_ccorres, simp+)
                      apply (vcg exspec=slowpath_noreturn_spec)
                     apply (simp cong: call_ignore_cong)

                     (* AARCH64+hyp specific *)
                     apply (drule isValidVTableRootD')
                     (* we now know base address we read on the C side was from a vspace cap *)
                     apply (rule_tac P="vspace_cap_c_ptr_maybe = capUntypedPtr (cteCap vs_cap)"
                                  in ccorres_gen_asm2)
                     apply (simp cong: call_ignore_cong)
                     (* C: get the asid *)
                     apply (rule ccorres_rhs_assoc2)
                     apply (rule_tac xf'=asid___unsigned_long_'
                                 and val="fst (the (capPTMappedAddress (capCap (cteCap vs_cap))))"
                                  in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
                        apply (rule conseqPre, vcg)
                        apply (clarsimp simp: cap_get_tag_isCap isArchVSpacePTCap_def2
                                              ccap_relation_vspace_mapped_asid[symmetric])
                       apply ceqv
                      (* get asid_entry for asid *)
                      apply (ctac add: findMapForASID_ccorres)
                        apply (rename_tac asid_map_entry_opt asid_map_entry')
                        apply csymbr
                        apply csymbr
                        apply (simp add: casid_map_relation_get_tag_None cong: call_ignore_cong)
                        apply (rule ccorres_Cond_rhs_Seq)
                         (* no asid map entry for asid *)
                         apply simp
                         apply (rule ccorres_cond_true_seq)
                         apply (rule ccorres_split_throws)
                          apply (rule ccorres_call_hSkip)
                            apply (rule slowpath_ccorres, simp+)
                         apply (vcg exspec=slowpath_noreturn_spec)
                        apply (simp cong: call_ignore_cong)
                        apply (rule_tac xf'=ret__int_'
                                    and val="from_bool (apVSpace (the asid_map_entry_opt)
                                                        \<noteq> capPTBasePtr (capCap (cteCap vs_cap)))"
                                     in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
                           apply (rule conseqPre, vcg)
                           apply (clarsimp simp: from_bool_eq_if' vspace_cap_capUntypedPtr_capPTBasePtr
                                                 casid_map_relation_Some_get_tag
                                                 casid_map_relation_Some_c_lift_eqs)
                          apply ceqv
                         apply (simp cong: call_ignore_cong)
                         (* C does two checks/aborts, but Haskell only one, so direct If-condition
                            equivalence doesn't match. Step over C side, resolve Haskell check using
                            resulting non-abort conditions. *)
                         apply (rule ccorres_Cond_rhs_Seq)
                          (* vspace in asid map entry doesn't match vspace cap *)
                          apply clarsimp
                          apply (rule ccorres_split_throws)
                           apply (rule ccorres_call_hSkip)
                             apply (rule slowpath_ccorres, simp+)
                          apply (vcg exspec=slowpath_noreturn_spec)
                         apply (simp cong: call_ignore_cong)
                         (* we can't directly relate getting stored_vmid_valid_CL to None/Some on the
                            Haskell side, but we can relate equating the result to 0 (i.e. no valid vmid) *)
                         apply csymbr
                         apply (simp cong: call_ignore_cong)
                         apply (rule_tac C'="{_. apVMID (the asid_map_entry_opt) = None}"
                                      in ccorres_rewrite_cond_sr_Seq[where Q=\<top> and Q'=UNIV])
                          apply (clarsimp simp: casid_map_relation_Some_c_lift_eqs)
                         apply (rule ccorres_Cond_rhs_Seq)
                          (* no valid VMID *)
                          apply clarsimp
                          apply (rule ccorres_split_throws)
                           apply (rule ccorres_call_hSkip)
                             apply (rule slowpath_ccorres, simp+)
                          apply (vcg exspec=slowpath_noreturn_spec)
                         (* ap_entry/VMID check on Haskell side is now trivially true with clarsimp, but we
                            have to avoid exploding our free variables to avoid having to wrap them
                            back up during wp reasoning (e.g. \<exists>y. asid_map_entry_opt = Some y) *)
                         apply (simp cong: call_ignore_cong)
                         apply (rule ccorres_If_True_drop, solves clarsimp)

                         (* store VMID in first word of stored_hw_asid, which will be used later on the C side *)
                         apply (rule_tac xf'=ret__unsigned_longlong_'
                                     and val="ucast (the (apVMID (the asid_map_entry_opt)))"
                                      in ccorres_symb_exec_r_known_rv[where R=\<top> and R'=UNIV])
                            apply (rule conseqPre, vcg)
                            apply (clarsimp simp: casid_map_relation_Some_get_tag
                                                  casid_map_relation_Some_c_lift_eqs)
                           apply ceqv
                          apply (simp cong: call_ignore_cong)
                          apply csymbr

                          apply (ctac add: getCurDomain_maxDom_ccorres_dom_')
                            apply (rename_tac curDom curDom')
                            apply (rule_tac P="curDom \<le> maxDomain" in ccorres_gen_asm)
                            apply (simp add: prio_and_dom_limit_helpers cong: call_ignore_cong)
                            apply (rule ccorres_move_c_guard_tcb)
                            apply (rule ccorres_pre_threadGet)
                            apply simp (* we have to do this simp without the call_ignore_cong,
                                          otherwise isHighestPrio_ccorres's args won't get simplified *)
                            apply (ctac add: isHighestPrio_ccorres)
                              apply (rename_tac highest highest')
                              apply (simp add: to_bool_def cong: call_ignore_cong)
                              apply (rule ccorres_cond_seq)
                              apply (rule ccorres_cond2'[where R=\<top>], blast)
                               (* not highest priority *)
                               apply (rule ccorres_split_throws)
                                apply (rule ccorres_call_hSkip)
                                  apply (rule slowpath_ccorres, simp+)
                               apply (vcg exspec=slowpath_noreturn_spec)
                              apply (simp cong: call_ignore_cong)

                              (* Note: AArch32 does its vspace checks here *)

                              (* get caller domain on Haskell side *)
                              apply (simp add: ccap_relation_reply_helper cong: call_ignore_cong)
                              apply (rule ccorres_move_c_guard_tcb ccorres_move_const_guard)+
                              apply (rule ccorres_pre_threadGet)
                              apply (rename_tac destDom)
                              (* The C does not compare domains when maxDomain is 0, since then both
                                 threads will be in the current domain. Since we can show both threads
                                 must be \<le> maxDomain, we can rewrite this test to only comparing domains
                                 even when maxDomain is 0, making the check identical to the Haskell. *)
                              apply (rule_tac C'="{s. destDom \<noteq> curDom}"
                                        and Q="obj_at' ((=) destDom \<circ> tcbDomain)
                                                       (capTCBPtr (cteCap caller_cap))
                                               and (\<lambda>s. ksCurDomain s = curDom \<and> curDom \<le> maxDomain
                                                        \<and> destDom \<le> maxDomain)"
                                        and Q'=UNIV in ccorres_rewrite_cond_sr_Seq)
                               apply (simp add: from_bool_eq_if from_bool_eq_if' ccorres_IF_True)
                               apply clarsimp
                               apply (drule(1) obj_at_cslift_tcb)+
                               apply (clarsimp simp: typ_heap_simps' rf_sr_ksCurDomain)
                               apply (drule ctcb_relation_tcbDomain[symmetric])
                               apply (case_tac "0 < maxDomain";
                                      solves \<open>clarsimp simp: maxDom_sgt_0_maxDomain not_less\<close>)
                              apply (rule ccorres_seq_cond_raise[THEN iffD2])
                              apply (rule_tac R=\<top> in ccorres_cond2', blast)
                               apply (rule ccorres_split_throws)
                                apply (rule ccorres_call_hSkip)
                                  apply (rule slowpath_ccorres, simp+)
                               apply (vcg exspec=slowpath_noreturn_spec)
                              apply (simp cong: call_ignore_cong)

                              (* Now fully committed to fastpath *)
                              (* set current thread to BlockedOnReceive *)
                              apply (rule ccorres_rhs_assoc2)
                              apply (rule ccorres_rhs_assoc2)
                              apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                                  apply (rule_tac P="capAligned (theRight luRet)" in ccorres_gen_asm)
                                  apply (rule_tac P="canonical_address (capEPPtr (projr luRet))" in ccorres_gen_asm)
                                  apply (rule_tac P=\<top> and P'="\<lambda>s. ksCurThread s = curThread"
                                               in threadSet_ccorres_lemma3)
                                   apply vcg
                                  apply (clarsimp simp: rf_sr_ksCurThread typ_heap_simps'
                                                        h_t_valid_clift_Some_iff)
                                  apply (clarsimp simp: capAligned_def isCap_simps objBits_simps
                                                        "StrictC'_thread_state_defs" mask_def)
                                  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                                        typ_heap_simps' objBits_defs)
                                  apply (rule conjI)
                                   apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                                         update_tcb_map_tos map_to_tcbs_upd)
                                   apply (subst map_to_ctes_upd_tcb_no_ctes, assumption)
                                    apply (rule ball_tcb_cte_casesI, simp_all)[1]
                                   apply (simp add: cep_relations_drop_fun_upd)
                                   apply (erule cmap_relation_updI, erule ko_at_projectKO_opt)
                                    apply (simp add: ctcb_relation_def cthread_state_relation_def
                                                     "StrictC'_thread_state_defs")
                                    apply (clarsimp simp: ccap_relation_ep_helpers)
                                   apply simp
                                  apply (rule conjI, erule cready_queues_relation_not_queue_ptrs)
                                    apply (rule ext, simp split: if_split)
                                   apply (rule ext, simp split: if_split)
                                  apply (simp add: carch_state_relation_def cmachine_state_relation_def
                                                   typ_heap_simps' map_comp_update projectKO_opt_tcb
                                                   cvariable_relation_upd_const ko_at_projectKO_opt)
                                 apply ceqv
                                (* update endpoint queue *)
                                apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
                                apply (rule_tac xf'=xfdc and r'=dc in ccorres_split_nothrow)
                                    apply (rule fastpath_enqueue_ccorres[simplified])
                                    apply simp
                                   apply ceqv

                                  (* update MDB and reset tcbCallerSlot in current thread *)
                                  apply (simp add: liftM_def)
                                  apply (rule ccorres_move_c_guard_tcb_ctes3)
                                  apply (rule_tac r'="\<lambda>rv rv'. rv' = mdbPrev (cteMDBNode rv)"
                                              and xf'=ret__unsigned_longlong_' in ccorres_split_nothrow)
                                      apply (rule_tac P="tcb_at' curThread
                                                         and (\<lambda>s. ksCurThread s = curThread)"
                                                   in getCTE_ccorres_helper[where P'=UNIV])
                                      apply (rule conseqPre, vcg)
                                      apply (clarsimp simp: typ_heap_simps' cte_level_bits_def
                                                            tcbCallerSlot_def size_of_def
                                                            tcb_cnode_index_defs)
                                      apply (clarsimp simp: ccte_relation_def map_option_Some_eq2)
                                     apply ceqv
                                    apply (rule ccorres_assert)
                                    apply (rename_tac mdbPrev_cte mdbPrev_cte_c)
                                    apply (rule ccorres_split_nothrow_dc)
                                       apply (simp add: updateMDB_def Let_def
                                                   cong: if_cong)
                                       apply (rule_tac P="cte_wp_at' ((=) mdbPrev_cte)
                                                            (curThread + (tcbCallerSlot << cte_level_bits))
                                                          and valid_mdb'"
                                                    in ccorres_from_vcg[where P'=UNIV])
                                       apply (rule allI, rule conseqPre, vcg)
                                       apply (clarsimp simp: cte_wp_at_ctes_of)
                                       apply (drule(2) valid_mdb_ctes_of_prev[rotated])
                                       apply (clarsimp simp: cte_wp_at_ctes_of)
                                       apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
                                       apply (clarsimp simp: typ_heap_simps' split_def)
                                       apply (rule getCTE_setCTE_rf_sr, simp_all)[1]
                                       apply (clarsimp simp: ccte_relation_def map_option_Some_eq2
                                                             cte_to_H_def mdb_node_to_H_def
                                                             c_valid_cte_def)
                                      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
                                             rule ccorres_rhs_assoc2)
                                      apply (rule ccorres_split_nothrow_dc)
                                         apply (rule_tac P="cte_at' (curThread + (tcbCallerSlot << cte_level_bits))
                                                            and tcb_at' curThread"
                                                      in ccorres_from_vcg[where P'=UNIV])
                                         apply (rule allI, rule conseqPre, vcg)
                                         apply (clarsimp simp: cte_wp_at_ctes_of)
                                         apply (rule cmap_relationE1[OF cmap_relation_cte], assumption+)
                                         apply (clarsimp simp: typ_heap_simps' split_def tcbCallerSlot_def
                                                               tcb_cnode_index_defs
                                                               cte_level_bits_def size_of_def
                                                               packed_heap_update_collapse_hrs)
                                         apply (rule setCTE_rf_sr, simp_all add: typ_heap_simps')[1]
                                         apply (clarsimp simp: ccte_relation_eq_ccap_relation makeObject_cte
                                                               mdb_node_to_H_def nullMDBNode_def
                                                               ccap_relation_NullCap_iff)
                                        (* copy message registers *)
                                        apply (simp add: ccap_relation_reply_helper)
                                        apply csymbr
                                        apply (ctac add: fastpath_copy_mrs_ccorres[unfolded forM_x_def])
                                          apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow)
                                              apply (simp add: setThreadState_runnable_simp)
                                              apply (rule_tac P=\<top> in threadSet_ccorres_lemma2, vcg)
                                              apply (clarsimp simp: typ_heap_simps' rf_sr_def
                                                                    cstate_relation_def Let_def)
                                              apply (rule conjI)
                                               apply (clarsimp simp: cpspace_relation_def typ_heap_simps'
                                                                     update_tcb_map_tos map_to_tcbs_upd)
                                               apply (subst map_to_ctes_upd_tcb_no_ctes, assumption)
                                                apply (rule ball_tcb_cte_casesI, simp_all)[1]
                                               apply (simp add: cep_relations_drop_fun_upd)
                                               apply (erule cmap_relation_updI, erule ko_at_projectKO_opt)
                                                apply (simp add: ctcb_relation_def cthread_state_relation_def)
                                               apply simp
                                              apply (rule conjI, erule cready_queues_relation_not_queue_ptrs)
                                                apply (rule ext, simp split: if_split)
                                               apply (rule ext, simp split: if_split)
                                              apply (simp add: carch_state_relation_def cmachine_state_relation_def
                                                               typ_heap_simps' map_comp_update projectKO_opt_tcb
                                                               cvariable_relation_upd_const ko_at_projectKO_opt)
                                             apply ceqv
                                            (* switch to thread *)
                                            apply (simp only: bind_assoc[symmetric])
                                            apply (rule ccorres_stateAssert_after)
                                            apply (rule ccorres_split_nothrow_novcg_dc)
                                               apply simp
                                               apply (rule ccorres_call,
                                                      rule_tac vmid="ucast (the (apVMID (the asid_map_entry_opt)))"
                                                           and vsroot="capUntypedPtr (cteCap vs_cap)"
                                                           and asid="fst (the (capPTMappedAddress (capCap (cteCap vs_cap))))"
                                                            in switchToThread_fp_ccorres,
                                                      simp+)[1]
                                              (* set message info registers and restore *)
                                              apply (rule_tac P="\<lambda>s. ksCurThread s = capTCBPtr (cteCap caller_cap)"
                                                           in ccorres_cross_over_guard)
                                              apply csymbr
                                              apply csymbr
                                              apply (rule ccorres_call_hSkip)
                                                apply (rule fastpath_restore_ccorres)
                                               apply simp
                                              apply simp
                                             (* now WP/VCG reasoning mop-up operation starts *)
                                             apply (simp add: setCurThread_def)
                                             apply wp
                                              apply (rule_tac P=\<top> in hoare_triv, simp)
                                             apply simp
                                            apply (simp add: imp_conjL rf_sr_ksCurThread del: all_imp_to_ex)
                                            apply (clarsimp simp: ccap_relation_ep_helpers guard_is_UNIV_def
                                                                  mi_from_H_def signed_n_msgRegisters_to_H
                                                                  messageInfoFromWord_def Let_def
                                                                  seL4_MessageInfo_lift_def
                                                                  msgLengthBits_def msgExtraCapBits_def
                                                                  msgMaxExtraCaps_def shiftL_nat
                                                                  mask_def msgLabelBits_def)
                                            apply (force simp: size_msgRegisters_def msgMaxLength_def
                                                         split: if_splits)
                                           apply (wp sts_valid_objs' asid_has_vmid_lift)
                                          apply simp
                                          apply (vcg exspec=thread_state_ptr_set_tsType_np_modifies)
                                         apply (simp add: pred_conj_def)
                                         apply (rule mapM_x_wp'[OF hoare_weaken_pre])
                                          apply (wp asid_has_vmid_lift)
                                         apply clarsimp
                                        apply simp
                                        apply (vcg exspec=fastpath_copy_mrs_modifies)
                                       apply simp
                                       apply wp
                                       apply (wp setCTE_cte_wp_at_other asid_has_vmid_lift)
                                      apply simp
                                      apply vcg
                                     apply simp
                                     apply (wp | simp
                                            | wp (once) updateMDB_weak_cte_wp_at
                                            | wp (once) updateMDB_cte_wp_at_other asid_has_vmid_lift)+
                                    apply (vcg exspec=mdb_node_ptr_mset_mdbNext_mdbRevocable_mdbFirstBadged_modifies)
                                   apply simp
                                   apply (wp getCTE_wp')
                                  apply simp
                                  apply vcg
                                 apply (simp add: shiftl_t2n)
                                 apply (wp hoare_drop_imps setEndpoint_valid_mdb' set_ep_valid_objs'
                                           setObject_no_0_obj'[where 'a=endpoint, folded setEndpoint_def]
                                           asid_has_vmid_lift)
                                apply simp
                                apply (vcg exspec=endpoint_ptr_mset_epQueue_tail_state_modifies
                                           exspec=endpoint_ptr_set_epQueue_head_np_modifies
                                           exspec=endpoint_ptr_get_epQueue_tail_modifies)
                               apply (simp add: valid_pspace'_def pred_conj_def conj_comms
                                                valid_mdb'_def)
                               apply (wp threadSet_cur threadSet_tcbState_valid_objs
                                         threadSet_state_refs_of' threadSet_ctes_of
                                         valid_ep_typ_at_lift' threadSet_cte_wp_at' asid_has_vmid_lift
                                      | simp)+
                              apply (vcg exspec=thread_state_ptr_mset_blockingObject_tsType_modifies)
                             apply simp
                             (* throw away results of isHighestPrio and the fastfail shortcut *)
                             apply (wp (once) hoare_drop_imp, wp)
                             apply (wp (once) hoare_drop_imp, wp)
                            apply simp
                            apply (vcg exspec=isHighestPrio_modifies)
                           apply simp
                           apply (rule cd_wp)
                          apply simp
                          apply vcg
                         apply simp
                         apply vcg
                        apply simp
                        apply vcg
                       apply simp
                       apply (rule getASIDPoolEntry_wp)
                      apply simp
                      apply (vcg exspec=findMapForASID_modifies)
                     apply simp
                     apply (vcg exspec=cap_vspace_cap_get_capVSMappedASID_modifies)
                    apply simp
                    (* accessing VSBasePtr without knowing it's a VSpace, can't use default spec *)
                    apply (rule conseqPre, vcg exspec=cap_vspace_cap_get_capVSBasePtr_spec2)
                    apply (rule subset_refl)
                   apply (rule conseqPre, vcg exspec=cap_vspace_cap_get_capVSBasePtr_spec2)
                   apply clarsimp
                  apply simp
                  apply (rule threadGet_wp)
                 apply (simp add: syscall_from_H_def ccap_relation_reply_helper)
                 apply (vcg exspec=seL4_Fault_get_seL4_FaultType_modifies)
                apply simp
                apply (simp add: ccap_relation_reply_helper)
                apply (rule return_wp)
               apply simp
               apply (vcg exspec=fastpath_reply_cap_check_modifies)
              apply simp
              apply (rule getEndpoint_wp)
             apply (simp add: syscall_from_H_def ccap_relation_reply_helper)
             apply (vcg exspec=endpoint_ptr_get_state_modifies)
            apply simp
            apply (wp option_case_liftM_getNotification_wp[unfolded fun_app_def])
           apply simp
           apply vcg
          apply (simp add: getSlotCap_def)
          apply (rule valid_isLeft_theRight_split)
          apply (wp getCTE_wp')
          apply (rule validE_R_abstract_rv)
          apply wp
         apply simp
         apply (vcg exspec=lookup_fp_modifies)
        apply simp
        apply (rule threadGet_wp)
       apply simp
       apply vcg
      apply simp
      apply (rule user_getreg_wp)
     apply simp
     apply (rule user_getreg_wp)
    apply (rule conjI)
     (* Haskell precondition *)
     apply (prop_tac "scast (scast tcbCallerSlot :: int_word) = tcbCallerSlot")
      apply (simp add: tcbCallerSlot_def)
     apply (clarsimp simp: ct_in_state'_def invs_cur' invs_arch_state' obj_at_tcbs_of word_sle_def)
     apply (clarsimp simp: invs_ksCurDomain_maxDomain')
     apply (rename_tac cur_tcb cte)
     apply (frule invs_valid_objs')
     apply (frule invs_queues)
     apply (clarsimp simp: valid_queues_def)
     apply (frule tcbs_of_aligned')
      apply (simp add: invs_pspace_aligned')
     apply (frule tcbs_of_cte_wp_at_caller)
     apply (clarsimp simp: size_of_def field_simps
                     dest!: ptr_val_tcb_ptr_mask2[unfolded mask_def])
     apply (frule st_tcb_at_state_refs_ofD')
     apply (frule ctes_of_valid', fastforce)
     apply (clarsimp simp: obj_at_tcbs_of ct_in_state'_def st_tcb_at_tcbs_of
                           invs_valid_objs' ctes_of_valid'
                           fun_upd_def[symmetric] fun_upd_idem pred_tcb_at'_def invs_no_0_obj'
                      cong: conj_cong)
     apply (rule conjI) (* obj_at' of ep ptr *)
      apply (fastforce dest: ctes_of_valid' simp: valid_cap_simps' isCap_simps cte_wp_at_ctes_of)
     apply clarsimp
     apply (frule_tac p="p + tcbCallerSlot * cte_size" for p cte_size in ctes_of_valid', clarsimp)
     apply (clarsimp simp: valid_capAligned)
     apply (frule_tac p="p + tcbVTableSlot * cte_size" for p cte_size in ctes_of_valid', clarsimp)
     apply (rule conjI) (* asid_wf *)
      apply (clarsimp simp: isCap_simps valid_cap'_def dest!: isValidVTableRootD)
      apply (solves \<open>clarsimp simp: wellformed_mapdata'_def\<close>)
     apply (frule_tac tcb=tcb in tcbs_of_valid_tcb'[OF invs_valid_objs', rotated], simp)
     apply (clarsimp simp add: valid_tcb'_def)
     apply (rule conjI; clarsimp?) (* canonical_address (capEPPtr (cteCap ctea)) *)
      apply (clarsimp simp: obj_at'_is_canonical dest!: invs_pspace_canonical')
     apply (clarsimp simp: isCap_simps valid_cap'_def[split_simps capability.split]
                           maskCapRights_def cte_wp_at_ctes_of cte_level_bits_def)
     apply (frule_tac p=a in ctes_of_valid', clarsimp)
     apply (simp add: valid_cap_simps')
     apply (frule invs_mdb')
     apply (rule conjI, solves clarsimp)+ (* a bunch of consequences of invs' *)
     apply (clarsimp simp: cte_wp_at_ctes_of cte_level_bits_def
                           makeObject_cte isValidVTableRoot_def
                           to_bool_def
                           valid_mdb'_def valid_tcb_state'_def)
     apply (rule conjI; clarsimp?) (* msglength *)
      apply (simp add: word_le_nat_alt size_msgRegisters_def n_msgRegisters_def length_msgRegisters)
     apply (prop_tac "capPTBasePtr (capCap (cteCap ctec)) = capUntypedPtr (cteCap ctec)")
      apply (solves \<open>clarsimp simp add: isVTableRoot_ex\<close>)
     apply (rule conjI) (* asid_has_vmid *)
      apply (clarsimp simp: asid_has_vmid_def asid_has_entry_def)
       apply (case_tac asid_entry, fastforce)
     apply (frule ko_at_valid_ep', fastforce)
     apply (frule invs_mdb')
     apply (safe del: notI disjE)[1]
       apply (simp add: isSendEP_def valid_ep'_def tcb_at_invs'
                 split: Structures_H.endpoint.split_asm)
       apply (rule subst[OF endpoint.sel(1)],
              erule st_tcb_at_not_in_ep_queue[where P="(=) Running", rotated],
              clarsimp+)
       apply (simp add: obj_at_tcbs_of st_tcb_at_tcbs_of)
      apply (drule invs_sym')
      apply (erule_tac P=sym_refs in subst[rotated])
      apply (rule fun_upd_idem[symmetric])
      apply (clarsimp simp: tcb_bound_refs'_def)
      apply (case_tac ntfnptr, simp_all)[1]
      apply (clarsimp simp: set_eq_subset)
     apply (solves \<open>clarsimp simp: capAligned_def isVTableRoot_def field_simps\<close>)

    (* C precondition *)
    apply (clarsimp simp: syscall_from_H_def[split_simps syscall.split]
                          word_sle_def word_sless_def rf_sr_ksCurThread
                          size_of_def cte_level_bits_def
                          tcb_cnode_index_defs tcbCTableSlot_def tcbVTableSlot_def
                          tcbReplySlot_def tcbCallerSlot_def from_bool_eq_if' of_bl_from_bool)
    apply (frule obj_at_bound_tcb_grandD, clarsimp, clarsimp, assumption)
    apply (clarsimp simp: typ_heap_simps' ccap_relation_ep_helpers)
    apply (clarsimp simp: ccte_relation_eq_ccap_relation ccap_relation_case_sum_Null_endpoint
                          typ_heap_simps' cap_get_tag_isCap mi_from_H_def)
    apply (intro conjI impI allI;
           clarsimp simp: isCap_simps capAligned_def objBits_simps'
                          typ_heap_simps
                          casid_map_relation_Some_get_tag
                   dest!: ptr_val_tcb_ptr_mask2[unfolded objBits_def mask_def, simplified];
           (solves \<open>clarsimp simp: ctcb_relation_def\<close>)?)
      (* cap_get_tag_isCap hides info obtained from isValidVTableRootD' *)
      apply (frule (1) capVSBasePtr_CL_capUntypedPtr_helper,
             clarsimp simp: cap_get_tag_isCap isCap_simps dest!: isValidVTableRootD')+

    done
qed

end

end
