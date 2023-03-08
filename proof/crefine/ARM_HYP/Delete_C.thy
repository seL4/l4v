(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Delete_C
imports Finalise_C
begin

context kernel_m
begin

lemma ccorres_drop_cutMon:
  "ccorres_underlying sr Gamm r xf arrel axf P P' hs f g
    \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf P P' hs (cutMon Q f) g"
  apply (clarsimp simp: ccorres_underlying_def
                        cutMon_def fail_def
                 split: if_split_asm)
  apply (subst if_P, simp)
  apply fastforce
  done

lemma ccorres_drop_cutMon_bind:
  "ccorres_underlying sr Gamm r xf arrel axf P P' hs (f >>= f') g
    \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf P P' hs (cutMon Q f >>= f') g"
  apply (clarsimp simp: ccorres_underlying_def
                        cutMon_def fail_def bind_def
                 split: if_split_asm)
  apply (subst if_P, simp)+
  apply fastforce
  done

lemma ccorres_drop_cutMon_bindE:
  "ccorres_underlying sr Gamm r xf arrel axf P P' hs (f >>=E f') g
    \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf P P' hs (cutMon Q f >>=E f') g"
  apply (clarsimp simp: ccorres_underlying_def
                        cutMon_def fail_def bind_def bindE_def lift_def
                 split: if_split_asm)
  apply (subst if_P, simp)+
  apply fastforce
  done

lemma ccorres_cutMon:
  "(\<And>s. Q s \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf P P' hs (cutMon ((=) s) f) g)
        \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf P P' hs (cutMon Q f) g"
  apply (clarsimp simp: ccorres_underlying_def
                        cutMon_def fail_def bind_def
                 split: if_split_asm)
  apply (erule meta_allE, drule(1) meta_mp)
  apply (drule(1) bspec)
  apply (clarsimp simp: fail_def
                 split: if_split_asm)
  apply (subst if_P, assumption)+
  apply fastforce
  done

lemma ccap_zombie_radix_less1:
  "\<lbrakk> ccap_relation cap ccap; isZombie cap; capAligned cap \<rbrakk>
      \<Longrightarrow> \<not> isZombieTCB_C (capZombieType_CL (cap_zombie_cap_lift ccap))
            \<longrightarrow> capZombieType_CL (cap_zombie_cap_lift ccap) < 28"
  apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap[THEN iffD2])
  apply (clarsimp simp: Let_def capAligned_def
                        objBits_simps' word_bits_conv word_less_nat_alt
                        word_le_nat_alt less_mask_eq
                 split: if_split_asm)
  done

lemmas ccap_zombie_radix_less2
  = order_less_le_trans [OF mp [OF ccap_zombie_radix_less1]]

lemma ccap_zombie_radix_less3:
  "\<lbrakk> ccap_relation cap ccap; isZombie cap; capAligned cap \<rbrakk>
      \<Longrightarrow> get_capZombieBits_CL (cap_zombie_cap_lift ccap) < 28"
  by (clarsimp simp: get_capZombieBits_CL_def Let_def
                     less_mask_eq ccap_zombie_radix_less2
              split: if_split)

lemmas ccap_zombie_radix_less4
  = order_less_le_trans [OF ccap_zombie_radix_less3]

lemma cap_zombie_cap_get_capZombieNumber_spec:
  notes if_cong[cong]
  shows
  "\<forall>cap s. \<Gamma>\<turnstile> \<lbrace>s. ccap_relation cap \<acute>cap \<and> isZombie cap \<and> capAligned cap\<rbrace>
     Call cap_zombie_cap_get_capZombieNumber_'proc
   {s'. ret__unsigned_long_' s' = of_nat (capZombieNumber cap)}"
  apply vcg
  apply clarsimp
  apply (rule context_conjI, simp add: cap_get_tag_isCap)
  apply (frule(2) ccap_zombie_radix_less1)
  apply (frule(2) ccap_zombie_radix_less3)
  apply (drule(1) cap_get_tag_to_H)
  apply clarsimp
  apply (rule conjI)
   apply unat_arith
  apply (fold mask_2pm1)
  apply (simp add: get_capZombieBits_CL_def Let_def split: if_split_asm)
  apply (subst unat_Suc2)
   apply clarsimp
  apply (subst less_mask_eq, erule order_less_le_trans)
   apply simp+
  done

lemma cap_zombie_cap_set_capZombieNumber_spec:
  "\<forall>cap s. \<Gamma>\<turnstile> \<lbrace>s. ccap_relation cap \<acute>cap \<and> isZombie cap \<and> capAligned cap
                     \<and> unat (n_' s) \<le> zombieCTEs (capZombieType cap)\<rbrace>
     Call cap_zombie_cap_set_capZombieNumber_'proc
   {s'. ccap_relation (capZombieNumber_update (\<lambda>_. unat (n_' s)) cap)
               (ret__struct_cap_C_' s')}"
  apply vcg
  apply (rule context_conjI, simp add: cap_get_tag_isCap)
  apply clarsimp
  apply (frule(2) ccap_zombie_radix_less3)
  apply (rule conjI, unat_arith)
  apply clarsimp
  apply (frule(2) ccap_zombie_radix_less1)
  apply (clarsimp simp: cap_zombie_cap_lift
                        ccap_relation_def map_option_Some_eq2
                        cap_to_H_def get_capZombieBits_CL_def
                 split: if_split_asm)
   apply (simp add: mask_def word_bw_assocs word_ao_dist)
   apply (rule sym, rule less_mask_eq[where n=5, unfolded mask_def, simplified])
   apply unat_arith
  apply (clarsimp simp: Let_def mask_2pm1[symmetric])
  apply (subst unat_Suc2, clarsimp)+
  apply (subst less_mask_eq, erule order_less_le_trans, simp)+
  apply (simp add: word_ao_dist word_bw_assocs)
  apply (rule sym, rule less_mask_eq)
  apply (simp only: word_less_nat_alt)
  apply (subst unat_power_lower)
   apply (simp add: word_bits_conv)
  apply (erule order_le_less_trans)
  apply simp
  done

lemma capRemovable_spec:
  "\<forall>cap s.  \<Gamma>\<turnstile> \<lbrace>s. ccap_relation cap \<acute>cap \<and> (isZombie cap \<or> cap = NullCap) \<and> capAligned cap\<rbrace>
     Call capRemovable_'proc
      {s'. ret__unsigned_long_' s' = from_bool (capRemovable cap (ptr_val (slot_' s)))}"
  supply if_cong[cong]
  apply vcg
  apply (clarsimp simp: cap_get_tag_isCap(1-8)[THEN trans[OF eq_commute]])
  apply (simp add: capRemovable_def)
  apply (clarsimp simp: ccap_zombie_radix_less4)
  apply (subst eq_commute, subst from_bool_eq_if)
  apply (rule exI, rule conjI, assumption)
  apply clarsimp
  apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap[THEN iffD2])
  apply (case_tac slot)
  apply (clarsimp simp: get_capZombiePtr_CL_def Let_def get_capZombieBits_CL_def
                        isCap_simps unat_eq_1 unat_eq_0
                        less_mask_eq ccap_zombie_radix_less2
             split: if_split_asm)
  done

lemma capCyclicZombie_spec:
  "\<forall>cap s.  \<Gamma>\<turnstile> \<lbrace>s. ccap_relation cap \<acute>cap \<and> isZombie cap \<and> capAligned cap\<rbrace>
     Call capCyclicZombie_'proc
      {s'. ret__unsigned_long_' s' = from_bool (capCyclicZombie cap (ptr_val (slot_' s)))}"
  supply if_cong[cong]
  apply vcg
  apply (clarsimp simp: from_bool_0)
  apply (frule(1) cap_get_tag_isCap [THEN iffD2], simp)
  apply (subst eq_commute, subst from_bool_eq_if)
  apply (simp add: ccap_zombie_radix_less4)
  apply (case_tac slot, simp)
  apply (frule(1) cap_get_tag_to_H)
  apply (clarsimp simp: capCyclicZombie_def Let_def
                        get_capZombieBits_CL_def get_capZombiePtr_CL_def
                 split: if_split_asm)
   apply (auto simp: less_mask_eq ccap_zombie_radix_less2)
  done

lemma case_assertE_to_assert:
  "(case cap of
           Zombie ptr2 x xa \<Rightarrow>
                  haskell_assertE (P ptr2 x xa) []
                | _ \<Rightarrow> returnOk ())
       = liftE (assert (case cap of Zombie ptr2 x xa \<Rightarrow> P ptr2 x xa | _ \<Rightarrow> True))"
  apply (simp add: assertE_def returnOk_liftE assert_def
            split: capability.split if_split)
  done

lemma cteDelete_ccorres1:
  assumes fs_cc:
    "ccorres (cintr \<currency> (\<lambda>(success, cap) (success', cap'). success' = from_bool success \<and> ccap_relation cap cap' \<and> cleanup_info_wf' cap))
     (liftxf errstate finaliseSlot_ret_C.status_C (\<lambda>v. (success_C v, finaliseSlot_ret_C.cleanupInfo_C v))
                   ret__struct_finaliseSlot_ret_C_')
     (\<lambda>s. invs' s \<and> sch_act_simple s \<and> (expo \<or> ex_cte_cap_to' slot s))
     (UNIV \<inter> {s. slot_' s = Ptr slot} \<inter> {s. immediate_' s = from_bool expo}) []
     (cutMon ((=) s) (finaliseSlot slot expo)) (Call finaliseSlot_'proc)"
  shows
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_' )
     (\<lambda>s. invs' s \<and> sch_act_simple s \<and> (expo \<or> ex_cte_cap_to' slot s))
     (UNIV \<inter> {s. slot_' s = Ptr slot} \<inter> {s. exposed_' s = from_bool expo}) []
     (cutMon ((=) s) (cteDelete slot expo)) (Call cteDelete_'proc)"
  apply (cinit' lift: slot_' exposed_' cong: call_ignore_cong)
   apply (simp add: cteDelete_def split_def cutMon_walk_bindE
               del: Collect_const cong: call_ignore_cong)
   apply (clarsimp simp del: Collect_const cong: call_ignore_cong)
   apply (ctac(no_vcg) add: fs_cc)
     apply (rule ccorres_drop_cutMon)
     apply (simp add: from_bool_0 whenE_def split_def
                      Collect_False
                 del: Collect_const)
     apply (rule ccorres_if_lhs)
      apply (simp only: imp_conv_disj simp_thms)
      apply (simp add: liftE_liftM liftM_def)
      apply (ctac(no_vcg) add: emptySlot_ccorres)
       apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply wp
     apply (simp only: imp_conv_disj simp_thms)
     apply (simp add: returnOk_def)
     apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def)
    apply simp
    apply (rule ccorres_split_throws)
     apply (rule ccorres_return_C_errorE, simp+)[1]
    apply vcg
   apply wp
   apply (rule_tac Q'="\<lambda>rv. invs'" in hoare_post_imp_R)
    apply (wp cutMon_validE_drop finaliseSlot_invs)
   apply fastforce
  apply (auto simp: cintr_def)
  done

lemma zombie_rf_sr_helperE:
  "\<lbrakk> cte_wp_at' P p s; (s, s') \<in> rf_sr; invs' s;
      \<And>cte. P cte \<Longrightarrow> isZombie (cteCap cte);
      \<And>cap ccap cte. \<lbrakk> cap = cteCap cte; ccap = h_val
                        (hrs_mem (t_hrs_' (globals s')))
                        (cap_Ptr &(cte_Ptr p\<rightarrow>[''cap_C'']));
                    P cte; ccap_relation cap ccap; capAligned cap;
                    cap_get_tag ccap = scast cap_zombie_cap;
                    get_capZombiePtr_CL (cap_zombie_cap_lift ccap)
                            = capZombiePtr cap;
                    capZombieType_CL (cap_zombie_cap_lift ccap)
                            = (case_zombie_type ZombieTCB_C of_nat (capZombieType cap)) \<rbrakk>
               \<Longrightarrow> Q \<rbrakk>
     \<Longrightarrow> Q"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
  apply atomize
  apply (simp add: typ_heap_simps)
  apply (drule spec, drule(1) mp)+
  apply (clarsimp simp: cap_get_tag_isCap
                 dest!: ccte_relation_ccap_relation
                        valid_capAligned)
  apply (frule cap_get_tag_to_H, erule(1) cap_get_tag_isCap[THEN iffD2])
  apply (clarsimp simp: get_capZombiePtr_CL_def Let_def
                        get_capZombieBits_CL_def
                        isZombieTCB_C_def
                 split: if_split_asm)
  apply (simp add: less_mask_eq ccap_zombie_radix_less2
                   isZombieTCB_C_def)
  done

lemma of_nat_ZombieTCB_C:
  "n < 28 \<Longrightarrow> of_nat n \<noteq> (ZombieTCB_C :: word32)"
  apply (drule of_nat_mono_maybe[rotated, where 'a=32])
   apply simp
  apply (clarsimp simp: ZombieTCB_C_def)
  done

lemma case_zombie_type_map_inj:
  "case_zombie_type (ZombieTCB_C :: word32) of_nat (capZombieType cap)
     = case_zombie_type (ZombieTCB_C :: word32) of_nat (capZombieType cap')
    \<Longrightarrow> capAligned cap \<Longrightarrow> capAligned cap'
    \<Longrightarrow> isZombie cap \<Longrightarrow> isZombie cap' \<Longrightarrow>
       capZombieType cap = capZombieType cap'"
  apply (clarsimp simp: capAligned_def word_bits_conv
                        objBits_simps' isCap_simps
                        of_nat_ZombieTCB_C
                        not_sym [OF of_nat_ZombieTCB_C]
                 split: zombie_type.split_asm)
  apply (subst(asm) word_unat.Abs_inject)
    apply (simp add: unats_def)+
  done

lemma valid_cap_capZombieNumber_unats:
  "\<lbrakk> s \<turnstile>' cap; isZombie cap \<rbrakk>
       \<Longrightarrow> capZombieNumber cap \<in> unats 32"
  apply (clarsimp simp: valid_cap'_def isCap_simps
                 split: zombie_type.split_asm)
   apply (simp add: unats_def)
  apply (clarsimp simp only: unats_def mem_simps)
  apply (erule order_le_less_trans)
  apply (rule power_strict_increasing)
   apply (simp add: word_bits_conv)
  apply simp
  done

lemma cteDelete_invs'':
  "\<lbrace>invs' and sch_act_simple and (\<lambda>s. ex \<or> ex_cte_cap_to' ptr s)\<rbrace> cteDelete ptr ex \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: cteDelete_def whenE_def split_def)
  apply (rule hoare_pre, wp finaliseSlot_invs)
   apply (rule hoare_post_imp_R)
    apply (unfold validE_R_def)
    apply (rule use_spec)
    apply (rule spec_valid_conj_liftE1)
     apply (rule valid_validE_R, rule finaliseSlot_invs)
    apply (rule spec_valid_conj_liftE1)
     apply (rule finaliseSlot_removeable)
    apply (rule spec_valid_conj_liftE1)
     apply (rule finaliseSlot_irqs)
    apply (rule finaliseSlot_abort_cases'[folded finaliseSlot_def])
   apply clarsimp
  apply clarsimp
  done

lemma ccorres_Cond_rhs_Seq_ret_int:
  "\<lbrakk> P \<Longrightarrow> ccorres rvr xf Q S hs absf (f;;h);
     \<And>rv' t t'. ceqv \<Gamma> ret__int_' rv' t t' (g ;; h) (j rv');
     \<not> P \<Longrightarrow> ccorres rvr xf R T hs absf (j 0) \<rbrakk>
     \<Longrightarrow> ccorres rvr xf (\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not> P \<longrightarrow> R s))
                       {s. (P \<longrightarrow> s \<in> S) \<and> (\<not> P \<longrightarrow> s \<in> {s. s \<in> T \<and> ret__int_' s = 0})}
            hs absf (Cond {s. P} f g ;; h)"
  apply (rule ccorres_guard_imp2)
   apply (erule ccorres_Cond_rhs_Seq)
   apply (erule ccorres_abstract)
   apply (rule_tac P="rv' = 0" in ccorres_gen_asm2)
   apply simp
  apply simp
  done

(* it's a little painful to have to do this from first principles *)
lemma ccorres_cutMon_stateAssert:
  "\<lbrakk> Q s \<Longrightarrow> ccorres_underlying sr Gamm r xf arrel axf P P' hs
      (cutMon ((=) s) (a ())) c \<rbrakk> \<Longrightarrow>
   ccorres_underlying sr Gamm r xf arrel axf (\<lambda>s. Q s \<longrightarrow> P s) P' hs
      (cutMon ((=) s) (stateAssert Q [] >>= a)) c"
  apply (simp add: cutMon_walk_bind)
  apply (cases "\<not> Q s")
   apply (simp add: stateAssert_def cutMon_def exec_get assert_def
                    ccorres_fail'
              cong: if_cong[OF eq_commute])
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_drop_cutMon_bind)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_cutMon)
      apply (simp add: stateAssert_def exec_get return_def)
     apply (wp | simp)+
  done

lemma valid_Zombie_number_word_bits:
  "valid_cap' cap s \<Longrightarrow> isZombie cap
    \<Longrightarrow> capZombieNumber cap < 2 ^ word_bits"
  apply (clarsimp simp: valid_cap'_def isCap_simps)
  apply (erule order_le_less_trans)
  apply (rule order_le_less_trans[OF zombieCTEs_le])
  apply simp
  done


lemma ccorres_cutMon_locateSlotCap_Zombie:
  "\<lbrakk> (capZombiePtr cap + 2 ^ cte_level_bits * n, s) \<in> fst (locateSlotCap cap n s)
    \<Longrightarrow> ccorres_underlying rf_sr Gamm r xf arrel axf
      Q Q' hs
      (cutMon ((=) s) (a (capZombiePtr cap + 2 ^ cte_level_bits * n))) c \<rbrakk>
    \<Longrightarrow> ccorres_underlying rf_sr Gamm r xf arrel axf
      (Q and valid_cap' cap and (\<lambda>_. isZombie cap \<and> n = of_nat (capZombieNumber cap - 1)))
      {s. array_assertion (cte_Ptr (capZombiePtr cap)) (capZombieNumber cap - 1)
           (hrs_htd (t_hrs_' (globals s))) \<longrightarrow> s \<in> Q'} hs
      (cutMon ((=) s) (locateSlotCap cap n >>= a)) c"
  apply (simp add: locateSlot_conv in_monad cutMon_walk_bind)
  apply (rule ccorres_gen_asm)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_drop_cutMon_bind)
   apply (rule ccorres_symb_exec_l)
      apply (rule ccorres_cutMon)
      apply (clarsimp simp: in_monad stateAssert_def)
      apply (rule_tac P="\<lambda>s'. (capZombieType cap \<noteq> ZombieTCB \<longrightarrow>
           (case gsCNodes s' (capUntypedPtr cap) of None \<Rightarrow> False
                | Some n \<Rightarrow> of_nat (capZombieNumber cap - 1) < 2 ^ n))"
              in ccorres_cross_over_guard)
      apply (clarsimp simp: isCap_simps)
      apply assumption
     apply (wp | simp)+
  apply (clarsimp simp: isCap_simps stateAssert_def in_monad)
  apply (cases "capZombieType cap = ZombieTCB")
   apply (clarsimp simp: valid_cap_simps')
   apply (drule(1) rf_sr_tcb_ctes_array_assertion[
       where tcb="tcb_ptr_to_ctcb_ptr t" for t, simplified])
   apply (simp add: tcb_cnode_index_defs array_assertion_shrink_right)
  apply (clarsimp simp: option.split[where P="\<lambda>x. x"])
  apply (rule conjI)
   apply clarsimp
   apply blast
  apply (clarsimp dest!: of_nat_less_t2n)
  apply (drule(1) rf_sr_gsCNodes_array_assertion)
  apply (erule notE, erule array_assertion_shrink_right)
  apply (frule valid_Zombie_number_word_bits, simp+)
  by (simp add: unat_arith_simps unat_of_nat word_bits_def valid_cap_simps')

lemma reduceZombie_ccorres1:
  assumes fs_cc:
    "\<And>slot. \<lbrakk> capZombieNumber cap \<noteq> 0; expo;
               (slot, s) \<in> fst (locateSlotCap cap
                               (fromIntegral (capZombieNumber cap - 1)) s) \<rbrakk> \<Longrightarrow>
     ccorres (cintr \<currency> (\<lambda>(success, irqopt) (success', irq'). success' = from_bool success \<and> ccap_relation irqopt irq' \<and> cleanup_info_wf' irqopt))
     (liftxf errstate finaliseSlot_ret_C.status_C (\<lambda>v. (success_C v, finaliseSlot_ret_C.cleanupInfo_C v))
                   ret__struct_finaliseSlot_ret_C_')
     (\<lambda>s. invs' s \<and> sch_act_simple s \<and> ex_cte_cap_to' slot s)
     (UNIV \<inter> {s. slot_' s = Ptr slot} \<inter> {s. immediate_' s = from_bool False}) []
     (cutMon ((=) s) (finaliseSlot slot False)) (Call finaliseSlot_'proc)"
  shows
  "isZombie cap \<Longrightarrow>
   ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_' )
     (invs' and sch_act_simple and cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot)
     (UNIV \<inter> {s. slot_' s = Ptr slot} \<inter> {s. immediate_' s = from_bool expo}) []
     (cutMon ((=) s) (reduceZombie cap slot expo)) (Call reduceZombie_'proc)"
  apply (cinit' lift: slot_' immediate_')
   apply (simp add: from_bool_0 del: Collect_const)
   apply (rule_tac P="capZombieNumber cap < 2 ^ word_bits" in ccorres_gen_asm)
   apply (rule ccorres_move_c_guard_cte)
   apply (rule_tac xf'=ret__unsigned_long_'
               and val="capZombiePtr cap"
               and R="cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot and invs'"
            in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply vcg
      apply clarsimp
      apply (erule(2) zombie_rf_sr_helperE)
       apply simp
      apply (clarsimp simp: ccap_zombie_radix_less4)
     apply ceqv
    apply csymbr
    apply (rule ccorres_move_c_guard_cte)
    apply (rule_tac xf'=n_'
                and val="of_nat (capZombieNumber cap)"
                and R="cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot and invs'"
             in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
       apply (rule conseqPre, vcg)
       apply clarsimp
       apply (erule(2) zombie_rf_sr_helperE)
        apply simp
       apply fastforce
      apply ceqv
     apply (rule ccorres_move_c_guard_cte)
     apply (rule_tac xf'=ret__unsigned_'
                 and val="case_zombie_type ZombieTCB_C of_nat (capZombieType cap)"
                 and R="cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot and invs'"
              in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
        apply vcg
        apply clarsimp
        apply (erule(2) zombie_rf_sr_helperE)
         apply simp
        apply clarsimp
       apply ceqv
      apply csymbr
      apply (simp add: reduceZombie_def del: Collect_const)
      apply (simp only: cutMon_walk_if)
      apply (rule ccorres_if_lhs)
       apply (simp, rule ccorres_drop_cutMon, rule ccorres_fail)
      apply (rule ccorres_if_lhs)
       apply (simp add: Let_def Collect_True Collect_False assertE_assert liftE_bindE
                   del: Collect_const)
       apply (rule ccorres_drop_cutMon, rule ccorres_assert)
       apply (rule ccorres_rhs_assoc)+
       apply (simp add: liftE_bindE liftM_def case_assertE_to_assert
                   del: Collect_const)
       apply (rule ccorres_symb_exec_l[OF _ getCTE_inv _ empty_fail_getCTE])
        apply (rule ccorres_assert)
        apply (rule ccorres_move_c_guard_cte)
        apply (rule ccorres_symb_exec_r)
          apply (simp add: liftE_liftM liftM_def)
          apply (ctac(no_vcg) add: capSwapForDelete_ccorres)
           apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (simp add: return_def)
          apply wp
         apply vcg
        apply (rule conseqPre, vcg)
        apply clarsimp
       apply wp
      apply (rule ccorres_if_lhs)
       apply (simp add: Let_def liftE_bindE del: Collect_const)
       apply (rule ccorres_cutMon_locateSlotCap_Zombie)
       apply (simp add: cutMon_walk_bindE Collect_True del: Collect_const)
       apply (rule ccorres_rhs_assoc ccorres_move_c_guard_cte ccorres_Guard_Seq)+
       apply csymbr
       apply (ctac(no_vcg, no_simp) add: cteDelete_ccorres1)
          apply (rule ccorres_guard_imp2)
           apply (rule fs_cc, clarsimp+)[1]
          apply simp
         apply (rule ccorres_drop_cutMon)
         apply (simp add: Collect_False del: Collect_const)
         apply (rule ccorres_rhs_assoc ccorres_move_c_guard_cte)+
         apply (rule ccorres_symb_exec_l[OF _ getCTE_inv _ empty_fail_getCTE])
          apply (rule_tac F="\<lambda>rv'. \<exists>cp. ccap_relation (cteCap rv) cp
                                      \<and> rv' = cap_get_tag cp"
                      and xf'=ret__unsigned_'
                      and R="cte_wp_at' ((=) rv) slot"
                   in ccorres_symb_exec_r_abstract_UNIV[where R'=UNIV])
             apply (rule conseqPre, vcg)
             apply (clarsimp simp: cte_wp_at_ctes_of)
             apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
             apply (clarsimp dest!: ccte_relation_ccap_relation simp: typ_heap_simps)
             apply fastforce
            apply ceqv
           apply (clarsimp simp: cap_get_tag_isCap simp del: Collect_const)
           apply (rule ccorres_Cond_rhs_Seq)
            apply simp
            apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: returnOk_def return_def)
           apply (rule ccorres_Cond_rhs_Seq)
            apply (simp add: Let_def del: Collect_const)
            apply (rule ccorres_move_c_guard_cte ccorres_rhs_assoc)+
            apply (rule_tac xf'=ret__unsigned_long_'
                        and val="capZombiePtr (cteCap rv)"
                        and R="cte_wp_at' ((=) rv) slot and invs'"
                     in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
               apply (rule conseqPre, vcg)
               apply clarsimp
               apply (erule(2) zombie_rf_sr_helperE)
                apply simp
               apply (clarsimp simp: ccap_zombie_radix_less4)
              apply ceqv
             apply csymbr
             apply csymbr
             apply (simp only: if_1_0_0 simp_thms)
             apply (rule ccorres_Cond_rhs_Seq[rotated])
              apply (simp add: assertE_assert liftE_def)
              apply (rule ccorres_assert)
              apply (rule ccorres_cond_false_seq | simp)+
              apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: return_def)
             apply (rule ccorres_rhs_assoc)+
             apply (rule ccorres_move_c_guard_cte)
             apply (rule_tac xf'=ret__unsigned_long_'
                         and val="of_nat (capZombieNumber (cteCap rv))"
                         and R="cte_wp_at' ((=) rv) slot and invs'"
                      in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
                apply (rule conseqPre, vcg)
                apply clarsimp
                apply (erule(2) zombie_rf_sr_helperE)
                 apply simp
                apply fastforce
               apply ceqv
              apply csymbr
              apply (simp only: if_1_0_0 simp_thms)
              apply (rule ccorres_Cond_rhs_Seq[rotated])
               apply (rule_tac P="\<exists>s. s \<turnstile>' cteCap rv \<and> s \<turnstile>' cap" in ccorres_gen_asm)
               apply (clarsimp simp: word_unat.Abs_inject valid_cap_capZombieNumber_unats)
               apply (simp add: assertE_def)
               apply (rule ccorres_fail)
              apply (rule ccorres_rhs_assoc)+
              apply (rule ccorres_move_c_guard_cte)
              apply (rule_tac xf'=ret__unsigned_'
                          and val="case_zombie_type ZombieTCB_C of_nat (capZombieType (cteCap rv))"
                          and R="cte_wp_at' ((=) rv) slot and invs'"
                       in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
                 apply (rule conseqPre, vcg)
                 apply clarsimp
                 apply (erule(2) zombie_rf_sr_helperE)
                  apply simp
                 subgoal by clarsimp
                apply ceqv
               apply csymbr
               apply (simp only: if_1_0_0 simp_thms)
               apply (rule ccorres_Cond_rhs_Seq)
                apply (rule_tac P="\<exists>s. s \<turnstile>' cap \<and> s \<turnstile>' cteCap rv" in ccorres_gen_asm)
                apply (subgoal_tac "P" for P, subst if_P, assumption)
                 prefer 2
                 apply (clarsimp simp: word_unat.Abs_inject valid_cap_capZombieNumber_unats)
                 apply (drule valid_capAligned)+
                 apply (drule(4) case_zombie_type_map_inj)
                 apply simp
                apply (rule ccorres_rhs_assoc)+
                apply (simp del: Collect_const)
                apply (rule ccorres_move_c_guard_cte)
                apply (simp add: liftE_def bind_assoc del: Collect_const)
                apply (rule ccorres_symb_exec_l [OF _ getCTE_inv _ empty_fail_getCTE])
                 apply (rule ccorres_assert)
                 apply (rule_tac xf'=ret__struct_cap_C_'
                             and F="\<lambda>rv'. ccap_relation (capZombieNumber_update (\<lambda>x. x - 1) cap) rv'"
                             and R="cte_wp_at' ((=) rv) slot and invs'"
                          in ccorres_symb_exec_r_abstract_UNIV[where R'=UNIV])
                    apply (rule conseqPre, vcg)
                    apply clarsimp
                    apply (erule(2) zombie_rf_sr_helperE, simp)
                    apply clarsimp
                    apply (rule exI, rule conjI, assumption, clarsimp)
                    apply (rule ssubst, rule unat_minus_one)
                     apply (erule of_nat_neq_0)
                     apply (drule(1) valid_cap_capZombieNumber_unats)
                     subgoal by (simp add: unats_def)
                    apply (rule conjI)
                     apply (clarsimp simp: isCap_simps valid_cap'_def)
                     apply (erule order_trans[rotated])
                     apply (rule order_trans, rule diff_le_self)
                     subgoal by (simp add: unat_of_nat)
                    apply clarsimp
                    apply (erule_tac P="\<lambda>cap. ccap_relation cap cap'" for cap' in rsubst)
                    apply (clarsimp simp: isCap_simps capAligned_def)
                    apply (drule valid_cap_capZombieNumber_unats | simp)+
                    apply (simp add: word_unat.Abs_inverse)
                   apply ceqv
                  apply (rule ccorres_move_c_guard_cte)
                  apply (ctac(no_vcg) add: ccorres_updateCap)
                    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                    apply (rule allI, rule conseqPre, vcg)
                    apply (clarsimp simp: return_def)
                   apply wp
                  apply simp
                 apply (simp add: guard_is_UNIV_def Collect_const_mem)
                 apply (clarsimp simp: isCap_simps)
                apply wp
               apply (subst if_not_P)
                apply clarsimp
               apply (simp add: assertE_assert liftE_def)
               apply (rule ccorres_fail)
              apply (simp add: guard_is_UNIV_def)+
           apply (rule ccorres_fail)
          apply (simp add: guard_is_UNIV_def)
         apply (simp add: conj_comms)
         apply (wp getCTE_wp)
        apply simp
        apply (rule ccorres_split_throws)
         apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply (clarsimp simp: throwError_def return_def cintr_def)
        apply vcg
       apply (wp cutMon_validE_drop)
       apply (rule_tac Q'="\<lambda>rv. invs' and cte_at' slot and valid_cap' cap" in hoare_post_imp_R)
        apply (wp cteDelete_invs'')
       apply (clarsimp simp: cte_wp_at_ctes_of)
       apply (fastforce dest: ctes_of_valid')
      apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
      apply simp
     apply (simp add: guard_is_UNIV_def Collect_const_mem)
     apply (clarsimp simp: isCap_simps size_of_def cte_level_bits_def)
     apply (simp only: word_bits_def unat_of_nat unat_arith_simps, simp)
    apply (simp add: guard_is_UNIV_def)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: isCap_simps)
  apply (frule ctes_of_valid', clarsimp+)
  apply (frule valid_Zombie_number_word_bits, clarsimp+)
  apply (frule(1) ex_Zombie_to2, clarsimp+)
  apply (clarsimp simp: cte_level_bits_def)
  apply (frule_tac n="v2 - 1" in valid_Zombie_cte_at')
   apply (fastforce simp add: valid_cap'_def)
  apply (frule_tac n=0 in valid_Zombie_cte_at')
   apply (fastforce simp: valid_cap'_def)
  apply (clarsimp simp: cte_wp_at_ctes_of size_of_def objBits_defs)
  apply auto
  done

lemma induction_setup_helper:
  "\<lbrakk> \<And>s slot exposed. P s slot exposed \<Longrightarrow> Q s slot exposed;
     \<lbrakk> \<And>s slot exposed. P s slot exposed \<Longrightarrow> Q s slot exposed \<rbrakk>
            \<Longrightarrow> P s slot exposed \<rbrakk>
        \<Longrightarrow> Q s slot exposed"
  by auto

schematic_goal finaliseSlot_ccorres_induction_helper:
  "\<And>s slot exposed. ?P s slot exposed
        \<Longrightarrow> ccorres (cintr \<currency> (\<lambda>(success, irqopt) (success', irq'). success' = from_bool success \<and> ccap_relation irqopt irq' \<and> cleanup_info_wf' irqopt))
     (liftxf errstate finaliseSlot_ret_C.status_C (\<lambda>v. (success_C v, finaliseSlot_ret_C.cleanupInfo_C v))
                   ret__struct_finaliseSlot_ret_C_')
     (\<lambda>s. invs' s \<and> sch_act_simple s \<and> (exposed \<or> ex_cte_cap_to' slot s))
     (UNIV \<inter> {s. slot_' s = Ptr slot} \<inter> {s. immediate_' s = from_bool exposed}) []
     (cutMon ((=) s) (finaliseSlot slot exposed)) (Call finaliseSlot_'proc)"
  unfolding finaliseSlot_def
  apply (rule ccorres_Call)
   apply (rule finaliseSlot_impl[unfolded finaliseSlot_body_def])
  apply (unfold whileAnno_def)
  apply (cinitlift slot_' immediate_')
  apply safe
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_rhs_assoc)+
   apply csymbr+
   apply (rule_tac P="\<lambda>s. invs' s \<and> sch_act_simple s \<and> (exposed \<or> ex_cte_cap_to' slota s)"
               in ccorres_inst[where P'=UNIV])
   apply assumption
  apply simp
  done

lemma finaliseSlot_ccorres:
  notes from_bool_neq_0 [simp del]
  shows
  "ccorres (cintr \<currency> (\<lambda>(success, irqopt) (success', irq'). success' = from_bool success \<and> ccap_relation irqopt irq' \<and> cleanup_info_wf' irqopt))
     (liftxf errstate finaliseSlot_ret_C.status_C (\<lambda>v. (success_C v, finaliseSlot_ret_C.cleanupInfo_C v))
                   ret__struct_finaliseSlot_ret_C_')
     (\<lambda>s. invs' s \<and> sch_act_simple s \<and> (exposed \<or> ex_cte_cap_to' slot s))
     (UNIV \<inter> {s. slot_' s = Ptr slot} \<inter> {s. immediate_' s = from_bool exposed}) []
     (cutMon ((=) s) (finaliseSlot slot exposed)) (Call finaliseSlot_'proc)"
  apply (rule finaliseSlot_ccorres_induction_helper)
  apply (induct rule: finaliseSlot'.induct[where ?a0.0=slot and ?a1.0=exposed and ?a2.0=s])
  subgoal premises hyps for slot' expo s'
    apply (subst finaliseSlot'.simps)
    apply (fold cteDelete_def[unfolded finaliseSlot_def])
    apply (fold reduceZombie_def)
    apply (simp only: liftE_bindE cutMon_walk_bind
                      withoutPreemption_def fun_app_def)
    apply (rule ccorres_drop_cutMon_bind)
    apply (rule ccorres_symb_exec_l'
                   [OF _ getCTE_inv getCTE_sp empty_fail_getCTE])
    apply (rule ccorres_guard_imp2)
     apply (rule ccorres_move_c_guard_cte)
     apply (rule ccorres_cutMon, simp only: cutMon_walk_if)
     apply (rule ccorres_symb_exec_r)
       apply (rule iffD1 [OF ccorres_expand_while_iff_Seq])
       apply (rule_tac xf'=ret__unsigned_' in ccorres_abstract)
        apply ceqv
       apply (rule_tac P="(rv' = scast cap_null_cap) = (cteCap rv = NullCap)"
                    in ccorres_gen_asm2)
       apply (rule ccorres_if_lhs)
        apply (simp del: Collect_const add: Collect_True Collect_False
                                            ccorres_cond_iffs)
        apply (rule ccorres_drop_cutMon)
        apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: returnOk_def return_def ccap_relation_NullCap_iff)
       apply (simp add: Collect_True liftE_bindE split_def
                        ccorres_cond_iffs cutMon_walk_bind
                   del: Collect_const cong: call_ignore_cong)
       apply (rule ccorres_drop_cutMon_bind)
       apply (clarsimp simp only: from_bool_0)
       apply (rule ccorres_rhs_assoc)+
       apply (ctac(no_vcg) add: isFinalCapability_ccorres[where slot=slot'])
        apply (rule ccorres_cutMon, simp only: cutMon_walk_bind)
        apply (rule ccorres_drop_cutMon_bind)
        apply (rule ccorres_move_c_guard_cte)
        apply (rule_tac A="\<lambda>s. invs' s \<and> sch_act_simple s \<and> cte_wp_at' ((=) rv) slot' s
                                \<and> (expo \<or> ex_cte_cap_to' slot' s)
                                \<and> (final_matters' (cteCap rv) \<longrightarrow> rva = isFinal (cteCap rv) slot' (cteCaps_of s))"
                    and A'=UNIV
                     in ccorres_guard_imp2)
         apply (ctac(no_vcg) add: finaliseCap_ccorres)
          apply (rule ccorres_add_return)
          apply (rule_tac r'="\<lambda>rv rv'. rv' = from_bool (capRemovable (fst rvb) slot')"
                     and xf'=ret__unsigned_long_' in ccorres_split_nothrow_novcg)
              apply (rule_tac P="\<lambda>s. capAligned (fst rvb) \<and> (isZombie (fst rvb) \<or> fst rvb = NullCap)"
                           in ccorres_from_vcg[where P'=UNIV])
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: return_def)
              apply auto[1]
             apply ceqv
            apply (rule ccorres_cutMon)
            apply (simp add: cutMon_walk_if from_bool_0
                        del: Collect_const
                       cong: call_ignore_cong)
            apply (rule ccorres_if_lhs)
             apply simp
             apply (rule ccorres_drop_cutMon,
                    rule ccorres_split_throws)
              apply (rule_tac P="\<lambda>s. case (snd rvb) of
                                        IRQHandlerCap irq \<Rightarrow> UCAST(10\<rightarrow>machine_word_len) irq \<le> SCAST(32 signed\<rightarrow>machine_word_len) Kernel_C.maxIRQ
                                      | _ \<Rightarrow> True"
                              in ccorres_from_vcg_throws[where P'=UNIV])
              apply (rule allI, rule conseqPre, vcg)
              apply (clarsimp simp: returnOk_def return_def)
              apply (clarsimp simp: cleanup_info_wf'_def arch_cleanup_info_wf'_def
                             split: if_split capability.splits)
             apply vcg
            apply (simp only: cutMon_walk_if Collect_False ccorres_seq_cond_empty
                              ccorres_seq_skip)
            apply (rule ccorres_move_c_guard_cte)
            apply (rule ccorres_if_lhs)
             apply (simp only: cutMon_walk_bind withoutPreemption_def
                               liftE_bindE fun_app_def)
             apply (rule ccorres_drop_cutMon_bind,
                    rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
                 apply (rule ccorres_guard_imp2[where A=\<top> and A'=UNIV])
                  apply (rule ccorres_updateCap)
                 apply clarsimp
                apply (rule ceqv_refl)
               apply csymbr
               apply (simp only: if_1_0_0 simp_thms Collect_True
                                 ccorres_seq_cond_univ)
               apply (rule ccorres_rhs_assoc)+
               apply (rule ccorres_add_return,
                      rule_tac r'="\<lambda>rv rv'. rv' = from_bool True"
                          and xf'=ret__unsigned_long_' in ccorres_split_nothrow_novcg)
                   apply (rule_tac P="\<lambda>s. capAligned (fst rvb)"
                               in ccorres_from_vcg[where P'=UNIV])
                   apply (rule allI, rule conseqPre, vcg)
                   apply (clarsimp simp: return_def)
                   apply (auto simp: isCap_simps capCyclicZombie_def)[1]
                  apply ceqv
                 apply csymbr
                 apply (simp add: from_bool_0)
                 apply (rule ccorres_split_throws)
                  apply (rule ccorres_drop_cutMon,
                         rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                  apply (rule allI, rule conseqPre, vcg)
                  apply (clarsimp simp: returnOk_def return_def)
                  apply (drule use_valid [OF _ finaliseCap_cases, OF _ TrueI])
                  apply (simp add: irq_opt_relation_def
                            split: if_split_asm)
                 apply vcg
                apply wp
               apply (simp add: guard_is_UNIV_def)
              apply wp
             apply (simp add: guard_is_UNIV_def)
            apply (simp only: liftE_bindE cutMon_walk_bind Let_def
                              withoutPreemption_def fun_app_def
                              split_def K_bind_def fst_conv snd_conv)
            apply (rule ccorres_drop_cutMon_bind,
                   rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
                apply (rule ccorres_guard_imp2[where A=\<top> and A'=UNIV])
                 apply (rule ccorres_updateCap)
                apply clarsimp
               apply (rule ceqv_refl)
              apply (subgoal_tac "isZombie (fst rvb)")
               prefer 2
               apply (drule use_valid [OF _ finaliseCap_cases, OF _ TrueI])
               apply (auto simp add: capRemovable_def)[1]
              apply (rule ccorres_cutMon, simp only: cutMon_walk_bindE cutMon_walk_if)
              apply (rule ccorres_rhs_assoc2)
              apply (rule ccorres_add_return,
                     rule_tac r'="\<lambda>rv rv'. rv' = from_bool False"
                         and xf'=ret__int_' in ccorres_split_nothrow_novcg)
                  apply (rule_tac P="\<lambda>s. capAligned (fst rvb)"
                               in ccorres_from_vcg[where P'=UNIV])
                  apply (rule allI, rule conseqPre, vcg)
                  apply (clarsimp simp: return_def)
                  apply fastforce
                 apply ceqv
                apply (simp only: from_bool_0 simp_thms Collect_False
                                  ccorres_seq_cond_empty ccorres_seq_skip)
                apply (ctac (no_vcg, no_simp) add: reduceZombie_ccorres1)
                    apply (rule ccorres_guard_imp2)
                     apply (rule finaliseSlot_ccorres_induction_helper)
                     apply (rule hyps(1), (simp add: in_monad | rule conjI refl)+)[1]
                    apply simp
                   apply assumption
                  apply (rule ccorres_cutMon)
                  apply (simp only: cutMon_walk_bindE id_apply simp_thms
                                    Collect_False ccorres_seq_cond_empty
                                    ccorres_seq_skip)
                  apply (rule ccorres_drop_cutMon_bindE)
                  apply (ctac(no_vcg) add: preemptionPoint_ccorres)
                    apply (rule ccorres_cutMon)
                    apply (simp only: id_apply simp_thms
                                      Collect_False ccorres_seq_cond_empty
                                      ccorres_seq_skip)
                    apply (rule rsubst[where P="ccorres r xf' P P' hs a" for r xf' P P' hs a])
                    apply (rule hyps[folded reduceZombie_def[unfolded cteDelete_def finaliseSlot_def],
                                         unfolded split_def, unfolded K_def],
                           (simp add: in_monad)+)
                    apply (simp add: from_bool_0)
                   apply simp
                   apply (rule ccorres_split_throws)
                    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                    apply (rule allI, rule conseqPre, vcg)
                    apply (clarsimp simp: throwError_def return_def cintr_def)
                   apply vcg
                  apply (wp preemptionPoint_invR)
                 apply simp
                 apply simp
                 apply (rule ccorres_split_throws)
                  apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
                  apply (rule allI, rule conseqPre, vcg)
                  apply (clarsimp simp: throwError_def return_def cintr_def)
                 apply vcg
                apply (wp cutMon_validE_drop reduceZombie_invs reduceZombie_sch_act_simple)
                apply (wp reduceZombie_cap_to[simplified imp_conv_disj, simplified])+
               apply (simp add: guard_is_UNIV_def)
              apply (simp add: conj_comms)
              apply (wp make_zombie_invs' updateCap_cte_wp_at_cases
                        updateCap_cap_to' hoare_vcg_disj_lift static_imp_wp)+
            apply (simp add: guard_is_UNIV_def)
           apply wp
          apply (simp add: guard_is_UNIV_def)
         apply (rule hoare_strengthen_post)
          apply (rule_tac Q="\<lambda>fin s. invs' s \<and> sch_act_simple s \<and> s \<turnstile>' (fst fin)
                                   \<and> (expo \<or> ex_cte_cap_to' slot' s)
                                   \<and> cte_wp_at' (\<lambda>cte. cteCap cte = cteCap rv) slot' s"
                     in hoare_vcg_conj_lift)
           apply (wp hoare_vcg_disj_lift finaliseCap_invs[where sl=slot'])[1]
          apply (rule hoare_vcg_conj_lift)
           apply (rule finaliseCap_cte_refs)
          apply (rule finaliseCap_replaceable[where slot=slot'])
         apply (clarsimp simp: cte_wp_at_ctes_of)
         apply (erule disjE[where P="F \<and> G" for F G])
          apply (clarsimp simp: capRemovable_def cte_wp_at_ctes_of cap_has_cleanup'_def
                         split: option.split capability.splits)
          apply (auto dest!: ctes_of_valid'
                       simp: valid_cap'_def Kernel_C.maxIRQ_def ARM_HYP.maxIRQ_def
                             unat_ucast word_le_nat_alt)[1]
         apply (clarsimp dest!: isCapDs)
         subgoal by (auto dest!: valid_capAligned ctes_of_valid'
                      simp: isCap_simps final_matters'_def o_def)
        apply clarsimp
        apply (frule valid_globals_cte_wpD'[rotated], clarsimp)
        apply (clarsimp simp: cte_wp_at_ctes_of)
        apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
        apply (frule valid_global_refsD_with_objSize, clarsimp)
        apply (auto simp: typ_heap_simps dest!: ccte_relation_ccap_relation)[1]
       apply (wp isFinalCapability_inv static_imp_wp | wp (once) isFinal[where x=slot'])+
      apply vcg
     apply (rule conseqPre, vcg)
     apply clarsimp
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (rule conjI, (auto)[1])
    apply clarsimp
    apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
    apply (clarsimp simp: typ_heap_simps cap_get_tag_isCap
                   dest!: ccte_relation_ccap_relation)
    done
  done

lemma ccorres_use_cutMon:
  "(\<And>s. ccorres rvr xf P P' hs (cutMon ((=) s) f) g)
       \<Longrightarrow> ccorres rvr xf P P' hs f g"
  apply (simp add: ccorres_underlying_def
                   snd_cutMon)
  apply (simp add: cutMon_def cong: xstate.case_cong)
  apply blast
  done

lemmas cteDelete_ccorres2 = cteDelete_ccorres1 [OF finaliseSlot_ccorres]
lemmas cteDelete_ccorres = ccorres_use_cutMon [OF cteDelete_ccorres2]

lemma cteRevoke_ccorres1:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and sch_act_simple) (UNIV \<inter> {s. slot_' s = cte_Ptr slot}) []
     (cutMon ((=) s) (cteRevoke slot)) (Call cteRevoke_'proc)"
  apply (cinit' lift: slot_' simp: whileAnno_def)
   apply simp
   apply (rule ccorres_inst[where P="invs' and sch_act_simple" and P'=UNIV])
   prefer 2
   apply simp
  apply (induct rule: cteRevoke.induct[where ?a0.0=slot and ?a1.0=s])
  subgoal premises hyps for slot' s'
    apply (rule ccorres_guard_imp2)
     apply (subst cteRevoke.simps[abs_def])
     apply (simp add: liftE_bindE cutMon_walk_bind
                 del: Collect_const)
     apply (rule ccorres_drop_cutMon_bind)
     apply (rule ccorres_symb_exec_l'
                       [OF _ getCTE_inv _ empty_fail_getCTE])
      apply (rule ccorres_move_c_guard_cte)
      apply (rule_tac xf'=ret__unsigned_' and val="mdbNext (cteMDBNode rv)"
                    and R="cte_wp_at' ((=) rv) slot'"
                     in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
         apply vcg
         apply (clarsimp simp: cte_wp_at_ctes_of)
         apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
         apply (simp add: typ_heap_simps)
         apply (clarsimp simp: ccte_relation_def map_option_Some_eq2)
        apply ceqv
       apply (rule ccorres_rhs_assoc2)+
       apply (rule iffD1 [OF ccorres_expand_while_iff_Seq2])
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply csymbr
       apply (simp only: if_1_0_0 simp_thms unlessE_def)
       apply (rule ccorres_Cond_rhs_Seq[rotated])
        apply simp
        apply (rule ccorres_cond_false)
        apply (rule ccorres_drop_cutMon)
        apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: returnOk_def return_def)
       apply (rule ccorres_cutMon, simp only: cutMon_walk_if cutMon_walk_bind)
       apply (rule ccorres_if_lhs)
        apply (rule ccorres_False[where P'=UNIV])
       apply (rule ccorres_drop_cutMon_bind)
       apply (rule ccorres_pre_getCTE)
       apply (rule ccorres_rhs_assoc)+
       apply (rule_tac xf'="ret__unsigned_long_'"
                      and val="from_bool (isMDBParentOf rv rva)"
                      and R="cte_wp_at' ((=) rv) slot' and invs'
                               and cte_wp_at' ((=) rva) (mdbNext (cteMDBNode rv))"
                       in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
          apply vcg
          apply (clarsimp simp: cte_wp_at_ctes_of)
          apply (frule_tac p="slot'" in ctes_of_valid', clarsimp)
          apply (frule_tac p="mdbNext m" for m in ctes_of_valid', clarsimp)
          apply (drule(1) rf_sr_ctes_of_clift[rotated])+
          apply (clarsimp simp: ccte_relation_def)
          apply (auto intro: valid_capAligned)[1]
         apply ceqv
        apply csymbr
        apply (rule ccorres_cutMon)
        apply (simp add: whenE_def cutMon_walk_if cutMon_walk_bindE
                         from_bool_0 if_1_0_0
                    del: Collect_const cong: if_cong call_ignore_cong)
        apply (rule ccorres_if_lhs)
         apply (rule ccorres_cond_true)
         apply (rule ccorres_drop_cutMon_bindE)
         apply (rule ccorres_rhs_assoc)+
         apply (ctac(no_vcg) add: cteDelete_ccorres)
           apply (simp del: Collect_const add: Collect_False ccorres_cond_iffs
                                               dc_def[symmetric])
           apply (rule ccorres_cutMon, simp only: cutMon_walk_bindE)
           apply (rule ccorres_drop_cutMon_bindE)
           apply (ctac(no_vcg) add: preemptionPoint_ccorres)
             apply (simp del: Collect_const add: Collect_False ccorres_cond_iffs
                                                 dc_def[symmetric])
             apply (rule ccorres_cutMon)
             apply (rule rsubst[where P="ccorres r xf' P P' hs a" for r xf' P P' hs a])
              apply (rule hyps[unfolded K_def],
                     (fastforce simp: in_monad)+)[1]
             apply simp
            apply (simp, rule ccorres_split_throws)
             apply (rule ccorres_return_C_errorE, simp+)[1]
            apply vcg
           apply (wp preemptionPoint_invR)
            apply simp
           apply simp
          apply (simp, rule ccorres_split_throws)
           apply (rule ccorres_return_C_errorE, simp+)[1]
          apply vcg
         apply (wp cteDelete_invs' cteDelete_sch_act_simple)
        apply (rule ccorres_cond_false)
        apply (rule ccorres_drop_cutMon)
        apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
        apply (rule allI, rule conseqPre, vcg)
        apply (clarsimp simp: returnOk_def return_def)
       apply (simp add: guard_is_UNIV_def cintr_def Collect_const_mem exception_defs)
      apply (simp add: guard_is_UNIV_def)
     apply (rule getCTE_wp)
    apply (clarsimp simp: cte_wp_at_ctes_of nullPointer_def)
    apply (drule invs_mdb')
    apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def valid_nullcaps_def)
    apply (case_tac cte, clarsimp)
    apply (fastforce simp: nullMDBNode_def)
    done
  done

lemmas cteRevoke_ccorres = ccorres_use_cutMon [OF cteRevoke_ccorres1]

end

end
