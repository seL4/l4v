(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory CSpace_RAB_C
imports CSpaceAcc_C "CLib.MonadicRewrite_C"
begin

context kernel
begin

abbreviation
  "rab_xf \<equiv> (liftxf errstate resolveAddressBits_ret_C.status_C
              (\<lambda>v. (resolveAddressBits_ret_C.slot_C v, bitsRemaining_C v))
              ret__struct_resolveAddressBits_ret_C_')"

lemma rab_failure_case_ccorres:
  assumes spec: "\<Gamma>\<turnstile> G' call_part {s. resolveAddressBits_ret_C.status_C v \<noteq> scast EXCEPTION_NONE
                                      \<and> lookup_failure_rel e (resolveAddressBits_ret_C.status_C v)
                                                           (errstate s)}"
  assumes mod:  "\<And>s. \<Gamma>\<turnstile> {s'. (s, s') \<in> rf_sr} call_part {s'. (s, s') \<in> rf_sr}"
  shows "ccorres (lookup_failure_rel \<currency> r) rab_xf \<top> G' (SKIP # hs)
   (throwError e)
   (call_part ;;
    \<acute>ret___struct_resolveAddressBits_ret_C :== v;;
    return_C ret__struct_resolveAddressBits_ret_C_'_update ret___struct_resolveAddressBits_ret_C_')"
  apply (rule ccorres_rhs_assoc)+
  apply (rule ccorres_symb_exec_r [where R=\<top>, OF _ spec])
   apply (rule ccorres_from_vcg_throws)
   apply (simp add: throwError_def return_def)
   apply (rule allI)
   apply (rule conseqPre)
   apply vcg
   apply (auto simp add: exception_defs errstate_def)[1]
  apply (rule conseqPre [OF mod])
  apply clarsimp
  done

lemma not_snd_bindE_I1:
  "\<not> snd ((a >>=E b) s) \<Longrightarrow> \<not> snd (a s)"
  unfolding bindE_def
  by (erule not_snd_bindI1)

declare isCNodeCap_CNodeCap[simp]

(* MOVE *)
lemma ccorres_gen_asm_state:
  assumes rl: "\<And>s. P s \<Longrightarrow> ccorres r xf G G' hs a c"
  shows "ccorres r xf (G and P) G' hs a c"
proof (rule ccorres_guard_imp2)
  show "ccorres r xf (G and (\<lambda>_. \<exists>s. P s)) G' hs a c"
    apply (rule ccorres_gen_asm)
    apply (erule exE)
    apply (erule rl)
    done
next
  fix s s'
  assume "(s, s') \<in> rf_sr" and "(G and P) s" and "s' \<in> G'"
  thus "(G and (\<lambda>_. \<exists>s. P s)) s \<and> s' \<in> G'"
    by (clarsimp elim!: exI)
qed

(* MOVE, generalise *)
lemma ccorres_req:
  assumes rl: "\<And>s s'. \<lbrakk> (s, s') \<in> rf_sr; Q s; Q' s' \<rbrakk> \<Longrightarrow> F s s'"
  and     cc: "\<And>s s'. F s s' \<Longrightarrow> ccorres r xf P P'  hs a c"
  shows   "ccorres r xf (P and Q) (P' \<inter> Collect Q') hs a c"
  apply (rule ccorresI')
  apply clarsimp
  apply (frule (2) rl)
  apply (erule (5) ccorresE [OF cc])
  apply (clarsimp elim!: bexI [rotated])
  done

declare ucast_id [simp]
declare resolveAddressBits.simps [simp del]

lemma rightsFromWord_wordFromRights:
  "rightsFromWord (wordFromRights rghts) = rghts"
  apply (cases rghts)
  apply (simp add: wordFromRights_def rightsFromWord_def
            split: if_split)
  done

lemma wordFromRights_inj:
  "inj wordFromRights"
  by (rule inj_on_inverseI, rule rightsFromWord_wordFromRights)

lemma ccorres_locateSlotCap_push:
  "ccorres_underlying sr \<Gamma> r xf ar axf P P' hs
    (a >>=E (\<lambda>x. locateSlotCap cp n >>= (\<lambda>p. b p x))) c
    \<Longrightarrow> (\<And>P. \<lbrace>P\<rbrace> a \<lbrace>\<lambda>_. P\<rbrace>, - )
    \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf ar axf P P' hs
    (locateSlotCap cp n >>= (\<lambda>p. a >>=E (\<lambda>x. b p x))) c"
  apply (simp add: locateSlot_conv)
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_stateAssert)
   apply (erule monadic_rewrite_ccorres_assemble)
   apply (rule monadic_rewrite_bindE[OF monadic_rewrite_refl])
    apply (rule monadic_rewrite_transverse)
     apply (rule monadic_rewrite_bind_head)
     apply (rule monadic_rewrite_stateAssert)
    apply simp
    apply (rule monadic_rewrite_refl)
   apply assumption
  apply simp
  done

declare Kernel_C.cte_C_size[simp del]

lemma resolveAddressBits_ccorres [corres]:
  shows "ccorres (lookup_failure_rel \<currency>
    (\<lambda>(cte, bits) (cte', bits'). cte' = Ptr cte \<and> bits = unat bits' \<and> bits'\<le> 32)) rab_xf
  (valid_pspace' and valid_cap' cap'
        and K (guard' \<le> 32))
  ({s. ccap_relation cap' (nodeCap_' s)} \<inter>
  {s. capptr_' s = cptr'} \<inter> {s. unat (n_bits_' s) = guard'}) []
  (resolveAddressBits cap' cptr' guard') (Call resolveAddressBits_'proc)"
  (is "ccorres ?rvr rab_xf ?P ?P' [] ?rab ?rab'")
proof (cases "isCNodeCap cap'")
  case False

  note Collect_const [simp del]

  show ?thesis using False
    apply (cinit' lift: nodeCap_' capptr_' n_bits_')
    apply csymbr+
      \<comment> \<open>Exception stuff\<close>
    apply (rule ccorres_split_throws)
    apply (simp add: Collect_const cap_get_tag_isCap isCap_simps ccorres_cond_iffs
                     resolveAddressBits.simps scast_id)
    apply (rule ccorres_from_vcg_throws [where P = \<top> and P' = UNIV])
    apply (rule allI)
    apply (rule conseqPre)
    apply (simp add: throwError_def return_def split)
    apply vcg
    apply (clarsimp simp add: exception_defs lookup_fault_lift_def)
    apply (simp split: if_split)
    apply (vcg strip_guards=true)
    apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
    done
next
  case True

  note word_neq_0_conv [simp del]

  from True show ?thesis
    apply -
    apply (cinit' simp add: whileAnno_def ucast_id)
    \<comment> \<open>This is done here as init lift usually throws away the relationship between nodeCap_' s and nodeCap.  Normally
      this OK, but the induction messes with everything :(\<close>
     apply (rule ccorres_abstract [where xf' = nodeCap_'])
      apply ceqv
     apply (rename_tac "nodeCap")
     apply (rule ccorres_abstract [where xf' = n_bits_'])
      apply ceqv
     apply (rename_tac "n_bits")
     apply (rule ccorres_abstract [where xf' = capptr_'])
      apply ceqv
     apply (rename_tac "capptr")
     apply (rule_tac P = "capptr = cptr' \<and> ccap_relation cap' nodeCap" in ccorres_gen_asm2)
     apply (erule conjE)
     apply (erule_tac t = capptr in ssubst)
     apply csymbr+
     apply (simp add: cap_get_tag_isCap split del: if_split)
     apply (thin_tac "ret__unsigned = X" for X)
     apply (rule ccorres_split_throws [where P = "?P"])
      apply (rule_tac P'="{s. nodeCap_' s = nodeCap} \<inter> {s. unat (n_bits_' s) = guard'}"
               in ccorres_inst)
      apply (rule_tac r' = "?rvr" in
          ccorres_rel_imp [where xf' = rab_xf])
       defer
       apply (case_tac x)
        apply clarsimp
       apply clarsimp
      apply (rule_tac I = "{s. cap_get_tag (nodeCap_' s) = scast cap_cnode_cap}"
         in HoarePartial.While [unfolded whileAnno_def, OF subset_refl])
       apply (vcg strip_guards=true) \<comment> \<open>takes a while\<close>
       apply clarsimp
      apply simp
     apply (clarsimp simp: cap_get_tag_isCap)
  \<comment> \<open>Main thm\<close>
  proof (induct cap' cptr' guard' rule: resolveAddressBits.induct [case_names ind])
    case (ind cap cptr guard)

    note conj_refl = conjI [OF refl refl]
    have imp_rem: "\<And>P X. P \<Longrightarrow> P \<and> (P \<longrightarrow> X = X)" by clarsimp
    have imp_rem': "\<And>P R X. P \<and> R \<Longrightarrow> P \<and> R \<and> (P \<and> R \<longrightarrow> X = X)" by clarsimp
    note conj_refl_r = conjI [OF _ refl]

    have getSlotCap_in_monad:
      "\<And>a b p rs s. ((a, b) \<in> fst (getSlotCap p s)) =
      (option_map cteCap (ctes_of s p) = Some a
       \<and> b = s)"
      apply (simp add: getSlotCap_def return_def bind_def objBits_simps split_def)
      apply rule
       apply (clarsimp simp: in_getCTE_cte_wp_at' cte_wp_at_ctes_of)
      apply clarsimp
      apply (rename_tac s p z)
      apply (subgoal_tac "cte_wp_at' ((=) z) p s")
       apply (clarsimp simp: getCTE_def cte_wp_at'_def)
      apply (simp add: cte_wp_at_ctes_of)
      done

    note ih = ind.hyps[simplified, simplified in_monad
        getSlotCap_in_monad locateSlot_conv stateAssert_def, simplified]

    have gsCNodes: "\<And>s bits p x P Q. bits = capCNodeBits cap \<Longrightarrow> capCNodeBits cap < 32 \<Longrightarrow>
        (case gsCNodes (s \<lparr> gsCNodes := [p \<mapsto> bits ] \<rparr>) p of None \<Rightarrow> False
            | Some n \<Rightarrow> ((n = capCNodeBits cap \<or> Q n))
                \<and> (x && mask bits :: word32) < 2 ^ n) \<or> P"
      by (clarsimp simp: word_size and_mask_less_size)

    have case_into_if:
      "\<And>c f g. (case c of CNodeCap _ _ _ _ \<Rightarrow> f | _ \<Rightarrow> g) = (if isCNodeCap c then f else g)"
      by (case_tac c, simp_all add: isCap_simps)

    note [split del] = if_split

    have gbD: "\<And>guardBits cap cap'. \<lbrakk> guardBits = capCNodeGuardSize_CL (cap_cnode_cap_lift cap');
                       ccap_relation cap cap'; isCNodeCap cap \<rbrakk>
           \<Longrightarrow> unat guardBits = capCNodeGuardSize cap \<and> capCNodeGuardSize cap < 32"
       apply (simp add: cap_get_tag_isCap[symmetric])
       apply (frule(1) cap_get_tag_CNodeCap [THEN iffD1])
       apply simp
       apply (simp add: cap_cnode_cap_lift_def cap_lift_cnode_cap)
       apply (rule order_le_less_trans, rule word_le_nat_alt[THEN iffD1],
              rule word_and_le1)
       apply (simp add: mask_def)
       done

    have cgD: "\<And>capGuard cap cap'. \<lbrakk> capGuard = capCNodeGuard_CL (cap_cnode_cap_lift cap');
        ccap_relation cap cap'; isCNodeCap cap \<rbrakk> \<Longrightarrow> capGuard = capCNodeGuard cap"
      apply (frule cap_get_tag_CNodeCap [THEN iffD1])
      apply (simp add: cap_get_tag_isCap)
      apply simp
      done

    have rbD: "\<And>radixBits cap cap'. \<lbrakk> radixBits = capCNodeRadix_CL (cap_cnode_cap_lift cap');
                       ccap_relation cap cap'; isCNodeCap cap \<rbrakk>
          \<Longrightarrow> unat radixBits = capCNodeBits cap \<and> capCNodeBits cap < 32"
       apply (simp add: cap_get_tag_isCap[symmetric])
       apply (frule(1) cap_get_tag_CNodeCap [THEN iffD1])
       apply simp
       apply (simp add: cap_cnode_cap_lift_def cap_lift_cnode_cap)
       apply (rule order_le_less_trans, rule word_le_nat_alt[THEN iffD1],
              rule word_and_le1)
       apply (simp add: mask_def)
       done

    have rxgd:
       "\<And>cap cap'. \<lbrakk> ccap_relation cap cap'; isCNodeCap cap \<rbrakk>
          \<Longrightarrow> unat (capCNodeRadix_CL (cap_cnode_cap_lift cap')
                      + capCNodeGuardSize_CL (cap_cnode_cap_lift cap'))
              = unat (capCNodeRadix_CL (cap_cnode_cap_lift cap'))
                      + unat (capCNodeGuardSize_CL (cap_cnode_cap_lift cap'))"
       apply (simp add: cap_get_tag_isCap[symmetric])
       apply (frule(1) cap_get_tag_CNodeCap [THEN iffD1])
       apply (simp add: cap_cnode_cap_lift_def cap_lift_cnode_cap)
       apply (subst unat_plus_simple[symmetric], subst no_olen_add_nat)
       apply (rule order_le_less_trans, rule add_le_mono)
         apply (rule word_le_nat_alt[THEN iffD1], rule word_and_le1)+
       apply (simp add: mask_def)
       done

    (* Move outside this context? *)
    note cap_simps = rxgd cgD [OF refl]
      rbD [OF refl, THEN conjunct1] rbD [OF refl, THEN conjunct2]
      gbD [OF refl, THEN conjunct1] gbD [OF refl, THEN conjunct2]

    have cond1: "\<And>(nb :: word32) guardBits capGuard.
       \<lbrakk>unat nb = guard; unat guardBits = capCNodeGuardSize cap; capGuard = capCNodeGuard cap;
        guard \<le> 32\<rbrakk>
       \<Longrightarrow> \<forall>s s'.
             (s, s') \<in> rf_sr \<and> True \<and> True \<longrightarrow>
             (\<not> (capCNodeGuardSize cap \<le> guard \<and>
                 (cptr >> guard - capCNodeGuardSize cap) &&
                 mask (capCNodeGuardSize cap) =
                 capCNodeGuard cap)) =
             (s' \<in> \<lbrace>nb < guardBits \<or>
                    (cptr >> unat (nb - guardBits && 0x1F)) &&
                    2 ^ unat guardBits - 1 \<noteq>  capGuard\<rbrace>)"
      apply (subst not_le [symmetric])
      apply (clarsimp simp: mask_def unat_of_nat Collect_const_mem)
      apply (cases "capCNodeGuardSize cap = 0")
       apply (simp add: word_le_nat_alt)
      apply (subgoal_tac "(0x1F :: word32) = mask 5")
       apply (erule ssubst [where t = "0x1F"])
       apply (simp add: less_mask_eq word_less_nat_alt word_le_nat_alt)
       apply (subst imp_cong)
         apply (rule refl)
        prefer 2
        apply (rule refl)
       apply (subst less_mask_eq)
        apply (simp add: word_less_nat_alt word_le_nat_alt unat_sub)
       apply (simp add: word_less_nat_alt word_le_nat_alt unat_sub)
      apply (simp add: mask_def)
      done

    have cond2: "\<And>nb (radixBits :: word32) (guardBits :: word32).
      \<lbrakk> unat nb = guard; unat radixBits = capCNodeBits cap; capCNodeBits cap < 32; capCNodeGuardSize cap < 32;
      unat guardBits = capCNodeGuardSize cap \<rbrakk> \<Longrightarrow>
      \<forall>s s'. (s, s') \<in> rf_sr \<and> True \<and> True \<longrightarrow>
                (guard < capCNodeBits cap + capCNodeGuardSize cap) = (s' \<in> \<lbrace>nb < radixBits + guardBits\<rbrace>)"
      by (simp add: Collect_const_mem word_less_nat_alt unat_word_ariths)

    have cond3: "\<And>nb (radixBits :: word32) (guardBits :: word32).
      \<lbrakk> unat nb = guard; unat radixBits = capCNodeBits cap; capCNodeBits cap < 32; capCNodeGuardSize cap < 32;
      unat guardBits = capCNodeGuardSize cap;
      \<not> guard < capCNodeBits cap + capCNodeGuardSize cap \<rbrakk> \<Longrightarrow>
      \<forall>s s'. (s, s') \<in> rf_sr \<and> True \<and> True \<longrightarrow>
                (guard = capCNodeBits cap + capCNodeGuardSize cap) = (s' \<in> \<lbrace>nb = radixBits + guardBits\<rbrace>)"
      by clarsimp unat_arith

    have cond4:
      "\<And>rva nodeCapb ret__unsigned_long.
      \<lbrakk> ccap_relation rva nodeCapb; ret__unsigned_long = cap_get_tag nodeCapb\<rbrakk>
       \<Longrightarrow> \<forall>s s'. (s, s') \<in> rf_sr \<and> True \<and> True \<longrightarrow> (\<not> isCNodeCap rva) = (s' \<in> \<lbrace>ret__unsigned_long \<noteq> scast cap_cnode_cap\<rbrace>)"
      by (simp add: cap_get_tag_isCap Collect_const_mem)

    let ?p = "(capCNodePtr cap + 0x10 * ((cptr >> guard - (capCNodeBits cap + capCNodeGuardSize cap)) &&
                                            mask (capCNodeBits cap)))"

    have n_bits_guard: "\<And>nb :: word32. \<lbrakk> guard \<le> 32; unat nb = guard \<rbrakk> \<Longrightarrow> unat (nb && mask 6) = guard"
      apply (subgoal_tac "nb \<le> 32")
      apply (clarsimp)
      apply (rule less_mask_eq)
      apply (erule order_le_less_trans)
      apply simp
      apply (simp add: word_le_nat_alt)
      done

    have mask6_eqs:
      "\<And>cap ccap. \<lbrakk> ccap_relation cap ccap; isCNodeCap cap \<rbrakk>
             \<Longrightarrow> (capCNodeRadix_CL (cap_cnode_cap_lift ccap) + capCNodeGuardSize_CL (cap_cnode_cap_lift ccap)) && mask 6
                 = capCNodeRadix_CL (cap_cnode_cap_lift ccap) + capCNodeGuardSize_CL (cap_cnode_cap_lift ccap)"
      "\<And>cap ccap. \<lbrakk> ccap_relation cap ccap; isCNodeCap cap \<rbrakk>
             \<Longrightarrow> capCNodeRadix_CL (cap_cnode_cap_lift ccap) && mask 6 = capCNodeRadix_CL (cap_cnode_cap_lift ccap)"
      "\<And>cap ccap. \<lbrakk> ccap_relation cap ccap; isCNodeCap cap \<rbrakk>
             \<Longrightarrow> capCNodeGuardSize_CL (cap_cnode_cap_lift ccap) && mask 6 = capCNodeGuardSize_CL (cap_cnode_cap_lift ccap)"
      apply (frule(1) rxgd)
      defer
      apply (simp_all add: cap_cnode_cap_lift_def cap_get_tag_isCap[symmetric]
                           cap_lift_cnode_cap)
        apply (rule less_mask_eq
                 | rule order_le_less_trans, (rule word_and_le1)+
                 | simp add: mask_def)+
      apply (simp add: word_less_nat_alt)
      apply (rule order_le_less_trans, rule add_le_mono)
        apply (rule word_le_nat_alt[THEN iffD1], rule word_and_le1)+
      apply simp
      done

    have gm: "\<And>(nb :: word32) cap cap'. \<lbrakk> unat nb = guard; ccap_relation cap cap'; isCNodeCap cap \<rbrakk>
                \<Longrightarrow> nb \<ge> capCNodeRadix_CL (cap_cnode_cap_lift cap') +
                       capCNodeGuardSize_CL (cap_cnode_cap_lift cap')
                     \<longrightarrow> unat (nb -
               (capCNodeRadix_CL (cap_cnode_cap_lift cap') +
                capCNodeGuardSize_CL (cap_cnode_cap_lift cap')))
                    = guard - (capCNodeBits cap + capCNodeGuardSize cap)"
      apply (simp add: unat_sub)
      apply (subst unat_plus_simple[THEN iffD1])
       apply (subst no_olen_add_nat)
       apply (simp add: cap_lift_cnode_cap cap_cnode_cap_lift_def
                        cap_get_tag_isCap[symmetric] mask_def)
       apply (rule order_le_less_trans, rule add_le_mono)
         apply (rule word_le_nat_alt[THEN iffD1], rule word_and_le1)+
       apply simp
      apply (simp add: cap_simps)
      done

    note if_cong[cong]
    show ?case
      using ind.prems
      supply option.case_cong[cong]
      apply -
      apply (rule iffD1 [OF ccorres_expand_while_iff])
      apply (subst resolveAddressBits.simps)
      apply (unfold case_into_if)
      apply (simp add: Let_def ccorres_cond_iffs split del: if_split)
      apply (rule ccorres_rhs_assoc)+
      apply (cinitlift nodeCap_' n_bits_')
      apply (erule_tac t = nodeCapa in ssubst)
      apply (rule ccorres_guard_imp2)
       apply (rule ccorres_gen_asm [where P="0 < capCNodeBits cap \<or> 0 < capCNodeGuardSize cap"])
       apply (rule ccorres_assertE)
       apply (csymbr | rule iffD2 [OF ccorres_seq_skip])+
       apply (rule ccorres_Guard_Seq)+
       apply csymbr
       \<comment> \<open>handle the stateAssert in locateSlotCap very carefully\<close>
       apply (simp(no_asm) only: liftE_bindE[where a="locateSlotCap a b" for a b])
       apply (rule ccorres_locateSlotCap_push[rotated])
        apply (simp add: unlessE_def)
        apply (rule hoare_pre, wp, simp)
       \<comment> \<open>Convert guardBits, radixBits and capGuard to their Haskell versions\<close>
       apply (drule (2) cgD, drule (2) rbD, drule (2) gbD)
       apply (elim conjE)
       apply (rule ccorres_gen_asm [where P = "guard \<le> 32"])
       apply (rule ccorres_split_unless_throwError_cond [OF cond1], assumption+)
         apply (rule rab_failure_case_ccorres, vcg, rule conseqPre, vcg)
         apply clarsimp
        apply (rule ccorres_locateSlotCap_push[rotated])
         apply (rule hoare_pre, wp whenE_throwError_wp, simp)
        apply (rule ccorres_split_when_throwError_cond [OF cond2], assumption+)
          apply (rule rab_failure_case_ccorres, vcg, rule conseqPre, vcg)
          apply clarsimp
         apply (rule ccorres_Guard_Seq)+
         apply csymbr
         apply csymbr
         apply (simp only: locateSlotCap_def Let_def if_True)
         apply (rule ccorres_split_nothrow)
             apply (rule locateSlotCNode_ccorres[where xf="slot_'" and xfu="slot_'_update"],
                    simp+)[1]
            apply ceqv
           apply (rename_tac rv slot)
           apply (erule_tac t = slot in ssubst)
           apply (simp del: Collect_const)
           apply (rule ccorres_if_cond_throws [OF cond3], assumption+)
             apply (rule ccorres_rhs_assoc)+
             apply csymbr+
             apply (rule ccorres_return_CE, simp_all)[1]
            apply (rule ccorres_Guard_Seq)
            apply (rule ccorres_basic_srnoop2, simp)
            apply csymbr
            apply (ctac pre: ccorres_liftE_Seq)
              apply (rename_tac rva nodeCapa)
              apply csymbr
              apply (rule ccorres_if_cond_throws2 [OF cond4], assumption+)
                apply (rule ccorres_rhs_assoc)+
                apply csymbr+
                apply (rule ccorres_return_CE, simp_all)[1]
               apply (frule_tac v1 = rva in iffD1 [OF isCap_simps(4)])
               apply (elim exE)
               apply (rule_tac
                    Q = "\<lambda>s. option_map cteCap (ctes_of s ?p) = Some rva"
                    and F = "\<lambda>s s'.
                    (option_map cteCap (ctes_of s ?p) = Some rva
                    \<and> (ccap_relation rva (h_val (hrs_mem (t_hrs_' (globals s'))) (Ptr &(Ptr ?p :: cte_C ptr\<rightarrow>[''cap_C'']) :: cap_C ptr))))"
                    in ccorres_req [where Q' = "\<lambda>s'. s' \<Turnstile>\<^sub>c (Ptr ?p :: cte_C ptr)"])
                apply (thin_tac "rva = X" for X)
                apply (clarsimp simp: h_t_valid_clift_Some_iff typ_heap_simps)
                apply (rule ccte_relation_ccap_relation)
                apply (erule (2) rf_sr_cte_relation)
               apply (elim conjE)
               apply (rule_tac nodeCap1 = "nodeCapa" in ih,
                    (simp | rule conjI refl gsCNodes)+)[1]
                   apply (clarsimp simp: cte_level_bits_def field_simps isCap_simps, fast)
                  apply (rule refl)
                 apply assumption
                apply assumption
               apply assumption
              apply vcg
             apply (simp add: getSlotCap_def imp_conjR)
             apply (wp getCTE_ctes_of | (wp (once) hoare_drop_imps))+
            apply (clarsimp simp: Collect_const_mem if_then_simps lookup_fault_lifts cong: imp_cong conj_cong)
            apply vcg
           apply (vcg strip_guards=true)
          apply (simp add: locateSlot_conv)
          apply wp
         apply vcg
        apply (vcg strip_guards=true)
       apply (vcg strip_guards=true)
      apply (rule conjI)
      \<comment> \<open>Haskell guard\<close>
       apply (clarsimp simp del: imp_disjL) \<comment> \<open>take a while\<close>
       apply (intro impI conjI allI)
           apply fastforce
          apply clarsimp
          apply arith
         apply (clarsimp simp: isCap_simps cte_level_bits_def
                               option.split[where P="\<lambda>x. x"])
        apply (clarsimp simp: isCap_simps valid_cap_simps' cte_level_bits_def objBits_defs
                              real_cte_at')
       apply (clarsimp simp: isCap_simps valid_cap'_def)
       \<comment> \<open>C guard\<close>
      apply (frule (1) cgD [OF refl], frule (1) rbD [OF refl], frule (1) gbD [OF refl])
      apply (simp add: Collect_const_mem cap_get_tag_isCap exception_defs lookup_fault_lifts
        n_bits_guard mask6_eqs word_le_nat_alt word_less_nat_alt gm)
      apply (elim conjE)
      apply (frule rf_sr_cte_at_valid [where p =
        "cte_Ptr (capCNodePtr cap + 2^cteSizeBits * ((cptr >> guard - (capCNodeBits cap + capCNodeGuardSize cap)) && mask (capCNodeBits cap)))", rotated])
       apply simp
       apply (erule (1) valid_cap_cte_at')
      apply (simp add: objBits_defs)
      apply (frule(2) gm)
      apply (simp add: word_less_nat_alt word_le_nat_alt less_mask_eq)
      apply (intro impI conjI allI, simp_all)
            apply (simp add: cap_simps)
           apply (frule iffD1 [OF cap_get_tag_CNodeCap])
            apply (simp add: cap_get_tag_isCap)
           apply (erule ssubst [where t = cap])
           apply simp
          apply (simp add: mask_def)
         apply (subgoal_tac "capCNodeBits cap \<noteq> 0")
          apply (clarsimp simp: linorder_not_less cap_simps)
         apply (clarsimp simp: isCap_simps valid_cap'_def)
        apply (clarsimp simp: linorder_not_less cap_simps)
        apply (clarsimp simp: isCap_simps valid_cap'_def)
       apply (clarsimp simp: linorder_not_less cap_simps)
       apply (clarsimp simp: isCap_simps valid_cap'_def)
       apply arith
      apply (subgoal_tac "(0x1F :: word32) = mask 5")
       apply (erule ssubst [where t = "0x1F"])
       apply (subst word_mod_2p_is_mask [symmetric])
        apply simp
       apply (simp add: unat_word_ariths)
      apply (simp add: mask_def)
      done
  qed
qed

abbreviation
  "lookupSlot_xf \<equiv> liftxf errstate lookupSlot_ret_C.status_C
                          lookupSlot_ret_C.slot_C ret__struct_lookupSlot_ret_C_'"


lemma rightsFromWord_spec:
  shows "\<forall>s. \<Gamma> \<turnstile> {s} \<acute>ret__struct_seL4_CapRights_C :== PROC rightsFromWord(\<acute>w)
  \<lbrace>seL4_CapRights_lift \<acute>ret__struct_seL4_CapRights_C = cap_rights_from_word_canon \<^bsup>s\<^esup>w \<rbrace>"
  apply vcg
  apply (simp add: seL4_CapRights_lift_def nth_shiftr mask_shift_simps nth_shiftr
                   cap_rights_from_word_canon_def word_and_1 eval_nat_numeral
                   word_sless_def word_sle_def)
  done


abbreviation
  "lookupSlot_rel' \<equiv> \<lambda>(cte, rm) (cte', rm'). cte' = Ptr cte \<and> rm = cap_rights_to_H (seL4_CapRights_lift rm')"

(* MOVE *)
lemma cap_rights_to_H_from_word_canon [simp]:
  "cap_rights_to_H (cap_rights_from_word_canon wd) = rightsFromWord wd"
  unfolding cap_rights_from_word_def rightsFromWord_def
  apply (simp add: cap_rights_from_word_canon_def)
  apply (simp add: cap_rights_to_H_def)
  done

abbreviation
  "lookupSlot_raw_xf \<equiv>
     liftxf errstate lookupSlot_raw_ret_C.status_C
           lookupSlot_raw_ret_C.slot_C
           ret__struct_lookupSlot_raw_ret_C_'"

definition
  lookupSlot_raw_rel :: "word32 \<Rightarrow> cte_C ptr \<Rightarrow> bool"
where
 "lookupSlot_raw_rel \<equiv> \<lambda>slot slot'. slot' = cte_Ptr slot"

lemma lookupSlotForThread_ccorres':
  "ccorres (lookup_failure_rel \<currency> lookupSlot_raw_rel) lookupSlot_raw_xf
  (valid_pspace' and tcb_at' thread)
  ({s. capptr_' s = cptr} \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread}) []
  (lookupSlotForThread thread cptr) (Call lookupSlot_'proc)"
  apply (cinit lift: capptr_' thread_'
           simp add: getThreadCSpaceRoot_def locateSlot_conv
                     returnOk_liftE[symmetric] split_def)
   apply (ctac pre: ccorres_liftE_Seq)
     apply (ctac (no_vcg) add: resolveAddressBits_ccorres)
       apply csymbr+
       apply (ctac add: ccorres_return_CE)
      apply csymbr+
      apply (ctac add: ccorres_return_C_errorE)
     apply wp+
   apply vcg
  apply (rule conjI)
   apply (clarsimp simp: conj_comms word_size tcbSlots Kernel_C.tcbCTable_def)
   apply (rule conjI, fastforce)
   apply (erule tcb_at_cte_at')
  apply (clarsimp simp add: Collect_const_mem errstate_def tcbSlots
                            Kernel_C.tcbCTable_def word_size lookupSlot_raw_rel_def
                            word_sle_def
                 split del: if_split)
  done

lemma lookupSlotForThread_ccorres[corres]:
  "ccorres (lookup_failure_rel \<currency> lookupSlot_raw_rel) lookupSlot_raw_xf
  (invs' and tcb_at' thread)
  (UNIV \<inter> {s. capptr_' s = cptr} \<inter> {s. thread_' s = tcb_ptr_to_ctcb_ptr thread}) []
  (lookupSlotForThread thread cptr) (Call lookupSlot_'proc)"
  apply (rule ccorres_guard_imp2, rule lookupSlotForThread_ccorres')
  apply fastforce
  done

end
end
