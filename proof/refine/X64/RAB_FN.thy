(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory RAB_FN

imports
  "CSpace1_R"
  "Lib.MonadicRewrite"

begin

definition
 "only_cnode_caps ctes =
    option_map ((\<lambda>x. if isCNodeCap x then x else NullCap) o cteCap) o ctes"

definition locateSlotFun_def:
"locateSlotFun cnode offset \<equiv> cnode + 2 ^ cte_level_bits * offset"

definition
  "cnode_caps_gsCNodes cts cns
    = (\<forall>cap \<in> ran cts. isCNodeCap cap
    \<longrightarrow> cns (capCNodePtr cap) = Some (capCNodeBits cap))"

abbreviation (input)
  "cnode_caps_gsCNodes' s \<equiv> cnode_caps_gsCNodes (only_cnode_caps (ctes_of s)) (gsCNodes s)"

function
  resolveAddressBitsFn ::
  "capability \<Rightarrow> cptr \<Rightarrow> nat \<Rightarrow> (machine_word \<Rightarrow> capability option)
    \<Rightarrow> (lookup_failure + (machine_word * nat))"
where
 "resolveAddressBitsFn a b c =
(\<lambda>x0 capptr bits caps. (let nodeCap = x0 in
  if isCNodeCap nodeCap
  then (let
        radixBits = capCNodeBits nodeCap;
        guardBits = capCNodeGuardSize nodeCap;
        levelBits = radixBits + guardBits;
        offset = (fromCPtr capptr `~shiftR~` (bits-levelBits)) &&
                   (mask radixBits);
        guard = (fromCPtr capptr `~shiftR~` (bits-guardBits)) &&
                   (mask guardBits);
        bitsLeft = bits - levelBits;
        slot = locateSlotFun (capCNodePtr nodeCap) offset
    in
      if levelBits = 0 then Inr (0, 0)
      else if \<not> (guardBits \<le> bits \<and> guard = capCNodeGuard nodeCap)
            then Inl $ GuardMismatch_ \<lparr>
                guardMismatchBitsLeft= bits,
                guardMismatchGuardFound= capCNodeGuard nodeCap,
                guardMismatchGuardSize= guardBits \<rparr>
      else if (levelBits > bits) then Inl $ DepthMismatch_ \<lparr>
            depthMismatchBitsLeft= bits,
            depthMismatchBitsFound= levelBits \<rparr>
      else if (bitsLeft = 0)
          then Inr (slot, 0)
      else (case caps slot of Some NullCap
        \<Rightarrow> Inr (slot, bitsLeft)
      | Some nextCap
        \<Rightarrow> resolveAddressBitsFn nextCap capptr bitsLeft caps
      | None \<Rightarrow> Inr (0, 0))
    )
  else Inl InvalidRoot
  ))

a b c"
  by auto

termination
  apply (relation "measure (snd o snd)")
  apply (auto split: if_split_asm)
  done

declare resolveAddressBitsFn.simps[simp del]

lemma isCNodeCap_capUntypedPtr_capCNodePtr:
  "isCNodeCap c \<Longrightarrow> capUntypedPtr c = capCNodePtr c"
  by (clarsimp simp: isCap_simps)

context begin interpretation Arch . (*FIXME: arch-split*)

lemma resolveAddressBitsFn_eq:
  "monadic_rewrite F E (\<lambda>s. (isCNodeCap cap \<longrightarrow> (\<exists>slot. cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot s))
        \<and> valid_objs' s \<and> cnode_caps_gsCNodes' s)
    (resolveAddressBits cap capptr bits)
    (gets (resolveAddressBitsFn cap capptr bits o only_cnode_caps o ctes_of))"
  (is "monadic_rewrite F E (?P cap) (?f cap bits) (?g cap capptr bits)")
proof (induct cap capptr bits rule: resolveAddressBits.induct)
  case (1 cap cref depth)
  show ?case
    apply (subst resolveAddressBits.simps, subst resolveAddressBitsFn.simps)
    apply (simp only: Let_def haskell_assertE_def K_bind_def)
    apply (rule monadic_rewrite_name_pre)
    apply (rule monadic_rewrite_guard_imp)
     apply (rule_tac P="(=) s" in monadic_rewrite_trans)
      (* step 1, apply the induction hypothesis on the lhs *)
      apply (rule monadic_rewrite_named_if monadic_rewrite_named_bindE
                  monadic_rewrite_refl[THEN monadic_rewrite_guard_imp, where f="returnOk y" for y]
                  monadic_rewrite_refl[THEN monadic_rewrite_guard_imp, where f="x $ y" for x y]
                  monadic_rewrite_refl[THEN monadic_rewrite_guard_imp, where f="assertE P" for P s]
                  TrueI)+
       apply (rule_tac g="case nextCap of CNodeCap a b c d
            \<Rightarrow> ?g nextCap cref bitsLeft
            | _ \<Rightarrow> returnOk (slot, bitsLeft)" in monadic_rewrite_guard_imp)
        apply (wpc | rule monadic_rewrite_refl "1.hyps"
           | simp only: capability.case haskell_assertE_def simp_thms)+
       apply (clarsimp simp: in_monad locateSlot_conv getSlotCap_def
                      dest!: in_getCTE fst_stateAssertD)
       apply (fastforce elim: cte_wp_at_weakenE')
      apply (rule monadic_rewrite_refl[THEN monadic_rewrite_guard_imp], simp)
     (* step 2, split and match based on the lhs structure *)
     apply (simp add: locateSlot_conv liftE_bindE unlessE_def whenE_def
                      if_to_top_of_bindE assertE_def stateAssert_def bind_assoc
                      assert_def if_to_top_of_bind getSlotCap_def
               split del: if_split cong: if_cong)
     apply (rule monadic_rewrite_if_l monadic_rewrite_symb_exec_l'[OF _ get_wp, rotated]
                 empty_fail_get no_fail_get impI
                 monadic_rewrite_refl get_wp
       | simp add: throwError_def returnOk_def locateSlotFun_def if_not_P
                   isCNodeCap_capUntypedPtr_capCNodePtr
             cong: if_cong split del: if_split)+
          apply (rule monadic_rewrite_symb_exec_l'[OF _ getCTE_inv _ _ getCTE_cte_wp_at, rotated])
            apply simp
           apply (rule impI, rule no_fail_getCTE)
          apply (simp add: monadic_rewrite_def simpler_gets_def return_def returnOk_def
                           only_cnode_caps_def cte_wp_at_ctes_of isCap_simps
                           locateSlotFun_def isCNodeCap_capUntypedPtr_capCNodePtr
                    split: capability.split)
         apply (rule monadic_rewrite_name_pre[where P="\<lambda>_. False" and f=fail]
                     monadic_rewrite_refl get_wp
           | simp add: throwError_def returnOk_def locateSlotFun_def if_not_P
                       isCNodeCap_capUntypedPtr_capCNodePtr
             cong: if_cong split del: if_split)+
  (* step 3, prove the non-failure conditions *)
  apply (clarsimp simp: isCap_simps)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap')
  apply (clarsimp simp: cte_level_bits_def valid_cap_simps'
                        real_cte_at' isCap_simps cteSizeBits_def objBits_simps)
  apply (clarsimp simp: cte_wp_at_ctes_of only_cnode_caps_def ball_Un
                        cnode_caps_gsCNodes_def ran_map_option o_def)
  apply (drule bspec, rule IntI, erule ranI, simp add: isCap_simps)
  apply (simp add: isCap_simps capAligned_def word_bits_def and_mask_less')
  done
qed

end

end
