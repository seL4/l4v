(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Author: Rafal Kolanski

   Assumptions and lemmas on machine operations.
*)

theory Machine_C
imports Ctac_lemmas_C
begin

locale kernel_m = kernel +

assumes setVSpaceRoot_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>addr___unsigned_long = pt\<rbrace> \<inter> \<lbrace>\<acute>asid___unsigned_long = asid\<rbrace>) []
           (doMachineOp (RISCV64.setVSpaceRoot pt asid))
           (Call setVSpaceRoot_'proc)"

assumes hwASIDFlush_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>asid___unsigned_long = asid\<rbrace>) []
           (doMachineOp (RISCV64.hwASIDFlush asid))
           (Call hwASIDFlush_'proc)"

assumes read_stval_ccorres:
  "ccorres (=) ret__unsigned_long_' \<top> UNIV []
           (doMachineOp RISCV64.read_stval)
           (Call read_stval_'proc)"

assumes sfence_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp RISCV64.sfence)
           (Call sfence_'proc)"

assumes maskInterrupt_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>disable = from_bool m\<rbrace> \<inter> \<lbrace>\<acute>irq = ucast irq\<rbrace>) []
           (doMachineOp (maskInterrupt m irq))
           (Call maskInterrupt_'proc)"

assumes getActiveIRQ_ccorres:
"\<And>in_kernel.
   ccorres (\<lambda>(a::irq option) c::64 word.
     case a of None \<Rightarrow> c = ucast irqInvalid
     | Some (x::irq) \<Rightarrow> c = ucast x \<and> c \<noteq> ucast irqInvalid)
     ret__unsigned_long_'
     \<top> UNIV hs
 (doMachineOp (getActiveIRQ in_kernel)) (Call getActiveIRQ_'proc)"

assumes ackInterrupt_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
           (doMachineOp (ackInterrupt irq))
           (Call ackInterrupt_'proc)"

assumes plic_complete_claim_ccorres:
  "ccorres dc xfdc \<top> \<lbrace>\<acute>irq = ucast irq\<rbrace> []
           (doMachineOp (plic_complete_claim irq))
           (Call plic_complete_claim_'proc)"

assumes setIRQTrigger_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>irq = ucast irq\<rbrace> \<inter> \<lbrace>\<acute>edge_triggered = from_bool trigger\<rbrace>) []
           (doMachineOp (RISCV64.setIRQTrigger irq trigger))
           (Call setIRQTrigger_'proc)"

assumes resetTimer_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp resetTimer)
           (Call resetTimer_'proc)"

(* This is not very correct, however our current implementation of Hardware in haskell is stateless *)
assumes isIRQPending_ccorres:
  "\<And>in_kernel.
     ccorres (\<lambda>rv rv'. rv' = from_bool (rv \<noteq> None)) ret__unsigned_long_'
      \<top> UNIV []
      (doMachineOp (getActiveIRQ in_kernel)) (Call isIRQPending_'proc)"

assumes getActiveIRQ_Normal:
  "\<Gamma> \<turnstile> \<langle>Call getActiveIRQ_'proc, Normal s\<rangle> \<Rightarrow> s' \<Longrightarrow> isNormal s'"

(* The following are fastpath specific assumptions.
   We might want to move them somewhere else. *)

(*
  @{text slowpath} is an assembly stub that switches execution
  from the fastpath to the slowpath. Its contract is equivalence
  to the toplevel slowpath function @{term callKernel} for the
  @{text SyscallEvent} case.
*)
assumes slowpath_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. invs' s \<and> ct_in_state' ((=) Running) s)
     ({s. syscall_' s = syscall_from_H ev})
     [SKIP]
     (callKernel (SyscallEvent ev)) (Call slowpath_'proc)"

(*
  @{text slowpath} does not return, but uses the regular
  slowpath kernel exit instead.
*)
assumes slowpath_noreturn_spec:
  "\<Gamma> \<turnstile> UNIV Call slowpath_'proc {},UNIV"

(*
  @{text fastpath_restore} updates badge and msgInfo registers
  and returns to the user.
*)
assumes fastpath_restore_ccorres:
  "ccorres dc xfdc
     (\<lambda>s. t = ksCurThread s)
     ({s. badge_' s = bdg} \<inter> {s. msgInfo_' s = msginfo}
      \<inter> {s. cur_thread_' s = tcb_ptr_to_ctcb_ptr t})
     [SKIP]
     (asUser t (zipWithM_x setRegister
               [RISCV64_H.badgeRegister, RISCV64_H.msgInfoRegister]
               [bdg, msginfo]))
     (Call fastpath_restore_'proc)"

context kernel_m begin

lemma index_xf_for_sequence:
  "\<forall>s f. index_' (index_'_update f s) = f (index_' s)
          \<and> globals (index_'_update f s) = globals s"
  by simp

lemma dmo_if:
  "(doMachineOp (if a then b else c)) = (if a then (doMachineOp b) else (doMachineOp c))"
  by (simp split: if_split)

(* Count leading and trailing zeros. *)

(* FIXME BV: move *)
lemma word_ctz_max:
  "word_ctz w \<le> size w"
  unfolding word_ctz_def
  by (rule order_trans[OF List.length_takeWhile_le], clarsimp simp: word_size)

(* FIXME BV: move *)
lemma scast_of_nat_small:
  "x < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> scast (of_nat x :: 'a :: len word) = (of_nat x :: 'b :: len word)"
  apply (rule sym, subst word_unat.inverse_norm)
  apply (simp add: scast_def word_of_int[symmetric]
                   of_nat_nat[symmetric] unat_def[symmetric])
  apply (simp add: int_eq_sint unat_of_nat)
  done

(* FIXME BV: move *)
lemmas casts_of_nat_small = ucast_of_nat_small scast_of_nat_small

(* FIXME BV: move *)
lemma hoarep_Seq_nothrow:
  assumes c: "hoarep \<Gamma> \<Theta> F P c Q {}"
  assumes d: "hoarep \<Gamma> \<Theta> F Q d R A"
  shows "hoarep \<Gamma> \<Theta> F P (Seq c d) R A"
  by (rule hoarep.Seq[OF HoarePartialDef.conseqPrePost[OF c] d]; simp)

definition clz32_step where
  "clz32_step i \<equiv> \<acute>mask___unsigned :== \<acute>mask___unsigned >> unat ((1::32 sword) << unat i);;
                 \<acute>bits :== SCAST(32 signed \<rightarrow> 32) (if \<acute>mask___unsigned < \<acute>x___unsigned then 1 else 0) << unat i;;
                 Guard ShiftError \<lbrace>\<acute>bits < SCAST(32 signed \<rightarrow> 32) 0x20\<rbrace> (\<acute>x___unsigned :== \<acute>x___unsigned >> unat \<acute>bits);;
                 \<acute>count :== \<acute>count - \<acute>bits"

definition clz32_invariant where
  "clz32_invariant i s \<equiv> {s'.
   mask___unsigned_' s' \<ge> x___unsigned_' s'
   \<and> of_nat (word_clz (x___unsigned_' s')) + count_' s' = of_nat (word_clz (x___unsigned_' s)) + 32
   \<and> mask___unsigned_' s' = mask (2 ^ unat i)}"

\<comment>\<open> This function returns an expression stating that "if xs contains an element satisfying P, then
    the nth element of xs is the *first* that satisfies P". \<close>
definition first_in_list where
  "first_in_list P n xs \<equiv> (\<forall>i. i < n \<longrightarrow> i < length xs \<longrightarrow> \<not> P (xs ! i)) \<and>
                           (n < length xs \<longrightarrow> P (xs ! n))"

\<comment>\<open> There is always some n at which P (x ! n) or P contains no such element \<close>
lemma first_in_list_exists:
  "\<exists>n. first_in_list P n xs"
  apply (induction xs; simp add: first_in_list_def)
  apply (erule exE)
  apply (case_tac "P x1")
   apply (rule_tac x=0 in exI, simp)
  apply (rule_tac x="Suc n" in exI, clarsimp)
  apply (case_tac i; simp)
  done

\<comment>\<open> If you know where P first fails to be true, then you know how to compute takeWhile with take. \<close>
lemma takeWhile_take_equiv:
  "first_in_list (not P) n xs \<Longrightarrow> takeWhile P xs = take n xs"
  apply (rule takeWhile_eq_take_P_nth)
  apply (clarsimp simp: first_in_list_def pred_neg_def)
  apply (clarsimp simp: first_in_list_def pred_neg_def)
  done

\<comment>\<open> If you know that P fails to be true early enough, then truncating the input does not effect the
    output of takeWhile. \<close>
lemma takeWhile_truncate:
  "length (takeWhile P xs) \<le> m
  \<Longrightarrow> takeWhile P (take m xs) = takeWhile P xs"
  apply (subgoal_tac "\<exists>n. first_in_list (not P) n xs")
   apply (clarsimp)
   apply (case_tac "n \<le> m")
    apply (subgoal_tac "first_in_list (not P) n (take m xs)")
     apply (drule takeWhile_take_equiv, simp)
     apply (drule takeWhile_take_equiv, simp)
    apply (clarsimp simp: first_in_list_def)
   apply (subst (asm) takeWhile_take_equiv, assumption)
   apply (clarsimp simp: first_in_list_def pred_neg_def)
  apply (rule first_in_list_exists)
  done

lemma word_clz_shiftr_1:
  fixes z::"'a::len word"
  assumes wordsize: "1 < LENGTH('a)"
  shows "z \<noteq> 0 \<Longrightarrow> word_clz (z >> 1) = word_clz z + 1"
  supply word_size [simp]
  apply (clarsimp simp: word_clz_def)
  using wordsize apply (subst bl_shiftr, simp)
  apply (subst takeWhile_append2; simp add: wordsize)
  apply (subst takeWhile_truncate)
  using word_clz_nonzero_max[where w=z]
  apply (clarsimp simp: word_clz_def)
  apply simp+
  done

(* FIXME BV: generalise and move *)
lemma word_clz_1[simp]:
  "word_clz (1::32 word) = 31"
  "word_clz (1::64 word) = 63"
  by (clarsimp simp: word_clz_def to_bl_def)+

lemma shiftr_Suc:
  fixes x::"'a::len word"
  shows "x >> (Suc n) = x >> n >> 1"
  by (clarsimp simp: shiftr_shiftr)

lemma shiftl_Suc:
  fixes x::"'a::len word"
  shows "x << (Suc n) = x << n << 1"
  by (clarsimp simp: shiftl_shiftl)

lemma word_clz_shiftr:
  fixes z::"'a::len word"
  shows "n < LENGTH('a) \<Longrightarrow> z >> n \<noteq> 0 \<Longrightarrow> word_clz (z >> n) = word_clz z + n"
  apply (induction n; simp)
  apply (subgoal_tac "0 \<noteq> z >> n")
  apply (subst shiftr_Suc)
  apply (subst word_clz_shiftr_1; simp)
  apply (clarsimp simp: word_less_nat_alt shiftr_div_2n' div_mult2_eq)
  apply (case_tac "unat z div 2 ^ n = 0"; simp)
  apply (clarsimp simp: div_eq_0_iff)
  done

lemma word_clz_shiftr':
  fixes z::"'a::len word"
  shows "n < LENGTH('a) \<Longrightarrow> z > mask n \<Longrightarrow> word_clz (z >> n) = word_clz z + n"
  apply (erule word_clz_shiftr)
  apply (clarsimp simp: mask_def)
  apply (clarsimp simp: word_less_nat_alt word_le_nat_alt shiftr_div_2n' div_mult2_eq)
  apply (case_tac "unat z div 2 ^ n = 0"; simp)
  apply (clarsimp simp: div_eq_0_iff)
  done

lemma clz32_step:
  "unat (i :: 32 sword) < 5 \<Longrightarrow>
   \<Gamma> \<turnstile> (clz32_invariant (i+1) s) clz32_step i (clz32_invariant i s)"
  unfolding clz32_step_def
  apply (vcg, clarsimp simp: clz32_invariant_def)
  \<comment> \<open>Introduce some trivial but useful facts so that most later goals are solved with simp\<close>
  apply (prop_tac "i \<noteq> -1", clarsimp simp: unat_minus_one_word)
  apply (frule unat_Suc2)
  apply (prop_tac "(2 :: nat) ^ unat i < (32 :: nat)",
         clarsimp simp: power_strict_increasing_iff[where b=2 and y=5, simplified])
  apply (prop_tac "(2 :: nat) ^ unat (i + 1) \<le> (32 :: nat)",
         clarsimp simp: unat_Suc2 power_increasing_iff[where b=2 and y=4, simplified])
  apply (intro conjI impI; clarsimp)
       apply (clarsimp simp: word_less_nat_alt)
      apply (erule le_shiftr)
     apply (clarsimp simp: word_size shiftr_mask2 word_clz_shiftr')
    apply (clarsimp simp: shiftr_mask2)
   apply fastforce
  apply (clarsimp simp: shiftr_mask2)
  done

(* FIXME BV: generalise this? *)
lemma word32_le_1:
  "(a :: 32 word) \<le> 1 = (a = 0 \<or> a = 1)"
  apply (word_bitwise)
  by fastforce

lemma word64_le_1:
  "(a :: 64 word) \<le> 1 = (a = 0 \<or> a = 1)"
  apply (word_bitwise)
  by fastforce

(* FIXME BV: move *)
lemma max_word_max32:
  "(a :: 32 word) \<le> 0xFFFFFFFF"
  by (word_bitwise)

lemma max_word_max64:
  "(a :: 64 word) \<le> 0xFFFFFFFFFFFFFFFF"
  by (word_bitwise)

lemma clz32_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call clz32_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_clz (x___unsigned_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold clz32_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="clz32_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
   apply (rule HoarePartial.SeqSwap[OF clz32_step], simp, simp)+
   apply (rule conseqPre, vcg)
   apply (all \<open>clarsimp simp: clz32_invariant_def mask_def max_word_max32\<close>)
  by (fastforce simp: word32_le_1)

definition clz64_step where
  "clz64_step i \<equiv> \<acute>mask___unsigned_longlong :== \<acute>mask___unsigned_longlong >> unat ((1::32 sword) << unat i);;
                   \<acute>bits :== SCAST(32 signed \<rightarrow> 32) (if \<acute>mask___unsigned_longlong < \<acute>x___unsigned_longlong then 1 else 0) << unat i;;
                   Guard ShiftError \<lbrace>\<acute>bits < SCAST(32 signed \<rightarrow> 32) 0x40\<rbrace> (\<acute>x___unsigned_longlong :== \<acute>x___unsigned_longlong >> unat \<acute>bits);;
                   \<acute>count :== \<acute>count - \<acute>bits"

definition clz64_invariant where
  "clz64_invariant i s \<equiv> {s'.
   mask___unsigned_longlong_' s' \<ge> x___unsigned_longlong_' s'
   \<and> of_nat (word_clz (x___unsigned_longlong_' s')) + count_' s' = of_nat (word_clz (x___unsigned_longlong_' s)) + 64
   \<and> mask___unsigned_longlong_' s' = mask (2 ^ unat i)}"

lemma clz64_step:
  "unat (i :: 32 sword) < 6 \<Longrightarrow>
   \<Gamma> \<turnstile> (clz64_invariant (i+1) s) clz64_step i (clz64_invariant i s)"
  unfolding clz64_step_def
  apply (vcg, clarsimp simp: clz64_invariant_def)
  \<comment> \<open>Introduce some trivial but useful facts so that most later goals are solved with simp\<close>
  apply (prop_tac "i \<noteq> -1", clarsimp simp: unat_minus_one_word)
  apply (frule unat_Suc2)
  apply (prop_tac "(2 :: nat) ^ unat i < (64 :: nat)",
         clarsimp simp: power_strict_increasing_iff[where b=2 and y=6, simplified])
  apply (prop_tac "(2 :: nat) ^ unat (i + 1) \<le> (64 :: nat)",
         clarsimp simp: unat_Suc2 power_increasing_iff[where b=2 and y=5, simplified])
  apply (intro conjI impI; clarsimp)
       apply (clarsimp simp: word_less_nat_alt)
      apply (erule le_shiftr)
     apply (clarsimp simp: word_size shiftr_mask2 word_clz_shiftr')
    apply (clarsimp simp: shiftr_mask2)
   apply fastforce
  apply (clarsimp simp: shiftr_mask2)
  done

lemma word_clz_not_minus_1:
  "of_nat (word_clz (w :: 64 word)) \<noteq> (max_word :: 32 word)"
  unfolding not_max_word_iff_less
  apply (rule word_of_nat_less)
  apply (rule le_less_trans[OF word_clz_max[where w=w]])
  by (simp add: word_size max_word_def)

lemma clz64_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call clz64_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_clz (x___unsigned_longlong_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold clz64_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="clz64_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
   apply (rule HoarePartial.SeqSwap[OF clz64_step], simp, simp)+
   apply (rule conseqPre, vcg)
   apply (all \<open>clarsimp simp: clz64_invariant_def mask_def max_word_max64\<close>)
  apply (clarsimp simp: word64_le_1)
  apply (erule disjE; clarsimp)
  apply (subst add.commute)
  apply (subst ucast_increment[symmetric])
   apply (rule word_clz_not_minus_1)
  apply (clarsimp)
  done

lemma word_ctz_bound_below_helper:
  fixes x :: "'a::len word"
  assumes sz: "n \<le> LENGTH('a)"
  shows "x && mask n = 0
   \<Longrightarrow> to_bl x = (take (LENGTH('a) - n) (to_bl x) @ replicate n False)"
  apply (subgoal_tac "replicate n False = drop (LENGTH('a) - n) (to_bl x)")
   apply (subgoal_tac "True \<notin> set (drop (LENGTH('a) - n) (to_bl x))")
    apply (drule list_of_false, clarsimp simp: sz)
   apply (drule_tac sym[where t="drop n x" for n x], clarsimp)
  apply (rule sym)
  apply (rule is_aligned_drop; clarsimp simp: is_aligned_mask sz)
  done

lemma word_ctz_bound_below:
  fixes x :: "'a::len word"
  assumes sz[simp]: "n \<le> LENGTH('a)"
  shows "x && mask n = 0 \<Longrightarrow> n \<le> word_ctz x"
  apply (clarsimp simp: word_ctz_def)
  apply (subst word_ctz_bound_below_helper[OF sz]; simp)
  apply (subst takeWhile_append2; clarsimp)
  done

lemma mask_to_bl_exists_True:
  "x && mask n \<noteq> 0 \<Longrightarrow> \<exists>m. (rev (to_bl x)) ! m \<and> m < n"
  apply (subgoal_tac "\<not>(\<forall>m. m < n \<longrightarrow> \<not>(rev (to_bl x)) ! m)", fastforce)
  apply (intro notI)
  apply (subgoal_tac "x && mask n = 0", clarsimp)
  apply (clarsimp simp: eq_zero_set_bl in_set_conv_nth)
  apply (subst (asm) to_bl_nth, clarsimp simp: word_size)
  apply (clarsimp simp: and_bang word_size)
  apply (drule_tac x="LENGTH('a) - Suc i" in spec, simp)
  apply (subst (asm) rev_nth, simp)
  apply (subst (asm) to_bl_nth; clarsimp simp: word_size)
  done

lemma word_ctz_bound_above:
  fixes x :: "'a::len word"
  assumes sz: "n \<le> LENGTH('a)"
  shows "x && mask n \<noteq> 0 \<Longrightarrow> word_ctz x < n"
  apply (frule mask_to_bl_exists_True, clarsimp)
  apply (clarsimp simp: word_ctz_def)
  apply (subgoal_tac "m < length ((rev (to_bl x)))")
  apply (subst id_take_nth_drop[where xs="rev (to_bl x)"], assumption)
  apply (subst takeWhile_tail, simp)
  apply (rule order.strict_trans1)
  apply (rule List.length_takeWhile_le)
  apply (simp add: length_take)
  apply (erule order.strict_trans2, clarsimp simp: sz)
  done

lemma word_ctz_shiftr_1:
  fixes z::"'a::len word"
  assumes wordsize: "1 < LENGTH('a)"
  shows "z \<noteq> 0 \<Longrightarrow> 1 \<le> word_ctz z \<Longrightarrow> word_ctz (z >> 1) = word_ctz z - 1"
  supply word_size [simp]
  apply (clarsimp simp: word_ctz_def)
  using wordsize apply (subst bl_shiftr, simp)
  apply (simp add: rev_take )
   apply (subgoal_tac
 "length (takeWhile Not (rev (to_bl z))) - Suc 0 = length (takeWhile Not (take 1 (rev (to_bl z)) @
    drop 1 (rev (to_bl z)))) - Suc 0")
   apply (subst (asm) takeWhile_append2)
    apply clarsimp
    apply (case_tac "rev (to_bl z)"; simp)
   apply clarsimp
   apply (subgoal_tac "\<exists>m. (rev (to_bl z)) ! m \<and> m < LENGTH('a)", clarsimp)
    apply (case_tac m)
     apply (case_tac "rev (to_bl z)"; simp)
    apply (subst takeWhile_append1, subst in_set_conv_nth)
      apply (rule_tac x=nat in exI)
      apply (intro conjI)
       apply (clarsimp simp: length_drop wordsize)
       using wordsize
       apply linarith
      apply (rule refl, clarsimp)
    apply simp
   apply (rule mask_to_bl_exists_True, simp)
  apply simp
  done

lemma word_ctz_shiftr:
  fixes z::"'a::len word"
  assumes nz: "z \<noteq> 0"
  shows "n < LENGTH('a) \<Longrightarrow> n \<le> word_ctz z \<Longrightarrow> word_ctz (z >> n) = word_ctz z - n"
  apply (induction n; simp)
  apply (subst shiftr_Suc)
  apply (subst word_ctz_shiftr_1, simp)
    apply (clarsimp simp del: word_neq_0_conv)
    apply (subgoal_tac "word_ctz z < n", clarsimp)
    apply (rule word_ctz_bound_above, clarsimp simp: word_size)
    apply (subst (asm) and_mask_eq_iff_shiftr_0[symmetric], clarsimp simp: nz)
   apply (rule word_ctz_bound_below, clarsimp simp: word_size)
   apply (rule mask_zero)
   apply (rule is_aligned_shiftr, simp add: is_aligned_mask)
   apply (case_tac "z && mask (Suc n) = 0", simp)
   apply (frule word_ctz_bound_above[rotated]; clarsimp simp: word_size)
   apply simp
  done

lemma word_ctz_0[simp]:
  "word_ctz (0::32 word) = 32"
  "word_ctz (0::64 word) = 64"
  by (clarsimp simp: word_ctz_def to_bl_def)+

definition ctz32_step where
  "ctz32_step i \<equiv> \<acute>mask___unsigned :== \<acute>mask___unsigned >> unat ((1::32 sword) << unat i);;
                   \<acute>bits :== SCAST(32 signed \<rightarrow> 32) (if \<acute>x___unsigned && \<acute>mask___unsigned = SCAST(32 signed \<rightarrow> 32) 0 then 1 else 0) << unat i;;
                   Guard ShiftError \<lbrace>\<acute>bits < SCAST(32 signed \<rightarrow> 32) 0x20\<rbrace> (\<acute>x___unsigned :== \<acute>x___unsigned >> unat \<acute>bits);;
                   \<acute>count :== \<acute>count + \<acute>bits"

definition ctz32_invariant where
  "ctz32_invariant (i :: 32 sword) s \<equiv> {s'.
     (x___unsigned_' s' \<noteq> 0 \<longrightarrow> (of_nat (word_ctz (x___unsigned_' s')) + count_' s' = of_nat (word_ctz (x___unsigned_' s))
   \<and> (word_ctz (x___unsigned_' s') < 2 ^ unat i)))
   \<and> (x___unsigned_' s' = 0 \<longrightarrow> (count_' s' + (0x1 << (unat i)) = 33 \<and> x___unsigned_' s = 0))
   \<and> mask___unsigned_' s' = mask (2 ^ unat i)}"

lemma mask_shiftr_zero:
  "\<lbrakk>x && mask a = 0;  x >> a = 0\<rbrakk> \<Longrightarrow> x = 0"
  by (simp add: and_mask_eq_iff_shiftr_0[symmetric])

lemma word_ctz_32:
  "word_ctz (x :: 32 word) = 32 \<Longrightarrow> x = 0"
  apply (clarsimp simp: word_ctz_def)
  apply (word_bitwise)
  by (auto split: if_splits)

lemma ctz32_step:
  "unat (i :: 32 sword) < 5 \<Longrightarrow>
   \<Gamma> \<turnstile> (ctz32_invariant (i+1) s) ctz32_step i (ctz32_invariant i s)"
  supply word_neq_0_conv [simp del]
  unfolding ctz32_step_def
  apply (vcg, clarsimp simp: ctz32_invariant_def)
  apply (prop_tac "i \<noteq> -1", clarsimp simp: unat_minus_one_word)
  apply (frule unat_Suc2)
  apply (prop_tac "(2 :: nat) ^ unat i < (32 :: nat)",
         clarsimp simp: power_strict_increasing_iff[where b=2 and y=5, simplified])
  apply (prop_tac "(2 :: nat) ^ unat (i + 1) \<le> (32 :: nat)",
         clarsimp simp: unat_Suc2 power_increasing_iff[where b=2 and y=4, simplified])
  apply (intro conjI; intro impI)
   apply (intro conjI)
      apply (clarsimp simp: word_less_nat_alt)
     apply (intro impI)
     apply (subgoal_tac "x___unsigned_' x \<noteq> 0")
      apply (intro conjI, clarsimp)
       apply (subst word_ctz_shiftr, clarsimp, clarsimp)
        apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
        apply (clarsimp simp: shiftr_mask2 is_aligned_mask[symmetric])
       apply (subst of_nat_diff)
        apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
        apply (clarsimp simp: shiftr_mask2)
     apply fastforce
      apply (subst word_ctz_shiftr, clarsimp, clarsimp)
       apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
       apply (clarsimp simp: shiftr_mask2 is_aligned_mask[symmetric])
      apply (fastforce elim: is_aligned_weaken)
     apply fastforce
    apply (intro impI conjI; clarsimp simp: shiftr_mask2)
     apply (subgoal_tac "x___unsigned_' x = 0", clarsimp)
      apply (subst add.commute, simp)
     apply (fastforce simp: shiftr_mask2 word_neq_0_conv elim: mask_shiftr_zero)
    apply (frule (1) mask_shiftr_zero, simp)
   apply (clarsimp simp: shiftr_mask2)
  by (fastforce simp: shiftr_mask2 intro: word_ctz_bound_above)

lemma ctz32_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call ctz32_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_ctz (x___unsigned_' s))\<rbrace>"
  supply word_neq_0_conv [simp del]
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold ctz32_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="ctz32_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
   apply (rule HoarePartial.SeqSwap[OF ctz32_step], simp, simp)+
   apply (rule conseqPre, vcg)
   apply (clarsimp simp: ctz32_invariant_def)
   apply (clarsimp simp: mask_def)
   apply (subgoal_tac "word_ctz (x___unsigned_' s) \<le> size (x___unsigned_' s)")
    apply (clarsimp simp: word_size)
  using word_ctz_32 apply force
   apply (rule word_ctz_max)
  apply (clarsimp simp: ctz32_invariant_def)
  apply (case_tac "x___unsigned_' x = 0"; clarsimp)
  done

definition ctz64_step where
  "ctz64_step i \<equiv> \<acute>mask___unsigned_longlong :== \<acute>mask___unsigned_longlong >> unat ((1::32 sword) << unat i);;
                   \<acute>bits :== SCAST(32 signed \<rightarrow> 32) (if \<acute>x___unsigned_longlong && \<acute>mask___unsigned_longlong = SCAST(32 signed \<rightarrow> 64) 0 then 1 else 0) << unat i;;
                   Guard ShiftError \<lbrace>\<acute>bits < SCAST(32 signed \<rightarrow> 32) 0x40\<rbrace> (\<acute>x___unsigned_longlong :== \<acute>x___unsigned_longlong >> unat \<acute>bits);;
                   \<acute>count :== \<acute>count + \<acute>bits"

definition ctz64_invariant where
  "ctz64_invariant i s \<equiv> {s'.
     (x___unsigned_longlong_' s' \<noteq> 0 \<longrightarrow> (of_nat (word_ctz (x___unsigned_longlong_' s')) + count_' s' = of_nat (word_ctz (x___unsigned_longlong_' s))
   \<and> (word_ctz (x___unsigned_longlong_' s') < 2 ^ unat i)))
   \<and> (x___unsigned_longlong_' s' = 0 \<longrightarrow> (count_' s' + (0x1 << (unat i)) = 65 \<and> x___unsigned_longlong_' s = 0))
   \<and> mask___unsigned_longlong_' s' = mask (2 ^ unat i)}"

lemma ctz64_step:
  "unat (i :: 32 sword) < 6 \<Longrightarrow>
   \<Gamma> \<turnstile> (ctz64_invariant (i+1) s) ctz64_step i (ctz64_invariant i s)"
supply word_neq_0_conv [simp del]
  unfolding ctz64_step_def
  apply (vcg, clarsimp simp: ctz64_invariant_def)
  apply (prop_tac "i \<noteq> -1", clarsimp simp: unat_minus_one_word)
  apply (frule unat_Suc2)
  apply (prop_tac "(2 :: nat) ^ unat i < (64 :: nat)",
         clarsimp simp: power_strict_increasing_iff[where b=2 and y=6, simplified])
  apply (prop_tac "(2 :: nat) ^ unat (i + 1) \<le> (64 :: nat)",
         clarsimp simp: unat_Suc2 power_increasing_iff[where b=2 and y=5, simplified])
  apply (intro conjI; intro impI)
   apply (intro conjI)
      apply (clarsimp simp: word_less_nat_alt)
     apply (intro impI)
     apply (subgoal_tac "x___unsigned_longlong_' x \<noteq> 0")
      apply (intro conjI, clarsimp)
       apply (subst word_ctz_shiftr, clarsimp, clarsimp)
        apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
        apply (clarsimp simp: shiftr_mask2 is_aligned_mask[symmetric])
       apply (subst of_nat_diff)
        apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
        apply (clarsimp simp: shiftr_mask2)
     apply fastforce
      apply (subst word_ctz_shiftr, clarsimp, clarsimp)
       apply (rule word_ctz_bound_below, clarsimp simp: shiftr_mask2)
       apply (clarsimp simp: shiftr_mask2 is_aligned_mask[symmetric])
      apply (fastforce elim: is_aligned_weaken)
     apply fastforce
    apply (intro impI conjI; clarsimp simp: shiftr_mask2)
     apply (subgoal_tac "x___unsigned_longlong_' x = 0", clarsimp)
      apply (subst add.commute, simp)
     apply (fastforce simp: shiftr_mask2 word_neq_0_conv elim: mask_shiftr_zero)
    apply (frule (1) mask_shiftr_zero, simp)
   apply (clarsimp simp: shiftr_mask2)
  by (fastforce simp: shiftr_mask2 intro: word_ctz_bound_above)

lemma word_and_mask_word_ctz_zero:
  assumes "l = word_ctz w"
  shows "w && mask l = 0"
  unfolding word_ctz_def assms
  apply (word_eqI)
  apply (drule takeWhile_take_has_property_nth)
  apply (simp add: test_bit_bl)
  done

lemmas word_ctz_64 = word_and_mask_word_ctz_zero[where 'a=64 and l=64, simplified]

lemma ctz64_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call ctz64_'proc \<lbrace>\<acute>ret__unsigned = of_nat (word_ctz (x___unsigned_longlong_' s))\<rbrace>"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (hoarep_rewrite, fold ctz64_step_def)
  apply (intro allI hoarep.Catch[OF _ hoarep.Skip])
  apply (rule_tac Q="ctz64_invariant 0 s" in hoarep_Seq_nothrow[OF _ creturn_wp])
   apply (rule HoarePartial.SeqSwap[OF ctz64_step], simp, simp)+
   apply (rule conseqPre, vcg)
   apply (clarsimp simp: ctz64_invariant_def)
   apply (clarsimp simp: mask_def)
   apply (subgoal_tac "word_ctz (x___unsigned_longlong_' s) \<le> size (x___unsigned_longlong_' s)")
    apply (clarsimp simp: word_size)
    apply (erule le_neq_trans, clarsimp)
  using word_ctz_64 apply force
   apply (rule word_ctz_max)
  apply (clarsimp simp: ctz64_invariant_def)
  apply (case_tac "x___unsigned_longlong_' x = 0"; clarsimp)
  done

(* The library implementations would allow us to weaken the preconditions to allow zero inputs,
   but we keep the stronger preconditions to preserve older proofs that use these specs. *)
lemma clzl_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> x___unsigned_long_' s \<noteq> 0}
   Call clzl_'proc
   \<lbrace>\<acute>ret__long = of_nat (word_clz (x___unsigned_long_' s))\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  by (clarsimp simp: casts_of_nat_small[OF word_clz_max[THEN le_less_trans]] word_size)

lemma ctzl_spec:
  "\<forall>s. \<Gamma> \<turnstile> {\<sigma>. s = \<sigma> \<and> x___unsigned_long_' s \<noteq> 0}
   Call ctzl_'proc
   \<lbrace>\<acute>ret__long = of_nat (word_ctz (x___unsigned_long_' s))\<rbrace>"
  apply (rule allI, rule conseqPre, vcg)
  by (clarsimp simp: casts_of_nat_small[OF word_ctz_max[THEN le_less_trans]] word_size)

end
end
