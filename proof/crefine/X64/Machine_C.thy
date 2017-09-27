(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
   Author: Gerwin Klein

   Assumptions and lemmas on machine operations.
*)

theory Machine_C
imports Ctac_lemmas_C
begin

(* FIXME x64: add all machine operations as required *)
locale kernel_m = kernel +
assumes resetTimer_ccorres:
  "ccorres dc xfdc \<top> UNIV []
           (doMachineOp resetTimer)
           (Call resetTimer_'proc)"

(* FIXME x64: double-check this, assumption is ccorres holds regardless of in_kernel *)
(* FIXME x64: accessor function relation was complicated on ARM, testing if you don't
              need it to be that way *)
assumes getActiveIRQ_ccorres:
"\<And>in_kernel.
   ccorres (\<lambda>(a::8 word option) c::8 word.
     case a of None \<Rightarrow> c = (0xFF::8 word)
     | Some (x::8 word) \<Rightarrow> c = ucast x \<and> c \<noteq> (0xFF::8 word))
     ret__unsigned_char_'
     \<top> UNIV hs
 (doMachineOp (getActiveIRQ in_kernel)) (Call getActiveIRQ_'proc)"

(* This is not very correct, however our current implementation of Hardware in haskell is stateless *)
assumes isIRQPending_ccorres:
  "\<And>in_kernel.
     ccorres (\<lambda>rv rv'. rv' = from_bool (rv \<noteq> None)) ret__unsigned_long_'
      \<top> UNIV []
      (doMachineOp (getActiveIRQ in_kernel)) (Call isIRQPending_'proc)"

assumes getActiveIRQ_Normal:
  "\<Gamma> \<turnstile> \<langle>Call getActiveIRQ_'proc, Normal s\<rangle> \<Rightarrow> s' \<Longrightarrow> isNormal s'"

assumes maskInterrupt_ccorres:
  "ccorres dc xfdc \<top> (\<lbrace>\<acute>disable = from_bool m\<rbrace> \<inter> \<lbrace>\<acute>irq = ucast irq\<rbrace>) []
           (doMachineOp (maskInterrupt m irq))
           (Call maskInterrupt_'proc)"

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
     (\<lambda>s. invs' s \<and> ct_in_state' (op = Running) s)
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
               [X64_H.badgeRegister, X64_H.msgInfoRegister]
               [bdg, msginfo]))
     (Call fastpath_restore_'proc)"

assumes ackInterrupt_ccorres:
  "ccorres dc xfdc \<top> UNIV hs
           (doMachineOp (ackInterrupt irq))
           (Call ackInterrupt_'proc)"

context kernel_m begin

lemma index_xf_for_sequence:
  "\<forall>s f. index_' (index_'_update f s) = f (index_' s)
          \<and> globals (index_'_update f s) = globals s"
  by simp

(* FIXME CLEANUP on all arches: this entire cache op section has:
   - a number of useful word lemmas that can go into WordLib
   - a ton of hardcoded "mask 6" and "64", which on sabre is "mask 5" and "32" respectively.
   - The proofs themselves are extremely similar.
     This can be much more generic! *)

lemma upto_enum_word_nth:
  "\<lbrakk>i \<le> j; k \<le> unat (j - i)\<rbrakk> \<Longrightarrow> [i .e. j] ! k = i + of_nat k"
  apply (clarsimp simp: upto_enum_def nth_upt nth_append)
  apply (clarsimp simp: toEnum_of_nat word_le_nat_alt[symmetric])
  apply (rule conjI, clarsimp)
   apply (subst toEnum_of_nat, unat_arith)
   apply unat_arith
  apply (clarsimp simp: not_less unat_sub[symmetric])
  apply unat_arith
  done

lemma upto_enum_step_nth:
  "\<lbrakk>a \<le> c; n \<le> unat ((c - a) div (b - a))\<rbrakk> \<Longrightarrow> [a, b .e. c] ! n = a + of_nat n * (b - a)"
  apply (clarsimp simp: upto_enum_step_def not_less[symmetric])
  apply (subst upto_enum_word_nth)
    apply (auto simp: not_less word_of_nat_le)
  done

lemma neg_mask_add:
  "y && mask n = 0 \<Longrightarrow> x + y && ~~ mask n = (x && ~~ mask n) + y"
  by (clarsimp simp: mask_out_sub_mask mask_eqs(7)[symmetric] mask_twice)

lemma minus_minus_swap:
  "\<lbrakk> a \<le> c; b \<le> d; b \<le> a; d \<le> c\<rbrakk> \<Longrightarrow> (d :: nat) - b = c - a \<Longrightarrow> a - b = c - d"
  by arith

lemma minus_minus_swap':
  "\<lbrakk> c \<le> a; d \<le> b; b \<le> a; d \<le> c\<rbrakk> \<Longrightarrow> (b :: nat) - d = a - c \<Longrightarrow> a - b = c - d"
  by arith

lemma shiftr_shiftl_shiftr[simp]:
  "x >> a << a >> a = (x :: ('a :: len) word) >> a"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftr nth_shiftl)
  apply safe
  apply (drule test_bit_size)
  apply (simp add: word_size)
  done

lemma add_right_shift:
  "\<lbrakk>x && mask n = 0; y && mask n = 0; x \<le> x + y \<rbrakk>
    \<Longrightarrow> (x + y :: ('a :: len) word) >> n = (x >> n) + (y >> n)"
  apply (simp add: no_olen_add_nat is_aligned_mask[symmetric])
  apply (simp add: unat_arith_simps shiftr_div_2n' split del: if_split)
  apply (subst if_P)
   apply (erule order_le_less_trans[rotated])
   apply (simp add: add_mono)
  apply (simp add: shiftr_div_2n' is_aligned_def)
  done

lemma sub_right_shift:
  "\<lbrakk>x && mask n = 0; y && mask n = 0; y \<le> x \<rbrakk>
    \<Longrightarrow> (x - y) >> n = (x >> n :: ('a :: len) word) - (y >> n)"
  using add_right_shift[where x="x - y" and y=y and n=n]
  by (simp add: aligned_sub_aligned is_aligned_mask[symmetric]
                word_sub_le)

lemma dmo_if:
  "(doMachineOp (if a then b else c)) = (if a then (doMachineOp b) else (doMachineOp c))"
  by (simp split: if_split)

end

end
