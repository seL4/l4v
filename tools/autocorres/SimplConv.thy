(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Convert a SIMPL fragment into a monadic fragment.
 *)

theory SimplConv
imports L1Defs L1Peephole
begin

(*
 * Lemmas to unfold prior to L1 conversion.
 *)
named_theorems L1unfold
declare creturn_def [L1unfold]
declare creturn_void_def [L1unfold]
declare cbreak_def [L1unfold]
declare whileAnno_def [L1unfold]
declare ccatchbrk_def [L1unfold]

(* Alternative definitions of "Language.switch" *)
lemma switch_alt_defs [L1unfold]:
  "switch x [] \<equiv> SKIP"
  "switch v ((a, b) # vs) \<equiv> Cond {s. v s \<in> a} b (switch v vs)"
  by auto

lemma sless_positive [simp]:
  "\<lbrakk> a < n; n \<le> (2 ^ (len_of TYPE('a) - 1)) - 1 \<rbrakk> \<Longrightarrow> (a :: ('a::{len}) word) <s n"
  apply (subst signed.less_le)
  apply safe
  apply (subst word_sle_msb_le)
  apply safe
    apply (force simp: not_msb_from_less)
   apply simp
  apply simp
  done

lemma sle_positive [simp]:
  "\<lbrakk> a \<le> n; n \<le> (2 ^ (len_of TYPE('a) - 1)) - 1 \<rbrakk> \<Longrightarrow> (a :: ('a::{len}) word) <=s n"
  apply (clarsimp simp: signed.le_less)
  done

(* An induction rule that matches our recursive definitions. *)
lemma recguard_induct: "\<lbrakk> P 0; \<And>n. P (recguard_dec n) \<Longrightarrow> P n \<rbrakk> \<Longrightarrow> P n"
  apply (unfold recguard_dec_def)
  apply (erule nat_induct)
  apply (metis diff_Suc_1)
  done


(*
 * These "optimisation" rules are actually assumed by LocalVarExtract,
 * so better apply them even if L1opt rules are disabled by no_opt.
 *)
lemmas [L1except] =
  L1_set_to_pred_def in_set_to_pred in_set_if_then (* rewrite SIMPL set notation *)
  L1_seq_assoc (* Normalise seqs. Not strictly required, but useful *)

end
