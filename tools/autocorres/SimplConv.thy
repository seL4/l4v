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

(* Convert "lvar_nondet_init" (which sets local variables to
 * undefined values) into a "Spec" command we can translate. *)
definition "lvar_init_spec upd \<equiv> {(s, t). \<exists>v. t = upd (\<lambda>_. v) s}"
lemma lvar_nondet_init_rewrite [L1unfold]:
  "lvar_nondet_init accessor upd \<equiv> Spec (lvar_init_spec upd)"
  apply (clarsimp simp: lvar_nondet_init_def lvar_init_spec_def)
  done

lemma lvar_init_spec_to_L1_init [L1opt]:
  "L1_spec (lvar_init_spec upd) \<equiv> L1_init upd"
  apply (rule eq_reflection)
  apply (clarsimp simp: L1_defs lvar_init_spec_def)
  apply (clarsimp simp: bind_liftE_distrib [symmetric])
  apply (rule arg_cong [where f=liftE])
  apply (rule ext)
  apply (clarsimp simp: spec_def select_def simpler_modify_def bind_def)
  apply force
  done

lemma not_msb_from_less:
  "(v :: 'a word) < 2 ^ (len_of TYPE('a :: len) - 1) \<Longrightarrow> \<not> msb v"
  apply (clarsimp simp add: msb_nth)
  apply (drule less_mask_eq)
  apply (drule word_eqD, drule(1) iffD2)
  apply simp
  done

lemma sless_positive [simp]:
  "\<lbrakk> a < n; n \<le> (2 ^ (len_of TYPE('a) - 1)) - 1 \<rbrakk> \<Longrightarrow> (a :: ('a::{len}) word) <s n"
  apply (subst signed.less_le)
  apply safe
  apply (subst word_sle_msb_le)
  apply safe
    apply clarsimp
    apply (metis One_nat_def msb_shift not_msb_from_less word_not_simps(1))
   apply simp
  apply simp
  done

lemma sle_positive [simp]:
  "\<lbrakk> a \<le> n; n \<le> (2 ^ (len_of TYPE('a) - 1)) - 1 \<rbrakk> \<Longrightarrow> (a :: ('a::{len}) word) <=s n"
  apply (subst signed.le_less)
  apply (case_tac "n=0")
   apply clarsimp
  apply (clarsimp simp: sless_positive)
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
  lvar_init_spec_to_L1_init (* rewrite variable initialisers *)
  L1_seq_assoc (* not strictly required, but useful *)

end
