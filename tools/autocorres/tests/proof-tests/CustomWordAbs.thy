(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CustomWordAbs
imports "../../AutoCorres"
begin

install_C_file "custom_word_abs.c"

lemma [word_abs]:
  "\<lbrakk> abstract_val P x sint x'; abstract_val Q y sint y' \<rbrakk> \<Longrightarrow>
        abstract_val (P \<and> Q) (max x y)
          sint (x' xor (x' xor y') && - (if x' <s y' then (1 :: sword32) else 0))"
  apply (clarsimp simp: max_def word_sless_def word_sle_def)
  done

lemma [word_abs]:
  "\<lbrakk> abstract_val P x unat x'; abstract_val Q y unat y' \<rbrakk> \<Longrightarrow>
         abstract_val (P \<and> Q \<and> y < 32) (x mod (2 ^ y)) unat (x' && 2 ^ unat y' - (1 :: word32))"
  apply (clarsimp simp del: shiftl_1 simp: shiftl_1 [symmetric])
  apply (fold mask_def)
  apply (subst word_mod_2p_is_mask [symmetric])
  apply (subst p2_gt_0)
  by (auto simp: unat_mod)

lemma [word_abs]:
  "\<lbrakk> abstract_val P x unat (x' :: word32);
     abstract_val Q y unat y' \<rbrakk> \<Longrightarrow>
      abstract_val (P \<and> Q) (x + y > UINT_MAX) id (x' + y' < x')"
  apply (subst not_le [symmetric], subst no_plus_overflow_unat_size)
  apply (clarsimp simp: not_less UINT_MAX_def word_size)
  apply arith
  done

autocorres [unsigned_word_abs = b c] "custom_word_abs.c"

context custom_word_abs begin

lemma "a' x y = max x y"
  by (unfold a'_def, rule refl)

lemma "b' x 4 s = Some (x mod 16)"
  by (unfold b'_def, simp)

lemma "c' x y = (if UINT_MAX < x + y then 1 else 0)"
  by (unfold c'_def, simp)

end

end
