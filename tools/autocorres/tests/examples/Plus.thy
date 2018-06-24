(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Plus
imports
  "AutoCorres.AutoCorres"
begin

external_file "plus.c"
install_C_file "plus.c"

autocorres [ ts_force nondet = plus2 ] "plus.c"

context plus begin

(* 3 + 2 should be 5 *)
lemma "plus' 3 2 = 5"
  unfolding plus'_def
  by eval

(* plus does what it says on the box *)
lemma plus_correct: "plus' a b = a + b"
  unfolding plus'_def
  apply (rule refl)
  done

(* Compare pre-lifting to post-lifting *)
thm plus_global_addresses.plus2_body_def
thm plus2'_def

(* plus2 does what it says on the box *)
lemma plus2_correct: "\<lbrace>\<lambda>s. True\<rbrace> plus2' a b \<lbrace> \<lambda>r s. r = a + b\<rbrace>"
  unfolding plus2'_def
  apply (subst whileLoop_add_inv
   [where I="\<lambda>(a', b') s. a' + b' = a + b"
      and M="\<lambda>((a', b'), s). b'"])
  apply (wp, auto simp: not_less)
  done

(* plus2 does what it says on plus's box *)
lemma plus2_is_plus: "\<lbrace> \<lambda>s. True \<rbrace> plus2' a b \<lbrace> \<lambda>r s. r = plus' a b \<rbrace>"
  unfolding plus'_def
  apply (simp add:plus2_correct)
  done

(* Prove plus2 with no failure *)
lemma plus2_valid:"\<lbrace> \<lambda>s. True \<rbrace> plus2' a b \<lbrace> \<lambda>r s. r = a + b \<rbrace>!"
  unfolding plus2'_def
  apply (subst whileLoop_add_inv
   [where I="\<lambda>(a', b') s. a' + b' = a + b"
      and M="\<lambda>((a', b'), s). b'"])
  apply wp
    apply clarsimp
    apply unat_arith
   apply clarsimp
   apply unat_arith
  apply clarsimp
  done

end

end
