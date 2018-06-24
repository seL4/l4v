(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Simple
imports
  "AutoCorres.AutoCorres"
begin

external_file "simple.c"

(* Parse the input file. *)
install_C_file "simple.c"

(* Abstract the input file. *)
autocorres [ ts_force pure = max, ts_force nondet = gcd, unsigned_word_abs = gcd ] "simple.c"

(* Generated theorems and proofs. *)
thm simple.max'_def simple.max'_ac_corres
thm simple.gcd'_def simple.gcd'_ac_corres

context simple begin

(* Show generated "max'" function matches in-built "max". *)
lemma "max' a b = max a b"
  unfolding max'_def max_def
  by (rule refl)

(* Show "gcd'" calculates the gcd. *)
lemma gcd_wp [wp]:
    "\<lbrace> P (gcd a b) \<rbrace> gcd' a b \<lbrace> P \<rbrace>!"
  (* Unfold definition of "gcd'". *)
  apply (unfold gcd'_def)

  (* Annoate the loop with an invariant and measure. *)
  apply (subst whileLoop_add_inv [where
     I="\<lambda>(a', b') s. gcd a b = gcd a' b' \<and> P (gcd a b) s"
     and M="\<lambda>((a', b'), s). a'"])

  (* Solve using weakest-precondition. *)
  apply (wp; clarsimp)
   apply (metis gcd.commute gcd_red_nat)
  using gt_or_eq_0 by fastforce

lemma monad_to_gets:
    "\<lbrakk> \<And>P. \<lbrace> P \<rbrace> f \<lbrace> \<lambda>r s. P s \<and> r = v s \<rbrace>!; empty_fail f \<rbrakk> \<Longrightarrow> f = gets v"
  apply atomize
  apply (monad_eq simp: validNF_def valid_def no_fail_def empty_fail_def)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x="\<lambda>s'. s = s'" in spec)
   apply clarsimp
   apply force
  apply clarsimp
  apply (drule_tac x="\<lambda>s'. s' = t" in spec)
  apply clarsimp
  apply force
  done

lemma gcd_to_return [simp]:
    "gcd' a b = return (gcd a b)"
  apply (subst monad_to_gets [where v="\<lambda>_. gcd a b"])
    apply (wp gcd_wp)
    apply simp
   apply (clarsimp simp: gcd'_def)
   apply (rule empty_fail_bind)
    apply (rule empty_fail_whileLoop)
    apply (clarsimp simp: split_def)
   apply (clarsimp simp: split_def)
  apply (clarsimp simp: split_def)
  done

end

end
