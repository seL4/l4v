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
A story of AutoCorres and recursion.

To do:
-- prove SIMPL total correctness
-- remove (* slow *) steps
-- remove word32 metis (or wait for word lifting...)
-- fix wp to support recursive fib'
-- Isar style proof?
*)

theory FibProof
imports
  "AutoCorres.AutoCorres"
begin

external_file "fib.c"

(*
 * The venerable Fibonacci function.
 *)
fun fibo :: "nat \<Rightarrow> nat" where
  "fibo 0 = 0" |
  "fibo (Suc 0) = Suc 0" |
  "fibo (Suc (Suc n)) = fibo n + fibo (Suc n)"
declare fibo.simps [simp del]

lemma fibo_alt_def: "fibo n = (if n = 0 then 0 else if n = 1 then 1 else fibo (n - 1) + fibo (n - 2))"
  apply (induct n rule: less_induct)
  apply (rename_tac n, case_tac n, simp add: fibo.simps)
  apply (rename_tac n1, case_tac n1, simp add: fibo.simps)
  apply (simp add: fibo.simps)
  done

lemma fibo_mono_Suc: "fibo n \<le> fibo (Suc n)"
  by (simp add: fibo_alt_def)
lemma fibo_mono: "a \<le> b \<Longrightarrow> fibo a \<le> fibo b"
  by (metis mono_iff_le_Suc mono_def fibo_mono_Suc)

lemma fibo_mono_strict: "n \<ge> 2 \<Longrightarrow> fibo n < fibo (Suc n)"
  apply (case_tac n, simp)
  apply (rename_tac n', subgoal_tac "fibo (Suc 0) \<le> fibo n'")
   apply (simp add: fibo.simps)
  apply (simp add: fibo_mono)
  done

lemma fiboI: "\<lbrakk> a + 1 = b; b + 1 = c \<rbrakk> \<Longrightarrow> fibo a + fibo b = fibo c"
  by (auto simp: fibo.simps)

(*
 * We write two versions in C, and compare correctness proofs on the
 * SIMPL and AutoCorres embeddings.
 *)


(*
 * C arithmetic is done using `unsigned', which is translated as `word32'.
 * So, it is much easier to prove that the C code implements this function,
 * which is not quite the same function as fibo.
 *)
function fibo32 :: "word32 \<Rightarrow> word32" where
  "fibo32 n = (if n = 0 then 0 else if n = 1 then 1 else fibo32 (n - 1) + fibo32 (n - 2))"
apply auto
done
termination fibo32
  by (relation "measure (\<lambda>x. unat x)", (simp|unat_arith)+)
declare fibo32.simps [simp del]

(*
 * But we really want to say that the C code does implement fibo
 * (at least up till 2971215073 < 2^32)...
 *)
lemma fibo_greater: "(6 + n) < fibo (6 + n)"
  apply (induct n)
   apply eval
  apply (subst add_Suc_right)+
  apply (subgoal_tac "Suc (6 + n) \<le> fibo (6 + n)")
   apply (subgoal_tac "fibo (6 + n) < fibo (Suc (6 + n))")
    apply simp
   apply (rule fibo_mono_strict)
   apply simp
  apply simp
  done
lemma fibo_greater': "n \<ge> 6 \<Longrightarrow> n < fibo n"
  by (metis le_iff_add fibo_greater)
lemma unat_word32_plus: "unat x + unat y < 2^32 \<Longrightarrow> unat x + unat y = unat (x + y :: word32)"
  by (metis len32 unat_of_nat_len word_arith_nat_add)

(* ... so we should say that too. *)
lemma fibo32_is_fibo: "fibo n < 2^32 \<Longrightarrow> fibo n = unat (fibo32 (of_nat n))"
  apply (induct n rule: less_induct)
  apply (subst fibo32.simps)
  apply (subst fibo_alt_def)
  apply (rename_tac n, case_tac "n = 0", simp)
  apply (case_tac "n = 1", simp)
  apply (subgoal_tac "n < 2^32"
                     "fibo (n - 1) + fibo (n - 2) < 2^32"
                     "of_nat n \<noteq> (0 :: word32)"
                     "of_nat n \<noteq> (1 :: word32)"
                     "fibo (n - 1) < 2^32"
                     "fibo (n - 2) < 2^32"
                     "fibo (n - 1) = unat (fibo32 (of_nat (n - 1)))"
                     "fibo (n - 2) = unat (fibo32 (of_nat (n - 2)))")
          apply (fastforce intro: unat_word32_plus)
         apply (metis diff_less gr0I zero_less_numeral)
        apply (metis diff_less gr0I zero_less_one)
       apply simp
      apply simp
     apply (metis len32 unat_1 unat_of_nat_len)
    apply (metis len32 unat_0 unat_of_nat_len)
   apply (metis fibo_alt_def)
  apply (case_tac "n < 6")
   apply simp
  apply (subgoal_tac "n < fibo n")
   apply simp
  apply (simp add: fibo_greater')
done

(* A helper for the SIMPL proofs later. *)
lemma fibo32_rec: "\<lbrakk> a < a + 2; b = a + 1; c = a + 2 \<rbrakk> \<Longrightarrow> fibo32 a + fibo32 b = fibo32 c"
  apply (subst(3) fibo32.simps)
  apply simp
  apply safe
     apply unat_arith
    apply (metis not_le overflow_plus_one_self word_n1_ge word_not_simps(1))
   apply (metis word_not_simps(1))
  apply (simp add: field_simps)
  done



(* First we invoke CParser to translate the C code to SIMPL. *)
install_C_file "fib.c"


context fib begin
(* fib_linear\<^bsub>C\<^esub> is the linear-time implementation. *)
thm fib_linear_body_def
(* fib\<^bsub>C\<^esub> is the pretty (inefficient) recursive implementation. *)
thm fib_body_def
(* First, let us prove that they implement fibo32. *)

(* First, the linear version. *)
lemma fib_linear_simpl_spec:
"\<Gamma> \<turnstile> {s. s = t}
     \<acute>ret__unsigned :== CALL fib_linear(\<acute>n)
     \<lbrace> (\<acute>ret__unsigned = fibo32 \<^bsup>t\<^esup>n) \<rbrace>"
  (* We have not annotated the code yet, so we cannot apply vcg usefully. *)
  (* First we expand the function call and defer the overall precondition. *)
  apply vcg_step
   defer
   (* Now we annotate the loop with the correct invariant and termination measure. *)
   apply (subst whileAnno_def)
   apply (subst whileAnno_def [symmetric,
     where I=" \<lbrace> \<acute>a = fibo32 (\<^bsup>t\<^esup>n - \<acute>n) \<and> \<acute>n \<le> \<^bsup>t\<^esup>n \<and> (\<acute>n \<noteq> 0 \<longrightarrow> (\<acute>b = fibo32 (\<^bsup>t\<^esup>n + 1 - \<acute>n))) \<rbrace>"
     and V="measure (\<lambda>s. unat (n_' s))"])
   apply vcg
  (* It is mostly word arithmetic from here on. *)
    apply (simp add: scast_def field_simps)
    apply clarsimp
    apply (case_tac "n = 0")
     apply clarsimp
    apply (case_tac "n = 1")
     apply (rename_tac n1, subgoal_tac "n1 = 1")
      apply simp
     apply unat_arith
    apply (rename_tac n1, case_tac "n1 = 1")
     apply simp
    apply clarsimp
    apply safe
       apply (metis linear word_must_wrap)
      apply (rule fibo32_rec)
        (* unat_arith is too slow for this subgoal *)
        apply (subst word_less_nowrapI'[where k = 2 and z = "-1"])
           apply (subgoal_tac "n1 \<ge> 2")
            apply (metis word_n1_ge word_sub_le_iff word_sub_mono)
           apply unat_arith
          apply simp
         apply simp
        apply simp
       apply (simp add: field_simps)+
   apply (simp add: fibo32.simps)
  apply (simp add: scast_def fibo32.simps)
done

(* And the recursive version. *)
thm fib_body_def

lemma fib_simpl_spec: "\<forall>n. \<Gamma>,\<Theta>\<turnstile>\<^sub>t\<lbrace>\<acute>n=n\<rbrace>  PROC fib(\<acute>n,\<acute>ret__unsigned) \<lbrace>\<acute>ret__unsigned = fibo32 n\<rbrace>"
  apply (hoare_rule HoareTotal.ProcRec1[where r = "measure (\<lambda>(s, d). unat \<^bsup>s\<^esup>n)"])
  apply (unfold creturn_def | vcg_step)+
  apply (subst fibo32.simps, simp)
  apply (subst fibo32.simps, simp)
  apply (subst fibo32.simps[where n = n])
  apply unat_arith
  done

(*
 * We need to temporarily leave the local context to run autocorres.
 * Normally, we would run autocorres immediately after install_C_file.
 *)
end (* context fib *)

autocorres [unsigned_word_abs = fib_linear] "fib.c"

context fib begin

thm fib_linear'_def
thm fib'.simps fib'.simps[unfolded fun_app_def, folded One_nat_def]
thm call_fib'_def call_fib'_def[simplified]

(*
 * fib_linear\<^bsub>C\<^esub> has been lifted to fib_linear', using the option monad.
 * The option monad expresses programs that read the heap
 * and may fail. fib_linear\<^bsub>C\<^esub> does not read the heap, but its loop
 * might fail to terminate, so it cannot be a simple HOL function.
 *
 * Note that arithmetic in fib_linear' has been converted to type @{typ nat}.
 * This conversion is enabled by the word_abs option.
 * fib_linear' still matches the C code as long as calculations do not wrap around;
 * AutoCorres inserts an extra guard to ensure this.
 *)

thm fib_linear'_def

(* Here we prove that fib_linear' implements fibo, assuming that
 * no calculations wrap around. *)
lemma fib_linear'_correct: "ovalid (\<lambda>_. True) (fib_linear' n) (\<lambda>r s. r = fibo n)"
  unfolding fib_linear'_def
  (* The loop invariant, as before. *)
  apply (subst owhile_add_inv
    [where I = "\<lambda>(a, b, i) s. i \<le> n \<and> a = fibo (n - i) \<and> (i \<noteq> 0 \<longrightarrow> (b = fibo (n - i + 1)))"])
  apply wp
     apply safe
        (* Again, we prove largely arithmetical facts. However, these
         * proofs are easier because we are using the @{typ nat} type. *)
        apply (fastforce intro: arg_cong[where f = fibo])
       apply (simp add: Suc_diff_le)
      apply (fastforce intro: fiboI simp: field_simps)
     apply simp
    apply (rename_tac b s, case_tac b, simp, simp)
   apply (simp_all add: fibo.simps)
  done

(* Here we prove that fib_linear' terminates, and calculations do not overflow
 * for Fibonacci numbers below UINT_MAX.
 * This involves proving something similar to fibo32_is_fibo, so we
 * do not need that theorem to interpret this one.
 *
 * NB: Because the variable b is ahead of the Fibonacci number
 *     being calculated, we need to consider integer wraparound for
 *     fibo (Suc n) instead of fibo n. *)
lemma fib_linear'_term: "no_ofail (\<lambda>_. fibo (Suc n) < UINT_MAX) (fib_linear' n)"
  (* We would like to use the wp tactic, so we will translate our goal into
     ovalidNF form. *)
  unfolding fib_linear'_def no_ofail_is_ovalidNF
  apply (subst owhile_add_inv
    [where I = "\<lambda>(a, b, i) s. i \<le> n \<and> a = fibo (n - i) \<and> b = fibo (n - i + 1) \<and> fibo (Suc n) \<le> UINT_MAX"
       and M = "\<lambda>(_, _, i) _. i"])
  apply wp
     apply safe
         apply (fastforce intro: le_trans[rotated] add_le_mono simp: fibo_alt_def[where n = "Suc n"] fibo_mono)
        apply arith
       apply (simp add: field_simps Suc_diff_le)
      apply (fastforce intro: fiboI simp: field_simps)
     apply wp
     apply simp
    apply (simp_all add: fibo.simps)
  done

(* And we are done. *)
lemma fib_linear'_proof: "ovalidNF (\<lambda>_. fibo (Suc n) < UINT_MAX) (fib_linear' n) (\<lambda>r _. r = fibo n)"
  by (metis ovalidNF_combine ovalid_pre_imp fib_linear'_correct fib_linear'_term)




(* WIP: convert and prove in nondet_monad *)

(* First, set up the conversion... *)
lemma validE_NF_validNF: "validE_NF P (liftE f) Q (K (K False)) \<Longrightarrow> validNF P f Q"
  unfolding validE_NF_def validE_def validNF_def valid_def no_fail_def liftE_def K_def
  apply monad_eq
  apply fastforce
  done

lemma [ts_rule option unlift]: "oreturn a = ogets (\<lambda>_. a)"
  by (simp add: oreturn_def ogets_def)

declare liftE_liftE[symmetric, ts_rule option unlift]

lemma gets_theE_split[ts_rule option unlift]:
  "gets_theE (case p of (x, y) \<Rightarrow> f x y) = (case p of (x, y) \<Rightarrow> gets_theE (f x y))"
  apply (simp split: prod.splits)
  done

declare gets_theE_L2_while[symmetric, where n = "[]", ts_rule option unlift]
declare K_bind_def[ts_rule option unlift]

lemma nondet_fib_linear'_proof: "\<lbrace> \<lambda>s. fibo (Suc n) \<le> UINT_MAX \<and> P s \<rbrace> gets_the (fib_linear' n) \<lbrace> \<lambda>r s. r = fibo n \<and> P s \<rbrace>!"
  unfolding fib_linear'_def
  apply (rule validE_NF_validNF)
  apply (subst fun_cong[OF gets_theE_def[symmetric, THEN meta_eq_to_obj_eq]])
  (* Then it works! *)
  apply (monad_convert nondet "gets_theE _")

  apply (subst whileLoop_add_inv
    [where I="\<lambda>(a', b', n') s. a' = fibo (n - n') \<and> n' \<le> n \<and> (n' \<noteq> 0 \<longrightarrow> (b' = fibo (n - n' + 1))) \<and> fibo (Suc n) \<le> UINT_MAX \<and> P s"
       and M="\<lambda>((_, _, n'), _). n'"])
  apply wp
    apply safe
           apply (fastforce intro: arg_cong[where f = fibo])
          apply arith
         apply (fastforce intro: fiboI simp: field_simps)
        apply simp
       apply (fastforce intro: le_trans[rotated] simp: fiboI field_simps fibo_mono)
      apply simp
     apply simp
    apply (simp_all add: UINT_MAX_def fibo.simps)
  done

(*
 * Now for the recursive function fib\<^bsub>C\<^esub>.
 * The lifted function fib' is a recursive function in HOL, but all HOL functions
 * must be well-founded (ie. terminate) and AutoCorres cannot prove this.
 * Instead, fib' gets an extra parameter called “measure”, which limits the
 * recursion depth. With this recursion limit, it is obvious that
 * fib' terminates, so fib' can be defined as a HOL function.
 *)
thm fib'.simps (* Just a reminder *)
(*
 * Like fib_linear\<^bsub>C\<^esub>, fib\<^bsub>C\<^esub> is lifted to the option monad. If the measure parameter
 * is too small, fib' will fail instead of giving the result that would be
 * returned by fib\<^bsub>C\<^esub>.
 *)

(*
 * AutoCorres also generates a \<^bitalic>measure function\<^eitalic> for fib'. This function is
 * used to generate the measure parameter anywhere fib' is called. For example,
 *
 *   void call_fib(void) { fib(42); }
 *
 * is translated to:
 *)
thm call_fib'_def
(*
 * The measure function receives all of the information needed, in principle,
 * to determine an upper bound on the call depth (if there is one).
 * Namely, the function arguments and the global program state.
 *)
term measure_of'_fib
(*
 * measure_of'_fib does not actually have a definition, yet.
 * To give it a sensible definition, we need to work out the maximum
 * recursion depth, and AutoCorres does not know how to do that.
 * We will manually define the function later.
 *)


(*
 * But first, let us prove the correctness of fib'.
 * Again, we prove partial correctness separately, assuming that fib'
 * does not return None.
 *)

lemma fib'_correct_rec_helper:
  assumes ind: "\<And>y P m. ovalid (\<lambda>_. y < x \<and> P (fibo32 y)) (fib' m y) (\<lambda>r _. P r)"
  shows "ovalid (\<lambda>_. P (fibo32 x)) (fib' m x) (\<lambda>r _. P r)"
  apply (subst fib'.simps)
  apply (clarsimp simp: unat_eq_of_nat)
  apply (wp ind)
  apply (clarsimp simp: split: if_split_asm)
  apply safe
      apply (subst (asm) fibo32.simps, simp)
     apply (subst (asm) fibo32.simps, simp)
    apply unat_arith
   apply unat_arith
  apply (subst (asm) fibo32.simps, simp)
  done

lemma fib'_correct: "ovalid P (fib' m n) (\<lambda>r s. P s \<and> r = fibo32 n)"
  apply (subgoal_tac "\<And>P. ovalid (\<lambda>_. P (fibo32 n)) (fib' m n) (\<lambda>r _. P r)")
   apply (unfold ovalid_def, fast)[1]
  apply (induct n arbitrary: P m rule: less_induct)
  apply (subgoal_tac "\<And>y P m. ovalid (\<lambda>_. y < x \<and> P (fibo32 y)) (fib' m y) (\<lambda>r _. P r)")
   apply (rule fib'_correct_rec_helper)
   apply (unfold ovalid_def, fast)[1]
  apply (unfold ovalid_def)
  apply blast
  done

lemma fib'_term_rec_helper:
  assumes ind: "\<And>y P rec_measure'. ovalidNF (\<lambda>_. y < x \<and> unat y < rec_measure' \<and> P) (fib' rec_measure' y) (\<lambda>_ _. P)"
  shows "ovalidNF (\<lambda>_. unat x < rec_measure') (fib' rec_measure' x) (\<lambda>_ _. True)"
  apply (subst fib'.simps)
  apply (wp ind)
  apply simp
  apply unat_arith (* slow *)
  done

lemma fib'_term: "no_ofail (\<lambda>_. rec_measure' > unat n) (fib' rec_measure' n)"
  apply (subst no_ofail_is_ovalidNF)
  apply (induct n arbitrary: rec_measure' rule: less_induct)
  apply (subgoal_tac "\<And>y P rec_measure'. ovalidNF (\<lambda>_. y < x \<and> unat y < rec_measure' \<and> P) (fib' rec_measure' y) (\<lambda>_ _. P)")
  apply (rule fib'_term_rec_helper, assumption)
  apply (metis (full_types) ovalidNF_assume_pre)
  done

(* The overall correctness proof. *)
lemma fib'_spec: "ovalidNF (\<lambda>s. P s \<and> m > unat n) (fib' m n) (\<lambda>r s. P s \<and> r = fibo32 n)"
  apply (rule ovalidNF_combine)
  apply (wp fib'_correct, simp)
  apply (wp fib'_term, simp)
  done

(*
If fib\<^bsub>C\<^esub> was lifted to the state monad...
Once we get hoare triples and wp reasoning on the option monad,
the proof might also look like this.

(* isar proof lets us rewrite the inductive assumption r and pass it to wp *)
lemma fib2'_correct: "\<lbrace> \<lambda>_. P (fibo32 n) \<rbrace> fib2' m n \<lbrace> \<lambda>r s. P r \<rbrace>"
proof (induct n arbitrary: P m rule: less_induct)
   fix x P m
   assume r: "\<And>y P m. y < x \<Longrightarrow> \<lbrace>  \<lambda>_. P (fibo32 y) \<rbrace> fib2' m y \<lbrace> \<lambda>r s. P r \<rbrace>"

   have r': "\<And>y P m. \<lbrace>  \<lambda>_. y < x \<and> P (fibo32 y) \<rbrace> fib2' m y \<lbrace> \<lambda>r s. P r \<rbrace>"
    apply (rule hoare_assume_pre)
    apply clarsimp
    apply (insert r)
    apply (clarsimp simp: valid_def)
    done

   show "\<lbrace> \<lambda>_. P (fibo32 x) \<rbrace> fib2' m x \<lbrace> \<lambda>r s. P r \<rbrace>"
     apply (subst fib2'.simps)
     apply (wp r')
    apply auto
    apply (simp_all add: fibo32.simps)
    apply unat_arith+
    done
qed
*)


(* Finally, we can show that anyone who calls fib' will get the correct result. *)
lemma fib'_call:
  "fib' (unat n + 1) n s = Some (fibo32 n)"
  using fib'_spec[unfolded ovalidNF_def]
  apply fastforce
  done

lemma "\<lbrace> P \<rbrace> call_fib' \<lbrace> \<lambda>_. P \<rbrace>!"
  including nf_no_pre
  apply (unfold call_fib'_def)
  apply wp
   apply (blast intro: fib'_call)
  apply (force simp: fib'_mono option_monad_mono_eq)
  done

end (* context fib *)

end
