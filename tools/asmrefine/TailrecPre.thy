(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory TailrecPre
imports
  "Word_Lib.WordSetup"
  "Lib.Lib"
begin

definition
  "tailrec_pre (f1 :: 'a \<Rightarrow> 'a) guard precondition (x::'a) \<equiv>
    (\<forall>k. (\<forall>m. m < k \<longrightarrow> guard ((f1 ^^ m) x)) \<longrightarrow> precondition ((f1 ^^ k) x)) \<and>
    (\<exists>n. \<not> guard ((f1 ^^ n) x))"

definition
  "short_tailrec_pre (f :: 'a \<Rightarrow> ('a + 'b) \<times> bool) \<equiv>
     tailrec_pre (theLeft o fst o f) (isLeft o fst o f) (snd o f)"

partial_function (tailrec)
  tailrec :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b"
where
 "tailrec f1 f2 g x = (if g x then tailrec f1 f2 g (f1 x) else f2 x)"

lemma tailrec_steps:
  "g x \<Longrightarrow> tailrec f1 f2 g x = tailrec f1 f2 g (f1 x)"
  "\<not> g x \<Longrightarrow> tailrec f1 f2 g x = f2 x"
  by (simp_all add: tailrec.simps cong: if_weak_cong split del: if_split)

definition
  "short_tailrec (f :: 'a \<Rightarrow> ('a + 'b) \<times> bool) \<equiv>
     tailrec (theLeft o fst o f) (theRight o fst o f) (isLeft o fst o f)"

definition
  "short_tailrec_pair stp v = (short_tailrec_pre stp v, short_tailrec stp v)"

lemma tailrec_pre_lemma:
  "!f1 g p x. tailrec_pre f1 g p (x::'a) = (p x \<and> (g x \<longrightarrow> tailrec_pre f1 g p (f1 x)))"
  apply (clarsimp simp add: tailrec_pre_def)
  apply (rule iffI)
   apply (rule conjI)
    apply auto[1]
   apply clarsimp
   apply (rule conjI[rotated])
    apply (case_tac n)
     apply simp
    apply (clarsimp simp: funpow_swap1)
    apply auto[1]
   apply clarsimp
   apply (drule_tac x="Suc n" for n in spec, simp add: funpow_swap1)
   apply (erule mp)
   apply clarsimp
   apply (case_tac m, simp_all add: funpow_swap1)[1]
  apply (case_tac "g x")
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (case_tac k)
     apply auto[1]
    apply (simp_all add: funpow_swap1)[1]
    apply (erule allE, erule impE)
     prefer 2
     apply assumption
    apply (rule allI)
    apply (rule impI)
    apply (drule_tac x="Suc m" in spec, simp_all add: funpow_swap1)
   apply (rule_tac x="Suc n" in exI)
   apply (simp add: funpow_swap1)
  apply (rule conjI)
   prefer 2
   apply (rule_tac x="0" in exI)
   apply auto[1]
  apply (rule allI)
  apply (rule impI)
  apply (case_tac k)
  apply auto
  done

lemma tailrec_pre_lemmata:
  "g x \<Longrightarrow> tailrec_pre f1 g p (x::'a) = (p x \<and> tailrec_pre f1 g p (f1 x))"
  "\<not> g x \<Longrightarrow> tailrec_pre f1 g p (x::'a) = p x"
  by (metis tailrec_pre_lemma)+

theorem short_tailrec_thm:
  "\<forall>f x. short_tailrec f x = (if isLeft (fst (f x))
     then short_tailrec f (theLeft (fst (f x)))
     else theRight (fst (f x))) \<and>
   (short_tailrec_pre f x = (snd (f x)
     \<and> (isLeft (fst (f x)) \<longrightarrow> short_tailrec_pre f (theLeft (fst (f x))))))"
  apply (clarsimp simp add: short_tailrec_pre_def short_tailrec_def)
  apply (simp add: tailrec_pre_lemmata tailrec_steps)
  done

lemma short_tailrec_pair_single_step:
  "\<forall>v. \<not> isLeft (fst (f v))
    \<Longrightarrow> short_tailrec_pair f = (\<lambda>v. let (rv, b) = (f v) in (b, theRight rv))"
  apply (rule ext)
  apply (simp add: short_tailrec_pair_def split_def Let_def)
  apply (simp add: short_tailrec_thm cong: imp_cong[OF _ refl] if_weak_cong)
  done

lemma eq_true_imp:
  "(x ==  Trueprop True) ==> PROP x"
  apply auto
  done

lemma forall_true:
  "(!x. True) = True"
  apply auto
  done

lemmas split_thm = split_conv

definition
  line_number :: "word32 \<Rightarrow> bool"
where
  "line_number n \<equiv> True"

end
