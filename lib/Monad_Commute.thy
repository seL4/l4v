(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* The monad_commute predicate + lemmas. *)

theory Monad_Commute
  imports
    Monads.Nondet_Monad_Equations
    Monad_Lists (* for mapM_x *)
begin


definition monad_commute where
  "monad_commute P a b \<equiv>
   \<forall>s. (P s \<longrightarrow> ((do x\<leftarrow>a;y\<leftarrow>b; return (x, y) od) s) = ((do y\<leftarrow>b;x\<leftarrow>a; return (x, y) od) s))"


lemma monad_eq:
  "a s = b s \<Longrightarrow> (a >>= g) s = (b >>= g) s"
  by (auto simp: bind_def)

lemma monad_commute_simple:
  "\<lbrakk> monad_commute P a b; P s \<rbrakk> \<Longrightarrow> (do x\<leftarrow>a;y\<leftarrow>b; g x y od) s = (do y\<leftarrow>b;x\<leftarrow>a; g x y od) s"
  apply (clarsimp simp: monad_commute_def)
  apply (drule spec)
  apply (erule(1) impE)
  apply (drule_tac g = "(\<lambda>t. g (fst t) (snd t))" in monad_eq)
  apply (simp add: bind_assoc)
  done

lemma monad_commute_simple':
  "monad_commute \<top> a b \<Longrightarrow> (do x \<leftarrow> a; y \<leftarrow> b; g x y od) = (do y \<leftarrow> b; x \<leftarrow> a; g x y od)"
  apply (clarsimp simp: monad_commute_def)
  apply (fastforce simp: bind_def' return_def)
  done

lemma commute_commute:
  "monad_commute P f h \<Longrightarrow> monad_commute P h f"
  apply (simp (no_asm) add: monad_commute_def)
  apply (clarsimp)
  apply (erule monad_commute_simple[symmetric])
  apply simp
  done

lemma assert_commute: "monad_commute (K G) (assert G) f"
  by (clarsimp simp: assert_def monad_commute_def)

lemma cond_fail_commute: "monad_commute (K (\<not>G)) (when G fail) f"
  by (clarsimp simp: when_def fail_def monad_commute_def)

lemma return_commute: "monad_commute \<top> (return a) f"
  by (clarsimp simp: return_def bind_def monad_commute_def)

lemma monad_commute_guard_imp:
  "\<lbrakk>monad_commute P f h; \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> monad_commute Q f h"
  by (clarsimp simp: monad_commute_def)

lemma monad_commute_split:
  "\<lbrakk>\<And>r. monad_commute (Q r) f (g r); monad_commute P f h; \<lbrace>P'\<rbrace> h \<lbrace>\<lambda>r. Q r\<rbrace>\<rbrakk>
   \<Longrightarrow> monad_commute (P and P') f (h>>=g)"
  apply (simp (no_asm) add: monad_commute_def)
   apply (clarsimp simp: bind_assoc)
   apply (subst monad_commute_simple)
    apply simp+
   apply (rule_tac Q = "(\<lambda>x. Q x)" in monad_eq_split)
   apply (subst monad_commute_simple[where a = f])
    apply assumption
    apply simp+
  done

lemma monad_commute_get:
  assumes hf: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. P\<rbrace>"
    and hg: "\<And>P. \<lbrace>P\<rbrace> g \<lbrace>\<lambda>r. P\<rbrace>"
    and eptyf: "empty_fail f" "empty_fail g"
  shows "monad_commute \<top> f g"
proof -
  have fsame: "\<And>a b s. (a,b) \<in> fst (f s) \<Longrightarrow> b = s"
    by (drule use_valid[OF _ hf],auto)
  have gsame: "\<And>a b s. (a,b) \<in> fst (g s) \<Longrightarrow> b = s"
    by (drule use_valid[OF _ hg],auto)
  note ef = empty_fail_not_snd[OF _ eptyf(1)]
  note eg = empty_fail_not_snd[OF _ eptyf(2)]
  show ?thesis
    apply (simp add: monad_commute_def)
    apply (clarsimp simp: bind_def split_def return_def)
    apply (intro conjI)
     apply (rule set_eqI)
     apply (rule iffI)
      apply (clarsimp simp:Union_eq)
      apply (frule fsame)
      apply clarsimp
      apply (frule gsame)
      apply (metis fst_conv snd_conv)
     apply (clarsimp simp:Union_eq)
     apply (frule gsame)
     apply clarsimp
     apply (frule fsame)
     apply clarsimp
     apply (metis fst_conv snd_conv)
    apply (rule iffI)
     apply (erule disjE)
      apply (clarsimp simp: image_def)
      apply (metis fsame)
     apply (clarsimp simp: image_def)
     apply (drule eg)
     apply clarsimp
     apply (rule bexI [rotated], assumption)
     apply (frule gsame)
     apply clarsimp
    apply (erule disjE)
     apply (clarsimp simp: image_def dest!: gsame)
    apply (clarsimp simp: image_def)
    apply (drule ef)
    apply clarsimp
    apply (frule fsame)
    apply (erule bexI[rotated])
    apply simp
    done
qed

lemma mapM_x_commute:
  assumes commute: "\<And>r. monad_commute (P r) a (b r)"
     and   single: "\<And>r x. \<lbrace>P r and K (f r \<noteq> f x) and P x\<rbrace> b x \<lbrace>\<lambda>v. P r \<rbrace>"
  shows "monad_commute (\<lambda>s. (distinct (map f list)) \<and> (\<forall>r\<in> set list. P r s)) a (mapM_x b list)"
  apply (induct list)
   apply (clarsimp simp: mapM_x_Nil return_def bind_def monad_commute_def)
  apply (clarsimp simp: mapM_x_Cons)
  apply (rule monad_commute_guard_imp)
   apply (rule monad_commute_split)
     apply assumption
    apply (rule monad_commute_guard_imp[OF commute])
   apply assumption
   apply (wp hoare_vcg_const_Ball_lift)
   apply (rule single)
  apply (clarsimp simp: image_def)
  apply auto
  done

(* Proof needs to be different from mapM_x_commute, to eliminate "distinct" *)
lemma mapM_x_commute_T:
  assumes commute: "\<And>r. monad_commute \<top> (b r) a"
  shows "monad_commute \<top> (mapM_x b xs) a"
  apply (induct xs)
   apply (clarsimp simp: mapM_x_Nil return_def bind_def monad_commute_def)
  apply (clarsimp simp: mapM_x_Cons)
  apply (rule monad_commute_guard_imp)
   apply (rule commute_commute, rule monad_commute_split)
     apply (rule commute_commute, assumption)
    apply (rule commute_commute, rule commute)
   apply wp
  apply clarsimp
  done

lemma commute_name_pre_state:
  assumes "\<And>s. P s \<Longrightarrow> monad_commute ((=) s) f g"
  shows "monad_commute P f g"
  using assms
  by (clarsimp simp: monad_commute_def)

lemma commute_rewrite:
  assumes rewrite: "\<And>s. Q s \<Longrightarrow> f s = t s"
  assumes hold: "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>x. Q\<rbrace>"
  shows  "monad_commute R t g \<Longrightarrow> monad_commute (P and Q and R) f g"
  apply (clarsimp simp: monad_commute_def bind_def split_def return_def)
  apply (drule_tac x = s in spec)
  apply (clarsimp simp: rewrite[symmetric])
  apply (intro conjI)
   apply (rule set_eqI)
   apply (rule iffI)
    apply clarsimp
    apply (rule bexI[rotated],assumption)
    apply (subst rewrite)
     apply (rule use_valid[OF _ hold])
      apply simp+
    apply (erule bexI[rotated],simp)
   apply clarsimp
   apply (rule bexI[rotated],assumption)
   apply (subst rewrite[symmetric])
    apply (rule use_valid[OF _ hold])
     apply simp+
   apply (erule bexI[rotated],simp)
  apply (intro iffI)
   apply clarsimp
   apply (rule bexI[rotated],assumption)
   apply simp
   apply (subst rewrite)
    apply (erule(1) use_valid[OF _ hold])
   apply simp
  apply (clarsimp)
  apply (drule bspec,assumption)
  apply clarsimp
  apply (metis rewrite use_valid[OF _ hold])
  done

lemma commute_grab_asm:
  "(F \<Longrightarrow> monad_commute P f g) \<Longrightarrow> (monad_commute (P and (K F)) f g)"
  by (clarsimp simp: monad_commute_def)

lemma select_modify_comm:
  "(do b \<leftarrow> select S; _ \<leftarrow> modify f; use b od) =
   (do _ \<leftarrow> modify f; b \<leftarrow> select S; use b od)"
  by (simp add: bind_def split_def select_def simpler_modify_def image_def)

lemma select_f_modify_comm:
  "(do b \<leftarrow> select_f S; _ \<leftarrow> modify f; use b od) =
   (do _ \<leftarrow> modify f; b \<leftarrow> select_f S; use b od)"
  by (simp add: bind_def split_def select_f_def simpler_modify_def image_def)

end