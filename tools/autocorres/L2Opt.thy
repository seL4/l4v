(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory L2Opt
imports L2Defs L2Peephole
begin

(* Flow-sensitive simplification rules for L2 programs. *)
named_theorems L2flow

(*
 * The monads "A" and "B" are equivalent under precondition "P".
 * Additionally, under this precondition, they always leave the
 * postcondition "Q" (normally) or "E" (if an exception occurs).
 *)
definition
  "monad_equiv P A B Q E \<equiv> (\<forall>s. P s \<longrightarrow> A s = B s) \<and> \<lbrace> P \<rbrace> A \<lbrace> Q \<rbrace>, \<lbrace> E \<rbrace>"

lemma monad_equivI [intro]:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> A s = B s; \<lbrace> P \<rbrace> A \<lbrace> Q \<rbrace>, \<lbrace> E \<rbrace> \<rbrakk> \<Longrightarrow> monad_equiv P A B Q E"
  apply (clarsimp simp: monad_equiv_def)
  done

lemma monad_equiv_eqI [intro]:
  "\<lbrakk> \<lbrace> P \<rbrace> A \<lbrace> Q \<rbrace>, \<lbrace> E \<rbrace> \<rbrakk> \<Longrightarrow> monad_equiv P A A Q E"
  apply (clarsimp simp: monad_equiv_def)
  done

lemma monad_equiv_eq:
    "monad_equiv (\<lambda>_. True) A B X Y \<Longrightarrow> A = B"
  apply (rule ext)
  apply (clarsimp simp: monad_equiv_def)
  done

lemma monad_equiv_triv [L2flow]:
    "monad_equiv P A A (\<lambda>_ _. \<exists>s. P s) (\<lambda>_ _. \<exists>s. P s)"
  apply rule
  apply wp
  apply force
  done

lemma monad_equiv_symmetric:
  "monad_equiv P A B X Y = monad_equiv P B A X Y"
  apply (clarsimp simp: monad_equiv_def validE_def2 Ball_def split: sum.splits)
  apply force
  done

lemma monad_equivD: "\<lbrakk> monad_equiv P A B R E; P s \<rbrakk> \<Longrightarrow> A s = B s"
  apply (clarsimp simp: monad_equiv_def)
  done

(*
 * Show that under condition "P", the values "A" and "B" are equal.
 *
 * We use this to simplify expressions inside our monads in a (somewhat)
 * controlled fashion.
 *)
definition "simp_expr P A B \<equiv> P \<longrightarrow> A = B"

lemma simp_expr_triv: "simp_expr P A A"
  apply (clarsimp simp: simp_expr_def)
  done

lemma simp_expr_P_cong:
  "\<lbrakk> P = P' \<rbrakk> \<Longrightarrow> simp_expr P A B = simp_expr P' A B"
  apply (clarsimp simp: simp_expr_def)
  done

lemma simp_expr_rhs_cong [cong]:
  "\<lbrakk> P = P'; P' \<Longrightarrow> B = B' \<rbrakk> \<Longrightarrow> simp_expr P A B = simp_expr P' A B'"
  apply (clarsimp simp: simp_expr_def simp_implies_def)
  done

lemma simp_expr_weaken:
  "\<lbrakk> simp_expr P A B; Q \<Longrightarrow> P \<rbrakk> \<Longrightarrow> simp_expr Q A B"
  apply (clarsimp simp: simp_expr_def)
  done

(*
 * Monad simplification rules.
 *
 * When solving "monad_equiv P A B R E", the l2_opt tactics assume that P is concrete;
 * to ensure this, monad_equiv rules should result in R being instantiated.
 * See e.g. monad_equiv_unreachable where we have to constrain the rule.
 *)

lemma monad_equiv_gets [L2flow]:
    "simp_expr True v v' \<Longrightarrow> monad_equiv P (L2_gets (\<lambda>s. v s) n) (L2_gets (\<lambda>s. v' s) n)
        (\<lambda>r s. P s \<and> r = v' s) (\<lambda>_ _. False)"
  apply rule
   apply (clarsimp simp: L2_defs simp_expr_def)+
  apply wpsimp
  done

lemma monad_equiv_throw [L2flow]:
    "simp_expr True v v' \<Longrightarrow>
       monad_equiv P (L2_throw v n) (L2_throw v' n) (\<lambda>_ _. False) (\<lambda>r s. P s \<and> r = v')"
  apply (clarsimp simp: monad_equiv_def L2_defs simp_expr_def)
  apply wp
  apply force
  done

lemma monad_equiv_guard:
    "\<lbrakk> \<And>s. simp_expr (P s) (G s) (G' s) \<rbrakk> \<Longrightarrow>
        monad_equiv P (L2_guard (\<lambda>s. G s)) (L2_guard (\<lambda>s. G' s)) (\<lambda>r s. P s \<and> G' s \<and> r = ()) (\<lambda>_ _. False)"
  apply (clarsimp simp: monad_equiv_def L2_defs simp_expr_def)
  apply rule
   apply (clarsimp simp: liftE_def guard_def bind_def in_return snd_return)
  apply wp
  apply force
  done

(* We use this weaker form of guard simplification to prevent bound
 * variables being expanded inside of guard statements. *)
lemma monad_equiv_guard' [L2flow]:
    "\<lbrakk> \<And>s. simp_expr True (G s) (G' s) \<rbrakk> \<Longrightarrow>
        monad_equiv P (L2_guard (\<lambda>s. G s)) (L2_guard (\<lambda>s. G' s)) (\<lambda>r s. P s \<and> G' s \<and> r = ()) (\<lambda>_ _. False)"
  apply (rule monad_equiv_guard)
  apply (rule simp_expr_weaken)
   apply assumption
  apply simp
  done

lemma monad_equiv_guard_False [L2flow]:
    "\<lbrakk> \<And>s. simp_expr (P s) False (G s) \<rbrakk>
          \<Longrightarrow> monad_equiv P (L2_guard G) (L2_fail) (\<lambda>_ _. False) (\<lambda>_ _. False)"
  apply (monad_eq simp: L2_defs monad_equiv_def simp_expr_def validE_def2)
  done

lemma monad_equiv_guard_True [L2flow]:
    "\<lbrakk> \<And>s. simp_expr (P s) True (G s) \<rbrakk>
          \<Longrightarrow> monad_equiv P (L2_guard G) L2_skip (\<lambda>r s. P s \<and> r = ()) (\<lambda>_ _. False)"
  apply (auto simp: L2_defs simp_expr_def guard_def liftE_def return_def returnOk_def bind_def validE_def valid_def)
  done

lemma monad_equiv_guard_conj [L2flow]:
    "\<lbrakk> monad_equiv P (L2_guard G1) G1' R1 E1;
       monad_equiv (\<lambda>s. R1 () s) (L2_guard G2) G2' R2 E2 \<rbrakk> \<Longrightarrow>
        monad_equiv P (L2_guard (\<lambda>s. G1 s \<and> G2 s)) (L2_seq G1' (\<lambda>_. G2')) (\<lambda>r s. R2 () s) (\<lambda>_ _. False)"
  apply (subst (asm) (1 2) monad_equiv_symmetric)
  apply (subst monad_equiv_symmetric)
  apply rule
   apply (monad_eq simp: L2_defs monad_equiv_def validE_def2 Bex_def Ball_def split: sum.splits)
   apply fast
  apply (monad_eq simp: monad_equiv_def L2_defs validE_def2 Ball_def split: sum.splits)
  apply fast
  done

lemma monad_equiv_unknown [L2flow]:
    "monad_equiv P (L2_unknown name) (L2_unknown name) (\<lambda>r s. P s) (\<lambda>_ _. False)"
  apply (clarsimp simp: monad_equiv_def L2_defs)
  apply (wp select_wp)
  apply force
  done

lemma monad_equiv_modify [L2flow]:
    "\<lbrakk> \<And>s. simp_expr True (m s) (m' s) \<rbrakk> \<Longrightarrow>
        monad_equiv P (L2_modify (\<lambda>s. m s)) (L2_modify (\<lambda>s. m' s)) (\<lambda>r s'. \<exists>s. P s \<and> m' s = s' \<and> r = ()) (\<lambda>_ _. False)"
  apply rule
   apply (clarsimp simp: L2_defs simp_expr_def liftE_def modify_def put_def get_def bind_def)
  apply (clarsimp simp: L2_defs simp_expr_def)
  apply wp
  apply force
  done

lemma monad_equiv_spec [L2flow]:
    "\<lbrakk> \<And>s s'. simp_expr True ((s, s') \<in> S) (S' s s') \<rbrakk> \<Longrightarrow>
        monad_equiv P (L2_spec S) (L2_spec ({(s, s'). S' s s'})) (\<lambda>r s. \<exists>s. P s) (\<lambda>_ _. False)"
  apply rule
   apply (clarsimp simp: L2_defs simp_expr_def liftE_def spec_def bind_def)
  apply (clarsimp simp: L2_defs)
  apply wp
  apply force
  done

lemma monad_equiv_fail [L2flow]:
    "monad_equiv P L2_fail L2_fail (\<lambda>_ _. False) (\<lambda>_ _. False)"
  apply (clarsimp simp: monad_equiv_def L2_defs)
  done

lemma monad_equiv_condition [L2flow]:
  "\<lbrakk> \<And>s. simp_expr True (C s) (C' s);
     monad_equiv (\<lambda>s. P s \<and> C' s) L L' QL EL;
     monad_equiv (\<lambda>s. P s \<and> \<not> C' s) R R' QR ER \<rbrakk> \<Longrightarrow>
   monad_equiv P (L2_condition (\<lambda>s. C s) L R) (L2_condition (\<lambda>s. C' s) L' R')
      (\<lambda>r s. \<exists>s. P s) \<comment> \<open>Deliberately weak to avoid exponential growth.\<close>
      (\<lambda>r s. \<exists>s. P s)"
  apply rule
   apply (monad_eq simp: L2_defs monad_equiv_def simp_expr_def split: condition_splits)
  apply (monad_eq simp: L2_defs monad_equiv_def validE_def2 split: condition_splits sum.splits)
  apply force
  done

lemma monad_equiv_condition_True [L2flow]:
  "\<lbrakk> \<And>s. simp_expr (P s) (C s) True;
     monad_equiv P L L' QL EL \<rbrakk> \<Longrightarrow>
     monad_equiv P (L2_condition C L R) L' QL EL"
  unfolding L2_defs condition_def
  apply (monad_eq simp: simp_expr_def monad_equiv_def validE_def2 Ball_def split: sum.splits)
  done

lemma monad_equiv_condition_False [L2flow]:
  "\<lbrakk> \<And>s. simp_expr (P s) (C s) False;
     monad_equiv P R R' QR ER \<rbrakk> \<Longrightarrow>
     monad_equiv P (L2_condition C L R) R' QR ER"
  unfolding L2_defs condition_def
  apply (monad_eq simp: simp_expr_def monad_equiv_def validE_def2 Ball_def split: sum.splits)
  done

(* C-parser sometimes generates boolean expressions like
     if P then (if P then 1 else 0) else Q
   This simplifies the branches. *)
lemma monad_equiv_gets_if [L2flow]:
   "\<lbrakk> \<And>s. simp_expr (P s) True (b s) \<rbrakk> \<Longrightarrow>
       monad_equiv P (L2_gets (\<lambda>s. if (b s) then L else R) f)
                     (L2_gets (\<lambda>s. L) f) (%r s. P s) (\<lambda>r s. False)"
   "\<lbrakk> \<And>s. simp_expr (P s) False (b s) \<rbrakk> \<Longrightarrow>
       monad_equiv P (L2_gets (\<lambda>s. if (b s) then L else R) f)
                     (L2_gets (\<lambda>s. R) f) (%r s. P s) (\<lambda>r s. False)"
  apply (monad_eq simp: L2_defs simp_expr_def monad_equiv_def
         validE_def valid_def split: sum.splits)+
  done

lemma monad_equiv_seq [L2flow]:
  "\<lbrakk> monad_equiv P A A' Q E;
     \<And>x. monad_equiv (Q x) (B x) (B' x) (R x) (E2 x) \<rbrakk> \<Longrightarrow>
   monad_equiv P (L2_seq A (\<lambda>x. B x)) (L2_seq A' (\<lambda>x. B' x)) (\<lambda>r s. \<exists>r'. R r' r s) (\<lambda>r s. \<exists>s. P s)"
  apply rule
   apply (clarsimp simp: monad_equiv_def L2_defs simp_expr_def)
   apply (rule bindE_apply_cong)
    apply simp
   apply (clarsimp simp: validE_def valid_def)
   apply force
  apply (clarsimp simp: monad_equiv_def L2_defs
               validE_def valid_def in_bindE simp_expr_def split: sum.splits)
  apply (erule allE, erule (1) impE)+
  apply fastforce
  done

lemma monad_equiv_catch [L2flow]:
  "\<lbrakk> monad_equiv P A A' Q E;
    \<And>x. monad_equiv (E x) (B x) (B' x) (Q' x) (E2 x) \<rbrakk> \<Longrightarrow>
   monad_equiv P (L2_catch A (\<lambda>x. B x)) (L2_catch A' (\<lambda>x. B' x)) (\<lambda>r s. \<exists>s. P s) (\<lambda>r s. \<exists>r'. E2 r' r s)"
  apply rule
   apply atomize
   apply (clarsimp simp: simp_expr_def L2_defs monad_equiv_def)
   apply (erule allE, erule impE, assumption)
   apply (clarsimp simp: validE_def2 split: sum.splits)
   apply (erule allE, erule impE, assumption)
   apply (rule monad_state_eqI)
     apply (clarsimp simp: in_handleE')
     apply force
    apply (clarsimp simp: in_handleE')
    apply force
   apply (fastforce simp: snd_handleE')
  apply (clarsimp simp: monad_equiv_def L2_defs
      validE_def valid_def simp_expr_def in_handleE' split: sum.splits)
  apply (erule allE, erule (1) impE)+
  apply fastforce
  done

lemma monad_equiv_cong:
  "\<lbrakk> \<And>s. P s = P' s;
     \<And>s. P s \<Longrightarrow> A s = A' s;
     \<And>s. P s \<Longrightarrow> B s = B' s;
     \<And>s s' r. P s \<Longrightarrow> Q r s' = Q' r s';
     \<And>s s' r. P s \<Longrightarrow> R r s' = R' r s' \<rbrakk> \<Longrightarrow>
   monad_equiv P A B Q R = monad_equiv P' A' B' Q' R'"
  apply atomize
  apply (clarsimp simp: monad_equiv_def validE_def valid_def split: sum.splits)
  apply (rule iffI)
   apply clarsimp
   apply fastforce
  apply clarsimp
  apply fastforce
  done

lemma monad_equiv_while [L2flow]:
  assumes cond_simp: "\<And>s r. simp_expr True (c r s) (c' r s)"
  assumes body_equiv: "\<And>r. monad_equiv (\<lambda>s. (\<exists>s'. P s') \<and> c' r s) (B r) (B' r) (Q r) (E r)"
  assumes init_simp: "\<And>s r. simp_expr True x x'"
  shows "monad_equiv P (L2_while (\<lambda>r s. c r s) B x n) (L2_while (\<lambda>r s. c' r s) B' x' n) (\<lambda>r s. \<not> c' r s \<and> (\<exists>x. P x)) (\<lambda>r s. \<exists>x. E x r s)"
  apply (insert cond_simp [unfolded simp_expr_def] init_simp [unfolded simp_expr_def])
  apply rule
   apply (clarsimp simp: L2_while_def)
   apply (rule whileLoopE_cong [THEN fun_cong, THEN fun_cong])
     apply force
    apply (cut_tac r=r in body_equiv)
    apply (clarsimp simp: monad_equiv_def)
    apply (erule allE, erule impE, auto)[1]
   apply simp
  apply (clarsimp simp: L2_while_def)
  apply (rule validE_whileLoopE [where I="\<lambda>r s. \<exists>s. P s"])
    apply force
   apply (cut_tac r=r in body_equiv)
   apply (clarsimp simp: validE_def valid_def monad_equiv_def split: sum.splits)
   apply blast
  apply simp
  done

lemma monad_equiv_recguard [L2flow]:
  "\<lbrakk> monad_equiv P B B' Q E \<rbrakk> \<Longrightarrow>
    monad_equiv P (L2_recguard a B) (L2_recguard a B') Q E"
  apply rule
   apply (clarsimp simp: L2_recguard_def monad_equiv_def valid_def validE_def
        split: sum.splits condition_splits)
  apply (clarsimp simp: L2_recguard_def monad_equiv_def valid_def validE_def in_fail
       split: sum.splits condition_splits)
  done

lemma monad_equiv_unreachable' [L2flow]:
  "monad_equiv (\<lambda>_. False) L (L2_gets (\<lambda>_. undefined) [''L2Opt_internal_var'']) Q R"
  by (simp add: monad_equiv_def)

(* avoid leaving schematic Q in goal *)
lemma monad_equiv_unreachable [L2flow]:
  "monad_equiv (\<lambda>_. False) L (L2_gets (\<lambda>_. undefined) [''L2Opt_internal_var'']) (\<lambda>_ _. False) R"
  by (rule monad_equiv_unreachable')

lemma monad_equiv_split [L2flow]:
  "\<lbrakk> \<And>a b. monad_equiv (P (a, b)) (X a b) (Y a b) (Q a b) (E a b) \<rbrakk> \<Longrightarrow>
    monad_equiv (P x) (case x of (a, b) \<Rightarrow> X a b) (case x of (a, b) \<Rightarrow> Y a b)
          (case x of (a, b) \<Rightarrow> Q a b) (case x of (a, b) \<Rightarrow> E a b)"
  apply (clarsimp simp: monad_equiv_def validE_def valid_def split_def)
  done

lemma simp_expr_solve_constant: "\<lbrakk> A \<Longrightarrow> B = C \<rbrakk> \<Longrightarrow> simp_expr A B C"
  by (clarsimp simp: simp_expr_def)

lemma monad_equiv_weaken_pre':
  "\<lbrakk> \<And>s. P' s \<Longrightarrow> P s; monad_equiv P L R Q E \<rbrakk> \<Longrightarrow> monad_equiv P' L R Q E"
  by (fastforce simp: monad_equiv_def validE_def valid_def)

lemma monad_equiv_weaken_pre'':
  "\<lbrakk> P' \<equiv> P; monad_equiv P L R Q E \<rbrakk> \<Longrightarrow> monad_equiv P' L R Q E"
  by (fastforce simp: monad_equiv_def validE_def valid_def)

end
