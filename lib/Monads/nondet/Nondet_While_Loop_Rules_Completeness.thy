(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * This is a purely theoretical theory containing proofs
 * that the whileLoop rules in "Nondet_While_Loop_Rules" are complete.
 *
 * You probably don't care about this.
 *)
theory Nondet_While_Loop_Rules_Completeness
  imports Nondet_While_Loop_Rules
begin

lemma whileLoop_rule_strong_complete:
  "(\<lbrace>\<lambda>s'. s' = s\<rbrace> whileLoop C B r \<lbrace>\<lambda>r s. (r, mstate s) \<in> fst Q\<rbrace> \<and>
    (\<forall>r'' s''. (r'', mstate s'') \<in> fst Q \<and> env s'' = env s \<longrightarrow>
               \<lbrace>\<lambda>s'. s' = s\<rbrace> whileLoop C B r \<exists>\<lbrace>\<lambda>r s. r = r'' \<and> s = s''\<rbrace>) \<and>
    (snd Q \<longrightarrow> snd (whileLoop C B r s)) \<and>
    (\<not> snd Q \<longrightarrow> \<lbrace>\<lambda>s'. s' = s\<rbrace> whileLoop C B r \<lbrace>\<lambda>_ _. True\<rbrace>!)) =
   (whileLoop C B r s = Q)"
  apply (rule iffI)
   apply (rule whileLoop_rule_strong; clarsimp)
   apply (clarsimp simp: exs_valid_def)
   apply (smt (verit) case_prod_beta select_convs)
  apply (force simp: valid_def exs_valid_def validNF_alt_def)
  done

lemma valid_whileLoop_complete:
  "(\<exists>I. (\<forall>s. P r s \<longrightarrow> I r s )
        \<and> (\<forall>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>)
        \<and> (\<forall>r s. ( I r s \<and> \<not> C r s ) \<longrightarrow> Q r s))
    = \<lbrace> P r \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>"
  apply (rule iffI)
   apply clarsimp
   apply (rename_tac I)
   apply (rule_tac I=I in valid_whileLoop, auto)[1]
  apply (rule exI [where x="\<lambda>r s. \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>"])
  apply (intro conjI)
    apply (clarsimp simp: valid_def)
   apply (subst (2) valid_def)
   apply clarsimp
   apply (rename_tac a b)
   apply (subst (asm) (2) whileLoop_unroll)
   apply (case_tac "C a (with_env_of s b)")
    apply (clarsimp simp: valid_def bind_def' Bex_def condition_def split: if_split_asm)
    apply force
   apply (clarsimp simp: valid_def bind_def' Bex_def condition_def split: if_split_asm)
   apply force
  apply (subst whileLoop_unroll)
  apply (clarsimp simp: valid_def bind_def' condition_def return_def)
  done

lemma validNF_whileLoop_complete:
  "(\<exists>I R.
       (\<forall>s. P r s \<longrightarrow> I r s )
     \<and> (\<forall>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s\<rbrace> B r \<lbrace>\<lambda>r' s'. I r' s' \<and> ((r', s'), r, s) \<in> R\<rbrace>!)
     \<and> wf R
     \<and> (\<forall>r s. ( I r s \<and> \<not> C r s ) \<longrightarrow> Q r s))
    = \<lbrace> P r \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>!"
  (is "(\<exists>I R. ?LHS I R) = ?RHS")
proof (rule iffI)
  assume lhs: "\<exists>I R. ?LHS I R"

  obtain I R where "?LHS I R"
    using lhs
    by auto

  thus ?RHS
    by - (rule validNF_whileLoop[where I=I], auto)
next
  assume loop: "?RHS"

  define I where "I \<equiv> \<lambda>r s. \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<lbrace> \<lambda>r s. Q r s \<rbrace>!"
  define R where "R \<equiv> {(x, y). C (fst y) (snd y) \<and> (fst x, mstate (snd x)) \<in> fst (B (fst y) (snd y)) \<and>
                               env (snd x) = env (snd y) \<and>
                               whileLoop_terminates C B (env (snd y)) (fst y) (mstate (snd y))}"

  have wf: "wf R"
    using R_def whileLoop_terminates_wf
    by auto

  have start: "\<And>s. P r s \<Longrightarrow> I r s"
    using I_def loop validNF_chain by fastforce

  have fin: "\<And>r s. \<lbrakk> I r s; \<not> C r s \<rbrakk> \<Longrightarrow> Q r s"
    apply (unfold I_def)
    apply (subst (asm) whileLoop_unroll)
    apply (clarsimp simp: condition_def bind_def'
                     validNF_alt_def return_def)
    done

  have step: "\<And>r s. \<lbrace>\<lambda>s'. I r s' \<and> C r s' \<and> s' = s\<rbrace> B r
                   \<lbrace>\<lambda>r' s'. I r' s' \<and> ((r', s'), r, s) \<in> R\<rbrace>!"
             (is "\<And>r s. \<lbrace> ?pre r s \<rbrace> B r \<lbrace> ?post r s \<rbrace>!")
  proof -
    have inv_step:
        "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> I r' (with_env_of s s')"
      apply (clarsimp simp: I_def)
      apply (subst (asm) whileLoop_unroll)
      apply (clarsimp simp: condition_def bind_def' validNF_alt_def)
      apply force
      done

    have R_step:
        "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> ((r', with_env_of s s'), (r, s)) \<in> R"
      apply (clarsimp simp: I_def R_def)
      apply (clarsimp simp: validNF_alt_def whileLoop_def)
      done

    show "\<And>r s. ?thesis r s"
      apply rule
       apply (clarsimp simp: valid_def inv_step R_step)
      apply (clarsimp simp: no_fail_def I_def validNF_alt_def)
      apply (drule (1) snd_whileLoop_first_step)
      apply simp
      done
  qed

  show "\<exists>I' R'. ?LHS I' R'"
    using wf start fin step
    by blast
qed


lemma snd_whileLoop_complete:
  shows "snd (whileLoop C B r s) =
              (\<exists>I. I r s \<and> C r s \<and>
                   (\<forall>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<and> \<not> snd (B r s) \<rbrace> B r \<exists>\<lbrace> \<lambda>r s. C r s \<and> I r s \<rbrace>))"
  (is "?LHS = ?RHS")
proof (rule iffI)
  assume "?LHS"
  thus "?RHS"
    apply (clarsimp simp: whileLoop_def)
    apply (erule disjE)
     apply (rule exI [where x="\<lambda>r s. (Some (r, mstate s), None) \<in> whileLoop_results C B (env s)"])
     apply (intro conjI)
       apply simp
      apply (force elim: whileLoop_results_cases_fail)
     apply (clarsimp simp: exs_valid_def)
     apply (erule whileLoop_results_cases_fail, fastforce)
     apply clarsimp
     apply (erule bexI [rotated])
     apply clarsimp
     apply (metis fst_conv snd_conv whileLoop_results_cases_fail)
    apply (rule exI [where x="\<lambda>r s. \<not> whileLoop_terminates C B (env s) r (mstate s)"])
    apply clarsimp
    apply (rule conjI)
     apply (subst (asm)  whileLoop_terminates_simps)
     apply clarsimp
    apply (clarsimp simp: exs_valid_def)
    apply (subst (asm) (2)  whileLoop_terminates_simps)
    apply clarsimp
    apply (erule bexI [rotated])
    apply clarsimp
    apply (subst (asm) (2)  whileLoop_terminates_simps)
    apply clarsimp
    done
next
  assume "?RHS"
  thus "?LHS"
    apply clarsimp
    apply (erule (1) snd_whileLoop)
    apply force
    done
qed

lemma not_snd_whileLoop_complete:
  "(\<not> snd (whileLoop C B r s)) =
   (\<exists>I R . I r s \<and> wf R
           \<and> (\<forall>r s r' s'. (I r s \<and> C r s \<and> (r', s') \<in> fst (B r s)) \<longrightarrow> I r' (with_env_of s s'))
           \<and> (\<forall>r s. I r s \<and> C r s \<longrightarrow> \<not> snd (B r s))
           \<and> (\<forall>r s r' s'. I r s \<and> C r s \<and> (r', s') \<in> fst (B r s) \<longrightarrow>
                          ((r', with_env_of s s'), (r, s)) \<in> R))"
   (is "?LHS = ?RHS")
proof (rule iffI)
  assume "?RHS"
  thus "?LHS"
    apply clarsimp
    apply (erule make_pos_goal, rule not_snd_whileLoop; assumption?)
    apply (clarsimp simp: validNF_def no_fail_def valid_def)
    done
next
  assume no_fail: "?LHS"
  define I where "I \<equiv> \<lambda>r s. \<not> snd (whileLoop C B r s)"
  define R where "R \<equiv> {((r', s'), (r, s)). C r s \<and> (r', mstate s') \<in> fst (B r s) \<and>
                                            env s' = env s \<and>
                                            whileLoop_terminates C B (env s) r (mstate s)}"

  have "I r s"
    by (clarsimp simp: I_def no_fail)

  moreover
  have "wf R"
    apply (rule wf_subset [OF whileLoop_terminates_wf [where C=C and B=B]])
    apply (clarsimp simp: R_def)
    done

  moreover
  have "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> I r' (with_env_of s s')"
    apply (clarsimp simp: I_def whileLoop_def)
    apply (rule conjI)
     apply (metis whileLoop_results.intros(3) with_env_of_mstate)
    apply (erule whileLoop_terminates_cases)
     apply clarsimp
    apply fastforce
    done

  moreover
  have "\<And>r s. \<lbrakk> I r s; C r s \<rbrakk> \<Longrightarrow> \<not> snd (B r s)"
    apply (clarsimp simp: I_def)
    apply (subst (asm) whileLoop_unroll)
    apply (clarsimp simp: condition_true bind_def)
    done

  moreover
  have "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> ((r', with_env_of s s'), (r, s)) \<in> R"
    apply (clarsimp simp: R_def)
    apply (metis I_def snd_conv whileLoop_def)
    done

  ultimately show ?RHS
    by (metis (mono_tags))
qed


fun valid_path where
    "valid_path C B [] = False"
  | "valid_path C B [x] = (\<not>C (fst x) (snd x))"
  | "valid_path C B (x#y#xs) = ((C (fst x) (snd x) \<and> (fst y, mstate (snd y)) \<in> fst (B (fst x) (snd x)) \<and>
                                env (snd y) = env (snd x) \<and> valid_path C B (y#xs)))"

lemma valid_path_not_empty:
  "valid_path C B xs \<Longrightarrow> xs \<noteq> []"
  by clarsimp

definition shortest_path_length where
  "shortest_path_length C B x Q \<equiv>
        (LEAST n. \<exists>l. valid_path C B l \<and> hd l = x \<and> Q (fst (last l)) (snd (last l)) \<and> length l = n)"

lemma shortest_path_length_same [simp]:
  "\<lbrakk> \<not> C (fst a) (snd a); Q (fst a) (snd a) \<rbrakk> \<Longrightarrow> shortest_path_length C B a Q = 1"
  apply (clarsimp simp: shortest_path_length_def)
  apply (rule Least_equality)
   apply (rule exI [where x="[a]"])
   apply clarsimp
  apply (rule Suc_leI)
  apply clarsimp
  done

lemma valid_path_simp:
  "valid_path C B l =
     ((\<exists>r s. l = [(r, s)] \<and> \<not>C r s) \<or>
             (\<exists>r s r' s' xs. l = (r, s)#(r', s')#xs \<and> C r s \<and> (r', mstate s') \<in> fst (B r s) \<and>
                             env s' = env s \<and> valid_path C B ((r', s')#xs)))"
  by (cases l rule: remdups_adj.cases; clarsimp)

lemma path_exists:
  assumes path: "\<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<exists>\<lbrace> Q \<rbrace>"
  shows "\<exists>l. valid_path C B l \<and> hd l = (r, s) \<and> Q (fst (last l)) (snd (last l))"
proof -
  {
    fix r' s'
    assume x: "(r', s') \<in> fst (whileLoop C B r s)"
    assume y: "Q r' (with_env_of s s')"
    have ?thesis
      using x y
    proof (induct rule: in_whileLoop_induct)
      case (1 r s)
      then show ?case
        apply -
        apply (rule exI[where x="[(r,s)]"])
        apply clarsimp
        done
    next
      case (2 r s r' s' r'' s'')
      then show ?case
        apply clarsimp
        apply (frule valid_path_not_empty)
        apply (rename_tac l)
        apply (rule_tac x="(r, s)#l" in exI)
        apply (clarsimp simp: neq_Nil_conv)
        done
    qed
  }

  thus ?thesis
    using path
    by (clarsimp simp: exs_valid_def)
qed

lemma shortest_path_exists:
  "\<lbrakk> \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<exists>\<lbrace> Q \<rbrace> \<rbrakk> \<Longrightarrow>
       \<exists>l. valid_path C B l
              \<and> shortest_path_length C B (r, s) Q = length l
              \<and> hd l = (r, s)
              \<and> Q (fst (last l)) (snd (last l))"
  apply (frule path_exists)
  apply (clarsimp simp: simp: shortest_path_length_def)
  apply (rule LeastI2_ex)
   apply force
  apply force
  done

lemma shortest_path_is_shortest:
  "\<lbrakk> valid_path C B l; Q (fst (last l)) (snd (last l)) \<rbrakk> \<Longrightarrow> shortest_path_length C B (hd l) Q \<le> length l"
  apply (clarsimp simp: simp: shortest_path_length_def)
  apply (rule Least_le)
  apply force
  done

lemma valid_path_implies_exs_valid_whileLoop:
  "valid_path C B l \<Longrightarrow> \<lbrace> \<lambda>s. s = snd (hd l) \<rbrace> whileLoop C B (fst (hd l)) \<exists>\<lbrace> \<lambda>r s. (r, s) = last l  \<rbrace>"
proof (induct l)
  case Nil
  then show ?case
    by clarsimp
next
  case (Cons a l)
  then show ?case
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (subst whileLoop_unroll)
     apply (clarsimp simp: condition_def bind_def' exs_valid_def return_def)
    apply clarsimp
    apply (subst whileLoop_unroll)
    apply (clarsimp simp: condition_def bind_def' exs_valid_def return_def)
    apply (cases l; clarsimp split del: if_split split: prod.splits)
    apply (metis fst_conv snd_conv with_env_of_mstate)
    done
qed

lemma shortest_path_gets_shorter:
  "\<lbrakk> \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<exists>\<lbrace> Q \<rbrace>; C r s \<rbrakk> \<Longrightarrow>
   \<exists>(r', s') \<in> fst (B r s).
     shortest_path_length C B (r', with_env_of s s') Q < shortest_path_length C B (r, s) Q
     \<and> \<lbrace> \<lambda>s''. s'' = with_env_of s s' \<rbrace> whileLoop C B r' \<exists>\<lbrace> Q \<rbrace>"
  apply (drule shortest_path_exists)
  apply clarsimp
  apply (rename_tac xs)
  apply (case_tac xs rule: remdups_adj.cases; clarsimp)
  apply (rename_tac r' s' ys)
  apply (case_tac s', clarsimp)
  apply (rule bexI[rotated], assumption)
  apply clarify
  apply (frule shortest_path_is_shortest [where Q=Q])
   apply simp
  apply clarsimp
  apply (drule valid_path_implies_exs_valid_whileLoop)
  apply (clarsimp simp: exs_valid_def)
  apply (erule bexI [rotated])
  apply (clarsimp split: if_split_asm simp: split_pairs)
  done

lemma exs_valid_whileLoop_complete:
  "(\<exists>T R. (\<forall>s. P s \<longrightarrow> T r s)
          \<and> (\<forall>r s0. \<lbrace> \<lambda>s. T r s \<and> C r s \<and> s = s0 \<rbrace>
                    B r
                    \<exists>\<lbrace> \<lambda>r' s'. T r' s' \<and> ((r', s'), (r, s0)) \<in> R \<rbrace>)
          \<and> wf R
          \<and> (\<forall>r s. (T r s \<and> \<not> C r s) \<longrightarrow> Q r s))
   = (\<lbrace> P \<rbrace> whileLoop C B r \<exists>\<lbrace> Q \<rbrace>)"
  (is "(\<exists>T R. ?LHS T R) = ?RHS")
proof (rule iffI)
  assume lhs: "\<exists>T R. ?LHS T R"
  obtain T R where TR: "?LHS T R"
    using lhs
    by blast

  show "?RHS"
    by (rule exs_valid_whileLoop [where T=T and R=R], auto simp: TR)
next
  assume rhs: "?RHS"

  define I where "I \<equiv> \<lambda>r s. \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<exists>\<lbrace> Q \<rbrace>"
  define R where "R \<equiv> measure (\<lambda>(r, s). shortest_path_length C B (r, s) Q)"

  have P_s: "\<And>s. P s \<Longrightarrow> I r s"
    using rhs
    by (clarsimp simp: I_def exs_valid_def)

  have inv_holds:
  "\<And>r s. \<lbrakk> I r s; C r s \<rbrakk> \<Longrightarrow> \<exists>(r', s') \<in> fst (B r s). I r' (with_env_of s s') \<and>
                                                       ((r', (with_env_of s s')), r, s) \<in> R"
    apply (clarsimp simp: I_def R_def)
    apply (frule (1) shortest_path_gets_shorter)
    apply clarsimp
    apply (rule bexI [rotated], assumption)
    apply clarsimp
    done

  have wf_R: "wf R"
    by (clarsimp simp: R_def)

  have last_step: "\<And>r s. \<lbrakk> I r s; \<not> C r s \<rbrakk> \<Longrightarrow> Q r s"
    unfolding I_def exs_valid_def
    by clarsimp (metis fst_whileLoop_cond_false whileLoop_cond_fail)

  show "\<exists>I R. ?LHS I R"
    using P_s inv_holds wf_R last_step
    unfolding exs_valid_def
    by (smt (verit, ccfv_threshold) case_prodD case_prodI2)
qed

end
