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
 * This is a purely theoretical theory containing proofs
 * that the whileLoop rules in "WhileLoopRules" are complete.
 *
 * You probably don't care about this.
 *)
theory WhileLoopRulesCompleteness
imports WhileLoopRules
begin

lemma whileLoop_rule_strong_complete:
  "(\<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<lbrace> \<lambda>r s. (r, s) \<in> fst Q \<rbrace>
        \<and> (\<forall>r'' s''. (r'', s'') \<in> fst Q \<longrightarrow> \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<exists>\<lbrace> \<lambda>r s. r = r'' \<and> s = s'' \<rbrace>)
        \<and> (snd Q \<longrightarrow> snd (whileLoop C B r s))
        \<and> (\<not> snd Q \<longrightarrow> \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<lbrace> \<lambda>_ _. True \<rbrace>!))
    = (whileLoop C B r s = Q)"
  apply (rule iffI)
   apply (rule whileLoop_rule_strong, auto)[1]
  apply (clarsimp simp: valid_def exs_valid_def validNF_alt_def)
  apply force
  done

lemma valid_whileLoop_complete:
  "(\<exists>I.
       (\<forall>s. P r s \<longrightarrow> I r s )
     \<and> (\<forall>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<rbrace> B r \<lbrace> I \<rbrace>)
     \<and> (\<forall>r s. ( I r s \<and> \<not> C r s ) \<longrightarrow> Q r s))
    = \<lbrace> P r \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>"
  apply (rule iffI)
   apply clarsimp
   apply (rule_tac I=I in valid_whileLoop, auto)[1]
  apply (rule exI [where x="\<lambda>r s. \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>"])
  apply (intro conjI)
    apply (clarsimp simp: valid_def)
   apply (subst (2) valid_def)
   apply clarsimp
   apply (subst (asm) (2) whileLoop_unroll)
   apply (case_tac "C a b")
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
     \<and> (wf R)
     \<and> (\<forall>r s. ( I r s \<and> \<not> C r s ) \<longrightarrow> Q r s))
    = \<lbrace> P r \<rbrace> whileLoop C B r \<lbrace> Q \<rbrace>!"
  (is "(\<exists>I R. ?LHS I R) = ?RHS")
proof (rule iffI)
  assume lhs: "\<exists>I R. ?LHS I R"

  obtain I R where "?LHS I R"
    using lhs
    by auto

  thus ?RHS
    by (rule_tac validNF_whileLoop [where I=I and R=R], auto)
next
  assume loop: "?RHS"

  define I where "I \<equiv> \<lambda>r s. \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<lbrace> \<lambda>r s. Q r s \<rbrace>!"
  define R where "R \<equiv> {(x, y). C (fst y) (snd y) \<and> x \<in> fst (B (fst y) (snd y)) \<and>
                                whileLoop_terminates C B (fst y) (snd y)}"

  have "wf R"
    using R_def whileLoop_terminates_wf
    by auto

  have start: "\<And>s. P r s \<Longrightarrow> I r s"
    by (metis (full_types) I_def loop validNF_weaken_pre)

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
        "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> I r' s'"
      apply (clarsimp simp: I_def)
      apply (subst (asm) whileLoop_unroll)
      apply (clarsimp simp: condition_def bind_def' validNF_alt_def)
      apply force
      done

    have R_step:
        "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> ((r', s'), (r, s)) \<in> R"
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
    using \<open>wf R\<close> start fin step
    by blast
qed


lemma snd_whileLoop_complete:
  shows "snd (whileLoop C B r s) =
              (\<exists>I. I r s \<and> C r s \<and>
                   (\<forall>r. \<lbrace> \<lambda>s. I r s \<and> C r s \<and> \<not> snd (B r s) \<rbrace>
                            B r \<exists>\<lbrace> \<lambda>r s. C r s \<and> I r s \<rbrace>))"
  (is "?LHS = ?RHS")
proof (rule iffI)
  assume "?LHS"
  thus "?RHS"
    apply (clarsimp simp: whileLoop_def)
    apply (erule disjE)
     apply (rule exI [where x="\<lambda>r s. (Some (r, s), None) \<in> whileLoop_results C B"])
     apply (intro conjI)
       apply simp
      apply (metis Pair_inject whileLoop_results_cases_fail)
     apply (clarsimp simp: exs_valid_def)
     apply (erule whileLoop_results_cases_fail, fastforce)
     apply clarsimp
     apply (erule bexI [rotated])
     apply clarsimp
     apply (metis fst_conv snd_conv whileLoop_results_cases_fail)
    apply (rule exI [where x="\<lambda>r s. \<not> whileLoop_terminates C B r s"])
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
  shows "(\<not> snd (whileLoop C B r s)) = (\<exists>I R . I r s \<and> wf R \<and>
           (\<forall>r s r' s'. (I r s \<and> C r s \<and> (r', s') \<in> fst (B r s)) \<longrightarrow> I r' s')
           \<and> (\<forall>r s. I r s \<and> C r s \<longrightarrow> \<not> snd (B r s))
           \<and> (\<forall>r s r' s'. I r s \<and> C r s \<and> (r', s') \<in> fst (B r s) \<longrightarrow> ((r', s'), (r, s)) \<in> R))"
   (is "?LHS = ?RHS")
proof (rule iffI)
  assume "?RHS"
  thus "?LHS"
    apply (clarsimp)
    apply (erule make_pos_goal, rule not_snd_whileLoop)
      apply assumption
     defer
     apply assumption
    apply (clarsimp simp: validNF_def no_fail_def valid_def)
    done
next
  assume no_fail: "?LHS"
  define I where "I \<equiv> \<lambda>r s. \<not> snd (whileLoop C B r s)"
  define R where "R \<equiv> {((r', s'), (r, s)). C r s \<and> (r', s') \<in> fst (B r s) \<and>
                                            whileLoop_terminates C B r s}"

  have "I r s"
    by (clarsimp simp: I_def no_fail)

  moreover have "wf R"
    apply (rule wf_subset [OF whileLoop_terminates_wf [where C=C and B=B]])
    apply (clarsimp simp: R_def)
    done

  moreover have "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> I r' s'"
    apply (clarsimp simp: I_def whileLoop_def)
    apply (rule conjI)
     apply (metis whileLoop_results_simps)
    apply (erule whileLoop_terminates_cases)
     apply clarsimp
    apply fastforce
    done

  moreover have "\<And>r s. \<lbrakk> I r s; C r s \<rbrakk> \<Longrightarrow> \<not> snd (B r s)"
    apply (clarsimp simp: I_def)
    apply (subst (asm) whileLoop_unroll)
    apply (clarsimp simp: condition_true bind_def)
    done

  moreover have "\<And>r s r' s'. \<lbrakk> I r s; C r s; (r', s') \<in> fst (B r s) \<rbrakk> \<Longrightarrow> ((r', s'), (r, s)) \<in> R"
    apply (clarsimp simp: R_def)
    apply (metis I_def snd_conv whileLoop_def)
    done

  ultimately show ?RHS
    by (metis (mono_tags))
qed


fun valid_path
where
    "valid_path C B [] = False"
  | "valid_path C B [x] = (\<not> C (fst x) (snd x))"
  | "valid_path C B (x#y#xs) = ((C (fst x) (snd x) \<and> y \<in> fst (B (fst x) (snd x)) \<and> valid_path C B (y#xs)))"

definition "shortest_path_length C B x Q \<equiv>
        (LEAST n. \<exists>l. valid_path C B l \<and> hd l = x \<and> Q (fst (last l)) (snd (last l)) \<and> length l = n)"

lemma shortest_path_length_same [simp]:
  "\<lbrakk> \<not> C (fst a) (snd a); Q (fst a) (snd a) \<rbrakk> \<Longrightarrow> shortest_path_length C B a Q = 1"
  apply (clarsimp simp: shortest_path_length_def)
  apply (rule Least_equality)
   apply (rule exI [where x="[a]"])
   apply clarsimp
  apply (case_tac "y = 0")
   apply clarsimp
  apply clarsimp
  done

lemma valid_path_simp:
  "valid_path C B l =
        (((\<exists>r s. l = [(r, s)] \<and> \<not> C r s) \<or>
              (\<exists>r s r' s' xs. l = (r, s)#(r', s')#xs \<and> C r s \<and> (r', s') \<in> fst (B r s) \<and> valid_path C B ((r', s')#xs))))"
  apply (case_tac l)
   apply clarsimp
  apply (case_tac list)
   apply clarsimp
  apply clarsimp
  done

lemma path_exists:
  assumes path: "\<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<exists>\<lbrace> Q \<rbrace>"
  shows "\<exists>l. valid_path C B l \<and> hd l = (r, s) \<and> Q (fst (last l)) (snd (last l))"
proof -
  {
    fix r' s'
    assume x: "(r', s') \<in> fst (whileLoop C B r s)"
    assume y: "Q r' s'"
    have ?thesis
      using x y
      apply (induct rule: in_whileLoop_induct)
       apply (rule_tac x="[(r,s)]" in exI)
       apply clarsimp
      apply clarsimp
      apply (case_tac l)
       apply clarsimp
      apply (rule_tac x="(r, s)#l" in exI)
      apply clarsimp
      done
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
  apply (induct l)
   apply clarsimp
  apply clarsimp
  apply rule
   apply clarsimp
   apply (subst whileLoop_unroll)
   apply (clarsimp simp: condition_def bind_def' exs_valid_def return_def)
  apply clarsimp
  apply (subst whileLoop_unroll)
  apply (clarsimp simp: condition_def bind_def' exs_valid_def return_def)
  apply rule
   apply (clarsimp split: prod.splits)
   apply (case_tac l)
    apply clarsimp
   apply (clarsimp split del: if_split)
   apply (erule bexI [rotated])
   apply clarsimp
  apply clarsimp
  apply (case_tac l, auto)
  done

lemma shortest_path_gets_shorter:
  "\<lbrakk> \<lbrace> \<lambda>s'. s' = s \<rbrace> whileLoop C B r \<exists>\<lbrace> Q \<rbrace>;
       C r s \<rbrakk>
     \<Longrightarrow> \<exists>(r', s') \<in> fst (B r s).
                shortest_path_length C B (r', s') Q < shortest_path_length C B (r, s) Q
                 \<and> \<lbrace> \<lambda>s. s = s' \<rbrace> whileLoop C B r' \<exists>\<lbrace> Q \<rbrace>"
  apply (drule shortest_path_exists)
  apply clarsimp
  apply (case_tac l)
   apply clarsimp
  apply (case_tac list)
   apply clarsimp
  apply (rule_tac x="aa" in bexI)
   apply clarify
   apply (simp only: valid_path.simps, clarify)
   apply (frule shortest_path_is_shortest [where Q=Q])
    apply simp
   apply clarsimp
   apply (drule valid_path_implies_exs_valid_whileLoop)
   apply (clarsimp simp: exs_valid_def)
   apply (erule bexI [rotated])
   apply (clarsimp split: if_split_asm)
  apply clarsimp
  done

lemma exs_valid_whileLoop_complete:
   "(\<exists>T R.
         (\<forall>s. P s \<longrightarrow> T r s)
         \<and> (\<forall>r s0. \<lbrace> \<lambda>s. T r s \<and> C r s \<and> s = s0 \<rbrace> B r
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

  have inv_holds: "\<And>r s. \<lbrakk> I r s; C r s \<rbrakk> \<Longrightarrow>
              \<exists>(r', s') \<in> fst (B r s). I r' s' \<and> ((r', s'), r, s) \<in> R"
    apply (clarsimp simp: I_def R_def)
    apply (frule (1) shortest_path_gets_shorter)
    apply clarsimp
    apply (rule bexI [rotated], assumption)
    apply clarsimp
    done

  have wf_R: "wf R"
    by (clarsimp simp: R_def)

  have last_step: "\<And>r s. \<lbrakk> I r s; \<not> C r s \<rbrakk> \<Longrightarrow> Q r s"
    apply (clarsimp simp: I_def exs_valid_def)
    apply (metis in_return whileLoop_cond_fail)
    done

  show "\<exists>I R. ?LHS I R"
    apply (rule exI [where x=I])
    apply (rule exI [where x=R])
    using P_s inv_holds wf_R last_step
    apply (clarsimp simp: exs_valid_def)
    done
qed

end
