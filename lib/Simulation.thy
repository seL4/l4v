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
   A general calculus of refinement in Isabelle.
*)

chapter "Refinement"

theory Simulation
imports Main
begin

text \<open>
  A data type is a collection of three functions on three basic types.
  The three basic types are the private state space @{typ 'a}, the observable
  state space @{typ 'b} and the operations @{typ 'j}.

  The three functions are the initialisation @{term "Init"} which (potentially
  nondeterministically) produces a private state space from an observable one,
  the finalisation @{term Fin} which projects the observable part of
  the state space out of the private one, and finally @{term Step} that gives
  the (potentially nondeterministic) transition relation on the private state
  space for each operation in @{typ 'j}.

  In the simple case, the private state space is something like a
  tuple @{typ "'a \<times> 'b"} fully containing the observable part such
  that @{term Fin} just becomes the projection @{term snd}, and @{term
  "Init s"} constructs an additional private part, e.g. just
  @{term "{(f x, x)}"}.

  Hoare triples on the system and refinement are defined over the observable
  part of the state.
\<close>

record ('a,'b,'j) data_type =
  Init :: "'b \<Rightarrow> 'a set"
  Fin :: "'a \<Rightarrow> 'b"
  Step :: "'j \<Rightarrow> ('a \<times> 'a) set"

text \<open>
  A sequence of operations over a transition relation @{term \<delta>} is executed
  by applying the relation repeatedly.
\<close>
definition
  steps :: "('j \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> 'a set \<Rightarrow> 'j list \<Rightarrow> 'a set" where
  "steps \<delta> \<equiv> foldl (\<lambda>S j. \<delta> j `` S)"

text \<open>
  The sequence of operations in the data type is then executed
  in an initial state by initialising the private state, executing
  the transition relation over this private state, and finally
  projecting back out the set of final, observable states.
\<close>
definition
   execution :: "('a,'b,'j) data_type \<Rightarrow> 'b \<Rightarrow> 'j list \<Rightarrow> 'b set" where
  "execution A s js \<equiv> Fin A ` steps (Step A) (Init A s) js"

text \<open>
  A Hoare triple over a list of operations in the data type is
  the usual: given a state in the pre-condition, all resulting states
  of the execution must be in the post-condition:
\<close>
definition
  hoare_triple :: "('a,'b,'j) data_type \<Rightarrow> 'b set \<Rightarrow> 'j list \<Rightarrow> 'b set \<Rightarrow> bool"
where
  "hoare_triple A P js Q \<equiv> \<forall>s \<in> P. execution A s js \<subseteq> Q"

text \<open>
  Refinement is defined by saying that all concrete behaviours are contained in
  their corresponding abstract ones. Only the private state spaces of the
  data type may differ.
\<close>
definition
  refines :: "('c,'b,'j) data_type \<Rightarrow> ('a,'b,'j) data_type \<Rightarrow> bool" (infix "\<sqsubseteq>" 60)
where
  "C \<sqsubseteq> A \<equiv> \<forall>js s. execution C s js \<subseteq> execution A s js"

text \<open>
  Alternatively, one may say that all Hoare triples proved on the abstract data
  type are true for the concrete one.
\<close>
lemma hoare_triple_refinement:
  "C \<sqsubseteq> A = (\<forall>P Q js. hoare_triple A P js Q \<longrightarrow> hoare_triple C P js Q)"
  by (simp add: refines_def hoare_triple_def) blast


\<comment> \<open>composing two relations\<close>
definition
  rel_semi :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'c) set \<Rightarrow> ('a \<times> 'c) set" (infixl ";;;" 65)
where
  "A ;;; B \<equiv> A O B"

text \<open>
  Refinement is a global property over all executions and/or all
  hoare triples. As this is hard to show, we define the weaker concept
  of forward simulation.
\<close>
definition
  fw_sim :: "('a \<times> 'c) set \<Rightarrow> ('c,'b,'j) data_type \<Rightarrow> ('a,'b,'j) data_type \<Rightarrow> bool"
where
  "fw_sim R C A \<equiv> (\<forall>s. Init C s \<subseteq> R `` Init A s) \<and>
                  (\<forall>j. R ;;; Step C j \<subseteq> Step A j ;;; R) \<and>
                  (\<forall>s s'. (s,s') \<in> R \<longrightarrow> Fin C s' = Fin A s)"

definition
  fw_simulates :: "('c,'b,'j) data_type \<Rightarrow> ('a,'b,'j) data_type \<Rightarrow> bool" (infixl "\<sqsubseteq>\<^sub>F" 50)
where
  "C \<sqsubseteq>\<^sub>F A \<equiv> \<exists>R. fw_sim R C A"

lemma fw_sim_steps:
  assumes steps: "t' \<in> steps (Step C) S' js" "S' \<subseteq> R `` S"
  assumes sim: "fw_sim R C A"
  shows "\<exists>t \<in> steps (Step A) S js. (t,t') \<in> R" using steps
proof (induct js arbitrary: S' S)
  case Nil
  thus ?case by (simp add: steps_def) blast
next
  case (Cons j js)
  hence "t' \<in> steps (Step C) (Step C j `` S') js"
    by (clarsimp simp: steps_def)
  moreover {
    from Cons.prems
    have "S' \<subseteq> R `` S" by simp
    moreover
    from sim
    have "R ;;; Step C j \<subseteq> Step A j ;;; R" by (simp add: fw_sim_def)
    ultimately
    have "Step C j `` S' \<subseteq> R `` (Step A j `` S)"
      by (simp add: rel_semi_def) blast
  }
  ultimately
  show ?case using Cons.hyps
    by (auto simp: steps_def)
qed

lemma sim_imp_refines:
  "C \<sqsubseteq>\<^sub>F A \<Longrightarrow> C \<sqsubseteq> A"
  apply (clarsimp simp: refines_def execution_def fw_simulates_def)
  apply (rename_tac t)
  apply (drule fw_sim_steps)
    prefer 2
    apply assumption
   apply (simp add: fw_sim_def)
   apply blast
  apply clarsimp
  apply (erule rev_image_eqI)
  apply (simp add: fw_sim_def)
  done


text \<open>
  To further aid proofs, we define (private) invariants on data types.
  Private invariants are properties that are true throughout execution
  on the private state space of the state type. The purpose is to exploit
  these properties while showing forward simulation.
\<close>
definition
  invariant_holds :: "('a,'b,'j) data_type \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<Turnstile>" 60)
where
  "D \<Turnstile> I \<equiv> (\<forall>s. Init D s \<subseteq> I) \<and> (\<forall>j. Step D j `` I \<subseteq> I)"

lemma invariant_T [iff]: "D \<Turnstile> UNIV"
  by (simp add: invariant_holds_def)

lemma invariantI:
  "\<lbrakk> \<forall>s. Init D s \<subseteq> I; \<forall>j. Step D j `` I \<subseteq> I \<rbrakk> \<Longrightarrow> D \<Turnstile> I"
  by (simp add: invariant_holds_def)

lemma invariant_CollectI [intro?]:
  assumes init: "\<And>s a. s \<in> Init D a \<Longrightarrow> I s"
  assumes step: "\<And>j s s'. \<lbrakk> I s; (s,s') \<in> Step D j \<rbrakk> \<Longrightarrow> I s'"
  shows "D \<Turnstile> Collect I"
proof (rule invariantI)
  show "\<forall>a. Init D a \<subseteq> Collect I" by (fast intro: init)
next
  show "\<forall>j. Step D j `` Collect I \<subseteq> Collect I"
    by (auto simp add: Image_def intro: step)
qed

lemma invariant_conjI:
  "D \<Turnstile> P \<Longrightarrow> D \<Turnstile> Q  \<Longrightarrow> D \<Turnstile> P \<inter> Q"
  by (simp add: invariant_holds_def) blast

lemma invariant_conjI2:
  "\<lbrakk> D \<Turnstile> I; \<And>s. Init D s \<subseteq> I \<Longrightarrow> Init D s \<subseteq> J;
    \<forall>j. Step D j `` (I \<inter> J) \<subseteq> J \<rbrakk> \<Longrightarrow> D \<Turnstile> I \<inter> J"
  by (simp add: invariant_holds_def) blast


text \<open>
  We can now define forward simulation with an invariant. The proof
  obligation for the step and final case in the correspondence proof
  can now assume that the invariant holds. The invariant itself can be
  shown separately.
\<close>
definition
  LI :: "('a,'b,'j) data_type \<Rightarrow> ('c,'b,'j) data_type \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> bool"
where
  "LI A C R I \<equiv> (\<forall>s. Init C s \<subseteq> R `` Init A s) \<and>
                (\<forall>j. (R \<inter> I) ;;; Step C j \<subseteq> Step A j ;;; R) \<and>
                (\<forall>s s'. (s,s') \<in> R \<inter> I \<longrightarrow> Fin C s' = Fin A s)"


lemma LI_fw_sim:
  assumes  ia: "A \<Turnstile> I\<^sub>a" and ic: "C \<Turnstile> I\<^sub>c" and li: "LI A C r (I\<^sub>a \<times> I\<^sub>c)"
  shows "fw_sim (r \<inter> I\<^sub>a \<times> I\<^sub>c) C A"
proof -
  from li have
    init: "\<forall>s. Init C s \<subseteq> r `` Init A s" and
    step: "\<forall>j. (r \<inter> (I\<^sub>a \<times> I\<^sub>c)) ;;; Step C j \<subseteq> Step A j ;;; r" and
    fin: "(\<forall>s s'. (s,s') \<in> r \<inter> (I\<^sub>a \<times> I\<^sub>c) \<longrightarrow> Fin C s' = Fin A s)"
    by (auto simp: LI_def)
  from ia have  "\<forall>s. (r \<inter> (UNIV \<times> I\<^sub>c) ) `` Init A s = (r \<inter> (I\<^sub>a \<times> I\<^sub>c)) `` Init A s"
    by (simp add: invariant_holds_def, blast)
  moreover from init ic have "\<forall>s. Init C s \<subseteq> (r \<inter> (UNIV \<times> I\<^sub>c)) `` Init A s"
    by (simp add: invariant_holds_def, blast)
  ultimately have initI: "\<forall>s. Init C s \<subseteq> (r \<inter> (I\<^sub>a \<times> I\<^sub>c)) `` Init A s" by simp
  moreover {
    fix j
    from step have "r \<inter> (I\<^sub>a \<times> I\<^sub>c) ;;; Step C j \<subseteq> Step A j ;;; r"..
    also
    have "r \<inter> (I\<^sub>a \<times> I\<^sub>c) = ((UNIV \<times> I\<^sub>a) \<inter> Id) ;;; r ;;; ((I\<^sub>c \<times> UNIV) \<inter> Id)"
      (is "_ = ?I\<^sub>a ;;; r ;;; ?I\<^sub>c")
      by (simp add: rel_semi_def, blast)
    finally
    have "?I\<^sub>a ;;; r ;;; ?I\<^sub>c ;;; Step C j \<subseteq> ?I\<^sub>a ;;; Step A j ;;; r"
      by (simp add: rel_semi_def, blast)
    also
    from ia have "\<dots> \<subseteq> Step A j ;;; ?I\<^sub>a ;;; r"
      by (simp add: invariant_holds_def rel_semi_def, blast)
    finally
    have "?I\<^sub>a ;;;  r ;;; ?I\<^sub>c ;;; Step C j;;; ?I\<^sub>c \<subseteq>  Step A j ;;; ?I\<^sub>a ;;; r ;;; ?I\<^sub>c"
      by (simp add: rel_semi_def, blast)
    also
    from ic
    have "?I\<^sub>a ;;; r ;;; ?I\<^sub>c ;;; Step C j;;; ?I\<^sub>c =  ?I\<^sub>a ;;; r ;;; ?I\<^sub>c ;;; Step C j"
      by (simp add: invariant_holds_def rel_semi_def, blast)
    finally
    have "r \<inter> (I\<^sub>a \<times> I\<^sub>c) ;;; Step C j \<subseteq> Step A j ;;; r \<inter> (I\<^sub>a \<times> I\<^sub>c)"
      by (simp add: rel_semi_def, blast)
  }
  ultimately show "fw_sim (r \<inter> I\<^sub>a \<times> I\<^sub>c) C A" using fin
    by (simp add: fw_sim_def)
qed


lemma weaken_LI:
  assumes LI: "LI A C R I'" and weaker: "I \<subseteq> I'" shows "LI A C R I"
proof -
  from weaker have step: "\<And>j. R \<inter> I ;;; Step C j \<subseteq> R \<inter> I' ;;; Step C j"
    by (fastforce simp: rel_semi_def relcomp_def)
  from weaker have fin: "\<And>S. S \<in> R \<inter> I \<Longrightarrow> S \<in> R \<inter> I'" by fastforce
  from subset_trans[OF step] fin LI show ?thesis  by (clarsimp simp: LI_def)
qed

lemma fw_sim_eq_LI: "fw_sim r C A = LI A C r UNIV"
  by (simp add: fw_sim_def LI_def)

lemma fw_sim_LI: "fw_sim r C A \<Longrightarrow> LI A C r I"
  by (simp add: fw_sim_eq_LI weaken_LI[where I'=UNIV])


lemma L_invariantI:
  assumes  "A \<Turnstile> I\<^sub>a" and "C \<Turnstile> I\<^sub>c" and "LI A C r (I\<^sub>a \<times> I\<^sub>c)"
  shows "C \<sqsubseteq>\<^sub>F A"
  using assms
  by (simp add: fw_simulates_def, rule_tac x="r \<inter> I\<^sub>a \<times> I\<^sub>c" in exI,
      simp add: LI_fw_sim)

lemma refinement_refl[simp]:
  "A \<sqsubseteq> A"
  by (simp add: refines_def)

lemma refinement_trans [trans]:
  "\<lbrakk>C \<sqsubseteq> B; B \<sqsubseteq> A\<rbrakk> \<Longrightarrow> C \<sqsubseteq> A"
  by (simp add: refines_def) blast


lemma fw_inv_transport:
  "\<lbrakk> A \<Turnstile> I\<^sub>a; C \<Turnstile> I\<^sub>c; LI A C R (I\<^sub>a \<times> I\<^sub>c) \<rbrakk> \<Longrightarrow> C \<Turnstile> {s'. \<exists>s. (s,s') \<in> R \<and> s \<in> I\<^sub>a \<and> s' \<in> I\<^sub>c}"
  apply (clarsimp simp: LI_def invariant_holds_def)
  apply (rule conjI)
   apply (rule allI)
   apply clarsimp
   apply (subgoal_tac "x \<in> (R `` Init A s)")
    prefer 2
    apply fastforce
   apply blast
  apply clarsimp
  apply (erule_tac x=j in allE)+
  apply (clarsimp simp: rel_semi_def)
  apply (subgoal_tac "(s,x) \<in> Step A j O R")
   prefer 2
   apply blast
  apply blast
  done

lemma fw_sim_refl:
  "fw_sim Id A A"
  apply (simp add: fw_sim_def rel_semi_def)
  done

lemma fw_simulates_refl[simp]:
  "A \<sqsubseteq>\<^sub>F A"
  apply (simp add: fw_simulates_def fw_sim_refl exI[where x="Id"])
  done

lemma fw_sim_trans:
  "\<lbrakk>fw_sim Q C B; fw_sim R B A\<rbrakk> \<Longrightarrow> fw_sim (R O Q) C A"
  by (auto simp: fw_sim_def rel_semi_def; blast)

lemma fw_simulates_trans:
  "\<lbrakk>C \<sqsubseteq>\<^sub>F B; B \<sqsubseteq>\<^sub>F A\<rbrakk> \<Longrightarrow> C \<sqsubseteq>\<^sub>F A"
  apply (auto simp: fw_simulates_def dest: fw_sim_trans)
  done

end
