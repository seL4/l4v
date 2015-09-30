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
   Methods and method combinators that are built using Eisbach.
*)

theory Eisbach_Methods
imports "~~/src/HOL/Eisbach/Eisbach_Tools" 
        "subgoal_focus/Subgoal_Focus"
        "subgoal_focus/Subgoal_Methods"
begin


section \<open>Debugging methods\<close>

method print_concl = (match conclusion in P for P \<Rightarrow> \<open>print_term P\<close>)

method_setup print_raw_goal = \<open>Scan.succeed (fn ctxt => fn facts => 
  (fn st => (Output.writeln (Display.string_of_thm ctxt st); Seq.single ([],st))))\<close>


method_setup print_headgoal = 
  \<open>Scan.succeed (fn ctxt =>
   SIMPLE_METHOD
    (SUBGOAL (fn (t,_) => 
     (Output.writeln 
     (Pretty.string_of (Syntax.pretty_term ctxt t)); all_tac)) 1))\<close>

section \<open>Simple Combinators\<close>

method_setup defer_tac = \<open>Scan.succeed (fn _ => SIMPLE_METHOD (defer_tac 1))\<close>

method_setup all =
 \<open>Method_Closure.parse_method >> (fn m => fn ctxt => fn facts =>
   let
     fun tac i st' =
       Goal.restrict i 1 st'
       |> Method_Closure.method_evaluate m ctxt facts
       |> Seq.map (Goal.unrestrict i o snd)

   in SIMPLE_METHOD (ALLGOALS tac) facts end)
\<close>

text \<open>The following @{text fails} and @{text succeeds} methods protect the goal from the effect
      of a method, instead simply determining whether or not it can be applied to the current goal.
      The @{text fails} method inverts success, only succeeding if the given method would fail.\<close>

method_setup fails =
 \<open>Method_Closure.parse_method >> (fn m => fn ctxt => fn facts =>
   let
     fun fail_tac st' = 
       (case Seq.pull (Method_Closure.method_evaluate m ctxt facts st') of
          SOME _ => Seq.empty
        | NONE => Seq.single st')

   in SIMPLE_METHOD fail_tac facts end)
\<close>

method_setup succeeds =
 \<open>Method_Closure.parse_method >> (fn m => fn ctxt => fn facts =>
   let
     fun can_tac st' = 
       (case Seq.pull (Method_Closure.method_evaluate m ctxt facts st') of
          SOME (st'',_) => Seq.single st'
        | NONE => Seq.empty)

   in SIMPLE_METHOD can_tac facts end)
\<close>

text \<open>This method wraps up the "focus" mechanic of match without actually doing any matching.
      We need to consider whether or not there are any assumptions in the goal,
      as premise matching fails if there are none.

      If the @{text fails} method is removed here, then backtracking will produce
      a set of invalid results, where only the conclusion is focused despite
      the presence of subgoal premises.
      \<close>

method focus_concl methods m =
  ((fails \<open>erule thin_rl\<close>, match conclusion in _ \<Rightarrow> \<open>m\<close>)
  | match premises (local) in H:_ (multi) \<Rightarrow> \<open>m\<close>)

section \<open>Advanced combinators\<close>

subsection \<open>Protecting goal elements (assumptions or conclusion) from methods\<close>

context
begin

private definition "protect_concl x \<equiv> \<not> x"
private definition "protect_false \<equiv> False"

private lemma protect_start: "(protect_concl P \<Longrightarrow> protect_false) \<Longrightarrow> P" 
  by (simp add: protect_concl_def protect_false_def) (rule ccontr)

private lemma protect_end: "protect_concl P \<Longrightarrow> P \<Longrightarrow> protect_false" 
  by (simp add: protect_concl_def protect_false_def)

method only_asm methods m = 
  (match premises in H[thin]:_ (multi,cut) \<Rightarrow> 
    \<open>rule protect_start, 
     match premises in H'[thin]:"protect_concl _" \<Rightarrow> 
       \<open>insert H,m;rule protect_end[OF H']\<close>\<close>)

method only_concl methods m = (focus_concl \<open>m\<close>)

end

notepad begin
 fix D C
  assume DC:"D \<Longrightarrow> C"
  have "D \<and> D \<Longrightarrow> C \<and> C"
  apply (only_asm \<open>simp\<close>) -- "stash conclusion before applying method"
  apply (only_concl \<open>simp add: DC\<close>) -- "hide premises from method"
  by (rule DC)

end

subsection \<open>Safe subgoal folding (avoids expanding meta-conjuncts)\<close>

text \<open>Isabelle's goal mechanism wants to aggressively expand meta-conjunctions if they
      are the top-level connective. This means that @{text fold_subgoals} will immediately
      be unfolded if there are no common assumptions to lift over.

      This method simply ensures that this is the case by inserting a dummy assumption
      as the first assumption to all subgoals, so that after folding the goal
      looks like this: @{term "dummy_asm ==> A &&& B"}. The inner method is then
      executed on the resulting goal, without expanding the conjuncts.

      The inner method should probably clear this dummy assumption internally at
      some point (using the provided @{text clear_dummy_asm}, 
      but only when it doesn't need the conjunction to persist.\<close>

context begin

private definition "dummy_asm == True"
private lemma dummy_asm: "dummy_asm" by (simp add: dummy_asm_def)

method clear_dummy_asm = (erule thin_rl[of dummy_asm])?

method safe_fold_subgoals methods m =
  (all \<open>insert dummy_asm, rotate_tac -1\<close>,
   fold_subgoals,
   (m ; clear_dummy_asm))

end

notepad begin
  fix D C E
  
  assume DC: "D &&& C"
  have "D" "C"
  apply -
  by (safe_fold_subgoals \<open>rule DC\<close>)

end


section \<open>Utility methods\<close>
  

subsection \<open>Finding a goal based on successful application of a method\<close>

text \<open>This method works by creating "tagged" subgoals in order to use the + operator
      to iterate over all goals without looping indefinitely.
      Effectively this looks like a while-loop, which breaks out when either
      the "end" subgoal is found or when the method succeeds and the "success"
      subgoal is found.\<close>

context begin

private definition "goal_tag (x :: unit) \<equiv> Trueprop True"

private lemma goal_tagI: "PROP goal_tag x"
  unfolding goal_tag_def
  by simp

private method make_tag_goal for tag_id :: unit = (rule thin_rl[of "PROP goal_tag tag_id"])

private method clear_tagged_goal for tag_id :: unit  = (rule goal_tagI[of tag_id])

private definition "goals_end \<equiv> ()"
private definition "method_succeed \<equiv> ()"
private definition "method_failure \<equiv> ()"


method find_goal methods m = 
  (make_tag_goal goals_end, 
   defer_tac,
   (fails \<open>clear_tagged_goal method_succeed | clear_tagged_goal goals_end\<close>,
     (((m)[1],make_tag_goal method_succeed) 
     | defer_tac))+,
   clear_tagged_goal method_succeed,
   all \<open>(clear_tagged_goal goals_end)?\<close>)

end

notepad begin

  fix A B
  assume A: "A" and B: "B"

  have "A" "A" "B"
    apply (find_goal \<open>match conclusion in B \<Rightarrow> \<open>-\<close>\<close>)
    apply (rule B)
    by (rule A)+

  have "A \<and> A" "A \<and> A" "B"
    apply (find_goal \<open>fails \<open>simp\<close>\<close>) -- "find the first goal which cannot be simplified"
    apply (rule B)
    by (simp add: A)+

  have  "B" "A" "A \<and> A"
    apply (find_goal \<open>succeeds \<open>simp\<close>\<close>) -- "find the first goal which can be simplified (without doing so)"
    apply (rule conjI)
    by (rule A B)+
 
end


subsection \<open>Remove redundant subgoals\<close>

text \<open>Tries to solve subgoals by assuming the others and then using the given method.
      Backtracks over all possible re-orderings of the subgoals.\<close>

context begin

definition "protect (PROP P) \<equiv> P"

lemma protectE: "PROP protect P \<Longrightarrow> (PROP P \<Longrightarrow> PROP R) \<Longrightarrow> PROP R" by (simp add: protect_def)

private lemmas protect_thin = thin_rl[where V="PROP protect P" for P]

private lemma context_conjI_protected:
  assumes P: "PROP P"
  assumes PQ: "PROP protect (PROP P) \<Longrightarrow> PROP Q"
  shows
  "PROP P &&& PROP Q"
   apply -
   apply (rule P)
  apply (rule PQ)
  apply (simp add: protect_def)
  by (rule P)

private lemma conjunction_sym: "PROP P &&& PROP Q \<Longrightarrow> PROP Q &&& PROP P"
  apply (frule conjunctionD1)
  apply (drule conjunctionD2)
  apply (rule conjunctionI)
  by assumption+

private lemma conjunctionE:
  assumes PQ: "PROP P &&& PROP Q"
  assumes PQR: "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R"
  shows
  "PROP R"
  apply (rule PQR)
  apply (rule PQ[THEN conjunctionD1])
  by (rule PQ[THEN conjunctionD2])
  
private lemmas context_conjI_protected' = context_conjI_protected[THEN conjunction_sym]

method distinct_subgoals_strong methods m = 
  (safe_fold_subgoals \<open>
   (intro context_conjI_protected context_conjI_protected'; 
     (((elim protectE conjunctionE)?,clear_dummy_asm, solves \<open>m\<close>)
     | (elim protect_thin)?))\<close>)?

end


notepad begin
  {
  fix A B C
  assume A: "A"
  have "A" "B \<Longrightarrow> A"
  apply (distinct_subgoals_strong \<open>assumption\<close>)
  by (rule A)

  have "B \<Longrightarrow> A" "A" 
  by (distinct_subgoals_strong \<open>assumption\<close>, rule A) -- "backtracking required here"
  }

  {
  fix A B C
  
  assume B: "B"
  assume BC: "B \<Longrightarrow> C" "B \<Longrightarrow> A"
  have "A" "B \<longrightarrow> (A \<and> C)" "B"
  apply (distinct_subgoals_strong \<open>simp\<close>, rule B) -- "backtracking required here"
  by (simp add: BC)
  
  }
end


end
