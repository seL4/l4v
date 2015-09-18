(* Some useful boilerplate methods for Eisbach *)

theory Eisbach_Methods
imports "~~/src/HOL/Eisbach/Eisbach_Tools" 
        "subgoal_focus/Subgoal_Focus"
        "subgoal_focus/Subgoal_Methods"
begin



method_setup all =
 \<open>Method_Closure.parse_method >> (fn m => fn ctxt => fn facts =>
   let
     fun tac i st' =
       Goal.restrict i 1 st'
       |> Method_Closure.method_evaluate m ctxt facts
       |> Seq.map (Goal.unrestrict i o snd)

   in EMPTY_CASES (ALLGOALS tac) end)
\<close>

method print_concl = (match conclusion in P for P \<Rightarrow> \<open>print_term P\<close>)

method_setup print_goal = \<open>Scan.succeed (fn ctxt => fn facts => 
  (fn st => (Output.writeln (Display.string_of_thm ctxt st); Seq.single ([],st))))\<close>




(* lift methods into logical tests *)

method_setup fails =
 \<open>Method_Closure.parse_method >> (fn m => fn ctxt => fn facts =>
   let
     fun fail_tac st' = 
       (case Seq.pull (Method_Closure.method_evaluate m ctxt facts st') of
          SOME _ => Seq.empty
        | NONE => Seq.single st')

   in EMPTY_CASES fail_tac end)
\<close>

method_setup succeeds =
 \<open>Method_Closure.parse_method >> (fn m => fn ctxt => fn facts =>
   let
     fun can_tac st' = 
       (case Seq.pull (Method_Closure.method_evaluate m ctxt facts st') of
          SOME (st'',_) => Seq.single st'
        | NONE => Seq.empty)

   in EMPTY_CASES can_tac end)
\<close>

(* focus without matching *)

method focus_concl methods m =
  ((fails \<open>erule thin_rl\<close>, match conclusion in _ \<Rightarrow> \<open>m\<close>)
  | match premises in H:_ (multi) \<Rightarrow> \<open>m\<close>)

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

context begin

private definition "goal_tag (x :: unit) \<equiv> TERM x"

private lemma goal_tagI: "PROP goal_tag x"
  unfolding goal_tag_def
  by (rule termI)

private method make_tag_goal for tag_id :: unit = (rule thin_rl[of "PROP goal_tag tag_id"])

private method clear_tagged_goal for tag_id :: unit  = (rule goal_tagI[of tag_id])

private definition "goals_end \<equiv> ()"
private definition "method_succeed \<equiv> ()"
private definition "method_failure \<equiv> ()"


private method defer_tac = tactic \<open>defer_tac 1\<close>

method find_goal methods m = 
  (make_tag_goal goals_end, 
   defer_tac,
   (fails \<open>clear_tagged_goal method_succeed | clear_tagged_goal goals_end\<close>,
     (((m)[1],make_tag_goal method_succeed) 
     | defer_tac))+,
   clear_tagged_goal method_succeed,
   all \<open>(clear_tagged_goal goals_end)?\<close>)

end

(* examples *)

notepad begin

  fix A B
  assume A: "A" and B: "B"

  have "A" "A" "B"
    apply (find_goal \<open>match conclusion in B \<Rightarrow> \<open>-\<close>\<close>)
    apply (rule B)
    by (rule A)+

  have "A \<and> A" "A \<and> A" "B"
    apply (find_goal \<open>fails \<open>simp\<close>\<close>) (* find the first goal which cannot be simplified *)
    apply (rule B)
    by (simp add: A)+

  have  "B" "A" "A \<and> A"
    apply (find_goal \<open>succeeds \<open>simp\<close>\<close>) (* find the first goal which can be simplified (without doing so) *)
    apply (rule conjI)
    by (rule A B)+


  fix D C
  assume DC:"D \<Longrightarrow> C"
  have "D \<and> D \<Longrightarrow> C \<and> C"
  apply (only_asm \<open>simp\<close>) (* stash conclusion before applying method *)
  apply (only_concl \<open>simp add: DC\<close>) (* hide premises from method *)
  by (rule DC)
end
    


end
