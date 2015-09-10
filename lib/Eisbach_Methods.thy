(* Some useful boilerplate methods for Eisbach *)

theory Eisbach_Methods
imports "~~/src/HOL/Eisbach/Eisbach_Tools" 
        "subgoal_focus/Subgoal_Focus"
        "subgoal_focus/Subgoal_Methods"
begin

ML \<open>fun DROP_CASES f xq = (Seq.map snd o f) xq\<close>

(* Focus without matching. No focus elements are available directly. *)
method_setup focus = \<open>
  Scan.lift (Args.mode "concl") -- Method_Closure.parse_method >> (fn (b,m) => fn ctxt => fn facts => 
  let
    val m' = Method_Closure.method_evaluate m;
    val focus = if b then Subgoal.FOCUS else Subgoal.FOCUS_PARAMS; 
  in
   focus (fn {context,...} => DROP_CASES (m' context facts)) ctxt 1
   |> EMPTY_CASES
   end)
\<close>

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


context
begin

private definition "protect_concl x \<equiv> \<not> x"
private definition "protect_false \<equiv> False"

private lemma protect_start: "(protect_concl P \<Longrightarrow> protect_false) \<Longrightarrow> P" 
  by (simp add: protect_concl_def protect_false_def) (rule ccontr)

private lemma protect_end: "protect_concl P \<Longrightarrow> P \<Longrightarrow> protect_false" 
  by (simp add: protect_concl_def protect_false_def)

method only_asm methods m = 
  (match premises in H[thin]:_ (multi) \<Rightarrow> 
    \<open>rule protect_start, 
     match premises in H'[thin]:"protect_concl _" \<Rightarrow> 
       \<open>insert H,m;rule protect_end[OF H']\<close>\<close>)

method only_concl methods m = (match premises in _ (multi) \<Rightarrow> \<open>m\<close>)

end


end
