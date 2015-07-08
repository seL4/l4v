(* Some useful boilerplate methods for Eisbach *)

theory Eisbach_Methods
imports "~~/src/HOL/Eisbach/Eisbach_Tools" 
        "wp/NonDetMonadVCG" 
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


definition "packed_valid P f si r s \<equiv> P si \<and> (r, s) \<in> fst (f si)"

lemma packed_validE:"(\<And>si r s. packed_valid P f si r s \<Longrightarrow> Q r s) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (clarsimp simp: valid_def packed_valid_def)

lemma packed_validI: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<forall>si r s. packed_valid P f si r s \<longrightarrow> Q r s"
  apply (clarsimp simp: valid_def packed_valid_def)
  by auto

definition "packed_validR P f si r s \<equiv> P si \<and> (Inr r, s) \<in> fst (f si)"


lemma packed_validRE:"(\<And>si r s. packed_validR P f si r s \<Longrightarrow> Q r s) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp: validE_R_def validE_def valid_def packed_validR_def)
  by (metis sum.case sumE)

lemma packed_validRI: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<Longrightarrow> \<forall>si r s. packed_validR P f si r s \<longrightarrow> Q r s"
  apply (clarsimp simp: valid_def validE_R_def validE_def packed_validR_def)
  by fastforce

lemma trivial_imp: "\<forall>r s. Q r s \<longrightarrow> Q r s" by simp

lemma uncurry2: "\<forall>r s. Q r s \<and> Q' r s \<longrightarrow> Q'' r s \<Longrightarrow> \<forall>r s. Q r s \<longrightarrow> Q' r s \<longrightarrow> Q'' r s"
  by simp


named_theorems hoare_post_imps

lemmas [hoare_post_imps] = hoare_post_imp_R hoare_post_imp[rotated]

method post_asm_raw methods m = 
  (drule hoare_post_imps,
   atomize (full),
   focus (concl) 
     \<open>intro impI allI, 
      m, 
      atomize (full),
      ((rule uncurry2)+)?\<close>,
   rule trivial_imp)

method post_asm methods m = 
  (post_asm_raw \<open>(simp only: bipred_conj_def pred_conj_def)?,(elim conjE)?,m\<close>)


named_theorems packed_validEs

lemmas [packed_validEs] = packed_validE packed_validRE

named_theorems packed_validIs

lemmas [packed_validIs] = packed_validI packed_validRI

method post_raw methods m = 
  (focus 
    \<open>rule packed_validEs,
     focus (concl) \<open>m,fold_subgoals\<close>, 
     atomize (full),
     rule packed_validI\<close>)

method post methods m = 
  (post_raw 
     \<open>intro impI conjI allI,
      distinct_subgoals,
      all \<open>m\<close>,
      fold_subgoals\<close>)

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
