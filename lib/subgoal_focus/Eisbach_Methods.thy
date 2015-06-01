(* Some useful boilerplate methods for Eisbach *)

theory Eisbach_Methods
imports "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

ML \<open>fun DROP_CASES f xq = (Seq.map snd o f) xq\<close>

(* Focus without matching. No focus elements are available directly. *)
method_setup focus = \<open>
  Method_Closure.parse_method >> (fn m => fn ctxt => fn facts => 
  let
    val m' = Method_Closure.method_evaluate m;
  in
   Subgoal.FOCUS (fn {context,...} => DROP_CASES (m' context facts)) ctxt 1
   |> EMPTY_CASES
   end)
\<close>

method print_concl = (match conclusion in P for P \<Rightarrow> \<open>print_term P\<close>)

end