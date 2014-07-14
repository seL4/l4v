(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Tutorial
imports Focus
begin

(*Some debugging methods*)

ML_method_definition print_term for x = {* 
  let 
    val _ = tracing ("print_term: " ^ (Pretty.string_of (Syntax.pretty_term ctxt x)))
  in
    all_tac end;*}


ML_method_definition print_fact facts f = {* 
  let 
    val _ = tracing ("print_fact: " ^ (Pretty.string_of (Pretty.block (Pretty.commas (map (Syntax.pretty_term ctxt o prop_of) f)))))
  in
    all_tac end;*}

(* Basic methods *)

method_definition my_intros = (rule conjI | rule impI)

lemma "P \<and> Q \<longrightarrow> (Z \<and> X)"
    apply my_intros+
    oops
    
method_definition my_intros' facts intros = (rule conjI | rule impI | rule intros)

lemma "P \<and> Q \<longrightarrow> Z \<or> X"
    apply (my_intros' intros: disjI1)+
    oops

method_definition my_spec for x :: 'a = (drule spec[where x="x"])

lemma "\<forall>x. P x \<Longrightarrow> P x"
    apply (my_spec x)
    apply assumption
    done
  
(*No "_tac" support. New explicit "focus" command works around it*)

lemma focus_test:
  shows "\<And>x. \<forall>x. P x \<Longrightarrow> P x"
  apply (my_spec x,assumption)? (* Wrong x*)
  focus
    thm focus_prems (* Bound by "focus" *)
    term ?concl
    apply (my_spec x) (* Newly fixed x*)
  unfocus
  apply assumption
done

(* This can get a bit complicated with schematics floating around.
   The new "apply" agressively ensures sound instantiations *)

schematic_lemma focus_test_schematic:
  "\<And>x. ?P \<Longrightarrow> ?Q \<and> R x"
  apply assumption? (* Wrong *)
  focus
    apply assumption? (* Still fails, though "x" is fixed*)
    apply (rule conjI)
    thm focus_prems (* Fixed P is ?P for any instantiation*)
    apply (rule focus_prems)
  unfocus
  apply (erule FalseE)
  done
  thm focus_test_schematic (* Both ?P and ?Q are False because of use of focus_prems*)
  
(*Focusing and matching*)

method_definition focus_test = (print_term "?concl", print_fact f: prems )

lemma "\<And>x. P x \<and> Q x \<Longrightarrow> R x y \<Longrightarrow> A x y"
  apply focus_test (*Meta-Quantified variables become fixed*)
  oops

method_definition match_test = 
  (match prems in U: "?P ?x \<and> ?Q ?x" \<Rightarrow>
    (print_term "?P",
     print_term "?Q", 
     print_term "?x",
     print_fact f: U))
  
lemma "\<And>x. P x \<and> Q x \<Longrightarrow> A x \<and> B x \<Longrightarrow> R x y \<Longrightarrow> True"
  apply match_test (*Valid match, but not quite what we were expecting..*)
  back (* Can backtrack over matches, exploring all bindings*)
  back
  back
  back
  back
  back (* Found the other conjunction *)
  back
  back
  back
  back
  back
  oops

method_definition subgoal_with for x :: bool methods meth =
  (rule cut_rl[where psi="?x",rotated],meth#)

(*Matches are exclusive. Backtracking will not occur
  past a match*)
  
method_definition match_test' = 
  (match "?concl" in 
    "?P \<and> ?Q" \<Rightarrow>
      (print_term ?P,print_term ?Q,rule conjI[where P="?P" and Q="?Q"] \<mapsto> assumption)
    \<bar> "?P" \<Rightarrow> (print_term ?P)
  )

(*Solves goal*)
lemma "P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q"
  apply (match_test')
  done

(*Fall-through case never taken*)
lemma "P \<and> Q"
  apply (match_test')? (*Duplicate match bug*)
  oops

lemma "P"
  apply (match_test')
  oops


method_definition my_spec_guess = 
  (match "?concl" in "?P (?x :: 'a)" \<Rightarrow> 
      (drule spec[where x="?x"],
       print_term "?P", 
       print_term "?x"))
  
lemma "\<forall>x. P (x :: nat) \<Longrightarrow> Q (x :: nat)"
    apply my_spec_guess
    oops
    
    
method_definition my_spec_guess2 =
  (match prems in "\<forall>x. ?P x \<longrightarrow> ?Q x" and "?P ?x" \<Rightarrow> 
      (drule spec[where x="?x"], 
       print_term "?P", 
       print_term "?Q"))
  
lemma "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> Q x \<Longrightarrow> Q x"
    apply my_spec_guess2? (*Fails. Note that both "?P"s must match *)
    oops
    
lemma "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> P x \<Longrightarrow> Q x"
    apply my_spec_guess2
    oops
    
(* Higher-order methods*)

method_definition higher_order_test for x methods meth =
  (cases x,meth,meth)
  
lemma
  assumes A: "x = Some a"
  shows "the x = a"
  apply (higher_order_test x (simp add: A))
  oops
  

(*Recursion*)

method_definition recursion_test for x =
  ((match "x" in "?A \<and> ?B" \<Rightarrow> 
    (print_term "?A", 
     print_term "?B",
     recursion_test "?A",
     recursion_test "?B")) | -)
  
lemma "P"
  apply (recursion_test "(A \<and> D) \<and> (B \<and> C)")
  oops
  
  
(* Custom combinators (Currently only ML supported) *)
(* See Method_Definition.thy for source*)
  
lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  apply ((rule conjI)#)? (* Doesn't solve the goal! *)
  apply (rule conjI,assumption,assumption)#
  done
      
lemma "A \<and> B \<Longrightarrow> A \<or> B"
  apply (cases A \<mapsto> cases B) (* Explode cases *)
  prefer 4
  apply ((rule disjI1,assumption | rule disjI2,assumption)?)@ (*Apply once to all goals*)
  oops

lemma "A \<Longrightarrow> A \<and> A"
  apply (rule conjI)
  apply (assumption)@ (* Apply to all subgoals (must succeed) *)
  done
  
(*Demo*)

method_definition solve_bool = 
  (assumption
  | intro conjI impI disjCI iffI notI allI
  | drule notnotD Meson.not_exD Meson.not_allD
  | elim impCE conjE disjE exE
  | subst ex_simps all_simps
  | subst (asm) ex_simps all_simps
  | (erule notE \<mapsto> solve_bool#))+
  
lemma "((A \<or> B) \<and> (A \<longrightarrow> C) \<and> (B \<longrightarrow> C)) \<longrightarrow> C"
  apply solve_bool
  done
  
method_definition guess_all =
          (match prems in "\<forall>x. ?P (x :: 'a)" \<Rightarrow>
            (match prems in "?H (?y :: 'a)" \<Rightarrow>
               (erule allE[where P="?P" and x="?y"])
           | match "?concl" in "?H (?y :: 'a)" \<Rightarrow>
               (erule allE[where P="?P" and x="?y"])))
          
lemma "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> P y \<Longrightarrow> Q y"
  apply guess_all
  apply solve_bool
done

lemma "(\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow>  P z \<Longrightarrow> P y \<Longrightarrow> Q y"
  apply (guess_all,solve_bool)# (*Try it without #*)
done

method_definition guess_ex = 
  (match "?concl" in
    "\<exists>x. ?P (x :: 'a)" \<Rightarrow>
      (match prems in "?H (?x :: 'a)" \<Rightarrow>
              (rule exI[where x="?x"])))
  
lemma "P x \<Longrightarrow> \<exists>x. P x"
  apply guess_ex
  apply solve_bool
  done
  
method_definition solve_taut = 
  (((guess_ex | guess_all) \<mapsto> solve_taut#) 
      | (solve_bool \<mapsto> solve_taut#))
                            
lemma "(\<forall>x. P x) \<and> (\<forall>x. Q x) \<Longrightarrow> (\<forall>x. P x \<and> Q x)"
  apply solve_taut
  done

lemma "(\<exists>x. P x) \<or> (\<exists>x. Q x) \<Longrightarrow> (\<exists>x. P x \<or> Q x)"
  apply solve_taut
  done
   

lemma "\<exists>x. (P x \<longrightarrow> (\<forall>x. P x))"
  apply solve_taut
  done
  
lemma "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> \<exists>x. P x \<Longrightarrow> \<exists>x. Q x"
  apply solve_taut
  done 

(* Fact groups *)

(*Square brackets declare it as a fact group*)

method_definition my_rules facts [my_erules] = (erule my_erules,assumption)

lemma "P \<and> Q \<Longrightarrow> P"
  apply my_rules?
  oops

declare conjE[add my_erules]

lemma "P \<and> Q \<Longrightarrow> P"
  apply (my_rules)
  done

declare conjE[del my_erules]

(* Can be added at invocation time as usual *)
lemma "P \<and> Q \<Longrightarrow> P"
  apply (my_rules)?
  apply (my_rules my_erules: conjE)
  done

(* Currently these are not dynamic facts and cannot be accessed as such*)

(* thm my_erules *) (* Error *)

(*We can re-declare it in another method and share its collection*)

declare conjE[add my_erules]

method_definition my_rules' facts [my_erules] = (erule my_erules,assumption)

lemma "P \<and> Q \<Longrightarrow> P"
  apply (my_rules')
  done

    
end
