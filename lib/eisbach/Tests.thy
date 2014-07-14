(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Tests
imports Tutorial
begin


lemma thin_rl': "PROP V \<Longrightarrow> PROP V \<Longrightarrow> PROP W \<Longrightarrow> PROP W" by simp

method_definition grule facts rule asm = (rule rule[OF asm],erule thin_rl'[OF asm])

method_definition gen_guess for my_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool" facts my_allE =
          (match prems in
            U: "my_all(\<lambda>x. ?P (x :: 'a))" => 
                ((match "?concl" in "?H (?y :: 'a)" => (grule rule: my_allE[where x="?y"] asm: U))
              | (match prems in "?H (?y :: 'a)" => (grule rule: my_allE[where x="?y"] asm: U))))

method_definition gen_elim for my_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool" and x :: "'a" facts my_allE =
          (match prems in
            U: "my_all(\<lambda>x. ?P (x :: 'a))" => (grule rule: my_allE[where x="x"] asm: U))          

method_definition check_input_consts for my_all :: "('d \<Rightarrow> bool) \<Rightarrow> bool" and my_all2 :: "('c \<Rightarrow> bool) \<Rightarrow> bool"  =
          (insert refl[where t="my_all x"],insert refl[where t="my_all2 y"])

lemma "A"
  apply (check_input_consts All All)
  oops

lemma
  fixes x :: 'b
  shows
  "\<forall>x. P x \<Longrightarrow> P x"
  apply (gen_elim All "x" my_allE:allE) (* "All" should be parsed with 'b type *)
  apply assumption
  done

lemma
  fixes x :: 'c
  shows
  "\<forall>x. P x \<Longrightarrow> P x"
  apply (gen_guess All my_allE:allE) (* "All" is polymorphic here *)
  apply assumption
  done

method_definition guess_all = (gen_guess All my_allE:allE)

lemma
  fixes x :: 'c
  shows
  "\<forall>x. P x \<Longrightarrow> P x"
  apply guess_all
  apply assumption
  done

method_definition testOF facts my_fact my_fact2 = (insert conjI[OF my_fact],insert my_fact2[OF my_fact])

ML_method_definition assert_goal for x :: "prop" = "
  (fn goal => if (hd (prems_of goal) = x) then Seq.single goal else Seq.empty)"

lemma
  "P"
  apply (assert_goal "P")
  apply (testOF my_fact: TrueI my_fact2: conjI)
  apply (assert_goal "(\<And>Q. Q \<Longrightarrow> True \<and> Q) \<Longrightarrow> (\<And>Q. Q \<Longrightarrow> True \<and> Q) \<Longrightarrow> P")
  oops

(* Testing inner methods *)

method_definition all_rules facts rule = (ALLGOALS (rule rule))

lemma
  assumes A: "P" 
  shows "P \<and> P"
  apply (rule conjI)
  apply (all_rules rule: A)
  done

method_definition all_spec for x :: 'a = (ALLGOALS (drule spec[where x=x]))

lemma "(\<forall>x. P x) \<Longrightarrow> (\<forall>x. Q x) \<Longrightarrow> P y \<and> Q y"
    apply (rule conjI)
    apply (all_spec y)+
    apply assumption+
    done



ML_method_definition ifm srcs flag1 methods meth  = 
  {* if flag1 = "debug" then meth else all_tac *}

method_definition ifm' srcs flag1 = (ifm flag1 (rule conjI))

lemma "P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q"
  apply (ifm' "notdebug")
  apply (ifm' "debug")
  apply assumption+
  done

method_definition ifm'' srcs flag1 for x = (ifm' flag1, print_term x)

lemma "P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q"
  apply (ifm'' "notdebug" P)
  apply (ifm'' "debug" P)
  apply assumption+
  done

end



