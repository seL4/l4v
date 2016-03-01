(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      VcgEx.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

section {* Examples using Statespaces *}

theory VcgExSP imports "../HeapList" "../Vcg" begin


subsection {* State Spaces *}

text {*
 First of all we provide a store of program variables that
 occur in the programs considered later.  Slightly unexpected
 things may happen when attempting to work with undeclared variables.
*}


hoarestate state_space = 
  A :: nat
  I :: nat
  M :: nat
  N :: nat
  R :: nat
  S :: nat
  B :: bool
  Abr:: string

lemma (in state_space)"\<Gamma>\<turnstile> \<lbrace>\<acute>N = n\<rbrace> LOC \<acute>N :== 10;; \<acute>N :== \<acute>N + 2 COL \<lbrace>\<acute>N = n\<rbrace>"
  by vcg

text {* Internally we decorate the state components in the statespace with the 
suffix @{text "_'"},
to avoid cluttering the namespace with the simple names that could no longer
be used for logical variables otherwise. 
*}

text {* We will first consider programs without procedures, later on
we will regard procedures without global variables and finally we
will get the full pictures: mutually recursive procedures with global
variables (including heap).
*}

subsection {* Basic Examples *}

text {*
 We look at few trivialities involving assignment and sequential
 composition, in order to get an idea of how to work with our
 formulation of Hoare Logic.
*}

text {*
 Using the basic rule directly is a bit cumbersome.
*}
 
lemma (in state_space) "\<Gamma>\<turnstile> {|\<acute>N = 5|} \<acute>N :== 2 * \<acute>N {|\<acute>N = 10|}"
  apply (rule HoarePartial.Basic)  
  apply simp
  done
 
lemma (in state_space) "\<Gamma>\<turnstile> \<lbrace>True\<rbrace> \<acute>N :== 10 \<lbrace>\<acute>N = 10\<rbrace>"
  by vcg

lemma (in state_space) "\<Gamma>\<turnstile> \<lbrace>2 * \<acute>N = 10\<rbrace> \<acute>N :== 2 * \<acute>N \<lbrace>\<acute>N = 10\<rbrace>"
  by vcg

lemma (in state_space) "\<Gamma>\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> \<acute>N :== 2 * \<acute>N \<lbrace>\<acute>N = 10\<rbrace>"
  apply vcg
  apply simp
  done

lemma (in state_space) "\<Gamma>\<turnstile> \<lbrace>\<acute>N + 1 = a + 1\<rbrace> \<acute>N :== \<acute>N + 1 \<lbrace>\<acute>N = a + 1\<rbrace>"
  by vcg 

lemma (in state_space) "\<Gamma>\<turnstile> \<lbrace>\<acute>N = a\<rbrace> \<acute>N :== \<acute>N + 1 \<lbrace>\<acute>N = a + 1\<rbrace>"
  apply vcg
  apply simp
  done
 

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>a = a \<and> b = b\<rbrace> \<acute>M :== a;; \<acute>N :== b \<lbrace>\<acute>M = a \<and> \<acute>N = b\<rbrace>"
  by vcg

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>True\<rbrace> \<acute>M :== a;; \<acute>N :== b \<lbrace>\<acute>M = a \<and> \<acute>N = b\<rbrace>"
  by vcg

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = a \<and> \<acute>N = b\<rbrace>
                \<acute>I :== \<acute>M;; \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I
              \<lbrace>\<acute>M = b \<and> \<acute>N = a\<rbrace>"
  apply vcg
  apply simp
  done

text {*
We can also perform verification conditions generation step by step by using
the @{text vcg_step} method.
*}

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = a \<and> \<acute>N = b\<rbrace>
               \<acute>I :== \<acute>M;; \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I
              \<lbrace>\<acute>M = b \<and> \<acute>N = a\<rbrace>"
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply simp
  done


text {*
 In the following assignments we make use of the consequence rule in
 order to achieve the intended precondition.  Certainly, the
 @{text vcg} method is able to handle this case, too.
*}

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = \<acute>N\<rbrace> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
proof -
  have "\<lbrace>\<acute>M = \<acute>N\<rbrace> \<subseteq> \<lbrace>\<acute>M + 1 \<noteq> \<acute>N\<rbrace>"
    by auto
  also have "\<Gamma>\<turnstile> \<dots> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
    by vcg
  finally show ?thesis .
qed

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = \<acute>N\<rbrace> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
proof -
  have "\<And>m n::nat. m = n \<longrightarrow> m + 1 \<noteq> n"
      -- {* inclusion of assertions expressed in ``pure'' logic, *}
      -- {* without mentioning the state space *}
    by simp
  also have "\<Gamma>\<turnstile> \<lbrace>\<acute>M + 1 \<noteq> \<acute>N\<rbrace> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
    by vcg
  finally show ?thesis .
qed

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = \<acute>N\<rbrace> \<acute>M :== \<acute>M + 1 \<lbrace>\<acute>M \<noteq> \<acute>N\<rbrace>"
  apply vcg
  apply simp
  done

subsection {* Multiplication by Addition *}

text {*
 We now do some basic examples of actual \texttt{WHILE} programs.
 This one is a loop for calculating the product of two natural
 numbers, by iterated addition.  We first give detailed structured
 proof based on single-step Hoare rules.
*}

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
      WHILE \<acute>M \<noteq> a
      DO \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 OD
      \<lbrace>\<acute>S = a * b\<rbrace>"
proof -
  let "\<Gamma>\<turnstile> _ ?while _" = ?thesis
  let "\<lbrace>\<acute>?inv\<rbrace>" = "\<lbrace>\<acute>S = \<acute>M * b\<rbrace>"

  have "\<lbrace>\<acute>M = 0 & \<acute>S = 0\<rbrace> \<subseteq> \<lbrace>\<acute>?inv\<rbrace>" by auto
  also have "\<Gamma>\<turnstile> \<dots> ?while \<lbrace>\<acute>?inv \<and> \<not> (\<acute>M \<noteq> a)\<rbrace>"
  proof
    let ?c = "\<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1"
    have "\<lbrace>\<acute>?inv \<and> \<acute>M \<noteq> a\<rbrace> \<subseteq> \<lbrace>\<acute>S + b = (\<acute>M + 1) * b\<rbrace>"
      by auto
    also have "\<Gamma>\<turnstile> \<dots> ?c \<lbrace>\<acute>?inv\<rbrace>" by vcg
    finally show "\<Gamma>\<turnstile> \<lbrace>\<acute>?inv \<and> \<acute>M \<noteq> a\<rbrace> ?c \<lbrace>\<acute>?inv\<rbrace>" .
  qed
  also have "\<lbrace>\<acute>?inv \<and> \<not> (\<acute>M \<noteq> a)\<rbrace> \<subseteq> \<lbrace>\<acute>S = a * b\<rbrace>" by auto
  finally show ?thesis by blast
qed


text {*
 The subsequent version of the proof applies the @{text vcg} method
 to reduce the Hoare statement to a purely logical problem that can be
 solved fully automatically.  Note that we have to specify the
 \texttt{WHILE} loop invariant in the original statement.
*}

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          WHILE \<acute>M \<noteq> a
          INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
          DO \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 OD
          \<lbrace>\<acute>S = a * b\<rbrace>"
  apply vcg
  apply auto
  done

text {* Here some examples of ``breaking'' out of a loop *}

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          TRY       
            WHILE True
            INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
            DO IF \<acute>M = a THEN THROW ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 FI OD
          CATCH
            SKIP
          END
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          TRY       
            WHILE True
            INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
            DO IF \<acute>M = a THEN \<acute>Abr :== ''Break'';;THROW 
               ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 
               FI 
            OD
          CATCH
            IF \<acute>Abr = ''Break'' THEN SKIP ELSE Throw FI
          END
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done







text {* Some more syntactic sugar, the label statement @{text "\<dots> \<bullet> \<dots>"} as shorthand
for the @{text "TRY-CATCH"} above, and the @{text "RAISE"} for an state-update followed
by a @{text "THROW"}. 
*}
lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          \<lbrace>\<acute>Abr = ''Break''\<rbrace>\<bullet> WHILE True INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
           DO IF \<acute>M = a THEN RAISE \<acute>Abr :== ''Break'' 
              ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 
              FI 
           OD
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          TRY       
            WHILE True
            INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
            DO IF \<acute>M = a THEN RAISE \<acute>Abr :== ''Break'' 
               ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 
               FI 
            OD
          CATCH
            IF \<acute>Abr = ''Break'' THEN SKIP ELSE Throw FI
          END
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          \<lbrace>\<acute>Abr = ''Break''\<rbrace> \<bullet> WHILE True
          INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
          DO IF \<acute>M = a THEN RAISE \<acute>Abr :== ''Break'' 
               ELSE \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 
               FI 
          OD
          \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
apply auto
done

text {* Blocks *}

lemma  (in state_space)
  shows "\<Gamma>\<turnstile>\<lbrace>\<acute>I = i\<rbrace> LOC \<acute>I;; \<acute>I :== 2  COL \<lbrace>\<acute>I \<le> i\<rbrace>"
  apply vcg
  by simp

 
subsection {* Summing Natural Numbers *}

text {*
 We verify an imperative program to sum natural numbers up to a given
 limit.  First some functional definition for proper specification of
 the problem.
*}

primrec
  sum :: "(nat => nat) => nat => nat"
where
  "sum f 0 = 0"
| "sum f (Suc n) = f n + sum f n"

syntax
  "_sum" :: "idt => nat => nat => nat"
    ("SUMM _<_. _" [0, 0, 10] 10)
translations
  "SUMM j<k. b" == "CONST sum (\<lambda>j. b) k"

text {*
 The following proof is quite explicit in the individual steps taken,
 with the @{text vcg} method only applied locally to take care of
 assignment and sequential composition.  Note that we express
 intermediate proof obligation in pure logic, without referring to the
 state space.
*}

theorem (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>
           \<acute>S :== 0;; \<acute>I :== 1;;
           WHILE \<acute>I \<noteq> n
           DO
             \<acute>S :== \<acute>S + \<acute>I;;
             \<acute>I :== \<acute>I + 1
           OD
           \<lbrace>\<acute>S = (SUMM j<n. j)\<rbrace>"
  (is "\<Gamma>\<turnstile> _ (_;; ?while) _")
proof -
  let ?sum = "\<lambda>k. SUMM j<k. j"
  let ?inv = "\<lambda>s i. s = ?sum i"

  have "\<Gamma>\<turnstile> \<lbrace>True\<rbrace> \<acute>S :== 0;; \<acute>I :== 1 \<lbrace>?inv \<acute>S \<acute>I\<rbrace>"
  proof -
    have "True \<longrightarrow> 0 = ?sum 1"
      by simp
    also have "\<Gamma>\<turnstile> \<lbrace>\<dots>\<rbrace> \<acute>S :== 0;; \<acute>I :== 1 \<lbrace>?inv \<acute>S \<acute>I\<rbrace>"
      by vcg
    finally show ?thesis .
  qed
  also have "\<Gamma>\<turnstile> \<lbrace>?inv \<acute>S \<acute>I\<rbrace> ?while \<lbrace>?inv \<acute>S \<acute>I \<and> \<not> \<acute>I \<noteq> n\<rbrace>"
  proof
    let ?body = "\<acute>S :== \<acute>S + \<acute>I;; \<acute>I :== \<acute>I + 1"
    have "\<And>s i. ?inv s i \<and> i \<noteq> n \<longrightarrow>  ?inv (s + i) (i + 1)"
      by simp
    also have "\<Gamma>\<turnstile> \<lbrace>\<acute>S + \<acute>I = ?sum (\<acute>I + 1)\<rbrace> ?body \<lbrace>?inv \<acute>S \<acute>I\<rbrace>"
      by vcg
    finally show "\<Gamma>\<turnstile> \<lbrace>?inv \<acute>S \<acute>I \<and> \<acute>I \<noteq> n\<rbrace> ?body \<lbrace>?inv \<acute>S \<acute>I\<rbrace>" .
  qed
  also have "\<And>s i. s = ?sum i \<and> \<not> i \<noteq> n \<longrightarrow> s = ?sum n"
    by simp 
  finally show ?thesis .
qed

text {*
 The next version uses the @{text vcg} method, while still explaining
 the resulting proof obligations in an abstract, structured manner.
*}

theorem (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>
           \<acute>S :== 0;; \<acute>I :== 1;;
           WHILE \<acute>I \<noteq> n
           INV \<lbrace>\<acute>S = (SUMM j<\<acute>I. j)\<rbrace>
           DO
             \<acute>S :== \<acute>S + \<acute>I;;
             \<acute>I :== \<acute>I + 1
           OD
          \<lbrace>\<acute>S = (SUMM j<n. j)\<rbrace>"
proof -
  let ?sum = "\<lambda>k. SUMM j<k. j"
  let ?inv = "\<lambda>s i. s = ?sum i"

  show ?thesis
  proof vcg
    show "?inv 0 1" by simp
  next
    fix i s assume "?inv s i" "i \<noteq> n"
    thus "?inv (s + i) (i + 1)" by simp
  next 
    fix i s assume x: "?inv s i" "\<not> i \<noteq> n"  
    thus "s = ?sum n" by simp
  qed
qed

text {*
 Certainly, this proof may be done fully automatically as well, provided
 that the invariant is given beforehand.
*}

theorem (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>True\<rbrace>
           \<acute>S :== 0;; \<acute>I :== 1;;
           WHILE \<acute>I \<noteq> n
           INV \<lbrace>\<acute>S = (SUMM j<\<acute>I. j)\<rbrace>
           DO
             \<acute>S :== \<acute>S + \<acute>I;;
             \<acute>I :== \<acute>I + 1
           OD
           \<lbrace>\<acute>S = (SUMM j<n. j)\<rbrace>"
  apply vcg 
  apply auto
  done

subsection {* SWITCH *}

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> SWITCH \<acute>B 
                        {True} \<Rightarrow> \<acute>N :== 6
                      | {False} \<Rightarrow> \<acute>N :== 7
                     END
          \<lbrace>\<acute>N > 5\<rbrace>"
apply vcg
apply simp
done

lemma (in state_space)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> SWITCH \<acute>N 
                        {v. v < 5} \<Rightarrow> \<acute>N :== 6
                      | {v. v \<ge> 5} \<Rightarrow> \<acute>N :== 7
                     END
          \<lbrace>\<acute>N > 5\<rbrace>"
apply vcg
apply simp
done

subsection {* (Mutually) Recursive Procedures *}

subsubsection {* Factorial *}

text {* We want to define a procedure for the factorial. We first
define a HOL functions that calculates it to specify the procedure later on.
*}

primrec fac:: "nat \<Rightarrow> nat"
where
"fac 0 = 1" |
"fac (Suc n) = (Suc n) * fac n"

lemma fac_simp [simp]: "0 < i \<Longrightarrow>  fac i = i * fac (i - 1)"
  by (cases i) simp_all

text {* Now we define the procedure *}


procedures 
  Fac (N::nat|R::nat)  
  "IF \<acute>N = 0 THEN \<acute>R :== 1
   ELSE \<acute>R :== CALL Fac(\<acute>N - 1);;
        \<acute>R :== \<acute>N * \<acute>R
   FI"

print_locale Fac_impl

text {*
To see how a call is syntactically translated you can switch off the
printing translation via the configuration option @{text hoare_use_call_tr'}
*}

context Fac_impl 
begin
text {*
@{term "CALL Fac(\<acute>N,\<acute>R)"} is internally:
*}
declare [[hoare_use_call_tr' = false]]
text {*
@{term "CALL Fac(\<acute>N,\<acute>R)"}
*}
term "CALL Fac(\<acute>N,\<acute>R)"
declare [[hoare_use_call_tr' = true]]


text {*
Now let us prove that @{term "Fac"} meets its specification. 
*}

end


lemma (in Fac_impl) Fac_spec':
  shows "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>{\<sigma>} PROC Fac(\<acute>N,\<acute>R) \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply vcg
  apply simp
  done


text {* 
Since the factorial was implemented recursively,
the main ingredient of this proof is, to assume that the specification holds for 
the recursive call of @{term Fac} and prove the body correct.
The assumption for recursive calls is added to the context by
the rule @{thm [source] HoarePartial.ProcRec1} 
(also derived from general rule for mutually recursive procedures):
@{thm [display] HoarePartial.ProcRec1 [no_vars]}
The verification condition generator will infer the specification out of the
context when it encounters a recursive call of the factorial.
*}

text {* We can also step through verification condition generation. When
the verification condition generator encounters a procedure call it tries to
  use the rule @{text ProcSpec}. To be successful there must be a specification
of the procedure in the context.  
*}

lemma (in Fac_impl) Fac_spec1:
  shows "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>{\<sigma>} \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply vcg_step
  apply   vcg_step
  apply  vcg_step
  apply vcg_step
  apply vcg_step
  apply simp
  done


text {* Here some Isar style version of the proof *}
lemma (in Fac_impl) Fac_spec2:
  
  shows "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>{\<sigma>} \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>"
proof (hoare_rule HoarePartial.ProcRec1)
  have Fac_spec: "\<forall>\<sigma>. \<Gamma>,(\<Theta>\<union>(\<Union>\<sigma>. {({\<sigma>}, Fac_'proc, \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>,{})}))
                       \<turnstile> {\<sigma>} \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>"
    apply (rule allI)
    apply (rule hoarep.Asm) 
    by simp
  show "\<forall>\<sigma>. \<Gamma>,(\<Theta>\<union>(\<Union>\<sigma>. {({\<sigma>}, Fac_'proc, \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>,{})}))
            \<turnstile> {\<sigma>} IF \<acute>N = 0 THEN \<acute>R :== 1
            ELSE \<acute>R :== CALL Fac(\<acute>N - 1);; \<acute>R :== \<acute>N * \<acute>R FI \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>"
    apply vcg
    apply simp
    done
qed

text {* To avoid retyping of potentially large pre and postconditions in 
the previous proof we can use the casual term abbreviations of the Isar 
language.
*}

lemma (in Fac_impl) Fac_spec3:
  shows "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>{\<sigma>} \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>" 
  (is "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>(?Pre \<sigma>) ?Fac (?Post \<sigma>)")
proof (hoare_rule HoarePartial.ProcRec1)
  have Fac_spec: "\<forall>\<sigma>. \<Gamma>,(\<Theta>\<union>(\<Union>\<sigma>. {(?Pre \<sigma>, Fac_'proc, ?Post \<sigma>,{})}))
                       \<turnstile>(?Pre \<sigma>) ?Fac (?Post \<sigma>)"
    apply (rule allI)
    apply (rule hoarep.Asm) 
    by simp
  show "\<forall>\<sigma>. \<Gamma>,(\<Theta>\<union>(\<Union>\<sigma>. {(?Pre \<sigma>, Fac_'proc, ?Post \<sigma>,{})}))
            \<turnstile> (?Pre \<sigma>) IF \<acute>N = 0 THEN \<acute>R :== 1
            ELSE \<acute>R :== CALL Fac(\<acute>N - 1);; \<acute>R :== \<acute>N * \<acute>R FI (?Post \<sigma>)"
    apply vcg
    apply simp
    done
qed

text {* The previous proof pattern has still some kind of inconvenience.
The augmented context is always printed in the proof state. That can
mess up the state, especially if we have large specifications. This may
be annoying if we want to develop single step or structured proofs. In this
case it can be a good idea to introduce a new variable for the augmented
context.
*}

lemma (in Fac_impl) Fac_spec4:
  shows "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>{\<sigma>} \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>" 
  (is "\<forall>\<sigma>. \<Gamma>,\<Theta>\<turnstile>(?Pre \<sigma>) ?Fac (?Post \<sigma>)")
proof (hoare_rule HoarePartial.ProcRec1)
  def "\<Theta>'"=="(\<Theta>\<union>(\<Union>\<sigma>. {(?Pre \<sigma>, Fac_'proc, ?Post \<sigma>,{})}))"
  have Fac_spec: "\<forall>\<sigma>. \<Gamma>,\<Theta>'\<turnstile>(?Pre \<sigma>) ?Fac (?Post \<sigma>)"
    by (unfold \<Theta>'_def, rule allI, rule hoarep.Asm) simp
  txt {* We have to name the fact @{text "Fac_spec"}, so that the vcg can
   use the specification for the recursive call, since it cannot infer it
   from the opaque @{term "\<Theta>'"}. *}
  show "\<forall>\<sigma>. \<Gamma>,\<Theta>'\<turnstile> (?Pre \<sigma>) IF \<acute>N = 0 THEN \<acute>R :== 1
            ELSE \<acute>R :== CALL Fac(\<acute>N - 1);; \<acute>R :== \<acute>N * \<acute>R FI (?Post \<sigma>)"
    apply vcg
    apply simp
    done
qed

text {* There are different rules available to prove procedure calls,
depending on the kind of postcondition and whether or not the
procedure is recursive or even mutually recursive. 
See for example @{thm [source] HoareTotal.ProcRec1}, 
@{thm [source] HoareTotal.ProcNoRec1}. 
They are all derived from the most general rule
@{thm [source] HoareTotal.ProcRec}. 
All of them have some side-conditions concerning the parameter
passing protocol and its relation to the pre and postcondition. They can be
solved in a uniform fashion. Thats why we have created the method 
@{text "hoare_rule"}, which behaves like the method @{text "rule"} but automatically
tries to solve the side-conditions.
*}

subsubsection {* Odd and Even *}

text {* Odd and even are defined mutually recursive here. In the 
@{text "procedures"} command we conjoin both definitions with @{text "and"}.
*}

procedures 
 odd(N::nat | A::nat) "IF \<acute>N=0 THEN \<acute>A:==0
                     ELSE IF \<acute>N=1 THEN CALL even (\<acute>N - 1,\<acute>A)
                          ELSE CALL odd (\<acute>N - 2,\<acute>A)
                          FI
                     FI"
   
and
  even(N::nat | A::nat) "IF \<acute>N=0 THEN \<acute>A:==1
                        ELSE IF \<acute>N=1 THEN CALL odd (\<acute>N - 1,\<acute>A)
                             ELSE CALL even (\<acute>N - 2,\<acute>A)
                             FI
                        FI"
print_theorems
print_locale! odd_even_clique


text {* To prove the procedure calls to @{term "odd"} respectively 
@{term "even"} correct we first derive a rule to justify that we
can assume both specifications to verify the bodies. This rule can
be derived from the general @{thm [source] HoareTotal.ProcRec} rule. An ML function will
do this work:
*}



ML {* ML_Thms.bind_thm ("ProcRec2", Hoare.gen_proc_rec @{context} Hoare.Partial 2) *}


lemma (in odd_even_clique)
  shows odd_spec: "\<forall>\<sigma>. \<Gamma>\<turnstile>{\<sigma>} \<acute>A :== PROC odd(\<acute>N) 
                  \<lbrace>(\<exists>b. \<^bsup>\<sigma>\<^esup>N = 2 * b + \<acute>A) \<and> \<acute>A < 2 \<rbrace>" (is ?P1)
   and even_spec: "\<forall>\<sigma>. \<Gamma>\<turnstile>{\<sigma>} \<acute>A :== PROC even(\<acute>N)
                  \<lbrace>(\<exists>b. \<^bsup>\<sigma>\<^esup>N + 1 = 2 * b + \<acute>A) \<and> \<acute>A < 2 \<rbrace>" (is ?P2)
proof -
  have "?P1 \<and> ?P2"
    apply (hoare_rule ProcRec2)
    apply  vcg
    apply  clarsimp
    apply  (rule_tac x="b + 1" in exI)
    apply  arith
    apply vcg
    apply clarsimp
    apply arith
    done
  thus "?P1" "?P2"
    by iprover+
qed

subsection {*Expressions With Side Effects *}


(* R := N++ + M++*) 
lemma (in state_space) shows "\<Gamma>\<turnstile> \<lbrace>True\<rbrace> 
  \<acute>N \<ggreater> n. \<acute>N :== \<acute>N + 1 \<ggreater>  
  \<acute>M \<ggreater> m. \<acute>M :== \<acute>M + 1 \<ggreater>
  \<acute>R :== n + m
  \<lbrace>\<acute>R = \<acute>N + \<acute>M - 2\<rbrace>"
apply vcg
apply simp
done

(* R := Fac (N) + Fac (N) *)
lemma (in Fac_impl) shows 
  "\<Gamma>\<turnstile> \<lbrace>True\<rbrace> 
  CALL Fac(\<acute>N) \<ggreater> n. CALL Fac(\<acute>N) \<ggreater> m. 
  \<acute>R :== n + m
  \<lbrace>\<acute>R = fac \<acute>N + fac \<acute>N\<rbrace>"
proof -
  note Fac_spec = Fac_spec4
  show ?thesis
    apply vcg
    done
qed

(* R := Fac (N) + Fac (M) *)
lemma (in Fac_impl) shows 
  "\<Gamma>\<turnstile> \<lbrace>True\<rbrace> 
  CALL Fac(\<acute>N) \<ggreater> n. CALL Fac(n) \<ggreater> m. 
  \<acute>R :== m
  \<lbrace>\<acute>R = fac (fac \<acute>N)\<rbrace>"
proof -
  note Fac_spec = Fac_spec4
  show ?thesis
    apply vcg
    done
qed


subsection {* Global Variables and Heap *}


text {*
Now we will define and verify some procedures on heap-lists. We consider
list structures consisting of two fields, a content element @{term "cont"} and
a reference to the next list element @{term "next"}. We model this by the 
following state space where every field has its own heap.
*}


hoarestate globals_list = 
  "next" :: "ref \<Rightarrow> ref"
  cont :: "ref \<Rightarrow> nat"




text {* Updates to global components inside a procedure will
always be propagated to the caller. This is implicitly done by the
parameter passing syntax translations. The record containing the global variables must begin with the prefix "globals".
*}

text {* We will first define an append function on lists. It takes two 
references as parameters. It appends the list referred to by the first
parameter with the list referred to by the second parameter, and returns
the result right into the first parameter.
*}

procedures (imports globals_list)
  append(p::ref,q::ref|p::ref) 
    "IF \<acute>p=Null THEN \<acute>p :== \<acute>q ELSE \<acute>p \<rightarrow>\<acute>next:== CALL append(\<acute>p\<rightarrow>\<acute>next,\<acute>q) FI"



declare [[hoare_use_call_tr' = false]]
context append_impl
begin 
term "CALL append(\<acute>p,\<acute>q,\<acute>p\<rightarrow>\<acute>next)"
end
declare [[hoare_use_call_tr' = true]]

text {* Below we give two specifications this time..
The first one captures the functional behaviour and focuses on the
entities that are potentially modified by the procedure, the second one
is a pure frame condition.
The list in the modifies clause has to list all global state components that
may be changed by the procedure. Note that we know from the modifies clause
that the @{term cont} parts of the lists will not be changed. Also a small
side note on the syntax. We use ordinary brackets in the postcondition
of the modifies clause, and also the state components do not carry the
acute, because we explicitly note the state @{term t} here. 

The functional specification now introduces two logical variables besides the
state space variable @{term "\<sigma>"}, namely @{term "Ps"} and @{term "Qs"}.
They are universally quantified and range over both the pre and the postcondition, so 
that we are able to properly instantiate the specification
during the proofs. The syntax @{text "\<lbrace>\<sigma>. \<dots>\<rbrace>"} is a shorthand to fix the current 
state: @{text "{s. \<sigma> = s \<dots>}"}.  
*}

lemma (in append_impl) append_spec:
  shows "\<forall>\<sigma> Ps Qs. \<Gamma>\<turnstile> 
            \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {}\<rbrace>
                \<acute>p :== PROC append(\<acute>p,\<acute>q) 
            \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply vcg
  apply fastforce
  done


text {* The modifies clause is equal to a proper record update specification
of the following form. 
*}

lemma (in append_impl) shows "{t. t may_only_modify_globals Z in [next]} 
       = 
       {t. \<exists>next. globals t=update id id next_' (K_statefun next) (globals Z)}"
  apply (unfold mex_def meq_def)
  apply simp
  done

text {* If the verification condition generator works on a procedure call
it checks whether it can find a modifies clause in the context. If one
is present the procedure call is simplified before the Hoare rule 
@{thm [source] HoareTotal.ProcSpec} is applied. Simplification of the procedure call means,
that the ``copy back'' of the global components is simplified. Only those
components that occur in the modifies clause will actually be copied back.
This simplification is justified by the rule @{thm [source] HoareTotal.ProcModifyReturn}. 
So after this simplification all global components that do not appear in
the modifies clause will be treated as local variables. 
*}

text {* You can study the effect of the modifies clause on the following two
examples, where we want to prove that @{term "append"} does not change
the @{term "cont"} part of the heap.
*}
lemma (in append_impl)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>p=Null \<and> \<acute>cont=c\<rbrace> \<acute>p :== CALL append(\<acute>p,Null) \<lbrace>\<acute>cont=c\<rbrace>" 
  apply vcg
  oops

text {* To prove the frame condition, 
we have to tell the verification condition generator to use only the
modifies clauses and not to search for functional specifications by 
the parameter @{text "spec=modifies"} It will also try to solve the 
verification conditions automatically.
*}

lemma (in append_impl) append_modifies: 
  shows
   "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC append(\<acute>p,\<acute>q){t. t may_only_modify_globals \<sigma> in [next]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies) 
  done

lemma (in append_impl)
  shows "\<Gamma>\<turnstile> \<lbrace>\<acute>p=Null \<and> \<acute>cont=c\<rbrace> \<acute>p\<rightarrow>\<acute>next :== CALL append(\<acute>p,Null) \<lbrace>\<acute>cont=c\<rbrace>"
  apply vcg
  apply simp
  done

text {*
Of course we could add the modifies clause to the functional specification as 
well. But separating both has the advantage that we split up the verification
work. We can make use of the modifies clause before we apply the
functional specification in a fully automatic fashion.
*}
 

text {* To verify the body of @{term "append"} we do not need the modifies
clause, since the specification does not talk about @{term "cont"} at all, and
we don't access @{term "cont"} inside the body. This may be different for 
more complex procedures.
*}

text {* 
To prove that a procedure respects the modifies clause, we only need
the modifies clauses of the procedures called in the body. We do not need
the functional specifications. So we can always prove the modifies
clause without functional specifications, but me may need the modifies
clause to prove the functional specifications.
*}



 
subsubsection {*Insertion Sort*}

primrec sorted:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list  \<Rightarrow> bool"
where
"sorted le [] = True" |
"sorted le (x#xs) = ((\<forall>y\<in>set xs. le x y) \<and> sorted le xs)"


 
procedures (imports globals_list)
  insert(r::ref,p::ref | p::ref) 
    "IF \<acute>r=Null THEN SKIP
     ELSE IF \<acute>p=Null THEN \<acute>p :== \<acute>r;; \<acute>p\<rightarrow>\<acute>next :== Null
          ELSE IF \<acute>r\<rightarrow>\<acute>cont \<le> \<acute>p\<rightarrow>\<acute>cont 
               THEN \<acute>r\<rightarrow>\<acute>next :== \<acute>p;; \<acute>p:==\<acute>r
               ELSE \<acute>p\<rightarrow>\<acute>next :== CALL insert(\<acute>r,\<acute>p\<rightarrow>\<acute>next)
               FI
          FI
     FI"


text {*
In the postcondition of the functional specification there is a small but 
important subtlety. Whenever we talk about the @{term "cont"} part we refer to 
the one of the pre-state, even in the conclusion of the implication.
The reason is, that we have separated out, that @{term "cont"} is not modified
by the procedure, to the modifies clause. So whenever we talk about unmodified
parts in the postcondition we have to use the pre-state part, or explicitely
state an equality in the postcondition.
The reason is simple. If the postcondition would talk about @{text "\<acute>cont"}
instead of @{text "\<^bsup>\<sigma>\<^esup>cont"}, we will get a new instance of @{text "cont"} during
verification and the postcondition would only state something about this
new instance. But as the verification condition generator will use the
modifies clause the caller of @{text "insert"} instead will still have the
old @{text "cont"} after the call. Thats the sense of the modifies clause.
So the caller and the specification will simply talk about two different things,
without being able to relate them (unless an explicit equality is added to
the specification). 
*}

lemma (in insert_impl) insert_modifies:
  "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC insert(\<acute>r,\<acute>p){t. t may_only_modify_globals \<sigma> in [next]}"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done


lemma (in insert_impl) insert_spec:
    "\<forall>\<sigma> Ps . \<Gamma>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and> sorted (op \<le>) (map \<acute>cont Ps) \<and> 
                  \<acute>r \<noteq> Null \<and> \<acute>r \<notin> set Ps\<rbrace>  
         \<acute>p :== PROC insert(\<acute>r,\<acute>p) 
   \<lbrace>\<exists>Qs. List \<acute>p \<acute>next Qs \<and> sorted (op \<le>) (map \<^bsup>\<sigma>\<^esup>cont  Qs) \<and>
           set Qs = insert \<^bsup>\<sigma>\<^esup>r (set Ps) \<and>
           (\<forall>x. x \<notin> set Qs \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"

apply (hoare_rule HoarePartial.ProcRec1)
apply vcg
apply (intro conjI impI)
apply    fastforce
apply   fastforce
apply  fastforce
apply (clarsimp) 
apply force
done

procedures (imports globals_list)
  insertSort(p::ref | p::ref) 
  where r::ref q::ref
  in
    "\<acute>r:==Null;;
     WHILE (\<acute>p \<noteq> Null) DO
       \<acute>q :== \<acute>p;;
       \<acute>p :== \<acute>p\<rightarrow>\<acute>next;;
       \<acute>r :== CALL insert(\<acute>q,\<acute>r)
     OD;;
     \<acute>p:==\<acute>r"

print_locale insertSort_impl


lemma (in insertSort_impl) insertSort_modifies: 
  shows
   "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC insertSort(\<acute>p)
              {t. t may_only_modify_globals \<sigma> in [next]}"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done


text {* Insertion sort is not implemented recursively here but with a while
loop. Note that the while loop is not annotated with an invariant in the
procedure definition. The invariant only comes into play during verification.
Therefore we will annotate the body during the proof with the
rule @{thm [source] HoareTotal.annotateI}.
*}


lemma (in insertSort_impl) insertSort_body_spec:
  shows "\<forall>\<sigma> Ps. \<Gamma>,\<Theta>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<rbrace> 
              \<acute>p :== PROC insertSort(\<acute>p)
          \<lbrace>\<exists>Qs. List \<acute>p \<acute>next Qs \<and> sorted (op \<le>) (map \<^bsup>\<sigma>\<^esup>cont Qs) \<and>
           set Qs = set Ps\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)  
  apply (hoare_rule anno= 
         "\<acute>r :== Null;;
         WHILE \<acute>p \<noteq> Null
         INV \<lbrace>\<exists>Qs Rs. List \<acute>p \<acute>next Qs \<and> List \<acute>r \<acute>next Rs \<and> 
                  set Qs \<inter> set Rs = {} \<and>
                  sorted (op \<le>) (map \<acute>cont Rs) \<and> set Qs \<union> set Rs = set Ps \<and>
                  \<acute>cont = \<^bsup>\<sigma>\<^esup>cont \<rbrace>
          DO \<acute>q :== \<acute>p;; \<acute>p :== \<acute>p\<rightarrow>\<acute>next;; \<acute>r :== CALL insert(\<acute>q,\<acute>r) OD;;
          \<acute>p :== \<acute>r" in HoarePartial.annotateI)
  apply vcg
  apply   fastforce
  prefer 2
  apply  fastforce
  apply (clarsimp)
  apply (rule_tac x=ps in exI)
  apply (intro conjI)
  apply    (rule heap_eq_ListI1)
  apply     assumption
  apply    clarsimp
  apply    (subgoal_tac "x\<noteq>p \<and> x \<notin> set Rs")
  apply     auto
  done

subsubsection "Memory Allocation and Deallocation"

text {* The basic idea of memory management is to keep a list of allocated
references in the state space. Allocation of a new reference adds a
new reference to the list deallocation removes a reference. Moreover
we keep a counter "free" for the free memory.
*}

(*
record globals_list_alloc = globals_list +
  alloc_'::"ref list"
  free_'::nat 

record 'g list_vars' = "'g list_vars" +
  i_'::nat
  first_'::ref
*)

hoarestate globals_list_alloc =
  alloc::"ref list"
  free::nat 
  "next"::"ref \<Rightarrow> ref"
  cont::"ref \<Rightarrow> nat"
hoarestate locals_list_alloc =
  i::nat
  first::ref
  p::ref
  q::ref
  r::ref
  root::ref
  tmp::ref 
locale list_alloc = globals_list_alloc + locals_list_alloc

definition "sz = (2::nat)"

lemma (in list_alloc)
 shows  
  "\<Gamma>,\<Theta>\<turnstile> \<lbrace>\<acute>i = 0 \<and> \<acute>first = Null \<and> n*sz \<le> \<acute>free\<rbrace>
       WHILE \<acute>i < n 
       INV \<lbrace>\<exists>Ps. List \<acute>first \<acute>next Ps \<and> length Ps = \<acute>i \<and> \<acute>i \<le> n \<and> 
             set Ps \<subseteq> set \<acute>alloc \<and> (n - \<acute>i)*sz \<le> \<acute>free\<rbrace>
       DO
         \<acute>p :== NEW sz [\<acute>cont:==0,\<acute>next:== Null];;
         \<acute>p\<rightarrow>\<acute>next :== \<acute>first;;
         \<acute>first :== \<acute>p;;
         \<acute>i :== \<acute>i+ 1 
       OD
       \<lbrace>\<exists>Ps. List \<acute>first \<acute>next  Ps \<and> length Ps = n \<and> set Ps \<subseteq> set \<acute>alloc\<rbrace>"
apply (vcg)
apply   simp
apply  clarsimp
apply  (rule conjI)
apply   clarsimp
apply   (rule_tac x="new (set alloc)#Ps" in exI)
apply   clarsimp
apply   (rule conjI)
apply    fastforce
apply   (simp add: sz_def)
apply  (simp add: sz_def)
apply fastforce
done


lemma (in list_alloc)
 shows  
  "\<Gamma>\<turnstile> \<lbrace>\<acute>i = 0 \<and> \<acute>first = Null \<and> n*sz \<le> \<acute>free\<rbrace>
       WHILE \<acute>i < n 
       INV \<lbrace>\<exists>Ps. List \<acute>first \<acute>next Ps \<and> length Ps = \<acute>i \<and> \<acute>i \<le> n \<and> 
             set Ps \<subseteq> set \<acute>alloc \<and> (n - \<acute>i)*sz \<le> \<acute>free\<rbrace>
       DO
         \<acute>p :== NNEW sz [\<acute>cont:==0,\<acute>next:== Null];;
         \<acute>p\<rightarrow>\<acute>next :== \<acute>first;;
         \<acute>first :== \<acute>p;;
         \<acute>i :== \<acute>i+ 1 
       OD
       \<lbrace>\<exists>Ps. List \<acute>first \<acute>next  Ps \<and> length Ps = n \<and> set Ps \<subseteq> set \<acute>alloc\<rbrace>"

apply (vcg)
apply   simp
apply  clarsimp
apply  (rule conjI)
apply   clarsimp
apply   (rule_tac x="new (set alloc)#Ps" in exI)
apply   clarsimp
apply   (rule conjI)
apply    fastforce
apply   (simp add: sz_def)
apply  (simp add: sz_def)
apply fastforce
done

subsection {* Fault Avoiding Semantics *}

text {*
If we want to ensure that no runtime errors occur we can insert guards into
the code. We will not be able to prove any nontrivial Hoare triple 
about code with guards, if we cannot show that the guards will never fail.
A trivial Hoare triple is one with an empty precondtion. 
*}


lemma (in list_alloc) "\<Gamma>,\<Theta>\<turnstile> \<lbrace>True\<rbrace>  \<lbrace>\<acute>p\<noteq>Null\<rbrace>\<longmapsto> \<acute>p\<rightarrow>\<acute>next :== \<acute>p \<lbrace>True\<rbrace>"
apply vcg
oops

lemma (in list_alloc) "\<Gamma>,\<Theta>\<turnstile> {}  \<lbrace>\<acute>p\<noteq>Null\<rbrace>\<longmapsto> \<acute>p\<rightarrow>\<acute>next :== \<acute>p \<lbrace>True\<rbrace>"
apply vcg
done

text {* Let us consider this small program that reverts a list. At
first without guards. 
*}
lemma (in list_alloc)
  shows 
  "\<Gamma>,\<Theta>\<turnstile> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and> 
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;; 
     \<acute>p :== \<acute>p\<rightarrow> \<acute>next;; 
     \<acute>r\<rightarrow>\<acute>next :== \<acute>q;; 
     \<acute>q :== \<acute>r OD
  \<lbrace>List \<acute>q \<acute>next (rev Ps @ Qs) \<and> set Ps\<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>"
apply (vcg)
apply fastforce+
done

text {* If we want to ensure that we do not dereference @{term "Null"} or
access unallocated memory, we have to add some guards.
*}
lemma (in list_alloc)
  shows 
  "\<Gamma>,\<Theta>\<turnstile> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and> 
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;; 
     \<lbrace>\<acute>p\<noteq>Null \<and> \<acute>p\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>p :== \<acute>p\<rightarrow> \<acute>next;; 
     \<lbrace>\<acute>r\<noteq>Null \<and> \<acute>r\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>q;; 
     \<acute>q :== \<acute>r OD
 \<lbrace>List \<acute>q \<acute>next (rev Ps @ Qs) \<and> set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>"
apply (vcg)
apply fastforce+
done


text {* We can also just prove that no faults will occur, by giving the
trivial postcondition.
*}
lemma (in list_alloc) rev_noFault:
  shows 
  "\<Gamma>,\<Theta>\<turnstile> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and> 
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;; 
     \<lbrace>\<acute>p\<noteq>Null \<and> \<acute>p\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>p :== \<acute>p\<rightarrow> \<acute>next;; 
     \<lbrace>\<acute>r\<noteq>Null \<and> \<acute>r\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>q;; 
     \<acute>q :== \<acute>r OD
  UNIV,UNIV"
apply (vcg)
apply fastforce+
done

lemma (in list_alloc) rev_moduloGuards: 
  
  shows 
  "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{True}\<^esub> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and> 
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;; 
     \<lbrace>\<acute>p\<noteq>Null \<and> \<acute>p\<in>set \<acute>alloc\<rbrace>\<surd> \<longmapsto> \<acute>p :== \<acute>p\<rightarrow> \<acute>next;; 
     \<lbrace>\<acute>r\<noteq>Null \<and> \<acute>r\<in>set \<acute>alloc\<rbrace>\<surd> \<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>q;; 
     \<acute>q :== \<acute>r OD
 \<lbrace>List \<acute>q \<acute>next (rev Ps @ Qs) \<and> set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>"
apply vcg
apply fastforce+
done




lemma CombineStrip': 
  assumes deriv: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/F\<^esub> P c' Q,A"
  assumes deriv_strip: "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c'' UNIV,UNIV"
  assumes c'': "c''= mark_guards False (strip_guards (-F) c')"
  assumes c: "c = mark_guards False c'"
  shows "\<Gamma>,\<Theta>\<turnstile>\<^bsub>/{}\<^esub> P c Q,A"
proof -
  from deriv_strip [simplified c'']
  have "\<Gamma>,\<Theta>\<turnstile> P (strip_guards (- F) c') UNIV,UNIV"
    by (rule HoarePartialProps.MarkGuardsD)
  with deriv 
  have "\<Gamma>,\<Theta>\<turnstile> P c' Q,A"
    by (rule HoarePartialProps.CombineStrip)
  hence "\<Gamma>,\<Theta>\<turnstile> P mark_guards False c' Q,A"
    by (rule HoarePartialProps.MarkGuardsI)
  thus ?thesis
    by (simp add: c)
qed


text {* We can then combine the prove that no fault will occur with the
functional prove of the programm without guards to get the full proove by
the rule @{thm HoarePartialProps.CombineStrip}
*}


lemma (in list_alloc)
  shows 
  "\<Gamma>,\<Theta>\<turnstile> \<lbrace>List \<acute>p \<acute>next Ps \<and> List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {} \<and>
       set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>
  WHILE \<acute>p \<noteq> Null
  INV \<lbrace>\<exists>ps qs. List \<acute>p \<acute>next  ps \<and> List \<acute>q \<acute>next qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs \<and> 
               set ps \<subseteq> set \<acute>alloc \<and> set qs \<subseteq> set \<acute>alloc\<rbrace>
  DO \<acute>r :== \<acute>p;; 
     \<lbrace>\<acute>p\<noteq>Null \<and> \<acute>p\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>p :== \<acute>p\<rightarrow> \<acute>next;; 
     \<lbrace>\<acute>r\<noteq>Null \<and> \<acute>r\<in>set \<acute>alloc\<rbrace>\<longmapsto> \<acute>r\<rightarrow>\<acute>next :== \<acute>q;; 
     \<acute>q :== \<acute>r OD
 \<lbrace>List \<acute>q \<acute>next (rev Ps @ Qs) \<and> set Ps \<subseteq> set \<acute>alloc \<and> set Qs \<subseteq> set \<acute>alloc\<rbrace>"

apply (rule CombineStrip' [OF rev_moduloGuards rev_noFault])
apply  simp
apply simp
done


text {* In the previous example the effort to split up the prove did not
really pay off. But when we think of programs with a lot of guards and
complicated specifications it may be better to first focus on a prove without
the messy guards. Maybe it is possible to automate the no fault proofs so
that it suffices to focus on the stripped program. 
*}

context list_alloc
begin
text {*
The purpose of guards is to watch for faults that can occur during 
evaluation of expressions. In the example before we watched for null pointer
dereferencing or memory faults. We can also look for array index bounds or
division by zero. As the condition of a while loop is evaluated in each
iteration we cannot just add a guard before the while loop. Instead we need
a special guard for the condition.
Example: @{term "WHILE  \<lbrace>\<acute>p\<noteq>Null\<rbrace>\<longmapsto> \<acute>p\<rightarrow>\<acute>next\<noteq>Null DO SKIP OD"}
*}
end

subsection {* Cicular Lists *}
definition
  distPath :: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> ref \<Rightarrow> ref list \<Rightarrow> bool" where
  "distPath x next y as = (Path x next y as  \<and>  distinct as)"


lemma neq_dP: "\<lbrakk>p \<noteq> q; Path p h q Ps; distinct Ps\<rbrakk> \<Longrightarrow>
 \<exists>Qs. p\<noteq>Null \<and> Ps = p#Qs \<and> p \<notin> set Qs"
by (cases Ps, auto)

lemma (in list_alloc) circular_list_rev_I:
  "\<Gamma>,\<Theta>\<turnstile> \<lbrace>\<acute>root = r \<and>  distPath \<acute>root \<acute>next \<acute>root (r#Ps)\<rbrace>
   \<acute>p :== \<acute>root;; \<acute>q :== \<acute>root\<rightarrow>\<acute>next;;
  WHILE \<acute>q \<noteq> \<acute>root
  INV \<lbrace>\<exists> ps qs. distPath \<acute>p \<acute>next \<acute>root ps  \<and> distPath \<acute>q \<acute>next \<acute>root qs \<and> 
             \<acute>root = r \<and> r\<noteq>Null \<and> r \<notin> set Ps  \<and> set ps \<inter> set qs = {} \<and> 
             Ps = (rev ps) @ qs \<rbrace>
  DO \<acute>tmp :== \<acute>q;; \<acute>q :== \<acute>q\<rightarrow>\<acute>next;; \<acute>tmp\<rightarrow>\<acute>next :== \<acute>p;; \<acute>p:==\<acute>tmp OD;;
  \<acute>root\<rightarrow>\<acute>next :== \<acute>p
  \<lbrace>\<acute>root = r \<and> distPath \<acute>root \<acute>next \<acute>root (r#rev Ps)\<rbrace>"
apply (simp only:distPath_def)
apply vcg
apply   (rule_tac x="[]" in exI)
apply   fastforce
apply  clarsimp
apply  (drule (2) neq_dP)
apply  (rule_tac x="q # ps" in exI)
apply  clarsimp
apply fastforce
done



lemma path_is_list:"\<And>a next b. \<lbrakk>Path b next a Ps ; a \<notin> set Ps; a\<noteq>Null\<rbrakk> 
\<Longrightarrow> List b (next(a := Null)) (Ps @ [a])"
apply (induct Ps)
apply (auto simp add:fun_upd_apply)
done

text {*
The simple algorithm for acyclic list reversal, with modified
annotations, works for cyclic lists as well.: 
*}

lemma (in list_alloc) circular_list_rev_II:
 "\<Gamma>,\<Theta>\<turnstile>
 \<lbrace>\<acute>p = r \<and> distPath \<acute>p \<acute>next \<acute>p (r#Ps)\<rbrace>
\<acute>q:==Null;;
WHILE \<acute>p \<noteq> Null
INV
 \<lbrace> ((\<acute>q = Null) \<longrightarrow> (\<exists>ps. distPath \<acute>p \<acute>next r ps  \<and>  ps = r#Ps)) \<and>
  ((\<acute>q \<noteq> Null) \<longrightarrow> (\<exists>ps qs. distPath \<acute>q \<acute>next r qs  \<and> List \<acute>p \<acute>next ps  \<and>
                   set ps \<inter> set qs = {} \<and> rev qs @ ps = Ps@[r])) \<and>
  \<not> (\<acute>p = Null \<and> \<acute>q = Null \<and> r = Null )
   \<rbrace>
DO
  \<acute>tmp :== \<acute>p;; \<acute>p :== \<acute>p\<rightarrow>\<acute>next;; \<acute>tmp\<rightarrow>\<acute>next :== \<acute>q;; \<acute>q:==\<acute>tmp
OD
 \<lbrace>\<acute>q = r \<and> distPath \<acute>q \<acute>next \<acute>q (r # rev Ps)\<rbrace>"

apply (simp only:distPath_def)
apply vcg
apply   clarsimp
apply  clarsimp
apply  (case_tac "(q = Null)")
apply   (fastforce intro: path_is_list)
apply  clarify
apply  (rule_tac x="psa" in exI)
apply  (rule_tac x=" p # qs" in exI) 
apply  force
apply fastforce
done

text{* Although the above algorithm is more succinct, its invariant
looks more involved. The reason for the case distinction on @{term q}
is due to the fact that during execution, the pointer variables can
point to either cyclic or acyclic structures.
*}

text {*
When working on lists, its sometimes better to remove
@{thm[source] fun_upd_apply} from the simpset, and instead include @{thm[source] fun_upd_same} and @{thm[source] fun_upd_other} to
the simpset
*}

(*
declare fun_upd_apply[simp del]fun_upd_same[simp] fun_upd_other[simp]
*)


lemma (in state_space) "\<Gamma>\<turnstile> {\<sigma>}
            \<acute>I :== \<acute>M;; 
            ANNO \<tau>. \<lbrace>\<tau>. \<acute>I = \<^bsup>\<sigma>\<^esup>M\<rbrace>
                      \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I 
                    \<lbrace>\<acute>M = \<^bsup>\<tau>\<^esup>N \<and> \<acute>N = \<^bsup>\<tau>\<^esup>I\<rbrace>
            \<lbrace>\<acute>M = \<^bsup>\<sigma>\<^esup>N \<and> \<acute>N = \<^bsup>\<sigma>\<^esup>M\<rbrace>"
apply vcg
apply auto
done

context state_space
begin
term "ANNO (\<tau>,m,k). (\<lbrace>\<tau>. \<acute>M = m\<rbrace>) \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I \<lbrace>\<acute>M = \<^bsup> \<tau>\<^esup>N & \<acute>N = \<^bsup>\<tau>\<^esup>I\<rbrace>,{}"
end

lemma (in state_space) "\<Gamma>\<turnstile> ({\<sigma>} \<inter> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>)
      (ANNO \<tau>. ({\<tau>} \<inter> \<lbrace>\<acute>A=\<^bsup>\<sigma>\<^esup>A \<and> \<acute>I=\<^bsup>\<sigma>\<^esup>I \<and> \<acute>M=0 \<and> \<acute>S=0\<rbrace>)
      WHILE \<acute>M \<noteq> \<acute>A
      INV \<lbrace>\<acute>S = \<acute>M * \<acute>I \<and> \<acute>A=\<^bsup>\<tau>\<^esup>A \<and> \<acute>I=\<^bsup>\<tau>\<^esup>I\<rbrace>
      DO \<acute>S :== \<acute>S + \<acute>I;; \<acute>M :== \<acute>M + 1 OD
      \<lbrace>\<acute>S = \<^bsup>\<tau>\<^esup>A * \<^bsup>\<tau>\<^esup>I\<rbrace>)
      \<lbrace>\<acute>S = \<^bsup>\<sigma>\<^esup>A * \<^bsup>\<sigma>\<^esup>I\<rbrace>"
apply vcg_step
apply vcg_step
apply simp
apply vcg_step
apply vcg_step
apply simp
apply vcg
apply simp
apply simp
apply vcg_step
apply auto
done

text {* Just some test on marked, guards *}
lemma (in state_space) "\<Gamma>\<turnstile>\<lbrace>True\<rbrace> WHILE \<lbrace>P \<acute>N \<rbrace>\<surd>, \<lbrace>Q \<acute>M\<rbrace>#, \<lbrace>R \<acute>N\<rbrace>\<longmapsto> \<acute>N < \<acute>M 
                    INV \<lbrace>\<acute>N < 2\<rbrace> DO
                    \<acute>N :== \<acute>M
                  OD 
           \<lbrace>hard\<rbrace>"
apply vcg
oops

lemma (in state_space) "\<Gamma>\<turnstile>\<^bsub>/{True}\<^esub> \<lbrace>True\<rbrace> WHILE \<lbrace>P \<acute>N \<rbrace>\<surd>, \<lbrace>Q \<acute>M\<rbrace>#, \<lbrace>R \<acute>N\<rbrace>\<longmapsto> \<acute>N < \<acute>M 
                    INV \<lbrace>\<acute>N < 2\<rbrace> DO
                    \<acute>N :== \<acute>M
                  OD 
           \<lbrace>hard\<rbrace>"
apply vcg
oops

end 