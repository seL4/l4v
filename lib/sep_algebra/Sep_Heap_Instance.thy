(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Gerwin Klein, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

chapter "Standard Heaps as an Instance of Separation Algebra"

theory Sep_Heap_Instance
imports Separation_Algebra
begin

text \<open>
  Example instantiation of a the separation algebra to a map, i.e.\ a
  function from any type to @{typ "'a option"}.
\<close>

class opt =
  fixes none :: 'a
begin
  definition "domain f \<equiv> {x. f x \<noteq> none}"
end

instantiation option :: (type) opt
begin
  definition none_def [simp]: "none \<equiv> None"
  instance ..
end

instantiation "fun" :: (type, opt) zero
begin
  definition zero_fun_def: "0 \<equiv> \<lambda>s. none"
  instance ..
end

instantiation "fun" :: (type, opt) sep_algebra
begin

definition
  plus_fun_def: "m1 + m2 \<equiv> \<lambda>x. if m2 x = none then m1 x else m2 x"

definition
  sep_disj_fun_def: "sep_disj m1 m2 \<equiv> domain m1 \<inter> domain m2 = {}"

instance
  apply intro_classes
        apply (simp add: sep_disj_fun_def domain_def zero_fun_def)
       apply (fastforce simp: sep_disj_fun_def)
      apply (simp add: plus_fun_def zero_fun_def)
     apply (simp add: plus_fun_def sep_disj_fun_def domain_def)
     apply (rule ext)
     apply fastforce
    apply (rule ext)
    apply (simp add: plus_fun_def)
   apply (simp add: sep_disj_fun_def domain_def plus_fun_def)
   apply fastforce
  apply (simp add: sep_disj_fun_def domain_def plus_fun_def)
  apply fastforce
  done

end

text \<open>
  For the actual option type @{const domain} and @{text "+"} are
  just @{const dom} and @{text "++"}:
\<close>

lemma domain_conv: "domain = dom"
  by (rule ext) (simp add: domain_def dom_def)

lemma plus_fun_conv: "a + b = a ++ b"
  by (auto simp: plus_fun_def map_add_def split: option.splits)

lemmas map_convs = domain_conv plus_fun_conv

text \<open>
  Any map can now act as a separation heap without further work:
\<close>
lemma
  fixes h :: "(nat => nat) => 'foo option"
  shows "(P ** Q ** H) h = (Q ** H ** P) h"
  by (simp add: sep_conj_ac)

section \<open>@{typ unit} Instantiation\<close>

text \<open>
  The @{typ unit} type also forms a separation algebra. Although
  typically not useful as a state space by itself, it may be
  a type parameter to more complex state space.
\<close>

instantiation "unit" :: stronger_sep_algebra
begin
  definition "plus_unit (a :: unit) (b :: unit) \<equiv> ()"
  definition "sep_disj_unit  (a :: unit) (b :: unit) \<equiv> True"
  instance
    apply intro_classes
    apply (simp add: plus_unit_def sep_disj_unit_def)+
    done
end

lemma unit_disj_sep_unit [simp]: "(a :: unit) ## b"
  by (clarsimp simp: sep_disj_unit_def)

lemma unit_plus_unit [simp]: "(a :: unit) + b = ()"
  by (rule unit_eq)

section \<open>@{typ "'a option"} Instantiation\<close>

text \<open>
  The @{typ "'a option"} is a seperation algebra, with @{term None}
  indicating emptyness.
\<close>

instantiation option :: (type) stronger_sep_algebra
begin
  definition
    "zero_option \<equiv> None"
  definition
    "plus_option (a :: 'a option) (b :: 'a option) \<equiv> (case b of None \<Rightarrow> a | Some x \<Rightarrow> b)"
  definition
    "sep_disj_option  (a :: 'a option) (b :: 'a option) \<equiv> a = None \<or> b = None"

  instance
    by intro_classes
       (auto simp: zero_option_def sep_disj_option_def plus_option_def split: option.splits)
end

lemma disj_sep_None [simp]:
  "a ## None"
  "None ## a"
  by (auto simp: sep_disj_option_def)

lemma disj_sep_Some_Some [simp]:
  "\<not> (Some a ## Some b)"
  by (auto simp: sep_disj_option_def)

lemma None_plus [simp]:
  "a + None = a"
  "None + a = a"
  by (auto simp: plus_option_def split: option.splits)

lemma None_plus_distrib:
  "(a :: 'a option) + (b + c) = (a + b) + c"
  by (clarsimp simp: plus_option_def split: option.splits)

end
