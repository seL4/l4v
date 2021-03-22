(*
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
*)

chapter \<open>An Isabelle Syntax Style Guide\<close>

theory Style
  imports Main
begin

typedecl type_foo
typedecl type_bar

definition valid ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> undefined"

definition
  pred_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "and" 35)
where
  "pred_conj P Q \<equiv> \<lambda>x. P x \<and> Q x"

text \<open>
This page describes the Isabelle syntax style conventions that we follow. For more on semantic
style see Gerwin's style guide (parts 1 and 2).

  * https://proofcraft.org/blog/isabelle-style.html
  * https://proofcraft.org/blog/isabelle-style-part2.html

Our Isabelle style is pretty much the same as in the Isabelle distribution. Look at files in 
l4.verified/isabelle/src/HOL to get a feel for it.
\<close>

section \<open>General Principles\<close>

text \<open>
The main rules:
  * Indent your proofs.
  * Follow naming conventions.
  * Be aware that others have to read what you write.

To not drive proof maintainers insane:
  * Do not use auto except at the end of a proof.
  * Never check in proofs containing back.
  * Instantiate bound variables in preference to leaving schematics in a subgoal 
    (i.e. use erule_tac ... allE in preference to erule allE)
  * Don't mix object and meta logic in a lemma statement.
\<close>

section \<open>Indentation\<close>

text \<open>
Isabelle code is much easier to maintain when indented consistently. In apply style proofs we
indent by 2 spaces, and add an additional space for every additional subgoal. For example, the 
rules iffI and conjI add a new subgoal, and fast removes a subgoal. The idea is that, when 
something breaks, the indentation tells you whether a tactic used to solve a subgoal or produced 
new ones.
\<close>

lemma disj_conj_distribR:
  "(A \<and> B \<or> C) = ((A \<or> C) \<and> (B \<or> C))"
  apply (rule iffI)
   apply (rule conjI)
    apply fast
   apply fast
  apply auto
  done

text \<open>
The statement of Hoare triple lemmas are generally indented in the following way.
\<close>

lemma my_hoare_triple_lemma:
  "\<lbrace> precondition_one and precondition_two and
     precondition three \<rbrace>
   my_function param_a param_b
   \<lbrace> post_condition \<rbrace>"
  oops

text \<open> or \<close>

lemma my_hoare_triple_lemma:
  "\<lbrace> precondition_one and precondition_two
     and precondition three \<rbrace>
   my_function param_a param_b
   \<lbrace> post_condition \<rbrace>"
  oops

text \<open>
Definitions, record and datatypes are generally indented as follows and use \<equiv> rather than =. Short 
datatypes can be on a single line.
\<close>

definition word_bits :: nat where
  "word_bits \<equiv> 32"

definition long_defn_type ::
  "'this => 'is => 'a => 'long => 'type => 'that => 'does =>
   'not => 'fit => 'in => 'one => 'line"
  where
  "long_defn_type \<equiv> undefined"

fun foo_fun :: "nat \<Rightarrow> nat" where
  "foo_fun 0 = 0" |
  "foo_fun (Suc n) = n"

record cdl_cnode =
  cdl_cnode_caps :: type_foo
  cdl_cnode_size_bits :: type_bar

datatype cdl_object =
    Endpoint
  | Tcb type_foo
  | CNode cdl_cnode
  | Untyped
 
datatype cdl_arch = IA32 | ARM11

text \<open>
There are tools to automatically indent proofs in both jEdit and Emacs. In terms of rules:
  * definition and fun should be on the same line as the name.
  * Everything after the first line of a definition or fun statement should be indented.
  * Type definitions (record, type_synonym, datatype) have the defined type on the same line, the
    rest only if it fits.
  * Avoid long hanging indentation in data types, case expressions, etc. That is:

Wrong:

@{term\<open>
case xs_blah of [] \<Rightarrow> foo
              | y#ys \<Rightarrow> baz
\<close>}

Right:

@{term\<open>
case xs_blah of
    [] \<Rightarrow> foo
  | y#ys \<Rightarrow> baz
\<close>}
\<close>

text \<open> 
  If a definition body causes an overflow of the 100 char line limit, use one
  of the following two patterns.
\<close>

definition hd_opt :: "'a list \<Rightarrow> 'a option" where
  "hd_opt \<equiv> case_list
            None
            (\<lambda>h t. Some h)"

definition hd_opt4 :: "'a list \<Rightarrow> 'a option" where
  "hd_opt4 \<equiv>
   case_list None (\<lambda>h t. Some h)"

text \<open>
  If an apply line causes an overflow of the 100 char line limit, use one
  of the following two patterns: aligning on ":" or aligning on left.
\<close>

lemma test_lemma0:
  "\<lbrakk>hd_opt l \<noteq> None; hd_opt (hd l) = Some x\<rbrakk> \<Longrightarrow>
    hd_opt (concat l) = Some x"
  apply (clarsimp simp: hd_opt_def
                 split: list.splits)
  done

lemma test_lemma1:
  "\<lbrakk>hd_opt l \<noteq> None; hd_opt (hd l) = Some x\<rbrakk> \<Longrightarrow>
    hd_opt (concat l) = Some x"
  apply (clarsimp simp: hd_opt_def
                  split: list.splits)
  done

lemma test_lemma3:
  "case_option None hd_opt (hd_opt l) = Some x \<Longrightarrow>
   hd_opt (concat l) = Some x"
  apply ((case_tac l; simp add: hd_opt_def),
         rename_tac h t,
         case_tac h; simp)
  done

section \<open>Other\<close>

text \<open>
General layout:
* Wrap at 100 (if possible), avoid overly long lines, not everyone has a big screen
* No hard tabs, use spaces instead, standard indentation is 2
* Avoid starting lines with quotes ("), it breaks some automated tools.
* Avoid unnecessary parentheses, unless it becomes really unclear what is going on. Roughly, 
  parentheses are unnecessary if Isabelle doesn't show them in output.

Other:
* Avoid commands that produce "legacy" warnings. Add a JIRA issue with tag cleanup if you see them 
  after an Isabelle update.
\<close>

section \<open>Comments\<close>

text \<open>
(* .. *) style comments are not printed in latex. Use them if you don't think anyone will want to 
see this printed. Otherwise, prefer text {* .. *}

In stark difference to the Isabelle distribution, we do comment stuff. If you have defined or done 
anything that is tricky, required you to think deeply, or similar, save everyone else the duplicated 
work and document why things are the way you've written them.

We've been slack on commenting in the past. We should do more of it rather than less.
There's no need to comment every single thing, though. Use your judgement. Prefer readable 
code/proofs/definitions over commented ones.\<close>


section \<open>More on proofs\<close>

subsection \<open>prefer and defer\<close>

text \<open> 
   There are currently no hard rules on the use of `prefer` and `defer n`. Two general principles
   apply:

   1. If they are used too frequently then a proof may become unreadable. Do not use them
      unnecessarily and consider including comments to indicate their purpose.
   2. If they are used too "specifically" then a proof may break very frequently for not-
      interesting reasons. This makes a proof less maintainable and so this should be avoided.
  
  A known use case for `prefer` is where a proof has a tree-like structure, and the prover wants to
  approach it with a breadth-first approach. Since the default isabelle strategy is depth-first,
  prefers (or defers) will be needed, e.g. corres proofs.
\<close>

end
