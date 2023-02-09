(*
     Copyright 2022, Proofcraft Pty Ltd
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
*)

chapter \<open>An Isabelle Syntax Style Guide\<close>

theory Style
  imports
    Style_pre
    Lib.SplitRule
begin

text \<open>
  This page describes the Isabelle syntax style conventions that we follow. For more on semantic
  style see Gerwin's style guides [1] and [2].\<close>

section \<open>General Principles\<close>

text \<open>
  Goals:
    * Readability and consistency:
      reduce cognitive overhead.

    * Make good use of horizontal space:
      most screens are wide, not high

    * Semantic indentation:
      where possible group things according to meaning. But remain syntactically consistent:
      a sub-term should not go more left than its parent term.

    * Support tools like diff and grep:
      diff tries to find the "function" each chunk belongs to by indentation. If we remain
      compatible, diffs are much easier to read. Pull requests mean we read a lot of diffs.
      grep and other regexp search is not needed as much as it used to, but it's still often
      useful to be able to find constants and lemmas by regexp search outside of Isabelle

    * Don't fight existing auto-indent where possible:
      there can be exceptions, but each time we go against defaults, it will be annoying to follow.

    * Compatibility with upstream style where it exists:
      there is not much consistent Isabelle distribution style, but where there is, we should follow
      it, so that others can read our code and we can contribute upstream\<close>

text \<open>
  The main rules:
    * Indent your proofs.

    * Follow naming conventions.

    * Be aware that others have to read what you write.\<close>

text \<open>
  To not drive proof maintainers insane:

    * Do not use `auto` except at the end of a proof, see [1].

    * Never check in proofs containing `back`.

    * Instantiate bound variables in preference to leaving schematics in a subgoal
      (i.e. use erule_tac ... allE in preference to erule allE)

    * Explicitly name variables that the proof text refers to (e.g. with rename_tac)

    * Don't mix object and meta logic in a lemma statement.\<close>

section \<open>Text and comments\<close>

text \<open>
  Generally, prefer @{command text} comments over (* source comments *), because the former
  will be displayed in LaTeX and HTML output. Be aware of LaTeX pitfalls and use antiquotations
  such as @{text some_id} or @{term "1+1"} for identifiers and terms, especially when they
  contain underscores and other sequences that already have meaning in LaTeX.

  For comments inside inner-syntax terms use the \<comment> \<open>comment symbol\<close> and to comment out parts
  of a term the \<^cancel>\<open>cancel symbol\<close>.

  For comments in apply proofs use either the \<comment> \<open>comment symbol\<close> or source (* comments *).
  Source comments are fine here because we don't expect apply proofs to be read in PDF.\<close>

text \<open>This is a comment that fits in one line. It is on the same line as @{command text}.\<close>

text \<open>
  Once you have to break the line, keep @{command text} and the opening bracket on its own line, and
  the closing bracket on the same line as the ending text to not waste too much vertical space.
  Indent text by 2 inside the @{command text} area. This achieves visual separation.\<close>

section \<open>Indentation\<close>

text \<open>
  Isabelle code is much easier to maintain when indented consistently. In apply style proofs we
  indent by 2 spaces, and add an additional space for every additional subgoal.

  In the following example, the rules iffI and conjI add a new subgoal, and fast removes a subgoal.
  The idea is that, when something breaks, the indentation tells you whether a tactic used to solve
  a subgoal or produced new ones.\<close>

lemma disj_conj_distribR:
  "(A \<and> B \<or> C) = ((A \<or> C) \<and> (B \<or> C))"
  apply (rule iffI)
   apply (rule conjI)
    apply fast
   apply fast
  apply auto
  done

text \<open>The statement of Hoare triple lemmas are generally indented in the following way.\<close>

lemma my_hoare_triple_lemma:
  "\<lbrace>precondition_one and precondition_two and
    precondition three\<rbrace>
   my_function param_a param_b
   \<lbrace>post_condition\<rbrace>"
  oops

text \<open> or \<close>

lemma my_hoare_triple_lemma:
  "\<lbrace>precondition_one and precondition_two
    and precondition three\<rbrace>
   my_function param_a param_b
   \<lbrace>post_condition\<rbrace>"
  oops

text \<open>
  Definitions, record and datatypes are generally indented as follows and generally use @{text \<open>\<equiv>\<close>}
  rather than @{text \<open>=\<close>}. Short datatypes can be on a single line.

  Note: Upstream Isabelle tends to use @{text \<open>=\<close>} rather than @{text \<open>\<equiv>\<close>}. So we don't enforce a
  strict rule in this case.\<close>

definition word_bits :: nat where
  "word_bits \<equiv> 32"

definition long_defn_type ::
  "'this => 'is => 'a => 'long => 'type => 'that => 'does =>
   'not => 'fit => 'in => 'one => 'line"
  where
  "long_defn_type \<equiv> undefined"

fun foo_fun :: "nat \<Rightarrow> nat" where
    "foo_fun 0 = 0"
  | "foo_fun (Suc n) = n"

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
  There are tools to automatically indent proofs in jEdit. In terms of rules:

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
  \<close>}\<close>

text \<open>
  If a definition body causes an overflow of the 100 char line limit, use one
  of the following two patterns.\<close>

definition hd_opt :: "'a list \<Rightarrow> 'a option" where
  "hd_opt \<equiv> case_list
              None
              (\<lambda>h t. Some h)"

definition hd_opt4 :: "'a list \<Rightarrow> 'a option" where
  "hd_opt4 \<equiv>
     case_list None (\<lambda>h t. Some h)"

text \<open>
  If an apply line causes an overflow of the 100 char line limit, use one
  of the following two patterns: aligning on ":" or aligning on left.\<close>

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
  apply ((cases l; simp add: hd_opt_def),
         rename_tac h t,
         case_tac h; simp)
  done

section \<open>Other\<close>

text \<open>
  General layout:
    * Wrap at 100, avoid overly long lines, not everyone has a big screen
    * No tabs, use spaces instead, standard indentation is 2
    * Avoid starting lines with quotes ("), it breaks some automated tools.
    * Avoid unnecessary parentheses, unless it becomes really unclear what is going on. Roughly,
      parentheses are unnecessary if Isabelle doesn't show them in output.

  Other:
    * Avoid commands that produce "legacy" warnings. Add an issue with tag cleanup if you see them
      after an Isabelle update.\<close>

section \<open>Comments\<close>

text \<open>
  (* .. *) style comments are not printed in latex. Use them if you don't think anyone will want to
  see this printed. Otherwise, prefer text \<open> .. \<close>

  In stark difference to the Isabelle distribution, we do comment stuff. If you have defined or done
  anything that is tricky, required you to think deeply, or similar, save everyone else the
  duplicated work and document why things are the way you've written them.

  We've been slack on commenting in the past. We should do more of it rather than less.
  There's no need to comment every single thing, though. Use your judgement. Prefer readable
  code/proofs/definitions over commented ones. Comment on why the proof is doing something,
  not what it is doing.\<close>


section \<open>Fun, primrec, or case? case!\<close>

text \<open>
  When defining a non-recursive function that uses pattern matching, there are multiple options:
  @{command fun}, @{command primrec}, and @{text case}. @{text case} initially seems like the least
  powerful of these, but combined with the @{attribute split_simps} attribute, it is the option that
  provides the highest degree of proof automation. @{command fun} and @{command primrec} provide
  a simp rule for each of the pattern cases, but when a closed term appears in the proof, there is
  no way to automatically perform a case distinction -- you need to do a manual @{method cases} or
  @{method case_tac} invocation. @{text case} does provide automatic splitting via split rules, and
  @{attribute split_simps} adds the missing simp rules.

  So the recommended pattern is to use @{text case} in the definition and supply the simp rules
  directly after it, adding them to the global simp set as @{command fun}/@{command primrec} would
  do. The split rule you need to provide to @{attribute split_simps} is the split rule for the type
  over which the pattern is matched. For nested patterns, multiple split rules can be provided. See
  also the example in @{theory Lib.SplitRule}.\<close>

definition some_f :: "nat \<Rightarrow> nat" where
  "some_f x \<equiv> case x of 0 \<Rightarrow> 1 | Suc n \<Rightarrow> n+2"

lemmas some_f_simps[simp] = some_f_def[split_simps nat.split]

(* Pattern is simplified automatically: *)
lemma "some_f 0 = 1"
  by simp

(* But automated case split is still available after unfolding: *)
lemma "some_f x > 0"
  unfolding some_f_def by (simp split: nat.split)


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
  prefers (or defers) will be needed, e.g. corres proofs.\<close>

subsection \<open>Using by\<close>

text \<open>
  When all subgoals of a proof can be solved in one apply statement, use `by`.\<close>

lemma
  "True"
  by simp

lemma
  "X"
  apply (subgoal_tac "True")
   prefer 2
   subgoal by blast
  apply (subgoal_tac "True")
   prefer 2
   subgoal
     by blast \<comment> \<open>for tactic invocations that would overflow the line\<close>
  oops

text \<open>
  When all subgoals of a proof can be solved in two apply statements, use `by` to indicate the
  intermediate state is not interesting.\<close>

lemma
  "True \<and> True"
  by (rule conjI) auto

lemma
  "True \<and> True"
  by (rule conjI)
     auto \<comment> \<open>for tactic invocations that would overflow the line\<close>

text \<open>
  Avoid using `by` at the end of an apply-style proof with multiple steps.
  The exception to this rule are long-running statements (over 2 seconds) that complete the proof.
  There, we favour parallelism (proof forking in interactive mode) over visual consistency.

  If you do use `by` starting on a line of its own, it should be indented as if it were an
  apply statement.
  NOTE: the default Isabelle auto-indenter will not indent `by` according to the number of goals,
        which is another reason to avoid mixing it with apply style\<close>

lemma
  "True \<and> True \<and> True \<and> True \<and> True \<and> True \<and> True"
  apply (intro conjI)
        apply blast
       apply blast
      apply auto
  done \<comment> \<open>use this style in general: no by\<close>

lemma long_running_ending:
  "True \<and> True \<and> True \<and> True \<and> True \<and> True \<and> True"
  apply (intro conjI)
        apply blast
       apply blast
      by auto \<comment> \<open>only if long-running, and note indentation!\<close>

subsection \<open>Unfolding definitions\<close>

text \<open>
  When unfolding definitions at the start of a proof, use `unfolding` instead of the simplifier.
  This is not a hard rule but is strongly preferred, since the unfolding step is then stable and it
  makes it obvious that nothing interesting is supposed to be happening. For example, use\<close>

lemma my_hoare_triple_lemma:
  "\<lbrace>precondition_one and precondition_two and
    precondition three\<rbrace>
   my_function param_a param_b
   \<lbrace>post_condition\<rbrace>"
  unfolding my_function_def
  oops

text \<open>instead of\<close>

lemma my_hoare_triple_lemma:
  "\<lbrace>precondition_one and precondition_two and
    precondition three\<rbrace>
   my_function param_a param_b
   \<lbrace>post_condition\<rbrace>"
  apply (clarsimp simp: my_function_def)
  oops

subsection \<open>ccorres statements\<close>

text \<open>
  We prefer the following formatting for ccorres statements. Recall that a ccorres statement has
  the form\<close>

lemma ccorres_example:
  "ccorres rrel xf P Q hs a c"
  oops

text \<open>
  where rrel is the return relation, xf is the extraction function, P is the abstract guard,
  Q is the concrete guard, hs is the handler stack, a is the abstract function, and c is the
  concrete function.

  If the statement can fit on a single line within the character limit, then this is best.
  If not, wherever possible
    - rrel and xf should occur on the same line,
    - P, Q, and hs should occur on the same line, and
    - a and c should occur on the same line

  Often the guards will require more than one line, and in this case, hs should occur on the same
  line as the concrete guard wherever possible.

  If the statement must use more than one line, all lines after the first should be indented by
  2 spaces from @{term ccorres}.

  Here are some examples.\<close>

lemma short_ccorres_example:
  "ccorres rrel xf short_abs_guard short_conc_guard hs short_abs_fn short_conc_fn"
  oops

lemma long_ccorres_example:
  "ccorres rrel xf
     long_abs_guard long_conc_guard hs
     long_abs_fn long_conc_fn"
  oops

lemma longer_ccorres_example:
  "ccorres
     long_rrel
     long_xf
     long_abs_guard
     long_conc_guard hs
     long_abs_fn
     long_conc_fn"
  oops

text \<open>
  The concrete guard will often be simply @{term UNIV}, or an intersection of terms of the form
  @{term "\<lbrace>\<acute>pointer = cond\<rbrace>"}, which supersedes the set-builder notation wherever applicable.
  Note that the semantically redundant form @{term "UNIV \<inter> \<lbrace>\<acute>pointer = cond\<rbrace>"} should no longer
  be necessary, and should be avoided wherever possible.\<close>

section \<open>Referenecs\<close>

text \<open>
[1] https://proofcraft.org/blog/isabelle-style.html
[2] https://proofcraft.org/blog/isabelle-style-part2.html \<close>

end
