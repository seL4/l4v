(*
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
*)

chapter \<open>An Isabelle Syntax Style Guide\<close>

theory Style
  imports
    Main
    Style_pre
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

section \<open>Referenecs\<close>

text \<open>
[1] https://proofcraft.org/blog/isabelle-style.html
[2] https://proofcraft.org/blog/isabelle-style-part2.html \<close>

end
