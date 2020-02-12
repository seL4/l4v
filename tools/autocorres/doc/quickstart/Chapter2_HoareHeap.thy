(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*<*)
theory Chapter2_HoareHeap
imports "AutoCorres.AutoCorres"
begin

external_file "mult_by_add.c"
(*>*)

section  \<open>More Complex Functions with AutoCorres\<close>

text \<open>

  In the previous section we saw how to use the C-Parser and AutoCorres
  to prove properties about some very simple C programs.

  Real life C programs tend to be far more complex however; they
  read and write to local variables, have loops and use pointers to
  access the heap. In this section we will look at some simple programs
  which use loops and access the heap to show how AutoCorres can
  allow such constructs to be reasoned about.

\<close>

subsection \<open>A simple loop: \texttt{mult\_by\_add}\<close>

text \<open>

  Our C function \texttt{mult\_by\_add} implements a multiply operation
  by successive additions:

\lstinputlisting[language=C, firstline=15]{../../mult_by_add.c}

  We start by translating the program using the C parser and AutoCorres,
  and entering the generated locale \texttt{mult\_by\_add}.
\<close>

install_C_file "mult_by_add.c"
autocorres [ts_rules = nondet] "mult_by_add.c"
(*<*)
context mult_by_add begin
(*>*)

text \<open>
  The C parser produces the SIMPL output as follows:
\<close>

thm mult_by_add_body_def
text \<open>@{thm [display] mult_by_add_body_def}\<close>

text \<open>
  Which is abstracted by AutoCorres to the following:
\<close>

thm mult_by_add'_def
text \<open>@{thm [display] mult_by_add'_def }\<close>

text \<open>

  In this case AutoCorres has abstracted \texttt{mult\_by\_add} into a
  \emph{monadic} form. Monads are a pattern frequently used in
  functional programming to represent imperative-style control-flow; an
  in-depth introduction to monads can be found elsewhere.

  The monads used by AutoCorres in this example is a
  \emph{non-deterministic state monad}; program state is implicitly
  passed between each statement, and results of computations may produce
  more than one (or possibly zero) results\footnote{Non-determinism
  becomes useful when modelling hardware, for example, where the exact
  results of the hardware cannot be determined ahead of time.}.
\<close>
  (* FIXME : probably describe below in further detail. *)
text \<open>
  The bulk of @{term "mult_by_add'"} is wrapped inside the @{term
  "whileLoop"} \emph{monad combinator}, which is really just a fancy way
  of describing the method used by AutoCorres to encode (potentially
  non-terminating) loops using monads.

  If we want to describe the behaviour of this program, we can use
  Hoare logic as follows:

    @{term [display] "\<lbrace> P \<rbrace> mult_by_add' a b \<lbrace> Q \<rbrace>"}

  This predicate states that, assuming @{term "P"} holds on the initial
  program state, if we execute @{term "mult_by_add' a b"}, then
  @{term "Q"} will hold on the final state of the program.

  There are a few details: while @{term "P"} has type
  @{typ "'s \<Rightarrow> bool"} (i.e., takes a state and returns true if
  it satisifies the precondition), @{term "Q"} has an additional
  parameter @{typ "'r \<Rightarrow> 's \<Rightarrow> bool"}. The additional parameter
  @{typ "'r"} is the \emph{return value} of the function; so, in
  our \texttt{mult\_by\_add'} example, it will be the result of
  the multiplication.

  For example one useful property to prove on our program would
  be:

    @{term [display] "\<lbrace> \<lambda>s. True \<rbrace> mult_by_add' a b \<lbrace> \<lambda>r s. r = a * b \<rbrace>"}

  That is, for all possible input states, our \texttt{mult\_by\_add'}
  function returns the product of @{term "a"} and @{term "b"}.

  Unfortunately, this is not sufficient. As mentioned in the previous
  section, AutoCorres produces a theorem for each function it abstracts
  stating that, \emph{assuming the function does not fail}, then the
  generated function is a valid abstraction of the concrete function.
  Thus, if we wish to reason about our concrete C function, we must
  also show non-failure on the abstract program. This can be done
  using the predicate @{term "no_fail"} as follows:

    @{term [display] "\<And>a b. no_fail (\<lambda>s. True) (mult_by_add' a b)"}

  Here @{term "\<lambda>s. True"} is the precondition on the input state.

  Instead of proving our Hoare triple and @{term no_fail} separately,
  we can prove them together using the ``valid no fail'' framework
  as follows:

    @{thm [display] validNF_def}

  Our proof of @{term mult_by_add'} could then proceed as follows:

\<close>

lemma mult_by_add_correct:
    "\<lbrace> \<lambda>s. True \<rbrace> mult_by_add' a b \<lbrace> \<lambda>r s. r = a * b \<rbrace>!"
  txt \<open>Unfold abstracted definition\<close>
  apply (unfold mult_by_add'_def)
  txt \<open>Annotate the loop with an invariant and a measure.\<close>
  apply (subst whileLoop_add_inv
    [where I="\<lambda>(a', result) s. result = (a - a') * b"
        and M="\<lambda>((a', result), s). a'"] )
  txt \<open>Run the ``weakest precondition'' tool \texttt{wp}.\<close>
  apply wp
  txt \<open>Solve the program correctness goals.\<close>
     apply (simp add: field_simps)
    apply unat_arith
   apply (auto simp: field_simps not_less)
  done

(* FIXME: Update the following explanation. *)
text \<open>
  The proof is straight-forward, but uses a few different techniques:
  The first is that we annotate the loop with a loop invariant and a
  measure, using the rule @{thm whileLoop_add_inv}. We then run the
  \texttt{wp} tool which applys a large set of
  \emph{weakest precondition} rules on the program\footnote{This set of
  rules includes a rule which can handle annotated @{term whileLoop}
  terms, but will not attempt to process @{term whileLoop} terms without
  annotations.}. We finially discharge the remaining subgoals left from
  the \texttt{wp} tool using \texttt{auto}, and our proof is complete.

  In the next section, we will look at how we can use AutoCorres to
  verify a C program that reads and writes to the heap.

\<close>

(*<*)
end
end
(*>*)
