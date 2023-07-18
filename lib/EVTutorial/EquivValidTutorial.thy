(*
 * Copyright 2020, The University of Melbourne (ABN 84 002 705 224)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Developers of future substantial additions to this tutorial may wish to
 * append their names to the author list in its document root.tex file.
 *)

theory EquivValidTutorial
imports Lib.EquivValid
begin

text \<open>
This tutorial provides a basic introduction to the seL4 verification repository's
EquivValid library, which formalises proof machinery first
introduced by the CPP'12 paper:
  ``Noninterference for Operating System Kernels''
  by Murray, Matichuk, Brassil, Gammie, and Klein \cite{Murray_MBGK_12}.
This mostly comes in the form of worked examples.

EquivValid statements are used to phrase seL4's information-flow security lemmas,
because they can be used to assert that a function preserves (or establishes)
``observable equivalence'' of system state, as seen by some attacker model.
The ``Valid'' part of EquivValid is based on the fact that the Isabelle definition
for Hoare triples in the seL4 proof base is called \<open>valid\<close>. The EquivValid statements
\<open>equiv_valid\<close>, \<open>equiv_valid_2\<close> are therefore the ``equivalence'' versions of \<open>valid\<close>.
In \cite{Murray_MBGK_12},
EquivValid statements are referred to as ``ev'' or ``ev2'' statements.
These roughly (but not exactly) correspond to \<open>equiv_valid\<close> and \<open>equiv_valid_2\<close>
(resp.) in the Isabelle theories.

This tutorial will assume that the reader knows how to use the weakest precondition tool,
``wp'', to discharge Hoare triples. More information on this is available in the
Lib.WPTutorial theory in the seL4 verification repo.
\<close>


section \<open> Preliminaries \<close>

text \<open> It will be best to think of an EquivValid statement as akin to a Hoare triple.
Recall that a Hoare triple consists of a precondition, function, and postcondition.
This following basic example of a Hoare triple asserts that, for any \<^emph>\<open>single\<close> run
of the function \<open>f\<close>, assuming the precondition \<open>P\<close> holds prior to that run,
the postcondition \<open>Q\<close> will hold afterwards. \<close>

term "\<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
thm valid_def

text \<open> Similarly to a Hoare triple, an EquivValid statement makes an assertion
about the possible executions (or ``runs'') of some function.
However, rather than making an assertion about single runs of the function,
it instead makes assertions about \<^emph>\<open>relations between\<close> runs of that function.
In this sense, EquivValid statements could be thought of as \<^emph>\<open>relational\<close> Hoare triples. \<close>

text \<open> This tutorial will introduce some syntactic sugar to emphasise the similarity
between Hoare triples and EquivValid statements.
(Here, \<open>\<top>\<top>\<close> is an alias provided by Monads.Nondet\_Monad for the trivial binary predicate,
which always returns \<open>True\<close>; similarly, there is also \<open>\<bottom>\<bottom>\<close> for \<open>False\<close>.) \<close>

abbreviation
  equiv_valid_sugar ::
  "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s,'b) nondet_monad \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>|_|, _\<rbrace>/ _ /\<lbrace>|_|\<rbrace>")
where
  "\<lbrace>|A|, P\<rbrace> f \<lbrace>|B|\<rbrace> \<equiv> equiv_valid \<top>\<top> A B P f"

text \<open> This most basic form of an EquivValid statement asserts that,
for any \<^emph>\<open>pair\<close> of runs of the function \<open>f\<close>,
assuming the \<^emph>\<open>pre-equivalence\<close> \<open>A\<close> relates the initial states of the two runs
(and the precondition \<open>P\<close> holds initially for both runs),
the \<^emph>\<open>post-equivalence\<close> \<open>B\<close> will relate the final states of the two runs afterwards. \<close>

term "\<lbrace>|A|, P\<rbrace> f \<lbrace>|B|\<rbrace>"
term "equiv_valid \<top>\<top> A B P f"

text \<open> The following Isabelle theorem in the EquivValid library gives
a definition for \<open>equiv_valid\<close> that is closest to that of ``ev'' as presented in
\cite{Murray_MBGK_12};
this is what we will use to unfold \<open>equiv_valid\<close> statements in this tutorial: \<close>

thm equiv_valid_def2[simplified equiv_valid_2_def]

text \<open> In the seL4 EquivValid library, the \<open>equiv_valid\<close> definition also includes,
as a convenience, an \<^emph>\<open>invariant equivalence\<close> \<open>I\<close> that it asserts as both pre- and
post-equivalence. We will ignore this convenience for the rest of this tutorial. \<close>

lemma "equiv_valid I \<top>\<top> \<top>\<top> P f = equiv_valid \<top>\<top> I I P f"
  unfolding equiv_valid_def2 equiv_valid_2_def
  by simp

text \<open> Furthermore, the library version of \<open>equiv_valid\<close> is defined in terms of a
version \<open>spec_equiv_valid\<close> that supports restricting the attention of the statement to
a particular initial state. We will avoid encountering \<open>spec_equiv_valid\<close> for the rest
of this tutorial, by unfolding \<open>equiv_valid_def2\<close> instead of \<open>equiv_valid_def\<close>. \<close>

\<comment> \<open>Specialised\<close>
thm equiv_valid_def
    equiv_valid_def[simplified spec_equiv_valid_def equiv_valid_2_def]

text \<open> Finally, the library also contains both simplified and more general forms of
EquivValid statement; the more general forms allow proof engineers to specify the
equivalences and functions on which they are asserted in a more fine-grained fashion
than is allowed by \<open>equiv_valid\<close>. These will be addressed further later in this tutorial. \<close>

\<comment> \<open>Simplified for A = B.\<close>
lemma "equiv_valid_inv I A P f" unfolding equiv_valid_def2 oops
\<comment> \<open>Generalised to allow specifying equivalence R on return values.\<close>
lemma "equiv_valid_rv_inv I A R P f" unfolding equiv_valid_2_def oops
\<comment> \<open>Generalised further.\<close>
lemma "equiv_valid_rv I A B R P f" unfolding equiv_valid_2_def oops
lemma "equiv_valid_2 I A B R P P' f f'" unfolding equiv_valid_2_def oops


section \<open> Example setting: a room with a view \<close>

text \<open> EquivValid statements assert equivalences between system states in alternative runs
of a given program; for this tutorial we define a basic structure for the system state: \<close>

record 'val Room =
  desk :: 'val
  window :: 'val
  outbox :: 'val
  inbox :: 'val
  job :: "'val \<Rightarrow> 'val"

text \<open> The state equivalences of interest will then be of the kind
``\<open>desk\<close> has the same value in both states'', and so forth.
We will typically use these to specify the attacker's assumed ability to make
observations of (or otherwise know) the contents of those parts of the state. \<close>

definition desk_equivalence :: "'val Room \<Rightarrow> 'val Room \<Rightarrow> bool"
where
  "desk_equivalence r1 r2 \<equiv> desk r1 = desk r2"

definition window_equivalence :: "'val Room \<Rightarrow> 'val Room \<Rightarrow> bool"
where
  "window_equivalence r1 r2 \<equiv> window r1 = window r2"

text \<open> We could just as well define equivalences similarly for
\<open>inbox\<close>, \<open>outbox\<close>, or \<open>job\<close> -- we omit these here. \<close>

text \<open> Furthermore, you can use the \<open>and\<close> alias provided by @{theory Monads.Fun_Pred_Syntax}
to write the conjunction of two binary predicates.
(Similarly, there is also an \<open>or\<close> alias for disjunction.)\<close>

lemma
  "(desk_equivalence and window_equivalence) r1 r2 =
   (desk r1 = desk r2 \<and> window r1 = window r2)"
  unfolding desk_equivalence_def window_equivalence_def
  by simp

text \<open> In this setting, we might consider a trivial program that just returns
the contents of \<open>desk\<close>; note, there is no difference between these two ways
of expressing it: \<close>
lemma "gets desk = do document \<leftarrow> gets desk; return document od"
  by simp

text \<open> Or, we might consider some programs that transfer values from one part
of the state to another, write constants to state, execute functions
that can themselves be found in state, or some combination of these: \<close>

definition reveal_desk_to_window :: "('val Room, unit) nondet_monad"
where
  "reveal_desk_to_window \<equiv> modify (\<lambda>s. s\<lparr>window := desk s\<rparr>)"

definition sanitise_desk :: "('val::zero Room, unit) nondet_monad"
where
  "sanitise_desk \<equiv> modify (\<lambda>s. s\<lparr>desk := 0\<rparr>)"

definition work_at_desk :: "('val Room, unit) nondet_monad"
where
  "work_at_desk \<equiv>
     do modify (\<lambda>s. s\<lparr>desk := inbox s\<rparr>);
        modify (\<lambda>s. s\<lparr>desk := (job s) (desk s)\<rparr>);
        modify (\<lambda>s. s\<lparr>outbox := desk s\<rparr>)
     od"

definition work_sanitise_reveal :: "('val::zero Room, unit) nondet_monad"
where
  "work_sanitise_reveal \<equiv>
     do work_at_desk;
        sanitise_desk;
        reveal_desk_to_window
     od"


section \<open> Attacker models expressible using EquivValid statements \<close>

subsection \<open> An attacker with access to return values \<close>

text \<open> The most basic form of \<open>equiv_valid\<close> asserts an information-flow security property
that would be appropriate against an attacker that can see only the program's return value:
that any two runs of this program will give the same return value.\footnote{If you think
this doesn't sound like a very useful program, you'd be spot on: Our goal here is
to prove that the program would be stubbornly uninformative to such an attacker.}

Of course, we will find that we can't expect to prove this unless we place some
restrictions on the runs under consideration.
Consider the case where we are maximally permissive with the pre- and post-equivalences
(by supplying \<open>\<top>\<top>\<close>) and precondition (by supplying \<open>\<top>\<close>): \<close>

lemma gets_desk_return_leak:
  \<comment> \<open> No restrictions on pre-equivalence, precondition, or post-equivalence. \<close>
  "\<lbrace>|\<top>\<top>|, \<top>\<rbrace> gets desk \<lbrace>|\<top>\<top>|\<rbrace>"
  find_theorems intro
  \<comment> \<open> There happens to be an applicable \<open>gets\<close> rule for \<open>equiv_valid_inv\<close>. \<close>
  thm gets_ev''
  apply(rule gets_ev'')
  \<comment> \<open> \<open>equiv_valid\<close> requires the return value to be the same in both runs.
     As expected, we are stuck, as we don't know that the contents of \<open>desk\<close>
     were initially the same for both runs. \<close>
  nitpick
  oops

text \<open> How might we know that \<open>gets desk\<close> will return the same value for each of
a given pair of runs?

One way we might know this is if the pre-equivalence tells us that we can assume
that \<open>desk\<close> initially has the same value in both runs.
This might be appropriate to assume, for example:
(1) after executing some function that equalises the value of \<open>desk\<close> between
   all runs under consideration, or
(2) when the attacker already knows the contents of \<open>desk\<close>.
Note that these are just two ways of saying that we consider it to be acceptable
for the attacker to know the initial contents of \<open>desk\<close>.

We can specify this formally by setting \<open>desk_equivalence\<close> as the pre-equivalence.%
\footnote{To avoid complicating things for now, we'll also set the post-equivalence
to be the same as the pre-equivalence. Examples of proving \<open>equiv_valid\<close> statements
with a different pre- and post-equivalence will be addressed later in this tutorial.}
The resulting EquivValid statement's demand for equal return values is easily provable
for \<open>gets desk\<close>, using the \<open>gets\<close> rule for \<open>equiv_valid\<close> we found earlier: \<close>

lemma gets_desk_equiv_return:
  \<comment> \<open> Pre-equivalence (and post-equivalence):
      The value of \<open>desk\<close> is equal initially (and finally) for both runs. \<close>
  "\<lbrace>|desk_equivalence|, \<top>\<rbrace>
     gets desk
   \<lbrace>|desk_equivalence|\<rbrace>"
  find_theorems intro
  apply(rule gets_ev'')
  unfolding desk_equivalence_def
  by simp

text \<open> Note that the \<open>equiv_valid_rv\<close> form of EquivValid allows you to customise the
relationship demanded between return values to be something other than equality: \<close>
lemma "\<lbrace>|\<top>\<top>|, \<top>\<rbrace> f \<lbrace>|\<top>\<top>|\<rbrace> = equiv_valid_rv \<top>\<top> \<top>\<top> \<top>\<top> (=) \<top> f"
  by (simp add:equiv_valid_def2) \<comment> \<open> Try replacing the \<open>(=)\<close> here. \<close>


subsection \<open> An attacker with a window into the system state \<close>

text \<open> As a rule of thumb, we use an EquivValid statement's pre-equivalence to specify
the secrecy (or initial attacker knowledge) of values in system state, and use the
post-equivalence to specify the attacker's powers of observation.

Suppose now a scenario where the desk in our room initially contains secrets,
and we wish to prevent these secrets from affecting what is observable to an attacker
with binoculars pointed at the window. In this case:
\begin{enumerate}
\item We \<^emph>\<open>do not\<close> include \<open>desk_equivalence\<close> in the pre-equivalence, as we
      do not consider it acceptable for the attacker to know the initial contents of \<open>desk\<close>.

\item Furthermore, we \<^emph>\<open>do\<close> include \<open>window_equivalence\<close> in the post-equivalence, as we
      do consider that the attacker will be able to observe the final contents of \<open>window\<close>.
\end{enumerate}

Clearly, in this situation, using \<open>modify\<close> to transfer the contents of \<open>desk\<close>
to \<open>window\<close> would constitute an unacceptable information leak.
So we should be encouraged to see that the following \<open>equiv_valid\<close>
statement is not provable: \<close>

lemma reveal_desk_window_leak:
  \<comment> \<open> Pre-equivalence and post-equivalence:
      The value of \<open>window\<close> is equal initially and finally for both runs. \<close>
  "\<lbrace>|window_equivalence|, \<top>\<rbrace>
     reveal_desk_to_window
   \<lbrace>|window_equivalence|\<rbrace>"
  unfolding reveal_desk_to_window_def
  \<comment> \<open> We find an applicable \<open>modify\<close> rule for \<open>equiv_valid_inv\<close>. \<close>
  find_theorems intro
  apply(rule modify_ev'')
  \<comment> \<open> Applying it, we see that it demands that \<open>window_equivalence\<close> holds
      between the final states of both runs. \<close>
  unfolding window_equivalence_def
  apply clarsimp
  \<comment> \<open> We should not expect to be able to prove this, because we have
      said nothing about the initial value of desk in these runs. \<close>
  oops (* Try: nitpick *)

text \<open> As before, however, we should expect this to hold with a pre-equivalence
that includes \<open>desk_equivalence\<close>. \<close>

lemma reveal_desk_equiv_window_equiv:
  "\<lbrace>|desk_equivalence and window_equivalence|, \<top>\<rbrace>
     reveal_desk_to_window
   \<lbrace>|desk_equivalence and window_equivalence|\<rbrace>"
  unfolding reveal_desk_to_window_def
  apply(rule modify_ev'')
  unfolding desk_equivalence_def window_equivalence_def
  by clarsimp


section \<open> The typical toolkit \<close>

subsection \<open> Using and customising the \<open>wp\<close> tool's rule set \<close>

text \<open> Recall the lemma we proved for \<open>gets desk\<close>: \<close>
thm gets_desk_equiv_return
text \<open> Instead of using any of the \<open>gets\<close> rules for \<open>equiv_valid\<close> directly, we can
also try using the \<open>wp\<close> tool to see if it has any applicable rules in its rule set: \<close>
thm wp_ev

text \<open>Before applying \<open>wp\<close> to EquivValid statements in this fashion, we may need
to use the rule \<open>pre_ev\<close> to weaken their precondition.
This allows us to apply rules that are designed to be applied when the precondition
is a schematic variable, so as to infer a weakest precondition for the statement to hold.
It then leaves a goal for later to show that our original precondition implies
the weaker one that was inferred.\<close>
thm pre_ev
\<comment> \<open> Note: \<open>pre_ev\<close> is just the standard \<open>hoare_pre\<close> + \<open>equiv_valid_guard_imp\<close> \<close>
thm hoare_pre
thm equiv_valid_guard_imp

text \<open> Applying the \<open>wp\<close> tactic then works because the \<open>gets_ev\<close> rule happens to be
in the \<open>wp\<close> tool's rule set: \<close>
thm gets_ev

lemma gets_desk_equiv_return_using_wp:
  "\<lbrace>|desk_equivalence|, \<top>\<rbrace>
     gets desk
   \<lbrace>|desk_equivalence|\<rbrace>"
  \<comment> \<open> Use \<open>pre_ev\<close> to weaken the precondition of the \<open>equiv_valid\<close> statement
       and make the \<open>wp\<close> method applicable. \<close>
  apply(rule pre_ev)
   apply wp
  unfolding desk_equivalence_def
  by simp

text \<open> You can freely customise the \<open>wp\<close> rule set as needed, whether to
add new rules, or to replace rules with ones that are more applicable
in a given situation.

For example, the \<open>modify_ev\<close> rule is not part of the default \<open>wp\<close> rule set: \<close>

thm reveal_desk_equiv_window_equiv
  modify_ev

lemma reveal_desk_equiv_window_equiv_using_wp:
  "\<lbrace>|desk_equivalence and window_equivalence|, \<top>\<rbrace>
     reveal_desk_to_window
   \<lbrace>|desk_equivalence and window_equivalence|\<rbrace>"
  unfolding reveal_desk_to_window_def
  apply(rule pre_ev)
   apply(wp add:modify_ev)
  unfolding desk_equivalence_def window_equivalence_def
  by clarsimp

text \<open> As another example:
It might be the \<^emph>\<open>precondition\<close> for both runs that tells us that \<open>desk\<close> has
a fixed initial constant value \<open>c\<close> that is common to both runs.
(This might be the case if, even if we might normally use \<open>desk\<close> for
secrets, we happen to have just executed a ``flush'' function that writes \<open>c\<close> to
\<open>desk\<close> before this point in the program, for all pairs of runs we care to compare.)

Here we can modify the wp rule set to invoke \<open>gets_ev''\<close> for \<open>equiv_valid\<close>,
which is better than the default \<open>gets_ev\<close> rule for situations like this
where we actually need to use the precondition: \<close>
thm gets_ev''

lemma example_precond_desk_return:
  \<comment> \<open> Precondition: The value of desk is some fixed value \<open>c\<close>.
      \<open>equiv_valid\<close> then assumes that this precondition applies to both runs. \<close>
  "\<lbrace>|\<top>\<top>|, (\<lambda>s. desk s = c)\<rbrace>
     gets desk
   \<lbrace>|\<top>\<top>|\<rbrace>"
  apply(wp del:gets_ev add:gets_ev'')
  by force

text \<open> Relying on such a precondition, a similar argument is possible
when proving that \<open>reveal_desk_to_window\<close> preserves \<open>window_equivalence\<close>: \<close>
thm modify_ev''

lemma reveal_const_desk_preserves_window_equiv:
  \<comment> \<open> Precondition: Desk initially has a fixed constant \<open>c\<close>.
      \<open>equiv_valid\<close> then assumes that this precondition applies to both runs. \<close>
  "\<lbrace>|window_equivalence|, (\<lambda>s. desk s = c)\<rbrace>
     reveal_desk_to_window
   \<lbrace>|window_equivalence|\<rbrace>"
  unfolding reveal_desk_to_window_def
  apply(wp add:modify_ev'')
  unfolding window_equivalence_def
  by clarsimp

text \<open> Finally, new EquivValid rules that we expect to be exercised
often can be added to the \<open>wp\<close> rule set using a declaration: \<close>
declare modify_ev[wp]


subsection \<open> Remainder of worked example using \<open>wp\<close> tool \<close>

text \<open> Let's use all this to prove that our overarching program,
\<open>work_sanitise_reveal\<close>, is secure against the attacker at the window
with the binoculars (i.e. preserves \<open>window_equivalence\<close>). \<close>

thm work_sanitise_reveal_def

text \<open> First, we expect these two statements to be provable, because
\<open>work_at_desk\<close> and \<open>sanitise_desk\<close> have nothing to do with the window. \<close>

lemma work_at_desk_preserves_window_equiv:
  "\<lbrace>|window_equivalence|, P\<rbrace>
     work_at_desk
   \<lbrace>|window_equivalence|\<rbrace>"
  unfolding work_at_desk_def
  apply wp \<comment> \<open> Instead of \<open>apply(wp add:modify_ev)\<close> \<close>
  unfolding window_equivalence_def
  by force

lemma sanitise_desk_preserves_window_equiv:
  "\<lbrace>|window_equivalence|, P\<rbrace>
     sanitise_desk
   \<lbrace>|window_equivalence|\<rbrace>"
  unfolding sanitise_desk_def
  apply(rule pre_ev)
   apply wp \<comment> \<open> Instead of \<open>apply(wp add:modify_ev)\<close> \<close>
  unfolding window_equivalence_def
  by force

text \<open> The consequence of all this is that \<open>work_at_desk\<close> might freely
shuttle secrets between \<open>inbox\<close> and \<open>outbox\<close> via \<open>desk\<close>, and execute
a secret \<open>job\<close> on them, but it does not allow any of these secrets
to affect what is visible at \<open>window\<close>.

The mere fact of \<^emph>\<open>excluding\<close> any equivalences on \<open>inbox\<close>, \<open>outbox\<close>, or
\<open>job\<close> from the pre- and post-equivalence of these statements
implies both:
\begin{enumerate}
\item We \<^emph>\<open>do not\<close> consider it acceptable for the attacker to know the
      initial values of \<open>inbox\<close> and \<open>outbox\<close> in these locations;
      even the \<open>job\<close> to be executed may differ between the runs.
      All of these are therefore secrets to be protected by the property.

\item We \<^emph>\<open>do\<close> consider it acceptable for \<open>inbox\<close>, \<open>outbox\<close>, and \<open>job\<close>
      to contain secret values after the program has finished executing.
\end{enumerate} \<close>

text \<open> We will, however, need that \<open>sanitise_desk\<close> establishes the precondition
demanded by our recently proved lemma: that \<open>desk\<close> contains a constant. \<close>
thm reveal_const_desk_preserves_window_equiv

text \<open> Note that this is a regular (non-EquivValid) Hoare triple: \<close>
lemma sanitise_desk_sets_zero:
  "\<lbrace>P\<rbrace> sanitise_desk \<lbrace>\<lambda>r s. desk s = 0\<rbrace>"
  unfolding sanitise_desk_def
  apply(rule pre_ev)
   apply wp
  by force

text \<open> We can now use all these lemmas to have \<open>wp\<close> discharge that
our overarching program \<open>work_sanitise_reveal\<close> preserves \<open>window_equivalence\<close>. \<close>

lemma work_sanitise_reveal_preserves_window_equiv:
  "\<lbrace>|window_equivalence|, \<top>\<rbrace>
     work_sanitise_reveal
   \<lbrace>|window_equivalence|\<rbrace>"
  unfolding work_sanitise_reveal_def
  apply(wp add:reveal_const_desk_preserves_window_equiv[where c=0]
               sanitise_desk_preserves_window_equiv
               sanitise_desk_sets_zero
               work_at_desk_preserves_window_equiv)
  by force


section \<open> The advanced toolkit \<close>

subsection \<open> More general forms of EquivValid statements \<close>

text \<open> Lib.EquivValid provides rules for discharging \<open>equiv_valid_inv\<close> statements for
the basic monad primitives \<open>return\<close> and \<open>bind\<close>, and some of the more basic functions
like \<open>gets\<close> (already seen); potentially in a number of variants. \<close>

thm return_ev
  bind_ev
  gets_ev gets_ev' gets_ev''
  modify_ev modify_ev' modify_ev''

text \<open> On rare occasions you may find a need to use some of the more general
forms of EquivValid. These are all defined in terms of the most general form,
\<open>equiv_valid_2\<close>, which allows full customisation of
(1) return value equivalence \<open>R\<close>,
(2) differing pre-equivalence \<open>A\<close> vs post-equivalence \<open>B\<close>, and even
(3) differing preconditions \<open>P,P'\<close> and functions \<open>f,f'\<close> for each run.
(In \cite{Murray_MBGK_12}, \<open>equiv_valid_2\<close> is referred to as ``ev2''.) \<close>

\<comment> \<open>Generalised to allow specifying equivalence R on return values.\<close>
lemma "equiv_valid_rv_inv I A R P f" unfolding equiv_valid_2_def oops
\<comment> \<open>Generalised further.\<close>
lemma "equiv_valid_rv I A B R P f" unfolding equiv_valid_2_def oops
lemma "equiv_valid_2 I A B R P P' f f'" unfolding equiv_valid_2_def oops

text \<open> If you ever have a need to unfold an \<open>equiv_valid\<close> statement to its
\<open>equiv_valid_2\<close> form -- perhaps as part of a more involved manual proof --
it is often better to unfold \<open>equiv_valid_def2\<close> rather than \<open>equiv_valid_def\<close>.

Lib.EquivValid also provides various rules for discharging \<open>equiv_valid_2\<close>
statements for the basic monad primitives. For example: \<close>

thm return_ev2
  equiv_valid_2_bind equiv_valid_2_bind_pre equiv_valid_2_bind_general
  modify_ev2

lemma reveal_desk_equiv_window_equiv_using_ev2:
  "\<lbrace>|desk_equivalence and window_equivalence|, \<top>\<rbrace>
     reveal_desk_to_window
   \<lbrace>|desk_equivalence and window_equivalence|\<rbrace>"
  unfolding reveal_desk_to_window_def
  apply(clarsimp simp:equiv_valid_def2)
  \<comment> \<open> After peeling back to \<open>equiv_valid_2\<close> form, we can use its \<open>modify\<close> rule. \<close>
  find_theorems intro
  apply(rule modify_ev2)
  unfolding desk_equivalence_def window_equivalence_def
  by simp

text \<open> The basic \<open>equiv_valid\<close> form and its rule set may sometimes
be too restrictive, due to their demand for return values to be equal.

For example, if we ever needed to prove an \<open>equiv_valid\<close> statement about
\<open>do s \<leftarrow> get; return (f s) od\<close>, we would need to unfold it to \<open>equiv_valid_2\<close> form.
This is because \<open>equiv_valid\<close> and its bind rule \<open>bind_ev_pre\<close> will both demand
that the return value of \<open>get\<close> (the entire state) be the same for both runs;
however, we might only need (or know) the parts of the state inspected
by the function \<open>f\<close> to be the same. Say \<open>f\<close> was \<open>desk\<close>: \<close>

thm bind_ev_pre
    equiv_valid_def2[simplified equiv_valid_2_def]

lemma pitfall1_using_bind_ev:
  "\<lbrace>|\<top>\<top>|, (\<lambda>s. desk s = c)\<rbrace>
     do
       s \<leftarrow> get;
       return (desk s)
     od
   \<lbrace>|\<top>\<top>|\<rbrace>"
  \<comment> \<open> Using the bind rule for \<open>equiv_valid\<close> splits the goal into
      two \<open>equiv_valid\<close> statements, one for each of \<open>get\<close> and \<open>return\<close>.
      It will ask us to prove them in reverse order. \<close>
  apply(rule bind_ev_pre)
     \<comment> \<open> The \<open>wp\<close> tool discharges the \<open>return (desk s)\<close> part trivially: \<close>
     apply wp
    \<comment> \<open> But the return value of \<open>get\<close> is the entire state: \<close>
    apply(clarsimp simp:equiv_valid_def2 equiv_valid_2_def)
    apply(clarsimp simp add:get_def)
    \<comment> \<open> This causes us to get stuck, because we have no idea whether the state
        is equivalent for parts of the room other than the desk. \<close>
    oops

text \<open> Therefore we need to use \<open>equiv_valid_2\<close> and its bind rule \<open>equiv_valid_2_bind_pre\<close>;
these will allow us to specify the equivalence \<open>R\<close> to be asserted between
the return values of the \<open>get\<close>. \<close>

thm equiv_valid_2_bind_pre
  equiv_valid_2_def

text \<open> Another anti-pattern to avoid when applying the bind rules directly is leaving
intermediate preconditions unspecified; the automation is liable to guess \<open>False\<close>,
which will later be unprovable.

Here, the \<open>force\<close> tactic correctly infers that \<open>desk_equivalence\<close> is the equivalence \<open>R\<close>
that we need between the return values from \<open>get\<close>.
However, it guesses an incorrect postcondition: \<close>

lemma pitfall2_using_bind_ev2:
  "\<lbrace>|\<top>\<top>|, (\<lambda>s. desk s = c)\<rbrace>
     do
       s \<leftarrow> get;
       return (desk s)
     od
   \<lbrace>|\<top>\<top>|\<rbrace>"
  \<comment> \<open> First we need to peel it back to \<open>equiv_valid_2\<close> form, so we can apply its bind rule. \<close>
  apply(clarsimp simp:equiv_valid_def2)
  apply(rule equiv_valid_2_bind_pre)
       \<comment> \<open> Here \<open>wp\<close> infers correctly that the equivalence between the
          intermediate return values needs to be \<open>\<lambda>rv rv'. desk rv = desk rv'\<close>,
          i.e. that \<open>desk\<close> has the same value in the state returned by \<open>get\<close> in both runs. \<close>
       apply(wp add:return_ev2)
      apply(clarsimp simp:equiv_valid_def spec_equiv_valid_def equiv_valid_2_def)
      \<comment> \<open> The \<open>force\<close> tactic just guesses \<open>False\<close> for the postcondition for both steps. \<close>
      apply(force simp add:get_def)
     \<comment> \<open> As these next two goals are Hoare triples, we use the \<open>wp\<close> tool, as usual for
         Hoare triples in the seL4 proof base. See Lib.WPTutorial for more information. \<close>
     apply wp
    apply wp
   \<comment> \<open> Now we are stuck because \<open>force\<close> guessed \<open>False\<close> as a premise
      to discharge the goal earlier, giving us an unsatisfiable goal here. \<close>
   oops

text \<open> We can avoid this by giving \<open>equiv_valid_2\<close>'s bind rule a little more information. \<close>

lemma precond_get_return_desk:
  "\<lbrace>|\<top>\<top>|, (\<lambda>s. desk s = c)\<rbrace>
     do
       s \<leftarrow> get;
       return (desk s)
     od
   \<lbrace>|\<top>\<top>|\<rbrace>"
  apply(clarsimp simp:equiv_valid_def2)
  \<comment> \<open> We want to use the fact that \<open>desk\<close> contains \<open>c\<close> initially for both runs.
    So we give it here. \<close>
  apply(rule_tac P="(\<lambda>s. desk s = c)" and P'="(\<lambda>s. desk s = c)" in equiv_valid_2_bind_pre)
       apply(wp add:return_ev2)
      apply(clarsimp simp:equiv_valid_def2 equiv_valid_2_def)
      \<comment> \<open> No need to guess anything. \<close>
      apply(force simp add:get_def)
     \<comment> \<open> Use \<open>wp\<close> tactic to discharge the two Hoare triples; see Lib.WPTutorial for more info. \<close>
     apply wp
    apply wp
   apply force
  apply force
  done

subsection \<open> A note on what is currently available and why \<close>

text \<open> As noted in \cite{Murray_MBGK_12}, the machinery developed of this kind
(available in Lib.EquivValid's default \<open>wp\<close> rule set) is mostly geared
towards \<open>equiv_valid_inv\<close>; this is an abbrevation for the simplified case of
\<open>equiv_valid\<close> where the post-equivalence is the same as the pre-equivalence: \<close>

lemma "equiv_valid_inv I A P f" unfolding equiv_valid_def2 equiv_valid_2_def oops

text \<open> The reason for this is that the seL4 infoflow proofs take the approach of defining an
\emph{unwinding} relation \cite{Goguen_Meseguer_84}: an equivalence relation
flexible enough to describe what we think ought to continue to look the same between
all possible pairs of executions as seen by a given attacker model.%
\footnote{If every pair of executions being compared is like a wound-up rope ladder thrown
over the side of a ship, then the rungs of those ladders would be the unwinding relation.}

However, the EquivValid library merely provides a way to reason about equivalences,
so it is not prescriptive about taking this approach.

Furthermore, the overall unwinding relation for a system may be composed from a number of
equivalences, which may each hold or not at different times, in a manner that depends on
where we are in the system.%
\footnote{This is like saying that the first six rungs of the ladder may be made of wood,
but the next seven rungs may be made of aluminium, and so on.}
As it happens, this is the case for seL4's unwinding relation, but the number of ev sub-lemmas
needing to be proved for differing pre-/post-equivalences is rather limited at current time of
writing, hence the lack of machinery.%
\footnote{This may perhaps be the lemma covering the step between the sixth and seventh
rung of our imaginary wood-and-aluminium--runged ladder.} \<close>


subsection \<open> Proving EquivValid with differing pre- and post-equivalences \<close>

text \<open> So far we have only proved \<open>equiv_valid\<close> statements
whose pre-equivalence is the same as their post-equivalence.

We will now attempt to prove an \<open>equiv_valid\<close> statement where they differ.

This allows us to say, for example, that although usually we use the desk
for secrets:
(1) at this point in the program we happened to make sure that
    desk contains the same value for any two runs we care to check, and
(2) we don't care if desk contains the same value for both runs afterwards. \<close>

lemma reveal_desk_equiv_to_window_equiv:
  "\<lbrace>|desk_equivalence|, \<top>\<rbrace>  \<comment> \<open> Pre-equivalence: The value of \<open>desk\<close> is
                                 the same initially in both runs. \<close>
     reveal_desk_to_window
   \<lbrace>|window_equivalence|\<rbrace>" \<comment> \<open> Post-equivalence: The value of \<open>window\<close> is required to be
                                the same at the end of both runs; no longer so for \<open>desk\<close>. \<close>
  unfolding reveal_desk_to_window_def
  apply(rule modify_ev'')
  unfolding window_equivalence_def desk_equivalence_def
  by simp

text \<open> This is handy, because we might subsequently copy secrets into the desk,
in which case \<open>desk_equivalence\<close> would no longer hold in the post-equivalence.

As before, the mere fact of \<^emph>\<open>excluding\<close> any equivalence on \<open>inbox\<close> from the
pre-equivalence implies we \<^emph>\<open>do not\<close> consider it acceptable for the attacker
to know \<open>inbox\<close>'s initial value; it is therefore a secret to be protected by this property.
Conversely, the absence of \<open>desk_equivalence\<close> from the post-equivalence implies
that we \<^emph>\<open>do\<close> consider it acceptable for the desk to contain secrets after the program
has finished executing.

Consequently, this \<open>equiv_valid\<close> statement is provable: \<close>

lemma desk_equiv_no_longer_needed:
  "\<lbrace>|desk_equivalence|, \<top>\<rbrace>
       do reveal_desk_to_window;
          modify (\<lambda>r. r\<lparr>desk := inbox r\<rparr>)
       od
   \<lbrace>|window_equivalence|\<rbrace>"
  \<comment> \<open> Use \<open>pre_ev\<close> to weaken the precondition of the \<open>equiv_valid\<close> statement. \<close>
  apply(rule pre_ev)
   \<comment> \<open> Use \<open>bind_ev_general\<close> to split the goal into \<open>equiv_valid\<close> statements for
       each of the two \<open>modify\<close> commands. It will ask us to prove them in reverse order. \<close>
   apply(rule bind_ev_general)
     \<comment> \<open> Prove \<open>equiv_valid\<close> for \<open>desk := inbox\<close> manually. \<close>
     apply clarsimp
     apply(rule modify_ev'')
     \<comment> \<open> The \<open>force\<close> tactic has enough information here to figure out that
         the intermediate equivalence \<open>B\<close> needs to be \<open>window_equivalence\<close>. \<close>
     apply(force simp:window_equivalence_def desk_equivalence_def)
    \<comment> \<open> This happens to be the post-equivalence for the \<open>equiv_valid\<close> lemma
        we just proved for \<open>window := desk\<close>, so we can reuse that lemma here. \<close>
    using reveal_desk_equiv_to_window_equiv
    unfolding window_equivalence_def
    apply force
   apply wp
  apply force
  done

end
