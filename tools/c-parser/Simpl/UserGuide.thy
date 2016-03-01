(*  Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

(*  Title:      UserGuide.thy
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

section {* User Guide \label{sec:UserGuide}*}
(*<*)
theory UserGuide 
imports HeapList Vcg
  "~~/src/HOL/Statespace/StateSpaceSyntax" "~~/src/HOL/Library/LaTeXsugar"
begin 
(*>*)

(*<*)
syntax
 "_statespace_updates" :: "('a \<Rightarrow> 'b) \<Rightarrow> updbinds \<Rightarrow> ('a \<Rightarrow> 'b)" ("_\<langle>_\<rangle>" [900,0] 900)
(*>*)



text {*
We introduce the verification environment with a couple
of examples that illustrate how to use the different
bits and pieces to verify programs. 
*}


subsection {* Basics *}

text {*

First of all we have to decide how to represent the state space. There
are currently two implementations. One is based on records the other
one on the concept called `statespace' that was introduced with
Isabelle 2007 (see \texttt{HOL/Statespace}) . In contrast to records a 
'satespace' does not define a new type, but provides a notion of state, 
based on locales. Logically
the state is modelled as a function from (abstract) names to
(abstract) values and the statespace infrastructure organises
distinctness of names an projection/injection of concrete values into
the abstract one. Towards the user the interface of records and
statespaces is quite similar. However, statespaces offer more
flexibility, inherited from the locale infrastructure, in
particular multiple inheritance and renaming of components.

In this user guide we prefer statespaces, but give some comments on
the usage of records in Section \ref{sec:records}. 


*}

hoarestate vars = 
  A :: nat
  I :: nat
  M :: nat
  N :: nat
  R :: nat
  S :: nat

text (in vars) {* The command \isacommand{hoarestate} is a simple preprocessor
for the command \isacommand{statespaces} which decorates the state
components with the suffix @{text "_'"}, to avoid cluttering the
namespace. Also note that underscores are printed as hyphens in this
documentation. So what you see as @{term "A_'"} in this document is
actually \texttt{A\_'}.  Every component name becomes a fixed variable in
the locale @{text vars} and can no longer be used for logical
variables. 

Lookup of a component @{term "A_'"} in a state @{term "s"} is written as
@{term "s\<cdot>A_'"}, and update with a value @{term "term v"} as @{term "s\<langle>A_' := v\<rangle>"}.

To deal with local and global variables in the context of procedures the
program state is organised as a record containing the two componets @{const "locals"} 
and @{const "globals"}. The variables defined in hoarestate @{text "vars"} reside
in the @{const "locals"} part.

*}

text {*
  Here is a first example.
*}

lemma (in vars) "\<Gamma>\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> \<acute>N :== 2 * \<acute>N \<lbrace>\<acute>N = 10\<rbrace>"
  apply vcg
  txt {* @{subgoals} *}
  apply simp
  txt {* @{subgoals} *}
  done

text {* We enable the locale of statespace @{text vars} by the
\texttt{in vars} directive.  The verification condition generator is
invoked via the @{text vcg} method and leaves us with the expected
subgoal that can be proved by simplification.  *}

text (in vars) {*
 If we refer to components (variables) of the state-space of the program
 we always mark these with @{text "\<acute>"} (in assertions and also in the
 program itself). It is the acute-symbol and is present on
 most keyboards. The assertions of the Hoare tuple are
 ordinary Isabelle sets. As we usually want to refer to the state space
 in the assertions, we provide special brackets for them. They can be written 
 as {\verb+{| |}+} in ASCII or @{text "\<lbrace> \<rbrace>"} with symbols. Internally,
 marking variables has two effects. First of all we refer to the implicit
 state and secondary we get rid of the suffix @{text "_'"}.
 So the assertion @{term "{|\<acute>N = 5|}"} internally gets expanded to 
 @{text "{s. locals s \<cdot>N_' = 5}"} written in ordinary set comprehension notation of
 Isabelle. It describes the set of states where the @{text "N_'"} component
 is equal to @{text "5"}. 
 An empty context and an empty postcondition for abrupt termination can be
 omitted. The lemma above is a shorthand for 
  @{text "\<Gamma>,{}\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> \<acute>N :== 2 * \<acute>N \<lbrace>\<acute>N = 10\<rbrace>,{}"}.
*}

text {* We can step through verification condition generation by the
method @{text vcg_step}.
*}

lemma (in vars) "\<Gamma>,{}\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> \<acute>N :== 2 * \<acute>N \<lbrace>\<acute>N = 10\<rbrace>"
  apply vcg_step
  txt {* @{subgoals} *}
  txt {* The last step of verification condition generation, 
         transforms the inclusion of state sets to the corresponding 
         predicate on components of the state space. 
  *}
  apply vcg_step
  txt {* @{subgoals} *}
  by simp

text {*
Although our assertions work semantically on the state space, stepping
through verification condition generation ``feels'' like the expected
syntactic substitutions of traditional Hoare logic. This is achieved
by light simplification on the assertions calculated by the Hoare rules.
*}

lemma (in vars) "\<Gamma>\<turnstile> \<lbrace>\<acute>N = 5\<rbrace> \<acute>N :== 2 * \<acute>N \<lbrace>\<acute>N = 10\<rbrace>"
  apply (rule HoarePartial.Basic)
  txt {* @{subgoals} *}
  apply (simp only: mem_Collect_eq)
  txt {* @{subgoals} *}
  apply (tactic 
    {* Hoare.BasicSimpTac @{context} Hoare.Function false
       [] (K all_tac) 1*})
  txt {* @{subgoals} *}
  by simp


text {* The next example shows how we deal with the while loop. Note the
invariant annotation.
*}

lemma (in vars) 
  "\<Gamma>,{}\<turnstile> \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
          WHILE \<acute>M \<noteq> a
          INV \<lbrace>\<acute>S = \<acute>M * b\<rbrace>
          DO \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 OD
          \<lbrace>\<acute>S = a * b\<rbrace>"
  apply vcg
  txt {* @{subgoals [display]} *}
  txt {* The verification condition generator gives us three proof obligations,
         stemming from the path from the precondition to the invariant,
         from the invariant together with loop condition through the
         loop body to the invariant, and finally from the invariant together
         with the negated loop condition to the postcondition.*}
  apply auto
  done

subsection {* Procedures *}

subsubsection {* Declaration *}

text {*
Our first procedure is a simple square procedure. We provide the
command \isacommand{procedures}, to declare and define a
procedure.
*}

procedures
  Square (N::nat|R::nat) 
  where I::nat in
  "\<acute>R :== \<acute>N * \<acute>N"
  


text {* A procedure is given by the signature of the procedure
followed by the procedure body.  The signature consists of the name of
the procedure and a list of parameters together with their types. The
parameters in front of the pipe @{text "|"} are value parameters and
behind the pipe are the result parameters. Value parameters model call
by value semantics. The value of a result parameter at the end of the
procedure is passed back to the caller. Local variables follow the
@{text "where"}. If there are no local variables the @{text "where \<dots>
in"} can be omitted. The variable @{term "I"} is actually unused in
the body, but is used in the examples below.  *}


text {*
The procedures command provides convenient syntax
for procedure calls (that creates the proper @{term init}, @{term return} and
@{term result} functions on the fly) and creates locales and statespaces to 
reason about the procedure. The purpose of locales is to set up logical contexts
to support modular reasoning. Locales can be seen as freeze-dried proof contexts that
get alive as you setup a new lemma or theorem (\cite{Ballarin-04-locales}).
The locale the user deals with is named @{text "Square_impl"}.
 It defines the procedure name (internally   @{term "Square_'proc"}), the procedure body 
(named @{text "Square_body"}) and the statespaces for parameters and local and
global variables.
Moreover it contains the 
assumption @{term "\<Gamma> Square_'proc = Some Square_body"}, which states 
that the procedure is properly defined in the procedure context. 

The purpose of the locale is to give us easy means to setup the context 
in which we prove programs correct.  
In this locale the procedure context @{term "\<Gamma>"} is fixed. 
So we always use this letter for the procedure
specification. This is crucial, if we prove programs under the
assumption of some procedure specifications.
*}

(*<*)
context Square_impl
begin
(*>*)
text {* The procedures command generates syntax, so that we can 
either write @{text "CALL Square(\<acute>I,\<acute>R)"} or @{term "\<acute>I :== CALL
Square(\<acute>R)"} for the procedure call. The internal term is the
following: 
*} 

(*<*) declare [[hoare_use_call_tr' = false]] (*>*) 
text {* \small @{term [display] "CALL Square(\<acute>I,\<acute>R)"} *} 
(*<*) declare [[hoare_use_call_tr' = true]] (*>*)

text {* Note the
        additional decoration (with the procedure name) of the parameter and
         local variable names.*}
(*<*)
end 
(*>*)

text {* The abstract syntax for the
procedure call is @{term "call init p return result"}.  The @{term
"init"} function copies the values of the actual parameters to the
formal parameters, the @{term return} function copies the global
variables back (in our case there are no global variables), and the
@{term "result"} function additionally copies the values of the formal
result parameters to the actual locations. Actual value parameters can
be all kind of expressions, since we only need their value. But result
parameters must be proper ``lvalues'': variables (including
dereferenced pointers) or array locations, since we have to assign
values to them. 
*}

subsubsection {* Verification *}

text (in Square_impl) {*
A procedure specification is an ordinary Hoare tuple. 
We use the parameterless
call for the specification; @{text "\<acute>R :== PROC Square(\<acute>N)"} is syntactic sugar
for @{text "Call Square_'proc"}. This emphasises that the specification 
describes the internal behaviour of the procedure, whereas parameter passing
corresponds to the procedure call.
The following precondition fixes the current value @{text "\<acute>N"} to the logical 
variable @{term n}. 
Universal quantification of @{term "n"} enables us to adapt 
the specification to an actual parameter. The specification is
used in the rule for procedure call when we come upon a call to @{term Square}. 
Thus @{term "n"} plays the role of the auxiliary variable @{term "Z"}.
*}


text {* To verify the procedure we need to verify the body. We use
a derived variant of the general recursion rule, tailored for non recursive procedures:
@{thm [source] HoarePartial.ProcNoRec1}:
\begin{center}
@{thm [mode=Rule,mode=ParenStmt] HoarePartial.ProcNoRec1 [no_vars]}
\end{center}
The naming convention for the rule 
is the following: The @{text "1"} expresses that we look at one
 procedure, and @{text NoRec} that the procedure is non
recursive. 
*} 


lemma (in Square_impl)
shows "\<forall>n. \<Gamma>\<turnstile>\<lbrace>\<acute>N = n\<rbrace>  \<acute>R :== PROC Square(\<acute>N) \<lbrace>\<acute>R = n * n\<rbrace>"
txt {* The directive @{text "in"} has the effect that
the context of the locale @{term "Square_impl"} is included to the current
lemma, and that the lemma is added as a fact to the locale, after it is proven. The
next time locale @{term "Square_impl"} is invoked this lemma is immediately available
as fact, which the verification condition generator can use.
*}
apply (hoare_rule HoarePartial.ProcNoRec1)
 txt "@{subgoals[display]}"
 txt {* The method @{text "hoare_rule"}, like @{text "rule"} applies a 
     single rule, but additionally does some ``obvious'' steps:
     It solves the canonical side-conditions of various Hoare-rules and it 
     automatically expands the
     procedure body: With @{thm [source] Square_impl}:  @{thm [names_short] Square_impl [no_vars]} we
     get the procedure body out of the procedure context @{term "\<Gamma>"}; 
     with @{thm [source] Square_body_def}: @{thm [names_short] Square_body_def [no_vars]} we
     can unfold the definition of the body.

     The proof is finished by the vcg and simp.
 *}
txt "@{subgoals[display]}"
by vcg simp

text {* If the procedure is non recursive and there is no specification given, the
verification condition generator automatically expands the body.*}

lemma (in Square_impl) Square_spec: 
shows "\<forall>n. \<Gamma>\<turnstile>\<lbrace>\<acute>N = n\<rbrace>  \<acute>R :== PROC Square(\<acute>N) \<lbrace>\<acute>R = n * n\<rbrace>"
  by vcg simp

text {* An important naming convention is to name the specification as
@{text "<procedure-name>_spec"}. The verification condition generator refers to
this name in order to search for a specification in the theorem database.
*}

subsubsection {* Usage *}


text{* Let us see how we can use procedure specifications. *}
(* FIXME: maybe don't show this at all *)
lemma (in Square_impl)
  shows "\<Gamma>\<turnstile>\<lbrace>\<acute>I = 2\<rbrace> \<acute>R :== CALL Square(\<acute>I) \<lbrace>\<acute>R = 4\<rbrace>"
  txt {* Remember that we have already proven @{thm [source] "Square_spec"} in the locale
  @{text "Square_impl"}. This is crucial for 
  verification condition generation. When reaching a procedure call,
  it looks for the specification (by its name) and applies the
  rule @{thm [source,mode=ParenStmt] HoarePartial.ProcSpec}  
instantiated with the specification
  (as last premise). 
  Before we apply the verification condition generator, let us
  take some time to think of what we can expect.
  Let's look at the specification @{thm [source] Square_spec} again:
  @{thm [display] Square_spec [no_vars]}
  The specification talks about the formal parameters @{term "N"} and 
  @{term R}. The precondition @{term "\<lbrace>\<acute>N = n\<rbrace>"} just fixes the initial
  value of @{text N}.
  The actual parameters are @{term "I"} and @{term "R"}. We 
  have to adapt the specification to this calling context.
  @{term "\<forall>n. \<Gamma>\<turnstile> \<lbrace>\<acute>I = n\<rbrace> \<acute>R :== CALL Square(\<acute>I) \<lbrace>\<acute>R = n * n\<rbrace>"}.
  From the postcondition @{term "\<lbrace>\<acute>R = n * n\<rbrace>"} we 
  have to derive the actual postcondition @{term "\<lbrace>\<acute>R = 4\<rbrace>"}. So
  we gain something like: @{term "\<lbrace>n * n = (4::nat)\<rbrace>"}.
  The precondition is @{term "\<lbrace>\<acute>I = 2\<rbrace>"} and the specification 
  tells us @{term "\<lbrace>\<acute>I = n\<rbrace>"} for the pre-state. So the value of @{term n}
  is the value of @{term I} in the pre-state. So we arrive at
  @{term "\<lbrace>\<acute>I = 2\<rbrace> \<subseteq> \<lbrace>\<acute>I * \<acute>I = 4\<rbrace>"}.
  *}
  apply vcg_step
  txt "@{subgoals[display]}"
  txt {*
  The second set looks slightly more involved:
    @{term "\<lbrace>\<forall>t. \<^bsup>t\<^esup>R = \<acute>I * \<acute>I \<longrightarrow> \<acute>I * \<acute>I = 4\<rbrace>"}, this is an artefact from the
  procedure call rule. Originally @{text "\<acute>I * \<acute>I = 4"} was @{text "\<^bsup>t\<^esup>R = 4"}. Where
  @{term "t"} denotes the final state of the procedure and the superscript notation
  allows to select a component from a particular state. 
  *}
  apply vcg_step
  txt "@{subgoals[display]}"
  by simp
  
text {*
The adaption of the procedure specification to the actual calling 
context is done due to the @{term init}, @{term return} and @{term result} functions 
in the rule @{thm [source] HoarePartial.ProcSpec} (or in the variant 
@{thm [source] HoarePartial.ProcSpecNoAbrupt} which already
incorporates the fact that the postcondition for abrupt termination
is the empty set). For the readers interested in the internals, 
here a version without vcg.
*}
lemma (in Square_impl)
  shows "\<Gamma>\<turnstile>\<lbrace>\<acute>I = 2\<rbrace> \<acute>R :== CALL Square(\<acute>I) \<lbrace>\<acute>R = 4\<rbrace>"
  apply (rule HoarePartial.ProcSpecNoAbrupt [OF _ _ Square_spec])
  txt "@{subgoals[display]}"
  txt {* This is the raw verification condition, 
         It is interesting to see how the auxiliary variable @{term "Z"} is
         actually used. It is unified with @{term n} of the specification and
         fixes the state after parameter passing. 
  *}
  apply simp
  txt "@{subgoals[display]}"
  prefer 2
  apply vcg_step
  txt "@{subgoals[display]}"
  apply (auto intro: ext)
  done



subsubsection {* Recursion *}

text {* We want to define a procedure for the factorial. We first
define a HOL function that calculates it, to specify the procedure later on.
*}

primrec fac:: "nat \<Rightarrow> nat"
where
"fac 0 = 1" |
"fac (Suc n) = (Suc n) * fac n"

(*<*)
lemma fac_simp [simp]: "0 < i \<Longrightarrow>  fac i = i * fac (i - 1)"
  by (cases i) simp_all
(*>*)

text {* Now we define the procedure. *}
procedures
  Fac (N::nat | R::nat) 
  "IF \<acute>N = 0 THEN \<acute>R :== 1
   ELSE \<acute>R :== CALL Fac(\<acute>N - 1);;
        \<acute>R :== \<acute>N * \<acute>R
   FI"
  
text {*
Now let us prove that our implementation of @{term "Fac"} meets its specification. 
*}

lemma (in Fac_impl)
shows "\<forall>n. \<Gamma>\<turnstile> \<lbrace>\<acute>N = n\<rbrace> \<acute>R :== PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac n\<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
txt "@{subgoals[display]}"
apply vcg
txt "@{subgoals[display]}"
apply simp
done

text {* 
Since the factorial is implemented recursively,
the main ingredient of this proof is, to assume that the specification holds for 
the recursive call of @{term Fac} and prove the body correct.
The assumption for recursive calls is added to the context by
the rule @{thm [source] HoarePartial.ProcRec1} 
(also derived from the general rule for mutually recursive procedures):
\begin{center}
@{thm [mode=Rule,mode=ParenStmt] HoarePartial.ProcRec1 [no_vars]}
\end{center}
The verification condition generator infers the specification out of the
context @{term "\<Theta>"} when it encounters a recursive call of the factorial.
*}

subsection {* Global Variables and Heap \label{sec:VcgHeap}*}

text {*
Now we define and verify some procedures on heap-lists. We consider
list structures consisting of two fields, a content element @{term "cont"} and
a reference to the next list element @{term "next"}. We model this by the 
following state space where every field has its own heap.
*}

hoarestate globals_heap =
  "next" :: "ref \<Rightarrow> ref"
  cont :: "ref \<Rightarrow> nat"

text {* It is mandatory to start the state name with `globals'. This is exploited
by the syntax translations to store the components in the @{const globals} part
of the state.
*}

text {* Updates to global components inside a procedure are
always propagated to the caller. This is implicitly done by the
parameter passing syntax translations. 
*}

text {* We first define an append function on lists. It takes two 
references as parameters. It appends the list referred to by the first
parameter with the list referred to by the second parameter. The statespace
of the global variables has to be imported.
*}

procedures (imports globals_heap)
  append(p :: ref, q::ref | p::ref) 
    "IF \<acute>p=Null THEN \<acute>p :== \<acute>q 
     ELSE \<acute>p\<rightarrow>\<acute>next :== CALL append(\<acute>p\<rightarrow>\<acute>next,\<acute>q) FI"

(*<*)
context append_impl
begin
(*>*)
text {*
The difference of a global and a local variable is that global
variables are automatically copied back to the procedure caller.
We can study this effect on the translation of @{term "\<acute>p :== CALL append(\<acute>p,\<acute>q)"}:
*}
(*<*)
declare [[hoare_use_call_tr' = false]]
(*>*)
text {*
@{term [display] "\<acute>p :== CALL append(\<acute>p,\<acute>q)"}
*}
(*<*)
declare [[hoare_use_call_tr' = true]]
end
(*>*)

text {* Below we give two specifications this time.
One captures the functional behaviour and focuses on the
entities that are potentially modified by the procedure, the second one
is a pure frame condition. 
*}



text {* 
The functional specification below introduces two logical variables besides the
state space variable @{term "\<sigma>"}, namely @{term "Ps"} and @{term "Qs"}.
They are universally quantified and range over both the pre-and the postcondition, so 
that we are able to properly instantiate the specification
during the proofs. The syntax @{text "\<lbrace>\<sigma>. \<dots>\<rbrace>"} is a shorthand to fix the current 
state: @{text "{s. \<sigma> = s \<dots>}"}. Moreover @{text "\<^bsup>\<sigma>\<^esup>x"} abbreviates 
the lookup of variable @{text "x"} in the state 
@{text \<sigma>}.  

The approach to specify procedures on lists
basically follows \cite{MehtaN-CADE03}. From the pointer structure
in the heap we (relationally) abstract to HOL lists of references. Then
we can specify further properties on the level of HOL lists, rather then 
on the heap. The basic abstractions are: 

@{thm [display] Path.simps [no_vars]}

@{term [show_types] "Path x h y ps"}: @{term ps} is a list of references that we can obtain
out of the heap @{term h} by starting with the reference @{term x}, following
the references in @{term h} up to the reference @{term y}. 


@{thm [display] List_def [no_vars]}

A list @{term "List p h ps"} is a path starting in @{term p} and ending up
in @{term Null}.
*}


lemma (in append_impl) append_spec1: 
shows "\<forall>\<sigma> Ps Qs. 
  \<Gamma>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {}\<rbrace>  
       \<acute>p :== PROC append(\<acute>p,\<acute>q) 
     \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
txt {* @{subgoals [margin=80,display]} 
Note that @{term "hoare_rule"} takes care of multiple auxiliary variables! 
@{thm [source] HoarePartial.ProcRec1} has only one auxiliary variable, namely @{term Z}. 
But the type of @{term Z} can be instantiated arbitrarily. So @{text "hoare_rule"} 
instantiates @{term Z} with the tuple @{term "(\<sigma>,Ps,Qs)"} and derives a proper variant
of the rule. Therefore @{text "hoare_rule"} depends on the proper quantification of
auxiliary variables!
*}
apply vcg
txt {* @{subgoals [display]} 
For each branch of the @{text IF} statement we have one conjunct to prove. The
@{text THEN} branch starts with @{text "p = Null \<longrightarrow> \<dots>"} and the @{text ELSE} branch
with @{text "p \<noteq> Null \<longrightarrow> \<dots>"}. Let us focus on the @{text ELSE} branch, were the
recursive call to append occurs. First of all we have to prove that the precondition for
the recursive call is fulfilled. That means we have to provide some witnesses for
the lists @{term Psa} and @{term Qsa} which are referenced by @{text "p\<rightarrow>next"} (now
written as @{term "next p"}) and @{term q}. Then we have to show that we can 
derive the overall postcondition from the postcondition of the recursive call. The
state components that have changed by the recursive call are the ones with the suffix
@{text a}, like @{text nexta} and @{text pa}.
*}
apply fastforce
done


text {* If the verification condition generator works on a procedure
call it checks whether it can find a modifies clause in the
context. If one is present the procedure call is simplified before the
Hoare rule @{thm [source] HoarePartial.ProcSpec} is
applied. Simplification of the procedure call means that the ``copy
back'' of the global components is simplified. Only those components
that occur in the modifies clause are actually copied back.  This
simplification is justified by the rule @{thm [source]
HoarePartial.ProcModifyReturn}. 
So after this simplification all global
components that do not appear in the modifies clause are treated
as local variables. *}

text {* We study the effect of the modifies clause on the following 
examples, where we want to prove that @{term "append"} does not change
the @{term "cont"} part of the heap.
*}
lemma (in append_impl)
shows "\<Gamma>\<turnstile> \<lbrace>\<acute>cont=c\<rbrace> \<acute>p :== CALL append(Null,Null) \<lbrace>\<acute>cont=c\<rbrace>" 
proof -
  note append_spec = append_spec1
  show ?thesis
    apply vcg
    txt {* @{subgoals [display]} *}
    txt {* Only focus on the very last line: @{term conta} is the heap component 
      after the procedure call,
      and @{term cont} the heap component before the procedure call. Since
      we have not added the modified clause we do not know that they have
      to be equal. 
      *}
    oops

text {*
We now add the frame condition.
The list in the modifies clause names all global state components that
may be changed by the procedure. Note that we know from the modifies clause
that the @{term cont} parts are not changed. Also a small
side note on the syntax. We use ordinary brackets in the postcondition
of the modifies clause, and also the state components do not carry the
acute, because we explicitly note the state @{term t} here.
*}


lemma (in append_impl) append_modifies:
  shows "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} \<acute>p :== PROC append(\<acute>p,\<acute>q) 
             {t. t may_only_modify_globals \<sigma> in [next]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

text {* We tell the verification condition generator to use only the
modifies clauses and not to search for functional specifications by 
the parameter @{text "spec=modifies"}. It also tries to solve the 
verification conditions automatically. Again it is crucial to name 
the lemma with this naming scheme, since the verfication condition 
generator searches for these names. 
*}

text {* The modifies clause is equal to a state update specification
of the following form. 
*}

lemma (in append_impl) shows "{t. t may_only_modify_globals Z in [next]} 
       = 
       {t. \<exists>next. globals t=update id id next_' (K_statefun next) (globals Z)}"
  apply (unfold mex_def meq_def)
  apply simp
  done

text {* Now that we have proven the frame-condition, it is available within
the locale @{text "append_impl"} and the @{text "vcg"} exploits it.*}

lemma (in append_impl) 
shows "\<Gamma>\<turnstile> \<lbrace>\<acute>cont=c\<rbrace> \<acute>p :== CALL append(Null,Null) \<lbrace>\<acute>cont=c\<rbrace>"
proof -
  note append_spec = append_spec1
  show ?thesis
    apply vcg
    txt {* @{subgoals [display]} *}
    txt {* With a modifies clause present we know that no change to @{term cont}
      has occurred. 
      *}
    by simp
qed
 

text {*
Of course we could add the modifies clause to the functional specification as 
well. But separating both has the advantage that we split up the verification
work. We can make use of the modifies clause before we apply the
functional specification in a fully automatic fashion.
*}
 

text {* 
To prove that a procedure respects the modifies clause, we only need
the modifies clauses of the procedures called in the body. We do not need
the functional specifications. So we can always prove the modifies
clause without functional specifications, but we may need the modifies
clause to prove the functional specifications. So usually the modifies clause is
proved before the proof of the functional specification, so that it can already be used
by the verification condition generator.
*}


 
subsection {* Total Correctness *}

text {* When proving total correctness the additional proof burden to
the user is to come up with a well-founded relation and to prove that
certain states get smaller according to this relation. Proving that a
relation is well-founded can be quite hard. But fortunately there are
ways to construct and stick together relations so that they are
well-founded by construction. This infrastructure is already present
in Isabelle/HOL.  For example, @{term "measure f"} is always well-founded;
the lexicographic product of two well-founded relations is again
well-founded and the inverse image construction @{term "inv_image"} of
a well-founded relation is again well-founded. The constructions are
best explained by some equations:

@{thm in_measure_iff [no_vars]}\\
@{thm in_lex_iff [no_vars]}\\
@{thm in_inv_image_iff [no_vars]}

Another useful construction is @{text "<*mlex*>"} which is a combination
of a measure and a lexicographic product:

@{thm in_mlex_iff [no_vars]}\\
In contrast to the lexicographic product it does not construct a product type.
The state may either decrease according to the measure function @{term f} or the
measure stays the same and the state decreases because of the relation @{term r}.

Lets look at a loop:
*}

lemma (in vars) 
  "\<Gamma>\<turnstile>\<^sub>t \<lbrace>\<acute>M = 0 \<and> \<acute>S = 0\<rbrace>
       WHILE \<acute>M \<noteq> a
       INV \<lbrace>\<acute>S = \<acute>M * b \<and> \<acute>M \<le> a\<rbrace>
       VAR MEASURE a - \<acute>M
       DO \<acute>S :== \<acute>S + b;; \<acute>M :== \<acute>M + 1 OD
       \<lbrace>\<acute>S = a * b\<rbrace>"
apply vcg
txt {* @{subgoals [display]} 
The first conjunct of the second subgoal is the proof obligation that the
variant decreases in the loop body. 
*}
by auto



text {* The variant annotation is preceded by @{text VAR}. The capital @{text MEASURE}
is a shorthand for @{text "measure (\<lambda>s. a - \<^bsup>s\<^esup>M)"}. Analogous there is a capital 
@{text "<*MLEX*>"}.
*}

lemma (in Fac_impl) Fac_spec': 
shows "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t {\<sigma>} \<acute>R :==  PROC Fac(\<acute>N) \<lbrace>\<acute>R = fac \<^bsup>\<sigma>\<^esup>N\<rbrace>"
apply (hoare_rule HoareTotal.ProcRec1 [where r="measure (\<lambda>(s,p). \<^bsup>s\<^esup>N)"])
txt {* In case of the factorial the parameter @{term N} decreases in every call. This
is easily expressed by the measure function. Note that the well-founded relation for
recursive procedures is formally defined on tuples
containing the state space and the procedure name.
*}
txt {* @{subgoals [display]} 
The initial call to the factorial is in state @{term "\<sigma>"}. Note that in the 
precondition @{term "{\<sigma>} \<inter> {\<sigma>'}"}, @{term "\<sigma>'"} stems from the lemma we want to prove
and @{term "\<sigma>"} stems from the recursion rule for total correctness. Both are
synonym for the initial state. To use the assumption in the Hoare context we
have to show that the call to the factorial is invoked on a smaller @{term N} compared
to the initial @{text "\<^bsup>\<sigma>\<^esup>N"}.
*}
apply vcg
txt {* @{subgoals [display]} 
The tribute to termination is that we have to show @{text "N - 1 < N"} in case of
the recursive call.
*}
by simp

lemma (in append_impl) append_spec2:
shows "\<forall>\<sigma> Ps Qs. \<Gamma>\<turnstile>\<^sub>t 
  \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {}\<rbrace>  
       \<acute>p :== PROC append(\<acute>p,\<acute>q) 
  \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
apply (hoare_rule HoareTotal.ProcRec1
           [where r="measure (\<lambda>(s,p). length (list \<^bsup>s\<^esup>p \<^bsup>s\<^esup>next))"])
txt {* In case of the append function the length of the list referenced by @{term p}
decreases in every recursive call.
*}
txt {* @{subgoals [margin=80,display]} *}
apply vcg
apply (fastforce simp add: List_list)
done

text {*
In case of the lists above, we have used a relational list abstraction @{term List}
to construct the HOL lists @{term Ps} and @{term Qs} for the pre- and postcondition.
To supply a proper measure function we use a functional abstraction @{term list}.
The functional abstraction can be defined by means of the relational list abstraction,
since the lists are already uniquely determined by the relational abstraction:

@{thm islist_def [no_vars]}\\
@{thm list_def [no_vars]}

\isacommand{lemma} @{thm List_conv_islist_list [no_vars]}
*}

text {*
The next contrived example is taken from \cite{Homeier-95-vcg}, to illustrate
a more complex termination criterion for mutually recursive procedures. The procedures
do not calculate anything useful.

*}


procedures 
  pedal(N::nat,M::nat) 
  "IF 0 < \<acute>N THEN
     IF 0 < \<acute>M THEN 
       CALL coast(\<acute>N- 1,\<acute>M- 1) FI;;
       CALL pedal(\<acute>N- 1,\<acute>M)
     FI"
  and
 
  coast(N::nat,M::nat) 
  "CALL pedal(\<acute>N,\<acute>M);;
   IF 0 < \<acute>M THEN CALL coast(\<acute>N,\<acute>M- 1) FI"


text {*
In the recursive calls in procedure @{text pedal} the first argument always decreases.
In the body of @{text coast} in the recursive call of @{text coast} the second
argument decreases, but in the call to @{text pedal} no argument decreases. 
Therefore an relation only on the state space is insufficient. We have to
take the procedure names into account, too.
We consider the procedure @{text coast} to be ``bigger'' than @{text pedal}
when we construct a well-founded relation on the product of state space and procedure
names.
*}

ML {* ML_Thms.bind_thm ("HoareTotal_ProcRec2", Hoare.gen_proc_rec @{context} Hoare.Total 2)*}


text {*
  We provide the ML function {\tt gen\_proc\_rec} to
automatically derive a convenient rule for recursion for a given number of mutually
recursive procedures.
*}

 
lemma (in pedal_coast_clique)
shows "(\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t {\<sigma>} PROC pedal(\<acute>N,\<acute>M) UNIV) \<and>
         (\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t {\<sigma>} PROC coast(\<acute>N,\<acute>M) UNIV)"
apply (hoare_rule HoareTotal_ProcRec2 
            [where r= "((\<lambda>(s,p). \<^bsup>s\<^esup>N) <*mlex*>
                           (\<lambda>(s,p). \<^bsup>s\<^esup>M) <*mlex*>
                           measure (\<lambda>(s,p). if p = coast_'proc then 1 else 0))"])
  txt {* We can directly express the termination condition described above with
  the @{text "<*mlex*>"} construction. Either state component @{text N} decreases,
  or it stays the same and @{text M} decreases or this also stays the same, but
  then the procedure name has to decrease.*}
  txt {* @{subgoals [margin=80,display]} *}
apply  simp_all
  txt {* @{subgoals [margin=75,display]} *}
by (vcg,simp)+

text {* We can achieve the same effect without @{text "<*mlex*>"} by using
 the ordinary lexicographic product @{text "<*lex*>"}, @{text "inv_image"} and
 @{text "measure"} 
*}
 
lemma (in pedal_coast_clique)
shows "(\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t {\<sigma>} PROC pedal(\<acute>N,\<acute>M) UNIV) \<and>
         (\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t {\<sigma>} PROC coast(\<acute>N,\<acute>M) UNIV)"
apply (hoare_rule HoareTotal_ProcRec2
          [where r= "inv_image (measure (\<lambda>m. m) <*lex*>
                                        measure (\<lambda>m. m) <*lex*> 
                                        measure (\<lambda>p. if p = coast_'proc then 1 else 0))
                           (\<lambda>(s,p). (\<^bsup>s\<^esup>N,\<^bsup>s\<^esup>M,p))"])
  txt {* With the lexicographic product we construct a well-founded relation on
         triples of type @{typ "(nat\<times>nat\<times>string)"}. With @{term inv_image} we project
         the components out of the state-space and the procedure names to this
         triple.
     *}
  txt {* @{subgoals [margin=75,display]} *}
apply simp_all
by (vcg,simp)+

text {* By doing some arithmetic we can express the termination condition with a single
measure function.
*}

lemma (in pedal_coast_clique) 
shows "(\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t {\<sigma>} PROC pedal(\<acute>N,\<acute>M) UNIV) \<and>
         (\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t {\<sigma>} PROC coast(\<acute>N,\<acute>M) UNIV)"
apply(hoare_rule HoareTotal_ProcRec2
       [where r= "measure (\<lambda>(s,p). \<^bsup>s\<^esup>N + \<^bsup>s\<^esup>M + (if p = coast_'proc then 1 else 0))"])
apply simp_all
txt {* @{subgoals [margin=75,display]} *}
by (vcg,simp,arith?)+


subsection {* Guards *}

text (in vars) {* The purpose of a guard is to guard the {\bf (sub-) expressions} of a
statement against runtime faults. Typical runtime faults are array bound violations,
dereferencing null pointers or arithmetical overflow. Guards make the potential
runtime faults explicit, since the expressions themselves never ``fail'' because 
they are ordinary HOL expressions. To relieve the user from typing in lots of standard
guards for every subexpression, we supply some input syntax for the common
language constructs that automatically generate the guards.
For example the guarded assignment @{text "\<acute>M :==\<^sub>g (\<acute>M + 1) div \<acute>N"} gets expanded to 
guarded command @{term "\<acute>M :==\<^sub>g (\<acute>M + 1) div \<acute>N"}. Here @{term "in_range"} is
uninterpreted by now. 
*}

lemma (in vars) "\<Gamma>\<turnstile>\<lbrace>True\<rbrace> \<acute>M :==\<^sub>g (\<acute>M + 1) div \<acute>N \<lbrace>True\<rbrace>"
apply vcg
txt {* @{subgoals} *}
oops

text {*
The user can supply on (overloaded) definition of @{text "in_range"}
to fit to his needs.

Currently guards are generated for:

\begin{itemize}
\item overflow and underflow of numbers (@{text "in_range"}). For subtraction of
      natural numbers @{text "a - b"} the guard @{text "b \<le> a"} is generated instead
      of @{text "in_range"} to guard against underflows.
\item division by @{text 0}
\item dereferencing of @{term Null} pointers
\item array bound violations
\end{itemize}

Following (input) variants of guarded statements are available:

\begin{itemize}
\item Assignment: @{text "\<dots> :==\<^sub>g \<dots>"}
\item If: @{text "IF\<^sub>g \<dots>"}
\item While: @{text "WHILE\<^sub>g \<dots>"}
\item Call: @{text "CALL\<^sub>g \<dots>"} or @{text "\<dots> :== CALL\<^sub>g \<dots>"}
\end{itemize}
*}

subsection {* Miscellaneous Techniques *}



subsubsection {* Modifies Clause *}

text {* We look at some issues regarding the modifies clause with the example
of insertion sort for heap lists.
*}

primrec sorted:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list  \<Rightarrow> bool"
where
"sorted le [] = True" |
"sorted le (x#xs) = ((\<forall>y\<in>set xs. le x y) \<and> sorted le xs)"

procedures (imports globals_heap)
  insert(r::ref,p::ref | p::ref) 
    "IF \<acute>r=Null THEN SKIP
     ELSE IF \<acute>p=Null THEN \<acute>p :== \<acute>r;; \<acute>p\<rightarrow>\<acute>next :== Null
          ELSE IF \<acute>r\<rightarrow>\<acute>cont \<le> \<acute>p\<rightarrow>\<acute>cont 
               THEN \<acute>r\<rightarrow>\<acute>next :== \<acute>p;; \<acute>p:==\<acute>r
               ELSE \<acute>p\<rightarrow>\<acute>next :== CALL insert(\<acute>r,\<acute>p\<rightarrow>\<acute>next)
               FI
          FI
     FI"

lemma (in insert_impl) insert_modifies:
   "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} \<acute>p :== PROC insert(\<acute>r,\<acute>p) 
        {t. t may_only_modify_globals \<sigma> in [next]}"
  by (hoare_rule HoarePartial.ProcRec1) (vcg spec=modifies)

lemma (in insert_impl) insert_spec:
  "\<forall>\<sigma> Ps . \<Gamma>\<turnstile> 
  \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and> sorted (op \<le>) (map \<acute>cont Ps) \<and> 
      \<acute>r \<noteq> Null \<and> \<acute>r \<notin> set Ps\<rbrace>
    \<acute>p :== PROC insert(\<acute>r,\<acute>p) 
  \<lbrace>\<exists>Qs. List \<acute>p \<acute>next Qs \<and> sorted (op \<le>) (map \<^bsup>\<sigma>\<^esup>cont  Qs) \<and>
        set Qs = insert \<^bsup>\<sigma>\<^esup>r (set Ps) \<and>
        (\<forall>x. x \<notin> set Qs \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
  (*<*)
  apply (hoare_rule HoarePartial.ProcRec1)
  apply vcg
  apply (intro conjI impI)
  apply    fastforce
  apply   fastforce
  apply  fastforce
  apply (clarsimp) 
  apply force
  done
  (*>*)

text {*
In the postcondition of the functional specification there is a small but 
important subtlety. Whenever we talk about the @{term "cont"} part we refer to 
the one of the pre-state.
The reason is that we have separated out the information that @{term "cont"} is not 
modified by the procedure, to the modifies clause. So whenever we talk about unmodified
parts in the postcondition we have to use the pre-state part, or explicitly
state an equality in the postcondition.
The reason is simple. If the postcondition would talk about @{text "\<acute>cont"}
instead of \mbox{@{text "\<^bsup>\<sigma>\<^esup>cont"}}, we get a new instance of @{text "cont"} during
verification and the postcondition would only state something about this
new instance. But as the verification condition generator uses the
modifies clause the caller of @{term "insert"} instead still has the
old @{text "cont"} after the call. Thats the sense of the modifies clause.
So the caller and the specification simply talk about two different things,
without being able to relate them (unless an explicit equality is added to
the specification). 
*}


subsubsection {* Annotations *}

text {*
Annotations (like loop invariants)
are mere syntactic sugar of statements that are used by the @{text "vcg"}.  
Logically a statement with an annotation is
equal to the statement without it. Hence annotations can be introduced by the user
while building a proof:

@{thm [source] HoarePartial.annotateI}: @{thm [mode=Rule] HoarePartial.annotateI [no_vars]} 

When introducing annotations it can easily happen that these mess around with the 
nesting of sequential composition. Then after stripping the annotations the resulting statement
is no longer syntactically identical to original one, only equivalent modulo associativity of sequential composition. The following rule also deals with this case:

@{thm [source] HoarePartial.annotate_normI}: @{thm [mode=Rule] HoarePartial.annotate_normI [no_vars]} 
*}

text_raw {* \paragraph{Loop Annotations} 
\mbox{}
\medskip

\mbox{}
*}

procedures (imports globals_heap)
  insertSort(p::ref| p::ref) 
  where r::ref q::ref in
    "\<acute>r:==Null;;
     WHILE (\<acute>p \<noteq> Null) DO
       \<acute>q :== \<acute>p;;
       \<acute>p :== \<acute>p\<rightarrow>\<acute>next;;
       \<acute>r :== CALL insert(\<acute>q,\<acute>r)
     OD;;
     \<acute>p:==\<acute>r"

lemma (in insertSort_impl) insertSort_modifies: 
  shows
   "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} \<acute>p :== PROC insertSort(\<acute>p) 
    {t. t may_only_modify_globals \<sigma> in [next]}"
apply (hoare_rule HoarePartial.ProcRec1)
apply (vcg spec=modifies)
done




text {* Insertion sort is not implemented recursively here, but with a 
loop. Note that the while loop is not annotated with an invariant in the
procedure definition. The invariant only comes into play during verification.
Therefore we annotate the loop first, before we run the @{text "vcg"}. 
*}

lemma (in insertSort_impl) insertSort_spec:
shows "\<forall>\<sigma> Ps. 
  \<Gamma>\<turnstile> \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<rbrace> 
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
txt {* @{text "\<dots>"} *}
(*<*)
  
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
(*>*)

text {* The method @{text "hoare_rule"} automatically solves the side-condition 
        that the annotated
        program is the same as the original one after stripping the annotations. *}

text_raw {* \paragraph{Specification Annotations} 
\mbox{}
\medskip

\mbox{}
*}



text {*
When verifying a larger block of program text, it might be useful to split up
the block and to prove the parts in isolation. This is especially useful to
isolate loops. On the level of the Hoare calculus
the parts can then be combined with the consequence rule. To automate this
process we introduce the derived command @{term specAnno}, which allows to introduce
a Hoare tuple (inclusive auxiliary variables) in the program text:

@{thm specAnno_def [no_vars]}

The whole annotation reduces to the body @{term "c undefined"}. The
type of the assertions @{term "P"}, @{term "Q"} and @{term "A"} is
@{typ "'a \<Rightarrow> 's set"} and the type of command @{term c} is @{typ "'a \<Rightarrow> ('s,'p,'f) com"}.
All entities formally depend on an auxiliary (logical) variable of type @{typ "'a"}.
The body @{term "c"} formally also depends on this variable, since a nested annotation
or loop invariant may also depend on this logical variable. But the raw body without
annotations does not depend on the logical variable. The logical variable is only
used by the verification condition generator. We express this by defining the
whole @{term specAnno} to be equivalent with the body applied to an arbitrary
variable.

The Hoare rule for @{text "specAnno"} is mainly an instance of the consequence rule:

@{thm [mode=Rule,mode=ParenStmt] HoarePartial.SpecAnno [no_vars]}

The side-condition @{term "\<forall>Z. c Z = c undefined"} expresses the intention of body @{term c}
explained above: The raw body is independent of the auxiliary variable. This
side-condition is solved automatically by the @{text "vcg"}. The concrete syntax for 
this specification annotation is shown in the following example: 
*}

lemma (in vars) "\<Gamma>\<turnstile> {\<sigma>} 
            \<acute>I :== \<acute>M;; 
            ANNO \<tau>. \<lbrace>\<tau>. \<acute>I = \<^bsup>\<sigma>\<^esup>M\<rbrace>
                         \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I 
                        \<lbrace>\<acute>M = \<^bsup>\<tau>\<^esup>N \<and> \<acute>N = \<^bsup>\<tau>\<^esup>I\<rbrace>
           \<lbrace>\<acute>M = \<^bsup>\<sigma>\<^esup>N \<and> \<acute>N = \<^bsup>\<sigma>\<^esup>M\<rbrace>"
txt {* With the annotation we can name an intermediate state @{term \<tau>}. Since the
       postcondition refers to @{term "\<sigma>"} we have to link the information about
       the equivalence of @{text "\<^bsup>\<tau>\<^esup>I"} and @{text "\<^bsup>\<sigma>\<^esup>M"} in the specification in order
       to be able to derive the postcondition.
    *}
apply vcg_step
apply   vcg_step
txt {* @{subgoals [display]} *}
txt {* The first subgoal is the isolated Hoare tuple. The second one is the
       side-condition of the consequence rule that allows us to derive the outermost
       pre/post condition from our inserted specification.
       @{text "\<acute>I = \<^bsup>\<sigma>\<^esup>M"} is the precondition of the specification, 
       The second conjunct is a simplified version of
       @{text "\<forall>t. \<^bsup>t\<^esup>M = \<acute>N \<and> \<^bsup>t\<^esup>N = \<acute>I \<longrightarrow> \<^bsup>t\<^esup>M = \<^bsup>\<sigma>\<^esup>N \<and> \<^bsup>t\<^esup>N = \<^bsup>\<sigma>\<^esup>M"} expressing that the
       postcondition of the specification implies the outermost postcondition.
    *}
apply  vcg
txt {* @{subgoals [display]} *}
apply  simp
apply vcg
txt {* @{subgoals [display]} *}
by simp


lemma (in vars) 
  "\<Gamma>\<turnstile> {\<sigma>} 
  \<acute>I :== \<acute>M;; 
  ANNO \<tau>. \<lbrace>\<tau>. \<acute>I = \<^bsup>\<sigma>\<^esup>M\<rbrace>
    \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I 
    \<lbrace>\<acute>M = \<^bsup>\<tau>\<^esup>N \<and> \<acute>N = \<^bsup>\<tau>\<^esup>I\<rbrace>
  \<lbrace>\<acute>M = \<^bsup>\<sigma>\<^esup>N \<and> \<acute>N = \<^bsup>\<sigma>\<^esup>M\<rbrace>"
apply vcg
txt {* @{subgoals [display]} *}
by simp_all

text {* Note that @{text "vcg_step"} changes the order of sequential composition, to 
allow the user to decompose sequences by repeated calls to @{text "vcg_step"}, whereas
@{text "vcg"} preserves the order.

The above example illustrates how we can introduce a new logical state variable 
@{term "\<tau>"}. You can introduce multiple variables by using a tuple:



*}


lemma (in vars) 
  "\<Gamma>\<turnstile> {\<sigma>} 
   \<acute>I :== \<acute>M;; 
   ANNO (n,i,m). \<lbrace>\<acute>I = \<^bsup>\<sigma>\<^esup>M \<and> \<acute>N=n \<and> \<acute>I=i \<and> \<acute>M=m\<rbrace>
     \<acute>M :== \<acute>N;; \<acute>N :== \<acute>I 
   \<lbrace>\<acute>M = n \<and> \<acute>N = i\<rbrace>
  \<lbrace>\<acute>M = \<^bsup>\<sigma>\<^esup>N \<and> \<acute>N = \<^bsup>\<sigma>\<^esup>M\<rbrace>"
apply vcg
txt {* @{subgoals [display]} *}
by simp_all

text_raw {* \paragraph{Lemma Annotations} 
\mbox{}
\medskip

\mbox{}

*}

text {*
The specification annotations described before split the verification
into several Hoare triples which result in several subgoals. If we
instead want to proof the Hoare triples independently as
separate lemmas we can use the @{text "LEMMA"} annotation to plug together the
lemmas. It
inserts the lemma in the same fashion as the specification annotation.
*}
lemma (in vars) foo_lemma: 
  "\<forall>n m. \<Gamma>\<turnstile> \<lbrace>\<acute>N = n \<and> \<acute>M = m\<rbrace> \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1   
             \<lbrace>\<acute>N = n + 1 \<and> \<acute>M = m + 1\<rbrace>"
  apply vcg
  apply simp
  done

lemma (in vars) 
  "\<Gamma>\<turnstile> \<lbrace>\<acute>N = n \<and> \<acute>M = m\<rbrace> 
       LEMMA foo_lemma 
             \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
       END;; 
       \<acute>N :== \<acute>N + 1 
       \<lbrace>\<acute>N = n + 2 \<and> \<acute>M = m + 1\<rbrace>"
  apply vcg
  apply simp
  done

lemma (in vars)
  "\<Gamma>\<turnstile> \<lbrace>\<acute>N = n \<and> \<acute>M = m\<rbrace> 
           LEMMA foo_lemma 
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
           END;;
           LEMMA foo_lemma 
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
           END
      \<lbrace>\<acute>N = n + 2 \<and> \<acute>M = m + 2\<rbrace>"
  apply vcg
  apply simp
  done

lemma (in vars) 
  "\<Gamma>\<turnstile> \<lbrace>\<acute>N = n \<and> \<acute>M = m\<rbrace> 
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1;;
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
      \<lbrace>\<acute>N = n + 2 \<and> \<acute>M = m + 2\<rbrace>"
  apply (hoare_rule anno= 
          "LEMMA foo_lemma 
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
           END;;
           LEMMA foo_lemma 
              \<acute>N :== \<acute>N + 1;; \<acute>M :== \<acute>M + 1
           END"
          in HoarePartial.annotate_normI)
  apply vcg
  apply simp
  done


subsubsection {* Total Correctness of Nested Loops *}

text {*
When proving termination of nested loops it is sometimes necessary to express that
the loop variable of the outer loop is not modified in the inner loop. To express this
one has to fix the value of the outer loop variable before the inner loop and use this value
in the invariant of the inner loop. This can be achieved by surrounding the inner while loop
with an @{text "ANNO"} specification as explained previously. However, this
leads to repeating the invariant of the inner loop three times: in the invariant itself and
in the the pre- and postcondition of the @{text "ANNO"} specification. Moreover one has
to deal with the additional subgoal introduced by @{text "ANNO"} that expresses how
the pre- and postcondition is connected to the invariant. To avoid this extra specification
and verification work, we introduce an variant of the annotated while-loop, where one can
introduce logical variables by @{text "FIX"}. As for the @{text "ANNO"} specification
multiple logical variables can be introduced via a tuple (@{text "FIX (a,b,c)."}).

The Hoare logic rule for the augmented while-loop is a mixture of the invariant rule for
loops and the consequence rule for @{text "ANNO"}:

\begin{center}
@{thm [mode=Rule,mode=ParenStmt] HoareTotal.WhileAnnoFix' [no_vars]}
\end{center}

The first premise expresses that the precondition implies the invariant and that
the invariant together with the negated loop condition implies the postcondition. Since
both implications may depend on the choice of the auxiliary variable @{term "Z"} these two
implications are expressed in a single premise and not in two of them as for the usual while
rule. The second premise is the preservation of the invariant by the loop body. And the third
premise is the side-condition that the computational part of the body does not depend on
the auxiliary variable. Finally the last premise is the well-foundedness of the variant.
The last two premises are usually discharged automatically by the verification condition
generator. Hence usually two subgoals remain for the user, stemming from the first two
premises.

The following example illustrates the usage of this rule. The outer loop increments the
loop variable @{term "M"} while the inner loop increments @{term "N"}. To discharge the
proof obligation for the termination of the outer loop, we need to know that the inner loop
does not mess around with @{term "M"}. This is expressed by introducing the logical variable
@{term "m"} and fixing the value of @{term "M"} to it.
*}


lemma (in vars) 
  "\<Gamma>\<turnstile>\<^sub>t \<lbrace>\<acute>M=0 \<and> \<acute>N=0\<rbrace> 
      WHILE (\<acute>M < i) 
      INV \<lbrace>\<acute>M \<le> i \<and> (\<acute>M \<noteq> 0 \<longrightarrow> \<acute>N = j) \<and> \<acute>N \<le> j\<rbrace>
      VAR MEASURE (i - \<acute>M)
      DO
         \<acute>N :== 0;;
         WHILE (\<acute>N < j)
         FIX m. 
         INV \<lbrace>\<acute>M=m \<and> \<acute>N \<le> j\<rbrace>
         VAR MEASURE (j - \<acute>N)
         DO
           \<acute>N :== \<acute>N + 1
         OD;;
       \<acute>M :== \<acute>M + 1
       OD
       \<lbrace>\<acute>M=i \<and> (\<acute>M\<noteq>0 \<longrightarrow> \<acute>N=j)\<rbrace>"
apply vcg
txt {* @{subgoals [display]} 

The first subgoal is from the precondition to the invariant of the outer loop.
The fourth subgoal is from the invariant together with the negated loop condition 
of the outer loop to the postcondition. The subgoals two and three are from the body
of the outer while loop which is mainly the inner while loop. Because we introduce the
logical variable @{term "m"} here, the while Rule described above is used instead of the
ordinary while Rule. That is why we end up with two subgoals for the inner loop. Subgoal
two is from the invariant and the loop condition of the outer loop to the invariant
of the inner loop. And at the same time from the invariant of the inner loop to the
invariant of the outer loop (together with the proof obligation that the measure of the
outer loop decreases). The universal quantified variables @{term "Ma"} and @{term "N"} are
the ``fresh'' state variables introduced for the final state of the inner loop. 
The equality @{term "Ma=M"} is the result of the equality @{text "\<acute>M=m"} in the inner 
invariant. Subgoal three is the preservation of the invariant by the
inner loop body (together with the proof obligation that the measure of
the inner loop decreases).
*}
(*<*)
apply    (simp)
apply   (simp,arith)
apply  (simp,arith)
done
(*>*)

subsection {* Functional Correctness, Termination and Runtime Faults *}

text {*
Total correctness of a program with guards conceptually leads to three verification 
tasks.
\begin{itemize}
\item functional (partial) correctness 
\item absence of runtime faults
\item termination
\end{itemize}

In case of a modifies specification the functional correctness part
can be solved automatically. But the absence of runtime faults and
termination may be non trivial.  Fortunately the modifies clause is
usually just a helpful companion of another specification that
expresses the ``real'' functional behaviour. Therefor the task to
prove the absence of runtime faults and termination can be dealt with
during the proof of this functional specification. In most cases the
absence of runtime faults and termination heavily build on the
functional specification parts.  So after all there is no reason why
we should again prove the absence of runtime faults and termination
for the modifies clause. Therefor it suffices to have partial
correctness of the modifies clause for a program were all guards are
ignored.  This leads to the following pattern: *}



procedures foo (N::nat|M::nat) 
  "\<acute>M :== \<acute>M 
   (* think of body with guards instead *)"

  foo_spec: "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^sub>t (P \<sigma>) \<acute>M :== PROC foo(\<acute>N) (Q \<sigma>)"
  foo_modifies: "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} \<acute>M :== PROC foo(\<acute>N) 
                   {t. t may_only_modify_globals \<sigma> in []}"

text {*
The verification condition generator can solve those modifies clauses automatically
and can use them to simplify calls to @{text foo} even in the context of total
correctness.
*}

subsection {* Procedures and Locales \label{sec:Locales}*}



text {*
Verification of a larger program is organised on the granularity of procedures. 
We proof the procedures in a bottom up fashion.  Of course you can also always use Isabelle's
dummy proof @{text "sorry"} to prototype your formalisation. So you can write the
theory in a bottom up fashion but actually prove the lemmas in any other order.
 
Here are some explanations of handling of locales. In the examples below, consider
@{text proc\<^sub>1} and @{text proc\<^sub>2} to be ``leaf'' procedures, which do not call any 
other procedure.
Procedure @{text "proc"} directly calls @{text proc\<^sub>1} and @{text proc\<^sub>2}.

\isacommand{lemma} (\isacommand{in} @{text "proc\<^sub>1_impl"}) @{text "proc\<^sub>1_modifies"}:\\
\isacommand{shows} @{text "\<dots>"} 

After the proof of @{text "proc\<^sub>1_modifies"}, the \isacommand{in} directive  
stores the lemma in the
locale @{text "proc\<^sub>1_impl"}. When we later on include @{text "proc\<^sub>1_impl"} or prove 
another theorem in locale @{text "proc\<^sub>1_impl"} the lemma @{text "proc\<^sub>1_modifies"}
will already be available as fact.

\isacommand{lemma} (\isacommand{in} @{text "proc\<^sub>1_impl"}) @{text "proc\<^sub>1_spec"}:\\
\isacommand{shows} @{text "\<dots>"} 

\isacommand{lemma} (\isacommand{in} @{text "proc\<^sub>2_impl"}) @{text "proc\<^sub>2_modifies"}:\\
\isacommand{shows} @{text "\<dots>"} 

\isacommand{lemma} (\isacommand{in} @{text "proc\<^sub>2_impl"}) @{text "proc\<^sub>2_spec"}:\\
\isacommand{shows} @{text "\<dots>"} 


\isacommand{lemma} (\isacommand{in} @{text "proc_impl"}) @{text "proc_modifies"}:\\
\isacommand{shows} @{text "\<dots>"} 

Note that we do not explicitly include anything about @{text "proc\<^sub>1"} or  
@{text "proc\<^sub>2"} here. This is handled automatically. When defining
an @{text impl}-locale it imports all @{text impl}-locales of procedures that are
called in the body. In case of @{text "proc_impl"} this means, that @{text "proc\<^sub>1_impl"}
and @{text "proc\<^sub>2_impl"} are imported. This has the neat effect that all theorems that
are proven in @{text "proc\<^sub>1_impl"} and @{text "proc\<^sub>2_impl"} are also present
in @{text "proc_impl"}.

\isacommand{lemma} (\isacommand{in} @{text "proc_impl"}) @{text "proc_spec"}:\\
\isacommand{shows} @{text "\<dots>"} 

As we have seen in this example you only have to prove a procedure in its own
@{text "impl"} locale. You do not have to include any other locale. 
*}

subsection {* Records \label{sec:records}*}

text {*
Before @{term "statespaces"} where introduced the state was represented as a @{term "record"}.
This is still supported. Compared to the flexibility of statespaces there are some drawbacks
in particular with respect to modularity. Even names of local variables and 
parameters are globally visible and records can only be extended in a linear fashion, whereas
statespaces also allow multiple inheritance. The usage of records is quite similar to the usage of statespaces. 
We repeat the example of an append function for heap lists.
First we define the global components. 
Again the appearance of the prefix `globals' is mandatory. This is the way the syntax layer distinguishes local and global variables.  
*}
record globals_list = 
  next_' :: "ref \<Rightarrow> ref"
  cont_' :: "ref \<Rightarrow> nat"


text {* The local variables also have to be defined as a record before the actual definition
of the procedure. The parent record @{text "state"} defines a generic @{term "globals"}
field as a place-holder for the record of global components. In contrast to the
statespace approach there is no single @{term "locals"} slot. The local components are
just added to the record.
*}
record 'g list_vars = "'g state" +
  p_'    :: "ref"
  q_'    :: "ref"
  r_'    :: "ref"
  root_' :: "ref"
  tmp_'  :: "ref"

text {* Since the parameters and local variables are determined by the record, there are
no type annotations or definitions of local variables while defining a procedure.
*}

procedures
  append'(p,q|p) = 
    "IF \<acute>p=Null THEN \<acute>p :== \<acute>q 
     ELSE \<acute>p \<rightarrow>\<acute>next:== CALL append'(\<acute>p\<rightarrow>\<acute>next,\<acute>q) FI"

text {* As in the statespace approach, a locale called @{text "append'_impl"} is created.
Note that we do not give any explicit information which global or local state-record to use.
Since the records are already defined we rely on Isabelle's type inference. 
Dealing with the locale is analogous to the case with statespaces.
*}

lemma (in append'_impl) append'_modifies: 
  shows
   "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>} \<acute>p :== PROC append'(\<acute>p,\<acute>q)
        {t. t may_only_modify_globals \<sigma> in [next]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

lemma (in append'_impl) append'_spec:
  shows "\<forall>\<sigma> Ps Qs. \<Gamma>\<turnstile> 
            \<lbrace>\<sigma>. List \<acute>p \<acute>next Ps \<and>  List \<acute>q \<acute>next Qs \<and> set Ps \<inter> set Qs = {}\<rbrace>
                \<acute>p :== PROC append'(\<acute>p,\<acute>q) 
            \<lbrace>List \<acute>p \<acute>next (Ps@Qs) \<and> (\<forall>x. x\<notin>set Ps \<longrightarrow> \<acute>next x = \<^bsup>\<sigma>\<^esup>next x)\<rbrace>"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply vcg
  apply fastforce
  done


text {*
However, in some corner cases the inferred state type in a procedure definition 
can be too general which raises problems when  attempting to proof a suitable 
specifications in the locale.
Consider for example the simple procedure body @{term "\<acute>p :== NULL"} for a procedure
@{text "init"}. 
*}

procedures init (|p) = 
  "\<acute>p:== Null"


text {*
Here Isabelle can only
infer the local variable record. Since no reference to any global variable is
made the type fixed for the global variables (in the locale @{text "init'_impl"}) is a 
type variable say @{typ "'g"} and not a @{term "globals_list"} record. Any specification
mentioning @{term "next"} or @{term "cont"} restricts the state type and cannot be
added to the locale @{text "init_impl"}. Hence we have to restrict the body
@{term "\<acute>p :== NULL"} in the first place by adding a typing annotation:
*}

procedures init' (|p) = 
  "\<acute>p:== Null::(('a globals_list_scheme, 'b) list_vars_scheme, char list, 'c) com"


subsubsection {* Extending State Spaces *}
text {*
The records in Isabelle are
extensible \cite{Nipkow-02-hol,NaraschewskiW-TPHOLs98}. In principle this can be exploited 
during verification. The state space can be extended while we we add procedures.
But there is one major drawback:
\begin{itemize}
  \item records can only be extended in a linear fashion (there is no multiple inheritance)
\end{itemize}

You can extend both the main state record as well as the record for the global variables.
*}

subsubsection {* Mapping Variables to Record Fields *}

text {*
Generally the state space (global and local variables) is flat and all components
are accessible from everywhere. Locality or globality of variables is achieved by
the proper @{text "init"} and @{text "return"}/@{text "result"} functions in procedure
calls. What is the best way to map programming language variables to the state records?
One way is to disambiguate all names, by using the procedure names as prefix or the
structure names for heap components. This leads to long names and lots of 
record components. But for local variables this is not necessary, since
variable @{term i} of procedure @{term A} and variable @{term "i"} of procedure @{term B}
can be mapped to the same record component, without any harm, provided they have the
same logical type. Therefor for local variables it is preferable to map them per type. You
only have to distinguish a variable with the same name if they have a different type.
Note that all pointers just have logical type @{text "ref"}. So you even do not
have to distinguish between a  pointer @{text p} to a integer and a pointer @{text p} to
a list.
For global components (global variables and heap structures) you have to disambiguate the
name. But hopefully the field names of structures have different names anyway.
Also note that there is no notion of hiding of a global component by a local one in
the logic. You have to disambiguate global and local names!
As the names of the components show up in the specifications and the
proof obligations, names are even more important as for programming. Try to
find meaningful and short names, to avoid cluttering up your reasoning.
*}

(*<*)
text {*
in locales, includes, spec or impl?
Names: per type not per procedure\<dots>
downgrading total to partial\<dots>
*}
(*>*)
text {**}
(*<*)
end
(*>*)
