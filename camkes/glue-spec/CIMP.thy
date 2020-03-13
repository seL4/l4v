(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
chapter \<open>Concurrent Imperative Syntax and Semantics \label{s:cimp}\<close>
(*<*)
theory CIMP
imports Main
begin
(*>*)
text \<open>
  This chapter introduces a small concurrent imperative language with synchronous
  message passing. The sequential part of the language is a standard, minimal, Turing-complete
  While-language. It is sufficient to express the semantics of \camkes glue code and
  the behaviour of small trusted components. It can be extended easily with procedures and
  other programming language concepts in standard ways if the behaviour of larger trusted
  components needs to be described. For this document, we concentrate on the ADL and glue
  code
  semantics and keep the language as simple as possible.

  The message passing mechanism is a slight variation of standard synchronous message
  passing instructions \texttt{send} and \texttt{receive} that would map directly to
  seL4 synchronous IPC. The standard mechanism in labelled transition systems would identify
  the message with a message label and potentially a payload. In our setting, we extend this
  concept slightly to the instructions @{text Request} and @{text Receive} that come with two
  labels, one for a question and one for the corresponding answer that is provided in the same
  execution step. The standard mechanism can be obtained simply by leaving out answers, e.g.\ by
  setting the answer type to @{typ unit}.

  We additionally allow these messages to depend on the state when they are sent as a question
  and to modify the local state to store the content of an answer.

  This variation allows us to conveniently
  use the same mechanism for modelling memory for instance, where the
  response from memory is instantaneous, or to model asynchronous messages, where the effect is
  simply to store the message in a buffer.

  Below follows the datatype for sequential commands in the language. We first define the type
  of (shallowly embedded) boolean expressions to be a function from the state @{typ 's} to
  @{typ bool}.
\<close>
type_synonym 's bexp = "'s \<Rightarrow> bool"

text \<open>
  The type of sequential commands itself is parameterised by a type @{typ 'a} for answers, a type
  @{typ 'q} for questions, and the type @{typ 's} for the state of the program.

  The alternatives of the data type are the usual:
  \begin{itemize}
  \item  Skip, which does nothing,
  \item a local operation that can model any function on the local state @{typ 's},
        such as a variable assignment for instance,
  \item standard sequential composition,
  \item standard if-then-else,
  \item standard while loops with a boolean expression and a body,
  \item binary non-deterministic choice,
  \item message sending (request),
  \item and finally message receiving (response).
  \end{itemize}

  In Isabelle, this is:
\<close>
datatype ('a, 'q, 's) com
  = Skip  ("SKIP")
  | LocalOp "'s \<Rightarrow> 's set"
  | Seq "('a,  'q, 's) com" "('a,  'q, 's) com"
    (infixr ";;"  60)
  | If "'s bexp" "('a,  'q, 's) com" "('a,  'q, 's) com"
    ("(IF _/ THEN _/ ELSE _)"  [0, 61] 61)
  | While "'s bexp" "('a,  'q, 's) com"
    ("(WHILE _/ DO _)"  [0, 61] 61)
  | Choose "('a,  'q, 's) com" "('a,  'q, 's) com"
    (infixl "\<squnion>" 20)
  | Request "'s \<Rightarrow> 'q set" "'a \<Rightarrow> 's \<Rightarrow> 's set"
  | Response "'q \<Rightarrow> 's \<Rightarrow> ('s \<times> 'a) set"

text \<open>
For notational convenience we introduce infinite loops as an
abbreviation. They are for instance used in event handling loops.
\<close>
abbreviation
  LOOP_syn ("LOOP/ _")
where
  "LOOP c \<equiv> WHILE (\<lambda>_. True) DO c"

text\<open>
  After the sequential part, we are now ready to define the
  externally-visible communication behaviour of a process.

  A process can make three kinds of labelled steps: internal $\tau$ steps,
  message sends, and message receives. Both of the latter are annotated
  with the action/payload of both the request and instantaneous response
  (if any) of that message.
\<close>
datatype ('a, 'q) seq_label
  = SL_Internal ("\<tau>")
  | SL_Send 'q 'a ("\<guillemotleft>_, _\<guillemotright>")
  | SL_Receive 'q 'a ("\<guillemotright>_, _\<guillemotleft>")

text \<open>
  The following inductive definition now gives the small-step or structural
  operational semantics of the sequential part of the language. The semantics judgment
  is a relation between configurations, labels, and follow-on configurations.
  A configuration consists, as is usual in such settings, of a command and local state @{typ 's}.

  The two interesting
  rules are at the top: a @{term "Request action val"} command can make a step labelled
  as @{term "\<guillemotleft>\<alpha>, \<beta>\<guillemotright>"} from state @{term s} to @{text s'} if @{text \<alpha>} is one of the
  actions that is enabled by @{text action} in state @{term s}, and if @{text val}
  extracts @{term s'} from the response @{text \<beta>} in @{text s}. Similarly, a
  @{term "Response action"} command progresses from @{text s} to @{text s'} with label
  @{term "\<guillemotright>\<alpha>, \<beta>\<guillemotleft>"} if @{term \<beta>} is among the possible responses for the
  request @{term "\<alpha>"}, and if @{text s'} is in the possible successor states after
  potentially extracting @{term \<alpha>}'s payload into the local state.

  The other rules are a standard small-step semantics for a minimal nondeterministic
  imperative language. Local and terminating steps produce @{text \<tau>} transitions, all
  other labels are passed through appropriately.
\<close>
inductive small_step ::
  "('a,  'q, 's) com \<times> 's \<Rightarrow> ('a, 'q) seq_label \<Rightarrow>
   ('a,  'q, 's) com \<times> 's \<Rightarrow> bool"
  ("_ \<rightarrow>\<^bsub>_\<^esub> _" [55, 0, 56] 55)
where
  Request:
  "\<lbrakk> \<alpha> \<in> action s; s' \<in> val \<beta> s \<rbrakk> \<Longrightarrow>
  (Request action val, s) \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> (SKIP, s')"
| Response:
  "(s', \<beta>) \<in> action \<alpha> s \<Longrightarrow> (Response action, s) \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> (SKIP, s')"

| LocalOp:
  "s' \<in> R s \<Longrightarrow> (LocalOp R, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (SKIP, s')"

| Seq1:
  "(c\<^sub>1, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (SKIP, s') \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>2, s')"
| Seq2:
  "\<lbrakk> (c\<^sub>1, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>1', s'); c\<^sub>1' \<noteq> SKIP \<rbrakk> \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>1';; c\<^sub>2, s')"

| IfTrue:
  "\<lbrakk> b s; (c\<^sub>1, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>1', s') \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>1', s')"
| IfFalse:
  "\<lbrakk> \<not> b s; (c\<^sub>2, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>2', s') \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>2', s')"

| WhileTrue:
  "\<lbrakk> b s; (c, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c', s') \<rbrakk> \<Longrightarrow>
  (WHILE b DO c, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c';; WHILE b DO c, s')"
| WhileFalse:
  "\<not> b s \<Longrightarrow> (WHILE b DO c, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (SKIP, s)"

| Choose1:
  "(c\<^sub>1, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>1', s') \<Longrightarrow> (c\<^sub>1 \<squnion> c\<^sub>2, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>1', s')"
| Choose2:
  "(c\<^sub>2, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>2', s') \<Longrightarrow> (c\<^sub>1 \<squnion> c\<^sub>2, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (c\<^sub>2', s')"

text\<open>
  Note that the generic nature of the @{const LocalOp} command lets us choose the
  atomicity of local actions as appropriate for the language. Since we are in a message
  passing setting, the atomicity of internal @{term \<tau>} actions is not important for
  the generation of verification conditions.

  With the semantics for the sequential part, we can now define composition of sequential
  processes into systems.

  For this purpose, we define the global state of a component system as a function from
  process names @{typ 'proc} to configurations. The type @{typ 'proc} will later be instantiated
  with a type that enumerates precisely all process names in the system.
\<close>
type_synonym ('a, 'proc, 'q, 's) global_state =
  "'proc \<Rightarrow> (('a, 'q, 's) com \<times> 's)"

text\<open>
  With this, we can now define an execution step of the overall system as either
  any enabled internal @{term \<tau>} step of any process, or as a communication step
  between two processes. For such a communication step to occur, two different
  processes @{term "p\<^sub>1"} and @{term "p\<^sub>2"} must be ready to execute a request/response
  pair with matching labels @{term \<alpha>} and @{term \<beta>}.
\<close>
inductive
  system_step ::
  "('a, 'proc, 'q, 's) global_state \<Rightarrow> ('a, 'proc, 'q, 's) global_state \<Rightarrow> bool"
  ("_ \<rightarrow> _" [55, 56] 55)
where
  LocalStep:
  "\<lbrakk> gs p \<rightarrow>\<^bsub>\<tau>\<^esub> c'; gs' = gs(p := c') \<rbrakk> \<Longrightarrow> gs \<rightarrow> gs'"
| CommunicationStep:
  "\<lbrakk>gs p\<^sub>1 \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> c\<^sub>1'; gs p\<^sub>2 \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> c\<^sub>2'; p\<^sub>1 \<noteq> p\<^sub>2;
    gs' = gs(p\<^sub>1 := c\<^sub>1', p\<^sub>2 := c\<^sub>2') \<rbrakk>
  \<Longrightarrow> gs \<rightarrow> gs'"

text \<open>
  From this point, we could go on to provide the usual definitions of finite and infinite
  execution traces and properties on these, depending on which flavour of properties
  are desired for a specific verification (e.g. invariants, safety, liveness).
  For the purposes of defining the glue-code
  semantics we only need the one-step execution, and can therefore leave open which expressive
  power is desired on top of this semantic structure.

  This concludes the definition of the small concurrent imperative base language.
  In the following, we use this language to express the high-level semantics of \camkes ADL glue
  code as it maps to the seL4 microkernel.
\<close>
(*<*)
end
(*>*)

