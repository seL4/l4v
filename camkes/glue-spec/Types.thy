(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
chapter \<open>\label{h:types}Datatypes\<close>

(*<*)
theory Types
imports CIMP
begin
(*>*)

text \<open>
This chapter builds up the basic data types that are necessary to cast
\camkes glue code in terms of the concurrent imperative language. In particular,
we define
data types for the kinds of variables glue code interacts with, the type
of messages that \camkes components send and receive, the local state of
components, the resulting type of components and finally the partially
instantiated, but still generic, global state of a component system.

\<close>
subsection \<open>\label{sec:messages}Messages\<close>
text \<open>
  Processes communicate via messages, which represent IPC payloads in seL4. The
  only message operations performed in a CAmkES system are initiated by the
  glue code. Variable data contained in messages are represented using the
  following data type. This is conceptually equivalent to @{term param_type}
  from the ADL model, with a value attached.
\<close>

datatype variable
  = Boolean bool
  | Char char
  | Integer int
  | Number nat
  | String string
  | Array "variable list"

text \<open>
  Messages are sent from one process to another as questions and
  acknowledged with answers. Communication with function call semantics
  -- `procedures' in CAmkES terminology -- is represented by a sequence of two
  transmissions; a call and the return. The call message takes a @{term nat}
  parameter that is an index indicating which method of the relevant procedure
  is being invoked. The variable list of a call message contains all the input
  parameters, while the variable list of a return message contains the return
  value, if there is one, and the output parameters.

  Event and shared memory connections are modelled using an intermediate
  component. This is explained in more detail in \autoref{h:connector}.
\<close>

datatype question_data
   \<comment> \<open>Inter-component questions\<close>
  = Call nat "variable list"
  | Return "variable list"
   \<comment> \<open>Questions from components to events\<close>
  | Set
  | Poll
   \<comment> \<open>Questions from components to shared memory\<close>
  | Read nat
  | Write nat variable

datatype answer_data
   \<comment> \<open>Answers from events to components\<close>
  = Pending bool
   \<comment> \<open>Answers from shared memory to components\<close>
  | Value variable
   \<comment> \<open>An answer that conveys no information\<close>
  | Void

record ('channel) question =
  q_channel :: 'channel
  q_data :: question_data

record ('channel) answer =
  a_channel :: 'channel
  a_data :: answer_data

text \<open>
  Message transmission is accomplished using a matching pair of @{term Request}
  and @{term Response} actions. This correspondence arises from using the same
  channel in a @{term question} and @{term answer}. A channel in this
  representation corresponds to a connection in the implementation.
\<close>

subsection \<open>\label{sec:lstate}Local State\<close>
text \<open>
  In this section we define the local state of components. There are three
  kinds of components: user-defined, event buffers, and shared memory.

  We keep the local state of a component parameterised to allow the user to
  represent as much (or as little) of the concrete state of a component as
  appropriate for a specific verification. If the local state of a component
  is not relevant to our current aim, it can be instantiated with @{term
  unit}.

  As mentioned, communication channels involving
  events and shared memory are modelled using an intermediate component with
  its own local state. For events, the intermediate component has a single bit
  of state indicating whether there is a pending signal or not. This is
  consistent with the desired semantics of the implementation, that emitting an
  event
  that is already pending has no effect.

  The local state of a shared memory component is a mapping from address offsets
  (or indicies) to
  variable values. At this level of abstraction, every shared memory region is
  considered infinite and all operations on the region are represented as
  manipulations of well-defined types. There is no loss of expressiveness here
  as raw byte accesses can be represented by mapping each offset to a
  @{term variable} of subtype @{term Number}.
\<close>

datatype 'component_state local_state
  = Component 'component_state
  | Event bool
  | Memory "(nat, variable) map"

subsection \<open>\label{sec:components}Components\<close>
text \<open>
  We model each component in the system as a process. The type itself
  is only partially instantiated to let the type representing the local state
  of a component be stated more precisely later as described above.
\<close>

type_synonym ('channel, 'component_state) comp =
  "('channel answer, 'channel question, 'component_state local_state) com"

subsection \<open>\label{sec:gstate}Global State\<close>
text \<open>
  The global state of a system is a mapping from component instance identifiers
  to a pair of component (i.e. program text) and local state. The global state
  and local state types are parameterised with general types so they
  can be instantiated to specifically apply to a given system. During
  generation, a global state is derived that covers all component
  instances; that is, the generated global state is total.
\<close>

type_synonym ('inst, 'channel, 'component_state) global_state =
  "('inst, ('channel, 'component_state) comp \<times>
    'component_state local_state) map"

(*<*)
end
(*>*)
