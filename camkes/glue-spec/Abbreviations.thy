(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
chapter \<open>\label{h:abbreviations}Convenience Definitions\<close>

(*<*)
theory Abbreviations
imports Types
begin
(*>*)

text \<open>
  This section defines static functionality that the generated glue code
  semantics relies on. It provides the basic building blocks for the
  \camkes communication mechanisms. They can also be used as building blocks
  for users describing the behaviour of trusted components.
\<close>

subsection \<open>\label{sec:componentlocal}Local Component Operations\<close>

subsubsection \<open>\label{ssec:univc}UNIV$_c$\<close>
text \<open>
  The set of all possible states a component can be in. This is
  essentially any local state with the exception of the states
  representing events and shared memory.
\<close>
definition
  UNIV\<^sub>c :: "'component_state local_state set"
where
  "UNIV\<^sub>c \<equiv> {x. case x of Component _ \<Rightarrow> True | _ \<Rightarrow> False}"

subsubsection \<open>\label{ssec:internal}Internal Step\<close>
text \<open>
  An internal step in a component that arbitrarily modifies its own local
  state. Note that it is not possible for an event or shared memory component
  to take this step.
\<close>
definition
  internal :: "'component_state local_state \<Rightarrow>
    'component_state local_state set"
where
  "internal s \<equiv> case s of Component _ \<Rightarrow> UNIV\<^sub>c | _ \<Rightarrow> {}"

subsubsection \<open>\label{ssec:userstep}User Steps\<close>
text \<open>
  A representation of @{term internal} in the concurrent imperative language.
  That is, an arbitrary local step.
\<close>
definition
  UserStep :: "('channel, 'component_state) comp"
where
  "UserStep \<equiv> LocalOp internal"

subsection \<open>\label{sec:componentcommunication}Communication Component Operations\<close>

subsubsection \<open>\label{ssec:discard}Discard Messages\<close>
text \<open>
  Receive a @{term Void} message and do nothing in reaction.
\<close>
definition
  discard :: "'channel answer \<Rightarrow> 'component_state local_state \<Rightarrow>
    'component_state local_state set"
where
  "discard a s \<equiv> if a_data a = Void then {s} else {}"

subsubsection \<open>\label{ssec:arbitraryrequest}Arbitrary Requests\<close>
text \<open>
  Non-deterministically send any message on a given channel. This provides a
  way of specifying unconstrained behaviour of a component given access to a
  particular channel. The command produces the set of all messages on a given
  channel as possible questions and receives any response with a fully
  nondeterministic local state update.
\<close>
definition
  ArbitraryRequest :: "'channel \<Rightarrow> ('channel, 'component_state) comp"
where
  "ArbitraryRequest c \<equiv> Request (\<lambda>_. {x. q_channel x = c}) (\<lambda>_ _. UNIV\<^sub>c)"

subsubsection \<open>\label{ssec:arbitraryresponse}Arbitrary Responses\<close>
text \<open>
  Non-deterministically receive any message on a given channel. The
  command receives any message, makes a nondeterministic local state
  update, and returns the set of all possible responses @{text \<beta>} on
  the given channel.
\<close>
definition
  ArbitraryResponse :: "'channel \<Rightarrow> ('channel, 'component_state) comp"
where
  "ArbitraryResponse c \<equiv>
    Response (\<lambda>_ _. {(s',\<beta>). s' \<in> UNIV\<^sub>c \<and> a_channel \<beta> = c})"

subsubsection \<open>\label{ssec:eventemit}Event Emit\<close>
text \<open>
  Emit an event. The command sends the message @{const Set} on the
  given channel and discards any response to model asynchronous behaviour
  with respect to the event buffer components. The message is independent of
  the local state @{text s}.
\<close>
definition
  EventEmit :: "'channel \<Rightarrow> ('channel, 'component_state) comp"
where
  "EventEmit c \<equiv> Request (\<lambda>s. {\<lparr>q_channel = c, q_data = Set\<rparr>}) discard"

subsubsection \<open>\label{ssec:eventpoll}Event Poll\<close>
text \<open>
  Poll for a pending event from an asynchronous buffer component.
  The command sends a @{const Poll} message to the buffer component, and
  expects a message @{term a} back that has the form @{term "Pending b"}
  with a boolean payload @{term b}. This payload is embedded in the local
  state of the component using the user-provided function @{text embed_data}.
\<close>
definition
  EventPoll :: "'channel \<Rightarrow>
    ('component_state local_state \<Rightarrow> bool \<Rightarrow> 'component_state local_state) \<Rightarrow>
    ('channel, 'component_state) comp"
where
  "EventPoll c embed_data \<equiv>
    Request (\<lambda>_. {\<lparr>q_channel = c, q_data = Poll\<rparr>})
            (\<lambda>a s. case a_data a of Pending b \<Rightarrow> {embed_data s b} | _ \<Rightarrow> {})"

subsubsection \<open>\label{ssec:eventwait}Event Wait\<close>
text \<open>
  Wait for a pending event. The command takes
  a channel @{text c}, and embedding function @{text embed} (see above).
  Because the set of target states is only non-empty when the pending bit of
  the polled event is set, this has the effect of blocking the component's
  execution until the event is available.
\<close>
definition
  EventWait :: "'channel \<Rightarrow>
    ('component_state local_state \<Rightarrow> bool \<Rightarrow> 'component_state local_state) \<Rightarrow>
    ('channel, 'component_state) comp"
where
  "EventWait c embed_data \<equiv>
    Request (\<lambda>_. {\<lparr>q_channel = c, q_data = Poll\<rparr>})
            (\<lambda>a s. case a_data a of Pending b \<Rightarrow> if b then {embed_data s b} else {}
                                  | _ \<Rightarrow> {})"

subsubsection \<open>\label{ssec:memoryread}Memory Read\<close>
text \<open>
  Read from a shared memory location. As mentioned above, shared memory is modelled
  as a separate process in our glue code semantics. The command below issues
  a @{const Read} request message to this process with a specified address, and expects
  an immediate response of the form @{term "Value v"} back, which is embedded into
  the local state with the same mechanism as above.
\<close>
definition
  MemoryRead :: "'channel \<Rightarrow>
    ('component_state local_state \<Rightarrow> nat) \<Rightarrow>
    ('component_state local_state \<Rightarrow> variable \<Rightarrow> 'component_state local_state) \<Rightarrow>
    ('channel, 'component_state) comp"
where
  "MemoryRead c addr embed_data \<equiv>
    Request (\<lambda>s. {\<lparr>q_channel = c, q_data = Read (addr s)\<rparr>})
            (\<lambda>a s. case a_data a of Value v \<Rightarrow> {embed_data s v} | _ \<Rightarrow> {})"

subsubsection \<open>\label{ssec:memorywrite}Memory Write\<close>
text \<open>
  Write to a shared memory location. The command sends a @{const Write} message to
  the memory component with specified address and value (which are extracted from the local state)
  and does not expect a response.
\<close>
definition
  MemoryWrite :: "'channel \<Rightarrow> ('component_state local_state \<Rightarrow> nat) \<Rightarrow>
    ('component_state local_state \<Rightarrow> variable) \<Rightarrow>
    ('channel, 'component_state) comp"
where
  "MemoryWrite c addr val \<equiv>
    Request (\<lambda>s. {\<lparr>q_channel = c, q_data = Write (addr s) (val s)\<rparr>}) discard"

text \<open>
 This concludes the list of the basic operations from which the glue code is
 composed. We now proceed to
 define the intermediate communication components for events and shared memory.

\<close>
(*<*)
end
(*>*)
