(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)
chapter {* \label{h:connector}Connector Components *}

(*<*)
theory Connector
imports Abbreviations
begin
(*>*)

text {*
  As mentioned in previous sections, we represent events and shared memory 
  as components. These connector components, unlike the component instances in
  the system, \emph{always} have a well-defined, constrained execution because
  they are effectively implemented by the kernel. This section outlines the definition
  of the program text and local state of these components.
  
  The semantics of small steps in the concurrent imperative language
  are such that a request and a response
  can only correspond and allow a global state transition when the question and
  answer match. Additionally, all communication between component instances and
  connector components is atomic, in the sense that they involve a single
  global transition consisting of a single request-response pair. The
  implication of this is that an untrusted component cannot disrupt the
  execution of an event or shared memory component causing it to stop
  responding to other components. Untrusted component definitions may contain
  unsafe transitions involving malformed messages, but these transitions can
  never be taken in a global step because there is no corresponding unsafe step
  in the connector component definition.
*}

subsection {* \label{ssec:eventcomponents}Event Components *}
text {*
  We represent a \camkes event connector as a component always listening for @{term Set} or
  @{term Poll} questions that then simultaneously responds with the relevant
  answer. In particular, the local state is expected to be of the form @{term "Event s"},
  and the component listens to messages of the form @{const Set} or @{const Poll}. No other
  messages are enabled. If a @{const Set} is received, the local state becomes @{term "Event True"},
  and the response back is @{const Void}. If the message is @{const Poll}, the local event
  state is cleared, and the response message contains the previous event state @{term s}.
*}
definition
  event :: "'channel \<Rightarrow> ('channel, 'component_state) comp"
where
  "event c \<equiv> LOOP
    Response (\<lambda>q s'. case s' of Event s \<Rightarrow>
      (case q_data q of 
         Set \<Rightarrow> {(Event True, \<lparr>a_channel = q_channel q, a_data = Void\<rparr>)}
       | Poll \<Rightarrow> {(Event False, \<lparr>a_channel = q_channel q, a_data = Pending s\<rparr>)}
       | _ \<Rightarrow> {}))"

text {*
  An event component always starts without a pending event.
*}
definition
  init_event_state :: "'component_state local_state"
where
  "init_event_state \<equiv> Event False"

subsection {* \label{ssec:memorycomponents}Shared Memory Components *}
text {*
  We represent shared memory as an always listening component that reads or
  writes information into its local state. Executing these reads and writes
  unconditionally accurately represents the behaviour of a read/write region of
  memory. The implementation is similar to @{const event}, it merely replaces
  a one-place buffer with a map.
*}
definition
  memory :: "'channel \<Rightarrow> ('channel, 'component_state) comp"
where
  "memory c \<equiv> LOOP
   Response (\<lambda>q s'. case s' of Memory s \<Rightarrow>
    (case q_data q of
      Read addr \<Rightarrow> {(Memory s, 
                    \<lparr>a_channel = q_channel q, a_data = Value (the (s addr))\<rparr>)}
    | Write addr val \<Rightarrow> {(Memory (s(addr \<mapsto> val)), 
                         \<lparr>a_channel = q_channel q, a_data = Void\<rparr>)})
    | _ \<Rightarrow> {})"

text {*
  The initial state of a shared memory component is an empty map. A shared
  memory region is assumed to be zeroed on startup.
*}
definition
  init_memory_state :: "'component_state local_state"
where
  "init_memory_state \<equiv> Memory empty"

text {*
  In \camkes ADL descriptions, shared memory regions can have a type, typically
  defined as a C struct. For now only the default type @{term Buf} is
  represented in this model. The model can be trivially extended to represent
  user types as components with a memory local state that have additional
  constraints on what can be read from or written to the state.
*}
type_synonym Buf\<^sub>d_channel = unit

definition
  Buf\<^sub>d :: "(Buf\<^sub>d_channel \<Rightarrow> 'channel) \<Rightarrow> ('channel, 'component_state) comp"
where
  "Buf\<^sub>d ch \<equiv> memory (ch ())"

(*<*)
end
(*>*)
